#!/usr/bin/env python3
"""
Driver for gen_dataset.py: runs many small chunks back-to-back inside a
single process invocation, so one call can be left running for ~30 min
without needing manual resume between tool calls.

Each chunk is still generated via a *subprocess* call to gen_dataset.py
(not an in-process function call), because that's the unit we already
verified is byte-for-byte resumable (same seeded RNG, fast-forwarded by
start_index draws) -- this driver just automates "check current progress,
launch next chunk, repeat" instead of a human doing it call by call.

Stops when:
  - target n_examples is reached, or
  - the wall-clock time budget is exhausted (finishes the in-flight chunk,
    does not start a new one), or
  - a chunk subprocess fails twice in a row (to avoid spinning forever on
    a real bug rather than a transient timeout)

Progress is determined by reading the actual last example_id in the
output file after each chunk -- not by trusting the subprocess's own
exit code/stdout -- since we've already seen a chunk get killed
mid-write after successfully flushing most of its examples.
"""

from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path


def last_written_index(out_path: str) -> int:
    """Returns the highest example_id actually present in out_path, or -1
    if the file doesn't exist or is empty. Reads the last line rather
    than assuming order/count match any particular chunk boundary, since
    a chunk can die mid-write."""
    p = Path(out_path)
    if not p.exists():
        return -1
    last_id = -1
    with open(out_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                # a partially-written final line from a killed process;
                # ignore it, it doesn't count as written
                continue
            last_id = max(last_id, rec["example_id"])
    return last_id


def run_driver(
    target: int,
    out_path: str,
    meta_path: str,
    chunk_size: int,
    time_budget_seconds: float,
    gen_script: str = "gen_dataset.py",
):
    t_deadline = time.time() + time_budget_seconds
    consecutive_failures = 0

    while True:
        current = last_written_index(out_path) + 1  # next index to generate
        if current >= target:
            print(f"target reached: {current}/{target} examples written", flush=True)
            return

        remaining = target - current
        this_chunk = min(chunk_size, remaining)

        time_left = t_deadline - time.time()
        if time_left <= 0:
            print(f"time budget exhausted; {current}/{target} examples written so far", flush=True)
            return

        print(f"--- launching chunk: start_index={current} n={this_chunk} "
              f"(time left in budget: {time_left:.0f}s) ---", flush=True)

        try:
            result = subprocess.run(
                [sys.executable, gen_script, str(this_chunk), out_path, meta_path, str(current)],
                timeout=max(60.0, min(time_left, 170.0)),  # stay under typical tool-call limits
                capture_output=True,
                text=True,
            )
            if result.returncode != 0:
                print(f"chunk subprocess exited nonzero: {result.returncode}", flush=True)
                print(result.stdout[-2000:], flush=True)
                print(result.stderr[-2000:], flush=True)
        except subprocess.TimeoutExpired as e:
            print(f"chunk subprocess timed out (may have partially written): {e}", flush=True)

        new_current = last_written_index(out_path) + 1
        progress_made = new_current > current
        print(f"after chunk: {new_current}/{target} written "
              f"({'progress' if progress_made else 'NO PROGRESS'})", flush=True)

        if progress_made:
            consecutive_failures = 0
        else:
            consecutive_failures += 1
            if consecutive_failures >= 2:
                print("two consecutive chunks made no progress; stopping to avoid spinning", flush=True)
                return


if __name__ == "__main__":
    target = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
    out_path = sys.argv[2] if len(sys.argv) > 2 else "/home/claude/genus2ml/dataset.jsonl"
    meta_path = sys.argv[3] if len(sys.argv) > 3 else "/home/claude/genus2ml/dataset_meta.json"
    chunk_size = int(sys.argv[4]) if len(sys.argv) > 4 else 300
    time_budget = float(sys.argv[5]) if len(sys.argv) > 5 else 1700.0  # ~28 min, safely under 30

    run_driver(
        target=target,
        out_path=out_path,
        meta_path=meta_path,
        chunk_size=chunk_size,
        time_budget_seconds=time_budget,
    )
