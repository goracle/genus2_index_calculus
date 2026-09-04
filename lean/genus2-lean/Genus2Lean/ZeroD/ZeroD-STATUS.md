# STATUS: verified sorry inventory, whole project

**Purpose**: a single, re-runnable ground-truth check, so "is X still a
sorry" never again has to be answered by trusting a roadmap file's prose
claim. Re-run the script below any time; don't trust the numbers below
past the date they were generated if you've touched any `.lean` file
since.

**Generated**: this pass, from a fresh comment-stripped scan (strips
`--` line comments and `/- ... -/` block comments, including nested
ones, before searching for the whole-word token `sorry`). A raw
`grep -c sorry` massively overcounts, because most hits across this
project are prose *about* sorries in module docstrings, not live tactic
uses -- see e.g. `ROADMAP-reduce-to-zerodim.md`'s own note making the
same point.

## How to re-run

```bash
python3 - << 'EOF'
import re, os

def strip_comments(text):
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if text[i:i+2] == '/-':
            depth += 1; i += 2
            while i < n and depth > 0:
                if text[i:i+2] == '/-':
                    depth += 1; i += 2
                elif text[i:i+2] == '-/':
                    depth -= 1; i += 2
                else:
                    i += 1
            continue
        if text[i:i+2] == '--':
            j = text.find('\n', i)
            i = n if j == -1 else j
            continue
        out.append(text[i]); i += 1
    return ''.join(out)

total, per_file = 0, {}
for root, _, files in os.walk('.'):
    for fn in files:
        if fn.endswith('.lean'):
            path = os.path.join(root, fn)
            text = open(path, encoding='utf-8', errors='replace').read()
            hits = re.findall(r'\bsorry\b', strip_comments(text))
            if hits:
                per_file[path] = len(hits)
                total += len(hits)
for path, count in sorted(per_file.items(), key=lambda x: x[1]):
    print(f"{count}\t{path}")
print("TOTAL:", total)
EOF
```

Run this from `Genus2Lean/` (the directory containing `ZeroD/` as a
subdirectory), so it scans both the top-level files and `ZeroD/`
together.

**Caveat, always**: this is a lexical scan, not a kernel check. It
tells you where `sorry` tokens live in source, not whether the
surrounding proof term actually typechecks, nor whether a theorem's
*statement* is what you think it is, nor whether a hypothesis bundle
the theorem depends on is itself provable. "Zero sorry" is a necessary
signal of progress, not a sufficient one -- see `README.md`'s "Sorry-free
is not the same as done" section. Only `lake build` (Claire's REPL, per
this project's own convention -- Claude does not run this) gives a real
compile-clean signal.

## Result, this pass

**Whole project total: 7 live `sorry` tokens. All 7 are in the
top-level `Genus2Lean/` directory. Zero are under `ZeroD/`.**

| count | file | theorem(s) near the sorry |
|---|---|---|
| 1 | `PrincipalSubgroupCollapse.lean` | (not individually traced this pass -- re-run the per-file theorem-locator snippet below if needed) |
| 1 | `SidonDichotomyGeneral.lean` | `sidonDichotomy_general` |
| 1 | `LCanonicalElementary.lean` | `isOnlyFibersInCanonicalClass_of_elementary` |
| 2 | `RiemannRochGenus2.lean` | `finrank_L_pair`, `finrank_L_canonical` |
| 2 | `RiemannRochCrux.lean` | `uniqueDegree2MapToP1` (and one more in the same file, not individually separated this pass) |

To find the nearest enclosing `theorem`/`lemma`/`def` for each hit
precisely, adapt the snippet above: after computing `stripped` for a
given file, split on `\n`, find each line matching `\bsorry\b`, and
scan backward for the nearest line matching
`^\s*(theorem|lemma|def)\s+\w+`.

## Why this list is short even though the project has ~70,000 lines of Lean

Per this project's own stated practice, most genuinely open mathematical
content has been **weakened to an explicit named hypothesis** rather
than left as a `sorry` or silently assumed. A `sorry` count near zero
does NOT mean the project is nearly done -- it means the open questions
have (correctly, per project convention) been made visible as
hypothesis bundles instead of TODO markers. See `README.md`'s "Sorry-
free is not the same as done" section for the specific bundles
(`Nondegenerate`, `CrossNondegenerate`, `PeelChainNondegenerate`,
`GenericPeelChainHyp`, etc.) carrying the real remaining content in
`ZeroD/`.

## Known stale claims found this pass (fix in place if you're touching these files anyway)

- `ROADMAP-alpha-locus.md`, `ROADMAP-alpha-to-degree-uniform.md`, and
  `ROADMAP-degree-uniform-step3.md` (all in `ZeroD/`) describe
  `decoupledSystem_degree_uniform` and `decoupledSystem_zeroDimensional`
  (`AlphaLocusDegreeUniform.lean`) as still-open `sorry`s. As of this
  pass's scan, neither has a live `sorry` token -- `AlphaLocusDegreeUniform.
  lean`'s own module docstring says both were closed in a later pass than
  any of those three roadmap files record, under a new hypothesis bundle
  `GenericPeelChainHyp`, and flags the result as not yet REPL-confirmed.
  None of the three roadmap files were edited to reflect this. Not fixed
  this pass (out of scope for a first documentation pass) -- flagged here
  so the next person doesn't have to rediscover it by re-reading all four
  files against each other.
- `ROADMAP-peel-chain-assembly.md` was itself already flagged as stale
  by `ROADMAP-reduce-to-zerodim.md` (see that file's own "Why this
  document exists" section) for a different reason (claimed 4 live
  sorries in `PeelChainAssembly.lean` that were already closed at the
  time). `ROADMAP-peel-chain-assembly.md`'s own later sections record
  the actual fix (`hv0_ext`-`hv3_ext` hypotheses, build green) -- so the
  file is internally inconsistent (stale early sections, accurate late
  sections) rather than uniformly wrong. Read its last "Update" section,
  not its opening framing.
