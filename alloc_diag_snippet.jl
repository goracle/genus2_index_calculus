# Paste-in diagnostic: run this block right after section 7's existing
# miss/insert let-block in alloc_test_harness.jl (same scope, same variables).
# Goal: confirm/deny whether @allocated's 0 at top-level is itself the
# unreliable measurement (global-scope specialization), by wrapping the
# identical call in a local function barrier.

