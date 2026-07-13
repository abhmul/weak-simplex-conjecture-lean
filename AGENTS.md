# Agent Guidance

- Run Lean and Lake commands from the repository root.
- Treat `lean-toolchain` and `lake-manifest.json` as authoritative; do not change toolchains, add overrides, or update dependencies unless explicitly requested.
- On a fresh clone or worktree, run `lake exe cache get` before building.
- Establish a clean baseline with `lake build --wfail` before substantial edits.
- After focused edits, validate affected files with `lake env lean path/to/File.lean`.
- Before completion, run `lake build --wfail`.
- Search the project and Mathlib for existing declarations before constructing proofs.
- Completed work must contain no `sorry`, `admit`, or new custom axioms.
- Do not weaken or change theorem statements, signatures, or docstrings merely to make proofs compile without explicit approval.
- Keep isolated experiments outside the repository; do not leave scratch files in the repository root.
