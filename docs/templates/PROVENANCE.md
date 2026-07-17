# Vendored Lean Code Provenance

Every file under `WeakSimplexConjectureLean/Vendor/` must have an entry before it can be imported by
a production root.

| Local path | Upstream repository | Commit | Original path | License | Local changes | Lean 4.31 build | Axiom audit |
|---|---|---|---|---|---|---|---|
| | | | | | | | |

## Audit requirements

For each imported top theorem, record:

1. the exact build command;
2. the transitive local file closure;
3. scans for `sorry`, `admit`, `axiom`, and `unsafe`;
4. `#print axioms` output;
5. any namespace or API adaptation;
6. whether the theorem is copied, modified, or wrapped.
