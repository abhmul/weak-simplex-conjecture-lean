# Weak Simplex Conjecture Lean Formalization

## Governing documents

Before editing Lean code, read:

1. `docs/weak_simplex_lean_formalization_report.v3-reassessment.md`;
2. the current work-package card;
3. the relevant mathematical source section;
4. the repository-local generic Lean 4 skill at `.agents/skills/lean4/SKILL.md`.

The reassessment report is the source of truth for theorem architecture, trust boundaries, module
ownership, milestone order, and acceptance criteria. Do not replace it with a fresh whole-paper
translation.

## Fixed environment

- Lean: `leanprover/lean4:v4.31.0`
- mathlib input revision: `v4.31.0`
- pinned mathlib commit: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- Project namespace: `WeakSimplex`
- Production line width: 100 characters

Run all Lean commands from the repository root.

## Trust policy

The trusted result must contain no `sorry`, `admit`, project-defined `axiom`, or unaudited imported
theorem. `Classical.choice`, `propext`, and `Quot.sound` are acceptable foundational axioms.
Anything else requires an explicit review decision.

Never:

- add a project axiom;
- weaken a public theorem or add assumptions merely to make it compile;
- change a frozen theorem statement without an issue-level architecture decision;
- import from `Scratch/` or `Scaffold/` into a production root;
- use `native_decide` for an analytic theorem;
- trust third-party code before it builds on Lean 4.31.0 and passes a transitive axiom audit;
- add an entire external repository as a dependency when a small audited port suffices;
- run whole-paper autoformalization;
- make autonomous commits.

Temporary upstream dependencies must be explicit theorem parameters or structures, never axioms.

## Mathematical architecture invariants

1. State and prove the analytic theorem directly for an admissible covariance matrix `R`.
   Codebook geometry belongs only in the final reduction.
2. Implement adaptive tilting with the unconstrained `s`-space potential

   `Ψ̃_c(s) = ∑ i, ℓ(s i) - 1/2 * qform (R⁻¹) (H ∘ s - c • 1)`.

   Do not formalize `H⁻¹`, `τ`, the auxiliary endpoint function `𝓕`, or the paper's `(q,v)`
   objective unless the integration lead approves a fallback.
3. Prove the centered log-concave product theorem only for positive-definite covariance.
4. Handle singular covariance once, at the outer lower-orthant theorem.
5. Defer measurable `argmax`; first formalize the Bayes/ML value as an integral of a pointwise
   finite maximum.
6. Freeze interfaces between the adaptive branch and the product branch before deep proof work.
7. Keep raw matrix predicates transparent initially; bundle them only after measured evidence that
   coercions are the dominant cost.

## Required workflow for each work package

1. Read the work-package card and identify the single acceptance theorem.
2. Search the exact mathlib checkout before defining a helper.
3. Record candidate declarations and failed approaches in the work-package log.
4. Prototype uncertain APIs in `Scratch/` or `/tmp`; do not pollute production modules.
5. Freeze the theorem statement before substantial proving.
6. Implement in the assigned file set only.
7. Compile the edited file with `lake env lean <file>`.
8. Run `lake build` before marking the package complete.
9. Add or update `Audit/Axioms.lean`, then inspect `#print axioms` for the acceptance theorem.
10. Run a read-only review and report exact remaining blockers.

A package is complete only when its acceptance theorem compiles, the production source contains no
placeholders, the full build passes, and the axiom report is clean.

## Search order

Use Lean LSP MCP first:

- `lean_goal`
- `lean_hover_info`
- `lean_local_search`
- `lean_leanfinder`
- `lean_leansearch`
- `lean_loogle`
- `lean_hammer_premise`
- `lean_state_search`
- `lean_multi_attempt`
- `lean_diagnostic_messages`
- `lean_code_actions`

Then use source search in `.lake/packages/mathlib/Mathlib`. Search external repositories only after
local mathlib search has been documented.

## Build and audit commands

```bash
lean --version
lake --version
lake build

grep -RInE '\b(sorry|admit)\b' WeakSimplexConjectureLean
grep -RInE '^[[:space:]]*axiom[[:space:]]' WeakSimplexConjectureLean
grep -RInE '^[[:space:]]*unsafe[[:space:]]' WeakSimplexConjectureLean
```

`Audit/Axioms.lean` must eventually inspect:

```lean
#print axioms WeakSimplex.centered_product_of_posDef
#print axioms WeakSimplex.exists_adaptiveWitnesses
#print axioms WeakSimplex.lowerOrthant_ge_iid_of_posDef
#print axioms WeakSimplex.lowerOrthant_ge_iid
#print axioms WeakSimplex.weak_simplex
```

## External-code policy

Vendor only the minimal transitive source closure required for a theorem. Every vendored file must
be listed in `PROVENANCE.md` with repository, commit, original path, license, local path, changes,
and an axiom-audit result. Keep vendored declarations in a dedicated namespace until the port is
accepted.

Current candidates and priority:

1. LeanPool/Isoperimetric Prékopa–Leindler port, because its Lean version is closest to 4.31;
2. StatLean Gaussian shift and product-density helpers;
3. StatLean Anderson/Prékopa code as an alternative or source of auxiliary lemmas;
4. older isoperimetric code as a fallback source of proof ideas.

## Coordination

Use disjoint file ownership or separate worktrees for parallel agents. One integration owner controls
public declarations and production imports. Subagents return patches and logs; they do not merge or
commit. Report a blocker with the exact goal, minimal reproduction, declarations searched, and the
smallest missing interface theorem.
