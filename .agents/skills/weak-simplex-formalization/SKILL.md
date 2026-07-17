---
name: weak-simplex-formalization
description: >
  Execute one frozen work package from the weak simplex conjecture Lean formalization plan. Use
  explicitly for theorem-interface design, proof implementation, external-port auditing, or milestone
  integration in this repository. Do not use for a whole-paper autoformalization or to rewrite public
  theorem statements autonomously.
---

# Weak Simplex Formalization Work Package

## Inputs

Require all of the following before starting:

- a work-package identifier `WP00`–`WP23`;
- an acceptance theorem or explicit spike deliverable;
- an owned file set;
- a stop budget;
- the relevant section of `references/lean-formalization-plan.md`.

When an input is missing, stop after repository/API reconnaissance and report the ambiguity. Do not
silently choose a different theorem.

## Preflight

1. Read the repository-root `AGENTS.md`.
2. Read the governing plan sections for the selected work package.
3. Run `lean --version`, `lake --version`, and `git status --short`.
4. Confirm the exact mathlib manifest commit.
5. Confirm Lean LSP MCP is available. Treat scripts-only operation as a blocked environment for a
   load-bearing analytic theorem.
6. Inspect imports and all upstream acceptance theorems.
7. State the resolved inputs and the exact theorem to be completed.

## Proof loop

### 1. Search

Search the exact checkout before proving:

- local declarations and callers;
- mathlib by name, type shape, and semantic query;
- only then audited external candidates.

Record candidate declaration names. Do not define a duplicate helper merely because a search by one
English phrase failed.

### 2. Freeze the statement

Check that the declaration matches the plan's quantifiers and trust boundary. Once proof work starts,
do not alter its header. Escalate any proposed assumption, type, namespace, or conclusion change.

### 3. Prototype

Use `/tmp` or `Scratch/` for uncertain APIs. First compile the smallest representative fragment:

- one matrix identity;
- one derivative;
- one measure map;
- one `lintegral` conversion;
- one CLT instantiation;
- one Portmanteau continuity-set limit.

Move only stable abstractions into production.

### 4. Prove incrementally

Prefer named lemmas with one mathematical role. Compile after each nontrivial step. For a difficult
goal, inspect the live goal and test several small tactic/term candidates rather than editing blindly.
Use local heartbeat increases only after profiling.

### 5. Validate

For the edited package:

```bash
lake env lean path/to/Edited.lean
lake build
```

Then scan the owned files for placeholders and inspect axioms of the acceptance theorem. A compiling
theorem with a non-clean axiom report is incomplete.

### 6. Review

Run a read-only review for:

- statement fidelity;
- hidden assumptions;
- import leakage;
- accidental dependence on `Scratch/`, `Scaffold/`, or unaudited `Vendor/` code;
- unnecessary local reproofs of mathlib facts;
- fragile simp dependence;
- excessive elaboration cost;
- theorem/documentation mismatch.

### 7. Handoff

Return:

- files changed;
- acceptance theorem status;
- exact build commands and results;
- axiom report;
- declarations reused;
- remaining blockers with exact goals;
- suggested next work package;
- no commit unless the integration owner explicitly requests one.

## Branch-specific invariants

### Adaptive-tilt branch

- Work in covariance space.
- Use `r`, `H`, `ℓ`, and the unconstrained `s`-space potential.
- Prove maximizer existence through an explicit compact superlevel set.
- Need only existence and stationarity, not strict concavity or uniqueness.
- Derive `s + a - R a = c • 1` with `a i = r (s i)`.
- Prove the rank-one inverse bound by evaluating `R - J/m ⪰ 0` at `R⁻¹ 1`; do not introduce
  matrix square roots for this step.

### Product branch

- Assume positive-definite covariance throughout.
- Keep the log-concavity interface no more general than needed.
- Follow: symmetric rectangles → even factors → normalized self-convolution → sum/difference
  deficit → dyadic CLT → explicit density-ratio lower bound → contradiction.
- Do not formalize the full centered forward–reverse Brascamp–Lieb theorem.
- Audit the direction of every deficit inequality independently.

### Singular-limit branch

- Approximate with `Rε = (1-ε)R + εI` only after the positive-definite orthant theorem exists.
- Prove the lower orthant is a continuity set from standard-normal coordinate marginals.
- Do not extend the product theorem to singular covariance.

### Coding branch

- Keep the Bayes value separate from measurable selector packaging.
- Prove covariance normalization and regular-simplex identity after the matrix theorem.
- Preserve the distinction between stochastic domination of the normalized maximum and MGF
  comparison for the original score maximum.

## Forbidden shortcuts

- project axioms;
- `sorry` or `admit` in production;
- whole-paper `/lean4:autoformalize`;
- autonomous statement rewriting;
- autonomous commits;
- broad external repository dependencies;
- importing `Mathlib` in production without a measured reason;
- claiming completion before a full build and axiom check.
