# Contributor guide

This repository is developed largely by AI agents under human direction. Everything below is
public. Keep it mathematical and technical.

## Ground rules

- Lean `v4.34.1` and Mathlib `v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`) are pinned in
  `lean-toolchain`, `lakefile.lean` and `lake-manifest.json`. Do not run `lake update`. To build
  for the first time: `lake exe cache get` then `lake build`.
- The build treats warnings as errors (`-DwarningAsError=true`). Every file under `DG/` is
  built (`globs := #[.andSubmodules `DG]`), so a file that does not compile breaks the build:
  develop new files elsewhere (a scratch directory outside the repository, or a `git worktree`)
  until they compile, then add them.
- No `sorry`, `admit`, `native_decide` or new `axiom` in committed files. Before presenting a
  result as done, run `#print axioms` on it in a scratch file and check the closure is
  contained in `propext`, `Classical.choice`, `Quot.sound`. Compilation alone is not the
  acceptance criterion; source fidelity is.
- `scripts/NonVacuity.lean` (run by CI) applies each headline theorem to concrete data with every
  hypothesis proved. When a headline theorem is added or its hypotheses change, add or update its
  example there.
- Read [docs/CONVENTIONS.md](docs/CONVENTIONS.md) before writing definitions. Do not
  introduce alternative sign or grading conventions.
- Work through [ROADMAP.md](ROADMAP.md) in order within a tier; later tiers depend on earlier
  ones. Each item has an acceptance predicate: the statement that must be proved, on the
  library's own definitions, with the generality stated. Prove the general statement; a
  special case proved in a replacement model is not the item.
- Reuse Mathlib. Before defining anything, search Mathlib for it (`HomologicalComplex`,
  `Homotopy`, `HomotopyCategory`, `CategoryTheory.Localization`, `Pretriangulated`,
  `GradedRing`, `DirectSum`, `Mon`, `Mod`, `Int.negOnePow`, ...). If Mathlib has a result
  for cochain complexes, the dg-module version should be proved by reduction to it whenever
  the forgetful functor allows, and otherwise by the same proof.
- Universe levels: the derived category is a localization and may live in a larger universe.
  Follow Mathlib's `HasDerivedCategory` pattern (a class asserting a chosen small localization
  exists) rather than fixing universes by hand.
- Distinguish the literal statement of a cited theorem, a repaired statement, and a proof gap.
  If a cited statement is false as printed, record a counterexample and the corrected
  statement in the docstring and in the README's errata list. Never weaken a hypothesis or
  change a sign silently to make something compile.
- Keep proofs readable: name intermediate lemmas, avoid giant `simp` sets and `maxHeartbeats`
  overrides where possible, and keep files under about 1500 lines.

## Workflow

The default branch is `master`. Keep DG independent: its only direct Lake dependency
is Mathlib. Do not introduce sibling-library dependencies.

Reuse the pinned dependency cache for builds. Keep verification logs and scratch
checks outside tracked sources; `.lake/build` is regenerable, while source, manifests
and verification evidence must be retained. Never delete shared `.lake/packages`
when cleaning local build products.

1. Pick the first roadmap item not yet done whose dependencies are done. Write the statements
   first, check them against the source reference, then prove.
2. Build the changed modules (`lake build DG.Foo`), then the whole package (`lake build`).
3. Record the item as done in `ROADMAP.md` (declaration names next to the item) and, once a
   tier is complete, update `README.md` from roadmap language to a description of what is
   formalized.
4. Commit messages describe the mathematics; no process narration.

## Layout

```
DG.lean                 root imports
DG/Basic.lean           sign conventions (koszulSign)
DG/Graded/              graded modules and algebras with Koszul signs (tier 1)
DG/Algebra/             dg abelian groups, dg rings and algebras (`DG/Algebra/Basic.lean`),
                        maps, tensor products, opposite, cohomology
DG/Module/              dg modules (`DG/Module/Basic.lean`), HOM/END, tensor, cohomology, corners
DG/Homotopy/            DGModuleCat, homotopies, homotopy category, shift, cone, triangulated
DG/Derived/             quasi-isomorphisms, localization, resolutions, derived functors, Keller
DG/Compact/             compact objects, perfect derived category
DG/K0/                  Grothendieck groups of triangulated categories, K₀ of dg algebras
DG/Positive/            positive dg algebras, Schnürer's theorem, formality
DG/Bigraded/            internal gradings, ⟨1⟩, ℤ[q,q⁻¹]-module structure on K₀
DG/Examples/            examples and small computations
docs/                   conventions and design notes
```

Directories are created when their first file lands.

## Staying on course

These rules apply to every contributor and take precedence over local habits or private
instructions that conflict with them.

**Targets and scope**

- Every PR advances a specific numbered result of a cited source (theorem, proposition,
  corollary, lemma, definition or equation) or a roadmap item that one of them needs. The PR
  title or body names it. Supporting lemmas land with, or shortly before, the result that uses
  them.
- Formalize what the source states. Do not label results "original", and do not develop new
  theory when a source step is missing. When a cited proof relies on a reference that is not
  available, on a step that has a gap, or on a result outside the library, stop and record this
  in the tracking issue as a question for the maintainer. The options are: (a) obtain the
  reference; (b) take the missing input as an explicit, documented hypothesis of the dependent
  results; (c) build a replacement route. Do not start (c) without the maintainer's approval.
- Scope decisions are the maintainer's. These include declaring a numbered result out of scope,
  choosing between several valid conventions, and substituting a different object for the one
  the source uses (for example a crystal basis for a canonical basis). List them as open
  questions; do not decide them silently.
- Prove one form of a result. Restate it in another form (maps → bimodule maps → natural
  isomorphisms → mates, and so on) only when a named downstream result needs that form.

**Statements**

- A headline statement carries exactly the source's hypotheses, after any recorded erratum
  correction.
- An extra hypothesis that the current proof route needs is allowed only on an intermediate
  statement. Its docstring must say so, the README status must say so, and a roadmap item must
  track its removal.
- Names, docstrings and status tables never overstate. Do not use `_unconditional` on a
  conditional theorem, and do not use "full" or "complete" for a statement that assumes part of
  its conclusion.
- An erratum entry gives the printed statement, the corrected statement with the extra
  hypothesis or correction, the declarations, and a short paragraph that can be sent to the
  authors as is.

**Lean engineering**

- Elaboration trouble is not a mathematical obstruction. Examples: `whnf` or `isDefEq` timeouts
  on dependent transports, heartbeat limits, motive errors, slow instance search.
- After two failed attempts at the same proof, redesign the encoding. Possible changes: reindex
  so that the types agree definitionally, prove one generic lemma instead of many instances, or
  avoid nested casts. Do not raise `maxHeartbeats` or retry with a larger budget.
- Names of declarations, modules and PRs describe the mathematics. Avoid process adjectives
  ("actual", "genuine", "original", "native", "fixed", "frontier"), stage labels (`LegA`,
  `AdapterB7`, `PbwL3`) and "WIP". A PR whose title says WIP is not merged.

**Workflow and evidence**

- All proof work happens on topic branches of this repository and lands through PRs with green
  CI. Work that does not build yet may be pushed as a draft PR. Proof developments are not kept
  in private copies, scratch archives or other repositories.
- The evidence that a result is done is CI: full build with warnings as errors, plus the axiom
  audit. Agreement between reviewers, private sign-offs, hash manifests and log archives are not
  evidence. Do not commit logs, manifests, archives or review packets.
- The same PR updates the README/ROADMAP status row and the tracking issue. Close an issue when
  its goal is met.
