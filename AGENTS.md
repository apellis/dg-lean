# Contributor guide

This repository is developed largely by AI agents under human direction. Everything below is
public. Keep it mathematical and technical.

## Ground rules

- Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned in
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
- Read [docs/CONVENTIONS.md](docs/CONVENTIONS.md) before writing definitions. Do not
  introduce alternative sign or grading conventions.
- Work through [ROADMAP.md](ROADMAP.md) in order within a tier; later tiers depend on earlier
  ones. Each item has an acceptance predicate: the statement that must be proved, on the
  library's own definitions, with the generality stated. Prove the general statement; a
  special case proved in a replacement model is not the item.
- Reuse Mathlib. Before defining anything, search Mathlib for it (`HomologicalComplex`,
  `Homotopy`, `HomotopyCategory`, `CategoryTheory.Localization`, `Pretriangulated`,
  `GradedRing`, `DirectSum`, `Mon_`, `Mod_`, `Int.negOnePow`, ...). If Mathlib has a result
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
