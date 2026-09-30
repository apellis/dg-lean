# dg-lean

A Lean 4 / Mathlib library of differential graded (dg) algebra: dg algebras and dg modules,
their homotopy and derived categories, compact objects and Grothendieck groups, and the
structure theory of positive dg algebras.

The library is at the roadmap stage. This file describes the goals; [ROADMAP.md](ROADMAP.md)
lists the intended results, with references and acceptance criteria, in the order they should
be built; [docs/CONVENTIONS.md](docs/CONVENTIONS.md) fixes gradings, signs and naming;
[AGENTS.md](AGENTS.md) is the contributor guide. As results are completed this file will be
rewritten to describe what is formalized.

## Goals

Mathlib (at the pinned revision) has homological complexes in an abelian category, the
homotopy category of cochain complexes with its triangulated structure, the derived category
of an abelian category, and the general theory of triangulated categories and localization.
It has no dg algebras, no dg modules over a dg algebra, no derived category of a dg algebra, no
compact or perfect objects, and no Grothendieck group of a triangulated category. This library
is meant to supply those, in a form that could be upstreamed to Mathlib, and to prove the
standard theorems about them:

1. **Foundations.** ℤ-graded dg algebras over a commutative ring with the Koszul sign rule;
   left, right and bi- dg modules; morphisms and the `HOM` complexes; endomorphism dg
   algebras; tensor products; cohomology; quasi-isomorphisms; dg ideals, quotients,
   idempotents and corners; comparison with monoid and module objects in Mathlib's monoidal
   category of cochain complexes.
2. **The homotopy category `H(A)`.** The abelian category of dg modules; homotopies; the
   homotopy category as a quotient, its shift, mapping cones and its (pre)triangulated
   structure; `Hom_{H(A)}(M, N) = H⁰(HOM_A(M, N))`; K-projective (cofibrant), semi-free and
   finite-cell modules.
3. **The derived category `D(A)`.** Localization of `H(A)` at quasi-isomorphisms, its
   triangulated structure, existence and uniqueness of K-projective resolutions,
   `Hom_{D(A)}(M, N) = H⁰(HOM_A(P_M, N))`, derived tensor and `RHom`, the tensor–Hom
   adjunction, induction and restriction along dg algebra maps, and Keller's theorem that a
   quasi-isomorphism of dg algebras induces an equivalence of derived categories; the
   acyclicity criterion `D(A) ≃ 0 ⟺ H(A) = 0 ⟺ ∃ x, d x = 1`.
4. **Compact objects and Grothendieck groups.** Compact objects of a triangulated category
   with coproducts; the perfect derived category `D^c(A)`; the Grothendieck group `K₀` of a
   triangulated category and `K₀(A) := K₀(D^c(A))`; `K₀` of a field and of a ring concentrated
   in degree `0`; comparison with Mathlib's derived category of modules.
5. **Positive dg algebras.** Schnürer's theorem: over a positive dg algebra the compact
   objects are exactly the finite-cell modules up to isomorphism, hence `K₀(A) ≅ K₀(A⁰)`;
   formality and Keller's theorem; bigraded variants (an additional internal grading with its
   shift functor, making `K₀` a `ℤ[q, q⁻¹]`-module).

Everything is stated over a commutative ring `R` unless a theorem needs a field. Cohomological
ℤ-gradings are primary; ℤ/2-graded and "differential of degree `n`" variants are obtained by
regrading, see the conventions.

## Building

The default branch is `master`. This package depends only on Mathlib (and its
transitive dependencies); it does not depend on the other formalization repositories.

Requires [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.34.1` and
Mathlib `v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`) are pinned.

```sh
lake exe cache get
lake build
```

The package treats warnings as errors. Completed results contain no `sorry` and no added
axioms; the axiom closure of a result should be contained in `propext`, `Classical.choice`
and `Quot.sound`.

## Models used

The code and proofs are produced with AI models under human direction and checked by Lean:

- Claude Opus 5.5
- Claude Fable 5.1

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
