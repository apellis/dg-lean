# Conventions

These conventions are fixed for the whole library. Changing one of them later means changing
every file, so read this before writing anything.

## Ground ring and gradings

- The ground ring `R` is a commutative ring (`CommRing R`). Results that need a field say so.
- Gradings are **cohomological** and indexed by `ℤ`: a dg algebra is `A = ⊕_{n ∈ ℤ} Aⁿ` and the
  differential has degree `+1`, `d : Aⁿ → Aⁿ⁺¹`, with `d ∘ d = 0`.
- The **parity** of a homogeneous element is its degree modulo `2`; the Koszul sign of degree
  `n` is `(-1)^n`, implemented as `Int.negOnePow n : ℤˣ` (`DG.koszulSign`). Never introduce a
  second, independent parity grading in the core library.
- ℤ/2-graded dg algebras, and dg algebras whose differential has degree `k ≠ 1`, are treated by
  regrading: a ℤ/2-graded dg algebra is a `ℤ`-graded one with `A^{2n} = A^{0̄}`, `A^{2n+1} = A^{1̄}`
  (a "2-periodic" dg algebra), and a differential of degree `k` on a `ℤ`-grading is a
  differential of degree `1` on the grading divided by `k` (with `k` residue classes as
  separate summands). Provide these as constructions from the core definitions, not as a
  second core.
- A **bigraded** (or "internally graded") dg algebra carries an additional `ℤ`-grading preserved
  by `d`; its category of dg modules has a shift `⟨1⟩` of the internal degree, commuting with
  the homological shift `[1]`, and `K₀` becomes a `ℤ[q, q⁻¹]`-module with `q = [⟨1⟩]`. This is a
  separate layer on top of the core (Roadmap, tier 5).

## Sign rule

Whenever two homogeneous symbols of degrees `m` and `n` are exchanged, multiply by `(-1)^{mn}`.
In particular:

- Leibniz: `d (a * b) = d a * b + (-1)^{|a|} * (a * d b)`.
- Left dg module: `d (a • m) = d a • m + (-1)^{|a|} * (a • d m)`.
- Right dg module: `d (m • a) = d m • a + (-1)^{|m|} * (m • d a)`.
- `HOM_A(M, N)ⁿ` is the module of `A`-linear maps of degree `n` (graded `A`-linear with the
  sign `f (a • m) = (-1)^{|f| |a|} a • f m`), with `d f = d_N ∘ f - (-1)^{|f|} f ∘ d_M`.
- The opposite dg algebra `Aᵒᵖ` has product `a ·ᵒᵖ b = (-1)^{|a||b|} b a`; a right dg `A`-module
  is a left dg `Aᵒᵖ`-module.
- Tensor product of dg modules over `R`: `d (m ⊗ n) = d m ⊗ n + (-1)^{|m|} m ⊗ d n`;
  `(a ⊗ b) (a' ⊗ b') = (-1)^{|b||a'|} (a a') ⊗ (b b')` on tensor products of dg algebras.
- Shift: `(M[n])ᵏ = Mᵏ⁺ⁿ`, `d_{M[n]} = (-1)^n d_M`, and the action is twisted by the Koszul
  sign, `a •_{M[n]} m = (-1)^{n|a|} (a • m)` (forced by the Leibniz rule once
  `d_{M[n]} = (-1)^n d_M`). In Lean: `DG.Shift n M`, a type synonym of `M`.
- Mapping cone of `f : M ⟶ N`: `C(f) = M[1] ⊕ N` with `d (x, y) = (-d_M x, f x + d_N y)` and the
  componentwise action (`DG.Cone f`, underlying type `Shift 1 M × N`). The summands are
  ordered as in Mathlib's `CochainComplex.mappingCone` (`X i = F.X (i + 1) ⊞ G.X i`), so that
  the first and second projections correspond to Mathlib's `mappingCone.fst` and
  `mappingCone.snd`. The standard triangle is `M → N → C(f) → M[1]` with maps `f`, the
  inclusion of `N`, and `-` the first projection, as in Mathlib's `mappingCone.triangle`.

**Match Mathlib.** The underlying cochain complex of a dg module is a
`CochainComplex (ModuleCat R) ℤ`, and the shift and cone above must agree, on underlying
complexes, with Mathlib's `CochainComplex.shiftFunctor` and `CochainComplex.mappingCone`
(`Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`), including signs. State and
prove that compatibility as early as possible (Roadmap, item 2.4); it is what makes the
forgetful functor from the homotopy category of dg modules to Mathlib's homotopy category a
triangulated functor, and it is the main check that the sign conventions are right. Use
Mathlib's `Int.negOnePow` API (`Int.negOnePow_add`, `Int.negOnePow_succ`, ...) rather than
`(-1 : R)^n` with natural-number exponents.

## Definitions: concrete first, categorical second

The core objects are concrete structures on types, in Mathlib's style for graded rings, with
the data in one class and compatibilities as `Prop`-valued mixins (as `Ring A` / `Module R M` /
`IsScalarTower R A M` in Mathlib):

- `DGAddCommGroup M` (the data): an abelian group with an internal grading
  `grading : ℤ → AddSubgroup M` (a `DirectSum.Decomposition`) and a differential `d : M →+ M`
  with `d (Mⁿ) ⊆ Mⁿ⁺¹` and `d ∘ d = 0`. This is an internally graded cochain complex of abelian
  groups; the same `d` and `grading` are used for rings and modules.
- `DGRing A` (`Prop`): for `[Ring A] [DGAddCommGroup A]`, the grading is a ring grading
  (`SetLike.GradedMonoid`, hence `GradedRing`) and `d` satisfies the graded Leibniz rule on
  homogeneous elements.
- `DGAlgebra R A` (`Prop`): for `[Algebra R A]`, the image of `R` lies in degree `0` and is
  killed by `d`. Consequences, not axioms: `d` is `R`-linear and every `Aⁿ` is an `R`-submodule
  (`DGAlgebra.gradingSubmodule R A`, a `GradedAlgebra`). Every dg ring is a dg `ℤ`-algebra.
- `DGModule A M` (`Prop`): for `[Module A M] [DGAddCommGroup M]`, the action is graded
  (`SetLike.GradedSMul`) and satisfies the signed Leibniz rule. A dg ring is a dg module over
  itself. With `[Module R M] [IsScalarTower R A M]` and `DGAlgebra R A`, `d` is `R`-linear.
  Right dg modules are the mixin for `Module Aᵐᵒᵖ M` with the right-handed sign rule; bimodules
  are two mixins plus `SMulCommClass`.
- Morphisms `DGModuleHom A M N` (notation `M →ᵈᵍ[A] N`): `A`-linear maps of degree `0`
  commuting with `d`.

Categorical packagings (`DGModuleCat A`, the homotopy category, the derived category) are
built on top, together with the comparisons to monoid and module objects in Mathlib's
monoidal category `CochainComplex (ModuleCat R) ℤ` (`Mon`, `Mod`). Prefer bundled
categorical statements for theorems about categories and concrete statements for
computations. Do not duplicate Mathlib: reuse `GradedRing`, `GradedAlgebra`, `DirectSum`,
`HomologicalComplex`, `Homotopy`, `HomotopyCategory`, `CategoryTheory.Quotient`,
`CategoryTheory.Localization`, `Pretriangulated`, `IsTriangulated`, and the
`HasDerivedCategory`-style universe handling.

## Dg categories

From tier 3 on, results are stated for small dg categories wherever possible; a dg ring is the
one-object case, and a dg ring with an additional internal ("weight") grading is the dg
category with objects `ℤ` (so the bigraded theory of tier 7 needs no separate development).

- A dg category is a category `C` with `[Category C] [Preadditive C]`, a
  `DGAddCommGroup (X ⟶ Y)` on every Hom group, and the `Prop` mixin `DGCategory C`:
  composition is graded (`f ∈ (X ⟶ Y)ⁱ`, `g ∈ (Y ⟶ Z)ʲ` give `f ≫ g ∈ (X ⟶ Z)ⁱ⁺ʲ`), identities
  have degree `0`, and the Leibniz rule holds in diagrammatic order,
  `d (f ≫ g) = f ≫ d g + (-1)^{|g|} (d f ≫ g)` for `g` homogeneous (the rule
  `d (g ∘ f) = d g ∘ f + (-1)^{|g|} g ∘ d f`, matching Mathlib's `HomComplex.δ_comp`). The
  morphisms of the Lean category are all homogeneous-sum maps; the category of degree-`0`
  cocycles `Z⁰(C)` and the homotopy category `H⁰(C)` are derived from it.
- The one-object dg category of a dg ring `A` is Mathlib's `SingleObj A` (composition
  `f ≫ g = g * f`), for which the mixin is exactly `DGRing A`.
- A dg module over `C` is a left module, i.e. a covariant dg functor to dg abelian groups:
  a family `M : C → Type*` of dg abelian groups with actions `(X ⟶ Y) → M X → M Y`, graded,
  unital, associative (`(f ≫ g) • m = g • (f • m)`) and satisfying
  `d (f • m) = d f • m + (-1)^{|f|} f • d m`. For `SingleObj A` these are the left dg
  `A`-modules; the equivalence with `DGModuleCat A` is part of the theory.

## Naming

- Namespace `DG`. Files under `DG/`, one topic per file, imported from `DG.lean`.
- Structures: `DGAddCommGroup M`, `DGRing A`, `DGAlgebra R A`, `DGModule A M`, `DGRingHom`,
  `DGModuleHom` (degree-`0` chain maps, `M →ᵈᵍ[A] N`), `DGModuleCat A`, `HomotopyCategory A`,
  `DerivedCategory A`, `DGModule.HOM`, `DGModule.END`, `DGModule.cohomology`.
- Theorems are named by Mathlib conventions (`d_mul`, `d_smul`, `d_comp_d`, `cohomology_map`,
  ...). A theorem from the literature gets a docstring citing the source (author, title,
  year, statement number) and a remark on any deviation.
- Mark every result whose proof is not yet complete as absent, not as `sorry`: keep
  in-progress files out of the default build (`lake_lib` globs) rather than committing a
  `sorry`. The build treats warnings as errors.
