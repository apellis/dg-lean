# dg-lean

A Lean 4 / Mathlib library of differential graded (dg) algebra: dg algebras, dg categories and
their dg modules, homotopy and derived categories, compact objects and Grothendieck groups, and
the structure theory of positive dg algebras, including internal gradings.

[ROADMAP.md](ROADMAP.md) lists the results item by item, with references, acceptance criteria and
the names of the declarations proving them; [docs/CONVENTIONS.md](docs/CONVENTIONS.md) fixes
gradings, signs and naming; [AGENTS.md](AGENTS.md) is the contributor guide.

## What is formalized

Gradings are cohomological (`ℤ`-graded, differential of degree `+1`) with the Koszul sign rule.
Most results are stated for a small dg category `C`, with a dg ring `A` as the one-object case
`SingleObj A`; the dg-ring statements are obtained through `D(SingleObj A) ≌ D(A)`.

1. **Foundations.** Graded modules and algebras with Koszul signs; dg abelian groups, dg rings
   and algebras, dg modules, `HOM`/`END`, tensor products, cohomology rings, corners `e A e`;
   regradings (`ℤ/2`-periodic, differentials of degree `k`); dg categories (`DG.DGCategory`),
   dg functors, the categories `Z⁰(C)`, `H⁰(C)`, right modules, bimodules, tensor products over
   `C`, induction along dg functors, the dg Yoneda lemma.
2. **Homotopy categories.** The abelian category of dg modules; homotopies; the homotopy
   category with its triangulated structure; `Hom_{H(C)}(M, N) = H⁰(HOM(M, N))`.
3. **Derived categories.** `D(C)` as a triangulated localization, with coproducts; K-projective,
   semi-free and finite-cell modules; existence and uniqueness of resolutions
   (`DG.CatModule.exists_kProjective_resolution`, `DG.CatModule.SemiFreeResolution`); `D(C)` is
   equivalent to the K-projective part of `H(C)`; derived induction and restriction along dg
   functors, derived tensor product and `RHOM` along bimodules; **Keller's theorem**: a
   quasi-equivalence induces a triangulated equivalence of derived categories
   (`DG.CatModule.DerivedCategory.kellerEquivalence`, and for dg rings
   `DG.DGRingHom.derivedEquivalence`); `D(A) ≃ 0 ⟺ H(A) = 0 ⟺ ∃ x, d x = 1`; comparison with
   Mathlib's derived category of `R`-modules for `R` in degree `0`.
4. **Compact objects and `K₀`.** Compact objects of triangulated categories, Neeman's
   characterization of the compact objects of a compactly generated category and Brown
   representability; the representable modules compactly generate `D(C)`; `K₀` of triangulated
   categories; `K₀(C) := K₀(D^c(C))` and `K₀(A)`, functorial along dg functors and dg ring maps
   and invariant under quasi-equivalences; `K₀(k) ≅ ℤ` for a field.
5. **Positive dg algebras and dg categories.** Schnürer's theorem: over a positive dg algebra (or
   dg category) the compact objects are exactly the ordered finite-cell modules up to isomorphism;
   `K₀(A) ≅ K₀(A⁰)`, free on the classes of simple idempotents; Künneth formula for `K₀` under a
   splitting hypothesis; formality and `D(A) ≃ D(H(A))` for formal `A`; Morita theory for
   idempotents.
6. **Internal gradings.** Bigraded dg algebras via the weight dg category `C_A`; the internal
   shift `⟨1⟩` on `H`, `D` and `K₀` (a `ℤ[q, q⁻¹]`-module); positive bigraded dg algebras;
   half-graded dg modules (a `ℤ × ℤ/2`-grading with differential of bidegree `(k, 1̄)`), odd
   morphisms and the super Grothendieck group, with the computations over a field
   `K₀(D(k)^c) ≅ ℤ[q]/(q^{2k} - 1)`, `[Π k] = -qᵏ[k]` and super `K₀ ≅ ℤ[q, q⁻¹]/(1 + qᵏ)`
   (`≅ ℤ[√-1]` for `k = 2`).
7. **Further topics.** Commutative dg algebras, dg Lie algebras and Chevalley–Eilenberg
   cochains, Hochschild cochains, the bar construction.

The remaining open items are listed as "Open:" in [ROADMAP.md](ROADMAP.md).

| Theorem | Source locator | Declaration | Hypotheses | Status |
|---|---|---|---|---|
| Perfect objects form a thick subcategory | Roadmap 5.6; bounded projective-complex description | `DG.IsPerfect.isThick` | Ring `R`; Mathlib `HasDerivedCategory (ModuleCat R)` | Proved |
| `K₀(Dᵖᵉʳᶠ(R)) ≃ K₀(R-proj)` via Euler characteristic | Roadmap 5.6; compare Weibel, *The K-book*, II §9 | `DG.perfectK0Equiv` | Same; perfect objects in Mathlib's derived category | Proved |
| Original compact-DG `K₀(ℤ) ≃ ℤ`, regular class ↦ 1 | Roadmap 5.6; integral track | — | Compact/perfect comparison and integral projective rank | Open |
| `K₀(K ⊗ A) ≃ ℤ` for `A` connected over `ℤ` and `K` a field | Roadmap 6.3; issue #6 E | `DG.ExtendScalars.isPositive`, `DG.ExtendScalars.K0EquivInt` | `Aⁿ = 0` for `n < 0`, `A⁰ = ℤ · 1` with `1` of infinite order; chosen derived categories | Proved; `K ⊗ A` is a dg `K`-algebra (`ExtendScalars.dgAlgebra`); the model `K ⊗_ℤ M` of module base change open |
| Half-graded morphisms induce Laurent-linear compact `K₀` maps | Issue #6 B | `HalfGradedDGRing.Hom.weightFunctor`, `Hom.K0Map` | Same arbitrary integer parameter; grading/differential-preserving ring hom; chosen derived categories | Proved; generic quasi-isomorphism invariance remains open |
| Compact `K₀` and super `K₀` of diagonal half-graded dg rings | Issue #6 D | `Diagonal.K0LinearEquiv`, `Diagonal.superK0LinearEquiv`, `Diagonal.blocksDerivedIso` | Any dg ring `A`, `H = HalfGradedDGRing.ofDGRing A` (parameter `2`); chosen derived categories | Proved: `K₀(D(C_H)^c) ≃ (ℤ[q,q⁻¹]/(q⁴-1)) ⊗ K₀(D(A)^c)`, `SuperK0c H ≃ (ℤ[q,q⁻¹]/(1+q²)) ⊗ K₀(D(A)^c)` as Laurent modules; a functor `G` commuting with internal shifts and with `G ι_A ≅ ι_B F` induces `id ⊗ K₀(F)` (`Diagonal.K0LinearEquiv_mapCompact`) |
| Positive half-graded `K₀` reduces to its internal-degree-zero part | Schnürer positivity analogue; `HalfGraded/Positive.lean` | `HalfGradedDGRing.IsPositive.K0DegreeZeroEquiv`, `IsPositive.superK0cDegreeZeroEquiv`; `IsPositive.K0DegreeZeroEvenEquiv` when `A^{0,1̄} = 0` | `k > 0`; `A^{j,•} = 0` for `j < 0` and `0 < j < k`; `A^{0,•}` graded semisimple as a `ℤ/2`-graded ring; `d(A^{0,•}) = 0`; chosen derived categories | Proved on weight-category compact `K₀` and super `K₀`; not a numerical computation |
| `M(m\|n)` and `Q(n)` are graded semisimple; superrings in internal degree `0` are positive | `Bigraded/GradedDivisionRing.lean`, `HalfGraded/PositiveSuper.lean` | `isGradedSemisimpleRing_superMatrix`, `isGradedSemisimpleRing_queerMatrix`, `HalfGradedDGRing.isPositive_ofSuper` | Division ring resp. field; matrices over any graded division ring | Proved |
| Odd units of internal degree `0` give `[Π X] = [X]` in `K₀` | `HalfGraded/PositiveSuper.lean` | `HalfGradedDGRing.IsPositive.mk_parityShiftCompact_eq_mk`, `clifford_mk_parityShiftCompact` | Positive; `c, c' ∈ A^{0,1̄}`, `c c' = 1`, `c' a c = a` on `A^{0,0̄}`; example `Cl₁` over a field | Proved |

## Errata

Some items of the roadmap were false as first stated; the library proves corrected versions and
records counterexamples.

- **3.5.** The lifting property against surjective quasi-isomorphisms is not equivalent to
  K-projectivity: it is equivalent to K-projectivity together with graded projectivity
  (`DG.hasLiftingProperty_iff`). Over `ℤ`, the cone of the identity of `ℚ` is contractible but
  not graded-projective.
- **6.5.** The Künneth formula `K₀(A ⊗_k B) ≅ K₀(A) ⊗ K₀(B)` needs the degree-zero parts to be
  split semisimple: `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` is a counterexample, and over an imperfect field the tensor
  product of positive dg algebras need not be positive.
- **7.3.** `A e A = A` does not imply `D(e A e) ≃ D(A)`
  (`DG/Examples/MoritaCounterexample.lean`); the equivalence holds when `[e]` generates `H⁰(A)` as
  a two-sided ideal (`DG.DGIdempotent.moritaEquivalence`), in particular for positive `A`.
- **D.5.** `K₀(C)` need not be generated by the classes of the representable modules (their
  direct summands may be needed, e.g. `k × k` in degree `0`).
- **6.2 (Schnürer's theorem).** The main theorem of O. M. Schnürer, *Perfect derived categories
  of positively graded DG algebras* (arXiv:0809.4782v2), is proved there as Theorems 13 and 16
  and needs no field hypothesis; it is formalized for left modules. Closure of the finite-cell
  modules under direct summands is proved directly in the derived category, avoiding the route
  through bounded t-structures.

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
axioms; `scripts/AxiomAudit.lean` checks that the axioms of every declaration are among
`propext`, `Classical.choice` and `Quot.sound`, and runs in CI.

## Models used

The code and proofs are produced with AI models under human direction and checked by Lean:

- Claude Opus 5.5
- Claude Fable 5.1

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
