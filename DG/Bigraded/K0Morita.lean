import DG.Bigraded.Morita
import DG.K0.Compact

/-!
# `K₀` and graded Morita theory

For an action of `ℤ` by triangulated functors on pretriangulated categories `𝒯`, `𝒯'`
(`DG.TriangulatedIntAction`), `K₀` is a `ℤ[q, q⁻¹]`-module with `qⁿ • [X] = [X⟨n⟩]`. A
homomorphism `K₀(𝒯) →+ K₀(𝒯')` commuting with the maps `K₀(⟨n⟩)` is `ℤ[q, q⁻¹]`-linear
(`DG.TriangulatedIntAction.map_smul_of_commute`).

Applied to the graded Morita equivalence `D(C_{eAe}) ≌ D(C_A)` of a bigraded dg ring `A` and an
idempotent cocycle `e` of bidegree `(0, 0)` which is full up to homotopy
(`DG.DGIdempotent.gradedMoritaEquivalence`), which commutes with the internal shifts
(`DG.DGIdempotent.gradedMoritaEquivalenceInternalShiftIso`), this gives the `K₀` corollary of
Roadmap 7.3 in the bigraded setting: an isomorphism of `ℤ[q, q⁻¹]`-modules
`K₀(D(C_{eAe})^c) ≅ K₀(D(C_A)^c)` (`DG.DGIdempotent.gradedK0MoritaEquiv`).
-/

open CategoryTheory Limits Pretriangulated

universe t w₂ v v' u u'

namespace DG

namespace TriangulatedIntAction

variable {𝒯 : Type u} [Category.{v} 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ] [Preadditive 𝒯]
  [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]
  {𝒯' : Type u'} [Category.{v'} 𝒯'] [HasZeroObject 𝒯'] [HasShift 𝒯' ℤ] [Preadditive 𝒯']
  [∀ n : ℤ, (shiftFunctor 𝒯' n).Additive] [Pretriangulated 𝒯']
  (σ : TriangulatedIntAction 𝒯) (τ : TriangulatedIntAction 𝒯')

/-- A homomorphism of Grothendieck groups commuting with the actions of the functors `⟨n⟩` is
`ℤ[q, q⁻¹]`-linear. -/
theorem map_smul_of_commute (φ : K0 𝒯 →+ K0 𝒯')
    (hφ : ∀ (n : ℤ) (x : K0 𝒯), φ (K0.map (σ.functor n) x) = K0.map (τ.functor n) (φ x))
    (p : LaurentPolynomial ℤ) (x : K0 𝒯) :
    letI := σ.K0Module
    letI := τ.K0Module
    φ (p • x) = p • φ x := by
  let := σ.K0Module
  let := τ.K0Module
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [add_smul, map_add, hp, hq, add_smul]
  | C_mul_T n a =>
    rw [mul_smul, mul_smul, σ.T_smul, τ.T_smul, eq_intCast LaurentPolynomial.C a,
      Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul, hφ]

/-- A homomorphism commuting with the actions, as a `ℤ[q, q⁻¹]`-linear map. -/
noncomputable def linearMapOfCommute (φ : K0 𝒯 →+ K0 𝒯')
    (hφ : ∀ (n : ℤ) (x : K0 𝒯), φ (K0.map (σ.functor n) x) = K0.map (τ.functor n) (φ x)) :
    letI := σ.K0Module
    letI := τ.K0Module
    K0 𝒯 →ₗ[LaurentPolynomial ℤ] K0 𝒯' :=
  letI := σ.K0Module
  letI := τ.K0Module
  { toFun := φ
    map_add' := map_add φ
    map_smul' := map_smul_of_commute σ τ φ hφ }

end TriangulatedIntAction

namespace DGIdempotent

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]
  [DGRing A] {e : DGIdempotent A} (he : e.val ∈ wgrading (M := A) 0)
  [CatModule.HasDerivedCategory.{max u t, max u t} (e.weightFamily he).Corner]
  [CatModule.HasDerivedCategory.{max u t, max u t} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{w₂, max u t} (e.weightFamily he).augment.Corner]
  [Fact (e.val ∈ wgrading (M := A) 0)]
  [CatModule.HasDerivedCategory.{max u t, max u t} (WeightCategory e.Corner)]

open CatModule.DerivedCategory in
/-- The isomorphism `K₀(D(C_{eAe})^c) ≃+ K₀(D(C_A)^c)` induced by the graded Morita equivalence
commutes with the internal shifts. -/
theorem gradedMorita_K0_map_internalShift (h : e.IsFullH0) (n : ℤ)
    (x : K0 (compactSubcategory.{max u t}
      (CatModule.DerivedCategory.{max u t, max u t} (WeightCategory e.Corner))).FullSubcategory) :
    K0.compactMapEquiv (gradedMoritaEquivalence.{t, w₂} he h)
        (K0.map ((compactInternalShiftAction e.Corner).functor n) x) =
      K0.map ((compactInternalShiftAction A).functor n)
        (K0.compactMapEquiv (gradedMoritaEquivalence.{t, w₂} he h) x) := by
  induction x using K0.induction_on with
  | zero => simp only [map_zero]
  | mk X =>
    simp only [K0.map_mk, K0.compactMapEquiv_mk]
    exact K0.mk_eq_of_iso_obj
      (((gradedMoritaEquivalenceInternalShiftIso.{t, w₂} he h n).app X.obj).symm)
  | neg x hx => simp only [map_neg, hx]
  | add x y hx hy => simp only [map_add, hx, hy]

open CatModule.DerivedCategory in
/-- **Graded Morita theory on `K₀`** (Roadmap 7.3, bigraded `K₀` corollary): for a bigraded dg
ring `A` and an idempotent cocycle `e` of bidegree `(0, 0)` which is full up to homotopy, the
graded Morita equivalence induces an isomorphism of `ℤ[q, q⁻¹]`-modules
`K₀(D(C_{eAe})^c) ≅ K₀(D(C_A)^c)` between the Grothendieck groups of compact bigraded dg
modules, where `qⁿ` acts by the internal shift `⟨n⟩`. -/
noncomputable def gradedK0MoritaEquiv (h : e.IsFullH0) :
    K0 (compactSubcategory.{max u t}
      (CatModule.DerivedCategory.{max u t, max u t} (WeightCategory e.Corner))).FullSubcategory ≃ₗ[
        LaurentPolynomial ℤ]
      K0 (compactSubcategory.{max u t}
        (CatModule.DerivedCategory.{max u t, max u t} (WeightCategory A))).FullSubcategory :=
  { TriangulatedIntAction.linearMapOfCommute (compactInternalShiftAction e.Corner)
      (compactInternalShiftAction A)
      (K0.compactMapEquiv (gradedMoritaEquivalence.{t, w₂} he h)).toAddMonoidHom
      (gradedMorita_K0_map_internalShift he h) with
    invFun := (K0.compactMapEquiv (gradedMoritaEquivalence.{t, w₂} he h)).symm
    left_inv := (K0.compactMapEquiv (gradedMoritaEquivalence.{t, w₂} he h)).left_inv
    right_inv := (K0.compactMapEquiv (gradedMoritaEquivalence.{t, w₂} he h)).right_inv }

theorem gradedK0MoritaEquiv_apply (h : e.IsFullH0)
    (x : K0 (compactSubcategory.{max u t}
      (CatModule.DerivedCategory.{max u t, max u t} (WeightCategory e.Corner))).FullSubcategory) :
    gradedK0MoritaEquiv.{t, w₂} he h x =
      K0.compactMapEquiv (gradedMoritaEquivalence.{t, w₂} he h) x :=
  rfl

end DGIdempotent

end DG
