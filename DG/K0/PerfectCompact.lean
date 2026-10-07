import DG.Derived.PerfectCompact
import DG.K0.DGRing
import DG.K0.PerfectComplex

/-!
# `K₀` of a commutative ring is `K₀` of its finitely generated projective modules

Let `R` be a commutative ring, regarded as a dg ring concentrated in degree `0`. Its Grothendieck
group `K₀(R) := K₀(D^c(R))` (`DG.DGRing.K0 R`, roadmap 5.5) is defined with the compact objects
of the derived category of dg modules. Under the comparison equivalence `D(R) ≌ D(Mod R)` the
compact objects are the perfect complexes (`DG.DerivedCategory.isCompact_iff_isPerfect`), whose
Grothendieck group is the Grothendieck group of finitely generated projective `R`-modules
(`DG.perfectK0Equiv`). Hence

  `K₀(R) ≃+ K₀(R-proj)`,   `[R] ↦ [R]`

(`DG.DGRing.K0.projK0Equiv`, roadmap 5.6), the isomorphism sending the class of a compact dg
module to the Euler characteristic `Σₙ (-1)ⁿ [Kⁿ]` of a perfect complex `K` representing it.

## Main definitions and results

* `DG.K0.fullSubcategoryMapEquiv e P P' h`: a triangulated equivalence `e : T ≌ T'` which maps
  a triangulated subcategory `P` onto a triangulated subcategory `P'` (`P X ↔ P' (e X)`) induces
  `K₀(P) ≃+ K₀(P')`.
* `DG.DGRing.K0.projK0Equiv R : DG.DGRing.K0 R ≃+ DG.ProjK0 R`, with
  `DG.DGRing.K0.projK0Equiv_self` (`[R] ↦ [R]`) and `DG.DGRing.K0.projK0Equiv_symm_mk`.
-/

open CategoryTheory Category Limits Pretriangulated

universe w u

namespace DG

namespace K0

variable {T : Type*} [Category T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
  {T' : Type*} [Category T'] [HasZeroObject T'] [HasShift T' ℤ] [Preadditive T']
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T']

/-- A triangulated equivalence `e : T ≌ T'` which maps the triangulated subcategory `P` of `T`
onto the triangulated subcategory `P'` of `T'` (closed under isomorphisms) induces an
isomorphism `K₀(P) ≃+ K₀(P')`, `[X] ↦ [e X]`. -/
noncomputable def fullSubcategoryMapEquiv (e : T ≌ T') [e.functor.CommShift ℤ]
    [e.functor.IsTriangulated] (P : ObjectProperty T) (P' : ObjectProperty T')
    [P.IsTriangulated] [P'.IsTriangulated] [P'.IsClosedUnderIsomorphisms]
    (h : ∀ X, P X ↔ P' (e.functor.obj X)) :
    K0 P.FullSubcategory ≃+ K0 P'.FullSubcategory :=
  letI := e.commShiftInverse ℤ
  haveI := e.commShift_of_functor ℤ
  haveI : e.inverse.IsTriangulated := e.toAdjunction.isTriangulated_rightAdjoint
  { toFun := map (P'.lift (P.ι ⋙ e.functor) fun X => (h X.obj).1 X.property)
    invFun := map (P.lift (P'.ι ⋙ e.inverse) fun Y =>
      (h _).2 (P'.prop_of_iso (e.counitIso.app Y.obj).symm Y.property))
    left_inv x := by
      induction x using induction_on with
      | zero => rw [map_zero, map_zero]
      | mk X =>
        rw [map_mk, map_mk]
        exact mk_eq_of_iso_obj (e.unitIso.app X.obj).symm
      | neg x hx => rw [map_neg, map_neg, hx]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    right_inv y := by
      induction y using induction_on with
      | zero => rw [map_zero, map_zero]
      | mk X =>
        rw [map_mk, map_mk]
        exact mk_eq_of_iso_obj (e.counitIso.app X.obj)
      | neg x hx => rw [map_neg, map_neg, hx]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    map_add' := map_add _ }

@[simp]
theorem fullSubcategoryMapEquiv_mk (e : T ≌ T') [e.functor.CommShift ℤ]
    [e.functor.IsTriangulated] (P : ObjectProperty T) (P' : ObjectProperty T')
    [P.IsTriangulated] [P'.IsTriangulated] [P'.IsClosedUnderIsomorphisms]
    (h : ∀ X, P X ↔ P' (e.functor.obj X)) (X : P.FullSubcategory) :
    fullSubcategoryMapEquiv e P P' h (mk X) =
      mk (⟨e.functor.obj X.obj, (h X.obj).1 X.property⟩ : P'.FullSubcategory) :=
  map_mk _ X

end K0

namespace DGRing.K0

open DegreeZero _root_.DG.DerivedCategory

variable (R : Type u) [CommRing R] [HasDerivedCategory.{u, u} R]

/-- `DG.DerivedCategory.isCompact_iff_isPerfect` in the form used by
`DG.K0.fullSubcategoryMapEquiv`. -/
theorem compactSubcategory_iff_isPerfect [_root_.HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (X : DerivedCategory R) : compactSubcategory.{u} (DerivedCategory R) X ↔
      IsPerfect R ((comparisonEquivalence R).functor.obj X) :=
  isCompact_iff_isPerfect R X

/-- **`K₀` of a commutative ring** (roadmap 5.6): for a commutative ring `R` concentrated in
degree `0`, the Grothendieck group `K₀(D^c(R))` of compact dg modules is isomorphic to the
Grothendieck group of finitely generated projective `R`-modules. The compact objects correspond
to the perfect complexes under `D(R) ≌ D(Mod R)` (`DG.DerivedCategory.isCompact_iff_isPerfect`),
and the class of a perfect complex `K` is sent to its Euler characteristic `Σₙ (-1)ⁿ [Kⁿ]`
(`DG.perfectK0Equiv`). -/
noncomputable def projK0Equiv : K0 R ≃+ ProjK0.{u} R :=
  letI := _root_.HasDerivedCategory.standard (ModuleCat.{u} R)
  (DG.K0.fullSubcategoryMapEquiv (comparisonEquivalence R) (compactSubcategory.{u} _) (IsPerfect R)
    (compactSubcategory_iff_isPerfect R)).trans (perfectK0Equiv R)

/-- The inverse of `K₀(R) ≃+ K₀(R-proj)` sends `[R]` to `[R]`. -/
theorem projK0Equiv_symm_self :
    (projK0Equiv R).symm (ProjK0.mk (ModuleCat.of R R) (IsFGProjective.self R)) =
      self R := by
  let := _root_.HasDerivedCategory.standard (ModuleCat.{u} R)
  rw [projK0Equiv, AddEquiv.symm_trans_apply, perfectK0Equiv_symm_mk, AddEquiv.symm_apply_eq,
    self, DG.K0.fullSubcategoryMapEquiv_mk]
  exact DG.K0.mk_eq_of_iso_obj (comparisonObjSelfIso R).symm

/-- The isomorphism `K₀(R) ≃+ K₀(R-proj)` sends `[R]` to `[R]`. -/
theorem projK0Equiv_self :
    projK0Equiv R (self R) = ProjK0.mk (ModuleCat.of R R) (IsFGProjective.self R) := by
  rw [← projK0Equiv_symm_self, AddEquiv.apply_symm_apply]

/-- The class of a dg module whose underlying complex is a perfect complex `K` is sent to the
Euler characteristic `Σₙ (-1)ⁿ [Kⁿ]`. -/
theorem projK0Equiv_mk_Q_obj (M : DGModuleCat.{u} R)
    (hM : IsPerfectComplex ((DGModuleCat.forget R R).obj M)) :
    projK0Equiv R (DG.K0.mk (⟨Q.obj M, isCompact_Q_obj_of_isPerfectComplex R M hM⟩ :
      PerfectDerivedCategory R)) = hM.eulerChar := by
  let := _root_.HasDerivedCategory.standard (ModuleCat.{u} R)
  rw [projK0Equiv, AddEquiv.trans_apply, DG.K0.fullSubcategoryMapEquiv_mk,
    ← perfectK0Equiv_mk_Q_obj hM]
  exact congrArg _ (DG.K0.mk_eq_of_iso_obj ((QCompComparisonIso R).app M))

end DGRing.K0

end DG
