import DG.Derived.PerfectThick
import DG.K0.Compact

/-!
# `K₀` of perfect complexes

Let `R` be a ring. The perfect objects of the derived category of `R`-modules
(`DG.IsPerfect R`, the objects isomorphic to a strictly bounded complex of finitely generated
projective modules) form a thick triangulated subcategory `D^perf(R)` (`DG.IsPerfect.isThick`).
This file proves that its Grothendieck group is the Grothendieck group `K₀(R)` of finitely
generated projective `R`-modules (`DG.ProjK0 R`):

  `K₀(D^perf(R)) ≃+ K₀(R)`,   `[X] ↦ χ(X)`,   `[P] ↤ [P]`,

where `χ(X) = Σₙ (-1)ⁿ [Kⁿ]` is the Euler characteristic of any perfect complex `K` representing
`X` (compare C. A. Weibel, *The K-book*, Chapter II, §9, on Euler characteristics of bounded
complexes).

## Main definitions and results

* `DG.IsPerfect.eulerChar X hX : DG.ProjK0 R`: the Euler characteristic of a perfect object,
  independent of the perfect complex representing it (`DG.IsPerfect.eulerChar_eq`), invariant
  under isomorphisms and additive on distinguished triangles (`DG.IsPerfect.eulerChar_obj₂`).
* `DG.IsPerfect.K0Equiv P hP : K₀(P) ≃+ DG.ProjK0 R` for any description `P` of the perfect
  objects (`hP : ∀ X, P X ↔ DG.IsPerfect R X`, with `P` a triangulated subcategory closed under
  isomorphisms). The flexibility in `P` allows to apply the result to other descriptions of the
  perfect objects, e.g. as the compact objects.
* `DG.perfectK0Equiv R : K₀(D^perf(R)) ≃+ DG.ProjK0 R`, with `DG.perfectK0Equiv_mk` and
  `DG.perfectK0Equiv_symm_mk`.
-/

open CategoryTheory Category Limits Pretriangulated ZeroObject

universe w u

namespace DG

variable {R : Type u} [Ring R] [_root_.HasDerivedCategory.{w} (ModuleCat.{u} R)]

namespace IsPerfect

/-! ### The Euler characteristic of a perfect object -/

/-- The Euler characteristic `χ(X) ∈ K₀(R)` of a perfect object of the derived category: the
Euler characteristic `Σₙ (-1)ⁿ [Kⁿ]` of a perfect complex `K` representing it. -/
noncomputable def eulerChar (X : _root_.DerivedCategory (ModuleCat.{u} R))
    (hX : IsPerfect R X) : ProjK0.{u} R :=
  hX.choose_spec.choose.eulerChar

/-- The Euler characteristic of a perfect object can be computed from any perfect complex
representing it. -/
theorem eulerChar_eq {X : _root_.DerivedCategory (ModuleCat.{u} R)} (hX : IsPerfect R X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsPerfectComplex K)
    (e : _root_.DerivedCategory.Q.obj K ≅ X) : eulerChar X hX = hK.eulerChar :=
  IsPerfectComplex.eulerChar_eq_of_iso_Q _ hK (hX.choose_spec.choose_spec.some ≪≫ e.symm)

/-- Isomorphic perfect objects have the same Euler characteristic. -/
theorem eulerChar_eq_of_iso {X Y : _root_.DerivedCategory (ModuleCat.{u} R)} (e : X ≅ Y)
    (hX : IsPerfect R X) (hY : IsPerfect R Y) : eulerChar X hX = eulerChar Y hY := by
  have hY' := hY
  obtain ⟨K, hK, ⟨e'⟩⟩ := hY'
  rw [eulerChar_eq hY hK e', eulerChar_eq hX hK (e' ≪≫ e.symm)]

/-- The Euler characteristic of a finitely generated projective module placed in degree `n`. -/
theorem eulerChar_singleFunctor_obj {M : ModuleCat.{u} R} (hM : IsFGProjective R M) (n : ℤ)
    (h : IsPerfect R ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj M)) :
    eulerChar _ h = n.negOnePow • ProjK0.mk M hM := by
  rw [eulerChar_eq h (IsPerfectComplex.single hM n) (singleFunctorObjIso n M).symm,
    IsPerfectComplex.eulerChar_single]

/-- **Additivity of the Euler characteristic**: `χ(Y) = χ(X) + χ(Z)` for a distinguished
triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` of perfect objects. -/
theorem eulerChar_obj₂ (T : Triangle (_root_.DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : IsPerfect R T.obj₁) (h₂ : IsPerfect R T.obj₂)
    (h₃ : IsPerfect R T.obj₃) :
    eulerChar T.obj₂ h₂ = eulerChar T.obj₁ h₁ + eulerChar T.obj₃ h₃ := by
  have h₁' := h₁
  have h₂' := h₂
  obtain ⟨K, hK, ⟨e₁⟩⟩ := h₁'
  obtain ⟨L, hL, ⟨e₂⟩⟩ := h₂'
  obtain ⟨g, ⟨e₃⟩⟩ := exists_iso_mappingCone T hT hK e₁ e₂
  rw [eulerChar_eq h₁ hK e₁, eulerChar_eq h₂ hL e₂, eulerChar_eq h₃ (hK.mappingCone g hL) e₃,
    hK.eulerChar_mappingCone g hL, add_sub_cancel]

/-! ### The comparison of Grothendieck groups -/

section K0

variable (P : ObjectProperty (_root_.DerivedCategory (ModuleCat.{u} R))) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] (hP : ∀ X, P X ↔ IsPerfect R X)

/-- The homomorphism `K₀(D^perf(R)) →+ K₀(R)`, `[X] ↦ χ(X)`. -/
noncomputable def K0ToProjK0 : K0 P.FullSubcategory →+ ProjK0.{u} R :=
  K0.lift (fun X => eulerChar X.obj ((hP _).1 X.property)) (fun T hT =>
    eulerChar_obj₂ (P.ι.mapTriangle.obj T) (P.ι.map_distinguished T hT)
      ((hP _).1 T.obj₁.property) ((hP _).1 T.obj₂.property) ((hP _).1 T.obj₃.property))

omit [P.IsClosedUnderIsomorphisms] in
@[simp]
theorem K0ToProjK0_mk [P.IsClosedUnderIsomorphisms] (X : P.FullSubcategory) :
    K0ToProjK0 P hP (K0.mk X) = eulerChar X.obj ((hP _).1 X.property) :=
  K0.lift_mk _ _ X

/-- The homomorphism `K₀(R) →+ K₀(D^perf(R))`, `[M] ↦ [M[0]]`: a short exact sequence of
finitely generated projective modules gives a distinguished triangle of the derived category
(`ShortComplex.ShortExact.singleTriangle_distinguished`). -/
noncomputable def projK0ToK0 : ProjK0.{u} R →+ K0 P.FullSubcategory :=
  ProjK0.lift (fun M hM => K0.mk (⟨(_root_.DerivedCategory.singleFunctor _ 0).obj M,
      (hP _).2 (singleFunctor_obj hM 0)⟩ : P.FullSubcategory))
    (fun _ hS h₁ h₂ h₃ => K0.mk_fullSubcategory_obj₂ _ hS.singleTriangle_distinguished
      ((hP _).2 (singleFunctor_obj h₁ 0)) ((hP _).2 (singleFunctor_obj h₂ 0))
      ((hP _).2 (singleFunctor_obj h₃ 0)))

omit [P.IsClosedUnderIsomorphisms] in
@[simp]
theorem projK0ToK0_mk [P.IsClosedUnderIsomorphisms] (M : ModuleCat.{u} R) (hM : IsFGProjective R M) :
    projK0ToK0 P hP (ProjK0.mk M hM) = K0.mk (⟨(_root_.DerivedCategory.singleFunctor _ 0).obj M,
      (hP _).2 (singleFunctor_obj hM 0)⟩ : P.FullSubcategory) :=
  ProjK0.lift_mk _ _ M hM

theorem K0ToProjK0_projK0ToK0 (x : ProjK0.{u} R) :
    K0ToProjK0 P hP (projK0ToK0 P hP x) = x := by
  induction x using ProjK0.induction_on with
  | zero => rw [map_zero, map_zero]
  | mk M hM =>
    rw [projK0ToK0_mk, K0ToProjK0_mk, eulerChar_singleFunctor_obj hM, Int.negOnePow_zero,
      one_smul]
  | neg x hx => rw [map_neg, map_neg, hx]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The class of a perfect object is the image of its Euler characteristic: perfect objects are
iterated extensions of finitely generated projective modules placed in single degrees. -/
theorem projK0ToK0_eulerChar (X : P.FullSubcategory) :
    projK0ToK0 P hP (eulerChar X.obj ((hP _).1 X.property)) = K0.mk X := by
  suffices h : ∀ (X : _root_.DerivedCategory (ModuleCat.{u} R)) (hX : IsPerfect R X)
      (h : P X), projK0ToK0 P hP (eulerChar X hX) = K0.mk (⟨X, h⟩ : P.FullSubcategory) from
    h X.obj _ X.property
  refine fun X hX => IsPerfect.induction (motive := fun X hX => ∀ h : P X,
    projK0ToK0 P hP (eulerChar X hX) = K0.mk (⟨X, h⟩ : P.FullSubcategory)) ?_ ?_ ?_ ?_ hX
  · intro X Y hX hY e ih h
    rw [← eulerChar_eq_of_iso e hX hY, ih ((hP _).2 hX)]
    exact K0.mk_eq_of_iso_obj e
  · intro M hM h
    rw [eulerChar_singleFunctor_obj hM, Int.negOnePow_zero, one_smul, projK0ToK0_mk]
  · intro X hX n ih h
    have h₂ : K0.mk (⟨_, h⟩ : P.FullSubcategory) =
        K0.mk ((⟨X, (hP _).2 hX⟩ : P.FullSubcategory)⟦n⟧) :=
      K0.mk_eq_of_iso_obj ((P.ι.commShiftIso n).app ⟨X, (hP _).2 hX⟩).symm
    have h₁ : (n.negOnePow : ℤ) • eulerChar X hX = eulerChar (X⟦n⟧) (hX.shift n) := by
      have h₃ := K0ToProjK0_mk P hP ⟨_, h⟩
      rw [h₂, K0.mk_shift, Units.smul_def, map_zsmul, K0ToProjK0_mk] at h₃
      exact h₃
    rw [← h₁, map_zsmul, ih ((hP _).2 hX), h₂, K0.mk_shift, Units.smul_def]
  · intro T hT h₁ h₂ h₃ ih₁ ih₃ h
    rw [eulerChar_obj₂ T hT h₁ h₂ h₃, map_add, ih₁ ((hP _).2 h₁), ih₃ ((hP _).2 h₃)]
    exact (K0.mk_fullSubcategory_obj₂ T hT _ _ _).symm

theorem projK0ToK0_K0ToProjK0 (x : K0 P.FullSubcategory) :
    projK0ToK0 P hP (K0ToProjK0 P hP x) = x := by
  induction x using K0.induction_on with
  | zero => rw [map_zero, map_zero]
  | mk X => rw [K0ToProjK0_mk, projK0ToK0_eulerChar]
  | neg x hx => rw [map_neg, map_neg, hx]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **`K₀` of perfect complexes**: the Grothendieck group of the triangulated category of perfect
objects of the derived category of `R`-modules is the Grothendieck group of finitely generated
projective `R`-modules, via the Euler characteristic. The perfect objects are given by any
property `P` equivalent to `DG.IsPerfect R`. -/
noncomputable def K0Equiv : K0 P.FullSubcategory ≃+ ProjK0.{u} R where
  toFun := K0ToProjK0 P hP
  invFun := projK0ToK0 P hP
  left_inv := projK0ToK0_K0ToProjK0 P hP
  right_inv := K0ToProjK0_projK0ToK0 P hP
  map_add' := map_add _

@[simp]
theorem K0Equiv_mk (X : P.FullSubcategory) :
    K0Equiv P hP (K0.mk X) = eulerChar X.obj ((hP _).1 X.property) :=
  K0ToProjK0_mk P hP X

@[simp]
theorem K0Equiv_symm_mk (M : ModuleCat.{u} R) (hM : IsFGProjective R M) :
    (K0Equiv P hP).symm (ProjK0.mk M hM) =
      K0.mk (⟨(_root_.DerivedCategory.singleFunctor _ 0).obj M,
        (hP _).2 (singleFunctor_obj hM 0)⟩ : P.FullSubcategory) :=
  projK0ToK0_mk P hP M hM

end K0

end IsPerfect

variable (R) in
/-- **`K₀(D^perf(R)) ≃+ K₀(R)`**: the Grothendieck group of the triangulated category of perfect
complexes over a ring `R` is isomorphic to the Grothendieck group of finitely generated
projective `R`-modules. The isomorphism sends the class of a perfect complex `K` to its Euler
characteristic `Σₙ (-1)ⁿ [Kⁿ]`, and its inverse sends `[M]` to the class of `M` placed in
degree `0`. -/
noncomputable def perfectK0Equiv : K0 (IsPerfect R).FullSubcategory ≃+ ProjK0.{u} R :=
  IsPerfect.K0Equiv (IsPerfect R) fun _ => Iff.rfl

/-- The class of a perfect complex `K` corresponds to its Euler characteristic
`Σₙ (-1)ⁿ [Kⁿ]`. -/
theorem perfectK0Equiv_mk_Q_obj {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsPerfectComplex K) :
    perfectK0Equiv R (K0.mk ⟨_root_.DerivedCategory.Q.obj K, IsPerfect.Q_obj hK⟩) =
      hK.eulerChar :=
  (IsPerfect.K0Equiv_mk _ _ _).trans (IsPerfect.eulerChar_eq _ hK (Iso.refl _))

/-- The class of a finitely generated projective module corresponds to the class of the module
placed in degree `0`. -/
theorem perfectK0Equiv_symm_mk (M : ModuleCat.{u} R) (hM : IsFGProjective R M) :
    (perfectK0Equiv R).symm (ProjK0.mk M hM) =
      K0.mk ⟨(_root_.DerivedCategory.singleFunctor _ 0).obj M,
        IsPerfect.singleFunctor_obj hM 0⟩ :=
  IsPerfect.K0Equiv_symm_mk _ _ M hM

end DG
