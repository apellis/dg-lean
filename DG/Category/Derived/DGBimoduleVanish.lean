import DG.Category.Derived.DGBimodule
import DG.Category.Derived.TensorInduction
import DG.Category.Derived.TensorIso
import DG.Category.Derived.InductionComp

/-!
# Vanishing and comparison results for derived tensor products with dg bimodules

* `DG.CatModule.isAcyclic_hom_of_isContractible`: for a contractible dg module `M` over a dg
  category, every Hom complex `HOM(M, N)` is acyclic (a cocycle of degree `n` is a morphism
  `M ⟶ N⟦n⟧`, null-homotopic since `M` is contractible);
* `DG.CatModule.DerivedCategory.derivedTensor_isZero_obj`: if every `B(-, Y)` of a dg bimodule `B`
  is contractible, `B ⊗^L (-)` sends every object to a zero object (its right adjoint
  `RHOM(B, -)` does, `DG.CatModule.DerivedCategory.rhom_isZero_obj`);
* `DG.DGBimodule.derivedTensor_isZero_obj`: for dg rings, if the dg bimodule `M` is K-projective
  and acyclic as a left dg `A`-module, then `M ⊗^L_B (-) : D(B) ⥤ D(A)` sends every object to a
  zero object;
* `DG.DGBimodule.derivedTensorIsoInduction`: if `M ≅ A` as dg `(A, B)`-bimodules, with right
  action through a morphism of dg rings `φ : B → A`, then `M ⊗^L_B (-) ≅ φ^*` (derived induction);
* `DG.DGRingHom.derivedInductionCompIso`: derived induction along `ψ ∘ φ` is derived induction
  along `φ` followed by derived induction along `ψ`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory Limits MulOpposite

universe w₁ w₂ w₃ w₄ w v v₁ v₂ u₁ u₂

namespace DG

namespace CatModule

section CatModule

variable {C : Type*} [Category C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]

/-- For a contractible dg module `M` over a dg category, every Hom complex `HOM(M, N)` is acyclic. -/
theorem isAcyclic_hom_of_isContractible {M : CatModule C} (hM : CatModule.IsContractible M)
    (N : CatModule C) : DG.IsAcyclic (CatModule.HOM M N) := by
  refine CatModule.isAcyclic_hom_iff.mpr fun n m hmn z hz => ?_
  have hz' : CatModule.δ 0 1 (z.rightShift n 0 (zero_add n)) = 0 := by
    rw [CatModule.Cochain.δ_rightShift z n 0 1 (zero_add n) (n + 1) (add_comm 1 n), hz,
      CatModule.Cochain.rightShift_zero, _root_.smul_zero]
  obtain ⟨h, hh⟩ := CatModule.homotopic_zero_iff_exists.mp
    (hM.homotopic_zero_of_left
      (CatModule.Cocycle.homOf (CatModule.Cocycle.mk _ 1 (zero_add 1) hz')))
  refine ⟨koszulSign n • h.rightUnshift m (by omega), ?_⟩
  rw [CatModule.δ_units_smul, CatModule.Cochain.δ_rightUnshift h m (by omega) n 0 (zero_add n), smul_smul,
    Int.units_mul_self, one_smul, ← hh, CatModule.Cocycle.cochain_ofHom_homOf_eq_coe,
    CatModule.Cocycle.mk_coe, CatModule.Cochain.rightUnshift_rightShift]

end CatModule

end CatModule

namespace CatModule.DerivedCategory

section Derived

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]
  (B : CatBimodule.{max u₁ u₂ v₁ w} D C) (hB : ∀ Y : C, CatModule.IsKProjective (B.left Y))
  [CatModule.HasDerivedCategory.{w₁, max u₁ u₂ v₁ w} C] [CatModule.HasDerivedCategory.{w₂, max u₁ u₂ v₁ w} D]

/-- If every `B(-, Y)` is contractible, `RHOM(B, -)` sends every object to a zero object. -/
theorem rhom_isZero_obj (hc : ∀ Y, CatModule.IsContractible (B.left Y))
    (W : CatModule.DerivedCategory.{w₂, max u₁ u₂ v₁ w} D) :
    IsZero ((CatModule.DerivedCategory.rhom B hB).obj W) := by
  have := Localization.essSurj (CatModule.DerivedCategory.Q (C := D)) (CatModule.quasiIso D)
  refine IsZero.of_iso ?_ ((CatModule.DerivedCategory.rhom B hB).mapIso
    (CatModule.DerivedCategory.Q.objObjPreimageIso W).symm)
  refine IsZero.of_iso ?_ ((CatModule.DerivedCategory.QCompRhomIso B hB).app _)
  exact (CatModule.DerivedCategory.isZero_Q_obj_iff _).mpr fun Y =>
    CatModule.isAcyclic_hom_of_isContractible (hc Y) _

/-- If every `B(-, Y)` is contractible, `B ⊗^L (-)` sends every object to a zero object. -/
theorem derivedTensor_isZero_obj (hc : ∀ Y, CatModule.IsContractible (B.left Y))
    (X : CatModule.DerivedCategory.{w₁, max u₁ u₂ v₁ w} C) :
    IsZero ((CatModule.DerivedCategory.derivedTensor.{w₁, w₂} B hB).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((CatModule.DerivedCategory.derivedTensorAdjunction B hB).homEquiv _ _).injective
  exact (rhom_isZero_obj B hB hc _).eq_of_tgt _ _

end Derived

end CatModule.DerivedCategory

namespace DGBimodule

section Ring


variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B] [DGRing B]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [DGBimodule A B M]
  (hM : DG.IsKProjective.{v} A M)
  [CatModule.HasDerivedCategory.{w₁, v} (SingleObj B)] [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- **`M ⊗^L_B (-)` vanishes when `M` is K-projective and acyclic as a left dg `A`-module.** -/
theorem derivedTensor_isZero_obj (hac : DG.IsAcyclic M) (Y : DG.DerivedCategory.{w₃, v} B) :
    IsZero ((derivedTensor.{w₁, w₂, w₃, w₄} A B M hM).obj Y) :=
  (CatModule.DerivedCategory.singleObjEquivalence A).functor.map_isZero
    (CatModule.DerivedCategory.derivedTensor_isZero_obj _ (catBimodule_left_isKProjective A B M hM)
      (fun Y => catBimodule_left_isKProjective A B M hM Y _ (fun _ => hac) (𝟙 _)) _)

end Ring

section OfFunctor

variable {A B : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (φ : B →ᵈᵍ+* A) {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [DGBimodule A B M]

/-- An isomorphism of `M` with `A` (left action by multiplication, right action through `φ`)
as an isomorphism of dg bimodules over the one-object dg categories. -/
def catBimoduleIsoOfFunctor (e : M ≃+ A)
    (he : ∀ {n : ℤ} {m : M}, e m ∈ grading n ↔ m ∈ grading n)
    (hd : ∀ m : M, e (d m) = d (e m)) (hl : ∀ (a : A) (m : M), e (a • m) = a * e m)
    (hr : ∀ (b : B) (m : M), e (op b • m) = e m * φ b) :
    CatBimodule.Iso (catBimodule A B M) (CatBimodule.ofFunctor φ.singleObjFunctor) where
  left _ := CatModule.isoMk (fun _ => e) he hd (fun f m => hl f m)
  ract g _ x := hr g x

variable [CatModule.HasDerivedCategory.{v, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₂, v} (SingleObj A)]
  [DG.HasDerivedCategory.{w₃, v} B] [DG.HasDerivedCategory.{w₄, v} A]

/-- **`M ⊗^L_B - ≅ φ^*`** for `M ≅ A` as above. -/
def derivedTensorIsoInduction (hM : IsKProjective.{v} A M) (e : M ≃+ A)
    (he : ∀ {n : ℤ} {m : M}, e m ∈ grading n ↔ m ∈ grading n)
    (hd : ∀ m : M, e (d m) = d (e m)) (hl : ∀ (a : A) (m : M), e (a • m) = a * e m)
    (hr : ∀ (b : B) (m : M), e (op b • m) = e m * φ b) :
    derivedTensor.{v, w₂, w₃, w₄} A B M hM ≅ φ.derivedInduction.{v, w₂, w₃, w₄} :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    (CatModule.DerivedCategory.derivedTensorIso (catBimoduleIsoOfFunctor φ e he hd hl hr) _ _) _) ≪≫
    (φ.derivedInductionIsoDerivedTensor).symm

end OfFunctor

end DGBimodule

namespace DGRingHom

section Comp

variable {A B C : Type v} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B] [DGRing B]
  [Ring C] [DGAddCommGroup C] [DGRing C]
  [CatModule.HasDerivedCategory.{w₁, v} (SingleObj A)] [CatModule.HasDerivedCategory.{w₁, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{w₁, v} (SingleObj C)]
  [DG.HasDerivedCategory.{w₂, v} A] [DG.HasDerivedCategory.{w₂, v} B] [DG.HasDerivedCategory.{w₂, v} C]

theorem singleObjFunctor_comp (φ : C →ᵈᵍ+* B) (ψ : B →ᵈᵍ+* A) :
    (ψ.comp φ).singleObjFunctor = φ.singleObjFunctor ⋙ ψ.singleObjFunctor := rfl

/-- **Derived induction along `ψ ∘ φ` is derived induction along `φ` followed by derived induction along `ψ`.** -/
def derivedInductionCompIso (φ : C →ᵈᵍ+* B) (ψ : B →ᵈᵍ+* A) :
    (ψ.comp φ).derivedInduction.{w₁, w₁, w₂, w₂} ≅
      φ.derivedInduction.{w₁, w₁, w₂, w₂} ⋙ ψ.derivedInduction.{w₁, w₁, w₂, w₂} :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (CatModule.DerivedCategory.inductionCompIso φ.singleObjFunctor ψ.singleObjFunctor) _) ≪≫
    Functor.isoWhiskerLeft ((CatModule.DerivedCategory.singleObjEquivalence C).inverse ⋙
        CatModule.DerivedCategory.induction.{w₁, w₁, v} φ.singleObjFunctor)
      (Functor.isoWhiskerRight (CatModule.DerivedCategory.singleObjEquivalence B).unitIso
        (CatModule.DerivedCategory.induction.{w₁, w₁, v} ψ.singleObjFunctor ⋙
          (CatModule.DerivedCategory.singleObjEquivalence A).functor))

end Comp

end DGRingHom

end DG
