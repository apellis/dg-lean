import DG.HalfGraded.DiagonalK0

/-!
# Functoriality of the diagonal `K₀` computation

Let `A`, `B` be dg rings with diagonal half-graded dg rings `H_A`, `H_B` and diagonal functors
`ι_A = toDerived A`, `ι_B = toDerived B`. Let `F : D(A) ⥤ D(B)` and
`G : D(C_{H_A}) ⥤ D(C_{H_B})` be triangulated functors preserving compact objects, such that `G`
commutes with the internal shifts and `G ∘ ι_A ≅ ι_B ∘ F` (objectwise isomorphisms suffice).
Then, under the identifications `K₀(D(C_H)^c) ≃ (ℤ[q, q⁻¹] ⧸ (q⁴ - 1)) ⊗ K₀(D(-)^c)` of
`DG.Diagonal.K0LinearEquiv`, the map induced by `G` is `id ⊗ K₀(F)`
(`DG.Diagonal.K0LinearEquiv_mapCompact`); the same holds for the compact super Grothendieck
groups (`DG.Diagonal.superK0LinearEquiv_superK0cMap`). The induced map on `K₀` is
`ℤ[q, q⁻¹]`-linear (`DG.Diagonal.mapCompactLinear`).

Typical instances: derived induction along a morphism of dg rings together with derived induction
along the induced weight dg functor, or derived tensor products with a dg bimodule and with its
diagonal counterpart. Constructing such a `G` from `F` is not done here.
-/

open CategoryTheory Limits LaurentPolynomial TensorProduct

universe w' w v u w₂' w₂ v₂ u₂

noncomputable section

namespace DG

namespace Diagonal

set_option backward.isDefEq.respectTransparency false

section Single

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, max u v} A]
  [CatModule.HasDerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

theorem K0LinearEquiv_smul_mapCompactK0 (p : LaurentPolynomial ℤ) (y : BaseK0.{w, v} A) :
    K0LinearEquiv.{w', w, v} A (p • mapCompactK0.{w', w, max u v} A y) = πP p ⊗ₜ y := by
  rw [← LinearEquiv.eq_symm_apply]
  exact (K0LinearEquiv_symm_tmul.{w', w, v} A p y).symm

theorem superK0LinearEquiv_apply
    (s : HalfGradedDGRing.SuperK0c.{w', v} (HalfGradedDGRing.ofDGRing A)) :
    superK0LinearEquiv.{w', w, v} A s = ofSuperK0.{w', w, v} A s := by
  apply toSuperK0_injective.{w', w, v} A
  exact (LinearEquiv.apply_symm_apply
    (LinearEquiv.ofBijective (toSuperK0.{w', w, v} A) _) s).trans
    (toSuperK0_ofSuperK0.{w', w, v} A s).symm

theorem superK0LinearEquiv_superK0cMk (x : DiagK0.{w', v} A) :
    superK0LinearEquiv.{w', w, v} A (HalfGradedDGRing.superK0cMk.{w', v} _ x) =
      reduceSuper.{w, v} A (K0LinearEquiv.{w', w, v} A x) :=
  (superK0LinearEquiv_apply.{w', w, v} A _).trans (ofSuperK0_superK0cMk.{w', w, v} A x)

end Single

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, max u v} A]
  [CatModule.HasDerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]
  (B : Type u₂) [Ring B] [DGAddCommGroup B] [DGRing B]
  [HasDerivedCategory.{w₂, max u₂ v₂} B]
  [CatModule.HasDerivedCategory.{w₂', max u₂ v₂}
    (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)]
  (F : DerivedCategory.{w, max u v} A ⥤ DerivedCategory.{w₂, max u₂ v₂} B)
  [F.CommShift ℤ] [F.IsTriangulated]
  (hF : ∀ X, IsCompact.{max u v} X → IsCompact.{max u₂ v₂} (F.obj X))
  (G : CatModule.DerivedCategory.{w', max u v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤
    CatModule.DerivedCategory.{w₂', max u₂ v₂}
      (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded))
  [G.CommShift ℤ] [G.IsTriangulated]
  (hG : ∀ X, IsCompact.{max u v} X → IsCompact.{max u₂ v₂} (G.obj X))

/-- A functor commuting with the internal shifts induces a `ℤ[q, q⁻¹]`-linear map on `K₀`. -/
def mapCompactLinear
    (eS : ∀ (n : ℤ) X, G.obj ((shiftDerived.{w', max u v} A n).obj X) ≅
      (shiftDerived.{w₂', max u₂ v₂} B n).obj (G.obj X)) :
    DiagK0.{w', v} A →ₗ[LaurentPolynomial ℤ] DiagK0.{w₂', v₂} B where
  toFun := K0.mapCompact G hG
  map_add' := map_add _
  map_smul' p z := by
    have hT : ∀ (n : ℤ) (z : DiagK0.{w', v} A), K0.mapCompact G hG ((T n : LaurentPolynomial ℤ) • z) =
        (T n : LaurentPolynomial ℤ) • K0.mapCompact G hG z := by
      intro n z
      induction z using K0.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | mk X =>
        exact (congrArg (K0.mapCompact G hG)
          (CatModule.DerivedCategory.T_smul_mk_compact (n := n) (M := X))).trans
          ((K0.mapCompact_mk G hG _).trans ((K0.mk_eq_of_iso_obj (eS n X.obj)).trans
            ((CatModule.DerivedCategory.T_smul_mk_compact (n := n)
              (M := ⟨G.obj X.obj, hG _ X.property⟩)).symm.trans
              (congrArg ((T n : LaurentPolynomial ℤ) • ·) (K0.mapCompact_mk G hG X).symm))))
      | neg x hx =>
        rw [_root_.smul_neg, (K0.mapCompact G hG).map_neg, (K0.mapCompact G hG).map_neg, hx,
          _root_.smul_neg]
      | add x y hx hy =>
        exact (congrArg _ (smul_add _ x y)).trans (((K0.mapCompact G hG).map_add _ _).trans
          ((congrArg₂ (· + ·) hx hy).trans ((smul_add _ _ _).symm.trans
            (congrArg _ ((K0.mapCompact G hG).map_add x y).symm))))
    rw [RingHom.id_apply]
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      exact (congrArg _ (add_smul p q z)).trans (((K0.mapCompact G hG).map_add _ _).trans
        ((congrArg₂ (· + ·) hp hq).trans (add_smul p q _).symm))
    | C_mul_T n a =>
      exact (congrArg _ ((mul_smul _ _ z).trans (HalfGradedDGRing.Field.C_smul a _))).trans
        ((map_zsmul (K0.mapCompact G hG) a _).trans ((congrArg (a • ·) (hT n z)).trans
          ((HalfGradedDGRing.Field.C_smul a _).symm.trans (mul_smul _ _ _).symm)))

omit [HasDerivedCategory.{w, max u v} A] [HasDerivedCategory.{w₂, max u₂ v₂} B] in
theorem mapCompactLinear_apply
    (eS : ∀ (n : ℤ) X, G.obj ((shiftDerived.{w', max u v} A n).obj X) ≅
      (shiftDerived.{w₂', max u₂ v₂} B n).obj (G.obj X)) (z : DiagK0.{w', v} A) :
    mapCompactLinear A B G hG eS z = K0.mapCompact G hG z := rfl

/-- **Functoriality.** If `G` commutes with the internal shifts and `G ∘ ι_A ≅ ι_B ∘ F`, then the
map induced by `G` on `K₀` of compact objects is `id ⊗ K₀(F)` under `K0LinearEquiv`. -/
theorem K0LinearEquiv_mapCompact
    (eS : ∀ (n : ℤ) X, G.obj ((shiftDerived.{w', max u v} A n).obj X) ≅
      (shiftDerived.{w₂', max u₂ v₂} B n).obj (G.obj X))
    (eι : ∀ Y, G.obj ((toDerived.{w', w, max u v} A).obj Y) ≅
      (toDerived.{w₂', w₂, max u₂ v₂} B).obj (F.obj Y))
    (x : DiagK0.{w', v} A) :
    K0LinearEquiv.{w₂', w₂, v₂} B (K0.mapCompact G hG x) =
      LinearMap.lTensor _ (K0.mapCompact F hF).toIntLinearMap
        (K0LinearEquiv.{w', w, v} A x) := by
  have hι : ∀ y : BaseK0.{w, v} A, K0.mapCompact G hG (mapCompactK0.{w', w, max u v} A y) =
      mapCompactK0.{w₂', w₂, max u₂ v₂} B (K0.mapCompact F hF y) := by
    intro y
    induction y using K0.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | mk Y =>
      rw [mapCompactK0_mk, K0.mapCompact_mk, K0.mapCompact_mk, mapCompactK0_mk]
      exact K0.mk_eq_of_iso_obj (eι Y.obj)
    | neg x hx => rw [map_neg, map_neg, hx, map_neg, map_neg]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have key : ∀ t : (LaurentPolynomial ℤ ⧸ periodIdeal) ⊗[ℤ] BaseK0.{w, v} A,
      K0LinearEquiv.{w₂', w₂, v₂} B (K0.mapCompact G hG (toK0.{w', w, v} A t)) =
        LinearMap.lTensor _ (K0.mapCompact F hF).toIntLinearMap t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul p y =>
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
      have h1 := (mapCompactLinear A B G hG eS).map_smul p (mapCompactK0.{w', w, max u v} A y)
      rw [mapCompactLinear_apply, mapCompactLinear_apply, hι] at h1
      rw [toK0_tmul, h1, K0LinearEquiv_smul_mapCompactK0, LinearMap.lTensor_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  have hx : x = toK0.{w', w, v} A (K0LinearEquiv.{w', w, v} A x) := by
    rw [K0LinearEquiv_apply, toK0_ofK0]
  conv_lhs => rw [hx]
  exact key _

/-- **Functoriality for the compact super Grothendieck groups.** Under the hypotheses of
`K0LinearEquiv_mapCompact`, the descended map on `SuperK0c` is `id ⊗ K₀(F)` under
`superK0LinearEquiv`. -/
theorem superK0LinearEquiv_superK0cMap
    (eS : ∀ (n : ℤ) X, G.obj ((shiftDerived.{w', max u v} A n).obj X) ≅
      (shiftDerived.{w₂', max u₂ v₂} B n).obj (G.obj X))
    (eι : ∀ Y, G.obj ((toDerived.{w', w, max u v} A).obj Y) ≅
      (toDerived.{w₂', w₂, max u₂ v₂} B).obj (F.obj Y))
    (s : HalfGradedDGRing.SuperK0c.{w', v} (HalfGradedDGRing.ofDGRing A)) :
    superK0LinearEquiv.{w₂', w₂, v₂} B
      (HalfGradedDGRing.superK0cMap _ _ (mapCompactLinear A B G hG eS) s) =
      LinearMap.lTensor _ (K0.mapCompact F hF).toIntLinearMap
        (superK0LinearEquiv.{w', w, v} A s) := by
  obtain ⟨x, rfl⟩ := HalfGradedDGRing.superK0cMk_surjective.{w', v} _ s
  rw [HalfGradedDGRing.superK0cMap_mk, superK0LinearEquiv_superK0cMk,
    superK0LinearEquiv_superK0cMk, mapCompactLinear_apply,
    K0LinearEquiv_mapCompact A B F hF G hG eS eι x]
  generalize K0LinearEquiv.{w', w, v} A x = t
  induction t using TensorProduct.inductionOn with
  | tmul p y =>
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Diagonal

end DG
