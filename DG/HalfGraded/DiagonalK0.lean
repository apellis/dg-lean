import DG.HalfGraded.DiagonalBlocks
import DG.HalfGraded.Field
import DG.HalfGraded.SuperK0Linear
import DG.Derived.KProjective
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Grothendieck groups of diagonal half-graded dg rings

Let `A` be a dg ring and `H = HalfGradedDGRing.ofDGRing A` its diagonal half-graded dg ring
(parameter `k = 2`), with weight dg category `C_H`. Write `ι = toDerived A : D(A) ⥤ D(C_H)` and
`q` for the internal shift `⟨1⟩`, so that `K₀(D(C_H)^c)` is a `ℤ[q, q⁻¹]`-module. We prove

`K₀(D(C_H)^c) ≃ₗ[ℤ[q, q⁻¹]] (ℤ[q, q⁻¹] ⧸ (q⁴ - 1)) ⊗[ℤ] K₀(D(A)^c)`,   `[ι X] ↦ 1 ⊗ [X]`

(`DG.Diagonal.K0LinearEquiv`), and the corresponding statement for the compact super
Grothendieck group,

`SuperK0c H ≃ₗ[ℤ[q, q⁻¹]] (ℤ[q, q⁻¹] ⧸ (1 + q²)) ⊗[ℤ] K₀(D(A)^c)`

(`DG.Diagonal.superK0LinearEquiv`). No hypothesis on `A` is needed.

The inverse of the first map is `x ↦ ∑_{r=0}^{3} q⁻ʳ ⊗ ρ_r(x)`, where
`ρ_j : K₀(D(C_H)^c) → K₀(D(A)^c)` is induced by `X ↦ R₀(X⟨j⟩)` (weight-zero derived recovery
after the internal shift, `DG.Diagonal.recoveryK0`). The proof uses the block decomposition
`X ≅ ⨁_{r=0}^{3} (ι (R₀ (X⟨r⟩)))⟨-r⟩` (`DG.Diagonal.blocksDerivedIso`), the vanishing of
`R₀ ((ι Y)⟨j⟩)` for `j ∉ 4ℤ`, and `q⁴ = 1` on `K₀(D(C_H)^c)`, which holds for every half-graded
dg ring with parameter `k` in the form `q²ᵏ = 1`, because `Π Π ≅ 𝟭` and `[Π X] = -q⁻ᵏ [X]`
(`DG.HalfGradedDGRing.T_two_mul_smul_compactK0`).
-/

open CategoryTheory Limits Pretriangulated LaurentPolynomial TensorProduct

universe w' w v u

noncomputable section

namespace DG

namespace HalfGradedDGRing

variable {A : Type u} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)
  [CatModule.HasDerivedCategory.{w', max u w} (WeightCategory H.Regraded)]

/-- `q²ᵏ` acts trivially on `K₀(D(C_H)^c)`, for every half-graded dg ring: `Π Π ≅ 𝟭` and
`[Π X] = -q⁻ᵏ [X]`. -/
theorem T_two_mul_smul_compactK0 (x : CompactK0.{w', w} H) :
    (T (2 * k) : LaurentPolynomial ℤ) • x = x := by
  have h : ∀ x : CompactK0.{w', w} H, (T (-(2 * k)) : LaurentPolynomial ℤ) • x = x := by
    intro x
    induction x using K0.induction_on with
    | zero => exact smul_zero _
    | mk X =>
      have e := K0.mk_eq_of_iso ((compactSubcategory _).fullyFaithfulι.preimageIso
        (X := parityShiftCompact.{w', w} H (parityShiftCompact.{w', w} H X)) (Y := X)
        ((parityShiftDIso.{w'} H).app X.obj))
      rw [mk_parityShiftCompact, mk_parityShiftCompact, _root_.smul_neg, neg_neg, smul_smul,
        ← T_add] at e
      rw [show -(2 * k) = -k + -k by ring, e]
    | neg x hx => rw [_root_.smul_neg, hx]
    | add x y hx hy => rw [_root_.smul_add, hx, hy]
  conv_lhs => rw [← h x, smul_smul, ← T_add, add_neg_cancel, T_zero, one_smul]

/-- `q²ᵏᵐ` acts trivially on `K₀(D(C_H)^c)`. -/
theorem T_two_mul_mul_smul_compactK0 (m : ℤ) (x : CompactK0.{w', w} H) :
    (T (2 * k * m) : LaurentPolynomial ℤ) • x = x := by
  induction m using Int.induction_on generalizing x with
  | zero => rw [mul_zero, T_zero, one_smul]
  | succ m ih => rw [mul_add, mul_one, T_add, mul_smul, T_two_mul_smul_compactK0, ih]
  | pred m ih =>
    have := T_two_mul_smul_compactK0 H ((T (2 * k * (-(m : ℤ) - 1)) : LaurentPolynomial ℤ) • x)
    rw [smul_smul, ← T_add, show 2 * k + 2 * k * (-(m : ℤ) - 1) = 2 * k * -(m : ℤ) by ring,
      ih] at this
    exact this.symm

end HalfGradedDGRing

namespace Diagonal

set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, max u v} A]
  [CatModule.HasDerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- `K₀` of the compact objects of `D(C_H)` for the diagonal half-graded dg ring. -/
abbrev DiagK0 := HalfGradedDGRing.CompactK0.{w', v} (HalfGradedDGRing.ofDGRing A)

/-- `K₀` of the compact objects of `D(A)`. -/
abbrev BaseK0 := K0 (compactSubcategory.{max u v} (DerivedCategory.{w, max u v} A)).FullSubcategory

/-- `ρ_j : K₀(D(C_H)^c) → K₀(D(A)^c)`, induced by `X ↦ R₀ (X⟨j⟩)`. -/
def recoveryK0 (j : ℤ) : DiagK0.{w', v} A →+ BaseK0.{w, v} A :=
  K0.mapCompact (shiftDerived.{w', max u v} A j ⋙ recoveryDerived.{w', w} A 0)
    (fun X hX => isCompact_recoveryDerived.{w', w} A
      ((CatModule.DerivedCategory.isCompact_internalShift_obj_iff _ j X).mpr hX))

theorem recoveryK0_mk (j : ℤ)
    (X : (compactSubcategory.{max u v} (CatModule.DerivedCategory.{w', max u v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))).FullSubcategory) :
    recoveryK0.{w', w, v} A j (K0.mk X) = K0.mk (⟨(recoveryDerived.{w', w} A 0).obj
      ((shiftDerived A j).obj X.obj), isCompact_recoveryDerived.{w', w} A
      ((CatModule.DerivedCategory.isCompact_internalShift_obj_iff _ j X.obj).mpr X.property)⟩ :
        (compactSubcategory.{max u v} (DerivedCategory.{w, max u v} A)).FullSubcategory) :=
  K0.mapCompact_mk _ _ X

/-- `ρ_j (qⁿ x) = ρ_{n + j} x`. -/
theorem recoveryK0_T_smul (j n : ℤ) (x : DiagK0.{w', v} A) :
    recoveryK0.{w', w, v} A j ((T n : LaurentPolynomial ℤ) • x) = recoveryK0 A (n + j) x := by
  induction x using K0.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | mk X =>
    rw [CatModule.DerivedCategory.T_smul_mk_compact, recoveryK0_mk, recoveryK0_mk]
    exact K0.mk_eq_of_iso_obj ((recoveryDerived A 0).mapIso
      ((CatModule.DerivedCategory.internalShiftAddIso _ n j).app X.obj)).symm
  | neg x hx => rw [_root_.smul_neg, map_neg, map_neg, hx]
  | add x y hx hy => rw [_root_.smul_add, map_add, map_add, hx, hy]

/-- `ρ_0 ∘ ι = id`, by the unit of the diagonal adjunction. -/
theorem recoveryK0_zero_mapCompactK0 (y : BaseK0.{w, v} A) :
    recoveryK0.{w', w, v} A 0 (mapCompactK0.{w', w, max u v} A y) = y := by
  induction y using K0.induction_on with
  | zero => rw [map_zero, map_zero]
  | mk Y =>
    rw [mapCompactK0_mk, recoveryK0_mk]
    exact K0.mk_eq_of_iso_obj ((recoveryDerived A 0).mapIso
      ((CatModule.DerivedCategory.internalShiftZeroIso _).app _) ≪≫
        (asIso ((diagonalDerivedAdjunction.{w', w, max u v} A).unit.app Y.obj)).symm)
  | neg x hx => rw [map_neg, map_neg, hx]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `ρ_j ∘ ι = 0` for `j ∉ 4ℤ`: the diagonal image vanishes at weights outside `4ℤ`. -/
theorem recoveryK0_mapCompactK0_eq_zero (j : ℤ) (hj : ∀ t : ℤ, j ≠ 4 * t)
    (y : BaseK0.{w, v} A) :
    recoveryK0.{w', w, v} A j (mapCompactK0.{w', w, max u v} A y) = 0 := by
  induction y using K0.induction_on with
  | zero => rw [map_zero, map_zero]
  | mk Y =>
    rw [mapCompactK0_mk, recoveryK0_mk]
    apply K0.mk_eq_zero_of_isZero
    apply IsZero.of_full_of_faithful_of_isZero (compactSubcategory _).ι
    obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj Y.obj
    let M' := (shiftModule A j).obj ((toCatModule A).obj N)
    have : Subsingleton ((recover A 0).obj M') :=
      value_subsingleton A N (0 + j) (fun ⟨t, ht⟩ => hj t (by omega))
    have hz : IsZero (DerivedCategory.Q.obj ((recover A 0).obj M')) :=
      DerivedCategory.Q.map_isZero (DGModuleCat.isZero_of_subsingleton _)
    refine hz.of_iso ((shiftDerived A j ⋙ recoveryDerived A 0).mapIso
      ((toDerived A).mapIso e ≪≫ toDerivedObjIso A N) ≪≫ (recoveryDerived A 0).mapIso
        ((CatModule.DerivedCategory.QCompRestrictIso _).app _) ≪≫ recoveryDerivedObjIso A 0 M')
  | neg x hx => rw [map_neg, map_neg, hx, neg_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- `ρ_{4t} ∘ ι = id`, using `q⁴ = 1`. -/
theorem recoveryK0_mapCompactK0_eq_self (t : ℤ) (y : BaseK0.{w, v} A) :
    recoveryK0.{w', w, v} A (4 * t) (mapCompactK0.{w', w, max u v} A y) = y := by
  have h := recoveryK0_T_smul.{w', w, v} A 0 (2 * 2 * t) (mapCompactK0.{w', w, max u v} A y)
  rw [HalfGradedDGRing.T_two_mul_mul_smul_compactK0, recoveryK0_zero_mapCompactK0,
    show 2 * 2 * t + 0 = 4 * t by ring] at h
  exact h.symm

omit [HasDerivedCategory.{w, max u v} A] in
theorem mk_biprod_compact
    (X Y : CatModule.DerivedCategory.{w', max u v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
    (h : IsCompact.{max u v} (X ⊞ Y)) :
    K0.mk (⟨X ⊞ Y, h⟩ : (compactSubcategory.{max u v} (CatModule.DerivedCategory.{w', max u v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))).FullSubcategory) =
      K0.mk ⟨X, h.of_biprod_left⟩ + K0.mk ⟨Y, h.of_biprod_right⟩ :=
  K0.mk_fullSubcategory_obj₂ (P := compactSubcategory.{max u v} _) (binaryBiproductTriangle X Y)
    (binaryBiproductTriangle_distinguished X Y) _ _ _

theorem mk_blockDerived (r : ℤ)
    (X : (compactSubcategory.{max u v} (CatModule.DerivedCategory.{w', max u v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))).FullSubcategory)
    (h : IsCompact.{max u v} ((blockDerived.{w', w} A r).obj X.obj)) :
    K0.mk (⟨(blockDerived.{w', w} A r).obj X.obj, h⟩ : (compactSubcategory.{max u v}
      (CatModule.DerivedCategory.{w', max u v}
        (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))).FullSubcategory) =
      (T (-r) : LaurentPolynomial ℤ) •
        mapCompactK0.{w', w, max u v} A (recoveryK0.{w', w, v} A r (K0.mk X)) := by
  rw [recoveryK0_mk, mapCompactK0_mk, CatModule.DerivedCategory.T_smul_mk_compact]
  exact K0.mk_eq_of_iso_obj (Iso.refl _)

/-- The block formula `x = ∑_{r=0}^{3} q⁻ʳ ι (ρ_r x)` in `K₀(D(C_H)^c)`. -/
theorem eq_sum_blocks (x : DiagK0.{w', v} A) :
    x = mapCompactK0.{w', w, max u v} A (recoveryK0 A 0 x) +
      (T (-1) : LaurentPolynomial ℤ) • mapCompactK0 A (recoveryK0 A 1 x) +
      (T (-2) : LaurentPolynomial ℤ) • mapCompactK0 A (recoveryK0 A 2 x) +
      (T (-3) : LaurentPolynomial ℤ) • mapCompactK0 A (recoveryK0 A 3 x) := by
  induction x using K0.induction_on with
  | zero => simp only [map_zero, smul_zero, add_zero]
  | mk X =>
    have h := X.property.of_iso (blocksDerivedIso.{w', w} A X.obj).symm
    have e := K0.mk_eq_of_iso_obj (X := X) (Y := ⟨_, h⟩) (blocksDerivedIso.{w', w} A X.obj)
    refine e.trans (((mk_biprod_compact A _ _ h).trans (congrArg₂ (· + ·)
      (mk_blockDerived A 0 X _) ((mk_biprod_compact A _ _ _).trans (congrArg₂ (· + ·)
        (mk_blockDerived A 1 X _) ((mk_biprod_compact A _ _ _).trans (congrArg₂ (· + ·)
          (mk_blockDerived A 2 X _) (mk_blockDerived A 3 X _))))))).trans ?_)
    simp only [neg_zero, T_zero, one_smul, add_assoc]
  | neg x hx =>
    conv_lhs => rw [hx]
    simp only [map_neg, _root_.smul_neg, neg_add]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, _root_.smul_add]
    abel

/-! ### The `ℤ[q, q⁻¹]`-linear equivalence -/

/-- The period ideal `(q⁴ - 1)`. -/
abbrev periodIdeal : Ideal (LaurentPolynomial ℤ) := HalfGradedDGRing.Field.idealPeriod 2

/-- The class of a Laurent polynomial modulo `q⁴ - 1`. -/
abbrev πP (p : LaurentPolynomial ℤ) : LaurentPolynomial ℤ ⧸ periodIdeal :=
  Submodule.Quotient.mk (p := periodIdeal) p

omit [HasDerivedCategory.{w, max u v} A] in
theorem T_four_smul (x : DiagK0.{w', v} A) : (T 4 : LaurentPolynomial ℤ) • x = x := by
  simpa using HalfGradedDGRing.T_two_mul_mul_smul_compactK0.{w', v}
    (HalfGradedDGRing.ofDGRing A) 1 x

/-- `p ↦ (y ↦ p • ι y)`, as a map out of `ℤ[q, q⁻¹] ⧸ (q⁴ - 1)`. -/
def toK0Bilin : (LaurentPolynomial ℤ ⧸ periodIdeal) →ₗ[LaurentPolynomial ℤ]
    (BaseK0.{w, v} A →ₗ[ℤ] DiagK0.{w', v} A) :=
  periodIdeal.liftQ (LinearMap.toSpanSingleton _ _
      (mapCompactK0.{w', w, max u v} A).toIntLinearMap)
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (LinearMap.mem_ker.mpr (by
      ext y
      rw [LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, _root_.sub_smul, one_smul,
        LinearMap.zero_apply]
      change (T (2 * ((2 : ℕ) : ℤ)) : LaurentPolynomial ℤ) • _ - _ = 0
      rw [show 2 * ((2 : ℕ) : ℤ) = 4 by norm_num, T_four_smul, sub_self]))))

/-- `(ℤ[q, q⁻¹] ⧸ (q⁴ - 1)) ⊗ K₀(D(A)^c) → K₀(D(C_H)^c)`, `p ⊗ y ↦ p • ι y`. -/
def toK0 : ((LaurentPolynomial ℤ ⧸ periodIdeal) ⊗[ℤ] BaseK0.{w, v} A) →ₗ[LaurentPolynomial ℤ]
    DiagK0.{w', v} A :=
  AlgebraTensorModule.lift (toK0Bilin.{w', w, v} A)

theorem toK0_tmul (p : LaurentPolynomial ℤ) (y : BaseK0.{w, v} A) :
    toK0.{w', w, v} A (πP p ⊗ₜ y) = p • mapCompactK0.{w', w, max u v} A y := rfl

/-- The inverse `x ↦ ∑_{r=0}^{3} q⁻ʳ ⊗ ρ_r x`. -/
def ofK0 : DiagK0.{w', v} A →+ (LaurentPolynomial ℤ ⧸ periodIdeal) ⊗[ℤ] BaseK0.{w, v} A :=
  ((TensorProduct.mk ℤ _ _ (πP 1)).toAddMonoidHom.comp (recoveryK0.{w', w, v} A 0)) +
  ((TensorProduct.mk ℤ _ _ (πP (T (-1)))).toAddMonoidHom.comp (recoveryK0.{w', w, v} A 1)) +
  ((TensorProduct.mk ℤ _ _ (πP (T (-2)))).toAddMonoidHom.comp (recoveryK0.{w', w, v} A 2)) +
  ((TensorProduct.mk ℤ _ _ (πP (T (-3)))).toAddMonoidHom.comp (recoveryK0.{w', w, v} A 3))

theorem ofK0_apply (x : DiagK0.{w', v} A) :
    ofK0.{w', w, v} A x = πP 1 ⊗ₜ recoveryK0 A 0 x + πP (T (-1)) ⊗ₜ recoveryK0 A 1 x +
      πP (T (-2)) ⊗ₜ recoveryK0 A 2 x + πP (T (-3)) ⊗ₜ recoveryK0 A 3 x := rfl

theorem toK0_ofK0 (x : DiagK0.{w', v} A) : toK0.{w', w, v} A (ofK0 A x) = x := by
  rw [ofK0_apply, map_add, map_add, map_add, toK0_tmul, toK0_tmul, toK0_tmul, toK0_tmul,
    one_smul]
  exact (eq_sum_blocks A x).symm

theorem πP_T_eq {a b : ℤ} (h : ∃ m : ℤ, a - b = 4 * m) : πP (T a) = πP (T b) := by
  obtain ⟨m, hm⟩ := h
  exact HalfGradedDGRing.Field.mk_T_eq (k := 2) (by push_cast; omega)

theorem ofK0_T_smul_mapCompactK0 (n : ℤ) (y : BaseK0.{w, v} A) :
    ofK0.{w', w, v} A ((T n : LaurentPolynomial ℤ) • mapCompactK0.{w', w, max u v} A y) =
      πP (T n) ⊗ₜ y := by
  rw [ofK0_apply, recoveryK0_T_smul, recoveryK0_T_smul, recoveryK0_T_smul, recoveryK0_T_smul]
  have z : ∀ j : ℤ, (∀ t : ℤ, j ≠ 4 * t) →
      recoveryK0.{w', w, v} A j (mapCompactK0.{w', w, max u v} A y) = 0 :=
    fun j hj => recoveryK0_mapCompactK0_eq_zero A j hj y
  have s : ∀ t : ℤ, recoveryK0.{w', w, v} A (4 * t) (mapCompactK0.{w', w, max u v} A y) = y :=
    fun t => recoveryK0_mapCompactK0_eq_self A t y
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · rw [z (n + 1) (by omega), z (n + 2) (by omega), z (n + 3) (by omega),
      show n + 0 = 4 * (n / 4) by omega, s, ← T_zero, πP_T_eq (a := 0) (b := n) ⟨-(n / 4), by omega⟩]
    simp only [tmul_zero, add_zero]
  · rw [z (n + 0) (by omega), z (n + 1) (by omega), z (n + 2) (by omega),
      show n + 3 = 4 * (n / 4 + 1) by omega, s, πP_T_eq (a := -3) (b := n) ⟨-(n / 4) - 1, by omega⟩]
    simp only [tmul_zero, zero_add]
  · rw [z (n + 0) (by omega), z (n + 1) (by omega), z (n + 3) (by omega),
      show n + 2 = 4 * (n / 4 + 1) by omega, s, πP_T_eq (a := -2) (b := n) ⟨-(n / 4) - 1, by omega⟩]
    simp only [tmul_zero, zero_add, add_zero]
  · rw [z (n + 0) (by omega), z (n + 2) (by omega), z (n + 3) (by omega),
      show n + 1 = 4 * (n / 4 + 1) by omega, s, πP_T_eq (a := -1) (b := n) ⟨-(n / 4) - 1, by omega⟩]
    simp only [tmul_zero, zero_add, add_zero]

theorem ofK0_toK0 (z : (LaurentPolynomial ℤ ⧸ periodIdeal) ⊗[ℤ] BaseK0.{w, v} A) :
    ofK0.{w', w, v} A (toK0 A z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul p y =>
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [show (Submodule.Quotient.mk (p + q) : LaurentPolynomial ℤ ⧸ periodIdeal) =
          πP p + πP q from rfl, add_tmul, map_add, map_add, hp, hq]
    | C_mul_T n a =>
      have hC : (Submodule.Quotient.mk (C a * T n) : LaurentPolynomial ℤ ⧸ periodIdeal) =
          a • πP (T n) := by
        rw [← Submodule.Quotient.mk_smul, ← HalfGradedDGRing.Field.C_smul, smul_eq_mul]
      rw [hC, ← TensorProduct.smul_tmul', map_zsmul, map_zsmul, toK0_tmul,
        ofK0_T_smul_mapCompactK0]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem toK0_injective : Function.Injective (toK0.{w', w, v} A) := by
  intro a b h
  have ha := ofK0_toK0 A a
  have hb := ofK0_toK0 A b
  rw [h] at ha
  exact ha.symm.trans hb

/-- **`K₀(D(C_H)^c) ≃ (ℤ[q, q⁻¹] ⧸ (q⁴ - 1)) ⊗ K₀(D(A)^c)`** for the diagonal half-graded dg ring
`H = ofDGRing A` of an arbitrary dg ring `A`, as `ℤ[q, q⁻¹]`-modules (`q` acting on the left by
the internal shift `⟨1⟩`), with `[ι X] ↦ 1 ⊗ [X]`. -/
def K0LinearEquiv : DiagK0.{w', v} A ≃ₗ[LaurentPolynomial ℤ]
    (LaurentPolynomial ℤ ⧸ periodIdeal) ⊗[ℤ] BaseK0.{w, v} A :=
  (LinearEquiv.ofBijective (toK0.{w', w, v} A)
    ⟨toK0_injective A, fun x => ⟨ofK0 A x, toK0_ofK0 A x⟩⟩).symm

theorem K0LinearEquiv_apply (x : DiagK0.{w', v} A) :
    K0LinearEquiv.{w', w, v} A x = ofK0.{w', w, v} A x := by
  apply toK0_injective A
  exact (LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective (toK0.{w', w, v} A) _) x).trans
    (toK0_ofK0.{w', w, v} A x).symm

theorem K0LinearEquiv_symm_tmul (p : LaurentPolynomial ℤ) (y : BaseK0.{w, v} A) :
    (K0LinearEquiv.{w', w, v} A).symm (πP p ⊗ₜ y) = p • mapCompactK0.{w', w, max u v} A y :=
  toK0_tmul.{w', w, v} A p y

theorem K0LinearEquiv_T_smul_mapCompactK0 (n : ℤ) (y : BaseK0.{w, v} A) :
    K0LinearEquiv.{w', w, v} A ((T n : LaurentPolynomial ℤ) • mapCompactK0.{w', w, max u v} A y) =
      πP (T n) ⊗ₜ y := by
  rw [K0LinearEquiv_apply.{w', w, v}, ofK0_T_smul_mapCompactK0.{w', w, v}]

theorem K0LinearEquiv_mapCompactK0 (y : BaseK0.{w, v} A) :
    K0LinearEquiv.{w', w, v} A (mapCompactK0.{w', w, max u v} A y) = πP 1 ⊗ₜ y := by
  simpa using K0LinearEquiv_T_smul_mapCompactK0.{w', w, v} A 0 y

/-! ### The compact super Grothendieck group -/

/-- The class of a Laurent polynomial modulo `1 + q²`. -/
abbrev πS (p : LaurentPolynomial ℤ) : LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2 :=
  Submodule.Quotient.mk (p := HalfGradedDGRing.superIdeal 2) p

theorem periodIdeal_le_superIdeal : periodIdeal ≤ HalfGradedDGRing.superIdeal 2 :=
  HalfGradedDGRing.Field.idealPeriod_le_idealSuper (k := 2)

/-- Reduction `(ℤ[q, q⁻¹] ⧸ (q⁴ - 1)) ⊗ K₀(D(A)^c) → (ℤ[q, q⁻¹] ⧸ (1 + q²)) ⊗ K₀(D(A)^c)`. -/
def reduceSuper : ((LaurentPolynomial ℤ ⧸ periodIdeal) ⊗[ℤ] BaseK0.{w, v} A) →ₗ[LaurentPolynomial ℤ]
    (LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2) ⊗[ℤ] BaseK0.{w, v} A :=
  AlgebraTensorModule.map (Submodule.factor periodIdeal_le_superIdeal) LinearMap.id

omit [CatModule.HasDerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)] in
theorem reduceSuper_tmul (p : LaurentPolynomial ℤ) (y : BaseK0.{w, v} A) :
    reduceSuper.{w, v} A (πP p ⊗ₜ y) = πS p ⊗ₜ y := rfl

omit [CatModule.HasDerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)] in
theorem superIdeal_smul_eq_zero
    (t : (LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2) ⊗[ℤ] BaseK0.{w, v} A) :
    (1 + T 2 : LaurentPolynomial ℤ) • t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul p y =>
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    rw [TensorProduct.smul_tmul', ← Submodule.Quotient.mk_smul,
      (Submodule.Quotient.mk_eq_zero _).mpr, TensorProduct.zero_tmul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  | add x y hx hy => rw [_root_.smul_add, hx, hy, add_zero]

/-- `p ↦ (y ↦ p • [ι y])` into the super Grothendieck group. -/
def toSuperK0Bilin : (LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2) →ₗ[LaurentPolynomial ℤ]
    (BaseK0.{w, v} A →ₗ[ℤ] HalfGradedDGRing.SuperK0c.{w', v} (HalfGradedDGRing.ofDGRing A)) :=
  (HalfGradedDGRing.superIdeal 2).liftQ (LinearMap.toSpanSingleton _ _
      ((HalfGradedDGRing.superK0cMk.{w', v} (HalfGradedDGRing.ofDGRing A)).toAddMonoidHom.comp
        (mapCompactK0.{w', w, max u v} A)).toIntLinearMap)
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (LinearMap.mem_ker.mpr (by
      ext y
      rw [LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, LinearMap.zero_apply]
      exact HalfGradedDGRing.superK0c_isTorsionBy.{w', v} (HalfGradedDGRing.ofDGRing A) (x := _)))))

/-- `(ℤ[q, q⁻¹] ⧸ (1 + q²)) ⊗ K₀(D(A)^c) → SuperK0c H`, `p ⊗ y ↦ p • [ι y]`. -/
def toSuperK0 : ((LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2) ⊗[ℤ] BaseK0.{w, v} A)
    →ₗ[LaurentPolynomial ℤ] HalfGradedDGRing.SuperK0c.{w', v} (HalfGradedDGRing.ofDGRing A) :=
  AlgebraTensorModule.lift (toSuperK0Bilin.{w', w, v} A)

theorem toSuperK0_tmul (p : LaurentPolynomial ℤ) (y : BaseK0.{w, v} A) :
    toSuperK0.{w', w, v} A (πS p ⊗ₜ y) = p • HalfGradedDGRing.superK0cMk.{w', v} _
      (mapCompactK0.{w', w, max u v} A y) := rfl

theorem toSuperK0_reduceSuper
    (t : (LaurentPolynomial ℤ ⧸ periodIdeal) ⊗[ℤ] BaseK0.{w, v} A) :
    toSuperK0.{w', w, v} A (reduceSuper.{w, v} A t) =
      HalfGradedDGRing.superK0cMk.{w', v} _ (toK0.{w', w, v} A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul p y =>
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    exact ((toSuperK0_tmul.{w', w, v} A p y).trans
      (LinearMap.map_smul (HalfGradedDGRing.superK0cMk.{w', v} _) p _).symm)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- `SuperK0c H → (ℤ[q, q⁻¹] ⧸ (1 + q²)) ⊗ K₀(D(A)^c)`, induced by `K0LinearEquiv`. -/
def ofSuperK0 : HalfGradedDGRing.SuperK0c.{w', v} (HalfGradedDGRing.ofDGRing A)
    →ₗ[LaurentPolynomial ℤ]
      (LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2) ⊗[ℤ] BaseK0.{w, v} A :=
  ((HalfGradedDGRing.paritySubmodule.{w', v} (HalfGradedDGRing.ofDGRing A)).liftQ
      ((reduceSuper.{w, v} A).comp (K0LinearEquiv.{w', w, v} A).toLinearMap) (by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_ker.mpr ?_
    exact (congrArg (reduceSuper.{w, v} A) (LinearEquiv.map_smul (K0LinearEquiv.{w', w, v} A)
      (1 + T 2 : LaurentPolynomial ℤ) y)).trans ((LinearMap.map_smul (reduceSuper.{w, v} A) _ _).trans
        (superIdeal_smul_eq_zero.{w, v} A _)))).comp
    (HalfGradedDGRing.superK0cLinearEquiv.{w', v} (HalfGradedDGRing.ofDGRing A)).toLinearMap

theorem ofSuperK0_superK0cMk (x : DiagK0.{w', v} A) :
    ofSuperK0.{w', w, v} A (HalfGradedDGRing.superK0cMk.{w', v} _ x) =
      reduceSuper.{w, v} A (K0LinearEquiv.{w', w, v} A x) := by
  simp only [ofSuperK0, HalfGradedDGRing.superK0cMk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]

theorem toSuperK0_ofSuperK0 (s : HalfGradedDGRing.SuperK0c.{w', v} (HalfGradedDGRing.ofDGRing A)) :
    toSuperK0.{w', w, v} A (ofSuperK0.{w', w, v} A s) = s := by
  obtain ⟨x, rfl⟩ := HalfGradedDGRing.superK0cMk_surjective.{w', v} _ s
  rw [ofSuperK0_superK0cMk, toSuperK0_reduceSuper, K0LinearEquiv_apply, toK0_ofK0]

theorem ofSuperK0_toSuperK0
    (t : (LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2) ⊗[ℤ] BaseK0.{w, v} A) :
    ofSuperK0.{w', w, v} A (toSuperK0.{w', w, v} A t) = t := by
  have key : ∀ t' : (LaurentPolynomial ℤ ⧸ periodIdeal) ⊗[ℤ] BaseK0.{w, v} A,
      ofSuperK0.{w', w, v} A (toSuperK0.{w', w, v} A (reduceSuper.{w, v} A t')) =
        reduceSuper.{w, v} A t' := by
    intro t'
    rw [toSuperK0_reduceSuper, ofSuperK0_superK0cMk, K0LinearEquiv_apply, ofK0_toK0]
  induction t using TensorProduct.inductionOn with
  | tmul p y =>
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    exact key (πP p ⊗ₜ y)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem toSuperK0_injective : Function.Injective (toSuperK0.{w', w, v} A) := by
  intro a b h
  have ha := ofSuperK0_toSuperK0.{w', w, v} A a
  have hb := ofSuperK0_toSuperK0.{w', w, v} A b
  rw [h] at ha
  exact ha.symm.trans hb

/-- **`SuperK0c H ≃ (ℤ[q, q⁻¹] ⧸ (1 + q²)) ⊗ K₀(D(A)^c)`** for the diagonal half-graded dg ring
`H = ofDGRing A` of an arbitrary dg ring `A`, as `ℤ[q, q⁻¹]`-modules, with `[ι X] ↦ 1 ⊗ [X]`.
Over `ℤ[q, q⁻¹] ⧸ (1 + q²) ≅ ℤ[√-1]` (`GaussianQuot.equivGaussianInt`) this is
`SuperK0c H ≃ ℤ[√-1] ⊗ K₀(D(A)^c)`. -/
def superK0LinearEquiv : HalfGradedDGRing.SuperK0c.{w', v} (HalfGradedDGRing.ofDGRing A)
    ≃ₗ[LaurentPolynomial ℤ]
      (LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2) ⊗[ℤ] BaseK0.{w, v} A :=
  (LinearEquiv.ofBijective (toSuperK0.{w', w, v} A)
    ⟨toSuperK0_injective A, fun s => ⟨ofSuperK0 A s, toSuperK0_ofSuperK0 A s⟩⟩).symm

theorem superK0LinearEquiv_symm_tmul (p : LaurentPolynomial ℤ) (y : BaseK0.{w, v} A) :
    (superK0LinearEquiv.{w', w, v} A).symm (πS p ⊗ₜ y) =
      p • HalfGradedDGRing.superK0cMk.{w', v} _ (mapCompactK0.{w', w, max u v} A y) :=
  toSuperK0_tmul.{w', w, v} A p y

theorem superK0LinearEquiv_superK0cMk_mapCompactK0 (y : BaseK0.{w, v} A) :
    superK0LinearEquiv.{w', w, v} A
      (HalfGradedDGRing.superK0cMk.{w', v} _ (mapCompactK0.{w', w, max u v} A y)) =
        πS 1 ⊗ₜ y := by
  rw [← LinearEquiv.eq_symm_apply, superK0LinearEquiv_symm_tmul.{w', w, v}, one_smul]

end Diagonal

end DG

