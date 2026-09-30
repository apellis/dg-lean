import DG.Bigraded.Derived
import DG.Bigraded.Schnurer
import DG.K0.PositiveCategory

/-!
# The Grothendieck group of a positive bigraded dg ring

Let `A` be a bigraded dg ring and `C_A` its weight dg category. The internal shift `⟨s⟩` of
`D(C_A)` (restriction along `k ↦ k + s`) moves the cells between the objects of `C_A`: for an
idempotent `e ∈ A^{0,0}`, `(e · C_A(k, -))⟨s⟩ ≅ e · C_A(k - s, -)`
(`DG.CatModule.DerivedCategory.internalShiftCellIso`). Hence in the `ℤ[q, q⁻¹]`-module
`K₀(C_A) = K₀(D^c(C_A))` (with `qⁿ • [M] = [M⟨n⟩]`),
`qˢ [e · C_A(k, -)] = [e · C_A(k - s, -)]` (`DG.WeightCategory.T_smul_cell`).

For `A` graded positive (Roadmap 7.2 (a)), `K₀(C_A)` is generated over `ℤ[q, q⁻¹]` by the classes
`[e · C_A(0, -)]` (the graded modules `A e`) of the graded simple idempotents `e ∈ A^{0,0}`
(`DG.IsGradedPositive.span_cell_eq_top`), by Schnürer's theorem.
-/

open CategoryTheory Limits

universe w u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A]

open CatModule DGCategory

namespace WeightCategory

/-- A degree-`0` idempotent cocycle `e` of an object of `C_A` (an idempotent of `A^{0,0}`), as a
degree-`0` idempotent cocycle of another object `k'`. -/
def idempotentAt {k : WeightCategory A} (e : Idempotent k) (k' : WeightCategory A) :
    Idempotent k' where
  val := homMk e.val.1 (mem_wgrading_of_eq (by rw [sub_self, sub_self]) e.val.2)
  mem_cocycles := ⟨e.mem_grading, hom_ext (show d e.val.1 = 0 from val_congr e.d_val)⟩
  comp_self := hom_ext (show e.val.1 * e.val.1 = e.val.1 from val_congr e.comp_self)

omit [DGRing A] in
@[simp]
theorem idempotentAt_val_val {k : WeightCategory A} (e : Idempotent k) (k' : WeightCategory A) :
    (idempotentAt e k').val.1 = e.val.1 :=
  rfl

theorem isSimple_idempotentAt {k : WeightCategory A} {e : Idempotent k} (he : e.IsSimple)
    (k' : WeightCategory A) : (idempotentAt e k').IsSimple :=
  (idempotent_isSimple_iff _).mpr ((idempotent_isSimple_iff e).mp he)

/-- Restriction of the corner `e · C_A(k, -)` along `l ↦ l + s` is the corner
`e' · C_A(k', -)` for `k' = k - s` and `e'` with the same underlying element of `A^{0,0}`. -/
def precompCornerIso (s : ℤ) {k k' : WeightCategory A} (e : Idempotent k) (e' : Idempotent k')
    (hk : k'.as = k.as - s) (he : e'.val.1 = e.val.1) :
    precompObj (shiftFunctor A s) (ulift.{w} (corner e)) ≅ ulift.{w} (corner e') := by
  have hw : ∀ l : WeightCategory A, (l.as + s) - k.as = l.as - k'.as := fun l => by
    rw [hk]
    ring
  refine isoMk (fun l => ?_) ?_ ?_ ?_
  · exact
      { toFun := fun x => ULift.up ⟨homMk x.down.1.1 (mem_wgrading_of_eq (hw l) x.down.1.2),
          hom_ext (show (x.down.1.1 : A) * e'.val.1 = x.down.1.1 by
            rw [he]
            exact val_congr x.down.2)⟩
        invFun := fun y => ULift.up ⟨homMk y.down.1.1
            (mem_wgrading_of_eq (hw l).symm y.down.1.2),
          hom_ext (show (y.down.1.1 : A) * e.val.1 = y.down.1.1 by
            rw [← he]
            exact val_congr y.down.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
  · intro l n x
    exact Iff.rfl
  · intro l x
    rfl
  · intro l l' f x
    rfl

end WeightCategory

namespace CatModule.DerivedCategory

variable [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]

/-- The internal shift of a cell: `(e · C_A(k, -))⟨s⟩ ≅ e' · C_A(k - s, -)` in `D(C_A)`, for `e'`
with the same underlying element of `A^{0,0}` as `e`. -/
def internalShiftCellIso (s : ℤ) {k k' : WeightCategory A} (e : Idempotent k)
    (e' : Idempotent k') (hk : k'.as = k.as - s) (he : e'.val.1 = e.val.1) :
    (internalShift A s).obj (cell.{max u w, w} e 0) ≅ cell.{max u w, w} e' 0 :=
  (QCompInternalShiftIso A s).app _ ≪≫
    Q.mapIso ((precomp (WeightCategory.shiftFunctor A s)).mapIso (shiftZeroIso _) ≪≫
      (WeightCategory.precompCornerIso s e e' hk he : precompObj (WeightCategory.shiftFunctor A s)
        (ulift.{w} (corner e)) ≅ ulift.{w} (corner e')) ≪≫
        (shiftZeroIso (ulift.{w} (corner e'))).symm)

end CatModule.DerivedCategory

namespace WeightCategory

variable [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]

open CatModule.DerivedCategory

/-- `qˢ [e · C_A(k, -)] = [e' · C_A(k - s, -)]` in `K₀(C_A)`, for `e'` with the same underlying
element of `A^{0,0}` as `e`. -/
theorem T_smul_cell (s : ℤ) {k k' : WeightCategory A} (e : Idempotent k) (e' : Idempotent k')
    (hk : k'.as = k.as - s) (he : e'.val.1 = e.val.1) :
    (LaurentPolynomial.T s : LaurentPolynomial ℤ) • K0.cell.{w} e 0 = K0.cell e' 0 := by
  rw [K0.cell, T_smul_mk_compact]
  exact DG.K0.mk_eq_of_iso_obj (internalShiftCellIso s e e' hk he)

end WeightCategory

namespace IsGradedPositive

variable (hA : IsGradedPositive A)
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]
include hA

/-- For `A` graded positive, `K₀(C_A)` is generated as a `ℤ[q, q⁻¹]`-module by the classes
`[e · C_A(0, -)]` (the bigraded modules `A e`) of the graded simple idempotents `e ∈ A^{0,0}`
(Roadmap 7.2 (a)). -/
theorem span_cell_eq_top :
    Submodule.span (LaurentPolynomial ℤ) (Set.range fun e :
      {e : Idempotent (⟨0⟩ : WeightCategory A) // e.IsSimple} => K0.cell.{w} e.1 0) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x ∈ AddSubgroup.closure
      (Set.range fun c : SimpleCorner (WeightCategory A) => K0.cell.{w} c.1.2 0) := by
    rw [hA.isPositive_weightCategory.closure_cell_eq_top]
    trivial
  refine AddSubgroup.closure_le (K := (Submodule.span (LaurentPolynomial ℤ) _).toAddSubgroup)
    |>.mpr ?_ hx
  rintro _ ⟨⟨⟨k, e⟩, he⟩, rfl⟩
  let e₀ := WeightCategory.idempotentAt e ⟨0⟩
  have h := WeightCategory.T_smul_cell (-k.as) e₀ e (by simp) rfl
  change K0.cell e 0 ∈ (Submodule.span (LaurentPolynomial ℤ) _).toAddSubgroup
  rw [← h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨⟨e₀, WeightCategory.isSimple_idempotentAt he _⟩, rfl⟩)

end IsGradedPositive

end DG

end
