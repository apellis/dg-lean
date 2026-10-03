import DG.HalfGraded.DiagonalDerived
import DG.Category.Yoneda
import DG.Category.Derived.Perfect

/-!
# The diagonal regular module and its compact derived image

The full half-regraded regular module is isomorphic to the representable at weight zero.
The comparison preserves actual homogeneous elements, including all periodic copies.
Consequently the derived diagonal functor sends the regular generator to a compact object.
This does not assert preservation of every compact object or derived full faithfulness.
-/

noncomputable section
open CategoryTheory
namespace DG.Diagonal
set_option backward.isDefEq.respectTransparency false
universe w w' u
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The additive identification of the full regraded regular module with the regraded ring. -/
def regularRegradedEquiv : RegradedModule A ≃+ (HalfGradedDGRing.ofDGRing A).Regraded :=
  AddEquiv.refl _

theorem regularRegradedEquiv_smul
    (a : (HalfGradedDGRing.ofDGRing A).Regraded) (m : RegradedModule A) :
    regularRegradedEquiv A (a • m) = a * regularRegradedEquiv A m := by
  induction a using HalfGradedDGRing.induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_smul, map_add, add_mul, ha, hb]
  | mk p a ha =>
    induction m using HalfRegrade.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, mul_add, hx, hy]
    | mk q m hm =>
      rw [place_smul_mk]
      change (HalfGradedDGRing.ofDGRing A).place (p + q) (a * m) _ =
        (HalfGradedDGRing.ofDGRing A).place p a ha *
          (HalfGradedDGRing.ofDGRing A).place q m hm
      exact (HalfGradedDGRing.place_mul_place ha hm).symm

/-- The diagonal regular module maps to the weight-zero representable by the identity
on actual homogeneous elements. -/
def regularToRepresentable :
    (toCatModule A).obj (DGModuleCat.of A A) ⟶
      CatModule.representable (⟨0⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) where
  app X :=
    { toFun := fun x => ⟨regularRegradedEquiv A x.1, by
        change x.1 ∈ HalfRegrade.weightGrading (grading A) 2 (X.as - 0)
        have hx := x.2
        change x.1 ∈ HalfRegrade.weightGrading (grading A) 2 X.as at hx
        simpa only [sub_zero] using hx⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  map_mem' hx := hx
  map_d' _ := Subtype.ext rfl
  map_smul' f x := Subtype.ext (regularRegradedEquiv_smul A f.1 x.1)

theorem regularToRepresentable_bijective
    (X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :
    Function.Bijective ((regularToRepresentable A).app X) := by
  constructor
  · intro x y h
    have he := congrArg
      (fun z : (⟨0⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⟶ X => z.1) h
    exact Subtype.ext he
  · intro y
    refine ⟨⟨(regularRegradedEquiv A).symm y.1, ?_⟩, ?_⟩
    · change y.1 ∈ HalfRegrade.weightGrading (grading A) 2 X.as
      have hy := y.2
      change y.1 ∈ HalfRegrade.weightGrading (grading A) 2 (X.as - 0) at hy
      simpa only [sub_zero] using hy
    · exact Subtype.ext ((regularRegradedEquiv A).apply_symm_apply y.1)

/-- The actual diagonal regular module is the representable at weight zero. -/
def regularRepresentableIso :
    (toCatModule A).obj (DGModuleCat.of A A) ≅
      CatModule.representable (⟨0⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) := by
  letI := CatModule.isIso_of_bijective (regularToRepresentable A)
    (regularToRepresentable_bijective A)
  exact asIso (regularToRepresentable A)

/-- On every homogeneous regular element, the comparison is the actual ring placement.
The weight is arbitrary, so the statement retains all supported periodic copies. -/
@[simp] theorem regularRepresentableIso_hom_mk (p : ℤ × ℤ) (a : A)
    (ha : a ∈ grading A (halfDegree 2 p)) :
    ((regularRepresentableIso A).hom.app ⟨p.2⟩
      ⟨HalfRegrade.mk (grading A) 2 p a ha, HalfRegrade.mk_mem_weightGrading p _⟩).1 =
      (HalfGradedDGRing.ofDGRing A).place p a ha := rfl

variable [CatModule.HasDerivedCategory.{w', u}
  (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The actual diagonal regular module is compact after localization, by the proved
representable comparison, not by an assumption of compactness preservation. -/
theorem isCompact_Q_diagonalRegular :
    IsCompact.{u} (CatModule.DerivedCategory.Q.obj
      ((toCatModule A).obj (DGModuleCat.of A A))) := by
  have h := CatModule.DerivedCategory.isCompact_Q_obj
    (CatModule.isCornerGenerator_representable
      (⟨0⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
  exact h.of_iso (CatModule.DerivedCategory.Q.mapIso (regularRepresentableIso A))

variable [HasDerivedCategory.{w, u} A]

/-- The induced derived functor sends the regular generator to a compact object. -/
theorem isCompact_toDerived_regular :
    IsCompact.{u} ((toDerived A).obj (DerivedCategory.Q.obj (DGModuleCat.of A A))) :=
  (isCompact_Q_diagonalRegular A).of_iso (toDerivedObjIso A (DGModuleCat.of A A))

end DG.Diagonal
