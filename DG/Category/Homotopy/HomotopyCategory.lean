import Mathlib.CategoryTheory.Quotient.Preadditive
import DG.Category.Homotopy.Homotopy

/-!
# The homotopy category of dg modules over a dg category

Let `C` be a category with dg Hom groups. The homotopy category
`DG.CatModule.HomotopyCategory C` is the quotient of the category `DG.CatModule C` of dg
modules over `C` by the homotopy relation (`DG.CatModule.homotopic`), built with Mathlib's
`CategoryTheory.Quotient`. This is a port of `DG.Homotopy.HomotopyCategory` (the case of a dg
ring).

## Main definitions and results

* `DG.CatModule.homotopic C : HomRel (CatModule C)`, a congruence.
* `DG.CatModule.HomotopyCategory C` and the quotient functor
  `DG.CatModule.HomotopyCategory.quotient C`, which is full, essentially surjective and
  additive; the homotopy category is preadditive with a zero object.
* `DG.CatModule.HomotopyCategory.quotient_map_eq_iff`: two morphisms become equal in the
  homotopy category iff they are homotopic.
* `DG.CatModule.HomotopyCategory.homAddEquivCohomology`:
  `Hom_{H(C)}(M, N) ≃+ H⁰(HOM_C(M, N))`.
* `DG.CatModule.HomotopyCategory.isoOfHomotopyEquiv` and
  `DG.CatModule.HomotopyCategory.isZero_quotient_obj_iff` (a dg module is zero in the homotopy
  category iff it is contractible).

## Differences with the dg-ring version

The dg-ring version is also `R`-linear for a dg `R`-algebra; linearity over a commutative ring
is not part of the present setting of dg categories (whose Hom groups are dg abelian groups),
so only the (`ℤ`-linear) preadditive structure is ported.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace DG

namespace CatModule

variable (C : Type u) [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- The homotopy relation on the morphisms of `CatModule C`. -/
def homotopic : HomRel (CatModule.{w} C) := fun _ _ f g => Homotopic f g

instance homotopic_congruence : Congruence (homotopic.{w} C) where
  equivalence :=
    { refl := fun f => Homotopic.refl f
      symm := Homotopic.symm
      trans := Homotopic.trans }
  compLeft f _ _ h := Homotopic.comp_left h f
  compRight g h := Homotopic.comp_right h g

/-- The homotopy category of dg modules over `C`: the quotient of `CatModule C` by the homotopy
relation. -/
def HomotopyCategory : Type _ :=
  CategoryTheory.Quotient (homotopic.{w} C)

namespace HomotopyCategory

instance : Category.{max u w} (HomotopyCategory.{w} C) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (homotopic.{w} C)))

/-- The quotient functor from dg modules to the homotopy category. -/
def quotient : CatModule.{w} C ⥤ HomotopyCategory.{w} C :=
  CategoryTheory.Quotient.functor _

instance : Preadditive (HomotopyCategory.{w} C) :=
  Quotient.preadditive _ fun _ _ _ _ _ _ h h' => Homotopic.add h h'

instance : (quotient C).Full := Quotient.full_functor _

instance : (quotient C).EssSurj := Quotient.essSurj_functor _

instance : (quotient C).Additive where
  map_add := rfl

instance : Preadditive (CategoryTheory.Quotient (homotopic.{w} C)) :=
  inferInstanceAs (Preadditive (HomotopyCategory.{w} C))

instance : (CategoryTheory.Quotient.functor (homotopic.{w} C)).Additive where
  map_add := rfl

open ZeroObject in
instance : HasZeroObject (HomotopyCategory.{w} C) :=
  ⟨(quotient C).obj 0, by
    rw [IsZero.iff_id_eq_zero, ← (quotient C).map_id, id_zero, Functor.map_zero]⟩

variable {C}

theorem quotient_obj_surjective (X : HomotopyCategory.{w} C) :
    ∃ M : CatModule.{w} C, (quotient C).obj M = X :=
  ⟨_, rfl⟩

@[simp]
theorem quotient_map_out {M N : HomotopyCategory.{w} C} (f : M ⟶ N) :
    (quotient C).map (Quot.out f) = f :=
  Quot.out_eq _

/-- Two morphisms of dg modules become equal in the homotopy category iff they are
homotopic. -/
theorem quotient_map_eq_iff {M N : CatModule.{w} C} (f g : M ⟶ N) :
    (quotient C).map f = (quotient C).map g ↔ Homotopic f g :=
  Quotient.functor_map_eq_iff _ _ _

theorem eq_of_homotopy {M N : CatModule.{w} C} (f g : M ⟶ N) (h : DGHomotopy f g) :
    (quotient C).map f = (quotient C).map g :=
  (quotient_map_eq_iff f g).mpr ⟨h⟩

/-- A homotopy between two morphisms which become equal in the homotopy category. -/
noncomputable def homotopyOfEq {M N : CatModule.{w} C} (f g : M ⟶ N)
    (w : (quotient C).map f = (quotient C).map g) : DGHomotopy f g :=
  ((quotient_map_eq_iff f g).mp w).some

/-- Homotopy equivalent dg modules are isomorphic in the homotopy category. -/
@[simps]
def isoOfHomotopyEquiv {M N : CatModule.{w} C} (e : DGHomotopyEquiv M N) :
    (quotient C).obj M ≅ (quotient C).obj N where
  hom := (quotient C).map e.hom
  inv := (quotient C).map e.inv
  hom_inv_id := by
    rw [← (quotient C).map_comp, ← (quotient C).map_id]
    exact eq_of_homotopy _ _ e.homotopyHomInvId
  inv_hom_id := by
    rw [← (quotient C).map_comp, ← (quotient C).map_id]
    exact eq_of_homotopy _ _ e.homotopyInvHomId

/-- A dg module is a zero object of the homotopy category iff it is contractible. -/
theorem isZero_quotient_obj_iff (M : CatModule.{w} C) :
    IsZero ((quotient C).obj M) ↔ IsContractible M := by
  rw [IsZero.iff_id_eq_zero, ← (quotient C).map_id, ← (quotient C).map_zero,
    quotient_map_eq_iff]
  rfl

/-! ### Morphisms in the homotopy category -/

section Hom

variable (M N : CatModule.{w} C)

/-- The additive map from morphisms of dg modules modulo null-homotopic ones to morphisms in
the homotopy category. -/
def quotientNullHomotopicAddHom :
    ((M ⟶ N) ⧸ nullHomotopic M N) →+ ((quotient C).obj M ⟶ (quotient C).obj N) :=
  QuotientAddGroup.lift _ (quotient C).mapAddHom fun f hf => by
    change (quotient C).map f = 0
    rw [← (quotient C).map_zero M N, quotient_map_eq_iff]
    exact hf

@[simp]
theorem quotientNullHomotopicAddHom_mk (f : M ⟶ N) :
    quotientNullHomotopicAddHom M N (QuotientAddGroup.mk f) = (quotient C).map f :=
  rfl

theorem quotientNullHomotopicAddHom_bijective :
    Function.Bijective (quotientNullHomotopicAddHom M N) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun φ => ?_⟩
  · induction x using QuotientAddGroup.induction_on with
    | H f =>
      rw [quotientNullHomotopicAddHom_mk, ← (quotient C).map_zero M N,
        quotient_map_eq_iff] at hx
      exact (QuotientAddGroup.eq_zero_iff f).mpr hx
  · obtain ⟨f, rfl⟩ := (quotient C).map_surjective φ
    exact ⟨QuotientAddGroup.mk f, rfl⟩

/-- Morphisms in the homotopy category are morphisms of dg modules modulo null-homotopic
ones. -/
noncomputable def homAddEquivQuotient :
    ((quotient C).obj M ⟶ (quotient C).obj N) ≃+ ((M ⟶ N) ⧸ nullHomotopic M N) :=
  (AddEquiv.ofBijective _ (quotientNullHomotopicAddHom_bijective M N)).symm

@[simp]
theorem homAddEquivQuotient_quotient_map (f : M ⟶ N) :
    homAddEquivQuotient M N ((quotient C).map f) = QuotientAddGroup.mk f := by
  rw [homAddEquivQuotient, AddEquiv.symm_apply_eq]
  rfl

/-- `Hom_{H(C)}(M, N) ≅ H⁰(HOM_C(M, N))`: morphisms in the homotopy category are the `0`-th
cohomology of the Hom complex. -/
noncomputable def homAddEquivCohomology :
    ((quotient C).obj M ⟶ (quotient C).obj N) ≃+ cohomology (HOM M N) 0 :=
  (homAddEquivQuotient M N).trans (quotientNullHomotopicAddEquivCohomology M N)

@[simp]
theorem homAddEquivCohomology_quotient_map (f : M ⟶ N) :
    homAddEquivCohomology M N ((quotient C).map f) =
      cohomology.mk _ 0 (HOM.cocyclesAddEquiv M N 0 (Cocycle.ofHom f)) := by
  rw [homAddEquivCohomology, AddEquiv.trans_apply, homAddEquivQuotient_quotient_map,
    quotientNullHomotopicAddEquivCohomology_mk]

end Hom

end HomotopyCategory

end CatModule

end DG
