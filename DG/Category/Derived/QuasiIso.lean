import DG.Category.Derived.Localization
import DG.Category.Homotopy.Acyclic
import DG.Category.Homotopy.Evaluation
import DG.Derived.QuasiIso

/-!
# Quasi-isomorphisms and acyclic objects in the homotopy category of a dg category

Let `C` be a dg category. This file introduces the class of quasi-isomorphisms
`DG.CatModule.HomotopyCategory.quasiIso C` in the homotopy category
`DG.CatModule.HomotopyCategory C` of dg modules over `C` and the triangulated subcategory
`DG.CatModule.HomotopyCategory.subcategoryAcyclic C` of acyclic dg modules, and shows that the
quasi-isomorphisms are exactly the morphisms whose cone is acyclic. Consequently the
quasi-isomorphisms form a multiplicative system compatible with the triangulation, with a
calculus of left and right fractions; this is what is needed to construct the derived category
`D(C)` (`DG/Category/Derived/Basic.lean`). It is a port of `DG.Derived.QuasiIso` (the case of a
dg ring).

## Main definitions and results

* `DG.CatModule.HomotopyCategory.quasiIso C`: the morphisms `f` such that, for every object `X`
  of `C`, the image of `f` under evaluation at `X`
  (`DG.CatModule.HomotopyCategory.eval X`, to Mathlib's homotopy category of complexes of
  abelian groups) is a quasi-isomorphism; equivalently, the cohomology functors
  `DG.CatModule.HomotopyCategory.cohomologyFunctor X n` all send `f` to an isomorphism
  (`DG.CatModule.HomotopyCategory.mem_quasiIso_iff`). By
  `DG.CatModule.HomotopyCategory.quotient_map_mem_quasiIso_iff`, the image of a morphism `φ` of
  dg modules is in `quasiIso C` iff `φ` is a quasi-isomorphism (`DG.CatModule.IsQuasiIso`).
* `DG.CatModule.HomotopyCategory.subcategoryAcyclic C`: the objects whose value at every object
  of `C` is acyclic (the intersection over `X` of the inverse images under `eval X` of Mathlib's
  acyclic complexes); `DG.CatModule.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff`:
  it consists of the acyclic dg modules (`DG.CatModule.IsAcyclic`);
  `DG.CatModule.HomotopyCategory.isThick_subcategoryAcyclic`: it is thick.
* `DG.CatModule.HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`: a morphism is a
  quasi-isomorphism iff its cone is acyclic; for morphisms of dg modules,
  `DG.CatModule.isQuasiIso_iff_isAcyclic_cone`.
* Instances: `quasiIso C` is multiplicative, compatible with the shift and with the
  triangulation, and has a calculus of left and right fractions.
* `DG.CatModule.quasiIso C`: the quasi-isomorphisms of dg modules, a class of morphisms of
  `CatModule C` containing the homotopy equivalences, whose image in the homotopy category is
  `quasiIso C` (`DG.CatModule.HomotopyCategory.quasiIso_eq_quasiIso_map_quotient`).

## Implementation notes

The comparison with the concrete notions goes through the dg-ring case: evaluation at `X`
factors through the homotopy category of dg modules over the endomorphism dg ring `End X`
(`DG.CatModule.HomotopyCategory.evalEnd X`), for which the quasi-isomorphisms are defined with
complexes of `ℤ`-modules; `DG.HomotopyCategory.mem_quasiIso_iff_forgetToAddCommGrp` identifies
them with the quasi-isomorphisms of the underlying complexes of abelian groups.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Pretriangulated ZeroObject

universe w v u

namespace DG

section Aux

variable {T T' : Type*} [Category T] [Category T'] [HasZeroObject T] [HasZeroObject T']
  [HasShift T ℤ] [HasShift T' ℤ] [Preadditive T] [Preadditive T']
  [∀ n : ℤ, (shiftFunctor T n).Additive] [∀ n : ℤ, (shiftFunctor T' n).Additive]
  [Pretriangulated T] [Pretriangulated T'] (G : T ⥤ T') [G.CommShift ℤ] [G.IsTriangulated]

/-- Let `G` be a triangulated functor and `S`, `S'` triangulated subcategories (closed under
isomorphisms) such that `f` is in `S.trW` iff `G.map f` is in `S'.trW`. Then an object is in `S` iff
its image is in `S'`. -/
theorem Triangulated.Subcategory.prop_iff_of_W_iff (S : ObjectProperty T)
    [S.IsTriangulated]
    (S' : ObjectProperty T') [S'.IsTriangulated] [S.IsClosedUnderIsomorphisms]
    [S'.IsClosedUnderIsomorphisms]
    (hW : ∀ ⦃X Y : T⦄ (f : X ⟶ Y), S.trW f ↔ S'.trW (G.map f)) (X : T) :
    S X ↔ S' (G.obj X) :=
  ((S.trW_iff_of_distinguished _ (contractible_distinguished₁ X)).symm.trans
    (hW _)).trans
    (S'.trW_iff_of_distinguished _ (G.map_distinguished _ (contractible_distinguished₁ X)))

end Aux

/-! ### Complexes of `ℤ`-modules and of abelian groups -/

namespace HomotopyCategory

/-- A morphism of the homotopy category of complexes of `ℤ`-modules is a quasi-isomorphism iff
its underlying morphism of complexes of abelian groups is. -/
theorem quasiIso_map_forget₂_iff
    {K L : _root_.HomotopyCategory (ModuleCat.{w} ℤ) (ComplexShape.up ℤ)} (g : K ⟶ L) :
    _root_.HomotopyCategory.quasiIso AddCommGrpCat.{w} (ComplexShape.up ℤ)
      (((forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).mapHomotopyCategory _).map g) ↔
    _root_.HomotopyCategory.quasiIso (ModuleCat.{w} ℤ) (ComplexShape.up ℤ) g := by
  obtain ⟨K⟩ := K
  obtain ⟨L⟩ := L
  obtain ⟨g, rfl⟩ := (_root_.HomotopyCategory.quotient _ _).map_surjective g
  rw [Functor.mapHomotopyCategory_map, _root_.HomotopyCategory.quotient_map_mem_quasiIso_iff,
    _root_.HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff]
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology g _

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The quasi-isomorphisms of `H(A)` are the morphisms whose underlying morphism of complexes of
abelian groups is a quasi-isomorphism. -/
theorem mem_quasiIso_iff_forgetToAddCommGrp {X Y : HomotopyCategory.{w} A} (f : X ⟶ Y) :
    quasiIso A f ↔ _root_.HomotopyCategory.quasiIso AddCommGrpCat.{w} (ComplexShape.up ℤ)
      ((forgetToAddCommGrp A).map f) :=
  (quasiIso_map_forget₂_iff _).symm

variable (A) in
/-- The acyclic objects of `H(A)` are the objects whose underlying complex of abelian groups is
acyclic. -/
theorem mem_subcategoryAcyclic_iff_forgetToAddCommGrp (X : HomotopyCategory.{w} A) :
    (subcategoryAcyclic A) X ↔
      (_root_.HomotopyCategory.subcategoryAcyclic AddCommGrpCat.{w})
        ((forgetToAddCommGrp A).obj X) :=
  Triangulated.Subcategory.prop_iff_of_W_iff (forgetToAddCommGrp A) _ _ (fun _ _ f => by
    rw [← quasiIso_eq_subcategoryAcyclic_W,
      ← _root_.HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact mem_quasiIso_iff_forgetToAddCommGrp f) X

end HomotopyCategory

namespace CatModule

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-! ### Evaluation as a dg module over the endomorphism dg ring -/

/-- Evaluation at an object `X`, on homotopy categories, as a dg module over the endomorphism dg
ring `End X`. -/
noncomputable def evalEnd (X : C) : HomotopyCategory.{w} C ⥤ DG.HomotopyCategory.{w} (End X) :=
  precomp (endInclusion X) ⋙ toDGHomotopyCategory (End X)

noncomputable instance evalEndCommShift (X : C) : (evalEnd.{w} X).CommShift ℤ :=
  inferInstanceAs ((precomp (endInclusion X) ⋙ toDGHomotopyCategory (End X)).CommShift ℤ)

/-- Evaluation at `X` as a dg `End X`-module is a triangulated functor. -/
instance evalEnd_isTriangulated (X : C) : (evalEnd.{w} X).IsTriangulated :=
  inferInstanceAs (precomp (endInclusion X) ⋙ toDGHomotopyCategory (End X)).IsTriangulated

omit [DGCategory C] in
@[simp]
theorem evalEnd_map_quotient_map (X : C) {M N : CatModule.{w} C} (f : M ⟶ N) :
    (evalEnd X).map ((quotient C).map f) =
      (DG.HomotopyCategory.quotient (End X)).map ((CatModule.eval X).map f) :=
  rfl

/-! ### Quasi-isomorphisms and acyclic objects -/

variable (C)

/-- The quasi-isomorphisms in the homotopy category of dg modules over `C`: the morphisms whose
evaluation at every object is a quasi-isomorphism of complexes of abelian groups, i.e. which
induce isomorphisms on the cohomology of the values at all objects. -/
def quasiIso : MorphismProperty (HomotopyCategory.{w} C) := fun _ _ f =>
  ∀ X : C, _root_.HomotopyCategory.quasiIso AddCommGrpCat.{w} (ComplexShape.up ℤ) ((eval X).map f)

/-- The triangulated subcategory of acyclic objects of the homotopy category of dg modules over
`C`: the objects whose evaluation at every object of `C` is an acyclic complex. -/
def subcategoryAcyclic : ObjectProperty (HomotopyCategory.{w} C) :=
  fun M => ∀ X : C,
    (_root_.HomotopyCategory.subcategoryAcyclic AddCommGrpCat.{w}) ((eval X).obj M)

instance : (subcategoryAcyclic.{w} C).IsTriangulated where
  exists_zero := ⟨0, CategoryTheory.Limits.isZero_zero _, fun X =>
    (_root_.HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      (eval X).mapZeroObject.symm (_root_.HomotopyCategory.subcategoryAcyclic _).prop_zero⟩
  isStableUnderShiftBy n := ⟨fun M hM X =>
    (_root_.HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      (((eval X).commShiftIso n).app M).symm
      ((_root_.HomotopyCategory.subcategoryAcyclic _).le_shift n _ (hM X))⟩
  ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _ (fun X =>
    (_root_.HomotopyCategory.subcategoryAcyclic _).ext_of_isTriangulatedClosed₂ _
      ((eval X).map_distinguished T hT) (h₁ X) (h₃ X))

instance : (subcategoryAcyclic.{w} C).IsClosedUnderIsomorphisms where
  of_iso e h X := (_root_.HomotopyCategory.subcategoryAcyclic _).prop_of_iso
    ((eval X).mapIso e) (h X)

variable {C}

theorem mem_quasiIso_iff {M N : HomotopyCategory.{w} C} (f : M ⟶ N) :
    quasiIso C f ↔ ∀ (X : C) (n : ℤ), IsIso ((cohomologyFunctor X n).map f) :=
  Iff.rfl

/-- An object is acyclic iff its cohomology at every object vanishes. -/
theorem mem_subcategoryAcyclic_iff (M : HomotopyCategory.{w} C) :
    (subcategoryAcyclic C) M ↔ ∀ (X : C) (n : ℤ), IsZero ((cohomologyFunctor X n).obj M) :=
  forall_congr' fun _ => _root_.HomotopyCategory.mem_subcategoryAcyclic_iff _

variable (C)

/-- A morphism of the homotopy category is a quasi-isomorphism iff its cone is acyclic, i.e.
the quasi-isomorphisms are the class of morphisms `W` attached to the triangulated subcategory
of acyclic objects. -/
theorem quasiIso_eq_subcategoryAcyclic_W : quasiIso.{w} C = (subcategoryAcyclic C).trW := by
  ext M N f
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  refine Iff.trans ?_ ((subcategoryAcyclic C).trW_iff_of_distinguished _ hT).symm
  refine forall_congr' fun X => ?_
  rw [_root_.HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (_root_.HomotopyCategory.subcategoryAcyclic _).trW_iff_of_distinguished _
    ((eval X).map_distinguished _ hT)

/-- The acyclic objects form a thick subcategory: it is triangulated and closed under direct
summands (retracts). -/
theorem isThick_subcategoryAcyclic : IsThick (subcategoryAcyclic.{w} C) where
  zero := (subcategoryAcyclic C).prop_zero
  shift X n := (subcategoryAcyclic C).le_shift n X
  ext₂ := (subcategoryAcyclic C).ext_of_isTriangulatedClosed₂
  retract {M N} e hN := by
    rw [mem_subcategoryAcyclic_iff] at hN ⊢
    intro X n
    have e' := e.map (cohomologyFunctor X n)
    rw [IsZero.iff_id_eq_zero]
    refine e'.retract.symm.trans ?_
    rw [(hN X n).eq_of_src e'.r 0, comp_zero]

instance : (quasiIso.{w} C).RespectsIso := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{w} C).IsMultiplicative := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{w} C).IsCompatibleWithShift ℤ := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{w} C).IsCompatibleWithTriangulation := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{w} C).HasLeftCalculusOfFractions := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{w} C).HasRightCalculusOfFractions := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

/-- The cohomology functors at the objects of `C` invert quasi-isomorphisms. -/
theorem cohomologyFunctor_inverts_quasiIso (X : C) (n : ℤ) :
    (quasiIso.{w} C).IsInvertedBy (cohomologyFunctor X n) :=
  fun _ _ _ hf => hf X n

/-! ### Concrete descriptions -/

variable {C}

/-- A morphism is a quasi-isomorphism iff its evaluation at every object is a quasi-isomorphism
of dg modules over the endomorphism dg ring. -/
theorem mem_quasiIso_iff_evalEnd {M N : HomotopyCategory.{w} C} (f : M ⟶ N) :
    quasiIso C f ↔ ∀ X : C, DG.HomotopyCategory.quasiIso (End X) ((evalEnd X).map f) :=
  forall_congr' fun _ => (DG.HomotopyCategory.mem_quasiIso_iff_forgetToAddCommGrp _).symm

/-- An object is acyclic iff its evaluation at every object is an acyclic dg module over the
endomorphism dg ring. -/
theorem mem_subcategoryAcyclic_iff_evalEnd (M : HomotopyCategory.{w} C) :
    (subcategoryAcyclic C) M ↔
      ∀ X : C, (DG.HomotopyCategory.subcategoryAcyclic (End X)) ((evalEnd X).obj M) :=
  forall_congr' fun X =>
    (DG.HomotopyCategory.mem_subcategoryAcyclic_iff_forgetToAddCommGrp (End X) _).symm

/-- The image of a morphism of dg modules in the homotopy category is a quasi-isomorphism iff it
is a quasi-isomorphism of dg modules. -/
theorem quotient_map_mem_quasiIso_iff {M N : CatModule.{w} C} (f : M ⟶ N) :
    quasiIso C ((quotient C).map f) ↔ IsQuasiIso f :=
  (mem_quasiIso_iff_evalEnd _).trans (forall_congr' fun X =>
    DG.HomotopyCategory.quotient_map_mem_quasiIso_iff ((CatModule.eval X).map f))

/-- A dg module is in the subcategory of acyclic objects iff it is acyclic. -/
theorem quotient_obj_mem_subcategoryAcyclic_iff (M : CatModule.{w} C) :
    (subcategoryAcyclic C) ((quotient C).obj M) ↔ IsAcyclic M :=
  (mem_subcategoryAcyclic_iff_evalEnd _).trans (forall_congr' fun X =>
    DG.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff ((CatModule.eval X).obj M))

/-- A morphism of dg modules becomes a quasi-isomorphism in the homotopy category iff its
mapping cone is acyclic. -/
theorem quotient_map_mem_quasiIso_iff_isAcyclic_cone {M N : CatModule.{w} C} (f : M ⟶ N) :
    quasiIso C ((quotient C).map f) ↔ IsAcyclic (cone f) := by
  rw [quasiIso_eq_subcategoryAcyclic_W, ← quotient_obj_mem_subcategoryAcyclic_iff]
  exact (subcategoryAcyclic C).trW_iff_of_distinguished _ (triangleh_distinguished f)

end HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- A morphism of dg modules over a dg category is a quasi-isomorphism iff its mapping cone is
acyclic. -/
theorem isQuasiIso_iff_isAcyclic_cone [DGCategory C] {M N : CatModule.{w} C} (f : M ⟶ N) :
    IsQuasiIso f ↔ IsAcyclic (cone f) :=
  (HomotopyCategory.quotient_map_mem_quasiIso_iff f).symm.trans
    (HomotopyCategory.quotient_map_mem_quasiIso_iff_isAcyclic_cone f)

variable (C)

/-- The quasi-isomorphisms of dg modules over `C`, as a class of morphisms of `CatModule C`. -/
def quasiIso : MorphismProperty (CatModule.{w} C) := fun _ _ f => IsQuasiIso f

/-- Homotopy equivalences are quasi-isomorphisms. -/
theorem homotopyEquivalences_le_quasiIso : homotopyEquivalences.{w} C ≤ quasiIso C := by
  rintro M N f ⟨e, rfl⟩ X n
  exact e.bijective_cohomologyMap_hom X n

/-- The quasi-isomorphisms of the homotopy category are the images of the quasi-isomorphisms of
dg modules. -/
theorem HomotopyCategory.quasiIso_eq_quasiIso_map_quotient [DGCategory C] :
    HomotopyCategory.quasiIso.{w} C = (CatModule.quasiIso C).map (HomotopyCategory.quotient C) := by
  ext ⟨M⟩ ⟨N⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C).map_surjective f
  constructor
  · intro hf
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨M', N', g, hg, ⟨e⟩⟩
    rw [CatModule.quasiIso, ← HomotopyCategory.quotient_map_mem_quasiIso_iff] at hg
    exact ((HomotopyCategory.quasiIso C).arrow_mk_iso_iff e).1 hg

end CatModule

end DG
