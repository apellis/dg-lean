import DG.Category.Derived.QuasiIso

/-!
# The derived category of a dg category

Let `C` be a dg category. The derived category `D(C)` is the localization of the homotopy
category `DG.CatModule.HomotopyCategory C` of dg modules over `C` at the quasi-isomorphisms
`DG.CatModule.HomotopyCategory.quasiIso C`. It is a port of `DG.Derived.Basic` (the case of a
dg ring). As in Mathlib's `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`, the localized
category is not constructed with a fixed universe of morphisms: we assume
`[DG.CatModule.HasDerivedCategory.{w'} C]`, the choice of a localization whose morphisms are in
`Type w'` (`CategoryTheory.MorphismProperty.HasLocalization`). The constructed localization,
with morphisms in a larger universe, is `DG.CatModule.HasDerivedCategory.standard C`; it should
only be used to prove statements which do not involve the derived category.

## Main definitions and results

* `DG.CatModule.DerivedCategory C`, with the localization functors
  `DG.CatModule.DerivedCategory.Qh : HomotopyCategory C ⥤ DerivedCategory C` (a localization
  functor for `quasiIso C`) and `DG.CatModule.DerivedCategory.Q : CatModule C ⥤ DerivedCategory C`
  (a localization functor for the quasi-isomorphisms of dg modules `DG.CatModule.quasiIso C`,
  using that the homotopy category is the localization at the homotopy equivalences,
  `DG.CatModule.HomotopyCategory.quotient_isLocalization`).
* `D(C)` is preadditive, has a zero object and a shift by `ℤ`, and is pretriangulated and
  triangulated; `Qh` commutes with the shifts and is a triangulated functor. The triangulated
  structure is obtained by Verdier localization (Mathlib's `Triangulated.Localization`), since
  `quasiIso C` is the class of morphisms whose cone is acyclic
  (`DG.CatModule.HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`).
  `DG.CatModule.DerivedCategory.mem_distTriang_iff`: the distinguished triangles are the
  triangles isomorphic to images of the standard triangles `M → N → cone f → M⟦1⟧`.
* `DG.CatModule.DerivedCategory.isIso_Q_map_iff`: `Q.map f` is an isomorphism iff `f` is a
  quasi-isomorphism; `DG.CatModule.DerivedCategory.isZero_Q_obj_iff`: `Q.obj M` is zero iff `M`
  is acyclic.
* Cohomology: for an object `X` of `C` and `n : ℤ`, the functor
  `DG.CatModule.DerivedCategory.cohomologyFunctor X n : DerivedCategory C ⥤ AddCommGrp`
  induced by the cohomology at `X` on the homotopy category (`cohomologyFunctorFactorsh`); it is
  homological.

Coproducts in `D(C)` are in `DG/Category/Derived/Coproducts.lean`.

## Universes

For `C : Type u` with `[Category.{v} C]` and dg modules with values in `Type w`, the homotopy
category `HomotopyCategory.{w} C` has objects in `Type (max u v (w + 1))` and morphisms in
`Type (max u w)`; `DG.CatModule.HasDerivedCategory.{w'} C` chooses a localization with morphisms
in `Type w'`.
-/

open CategoryTheory Limits Pretriangulated ZeroObject

universe w' w v u

namespace DG

namespace CatModule

variable (C : Type u) [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-- The assumption that a localization of the homotopy category of dg modules over `C` (with
values in `Type w`) at the quasi-isomorphisms has been chosen, with morphisms in `Type w'`. -/
abbrev HasDerivedCategory :=
  MorphismProperty.HasLocalization.{w'} (HomotopyCategory.quasiIso.{w} C)

/-- The derived category obtained from the constructed localization. This should be used only
while proving statements which do not involve the derived category. -/
def HasDerivedCategory.standard : HasDerivedCategory.{max u v (w + 1), w} C :=
  MorphismProperty.HasLocalization.standard _

variable [HasDerivedCategory.{w', w} C]

/-- The derived category `D(C)` of a dg category `C`: the localization of the homotopy category
of dg modules over `C` at the quasi-isomorphisms. -/
def DerivedCategory : Type (max u v (w + 1)) := (HomotopyCategory.quasiIso.{w} C).Localization'

namespace DerivedCategory

instance : Category.{w'} (DerivedCategory C) := by
  dsimp [DerivedCategory]
  infer_instance

variable {C}

/-- The localization functor `H(C) ⥤ D(C)`. -/
def Qh : HomotopyCategory.{w} C ⥤ DerivedCategory C := MorphismProperty.Q' _

/-- The localization functor `CatModule C ⥤ D(C)`. -/
def Q : CatModule.{w} C ⥤ DerivedCategory C := HomotopyCategory.quotient C ⋙ Qh

variable (C) in
/-- The isomorphism `HomotopyCategory.quotient C ⋙ Qh ≅ Q` (an identity). -/
def quotientCompQhIso : HomotopyCategory.quotient C ⋙ Qh ≅ Q (C := C) := Iso.refl _

instance Qh_isLocalization : (Qh (C := C)).IsLocalization (HomotopyCategory.quasiIso C) := by
  dsimp only [Qh, DerivedCategory]
  infer_instance

instance : (Qh (C := C)).IsLocalization (HomotopyCategory.subcategoryAcyclic C).W := by
  rw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Q (C := C)).Additive := by
  dsimp only [Q]
  infer_instance

noncomputable instance : HasZeroObject (DerivedCategory C) :=
  Qh.hasZeroObject_of_additive

noncomputable instance : HasShift (DerivedCategory C) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance Qh_commShift : (Qh (C := C)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance : (Q (C := C)).CommShift ℤ := by
  dsimp only [Q]
  infer_instance

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  rw [Localization.functor_additive_iff Qh (HomotopyCategory.subcategoryAcyclic C).W]
  exact Functor.additive_of_iso (Qh.commShiftIso n)

/-- The derived category is pretriangulated. -/
noncomputable instance pretriangulated : Pretriangulated (DerivedCategory C) :=
  Triangulated.Localization.pretriangulated Qh (HomotopyCategory.subcategoryAcyclic C).W

/-- The localization functor `H(C) ⥤ D(C)` is triangulated. -/
instance Qh_isTriangulated : (Qh (C := C)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor Qh (HomotopyCategory.subcategoryAcyclic C).W

/-- The derived category is triangulated. -/
noncomputable instance isTriangulated : IsTriangulated (DerivedCategory C) :=
  Triangulated.Localization.isTriangulated Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).W

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (C := C))).Full :=
  inferInstanceAs (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso C) D).Full

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (C := C))).Faithful :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso C) D).Faithful

/-- The distinguished triangles of `D(C)` are the triangles isomorphic to the images of the
standard triangles `M → N → cone f → M⟦1⟧` of morphisms of dg modules. -/
theorem mem_distTriang_iff (T : Triangle (DerivedCategory C)) :
    (T ∈ distTriang (DerivedCategory C)) ↔ ∃ (M N : CatModule.{w} C) (f : M ⟶ N),
      Nonempty (T ≅ Q.mapTriangle.obj (cone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨M, N, f, ⟨e'⟩⟩⟩
    exact ⟨M, N, f, ⟨e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C) Qh).symm.app _⟩⟩
  · rintro ⟨M, N, f, ⟨e⟩⟩
    exact isomorphic_distinguished _
      (Qh.map_distinguished _ (HomotopyCategory.triangleh_distinguished f)) _
      (e ≪≫ (Functor.mapTriangleCompIso (HomotopyCategory.quotient C) Qh).app _)

/-! ### Cohomology -/

/-- The `n`-th cohomology at an object `X` of `C`, as a functor `D(C) ⥤ AddCommGrp`, induced by
the cohomology functor at `X` on the homotopy category. -/
noncomputable def cohomologyFunctor (X : C) (n : ℤ) : DerivedCategory C ⥤ AddCommGrp.{w} :=
  Localization.lift _ (HomotopyCategory.cohomologyFunctor_inverts_quasiIso C X n) Qh

/-- The cohomology functor at `X` on `D(C)` is induced by the cohomology functor at `X` on
`H(C)`. -/
noncomputable def cohomologyFunctorFactorsh (X : C) (n : ℤ) :
    Qh ⋙ cohomologyFunctor X n ≅ HomotopyCategory.cohomologyFunctor.{w} X n :=
  Localization.fac _ (HomotopyCategory.cohomologyFunctor_inverts_quasiIso C X n) Qh

/-- The cohomology functors on the derived category are homological. -/
instance cohomologyFunctor_isHomological (X : C) (n : ℤ) :
    (cohomologyFunctor (C := C) X n).IsHomological :=
  Functor.isHomological_of_localization Qh _ _ (cohomologyFunctorFactorsh X n)

/-! ### Isomorphisms and zero objects -/

/-- A morphism of the homotopy category becomes an isomorphism in the derived category iff it
is a quasi-isomorphism. -/
theorem isIso_Qh_map_iff {M N : HomotopyCategory.{w} C} (f : M ⟶ N) :
    IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso C f := by
  refine ⟨fun hf => ?_, fun hf => Localization.inverts Qh (HomotopyCategory.quasiIso C) _ hf⟩
  rw [HomotopyCategory.mem_quasiIso_iff]
  intro X n
  rw [← NatIso.isIso_map_iff (cohomologyFunctorFactorsh X n) f]
  dsimp
  infer_instance

/-- A morphism of dg modules becomes an isomorphism in the derived category iff it is a
quasi-isomorphism. -/
theorem isIso_Q_map_iff {M N : CatModule.{w} C} (f : M ⟶ N) :
    IsIso (Q.map f) ↔ IsQuasiIso f :=
  (isIso_Qh_map_iff _).trans (HomotopyCategory.quotient_map_mem_quasiIso_iff f)

/-- The functor `Q : CatModule C ⥤ D(C)` is a localization functor for the quasi-isomorphisms of
dg modules. -/
instance Q_isLocalization : (Q (C := C)).IsLocalization (CatModule.quasiIso C) :=
  Functor.IsLocalization.comp (HomotopyCategory.quotient C) Qh
    (homotopyEquivalences C) (HomotopyCategory.quasiIso C) (CatModule.quasiIso C)
    (fun _ _ f hf => (isIso_Q_map_iff f).mpr hf) (homotopyEquivalences_le_quasiIso C)
    (HomotopyCategory.quasiIso_eq_quasiIso_map_quotient C).le

private theorem isIso_iff_isZero_of_isZero {D : Type*} [Category D] [HasZeroMorphisms D]
    {Y Z : D} (g : Y ⟶ Z) (hZ : IsZero Z) : IsIso g ↔ IsZero Y :=
  ⟨fun _ => hZ.of_iso (asIso g), fun hY => ⟨⟨0, hY.eq_of_src _ _, hZ.eq_of_src _ _⟩⟩⟩

/-- An object of the homotopy category becomes zero in the derived category iff it is
acyclic. -/
theorem isZero_Qh_obj_iff (M : HomotopyCategory.{w} C) :
    IsZero (Qh.obj M) ↔ (HomotopyCategory.subcategoryAcyclic C).P M := by
  have h₀ : IsZero (Qh.obj (0 : HomotopyCategory.{w} C)) := Qh.map_isZero (Limits.isZero_zero _)
  rw [← isIso_iff_isZero_of_isZero (Qh.map (0 : M ⟶ 0)) h₀, isIso_Qh_map_iff,
    HomotopyCategory.mem_quasiIso_iff, HomotopyCategory.mem_subcategoryAcyclic_iff]
  exact forall_congr' fun X => forall_congr' fun n =>
    isIso_iff_isZero_of_isZero _ (Functor.map_isZero _ (Limits.isZero_zero _))

/-- A dg module becomes zero in the derived category iff it is acyclic. -/
theorem isZero_Q_obj_iff (M : CatModule.{w} C) : IsZero (Q.obj M) ↔ IsAcyclic M :=
  (isZero_Qh_obj_iff _).trans (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff M)

end DerivedCategory

end CatModule

end DG
