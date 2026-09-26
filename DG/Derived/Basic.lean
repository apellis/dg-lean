import DG.Derived.QuasiIso

/-!
# The derived category of a dg ring

Let `A` be a dg ring. The derived category `D(A)` is the localization of the homotopy category
`DG.HomotopyCategory A` of dg `A`-modules at the quasi-isomorphisms
`DG.HomotopyCategory.quasiIso A`. As in Mathlib's
`Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`, the localized category is not
constructed with a fixed universe of morphisms: we assume `[DG.HasDerivedCategory.{w} A]`, the
choice of a localization whose morphisms are in `Type w`
(`CategoryTheory.MorphismProperty.HasLocalization`). The constructed localization, with
morphisms in a larger universe, is `DG.HasDerivedCategory.standard A`; it should only be used to
prove statements which do not involve the derived category.

## Main definitions and results

* `DG.DerivedCategory A`, with the localization functors
  `DG.DerivedCategory.Qh : HomotopyCategory A ⥤ DerivedCategory A` (a localization functor for
  `quasiIso A`) and `DG.DerivedCategory.Q : DGModuleCat A ⥤ DerivedCategory A` (a localization
  functor for the quasi-isomorphisms of dg modules `DG.DGModuleCat.quasiIso A`, using that the
  homotopy category is the localization at the homotopy equivalences,
  `DG.HomotopyCategory.quotient_isLocalization`).
* `D(A)` is preadditive, has a zero object and a shift by `ℤ`, and is pretriangulated and
  triangulated; `Qh` commutes with the shifts and is a triangulated functor. The triangulated
  structure is obtained by Verdier localization (Mathlib's `Triangulated.Localization`), since
  `quasiIso A` is the class of morphisms whose cone is acyclic
  (`DG.HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`).
  `DG.DerivedCategory.mem_distTriang_iff`: the distinguished triangles are the triangles
  isomorphic to images of the standard triangles `M → N → Cone(f) → M⟦1⟧`.
* `DG.DerivedCategory.isIso_Q_map_iff`: `Q.map f` is an isomorphism iff `f` is a
  quasi-isomorphism; `DG.DerivedCategory.isZero_Q_obj_iff`: `Q.obj M` is zero iff `M` is
  acyclic.
* Cohomology: for a dg `R`-algebra `A`, the functors
  `DG.DerivedCategory.homologyFunctor R n : DerivedCategory A ⥤ ModuleCat R` induced by the
  cohomology functors on the homotopy category (`homologyFunctorFactorsh`; through `Q` they
  give the cohomology `M ↦ Hⁿ(M)` of dg modules, `homologyFunctorFactors`); they are
  homological.
  `DG.DerivedCategory.cohomologyAddEquiv R M n : Hⁿ(M) ≃+ Hⁿ(Q M)`. The case `R = ℤ`,
  composed with `ModuleCat ℤ ⥤ AddCommGrp`, is `DG.DerivedCategory.cohomologyFunctor A n`,
  defined for every dg ring.

Coproducts in `D(A)` are in `DG/Derived/Coproducts.lean`.

## Universes

For `A : Type u` and dg modules in `Type v`, `HomotopyCategory.{v} A` has objects in
`Type (max (v + 1) u)` and morphisms in `Type v`; `DG.HasDerivedCategory.{w, v} A` chooses a
localization with morphisms in `Type w`, and the standard choice has `w = max (v + 1) u`.
-/

open CategoryTheory Limits Pretriangulated ZeroObject

universe w v u w'

namespace DG

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The assumption that a localization of the homotopy category of dg `A`-modules (in
`Type v`) at the quasi-isomorphisms has been chosen, with morphisms in `Type w`. -/
abbrev HasDerivedCategory :=
  MorphismProperty.HasLocalization.{w} (HomotopyCategory.quasiIso.{v} A)

/-- The derived category obtained from the constructed localization. This should be used only
while proving statements which do not involve the derived category. -/
def HasDerivedCategory.standard : HasDerivedCategory.{max (v + 1) u, v} A :=
  MorphismProperty.HasLocalization.standard _

variable [HasDerivedCategory.{w, v} A]

/-- The derived category `D(A)` of a dg ring `A`: the localization of the homotopy category of
dg `A`-modules at the quasi-isomorphisms. -/
def DerivedCategory : Type (max (v + 1) u) := (HomotopyCategory.quasiIso.{v} A).Localization'

namespace DerivedCategory

instance : Category.{w} (DerivedCategory A) := by
  dsimp [DerivedCategory]
  infer_instance

variable {A}

/-- The localization functor `H(A) ⥤ D(A)`. -/
def Qh : HomotopyCategory.{v} A ⥤ DerivedCategory A := MorphismProperty.Q' _

/-- The localization functor `DGModuleCat A ⥤ D(A)`. -/
def Q : DGModuleCat.{v} A ⥤ DerivedCategory A := HomotopyCategory.quotient A ⋙ Qh

variable (A) in
/-- The isomorphism `HomotopyCategory.quotient A ⋙ Qh ≅ Q` (an identity). -/
def quotientCompQhIso : HomotopyCategory.quotient A ⋙ Qh ≅ Q (A := A) := Iso.refl _

instance Qh_isLocalization : (Qh (A := A)).IsLocalization (HomotopyCategory.quasiIso A) := by
  dsimp only [Qh, DerivedCategory]
  infer_instance

instance : (Qh (A := A)).IsLocalization (HomotopyCategory.subcategoryAcyclic A).W := by
  rw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory A) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic A).W

instance : (Qh (A := A)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic A).W

instance : (Q (A := A)).Additive := by
  dsimp only [Q]
  infer_instance

noncomputable instance : HasZeroObject (DerivedCategory A) :=
  Qh.hasZeroObject_of_additive

noncomputable instance : HasShift (DerivedCategory A) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic A).W ℤ

noncomputable instance Qh_commShift : (Qh (A := A)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic A).W ℤ

noncomputable instance : (Q (A := A)).CommShift ℤ := by
  dsimp only [Q]
  infer_instance

instance (n : ℤ) : (shiftFunctor (DerivedCategory A) n).Additive := by
  rw [Localization.functor_additive_iff Qh (HomotopyCategory.subcategoryAcyclic A).W]
  exact Functor.additive_of_iso (Qh.commShiftIso n)

/-- The derived category is pretriangulated. -/
noncomputable instance pretriangulated : Pretriangulated (DerivedCategory A) :=
  Triangulated.Localization.pretriangulated Qh (HomotopyCategory.subcategoryAcyclic A).W

/-- The localization functor `H(A) ⥤ D(A)` is triangulated. -/
instance Qh_isTriangulated : (Qh (A := A)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor Qh (HomotopyCategory.subcategoryAcyclic A).W

/-- The derived category is triangulated. -/
noncomputable instance isTriangulated : IsTriangulated (DerivedCategory A) :=
  Triangulated.Localization.isTriangulated Qh (HomotopyCategory.subcategoryAcyclic A).W

instance : (Qh (A := A)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic A).W

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (A := A))).Full :=
  inferInstanceAs (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso A) D).Full

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (A := A))).Faithful :=
  inferInstanceAs (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso A) D).Faithful

/-- The distinguished triangles of `D(A)` are the triangles isomorphic to the images of the
standard triangles `M → N → Cone(f) → M⟦1⟧` of morphisms of dg modules. -/
theorem mem_distTriang_iff (T : Triangle (DerivedCategory A)) :
    (T ∈ distTriang (DerivedCategory A)) ↔ ∃ (M N : DGModuleCat.{v} A) (f : M ⟶ N),
      Nonempty (T ≅ Q.mapTriangle.obj (Cone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨M, N, f, ⟨e'⟩⟩⟩
    exact ⟨M, N, f, ⟨e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient A) Qh).symm.app _⟩⟩
  · rintro ⟨M, N, f, ⟨e⟩⟩
    exact isomorphic_distinguished _
      (Qh.map_distinguished _ (HomotopyCategory.triangleh_distinguished f)) _
      (e ≪≫ (Functor.mapTriangleCompIso (HomotopyCategory.quotient A) Qh).app _)

/-! ### Cohomology -/

section Cohomology

variable (R : Type w') [CommRing R] [Algebra R A] [DGAlgebra R A]

/-- The `n`-th cohomology functor `D(A) ⥤ ModuleCat R` of a dg `R`-algebra `A`, induced by the
cohomology functor on the homotopy category. -/
noncomputable def homologyFunctor (n : ℤ) : DerivedCategory A ⥤ ModuleCat.{v} R :=
  Localization.lift _ (HomotopyCategory.homologyFunctor_inverts_quasiIso A R n) Qh

/-- The cohomology functor on `D(A)` is induced by the cohomology functor on `H(A)`. -/
noncomputable def homologyFunctorFactorsh (n : ℤ) :
    Qh ⋙ homologyFunctor R n ≅ HomotopyCategory.homologyFunctor R A n :=
  Localization.fac _ (HomotopyCategory.homologyFunctor_inverts_quasiIso A R n) Qh

/-- The cohomology functors on the derived category are homological. -/
instance homologyFunctor_isHomological (n : ℤ) : (homologyFunctor (A := A) R n).IsHomological :=
  Functor.isHomological_of_localization Qh _ _ (homologyFunctorFactorsh R n)

/-- The cohomology functor on `D(A)` composed with `Q` is the cohomology `M ↦ Hⁿ(M)` of dg
modules. -/
noncomputable def homologyFunctorFactors (n : ℤ) :
    Q ⋙ homologyFunctor R n ≅ DGModuleCat.cohomologyFunctor.{v} R A n :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (HomotopyCategory.quotient A)
    (homologyFunctorFactorsh R n) ≪≫ HomotopyCategory.quotientCompHomologyFunctorIso R A n

/-- The cohomology of a dg module is the cohomology of its image in the derived category. -/
noncomputable def cohomologyAddEquiv (M : DGModuleCat.{v} A) (n : ℤ) :
    cohomology M n ≃+ (homologyFunctor R n).obj (Q.obj M) :=
  ((homologyFunctorFactors R n).app M).symm.toLinearEquiv.toAddEquiv

end Cohomology

variable (A) in
/-- The `n`-th cohomology functor `D(A) ⥤ AddCommGrp` of a dg ring `A`. -/
noncomputable def cohomologyFunctor (n : ℤ) : DerivedCategory A ⥤ AddCommGrp.{v} :=
  homologyFunctor ℤ n ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrp.{v}

instance (n : ℤ) : (cohomologyFunctor A n).PreservesZeroMorphisms := by
  dsimp only [cohomologyFunctor]
  infer_instance

/-- The cohomology functors `D(A) ⥤ AddCommGrp` are homological. -/
instance cohomologyFunctor_isHomological (n : ℤ) : (cohomologyFunctor A n).IsHomological where
  exact T hT := ((homologyFunctor ℤ n).map_distinguished_exact T hT).map
    (forget₂ (ModuleCat.{v} ℤ) AddCommGrp.{v})

/-- `Hⁿ(M) ≃+ Hⁿ(Q M)` for the cohomology functor `D(A) ⥤ AddCommGrp`. -/
noncomputable def cohomologyFunctorObjQAddEquiv (M : DGModuleCat.{v} A) (n : ℤ) :
    cohomology M n ≃+ (cohomologyFunctor A n).obj (Q.obj M) :=
  cohomologyAddEquiv ℤ M n

/-! ### Isomorphisms and zero objects -/

/-- A morphism of the homotopy category becomes an isomorphism in the derived category iff it
is a quasi-isomorphism. -/
theorem isIso_Qh_map_iff {X Y : HomotopyCategory.{v} A} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso A f := by
  refine ⟨fun hf n => ?_, fun hf => Localization.inverts Qh (HomotopyCategory.quasiIso A) _ hf⟩
  change IsIso ((HomotopyCategory.homologyFunctor ℤ A n).map f)
  rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh ℤ n) f]
  dsimp
  infer_instance

/-- A morphism of dg modules becomes an isomorphism in the derived category iff it is a
quasi-isomorphism. -/
theorem isIso_Q_map_iff {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    IsIso (Q.map f) ↔ f.hom.IsQuasiIso :=
  (isIso_Qh_map_iff _).trans (HomotopyCategory.quotient_map_mem_quasiIso_iff f)

/-- The functor `Q : DGModuleCat A ⥤ D(A)` is a localization functor for the
quasi-isomorphisms of dg modules. -/
instance Q_isLocalization : (Q (A := A)).IsLocalization (DGModuleCat.quasiIso A) :=
  Functor.IsLocalization.comp (HomotopyCategory.quotient A) Qh
    (DGModuleCat.homotopyEquivalences A) (HomotopyCategory.quasiIso A) (DGModuleCat.quasiIso A)
    (fun _ _ f hf => (isIso_Q_map_iff f).mpr hf) (DGModuleCat.homotopyEquivalences_le_quasiIso A)
    (HomotopyCategory.quasiIso_eq_quasiIso_map_quotient A).le

private theorem isIso_iff_isZero_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {Y Z : C} (g : Y ⟶ Z) (hZ : IsZero Z) : IsIso g ↔ IsZero Y :=
  ⟨fun _ => hZ.of_iso (asIso g), fun hY => ⟨⟨0, hY.eq_of_src _ _, hZ.eq_of_src _ _⟩⟩⟩

/-- An object of the homotopy category becomes zero in the derived category iff it is
acyclic. -/
theorem isZero_Qh_obj_iff (X : HomotopyCategory.{v} A) :
    IsZero (Qh.obj X) ↔ (HomotopyCategory.subcategoryAcyclic A).P X := by
  have h₀ : IsZero (Qh.obj (0 : HomotopyCategory.{v} A)) := Qh.map_isZero (isZero_zero _)
  rw [← isIso_iff_isZero_of_isZero (Qh.map (0 : X ⟶ 0)) h₀, isIso_Qh_map_iff,
    HomotopyCategory.mem_quasiIso_iff, HomotopyCategory.mem_subcategoryAcyclic_iff]
  exact forall_congr' fun n => isIso_iff_isZero_of_isZero _ (Functor.map_isZero _ (isZero_zero _))

/-- A dg module becomes zero in the derived category iff it is acyclic. -/
theorem isZero_Q_obj_iff (M : DGModuleCat.{v} A) : IsZero (Q.obj M) ↔ IsAcyclic M :=
  (isZero_Qh_obj_iff _).trans (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff M)

end DerivedCategory

end DG
