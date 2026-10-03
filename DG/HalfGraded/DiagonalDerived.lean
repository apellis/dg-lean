import DG.HalfGraded.DiagonalCohomology
import DG.Derived.Basic
import DG.Category.Derived.Basic

/-!
# The diagonal functor on derived categories

The diagonal module functor descends through the existing localizations, for arbitrary
ordinary dg rings and independently chosen morphism universes. The comparison is a natural
isomorphism, not a definitional identification of the localized objects. Its naturality
computes the functor on actual module morphisms and on roofs with quasi-isomorphic left leg.

This construction does not assert full faithfulness, preservation of compact objects, or
an equivalence with the whole half-graded derived category.
-/

open CategoryTheory

universe w' w v u

namespace DG.Diagonal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

omit [HasDerivedCategory.{w, v} A] in
/-- The diagonal module functor followed by localization inverts ordinary quasi-isomorphisms.
The proof uses the all-weight cohomology theorem, including unsupported-weight vanishing. -/
theorem toCatModuleCompQ_inverts :
    (DGModuleCat.quasiIso A).IsInvertedBy
      (toCatModule.{v} A ⋙ CatModule.DerivedCategory.Q) := by
  intro M N f hf
  exact (CatModule.DerivedCategory.isIso_Q_map_iff _).mpr
    ((quasiIso_toCatModule_iff f).mpr hf)

/-- The functor on the existing derived categories induced by diagonal half-regrading. -/
def toDerived : DerivedCategory.{w, v} A ⥤
    CatModule.DerivedCategory.{w', v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  Localization.lift (toCatModule A ⋙ CatModule.DerivedCategory.Q)
    (toCatModuleCompQ_inverts A) DerivedCategory.Q

noncomputable instance toDerivedLifting :
    Localization.Lifting DerivedCategory.Q (DGModuleCat.quasiIso A)
      (toCatModule A ⋙ CatModule.DerivedCategory.Q) (toDerived A) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ DerivedCategory.Q))

/-- Localization comparison for the actual diagonal ordinary-module functor. -/
def QCompToDerivedIso :
    DerivedCategory.Q ⋙ toDerived A ≅ toCatModule A ⋙ CatModule.DerivedCategory.Q :=
  Localization.Lifting.iso DerivedCategory.Q (DGModuleCat.quasiIso A) _ _

/-- The comparison on an actual ordinary dg module. -/
def toDerivedObjIso (M : DGModuleCat.{v} A) :
    (toDerived A).obj (DerivedCategory.Q.obj M) ≅
      CatModule.DerivedCategory.Q.obj ((toCatModule A).obj M) :=
  (QCompToDerivedIso A).app M

variable {A}

/-- Naturality computes the image of every actual dg module map. -/
@[reassoc]
theorem toDerived_map_Q {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    (toDerived A).map (DerivedCategory.Q.map f) ≫ (toDerivedObjIso A N).hom =
      (toDerivedObjIso A M).hom ≫ CatModule.DerivedCategory.Q.map ((toCatModule A).map f) :=
  (QCompToDerivedIso A).hom.naturality f

/-- Invertibility of images of actual module maps is detected exactly by ordinary
quasi-isomorphisms. This alone is not a full-faithfulness assertion. -/
theorem isIso_toDerived_map_Q_iff {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    IsIso ((toDerived A).map (DerivedCategory.Q.map f)) ↔ f.hom.IsQuasiIso := by
  exact (NatIso.isIso_map_iff (QCompToDerivedIso A) f).trans
    ((CatModule.DerivedCategory.isIso_Q_map_iff _).trans (isQuasiIso_toCatModule_iff f))

/-- A quasi-isomorphism is sent to the actual isomorphism induced by its diagonal lift. -/
def toDerivedQuasiIso {M N : DGModuleCat.{v} A} (f : M ⟶ N) (hf : f.hom.IsQuasiIso) :
    (toDerived A).obj (DerivedCategory.Q.obj M) ≅
      (toDerived A).obj (DerivedCategory.Q.obj N) := by
  letI := (DerivedCategory.isIso_Q_map_iff f).mpr hf
  exact (toDerived A).mapIso (asIso (DerivedCategory.Q.map f))

/-- A genuine roof consumer: diagonal localization takes the roof `M ← P → N` to
its componentwise diagonal roof, conjugated by the localization comparison. -/
theorem toDerived_map_roof {M N P : DGModuleCat.{v} A}
    (s : P ⟶ M) (f : P ⟶ N) (hs : s.hom.IsQuasiIso) :
    letI := (DerivedCategory.isIso_Q_map_iff s).mpr hs
    letI := (CatModule.DerivedCategory.isIso_Q_map_iff ((toCatModule A).map s)).mpr
      ((isQuasiIso_toCatModule_iff s).mpr hs)
    (toDerived A).map (inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map f) =
      (toDerivedObjIso A M).hom ≫
        inv (CatModule.DerivedCategory.Q.map ((toCatModule A).map s)) ≫
        CatModule.DerivedCategory.Q.map ((toCatModule A).map f) ≫
        (toDerivedObjIso A N).inv := by
  let := (DerivedCategory.isIso_Q_map_iff s).mpr hs
  let := (CatModule.DerivedCategory.isIso_Q_map_iff ((toCatModule A).map s)).mpr
    ((isQuasiIso_toCatModule_iff s).mpr hs)
  rw [Functor.map_comp, Functor.map_inv]
  apply (cancel_mono (toDerivedObjIso A N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [toDerived_map_Q]
  apply (cancel_epi ((toDerived A).map (DerivedCategory.Q.map s))).mp
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, toDerived_map_Q]
  simp

end

end DG.Diagonal
