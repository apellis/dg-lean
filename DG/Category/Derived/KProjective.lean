import DG.Category.Derived.Basic
import DG.Category.Resolution.Resolution
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# K-projective modules and the derived category of a dg category

Let `C` be a dg category. The K-projective dg modules over `C` are exactly the objects of the
homotopy category `H(C)` which are left orthogonal to the acyclic modules. By a general property
of Verdier localizations (Mathlib's
`ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`), morphisms out of a K-projective
module in `H(C)` and in `D(C)` therefore agree. Together with the existence of K-projective
resolutions (`DG.CatModule.exists_kProjective_resolution`), this shows that the full subcategory of K-projective objects of `H(C)` is equivalent to `D(C)`
[Keller, *Deriving DG categories*, §3.1, Cor. 3.1], [Stacks 09KV].

## Main definitions and results

* `DG.CatModule.HomotopyCategory.subcategoryKProjective C`: the K-projective objects of `H(C)`,
  defined as the left orthogonal of the acyclic objects;
  `DG.CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff`: it consists of
  the (images of) K-projective dg modules.
* `DG.CatModule.DerivedCategory.Qh_map_bijective_of_isKProjective`: for `P` K-projective and any
  `N`, `Hom_{H(C)}(P, N) → Hom_{D(C)}(P, N)` is bijective;
  `DG.CatModule.DerivedCategory.homAddEquivOfIsKProjective`:
  `Hom_{D(C)}(Q P, Q N) ≃+ H⁰(HOM_C(P, N))`.
* `DG.CatModule.isIso_quotient_map_of_isQuasiIso`: a quasi-isomorphism between K-projective dg
  modules is a homotopy equivalence (an isomorphism in `H(C)`).
* `DG.CatModule.DerivedCategory.exists_isKProjective_iso`: every object of `D(C)` is the image of
  a K-projective dg module; `DG.CatModule.DerivedCategory.kProjRep` chooses one.
* `DG.CatModule.DerivedCategory.kProjectiveEquivalence`: the equivalence between the full
  subcategory of K-projective objects of `H(C)` and `D(C)`.

## Universes

Resolutions exist for dg modules in `CatModule.{max u v w} C` (see
`DG/Category/Resolution/Resolution.lean`), so the equivalence is stated in this universe.
-/

open CategoryTheory Limits

universe w'' w v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

namespace HomotopyCategory

variable (C) in
/-- The K-projective objects of the homotopy category: the left orthogonal of the acyclic
objects. -/
abbrev subcategoryKProjective : ObjectProperty (HomotopyCategory.{w} C) :=
  ObjectProperty.leftOrthogonal (subcategoryAcyclic C)

/-- The image of a dg module in the homotopy category is K-projective iff the dg module is. -/
theorem quotient_obj_mem_subcategoryKProjective_iff (P : CatModule.{w} C) :
    subcategoryKProjective C ((quotient C).obj P) ↔ IsKProjective P := by
  constructor
  · intro h N hN f
    rw [← quotient_map_eq_iff, Functor.map_zero]
    exact h ((quotient C).map f) ((quotient_obj_mem_subcategoryAcyclic_iff N).mpr hN)
  · intro h Y f hY
    obtain ⟨N, rfl⟩ := quotient_obj_surjective Y
    obtain ⟨g, rfl⟩ := (quotient C).map_surjective f
    rw [quotient_obj_mem_subcategoryAcyclic_iff] at hY
    rw [← Functor.map_zero (quotient C), quotient_map_eq_iff]
    exact h N hY g

end HomotopyCategory

namespace DerivedCategory

variable [HasDerivedCategory.{w'', w} C]

/-- Morphisms out of a K-projective dg module are the same in the homotopy category and in the
derived category. -/
theorem Qh_map_bijective_of_isKProjective {P : CatModule.{w} C} (hP : IsKProjective P)
    (Y : HomotopyCategory.{w} C) :
    Function.Bijective (Qh.map : ((HomotopyCategory.quotient C).obj P ⟶ Y) → _) :=
  ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated
    ((HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP) _ _

/-- For `P` K-projective, `Hom_{D(C)}(P, N)` is `H⁰(HOM_C(P, N))`. -/
noncomputable def homAddEquivOfIsKProjective {P : CatModule.{w} C} (hP : IsKProjective P)
    (N : CatModule.{w} C) : (Q.obj P ⟶ Q.obj N) ≃+ cohomology (HOM P N) 0 :=
  (AddEquiv.ofBijective (Qh.mapAddHom (X := (HomotopyCategory.quotient C).obj P)
    (Y := (HomotopyCategory.quotient C).obj N))
    (Qh_map_bijective_of_isKProjective hP _)).symm.trans
    (HomotopyCategory.homAddEquivCohomology P N)

end DerivedCategory

/-- A quasi-isomorphism between K-projective dg modules is a homotopy equivalence: its image in
the homotopy category is an isomorphism. -/
theorem isIso_quotient_map_of_isQuasiIso {P P' : CatModule.{w} C} (hP : IsKProjective P)
    (hP' : IsKProjective P') {f : P ⟶ P'} (hf : IsQuasiIso f) :
    IsIso ((HomotopyCategory.quotient C).map f) := by
  let := HasDerivedCategory.standard C
  have hQ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C).map f)) :=
    (DerivedCategory.isIso_Q_map_iff f).mpr hf
  obtain ⟨g, hg⟩ := (DerivedCategory.Qh_map_bijective_of_isKProjective hP' _).surjective
    (inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient C).map f)))
  refine ⟨g, (DerivedCategory.Qh_map_bijective_of_isKProjective hP _).injective ?_,
    (DerivedCategory.Qh_map_bijective_of_isKProjective hP' _).injective ?_⟩
  · simp [hg]
  · simp [hg]

namespace DerivedCategory

variable [HasDerivedCategory.{w'', max u v w} C]

/-- Every object of `D(C)` is isomorphic to the image of a K-projective dg module. -/
theorem exists_isKProjective_iso (X : DerivedCategory.{w'', max u v w} C) :
    ∃ P : CatModule.{max u v w} C, IsKProjective P ∧ Nonempty (X ≅ Q.obj P) := by
  obtain ⟨Z, ⟨e⟩⟩ :=
    (Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso C)).mem_essImage X
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨P, π, hP, hπ, -⟩ := exists_kProjective_resolution M
  have : IsIso (Q.map π) := (isIso_Q_map_iff π).mpr hπ
  exact ⟨P, hP, ⟨e.symm ≪≫ (asIso (Q.map π)).symm⟩⟩

/-- A chosen K-projective dg module representing an object of `D(C)`. -/
noncomputable def kProjRep (X : DerivedCategory.{w'', max u v w} C) : CatModule.{max u v w} C :=
  (exists_isKProjective_iso X).choose

theorem isKProjective_kProjRep (X : DerivedCategory.{w'', max u v w} C) :
    IsKProjective (kProjRep X) :=
  (exists_isKProjective_iso X).choose_spec.1

/-- The isomorphism `X ≅ Q (kProjRep X)`. -/
noncomputable def kProjRepIso (X : DerivedCategory.{w'', max u v w} C) :
    X ≅ Q.obj (kProjRep X) :=
  (exists_isKProjective_iso X).choose_spec.2.some

variable (C) in
/-- The composition `K-projective objects of H(C) ⥤ H(C) ⥤ D(C)`. -/
noncomputable abbrev kProjectiveFunctor :
    (HomotopyCategory.subcategoryKProjective.{max u v w} C).FullSubcategory ⥤
      DerivedCategory.{w''} C :=
  (HomotopyCategory.subcategoryKProjective C).ι ⋙ Qh

theorem kProjectiveFunctor_map_bijective
    (P Y : (HomotopyCategory.subcategoryKProjective.{max u v w} C).FullSubcategory) :
    Function.Bijective ((kProjectiveFunctor C).map : (P ⟶ Y) → _) := by
  obtain ⟨M, hM⟩ := HomotopyCategory.quotient_obj_surjective P.obj
  have hP := P.property
  rw [← hM, HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff] at hP
  have h := Qh_map_bijective_of_isKProjective (C := C) hP Y.obj
  rw [hM] at h
  exact h.comp ((ObjectProperty.fullyFaithfulι _).map_bijective P Y)

instance : (kProjectiveFunctor C).Full where
  map_surjective := (kProjectiveFunctor_map_bijective _ _).2

instance : (kProjectiveFunctor C).Faithful where
  map_injective h := (kProjectiveFunctor_map_bijective _ _).1 h

instance : (kProjectiveFunctor C).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨e⟩⟩ :=
      (Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso C)).mem_essImage Y
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, π, hP, hπ, -⟩ := exists_kProjective_resolution M
    have : IsIso (Q.map π) := (isIso_Q_map_iff π).mpr hπ
    exact ⟨⟨(HomotopyCategory.quotient C).obj P,
      (HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩,
      ⟨asIso (Q.map π) ≪≫ e⟩⟩

instance : (kProjectiveFunctor C).IsEquivalence where

variable (C) in
/-- The derived category of a dg category is equivalent to the full subcategory of K-projective
objects of the homotopy category. -/
noncomputable def kProjectiveEquivalence :
    (HomotopyCategory.subcategoryKProjective.{max u v w} C).FullSubcategory ≌
      DerivedCategory.{w''} C :=
  (kProjectiveFunctor C).asEquivalence

end DerivedCategory

end CatModule

end DG

