import DG.Derived.Basic
import DG.Derived.Resolution
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Localization.LocallySmall

/-!
# K-projective modules and the derived category of a dg ring

Let `A` be a dg ring. The K-projective dg modules are exactly the objects of the homotopy
category `H(A)` which are left orthogonal to the acyclic modules, so, by a general property of
Verdier localizations (Mathlib's `ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`),
morphisms out of a K-projective module in `H(A)` and in `D(A)` agree
[Keller, *Deriving DG categories*, §3.1], [Stacks 09KV]. This is the dg-ring counterpart of
`DG/Category/Derived/KProjective.lean`.

## Main definitions and results

* `DG.HomotopyCategory.subcategoryKProjective A`: the left orthogonal of the acyclic objects;
  `DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff`: it consists of the images of
  the K-projective dg modules.
* `DG.DerivedCategory.Qh_map_bijective_of_isKProjective`: for `P` K-projective,
  `Hom_{H(A)}(P, Y) → Hom_{D(A)}(P, Y)` is bijective; `DG.DerivedCategory.exists_Q_map_eq`,
  `DG.DerivedCategory.Q_map_eq_zero_iff`, `DG.DerivedCategory.Q_map_injective`;
  `DG.DerivedCategory.homAddEquivOfIsKProjective`: `Hom_{D(A)}(Q P, Q N) ≃+ H⁰(HOM_A(P, N))`.
* `DG.DerivedCategory.exists_iso_Q_obj`, `DG.DerivedCategory.exists_isKProjective_iso`: every
  object of `D(A)` is the image of a (K-projective) dg module.
* `DG.DerivedCategory.locallySmall`, `DG.HasDerivedCategory.small`: the derived category of dg
  modules in `Type (max u w)` can be chosen with morphisms in `Type (max u w)`.
-/

open CategoryTheory Limits

universe w'' w v u

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

namespace HomotopyCategory

variable (A) in
/-- The K-projective objects of the homotopy category: the left orthogonal of the acyclic
objects. -/
abbrev subcategoryKProjective : ObjectProperty (HomotopyCategory.{v} A) :=
  ObjectProperty.leftOrthogonal (subcategoryAcyclic A)

/-- The image of a dg module in the homotopy category is K-projective iff the dg module is. -/
theorem quotient_obj_mem_subcategoryKProjective_iff (P : DGModuleCat.{v} A) :
    subcategoryKProjective A ((quotient A).obj P) ↔ IsKProjective.{v} A P := by
  constructor
  · intro h N _ _ _ _ hN f
    have := h ((quotient A).map (DGModuleCat.ofHom f))
      ((quotient_obj_mem_subcategoryAcyclic_iff (DGModuleCat.of A N)).mpr hN)
    rw [← Functor.map_zero (quotient A), quotient_map_eq_iff] at this
    exact this
  · intro h Y f hY
    obtain ⟨N, rfl⟩ := quotient_obj_surjective Y
    obtain ⟨g, rfl⟩ := (quotient A).map_surjective f
    rw [quotient_obj_mem_subcategoryAcyclic_iff] at hY
    rw [← Functor.map_zero (quotient A), quotient_map_eq_iff]
    exact h N hY g.hom

end HomotopyCategory

namespace DerivedCategory

section

variable [HasDerivedCategory.{w, v} A]

/-- Morphisms out of a K-projective dg module are the same in the homotopy category and in the
derived category. -/
theorem Qh_map_bijective_of_isKProjective {P : DGModuleCat.{v} A} (hP : IsKProjective.{v} A P)
    (Y : HomotopyCategory.{v} A) :
    Function.Bijective (Qh.map : ((HomotopyCategory.quotient A).obj P ⟶ Y) → _) :=
  ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated
    ((HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP) _ _

/-- Every morphism `Q P ⟶ Q N` out of a K-projective dg module is the image of a morphism of dg
modules. -/
theorem exists_Q_map_eq {P N : DGModuleCat.{v} A} (hP : IsKProjective.{v} A P)
    (φ : Q.obj P ⟶ Q.obj N) : ∃ f : P ⟶ N, Q.map f = φ := by
  obtain ⟨f', hf'⟩ := (Qh_map_bijective_of_isKProjective hP _).2 φ
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective f'
  exact ⟨f, hf'⟩

/-- Two morphisms out of a K-projective module have the same image in `D(A)` iff they are
homotopic. -/
theorem Q_map_eq_iff {P N : DGModuleCat.{v} A} (hP : IsKProjective.{v} A P) (f g : P ⟶ N) :
    Q.map f = Q.map g ↔ Homotopic f.hom g.hom := by
  rw [← HomotopyCategory.quotient_map_eq_iff]
  exact (Qh_map_bijective_of_isKProjective hP _).1.eq_iff

/-- A morphism out of a K-projective module becomes zero in `D(A)` iff it is null-homotopic. -/
theorem Q_map_eq_zero_iff {P N : DGModuleCat.{v} A} (hP : IsKProjective.{v} A P) (f : P ⟶ N) :
    Q.map f = 0 ↔ Homotopic f.hom 0 := by
  rw [← Functor.map_zero Q P N, Q_map_eq_iff hP]
  rfl

/-- For `P` K-projective, `Hom_{D(A)}(Q P, Q N)` is `H⁰(HOM_A(P, N))`. -/
noncomputable def homAddEquivOfIsKProjective {P : DGModuleCat.{v} A} (hP : IsKProjective.{v} A P)
    (N : DGModuleCat.{v} A) : (Q.obj P ⟶ Q.obj N) ≃+ cohomology (DGModule.HOM A P N) 0 :=
  (AddEquiv.ofBijective (Qh.mapAddHom (X := (HomotopyCategory.quotient A).obj P)
    (Y := (HomotopyCategory.quotient A).obj N))
    (Qh_map_bijective_of_isKProjective hP _)).symm.trans
    (HomotopyCategory.homAddEquivCohomology P N)

omit [HasDerivedCategory.{w, v} A] in
/-- Every object of `D(A)` is isomorphic to the image of a dg module. -/
theorem exists_iso_Q_obj [HasDerivedCategory.{w, v} A] (Y : DerivedCategory.{w, v} A) :
    ∃ N : DGModuleCat.{v} A, Nonempty (Y ≅ Q.obj N) := by
  obtain ⟨Z, ⟨e⟩⟩ :=
    (Localization.essSurj (Qh (A := A)) (HomotopyCategory.quasiIso A)).mem_essImage Y
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  exact ⟨N, ⟨e.symm⟩⟩

end

section Resolution

variable [HasDerivedCategory.{w, max u v} A]

/-- Every object of `D(A)` is isomorphic to the image of a K-projective (indeed semi-free) dg
module. -/
theorem exists_isKProjective_iso (X : DerivedCategory.{w, max u v} A) :
    ∃ P : DGModuleCat.{max u v} A, IsKProjective.{max u v} A P ∧ Nonempty (X ≅ Q.obj P) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_Q_obj X
  obtain ⟨P, _, _, _, _, π, -, hπ, ⟨F⟩⟩ := exists_semiFreeResolution A M
  have : IsIso (Q.map (DGModuleCat.ofHom π)) := (isIso_Q_map_iff _).mpr hπ
  exact ⟨DGModuleCat.of A P, F.isKProjective, ⟨e ≪≫ (asIso (Q.map (DGModuleCat.ofHom π))).symm⟩⟩

/-- The derived category of a dg ring is locally small: its morphisms are `(max u v)`-small,
for dg modules with values in `Type (max u v)`. -/
theorem locallySmall : LocallySmall.{max u v} (DerivedCategory.{w, max u v} A) where
  hom_small X Y := by
    obtain ⟨P, hP, ⟨eX⟩⟩ := exists_isKProjective_iso X
    obtain ⟨N, ⟨eY⟩⟩ := exists_iso_Q_obj Y
    have : Small.{max u v} (Q.obj P ⟶ Q.obj N) :=
      small_of_surjective (f := fun f : P ⟶ N => Q.map f) fun φ => exists_Q_map_eq hP φ
    exact small_map (Iso.homCongr eX eY)

end Resolution

end DerivedCategory

variable (A) in
/-- A choice of the derived category of a dg ring with morphisms in `Type (max u v)`, for dg
modules with values in `Type (max u v)`, obtained by shrinking the morphisms of the constructed
localization. -/
@[instance_reducible]
noncomputable def HasDerivedCategory.small : HasDerivedCategory.{max u v, max u v} A :=
  letI : HasDerivedCategory.{_, max u v} A := HasDerivedCategory.standard A
  have := DerivedCategory.locallySmall.{_, v} (A := A)
  { toHasLocalization := MorphismProperty.hasLocalizationOfLocallySmall _ DerivedCategory.Qh }

end DG
