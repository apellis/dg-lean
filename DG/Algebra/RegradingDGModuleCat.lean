import DG.Algebra.RegradingModuleCat
import DG.Homotopy.ModuleCat

/-!
# Periodic dg modules as objects of `DGModuleCat`

Let `(B, ℬ, dA)` be a `ℤ/2`-graded dg ring (`DG.IsZMod2DGRing`). Its periodization
`Periodize ℬ` is a dg ring (`DG.Periodize.dgAddCommGroup`, `DG.Periodize.dgRing`), and the
category `DG.GradedModuleCat.PeriodicDGModuleCat ℬ hA` of `DG.Algebra.RegradingModuleCat` (graded
`Periodize ℬ`-modules with a differential satisfying `DG.IsPeriodicDGModule`) is a description of
dg modules over it on data. This file identifies it with the library's category of dg modules
`DG.DGModuleCat (Periodize ℬ)`:

* `DG.GradedModuleCat.PeriodizeDGModuleCat hA`: `DGModuleCat (Periodize ℬ)` for the dg ring
  structure `DG.Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential` (which is not an instance);
* `DG.GradedModuleCat.periodicToDGModuleCat hA`, `DG.GradedModuleCat.dgModuleCatToPeriodic hA`:
  the two functors, the identity on underlying types, gradings, differentials and maps;
* `DG.GradedModuleCat.periodicDGModuleCatEquivalence hA :
    PeriodicDGModuleCat ℬ hA ≌ PeriodizeDGModuleCat hA` (an isomorphism of categories: the unit
  and counit are identities);
* `DG.GradedModuleCat.zmod2DGModuleCatEquivalence hA :
    ZMod2DGModuleCat ℬ dA ≌ PeriodizeDGModuleCat hA`: `ℤ/2`-graded dg `B`-modules are
  equivalent to dg modules over the periodization, the composite with
  `DG.GradedModuleCat.periodizeDGEquivalence`.
-/

universe v

noncomputable section

namespace DG

open CategoryTheory DirectSum

namespace GradedModuleCat

variable {B τ : Type*} [Ring B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ZMod 2 → τ}
  [GradedRing ℬ] {dA : B →+ B} (hA : IsZMod2DGRing ℬ dA)

/-- The category `DGModuleCat (Periodize ℬ)` of dg modules over the periodization of a
`ℤ/2`-graded dg ring, for the dg structure `DG.Periodize.dgAddCommGroup` of `Periodize ℬ`. -/
abbrev PeriodizeDGModuleCat : Type _ :=
  letI := Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential
  DGModuleCat.{v} (Periodize ℬ)

/-- A periodic dg module, as an object of `DGModuleCat (Periodize ℬ)`. -/
def periodicToDGModuleCatObj (X : PeriodicDGModuleCat.{v} ℬ hA) : PeriodizeDGModuleCat.{v} hA :=
  letI := Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential
  letI := X.prop.dgAddCommGroup
  haveI := X.prop.dgModule
  DGModuleCat.of (Periodize ℬ) X.obj

/-- The functor from periodic dg modules (on data) to `DGModuleCat (Periodize ℬ)`: the identity
on underlying types, gradings, differentials and maps. -/
def periodicToDGModuleCat : PeriodicDGModuleCat.{v} ℬ hA ⥤ PeriodizeDGModuleCat.{v} hA where
  obj X := periodicToDGModuleCatObj hA X
  map {X Y} f :=
    letI := Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential
    letI := X.prop.dgAddCommGroup
    letI := Y.prop.dgAddCommGroup
    haveI := X.prop.dgModule
    haveI := Y.prop.dgModule
    DGModuleCat.ofHom (M := X.obj) (N := Y.obj)
      { toLinearMap := f.hom.hom
        map_mem' := fun hm => f.hom.map_mem hm
        map_d' := f.comm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A dg module over `Periodize ℬ`, as a periodic dg module on data. -/
def dgModuleCatToPeriodicObj (M : PeriodizeDGModuleCat.{v} hA) : PeriodicDGModuleCat.{v} ℬ hA :=
  letI := Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential
  haveI : SetLike.GradedSMul (periodizeGrading ℬ) (DGAddCommGroup.grading (M := M)) :=
    DGModule.toGradedSMul (A := Periodize ℬ) (M := M)
  { obj := GradedModuleCat.of (periodizeGrading ℬ) M (DGAddCommGroup.grading (M := M))
    d := d
    prop :=
      { map_mem := fun hm => d_mem hm
        d_d := fun x => d_d x
        d_smul := fun hp x => DGModule.d_smul' (A := Periodize ℬ) hp x } }

/-- The functor from `DGModuleCat (Periodize ℬ)` to periodic dg modules (on data): the identity
on underlying types, gradings, differentials and maps. -/
def dgModuleCatToPeriodic : PeriodizeDGModuleCat.{v} hA ⥤ PeriodicDGModuleCat.{v} ℬ hA where
  obj M := dgModuleCatToPeriodicObj hA M
  map f :=
    letI := Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential
    { hom := ⟨f.hom.toLinearMap, fun hm => f.hom.map_mem hm⟩
      comm := fun x => f.hom.map_d x }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Periodic dg modules are the dg modules over the periodization.** The category of periodic
dg modules on data, `PeriodicDGModuleCat ℬ hA`, is equivalent (indeed isomorphic, the unit and
counit being identities) to the category `DGModuleCat (Periodize ℬ)` of dg modules over the dg
ring `Periodize ℬ`. -/
def periodicDGModuleCatEquivalence :
    PeriodicDGModuleCat.{v} ℬ hA ≌ PeriodizeDGModuleCat.{v} hA :=
  CategoryTheory.Equivalence.mk (periodicToDGModuleCat hA) (dgModuleCatToPeriodic hA)
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- **`ℤ/2`-graded dg modules and dg modules over the periodization.** For a `ℤ/2`-graded dg
ring `(B, ℬ, dA)`, the category of `ℤ/2`-graded dg `B`-modules is equivalent to the category
`DGModuleCat (Periodize ℬ)` of dg modules over the periodization, by `M ↦ Periodize M`. -/
def zmod2DGModuleCatEquivalence : ZMod2DGModuleCat.{v} ℬ dA ≌ PeriodizeDGModuleCat.{v} hA :=
  (periodizeDGEquivalence hA).trans (periodicDGModuleCatEquivalence hA)

end GradedModuleCat

end DG
