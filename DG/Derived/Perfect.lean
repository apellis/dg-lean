import DG.Category.Derived.Comparison
import DG.Category.Derived.Small
import DG.Derived.Coproducts
import DG.K0.Compact

/-!
# The perfect derived category of a dg ring

Let `A` be a dg ring and `D(A)` its derived category, for dg modules with values in the universe
`u` of `A` (`[DG.HasDerivedCategory.{w', u} A]`). This file shows that `A` is a compact
generator of `D(A)`, so that the compact objects of `D(A)` form the thick subcategory generated
by `A`, and defines the perfect derived category `D^c(A)`.

The results are transported from the one-object dg category `SingleObj A` along the triangulated
equivalence `DG.CatModule.DerivedCategory.singleObjEquivalence A : D(SingleObj A) ≌ D(A)`, under
which `A` corresponds to the representable module (`DG.DerivedCategory.singleObjEquivalenceObjIso`
and `DG.CatModule.IsCornerGenerator.isoOfGen`).

## Main definitions and results

* `DG.CompactlyGenerates.of_equivalence`: compact generation is invariant under equivalences.
* `DG.DerivedCategory.isCompact_Q_self`: `A` is compact in `D(A)` (roadmap 5.2).
* `DG.DerivedCategory.compactlyGenerates`: `A` compactly generates `D(A)`, and
  `DG.DerivedCategory.thickClosure_self_eq_isCompact`: the compact objects of `D(A)` are the thick
  closure of `A` [Keller, *Deriving DG categories*, Thm. 5.3] (roadmap 5.3). These two need a
  model of `D(A)` whose morphisms lie in the universe `u` (`[DG.HasDerivedCategory.{u, u} A]`),
  since compact generation refers to coproducts indexed by types of that universe.
* `DG.PerfectDerivedCategory A`: the perfect derived category `D^c(A)`, the full triangulated
  subcategory of compact objects of `D(A)`.
-/

open CategoryTheory Limits Pretriangulated

universe w' w'' u

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]


/-! ### Transport of compact generation along equivalences -/

section Transport

variable {T : Type*} [Category.{w'} T] [HasShift T ℤ] [Preadditive T]
  {T' : Type*} [Category.{w'} T'] [HasShift T' ℤ] [Preadditive T']

/-- Compact generation is invariant under equivalences commuting with the shifts: if `G`
compactly generates `T` and `e : T ≌ T'`, any family `G'` with `e.functor.obj (G i) ≅ G' i`
compactly generates `T'`. -/
theorem CompactlyGenerates.of_equivalence {ι : Type w''} {G : ι → T}
    (hG : CompactlyGenerates G) (e : T ≌ T') [e.functor.Additive] [e.functor.CommShift ℤ]
    (G' : ι → T') (f : ∀ i, e.functor.obj (G i) ≅ G' i) : CompactlyGenerates G' where
  isCompact i := ((hG.isCompact i).map_of_equivalence e).of_iso (f i).symm
  isZero_of_forall_eq_zero Y h := by
    refine IsZero.of_iso (e.functor.map_isZero (hG.isZero_of_forall_eq_zero _ fun i n φ => ?_))
      (e.counitIso.app Y).symm
    have h0 := h i n ((f i).inv⟦n⟧' ≫ (e.functor.commShiftIso n).inv.app (G i) ≫
      e.functor.map φ ≫ e.counitIso.hom.app Y)
    rw [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_left_eq_zero,
      Preadditive.IsIso.comp_right_eq_zero] at h0
    exact e.functor.map_injective (h0.trans (e.functor.map_zero _ _).symm)

end Transport

namespace CatModule

/-- The dg ring `A`, regarded as a dg module over `SingleObj A`, is free on the generator `1`. -/
theorem isCornerGenerator_toCatModuleObj_self :
    IsCornerGenerator (DGModuleCat.toCatModuleObj (DGModuleCat.of A A))
      (DGCategory.Idempotent.id (SingleObj.star A)) 0
      (show (DGModuleCat.toCatModuleObj (DGModuleCat.of A A)).obj (SingleObj.star A) from
        (1 : A)) :=
  IsCornerGenerator.of_bijective (one_mem_grading (A := A)) (d_one (A := A)) fun _ =>
    ⟨fun f g h => by simpa [DGModuleCat.toCatModuleObj_smul] using h,
      fun a => ⟨(a : A), by simp⟩⟩

/-- Two dg modules which are free on generators of the same degree at the same object are
isomorphic, by the morphisms exchanging the generators. -/
noncomputable def IsCornerGenerator.isoOfGen {C : Type*} [Category C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] {R R' : CatModule.{u} C} {X : C} {k : ℤ}
    {g : R.obj X} {g' : R'.obj X} (hg : IsCornerGenerator R (DGCategory.Idempotent.id X) k g)
    (hg' : IsCornerGenerator R' (DGCategory.Idempotent.id X) k g') : R ≅ R' where
  hom := hg.homOfCocycle g' hg'.mem_grading hg'.d_eq_zero
  inv := hg'.homOfCocycle g hg.mem_grading hg.d_eq_zero
  hom_inv_id := hg.ext_hom (by
    rw [comp_app, hg.homOfCocycle_app_gen, hg'.homOfCocycle_app_gen, id_app])
  inv_hom_id := hg'.ext_hom (by
    rw [comp_app, hg'.homOfCocycle_app_gen, hg.homOfCocycle_app_gen, id_app])

end CatModule

namespace DerivedCategory

section Comparison

variable [CatModule.HasDerivedCategory.{w'', u} (SingleObj A)] [HasDerivedCategory.{w', u} A]


noncomputable instance : (CatModule.DerivedCategory.singleObjEquivalence A).functor.CommShift ℤ :=
  inferInstanceAs ((CatModule.DerivedCategory.toDGDerivedCategory A).CommShift ℤ)

instance : (CatModule.DerivedCategory.singleObjEquivalence A).functor.IsTriangulated :=
  inferInstanceAs (CatModule.DerivedCategory.toDGDerivedCategory A).IsTriangulated

/-- The image of the dg module `M`, regarded as a dg module over `SingleObj A`, under the
equivalence `D(SingleObj A) ≌ D(A)` is `M`. -/
noncomputable def singleObjEquivalenceObjIso (M : DGModuleCat.{u} A) :
    (CatModule.DerivedCategory.singleObjEquivalence A).functor.obj
      (CatModule.DerivedCategory.Q.obj (DGModuleCat.toCatModuleObj M)) ≅ Q.obj M :=
  (CatModule.DerivedCategory.QhCompToDGDerivedCategoryIso A).app _ ≪≫
    Qh.mapIso ((CatModule.HomotopyCategory.toDGHomotopyCategoryFactors A).app _) ≪≫
    Q.mapIso ((CatModule.singleObjEquivalence A).counitIso.app M)

end Comparison

section Compact

variable [HasDerivedCategory.{w', u} A]

/-- The dg ring `A` is compact in its derived category `D(A)` (for coproducts indexed by types
in the universe `u` of the dg modules): it corresponds, under `D(SingleObj A) ≌ D(A)`, to the
representable module, which is compact (`DG.CatModule.DerivedCategory.isCompact_Q_obj`). -/
theorem isCompact_Q_self : IsCompact.{u} (Q.obj (DGModuleCat.of A A)) := by
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  exact ((CatModule.DerivedCategory.isCompact_Q_obj
    CatModule.isCornerGenerator_toCatModuleObj_self).map_of_equivalence
      (CatModule.DerivedCategory.singleObjEquivalence A)).of_iso (singleObjEquivalenceObjIso _).symm

end Compact

section Generation

variable [HasDerivedCategory.{u, u} A]

/-- The dg ring `A` compactly generates its derived category `D(A)`: it is compact, and an
object `Y` with `Hom(A⟦n⟧, Y) = 0` for all `n` is zero. -/
theorem compactlyGenerates : CompactlyGenerates (fun _ : Unit => Q.obj (DGModuleCat.of A A)) := by
  let := CatModule.HasDerivedCategory.small.{u} (SingleObj A)
  have hG := CatModule.DerivedCategory.compactlyGenerates.{u} (C := SingleObj A)
  have hG' : CompactlyGenerates fun _ : Unit =>
      (CatModule.DerivedCategory.Q.obj (CatModule.representableW.{u} (SingleObj A)
        (SingleObj.star A)) : CatModule.DerivedCategory (SingleObj A)) :=
    { isCompact := fun _ => hG.isCompact _
      isZero_of_forall_eq_zero := fun Y h => hG.isZero_of_forall_eq_zero Y fun _ n φ => h () n φ }
  exact hG'.of_equivalence (CatModule.DerivedCategory.singleObjEquivalence A) _ fun _ =>
    (CatModule.DerivedCategory.singleObjEquivalence A).functor.mapIso
      (CatModule.DerivedCategory.Q.mapIso (CatModule.IsCornerGenerator.isoOfGen
        (CatModule.isCornerGenerator_representableW.{u} (SingleObj.star A))
        CatModule.isCornerGenerator_toCatModuleObj_self)) ≪≫ singleObjEquivalenceObjIso _

/-- The compact objects of `D(A)` are exactly the objects of the thick subcategory generated by
`A` [Keller, *Deriving DG categories*, Thm. 5.3]. -/
theorem thickClosure_self_eq_isCompact :
    ThickClosure (fun Y : DerivedCategory A => ∃ _ : Unit, Q.obj (DGModuleCat.of A A) = Y) =
      IsCompact.{u} :=
  thickClosure_eq_isCompact _ compactlyGenerates

end Generation

end DerivedCategory

variable (A) in
/-- The perfect derived category `D^c(A)` of a dg ring `A`: the full subcategory of compact
objects of `D(A)` (compactness with respect to coproducts indexed by types in the universe `u`
of the dg modules). It is a pretriangulated category, closed under direct summands in `D(A)`. -/
abbrev PerfectDerivedCategory [HasDerivedCategory.{w', u} A] : Type (u + 1) :=
  (compactSubcategory.{u} (DerivedCategory A)).FullSubcategory

end DG
