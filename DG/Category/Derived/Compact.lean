import DG.Category.Derived.Coproducts
import DG.Category.Derived.KProjective
import DG.Compact.Generation

/-!
# The representable modules compactly generate the derived category

Let `C` be a dg category. The images in `D(C)` of the representable dg modules `C(X, -)` are
compact, and an object `Y` of `D(C)` with `Hom(C(X, -)⟦n⟧, Y) = 0` for all objects `X` and all
`n` is zero: the representable modules compactly generate `D(C)` [Keller, *Deriving DG
categories*, §5.2]. Consequently the compact objects of `D(C)` are the thick closure of the
representable modules (`DG.thickClosure_eq_isCompact`).

Both statements reduce to morphisms of dg modules, since the representable modules are
K-projective: a morphism `Q C(X, -)⟦-k⟧ ⟶ Q N` is the image of a morphism of dg modules, which is
determined by a cocycle of `N(X)` of degree `k`, and it vanishes iff that cocycle is a coboundary
(`DG.CatModule.IsCornerGenerator.homotopic_zero_iff`). Morphisms into a coproduct are computed in
the direct sum `⨁ j, N j`, whose cocycles have finitely many nonzero components.

## Main definitions and results

* `DG.CatModule.IsCornerGenerator.homOfCocycle`: the morphism out of a free module on one
  generator sending the generator to a cocycle; `DG.CatModule.IsCornerGenerator.ext_hom`,
  `DG.CatModule.IsCornerGenerator.homotopic_zero_iff`.
* `DG.CatModule.representableW X`: the representable module `C(X, -)`, as a dg module with values
  in `Type (max u v w)`.
* `DG.CatModule.DerivedCategory.isZero_of_forall_representable`: the representables detect zero
  objects of `D(C)`.
* `DG.CatModule.DerivedCategory.isCompact_representable`: the representables are compact in
  `D(C)`.
* `DG.CatModule.DerivedCategory.compactlyGenerates`: the family `X ↦ Q C(X, -)` compactly
  generates `D(C)` (`DG.CompactlyGenerates`).

## Universes

For `C : Type u` with `[Category.{v} C]`, the family of generators is indexed by `C`, and
compactness refers to coproducts indexed by types in the universe of the morphisms of `D(C)`.
The statements are made for dg modules in `Type (max u v w)` and a derived category whose
morphisms are in the same universe, `[HasDerivedCategory.{max u v w, max u v w} C]`.
-/

open CategoryTheory Limits

universe w' w v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-! ### Morphisms out of a free module on one generator -/

namespace IsCornerGenerator

variable {R N : CatModule.{w} C} {X : C} {k : ℤ} {g : R.obj X}
  (hg : IsCornerGenerator R (DGCategory.Idempotent.id X) k g)
include hg

/-- The morphism out of a free module `R` on a generator `g` of degree `k` sending `g` to a
cocycle `y` of degree `k`. -/
noncomputable def homOfCocycle (y : N.obj X) (hy : y ∈ grading k) (hdy : d y = 0) : R ⟶ N :=
  Cocycle.homOf (Cocycle.mk (hg.ofElement (n := 0) y (by rwa [add_zero])) 1 (zero_add 1) (by
    rw [hg.δ_ofElement (zero_add 1) y _ (by rw [hdy]; exact zero_mem _),
      hg.ofElement_congr hdy _ (zero_mem _)]
    exact hg.ofElement_zero))

theorem homOfCocycle_app_gen (y : N.obj X) (hy : y ∈ grading k) (hdy : d y = 0) :
    (hg.homOfCocycle y hy hdy).app X g = y := by
  change (hg.ofElement (n := 0) y (by rwa [add_zero])).app X g = y
  rw [ofElement_gen, DGCategory.Idempotent.id_val, id_smul]

/-- A morphism out of a free module is determined by the image of the generator. -/
theorem ext_hom {f f' : R ⟶ N} (h : f.app X g = f'.app X g) : f = f' :=
  hom_ext fun Y r => congrArg (fun z : Cochain R N 0 => z.app Y r)
    (hg.ext_gen (z := Cochain.ofHom f) (z' := Cochain.ofHom f') h)

/-- A morphism out of a free module on a generator `g` of degree `k` is null-homotopic iff the
image of `g` is a coboundary. -/
theorem homotopic_zero_iff (f : R ⟶ N) :
    Homotopic f 0 ↔ ∃ y ∈ grading (k - 1), d y = f.app X g := by
  constructor
  · intro hf
    obtain ⟨h, hh⟩ := homotopic_zero_iff_exists.mp hf
    have e := congrArg (fun z : Cochain R N 0 => z.app X g) hh
    simp only [Cochain.ofHom_apply, δ_neg_one_apply, hg.d_eq_zero, map_zero, add_zero] at e
    exact ⟨h.app X g, by simpa [sub_eq_add_neg] using h.map_mem hg.mem_grading, e.symm⟩
  · rintro ⟨y, hy, hdy⟩
    have hy' : y ∈ grading (k + -1) := by rwa [← sub_eq_add_neg]
    refine homotopic_zero_iff_exists.mpr ⟨hg.ofElement (n := -1) y hy', ?_⟩
    have hdy' : d y ∈ grading (k + 0) := by
      rw [hdy, add_zero]
      exact f.map_mem hg.mem_grading
    rw [hg.δ_ofElement (neg_add_cancel 1) y hy' hdy', hg.ofHom_eq_ofElement f]
    exact hg.ofElement_congr hdy.symm _ _

end IsCornerGenerator

/-! ### Representable modules -/

variable (C) in
/-- The representable module `C(X, -)`, with values in `Type (max u v w)`. -/
noncomputable abbrev representableW (X : C) : CatModule.{max u v w} C :=
  ulift.{max u w} (representable X)

theorem isCornerGenerator_representableW (X : C) :
    IsCornerGenerator (representableW.{w} C X) (DGCategory.Idempotent.id X) 0 (ULift.up (𝟙 X)) :=
  (isCornerGenerator_representable X).ulift

namespace DerivedCategory

section

variable {R N : CatModule.{w} C} [HasDerivedCategory.{w', w} C]

/-- Every morphism `Q R ⟶ Q N` out of a K-projective module is the image of a morphism of dg
modules. -/
theorem exists_Q_map_eq (hR : IsKProjective R) (φ : Q.obj R ⟶ Q.obj N) :
    ∃ f : R ⟶ N, Q.map f = φ := by
  obtain ⟨f', hf'⟩ := (Qh_map_bijective_of_isKProjective hR _).2 φ
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C).map_surjective f'
  exact ⟨f, hf'⟩

/-- A morphism out of a K-projective module becomes zero in `D(C)` iff it is null-homotopic. -/
theorem Q_map_eq_zero_iff (hR : IsKProjective R) (f : R ⟶ N) : Q.map f = 0 ↔ Homotopic f 0 := by
  rw [← HomotopyCategory.quotient_map_eq_iff, ← Functor.map_zero Q R N]
  exact (Qh_map_bijective_of_isKProjective hR _).1.eq_iff

end

/-! ### Compactness -/

section Compact

variable {R : CatModule.{w} C} {X : C} {k : ℤ} {g : R.obj X}
  (hg : IsCornerGenerator R (DGCategory.Idempotent.id X) k g) [HasDerivedCategory.{w', w} C]

omit [DGCategory C] in
theorem sum_app {M N : CatModule.{w} C} {J : Type*} (s : Finset J) (φ : J → (M ⟶ N)) {Y : C}
    (m : M.obj Y) : (∑ j ∈ s, φ j).app Y m = ∑ j ∈ s, (φ j).app Y m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, add_app, ih, Finset.sum_insert hj]

omit [HasDerivedCategory.{w', w} C] in
/-- Every object of `D(C)` is isomorphic to the image of a dg module. -/
theorem exists_iso_Q_obj [HasDerivedCategory.{w', w} C] (Y : DerivedCategory.{w', w} C) :
    ∃ N : CatModule.{w} C, Nonempty (Y ≅ Q.obj N) := by
  obtain ⟨Z, ⟨e⟩⟩ :=
    (Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso C)).mem_essImage Y
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  exact ⟨N, ⟨e.symm⟩⟩

include hg in
/-- Morphisms from the image in `D(C)` of a free module on one generator into the image of a
direct sum `⨁ j, N j` are finite sums of morphisms into the summands. -/
theorem bijective_directSum {J : Type w} [DecidableEq J] (N : J → CatModule.{w} C) :
    Function.Bijective (DirectSum.toAddMonoid fun j =>
      Preadditive.rightComp (Q.obj R) (Q.map (directSumι.{w, w} N j)) :
        (DirectSum J fun j => (Q.obj R ⟶ Q.obj (N j))) →+ (Q.obj R ⟶ Q.obj (directSum N))) := by
  classical
  have hK := hg.isKProjective
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    choose f hf using fun j => exists_Q_map_eq hK (a j)
    have ha' : Q.map (∑ j ∈ a.support, f j ≫ directSumι N j) = 0 := by
      rw [← ha]
      conv_rhs => rw [← DirectSum.sum_support_of a]
      rw [map_sum, Q.map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [DirectSum.toAddMonoid_of, Q.map_comp, hf]
      rfl
    obtain ⟨y, hy, hdy⟩ := (hg.homotopic_zero_iff _).mp ((Q_map_eq_zero_iff hK _).mp ha')
    ext i
    rw [DirectSum.zero_apply]
    by_cases hi : i ∈ a.support
    · let y' : DirectSum J fun j => (N j).obj X := y
      rw [← hf i, Q_map_eq_zero_iff hK, hg.homotopic_zero_iff]
      refine ⟨y' i, hy i, ?_⟩
      have e := congrArg (fun z : DirectSum J fun j => (N j).obj X => z i) hdy
      simp only [sum_app, comp_app, directSumι_app] at e
      rw [show d (y' i) = (d y') i from (DG.DirectSum.coe_d_apply _ y' i).symm]
      refine e.trans ?_
      rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single i]
      · rw [DirectSum.of_eq_same]
      · intro j _ hji
        exact DirectSum.of_eq_of_ne j i _ (Ne.symm hji)
      · intro h
        exact absurd hi h
    · exact DFinsupp.notMem_support_iff.mp hi
  · intro φ
    obtain ⟨f, rfl⟩ := exists_Q_map_eq hK φ
    let s : DirectSum J fun j => (N j).obj X := f.app X g
    have hs : ∀ j, s j ∈ grading k := f.map_mem hg.mem_grading
    have hds : ∀ j, d (s j) = 0 := fun j => by
      rw [show d (s j) = (d s) j from (DG.DirectSum.coe_d_apply _ s j).symm]
      have h0 : d s = 0 := by
        change d (f.app X g) = 0
        rw [← Hom.map_d, hg.d_eq_zero, map_zero]
      rw [h0, DirectSum.zero_apply]
    refine ⟨∑ j ∈ s.support, DirectSum.of _ j (Q.map (hg.homOfCocycle (s j) (hs j) (hds j))), ?_⟩
    rw [map_sum]
    simp only [DirectSum.toAddMonoid_of, Preadditive.rightComp, AddMonoidHom.mk'_apply,
      ← Q.map_comp, ← Q.map_sum]
    congr 1
    refine hg.ext_hom ?_
    rw [sum_app]
    simp only [comp_app, hg.homOfCocycle_app_gen, directSumι_app]
    exact DirectSum.sum_support_of s

include hg in
/-- The image in `D(C)` of a free module on one generator is compact. -/
theorem isCompact_Q_obj : IsCompact.{w} (Q.obj R) := by
  rw [isCompact_iff_preservesColimitsOfShape]
  intro J
  suffices ∀ Y : J → DerivedCategory.{w', w} C,
      PreservesColimit (Discrete.functor Y) (preadditiveCoyoneda.obj (Opposite.op (Q.obj R))) from
    preservesColimitsOfShape_of_discrete _
  intro Y
  classical
  choose N e using fun j => exists_iso_Q_obj (Y j)
  have hc := isColimitCofanMkObjOfIsColimit Q _ _ (coproductCoconeIsColimit.{w, w} N)
  let E : Q.obj (directSum N) ≅ ∐ fun j => Q.obj (N j) :=
    hc.coconePointUniqueUpToIso (colimit.isColimit _)
  have hE : ∀ j, Q.map (directSumι N j) ≫ E.hom = Sigma.ι (fun j => Q.obj (N j)) j := fun j =>
    hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨j⟩
  have hb : Function.Bijective (coproductComparison (Q.obj R) fun j => Q.obj (N j)) := by
    have h := (bijective_directSum hg N)
    have key : coproductComparison (Q.obj R) (fun j => Q.obj (N j)) =
        (Preadditive.rightComp (Q.obj R) E.hom).comp (DirectSum.toAddMonoid fun j =>
          Preadditive.rightComp (Q.obj R) (Q.map (directSumι N j))) := by
      ext j a
      simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of, Preadditive.rightComp,
        AddMonoidHom.mk'_apply, coproductComparison_of, Category.assoc, hE]
    rw [key, AddMonoidHom.coe_comp]
    refine Function.Bijective.comp ?_ h
    exact Function.bijective_iff_has_inverse.mpr
      ⟨fun a => a ≫ E.inv, fun a => by simp [Preadditive.rightComp],
        fun a => by simp [Preadditive.rightComp]⟩
  have := preservesColimit_of_bijective (Q.obj R) (fun j => Q.obj (N j)) hb
  exact preservesColimit_of_iso_diagram _
    (Discrete.natIso fun j => (e j.as).some.symm :
      Discrete.functor (fun j => Q.obj (N j)) ≅ Discrete.functor Y)

end Compact

section Generation

variable [HasDerivedCategory.{max u v w, max u v w} C]

/-- The representable modules detect zero objects of `D(C)`: if every morphism
`Q C(X, -)⟦n⟧ ⟶ Y` vanishes, then `Y` is zero. -/
theorem isZero_of_forall_representable (Y : DerivedCategory.{max u v w, max u v w} C)
    (h : ∀ (X : C) (n : ℤ) (φ : (Q.obj (representableW.{w} C X))⟦n⟧ ⟶ Y), φ = 0) :
    IsZero Y := by
  obtain ⟨N, -, ⟨e⟩⟩ := exists_isKProjective_iso.{max u v w, w} Y
  refine IsZero.of_iso ?_ e
  rw [isZero_Q_obj_iff]
  intro X
  refine DG.isAcyclic_iff.mpr fun k y hy hdy => ?_
  have hg := (isCornerGenerator_representableW.{w} X).shift (-k)
  have hy' : y ∈ grading (0 - -k) := by rwa [zero_sub, neg_neg]
  let f := hg.homOfCocycle y hy' hdy
  have hf : Q.map f = 0 := by
    have h0 := h X (-k) (((Q.commShiftIso (-k)).app _).inv ≫ Q.map f ≫ e.inv)
    rwa [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero] at h0
  obtain ⟨z, hz, hdz⟩ := (hg.homotopic_zero_iff f).mp
    ((Q_map_eq_zero_iff (hg.isKProjective) f).mp hf)
  rw [hg.homOfCocycle_app_gen] at hdz
  exact ⟨z, by rwa [zero_sub, neg_neg] at hz, hdz⟩

/-- The representable modules compactly generate the derived category of a dg category
[Keller, *Deriving DG categories*, §5.2]. -/
theorem compactlyGenerates :
    CompactlyGenerates (fun X : C =>
      (Q.obj (representableW.{w} C X) : DerivedCategory.{max u v w, max u v w} C)) where
  isCompact X := isCompact_Q_obj (isCornerGenerator_representableW.{w} X)
  isZero_of_forall_eq_zero Y h := isZero_of_forall_representable Y h

/-- The compact objects of `D(C)` are the objects of the thick closure of the representable
modules (the perfect dg modules). -/
theorem thickClosure_representable_eq_isCompact :
    ThickClosure (fun Y : DerivedCategory.{max u v w, max u v w} C =>
      ∃ X : C, Q.obj (representableW.{w} C X) = Y) = IsCompact.{max u v w} :=
  thickClosure_eq_isCompact _ compactlyGenerates

end Generation

end DerivedCategory

end CatModule

end DG
