import DG.HalfGraded.DiagonalCompactK0
import DG.HalfGraded.DiagonalEssentialImage
import DG.Bigraded.Derived

/-!
# Block decomposition over the diagonal weight category

Let `A` be a dg ring and `C = C_H` the weight dg category of the diagonal half-graded dg ring
`H = HalfGradedDGRing.ofDGRing A` (parameter `2`). There are no nonzero morphisms of `C` between
weights in different residue classes modulo `4`, and the weight-zero block is the diagonal
image of `A`. Consequently every dg module `M` over `C` is the direct sum of its four blocks:

`M ≅ ⨁_{r = 0}^{3} (diag (rec₀ (M⟨r⟩)))⟨-r⟩`,

where `M⟨r⟩` is the internal shift (restriction along `k ↦ k + r`), `rec₀` is weight-zero
recovery and `diag` is the diagonal module functor. The `r`-th summand maps to `M` by the
adjunction counit, which is bijective at the weights `≡ r (mod 4)`, while the other summands
vanish there (`blocksMap`, an isomorphism of dg modules).

On derived categories this gives, for every object `X` of `D(C)`,

`X ≅ ⨁_{r = 0}^{3} (ι (R₀ (X⟨r⟩)))⟨-r⟩`

with `ι = toDerived A` and `R₀ = recoveryDerived A 0` (`blocksDerivedIso`). Since `ι` is fully
faithful and preserves coproducts, it reflects compact objects; hence `R₀` preserves compact
objects (`isCompact_recoveryDerived`) and each summand of a compact object is compact.

## Main results

* `DG.Diagonal.blocksMap`, `DG.Diagonal.isIso_blocksMap`: the module-level block decomposition.
* `DG.Diagonal.blocksDerivedIso`: the derived block decomposition of every object.
* `DG.IsCompact.of_map_of_fullyFaithful`: a fully faithful additive functor preserving
  coproducts reflects compact objects.
* `DG.Diagonal.isCompact_recoveryDerived`, `DG.Diagonal.isCompact_blockDerived`.
-/

open CategoryTheory Limits

universe w' w v u

namespace DG

section Reflect

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]

/-- A fully faithful additive functor preserving coproducts indexed by `Type w` reflects compact
objects: `Hom(X, ∐ Y) ≅ Hom(F X, F (∐ Y)) ≅ Hom(F X, ∐ F Y)`. -/
theorem IsCompact.of_map_of_fullyFaithful {F : C ⥤ D} (hF : F.FullyFaithful) [F.Additive]
    [∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) F] {X : C}
    (hX : IsCompact.{w} (F.obj X)) : IsCompact.{w} X := by
  intro ι _ Y _
  have hc := isColimitCofanMkObjOfIsColimit F _ _ (coproductIsCoproduct Y)
  have : HasCoproduct fun i => F.obj (Y i) := ⟨⟨_, hc⟩⟩
  let E := hc.coconePointUniqueUpToIso (colimit.isColimit _)
  have hE : ∀ i, F.map (Sigma.ι Y i) ≫ E.hom = Sigma.ι (fun i => F.obj (Y i)) i := fun i =>
    hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨i⟩
  let eF : ∀ i, (X ⟶ Y i) ≃+ (F.obj X ⟶ F.obj (Y i)) := fun i =>
    AddEquiv.mk' hF.homEquiv (fun f g => by simp)
  let e : (DirectSum ι fun i => (X ⟶ Y i)) ≃+ DirectSum ι fun i => (F.obj X ⟶ F.obj (Y i)) :=
    DFinsupp.mapRange.addEquiv eF
  have key : ∀ a, F.map (coproductComparison X Y a) ≫ E.hom =
      coproductComparison (F.obj X) (fun i => F.obj (Y i)) (e a) := by
    intro a
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i f =>
      have he : e (DirectSum.of _ i f) = DirectSum.of _ i (F.map f) := by
        change DFinsupp.mapRange (fun i => eF i) (fun i => map_zero _)
          (DFinsupp.single i f) = DFinsupp.single i _
        rw [DFinsupp.mapRange_single]
        rfl
      rw [he, coproductComparison_of, coproductComparison_of, F.map_comp, Category.assoc, hE]
    | add a b ha hb => rw [map_add, F.map_add, Preadditive.add_comp, ha, hb, map_add, map_add]
  have hk : ⇑(coproductComparison X Y) = hF.homEquiv.symm ∘ (fun a => a ≫ E.inv) ∘
      coproductComparison (F.obj X) (fun i => F.obj (Y i)) ∘ e := by
    funext a
    simp only [Function.comp_apply, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (hF.homEquiv.symm_apply_apply _).symm
  have hE' : Function.Bijective fun a : F.obj X ⟶ ∐ fun i => F.obj (Y i) => a ≫ E.inv :=
    Function.bijective_iff_has_inverse.mpr ⟨fun a => a ≫ E.hom, fun a => by simp, fun a => by simp⟩
  rw [hk]
  exact hF.homEquiv.symm.bijective.comp (hE'.comp ((hX ι _).comp e.bijective))

end Reflect

namespace Diagonal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-! ### Binary sums of module maps -/

section SumMap

variable {C : Type*} [Category C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- The map `prod X Y ⟶ M`, `(x, y) ↦ f x + g y`. -/
def sumMap {X Y M : CatModule.{v} C} (f : X ⟶ M) (g : Y ⟶ M) : CatModule.prod X Y ⟶ M :=
  CatModule.fst X Y ≫ f + CatModule.snd X Y ≫ g

theorem sumMap_app {X Y M : CatModule.{v} C} (f : X ⟶ M) (g : Y ⟶ M) (Z : C)
    (m : (CatModule.prod X Y).obj Z) : (sumMap f g).app Z m = f.app Z m.1 + g.app Z m.2 := rfl

instance prod_subsingleton {X Y : CatModule.{v} C} (Z : C) [Subsingleton (X.obj Z)]
    [Subsingleton (Y.obj Z)] : Subsingleton ((CatModule.prod X Y).obj Z) :=
  inferInstanceAs (Subsingleton (X.obj Z × Y.obj Z))

theorem sumMap_app_bijective_left {X Y M : CatModule.{v} C} (f : X ⟶ M) (g : Y ⟶ M) (Z : C)
    (hf : Function.Bijective (f.app Z)) [Subsingleton (Y.obj Z)] :
    Function.Bijective ((sumMap f g).app Z) := by
  have hg : ∀ y, g.app Z y = 0 := fun y => by rw [Subsingleton.elim y 0, map_zero]
  refine ⟨fun m m' h => ?_, fun n => ?_⟩
  · rw [sumMap_app, sumMap_app, hg, hg, add_zero, add_zero] at h
    exact Prod.ext (hf.1 h) (Subsingleton.elim _ _)
  · obtain ⟨x, rfl⟩ := hf.2 n
    exact ⟨((x, 0) : X.obj Z × Y.obj Z), by rw [sumMap_app, hg, add_zero]⟩

theorem sumMap_app_bijective_right {X Y M : CatModule.{v} C} (f : X ⟶ M) (g : Y ⟶ M) (Z : C)
    [Subsingleton (X.obj Z)] (hg : Function.Bijective (g.app Z)) :
    Function.Bijective ((sumMap f g).app Z) := by
  have hf : ∀ x, f.app Z x = 0 := fun x => by rw [Subsingleton.elim x 0, map_zero]
  refine ⟨fun m m' h => ?_, fun n => ?_⟩
  · rw [sumMap_app, sumMap_app, hf, hf, zero_add, zero_add] at h
    exact Prod.ext (Subsingleton.elim _ _) (hg.1 h)
  · obtain ⟨y, rfl⟩ := hg.2 n
    exact ⟨((0, y) : X.obj Z × Y.obj Z), by rw [sumMap_app, hf, zero_add]⟩

/-- `prod X Y ≅ X ⊞ Y`. -/
def prodIsoBiprod (X Y : CatModule.{v} C) : CatModule.prod X Y ≅ X ⊞ Y :=
  (limit.isoLimitCone (CatModule.binaryProductLimitCone X Y)).symm ≪≫ (biprod.isoProd X Y).symm

end SumMap

/-! ### Blocks of modules over the diagonal weight category -/

/-- The internal shift of modules over the diagonal weight category, `M⟨s⟩⟨k⟩ = M⟨k + s⟩`:
restriction along `k ↦ k + s`. -/
abbrev shiftModule (s : ℤ) :
    CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤
      CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  CatModule.precomp (WeightCategory.shiftFunctor _ s)

/-- `(k ↦ k - r) ⋙ (k ↦ k + r) ≅ 𝟭`, by `1`. -/
def shiftFunctorNegCompIso (r : ℤ) :
    WeightCategory.shiftFunctor (HalfGradedDGRing.ofDGRing A).Regraded (-r) ⋙
      WeightCategory.shiftFunctor _ r ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => WeightCategory.isoOfEq (by simp)) (fun f => Subtype.ext (by simp))

/-- `M⟨r⟩⟨-r⟩ ≅ M`, by the action of `1`. -/
def shiftModuleCancelIso (r : ℤ)
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (shiftModule A (-r)).obj ((shiftModule A r).obj M) ≅ M :=
  (CatModule.precompCompIso _ _).symm.app M ≪≫
    (CatModule.precompNatIso (shiftFunctorNegCompIso A r)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)).app M ≪≫
    (CatModule.precompIdIso _).app M

/-- The block of `M` in the residue class of `r` modulo `4`:
`(diag (rec₀ (M⟨r⟩)))⟨-r⟩`. -/
def block (r : ℤ) (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  (shiftModule A (-r)).obj ((toCatModule A).obj ((recover A 0).obj ((shiftModule A r).obj M)))

/-- The inclusion of a block, given by the adjunction counit. -/
def blockι (r : ℤ) (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    block A r M ⟶ M :=
  (shiftModule A (-r)).map (counitMap A ((shiftModule A r).obj M)) ≫
    (shiftModuleCancelIso A r M).hom

theorem block_subsingleton (r w : ℤ) (h : ¬ ∃ t : ℤ, w + -r = 4 * t)
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    Subsingleton ((block A r M).obj ⟨w⟩) :=
  value_subsingleton A _ (w + -r) h

theorem blockι_app_bijective (r w t : ℤ) (h : w + -r = 4 * t)
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    Function.Bijective ((blockι A r M).app ⟨w⟩) := by
  have he := (CatModule.isIso_iff_bijective (shiftModuleCancelIso A r M).hom).mp inferInstance ⟨w⟩
  have hc : ∀ j, j = 4 * t → Function.Bijective
      (counitApp A ((shiftModule A r).obj M) j) := by
    rintro _ rfl
    exact counitApp_supported_bijective A _ t
  exact he.comp (hc (w + -r) h)

/-- The four blocks of `M`. -/
def blocks (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  CatModule.prod (block A 0 M)
    (CatModule.prod (block A 1 M) (CatModule.prod (block A 2 M) (block A 3 M)))

/-- The sum of the four block inclusions. -/
def blocksMap (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    blocks A M ⟶ M :=
  sumMap (blockι A 0 M) (sumMap (blockι A 1 M) (sumMap (blockι A 2 M) (blockι A 3 M)))

/-- Every dg module over the diagonal weight category is the direct sum of its four blocks. -/
instance isIso_blocksMap
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    IsIso (blocksMap A M) := by
  rw [CatModule.isIso_iff_bijective]
  rintro ⟨w⟩
  have hs : ∀ r : ℤ, (∀ t : ℤ, w + -r ≠ 4 * t) → Subsingleton ((block A r M).obj ⟨w⟩) :=
    fun r h => block_subsingleton A r w (fun ⟨t, ht⟩ => h t ht) M
  have h4 : w % 4 = 0 ∨ w % 4 = 1 ∨ w % 4 = 2 ∨ w % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · have := hs 1 (by omega); have := hs 2 (by omega); have := hs 3 (by omega)
    exact sumMap_app_bijective_left _ _ _ (blockι_app_bijective A 0 w (w / 4) (by omega) M)
  · have := hs 0 (by omega); have := hs 2 (by omega); have := hs 3 (by omega)
    refine sumMap_app_bijective_right _ _ _ (sumMap_app_bijective_left _ _ _
      (blockι_app_bijective A 1 w (w / 4) (by omega) M))
  · have := hs 0 (by omega); have := hs 1 (by omega); have := hs 3 (by omega)
    refine sumMap_app_bijective_right _ _ _ (sumMap_app_bijective_right _ _ _
      (sumMap_app_bijective_left _ _ _ (blockι_app_bijective A 2 w (w / 4) (by omega) M)))
  · have := hs 0 (by omega); have := hs 1 (by omega); have := hs 2 (by omega)
    refine sumMap_app_bijective_right _ _ _ (sumMap_app_bijective_right _ _ _
      (sumMap_app_bijective_right _ _ _ (blockι_app_bijective A 3 w ((w - 3) / 4) (by omega) M)))

/-! ### The derived block decomposition -/

variable [HasDerivedCategory.{w, v} A]
  [CatModule.HasDerivedCategory.{w', v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The internal shift `⟨s⟩` on the derived category of the diagonal weight category. -/
abbrev shiftDerived (s : ℤ) :
    CatModule.DerivedCategory.{w', v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤
      CatModule.DerivedCategory.{w', v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  CatModule.DerivedCategory.internalShift (HalfGradedDGRing.ofDGRing A).Regraded s

/-- The derived block functor `X ↦ (ι (R₀ (X⟨r⟩)))⟨-r⟩`. -/
def blockDerived (r : ℤ) :
    CatModule.DerivedCategory.{w', v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤
      CatModule.DerivedCategory.{w', v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  shiftDerived A r ⋙ recoveryDerived.{w', w} A 0 ⋙ toDerived A ⋙ shiftDerived A (-r)

/-- The derived image of a module block is the derived block of its localization. -/
def QBlockIso (r : ℤ)
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    CatModule.DerivedCategory.Q.obj (block A r M) ≅
      (blockDerived.{w', w} A r).obj (CatModule.DerivedCategory.Q.obj M) :=
  ((CatModule.DerivedCategory.QCompRestrictIso _).app _).symm ≪≫
    (shiftDerived A (-r)).mapIso ((toDerivedObjIso A _).symm ≪≫
      (toDerived A).mapIso ((recoveryDerivedObjIso A 0 _).symm ≪≫
        (recoveryDerived A 0).mapIso ((CatModule.DerivedCategory.QCompRestrictIso _).app M).symm))

/-- `Q (prod X Y) ≅ Q X ⊞ Q Y`. -/
def QProdIso (X Y : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (CatModule.DerivedCategory.Q.{w'}).obj (CatModule.prod X Y) ≅
      CatModule.DerivedCategory.Q.obj X ⊞ CatModule.DerivedCategory.Q.obj Y :=
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (CatModule.DerivedCategory.Q.{w'} (C := WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))
  CatModule.DerivedCategory.Q.mapIso (prodIsoBiprod X Y) ≪≫
    CatModule.DerivedCategory.Q.mapBiprod X Y

/-- The derived block decomposition of a localized module. -/
def QBlocksIso (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (CatModule.DerivedCategory.Q.{w'}).obj M ≅
      (blockDerived.{w', w} A 0).obj (CatModule.DerivedCategory.Q.obj M) ⊞
        ((blockDerived.{w', w} A 1).obj (CatModule.DerivedCategory.Q.obj M) ⊞
          ((blockDerived.{w', w} A 2).obj (CatModule.DerivedCategory.Q.obj M) ⊞
            (blockDerived.{w', w} A 3).obj (CatModule.DerivedCategory.Q.obj M))) :=
  CatModule.DerivedCategory.Q.mapIso (asIso (blocksMap A M)).symm ≪≫ QProdIso A _ _ ≪≫
    biprod.mapIso (QBlockIso A 0 M) (QProdIso A _ _ ≪≫
      biprod.mapIso (QBlockIso A 1 M) (QProdIso A _ _ ≪≫
        biprod.mapIso (QBlockIso A 2 M) (QBlockIso A 3 M)))

/-- Every object of the derived category of the diagonal weight category is the direct sum of
its four derived blocks: `X ≅ ⨁_{r=0}^{3} (ι (R₀ (X⟨r⟩)))⟨-r⟩`. -/
def blocksDerivedIso
    (X : CatModule.DerivedCategory.{w', v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    X ≅ (blockDerived.{w', w} A 0).obj X ⊞ ((blockDerived.{w', w} A 1).obj X ⊞
      ((blockDerived.{w', w} A 2).obj X ⊞ (blockDerived.{w', w} A 3).obj X)) :=
  let M := (CatModule.DerivedCategory.exists_iso_Q_obj X).choose
  let e : X ≅ CatModule.DerivedCategory.Q.obj M :=
    (CatModule.DerivedCategory.exists_iso_Q_obj X).choose_spec.some
  e ≪≫ QBlocksIso.{w', w} A M ≪≫ (biprod.mapIso ((blockDerived A 0).mapIso e.symm)
    (biprod.mapIso ((blockDerived A 1).mapIso e.symm) (biprod.mapIso
      ((blockDerived A 2).mapIso e.symm) ((blockDerived A 3).mapIso e.symm))))

/-- The diagonal derived functor preserves coproducts (it is a left adjoint). -/
instance toDerived_preservesColimitsOfShape (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (toDerived.{w', w, v} A) :=
  have := (diagonalDerivedAdjunction.{w', w, v} A).leftAdjoint_preservesColimits
  inferInstance

/-- The diagonal derived functor reflects compact objects. -/
theorem isCompact_of_isCompact_toDerived {Y : DerivedCategory.{w, v} A}
    (h : IsCompact.{v} ((toDerived.{w', w, v} A).obj Y)) : IsCompact.{v} Y :=
  IsCompact.of_map_of_fullyFaithful (toDerivedFullyFaithful A) h

/-- The derived blocks of a compact object are compact. -/
theorem isCompact_blockDerived
    {X : CatModule.DerivedCategory.{w', v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (hX : IsCompact.{v} X) :
    IsCompact.{v} ((blockDerived.{w', w} A 0).obj X) ∧
      IsCompact.{v} ((blockDerived.{w', w} A 1).obj X) ∧
      IsCompact.{v} ((blockDerived.{w', w} A 2).obj X) ∧
      IsCompact.{v} ((blockDerived.{w', w} A 3).obj X) := by
  have h := hX.of_iso (blocksDerivedIso.{w', w} A X).symm
  exact ⟨h.of_biprod_left, h.of_biprod_right.of_biprod_left,
    h.of_biprod_right.of_biprod_right.of_biprod_left,
    h.of_biprod_right.of_biprod_right.of_biprod_right⟩

/-- Weight-zero derived recovery preserves compact objects. -/
theorem isCompact_recoveryDerived
    {X : CatModule.DerivedCategory.{w', v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (hX : IsCompact.{v} X) : IsCompact.{v} ((recoveryDerived.{w', w} A 0).obj X) := by
  have h := (isCompact_blockDerived.{w', w} A hX).1
  rw [blockDerived, Functor.comp_obj, Functor.comp_obj, Functor.comp_obj,
    CatModule.DerivedCategory.isCompact_internalShift_obj_iff] at h
  exact (isCompact_of_isCompact_toDerived A h).of_iso
    ((recoveryDerived A 0).mapIso
      ((CatModule.DerivedCategory.internalShiftZeroIso _).app X)).symm

end

end Diagonal

end DG
