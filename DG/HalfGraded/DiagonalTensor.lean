import DG.HalfGraded.DiagonalBimoduleHom
import DG.HalfGraded.DiagonalTransport
import DG.HalfGraded.DiagonalInduction
import DG.Category.Derived.Tensor
import DG.Category.Derived.RestrictionIso

/-!
# The derived tensor product with the diagonally regraded bimodule

Let `A`, `B` be dg rings, `M` a dg `(A, B)`-bimodule which is K-projective as a left dg
`A`-module, `Mᵈ = DG.Diagonal.bimodule A B M` its diagonal regrading over the weight dg categories
`C_A`, `C_B` of the diagonal half-graded dg rings, and `G = M ⊗^L_B - : D(B) ⥤ D(A)`
(`DG.DGBimodule.derivedTensor`). This file identifies the derived tensor product
`Mᵈ ⊗^L_{C_B} - : D(C_B) ⥤ D(C_A)` (`DG.Diagonal.derivedTensor`) with the diagonal transport
`Gᵈ = DG.Diagonal.transport B A G` of `G`:

* `DG.Diagonal.rhomRestrictIso`: for every weight `r`, `RHOM_{C_A}(Mᵈ, -)` followed by restriction
  to the weight `r` is `RHOM_A(M, -)` after restriction to the weight `r`, from the isomorphism of
  Hom modules `DG.Diagonal.homFunctorRestrictIso`;
* `DG.Diagonal.inductionDerivedTensorIso`: hence, for the left adjoints, derived induction along the
  weight-`r` inclusion `ι_r` followed by `Mᵈ ⊗^L -` is `M ⊗^L -` followed by derived induction;
* `DG.Diagonal.toDerivedShiftIso`: the diagonal functor `ι` followed by the internal shift `⟨-r⟩` is
  derived induction along `ι_r` (both are left adjoint to restriction to the weight `r`);
* `DG.Diagonal.blockDerivedTensorIso`: on each block `(ι (R₀ (X⟨r⟩)))⟨-r⟩`,
  `Mᵈ ⊗^L -` acts by `G`;
* `DG.Diagonal.blocksNatIso`: the block decomposition `X ≅ ∏_{r<4} (ι (R₀ (X⟨r⟩)))⟨-r⟩` of
  `DG.Diagonal.blocksDerivedIso`, as a natural isomorphism;
* `DG.Diagonal.derivedTensorTransportIso`: **`Mᵈ ⊗^L_{C_B} - ≅ Gᵈ`**, a natural isomorphism;
  consequently the maps induced by `Mᵈ ⊗^L -` on `K₀` and on super `K₀` are `id ⊗ K₀(G)`
  (`DG.Diagonal.K0LinearEquiv_derivedTensor`, `DG.Diagonal.superK0LinearEquiv_derivedTensor`).
-/

open CategoryTheory Limits

universe v

noncomputable section

namespace DG.Diagonal

set_option backward.isDefEq.respectTransparency false

/-! ### The diagonal functor followed by an internal shift is derived induction -/

section Induction

variable (A : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{v, v} A]
  [CatModule.HasDerivedCategory.{v, v} (SingleObj A)]
  [CatModule.HasDerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- Restriction to the weight `r`: `⟨r⟩` followed by weight-zero recovery is restriction along
`ι_r`, followed by `D(SingleObj A) ≌ D(A)`. -/
def shiftRecoveryIso (r : ℤ) :
    shiftDerived.{v, v} A r ⋙ recoveryDerived.{v, v} A 0 ≅
      CatModule.DerivedCategory.restrict (inclusion A r) ⋙
        (CatModule.DerivedCategory.singleObjEquivalence A).functor :=
  Functor.isoWhiskerLeft _ (recoveryDerivedIso A) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (CatModule.DerivedCategory.restrictCompIso (scalarInclusion A 0)
        (WeightCategory.shiftFunctor _ r)).symm _

/-- `ι ⋙ ⟨-r⟩ ⊣ ⟨r⟩ ⋙ R₀`. -/
def toDerivedShiftAdjunction (r : ℤ) :
    toDerived.{v, v, v} A ⋙ shiftDerived.{v, v} A (-r) ⊣
      shiftDerived.{v, v} A r ⋙ recoveryDerived.{v, v} A 0 :=
  (diagonalDerivedAdjunction.{v, v, v} A).comp
    (CatModule.DerivedCategory.internalShiftEquiv _ r).symm.toAdjunction

/-- **The diagonal functor followed by `⟨-r⟩` is derived induction along `ι_r`**, after
`D(SingleObj A) ≌ D(A)`: both are left adjoint to restriction to the weight `r`. -/
def toDerivedShiftIso (r : ℤ) :
    toDerived.{v, v, v} A ⋙ shiftDerived.{v, v} A (-r) ≅
      (CatModule.DerivedCategory.singleObjEquivalence A).inverse ⋙
        CatModule.DerivedCategory.induction (inclusion A r) :=
  (toDerivedShiftAdjunction A r).leftAdjointUniq
    (((CatModule.DerivedCategory.singleObjEquivalence A).symm.toAdjunction.comp
      (CatModule.DerivedCategory.inductionAdjunction (inclusion A r))).ofNatIsoRight
        (shiftRecoveryIso A r).symm)

end Induction

/-! ### The natural block decomposition -/

section BlocksModule

variable (A : Type v) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The block functor on modules, `M ↦ (diag (rec₀ (M⟨r⟩)))⟨-r⟩` (`DG.Diagonal.block`). -/
abbrev blockFunctor (r : ℤ) :
    CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤
      CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  shiftModule A r ⋙ recover A 0 ⋙ toCatModule A ⋙ shiftModule A (-r)

/-- `M⟨r⟩⟨-r⟩ ≅ M`, naturally in `M`. -/
def shiftModuleCancelNatIso (r : ℤ) : shiftModule A r ⋙ shiftModule A (-r) ≅ 𝟭 _ :=
  (CatModule.precompCompIso _ _).symm ≪≫
    CatModule.precompNatIso (shiftFunctorNegCompIso A r)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.mem_grading_zero_of_val_eq_one _ rfl)
      (fun _ => WeightCategory.d_eq_zero_of_val_eq_one _ rfl) ≪≫
    CatModule.precompIdIso _

/-- The block inclusions `blockι`, as a natural transformation. -/
def blockιNat (r : ℤ) : blockFunctor A r ⟶ 𝟭 _ :=
  Functor.whiskerLeft (shiftModule A r)
      (Functor.whiskerLeft (recover A 0 ⋙ toCatModule A) (𝟙 (shiftModule A (-r))) ≫
        Functor.whiskerRight (diagonalCounit A) (shiftModule A (-r))) ≫
    (shiftModuleCancelNatIso A r).hom

theorem blockιNat_app (r : ℤ)
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (blockιNat A r).app M = blockι A r M := by
  apply CatModule.hom_ext
  intro X x
  rfl

/-- The projection of `blocks A M` onto its block of index `r < 4`. -/
def projBlock (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (r : Fin 4) → (blocks A M ⟶ block A (r : ℤ) M)
  | 0 => CatModule.fst _ _
  | 1 => CatModule.snd _ _ ≫ CatModule.fst _ _
  | 2 => CatModule.snd _ _ ≫ CatModule.snd _ _ ≫ CatModule.fst _ _
  | 3 => CatModule.snd _ _ ≫ CatModule.snd _ _ ≫ CatModule.snd _ _

/-- The inclusion of the block of index `r < 4` into `blocks A M`. -/
def injBlock (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (r : Fin 4) → (block A (r : ℤ) M ⟶ blocks A M)
  | 0 => CatModule.lift (𝟙 _) 0
  | 1 => CatModule.lift 0 (CatModule.lift (𝟙 _) 0)
  | 2 => CatModule.lift 0 (CatModule.lift 0 (CatModule.lift (𝟙 _) 0))
  | 3 => CatModule.lift 0 (CatModule.lift 0 (CatModule.lift 0 (𝟙 _)))

theorem sum_projBlock_blockι
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    ∑ r : Fin 4, projBlock A M r ≫ blockι A (r : ℤ) M = blocksMap A M := by
  rw [Fin.sum_univ_four]
  simp only [blocksMap, sumMap, Preadditive.comp_add, add_assoc]
  rfl

omit [DGRing A] in
private theorem lift_fst' {C : Type*} [Category C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] {P M N : CatModule.{v} C} (φ : P ⟶ M) (ψ : P ⟶ N) :
    CatModule.lift φ ψ ≫ CatModule.fst M N = φ :=
  CatModule.hom_ext fun _ _ => rfl

omit [DGRing A] in
private theorem lift_snd' {C : Type*} [Category C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] {P M N : CatModule.{v} C} (φ : P ⟶ M) (ψ : P ⟶ N) :
    CatModule.lift φ ψ ≫ CatModule.snd M N = ψ :=
  CatModule.hom_ext fun _ _ => rfl

theorem injBlock_blocksMap
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (r : Fin 4) :
    injBlock A M r ≫ blocksMap A M = blockι A (r : ℤ) M := by
  fin_cases r <;>
    simp only [injBlock, blocksMap, sumMap, Preadditive.comp_add, ← Category.assoc, lift_fst',
      lift_snd', zero_comp, add_zero, zero_add] <;> rfl

theorem injBlock_projBlock_self
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (r : Fin 4) :
    injBlock A M r ≫ projBlock A M r = 𝟙 _ := by
  apply CatModule.hom_ext
  intro X x
  fin_cases r <;> rfl

theorem injBlock_projBlock_of_ne
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) {r s : Fin 4}
    (h : r ≠ s) : injBlock A M r ≫ projBlock A M s = 0 := by
  apply CatModule.hom_ext
  intro X x
  fin_cases r <;> fin_cases s <;>
    first
    | exact absurd rfl h
    | rfl

theorem sum_projBlock_blockιNat
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    ∑ r : Fin 4, projBlock A M r ≫ (blockιNat A (r : ℤ)).app M = blocksMap A M :=
  sum_projBlock_blockι A M

/-- The block decomposition `blocks A M ≅ M` of `DG.Diagonal.isIso_blocksMap`. -/
def blocksMapIso (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    blocks A M ≅ M :=
  @asIso _ _ _ _ (blocksMap A M) (isIso_blocksMap A M)

theorem blockιNat_blocksMapIso_inv
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (r : Fin 4) :
    (blockιNat A (r : ℤ)).app M ≫ (blocksMapIso A M).inv = injBlock A M r := by
  rw [blockιNat_app, Iso.comp_inv_eq]
  exact (injBlock_blocksMap A M r).symm

theorem blockιNat_inv_projBlock_self
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) (r : Fin 4) :
    (blockιNat A (r : ℤ)).app M ≫ (blocksMapIso A M).inv ≫ projBlock A M r = 𝟙 _ := by
  rw [← Category.assoc, blockιNat_blocksMapIso_inv, injBlock_projBlock_self]
  rfl

theorem blockιNat_inv_projBlock_of_ne
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) {r s : Fin 4}
    (h : r ≠ s) :
    (blockιNat A (r : ℤ)).app M ≫ (blocksMapIso A M).inv ≫ projBlock A M s = 0 := by
  rw [← Category.assoc, blockιNat_blocksMapIso_inv, injBlock_projBlock_of_ne A M h]

end BlocksModule

section Blocks

variable (A : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{v, v} A]
  [CatModule.HasDerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- The block functor on derived categories is induced by the block functor on modules. -/
def QBlockNatIso (r : ℤ) :
    CatModule.DerivedCategory.Q ⋙ blockDerived.{v, v} A r ≅
      blockFunctor A r ⋙ CatModule.DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CatModule.DerivedCategory.QCompRestrictIso _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (QCompRecoveryDerivedIso A 0) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (QCompToDerivedIso A) _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (CatModule.DerivedCategory.QCompRestrictIso _)))

/-- The derived block inclusion `(ι (R₀ (X⟨r⟩)))⟨-r⟩ ⟶ X`, induced by `blockι`. -/
def blockDerivedι (r : ℤ) : blockDerived.{v, v} A r ⟶ 𝟭 _ :=
  (Localization.whiskeringLeftFunctor' CatModule.DerivedCategory.Q
    (CatModule.quasiIso (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) _).preimage
    ((QBlockNatIso A r).hom ≫ Functor.whiskerRight (blockιNat A r) _ ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)

theorem blockDerivedι_app_Q (r : ℤ)
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (blockDerivedι A r).app (CatModule.DerivedCategory.Q.obj M) =
      (QBlockNatIso A r).hom.app M ≫ CatModule.DerivedCategory.Q.map ((blockιNat A r).app M) := by
  have h := NatTrans.congr_app ((Localization.whiskeringLeftFunctor' CatModule.DerivedCategory.Q
    (CatModule.quasiIso (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) _).map_preimage
    ((QBlockNatIso A r).hom ≫ Functor.whiskerRight (blockιNat A r) _ ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)) M
  refine h.trans ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Category.comp_id]
  erw [Category.comp_id]

/-- The sum of the derived block inclusions, `∏_{r<4} (ι (R₀ (X⟨r⟩)))⟨-r⟩ ⟶ X`. -/
def blocksDerivedι : piFunctor (fun r : Fin 4 => blockDerived.{v, v} A (r : ℤ)) ⟶ 𝟭 _ where
  app X := ∑ r : Fin 4, Pi.π _ r ≫ (blockDerivedι A (r : ℤ)).app X
  naturality X Y f := by
    rw [Preadditive.comp_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Category.assoc, piFunctor_map_π, Category.assoc, (blockDerivedι A (r : ℤ)).naturality,
      Category.assoc]

theorem isIso_blocksDerivedι_app_Q
    (M : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    IsIso ((blocksDerivedι A).app (CatModule.DerivedCategory.Q.obj M)) := by
  let Q := CatModule.DerivedCategory.Q (C := WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)
  let φ : Q.obj M ⟶ ∏ᶜ fun r : Fin 4 => (blockDerived.{v, v} A (r : ℤ)).obj (Q.obj M) :=
    Pi.lift fun r : Fin 4 => Q.map ((blocksMapIso A M).inv ≫ projBlock A M r) ≫
      (QBlockNatIso A (r : ℤ)).inv.app M
  have hφ : ∀ s : Fin 4, φ ≫ Pi.π _ s =
      Q.map ((blocksMapIso A M).inv ≫ projBlock A M s) ≫ (QBlockNatIso A (s : ℤ)).inv.app M :=
    fun s => Limits.Pi.lift_comp_π _ s
  have hself : ∀ s : Fin 4, (blockDerivedι A (s : ℤ)).app (Q.obj M) ≫
      Q.map ((blocksMapIso A M).inv ≫ projBlock A M s) ≫ (QBlockNatIso A (s : ℤ)).inv.app M =
        𝟙 _ := by
    intro s
    rw [blockDerivedι_app_Q, Category.assoc, ← Functor.map_comp_assoc,
      blockιNat_inv_projBlock_self, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app]
    rfl
  have hne : ∀ r s : Fin 4, r ≠ s → (blockDerivedι A (r : ℤ)).app (Q.obj M) ≫
      Q.map ((blocksMapIso A M).inv ≫ projBlock A M s) = 0 := by
    intro r s h
    rw [blockDerivedι_app_Q, Category.assoc, ← Functor.map_comp,
      blockιNat_inv_projBlock_of_ne A M h, CategoryTheory.Functor.map_zero, comp_zero]
  have hterm : ∀ r : Fin 4, φ ≫ Pi.π _ r ≫ (blockDerivedι A (r : ℤ)).app (Q.obj M) =
      Q.map ((blocksMapIso A M).inv ≫ projBlock A M r ≫ (blockιNat A (r : ℤ)).app M) := by
    intro r
    rw [← Category.assoc, hφ, blockDerivedι_app_Q, Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp, Category.assoc]
  refine ⟨φ, ?_, ?_⟩
  · apply Limits.Pi.hom_ext
    intro s
    rw [Category.assoc, hφ, Category.id_comp]
    change (∑ r : Fin 4, Pi.π _ r ≫ (blockDerivedι A (r : ℤ)).app _) ≫ _ = _
    rw [Preadditive.sum_comp, Finset.sum_eq_single s]
    · rw [Category.assoc, hself, Category.comp_id]
    · intro r _ hrs
      rw [Category.assoc, ← Category.assoc ((blockDerivedι A (r : ℤ)).app _), hne r s hrs,
        zero_comp, comp_zero]
    · exact fun h => absurd (Finset.mem_univ s) h
  · change φ ≫ ∑ r : Fin 4, Pi.π _ r ≫ (blockDerivedι A (r : ℤ)).app _ = _
    rw [Preadditive.comp_sum, Finset.sum_congr rfl fun r _ => hterm r, ← Functor.map_sum,
      ← Preadditive.comp_sum, sum_projBlock_blockιNat]
    exact (congrArg Q.map (blocksMapIso A M).inv_hom_id).trans (CategoryTheory.Functor.map_id _ _)

instance isIso_blocksDerivedι : IsIso (blocksDerivedι A) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  obtain ⟨M, ⟨e⟩⟩ := CatModule.DerivedCategory.exists_iso_Q_obj X
  have := isIso_blocksDerivedι_app_Q A M
  have h : (blocksDerivedι A).app X =
      (piFunctor (fun r : Fin 4 => blockDerived.{v, v} A (r : ℤ))).map e.hom ≫
        (blocksDerivedι A).app _ ≫ e.inv := by
    rw [← Category.assoc, (blocksDerivedι A).naturality e.hom]
    simp
  rw [h]
  infer_instance

/-- **The natural block decomposition** `X ≅ ∏_{r<4} (ι (R₀ (X⟨r⟩)))⟨-r⟩`, the inverse of the sum
of the derived block inclusions. -/
def blocksNatIso : 𝟭 _ ≅ piFunctor (fun r : Fin 4 => blockDerived.{v, v} A (r : ℤ)) :=
  (asIso (blocksDerivedι A)).symm

end Blocks

/-! ### Products of functors -/

section Pi

variable {C D : Type*} [Category C] [Category D] [Preadditive D] [HasFiniteBiproducts D]
  {E : Type*} [Category E] [Preadditive E] [HasFiniteBiproducts E]

/-- An additive functor commutes with finite products of functors. -/
def piFunctorCompIso {J : Type} [Finite J] (Φ : J → C ⥤ D) (F : D ⥤ E) [F.Additive] :
    piFunctor Φ ⋙ F ≅ piFunctor fun j => Φ j ⋙ F :=
  NatIso.ofComponents (fun X =>
    have : PreservesLimit (Discrete.functor fun j => (Φ j).obj X) F :=
      preservesProduct_of_preservesBiproduct F
    asIso (piComparison F fun j => (Φ j).obj X)) fun {X Y} f => by
    apply Limits.Pi.hom_ext
    intro j
    simp only [Category.assoc, asIso_hom]
    erw [piComparison_comp_π, Limits.Pi.map_π, piComparison_comp_π_assoc]
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    exact piFunctor_map_π Φ f j

/-- Products of isomorphic families of functors are isomorphic. -/
def piFunctorMapIso {J : Type} [Finite J] {Φ Ψ : J → C ⥤ D} (e : ∀ j, Φ j ≅ Ψ j) :
    piFunctor Φ ≅ piFunctor Ψ :=
  NatIso.ofComponents (fun X => Limits.Pi.mapIso fun j => (e j).app X) fun {X Y} f => by
    apply Limits.Pi.hom_ext
    intro j
    simp

end Pi

/-! ### Restriction to a weight and the derived Hom functors -/

section Tensor

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] [HasDerivedCategory.{v, v} A] [HasDerivedCategory.{v, v} B]
  [CatModule.HasDerivedCategory.{v, v} (SingleObj A)]
  [CatModule.HasDerivedCategory.{v, v} (SingleObj B)]
  [CatModule.HasDerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]
  [CatModule.HasDerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] (hM : IsKProjective.{v} A M)

/-- **The derived tensor product with the diagonally regraded bimodule**,
`Mᵈ ⊗^L_{C_B} - : D(C_B) ⥤ D(C_A)`. -/
abbrev derivedTensor :
    CatModule.DerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded) ⥤
      CatModule.DerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  CatModule.DerivedCategory.derivedTensor (bimodule A B M) (bimodule_left_isKProjective A B M hM)

/-- `RHOM_{C_A}(Mᵈ, -)` followed by restriction to the weight `r` is restriction to the weight
`r` followed by `RHOM_A(M, -)`. -/
def rhomRestrictIso (r : ℤ) :
    CatModule.DerivedCategory.rhom (bimodule A B M) (bimodule_left_isKProjective A B M hM) ⋙
        CatModule.DerivedCategory.restrict (inclusion B r) ≅
      CatModule.DerivedCategory.restrict (inclusion A r) ⋙
        CatModule.DerivedCategory.rhom (DGBimodule.catBimodule A B M)
          (DGBimodule.catBimodule_left_isKProjective A B M hM) :=
  (Localization.whiskeringLeftFunctor' CatModule.DerivedCategory.Q
    (CatModule.quasiIso (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) _).preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CatModule.DerivedCategory.QCompRhomIso _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatModule.DerivedCategory.QCompRestrictIso (inclusion B r)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (homFunctorRestrictIso A B M r) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatModule.DerivedCategory.QCompRhomIso _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CatModule.DerivedCategory.QCompRestrictIso (inclusion A r)).symm _ ≪≫
      Functor.associator _ _ _)

/-- Derived induction along the weight-`r` inclusion followed by `Mᵈ ⊗^L -` is `M ⊗^L -` followed
by derived induction: the left adjoints of the functors of `DG.Diagonal.rhomRestrictIso`. -/
def inductionDerivedTensorIso (r : ℤ) :
    CatModule.DerivedCategory.induction (inclusion B r) ⋙ derivedTensor A B M hM ≅
      CatModule.DerivedCategory.derivedTensor (DGBimodule.catBimodule A B M)
          (DGBimodule.catBimodule_left_isKProjective A B M hM) ⋙
        CatModule.DerivedCategory.induction (inclusion A r) :=
  ((CatModule.DerivedCategory.inductionAdjunction (inclusion B r)).comp
      (CatModule.DerivedCategory.derivedTensorAdjunction _ _)).leftAdjointUniq
    (((CatModule.DerivedCategory.derivedTensorAdjunction _ _).comp
      (CatModule.DerivedCategory.inductionAdjunction (inclusion A r))).ofNatIsoRight
        (rhomRestrictIso A B M hM r).symm)

/-- Derived induction along the weight-`r` inclusion is `D(SingleObj A) ≌ D(A)` followed by the
diagonal functor and `⟨-r⟩`. -/
def inductionIso (r : ℤ) :
    CatModule.DerivedCategory.induction (inclusion A r) ≅
      (CatModule.DerivedCategory.singleObjEquivalence A).functor ⋙
        (toDerived.{v, v, v} A ⋙ shiftDerived.{v, v} A (-r)) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (CatModule.DerivedCategory.singleObjEquivalence A).unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (toDerivedShiftIso A r).symm

/-- On the image `(ι Y)⟨-r⟩` of the diagonal functor followed by an internal shift,
`Mᵈ ⊗^L -` acts by `G = M ⊗^L_B -`. -/
def toDerivedShiftDerivedTensorIso (r : ℤ) :
    (toDerived.{v, v, v} B ⋙ shiftDerived.{v, v} B (-r)) ⋙ derivedTensor A B M hM ≅
      DGBimodule.derivedTensor.{v, v, v, v} A B M hM ⋙
        (toDerived.{v, v, v} A ⋙ shiftDerived.{v, v} A (-r)) :=
  Functor.isoWhiskerRight (toDerivedShiftIso B r) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (inductionDerivedTensorIso A B M hM r) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (inductionIso A r)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm

/-- **On each block, `Mᵈ ⊗^L -` acts by `G = M ⊗^L_B -`**: the block functor
`X ↦ (ι (R₀ (X⟨r⟩)))⟨-r⟩` followed by `Mᵈ ⊗^L -` is the block functor of the diagonal transport
of `G`. -/
def blockDerivedTensorIso (r : ℤ) :
    blockDerived.{v, v} B r ⋙ derivedTensor A B M hM ≅
      transportBlock.{v, v, v, v, v, v, v, v} B A (DGBimodule.derivedTensor.{v, v, v, v} A B M hM)
        r :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (shiftDerived.{v, v} B r)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (recoveryDerived.{v, v} B 0)
      (toDerivedShiftDerivedTensorIso A B M hM r))

/-- **The derived tensor product with the diagonally regraded bimodule is the diagonal transport
of the derived tensor product**: `Mᵈ ⊗^L_{C_B} - ≅ Gᵈ` for `G = M ⊗^L_B -`, a natural
isomorphism of functors `D(C_B) ⥤ D(C_A)`. -/
def derivedTensorTransportIso :
    derivedTensor A B M hM ≅
      transport.{v, v, v, v, v, v, v, v} B A (DGBimodule.derivedTensor.{v, v, v, v} A B M hM) :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (blocksNatIso B) _ ≪≫
    piFunctorCompIso _ _ ≪≫ piFunctorMapIso fun r => blockDerivedTensorIso A B M hM (r : ℤ)

/-- `Mᵈ ⊗^L -` extends `G = M ⊗^L_B -` along the diagonal functors. -/
def derivedTensorToDerivedIso (Y : DG.DerivedCategory.{v, v} B) :
    (derivedTensor A B M hM).obj ((toDerived.{v, v, v} B).obj Y) ≅
      (toDerived.{v, v, v} A).obj ((DGBimodule.derivedTensor.{v, v, v, v} A B M hM).obj Y) :=
  (derivedTensorTransportIso A B M hM).app _ ≪≫ transportToDerivedIso B A _ Y

/-- `Mᵈ ⊗^L -` commutes with the internal shifts. -/
def derivedTensorShiftIso (n : ℤ)
    (X : CatModule.DerivedCategory.{v, v}
      (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)) :
    (derivedTensor A B M hM).obj ((shiftDerived.{v, v} B n).obj X) ≅
      (shiftDerived.{v, v} A n).obj ((derivedTensor A B M hM).obj X) :=
  (derivedTensorTransportIso A B M hM).app _ ≪≫ transportShiftIso B A _ n X ≪≫
    (shiftDerived.{v, v} A n).mapIso ((derivedTensorTransportIso A B M hM).app X).symm

variable (hc : IsCompact.{v} (DG.DerivedCategory.Q.obj (DGModuleCat.of A M)))

include hc in
theorem isCompact_derivedTensor_obj
    {X : CatModule.DerivedCategory.{v, v}
      (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)} (hX : IsCompact.{v} X) :
    IsCompact.{v} ((derivedTensor A B M hM).obj X) :=
  (isCompact_transport_obj B A _ (fun _ hY => DGBimodule.isCompact_derivedTensor_obj hM hc hY)
    hX).of_iso ((derivedTensorTransportIso A B M hM).app X)

/-- The `ℤ[q, q⁻¹]`-linear map induced by `Mᵈ ⊗^L -` on `K₀` of compact objects. -/
def derivedTensorK0 : DiagK0.{v, v} B →ₗ[LaurentPolynomial ℤ] DiagK0.{v, v} A :=
  mapCompactLinear B A (derivedTensor A B M hM)
    (fun _ hX => isCompact_derivedTensor_obj A B M hM hc hX) (derivedTensorShiftIso A B M hM)

/-- **`K₀` of `Mᵈ ⊗^L -` is `id ⊗ K₀(M ⊗^L_B -)`** under
`K₀(D(C_H)^c) ≃ (ℤ[q, q⁻¹] ⧸ (q⁴ - 1)) ⊗ K₀(D(-)^c)`. -/
theorem K0LinearEquiv_derivedTensor (x : DiagK0.{v, v} B) :
    K0LinearEquiv.{v, v, v} A (derivedTensorK0 A B M hM hc x) =
      LinearMap.lTensor _ (K0.mapCompact (DGBimodule.derivedTensor.{v, v, v, v} A B M hM)
        (fun _ hY => DGBimodule.isCompact_derivedTensor_obj hM hc hY)).toIntLinearMap
        (K0LinearEquiv.{v, v, v} B x) :=
  K0LinearEquiv_mapCompact B A _ _ (derivedTensor A B M hM) _ (derivedTensorShiftIso A B M hM)
    (derivedTensorToDerivedIso A B M hM) x

/-- **Super `K₀` of `Mᵈ ⊗^L -` is `id ⊗ K₀(M ⊗^L_B -)`** under
`SuperK0c H ≃ (ℤ[q, q⁻¹] ⧸ (1 + q²)) ⊗ K₀(D(-)^c)`. -/
theorem superK0LinearEquiv_derivedTensor
    (s : HalfGradedDGRing.SuperK0c.{v, v} (HalfGradedDGRing.ofDGRing B)) :
    superK0LinearEquiv.{v, v, v} A
        (HalfGradedDGRing.superK0cMap _ _ (derivedTensorK0 A B M hM hc) s) =
      LinearMap.lTensor _ (K0.mapCompact (DGBimodule.derivedTensor.{v, v, v, v} A B M hM)
        (fun _ hY => DGBimodule.isCompact_derivedTensor_obj hM hc hY)).toIntLinearMap
        (superK0LinearEquiv.{v, v, v} B s) :=
  superK0LinearEquiv_superK0cMap B A _ _ (derivedTensor A B M hM) _
    (derivedTensorShiftIso A B M hM) (derivedTensorToDerivedIso A B M hM) s

end Tensor

end DG.Diagonal
