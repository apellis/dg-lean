import DG.HalfGraded.DiagonalK0Map
import DG.K0.PiFunctor

/-!
# Transport of triangulated functors to the diagonal half-graded setting

Let `A`, `B` be dg rings with diagonal half-graded dg rings `H_A = ofDGRing A`, `H_B = ofDGRing B`
(parameter `2`), weight dg categories `C_A`, `C_B`, diagonal functors `ι = toDerived`, weight-zero
recovery `R₀ = recoveryDerived _ 0` and internal shifts `⟨s⟩ = shiftDerived _ s`. Every object of
`D(C_A)` is the sum of its four blocks `(ι (R₀ (X⟨r⟩)))⟨-r⟩`, `r = 0, …, 3`
(`DG.Diagonal.blocksDerivedIso`). For a triangulated functor `F : D(A) ⥤ D(B)` define

`Fᵈ X = ∏_{r=0}^{3} (ι_B (F (R₀ (X⟨r⟩))))⟨-r⟩`   (`DG.Diagonal.transport F`),

the functor acting by `F` on each block. It is triangulated (`DG.piFunctor_isTriangulated`),
preserves compact objects when `F` does (`DG.Diagonal.isCompact_transport_obj`), extends `F`
along the diagonal functors, `Fᵈ (ι_A Y) ≅ ι_B (F Y)` (`DG.Diagonal.transportToDerivedIso`), and
commutes with the internal shifts, `Fᵈ (X⟨n⟩) ≅ (Fᵈ X)⟨n⟩` (`DG.Diagonal.transportShiftIso`; the
block of index `4` is identified with that of index `0` using `X⟨4⟩ ≅ X⟦2⟧`, which follows from
`Π Π ≅ 𝟭` for the parity shift `Π = ⟨-2⟩ ⋙ ⟦1⟧`). Consequently, under
`DG.Diagonal.K0LinearEquiv` and `DG.Diagonal.superK0LinearEquiv`, the maps induced by `Fᵈ` on `K₀`
and on `SuperK0c` are `id ⊗ K₀(F)` (`DG.Diagonal.K0LinearEquiv_transport`,
`DG.Diagonal.superK0LinearEquiv_transport`).

Applied to a derived tensor product `F = M ⊗^L_B -` with a dg bimodule
(`DG.DGBimodule.derivedTensor`), this gives the half-graded functor induced by `M` together with
its `K₀` and super `K₀` maps. Its identification with the derived tensor product with the
diagonal regrading of `M` over the weight dg categories is `DG.Diagonal.derivedTensorTransportIso`
(`DG/HalfGraded/DiagonalTensor.lean`).
-/

open CategoryTheory Limits LaurentPolynomial

universe w' w v u w₂' w₂ v₂ u₂

noncomputable section

namespace DG

namespace Diagonal

set_option backward.isDefEq.respectTransparency false

/-! ### Products indexed by `Fin 4` -/

section Fin4

variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D] [HasFiniteProducts D]

/-- `∏_{r < 4} f r ≅ f 0 ⊞ (f 1 ⊞ (f 2 ⊞ f 3))`. -/
def piFinFourIso (f : Fin 4 → D) : ∏ᶜ f ≅ f 0 ⊞ (f 1 ⊞ (f 2 ⊞ f 3)) where
  hom := biprod.lift (Pi.π f 0) (biprod.lift (Pi.π f 1) (biprod.lift (Pi.π f 2) (Pi.π f 3)))
  inv := Pi.lift fun r => match r with
    | 0 => biprod.fst
    | 1 => biprod.snd ≫ biprod.fst
    | 2 => biprod.snd ≫ biprod.snd ≫ biprod.fst
    | 3 => biprod.snd ≫ biprod.snd ≫ biprod.snd
  hom_inv_id := by
    ext r
    fin_cases r <;> simp
  inv_hom_id := by
    ext <;> simp

theorem isCompact_piFinFour [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasCoproducts.{w} D]
    {f : Fin 4 → D} (hf : ∀ r, IsCompact.{w} (f r)) : IsCompact.{w} (∏ᶜ f) :=
  ((hf 0).biprod ((hf 1).biprod ((hf 2).biprod (hf 3)))).of_iso (piFinFourIso f)

/-- If `f r` is zero for `r ≠ 0`, then `∏_{r < 4} f r ≅ f 0`. -/
def piFinFourIsoOfIsZero (f : Fin 4 → D) (h1 : IsZero (f 1)) (h2 : IsZero (f 2))
    (h3 : IsZero (f 3)) : ∏ᶜ f ≅ f 0 :=
  piFinFourIso f ≪≫ (isoBiprodZero (biprod_isZero_iff _ _ |>.mpr
    ⟨h1, (biprod_isZero_iff _ _).mpr ⟨h2, h3⟩⟩)).symm

end Fin4

/-! ### Vanishing of the off-diagonal recovery -/

section Vanishing

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, max u v} A]
  [CatModule.HasDerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- `R₀ ((ι Y)⟨j⟩) = 0` for `j ∉ 4ℤ`: the diagonal image vanishes at weights outside `4ℤ`. -/
theorem isZero_recoveryDerived_shift_toDerived (j : ℤ) (hj : ∀ t : ℤ, j ≠ 4 * t)
    (Y : DerivedCategory.{w, max u v} A) :
    IsZero ((recoveryDerived.{w', w} A 0).obj ((shiftDerived.{w', max u v} A j).obj
      ((toDerived.{w', w, max u v} A).obj Y))) := by
  obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj Y
  let M' := (shiftModule A j).obj ((toCatModule A).obj N)
  have : Subsingleton ((recover A 0).obj M') :=
    value_subsingleton A N (0 + j) (fun ⟨t, ht⟩ => hj t (by omega))
  have hz : IsZero (DerivedCategory.Q.obj ((recover A 0).obj M')) :=
    DerivedCategory.Q.map_isZero (DGModuleCat.isZero_of_subsingleton _)
  exact hz.of_iso ((shiftDerived A j ⋙ recoveryDerived A 0).mapIso
    ((toDerived A).mapIso e ≪≫ toDerivedObjIso A N) ≪≫ (recoveryDerived A 0).mapIso
      ((CatModule.DerivedCategory.QCompRestrictIso _).app _) ≪≫ recoveryDerivedObjIso A 0 M')

end Vanishing

/-! ### Periodicity: `X⟨4⟩ ≅ X⟦2⟧` -/

section Periodicity

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [CatModule.HasDerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]

/-- `⟨s⟩ ≅ ⟨t⟩` for `s = t`. -/
abbrev shiftEqIso {s t : ℤ} (h : s = t) :
    shiftDerived.{w', max u v} A s ≅ shiftDerived A t :=
  (CatModule.DerivedCategory.internalShiftAction _).isoOfEq h

/-- `Π Y = (Y⟨-2⟩)⟦1⟧`. -/
def parityShiftObjIso (Y : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (HalfGradedDGRing.parityShiftD (HalfGradedDGRing.ofDGRing A)).obj Y ≅
      ((shiftDerived.{w', max u v} A (-2)).obj Y)⟦(1 : ℤ)⟧ :=
  Iso.refl _

/-- `(Z⟨-4⟩)⟦2⟧ ≅ Z`, from `Π Π ≅ 𝟭` for the parity shift `Π = ⟨-2⟩ ⋙ ⟦1⟧`. -/
def shiftNegFourIso (Z : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    ((shiftDerived.{w', max u v} A (-4)).obj Z)⟦(2 : ℤ)⟧ ≅ Z :=
  (shiftFunctorAdd' _ (1 : ℤ) 1 2 (by norm_num)).app _ ≪≫
    (shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)).mapIso
      (((CatModule.DerivedCategory.internalShiftAddIso _ (-2) (-2)).app Z).symm ≪≫
        (shiftEqIso A (by norm_num : (-2 : ℤ) + -2 = -4)).app Z).symm ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso
      (((shiftDerived.{w', max u v} A (-2)).commShiftIso (1 : ℤ)).app
        ((shiftDerived A (-2)).obj Z)).symm ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso ((shiftDerived.{w', max u v} A (-2)).mapIso
      (parityShiftObjIso A Z).symm) ≪≫
    (parityShiftObjIso A _).symm ≪≫
    (HalfGradedDGRing.parityShiftDIso (HalfGradedDGRing.ofDGRing A)).app Z

/-- `Z⟨4⟩ ≅ Z⟦2⟧`. -/
def shiftFourIso (Z : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (shiftDerived.{w', max u v} A 4).obj Z ≅ Z⟦(2 : ℤ)⟧ :=
  (shiftNegFourIso A _).symm ≪≫ (shiftFunctor _ (2 : ℤ)).mapIso
    (((CatModule.DerivedCategory.internalShiftAddIso _ 4 (-4)).app Z).symm ≪≫
      (shiftEqIso A (by norm_num : (4 : ℤ) + -4 = 0)).app Z ≪≫
      (CatModule.DerivedCategory.internalShiftZeroIso _).app Z)

/-- `(W⟦2⟧)⟨-4⟩ ≅ W`. -/
def shiftTwoNegFourIso (W : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (shiftDerived.{w', max u v} A (-4)).obj (W⟦(2 : ℤ)⟧) ≅ W :=
  ((shiftDerived.{w', max u v} A (-4)).commShiftIso (2 : ℤ)).app W ≪≫ shiftNegFourIso A W

end Periodicity

/-! ### The transported functor -/

section Transport

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, max u v} A]
  [CatModule.HasDerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]
  (B : Type u₂) [Ring B] [DGAddCommGroup B] [DGRing B]
  [HasDerivedCategory.{w₂, max u₂ v₂} B]
  [CatModule.HasDerivedCategory.{w₂', max u₂ v₂}
    (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)]
  (F : DerivedCategory.{w, max u v} A ⥤ DerivedCategory.{w₂, max u₂ v₂} B)
  [F.CommShift ℤ] [F.IsTriangulated]

/-- The block functor `X ↦ (ι_B (F (R₀ (X⟨s⟩))))⟨-s⟩`. -/
abbrev transportBlock (s : ℤ) :
    CatModule.DerivedCategory.{w', max u v}
        (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤
      CatModule.DerivedCategory.{w₂', max u₂ v₂}
        (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded) :=
  shiftDerived.{w', max u v} A s ⋙ recoveryDerived.{w', w} A 0 ⋙ F ⋙
    toDerived.{w₂', w₂, max u₂ v₂} B ⋙ shiftDerived.{w₂', max u₂ v₂} B (-s)

/-- **The diagonal transport** `Fᵈ X = ∏_{r=0}^{3} (ι_B (F (R₀ (X⟨r⟩))))⟨-r⟩` of a triangulated
functor `F : D(A) ⥤ D(B)`: a triangulated functor `D(C_A) ⥤ D(C_B)` acting by `F` on blocks. -/
abbrev transport :
    CatModule.DerivedCategory.{w', max u v}
        (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⥤
      CatModule.DerivedCategory.{w₂', max u₂ v₂}
        (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded) :=
  piFunctor fun r : Fin 4 => transportBlock A B F (r : ℤ)

omit [F.CommShift ℤ] [F.IsTriangulated] in
/-- The transported functor preserves compact objects when `F` does. -/
theorem isCompact_transport_obj
    (hF : ∀ X, IsCompact.{max u v} X → IsCompact.{max u₂ v₂} (F.obj X))
    {X : CatModule.DerivedCategory.{w', max u v}
      (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (hX : IsCompact.{max u v} X) :
    IsCompact.{max u₂ v₂} ((transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F).obj X) :=
  isCompact_piFinFour fun _ =>
    (CatModule.DerivedCategory.isCompact_internalShift_obj_iff _ _ _).mpr
      (isCompact_toDerived B (hF _ (isCompact_recoveryDerived A
        ((CatModule.DerivedCategory.isCompact_internalShift_obj_iff _ _ _).mpr hX))))

/-- **`Fᵈ (ι_A Y) ≅ ι_B (F Y)`**: the transported functor extends `F` along the diagonal
functors. -/
def transportToDerivedIso (Y : DerivedCategory.{w, max u v} A) :
    (transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F).obj ((toDerived.{w', w, max u v} A).obj Y) ≅
      (toDerived.{w₂', w₂, max u₂ v₂} B).obj (F.obj Y) :=
  have hz : ∀ j : ℤ, (∀ t : ℤ, j ≠ 4 * t) →
      IsZero ((transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F j).obj
        ((toDerived.{w', w, max u v} A).obj Y)) := fun j hj =>
    ((shiftDerived B (-j)).map_isZero ((toDerived B).map_isZero
      (F.map_isZero (isZero_recoveryDerived_shift_toDerived A j hj Y))))
  piFinFourIsoOfIsZero _ (hz 1 (fun t => by omega)) (hz 2 (fun t => by omega))
      (hz 3 (fun t => by omega)) ≪≫
    (CatModule.DerivedCategory.internalShiftZeroIso _).app _ ≪≫
    (toDerived B).mapIso (F.mapIso ((recoveryDerived A 0).mapIso
      ((CatModule.DerivedCategory.internalShiftZeroIso _).app _) ≪≫
        (asIso ((diagonalDerivedAdjunction.{w', w, max u v} A).unit.app Y)).symm))

/-- Equal indices give isomorphic blocks. -/
def blockCongr {s t : ℤ} (h : s = t) (X : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F s).obj X ≅
      (transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F t).obj X :=
  eqToIso (by rw [h])

/-- `Φₛ (X⟨1⟩) ≅ (Φₛ₊₁ X)⟨1⟩` for the block functors. -/
def blockShiftIso (s : ℤ) (X : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F s).obj
        ((shiftDerived.{w', max u v} A 1).obj X) ≅
      (shiftDerived.{w₂', max u₂ v₂} B 1).obj
        ((transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F (s + 1)).obj X) :=
  (shiftDerived B (-s)).mapIso ((toDerived B).mapIso (F.mapIso ((recoveryDerived A 0).mapIso
      (((CatModule.DerivedCategory.internalShiftAddIso _ 1 s).app X).symm ≪≫
        (shiftEqIso A (add_comm 1 s)).app X)))) ≪≫
    (shiftEqIso B (by ring : -s = -(s + 1) + 1)).app _ ≪≫
    (CatModule.DerivedCategory.internalShiftAddIso _ (-(s + 1)) 1).app _

/-- `Φ₄ X ≅ Φ₀ X`, using `X⟨4⟩ ≅ X⟦2⟧` and `(W⟦2⟧)⟨-4⟩ ≅ W`. -/
def blockFourIso (X : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F 4).obj X ≅
      (transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F 0).obj X :=
  (shiftDerived B (-4)).mapIso
      ((recoveryDerived.{w', w} A 0 ⋙ F ⋙ toDerived.{w₂', w₂, max u₂ v₂} B).mapIso
        (shiftFourIso A X) ≪≫
        ((recoveryDerived.{w', w} A 0 ⋙ F ⋙ toDerived.{w₂', w₂, max u₂ v₂} B).commShiftIso
          (2 : ℤ)).app X) ≪≫
    shiftTwoNegFourIso B _ ≪≫
    ((recoveryDerived.{w', w} A 0 ⋙ F ⋙ toDerived.{w₂', w₂, max u₂ v₂} B).mapIso
      ((CatModule.DerivedCategory.internalShiftZeroIso _).app X)).symm ≪≫
    ((CatModule.DerivedCategory.internalShiftZeroIso _).app _).symm ≪≫
    (shiftEqIso B (neg_zero).symm).app _

theorem fin_four_succ (r : Fin 4) :
    (r : ℤ) + 1 = ((r + 1 : Fin 4) : ℤ) ∨ ((r : ℤ) + 1 = 4 ∧ ((r + 1 : Fin 4) : ℤ) = 0) := by
  fin_cases r <;> decide

/-- The block of index `r + 1` at the index `r + 1 ∈ Fin 4`. -/
def blockSuccIso (r : Fin 4) (X : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F ((r : ℤ) + 1)).obj X ≅
      (transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F ((r + 1 : Fin 4) : ℤ)).obj X :=
  if h : (r : ℤ) + 1 = ((r + 1 : Fin 4) : ℤ) then blockCongr A B F h X else
    have h' := (fin_four_succ r).resolve_left h
    blockCongr A B F h'.1 X ≪≫ blockFourIso A B F X ≪≫ blockCongr A B F h'.2.symm X

instance (n : ℤ) (f : Fin 4 → CatModule.DerivedCategory.{w₂', max u₂ v₂}
    (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)) :
    IsIso (piComparison (shiftDerived.{w₂', max u₂ v₂} B n) f) :=
  have : (shiftDerived.{w₂', max u₂ v₂} B n).IsEquivalence :=
    inferInstanceAs (CatModule.DerivedCategory.internalShiftEquiv _ n).functor.IsEquivalence
  inferInstance

/-- **`Fᵈ (X⟨1⟩) ≅ (Fᵈ X)⟨1⟩`**: the block of index `r` of `X⟨1⟩` is the shifted block of index
`r + 1` of `X`, the index `4` being identified with `0`. -/
def transportShiftOneIso (X : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F).obj ((shiftDerived.{w', max u v} A 1).obj X) ≅
      (shiftDerived.{w₂', max u₂ v₂} B 1).obj
        ((transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F).obj X) :=
  Limits.Pi.mapIso (fun r : Fin 4 => blockShiftIso A B F r X ≪≫
      (shiftDerived B 1).mapIso (blockSuccIso A B F r X)) ≪≫
    Pi.whiskerEquiv (f := fun r : Fin 4 => (shiftDerived.{w₂', max u₂ v₂} B 1).obj
        ((transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F ((r + 1 : Fin 4) : ℤ)).obj X))
      (g := fun r : Fin 4 => (shiftDerived.{w₂', max u₂ v₂} B 1).obj
        ((transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F (r : ℤ)).obj X))
      (Equiv.addRight 1) (fun _ => Iso.refl _) ≪≫
    (asIso (piComparison (shiftDerived.{w₂', max u₂ v₂} B 1) fun r : Fin 4 =>
      (transportBlock.{w', w, v, u, w₂', w₂, v₂, u₂} A B F (r : ℤ)).obj X)).symm

omit [F.IsTriangulated] in
/-- `Fᵈ (X⟨n⟩) ≅ (Fᵈ X)⟨n⟩` for every `n`, by induction from `n = 1`. -/
theorem nonempty_transportShiftIso (n : ℤ) (X : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    Nonempty ((transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F).obj
        ((shiftDerived.{w', max u v} A n).obj X) ≅
      (shiftDerived.{w₂', max u₂ v₂} B n).obj
        ((transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F).obj X)) := by
  let G := transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F
  induction n using Int.induction_on generalizing X with
  | zero =>
    exact ⟨G.mapIso ((CatModule.DerivedCategory.internalShiftZeroIso _).app X) ≪≫
      ((CatModule.DerivedCategory.internalShiftZeroIso _).app _).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih X
    exact ⟨G.mapIso ((CatModule.DerivedCategory.internalShiftAddIso _ n 1).app X) ≪≫
      transportShiftOneIso A B F _ ≪≫ (shiftDerived B 1).mapIso e ≪≫
      ((CatModule.DerivedCategory.internalShiftAddIso _ n 1).app _).symm⟩
  | pred n ih =>
    let X' := (shiftDerived.{w', max u v} A (-(n : ℤ) - 1)).obj X
    obtain ⟨e⟩ := ih X
    have e1 : (shiftDerived.{w', max u v} A 1).obj X' ≅ (shiftDerived A (-(n : ℤ))).obj X :=
      ((CatModule.DerivedCategory.internalShiftAddIso _ (-(n : ℤ) - 1) 1).app X).symm ≪≫
        (shiftEqIso A (by ring)).app X
    have e2 : (shiftDerived.{w₂', max u₂ v₂} B 1).obj (G.obj X') ≅
        (shiftDerived B (-(n : ℤ))).obj (G.obj X) :=
      (transportShiftOneIso A B F X').symm ≪≫ G.mapIso e1 ≪≫ e
    exact ⟨((CatModule.DerivedCategory.internalShiftZeroIso _).app _).symm ≪≫
      (shiftEqIso B (by ring : (0 : ℤ) = 1 + -1)).app _ ≪≫
      (CatModule.DerivedCategory.internalShiftAddIso _ 1 (-1)).app _ ≪≫
      (shiftDerived B (-1)).mapIso e2 ≪≫
      ((CatModule.DerivedCategory.internalShiftAddIso _ (-(n : ℤ)) (-1)).app _).symm ≪≫
      (shiftEqIso B (by ring)).app _⟩

/-- The isomorphisms `Fᵈ (X⟨n⟩) ≅ (Fᵈ X)⟨n⟩`. -/
def transportShiftIso (n : ℤ) (X : CatModule.DerivedCategory.{w', max u v}
    (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    (transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F).obj
        ((shiftDerived.{w', max u v} A n).obj X) ≅
      (shiftDerived.{w₂', max u₂ v₂} B n).obj
        ((transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F).obj X) :=
  (nonempty_transportShiftIso A B F n X).some

variable (hF : ∀ X, IsCompact.{max u v} X → IsCompact.{max u₂ v₂} (F.obj X))

/-- The `ℤ[q, q⁻¹]`-linear map induced by `Fᵈ` on `K₀` of compact objects. -/
def transportK0 : DiagK0.{w', v} A →ₗ[LaurentPolynomial ℤ] DiagK0.{w₂', v₂} B :=
  mapCompactLinear A B (transport.{w', w, v, u, w₂', w₂, v₂, u₂} A B F)
    (fun _ hX => isCompact_transport_obj A B F hF hX) (transportShiftIso A B F)

/-- **`K₀` of the transported functor is `id ⊗ K₀(F)`** under
`K₀(D(C_H)^c) ≃ (ℤ[q, q⁻¹] ⧸ (q⁴ - 1)) ⊗ K₀(D(-)^c)`. -/
theorem K0LinearEquiv_transport (x : DiagK0.{w', v} A) :
    K0LinearEquiv.{w₂', w₂, v₂} B (transportK0 A B F hF x) =
      LinearMap.lTensor _ (K0.mapCompact F hF).toIntLinearMap
        (K0LinearEquiv.{w', w, v} A x) :=
  K0LinearEquiv_mapCompact A B F hF _ _ (transportShiftIso A B F)
    (transportToDerivedIso A B F) x

/-- **Super `K₀` of the transported functor is `id ⊗ K₀(F)`** under
`SuperK0c H ≃ (ℤ[q, q⁻¹] ⧸ (1 + q²)) ⊗ K₀(D(-)^c)`. -/
theorem superK0LinearEquiv_transport
    (s : HalfGradedDGRing.SuperK0c.{w', v} (HalfGradedDGRing.ofDGRing A)) :
    superK0LinearEquiv.{w₂', w₂, v₂} B
      (HalfGradedDGRing.superK0cMap _ _ (transportK0 A B F hF) s) =
      LinearMap.lTensor _ (K0.mapCompact F hF).toIntLinearMap
        (superK0LinearEquiv.{w', w, v} A s) :=
  superK0LinearEquiv_superK0cMap A B F hF _ _ (transportShiftIso A B F)
    (transportToDerivedIso A B F) s

end Transport

end Diagonal

end DG

end
