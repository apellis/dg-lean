import DG.HalfGraded.DiagonalTensor

/-!
# Functoriality of the diagonal transport

For triangulated functors `F : D(A) ⥤ D(B)` and `G : D(B) ⥤ D(C)` between derived categories of
dg rings, the diagonal transport `Fᵈ : D(C_A) ⥤ D(C_B)` (`DG.Diagonal.transport`, acting by `F` on
the four blocks `(ι (R₀ (X⟨r⟩)))⟨-r⟩`) is functorial:

* `DG.Diagonal.transportMapIso`: `F ≅ F'` induces `Fᵈ ≅ F'ᵈ`;
* `DG.Diagonal.recoveryShiftTransportIso`: `R₀ ((Fᵈ X)⟨s⟩) ≅ F (R₀ (X⟨s⟩))` for `s = 0, …, 3`,
  naturally in `X` (the other blocks of `Fᵈ X` vanish there);
* `DG.Diagonal.transportCompIso`: **`(F ⋙ G)ᵈ ≅ Fᵈ ⋙ Gᵈ`**;
* `DG.Diagonal.transportIdIso`: `(𝟭)ᵈ ≅ 𝟭`, the block decomposition `DG.Diagonal.blocksNatIso`;
* `DG.Diagonal.transportEquivalence`: hence the transport of an equivalence (with triangulated
  quasi-inverse) is an equivalence, and `DG.Diagonal.transportFullyFaithful`: it is fully faithful.

Combined with `DG.Diagonal.derivedTensorTransportIso` (`Mᵈ ⊗^L - ≅ (M ⊗^L -)ᵈ`), isomorphisms
between composites of derived tensor products with dg bimodules transport to the corresponding
isomorphisms between composites of derived tensor products with the diagonally regraded bimodules.
All rings, modules and derived categories are taken in one universe.
-/

open CategoryTheory Limits

universe v

namespace DG

noncomputable section

/-! ### Products of functors with one nonzero factor -/

section Pi

variable {C D : Type*} [Category C] [Category D] [Preadditive D] [HasFiniteBiproducts D]

/-- If all factors but `Φ s` vanish, the product of the functors `Φ j` is `Φ s`. -/
def piFunctorIsoOfIsZero {J : Type} [Finite J] [DecidableEq J] (Φ : J → C ⥤ D) (s : J)
    (h : ∀ j, j ≠ s → ∀ X, IsZero ((Φ j).obj X)) : piFunctor Φ ≅ Φ s :=
  NatIso.ofComponents (fun X =>
    { hom := Pi.π (fun j => (Φ j).obj X) s
      inv := Pi.lift fun j => if hj : j = s then eqToHom (by subst hj; rfl) else 0
      hom_inv_id := by
        ext j
        by_cases hj : j = s
        · subst hj
          simp
        · exact (h j hj X).eq_of_tgt _ _
      inv_hom_id := by simp }) fun f => piFunctor_map_π Φ f s

end Pi

namespace Diagonal

variable (A B C : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] [Ring C] [DGAddCommGroup C] [DGRing C]
  [HasDerivedCategory.{v, v} A] [HasDerivedCategory.{v, v} B] [HasDerivedCategory.{v, v} C]
  [CatModule.HasDerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]
  [CatModule.HasDerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)]
  [CatModule.HasDerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing C).Regraded)]

/-- An isomorphism of triangulated functors induces an isomorphism of their transports. -/
def transportMapIso {F F' : DerivedCategory.{v, v} A ⥤ DerivedCategory.{v, v} B}
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated] (e : F ≅ F') :
    transport.{v, v, v, v, v, v, v, v} A B F ≅ transport.{v, v, v, v, v, v, v, v} A B F' :=
  piFunctorMapIso fun _ => Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
    (Functor.isoWhiskerRight e _))

variable {A B C}

variable (F : DerivedCategory.{v, v} A ⥤ DerivedCategory.{v, v} B) [F.CommShift ℤ]
  [F.IsTriangulated]

/-- `⟨-r⟩ ⋙ ⟨s⟩ ≅ ⟨s - r⟩`. -/
def shiftShiftIso (r s : ℤ) :
    shiftDerived.{v, v} B (-r) ⋙ shiftDerived.{v, v} B s ≅ shiftDerived.{v, v} B (s - r) :=
  (CatModule.DerivedCategory.internalShiftAddIso _ (-r) s).symm ≪≫
    shiftEqIso B (by ring)

omit [F.CommShift ℤ] [F.IsTriangulated] in
/-- The `r`-th block of `Fᵈ X`, shifted by `s` and recovered at weight zero: zero unless `r = s`. -/
theorem isZero_block_shift_recovery (r s : Fin 4) (hrs : r ≠ s)
    (X : CatModule.DerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)) :
    IsZero ((transportBlock.{v, v, v, v, v, v, v, v} A B F (r : ℤ) ⋙ shiftDerived.{v, v} B (s : ℤ) ⋙
      recoveryDerived.{v, v} B 0).obj X) := by
  have hj : ∀ t : ℤ, (s : ℤ) - (r : ℤ) ≠ 4 * t := by
    intro t ht
    have hr := r.isLt
    have hs := s.isLt
    apply hrs
    ext
    omega
  exact (isZero_recoveryDerived_shift_toDerived B ((s : ℤ) - r) hj _).of_iso
    ((recoveryDerived B 0).mapIso ((shiftShiftIso (B := B) (r : ℤ) (s : ℤ)).app _))

/-- **`R₀ ((Fᵈ X)⟨s⟩) ≅ F (R₀ (X⟨s⟩))`** for `s = 0, …, 3`, naturally in `X`. -/
def recoveryShiftTransportIso (s : Fin 4) :
    transport.{v, v, v, v, v, v, v, v} A B F ⋙ shiftDerived.{v, v} B (s : ℤ) ⋙
        recoveryDerived.{v, v} B 0 ≅
      shiftDerived.{v, v} A (s : ℤ) ⋙ recoveryDerived.{v, v} A 0 ⋙ F :=
  piFunctorCompIso _ _ ≪≫
    piFunctorIsoOfIsZero _ s (fun r hrs X => isZero_block_shift_recovery F r s hrs X) ≪≫
    Functor.isoWhiskerLeft (shiftDerived.{v, v} A (s : ℤ) ⋙ recoveryDerived.{v, v} A 0 ⋙ F)
      (Functor.isoWhiskerLeft (toDerived.{v, v, v} B)
          (Functor.isoWhiskerRight ((shiftShiftIso (B := B) (s : ℤ) (s : ℤ)) ≪≫
            shiftEqIso B (sub_self _) ≪≫ CatModule.DerivedCategory.internalShiftZeroIso _)
            (recoveryDerived.{v, v} B 0) ≪≫ Functor.leftUnitor _) ≪≫
        derivedRecoveryNatIso B) ≪≫ Functor.rightUnitor _

variable (G : DerivedCategory.{v, v} B ⥤ DerivedCategory.{v, v} C) [G.CommShift ℤ]
  [G.IsTriangulated]

/-- **`(F ⋙ G)ᵈ ≅ Fᵈ ⋙ Gᵈ`**: transport is compatible with composition. -/
def transportCompIso :
    transport.{v, v, v, v, v, v, v, v} A C (F ⋙ G) ≅
      transport.{v, v, v, v, v, v, v, v} A B F ⋙ transport.{v, v, v, v, v, v, v, v} B C G :=
  (piFunctorMapIso fun s : Fin 4 =>
    (Functor.isoWhiskerRight (recoveryShiftTransportIso F s)
      (G ⋙ toDerived.{v, v, v} C ⋙ shiftDerived.{v, v} C (-(s : ℤ)))).symm) ≪≫ Iso.refl _

variable (A) in
/-- `(𝟭)ᵈ ≅ 𝟭`: the transport of the identity is the block decomposition. -/
def transportIdIso :
    transport.{v, v, v, v, v, v, v, v} A A (𝟭 (DerivedCategory.{v, v} A)) ≅ 𝟭 _ :=
  (blocksNatIso A).symm

/-- **The transport of an equivalence is an equivalence**: for triangulated `F`, `G` with
`F ⋙ G ≅ 𝟭` and `G ⋙ F ≅ 𝟭`, the transports form an equivalence. -/
def transportEquivalence (G : DerivedCategory.{v, v} B ⥤ DerivedCategory.{v, v} A)
    [G.CommShift ℤ] [G.IsTriangulated] (eFG : F ⋙ G ≅ 𝟭 _) (eGF : G ⋙ F ≅ 𝟭 _) :
    CatModule.DerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ≌
      CatModule.DerivedCategory.{v, v} (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded) :=
  CategoryTheory.Equivalence.mk (transport.{v, v, v, v, v, v, v, v} A B F)
    (transport.{v, v, v, v, v, v, v, v} B A G)
    ((transportIdIso A).symm ≪≫ transportMapIso A A eFG.symm ≪≫ transportCompIso F G)
    ((transportCompIso G F).symm ≪≫ transportMapIso B B eGF ≪≫ transportIdIso B)

/-- The transport of an equivalence is fully faithful. -/
def transportFullyFaithful (G : DerivedCategory.{v, v} B ⥤ DerivedCategory.{v, v} A)
    [G.CommShift ℤ] [G.IsTriangulated] (eFG : F ⋙ G ≅ 𝟭 _) (eGF : G ⋙ F ≅ 𝟭 _) :
    (transport.{v, v, v, v, v, v, v, v} A B F).FullyFaithful :=
  (transportEquivalence F G eFG eGF).fullyFaithfulFunctor

end Diagonal

end

end DG
