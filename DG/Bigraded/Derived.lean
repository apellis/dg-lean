import DG.Bigraded.TriangulatedAction
import DG.Category.Derived.Coproducts
import DG.Category.Derived.RestrictionIso
import DG.Category.WeightComparison

/-!
# The internal shift on the homotopy and derived categories of a bigraded dg ring

Let `A` be a dg ring with an internal (weight) grading (`DG.BigradedDGRing A`) and let
`C_A = DG.WeightCategory A` be its weight dg category (objects `k : ℤ`, `C_A(k, l) = A⟨l - k⟩`).
Dg modules over `C_A` are the bigraded dg `A`-modules (`DG.CatModule.weightEquivalence`), so the
homotopy category `H(C_A)` and the derived category `D(C_A)` are the homotopy and derived
categories of bigraded dg `A`-modules.

The shift of objects `k ↦ k + s` is a dg automorphism of `C_A`
(`DG.WeightCategory.shiftFunctor`, `DG.WeightCategory.shiftEquiv`), and the internal shift
`M ↦ M⟨s⟩`, `(M⟨s⟩)⟨k⟩ = M⟨k + s⟩`, is restriction along it
(`DG.BigradedDGModuleCat.internalShiftToCatModuleIso`). We define the internal shift on
`H(C_A)` and `D(C_A)` in this way, as restriction along `k ↦ k + s`. Restriction along a dg
functor is a triangulated functor (`DG.CatModule.HomotopyCategory.precomp_isTriangulated`,
`DG.CatModule.DerivedCategory.restrict_isTriangulated`), so `⟨s⟩` commutes with the homological
shift `⟦1⟧` and is triangulated.

## Main definitions and results

* `DG.WeightCategory.shiftFunctorZeroIso`, `DG.WeightCategory.shiftFunctorAddIso`: the dg
  isomorphisms `(k ↦ k + 0) ≅ 𝟭` and `(k ↦ k + (s + t)) ≅ (k ↦ k + t) ⋙ (k ↦ k + s)`, with
  components `1 ∈ A⟨0⟩`.
* `DG.CatModule.HomotopyCategory.internalShift A s` and
  `DG.CatModule.DerivedCategory.internalShift A s`: the internal shift `⟨s⟩` on `H(C_A)` and
  `D(C_A)`; triangulated (instances), with `⟨0⟩ ≅ 𝟭` and `⟨s + t⟩ ≅ ⟨s⟩ ⋙ ⟨t⟩`
  (`internalShiftZeroIso`, `internalShiftAddIso`), packaged as an action of `ℤ` by triangulated
  functors (`internalShiftAction`, `DG.TriangulatedIntAction`); `internalShiftEquiv s` is the
  triangulated autoequivalence `⟨s⟩` with inverse `⟨-s⟩`.
* Compatibility with the internal shift of bigraded dg modules
  (`DG.BigradedDGModuleCat.internalShiftFunctor`) under `M ↦ (k ↦ M⟨k⟩)`:
  `DG.CatModule.HomotopyCategory.toCatModuleCompInternalShiftIso` and
  `DG.CatModule.DerivedCategory.toCatModuleCompInternalShiftIso`.
* `DG.CatModule.DerivedCategory.isCompact_internalShift_obj_iff`: `⟨s⟩` preserves and reflects
  compact objects of `D(C_A)`.
* The `ℤ[q, q⁻¹]`-module structures on `K₀(H(C_A))`, `K₀(D(C_A))` and on `K₀` of the compact
  objects `D(C_A)^c = DG.compactSubcategory (D(C_A))`, with `qⁿ • [M] = [M⟨n⟩]`
  (`DG.CatModule.DerivedCategory.T_smul_mk`, `DG.CatModule.DerivedCategory.T_smul_mk_compact`).

## Universes

For `A : Type u`, dg modules take values in `Type w` and `D(C_A)` has morphisms in `Type w'`
(`[DG.CatModule.HasDerivedCategory.{w', w} (DG.WeightCategory A)]`); compactness in `D(C_A)` is
relative to coproducts indexed by `Type w`, which exist in `D(C_A)`
(`DG.CatModule.DerivedCategory.hasCoproducts`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Category Limits Pretriangulated

universe w' w u

namespace DG

namespace WeightCategory

variable (A : Type u) [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]

/-- The shift by `0` of the objects of `C_A` is isomorphic to the identity, by `1 ∈ A⟨0⟩`. -/
def shiftFunctorZeroIso : shiftFunctor A 0 ≅ 𝟭 (WeightCategory A) :=
  NatIso.ofComponents (fun _ => isoOfEq (by simp)) (fun f => Subtype.ext (by simp))

/-- `(k ↦ k + (s + t)) ≅ (k ↦ k + t) ⋙ (k ↦ k + s)`, by `1 ∈ A⟨0⟩`. -/
def shiftFunctorAddIso (s t : ℤ) :
    shiftFunctor A (s + t) ≅ shiftFunctor A t ⋙ shiftFunctor A s :=
  NatIso.ofComponents (fun _ => isoOfEq (by simp only [shiftFunctor_obj, Functor.comp_obj]; ring))
    (fun f => Subtype.ext (by simp))

variable {A} [DGRing A]

/-- A morphism of `C_A` given by `1 ∈ A⟨0⟩` has degree `0`. -/
theorem mem_grading_zero_of_val_eq_one {k l : WeightCategory A} (f : k ⟶ l) (hf : f.1 = 1) :
    f ∈ grading 0 := by
  rw [mem_grading_iff, hf]
  exact one_mem_grading (A := A)

/-- A morphism of `C_A` given by `1 ∈ A⟨0⟩` is a cocycle. -/
theorem d_eq_zero_of_val_eq_one {k l : WeightCategory A} (f : k ⟶ l) (hf : f.1 = 1) :
    d f = 0 :=
  Subtype.ext (by rw [d_val, hf, d_one]; rfl)

end WeightCategory

open WeightCategory

variable (A : Type u) [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]
  [DGRing A]

namespace CatModule

/-! ### The internal shift on the homotopy category -/

namespace HomotopyCategory

/-- The internal shift `⟨s⟩` on the homotopy category `H(C_A)` of bigraded dg modules:
restriction along the shift `k ↦ k + s` of the objects of `C_A`, `(M⟨s⟩)⟨k⟩ = M⟨k + s⟩`. -/
noncomputable def internalShift (s : ℤ) :
    HomotopyCategory.{w} (WeightCategory A) ⥤ HomotopyCategory.{w} (WeightCategory A) :=
  precomp (shiftFunctor A s)

/-- The internal shift commutes with the homological shift. -/
noncomputable instance (s : ℤ) : (internalShift.{w} A s).CommShift ℤ :=
  inferInstanceAs ((precomp (shiftFunctor A s)).CommShift ℤ)

/-- The internal shift is a triangulated functor. -/
instance (s : ℤ) : (internalShift.{w} A s).IsTriangulated :=
  inferInstanceAs (precomp (shiftFunctor A s)).IsTriangulated

/-- `M⟨0⟩ ≅ M`. -/
noncomputable def internalShiftZeroIso : internalShift.{w} A 0 ≅ 𝟭 _ :=
  precompNatIso (shiftFunctorZeroIso A) (fun _ => mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => d_eq_zero_of_val_eq_one _ rfl) (fun _ => mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => d_eq_zero_of_val_eq_one _ rfl) ≪≫ precompIdIso _

/-- `M⟨s + t⟩ ≅ M⟨s⟩⟨t⟩`. -/
noncomputable def internalShiftAddIso (s t : ℤ) :
    internalShift.{w} A (s + t) ≅ internalShift A s ⋙ internalShift A t :=
  precompNatIso (shiftFunctorAddIso A s t) (fun _ => mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => d_eq_zero_of_val_eq_one _ rfl) (fun _ => mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => d_eq_zero_of_val_eq_one _ rfl) ≪≫ precompCompIso _ _

/-- The internal shifts form an action of `ℤ` on `H(C_A)` by triangulated functors. -/
noncomputable def internalShiftAction :
    TriangulatedIntAction (HomotopyCategory.{w} (WeightCategory A)) where
  functor := internalShift A
  zeroIso := internalShiftZeroIso A
  addIso := internalShiftAddIso A

@[simp]
theorem internalShiftAction_functor (s : ℤ) :
    (internalShiftAction.{w} A).functor s = internalShift A s := rfl

/-- The internal shift `⟨s⟩` is a triangulated autoequivalence of `H(C_A)`, with inverse
`⟨-s⟩`. -/
noncomputable def internalShiftEquiv (s : ℤ) :
    HomotopyCategory.{w} (WeightCategory A) ≌ HomotopyCategory.{w} (WeightCategory A) :=
  (internalShiftAction A).equivalence s

@[simp]
theorem internalShiftEquiv_functor (s : ℤ) :
    (internalShiftEquiv.{w} A s).functor = internalShift A s := rfl

@[simp]
theorem internalShiftEquiv_inverse (s : ℤ) :
    (internalShiftEquiv.{w} A s).inverse = internalShift A (-s) := rfl

/-- The internal shift commutes with the homological shifts: `M⟨s⟩⟦n⟧ ≅ M⟦n⟧⟨s⟩`. -/
noncomputable def internalShiftShiftIso (s n : ℤ) (M : HomotopyCategory.{w} (WeightCategory A)) :
    (internalShift A s).obj (M⟦n⟧) ≅ ((internalShift A s).obj M)⟦n⟧ :=
  ((internalShift A s).commShiftIso n).app M

/-- The internal shift on `H(C_A)` is induced by restriction along `k ↦ k + s` on dg
modules. -/
noncomputable def quotientCompInternalShiftIso (s : ℤ) :
    quotient.{w} (WeightCategory A) ⋙ internalShift A s ≅
      CatModule.precomp (shiftFunctor A s) ⋙ quotient _ :=
  precompFactors _

/-- Compatibility with the internal shift of bigraded dg modules: for a bigraded dg module `M`,
the image of `M⟨s⟩` in `H(C_A)` is the internal shift of the image of `M`. -/
noncomputable def toCatModuleCompInternalShiftIso (s : ℤ) :
    BigradedDGModuleCat.toCatModule.{w} A ⋙ quotient _ ⋙ internalShift A s ≅
      BigradedDGModuleCat.internalShiftFunctor s ⋙ BigradedDGModuleCat.toCatModule A ⋙
        quotient _ :=
  Functor.isoWhiskerLeft _ (quotientCompInternalShiftIso A s) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (BigradedDGModuleCat.internalShiftToCatModuleIso s).symm _ ≪≫
    Functor.associator _ _ _

end HomotopyCategory

/-! ### The internal shift on the derived category -/

namespace DerivedCategory

variable [HasDerivedCategory.{w', w} (WeightCategory A)]

/-- The internal shift `⟨s⟩` on the derived category `D(C_A)` of bigraded dg modules:
restriction along the shift `k ↦ k + s` of the objects of `C_A`. -/
noncomputable def internalShift (s : ℤ) :
    DerivedCategory.{w', w} (WeightCategory A) ⥤ DerivedCategory.{w', w} (WeightCategory A) :=
  restrict (shiftFunctor A s)

/-- The internal shift commutes with the homological shift. -/
noncomputable instance (s : ℤ) : (internalShift.{w', w} A s).CommShift ℤ :=
  inferInstanceAs ((restrict (shiftFunctor A s)).CommShift ℤ)

/-- The internal shift is a triangulated functor. -/
instance (s : ℤ) : (internalShift.{w', w} A s).IsTriangulated :=
  inferInstanceAs (restrict (shiftFunctor A s)).IsTriangulated

/-- `M⟨0⟩ ≅ M`. -/
noncomputable def internalShiftZeroIso : internalShift.{w', w} A 0 ≅ 𝟭 _ :=
  restrictNatIso (shiftFunctorZeroIso A) (fun _ => mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => d_eq_zero_of_val_eq_one _ rfl) (fun _ => mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => d_eq_zero_of_val_eq_one _ rfl) ≪≫ restrictIdIso _

/-- `M⟨s + t⟩ ≅ M⟨s⟩⟨t⟩`. -/
noncomputable def internalShiftAddIso (s t : ℤ) :
    internalShift.{w', w} A (s + t) ≅ internalShift A s ⋙ internalShift A t :=
  restrictNatIso (shiftFunctorAddIso A s t) (fun _ => mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => d_eq_zero_of_val_eq_one _ rfl) (fun _ => mem_grading_zero_of_val_eq_one _ rfl)
    (fun _ => d_eq_zero_of_val_eq_one _ rfl) ≪≫ restrictCompIso _ _

/-- The internal shifts form an action of `ℤ` on `D(C_A)` by triangulated functors. -/
noncomputable def internalShiftAction :
    TriangulatedIntAction (DerivedCategory.{w', w} (WeightCategory A)) where
  functor := internalShift A
  zeroIso := internalShiftZeroIso A
  addIso := internalShiftAddIso A

@[simp]
theorem internalShiftAction_functor (s : ℤ) :
    (internalShiftAction.{w', w} A).functor s = internalShift A s := rfl

/-- The internal shift `⟨s⟩` is a triangulated autoequivalence of `D(C_A)`, with inverse
`⟨-s⟩`. -/
noncomputable def internalShiftEquiv (s : ℤ) :
    DerivedCategory.{w', w} (WeightCategory A) ≌ DerivedCategory.{w', w} (WeightCategory A) :=
  (internalShiftAction A).equivalence s

@[simp]
theorem internalShiftEquiv_functor (s : ℤ) :
    (internalShiftEquiv.{w', w} A s).functor = internalShift A s := rfl

@[simp]
theorem internalShiftEquiv_inverse (s : ℤ) :
    (internalShiftEquiv.{w', w} A s).inverse = internalShift A (-s) := rfl

/-- The internal shift commutes with the homological shifts: `M⟨s⟩⟦n⟧ ≅ M⟦n⟧⟨s⟩`. -/
noncomputable def internalShiftShiftIso (s n : ℤ) (M : DerivedCategory.{w', w} (WeightCategory A)) :
    (internalShift A s).obj (M⟦n⟧) ≅ ((internalShift A s).obj M)⟦n⟧ :=
  ((internalShift A s).commShiftIso n).app M

/-- The internal shift on `D(C_A)` is induced by the internal shift on `H(C_A)`. -/
noncomputable def QhCompInternalShiftIso (s : ℤ) :
    Qh ⋙ internalShift.{w', w} A s ≅ HomotopyCategory.internalShift A s ⋙ Qh :=
  QhCompRestrictIso _

/-- The internal shift on `D(C_A)` is induced by restriction along `k ↦ k + s` on dg
modules. -/
noncomputable def QCompInternalShiftIso (s : ℤ) :
    Q ⋙ internalShift.{w', w} A s ≅ CatModule.precomp (shiftFunctor A s) ⋙ Q :=
  QCompRestrictIso _

/-- Compatibility with the internal shift of bigraded dg modules: for a bigraded dg module `M`,
the image of `M⟨s⟩` in `D(C_A)` is the internal shift of the image of `M`. -/
noncomputable def toCatModuleCompInternalShiftIso (s : ℤ) :
    BigradedDGModuleCat.toCatModule.{w} A ⋙ Q ⋙ internalShift.{w', w} A s ≅
      BigradedDGModuleCat.internalShiftFunctor s ⋙ BigradedDGModuleCat.toCatModule A ⋙ Q :=
  Functor.isoWhiskerLeft _ (QCompInternalShiftIso A s) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (BigradedDGModuleCat.internalShiftToCatModuleIso s).symm _ ≪≫
    Functor.associator _ _ _

/-- The internal shift preserves and reflects compact objects of `D(C_A)`. -/
theorem isCompact_internalShift_obj_iff (s : ℤ) (M : DerivedCategory.{w', w} (WeightCategory A)) :
    IsCompact.{w} ((internalShift A s).obj M) ↔ IsCompact.{w} M :=
  (internalShiftAction A).isCompact_functor_obj_iff s M

end DerivedCategory

/-! ### Grothendieck groups as `ℤ[q, q⁻¹]`-modules -/

namespace HomotopyCategory

/-- `K₀(H(C_A))` is a `ℤ[q, q⁻¹]`-module, with `qⁿ • [M] = [M⟨n⟩]`. -/
noncomputable instance :
    Module (LaurentPolynomial ℤ) (K0 (HomotopyCategory.{w} (WeightCategory A))) :=
  (internalShiftAction A).K0Module

/-- `qⁿ • [M] = [M⟨n⟩]` in `K₀(H(C_A))`. -/
theorem T_smul_mk (n : ℤ) (M : HomotopyCategory.{w} (WeightCategory A)) :
    (LaurentPolynomial.T n : LaurentPolynomial ℤ) • K0.mk M = K0.mk ((internalShift A n).obj M) :=
  (internalShiftAction A).T_smul_mk n M

end HomotopyCategory

namespace DerivedCategory

variable [HasDerivedCategory.{w', w} (WeightCategory A)]

/-- `K₀(D(C_A))` is a `ℤ[q, q⁻¹]`-module, with `qⁿ • [M] = [M⟨n⟩]`. -/
noncomputable instance :
    Module (LaurentPolynomial ℤ) (K0 (DerivedCategory.{w', w} (WeightCategory A))) :=
  (internalShiftAction A).K0Module

/-- `qⁿ • [M] = [M⟨n⟩]` in `K₀(D(C_A))`. -/
theorem T_smul_mk (n : ℤ) (M : DerivedCategory.{w', w} (WeightCategory A)) :
    (LaurentPolynomial.T n : LaurentPolynomial ℤ) • K0.mk M = K0.mk ((internalShift A n).obj M) :=
  (internalShiftAction A).T_smul_mk n M

/-- The internal shifts restricted to the compact objects `D(C_A)^c` of `D(C_A)`. -/
noncomputable def compactInternalShiftAction :
    TriangulatedIntAction
      (compactSubcategory.{w} (DerivedCategory.{w', w} (WeightCategory A))).FullSubcategory :=
  (internalShiftAction A).compact

/-- `K₀(D(C_A)^c)` is a `ℤ[q, q⁻¹]`-module, with `qⁿ • [M] = [M⟨n⟩]`. -/
noncomputable instance :
    Module (LaurentPolynomial ℤ)
      (K0 (compactSubcategory.{w} (DerivedCategory.{w', w} (WeightCategory A))).FullSubcategory) :=
  (compactInternalShiftAction A).K0Module

/-- `qⁿ • [M] = [M⟨n⟩]` in `K₀(D(C_A)^c)`. -/
theorem T_smul_mk_compact (n : ℤ)
    (M : (compactSubcategory.{w} (DerivedCategory.{w', w} (WeightCategory A))).FullSubcategory) :
    (LaurentPolynomial.T n : LaurentPolynomial ℤ) • K0.mk M =
      K0.mk (((compactInternalShiftAction A).functor n).obj M) :=
  (compactInternalShiftAction A).T_smul_mk n M

end DerivedCategory

end CatModule

end DG
