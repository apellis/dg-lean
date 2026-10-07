import DG.Positive.ScalarExtensionModule
import DG.K0.ExtendScalars

/-!
# Derived base change along `ℤ → K`

For a commutative ring `K` and a dg ring `A`, derived induction along `unitHom : A → K ⊗ A`
(`DG.DGRingHom.derivedInduction`) is computed on K-projective dg modules by the base change
`K ⊗_ℤ -` (`DG.ExtendScalars.baseChange`):

* `DG.ExtendScalars.derivedInductionObjIso`: `unitHom^*(P) ≅ K ⊗_ℤ P` in `D(K ⊗ A)` for a
  K-projective dg `A`-module `P`;
* `DG.ExtendScalars.K0_map_mk`: if moreover `P` is compact in `D(A)`, then `K ⊗_ℤ P` is compact in
  `D(K ⊗ A)` and `K₀(unitHom) [P] = [K ⊗_ℤ P]`.
-/

open CategoryTheory

universe w₁ w₂ w₃ w₄ u

noncomputable section

namespace DG

namespace ExtendScalars

variable {K : Type u} [CommRing K] {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  {P : DGModuleCat.{u} A} (hP : IsKProjective.{u} A P)

section Derived

variable [CatModule.HasDerivedCategory.{w₁, u} (SingleObj A)]
  [CatModule.HasDerivedCategory.{w₂, u} (SingleObj (ExtendScalars K A))]
  [DG.HasDerivedCategory.{w₃, u} A] [DG.HasDerivedCategory.{w₄, u} (ExtendScalars K A)]

variable (K) in
/-- **Derived base change of a K-projective module**: `unitHom^*(P) ≅ K ⊗_ℤ P` in `D(K ⊗ A)`. -/
def derivedInductionObjIso :
    (unitHom K A).derivedInduction.{w₁, w₂, w₃, w₄}.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((baseChange K A).obj P) :=
  (unitHom K A).derivedInductionObjIso hP ≪≫
    DerivedCategory.Q.mapIso ((extendScalarsIso K A).app P)

end Derived

variable [HasDerivedCategory.{w₁, u} A] [HasDerivedCategory.{w₂, u} (ExtendScalars K A)]
  (hc : IsCompact.{u} (DerivedCategory.Q.obj P))

variable (K) in
include hP hc in
/-- Base change of a K-projective dg module compact in `D(A)` is compact in `D(K ⊗ A)`. -/
theorem isCompact_Q_baseChange_obj :
    IsCompact.{u} (DerivedCategory.Q.obj ((baseChange K A).obj P)) :=
  ((unitHom K A).isCompact_Q_extendScalars_obj hP hc).of_iso
    (DerivedCategory.Q.mapIso ((extendScalarsIso K A).app P)).symm

variable (K) in
include hP in
/-- **`K₀` of base change**: for a K-projective dg `A`-module `P` compact in `D(A)`,
`K₀(unitHom) [P] = [K ⊗_ℤ P]` in `K₀(K ⊗ A)`. -/
theorem K0_map_mk :
    DGRing.K0.map (unitHom K A) (DG.K0.mk (⟨DerivedCategory.Q.obj P, hc⟩ :
        PerfectDerivedCategory A)) =
      DG.K0.mk (⟨DerivedCategory.Q.obj ((baseChange K A).obj P),
        isCompact_Q_baseChange_obj K hP hc⟩ : PerfectDerivedCategory (ExtendScalars K A)) := by
  rw [DGRing.K0.map_mk_of_isKProjective (unitHom K A) hP hc]
  exact DG.K0.mk_eq_of_iso_obj (DerivedCategory.Q.mapIso ((extendScalarsIso K A).app P))

end ExtendScalars

end DG

end
