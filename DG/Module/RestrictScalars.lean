import DG.Algebra.Hom
import DG.Module.Right

/-!
# Restriction of scalars for dg bimodules

For a morphism of dg rings `φ : A →ᵈᵍ+* B` and a dg `(B, C)`-bimodule `M`, the restriction
`DG.RestrictScalars φ M` keeps the right action of `C`: it is a right dg `C`-module
(`DG.RestrictScalars.dgRightModule`) and a dg `(A, C)`-bimodule (`DG.RestrictScalars.dgBimodule`).
-/

noncomputable section

open MulOpposite

namespace DG

namespace RestrictScalars

/-! ### Restriction of the left action of a dg bimodule -/

section Restrict

variable {A B C : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B] [Ring C]
  [DGAddCommGroup C] (φ : A →ᵈᵍ+* B) (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module B M]
  [Module Cᵐᵒᵖ M]

instance moduleOp : Module Cᵐᵒᵖ (RestrictScalars φ M) := inferInstanceAs (Module Cᵐᵒᵖ M)

instance dgRightModule [DGRightModule C M] : DGRightModule C (RestrictScalars φ M) :=
  inferInstanceAs (DGRightModule C M)

instance smulCommClass [SMulCommClass B Cᵐᵒᵖ M] :
    SMulCommClass A Cᵐᵒᵖ (RestrictScalars φ M) where
  smul_comm a c m := smul_comm (φ a) c (show M from m)

/-- Restricting the left action of a dg `(B, C)`-bimodule along `φ : A →ᵈᵍ+* B`. -/
instance dgBimodule [DGBimodule B C M] : DGBimodule A C (RestrictScalars φ M) :=
  DGBimodule.mk'

end Restrict

end RestrictScalars

end DG
