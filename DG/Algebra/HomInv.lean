import DG.Algebra.Hom
import DG.Algebra.AddEquiv

/-!
# The inverse of a bijective morphism of dg rings

`DG.DGRingHom.invOfBijective f hf`: the inverse of a bijective morphism of dg rings
`f : R →ᵈᵍ+* S`, again a morphism of dg rings (`DG.DGRingHom.apply_invOfBijective`,
`DG.DGRingHom.invOfBijective_apply`).
-/

noncomputable section

namespace DG

namespace DGRingHom

section Inv

variable {R S : Type*} [Ring R] [DGAddCommGroup R] [Ring S] [DGAddCommGroup S] (f : R →ᵈᵍ+* S)
  (hf : Function.Bijective f)

/-- The inverse of a bijective morphism of dg rings. -/
def invOfBijective : S →ᵈᵍ+* R where
  toFun := Function.surjInv hf.2
  map_one' := hf.1 (by rw [Function.surjInv_eq hf.2, map_one])
  map_mul' x y := hf.1 (by rw [Function.surjInv_eq hf.2, map_mul, Function.surjInv_eq hf.2, Function.surjInv_eq hf.2])
  map_zero' := hf.1 (by rw [Function.surjInv_eq hf.2, map_zero])
  map_add' x y := hf.1 (by rw [Function.surjInv_eq hf.2, map_add, Function.surjInv_eq hf.2, Function.surjInv_eq hf.2])
  map_mem' {n x} hx := mem_grading_of_injective f.toRingHom.toAddMonoidHom (fun h => f.map_mem h) hf.1
    (by change f (Function.surjInv hf.2 x) ∈ _; rwa [Function.surjInv_eq hf.2])
  map_d' x := hf.1 (by rw [Function.surjInv_eq hf.2, f.map_d, Function.surjInv_eq hf.2])

theorem apply_invOfBijective (x : S) : f (invOfBijective f hf x) = x := Function.surjInv_eq hf.2 x

theorem invOfBijective_apply (a : R) : invOfBijective f hf (f a) = a := hf.1 (apply_invOfBijective f hf _)

end Inv

end DGRingHom

end DG
