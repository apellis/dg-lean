import DG.Category.Homotopy.Homotopy
import DG.Homotopy.KProjective

/-!
# Acyclic modules and quasi-isomorphisms over a dg category

A dg module `M` over a dg category `C` is *acyclic* if its value `M X` at every object is an
acyclic dg abelian group, and a morphism `φ : M ⟶ N` is a *quasi-isomorphism* if it induces
bijections `Hⁿ(M X) → Hⁿ(N X)` for all objects `X` and degrees `n`.

## Main definitions

* `DG.CatModule.IsAcyclic M`
* `DG.CatModule.IsQuasiIso φ`
-/

open CategoryTheory

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- A dg module over `C` is acyclic if its value at every object is acyclic. -/
def IsAcyclic (M : CatModule.{w} C) : Prop :=
  ∀ X : C, DG.IsAcyclic (M.obj X)

/-- A morphism of dg modules over `C` is a quasi-isomorphism if it induces bijections on the
cohomology of the values at every object. -/
def IsQuasiIso {M N : CatModule.{w} C} (φ : M ⟶ N) : Prop :=
  ∀ (X : C) (n : ℤ), Function.Bijective (cohomologyMap φ X n)

variable {M N P : CatModule.{w} C}

theorem isAcyclic_iff (M : CatModule.{w} C) :
    IsAcyclic M ↔ ∀ (X : C) (n : ℤ), Subsingleton (cohomology (M.obj X) n) :=
  Iff.rfl

theorem isQuasiIso_id (M : CatModule.{w} C) : IsQuasiIso (𝟙 M) := fun X n => by
  rw [cohomologyMap_id]
  exact Function.bijective_id

theorem IsQuasiIso.comp {φ : M ⟶ N} {ψ : N ⟶ P} (hφ : IsQuasiIso φ) (hψ : IsQuasiIso ψ) :
    IsQuasiIso (φ ≫ ψ) := fun X n => by
  have : ⇑(cohomologyMap (φ ≫ ψ) X n) = cohomologyMap ψ X n ∘ cohomologyMap φ X n :=
    funext (cohomologyMap_comp_apply φ ψ X n)
  rw [this]
  exact (hψ X n).comp (hφ X n)

theorem IsQuasiIso.of_isIso (φ : M ⟶ N) [IsIso φ] : IsQuasiIso φ := fun X n => by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨cohomologyMap (inv φ) X n, fun x => ?_, fun y => ?_⟩
  · rw [← cohomologyMap_comp_apply, IsIso.hom_inv_id, cohomologyMap_id, AddMonoidHom.id_apply]
  · rw [← cohomologyMap_comp_apply, IsIso.inv_hom_id, cohomologyMap_id, AddMonoidHom.id_apply]

end CatModule

end DG
