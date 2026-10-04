import DG.HalfGraded.Hom
import DG.HalfGraded.SuperK0Linear

/-!
# Quasi-isomorphisms of half-graded dg rings

A morphism `f : H → H'` of half-graded dg rings (same parameter `k`) induces, for every weight
`w`, a map of dg abelian groups between the weight-`w` components of the regraded rings
(`DG.HalfGradedDGRing.Hom.weightComponentMap`); these are the Hom complexes of the weight dg
categories. Call `f` a *quasi-isomorphism* if all these maps are quasi-isomorphisms
(`DG.HalfGradedDGRing.Hom.IsQuasiIso`). Then:

* the weight dg functor `C_H ⥤ C_{H'}` is a quasi-equivalence
  (`DG.HalfGradedDGRing.Hom.isQuasiEquivalence_weightFunctor`; it is the identity on objects);
* the induced `ℤ[q, q⁻¹]`-linear map `K₀(C_H) → K₀(C_{H'})` is an isomorphism
  (`DG.HalfGradedDGRing.Hom.K0LinearEquiv`), and so is the map on the compact super
  Grothendieck groups (`DG.HalfGradedDGRing.Hom.superK0cLinearEquiv`).
-/

open CategoryTheory

universe w u

noncomputable section

namespace DG

namespace HalfGradedDGRing

namespace Hom

variable {A A' : Type u} [Ring A] [Ring A'] {k : ℤ} {H : HalfGradedDGRing A k}
  {H' : HalfGradedDGRing A' k}

/-- The map of weight-`w` components of the regraded rings. -/
def weightComponentMap (f : Hom H H') (w : ℤ) :
    wgrading (M := H.Regraded) w →+ wgrading (M := H'.Regraded) w where
  toFun x := ⟨f.regraded x.1, f.regraded_mem_wgrading x.2⟩
  map_zero' := Subtype.ext (map_zero f.regraded)
  map_add' x y := Subtype.ext (map_add f.regraded x.1 y.1)

/-- A morphism of half-graded dg rings is a *quasi-isomorphism* if it induces bijections on the
cohomology of all weight components of the regraded rings. -/
def IsQuasiIso (f : Hom H H') : Prop :=
  ∀ w n : ℤ, Function.Bijective (cohomology.mapAddMonoidHom (f.weightComponentMap w)
    (fun hm => f.regraded.map_mem hm) (fun m => Subtype.ext (f.regraded.map_d m.1)) n)

/-- The weight dg functor of a quasi-isomorphism is a quasi-equivalence. -/
theorem isQuasiEquivalence_weightFunctor {f : Hom H H'} (hf : f.IsQuasiIso) :
    IsQuasiEquivalence f.weightFunctor where
  bijective_cohomology X X' n := hf (X'.as - X.as) n
  exists_iso Y := ⟨⟨Y.as⟩, 𝟙 Y, 𝟙 Y, id_mem_cocycles Y, id_mem_cocycles Y,
    by
      change (𝟙 Y ≫ 𝟙 Y - 𝟙 Y : Y ⟶ Y) ∈ coboundaries (Y ⟶ Y) 0
      rw [Category.id_comp, sub_self]; exact zero_mem _,
    by
      change (𝟙 Y ≫ 𝟙 Y - 𝟙 Y : Y ⟶ Y) ∈ coboundaries (Y ⟶ Y) 0
      rw [Category.id_comp, sub_self]; exact zero_mem _⟩

variable [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory H.Regraded)]
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory H'.Regraded)]

/-- **A quasi-isomorphism of half-graded dg rings induces `K₀(C_H) ≃ K₀(C_{H'})`**, linearly
over `ℤ[q, q⁻¹]`. -/
def K0LinearEquiv (f : Hom H H') (hf : f.IsQuasiIso) :
    DGCategory.K0.{max u w, max u w} (WeightCategory H.Regraded) ≃ₗ[LaurentPolynomial ℤ]
      DGCategory.K0.{max u w, max u w} (WeightCategory H'.Regraded) :=
  LinearEquiv.ofBijective f.K0Map
    (DGCategory.K0.mapEquivOfIsQuasiEquivalence f.weightFunctor
      (isQuasiEquivalence_weightFunctor hf)).bijective

@[simp]
theorem K0LinearEquiv_apply (f : Hom H H') (hf : f.IsQuasiIso)
    (x : DGCategory.K0.{max u w, max u w} (WeightCategory H.Regraded)) :
    K0LinearEquiv f hf x = f.K0Map x := rfl

/-- **A quasi-isomorphism induces an isomorphism of compact super Grothendieck groups.** -/
def superK0cLinearEquiv (f : Hom H H') (hf : f.IsQuasiIso) :
    SuperK0c.{max u w, w} H ≃ₗ[LaurentPolynomial ℤ] SuperK0c.{max u w, w} H' where
  __ := superK0cMap H H' (K0LinearEquiv f hf).toLinearMap
  invFun := superK0cMap H' H (K0LinearEquiv f hf).symm.toLinearMap
  left_inv s := by
    obtain ⟨x, rfl⟩ := superK0cMk_surjective H s
    change superK0cMap H' H _ (superK0cMap H H' _ (superK0cMk H x)) = _
    rw [superK0cMap_mk, superK0cMap_mk, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  right_inv s := by
    obtain ⟨x, rfl⟩ := superK0cMk_surjective H' s
    change superK0cMap H H' _ (superK0cMap H' H _ (superK0cMk H' x)) = _
    rw [superK0cMap_mk, superK0cMap_mk, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

theorem superK0cLinearEquiv_superK0cMk (f : Hom H H') (hf : f.IsQuasiIso)
    (x : DGCategory.K0.{max u w, max u w} (WeightCategory H.Regraded)) :
    superK0cLinearEquiv f hf (superK0cMk H x) = superK0cMk H' (f.K0Map x) :=
  superK0cMap_mk H H' _ x

end Hom

end HalfGradedDGRing

end DG
