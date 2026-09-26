import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import DG.Homotopy.Pretriangulated

/-!
# The forgetful functor on homotopy categories is triangulated

Let `A` be a dg `R`-algebra. The forgetful functor
`DG.DGModuleCat.forget R A : DGModuleCat A ⥤ CochainComplex (ModuleCat R) ℤ` sends homotopic
morphisms to homotopic morphisms, hence induces a functor
`DG.HomotopyCategory.forget R A : DG.HomotopyCategory A ⥤ HomotopyCategory (ModuleCat R) (up ℤ)`
to Mathlib's homotopy category of cochain complexes. This file shows that it is a triangulated
functor, and deduces that the cohomology functors on `DG.HomotopyCategory A` are homological.

## Main definitions and results

* `DG.Cochain.toHomComplex R z`: a cochain `z` of the Hom complex `HOM_A(M, N)` as a cochain of
  Mathlib's Hom complex of the underlying complexes (`CochainComplex.HomComplex.Cochain`),
  compatible with sums, composition (`DG.Cochain.toHomComplex_comp`), morphisms
  (`DG.Cochain.toHomComplex_ofHom`) and the differentials (`DG.Cochain.toHomComplex_δ`).
* `DG.DGHomotopy.toHomotopy`: a homotopy of dg modules gives a homotopy of the underlying
  complexes.
* `DG.Cone.forgetIso R φ`: the underlying complex of `Cone φ` is Mathlib's
  `CochainComplex.mappingCone` of the underlying morphism (in degree `i` both are
  `Mⁱ⁺¹ ⊕ Nⁱ`); it is built with Mathlib's `mappingCone.lift` and `mappingCone.desc` from the
  cochains `fst`, `snd`, `inl`, `inr` of `DG.Homotopy.ConeCochain`, whose signs agree with
  Mathlib's. `DG.Cone.forgetTriangleIso R φ` upgrades it to an isomorphism between the image of
  the standard triangle `DG.Cone.triangle φ` and Mathlib's `mappingCone.triangle`; this is where
  the compatibility of the forgetful functor with the shift (`DG.DGModuleCat.forgetCommShift`)
  enters.
* `DG.HomotopyCategory.forget R A`, with `DG.HomotopyCategory.forgetCommShift` and
  `DG.HomotopyCategory.forget_isTriangulated`: a triangulated functor.
* `DG.HomotopyCategory.homologyFunctor R A n = forget R A ⋙ HomotopyCategory.homologyFunctor _ _
  n`, the `n`-th cohomology of the underlying complex, and
  `DG.HomotopyCategory.homologyFunctor_isHomological`: it is a homological functor (in
  particular for `n = 0`), by Mathlib's `HomotopyCategory.homologyFunctor` being homological.
-/

open CategoryTheory Category Limits Pretriangulated

universe v u w

namespace DG

open DGModuleCat DGModuleCat.Algebra

variable (R : Type w) {A : Type u} [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]

private theorem ModuleCat.units_smul_apply {X Y : ModuleCat.{v} R} (k : ℤˣ) (φ : X ⟶ Y) (x : X) :
    (k • φ).hom x = k • φ.hom x := rfl

private theorem Submodule.coe_units_smul {X : Type*} [AddCommGroup X] [Module R X]
    (S : Submodule R X) (k : ℤˣ) (x : S) : ((k • x : S) : X) = k • (x : X) := rfl

theorem DGModuleCat.forget_obj_d_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i + 1 = j)
    (x : DGModule.gradingSubmodule R A M i) :
    ((((forget R A).obj M).d i j).hom x).1 = d (x : M) :=
  toComplex_d_apply R M h x

theorem DGModuleCat.forget_obj_XIsoOfEq_inv_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i = j)
    (x : DGModule.gradingSubmodule R A M j) :
    ((((forget R A).obj M).XIsoOfEq h).inv.hom x).1 = x.1 := by
  subst h
  rfl

/-! ### Cochains of the Hom complex as cochains of the underlying complexes -/

namespace Cochain

variable {M N P : DGModuleCat.{v} A} {n : ℤ}

/-- A cochain of degree `n` restricted to the homogeneous components `Mᵖ → N^q`, `p + n = q`,
as an `R`-linear map. -/
def restrict (z : Cochain A M N n) (p q : ℤ) (hpq : p + n = q) :
    DGModule.gradingSubmodule R A M p →ₗ[R] DGModule.gradingSubmodule R A N q where
  toFun x := ⟨z x.1, hpq ▸ z.map_mem x.2⟩
  map_add' x y := Subtype.ext (map_add z x.1 y.1)
  map_smul' r x := Subtype.ext (by
    change z (algebraMap R A r • x.1) = algebraMap R A r • z x.1
    rw [z.map_smul (algebraMap_mem_grading R r), mul_zero, koszulSign_zero, one_smul])

/-- A cochain of the Hom complex `HOM_A(M, N)` as a cochain of Mathlib's Hom complex of the
underlying cochain complexes of `R`-modules. -/
def toHomComplex (z : Cochain A M N n) :
    CochainComplex.HomComplex.Cochain ((forget R A).obj M) ((forget R A).obj N) n :=
  CochainComplex.HomComplex.Cochain.mk fun p q hpq => ModuleCat.ofHom (z.restrict R p q hpq)

@[simp]
theorem toHomComplex_v_apply (z : Cochain A M N n) (p q : ℤ) (hpq : p + n = q)
    (x : DGModule.gradingSubmodule R A M p) :
    (((z.toHomComplex R).v p q hpq).hom x).1 = z x.1 := rfl

theorem toHomComplex_ext {z₁ z₂ : CochainComplex.HomComplex.Cochain ((forget R A).obj M)
      ((forget R A).obj N) n}
    (h : ∀ p q hpq (x : DGModule.gradingSubmodule R A M p),
      ((z₁.v p q hpq).hom x).1 = ((z₂.v p q hpq).hom x).1) : z₁ = z₂ :=
  CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq =>
    ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (h p q hpq x))

@[simp]
theorem toHomComplex_add (z₁ z₂ : Cochain A M N n) :
    (z₁ + z₂).toHomComplex R = z₁.toHomComplex R + z₂.toHomComplex R :=
  toHomComplex_ext R fun _ _ _ _ => rfl

@[simp]
theorem toHomComplex_neg (z : Cochain A M N n) :
    (-z).toHomComplex R = -z.toHomComplex R :=
  toHomComplex_ext R fun _ _ _ _ => rfl

@[simp]
theorem toHomComplex_zero : (0 : Cochain A M N n).toHomComplex R = 0 :=
  toHomComplex_ext R fun _ _ _ _ => rfl

@[simp]
theorem toHomComplex_ofHom (f : M ⟶ N) :
    (ofHom f.hom).toHomComplex R =
      CochainComplex.HomComplex.Cochain.ofHom ((forget R A).map f) :=
  toHomComplex_ext R fun p q hpq x => by
    obtain rfl : q = p := by omega
    rw [CochainComplex.HomComplex.Cochain.ofHom_v]
    rfl

@[simp]
theorem toHomComplex_comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain A N P n₂) (z₁ : Cochain A M N n₁)
    (h : n₁ + n₂ = n₁₂) :
    (z₂.comp z₁ h).toHomComplex R = (z₁.toHomComplex R).comp (z₂.toHomComplex R) h :=
  toHomComplex_ext R fun p q hpq x => by
    rw [CochainComplex.HomComplex.Cochain.comp_v _ _ h p (p + n₁) q rfl (by omega)]
    rfl

theorem toHomComplex_δ (m : ℤ) (z : Cochain A M N n) :
    (δ n m z).toHomComplex R = CochainComplex.HomComplex.δ n m (z.toHomComplex R) := by
  by_cases hnm : n + 1 = m
  · refine toHomComplex_ext R fun p q hpq x => ?_
    rw [CochainComplex.HomComplex.δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl]
    simp only [ModuleCat.hom_add, LinearMap.add_apply, Submodule.coe_add, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.units_smul_apply, toHomComplex_v_apply, forget_obj_d_apply,
      Submodule.coe_units_smul]
    rw [δ_apply' n m hnm]
    erw [Submodule.coe_add, Submodule.coe_units_smul, forget_obj_d_apply, toHomComplex_v_apply,
      toHomComplex_v_apply, forget_obj_d_apply]
    all_goals omega
  · rw [δ_shape _ _ hnm, CochainComplex.HomComplex.δ_shape _ _ hnm, toHomComplex_zero]

end Cochain

/-! ### Homotopies -/

/-- A homotopy between morphisms of dg modules gives a homotopy between the underlying morphisms
of cochain complexes. -/
noncomputable def DGHomotopy.toHomotopy {M N : DGModuleCat.{v} A} {f g : M ⟶ N}
    (h : DGHomotopy f.hom g.hom) : Homotopy ((forget R A).map f) ((forget R A).map g) :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm ⟨h.hom.toHomComplex R, by
    rw [← Cochain.toHomComplex_ofHom, ← Cochain.toHomComplex_ofHom, ← Cochain.toHomComplex_δ,
      h.ofHom_eq, Cochain.toHomComplex_add]⟩

/-! ### The mapping cone -/

namespace Cone

variable {M N : DGModuleCat.{v} A} (φ : M ⟶ N)

theorem forgetIso_inv_eq :
    CochainComplex.HomComplex.δ (-1) 0
        ((inl φ.hom).toHomComplex (M := M) (N := of A (Cone φ.hom)) R) =
      CochainComplex.HomComplex.Cochain.ofHom
        ((forget R A).map φ ≫ (forget R A).map (ofHom (inr φ.hom))) := by
  rw [← Cochain.toHomComplex_δ, δ_inl, ← Functor.map_comp, ← Cochain.toHomComplex_ofHom]
  rfl

/-- The underlying cochain complex of the mapping cone of `φ` is Mathlib's mapping cone of the
underlying morphism of cochain complexes: in degree `i` both are `Mⁱ⁺¹ ⊕ Nⁱ`, with the same
differential. -/
noncomputable def forgetIso :
    (forget R A).obj (of A (Cone φ.hom)) ≅ CochainComplex.mappingCone ((forget R A).map φ) where
  hom := CochainComplex.mappingCone.lift _
    (CochainComplex.HomComplex.Cocycle.mk
      ((fst φ.hom).1.toHomComplex (M := of A (Cone φ.hom)) (N := M) R) 2 (by norm_num) (by
        rw [← Cochain.toHomComplex_δ, Cocycle.δ_eq_zero, Cochain.toHomComplex_zero]))
    ((snd φ.hom).toHomComplex (M := of A (Cone φ.hom)) (N := N) R) (by
      rw [← Cochain.toHomComplex_δ, δ_snd]
      change Cochain.toHomComplex R (M := of A (Cone φ.hom)) (N := N)
          (-(Cochain.ofHom φ.hom).comp (fst φ.hom).1 (add_zero 1)) + _ = 0
      rw [Cochain.toHomComplex_neg, Cochain.toHomComplex_comp, Cochain.toHomComplex_ofHom]
      exact neg_add_cancel _)
  inv := CochainComplex.mappingCone.desc _
    ((inl φ.hom).toHomComplex (M := M) (N := of A (Cone φ.hom)) R)
    ((forget R A).map (ofHom (inr φ.hom))) (forgetIso_inv_eq R φ)
  hom_inv_id := by
    ext n : 1
    rw [HomologicalComplex.comp_f,
      CochainComplex.mappingCone.lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
    erw [Submodule.coe_add]
    exact id_X (f := φ.hom) x.1
  inv_hom_id := by
    ext n : 1
    refine CochainComplex.mappingCone.ext_from _ (n + 1) n rfl ?_ ?_ <;>
      refine CochainComplex.mappingCone.ext_to _ n (n + 1) rfl ?_ ?_ <;>
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, comp_id, assoc,
        CochainComplex.mappingCone.lift_f_fst_v, CochainComplex.mappingCone.lift_f_snd_v,
        CochainComplex.mappingCone.inl_v_desc_f_assoc,
        CochainComplex.mappingCone.inr_f_desc_f_assoc, CochainComplex.mappingCone.inl_v_fst_v,
        CochainComplex.mappingCone.inl_v_snd_v, CochainComplex.mappingCone.inr_f_fst_v,
        CochainComplex.mappingCone.inr_f_snd_v] <;>
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl)

theorem inr_forgetIso_inv :
    CochainComplex.mappingCone.inr ((forget R A).map φ) ≫ (forgetIso R φ).inv =
      (forget R A).map (ofHom (inr φ.hom)) :=
  CochainComplex.mappingCone.inr_desc _ _ _ (forgetIso_inv_eq R φ)

theorem inl_v_forgetIso_inv_f (p q : ℤ) (h : p + (-1) = q) :
    (CochainComplex.mappingCone.inl ((forget R A).map φ)).v p q h ≫ (forgetIso R φ).inv.f q =
      ((inl φ.hom).toHomComplex (M := M) (N := of A (Cone φ.hom)) R).v p q h :=
  CochainComplex.mappingCone.inl_v_desc_f _ _ _ (forgetIso_inv_eq R φ) p q h

theorem inr_f_forgetIso_inv_f (p : ℤ) :
    (CochainComplex.mappingCone.inr ((forget R A).map φ)).f p ≫ (forgetIso R φ).inv.f p =
      ((forget R A).map (ofHom (inr φ.hom))).f p :=
  CochainComplex.mappingCone.inr_f_desc_f _ _ _ (forgetIso_inv_eq R φ) p

/-- The image of the standard triangle of `φ` under the forgetful functor is Mathlib's standard
triangle of the underlying morphism of cochain complexes. -/
noncomputable def forgetTriangleIso :
    (forget R A).mapTriangle.obj (triangle φ) ≅
      CochainComplex.mappingCone.triangle ((forget R A).map φ) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (forgetIso R φ) (by simp) ?_ ?_
  · rw [Iso.refl_hom, id_comp, ← cancel_mono (forgetIso R φ).inv, assoc, Iso.hom_inv_id,
      comp_id]
    exact (inr_forgetIso_inv R φ).symm
  · rw [Iso.refl_hom, CategoryTheory.Functor.map_id, comp_id, ← cancel_epi (forgetIso R φ).inv,
      Iso.inv_hom_id_assoc]
    ext n : 1
    refine CochainComplex.mappingCone.ext_from _ (n + 1) n rfl ?_ ?_
    · rw [CochainComplex.mappingCone.inl_v_triangle_mor₃_f, HomologicalComplex.comp_f,
        ← assoc, inl_v_forgetIso_inv_f]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
      simp only [CochainComplex.shiftFunctorObjXIso]
      erw [ModuleCat.hom_neg, LinearMap.neg_apply, Submodule.coe_neg]
    · rw [CochainComplex.mappingCone.inr_f_triangle_mor₃_f, HomologicalComplex.comp_f,
        ← assoc, inr_f_forgetIso_inv_f]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
      exact (neg_zero : -(0 : (M : Type v)) = 0)

end Cone

/-! ### The forgetful functor on homotopy categories -/

namespace HomotopyCategory

variable (A)

/-- The forgetful functor from the homotopy category of dg `A`-modules to Mathlib's homotopy
category of cochain complexes of `R`-modules, induced by `DG.DGModuleCat.forget R A`. -/
noncomputable def forget :
    HomotopyCategory.{v} A ⥤ _root_.HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _
    (DGModuleCat.forget R A ⋙ _root_.HomotopyCategory.quotient _ _)
    (fun _ _ _ _ h => _root_.HomotopyCategory.eq_of_homotopy _ _ (h.some.toHomotopy R))

/-- The forgetful functor on homotopy categories is induced by the forgetful functor on dg
modules. -/
noncomputable def forgetFactors :
    quotient A ⋙ forget R A ≅
      DGModuleCat.forget R A ⋙ _root_.HomotopyCategory.quotient _ _ :=
  CategoryTheory.Quotient.lift.isLift _ _ _

variable {A}

@[simp]
theorem forget_map_quotient_map {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    (forget R A).map ((quotient A).map f) =
      (_root_.HomotopyCategory.quotient _ _).map ((DGModuleCat.forget R A).map f) :=
  rfl

variable (A)

instance : (forget R A).Additive := by
  have := Functor.additive_of_iso (forgetFactors R A).symm
  exact Functor.additive_of_full_essSurj_comp (quotient A) _

/-- The forgetful functor on homotopy categories commutes with the shifts. -/
noncomputable instance forgetCommShift : (forget R A).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift _ _ _ _

instance : NatTrans.CommShift (forgetFactors R A).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility _ _ _ _

variable {A}

/-- The image of the standard triangle `triangleh φ` under the forgetful functor is Mathlib's
standard triangle of the underlying morphism of cochain complexes (compare Mathlib's
`CochainComplex.mappingCone.mapTrianglehIso`). -/
noncomputable def mapTrianglehIso {M N : DGModuleCat.{v} A} (φ : M ⟶ N) :
    (forget R A).mapTriangle.obj (Cone.triangleh φ) ≅
      CochainComplex.mappingCone.triangleh ((DGModuleCat.forget R A).map φ) :=
  (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (Functor.mapTriangleIso (forgetFactors R A)).app _ ≪≫
    (Functor.mapTriangleCompIso _ _).app _ ≪≫
    (_root_.HomotopyCategory.quotient _ _).mapTriangle.mapIso (Cone.forgetTriangleIso R φ)

variable (A)

/-- The forgetful functor from the homotopy category of dg modules to the homotopy category of
cochain complexes of `R`-modules is a triangulated functor. -/
instance forget_isTriangulated : (forget R A).IsTriangulated where
  map_distinguished := by
    rintro T ⟨M, N, φ, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(forget R A).mapTriangle.mapIso e ≪≫ mapTrianglehIso R φ⟩⟩

/-- The `n`-th cohomology functor `H(A) ⥤ ModuleCat R`: the cohomology of the underlying
cochain complex, induced by Mathlib's `HomotopyCategory.homologyFunctor`. -/
noncomputable def homologyFunctor (n : ℤ) : HomotopyCategory.{v} A ⥤ ModuleCat.{v} R :=
  forget R A ⋙ _root_.HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n

/-- The cohomology functors on the homotopy category of dg modules are homological. -/
instance homologyFunctor_isHomological (n : ℤ) : (homologyFunctor R A n).IsHomological := by
  dsimp only [homologyFunctor]
  infer_instance

end HomotopyCategory

end DG
