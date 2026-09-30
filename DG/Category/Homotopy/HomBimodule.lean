import DG.Category.Tensor.Hom
import DG.Category.Homotopy.Path
import DG.Category.Homotopy.Shift

set_option backward.isDefEq.respectTransparency false

/-!
# The Hom functor of a dg bimodule: cochains, homotopies, path objects and shifts

Let `B` be a dg `(D, C)`-bimodule and `HOM_D(B, -) : CatModule D ⥤ CatModule C` its Hom functor
(`DG.CatBimodule.homFunctor`), `HOM_D(B, N)(Y) = HOM_D(B(-, Y), N)`. It acts on the cochains of
the Hom complexes by postcomposition (`DG.CatBimodule.homCochain`), compatibly with composition,
identities and the differentials; in particular it preserves homotopies
(`DG.CatModule.DGHomotopy.homMap`). This file also shows:

* `DG.CatBimodule.homPathIso B N : pathObj (HOM_D(B, N)) ≅ HOM_D(B, pathObj N)`, compatible
  with the projections (`DG.CatBimodule.homPathMap_π`): the Hom functor commutes with the path
  object. It is used to show that the tensor–Hom adjunction descends to homotopy classes.
* `DG.CatBimodule.homShiftIso B n N : HOM_D(B, N⟦n⟧) ≅ HOM_D(B, N)⟦n⟧`, given on the degree-`k`
  cochains by `z ↦ z` (a cochain `B(-, Y) → N⟦n⟧` of degree `k` is a cochain `B(-, Y) → N` of
  degree `k + n`, without sign, as for Mathlib's `Cochain.rightShift`), and the resulting
  `CommShift` structure `DG.CatBimodule.homFunctor_commShift` on the Hom functor.
-/

open CategoryTheory

universe w v₁ v₂ u₁ u₂

noncomputable section

namespace DG

open DGOpposite
open scoped CatModule
open CatModule (HOM)

namespace CatBimodule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]

/-! ### Cochains and homotopies -/

section Cochain

variable (B : CatBimodule.{w} D C) {N N' N'' : CatModule.{w} D}

/-- The Hom functor on cochains: a cochain `z : N ⟶ N'` of degree `k` induces the cochain
`w ↦ z ∘ w` of degree `k` from `HOM_D(B, N)` to `HOM_D(B, N')`. -/
def homCochain {k : ℤ} (z : CatModule.Cochain N N' k) :
    CatModule.Cochain (B.homObj N) (B.homObj N') k where
  app _ := HOM.postcompCochain z
  map_mem' hw := HOM.postcompCochain_mem z hw
  map_smul' {Y Y' i f} hf w := by
    change HOM.postcompCochain z (B.homAct N f w) = koszulSign (k * i) • B.homAct N' f
      (HOM.postcompCochain z w)
    rw [homAct_of_mem hf, homAct_of_mem hf, HOM.postcompCochain_precompCochain, mul_comm]

variable {B}

@[simp]
theorem homCochain_app {k : ℤ} (z : CatModule.Cochain N N' k) (Y : C) (w : HOM (B.left Y) N) :
    (B.homCochain z).app Y w = HOM.postcompCochain z w :=
  rfl

theorem homCochain_add {k : ℤ} (z z' : CatModule.Cochain N N' k) :
    B.homCochain (z + z') = B.homCochain z + B.homCochain z' :=
  CatModule.Cochain.ext fun _ w => HOM.postcompCochain_add z z' w

theorem homCochain_neg {k : ℤ} (z : CatModule.Cochain N N' k) :
    B.homCochain (-z) = -B.homCochain z :=
  CatModule.Cochain.ext fun _ w => HOM.postcompCochain_neg z w

theorem homCochain_zero (k : ℤ) :
    B.homCochain (0 : CatModule.Cochain N N' k) = 0 :=
  CatModule.Cochain.ext fun _ w => HOM.postcompCochain_zero w

theorem homCochain_units_smul {k : ℤ} (u : ℤˣ) (z : CatModule.Cochain N N' k) :
    B.homCochain (u • z) = u • B.homCochain z :=
  CatModule.Cochain.ext fun _ w => HOM.postcompCochain_units_smul u z w

theorem homCochain_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : CatModule.Cochain N N' n₁)
    (z₂ : CatModule.Cochain N' N'' n₂) (h : n₁ + n₂ = n₁₂) :
    B.homCochain (z₂.comp z₁ h) = (B.homCochain z₂).comp (B.homCochain z₁) h :=
  CatModule.Cochain.ext fun _ w => by
    rw [CatModule.Cochain.comp_apply, homCochain_app, homCochain_app, homCochain_app,
      HOM.postcompCochain_postcompCochain]
    exact HOM.postcompCochain_congr h.symm (fun _ _ => rfl) w

theorem homCochain_id : B.homCochain (CatModule.Cochain.id N) = CatModule.Cochain.id _ :=
  CatModule.Cochain.ext fun _ w => HOM.postcompCochain_id w

theorem homCochain_ofHom (φ : N ⟶ N') :
    B.homCochain (CatModule.Cochain.ofHom φ) = CatModule.Cochain.ofHom (B.homMap φ) :=
  CatModule.Cochain.ext fun _ _ => rfl

theorem homCochain_δ {k : ℤ} (z : CatModule.Cochain N N' k) (m : ℤ) :
    CatModule.δ k m (B.homCochain z) = B.homCochain (CatModule.δ k m z) := by
  by_cases hkm : k + 1 = m
  · subst hkm
    refine CatModule.Cochain.ext fun Y w => ?_
    rw [CatModule.δ_apply _ _ rfl, homCochain_app, homCochain_app, homCochain_app]
    exact (eq_sub_of_add_eq (HOM.d_postcompCochain z w).symm).symm
  · rw [CatModule.δ_shape _ _ hkm, CatModule.δ_shape _ _ hkm, homCochain_zero]

end Cochain

end CatBimodule

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] (B : CatBimodule.{w} D C) {N N' : CatModule.{w} D}

/-- The Hom functor of a dg bimodule preserves homotopies. -/
@[simps]
def DGHomotopy.homMap {f g : N ⟶ N'} (h : DGHomotopy f g) :
    DGHomotopy (B.homMap f) (B.homMap g) where
  hom := B.homCochain h.hom
  ofHom_eq := by
    rw [← CatBimodule.homCochain_ofHom, ← CatBimodule.homCochain_ofHom,
      CatBimodule.homCochain_δ, ← CatBimodule.homCochain_add, ← h.ofHom_eq]

theorem Homotopic.homMap {f g : N ⟶ N'} (h : Homotopic f g) :
    Homotopic (B.homMap f) (B.homMap g) :=
  ⟨h.some.homMap B⟩

end CatModule

namespace CatBimodule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D]

private theorem map_units {A A' : Type*} [AddCommGroup A] [AddCommGroup A'] (f : A →+ A')
    (u : ℤˣ) (x : A) : f (u • x) = u • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-! ### The path object -/

section Path

variable (N : CatModule.{w} D)

/-- The inclusion `x ↦ (x, 0)` of `N` into its path object, a cochain of degree `0` (not a
morphism: `d (x, 0) = (d x, x)`). -/
def pathIncl₁ : CatModule.Cochain N (CatModule.pathObj N) 0 :=
  CatModule.Cochain.ofHoms (fun X => AddMonoidHom.inl (N.obj X) ((CatModule.shift (-1) N).obj X))
    (fun hx => Prod.mem_grading.mpr ⟨hx, zero_mem _⟩)
    (fun f x => Prod.ext rfl (by
      change 0 = (CatModule.shift (-1) N).act f 0
      rw [map_zero]))

/-- The inclusion `x ↦ (0, x)` of `N` into its path object, a cochain of degree `1`. -/
def pathIncl₂ : CatModule.Cochain N (CatModule.pathObj N) 1 where
  app X := (AddMonoidHom.inr (N.obj X) ((CatModule.shift (-1) N).obj X)).comp
    (CatModule.shift.mk (-1)).toAddMonoidHom
  map_mem' {X i x} hx := Prod.mem_grading.mpr ⟨zero_mem _, by
    have := CatModule.shift.mk_mem_grading (n := -1) hx
    rwa [sub_neg_eq_add] at this⟩
  map_smul' {X Y i f} hf x := by
    refine Prod.ext ?_ ?_
    · change (0 : N.obj Y) = koszulSign (1 * i) • N.act f 0
      rw [map_zero, smul_zero]
    · change CatModule.shift.mk (-1) (f • x) =
        koszulSign (1 * i) • (f • CatModule.shift.mk (M := N) (-1) x)
      rw [CatModule.shift.mk_smul hf]
      congr 1
      rw [neg_one_mul, one_mul, koszulSign, koszulSign, Int.negOnePow_neg]

variable {N}

theorem pathIncl₁_app {X : D} (x : N.obj X) : (pathIncl₁ N).app X x = (x, 0) := rfl

theorem pathIncl₂_app {X : D} (x : N.obj X) :
    (pathIncl₂ N).app X x = (0, CatModule.shift.mk (-1) x) := rfl

variable (N)

theorem δ_pathIncl₁ : CatModule.δ 0 1 (pathIncl₁ N) = pathIncl₂ N := by
  refine CatModule.Cochain.ext fun X x => ?_
  rw [CatModule.δ_zero_cochain_apply, pathIncl₁_app, pathIncl₁_app, pathIncl₂_app]
  refine Prod.ext ?_ ?_
  · exact sub_self _
  · change CatModule.shift.mk (-1) x + d (0 : (CatModule.shift (-1) N).obj X) -
      (0 : (CatModule.shift (-1) N).obj X) = CatModule.shift.mk (-1) x
    rw [d_zero, add_zero, sub_zero]

theorem δ_pathIncl₂ : CatModule.δ 1 2 (pathIncl₂ N) = 0 := by
  refine CatModule.Cochain.ext fun X x => ?_
  rw [CatModule.δ_apply 1 2 rfl, pathIncl₂_app, pathIncl₂_app, CatModule.Cochain.zero_apply]
  refine Prod.ext ?_ ?_
  · change d (0 : N.obj X) - koszulSign 1 • (0 : N.obj X) = 0
    rw [d_zero, smul_zero, sub_zero]
  · change CatModule.shift.mk (-1) (0 : N.obj X) +
      d (CatModule.shift.mk (M := N) (X := X) (-1) x) -
      koszulSign 1 • CatModule.shift.mk (M := N) (-1) (d x) = 0
    rw [CatModule.shift.d_mk, map_zero, zero_add, ← CatModule.shift.mk_units_smul, sub_eq_zero,
      koszulSign, koszulSign, Int.negOnePow_neg]

variable (B : CatBimodule.{w} D C)

/-- The morphism `pathObj (HOM_D(B, N)) ⟶ HOM_D(B, pathObj N)`, `(a, b) ↦ ι₁ ∘ a + ι₂ ∘ b` for
the inclusions `ι₁ = pathIncl₁ N` and `ι₂ = pathIncl₂ N`. -/
def homPathMap : CatModule.pathObj (B.homObj N) ⟶ B.homObj (CatModule.pathObj N) where
  app Y := (HOM.postcompCochain (pathIncl₁ N)).comp
      (AddMonoidHom.fst ((B.homObj N).obj Y) ((CatModule.shift (-1) (B.homObj N)).obj Y)) +
    (HOM.postcompCochain (pathIncl₂ N)).comp ((CatModule.shift.unmk (-1)).toAddMonoidHom.comp
      (AddMonoidHom.snd ((B.homObj N).obj Y) ((CatModule.shift (-1) (B.homObj N)).obj Y)))
  map_mem' {Y k p} hp := by
    have hp' := Prod.mem_grading.mp hp
    refine add_mem ?_ ?_
    · have := HOM.postcompCochain_mem (pathIncl₁ N) hp'.1
      rwa [add_zero] at this
    · have := HOM.postcompCochain_mem (pathIncl₂ N) (CatModule.shift.unmk_mem_grading hp'.2)
      rwa [add_assoc, neg_add_cancel, add_zero] at this
  map_d' {Y} p := by
    obtain ⟨a, b⟩ := p
    obtain ⟨b, rfl⟩ := CatModule.shift.mk_surjective (n := -1) b
    change HOM.postcompCochain (pathIncl₁ N) (d a) + HOM.postcompCochain (pathIncl₂ N)
        (CatModule.shift.unmk (-1) (CatModule.shift.mk (-1) a + d (CatModule.shift.mk (-1) b))) =
      d (M := HOM (B.left Y) (CatModule.pathObj N)) (HOM.postcompCochain (pathIncl₁ N) a +
        HOM.postcompCochain (pathIncl₂ N) (CatModule.shift.unmk (-1) (CatModule.shift.mk (-1) b)))
    rw [CatModule.shift.d_mk, CatModule.shift.unmk_mk, map_add, CatModule.shift.unmk_mk,
      CatModule.shift.unmk_mk, d_add, HOM.d_postcompCochain, HOM.d_postcompCochain,
      show (0 : ℤ) + 1 = 1 from rfl, show (1 : ℤ) + 1 = 2 from rfl, δ_pathIncl₁, δ_pathIncl₂,
      HOM.postcompCochain_zero, map_add (HOM.postcompCochain (pathIncl₂ N)), map_units]
    simp only [koszulSign_zero, one_smul, zero_add, koszulSign, Int.negOnePow_neg,
      Int.negOnePow_one, Units.neg_smul]
    abel
  map_smul' {Y Y'} f p := by
    obtain ⟨a, b⟩ := p
    change HOM.postcompCochain (pathIncl₁ N) (B.homAct N f a) + HOM.postcompCochain (pathIncl₂ N)
        (CatModule.shift.unmk (-1) ((CatModule.shift (-1) (B.homObj N)).act f b)) =
      B.homAct _ f (HOM.postcompCochain (pathIncl₁ N) a +
        HOM.postcompCochain (pathIncl₂ N) (CatModule.shift.unmk (-1) b))
    rw [map_add]
    congr 1
    · induction f using DG.induction_on with
      | h_zero => simp
      | h_add f g hf hg => rw [map_add, AddMonoidHom.add_apply, map_add, hf, hg, map_add,
          AddMonoidHom.add_apply]
      | h_homogeneous f =>
        rw [homAct_of_mem f.2, homAct_of_mem f.2, HOM.postcompCochain_precompCochain, mul_zero,
          koszulSign_zero, one_smul]
    · induction f using DG.induction_on with
      | h_zero => simp
      | h_add f g hf hg => rw [map_add, AddMonoidHom.add_apply, map_add, map_add, hf, hg,
          map_add, AddMonoidHom.add_apply]
      | h_homogeneous f =>
        rename_i i
        rw [CatModule.act_apply, CatModule.shift.unmk_smul f.2, map_units,
          ← CatModule.act_apply (M := B.homObj N), homObj_act, homAct_of_mem f.2,
          homAct_of_mem f.2, HOM.postcompCochain_precompCochain, smul_smul, ← koszulSign_add]
        convert one_smul ℤˣ _
        rw [show -1 * i + i * 1 = 0 by ring, koszulSign_zero]

@[reassoc (attr := simp)]
theorem homPathMap_π : B.homPathMap N ≫ B.homMap (CatModule.pathObj.π N) =
    CatModule.pathObj.π (B.homObj N) := by
  refine CatModule.hom_ext fun Y p => ?_
  obtain ⟨a, b⟩ := p
  change HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N))
    (HOM.postcompCochain (pathIncl₁ N) a +
      HOM.postcompCochain (pathIncl₂ N) (CatModule.shift.unmk (-1) b)) = a
  rw [map_add, HOM.postcompCochain_postcompCochain, HOM.postcompCochain_postcompCochain,
    HOM.postcompCochain_eq_self (add_zero 0) (fun _ _ => rfl),
    HOM.postcompCochain_eq_zero (fun _ _ => rfl), add_zero]

/-- The morphism `HOM_D(B, pathObj N) ⟶ pathObj (HOM_D(B, N))`, `w ↦ (π ∘ w, h ∘ w)` for the
projection `π` and the null-homotopy `h = pathObj.homotopy N` of `π`; inverse to
`homPathMap`. -/
def homPathInv : B.homObj (CatModule.pathObj N) ⟶ CatModule.pathObj (B.homObj N) where
  app Y := (HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N))).prod
    ((CatModule.shift.mk (M := B.homObj N) (X := Y) (-1)).toAddMonoidHom.comp
      (HOM.postcompCochain (CatModule.pathObj.homotopy N)))
  map_mem' {Y k w} hw := Prod.mem_grading.mpr ⟨by
    have := HOM.postcompCochain_mem (CatModule.Cochain.ofHom (CatModule.pathObj.π N)) hw
    rwa [add_zero] at this,
    CatModule.shift.mem_grading_iff.mpr (HOM.postcompCochain_mem _ hw)⟩
  map_d' {Y} w := by
    refine Prod.ext ?_ ?_
    · change HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N)) (d w) =
        d (M := HOM (B.left Y) N)
          (HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N)) w)
      rw [HOM.d_postcompCochain, CatModule.δ_ofHom, HOM.postcompCochain_zero, zero_add,
        koszulSign_zero, one_smul]
    · change CatModule.shift.mk (M := B.homObj N) (-1)
          (HOM.postcompCochain (CatModule.pathObj.homotopy N) (d w)) =
        CatModule.shift.mk (M := B.homObj N) (-1)
          (HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N)) w) +
        d (CatModule.shift.mk (M := B.homObj N) (X := Y) (-1)
          (HOM.postcompCochain (CatModule.pathObj.homotopy N) w))
      rw [CatModule.shift.d_mk, ← map_add, HOM.d_postcompCochain,
        show (-1 : ℤ) + 1 = 0 from rfl, ← CatModule.pathObj.ofHom_π, _root_.smul_add, smul_smul,
        Int.units_mul_self, one_smul]
      simp only [koszulSign, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
      abel
  map_smul' {Y Y'} f w := by
    refine Prod.ext ?_ ?_
    · change HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N))
          (B.homAct _ f w) =
        B.homAct N f (HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N)) w)
      induction f using DG.induction_on with
      | h_zero => simp
      | h_add f g hf hg => rw [map_add, AddMonoidHom.add_apply, map_add, hf, hg, map_add,
          AddMonoidHom.add_apply]
      | h_homogeneous f =>
        rw [homAct_of_mem f.2, homAct_of_mem f.2, HOM.postcompCochain_precompCochain, mul_zero,
          koszulSign_zero, one_smul]
    · change CatModule.shift.mk (M := B.homObj N) (-1)
          (HOM.postcompCochain (CatModule.pathObj.homotopy N) (B.homAct _ f w)) =
        (CatModule.shift (-1) (B.homObj N)).act f (CatModule.shift.mk (M := B.homObj N) (-1)
          (HOM.postcompCochain (CatModule.pathObj.homotopy N) w))
      induction f using DG.induction_on with
      | h_zero => simp
      | h_add f g hf hg => rw [map_add, AddMonoidHom.add_apply, map_add, map_add, hf, hg,
          map_add, AddMonoidHom.add_apply]
      | h_homogeneous f =>
        rw [CatModule.act_apply, CatModule.shift.smul_mk f.2, homAct_of_mem f.2,
          HOM.postcompCochain_precompCochain, ← CatModule.act_apply (M := B.homObj N),
          homObj_act, homAct_of_mem f.2, mul_comm]

@[reassoc (attr := simp)]
theorem homPathMap_inv : B.homPathMap N ≫ B.homPathInv N = 𝟙 _ := by
  refine CatModule.hom_ext fun Y p => ?_
  obtain ⟨a, b⟩ := p
  obtain ⟨b, rfl⟩ := CatModule.shift.mk_surjective (n := -1) b
  refine Prod.ext ?_ ?_
  · change HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N))
      (HOM.postcompCochain (pathIncl₁ N) a + HOM.postcompCochain (pathIncl₂ N)
        (CatModule.shift.unmk (-1) (CatModule.shift.mk (-1) b))) = a
    rw [map_add, HOM.postcompCochain_postcompCochain, HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_eq_self (add_zero 0) (fun _ _ => rfl),
      HOM.postcompCochain_eq_zero (fun _ _ => rfl), add_zero]
  · change CatModule.shift.mk (M := B.homObj N) (-1)
      (HOM.postcompCochain (CatModule.pathObj.homotopy N)
        (HOM.postcompCochain (pathIncl₁ N) a + HOM.postcompCochain (pathIncl₂ N)
          (CatModule.shift.unmk (-1) (CatModule.shift.mk (-1) b)))) = CatModule.shift.mk (-1) b
    rw [map_add, HOM.postcompCochain_postcompCochain, HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_eq_zero (fun _ _ => rfl),
      HOM.postcompCochain_eq_self (add_neg_cancel 1) (fun _ _ => rfl), zero_add,
      CatModule.shift.unmk_mk]

@[reassoc (attr := simp)]
theorem homPathInv_map : B.homPathInv N ≫ B.homPathMap N = 𝟙 _ := by
  refine CatModule.hom_ext fun Y w => ?_
  change HOM.postcompCochain (pathIncl₁ N)
      (HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.pathObj.π N)) w) +
    HOM.postcompCochain (pathIncl₂ N) (HOM.postcompCochain (CatModule.pathObj.homotopy N) w) = w
  rw [HOM.postcompCochain_postcompCochain, HOM.postcompCochain_postcompCochain,
    HOM.postcompCochain_congr (neg_add_cancel 1) (z' := (pathIncl₂ N).comp
      (CatModule.pathObj.homotopy N) (neg_add_cancel 1)) (fun _ _ => rfl) w,
    HOM.postcompCochain_congr (add_zero 0) (z' := (pathIncl₁ N).comp
      (CatModule.Cochain.ofHom (CatModule.pathObj.π N)) (add_zero 0)) (fun _ _ => rfl) w,
    ← HOM.postcompCochain_add]
  exact HOM.postcompCochain_eq_self rfl (fun X (p : (CatModule.pathObj N).obj X) =>
    Prod.ext (add_zero p.1) (zero_add p.2)) w

/-- The Hom functor of a dg bimodule commutes with the path object:
`pathObj (HOM_D(B, N)) ≅ HOM_D(B, pathObj N)`, compatibly with the projections
(`DG.CatBimodule.homPathMap_π`). -/
@[simps]
def homPathIso : CatModule.pathObj (B.homObj N) ≅ B.homObj (CatModule.pathObj N) where
  hom := B.homPathMap N
  inv := B.homPathInv N

end Path

/-! ### Shifts -/

section Shift

variable (n : ℤ) (N : CatModule.{w} D)

/-- The identity `N⟦n⟧ → N` as a cochain of degree `n`. -/
def shiftUnmkCochain : CatModule.Cochain (CatModule.shift n N) N n where
  app _ := (CatModule.shift.unmk n).toAddMonoidHom
  map_mem' hx := CatModule.shift.unmk_mem_grading hx
  map_smul' hf x := CatModule.shift.unmk_smul hf x

/-- The identity `N → N⟦n⟧` as a cochain of degree `-n`. -/
def shiftMkCochain : CatModule.Cochain N (CatModule.shift n N) (-n) where
  app _ := (CatModule.shift.mk n).toAddMonoidHom
  map_mem' hx := by
    have := CatModule.shift.mk_mem_grading (n := n) hx
    rwa [sub_eq_add_neg] at this
  map_smul' {X Y i f} hf x := by
    change CatModule.shift.mk n (f • x) = _
    rw [CatModule.shift.mk_smul hf, neg_mul, koszulSign, koszulSign, Int.negOnePow_neg]
    rfl

variable {n N}

@[simp]
theorem shiftUnmkCochain_app {X : D} (x : (CatModule.shift n N).obj X) :
    (shiftUnmkCochain n N).app X x = CatModule.shift.unmk n x := rfl

@[simp]
theorem shiftMkCochain_app {X : D} (x : N.obj X) :
    (shiftMkCochain n N).app X x = CatModule.shift.mk n x := rfl

variable (n N)

theorem δ_shiftUnmkCochain : CatModule.δ n (n + 1) (shiftUnmkCochain n N) = 0 :=
  CatModule.Cochain.ext fun X x => by
    rw [CatModule.δ_apply _ _ rfl, shiftUnmkCochain_app, shiftUnmkCochain_app,
      CatModule.shift.unmk_d, CatModule.Cochain.zero_apply, smul_smul, Int.units_mul_self,
      one_smul, sub_self]

theorem δ_shiftMkCochain : CatModule.δ (-n) (-n + 1) (shiftMkCochain n N) = 0 :=
  CatModule.Cochain.ext fun X x => by
    rw [CatModule.δ_apply _ _ rfl, shiftMkCochain_app, shiftMkCochain_app,
      CatModule.shift.d_mk, CatModule.Cochain.zero_apply]
    simp only [koszulSign, Int.negOnePow_neg]
    rw [← CatModule.shift.mk_units_smul, sub_self]

variable (B : CatBimodule.{w} D C)

/-- The morphism `HOM_D(B, N⟦n⟧) ⟶ HOM_D(B, N)⟦n⟧`: a cochain of degree `k` into `N⟦n⟧` is a
cochain of degree `k + n` into `N`. -/
def homShiftHom : B.homObj (CatModule.shift n N) ⟶ CatModule.shift n (B.homObj N) where
  app Y := (CatModule.shift.mk n).toAddMonoidHom.comp (HOM.postcompCochain (shiftUnmkCochain n N))
  map_mem' hw := CatModule.shift.mem_grading_iff.mpr (HOM.postcompCochain_mem _ hw)
  map_d' {Y} w := by
    change CatModule.shift.mk (M := B.homObj N) n
        (HOM.postcompCochain (shiftUnmkCochain n N) (d w)) =
      d (CatModule.shift.mk (M := B.homObj N) n (HOM.postcompCochain (shiftUnmkCochain n N) w))
    rw [CatModule.shift.d_mk, HOM.d_postcompCochain, δ_shiftUnmkCochain, HOM.postcompCochain_zero,
      zero_add,
      smul_smul, Int.units_mul_self, one_smul]
  map_smul' {Y Y'} f w := by
    change CatModule.shift.mk (M := B.homObj N) n
        (HOM.postcompCochain (shiftUnmkCochain n N) (B.homAct _ f w)) =
      (CatModule.shift n (B.homObj N)).act f
        (CatModule.shift.mk (M := B.homObj N) n (HOM.postcompCochain (shiftUnmkCochain n N) w))
    induction f using DG.induction_on with
    | h_zero => simp
    | h_add f g hf hg => rw [map_add, AddMonoidHom.add_apply, map_add, map_add, hf, hg,
        map_add, AddMonoidHom.add_apply]
    | h_homogeneous f =>
      rw [CatModule.act_apply, CatModule.shift.smul_mk f.2, homAct_of_mem f.2,
        HOM.postcompCochain_precompCochain, ← CatModule.act_apply (M := B.homObj N), homObj_act,
        homAct_of_mem f.2, mul_comm]

/-- The morphism `HOM_D(B, N)⟦n⟧ ⟶ HOM_D(B, N⟦n⟧)`, inverse to `homShiftHom`. -/
def homShiftInv : CatModule.shift n (B.homObj N) ⟶ B.homObj (CatModule.shift n N) where
  app Y := (HOM.postcompCochain (shiftMkCochain n N)).comp (CatModule.shift.unmk n).toAddMonoidHom
  map_mem' {Y k w} hw := by
    have := HOM.postcompCochain_mem (shiftMkCochain n N) (CatModule.shift.unmk_mem_grading hw)
    rwa [add_neg_cancel_right] at this
  map_d' {Y} w := by
    change HOM.postcompCochain (shiftMkCochain n N) (CatModule.shift.unmk n (d w)) =
      d (M := HOM (B.left Y) (CatModule.shift n N))
        (HOM.postcompCochain (shiftMkCochain n N) (CatModule.shift.unmk n w))
    rw [CatModule.shift.unmk_d, map_units, HOM.d_postcompCochain, δ_shiftMkCochain,
      HOM.postcompCochain_zero,
      zero_add, koszulSign, koszulSign, Int.negOnePow_neg]
  map_smul' {Y Y'} f w := by
    change HOM.postcompCochain (shiftMkCochain n N)
        (CatModule.shift.unmk n ((CatModule.shift n (B.homObj N)).act f w)) =
      B.homAct _ f (HOM.postcompCochain (shiftMkCochain n N) (CatModule.shift.unmk n w))
    induction f using DG.induction_on with
    | h_zero => simp
    | h_add f g hf hg => rw [map_add, AddMonoidHom.add_apply, map_add, map_add, hf, hg,
        map_add, AddMonoidHom.add_apply]
    | h_homogeneous f =>
      rename_i i
      rw [CatModule.act_apply, CatModule.shift.unmk_smul f.2, map_units,
        ← CatModule.act_apply (M := B.homObj N), homObj_act, homAct_of_mem f.2,
        homAct_of_mem f.2, HOM.postcompCochain_precompCochain, smul_smul, ← koszulSign_add]
      convert one_smul ℤˣ _
      rw [show n * i + i * -n = 0 by ring, koszulSign_zero]

@[reassoc (attr := simp)]
theorem homShiftHom_inv : B.homShiftHom n N ≫ B.homShiftInv n N = 𝟙 _ :=
  CatModule.hom_ext fun Y w => by
    change HOM.postcompCochain (shiftMkCochain n N)
      (HOM.postcompCochain (shiftUnmkCochain n N) w) = w
    rw [HOM.postcompCochain_postcompCochain]
    exact HOM.postcompCochain_eq_self (add_neg_cancel n) (fun _ _ => rfl) w

@[reassoc (attr := simp)]
theorem homShiftInv_hom : B.homShiftInv n N ≫ B.homShiftHom n N = 𝟙 _ :=
  CatModule.hom_ext fun Y w => by
    change CatModule.shift.mk (M := B.homObj N) n (HOM.postcompCochain (shiftUnmkCochain n N)
      (HOM.postcompCochain (shiftMkCochain n N) (CatModule.shift.unmk n w))) = w
    rw [HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_eq_self (neg_add_cancel n) (fun _ _ => rfl), CatModule.shift.mk_unmk]

/-- The Hom functor of a dg bimodule commutes with the shifts:
`HOM_D(B, N⟦n⟧) ≅ HOM_D(B, N)⟦n⟧`. -/
@[simps]
def homShiftIso : B.homObj (CatModule.shift n N) ≅ CatModule.shift n (B.homObj N) where
  hom := B.homShiftHom n N
  inv := B.homShiftInv n N

theorem homShiftHom_app (Y : C) (w : (B.homObj (CatModule.shift n N)).obj Y) :
    (B.homShiftHom n N).app Y w =
      CatModule.shift.mk n (HOM.postcompCochain (shiftUnmkCochain n N) w) := rfl

theorem homShiftHom_naturality {N' : CatModule.{w} D} (φ : N ⟶ N') :
    B.homMap (CatModule.shiftMap n φ) ≫ B.homShiftHom n N' =
      B.homShiftHom n N ≫ CatModule.shiftMap n (B.homMap φ) :=
  CatModule.hom_ext fun Y w => by
    change CatModule.shift.mk (M := B.homObj N') n (HOM.postcompCochain (shiftUnmkCochain n N')
        (HOM.postcompCochain (CatModule.Cochain.ofHom (CatModule.shiftMap n φ)) w)) =
      CatModule.shift.mk (M := B.homObj N') n (HOM.postcompCochain (CatModule.Cochain.ofHom φ)
        (HOM.postcompCochain (shiftUnmkCochain n N) w))
    rw [HOM.postcompCochain_postcompCochain, HOM.postcompCochain_postcompCochain]
    exact congrArg _ (HOM.postcompCochain_congr (k := 0 + n) (k' := n + 0) (by omega)
      (fun _ _ => rfl) w)

theorem homShiftHom_add (a b : ℤ) :
    B.homShiftHom (a + b) N = B.homMap (CatModule.shiftShiftIso N a b (a + b) rfl).hom ≫
      B.homShiftHom b (CatModule.shift a N) ≫ CatModule.shiftMap b (B.homShiftHom a N) ≫
      (CatModule.shiftShiftIso (B.homObj N) a b (a + b) rfl).inv :=
  CatModule.hom_ext fun Y w => by
    rw [CatModule.comp_app, CatModule.comp_app, CatModule.comp_app,
      CatModule.shiftShiftIso_inv_app, CatModule.unmk_shiftMap_app, homShiftHom_app,
      homShiftHom_app, homShiftHom_app, homMap_app, CatModule.shift.unmk_mk,
      CatModule.shift.unmk_mk, HOM.postcompCochain_postcompCochain,
      HOM.postcompCochain_postcompCochain]
    refine congrArg (CatModule.shift.mk (M := B.homObj N) (X := Y) (a + b)) ?_
    apply HOM.postcompCochain_congr
    · omega
    · intro _ _
      rfl

/-- The Hom functor of a dg bimodule commutes with the shifts. -/
instance homFunctor_commShift : (B.homFunctor).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (fun N => B.homShiftIso n N)
    fun {N _} φ => B.homShiftHom_naturality n N φ
  commShiftIso_zero := by
    ext N : 3
    refine CatModule.hom_ext fun Y w => ?_
    rw [Functor.CommShift.isoZero_hom_app]
    change CatModule.shift.mk (M := B.homObj N) 0 (HOM.postcompCochain (shiftUnmkCochain 0 N) w) =
      CatModule.shift.mk (M := B.homObj N) 0 (HOM.postcompCochain (CatModule.Cochain.ofHom
        ((shiftFunctorZero (CatModule.{w} D) ℤ).hom.app N)) w)
    exact congrArg _ (HOM.postcompCochain_congr rfl (fun _ _ => rfl) w)
  commShiftIso_add a b := by
    ext N : 3
    rw [Functor.CommShift.isoAdd_hom_app]
    exact B.homShiftHom_add N a b

theorem homFunctor_commShiftIso_hom_app (N : CatModule.{w} D) :
    ((B.homFunctor).commShiftIso n).hom.app N = B.homShiftHom n N := rfl

end Shift

end CatBimodule

end DG
