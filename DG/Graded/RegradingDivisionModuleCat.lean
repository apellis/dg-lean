import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Equivalence
import DG.Graded.Regrading
import DG.Graded.ModuleCat

/-!
# The regrading equivalence of graded module categories for division by `k`

Let `k ≥ 1` and let `(A, 𝒜)` be a `ℤ`-graded ring concentrated in degrees divisible by `k`
(`DG.IsConcentratedInMultiples 𝒜 k`). Then `A` is the regraded ring
`B = RegradeByDivision 𝒜 k 0 = ⨁ q, A^{q k}` of `DG.Graded.Regrading` (`DG.regradeRingEquiv`),
and a `ℤ`-graded `A`-module is the same as a family, indexed by the residues `r ∈ ℤ/k`, of
`ℤ`-graded `B`-modules: its residue classes `RegradeByDivision ℳ k r = ⨁ q, ℳ (q k + r)`
(`DG.residueEquiv`).

## Main definitions

* `DG.regradeRingHom h : A →+* B`, `a ↦ a` placed in degree `q` for `a ∈ A^{q k}`, and the ring
  isomorphism `DG.regradeRingEquiv h : A ≃+* B`, whose inverse is `RegradeByDivision.fold`.
* `DG.GradedModuleCat.regradeFunctor 𝒜 k r : GradedModuleCat 𝒜 ⥤ GradedModuleCat ℬ` (with
  `ℬ = regradeGrading 𝒜 k 0`): `M ↦ RegradeByDivision ℳ k r`.
* `DG.GradedModuleCat.unregrade h : (ZMod k → GradedModuleCat ℬ) ⥤ GradedModuleCat 𝒜`:
  a family `N` goes to `⨁ r, N r`, with `A` acting through `DG.regradeRingHom h` and the
  degree-`n` piece `(N (n mod k))^{n / k}` (`DG.GradedModuleCat.unregradeGrading`).
* `DG.GradedModuleCat.regradeEquivalence h :
    GradedModuleCat 𝒜 ≌ (ZMod k → GradedModuleCat ℬ)`, with unit given by the residue
  decomposition `DG.residueEquiv` (`DG.GradedModuleCat.regradeUnitIso`).

The hypothesis that `𝒜` is concentrated in degrees divisible by `k` is necessary: otherwise the
residue classes of a graded `A`-module are not `A`-submodules.
-/

set_option backward.isDefEq.respectTransparency false

universe v

noncomputable section

namespace DG

open CategoryTheory DirectSum

/-! ### Rings concentrated in degrees divisible by `k` -/

section Concentrated

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A]

/-- A `ℤ`-grading concentrated in degrees divisible by `k`: `Aⁿ = 0` unless `k ∣ n`. -/
class IsConcentratedInMultiples (𝒜 : ℤ → τ) (k : ℕ) : Prop where
  eq_zero : ∀ ⦃n : ℤ⦄, ¬ (k : ℤ) ∣ n → ∀ ⦃a : A⦄, a ∈ 𝒜 n → a = 0

variable {𝒜 : ℤ → τ} {k : ℕ}

variable (k) in
theorem IsConcentratedInMultiples.mem_ediv [IsConcentratedInMultiples 𝒜 k] {n : ℤ} {a : A}
    (ha : a ∈ 𝒜 n) : a ∈ 𝒜 (n / k * k + 0) := by
  by_cases hn : (k : ℤ) ∣ n
  · rwa [Int.ediv_mul_cancel hn, add_zero]
  · rw [IsConcentratedInMultiples.eq_zero hn ha]; exact zero_mem _

variable [GradedRing 𝒜] [NeZero k] [IsConcentratedInMultiples 𝒜 k]

variable (𝒜 k) in
/-- The additive map `A → ⨁ q, A^{q k}` placing `a ∈ Aⁿ` in degree `n / k`, for `𝒜` concentrated
in degrees divisible by `k`. -/
def regradeAddHom : A →+ RegradeByDivision 𝒜 k 0 :=
  liftHomogeneous 𝒜 fun n =>
    { toFun := fun a =>
        RegradeByDivision.mk 𝒜 k 0 (n / k) a (IsConcentratedInMultiples.mem_ediv k a.2)
      map_zero' := RegradeByDivision.mk_zero _
      map_add' := fun _ _ => RegradeByDivision.mk_add _ _ _ }

theorem regradeAddHom_of_mem {q : ℤ} {a : A}
    (ha : a ∈ 𝒜 (q * k + 0)) : regradeAddHom 𝒜 k a = RegradeByDivision.mk 𝒜 k 0 q a ha := by
  rw [regradeAddHom, liftHomogeneous_of_mem 𝒜 _ ha]
  have hk : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne k)
  exact RegradeByDivision.mk_congr (by rw [add_zero, Int.mul_ediv_cancel _ hk]) rfl _ _

variable (𝒜 k) in
/-- The ring homomorphism `A → ⨁ q, A^{q k}` placing `a ∈ A^{q k}` in degree `q`, for `𝒜`
concentrated in degrees divisible by `k`. -/
def regradeRingHom : A →+* RegradeByDivision 𝒜 k 0 :=
  { regradeAddHom 𝒜 k with
    map_one' := by
      change regradeAddHom 𝒜 k 1 = 1
      rw [regradeAddHom_of_mem (q := 0) (by simpa using SetLike.GradedOne.one_mem (A := 𝒜)),
        RegradeByDivision.one_eq_mk]
    map_mul' := fun a b => by
      change regradeAddHom 𝒜 k (a * b) = regradeAddHom 𝒜 k a * regradeAddHom 𝒜 k b
      induction a using Decomposition.inductionOn 𝒜 with
      | zero => simp
      | homogeneous a =>
        induction b using Decomposition.inductionOn 𝒜 with
        | zero => simp
        | homogeneous b =>
          rw [regradeAddHom_of_mem (IsConcentratedInMultiples.mem_ediv k a.2),
            regradeAddHom_of_mem (IsConcentratedInMultiples.mem_ediv k b.2),
            RegradeByDivision.mk_mul_mk]
          exact regradeAddHom_of_mem _
        | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
      | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul] }

theorem regradeRingHom_of_mem {q : ℤ} {a : A}
    (ha : a ∈ 𝒜 (q * k + 0)) : regradeRingHom 𝒜 k a = RegradeByDivision.mk 𝒜 k 0 q a ha :=
  regradeAddHom_of_mem ha

variable (𝒜 k) in
/-- **A ring concentrated in degrees divisible by `k` is its regrading.** The ring isomorphism
`A ≃+* ⨁ q, A^{q k}`, `a ∈ A^{q k}` placed in degree `q`, with inverse
`DG.RegradeByDivision.fold`. -/
def regradeRingEquiv : A ≃+* RegradeByDivision 𝒜 k 0 :=
  { regradeRingHom 𝒜 k with
    invFun := RegradeByDivision.fold 𝒜 k 0
    left_inv := fun a => by
      induction a using Decomposition.inductionOn 𝒜 with
      | zero => simp
      | homogeneous a =>
        change RegradeByDivision.fold 𝒜 k 0 (regradeRingHom 𝒜 k a) = a
        rw [regradeRingHom_of_mem (IsConcentratedInMultiples.mem_ediv k a.2),
          RegradeByDivision.fold_mk]
      | add a a' ha ha' =>
        change RegradeByDivision.fold 𝒜 k 0 (regradeRingHom 𝒜 k (a + a')) = a + a'
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) ha ha'
    right_inv := fun x => by
      induction x using RegradeByDivision.induction_on with
      | zero => simp
      | mk q a ha =>
        change regradeRingHom 𝒜 k (RegradeByDivision.fold 𝒜 k 0 _) = _
        rw [RegradeByDivision.fold_mk, regradeRingHom_of_mem ha]
      | add x y hx hy =>
        change regradeRingHom 𝒜 k (RegradeByDivision.fold 𝒜 k 0 (x + y)) = x + y
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) hx hy }

@[simp]
theorem regradeRingEquiv_apply (a : A) :
    regradeRingEquiv 𝒜 k a = regradeRingHom 𝒜 k a := rfl

end Concentrated

/-! ### Maps between residue classes -/

namespace RegradeByDivision

variable {M N σ σ' : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]
  [AddCommGroup N] [SetLike σ' N] [AddSubgroupClass σ' N] {ℳ : ℤ → σ} {𝒩 : ℤ → σ'} {k r : ℤ}

variable (ℳ 𝒩 k r) in
/-- The map `RegradeByDivision ℳ k r → RegradeByDivision 𝒩 k r` induced by an additive map of
degree `0`. -/
def mapHom (f : M →+ N) (hf : ∀ {n : ℤ} {m : M}, m ∈ ℳ n → f m ∈ 𝒩 n) :
    RegradeByDivision ℳ k r →+ RegradeByDivision 𝒩 k r :=
  DirectSum.map fun q =>
    (f.comp (AddSubmonoidClass.subtype (divGrading ℳ k r q))).codRestrict _ fun m => hf m.2

theorem mapHom_mk (f : M →+ N) (hf : ∀ {n : ℤ} {m : M}, m ∈ ℳ n → f m ∈ 𝒩 n) (q : ℤ) (m : M)
    (hm : m ∈ ℳ (q * k + r)) : mapHom ℳ 𝒩 k r f hf (mk ℳ k r q m hm) = mk 𝒩 k r q (f m) (hf hm) :=
  DirectSum.map_of _ _ _

end RegradeByDivision

/-! ### The functors -/

namespace GradedModuleCat

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ℤ → τ)
  [GradedRing 𝒜] (k : ℕ) [NeZero k]

section Regrade

variable (r : ZMod k)

/-- The residue class `RegradeByDivision ℳ k r` of a graded `A`-module, as a graded module over
`⨁ q, A^{q k}`. -/
abbrev regradeObj (M : GradedModuleCat.{v} 𝒜) : GradedModuleCat.{v} (regradeGrading 𝒜 k 0) :=
  GradedModuleCat.of (regradeGrading 𝒜 k 0) (RegradeByDivision M.grading k (r.val : ℤ))
    (regradeGrading M.grading k (r.val : ℤ))

variable {𝒜 k}

/-- The additive map on residue classes induced by a morphism of graded `A`-modules. -/
def regradeMapAddHom {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) :
    RegradeByDivision M.grading k (r.val : ℤ) →+ RegradeByDivision N.grading k (r.val : ℤ) :=
  RegradeByDivision.mapHom M.grading N.grading k (r.val : ℤ) f.hom.toAddMonoidHom
    fun hm => f.map_mem hm

omit [AddSubgroupClass τ A] [GradedRing 𝒜] [NeZero k] in
theorem regradeMapAddHom_mk {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (q : ℤ) (m : M)
    (hm : m ∈ M.grading (q * k + (r.val : ℤ))) :
    regradeMapAddHom r f (RegradeByDivision.mk _ k _ q m hm) =
      RegradeByDivision.mk _ k _ q (f.hom m) (f.map_mem hm) :=
  RegradeByDivision.mapHom_mk _ _ q m hm

/-- The map on residue classes induced by a morphism of graded `A`-modules. -/
def regradeMap {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) :
    regradeObj 𝒜 k r M ⟶ regradeObj 𝒜 k r N where
  hom :=
    { toFun := regradeMapAddHom r f
      map_add' := map_add _
      map_smul' := map_smul_of_homogeneous (regradeGrading 𝒜 k 0)
        (regradeGrading M.grading k (r.val : ℤ)) (regradeMapAddHom r f) fun p q x y hx hy => by
          obtain ⟨a, ha, rfl⟩ := RegradeByDivision.mem_regradeGrading_iff.mp hx
          obtain ⟨m, hm, rfl⟩ := RegradeByDivision.mem_regradeGrading_iff.mp hy
          rw [RegradeByDivision.mk_smul_mk, regradeMapAddHom_mk, regradeMapAddHom_mk,
            RegradeByDivision.mk_smul_mk]
          exact RegradeByDivision.mk_congr rfl (f.hom.map_smul a m) _ _ }
  map_mem' := by
    intro q x hx
    obtain ⟨m, hm, rfl⟩ := RegradeByDivision.mem_regradeGrading_iff.mp hx
    change regradeMapAddHom r f _ ∈ _
    rw [regradeMapAddHom_mk]
    exact RegradeByDivision.mk_mem _ _

omit [NeZero k] in
theorem regradeMap_mk {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (q : ℤ) (m : M)
    (hm : m ∈ M.grading (q * k + (r.val : ℤ))) :
    (regradeMap r f).hom (RegradeByDivision.mk _ k _ q m hm) =
      RegradeByDivision.mk _ k _ q (f.hom m) (f.map_mem hm) :=
  regradeMapAddHom_mk r f q m hm

variable (𝒜 k)

/-- The functor `M ↦ RegradeByDivision ℳ k r` from graded `A`-modules to graded modules over
`⨁ q, A^{q k}`. -/
def regradeFunctor : GradedModuleCat.{v} 𝒜 ⥤ GradedModuleCat.{v} (regradeGrading 𝒜 k 0) where
  obj M := regradeObj 𝒜 k r M
  map f := regradeMap r f
  map_id M := hom_ext (LinearMap.ext fun x => by
    induction x using RegradeByDivision.induction_on with
    | zero => simp
    | mk q m hm => exact regradeMap_mk r (𝟙 M) q m hm
    | add x y hx hy => rw [map_add, map_add, hx, hy])
  map_comp f g := hom_ext (LinearMap.ext fun x => by
    induction x using RegradeByDivision.induction_on with
    | zero => simp
    | mk q m hm =>
      change (regradeMap r (f ≫ g)).hom _ = (regradeMap r g).hom ((regradeMap r f).hom _)
      rw [regradeMap_mk, regradeMap_mk, regradeMap_mk]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy])

/-- The functor from graded `A`-modules to families, indexed by `ℤ/k`, of graded modules over
`⨁ q, A^{q k}`: the residue classes. -/
def regrade : GradedModuleCat.{v} 𝒜 ⥤ (ZMod k → GradedModuleCat.{v} (regradeGrading 𝒜 k 0)) :=
  Functor.pi' fun r => regradeFunctor 𝒜 k r

end Regrade

section Unregrade

variable {𝒜 k} (N : ZMod k → GradedModuleCat.{v} (regradeGrading 𝒜 k 0))

/-- The grading of `⨁ r, N r` for a family `N` of graded modules over `⨁ q, A^{q k}`: the
degree-`n` piece is `(N (n mod k))^{n / k}`. -/
def unregradeGrading (n : ℤ) : AddSubgroup (⨁ r : ZMod k, (N r : Type v)) :=
  ((N (n : ZMod k)).grading (n / k)).map (DirectSum.of (fun r => (N r : Type v)) (n : ZMod k))

omit [NeZero k] in
theorem of_mem_unregradeGrading {r : ZMod k} {q n : ℤ} (hr : (n : ZMod k) = r) (hq : n / k = q)
    {y : N r} (hy : y ∈ (N r).grading q) :
    DirectSum.of (fun r => (N r : Type v)) r y ∈ unregradeGrading N n := by
  subst hr hq
  exact ⟨y, hy, rfl⟩

theorem of_mem_unregradeGrading' (r : ZMod k) (q : ℤ) {y : N r} (hy : y ∈ (N r).grading q) :
    DirectSum.of (fun r => (N r : Type v)) r y ∈ unregradeGrading N (q * k + (r.val : ℤ)) :=
  of_mem_unregradeGrading N (intCast_mul_add_val k q r) (mul_add_val_ediv k q r) hy

/-- The decomposition of `⨁ r, N r` into the pieces `DG.GradedModuleCat.unregradeGrading`. -/
def unregradeDecompose : (⨁ r : ZMod k, (N r : Type v)) →+ ⨁ n : ℤ, unregradeGrading N n :=
  DirectSum.toAddMonoid fun r =>
    liftHomogeneous (N r).grading fun q =>
      (DirectSum.of (fun n => ↥(unregradeGrading N n)) (q * k + (r.val : ℤ))).comp
        (((DirectSum.of (fun r => (N r : Type v)) r).comp
          (AddSubmonoidClass.subtype ((N r).grading q))).codRestrict _ fun y =>
            of_mem_unregradeGrading' N r q y.2)

theorem unregradeDecompose_of_mem (r : ZMod k) {q : ℤ} {y : N r} (hy : y ∈ (N r).grading q) :
    unregradeDecompose N (DirectSum.of _ r y) =
      DirectSum.of (fun n => ↥(unregradeGrading N n)) (q * k + (r.val : ℤ))
        ⟨DirectSum.of _ r y, of_mem_unregradeGrading' N r q hy⟩ := by
  rw [unregradeDecompose, DirectSum.toAddMonoid_of, liftHomogeneous_of_mem _ _ hy]
  rfl

omit [NeZero k] in
theorem of_congr_unregrade {n n' : ℤ} (h : n = n') {x : ⨁ r : ZMod k, (N r : Type v)}
    (hx : x ∈ unregradeGrading N n) (hx' : x ∈ unregradeGrading N n') :
    DirectSum.of (fun n => ↥(unregradeGrading N n)) n ⟨x, hx⟩ =
      DirectSum.of (fun n => ↥(unregradeGrading N n)) n' ⟨x, hx'⟩ := by
  subst h; rfl

instance unregradeDecomposition : Decomposition (unregradeGrading N) :=
  Decomposition.ofAddHom (unregradeGrading N) (unregradeDecompose N)
    (DirectSum.addHom_ext fun r y => by
      induction y using Decomposition.inductionOn (N r).grading with
      | zero => simp
      | homogeneous y =>
        rw [AddMonoidHom.comp_apply, unregradeDecompose_of_mem N r y.2, coeAddMonoidHom_of]
        rfl
      | add y y' hy hy' => simp only [map_add, hy, hy'])
    (DirectSum.addHom_ext fun n x => by
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy, rfl⟩ := id hx
      rw [AddMonoidHom.comp_apply, coeAddMonoidHom_of, AddMonoidHom.id_apply,
        unregradeDecompose_of_mem N _ hy]
      exact of_congr_unregrade N (ediv_mul_add_val k n) _ _)

variable [IsConcentratedInMultiples 𝒜 k]

/-- The `A`-module structure on `⨁ r, N r`, through `DG.regradeRingHom`. -/
instance unregradeModule : Module A (⨁ r : ZMod k, (N r : Type v)) :=
  Module.compHom _ (regradeRingHom 𝒜 k)

theorem unregrade_smul_def (a : A) (x : ⨁ r : ZMod k, (N r : Type v)) :
    a • x = regradeRingHom 𝒜 k a • x := rfl

instance unregrade_gradedSMul : SetLike.GradedSMul 𝒜 (unregradeGrading N) where
  smul_mem := by
    intro i j a x ha hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [unregrade_smul_def]
    by_cases hi : (k : ℤ) ∣ i
    · rw [regradeRingHom_of_mem (IsConcentratedInMultiples.mem_ediv k ha),
        ← DirectSum.lof_eq_of (RegradeByDivision 𝒜 k 0), ← map_smul, DirectSum.lof_eq_of]
      have hy' := SetLike.GradedSMul.smul_mem (A := regradeGrading 𝒜 k 0)
        (B := (N (j : ZMod k)).grading)
        (RegradeByDivision.mk_mem (i / k) (IsConcentratedInMultiples.mem_ediv k ha)) hy
      rw [vadd_eq_add] at hy'
      exact of_mem_unregradeGrading N
        (by rw [Int.cast_add, (ZMod.intCast_zmod_eq_zero_iff_dvd i k).mpr hi, zero_add])
        (Int.add_ediv_of_dvd_left hi) hy'
    · rw [IsConcentratedInMultiples.eq_zero hi ha, map_zero, zero_smul]
      exact zero_mem _

/-- The graded `A`-module `⨁ r, N r` attached to a family `N` of graded modules over
`⨁ q, A^{q k}`: `A` acts through `DG.regradeRingHom`, and the degree-`n` piece is
`(N (n mod k))^{n / k}`. -/
abbrev unregradeObj : GradedModuleCat.{v} 𝒜 :=
  GradedModuleCat.of 𝒜 (⨁ r : ZMod k, (N r : Type v)) (unregradeGrading N)

variable {N} {N' : ZMod k → GradedModuleCat.{v} (regradeGrading 𝒜 k 0)}

/-- The additive map `⨁ r, N r → ⨁ r, N' r` induced by a family of morphisms. -/
def unregradeMapAddHom (g : N ⟶ N') :
    (⨁ r : ZMod k, (N r : Type v)) →+ ⨁ r : ZMod k, (N' r : Type v) :=
  DirectSum.map fun r => (g r).hom.toAddMonoidHom

omit [NeZero k] [IsConcentratedInMultiples 𝒜 k] in
theorem unregradeMapAddHom_of (g : N ⟶ N') (r : ZMod k) (y : N r) :
    unregradeMapAddHom g (DirectSum.of (fun r => (N r : Type v)) r y) =
      DirectSum.of (fun r => (N' r : Type v)) r ((g r).hom y) :=
  DirectSum.map_of _ _ _

omit [NeZero k] [IsConcentratedInMultiples 𝒜 k] in
@[simp]
theorem unregradeMapAddHom_apply (g : N ⟶ N') (x : ⨁ r : ZMod k, (N r : Type v)) (r : ZMod k) :
    unregradeMapAddHom g x r = (g r).hom (x r) :=
  DirectSum.map_apply _ _ _

/-- The morphism `⨁ r, N r → ⨁ r, N' r` of graded `A`-modules induced by a family of
morphisms. -/
def unregradeMap (g : N ⟶ N') : unregradeObj N ⟶ unregradeObj N' where
  hom :=
    { toFun := unregradeMapAddHom g
      map_add' := map_add _
      map_smul' := fun a x => DirectSum.ext fun r => by
        rw [RingHom.id_apply, unregrade_smul_def, unregrade_smul_def, DirectSum.smul_apply,
          unregradeMapAddHom_apply, unregradeMapAddHom_apply, DirectSum.smul_apply, map_smul] }
  map_mem' := by
    rintro n _ ⟨y, hy, rfl⟩
    change unregradeMapAddHom g (DirectSum.of _ _ y) ∈ _
    rw [unregradeMapAddHom_of]
    exact ⟨_, (g _).map_mem hy, rfl⟩

theorem unregradeMap_apply (g : N ⟶ N') (x : ⨁ r : ZMod k, (N r : Type v)) (r : ZMod k) :
    ((unregradeMap g).hom x : ⨁ r : ZMod k, (N' r : Type v)) r = (g r).hom (x r) :=
  DirectSum.map_apply _ _ _

variable (𝒜 k) in
/-- The functor from families, indexed by `ℤ/k`, of graded modules over `⨁ q, A^{q k}` to
graded `A`-modules: `N ↦ ⨁ r, N r`. -/
def unregrade :
    (ZMod k → GradedModuleCat.{v} (regradeGrading 𝒜 k 0)) ⥤ GradedModuleCat.{v} 𝒜 where
  obj N := unregradeObj N
  map g := unregradeMap g
  map_id N := hom_ext (LinearMap.ext fun x => DirectSum.ext fun r => unregradeMap_apply _ x r)
  map_comp f g := hom_ext (LinearMap.ext fun x => DirectSum.ext fun r => by
    change ((unregradeMap (f ≫ g)).hom x : ⨁ r : ZMod k, _) r =
      ((unregradeMap g).hom ((unregradeMap f).hom x) : ⨁ r : ZMod k, _) r
    rw [unregradeMap_apply, unregradeMap_apply, unregradeMap_apply]
    rfl)

end Unregrade

/-! ### The unit and the counit -/

section Equivalence

variable {𝒜 k} [IsConcentratedInMultiples 𝒜 k]

/-- The residue decomposition `DG.residueEquiv` as an `A`-linear equivalence
`M ≃ ⨁ r, RegradeByDivision ℳ k r`. -/
def regradeUnitLinearEquiv (M : GradedModuleCat.{v} 𝒜) :
    M ≃ₗ[A] ⨁ r : ZMod k, (regradeObj 𝒜 k r M : Type v) where
  toFun := residueEquiv M.grading k
  invFun := (residueEquiv M.grading k).symm
  left_inv := (residueEquiv M.grading k).symm_apply_apply
  right_inv := (residueEquiv M.grading k).apply_symm_apply
  map_add' := map_add _
  map_smul' a m := by
    refine map_smul_of_homogeneous 𝒜 M.grading
      (N := ⨁ r : ZMod k, (regradeObj 𝒜 k r M : Type v))
      (residueEquiv M.grading k).toAddMonoidHom (fun i j a m ha _ => ?_) a m
    change residueEquiv M.grading k (a • m) = regradeRingHom 𝒜 k a • residueEquiv M.grading k m
    rw [regradeRingHom_of_mem (IsConcentratedInMultiples.mem_ediv k ha)]
    exact residueEquiv_smul (𝒜 := 𝒜) (ℳ := M.grading) (n := k)
      (IsConcentratedInMultiples.mem_ediv k ha) m

/-- The unit of the regrading equivalence at `M`: `M ≅ ⨁ r, RegradeByDivision ℳ k r`, given by
the residue decomposition `DG.residueEquiv`. -/
def regradeUnitIsoApp (M : GradedModuleCat.{v} 𝒜) :
    M ≅ (unregrade 𝒜 k).obj ((regrade 𝒜 k).obj M) :=
  isoMk (M := M) (N := unregradeObj (fun r => regradeObj 𝒜 k r M)) (regradeUnitLinearEquiv M)
    (fun n m hm => by
      change residueEquiv M.grading k m ∈ unregradeGrading (fun r => regradeObj 𝒜 k r M) n
      rw [residueEquiv_of_mem M.grading k hm]
      exact ⟨_, RegradeByDivision.mk_mem _ _, rfl⟩)
    (by
      rintro n _ ⟨y, hy, rfl⟩
      obtain ⟨m, hm, rfl⟩ := RegradeByDivision.mem_regradeGrading_iff.mp hy
      change (residueEquiv M.grading k).symm
        (DirectSum.of (fun r : ZMod k => RegradeByDivision M.grading k (r.val : ℤ)) (n : ZMod k)
          (RegradeByDivision.mk M.grading k _ (n / k) m hm)) ∈ M.grading n
      rw [residueEquiv_symm_of_mk]
      rwa [ediv_mul_add_val] at hm)

theorem regradeUnitIsoApp_hom_apply (M : GradedModuleCat.{v} 𝒜) (m : M) :
    (regradeUnitIsoApp M).hom.hom m = residueEquiv M.grading k m := rfl

omit [IsConcentratedInMultiples 𝒜 k] in
theorem regradeUnit_naturality {M M' : GradedModuleCat.{v} 𝒜} (f : M ⟶ M') {n : ℤ} {m : M}
    (hm : m ∈ M.grading n) :
    residueEquiv M'.grading k (f.hom m) =
      unregradeMapAddHom (N := fun r => regradeObj 𝒜 k r M) (N' := fun r => regradeObj 𝒜 k r M')
        (fun r => regradeMap r f) (residueEquiv M.grading k m) := by
  have hm' : m ∈ M.grading (n / k * k + (((n : ZMod k)).val : ℤ)) := by rwa [ediv_mul_add_val]
  have h₁ := residueEquiv_of_mem M'.grading k (f.map_mem hm)
  have h₂ := residueEquiv_of_mem M.grading k hm
  have h₃ := unregradeMapAddHom_of (N := fun r => regradeObj 𝒜 k r M)
    (N' := fun r => regradeObj 𝒜 k r M') (fun r => regradeMap r f) (n : ZMod k)
    (RegradeByDivision.mk M.grading k _ (n / k) m hm')
  have h₄ := regradeMap_mk (n : ZMod k) f (n / k) m hm'
  exact h₁.trans ((congrArg (DirectSum.of (fun r : ZMod k => (regradeObj 𝒜 k r M' : Type v))
    (n : ZMod k)) h₄).symm.trans (h₃.symm.trans (congrArg (unregradeMapAddHom
      (N := fun r => regradeObj 𝒜 k r M) (N' := fun r => regradeObj 𝒜 k r M')
        (fun r => regradeMap r f)) h₂.symm)))

variable (𝒜 k) in
/-- The unit of the regrading equivalence, `M ≅ ⨁ r, RegradeByDivision ℳ k r`. -/
def regradeUnitIso : 𝟭 (GradedModuleCat.{v} 𝒜) ≅ regrade 𝒜 k ⋙ unregrade 𝒜 k :=
  NatIso.ofComponents regradeUnitIsoApp fun f => hom_ext_homogeneous fun _ _ hm =>
    regradeUnit_naturality f hm

variable (N : ZMod k → GradedModuleCat.{v} (regradeGrading 𝒜 k 0)) (r : ZMod k)

/-- The component at `r`: `RegradeByDivision (⨁ r', N r') k r → N r`. -/
def counitAddHom : RegradeByDivision (unregradeGrading N) k (r.val : ℤ) →+ N r where
  toFun x := RegradeByDivision.fold _ k _ x r
  map_zero' := by simp
  map_add' x y := by simp

omit [NeZero k] [IsConcentratedInMultiples 𝒜 k] in
theorem counitAddHom_mk {q : ℤ} {x : ⨁ r : ZMod k, (N r : Type v)}
    (hx : x ∈ unregradeGrading N (q * k + (r.val : ℤ))) :
    counitAddHom N r (RegradeByDivision.mk _ k _ q x hx) = x r := by
  simp [counitAddHom]

/-- The inclusion `N r → RegradeByDivision (⨁ r', N r') k r`. -/
def counitInvAddHom : N r →+ RegradeByDivision (unregradeGrading N) k (r.val : ℤ) :=
  liftHomogeneous (N r).grading fun q =>
    { toFun := fun y => RegradeByDivision.mk _ k _ q (DirectSum.of _ r (y : N r))
        (of_mem_unregradeGrading' N r q y.2)
      map_zero' := by simp
      map_add' := fun y y' => by
        simp only [AddMemClass.coe_add, map_add]
        exact RegradeByDivision.mk_add _ _ _ }

omit [IsConcentratedInMultiples 𝒜 k] in
theorem counitInvAddHom_of_mem {q : ℤ} {y : N r} (hy : y ∈ (N r).grading q) :
    counitInvAddHom N r y =
      RegradeByDivision.mk _ k _ q (DirectSum.of _ r y) (of_mem_unregradeGrading' N r q hy) := by
  rw [counitInvAddHom, liftHomogeneous_of_mem _ _ hy]
  rfl

omit [IsConcentratedInMultiples 𝒜 k] in
theorem counit_aux {r' : ZMod k} (hr : r' = r) {q q' : ℤ} (hq : q' = q) {y : N r'}
    (hy : y ∈ (N r').grading q')
    (hx : DirectSum.of (fun r => (N r : Type v)) r' y ∈
      unregradeGrading N (q * k + (r.val : ℤ))) :
    counitInvAddHom N r (DirectSum.of (fun r => (N r : Type v)) r' y r) =
        RegradeByDivision.mk _ k _ q (DirectSum.of _ r' y) hx ∧
      DirectSum.of (fun r => (N r : Type v)) r' y r ∈ (N r).grading q := by
  subst hr hq
  rw [DirectSum.of_eq_same]
  exact ⟨counitInvAddHom_of_mem N r' hy, hy⟩

omit [IsConcentratedInMultiples 𝒜 k] in
theorem counit_mem {q : ℤ} {x : ⨁ r : ZMod k, (N r : Type v)}
    (hx : x ∈ unregradeGrading N (q * k + (r.val : ℤ))) :
    counitInvAddHom N r (x r) = RegradeByDivision.mk _ k _ q x hx ∧ x r ∈ (N r).grading q := by
  obtain ⟨y, hy, rfl⟩ := id hx
  exact counit_aux N r (intCast_mul_add_val k q r) (mul_add_val_ediv k q r) hy hx

/-- The counit of the regrading equivalence at `r`: the residue class `r` of `⨁ r', N r'` is
`N r`, as a linear equivalence over `⨁ q, A^{q k}`. -/
def counitLinearEquiv :
    RegradeByDivision (unregradeGrading N) k (r.val : ℤ) ≃ₗ[RegradeByDivision 𝒜 k 0] N r where
  toFun := counitAddHom N r
  invFun := counitInvAddHom N r
  map_add' := map_add _
  map_smul' := map_smul_of_homogeneous (regradeGrading 𝒜 k 0)
    (regradeGrading (unregradeGrading N) k (r.val : ℤ)) (counitAddHom N r)
    fun p q b z hb hz => by
      obtain ⟨a, ha, rfl⟩ := RegradeByDivision.mem_regradeGrading_iff.mp hb
      obtain ⟨x, hx, rfl⟩ := RegradeByDivision.mem_regradeGrading_iff.mp hz
      rw [RegradeByDivision.mk_smul_mk, counitAddHom_mk, counitAddHom_mk, unregrade_smul_def,
        DirectSum.smul_apply, regradeRingHom_of_mem ha]
  left_inv z := by
    induction z using RegradeByDivision.induction_on with
    | zero => simp
    | mk q x hx =>
      rw [counitAddHom_mk]
      exact (counit_mem N r hx).1
    | add z z' hz hz' =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hz hz'
  right_inv y := by
    induction y using Decomposition.inductionOn (N r).grading with
    | zero => simp
    | homogeneous y =>
      rw [counitInvAddHom_of_mem N r y.2, counitAddHom_mk, DirectSum.of_eq_same]
    | add y y' hy hy' =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hy hy'

/-- The counit of the regrading equivalence at `r`. -/
def regradeCounitIsoApp : (regrade 𝒜 k).obj ((unregrade 𝒜 k).obj N) r ≅ N r :=
  isoMk (M := regradeObj 𝒜 k r (unregradeObj N)) (N := N r) (counitLinearEquiv N r)
    (fun q z hz => by
      obtain ⟨x, hx, rfl⟩ := RegradeByDivision.mem_regradeGrading_iff.mp hz
      have h := (counit_mem N r hx).2
      rw [← counitAddHom_mk N r hx] at h
      exact h)
    (fun q y hy => by
      change counitInvAddHom N r y ∈ regradeGrading (unregradeGrading N) k (r.val : ℤ) q
      rw [counitInvAddHom_of_mem N r hy]
      exact RegradeByDivision.mk_mem _ _)

variable {N} in
theorem counitAddHom_regradeMap {N' : ZMod k → GradedModuleCat.{v} (regradeGrading 𝒜 k 0)}
    (g : N ⟶ N') (r : ZMod k) (z : RegradeByDivision (unregradeGrading N) k (r.val : ℤ)) :
    counitAddHom N' r ((regradeMap r (unregradeMap g)).hom z) =
      (g r).hom (counitAddHom N r z) := by
  induction z using RegradeByDivision.induction_on with
  | zero => simp
  | mk q x hx =>
    rw [regradeMap_mk, counitAddHom_mk, counitAddHom_mk]
    exact unregradeMap_apply g x r
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]

variable (𝒜 k) in
/-- The counit of the regrading equivalence: the residue classes of `⨁ r, N r` are the `N r`. -/
def regradeCounitIso : unregrade 𝒜 k ⋙ regrade 𝒜 k ≅
    𝟭 (ZMod k → GradedModuleCat.{v} (regradeGrading 𝒜 k 0)) :=
  NatIso.ofComponents (fun N => Pi.isoMk fun r => regradeCounitIsoApp N r)
    fun g => funext fun r => hom_ext (LinearMap.ext fun z =>
      counitAddHom_regradeMap g r z)

variable (𝒜 k) in
/-- **The regrading equivalence for division by `k`.** For a `ℤ`-graded ring `A` concentrated in
degrees divisible by `k ≥ 1`, the category of `ℤ`-graded `A`-modules is equivalent to the
category of families, indexed by `ℤ/k`, of `ℤ`-graded modules over the regraded ring
`⨁ q, A^{q k}`: `M ↦ (RegradeByDivision ℳ k r)_r`, with quasi-inverse `N ↦ ⨁ r, N r` and unit
the residue decomposition `DG.residueEquiv`. -/
def regradeEquivalence :
    GradedModuleCat.{v} 𝒜 ≌ (ZMod k → GradedModuleCat.{v} (regradeGrading 𝒜 k 0)) :=
  CategoryTheory.Equivalence.mk (regrade 𝒜 k) (unregrade 𝒜 k) (regradeUnitIso 𝒜 k)
    (regradeCounitIso 𝒜 k)

end Equivalence

end GradedModuleCat

end DG
