import DG.Bigraded.ModuleCat
import DG.Category.Module
import DG.Category.Weight
import DG.Module.DirectSum

/-!
# Bigraded dg modules are dg modules over `C_A`

For a ring `A` with a dg structure and an internal grading (`DG.BigradedDGRing A`), a bigraded
dg `A`-module is the same as a dg module over the dg category `C_A = DG.WeightCategory A`
(objects `k : ℤ`, `C_A(k, l) = A⟨l - k⟩`):

* a bigraded dg module `M` gives the dg module `k ↦ M⟨k⟩` over `C_A`, on which `a ∈ A⟨l - k⟩`
  acts by `M⟨k⟩ → M⟨l⟩`, `m ↦ a • m` (`DG.BigradedDGModuleCat.toCatModule`);
* a dg module `N` over `C_A` gives the bigraded dg module `⨁ k, N⟨k⟩`
  (`DG.CatModule.WeightSum N`), with the weight grading by the summands and with `a ∈ A⟨j⟩`
  acting on the summand `N⟨k⟩` through `a : k ⟶ k + j` (`DG.CatModule.toBigraded`).

## Main results

* `DG.CatModule.weightEquivalence : CatModule (WeightCategory A) ≌ BigradedDGModuleCat A`, an
  equivalence of categories.
* `DG.BigradedDGModuleCat.internalShiftToCatModuleIso s`: under this equivalence the internal
  shift `M ↦ M⟨s⟩` corresponds to restriction along the shift `k ↦ k + s` of `C_A`
  (`DG.WeightCategory.shiftFunctor`): `(M⟨s⟩)⟨k⟩ = M⟨k + s⟩`.
-/

open CategoryTheory DirectSum

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]

/-! ### Ranges of the summand inclusions -/

section RangeDecomposition

variable {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, AddCommGroup (β i)] {T : Type*}
  [AddCommGroup T] (f : ∀ i, β i →+ T)

/-- If `⨁ i, β i → T` is bijective, then `T` is the internal
direct sum of the ranges of the `f i`. -/
theorem isInternal_range_of_bijective
    (h : Function.Bijective (DirectSum.toAddMonoid f)) :
    DirectSum.IsInternal fun i => (f i).range := by
  let m : (⨁ i, β i) →+ ⨁ i, (f i).range := DirectSum.map fun i => (f i).rangeRestrict
  have hm : ∀ w, DirectSum.coeAddMonoidHom (fun i => (f i).range) (m w) =
      DirectSum.toAddMonoid f w := by
    intro w
    induction w using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of i y =>
      simp only [m, DirectSum.map_of, DirectSum.coeAddMonoidHom_of, DirectSum.toAddMonoid_of,
        AddMonoidHom.coe_rangeRestrict]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsurj : Function.Surjective m := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of i y =>
      obtain ⟨_, y, rfl⟩ := y
      exact ⟨DirectSum.of β i y, by simp only [m, DirectSum.map_of]; rfl⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩
  refine ⟨fun z z' hz => ?_, fun t => ?_⟩
  · obtain ⟨w, rfl⟩ := hsurj z
    obtain ⟨w', rfl⟩ := hsurj z'
    rw [hm, hm] at hz
    rw [h.1 hz]
  · obtain ⟨w, rfl⟩ := h.2 t
    exact ⟨m w, hm w⟩

/-- The components of the decomposition by the ranges of the `f i`. -/
theorem coe_decompose_range [Decomposition fun i => (f i).range]
    (w : ⨁ i, β i) (i : ι) :
    (decompose (fun i => (f i).range) (DirectSum.toAddMonoid f w) i : T) = f i (w i) := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [DirectSum.toAddMonoid_of]
    by_cases h : j = i
    · subst h
      rw [decompose_of_mem_same (fun i => (f i).range) (AddMonoidHom.mem_range.mpr ⟨y, rfl⟩),
        DirectSum.of_eq_same]
    · rw [decompose_of_mem_ne (fun i => (f i).range) (AddMonoidHom.mem_range.mpr ⟨y, rfl⟩) h,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
  | add x y hx hy =>
    simp only [map_add, decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, hx, hy]

end RangeDecomposition

namespace WeightCategory

/-- The morphism `⟨k⟩ ⟶ ⟨l⟩` of `C_A` given by an element `a ∈ A⟨j⟩`, for `l - k = j`. -/
def homOfMem {j : ℤ} {a : A} (ha : a ∈ wgrading (M := A) j) (k l : ℤ) (h : l - k = j) :
    (⟨k⟩ : WeightCategory A) ⟶ ⟨l⟩ :=
  ⟨a, show a ∈ wgrading (M := A) (l - k) by rw [h]; exact ha⟩

@[simp]
theorem homOfMem_val {j : ℤ} {a : A} (ha : a ∈ wgrading (M := A) j) (k l : ℤ) (h : l - k = j) :
    (homOfMem ha k l h).1 = a := rfl

end WeightCategory

open WeightCategory

/-! ### From bigraded dg modules to dg modules over `C_A` -/

namespace BigradedDGModuleCat

variable (M : BigradedDGModuleCat.{v} A)

/-- The action of `C_A` on the weight components of a bigraded dg module:
`a ∈ A⟨l - k⟩` maps `M⟨k⟩` to `M⟨l⟩`. -/
def weightAct {k l : WeightCategory A} :
    (k ⟶ l) →+ wgrading (M := M) k.as →+ wgrading (M := M) l.as :=
  AddMonoidHom.mk'
    (fun f => AddMonoidHom.mk'
      (fun m => ⟨f.1 • m.1, by simpa using smul_mem_wgrading f.2 m.2⟩)
      fun m m' => Subtype.ext (smul_add f.1 m.1 m'.1))
    fun f g => by
      ext m
      exact add_smul f.1 g.1 m.1

/-- A bigraded dg module as a dg module over `C_A`: `k ↦ M⟨k⟩`. -/
def toCatModuleObj : CatModule.{v} (WeightCategory A) where
  obj k := wgrading (M := M) k.as
  act := weightAct M
  act_mem' hf hm := smul_mem_grading (A := A) (M := M) hf hm
  act_id' _ m := Subtype.ext (one_smul A m.1)
  act_comp' f g m := Subtype.ext (mul_smul g.1 f.1 m.1)
  d_act' {k l i f} hf m := Subtype.ext (by
    change d (f.1 • m.1) = d f.1 • m.1 + ((koszulSign i : ℤ) • (f.1 • d m.1))
    rw [d_smul (A := A) (a := f.1) hf, Units.smul_def])

@[simp]
theorem toCatModuleObj_obj (k : WeightCategory A) :
    (toCatModuleObj M).obj k = wgrading (M := M) k.as := rfl

theorem toCatModuleObj_smul {k l : WeightCategory A} (f : k ⟶ l)
    (m : (toCatModuleObj M).obj k) : (f • m : (toCatModuleObj M).obj l).1 = f.1 • m.1 := rfl

variable (A) in
/-- The functor from bigraded dg `A`-modules to dg modules over `C_A`, `M ↦ (k ↦ M⟨k⟩)`. -/
@[simps obj]
def toCatModule : BigradedDGModuleCat.{v} A ⥤ CatModule.{v} (WeightCategory A) where
  obj M := toCatModuleObj M
  map {M N} φ :=
    { app := fun k => AddMonoidHom.mk'
        (fun m => ⟨φ.hom m.1, φ.map_mem_wgrading m.2⟩) fun m m' => Subtype.ext (map_add _ _ _)
      map_mem' := fun hm => φ.hom.map_mem hm
      map_d' := fun m => Subtype.ext (φ.hom.map_d m.1)
      map_smul' := fun f m => Subtype.ext (φ.hom.map_smul f.1 m.1) }

@[simp]
theorem toCatModule_map_app_coe {M N : BigradedDGModuleCat.{v} A} (φ : M ⟶ N)
    (k : WeightCategory A) (m : (toCatModuleObj M).obj k) :
    (((toCatModule A).map φ).app k m).1 = φ.hom m.1 := rfl

end BigradedDGModuleCat

/-! ### From dg modules over `C_A` to bigraded dg modules -/

namespace CatModule

variable (N : CatModule.{v} (WeightCategory A))

/-- The underlying group of the bigraded dg module attached to a dg module over `C_A`:
`⨁ k, N⟨k⟩`. -/
abbrev WeightSum : Type v :=
  ⨁ k : ℤ, N.obj ⟨k⟩

/-- The inclusion of the summand `N⟨k⟩` into `⨁ k, N⟨k⟩`. -/
abbrev weightSumOf (k : ℤ) : N.obj ⟨k⟩ →+ N.WeightSum :=
  DirectSum.of (fun k => N.obj ⟨k⟩) k

theorem weightSum_mem_grading_iff {n : ℤ} {x : N.WeightSum} :
    x ∈ grading n ↔ ∀ k, x k ∈ grading n :=
  Iff.rfl

/-- Moving a summand along an equality of indices. -/
theorem of_act_eq {k l l' : ℤ} (h : l = l') (f : (⟨k⟩ : WeightCategory A) ⟶ ⟨l⟩)
    (f' : (⟨k⟩ : WeightCategory A) ⟶ ⟨l'⟩) (hf : f.1 = f'.1) (y : N.obj ⟨k⟩) :
    weightSumOf N l (f • y) =
      weightSumOf N l' (f' • y) := by
  subst h
  rw [Subtype.ext hf]

/-- The action of the elements of `A⟨j⟩` on `⨁ k, N⟨k⟩`. -/
def weightSumActHom (j : ℤ) : wgrading (M := A) j →+ N.WeightSum →+ N.WeightSum :=
  AddMonoidHom.mk'
    (fun a => DirectSum.toAddMonoid fun k =>
      (weightSumOf N (k + j)).comp
        (N.act (homOfMem a.2 k (k + j) (by ring))))
    fun a b => DirectSum.addHom_ext fun k y => by
      have : homOfMem (a + b).2 k (k + j) (by ring) =
          homOfMem a.2 k (k + j) (by ring) + homOfMem b.2 k (k + j) (by ring) := Subtype.ext rfl
      simp only [DirectSum.toAddMonoid_of, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, this,
        map_add]

/-- The action of `A` on `⨁ k, N⟨k⟩`, through the weight decomposition of `A`. -/
def weightSumSMulHom : A →+ N.WeightSum →+ N.WeightSum :=
  (DirectSum.toAddMonoid (weightSumActHom N)).comp
    (decomposeAddEquiv (wgrading (M := A))).toAddMonoidHom

instance : SMul A N.WeightSum :=
  ⟨fun a x => weightSumSMulHom N a x⟩

theorem weightSum_smul_def (a : A) (x : N.WeightSum) : a • x = weightSumSMulHom N a x := rfl

/-- The action of a homogeneous element on a summand. -/
theorem weightSum_smul_of {j : ℤ} {a : A} (ha : a ∈ wgrading (M := A) j) (k : ℤ)
    (y : N.obj ⟨k⟩) :
    a • weightSumOf N k y =
      weightSumOf N (k + j) (homOfMem ha k (k + j) (by ring) • y) := by
  rw [weightSum_smul_def, weightSumSMulHom, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, decomposeAddEquiv_apply, decompose_of_mem _ ha, DirectSum.toAddMonoid_of]
  erw [DirectSum.toAddMonoid_of]
  rfl

theorem weightSum_add_smul (a b : A) (x : N.WeightSum) : (a + b) • x = a • x + b • x := by
  simp only [weightSum_smul_def, map_add, AddMonoidHom.add_apply]

theorem weightSum_smul_add (a : A) (x y : N.WeightSum) : a • (x + y) = a • x + a • y := by
  simp only [weightSum_smul_def, map_add]

theorem weightSum_zero_smul (x : N.WeightSum) : (0 : A) • x = 0 := by
  simp only [weightSum_smul_def, map_zero, AddMonoidHom.zero_apply]

theorem weightSum_smul_zero (a : A) : a • (0 : N.WeightSum) = 0 := by
  simp only [weightSum_smul_def, map_zero]

theorem weightSum_one_smul (x : N.WeightSum) : (1 : A) • x = x := by
  induction x using DirectSum.induction_on with
  | zero => exact weightSum_smul_zero N 1
  | of k y =>
    rw [weightSum_smul_of N one_mem_wgrading,
      of_act_eq N (add_zero k) _ (𝟙 (⟨k⟩ : WeightCategory A)) rfl, id_smul]
  | add x y hx hy => rw [weightSum_smul_add, hx, hy]

theorem weightSum_mul_smul (a b : A) (x : N.WeightSum) : (a * b) • x = a • b • x := by
  induction a using DirectSum.Decomposition.inductionOn (wgrading (M := A)) with
  | zero => simp only [zero_mul, weightSum_zero_smul]
  | add a a' ha ha' => rw [add_mul, weightSum_add_smul, weightSum_add_smul, ha, ha']
  | homogeneous a =>
    rename_i i
    induction b using DirectSum.Decomposition.inductionOn (wgrading (M := A)) with
    | zero => simp only [mul_zero, weightSum_zero_smul, weightSum_smul_zero]
    | add b b' hb hb' => rw [mul_add, weightSum_add_smul, weightSum_add_smul, hb, hb',
        weightSum_smul_add]
    | homogeneous b =>
      rename_i j
      induction x using DirectSum.induction_on with
      | zero => simp only [weightSum_smul_zero]
      | add x y hx hy => rw [weightSum_smul_add, weightSum_smul_add, weightSum_smul_add, hx, hy]
      | of k y =>
        rw [weightSum_smul_of N (mul_mem_wgrading a.2 b.2), weightSum_smul_of N b.2,
          weightSum_smul_of N a.2, ← comp_smul]
        exact of_act_eq N (show k + (i + j) = k + j + i by ring) _ _ rfl y

/-- `⨁ k, N⟨k⟩` is an `A`-module. -/
instance instModule : Module A N.WeightSum where
  one_smul := weightSum_one_smul N
  mul_smul := weightSum_mul_smul N
  smul_zero := weightSum_smul_zero N
  smul_add := weightSum_smul_add N
  add_smul a b := weightSum_add_smul N a b
  zero_smul := weightSum_zero_smul N

theorem weightSum_smul_mem_grading {i j : ℤ} {a : A} (ha : a ∈ grading i) {x : N.WeightSum}
    (hx : x ∈ grading j) : a • x ∈ grading (i + j) := by
  classical
  rw [← DirectSum.sum_support_decompose (wgrading (M := A)) a, ← DirectSum.sum_support_of x,
    Finset.sum_smul]
  refine sum_mem fun l _ => ?_
  rw [Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [weightSum_smul_of N (decompose (wgrading (M := A)) a l).2]
  exact DG.DirectSum.of_mem_grading _ _
    (smul_mem_grading (M := N) (decompose_wgrading_mem_grading ha l) (hx k))

theorem weightSum_d_of (k : ℤ) (y : N.obj ⟨k⟩) :
    d (weightSumOf N k y) = weightSumOf N k (d y) :=
  DG.DirectSum.d_of (fun k => N.obj ⟨k⟩) k y

theorem weightSum_d_smul {n : ℤ} {a : A} (ha : a ∈ grading n) (x : N.WeightSum) :
    d (a • x) = d a • x + koszulSign n • (a • d x) := by
  classical
  have hom : ∀ (l : ℤ) (b : A), b ∈ wgrading (M := A) l → b ∈ grading n → ∀ x : N.WeightSum,
      d (b • x) = d b • x + koszulSign n • (b • d x) := by
    intro l b hbl hbn x
    induction x using DirectSum.induction_on with
    | zero => rw [weightSum_smul_zero, weightSum_smul_zero, d_zero, weightSum_smul_zero,
        Units.smul_def, zsmul_zero, add_zero]
    | add x y hx hy => rw [weightSum_smul_add, d_add, hx, hy, d_add, weightSum_smul_add,
        weightSum_smul_add, _root_.smul_add]; abel
    | of k y =>
      rw [weightSum_smul_of N hbl, weightSum_d_of, weightSum_d_of, weightSum_smul_of N hbl,
        weightSum_smul_of N (d_mem_wgrading hbl),
        CatModule.d_smul (M := N) (f := homOfMem hbl k (k + l) (by ring)) hbn, map_add,
        Units.smul_def, Units.smul_def, map_zsmul]
      rfl
  rw [← DirectSum.sum_support_decompose (wgrading (M := A)) a]
  simp only [map_sum, Finset.sum_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => hom l _ (decompose (wgrading (M := A)) a l).2
    (decompose_wgrading_mem_grading ha l) x

/-- `⨁ k, N⟨k⟩` is a dg `A`-module. -/
instance instDGModule : DGModule A N.WeightSum where
  smul_mem _ _ _ _ ha hx := weightSum_smul_mem_grading N ha hx
  d_smul' ha x := weightSum_d_smul N ha x

/-- The weight grading of `⨁ k, N⟨k⟩`: `(⨁ k, N⟨k⟩)⟨k⟩ = N⟨k⟩`. -/
abbrev weightSumGrading (k : ℤ) : AddSubgroup N.WeightSum :=
  (weightSumOf N k).range

theorem of_mem_weightSumGrading (k : ℤ) (y : N.obj ⟨k⟩) :
    weightSumOf N k y ∈ weightSumGrading N k :=
  ⟨y, rfl⟩

theorem weightSum_toAddMonoid_of (x : N.WeightSum) :
    DirectSum.toAddMonoid (weightSumOf N) x = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of k y => exact DirectSum.toAddMonoid_of (weightSumOf N) k y
  | add x y hx hy => rw [map_add, hx, hy]

/-- The decomposition of `⨁ k, N⟨k⟩` by its summands. -/
instance weightSumDecomposition : Decomposition (weightSumGrading N) :=
  (isInternal_range_of_bijective (weightSumOf N)
    ⟨fun x y h => by rwa [weightSum_toAddMonoid_of, weightSum_toAddMonoid_of] at h,
      fun x => ⟨x, weightSum_toAddMonoid_of N x⟩⟩).chooseDecomposition

theorem coe_decompose_weightSumGrading (x : N.WeightSum) (k : ℤ) :
    (decompose (weightSumGrading N) x k : N.WeightSum) = weightSumOf N k (x k) := by
  conv_lhs => rw [← weightSum_toAddMonoid_of N x]
  exact coe_decompose_range (weightSumOf N) x k

/-- The internal grading of `⨁ k, N⟨k⟩` by its summands. -/
instance instInternalGrading : InternalGrading N.WeightSum where
  wgrading := weightSumGrading N
  isHomogeneous_grading' n k x hx := by
    rw [coe_decompose_weightSumGrading]
    exact DG.DirectSum.of_mem_grading _ k (hx k)
  d_mem_wgrading' := by
    rintro k _ ⟨y, rfl⟩
    exact ⟨d y, (weightSum_d_of N k y).symm⟩

theorem mem_wgrading_weightSum_iff {k : ℤ} {x : N.WeightSum} :
    x ∈ wgrading k ↔ ∃ y, weightSumOf N k y = x :=
  Iff.rfl

/-- `⨁ k, N⟨k⟩` is a bigraded dg `A`-module. -/
instance instBigradedDGModule : BigradedDGModule A N.WeightSum where
  smul_mem := by
    rintro i j a _ ha ⟨y, rfl⟩
    rw [weightSum_smul_of N ha, of_act_eq N (add_comm j i) _ (homOfMem ha j (i + j) (by ring)) rfl]
    exact of_mem_weightSumGrading N _ _

/-- The bigraded dg `A`-module `⨁ k, N⟨k⟩` attached to a dg module over `C_A`. -/
abbrev toBigradedObj : BigradedDGModuleCat.{v} A :=
  BigradedDGModuleCat.of A N.WeightSum

variable {N} in
/-- The morphism of bigraded dg modules induced by a morphism of dg modules over `C_A`. -/
def weightSumMap {N' : CatModule.{v} (WeightCategory A)} (φ : N ⟶ N') :
    N.WeightSum →ᵈᵍ[A] N'.WeightSum where
  toFun := DirectSum.map fun k => φ.app ⟨k⟩
  map_add' := map_add _
  map_smul' a x := by
    induction a using DirectSum.Decomposition.inductionOn (wgrading (M := A)) with
    | zero => simp only [_root_.zero_smul, map_zero]
    | add a a' ha ha' => simp only [_root_.add_smul, map_add, ha, ha', RingHom.id_apply]
    | homogeneous a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [_root_.smul_zero, map_zero, RingHom.id_apply]
      | add x y hx hy => simp only [_root_.smul_add, map_add, hx, hy, RingHom.id_apply]
      | of k y =>
        rw [RingHom.id_apply, weightSum_smul_of N a.2, DirectSum.map_of, DirectSum.map_of,
          weightSum_smul_of N' a.2, φ.map_smul]
  map_mem' {n x} hx k := by
    change (DirectSum.map (fun k => φ.app ⟨k⟩) x) k ∈ _
    rw [DirectSum.map_apply]
    exact φ.map_mem (hx k)
  map_d' x := by
    ext k
    change (DirectSum.map (fun k => φ.app ⟨k⟩) (d x)) k = d (DirectSum.map (fun k => φ.app ⟨k⟩) x) k
    rw [DirectSum.map_apply, DG.DirectSum.coe_d_apply, DG.DirectSum.coe_d_apply,
      DirectSum.map_apply, φ.map_d]

variable {N} in
theorem weightSumMap_of {N' : CatModule.{v} (WeightCategory A)} (φ : N ⟶ N') (k : ℤ)
    (y : N.obj ⟨k⟩) :
    weightSumMap φ (weightSumOf N k y) =
      weightSumOf N' k (φ.app ⟨k⟩ y) :=
  DirectSum.map_of _ _ _

variable (A) in
/-- The functor from dg modules over `C_A` to bigraded dg `A`-modules, `N ↦ ⨁ k, N⟨k⟩`. -/
@[simps obj]
def toBigraded : CatModule.{v} (WeightCategory A) ⥤ BigradedDGModuleCat.{v} A where
  obj N := toBigradedObj N
  map φ := ⟨weightSumMap φ, by
    rintro k _ ⟨y, rfl⟩
    exact ⟨φ.app ⟨k⟩ y, (weightSumMap_of φ k y).symm⟩⟩
  map_id N := BigradedDGModuleCat.hom_ext_apply fun x => by
    change DirectSum.map (fun k => AddMonoidHom.id _) x = x
    ext k
    rw [DirectSum.map_apply]
    rfl
  map_comp φ ψ := BigradedDGModuleCat.hom_ext_apply fun x => by
    ext k
    change (DirectSum.map (fun k => (φ ≫ ψ).app ⟨k⟩) x) k =
      (DirectSum.map (fun k => ψ.app ⟨k⟩) (DirectSum.map (fun k => φ.app ⟨k⟩) x)) k
    rw [DirectSum.map_apply, DirectSum.map_apply, DirectSum.map_apply]
    rfl

end CatModule

/-! ### The equivalence -/

namespace BigradedDGModuleCat

variable (M : BigradedDGModuleCat.{v} A)

theorem coe_smul_weightSum (a : A) (x : (toCatModuleObj M).WeightSum) :
    ((decomposeAddEquiv (wgrading (M := M))).symm (a • x) : M) =
      a • (decomposeAddEquiv (wgrading (M := M))).symm x := by
  induction a using DirectSum.Decomposition.inductionOn (wgrading (M := A)) with
  | zero => simp only [zero_smul, map_zero]
  | add a a' ha ha' => simp only [add_smul, map_add, ha, ha']
  | homogeneous a =>
    induction x using DirectSum.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | of k y =>
      rw [CatModule.weightSum_smul_of _ a.2]
      change DirectSum.coeAddMonoidHom (wgrading (M := M)) (DirectSum.of _ _ _) =
        (a : A) • DirectSum.coeAddMonoidHom (wgrading (M := M)) (DirectSum.of _ k y)
      rw [DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
      rfl

/-- The weight decomposition `M ≃ ⨁ k, M⟨k⟩` as an isomorphism of dg modules. -/
def weightDecomposeEquiv : M ≃ᵈᵍ[A] (toCatModuleObj M).WeightSum where
  toFun := decompose (wgrading (M := M))
  invFun := (decompose (wgrading (M := M))).symm
  left_inv := (decompose (wgrading (M := M))).symm_apply_apply
  right_inv := (decompose (wgrading (M := M))).apply_symm_apply
  map_add' := decompose_add (wgrading (M := M))
  map_smul' a m := (decomposeAddEquiv (wgrading (M := M))).symm.injective (by
    rw [RingHom.id_apply, coe_smul_weightSum]
    exact ((decompose (wgrading (M := M))).symm_apply_apply _).trans
      (congrArg (a • ·) ((decompose (wgrading (M := M))).symm_apply_apply m).symm))
  map_mem' {n m} hm k := by
    change (decompose (wgrading (M := M)) m k : M) ∈ grading (M := M) n
    exact decompose_wgrading_mem_grading hm k
  map_d' m := by
    ext k
    change (decompose (wgrading (M := M)) (d m) k : M) =
      d (decompose (wgrading (M := M)) m k : M)
    exact decompose_wgrading_d m k

theorem weightDecomposeEquiv_apply (m : M) :
    weightDecomposeEquiv M m = decompose (wgrading (M := M)) m := rfl

theorem mem_wgrading_weightDecomposeEquiv_iff {k : ℤ} {m : M} :
    weightDecomposeEquiv M m ∈ wgrading k ↔ m ∈ wgrading k := by
  constructor
  · rintro ⟨y, hy⟩
    have h := congrArg (decompose (wgrading (M := M))).symm hy
    rw [weightDecomposeEquiv_apply, Equiv.symm_apply_apply] at h
    change DirectSum.coeAddMonoidHom _ (DirectSum.of _ k y) = m at h
    rw [DirectSum.coeAddMonoidHom_of] at h
    rw [← h]
    exact y.2
  · intro hm
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [weightDecomposeEquiv_apply, decompose_of_mem _ hm]
    rfl

/-- `M ≅ ⨁ k, M⟨k⟩` in `BigradedDGModuleCat A`. -/
def unitIsoApp : M ≅ (CatModule.toBigraded A).obj ((toCatModule A).obj M) :=
  isoMk (weightDecomposeEquiv M) (mem_wgrading_weightDecomposeEquiv_iff M)

variable {M} in
omit [BigradedDGRing A] in
theorem decompose_hom_apply {N : BigradedDGModuleCat.{v} A} (φ : M ⟶ N) (m : M) (k : ℤ) :
    (decompose (wgrading (M := N)) (φ.hom m) k : N) =
      φ.hom (decompose (wgrading (M := M)) m k) := by
  induction m using DirectSum.Decomposition.inductionOn (wgrading (M := M)) with
  | zero => simp
  | homogeneous m =>
    rename_i j
    by_cases h : j = k
    · subst h
      rw [decompose_of_mem_same _ m.2, decompose_of_mem_same _ (φ.map_mem_wgrading m.2)]
    · rw [decompose_of_mem_ne _ m.2 h, decompose_of_mem_ne _ (φ.map_mem_wgrading m.2) h,
        map_zero]
  | add m m' hm hm' => simp only [map_add, decompose_add, add_apply, AddSubgroup.coe_add, hm, hm']

end BigradedDGModuleCat

namespace CatModule

variable (N : CatModule.{v} (WeightCategory A))

/-- `N⟨k⟩ ≅ (⨁ l, N⟨l⟩)⟨k⟩`, the inclusion of the summand. -/
def summandAddEquiv (k : WeightCategory A) :
    N.obj k ≃+ ((BigradedDGModuleCat.toCatModule A).obj ((toBigraded A).obj N)).obj k :=
  AddMonoidHom.ofInjective (DirectSum.of_injective (β := fun k => N.obj ⟨k⟩) k.as)

theorem coe_summandAddEquiv_apply (k : WeightCategory A) (y : N.obj k) :
    (summandAddEquiv N k y).1 = weightSumOf N k.as y := rfl

/-- `N ≅ (k ↦ (⨁ l, N⟨l⟩)⟨k⟩)` in `CatModule C_A`. -/
def counitIsoApp : N ≅ (BigradedDGModuleCat.toCatModule A).obj ((toBigraded A).obj N) :=
  isoMk (summandAddEquiv N)
    (fun {k n y} => by
      change (∀ l, weightSumOf N k.as y l ∈ grading n) ↔ y ∈ grading n
      refine ⟨fun h => by simpa using h k.as, fun h => DG.DirectSum.of_mem_grading _ k.as h⟩)
    (fun {k} y => Subtype.ext (weightSum_d_of N k.as y).symm)
    (fun {k l} f y => Subtype.ext (by
      change weightSumOf N l.as (f • y) =
        f.1 • weightSumOf N k.as y
      rw [weightSum_smul_of N f.2]
      exact of_act_eq N (show l.as = k.as + (l.as - k.as) by ring) f _ rfl y))

variable (A) in
/-- Dg modules over `C_A` are the same as bigraded dg `A`-modules: the equivalence
`N ↦ ⨁ k, N⟨k⟩`, with inverse `M ↦ (k ↦ M⟨k⟩)`. -/
def weightEquivalence : CatModule.{v} (WeightCategory A) ≌ BigradedDGModuleCat.{v} A :=
  (CategoryTheory.Equivalence.mk (BigradedDGModuleCat.toCatModule A) (toBigraded A)
    (NatIso.ofComponents BigradedDGModuleCat.unitIsoApp fun {M M'} φ =>
      BigradedDGModuleCat.hom_ext_apply fun m => by
        refine DFinsupp.ext fun k => Subtype.ext ?_
        change (decompose (wgrading (M := M')) (φ.hom m) k : M') =
          φ.hom (decompose (wgrading (M := M)) m k)
        exact BigradedDGModuleCat.decompose_hom_apply φ m k)
    (NatIso.ofComponents (fun N => (counitIsoApp N).symm) fun {N N'} φ =>
      hom_ext fun k x => by
        obtain ⟨y, rfl⟩ := (summandAddEquiv N k).surjective x
        change (summandAddEquiv N' k).symm _ = φ.app k ((summandAddEquiv N k).symm _)
        rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_eq]
        exact Subtype.ext (weightSumMap_of φ k.as y))).symm

@[simp]
theorem weightEquivalence_functor : (weightEquivalence A).functor = toBigraded A := rfl

@[simp]
theorem weightEquivalence_inverse :
    (weightEquivalence A).inverse = BigradedDGModuleCat.toCatModule A := rfl

end CatModule

/-! ### The internal shift -/

namespace BigradedDGModuleCat

/-- Under `M ↦ (k ↦ M⟨k⟩)`, the internal shift `M ↦ M⟨s⟩` corresponds to restriction along the
shift `k ↦ k + s` of `C_A`: `(M⟨s⟩)⟨k⟩ = M⟨k + s⟩`. -/
def internalShiftToCatModuleIso (s : ℤ) :
    internalShiftFunctor s ⋙ toCatModule.{v} A ≅
      toCatModule A ⋙ CatModule.precomp (WeightCategory.shiftFunctor A s) :=
  NatIso.ofComponents (fun _ => CatModule.isoMk
    (fun _ => { toFun := fun m => ⟨m.1, m.2⟩
                invFun := fun m => ⟨m.1, m.2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl
                map_add' := fun _ _ => rfl })
    Iff.rfl (fun _ => rfl) (fun _ _ => rfl)) fun _ => rfl

end BigradedDGModuleCat

end DG
