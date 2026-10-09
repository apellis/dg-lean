import DG.Derived.TriangularBasis
import DG.Module.HomAction

/-!
# The dual of a right dg module

Let `A` be a dg ring and `M` a right dg `A`-module (`DG.DGRightModule`).

* `RightDual A M`: the graded dual `M^∨ = HOM_A(M, A)`, the additive maps `f : M → A` which are
  finite sums of homogeneous right `A`-linear maps (`f (m a) = f(m) a`; no sign appears since `f`
  is written on the left and the scalars act on the right). Its degree-`k` part
  (`RightDual.grade`) consists of the maps raising degrees by `k`, and its differential is the
  differential of the Hom complex, `(d f)(m) = d(f m) - (-1)^{|f|} f(d m)`
  (`RightDual.d_apply_of_mem`): a dg abelian group (`RightDual.instDGAddCommGroup`).
* `M^∨` is a left dg `A`-module, `(a f)(m) = a f(m)` (`RightDual.instDGModule`).
* If `M` is a dg `(B, A)`-bimodule, `M^∨` is a right dg `B`-module, `(f b)(m) = f(b m)`, and a
  dg `(A, B)`-bimodule (`RightDual.instDGRightModule`, `RightDual.instDGBimodule`).
* `RightBasis A M ι`: a finite homogeneous basis `(b_i)` of `M` as a right `A`-module, given by
  its coefficient functions. Then every right `A`-linear map `M → A` belongs to `M^∨`
  (`RightBasis.ofRightLinear`), the dual basis `δ_i` (`δ_i(b_j a) = δ_{ij} a`, of degree
  `-|b_i|`) is a homogeneous basis of the left `A`-module `M^∨` (`RightBasis.dualBasis`), and
  `(d δ_i)(b_l) = -(-1)^{|b_i|} (coefficient of b_i in d b_l)`
  (`RightBasis.dualBasis_coeff_d`).
* Consequently, if the basis of `M` is triangular for the differential (`d b_l` involves only
  the `b_i` with `key i < key l`), the dual basis is triangular in the opposite order
  (`RightBasis.dualTriangular`): `M^∨` is a finite-cell left dg `A`-module with cells
  `A⟦|b_i|⟧`, hence K-projective and cofibrant (`RightBasis.dual_isKProjective`,
  `RightBasis.dual_hasLiftingProperty`).
-/

universe w

open MulOpposite DirectSum

set_option linter.unusedSectionVars false

namespace DG

noncomputable section

/-! ## The graded dual as an abelian group -/

section Group

variable (A : Type*) [Ring A] [DGAddCommGroup A]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M]

/-- The right `A`-linear maps `M → A` raising degrees by `k`. -/
def dualPiece (k : ℤ) : AddSubgroup (M →+ A) where
  carrier := {f | (∀ (a : A) (m : M), f (op a • m) = f m * a) ∧
    ∀ (i : ℤ) (m : M), m ∈ grading i → f m ∈ grading (i + k)}
  zero_mem' := ⟨fun a m => by
    rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, zero_mul], fun _ _ _ => zero_mem _⟩
  add_mem' {f g} hf hg := ⟨fun a m => by
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hf.1, hg.1, add_mul],
    fun i m hm => add_mem (hf.2 i m hm) (hg.2 i m hm)⟩
  neg_mem' {f} hf := ⟨fun a m => by
    rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, hf.1, neg_mul],
    fun i m hm => neg_mem (hf.2 i m hm)⟩

/-- The finite sums of homogeneous right `A`-linear maps `M → A`. -/
def dualSubgroup : AddSubgroup (M →+ A) := ⨆ k, dualPiece A M k

/-- **The graded dual** `M^∨ = HOM_A(M, A)` of a right dg `A`-module `M`: the finite sums of
homogeneous right `A`-linear maps `M → A`. -/
def RightDual : Type _ := dualSubgroup A M

namespace RightDual

variable {A M}

instance instAddCommGroup : AddCommGroup (RightDual A M) :=
  inferInstanceAs (AddCommGroup (dualSubgroup A M))

/-- The underlying additive map. -/
def toHom (f : RightDual A M) : M →+ A := Subtype.val (p := (· ∈ dualSubgroup A M)) f

theorem toHom_mem (f : RightDual A M) : toHom f ∈ dualSubgroup A M :=
  Subtype.property (p := (· ∈ dualSubgroup A M)) f

/-- An element of `M^∨` from an additive map in the span of the homogeneous right-linear maps. -/
def mk (g : M →+ A) (hg : g ∈ dualSubgroup A M) : RightDual A M := ⟨g, hg⟩

@[simp] theorem toHom_mk (g : M →+ A) (hg : g ∈ dualSubgroup A M) : toHom (mk g hg) = g := rfl

theorem toHom_injective : Function.Injective (toHom (A := A) (M := M)) := fun _ _ h =>
  Subtype.ext h

@[ext] theorem ext {f g : RightDual A M} (h : ∀ m, toHom f m = toHom g m) : f = g :=
  toHom_injective (AddMonoidHom.ext h)

@[simp] theorem toHom_add (f g : RightDual A M) : toHom (f + g) = toHom f + toHom g := rfl
@[simp] theorem toHom_zero : toHom (0 : RightDual A M) = 0 := rfl
@[simp] theorem toHom_neg (f : RightDual A M) : toHom (-f) = -toHom f := rfl
@[simp] theorem toHom_sub (f g : RightDual A M) : toHom (f - g) = toHom f - toHom g := rfl
@[simp] theorem toHom_zsmul (k : ℤ) (f : RightDual A M) : toHom (k • f) = k • toHom f := rfl

/-- `f ↦ f`, as an additive map. -/
def toHomAddHom (A : Type*) [Ring A] [DGAddCommGroup A] (M : Type*) [AddCommGroup M]
    [DGAddCommGroup M] [Module Aᵐᵒᵖ M] : RightDual A M →+ (M →+ A) where
  toFun := toHom
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem toHom_sum {ι : Type*} (s : Finset ι) (f : ι → RightDual A M) :
    toHom (∑ i ∈ s, f i) = ∑ i ∈ s, toHom (f i) :=
  map_sum (toHomAddHom A M) f s

theorem toHom_units_smul (u : ℤˣ) (f : RightDual A M) : toHom (u • f) = u • toHom f := rfl

/-- Elements of `M^∨` are right `A`-linear. -/
theorem map_op_smul (f : RightDual A M) (a : A) (m : M) : toHom f (op a • m) = toHom f m * a := by
  refine AddSubgroup.iSup_induction (dualPiece A M) (C := fun g => g (op a • m) = g m * a)
    (toHom_mem f) (fun k g hg => hg.1 a m) ?_ fun g g' hg hg' => ?_
  · rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, zero_mul]
  · rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hg, hg', add_mul]

variable (A M) in
/-- The maps of degree `k` in `M^∨`: `Mⁱ` goes to `Aⁱ⁺ᵏ`. -/
def grade (k : ℤ) : AddSubgroup (RightDual A M) where
  carrier := {f | ∀ (i : ℤ) (m : M), m ∈ grading i → toHom f m ∈ grading (i + k)}
  zero_mem' _ _ _ := zero_mem _
  add_mem' hf hg i m hm := add_mem (hf i m hm) (hg i m hm)
  neg_mem' hf i m hm := neg_mem (hf i m hm)

theorem mem_grade {k : ℤ} {f : RightDual A M} :
    f ∈ grade A M k ↔ ∀ (i : ℤ) (m : M), m ∈ grading i → toHom f m ∈ grading (i + k) := Iff.rfl

theorem toHom_mem_dualPiece {k : ℤ} {f : RightDual A M} (hf : f ∈ grade A M k) :
    toHom f ∈ dualPiece A M k :=
  ⟨map_op_smul f, hf⟩

/-- A homogeneous right-linear map as an element of `M^∨`. -/
def ofPiece {k : ℤ} (g : M →+ A) (hg : g ∈ dualPiece A M k) : RightDual A M :=
  mk g (AddSubgroup.mem_iSup_of_mem k hg)

@[simp] theorem toHom_ofPiece {k : ℤ} (g : M →+ A) (hg : g ∈ dualPiece A M k) :
    toHom (ofPiece g hg) = g := rfl

theorem ofPiece_mem_grade {k : ℤ} (g : M →+ A) (hg : g ∈ dualPiece A M k) :
    ofPiece g hg ∈ grade A M k := hg.2

/-- Induction on `M^∨`: a property holds for all elements if it holds for `0`, for homogeneous
elements and is preserved by sums. -/
@[elab_as_elim]
theorem induction_on' {P : RightDual A M → Prop} (f : RightDual A M) (zero : P 0)
    (homogeneous : ∀ (k : ℤ) (f : RightDual A M), f ∈ grade A M k → P f)
    (add : ∀ f g, P f → P g → P (f + g)) : P f := by
  have key : ∀ (g : M →+ A) (hg : g ∈ dualSubgroup A M), P (mk g hg) := by
    intro g hg
    refine AddSubgroup.iSup_induction' (dualPiece A M)
      (C := fun g hg => P (mk g hg)) (fun k g hg => ?_) zero (fun g g' hg hg' h h' => ?_) hg
    · exact homogeneous k (ofPiece g hg) hg.2
    · exact add _ _ h h'
  exact key (toHom f) (toHom_mem f)

/-- Two elements of `M^∨` agreeing on homogeneous elements are equal. -/
theorem ext_of_homogeneous {f g : RightDual A M}
    (h : ∀ (i : ℤ) (m : M), m ∈ grading i → toHom f m = toHom g m) : f = g := by
  refine ext fun m => ?_
  induction m using DG.induction_on with
  | h_zero => rw [map_zero, map_zero]
  | h_homogeneous m => exact h _ _ m.2
  | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']

theorem mem_range_coe {k : ℤ} {f : RightDual A M} (hf : f ∈ grade A M k) :
    f ∈ (DirectSum.coeAddMonoidHom (grade A M)).range :=
  ⟨DirectSum.of (fun k => grade A M k) k ⟨f, hf⟩, DirectSum.coeAddMonoidHom_of _ _ _⟩

/-- `M^∨` is the direct sum of its homogeneous parts. -/
theorem isInternal_grade : DirectSum.IsInternal (grade A M) := by
  classical
  constructor
  · intro x y hxy
    rw [← sub_eq_zero, ← map_sub] at hxy
    rw [← sub_eq_zero]
    set z := x - y
    ext k : 1
    have hz : ∀ (i : ℤ) (m : M), m ∈ grading i → toHom (z k : RightDual A M) m = 0 := by
      intro i m hm
      have h0 := congrArg (fun g : RightDual A M =>
        (decompose (grading (M := A)) (toHom g m) (i + k) : A)) hxy
      simp only [toHom_zero, AddMonoidHom.zero_apply, decompose_zero, DirectSum.zero_apply,
        ZeroMemClass.coe_zero] at h0
      rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, toHom_sum,
        AddMonoidHom.finsetSum_apply, decompose_sum, DFinsupp.finsetSum_apply,
        AddSubmonoidClass.coe_finsetSum] at h0
      by_cases hk : k ∈ z.support
      · rw [Finset.sum_eq_single_of_mem _ hk, decompose_of_mem_same _ ((z k).2 i m hm)] at h0
        · exact h0
        · intro q _ hq
          exact decompose_of_mem_ne _ ((z q).2 i m hm) (by omega)
      · rw [DFinsupp.notMem_support_iff.mp hk]
        rfl
    have : (z k : RightDual A M) = 0 := ext_of_homogeneous fun i m hm => by
      rw [hz i m hm]; rfl
    exact Subtype.ext this
  · intro f
    rw [← AddMonoidHom.mem_range]
    induction f using induction_on' with
    | zero => exact zero_mem _
    | homogeneous k f hf => exact mem_range_coe hf
    | add f g hf hg => exact add_mem hf hg

end RightDual

end Group

/-! ## The differential -/

section Differential

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M]

/-- The differential of the Hom complex on all additive maps, written without reference to the
degree: `g ↦ d ∘ g - ι ∘ g ∘ ι ∘ d` with `ι` the sign `x ↦ (-1)^{|x|} x`. -/
def dualD : (M →+ A) →+ (M →+ A) where
  toFun g := (d : A →+ A).comp g -
    (((Shift.twist A 1 : A →+* A) : A →+ A).comp g).comp ((gradeSign M 1).comp (d : M →+ M))
  map_zero' := by
    ext m
    simp
  map_add' g g' := by
    ext m
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add]
    abel

variable {A M}

theorem dualD_apply (g : M →+ A) (m : M) :
    dualD A M g m = d (g m) - Shift.twist A 1 (g (gradeSign M 1 (d m))) := rfl

/-- On a map of degree `k`, `(d g)(m) = d(g m) - (-1)^k g(d m)`. -/
theorem dualD_apply_of_mem {k : ℤ} {g : M →+ A}
    (hg : ∀ (i : ℤ) (m : M), m ∈ grading i → g m ∈ grading (i + k)) (m : M) :
    dualD A M g m = d (g m) - koszulSign k • g (d m) := by
  induction m using DG.induction_on with
  | h_zero => simp [dualD_apply]
  | h_homogeneous m =>
    rename_i i
    rw [dualD_apply, gradeSign_of_mem 1 (d_mem m.2), Units.smul_def, map_zsmul, map_zsmul,
      ← Units.smul_def, Shift.twist_of_mem (hg _ _ (d_mem m.2)), smul_smul, ← koszulSign_add]
    congr 2
    exact (Int.negOnePow_eq_iff _ _).mpr ⟨i + 1, by ring⟩
  | h_add m m' hm hm' =>
    simp only [map_add, smul_add, hm, hm']
    abel

variable [Module Aᵐᵒᵖ M] [DGRightModule A M]

theorem dualD_mem_dualPiece {k : ℤ} {g : M →+ A} (hg : g ∈ dualPiece A M k) :
    dualD A M g ∈ dualPiece A M (k + 1) := by
  refine ⟨fun a m => ?_, fun i m hm => ?_⟩
  · induction m using DG.induction_on with
    | h_zero => simp
    | h_homogeneous m =>
      rename_i i
      rw [dualD_apply_of_mem hg.2, dualD_apply_of_mem hg.2, hg.1, d_mul (hg.2 _ _ m.2),
        d_op_smul m.2, map_add, hg.1, Units.smul_def (koszulSign i), map_zsmul,
        ← Units.smul_def, hg.1, smul_add, smul_smul, ← koszulSign_add, sub_mul, smul_mul_assoc,
        add_comm k i]
      abel
    | h_add m m' hm hm' => rw [smul_add, map_add, map_add, hm, hm', add_mul]
  · rw [dualD_apply_of_mem hg.2, ← add_assoc]
    refine sub_mem (d_mem (hg.2 i m hm)) ?_
    rw [Units.smul_def]
    refine zsmul_mem ?_ _
    rw [add_right_comm]
    exact hg.2 _ _ (d_mem hm)

theorem dualD_mem {g : M →+ A} (hg : g ∈ dualSubgroup A M) : dualD A M g ∈ dualSubgroup A M := by
  refine AddSubgroup.iSup_induction (dualPiece A M) (C := fun g => dualD A M g ∈ dualSubgroup A M)
    hg (fun k g hg => AddSubgroup.mem_iSup_of_mem (k + 1) (dualD_mem_dualPiece hg)) ?_
    fun g g' h h' => ?_
  · rw [map_zero]; exact zero_mem _
  · rw [map_add]; exact add_mem h h'

namespace RightDual

variable (A M) in
/-- The differential of `M^∨`. -/
def dHom : RightDual A M →+ RightDual A M where
  toFun f := mk (dualD A M (toHom f)) (dualD_mem (toHom_mem f))
  map_zero' := toHom_injective (map_zero (dualD A M))
  map_add' f g := toHom_injective (map_add (dualD A M) (toHom f) (toHom g))

theorem toHom_dHom (f : RightDual A M) : toHom (dHom A M f) = dualD A M (toHom f) := rfl

theorem dHom_apply_of_mem {k : ℤ} {f : RightDual A M} (hf : f ∈ grade A M k) (m : M) :
    toHom (dHom A M f) m = d (toHom f m) - koszulSign k • toHom f (d m) :=
  dualD_apply_of_mem hf m

theorem dHom_mem {k : ℤ} {f : RightDual A M} (hf : f ∈ grade A M k) :
    dHom A M f ∈ grade A M (k + 1) :=
  (dualD_mem_dualPiece (toHom_mem_dualPiece hf)).2

theorem dHom_dHom (f : RightDual A M) : dHom A M (dHom A M f) = 0 := by
  induction f using induction_on' with
  | zero => rw [map_zero, map_zero]
  | homogeneous k f hf =>
    refine ext fun m => ?_
    rw [dHom_apply_of_mem (dHom_mem hf), dHom_apply_of_mem hf, dHom_apply_of_mem hf, d_sub, d_d,
      d_d, map_zero, smul_zero, sub_zero, zero_sub, d_units_smul, koszulSign_add, mul_smul,
      toHom_zero, AddMonoidHom.zero_apply]
    simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]

/-- **`M^∨` as a dg abelian group**: graded by the degree of maps, with the differential of the
Hom complex. -/
instance instDGAddCommGroup : DGAddCommGroup (RightDual A M) where
  grading := grade A M
  decomposition := isInternal_grade.chooseDecomposition
  d := dHom A M
  d_mem' hf := dHom_mem hf
  d_d' := dHom_dHom

theorem mem_grading_iff {k : ℤ} {f : RightDual A M} :
    f ∈ grading k ↔ ∀ (i : ℤ) (m : M), m ∈ grading i → toHom f m ∈ grading (i + k) := Iff.rfl

theorem apply_mem_grading {k i : ℤ} {f : RightDual A M} (hf : f ∈ grading k) {m : M}
    (hm : m ∈ grading i) : toHom f m ∈ grading (i + k) := hf i m hm

theorem toHom_d (f : RightDual A M) : toHom (d f) = dualD A M (toHom f) := rfl

/-- `(d f)(m) = d(f m) - (-1)^{|f|} f(d m)`. -/
theorem d_apply_of_mem {k : ℤ} {f : RightDual A M} (hf : f ∈ grading k) (m : M) :
    toHom (d f) m = d (toHom f m) - koszulSign k • toHom f (d m) :=
  dHom_apply_of_mem hf m

end RightDual

end Differential

/-! ## The left action of `A` -/

section LeftAction

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M]

/-- `g ↦ a g`, on all additive maps. -/
def dualLmul (a : A) : (M →+ A) →+ (M →+ A) where
  toFun g := (AddMonoidHom.mulLeft a).comp g
  map_zero' := by ext m; simp
  map_add' g g' := by ext m; simp [mul_add]

variable {A M}

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup M] [Module Aᵐᵒᵖ M] in
@[simp] theorem dualLmul_apply (a : A) (g : M →+ A) (m : M) : dualLmul A M a g m = a * g m := rfl

theorem dualLmul_mem_dualPiece {i k : ℤ} {a : A} (ha : a ∈ grading i) {g : M →+ A}
    (hg : g ∈ dualPiece A M k) : dualLmul A M a g ∈ dualPiece A M (i + k) :=
  ⟨fun c m => by rw [dualLmul_apply, dualLmul_apply, hg.1, mul_assoc], fun j m hm => by
    rw [dualLmul_apply, show j + (i + k) = i + (j + k) by ring]
    exact mul_mem_grading ha (hg.2 j m hm)⟩

theorem dualLmul_mem (a : A) {g : M →+ A} (hg : g ∈ dualSubgroup A M) :
    dualLmul A M a g ∈ dualSubgroup A M := by
  refine AddSubgroup.iSup_induction (dualPiece A M)
    (C := fun g => dualLmul A M a g ∈ dualSubgroup A M) hg (fun k g hg => ?_) ?_
    fun g g' h h' => ?_
  · induction a using DG.induction_on with
    | h_zero =>
      have : dualLmul A M 0 g = 0 := by ext m; simp
      rw [this]; exact zero_mem _
    | h_homogeneous a => exact AddSubgroup.mem_iSup_of_mem _ (dualLmul_mem_dualPiece a.2 hg)
    | h_add a a' ha ha' =>
      have : dualLmul A M (a + a') g = dualLmul A M a g + dualLmul A M a' g := by
        ext m; simp [add_mul]
      rw [this]; exact add_mem ha ha'
  · rw [map_zero]; exact zero_mem _
  · rw [map_add]; exact add_mem h h'

namespace RightDual

instance instModule : Module A (RightDual A M) where
  smul a f := mk (dualLmul A M a (toHom f)) (dualLmul_mem a (toHom_mem f))
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_mul _ _ _
  zero_smul _ := ext fun _ => zero_mul _

/-- `(a f)(m) = a f(m)`. -/
@[simp] theorem toHom_smul (a : A) (f : RightDual A M) (m : M) :
    toHom (a • f) m = a * toHom f m := rfl

variable [DGRightModule A M]

/-- **`M^∨` is a left dg `A`-module**, `(a f)(m) = a f(m)`. -/
instance instDGModule : DGModule A (RightDual A M) where
  smul_mem i k a f ha hf := by
    rw [vadd_eq_add]
    exact (dualLmul_mem_dualPiece ha (toHom_mem_dualPiece hf)).2
  d_smul' {n a} ha f := by
    refine ext fun m => ?_
    change dualD A M (dualLmul A M a (toHom f)) m =
      d a * toHom f m + (koszulSign n : ℤ) • (a * dualD A M (toHom f) m)
    simp only [dualD_apply, dualLmul_apply]
    rw [d_mul ha, map_mul, Shift.twist_of_mem ha, one_mul]
    simp only [Units.smul_def, smul_mul_assoc, mul_sub, smul_sub]
    abel

end RightDual

end LeftAction

/-! ## The right action of `B` on the dual of a `(B, A)`-bimodule -/

section RightAction

variable (A : Type*) [Ring A] [DGAddCommGroup A]
  (B : Type*) [Ring B] [DGAddCommGroup B]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M] [Module B M]

/-- `g ↦ g ∘ (b • -)`, on all additive maps. -/
def dualRmul (b : B) : (M →+ A) →+ (M →+ A) where
  toFun g := g.comp (DistribSMul.toAddMonoidHom M b)
  map_zero' := rfl
  map_add' _ _ := rfl

variable {A B M}

omit [DGAddCommGroup A] [DGAddCommGroup B] [DGAddCommGroup M] [Module Aᵐᵒᵖ M] in
@[simp] theorem dualRmul_apply (b : B) (g : M →+ A) (m : M) : dualRmul A B M b g m = g (b • m) :=
  rfl

variable [SMulCommClass B Aᵐᵒᵖ M] [DGModule B M]

theorem dualRmul_mem_dualPiece {p k : ℤ} {b : B} (hb : b ∈ grading p) {g : M →+ A}
    (hg : g ∈ dualPiece A M k) : dualRmul A B M b g ∈ dualPiece A M (k + p) :=
  ⟨fun c m => by rw [dualRmul_apply, dualRmul_apply, smul_comm, hg.1], fun j m hm => by
    rw [dualRmul_apply, show j + (k + p) = p + j + k by ring]
    exact hg.2 _ _ (smul_mem_grading hb hm)⟩

theorem dualRmul_mem (b : B) {g : M →+ A} (hg : g ∈ dualSubgroup A M) :
    dualRmul A B M b g ∈ dualSubgroup A M := by
  refine AddSubgroup.iSup_induction (dualPiece A M)
    (C := fun g => dualRmul A B M b g ∈ dualSubgroup A M) hg (fun k g hg => ?_) ?_
    fun g g' h h' => ?_
  · induction b using DG.induction_on with
    | h_zero =>
      have : dualRmul A B M 0 g = 0 := by
        ext m; simp only [dualRmul_apply, zero_smul, map_zero, AddMonoidHom.zero_apply]
      rw [this]; exact zero_mem _
    | h_homogeneous b => exact AddSubgroup.mem_iSup_of_mem _ (dualRmul_mem_dualPiece b.2 hg)
    | h_add b b' hb hb' =>
      have : dualRmul A B M (b + b') g = dualRmul A B M b g + dualRmul A B M b' g := by
        ext m; simp only [dualRmul_apply, add_smul, map_add, AddMonoidHom.add_apply]
      rw [this]; exact add_mem hb hb'
  · rw [map_zero]; exact zero_mem _
  · rw [map_add]; exact add_mem h h'

namespace RightDual

/-- The right `B`-module structure on the dual of a `(B, A)`-bimodule: `(f b)(m) = f(b m)`. -/
instance instModuleOp : Module Bᵐᵒᵖ (RightDual A M) where
  smul b f := mk (dualRmul A B M (unop b) (toHom f)) (dualRmul_mem (unop b) (toHom_mem f))
  one_smul f := ext fun m => congrArg (toHom f) (one_smul B m)
  mul_smul b b' f := ext fun m => congrArg (toHom f) (mul_smul (unop b') (unop b) m)
  smul_zero b := ext fun m => rfl
  smul_add b f g := ext fun m => rfl
  add_smul b b' f := ext fun m => by
    change toHom f ((unop b + unop b') • m) = toHom f (unop b • m) + toHom f (unop b' • m)
    rw [add_smul, map_add]
  zero_smul f := ext fun m => by
    change toHom f ((0 : B) • m) = 0
    rw [zero_smul, map_zero]

/-- `(f b)(m) = f(b m)`. -/
@[simp] theorem toHom_op_smul (b : B) (f : RightDual A M) (m : M) :
    toHom (op b • f) m = toHom f (b • m) := rfl

variable [DGRing A]

instance instSMulCommClass : SMulCommClass A Bᵐᵒᵖ (RightDual A M) where
  smul_comm _ _ _ := ext fun _ => rfl

variable [DGRightModule A M]

/-- **The dual of a dg `(B, A)`-bimodule is a right dg `B`-module**, `(f b)(m) = f(b m)`. -/
instance instDGRightModule : DGRightModule B (RightDual A M) where
  op_smul_mem' hb hf := (dualRmul_mem_dualPiece hb (toHom_mem_dualPiece hf)).2
  d_op_smul' {j f} hf b := by
    induction b using DG.induction_on with
    | h_zero => simp
    | h_homogeneous b =>
      rename_i p
      refine ext_of_homogeneous fun i m hm => ?_
      have hbf : op (b : B) • f ∈ grading (j + p) :=
        (dualRmul_mem_dualPiece b.2 (toHom_mem_dualPiece hf)).2
      rw [d_apply_of_mem hbf, toHom_add, AddMonoidHom.add_apply, toHom_units_smul,
        Units.smul_def (koszulSign j), AddMonoidHom.smul_apply, ← Units.smul_def, toHom_op_smul,
        toHom_op_smul, toHom_op_smul, toHom_op_smul, d_apply_of_mem hf, d_smul b.2, map_add,
        Units.smul_def (koszulSign p), map_zsmul, ← Units.smul_def, smul_add, smul_smul,
        ← koszulSign_add]
      abel
    | h_add b b' hb hb' =>
      rw [op_add, add_smul, d_add, hb, hb', d_add, op_add, add_smul, add_smul, smul_add]
      abel

/-- **The dual of a dg `(B, A)`-bimodule is a dg `(A, B)`-bimodule.** -/
instance instDGBimodule : DGBimodule A B (RightDual A M) :=
  DGBimodule.mk'

end RightDual

end RightAction

/-! ## Finite right bases and the dual basis -/

section Basis

variable (A : Type*) [Ring A]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M]

/-- A finite homogeneous basis of `M` as a right `A`-module, indexed by a finite type `ι`, given
with its coefficient functions: `x = Σ_i b_i · coeff x i`, with unique coefficients. -/
structure RightBasis (ι : Type*) [Fintype ι] where
  /-- The basis elements. -/
  b : ι → M
  /-- Their degrees. -/
  deg : ι → ℤ
  b_mem : ∀ i, b i ∈ grading (deg i)
  /-- The coefficients of an element. -/
  coeff : M → ι → A
  sum_coeff : ∀ x, ∑ i, op (coeff x i) • b i = x
  coeff_sum : ∀ a : ι → A, coeff (∑ i, op (a i) • b i) = a

namespace RightBasis

variable {A M} {ι : Type*} [Fintype ι] (R : RightBasis A M ι)

theorem coeff_add (x y : M) : R.coeff (x + y) = R.coeff x + R.coeff y := by
  conv_lhs => rw [← R.sum_coeff x, ← R.sum_coeff y, ← Finset.sum_add_distrib]
  simp only [← add_smul, ← op_add]
  exact R.coeff_sum (R.coeff x + R.coeff y)

theorem coeff_zero : R.coeff 0 = 0 := by
  have h := R.coeff_sum 0
  simpa using h

/-- The coefficient of `b_i`, as an additive map. -/
def coeffHom (i : ι) : M →+ A where
  toFun x := R.coeff x i
  map_zero' := by rw [R.coeff_zero, Pi.zero_apply]
  map_add' x y := by rw [R.coeff_add, Pi.add_apply]

@[simp] theorem coeffHom_apply (i : ι) (x : M) : R.coeffHom i x = R.coeff x i := rfl

/-- The coefficients are right `A`-linear. -/
theorem coeff_op_smul (a : A) (x : M) (i : ι) : R.coeff (op a • x) i = R.coeff x i * a := by
  have h : op a • x = ∑ i, op (R.coeff x i * a) • R.b i := by
    conv_lhs => rw [← R.sum_coeff x, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← op_mul]
  rw [h, R.coeff_sum]

theorem coeff_basis [DecidableEq ι] (i : ι) : R.coeff (R.b i) = Pi.single i 1 := by
  have h := R.coeff_sum (Pi.single i 1)
  rwa [Finset.sum_eq_single i (fun l _ hl => by rw [Pi.single_eq_of_ne hl, op_zero, zero_smul])
    (by simp), Pi.single_eq_same, op_one, one_smul] at h

variable [DGAddCommGroup A] [DGRightModule A M]

omit [Fintype ι] in
/-- The homogeneous components of `m a` for homogeneous `m ∈ Mᵏ`: `(m a)_p = m a_{p-k}`. -/
theorem decompose_op_smul_of_mem {k : ℤ} {m : M} (hm : m ∈ grading k) (a : A) (p : ℤ) :
    (decompose (grading (M := M)) (op a • m) p : M) =
      op (decompose (grading (M := A)) a (p - k) : A) • m := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rename_i i
    have ham := op_smul_mem_grading a.2 hm
    by_cases hi : k + i = p
    · subst hi
      rw [decompose_of_mem_same _ ham, add_sub_cancel_left, decompose_of_mem_same _ a.2]
    · rw [decompose_of_mem_ne _ ham hi, decompose_of_mem_ne _ a.2 (by omega), op_zero, zero_smul]
  | h_add a a' ha ha' =>
    rw [op_add, add_smul, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, ha, ha',
      decompose_add, DirectSum.add_apply, AddMemClass.coe_add, op_add, add_smul]

/-- The coefficient of a homogeneous component: `coeff (x_p) i = (coeff x i)_{p - |b_i|}`. -/
theorem coeff_decompose (x : M) (p : ℤ) (i : ι) :
    R.coeff (decompose (grading (M := M)) x p) i =
      decompose (grading (M := A)) (R.coeff x i) (p - R.deg i) := by
  have hx : (decompose (grading (M := M)) x p : M) =
      ∑ l, op (decompose (grading (M := A)) (R.coeff x l) (p - R.deg l) : A) • R.b l := by
    conv_lhs => rw [← R.sum_coeff x]
    rw [decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun l _ => decompose_op_smul_of_mem (R.b_mem l) _ p
  rw [hx, R.coeff_sum]

/-- Coefficients of homogeneous elements are homogeneous. -/
theorem coeff_mem {x : M} {p : ℤ} (hx : x ∈ grading p) (i : ι) :
    R.coeff x i ∈ grading (p - R.deg i) := by
  have h := R.coeff_decompose x p i
  rw [decompose_of_mem_same _ hx] at h
  rw [h]
  exact (decompose (grading (M := A)) (R.coeff x i) (p - R.deg i)).2

omit [DGRightModule A M] in
theorem coeffHom_mem_dualPiece' (h : ∀ {x : M} {p : ℤ}, x ∈ grading p → ∀ i,
    R.coeff x i ∈ grading (p - R.deg i)) (i : ι) : R.coeffHom i ∈ dualPiece A M (-R.deg i) :=
  ⟨fun a m => R.coeff_op_smul a m i, fun p m hm => by
    rw [← sub_eq_add_neg]; exact h hm i⟩

theorem coeffHom_mem_dualPiece (i : ι) : R.coeffHom i ∈ dualPiece A M (-R.deg i) :=
  R.coeffHom_mem_dualPiece' (fun hx i => R.coeff_mem hx i) i

variable [DGRing A]

/-- **The dual basis** `δ_i`: the coefficient of `b_i`, a right-linear map of degree `-|b_i|`. -/
def δ (i : ι) : RightDual A M := RightDual.ofPiece (R.coeffHom i) (R.coeffHom_mem_dualPiece i)

omit [DGRing A] in
@[simp] theorem toHom_δ (i : ι) (x : M) : RightDual.toHom (R.δ i) x = R.coeff x i := rfl

theorem δ_mem (i : ι) : R.δ i ∈ grading (-R.deg i) :=
  RightDual.ofPiece_mem_grade _ (R.coeffHom_mem_dualPiece i)

omit [DGAddCommGroup A] [DGRightModule A M] [DGRing A] in
/-- A right `A`-linear map is determined by its values on the basis. -/
theorem apply_eq_sum (g : M →+ A) (hg : ∀ (a : A) (m : M), g (op a • m) = g m * a) (x : M) :
    g x = ∑ i, g (R.b i) * R.coeff x i := by
  conv_lhs => rw [← R.sum_coeff x, map_sum]
  exact Finset.sum_congr rfl fun i _ => hg _ _

include R in
/-- With a finite basis, every right `A`-linear map `M → A` is a finite sum of homogeneous
ones. -/
theorem mem_dualSubgroup (g : M →+ A) (hg : ∀ (a : A) (m : M), g (op a • m) = g m * a) :
    g ∈ dualSubgroup A M := by
  have h : g = ∑ i, dualLmul A M (g (R.b i)) (R.coeffHom i) := by
    ext x
    rw [R.apply_eq_sum g hg x, AddMonoidHom.finsetSum_apply]
    rfl
  rw [h]
  exact sum_mem fun i _ => dualLmul_mem _ (AddSubgroup.mem_iSup_of_mem _ (R.coeffHom_mem_dualPiece i))

/-- A right `A`-linear map `M → A` as an element of `M^∨`, for `M` with a finite basis. -/
def ofRightLinear (g : M →+ A) (hg : ∀ (a : A) (m : M), g (op a • m) = g m * a) : RightDual A M :=
  RightDual.mk g (R.mem_dualSubgroup g hg)

@[simp] theorem toHom_ofRightLinear (g : M →+ A)
    (hg : ∀ (a : A) (m : M), g (op a • m) = g m * a) :
    RightDual.toHom (R.ofRightLinear g hg) = g := rfl

/-- **The dual basis is a basis** of the left `A`-module `M^∨`: `f = Σ_i f(b_i) δ_i`, with
`δ_i` of degree `-|b_i|`. -/
def dualBasis : FreeBasis A (RightDual A M) ι where
  b := R.δ
  deg i := -R.deg i
  b_mem := R.δ_mem
  coeff f i := RightDual.toHom f (R.b i)
  sum_coeff f := RightDual.ext fun x => by
    rw [RightDual.toHom_sum, AddMonoidHom.finsetSum_apply,
      R.apply_eq_sum _ (RightDual.map_op_smul f) x]
    rfl
  coeff_sum a := by
    classical
    funext i
    rw [RightDual.toHom_sum, AddMonoidHom.finsetSum_apply]
    simp only [RightDual.toHom_smul, toHom_δ, R.coeff_basis]
    rw [Finset.sum_eq_single i (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero])
      (by simp), Pi.single_eq_same, mul_one]

@[simp] theorem dualBasis_b (i : ι) : R.dualBasis.b i = R.δ i := rfl
@[simp] theorem dualBasis_deg (i : ι) : R.dualBasis.deg i = -R.deg i := rfl
@[simp] theorem dualBasis_coeff (f : RightDual A M) (i : ι) :
    R.dualBasis.coeff f i = RightDual.toHom f (R.b i) := rfl

/-- The differential of the dual basis: `(d δ_i)(b_l) = -(-1)^{|b_i|} · (coefficient of b_i in
d b_l)`. -/
theorem dualBasis_coeff_d (i l : ι) :
    R.dualBasis.coeff (d (R.δ i)) l = -(koszulSign (R.deg i) • R.coeff (d (R.b l)) i) := by
  classical
  rw [dualBasis_coeff, RightDual.d_apply_of_mem (R.δ_mem i), toHom_δ, toHom_δ, R.coeff_basis]
  have h0 : d (Pi.single (M := fun _ : ι => A) l (1 : A) i) = 0 := by
    by_cases h : i = l
    · subst h; rw [Pi.single_eq_same, d_one]
    · rw [Pi.single_eq_of_ne h, d_zero]
  rw [h0, zero_sub]
  congr 2
  exact (Int.negOnePow_eq_iff _ _).mpr ⟨-R.deg i, by ring⟩

/-- **The dual of a triangular basis is triangular**: if `d b_l` only involves the `b_i` with
`key i < key l`, then the dual basis, ordered by decreasing key, is a triangular basis of the left
dg `A`-module `M^∨`. -/
def dualTriangular (key : ι → ℤ) (hkey : ∀ l i, R.coeff (d (R.b l)) i ≠ 0 → key i < key l) :
    TriangularBasis A (RightDual A M) :=
  R.dualBasis.toTriangular (fun i => -key i) fun i l h => by
    have h' : R.coeff (d (R.b l)) i ≠ 0 := by
      intro h0
      apply h
      rw [dualBasis_b, dualBasis_coeff_d, h0, smul_zero, neg_zero]
    have := hkey l i h'
    omega

theorem dualTriangular_length (key : ι → ℤ)
    (hkey : ∀ l i, R.coeff (d (R.b l)) i ≠ 0 → key i < key l) :
    (R.dualTriangular key hkey).length = Fintype.card ι := rfl

/-- The dual of a right dg module with a finite triangular basis is K-projective as a left dg
module. -/
theorem dual_isKProjective (key : ι → ℤ)
    (hkey : ∀ l i, R.coeff (d (R.b l)) i ≠ 0 → key i < key l) :
    IsKProjective.{w} A (RightDual A M) :=
  (R.dualTriangular key hkey).isKProjective

/-- The dual of a right dg module with a finite triangular basis is cofibrant as a left dg
module. -/
theorem dual_hasLiftingProperty (key : ι → ℤ)
    (hkey : ∀ l i, R.coeff (d (R.b l)) i ≠ 0 → key i < key l) :
    HasLiftingProperty.{w} A (RightDual A M) :=
  (R.dualTriangular key hkey).hasLiftingProperty

end RightBasis

end Basis

/-! ## Rank-one maps -/

section RankOne

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M]

/-- The rank-one map `x ↦ m · φ(x)`. -/
def rankOne (m : M) (φ : M →+ A) : M →+ M where
  toFun x := op (φ x) • m
  map_zero' := by rw [map_zero, op_zero, zero_smul]
  map_add' x y := by rw [map_add, op_add, add_smul]

omit [DGAddCommGroup M] in
@[simp] theorem rankOne_apply (m : M) (φ : M →+ A) (x : M) : rankOne m φ x = op (φ x) • m := rfl

variable {ι : Type*} [Fintype ι] (R : RightBasis A M ι)

/-- Every right-linear additive endomorphism is `Σ_i f(b_i) · δ_i(−)`. -/
theorem RightBasis.eq_sum_rankOne (f : M →+ M) (hf : ∀ (a : A) (x : M), f (op a • x) = op a • f x) :
    f = ∑ i, rankOne (f (R.b i)) (R.coeffHom i) := by
  ext x
  conv_lhs => rw [← R.sum_coeff x]
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [hf]; rfl

/-- The coefficients `m_i` of `Σ_i m_i · δ_i(−)` are unique. -/
theorem RightBasis.rankOne_injective [DecidableEq ι] (m m' : ι → M)
    (h : ∑ i, rankOne (m i) (R.coeffHom i) = ∑ i, rankOne (m' i) (R.coeffHom i)) : m = m' := by
  funext j
  have key : ∀ m : ι → M, (∑ i, rankOne (m i) (R.coeffHom i)) (R.b j) = m j := by
    intro m
    rw [AddMonoidHom.finsetSum_apply, Finset.sum_eq_single j]
    · rw [rankOne_apply, RightBasis.coeffHom_apply, R.coeff_basis, Pi.single_eq_same, op_one,
        one_smul]
    · intro i _ hij
      rw [rankOne_apply, RightBasis.coeffHom_apply, R.coeff_basis, Pi.single_eq_of_ne hij,
        op_zero, zero_smul]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [← key m, h, key m']

end RankOne

/-! ### Duals of isomorphic right modules -/

section Precomp

variable {A M M' : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [AddCommGroup M] [DGAddCommGroup M]
  [Module Aᵐᵒᵖ M] [DGRightModule A M] [AddCommGroup M'] [DGAddCommGroup M'] [Module Aᵐᵒᵖ M']
  [DGRightModule A M'] (e : DGAddEquiv M M') (he : ∀ (a : A) (m : M), e (op a • m) = op a • e m)

include he

omit he in
/-- An isomorphism of dg abelian groups commutes with the grade signs `m ↦ (-1)^{j |m|} m`. -/
theorem gradeSign_dgAddEquiv (j : ℤ) (m : M) : e (gradeSign M j m) = gradeSign M' j (e m) := by
  induction m using DG.induction_on with
  | h_zero => rw [map_zero, map_zero, map_zero]
  | @h_homogeneous i m =>
    rw [gradeSign_of_mem j m.2, gradeSign_of_mem j (e.map_mem m.2), Units.smul_def, Units.smul_def, map_zsmul]
  | h_add m m' hm hm' => rw [map_add, map_add, hm, hm', map_add, map_add]

namespace RightDual

theorem precomp_mem_dualPiece {k : ℤ} {g : M' →+ A} (hg : g ∈ dualPiece A M' k) :
    g.comp e.toAddMonoidHom ∈ dualPiece A M k :=
  ⟨fun a m => by
    change g (e (op a • m)) = g (e m) * a
    rw [he, hg.1], fun i m hm => hg.2 i (e m) (e.map_mem hm)⟩

theorem precomp_mem_dualSubgroup {g : M' →+ A} (hg : g ∈ dualSubgroup A M') :
    g.comp e.toAddMonoidHom ∈ dualSubgroup A M := by
  induction hg using AddSubgroup.iSup_induction' with
  | hp k g hg => exact AddSubgroup.mem_iSup_of_mem k (precomp_mem_dualPiece e he hg)
  | h1 => exact zero_mem _
  | hadd g g' _ _ hg hg' => rw [AddMonoidHom.add_comp]; exact add_mem hg hg'

/-- `f ↦ f ∘ e : M'^∨ → M^∨`. -/
def precompHom : RightDual A M' →+ RightDual A M where
  toFun f := RightDual.mk ((RightDual.toHom f).comp e.toAddMonoidHom)
    (precomp_mem_dualSubgroup e he (RightDual.toHom_mem f))
  map_zero' := RightDual.ext fun _ => rfl
  map_add' _ _ := RightDual.ext fun _ => rfl

theorem toHom_precompHom (f : RightDual A M') (m : M) :
    RightDual.toHom (precompHom e he f) m = RightDual.toHom f (e m) := rfl

/-- **An isomorphism of right dg modules induces an isomorphism of graded duals** (by precomposition). -/
def precompDGAddEquiv : DGAddEquiv (RightDual A M') (RightDual A M) where
  toFun := precompHom e he
  invFun := precompHom e.symm fun a m => by
    apply e.injective
    rw [he, DGAddEquiv.apply_symm_apply, DGAddEquiv.apply_symm_apply]
  left_inv f := RightDual.ext fun m => by
    rw [toHom_precompHom, toHom_precompHom, DGAddEquiv.apply_symm_apply]
  right_inv f := RightDual.ext fun m => by
    rw [toHom_precompHom, toHom_precompHom, DGAddEquiv.symm_apply_apply]
  map_add' := map_add _
  map_mem' {k f} hf := fun i m hm => hf i (e m) (e.map_mem hm)
  map_d' f := RightDual.ext fun m => by
    change RightDual.toHom (DG.d f) (e m) = RightDual.toHom (DG.d (precompHom e he f)) m
    rw [RightDual.toHom_d, RightDual.toHom_d, dualD_apply, dualD_apply, toHom_precompHom, ← e.map_d,
      ← gradeSign_dgAddEquiv]
    rfl

end RightDual

end Precomp

end

end DG
