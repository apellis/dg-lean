import Mathlib.RingTheory.Idempotents
import DG.Module.Right

/-!
# Corner rings and corner modules of a degree-`0` idempotent

For a dg ring `A` and a degree-`0` idempotent cocycle `e` (`e ∈ A⁰`, `e * e = e`, `d e = 0`,
bundled as `DGIdempotent A`), this file constructs

* the corner ring `e A e` (`DGIdempotent.Corner e`, Mathlib's `IsIdempotentElem.Corner`; a
  ring with unit `e`, not a subring of `A`) as a dg ring, with the differential and grading
  restricted from `A`;
* the left ideal `A e` (`DGIdempotent.leftIdeal e`, with underlying type
  `DGIdempotent.LeftCorner e`) as a dg `(A, e A e)`-bimodule;
* the right ideal `e A` (`DGIdempotent.rightIdeal e`, with underlying type
  `DGIdempotent.RightCorner e`) as a dg `(e A e, A)`-bimodule.

The gradings are the restricted ones: the homogeneous components of `a * e` are the
`aₙ * e`, and similarly for `e * a` and `e * a * e` (`DGIdempotent.LeftCorner.coe_decompose`,
...). This is packaged once as `DGAddCommGroup.ofInjective`, which transports a dg structure
along an injective additive map whose image is closed under the homogeneous projections and
under `d`.

Throughout, the idempotent is assumed to be a cocycle, `d e = 0`. For an idempotent with only
`d e ∈ A e` the left ideal `A e` is still `d`-stable, but the differential on `e A e` has to be
modified (`e a e ↦ e * d (a e)`); this more general case is `DG.LeftDGIdempotent`
(`DG.Module.CornerEnd`).
-/

open DirectSum MulOpposite

namespace DG

/-! ### Transport of dg structures along injective maps -/

section OfInjective

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M]
variable {T : Type*} [AddCommGroup T] (ι : T →+ M) (hι : Function.Injective ι)
  (dT : T →+ T) (hd : ∀ t, ι (dT t) = d (ι t))
  (hhom : ∀ (n : ℤ) (t : T), (decompose (grading (M := M)) (ι t) n : M) ∈ ι.range)

/-- The homogeneous components of `T`, pulled back along `ι`. -/
def gradingComap (n : ℤ) : AddSubgroup T := (grading (M := M) n).comap ι

theorem mem_gradingComap {n : ℤ} {t : T} : t ∈ gradingComap ι n ↔ ι t ∈ grading n :=
  Iff.rfl

/-- The map of direct sums induced by `ι` on homogeneous components. -/
def gradingComapMap : (⨁ n, gradingComap ι n) →+ ⨁ n, grading (M := M) n :=
  DirectSum.map fun n => (ι.domRestrict (gradingComap ι n)).codRestrict (grading n) fun t => t.2

set_option backward.isDefEq.respectTransparency false in
theorem coeAddMonoidHom_gradingComapMap (x : ⨁ n, gradingComap ι n) :
    DirectSum.coeAddMonoidHom (grading (M := M)) (gradingComapMap ι x) =
      ι (DirectSum.coeAddMonoidHom (gradingComap ι) x) := by
  suffices h : (DirectSum.coeAddMonoidHom (grading (M := M))).comp (gradingComapMap ι) =
      ι.comp (DirectSum.coeAddMonoidHom (gradingComap ι)) from DFunLike.congr_fun h x
  ext n t
  simp [gradingComapMap]

set_option backward.isDefEq.respectTransparency false in
include hι hhom in
theorem isInternal_gradingComap : DirectSum.IsInternal (gradingComap ι) := by
  classical
  constructor
  · intro x y hxy
    have h : gradingComapMap ι x = gradingComapMap ι y :=
      (DirectSum.Decomposition.isInternal (grading (M := M))).injective (by
        rw [coeAddMonoidHom_gradingComapMap, coeAddMonoidHom_gradingComapMap, hxy])
    rw [gradingComapMap, DirectSum.map_eq_iff] at h
    ext n
    exact hι (by simpa using h n)
  · intro t
    choose s hs using fun n => hhom n t
    refine ⟨∑ n ∈ (decompose (grading (M := M)) (ι t)).support,
      DirectSum.of _ n ⟨s n, ?_⟩, ?_⟩
    · rw [mem_gradingComap, hs]; exact Subtype.property _
    · apply hι
      simp only [map_sum, DirectSum.coeAddMonoidHom_of]
      conv_rhs => rw [← DirectSum.sum_support_decompose (grading (M := M)) (ι t)]
      exact Finset.sum_congr rfl fun n _ => hs n

include hι hhom in
/-- Transport a dg structure along an injective additive map `ι : T →+ M` whose image is
closed under the homogeneous projections, given a differential `dT` on `T` compatible with
`ι`. The homogeneous components of `T` are the preimages of those of `M`. -/
@[instance_reducible]
noncomputable def DGAddCommGroup.ofInjective : DGAddCommGroup T where
  grading := gradingComap ι
  decomposition := (isInternal_gradingComap ι hι hhom).chooseDecomposition
  d := dT
  d_mem' {n t} ht := by
    rw [mem_gradingComap, hd]
    exact d_mem ht
  d_d' t := hι (by rw [hd, hd, d_d, map_zero])

set_option backward.isDefEq.respectTransparency false in
include hd in
theorem DGAddCommGroup.ofInjective_coe_decompose (t : T) (n : ℤ) :
    letI := DGAddCommGroup.ofInjective ι hι dT hd hhom
    ι (decompose (grading (M := T)) t n) = decompose (grading (M := M)) (ι t) n := by
  let := DGAddCommGroup.ofInjective ι hι dT hd hhom
  have h : gradingComapMap ι (decompose (grading (M := T)) t) =
      decompose (grading (M := M)) (ι t) := by
    apply (DirectSum.Decomposition.isInternal (grading (M := M))).injective
    change DirectSum.coeAddMonoidHom _ _ = (decompose (grading (M := M))).symm _
    rw [coeAddMonoidHom_gradingComapMap, Equiv.symm_apply_apply]
    change ι ((decompose (grading (M := T))).symm _) = _
    rw [Equiv.symm_apply_apply]
  rw [← h]
  simp only [gradingComapMap, DirectSum.map_apply]
  rfl

end OfInjective

/-- A degree-`0` idempotent cocycle of a dg ring `A`: an element `e ∈ A⁰` with `e * e = e` and
`d e = 0`. -/
structure DGIdempotent (A : Type*) [Ring A] [DGAddCommGroup A] where
  /-- The underlying element. -/
  val : A
  mem_zero : val ∈ grading (M := A) 0
  mul_self : val * val = val
  d_eq_zero : d val = 0

namespace DGIdempotent

variable {A : Type*} [Ring A] [DGAddCommGroup A] (e : DGIdempotent A)

theorem isIdempotentElem : IsIdempotentElem e.val := e.mul_self

/-- The left ideal `A e = {a | a * e = a}`. -/
def leftIdeal : Ideal A where
  carrier := {a | a * e.val = a}
  add_mem' ha hb := by simp only [Set.mem_ofPred_eq] at *; rw [add_mul, ha, hb]
  zero_mem' := zero_mul _
  smul_mem' r a ha := by simp only [Set.mem_ofPred_eq, smul_eq_mul] at *; rw [mul_assoc, ha]

theorem mem_leftIdeal {a : A} : a ∈ e.leftIdeal ↔ a * e.val = a := Iff.rfl

theorem mul_val_mem_leftIdeal (a : A) : a * e.val ∈ e.leftIdeal := by
  rw [mem_leftIdeal, mul_assoc, e.mul_self]

theorem leftIdeal_eq_span : e.leftIdeal = Ideal.span {e.val} := by
  ext a
  rw [Ideal.mem_span_singleton', mem_leftIdeal]
  exact ⟨fun h => ⟨a, h⟩, fun ⟨b, hb⟩ => by rw [← hb, mul_assoc, e.mul_self]⟩

/-- The right ideal `e A = {a | e * a = a}`, as a submodule over `Aᵐᵒᵖ`. -/
def rightIdeal : Submodule Aᵐᵒᵖ A where
  carrier := {a | e.val * a = a}
  add_mem' ha hb := by simp only [Set.mem_ofPred_eq] at *; rw [mul_add, ha, hb]
  zero_mem' := mul_zero _
  smul_mem' r a ha := by
    simp only [Set.mem_ofPred_eq, MulOpposite.smul_eq_mul_unop] at *; rw [← mul_assoc, ha]

theorem mem_rightIdeal {a : A} : a ∈ e.rightIdeal ↔ e.val * a = a := Iff.rfl

theorem val_mul_mem_rightIdeal (a : A) : e.val * a ∈ e.rightIdeal := by
  rw [mem_rightIdeal, ← mul_assoc, e.mul_self]

theorem rightIdeal_eq_span : e.rightIdeal = Submodule.span Aᵐᵒᵖ {e.val} := by
  ext a
  rw [Submodule.mem_span_singleton, mem_rightIdeal]
  exact ⟨fun h => ⟨op a, by rw [MulOpposite.smul_eq_mul_unop, unop_op, h]⟩,
    fun ⟨b, hb⟩ => by rw [← hb, MulOpposite.smul_eq_mul_unop, ← mul_assoc, e.mul_self]⟩

variable [DGRing A]

/-- The differential of a right multiple of `e`: `d (a * e) = d a * e`. -/
theorem d_mul_val (a : A) : d (a * e.val) = d a * e.val :=
  d_op_smul_of_d_eq_zero' (M := A) e.d_eq_zero a

/-- The differential of a left multiple of `e`: `d (e * a) = e * d a`. -/
theorem d_val_mul (a : A) : d (e.val * a) = e.val * d a := by
  rw [d_mul_of_mem_zero e.mem_zero, e.d_eq_zero, zero_mul, zero_add]

theorem coe_decompose_mul_val (a : A) (n : ℤ) :
    (decompose (grading (M := A)) (a * e.val) n : A) = decompose (grading (M := A)) a n * e.val :=
  DirectSum.coe_decompose_mul_of_right_mem_zero _ e.mem_zero

theorem coe_decompose_val_mul (a : A) (n : ℤ) :
    (decompose (grading (M := A)) (e.val * a) n : A) = e.val * decompose (grading (M := A)) a n :=
  DirectSum.coe_decompose_mul_of_left_mem_zero _ e.mem_zero

/-! ### The left ideal `A e` -/

theorem d_mem_leftIdeal {a : A} (ha : a ∈ e.leftIdeal) : d a ∈ e.leftIdeal := by
  rw [mem_leftIdeal] at *
  rw [← ha, e.d_mul_val, mul_assoc, e.mul_self]

theorem decompose_mem_leftIdeal {a : A} (ha : a ∈ e.leftIdeal) (n : ℤ) :
    (decompose (grading (M := A)) a n : A) ∈ e.leftIdeal := by
  rw [mem_leftIdeal] at *
  rw [← e.coe_decompose_mul_val, ha]

/-- The left ideal `A e` as a type; a dg left `A`-module and a dg right `e A e`-module. -/
abbrev LeftCorner : Type _ := e.leftIdeal

namespace LeftCorner

/-- The differential of `A e`, the restriction of that of `A`. -/
def dAddHom : e.LeftCorner →+ e.LeftCorner where
  toFun a := ⟨d a, e.d_mem_leftIdeal a.2⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [d_add]

noncomputable instance instDGAddCommGroup : DGAddCommGroup e.LeftCorner :=
  DGAddCommGroup.ofInjective (AddSubmonoidClass.subtype e.leftIdeal) Subtype.val_injective
    (dAddHom e) (fun _ => rfl) fun n a =>
      ⟨⟨_, e.decompose_mem_leftIdeal a.2 n⟩, rfl⟩

@[simp]
theorem coe_d (a : e.LeftCorner) : ((d a : e.LeftCorner) : A) = d (a : A) := rfl

theorem mem_grading_iff {n : ℤ} {a : e.LeftCorner} : a ∈ grading n ↔ (a : A) ∈ grading n :=
  Iff.rfl

/-- The homogeneous components of an element of `A e` are those of the underlying element of
`A` (which lie in `A e`). -/
@[simp]
theorem coe_decompose (a : e.LeftCorner) (n : ℤ) :
    ((decompose (grading (M := e.LeftCorner)) a n : e.LeftCorner) : A) =
      decompose (grading (M := A)) (a : A) n :=
  DGAddCommGroup.ofInjective_coe_decompose (AddSubmonoidClass.subtype e.leftIdeal)
    Subtype.val_injective (dAddHom e) (fun _ => rfl) _ a n

/-- `A e` is a dg left `A`-module. -/
instance instDGModule : DGModule A e.LeftCorner where
  smul_mem _ _ _ _ ha hb := mul_mem_grading ha hb
  d_smul' {n a} ha b := by
    apply Subtype.ext
    simp only [coe_d, Submodule.coe_smul, Submodule.coe_add, Units.smul_def,
      Submodule.coe_smul_of_tower]
    exact d_mul ha b

end LeftCorner

/-! ### The corner ring `e A e` -/

/-- The corner ring `e A e = {a | e * a * e = a}`, a ring with unit `e` (Mathlib's
`IsIdempotentElem.Corner`); it is not a subring of `A` unless `e = 1`. -/
abbrev Corner : Type _ := e.isIdempotentElem.Corner

namespace Corner

omit [DGRing A] in
/-- The underlying element of `A` of an element of `e A e`. -/
def val (x : e.Corner) : A := Subtype.val x

instance : CoeOut e.Corner A := ⟨val e⟩

omit [DGRing A] in
@[simp] theorem val_mk (a : A) (h : a ∈ Subsemigroup.corner e.val) : val e ⟨a, h⟩ = a := rfl

omit [DGRing A] in
theorem coe_mem (x : e.Corner) : (x : A) ∈ Subsemigroup.corner e.val := Subtype.property x

omit [DGRing A] in
theorem mem_iff {a : A} : a ∈ Subsemigroup.corner e.val ↔ e.val * a = a ∧ a * e.val = a :=
  Subsemigroup.mem_corner_iff e.isIdempotentElem

omit [DGRing A] in
theorem val_mul_coe (x : e.Corner) : e.val * (x : A) = x := (mem_iff e |>.mp (coe_mem e x)).1

omit [DGRing A] in
theorem coe_mul_val (x : e.Corner) : (x : A) * e.val = x := (mem_iff e |>.mp (coe_mem e x)).2

omit [DGRing A] in
theorem val_mul_mul_val_mem (a : A) : e.val * a * e.val ∈ Subsemigroup.corner e.val :=
  ⟨a, rfl⟩

omit [DGRing A] in
@[simp] theorem coe_zero : ((0 : e.Corner) : A) = 0 := rfl
omit [DGRing A] in
@[simp] theorem coe_one : ((1 : e.Corner) : A) = e.val := rfl
omit [DGRing A] in
@[simp] theorem coe_add (x y : e.Corner) : ((x + y : e.Corner) : A) = x + y := rfl
omit [DGRing A] in
@[simp] theorem coe_neg (x : e.Corner) : ((-x : e.Corner) : A) = -x := rfl
omit [DGRing A] in
@[simp] theorem coe_sub (x y : e.Corner) : ((x - y : e.Corner) : A) = x - y := rfl
omit [DGRing A] in
@[simp] theorem coe_mul (x y : e.Corner) : ((x * y : e.Corner) : A) = x * y := rfl
omit [DGRing A] in
@[simp] theorem coe_zsmul (k : ℤ) (x : e.Corner) : ((k • x : e.Corner) : A) = k • (x : A) :=
  rfl

omit [DGRing A] in
theorem coe_injective : Function.Injective ((↑) : e.Corner → A) := Subtype.val_injective

omit [DGRing A] in
@[ext] theorem ext {x y : e.Corner} (h : (x : A) = y) : x = y := Subtype.ext h

omit [DGRing A] in
/-- The inclusion `e A e → A` as an additive map (it is not unital). -/
def valAddHom : e.Corner →+ A where
  toFun := val e
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DGRing A] in
@[simp] theorem valAddHom_apply (x : e.Corner) : valAddHom e x = x := rfl

theorem d_mem {a : A} (ha : a ∈ Subsemigroup.corner e.val) :
    d a ∈ Subsemigroup.corner e.val := by
  obtain ⟨he, he'⟩ := (mem_iff e).mp ha
  refine ⟨d a, ?_⟩
  conv_rhs => rw [← he, ← he', e.d_val_mul, e.d_mul_val, ← mul_assoc]

theorem decompose_mem {a : A} (ha : a ∈ Subsemigroup.corner e.val) (n : ℤ) :
    (decompose (grading (M := A)) a n : A) ∈ Subsemigroup.corner e.val := by
  obtain ⟨he, he'⟩ := (mem_iff e).mp ha
  refine ⟨decompose (grading (M := A)) a n, ?_⟩
  conv_rhs => rw [← he, ← he', e.coe_decompose_val_mul, e.coe_decompose_mul_val, ← mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The differential of `e A e`, the restriction of that of `A`. -/
def dAddHom : e.Corner →+ e.Corner where
  toFun x := ⟨d x, d_mem e (coe_mem e x)⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [d_add]

noncomputable instance instDGAddCommGroup : DGAddCommGroup e.Corner :=
  DGAddCommGroup.ofInjective (valAddHom e) (coe_injective e) (dAddHom e) (fun _ => rfl)
    fun n x => ⟨⟨_, decompose_mem e (coe_mem e x) n⟩, rfl⟩

@[simp]
theorem coe_d (x : e.Corner) : ((d x : e.Corner) : A) = d (x : A) := rfl

theorem mem_grading_iff {n : ℤ} {x : e.Corner} : x ∈ grading n ↔ (x : A) ∈ grading n :=
  Iff.rfl

/-- The homogeneous components of an element of `e A e` are those of the underlying element
of `A` (which lie in `e A e`). -/
@[simp]
theorem coe_decompose (x : e.Corner) (n : ℤ) :
    ((decompose (grading (M := e.Corner)) x n : e.Corner) : A) =
      decompose (grading (M := A)) (x : A) n :=
  DGAddCommGroup.ofInjective_coe_decompose (valAddHom e) (coe_injective e) (dAddHom e)
    (fun _ => rfl) _ x n

/-- `e A e` is a dg ring, with the differential restricted from `A`. -/
instance instDGRing : DGRing e.Corner where
  one_mem := e.mem_zero
  mul_mem _ _ _ _ hx hy := mul_mem_grading (A := A) hx hy
  d_mul' {n x} hx y := by
    apply ext
    simp only [coe_d, coe_mul, coe_add, Units.smul_def, coe_zsmul]
    exact d_mul (A := A) hx y

end Corner

/-! ### `A e` as a dg `(A, e A e)`-bimodule -/

namespace LeftCorner

omit [DGRing A] in
theorem coe_mul_corner_mem (a : e.LeftCorner) (y : e.Corner) :
    (a : A) * (y : A) ∈ e.leftIdeal := by
  rw [mem_leftIdeal, mul_assoc, Corner.coe_mul_val]

/-- The right action of `e A e` on `A e` by multiplication, `op y • a = a * y`. -/
instance instSMulOp : SMul e.Cornerᵐᵒᵖ e.LeftCorner :=
  ⟨fun y a => ⟨(a : A) * (y.unop : A), coe_mul_corner_mem e a y.unop⟩⟩

omit [DGRing A] in
@[simp]
theorem coe_op_smul (y : e.Corner) (a : e.LeftCorner) : ((op y • a : e.LeftCorner) : A) = a * y :=
  rfl

omit [DGRing A] in
theorem coe_smul_op (y : e.Cornerᵐᵒᵖ) (a : e.LeftCorner) :
    ((y • a : e.LeftCorner) : A) = a * (y.unop : A) :=
  rfl

/-- `A e` is a right `e A e`-module. -/
instance instModuleOp : Module e.Cornerᵐᵒᵖ e.LeftCorner where
  one_smul a := Subtype.ext (by rw [coe_smul_op, unop_one, Corner.coe_one]; exact a.2)
  mul_smul y z a := Subtype.ext (by simp only [coe_smul_op, unop_mul, Corner.coe_mul, mul_assoc])
  smul_zero y := Subtype.ext (by simp only [coe_smul_op, Submodule.coe_zero, zero_mul])
  smul_add y a b := Subtype.ext (by simp only [coe_smul_op, Submodule.coe_add, add_mul])
  add_smul y z a := Subtype.ext (by
    simp only [coe_smul_op, unop_add, Corner.coe_add, mul_add, Submodule.coe_add])
  zero_smul a := Subtype.ext (by simp only [coe_smul_op, unop_zero, Corner.coe_zero, mul_zero,
    Submodule.coe_zero])

/-- `A e` is a dg right `e A e`-module. -/
instance instDGRightModule : DGRightModule e.Corner e.LeftCorner where
  op_smul_mem' hy ha := mul_mem_grading (A := A) ha hy
  d_op_smul' {j a} ha y := by
    apply Subtype.ext
    simp only [coe_d, coe_op_smul, Submodule.coe_add, Units.smul_def, Submodule.coe_smul_of_tower,
      Corner.coe_d]
    exact d_mul (A := A) ha y

/-- The left action of `A` and the right action of `e A e` on `A e` commute. -/
instance instSMulCommClass : SMulCommClass A e.Cornerᵐᵒᵖ e.LeftCorner where
  smul_comm x y a := Subtype.ext (by
    simp only [coe_smul_op, Submodule.coe_smul, smul_eq_mul, mul_assoc])

/-- `A e` is a dg `(A, e A e)`-bimodule. -/
instance instDGBimodule : DGBimodule A e.Corner e.LeftCorner := DGBimodule.mk'

end LeftCorner

/-! ### `e A` as a dg `(e A e, A)`-bimodule -/

theorem d_mem_rightIdeal {a : A} (ha : a ∈ e.rightIdeal) : d a ∈ e.rightIdeal := by
  rw [mem_rightIdeal] at *
  rw [← ha, e.d_val_mul, ← mul_assoc, e.mul_self]

theorem decompose_mem_rightIdeal {a : A} (ha : a ∈ e.rightIdeal) (n : ℤ) :
    (decompose (grading (M := A)) a n : A) ∈ e.rightIdeal := by
  rw [mem_rightIdeal] at *
  rw [← e.coe_decompose_val_mul, ha]

/-- The right ideal `e A` as a type; a dg right `A`-module and a dg left `e A e`-module. -/
abbrev RightCorner : Type _ := e.rightIdeal

namespace RightCorner

/-- The differential of `e A`, the restriction of that of `A`. -/
def dAddHom : e.RightCorner →+ e.RightCorner where
  toFun a := ⟨d a, e.d_mem_rightIdeal a.2⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [d_add]

noncomputable instance instDGAddCommGroup : DGAddCommGroup e.RightCorner :=
  DGAddCommGroup.ofInjective (AddSubmonoidClass.subtype e.rightIdeal) Subtype.val_injective
    (dAddHom e) (fun _ => rfl) fun n a =>
      ⟨⟨_, e.decompose_mem_rightIdeal a.2 n⟩, rfl⟩

@[simp]
theorem coe_d (a : e.RightCorner) : ((d a : e.RightCorner) : A) = d (a : A) := rfl

theorem mem_grading_iff {n : ℤ} {a : e.RightCorner} : a ∈ grading n ↔ (a : A) ∈ grading n :=
  Iff.rfl

/-- The homogeneous components of an element of `e A` are those of the underlying element of
`A` (which lie in `e A`). -/
@[simp]
theorem coe_decompose (a : e.RightCorner) (n : ℤ) :
    ((decompose (grading (M := e.RightCorner)) a n : e.RightCorner) : A) =
      decompose (grading (M := A)) (a : A) n :=
  DGAddCommGroup.ofInjective_coe_decompose (AddSubmonoidClass.subtype e.rightIdeal)
    Subtype.val_injective (dAddHom e) (fun _ => rfl) _ a n

/-- `e A` is a dg right `A`-module. -/
instance instDGRightModule : DGRightModule A e.RightCorner where
  op_smul_mem' ha hb := by
    rw [mem_grading_iff, Submodule.coe_smul, op_smul_eq_mul]; exact mul_mem_grading hb ha
  d_op_smul' {j a} ha b := by
    apply Subtype.ext
    simp only [coe_d, Submodule.coe_smul, Submodule.coe_add, Units.smul_def,
      Submodule.coe_smul_of_tower, op_smul_eq_mul]
    exact d_mul ha b

omit [DGRing A] in
theorem corner_mul_coe_mem (y : e.Corner) (a : e.RightCorner) :
    (y : A) * (a : A) ∈ e.rightIdeal := by
  rw [mem_rightIdeal, ← mul_assoc, Corner.val_mul_coe]

/-- The left action of `e A e` on `e A` by multiplication. -/
instance instSMul : SMul e.Corner e.RightCorner :=
  ⟨fun y a => ⟨(y : A) * (a : A), corner_mul_coe_mem e y a⟩⟩

omit [DGRing A] in
@[simp]
theorem coe_corner_smul (y : e.Corner) (a : e.RightCorner) :
    ((y • a : e.RightCorner) : A) = y * a :=
  rfl

/-- `e A` is a left `e A e`-module. -/
instance instModule : Module e.Corner e.RightCorner where
  one_smul a := Subtype.ext (by rw [coe_corner_smul, Corner.coe_one]; exact a.2)
  mul_smul y z a := Subtype.ext (by simp only [coe_corner_smul, Corner.coe_mul, mul_assoc])
  smul_zero y := Subtype.ext (by simp only [coe_corner_smul, Submodule.coe_zero, mul_zero])
  smul_add y a b := Subtype.ext (by simp only [coe_corner_smul, Submodule.coe_add, mul_add])
  add_smul y z a := Subtype.ext (by
    simp only [coe_corner_smul, Corner.coe_add, add_mul, Submodule.coe_add])
  zero_smul a := Subtype.ext (by
    simp only [coe_corner_smul, Corner.coe_zero, zero_mul, Submodule.coe_zero])

/-- `e A` is a dg left `e A e`-module. -/
instance instDGModule : DGModule e.Corner e.RightCorner where
  smul_mem _ _ _ _ hy ha := mul_mem_grading (A := A) hy ha
  d_smul' {n y} hy a := by
    apply Subtype.ext
    simp only [coe_d, coe_corner_smul, Submodule.coe_add, Units.smul_def,
      Submodule.coe_smul_of_tower, Corner.coe_d]
    exact d_mul (A := A) hy a

/-- The left action of `e A e` and the right action of `A` on `e A` commute. -/
instance instSMulCommClass : SMulCommClass e.Corner Aᵐᵒᵖ e.RightCorner where
  smul_comm y x a := Subtype.ext (by
    simp only [coe_corner_smul, Submodule.coe_smul, MulOpposite.smul_eq_mul_unop, mul_assoc])

/-- `e A` is a dg `(e A e, A)`-bimodule. -/
instance instDGBimodule : DGBimodule e.Corner A e.RightCorner := DGBimodule.mk'

end RightCorner

end DGIdempotent

end DG
