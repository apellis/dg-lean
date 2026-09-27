import DG.Module.Corner
import DG.Module.EndBimodule

/-!
# Endomorphism dg rings of corner modules

Let `A` be a dg ring and `e ∈ A⁰` an idempotent. This file identifies the endomorphism dg ring
`END_A(A e)` of the dg left `A`-module `A e` with the corner ring `e A e`.

An `A`-linear map `f : A e → A e` of degree `n` (with the Koszul sign,
`f (a • x) = (-1)^{n |a|} • (a • f x)`) is determined by `f e`, which lies in `e A e` since
`f e = f (e • e) = e • f e`. With the product `f * g = (-1)^{|f||g|} • g ∘ f` of
`DG.DGModule.END` (for which `M` is a right `END_A(M)`-module), `F ↦ e · F` is a ring
isomorphism `END_A(A e) ≃+* e A e` with no opposite ring: for `f` of degree `m` and `g` of
degree `n`, `(f * g) e = (-1)^{m n} • g (f e) = (-1)^{m n} (-1)^{m n} • (f e * g e)`. Its inverse
sends `y` to the right multiplication `x ↦ x * y`. It is an instance of
`DG.DGBimodule.endEquivOfGenerator`, applied to the dg `(A, e A e)`-bimodule `A e` and its
generator `e`.

## Main definitions and results

* `DG.DGModule.END.selfEquiv : END A A ≃+* A`, the case `e = 1`.
* `DG.DGIdempotent.endLeftCornerEquiv : END A e.LeftCorner ≃+* e.Corner` for a dg idempotent
  (`d e = 0`), preserving degrees (`DG.DGIdempotent.endLeftCornerEquiv_mem_grading_iff`) and
  differentials (`DG.DGIdempotent.endLeftCornerEquiv_d`).
* `DG.LeftDGIdempotent A`: a degree-`0` idempotent with `d e ∈ A e` (equivalently
  `e * d e = 0`, `DG.LeftDGIdempotent.val_mul_d`). Then `A e` is a dg left `A`-submodule of `A`,
  and `e A e` (`DG.LeftDGIdempotent.Corner`, a type synonym of Mathlib's
  `IsIdempotentElem.Corner`) is a dg ring for the differential `x ↦ e * d x`, that is,
  `e a e ↦ e * d (a * e)` (`DG.LeftDGIdempotent.Corner.coe_d_mk`); `A e` is a dg
  `(A, e A e)`-bimodule, and `DG.LeftDGIdempotent.endLeftCornerEquiv :
  END A e.LeftCorner ≃+* e.Corner` is an isomorphism of dg rings. The differential is forced:
  for `f` of degree `n`, `(δ f) e = d (f e) - (-1)^n • f (d e) = d (f e) - d e * f e`, since
  `d e = d e • e`, and this equals `e * d (f e)` because `f e = e * f e`.
* `DG.DGIdempotent.toLeftDGIdempotent` and `DG.DGIdempotent.toLeftDGIdempotentCornerEquiv`:
  for `d e = 0` the two constructions of `e A e` agree (`e * d x = d x` on `e A e`).
-/

open DirectSum MulOpposite

namespace DG

/-! ### The regular module: `END_A(A) ≅ A` -/

namespace DGModule.END

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The endomorphism dg ring of the regular dg module is `A` itself: the isomorphism of dg
rings `END_A(A) ≃+* A` sends `F` to `1 · F`, the value at `1` of its degree-`n` components
summed over `n`; its inverse sends `a` to the right multiplication `x ↦ x * a` (with the Koszul
sign `(-1)^{|a||x|}` built into the cochains). -/
noncomputable def selfEquiv : END A A ≃+* A :=
  DGBimodule.endEquivOfGenerator A A 1 (fun x => ⟨x, by rw [smul_eq_mul, mul_one]⟩)
    (fun a b (h : op a • (1 : A) = op b • 1) => by simpa only [op_smul_eq_mul, one_mul] using h)
    (fun F => op F • (1 : A)) fun F => by rw [op_smul_eq_mul, one_mul]

variable {A}

@[simp]
theorem selfEquiv_apply (F : END A A) : selfEquiv A F = op F • (1 : A) := rfl

theorem selfEquiv_of {n : ℤ} (f : Cochain A A A n) :
    selfEquiv A (DirectSum.of (fun n => Cochain A A A n) n f) = f 1 := by
  rw [selfEquiv_apply, op_of_smul f one_mem_grading, mul_zero, koszulSign, Int.negOnePow_zero,
    one_smul]

/-- The inverse of `DG.DGModule.END.selfEquiv` acts on `A` by right multiplication. -/
@[simp]
theorem op_selfEquiv_symm_smul (a x : A) : op ((selfEquiv A).symm a) • x = x * a := by
  rw [selfEquiv, DGBimodule.endEquivOfGenerator_symm_apply, DGBimodule.op_toEND_smul,
    op_smul_eq_mul]

theorem selfEquiv_d (F : END A A) : selfEquiv A (d F) = d (selfEquiv A F) :=
  DGBimodule.endEquivOfGenerator_d F

theorem selfEquiv_mem_grading_iff {n : ℤ} {F : END A A} :
    selfEquiv A F ∈ grading n ↔ F ∈ grading n :=
  DGBimodule.endEquivOfGenerator_mem_grading_iff

end DGModule.END

/-! ### Corners of a dg idempotent with `d e = 0` -/

namespace DGIdempotent

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] (e : DGIdempotent A)

namespace LeftCorner

/-- The idempotent `e` as an element of `A e`; it generates `A e` as a left `A`-module. -/
def idem : e.LeftCorner := ⟨e.val, e.mul_self⟩

omit [DGRing A] in
@[simp]
theorem coe_idem : (idem e : A) = e.val := rfl

theorem idem_mem_grading : idem e ∈ grading 0 := e.mem_zero

omit [DGRing A] in
theorem smul_idem (x : e.LeftCorner) : (x : A) • idem e = x := Subtype.ext x.2

omit [DGRing A] in
theorem val_smul_idem : e.val • idem e = idem e := Subtype.ext e.mul_self

/-- The value `e · F` of an endomorphism of `A e` at the generator lies in `e A e`. -/
theorem op_smul_idem_mem (F : DGModule.END A e.LeftCorner) :
    ((op F • idem e : e.LeftCorner) : A) ∈ Subsemigroup.corner e.val := by
  refine (Corner.mem_iff e).mpr ⟨?_, (op F • idem e).2⟩
  conv_rhs => rw [← val_smul_idem e, ← smul_comm]
  rfl

end LeftCorner

open LeftCorner

/-- The value at `e` of an endomorphism of `A e`, as an element of `e A e`. -/
noncomputable def endToCorner (F : DGModule.END A e.LeftCorner) : e.Corner :=
  ⟨_, op_smul_idem_mem e F⟩

/-- For a dg idempotent `e` (`e ∈ A⁰`, `e * e = e`, `d e = 0`), the endomorphism dg ring of
the dg left `A`-module `A e` is the corner dg ring `e A e`: the ring isomorphism sends `F` to
`e · F`, which on a homogeneous `f` of degree `n` is `f e`
(`DG.DGIdempotent.endLeftCornerEquiv_of`); it preserves the degrees and the differentials. With
the product
`f * g = (-1)^{|f||g|} • g ∘ f` of `END` there is no opposite ring: `(f * g) e = f e * g e`.
The inverse sends `y ∈ e A e` to the right multiplication `x ↦ x * y` on `A e`. -/
noncomputable def endLeftCornerEquiv : DGModule.END A e.LeftCorner ≃+* e.Corner :=
  DGBimodule.endEquivOfGenerator A e.LeftCorner (idem e) (fun x => ⟨x, smul_idem e x⟩)
    (fun y z h => Corner.ext e (by
      simpa only [LeftCorner.coe_op_smul, coe_idem, Corner.val_mul_coe] using
        congrArg Subtype.val h))
    (endToCorner e) fun F => Subtype.ext (by
      rw [LeftCorner.coe_op_smul, coe_idem]
      exact ((Corner.mem_iff e).mp (op_smul_idem_mem e F)).1)

theorem coe_endLeftCornerEquiv (F : DGModule.END A e.LeftCorner) :
    (e.endLeftCornerEquiv F : A) = (op F • idem e : e.LeftCorner) := rfl

theorem endLeftCornerEquiv_of {n : ℤ} (f : Cochain A e.LeftCorner e.LeftCorner n) :
    (e.endLeftCornerEquiv (DirectSum.of (fun n => Cochain A e.LeftCorner e.LeftCorner n) n f) :
      A) = f (idem e) := by
  rw [coe_endLeftCornerEquiv, DGModule.END.op_of_smul f (idem_mem_grading e), mul_zero,
    koszulSign, Int.negOnePow_zero, one_smul]

/-- The inverse of `DG.DGIdempotent.endLeftCornerEquiv` sends `y` to the right multiplication by
`y`. -/
theorem coe_op_endLeftCornerEquiv_symm_smul (y : e.Corner) (x : e.LeftCorner) :
    ((op (e.endLeftCornerEquiv.symm y) • x : e.LeftCorner) : A) = x * y := by
  rw [endLeftCornerEquiv, DGBimodule.endEquivOfGenerator_symm_apply, DGBimodule.op_toEND_smul,
    LeftCorner.coe_op_smul]

theorem endLeftCornerEquiv_d (F : DGModule.END A e.LeftCorner) :
    e.endLeftCornerEquiv (d F) = d (e.endLeftCornerEquiv F) :=
  DGBimodule.endEquivOfGenerator_d F

theorem endLeftCornerEquiv_mem_grading_iff {n : ℤ} {F : DGModule.END A e.LeftCorner} :
    e.endLeftCornerEquiv F ∈ grading n ↔ F ∈ grading n :=
  DGBimodule.endEquivOfGenerator_mem_grading_iff

end DGIdempotent

/-! ### Idempotents with `d e ∈ A e` -/

/-- A degree-`0` idempotent of a dg ring whose differential lies in the left ideal `A e`:
`e ∈ A⁰`, `e * e = e` and `d e * e = d e`. Equivalently (`DG.LeftDGIdempotent.val_mul_d`),
`e * d e = 0`. Then `A e` is a dg left `A`-submodule of `A`, but `e A e` is in general not
stable under `d`; it is a dg ring for the differential `x ↦ e * d x`
(`DG.LeftDGIdempotent.Corner.instDGRing`). Every `DGIdempotent` (for which `d e = 0`) is one
(`DG.DGIdempotent.toLeftDGIdempotent`). -/
structure LeftDGIdempotent (A : Type*) [Ring A] [DGAddCommGroup A] where
  /-- The underlying element. -/
  val : A
  mem_zero : val ∈ grading (M := A) 0
  mul_self : val * val = val
  d_mul_self : d val * val = d val

/-- A degree-`0` idempotent cocycle is a degree-`0` idempotent with `d e ∈ A e`. -/
def DGIdempotent.toLeftDGIdempotent {A : Type*} [Ring A] [DGAddCommGroup A]
    (e : DGIdempotent A) : LeftDGIdempotent A where
  val := e.val
  mem_zero := e.mem_zero
  mul_self := e.mul_self
  d_mul_self := by rw [e.d_eq_zero, zero_mul]

namespace LeftDGIdempotent

variable {A : Type*} [Ring A] [DGAddCommGroup A] (e : LeftDGIdempotent A)

theorem isIdempotentElem : IsIdempotentElem e.val := e.mul_self

/-- The left ideal `A e = {a | a * e = a}`. -/
def leftIdeal : Ideal A where
  carrier := {a | a * e.val = a}
  add_mem' ha hb := by simp only [Set.mem_setOf_eq] at *; rw [add_mul, ha, hb]
  zero_mem' := zero_mul _
  smul_mem' r a ha := by simp only [Set.mem_setOf_eq, smul_eq_mul] at *; rw [mul_assoc, ha]

theorem mem_leftIdeal {a : A} : a ∈ e.leftIdeal ↔ a * e.val = a := Iff.rfl

/-! #### The corner ring `e A e` -/

/-- The corner ring `e A e` (Mathlib's `IsIdempotentElem.Corner`, a ring with unit `e`), to be
equipped with the differential `x ↦ e * d x`. It is a type synonym, so that this differential
does not conflict with the restricted differential on `DG.DGIdempotent.Corner`. -/
def Corner : Type _ := e.isIdempotentElem.Corner

namespace Corner

instance : Ring e.Corner := inferInstanceAs (Ring e.isIdempotentElem.Corner)

/-- The underlying element of `A` of an element of `e A e`. -/
def val (x : e.Corner) : A := Subtype.val (p := (· ∈ Subsemigroup.corner e.val)) x

instance : CoeOut e.Corner A := ⟨val e⟩

/-- The element of `e A e` given by an element of `A` in the corner. -/
def mk (a : A) (h : a ∈ Subsemigroup.corner e.val) : e.Corner := ⟨a, h⟩

@[simp] theorem coe_mk (a : A) (h : a ∈ Subsemigroup.corner e.val) : (mk e a h : A) = a := rfl

theorem coe_mem (x : e.Corner) : (x : A) ∈ Subsemigroup.corner e.val :=
  Subtype.property (p := (· ∈ Subsemigroup.corner e.val)) x

theorem mem_iff {a : A} : a ∈ Subsemigroup.corner e.val ↔ e.val * a = a ∧ a * e.val = a :=
  Subsemigroup.mem_corner_iff e.isIdempotentElem

theorem val_mul_coe (x : e.Corner) : e.val * (x : A) = x := (mem_iff e |>.mp (coe_mem e x)).1

theorem coe_mul_val (x : e.Corner) : (x : A) * e.val = x := (mem_iff e |>.mp (coe_mem e x)).2

@[simp] theorem coe_zero : ((0 : e.Corner) : A) = 0 := rfl
@[simp] theorem coe_one : ((1 : e.Corner) : A) = e.val := rfl
@[simp] theorem coe_add (x y : e.Corner) : ((x + y : e.Corner) : A) = x + y := rfl
@[simp] theorem coe_neg (x : e.Corner) : ((-x : e.Corner) : A) = -x := rfl
@[simp] theorem coe_sub (x y : e.Corner) : ((x - y : e.Corner) : A) = x - y := rfl
@[simp] theorem coe_mul (x y : e.Corner) : ((x * y : e.Corner) : A) = x * y := rfl
@[simp] theorem coe_zsmul (k : ℤ) (x : e.Corner) : ((k • x : e.Corner) : A) = k • (x : A) :=
  rfl

theorem coe_injective : Function.Injective ((↑) : e.Corner → A) :=
  Subtype.val_injective (p := (· ∈ Subsemigroup.corner e.val))

@[ext] theorem ext {x y : e.Corner} (h : (x : A) = y) : x = y := coe_injective e h

/-- The inclusion `e A e → A` as an additive map (it is not unital). -/
def valAddHom : e.Corner →+ A where
  toFun := val e
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem valAddHom_apply (x : e.Corner) : valAddHom e x = x := rfl

end Corner


variable [DGRing A]

/-- For a degree-`0` idempotent, `d e ∈ A e` is equivalent to `e * d e = 0`. -/
theorem val_mul_d : e.val * d e.val = 0 := by
  have h := d_mul_of_mem_zero e.mem_zero e.val
  rw [e.mul_self, e.d_mul_self] at h
  exact left_eq_add.mp h

/-- `A e` is stable under `d`: `d (a * e) * e = d (a * e)`. -/
theorem d_mul_val_mul_val (a : A) : d (a * e.val) * e.val = d (a * e.val) := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rw [d_mul a.2, add_mul, mul_assoc, e.mul_self, smul_mul_assoc, mul_assoc, e.d_mul_self]
  | h_add a b ha hb => rw [add_mul, d_add, add_mul, ha, hb]

theorem d_mem_leftIdeal {a : A} (ha : a ∈ e.leftIdeal) : d a ∈ e.leftIdeal := by
  rw [mem_leftIdeal] at *
  conv_lhs => rw [← ha]
  rw [e.d_mul_val_mul_val, ha]

theorem decompose_mem_leftIdeal {a : A} (ha : a ∈ e.leftIdeal) (n : ℤ) :
    (decompose (grading (M := A)) a n : A) ∈ e.leftIdeal := by
  rw [mem_leftIdeal] at *
  rw [← DirectSum.coe_decompose_mul_of_right_mem_zero _ e.mem_zero, ha]

/-! #### The left ideal `A e` -/

/-- The left ideal `A e` as a type; a dg left `A`-module (with the differential of `A`) and a
dg right `e A e`-module. -/
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

/-- `A e` is a dg left `A`-module. -/
instance instDGModule : DGModule A e.LeftCorner where
  smul_mem _ _ _ _ ha hb := mul_mem_grading ha hb
  d_smul' {n a} ha b := by
    apply Subtype.ext
    simp only [coe_d, Submodule.coe_smul, Submodule.coe_add, Units.smul_def,
      Submodule.coe_smul_of_tower]
    exact d_mul ha b

/-- The idempotent `e` as an element of `A e`; it generates `A e` as a left `A`-module. -/
def idem : e.LeftCorner := ⟨e.val, e.mul_self⟩

omit [DGRing A] in
@[simp]
theorem coe_idem : (idem e : A) = e.val := rfl

theorem idem_mem_grading : idem e ∈ grading 0 := e.mem_zero

omit [DGRing A] in
theorem smul_idem (x : e.LeftCorner) : (x : A) • idem e = x := Subtype.ext x.2

omit [DGRing A] in
theorem val_smul_idem : e.val • idem e = idem e := Subtype.ext e.mul_self

end LeftCorner

/-! #### The differential `x ↦ e * d x` on the corner ring `e A e` -/

namespace Corner

theorem decompose_mem {a : A} (ha : a ∈ Subsemigroup.corner e.val) (n : ℤ) :
    (decompose (grading (M := A)) a n : A) ∈ Subsemigroup.corner e.val := by
  obtain ⟨he, he'⟩ := (mem_iff e).mp ha
  refine ⟨decompose (grading (M := A)) a n, ?_⟩
  conv_rhs => rw [← he, ← he', DirectSum.coe_decompose_mul_of_left_mem_zero _ e.mem_zero,
    DirectSum.coe_decompose_mul_of_right_mem_zero _ e.mem_zero, ← mul_assoc]

theorem hhom (n : ℤ) (x : e.Corner) :
    (decompose (grading (M := A)) (valAddHom e x) n : A) ∈ (valAddHom e).range :=
  ⟨mk e _ (decompose_mem e (coe_mem e x) n), rfl⟩

theorem val_mul_d_mem {a : A} (ha : a ∈ Subsemigroup.corner e.val) :
    e.val * d a ∈ Subsemigroup.corner e.val := by
  have h := e.d_mul_val_mul_val a
  rw [((mem_iff e).mp ha).2] at h
  exact ⟨d a, show e.val * d a * e.val = _ by rw [mul_assoc, h]⟩

/-- The differential `x ↦ e * d x` of `e A e`. -/
def dAddHom : e.Corner →+ e.Corner where
  toFun x := mk e _ (val_mul_d_mem e (coe_mem e x))
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [d_add, mul_add]

/-- `e A e` is a dg abelian group, with the grading restricted from `A` and the differential
`x ↦ e * d x`. -/
noncomputable instance instDGAddCommGroup : DGAddCommGroup e.Corner where
  grading := gradingComap (valAddHom e)
  decomposition :=
    (isInternal_gradingComap (valAddHom e) (coe_injective e) (hhom e)).chooseDecomposition
  d := dAddHom e
  d_mem' {n x} hx := by
    rw [mem_gradingComap]
    simpa using mul_mem_grading e.mem_zero (d_mem hx)
  d_d' x := ext e (by
    show e.val * d (e.val * d (x : A)) = 0
    rw [d_mul_of_mem_zero e.mem_zero, d_d, mul_zero, add_zero, ← mul_assoc, val_mul_d,
      zero_mul])

/-- The differential of `e A e` is `x ↦ e * d x`. -/
@[simp]
theorem coe_d (x : e.Corner) : ((d x : e.Corner) : A) = e.val * d (x : A) := rfl

/-- The differential of `e A e` in the form `e a e ↦ e * d (a * e)`. -/
theorem coe_d_mk (a : A) :
    ((d (mk e (e.val * a * e.val) ⟨a, rfl⟩) : e.Corner) : A) = e.val * d (a * e.val) := by
  rw [coe_d, coe_mk, mul_assoc, d_mul_of_mem_zero e.mem_zero, mul_add, ← mul_assoc,
    val_mul_d, zero_mul, zero_add, ← mul_assoc, e.mul_self]

/-- If `d e = 0`, the differential of `e A e` is the restriction of that of `A`. -/
theorem coe_d_of_d_eq_zero (h : d e.val = 0) (x : e.Corner) :
    ((d x : e.Corner) : A) = d (x : A) := by
  rw [coe_d]
  conv_rhs => rw [← val_mul_coe e x, d_mul_of_mem_zero e.mem_zero, h, zero_mul, zero_add]

theorem mem_grading_iff {n : ℤ} {x : e.Corner} : x ∈ grading n ↔ (x : A) ∈ grading n :=
  Iff.rfl

/-- The homogeneous components of an element of `e A e` are those of the underlying element
of `A` (which lie in `e A e`). -/
@[simp]
theorem coe_decompose (x : e.Corner) (n : ℤ) :
    ((decompose (grading (M := e.Corner)) x n : e.Corner) : A) =
      decompose (grading (M := A)) (x : A) n := by
  have h : gradingComapMap (valAddHom e) (decompose (grading (M := e.Corner)) x) =
      decompose (grading (M := A)) (x : A) := by
    apply (DirectSum.Decomposition.isInternal (grading (M := A))).injective
    change DirectSum.coeAddMonoidHom _ _ = (decompose (grading (M := A))).symm _
    rw [coeAddMonoidHom_gradingComapMap, Equiv.symm_apply_apply]
    change valAddHom e ((decompose (grading (M := e.Corner))).symm _) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [← h]
  simp only [gradingComapMap, DirectSum.map_apply]
  rfl

/-- `e A e` is a dg ring for the differential `x ↦ e * d x`. -/
instance instDGRing : DGRing e.Corner where
  one_mem := e.mem_zero
  mul_mem _ _ _ _ hx hy := mul_mem_grading (A := A) hx hy
  d_mul' {n x} hx y := by
    apply ext
    have hx' : (x : A) ∈ grading n := hx
    simp only [coe_d, coe_mul, coe_add, Units.smul_def, coe_zsmul]
    rw [d_mul hx', mul_add, mul_smul_comm, ← mul_assoc, ← mul_assoc, val_mul_coe,
      ← mul_assoc (x : A), coe_mul_val, Units.smul_def]

end Corner

/-! #### `A e` as a dg `(A, e A e)`-bimodule -/

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
theorem coe_op_smul (y : e.Corner) (a : e.LeftCorner) :
    ((op y • a : e.LeftCorner) : A) = a * y :=
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

/-- `A e` is a dg right `e A e`-module, for the differential `x ↦ e * d x` of `e A e`. -/
instance instDGRightModule : DGRightModule e.Corner e.LeftCorner where
  op_smul_mem' hy ha := mul_mem_grading (A := A) ha hy
  d_op_smul' {j a} ha y := by
    apply Subtype.ext
    simp only [coe_d, coe_op_smul, Submodule.coe_add, Units.smul_def, Submodule.coe_smul_of_tower,
      Corner.coe_d]
    have ha' : (a : A) ∈ grading j := ha
    rw [d_mul ha', ← mul_assoc (a : A), a.2, Units.smul_def]

/-- The left action of `A` and the right action of `e A e` on `A e` commute. -/
instance instSMulCommClass : SMulCommClass A e.Cornerᵐᵒᵖ e.LeftCorner where
  smul_comm x y a := Subtype.ext (by
    simp only [coe_smul_op, Submodule.coe_smul, smul_eq_mul, mul_assoc])

/-- `A e` is a dg `(A, e A e)`-bimodule. -/
instance instDGBimodule : DGBimodule A e.Corner e.LeftCorner := DGBimodule.mk'

/-- The value `e · F` of an endomorphism of `A e` at the generator lies in `e A e`. -/
theorem op_smul_idem_mem (F : DGModule.END A e.LeftCorner) :
    ((op F • idem e : e.LeftCorner) : A) ∈ Subsemigroup.corner e.val := by
  refine (Corner.mem_iff e).mpr ⟨?_, (op F • idem e).2⟩
  conv_rhs => rw [← val_smul_idem e, ← smul_comm]
  rfl

end LeftCorner

open LeftCorner

/-- The value at `e` of an endomorphism of `A e`, as an element of `e A e`. -/
noncomputable def endToCorner (F : DGModule.END A e.LeftCorner) : e.Corner :=
  Corner.mk e _ (op_smul_idem_mem e F)

/-- For a degree-`0` idempotent `e` with `d e ∈ A e`, the endomorphism dg ring of the dg left
`A`-module `A e` is the corner ring `e A e` with the differential `x ↦ e * d x`
(equivalently `e a e ↦ e * d (a * e)`, `DG.LeftDGIdempotent.Corner.coe_d_mk`): the ring
isomorphism sends `F` to `e · F`, which on a homogeneous `f` is `f e`; it preserves the degrees
and the differentials. The inverse sends `y ∈ e A e` to the right multiplication `x ↦ x * y`. -/
noncomputable def endLeftCornerEquiv : DGModule.END A e.LeftCorner ≃+* e.Corner :=
  DGBimodule.endEquivOfGenerator A e.LeftCorner (idem e) (fun x => ⟨x, smul_idem e x⟩)
    (fun y z h => Corner.ext e (by
      simpa only [LeftCorner.coe_op_smul, coe_idem, Corner.val_mul_coe] using
        congrArg Subtype.val h))
    (endToCorner e) fun F => Subtype.ext (by
      rw [LeftCorner.coe_op_smul, coe_idem]
      exact ((Corner.mem_iff e).mp (op_smul_idem_mem e F)).1)

theorem coe_endLeftCornerEquiv (F : DGModule.END A e.LeftCorner) :
    (e.endLeftCornerEquiv F : A) = (op F • idem e : e.LeftCorner) := rfl

theorem endLeftCornerEquiv_of {n : ℤ} (f : Cochain A e.LeftCorner e.LeftCorner n) :
    (e.endLeftCornerEquiv (DirectSum.of (fun n => Cochain A e.LeftCorner e.LeftCorner n) n f) :
      A) = f (idem e) := by
  rw [coe_endLeftCornerEquiv, DGModule.END.op_of_smul f (idem_mem_grading e), mul_zero,
    koszulSign, Int.negOnePow_zero, one_smul]

/-- The inverse of `DG.LeftDGIdempotent.endLeftCornerEquiv` sends `y` to the right
multiplication by `y`. -/
theorem coe_op_endLeftCornerEquiv_symm_smul (y : e.Corner) (x : e.LeftCorner) :
    ((op (e.endLeftCornerEquiv.symm y) • x : e.LeftCorner) : A) = x * y := by
  rw [endLeftCornerEquiv, DGBimodule.endEquivOfGenerator_symm_apply, DGBimodule.op_toEND_smul,
    LeftCorner.coe_op_smul]

/-- `DG.LeftDGIdempotent.endLeftCornerEquiv` commutes with the differentials: for `f` of degree
`n`, `(δ f) e = d (f e) - (-1)^n • f (d e) = e * d (f e)`. -/
theorem endLeftCornerEquiv_d (F : DGModule.END A e.LeftCorner) :
    e.endLeftCornerEquiv (d F) = d (e.endLeftCornerEquiv F) :=
  DGBimodule.endEquivOfGenerator_d F

theorem endLeftCornerEquiv_mem_grading_iff {n : ℤ} {F : DGModule.END A e.LeftCorner} :
    e.endLeftCornerEquiv F ∈ grading n ↔ F ∈ grading n :=
  DGBimodule.endEquivOfGenerator_mem_grading_iff

end LeftDGIdempotent

namespace DGIdempotent

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] (e : DGIdempotent A)

/-- For a dg idempotent `e` (`d e = 0`), the corner ring `e A e` of `e` regarded as a
`DG.LeftDGIdempotent` is the corner dg ring `DG.DGIdempotent.Corner`: the identity of the
underlying elements is a ring isomorphism preserving the degrees and the differentials
(`DG.DGIdempotent.toLeftDGIdempotentCornerEquiv_d`). -/
def toLeftDGIdempotentCornerEquiv : e.toLeftDGIdempotent.Corner ≃+* e.Corner where
  toFun x := ⟨(x : A), LeftDGIdempotent.Corner.coe_mem _ x⟩
  invFun y := LeftDGIdempotent.Corner.mk _ (y : A) (DGIdempotent.Corner.coe_mem e y)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [DGRing A] in
theorem coe_toLeftDGIdempotentCornerEquiv (x : e.toLeftDGIdempotent.Corner) :
    (e.toLeftDGIdempotentCornerEquiv x : A) = x := rfl

theorem toLeftDGIdempotentCornerEquiv_mem_grading_iff {n : ℤ} {x : e.toLeftDGIdempotent.Corner} :
    e.toLeftDGIdempotentCornerEquiv x ∈ grading n ↔ x ∈ grading n :=
  Iff.rfl

theorem toLeftDGIdempotentCornerEquiv_d (x : e.toLeftDGIdempotent.Corner) :
    e.toLeftDGIdempotentCornerEquiv (d x) = d (e.toLeftDGIdempotentCornerEquiv x) :=
  DGIdempotent.Corner.ext e (LeftDGIdempotent.Corner.coe_d_of_d_eq_zero _ e.d_eq_zero x)

end DGIdempotent

end DG
