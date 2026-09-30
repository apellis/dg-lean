import DG.Module.Equiv

/-!
# Shifts of dg modules

This file defines the shift `M⟦n⟧` of a dg module `M` by an integer `n`, on the level of
types; the categorical packaging (`CategoryTheory.HasShift` on the category of dg modules)
is built on top of it.

* `DG.Shift n M`: a type synonym for `M` with the grading `(M⟦n⟧)ᵏ = Mᵏ⁺ⁿ`, the differential
  `d_{M⟦n⟧} = (-1)ⁿ d_M` and, for a dg `A`-module `M`, the action twisted by the Koszul sign,
  `a • m = (-1)^{n |a|} (a • m)` for `a` homogeneous. These are the conventions of Mathlib's
  `CochainComplex.shiftFunctor` (`(K⟦n⟧).X i = K.X (i + n)`, `d = n.negOnePow • K.d`); the
  twist of the action is forced by the Leibniz rule.
* `DG.Shift.mk n : M ≃+ Shift n M` and `DG.Shift.unmk n : Shift n M ≃+ M`, the identity.
* `DG.Shift.twist A n : A →+* A`, the graded ring endomorphism `a ↦ (-1)^{n |a|} a`; the
  `A`-module structure of `M⟦n⟧` is that of `M` restricted along it.
* `DG.DGModuleHom.shift n : (M →ᵈᵍ[A] N) → (Shift n M →ᵈᵍ[A] Shift n N)`, the shift of
  morphisms (the same underlying function).
* `DG.Shift.zeroEquiv : Shift 0 M ≃ᵈᵍ[A] M` and
  `DG.Shift.addEquiv m n : Shift m (Shift n M) ≃ᵈᵍ[A] Shift (m + n) M`.
* `DirectSum.Decomposition.reindex`: a decomposition reindexed along an equivalence of index
  types, used to grade the shift.

`Shift n M` is a `def`, not an `abbrev`: instances on `M` are not visible on `Shift n M`, and
the structures on `Shift n M` are declared explicitly.
-/

open DirectSum

namespace DirectSum.Decomposition

variable {ι κ M σ : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [SetLike σ M]
  [AddSubmonoidClass σ M] (ℳ : ι → σ) [Decomposition ℳ] (e : κ ≃ ι)

/-- A decomposition `M = ⨁ i, ℳ i` reindexed along an equivalence `e : κ ≃ ι` of index types:
`M = ⨁ k, ℳ (e k)`. -/
@[instance_reducible]
def reindex : Decomposition fun k => ℳ (e k) where
  decompose' m :=
    DirectSum.toAddMonoid (fun i => (DirectSum.of (fun k => ℳ (e k)) (e.symm i)).comp
      ({ toFun := fun x => ⟨x, by rw [e.apply_symm_apply]; exact x.2⟩
         map_zero' := rfl
         map_add' := fun _ _ => rfl } : ℳ i →+ ℳ (e (e.symm i)))) (decompose ℳ m)
  left_inv m := by
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | homogeneous x => simp
    | add m m' hm hm' => simp only [decompose_add, map_add, hm, hm']
  right_inv z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of k y =>
      dsimp only
      rw [coeAddMonoidHom_of, decompose_coe, toAddMonoid_of, AddMonoidHom.comp_apply]
      exact of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (e.symm_apply_apply k) rfl)
    | add z z' hz hz' =>
      dsimp only at hz hz' ⊢
      rw [map_add, decompose_add, map_add, hz, hz']

end DirectSum.Decomposition

namespace DG

universe u

/-- The shift `M⟦n⟧` of a dg module `M` by `n : ℤ`: the same abelian group with
`(M⟦n⟧)ᵏ = Mᵏ⁺ⁿ`, `d_{M⟦n⟧} = (-1)ⁿ d_M` and the action twisted by `(-1)^{n |a|}`. -/
def Shift (_n : ℤ) (M : Type u) : Type u := M

namespace Shift

section Twist

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] (n : ℤ)

/-- The additive map `a ↦ (-1)^{n |a|} a` on a dg ring, `a` homogeneous of degree `|a|`. -/
def twistAddHom : A →+ A :=
  (DirectSum.toAddMonoid fun i : ℤ =>
    (DistribSMul.toAddMonoidHom A (koszulSign (n * i))).comp (grading (M := A) i).subtype).comp
    (decomposeAddEquiv (grading (M := A))).toAddMonoidHom

variable {A} {n}

theorem twistAddHom_of_mem {i : ℤ} {a : A} (ha : a ∈ grading i) :
    twistAddHom A n a = koszulSign (n * i) • a := by
  simp only [twistAddHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    decomposeAddEquiv_apply, decompose_of_mem _ ha, toAddMonoid_of]
  rfl

variable (A) (n)

/-- The graded ring endomorphism `a ↦ (-1)^{n |a|} a` of a dg ring `A` (`a` homogeneous of
degree `|a|`). The shift `M⟦n⟧` of a dg `A`-module is `M` with the action restricted along
`twist A n`. It is graded of degree `0` but does not commute with `d` when `n` is odd. -/
def twist : A →+* A where
  __ := twistAddHom A n
  map_one' := by
    change twistAddHom A n 1 = 1
    rw [twistAddHom_of_mem one_mem_grading, mul_zero, koszulSign, Int.negOnePow_zero,
      one_smul]
  map_mul' a b := by
    change twistAddHom A n (a * b) = twistAddHom A n a * twistAddHom A n b
    induction a using induction_on with
    | h_zero => simp
    | h_homogeneous a =>
      rename_i i
      induction b using induction_on with
      | h_zero => simp
      | h_homogeneous b =>
        rename_i j
        rw [twistAddHom_of_mem a.2, twistAddHom_of_mem b.2,
          twistAddHom_of_mem (mul_mem_grading a.2 b.2), smul_mul_assoc, mul_smul_comm,
          smul_smul, ← koszulSign_add, mul_add]
      | h_add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
    | h_add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]

variable {A} {n}

theorem twist_of_mem {i : ℤ} {a : A} (ha : a ∈ grading i) :
    twist A n a = koszulSign (n * i) • a :=
  twistAddHom_of_mem ha

theorem twist_mem {i : ℤ} {a : A} (ha : a ∈ grading i) : twist A n a ∈ grading i := by
  rw [twist_of_mem ha, Units.smul_def]
  exact zsmul_mem ha _

@[simp]
theorem twist_zero (a : A) : twist A 0 a = a := by
  induction a using induction_on with
  | h_zero => simp
  | h_homogeneous a => rw [twist_of_mem a.2, zero_mul, koszulSign, Int.negOnePow_zero, one_smul]
  | h_add a a' ha ha' => rw [map_add, ha, ha']

theorem twist_twist (m : ℤ) (a : A) : twist A m (twist A n a) = twist A (m + n) a := by
  induction a using induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rw [twist_of_mem a.2, Units.smul_def, map_zsmul, ← Units.smul_def, twist_of_mem a.2,
      twist_of_mem a.2, smul_smul, ← koszulSign_add, add_mul, add_comm]
  | h_add a a' ha ha' => rw [map_add, map_add, ha, ha', map_add]

theorem twist_comp_twist (m : ℤ) : (twist A m).comp (twist A n) = twist A (m + n) :=
  RingHom.ext fun a => twist_twist m a

end Twist

variable (n : ℤ) {M : Type*}

section AddCommGroup

variable [AddCommGroup M]

instance : AddCommGroup (Shift n M) := inferInstanceAs (AddCommGroup M)

/-- The identity `M → M⟦n⟧`, as an additive equivalence. -/
def mk : M ≃+ Shift n M := AddEquiv.refl M

/-- The identity `M⟦n⟧ → M`, as an additive equivalence. -/
def unmk : Shift n M ≃+ M := AddEquiv.refl M

variable {n}

@[simp] theorem unmk_mk (m : M) : unmk n (mk n m) = m := rfl
@[simp] theorem mk_unmk (m : Shift n M) : mk n (unmk n m) = m := rfl
@[simp] theorem mk_symm : (mk n (M := M)).symm = unmk n := rfl
@[simp] theorem unmk_symm : (unmk n (M := M)).symm = mk n := rfl

theorem mk_injective : Function.Injective (mk n (M := M)) := (mk n).injective
theorem mk_surjective : Function.Surjective (mk n (M := M)) := (mk n).surjective

@[simp] theorem mk_inj {m m' : M} : mk n m = mk n m' ↔ m = m' := (mk n).injective.eq_iff
@[simp] theorem unmk_inj {m m' : Shift n M} : unmk n m = unmk n m' ↔ m = m' :=
  (unmk n).injective.eq_iff

@[simp] theorem mk_zero : mk n (0 : M) = 0 := rfl
@[simp] theorem unmk_zero : unmk n (0 : Shift n M) = 0 := rfl
theorem mk_add (m m' : M) : mk n (m + m') = mk n m + mk n m' := rfl
theorem unmk_add (m m' : Shift n M) : unmk n (m + m') = unmk n m + unmk n m' := rfl
theorem mk_neg (m : M) : mk n (-m) = -mk n m := rfl
theorem unmk_neg (m : Shift n M) : unmk n (-m) = -unmk n m := rfl
theorem mk_sub (m m' : M) : mk n (m - m') = mk n m - mk n m' := rfl
theorem unmk_sub (m m' : Shift n M) : unmk n (m - m') = unmk n m - unmk n m' := rfl
@[simp] theorem mk_zsmul (k : ℤ) (m : M) : mk n (k • m) = k • mk n m := rfl
@[simp] theorem unmk_zsmul (k : ℤ) (m : Shift n M) : unmk n (k • m) = k • unmk n m := rfl
@[simp] theorem mk_units_smul (u : ℤˣ) (m : M) : mk n (u • m) = u • mk n m := rfl
@[simp] theorem unmk_units_smul (u : ℤˣ) (m : Shift n M) : unmk n (u • m) = u • unmk n m := rfl

end AddCommGroup

section DGAddCommGroup

variable {n} [AddCommGroup M] [DGAddCommGroup M]

instance : DGAddCommGroup (Shift n M) where
  grading k := grading (M := M) (k + n)
  decomposition := Decomposition.reindex (grading (M := M)) (Equiv.addRight n)
  d := (DistribSMul.toAddMonoidHom M (koszulSign n)).comp (d : M →+ M)
  d_mem' {k m} hm := by
    have hm' : unmk n m ∈ grading (M := M) (k + n) := hm
    change koszulSign n • d (unmk n m) ∈ grading (M := M) (k + 1 + n)
    rw [add_right_comm, Units.smul_def]
    exact zsmul_mem (d_mem hm') _
  d_d' m := by
    change koszulSign n • d (koszulSign n • d (unmk n m)) = 0
    rw [d_units_smul, d_d, smul_zero, smul_zero]

theorem mem_grading_iff {k : ℤ} {m : M} : mk n m ∈ grading k ↔ m ∈ grading (k + n) := Iff.rfl

theorem mem_grading_iff' {k : ℤ} {m : Shift n M} :
    m ∈ grading k ↔ unmk n m ∈ grading (k + n) := Iff.rfl

theorem mk_mem_grading {k : ℤ} {m : M} (hm : m ∈ grading k) : mk n m ∈ grading (k - n) :=
  mem_grading_iff.mpr (by rwa [sub_add_cancel])

theorem unmk_mem_grading {k : ℤ} {m : Shift n M} (hm : m ∈ grading k) :
    unmk n m ∈ grading (k + n) :=
  mem_grading_iff'.mp hm

@[simp] theorem d_mk (m : M) : d (mk n m) = mk n (koszulSign n • d m) := rfl
@[simp] theorem unmk_d (m : Shift n M) : unmk n (d m) = koszulSign n • d (unmk n m) := rfl

end DGAddCommGroup

section Module

variable {n} {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [AddCommGroup M] [Module A M]

/-- The `A`-module structure of `M⟦n⟧`: the action of `M` restricted along `twist A n`, i.e.
`a • m = (-1)^{n |a|} (a • m)` for `a` homogeneous. -/
instance : Module A (Shift n M) := Module.compHom M (twist A n)

theorem smul_def (a : A) (m : Shift n M) : a • m = mk n (twist A n a • unmk n m) := rfl

theorem smul_mk_eq (a : A) (m : M) : a • mk n m = mk n (twist A n a • m) := rfl

theorem unmk_smul_eq (a : A) (m : Shift n M) : unmk n (a • m) = twist A n a • unmk n m := rfl

theorem smul_mk {i : ℤ} {a : A} (ha : a ∈ grading i) (m : M) :
    a • mk n m = mk n (koszulSign (n * i) • (a • m)) := by
  rw [smul_mk_eq, twist_of_mem ha, smul_assoc]

theorem unmk_smul {i : ℤ} {a : A} (ha : a ∈ grading i) (m : Shift n M) :
    unmk n (a • m) = koszulSign (n * i) • (a • unmk n m) := by
  rw [unmk_smul_eq, twist_of_mem ha, smul_assoc]

theorem mk_smul {i : ℤ} {a : A} (ha : a ∈ grading i) (m : M) :
    mk n (a • m) = koszulSign (n * i) • (a • mk n m) := by
  rw [smul_mk ha, mk_units_smul, smul_smul, ← koszulSign_add, ← two_mul,
    koszulSign_even (even_two_mul _), one_smul]

end Module

section DGModule

variable {n} {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [DGModule A M]

instance : DGModule A (Shift n M) where
  smul_mem {i j} a m ha hm := by
    obtain ⟨m, rfl⟩ := mk_surjective m
    rw [mem_grading_iff] at hm
    rw [smul_mk ha, mem_grading_iff, vadd_eq_add, add_assoc, Units.smul_def]
    exact zsmul_mem (smul_mem_grading ha hm) _
  d_smul' {i} a ha m := by
    obtain ⟨m, rfl⟩ := mk_surjective m
    rw [smul_mk ha, d_mk, d_units_smul, d_smul ha, smul_mk (d_mem ha), d_mk, smul_mk ha,
      ← mk_units_smul, ← mk_add, mk_inj, smul_comm a (koszulSign n), smul_add]
    simp only [smul_smul, ← koszulSign_add]
    have h1 : koszulSign n * koszulSign (n * i) = koszulSign (n * (i + 1)) := by
      rw [← koszulSign_add]; congr 1; ring
    have h2 : koszulSign n * koszulSign (n * i + i) = koszulSign (i + (n * i + n)) := by
      rw [← koszulSign_add]; congr 1; ring
    rw [smul_add, smul_smul, smul_smul, h1, h2]

end DGModule

end Shift

namespace DGModuleHom

variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

open Shift

/-- The shift of a morphism of dg modules: the same function `M⟦n⟧ → N⟦n⟧`. -/
def shift (n : ℤ) (f : M →ᵈᵍ[A] N) : Shift n M →ᵈᵍ[A] Shift n N where
  toFun m := Shift.mk n (f (unmk n m))
  map_add' m m' := by simp [map_add]
  map_smul' a m := by
    change Shift.mk n (f (unmk n (a • m))) = a • Shift.mk n (f (unmk n m))
    rw [unmk_smul_eq, map_smul, smul_mk_eq]
  map_mem' hm := f.map_mem hm
  map_d' m := by
    rw [unmk_d, Units.smul_def, map_zsmul, ← Units.smul_def, map_d, d_mk]

@[simp]
theorem shift_apply (n : ℤ) (f : M →ᵈᵍ[A] N) (m : M) :
    f.shift n (Shift.mk n m) = Shift.mk n (f m) := rfl

theorem unmk_shift_apply (n : ℤ) (f : M →ᵈᵍ[A] N) (m : Shift n M) :
    unmk n (f.shift n m) = f (unmk n m) := rfl

@[simp]
theorem shift_id (n : ℤ) : (DGModuleHom.id : M →ᵈᵍ[A] M).shift n = DGModuleHom.id := rfl

@[simp]
theorem shift_comp (n : ℤ) (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) :
    (g.comp f).shift n = (g.shift n).comp (f.shift n) := rfl

@[simp] theorem shift_zero (n : ℤ) : (0 : M →ᵈᵍ[A] N).shift n = 0 := rfl
@[simp] theorem shift_add (n : ℤ) (f g : M →ᵈᵍ[A] N) :
    (f + g).shift n = f.shift n + g.shift n := rfl
@[simp] theorem shift_neg (n : ℤ) (f : M →ᵈᵍ[A] N) : (-f).shift n = -f.shift n := rfl
@[simp] theorem shift_sub (n : ℤ) (f g : M →ᵈᵍ[A] N) :
    (f - g).shift n = f.shift n - g.shift n := rfl

/-- The shift of morphisms as an additive map. -/
def shiftAddMonoidHom (n : ℤ) : (M →ᵈᵍ[A] N) →+ (Shift n M →ᵈᵍ[A] Shift n N) where
  toFun := shift n
  map_zero' := rfl
  map_add' _ _ := rfl

end DGModuleHom

namespace Shift

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]

/-- The shift by `0` is the identity: `M⟦0⟧ ≃ M`. -/
def zeroEquiv : Shift 0 M ≃ᵈᵍ[A] M where
  toFun := unmk 0
  invFun := mk 0
  left_inv := mk_unmk
  right_inv := unmk_mk
  map_add' := map_add (unmk 0)
  map_smul' a m := by rw [unmk_smul_eq, twist_zero]; rfl
  map_mem' {k m} hm := by rw [mem_grading_iff', add_zero] at hm; exact hm
  map_d' m := by rw [unmk_d, koszulSign, Int.negOnePow_zero, one_smul]

@[simp] theorem zeroEquiv_apply (m : Shift 0 M) : zeroEquiv (A := A) m = unmk 0 m := rfl
@[simp] theorem zeroEquiv_symm_apply (m : M) : (zeroEquiv (A := A)).symm m = mk 0 m := rfl

/-- Shifts compose: `(M⟦n⟧)⟦m⟧ ≃ M⟦m + n⟧`. On underlying elements this is the identity; the
signs `(-1)^{m |a|} (-1)^{n |a|} = (-1)^{(m + n) |a|}` and `(-1)^m (-1)^n = (-1)^{m + n}` make it
`A`-linear and compatible with the differentials. -/
def addEquiv (m n : ℤ) : Shift m (Shift n M) ≃ᵈᵍ[A] Shift (m + n) M where
  toFun x := mk (m + n) (unmk n (unmk m x))
  invFun y := mk m (mk n (unmk (m + n) y))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change mk (m + n) (unmk n (unmk m (a • x))) = a • mk (m + n) (unmk n (unmk m x))
    rw [unmk_smul_eq, unmk_smul_eq, twist_twist, add_comm n m, smul_mk_eq]
  map_mem' {k x} hx := by
    rw [mem_grading_iff', mem_grading_iff'] at hx
    rw [mem_grading_iff, ← add_assoc]
    exact hx
  map_d' x := by
    rw [unmk_d, unmk_units_smul, unmk_d, d_mk, smul_smul, ← koszulSign_add]

@[simp] theorem addEquiv_apply (m n : ℤ) (x : Shift m (Shift n M)) :
    addEquiv (A := A) m n x = mk (m + n) (unmk n (unmk m x)) := rfl

@[simp] theorem addEquiv_symm_apply (m n : ℤ) (y : Shift (m + n) M) :
    (addEquiv (A := A) m n).symm y = mk m (mk n (unmk (m + n) y)) := rfl

end Shift

end DG
