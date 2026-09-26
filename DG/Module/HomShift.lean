import DG.Module.Hom
import DG.Module.Shift

/-!
# Shifting cochains of the Hom complex

Let `A` be a dg ring and `M`, `N` dg `A`-modules. This file studies how the cochains
`DG.Cochain A M N n` of the Hom complex behave with respect to the shifts `DG.Shift a M` and
`DG.Shift a N`. It is a port of Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/
HomComplexShift.lean`, with the same names and the same signs.

## Main definitions

For integers `n`, `a`, `n'`:

* `DG.Cochain.rightShift z a n' h : Cochain A M (Shift a N) n'` for `z : Cochain A M N n` and
  `h : n' + a = n`: the map `x ↦ z x`, without sign; its inverse is `DG.Cochain.rightUnshift`.
* `DG.Cochain.leftShift z a n' h : Cochain A (Shift a M) N n'` for `z : Cochain A M N n` and
  `h : n + a = n'`: the map `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x`; its inverse is
  `DG.Cochain.leftUnshift`.
* `DG.Cochain.shift z a : Cochain A (Shift a M) (Shift a N) n`: the map `x ↦ z x`, without sign.
* The corresponding additive equivalences `DG.Cochain.rightShiftAddEquiv`,
  `DG.Cochain.leftShiftAddEquiv`, the additive map `DG.Cochain.shiftAddHom`, and the versions for
  cocycles `DG.Cocycle.rightShift`, `DG.Cocycle.leftShift`, `DG.Cocycle.shift`, ...

## Main results

* `DG.Cochain.δ_rightShift`, `DG.Cochain.δ_leftShift`, `DG.Cochain.δ_shift`: the differential
  commutes with the shifts up to the sign `(-1)^a`.
* `DG.Cochain.leftShift_comp`, `DG.Cochain.rightUnshift_comp`, `DG.Cochain.rightShift_comp`,
  `DG.Cochain.shift_comp`: compatibility with composition.
* `DG.Cochain.leftShift_rightShift_eq_negOnePow_rightShift_leftShift`: the left and right
  shifts commute up to the sign `(-1)^a`.

## Signs

The signs are exactly those of Mathlib, which follow the conventions of the introduction of
B. Conrad, *Grothendieck duality and base change*. With the action on `Shift a M` twisted by
`(-1)^{a |b|}` (see `DG.Shift`), all these maps are `A`-linear with the Koszul sign, i.e. they are
cochains: for `rightShift` and `shift` the twist is exactly compensated by the change of degree,
and for `leftShift` the twist `(-1)^{a |b|}` and the Koszul sign `(-1)^{n |b|}` of `z` combine to
the Koszul sign `(-1)^{n' |b|}` of a cochain of degree `n' = n + a`, whatever constant sign is
put in front. In particular no deviation from Mathlib's signs is needed.

Since cochains are functions here, Mathlib's lemmas `rightShift_v`, `leftShift_v`, ... on
components become the evaluation lemmas `rightShift_apply`, `leftShift_apply`, ....
Composition is written in the usual order (see `DG.Cochain.comp`): Mathlib's `γ.comp γ' h`
is `γ'.comp γ h` here.
-/

namespace DG

namespace Cochain

open Shift

variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

/-- Two Koszul signs agree when the degrees differ by an even integer. -/
theorem _root_.DG.koszulSign_eq_of_sub_eq_two_mul {m n : ℤ} (k : ℤ) (h : m - n = 2 * k) :
    koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).2 ⟨k, by omega⟩

/-- The sign `(-1)^{a n' + a (a - 1) / 2}` appearing in `Cochain.leftShift`. -/
abbrev leftShiftSign (a n' : ℤ) : ℤˣ := koszulSign (a * n' + a * (a - 1) / 2)

section Defs

variable {n : ℤ} (z : Cochain A M N n)

/-- The cochain `Cochain A M (Shift a N) n'` attached to `z : Cochain A M N n` when
`n' + a = n`: the same underlying map, without sign (Mathlib's `Cochain.rightShift`). -/
def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain A M (Shift a N) n' where
  toFun x := Shift.mk a (z x)
  map_zero' := by simp
  map_add' x y := by rw [map_add, mk_add]
  map_mem' i x hx := by
    rw [mem_grading_iff, add_assoc, hn']
    exact z.map_mem hx
  map_smul' {i b} hb x := by
    rw [z.map_smul hb, smul_mk hb, ← mk_units_smul, smul_smul, ← koszulSign_add, ← add_mul, hn']

@[simp]
theorem rightShift_apply (a n' : ℤ) (hn' : n' + a = n) (x : M) :
    z.rightShift a n' hn' x = Shift.mk a (z x) := rfl

theorem unmk_rightShift_apply (a n' : ℤ) (hn' : n' + a = n) (x : M) :
    unmk a (z.rightShift a n' hn' x) = z x := rfl

/-- The cochain `Cochain A (Shift a M) N n'` attached to `z : Cochain A M N n` when
`n + a = n'`: the map `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x` (Mathlib's
`Cochain.leftShift`, with the same sign). -/
def leftShift (a n' : ℤ) (hn' : n + a = n') : Cochain A (Shift a M) N n' where
  toFun x := leftShiftSign a n' • z (unmk a x)
  map_zero' := by simp
  map_add' x y := by rw [unmk_add, map_add, smul_add]
  map_mem' i x hx := by
    refine units_smul_mem_grading _ ?_
    rw [← hn', add_comm n a, ← add_assoc]
    exact z.map_mem (unmk_mem_grading hx)
  map_smul' {i b} hb x := by
    rw [unmk_smul hb, map_units_smul, z.map_smul hb, smul_comm b (leftShiftSign a n'),
      smul_smul, smul_smul, smul_smul, ← hn']
    congr 1
    simp only [← koszulSign_add]
    congr 1
    ring

theorem leftShift_apply (a n' : ℤ) (hn' : n + a = n') (x : Shift a M) :
    z.leftShift a n' hn' x = leftShiftSign a n' • z (unmk a x) := rfl

@[simp]
theorem leftShift_apply_mk (a n' : ℤ) (hn' : n + a = n') (x : M) :
    z.leftShift a n' hn' (Shift.mk a x) = leftShiftSign a n' • z x := rfl

/-- The cochain `Cochain A (Shift a M) (Shift a N) n` attached to `z : Cochain A M N n`: the
same underlying map, without sign (Mathlib's `Cochain.shift`). -/
def shift (a : ℤ) : Cochain A (Shift a M) (Shift a N) n where
  toFun x := Shift.mk a (z (unmk a x))
  map_zero' := by simp
  map_add' x y := by rw [unmk_add, map_add, mk_add]
  map_mem' i x hx := by
    rw [mem_grading_iff, add_right_comm]
    exact z.map_mem (unmk_mem_grading hx)
  map_smul' {i b} hb x := by
    rw [unmk_smul hb, map_units_smul, z.map_smul hb, smul_mk hb, ← mk_units_smul, smul_smul,
      smul_smul, mul_comm]

theorem shift_apply (a : ℤ) (x : Shift a M) :
    z.shift a x = Shift.mk a (z (unmk a x)) := rfl

@[simp]
theorem shift_apply_mk (a : ℤ) (x : M) : z.shift a (Shift.mk a x) = Shift.mk a (z x) := rfl

end Defs

/-- The cochain `Cochain A M N n` attached to `z : Cochain A M (Shift a N) n'` when
`n' + a = n`: the inverse of `Cochain.rightShift` (Mathlib's `Cochain.rightUnshift`). -/
def rightUnshift {n' a : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ) (hn : n' + a = n) :
    Cochain A M N n where
  toFun x := unmk a (z x)
  map_zero' := by simp
  map_add' x y := by rw [map_add, unmk_add]
  map_mem' i x hx := by
    rw [← hn, ← add_assoc]
    exact unmk_mem_grading (z.map_mem hx)
  map_smul' {i b} hb x := by
    rw [z.map_smul hb, unmk_units_smul, unmk_smul hb, smul_smul, ← koszulSign_add, ← add_mul, hn]

@[simp]
theorem rightUnshift_apply {n' a : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ)
    (hn : n' + a = n) (x : M) : z.rightUnshift n hn x = unmk a (z x) := rfl

/-- The cochain `Cochain A M N n` attached to `z : Cochain A (Shift a M) N n'` when
`n + a = n'`: the inverse of `Cochain.leftShift`, `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x`
(Mathlib's `Cochain.leftUnshift`). -/
def leftUnshift {n' a : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ) (hn : n + a = n') :
    Cochain A M N n where
  toFun x := leftShiftSign a n' • z (Shift.mk a x)
  map_zero' := by simp
  map_add' x y := by rw [mk_add, map_add, smul_add]
  map_mem' i x hx := by
    refine units_smul_mem_grading _ ?_
    convert z.map_mem (mk_mem_grading (n := a) hx) using 2
    omega
  map_smul' {i b} hb x := by
    subst hn
    rw [mk_smul hb, map_units_smul, z.map_smul hb, smul_comm b (leftShiftSign a _),
      smul_smul, smul_smul, smul_smul]
    congr 1
    simp only [leftShiftSign, ← koszulSign_add]
    exact koszulSign_eq_of_sub_eq_two_mul (a * i) (by ring)

@[simp]
theorem leftUnshift_apply {n' a : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ)
    (hn : n + a = n') (x : M) : z.leftUnshift n hn x = leftShiftSign a n' • z (Shift.mk a x) :=
  rfl

section Lemmas

variable {n : ℤ} (z z₁ z₂ : Cochain A M N n)

@[simp]
theorem rightUnshift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (z.rightShift a n' hn').rightUnshift n hn' = z := rfl

@[simp]
theorem rightShift_rightUnshift {a n' : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ)
    (hn' : n' + a = n) : (z.rightUnshift n hn').rightShift a n' hn' = z := rfl

@[simp]
theorem leftUnshift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (z.leftShift a n' hn').leftUnshift n hn' = z := by
  ext x
  simp [leftShift_apply, smul_smul]

@[simp]
theorem leftShift_leftUnshift {a n' : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ)
    (hn' : n + a = n') : (z.leftUnshift n hn').leftShift a n' hn' = z := by
  ext x
  simp [leftShift_apply, smul_smul]

@[simp]
theorem rightShift_add (a n' : ℤ) (hn' : n' + a = n) :
    (z₁ + z₂).rightShift a n' hn' = z₁.rightShift a n' hn' + z₂.rightShift a n' hn' := rfl

@[simp]
theorem leftShift_add (a n' : ℤ) (hn' : n + a = n') :
    (z₁ + z₂).leftShift a n' hn' = z₁.leftShift a n' hn' + z₂.leftShift a n' hn' := by
  ext x
  simp [leftShift_apply, smul_add]

@[simp]
theorem shift_add (a : ℤ) : (z₁ + z₂).shift a = z₁.shift a + z₂.shift a := rfl

variable (A M N) in
/-- The additive equivalence `Cochain A M N n ≃+ Cochain A M (Shift a N) n'` when
`n' + a = n`. -/
@[simps]
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain A M N n ≃+ Cochain A M (Shift a N) n' where
  toFun z := z.rightShift a n' hn'
  invFun z := z.rightUnshift n hn'
  left_inv z := rightUnshift_rightShift z a n' hn'
  right_inv z := rightShift_rightUnshift z n hn'
  map_add' z₁ z₂ := rightShift_add z₁ z₂ a n' hn'

variable (A M N) in
/-- The additive equivalence `Cochain A M N n ≃+ Cochain A (Shift a M) N n'` when
`n + a = n'`. -/
@[simps]
def leftShiftAddEquiv (n a n' : ℤ) (hn' : n + a = n') :
    Cochain A M N n ≃+ Cochain A (Shift a M) N n' where
  toFun z := z.leftShift a n' hn'
  invFun z := z.leftUnshift n hn'
  left_inv z := leftUnshift_leftShift z a n' hn'
  right_inv z := leftShift_leftUnshift z n hn'
  map_add' z₁ z₂ := leftShift_add z₁ z₂ a n' hn'

variable (A M N) in
/-- The additive map `Cochain A M N n →+ Cochain A (Shift a M) (Shift a N) n`. -/
@[simps]
def shiftAddHom (n a : ℤ) : Cochain A M N n →+ Cochain A (Shift a M) (Shift a N) n where
  toFun z := z.shift a
  map_zero' := rfl
  map_add' z₁ z₂ := shift_add z₁ z₂ a

variable (A M N n)

@[simp]
theorem rightShift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain A M N n).rightShift a n' hn' = 0 := rfl

@[simp]
theorem rightUnshift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain A M (Shift a N) n').rightUnshift n hn' = 0 := rfl

@[simp]
theorem leftShift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain A M N n).leftShift a n' hn' = 0 :=
  map_zero (leftShiftAddEquiv A M N n a n' hn')

@[simp]
theorem leftUnshift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain A (Shift a M) N n').leftUnshift n hn' = 0 :=
  map_zero (leftShiftAddEquiv A M N n a n' hn').symm

@[simp]
theorem shift_zero (a : ℤ) : (0 : Cochain A M N n).shift a = 0 := rfl

variable {A M N n}

@[simp]
theorem rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
    (-z).rightShift a n' hn' = -z.rightShift a n' hn' := rfl

@[simp]
theorem rightShift_sub (a n' : ℤ) (hn' : n' + a = n) :
    (z₁ - z₂).rightShift a n' hn' = z₁.rightShift a n' hn' - z₂.rightShift a n' hn' := rfl

@[simp]
theorem rightUnshift_neg {n' a : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ) (hn : n' + a = n) :
    (-z).rightUnshift n hn = -z.rightUnshift n hn := rfl

@[simp]
theorem rightUnshift_add {n' a : ℤ} (z₁ z₂ : Cochain A M (Shift a N) n') (n : ℤ)
    (hn : n' + a = n) :
    (z₁ + z₂).rightUnshift n hn = z₁.rightUnshift n hn + z₂.rightUnshift n hn := rfl

@[simp]
theorem leftShift_neg (a n' : ℤ) (hn' : n + a = n') :
    (-z).leftShift a n' hn' = -z.leftShift a n' hn' :=
  map_neg (leftShiftAddEquiv A M N n a n' hn') z

@[simp]
theorem leftShift_sub (a n' : ℤ) (hn' : n + a = n') :
    (z₁ - z₂).leftShift a n' hn' = z₁.leftShift a n' hn' - z₂.leftShift a n' hn' :=
  map_sub (leftShiftAddEquiv A M N n a n' hn') z₁ z₂

@[simp]
theorem leftUnshift_neg {n' a : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ) (hn : n + a = n') :
    (-z).leftUnshift n hn = -z.leftUnshift n hn :=
  map_neg (leftShiftAddEquiv A M N n a n' hn).symm z

@[simp]
theorem leftUnshift_add {n' a : ℤ} (z₁ z₂ : Cochain A (Shift a M) N n') (n : ℤ)
    (hn : n + a = n') :
    (z₁ + z₂).leftUnshift n hn = z₁.leftUnshift n hn + z₂.leftUnshift n hn :=
  map_add (leftShiftAddEquiv A M N n a n' hn).symm z₁ z₂

@[simp]
theorem shift_neg (a : ℤ) : (-z).shift a = -z.shift a := rfl

@[simp]
theorem shift_sub (a : ℤ) : (z₁ - z₂).shift a = z₁.shift a - z₂.shift a := rfl

@[simp]
theorem rightShift_zsmul (a n' : ℤ) (hn' : n' + a = n) (k : ℤ) :
    (k • z).rightShift a n' hn' = k • z.rightShift a n' hn' := rfl

@[simp]
theorem rightShift_units_smul (a n' : ℤ) (hn' : n' + a = n) (u : ℤˣ) :
    (u • z).rightShift a n' hn' = u • z.rightShift a n' hn' := rfl

@[simp]
theorem rightUnshift_units_smul {n' a : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ)
    (hn : n' + a = n) (u : ℤˣ) : (u • z).rightUnshift n hn = u • z.rightUnshift n hn := rfl

@[simp]
theorem leftShift_zsmul (a n' : ℤ) (hn' : n + a = n') (k : ℤ) :
    (k • z).leftShift a n' hn' = k • z.leftShift a n' hn' :=
  map_zsmul (leftShiftAddEquiv A M N n a n' hn') k z

@[simp]
theorem leftShift_units_smul (a n' : ℤ) (hn' : n + a = n') (u : ℤˣ) :
    (u • z).leftShift a n' hn' = u • z.leftShift a n' hn' := by
  rw [Units.smul_def, Units.smul_def, leftShift_zsmul]

@[simp]
theorem leftUnshift_units_smul {n' a : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ)
    (hn : n + a = n') (u : ℤˣ) : (u • z).leftUnshift n hn = u • z.leftUnshift n hn := by
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul (leftShiftAddEquiv A M N n a n' hn).symm _ z

@[simp]
theorem shift_zsmul (a k : ℤ) : (k • z).shift a = k • z.shift a := rfl

@[simp]
theorem shift_units_smul (a : ℤ) (u : ℤˣ) : (u • z).shift a = u • z.shift a := rfl

@[simp]
theorem shift_id (a : ℤ) : (Cochain.id A M).shift a = Cochain.id A (Shift a M) := rfl

@[simp]
theorem shift_ofHom (φ : M →ᵈᵍ[A] N) (a : ℤ) : (ofHom φ).shift a = ofHom (φ.shift a) := rfl

/-! ### Composition -/

/-- The right shift of a composition (Mathlib's `Cochain.rightUnshift_comp`, written with the
composition in the usual order). -/
theorem rightUnshift_comp {m a : ℤ} (z' : Cochain A N (Shift a P) m) {nm : ℤ}
    (hnm : n + m = nm) (nm' : ℤ) (hnm' : nm + a = nm') (m' : ℤ) (hm' : m + a = m') :
    (z'.comp z hnm).rightUnshift nm' hnm' =
      (z'.rightUnshift m' hm').comp z (by rw [← hm', ← add_assoc, hnm, hnm']) := rfl

/-- The right shift of a composition is the composition with the right shift. -/
theorem rightShift_comp {m : ℤ} (z' : Cochain A N P m) {nm : ℤ} (hnm : n + m = nm)
    (a nm' : ℤ) (hnm' : nm' + a = nm) (m' : ℤ) (hm' : m' + a = m) :
    (z'.comp z hnm).rightShift a nm' hnm' =
      (z'.rightShift a m' hm').comp z (by
        rw [← add_left_inj a, add_assoc, hm', hnm, hnm']) := rfl

/-- The left shift of a composition (Mathlib's `Cochain.leftShift_comp`): for `z` of degree
`n` and `z'` of degree `m`, `(z' ∘ z).leftShift a = (-1)^{a m} • z' ∘ z.leftShift a`. -/
theorem leftShift_comp (a n' : ℤ) (hn' : n + a = n') {m t t' : ℤ} (z' : Cochain A N P m)
    (h : n + m = t) (ht' : t + a = t') :
    (z'.comp z h).leftShift a t' ht' = koszulSign (a * m) • z'.comp (z.leftShift a n' hn')
      (by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]) := by
  ext x
  simp only [leftShift_apply, comp_apply, units_smul_apply, map_units_smul, smul_smul]
  congr 1
  simp only [leftShiftSign, ← koszulSign_add]
  congr 1
  rw [← ht', ← h, ← hn']
  ring

@[simp]
theorem leftShift_comp_zero_cochain (a n' : ℤ) (hn' : n + a = n') (z' : Cochain A N P 0) :
    (z'.comp z (add_zero n)).leftShift a n' hn' =
      z'.comp (z.leftShift a n' hn') (add_zero n') := by
  rw [leftShift_comp z a n' hn' z' (add_zero _) hn', mul_zero, koszulSign, Int.negOnePow_zero,
    one_smul]

/-- The shift of a composition is the composition of the shifts. -/
@[simp]
theorem shift_comp (a : ℤ) {m nm : ℤ} (z' : Cochain A N P m) (h : n + m = nm) :
    (z'.comp z h).shift a = (z'.shift a).comp (z.shift a) h := rfl

end Lemmas

/-! ### The differential -/

section Differential

variable [DGModule A M] [DGModule A N]

variable {n : ℤ} (z : Cochain A M N n)

theorem δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (z.rightShift a n' hn') = koszulSign a • (δ n m z).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    ext x
    apply (unmk a).injective
    simp only [δ_apply _ _ hnm', δ_apply _ _ hnm, rightShift_apply, units_smul_apply, unmk_sub,
      unmk_d, unmk_units_smul, unmk_mk, smul_sub, smul_smul, ← koszulSign_add]
    congr 2
    rw [Int.negOnePow_eq_iff]
    exact ⟨-a, by omega⟩
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by omega)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, rightShift_zero, smul_zero]

theorem δ_rightUnshift {a n' : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ) (hn : n' + a = n)
    (m m' : ℤ) (hm' : m' + a = m) :
    δ n m (z.rightUnshift n hn) = koszulSign a • (δ n' m' z).rightUnshift m hm' := by
  obtain ⟨z, rfl⟩ := (rightShiftAddEquiv A M N n a n' hn).surjective z
  simp only [rightShiftAddEquiv_apply, rightUnshift_rightShift, z.δ_rightShift a n' m' hn m hm',
    rightUnshift_units_smul, smul_smul, Int.units_mul_self, one_smul]

theorem δ_leftShift (a n' m' : ℤ) (hn' : n + a = n') (m : ℤ) (hm' : m + a = m') :
    δ n' m' (z.leftShift a n' hn') = koszulSign a • (δ n m z).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    ext x
    simp only [δ_apply _ _ hnm', δ_apply _ _ hnm, leftShift_apply, units_smul_apply, unmk_d,
      d_units_smul, map_units_smul, smul_sub, smul_smul, leftShiftSign, ← koszulSign_add]
    congr 2
    all_goals rw [← hnm', ← hn']
    · exact koszulSign_eq_of_sub_eq_two_mul (-a) (by ring)
    · congr 1
      ring
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by omega)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, leftShift_zero, smul_zero]

theorem δ_leftUnshift {a n' : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ) (hn : n + a = n')
    (m m' : ℤ) (hm' : m + a = m') :
    δ n m (z.leftUnshift n hn) = koszulSign a • (δ n' m' z).leftUnshift m hm' := by
  obtain ⟨z, rfl⟩ := (leftShiftAddEquiv A M N n a n' hn).surjective z
  simp only [leftShiftAddEquiv_apply, leftUnshift_leftShift, z.δ_leftShift a n' m' hn m hm',
    leftUnshift_units_smul, smul_smul, Int.units_mul_self, one_smul]

@[simp]
theorem δ_shift (a m : ℤ) : δ n m (z.shift a) = koszulSign a • (δ n m z).shift a := by
  by_cases hnm : n + 1 = m
  · ext x
    apply (unmk a).injective
    simp only [δ_apply _ _ hnm, shift_apply, units_smul_apply, unmk_sub, unmk_d,
      unmk_units_smul, unmk_mk, d_units_smul, map_units_smul, smul_sub, smul_smul]
    rw [mul_comm]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, shift_zero, smul_zero]

end Differential

/-! ### Left and right shifts -/

section LeftRight

variable {n : ℤ} (z : Cochain A M N n)

theorem leftShift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (z.rightShift a n' hn').leftShift a n hn' =
      koszulSign (a * n + (a * (a - 1)) / 2) • z.shift a := rfl

theorem rightShift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (z.leftShift a n' hn').rightShift a n hn' =
      koszulSign (a * n' + (a * (a - 1)) / 2) • z.shift a := rfl

/-- The left and right shifts of cochains commute only up to the sign `(-1)^a`. -/
theorem leftShift_rightShift_eq_negOnePow_rightShift_leftShift
    (a n' n'' : ℤ) (hn' : n' + a = n) (hn'' : n + a = n'') :
    (z.rightShift a n' hn').leftShift a n hn' =
      koszulSign a • (z.leftShift a n'' hn'').rightShift a n hn'' := by
  rw [leftShift_rightShift, rightShift_leftShift, smul_smul, ← hn'', ← koszulSign_add,
    show a + (a * (n + a) + a * (a - 1) / 2) = a * n + a * (a - 1) / 2 + (a * a + a) by ring,
    koszulSign_add _ (a * a + a)]
  have h : koszulSign (a * a + a) = 1 := by
    rw [koszulSign_add, koszulSign, Int.negOnePow_mul_self, Int.units_mul_self]
  rw [h, mul_one]

end LeftRight

end Cochain

namespace Cocycle

open Cochain

variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  {n : ℤ}

/-- The cocycle `Cocycle A M (Shift a N) n'` attached to `z : Cocycle A M N n` when
`n' + a = n`. -/
@[simps!]
def rightShift (z : Cocycle A M N n) (a n' : ℤ) (hn' : n' + a = n) :
    Cocycle A M (Shift a N) n' :=
  Cocycle.mk ((z : Cochain A M N n).rightShift a n' hn') _ rfl (by
    simp only [δ_rightShift _ a n' (n' + 1) hn' (n + 1) (by omega), δ_eq_zero, rightShift_zero,
      smul_zero])

/-- The cocycle `Cocycle A M N n` attached to `z : Cocycle A M (Shift a N) n'` when
`n' + a = n`. -/
@[simps!]
def rightUnshift {n' a : ℤ} (z : Cocycle A M (Shift a N) n') (n : ℤ) (hn : n' + a = n) :
    Cocycle A M N n :=
  Cocycle.mk ((z : Cochain A M (Shift a N) n').rightUnshift n hn) _ rfl (by
    rw [δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by omega), δ_eq_zero, rightUnshift_zero,
      smul_zero])

/-- The cocycle `Cocycle A (Shift a M) N n'` attached to `z : Cocycle A M N n` when
`n + a = n'`. -/
@[simps!]
def leftShift (z : Cocycle A M N n) (a n' : ℤ) (hn' : n + a = n') :
    Cocycle A (Shift a M) N n' :=
  Cocycle.mk ((z : Cochain A M N n).leftShift a n' hn') _ rfl (by
    simp only [δ_leftShift _ a n' (n' + 1) hn' (n + 1) (by omega), δ_eq_zero, leftShift_zero,
      smul_zero])

/-- The cocycle `Cocycle A M N n` attached to `z : Cocycle A (Shift a M) N n'` when
`n + a = n'`. -/
@[simps!]
def leftUnshift {n' a : ℤ} (z : Cocycle A (Shift a M) N n') (n : ℤ) (hn : n + a = n') :
    Cocycle A M N n :=
  Cocycle.mk ((z : Cochain A (Shift a M) N n').leftUnshift n hn) _ rfl (by
    rw [δ_leftUnshift _ n hn (n + 1) (n + 1 + a) rfl, δ_eq_zero, leftUnshift_zero, smul_zero])

/-- The cocycle `Cocycle A (Shift a M) (Shift a N) n` attached to `z : Cocycle A M N n`. -/
@[simps!]
def shift (z : Cocycle A M N n) (a : ℤ) : Cocycle A (Shift a M) (Shift a N) n :=
  Cocycle.mk ((z : Cochain A M N n).shift a) _ rfl
    (by simp only [δ_shift, δ_eq_zero, shift_zero, smul_zero])

end Cocycle

end DG
