import DG.Graded.Basic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
# Regrading of graded objects

This file provides the regrading constructions of `docs/CONVENTIONS.md` for graded abelian
groups, rings and modules; the differentials are added in `DG.Algebra.Regrading`. A
`ℤ/2`-grading is turned into a 2-periodic `ℤ`-grading and back, and a `ℤ`-grading is split into
`k` residue classes regraded by division by `k`.

## `ℤ/2`-gradings and 2-periodic `ℤ`-gradings

* `DG.Periodize ℳ := ⨁ n : ℤ, ℳ (n mod 2)` for a `ℤ/2`-graded object `ℳ : ZMod 2 → σ`, with its
  `ℤ`-grading `DG.periodizeGrading ℳ` by the summands. The carrier changes: `Mⁿ` and `Mⁿ⁺²` are
  different summands, both copies of `M^{n mod 2}`. `DG.Periodize.mk ℳ n m hm` is `m` placed in
  degree `n`, and `DG.Periodize.fold` sums the components.
* `DG.Periodize.shiftTwo ℳ`: the additive automorphism of degree `2`, `σ₂ (Mⁿ) = Mⁿ⁺²`.
* For a `ℤ/2`-graded ring `𝒜`, `Periodize 𝒜` is a `ℤ`-graded ring through `DirectSum.GRing`
  (`Aⁱ × Aʲ → A^{i + j}` is the product of `A`), with the central unit
  `DG.Periodize.periodUnit 𝒜`, `1` placed in degree `2`. For a `ℤ/2`-graded `𝒜`-module `ℳ`,
  `Periodize ℳ` is a `ℤ`-graded `Periodize 𝒜`-module on which the periodicity unit acts by
  `shiftTwo` (`DG.Periodize.periodUnit_smul`).
* `DG.PeriodicityUnit 𝒜`: a central unit `u` of degree `2` of a `ℤ`-graded ring `A`. The quotient
  `A ⧸ (u - 1)` (`DG.PeriodicityUnit.Quotient`) is `ℤ/2`-graded by the images of `A⁰` and `A¹`,
  equivalently of all `Aⁿ` with `n` of the given parity (`DG.PeriodicityUnit.quotientGrading`,
  a `GradedRing`). The proofs use the collapse maps `DG.PeriodicityUnit.collapse n : A → Aⁿ`,
  `a ↦ u^((n - k) / 2) * a` on `Aᵏ` for `k ≡ n (mod 2)`, which vanish on `(u - 1)`.
* The two constructions are inverse to each other, as graded rings:
  `DG.Periodize.quotientEquiv 𝒜 : Periodize 𝒜 ⧸ (u - 1) ≃+* A` (`quotientEquiv_mem_iff`) and
  `DG.PeriodicityUnit.periodizeEquiv P : A ≃+* Periodize (A ⧸ (u - 1))`
  (`periodizeEquiv_mem_iff`, `periodizeEquiv_periodUnit`).

The equivalence of the categories of graded modules is
`DG.GradedModuleCat.periodizeEquivalence` in `DG.Graded.RegradingModuleCat`.

## Division of the grading

* `DG.RegradeByDivision ℳ k r := ⨁ q : ℤ, ℳ (q * k + r)`, graded by `q` (`DG.regradeGrading`).
* `DG.residueEquiv ℳ k : M ≃+ ⨁ r : ZMod k, RegradeByDivision ℳ k r` for a natural number
  `k ≠ 0`: `m ∈ Mⁿ` goes to `m` placed in degree `n / k` of the summand of `n mod k` (Euclidean
  division, `0 ≤ n mod k < k`).
* For a `ℤ`-graded ring `𝒜`, `RegradeByDivision 𝒜 k 0 = ⨁ q, A^{q k}` is a graded ring, each
  `RegradeByDivision ℳ k r` is a graded module over it, and the residue decomposition is linear
  for it (`DG.residueEquiv_smul`).

## Conventions

Residues in `ZMod 2` (resp. `ZMod k`) are represented through `ZMod.val`, i.e. by `0, 1` (resp.
`0, …, k - 1`). The new objects are external direct sums, so that the degree is part of the data.
`DG.Periodize` is a `def` with its own instances (`AddCommGroup`, `Ring`, `Module`), which keeps
instance search on it fast.
-/

namespace DG
open DirectSum

/-- The integer representative `j.val ∈ {0, 1}` of `j ∈ ℤ/2` reduces to `j`. -/
theorem intCast_val_zmodTwo (j : ZMod 2) : ((j.val : ℤ) : ZMod 2) = j := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

section Periodize

variable {M σ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]

/-- The pullback of a `ℤ/2`-grading to `ℤ`: `n ↦ ℳ (n mod 2)`. -/
def periodicGrading (ℳ : ZMod 2 → σ) (n : ℤ) : σ := ℳ n

omit [AddCommGroup M] [AddSubgroupClass σ M] in
@[simp]
theorem mem_periodicGrading {ℳ : ZMod 2 → σ} {n : ℤ} {m : M} :
    m ∈ periodicGrading ℳ n ↔ m ∈ ℳ n := Iff.rfl

/-- The 2-periodic `ℤ`-graded object attached to a `ℤ/2`-graded object `ℳ`: the external direct
sum `⨁ n : ℤ, ℳ (n mod 2)`. -/
def Periodize (ℳ : ZMod 2 → σ) : Type _ := ⨁ n : ℤ, ↥(periodicGrading ℳ n)

instance (ℳ : ZMod 2 → σ) : AddCommGroup (Periodize ℳ) :=
  inferInstanceAs (AddCommGroup (⨁ n : ℤ, ↥(periodicGrading ℳ n)))

variable (ℳ : ZMod 2 → σ)

/-- The `ℤ`-grading of `Periodize ℳ`: the degree-`n` piece is the summand `ℳ (n mod 2)`. -/
def periodizeGrading : ℤ → AddSubgroup (Periodize ℳ) :=
  summand fun n => ↥(periodicGrading ℳ n)

noncomputable instance : Decomposition (periodizeGrading ℳ) :=
  inferInstanceAs (Decomposition (summand fun n => ↥(periodicGrading ℳ n)))

namespace Periodize

/-- An element `m ∈ ℳ (n mod 2)`, placed in degree `n` of `Periodize ℳ`. -/
def mk (n : ℤ) (m : M) (hm : m ∈ ℳ n) : Periodize ℳ :=
  DirectSum.of (fun n => ↥(periodicGrading ℳ n)) n ⟨m, hm⟩

/-- The inclusion of the degree-`n` summand `ℳ^{n mod 2}` of `Periodize ℳ`. -/
def ofHom (n : ℤ) : ↥(periodicGrading ℳ n) →+ Periodize ℳ :=
  DirectSum.of (fun n => ↥(periodicGrading ℳ n)) n

theorem ofHom_apply (n : ℤ) (m : ↥(periodicGrading ℳ n)) :
    ofHom ℳ n m = mk ℳ n (m : M) m.2 := rfl

variable {ℳ}

theorem mk_mem (n : ℤ) {m : M} (hm : m ∈ ℳ n) : mk ℳ n m hm ∈ periodizeGrading ℳ n :=
  of_mem_summand n _

theorem mk_congr {n n' : ℤ} (h : n = n') {m m' : M} (h' : m = m') (hm : m ∈ ℳ n)
    (hm' : m' ∈ ℳ n') : mk ℳ n m hm = mk ℳ n' m' hm' := by
  subst h h'; rfl

@[simp]
theorem mk_zero (n : ℤ) : mk ℳ n 0 (zero_mem _) = 0 := by
  simp only [mk]; exact (DirectSum.of _ n).map_zero

theorem mk_add (n : ℤ) {m m' : M} (hm : m ∈ ℳ n) (hm' : m' ∈ ℳ n) :
    mk ℳ n (m + m') (add_mem hm hm') = mk ℳ n m hm + mk ℳ n m' hm' :=
  (DirectSum.of (fun n => ↥(periodicGrading ℳ n)) n).map_add ⟨m, hm⟩ ⟨m', hm'⟩

theorem mk_neg (n : ℤ) {m : M} (hm : m ∈ ℳ n) :
    mk ℳ n (-m) (neg_mem hm) = -mk ℳ n m hm :=
  (DirectSum.of (fun n => ↥(periodicGrading ℳ n)) n).map_neg ⟨m, hm⟩

theorem mem_periodizeGrading_iff {n : ℤ} {x : Periodize ℳ} :
    x ∈ periodizeGrading ℳ n ↔ ∃ m, ∃ hm : m ∈ ℳ n, mk ℳ n m hm = x := by
  constructor
  · rintro ⟨⟨m, hm⟩, rfl⟩; exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact mk_mem n hm

@[elab_as_elim]
theorem induction_on {P : Periodize ℳ → Prop} (x : Periodize ℳ) (zero : P 0)
    (mk : ∀ (n : ℤ) (m : M) (hm : m ∈ ℳ n), P (mk ℳ n m hm))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact zero
  | of n m => exact mk n m.1 m.2
  | add x y hx hy => exact add x y hx hy

theorem addHom_ext {N : Type*} [AddCommMonoid N] {f g : Periodize ℳ →+ N}
    (h : ∀ (n : ℤ) (m : M) (hm : m ∈ ℳ n), f (mk ℳ n m hm) = g (mk ℳ n m hm)) : f = g :=
  DirectSum.addHom_ext fun n m => h n m.1 m.2

variable (ℳ)

/-- The additive map `Periodize ℳ → M` summing the components. -/
def fold : Periodize ℳ →+ M :=
  DirectSum.toAddMonoid fun n => AddSubmonoidClass.subtype (periodicGrading ℳ n)

@[simp]
theorem fold_mk (n : ℤ) (m : M) (hm : m ∈ ℳ n) : fold ℳ (mk ℳ n m hm) = m :=
  DirectSum.toAddMonoid_of (fun n => AddSubmonoidClass.subtype (periodicGrading ℳ n)) n ⟨m, hm⟩

/-- The additive endomorphism of degree `k` (`k` even) moving `m` from degree `n` to degree
`n + k`. -/
def move (k : ℤ) (hk : (k : ZMod 2) = 0) : Periodize ℳ →+ Periodize ℳ :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun n => ↥(periodicGrading ℳ n)) (n + k)).comp
      { toFun := fun m => ⟨m, by
          rw [mem_periodicGrading, Int.cast_add, hk, add_zero]; exact m.2⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }

@[simp]
theorem move_mk (k : ℤ) (hk : (k : ZMod 2) = 0) (n : ℤ) (m : M) (hm : m ∈ ℳ n) :
    move ℳ k hk (mk ℳ n m hm) =
      mk ℳ (n + k) m (by rw [Int.cast_add, hk, add_zero]; exact hm) :=
  DirectSum.toAddMonoid_of (β := fun n => ↥(periodicGrading ℳ n)) _ n ⟨m, hm⟩

theorem move_move (k l : ℤ) (hk : (k : ZMod 2) = 0) (hl : (l : ZMod 2) = 0) (x : Periodize ℳ) :
    move ℳ k hk (move ℳ l hl x) = move ℳ (l + k) (by rw [Int.cast_add, hk, hl, add_zero]) x := by
  induction x using induction_on with
  | zero => simp
  | mk n m hm => simp only [move_mk]; exact mk_congr (add_assoc _ _ _) rfl _ _
  | add x y hx hy => simp only [map_add, hx, hy]

theorem move_zero (x : Periodize ℳ) : move ℳ 0 Int.cast_zero x = x := by
  induction x using induction_on with
  | zero => simp
  | mk n m hm => simp only [move_mk]; exact mk_congr (add_zero _) rfl _ _
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The shift-by-2 automorphism `σ₂` of `Periodize ℳ`, of degree `2`: `σ₂ (Mⁿ) = Mⁿ⁺²`, the
identity of `M^{n mod 2}` on each summand. -/
def shiftTwo : Periodize ℳ ≃+ Periodize ℳ where
  toFun := move ℳ 2 rfl
  invFun := move ℳ (-2) rfl
  left_inv x := by rw [move_move]; exact move_zero ℳ x
  right_inv x := by rw [move_move]; exact move_zero ℳ x
  map_add' := map_add _

@[simp]
theorem shiftTwo_mk (n : ℤ) (m : M) (hm : m ∈ ℳ n) :
    shiftTwo ℳ (mk ℳ n m hm) =
      mk ℳ (n + 2) m
        (by rw [Int.cast_add, show ((2 : ℤ) : ZMod 2) = 0 from rfl, add_zero]; exact hm) :=
  move_mk ℳ 2 rfl n m hm

theorem shiftTwo_mem {n : ℤ} {x : Periodize ℳ} (hx : x ∈ periodizeGrading ℳ n) :
    shiftTwo ℳ x ∈ periodizeGrading ℳ (n + 2) := by
  obtain ⟨m, hm, rfl⟩ := mem_periodizeGrading_iff.mp hx
  rw [shiftTwo_mk]; exact mk_mem _ _

section Single

variable [Decomposition ℳ]

/-- The component of `m` of parity `n`, placed in degree `n`. -/
def single (n : ℤ) : M →+ Periodize ℳ :=
  (DirectSum.of (fun n => ↥(periodicGrading ℳ n)) n).comp (proj ℳ (n : ZMod 2))

variable {ℳ}

theorem single_of_mem {n : ℤ} {m : M} (hm : m ∈ ℳ n) : single ℳ n m = mk ℳ n m hm := by
  exact congrArg (DirectSum.of (fun n => ↥(periodicGrading ℳ n)) n) (proj_of_mem_same ℳ hm)

theorem single_of_mem_ne {n : ℤ} {i : ZMod 2} {m : M} (hm : m ∈ ℳ i) (h : i ≠ n) :
    single ℳ n m = 0 := by
  exact (congrArg (DirectSum.of (fun n => ↥(periodicGrading ℳ n)) n)
    (proj_of_mem_ne ℳ hm h)).trans (map_zero _)

theorem single_mem (n : ℤ) (m : M) : single ℳ n m ∈ periodizeGrading ℳ n :=
  of_mem_summand n _

theorem fold_single (n : ℤ) (m : M) : fold ℳ (single ℳ n m) = decompose ℳ m n :=
  DirectSum.toAddMonoid_of _ n _

end Single

end Periodize

end Periodize

/-! ### Rings and modules -/

section PeriodizeRing

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ZMod 2 → τ)
  [SetLike.GradedMonoid 𝒜]

instance periodicGrading.gradedMonoid : SetLike.GradedMonoid (periodicGrading 𝒜) where
  one_mem := by simpa using SetLike.GradedOne.one_mem (A := 𝒜)
  mul_mem i j a b ha hb := by
    rw [mem_periodicGrading, Int.cast_add]
    exact SetLike.GradedMul.mul_mem (A := 𝒜) ha hb

instance : Ring (Periodize 𝒜) := inferInstanceAs (Ring (⨁ n : ℤ, ↥(periodicGrading 𝒜 n)))

noncomputable instance : GradedRing (periodizeGrading 𝒜) :=
  inferInstanceAs (GradedRing (summand fun n => ↥(periodicGrading 𝒜 n)))

namespace Periodize

variable {𝒜}

theorem mk_mul_mk {m n : ℤ} {a b : A} (ha : a ∈ 𝒜 m) (hb : b ∈ 𝒜 n) :
    mk 𝒜 m a ha * mk 𝒜 n b hb =
      mk 𝒜 (m + n) (a * b) (SetLike.GradedMul.mul_mem (A := periodicGrading 𝒜) ha hb) :=
  DirectSum.of_mul_of _ _

variable (𝒜)

theorem one_eq_mk : (1 : Periodize 𝒜) =
    mk 𝒜 0 1 (SetLike.GradedOne.one_mem (A := periodicGrading 𝒜)) := rfl

/-- `fold` as a ring homomorphism `Periodize 𝒜 →+* A`. -/
def foldRingHom : Periodize 𝒜 →+* A where
  __ := fold 𝒜
  map_one' := by rw [one_eq_mk]; exact fold_mk _ _ _ _
  map_mul' x y := by
    change fold 𝒜 (x * y) = fold 𝒜 x * fold 𝒜 y
    induction x using induction_on with
    | zero => simp
    | mk m a ha =>
      induction y using induction_on with
      | zero => simp
      | mk n b hb => rw [mk_mul_mk, fold_mk, fold_mk, fold_mk]
      | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

@[simp]
theorem foldRingHom_apply (x : Periodize 𝒜) : foldRingHom 𝒜 x = fold 𝒜 x := rfl

/-- The periodicity unit `u` of `Periodize 𝒜`: the identity `1 ∈ A^{0̄}` placed in degree `2`. Its
inverse is `1` placed in degree `-2`. -/
def periodUnit : (Periodize 𝒜)ˣ where
  val := mk 𝒜 2 1 (SetLike.GradedOne.one_mem (A := 𝒜))
  inv := mk 𝒜 (-2) 1 (SetLike.GradedOne.one_mem (A := 𝒜))
  val_inv := by rw [mk_mul_mk, one_eq_mk]; exact mk_congr (by norm_num) (one_mul 1) _ _
  inv_val := by rw [mk_mul_mk, one_eq_mk]; exact mk_congr (by norm_num) (one_mul 1) _ _

theorem coe_periodUnit_zpow (k : ℤ) :
    ((periodUnit 𝒜 ^ k : (Periodize 𝒜)ˣ) : Periodize 𝒜) =
      mk 𝒜 (2 * k) 1 (by
        rw [Int.cast_mul, show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_mul]
        exact SetLike.GradedOne.one_mem (A := 𝒜)) := by
  induction k using Int.induction_on with
  | hz => rw [zpow_zero, Units.val_one, one_eq_mk]; exact mk_congr (by norm_num) rfl _ _
  | hp k ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    change _ * mk 𝒜 2 1 _ = _
    rw [mk_mul_mk]; exact mk_congr (by ring) (one_mul 1) _ _
  | hn k ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    change _ * mk 𝒜 (-2) 1 _ = _
    rw [mk_mul_mk]; exact mk_congr (by ring) (one_mul 1) _ _

theorem periodUnit_mul_mk {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) :
    (periodUnit 𝒜 : Periodize 𝒜) * mk 𝒜 n a ha = mk 𝒜 (n + 2) a
      (by rw [Int.cast_add, show ((2 : ℤ) : ZMod 2) = 0 from rfl, add_zero]; exact ha) := by
  change mk 𝒜 2 1 _ * _ = _
  rw [mk_mul_mk]; exact mk_congr (add_comm _ _) (one_mul a) _ _

end Periodize

end PeriodizeRing

section PeriodizeModule

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ZMod 2 → τ)
  [SetLike.GradedMonoid 𝒜]
variable {M σ : Type*} [AddCommGroup M] [Module A M] [SetLike σ M] [AddSubgroupClass σ M]
  (ℳ : ZMod 2 → σ) [SetLike.GradedSMul 𝒜 ℳ]

instance periodicGrading.gradedSMul :
    SetLike.GradedSMul (periodicGrading 𝒜) (periodicGrading ℳ) where
  smul_mem i j a b ha hb := by
    rw [mem_periodicGrading, vadd_eq_add, Int.cast_add]
    exact SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha hb

instance : Module (Periodize 𝒜) (Periodize ℳ) :=
  inferInstanceAs (Module (⨁ n : ℤ, ↥(periodicGrading 𝒜 n)) (⨁ n : ℤ, ↥(periodicGrading ℳ n)))

namespace Periodize

variable {𝒜 ℳ}

theorem mk_smul_mk {m n : ℤ} {a : A} {x : M} (ha : a ∈ 𝒜 m) (hx : x ∈ ℳ n) :
    mk 𝒜 m a ha • mk ℳ n x hx =
      mk ℳ (m + n) (a • x) (SetLike.GradedSMul.smul_mem (A := periodicGrading 𝒜)
        (B := periodicGrading ℳ) ha hx) :=
  DirectSum.Gmodule.of_smul_of _ _ _ _

variable (𝒜 ℳ)

instance periodizeGrading.gradedSMul :
    SetLike.GradedSMul (periodizeGrading 𝒜) (periodizeGrading ℳ) where
  smul_mem i j a x ha hx := by
    obtain ⟨a, ha, rfl⟩ := mem_periodizeGrading_iff.mp ha
    obtain ⟨x, hx, rfl⟩ := mem_periodizeGrading_iff.mp hx
    rw [mk_smul_mk]; exact mk_mem _ _

theorem fold_smul (p : Periodize 𝒜) (x : Periodize ℳ) :
    fold ℳ (p • x) = fold 𝒜 p • fold ℳ x := by
  induction p using induction_on with
  | zero => simp
  | mk m a ha =>
    induction x using induction_on with
    | zero => simp
    | mk n y hy => rw [mk_smul_mk, fold_mk, fold_mk, fold_mk]
    | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, smul_add]
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', map_add, add_smul]

theorem periodUnit_smul (x : Periodize ℳ) :
    (periodUnit 𝒜 : Periodize 𝒜) • x = shiftTwo ℳ x := by
  induction x using induction_on with
  | zero => simp
  | mk n y hy =>
    change mk 𝒜 2 1 _ • _ = _
    rw [mk_smul_mk, shiftTwo_mk]; exact mk_congr (add_comm _ _) (one_smul A y) _ _
  | add x y hx hy => rw [smul_add, hx, hy, map_add]

end Periodize

end PeriodizeModule

theorem sum_decompose_univ {ι M σ : Type*} [DecidableEq ι] [Fintype ι] [AddCommMonoid M]
    [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ) [Decomposition ℳ] (m : M) :
    ∑ i, (decompose ℳ m i : M) = m := by
  conv_rhs => rw [← (decompose ℳ).symm_apply_apply m, ← sum_univ_of (decompose ℳ m)]
  change _ = DirectSum.coeAddMonoidHom ℳ _
  rw [map_sum]
  simp

section PeriodicityUnit

variable {A : Type*} [Ring A] (𝒜 : ℤ → AddSubgroup A) [GradedRing 𝒜]

/-- A periodicity unit of a `ℤ`-graded ring: a central unit of degree `2`. -/
structure PeriodicityUnit where
  /-- The unit. -/
  unit : Aˣ
  mem : (unit : A) ∈ 𝒜 2
  commute : ∀ a : A, Commute (unit : A) a

namespace PeriodicityUnit

variable {𝒜} (P : PeriodicityUnit 𝒜)

theorem inv_mem : ((P.unit⁻¹ : Aˣ) : A) ∈ 𝒜 (-2) := by
  set w : A := (decompose 𝒜 ((P.unit⁻¹ : Aˣ) : A) (-2) : A)
  have hw : (P.unit : A) * w = 1 := by
    have h := coe_decompose_mul_add_of_left_mem 𝒜 (j := -2) (b := ((P.unit⁻¹ : Aˣ) : A)) P.mem
    rw [Units.mul_inv, show (2 : ℤ) + -2 = 0 by norm_num, decompose_of_mem_same 𝒜
      SetLike.GradedOne.one_mem] at h
    exact h.symm
  have : ((P.unit⁻¹ : Aˣ) : A) = w := by
    rw [← one_mul w, ← Units.inv_mul P.unit, mul_assoc, hw, mul_one]
  rw [this]; exact (decompose 𝒜 _ (-2)).2

theorem zpow_mem (k : ℤ) : ((P.unit ^ k : Aˣ) : A) ∈ 𝒜 (2 * k) := by
  induction k using Int.induction_on with
  | hz => simpa using (SetLike.GradedOne.one_mem (A := 𝒜))
  | hp k ih =>
    rw [zpow_add_one, Units.val_mul, mul_add, mul_one]
    exact SetLike.GradedMul.mul_mem ih P.mem
  | hn k ih =>
    rw [zpow_sub_one, Units.val_mul, mul_sub, mul_one, sub_eq_add_neg]
    exact SetLike.GradedMul.mul_mem ih P.inv_mem

omit [GradedRing 𝒜] in
theorem commute_zpow (k : ℤ) (a : A) : Commute ((P.unit ^ k : Aˣ) : A) a :=
  (P.commute a).units_zpow_left k

omit [GradedRing 𝒜] in
theorem two_dvd_sub {k n : ℤ} (h : (k : ZMod 2) = n) : 2 ∣ n - k :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub k n 2).mp h

/-- The collapse `A → Aⁿ` onto degree `n`: a homogeneous element `a` of degree `k ≡ n (mod 2)` is
sent to `u^((n - k) / 2) * a`, and homogeneous elements of degree `k ≢ n` are sent to `0`. -/
def collapse (n : ℤ) : A →+ A :=
  liftHomogeneous 𝒜 fun k =>
    if (k : ZMod 2) = n then
      (AddMonoidHom.mulLeft ((P.unit ^ ((n - k) / 2) : Aˣ) : A)).comp (𝒜 k).subtype
    else 0

theorem collapse_of_mem {k n : ℤ} {a : A} (ha : a ∈ 𝒜 k) (h : (k : ZMod 2) = n) :
    P.collapse n a = ((P.unit ^ ((n - k) / 2) : Aˣ) : A) * a := by
  rw [collapse, liftHomogeneous_of_mem 𝒜 _ ha, if_pos h]; rfl

theorem collapse_of_mem_of_ne {k n : ℤ} {a : A} (ha : a ∈ 𝒜 k) (h : (k : ZMod 2) ≠ n) :
    P.collapse n a = 0 := by
  rw [collapse, liftHomogeneous_of_mem 𝒜 _ ha, if_neg h]; rfl

theorem collapse_of_mem_same {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) : P.collapse n a = a := by
  rw [P.collapse_of_mem ha rfl, sub_self, Int.zero_ediv, zpow_zero, Units.val_one, one_mul]

theorem collapse_mem (n : ℤ) (a : A) : P.collapse n a ∈ 𝒜 n := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => rw [map_zero]; exact zero_mem _
  | homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i k
    by_cases h : (k : ZMod 2) = n
    · rw [P.collapse_of_mem ha h]
      have := SetLike.GradedMul.mul_mem (P.zpow_mem ((n - k) / 2)) ha
      rwa [Int.mul_ediv_cancel' (two_dvd_sub h), sub_add_cancel] at this
    · rw [P.collapse_of_mem_of_ne ha h]; exact zero_mem _
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

theorem collapse_unit_mul (n : ℤ) (a : A) : P.collapse n ((P.unit : A) * a) = P.collapse n a := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i k
    have hua := SetLike.GradedMul.mul_mem P.mem ha
    by_cases h : (k : ZMod 2) = n
    · have h' : ((2 + k : ℤ) : ZMod 2) = n := by
        rw [Int.cast_add, show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_add, h]
      rw [P.collapse_of_mem ha h, P.collapse_of_mem hua h', ← mul_assoc, ← Units.val_mul,
        show n - (2 + k) = (n - k) + (-1) * 2 by ring, Int.add_mul_ediv_right _ _ two_ne_zero,
        zpow_add, zpow_neg_one, mul_assoc, inv_mul_cancel, mul_one]
    · have h' : ((2 + k : ℤ) : ZMod 2) ≠ n := by
        rwa [Int.cast_add, show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_add]
      rw [P.collapse_of_mem_of_ne ha h, P.collapse_of_mem_of_ne hua h']
  | add a b ha hb => rw [mul_add, map_add, map_add, ha, hb]

/-- The two-sided ideal generated by `u - 1`. -/
def ideal : Ideal A := Ideal.span {(P.unit : A) - 1}

omit [GradedRing 𝒜] in
theorem mem_ideal {a : A} : a ∈ P.ideal ↔ ∃ b, b * ((P.unit : A) - 1) = a :=
  Ideal.mem_span_singleton'

instance isTwoSided : P.ideal.IsTwoSided where
  mul_mem_of_left b ha := by
    obtain ⟨c, rfl⟩ := P.mem_ideal.mp ha
    refine P.mem_ideal.mpr ⟨c * b, ?_⟩
    rw [mul_assoc, mul_assoc, mul_sub, sub_mul, (P.commute b).eq, mul_one, one_mul]

theorem collapse_eq_zero_of_mem_ideal (n : ℤ) {a : A} (ha : a ∈ P.ideal) : P.collapse n a = 0 := by
  obtain ⟨b, rfl⟩ := P.mem_ideal.mp ha
  rw [mul_sub, mul_one, map_sub, ← (P.commute b).eq, collapse_unit_mul, sub_self]

/-- The quotient ring `A ⧸ (u - 1)`. -/
def Quotient : Type _ := A ⧸ P.ideal

instance : Ring P.Quotient := inferInstanceAs (Ring (A ⧸ P.ideal))

instance : AddCommGroup P.Quotient := inferInstanceAs (AddCommGroup (A ⧸ P.ideal))

/-- The quotient map `A → A ⧸ (u - 1)`. -/
def mkQ : A →+* P.Quotient := Ideal.Quotient.mk P.ideal

omit [GradedRing 𝒜] in
theorem mkQ_surjective : Function.Surjective P.mkQ := Ideal.Quotient.mk_surjective

omit [GradedRing 𝒜] in
theorem mkQ_eq_zero_iff_mem {a : A} : P.mkQ a = 0 ↔ a ∈ P.ideal := Ideal.Quotient.eq_zero_iff_mem

omit [GradedRing 𝒜] in
theorem mkQ_unit : P.mkQ (P.unit : A) = 1 := by
  rw [← sub_eq_zero, ← map_one P.mkQ, ← map_sub, mkQ_eq_zero_iff_mem]
  exact Ideal.subset_span rfl

omit [GradedRing 𝒜] in
theorem mkQ_zpow (k : ℤ) : P.mkQ ((P.unit ^ k : Aˣ) : A) = 1 := by
  have h : Units.map (P.mkQ : A →* P.Quotient) P.unit = 1 := Units.ext (P.mkQ_unit)
  have := congrArg (fun v : (P.Quotient)ˣ => (v : P.Quotient))
    (congrArg (· ^ k) h)
  simpa [← map_zpow] using this

theorem mkQ_collapse_of_mem {k n : ℤ} {a : A} (ha : a ∈ 𝒜 k) (h : (k : ZMod 2) = n) :
    P.mkQ (P.collapse n a) = P.mkQ a := by
  rw [P.collapse_of_mem ha h, map_mul, mkQ_zpow, one_mul]

/-- The collapse onto degree `n`, on the quotient `A ⧸ (u - 1)`. -/
def collapseQ (n : ℤ) : P.Quotient →+ A :=
  QuotientAddGroup.lift P.ideal.toAddSubgroup (P.collapse n) fun _ ha =>
    P.collapse_eq_zero_of_mem_ideal n ha

@[simp]
theorem collapseQ_mkQ (n : ℤ) (a : A) : P.collapseQ n (P.mkQ a) = P.collapse n a := rfl

theorem sum_mkQ_collapse (a : A) : ∑ j : ZMod 2, P.mkQ (P.collapse (j.val : ℤ) a) = P.mkQ a := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i k
    rw [Finset.sum_eq_single (k : ZMod 2)]
    · exact P.mkQ_collapse_of_mem ha (intCast_val_zmodTwo _).symm
    · intro j _ hj
      rw [P.collapse_of_mem_of_ne ha (by rwa [intCast_val_zmodTwo, ne_comm]), map_zero]
    · simp
  | add a b ha hb => simp only [map_add, Finset.sum_add_distrib, ha, hb]

theorem mkQ_eq_zero_iff {a : A} : P.mkQ a = 0 ↔ ∀ n, P.collapse n a = 0 := by
  constructor
  · intro h n
    exact P.collapse_eq_zero_of_mem_ideal n (P.mkQ_eq_zero_iff_mem.mp h)
  · intro h
    rw [← sum_mkQ_collapse]
    simp [h]

theorem eq_zero_of_mem_of_mkQ_eq_zero {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) (h : P.mkQ a = 0) : a = 0 := by
  rw [← P.collapse_of_mem_same ha]; exact P.mkQ_eq_zero_iff.mp h n

/-- The `ℤ/2`-grading of `A ⧸ (u - 1)`: the degree-`j` piece is the image of `A^{j}`, `j ∈ {0, 1}`,
equivalently of every `Aⁿ` with `n ≡ j (mod 2)` (`DG.PeriodicityUnit.mkQ_mem_quotientGrading`). -/
def quotientGrading (j : ZMod 2) : AddSubgroup (P.Quotient) :=
  (𝒜 (j.val : ℤ)).map P.mkQ.toAddMonoidHom

theorem mkQ_mem_quotientGrading {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) :
    P.mkQ a ∈ P.quotientGrading (n : ZMod 2) := by
  rw [← P.mkQ_collapse_of_mem ha (intCast_val_zmodTwo (n : ZMod 2)).symm]
  exact ⟨_, P.collapse_mem _ a, rfl⟩

/-- The decomposition of `A ⧸ (u - 1)`, as an additive map. -/
def decomposeAux : P.Quotient →+ ⨁ j : ZMod 2, P.quotientGrading j :=
  QuotientAddGroup.lift P.ideal.toAddSubgroup
    (∑ j : ZMod 2, (DirectSum.of (fun j => P.quotientGrading j) j).comp
      ((P.mkQ.toAddMonoidHom.comp (P.collapse (j.val : ℤ))).codRestrict _
        fun a => ⟨_, P.collapse_mem _ a, rfl⟩))
    fun a ha => by
      refine (AddMonoidHom.finset_sum_apply _ _ _).trans (Finset.sum_eq_zero fun j _ => ?_)
      have h0 : (⟨P.mkQ (P.collapse (j.val : ℤ) a), _, P.collapse_mem _ a, rfl⟩ :
          P.quotientGrading j) = 0 :=
        Subtype.ext (by simp [P.collapse_eq_zero_of_mem_ideal _ ha])
      exact (congrArg (DirectSum.of (fun j => P.quotientGrading j) j) h0).trans (map_zero _)

theorem decomposeAux_mkQ (a : A) : P.decomposeAux (P.mkQ a) =
    ∑ j : ZMod 2, DirectSum.of (fun j => P.quotientGrading j) j
      ⟨P.mkQ (P.collapse (j.val : ℤ) a), _, P.collapse_mem _ a, rfl⟩ := by
  simp [decomposeAux]; rfl

theorem coe_decomposeAux (x : P.Quotient) :
    DirectSum.coeAddMonoidHom P.quotientGrading (P.decomposeAux x) = x := by
      obtain ⟨a, rfl⟩ := P.mkQ_surjective x
      rw [decomposeAux_mkQ, map_sum]
      simp only [coeAddMonoidHom_of]
      exact P.sum_mkQ_collapse a

theorem decomposeAux_of_mem {j : ZMod 2} {x : P.Quotient} (hx : x ∈ P.quotientGrading j) :
    P.decomposeAux x = DirectSum.of (fun j => P.quotientGrading j) j ⟨x, hx⟩ := by
      obtain ⟨a, ha, rfl⟩ := hx
      change P.decomposeAux (P.mkQ a) = _
      rw [decomposeAux_mkQ, Finset.sum_eq_single j]
      · congr 2; exact congrArg P.mkQ (P.collapse_of_mem_same ha)
      · intro j' _ hj'
        have h0 : (⟨P.mkQ (P.collapse (j'.val : ℤ) a), _, P.collapse_mem _ a, rfl⟩ :
            P.quotientGrading j') = 0 :=
          Subtype.ext (by
            show P.mkQ _ = 0
            rw [P.collapse_of_mem_of_ne (n := (j'.val : ℤ)) ha
              (by rw [intCast_val_zmodTwo, intCast_val_zmodTwo]; exact hj'.symm), map_zero])
        exact (congrArg (DirectSum.of (fun j => P.quotientGrading j) j') h0).trans (map_zero _)
      · simp

instance quotientDecomposition : Decomposition P.quotientGrading :=
  Decomposition.ofAddHom _ P.decomposeAux
    (AddMonoidHom.ext P.coe_decomposeAux)
    (DirectSum.addHom_ext fun j x => by
      simp only [AddMonoidHom.comp_apply, coeAddMonoidHom_of, AddMonoidHom.id_apply]
      exact P.decomposeAux_of_mem x.2)

instance quotientGradedRing : GradedRing P.quotientGrading where
  one_mem := by
    simpa using P.mkQ_mem_quotientGrading (SetLike.GradedOne.one_mem (A := 𝒜))
  mul_mem i j _ _ := by
    rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    show P.mkQ a * P.mkQ b ∈ _
    have := P.mkQ_mem_quotientGrading (SetLike.GradedMul.mul_mem ha hb)
    rwa [Int.cast_add, intCast_val_zmodTwo, intCast_val_zmodTwo, map_mul] at this

end PeriodicityUnit

end PeriodicityUnit

namespace PeriodicityUnit

variable {A : Type*} [Ring A] {𝒜 : ℤ → AddSubgroup A} [GradedRing 𝒜] (P : PeriodicityUnit 𝒜)

/-- The map `A → Periodize (A ⧸ (u - 1))` sending `a ∈ Aⁿ` to the class of `a`, in degree `n`. -/
def toPeriodizeHom : A →+ Periodize P.quotientGrading :=
  liftHomogeneous 𝒜 fun n =>
    (DirectSum.of (fun n => ↥(periodicGrading P.quotientGrading n)) n).comp
      ((P.mkQ.toAddMonoidHom.comp (𝒜 n).subtype).codRestrict _
        fun a => P.mkQ_mem_quotientGrading a.2)

theorem toPeriodizeHom_of_mem {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) :
    P.toPeriodizeHom a = Periodize.mk _ n (P.mkQ a) (P.mkQ_mem_quotientGrading ha) := by
  rw [toPeriodizeHom, liftHomogeneous_of_mem 𝒜 _ ha]; rfl

/-- The inverse map `Periodize (A ⧸ (u - 1)) → A`: a class `x` of parity `n mod 2`, placed in
degree `n`, is sent to its unique representative of degree `n`. -/
def ofPeriodizeHom : Periodize P.quotientGrading →+ A :=
  DirectSum.toAddMonoid fun n =>
    (P.collapseQ n).comp (AddSubmonoidClass.subtype (periodicGrading P.quotientGrading n))

theorem ofPeriodizeHom_mk (n : ℤ) (x : P.Quotient) (hx : x ∈ P.quotientGrading n) :
    P.ofPeriodizeHom (Periodize.mk _ n x hx) = P.collapseQ n x :=
  DirectSum.toAddMonoid_of (β := fun n => ↥(periodicGrading P.quotientGrading n)) _ n ⟨x, hx⟩

theorem ofPeriodizeHom_toPeriodizeHom (a : A) : P.ofPeriodizeHom (P.toPeriodizeHom a) = a := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    rw [P.toPeriodizeHom_of_mem a.2, ofPeriodizeHom_mk, collapseQ_mkQ,
      P.collapse_of_mem_same a.2]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem toPeriodizeHom_ofPeriodizeHom (x : Periodize P.quotientGrading) :
    P.toPeriodizeHom (P.ofPeriodizeHom x) = x := by
  induction x using Periodize.induction_on with
  | zero => simp
  | mk n x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    change P.toPeriodizeHom (P.ofPeriodizeHom (Periodize.mk _ n (P.mkQ a) _)) =
      Periodize.mk _ n (P.mkQ a) _
    rw [ofPeriodizeHom_mk, collapseQ_mkQ, P.toPeriodizeHom_of_mem (P.collapse_mem n a)]
    exact Periodize.mk_congr rfl
      (P.mkQ_collapse_of_mem ha (by rw [intCast_val_zmodTwo])) _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem toPeriodizeHom_mul (a b : A) :
    P.toPeriodizeHom (a * b) = P.toPeriodizeHom a * P.toPeriodizeHom b := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    induction b using Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous b =>
      rw [P.toPeriodizeHom_of_mem (SetLike.GradedMul.mul_mem a.2 b.2),
        P.toPeriodizeHom_of_mem a.2, P.toPeriodizeHom_of_mem b.2, Periodize.mk_mul_mk]
      exact Periodize.mk_congr rfl (map_mul _ _ _) _ _
    | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]

/-- **Periodization of the quotient.** A `ℤ`-graded ring `A` with a periodicity unit `u` is
isomorphic, as a graded ring, to the periodization of the `ℤ/2`-graded ring `A ⧸ (u - 1)`
(see `DG.PeriodicityUnit.periodizeEquiv_mem_iff`). -/
def periodizeEquiv : A ≃+* Periodize P.quotientGrading where
  toFun := P.toPeriodizeHom
  invFun := P.ofPeriodizeHom
  left_inv := P.ofPeriodizeHom_toPeriodizeHom
  right_inv := P.toPeriodizeHom_ofPeriodizeHom
  map_add' := map_add _
  map_mul' := P.toPeriodizeHom_mul

theorem periodizeEquiv_of_mem {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) :
    P.periodizeEquiv a = Periodize.mk _ n (P.mkQ a) (P.mkQ_mem_quotientGrading ha) :=
  P.toPeriodizeHom_of_mem ha

theorem periodizeEquiv_symm_apply (x : Periodize P.quotientGrading) :
    P.periodizeEquiv.symm x = P.ofPeriodizeHom x := rfl

theorem periodizeEquiv_symm_mem (n : ℤ) {x : Periodize P.quotientGrading}
    (hx : x ∈ periodizeGrading P.quotientGrading n) : P.periodizeEquiv.symm x ∈ 𝒜 n := by
  obtain ⟨x, hx, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hx
  rw [periodizeEquiv_symm_apply, ofPeriodizeHom_mk]
  obtain ⟨a, -, rfl⟩ := P.mkQ_surjective x
  exact P.collapse_mem n a

/-- `DG.PeriodicityUnit.periodizeEquiv` preserves degrees. -/
theorem periodizeEquiv_mem_iff {n : ℤ} {a : A} :
    P.periodizeEquiv a ∈ periodizeGrading P.quotientGrading n ↔ a ∈ 𝒜 n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := P.periodizeEquiv_symm_mem n h
    rwa [RingEquiv.symm_apply_apply] at this
  · rw [P.periodizeEquiv_of_mem h]; exact Periodize.mk_mem _ _

theorem periodizeEquiv_periodUnit :
    P.periodizeEquiv (P.unit : A) = (Periodize.periodUnit P.quotientGrading : _) := by
  rw [P.periodizeEquiv_of_mem P.mem]
  exact Periodize.mk_congr rfl P.mkQ_unit _ _

end PeriodicityUnit

namespace Periodize

variable {B τ : Type*} [Ring B] [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ZMod 2 → τ)
  [GradedRing ℬ]

variable {ℬ} in
theorem mk_eq_periodUnit_zpow_mul {m n : ℤ} (h : (m : ZMod 2) = n) {b : B} (hb : b ∈ ℬ n) :
    mk ℬ n b hb = ((periodUnit ℬ ^ ((n - m) / 2) : (Periodize ℬ)ˣ) : Periodize ℬ) *
      mk ℬ m b (h ▸ hb) := by
  rw [coe_periodUnit_zpow, mk_mul_mk]
  exact mk_congr (by rw [Int.mul_ediv_cancel' (PeriodicityUnit.two_dvd_sub h), sub_add_cancel])
    (one_mul b).symm _ _

/-- The periodicity unit `u` of `Periodize ℬ` (`1` placed in degree `2`), as a central unit of
degree `2`. -/
def periodicityUnit : PeriodicityUnit (periodizeGrading ℬ) where
  unit := periodUnit ℬ
  mem := mk_mem 2 _
  commute x := by
    induction x using induction_on with
    | zero => exact Commute.zero_right _
    | mk n b hb =>
      change mk ℬ 2 1 _ * mk ℬ n b hb = mk ℬ n b hb * mk ℬ 2 1 _
      rw [mk_mul_mk, mk_mul_mk]
      exact mk_congr (add_comm _ _) ((one_mul b).trans (mul_one b).symm) _ _
    | add x y hx hy => exact hx.add_right hy

@[simp]
theorem periodicityUnit_unit : (periodicityUnit ℬ).unit = periodUnit ℬ := rfl

theorem mkQ_mk_eq {m n : ℤ} (h : (m : ZMod 2) = n) {b : B} (hb : b ∈ ℬ n) :
    (periodicityUnit ℬ).mkQ (mk ℬ n b hb) = (periodicityUnit ℬ).mkQ (mk ℬ m b (h ▸ hb)) := by
  rw [mk_eq_periodUnit_zpow_mul h, map_mul, ← periodicityUnit_unit,
    PeriodicityUnit.mkQ_zpow, one_mul]

/-- The ring homomorphism `Periodize ℬ ⧸ (u - 1) → B` induced by `DG.Periodize.fold`. -/
def foldQ : (periodicityUnit ℬ).Quotient →+* B :=
  Ideal.Quotient.lift (periodicityUnit ℬ).ideal (foldRingHom ℬ) fun x hx => by
    obtain ⟨y, rfl⟩ := (periodicityUnit ℬ).mem_ideal.mp hx
    have hu : foldRingHom ℬ ((periodUnit ℬ : (Periodize ℬ)ˣ) : Periodize ℬ) = 1 := fold_mk _ _ _ _
    rw [map_mul, map_sub, map_one, periodicityUnit_unit, hu, sub_self, mul_zero]

@[simp]
theorem foldQ_mkQ (x : Periodize ℬ) : foldQ ℬ ((periodicityUnit ℬ).mkQ x) = fold ℬ x :=
  Ideal.Quotient.lift_mk _ _ _

/-- The inverse of `DG.Periodize.foldQ`: `b ↦` the class of `b⁰ + b¹`, placed in degrees `0`
and `1`. -/
def unfoldQ : B →+ (periodicityUnit ℬ).Quotient :=
  (periodicityUnit ℬ).mkQ.toAddMonoidHom.comp (∑ j : ZMod 2, single ℬ (j.val : ℤ))

variable {ℬ} in
theorem unfoldQ_of_mem {j : ZMod 2} {b : B} (hb : b ∈ ℬ j) :
    unfoldQ ℬ b = (periodicityUnit ℬ).mkQ (mk ℬ (j.val : ℤ) b (by rwa [intCast_val_zmodTwo])) := by
  simp only [unfoldQ, AddMonoidHom.comp_apply, AddMonoidHom.finset_sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [single_of_mem]; rfl
  · intro j' _ hj'
    exact single_of_mem_ne hb (by rw [intCast_val_zmodTwo]; exact hj'.symm)
  · simp

theorem foldQ_unfoldQ (b : B) : foldQ ℬ (unfoldQ ℬ b) = b := by
  simp only [unfoldQ, AddMonoidHom.comp_apply, AddMonoidHom.finset_sum_apply]
  change foldQ ℬ ((periodicityUnit ℬ).mkQ _) = b
  rw [foldQ_mkQ, map_sum]
  simp only [fold_single, intCast_val_zmodTwo]
  exact sum_decompose_univ ℬ b

theorem unfoldQ_foldQ (y : (periodicityUnit ℬ).Quotient) : unfoldQ ℬ (foldQ ℬ y) = y := by
  obtain ⟨x, rfl⟩ := (periodicityUnit ℬ).mkQ_surjective y
  rw [foldQ_mkQ]
  induction x using induction_on with
  | zero => simp
  | mk n b hb =>
    rw [fold_mk, unfoldQ_of_mem hb, mkQ_mk_eq ℬ (intCast_val_zmodTwo _) hb]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- **The quotient of the periodization.** For a `ℤ/2`-graded ring `B`, the quotient of its
periodization by `u - 1`, where `u` is `1` placed in degree `2`, is isomorphic to `B` as a
`ℤ/2`-graded ring (`DG.Periodize.quotientEquiv_mem_iff`). -/
def quotientEquiv : (periodicityUnit ℬ).Quotient ≃+* B where
  toFun := foldQ ℬ
  invFun := unfoldQ ℬ
  left_inv := unfoldQ_foldQ ℬ
  right_inv := foldQ_unfoldQ ℬ
  map_add' := map_add _
  map_mul' := map_mul _

theorem quotientEquiv_mkQ (x : Periodize ℬ) :
    quotientEquiv ℬ ((periodicityUnit ℬ).mkQ x) = fold ℬ x :=
  foldQ_mkQ ℬ x

theorem quotientEquiv_symm_apply (b : B) : (quotientEquiv ℬ).symm b = unfoldQ ℬ b := rfl

/-- `DG.Periodize.quotientEquiv` preserves the `ℤ/2`-gradings. -/
theorem quotientEquiv_mem_iff {j : ZMod 2} {y : (periodicityUnit ℬ).Quotient} :
    quotientEquiv ℬ y ∈ ℬ j ↔ y ∈ (periodicityUnit ℬ).quotientGrading j := by
  constructor
  · intro h
    rw [← (quotientEquiv ℬ).symm_apply_apply y, quotientEquiv_symm_apply, unfoldQ_of_mem h]
    exact ⟨_, mk_mem _ _, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨b, hb, rfl⟩ := mem_periodizeGrading_iff.mp hx
    change quotientEquiv ℬ ((periodicityUnit ℬ).mkQ _) ∈ _
    rw [quotientEquiv_mkQ, fold_mk]
    rwa [intCast_val_zmodTwo] at hb

end Periodize

section Division

variable {M σ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]

/-- The family `q ↦ ℳ (q * k + r)`: the pieces of `ℳ` in degrees `≡ r (mod k)`, indexed by the
quotient `q` of the degree by `k`. -/
def divGrading (ℳ : ℤ → σ) (k r q : ℤ) : σ := ℳ (q * k + r)

omit [AddCommGroup M] [AddSubgroupClass σ M] in
@[simp]
theorem mem_divGrading {ℳ : ℤ → σ} {k r q : ℤ} {m : M} :
    m ∈ divGrading ℳ k r q ↔ m ∈ ℳ (q * k + r) := Iff.rfl

/-- The regrading of `ℳ` by division by `k`, on the residue class of `r`: the external direct sum
`⨁ q, ℳ (q * k + r)`, graded by `q`. A map of degree `k` on `ℳ` induces a map of degree `1` on
it. -/
abbrev RegradeByDivision (ℳ : ℤ → σ) (k r : ℤ) : Type _ := ⨁ q : ℤ, ↥(divGrading ℳ k r q)

/-- The canonical grading of `RegradeByDivision ℳ k r`: the degree-`q` piece is `ℳ (q * k + r)`. -/
abbrev regradeGrading (ℳ : ℤ → σ) (k r : ℤ) : ℤ → AddSubgroup (RegradeByDivision ℳ k r) :=
  summand fun q => ↥(divGrading ℳ k r q)

namespace RegradeByDivision

variable (ℳ : ℤ → σ) (k r : ℤ)

/-- An element `m ∈ ℳ (q * k + r)`, placed in degree `q` of `RegradeByDivision ℳ k r`. -/
def mk (q : ℤ) (m : M) (hm : m ∈ ℳ (q * k + r)) : RegradeByDivision ℳ k r :=
  DirectSum.of (fun q => ↥(divGrading ℳ k r q)) q ⟨m, hm⟩

variable {ℳ k r}

theorem mk_mem (q : ℤ) {m : M} (hm : m ∈ ℳ (q * k + r)) :
    mk ℳ k r q m hm ∈ regradeGrading ℳ k r q :=
  of_mem_summand q _

theorem mk_congr {q q' : ℤ} (h : q = q') {m m' : M} (h' : m = m') (hm : m ∈ ℳ (q * k + r))
    (hm' : m' ∈ ℳ (q' * k + r)) : mk ℳ k r q m hm = mk ℳ k r q' m' hm' := by
  subst h h'; rfl

@[simp]
theorem mk_zero (q : ℤ) : mk ℳ k r q 0 (zero_mem _) = 0 :=
  (DirectSum.of (fun q => ↥(divGrading ℳ k r q)) q).map_zero

theorem mk_add (q : ℤ) {m m' : M} (hm : m ∈ ℳ (q * k + r)) (hm' : m' ∈ ℳ (q * k + r)) :
    mk ℳ k r q (m + m') (add_mem hm hm') = mk ℳ k r q m hm + mk ℳ k r q m' hm' :=
  (DirectSum.of (fun q => ↥(divGrading ℳ k r q)) q).map_add ⟨m, hm⟩ ⟨m', hm'⟩

theorem mem_regradeGrading_iff {q : ℤ} {x : RegradeByDivision ℳ k r} :
    x ∈ regradeGrading ℳ k r q ↔ ∃ m, ∃ hm : m ∈ ℳ (q * k + r), mk ℳ k r q m hm = x := by
  constructor
  · rintro ⟨⟨m, hm⟩, rfl⟩; exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact mk_mem q hm

@[elab_as_elim]
theorem induction_on {P : RegradeByDivision ℳ k r → Prop} (x : RegradeByDivision ℳ k r)
    (zero : P 0) (mk : ∀ (q : ℤ) (m : M) (hm : m ∈ ℳ (q * k + r)), P (mk ℳ k r q m hm))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact zero
  | of q m => exact mk q m.1 m.2
  | add x y hx hy => exact add x y hx hy

theorem addHom_ext {N : Type*} [AddCommMonoid N] {f g : RegradeByDivision ℳ k r →+ N}
    (h : ∀ (q : ℤ) (m : M) (hm : m ∈ ℳ (q * k + r)), f (mk ℳ k r q m hm) = g (mk ℳ k r q m hm)) :
    f = g :=
  DirectSum.addHom_ext fun q m => h q m.1 m.2

variable (ℳ k r)

/-- The additive map `RegradeByDivision ℳ k r → M` summing the components. -/
def fold : RegradeByDivision ℳ k r →+ M :=
  DirectSum.toAddMonoid fun q => AddSubmonoidClass.subtype (divGrading ℳ k r q)

@[simp]
theorem fold_mk (q : ℤ) (m : M) (hm : m ∈ ℳ (q * k + r)) : fold ℳ k r (mk ℳ k r q m hm) = m := by
  simp [fold, mk]

end RegradeByDivision

section Residue

variable (ℳ : ℤ → σ) [Decomposition ℳ] (k : ℕ) [NeZero k]

theorem intCast_val_zmod (r : ZMod k) : ((r.val : ℤ) : ZMod k) = r := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem ediv_mul_add_val (n : ℤ) : n / k * k + ((n : ZMod k).val : ℤ) = n := by
  rw [ZMod.val_intCast]; exact Int.ediv_add_emod' n k

theorem mul_add_val_ediv (q : ℤ) (r : ZMod k) : (q * k + (r.val : ℤ)) / k = q := by
  have hk : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne k)
  rw [add_comm, Int.add_mul_ediv_right _ _ hk,
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (ZMod.val_lt r)), zero_add]

theorem intCast_mul_add_val (q : ℤ) (r : ZMod k) : ((q * k + (r.val : ℤ) : ℤ) : ZMod k) = r := by
  rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, zero_add,
    intCast_val_zmod]

omit [Decomposition ℳ] [NeZero k] in
variable {ℳ k} in
theorem of_mk_congr {r r' : ZMod k} (h : r = r') {q q' : ℤ} (hq : q = q') {m : M}
    (hm : m ∈ ℳ (q * k + (r.val : ℤ))) (hm' : m ∈ ℳ (q' * k + (r'.val : ℤ))) :
    DirectSum.of (fun r : ZMod k => RegradeByDivision ℳ k (r.val : ℤ)) r
        (RegradeByDivision.mk ℳ k _ q m hm) =
      DirectSum.of (fun r : ZMod k => RegradeByDivision ℳ k (r.val : ℤ)) r'
        (RegradeByDivision.mk ℳ k _ q' m hm') := by
  subst h hq; rfl

/-- The additive map `M → ⨁ r : ZMod k, RegradeByDivision ℳ k r` sending `m ∈ ℳ n` to `m` placed
in degree `n / k` of the residue class of `n`. -/
def toResidues : M →+ ⨁ r : ZMod k, RegradeByDivision ℳ k (r.val : ℤ) :=
  liftHomogeneous ℳ fun n =>
    (DirectSum.of (fun r : ZMod k => RegradeByDivision ℳ k (r.val : ℤ)) (n : ZMod k)).comp
      { toFun := fun m => RegradeByDivision.mk ℳ k _ (n / k) m
          (by rw [ediv_mul_add_val]; exact m.2)
        map_zero' := RegradeByDivision.mk_zero _
        map_add' := fun m m' => RegradeByDivision.mk_add _ (by rw [ediv_mul_add_val]; exact m.2)
          (by rw [ediv_mul_add_val]; exact m'.2) }

variable {ℳ k} in
theorem toResidues_of_mem {n : ℤ} {m : M} (hm : m ∈ ℳ n) :
    toResidues ℳ k m =
      DirectSum.of (fun r : ZMod k => RegradeByDivision ℳ k (r.val : ℤ)) (n : ZMod k)
        (RegradeByDivision.mk ℳ k _ (n / k) m (by rw [ediv_mul_add_val]; exact hm)) := by
  rw [toResidues, liftHomogeneous_of_mem ℳ _ hm]; rfl

/-- The additive map `⨁ r : ZMod k, RegradeByDivision ℳ k r → M` summing the components. -/
def ofResidues : (⨁ r : ZMod k, RegradeByDivision ℳ k (r.val : ℤ)) →+ M :=
  DirectSum.toAddMonoid fun r => RegradeByDivision.fold ℳ k (r.val : ℤ)

omit [Decomposition ℳ] [NeZero k] in
@[simp]
theorem ofResidues_of_mk (r : ZMod k) (q : ℤ) (m : M) (hm : m ∈ ℳ (q * k + (r.val : ℤ))) :
    ofResidues ℳ k (DirectSum.of (fun r : ZMod k => RegradeByDivision ℳ k (r.val : ℤ)) r
      (RegradeByDivision.mk ℳ k _ q m hm)) = m := by
  simp [ofResidues]

/-- **The residue decomposition.** A `ℤ`-graded object `M` is the direct sum, over the residues
`r ∈ ℤ/k`, of the regradings `RegradeByDivision ℳ k r` of its residue classes: `m ∈ Mⁿ`
corresponds to `m` placed in degree `n / k` of the summand of `n mod k`. -/
def residueEquiv : M ≃+ ⨁ r : ZMod k, RegradeByDivision ℳ k (r.val : ℤ) where
  toFun := toResidues ℳ k
  invFun := ofResidues ℳ k
  left_inv m := by
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | homogeneous m => rw [toResidues_of_mem m.2, ofResidues_of_mk]
    | add m m' hm hm' => rw [map_add, map_add, hm, hm']
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of r x =>
      induction x using RegradeByDivision.induction_on with
      | zero => simp
      | mk q m hm =>
        rw [ofResidues_of_mk, toResidues_of_mem hm]
        exact of_mk_congr (intCast_mul_add_val k q r) (mul_add_val_ediv k q r) _ _
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' := map_add _

theorem residueEquiv_of_mem {n : ℤ} {m : M} (hm : m ∈ ℳ n) :
    residueEquiv ℳ k m =
      DirectSum.of (fun r : ZMod k => RegradeByDivision ℳ k (r.val : ℤ)) (n : ZMod k)
        (RegradeByDivision.mk ℳ k _ (n / k) m (by rw [ediv_mul_add_val]; exact hm)) :=
  toResidues_of_mem hm

theorem residueEquiv_symm_of_mk (r : ZMod k) (q : ℤ) (m : M) (hm : m ∈ ℳ (q * k + (r.val : ℤ))) :
    (residueEquiv ℳ k).symm (DirectSum.of (fun r : ZMod k => RegradeByDivision ℳ k (r.val : ℤ)) r
      (RegradeByDivision.mk ℳ k _ q m hm)) = m :=
  ofResidues_of_mk ℳ k r q m hm

end Residue

/-! ### Rings and modules -/

section DivisionRing

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ℤ → τ)
  [SetLike.GradedMonoid 𝒜] (k : ℤ)

instance divGrading.gradedMonoid : SetLike.GradedMonoid (divGrading 𝒜 k 0) where
  one_mem := by simpa using SetLike.GradedOne.one_mem (A := 𝒜)
  mul_mem p q a b ha hb := by
    rw [mem_divGrading] at *
    have := SetLike.GradedMul.mul_mem (A := 𝒜) ha hb
    rwa [show p * k + 0 + (q * k + 0) = (p + q) * k + 0 by ring] at this

variable {M σ : Type*} [AddCommGroup M] [Module A M] [SetLike σ M] [AddSubgroupClass σ M]
  (ℳ : ℤ → σ) [SetLike.GradedSMul 𝒜 ℳ] (r : ℤ)

instance divGrading.gradedSMul : SetLike.GradedSMul (divGrading 𝒜 k 0) (divGrading ℳ k r) where
  smul_mem p q a m ha hm := by
    rw [mem_divGrading] at *
    have := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha hm
    simp only [vadd_eq_add] at this ⊢
    rwa [show p * k + 0 + (q * k + r) = (p + q) * k + r by ring] at this

namespace RegradeByDivision

variable {𝒜 k ℳ r}

theorem mk_mul_mk {p q : ℤ} {a b : A} (ha : a ∈ 𝒜 (p * k + 0)) (hb : b ∈ 𝒜 (q * k + 0)) :
    mk 𝒜 k 0 p a ha * mk 𝒜 k 0 q b hb =
      mk 𝒜 k 0 (p + q) (a * b) (SetLike.GradedMul.mul_mem (A := divGrading 𝒜 k 0) ha hb) :=
  DirectSum.of_mul_of _ _

theorem one_eq_mk : (1 : RegradeByDivision 𝒜 k 0) =
    mk 𝒜 k 0 0 1 (SetLike.GradedOne.one_mem (A := divGrading 𝒜 k 0)) := rfl

theorem mk_smul_mk {p q : ℤ} {a : A} {m : M} (ha : a ∈ 𝒜 (p * k + 0)) (hm : m ∈ ℳ (q * k + r)) :
    mk 𝒜 k 0 p a ha • mk ℳ k r q m hm =
      mk ℳ k r (p + q) (a • m) (SetLike.GradedSMul.smul_mem (A := divGrading 𝒜 k 0)
        (B := divGrading ℳ k r) ha hm) :=
  DirectSum.Gmodule.of_smul_of _ _ _ _

instance regradeGrading.gradedSMul :
    SetLike.GradedSMul (regradeGrading 𝒜 k 0) (regradeGrading ℳ k r) where
  smul_mem p q a m ha hm := by
    obtain ⟨a, ha, rfl⟩ := mem_regradeGrading_iff.mp ha
    obtain ⟨m, hm, rfl⟩ := mem_regradeGrading_iff.mp hm
    rw [mk_smul_mk]; exact mk_mem _ _

end RegradeByDivision

variable [Decomposition ℳ] (n : ℕ) [NeZero n]

/-- The residue decomposition `DG.residueEquiv` is linear over the regraded ring
`⨁ q, A^{q n}`: for `a ∈ A^{q n}`, the image of `a • m` is `a`, placed in degree `q`, acting on
the image of `m`. -/
theorem residueEquiv_smul {q : ℤ} {a : A} (ha : a ∈ 𝒜 (q * n + 0)) (m : M) :
    residueEquiv ℳ n (a • m) =
      RegradeByDivision.mk 𝒜 n 0 q a ha • residueEquiv ℳ n m := by
  induction m using Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous m =>
    obtain ⟨m, hm⟩ := m
    rename_i l
    have ham := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha hm
    rw [vadd_eq_add] at ham
    rw [residueEquiv_of_mem ℳ n ham, residueEquiv_of_mem ℳ n hm, ← DirectSum.of_smul,
      RegradeByDivision.mk_smul_mk]
    have hk : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne n)
    exact of_mk_congr
      (by rw [add_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
        zero_add])
      (by rw [add_zero, add_comm, Int.add_mul_ediv_right _ _ hk, add_comm]) _ _
  | add m m' hm hm' => rw [smul_add, map_add, map_add, hm, hm', smul_add]

end DivisionRing

end Division

end DG
