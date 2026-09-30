import Mathlib.Algebra.DirectSum.Ring
import DG.Algebra.Commutative
import DG.Graded.Basic
import DG.Lie.ChevalleyEilenberg

/-!
# The Chevalley–Eilenberg cochain algebra

For a Lie algebra `𝔤` over a commutative ring `R`, this file makes the Chevalley–Eilenberg
cochains `C^*(𝔤) = ⨁ₙ Cⁿ(𝔤)` (alternating `R`-multilinear maps `𝔤ⁿ → R`, see
`DG.Lie.ChevalleyEilenberg`) into a commutative dg `R`-algebra, with the wedge product of
alternating maps and the Chevalley–Eilenberg differential.

## Main definitions and results

* `DG.ChevalleyEilenberg.wedgeCochain ω η ∈ Cᵐ⁺ⁿ(𝔤)`: the wedge product of `ω ∈ Cᵐ(𝔤)` and
  `η ∈ Cⁿ(𝔤)`; with it, `n ↦ Cⁿ(𝔤)` is a graded ring (`DG.ChevalleyEilenberg.gRing`).
* `DG.ChevalleyEilenberg.CEAlgebra R 𝔤 = ⨁ n : ℕ, Cⁿ(𝔤)`: an `R`-algebra, a dg abelian group with
  `Cⁿ(𝔤)` in degree `n` (`DG.reindexGrading`) and the Chevalley–Eilenberg differential
  (`DG.ChevalleyEilenberg.CEAlgebra.d_of`), a dg ring (graded Leibniz rule), a dg `R`-algebra and
  a commutative dg algebra (`DG.ChevalleyEilenberg.CEAlgebra.isCDGA`).
* `DG.reindexGrading β e`: the grading of an external direct sum `⨁ n : κ, β n` by `ι` along an
  injective `e : κ → ι`, with its decomposition; used for `ℕ ⊆ ℤ`.

## Implementation notes

The wedge product is defined on *families* `(Fₙ)ₙ` of multilinear cochains
(`DG.ChevalleyEilenberg.Family`) by recursion on the degree, through the contraction formula
`ι_x (F ∧ G) = ι_x F ∧ G + σ F ∧ ι_x G`, where `ι_x` is contraction with `x` in the first
argument and `σ F = ((-1)ⁿ Fₙ)ₙ`. Associativity, unitality, graded commutativity, the vanishing of
odd squares, the preservation of alternating families, and the Leibniz rules for the coadjoint
action and for the differential are all proved by induction on the degree using this formula.
The wedge of alternating maps agrees with the usual shuffle formula (Mathlib's
`AlternatingMap.domCoprod`); this comparison is not formalized here.
-/

noncomputable section

open DirectSum

namespace DG.ChevalleyEilenberg

variable (R 𝔤 : Type*) [CommRing R] [LieRing 𝔤] [LieAlgebra R 𝔤]

/-- Families `(Fₙ)ₙ` of multilinear cochains, one in each degree: the completed cochain
algebra `∏ₙ Cⁿ`, on which the wedge product is defined. -/
abbrev Family : Type _ := (n : ℕ) → MCochain R 𝔤 n

/-- Contraction `ι_x` with `x ∈ 𝔤` in the first argument, on families:
`(ι_x F)ₙ = F_{n+1}(x, -)`. -/
def contr : 𝔤 →ₗ[R] Family R 𝔤 →ₗ[R] Family R 𝔤 :=
  LinearMap.mk₂ R (fun x F n => curryEquiv R 𝔤 n (F (n + 1)) x)
    (fun x x' F => funext fun n => map_add _ x x')
    (fun r x F => funext fun n => map_smul _ r x)
    (fun x F F' => funext fun n => by simp)
    (fun r x F => funext fun n => by simp)

/-- The grading involution `(σ F)ₙ = (-1)^n Fₙ` on families. -/
def sgn : Family R 𝔤 →ₗ[R] Family R 𝔤 where
  toFun F n := koszulSign (n : ℤ) • F n
  map_add' F G := funext fun n => smul_add _ _ _
  map_smul' r F := funext fun n => by
    simp only [Pi.smul_apply, RingHom.id_apply, Units.smul_def]
    exact smul_comm _ r _

/-- The wedge product on families, in degree `K`, defined recursively by
`ι_x (F ∧ G) = ι_x F ∧ G + σ F ∧ ι_x G`. -/
def star : (K : ℕ) → Family R 𝔤 →ₗ[R] Family R 𝔤 →ₗ[R] MCochain R 𝔤 K
  | 0 => LinearMap.mk₂ R (fun F G => MultilinearMap.constOfIsEmpty R _ (F 0 0 * G 0 0))
      (fun F F' G => by ext; simp [add_mul]) (fun r F G => by ext; simp [mul_assoc])
      (fun F G G' => by ext; simp [mul_add]) (fun r F G => by ext; simp [mul_left_comm])
  | K + 1 => LinearMap.mk₂ R (fun F G => (curryEquiv R 𝔤 K).symm
        ((star K).flip G ∘ₗ (contr R 𝔤).flip F + star K (sgn R 𝔤 F) ∘ₗ (contr R 𝔤).flip G))
      (fun F F' G => by ext; simp; abel)
      (fun r F G => by ext; simp)
      (fun F G G' => by ext; simp; abel)
      (fun r F G => by ext; simp)

/-- The wedge product of families of cochains. -/
def wedge : Family R 𝔤 →ₗ[R] Family R 𝔤 →ₗ[R] Family R 𝔤 :=
  LinearMap.mk₂ R (fun F G K => star R 𝔤 K F G)
    (fun F F' G => funext fun K => by simp) (fun r F G => funext fun K => by simp)
    (fun F G G' => funext fun K => by simp) (fun r F G => funext fun K => by simp)

variable {R 𝔤}

@[simp]
theorem contr_apply (x : 𝔤) (F : Family R 𝔤) (n : ℕ) :
    contr R 𝔤 x F n = curryEquiv R 𝔤 n (F (n + 1)) x := rfl

@[simp]
theorem sgn_apply (F : Family R 𝔤) (n : ℕ) : sgn R 𝔤 F n = koszulSign (n : ℤ) • F n := rfl

theorem wedge_apply (F G : Family R 𝔤) (K : ℕ) : wedge R 𝔤 F G K = star R 𝔤 K F G := rfl

theorem wedge_apply_zero_apply (F G : Family R 𝔤) (v : Fin 0 → 𝔤) :
    wedge R 𝔤 F G 0 v = F 0 0 * G 0 0 := rfl

theorem curry_wedge (F G : Family R 𝔤) (K : ℕ) (x : 𝔤) :
    curryEquiv R 𝔤 K (wedge R 𝔤 F G (K + 1)) x =
      wedge R 𝔤 (contr R 𝔤 x F) G K + wedge R 𝔤 (sgn R 𝔤 F) (contr R 𝔤 x G) K := by
  ext v
  simp [wedge_apply, star]

theorem contr_wedge (x : 𝔤) (F G : Family R 𝔤) :
    contr R 𝔤 x (wedge R 𝔤 F G) =
      wedge R 𝔤 (contr R 𝔤 x F) G + wedge R 𝔤 (sgn R 𝔤 F) (contr R 𝔤 x G) :=
  funext fun K => curry_wedge F G K x

theorem mcochain_zero_ext {f g : MCochain R 𝔤 0} (h : f 0 = g 0) : f = g :=
  MultilinearMap.ext fun v => by rwa [Subsingleton.elim v 0]

theorem family_ext {F G : Family R 𝔤} (h₀ : F 0 0 = G 0 0)
    (h : ∀ x, contr R 𝔤 x F = contr R 𝔤 x G) :
    F = G := by
  funext n
  cases n with
  | zero => exact mcochain_zero_ext h₀
  | succ n => exact ext_curry fun x => congrFun (h x) n

theorem contr_sgn (x : 𝔤) (F : Family R 𝔤) :
    contr R 𝔤 x (sgn R 𝔤 F) = -sgn R 𝔤 (contr R 𝔤 x F) := by
  funext n
  ext v
  simp [Units.smul_def, koszulSign_add, koszulSign_odd odd_one]

@[simp]
theorem sgn_sgn (F : Family R 𝔤) : sgn R 𝔤 (sgn R 𝔤 F) = F :=
  funext fun n => by rw [sgn_apply, sgn_apply, smul_smul, Int.units_mul_self, one_smul]

theorem sgn_wedge_apply (K : ℕ) :
    ∀ F G : Family R 𝔤, koszulSign (K : ℤ) • wedge R 𝔤 F G K =
      wedge R 𝔤 (sgn R 𝔤 F) (sgn R 𝔤 G) K := by
  induction K with
  | zero =>
    intro F G
    refine mcochain_zero_ext ?_
    simp [wedge_apply_zero_apply]
  | succ K ih =>
    intro F G
    refine ext_curry fun x => ?_
    have h₂ := ih (sgn R 𝔤 F) (contr R 𝔤 x G)
    rw [sgn_sgn] at h₂
    rw [Units.smul_def, map_zsmul, LinearMap.smul_apply, curry_wedge, curry_wedge, contr_sgn,
      contr_sgn, sgn_sgn, map_neg, LinearMap.neg_apply, Pi.neg_apply, map_neg, Pi.neg_apply,
      ← ih, ← h₂]
    rw [Nat.cast_succ, koszulSign_add, koszulSign_odd odd_one, mul_neg_one, Units.val_neg,
      neg_smul, smul_add, Units.smul_def, Units.smul_def]
    abel

theorem sgn_wedge (F G : Family R 𝔤) :
    sgn R 𝔤 (wedge R 𝔤 F G) = wedge R 𝔤 (sgn R 𝔤 F) (sgn R 𝔤 G) :=
  funext fun K => sgn_wedge_apply K F G

theorem wedge_assoc_apply (K : ℕ) :
    ∀ F G H : Family R 𝔤, wedge R 𝔤 (wedge R 𝔤 F G) H K = wedge R 𝔤 F (wedge R 𝔤 G H) K := by
  induction K with
  | zero =>
    intro F G H
    refine mcochain_zero_ext ?_
    simp only [wedge_apply_zero_apply, mul_assoc]
  | succ K ih =>
    intro F G H
    refine ext_curry fun x => ?_
    simp only [curry_wedge, contr_wedge, sgn_wedge, map_add, LinearMap.add_apply, Pi.add_apply,
      ih]
    abel

/-- The wedge product of families is associative. -/
theorem wedge_assoc (F G H : Family R 𝔤) :
    wedge R 𝔤 (wedge R 𝔤 F G) H = wedge R 𝔤 F (wedge R 𝔤 G H) :=
  funext fun K => wedge_assoc_apply K F G H

variable (R 𝔤) in
/-- The unit family: the constant `1` in degree `0`. -/
def one : Family R 𝔤 := Pi.single 0 (MultilinearMap.constOfIsEmpty R _ 1)

@[simp]
theorem one_zero_apply (v : Fin 0 → 𝔤) : one R 𝔤 0 v = 1 := rfl

@[simp]
theorem contr_one (x : 𝔤) : contr R 𝔤 x (one R 𝔤) = 0 :=
  funext fun n => by simp [one]

@[simp]
theorem sgn_one : sgn R 𝔤 (one R 𝔤) = one R 𝔤 := by
  funext n
  cases n with
  | zero => simp
  | succ n => simp [one]

theorem one_wedge_apply (K : ℕ) : ∀ F : Family R 𝔤, wedge R 𝔤 (one R 𝔤) F K = F K := by
  induction K with
  | zero => intro F; exact mcochain_zero_ext (by simp [wedge_apply_zero_apply])
  | succ K ih =>
    intro F
    refine ext_curry fun x => ?_
    rw [curry_wedge, contr_one, sgn_one, map_zero, LinearMap.zero_apply, Pi.zero_apply, zero_add,
      ih]
    rfl

theorem wedge_one_apply (K : ℕ) : ∀ F : Family R 𝔤, wedge R 𝔤 F (one R 𝔤) K = F K := by
  induction K with
  | zero => intro F; exact mcochain_zero_ext (by simp [wedge_apply_zero_apply])
  | succ K ih =>
    intro F
    refine ext_curry fun x => ?_
    rw [curry_wedge, contr_one, map_zero, Pi.zero_apply, add_zero, ih]
    rfl

@[simp] theorem one_wedge (F : Family R 𝔤) : wedge R 𝔤 (one R 𝔤) F = F :=
  funext fun K => one_wedge_apply K F

@[simp] theorem wedge_one (F : Family R 𝔤) : wedge R 𝔤 F (one R 𝔤) = F :=
  funext fun K => wedge_one_apply K F

/-! ### Homogeneous families -/

/-- A family is homogeneous of degree `m` if it vanishes outside degree `m`. -/
def IsHomog (m : ℕ) (F : Family R 𝔤) : Prop := ∀ n, n ≠ m → F n = 0

theorem IsHomog.contr_of_zero {F : Family R 𝔤} (hF : IsHomog 0 F) (x : 𝔤) :
    contr R 𝔤 x F = 0 :=
  funext fun n => by rw [contr_apply, hF (n + 1) (Nat.succ_ne_zero n), map_zero]; rfl

theorem IsHomog.contr_succ {m : ℕ} {F : Family R 𝔤} (hF : IsHomog (m + 1) F) (x : 𝔤) :
    IsHomog m (contr R 𝔤 x F) := fun n hn => by
  rw [contr_apply, hF (n + 1) (by omega), map_zero]; rfl

theorem IsHomog.sgn_eq {m : ℕ} {F : Family R 𝔤} (hF : IsHomog m F) :
    sgn R 𝔤 F = koszulSign (m : ℤ) • F := funext fun n => by
  rcases eq_or_ne n m with rfl | h
  · rfl
  · rw [sgn_apply, hF n h, smul_zero, Pi.smul_apply, hF n h, smul_zero]

theorem IsHomog.zero_apply_zero {m : ℕ} {F : Family R 𝔤} (hF : IsHomog m F) (hm : m ≠ 0) :
    F 0 0 = 0 := by
  rw [hF 0 hm.symm]; rfl

theorem isHomog_zero (m : ℕ) : IsHomog m (0 : Family R 𝔤) := fun _ _ => rfl

theorem IsHomog.smul {m : ℕ} {F : Family R 𝔤} (hF : IsHomog m F) (u : ℤˣ) :
    IsHomog m (u • F) := fun n hn => by rw [Pi.smul_apply, hF n hn, smul_zero]

theorem isHomog_one : IsHomog 0 (one R 𝔤) := fun n hn => by simp [one, hn]

theorem wedge_apply_eq_zero (K : ℕ) : ∀ (m n : ℕ) (F G : Family R 𝔤), IsHomog m F →
    IsHomog n G → K ≠ m + n → wedge R 𝔤 F G K = 0 := by
  induction K with
  | zero =>
    intro m n F G hF hG hK
    refine mcochain_zero_ext ?_
    rw [wedge_apply_zero_apply]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hG.zero_apply_zero (by omega), mul_zero]; rfl
    · rw [hF.zero_apply_zero (by omega), zero_mul]; rfl
  | succ K ih =>
    intro m n F G hF hG hK
    refine ext_curry fun x => ?_
    rw [curry_wedge, map_zero, LinearMap.zero_apply]
    have h₁ : wedge R 𝔤 (contr R 𝔤 x F) G K = 0 := by
      cases m with
      | zero => rw [hF.contr_of_zero, map_zero, LinearMap.zero_apply]; rfl
      | succ m => exact ih m n _ G (hF.contr_succ x) hG (by omega)
    have h₂ : wedge R 𝔤 (sgn R 𝔤 F) (contr R 𝔤 x G) K = 0 := by
      cases n with
      | zero => rw [hG.contr_of_zero, map_zero]; rfl
      | succ n => exact ih m n _ _ (by rw [hF.sgn_eq]; exact hF.smul _) (hG.contr_succ x) (by omega)
    rw [h₁, h₂, add_zero]

/-- The wedge product of homogeneous families of degrees `m` and `n` is homogeneous of degree
`m + n`. -/
theorem isHomog_wedge {m n : ℕ} {F G : Family R 𝔤} (hF : IsHomog m F) (hG : IsHomog n G) :
    IsHomog (m + n) (wedge R 𝔤 F G) := fun K hK => wedge_apply_eq_zero K m n F G hF hG hK

theorem wedge_units_smul_left (u : ℤˣ) (F G : Family R 𝔤) :
    wedge R 𝔤 (u • F) G = u • wedge R 𝔤 F G := by
  rw [Units.smul_def, Units.smul_def, map_zsmul, LinearMap.smul_apply]

theorem wedge_units_smul_right (u : ℤˣ) (F G : Family R 𝔤) :
    wedge R 𝔤 F (u • G) = u • wedge R 𝔤 F G := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem ks_congr {a b : ℤ} (h : Even (a - b)) : koszulSign a = koszulSign b :=
  (Int.negOnePow_eq_iff a b).mpr h

theorem wedge_comm_apply (K : ℕ) : ∀ (m n : ℕ) (F G : Family R 𝔤), IsHomog m F → IsHomog n G →
    wedge R 𝔤 F G K = koszulSign ((m * n : ℕ) : ℤ) • wedge R 𝔤 G F K := by
  induction K with
  | zero =>
    intro m n F G hF hG
    refine mcochain_zero_ext ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [wedge_apply_zero_apply, mul_comm]
    · rw [wedge_apply_zero_apply, Units.smul_def, _root_.smul_apply,
        wedge_apply_zero_apply, hF.zero_apply_zero (by omega), zero_mul, mul_zero, smul_zero]
  | succ K ih =>
    intro m n F G hF hG
    refine ext_curry fun x => ?_
    rw [Units.smul_def, map_zsmul, LinearMap.smul_apply, curry_wedge, curry_wedge, hF.sgn_eq,
      hG.sgn_eq, wedge_units_smul_left, wedge_units_smul_left, Pi.smul_apply, Pi.smul_apply,
      ← Units.smul_def]
    cases m with
    | zero =>
      rw [hF.contr_of_zero, map_zero, LinearMap.zero_apply, Pi.zero_apply, zero_add,
        map_zero, Pi.zero_apply, smul_zero, add_zero, Nat.zero_mul, Nat.cast_zero,
        koszulSign_zero, one_smul, one_smul]
      cases n with
      | zero => rw [hG.contr_of_zero, map_zero, Pi.zero_apply, map_zero, LinearMap.zero_apply,
          Pi.zero_apply]
      | succ n => rw [ih 0 n F _ hF (hG.contr_succ x), Nat.zero_mul, Nat.cast_zero,
          koszulSign_zero, one_smul]
    | succ m =>
      cases n with
      | zero =>
        rw [hG.contr_of_zero, map_zero, Pi.zero_apply, smul_zero, add_zero, map_zero,
          LinearMap.zero_apply, Pi.zero_apply, zero_add, Nat.mul_zero, Nat.cast_zero,
          koszulSign_zero, one_smul, one_smul, ih m 0 _ G (hF.contr_succ x) hG, Nat.mul_zero,
          Nat.cast_zero, koszulSign_zero, one_smul]
      | succ n =>
        rw [ih m (n + 1) _ G (hF.contr_succ x) hG, ih (m + 1) n F _ hF (hG.contr_succ x),
          smul_smul, smul_add, smul_smul, ← koszulSign_add, ← koszulSign_add, add_comm]
        congr 2
        · exact ks_congr ⟨0, by push_cast; ring⟩
        · exact ks_congr ⟨-((n : ℤ) + 1), by push_cast; ring⟩

/-- Graded commutativity of the wedge product of homogeneous families. -/
theorem wedge_comm {m n : ℕ} {F G : Family R 𝔤} (hF : IsHomog m F) (hG : IsHomog n G) :
    wedge R 𝔤 F G = koszulSign ((m * n : ℕ) : ℤ) • wedge R 𝔤 G F :=
  funext fun K => wedge_comm_apply K m n F G hF hG

/-- The wedge square of a homogeneous family of odd degree vanishes. -/
theorem wedge_self_of_odd {m : ℕ} {F : Family R 𝔤} (hF : IsHomog m F) (hm : Odd m) :
    wedge R 𝔤 F F = 0 := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by obtain ⟨k, rfl⟩ := hm; omega⟩
  refine family_ext ?_ fun x => ?_
  · rw [wedge_apply_zero_apply, hF.zero_apply_zero (Nat.succ_ne_zero m), zero_mul]; rfl
  · have ha : Odd ((m : ℤ) + 1) := by exact_mod_cast hm
    have hb : Even (((m : ℤ) + 1) * m) := by
      rw [mul_comm]; exact Int.even_mul_succ_self m
    have h : Odd (((m + 1 : ℕ) : ℤ) + ((m + 1) * m : ℕ)) := by
      push_cast; exact ha.add_even hb
    rw [contr_wedge, hF.sgn_eq, wedge_units_smul_left, wedge_comm hF (hF.contr_succ x),
      smul_smul, ← koszulSign_add, koszulSign_odd h, Units.neg_smul, one_smul, add_neg_cancel,
      map_zero]

/-! ### Alternating families -/

/-- A family of cochains is alternating if each of its components is. -/
def IsAltFam (F : Family R 𝔤) : Prop := ∀ n, IsAlt (F n)

theorem IsAlt.units_smul {n : ℕ} {f : MCochain R 𝔤 n} (hf : IsAlt f) (u : ℤˣ) :
    IsAlt (u • f) := fun v i j h hij => by
  rw [Units.smul_def, _root_.smul_apply, hf v i j h hij, smul_zero]

theorem IsAlt.add {n : ℕ} {f g : MCochain R 𝔤 n} (hf : IsAlt f) (hg : IsAlt g) :
    IsAlt (f + g) := fun v i j h hij => by
  rw [_root_.add_apply, hf v i j h hij, hg v i j h hij, add_zero]

theorem isAlt_zero_degree (f : MCochain R 𝔤 0) : IsAlt f := fun _ i => i.elim0

theorem isAltFam_contr {F : Family R 𝔤} (hF : IsAltFam F) (x : 𝔤) :
    IsAltFam (contr R 𝔤 x F) := fun n => (hF (n + 1)).curry x

theorem isAltFam_sgn {F : Family R 𝔤} (hF : IsAltFam F) : IsAltFam (sgn R 𝔤 F) :=
  fun n => (hF n).units_smul _

theorem IsAltFam.contr_contr {F : Family R 𝔤} (hF : IsAltFam F) (x : 𝔤) :
    contr R 𝔤 x (contr R 𝔤 x F) = 0 :=
  funext fun n => (hF (n + 2)).curry_curry x

theorem contr_contr_wedge {F G : Family R 𝔤} (hF : IsAltFam F) (hG : IsAltFam G) (x : 𝔤) :
    contr R 𝔤 x (contr R 𝔤 x (wedge R 𝔤 F G)) = 0 := by
  rw [contr_wedge, map_add, contr_wedge, contr_wedge, hF.contr_contr, hG.contr_contr, contr_sgn,
    map_zero, map_zero, LinearMap.zero_apply, map_neg, LinearMap.neg_apply]
  abel

theorem isAlt_wedge_apply (K : ℕ) :
    ∀ F G : Family R 𝔤, IsAltFam F → IsAltFam G → IsAlt (wedge R 𝔤 F G K) := by
  induction K with
  | zero => exact fun F G _ _ => isAlt_zero_degree _
  | succ K ih =>
    intro F G hF hG
    have hφ : ∀ x, IsAlt (curryEquiv R 𝔤 K (wedge R 𝔤 F G (K + 1)) x) := fun x => by
      rw [curry_wedge]
      exact (ih _ _ (isAltFam_contr hF x) hG).add (ih _ _ (isAltFam_sgn hF) (isAltFam_contr hG x))
    rw [← (curryEquiv R 𝔤 K).symm_apply_apply (wedge R 𝔤 F G (K + 1))]
    refine isAlt_curryEquiv_symm _ hφ fun x w k hk => ?_
    cases K with
    | zero => exact k.elim0
    | succ K =>
      refine IsAlt.eq_zero_of_apply_eq (hφ x) (fun u => ?_) w k hk
      rw [← curryEquiv_apply]
      exact congrArg (fun F : Family R 𝔤 => F K u) (contr_contr_wedge hF hG x)

/-- The wedge product of alternating families is alternating. -/
theorem isAltFam_wedge {F G : Family R 𝔤} (hF : IsAltFam F) (hG : IsAltFam G) :
    IsAltFam (wedge R 𝔤 F G) := fun K => isAlt_wedge_apply K F G hF hG

/-! ### The differential on families -/

variable (R 𝔤) in
/-- The coadjoint action on families. -/
def lieFam : 𝔤 →ₗ[R] Family R 𝔤 →ₗ[R] Family R 𝔤 :=
  LinearMap.mk₂ R (fun x F n => lieAct R 𝔤 n x (F n))
    (fun x x' F => funext fun n => by simp) (fun r x F => funext fun n => by simp)
    (fun x F F' => funext fun n => by simp) (fun r x F => funext fun n => by simp)

variable (R 𝔤) in
/-- The Chevalley–Eilenberg differential on families: `(d F)₀ = 0` and `(d F)ₙ₊₁ = d Fₙ`. -/
def dFam : Family R 𝔤 →ₗ[R] Family R 𝔤 where
  toFun F n := match n with
    | 0 => 0
    | n + 1 => ceDiff R 𝔤 n (F n)
  map_add' F G := funext fun n => by cases n <;> simp
  map_smul' r F := funext fun n => by cases n <;> simp

@[simp] theorem lieFam_apply (x : 𝔤) (F : Family R 𝔤) (n : ℕ) :
    lieFam R 𝔤 x F n = lieAct R 𝔤 n x (F n) := rfl

@[simp] theorem dFam_apply_zero (F : Family R 𝔤) : dFam R 𝔤 F 0 = 0 := rfl

@[simp] theorem dFam_apply_succ (F : Family R 𝔤) (n : ℕ) :
    dFam R 𝔤 F (n + 1) = ceDiff R 𝔤 n (F n) := rfl

theorem contr_lieFam (x y : 𝔤) (F : Family R 𝔤) :
    contr R 𝔤 y (lieFam R 𝔤 x F) = lieFam R 𝔤 x (contr R 𝔤 y F) - contr R 𝔤 ⁅x, y⁆ F :=
  funext fun n => curry_lieAct x (F (n + 1)) y

/-- The Cartan formula `ι_x d = x • - - d ι_x` on families. -/
theorem contr_dFam (x : 𝔤) (F : Family R 𝔤) :
    contr R 𝔤 x (dFam R 𝔤 F) = lieFam R 𝔤 x F - dFam R 𝔤 (contr R 𝔤 x F) := by
  funext n
  cases n with
  | zero =>
    ext v
    simp
  | succ n => exact curry_ceDiff (F (n + 1)) x

theorem lieFam_sgn (x : 𝔤) (F : Family R 𝔤) :
    lieFam R 𝔤 x (sgn R 𝔤 F) = sgn R 𝔤 (lieFam R 𝔤 x F) :=
  funext fun n => by simp [Units.smul_def]

theorem dFam_sgn (F : Family R 𝔤) : dFam R 𝔤 (sgn R 𝔤 F) = -sgn R 𝔤 (dFam R 𝔤 F) := by
  funext n
  cases n with
  | zero => simp
  | succ n =>
    ext v
    simp [Units.smul_def, koszulSign_add, koszulSign_odd odd_one]

theorem dFam_dFam (F : Family R 𝔤) : dFam R 𝔤 (dFam R 𝔤 F) = 0 := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => exact map_zero (ceDiff R 𝔤 0)
    | succ n => exact ceDiff_ceDiff (F n)

theorem lieFam_wedge_apply (x : 𝔤) (K : ℕ) : ∀ F G : Family R 𝔤,
    lieFam R 𝔤 x (wedge R 𝔤 F G) K =
      (wedge R 𝔤 (lieFam R 𝔤 x F) G + wedge R 𝔤 F (lieFam R 𝔤 x G)) K := by
  induction K with
  | zero =>
    intro F G
    refine mcochain_zero_ext ?_
    simp [wedge_apply_zero_apply]
  | succ K ih =>
    intro F G
    refine ext_curry fun y => ?_
    change (contr R 𝔤 y (lieFam R 𝔤 x (wedge R 𝔤 F G))) K = (contr R 𝔤 y
      (wedge R 𝔤 (lieFam R 𝔤 x F) G + wedge R 𝔤 F (lieFam R 𝔤 x G))) K
    simp only [contr_lieFam, contr_wedge, map_add, map_sub, lieFam_sgn, Pi.add_apply,
      Pi.sub_apply, ih, LinearMap.sub_apply]
    abel

/-- The coadjoint action is a derivation of the wedge product. -/
theorem lieFam_wedge (x : 𝔤) (F G : Family R 𝔤) :
    lieFam R 𝔤 x (wedge R 𝔤 F G) = wedge R 𝔤 (lieFam R 𝔤 x F) G + wedge R 𝔤 F (lieFam R 𝔤 x G) :=
  funext fun K => lieFam_wedge_apply x K F G

theorem dFam_wedge_apply (K : ℕ) : ∀ F G : Family R 𝔤,
    dFam R 𝔤 (wedge R 𝔤 F G) K =
      (wedge R 𝔤 (dFam R 𝔤 F) G + wedge R 𝔤 (sgn R 𝔤 F) (dFam R 𝔤 G)) K := by
  induction K with
  | zero =>
    intro F G
    refine mcochain_zero_ext ?_
    simp [wedge_apply_zero_apply]
  | succ K ih =>
    intro F G
    refine ext_curry fun x => ?_
    change (contr R 𝔤 x (dFam R 𝔤 (wedge R 𝔤 F G))) K = (contr R 𝔤 x
      (wedge R 𝔤 (dFam R 𝔤 F) G + wedge R 𝔤 (sgn R 𝔤 F) (dFam R 𝔤 G))) K
    simp only [contr_dFam, contr_wedge, map_add, map_sub, lieFam_wedge, contr_sgn, dFam_sgn,
      sgn_sgn, Pi.add_apply, Pi.sub_apply, ih, LinearMap.sub_apply, map_neg,
      LinearMap.neg_apply, Pi.neg_apply]
    abel

/-- The Leibniz rule `d (F ∧ G) = d F ∧ G + σ F ∧ d G`. -/
theorem dFam_wedge (F G : Family R 𝔤) :
    dFam R 𝔤 (wedge R 𝔤 F G) = wedge R 𝔤 (dFam R 𝔤 F) G + wedge R 𝔤 (sgn R 𝔤 F) (dFam R 𝔤 G) :=
  funext fun K => dFam_wedge_apply K F G

/-! ### The graded product on alternating cochains -/

variable (R 𝔤) in
/-- The inclusion of alternating cochains into multilinear cochains, as a linear map. -/
def toMCochain (n : ℕ) : CECochain R 𝔤 n →ₗ[R] MCochain R 𝔤 n where
  toFun ω := ω.toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toMCochain_injective (n : ℕ) : Function.Injective (toMCochain R 𝔤 n) :=
  fun _ _ h => AlternatingMap.ext fun v => congrArg (fun f : MCochain R 𝔤 n => f v) h

variable (R 𝔤) in
/-- An alternating cochain of degree `n`, as a family concentrated in degree `n`. -/
def single (n : ℕ) : CECochain R 𝔤 n →ₗ[R] Family R 𝔤 :=
  LinearMap.single R (fun n => MCochain R 𝔤 n) n ∘ₗ toMCochain R 𝔤 n

theorem single_apply_self {n : ℕ} (ω : CECochain R 𝔤 n) :
    single R 𝔤 n ω n = ω.toMultilinearMap := by
  simp [single, toMCochain]

theorem single_injective (n : ℕ) : Function.Injective (single R 𝔤 n) := fun ω ω' h =>
  toMCochain_injective n (by simpa [single] using congrFun h n)

theorem isHomog_single {n : ℕ} (ω : CECochain R 𝔤 n) : IsHomog n (single R 𝔤 n ω) :=
  fun k hk => by simp [single, hk]

theorem isAltFam_single {n : ℕ} (ω : CECochain R 𝔤 n) : IsAltFam (single R 𝔤 n ω) := fun k => by
  rcases eq_or_ne k n with rfl | hk
  · rw [single_apply_self]; exact isAlt_toMultilinearMap ω
  · rw [isHomog_single ω k hk]; exact isAlt_zero

theorem IsHomog.eq_single {n : ℕ} {F : Family R 𝔤} (hF : IsHomog n F) :
    F = Pi.single n (F n) := funext fun k => by
  rcases eq_or_ne k n with rfl | hk
  · simp
  · rw [hF k hk, Pi.single_eq_of_ne hk]

/-- The wedge product of alternating cochains, `Cᵐ × Cⁿ → Cᵐ⁺ⁿ`. -/
def wedgeCochain {m n : ℕ} (ω : CECochain R 𝔤 m) (η : CECochain R 𝔤 n) :
    CECochain R 𝔤 (m + n) where
  toMultilinearMap := wedge R 𝔤 (single R 𝔤 m ω) (single R 𝔤 n η) (m + n)
  map_eq_zero_of_eq' v i j h hij :=
    isAltFam_wedge (isAltFam_single ω) (isAltFam_single η) (m + n) v i j h hij

theorem single_wedgeCochain {m n : ℕ} (ω : CECochain R 𝔤 m) (η : CECochain R 𝔤 n) :
    single R 𝔤 (m + n) (wedgeCochain ω η) = wedge R 𝔤 (single R 𝔤 m ω) (single R 𝔤 n η) := by
  rw [(isHomog_wedge (isHomog_single ω) (isHomog_single η)).eq_single]
  rfl

/-- Equality of graded monoid elements from equality of the corresponding families. -/
theorem gradedMonoid_mk_eq {i j : ℕ} (h : i = j) {ω : CECochain R 𝔤 i} {η : CECochain R 𝔤 j}
    (hωη : single R 𝔤 i ω = single R 𝔤 j η) :
    (GradedMonoid.mk i ω : GradedMonoid fun n => CECochain R 𝔤 n) = GradedMonoid.mk j η := by
  subst h
  rw [single_injective i hωη]

variable (R 𝔤) in
/-- The unit cochain `1 ∈ C⁰`. -/
def oneCochain : CECochain R 𝔤 0 := AlternatingMap.constOfIsEmpty R 𝔤 (Fin 0) 1

theorem single_oneCochain : single R 𝔤 0 (oneCochain R 𝔤) = one R 𝔤 := by
  simp only [single, one, LinearMap.comp_apply, LinearMap.coe_single]
  rfl

instance gradedMonoid.gMul : GradedMonoid.GMul fun n => CECochain R 𝔤 n :=
  ⟨fun ω η => wedgeCochain ω η⟩

instance gradedMonoid.gOne : GradedMonoid.GOne fun n => CECochain R 𝔤 n := ⟨oneCochain R 𝔤⟩

theorem gMul_def {m n : ℕ} (ω : CECochain R 𝔤 m) (η : CECochain R 𝔤 n) :
    GradedMonoid.GMul.mul ω η = wedgeCochain ω η := rfl

set_option backward.isDefEq.respectTransparency false in
instance gMonoid : GradedMonoid.GMonoid fun n => CECochain R 𝔤 n where
  one_mul := fun ⟨n, ω⟩ => gradedMonoid_mk_eq (zero_add n) (by
    rw [gMul_def, single_wedgeCochain]
    exact (congrArg (wedge R 𝔤 · _) single_oneCochain).trans (one_wedge _))
  mul_one := fun ⟨n, ω⟩ => gradedMonoid_mk_eq (add_zero n) (by
    rw [gMul_def, single_wedgeCochain]
    exact (congrArg (wedge R 𝔤 _ ·) single_oneCochain).trans (wedge_one _))
  mul_assoc := fun ⟨i, ω⟩ ⟨j, η⟩ ⟨k, θ⟩ => gradedMonoid_mk_eq (add_assoc i j k) (by
    simp only [GradedMonoid.snd_mul, gMul_def, single_wedgeCochain, wedge_assoc])

theorem wedgeCochain_add_left {m n : ℕ} (ω ω' : CECochain R 𝔤 m) (η : CECochain R 𝔤 n) :
    wedgeCochain (ω + ω') η = wedgeCochain ω η + wedgeCochain ω' η :=
  single_injective _ (by simp only [map_add, single_wedgeCochain, LinearMap.add_apply])

theorem wedgeCochain_add_right {m n : ℕ} (ω : CECochain R 𝔤 m) (η η' : CECochain R 𝔤 n) :
    wedgeCochain ω (η + η') = wedgeCochain ω η + wedgeCochain ω η' :=
  single_injective _ (by simp only [map_add, single_wedgeCochain])

theorem wedgeCochain_smul_left {m n : ℕ} (r : R) (ω : CECochain R 𝔤 m) (η : CECochain R 𝔤 n) :
    wedgeCochain (r • ω) η = r • wedgeCochain ω η :=
  single_injective _ (by simp only [map_smul, single_wedgeCochain, LinearMap.smul_apply])

theorem wedgeCochain_smul_right {m n : ℕ} (r : R) (ω : CECochain R 𝔤 m) (η : CECochain R 𝔤 n) :
    wedgeCochain ω (r • η) = r • wedgeCochain ω η :=
  single_injective _ (by simp only [map_smul, single_wedgeCochain])

theorem wedgeCochain_zero_left {m n : ℕ} (η : CECochain R 𝔤 n) :
    wedgeCochain (0 : CECochain R 𝔤 m) η = 0 :=
  single_injective _ (by simp only [map_zero, single_wedgeCochain, LinearMap.zero_apply])

theorem wedgeCochain_zero_right {m n : ℕ} (ω : CECochain R 𝔤 m) :
    wedgeCochain ω (0 : CECochain R 𝔤 n) = 0 :=
  single_injective _ (by simp only [map_zero, single_wedgeCochain])

instance gSemiring : DirectSum.GSemiring fun n => CECochain R 𝔤 n :=
  { gMonoid with
    mul_zero := wedgeCochain_zero_right
    zero_mul := wedgeCochain_zero_left
    mul_add := wedgeCochain_add_right
    add_mul := wedgeCochain_add_left
    natCast := fun k => k • oneCochain R 𝔤
    natCast_zero := zero_nsmul _
    natCast_succ := fun k => succ_nsmul _ k }

instance gRing : DirectSum.GRing fun n => CECochain R 𝔤 n :=
  { gSemiring with
    intCast := fun k => k • oneCochain R 𝔤
    intCast_ofNat := fun k => natCast_zsmul _ k
    intCast_negSucc_ofNat := fun k => negSucc_zsmul _ k }

variable (R 𝔤) in
/-- The Chevalley–Eilenberg cochain algebra `C^*(𝔤) = ⨁ₙ Cⁿ(𝔤)` of alternating cochains, with
the wedge product. -/
abbrev CEAlgebra : Type _ := ⨁ n : ℕ, CECochain R 𝔤 n

theorem CEAlgebra.of_mul_of {m n : ℕ} (ω : CECochain R 𝔤 m) (η : CECochain R 𝔤 n) :
    (DirectSum.of (fun n => CECochain R 𝔤 n) m ω * DirectSum.of _ n η : CEAlgebra R 𝔤) =
      DirectSum.of _ (m + n) (wedgeCochain ω η) :=
  DirectSum.of_mul_of ω η

theorem CEAlgebra.one_def :
    (1 : CEAlgebra R 𝔤) = DirectSum.of (fun n => CECochain R 𝔤 n) 0 (oneCochain R 𝔤) := rfl

variable (R 𝔤) in
/-- The embedding of the cochain algebra into families. -/
def CEAlgebra.toFamily : CEAlgebra R 𝔤 →ₗ[R] Family R 𝔤 :=
  DirectSum.toModule R ℕ _ fun n => single R 𝔤 n

theorem CEAlgebra.toFamily_of {n : ℕ} (ω : CECochain R 𝔤 n) :
    CEAlgebra.toFamily R 𝔤 (DirectSum.of _ n ω) = single R 𝔤 n ω :=
  DirectSum.toModule_lof R n ω

theorem CEAlgebra.toFamily_apply (x : CEAlgebra R 𝔤) (n : ℕ) :
    CEAlgebra.toFamily R 𝔤 x n = (x n).toMultilinearMap := by
  induction x using DirectSum.induction_on with
  | zero => rfl
  | of k ω =>
    rw [CEAlgebra.toFamily_of]
    rcases eq_or_ne n k with rfl | h
    · rw [single_apply_self, DirectSum.of_eq_same]
    · rw [isHomog_single ω n h, DirectSum.of_eq_of_ne _ _ _ h]; rfl
  | add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, DirectSum.add_apply]; rfl

theorem CEAlgebra.toFamily_injective : Function.Injective (CEAlgebra.toFamily R 𝔤) :=
  fun x y h => DFinsupp.ext fun n => toMCochain_injective n (by
    have := congrFun h n
    rwa [CEAlgebra.toFamily_apply, CEAlgebra.toFamily_apply] at this)

theorem CEAlgebra.toFamily_mul (x y : CEAlgebra R 𝔤) :
    CEAlgebra.toFamily R 𝔤 (x * y) =
      wedge R 𝔤 (CEAlgebra.toFamily R 𝔤 x) (CEAlgebra.toFamily R 𝔤 y) := by
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero, map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, map_add, LinearMap.add_apply]
  | of m ω =>
    induction y using DirectSum.induction_on with
    | zero => rw [mul_zero, map_zero, map_zero]
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, map_add]
    | of n η =>
      rw [CEAlgebra.of_mul_of, CEAlgebra.toFamily_of, CEAlgebra.toFamily_of,
        CEAlgebra.toFamily_of, single_wedgeCochain]

theorem CEAlgebra.toFamily_one : CEAlgebra.toFamily R 𝔤 1 = one R 𝔤 := by
  rw [CEAlgebra.one_def, CEAlgebra.toFamily_of, single_oneCochain]

/-- The cochain algebra is an `R`-algebra. -/
instance CEAlgebra.instAlgebra : Algebra R (CEAlgebra R 𝔤) :=
  Algebra.ofModule
    (fun r x y => CEAlgebra.toFamily_injective (by
      rw [CEAlgebra.toFamily_mul, map_smul, map_smul, map_smul, CEAlgebra.toFamily_mul,
        LinearMap.smul_apply]))
    (fun r x y => CEAlgebra.toFamily_injective (by
      rw [CEAlgebra.toFamily_mul, map_smul, map_smul, map_smul, CEAlgebra.toFamily_mul]))

end DG.ChevalleyEilenberg

namespace DG

/-! ### Reindexing the grading of an external direct sum -/

section Reindex

variable {κ ι : Type*} [DecidableEq κ] [DecidableEq ι] (β : κ → Type*) [∀ n, AddCommGroup (β n)]
  (e : κ → ι)

/-- The grading of an external direct sum `⨁ n : κ, β n` by `ι` along a map `e : κ → ι`: the
degree-`i` part consists of the elements supported on `e⁻¹ {i}`. For `e = Nat.cast : ℕ → ℤ`,
this places `β n` in degree `n` and `0` in negative degrees. -/
def reindexGrading (i : ι) : AddSubgroup (⨁ n : κ, β n) where
  carrier := {x | ∀ n : κ, e n ≠ i → x n = 0}
  zero_mem' _ _ := rfl
  add_mem' {x y} hx hy n hn := by
    change x n + y n = 0
    rw [hx n hn, hy n hn, add_zero]
  neg_mem' {x} hx n hn := by
    change -(x n) = 0
    rw [hx n hn, neg_zero]

variable {β e}

omit [DecidableEq ι] in
theorem of_mem_reindexGrading (n : κ) (b : β n) :
    DirectSum.of β n b ∈ reindexGrading β e (e n) :=
  fun m hm => DirectSum.of_eq_of_ne _ _ _ (fun h => hm (by rw [← h]))

omit [DecidableEq ι] in
theorem eq_of_mem_reindexGrading {i : ι} {x : ⨁ n : κ, β n} (hx : x ∈ reindexGrading β e i)
    (he : Function.Injective e) (n : κ) (hn : e n = i) : x = DirectSum.of β n (x n) := by
  ext m
  rcases eq_or_ne m n with rfl | h
  · rw [DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, hx m (by rw [← hn]; exact he.ne h)]

omit [DecidableEq κ] [DecidableEq ι] in
theorem eq_zero_of_mem_reindexGrading {i : ι} (hi : i ∉ Set.range e) {x : ⨁ n : κ, β n}
    (hx : x ∈ reindexGrading β e i) : x = 0 := by
  ext m
  exact hx m fun h => hi ⟨m, h⟩

omit [DecidableEq ι] in
/-- Elements of `reindexGrading β e i` (for `e` injective) are `0` or of the form `of β n b`
with `e n = i`. -/
theorem reindexGrading_cases (he : Function.Injective e) {i : ι} {x : ⨁ n : κ, β n}
    (hx : x ∈ reindexGrading β e i) {P : (⨁ n : κ, β n) → Prop} (h₀ : P 0)
    (h : ∀ (n : κ) (b : β n), e n = i → P (of β n b)) : P x := by
  by_cases hi : i ∈ Set.range e
  · obtain ⟨n, hn⟩ := hi
    rw [eq_of_mem_reindexGrading hx he n hn]
    exact h _ _ hn
  · rw [eq_zero_of_mem_reindexGrading hi hx]; exact h₀

/-- The decomposition of `⨁ n : κ, β n` along `reindexGrading β e`, for `e` injective. -/
@[instance_reducible]
noncomputable def reindexGrading.decomposition (he : Function.Injective e) :
    DirectSum.Decomposition (reindexGrading β e) :=
  Decomposition.ofAddHom (reindexGrading β e)
    (DirectSum.toAddMonoid fun n => (DirectSum.of (fun i => reindexGrading β e i) (e n)).comp
      (AddMonoidHom.codRestrict (DirectSum.of β n) _ (of_mem_reindexGrading n)))
    (by ext n b; simp)
    (by
      refine DirectSum.addHom_ext fun i ⟨x, hx⟩ => ?_
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      refine reindexGrading_cases he hx (P := fun x => ∀ hx : x ∈ reindexGrading β e i,
        (DirectSum.toAddMonoid fun n => (DirectSum.of (fun i => reindexGrading β e i) (e n)).comp
          (AddMonoidHom.codRestrict (DirectSum.of β n) _ (of_mem_reindexGrading n))) x =
          DirectSum.of (fun i => reindexGrading β e i) i ⟨x, hx⟩) ?_ ?_ hx
      · intro hx
        rw [map_zero]
        exact (map_zero (DirectSum.of (fun i => reindexGrading β e i) i)).symm
      · rintro n b rfl hx
        rw [DirectSum.toAddMonoid_of]
        rfl)

end Reindex



namespace ChevalleyEilenberg

variable {R 𝔤 : Type*} [CommRing R] [LieRing 𝔤] [LieAlgebra R 𝔤]

/-! ### The dg algebra structure -/

variable (R 𝔤) in
/-- The Chevalley–Eilenberg differential on the cochain algebra `C^*(𝔤) = ⨁ₙ Cⁿ(𝔤)`. -/
def CEAlgebra.dLinear : CEAlgebra R 𝔤 →ₗ[R] CEAlgebra R 𝔤 :=
  DirectSum.toModule R ℕ _ fun n =>
    DirectSum.lof R ℕ (fun n => CECochain R 𝔤 n) (n + 1) ∘ₗ ceD R 𝔤 n

theorem CEAlgebra.dLinear_of {n : ℕ} (ω : CECochain R 𝔤 n) :
    CEAlgebra.dLinear R 𝔤 (DirectSum.of _ n ω) = DirectSum.of _ (n + 1) (ceD R 𝔤 n ω) := by
  rw [← DirectSum.lof_eq_of R, CEAlgebra.dLinear, DirectSum.toModule_lof, LinearMap.comp_apply,
    DirectSum.lof_eq_of]

theorem CEAlgebra.toFamily_dLinear (x : CEAlgebra R 𝔤) :
    CEAlgebra.toFamily R 𝔤 (CEAlgebra.dLinear R 𝔤 x) = dFam R 𝔤 (CEAlgebra.toFamily R 𝔤 x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | of n ω =>
    rw [CEAlgebra.dLinear_of, CEAlgebra.toFamily_of, CEAlgebra.toFamily_of]
    funext k
    cases k with
    | zero => rw [isHomog_single _ 0 (by omega), dFam_apply_zero]
    | succ k =>
      rw [dFam_apply_succ]
      rcases eq_or_ne k n with rfl | h
      · rw [single_apply_self, single_apply_self]; rfl
      · rw [isHomog_single _ (k + 1) (by omega), isHomog_single _ k h, map_zero]

/-- The Chevalley–Eilenberg cochain algebra is a dg abelian group: `Cⁿ(𝔤)` in degree `n`,
nothing in negative degrees, with the Chevalley–Eilenberg differential. -/
noncomputable instance CEAlgebra.instDGAddCommGroup : DGAddCommGroup (CEAlgebra R 𝔤) where
  grading := reindexGrading (fun n => CECochain R 𝔤 n) (Nat.cast : ℕ → ℤ)
  decomposition := reindexGrading.decomposition Nat.cast_injective
  d := (CEAlgebra.dLinear R 𝔤).toAddMonoidHom
  d_mem' {k x} hx := by
    refine reindexGrading_cases Nat.cast_injective hx
      (P := fun x => CEAlgebra.dLinear R 𝔤 x ∈
        reindexGrading (fun n => CECochain R 𝔤 n) (Nat.cast : ℕ → ℤ) (k + 1))
      (by simp only [map_zero]; exact zero_mem _) fun n ω hn => ?_
    rw [CEAlgebra.dLinear_of, ← hn]
    have := of_mem_reindexGrading (e := (Nat.cast : ℕ → ℤ)) (n + 1) (ceD R 𝔤 n ω)
    rwa [Nat.cast_succ] at this
  d_d' x := CEAlgebra.toFamily_injective (by
    change CEAlgebra.toFamily R 𝔤 (CEAlgebra.dLinear R 𝔤 (CEAlgebra.dLinear R 𝔤 x)) =
      CEAlgebra.toFamily R 𝔤 0
    rw [CEAlgebra.toFamily_dLinear, CEAlgebra.toFamily_dLinear, dFam_dFam, map_zero])

theorem CEAlgebra.d_def (x : CEAlgebra R 𝔤) : d x = CEAlgebra.dLinear R 𝔤 x := rfl

theorem CEAlgebra.d_of {n : ℕ} (ω : CECochain R 𝔤 n) :
    d (DirectSum.of (fun n => CECochain R 𝔤 n) n ω : CEAlgebra R 𝔤) =
      DirectSum.of _ (n + 1) (ceD R 𝔤 n ω) :=
  CEAlgebra.dLinear_of ω

theorem CEAlgebra.of_mem_grading {n : ℕ} (ω : CECochain R 𝔤 n) :
    (DirectSum.of (fun n => CECochain R 𝔤 n) n ω : CEAlgebra R 𝔤) ∈ grading (n : ℤ) :=
  of_mem_reindexGrading n ω

/-- Induction on homogeneous elements of the cochain algebra. -/
theorem CEAlgebra.grading_cases {k : ℤ} {x : CEAlgebra R 𝔤} (hx : x ∈ grading k)
    {P : CEAlgebra R 𝔤 → Prop} (h₀ : P 0)
    (h : ∀ (n : ℕ) (ω : CECochain R 𝔤 n), (n : ℤ) = k → P (DirectSum.of _ n ω)) : P x :=
  reindexGrading_cases Nat.cast_injective hx h₀ h

theorem CEAlgebra.toFamily_units_smul (u : ℤˣ) (x : CEAlgebra R 𝔤) :
    CEAlgebra.toFamily R 𝔤 (u • x) = u • CEAlgebra.toFamily R 𝔤 x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- The Chevalley–Eilenberg cochain algebra is a dg ring: the differential satisfies the graded
Leibniz rule for the wedge product. -/
instance CEAlgebra.instDGRing : DGRing (CEAlgebra R 𝔤) where
  one_mem := by
    rw [CEAlgebra.one_def]
    simpa using CEAlgebra.of_mem_grading (oneCochain R 𝔤)
  mul_mem i j a b ha hb := by
    refine CEAlgebra.grading_cases ha (P := fun a => a * b ∈ grading (i + j))
      (by rw [zero_mul]; exact zero_mem _) fun m ω hm => ?_
    refine CEAlgebra.grading_cases hb (P := fun b => DirectSum.of _ m ω * b ∈ grading (i + j))
      (by rw [mul_zero]; exact zero_mem _) fun p η hp => ?_
    rw [CEAlgebra.of_mul_of, ← hm, ← hp, ← Nat.cast_add]
    exact CEAlgebra.of_mem_grading _
  d_mul' {n a} ha b := by
    refine CEAlgebra.grading_cases ha (P := fun a => d (a * b) = d a * b +
      koszulSign n • (a * d b)) (by simp) fun m ω hm => ?_
    subst hm
    refine CEAlgebra.toFamily_injective ?_
    simp only [CEAlgebra.d_def, map_add, CEAlgebra.toFamily_units_smul, CEAlgebra.toFamily_mul,
      CEAlgebra.toFamily_dLinear, dFam_wedge, CEAlgebra.toFamily_of,
      (isHomog_single ω).sgn_eq, wedge_units_smul_left]

/-- The Chevalley–Eilenberg cochain algebra is a dg `R`-algebra. -/
instance CEAlgebra.instDGAlgebra : DGAlgebra R (CEAlgebra R 𝔤) where
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    intro n hn
    rw [DirectSum.smul_apply, (one_mem_grading (A := CEAlgebra R 𝔤)) n hn, smul_zero]
  d_algebraMap' r := by
    rw [Algebra.algebraMap_eq_smul_one, CEAlgebra.d_def, map_smul, ← CEAlgebra.d_def,
      CEAlgebra.one_def, CEAlgebra.d_of, ceD_zero, map_zero, smul_zero]

/-- The Chevalley–Eilenberg cochain algebra is a commutative dg algebra. -/
instance CEAlgebra.isCDGA : IsCDGA (CEAlgebra R 𝔤) where
  mul_comm_of_mem' {i j a b} ha hb := by
    refine CEAlgebra.grading_cases ha (P := fun a => a * b = koszulSign (i * j) • (b * a))
      (by simp) fun m ω hm => ?_
    refine CEAlgebra.grading_cases hb (P := fun b => DirectSum.of _ m ω * b =
      koszulSign (i * j) • (b * DirectSum.of _ m ω)) (by simp) fun p η hp => ?_
    subst hm hp
    refine CEAlgebra.toFamily_injective ?_
    rw [CEAlgebra.toFamily_units_smul, CEAlgebra.toFamily_mul, CEAlgebra.toFamily_mul,
      CEAlgebra.toFamily_of, CEAlgebra.toFamily_of,
      wedge_comm (isHomog_single ω) (isHomog_single η), Nat.cast_mul]
  mul_self_of_odd' {i a} ha hi := by
    refine CEAlgebra.grading_cases ha (P := fun a => a * a = 0) (by simp) fun m ω hm => ?_
    subst hm
    refine CEAlgebra.toFamily_injective ?_
    rw [CEAlgebra.toFamily_mul, CEAlgebra.toFamily_of, map_zero,
      wedge_self_of_odd (isHomog_single ω) (by exact_mod_cast hi)]

end ChevalleyEilenberg

end DG