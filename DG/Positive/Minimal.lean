import DG.Derived.Minimal
import DG.Positive.Schnurer

/-!
# Minimal finite-cell models over positive dg rings

Let `A` be a dg ring without negative degrees and with `d(A⁰) = 0` (conditions (P1) and (P3) of
a positive dg ring, `DG.IsPositive`). This file shows that a finite-cell dg module over `A` whose
cells `(A eᵢ)⟦nᵢ⟧` are ordered (`n₁ ≥ n₂ ≥ ⋯`, `DG.FiniteCellFiltration.IsOrdered`) is minimal
(`DG.FiniteCellFiltration.IsOrdered.isMinimal`) and bounded below
(`DG.FiniteCellFiltration.isBoundedBelow`). With Schnürer's theorem
(`DG.IsPositive.exists_finiteCellFiltration_of_isCompact`) and the uniqueness of minimal models
(`DG/Derived/Minimal.lean`): for a positive dg ring, every compact object of `D(A)` is the image
of a minimal ordered finite-cell module, unique up to isomorphism of dg modules
(`DG.IsPositive.exists_isBoundedMinimal_of_isCompact`,
`DG.IsPositive.exists_bijective_of_iso`).

## Proof of minimality

Write `gᵢ = -nᵢ` for the degree of the generator of the `i`-th cell, so `g₁ ≤ g₂ ≤ ⋯`, and let
`s` be a graded section of the projection `π : F (i + 1) → (A eᵢ)⟦nᵢ⟧`. By induction on `i`:
for `x ∈ F i` homogeneous of degree `m`, `d x` is decomposable, and `x` itself is decomposable
when `m > gⱼ` for all `j < i`. For `x ∈ F (i + 1)` of degree `m` write `x = (x - s(π x)) + s(π x)`
with `x - s(π x) ∈ F i`, and `π x = b • εᵢ` for `b ∈ A^{m - gᵢ}` and the generator `εᵢ`:
* if `m > gᵢ`, then `s (π x) = ± b • s(εᵢ)` and its differential are decomposable;
* if `m = gᵢ`, then `d b = 0` (as `b ∈ A⁰`), so `d s(π x) ∈ F i` has degree `gᵢ + 1 > gⱼ` for
  `j < i` and is decomposable by induction;
* if `m < gᵢ`, then `π x = 0`.
-/

open CategoryTheory DirectSum

universe u

namespace DG

namespace FiniteCellFiltration

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  (C : FiniteCellFiltration A P) (hA : ∀ j < 0, ∀ a ∈ grading (M := A) j, a = 0)

omit [DGRing A] [DGAddCommGroup P] [DGModule A P] in
private theorem units_smul_mem_decomposables (u : ℤˣ) {y : P} (hy : y ∈ decomposables A P) :
    u • y ∈ decomposables A P := by
  rw [Units.smul_def]
  exact zsmul_mem hy _

include hA

omit [DGModule A P] in
/-- The element `π x` of the subquotient `(A eᵢ)⟦nᵢ⟧`, for `x` homogeneous of degree `m`, is
an element of `A` of degree `m + nᵢ`; it vanishes if `m + nᵢ < 0`. -/
theorem π_eq_zero_of_lt {i : Fin C.length} {m : ℤ} {x : C.F (i.1 + 1)}
    (hx : (x : P) ∈ grading m) (hm : m + C.shift i < 0) : C.π i x = 0 := by
  have h1 : Shift.unmk (C.shift i) (C.π i x) ∈ grading (m + C.shift i) :=
    Shift.unmk_mem_grading ((C.π i).map_mem ((DGSubmodule.mem_grading _).mpr hx))
  have h2 : ((Shift.unmk (C.shift i) (C.π i x) : (C.e i).LeftCorner) : A) = 0 :=
    hA _ hm _ ((DGIdempotent.LeftCorner.mem_grading_iff _).mp h1)
  exact (Shift.unmk (C.shift i)).injective (Subtype.ext h2)

omit [DGModule A P] in
/-- A homogeneous element of `F k` of degree smaller than the degrees `-nᵢ` of the generators of
the cells `i < k` vanishes. -/
theorem eq_zero_of_lt : ∀ k ≤ C.length, ∀ {m : ℤ} {x : P}, x ∈ C.F k → x ∈ grading m →
    (∀ i : Fin C.length, i.1 < k → m < -C.shift i) → x = 0 := by
  intro k
  induction k with
  | zero => intro _ m x hx _ _; exact C.eq_zero_of_mem_zero x hx
  | succ k ih =>
    intro hk m x hx hxm h
    let i : Fin C.length := ⟨k, by omega⟩
    have hπ : C.π i ⟨x, hx⟩ = 0 :=
      C.π_eq_zero_of_lt hA (x := ⟨x, hx⟩) hxm (by have := h i (by simp [i]); omega)
    exact ih (by omega) ((C.π_eq_zero_iff i ⟨x, hx⟩).mp hπ) hxm fun j hj => h j (by omega)

omit [DGModule A P] in
include C in
/-- Over a dg ring without negative degrees, a finite-cell dg module is bounded below. -/
theorem isBoundedBelow : IsBoundedBelow P := by
  refine ⟨-∑ i, |C.shift i|, fun m hm x hx => C.eq_zero_of_lt hA _ le_rfl (C.mem_length x) hx
    fun i _ => ?_⟩
  have h1 := Finset.single_le_sum (f := fun j => |C.shift j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  have h2 := le_abs_self (C.shift i)
  omega

variable (hd : ∀ a ∈ grading (M := A) 0, d a = 0)
include hd

theorem isMinimal_aux (hC : C.IsOrdered) : ∀ k ≤ C.length, ∀ {m : ℤ} {x : P}, x ∈ C.F k →
    x ∈ grading m → d x ∈ decomposables A P ∧
      ((∀ i : Fin C.length, i.1 < k → -C.shift i < m) → x ∈ decomposables A P) := by
  intro k
  induction k with
  | zero =>
    intro _ m x hx _
    rw [C.eq_zero_of_mem_zero x hx, d_zero]
    exact ⟨zero_mem _, fun _ => zero_mem _⟩
  | succ k ih =>
    intro hk m x hx hxm
    let i : Fin C.length := ⟨k, by omega⟩
    obtain ⟨s, hs⟩ := C.exists_section i
    let x' : C.F (i.1 + 1) := ⟨x, hx⟩
    let y := C.π i x'
    have hy : y ∈ grading m := (C.π i).map_mem ((DGSubmodule.mem_grading _).mpr hxm)
    let z : P := (s y : C.F (i.1 + 1))
    have hz : z ∈ grading m := by
      have := s.map_mem hy
      rw [add_zero] at this
      exact (DGSubmodule.mem_grading _).mp this
    have hxz : x - z ∈ C.F k := by
      have := (C.π_eq_zero_iff i (x' - s y)).mp (by rw [map_sub, hs, sub_self])
      exact this
    obtain ⟨ih₁, ih₂⟩ := ih (by omega) hxz (sub_mem hxm hz)
    have hdx : d x = d (x - z) + d z := by rw [d_sub, sub_add_cancel]
    have hxx : x = (x - z) + z := by rw [sub_add_cancel]
    let n := C.shift i
    let b : (C.e i).LeftCorner := Shift.unmk n y
    have hb : (b : A) ∈ grading (m + n) :=
      (DGIdempotent.LeftCorner.mem_grading_iff _).mp (Shift.unmk_mem_grading hy)
    rcases lt_trichotomy (m + n) 0 with hmn | hmn | hmn
    · -- `π x = 0`: then `x ∈ F k`.
      have hy0 : y = 0 := C.π_eq_zero_of_lt hA (x := x') hxm hmn
      have hz0 : z = 0 := by
        change ((s y : C.F (i.1 + 1)) : P) = 0
        rw [hy0, map_zero]
        rfl
      rw [hz0, sub_zero] at ih₁ ih₂
      exact ⟨ih₁, fun h => ih₂ fun j hj => h j (by omega)⟩
    · -- `m = gᵢ`: `d (s (π x)) ∈ F k` has degree `gᵢ + 1`.
      have hdb : d (b : A) = 0 := hd _ (by rw [hmn] at hb; exact hb)
      have hdy : d y = 0 := by
        apply (Shift.unmk n).injective
        rw [Shift.unmk_d, map_zero]
        have : d b = 0 := Subtype.ext (by rw [DGIdempotent.LeftCorner.coe_d, hdb]; rfl)
        rw [this, smul_zero]
      have hdz : d z ∈ C.F k := by
        have := (C.π_eq_zero_iff i (d (s y))).mp (by rw [(C.π i).map_d, hs, hdy])
        exact this
      have hdz' : d z ∈ grading (m + 1) := d_mem hz
      have h₂ := (ih (by omega) hdz hdz').2 fun j hj => by
        have := hC j i (Fin.le_iff_val_le_val.mpr (by simp [i]; omega))
        change -C.shift j < m + 1
        omega
      refine ⟨by rw [hdx]; exact add_mem ih₁ h₂, fun h => ?_⟩
      have := h i (by simp [i])
      change -C.shift i < m at this
      omega
    · -- `m > gᵢ`: `s (π x) = ± b • s(εᵢ)` is decomposable.
      have hε : (C.e i).val ∈ (C.e i).leftIdeal := by
        rw [DGIdempotent.mem_leftIdeal, (C.e i).mul_self]
      let ε : (C.e i).LeftCorner := ⟨(C.e i).val, hε⟩
      have hbε : (b : A) • ε = b := Subtype.ext (by
        change (b : A) * (C.e i).val = b
        exact (DGIdempotent.mem_leftIdeal _).mp b.2)
      have hyε : y = koszulSign (n * (m + n)) • ((b : A) • Shift.mk n ε) := by
        rw [← Shift.mk_smul hb, hbε]
        rfl
      let w : P := (s (Shift.mk n ε) : C.F (i.1 + 1))
      have hzw : z = koszulSign (n * (m + n)) • ((b : A) • w) := by
        change ((s y : C.F (i.1 + 1)) : P) = _
        rw [hyε, Units.smul_def, map_zsmul, s.map_smul hb, zero_mul, koszulSign_zero, one_smul]
        rfl
      have hmn' : m + n ≠ 0 := by omega
      have hzd : z ∈ decomposables A P := by
        rw [hzw]
        exact units_smul_mem_decomposables _ (smul_mem_decomposables hmn' hb w)
      have hdzd : d z ∈ decomposables A P := by
        rw [hzw, d_units_smul, d_smul hb]
        refine units_smul_mem_decomposables _ (add_mem ?_ ?_)
        · exact smul_mem_decomposables (show m + n + 1 ≠ 0 by omega) (d_mem hb) w
        · exact units_smul_mem_decomposables _ (smul_mem_decomposables hmn' hb _)
      refine ⟨by rw [hdx]; exact add_mem ih₁ hdzd, fun h => ?_⟩
      rw [hxx]
      exact add_mem (ih₂ fun j hj => h j (by omega)) hzd

/-- **Ordered finite-cell modules are minimal**: over a dg ring without negative degrees and with
`d(A⁰) = 0`, a finite-cell dg module whose cells `(A eᵢ)⟦nᵢ⟧` satisfy `n₁ ≥ n₂ ≥ ⋯` is minimal. -/
theorem IsOrdered.isMinimal (hC : C.IsOrdered) : IsMinimal A P := by
  intro x
  induction x using DG.induction_on with
  | h_zero => rw [d_zero]; exact zero_mem _
  | @h_homogeneous m x => exact (C.isMinimal_aux hA hd hC _ le_rfl (C.mem_length _) x.2).1
  | h_add x y hx hy => rw [d_add]; exact add_mem hx hy

theorem IsOrdered.isBoundedMinimal (hC : C.IsOrdered) : IsBoundedMinimal A P :=
  .of_nonneg hA (hC.isMinimal C hA hd) (isBoundedBelow C hA)

end FiniteCellFiltration

namespace IsPositive

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (hA : IsPositive A)
include hA

theorem eq_zero_of_mem_grading_neg {j : ℤ} (hj : j < 0) {a : A} (ha : a ∈ grading j) : a = 0 := by
  rw [hA.grading_eq_bot j hj] at ha
  exact ha

variable [HasDerivedCategory.{u, u} A]

/-- **Minimal models of compact objects**: for a positive dg ring, every compact object of `D(A)`
is the image of a minimal (and bounded-below) ordered finite-cell dg module with simple cells. -/
theorem exists_isBoundedMinimal_of_isCompact {X : DerivedCategory.{u, u} A}
    (hX : IsCompact.{u} X) :
    ∃ (P : DGModuleCat.{u} A) (C : FiniteCellFiltration A P), C.IsOrdered ∧
      (∀ i, (C.e i).IsSimple) ∧ IsBoundedMinimal A P ∧ Nonempty (X ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨P, C, hC, hs, he⟩ := hA.exists_finiteCellFiltration_of_isCompact hX
  exact ⟨P, C, hC, hs, hC.isBoundedMinimal C (fun _ hj _ ha => hA.eq_zero_of_mem_grading_neg hj ha)
    hA.d_eq_zero_of_mem_zero, he⟩

/-- **Uniqueness of minimal finite-cell models**: for a positive dg ring, two ordered
finite-cell dg modules whose images in `D(A)` are isomorphic are isomorphic as dg modules: every
isomorphism `Q P ≅ Q P'` in `D(A)` is the image of a bijective morphism of dg modules. -/
theorem exists_bijective_of_iso {P P' : DGModuleCat.{u} A} (C : FiniteCellFiltration A P)
    (hC : C.IsOrdered) (C' : FiniteCellFiltration A P') (hC' : C'.IsOrdered)
    (φ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    ∃ f : P ⟶ P', Function.Bijective f ∧ DerivedCategory.Q.map f = φ.hom := by
  have hA' : ∀ j < 0, ∀ a ∈ grading (M := A) j, a = 0 := fun _ hj _ ha =>
    hA.eq_zero_of_mem_grading_neg hj ha
  obtain ⟨f, hf⟩ := DerivedCategory.exists_Q_map_eq (C.isKProjective : IsKProjective.{u} A P) φ.hom
  have hq : f.hom.IsQuasiIso := by
    rw [← DerivedCategory.isIso_Q_map_iff, hf]
    infer_instance
  exact ⟨f, IsKProjective.bijective_of_isQuasiIso (C.isKProjective : IsKProjective.{u} A P)
    (C'.isKProjective : IsKProjective.{u} A P') (hC.isBoundedMinimal C hA' hA.d_eq_zero_of_mem_zero)
    (hC'.isBoundedMinimal C' hA' hA.d_eq_zero_of_mem_zero) hq, hf⟩

end IsPositive

end DG
