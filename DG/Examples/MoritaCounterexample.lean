import DG.Derived.Morita
import DG.Derived.Zero
import DG.Module.Cone
import DG.Module.Prod
import DG.Module.End

/-!
# A counterexample to Morita theory for idempotents with `A e A = A`

The literal form of Roadmap item 7.3 asserts that for a dg ring `A` and a degree-`0` idempotent
cocycle `e` with `A e A = A`, the derived categories of `e A e` and `A` are equivalent. This is
false; the correct hypothesis is that `e` is full up to homotopy (`DG.DGIdempotent.IsFullH0`,
`DG.DGIdempotent.moritaEquivalence`).

Let `R` be a nontrivial commutative ring, concentrated in degree `0`, let `K = cone(id_R)` (`R` in
degrees `-1` and `0` with `d = id`, a contractible complex), `V = K ⊕ R` and `A = END_R(V)`, and
let `e ∈ Z⁰(A)` be the projection onto `K` (`DG.MoritaCounterexample.e`). Then:

* `A e A = A`: `1 = e + f e g` for the chain map `f : (k, r) ↦ ((0, r), 0)` and the (non-closed)
  map `g : ((x, y), r) ↦ (0, y)` (`DG.MoritaCounterexample.one_eq`,
  `DG.MoritaCounterexample.one_mem_span`);
* `e A e` is acyclic: the contracting homotopy `h` of `K` lies in `e A e` and `d h = e = 1`
  (`DG.MoritaCounterexample.d_hCorner`), so `D(e A e) = 0`;
* `A` is not acyclic: `d x = 1` has no solution in `A`
  (`DG.MoritaCounterexample.not_exists_d_eq_one`), so `D(A) ≠ 0`.

Hence there is no equivalence `D(e A e) ≌ D(A)`
(`DG.MoritaCounterexample.isEmpty_derivedEquivalence`), and in particular `e` is not full up to
homotopy (`DG.MoritaCounterexample.not_isFullH0`). Over a field `k`, `A` is the matrix algebra
`M₃(k)` with the grading and differential of `END_k(k x ⊕ k y ⊕ k z)`, `|y| = -1`, `d y = x`.
-/

open CategoryTheory DirectSum

universe w₁ w₂ u

namespace DG

namespace MoritaCounterexample

variable (R : Type u) [CommRing R]

/-- `R` concentrated in degree `0` (local instance). -/
local instance instDGAddCommGroupGround : DGAddCommGroup R := DGAddCommGroup.degreeZero R

/-- `R` concentrated in degree `0`, as a dg ring (local instance). -/
local instance instDGRingGround : DGRing R := DGRing.degreeZero R

/-- The contractible complex `K = cone(id_R)`: `R` in degrees `-1` and `0`, with `d = id`. -/
abbrev K : Type u := Cone (DGModuleHom.id : R →ᵈᵍ[R] R)

/-- The complex `V = K ⊕ R` (with `R` in degree `0`). -/
abbrev V : Type u := K R × R

/-- The dg ring `A = END_R(V)`. -/
abbrev A : Type u := DGModule.END R (V R)

/-- The projection of `V` onto `K`, a chain map. -/
def p : V R →ᵈᵍ[R] V R := (DGModuleHom.inl (K R) R).comp (DGModuleHom.fst (K R) R)

@[simp] theorem p_apply (v : V R) : p R v = (v.1, 0) := rfl

/-- The idempotent `e ∈ Z⁰(A)`: the projection onto the contractible summand `K`. -/
noncomputable def e : DGIdempotent (A R) where
  val := DirectSum.of _ 0 (Cochain.ofHom (p R))
  mem_zero := of_mem_summand _ _
  mul_self := by
    rw [DGModule.END.of_mul_of]
    exact DGModule.HOM.of_congr (add_zero 0) fun v => by
      rw [Cochain.units_smul_apply, mul_zero, koszulSign_zero, one_smul]
      rfl
  d_eq_zero := by
    rw [DGModule.HOM.d_of, δ_ofHom]
    exact map_zero _

theorem e_val : (e R).val = DirectSum.of _ 0 (Cochain.ofHom (p R)) := rfl

/-- The chain map `V → V`, `(k, r) ↦ ((0, r), 0)`, onto the degree-`0` part of `K`. -/
def f : V R →ᵈᵍ[R] V R :=
  (DGModuleHom.inl (K R) R).comp ((Cone.inr _).comp (DGModuleHom.snd (K R) R))

@[simp] theorem f_apply (v : V R) : f R v = (Cone.inr _ v.2, 0) := rfl

/-- The (non-closed) degree-`0` map `V → V`, `((x, y), r) ↦ (0, y)`. -/
def g : Cochain R (V R) (V R) 0 :=
  Cochain.ofHoms ((LinearMap.inr R (K R) R).comp ((Cone.sndLinear _).comp
      (LinearMap.fst R (K R) R)))
    fun hv => ⟨zero_mem _, Cone.sndLinear_mem hv.1⟩

@[simp] theorem g_apply (v : V R) : g R v = (0, Cone.sndLinear _ v.1) := rfl

/-- `1 = e + f e g` in `A`: the idempotent `e` generates `A` as a two-sided ideal. -/
theorem one_eq : (1 : A R) = (e R).val +
    DirectSum.of _ 0 (Cochain.ofHom (f R)) * (e R).val * DirectSum.of _ 0 (g R) := by
  rw [e_val, DGModule.END.of_mul_of, DGModule.END.of_mul_of, DGModule.END.one_def,
    DGModule.HOM.of_congr (show (0 : ℤ) + 0 + 0 = 0 by simp)
      (g := (g R).comp ((Cochain.ofHom (p R)).comp (Cochain.ofHom (f R)) (add_zero 0)) (add_zero 0))
      (fun v => by simp [Cochain.comp_apply]), ← map_add]
  refine DGModule.HOM.of_congr rfl fun v => ?_
  obtain ⟨c, r⟩ := v
  simp only [Cochain.id_apply, Cochain.add_apply, Cochain.comp_apply, Cochain.ofHom_apply,
    p_apply, f_apply, g_apply]
  refine Prod.ext ?_ ?_
  · change c = c + 0
    rw [add_zero]
  · change r = 0 + Cone.sndLinear _ (Cone.inr _ r)
    rw [zero_add]
    rfl

/-- `A e A = A`. -/
theorem one_mem_span : (1 : A R) ∈ TwoSidedIdeal.span {(e R).val} := by
  rw [one_eq]
  refine TwoSidedIdeal.add_mem _ (TwoSidedIdeal.subset_span rfl) ?_
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span rfl))

/-- The contracting homotopy of `K`, extended by `0` on `R`: a cochain of degree `-1` on `V`. -/
def h : Cochain R (V R) (V R) (-1) where
  toFun v := (Cone.contraction R v.1, 0)
  map_zero' := by simp
  map_add' v w := by simp
  map_mem' i v hv := ⟨by simpa [sub_eq_add_neg] using Cone.contraction_mem hv.1, zero_mem _⟩
  map_smul' {i r} hr v := by
    refine Prod.ext ?_ ?_
    · change Cone.contraction R (r • v.1) = _
      rw [Cone.contraction_smul hr, neg_one_mul, koszulSign, koszulSign, Int.negOnePow_neg]
      rfl
    · change (0 : R) = _
      simp

@[simp] theorem h_apply (v : V R) : h R v = (Cone.contraction R v.1, 0) := rfl

theorem h_mem_corner :
    (DirectSum.of _ (-1) (h R) : A R) ∈ Subsemigroup.corner (e R).val := by
  refine (DGIdempotent.Corner.mem_iff (e R)).mpr ⟨?_, ?_⟩
  · rw [e_val, DGModule.END.of_mul_of]
    exact DGModule.HOM.of_congr (zero_add _) fun v => by
      rw [Cochain.units_smul_apply, zero_mul, koszulSign_zero, one_smul]
      rfl
  · rw [e_val, DGModule.END.of_mul_of]
    exact DGModule.HOM.of_congr (add_zero _) fun v => by
      rw [Cochain.units_smul_apply, mul_zero, koszulSign_zero, one_smul]
      rfl

/-- The contracting homotopy as an element of `e A e`. -/
def hCorner : (e R).Corner := ⟨DirectSum.of _ (-1) (h R), h_mem_corner R⟩

/-- `e A e` is acyclic: `d h = 1` in `e A e`. -/
theorem d_hCorner : d (hCorner R) = 1 := by
  apply DGIdempotent.Corner.ext
  rw [DGIdempotent.Corner.coe_d, DGIdempotent.Corner.coe_one, e_val]
  change d (DirectSum.of _ (-1) (h R) : A R) = _
  rw [DGModule.HOM.d_of]
  refine DGModule.HOM.of_congr (by norm_num) fun v => ?_
  rw [δ_apply _ _ rfl, Cochain.ofHom_apply, p_apply, h_apply, h_apply]
  refine Prod.ext ?_ ?_
  · change d (Cone.contraction R v.1) - koszulSign (-1) • Cone.contraction R (d v.1) = v.1
    rw [koszulSign, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      sub_neg_eq_add]
    exact Cone.d_contraction_add_contraction_d v.1
  · change d (0 : R) - _ = 0
    simp

/-- `A` is not acyclic: there is no `x ∈ A` with `d x = 1`. Indeed `d x = 1` would give a cochain
`z` of degree `-1` with `d ∘ z + z ∘ d = id`, and evaluating at `(0, 1) ∈ K ⊕ R` gives
`(0, 1) = d (z (0, 1))`, whose second component is `0`. -/
theorem not_exists_d_eq_one [Nontrivial R] : ¬ ∃ x : A R, d x = 1 := by
  rintro ⟨x, hx⟩
  have h1 : d (decompose (grading (M := A R)) x (-1) : A R) = 1 := by
    have h := decompose_d x (-1)
    rw [hx, show (-1 : ℤ) + 1 = 0 by norm_num,
      decompose_of_mem_same _ (one_mem_grading (A := A R))] at h
    exact h.symm
  obtain ⟨z, hz⟩ := mem_summand.mp (decompose (grading (M := A R)) x (-1)).2
  rw [← hz, DGModule.HOM.d_of, DGModule.END.one_def] at h1
  rw [DGModule.HOM.of_congr (show (-1 : ℤ) + 1 = 0 by norm_num) (g := δ (-1) 0 z)
    (fun v => by rw [δ_apply _ _ rfl, δ_apply _ _ (by norm_num)])] at h1
  have h2 : δ (-1) 0 z = Cochain.id R (V R) := DirectSum.of_injective (β := fun n =>
    Cochain R (V R) (V R) n) 0 h1
  have h4 := congrArg (fun v : V R => v.2) (Cochain.ext_iff.mp h2 (0, 1))
  have hd : d ((0, 1) : V R) = 0 := Prod.ext (d_zero (M := K R)) rfl
  simp only [δ_apply _ _ (show (-1 : ℤ) + 1 = 0 by norm_num), hd, map_zero, smul_zero,
    sub_zero] at h4
  have h5 : d ((z (0, 1)).2) = (0 : R) := rfl
  exact zero_ne_one (h5.symm.trans h4)

/-- **Counterexample to the literal statement of Roadmap 7.3.** For `A = END_R(K ⊕ R)` and the
projection `e` onto the contractible summand `K`, `A e A = A` (`one_mem_span`), but `D(e A e)` and
`D(A)` are not equivalent: `D(e A e) = 0` since `e A e` is acyclic (`d_hCorner`), while `D(A) ≠ 0`
since `A` is not (`not_exists_d_eq_one`). -/
theorem isEmpty_derivedEquivalence [Nontrivial R]
    [DG.HasDerivedCategory.{w₁, u} (e R).Corner] [DG.HasDerivedCategory.{w₂, u} (A R)] :
    IsEmpty (DG.DerivedCategory (e R).Corner ≌ DG.DerivedCategory (A R)) := by
  refine ⟨fun E => ?_⟩
  have hex : ∃ x : (e R).Corner, d x = 1 := ⟨hCorner R, d_hCorner R⟩
  have hC : ∀ X : DG.DerivedCategory (e R).Corner, Limits.IsZero X :=
    ((DG.DerivedCategory.tfae_isZero (A := (e R).Corner)).out 1 3).mpr hex
  refine not_exists_d_eq_one R (((DG.DerivedCategory.tfae_isZero (A := A R)).out 1 3).mp
    fun Y => ?_)
  exact Limits.IsZero.of_iso (Functor.map_isZero E.functor (hC _)) (E.counitIso.app Y).symm

/-- In particular `e` is not full up to homotopy, although `A e A = A`. -/
theorem not_isFullH0 [Nontrivial R] : ¬ (e R).IsFullH0 := fun he =>
  letI := DG.HasDerivedCategory.standard (e R).Corner
  letI := DG.HasDerivedCategory.standard (A R)
  (isEmpty_derivedEquivalence R).false ((e R).moritaEquivalence.{u} he)

end MoritaCounterexample

end DG
