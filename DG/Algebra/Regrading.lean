import DG.Graded.RegradingModuleCat
import DG.Module.Basic

/-!
# Regrading dg objects

The regrading constructions of `DG.Graded.Regrading`, with differentials.

## `ℤ/2`-graded dg rings and modules

* `DG.IsOddDifferential ℳ d`, `DG.IsZMod2DGRing 𝒜 d`, `DG.IsZMod2DGModule 𝒜 dA ℳ dM`: a
  `ℤ/2`-graded dg ring is a `ℤ/2`-graded ring with an odd differential `d`, `d ∘ d = 0`,
  satisfying `d (a * b) = d a * b + (-1)^{|a|} • (a * d b)` with `|a| ∈ ℤ/2`; similarly for
  modules. The sign is written `koszulSign n` for an integer `n` of parity `|a|`
  (`DG.koszulSign_congr`). These are hypotheses on data used as input of the constructions, not a
  second core: the dg objects of the library are the `ℤ`-graded ones.
* `DG.Periodize.dgAddCommGroup`, `DG.Periodize.dgRing`, `DG.Periodize.dgModule`: the
  periodization of a `ℤ/2`-graded dg ring (module), with the differential acting componentwise
  (`m` in degree `n` goes to `d m` in degree `n + 1`), is a dg ring (dg module) in the sense of
  `DG.DGRing` (`DG.DGModule`).
* `DG.IsPeriodicDGModule hA 𝒩 dN`: a dg module over the periodization of a `ℤ/2`-graded dg ring,
  stated on data; it is equivalent to `DG.DGModule` for the dg ring `DG.Periodize.dgRing`
  (`DG.IsPeriodicDGModule.dgModule`, `DG.IsPeriodicDGModule.of_dgModule`).

The equivalence of the categories of dg modules is `DG.GradedModuleCat.periodizeDGEquivalence`
(`DG.Algebra.RegradingModuleCat`).

## Differentials of degree `k`

* `DG.IsDifferentialOfDegree ℳ k d`: `d (Mⁿ) ⊆ Mⁿ⁺ᵏ`, `d ∘ d = 0`. It induces a differential of
  degree `1` on each regrading `RegradeByDivision ℳ k r = ⨁ q, ℳ (q * k + r)`
  (`DG.RegradeByDivision.dgAddCommGroup`), and the residue decomposition
  `M ≃+ ⨁ r : ZMod k, RegradeByDivision ℳ k r` intertwines `d` with the direct sum of the induced
  differentials (`DG.residueEquiv_d`).
* `DG.IsDivDGRing 𝒜 k d`, `DG.IsDivDGModule 𝒜 k dA ℳ dM`: the Leibniz rule with the sign
  `(-1)^{|a| / k}` of the regraded degree, for `a` of degree divisible by `k` (no condition on the
  other elements). Then `⨁ q, A^{q k}` is a dg ring (`DG.RegradeByDivision.dgRing`) and each
  residue class `⨁ q, ℳ (q * k + r)` is a dg module over it (`DG.RegradeByDivision.dgModule`).
  The sign `(-1)^{|a|}` of the original degree would not do for even `k`: it is `1` on `A^{q k}`,
  whereas the Leibniz rule of `DG.DGRing` in degree `q` has the sign `(-1)^q`.
-/

noncomputable section

namespace DG

open DirectSum

/-- The Koszul sign only depends on the parity. -/
theorem koszulSign_congr {m n : ℤ} (h : (m : ZMod 2) = n) : koszulSign m = koszulSign n := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub m n 2).mp h
  have hn : n = m + 2 * c := by push_cast at hc; omega
  rw [hn, koszulSign_add, koszulSign_even (n := 2 * c) ⟨c, by ring⟩, mul_one]

section ZMod2

variable {M σ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]

/-- An odd differential on a `ℤ/2`-graded abelian group `M = M^{0̄} ⊕ M^{1̄}`: an additive map
`d` with `d (M^{i}) ⊆ M^{i + 1}` and `d ∘ d = 0`. -/
structure IsOddDifferential (ℳ : ZMod 2 → σ) (d : M →+ M) : Prop where
  map_mem : ∀ {i : ZMod 2} {m : M}, m ∈ ℳ i → d m ∈ ℳ (i + 1)
  d_d : ∀ m, d (d m) = 0

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A]

/-- A `ℤ/2`-graded dg ring structure: an odd differential `d` on a `ℤ/2`-graded ring `A`
satisfying the graded Leibniz rule `d (a * b) = d a * b + (-1)^{|a|} • (a * d b)` for `a`
homogeneous of parity `|a|`. The sign is written `koszulSign n` for any integer `n` of parity
`|a|` (it only depends on `n mod 2`, `DG.koszulSign_congr`). -/
structure IsZMod2DGRing (𝒜 : ZMod 2 → τ) (d : A →+ A) : Prop extends IsOddDifferential 𝒜 d where
  d_mul : ∀ {n : ℤ} {a : A}, a ∈ 𝒜 n → ∀ b : A, d (a * b) = d a * b + koszulSign n • (a * d b)

/-- A `ℤ/2`-graded dg module structure over a `ℤ/2`-graded dg ring `(A, 𝒜, dA)`: an odd
differential `dM` on a `ℤ/2`-graded `A`-module `M` with the signed Leibniz rule
`dM (a • m) = dA a • m + (-1)^{|a|} • (a • dM m)`. -/
structure IsZMod2DGModule [Module A M] (𝒜 : ZMod 2 → τ) (dA : A →+ A) (ℳ : ZMod 2 → σ)
    (dM : M →+ M) : Prop extends IsOddDifferential ℳ dM where
  d_smul : ∀ {n : ℤ} {a : A}, a ∈ 𝒜 n → ∀ m : M,
    dM (a • m) = dA a • m + koszulSign n • (a • dM m)

end ZMod2

namespace Periodize

section Differential

variable {M σ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M] {ℳ : ZMod 2 → σ}

theorem mk_zsmul (n : ℤ) (z : ℤ) {m : M} (hm : m ∈ ℳ n) :
    mk ℳ n (z • m) (zsmul_mem hm z) = z • mk ℳ n m hm :=
  map_zsmul (ofHom ℳ n) z ⟨m, hm⟩

theorem mk_units_smul (n : ℤ) (z : ℤˣ) {m : M} (hm : m ∈ ℳ n) :
    mk ℳ n (z • m) (by rw [Units.smul_def]; exact zsmul_mem hm _) = z • mk ℳ n m hm :=
  (mk_congr rfl (Units.smul_def z m) _ (zsmul_mem hm _)).trans
    ((mk_zsmul n (z : ℤ) hm).trans (Units.smul_def z _).symm)

theorem mk_eq_add {n n₁ n₂ : ℤ} (h₁ : n₁ = n) (h₂ : n₂ = n) {m m₁ m₂ : M} (h : m = m₁ + m₂)
    (hm : m ∈ ℳ n) (hm₁ : m₁ ∈ ℳ n₁) (hm₂ : m₂ ∈ ℳ n₂) :
    mk ℳ n m hm = mk ℳ n₁ m₁ hm₁ + mk ℳ n₂ m₂ hm₂ := by
  subst h₁ h₂ h; exact mk_add _ _ _

variable (ℳ) {d : M →+ M}

/-- The differential of `Periodize ℳ` induced by an odd differential `d` on `ℳ`: it sends `m`
placed in degree `n` to `d m` placed in degree `n + 1`. -/
def dHom (hd : IsOddDifferential ℳ d) : Periodize ℳ →+ Periodize ℳ :=
  DirectSum.toAddMonoid fun n =>
    (ofHom ℳ (n + 1)).comp
      ((d.comp (AddSubmonoidClass.subtype (periodicGrading ℳ n))).codRestrict _ fun m => by
        rw [mem_periodicGrading, Int.cast_add, Int.cast_one]; exact hd.map_mem m.2)

variable {ℳ}

theorem dHom_mk (hd : IsOddDifferential ℳ d) (n : ℤ) (m : M) (hm : m ∈ ℳ n) :
    dHom ℳ hd (mk ℳ n m hm) =
      mk ℳ (n + 1) (d m) (by rw [Int.cast_add, Int.cast_one]; exact hd.map_mem hm) :=
  DirectSum.toAddMonoid_of (β := fun n => ↥(periodicGrading ℳ n)) _ n ⟨m, hm⟩

theorem dHom_dHom (hd : IsOddDifferential ℳ d) (x : Periodize ℳ) :
    dHom ℳ hd (dHom ℳ hd x) = 0 := by
  induction x using induction_on with
  | zero => simp
  | mk n m hm =>
    rw [dHom_mk, dHom_mk]
    exact (mk_congr rfl (hd.d_d m) _ (zero_mem _)).trans (mk_zero _)
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

variable (ℳ)

/-- The periodization of a `ℤ/2`-graded abelian group with an odd differential, as a dg abelian
group: `Periodize ℳ` with its `ℤ`-grading and the differential `DG.Periodize.dHom`. Not an
instance, since it depends on the choice of `d`. -/
def dgAddCommGroup (hd : IsOddDifferential ℳ d) : DGAddCommGroup (Periodize ℳ) where
  grading := periodizeGrading ℳ
  d := dHom ℳ hd
  d_mem' := by
    intro n x hx
    obtain ⟨m, hm, rfl⟩ := mem_periodizeGrading_iff.mp hx
    rw [dHom_mk]; exact mk_mem _ _
  d_d' := dHom_dHom hd

end Differential

section Ring

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A] {𝒜 : ZMod 2 → τ}
  [SetLike.GradedMonoid 𝒜] {d : A →+ A}

/-- **Periodization of a `ℤ/2`-graded dg ring.** The periodization `Periodize 𝒜` of a
`ℤ/2`-graded dg ring, with the differential acting componentwise, is a dg ring. -/
theorem dgRing (hd : IsZMod2DGRing 𝒜 d) :
    letI := dgAddCommGroup 𝒜 hd.toIsOddDifferential
    DGRing (Periodize 𝒜) :=
  letI := dgAddCommGroup 𝒜 hd.toIsOddDifferential
  { toGradedMonoid := inferInstanceAs (SetLike.GradedMonoid (periodizeGrading 𝒜))
    d_mul' := by
      intro n x hx y
      change dHom 𝒜 _ (x * y) = dHom 𝒜 _ x * y + koszulSign n • (x * dHom 𝒜 _ y)
      obtain ⟨a, ha, rfl⟩ := mem_periodizeGrading_iff.mp hx
      induction y using induction_on with
      | zero => simp
      | mk m b hb =>
        rw [mk_mul_mk, dHom_mk, dHom_mk, dHom_mk, mk_mul_mk, mk_mul_mk, ← mk_units_smul]
        exact mk_eq_add (by ring) (by ring) (hd.d_mul ha b) _ _ _
      | add y y' hy hy' =>
        rw [mul_add, map_add, hy, hy', map_add, mul_add, mul_add, smul_add]
        abel }

end Ring

end Periodize

/-! ### Dg modules over the periodization -/

section PeriodicDGModule

variable {B τ : Type*} [Ring B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ZMod 2 → τ}
  [SetLike.GradedMonoid ℬ] {dA : B →+ B}

omit [AddSubgroupClass τ B] in
theorem IsZMod2DGRing.d_one (hA : IsZMod2DGRing ℬ dA) : dA 1 = 0 := by
  have h := hA.d_mul (n := 0) (by simpa using SetLike.GradedOne.one_mem (A := ℬ)) 1
  rw [mul_one, one_mul, koszulSign, Int.negOnePow_zero, one_smul] at h
  simpa using h

theorem even_of_cast_eq_zero {k : ℤ} (hk : (k : ZMod 2) = 0) : Even k :=
  even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd k 2).mp hk)

namespace Periodize

theorem dHom_evenOne (hA : IsZMod2DGRing ℬ dA) (k : ℤ) (hk : (k : ZMod 2) = 0) :
    dHom ℬ hA.toIsOddDifferential (evenOne ℬ k hk) = 0 := by
  rw [evenOne, dHom_mk]; exact (mk_congr rfl hA.d_one _ (zero_mem _)).trans (mk_zero _)

end Periodize

variable {N : Type*} [AddCommGroup N] [Module (Periodize ℬ) N]

/-- A dg module structure on a `ℤ`-graded module `N` over the periodization of a `ℤ/2`-graded dg
ring `(B, ℬ, dA)`: a differential `dN` of degree `1` with the signed Leibniz rule for the
differential `DG.Periodize.dHom` of `Periodize ℬ`. This is `DG.DGModule` for the dg ring
structure `DG.Periodize.dgAddCommGroup` (`DG.IsPeriodicDGModule.dgModule`,
`DG.IsPeriodicDGModule.of_dgModule`). -/
structure IsPeriodicDGModule (hA : IsZMod2DGRing ℬ dA) (𝒩 : ℤ → AddSubgroup N) (dN : N →+ N) :
    Prop where
  map_mem : ∀ {n : ℤ} {x : N}, x ∈ 𝒩 n → dN x ∈ 𝒩 (n + 1)
  d_d : ∀ x, dN (dN x) = 0
  d_smul : ∀ {n : ℤ} {p : Periodize ℬ}, p ∈ periodizeGrading ℬ n → ∀ x : N,
    dN (p • x) = Periodize.dHom ℬ hA.toIsOddDifferential p • x + koszulSign n • (p • dN x)

namespace IsPeriodicDGModule

variable {hA : IsZMod2DGRing ℬ dA} {𝒩 : ℤ → AddSubgroup N} {dN : N →+ N}

/-- The dg abelian group structure on `N` given by its grading and `dN`. -/
def dgAddCommGroup (hN : IsPeriodicDGModule hA 𝒩 dN) [Decomposition 𝒩] : DGAddCommGroup N where
  grading := 𝒩
  d := dN
  d_mem' := hN.map_mem
  d_d' := hN.d_d

theorem dgModule (hN : IsPeriodicDGModule hA 𝒩 dN) [Decomposition 𝒩]
    [SetLike.GradedSMul (periodizeGrading ℬ) 𝒩] :
    letI := Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential
    letI := hN.dgAddCommGroup
    DGModule (Periodize ℬ) N :=
  letI := Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential
  letI := hN.dgAddCommGroup
  { toGradedSMul := inferInstanceAs (SetLike.GradedSMul (periodizeGrading ℬ) 𝒩)
    d_smul' := fun hp x => hN.d_smul hp x }

theorem of_dgModule [Decomposition 𝒩] (hd : ∀ {n : ℤ} {x : N}, x ∈ 𝒩 n → dN x ∈ 𝒩 (n + 1))
    (hdd : ∀ x, dN (dN x) = 0)
    (h : letI := Periodize.dgAddCommGroup ℬ hA.toIsOddDifferential
      letI : DGAddCommGroup N := ⟨𝒩, dN, hd, hdd⟩
      DGModule (Periodize ℬ) N) : IsPeriodicDGModule hA 𝒩 dN where
  map_mem := hd
  d_d := hdd
  d_smul := fun hp x => @DGModule.d_smul' _ _ _ _ _ _ _ h _ _ hp x

theorem d_evenOne_smul (hN : IsPeriodicDGModule hA 𝒩 dN) (k : ℤ) (hk : (k : ZMod 2) = 0) (x : N) :
    dN (Periodize.evenOne ℬ k hk • x) = Periodize.evenOne ℬ k hk • dN x := by
  have hp : Periodize.evenOne ℬ k hk ∈ periodizeGrading ℬ k := Periodize.mk_mem k _
  rw [hN.d_smul hp x, Periodize.dHom_evenOne hA, zero_smul, zero_add,
    koszulSign_even (even_of_cast_eq_zero hk), one_smul]

end IsPeriodicDGModule

namespace Periodize

variable {M σ : Type*} [AddCommGroup M] [Module B M] [SetLike σ M] [AddSubgroupClass σ M]
  {ℳ : ZMod 2 → σ} [SetLike.GradedSMul ℬ ℳ] {dM : M →+ M}

/-- The periodization of a `ℤ/2`-graded dg module is a dg module over the periodization. -/
theorem isPeriodicDGModule (hA : IsZMod2DGRing ℬ dA) (hM : IsZMod2DGModule ℬ dA ℳ dM) :
    IsPeriodicDGModule hA (periodizeGrading ℳ) (dHom ℳ hM.toIsOddDifferential) where
  map_mem := by
    intro n x hx
    obtain ⟨m, hm, rfl⟩ := mem_periodizeGrading_iff.mp hx
    rw [dHom_mk]; exact mk_mem _ _
  d_d := dHom_dHom _
  d_smul := by
    intro n x hx y
    obtain ⟨a, ha, rfl⟩ := mem_periodizeGrading_iff.mp hx
    induction y using induction_on with
    | zero => simp
    | mk m b hb =>
      rw [mk_smul_mk, dHom_mk, dHom_mk, dHom_mk, mk_smul_mk, mk_smul_mk, ← mk_units_smul]
      exact mk_eq_add (by ring) (by ring) (hM.d_smul ha b) _ _ _
    | add y y' hy hy' =>
      rw [smul_add, map_add, hy, hy', map_add, smul_add, smul_add, smul_add]
      abel

end Periodize

namespace Periodize

variable {M σ : Type*} [AddCommGroup M] [Module B M] [SetLike σ M] [AddSubgroupClass σ M]
  {ℳ : ZMod 2 → σ} [SetLike.GradedSMul ℬ ℳ] {dM : M →+ M}

/-- **Periodization of a `ℤ/2`-graded dg module.** The periodization of a `ℤ/2`-graded dg module
over a `ℤ/2`-graded dg ring `B` is a dg module over the periodization of `B`. -/
theorem dgModule (hA : IsZMod2DGRing ℬ dA) (hM : IsZMod2DGModule ℬ dA ℳ dM) :
    letI := dgAddCommGroup ℬ hA.toIsOddDifferential
    letI := dgAddCommGroup ℳ hM.toIsOddDifferential
    DGModule (Periodize ℬ) (Periodize ℳ) :=
  (isPeriodicDGModule hA hM).dgModule

end Periodize

end PeriodicDGModule

/-! ### Differentials of degree `k` -/

section Division

variable {M σ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]

/-- A differential of degree `k` on a `ℤ`-graded abelian group: an additive map `d` with
`d (Mⁿ) ⊆ Mⁿ⁺ᵏ` and `d ∘ d = 0`. -/
structure IsDifferentialOfDegree (ℳ : ℤ → σ) (k : ℤ) (d : M →+ M) : Prop where
  map_mem : ∀ {n : ℤ} {m : M}, m ∈ ℳ n → d m ∈ ℳ (n + k)
  d_d : ∀ m, d (d m) = 0

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A]

/-- A differential `d` of degree `k` on a `ℤ`-graded ring `A` satisfying the Leibniz rule
`d (a * b) = d a * b + (-1)^q • (a * d b)` for `a` homogeneous of degree `q * k`, i.e. with the
sign `(-1)^{|a| / k}` of the *regraded* degree. No condition is imposed on elements of degree
not divisible by `k`. This is exactly what makes the residue-`0` part `⨁ q, A^{q k}` a dg ring
(`DG.RegradeByDivision.dgRing`). -/
structure IsDivDGRing (𝒜 : ℤ → τ) (k : ℤ) (d : A →+ A) : Prop
    extends IsDifferentialOfDegree 𝒜 k d where
  d_mul : ∀ {q : ℤ} {a : A}, a ∈ 𝒜 (q * k) → ∀ b : A,
    d (a * b) = d a * b + koszulSign q • (a * d b)

/-- A differential `dM` of degree `k` on a `ℤ`-graded module `M` over a `ℤ`-graded ring
`(A, 𝒜, dA)`, satisfying `dM (a • m) = dA a • m + (-1)^q • (a • dM m)` for `a` homogeneous of
degree `q * k`. -/
structure IsDivDGModule [Module A M] (𝒜 : ℤ → τ) (k : ℤ) (dA : A →+ A) (ℳ : ℤ → σ)
    (dM : M →+ M) : Prop extends IsDifferentialOfDegree ℳ k dM where
  d_smul : ∀ {q : ℤ} {a : A}, a ∈ 𝒜 (q * k) → ∀ m : M,
    dM (a • m) = dA a • m + koszulSign q • (a • dM m)

namespace RegradeByDivision

variable {ℳ : ℤ → σ} {k r : ℤ} {d : M →+ M}

theorem mk_zsmul (q : ℤ) (z : ℤ) {m : M} (hm : m ∈ ℳ (q * k + r)) :
    mk ℳ k r q (z • m) (zsmul_mem hm z) = z • mk ℳ k r q m hm :=
  map_zsmul (DirectSum.of (fun q => ↥(divGrading ℳ k r q)) q) z ⟨m, hm⟩

theorem mk_units_smul (q : ℤ) (z : ℤˣ) {m : M} (hm : m ∈ ℳ (q * k + r)) :
    mk ℳ k r q (z • m) (by rw [Units.smul_def]; exact zsmul_mem hm _) = z • mk ℳ k r q m hm :=
  (mk_congr rfl (Units.smul_def z m) _ (zsmul_mem hm _)).trans
    ((mk_zsmul q (z : ℤ) hm).trans (Units.smul_def z _).symm)

theorem mk_eq_add {q q₁ q₂ : ℤ} (h₁ : q₁ = q) (h₂ : q₂ = q) {m m₁ m₂ : M} (h : m = m₁ + m₂)
    (hm : m ∈ ℳ (q * k + r)) (hm₁ : m₁ ∈ ℳ (q₁ * k + r)) (hm₂ : m₂ ∈ ℳ (q₂ * k + r)) :
    mk ℳ k r q m hm = mk ℳ k r q₁ m₁ hm₁ + mk ℳ k r q₂ m₂ hm₂ := by
  subst h₁ h₂ h; exact mk_add _ _ _

omit [AddSubgroupClass σ M] in
theorem map_mem_succ (hd : IsDifferentialOfDegree ℳ k d) {q : ℤ} {m : M} (hm : m ∈ ℳ (q * k + r)) :
    d m ∈ ℳ ((q + 1) * k + r) := by
  have := hd.map_mem hm
  rwa [show q * k + r + k = (q + 1) * k + r by ring] at this

variable (ℳ k r)

/-- The differential of degree `1` on `RegradeByDivision ℳ k r` induced by a differential of
degree `k` on `ℳ`: it sends `m ∈ ℳ (q * k + r)`, placed in degree `q`, to
`d m ∈ ℳ ((q + 1) * k + r)`, placed in degree `q + 1`. -/
def dHom (hd : IsDifferentialOfDegree ℳ k d) : RegradeByDivision ℳ k r →+ RegradeByDivision ℳ k r :=
  DirectSum.toAddMonoid fun q =>
    (DirectSum.of (fun q => ↥(divGrading ℳ k r q)) (q + 1)).comp
      ((d.comp (AddSubmonoidClass.subtype (divGrading ℳ k r q))).codRestrict _ fun m =>
        map_mem_succ hd m.2)

variable {ℳ k r}

theorem dHom_mk (hd : IsDifferentialOfDegree ℳ k d) (q : ℤ) (m : M) (hm : m ∈ ℳ (q * k + r)) :
    dHom ℳ k r hd (mk ℳ k r q m hm) = mk ℳ k r (q + 1) (d m) (map_mem_succ hd hm) :=
  DirectSum.toAddMonoid_of (β := fun q => ↥(divGrading ℳ k r q)) _ q ⟨m, hm⟩

theorem dHom_dHom (hd : IsDifferentialOfDegree ℳ k d) (x : RegradeByDivision ℳ k r) :
    dHom ℳ k r hd (dHom ℳ k r hd x) = 0 := by
  induction x using induction_on with
  | zero => simp
  | mk q m hm =>
    rw [dHom_mk, dHom_mk]
    exact (mk_congr rfl (hd.d_d m) _ (zero_mem _)).trans (mk_zero _)
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

variable (ℳ k r)

/-- `RegradeByDivision ℳ k r` as a dg abelian group, for a differential of degree `k` on `ℳ`.
Not an instance, since it depends on the choice of `d`. -/
def dgAddCommGroup (hd : IsDifferentialOfDegree ℳ k d) :
    DGAddCommGroup (RegradeByDivision ℳ k r) where
  grading := regradeGrading ℳ k r
  d := dHom ℳ k r hd
  d_mem' := by
    intro q x hx
    obtain ⟨m, hm, rfl⟩ := mem_regradeGrading_iff.mp hx
    rw [dHom_mk]; exact mk_mem _ _
  d_d' := dHom_dHom hd

end RegradeByDivision

section Residue

variable (ℳ : ℤ → σ) [Decomposition ℳ] (k : ℕ) [NeZero k] {d : M →+ M}

/-- **The residue decomposition is compatible with differentials.** Under
`DG.residueEquiv ℳ k : M ≃+ ⨁ r : ZMod k, RegradeByDivision ℳ k r`, a differential of degree `k`
on `M` corresponds to the direct sum of the induced differentials of degree `1`. -/
theorem residueEquiv_d (hd : IsDifferentialOfDegree ℳ k d) (m : M) :
    residueEquiv ℳ k (d m) =
      DirectSum.map (fun r : ZMod k => RegradeByDivision.dHom ℳ k (r.val : ℤ) hd)
        (residueEquiv ℳ k m) := by
  induction m using Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous m =>
    obtain ⟨m, hm⟩ := m
    rename_i n
    rw [residueEquiv_of_mem ℳ k (hd.map_mem hm), residueEquiv_of_mem ℳ k hm, DirectSum.map_of,
      RegradeByDivision.dHom_mk]
    have hk : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne k)
    exact of_mk_congr (by rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero])
      (by rw [show n + (k : ℤ) = n + 1 * k by ring, Int.add_mul_ediv_right _ _ hk])
      _ _
  | add m m' hm hm' => rw [map_add, map_add, hm, hm', map_add, map_add]

end Residue

namespace RegradeByDivision

section Ring

variable {𝒜 : ℤ → τ} [SetLike.GradedMonoid 𝒜] {k : ℤ} {d : A →+ A}

omit [Ring A] [AddSubgroupClass τ A] [SetLike.GradedMonoid 𝒜] in
theorem mem_of_mem_mul_add_zero {q : ℤ} {a : A} (ha : a ∈ 𝒜 (q * k + 0)) : a ∈ 𝒜 (q * k) := by
  rwa [add_zero] at ha

/-- **The residue-`0` part is a dg ring.** For a differential `d` of degree `k` on a `ℤ`-graded
ring `A` satisfying the Leibniz rule with the sign `(-1)^{|a| / k}` on elements of degree
divisible by `k`, `⨁ q, A^{q k}` is a dg ring for the induced differential of degree `1`. -/
theorem dgRing (hd : IsDivDGRing 𝒜 k d) :
    letI := dgAddCommGroup 𝒜 k 0 hd.toIsDifferentialOfDegree
    DGRing (RegradeByDivision 𝒜 k 0) :=
  letI := dgAddCommGroup 𝒜 k 0 hd.toIsDifferentialOfDegree
  { toGradedMonoid := inferInstanceAs (SetLike.GradedMonoid (regradeGrading 𝒜 k 0))
    d_mul' := by
      intro q x hx y
      change dHom 𝒜 k 0 _ (x * y) = dHom 𝒜 k 0 _ x * y + koszulSign q • (x * dHom 𝒜 k 0 _ y)
      obtain ⟨a, ha, rfl⟩ := mem_regradeGrading_iff.mp hx
      induction y using induction_on with
      | zero => simp
      | mk p b hb =>
        rw [mk_mul_mk, dHom_mk, dHom_mk, dHom_mk, mk_mul_mk, mk_mul_mk, ← mk_units_smul]
        exact mk_eq_add (by ring) (by ring) (hd.d_mul (mem_of_mem_mul_add_zero ha) b) _ _ _
      | add y y' hy hy' =>
        rw [mul_add, map_add, hy, hy', map_add, mul_add, mul_add, smul_add]
        abel }

end Ring

section Module

variable {𝒜 : ℤ → τ} [SetLike.GradedMonoid 𝒜] {k : ℤ} {dA : A →+ A}
variable [Module A M] {ℳ : ℤ → σ} [SetLike.GradedSMul 𝒜 ℳ] {dM : M →+ M}

/-- **Each residue class is a dg module.** For `ℳ` a `ℤ`-graded `A`-module with a differential of
degree `k` satisfying the Leibniz rule with the sign `(-1)^{|a| / k}` for `a` of degree divisible by
`k`, each residue class `⨁ q, ℳ (q k + r)` is a dg module over the dg ring `⨁ q, A^{q k}`. -/
theorem dgModule (hA : IsDivDGRing 𝒜 k dA) (hM : IsDivDGModule 𝒜 k dA ℳ dM) (r : ℤ) :
    letI := dgAddCommGroup 𝒜 k 0 hA.toIsDifferentialOfDegree
    letI := dgAddCommGroup ℳ k r hM.toIsDifferentialOfDegree
    DGModule (RegradeByDivision 𝒜 k 0) (RegradeByDivision ℳ k r) :=
  letI := dgAddCommGroup 𝒜 k 0 hA.toIsDifferentialOfDegree
  letI := dgAddCommGroup ℳ k r hM.toIsDifferentialOfDegree
  { toGradedSMul := inferInstanceAs
      (SetLike.GradedSMul (regradeGrading 𝒜 k 0) (regradeGrading ℳ k r))
    d_smul' := by
      intro q x hx y
      change dHom ℳ k r _ (x • y) = dHom 𝒜 k 0 _ x • y + koszulSign q • (x • dHom ℳ k r _ y)
      obtain ⟨a, ha, rfl⟩ := mem_regradeGrading_iff.mp hx
      induction y using induction_on with
      | zero => simp
      | mk p m hm =>
        rw [mk_smul_mk, dHom_mk, dHom_mk, dHom_mk, mk_smul_mk, mk_smul_mk, ← mk_units_smul]
        exact mk_eq_add (by ring) (by ring) (hM.d_smul (mem_of_mem_mul_add_zero ha) m) _ _ _
      | add y y' hy hy' =>
        rw [smul_add, map_add, hy, hy', map_add, smul_add, smul_add, smul_add]
        abel }

end Module

end RegradeByDivision

end Division

end DG
