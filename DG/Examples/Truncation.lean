import DG.Algebra.Cohomology
import DG.Algebra.Constructions

/-!
# Truncations of dg rings

Let `A` be a dg ring (cohomological grading, `d` of degree `+1`).

* The good truncation `τ^{≤ 0} A = (⋯ → A⁻² → A⁻¹ → Z⁰(A) → 0 → ⋯)`, the elements whose
  components in positive degrees vanish and whose degree-`0` component is a cocycle, is a dg
  subring of `A` (`DG.truncLEZero A`), and its inclusion induces isomorphisms `Hⁿ(τ^{≤ 0} A) ≅
  Hⁿ(A)` for `n ≤ 0` (`DG.bijective_cohomologyMap_truncLEZero`), while `Hⁿ(τ^{≤ 0} A) = 0` for
  `n > 0` (`DG.truncLEZero.subsingleton_cohomology_of_pos`).
* If `A` is concentrated in non-positive degrees (`Aⁿ = 0` for `n > 0`), the elements whose
  degree-`0` component is a coboundary, `A^{< 0} ⊕ d(A⁻¹)`, form a dg ideal
  (`DG.truncGEZeroIdeal`), and the quotient `τ^{≥ 0} A = A ⧸ (A^{< 0} ⊕ d(A⁻¹))` is
  `H⁰(A) = A⁰ / d(A⁻¹)` concentrated in degree `0` with zero differential
  (`DG.truncGEZero.eq_zero_of_mem_grading`, `DG.truncGEZero.d_eq_zero`). The projection
  `DG.truncGEZeroπ : A →ᵈᵍ+* A ⧸ truncGEZeroIdeal hA` is a morphism of dg rings inducing an
  isomorphism on `H⁰` (`DG.bijective_cohomologyMap_truncGEZeroπ`).

Both constructions use `DG.ofComponents T`, the additive subgroup of elements whose
homogeneous components of degree `n` lie in `T n`.
-/

open DirectSum

namespace DG

/-! ### Subgroups defined componentwise -/

section Components

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M]

/-- The additive subgroup of elements whose degree-`n` component lies in `T n` for every `n`. -/
def ofComponents (T : ℤ → AddSubgroup M) : AddSubgroup M where
  carrier := {a | ∀ n, (decompose (grading (M := M)) a n : M) ∈ T n}
  zero_mem' n := by
    rw [decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
    exact zero_mem _
  add_mem' {a b} ha hb n := by
    show _ ∈ T n
    rw [decompose_add, DirectSum.add_apply, AddSubgroup.coe_add]
    exact add_mem (ha n) (hb n)
  neg_mem' {a} ha n := by
    show _ ∈ T n
    rw [decompose_neg]
    exact neg_mem (ha n)

theorem mem_ofComponents {T : ℤ → AddSubgroup M} {a : M} :
    a ∈ ofComponents T ↔ ∀ n, (decompose (grading (M := M)) a n : M) ∈ T n :=
  Iff.rfl

/-- A homogeneous element of degree `k` lies in `ofComponents T` if and only if it lies in
`T k`. -/
theorem mem_ofComponents_of_mem_grading {T : ℤ → AddSubgroup M} {k : ℤ} {x : M}
    (hx : x ∈ grading k) : x ∈ ofComponents T ↔ x ∈ T k := by
  constructor
  · intro h
    have := h k
    rwa [decompose_of_mem_same _ hx] at this
  · intro h n
    by_cases hn : k = n
    · subst hn
      rw [decompose_of_mem_same _ hx]
      exact h
    · rw [decompose_of_mem_ne _ hx hn]
      exact zero_mem _

theorem isHomogeneous_ofComponents (T : ℤ → AddSubgroup M) :
    SetLike.IsHomogeneous (grading (M := M)) (ofComponents T) := by
  intro i a ha
  rw [mem_ofComponents_of_mem_grading (decompose (grading (M := M)) a i).2]
  exact ha i

end Components

/-! ### The good truncation `τ^{≤ 0}` -/

section TruncLE

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The components of the good truncation `τ^{≤ 0} A`: `0` in positive degrees, the cocycles in
degree `0`, and everything in negative degrees. -/
def truncLEZeroComponents (n : ℤ) : AddSubgroup A :=
  if 0 < n then ⊥ else if n = 0 then cocycles A 0 else ⊤

variable {A}

omit [DGRing A] in
theorem mem_truncLEZeroComponents_iff {k : ℤ} {x : A} (hx : x ∈ grading k) :
    x ∈ ofComponents (truncLEZeroComponents A) ↔ (0 < k → x = 0) ∧ (k = 0 → d x = 0) := by
  rw [mem_ofComponents_of_mem_grading hx, truncLEZeroComponents]
  by_cases h1 : 0 < k
  · simp [h1, h1.ne']
  · by_cases h2 : k = 0
    · subst h2
      simp [mem_cocycles, hx]
    · simp [h1, h2]

theorem truncLEZero_mul_mem {a b : A} (ha : a ∈ ofComponents (truncLEZeroComponents A))
    (hb : b ∈ ofComponents (truncLEZeroComponents A)) :
    a * b ∈ ofComponents (truncLEZeroComponents A) := by
  refine induction_on_of_isHomogeneous (isHomogeneous_ofComponents _)
    (P := fun a => a * b ∈ ofComponents (truncLEZeroComponents A)) (by simp [zero_mem]) ?_
    (fun a a' h h' => by simpa only [add_mul] using add_mem h h') ha
  intro i a hai haS
  refine induction_on_of_isHomogeneous (isHomogeneous_ofComponents _)
    (P := fun b => a * b ∈ ofComponents (truncLEZeroComponents A)) (by simp [zero_mem]) ?_
    (fun b b' h h' => by simpa only [mul_add] using add_mem h h') hb
  intro j b hbj hbS
  rw [mem_truncLEZeroComponents_iff hai] at haS
  rw [mem_truncLEZeroComponents_iff hbj] at hbS
  rw [mem_truncLEZeroComponents_iff (mul_mem_grading hai hbj)]
  by_cases hi : 0 < i
  · simp [haS.1 hi]
  by_cases hj : 0 < j
  · simp [hbS.1 hj]
  refine ⟨fun h => absurd h (by omega), fun h => ?_⟩
  obtain rfl : i = 0 := by omega
  obtain rfl : j = 0 := by omega
  rw [d_mul_of_mem_zero hai, haS.2 rfl, hbS.2 rfl, zero_mul, mul_zero, add_zero]

omit [DGRing A] in
theorem truncLEZero_d_mem {a : A} (ha : a ∈ ofComponents (truncLEZeroComponents A)) :
    d a ∈ ofComponents (truncLEZeroComponents A) := by
  refine induction_on_of_isHomogeneous (isHomogeneous_ofComponents _)
    (P := fun a => d a ∈ ofComponents (truncLEZeroComponents A)) (by simp [zero_mem]) ?_
    (fun a a' h h' => by simpa only [d_add] using add_mem h h') ha
  intro i a hai haS
  rw [mem_truncLEZeroComponents_iff hai] at haS
  rw [mem_truncLEZeroComponents_iff (d_mem hai)]
  refine ⟨fun h => ?_, fun _ => d_d a⟩
  by_cases hi : 0 < i
  · rw [haS.1 hi, d_zero]
  · exact haS.2 (by omega)

variable (A)

/-- The good truncation `τ^{≤ 0} A = (⋯ → A⁻¹ → Z⁰(A) → 0 → ⋯)` of a dg ring, as a dg subring:
the elements whose positive-degree components vanish and whose degree-`0` component is a
cocycle. -/
def truncLEZero : DGSubring A where
  carrier := ofComponents (truncLEZeroComponents A)
  zero_mem' := zero_mem _
  add_mem' := add_mem
  neg_mem' := neg_mem
  one_mem' := (mem_truncLEZeroComponents_iff one_mem_grading).mpr ⟨by omega, fun _ => d_one⟩
  mul_mem' := truncLEZero_mul_mem
  isHomogeneous' := isHomogeneous_ofComponents _
  d_mem' := truncLEZero_d_mem

variable {A}

theorem mem_truncLEZero_iff_of_mem_grading {k : ℤ} {x : A} (hx : x ∈ grading k) :
    x ∈ truncLEZero A ↔ (0 < k → x = 0) ∧ (k = 0 → d x = 0) :=
  mem_truncLEZeroComponents_iff hx

theorem mem_truncLEZero_of_neg {k : ℤ} {x : A} (hx : x ∈ grading k) (hk : k < 0) :
    x ∈ truncLEZero A :=
  (mem_truncLEZero_iff_of_mem_grading hx).mpr ⟨fun h => absurd h (by omega),
    fun h => absurd h (by omega)⟩

/-- The inclusion `τ^{≤ 0} A → A` induces an isomorphism `Hⁿ(τ^{≤ 0} A) ≅ Hⁿ(A)` for `n ≤ 0`. -/
theorem bijective_cohomologyMap_truncLEZero {n : ℤ} (hn : n ≤ 0) :
    Function.Bijective ((DGSubring.subtype (truncLEZero A)).cohomologyMap n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using cohomology.induction_on with
    | h z =>
    rw [DGRingHom.cohomologyMap_mk, cohomology.mk_eq_zero_iff, DGRingHom.coe_cocyclesMap,
      DGSubring.subtype_apply] at hx
    obtain ⟨a, ha, hda⟩ := hx
    rw [cohomology.mk_eq_zero_iff]
    exact ⟨⟨a, mem_truncLEZero_of_neg ha (by omega)⟩, ha, Subtype.ext hda⟩
  · intro x
    induction x using cohomology.induction_on with
    | h z =>
    have hz : (z : A) ∈ truncLEZero A :=
      (mem_truncLEZero_iff_of_mem_grading z.2.1).mpr
        ⟨fun h => absurd h (by omega), fun _ => z.2.2⟩
    refine ⟨cohomology.mk _ n ⟨⟨z, hz⟩, z.2.1, Subtype.ext z.2.2⟩, ?_⟩
    rw [DGRingHom.cohomologyMap_mk]
    rfl

/-- `Hⁿ(τ^{≤ 0} A) = 0` for `n > 0`. -/
theorem truncLEZero.subsingleton_cohomology_of_pos {n : ℤ} (hn : 0 < n) :
    Subsingleton (cohomology (truncLEZero A) n) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ x : cohomology (truncLEZero A) n, x = 0 := by
    intro x
    induction x using cohomology.induction_on with
    | h z =>
    have hz : (z : truncLEZero A) = 0 :=
      Subtype.ext (((mem_truncLEZero_iff_of_mem_grading (A := A)
        (x := ((z : truncLEZero A) : A)) z.2.1).mp (z : truncLEZero A).2).1 hn)
    have : z = 0 := Subtype.ext hz
    rw [this, map_zero]
  rw [key x, key y]

end TruncLE

/-! ### The truncation `τ^{≥ 0}` of a non-positively graded dg ring -/

section TruncGE

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  (hA : ∀ n : ℤ, 0 < n → grading (M := A) n = ⊥)

variable (A) in
/-- The components of the dg ideal `A^{< 0} ⊕ d(A⁻¹)`: the coboundaries in degree `0`, and
everything in the other degrees. -/
def truncGEZeroComponents (n : ℤ) : AddSubgroup A :=
  if n = 0 then coboundaries A 0 else ⊤

omit [DGRing A] in
theorem mem_truncGEZeroComponents_iff {k : ℤ} {x : A} (hx : x ∈ grading k) :
    x ∈ ofComponents (truncGEZeroComponents A) ↔ (k = 0 → x ∈ coboundaries A 0) := by
  rw [mem_ofComponents_of_mem_grading hx, truncGEZeroComponents]
  by_cases h : k = 0 <;> simp [h]

omit [DGRing A] in
include hA in
theorem eq_zero_of_mem_grading_of_pos {k : ℤ} {x : A} (hx : x ∈ grading k) (hk : 0 < k) :
    x = 0 := by
  rw [hA k hk] at hx
  exact hx

omit [DGRing A] in
include hA in
theorem d_eq_zero_of_mem_grading_zero {x : A} (hx : x ∈ grading 0) : d x = 0 :=
  eq_zero_of_mem_grading_of_pos hA (d_mem hx) (by norm_num)

omit [DGRing A] in
theorem truncGEZero_d_mem (a : A) : d a ∈ ofComponents (truncGEZeroComponents A) := by
  induction a using induction_on with
  | h_zero => rw [d_zero]; exact zero_mem _
  | h_add a b ha hb => rw [d_add]; exact add_mem ha hb
  | h_homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i i
    rw [mem_truncGEZeroComponents_iff (d_mem ha)]
    intro h
    obtain rfl : i = 0 - 1 := by omega
    exact ⟨a, ha, rfl⟩

include hA in
theorem truncGEZero_mul_mem_left (c : A) {a : A}
    (ha : a ∈ ofComponents (truncGEZeroComponents A)) :
    c * a ∈ ofComponents (truncGEZeroComponents A) := by
  refine induction_on_of_isHomogeneous (isHomogeneous_ofComponents _)
    (P := fun a => c * a ∈ ofComponents (truncGEZeroComponents A)) (by simp [zero_mem]) ?_
    (fun a a' h h' => by simpa only [mul_add] using add_mem h h') ha
  intro i a hai haS
  induction c using induction_on with
  | h_zero => simp [zero_mem]
  | h_add c c' hc hc' => rw [add_mul]; exact add_mem hc hc'
  | h_homogeneous c =>
    obtain ⟨c, hc⟩ := c
    rename_i j
    rw [mem_truncGEZeroComponents_iff hai] at haS
    rw [mem_truncGEZeroComponents_iff (mul_mem_grading hc hai)]
    intro h
    by_cases hj : 0 < j
    · rw [eq_zero_of_mem_grading_of_pos hA hc hj, zero_mul]
      exact zero_mem _
    by_cases hi : 0 < i
    · rw [eq_zero_of_mem_grading_of_pos hA hai hi, mul_zero]
      exact zero_mem _
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    obtain ⟨b, hb, rfl⟩ := haS rfl
    refine ⟨c * b, by simpa using mul_mem_grading hc hb, ?_⟩
    rw [d_mul_of_mem_zero hc, d_eq_zero_of_mem_grading_zero hA hc, zero_mul, zero_add]

include hA in
theorem truncGEZero_mul_mem_right {a : A} (c : A)
    (ha : a ∈ ofComponents (truncGEZeroComponents A)) :
    a * c ∈ ofComponents (truncGEZeroComponents A) := by
  refine induction_on_of_isHomogeneous (isHomogeneous_ofComponents _)
    (P := fun a => a * c ∈ ofComponents (truncGEZeroComponents A)) (by simp [zero_mem]) ?_
    (fun a a' h h' => by simpa only [add_mul] using add_mem h h') ha
  intro i a hai haS
  induction c using induction_on with
  | h_zero => simp [zero_mem]
  | h_add c c' hc hc' => rw [mul_add]; exact add_mem hc hc'
  | h_homogeneous c =>
    obtain ⟨c, hc⟩ := c
    rename_i j
    rw [mem_truncGEZeroComponents_iff hai] at haS
    rw [mem_truncGEZeroComponents_iff (mul_mem_grading hai hc)]
    intro h
    by_cases hj : 0 < j
    · rw [eq_zero_of_mem_grading_of_pos hA hc hj, mul_zero]
      exact zero_mem _
    by_cases hi : 0 < i
    · rw [eq_zero_of_mem_grading_of_pos hA hai hi, zero_mul]
      exact zero_mem _
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    obtain ⟨b, hb, rfl⟩ := haS rfl
    refine ⟨b * c, by simpa using mul_mem_grading hb hc, ?_⟩
    rw [d_mul hb, d_eq_zero_of_mem_grading_zero hA hc, mul_zero, smul_zero, add_zero]

/-- For a dg ring `A` concentrated in non-positive degrees, the dg ideal `A^{< 0} ⊕ d(A⁻¹)` of
elements whose degree-`0` component is a coboundary. The quotient is `H⁰(A)` in degree `0`. -/
def truncGEZeroIdeal : DGIdeal A where
  carrier := ofComponents (truncGEZeroComponents A)
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' c _ ha := truncGEZero_mul_mem_left hA c ha
  mul_mem_right' c ha := truncGEZero_mul_mem_right hA c ha
  isHomogeneous' := isHomogeneous_ofComponents _
  d_mem' {a} _ := truncGEZero_d_mem a

theorem mem_truncGEZeroIdeal_iff_of_mem_grading {k : ℤ} {x : A} (hx : x ∈ grading k) :
    x ∈ truncGEZeroIdeal hA ↔ (k = 0 → x ∈ coboundaries A 0) :=
  mem_truncGEZeroComponents_iff hx

/-- The projection `A → τ^{≥ 0} A = A ⧸ (A^{< 0} ⊕ d(A⁻¹))` onto `H⁰(A)`, a morphism of dg
rings. -/
def truncGEZeroπ : A →ᵈᵍ+* A ⧸ truncGEZeroIdeal hA :=
  DGIdeal.Quotient.mk (truncGEZeroIdeal hA)

theorem truncGEZeroπ_surjective : Function.Surjective (truncGEZeroπ hA) :=
  DGIdeal.Quotient.mk_surjective _

namespace truncGEZero

/-- The differential of `τ^{≥ 0} A` is zero. -/
theorem d_eq_zero (x : A ⧸ truncGEZeroIdeal hA) : d x = 0 := by
  obtain ⟨a, rfl⟩ := truncGEZeroπ_surjective hA x
  rw [← DGRingHom.map_d]
  exact (DGIdeal.Quotient.mk_eq_zero_iff_mem _).mpr (truncGEZero_d_mem a)

/-- `τ^{≥ 0} A` is concentrated in degree `0`. -/
theorem eq_zero_of_mem_grading {n : ℤ} (hn : n ≠ 0) {x : A ⧸ truncGEZeroIdeal hA}
    (hx : x ∈ grading n) : x = 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact (DGIdeal.Quotient.mk_eq_zero_iff_mem _).mpr
    ((mem_truncGEZeroIdeal_iff_of_mem_grading hA ha).mpr fun h => absurd h hn)

end truncGEZero

/-- The projection `A → τ^{≥ 0} A` induces an isomorphism `H⁰(A) ≅ H⁰(τ^{≥ 0} A)`. -/
theorem bijective_cohomologyMap_truncGEZeroπ :
    Function.Bijective ((truncGEZeroπ hA).cohomologyMap 0) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using cohomology.induction_on with
    | h z =>
    rw [DGRingHom.cohomologyMap_mk, cohomology.mk_eq_zero_iff, DGRingHom.coe_cocyclesMap] at hx
    obtain ⟨y, _, hy⟩ := hx
    rw [truncGEZero.d_eq_zero] at hy
    have hz : (z : A) ∈ truncGEZeroIdeal hA :=
      (DGIdeal.Quotient.mk_eq_zero_iff_mem _).mp hy.symm
    rw [cohomology.mk_eq_zero_iff]
    exact (mem_truncGEZeroIdeal_iff_of_mem_grading hA z.2.1).mp hz rfl
  · intro x
    induction x using cohomology.induction_on with
    | h w =>
    obtain ⟨a, ha, hw⟩ := w.2.1
    refine ⟨cohomology.mk _ 0 ⟨a, ha, d_eq_zero_of_mem_grading_zero hA ha⟩, ?_⟩
    rw [DGRingHom.cohomologyMap_mk]
    congr 1
    exact Subtype.ext hw

/-- `H⁰(A) ≅ H⁰(τ^{≥ 0} A)` for a dg ring `A` concentrated in non-positive degrees. -/
noncomputable def cohomologyZeroAddEquivTruncGEZero :
    cohomology A 0 ≃+ cohomology (A ⧸ truncGEZeroIdeal hA) 0 :=
  AddEquiv.ofBijective _ (bijective_cohomologyMap_truncGEZeroπ hA)

end TruncGE

end DG
