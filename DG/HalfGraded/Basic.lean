import DG.Bigraded.Basic
import DG.Graded.Basic

/-!
# Half-graded dg rings

A *half-graded* dg ring (with parameter `k : ℤ`) is a ring `A` graded by `ℤ × ℤ/2` (an internal
degree and a parity), `A = ⨁ (j, ε), A^{j,ε}`, with a differential `d` of bidegree `(k, 1̄)`: `d` is
odd and raises the internal degree by `k`. The sign rule is that of the parity:
`d (a * b) = d a * b + (-1)^{|a|} • (a * d b)` where `|a| ∈ ℤ/2` is the parity of `a`. The main
case is `k = 2`.

Following `docs/CONVENTIONS.md`, half-graded objects are not a second core: they are treated by
regrading into bigraded dg objects (tier 7), which are then dg modules over the weight dg
category (`DG.WeightCategory`). The regrading is the pullback of the `ℤ × ℤ/2`-grading along the
group homomorphism

  `DG.halfDegree k : ℤ × ℤ →+ ℤ × ℤ/2`, `(n, w) ↦ (w + n k, n mod 2)`,

where `n` is a cohomological degree and `w` a weight:
`DG.HalfRegrade ℳ k = ⨁ (n, w), ℳ^{w + n k, n}`.
The differential of bidegree `(k, 1̄)` becomes a differential of bidegree `(1, 0)`, since
`halfDegree k (n + 1, w) = halfDegree k (n, w) + (k, 1̄)`, and the parity of an element placed in
cohomological degree `n` is `n mod 2`, so the Koszul signs of the parity become those of the
cohomological degree. This combines the two regradings of item 1.4 of the roadmap: the
periodization of a `ℤ/2`-grading (`DG.Periodize`, the fibres of `halfDegree k` are the
translates of `(2, -2k) ℤ`) and the division of a grading by the degree of the differential
(`DG.RegradeByDivision`, here the division of the internal degree by the translation by
`(k, 1̄)`). Every element of `A^{j,ε}` appears once in each bidegree `(n, w)` with `n ≡ ε` and
`w + n k = j`; these copies are related by the central unit `u = 1 ∈ A^{0,0̄}` placed in bidegree
`(2, -2k)` (`DG.HalfGradedDGRing.periodUnit`).

## Main definitions

* `DG.coarseGrading β f`: for `f : ι → κ`, the grading of an external direct sum `⨁ i, β i` by
  the fibres of `f`, with its `DirectSum.Decomposition` and the formula for its components
  (`DG.coe_decompose_coarseGrading_apply`).
* `DG.halfDegree k`, `DG.HalfRegrade ℳ k := ⨁ p : ℤ × ℤ, ℳ (halfDegree k p)` for a
  `ℤ × ℤ/2`-graded object `ℳ`, with `DG.HalfRegrade.mk ℳ k p m hm` (an element `m ∈ ℳ^{w + n k, n}`
  placed in bidegree `p = (n, w)`), the cohomological grading `DG.HalfRegrade.cohGrading` and the
  weight grading `DG.HalfRegrade.weightGrading`, and the regraded differential
  `DG.HalfRegrade.dHom`.
* `DG.HalfGradedDGRing A k`: a half-graded dg ring structure on a ring `A`.
* `DG.HalfGradedDGRing.Regraded H`: the regraded ring `⨁ (n, w), A^{w + n k, n}`, with the
  instances `DGAddCommGroup`, `DGRing`, `InternalGrading` and `BigradedDGRing`; its weight dg
  category `DG.WeightCategory H.Regraded` is the dg category whose dg modules are the half-graded
  dg `A`-modules.
* `DG.HalfGradedDGRing.periodUnit H`: the central unit `u` of bidegree `(2, -2k)`, with inverse
  `DG.HalfGradedDGRing.periodUnitInv H` of bidegree `(-2, 2k)`; both are cocycles.
-/

open DirectSum

namespace DG

/-! ### Coarsening the grading of an external direct sum -/

section Coarse

variable {ι κ : Type*} (β : ι → Type*) [∀ i, AddCommGroup (β i)] (f : ι → κ)

/-- The grading of an external direct sum `⨁ i, β i` by the fibres of a map `f : ι → κ`: the
component of `k : κ` consists of the elements supported on `f⁻¹ {k}`. -/
def coarseGrading (k : κ) : AddSubgroup (⨁ i, β i) where
  carrier := {x | ∀ i, f i ≠ k → x i = 0}
  add_mem' {x y} hx hy i hi := by rw [add_apply, hx i hi, hy i hi, add_zero]
  zero_mem' i _ := DirectSum.zero_apply (β := β) i
  neg_mem' {x} hx i hi := by
    change (-x) i = 0
    rw [DFinsupp.neg_apply, hx i hi, neg_zero]

variable {β f}

theorem mem_coarseGrading_iff {k : κ} {x : ⨁ i, β i} :
    x ∈ coarseGrading β f k ↔ ∀ i, f i ≠ k → x i = 0 :=
  Iff.rfl

variable [DecidableEq ι]

theorem of_mem_coarseGrading (i : ι) (b : β i) : DirectSum.of β i b ∈ coarseGrading β f (f i) :=
  fun j hj => of_eq_of_ne i j b fun h => hj (h ▸ rfl)

theorem of_mem_coarseGrading' {i : ι} {k : κ} (h : f i = k) (b : β i) :
    DirectSum.of β i b ∈ coarseGrading β f k :=
  h ▸ of_mem_coarseGrading i b

variable (β f) [DecidableEq κ]

/-- The inclusion of `β i` into the component of `f i` of the coarse grading. -/
def toCoarseGrading (i : ι) : β i →+ coarseGrading β f (f i) where
  toFun b := ⟨DirectSum.of β i b, of_mem_coarseGrading i b⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The decomposition of `⨁ i, β i` into the components of the coarse grading. -/
def coarseDecompose : (⨁ i, β i) →+ ⨁ k, coarseGrading β f k :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.of (fun k => coarseGrading β f k) (f i)).comp (toCoarseGrading β f i)

variable {β f}

theorem coe_coarseDecompose_apply (x : ⨁ i, β i) (k : κ) (i : ι) :
    ((coarseDecompose β f x k : ⨁ i, β i) i) = if f i = k then x i else 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j b =>
    simp only [coarseDecompose, toAddMonoid_of, AddMonoidHom.comp_apply]
    by_cases hjk : f j = k
    · subst hjk
      rw [of_eq_same]
      change (DirectSum.of β j b) i = _
      by_cases hij : i = j
      · subst hij; simp
      · rw [of_eq_of_ne j i b hij]; simp
    · rw [of_eq_of_ne _ _ _ (Ne.symm hjk), ZeroMemClass.coe_zero, zero_apply]
      by_cases hij : i = j
      · subst hij; simp [hjk]
      · rw [of_eq_of_ne j i b hij]; simp
  | add x y hx hy =>
    rw [map_add, add_apply, AddSubgroup.coe_add, add_apply, hx, hy, add_apply]
    split_ifs <;> simp

theorem coeAddMonoidHom_comp_coarseDecompose :
    (DirectSum.coeAddMonoidHom (coarseGrading β f)).comp (coarseDecompose β f) =
      AddMonoidHom.id _ := by
  refine DirectSum.addHom_ext fun i b => ?_
  simp only [AddMonoidHom.comp_apply, coarseDecompose, toAddMonoid_of, coeAddMonoidHom_of,
    AddMonoidHom.id_apply]
  rfl

theorem coarseDecompose_comp_coeAddMonoidHom :
    (coarseDecompose β f).comp (DirectSum.coeAddMonoidHom (coarseGrading β f)) =
      AddMonoidHom.id _ := by
  refine DirectSum.addHom_ext fun k y => ?_
  simp only [AddMonoidHom.comp_apply, coeAddMonoidHom_of, AddMonoidHom.id_apply]
  ext k' i
  rw [coe_coarseDecompose_apply]
  by_cases hk : k = k'
  · subst hk
    rw [of_eq_same]
    split_ifs with h
    · rfl
    · exact (y.2 i h).symm
  · rw [of_eq_of_ne _ _ _ (Ne.symm hk), ZeroMemClass.coe_zero, zero_apply]
    split_ifs with h
    · exact y.2 i (h ▸ Ne.symm hk)
    · rfl

variable (β f)

/-- The coarse grading is a decomposition of `⨁ i, β i`. -/
instance instDecompositionCoarseGrading : Decomposition (coarseGrading β f) :=
  Decomposition.ofAddHom _ (coarseDecompose β f) coeAddMonoidHom_comp_coarseDecompose
    coarseDecompose_comp_coeAddMonoidHom

variable {β f}

/-- The components of the coarse decomposition: the component of `k` of `x` is the restriction
of `x` to `f⁻¹ {k}`. -/
theorem coe_decompose_coarseGrading_apply (x : ⨁ i, β i) (k : κ) (i : ι) :
    ((decompose (coarseGrading β f) x k : ⨁ i, β i) i) = if f i = k then x i else 0 :=
  coe_coarseDecompose_apply x k i

/-- Induction on an element of a component of the coarse grading. -/
theorem coarseGrading_induction {k : κ} {P : (⨁ i, β i) → Prop} (zero : P 0)
    (of : ∀ i (b : β i), f i = k → P (DirectSum.of β i b)) (add : ∀ x y, P x → P y → P (x + y))
    {x : ⨁ i, β i} (hx : x ∈ coarseGrading β f k) : P x := by
  classical
  rw [← DirectSum.sum_support_of x]
  induction x.support using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine add _ _ ?_ ih
    by_cases h : f i = k
    · exact of i _ h
    · rw [hx i h, map_zero]; exact zero

end Coarse

/-! ### The regrading of a `ℤ × ℤ/2`-graded object -/

/-- The group homomorphism `ℤ × ℤ →+ ℤ × ℤ/2`, `(n, w) ↦ (w + n k, n mod 2)`, sending a
cohomological degree `n` and a weight `w` to an internal degree and a parity. -/
def halfDegree (k : ℤ) : ℤ × ℤ →+ ℤ × ZMod 2 where
  toFun p := (p.2 + p.1 * k, (p.1 : ZMod 2))
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Prod.mk_add_mk, Prod.mk.injEq, and_true]
    ring

@[simp]
theorem halfDegree_apply (k : ℤ) (p : ℤ × ℤ) :
    halfDegree k p = (p.2 + p.1 * k, (p.1 : ZMod 2)) :=
  rfl

/-- Raising the cohomological degree by `1` raises the half-degree by `(k, 1̄)`. -/
theorem halfDegree_add_one_zero (k : ℤ) (p : ℤ × ℤ) :
    halfDegree k (p + (1, 0)) = halfDegree k p + (k, 1) := by
  simp only [halfDegree_apply, Prod.fst_add, Prod.snd_add, add_zero, Int.cast_add, Int.cast_one,
    Prod.mk_add_mk, Prod.mk.injEq, and_true]
  ring

section HalfRegrade

variable {M σ : Type*} [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M]

/-- The pullback `p ↦ ℳ (halfDegree k p)` of a `ℤ × ℤ/2`-grading to `ℤ × ℤ`. -/
def halfGrading (ℳ : ℤ × ZMod 2 → σ) (k : ℤ) (p : ℤ × ℤ) : σ := ℳ (halfDegree k p)

omit [AddCommGroup M] [AddSubgroupClass σ M] in
@[simp]
theorem mem_halfGrading {ℳ : ℤ × ZMod 2 → σ} {k : ℤ} {p : ℤ × ℤ} {m : M} :
    m ∈ halfGrading ℳ k p ↔ m ∈ ℳ (halfDegree k p) := Iff.rfl

/-- The bigraded object attached to a `ℤ × ℤ/2`-graded object `ℳ` and `k : ℤ`: the external
direct sum `⨁ (n, w), ℳ^{w + n k, n mod 2}`, bigraded by the cohomological degree `n` and the
weight `w`. -/
def HalfRegrade (ℳ : ℤ × ZMod 2 → σ) (k : ℤ) : Type _ := ⨁ p : ℤ × ℤ, ↥(halfGrading ℳ k p)

instance (ℳ : ℤ × ZMod 2 → σ) (k : ℤ) : AddCommGroup (HalfRegrade ℳ k) :=
  inferInstanceAs (AddCommGroup (⨁ p : ℤ × ℤ, ↥(halfGrading ℳ k p)))

namespace HalfRegrade

variable (ℳ : ℤ × ZMod 2 → σ) (k : ℤ)

/-- An element `m ∈ ℳ^{w + n k, n}`, placed in bidegree `p = (n, w)` of `HalfRegrade ℳ k`. -/
def mk (p : ℤ × ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k p)) : HalfRegrade ℳ k :=
  DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p ⟨m, hm⟩

/-- The cohomological grading of `HalfRegrade ℳ k`: the elements supported in cohomological
degree `n`. -/
def cohGrading (n : ℤ) : AddSubgroup (HalfRegrade ℳ k) :=
  coarseGrading (fun p => ↥(halfGrading ℳ k p)) Prod.fst n

/-- The weight grading of `HalfRegrade ℳ k`: the elements supported in weight `w`. -/
def weightGrading (w : ℤ) : AddSubgroup (HalfRegrade ℳ k) :=
  coarseGrading (fun p => ↥(halfGrading ℳ k p)) Prod.snd w

instance instDecompositionCohGrading : Decomposition (cohGrading ℳ k) :=
  inferInstanceAs (Decomposition (coarseGrading (fun p => ↥(halfGrading ℳ k p)) Prod.fst))

instance instDecompositionWeightGrading : Decomposition (weightGrading ℳ k) :=
  inferInstanceAs (Decomposition (coarseGrading (fun p => ↥(halfGrading ℳ k p)) Prod.snd))

variable {ℳ k}

theorem mk_congr {p p' : ℤ × ℤ} (h : p = p') {m m' : M} (h' : m = m')
    (hm : m ∈ ℳ (halfDegree k p)) (hm' : m' ∈ ℳ (halfDegree k p')) :
    mk ℳ k p m hm = mk ℳ k p' m' hm' := by
  subst h h'; rfl

@[simp]
theorem mk_zero (p : ℤ × ℤ) : mk ℳ k p 0 (zero_mem _) = 0 :=
  (DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p).map_zero

theorem mk_add (p : ℤ × ℤ) {m m' : M} (hm : m ∈ ℳ (halfDegree k p))
    (hm' : m' ∈ ℳ (halfDegree k p)) :
    mk ℳ k p (m + m') (add_mem hm hm') = mk ℳ k p m hm + mk ℳ k p m' hm' :=
  (DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p).map_add ⟨m, hm⟩ ⟨m', hm'⟩

theorem mk_neg (p : ℤ × ℤ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p (-m) (neg_mem hm) = -mk ℳ k p m hm :=
  (DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p).map_neg ⟨m, hm⟩

theorem mk_zsmul (p : ℤ × ℤ) (c : ℤ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p (c • m) (zsmul_mem hm c) = c • mk ℳ k p m hm :=
  (DirectSum.of (fun p => ↥(halfGrading ℳ k p)) p).map_zsmul c ⟨m, hm⟩

theorem mk_units_smul (p : ℤ × ℤ) (c : ℤˣ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p (c • m) (by rw [Units.smul_def]; exact zsmul_mem hm _) = c • mk ℳ k p m hm := by
  simp only [Units.smul_def]
  exact mk_zsmul p (c : ℤ) hm

@[elab_as_elim]
theorem induction_on {P : HalfRegrade ℳ k → Prop} (x : HalfRegrade ℳ k) (zero : P 0)
    (mk : ∀ (p : ℤ × ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k p)), P (mk ℳ k p m hm))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact zero
  | of p m => exact mk p m.1 m.2
  | add x y hx hy => exact add x y hx hy

theorem addHom_ext {N : Type*} [AddCommMonoid N] {f g : HalfRegrade ℳ k →+ N}
    (h : ∀ (p : ℤ × ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k p)),
      f (mk ℳ k p m hm) = g (mk ℳ k p m hm)) :
    f = g :=
  DirectSum.addHom_ext fun p m => h p m.1 m.2

theorem mk_mem_cohGrading (p : ℤ × ℤ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p m hm ∈ cohGrading ℳ k p.1 :=
  of_mem_coarseGrading (f := Prod.fst) p _

theorem mk_mem_weightGrading (p : ℤ × ℤ) {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    mk ℳ k p m hm ∈ weightGrading ℳ k p.2 :=
  of_mem_coarseGrading (f := Prod.snd) p _

/-- Induction on an element of cohomological degree `n`. -/
theorem cohGrading_induction {n : ℤ} {P : HalfRegrade ℳ k → Prop} (zero : P 0)
    (mk : ∀ (w : ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k (n, w))), P (mk ℳ k (n, w) m hm))
    (add : ∀ x y, P x → P y → P (x + y)) {x : HalfRegrade ℳ k} (hx : x ∈ cohGrading ℳ k n) :
    P x :=
  coarseGrading_induction (f := Prod.fst) zero
    (fun (p : ℤ × ℤ) b hp => by rcases p with ⟨n', w⟩; subst hp; exact mk w b.1 b.2) add hx

/-- Induction on an element of weight `w`. -/
theorem weightGrading_induction {w : ℤ} {P : HalfRegrade ℳ k → Prop} (zero : P 0)
    (mk : ∀ (n : ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k (n, w))), P (mk ℳ k (n, w) m hm))
    (add : ∀ x y, P x → P y → P (x + y)) {x : HalfRegrade ℳ k} (hx : x ∈ weightGrading ℳ k w) :
    P x :=
  coarseGrading_induction (f := Prod.snd) zero
    (fun (p : ℤ × ℤ) b hp => by rcases p with ⟨n, w'⟩; subst hp; exact mk n b.1 b.2) add hx

/-- The two gradings of `HalfRegrade ℳ k` commute: the weight components of an element of
cohomological degree `n` have cohomological degree `n`. -/
theorem decompose_weightGrading_mem_cohGrading {n : ℤ} {x : HalfRegrade ℳ k}
    (hx : x ∈ cohGrading ℳ k n) (w : ℤ) :
    (decompose (weightGrading ℳ k) x w : HalfRegrade ℳ k) ∈ cohGrading ℳ k n := by
  intro p hp
  have h := coe_decompose_coarseGrading_apply (β := fun p => ↥(halfGrading ℳ k p))
    (f := Prod.snd) x w p
  refine h.trans ?_
  split_ifs
  · exact hx p hp
  · rfl

/-- The weight grading is homogeneous for the cohomological grading. -/
theorem isHomogeneous_cohGrading (n : ℤ) :
    SetLike.IsHomogeneous (weightGrading ℳ k) (cohGrading ℳ k n) :=
  fun w _ hx => decompose_weightGrading_mem_cohGrading hx w

section Differential

variable (ℳ k) (d : M →+ M)
  (hd : ∀ {j : ℤ} {ε : ZMod 2} {m : M}, m ∈ ℳ (j, ε) → d m ∈ ℳ (j + k, ε + 1))

omit [AddSubgroupClass σ M] in
include hd in
theorem d_mem_halfDegree_add {p : ℤ × ℤ} {m : M} (hm : m ∈ ℳ (halfDegree k p)) :
    d m ∈ ℳ (halfDegree k (p + (1, 0))) := by
  rw [halfDegree_add_one_zero]
  exact hd hm

/-- The differential of `HalfRegrade ℳ k` induced by a map `d` of bidegree `(k, 1̄)`: `m` placed
in bidegree `(n, w)` goes to `d m` placed in bidegree `(n + 1, w)`. -/
def dHom : HalfRegrade ℳ k →+ HalfRegrade ℳ k :=
  DirectSum.toAddMonoid fun p =>
    { toFun := fun m => mk ℳ k (p + (1, 0)) (d m) (d_mem_halfDegree_add ℳ k d hd m.2)
      map_zero' := by simp only [ZeroMemClass.coe_zero, map_zero]; exact mk_zero _
      map_add' := fun m m' => by
        simp only [AddMemClass.coe_add, map_add]
        exact mk_add _ _ _ }

variable {d hd}

@[simp]
theorem dHom_mk (p : ℤ × ℤ) (m : M) (hm : m ∈ ℳ (halfDegree k p)) :
    dHom ℳ k d hd (mk ℳ k p m hm) =
      mk ℳ k (p + (1, 0)) (d m) (d_mem_halfDegree_add ℳ k d hd hm) :=
  DirectSum.toAddMonoid_of (β := fun p => ↥(halfGrading ℳ k p)) _ p ⟨m, hm⟩

theorem dHom_mem_cohGrading {n : ℤ} {x : HalfRegrade ℳ k} (hx : x ∈ cohGrading ℳ k n) :
    dHom ℳ k d hd x ∈ cohGrading ℳ k (n + 1) := by
  refine cohGrading_induction (P := fun x => dHom ℳ k d hd x ∈ cohGrading ℳ k (n + 1)) ?_
    (fun w m hm => ?_) (fun x y hx hy => ?_) hx
  · rw [map_zero]; exact zero_mem _
  · rw [dHom_mk]; exact mk_mem_cohGrading (ℳ := ℳ) (k := k) ((n, w) + (1, 0)) _
  · rw [map_add]; exact add_mem hx hy

theorem dHom_mem_weightGrading {w : ℤ} {x : HalfRegrade ℳ k} (hx : x ∈ weightGrading ℳ k w) :
    dHom ℳ k d hd x ∈ weightGrading ℳ k w := by
  refine weightGrading_induction (P := fun x => dHom ℳ k d hd x ∈ weightGrading ℳ k w) ?_
    (fun n m hm => ?_) (fun x y hx hy => ?_) hx
  · rw [map_zero]; exact zero_mem _
  · rw [dHom_mk]
    have := mk_mem_weightGrading (ℳ := ℳ) (k := k) ((n, w) + (1, 0))
      (d_mem_halfDegree_add ℳ k d hd hm)
    simpa using this
  · rw [map_add]; exact add_mem hx hy

theorem dHom_dHom (hdd : ∀ m, d (d m) = 0) (x : HalfRegrade ℳ k) :
    dHom ℳ k d hd (dHom ℳ k d hd x) = 0 := by
  induction x using induction_on with
  | zero => simp
  | mk p m hm => simp only [dHom_mk]; exact (mk_congr rfl (hdd m) _ _).trans (mk_zero _)
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end Differential

end HalfRegrade

end HalfRegrade

/-! ### Half-graded dg rings -/

/-- A half-graded dg ring structure with parameter `k : ℤ` on a ring `A`: a `ℤ × ℤ/2`-grading
`A = ⨁ (j, ε), A^{j,ε}` (internal degree `j`, parity `ε`) which is a ring grading, and a
differential `d` of bidegree `(k, 1̄)` with `d ∘ d = 0`, satisfying the Leibniz rule with the sign
of the parity, `d (a * b) = d a * b + (-1)^ε • (a * d b)` for `a ∈ A^{j,ε}`; the sign is written
`koszulSign n` for an integer `n` with `n mod 2 = ε`. -/
structure HalfGradedDGRing (A : Type*) [Ring A] (k : ℤ) where
  /-- The homogeneous components `A^{j,ε}`. -/
  hgrading : ℤ × ZMod 2 → AddSubgroup A
  /-- The grading is an internal direct sum decomposition. -/
  [decomposition : DirectSum.Decomposition hgrading]
  /-- The grading is a ring grading. -/
  [gradedMonoid : SetLike.GradedMonoid hgrading]
  /-- The differential, of bidegree `(k, 1̄)`. -/
  hd : A →+ A
  hd_mem : ∀ {j : ℤ} {ε : ZMod 2} {a : A}, a ∈ hgrading (j, ε) → hd a ∈ hgrading (j + k, ε + 1)
  hd_hd : ∀ a : A, hd (hd a) = 0
  hd_mul : ∀ {j n : ℤ} {a : A}, a ∈ hgrading (j, (n : ZMod 2)) → ∀ b : A,
    hd (a * b) = hd a * b + koszulSign n • (a * hd b)

attribute [instance] HalfGradedDGRing.decomposition HalfGradedDGRing.gradedMonoid

namespace HalfGradedDGRing

variable {A : Type*} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)

instance gradedMonoid_halfGrading : SetLike.GradedMonoid (halfGrading H.hgrading k) where
  one_mem := by
    rw [mem_halfGrading, map_zero]
    exact SetLike.GradedOne.one_mem
  mul_mem p q a b ha hb := by
    rw [mem_halfGrading, map_add]
    exact SetLike.GradedMul.mul_mem ha hb

/-- The regraded ring `⨁ (n, w), A^{w + n k, n mod 2}` of a half-graded dg ring, bigraded by the
cohomological degree `n` and the weight `w`, with the differential of bidegree `(1, 0)` induced by
`d`. -/
def Regraded : Type _ := HalfRegrade H.hgrading k

instance : Ring H.Regraded :=
  inferInstanceAs (Ring (⨁ p : ℤ × ℤ, ↥(halfGrading H.hgrading k p)))

/-- An element `a ∈ A^{w + n k, n}` placed in bidegree `p = (n, w)` of the regraded ring. -/
def place (p : ℤ × ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k p)) : H.Regraded :=
  HalfRegrade.mk H.hgrading k p a ha

variable {H}

theorem place_congr {p p' : ℤ × ℤ} (h : p = p') {a a' : A} (h' : a = a')
    (ha : a ∈ H.hgrading (halfDegree k p)) (ha' : a' ∈ H.hgrading (halfDegree k p')) :
    H.place p a ha = H.place p' a' ha' :=
  HalfRegrade.mk_congr h h' ha ha'

@[simp]
theorem place_zero (p : ℤ × ℤ) : H.place p 0 (zero_mem _) = 0 :=
  HalfRegrade.mk_zero p

theorem place_add (p : ℤ × ℤ) {a a' : A} (ha : a ∈ H.hgrading (halfDegree k p))
    (ha' : a' ∈ H.hgrading (halfDegree k p)) :
    H.place p (a + a') (add_mem ha ha') = H.place p a ha + H.place p a' ha' :=
  HalfRegrade.mk_add p ha ha'

theorem place_add_of_eq {p₁ p₂ p : ℤ × ℤ} (h₁ : p₁ = p) (h₂ : p₂ = p) {a a' : A}
    (ha : a ∈ H.hgrading (halfDegree k p₁)) (ha' : a' ∈ H.hgrading (halfDegree k p₂)) :
    H.place p₁ a ha + H.place p₂ a' ha' =
      H.place p (a + a') (by subst h₁ h₂; exact add_mem ha ha') := by
  subst h₁ h₂
  exact (place_add _ ha ha').symm

theorem place_units_smul (p : ℤ × ℤ) (c : ℤˣ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p (c • a) (by rw [Units.smul_def]; exact zsmul_mem ha _) = c • H.place p a ha :=
  HalfRegrade.mk_units_smul p c ha

theorem place_mul_place {p q : ℤ × ℤ} {a b : A} (ha : a ∈ H.hgrading (halfDegree k p))
    (hb : b ∈ H.hgrading (halfDegree k q)) :
    H.place p a ha * H.place q b hb =
      H.place (p + q) (a * b) (show a * b ∈ H.hgrading (halfDegree k (p + q)) from
        SetLike.GradedMul.mul_mem (A := halfGrading H.hgrading k) ha hb) :=
  DirectSum.of_mul_of _ _

theorem one_eq_place : (1 : H.Regraded) =
    H.place 0 1 (SetLike.GradedOne.one_mem (A := halfGrading H.hgrading k)) :=
  rfl

@[elab_as_elim]
theorem induction_on {P : H.Regraded → Prop} (x : H.Regraded) (zero : P 0)
    (mk : ∀ (p : ℤ × ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k p)), P (H.place p a ha))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  HalfRegrade.induction_on x zero mk add

variable (H)

/-- The regraded ring is a dg abelian group, graded by the cohomological degree, with the
differential induced by `d`. -/
instance instDGAddCommGroup : DGAddCommGroup H.Regraded where
  grading := HalfRegrade.cohGrading H.hgrading k
  decomposition := HalfRegrade.instDecompositionCohGrading H.hgrading k
  d := HalfRegrade.dHom H.hgrading k H.hd H.hd_mem
  d_mem' := HalfRegrade.dHom_mem_cohGrading _ _
  d_d' := HalfRegrade.dHom_dHom _ _ H.hd_hd

/-- The weight grading of the regraded ring. -/
instance instInternalGrading : InternalGrading H.Regraded where
  wgrading := HalfRegrade.weightGrading H.hgrading k
  wdecomposition := HalfRegrade.instDecompositionWeightGrading H.hgrading k
  isHomogeneous_grading' := HalfRegrade.isHomogeneous_cohGrading
  d_mem_wgrading' := HalfRegrade.dHom_mem_weightGrading _ _

variable {H}

theorem mem_grading_iff {n : ℤ} {x : H.Regraded} :
    x ∈ grading n ↔ x ∈ HalfRegrade.cohGrading H.hgrading k n :=
  Iff.rfl

theorem mem_wgrading_iff {w : ℤ} {x : H.Regraded} :
    x ∈ wgrading w ↔ x ∈ HalfRegrade.weightGrading H.hgrading k w :=
  Iff.rfl

theorem place_mem_grading (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p a ha ∈ grading (M := H.Regraded) p.1 :=
  HalfRegrade.mk_mem_cohGrading p ha

theorem place_mem_wgrading (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p a ha ∈ wgrading (M := H.Regraded) p.2 :=
  HalfRegrade.mk_mem_weightGrading p ha

@[simp]
theorem d_place (p : ℤ × ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k p)) :
    d (H.place p a ha) =
      H.place (p + (1, 0)) (H.hd a)
        (HalfRegrade.d_mem_halfDegree_add H.hgrading k H.hd H.hd_mem ha) :=
  HalfRegrade.dHom_mk H.hgrading k p a ha

/-- Induction on an element of cohomological degree `n`. -/
theorem grading_induction {n : ℤ} {P : H.Regraded → Prop} (zero : P 0)
    (mk : ∀ (w : ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k (n, w))), P (H.place (n, w) a ha))
    (add : ∀ x y, P x → P y → P (x + y)) {x : H.Regraded} (hx : x ∈ grading n) : P x :=
  HalfRegrade.cohGrading_induction zero mk add hx

/-- Induction on an element of weight `w`. -/
theorem wgrading_induction {w : ℤ} {P : H.Regraded → Prop} (zero : P 0)
    (mk : ∀ (n : ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k (n, w))), P (H.place (n, w) a ha))
    (add : ∀ x y, P x → P y → P (x + y)) {x : H.Regraded} (hx : x ∈ wgrading w) : P x :=
  HalfRegrade.weightGrading_induction zero mk add hx

/-- A property of products which is additive in both factors holds as soon as it holds for
products of elements of the form `mk p a ha`, `mk q b hb`, with `p` in a given subset. -/
theorem mul_induction {P : H.Regraded → H.Regraded → Prop}
    (zero_left : ∀ y, P 0 y) (zero_right : ∀ x, P x 0)
    (add_left : ∀ x x' y, P x y → P x' y → P (x + x') y)
    (add_right : ∀ x y y', P x y → P x y' → P x (y + y'))
    (mk_mk : ∀ (p q : ℤ × ℤ) (a : A) (ha : a ∈ H.hgrading (halfDegree k p)) (b : A)
      (hb : b ∈ H.hgrading (halfDegree k q)), P (H.place p a ha) (H.place q b hb))
    (x y : H.Regraded) : P x y := by
  induction x using induction_on with
  | zero => exact zero_left y
  | mk p a ha =>
    induction y using induction_on with
    | zero => exact zero_right _
    | mk q b hb => exact mk_mk p q a ha b hb
    | add y y' hy hy' => exact add_right _ _ _ hy hy'
  | add x x' hx hx' => exact add_left _ _ _ hx hx'

variable (H)

/-- The weight grading of the regraded ring is a ring grading. -/
instance instBigradedDGRing : BigradedDGRing H.Regraded where
  one_mem := by
    rw [one_eq_place]
    exact place_mem_wgrading (H := H) 0 _
  mul_mem i j x y hx hy := by
    refine wgrading_induction (P := fun x => x * y ∈ wgrading (i + j)) (by simp)
      (fun n a ha => ?_) (fun x x' h h' => by rw [add_mul]; exact add_mem h h') hx
    refine wgrading_induction (P := fun y => H.place (n, i) a ha * y ∈ wgrading (i + j)) (by simp)
      (fun n' b hb => ?_) (fun y y' h h' => by rw [mul_add]; exact add_mem h h') hy
    rw [place_mul_place]
    exact place_mem_wgrading (H := H) ((n, i) + (n', j)) _

/-- The regraded ring is a dg ring: the Leibniz rule for the cohomological degree is the Leibniz
rule of `A` for the parity. -/
instance instDGRing : DGRing H.Regraded where
  one_mem := by
    rw [one_eq_place]
    exact place_mem_grading (H := H) 0 _
  mul_mem i j x y hx hy := by
    refine grading_induction (P := fun x => x * y ∈ grading (i + j)) (by simp)
      (fun w a ha => ?_) (fun x x' h h' => by rw [add_mul]; exact add_mem h h') hx
    refine grading_induction
      (P := fun y => H.place (i, w) a ha * y ∈ grading (i + j)) (by simp)
      (fun w' b hb => ?_) (fun y y' h h' => by rw [mul_add]; exact add_mem h h') hy
    rw [place_mul_place]
    exact place_mem_grading (H := H) ((i, w) + (j, w')) _
  d_mul' {n x} hx y := by
    refine grading_induction
      (P := fun x => d (x * y) =
        d x * y + koszulSign n • (x * d y)) (by simp)
      (fun w a ha => ?_) (fun x x' h h' => by
        rw [add_mul, d_add, h, h', d_add, add_mul, add_mul, smul_add]; abel) hx
    induction y using induction_on with
    | zero => simp
    | mk q b hb =>
      rw [place_mul_place, d_place, d_place, d_place, place_mul_place, place_mul_place,
        ← place_units_smul, place_add_of_eq (p := (n, w) + q + (1, 0)) (by abel) (by abel)]
      exact place_congr rfl (H.hd_mul ha b) _ _
    | add y y' hy hy' => rw [mul_add, d_add, hy, hy', d_add, mul_add, mul_add, smul_add]; abel

/-! ### The periodicity unit -/

section PeriodUnit

variable {H}

theorem hd_one : H.hd 1 = 0 := by
  have h := H.hd_mul (j := 0) (n := 0) (SetLike.GradedOne.one_mem (A := H.hgrading)) 1
  rw [mul_one, one_mul, koszulSign_zero, one_smul, mul_one] at h
  exact left_eq_add.mp h

theorem one_mem_of_halfDegree_eq_zero {p : ℤ × ℤ} (hp : halfDegree k p = 0) :
    (1 : A) ∈ H.hgrading (halfDegree k p) := by
  rw [hp]; exact SetLike.GradedOne.one_mem

theorem halfDegree_two : halfDegree k (2, -2 * k) = 0 := by
  simp only [halfDegree_apply, Int.cast_ofNat, Prod.mk_eq_zero]
  exact ⟨by ring, rfl⟩

theorem halfDegree_neg_two : halfDegree k (-2, 2 * k) = 0 := by
  simp only [halfDegree_apply, Int.cast_neg, Int.cast_ofNat, Prod.mk_eq_zero]
  exact ⟨by ring, rfl⟩

variable (H)

/-- The periodicity unit `u` of the regraded ring: `1 ∈ A^{0,0̄}` placed in bidegree `(2, -2k)`
(cohomological degree `2`, weight `-2k`). It is central, a cocycle, and invertible with inverse
`DG.HalfGradedDGRing.periodUnitInv`. Multiplication by `u` identifies the copies
`(n, w)` and `(n + 2, w - 2k)` of `A^{w + n k, n}`. -/
def periodUnit : H.Regraded :=
  H.place (2, -2 * k) 1 (one_mem_of_halfDegree_eq_zero halfDegree_two)

/-- The inverse `u⁻¹` of the periodicity unit: `1 ∈ A^{0,0̄}` placed in bidegree `(-2, 2k)`. -/
def periodUnitInv : H.Regraded :=
  H.place (-2, 2 * k) 1 (one_mem_of_halfDegree_eq_zero halfDegree_neg_two)

variable {H}

theorem place_mul_periodUnit (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p a ha * H.periodUnit =
      H.place (p + (2, -2 * k)) a (by rw [map_add, halfDegree_two, add_zero]; exact ha) := by
  rw [periodUnit, place_mul_place]
  exact place_congr rfl (mul_one a) _ _

theorem periodUnit_mul_place (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.periodUnit * H.place p a ha =
      H.place (p + (2, -2 * k)) a (by rw [map_add, halfDegree_two, add_zero]; exact ha) := by
  rw [periodUnit, place_mul_place]
  exact place_congr (add_comm _ _) (one_mul a) _ _

theorem place_mul_periodUnitInv (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.place p a ha * H.periodUnitInv =
      H.place (p + (-2, 2 * k)) a (by rw [map_add, halfDegree_neg_two, add_zero]; exact ha) := by
  rw [periodUnitInv, place_mul_place]
  exact place_congr rfl (mul_one a) _ _

theorem periodUnitInv_mul_place (p : ℤ × ℤ) {a : A} (ha : a ∈ H.hgrading (halfDegree k p)) :
    H.periodUnitInv * H.place p a ha =
      H.place (p + (-2, 2 * k)) a (by rw [map_add, halfDegree_neg_two, add_zero]; exact ha) := by
  rw [periodUnitInv, place_mul_place]
  exact place_congr (add_comm _ _) (one_mul a) _ _

variable (H)

theorem periodUnit_mul_periodUnitInv : H.periodUnit * H.periodUnitInv = 1 := by
  rw [periodUnit, place_mul_periodUnitInv, one_eq_place]
  exact place_congr (by ext <;> simp) rfl _ _

theorem periodUnitInv_mul_periodUnit : H.periodUnitInv * H.periodUnit = 1 := by
  rw [periodUnitInv, place_mul_periodUnit, one_eq_place]
  exact place_congr (by ext <;> simp) rfl _ _

/-- The periodicity unit is central. -/
theorem periodUnit_mul_comm (x : H.Regraded) : H.periodUnit * x = x * H.periodUnit := by
  induction x using induction_on with
  | zero => simp
  | mk p a ha => rw [periodUnit_mul_place, place_mul_periodUnit]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

/-- The inverse of the periodicity unit is central. -/
theorem periodUnitInv_mul_comm (x : H.Regraded) : H.periodUnitInv * x = x * H.periodUnitInv := by
  induction x using induction_on with
  | zero => simp
  | mk p a ha => rw [periodUnitInv_mul_place, place_mul_periodUnitInv]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

theorem periodUnit_mem_grading : H.periodUnit ∈ grading (M := H.Regraded) 2 :=
  place_mem_grading (H := H) (2, -2 * k) _

theorem periodUnit_mem_wgrading :
    H.periodUnit ∈ wgrading (M := H.Regraded) (-2 * k) :=
  place_mem_wgrading (H := H) (2, -2 * k) _

theorem periodUnitInv_mem_grading :
    H.periodUnitInv ∈ grading (M := H.Regraded) (-2) :=
  place_mem_grading (H := H) (-2, 2 * k) _

theorem periodUnitInv_mem_wgrading :
    H.periodUnitInv ∈ wgrading (M := H.Regraded) (2 * k) :=
  place_mem_wgrading (H := H) (-2, 2 * k) _

@[simp]
theorem d_periodUnit : d H.periodUnit = 0 := by
  rw [periodUnit, d_place]
  exact (place_congr rfl hd_one _ _).trans (place_zero _)

@[simp]
theorem d_periodUnitInv : d H.periodUnitInv = 0 := by
  rw [periodUnitInv, d_place]
  exact (place_congr rfl hd_one _ _).trans (place_zero _)

end PeriodUnit

end HalfGradedDGRing

end DG
