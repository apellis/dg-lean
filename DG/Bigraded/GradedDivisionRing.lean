import DG.Bigraded.GradedSemisimple
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.Data.Matrix.Basis

/-!
# Graded division rings and graded matrix rings

Let `ι` be an abelian group. A ring `R` graded by `ι` is a *graded division ring*
(`DG.IsGradedDivisionRing 𝒜`) if `1 ≠ 0` and every nonzero homogeneous element has a homogeneous
left inverse. A graded division ring is graded semisimple (`1` is a graded simple idempotent).

For a finite set `n` with a degree function `p : n → ι`, the matrix ring `Mₙ(R)` is graded by
`(Mₙ(R))_i = {x | x_{ab} ∈ R_{i + p a - p b}}` (`DG.matrixGrading 𝒜 p`): the matrix unit `E_{ab}`
has degree `p a - p b`. Over a graded division ring this graded ring is graded semisimple, the
diagonal matrix units `E_{aa}` being orthogonal graded simple idempotents of degree `0` with sum
`1` (`DG.IsGradedDivisionRing.isGradedSemisimpleRing_matrixGrading`).

For `ι = ℤ/2` this covers the two families of simple superalgebras:

* `M(m|n)` over a division ring `D`: matrices over `D` (concentrated in degree `0`,
  `DG.trivialGrading`) with the parity `p = (0, …, 0, 1, …, 1)` of `Fin m ⊕ Fin n`
  (`DG.isGradedSemisimpleRing_superMatrix`);
* `Q(n) = Mₙ(K) ⊗ Cl₁` over a field `K`: `n × n` matrices over the Clifford algebra
  `Cl₁ = K[ℤ/2] = K ⊕ K c` with `c` odd and `c² = 1` (the group algebra of `ℤ/2`, graded by
  `ℤ/2`, `DG.groupAlgebraGrading`), with `p = 0` (`DG.isGradedSemisimpleRing_queerMatrix`).

The group algebra `K[ℤ/2]` is a graded division ring for every field `K`
(`DG.isGradedDivisionRing_groupAlgebraGrading`), hence graded semisimple, even in
characteristic `2`, where it is not semisimple as an ungraded ring (`c - 1` is nilpotent).

## Main definitions

* `DG.IsGradedDivisionRing 𝒜`, `DG.IsGradedDivisionRing.isGradedSemisimpleRing`.
* `DG.trivialGrading ι R`: the grading concentrated in degree `0`.
* `DG.matrixGrading 𝒜 p`, with its `GradedRing` instance (for `ι` finite).
* `DG.groupAlgebraGrading K G`: the grading of `K[G]` by `G`.
-/

open DirectSum

noncomputable section

namespace DG

/-! ### Graded division rings -/

section DivisionRing

variable {ι : Type*} [AddCommGroup ι] {R : Type*} [Ring R] (𝒜 : ι → AddSubgroup R)

/-- A graded ring is a *graded division ring* if `1 ≠ 0` and every nonzero homogeneous element
`x` of degree `i` has a left inverse of degree `-i`. -/
def IsGradedDivisionRing : Prop :=
  (1 : R) ≠ 0 ∧ ∀ ⦃i : ι⦄ ⦃x : R⦄, x ∈ 𝒜 i → x ≠ 0 → ∃ y ∈ 𝒜 (-i), y * x = 1

variable {𝒜}

/-- In a graded division ring, `1` is a graded simple idempotent. -/
theorem IsGradedDivisionRing.isGradedSimpleIdempotent_one (h : IsGradedDivisionRing 𝒜) :
    IsGradedSimpleIdempotent 𝒜 1 :=
  ⟨h.1, fun _ _ hx _ hx0 => h.2 hx hx0⟩

/-- A graded division ring is graded semisimple. -/
theorem IsGradedDivisionRing.isGradedSemisimpleRing [DecidableEq ι] [GradedRing 𝒜]
    (h : IsGradedDivisionRing 𝒜) : IsGradedSemisimpleRing 𝒜 := by
  refine isGradedSemisimpleRing_iff_exists_list.mpr ⟨[1], fun e he => ?_,
    List.pairwise_singleton _ _, List.sum_singleton⟩
  rw [List.mem_singleton] at he
  subst he
  exact ⟨SetLike.GradedOne.one_mem, IsIdempotentElem.one, h.isGradedSimpleIdempotent_one⟩

end DivisionRing

/-! ### The grading concentrated in degree `0` -/

section Trivial

variable (ι : Type*) [AddCommGroup ι] [DecidableEq ι] (R : Type*) [Ring R]

/-- The grading of a ring concentrated in degree `0`. -/
def trivialGrading (i : ι) : AddSubgroup R := if i = 0 then ⊤ else ⊥

variable {ι R}

theorem mem_trivialGrading_iff {i : ι} {x : R} : x ∈ trivialGrading ι R i ↔ i = 0 ∨ x = 0 := by
  unfold trivialGrading
  split_ifs with h <;> simp [h]

variable (ι R)

/-- The decomposition of a ring for the grading concentrated in degree `0`. -/
def trivialDecompose : R →+ ⨁ i, trivialGrading ι R i :=
  (DirectSum.of (fun i => trivialGrading ι R i) 0).comp
    { toFun := fun x => ⟨x, mem_trivialGrading_iff.mpr (Or.inl rfl)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

instance : Decomposition (trivialGrading ι R) :=
  Decomposition.ofAddHom _ (trivialDecompose ι R)
    (AddMonoidHom.ext fun x => by
      simp [trivialDecompose, DirectSum.coeAddMonoidHom_of])
    (DirectSum.addHom_ext fun i x => by
      obtain ⟨x, hx⟩ := x
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply,
        trivialDecompose, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rcases mem_trivialGrading_iff.mp hx with rfl | rfl
      · rfl
      · exact (map_zero (DirectSum.of (fun i => trivialGrading ι R i) 0)).trans
          (map_zero (DirectSum.of (fun i => trivialGrading ι R i) i)).symm)

instance : SetLike.GradedMonoid (trivialGrading ι R) where
  one_mem := mem_trivialGrading_iff.mpr (Or.inl rfl)
  mul_mem i j a b ha hb := by
    rcases mem_trivialGrading_iff.mp ha with rfl | rfl
    · rcases mem_trivialGrading_iff.mp hb with rfl | rfl
      · exact mem_trivialGrading_iff.mpr (Or.inl (add_zero 0))
      · rw [mul_zero]; exact zero_mem _
    · rw [zero_mul]; exact zero_mem _

instance : GradedRing (trivialGrading ι R) where

/-- A division ring concentrated in degree `0` is a graded division ring. -/
theorem isGradedDivisionRing_trivialGrading (D : Type*) [DivisionRing D] :
    IsGradedDivisionRing (trivialGrading ι D) := by
  refine ⟨one_ne_zero, fun i x hx hx0 => ⟨x⁻¹, ?_, inv_mul_cancel₀ hx0⟩⟩
  rcases mem_trivialGrading_iff.mp hx with rfl | h
  · exact mem_trivialGrading_iff.mpr (Or.inl neg_zero)
  · exact absurd h hx0

end Trivial

/-! ### Graded matrix rings -/

section Matrix

variable {ι : Type*} [AddCommGroup ι] {R : Type*} [Ring R] (𝒜 : ι → AddSubgroup R)
  {n : Type*} [DecidableEq n] (p : n → ι)

/-- The grading of the matrix ring `Mₙ(R)` for degrees `p : n → ι` of the basis vectors: a matrix
has degree `i` if its entry `(a, b)` has degree `i + p a - p b`. The matrix unit `E_{ab}` has
degree `p a - p b`. -/
def matrixGrading (i : ι) : AddSubgroup (Matrix n n R) where
  carrier := {x | ∀ a b, x a b ∈ 𝒜 (i + p a - p b)}
  add_mem' hx hy a b := add_mem (hx a b) (hy a b)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx a b := neg_mem (hx a b)

variable {𝒜 p}

omit [DecidableEq n] in
theorem mem_matrixGrading_iff {i : ι} {x : Matrix n n R} :
    x ∈ matrixGrading 𝒜 p i ↔ ∀ a b, x a b ∈ 𝒜 (i + p a - p b) :=
  Iff.rfl

theorem single_mem_matrixGrading {a b : n} {i : ι} {y : R} (hy : y ∈ 𝒜 (i + p a - p b)) :
    Matrix.single a b y ∈ matrixGrading 𝒜 p i := by
  intro a' b'
  by_cases h : a = a' ∧ b = b'
  · obtain ⟨rfl, rfl⟩ := h
    rwa [Matrix.single_apply_same]
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ h]
    exact zero_mem _

variable (𝒜 p)

instance [Fintype n] [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (matrixGrading 𝒜 p) where
  one_mem a b := by
    rw [Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [zero_add, sub_self]
      exact SetLike.GradedOne.one_mem
    · exact zero_mem _
  mul_mem i j x y hx hy a b := by
    rw [Matrix.mul_apply]
    refine sum_mem fun c _ => ?_
    have h := SetLike.GradedMul.mul_mem (hx a c) (hy c b)
    rwa [show i + p a - p c + (j + p c - p b) = i + j + p a - p b by abel] at h

variable [DecidableEq ι] [Decomposition 𝒜]

/-- The component of degree `i` of a matrix. -/
def matrixComponent (i : ι) : Matrix n n R →+ matrixGrading 𝒜 p i where
  toFun x := ⟨fun a b => decompose 𝒜 (x a b) (i + p a - p b), fun _ _ => SetLike.coe_mem _⟩
  map_zero' := Subtype.ext (funext₂ fun a b => by simp)
  map_add' x y := Subtype.ext (funext₂ fun a b => by
    simp only [Matrix.add_apply, decompose_add, DirectSum.add_apply, AddSubgroup.coe_add]
    rfl)

omit [DecidableEq n] in
theorem coe_matrixComponent_apply (i : ι) (x : Matrix n n R) (a b : n) :
    (matrixComponent 𝒜 p i x : Matrix n n R) a b = decompose 𝒜 (x a b) (i + p a - p b) :=
  rfl

variable [Fintype ι]

/-- The decomposition of a matrix into its homogeneous components. -/
def matrixDecompose : Matrix n n R →+ ⨁ i, matrixGrading 𝒜 p i :=
  ∑ i, (DirectSum.of (fun i => matrixGrading 𝒜 p i) i).comp (matrixComponent 𝒜 p i)

omit [AddCommGroup ι] [DecidableEq n] in
theorem sum_coe_decompose (r : R) : ∑ j, (decompose 𝒜 r j : R) = r := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  rw [DFinsupp.notMem_support_iff.mp hj, ZeroMemClass.coe_zero]

instance : Decomposition (matrixGrading 𝒜 p) :=
  Decomposition.ofAddHom _ (matrixDecompose 𝒜 p)
    (AddMonoidHom.ext fun x => by
      ext a b
      simp only [matrixDecompose, AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply,
        map_sum, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply, Matrix.sum_apply,
        coe_matrixComponent_apply]
      conv_rhs => rw [← sum_coe_decompose 𝒜 (x a b)]
      exact Fintype.sum_equiv (Equiv.addRight (p a - p b)) _ _ fun j => by
        simp only [Equiv.coe_addRight]
        rw [add_sub_assoc])
    (DirectSum.addHom_ext fun i x => by
      simp only [matrixDecompose, AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply,
        DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
      rw [Finset.sum_eq_single i]
      · congr 1
        refine Subtype.ext (funext₂ fun a b => ?_)
        rw [coe_matrixComponent_apply]
        exact decompose_of_mem_same 𝒜 (x.2 a b)
      · intro j _ hji
        have h0 : matrixComponent 𝒜 p j x = 0 := Subtype.ext (funext₂ fun a b => by
          rw [coe_matrixComponent_apply]
          exact decompose_of_mem_ne 𝒜 (x.2 a b) (fun h => hji (by simpa using h.symm)))
        rw [h0, map_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h)

instance [Fintype n] [SetLike.GradedMonoid 𝒜] : GradedRing (matrixGrading 𝒜 p) where

end Matrix

/-! ### Matrices over a graded division ring -/

section MatrixDivision

variable {ι : Type*} [AddCommGroup ι] {R : Type*} [Ring R] {𝒜 : ι → AddSubgroup R}
  {n : Type*} [Fintype n] [DecidableEq n] (p : n → ι)

/-- Over a graded division ring, the diagonal matrix unit `E_{cc}` is a graded simple
idempotent: a nonzero homogeneous `x` with `x E_{cc} = x` is supported in column `c`, and if
`y x_{ac} = 1` with `y` homogeneous, then `(y E_{ca}) x = E_{cc}`. -/
theorem IsGradedDivisionRing.isGradedSimpleIdempotent_single (h : IsGradedDivisionRing 𝒜)
    (c : n) : IsGradedSimpleIdempotent (matrixGrading 𝒜 p) (Matrix.single c c (1 : R)) := by
  refine ⟨fun h0 => h.1 (by rw [← Matrix.single_apply_same c c (1 : R), h0]; rfl),
    fun j x hx hxc hx0 => ?_⟩
  have hcol : ∀ a b, b ≠ c → x a b = 0 := fun a b hb => by
    rw [← hxc, Matrix.mul_single_apply_of_ne _ _ _ _ _ hb]
  obtain ⟨a, hac⟩ : ∃ a, x a c ≠ 0 := by
    by_contra! hall
    exact hx0 (Matrix.ext fun a b => by
      by_cases hb : b = c
      · subst hb; exact hall a
      · exact hcol a b hb)
  obtain ⟨y, hy, hyx⟩ := h.2 (hx a c) hac
  refine ⟨Matrix.single c a y, single_mem_matrixGrading (by
    rwa [show -j + p c - p a = -(j + p a - p c) by abel]), Matrix.ext fun r s => ?_⟩
  by_cases hr : r = c
  · subst hr
    rw [Matrix.single_mul_apply_same]
    by_cases hs : s = r
    · subst hs
      rw [hyx, Matrix.single_apply_same]
    · rw [hcol a s hs, mul_zero, Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hs h.2.symm)]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hr,
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hr h.1.symm)]

variable [DecidableEq ι] [Fintype ι] [GradedRing 𝒜]

/-- Matrices over a graded division ring (with arbitrary degrees of the basis vectors) form a
graded semisimple ring. -/
theorem IsGradedDivisionRing.isGradedSemisimpleRing_matrixGrading (h : IsGradedDivisionRing 𝒜) :
    IsGradedSemisimpleRing (matrixGrading 𝒜 p) := by
  classical
  refine isGradedSemisimpleRing_iff_exists_list.mpr
    ⟨(Finset.univ : Finset n).toList.map fun c => Matrix.single c c (1 : R),
      fun e he => ?_, ?_, ?_⟩
  · obtain ⟨c, -, rfl⟩ := List.mem_map.mp he
    refine ⟨single_mem_matrixGrading (by
        rw [zero_add, sub_self]
        exact SetLike.GradedOne.one_mem),
      by rw [IsIdempotentElem, Matrix.single_mul_single_same, mul_one],
      h.isGradedSimpleIdempotent_single p c⟩
  · rw [List.pairwise_map]
    exact (Finset.nodup_toList _).imp fun hab =>
      ⟨Matrix.single_mul_single_of_ne _ _ _ _ hab _,
        Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hab) _⟩
  · rw [Finset.sum_map_toList]
    exact Matrix.sum_single_one

end MatrixDivision

/-! ### Group algebras -/

section GroupAlgebra

variable (K : Type*) [Field K] (G : Type*) [AddCommGroup G] [DecidableEq G]

/-- The grading of the group algebra `K[G]` by `G`: `K[G]_g = K g`. -/
abbrev groupAlgebraGrading (g : G) : AddSubgroup (AddMonoidAlgebra K G) :=
  (AddMonoidAlgebra.grade K g).toAddSubgroup

instance : SetLike.GradedMonoid (groupAlgebraGrading K G) where
  one_mem := SetLike.GradedOne.one_mem (A := (AddMonoidAlgebra.grade K : G → Submodule K _))
  mul_mem _ _ _ _ ha hb :=
    SetLike.GradedMul.mul_mem (A := (AddMonoidAlgebra.grade K : G → Submodule K _)) ha hb

instance : Decomposition (groupAlgebraGrading K G) where
  decompose' := DirectSum.decompose (AddMonoidAlgebra.grade K : G → Submodule K _)
  left_inv := Decomposition.left_inv (ℳ := (AddMonoidAlgebra.grade K : G → Submodule K _))
  right_inv := Decomposition.right_inv (ℳ := (AddMonoidAlgebra.grade K : G → Submodule K _))

instance : GradedRing (groupAlgebraGrading K G) where

omit [DecidableEq G] in
/-- The group algebra of an abelian group over a field, graded by the group, is a graded
division ring: `(a⁻¹ (-g)) (a g) = 1`. -/
theorem isGradedDivisionRing_groupAlgebraGrading :
    IsGradedDivisionRing (groupAlgebraGrading K G) := by
  refine ⟨one_ne_zero, fun g x hx hx0 => ?_⟩
  obtain ⟨a, rfl⟩ := (AddMonoidAlgebra.mem_grade_iff' K g x).mp hx
  have ha : a ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  refine ⟨AddMonoidAlgebra.single (-g) a⁻¹, AddMonoidAlgebra.single_mem_grade _ _, ?_⟩
  change AddMonoidAlgebra.single (-g) a⁻¹ * AddMonoidAlgebra.single g a = 1
  rw [AddMonoidAlgebra.single_mul_single, neg_add_cancel, inv_mul_cancel₀ ha,
    AddMonoidAlgebra.one_def]

end GroupAlgebra

/-! ### The simple superalgebras `M(m|n)` and `Q(n)` -/

/-- The parity of the basis of `K^{m|n}`: `0` on the first `m` vectors, `1` on the last `n`. -/
def superParity (m n : ℕ) : Fin m ⊕ Fin n → ZMod 2 :=
  Sum.elim (fun _ => 0) (fun _ => 1)

/-- The matrix superalgebra `M(m|n)` over a division ring `D` (matrices on `D^{m|n}` with the
parity grading) is a `ℤ/2`-graded semisimple ring. -/
theorem isGradedSemisimpleRing_superMatrix (D : Type*) [DivisionRing D] (m n : ℕ) :
    IsGradedSemisimpleRing (matrixGrading (trivialGrading (ZMod 2) D) (superParity m n)) :=
  (isGradedDivisionRing_trivialGrading (ZMod 2) D).isGradedSemisimpleRing_matrixGrading _

/-- The queer matrix superalgebra `Q(n) = Mₙ(K) ⊗ Cl₁`, realized as `n × n` matrices over the
Clifford algebra `Cl₁ = K[ℤ/2]` (`c` odd, `c² = 1`) with even matrix units, is a `ℤ/2`-graded
semisimple ring, over every field `K`. -/
theorem isGradedSemisimpleRing_queerMatrix (K : Type*) [Field K] (n : ℕ) :
    IsGradedSemisimpleRing (matrixGrading (groupAlgebraGrading K (ZMod 2)) (0 : Fin n → ZMod 2)) :=
  (isGradedDivisionRing_groupAlgebraGrading K (ZMod 2)).isGradedSemisimpleRing_matrixGrading _

end DG

end
