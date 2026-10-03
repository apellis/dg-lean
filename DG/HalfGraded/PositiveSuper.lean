import DG.HalfGraded.Positive
import DG.Bigraded.GradedDivisionRing

/-!
# Positive half-graded dg rings with odd elements of internal degree `0`

For a positive half-graded dg ring `H` (`DG.HalfGradedDGRing.IsPositive`) the part `A^{0,•}` of
internal degree `0` is a graded semisimple `ℤ/2`-graded ring. Its graded simple modules are of two
kinds: those not isomorphic to their parity shift (for instance the simple modules of `M(m|n)`),
and those isomorphic to their parity shift by an odd isomorphism (*type Q*, for instance the
simple module of the Clifford algebra `Cl₁`). This file treats the second kind on `K₀`.

## Main results

* `DG.HalfGradedDGRing.isPositive_ofSuper`: a graded semisimple superring placed in internal
  degree `0` (`DG.HalfGradedDGRing.ofSuper`) is positive, for every `k > 0`; in particular
  `M(m|n)` over a division ring (`isPositive_ofSuper_superMatrix`) and `Q(n) = Mₙ(K) ⊗ Cl₁`
  over a field (`isPositive_ofSuper_queerMatrix`).
* `DG.HalfGradedDGRing.IsPositive.T_neg_smul_eq_neg`: if `A^{0,1̄}` contains an odd unit `c`
  (with odd inverse `c'`) such that `c' e c = e` for every `e ∈ A^{0,0̄}`, then
  `q⁻ᵏ x = -x` for every `x ∈ K₀(C_H)`: the closed isomorphism `c` of degree `1` between `w + k`
  and `w` identifies every generating class `[e · C_H(w, -)]` with `-q⁻ᵏ` times itself.
  Consequently (`DG.HalfGradedDGRing.IsPositive.mk_parityShiftCompact_eq_mk`) `[Π X] = [X]` in
  the (even) Grothendieck group `K₀(D(C_H)^c)`: the parity relations of the super Grothendieck
  group are already satisfied.
* The Clifford algebra `Cl₁ = K[ℤ/2]` over a field `K` (`c` odd, `c² = 1`), placed in internal
  degree `0` (`DG.HalfGradedDGRing.clifford`): it is positive (`isPositive_clifford`), it has a
  nonzero odd part of internal degree `0` (`clifford_odd_ne_zero`), so that it does not satisfy
  the positivity conditions with `A^{0,1̄} = 0`, and `[Π X] = [X]` for all compact `X`
  (`clifford_mk_parityShiftCompact`). By contrast, over `K` itself
  (`DG.HalfGradedDGRing.Field.cls_parityShift`) `[Π K] = -qᵏ [K] ≠ [K]`.
-/

open CategoryTheory DirectSum LaurentPolynomial

universe w u

noncomputable section

namespace DG

namespace HalfGradedDGRing

/-! ### Superrings placed in internal degree `0` -/

section OfSuper

variable {B : Type u} [Ring B] {ℬ : ZMod 2 → AddSubgroup B} [GradedRing ℬ]

/-- A graded semisimple superring placed in internal degree `0` is a positive half-graded dg ring,
for every `k > 0`. -/
theorem isPositive_ofSuper {k : ℤ} (hk : 0 < k) (h : IsGradedSemisimpleRing ℬ) :
    (ofSuper ℬ k).IsPositive where
  pos := hk
  eq_zero_of_lt _ hj ha := eq_zero_of_mem_superGrading hj ha
  isGradedSemisimple := isGradedSemisimpleRing_internalZeroGrading_ofSuper k h
  hd_eq_zero _ := rfl

end OfSuper

/-- The matrix superalgebra `M(m|n)` over a division ring, placed in internal degree `0`, is
positive. -/
theorem isPositive_ofSuper_superMatrix (D : Type u) [DivisionRing D] (m n : ℕ) {k : ℤ}
    (hk : 0 < k) :
    (ofSuper (matrixGrading (trivialGrading (ZMod 2) D) (superParity m n)) k).IsPositive :=
  isPositive_ofSuper hk (isGradedSemisimpleRing_superMatrix D m n)

/-- The queer matrix superalgebra `Q(n) = Mₙ(K) ⊗ Cl₁` over a field, placed in internal degree
`0`, is positive. -/
theorem isPositive_ofSuper_queerMatrix (K : Type u) [Field K] (n : ℕ) {k : ℤ} (hk : 0 < k) :
    (ofSuper (matrixGrading (groupAlgebraGrading K (ZMod 2)) (0 : Fin n → ZMod 2)) k).IsPositive :=
  isPositive_ofSuper hk (isGradedSemisimpleRing_queerMatrix K n)

/-! ### Odd units of internal degree `0` -/

variable {A : Type u} [Ring A] {k : ℤ} {H : HalfGradedDGRing A k}

theorem halfDegree_one_neg (k : ℤ) : halfDegree k ((1 : ℤ), -k) = ((0 : ℤ), (1 : ZMod 2)) :=
  Prod.ext (by simp) (by simp)

theorem halfDegree_neg_one (k : ℤ) : halfDegree k ((-1 : ℤ), k) = ((0 : ℤ), (1 : ZMod 2)) :=
  Prod.ext (by simp) (by simp)

variable {c c' : A}

/-- An odd element `c ∈ A^{0,1̄}`, as a morphism `w + k ⟶ w` of degree `1` of `C_H`. -/
def oddHom (hc : c ∈ H.hgrading (0, 1)) (X : WeightCategory H.Regraded) :
    (⟨X.as + k⟩ : WeightCategory H.Regraded) ⟶ X :=
  WeightCategory.homMk (H.place ((1 : ℤ), -k) c (by rw [halfDegree_one_neg]; exact hc)) (by
    rw [show X.as - (X.as + k) = -k by ring]
    exact place_mem_wgrading (H := H) ((1 : ℤ), -k) _)

/-- An odd element `c' ∈ A^{0,1̄}`, as a morphism `w ⟶ w + k` of degree `-1` of `C_H`. -/
def oddHomInv (hc' : c' ∈ H.hgrading (0, 1)) (X : WeightCategory H.Regraded) :
    X ⟶ (⟨X.as + k⟩ : WeightCategory H.Regraded) :=
  WeightCategory.homMk (H.place ((-1 : ℤ), k) c' (by rw [halfDegree_neg_one]; exact hc')) (by
    rw [show X.as + k - X.as = k by ring]
    exact place_mem_wgrading (H := H) ((-1 : ℤ), k) _)

theorem oddHomInv_comp_oddHom (hc : c ∈ H.hgrading (0, 1)) (hc' : c' ∈ H.hgrading (0, 1))
    (h1 : c * c' = 1) (X : WeightCategory H.Regraded) :
    oddHomInv hc' X ≫ oddHom hc X = 𝟙 X := by
  refine WeightCategory.hom_ext ?_
  rw [WeightCategory.comp_val, WeightCategory.id_val]
  change H.place ((1 : ℤ), -k) c _ * H.place ((-1 : ℤ), k) c' _ = 1
  rw [place_mul_place, one_eq_place]
  exact place_congr (by simp) h1 _ _

namespace IsPositive

variable (hH : H.IsPositive)
include hH

theorem oddHom_mem_cocycles (hc : c ∈ H.hgrading (0, 1)) (X : WeightCategory H.Regraded) :
    oddHom hc X ∈ cocycles ((⟨X.as + k⟩ : WeightCategory H.Regraded) ⟶ X) 1 :=
  mem_cocycles.mpr ⟨WeightCategory.mem_grading_iff.mpr
      (place_mem_grading (H := H) ((1 : ℤ), -k) _),
    WeightCategory.hom_ext (by
      rw [WeightCategory.d_val]
      change d (H.place ((1 : ℤ), -k) c _) = 0
      rw [d_place]
      exact (place_congr rfl (hH.hd_eq_zero hc) _ _).trans (place_zero _))⟩

variable [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory H.Regraded)]

/-- If `c ∈ A^{0,1̄}` has a right inverse `c' ∈ A^{0,1̄}` with `c' a c = a` for `a ∈ A^{0,0̄}`,
then `q⁻ᵏ [e · C_H(w, -)] = -[e · C_H(w, -)]` for every degree-`0` idempotent `e` of `w`: the
cocycle `c` of degree `1` identifies `e · C_H(w + k, -)` with `(e · C_H(w, -))⟦-1⟧`. -/
theorem T_neg_smul_cell (hc : c ∈ H.hgrading (0, 1)) (hc' : c' ∈ H.hgrading (0, 1))
    (h1 : c * c' = 1) (hce : ∀ {a : A}, a ∈ H.hgrading 0 → c' * a * c = a)
    {X : WeightCategory H.Regraded} (e : DGCategory.Idempotent X) :
    (T (-k) : LaurentPolynomial ℤ) • DGCategory.K0.cell.{max u w} e 0 =
      -DGCategory.K0.cell.{max u w} e 0 := by
  let Y : WeightCategory H.Regraded := ⟨X.as + k⟩
  let f := WeightCategory.idempotentAt e Y
  have hT := WeightCategory.T_smul_cell.{max u w} (-k) e f (by
    change X.as + k = X.as - -k
    ring) rfl
  rw [hT]
  have hcell := DGCategory.K0.cell_eq_of_comp_eq.{max u w} (hH.oddHom_mem_cocycles hc X)
    (oddHomInv_comp_oddHom hc hc' h1 X) e f (by
      obtain ⟨a, ha, hea⟩ := exists_eq_place (H := H)
        (WeightCategory.mem_grading_iff.mp e.mem_grading)
        (WeightCategory.mem_wgrading_of_eq (sub_self _) e.val.2)
      have ha0 : a ∈ H.hgrading 0 := by
        rwa [show halfDegree k ((0 : ℤ), (0 : ℤ)) = 0 from map_zero (halfDegree k)] at ha
      refine WeightCategory.hom_ext ?_
      rw [WeightCategory.comp_val, WeightCategory.comp_val]
      change e.val.1 = H.place ((-1 : ℤ), k) c' _ * e.val.1 * H.place ((1 : ℤ), -k) c _
      rw [hea, place_mul_place, place_mul_place]
      exact place_congr (by simp) (hce ha0).symm _ _)
  rw [hcell, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]

/-- If `A^{0,1̄}` contains `c` with a right inverse `c' ∈ A^{0,1̄}` such that `c' a c = a` for
`a ∈ A^{0,0̄}`, then `q⁻ᵏ x = -x` for every `x ∈ K₀(C_H)`. -/
theorem T_neg_smul_eq_neg (hc : c ∈ H.hgrading (0, 1)) (hc' : c' ∈ H.hgrading (0, 1))
    (h1 : c * c' = 1) (hce : ∀ {a : A}, a ∈ H.hgrading 0 → c' * a * c = a)
    (x : DGCategory.K0.{max u w, max u w} (WeightCategory H.Regraded)) :
    (T (-k) : LaurentPolynomial ℤ) • x = -x := by
  have hx : x ∈ AddSubgroup.closure
      (Set.range fun c : DGCategory.Corner (WeightCategory H.Regraded) =>
        DGCategory.K0.cell.{max u w} c.2 0) := by
    rw [hH.closure_cell_eq_top.{w}]
    trivial
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨e, rfl⟩ := hy
    exact hH.T_neg_smul_cell hc hc' h1 hce e.2
  | zero => rw [smul_zero, neg_zero]
  | add x y _ _ hx hy => rw [smul_add, hx, hy, neg_add]
  | neg x _ hx => rw [smul_neg, hx]

/-- If `A^{0,1̄}` contains `c` with a right inverse `c' ∈ A^{0,1̄}` such that `c' a c = a` for
`a ∈ A^{0,0̄}`, then `[Π X] = [X]` in the Grothendieck group of `D(C_H)^c`, for every compact
`X`: the parity relations defining the super Grothendieck group hold in `K₀`. -/
theorem mk_parityShiftCompact_eq_mk (hc : c ∈ H.hgrading (0, 1))
    (hc' : c' ∈ H.hgrading (0, 1)) (h1 : c * c' = 1)
    (hce : ∀ {a : A}, a ∈ H.hgrading 0 → c' * a * c = a)
    (X : (compactSubcategory.{max u w}
      (CatModule.DerivedCategory.{max u w, max u w} (WeightCategory H.Regraded))).FullSubcategory) :
    K0.mk (parityShiftCompact H X) = K0.mk X := by
  rw [mk_parityShiftCompact.{max u w, w}, hH.T_neg_smul_eq_neg hc hc' h1 hce, neg_neg]

end IsPositive

/-! ### The Clifford algebra `Cl₁` -/

section Clifford

variable (K : Type u) [Field K]

/-- The Clifford algebra `Cl₁ = K[ℤ/2] = K ⊕ K c` (`c` odd, `c² = 1`) placed in internal degree
`0`, as a half-graded dg ring with parameter `k`. -/
abbrev clifford (k : ℤ) : HalfGradedDGRing (AddMonoidAlgebra K (ZMod 2)) k :=
  ofSuper (groupAlgebraGrading K (ZMod 2)) k

/-- The odd generator `c` of `Cl₁`. -/
abbrev cliffordGen : AddMonoidAlgebra K (ZMod 2) := AddMonoidAlgebra.single 1 1

variable {K}

theorem cliffordGen_mem (k : ℤ) : cliffordGen K ∈ (clifford K k).hgrading (0, 1) := by
  rw [ofSuper_hgrading, superGrading_zero]
  exact AddMonoidAlgebra.single_mem_grade _ _

theorem cliffordGen_mul_self : cliffordGen K * cliffordGen K = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def]
  rfl

/-- `Cl₁` placed in internal degree `0` is positive, for every `k > 0`. -/
theorem isPositive_clifford {k : ℤ} (hk : 0 < k) : (clifford K k).IsPositive :=
  isPositive_ofSuper hk (isGradedDivisionRing_groupAlgebraGrading K (ZMod 2)).isGradedSemisimpleRing

/-- `Cl₁` has a nonzero odd element of internal degree `0`: it does not satisfy the positivity
conditions with `A^{0,1̄} = 0`. -/
theorem clifford_odd_ne_zero (k : ℤ) :
    ∃ a ∈ (clifford K k).hgrading (0, 1), a ≠ 0 :=
  ⟨cliffordGen K, cliffordGen_mem k, fun h => one_ne_zero (by
    rw [← cliffordGen_mul_self (K := K), h, zero_mul])⟩

variable [CatModule.HasDerivedCategory.{max u w, max u w}
  (WeightCategory (clifford K k).Regraded)]

/-- For `Cl₁` placed in internal degree `0`, `q⁻ᵏ x = -x` for every `x ∈ K₀(C_H)`. -/
theorem clifford_T_neg_smul (hk : 0 < k)
    (x : DGCategory.K0.{max u w, max u w} (WeightCategory (clifford K k).Regraded)) :
    (T (-k) : LaurentPolynomial ℤ) • x = -x :=
  (isPositive_clifford hk).T_neg_smul_eq_neg (cliffordGen_mem k) (cliffordGen_mem k)
    cliffordGen_mul_self (fun {a} _ => by rw [mul_comm _ a, mul_assoc, cliffordGen_mul_self,
      mul_one]) x

/-- For `Cl₁` placed in internal degree `0`, `[Π X] = [X]` in the Grothendieck group of compact
half-graded dg modules: the simple `Cl₁`-module is isomorphic to its parity shift by an odd
isomorphism. -/
theorem clifford_mk_parityShiftCompact (hk : 0 < k)
    (X : (compactSubcategory.{max u w} (CatModule.DerivedCategory.{max u w, max u w}
      (WeightCategory (clifford K k).Regraded))).FullSubcategory) :
    K0.mk (parityShiftCompact (clifford K k) X) = K0.mk X :=
  (isPositive_clifford hk).mk_parityShiftCompact_eq_mk (cliffordGen_mem k) (cliffordGen_mem k)
    cliffordGen_mul_self (fun {a} _ => by rw [mul_comm _ a, mul_assoc, cliffordGen_mul_self,
      mul_one]) X

end Clifford

end HalfGradedDGRing

end DG

end
