import DG.Derived.Basic

/-!
# Dg rings with vanishing derived category

For a dg ring `A` the following are equivalent [Keller, *Deriving DG categories*, Ex. 6.1]:

* the derived category `D(A)` is zero (every object is a zero object);
* the cohomology `H(A)` vanishes (`A` is acyclic);
* there is `x ∈ A` with `d x = 1`.

If `d x = 1`, then `x` may be taken of degree `-1`, and every dg module `M` is acyclic: for a
cocycle `m`, `d (x • m) = d x • m = m`. Conversely, `H(A) = 0` gives `x` since `1` is a cocycle,
and if `D(A)` is zero then `A`, as a dg module over itself, is acyclic.

## Main results

* `DG.exists_mem_grading_d_eq_one`: if `d x = 1`, some `y` of degree `-1` has `d y = 1`.
* `DG.IsAcyclic.of_exists_d_eq_one`: if `d x = 1`, every dg `A`-module is acyclic.
* `DG.isAcyclic_iff_exists_d_eq_one`: `H(A) = 0 ↔ ∃ x, d x = 1`.
* `DG.DerivedCategory.tfae_isZero`: the three conditions above are equivalent.
-/

open CategoryTheory Limits DirectSum

universe w u

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- If `d x = 1`, the component of degree `-1` of `x` also satisfies `d y = 1`. -/
theorem exists_mem_grading_d_eq_one {x : A} (hx : d x = 1) :
    ∃ y ∈ grading (M := A) (-1), d y = 1 := by
  refine ⟨decompose (grading (M := A)) x (-1), SetLike.coe_mem _, ?_⟩
  have h := decompose_d x (-1)
  rw [show (-1 : ℤ) + 1 = 0 by norm_num, hx,
    decompose_of_mem_same _ (one_mem_grading (A := A))] at h
  exact h.symm

/-- If some `x` has `d x = 1`, every dg `A`-module is acyclic. -/
theorem IsAcyclic.of_exists_d_eq_one {x : A} (hx : d x = 1) (M : Type*) [AddCommGroup M]
    [DGAddCommGroup M] [Module A M] [DGModule A M] : IsAcyclic M := by
  obtain ⟨y, hy, hdy⟩ := exists_mem_grading_d_eq_one hx
  refine isAcyclic_iff.mpr fun n m hm hdm => ⟨y • m, ?_, ?_⟩
  · have := smul_mem_grading hy hm
    rwa [neg_add_eq_sub] at this
  · rw [d_smul_of_d_eq_zero_right hdm, hdy, one_smul]

/-- A dg ring is acyclic iff `1` is a coboundary. -/
theorem isAcyclic_iff_exists_d_eq_one : IsAcyclic A ↔ ∃ x : A, d x = 1 := by
  constructor
  · intro h
    obtain ⟨x, -, hx⟩ := isAcyclic_iff.mp h 0 1 one_mem_grading d_one
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact IsAcyclic.of_exists_d_eq_one hx A

namespace DerivedCategory

/-- For a dg ring `A`, the following are equivalent: the derived category `D(A)` (of dg modules
with values in the universe of `A`) is zero; `H(A) = 0`; `d x = 1` for some `x ∈ A`
[Keller, *Deriving DG categories*, Ex. 6.1]. -/
theorem tfae_isZero [HasDerivedCategory.{w, u} A] :
    List.TFAE [∀ X : DerivedCategory A, IsZero X, IsAcyclic A, ∃ x : A, d x = 1] := by
  tfae_have 1 → 2 := fun h =>
    (isZero_Q_obj_iff (DGModuleCat.of A A)).mp (h _)
  tfae_have 2 ↔ 3 := isAcyclic_iff_exists_d_eq_one
  tfae_have 3 → 1 := by
    rintro ⟨x, hx⟩ X
    obtain ⟨Z, ⟨e⟩⟩ :=
      (Localization.essSurj (Qh (A := A)) (HomotopyCategory.quasiIso A)).mem_essImage X
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    exact IsZero.of_iso ((isZero_Q_obj_iff M).mpr (IsAcyclic.of_exists_d_eq_one hx M)) e.symm
  tfae_finish

end DerivedCategory

end DG
