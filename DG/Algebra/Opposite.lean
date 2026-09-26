import DG.Algebra.Equiv
import DG.Graded.Opposite

/-!
# The opposite dg algebra

For a dg `R`-algebra `A`, the graded opposite algebra
`Aᵒᵖ = GradedOpposite (DGAlgebra.gradingSubmodule R A)` (a type synonym of `A`, with product
`op a * op b = (-1)^{|a||b|} • op (b * a)`, see `DG.Graded.Opposite`) is a dg `R`-algebra for the
same grading and the same differential, `d (op a) = op (d a)`.

## Main definitions and results

* `DG.GradedOpposite.instDGAddCommGroup`, `DG.GradedOpposite.instDGRing`,
  `DG.GradedOpposite.instDGAlgebra`: the dg algebra structure on `Aᵒᵖ`. The Leibniz rule for the
  signed opposite product is `DG.GradedOpposite.instDGRing`.
* `DG.GradedOpposite.d_op`, `DG.GradedOpposite.d_unop`: `op` and `unop` commute with `d`.
* `DG.GradedOpposite.opOpDGAlgEquiv`: the isomorphism of dg algebras `(Aᵒᵖ)ᵒᵖ ≃ A`.
* `DG.GradedOpposite.opDGAlgEquiv`: for graded commutative `A`, the isomorphism of dg algebras
  `A ≃ Aᵒᵖ` given by `op`.

The correspondence between right dg `A`-modules and left dg `Aᵒᵖ`-modules is in
`DG.Module.Opposite`.
-/

noncomputable section

namespace DG

private theorem ks_eq {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A]

local notation "𝒜" => DGAlgebra.gradingSubmodule R A
local notation "Aᵒᵖ" => GradedOpposite (DGAlgebra.gradingSubmodule R A)

/-- The dg abelian group structure of the opposite of a dg algebra: the grading of the graded
opposite algebra and the differential `d (op a) = op (d a)`. -/
instance GradedOpposite.instDGAddCommGroup : DGAddCommGroup Aᵒᵖ where
  grading i := (GradedOpposite.grading 𝒜 i).toAddSubgroup
  decomposition :=
    { decompose' := DirectSum.decompose (GradedOpposite.grading 𝒜)
      left_inv := DirectSum.Decomposition.left_inv (ℳ := GradedOpposite.grading 𝒜)
      right_inv := DirectSum.Decomposition.right_inv (ℳ := GradedOpposite.grading 𝒜) }
  d := (GradedOpposite.op 𝒜).toLinearMap.toAddMonoidHom.comp
    ((d : A →+ A).comp (GradedOpposite.unop 𝒜).toLinearMap.toAddMonoidHom)
  d_mem' {n x} hx := by
    change GradedOpposite.op 𝒜 (d (GradedOpposite.unop 𝒜 x)) ∈ GradedOpposite.grading 𝒜 (n + 1)
    exact GradedOpposite.op_mem_grading 𝒜 (d_mem ((GradedOpposite.mem_grading_iff 𝒜).mp hx))
  d_d' x := by
    change GradedOpposite.op 𝒜 (d (d (GradedOpposite.unop 𝒜 x))) = 0
    rw [d_d, map_zero]

namespace GradedOpposite

@[simp]
theorem d_op (a : A) : d (op 𝒜 a) = op 𝒜 (d a) := rfl

@[simp]
theorem d_unop (x : Aᵒᵖ) : d (unop 𝒜 x) = unop 𝒜 (d x) := rfl

theorem mem_dgGrading_iff {n : ℤ} {x : Aᵒᵖ} : x ∈ DG.grading n ↔ unop 𝒜 x ∈ DG.grading n :=
  mem_grading_iff 𝒜

theorem op_mem_dgGrading_iff {n : ℤ} {a : A} : op 𝒜 a ∈ DG.grading n ↔ a ∈ DG.grading n :=
  mem_grading_iff 𝒜

/-- The opposite of a dg algebra is a dg ring: the Leibniz rule holds for the signed opposite
product. -/
instance instDGRing : DGRing Aᵒᵖ where
  one_mem := (GradedOpposite.instGradedMonoid 𝒜).one_mem
  mul_mem := (GradedOpposite.instGradedMonoid 𝒜).mul_mem
  d_mul' {i x} hx y := by
    induction y using induction_on with
    | h_zero => simp
    | h_homogeneous y =>
      obtain ⟨y, hy⟩ := y
      rename_i j
      have ha : unop 𝒜 x ∈ DG.grading i := (mem_dgGrading_iff).mp hx
      have hb : unop 𝒜 y ∈ DG.grading j := (mem_dgGrading_iff).mp hy
      have hdx : d x ∈ DG.grading (i + 1) := d_mem hx
      have hdy : d y ∈ DG.grading (j + 1) := d_mem hy
      apply (unop 𝒜).injective
      rw [map_add, map_koszulSign_smul, ← d_unop, unop_mul 𝒜 hx hy, unop_mul 𝒜 hdx hy,
        unop_mul 𝒜 hx hdy, d_units_smul, d_mul hb, ← d_unop, ← d_unop]
      simp only [smul_add, smul_smul, ← koszulSign_add]
      rw [ks_eq (m := i * j + j) (n := (i + 1) * j) ⟨0, by ring⟩,
        ks_eq (m := i + i * (j + 1)) (n := i * j) ⟨i, by ring⟩]
      abel
    | h_add y y' hy hy' => rw [mul_add, d_add, hy, hy', d_add, mul_add, mul_add, smul_add]; abel

instance instDGAlgebra : DGAlgebra R Aᵒᵖ where
  algebraMap_mem' r := by
    rw [← op_algebraMap, op_mem_dgGrading_iff]
    exact algebraMap_mem_grading R r
  d_algebraMap' r := by
    rw [← op_algebraMap, d_op, d_algebraMap, map_zero]

theorem dgGrading_eq : DGAlgebra.gradingSubmodule R Aᵒᵖ = GradedOpposite.grading 𝒜 := rfl

/-- The double opposite of a dg algebra is isomorphic to it, via `unop ∘ unop`. -/
def opOpDGAlgEquiv : GradedOpposite (DGAlgebra.gradingSubmodule R Aᵒᵖ) ≃ᵈᵍₐ[R] A :=
  DGAlgEquiv.ofAlgEquiv (opOpAlgEquiv 𝒜) (fun hx => (opOpAlgEquiv_mem_iff 𝒜).mpr hx)
    fun _ => rfl

@[simp]
theorem opOpDGAlgEquiv_apply (x : GradedOpposite (DGAlgebra.gradingSubmodule R Aᵒᵖ)) :
    opOpDGAlgEquiv x = unop 𝒜 (unop (DGAlgebra.gradingSubmodule R Aᵒᵖ) x) := rfl

/-- A graded commutative dg algebra is isomorphic to its opposite, via `op`. -/
def opDGAlgEquiv [IsGradedComm 𝒜] : A ≃ᵈᵍₐ[R] Aᵒᵖ :=
  DGAlgEquiv.ofAlgEquiv (opAlgEquiv 𝒜) (fun ha => op_mem_grading 𝒜 ha) fun _ => rfl

@[simp]
theorem opDGAlgEquiv_apply [IsGradedComm 𝒜] (a : A) : opDGAlgEquiv a = op 𝒜 a := rfl

end GradedOpposite

end DG

end
