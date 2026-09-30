import DG.Module.Cohomology
import DG.Module.DirectSum

/-!
# Cohomology commutes with direct sums

For a family `M : ι → Type*` of dg abelian groups, the maps `Hⁿ(M i) → Hⁿ(⨁ i, M i)` induced by
the inclusions of the summands (`DG.cohomology.ofSummand`) induce an isomorphism

  `DG.cohomology.directSumAddEquiv M n : Hⁿ(⨁ i, M i) ≃+ ⨁ i, Hⁿ(M i)`,
whose components are induced by the projections (`DG.cohomology.component`). For families of
dg modules the inclusions are the morphisms `DG.DGModuleHom.lof`
(`DG.cohomology.directSumAddEquiv_map_lof`); these are the coproduct inclusions of
`DG.DGModuleCat` (`DG.DGModuleCat.coproductCocone`).
-/

open DirectSum

noncomputable section

namespace DG

variable {ι : Type*} [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, DGAddCommGroup (M i)]

namespace cohomology

/-- The map `Hⁿ(M i) → Hⁿ(⨁ i, M i)` induced by the inclusion of a summand. -/
def ofSummand (i : ι) (n : ℤ) : cohomology (M i) n →+ cohomology (⨁ i, M i) n :=
  mapAddMonoidHom (DirectSum.of M i) (fun hm => DirectSum.of_mem_grading M i hm)
    (fun m => (DirectSum.d_of M i m).symm) n

/-- The map `Hⁿ(⨁ i, M i) → Hⁿ(M i)` induced by the projection onto a summand. -/
def component (i : ι) (n : ℤ) : cohomology (⨁ i, M i) n →+ cohomology (M i) n :=
  mapAddMonoidHom (DFinsupp.evalAddMonoidHom i) (fun hx => (DirectSum.mem_grading M).mp hx i)
    (fun x => DirectSum.coe_d_apply M x i) n

variable {M}

/-- `DG.cohomology.ofSummand` on the class of a cocycle. -/
theorem ofSummand_mk (i : ι) (n : ℤ) (z : cocycles (M i) n) :
    ofSummand M i n (mk _ n z) = mk _ n ⟨DirectSum.of M i z, mem_cocycles.mpr
      ⟨DirectSum.of_mem_grading M i (cocycles.mem_grading z),
        by rw [DirectSum.d_of, cocycles.d_eq_zero z, _root_.map_zero]⟩⟩ :=
  mapAddMonoidHom_mk _ _ _ n z

/-- `DG.cohomology.component` on the class of a cocycle. -/
theorem component_mk (i : ι) (n : ℤ) (z : cocycles (⨁ i, M i) n) :
    component M i n (mk _ n z) = mk _ n ⟨(z : ⨁ i, M i) i, mem_cocycles.mpr
      ⟨(DirectSum.mem_grading M).mp (cocycles.mem_grading z) i,
        by rw [← DirectSum.coe_d_apply, cocycles.d_eq_zero z, DirectSum.zero_apply]⟩⟩ :=
  rfl

theorem component_ofSummand_self (i : ι) (n : ℤ) (y : cohomology (M i) n) :
    component M i n (ofSummand M i n y) = y := by
  induction y using induction_on with
  | h z =>
    rw [ofSummand_mk, component_mk]
    congr 1
    ext
    exact DirectSum.of_eq_same i _

theorem component_ofSummand_of_ne {i j : ι} (h : i ≠ j) (n : ℤ) (y : cohomology (M i) n) :
    component M j n (ofSummand M i n y) = 0 := by
  induction y using induction_on with
  | h z =>
    rw [ofSummand_mk, component_mk, mk_eq_zero_iff]
    change (DirectSum.of M i z) j ∈ _
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    exact zero_mem _

variable (M) in
/-- The comparison map `⨁ i, Hⁿ(M i) → Hⁿ(⨁ i, M i)` induced by the inclusions. -/
def fromDirectSum (n : ℤ) : (⨁ i, cohomology (M i) n) →+ cohomology (⨁ i, M i) n :=
  DirectSum.toAddMonoid fun i => ofSummand M i n

theorem fromDirectSum_of (n : ℤ) (i : ι) (y : cohomology (M i) n) :
    fromDirectSum M n (DirectSum.of _ i y) = ofSummand M i n y :=
  DirectSum.toAddMonoid_of (fun i => ofSummand M i n) i y

theorem component_fromDirectSum (n : ℤ) (x : ⨁ i, cohomology (M i) n) (j : ι) :
    component M j n (fromDirectSum M n x) = x j := by
  induction x using DirectSum.induction_on with
  | zero => rw [_root_.map_zero, _root_.map_zero, DirectSum.zero_apply]
  | of i y =>
    rw [fromDirectSum_of]
    by_cases h : i = j
    · subst h
      rw [component_ofSummand_self, DirectSum.of_eq_same]
    · rw [component_ofSummand_of_ne h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy, DirectSum.add_apply]

theorem fromDirectSum_injective (n : ℤ) : Function.Injective (fromDirectSum M n) := by
  intro x y h
  ext j
  rw [← component_fromDirectSum n x j, ← component_fromDirectSum n y j, h]

theorem fromDirectSum_surjective (n : ℤ) : Function.Surjective (fromDirectSum M n) := by
  classical
  intro x
  induction x using induction_on with
  | h z =>
    have hz : z = ∑ i ∈ (z : ⨁ i, M i).support, (⟨DirectSum.of M i ((z : ⨁ i, M i) i),
        mem_cocycles.mpr ⟨DirectSum.of_mem_grading M i
          ((DirectSum.mem_grading M).mp (cocycles.mem_grading z) i), by
          rw [DirectSum.d_of, ← DirectSum.coe_d_apply, cocycles.d_eq_zero z,
            DirectSum.zero_apply, _root_.map_zero]⟩⟩ : cocycles (⨁ i, M i) n) := by
      ext1
      rw [AddSubgroup.val_finsetSum]
      exact (DirectSum.sum_support_of _).symm
    rw [← AddMonoidHom.mem_range, hz, map_sum]
    refine sum_mem fun i _ => ⟨DirectSum.of _ i (mk _ n ⟨(z : ⨁ i, M i) i, mem_cocycles.mpr
      ⟨(DirectSum.mem_grading M).mp (cocycles.mem_grading z) i, by
        rw [← DirectSum.coe_d_apply, cocycles.d_eq_zero z, DirectSum.zero_apply]⟩⟩), ?_⟩
    rw [fromDirectSum_of, ofSummand_mk]

variable (M) in
/-- Cohomology commutes with arbitrary direct sums: `Hⁿ(⨁ i, M i) ≃+ ⨁ i, Hⁿ(M i)`. The
inverse is induced by the inclusions of the summands (`DG.cohomology.directSumAddEquiv_symm_of`,
`DG.cohomology.directSumAddEquiv_ofSummand`), and the components are induced by the
projections (`DG.cohomology.directSumAddEquiv_apply`). -/
def directSumAddEquiv (n : ℤ) :
    cohomology (⨁ i, M i) n ≃+ ⨁ i, cohomology (M i) n :=
  (AddEquiv.ofBijective (fromDirectSum M n)
    ⟨fromDirectSum_injective n, fromDirectSum_surjective n⟩).symm

theorem directSumAddEquiv_symm_apply (n : ℤ) (x : ⨁ i, cohomology (M i) n) :
    (directSumAddEquiv M n).symm x = fromDirectSum M n x :=
  rfl

theorem directSumAddEquiv_symm_of (n : ℤ) (i : ι) (y : cohomology (M i) n) :
    (directSumAddEquiv M n).symm (DirectSum.of _ i y) = ofSummand M i n y :=
  fromDirectSum_of n i y

/-- The isomorphism `Hⁿ(⨁ i, M i) ≃+ ⨁ i, Hⁿ(M i)` is compatible with the inclusions of the
summands. -/
theorem directSumAddEquiv_ofSummand (n : ℤ) (i : ι) (y : cohomology (M i) n) :
    directSumAddEquiv M n (ofSummand M i n y) = DirectSum.of _ i y := by
  rw [← directSumAddEquiv_symm_of, AddEquiv.apply_symm_apply]

/-- The components of `Hⁿ(⨁ i, M i) ≃+ ⨁ i, Hⁿ(M i)` are induced by the projections. -/
theorem directSumAddEquiv_apply (n : ℤ) (x : cohomology (⨁ i, M i) n) (j : ι) :
    directSumAddEquiv M n x j = component M j n x := by
  obtain ⟨y, rfl⟩ := (directSumAddEquiv M n).symm.surjective x
  rw [AddEquiv.apply_symm_apply, directSumAddEquiv_symm_apply, component_fromDirectSum]

section DGModule

variable {A : Type*} [Ring A] [DGAddCommGroup A] [∀ i, Module A (M i)]

/-- The map induced by the inclusion `DG.DGModuleHom.lof` is `DG.cohomology.ofSummand`. -/
theorem map_lof (n : ℤ) (i : ι) :
    map (DGModuleHom.lof A M i) n = ofSummand M i n :=
  rfl

/-- The isomorphism `Hⁿ(⨁ i, M i) ≃+ ⨁ i, Hⁿ(M i)` is compatible with the maps induced by the
inclusions `DG.DGModuleHom.lof` of dg modules. -/
theorem directSumAddEquiv_map_lof (n : ℤ) (i : ι) (y : cohomology (M i) n) :
    directSumAddEquiv M n (map (DGModuleHom.lof A M i) n y) = DirectSum.of _ i y :=
  directSumAddEquiv_ofSummand n i y

end DGModule

end cohomology

end DG

end
