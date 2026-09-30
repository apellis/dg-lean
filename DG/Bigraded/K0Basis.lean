import DG.Bigraded.DegreeZero
import DG.Bigraded.K0Morita
import DG.Bigraded.SchnurerK0
import DG.K0.PositiveCategoryBasis

/-!
# `K₀` of a positive bigraded dg ring over `ℤ[q, q⁻¹]`

Let `A` be a bigraded dg ring, `C_A` its weight dg category and `K₀(C_A) = K₀(D^c(C_A))` the
Grothendieck group of compact bigraded dg modules, a `ℤ[q, q⁻¹]`-module with `qⁿ • [M] = [M⟨n⟩]`.
This file proves the `K₀` statements of Roadmap 7.2.

## (a) The graded version

For `A` graded positive (`DG.IsGradedPositive A`), with degree-`0` part `A⁰`
(`DG.IsGradedPositive.degreeZeroDGSubring`, a bigraded dg ring concentrated in degree `0`):

* `DG.IsGradedPositive.K0DegreeZeroEquiv : K₀(C_A) ≃ₗ[ℤ[q, q⁻¹]] K₀(C_{A⁰})`, induced by the
  projection `A → A⁰`, with inverse induced by the inclusion `A⁰ → A` (on weight dg categories,
  by derived induction); it sends `[e · C_A(k, -)]` to `[e · C_{A⁰}(k, -)]`
  (`DG.IsGradedPositive.K0DegreeZeroEquiv_cell`). One composite is `K₀` of
  `C_{A⁰} ⥤ C_A ⥤ C_{A⁰}`, the identity; the other is the identity on the generators
  `[e · C_A(k, -)]` of `K₀(C_A)` (Schnürer's theorem). Linearity over `ℤ[q, q⁻¹]` is checked on
  the same generators, using `qˢ [e · C(k, -)] = [e · C(k - s, -)]`.

`K₀(C_{A⁰})` need not be free over `ℤ[q, q⁻¹]` (a graded simple module isomorphic to its shift
`⟨d⟩` contributes `ℤ[q, q⁻¹]/(q^d - 1)`), so no freeness is claimed in (a). It is always free as
an abelian group (`DG.DGCategory.IsPositive.basisOfConcentrated`).
-/

open CategoryTheory Limits

universe w u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

open CatModule CatModule.DerivedCategory DGCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A]

namespace IsGradedPositive

variable (hA : IsGradedPositive A)

/-! ### Idempotents of `C_A` and `C_{A⁰}` -/

omit [DGRing A] in
theorem _root_.DG.WeightCategory.idempotent_ext {k : WeightCategory A}
    {e f : Idempotent k} (h : e.val.1 = f.val.1) : e = f := by
  obtain ⟨e, he, he'⟩ := e
  obtain ⟨f, hf, hf'⟩ := f
  obtain rfl : e = f := WeightCategory.hom_ext h
  rfl

theorem map_projFunctor_map_inclFunctor {k : WeightCategory A} (e : Idempotent k) :
    (e.map hA.projFunctor).map hA.inclFunctor = e :=
  WeightCategory.idempotent_ext (hA.projZero_apply_of_mem_zero e.mem_grading)

theorem map_inclFunctor_map_projFunctor {k : WeightCategory hA.degreeZeroDGSubring}
    (e : Idempotent k) : (e.map hA.inclFunctor).map hA.projFunctor = e :=
  WeightCategory.idempotent_ext (Subtype.ext (hA.projZero_apply_of_mem_zero e.val.1.2))

/-! ### `K₀(C_A) ≅ K₀(C_{A⁰})` -/

variable [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory hA.degreeZeroDGSubring)]

/-- The homomorphism `K₀(C_A) → K₀(C_{A⁰})` induced by the projection `A → A⁰`. -/
abbrev K0DegreeZeroMap :
    DGCategory.K0.{max u w, max u w} (WeightCategory A) →+
      DGCategory.K0.{max u w, max u w} (WeightCategory hA.degreeZeroDGSubring) :=
  DGCategory.K0.map.{max u w, max u w} hA.projFunctor

/-- The homomorphism `K₀(C_{A⁰}) → K₀(C_A)` induced by the inclusion `A⁰ → A`. -/
abbrev K0DegreeZeroInv :
    DGCategory.K0.{max u w, max u w} (WeightCategory hA.degreeZeroDGSubring) →+
      DGCategory.K0.{max u w, max u w} (WeightCategory A) :=
  DGCategory.K0.map.{max u w, max u w} hA.inclFunctor

theorem K0DegreeZeroMap_cell {k : WeightCategory A} (e : Idempotent k) :
    hA.K0DegreeZeroMap (DGCategory.K0.cell.{max u w} e 0) =
      DGCategory.K0.cell.{max u w} (e.map hA.projFunctor) 0 :=
  DGCategory.K0.map_cell.{max u w} _ e

theorem K0DegreeZeroInv_cell {k : WeightCategory hA.degreeZeroDGSubring} (e : Idempotent k) :
    hA.K0DegreeZeroInv (DGCategory.K0.cell.{max u w} e 0) =
      DGCategory.K0.cell.{max u w} (e.map hA.inclFunctor) 0 :=
  DGCategory.K0.map_cell.{max u w} _ e

theorem K0DegreeZeroInv_comp_map :
    hA.K0DegreeZeroInv.comp hA.K0DegreeZeroMap = AddMonoidHom.id _ := by
  refine AddMonoidHom.eq_of_eqOn_dense
    (hA.isPositive_weightCategory.closure_cell_eq_top.{max u w}) ?_
  rintro _ ⟨c, rfl⟩
  rw [AddMonoidHom.comp_apply, K0DegreeZeroMap_cell, K0DegreeZeroInv_cell,
    map_projFunctor_map_inclFunctor, AddMonoidHom.id_apply]

theorem K0DegreeZeroMap_comp_inv :
    hA.K0DegreeZeroMap.comp hA.K0DegreeZeroInv = AddMonoidHom.id _ := by
  refine AddMonoidHom.eq_of_eqOn_dense (hA.isGradedPositive_degreeZeroDGSubring
    |>.isPositive_weightCategory.closure_cell_eq_top.{max u w}) ?_
  rintro _ ⟨c, rfl⟩
  rw [AddMonoidHom.comp_apply, K0DegreeZeroInv_cell, K0DegreeZeroMap_cell,
    map_inclFunctor_map_projFunctor, AddMonoidHom.id_apply]

/-- The map `K₀(C_A) → K₀(C_{A⁰})` commutes with `qˢ`, checked on the generators
`[e · C_A(k, -)]`. -/
theorem K0DegreeZeroMap_T_smul (s : ℤ) (x : DGCategory.K0.{max u w, max u w} (WeightCategory A)) :
    hA.K0DegreeZeroMap ((LaurentPolynomial.T s : LaurentPolynomial ℤ) • x) =
      (LaurentPolynomial.T s : LaurentPolynomial ℤ) • hA.K0DegreeZeroMap x := by
  have hx : x ∈ AddSubgroup.closure (Set.range fun c : SimpleCorner (WeightCategory A) =>
      DGCategory.K0.cell.{max u w} c.1.2 0) := by
    rw [hA.isPositive_weightCategory.closure_cell_eq_top.{max u w}]
    trivial
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨⟨k, e⟩, -⟩, rfl⟩ := hy
    let e' := WeightCategory.idempotentAt e ⟨k.as - s⟩
    rw [WeightCategory.T_smul_cell.{max u w} s e e' rfl rfl, K0DegreeZeroMap_cell,
      K0DegreeZeroMap_cell,
      WeightCategory.T_smul_cell.{max u w} s (e.map hA.projFunctor) (e'.map hA.projFunctor) rfl
        rfl]
  | zero => rw [_root_.smul_zero, map_zero, _root_.smul_zero]
  | add x y _ _ hx hy => rw [_root_.smul_add, map_add, map_add, hx, hy, _root_.smul_add]
  | neg x _ hx => rw [_root_.smul_neg, map_neg, map_neg, hx, _root_.smul_neg]

/-- **`K₀(C_A) ≅ K₀(C_{A⁰})` as `ℤ[q, q⁻¹]`-modules** for a graded positive bigraded dg ring
(Roadmap 7.2 (a)): the isomorphism is induced by the projection `A → A⁰`, with inverse induced
by the inclusion `A⁰ → A`, and sends `[e · C_A(k, -)]` to `[e · C_{A⁰}(k, -)]`
(`DG.IsGradedPositive.K0DegreeZeroEquiv_cell`). -/
def K0DegreeZeroEquiv :
    DGCategory.K0.{max u w, max u w} (WeightCategory A) ≃ₗ[LaurentPolynomial ℤ]
      DGCategory.K0.{max u w, max u w} (WeightCategory hA.degreeZeroDGSubring) :=
  { TriangulatedIntAction.linearMapOfCommute (compactInternalShiftAction A)
      (compactInternalShiftAction hA.degreeZeroDGSubring) hA.K0DegreeZeroMap fun n x => by
        rw [← TriangulatedIntAction.T_smul, ← TriangulatedIntAction.T_smul]
        exact hA.K0DegreeZeroMap_T_smul n x with
    invFun := hA.K0DegreeZeroInv
    left_inv := fun x => DFunLike.congr_fun hA.K0DegreeZeroInv_comp_map x
    right_inv := fun x => DFunLike.congr_fun hA.K0DegreeZeroMap_comp_inv x }

theorem K0DegreeZeroEquiv_apply (x : DGCategory.K0.{max u w, max u w} (WeightCategory A)) :
    hA.K0DegreeZeroEquiv x = hA.K0DegreeZeroMap x :=
  rfl

theorem K0DegreeZeroEquiv_symm_apply
    (x : DGCategory.K0.{max u w, max u w} (WeightCategory hA.degreeZeroDGSubring)) :
    hA.K0DegreeZeroEquiv.symm x = hA.K0DegreeZeroInv x :=
  rfl

/-- `K₀(C_A) ≅ K₀(C_{A⁰})` sends `[e · C_A(k, -)]` to `[e · C_{A⁰}(k, -)]`. -/
theorem K0DegreeZeroEquiv_cell {k : WeightCategory A} (e : Idempotent k) :
    hA.K0DegreeZeroEquiv (DGCategory.K0.cell.{max u w} e 0) =
      DGCategory.K0.cell.{max u w} (e.map hA.projFunctor) 0 :=
  hA.K0DegreeZeroMap_cell e

theorem K0DegreeZeroEquiv_symm_cell {k : WeightCategory hA.degreeZeroDGSubring}
    (e : Idempotent k) :
    hA.K0DegreeZeroEquiv.symm (DGCategory.K0.cell.{max u w} e 0) =
      DGCategory.K0.cell.{max u w} (e.map hA.inclFunctor) 0 :=
  hA.K0DegreeZeroInv_cell e

end IsGradedPositive

end DG

end
