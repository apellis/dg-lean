import DG.Derived.TriangularBasis
import DG.K0.DGRing

/-!
# Classes of modules with finite triangular bases in `K₀`

* `DG.DGRing.K0.leftCorner_one`: the class of the corner module `A · 1` is `[A]`;
* `DG.TriangularBasis.K0_mk`, `DG.FreeBasis.K0_mk_toTriangular`: in `K₀(A)`, the class of a dg
  module with a finite triangular basis `(b_j)` is `Σ_j (-1)^{|b_j|} [A]`.
-/

open CategoryTheory

universe w' v

noncomputable section

namespace DG

section K0

variable {A : Type v} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- `A · 1 ≅ A` as dg `A`-modules. -/
def DGIdempotent.oneLeftCornerIso :
    DGModuleCat.of A (DGIdempotent.one A).LeftCorner ≅ DGModuleCat.of A A where
  hom := DGModuleCat.ofHom (DGIdempotent.one A).leftCornerInclusion
  inv := DGModuleCat.ofHom (DGIdempotent.one A).leftCornerProjection
  hom_inv_id := DGModuleCat.hom_ext_apply fun x => Subtype.ext x.2
  inv_hom_id := DGModuleCat.hom_ext_apply fun _ => mul_one _

variable [DG.HasDerivedCategory.{w', v} A]

/-- The class of the corner module `A · 1` is `[A]`. -/
theorem DGRing.K0.leftCorner_one :
    DGRing.K0.leftCorner (DGIdempotent.one A) = DGRing.K0.self.{w'} A :=
  DG.K0.mk_eq_of_iso_obj (DG.DerivedCategory.Q.mapIso (DGIdempotent.oneLeftCornerIso (A := A)))

/-- **The class of a dg module with a finite triangular basis** `(b_j)`:
`[P] = Σ_j (-1)^{|b_j|} [A]` in `K₀(A)`. -/
theorem TriangularBasis.K0_mk {P : Type v} [AddCommGroup P]
    [DGAddCommGroup P] [Module A P] [DGModule A P] (T : TriangularBasis A P) :
    DG.K0.mk (⟨DG.DerivedCategory.Q.obj (DGModuleCat.of A P),
        T.finiteCellFiltration.isCompact_Q_obj⟩ : PerfectDerivedCategory.{w', v} A) =
      ∑ j, (T.deg j).negOnePow • DGRing.K0.self.{w'} A := by
  rw [DGRing.K0.mk_finiteCell T.finiteCellFiltration]
  change ∑ j : Fin T.length,
    (-T.deg j).negOnePow • DGRing.K0.leftCorner (DGIdempotent.one A) = _
  simp only [DGRing.K0.leftCorner_one, Int.negOnePow_neg]

/-- **The class of a dg module with a finite free basis** `(b_i)` ordered by a key decreased by
the differential: `[P] = Σ_i (-1)^{|b_i|} [A]` in `K₀(A)`. -/
theorem FreeBasis.K0_mk_toTriangular {P : Type v} [AddCommGroup P]
    [DGAddCommGroup P] [Module A P] [DGModule A P] {ι : Type*} [Fintype ι]
    (Bs : FreeBasis A P ι) (key : ι → ℤ)
    (hkey : ∀ i l, Bs.coeff (d (Bs.b i)) l ≠ 0 → key l < key i) :
    DG.K0.mk (⟨DG.DerivedCategory.Q.obj (DGModuleCat.of A P),
        (Bs.toTriangular key hkey).finiteCellFiltration.isCompact_Q_obj⟩ :
          PerfectDerivedCategory.{w', v} A) =
      ∑ i, (Bs.deg i).negOnePow • DGRing.K0.self.{w'} A := by
  rw [TriangularBasis.K0_mk (Bs.toTriangular key hkey)]
  exact (FreeBasis.order key).sum_comp fun i => (Bs.deg i).negOnePow • DGRing.K0.self A

end K0

end DG
