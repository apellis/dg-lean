import DG.Derived.Morita
import DG.K0.DGRing

/-!
# `K₀` and Morita theory for an idempotent

For a degree-`0` idempotent cocycle `e` of a dg ring `A` which is full up to homotopy
(`DG.DGIdempotent.IsFullH0`: `1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`), the triangulated
Morita equivalence `D(e A e) ≌ D(A)` (`DG.DGIdempotent.moritaEquivalence`) restricts to the
compact objects and induces `K₀(e A e) ≅ K₀(A)` (Roadmap 7.3, `K₀` corollary):
`DG.DGIdempotent.K0MoritaEquiv`.

As for the equivalence itself, the hypothesis `A e A = A` alone is not sufficient (see
`DG.Derived.Morita`). The functor of the equivalence is `A e ⊗^L_{eAe} -`; the images of
individual classes (e.g. `[e A e] ↦ [A e]`) are not computed here.
-/

open CategoryTheory

universe t w₁ w₂ u

namespace DG

namespace DGIdempotent

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (e : DGIdempotent A)
  [HasDerivedCategory.{w₁, max u t} e.Corner] [HasDerivedCategory.{w₂, max u t} A]

/-- **`K₀(e A e) ≅ K₀(A)`** (Roadmap 7.3) for a degree-`0` idempotent cocycle `e` which is full up
to homotopy, induced by the triangulated Morita equivalence `D(e A e) ≌ D(A)` on the compact
objects. -/
noncomputable def K0MoritaEquiv (he : e.IsFullH0) :
    DGRing.K0.{w₁, max u t} e.Corner ≃+ DGRing.K0.{w₂, max u t} A :=
  DG.K0.compactMapEquiv (e.moritaEquivalence.{t} he)

theorem K0MoritaEquiv_mk (he : e.IsFullH0) (X : PerfectDerivedCategory.{w₁, max u t} e.Corner) :
    e.K0MoritaEquiv.{t} he (DG.K0.mk X) =
      DG.K0.mk (⟨(e.moritaEquivalence.{t} he).functor.obj X.obj,
        X.property.map_of_equivalence _⟩ : PerfectDerivedCategory.{w₂, max u t} A) :=
  DG.K0.compactMapEquiv_mk _ X

end DGIdempotent

end DG
