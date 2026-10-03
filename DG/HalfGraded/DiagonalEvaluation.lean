import DG.HalfGraded.DiagonalCohomology
import DG.Category.Abelian
import DG.Homotopy.Shift

/-!
# Chain-level recovery from diagonal weight values

At weight `4t`, the actual evaluated diagonal complex is naturally isomorphic to the
underlying complex of the ordinary module shifted by `2t`. This strengthens the cohomology
comparison to a chain-level comparison, with the library's differential signs. The result
forgets the action; it does not assert derived full faithfulness or compactness preservation.
-/

open CategoryTheory
universe v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The supported homogeneous component as a component of the ordinary even shift. -/
def supportedValueGradingEquiv (M : DGModuleCat.{v} A) (n t : ℤ) :
    DG.grading (M := Value A M (4 * t)) n ≃+
      DG.grading (M := Shift (2 * t) M) n where
  toFun x := ⟨Shift.mk (2 * t) (valueEvaluation A M (4 * t) x.1),
    valueEvaluation_mem A M x.2⟩
  invFun m := ⟨supportedElement A M n t ⟨Shift.unmk (2 * t) m.1, m.2⟩,
    supportedElement_mem A M n t _⟩
  left_inv x := by
    apply Subtype.ext
    apply valueEvaluation_injective_degree A M (supportedElement_mem A M n t _) x.2
    exact valueEvaluation_supportedElement A M n t _
  right_inv m := by
    apply Subtype.ext
    exact congrArg (Shift.mk (2 * t)) (valueEvaluation_supportedElement A M n t _)
  map_add' x y := by
    apply Subtype.ext
    change Shift.mk (2 * t) (valueEvaluation A M (4 * t) (x.1 + y.1)) =
      Shift.mk (2 * t) (valueEvaluation A M (4 * t) x.1) +
        Shift.mk (2 * t) (valueEvaluation A M (4 * t) y.1)
    rw [map_add, map_add]

/-- A supported weight value recovers the actual complex of the ordinary even shift. -/
def supportedEvaluationIso (M : DGModuleCat.{v} A) (t : ℤ) :
    (CatModule.evalComplex ⟨4 * t⟩).obj ((toCatModule A).obj M) ≅
      (DGModuleCat.forgetToAddCommGrp A).obj
        ((shiftFunctor (DGModuleCat.{v} A) (2 * t)).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (supportedValueGradingEquiv A M n t).toAddCommGrpIso) (by
      rintro i j (rfl : i + 1 = j)
      dsimp [CatModule.evalComplex, DGModuleCat.forgetToAddCommGrp,
        DGModuleCat.forget, Functor.mapHomologicalComplex]
      rw [DGModuleCat.toComplex_d, DGModuleCat.toComplex_d]
      apply AddCommGrpCat.hom_ext
      ext x
      exact (valueEvaluation_shift_d A M t x.1).symm)

/-- The chain-level comparison is natural for every actual ordinary dg module map. -/
def supportedEvaluationNatIso (t : ℤ) :
    toCatModule.{v} A ⋙ CatModule.evalComplex ⟨4 * t⟩ ≅
      shiftFunctor (DGModuleCat.{v} A) (2 * t) ⋙ DGModuleCat.forgetToAddCommGrp A :=
  NatIso.ofComponents (fun M => supportedEvaluationIso A M t) (by
    intro M N f
    apply HomologicalComplex.hom_ext
    intro n
    apply AddCommGrpCat.hom_ext
    ext x
    exact Subtype.ext (congrArg (Shift.mk (2 * t)) (evaluation_regradedMap f x.1.1)))

/-- A concrete element consumer for the chain-level comparison, at every supported weight. -/
@[simp] theorem supportedEvaluationIso_hom_f_supportedElement
    (M : DGModuleCat.{v} A) (n t : ℤ) (m : DG.grading (M := M) (n + 2 * t)) :
    (((supportedEvaluationIso A M t).hom.f n).hom
      ⟨supportedElement A M n t m, supportedElement_mem A M n t m⟩).1 =
      Shift.mk (2 * t) m.1 :=
  congrArg (Shift.mk (2 * t)) (valueEvaluation_supportedElement A M n t m)

end
end DG.Diagonal
