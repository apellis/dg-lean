import DG.HalfGraded.DiagonalRecovery

/-!
# Full faithfulness of the diagonal module functor

The genuine weight arrow obtained by placing `1` in bidegree `(-2t, 4t)` carries
weight-zero generators to all supported generators. Compatibility with this actual
action therefore determines every component of a CatModule morphism from weight zero;
unsupported weights vanish. Recovery supplies an explicit inverse on morphisms.

These statements concern the existing module categories, for arbitrary dg rings and
module universes. Fullness after derived localization, preservation of all compact
objects, and an essential-image equivalence are separate claims, not proved here.
-/

open CategoryTheory
universe v u
namespace DG.Diagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The actual weight arrow given by the periodic copy of the unit. -/
def periodicUnit (t : ℤ) :
    (⟨0⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⟶ ⟨4 * t⟩ :=
  ⟨(HalfGradedDGRing.ofDGRing A).place (-2 * t, 4 * t) 1 (by
    change (1 : A) ∈ halfGrading (grading A) 2 (-2 * t, 4 * t)
    rw [halfGrading_supported]
    rw [show -2 * t + 2 * t = 0 by ring]
    exact one_mem_grading), by
    simpa only [sub_zero] using
      (HalfGradedDGRing.ofDGRing A).place_mem_wgrading (-2 * t, 4 * t) _⟩

/-- The original regraded action moves each weight-zero generator to its supported copy. -/
theorem periodicUnit_act_toWeightZero (M : DGModuleCat.{v} A) (n t : ℤ)
    (m : DG.grading (M := M) (n + 2 * t)) :
    ((toCatModule A).obj M).act (periodicUnit A t)
      (toWeightZero A M (n + 2 * t) m) = supportedElement A M n t m := by
  apply Subtype.ext
  change (HalfGradedDGRing.ofDGRing A).place _ 1 _ •
    HalfRegrade.mk (grading M) 2 _ m.1 _ = _
  rw [place_smul_mk]
  exact HalfRegrade.mk_congr (by ext <;> dsimp <;> ring) (one_smul A m.1) _ _

/-- All components of an actual morphism between diagonal modules are forced by weight zero. -/
theorem diagonal_hom_ext {M N : DGModuleCat.{v} A}
    {f g : (toCatModule A).obj M ⟶ (toCatModule A).obj N}
    (h : ∀ x, f.app ⟨0⟩ x = g.app ⟨0⟩ x) : f = g := by
  apply CatModule.Hom.ext
  rintro ⟨w⟩ x
  by_cases hw : ∃ t : ℤ, w = 4 * t
  · obtain ⟨t, rfl⟩ := hw
    induction x using DG.induction_on with
    | h_zero => exact (f.app _).map_zero.trans (g.app _).map_zero.symm
    | h_add x y hx hy => simp only [map_add, hx, hy]
    | @h_homogeneous n x =>
      have hx : x.1 = supportedElement A M n t
          ⟨valueEvaluation A M (4 * t) x.1, valueEvaluation_mem A M x.2⟩ := by
        apply valueEvaluation_injective_degree A M x.2 (supportedElement_mem A M n t _)
        simp
      rw [hx, ← periodicUnit_act_toWeightZero A M]
      exact (f.map_smul (periodicUnit A t) _).trans
        ((congrArg (((toCatModule A).obj N).act (periodicUnit A t)) (h _)).trans
          (g.map_smul (periodicUnit A t) _).symm)
  · let := value_subsingleton A N w hw
    exact Subsingleton.elim _ _

/-- Recover an ordinary dg module map from an actual morphism of diagonal CatModules. -/
def diagonalPreimage {M N : DGModuleCat.{v} A}
    (f : (toCatModule A).obj M ⟶ (toCatModule A).obj N) : M ⟶ N :=
  (recoveryIso A M).inv ≫ (recover A 0).map f ≫ (recoveryIso A N).hom

/-- The explicit recovered map induces the entire original morphism, at every weight. -/
@[simp] theorem map_diagonalPreimage {M N : DGModuleCat.{v} A}
    (f : (toCatModule A).obj M ⟶ (toCatModule A).obj N) :
    (toCatModule A).map (diagonalPreimage A f) = f := by
  apply diagonal_hom_ext A
  have h := (recoveryNatIso A).hom.naturality (diagonalPreimage A f)
  change (recover A 0).map ((toCatModule A).map (diagonalPreimage A f)) ≫
    (recoveryIso A N).hom = (recoveryIso A M).hom ≫ diagonalPreimage A f at h
  have hh : (recover A 0).map ((toCatModule A).map (diagonalPreimage A f)) =
      (recover A 0).map f := by
    apply (cancel_mono (recoveryIso A N).hom).mp
    simpa [diagonalPreimage] using h
  intro x
  exact congrArg (fun k => k.hom x) hh

/-- Weight-zero recovery already implies module-level faithfulness. -/
instance toCatModule_faithful : (toCatModule.{v} A).Faithful :=
  (recoveryNatIso A).faithful_of_comp

/-- Every actual morphism between diagonal modules is induced by an ordinary module map. -/
instance toCatModule_full : (toCatModule.{v} A).Full where
  map_surjective f := ⟨diagonalPreimage A f, map_diagonalPreimage A f⟩

/-- Recovery also gives the left inverse on ordinary dg module morphisms. -/
@[simp] theorem diagonalPreimage_map {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    diagonalPreimage A ((toCatModule A).map f) = f :=
  (toCatModule A).map_injective (map_diagonalPreimage A _)

/-- Full faithfulness with the explicit action-compatible recovery formula as inverse. -/
def toCatModuleFullyFaithful : (toCatModule.{v} A).FullyFaithful where
  preimage := diagonalPreimage A
  map_preimage := map_diagonalPreimage A
  preimage_map := diagonalPreimage_map A

end
end DG.Diagonal
