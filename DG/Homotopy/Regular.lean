import DG.Homotopy.Lifting
import DG.Module.ULift

/-!
# The regular module is cofibrant; acyclic cofibrant modules are contractible

Let `A` be a dg ring.

* `DG.isGradedProjective_self`, `DG.hasLiftingProperty_self`: the regular dg module `A` is
  graded-projective (a graded map `f : A → N` of degree `0` is determined by `f 1`, which lifts
  along a surjection) and has the lifting property against surjective quasi-isomorphisms.
* `DG.isContractible_of_isKProjective`: an acyclic K-projective dg module is contractible, since
  its identity is a morphism to an acyclic module; K-projectivity is tested in a larger universe
  through the universe lift `ULift M` (`DG.ULift.instDGModule`).
  `DG.isContractible_of_hasLiftingProperty`: likewise for the lifting property.
-/

universe w u

namespace DG

section Contractible

variable {A : Type*} [Ring A] [DGAddCommGroup A] {M : Type u} [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- The universe lift of an acyclic dg module is acyclic. -/
theorem IsAcyclic.ulift (hac : IsAcyclic M) : IsAcyclic (ULift.{w} M) :=
  isAcyclic_iff.mpr fun _ x hx hdx => by
    obtain ⟨y, hy, hdy⟩ := hac.exists_d_eq (ULift.mem_grading_iff.mp hx) (congrArg ULift.down hdx)
    exact ⟨ULift.up y, hy, ULift.ext _ _ hdy⟩

/-- An acyclic K-projective dg module is contractible: its identity factors through the acyclic
universe lift `ULift M`, hence is null-homotopic. -/
theorem isContractible_of_isKProjective (hP : IsKProjective.{max u w} A M) (hac : IsAcyclic M) :
    IsContractible A M := by
  have h := (hP (ULift.{w} M) hac.ulift (ULift.upHom.{w} M)).comp_right (ULift.downHom.{w} M)
  rwa [DGModuleHom.comp_zero] at h

/-- An acyclic dg module with the lifting property against surjective quasi-isomorphisms is
contractible. -/
theorem isContractible_of_hasLiftingProperty [DGRing A] (hP : HasLiftingProperty.{max u w} A M)
    (hac : IsAcyclic M) : IsContractible A M :=
  isContractible_of_isKProjective hP.isKProjective hac

end Contractible

section Regular

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The regular dg module is graded-projective: a graded map `f : A → N` of degree `0` is
determined by `f 1`, which lifts along a surjection. -/
theorem isGradedProjective_self : IsGradedProjective.{w} A A := by
  intro M N _ _ _ _ _ _ _ _ p hp f
  have h1 : f 1 ∈ grading (M := N) (-0) := by
    simpa using f.map_mem (one_mem_grading (A := A))
  obtain ⟨x, hx, hpx⟩ := p.exists_mem_grading_of_surjective hp h1
  refine ⟨Cochain.ofElement x hx, Cochain.ext fun a => ?_⟩
  rw [Cochain.comp_apply, Cochain.ofHom_apply, Cochain.eq_ofElement f, Cochain.ofElement_apply,
    Cochain.ofElement_apply]
  rw [Shift.twist_zero, _root_.map_smul, hpx]

/-- The regular dg module `A` is cofibrant: it has the lifting property against surjective
quasi-isomorphisms. -/
theorem hasLiftingProperty_self : HasLiftingProperty.{w} A A :=
  (isKProjective_self A).hasLiftingProperty (isGradedProjective_self A)

end Regular

end DG
