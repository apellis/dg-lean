import DG.Category.Tensor.Cone
import DG.Category.Tensor.ShiftedCorner

/-!
# Comparing resolutions in the dg coend

The coend cone theorem converts preservation of acyclicity to preservation
of quasi-isomorphisms. Signed exchange handles the second variable, and
the two augmentations compare its cohomology through the common model.
-/

noncomputable section

namespace DG.CatTensorProduct
open CategoryTheory DGOpposite
open scoped DG.DegreeZero

private instance intDGModule (A : Type*) [AddCommGroup A] [DGAddCommGroup A] : DGModule ℤ A where
  smul_mem i j a x ha hx := by
    change a • x ∈ grading (i + j)
    rcases DegreeZero.mem_grading_iff.mp ha with hi | ha
    · subst i
      simpa only [zero_add] using zsmul_mem hx a
    · subst a
      simpa only [zero_smul] using (zero_mem (grading (M := A) (i+j)))
  d_smul' {i a} ha x := by
    rcases DegreeZero.mem_grading_iff.mp ha with hi | ha
    · subst i
      simp only [map_zsmul, koszulSign_zero, one_smul, DegreeZero.d_apply, zero_smul, zero_add]
    · subst a
      simp only [zero_smul, map_zero, smul_zero, add_zero]

private def dgIntHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DGAddCommGroup A] [DGAddCommGroup B] (e : DGAddEquiv A B) : A →ᵈᵍ[ℤ] B where
  toLinearMap := e.toAddEquiv.toAddMonoidHom.toIntLinearMap
  map_mem' := e.map_mem
  map_d' := e.map_d

private theorem dgIntHom_isQuasiIso {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DGAddCommGroup A] [DGAddCommGroup B] (e : DGAddEquiv A B) : (dgIntHom e).IsQuasiIso := by
  have hl : (dgIntHom e.symm).comp (dgIntHom e) = DGModuleHom.id :=
    DGModuleHom.ext (fun x => e.symm_apply_apply x)
  have hr : (dgIntHom e).comp (dgIntHom e.symm) = DGModuleHom.id :=
    DGModuleHom.ext (fun y => e.apply_symm_apply y)
  intro j
  refine ⟨?_, ?_⟩
  · have hh : Function.LeftInverse (cohomology.map (dgIntHom e.symm) j)
        (cohomology.map (dgIntHom e) j) := fun x => by
      have h := congrArg (fun g => DG.cohomology.map g j x) hl
      rw [cohomology.map_comp, AddMonoidHom.comp_apply, cohomology.map_id, AddMonoidHom.id_apply] at h
      exact h
    exact hh.injective
  · have hh : Function.RightInverse (cohomology.map (dgIntHom e.symm) j)
        (cohomology.map (dgIntHom e) j) := fun y => by
      have h := congrArg (fun g => DG.cohomology.map g j y) hr
      rw [cohomology.map_comp, AddMonoidHom.comp_apply, cohomology.map_id, AddMonoidHom.id_apply] at h
      exact h
    exact hh.surjective

universe w v u
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {N N' : CatModule.{w} (DGOpposite C)} (M : CatModule.{w} C)
  (h₀ : ∀ {X Y : C} (p : X ⟶ Y), p ∈ grading (0 : ℤ))

include h₀ in
/-- A module whose coend preserves acyclicity also preserves quasi-isomorphisms. -/
theorem isQuasiIso_mapLeftInt_of_acyclic
    (h : ∀ P : CatModule.{w} (DGOpposite C), CatModule.IsAcyclic P →
      DG.IsAcyclic (CatTensorProduct P M))
    (f : N ⟶ N') (hf : CatModule.IsQuasiIso f) :
    (mapLeftInt M f).IsQuasiIso := by
  apply (DGModuleHom.isQuasiIso_iff_isAcyclic_cone _).mpr
  exact acyclic_of_DGAddEquiv (coneLeftDGEquiv M h₀ f).symm
    (h (CatModule.cone f) ((CatModule.isQuasiIso_iff_isAcyclic_cone f).mp hf))

variable {M M' : CatModule.{w} C}

/-- The integer DG map induced by a morphism in the left module. -/
def mapRightInt (N : CatModule.{w} (DGOpposite C)) (g : M ⟶ M') :
    CatTensorProduct N M →ᵈᵍ[ℤ] CatTensorProduct N M' where
  toLinearMap := (map (𝟙 N) g).toIntLinearMap
  map_mem' := map_mem (𝟙 N) g
  map_d' := map_d (𝟙 N) g

include h₀ in
theorem isQuasiIso_mapRightInt_of_acyclic
    (h : ∀ P : CatModule.{w} (DGOpposite (DGOpposite C)), CatModule.IsAcyclic P →
      DG.IsAcyclic (CatTensorProduct P N))
    (g : M ⟶ M') (hg : CatModule.IsQuasiIso g) :
    (mapRightInt N g).IsQuasiIso := by
  let f : transposeLeftModule M ⟶ transposeLeftModule M' := transposeLeftModuleMap g
  let e := transposeDGEquiv N M h₀
  let e' := transposeDGEquiv N M' h₀
  have h₀' {X Y : DGOpposite C} (p : X ⟶ Y) : p ∈ grading (0 : ℤ) := h₀ (homUnop p)
  have hf : CatModule.IsQuasiIso f := fun X j => hg (doubleUnopFunctor C |>.obj X) j
  have hF := isQuasiIso_mapLeftInt_of_acyclic N h₀' h f hf
  have he := dgIntHom_isQuasiIso e
  have he' := dgIntHom_isQuasiIso e'
  have hcomp : (dgIntHom e').comp (mapRightInt N g) = (mapLeftInt N f).comp (dgIntHom e) := by
    apply DGModuleHom.ext
    intro x
    exact DFunLike.congr_fun (transposeHom_natural (𝟙 N) g h₀) x
  apply DGModuleHom.IsQuasiIso.of_comp_left _ he'
  rw [hcomp]
  exact hF.comp he

/-- Resolve either variable of a coend when both resolutions preserve acyclicity
against the other variable. -/
def resolutionCohomologyEquiv
    (f : N ⟶ N') (hf : CatModule.IsQuasiIso f)
    (g : M ⟶ M') (hg : CatModule.IsQuasiIso g)
    (hM : ∀ P : CatModule.{w} (DGOpposite C), CatModule.IsAcyclic P →
      DG.IsAcyclic (CatTensorProduct P M))
    (hN : ∀ P : CatModule.{w} (DGOpposite (DGOpposite C)), CatModule.IsAcyclic P →
      DG.IsAcyclic (CatTensorProduct P N)) (j : ℤ) :
    DG.cohomology (CatTensorProduct N' M) j ≃+ DG.cohomology (CatTensorProduct N M') j :=
  (AddEquiv.ofBijective _ (isQuasiIso_mapLeftInt_of_acyclic M h₀ hM f hf j)).symm.trans
    (AddEquiv.ofBijective _ (isQuasiIso_mapRightInt_of_acyclic h₀ hN g hg j))

end DG.CatTensorProduct
