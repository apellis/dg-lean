import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Preadditive.LeftExact
import DG.Category.Comparison
import DG.Category.SubQuotient
import DG.Homotopy.Abelian

/-!
# The abelian category of dg modules over a dg category

For a dg category `C`, the category `DG.CatModule C` of dg modules over `C` is abelian, with
kernels, cokernels and exactness computed objectwise.

* Kernels are the kernel dg submodules `DG.CatModule.Hom.ker` (`DG.CatModule.kernelIsLimit`) and
  cokernels the quotients by the images (`DG.CatModule.cokernelIsColimit`). Monomorphisms are the
  objectwise injective morphisms and epimorphisms the objectwise surjective ones
  (`DG.CatModule.mono_iff_injective`, `DG.CatModule.epi_iff_surjective`).
* `DG.CatModule.eval X : CatModule C ⥤ DGModuleCat (End X)`: evaluation at an object `X`, where
  `M.obj X` is a dg module over the endomorphism dg ring `End X` (`DG.End.instDGRing`); it is
  restriction along the dg functor `DG.CatModule.endInclusion X : SingleObj (End X) ⥤ C`
  followed by `DG.CatModule.toDGModuleCat`. The evaluation functors are additive, jointly
  faithful (`DG.CatModule.eval_jointly_faithful`) and jointly reflect isomorphisms, and each of
  them preserves kernels and cokernels, hence finite limits and colimits (it is exact). Composed
  with `DG.DGModuleCat.forgetToAddCommGrp (End X)` they give the jointly faithful additive
  functors `DG.CatModule.evalComplex X : CatModule C ⥤ CochainComplex AddCommGrp ℤ` to the
  underlying cochain complexes of abelian groups.
* `DG.CatModule.abelian`: the coimage-image comparison is an isomorphism, since it is so after
  every evaluation.
* A short complex is exact, resp. short exact, if and only if it is objectwise exact as a
  sequence of abelian groups (`DG.CatModule.exact_iff_function_exact`,
  `DG.CatModule.shortExact_iff`).
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

noncomputable section

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### Kernels and cokernels -/

section KernelCokernel

variable {M N : CatModule.{w} C} (φ : M ⟶ N)

theorem ker_subtype_comp : (Hom.ker φ).subtype ≫ φ = 0 :=
  hom_ext fun _ m => m.2

/-- The kernel fork given by the kernel dg submodule. -/
def kernelFork : KernelFork φ :=
  KernelFork.ofι _ (ker_subtype_comp φ)

@[simp]
theorem kernelFork_ι : (kernelFork φ).ι = (Hom.ker φ).subtype := rfl

/-- The kernel dg submodule is a kernel. -/
def kernelIsLimit : IsLimit (kernelFork φ) :=
  KernelFork.IsLimit.ofι _ (ker_subtype_comp φ)
    (fun {W} g hg => CatSubmodule.codRestrict g fun X m =>
      show φ.app X (g.app X m) = 0 from congrArg (fun χ : W ⟶ N => χ.app X m) hg)
    (fun _ _ => rfl)
    (fun _ _ _ hm => hom_ext fun X m => Subtype.ext (congrArg (fun χ => χ.app X m) hm))

theorem comp_range_mkQ : φ ≫ (Hom.range φ).mkQ = 0 :=
  hom_ext fun _ m => (Hom.range φ).mkQ_eq_zero_iff.mpr ⟨m, rfl⟩

/-- The cokernel cofork given by the quotient by the image. -/
def cokernelCofork : CokernelCofork φ :=
  CokernelCofork.ofπ _ (comp_range_mkQ φ)

@[simp]
theorem cokernelCofork_π : (cokernelCofork φ).π = (Hom.range φ).mkQ := rfl

/-- The quotient by the image is a cokernel. -/
def cokernelIsColimit : IsColimit (cokernelCofork φ) :=
  CokernelCofork.IsColimit.ofπ _ (comp_range_mkQ φ)
    (fun {W} g hg => CatSubmodule.liftQ g (by
      rintro X _ ⟨m, rfl⟩
      exact congrArg (fun χ : M ⟶ W => χ.app X m) hg))
    (fun _ _ => rfl)
    (fun _ _ _ hm => CatSubmodule.quotient_hom_ext _ hm)

instance hasKernels : HasKernels (CatModule.{w} C) :=
  ⟨fun φ => HasLimit.mk ⟨_, kernelIsLimit φ⟩⟩

instance hasCokernels : HasCokernels (CatModule.{w} C) :=
  ⟨fun φ => HasColimit.mk ⟨_, cokernelIsColimit φ⟩⟩

end KernelCokernel

/-! ### Monomorphisms and epimorphisms -/

section MonoEpi

variable {M N : CatModule.{w} C} (φ : M ⟶ N)

theorem injective_of_mono [Mono φ] (X : C) : Function.Injective (φ.app X) := by
  have h : (Hom.ker φ).subtype = 0 :=
    (cancel_mono φ).1 ((kernelFork φ).condition.trans zero_comp.symm)
  rw [injective_iff_map_eq_zero]
  intro m hm
  exact congrArg (fun χ : (Hom.ker φ).toCatModule ⟶ M => χ.app X ⟨m, hm⟩) h

theorem surjective_of_epi [Epi φ] (X : C) : Function.Surjective (φ.app X) := by
  have h : (Hom.range φ).mkQ = 0 :=
    (cancel_epi φ).1 ((cokernelCofork φ).condition.trans comp_zero.symm)
  intro n
  exact (Hom.range φ).mkQ_eq_zero_iff.mp (congrArg (fun χ => χ.app X n) h)

theorem mono_of_injective (h : ∀ X, Function.Injective (φ.app X)) : Mono φ :=
  ⟨fun _ _ hg => hom_ext fun X m => h X (congrArg (fun χ => χ.app X m) hg)⟩

theorem epi_of_surjective (h : ∀ X, Function.Surjective (φ.app X)) : Epi φ :=
  ⟨fun g g' hg => hom_ext fun X n => by
    obtain ⟨m, rfl⟩ := h X n
    exact congrArg (fun χ => χ.app X m) hg⟩

/-- A morphism of dg modules is a monomorphism if and only if it is injective at every
object. -/
theorem mono_iff_injective : Mono φ ↔ ∀ X, Function.Injective (φ.app X) :=
  ⟨fun _ => injective_of_mono φ, mono_of_injective φ⟩

/-- A morphism of dg modules is an epimorphism if and only if it is surjective at every
object. -/
theorem epi_iff_surjective : Epi φ ↔ ∀ X, Function.Surjective (φ.app X) :=
  ⟨fun _ => surjective_of_epi φ, epi_of_surjective φ⟩

end MonoEpi

/-! ### Evaluation at an object -/

section Eval

variable (X : C)

/-- The inclusion `SingleObj (End X) ⥤ C` of the endomorphism dg ring of `X`. -/
@[simps]
def endInclusion : SingleObj (End X) ⥤ C where
  obj _ := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (endInclusion X).Additive where

instance : (endInclusion X).IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

/-- Evaluation at an object `X`: `M ↦ M.obj X`, a dg module over the endomorphism dg ring
`End X`, with `f • m` the action of `f : X ⟶ X`. -/
def eval : CatModule.{w} C ⥤ DGModuleCat.{w} (End X) :=
  precomp (endInclusion X) ⋙ toDGModuleCat (End X)

@[simp]
theorem eval_obj_carrier (M : CatModule.{w} C) : ((eval X).obj M : Type w) = M.obj X := rfl

@[simp]
theorem eval_map_hom_apply {M N : CatModule.{w} C} (φ : M ⟶ N) (m : M.obj X) :
    ((eval X).map φ).hom m = φ.app X m := rfl

instance : (eval.{w} X).Additive where
  map_add := rfl

variable {X} in
/-- The evaluation functors are jointly faithful. -/
theorem eval_jointly_faithful {M N : CatModule.{w} C} {φ ψ : M ⟶ N}
    (h : ∀ X, (eval X).map φ = (eval X).map ψ) : φ = ψ :=
  hom_ext fun X m => congrArg (fun χ => χ.hom m) (h X)

/-- The evaluation functors jointly reflect isomorphisms. -/
theorem isIso_of_isIso_eval {M N : CatModule.{w} C} (φ : M ⟶ N)
    (h : ∀ X, IsIso ((eval X).map φ)) : IsIso φ :=
  isIso_of_bijective φ fun X => ConcreteCategory.bijective_of_isIso ((eval X).map φ)

variable [DGCategory C]

/-- A short complex of dg modules which is objectwise exact is mapped to an exact short complex
by the evaluation functors. -/
theorem exact_map_eval_of_exact (S : ShortComplex (CatModule.{w} C))
    (hS : Function.Exact (S.f.app X) (S.g.app X)) : (S.map (eval X)).Exact :=
  (DGModuleCat.exact_iff_function_exact _).2 hS

/-- Evaluation preserves kernels. -/
instance eval_preservesKernel {M N : CatModule.{w} C} (φ : M ⟶ N) :
    PreservesLimit (parallelPair φ 0) (eval X) := by
  have h : ((ShortComplex.mk _ _ (kernelFork φ).condition).map (eval X)).Exact :=
    exact_map_eval_of_exact X _ fun y =>
      ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  have : Mono ((ShortComplex.mk _ _ (kernelFork φ).condition).map (eval X)).f :=
    (DGModuleCat.mono_iff_injective _).2 Subtype.val_injective
  exact preservesLimit_of_preserves_limit_cone (kernelIsLimit φ)
    ((KernelFork.isLimitMapConeEquiv _ _).symm h.fIsKernel)

/-- Evaluation preserves cokernels. -/
instance eval_preservesCokernel {M N : CatModule.{w} C} (φ : M ⟶ N) :
    PreservesColimit (parallelPair φ 0) (eval X) := by
  have h : ((ShortComplex.mk _ _ (cokernelCofork φ).condition).map (eval X)).Exact :=
    exact_map_eval_of_exact X _ fun _ => (Hom.range φ).mkQ_eq_zero_iff
  have : Epi ((ShortComplex.mk _ _ (cokernelCofork φ).condition).map (eval X)).g :=
    (DGModuleCat.epi_iff_surjective _).2 ((Hom.range φ).mkQ_surjective X)
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit φ)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm h.gIsCokernel)

instance eval_preservesLimitsOfShape_walkingParallelPair :
    PreservesLimitsOfShape WalkingParallelPair (eval.{w} X) :=
  Functor.preservesEqualizers_of_preservesKernels _

instance eval_preservesColimitsOfShape_walkingParallelPair :
    PreservesColimitsOfShape WalkingParallelPair (eval.{w} X) :=
  Functor.preservesCoequalizers_of_preservesCokernels _

end Eval

/-! ### The abelian structure -/

section Abelian

variable [DGCategory C]

/-- The coimage-image comparison morphisms are isomorphisms: they are so after evaluation at
every object. -/
instance isIso_coimageImageComparison {M N : CatModule.{w} C} (φ : M ⟶ N) :
    IsIso (Abelian.coimageImageComparison φ) :=
  isIso_of_isIso_eval _ fun X =>
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Abelian.PreservesCoimageImageComparison.iso (eval X) φ)).2
      (inferInstanceAs (IsIso (Abelian.coimageImageComparison _)))

/-- The category of dg modules over a dg category is abelian. -/
instance abelian : Abelian (CatModule.{w} C) :=
  Abelian.ofCoimageImageComparisonIsIso

/-- Evaluation at an object is left exact. -/
instance eval_preservesFiniteLimits (X : C) : PreservesFiniteLimits (eval.{w} X) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- Evaluation at an object is right exact. -/
instance eval_preservesFiniteColimits (X : C) : PreservesFiniteColimits (eval.{w} X) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- The underlying cochain complex of abelian groups of the value at `X`, as an additive functor
`CatModule C ⥤ CochainComplex AddCommGrp ℤ`. -/
def evalComplex (X : C) : CatModule.{w} C ⥤ CochainComplex AddCommGrp.{w} ℤ :=
  eval X ⋙ DGModuleCat.forgetToAddCommGrp (End X)

instance (X : C) : (evalComplex.{w} X).Additive := by
  dsimp only [evalComplex, DGModuleCat.forgetToAddCommGrp]
  infer_instance

variable {X} in
/-- The underlying cochain complexes functors are jointly faithful. -/
theorem evalComplex_jointly_faithful {M N : CatModule.{w} C} {φ ψ : M ⟶ N}
    (h : ∀ X, (evalComplex X).map φ = (evalComplex X).map ψ) : φ = ψ :=
  eval_jointly_faithful fun X => (DGModuleCat.forgetToAddCommGrp (End X)).map_injective (h X)

/-- A short complex of dg modules is exact if and only if it is exact as a sequence of abelian
groups at every object. -/
theorem exact_iff_function_exact (S : ShortComplex (CatModule.{w} C)) :
    S.Exact ↔ ∀ X, Function.Exact (S.f.app X) (S.g.app X) := by
  constructor
  · intro hS X
    exact (DGModuleCat.exact_iff_function_exact _).1 (hS.map (eval X))
  · intro hS
    rw [S.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    refine eval_jointly_faithful fun X => ?_
    have h := ((S.map (eval X)).exact_iff_isZero_homology.1 (exact_map_eval_of_exact X S (hS X)))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (h.of_iso (S.mapHomologyIso (eval X)).symm).eq_of_src _ _

/-- A short complex of dg modules is short exact if and only if it is short exact as a sequence
of abelian groups at every object. -/
theorem shortExact_iff (S : ShortComplex (CatModule.{w} C)) :
    S.ShortExact ↔ ∀ X, Function.Injective (S.f.app X) ∧ Function.Exact (S.f.app X) (S.g.app X) ∧
      Function.Surjective (S.g.app X) :=
  ⟨fun h X => by
      have := h.mono_f
      have := h.epi_g
      exact ⟨injective_of_mono S.f X, (exact_iff_function_exact S).1 h.exact X,
        surjective_of_epi S.g X⟩,
    fun h => by
      have := mono_of_injective S.f fun X => (h X).1
      have := epi_of_surjective S.g fun X => (h X).2.2
      exact ⟨(exact_iff_function_exact S).2 fun X => (h X).2.1⟩⟩

end Abelian

end CatModule

end DG
