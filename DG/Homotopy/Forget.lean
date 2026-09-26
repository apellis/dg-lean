import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import DG.Homotopy.ModuleCat

/-!
# The underlying cochain complex of a dg module

For a dg `R`-algebra `A` and a dg `A`-module `M`, the homogeneous components `Mⁿ` are
`R`-submodules and `d : Mⁿ → Mⁿ⁺¹` is `R`-linear, so `M` has an underlying cochain complex
of `R`-modules, `DG.DGModuleCat.toComplex R M : CochainComplex (ModuleCat R) ℤ`. This is the
object map of the forgetful functor

  `DG.DGModuleCat.forget R A : DGModuleCat A ⥤ CochainComplex (ModuleCat R) ℤ`,

which is additive, `R`-linear, faithful and reflects isomorphisms. The forgetful functor to
cochain complexes of abelian groups, `DG.DGModuleCat.forgetToAddCommGrp A`, is the case `R = ℤ`
composed with the forgetful functor `ModuleCat ℤ ⥤ AddCommGrp`.

## Implementation notes

The `R`-module structure on the carrier of an object `M : DGModuleCat A` is
`Module.compHom M (algebraMap R A)`, i.e. `r • m = algebraMap R A r • m`. It is a scoped instance
in the namespace `DG.DGModuleCat.Algebra`, as for `ModuleCat.Algebra` in Mathlib; it is needed
to state that `(toComplex R M).X n` is `ModuleCat.of R (DGModule.gradingSubmodule R A M n)`.
-/

open CategoryTheory CategoryTheory.Limits

universe v u w

/-- A faithful additive functor induces a faithful functor on homological complexes. -/
instance CategoryTheory.Functor.mapHomologicalComplex_faithful {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Faithful]
    {ι : Type*} (c : ComplexShape ι) : (F.mapHomologicalComplex c).Faithful where
  map_injective h := HomologicalComplex.hom_ext _ _ fun n =>
    F.map_injective (congrArg (fun φ => φ.f n) h)

namespace DG

namespace DGModuleCat

variable (R : Type w) {A : Type u} [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]

namespace Algebra

/-- The carrier of a dg `A`-module is an `R`-module through `algebraMap R A`. -/
scoped instance instModule (M : DGModuleCat.{v} A) : Module R M :=
  Module.compHom M (algebraMap R A)

scoped instance instIsScalarTower (M : DGModuleCat.{v} A) : IsScalarTower R A M where
  smul_assoc r a m := by
    change (r • a) • m = algebraMap R A r • a • m
    rw [Algebra.smul_def, mul_smul]

end Algebra

open Algebra

variable [DGRing A] [DGAlgebra R A]

section Object

variable (M : DGModuleCat.{v} A)

/-- The differential `Mⁿ → Mⁿ⁺¹` as an `R`-linear map. -/
def dRestrict (n : ℤ) :
    DGModule.gradingSubmodule R A M n →ₗ[R] DGModule.gradingSubmodule R A M (n + 1) :=
  (DGModule.dLinear R A M).restrict fun _ hm => d_mem hm

@[simp]
theorem coe_dRestrict_apply (n : ℤ) (m : DGModule.gradingSubmodule R A M n) :
    (dRestrict R M n m : M) = d (m : M) := rfl

/-- The underlying cochain complex of `R`-modules of a dg `A`-module. -/
def toComplex : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (DGModule.gradingSubmodule R A M n))
    (fun n => ModuleCat.ofHom (dRestrict R M n)) fun n => by
      ext m
      exact d_d (m : M)

@[simp]
theorem toComplex_X (n : ℤ) :
    (toComplex R M).X n = ModuleCat.of R (DGModule.gradingSubmodule R A M n) := rfl

@[simp]
theorem toComplex_d (n : ℤ) :
    (toComplex R M).d n (n + 1) = ModuleCat.ofHom (dRestrict R M n) :=
  CochainComplex.of_d _ _ _ n

end Object

section Morphism

variable {M N P : DGModuleCat.{v} A}

/-- A morphism of dg modules restricted to the homogeneous components of degree `n`, as an
`R`-linear map. -/
def homRestrict (f : M ⟶ N) (n : ℤ) :
    DGModule.gradingSubmodule R A M n →ₗ[R] DGModule.gradingSubmodule R A N n :=
  (f.hom.toLinearMap.restrictScalars R).restrict fun _ hm => f.hom.map_mem hm

@[simp]
theorem coe_homRestrict_apply (f : M ⟶ N) (n : ℤ) (m : DGModule.gradingSubmodule R A M n) :
    (homRestrict R f n m : N) = f m := rfl

/-- The morphism of cochain complexes underlying a morphism of dg modules. -/
def toComplexMap (f : M ⟶ N) : toComplex R M ⟶ toComplex R N :=
  CochainComplex.ofHom _ _ _ _ _ _ (fun n => ModuleCat.ofHom (homRestrict R f n)) fun n => by
    ext m
    exact (f.hom.map_d (m : M)).symm

@[simp]
theorem toComplexMap_f (f : M ⟶ N) (n : ℤ) :
    (toComplexMap R f).f n = ModuleCat.ofHom (homRestrict R f n) := rfl

variable (A) in
/-- The forgetful functor from dg `A`-modules to cochain complexes of `R`-modules. -/
@[simps]
def forget : DGModuleCat.{v} A ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj M := toComplex R M
  map f := toComplexMap R f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance forget_additive : (forget R A).Additive where
  map_add := by intros; ext; rfl

instance forget_linear : Functor.Linear R (forget R A) where
  map_smul _ _ := by ext; rfl

theorem forget_map_injective {f g : M ⟶ N} (h : (forget R A).map f = (forget R A).map g) :
    f = g := by
  refine hom_ext_apply fun m => ?_
  induction m using DG.induction_on with
  | h_zero => rw [map_zero, map_zero]
  | @h_homogeneous n m =>
    have h1 : homRestrict R f n = homRestrict R g n :=
      congrArg (fun φ : toComplex R M ⟶ toComplex R N => ModuleCat.Hom.hom (φ.f n)) h
    exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨m, m.2⟩)
  | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']

/-- The forgetful functor to cochain complexes is faithful. -/
instance forget_faithful : (forget R A).Faithful where
  map_injective h := forget_map_injective R h

theorem bijective_of_forget_map_isIso (f : M ⟶ N) [IsIso ((forget R A).map f)] :
    Function.Bijective f := by
  have hn : ∀ n : ℤ, Function.Bijective (homRestrict R f n) := fun n => by
    haveI : IsIso (((forget R A).map f).f n) :=
      inferInstanceAs (IsIso ((HomologicalComplex.eval _ _ n).map ((forget R A).map f)))
    exact ConcreteCategory.bijective_of_isIso (((forget R A).map f).f n)
  constructor
  · intro m m' hmm'
    rw [← sub_eq_zero, ← map_sub] at hmm'
    rw [← sub_eq_zero]
    generalize m - m' = x at hmm'
    have h : ∀ n, (DirectSum.decompose (grading (M := M)) x n : M) = 0 := fun n => by
      have h1 : (DirectSum.decompose (grading (M := N)) (f x) n : N) =
          f (DirectSum.decompose (grading (M := M)) x n) :=
        coe_decompose_map_of_map_mem f.hom.toLinearMap.toAddMonoidHom
          (fun h => f.hom.map_mem h) x n
      rw [hmm', DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at h1
      have h2 : homRestrict R f n ⟨_, (DirectSum.decompose (grading (M := M)) x n).2⟩ = 0 :=
        Subtype.ext h1.symm
      rw [← map_zero (homRestrict R f n)] at h2
      exact congrArg Subtype.val ((hn n).injective h2)
    rw [← (DirectSum.decompose (grading (M := M))).symm_apply_apply x]
    have : DirectSum.decompose (grading (M := M)) x = 0 := DirectSum.ext _ fun n =>
      Subtype.ext ((h n).trans (ZeroMemClass.coe_zero _).symm)
    rw [this, DirectSum.decompose_symm_zero]
  · intro y
    induction y using DG.induction_on with
    | h_zero => exact ⟨0, map_zero _⟩
    | h_homogeneous y =>
      obtain ⟨x, hx⟩ := (hn _).surjective ⟨y, y.2⟩
      exact ⟨x, congrArg Subtype.val hx⟩
    | h_add y y' hy hy' =>
      obtain ⟨x, rfl⟩ := hy
      obtain ⟨x', rfl⟩ := hy'
      exact ⟨x + x', map_add _ _ _⟩

/-- The forgetful functor to cochain complexes reflects isomorphisms. -/
instance forget_reflectsIsomorphisms : (forget R A).ReflectsIsomorphisms where
  reflects f _ := isIso_of_bijective f (bijective_of_forget_map_isIso R f)

end Morphism

section AddCommGrp

variable (A)

/-- The forgetful functor from dg `A`-modules to cochain complexes of abelian groups. -/
noncomputable def forgetToAddCommGrp : DGModuleCat.{v} A ⥤ CochainComplex AddCommGrp.{v} ℤ :=
  forget ℤ A ⋙ (forget₂ (ModuleCat.{v} ℤ) AddCommGrp.{v}).mapHomologicalComplex _

instance forgetToAddCommGrp_additive : (forgetToAddCommGrp A).Additive := by
  unfold forgetToAddCommGrp
  infer_instance

instance forgetToAddCommGrp_faithful : (forgetToAddCommGrp A).Faithful := by
  unfold forgetToAddCommGrp
  infer_instance

end AddCommGrp

end DGModuleCat

end DG
