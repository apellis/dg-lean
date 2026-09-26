import Mathlib.CategoryTheory.Adjunction.Unique
import DG.Algebra.Hom
import DG.Homotopy.Abelian
import DG.Module.TensorProductOver

/-!
# Restriction and extension of scalars for dg modules

Let `φ : B →ᵈᵍ+* A` be a morphism of dg rings.

* `DG.DGModuleCat.restrictScalars φ : DGModuleCat A ⥤ DGModuleCat B` sends a dg `A`-module `M`
  to `DG.RestrictScalars φ M` (`b • m = φ b • m`). It is additive, faithful, and exact
  (`restrictScalars_preservesFiniteLimits`, `restrictScalars_preservesFiniteColimits`): it does
  not change the underlying abelian groups (`DG.DGModuleCat.restrictScalarsCompForget`) nor the
  underlying cochain complexes of abelian groups
  (`DG.DGModuleCat.restrictScalarsCompForgetToAddCommGrp`), and kernels and cokernels in
  `DGModuleCat` are computed on underlying abelian groups. Along a morphism of dg `R`-algebras
  it is `R`-linear (`DG.DGModuleCat.restrictScalars_linear`).
* `DG.DGRingHom.Bimodule φ`: the dg ring `A` as a dg `(A, B)`-bimodule, with the right action
  `x • b = x * φ b`; a type synonym for `A`, with `DG.DGRingHom.bimoduleEquiv φ : A ≃ₗ[A] _`.
* `DG.DGModuleHom.lTensor A M g : M ⊗_B N →ᵈᵍ[A] M ⊗_B N'` for a dg `(A, B)`-bimodule `M` and a
  morphism `g : N →ᵈᵍ[B] N'`.
* `DG.DGModuleCat.extendScalars φ : DGModuleCat B ⥤ DGModuleCat A`, `N ↦ A ⊗_B N`
  (`DG.TensorProductOver B φ.Bimodule N`) with the left action `a • (x ⊗ n) = (a * x) ⊗ n`.
* `DG.DGModuleCat.extendRestrictScalarsAdj φ : extendScalars φ ⊣ restrictScalars φ`, from the
  bijection `(A ⊗_B N →ᵈᵍ[A] M) ≃ (N →ᵈᵍ[B] RestrictScalars φ M)`, `f ↦ (n ↦ f (1 ⊗ n))`, with
  inverse `g ↦ (x ⊗ n ↦ x • g n)` (`DG.DGModuleCat.ExtendScalars.homEquiv`).
* Functoriality in `φ`: `DG.DGModuleCat.restrictScalarsId`, `DG.DGModuleCat.restrictScalarsComp`
  (the underlying types are unchanged), and `DG.DGModuleCat.extendScalarsId`,
  `DG.DGModuleCat.extendScalarsComp` (by uniqueness of left adjoints).

## Universes

As for Mathlib's `ModuleCat.extendScalars`, extension of scalars along `φ : B →ᵈᵍ+* A` with
`A : Type u₁` is a functor `DGModuleCat.{max v u₁} B ⥤ DGModuleCat.{max v u₁} A`, since
`A ⊗_B N` lives in the universe of `A` and `N`. The functoriality isomorphisms for extension of
scalars are stated for dg rings in a common universe.
-/

open CategoryTheory CategoryTheory.Limits MulOpposite

universe v u u₁ u₂

noncomputable section

namespace DG

/-! ### `A` as a dg `(A, B)`-bimodule -/

section Bimodule

variable {A : Type u₁} {B : Type u₂} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]

/-- The dg ring `A` regarded as a dg `(A, B)`-bimodule through `φ : B →ᵈᵍ+* A`: the left action
is multiplication in `A` and the right action is `x • b = x * φ b`. A type synonym for `A`. -/
@[nolint unusedArguments]
def DGRingHom.Bimodule (_φ : B →ᵈᵍ+* A) : Type u₁ := A

namespace DGRingHom.Bimodule

variable (φ : B →ᵈᵍ+* A)

instance instAddCommGroup : AddCommGroup φ.Bimodule := inferInstanceAs (AddCommGroup A)

instance instDGAddCommGroup : DGAddCommGroup φ.Bimodule := inferInstanceAs (DGAddCommGroup A)

instance instModule : Module A φ.Bimodule := inferInstanceAs (Module A A)

instance instDGModule [DGRing A] : DGModule A φ.Bimodule := inferInstanceAs (DGModule A A)

/-- The right action of `B`, `x • b = x * φ b`. -/
instance instModuleOp : Module Bᵐᵒᵖ φ.Bimodule := Module.compHom A (RingHom.op φ.toRingHom)

end DGRingHom.Bimodule

/-- The identity map `A → φ.Bimodule`, as an isomorphism of left `A`-modules. -/
def DGRingHom.bimoduleEquiv (φ : B →ᵈᵍ+* A) : A ≃ₗ[A] φ.Bimodule := LinearEquiv.refl A A

namespace DGRingHom.Bimodule

variable {φ : B →ᵈᵍ+* A}

@[simp]
theorem bimoduleEquiv_symm_apply (a : A) : φ.bimoduleEquiv.symm (φ.bimoduleEquiv a) = a := rfl

@[simp]
theorem bimoduleEquiv_apply_symm (x : φ.Bimodule) :
    φ.bimoduleEquiv (φ.bimoduleEquiv.symm x) = x := rfl

theorem smul_bimoduleEquiv (a a' : A) : a • φ.bimoduleEquiv a' = φ.bimoduleEquiv (a * a') := rfl

theorem op_smul_bimoduleEquiv (b : B) (a : A) :
    op b • φ.bimoduleEquiv a = φ.bimoduleEquiv (a * φ b) := rfl

theorem bimoduleEquiv_mem_grading_iff {n : ℤ} {a : A} :
    φ.bimoduleEquiv a ∈ grading n ↔ a ∈ grading n := Iff.rfl

theorem d_bimoduleEquiv (a : A) : d (φ.bimoduleEquiv a) = φ.bimoduleEquiv (d a) := rfl

variable (φ)

instance instSMulCommClass : SMulCommClass A Bᵐᵒᵖ φ.Bimodule where
  smul_comm a b x := (mul_assoc a (φ.bimoduleEquiv.symm x) (φ (unop b))).symm

variable [DGRing A]

/-- The right action `x • b = x * φ b` makes `A` a right dg `B`-module. -/
instance instDGRightModule : DGRightModule B φ.Bimodule where
  op_smul_mem' {i j b x} hb hx := mul_mem_grading (A := A) hx (φ.map_mem hb)
  d_op_smul' {j x} hx b := by
    change d (φ.bimoduleEquiv.symm x * φ b) = (d (φ.bimoduleEquiv.symm x)) * φ b +
      koszulSign j • (φ.bimoduleEquiv.symm x * φ (d b))
    rw [DGRingHom.map_d]
    exact d_mul (A := A) hx (φ b)

/-- `A` is a dg `(A, B)`-bimodule through `φ`. -/
instance instDGBimodule : DGBimodule A B φ.Bimodule := DGBimodule.mk'

end DGRingHom.Bimodule

end Bimodule

/-! ### Functoriality of `M ⊗_B -` for a dg bimodule `M` -/

section LTensor

variable (A : Type*) {B : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGRightModule B M] [SMulCommClass A Bᵐᵒᵖ M]
  {N N' N'' : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']
  [AddCommGroup N''] [DGAddCommGroup N''] [Module B N''] [DGModule B N'']

/-- For a dg `(A, B)`-bimodule `M`, a morphism of dg `B`-modules `g : N → N'` induces the
morphism of dg `A`-modules `M ⊗_B N → M ⊗_B N'`, `m ⊗ n ↦ m ⊗ g n`. -/
def DGModuleHom.lTensor (g : N →ᵈᵍ[B] N') :
    TensorProductOver B M N →ᵈᵍ[A] TensorProductOver B M N' where
  toFun := TensorProductOver.map LinearMap.id g.toLinearMap
  map_add' := map_add _
  map_smul' a y := by
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, RingHom.id_apply] at *
  map_mem' hy := TensorProductOver.map_mem _ _ (fun h => h) (fun h => g.map_mem h) hy
  map_d' y := TensorProductOver.map_d_of_dgModuleHom _ g (fun h => h) (fun _ => rfl) y

variable {A M}

@[simp]
theorem DGModuleHom.lTensor_tmul (g : N →ᵈᵍ[B] N') (m : M) (n : N) :
    DGModuleHom.lTensor A M g (TensorProductOver.tmul B m n) =
      TensorProductOver.tmul B m (g n) := rfl

variable (A M N) in
@[simp]
theorem DGModuleHom.lTensor_id :
    DGModuleHom.lTensor A M (DGModuleHom.id : N →ᵈᵍ[B] N) = DGModuleHom.id :=
  DGModuleHom.ext fun y => DFunLike.congr_fun (TensorProductOver.map_id (A := B)) y

theorem DGModuleHom.lTensor_comp (g : N' →ᵈᵍ[B] N'') (f : N →ᵈᵍ[B] N') :
    DGModuleHom.lTensor A M (g.comp f) =
      (DGModuleHom.lTensor A M g).comp (DGModuleHom.lTensor A M f) :=
  DGModuleHom.ext fun y => DFunLike.congr_fun (TensorProductOver.map_comp LinearMap.id
    LinearMap.id f.toLinearMap g.toLinearMap) y

end LTensor

namespace DGModuleCat

/-! ### Restriction of scalars -/

section Restrict

variable {A : Type u₁} {B : Type u₂} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  (φ : B →ᵈᵍ+* A)

/-- Restriction of scalars along a morphism of dg rings `φ : B →ᵈᵍ+* A`, as a functor
`DGModuleCat A ⥤ DGModuleCat B`: a dg `A`-module `M` becomes the dg `B`-module
`RestrictScalars φ M`, with `b • m = φ b • m`. -/
def restrictScalars : DGModuleCat.{v} A ⥤ DGModuleCat.{v} B where
  obj M := of B (RestrictScalars φ M)
  map f := ofHom (f.hom.restrictScalars φ)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem restrictScalars_map_apply {M N : DGModuleCat.{v} A} (f : M ⟶ N) (x : M) :
    (restrictScalars φ).map f x = f x := rfl

instance restrictScalars_additive : (restrictScalars.{v} φ).Additive where
  map_add := rfl

instance restrictScalars_faithful : (restrictScalars.{v} φ).Faithful where
  map_injective h := hom_ext_apply fun x => congrArg (fun g => g x) h

/-- Restriction of scalars does not change the underlying abelian groups. -/
def restrictScalarsCompForget :
    restrictScalars.{v} φ ⋙ CategoryTheory.forget (DGModuleCat.{v} B) ≅
      CategoryTheory.forget (DGModuleCat.{v} A) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

section Exact

variable [DGRing A] [DGRing B]

/-- Restriction of scalars commutes with the forgetful functors to cochain complexes of abelian
groups: the underlying complex of `RestrictScalars φ M` is that of `M`. -/
def restrictScalarsCompForgetToAddCommGrp :
    restrictScalars.{v} φ ⋙ forgetToAddCommGrp B ≅ forgetToAddCommGrp A :=
  NatIso.ofComponents (fun M => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by
      rintro i _ rfl
      ext x
      change (forget₂ (ModuleCat ℤ) AddCommGrp).map ((toComplex ℤ M).d i (i + 1)) x =
        (forget₂ (ModuleCat ℤ) AddCommGrp).map
          ((toComplex ℤ ((restrictScalars φ).obj M)).d i (i + 1)) x
      rw [toComplex_d, toComplex_d]
      rfl)) (fun _ => by ext; rfl)

/-- Restriction of scalars preserves kernels. -/
instance restrictScalars_preservesKernel {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (restrictScalars.{v} φ) := by
  have h : ((ShortComplex.mk _ _ (kernelFork f).condition).map (restrictScalars φ)).Exact :=
    (exact_iff_function_exact _).2 fun y =>
      ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  have : Mono ((ShortComplex.mk _ _ (kernelFork f).condition).map (restrictScalars φ)).f :=
    (mono_iff_injective _).2 Subtype.val_injective
  exact preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
    ((KernelFork.isLimitMapConeEquiv _ _).symm h.fIsKernel)

/-- Restriction of scalars preserves cokernels. -/
instance restrictScalars_preservesCokernel {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (restrictScalars.{v} φ) := by
  have h : ((ShortComplex.mk _ _ (cokernelCofork f).condition).map (restrictScalars φ)).Exact :=
    (exact_iff_function_exact _).2 fun _ => f.hom.range.mkQ_eq_zero_iff
  have : Epi ((ShortComplex.mk _ _ (cokernelCofork f).condition).map (restrictScalars φ)).g :=
    (epi_iff_surjective _).2 f.hom.range.mkQ_surjective
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm h.gIsCokernel)

/-- Restriction of scalars is left exact. -/
instance restrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (restrictScalars.{v} φ) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- Restriction of scalars is right exact. -/
instance restrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (restrictScalars.{v} φ) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- Restriction of scalars maps short exact sequences to short exact sequences. -/
theorem shortExact_map_restrictScalars {S : ShortComplex (DGModuleCat.{v} A)}
    (hS : S.ShortExact) : (S.map (restrictScalars φ)).ShortExact :=
  hS.map_of_exact _

end Exact

/-- Restriction of scalars along a morphism of dg `R`-algebras is `R`-linear. -/
instance restrictScalars_linear (R : Type*) [CommRing R] [Algebra R A] [Algebra R B] [DGRing A]
    [DGRing B] [DGAlgebra R A] [DGAlgebra R B] (f : B →ᵈᵍₐ[R] A) :
    (restrictScalars.{v} f.toDGRingHom).Linear R where
  map_smul g r := hom_ext_apply fun m => by
    change algebraMap R A r • g m = f (algebraMap R B r) • g m
    rw [AlgHomClass.commutes]

end Restrict

/-! ### Extension of scalars -/

section Extend

variable {A : Type u₁} {B : Type u₂} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B]
  [DGAddCommGroup B] (φ : B →ᵈᵍ+* A)

open TensorProductOver DGRingHom.Bimodule

/-- Extension of scalars along a morphism of dg rings `φ : B →ᵈᵍ+* A`, as a functor
`DGModuleCat B ⥤ DGModuleCat A`: `N ↦ A ⊗_B N`, where `A` is the dg `(A, B)`-bimodule
`φ.Bimodule`, with `a • (x ⊗ n) = (a * x) ⊗ n`. -/
def extendScalars : DGModuleCat.{max v u₁} B ⥤ DGModuleCat.{max v u₁} A where
  obj N := of A (TensorProductOver B φ.Bimodule N)
  map g := ofHom (DGModuleHom.lTensor A φ.Bimodule g.hom)
  map_id N := hom_ext (DGModuleHom.lTensor_id A φ.Bimodule N)
  map_comp f g := hom_ext (DGModuleHom.lTensor_comp g.hom f.hom)

@[simp]
theorem extendScalars_map_tmul {N N' : DGModuleCat.{max v u₁} B} (g : N ⟶ N') (x : φ.Bimodule)
    (n : N) : (extendScalars φ).map g (tmul B x n) = tmul B x (g n) := rfl

variable {φ}

/-- The element `1 ⊗ n` of `A ⊗_B N`. -/
theorem one_tmul_mem_grading {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N]
    [DGModule B N] {k : ℤ} {n : N} (hn : n ∈ grading k) :
    tmul B (φ.bimoduleEquiv 1) n ∈ grading k := by
  simpa using TensorProductOver.tmul_mem_grading
    (bimoduleEquiv_mem_grading_iff.mpr (one_mem_grading (A := A))) hn

namespace ExtendScalars

variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

omit [DGRing A] [DGAddCommGroup N] [DGModule B N] in
/-- `1 ⊗ (b • n) = φ b • (1 ⊗ n)` in `A ⊗_B N`. -/
theorem tmul_smul_eq (b : B) (n : N) :
    tmul B (φ.bimoduleEquiv 1) (b • n) = φ b • tmul B (φ.bimoduleEquiv 1) n := by
  rw [← op_smul_tmul, op_smul_bimoduleEquiv, smul_tmul, smul_bimoduleEquiv, one_mul, mul_one]

/-- `d (1 ⊗ n) = 1 ⊗ d n` in `A ⊗_B N`. -/
theorem d_one_tmul (n : N) :
    d (tmul B (φ.bimoduleEquiv 1) n) = tmul B (φ.bimoduleEquiv 1) (d n) := by
  rw [TensorProductOver.d_tmul_of_mem
      (bimoduleEquiv_mem_grading_iff.mpr (one_mem_grading (A := A))),
    d_bimoduleEquiv, d_one, map_zero, zero_tmul, zero_add, koszulSign, Int.negOnePow_zero,
    one_smul]

variable (φ) in
/-- The restriction `n ↦ f (1 ⊗ n)` of a morphism `f : A ⊗_B N → M` of dg `A`-modules, a
morphism of dg `B`-modules `N → RestrictScalars φ M`. -/
def homEquivToFun (f : TensorProductOver B φ.Bimodule N →ᵈᵍ[A] M) :
    N →ᵈᵍ[B] RestrictScalars φ M where
  toFun n := f (tmul B (φ.bimoduleEquiv 1) n)
  map_add' n n' := by rw [tmul_add, map_add]
  map_smul' b n := by
    rw [RingHom.id_apply, tmul_smul_eq, map_smul]
    rfl
  map_mem' hn := f.map_mem (one_tmul_mem_grading hn)
  map_d' n := by rw [← d_one_tmul, f.map_d]; rfl

omit [DGModule A M] in
theorem homEquivToFun_apply (f : TensorProductOver B φ.Bimodule N →ᵈᵍ[A] M) (n : N) :
    homEquivToFun φ f n = f (tmul B (φ.bimoduleEquiv 1) n) := rfl

variable (φ) in
/-- The bi-additive map `(x, n) ↦ x • g n`. -/
def homEquivInvFunAux (g : N →ᵈᵍ[B] RestrictScalars φ M) : φ.Bimodule →+ N →+ M :=
  ((smulAddHom A M).comp φ.bimoduleEquiv.symm.toLinearMap.toAddMonoidHom).compl₂
    ((RestrictScalars.addEquiv φ (M := M)).toAddMonoidHom.comp g.toLinearMap.toAddMonoidHom)

omit [DGRing A] [DGModule B N] [DGModule A M] in
theorem homEquivInvFunAux_apply (g : N →ᵈᵍ[B] RestrictScalars φ M) (x : φ.Bimodule) (n : N) :
    homEquivInvFunAux φ g x n = φ.bimoduleEquiv.symm x • RestrictScalars.addEquiv φ (g n) :=
  rfl

omit [DGRing A] [DGModule B N] [DGModule A M] in
theorem homEquivInvFunAux_balanced (g : N →ᵈᵍ[B] RestrictScalars φ M) (b : B)
    (x : φ.Bimodule) (n : N) :
    homEquivInvFunAux φ g (op b • x) n = homEquivInvFunAux φ g x (b • n) := by
  rw [homEquivInvFunAux_apply, homEquivInvFunAux_apply, map_smul g b n]
  exact mul_smul (φ.bimoduleEquiv.symm x) (φ b) (RestrictScalars.addEquiv φ (g n))

variable (φ) in
/-- The morphism of dg `A`-modules `A ⊗_B N → M`, `x ⊗ n ↦ x • g n`, induced by a morphism of
dg `B`-modules `g : N → RestrictScalars φ M`. -/
def homEquivInvFun (g : N →ᵈᵍ[B] RestrictScalars φ M) :
    TensorProductOver B φ.Bimodule N →ᵈᵍ[A] M where
  toFun := lift (homEquivInvFunAux φ g) (homEquivInvFunAux_balanced g)
  map_add' := map_add _
  map_smul' a y := by
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | tmul x n =>
      exact mul_smul a (φ.bimoduleEquiv.symm x) (RestrictScalars.addEquiv φ (g n))
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, RingHom.id_apply] at *
  map_mem' hy := lift_mem _ _ (fun {_ _ x n} hx hn => smul_mem_grading (A := A) (M := M)
    (a := φ.bimoduleEquiv.symm x) (m := RestrictScalars.addEquiv φ (g n)) hx (g.map_mem hn)) hy
  map_d' y := lift_d _ _ (fun {i x} hx n => by
    simp only [homEquivInvFunAux_apply]
    rw [g.map_d]
    exact d_smul (A := A) (M := M) (a := φ.bimoduleEquiv.symm x) hx
      (RestrictScalars.addEquiv φ (g n))) y

theorem homEquivInvFun_tmul (g : N →ᵈᵍ[B] RestrictScalars φ M) (x : φ.Bimodule) (n : N) :
    homEquivInvFun φ g (tmul B x n) =
      φ.bimoduleEquiv.symm x • RestrictScalars.addEquiv φ (g n) := rfl

variable (φ N M) in
/-- The adjunction bijection `(A ⊗_B N →ᵈᵍ[A] M) ≃ (N →ᵈᵍ[B] RestrictScalars φ M)`,
`f ↦ (n ↦ f (1 ⊗ n))`, with inverse `g ↦ (x ⊗ n ↦ x • g n)`. -/
def homEquiv :
    (TensorProductOver B φ.Bimodule N →ᵈᵍ[A] M) ≃ (N →ᵈᵍ[B] RestrictScalars φ M) where
  toFun := homEquivToFun φ
  invFun := homEquivInvFun φ
  left_inv f := DGModuleHom.ext fun y => by
    induction y using TensorProductOver.induction_on with
    | zero => simp
    | tmul x n =>
      rw [homEquivInvFun_tmul]
      change φ.bimoduleEquiv.symm x • f (tmul B (φ.bimoduleEquiv 1) n) = f (tmul B x n)
      rw [← map_smul, smul_tmul, smul_bimoduleEquiv, mul_one]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv g := DGModuleHom.ext fun n => one_smul A (RestrictScalars.addEquiv φ (g n))

@[simp]
theorem homEquiv_apply (f : TensorProductOver B φ.Bimodule N →ᵈᵍ[A] M) (n : N) :
    homEquiv φ N M f n = f (tmul B (φ.bimoduleEquiv 1) n) := rfl

@[simp]
theorem homEquiv_symm_tmul (g : N →ᵈᵍ[B] RestrictScalars φ M) (x : φ.Bimodule) (n : N) :
    (homEquiv φ N M).symm g (tmul B x n) =
      φ.bimoduleEquiv.symm x • RestrictScalars.addEquiv φ (g n) := rfl

end ExtendScalars

variable (φ)

/-- Extension of scalars is left adjoint to restriction of scalars:
`(A ⊗_B N ⟶ M) ≃ (N ⟶ RestrictScalars φ M)`, `f ↦ (n ↦ f (1 ⊗ n))`. -/
def extendRestrictScalarsAdj :
    extendScalars.{v} φ ⊣ restrictScalars.{max v u₁} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N M =>
        (DGModuleCat.homEquiv.trans (ExtendScalars.homEquiv φ N M)).trans
          (DGModuleCat.homEquiv (M := N) (N := (restrictScalars φ).obj M)).symm
      homEquiv_naturality_left_symm := fun f g => hom_ext_apply fun y => by
        induction y using TensorProductOver.induction_on with
        | zero => simp
        | tmul x n => rfl
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      homEquiv_naturality_right := fun _ _ => rfl }

@[simp]
theorem extendRestrictScalarsAdj_homEquiv_apply {N : DGModuleCat.{max v u₁} B}
    {M : DGModuleCat.{max v u₁} A} (f : (extendScalars φ).obj N ⟶ M) (n : N) :
    (extendRestrictScalarsAdj φ).homEquiv N M f n = f (tmul B (φ.bimoduleEquiv 1) n) := rfl

@[simp]
theorem extendRestrictScalarsAdj_homEquiv_symm_apply_tmul {N : DGModuleCat.{max v u₁} B}
    {M : DGModuleCat.{max v u₁} A} (g : N ⟶ (restrictScalars φ).obj M) (x : φ.Bimodule)
    (n : N) :
    ((extendRestrictScalarsAdj φ).homEquiv N M).symm g (tmul B x n) =
      φ.bimoduleEquiv.symm x • RestrictScalars.addEquiv φ (M := M) (g n) := rfl

end Extend

/-! ### Functoriality in the morphism of dg rings -/

section Functoriality

variable {A B C : Type u} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B] [Ring C]
  [DGAddCommGroup C]

variable (A) in
/-- Restriction of scalars along the identity is the identity functor. -/
def restrictScalarsId : restrictScalars.{v} (DGRingHom.id : A →ᵈᵍ+* A) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

/-- Restriction of scalars along a composite is the composite of the restrictions. -/
def restrictScalarsComp (φ : B →ᵈᵍ+* A) (ψ : A →ᵈᵍ+* C) :
    restrictScalars.{v} (ψ.comp φ) ≅ restrictScalars ψ ⋙ restrictScalars φ :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

variable [DGRing A] [DGRing B] [DGRing C]

variable (A) in
/-- Extension of scalars along the identity is isomorphic to the identity functor (by uniqueness
of left adjoints). -/
def extendScalarsId : extendScalars.{v} (DGRingHom.id : A →ᵈᵍ+* A) ≅ 𝟭 _ :=
  (extendRestrictScalarsAdj _).leftAdjointUniq (Adjunction.id.ofNatIsoRight
    (restrictScalarsId A).symm)

/-- Extension of scalars along a composite is isomorphic to the composite of the extensions (by
uniqueness of left adjoints). -/
def extendScalarsComp (φ : B →ᵈᵍ+* A) (ψ : A →ᵈᵍ+* C) :
    extendScalars.{v} (ψ.comp φ) ≅ extendScalars φ ⋙ extendScalars ψ :=
  (extendRestrictScalarsAdj _).leftAdjointUniq (((extendRestrictScalarsAdj φ).comp
    (extendRestrictScalarsAdj ψ)).ofNatIsoRight (restrictScalarsComp φ ψ).symm)

end Functoriality

end DGModuleCat

end DG
