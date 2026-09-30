import Mathlib.Algebra.GradedMulAction
import DG.Algebra.Basic

/-!
# Differential graded modules

* `DGModule A M`: a `Prop`-valued mixin on a dg abelian group `M` (`DGAddCommGroup M`) with a
  module structure `Module A M` over a dg ring `A`, saying that the action is graded
  (`Aⁱ • Mʲ ⊆ Mⁱ⁺ʲ`) and satisfies the signed Leibniz rule
  `d (a • m) = d a • m + (-1)^{|a|} • (a • d m)`.
* `DGModuleHom A M N` (notation `M →ᵈᵍ[A] N`): `A`-linear maps of degree `0` commuting with the
  differentials — the morphisms of the category of dg modules.

A dg ring is a dg module over itself (`DG.DGModule.regular`). If `A` is a dg `R`-algebra and
`M` is a dg `A`-module with a compatible `R`-module structure (`IsScalarTower R A M`), then
`d` is `R`-linear and the graded pieces are `R`-submodules.

Right modules and bimodules are further mixins (`DG.Module.Right`).
-/

open DirectSum

namespace DG

/-- A left differential graded module over a dg ring `A`: a dg abelian group `M` with an
`A`-module structure such that the action is graded and satisfies the signed Leibniz rule
`d (a • m) = d a • m + (-1)^{|a|} • (a • d m)`. -/
class DGModule (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A] [AddCommGroup M]
    [DGAddCommGroup M] [Module A M] : Prop
    extends SetLike.GradedSMul (grading (M := A)) (grading (M := M)) where
  d_smul' : ∀ {n : ℤ} {a : A}, a ∈ grading n → ∀ m : M,
    d (a • m) = d a • m + koszulSign n • (a • d m)

section DGModule

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [DGModule A M]

theorem smul_mem_grading {i j : ℤ} {a : A} {m : M} (ha : a ∈ grading i) (hm : m ∈ grading j) :
    a • m ∈ grading (i + j) :=
  SetLike.GradedSMul.smul_mem ha hm

/-- The signed Leibniz rule for the action. -/
theorem d_smul {n : ℤ} {a : A} (ha : a ∈ grading n) (m : M) :
    d (a • m) = d a • m + koszulSign n • (a • d m) :=
  DGModule.d_smul' ha m

theorem d_smul_of_even {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Even n) (m : M) :
    d (a • m) = d a • m + a • d m := by
  rw [d_smul ha, koszulSign_even hn, one_smul]

theorem d_smul_of_odd {n : ℤ} {a : A} (ha : a ∈ grading n) (hn : Odd n) (m : M) :
    d (a • m) = d a • m - a • d m := by
  rw [d_smul ha, koszulSign_odd hn, Units.neg_smul, one_smul, sub_eq_add_neg]

theorem d_smul_of_mem_zero {a : A} (ha : a ∈ grading 0) (m : M) :
    d (a • m) = d a • m + a • d m :=
  d_smul_of_even ha Even.zero m

/-- For a cocycle `a`, `d (a • m) = (-1)^{|a|} • (a • d m)`. -/
theorem d_smul_of_d_eq_zero {n : ℤ} {a : A} (ha : a ∈ grading n) (hda : d a = 0) (m : M) :
    d (a • m) = koszulSign n • (a • d m) := by
  rw [d_smul ha, hda, zero_smul, zero_add]

/-- For a cocycle `m`, `d (a • m) = d a • m` for every `a`. -/
theorem d_smul_of_d_eq_zero_right {m : M} (hm : d m = 0) (a : A) : d (a • m) = d a • m := by
  induction a using induction_on with
  | h_zero => simp
  | h_homogeneous a => rw [d_smul a.2, hm, smul_zero, smul_zero, add_zero]
  | h_add a a' ha ha' => rw [add_smul, d_add, ha, ha', d_add, add_smul]

/-- A dg ring is a dg module over itself. -/
instance DGModule.regular {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] : DGModule A A where
  smul_mem _ _ _ _ ha hb := mul_mem_grading ha hb
  d_smul' ha b := d_mul ha b

end DGModule

section Ground

variable (R : Type*) (A : Type*) {M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [DGAddCommGroup A] [DGRing A] [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M]
  [Module A M] [DGModule A M] [Module R M] [IsScalarTower R A M]

include A

variable {R} in
theorem DGModule.ground_smul_mem {n : ℤ} (r : R) {m : M} (hm : m ∈ grading n) :
    r • m ∈ grading n := by
  rw [← algebraMap_smul A r m]
  simpa using smul_mem_grading (algebraMap_mem_grading R (A := A) r) hm

variable {R} in
/-- The differential of a dg module over a dg `R`-algebra is `R`-linear. -/
theorem d_ground_smul (r : R) (m : M) : d (r • m) = r • d m := by
  rw [← algebraMap_smul A r m, d_smul (algebraMap_mem_grading R (A := A) r), d_algebraMap,
    zero_smul,
    zero_add, koszulSign, Int.negOnePow_zero, one_smul, algebraMap_smul]

variable (M)

/-- The graded pieces of a dg module over a dg `R`-algebra, as `R`-submodules. -/
def DGModule.gradingSubmodule (n : ℤ) : Submodule R M where
  __ := grading (M := M) n
  smul_mem' r _ hm := DGModule.ground_smul_mem A r hm

@[simp]
theorem DGModule.mem_gradingSubmodule {n : ℤ} {m : M} :
    m ∈ DGModule.gradingSubmodule R A M n ↔ m ∈ grading n :=
  Iff.rfl

instance DGModule.decompositionSubmodule :
    DirectSum.Decomposition (DGModule.gradingSubmodule R A M) where
  decompose' := DirectSum.decompose (grading (M := M))
  left_inv := DirectSum.Decomposition.left_inv (ℳ := grading (M := M))
  right_inv := DirectSum.Decomposition.right_inv (ℳ := grading (M := M))

/-- The differential of a dg module over a dg `R`-algebra as an `R`-linear map. -/
def DGModule.dLinear : M →ₗ[R] M where
  __ := (d : M →+ M)
  map_smul' := d_ground_smul A

@[simp]
theorem DGModule.dLinear_apply (m : M) : DGModule.dLinear R A M m = d m := rfl

end Ground

/-- A morphism of dg `A`-modules: an `A`-linear map of degree `0` commuting with the
differentials. -/
structure DGModuleHom (A : Type*) (M : Type*) (N : Type*) [Ring A] [DGAddCommGroup A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] extends M →ₗ[A] N where
  map_mem' : ∀ {n : ℤ} {m : M}, m ∈ grading n → toFun m ∈ grading n
  map_d' : ∀ m : M, toFun (d m) = d (toFun m)

@[inherit_doc]
notation:25 M " →ᵈᵍ[" A "] " N => DGModuleHom A M N

namespace DGModuleHom

variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

instance : FunLike (M →ᵈᵍ[A] N) M N where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _, _⟩ := g
    congr

instance : LinearMapClass (M →ᵈᵍ[A] N) A M N where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'

@[simp]
theorem coe_toLinearMap (f : M →ᵈᵍ[A] N) : ⇑f.toLinearMap = f := rfl

@[simp]
theorem toLinearMap_apply (f : M →ᵈᵍ[A] N) (m : M) : f.toLinearMap m = f m := rfl

@[ext]
theorem ext {f g : M →ᵈᵍ[A] N} (h : ∀ m, f m = g m) : f = g :=
  DFunLike.ext f g h

theorem toLinearMap_injective :
    Function.Injective (DGModuleHom.toLinearMap : (M →ᵈᵍ[A] N) → M →ₗ[A] N) :=
  fun _ _ h => ext fun m => congrArg (fun φ : M →ₗ[A] N => φ m) h

theorem map_mem (f : M →ᵈᵍ[A] N) {n : ℤ} {m : M} (hm : m ∈ grading n) : f m ∈ grading n :=
  f.map_mem' hm

@[simp]
theorem map_d (f : M →ᵈᵍ[A] N) (m : M) : f (d m) = d (f m) :=
  f.map_d' m

/-- The identity morphism. -/
def id : M →ᵈᵍ[A] M where
  __ := LinearMap.id
  map_mem' hm := hm
  map_d' _ := rfl

@[simp]
theorem id_apply (m : M) : (DGModuleHom.id : M →ᵈᵍ[A] M) m = m := rfl

/-- Composition of morphisms. -/
def comp (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) : M →ᵈᵍ[A] P where
  __ := g.toLinearMap.comp f.toLinearMap
  map_mem' hm := g.map_mem (f.map_mem hm)
  map_d' m := by simp

@[simp]
theorem comp_apply (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) (m : M) : g.comp f m = g (f m) := rfl

@[simp]
theorem comp_id (f : M →ᵈᵍ[A] N) : f.comp DGModuleHom.id = f := rfl

@[simp]
theorem id_comp (f : M →ᵈᵍ[A] N) : DGModuleHom.id.comp f = f := rfl

theorem comp_assoc {Q : Type*} [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q]
    (h : P →ᵈᵍ[A] Q) (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

instance : Zero (M →ᵈᵍ[A] N) :=
  ⟨{ (0 : M →ₗ[A] N) with
      map_mem' := fun _ => zero_mem _
      map_d' := fun _ => by simp }⟩

instance : Add (M →ᵈᵍ[A] N) :=
  ⟨fun f g =>
    { f.toLinearMap + g.toLinearMap with
      map_mem' := fun hm => add_mem (f.map_mem hm) (g.map_mem hm)
      map_d' := fun m => by simp [d_add] }⟩

instance : Neg (M →ᵈᵍ[A] N) :=
  ⟨fun f =>
    { -f.toLinearMap with
      map_mem' := fun hm => neg_mem (f.map_mem hm)
      map_d' := fun m => by simp [d_neg] }⟩

instance : Sub (M →ᵈᵍ[A] N) :=
  ⟨fun f g =>
    { f.toLinearMap - g.toLinearMap with
      map_mem' := fun hm => sub_mem (f.map_mem hm) (g.map_mem hm)
      map_d' := fun m => by simp [d_sub] }⟩

@[simp] theorem zero_apply (m : M) : (0 : M →ᵈᵍ[A] N) m = 0 := rfl
@[simp] theorem add_apply (f g : M →ᵈᵍ[A] N) (m : M) : (f + g) m = f m + g m := rfl
@[simp] theorem neg_apply (f : M →ᵈᵍ[A] N) (m : M) : (-f) m = -f m := rfl
@[simp] theorem sub_apply (f g : M →ᵈᵍ[A] N) (m : M) : (f - g) m = f m - g m := rfl

instance : SMul ℕ (M →ᵈᵍ[A] N) :=
  ⟨fun k f =>
    { k • f.toLinearMap with
      map_mem' := fun hm => nsmul_mem (f.map_mem hm) k
      map_d' := fun m => by simp [d_nsmul] }⟩

instance : SMul ℤ (M →ᵈᵍ[A] N) :=
  ⟨fun k f =>
    { k • f.toLinearMap with
      map_mem' := fun hm => zsmul_mem (f.map_mem hm) k
      map_d' := fun m => by simp [d_zsmul] }⟩

@[simp] theorem nsmul_apply (k : ℕ) (f : M →ᵈᵍ[A] N) (m : M) : (k • f) m = k • f m := rfl
@[simp] theorem zsmul_apply (k : ℤ) (f : M →ᵈᵍ[A] N) (m : M) : (k • f) m = k • f m := rfl

instance : AddCommGroup (M →ᵈᵍ[A] N) :=
  toLinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem toLinearMap_zero : (0 : M →ᵈᵍ[A] N).toLinearMap = 0 := rfl
@[simp] theorem toLinearMap_add (f g : M →ᵈᵍ[A] N) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl
@[simp] theorem toLinearMap_neg (f : M →ᵈᵍ[A] N) : (-f).toLinearMap = -f.toLinearMap := rfl
@[simp] theorem toLinearMap_sub (f g : M →ᵈᵍ[A] N) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap := rfl

theorem comp_add (g : N →ᵈᵍ[A] P) (f f' : M →ᵈᵍ[A] N) :
    g.comp (f + f') = g.comp f + g.comp f' := by ext; simp
theorem add_comp (g g' : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) :
    (g + g').comp f = g.comp f + g'.comp f := by ext; simp
@[simp] theorem comp_zero (g : N →ᵈᵍ[A] P) : g.comp (0 : M →ᵈᵍ[A] N) = 0 := by ext; simp
@[simp] theorem zero_comp (f : M →ᵈᵍ[A] N) : (0 : N →ᵈᵍ[A] P).comp f = 0 := by ext; simp

/-- A morphism of dg modules is a graded map of degree `0`: it preserves each `Mⁿ`. -/
def restrict (f : M →ᵈᵍ[A] N) (n : ℤ) : grading (M := M) n →+ grading (M := N) n where
  toFun m := ⟨f m, f.map_mem m.2⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

@[simp]
theorem coe_restrict_apply (f : M →ᵈᵍ[A] N) (n : ℤ) (m : grading (M := M) n) :
    (f.restrict n m : N) = f m := rfl

theorem restrict_comp_dHom (f : M →ᵈᵍ[A] N) (n : ℤ) :
    (f.restrict (n + 1)).comp (dHom M n) = (dHom N n).comp (f.restrict n) := by
  ext; simp

end DGModuleHom

end DG
