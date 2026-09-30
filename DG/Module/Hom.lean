import DG.Graded.Hom
import DG.Module.Basic

/-!
# The Hom complex of dg modules

Let `A` be a dg ring and `M`, `N` dg `A`-modules. This file constructs the Hom complex
`HOM_A(M, N)`, whose degree-`n` part consists of the graded `A`-linear maps of degree `n`
(with the Koszul sign), and whose differential is `δ f = d_N ∘ f - (-1)^{|f|} f ∘ d_M`. The API
is modelled on Mathlib's `CochainComplex.HomComplex` (`Mathlib/Algebra/Homology/HomotopyCategory/
HomComplex.lean`), with the same names, so that constructions written against that API
(mapping cones, the pretriangulated structure of the homotopy category) can be transported.

## Main definitions

* `DG.Cochain A M N n`: the `A`-linear maps of degree `n` from `M` to `N`, that is, the additive
  maps `f` sending `Mⁱ` into `Nⁱ⁺ⁿ` with `f (a • x) = (-1)^{n i} • (a • f x)` for `a ∈ Aⁱ`.
  These form an additive group.
* `DG.Cochain.comp z₂ z₁ h`: the composition `z₂ ∘ z₁` of cochains of degrees `n₁` and `n₂`,
  as a cochain of any degree `n₁₂` with `h : n₁ + n₂ = n₁₂`; `DG.Cochain.id A M`: the identity.
* `DG.Cochain.ofHom φ`: the `0`-cochain of a morphism of dg modules `φ : M →ᵈᵍ[A] N`, and more
  generally `DG.Cochain.ofHoms` for `A`-linear maps of degree `0`.
* `DG.δ n m z`: the differential of the Hom complex, a cochain of degree `m`, equal to
  `d ∘ z - (-1)^n • z ∘ d` if `n + 1 = m` and to `0` otherwise.
* `DG.cocycle A M N n`, `DG.Cocycle A M N n`: the cocycles of degree `n`, and
  `DG.Cocycle.equivHom : (M →ᵈᵍ[A] N) ≃+ Cocycle A M N 0`.
* `DG.DGModule.HOM A M N := ⨁ n, Cochain A M N n`: the Hom complex as a dg abelian group.

## Main results

* `DG.δ_δ`: `δ ∘ δ = 0`.
* `DG.δ_comp`: the Leibniz rule `δ (z₂ ∘ z₁) = δ z₂ ∘ z₁ + (-1)^{n₂} • z₂ ∘ δ z₁` for `z₂` of
  degree `n₂`.
* `DG.δ_ofHom`, `DG.Cocycle.equivHom`: the degree-`0` cocycles are exactly the morphisms of dg
  modules.

## Conventions and comparison with Mathlib

* Cochains are functions: `Cochain.comp` is written in the usual order, `z₂.comp z₁ h` applies
  `z₁` first (as `GradedHom.comp` and `LinearMap.comp`), whereas Mathlib's `Cochain.comp` is in
  diagrammatic order. Mathlib's `z₁.comp z₂ h` corresponds to `z₂.comp z₁ h` here, with the same
  degree hypothesis `h : n₁ + n₂ = n₁₂` (the degree of the map applied first comes first), and
  Mathlib's `comp_id`/`id_comp` correspond to `id_comp`/`comp_id` here.
* The differential agrees with Mathlib's: `δ z = d ∘ z - (-1)^n • z ∘ d = d ∘ z + (-1)^m • z ∘ d`
  for `n + 1 = m` (`DG.δ_apply`, `DG.δ_apply'`); in Mathlib this reads
  `z ≫ d + m.negOnePow • d ≫ z`.
* Signs are `koszulSign n = Int.negOnePow n : ℤˣ`, acting through the `ℤˣ`-action.
-/

open DirectSum

namespace DG

section Defs

variable (A : Type*) (M : Type*) (N : Type*) [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- A cochain of degree `n` from `M` to `N` (a homogeneous element of degree `n` of the Hom
complex `HOM_A(M, N)`): an additive map of degree `n` which is `A`-linear with the Koszul sign,
`f (a • x) = (-1)^{n i} • (a • f x)` for `a ∈ Aⁱ`. This is the analogue of Mathlib's
`CochainComplex.HomComplex.Cochain`. -/
structure Cochain (n : ℤ) extends GradedHom (grading (M := M)) (grading (M := N)) n where
  /-- The Koszul-signed `A`-linearity: `f (a • x) = (-1)^{n i} • (a • f x)` for `a ∈ Aⁱ`. -/
  map_smul' : ∀ {i : ℤ} {a : A}, a ∈ grading i → ∀ x : M,
    toFun (a • x) = koszulSign (n * i) • (a • toFun x)

end Defs

theorem units_smul_mem_grading {M : Type*} [AddCommGroup M] [DGAddCommGroup M] (u : ℤˣ)
    {n : ℤ} {x : M} (hx : x ∈ grading n) : u • x ∈ grading n := by
  rw [Units.smul_def]; exact zsmul_mem hx _

namespace Cochain

variable {A : Type*} {M N P Q : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]
  [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q]

section Basic

variable {n : ℤ}

instance : FunLike (Cochain A M N n) M N where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := g
    congr

instance : AddMonoidHomClass (Cochain A M N n) M N where
  map_add f := f.map_add'
  map_zero f := f.map_zero'

@[ext]
theorem ext {f g : Cochain A M N n} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
theorem coe_toGradedHom (f : Cochain A M N n) : ⇑f.toGradedHom = f := rfl

theorem toGradedHom_injective :
    Function.Injective (toGradedHom : Cochain A M N n → GradedHom _ _ n) := fun _ _ h =>
  ext fun x => congrArg (fun k : GradedHom _ _ n => k x) h

theorem map_mem (f : Cochain A M N n) {i : ℤ} {x : M} (hx : x ∈ grading i) :
    f x ∈ grading (i + n) :=
  f.map_mem' i x hx

theorem map_smul (f : Cochain A M N n) {i : ℤ} {a : A} (ha : a ∈ grading i) (x : M) :
    f (a • x) = koszulSign (n * i) • (a • f x) :=
  f.map_smul' ha x

theorem map_units_smul (f : Cochain A M N n) (u : ℤˣ) (x : M) : f (u • x) = u • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- Two cochains of possibly different (but equal) degrees agreeing pointwise are
heterogeneously equal. -/
theorem heq_of_forall {m n : ℤ} {f : Cochain A M N m} {g : Cochain A M N n} (hmn : m = n)
    (h : ∀ x, f x = g x) : HEq f g := by
  subst hmn
  exact heq_of_eq (ext h)

end Basic

section AddCommGroup

variable {n : ℤ}

instance : Zero (Cochain A M N n) :=
  ⟨{ (0 : GradedHom _ _ n) with map_smul' := fun _ _ => by simp }⟩

instance : Add (Cochain A M N n) :=
  ⟨fun f g =>
    { f.toGradedHom + g.toGradedHom with
      map_smul' := fun ha x => by
        show f _ + g _ = _ • (_ • (f x + g x))
        rw [f.map_smul ha, g.map_smul ha, smul_add, smul_add] }⟩

instance : Neg (Cochain A M N n) :=
  ⟨fun f =>
    { -f.toGradedHom with
      map_smul' := fun ha x => by
        show -f _ = _ • (_ • -f x)
        rw [f.map_smul ha, smul_neg, smul_neg] }⟩

instance : Sub (Cochain A M N n) :=
  ⟨fun f g =>
    { f.toGradedHom - g.toGradedHom with
      map_smul' := fun ha x => by
        show f _ - g _ = _ • (_ • (f x - g x))
        rw [f.map_smul ha, g.map_smul ha, smul_sub, smul_sub] }⟩

instance : SMul ℕ (Cochain A M N n) :=
  ⟨fun k f =>
    { k • f.toGradedHom with
      map_smul' := fun ha x => by
        show k • f _ = _ • (_ • (k • f x))
        rw [f.map_smul ha, smul_comm k, smul_comm k] }⟩

instance : SMul ℤ (Cochain A M N n) :=
  ⟨fun k f =>
    { k • f.toGradedHom with
      map_smul' := fun ha x => by
        show k • f _ = _ • (_ • (k • f x))
        rw [f.map_smul ha, smul_comm k, smul_comm k] }⟩

@[simp] theorem toGradedHom_zero : (0 : Cochain A M N n).toGradedHom = 0 := rfl
@[simp] theorem toGradedHom_add (f g : Cochain A M N n) :
    (f + g).toGradedHom = f.toGradedHom + g.toGradedHom := rfl
@[simp] theorem toGradedHom_neg (f : Cochain A M N n) :
    (-f).toGradedHom = -f.toGradedHom := rfl
@[simp] theorem toGradedHom_sub (f g : Cochain A M N n) :
    (f - g).toGradedHom = f.toGradedHom - g.toGradedHom := rfl

@[simp] theorem coe_zero : ⇑(0 : Cochain A M N n) = 0 := rfl
@[simp] theorem coe_add (f g : Cochain A M N n) : ⇑(f + g) = ⇑f + ⇑g := rfl
@[simp] theorem coe_neg (f : Cochain A M N n) : ⇑(-f) = -⇑f := rfl
@[simp] theorem coe_sub (f g : Cochain A M N n) : ⇑(f - g) = ⇑f - ⇑g := rfl
@[simp] theorem coe_nsmul (k : ℕ) (f : Cochain A M N n) : ⇑(k • f) = k • ⇑f := rfl
@[simp] theorem coe_zsmul (k : ℤ) (f : Cochain A M N n) : ⇑(k • f) = k • ⇑f := rfl

theorem zero_apply (x : M) : (0 : Cochain A M N n) x = 0 := rfl
theorem add_apply (f g : Cochain A M N n) (x : M) : (f + g) x = f x + g x := rfl
theorem neg_apply (f : Cochain A M N n) (x : M) : (-f) x = -f x := rfl
theorem sub_apply (f g : Cochain A M N n) (x : M) : (f - g) x = f x - g x := rfl
theorem nsmul_apply (k : ℕ) (f : Cochain A M N n) (x : M) : (k • f) x = k • f x := rfl
theorem zsmul_apply (k : ℤ) (f : Cochain A M N n) (x : M) : (k • f) x = k • f x := rfl

instance : AddCommGroup (Cochain A M N n) :=
  toGradedHom_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem coe_units_smul (u : ℤˣ) (f : Cochain A M N n) : ⇑(u • f) = u • ⇑f := rfl

theorem units_smul_apply (u : ℤˣ) (f : Cochain A M N n) (x : M) : (u • f) x = u • f x := rfl

end AddCommGroup

section Comp

/-- Composition of cochains: `z₂.comp z₁ h` is `z₂ ∘ z₁` (first `z₁`, then `z₂`). -/
def comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain A N P n₂) (z₁ : Cochain A M N n₁) (h : n₁ + n₂ = n₁₂) :
    Cochain A M P n₁₂ where
  toFun x := z₂ (z₁ x)
  map_zero' := by simp
  map_add' x y := by simp
  map_mem' i x hx := by
    rw [← h, ← add_assoc]
    exact z₂.map_mem (z₁.map_mem hx)
  map_smul' {i a} ha x := by
    show z₂ (z₁ _) = _ • (_ • z₂ (z₁ x))
    rw [z₁.map_smul ha, map_units_smul, z₂.map_smul ha, ← h, add_mul, koszulSign_add,
      mul_smul]

@[simp]
theorem comp_apply {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain A N P n₂) (z₁ : Cochain A M N n₁)
    (h : n₁ + n₂ = n₁₂) (x : M) : z₂.comp z₁ h x = z₂ (z₁ x) := rfl

/-- Associativity of the composition of cochains. -/
theorem comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
    (z₁ : Cochain A M N n₁) (z₂ : Cochain A N P n₂) (z₃ : Cochain A P Q n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    z₃.comp (z₂.comp z₁ h₁₂) (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) =
      (z₃.comp z₂ h₂₃).comp z₁ (by rw [← h₂₃, ← h₁₂₃, add_assoc]) :=
  rfl

@[simp]
protected theorem zero_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain A M N n₁) (h : n₁ + n₂ = n₁₂) :
    (0 : Cochain A N P n₂).comp z₁ h = 0 := rfl

@[simp]
protected theorem add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain A M N n₁) (z₂ z₂' : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) : (z₂ + z₂').comp z₁ h = z₂.comp z₁ h + z₂'.comp z₁ h := rfl

@[simp]
protected theorem sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain A M N n₁) (z₂ z₂' : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) : (z₂ - z₂').comp z₁ h = z₂.comp z₁ h - z₂'.comp z₁ h := rfl

@[simp]
protected theorem neg_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain A M N n₁) (z₂ : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) : (-z₂).comp z₁ h = -z₂.comp z₁ h := rfl

@[simp]
protected theorem zsmul_comp {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain A M N n₁)
    (z₂ : Cochain A N P n₂) (h : n₁ + n₂ = n₁₂) : (k • z₂).comp z₁ h = k • z₂.comp z₁ h := rfl

@[simp]
theorem units_smul_comp {n₁ n₂ n₁₂ : ℤ} (u : ℤˣ) (z₁ : Cochain A M N n₁)
    (z₂ : Cochain A N P n₂) (h : n₁ + n₂ = n₁₂) : (u • z₂).comp z₁ h = u • z₂.comp z₁ h := rfl

@[simp]
protected theorem comp_zero {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain A N P n₂) (h : n₁ + n₂ = n₁₂) :
    z₂.comp (0 : Cochain A M N n₁) h = 0 := ext fun _ => map_zero z₂

@[simp]
protected theorem comp_add {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain A M N n₁) (z₂ : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (z₁ + z₁') h = z₂.comp z₁ h + z₂.comp z₁' h :=
  ext fun _ => map_add z₂ _ _

@[simp]
protected theorem comp_sub {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain A M N n₁) (z₂ : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (z₁ - z₁') h = z₂.comp z₁ h - z₂.comp z₁' h :=
  ext fun _ => map_sub z₂ _ _

@[simp]
protected theorem comp_neg {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain A M N n₁) (z₂ : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (-z₁) h = -z₂.comp z₁ h :=
  ext fun _ => map_neg z₂ _

@[simp]
protected theorem comp_zsmul {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain A M N n₁)
    (z₂ : Cochain A N P n₂) (h : n₁ + n₂ = n₁₂) : z₂.comp (k • z₁) h = k • z₂.comp z₁ h :=
  ext fun _ => map_zsmul z₂ _ _

@[simp]
theorem comp_units_smul {n₁ n₂ n₁₂ : ℤ} (u : ℤˣ) (z₁ : Cochain A M N n₁)
    (z₂ : Cochain A N P n₂) (h : n₁ + n₂ = n₁₂) : z₂.comp (u • z₁) h = u • z₂.comp z₁ h :=
  ext fun _ => map_units_smul z₂ _ _

variable (A M) in
/-- The identity of `M` as a cochain of degree `0`. -/
def id : Cochain A M M 0 where
  toFun x := x
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mem' i x hx := by simpa using hx
  map_smul' _ x := by simp

@[simp]
theorem id_apply (x : M) : Cochain.id A M x = x := rfl

@[simp]
protected theorem comp_id {n : ℤ} (z : Cochain A M N n) :
    z.comp (Cochain.id A M) (zero_add n) = z := rfl

@[simp]
protected theorem id_comp {n : ℤ} (z : Cochain A M N n) :
    (Cochain.id A N).comp z (add_zero n) = z := rfl

end Comp

section OfHom

/-- The `0`-cochain given by an `A`-linear map preserving the degrees (not necessarily
commuting with the differentials). -/
def ofHoms (φ : M →ₗ[A] N) (hφ : ∀ {i : ℤ} {x : M}, x ∈ grading i → φ x ∈ grading i) :
    Cochain A M N 0 where
  toFun := φ
  map_zero' := map_zero φ
  map_add' := map_add φ
  map_mem' i x hx := by simpa using hφ hx
  map_smul' _ x := by simp

@[simp]
theorem ofHoms_apply (φ : M →ₗ[A] N)
    (hφ : ∀ {i : ℤ} {x : M}, x ∈ grading i → φ x ∈ grading i) (x : M) :
    ofHoms φ hφ x = φ x := rfl

/-- The `0`-cochain attached to a morphism of dg modules. -/
def ofHom (φ : M →ᵈᵍ[A] N) : Cochain A M N 0 := ofHoms φ.toLinearMap φ.map_mem

@[simp]
theorem ofHom_apply (φ : M →ᵈᵍ[A] N) (x : M) : ofHom φ x = φ x := rfl

variable (M N) in
@[simp]
theorem ofHom_zero : ofHom (0 : M →ᵈᵍ[A] N) = 0 := rfl

@[simp]
theorem ofHom_add (φ₁ φ₂ : M →ᵈᵍ[A] N) : ofHom (φ₁ + φ₂) = ofHom φ₁ + ofHom φ₂ := rfl

@[simp]
theorem ofHom_sub (φ₁ φ₂ : M →ᵈᵍ[A] N) : ofHom (φ₁ - φ₂) = ofHom φ₁ - ofHom φ₂ := rfl

@[simp]
theorem ofHom_neg (φ : M →ᵈᵍ[A] N) : ofHom (-φ) = -ofHom φ := rfl

@[simp]
theorem ofHom_id : ofHom (DGModuleHom.id : M →ᵈᵍ[A] M) = Cochain.id A M := rfl

@[simp]
theorem ofHom_comp (φ : M →ᵈᵍ[A] N) (ψ : N →ᵈᵍ[A] P) :
    ofHom (ψ.comp φ) = (ofHom ψ).comp (ofHom φ) (zero_add 0) := rfl

theorem ofHom_injective : Function.Injective (ofHom : (M →ᵈᵍ[A] N) → Cochain A M N 0) :=
  fun _ _ h => DGModuleHom.ext fun x => congrArg (fun z : Cochain A M N 0 => z x) h

end OfHom

end Cochain

section Differential

variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

open Cochain

/-- The differential of the Hom complex: for a cochain `z` of degree `n`, `δ n m z` is the
cochain `d ∘ z - (-1)^n • z ∘ d` of degree `m` if `n + 1 = m`, and `0` otherwise (the
convention of Mathlib's `CochainComplex.HomComplex.δ`, which avoids casts along equalities of
degrees). It is `A`-linear with the Koszul sign by the Leibniz rules of `M` and `N`. -/
def δ (n m : ℤ) (z : Cochain A M N n) : Cochain A M N m :=
  if hnm : n + 1 = m then
    { toFun := fun x => d (z x) - koszulSign n • z (d x)
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        abel
      map_mem' := fun i x hx => by
        subst hnm
        refine sub_mem ?_ (units_smul_mem_grading _ ?_)
        · have := d_mem (z.map_mem hx)
          rwa [add_assoc] at this
        · have := z.map_mem (d_mem hx)
          rwa [add_right_comm, add_assoc] at this
      map_smul' := fun {i a} ha x => by
        subst hnm
        have hda := d_mem ha
        rw [z.map_smul ha, d_units_smul, d_smul ha, d_smul ha, map_add, map_units_smul,
          z.map_smul ha, z.map_smul hda]
        rcases Int.units_eq_one_or (koszulSign n) with h₁ | h₁ <;>
        rcases Int.units_eq_one_or (koszulSign i) with h₂ | h₂ <;>
        rcases Int.units_eq_one_or (koszulSign (n * i)) with h₃ | h₃ <;>
        simp [add_mul, mul_add, koszulSign_add, h₁, h₂, h₃, smul_sub, smul_add] <;> abel }
  else 0

variable (n m : ℤ)

theorem δ_apply (hnm : n + 1 = m) (z : Cochain A M N n) (x : M) :
    δ n m z x = d (z x) - koszulSign n • z (d x) := by
  unfold δ
  rw [dite_eq_left hnm]
  rfl

/-- The differential in the form used by Mathlib's `CochainComplex.HomComplex.δ`:
`δ z = d ∘ z + (-1)^m • z ∘ d`. -/
theorem δ_apply' (hnm : n + 1 = m) (z : Cochain A M N n) (x : M) :
    δ n m z x = d (z x) + koszulSign m • z (d x) := by
  subst hnm
  rw [δ_apply n _ rfl, koszulSign, koszulSign, Int.negOnePow_succ, Units.neg_smul,
    sub_eq_add_neg]

theorem δ_shape (hnm : ¬ n + 1 = m) (z : Cochain A M N n) : δ n m z = 0 := by
  unfold δ
  rw [dite_eq_right hnm]

variable (A M N) in
/-- The differential of the Hom complex, as an additive map. -/
@[simps]
def δ_hom : Cochain A M N n →+ Cochain A M N m where
  toFun := δ n m
  map_zero' := by
    by_cases h : n + 1 = m
    · ext x
      simp [δ_apply n m h]
    · exact δ_shape n m h _
  map_add' z₁ z₂ := by
    by_cases h : n + 1 = m
    · ext x
      simp only [δ_apply n m h, Cochain.add_apply, d_add, smul_add]
      abel
    · simp only [δ_shape n m h, add_zero]

@[simp] theorem δ_add (z₁ z₂ : Cochain A M N n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
  (δ_hom A M N n m).map_add z₁ z₂

@[simp] theorem δ_sub (z₁ z₂ : Cochain A M N n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
  (δ_hom A M N n m).map_sub z₁ z₂

@[simp] theorem δ_zero : δ n m (0 : Cochain A M N n) = 0 := (δ_hom A M N n m).map_zero

@[simp] theorem δ_neg (z : Cochain A M N n) : δ n m (-z) = -δ n m z :=
  (δ_hom A M N n m).map_neg z

@[simp] theorem δ_zsmul (k : ℤ) (z : Cochain A M N n) : δ n m (k • z) = k • δ n m z :=
  (δ_hom A M N n m).map_zsmul k z

@[simp] theorem δ_units_smul (u : ℤˣ) (z : Cochain A M N n) : δ n m (u • z) = u • δ n m z := by
  rw [Units.smul_def, Units.smul_def, δ_zsmul]

/-- The differential of the Hom complex squares to zero. -/
theorem δ_δ (n₀ n₁ n₂ : ℤ) (z : Cochain A M N n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂; swap
  · rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁; swap
  · rw [δ_shape _ _ h₀₁, δ_zero]
  ext x
  rw [δ_apply _ _ h₁₂, δ_apply _ _ h₀₁, δ_apply _ _ h₀₁, Cochain.zero_apply, ← h₀₁]
  simp only [koszulSign, Int.negOnePow_succ, d_sub, d_units_smul, d_d, map_zero, smul_zero,
    sub_zero, zero_sub, Units.neg_smul, sub_neg_eq_add, neg_add_cancel]

/-- The Leibniz rule for the composition of cochains: for `z₁` of degree `n₁` and `z₂` of
degree `n₂`, `δ (z₂ ∘ z₁) = δ z₂ ∘ z₁ + (-1)^{n₂} • z₂ ∘ δ z₁`. This is Mathlib's
`CochainComplex.HomComplex.δ_comp` with the composition written in the opposite order. -/
theorem δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain A M N n₁) (z₂ : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁)
    (h₂ : n₂ + 1 = m₂) :
    δ n₁₂ m₁₂ (z₂.comp z₁ h) =
      (δ n₂ m₂ z₂).comp z₁ (by rw [← h₁₂, ← h₂, ← h, add_assoc]) +
        koszulSign n₂ • z₂.comp (δ n₁ m₁ z₁)
          (by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]) := by
  ext x
  simp only [Cochain.add_apply, units_smul_apply, comp_apply, δ_apply _ _ h₁₂, δ_apply _ _ h₁,
    δ_apply _ _ h₂, map_sub, map_units_smul, smul_sub, smul_smul, ← h, koszulSign_add,
    mul_comm (koszulSign n₁)]
  abel

theorem δ_zero_cochain_comp {n₂ : ℤ} (z₁ : Cochain A M N 0) (z₂ : Cochain A N P n₂)
    (m₂ : ℤ) (h₂ : n₂ + 1 = m₂) :
    δ n₂ m₂ (z₂.comp z₁ (zero_add n₂)) =
      (δ n₂ m₂ z₂).comp z₁ (zero_add m₂) +
        koszulSign n₂ • z₂.comp (δ 0 1 z₁) (by rw [add_comm, h₂]) :=
  δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

theorem δ_comp_zero_cochain {n₁ : ℤ} (z₁ : Cochain A M N n₁) (z₂ : Cochain A N P 0)
    (m₁ : ℤ) (h₁ : n₁ + 1 = m₁) :
    δ n₁ m₁ (z₂.comp z₁ (add_zero n₁)) =
      (δ 0 1 z₂).comp z₁ h₁ + z₂.comp (δ n₁ m₁ z₁) (add_zero m₁) := by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), koszulSign,
    Int.negOnePow_zero, one_smul]

@[simp]
theorem δ_zero_cochain_apply (z : Cochain A M N 0) (x : M) :
    δ 0 1 z x = d (z x) - z (d x) := by
  rw [δ_apply 0 1 (zero_add 1), koszulSign, Int.negOnePow_zero, one_smul]

@[simp]
theorem δ_ofHom {p : ℤ} (φ : M →ᵈᵍ[A] N) : δ 0 p (Cochain.ofHom φ) = 0 := by
  by_cases h : 0 + 1 = p
  · ext x
    rw [δ_apply 0 p h, Cochain.zero_apply, ofHom_apply, ofHom_apply, DGModuleHom.map_d, koszulSign,
      Int.negOnePow_zero, one_smul, sub_self]
  · exact δ_shape _ _ h _

end Differential

section Cocycle

variable (A : Type*) (M N : Type*) {P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- The subgroup of cocycles in `Cochain A M N n`: the kernel of `δ n (n + 1)`. -/
def cocycle (n : ℤ) : AddSubgroup (Cochain A M N n) :=
  (δ_hom A M N n (n + 1)).ker

/-- The type of `n`-cocycles from `M` to `N`. -/
abbrev Cocycle (n : ℤ) : Type _ := cocycle A M N n

namespace Cocycle

variable {A M N}

theorem mem_iff {n : ℤ} (m : ℤ) (hnm : n + 1 = m) (z : Cochain A M N n) :
    z ∈ cocycle A M N n ↔ δ n m z = 0 := by
  subst hnm; rfl

@[ext]
theorem ext {n : ℤ} {z₁ z₂ : Cocycle A M N n} (h : (z₁ : Cochain A M N n) = z₂) : z₁ = z₂ :=
  Subtype.ext h

/-- Constructor for `Cocycle A M N n`, from `z : Cochain A M N n`, an integer `m` with
`n + 1 = m`, and the relation `δ n m z = 0`. -/
@[simps]
def mk {n : ℤ} (z : Cochain A M N n) (m : ℤ) (hnm : n + 1 = m) (h : δ n m z = 0) :
    Cocycle A M N n :=
  ⟨z, (mem_iff m hnm z).2 h⟩

@[simp]
theorem δ_eq_zero {n : ℤ} (z : Cocycle A M N n) (m : ℤ) : δ n m (z : Cochain A M N n) = 0 := by
  by_cases h : n + 1 = m
  · exact (mem_iff m h _).1 z.2
  · exact δ_shape n m h _

/-- The `0`-cocycle associated to a morphism of dg modules. -/
@[simps!]
def ofHom (φ : M →ᵈᵍ[A] N) : Cocycle A M N 0 :=
  mk (Cochain.ofHom φ) 1 (zero_add 1) (δ_ofHom φ)

/-- A `0`-cocycle is `A`-linear (for all, not only homogeneous, scalars). -/
theorem map_smul (z : Cocycle A M N 0) (a : A) (x : M) :
    (z : Cochain A M N 0) (a • x) = a • (z : Cochain A M N 0) x := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rw [(z : Cochain A M N 0).map_smul a.2, zero_mul, koszulSign, Int.negOnePow_zero, one_smul]
  | h_add a a' ha ha' => rw [add_smul, map_add, ha, ha', add_smul]

theorem map_d (z : Cocycle A M N 0) (x : M) :
    (z : Cochain A M N 0) (d x) = d ((z : Cochain A M N 0) x) := by
  have h := congrArg (fun c : Cochain A M N 1 => c x) (z.δ_eq_zero 1)
  simp only [δ_zero_cochain_apply, Cochain.zero_apply, sub_eq_zero] at h
  exact h.symm

/-- The morphism of dg modules associated to a `0`-cocycle. -/
def homOf (z : Cocycle A M N 0) : M →ᵈᵍ[A] N where
  toFun := (z : Cochain A M N 0)
  map_add' := map_add _
  map_smul' := z.map_smul
  map_mem' hx := by simpa using (z : Cochain A M N 0).map_mem hx
  map_d' := z.map_d

@[simp]
theorem homOf_apply (z : Cocycle A M N 0) (x : M) :
    homOf z x = (z : Cochain A M N 0) x := rfl

@[simp]
theorem homOf_ofHom_eq_self (φ : M →ᵈᵍ[A] N) : homOf (ofHom φ) = φ := rfl

@[simp]
theorem ofHom_homOf_eq_self (z : Cocycle A M N 0) : ofHom (homOf z) = z := rfl

@[simp]
theorem cochain_ofHom_homOf_eq_coe (z : Cocycle A M N 0) :
    Cochain.ofHom (homOf z) = (z : Cochain A M N 0) := rfl

variable (A M N)

/-- The additive equivalence between morphisms of dg modules `M →ᵈᵍ[A] N` and `0`-cocycles of
the Hom complex. -/
@[simps]
def equivHom : (M →ᵈᵍ[A] N) ≃+ Cocycle A M N 0 where
  toFun := ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' _ _ := rfl

end Cocycle

variable {A M N}

@[simp]
theorem δ_comp_zero_cocycle {n : ℤ} (z₁ : Cochain A M N n) (z₂ : Cocycle A N P 0) (m : ℤ) :
    δ n m ((z₂ : Cochain A N P 0).comp z₁ (add_zero n)) =
      (z₂ : Cochain A N P 0).comp (δ n m z₁) (add_zero m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_comp_zero_cochain _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
theorem δ_comp_ofHom {n : ℤ} (z₁ : Cochain A M N n) (f : N →ᵈᵍ[A] P) (m : ℤ) :
    δ n m ((Cochain.ofHom f).comp z₁ (add_zero n)) =
      (Cochain.ofHom f).comp (δ n m z₁) (add_zero m) :=
  δ_comp_zero_cocycle z₁ (Cocycle.ofHom f) m

@[simp]
theorem δ_zero_cocycle_comp {n : ℤ} (z₁ : Cocycle A M N 0) (z₂ : Cochain A N P n) (m : ℤ) :
    δ n m (z₂.comp (z₁ : Cochain A M N 0) (zero_add n)) =
      (δ n m z₂).comp (z₁ : Cochain A M N 0) (zero_add m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_zero_cochain_comp _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
theorem δ_ofHom_comp {n : ℤ} (f : M →ᵈᵍ[A] N) (z : Cochain A N P n) (m : ℤ) :
    δ n m (z.comp (Cochain.ofHom f) (zero_add n)) =
      (δ n m z).comp (Cochain.ofHom f) (zero_add m) :=
  δ_zero_cocycle_comp (Cocycle.ofHom f) z m

end Cocycle

/-! ### The Hom complex -/

namespace DGModule

section HOM

variable (A : Type*) (M N : Type*) [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- The Hom complex `HOM_A(M, N) = ⨁ n, Cochain A M N n` of two dg `A`-modules. Its grading
(`DG.summand`) and differential (induced by `DG.δ`) are given by the instance
`DG.DGModule.HOM.instDGAddCommGroup`. -/
abbrev HOM : Type _ := ⨁ n : ℤ, Cochain A M N n

namespace HOM

variable {A M N}

theorem of_congr {i j : ℤ} (h : i = j) {f : Cochain A M N i} {g : Cochain A M N j}
    (hfg : ∀ x, f x = g x) :
    (DirectSum.of (fun n => Cochain A M N n) i f : HOM A M N) = DirectSum.of _ j g := by
  subst h
  rw [Cochain.ext hfg]

theorem of_units_smul (i : ℤ) (u : ℤˣ) (f : Cochain A M N i) :
    (DirectSum.of (fun n => Cochain A M N n) i (u • f) : HOM A M N) =
      u • DirectSum.of (fun n => Cochain A M N n) i f := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

end HOM

end HOM

section DGAddCommGroup

variable (A : Type*) (M N : Type*) [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

namespace HOM

/-- The differential of the Hom complex, `δ n (n + 1)` on the degree-`n` summand. -/
def dHom : HOM A M N →+ HOM A M N :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun n => Cochain A M N n) (n + 1)).comp (δ_hom A M N n (n + 1))

variable {A M N}

theorem dHom_of (n : ℤ) (z : Cochain A M N n) :
    dHom A M N (DirectSum.of _ n z) = DirectSum.of _ (n + 1) (δ n (n + 1) z) := by
  simp [dHom]

variable (A M N)

/-- The Hom complex is a dg abelian group: it is graded by its summands and its differential
is `δ`. -/
noncomputable instance instDGAddCommGroup : DGAddCommGroup (HOM A M N) where
  grading := summand fun n => Cochain A M N n
  d := dHom A M N
  d_mem' := by
    rintro n _ ⟨z, rfl⟩
    rw [dHom_of]
    exact of_mem_summand _ _
  d_d' x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n z => simp [dHom_of, δ_δ]
    | add x y hx hy => simp [hx, hy]

variable {A M N}

theorem grading_eq (n : ℤ) :
    grading (M := HOM A M N) n = summand (fun n => Cochain A M N n) n := rfl

theorem d_of (n : ℤ) (z : Cochain A M N n) :
    d (DirectSum.of (fun n => Cochain A M N n) n z : HOM A M N) =
      DirectSum.of _ (n + 1) (δ n (n + 1) z) :=
  dHom_of n z

end HOM

end DGAddCommGroup

end DGModule

end DG
