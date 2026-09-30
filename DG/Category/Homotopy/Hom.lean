import DG.Category.Module
import DG.Module.Hom

/-!
# The Hom complex of dg modules over a dg category

Let `C` be a category with dg Hom groups and `M`, `N` dg modules over `C`
(`DG.CatModule`). This file constructs the Hom complex `HOM_C(M, N)`, whose degree-`n` part
consists of the families of additive maps `M.obj X → N.obj X` of degree `n` which commute with
the action of `C` up to the Koszul sign, and whose differential is
`δ z = d ∘ z - (-1)^{|z|} z ∘ d`, objectwise. It is a port of `DG.Module.Hom` (the case of a dg
ring, i.e. of the one-object dg category), with the same names in the namespace
`DG.CatModule`, the same statements and the same signs; the single carrier of a dg module is
replaced by the family `M.obj X` and the action of the ring by the action of the morphisms of
`C`.

## Main definitions

* `DG.CatModule.Cochain M N n`: the cochains of degree `n`, families of additive maps
  `app X : M.obj X →+ N.obj X` sending `(M X)ⁱ` into `(N X)ⁱ⁺ⁿ` with
  `app Y (f • x) = (-1)^{n i} • (f • app X x)` for `f ∈ (X ⟶ Y)ⁱ`. These form an additive group.
* `DG.CatModule.Cochain.comp z₂ z₁ h`: the composition `z₂ ∘ z₁` (first `z₁`), a cochain of
  any degree `n₁₂` with `h : n₁ + n₂ = n₁₂`; `DG.CatModule.Cochain.id M`: the identity.
* `DG.CatModule.Cochain.ofHom φ`: the `0`-cochain of a morphism of dg modules `φ : M ⟶ N`.
* `DG.CatModule.δ n m z`: the differential of the Hom complex, a cochain of degree `m`, equal to
  `d ∘ z - (-1)^n • z ∘ d` if `n + 1 = m` and to `0` otherwise.
* `DG.CatModule.cocycle M N n`, `DG.CatModule.Cocycle M N n`: the cocycles of degree `n`, and
  `DG.CatModule.Cocycle.equivHom : (M ⟶ N) ≃+ Cocycle M N 0`.
* `DG.CatModule.HOM M N := ⨁ n, Cochain M N n`: the Hom complex as a dg abelian group.

## Main results

* `DG.CatModule.δ_δ`: `δ ∘ δ = 0`.
* `DG.CatModule.δ_comp`: the Leibniz rule `δ (z₂ ∘ z₁) = δ z₂ ∘ z₁ + (-1)^{n₂} • z₂ ∘ δ z₁`.
* `DG.CatModule.δ_ofHom`, `DG.CatModule.Cocycle.equivHom`: the degree-`0` cocycles are exactly
  the morphisms of dg modules.

## Conventions

As in `DG.Module.Hom`, cochains compose in the usual order (`z₂.comp z₁ h` applies `z₁` first)
and the differential agrees with Mathlib's `CochainComplex.HomComplex.δ`:
`δ z = d ∘ z + (-1)^m • z ∘ d` for `n + 1 = m` (`DG.CatModule.δ_apply'`).
-/

open CategoryTheory DirectSum

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

section Defs

/-- A cochain of degree `n` from `M` to `N` (a homogeneous element of degree `n` of the Hom
complex `HOM_C(M, N)`): a family of additive maps of degree `n` commuting with the action of
`C` up to the Koszul sign, `app Y (f • x) = (-1)^{n i} • (f • app X x)` for `f ∈ (X ⟶ Y)ⁱ`. -/
structure Cochain (M N : CatModule.{w} C) (n : ℤ) where
  /-- The component at an object. -/
  app : ∀ X : C, M.obj X →+ N.obj X
  map_mem' : ∀ {X : C} {i : ℤ} {x : M.obj X}, x ∈ grading i → app X x ∈ grading (i + n)
  /-- The Koszul-signed linearity: `app Y (f • x) = (-1)^{n i} • (f • app X x)` for
  `f ∈ (X ⟶ Y)ⁱ`. -/
  map_smul' : ∀ {X Y : C} {i : ℤ} {f : X ⟶ Y}, f ∈ grading i → ∀ x : M.obj X,
    app Y (f • x) = koszulSign (n * i) • (f • app X x)

end Defs

namespace Cochain

variable {M N P Q : CatModule.{w} C}

section Basic

variable {n : ℤ}

@[ext]
theorem ext {z₁ z₂ : Cochain M N n} (h : ∀ X x, z₁.app X x = z₂.app X x) : z₁ = z₂ := by
  obtain ⟨_, _, _⟩ := z₁
  obtain ⟨_, _, _⟩ := z₂
  congr
  funext X
  exact AddMonoidHom.ext (h X)

theorem app_injective : Function.Injective (app : Cochain M N n → ∀ X, M.obj X →+ N.obj X) :=
  fun _ _ h => ext fun X x => congrArg (fun φ => φ X x) h

theorem map_mem (z : Cochain M N n) {X : C} {i : ℤ} {x : M.obj X} (hx : x ∈ grading i) :
    z.app X x ∈ grading (i + n) :=
  z.map_mem' hx

theorem map_smul (z : Cochain M N n) {X Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i)
    (x : M.obj X) : z.app Y (f • x) = koszulSign (n * i) • (f • z.app X x) :=
  z.map_smul' hf x

theorem map_units_smul (z : Cochain M N n) {X : C} (u : ℤˣ) (x : M.obj X) :
    z.app X (u • x) = u • z.app X x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- Two cochains of possibly different (but equal) degrees agreeing pointwise are
heterogeneously equal. -/
theorem heq_of_forall {m n : ℤ} {z₁ : Cochain M N m} {z₂ : Cochain M N n} (hmn : m = n)
    (h : ∀ X x, z₁.app X x = z₂.app X x) : HEq z₁ z₂ := by
  subst hmn
  exact heq_of_eq (ext h)

end Basic

section AddCommGroup

variable {n : ℤ}

instance : Zero (Cochain M N n) :=
  ⟨{ app := fun _ => 0
     map_mem' := fun _ => zero_mem _
     map_smul' := fun _ _ => by simp }⟩

instance : Add (Cochain M N n) :=
  ⟨fun z₁ z₂ =>
    { app := fun X => z₁.app X + z₂.app X
      map_mem' := fun hx => add_mem (z₁.map_mem hx) (z₂.map_mem hx)
      map_smul' := fun hf x => by
        simp only [AddMonoidHom.add_apply, z₁.map_smul hf, z₂.map_smul hf, smul_add,
          _root_.smul_add] }⟩

instance : Neg (Cochain M N n) :=
  ⟨fun z =>
    { app := fun X => -z.app X
      map_mem' := fun hx => neg_mem (z.map_mem hx)
      map_smul' := fun hf x => by
        simp only [AddMonoidHom.neg_apply, z.map_smul hf, smul_neg,
          _root_.smul_neg] }⟩

instance : Sub (Cochain M N n) :=
  ⟨fun z₁ z₂ =>
    { app := fun X => z₁.app X - z₂.app X
      map_mem' := fun hx => sub_mem (z₁.map_mem hx) (z₂.map_mem hx)
      map_smul' := fun hf x => by
        simp only [AddMonoidHom.sub_apply, z₁.map_smul hf, z₂.map_smul hf, smul_sub,
          _root_.smul_sub] }⟩

instance : SMul ℕ (Cochain M N n) :=
  ⟨fun k z =>
    { app := fun X => k • z.app X
      map_mem' := fun hx => nsmul_mem (z.map_mem hx) k
      map_smul' := fun {X Y i f} hf x => by
        change k • z.app Y (f • x) = _ • (f • (k • z.app X x))
        rw [z.map_smul hf, show f • (k • z.app X x) = k • (f • z.app X x) from
          map_nsmul (N.act f) k _, smul_comm k] }⟩

instance : SMul ℤ (Cochain M N n) :=
  ⟨fun k z =>
    { app := fun X => k • z.app X
      map_mem' := fun hx => zsmul_mem (z.map_mem hx) k
      map_smul' := fun {X Y i f} hf x => by
        change k • z.app Y (f • x) = _ • (f • (k • z.app X x))
        rw [z.map_smul hf, smul_zsmul, smul_comm k] }⟩

@[simp] theorem zero_app (X : C) : (0 : Cochain M N n).app X = 0 := rfl
@[simp] theorem add_app (z₁ z₂ : Cochain M N n) (X : C) :
    (z₁ + z₂).app X = z₁.app X + z₂.app X := rfl
@[simp] theorem neg_app (z : Cochain M N n) (X : C) : (-z).app X = -z.app X := rfl
@[simp] theorem sub_app (z₁ z₂ : Cochain M N n) (X : C) :
    (z₁ - z₂).app X = z₁.app X - z₂.app X := rfl
@[simp] theorem nsmul_app (k : ℕ) (z : Cochain M N n) (X : C) : (k • z).app X = k • z.app X :=
  rfl
@[simp] theorem zsmul_app (k : ℤ) (z : Cochain M N n) (X : C) : (k • z).app X = k • z.app X :=
  rfl

theorem zero_apply {X : C} (x : M.obj X) : (0 : Cochain M N n).app X x = 0 := rfl
theorem add_apply (z₁ z₂ : Cochain M N n) {X : C} (x : M.obj X) :
    (z₁ + z₂).app X x = z₁.app X x + z₂.app X x := rfl
theorem neg_apply (z : Cochain M N n) {X : C} (x : M.obj X) : (-z).app X x = -z.app X x := rfl
theorem sub_apply (z₁ z₂ : Cochain M N n) {X : C} (x : M.obj X) :
    (z₁ - z₂).app X x = z₁.app X x - z₂.app X x := rfl
theorem nsmul_apply (k : ℕ) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (k • z).app X x = k • z.app X x := rfl
theorem zsmul_apply (k : ℤ) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (k • z).app X x = k • z.app X x := rfl

instance : AddCommGroup (Cochain M N n) :=
  app_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem units_smul_app (u : ℤˣ) (z : Cochain M N n) (X : C) :
    (u • z).app X = u • z.app X := rfl

theorem units_smul_apply (u : ℤˣ) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (u • z).app X x = u • z.app X x := rfl

end AddCommGroup

section Comp

/-- Composition of cochains: `z₂.comp z₁ h` is `z₂ ∘ z₁` (first `z₁`, then `z₂`). -/
def comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain N P n₂) (z₁ : Cochain M N n₁) (h : n₁ + n₂ = n₁₂) :
    Cochain M P n₁₂ where
  app X := (z₂.app X).comp (z₁.app X)
  map_mem' hx := by
    rw [← h, ← add_assoc]
    exact z₂.map_mem (z₁.map_mem hx)
  map_smul' {X Y i f} hf x := by
    change z₂.app Y (z₁.app Y _) = _ • (_ • z₂.app X (z₁.app X x))
    rw [z₁.map_smul hf, map_units_smul, z₂.map_smul hf, ← h, add_mul, koszulSign_add,
      mul_smul]

@[simp]
theorem comp_apply {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain N P n₂) (z₁ : Cochain M N n₁)
    (h : n₁ + n₂ = n₁₂) {X : C} (x : M.obj X) : (z₂.comp z₁ h).app X x = z₂.app X (z₁.app X x) :=
  rfl

/-- Associativity of the composition of cochains. -/
theorem comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
    (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂) (z₃ : Cochain P Q n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    z₃.comp (z₂.comp z₁ h₁₂) (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) =
      (z₃.comp z₂ h₂₃).comp z₁ (by rw [← h₂₃, ← h₁₂₃, add_assoc]) :=
  rfl

@[simp]
protected theorem zero_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (h : n₁ + n₂ = n₁₂) :
    (0 : Cochain N P n₂).comp z₁ h = 0 := rfl

@[simp]
protected theorem add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ z₂' : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : (z₂ + z₂').comp z₁ h = z₂.comp z₁ h + z₂'.comp z₁ h := rfl

@[simp]
protected theorem sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ z₂' : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : (z₂ - z₂').comp z₁ h = z₂.comp z₁ h - z₂'.comp z₁ h := rfl

@[simp]
protected theorem neg_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : (-z₂).comp z₁ h = -z₂.comp z₁ h := rfl

@[simp]
protected theorem zsmul_comp {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain M N n₁)
    (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) : (k • z₂).comp z₁ h = k • z₂.comp z₁ h := rfl

@[simp]
theorem units_smul_comp {n₁ n₂ n₁₂ : ℤ} (u : ℤˣ) (z₁ : Cochain M N n₁)
    (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) : (u • z₂).comp z₁ h = u • z₂.comp z₁ h := rfl

@[simp]
protected theorem comp_zero {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) :
    z₂.comp (0 : Cochain M N n₁) h = 0 := ext fun X _ => map_zero (z₂.app X)

@[simp]
protected theorem comp_add {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (z₁ + z₁') h = z₂.comp z₁ h + z₂.comp z₁' h :=
  ext fun X _ => map_add (z₂.app X) _ _

@[simp]
protected theorem comp_sub {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (z₁ - z₁') h = z₂.comp z₁ h - z₂.comp z₁' h :=
  ext fun X _ => map_sub (z₂.app X) _ _

@[simp]
protected theorem comp_neg {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (-z₁) h = -z₂.comp z₁ h :=
  ext fun X _ => map_neg (z₂.app X) _

@[simp]
protected theorem comp_zsmul {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain M N n₁)
    (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) : z₂.comp (k • z₁) h = k • z₂.comp z₁ h :=
  ext fun X _ => map_zsmul (z₂.app X) _ _

@[simp]
theorem comp_units_smul {n₁ n₂ n₁₂ : ℤ} (u : ℤˣ) (z₁ : Cochain M N n₁)
    (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) : z₂.comp (u • z₁) h = u • z₂.comp z₁ h :=
  ext fun _ _ => map_units_smul z₂ _ _

variable (M) in
/-- The identity of `M` as a cochain of degree `0`. -/
def id : Cochain M M 0 where
  app X := AddMonoidHom.id _
  map_mem' {X i x} hx := by simpa using hx
  map_smul' _ x := by simp

@[simp]
theorem id_apply {X : C} (x : M.obj X) : (Cochain.id M).app X x = x := rfl

@[simp]
protected theorem comp_id {n : ℤ} (z : Cochain M N n) :
    z.comp (Cochain.id M) (zero_add n) = z := rfl

@[simp]
protected theorem id_comp {n : ℤ} (z : Cochain M N n) :
    (Cochain.id N).comp z (add_zero n) = z := rfl

end Comp

section OfHom

/-- The `0`-cochain given by a family of additive maps preserving the degrees and commuting
with the action (not necessarily with the differentials). -/
def ofHoms (φ : ∀ X, M.obj X →+ N.obj X)
    (hφ : ∀ {X : C} {i : ℤ} {x : M.obj X}, x ∈ grading i → φ X x ∈ grading i)
    (hs : ∀ {X Y : C} (f : X ⟶ Y) (x : M.obj X), φ Y (f • x) = f • φ X x) :
    Cochain M N 0 where
  app := φ
  map_mem' hx := by simpa using hφ hx
  map_smul' _ x := by simp [hs]

@[simp]
theorem ofHoms_apply (φ : ∀ X, M.obj X →+ N.obj X)
    (hφ : ∀ {X : C} {i : ℤ} {x : M.obj X}, x ∈ grading i → φ X x ∈ grading i)
    (hs : ∀ {X Y : C} (f : X ⟶ Y) (x : M.obj X), φ Y (f • x) = f • φ X x) {X : C}
    (x : M.obj X) : (ofHoms φ hφ hs).app X x = φ X x := rfl

/-- The `0`-cochain attached to a morphism of dg modules. -/
def ofHom (φ : M ⟶ N) : Cochain M N 0 := ofHoms φ.app φ.map_mem φ.map_smul

@[simp]
theorem ofHom_apply (φ : M ⟶ N) {X : C} (x : M.obj X) : (ofHom φ).app X x = φ.app X x := rfl

variable (M N) in
@[simp]
theorem ofHom_zero : ofHom (0 : M ⟶ N) = 0 := rfl

@[simp]
theorem ofHom_add (φ₁ φ₂ : M ⟶ N) : ofHom (φ₁ + φ₂) = ofHom φ₁ + ofHom φ₂ := rfl

@[simp]
theorem ofHom_sub (φ₁ φ₂ : M ⟶ N) : ofHom (φ₁ - φ₂) = ofHom φ₁ - ofHom φ₂ := rfl

@[simp]
theorem ofHom_neg (φ : M ⟶ N) : ofHom (-φ) = -ofHom φ := rfl

theorem ofHom_zsmul (k : ℤ) (φ : M ⟶ N) : ofHom (k • φ) = k • ofHom φ := rfl

@[simp]
theorem ofHom_id : ofHom (𝟙 M) = Cochain.id M := rfl

@[simp]
theorem ofHom_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    ofHom (φ ≫ ψ) = (ofHom ψ).comp (ofHom φ) (zero_add 0) := rfl

theorem ofHom_injective : Function.Injective (ofHom : (M ⟶ N) → Cochain M N 0) :=
  fun _ _ h => hom_ext fun X x => congrArg (fun z : Cochain M N 0 => z.app X x) h

end OfHom

end Cochain

section Differential

variable {M N P : CatModule.{w} C}

open DG.CatModule.Cochain

/-- The differential of the Hom complex: for a cochain `z` of degree `n`, `δ n m z` is the
cochain `d ∘ z - (-1)^n • z ∘ d` (objectwise) of degree `m` if `n + 1 = m`, and `0` otherwise
(the convention of Mathlib's `CochainComplex.HomComplex.δ`). It commutes with the action of `C`
up to the Koszul sign by the Leibniz rules of `M` and `N`. -/
def δ (n m : ℤ) (z : Cochain M N n) : Cochain M N m :=
  if hnm : n + 1 = m then
    { app := fun X =>
        { toFun := fun x => d (z.app X x) - koszulSign n • z.app X (d x)
          map_zero' := by simp
          map_add' := fun x y => by
            simp only [map_add, _root_.smul_add]
            abel }
      map_mem' := fun {X i x} hx => by
        subst hnm
        refine sub_mem ?_ (units_smul_mem_grading _ ?_)
        · have := d_mem (z.map_mem hx)
          rwa [add_assoc] at this
        · have := z.map_mem (d_mem hx)
          rwa [add_right_comm, add_assoc] at this
      map_smul' := fun {X Y i f} hf x => by
        subst hnm
        have hdf := d_mem hf
        change d (z.app Y (f • x)) - koszulSign n • z.app Y (d (f • x)) =
          _ • (f • (d (z.app X x) - koszulSign n • z.app X (d x)))
        rw [z.map_smul hf, d_units_smul, d_smul hf, d_smul hf, map_add, map_units_smul,
          z.map_smul hf, z.map_smul hdf]
        rcases Int.units_eq_one_or (koszulSign n) with h₁ | h₁ <;>
        rcases Int.units_eq_one_or (koszulSign i) with h₂ | h₂ <;>
        rcases Int.units_eq_one_or (koszulSign (n * i)) with h₃ | h₃ <;>
        simp [add_mul, mul_add, koszulSign_add, h₁, h₂, h₃, smul_sub, smul_add] <;> abel }
  else 0

variable (n m : ℤ)

theorem δ_apply (hnm : n + 1 = m) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (δ n m z).app X x = d (z.app X x) - koszulSign n • z.app X (d x) := by
  unfold δ
  rw [dite_eq_left hnm]
  rfl

/-- The differential in the form used by Mathlib's `CochainComplex.HomComplex.δ`:
`δ z = d ∘ z + (-1)^m • z ∘ d`. -/
theorem δ_apply' (hnm : n + 1 = m) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (δ n m z).app X x = d (z.app X x) + koszulSign m • z.app X (d x) := by
  subst hnm
  rw [δ_apply n _ rfl, koszulSign, koszulSign, Int.negOnePow_succ, Units.neg_smul,
    sub_eq_add_neg]

theorem δ_shape (hnm : ¬ n + 1 = m) (z : Cochain M N n) : δ n m z = 0 := by
  unfold δ
  rw [dite_eq_right hnm]

variable (M N) in
/-- The differential of the Hom complex, as an additive map. -/
@[simps]
def δ_hom : Cochain M N n →+ Cochain M N m where
  toFun := δ n m
  map_zero' := by
    by_cases h : n + 1 = m
    · ext X x
      simp [δ_apply n m h]
    · exact δ_shape n m h _
  map_add' z₁ z₂ := by
    by_cases h : n + 1 = m
    · ext X x
      simp only [δ_apply n m h, Cochain.add_apply, d_add, _root_.smul_add]
      abel
    · simp only [δ_shape n m h, add_zero]

@[simp] theorem δ_add (z₁ z₂ : Cochain M N n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
  (δ_hom M N n m).map_add z₁ z₂

@[simp] theorem δ_sub (z₁ z₂ : Cochain M N n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
  (δ_hom M N n m).map_sub z₁ z₂

@[simp] theorem δ_zero : δ n m (0 : Cochain M N n) = 0 := (δ_hom M N n m).map_zero

@[simp] theorem δ_neg (z : Cochain M N n) : δ n m (-z) = -δ n m z :=
  (δ_hom M N n m).map_neg z

@[simp] theorem δ_zsmul (k : ℤ) (z : Cochain M N n) : δ n m (k • z) = k • δ n m z :=
  (δ_hom M N n m).map_zsmul k z

@[simp] theorem δ_units_smul (u : ℤˣ) (z : Cochain M N n) : δ n m (u • z) = u • δ n m z := by
  rw [Units.smul_def, Units.smul_def, δ_zsmul]

/-- The differential of the Hom complex squares to zero. -/
theorem δ_δ (n₀ n₁ n₂ : ℤ) (z : Cochain M N n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂; swap
  · rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁; swap
  · rw [δ_shape _ _ h₀₁, δ_zero]
  ext X x
  rw [δ_apply _ _ h₁₂, δ_apply _ _ h₀₁, δ_apply _ _ h₀₁, Cochain.zero_apply, ← h₀₁]
  simp only [koszulSign, Int.negOnePow_succ, d_sub, d_units_smul, d_d, map_zero, _root_.smul_zero,
    sub_zero, zero_sub, Units.neg_smul, sub_neg_eq_add, neg_add_cancel]

/-- The Leibniz rule for the composition of cochains: for `z₁` of degree `n₁` and `z₂` of
degree `n₂`, `δ (z₂ ∘ z₁) = δ z₂ ∘ z₁ + (-1)^{n₂} • z₂ ∘ δ z₁`. -/
theorem δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁)
    (h₂ : n₂ + 1 = m₂) :
    δ n₁₂ m₁₂ (z₂.comp z₁ h) =
      (δ n₂ m₂ z₂).comp z₁ (by rw [← h₁₂, ← h₂, ← h, add_assoc]) +
        koszulSign n₂ • z₂.comp (δ n₁ m₁ z₁)
          (by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]) := by
  ext X x
  simp only [Cochain.add_apply, units_smul_apply, Cochain.comp_apply, δ_apply _ _ h₁₂, δ_apply _ _ h₁,
    δ_apply _ _ h₂, map_sub, map_units_smul, _root_.smul_sub, smul_smul, ← h, koszulSign_add,
    mul_comm (koszulSign n₁)]
  abel

theorem δ_zero_cochain_comp {n₂ : ℤ} (z₁ : Cochain M N 0) (z₂ : Cochain N P n₂)
    (m₂ : ℤ) (h₂ : n₂ + 1 = m₂) :
    δ n₂ m₂ (z₂.comp z₁ (zero_add n₂)) =
      (δ n₂ m₂ z₂).comp z₁ (zero_add m₂) +
        koszulSign n₂ • z₂.comp (δ 0 1 z₁) (by rw [add_comm, h₂]) :=
  δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

theorem δ_comp_zero_cochain {n₁ : ℤ} (z₁ : Cochain M N n₁) (z₂ : Cochain N P 0)
    (m₁ : ℤ) (h₁ : n₁ + 1 = m₁) :
    δ n₁ m₁ (z₂.comp z₁ (add_zero n₁)) =
      (δ 0 1 z₂).comp z₁ h₁ + z₂.comp (δ n₁ m₁ z₁) (add_zero m₁) := by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), koszulSign,
    Int.negOnePow_zero, one_smul]

@[simp]
theorem δ_zero_cochain_apply (z : Cochain M N 0) {X : C} (x : M.obj X) :
    (δ 0 1 z).app X x = d (z.app X x) - z.app X (d x) := by
  rw [δ_apply 0 1 (zero_add 1), koszulSign, Int.negOnePow_zero, one_smul]

@[simp]
theorem δ_ofHom {p : ℤ} (φ : M ⟶ N) : δ 0 p (Cochain.ofHom φ) = 0 := by
  by_cases h : 0 + 1 = p
  · ext X x
    rw [δ_apply 0 p h, Cochain.zero_apply, ofHom_apply, ofHom_apply, Hom.map_d, koszulSign,
      Int.negOnePow_zero, one_smul, sub_self]
  · exact δ_shape _ _ h _

end Differential

section Cocycle

variable (M N : CatModule.{w} C) {P : CatModule.{w} C}

/-- The subgroup of cocycles in `Cochain M N n`: the kernel of `δ n (n + 1)`. -/
def cocycle (n : ℤ) : AddSubgroup (Cochain M N n) :=
  (δ_hom M N n (n + 1)).ker

/-- The type of `n`-cocycles from `M` to `N`. -/
abbrev Cocycle (n : ℤ) : Type _ := cocycle M N n

namespace Cocycle

variable {M N}

theorem mem_iff {n : ℤ} (m : ℤ) (hnm : n + 1 = m) (z : Cochain M N n) :
    z ∈ cocycle M N n ↔ δ n m z = 0 := by
  subst hnm; rfl

@[ext]
theorem ext {n : ℤ} {z₁ z₂ : Cocycle M N n} (h : (z₁ : Cochain M N n) = z₂) : z₁ = z₂ :=
  Subtype.ext h

/-- Constructor for `Cocycle M N n`, from `z : Cochain M N n`, an integer `m` with
`n + 1 = m`, and the relation `δ n m z = 0`. -/
@[simps]
def mk {n : ℤ} (z : Cochain M N n) (m : ℤ) (hnm : n + 1 = m) (h : δ n m z = 0) :
    Cocycle M N n :=
  ⟨z, (mem_iff m hnm z).2 h⟩

@[simp]
theorem δ_eq_zero {n : ℤ} (z : Cocycle M N n) (m : ℤ) : δ n m (z : Cochain M N n) = 0 := by
  by_cases h : n + 1 = m
  · exact (mem_iff m h _).1 z.2
  · exact δ_shape n m h _

/-- The `0`-cocycle associated to a morphism of dg modules. -/
@[simps!]
def ofHom (φ : M ⟶ N) : Cocycle M N 0 :=
  mk (Cochain.ofHom φ) 1 (zero_add 1) (δ_ofHom φ)

/-- A `0`-cocycle commutes with the action of all (not only homogeneous) morphisms. -/
theorem map_smul (z : Cocycle M N 0) {X Y : C} (f : X ⟶ Y) (x : M.obj X) :
    (z : Cochain M N 0).app Y (f • x) = f • (z : Cochain M N 0).app X x := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rw [(z : Cochain M N 0).map_smul f.2, zero_mul, koszulSign, Int.negOnePow_zero, one_smul]
  | h_add f f' hf hf' => rw [add_smul, map_add, hf, hf', add_smul]

theorem map_d (z : Cocycle M N 0) {X : C} (x : M.obj X) :
    (z : Cochain M N 0).app X (d x) = d ((z : Cochain M N 0).app X x) := by
  have h := congrArg (fun c : Cochain M N 1 => c.app X x) (z.δ_eq_zero 1)
  simp only [δ_zero_cochain_apply, Cochain.zero_apply, sub_eq_zero] at h
  exact h.symm

/-- The morphism of dg modules associated to a `0`-cocycle. -/
def homOf (z : Cocycle M N 0) : M ⟶ N where
  app := (z : Cochain M N 0).app
  map_mem' hx := by simpa using (z : Cochain M N 0).map_mem hx
  map_d' := z.map_d
  map_smul' := z.map_smul

@[simp]
theorem homOf_app (z : Cocycle M N 0) {X : C} (x : M.obj X) :
    (homOf z).app X x = (z : Cochain M N 0).app X x := rfl

@[simp]
theorem homOf_ofHom_eq_self (φ : M ⟶ N) : homOf (ofHom φ) = φ := rfl

@[simp]
theorem ofHom_homOf_eq_self (z : Cocycle M N 0) : ofHom (homOf z) = z := rfl

@[simp]
theorem cochain_ofHom_homOf_eq_coe (z : Cocycle M N 0) :
    Cochain.ofHom (homOf z) = (z : Cochain M N 0) := rfl

variable (M N)

/-- The additive equivalence between morphisms of dg modules `M ⟶ N` and `0`-cocycles of the
Hom complex. -/
@[simps]
def equivHom : (M ⟶ N) ≃+ Cocycle M N 0 where
  toFun := ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' _ _ := rfl

end Cocycle

variable {M N}

@[simp]
theorem δ_comp_zero_cocycle {n : ℤ} (z₁ : Cochain M N n) (z₂ : Cocycle N P 0) (m : ℤ) :
    δ n m ((z₂ : Cochain N P 0).comp z₁ (add_zero n)) =
      (z₂ : Cochain N P 0).comp (δ n m z₁) (add_zero m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_comp_zero_cochain _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
theorem δ_comp_ofHom {n : ℤ} (z₁ : Cochain M N n) (f : N ⟶ P) (m : ℤ) :
    δ n m ((Cochain.ofHom f).comp z₁ (add_zero n)) =
      (Cochain.ofHom f).comp (δ n m z₁) (add_zero m) :=
  δ_comp_zero_cocycle z₁ (Cocycle.ofHom f) m

@[simp]
theorem δ_zero_cocycle_comp {n : ℤ} (z₁ : Cocycle M N 0) (z₂ : Cochain N P n) (m : ℤ) :
    δ n m (z₂.comp (z₁ : Cochain M N 0) (zero_add n)) =
      (δ n m z₂).comp (z₁ : Cochain M N 0) (zero_add m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_zero_cochain_comp _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

@[simp]
theorem δ_ofHom_comp {n : ℤ} (f : M ⟶ N) (z : Cochain N P n) (m : ℤ) :
    δ n m (z.comp (Cochain.ofHom f) (zero_add n)) =
      (δ n m z).comp (Cochain.ofHom f) (zero_add m) :=
  δ_zero_cocycle_comp (Cocycle.ofHom f) z m

end Cocycle

/-! ### The Hom complex -/

section HOM

variable (M N : CatModule.{w} C)

/-- The Hom complex `HOM_C(M, N) = ⨁ n, Cochain M N n` of two dg modules over `C`. Its grading
(`DG.summand`) and differential (induced by `DG.CatModule.δ`) are given by the instance
`DG.CatModule.HOM.instDGAddCommGroup`. -/
abbrev HOM : Type _ := ⨁ n : ℤ, Cochain M N n

namespace HOM

variable {M N}

theorem of_congr {i j : ℤ} (h : i = j) {f : Cochain M N i} {g : Cochain M N j}
    (hfg : ∀ X x, f.app X x = g.app X x) :
    (DirectSum.of (fun n => Cochain M N n) i f : HOM M N) = DirectSum.of _ j g := by
  subst h
  rw [Cochain.ext hfg]

theorem of_units_smul (i : ℤ) (u : ℤˣ) (f : Cochain M N i) :
    (DirectSum.of (fun n => Cochain M N n) i (u • f) : HOM M N) =
      u • DirectSum.of (fun n => Cochain M N n) i f := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

variable (M N)

/-- The differential of the Hom complex, `δ n (n + 1)` on the degree-`n` summand. -/
def dHom : HOM M N →+ HOM M N :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun n => Cochain M N n) (n + 1)).comp (δ_hom M N n (n + 1))

variable {M N}

theorem dHom_of (n : ℤ) (z : Cochain M N n) :
    dHom M N (DirectSum.of _ n z) = DirectSum.of _ (n + 1) (δ n (n + 1) z) := by
  simp [dHom]

variable (M N)

/-- The Hom complex is a dg abelian group: it is graded by its summands and its differential
is `δ`. -/
noncomputable instance instDGAddCommGroup : DGAddCommGroup (HOM M N) where
  grading := summand fun n => Cochain M N n
  d := dHom M N
  d_mem' := by
    rintro n _ ⟨z, rfl⟩
    rw [dHom_of]
    exact of_mem_summand _ _
  d_d' x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n z => simp [dHom_of, δ_δ]
    | add x y hx hy => simp [hx, hy]

variable {M N}

theorem grading_eq (n : ℤ) :
    grading (M := HOM M N) n = summand (fun n => Cochain M N n) n := rfl

theorem d_of (n : ℤ) (z : Cochain M N n) :
    d (DirectSum.of (fun n => Cochain M N n) n z : HOM M N) =
      DirectSum.of _ (n + 1) (δ n (n + 1) z) :=
  dHom_of n z

end HOM

end HOM

end CatModule

end DG
