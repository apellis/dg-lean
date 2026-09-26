import DG.Graded.Basic

/-!
# Graded maps of degree `n` and the graded `Hom`

Let `M` and `N` be additive groups graded by an additive monoid `ι` (in the rest of the library
`ι = ℤ`) in Mathlib's internal style: families `ℳ : ι → σ`, `𝒩 : ι → τ` of subobjects with
`[SetLike σ M]`, `[SetLike τ N]` and the closure assumptions `AddSubgroupClass`,
`AddSubmonoidClass`, `SMulMemClass` where needed, so that both gradings by additive subgroups
and gradings by submodules are covered.

## Main definitions

* `DG.HasDegree ℳ 𝒩 n f`: an additive map `f : M →+ N` has degree `n` if it sends `ℳ i` into
  `𝒩 (i + n)` for every `i`.
* `DG.GradedHom ℳ 𝒩 n`: the additive maps of degree `n`, bundled as a structure extending
  `M →+ N`, with `FunLike` and `AddMonoidHomClass` instances. It is an additive group, and an
  `R`-module whenever `N` is an `R`-module whose grading consists of `R`-submodules (no
  `R`-linearity of the maps is assumed). Composition `g.comp f` of maps of degrees `m` and `n`
  has degree `m + n`, and `GradedHom.id ℳ` has degree `0`.
* `DG.GradedHom.lift`, `DG.GradedHom.component`, `DG.GradedHom.liftEquiv`: a graded map of
  degree `n` is the same as a family of additive maps `ℳ i →+ 𝒩 (i + n)` (when `ℳ` is a
  `DirectSum.Decomposition`); `DG.GradedHom.ext_homogeneous`: two graded maps of the same degree
  agreeing on homogeneous elements are equal.
* `DG.GradedHOM ℳ 𝒩 := ⨁ n, GradedHom ℳ 𝒩 n`: the total graded `Hom`, with its canonical
  grading `DG.GradedHOM.grading ℳ 𝒩` (a `DirectSum.Decomposition`), the evaluation
  `DG.GradedHOM.eval ℳ 𝒩 : GradedHOM ℳ 𝒩 →+ (M →+ N)` and the biadditive composition
  `DG.GradedHOM.compHom`.
* `DG.GradedEND ℳ := GradedHOM ℳ ℳ`: the graded endomorphism ring, a `Ring` (through
  `DirectSum.GRing`) which is a `GradedRing` for its canonical grading `DG.GradedEND.grading ℳ`.

## Conventions

* A map of degree `n` sends degree `i` to degree `i + n` (not `n + i`); the distinction only
  matters for a non-commutative index monoid.
* If `f` has degree `m` and `g` has degree `n` then `g.comp f` (apply `f` first) has degree
  `m + n`. Consequently the product of the graded endomorphism ring is composition in
  diagrammatic order: `f * g = g.comp f`, that is `(f * g) x = g (f x)`; see
  `DG.GradedEND.of_mul_of` and `DG.GradedEND.eval_mul`. With this convention `GradedEND ℳ` acts on
  `M` on the right, and evaluation `DG.GradedEND.evalRingHom` is a ring homomorphism to the
  multiplicative opposite of `AddMonoid.End M`.
* No Koszul signs appear here: composition of graded maps is unsigned. Signs enter only in the
  compatibility of graded maps with graded actions, treated in later files.
-/

namespace DG

open DirectSum

variable {ι M N P σ τ υ : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [SetLike σ M] [SetLike τ N] [SetLike υ P]
variable (ℳ : ι → σ) (𝒩 : ι → τ) (𝒪 : ι → υ)

/-! ### Additive maps of degree `n` -/

section HasDegree

variable [Add ι]

/-- An additive map `f : M →+ N` has degree `n` with respect to the gradings `ℳ` and `𝒩` if it
sends the homogeneous component `ℳ i` into `𝒩 (i + n)` for every `i`. -/
def HasDegree (n : ι) (f : M →+ N) : Prop :=
  ∀ i, ∀ m ∈ ℳ i, f m ∈ 𝒩 (i + n)

variable {ℳ 𝒩}

theorem HasDegree.smul {R : Type*} [Monoid R] [DistribMulAction R N] [SMulMemClass τ R N]
    {n : ι} {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (r : R) : HasDegree ℳ 𝒩 n (r • f) :=
  fun i m hm => SMulMemClass.smul_mem r (hf i m hm)

variable [AddSubgroupClass τ N]

theorem HasDegree.zero (n : ι) : HasDegree ℳ 𝒩 n 0 := fun _ _ _ => zero_mem _

theorem HasDegree.add {n : ι} {f g : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (hg : HasDegree ℳ 𝒩 n g) :
    HasDegree ℳ 𝒩 n (f + g) := fun i m hm => add_mem (hf i m hm) (hg i m hm)

theorem HasDegree.neg {n : ι} {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) : HasDegree ℳ 𝒩 n (-f) :=
  fun i m hm => neg_mem (hf i m hm)

theorem HasDegree.sub {n : ι} {f g : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (hg : HasDegree ℳ 𝒩 n g) :
    HasDegree ℳ 𝒩 n (f - g) := fun i m hm => sub_mem (hf i m hm) (hg i m hm)

theorem HasDegree.nsmul {n : ι} {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (k : ℕ) :
    HasDegree ℳ 𝒩 n (k • f) := fun i m hm => nsmul_mem (hf i m hm) k

theorem HasDegree.zsmul {n : ι} {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) (k : ℤ) :
    HasDegree ℳ 𝒩 n (k • f) := fun i m hm => zsmul_mem (hf i m hm) k

theorem HasDegree.sum {α : Type*} (s : Finset α) {n : ι} {f : α → M →+ N}
    (hf : ∀ a ∈ s, HasDegree ℳ 𝒩 n (f a)) : HasDegree ℳ 𝒩 n (∑ a ∈ s, f a) := fun i m hm => by
  rw [AddMonoidHom.finset_sum_apply]
  exact sum_mem fun a ha => hf a ha i m hm

end HasDegree

theorem HasDegree.comp [AddSemigroup ι] {ℳ : ι → σ} {𝒩 : ι → τ} {𝒪 : ι → υ} {m n : ι}
    {f : M →+ N} {g : N →+ P} (hf : HasDegree ℳ 𝒩 m f) (hg : HasDegree 𝒩 𝒪 n g) :
    HasDegree ℳ 𝒪 (m + n) (g.comp f) := fun i x hx => by
  rw [AddMonoidHom.comp_apply, ← add_assoc]
  exact hg _ _ (hf i x hx)

theorem HasDegree.id [AddZeroClass ι] (ℳ : ι → σ) : HasDegree ℳ ℳ 0 (AddMonoidHom.id M) :=
  fun i m hm => by simpa using hm

/-! ### Bundled maps of degree `n` -/

section GradedHom

variable [Add ι]

/-- The type of additive maps `M →+ N` of degree `n` with respect to the gradings `ℳ` and `𝒩`:
maps sending `ℳ i` into `𝒩 (i + n)` for every `i`. -/
structure GradedHom (n : ι) extends M →+ N where
  /-- A map of degree `n` sends degree `i` to degree `i + n`. -/
  map_mem' : ∀ i, ∀ m ∈ ℳ i, toFun m ∈ 𝒩 (i + n)

end GradedHom

namespace GradedHom

section Basic

variable [Add ι] {ℳ 𝒩} {n : ι}

instance : FunLike (GradedHom ℳ 𝒩 n) M N where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    congr 1
    exact DFunLike.coe_injective h

instance : AddMonoidHomClass (GradedHom ℳ 𝒩 n) M N where
  map_add f := f.map_add'
  map_zero f := f.map_zero'

@[ext]
theorem ext {f g : GradedHom ℳ 𝒩 n} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
theorem coe_mk (f : M →+ N) (h) : ⇑(mk (ℳ := ℳ) (𝒩 := 𝒩) (n := n) f h) = f := rfl

@[simp]
theorem coe_toAddMonoidHom (f : GradedHom ℳ 𝒩 n) : ⇑f.toAddMonoidHom = f := rfl

@[simp]
theorem toAddMonoidHom_mk (f : M →+ N) (h) :
    (mk (ℳ := ℳ) (𝒩 := 𝒩) (n := n) f h).toAddMonoidHom = f := rfl

theorem toAddMonoidHom_injective :
    Function.Injective (toAddMonoidHom : GradedHom ℳ 𝒩 n → M →+ N) := fun _ _ h =>
  ext fun x => congrArg (fun k : M →+ N => k x) h

theorem map_mem (f : GradedHom ℳ 𝒩 n) {i : ι} {m : M} (hm : m ∈ ℳ i) : f m ∈ 𝒩 (i + n) :=
  f.map_mem' i m hm

theorem hasDegree (f : GradedHom ℳ 𝒩 n) : HasDegree ℳ 𝒩 n f.toAddMonoidHom := f.map_mem'

/-- Bundle an additive map of degree `n` as a `GradedHom`. -/
def ofHasDegree {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) : GradedHom ℳ 𝒩 n := ⟨f, hf⟩

@[simp]
theorem toAddMonoidHom_ofHasDegree {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) :
    (ofHasDegree hf).toAddMonoidHom = f := rfl

@[simp]
theorem coe_ofHasDegree {f : M →+ N} (hf : HasDegree ℳ 𝒩 n f) : ⇑(ofHasDegree hf) = f := rfl

/-- The map `f : M →+ N` has degree `n` if and only if it is the underlying additive map of a
`GradedHom ℳ 𝒩 n`. -/
theorem hasDegree_iff {f : M →+ N} :
    HasDegree ℳ 𝒩 n f ↔ ∃ g : GradedHom ℳ 𝒩 n, g.toAddMonoidHom = f :=
  ⟨fun h => ⟨ofHasDegree h, rfl⟩, fun ⟨g, hg⟩ => hg ▸ g.hasDegree⟩

/-- The linear map underlying a graded map which commutes with the scalars. -/
@[simps]
def toLinearMap {R : Type*} [Semiring R] [Module R M] [Module R N] (f : GradedHom ℳ 𝒩 n)
    (hf : ∀ (r : R) (x : M), f (r • x) = r • f x) : M →ₗ[R] N where
  toFun := f
  map_add' := map_add f
  map_smul' := hf

end Basic

section Component

variable [Add ι] {ℳ 𝒩} {n : ι} [AddSubmonoidClass σ M] [AddSubmonoidClass τ N]

/-- The homogeneous component of a graded map of degree `n`: its restriction to `ℳ i`, with
values in `𝒩 (i + n)`. -/
def component (f : GradedHom ℳ 𝒩 n) (i : ι) : ℳ i →+ 𝒩 (i + n) where
  toFun m := ⟨f m, f.map_mem m.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp]
theorem coe_component_apply (f : GradedHom ℳ 𝒩 n) (i : ι) (m : ℳ i) :
    (f.component i m : N) = f m := rfl

end Component

/-! #### The additive group structure -/

section AddCommGroup

variable [Add ι] {ℳ 𝒩} {n : ι} [AddSubgroupClass τ N]

instance : Zero (GradedHom ℳ 𝒩 n) := ⟨ofHasDegree (HasDegree.zero n)⟩
instance : Add (GradedHom ℳ 𝒩 n) := ⟨fun f g => ofHasDegree (f.hasDegree.add g.hasDegree)⟩
instance : Neg (GradedHom ℳ 𝒩 n) := ⟨fun f => ofHasDegree f.hasDegree.neg⟩
instance : Sub (GradedHom ℳ 𝒩 n) := ⟨fun f g => ofHasDegree (f.hasDegree.sub g.hasDegree)⟩
instance : SMul ℕ (GradedHom ℳ 𝒩 n) := ⟨fun k f => ofHasDegree (f.hasDegree.nsmul k)⟩
instance : SMul ℤ (GradedHom ℳ 𝒩 n) := ⟨fun k f => ofHasDegree (f.hasDegree.zsmul k)⟩

@[simp] theorem toAddMonoidHom_zero : (0 : GradedHom ℳ 𝒩 n).toAddMonoidHom = 0 := rfl
@[simp] theorem toAddMonoidHom_add (f g : GradedHom ℳ 𝒩 n) :
    (f + g).toAddMonoidHom = f.toAddMonoidHom + g.toAddMonoidHom := rfl
@[simp] theorem toAddMonoidHom_neg (f : GradedHom ℳ 𝒩 n) :
    (-f).toAddMonoidHom = -f.toAddMonoidHom := rfl
@[simp] theorem toAddMonoidHom_sub (f g : GradedHom ℳ 𝒩 n) :
    (f - g).toAddMonoidHom = f.toAddMonoidHom - g.toAddMonoidHom := rfl
@[simp] theorem toAddMonoidHom_nsmul (k : ℕ) (f : GradedHom ℳ 𝒩 n) :
    (k • f).toAddMonoidHom = k • f.toAddMonoidHom := rfl
@[simp] theorem toAddMonoidHom_zsmul (k : ℤ) (f : GradedHom ℳ 𝒩 n) :
    (k • f).toAddMonoidHom = k • f.toAddMonoidHom := rfl

@[simp] theorem coe_zero : ⇑(0 : GradedHom ℳ 𝒩 n) = 0 := rfl
@[simp] theorem coe_add (f g : GradedHom ℳ 𝒩 n) : ⇑(f + g) = ⇑f + ⇑g := rfl
@[simp] theorem coe_neg (f : GradedHom ℳ 𝒩 n) : ⇑(-f) = -⇑f := rfl
@[simp] theorem coe_sub (f g : GradedHom ℳ 𝒩 n) : ⇑(f - g) = ⇑f - ⇑g := rfl
@[simp] theorem coe_nsmul (k : ℕ) (f : GradedHom ℳ 𝒩 n) : ⇑(k • f) = k • ⇑f := rfl
@[simp] theorem coe_zsmul (k : ℤ) (f : GradedHom ℳ 𝒩 n) : ⇑(k • f) = k • ⇑f := rfl

theorem zero_apply (x : M) : (0 : GradedHom ℳ 𝒩 n) x = 0 := rfl
theorem add_apply (f g : GradedHom ℳ 𝒩 n) (x : M) : (f + g) x = f x + g x := rfl
theorem neg_apply (f : GradedHom ℳ 𝒩 n) (x : M) : (-f) x = -f x := rfl
theorem sub_apply (f g : GradedHom ℳ 𝒩 n) (x : M) : (f - g) x = f x - g x := rfl
theorem nsmul_apply (k : ℕ) (f : GradedHom ℳ 𝒩 n) (x : M) : (k • f) x = k • f x := rfl
theorem zsmul_apply (k : ℤ) (f : GradedHom ℳ 𝒩 n) (x : M) : (k • f) x = k • f x := rfl

instance : AddCommGroup (GradedHom ℳ 𝒩 n) :=
  toAddMonoidHom_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

variable (ℳ 𝒩 n) in
/-- The underlying additive map, as an additive map `GradedHom ℳ 𝒩 n →+ (M →+ N)`. -/
@[simps]
def coeAddMonoidHom : GradedHom ℳ 𝒩 n →+ (M →+ N) where
  toFun := toAddMonoidHom
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeAddMonoidHom_injective : Function.Injective (coeAddMonoidHom ℳ 𝒩 n) :=
  toAddMonoidHom_injective

end AddCommGroup

/-! #### Scalar multiplication -/

section SMul

variable [Add ι] {ℳ 𝒩} {n : ι}
variable {R : Type*} [Monoid R] [DistribMulAction R N] [SMulMemClass τ R N]

instance : SMul R (GradedHom ℳ 𝒩 n) := ⟨fun r f => ofHasDegree (f.hasDegree.smul r)⟩

@[simp] theorem toAddMonoidHom_smul (r : R) (f : GradedHom ℳ 𝒩 n) :
    (r • f).toAddMonoidHom = r • f.toAddMonoidHom := rfl
@[simp] theorem coe_smul (r : R) (f : GradedHom ℳ 𝒩 n) : ⇑(r • f) = r • ⇑f := rfl
theorem smul_apply (r : R) (f : GradedHom ℳ 𝒩 n) (x : M) : (r • f) x = r • f x := rfl

variable [AddSubgroupClass τ N]

instance : DistribMulAction R (GradedHom ℳ 𝒩 n) :=
  toAddMonoidHom_injective.distribMulAction (coeAddMonoidHom ℳ 𝒩 n) fun _ _ => rfl

end SMul

section Module

variable [Add ι] {ℳ 𝒩} {n : ι} [AddSubgroupClass τ N]
variable {R : Type*} [Semiring R] [Module R N] [SMulMemClass τ R N]

/-- Graded maps of degree `n` into an `R`-module `N` whose grading consists of `R`-submodules form
an `R`-module. (No `R`-linearity of the maps is assumed.) -/
instance : Module R (GradedHom ℳ 𝒩 n) :=
  toAddMonoidHom_injective.module R (coeAddMonoidHom ℳ 𝒩 n) fun _ _ => rfl

end Module

/-! #### Composition and identity -/

section Comp

variable [AddSemigroup ι] {ℳ 𝒩 𝒪}

/-- Composition of graded maps: if `f` has degree `m` and `g` has degree `n` then `g.comp f` has
degree `m + n`. -/
def comp {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) : GradedHom ℳ 𝒪 (m + n) :=
  ofHasDegree (f.hasDegree.comp g.hasDegree)

@[simp] theorem toAddMonoidHom_comp {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    (g.comp f).toAddMonoidHom = g.toAddMonoidHom.comp f.toAddMonoidHom := rfl
@[simp] theorem coe_comp {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    ⇑(g.comp f) = g ∘ f := rfl
theorem comp_apply {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) (x : M) :
    g.comp f x = g (f x) := rfl

/-- Graded maps of possibly different degrees are heterogeneously equal as soon as their degrees
agree and they agree pointwise. -/
theorem heq_of_forall {m n : ι} {f : GradedHom ℳ 𝒩 m} {g : GradedHom ℳ 𝒩 n} (hmn : m = n)
    (h : ∀ x, f x = g x) : HEq f g := by
  subst hmn
  exact heq_of_eq (ext h)

theorem comp_assoc {Q ω : Type*} [AddCommGroup Q] [SetLike ω Q] {𝒬 : ι → ω} {m n p : ι}
    (h : GradedHom 𝒪 𝒬 p) (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    HEq ((h.comp g).comp f) (h.comp (g.comp f)) :=
  heq_of_forall (add_assoc m n p).symm fun _ => rfl

theorem toAddMonoidHom_comp_assoc {Q ω : Type*} [AddCommGroup Q] [SetLike ω Q] {𝒬 : ι → ω}
    {m n p : ι} (h : GradedHom 𝒪 𝒬 p) (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    ((h.comp g).comp f).toAddMonoidHom = (h.comp (g.comp f)).toAddMonoidHom := rfl

variable [AddSubgroupClass υ P]

@[simp] theorem zero_comp {m n : ι} (f : GradedHom ℳ 𝒩 m) :
    (0 : GradedHom 𝒩 𝒪 n).comp f = 0 := rfl
theorem add_comp {m n : ι} (g₁ g₂ : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := rfl
theorem neg_comp {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    (-g).comp f = -g.comp f := rfl
theorem sub_comp {m n : ι} (g₁ g₂ : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    (g₁ - g₂).comp f = g₁.comp f - g₂.comp f := rfl

variable [AddSubgroupClass τ N]

@[simp] theorem comp_zero {m n : ι} (g : GradedHom 𝒩 𝒪 n) :
    g.comp (0 : GradedHom ℳ 𝒩 m) = 0 := ext fun _ => map_zero g
theorem comp_add {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f₁ f₂ : GradedHom ℳ 𝒩 m) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := ext fun _ => map_add g _ _
theorem comp_neg {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    g.comp (-f) = -g.comp f := ext fun _ => map_neg g _
theorem comp_sub {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f₁ f₂ : GradedHom ℳ 𝒩 m) :
    g.comp (f₁ - f₂) = g.comp f₁ - g.comp f₂ := ext fun _ => map_sub g _ _

/-- Composition as a biadditive map on the homogeneous pieces `GradedHom`. -/
@[simps]
def compAddMonoidHom (m n : ι) :
    GradedHom 𝒩 𝒪 n →+ GradedHom ℳ 𝒩 m →+ GradedHom ℳ 𝒪 (m + n) where
  toFun g := AddMonoidHom.mk' g.comp (comp_add g)
  map_zero' := AddMonoidHom.ext fun f => zero_comp f
  map_add' g₁ g₂ := AddMonoidHom.ext fun f => add_comp g₁ g₂ f

end Comp

section Id

variable [AddZeroClass ι]

/-- The identity as a graded map of degree `0`. -/
def id : GradedHom ℳ ℳ 0 := ofHasDegree (HasDegree.id ℳ)

@[simp] theorem toAddMonoidHom_id : (id ℳ).toAddMonoidHom = AddMonoidHom.id M := rfl
@[simp] theorem coe_id : ⇑(id ℳ) = _root_.id := rfl
theorem id_apply (x : M) : id ℳ x = x := rfl

end Id

section Monoid

variable [AddMonoid ι] {ℳ 𝒩}

theorem comp_id {m : ι} (f : GradedHom ℳ 𝒩 m) : HEq (f.comp (id ℳ)) f :=
  heq_of_forall (zero_add m) fun _ => rfl

theorem id_comp {m : ι} (f : GradedHom ℳ 𝒩 m) : HEq ((id 𝒩).comp f) f :=
  heq_of_forall (add_zero m) fun _ => rfl

@[simp] theorem toAddMonoidHom_comp_id {m : ι} (f : GradedHom ℳ 𝒩 m) :
    (f.comp (id ℳ)).toAddMonoidHom = f.toAddMonoidHom := rfl
@[simp] theorem toAddMonoidHom_id_comp {m : ι} (f : GradedHom ℳ 𝒩 m) :
    ((id 𝒩).comp f).toAddMonoidHom = f.toAddMonoidHom := rfl

end Monoid

/-! #### Graded maps out of a decomposed object -/

section Decomposition

variable [Add ι] [DecidableEq ι] {ℳ 𝒩} {n : ι} [AddSubmonoidClass σ M] [Decomposition ℳ]

/-- Two graded maps of the same degree agreeing on homogeneous elements are equal. -/
theorem ext_homogeneous {f g : GradedHom ℳ 𝒩 n} (h : ∀ (i : ι) (m : ℳ i), f m = g m) : f = g :=
  toAddMonoidHom_injective (decompose_addHom_ext ℳ h)

section Lift

variable [AddSubmonoidClass τ N]

/-- The graded map of degree `n` extending a family of additive maps `ℳ i →+ 𝒩 (i + n)` on the
homogeneous components. -/
def lift (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) : GradedHom ℳ 𝒩 n :=
  ofHasDegree (f := liftHomogeneous ℳ fun i => (AddSubmonoidClass.subtype _).comp (φ i))
    fun i m hm => by
      rw [liftHomogeneous_of_mem ℳ _ hm]
      exact (φ i ⟨m, hm⟩).2

@[simp]
theorem lift_coe (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) {i : ι} (m : ℳ i) : lift φ m = φ i m :=
  liftHomogeneous_coe ℳ _ m

theorem lift_of_mem (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) {i : ι} {m : M} (hm : m ∈ ℳ i) :
    lift φ m = φ i ⟨m, hm⟩ :=
  lift_coe φ ⟨m, hm⟩

theorem lift_apply (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) (m : M) :
    lift φ m = DirectSum.toAddMonoid (fun i => (AddSubmonoidClass.subtype _).comp (φ i))
      (decompose ℳ m) := rfl

@[simp]
theorem component_lift (φ : ∀ i, ℳ i →+ 𝒩 (i + n)) (i : ι) : (lift φ).component i = φ i :=
  AddMonoidHom.ext fun m => Subtype.ext (lift_coe φ m)

@[simp]
theorem lift_component (f : GradedHom ℳ 𝒩 n) : lift f.component = f :=
  ext_homogeneous fun _ _ => lift_coe _ _

end Lift

section LiftEquiv

variable (ℳ 𝒩 n) [AddSubgroupClass τ N]

/-- Graded maps of degree `n` are the same as families of additive maps `ℳ i →+ 𝒩 (i + n)`. -/
def liftEquiv : (∀ i, ℳ i →+ 𝒩 (i + n)) ≃+ GradedHom ℳ 𝒩 n where
  toFun := lift
  invFun := component
  left_inv φ := funext (component_lift φ)
  right_inv := lift_component
  map_add' φ ψ := ext_homogeneous fun _ _ => by simp

end LiftEquiv

end Decomposition

end GradedHom

/-! ### The total graded `Hom` -/

section GradedHOM

variable [Add ι] [DecidableEq ι] [AddSubgroupClass τ N]

/-- The total graded `Hom` from `ℳ` to `𝒩`: the direct sum over all degrees `n` of the maps of
degree `n`. -/
abbrev GradedHOM : Type _ := ⨁ n : ι, GradedHom ℳ 𝒩 n

namespace GradedHOM

/-- The canonical grading of the total graded `Hom`: the degree-`n` component is the image of
`GradedHom ℳ 𝒩 n`. -/
abbrev grading : ι → AddSubgroup (GradedHOM ℳ 𝒩) := summand fun n => GradedHom ℳ 𝒩 n

noncomputable example : Decomposition (grading ℳ 𝒩) := inferInstance

/-- Evaluation of the total graded `Hom` on `M`: the additive map `GradedHOM ℳ 𝒩 →+ (M →+ N)`
which is the underlying additive map on each summand. -/
def eval : GradedHOM ℳ 𝒩 →+ (M →+ N) :=
  DirectSum.toAddMonoid fun n => GradedHom.coeAddMonoidHom ℳ 𝒩 n

@[simp]
theorem eval_of (n : ι) (f : GradedHom ℳ 𝒩 n) :
    eval ℳ 𝒩 (DirectSum.of (fun n => GradedHom ℳ 𝒩 n) n f) = f.toAddMonoidHom :=
  DirectSum.toAddMonoid_of _ _ _

theorem eval_of_apply (n : ι) (f : GradedHom ℳ 𝒩 n) (x : M) :
    eval ℳ 𝒩 (DirectSum.of (fun n => GradedHom ℳ 𝒩 n) n f) x = f x := by simp

end GradedHOM

end GradedHOM

section GradedHOMComp

variable [AddSemigroup ι] [DecidableEq ι] [AddSubgroupClass τ N] [AddSubgroupClass υ P]
variable {ℳ 𝒩 𝒪}

namespace GradedHOM

/-- Composition on the total graded `Hom`, as a biadditive map: on the summands it is the
composition `GradedHom.comp`, of degree `m + n` on maps of degrees `m` and `n`. -/
def compHom : GradedHOM 𝒩 𝒪 →+ GradedHOM ℳ 𝒩 →+ GradedHOM ℳ 𝒪 :=
  DirectSum.toAddMonoid fun n =>
    AddMonoidHom.mk'
      (fun g => DirectSum.toAddMonoid fun m =>
        (DirectSum.of (fun k => GradedHom ℳ 𝒪 k) (m + n)).comp (GradedHom.compAddMonoidHom m n g))
      fun g₁ g₂ => DirectSum.addHom_ext fun m f => by simp [GradedHom.add_comp]

@[simp]
theorem compHom_of_of {m n : ι} (g : GradedHom 𝒩 𝒪 n) (f : GradedHom ℳ 𝒩 m) :
    compHom (DirectSum.of (fun n => GradedHom 𝒩 𝒪 n) n g)
        (DirectSum.of (fun m => GradedHom ℳ 𝒩 m) m f) =
      DirectSum.of (fun k => GradedHom ℳ 𝒪 k) (m + n) (g.comp f) := by
  simp [compHom]

/-- Evaluation is compatible with composition: `eval (compHom g f) = (eval g).comp (eval f)`. -/
theorem eval_compHom (g : GradedHOM 𝒩 𝒪) (f : GradedHOM ℳ 𝒩) :
    eval ℳ 𝒪 (compHom g f) = (eval 𝒩 𝒪 g).comp (eval ℳ 𝒩 f) := by
  induction g using DirectSum.induction_on with
  | zero => simp
  | of n g =>
    induction f using DirectSum.induction_on with
    | zero => simp
    | of m f => simp
    | add f₁ f₂ h₁ h₂ => simp [map_add, h₁, h₂, AddMonoidHom.comp_add]
  | add g₁ g₂ h₁ h₂ => simp [map_add, h₁, h₂, AddMonoidHom.add_comp]

theorem eval_compHom_apply (g : GradedHOM 𝒩 𝒪) (f : GradedHOM ℳ 𝒩) (x : M) :
    eval ℳ 𝒪 (compHom g f) x = eval 𝒩 𝒪 g (eval ℳ 𝒩 f x) := by
  rw [eval_compHom]; rfl

end GradedHOM

end GradedHOMComp

/-! ### The graded endomorphism ring -/

section GradedEND

namespace GradedEND

variable [AddMonoid ι]

instance instGOne : GradedMonoid.GOne fun n => GradedHom ℳ ℳ n := ⟨GradedHom.id ℳ⟩

/-- The graded multiplication on `GradedEND ℳ` is composition in diagrammatic order: for `f` of
degree `m` and `g` of degree `n`, `f * g = g.comp f` has degree `m + n`. -/
instance instGMul : GradedMonoid.GMul fun n => GradedHom ℳ ℳ n := ⟨fun f g => g.comp f⟩

theorem gOne_eq : (GradedMonoid.GOne.one : GradedHom ℳ ℳ 0) = GradedHom.id ℳ := rfl

theorem gMul_eq {m n : ι} (f : GradedHom ℳ ℳ m) (g : GradedHom ℳ ℳ n) :
    (GradedMonoid.GMul.mul f g : GradedHom ℳ ℳ (m + n)) = g.comp f := rfl

end GradedEND

variable [AddMonoid ι] [DecidableEq ι] [AddSubgroupClass σ M]

/-- The graded endomorphism ring of a graded additive group: the total graded `Hom` from `ℳ` to
itself. Its product is composition in diagrammatic order, `f * g = g.comp f`. -/
abbrev GradedEND : Type _ := GradedHOM ℳ ℳ

namespace GradedEND

instance instGRing : DirectSum.GRing fun n => GradedHom ℳ ℳ n where
  mul_zero _ := GradedHom.zero_comp _
  zero_mul _ := GradedHom.comp_zero _
  mul_add _ _ _ := GradedHom.add_comp _ _ _
  add_mul _ _ _ := GradedHom.comp_add _ _ _
  one_mul _ := Sigma.ext (zero_add _) (GradedHom.comp_id _)
  mul_one _ := Sigma.ext (add_zero _) (GradedHom.id_comp _)
  mul_assoc _ _ _ := Sigma.ext (add_assoc _ _ _) (GradedHom.comp_assoc _ _ _).symm
  natCast k := k • GradedHom.id ℳ
  natCast_zero := zero_nsmul _
  natCast_succ k := succ_nsmul _ k
  intCast k := k • GradedHom.id ℳ
  intCast_ofNat k := natCast_zsmul _ k
  intCast_negSucc_ofNat k := negSucc_zsmul _ k

noncomputable example : Ring (GradedEND ℳ) := inferInstance

/-- The canonical grading of the graded endomorphism ring. -/
abbrev grading : ι → AddSubgroup (GradedEND ℳ) := GradedHOM.grading ℳ ℳ

/-- The graded endomorphism ring is a graded ring with respect to its canonical grading. -/
noncomputable instance instGradedRing : GradedRing (grading ℳ) := inferInstance

variable {ℳ}

theorem one_def :
    (1 : GradedEND ℳ) = DirectSum.of (fun n => GradedHom ℳ ℳ n) 0 (GradedHom.id ℳ) :=
  rfl

theorem of_mul_of {m n : ι} (f : GradedHom ℳ ℳ m) (g : GradedHom ℳ ℳ n) :
    DirectSum.of (fun n => GradedHom ℳ ℳ n) m f * DirectSum.of (fun n => GradedHom ℳ ℳ n) n g =
      DirectSum.of (fun n => GradedHom ℳ ℳ n) (m + n) (g.comp f) :=
  DirectSum.of_mul_of f g

/-- The product on `GradedEND ℳ` is the composition `GradedHOM.compHom` in diagrammatic order. -/
theorem mul_eq_compHom (f g : GradedEND ℳ) : f * g = GradedHOM.compHom g f := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of m f =>
    induction g using DirectSum.induction_on with
    | zero => simp
    | of n g => simp [of_mul_of]
    | add g₁ g₂ h₁ h₂ => simp [mul_add, h₁, h₂]
  | add f₁ f₂ h₁ h₂ => simp [add_mul, h₁, h₂]

@[simp]
theorem eval_one : GradedHOM.eval ℳ ℳ (1 : GradedEND ℳ) = AddMonoidHom.id M := by
  simp [one_def]

/-- Evaluation is anti-multiplicative: `eval (f * g) = (eval g).comp (eval f)`. -/
theorem eval_mul (f g : GradedEND ℳ) :
    GradedHOM.eval ℳ ℳ (f * g) = (GradedHOM.eval ℳ ℳ g).comp (GradedHOM.eval ℳ ℳ f) := by
  rw [mul_eq_compHom, GradedHOM.eval_compHom]

theorem eval_mul_apply (f g : GradedEND ℳ) (x : M) :
    GradedHOM.eval ℳ ℳ (f * g) x = GradedHOM.eval ℳ ℳ g (GradedHOM.eval ℳ ℳ f x) := by
  rw [eval_mul]; rfl

variable (ℳ) in
/-- Evaluation as a ring homomorphism from `GradedEND ℳ` to the multiplicative opposite of the
endomorphism ring `AddMonoid.End M`: the graded endomorphism ring acts on `M` on the right. -/
def evalRingHom : GradedEND ℳ →+* (AddMonoid.End M)ᵐᵒᵖ where
  toFun f := MulOpposite.op (GradedHOM.eval ℳ ℳ f)
  map_one' := by simp; rfl
  map_mul' f g := by
    rw [eval_mul, ← MulOpposite.op_mul]
    rfl
  map_zero' := by simp
  map_add' f g := by simp

@[simp]
theorem evalRingHom_apply (f : GradedEND ℳ) :
    evalRingHom ℳ f = MulOpposite.op (GradedHOM.eval ℳ ℳ f) := rfl

end GradedEND

end GradedEND

end DG
