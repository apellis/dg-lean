import DG.Module.Prod
import DG.Module.Shift

/-!
# Mapping cones of morphisms of dg modules

The mapping cone of a morphism `f : M →ᵈᵍ[A] N` is the dg module
`Cone f = M⟦1⟧ ⊕ N` (as a graded `A`-module, the product `Shift 1 M × N` with the
componentwise action, where the action on `M⟦1⟧` is the twisted one) with the differential

  `d (x, y) = (d_{M⟦1⟧} x, f x + d_N y) = (-d_M x, f x + d_N y)`,

i.e. the matrix `(-d_M, 0; f, d_N)` with respect to the decomposition `M⟦1⟧ ⊕ N`. This is
the differential of Mathlib's `CochainComplex.mappingCone` (whose degree-`i` piece is
`F.X (i + 1) ⊞ G.X i`), so the order of the factors follows Mathlib. It is also the mapping
cone `N ⊕ M[1]` with `d = (d_N, f; 0, -d_M)` of `docs/CONVENTIONS.md`, with the two summands
written in the other order.

* `DG.Cone f`: the mapping cone, a `def` (a type synonym for `Shift 1 M × N`) with explicit
  `AddCommGroup`, `Module A`, `DGAddCommGroup` and `DGModule A` instances.
* `DG.Cone.inr f : N →ᵈᵍ[A] Cone f` and `DG.Cone.fst f : Cone f →ᵈᵍ[A] Shift 1 M`, the
  morphisms of the standard triangle `M → N → Cone f → M⟦1⟧`, with `fst ∘ inr = 0`.
  (Mathlib's standard triangle `CochainComplex.mappingCone.triangle` uses `-fst` as its third
  morphism.)
* `DG.Cone.inl f : Shift 1 M →ₗ[A] Cone f` and `DG.Cone.snd f : Cone f →ₗ[A] N`, the other
  two structure maps: `A`-linear, graded of degree `0`, but not chain maps. They satisfy
  `snd ∘ inl = 0`, `snd ∘ inr = id`, `fst ∘ inl = id`, `inl ∘ fst + inr ∘ snd = id`, and
  `d ∘ inl - inl ∘ d = inr ∘ f` (`DG.Cone.d_inl`), expressing that `inl` is a chain map up to
  the homotopy `f`.
* `DG.Cone.contraction M`: the degree `-1` map `h (x, y) = (y, 0)` on the cone of the identity
  of `M`, with `d ∘ h + h ∘ d = id`: the cone of the identity is contractible.
* `DG.Cone.map`: functoriality, a commutative square `g ∘ f = f' ∘ e` induces
  `Cone f →ᵈᵍ[A] Cone f'`.
-/

namespace DG

variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- The mapping cone of a morphism `f : M →ᵈᵍ[A] N` of dg modules: the graded `A`-module
`M⟦1⟧ × N` with the differential `d (x, y) = (-d x, f x + d y)`. -/
def Cone (_f : M →ᵈᵍ[A] N) : Type _ := Shift 1 M × N

namespace Cone

open Shift

variable (f : M →ᵈᵍ[A] N)

instance : AddCommGroup (Cone f) := inferInstanceAs (AddCommGroup (Shift 1 M × N))

instance : Module A (Cone f) := inferInstanceAs (Module A (Shift 1 M × N))

/-- The inclusion of `M⟦1⟧` into the cone, `x ↦ (x, 0)`: `A`-linear and graded of degree `0`,
but not a chain map (see `Cone.d_inl`). -/
def inl : Shift 1 M →ₗ[A] Cone f := LinearMap.inl A (Shift 1 M) N

/-- The projection of the cone onto `N`, `(x, y) ↦ y`: `A`-linear and graded of degree `0`,
but not a chain map (see `Cone.snd_d`). -/
def snd : Cone f →ₗ[A] N := LinearMap.snd A (Shift 1 M) N

/-- The inclusion of `N` into the cone, `y ↦ (0, y)`, as an `A`-linear map; see `Cone.inr` for
the morphism of dg modules. -/
def inrLinear : N →ₗ[A] Cone f := LinearMap.inr A (Shift 1 M) N

/-- The projection of the cone onto `M⟦1⟧`, `(x, y) ↦ x`, as an `A`-linear map; see `Cone.fst`
for the morphism of dg modules. -/
def fstLinear : Cone f →ₗ[A] Shift 1 M := LinearMap.fst A (Shift 1 M) N

/-- The differential of the mapping cone, `d (x, y) = (d_{M⟦1⟧} x, f x + d y)`, as an additive
map. -/
def dAddMonoidHom : Cone f →+ Cone f :=
  ((d : Shift 1 M →+ Shift 1 M).comp (AddMonoidHom.fst (Shift 1 M) N)).prod
    ((f : M →+ N).comp ((unmk 1).toAddMonoidHom.comp (AddMonoidHom.fst (Shift 1 M) N)) +
      (d : N →+ N).comp (AddMonoidHom.snd (Shift 1 M) N))

instance : DGAddCommGroup (Cone f) where
  grading := grading (M := Shift 1 M × N)
  decomposition := DGAddCommGroup.decomposition (M := Shift 1 M × N)
  d := dAddMonoidHom f
  d_mem' {k p} hp := by
    have hp' : fstLinear f p ∈ grading k ∧ snd f p ∈ grading k := hp
    exact ⟨d_mem hp'.1, add_mem (f.map_mem (unmk_mem_grading hp'.1)) (d_mem hp'.2)⟩
  d_d' p := by
    apply Prod.ext
    · exact d_d _
    · change f (unmk 1 (d (fstLinear f p))) + d (f (unmk 1 (fstLinear f p)) + d (snd f p)) = 0
      rw [unmk_d, koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul, map_neg, d_add, d_d,
        add_zero, f.map_d, neg_add_cancel]

/-- The inclusion of `N` into the cone, `y ↦ (0, y)`, as a morphism of dg modules. -/
def inr : N →ᵈᵍ[A] Cone f where
  __ := inrLinear f
  map_mem' hy := ⟨zero_mem _, hy⟩
  map_d' y := by
    apply Prod.ext
    · exact (d_zero (M := Shift 1 M)).symm
    · change d y = f (unmk 1 0) + d y
      rw [unmk_zero, map_zero, zero_add]

/-- The projection of the cone onto `M⟦1⟧`, `(x, y) ↦ x`, as a morphism of dg modules. -/
def fst : Cone f →ᵈᵍ[A] Shift 1 M where
  __ := fstLinear f
  map_mem' hp := hp.1
  map_d' _ := rfl

/-! ### Evaluation lemmas -/

variable {f}

@[simp] theorem fst_inl (x : Shift 1 M) : fst f (inl f x) = x := rfl
@[simp] theorem snd_inl (x : Shift 1 M) : snd f (inl f x) = 0 := rfl
@[simp] theorem fst_inr (y : N) : fst f (inr f y) = 0 := rfl
@[simp] theorem snd_inr (y : N) : snd f (inr f y) = y := rfl

theorem fstLinear_apply (p : Cone f) : fstLinear f p = fst f p := rfl
theorem inrLinear_apply (y : N) : inrLinear f y = inr f y := rfl

@[ext]
theorem ext {p q : Cone f} (h₁ : fst f p = fst f q) (h₂ : snd f p = snd f q) : p = q :=
  Prod.ext h₁ h₂

theorem inl_fst_add_inr_snd (p : Cone f) : inl f (fst f p) + inr f (snd f p) = p :=
  ext (add_zero _) (zero_add _)

variable (f) in
@[simp]
theorem fst_comp_inr : (fst f).comp (inr f) = 0 := rfl

theorem mem_grading_iff {k : ℤ} {p : Cone f} :
    p ∈ grading k ↔ fst f p ∈ grading k ∧ snd f p ∈ grading k :=
  Iff.rfl

theorem inl_mem {k : ℤ} {x : Shift 1 M} (hx : x ∈ grading k) : inl f x ∈ grading k :=
  ⟨hx, zero_mem _⟩

theorem snd_mem {k : ℤ} {p : Cone f} (hp : p ∈ grading k) : snd f p ∈ grading k :=
  hp.2

/-- The first component of the differential of the cone: `fst` is a chain map. -/
theorem fst_d (p : Cone f) : fst f (d p) = d (fst f p) := rfl

/-- The second component of the differential of the cone. -/
theorem snd_d (p : Cone f) : snd f (d p) = f (unmk 1 (fst f p)) + d (snd f p) := rfl

theorem d_inl (x : Shift 1 M) : d (inl f x) = inl f (d x) + inr f (f (unmk 1 x)) :=
  ext (by simp [fst_d]) (by simp [snd_d])

/-- `inl` is a chain map up to the homotopy `f`: `d ∘ inl - inl ∘ d = inr ∘ f`. -/
theorem d_inl_sub_inl_d (x : Shift 1 M) : d (inl f x) - inl f (d x) = inr f (f (unmk 1 x)) := by
  rw [d_inl, add_sub_cancel_left]

theorem d_inl_add_inr (x : Shift 1 M) (y : N) :
    d (inl f x + inr f y) = inl f (d x) + inr f (f (unmk 1 x) + d y) :=
  ext (by simp [fst_d]) (by simp [snd_d])

/-! ### The dg module structure -/

section DGModule

variable [DGModule A M] [DGModule A N]

instance : DGModule A (Cone f) where
  smul_mem {i j} a p ha hp :=
    ⟨smul_mem_grading ha hp.1, smul_mem_grading ha hp.2⟩
  d_smul' {i} a ha p := by
    refine ext ?_ ?_
    · simp only [fst_d, map_add, map_smul, Units.smul_def, map_zsmul, d_smul ha]
    · simp only [snd_d, map_add, map_smul, Units.smul_def, map_zsmul, unmk_smul ha, one_mul,
        d_smul ha, smul_add]
      abel

end DGModule

/-! ### The cone of the identity is contractible -/

section Contraction

variable (M)

/-- The contracting homotopy `h (x, y) = (y, 0)` of the cone of the identity of `M`: a map of
degree `-1` with `d ∘ h + h ∘ d = id` (`Cone.d_contraction_add_contraction_d`). It is graded
`A`-linear up to the Koszul sign, `h (a • p) = (-1)^{|a|} a • h p` (`Cone.contraction_smul`). -/
def contraction : Cone (DGModuleHom.id : M →ᵈᵍ[A] M) →+ Cone (DGModuleHom.id : M →ᵈᵍ[A] M) :=
  ((inl _).toAddMonoidHom.comp (Shift.mk 1).toAddMonoidHom).comp (snd _).toAddMonoidHom

variable {M}

theorem contraction_apply (p : Cone (DGModuleHom.id : M →ᵈᵍ[A] M)) :
    contraction M p = inl _ (Shift.mk 1 (snd _ p)) := rfl

/-- The cone of the identity is contractible: `d ∘ h + h ∘ d = id`. -/
theorem d_contraction_add_contraction_d (p : Cone (DGModuleHom.id : M →ᵈᵍ[A] M)) :
    d (contraction M p) + contraction M (d p) = p := by
  refine ext ?_ ?_
  · simp only [contraction_apply, map_add, fst_d, fst_inl, snd_d, d_mk, unmk_mk,
      DGModuleHom.id_apply, mk_add, koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul,
      mk_neg, mk_unmk]
    abel
  · simp [contraction_apply, snd_d]

/-- The contracting homotopy has degree `-1`. -/
theorem contraction_mem {k : ℤ} {p : Cone (DGModuleHom.id : M →ᵈᵍ[A] M)} (hp : p ∈ grading k) :
    contraction M p ∈ grading (k - 1) :=
  inl_mem (mk_mem_grading (snd_mem hp))

/-- The contracting homotopy is graded `A`-linear of degree `-1`, with the Koszul sign. -/
theorem contraction_smul {i : ℤ} {a : A} (ha : a ∈ grading i)
    (p : Cone (DGModuleHom.id : M →ᵈᵍ[A] M)) :
    contraction M (a • p) = koszulSign i • (a • contraction M p) := by
  rw [contraction_apply, contraction_apply, map_smul, mk_smul ha, one_mul, Units.smul_def,
    map_zsmul, map_smul, ← Units.smul_def]

end Contraction

/-! ### Functoriality -/

section Map

variable {M' N' : Type*} [AddCommGroup M'] [DGAddCommGroup M'] [Module A M']
  [AddCommGroup N'] [DGAddCommGroup N'] [Module A N']
  {f' : M' →ᵈᵍ[A] N'} (e : M →ᵈᵍ[A] M') (g : N →ᵈᵍ[A] N')

/-- A commutative square `g ∘ f = f' ∘ e` induces a morphism of mapping cones,
`(x, y) ↦ (e x, g y)`. -/
def map (h : g.comp f = f'.comp e) : Cone f →ᵈᵍ[A] Cone f' where
  __ := (e.shift 1).toLinearMap.prodMap g.toLinearMap
  map_mem' hp := ⟨(e.shift 1).map_mem hp.1, g.map_mem hp.2⟩
  map_d' p := by
    refine ext ?_ ?_
    · exact ((e.shift 1).map_d _)
    · change g (f (unmk 1 (fst f p)) + d (snd f p)) =
        f' (unmk 1 (e.shift 1 (fst f p))) + d (g (snd f p))
      rw [map_add, g.map_d, DGModuleHom.unmk_shift_apply, ← DGModuleHom.comp_apply, h,
        DGModuleHom.comp_apply]

@[simp]
theorem fst_map (h : g.comp f = f'.comp e) (p : Cone f) :
    fst f' (map e g h p) = e.shift 1 (fst f p) := rfl

@[simp]
theorem snd_map (h : g.comp f = f'.comp e) (p : Cone f) :
    snd f' (map e g h p) = g (snd f p) := rfl

theorem map_comp_inr (h : g.comp f = f'.comp e) :
    (map e g h).comp (inr f) = (inr f').comp g :=
  DGModuleHom.ext fun y => ext (by simp) rfl

theorem fst_comp_map (h : g.comp f = f'.comp e) :
    (fst f').comp (map e g h) = (e.shift 1).comp (fst f) :=
  rfl

end Map

end Cone

end DG
