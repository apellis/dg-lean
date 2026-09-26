import DG.Module.Basic

/-!
# Products of dg modules

The product `M × N` of two dg abelian groups is a dg abelian group with the componentwise
grading `(M × N)ⁿ = Mⁿ × Nⁿ` and the componentwise differential. For dg `A`-modules `M`, `N`,
the product is a dg `A`-module, and the projections `M × N → M`, `M × N → N` and the
inclusions `M → M × N`, `N → M × N` are morphisms of dg modules.

The grading of `M × N` is an internal direct sum decomposition by
`DirectSum.Decomposition.prod`, the product of two internal direct sum decompositions.
-/

open DirectSum

namespace DirectSum.Decomposition

variable {ι M N : Type*} [DecidableEq ι] [AddCommGroup M] [AddCommGroup N]
  (ℳ : ι → AddSubgroup M) (𝒩 : ι → AddSubgroup N) [Decomposition ℳ] [Decomposition 𝒩]

/-- The inclusion `ℳ i →+ ℳ i × 𝒩 i` of the first factor, used for `Decomposition.prod`. -/
private def prodInl (i : ι) : ℳ i →+ (ℳ i).prod (𝒩 i) :=
  ((AddMonoidHom.inl M N).comp (ℳ i).subtype).codRestrict _ fun x => ⟨x.2, zero_mem _⟩

/-- The inclusion `𝒩 i →+ ℳ i × 𝒩 i` of the second factor, used for `Decomposition.prod`. -/
private def prodInr (i : ι) : 𝒩 i →+ (ℳ i).prod (𝒩 i) :=
  ((AddMonoidHom.inr M N).comp (𝒩 i).subtype).codRestrict _ fun y => ⟨zero_mem _, y.2⟩

/-- The decomposition of the first factor of `M × N`. -/
private def prodDecomposeFst : M →+ ⨁ i, (ℳ i).prod (𝒩 i) :=
  (DirectSum.toAddMonoid fun i => (DirectSum.of _ i).comp (prodInl ℳ 𝒩 i)).comp
    (decomposeAddEquiv ℳ).toAddMonoidHom

/-- The decomposition of the second factor of `M × N`. -/
private def prodDecomposeSnd : N →+ ⨁ i, (ℳ i).prod (𝒩 i) :=
  (DirectSum.toAddMonoid fun i => (DirectSum.of _ i).comp (prodInr ℳ 𝒩 i)).comp
    (decomposeAddEquiv 𝒩).toAddMonoidHom

omit [Decomposition 𝒩] in
private theorem coe_prodDecomposeFst (m : M) :
    DirectSum.coeAddMonoidHom (fun i => (ℳ i).prod (𝒩 i)) (prodDecomposeFst ℳ 𝒩 m) = (m, 0) := by
  induction m using Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous x =>
    simp only [prodDecomposeFst, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      decomposeAddEquiv_apply, decompose_coe, toAddMonoid_of, coeAddMonoidHom_of]
    rfl
  | add m m' hm hm' => rw [map_add, map_add, hm, hm', Prod.mk_add_mk, add_zero]

omit [Decomposition ℳ] in
private theorem coe_prodDecomposeSnd (n : N) :
    DirectSum.coeAddMonoidHom (fun i => (ℳ i).prod (𝒩 i)) (prodDecomposeSnd ℳ 𝒩 n) = (0, n) := by
  induction n using Decomposition.inductionOn 𝒩 with
  | zero => simp
  | homogeneous y =>
    simp only [prodDecomposeSnd, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      decomposeAddEquiv_apply, decompose_coe, toAddMonoid_of, coeAddMonoidHom_of]
    rfl
  | add n n' hn hn' => rw [map_add, map_add, hn, hn', Prod.mk_add_mk, add_zero]

/-- The product of two internal direct sum decompositions:
`M × N = ⨁ i, ℳ i × 𝒩 i`. -/
def prod : Decomposition fun i => (ℳ i).prod (𝒩 i) where
  decompose' p := prodDecomposeFst ℳ 𝒩 p.1 + prodDecomposeSnd ℳ 𝒩 p.2
  left_inv p := by
    rw [map_add, coe_prodDecomposeFst, coe_prodDecomposeSnd, Prod.mk_add_mk, add_zero, zero_add]
  right_inv z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of i w =>
      obtain ⟨⟨x, y⟩, hx, hy⟩ := w
      have hx : x ∈ ℳ i := hx
      have hy : y ∈ 𝒩 i := hy
      dsimp only
      rw [coeAddMonoidHom_of]
      simp only [prodDecomposeFst, prodDecomposeSnd, AddMonoidHom.comp_apply,
        AddEquiv.coe_toAddMonoidHom, decomposeAddEquiv_apply, decompose_of_mem ℳ hx,
        decompose_of_mem 𝒩 hy, toAddMonoid_of, ← map_add]
      refine congrArg (DirectSum.of (fun i => (ℳ i).prod (𝒩 i)) i) (Subtype.ext ?_)
      change ((x, 0) : M × N) + (0, y) = (x, y)
      rw [Prod.mk_add_mk, add_zero, zero_add]
    | add z z' hz hz' =>
      dsimp only at hz hz' ⊢
      rw [map_add, Prod.fst_add, Prod.snd_add, map_add, map_add, add_add_add_comm, hz, hz']

end DirectSum.Decomposition

namespace DG

section DGAddCommGroup

variable (M N : Type*) [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]

/-- The product of two dg abelian groups, with the componentwise grading and differential. -/
instance Prod.instDGAddCommGroup : DGAddCommGroup (M × N) where
  grading n := (grading (M := M) n).prod (grading (M := N) n)
  decomposition := Decomposition.prod _ _
  d := AddMonoidHom.prodMap d d
  d_mem' hm := ⟨d_mem hm.1, d_mem hm.2⟩
  d_d' _ := by ext <;> simp

variable {M N}

@[simp]
theorem Prod.grading_eq (n : ℤ) :
    grading (M := M × N) n = (grading (M := M) n).prod (grading (M := N) n) := rfl

theorem Prod.mem_grading {n : ℤ} {p : M × N} :
    p ∈ grading (M := M × N) n ↔ p.1 ∈ grading n ∧ p.2 ∈ grading n :=
  Iff.rfl

@[simp]
theorem Prod.d_apply (p : M × N) : d p = (d p.1, d p.2) := rfl

@[simp]
theorem Prod.fst_d (p : M × N) : (d p).1 = d p.1 := rfl

@[simp]
theorem Prod.snd_d (p : M × N) : (d p).2 = d p.2 := rfl

end DGAddCommGroup

section DGModule

variable {A : Type*} [Ring A] [DGAddCommGroup A]
variable (M N : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- The product of two dg `A`-modules is a dg `A`-module. -/
instance Prod.instDGModule [DGModule A M] [DGModule A N] : DGModule A (M × N) where
  smul_mem _ _ _ _ ha hp := ⟨smul_mem_grading ha hp.1, smul_mem_grading ha hp.2⟩
  d_smul' ha p := by ext <;> simp [d_smul ha]

namespace DGModuleHom

/-- The first projection `M × N →ᵈᵍ[A] M`. -/
def fst : (M × N) →ᵈᵍ[A] M where
  __ := LinearMap.fst A M N
  map_mem' hp := hp.1
  map_d' _ := rfl

/-- The second projection `M × N →ᵈᵍ[A] N`. -/
def snd : (M × N) →ᵈᵍ[A] N where
  __ := LinearMap.snd A M N
  map_mem' hp := hp.2
  map_d' _ := rfl

/-- The inclusion of the first factor `M →ᵈᵍ[A] M × N`. -/
def inl : M →ᵈᵍ[A] M × N where
  __ := LinearMap.inl A M N
  map_mem' hm := ⟨hm, zero_mem _⟩
  map_d' _ := by ext <;> simp

/-- The inclusion of the second factor `N →ᵈᵍ[A] M × N`. -/
def inr : N →ᵈᵍ[A] M × N where
  __ := LinearMap.inr A M N
  map_mem' hn := ⟨zero_mem _, hn⟩
  map_d' _ := by ext <;> simp

/-- The pairing of two morphisms of dg modules `P →ᵈᵍ[A] M × N`. -/
def prod {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P]
    (f : P →ᵈᵍ[A] M) (g : P →ᵈᵍ[A] N) : P →ᵈᵍ[A] M × N where
  __ := f.toLinearMap.prod g.toLinearMap
  map_mem' hx := ⟨f.map_mem hx, g.map_mem hx⟩
  map_d' x := by ext <;> simp

variable {M N}

@[simp] theorem prod_apply {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P]
    (f : P →ᵈᵍ[A] M) (g : P →ᵈᵍ[A] N) (x : P) : prod M N f g x = (f x, g x) := rfl

@[simp] theorem fst_apply (p : M × N) : fst (A := A) M N p = p.1 := rfl
@[simp] theorem snd_apply (p : M × N) : snd (A := A) M N p = p.2 := rfl
@[simp] theorem inl_apply (m : M) : inl (A := A) M N m = (m, 0) := rfl
@[simp] theorem inr_apply (n : N) : inr (A := A) M N n = (0, n) := rfl

end DGModuleHom

end DGModule

end DG
