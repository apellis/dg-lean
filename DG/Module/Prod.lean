import DG.Module.Basic

/-!
# Products of dg modules

The product `M × N` of two dg abelian groups is a dg abelian group with the componentwise
grading `(M × N)ⁿ = Mⁿ × Nⁿ` and the componentwise differential. For dg `A`-modules `M`, `N`,
the product is a dg `A`-module, and the projections `M × N → M`, `M × N → N` and the
inclusions `M → M × N`, `N → M × N` are morphisms of dg modules.
-/

open DirectSum




namespace DG

section DGAddCommGroup

variable (M N : Type*) [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]

/-- The inclusion `Mⁿ →+ Mⁿ × Nⁿ` of the first factor. -/
private def gradingInl (n : ℤ) :
    grading (M := M) n →+ (grading (M := M) n).prod (grading (M := N) n) where
  toFun m := ⟨(m, 0), m.2, zero_mem _⟩
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

/-- The inclusion `Nⁿ →+ Mⁿ × Nⁿ` of the second factor. -/
private def gradingInr (n : ℤ) :
    grading (M := N) n →+ (grading (M := M) n).prod (grading (M := N) n) where
  toFun m := ⟨(0, m), zero_mem _, m.2⟩
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

-- Instance search on `⨁ n, ↥(H n)` for subgroups `H n` of a product `M × N` is slow: the
-- `SetLike.gsemiring`-style instances are tried first and explore the ring instances of `M × N`.
set_option synthInstance.maxHeartbeats 40000

/-- The decomposition of `M × N` into the componentwise homogeneous pieces, as an additive map. -/
private def prodDecompose :
    M × N →+ ⨁ n, (grading (M := M) n).prod (grading (M := N) n) :=
  ((DirectSum.map (gradingInl M N)).comp
      (DirectSum.decomposeAddEquiv (grading (M := M))).toAddMonoidHom).comp
    (AddMonoidHom.fst M N) +
  ((DirectSum.map (gradingInr M N)).comp
      (DirectSum.decomposeAddEquiv (grading (M := N))).toAddMonoidHom).comp
    (AddMonoidHom.snd M N)

private theorem prodDecompose_apply (p : M × N) :
    prodDecompose M N p = DirectSum.map (gradingInl M N) (decompose _ p.1) +
      DirectSum.map (gradingInr M N) (decompose _ p.2) := rfl

private theorem coeAddMonoidHom_map_gradingInl
    (x : ⨁ n, grading (M := M) n) :
    (DirectSum.coeAddMonoidHom _ (DirectSum.map (gradingInl M N) x) : M × N) =
      (DirectSum.coeAddMonoidHom _ x, 0) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x => simp [gradingInl]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk, add_zero]

private theorem coeAddMonoidHom_map_gradingInr
    (x : ⨁ n, grading (M := N) n) :
    (DirectSum.coeAddMonoidHom _ (DirectSum.map (gradingInr M N) x) : M × N) =
      (0, DirectSum.coeAddMonoidHom _ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x => simp [gradingInr]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk, add_zero]

/-- The product of two dg abelian groups, with the componentwise grading and differential. -/
instance Prod.instDGAddCommGroup : DGAddCommGroup (M × N) where
  grading n := (grading (M := M) n).prod (grading (M := N) n)
  decomposition :=
    { decompose' := prodDecompose M N
      left_inv := fun p => by
        rw [prodDecompose_apply, map_add, coeAddMonoidHom_map_gradingInl,
          coeAddMonoidHom_map_gradingInr]
        change ((decompose _).symm (decompose _ p.1), 0) +
          (0, (decompose _).symm (decompose _ p.2)) = p
        simp
      right_inv := fun x => by
        induction x using DirectSum.induction_on with
        | zero => simp
        | of i x =>
          obtain ⟨⟨m, n⟩, hm, hn⟩ := x
          rw [DirectSum.coeAddMonoidHom_of, prodDecompose_apply]
          change DirectSum.map _ (decompose _ m) + DirectSum.map _ (decompose _ n) = _
          rw [decompose_of_mem (grading (M := M)) hm, decompose_of_mem (grading (M := N)) hn,
            DirectSum.map_of, DirectSum.map_of, ← map_add]
          congr 1
          ext <;> simp [gradingInl, gradingInr]
        | add x y hx hy => rw [map_add, map_add, hx, hy] }
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

variable {M N}

@[simp] theorem fst_apply (p : M × N) : fst (A := A) M N p = p.1 := rfl
@[simp] theorem snd_apply (p : M × N) : snd (A := A) M N p = p.2 := rfl
@[simp] theorem inl_apply (m : M) : inl (A := A) M N m = (m, 0) := rfl
@[simp] theorem inr_apply (n : N) : inr (A := A) M N n = (0, n) := rfl

end DGModuleHom

end DGModule

end DG
