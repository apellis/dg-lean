import DG.Algebra.Hom

/-!
# Isomorphisms of dg algebras

* `DGAlgEquiv R A B` (notation `A ≃ᵈᵍₐ[R] B`): `R`-algebra isomorphisms of degree `0`
  commuting with the differentials, the isomorphisms of dg `R`-algebras.
* `DGAlgEquiv.ofAlgEquiv`: an algebra isomorphism which maps `Aⁿ` into `Bⁿ` for every `n` and
  commutes with `d` is a dg algebra isomorphism; the inverse automatically has the same
  properties (`DG.symm_mem_of_map_mem`).
-/

open DirectSum

namespace DG

section Inverse

variable {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]

/-- If a bijective additive map of degree `0` between graded abelian groups maps `Mⁿ` into `Nⁿ`
for every `n`, then its inverse maps `Nⁿ` into `Mⁿ`. -/
theorem symm_mem_of_map_mem (e : M ≃+ N) (he : ∀ {n : ℤ} {m : M}, m ∈ grading n → e m ∈ grading n)
    {n : ℤ} {x : N} (hx : x ∈ grading n) : e.symm x ∈ grading n := by
  classical
  set m := e.symm x with hm
  have hcomp : ∀ i, i ≠ n → (decompose (grading (M := M)) m i : M) = 0 := by
    intro i hi
    apply e.injective
    rw [map_zero]
    have h := decompose_map (k := 0) (e : M →+ N) (fun hm => by rw [add_zero]; exact he hm) m i
    rw [add_zero] at h
    change (e : M →+ N) _ = 0
    rw [← h, hm]
    change (decompose (grading (M := N)) (e (e.symm x)) i : N) = 0
    rw [AddEquiv.apply_symm_apply, decompose_of_mem_ne _ hx hi.symm]
  have : m = (decompose (grading (M := M)) m n : M) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose (grading (M := M)) m]
    by_cases hn : n ∈ DFinsupp.support (decompose (grading (M := M)) m)
    · exact Finset.sum_eq_single_of_mem n hn fun i _ hi => hcomp i hi
    · rw [Finset.sum_eq_zero fun i hi => hcomp i fun h => hn (h ▸ hi)]
      rw [DFinsupp.notMem_support_iff] at hn
      rw [hn, ZeroMemClass.coe_zero]
  rw [this]
  exact (decompose (grading (M := M)) m n).2

end Inverse

/-- An isomorphism of dg `R`-algebras: an `R`-algebra isomorphism of degree `0` commuting with
the differentials. -/
structure DGAlgEquiv (R A B : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
    [Ring B] [Algebra R B] [DGAddCommGroup B] extends A ≃ₐ[R] B where
  map_mem' : ∀ {n : ℤ} {a : A}, a ∈ grading n → toFun a ∈ grading n
  map_d' : ∀ a : A, toFun (d a) = d (toFun a)

@[inherit_doc]
notation:50 A " ≃ᵈᵍₐ[" R "] " B => DGAlgEquiv R A B

namespace DGAlgEquiv

variable {R A B C : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [Ring C] [Algebra R C] [DGAddCommGroup C]

instance : EquivLike (A ≃ᵈᵍₐ[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f, _, _⟩ := f
    obtain ⟨g, _, _⟩ := g
    congr
    exact AlgEquiv.ext (congrFun h₁)

instance : AlgEquivClass (A ≃ᵈᵍₐ[R] B) R A B where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[simp]
theorem coe_toAlgEquiv (e : A ≃ᵈᵍₐ[R] B) : ⇑e.toAlgEquiv = e := rfl

@[ext]
theorem ext {e e' : A ≃ᵈᵍₐ[R] B} (h : ∀ a, e a = e' a) : e = e' :=
  DFunLike.ext e e' h

theorem map_mem (e : A ≃ᵈᵍₐ[R] B) {n : ℤ} {a : A} (ha : a ∈ grading n) : e a ∈ grading n :=
  e.map_mem' ha

@[simp]
theorem map_d (e : A ≃ᵈᵍₐ[R] B) (a : A) : e (d a) = d (e a) :=
  e.map_d' a

/-- The underlying morphism of dg algebras. -/
def toDGAlgHom (e : A ≃ᵈᵍₐ[R] B) : A →ᵈᵍₐ[R] B where
  __ := e.toAlgEquiv.toAlgHom
  map_mem' := e.map_mem'
  map_d' := e.map_d'

@[simp]
theorem coe_toDGAlgHom (e : A ≃ᵈᵍₐ[R] B) : ⇑e.toDGAlgHom = e := rfl

/-- An algebra isomorphism which maps `Aⁿ` into `Bⁿ` and commutes with the differentials is an
isomorphism of dg algebras. -/
def ofAlgEquiv (e : A ≃ₐ[R] B) (map_mem : ∀ {n : ℤ} {a : A}, a ∈ grading n → e a ∈ grading n)
    (map_d : ∀ a : A, e (d a) = d (e a)) : A ≃ᵈᵍₐ[R] B where
  __ := e
  map_mem' := map_mem
  map_d' := map_d

@[simp]
theorem coe_ofAlgEquiv (e : A ≃ₐ[R] B) (map_mem) (map_d) : ⇑(ofAlgEquiv e map_mem map_d) = e :=
  rfl

/-- The identity isomorphism. -/
def refl : A ≃ᵈᵍₐ[R] A :=
  ofAlgEquiv AlgEquiv.refl (fun ha => ha) fun _ => rfl

@[simp]
theorem refl_apply (a : A) : (refl : A ≃ᵈᵍₐ[R] A) a = a := rfl

/-- The inverse of an isomorphism of dg algebras. -/
def symm (e : A ≃ᵈᵍₐ[R] B) : B ≃ᵈᵍₐ[R] A :=
  ofAlgEquiv e.toAlgEquiv.symm
    (fun hb => symm_mem_of_map_mem e.toAlgEquiv.toAddEquiv (fun ha => e.map_mem ha) hb)
    fun b => e.toAlgEquiv.injective <| by
      rw [AlgEquiv.apply_symm_apply, coe_toAlgEquiv, map_d, ← coe_toAlgEquiv e,
        AlgEquiv.apply_symm_apply]

@[simp]
theorem apply_symm_apply (e : A ≃ᵈᵍₐ[R] B) (b : B) : e (e.symm b) = b :=
  e.toAlgEquiv.apply_symm_apply b

@[simp]
theorem symm_apply_apply (e : A ≃ᵈᵍₐ[R] B) (a : A) : e.symm (e a) = a :=
  e.toAlgEquiv.symm_apply_apply a

/-- The composition of isomorphisms of dg algebras. -/
def trans (e : A ≃ᵈᵍₐ[R] B) (e' : B ≃ᵈᵍₐ[R] C) : A ≃ᵈᵍₐ[R] C :=
  ofAlgEquiv (e.toAlgEquiv.trans e'.toAlgEquiv) (fun ha => e'.map_mem (e.map_mem ha))
    fun a => by simp

@[simp]
theorem trans_apply (e : A ≃ᵈᵍₐ[R] B) (e' : B ≃ᵈᵍₐ[R] C) (a : A) : e.trans e' a = e' (e a) :=
  rfl

end DGAlgEquiv

end DG
