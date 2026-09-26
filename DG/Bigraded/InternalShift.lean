import DG.Bigraded.Basic
import DG.Module.Shift

/-!
# The internal shift of bigraded dg modules

* `DG.InternalShift k M`: the internal shift `M⟨k⟩` of a dg abelian group (or dg module) with an
  internal grading, a type synonym for `M` with the same cohomological grading, differential
  and action, and with the weight grading `(M⟨k⟩)⟨j⟩ = M⟨j + k⟩`. This is the analogue for
  weights of the convention `(M[n])ʲ = Mʲ⁺ⁿ` of `DG.Shift`. Since weights carry no signs,
  neither the differential nor the action is twisted.
* `DG.InternalShift.zeroEquiv : M⟨0⟩ ≃ M` and
  `DG.InternalShift.addEquiv k l : (M⟨l⟩)⟨k⟩ ≃ M⟨k + l⟩`, isomorphisms of dg modules which are
  the identity on elements and preserve weights (`DG.InternalShift.mem_wgrading_zeroEquiv_iff`,
  `DG.InternalShift.mem_wgrading_addEquiv_iff`).
* The cohomological shift `DG.Shift n M` of a bigraded dg module is bigraded, with the weight
  grading of `M` (`DG.Shift.instInternalGrading`, `DG.Shift.instBigradedDGModule`): the Koszul
  twist `a • m = (-1)^{n |a|} (a • m)` of the action preserves weights, because `|a|` is the
  cohomological degree of `a` only.
* `DG.InternalShift.shiftEquiv n k : (M[n])⟨k⟩ ≃ (M⟨k⟩)[n]`: the internal and cohomological
  shifts commute; the isomorphism is the identity on elements, without sign.
* `DG.DGModuleHom.internalShift k : (M →ᵈᵍ[A] N) → (M⟨k⟩ →ᵈᵍ[A] N⟨k⟩)`, the internal shift of
  morphisms (the same underlying function).

`InternalShift k M` is a `def`, not an `abbrev`, so that the weight grading of `M` is not
visible on it; its structures are declared explicitly.
-/

open DirectSum

namespace DG

universe u

/-- The internal shift `M⟨k⟩` of a dg abelian group `M` with an internal grading: the same dg
abelian group (and the same action of a dg ring), with the weight grading
`(M⟨k⟩)⟨j⟩ = M⟨j + k⟩`. -/
def InternalShift (_k : ℤ) (M : Type u) : Type u := M

namespace InternalShift

variable (k : ℤ) {M : Type*}

section AddCommGroup

variable [AddCommGroup M]

instance : AddCommGroup (InternalShift k M) := inferInstanceAs (AddCommGroup M)

/-- The identity `M → M⟨k⟩`, as an additive equivalence. -/
def mk : M ≃+ InternalShift k M := AddEquiv.refl M

/-- The identity `M⟨k⟩ → M`, as an additive equivalence. -/
def unmk : InternalShift k M ≃+ M := AddEquiv.refl M

variable {k}

@[simp] theorem unmk_mk (m : M) : unmk k (mk k m) = m := rfl
@[simp] theorem mk_unmk (m : InternalShift k M) : mk k (unmk k m) = m := rfl
@[simp] theorem mk_symm : (mk k (M := M)).symm = unmk k := rfl
@[simp] theorem unmk_symm : (unmk k (M := M)).symm = mk k := rfl

theorem mk_surjective : Function.Surjective (mk k (M := M)) := (mk k).surjective

end AddCommGroup

section DGAddCommGroup

variable {k} [AddCommGroup M] [DGAddCommGroup M]

instance : DGAddCommGroup (InternalShift k M) := inferInstanceAs (DGAddCommGroup M)

theorem mem_grading_iff {n : ℤ} {m : M} : mk k m ∈ grading n ↔ m ∈ grading n := Iff.rfl

theorem mem_grading_iff' {n : ℤ} {m : InternalShift k M} :
    m ∈ grading n ↔ unmk k m ∈ grading n := Iff.rfl

@[simp] theorem d_mk (m : M) : d (mk k m) = mk k (d m) := rfl
@[simp] theorem unmk_d (m : InternalShift k M) : unmk k (d m) = d (unmk k m) := rfl

variable [InternalGrading M]

instance instInternalGrading : InternalGrading (InternalShift k M) where
  wgrading j := wgrading (M := M) (j + k)
  wdecomposition := Decomposition.reindex (wgrading (M := M)) (Equiv.addRight k)
  isHomogeneous_grading' n j m hm := by
    letI : Decomposition fun j => wgrading (M := M) (Equiv.addRight k j) :=
      Decomposition.reindex (wgrading (M := M)) (Equiv.addRight k)
    have h := Decomposition.coe_decompose_reindex (wgrading (M := M)) (Equiv.addRight k)
      (unmk k m) j
    change (decompose (fun j => wgrading (M := M) (Equiv.addRight k j)) (unmk k m) j : M) ∈
      grading (M := M) n
    rw [h]
    exact decompose_wgrading_mem_grading (M := M) hm _
  d_mem_wgrading' hm := d_mem_wgrading (M := M) hm

theorem mem_wgrading_iff {j : ℤ} {m : M} : mk k m ∈ wgrading j ↔ m ∈ wgrading (j + k) :=
  Iff.rfl

theorem mem_wgrading_iff' {j : ℤ} {m : InternalShift k M} :
    m ∈ wgrading j ↔ unmk k m ∈ wgrading (j + k) := Iff.rfl

/-- The weight components of `M⟨k⟩` are those of `M`, reindexed. -/
theorem coe_decompose_wgrading (m : InternalShift k M) (j : ℤ) :
    unmk k (decompose (wgrading (M := InternalShift k M)) m j : InternalShift k M) =
      (decompose (wgrading (M := M)) (unmk k m) (j + k) : M) := by
  letI : Decomposition fun j => wgrading (M := M) (Equiv.addRight k j) :=
    Decomposition.reindex (wgrading (M := M)) (Equiv.addRight k)
  change (decompose (fun j => wgrading (M := M) (Equiv.addRight k j)) (unmk k m) j : M) = _
  exact Decomposition.coe_decompose_reindex (wgrading (M := M)) (Equiv.addRight k) (unmk k m) j

end DGAddCommGroup

section Module

variable {k} {A : Type*} [Ring A] [AddCommGroup M] [Module A M]

instance : Module A (InternalShift k M) := inferInstanceAs (Module A M)

theorem smul_mk (a : A) (m : M) : a • mk k m = mk k (a • m) := rfl

theorem unmk_smul (a : A) (m : InternalShift k M) : unmk k (a • m) = a • unmk k m := rfl

variable [DGAddCommGroup A] [DGAddCommGroup M]

instance [DGModule A M] : DGModule A (InternalShift k M) := inferInstanceAs (DGModule A M)

instance [InternalGrading A] [InternalGrading M] [BigradedDGModule A M] :
    BigradedDGModule A (InternalShift k M) where
  smul_mem {i j} a m ha hm := by
    rw [mem_wgrading_iff'] at hm ⊢
    rw [vadd_eq_add, add_assoc]
    exact smul_mem_wgrading (M := M) ha hm

end Module

section Equivs

variable {A : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M] [DGAddCommGroup M]
  [Module A M]

variable (A) in
/-- The internal shift by `0` is the identity: `M⟨0⟩ ≃ M`. -/
def zeroEquiv : InternalShift 0 M ≃ᵈᵍ[A] M where
  toFun := unmk 0
  invFun := mk 0
  left_inv := mk_unmk
  right_inv := unmk_mk
  map_add' := map_add (unmk 0)
  map_smul' _ _ := rfl
  map_mem' hm := hm
  map_d' _ := rfl

@[simp] theorem zeroEquiv_apply (m : InternalShift 0 M) : zeroEquiv A m = unmk 0 m := rfl
@[simp] theorem zeroEquiv_symm_apply (m : M) : (zeroEquiv A).symm m = mk 0 m := rfl

variable (A) in
/-- Internal shifts compose: `(M⟨l⟩)⟨k⟩ ≃ M⟨k + l⟩`, the identity on elements. -/
def addEquiv (k l : ℤ) : InternalShift k (InternalShift l M) ≃ᵈᵍ[A] InternalShift (k + l) M where
  toFun x := mk (k + l) (unmk l (unmk k x))
  invFun y := mk k (mk l (unmk (k + l) y))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' hm := hm
  map_d' _ := rfl

@[simp] theorem addEquiv_apply (k l : ℤ) (x : InternalShift k (InternalShift l M)) :
    addEquiv A k l x = mk (k + l) (unmk l (unmk k x)) := rfl

@[simp] theorem addEquiv_symm_apply (k l : ℤ) (y : InternalShift (k + l) M) :
    (addEquiv A k l).symm y = mk k (mk l (unmk (k + l) y)) := rfl

variable [InternalGrading M]

theorem mem_wgrading_zeroEquiv_iff {j : ℤ} {m : InternalShift 0 M} :
    zeroEquiv A m ∈ wgrading j ↔ m ∈ wgrading j := by
  rw [mem_wgrading_iff', add_zero]
  rfl

theorem mem_wgrading_addEquiv_iff (k l : ℤ) {j : ℤ} {x : InternalShift k (InternalShift l M)} :
    addEquiv A k l x ∈ wgrading j ↔ x ∈ wgrading j := by
  rw [mem_wgrading_iff', mem_wgrading_iff', mem_wgrading_iff', add_assoc]
  rfl

end Equivs

end InternalShift

/-! ### Cohomological shifts of bigraded dg modules -/

namespace Shift

variable {n : ℤ} {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [InternalGrading M]

/-- The cohomological shift `M[n]` of a dg abelian group with an internal grading has the
weight grading of `M`. -/
instance instInternalGrading : InternalGrading (Shift n M) where
  wgrading k := wgrading (M := M) k
  wdecomposition := InternalGrading.wdecomposition (M := M)
  isHomogeneous_grading' j k m hm := isHomogeneous_grading M (j + n) k hm
  d_mem_wgrading' {k m} hm := by
    change koszulSign n • d (unmk n m) ∈ wgrading (M := M) k
    rw [Units.smul_def]
    exact zsmul_mem (d_mem_wgrading (M := M) (show unmk n m ∈ wgrading (M := M) k from hm)) _

theorem mem_wgrading_iff {k : ℤ} {m : M} : mk n m ∈ wgrading k ↔ m ∈ wgrading k := Iff.rfl

theorem mem_wgrading_iff' {k : ℤ} {m : Shift n M} : m ∈ wgrading k ↔ unmk n m ∈ wgrading k :=
  Iff.rfl

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]

/-- The twist `a ↦ (-1)^{n |a|} a` preserves weights. -/
theorem twist_mem_wgrading {k : ℤ} {a : A} (ha : a ∈ wgrading k) :
    twist A n a ∈ wgrading k := by
  refine induction_on_of_isHomogeneous (isHomogeneous_wgrading A k) (P := fun a =>
    twist A n a ∈ wgrading k) ?_ (fun {i b} hb hbk => ?_) (fun b b' hb hb' => ?_) ha
  · show twist A n 0 ∈ wgrading k
    rw [map_zero]
    exact zero_mem _
  · show twist A n b ∈ wgrading k
    rw [twist_of_mem hb, Units.smul_def]
    exact zsmul_mem hbk _
  · simp only [map_add]
    exact add_mem hb hb'

variable [Module A M] [BigradedDGModule A M]

/-- The cohomological shift `M[n]` of a bigraded dg module is a bigraded dg module: the Koszul
twist of the action does not affect weights. -/
instance instBigradedDGModule : BigradedDGModule A (Shift n M) where
  smul_mem {i j} a m ha hm := by
    rw [mem_wgrading_iff'] at hm ⊢
    rw [unmk_smul_eq]
    exact smul_mem_wgrading (twist_mem_wgrading ha) hm

end Shift

namespace InternalShift

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] {M : Type*} [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]

variable (A) in
/-- The internal and cohomological shifts commute: `(M[n])⟨k⟩ ≃ (M⟨k⟩)[n]`. The isomorphism is
the identity on elements; no sign appears, since the Koszul twist `(-1)^{n |a|}` of the action
on `M[n]` only involves the cohomological degree `|a|`, which the internal shift does not
change. -/
def shiftEquiv (n k : ℤ) : InternalShift k (Shift n M) ≃ᵈᵍ[A] Shift n (InternalShift k M) where
  toFun x := Shift.mk n (mk k (Shift.unmk n (unmk k x)))
  invFun y := mk k (Shift.mk n (unmk k (Shift.unmk n y)))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' hm := hm
  map_d' _ := rfl

@[simp] theorem shiftEquiv_apply (n k : ℤ) (x : InternalShift k (Shift n M)) :
    shiftEquiv A n k x = Shift.mk n (mk k (Shift.unmk n (unmk k x))) := rfl

@[simp] theorem shiftEquiv_symm_apply (n k : ℤ) (y : Shift n (InternalShift k M)) :
    (shiftEquiv A n k).symm y = mk k (Shift.mk n (unmk k (Shift.unmk n y))) := rfl

theorem mem_wgrading_shiftEquiv_iff [InternalGrading M] (n k : ℤ) {j : ℤ}
    {x : InternalShift k (Shift n M)} : shiftEquiv A n k x ∈ wgrading j ↔ x ∈ wgrading j :=
  Iff.rfl

end InternalShift

/-! ### Internal shifts of morphisms -/

namespace DGModuleHom

variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

open InternalShift

/-- The internal shift of a morphism of dg modules: the same function `M⟨k⟩ → N⟨k⟩`. -/
def internalShift (k : ℤ) (f : M →ᵈᵍ[A] N) : InternalShift k M →ᵈᵍ[A] InternalShift k N where
  toFun m := InternalShift.mk k (f (unmk k m))
  map_add' m m' := map_add f (unmk k m) (unmk k m')
  map_smul' a m := map_smul f a (unmk k m)
  map_mem' hm := f.map_mem hm
  map_d' m := f.map_d (unmk k m)

@[simp]
theorem internalShift_apply (k : ℤ) (f : M →ᵈᵍ[A] N) (m : M) :
    f.internalShift k (InternalShift.mk k m) = InternalShift.mk k (f m) := rfl

theorem unmk_internalShift_apply (k : ℤ) (f : M →ᵈᵍ[A] N) (m : InternalShift k M) :
    unmk k (f.internalShift k m) = f (unmk k m) := rfl

@[simp]
theorem internalShift_id (k : ℤ) :
    (DGModuleHom.id : M →ᵈᵍ[A] M).internalShift k = DGModuleHom.id := rfl

@[simp]
theorem internalShift_comp (k : ℤ) (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) :
    (g.comp f).internalShift k = (g.internalShift k).comp (f.internalShift k) := rfl

@[simp] theorem internalShift_zero (k : ℤ) : (0 : M →ᵈᵍ[A] N).internalShift k = 0 := rfl
@[simp] theorem internalShift_add (k : ℤ) (f g : M →ᵈᵍ[A] N) :
    (f + g).internalShift k = f.internalShift k + g.internalShift k := rfl

/-- The internal shift of a weight-preserving morphism preserves weights. -/
theorem internalShift_mem_wgrading [InternalGrading M] [InternalGrading N] (k : ℤ)
    (f : M →ᵈᵍ[A] N) (hf : ∀ {j : ℤ} {m : M}, m ∈ wgrading j → f m ∈ wgrading j) {j : ℤ}
    {m : InternalShift k M} (hm : m ∈ wgrading j) : f.internalShift k m ∈ wgrading j :=
  hf (j := j + k) hm

end DGModuleHom

end DG
