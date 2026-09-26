import DG.Algebra.Constructions
import DG.Bigraded.InternalShift
import DG.Module.Cohomology

/-!
# Weight gradings on cohomology

Let `M` be a dg abelian group with an internal grading (`DG.InternalGrading M`). Since `d`
preserves weights and the weight projections preserve the cohomological degree, the cocycles
and the coboundaries are homogeneous for the weight grading, so each cohomology group inherits
a weight grading, `Hⁿ(M) = ⨁ k, Hⁿ(M)⟨k⟩` with `Hⁿ(M)⟨k⟩` the classes of cocycles of weight `k`.

* `DG.cocycles.wgrading M n`: the weight grading `Zⁿ(M)⟨k⟩ = Zⁿ(M) ∩ M⟨k⟩` of the cocycles,
  with its decomposition.
* `DG.cohomology.wgrading M n`: the weight grading of `Hⁿ(M)`, the image of the weight grading
  of the cocycles, with its decomposition `DG.cohomology.decomposition`
  (`DG.cohomology.isInternal_wgrading`: `Hⁿ(M)` is the internal direct sum of the `Hⁿ(M)⟨k⟩`).
* `DG.cohomology.map_mem_wgrading`: a morphism of dg modules preserving weights induces maps on
  cohomology preserving weights.
* `DG.cohomology.internalShiftAddEquiv k n : Hⁿ(M⟨k⟩) ≃ Hⁿ(M)`, the identity on classes of
  cocycles, with `Hⁿ(M⟨k⟩)⟨j⟩ ≅ Hⁿ(M)⟨j + k⟩`
  (`DG.cohomology.mem_wgrading_internalShiftAddEquiv_iff`); that is, `H(M⟨k⟩) ≅ H(M)⟨k⟩`.
-/

open DirectSum

namespace DG

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [InternalGrading M]

namespace cocycles

variable (M) in
/-- The weight grading of the cocycles: `Zⁿ(M)⟨k⟩ = Zⁿ(M) ∩ M⟨k⟩`. -/
def wgrading (n k : ℤ) : AddSubgroup (cocycles M n) :=
  (InternalGrading.wgrading k).comap (cocycles M n).subtype

theorem mem_wgrading_iff {n k : ℤ} {z : cocycles M n} :
    z ∈ cocycles.wgrading M n k ↔ (z : M) ∈ InternalGrading.wgrading k :=
  Iff.rfl

variable (M) in
theorem isInternal_wgrading (n : ℤ) : DirectSum.IsInternal (cocycles.wgrading M n) :=
  isInternal_comap _ _ Subtype.val_injective fun k z =>
    ⟨⟨_, isHomogeneous_wgrading_cocycles n k z.2⟩, rfl⟩

/-- The decomposition `Zⁿ(M) = ⨁ k, Zⁿ(M)⟨k⟩`. -/
noncomputable instance decomposition (n : ℤ) : Decomposition (cocycles.wgrading M n) :=
  (isInternal_wgrading M n).chooseDecomposition

/-- The weight components of a cocycle are its weight components in `M`. -/
theorem coe_decompose_wgrading {n : ℤ} (z : cocycles M n) (k : ℤ) :
    ((decompose (cocycles.wgrading M n) z k : cocycles M n) : M) =
      decompose (InternalGrading.wgrading (M := M)) (z : M) k := by
  letI : Decomposition fun k =>
      (InternalGrading.wgrading (M := M) k).comap (cocycles M n).subtype :=
    cocycles.decomposition n
  exact coe_decompose_comap _ (cocycles M n).subtype z k

end cocycles

namespace cohomology

variable (M) in
/-- The weight grading of the cohomology: `Hⁿ(M)⟨k⟩` is the subgroup of classes of cocycles of
weight `k`. -/
def wgrading (n k : ℤ) : AddSubgroup (cohomology M n) :=
  (cocycles.wgrading M n k).map (mk M n)

theorem mem_wgrading_iff {n k : ℤ} {x : cohomology M n} :
    x ∈ cohomology.wgrading M n k ↔
      ∃ z : cocycles M n, (z : M) ∈ InternalGrading.wgrading k ∧ mk M n z = x :=
  AddSubgroup.mem_map

theorem mkOf_mem_wgrading {n k : ℤ} {m : M} (hm : m ∈ grading n) (hd : d m = 0)
    (hk : m ∈ InternalGrading.wgrading k) : mkOf hm hd ∈ cohomology.wgrading M n k :=
  mem_wgrading_iff.mpr ⟨⟨m, hm, hd⟩, hk, rfl⟩

variable (M) in
/-- The kernel of `Zⁿ(M) → Hⁿ(M)` (the coboundaries) is homogeneous for the weight grading. -/
theorem isHomogeneous_ker_mk (n : ℤ) :
    SetLike.IsHomogeneous (cocycles.wgrading M n) (mk M n).ker := by
  intro k z hz
  rw [AddMonoidHom.mem_ker, mk_eq_zero_iff] at hz ⊢
  rw [cocycles.coe_decompose_wgrading]
  exact isHomogeneous_wgrading_coboundaries n k hz

/-- The decomposition `Hⁿ(M) = ⨁ k, Hⁿ(M)⟨k⟩`. -/
noncomputable instance decomposition (n : ℤ) : Decomposition (cohomology.wgrading M n) :=
  Decomposition.map (cocycles.wgrading M n) (mk M n) (mk_surjective M n) (isHomogeneous_ker_mk M n)

variable (M) in
/-- `Hⁿ(M)` is the internal direct sum of its weight components `Hⁿ(M)⟨k⟩`. -/
theorem isInternal_wgrading (n : ℤ) : DirectSum.IsInternal (cohomology.wgrading M n) :=
  Decomposition.isInternal _

/-- The weight components of the class of a cocycle are the classes of its weight
components. -/
theorem decompose_mk {n : ℤ} (z : cocycles M n) (k : ℤ) :
    (decompose (cohomology.wgrading M n) (mk M n z) k : cohomology M n) =
      mk M n (decompose (cocycles.wgrading M n) z k) := by
  induction z using Decomposition.inductionOn (cocycles.wgrading M n) with
  | zero => simp
  | homogeneous z =>
    rename_i j
    have hz : mk M n z ∈ cohomology.wgrading M n j := ⟨z, z.2, rfl⟩
    by_cases h : j = k
    · subst h
      rw [decompose_of_mem_same _ hz, decompose_of_mem_same _ z.2]
    · rw [decompose_of_mem_ne _ hz h, decompose_of_mem_ne _ z.2 h, _root_.map_zero]
  | add z z' hz hz' =>
    rw [_root_.map_add, decompose_add, add_apply, AddSubgroup.coe_add, hz, hz', decompose_add,
      add_apply, AddSubgroup.coe_add, _root_.map_add]

section Map

variable {A : Type*} [Ring A] [DGAddCommGroup A] {N : Type*} [AddCommGroup N] [DGAddCommGroup N]
  [InternalGrading N] [Module A M] [Module A N]

/-- A morphism of dg modules preserving weights induces maps on cohomology preserving
weights. -/
theorem map_mem_wgrading (f : M →ᵈᵍ[A] N)
    (hf : ∀ {k : ℤ} {m : M}, m ∈ InternalGrading.wgrading k → f m ∈ InternalGrading.wgrading k)
    {n k : ℤ} {x : cohomology M n} (hx : x ∈ cohomology.wgrading M n k) :
    map f n x ∈ cohomology.wgrading N n k := by
  obtain ⟨z, hz, rfl⟩ := mem_wgrading_iff.mp hx
  exact mem_wgrading_iff.mpr ⟨_, hf hz, (map_mk f n z).symm⟩

end Map

section InternalShift

omit [InternalGrading M]

/-- The cohomology of the internal shift: `Hⁿ(M⟨k⟩) ≃ Hⁿ(M)`, the identity on classes of
cocycles. It sends `Hⁿ(M⟨k⟩)⟨j⟩` onto `Hⁿ(M)⟨j + k⟩`
(`DG.cohomology.mem_wgrading_internalShiftAddEquiv_iff`), so that `H(M⟨k⟩) ≅ H(M)⟨k⟩`. -/
def internalShiftAddEquiv (k n : ℤ) : cohomology (InternalShift k M) n ≃+ cohomology M n where
  toFun := mapAddMonoidHom (InternalShift.unmk k).toAddMonoidHom (fun hm => hm) (fun _ => rfl) n
  invFun := mapAddMonoidHom (InternalShift.mk k).toAddMonoidHom (fun hm => hm) (fun _ => rfl) n
  left_inv x := by
    induction x using induction_on with
    | h z => rw [mapAddMonoidHom_mk, mapAddMonoidHom_mk]; rfl
  right_inv x := by
    induction x using induction_on with
    | h z => rw [mapAddMonoidHom_mk, mapAddMonoidHom_mk]; rfl
  map_add' := _root_.map_add _

theorem internalShiftAddEquiv_mk (k n : ℤ) (z : cocycles (InternalShift k M) n) :
    internalShiftAddEquiv k n (mk _ n z) =
      mk M n ⟨InternalShift.unmk k z, z.2⟩ :=
  mapAddMonoidHom_mk (InternalShift.unmk k (M := M)).toAddMonoidHom (fun hm => hm) (fun _ => rfl)
    n z

theorem internalShiftAddEquiv_symm_mk (k n : ℤ) (z : cocycles M n) :
    (internalShiftAddEquiv k n).symm (mk M n z) =
      mk (InternalShift k M) n ⟨InternalShift.mk k z, z.2⟩ :=
  mapAddMonoidHom_mk (InternalShift.mk k (M := M)).toAddMonoidHom (fun hm => hm) (fun _ => rfl)
    n z

variable [InternalGrading M]

/-- `Hⁿ(M⟨k⟩)⟨j⟩ ≅ Hⁿ(M)⟨j + k⟩` under `DG.cohomology.internalShiftAddEquiv`. -/
theorem mem_wgrading_internalShiftAddEquiv_iff {k n j : ℤ} {x : cohomology (InternalShift k M) n} :
    internalShiftAddEquiv k n x ∈ cohomology.wgrading M n (j + k) ↔
      x ∈ cohomology.wgrading (InternalShift k M) n j := by
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ := mem_wgrading_iff.mp hx
    rw [← (internalShiftAddEquiv k n).symm_apply_apply x, ← hzx, internalShiftAddEquiv_symm_mk]
    exact mem_wgrading_iff.mpr ⟨_, hz, rfl⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := mem_wgrading_iff.mp hx
    rw [internalShiftAddEquiv_mk]
    exact mem_wgrading_iff.mpr ⟨_, hz, rfl⟩

end InternalShift

end cohomology

end DG
