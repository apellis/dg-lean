import DG.Category.Tensor.RightModule
import DG.Module.DirectSum
import DG.Module.Quotient
import DG.Module.TensorProduct
import DG.Algebra.AddEquiv

/-!
# The tensor product over a dg category

For a dg category `C`, a right dg module `N` over `C` (a left dg module over `DGOpposite C`,
`DG.Category.Tensor.RightModule`) and a left dg module `M` over `C`, the tensor product
`N ⊗_C M` (`DG.CatTensorProduct N M`) is the dg abelian group

  `N ⊗_C M = (⨁_{X ∈ C} N(X) ⊗ M(X)) ⧸ ⟨(n • f) ⊗ m - n ⊗ (f • m)⟩`,

the relations running over the morphisms `f : X ⟶ Y`, `n ∈ N(Y)`, `m ∈ M(X)`, where `n • f` is
the right action `DG.CatModule.ract` (written `n <• f`). With the right action, the relations
carry no sign, as for the tensor product `M ⊗_A N` over a dg ring
(`DG.Module.TensorProductOver`); the Koszul sign of the exchange of `f` and `n` is contained in
the passage from the left `DGOpposite C`-action to the right action, `n • f = (-1)^{|f||n|} f • n`.

The grading and the differential are induced from those of the direct sum of the tensor
products of dg abelian groups (`DG.Module.TensorProduct`), with
`d (n ⊗ m) = d n ⊗ m + (-1)^{|n|} n ⊗ d m`; the relations form a dg subgroup because of the
right and left Leibniz rules.

## Main definitions and results

* `DG.CatTensorProduct N M`, with the classes `DG.CatTensorProduct.tmul X n m` of the tensors
  `n ⊗ m ∈ N(X) ⊗ M(X)` and the balancing relation
  `DG.CatTensorProduct.ract_tmul : tmul X (n <• f) m = tmul Y n (f • m)`.
* `DG.CatTensorProduct.lift`: the universal property, the additive map induced by a balanced
  family of bi-additive maps `N(X) →+ M(X) →+ P`; its compatibility with the gradings and the
  differentials (`lift_mem`, `lift_d`), and uniqueness (`lift_unique`, `addHom_ext`).
* `DG.CatTensorProduct.map φ ψ`: functoriality in both variables (`map_id`, `map_comp`), by
  chain maps of degree `0` (`map_mem`, `map_d`), and `DG.CatTensorProduct.congr` for
  isomorphisms.
* The co-Yoneda isomorphisms: `DG.CatTensorProduct.lid M X : C(-, X) ⊗_C M ≅ M(X)`,
  `h ⊗ m ↦ h • m`, and `DG.CatTensorProduct.rid N X : N ⊗_C C(X, -) ≅ N(X)`,
  `n ⊗ h ↦ n • h`, as isomorphisms of dg abelian groups (`DG.DGAddEquiv`), natural in the
  module (`lid_naturality`, `rid_naturality`).

## Implementation notes

The direct sum over the objects of `C` uses classical decidability of equality of objects;
all statements are phrased through `tmul`, `lift` and the induction principles, so the choice is
invisible downstream.
-/

open CategoryTheory TensorProduct

universe w w₁ w₂ w₃ w₄ v u

noncomputable section

namespace DG

open DGOpposite
open scoped CatModule
open CatModule (representable representable_op_ract ract_add add_ract ract_zero zero_ract
  ract_neg neg_ract ract_units_smul units_smul_ract ract_mem_grading ract_comp ract_id d_ract)

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

namespace CatTensorProduct

variable (N : CatModule.{w₁} (DGOpposite C)) (M : CatModule.{w₂} C)

/-- The summand `N(X) ⊗ M(X)` of the tensor product over `C`. -/
abbrev Summand (X : C) : Type (max w₁ w₂) := N.obj (op X) ⊗[ℤ] M.obj X

/-- The direct sum `⨁_X N(X) ⊗ M(X)`, of which `N ⊗_C M` is a quotient. -/
abbrev Pre : Type (max u w₁ w₂) := DirectSum C (Summand N M)

open scoped Classical in
/-- The inclusion of the summand `N(X) ⊗ M(X)`. -/
def ι (X : C) : Summand N M X →+ Pre N M := DirectSum.of (Summand N M) X

open scoped Classical in
/-- The dg structure on `⨁_X N(X) ⊗ M(X)`. -/
instance instDGAddCommGroupPre : DGAddCommGroup (Pre N M) :=
  DG.DirectSum.instDGAddCommGroup (Summand N M)

variable {N M}

theorem ι_mem_grading {X : C} {k : ℤ} {x : Summand N M X} (hx : x ∈ grading k) :
    ι N M X x ∈ grading k := by
  classical
  exact DG.DirectSum.of_mem_grading (Summand N M) X hx

theorem d_ι {X : C} (x : Summand N M X) : d (ι N M X x) = ι N M X (d x) := by
  classical
  exact DG.DirectSum.d_of (Summand N M) X x

/-- Induction on the elements of `⨁_X N(X) ⊗ M(X)`. -/
theorem pre_induction_on {P : Pre N M → Prop} (x : Pre N M) (zero : P 0)
    (tmul : ∀ (X : C) (n : N.obj (op X)) (m : M.obj X), P (ι N M X (n ⊗ₜ m)))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact zero
  | of X y =>
    induction y using TensorProduct.induction_on with
    | zero => simpa [ι] using zero
    | tmul n m => exact tmul X n m
    | add y y' hy hy' =>
      have := add _ _ hy hy'
      rwa [← map_add] at this
  | add x y hx hy => exact add x y hx hy

variable (N M) in
/-- The balancing relation `(n • f) ⊗ m - n ⊗ (f • m)` attached to `f : X ⟶ Y`, `n ∈ N(Y)`
and `m ∈ M(X)`. -/
def relElem {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X) : Pre N M :=
  ι N M X ((n <• f) ⊗ₜ m) - ι N M Y (n ⊗ₜ (f • m))

theorem relElem_add_left {X Y : C} (f f' : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X) :
    relElem N M (f + f') n m = relElem N M f n m + relElem N M f' n m := by
  simp only [relElem, ract_add, AddMonoidHom.add_apply, CatModule.add_smul,
    TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
  abel

theorem relElem_add_mid {X Y : C} (f : X ⟶ Y) (n n' : N.obj (op Y)) (m : M.obj X) :
    relElem N M f (n + n') m = relElem N M f n m + relElem N M f n' m := by
  simp only [relElem, add_ract, TensorProduct.add_tmul, map_add]
  abel

theorem relElem_add_right {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) (m m' : M.obj X) :
    relElem N M f n (m + m') = relElem N M f n m + relElem N M f n m' := by
  simp only [relElem, CatModule.smul_add, TensorProduct.tmul_add, map_add]
  abel

@[simp]
theorem relElem_zero_left {X Y : C} (n : N.obj (op Y)) (m : M.obj X) :
    relElem N M (0 : X ⟶ Y) n m = 0 := by
  simp [relElem]

@[simp]
theorem relElem_zero_mid {X Y : C} (f : X ⟶ Y) (m : M.obj X) :
    relElem N M f (0 : N.obj (op Y)) m = 0 := by
  simp [relElem]

@[simp]
theorem relElem_zero_right {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) :
    relElem N M f n (0 : M.obj X) = 0 := by
  simp [relElem]

theorem relElem_units_smul_right {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X)
    (u : ℤˣ) : relElem N M f n (u • m) = u • relElem N M f n m := by
  rw [relElem, relElem, CatModule.smul_units_smul]
  simp only [Units.smul_def, TensorProduct.tmul_smul, map_zsmul, _root_.smul_sub]

theorem relElem_units_smul_left {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X)
    (u : ℤˣ) : relElem N M (u • f) n m = u • relElem N M f n m := by
  rw [relElem, relElem, ract_units_smul, CatModule.units_smul_smul]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul,
    _root_.smul_sub]

variable (N M) in
/-- The subgroup of balancing relations. -/
def rel : AddSubgroup (Pre N M) :=
  AddSubgroup.closure {x | ∃ (X Y : C) (f : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X),
    relElem N M f n m = x}

theorem relElem_mem_rel {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X) :
    relElem N M f n m ∈ rel N M :=
  AddSubgroup.subset_closure ⟨X, Y, f, n, m, rfl⟩

variable (N M) in
/-- The homogeneous balancing relations. -/
def relGen : Set (Pre N M) :=
  {x | ∃ (X Y : C) (i j k : ℤ) (f : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X),
    f ∈ grading i ∧ n ∈ grading j ∧ m ∈ grading k ∧ relElem N M f n m = x}

theorem rel_eq_closure_relGen : rel N M = AddSubgroup.closure (relGen N M) := by
  refine le_antisymm (AddSubgroup.closure_le _ |>.mpr ?_)
    (AddSubgroup.closure_mono fun x ⟨X, Y, _, _, _, f, n, m, _, _, _, hx⟩ => ⟨X, Y, f, n, m, hx⟩)
  rintro _ ⟨X, Y, f, n, m, rfl⟩
  set S := AddSubgroup.closure (relGen N M)
  induction f using DG.induction_on with
  | h_zero => simpa using zero_mem S
  | h_add f f' hf hf' => rw [relElem_add_left]; exact add_mem hf hf'
  | h_homogeneous f =>
    induction n using DG.induction_on with
    | h_zero => simpa using zero_mem S
    | h_add n n' hn hn' => rw [relElem_add_mid]; exact add_mem hn hn'
    | h_homogeneous n =>
      induction m using DG.induction_on with
      | h_zero => simpa using zero_mem S
      | h_add m m' hm hm' => rw [relElem_add_right]; exact add_mem hm hm'
      | h_homogeneous m =>
        exact AddSubgroup.subset_closure ⟨X, Y, _, _, _, f, n, m, f.2, n.2, m.2, rfl⟩

theorem relElem_mem_grading {X Y : C} {i j k : ℤ} {f : X ⟶ Y} {n : N.obj (op Y)}
    {m : M.obj X} (hf : f ∈ grading i) (hn : n ∈ grading j) (hm : m ∈ grading k) :
    relElem N M f n m ∈ grading (j + i + k) := by
  refine sub_mem (ι_mem_grading (tmul_mem_grading (ract_mem_grading hn hf) hm)) ?_
  rw [add_assoc]
  exact ι_mem_grading (tmul_mem_grading hn (CatModule.smul_mem_grading hf hm))

/-- The differential of a balancing relation is a combination of balancing relations. -/
theorem d_relElem {X Y : C} {i j : ℤ} {f : X ⟶ Y} {n : N.obj (op Y)} (hf : f ∈ grading i)
    (hn : n ∈ grading j) (m : M.obj X) :
    d (relElem N M f n m) = relElem N M f (d n) m + koszulSign j • relElem N M (d f) n m +
      koszulSign (j + i) • relElem N M f n (d m) := by
  rw [← relElem_units_smul_right, ← relElem_units_smul_left, relElem, relElem, relElem, relElem,
    d_sub, d_ι, d_ι, d_tmul_of_mem (ract_mem_grading hn hf), d_tmul_of_mem hn, d_ract hn,
    CatModule.d_smul hf, TensorProduct.add_tmul, TensorProduct.tmul_add, ract_units_smul,
    CatModule.smul_units_smul, CatModule.units_smul_smul, koszulSign_add]
  simp only [Units.smul_def, Units.val_mul, mul_smul, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, map_add, map_zsmul, map_sub, _root_.smul_sub, _root_.smul_add]
  abel

instance isDGAddSubgroup_rel : IsDGAddSubgroup (rel N M) := by
  rw [rel_eq_closure_relGen]
  refine IsDGAddSubgroup.closure ?_ ?_
  · rintro _ ⟨X, Y, i, j, k, f, n, m, hf, hn, hm, rfl⟩
    exact ⟨_, relElem_mem_grading hf hn hm⟩
  · rintro _ ⟨X, Y, i, j, k, f, n, m, hf, hn, hm, rfl⟩
    rw [d_relElem hf hn, ← rel_eq_closure_relGen]
    refine add_mem (add_mem (relElem_mem_rel _ _ _) ?_) ?_ <;>
      (rw [Units.smul_def]; exact zsmul_mem (relElem_mem_rel _ _ _) _)

end CatTensorProduct

variable (N : CatModule.{w₁} (DGOpposite C)) (M : CatModule.{w₂} C)

/-- The tensor product `N ⊗_C M` of a right dg module `N` and a left dg module `M` over a dg
category `C`: the quotient of `⨁_X N(X) ⊗ M(X)` by the balancing relations
`(n • f) ⊗ m = n ⊗ (f • m)`. -/
def CatTensorProduct : Type (max u w₁ w₂) :=
  CatTensorProduct.Pre N M ⧸ CatTensorProduct.rel N M

namespace CatTensorProduct

instance : AddCommGroup (CatTensorProduct N M) :=
  inferInstanceAs (AddCommGroup (Pre N M ⧸ rel N M))

/-- The tensor product `N ⊗_C M` is a dg abelian group, with `(N ⊗_C M)ᵏ` spanned by the
`n ⊗ m` with `|n| + |m| = k` and `d (n ⊗ m) = d n ⊗ m + (-1)^{|n|} n ⊗ d m`. -/
instance instDGAddCommGroup : DGAddCommGroup (CatTensorProduct N M) :=
  inferInstanceAs (DGAddCommGroup (Pre N M ⧸ rel N M))

/-- The quotient map `⨁_X N(X) ⊗ M(X) →+ N ⊗_C M`. -/
def mk : Pre N M →+ CatTensorProduct N M := QuotientAddGroup.mk' _

variable {N M}

/-- The class `n ⊗ m ∈ N ⊗_C M` of `n ⊗ m ∈ N(X) ⊗ M(X)`. -/
def tmul (X : C) (n : N.obj (op X)) (m : M.obj X) : CatTensorProduct N M :=
  mk N M (ι N M X (n ⊗ₜ m))

theorem mk_ι_tmul (X : C) (n : N.obj (op X)) (m : M.obj X) :
    mk N M (ι N M X (n ⊗ₜ m)) = tmul X n m := rfl

theorem mk_surjective : Function.Surjective (mk N M) :=
  QuotientAddGroup.mk'_surjective _

theorem mk_eq_zero_iff {x : Pre N M} : mk N M x = 0 ↔ x ∈ rel N M :=
  QuotientAddGroup.eq_zero_iff x

/-- The balancing relation `(n • f) ⊗ m = n ⊗ (f • m)`. -/
theorem ract_tmul {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X) :
    tmul X (n <• f) m = tmul Y n (f • m) := by
  rw [tmul, tmul, ← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  exact relElem_mem_rel f n m

theorem tmul_add (X : C) (n : N.obj (op X)) (m m' : M.obj X) :
    tmul X n (m + m') = tmul X n m + tmul X n m' := by
  rw [tmul, TensorProduct.tmul_add, map_add, map_add]; rfl

theorem add_tmul (X : C) (n n' : N.obj (op X)) (m : M.obj X) :
    tmul X (n + n') m = tmul X n m + tmul X n' m := by
  rw [tmul, TensorProduct.add_tmul, map_add, map_add]; rfl

@[simp]
theorem tmul_zero (X : C) (n : N.obj (op X)) : tmul X n (0 : M.obj X) = 0 := by
  rw [tmul, TensorProduct.tmul_zero, map_zero, map_zero]

@[simp]
theorem zero_tmul (X : C) (m : M.obj X) : tmul X (0 : N.obj (op X)) m = 0 := by
  rw [tmul, TensorProduct.zero_tmul, map_zero, map_zero]

theorem tmul_neg (X : C) (n : N.obj (op X)) (m : M.obj X) :
    tmul X n (-m) = -tmul X n m := by
  rw [tmul, TensorProduct.tmul_neg, map_neg, map_neg]; rfl

theorem neg_tmul (X : C) (n : N.obj (op X)) (m : M.obj X) :
    tmul X (-n) m = -tmul X n m := by
  rw [tmul, TensorProduct.neg_tmul, map_neg, map_neg]; rfl

theorem tmul_zsmul (X : C) (k : ℤ) (n : N.obj (op X)) (m : M.obj X) :
    tmul X n (k • m) = k • tmul X n m := by
  rw [tmul, TensorProduct.tmul_smul, map_zsmul, map_zsmul]; rfl

theorem zsmul_tmul (X : C) (k : ℤ) (n : N.obj (op X)) (m : M.obj X) :
    tmul X (k • n) m = k • tmul X n m := by
  rw [tmul, ← TensorProduct.smul_tmul', map_zsmul, map_zsmul]; rfl

theorem tmul_units_smul (X : C) (u : ℤˣ) (n : N.obj (op X)) (m : M.obj X) :
    tmul X n (u • m) = u • tmul X n m := by
  rw [Units.smul_def, Units.smul_def, tmul_zsmul]

theorem units_smul_tmul (X : C) (u : ℤˣ) (n : N.obj (op X)) (m : M.obj X) :
    tmul X (u • n) m = u • tmul X n m := by
  rw [Units.smul_def, Units.smul_def, zsmul_tmul]

variable (N M) in
/-- The bi-additive map `(n, m) ↦ n ⊗ m` into `N ⊗_C M`, at an object `X`. -/
def tmulAddHom (X : C) : N.obj (op X) →+ M.obj X →+ CatTensorProduct N M :=
  AddMonoidHom.compHom ((mk N M).comp (ι N M X)) |>.comp (DG.tmulAddHom _ _)

@[simp]
theorem tmulAddHom_apply (X : C) (n : N.obj (op X)) (m : M.obj X) :
    tmulAddHom N M X n m = tmul X n m := rfl

/-- Induction principle for `N ⊗_C M`. -/
@[elab_as_elim]
theorem induction_on {P : CatTensorProduct N M → Prop} (x : CatTensorProduct N M)
    (zero : P 0) (tmul : ∀ (X : C) (n : N.obj (op X)) (m : M.obj X), P (tmul X n m))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  obtain ⟨x, rfl⟩ := mk_surjective x
  induction x using pre_induction_on with
  | zero => simpa using zero
  | tmul X n m => exact tmul X n m
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

/-- Two additive maps out of `N ⊗_C M` agreeing on the tensors `n ⊗ m` are equal. -/
@[ext]
theorem addHom_ext {P : Type*} [AddCommGroup P] {f g : CatTensorProduct N M →+ P}
    (h : ∀ (X : C) (n : N.obj (op X)) (m : M.obj X), f (tmul X n m) = g (tmul X n m)) :
    f = g :=
  AddMonoidHom.ext fun x => induction_on (P := fun x => f x = g x) x (by simp) h
    (fun x y (hx : f x = g x) (hy : f y = g y) => by
      show f (x + y) = g (x + y); rw [map_add, map_add, hx, hy])

/-! ### The universal property -/

section Lift

variable {P : Type*} [AddCommGroup P]

/-- A family of bi-additive maps `φ X : N(X) →+ M(X) →+ P` is *balanced* if
`φ X (n • f) m = φ Y n (f • m)` for all `f : X ⟶ Y`. -/
def Balanced (φ : ∀ X : C, N.obj (op X) →+ M.obj X →+ P) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) (m : M.obj X), φ X (n <• f) m = φ Y n (f • m)

open scoped Classical in
/-- The additive map `N ⊗_C M →+ P` induced by a balanced family of bi-additive maps
`φ X : N(X) →+ M(X) →+ P`, `n ⊗ m ↦ φ X n m`. -/
def lift (φ : ∀ X : C, N.obj (op X) →+ M.obj X →+ P) (hφ : Balanced φ) :
    CatTensorProduct N M →+ P :=
  QuotientAddGroup.lift _
    (DirectSum.toAddMonoid fun X => TensorProduct.liftAddHom (φ X) fun r n m => by
      rw [map_zsmul, map_zsmul (φ X n)]; rfl)
    ((AddSubgroup.closure_le _).mpr fun _ ⟨X, Y, f, n, m, hx⟩ => by
      rw [← hx, SetLike.mem_coe, AddMonoidHom.mem_ker, relElem, map_sub, ι, ι,
        DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, liftAddHom_tmul, liftAddHom_tmul,
        hφ, sub_self])

@[simp]
theorem lift_tmul (φ : ∀ X : C, N.obj (op X) →+ M.obj X →+ P) (hφ : Balanced φ) (X : C)
    (n : N.obj (op X)) (m : M.obj X) : lift φ hφ (tmul X n m) = φ X n m := by
  classical
  change DirectSum.toAddMonoid (fun X => TensorProduct.liftAddHom (φ X) _)
    (DirectSum.of (Summand N M) X (n ⊗ₜ m)) = _
  rw [DirectSum.toAddMonoid_of, liftAddHom_tmul]

/-- The universal property: an additive map out of `N ⊗_C M` is determined by its values on the
tensors `n ⊗ m`. -/
theorem lift_unique (φ : ∀ X : C, N.obj (op X) →+ M.obj X →+ P) (hφ : Balanced φ)
    (g : CatTensorProduct N M →+ P) (hg : ∀ X n m, g (tmul X n m) = φ X n m) :
    g = lift φ hφ :=
  addHom_ext fun X n m => by rw [hg, lift_tmul]

/-- The family `(n, m) ↦ n ⊗ m` is balanced. -/
theorem balanced_tmulAddHom : Balanced (tmulAddHom N M) :=
  fun f n m => ract_tmul f n m

@[simp]
theorem lift_tmulAddHom : lift (tmulAddHom N M) balanced_tmulAddHom = AddMonoidHom.id _ :=
  (lift_unique _ _ _ fun _ _ _ => rfl).symm

end Lift

/-! ### The dg structure -/

theorem mem_grading_iff {k : ℤ} {y : CatTensorProduct N M} :
    y ∈ grading k ↔ ∃ x ∈ grading (M := Pre N M) k, mk N M x = y :=
  Iff.rfl

theorem mk_mem_grading {k : ℤ} {x : Pre N M} (hx : x ∈ grading k) : mk N M x ∈ grading k :=
  ⟨x, hx, rfl⟩

@[simp]
theorem d_mk (x : Pre N M) : d (mk N M x) = mk N M (d x) := rfl

/-- The tensor of homogeneous elements of degrees `i` and `j` has degree `i + j`. -/
theorem tmul_mem_grading {X : C} {i j : ℤ} {n : N.obj (op X)} (hn : n ∈ grading i)
    {m : M.obj X} (hm : m ∈ grading j) : tmul X n m ∈ grading (i + j) :=
  mk_mem_grading (ι_mem_grading (DG.tmul_mem_grading hn hm))

/-- The differential of `N ⊗_C M`: `d (n ⊗ m) = d n ⊗ m + (-1)^{|n|} n ⊗ d m`. -/
theorem d_tmul_of_mem (X : C) {i : ℤ} {n : N.obj (op X)} (hn : n ∈ grading i) (m : M.obj X) :
    d (tmul X n m) = tmul X (d n) m + koszulSign i • tmul X n (d m) := by
  rw [tmul, d_mk, d_ι, DG.d_tmul_of_mem hn, map_add, map_add, map_units_zsmul,
    map_units_zsmul]
  rfl

/-- Induction on the homogeneous elements of `N ⊗_C M` of degree `k`: they are generated by the
`n ⊗ m` with `n`, `m` homogeneous of degrees adding up to `k`. -/
theorem induction_on_mem_grading {k : ℤ} {P : CatTensorProduct N M → Prop} (zero : P 0)
    (tmul : ∀ (X : C) {i j : ℤ} {n : N.obj (op X)} {m : M.obj X}, n ∈ grading i →
      m ∈ grading j → i + j = k → P (tmul X n m))
    (add : ∀ x y, P x → P y → P (x + y)) (neg : ∀ x, P x → P (-x))
    {y : CatTensorProduct N M} (hy : y ∈ grading k) : P y := by
  classical
  obtain ⟨x, hx, rfl⟩ := hy
  have key : ∀ (X : C) (z : Summand N M X), z ∈ grading k → P (mk N M (ι N M X z)) := by
    intro X z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨i, j, h, n, hn, m, hm, rfl⟩ := hz
      exact tmul X hn hm h
    | one => simpa using zero
    | mul z z' _ _ hz hz' => rw [map_add, map_add]; exact add _ _ hz hz'
    | inv z _ hz => rw [map_neg, map_neg]; exact neg _ hz
  rw [← DirectSum.sum_support_of x, map_sum]
  refine Finset.sum_induction _ P (fun a b ha hb => add a b ha hb) (by simpa using zero) ?_
  intro X _
  exact key X (x X) (hx X)

section Lift

variable {P : Type*} [AddCommGroup P] [DGAddCommGroup P]

/-- If a balanced family of bi-additive maps sends `N(X)ⁱ × M(X)ʲ` to `Pⁱ⁺ʲ⁺ˢ`, the induced map
has degree `s`. -/
theorem lift_mem_add (φ : ∀ X : C, N.obj (op X) →+ M.obj X →+ P) (hφ : Balanced φ) (s : ℤ)
    (hdeg : ∀ (X : C) {i j : ℤ} {n : N.obj (op X)} {m : M.obj X}, n ∈ grading i →
      m ∈ grading j → φ X n m ∈ grading (i + j + s))
    {k : ℤ} {y : CatTensorProduct N M} (hy : y ∈ grading k) :
    lift φ hφ y ∈ grading (k + s) :=
  induction_on_mem_grading (P := fun y => lift φ hφ y ∈ grading (k + s))
    (by show lift φ hφ 0 ∈ _; rw [map_zero]; exact zero_mem _)
    (fun X _ _ _ _ hn hm h => by
      show lift φ hφ (tmul X _ _) ∈ _
      rw [lift_tmul, ← h]; exact hdeg X hn hm)
    (fun x y hx hy => by show lift φ hφ (x + y) ∈ _; rw [map_add]; exact add_mem hx hy)
    (fun x hx => by show lift φ hφ (-x) ∈ _; rw [map_neg]; exact neg_mem hx) hy

/-- If a balanced family of bi-additive maps sends `N(X)ⁱ × M(X)ʲ` to `Pⁱ⁺ʲ`, the induced map has
degree `0`. -/
theorem lift_mem (φ : ∀ X : C, N.obj (op X) →+ M.obj X →+ P) (hφ : Balanced φ)
    (hdeg : ∀ (X : C) {i j : ℤ} {n : N.obj (op X)} {m : M.obj X}, n ∈ grading i →
      m ∈ grading j → φ X n m ∈ grading (i + j))
    {k : ℤ} {y : CatTensorProduct N M} (hy : y ∈ grading k) : lift φ hφ y ∈ grading k := by
  simpa using lift_mem_add φ hφ 0 (fun X _ _ _ _ hn hm => by simpa using hdeg X hn hm) hy

/-- If a balanced family satisfies the Leibniz rule
`d (φ X n m) = φ X (d n) m + (-1)^{|n|} φ X n (d m)`, the induced map commutes with `d`. -/
theorem lift_d (φ : ∀ X : C, N.obj (op X) →+ M.obj X →+ P) (hφ : Balanced φ)
    (hd : ∀ (X : C) {i : ℤ} {n : N.obj (op X)}, n ∈ grading i → ∀ m : M.obj X,
      d (φ X n m) = φ X (d n) m + koszulSign i • φ X n (d m))
    (y : CatTensorProduct N M) : lift φ hφ (d y) = d (lift φ hφ y) := by
  induction y using induction_on with
  | zero => simp
  | tmul X n m =>
    induction n using DG.induction_on with
    | h_zero => simp
    | h_homogeneous n =>
      rw [d_tmul_of_mem X n.2, map_add, map_units_zsmul, lift_tmul, lift_tmul, lift_tmul,
        hd X n.2]
    | h_add n n' hn hn' => rw [add_tmul, d_add, map_add, hn, hn', map_add, d_add]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

end Lift

/-! ### Functoriality -/

section Map

variable {N' N'' : CatModule.{w₁} (DGOpposite C)} {M' M'' : CatModule.{w₂} C}

theorem balanced_map (φ : N ⟶ N') (ψ : M ⟶ M') :
    Balanced fun X => ((tmulAddHom N' M' X).compl₂ (ψ.app X)).comp (φ.app (op X)) :=
  fun f n m => by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.compl₂_apply,
      tmulAddHom_apply, CatModule.Hom.map_ract, CatModule.Hom.map_smul, ract_tmul]

/-- The map `φ ⊗ ψ : N ⊗_C M →+ N' ⊗_C M'` induced by morphisms of dg modules. -/
def map (φ : N ⟶ N') (ψ : M ⟶ M') : CatTensorProduct N M →+ CatTensorProduct N' M' :=
  lift _ (balanced_map φ ψ)

@[simp]
theorem map_tmul (φ : N ⟶ N') (ψ : M ⟶ M') (X : C) (n : N.obj (op X)) (m : M.obj X) :
    map φ ψ (tmul X n m) = tmul X (φ.app (op X) n) (ψ.app X m) :=
  lift_tmul _ (balanced_map φ ψ) X n m

@[simp]
theorem map_id : map (𝟙 N) (𝟙 M) = AddMonoidHom.id _ :=
  addHom_ext fun X n m => by simp

theorem map_comp (φ : N ⟶ N') (φ' : N' ⟶ N'') (ψ : M ⟶ M') (ψ' : M' ⟶ M'') :
    map (φ ≫ φ') (ψ ≫ ψ') = (map φ' ψ').comp (map φ ψ) :=
  addHom_ext fun X n m => by simp

theorem map_comp_apply (φ : N ⟶ N') (φ' : N' ⟶ N'') (ψ : M ⟶ M') (ψ' : M' ⟶ M'')
    (x : CatTensorProduct N M) : map (φ ≫ φ') (ψ ≫ ψ') x = map φ' ψ' (map φ ψ x) := by
  rw [map_comp]; rfl

/-- The map induced by morphisms of dg modules has degree `0`. -/
theorem map_mem (φ : N ⟶ N') (ψ : M ⟶ M') {k : ℤ} {y : CatTensorProduct N M}
    (hy : y ∈ grading k) : map φ ψ y ∈ grading k :=
  lift_mem _ (balanced_map φ ψ)
    (fun _ _ _ _ _ hn hm => tmul_mem_grading (φ.map_mem hn) (ψ.map_mem hm)) hy

/-- The map induced by morphisms of dg modules commutes with the differentials. -/
theorem map_d (φ : N ⟶ N') (ψ : M ⟶ M') (y : CatTensorProduct N M) :
    map φ ψ (d y) = d (map φ ψ y) :=
  lift_d _ (balanced_map φ ψ) (fun X _ _ hn m => by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.compl₂_apply,
      tmulAddHom_apply]
    rw [d_tmul_of_mem X (φ.map_mem hn), CatModule.Hom.map_d, CatModule.Hom.map_d]) y

/-- The isomorphism `N ⊗_C M ≅ N' ⊗_C M'` of dg abelian groups induced by isomorphisms of dg
modules. -/
def congr (e : N ≅ N') (e' : M ≅ M') : DGAddEquiv (CatTensorProduct N M) (CatTensorProduct N' M') :=
  DGAddEquiv.ofAddMonoidHom (map e.hom e'.hom) (map e.inv e'.inv)
    (fun x => by rw [← map_comp_apply, e.hom_inv_id, e'.hom_inv_id, map_id]; rfl)
    (fun x => by rw [← map_comp_apply, e.inv_hom_id, e'.inv_hom_id, map_id]; rfl)
    (fun hy => map_mem _ _ hy) (map_d _ _)

@[simp]
theorem congr_tmul (e : N ≅ N') (e' : M ≅ M') (X : C) (n : N.obj (op X)) (m : M.obj X) :
    congr e e' (tmul X n m) = tmul X (e.hom.app (op X) n) (e'.hom.app X m) :=
  map_tmul _ _ X n m

end Map

/-! ### The co-Yoneda isomorphisms -/

section CoYoneda

theorem balanced_lid (X : C) :
    Balanced (N := representable (op X)) (M := M) fun Y => M.act (X := Y) (Y := X) :=
  fun f h m => by
    change M.act (homUnop (h <• f)) m = M.act (homUnop h) (f • m)
    rw [representable_op_ract]
    exact CatModule.comp_smul (M := M) f (homUnop h) m

variable (M) in
/-- The action map `C(-, X) ⊗_C M →+ M(X)`, `h ⊗ m ↦ h • m`. -/
def lidHom (X : C) : CatTensorProduct (representable (op X)) M →+ M.obj X :=
  lift _ (balanced_lid X)

@[simp]
theorem lidHom_tmul (X Y : C) (h : Y ⟶ X) (m : M.obj Y) :
    lidHom M X (tmul Y (homOp h) m) = h • m :=
  lift_tmul _ (balanced_lid X) Y _ m

variable (M) in
/-- The co-Yoneda isomorphism `C(-, X) ⊗_C M ≅ M(X)`, `h ⊗ m ↦ h • m`, of dg abelian groups; its
inverse is `m ↦ 𝟙 X ⊗ m`. -/
def lid (X : C) : DGAddEquiv (CatTensorProduct (representable (op X)) M) (M.obj X) :=
  DGAddEquiv.ofAddMonoidHom (lidHom M X)
    (tmulAddHom (representable (op X)) M X (homOp (𝟙 X)))
    (fun x => by
      induction x using induction_on with
      | zero => simp
      | tmul Y h m =>
        rw [← homOp_homUnop h, lidHom_tmul, tmulAddHom_apply, ← ract_tmul,
          representable_op_ract]
        exact congrArg (fun h => tmul Y h m) (Category.comp_id _)
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun m => by
      rw [tmulAddHom_apply, lidHom_tmul]
      exact CatModule.id_smul (M := M) m)
    (fun hy => lift_mem _ (balanced_lid X)
      (fun _ _ _ _ _ hh hm => CatModule.smul_mem_grading (M := M) hh hm) hy)
    (lift_d _ (balanced_lid X) fun _ _ _ hh m => CatModule.d_smul (M := M) hh m)

@[simp]
theorem lid_tmul (X Y : C) (h : Y ⟶ X) (m : M.obj Y) :
    lid M X (tmul Y (homOp h) m) = h • m :=
  lidHom_tmul X Y h m

@[simp]
theorem lid_symm_apply (X : C) (m : M.obj X) :
    (lid M X).symm m = tmul X (homOp (𝟙 X)) m :=
  rfl

/-- The co-Yoneda isomorphism is natural in the module. -/
theorem lid_naturality {M' : CatModule.{w₂} C} (ψ : M ⟶ M') (X : C)
    (x : CatTensorProduct (representable (op X)) M) :
    lid M' X (map (𝟙 _) ψ x) = ψ.app X (lid M X x) := by
  induction x using induction_on with
  | zero => simp
  | tmul Y h m =>
    rw [← homOp_homUnop h, map_tmul, CatModule.id_app, lid_tmul, lid_tmul]
    exact (ψ.map_smul _ m).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem balanced_rid (X : C) :
    Balanced (M := representable X) fun Y => (N.ract (X := X) (Y := Y)).flip :=
  fun f n h => by
    change (n <• f) <• h = n <• (h ≫ f)
    rw [ract_comp]

variable (N) in
/-- The action map `N ⊗_C C(X, -) →+ N(X)`, `n ⊗ h ↦ n • h`. -/
def ridHom (X : C) : CatTensorProduct N (representable X) →+ N.obj (op X) :=
  lift _ (balanced_rid X)

@[simp]
theorem ridHom_tmul (X Y : C) (n : N.obj (op Y)) (h : X ⟶ Y) :
    ridHom N X (tmul Y n h) = n <• h :=
  lift_tmul _ (balanced_rid X) Y n h

variable (N) in
/-- The co-Yoneda isomorphism `N ⊗_C C(X, -) ≅ N(X)`, `n ⊗ h ↦ n • h`, of dg abelian groups;
its inverse is `n ↦ n ⊗ 𝟙 X`. -/
def rid (X : C) : DGAddEquiv (CatTensorProduct N (representable X)) (N.obj (op X)) :=
  DGAddEquiv.ofAddMonoidHom (ridHom N X)
    ((tmulAddHom N (representable X) X).flip (𝟙 X))
    (fun x => by
      induction x using induction_on with
      | zero => simp
      | tmul Y n h =>
        rw [ridHom_tmul, AddMonoidHom.flip_apply, tmulAddHom_apply, ract_tmul]
        exact congrArg (fun h => tmul Y n h) (Category.id_comp (h : X ⟶ Y))
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun n => by
      rw [AddMonoidHom.flip_apply, tmulAddHom_apply, ridHom_tmul]
      exact ract_id n)
    (fun hy => lift_mem _ (balanced_rid X) (fun _ _ _ _ _ hn hh => by
      rw [AddMonoidHom.flip_apply]; exact ract_mem_grading hn hh) hy)
    (lift_d _ (balanced_rid X) fun _ _ _ hn h => by
      simp only [AddMonoidHom.flip_apply]
      exact d_ract hn h)

@[simp]
theorem rid_tmul (X Y : C) (n : N.obj (op Y)) (h : X ⟶ Y) :
    rid N X (tmul Y n h) = n <• h :=
  ridHom_tmul X Y n h

@[simp]
theorem rid_symm_apply (X : C) (n : N.obj (op X)) :
    (rid N X).symm n = tmul X (M := representable X) n (𝟙 X) :=
  rfl

/-- The co-Yoneda isomorphism `N ⊗_C C(X, -) ≅ N(X)` is natural in the module. -/
theorem rid_naturality {N' : CatModule.{w₁} (DGOpposite C)} (φ : N ⟶ N') (X : C)
    (x : CatTensorProduct N (representable X)) :
    rid N' X (map φ (𝟙 _) x) = φ.app (op X) (rid N X x) := by
  induction x using induction_on with
  | zero => simp
  | tmul Y n h =>
    rw [map_tmul, rid_tmul, rid_tmul]
    exact (CatModule.Hom.map_ract φ h n).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end CoYoneda

end CatTensorProduct

end DG
