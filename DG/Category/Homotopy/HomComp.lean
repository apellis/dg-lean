import DG.Category.Homotopy.Hom

/-!
# Composition with cochains on Hom complexes

Let `C` be a category with dg Hom groups and `P`, `N` dg modules over `C`. A cochain
`z : Cochain N N' k` acts on the Hom complex `HOM_C(P, N)` by postcomposition, and a cochain
`c : Cochain P' P i` acts on `HOM_C(P, N)` by precomposition with the Koszul sign of the exchange
of `c` and the element of the Hom complex:

* `DG.CatModule.HOM.postcompCochain z : HOM P N →+ HOM P N'`, `w ↦ z ∘ w`, of degree `k`, with the
  Leibniz rule `d (z ∘ w) = δ z ∘ w + (-1)^k • z ∘ d w` (`DG.CatModule.HOM.d_postcompCochain`);
* `DG.CatModule.HOM.precompCochain c : HOM P N →+ HOM P' N`, `w ↦ (-1)^{|c||w|} • w ∘ c`, of degree
  `i`, with the Leibniz rule `d (w ∘ c) = δ c • w + (-1)^i • d w ∘ c`
  (`DG.CatModule.HOM.d_precompCochain`).

Both are associative and commute up to the Koszul sign
(`DG.CatModule.HOM.postcompCochain_precompCochain`).
The evaluation `DG.CatModule.HOM.eval X : HOM P N →+ P.obj X →+ N.obj X` sums the components of
the homogeneous parts at `X`. These operations are used to make `HOM` functorial in both
variables, for instance to define the Hom functor of a dg bimodule.
-/

open CategoryTheory DirectSum

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

namespace HOM

private theorem ks_eq {m n : ℤ} (k : ℤ) (h : m - n = 2 * k) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr ⟨k, by omega⟩

private theorem map_units {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (u : ℤˣ)
    (x : A) : f (u • x) = u • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

variable {P P' P'' N N' N'' : CatModule.{w} C}

/-! ### Postcomposition -/

section Postcomp

variable {k : ℤ}

/-- Postcomposition with a cochain `z` of degree `k`, as an additive map on the degree-`j`
cochains. -/
def postcompCochainAddHom (z : Cochain N N' k) (j : ℤ) : Cochain P N j →+ Cochain P N' (j + k) where
  toFun w := z.comp w rfl
  map_zero' := Cochain.comp_zero _ _
  map_add' _ _ := Cochain.comp_add _ _ _ _

/-- Postcomposition `w ↦ z ∘ w` with a cochain `z` of degree `k`, as an additive map
`HOM P N →+ HOM P N'` of degree `k`. -/
def postcompCochain (z : Cochain N N' k) : HOM P N →+ HOM P N' :=
  DirectSum.toAddMonoid fun j =>
    (DirectSum.of (fun n => Cochain P N' n) (j + k)).comp (postcompCochainAddHom z j)

@[simp]
theorem postcompCochain_of (z : Cochain N N' k) (j : ℤ) (w : Cochain P N j) :
    postcompCochain z (DirectSum.of (fun n => Cochain P N n) j w) =
      DirectSum.of (fun n => Cochain P N' n) (j + k) (z.comp w rfl) := by
  simp [postcompCochain, postcompCochainAddHom]

theorem postcompCochain_mem (z : Cochain N N' k) {j : ℤ} {w : HOM P N} (hw : w ∈ grading j) :
    postcompCochain z w ∈ grading (j + k) := by
  obtain ⟨w, rfl⟩ := hw
  rw [postcompCochain_of]
  exact of_mem_summand _ _

theorem postcompCochain_add (z z' : Cochain N N' k) (w : HOM P N) :
    postcompCochain (z + z') w = postcompCochain z w + postcompCochain z' w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w => simp [Cochain.add_comp]
  | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw']; abel

theorem postcompCochain_neg (z : Cochain N N' k) (w : HOM P N) :
    postcompCochain (-z) w = -postcompCochain z w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w => simp [Cochain.neg_comp]
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', neg_add]

theorem postcompCochain_sub (z z' : Cochain N N' k) (w : HOM P N) :
    postcompCochain (z - z') w = postcompCochain z w - postcompCochain z' w := by
  rw [sub_eq_add_neg, postcompCochain_add, postcompCochain_neg, ← sub_eq_add_neg]

@[simp]
theorem postcompCochain_zero (w : HOM P N) : postcompCochain (0 : Cochain N N' k) w = 0 := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w => simp
  | add w w' hw hw' => rw [map_add, hw, hw', add_zero]

theorem postcompCochain_units_smul (u : ℤˣ) (z : Cochain N N' k) (w : HOM P N) :
    postcompCochain (u • z) w = u • postcompCochain z w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w => rw [postcompCochain_of, postcompCochain_of, Cochain.units_smul_comp, of_units_smul]
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', _root_.smul_add]

@[simp]
theorem postcompCochain_id (w : HOM P N) : postcompCochain (Cochain.id N) w = w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w => rw [postcompCochain_of]; exact of_congr (add_zero j) fun _ _ => rfl
  | add w w' hw hw' => rw [map_add, hw, hw']

/-- Postcomposition with cochains of equal degrees which agree objectwise. -/
theorem postcompCochain_congr {k' : ℤ} (h : k = k') {z : Cochain N N' k} {z' : Cochain N N' k'}
    (hz : ∀ X x, z.app X x = z'.app X x) (w : HOM P N) :
    postcompCochain z w = postcompCochain z' w := by
  subst h
  rw [Cochain.ext hz]

/-- Postcomposition with a cochain of degree `0` which is the identity objectwise. -/
theorem postcompCochain_eq_self (h : k = 0) {z : Cochain N N k} (hz : ∀ X x, z.app X x = x)
    (w : HOM P N) : postcompCochain z w = w :=
  (postcompCochain_congr h (z' := Cochain.id N) hz w).trans (postcompCochain_id w)

/-- Postcomposition with a cochain which vanishes objectwise. -/
theorem postcompCochain_eq_zero {z : Cochain N N' k} (hz : ∀ X x, z.app X x = 0) (w : HOM P N) :
    postcompCochain z w = 0 :=
  (postcompCochain_congr rfl (z' := 0) hz w).trans (postcompCochain_zero w)

/-- Postcomposition is associative. -/
theorem postcompCochain_postcompCochain {k' : ℤ} (z : Cochain N N' k) (z' : Cochain N' N'' k')
    (w : HOM P N) :
    postcompCochain z' (postcompCochain z w) = postcompCochain (z'.comp z rfl) w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w =>
    simp only [postcompCochain_of]
    exact of_congr (add_assoc _ _ _) fun _ _ => rfl
  | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw']

/-- The Leibniz rule for postcomposition: `d (z ∘ w) = δ z ∘ w + (-1)^k • z ∘ d w`. -/
theorem d_postcompCochain (z : Cochain N N' k) (w : HOM P N) :
    d (postcompCochain z w) =
      postcompCochain (δ k (k + 1) z) w + koszulSign k • postcompCochain z (d w) := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w =>
    rw [postcompCochain_of, d_of, d_of, postcompCochain_of, postcompCochain_of,
      δ_comp w z rfl (j + 1) (k + 1) (j + k + 1) rfl rfl rfl, map_add, ← of_units_smul]
    congr 1
    · exact of_congr (by ring) fun _ _ => rfl
    · exact of_congr (by ring) fun _ _ => rfl
  | add w w' hw hw' =>
    rw [map_add, map_add, hw, hw', map_add, map_add, map_add, _root_.smul_add]
    abel

end Postcomp

/-! ### Precomposition -/

section Precomp

variable {i : ℤ}

/-- Precomposition with a cochain `c` of degree `i`, with the Koszul sign, on the degree-`j`
cochains: `w ↦ (-1)^{i j} • w ∘ c`. -/
def precompCochainAddHom (c : Cochain P' P i) (j : ℤ) : Cochain P N j →+ Cochain P' N (i + j) where
  toFun w := koszulSign (i * j) • w.comp c rfl
  map_zero' := by simp
  map_add' _ _ := by simp [_root_.smul_add]

/-- Precomposition with a cochain `c` of degree `i`, with the Koszul sign of the exchange of `c`
and `w`: `w ↦ (-1)^{|c| |w|} • w ∘ c`, as an additive map `HOM P N →+ HOM P' N` of degree
`i`. -/
def precompCochain (c : Cochain P' P i) : HOM P N →+ HOM P' N :=
  DirectSum.toAddMonoid fun j =>
    (DirectSum.of (fun n => Cochain P' N n) (i + j)).comp (precompCochainAddHom c j)

@[simp]
theorem precompCochain_of (c : Cochain P' P i) (j : ℤ) (w : Cochain P N j) :
    precompCochain c (DirectSum.of (fun n => Cochain P N n) j w) =
      koszulSign (i * j) • DirectSum.of (fun n => Cochain P' N n) (i + j) (w.comp c rfl) := by
  simp [precompCochain, precompCochainAddHom]

theorem precompCochain_mem (c : Cochain P' P i) {j : ℤ} {w : HOM P N} (hw : w ∈ grading j) :
    precompCochain c w ∈ grading (i + j) := by
  obtain ⟨w, rfl⟩ := hw
  rw [precompCochain_of]
  exact units_smul_mem_grading _ (of_mem_summand _ _)

theorem precompCochain_add (c c' : Cochain P' P i) (w : HOM P N) :
    precompCochain (c + c') w = precompCochain c w + precompCochain c' w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w => simp
  | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw']; abel

theorem precompCochain_units_smul (u : ℤˣ) (c : Cochain P' P i) (w : HOM P N) :
    precompCochain (u • c) w = u • precompCochain c w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w =>
    rw [precompCochain_of, precompCochain_of, Cochain.comp_units_smul, of_units_smul, smul_comm]
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', _root_.smul_add]

@[simp]
theorem precompCochain_zero (w : HOM P N) : precompCochain (0 : Cochain P' P i) w = 0 := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w => simp
  | add w w' hw hw' => rw [map_add, hw, hw', add_zero]

@[simp]
theorem precompCochain_id (w : HOM P N) : precompCochain (Cochain.id P) w = w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w =>
    rw [precompCochain_of, zero_mul, koszulSign_zero, one_smul]
    exact of_congr (zero_add j) fun _ _ => rfl
  | add w w' hw hw' => rw [map_add, hw, hw']

/-- Precomposition is associative up to the Koszul sign:
`(w ∘ c') ∘ c = (-1)^{|c| |c'|} • w ∘ (c' ∘ c)` with the signs of `precompCochain`. -/
theorem precompCochain_precompCochain {i' : ℤ} (c : Cochain P'' P' i) (c' : Cochain P' P i')
    (w : HOM P N) :
    precompCochain c (precompCochain c' w) =
      koszulSign (i * i') • precompCochain (c'.comp c rfl) w := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w =>
    rw [precompCochain_of, map_units _, precompCochain_of, precompCochain_of, smul_smul,
      ← koszulSign_add, smul_smul, ← koszulSign_add]
    congr 1
    · exact congrArg koszulSign (by ring)
    · exact of_congr (add_assoc _ _ _).symm fun _ _ => rfl
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, _root_.smul_add]

/-- Pre- and postcomposition commute up to the Koszul sign. -/
theorem postcompCochain_precompCochain {k : ℤ} (z : Cochain N N' k) (c : Cochain P' P i)
    (w : HOM P N) :
    postcompCochain z (precompCochain c w) =
      koszulSign (i * k) • precompCochain c (postcompCochain z w) := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w =>
    rw [precompCochain_of, map_units _, postcompCochain_of, postcompCochain_of, precompCochain_of,
      smul_smul, ← koszulSign_add]
    congr 1
    · exact ks_eq (-(i * k)) (by ring)
    · exact of_congr (add_assoc _ _ _) fun _ _ => rfl
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add, _root_.smul_add]

/-- The Leibniz rule for precomposition: `d (w ∘ c) = (δ c) • w + (-1)^i • d w ∘ c`, with the
signs of `precompCochain`. -/
theorem d_precompCochain (c : Cochain P' P i) (w : HOM P N) :
    d (precompCochain c w) =
      precompCochain (δ i (i + 1) c) w + koszulSign i • precompCochain c (d w) := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j w =>
    rw [precompCochain_of, d_units_smul, d_of, d_of, precompCochain_of, precompCochain_of,
      δ_comp c w rfl (i + 1) (j + 1) (i + j + 1) rfl rfl rfl, map_add, _root_.smul_add]
    simp only [← of_units_smul]
    rw [add_comm]
    congr 1 <;> refine of_congr (by ring) fun X x => ?_ <;>
      simp only [Cochain.units_smul_apply, Cochain.comp_apply, smul_smul, ← koszulSign_add]
    · exact congrArg (· • _) (ks_eq 0 (by ring))
    · exact congrArg (· • _) (ks_eq (-i) (by ring))
  | add w w' hw hw' =>
    rw [map_add, map_add, hw, hw', map_add, map_add, map_add, _root_.smul_add]
    abel

end Precomp

/-! ### Evaluation -/

section Eval

variable (P N) in
/-- The evaluation `HOM P N →+ P.obj X →+ N.obj X` at an object `X`: the sum of the components
at `X` of the homogeneous parts. -/
def eval (X : C) : HOM P N →+ P.obj X →+ N.obj X :=
  DirectSum.toAddMonoid fun _ =>
    { toFun := fun w => w.app X
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

@[simp]
theorem eval_of (X : C) (j : ℤ) (w : Cochain P N j) (x : P.obj X) :
    eval P N X (DirectSum.of (fun n => Cochain P N n) j w) x = w.app X x := by
  simp [eval]

theorem eval_postcompCochain {k : ℤ} (z : Cochain N N' k) (X : C) (w : HOM P N) (x : P.obj X) :
    eval P N' X (postcompCochain z w) x = z.app X (eval P N X w x) := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of _ w => simp
  | add w w' hw hw' =>
    rw [map_add, map_add, AddMonoidHom.add_apply, hw, hw', map_add, AddMonoidHom.add_apply,
      map_add]

theorem eval_d_of (X : C) {j : ℤ} (w : Cochain P N j) (x : P.obj X) :
    eval P N X (d (DirectSum.of (fun n => Cochain P N n) j w)) x =
      d (w.app X x) - koszulSign j • w.app X (d x) := by
  rw [d_of, eval_of, δ_apply _ _ rfl]

end Eval

end HOM

end CatModule

end DG
