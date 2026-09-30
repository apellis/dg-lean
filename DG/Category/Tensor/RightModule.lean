import DG.Category.Yoneda
import DG.Category.Opposite
import DG.Module.Opposite
import DG.Module.TensorProduct

/-!
# Right dg modules over a dg category

Following `docs/CONVENTIONS.md`, a right dg module over a dg category `C` is a left dg module
over the opposite dg category `DG.DGOpposite C`, i.e. an object of
`DG.CatModule (DG.DGOpposite C)`. Its value at `X : C` is `N.obj (DGOpposite.op X)`, and a
morphism `f : X ⟶ Y` of `C` acts by `homOp f • n : N.obj (op X)` for `n : N.obj (op Y)`.

Since the composition of `DGOpposite C` is twisted by the Koszul sign, this left action is not
associative in the naive sense. The associated *right action* (`DG.CatModule.ract`), written
`n • f`, is defined by the Koszul rule of `docs/CONVENTIONS.md` (the symbols `f` and `n` are
exchanged):

  `n • f = (-1)^{|f||n|} • (homOp f • n)`   for homogeneous `f` and `n`,

(the Koszul twist `DG.koszulTwist` of the left action), and it satisfies the familiar axioms of a
right dg module, without signs in the associativity:

* `n • 𝟙 X = n` and `n • (f ≫ g) = (n • g) • f` (`DG.CatModule.ract_id`, `DG.CatModule.ract_comp`),
* `(N Y)ʲ • (X ⟶ Y)ⁱ ⊆ (N X)ʲ⁺ⁱ` (`DG.CatModule.ract_mem_grading`),
* the right Leibniz rule `d (n • f) = d n • f + (-1)^{|n|} • (n • d f)` (`DG.CatModule.d_ract`).

Conversely, a family of dg abelian groups with a right action satisfying these axioms defines a
right dg module (`DG.CatModule.ofRightAction`), whose right action is the given one
(`DG.CatModule.ract_ofRightAction`). For a one-object dg category `SingleObj A` this is the
passage between right dg `A`-modules (`Module Aᵐᵒᵖ`) and left dg modules over the opposite dg
ring (`DG.Module.Opposite`).

## Main definitions and results

* `DG.CatModule.ract N : (X ⟶ Y) →+ N.obj (op Y) →+ N.obj (op X)`, with notation `n <• f` (scoped).
* `DG.CatModule.Hom.map_ract`: morphisms of right dg modules commute with the right action.
* `DG.CatModule.ofRightAction`: the right dg module attached to a right action.
* `DG.CatModule.representable_op_ract`: the representable module `C(-, X)`, i.e.
  `representable (op X)` over `DGOpposite C`, has the right action by precomposition,
  `h • f = f ≫ h`.
-/

open CategoryTheory

universe w w' v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

open DGOpposite

private theorem ks_congr {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

private theorem units_smul_apply' {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (u : ℤˣ)
    (f : M →+ M') (m : M) : (u • f) m = u • f m := rfl

section RightAction

variable (N : CatModule.{w} (DGOpposite C))

/-- The right action of the morphisms of `C` on a right dg module `N` over `C` (a left dg module
over `DGOpposite C`): the Koszul twist of the left action, `n • f = (-1)^{|f||n|} • (f • n)`
on homogeneous elements. -/
def ract {X Y : C} : (X ⟶ Y) →+ N.obj (op Y) →+ N.obj (op X) :=
  koszulTwist (N.act (X := op Y) (Y := op X))

/-- The right action `n <• f = N.ract f n` of `f : X ⟶ Y` on `n : N.obj (op Y)`. -/
scoped notation:73 n:73 " <• " f:74 => DG.CatModule.ract _ f n

variable {N}

theorem homOp_units_smul {X Y : C} (u : ℤˣ) (f : X ⟶ Y) : homOp (u • f) = u • homOp f := rfl

theorem ract_apply {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) : N.ract f n = n <• f := rfl

/-- The right action on homogeneous elements: `n • f = (-1)^{|f||n|} • (f • n)`. -/
theorem ract_of_mem {X Y : C} {i j : ℤ} {f : X ⟶ Y} {n : N.obj (op Y)} (hf : f ∈ grading i)
    (hn : n ∈ grading j) : n <• f = koszulSign (i * j) • (homOp f • n) :=
  koszulTwist_apply_of_mem (N.act (X := op Y) (Y := op X)) (A := X ⟶ Y) hf hn

/-- The left action of `DGOpposite C` in terms of the right action:
`f • n = (-1)^{|f||n|} • (n • f)`. -/
theorem homOp_smul_of_mem {X Y : C} {i j : ℤ} {f : X ⟶ Y} {n : N.obj (op Y)}
    (hf : f ∈ grading i) (hn : n ∈ grading j) : homOp f • n = koszulSign (i * j) • (n <• f) := by
  rw [ract_of_mem hf hn, smul_smul, Int.units_mul_self, one_smul]

/-- The left action of `DGOpposite C` in terms of the right action, for a morphism of
`DGOpposite C`: `f • n = (-1)^{|f||n|} • (n <• f)`. -/
theorem smul_eq_ract_of_mem {X Y : DGOpposite C} {i j : ℤ} {f : X ⟶ Y} {n : N.obj X}
    (hf : f ∈ grading i) (hn : n ∈ grading j) :
    f • n = koszulSign (i * j) • ((n : N.obj (op X.unop)) <• homUnop f) :=
  homOp_smul_of_mem (X := Y.unop) (Y := X.unop) hf hn

@[simp]
theorem add_ract {X Y : C} (f : X ⟶ Y) (n n' : N.obj (op Y)) : (n + n') <• f = n <• f + n' <• f :=
  map_add (N.ract f) n n'

@[simp]
theorem ract_add {X Y : C} (f g : X ⟶ Y) (n : N.obj (op Y)) : n <• (f + g) = n <• f + n <• g := by
  rw [map_add, AddMonoidHom.add_apply]

@[simp]
theorem zero_ract {X Y : C} (f : X ⟶ Y) : (0 : N.obj (op Y)) <• f = 0 :=
  map_zero (N.ract f)

@[simp]
theorem ract_zero {X Y : C} (n : N.obj (op Y)) : n <• (0 : X ⟶ Y) = 0 := by
  rw [map_zero, AddMonoidHom.zero_apply]

@[simp]
theorem neg_ract {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) : (-n) <• f = -(n <• f) :=
  map_neg (N.ract f) n

@[simp]
theorem ract_neg {X Y : C} (f : X ⟶ Y) (n : N.obj (op Y)) : n <• (-f) = -(n <• f) := by
  rw [map_neg, AddMonoidHom.neg_apply]

@[simp]
theorem sub_ract {X Y : C} (f : X ⟶ Y) (n n' : N.obj (op Y)) : (n - n') <• f = n <• f - n' <• f :=
  map_sub (N.ract f) n n'

@[simp]
theorem ract_sub {X Y : C} (f g : X ⟶ Y) (n : N.obj (op Y)) : n <• (f - g) = n <• f - n <• g := by
  rw [sub_eq_add_neg, ract_add, ract_neg, sub_eq_add_neg]

@[simp]
theorem units_smul_ract {X Y : C} (u : ℤˣ) (f : X ⟶ Y) (n : N.obj (op Y)) :
    (u • n) <• f = u • (n <• f) :=
  map_units_zsmul (N.ract f) u n

@[simp]
theorem ract_units_smul {X Y : C} (u : ℤˣ) (f : X ⟶ Y) (n : N.obj (op Y)) :
    n <• (u • f) = u • (n <• f) := by
  rw [map_units_zsmul, Units.smul_def, Units.smul_def, AddMonoidHom.smul_apply]

@[simp]
theorem zsmul_ract {X Y : C} (k : ℤ) (f : X ⟶ Y) (n : N.obj (op Y)) :
    (k • n) <• f = k • (n <• f) :=
  map_zsmul (N.ract f) k n

@[simp]
theorem ract_zsmul {X Y : C} (k : ℤ) (f : X ⟶ Y) (n : N.obj (op Y)) :
    n <• (k • f) = k • (n <• f) := by
  rw [map_zsmul, AddMonoidHom.smul_apply]

/-- The right action is graded: `(N Y)ʲ • (X ⟶ Y)ⁱ ⊆ (N X)ʲ⁺ⁱ`. -/
theorem ract_mem_grading {X Y : C} {i j : ℤ} {f : X ⟶ Y} {n : N.obj (op Y)}
    (hn : n ∈ grading j) (hf : f ∈ grading i) : n <• f ∈ grading (j + i) := by
  rw [ract_of_mem hf hn, Units.smul_def, add_comm]
  exact zsmul_mem (smul_mem_grading (M := N) (f := homOp f) hf hn) _

@[simp]
theorem ract_id {X : C} (n : N.obj (op X)) : n <• 𝟙 X = n := by
  induction n using DG.induction_on with
  | h_zero => exact zero_ract _
  | h_homogeneous n =>
    rw [ract_of_mem (id_mem_grading X) n.2, zero_mul, koszulSign_zero, one_smul]
    exact id_smul (M := N) (X := op X) (n : N.obj (op X))
  | h_add n n' hn hn' => rw [add_ract, hn, hn']

/-- The right action is associative: `n • (f ≫ g) = (n • g) • f`. -/
theorem ract_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : N.obj (op Z)) :
    n <• (f ≫ g) = (n <• g) <• f := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_add f f' hf hf' => rw [Preadditive.add_comp, ract_add, ract_add, hf, hf']
  | h_homogeneous f =>
    rename_i i
    induction g using DG.induction_on with
    | h_zero => simp
    | h_add g g' hg hg' => rw [Preadditive.comp_add, ract_add, ract_add, add_ract, hg, hg']
    | h_homogeneous g =>
      rename_i k
      induction n using DG.induction_on with
      | h_zero => simp
      | h_add n n' hn hn' => rw [add_ract, add_ract, add_ract, hn, hn']
      | h_homogeneous n =>
        rename_i j
        have hfg : homOp ((f : X ⟶ Y) ≫ (g : Y ⟶ Z)) • (n : N.obj (op Z)) =
            koszulSign (k * i) • (homOp (f : X ⟶ Y) • homOp (g : Y ⟶ Z) • (n : N.obj (op Z))) := by
          have := homUnop_comp_of_mem (X := op Z) (Y := op Y) (Z := op X)
            (f := homOp (g : Y ⟶ Z)) (g := homOp (f : X ⟶ Y)) g.2 f.2
          rw [homUnop_homOp, homUnop_homOp] at this
          rw [← comp_smul, ← homOp_homUnop (homOp (g : Y ⟶ Z) ≫ homOp (f : X ⟶ Y)), this]
          rw [homOp_units_smul, units_smul_smul (M := N), smul_smul, Int.units_mul_self,
            one_smul]
        rw [ract_of_mem (comp_mem_grading f.2 g.2) n.2,
          ract_of_mem f.2 (ract_mem_grading n.2 g.2), ract_of_mem g.2 n.2, hfg,
          smul_units_smul (M := N), smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add]
        congr 1
        exact ks_congr ⟨0, by ring⟩

/-- The right Leibniz rule `d (n <• f) = d n <• f + (-1)^{|n|} • (n <• d f)`. -/
theorem d_ract {X Y : C} {j : ℤ} {n : N.obj (op Y)} (hn : n ∈ grading j) (f : X ⟶ Y) :
    d (n <• f) = d n <• f + koszulSign j • (n <• d f) := by
  induction f using DG.induction_on with
  | h_zero => simp [d_zero]
  | h_add f f' hf hf' =>
    rw [ract_add, d_add, hf, hf', d_add, ract_add, ract_add, _root_.smul_add]
    abel
  | h_homogeneous f =>
    rename_i i
    have e1 : koszulSign (i * j + i) = koszulSign (i * (j + 1)) := ks_congr ⟨0, by ring⟩
    have e2 : koszulSign (i * j) = koszulSign (j + (i + 1) * j) := ks_congr ⟨-j, by ring⟩
    rw [ract_of_mem f.2 hn, ract_of_mem f.2 (d_mem hn), ract_of_mem (d_mem f.2) hn, d_units_smul,
      d_smul (M := N) (f := homOp (f : X ⟶ Y)) f.2, _root_.smul_add, smul_smul, smul_smul,
      ← koszulSign_add, ← koszulSign_add, e1, e2]
    exact add_comm _ _

/-- For a cocycle `f`, `d (n • f) = d n • f`. -/
theorem d_ract_of_d_eq_zero {X Y : C} {f : X ⟶ Y} (hf : d f = 0) (n : N.obj (op Y)) :
    d (n <• f) = d n <• f := by
  induction n using DG.induction_on with
  | h_zero => simp
  | h_homogeneous n => rw [d_ract n.2, hf, ract_zero, _root_.smul_zero, add_zero]
  | h_add n n' hn hn' => rw [add_ract, d_add, hn, hn', d_add, add_ract]

/-- Morphisms of right dg modules commute with the right action. -/
theorem Hom.map_ract {N' : CatModule.{w} (DGOpposite C)} (φ : N ⟶ N') {X Y : C} (f : X ⟶ Y)
    (n : N.obj (op Y)) : φ.app (op X) (n <• f) = φ.app (op Y) n <• f := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_add f f' hf hf' => rw [ract_add, map_add, hf, hf', ract_add]
  | h_homogeneous f =>
    induction n using DG.induction_on with
    | h_zero => simp
    | h_add n n' hn hn' => rw [add_ract, map_add, hn, hn', map_add, add_ract]
    | h_homogeneous n =>
      rw [ract_of_mem f.2 n.2, ract_of_mem f.2 (φ.map_mem n.2), map_units_zsmul]
      exact congrArg _ (φ.map_smul (homOp (f : X ⟶ Y)) (n : N.obj (op Y)))

end RightAction

/-! ### Right dg modules from right actions -/

section OfRightAction

variable (obj : C → Type w) [∀ X, AddCommGroup (obj X)] [∀ X, DGAddCommGroup (obj X)]
  (act : ∀ {X Y : C}, (X ⟶ Y) →+ obj Y →+ obj X)
  (act_mem : ∀ {X Y : C} {i j : ℤ} {f : X ⟶ Y} {n : obj Y}, f ∈ grading i → n ∈ grading j →
    act f n ∈ grading (j + i))
  (act_id : ∀ (X : C) (n : obj X), act (𝟙 X) n = n)
  (act_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : obj Z),
    act (f ≫ g) n = act f (act g n))
  (d_act : ∀ {X Y : C} {j : ℤ} {n : obj Y}, n ∈ grading j → ∀ f : X ⟶ Y,
    d (act f n) = act f (d n) + koszulSign j • act (d f) n)

/-- The Koszul twist `f ⊙ n = (-1)^{|f||n|} • (n • f)` of a right action (an auxiliary
definition for `ofRightAction`). -/
def twistAct {X Y : C} : (X ⟶ Y) →+ obj Y →+ obj X :=
  koszulTwist (act (X := X) (Y := Y))

omit [DGCategory C] in
include act_mem in
theorem twistAct_mem {X Y : C} {i j : ℤ} {f : X ⟶ Y} {n : obj Y} (hf : f ∈ grading i)
    (hn : n ∈ grading j) : twistAct obj act f n ∈ grading (i + j) := by
  rw [twistAct, koszulTwist_apply_of_mem _ hf hn, Units.smul_def, add_comm]
  exact zsmul_mem (act_mem hf hn) _

include act_id in
theorem twistAct_id (X : C) (n : obj X) : twistAct obj act (𝟙 X) n = n := by
  induction n using DG.induction_on with
  | h_zero => exact map_zero _
  | h_homogeneous n =>
    rw [twistAct, koszulTwist_apply_of_mem _ (id_mem_grading X) n.2, zero_mul, koszulSign_zero,
      one_smul]
    exact act_id _ _
  | h_add n n' hn hn' => rw [map_add, hn, hn']

include act_mem act_comp in
theorem twistAct_signedComp {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X) (n : obj X) :
    twistAct obj act (signedComp Z Y X g f) n = twistAct obj act g (twistAct obj act f n) := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_add f f' hf hf' => simp only [map_add, AddMonoidHom.add_apply, hf, hf']
  | h_homogeneous f =>
    rename_i i
    induction g using DG.induction_on with
    | h_zero => simp
    | h_add g g' hg hg' => simp only [map_add, AddMonoidHom.add_apply, hg, hg']
    | h_homogeneous g =>
      rename_i k
      induction n using DG.induction_on with
      | h_zero => simp
      | h_add n n' hn hn' => simp only [map_add, hn, hn']
      | h_homogeneous n =>
        rename_i j
        have hm : koszulSign (i * j) • act (f : Y ⟶ X) (n : obj X) ∈ grading (j + i) := by
          rw [Units.smul_def]; exact zsmul_mem (act_mem f.2 n.2) _
        unfold twistAct
        rw [signedComp_of_mem g.2 f.2, map_units_zsmul, units_smul_apply',
          koszulTwist_apply_of_mem _ (comp_mem_grading g.2 f.2) n.2,
          koszulTwist_apply_of_mem _ f.2 n.2, koszulTwist_apply_of_mem _ g.2 hm, act_comp,
          map_units_zsmul, smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add]
        congr 1
        exact ks_congr ⟨0, by ring⟩

omit [DGCategory C] in
include d_act in
theorem d_twistAct {X Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (n : obj Y) :
    d (twistAct obj act f n) =
      twistAct obj act (d f) n + koszulSign i • twistAct obj act f (d n) := by
  induction n using DG.induction_on with
  | h_zero => simp
  | h_add n n' hn hn' =>
    simp only [map_add, hn, hn', _root_.smul_add]
    abel
  | h_homogeneous n =>
    rename_i j
    have e1 : koszulSign (i * j + j) = koszulSign ((i + 1) * j) := ks_congr ⟨0, by ring⟩
    have e2 : koszulSign (i * j) = koszulSign (i + i * (j + 1)) := ks_congr ⟨-i, by ring⟩
    rw [twistAct, koszulTwist_apply_of_mem _ hf n.2, koszulTwist_apply_of_mem _ (d_mem hf) n.2,
      koszulTwist_apply_of_mem _ hf (d_mem n.2), d_units_smul, d_act n.2, _root_.smul_add,
      smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add, e1, e2]
    exact add_comm _ _

/-- The right dg module over `C` (a left dg module over `DGOpposite C`) attached to a family of
dg abelian groups `obj X` with a right action `act f : obj Y →+ obj X` of the morphisms
`f : X ⟶ Y` which is graded, unital, associative (`n • (f ≫ g) = (n • g) • f`) and satisfies
the right Leibniz rule `d (n • f) = d n • f + (-1)^{|n|} • (n • d f)`. The left action of
`DGOpposite C` is the Koszul twist `f • n = (-1)^{|f||n|} • (n • f)`. -/
@[reducible]
def ofRightAction : CatModule.{w} (DGOpposite C) where
  obj X := obj X.unop
  act {X Y} := twistAct obj act (X := Y.unop) (Y := X.unop)
  act_mem' hf hn := twistAct_mem obj act act_mem hf hn
  act_id' X n := twistAct_id obj act act_id X.unop n
  act_comp' f g n := twistAct_signedComp obj act act_mem act_comp g f n
  d_act' hf n := d_twistAct obj act d_act hf n

@[simp]
theorem ofRightAction_obj (X : DGOpposite C) :
    (ofRightAction obj act act_mem act_id act_comp d_act).obj X = obj X.unop := rfl

/-- The right action of `ofRightAction` is the given right action. -/
@[simp]
theorem ract_ofRightAction {X Y : C} (f : X ⟶ Y) (n : obj Y) :
    (ofRightAction obj act act_mem act_id act_comp d_act).ract f n = act f n :=
  DFunLike.congr_fun (DFunLike.congr_fun (koszulTwist_koszulTwist (act (X := X) (Y := Y))) f) n

end OfRightAction

/-! ### Morphisms from maps commuting with the right action -/

section HomOfRight

variable {N N' : CatModule.{w} (DGOpposite C)}

/-- A family of additive maps of degree `0` commuting with the differentials and with the right
actions is a morphism of right dg modules. -/
@[simps]
def homOfRight (app : ∀ X : C, N.obj (op X) →+ N'.obj (op X))
    (map_mem : ∀ {X : C} {n : ℤ} {m : N.obj (op X)}, m ∈ grading n → app X m ∈ grading n)
    (map_d : ∀ {X : C} (m : N.obj (op X)), app X (d m) = d (app X m))
    (map_ract : ∀ {X Y : C} (f : X ⟶ Y) (m : N.obj (op Y)), app X (m <• f) = app Y m <• f) :
    N ⟶ N' where
  app X := app X.unop
  map_mem' hm := map_mem hm
  map_d' m := map_d m
  map_smul' {X Y} f m := by
    induction f using DG.induction_on with
    | h_zero => simp
    | h_add f f' hf hf' => rw [add_smul, map_add, hf, hf', add_smul]
    | h_homogeneous f =>
      induction m using DG.induction_on with
      | h_zero => simp
      | h_add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add]
      | h_homogeneous m =>
        rw [smul_eq_ract_of_mem f.2 m.2, smul_eq_ract_of_mem f.2 (map_mem m.2),
          map_units_zsmul]
        exact congrArg _ (map_ract (homUnop (f : X ⟶ Y)) (m : N.obj X))

end HomOfRight

/-! ### Representable right modules -/

section Representable

/-- The representable right dg module `C(-, X)`, i.e. `representable (op X)` over
`DGOpposite C`, has the right action by precomposition, `h • f = f ≫ h`. -/
@[simp]
theorem representable_op_ract (X : C) {Y Z : C} (f : Z ⟶ Y)
    (h : (representable (op X)).obj (op Y)) :
    h <• f = f ≫ (h : Y ⟶ X) := by
  induction f using DG.induction_on with
  | h_zero => rw [ract_zero, Limits.zero_comp]
  | h_add f f' hf hf' => rw [ract_add, hf, hf', Preadditive.add_comp]
  | h_homogeneous f =>
    rename_i i
    induction h using DG.induction_on with
    | h_zero => rw [zero_ract, Limits.comp_zero]
    | h_add h h' hh hh' => rw [add_ract, hh, hh', Preadditive.comp_add]
    | h_homogeneous h =>
      rename_i j
      obtain ⟨h, hh⟩ := h
      obtain ⟨f, hf⟩ := f
      rw [ract_of_mem hf hh, representable_smul]
      show koszulSign (i * j) • homUnop ((h : op X ⟶ op Y) ≫ homOp f) = f ≫ (h : Y ⟶ X)
      rw [homUnop_comp_of_mem (X := op X) (Y := op Y) (Z := op Z) (f := h) (g := homOp f) hh hf,
        smul_smul, mul_comm j i, Int.units_mul_self, one_smul]
      rfl

end Representable

end CatModule

end DG
