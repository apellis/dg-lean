import Mathlib.Algebra.DirectSum.Decomposition
import DG.Category.Basic

/-!
# The opposite dg category

The opposite of a dg category `C` has the objects of `C`, the Hom complexes
`Cᵒᵖ(X, Y) = C(Y, X)` (with the same grading and differential), and the composition twisted by the
Koszul sign: for homogeneous `f ∈ Cᵒᵖ(X, Y)ⁱ` and `g ∈ Cᵒᵖ(Y, Z)ʲ`,

  `f ≫ᵒᵖ g = (-1)^{i j} • (g ≫ f)`,

extended bilinearly. This is the sign rule of `docs/CONVENTIONS.md` (the two morphisms are
exchanged), and it is the sign making the Leibniz rule hold in `Cᵒᵖ`. Mathlib's `Cᵒᵖ` has the
unsigned composition, so the opposite dg category is the separate type `DG.DGOpposite C`.

## Main definitions

* `DG.signedComp : (X ⟶ Y) →+ (Y ⟶ Z) →+ (X ⟶ Z)`, the bilinear map with
  `signedComp f g = (-1)^{|f||g|} • (f ≫ g)` on homogeneous morphisms (`DG.signedComp_of_mem`),
  and its associativity (`DG.signedComp_assoc`).
* `DG.DGOpposite C` (objects `DG.DGOpposite.op X`), with the category structure
  `f ≫ g = signedComp g f`, and the instances `Preadditive`, `DGAddCommGroup` on Hom groups and
  `DGCategory` (`DG.DGOpposite.instDGCategory`).
* `DG.DGOpposite.homOp`, `DG.DGOpposite.homUnop`: the identifications of Hom groups, and
  `DG.DGOpposite.homUnop_comp_of_mem`: the composition formula on homogeneous morphisms.
-/

open CategoryTheory DirectSum

universe v u

namespace DG

section SignedComp

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {X Y Z : C}

/-- The signed composition of homogeneous morphisms of degrees `i` and `j`. -/
def signedCompHomogeneous (i j : ℤ) :
    grading (M := X ⟶ Y) i →+ grading (M := Y ⟶ Z) j →+ (X ⟶ Z) :=
  AddMonoidHom.mk'
    (fun f => AddMonoidHom.mk' (fun g => koszulSign (i * j) • ((f : X ⟶ Y) ≫ (g : Y ⟶ Z)))
      fun g g' => by simp only [AddSubgroup.coe_add, Preadditive.comp_add, smul_add])
    fun f f' => by
      ext g
      simp only [AddSubgroup.coe_add, Preadditive.add_comp, smul_add, AddMonoidHom.mk'_apply,
        AddMonoidHom.add_apply]

/-- The signed composition on the external direct sums of homogeneous components. -/
def signedCompAux :
    (⨁ i, grading (M := X ⟶ Y) i) →+ (⨁ j, grading (M := Y ⟶ Z) j) →+ (X ⟶ Z) :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.toAddMonoid fun j =>
      (signedCompHomogeneous (X := X) (Y := Y) (Z := Z) i j).flip).flip

theorem signedCompAux_of_of (i j : ℤ) (f : grading (M := X ⟶ Y) i) (g : grading (M := Y ⟶ Z) j) :
    signedCompAux (DirectSum.of _ i f) (DirectSum.of _ j g) =
      koszulSign (i * j) • ((f : X ⟶ Y) ≫ (g : Y ⟶ Z)) := by
  simp only [signedCompAux, DirectSum.toAddMonoid_of, AddMonoidHom.flip_apply]
  rfl

variable (X Y Z) in
/-- The Koszul-signed composition `(X ⟶ Y) →+ (Y ⟶ Z) →+ (X ⟶ Z)`: on homogeneous morphisms,
`signedComp f g = (-1)^{|f||g|} • (f ≫ g)`, extended bilinearly. -/
def signedComp : (X ⟶ Y) →+ (Y ⟶ Z) →+ (X ⟶ Z) :=
  AddMonoidHom.mk'
    (fun f => (signedCompAux (decompose (grading (M := X ⟶ Y)) f)).comp
      (decomposeAddEquiv (grading (M := Y ⟶ Z))).toAddMonoidHom)
    fun f f' => by
      ext g
      simp only [decompose_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.comp_apply]

theorem signedComp_apply (f : X ⟶ Y) (g : Y ⟶ Z) :
    signedComp X Y Z f g =
      signedCompAux (decompose (grading (M := X ⟶ Y)) f) (decompose (grading (M := Y ⟶ Z)) g) :=
  rfl

/-- The signed composition of homogeneous morphisms. -/
theorem signedComp_of_mem {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : f ∈ grading i)
    (hg : g ∈ grading j) : signedComp X Y Z f g = koszulSign (i * j) • (f ≫ g) := by
  rw [signedComp_apply, decompose_of_mem _ hf, decompose_of_mem _ hg, signedCompAux_of_of]

variable [DGCategory C]

theorem signedComp_mem_grading {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : f ∈ grading i)
    (hg : g ∈ grading j) : signedComp X Y Z f g ∈ grading (i + j) := by
  rw [signedComp_of_mem hf hg, Units.smul_def]
  exact zsmul_mem (comp_mem_grading hf hg) _

@[simp]
theorem signedComp_id (f : X ⟶ Y) : signedComp X Y Y f (𝟙 Y) = f := by
  induction f using induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rw [signedComp_of_mem f.2 (id_mem_grading Y), mul_zero, koszulSign_zero, one_smul,
      Category.comp_id]
  | h_add f f' hf hf' => rw [map_add, AddMonoidHom.add_apply, hf, hf']

@[simp]
theorem id_signedComp (f : X ⟶ Y) : signedComp X X Y (𝟙 X) f = f := by
  induction f using induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rw [signedComp_of_mem (id_mem_grading X) f.2, zero_mul, koszulSign_zero, one_smul,
      Category.id_comp]
  | h_add f f' hf hf' => rw [map_add, hf, hf']

/-- The signed composition is associative. -/
theorem signedComp_assoc {W : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    signedComp W Y Z (signedComp W X Y f g) h = signedComp W X Z f (signedComp X Y Z g h) := by
  induction f using induction_on with
  | h_zero => simp
  | h_add f f' hf hf' => simp only [map_add, AddMonoidHom.add_apply, hf, hf']
  | h_homogeneous f =>
    rename_i i
    induction g using induction_on with
    | h_zero => simp
    | h_add g g' hg hg' => simp only [map_add, AddMonoidHom.add_apply, hg, hg']
    | h_homogeneous g =>
      rename_i j
      induction h using induction_on with
      | h_zero => simp
      | h_add h h' hh hh' => simp only [map_add, hh, hh']
      | h_homogeneous h =>
        rename_i k
        rw [signedComp_of_mem (signedComp_mem_grading f.2 g.2) h.2,
          signedComp_of_mem f.2 (signedComp_mem_grading g.2 h.2), signedComp_of_mem f.2 g.2,
          signedComp_of_mem g.2 h.2, units_smul_comp, comp_units_smul, smul_smul, smul_smul,
          ← koszulSign_add, ← koszulSign_add, Category.assoc]
        congr 2
        ring

/-- The Leibniz rule for the signed composition, for `g` homogeneous of degree `j`:
`d (signedComp g f) = signedComp (d g) f + (-1)^j • signedComp g (d f)`. -/
theorem d_signedComp {j : ℤ} {g : X ⟶ Y} (hg : g ∈ grading j) (f : Y ⟶ Z) :
    d (signedComp X Y Z g f) =
      signedComp X Y Z (d g) f + koszulSign j • signedComp X Y Z g (d f) := by
  induction f using induction_on with
  | h_zero => simp
  | h_add f f' hf hf' => simp only [map_add, d_add, hf, hf', smul_add]; abel
  | h_homogeneous f =>
    rename_i i
    have h₁ : koszulSign ((j + 1) * i) = koszulSign (j * i + i) := by rw [add_mul, one_mul]
    have h₂ : koszulSign (j + j * (i + 1)) = koszulSign (j * i) := by
      rw [show j + j * (i + 1) = j * i + 2 * j by ring, koszulSign_add,
        koszulSign_even (even_two_mul j), mul_one]
    rw [signedComp_of_mem hg f.2, signedComp_of_mem (d_mem hg) f.2,
      signedComp_of_mem hg (d_mem f.2), d_units_smul, d_comp _ f.2, smul_add, smul_smul,
      smul_smul, ← koszulSign_add, ← koszulSign_add, h₁, h₂, add_comm]

end SignedComp

/-- The opposite dg category of `C`: the objects of `C`, with `Cᵒᵖ(X, Y) = C(Y, X)` and the
composition twisted by the Koszul sign, `f ≫ g = (-1)^{|f||g|} • (g ≫ f)` in `C`. -/
structure DGOpposite (C : Type u) where
  /-- The object of `DGOpposite C` attached to an object of `C`. -/
  op ::
  /-- The object of `C` underlying an object of `DGOpposite C`. -/
  unop : C

namespace DGOpposite

@[simp] theorem op_unop {C : Type u} (X : DGOpposite C) : op X.unop = X := rfl
@[simp] theorem unop_op {C : Type u} (X : C) : (op X).unop = X := rfl

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-- The opposite dg category: composition is the signed composition in the opposite order. -/
instance category : Category.{v} (DGOpposite C) where
  Hom X Y := Y.unop ⟶ X.unop
  id X := 𝟙 X.unop
  comp {X Y Z} f g := signedComp Z.unop Y.unop X.unop g f
  id_comp f := signedComp_id f
  comp_id f := id_signedComp f
  assoc f g h := (signedComp_assoc h g f).symm

/-- A morphism of `C` as a morphism of the opposite dg category. -/
def homOp {X Y : C} (f : X ⟶ Y) : op Y ⟶ op X := f

/-- A morphism of the opposite dg category as a morphism of `C`. -/
def homUnop {X Y : DGOpposite C} (f : X ⟶ Y) : Y.unop ⟶ X.unop := f

@[simp] theorem homOp_homUnop {X Y : DGOpposite C} (f : X ⟶ Y) : homOp (homUnop f) = f := rfl
@[simp] theorem homUnop_homOp {X Y : C} (f : X ⟶ Y) : homUnop (homOp f) = f := rfl

@[simp] theorem homUnop_id (X : DGOpposite C) : homUnop (𝟙 X) = 𝟙 X.unop := rfl

theorem homUnop_comp {X Y Z : DGOpposite C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homUnop (f ≫ g) = signedComp Z.unop Y.unop X.unop (homUnop g) (homUnop f) := rfl

instance (X Y : DGOpposite C) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (Y.unop ⟶ X.unop))

instance preadditive : Preadditive (DGOpposite C) where
  add_comp X Y Z f f' g := by
    change signedComp Z.unop Y.unop X.unop (homUnop g) (homUnop f + homUnop f') =
      signedComp Z.unop Y.unop X.unop (homUnop g) (homUnop f) +
        signedComp Z.unop Y.unop X.unop (homUnop g) (homUnop f')
    rw [map_add]
  comp_add X Y Z f g g' := by
    change signedComp Z.unop Y.unop X.unop (homUnop g + homUnop g') (homUnop f) =
      signedComp Z.unop Y.unop X.unop (homUnop g) (homUnop f) +
        signedComp Z.unop Y.unop X.unop (homUnop g') (homUnop f)
    rw [map_add, AddMonoidHom.add_apply]

/-- The Hom groups of the opposite dg category are those of `C`, with the same grading and
differential. -/
instance instDGAddCommGroupHom (X Y : DGOpposite C) : DGAddCommGroup (X ⟶ Y) :=
  inferInstanceAs (DGAddCommGroup (Y.unop ⟶ X.unop))

@[simp] theorem homUnop_add {X Y : DGOpposite C} (f g : X ⟶ Y) :
    homUnop (f + g) = homUnop f + homUnop g := rfl
@[simp] theorem homUnop_neg {X Y : DGOpposite C} (f : X ⟶ Y) : homUnop (-f) = -homUnop f := rfl
@[simp] theorem homUnop_zero (X Y : DGOpposite C) : homUnop (0 : X ⟶ Y) = 0 := rfl

theorem mem_grading_iff {X Y : DGOpposite C} {n : ℤ} {f : X ⟶ Y} :
    f ∈ grading n ↔ homUnop f ∈ grading n :=
  Iff.rfl

@[simp]
theorem homUnop_d {X Y : DGOpposite C} (f : X ⟶ Y) : homUnop (d f) = d (homUnop f) := rfl

/-- The composition of homogeneous morphisms in the opposite dg category:
`f ≫ g = (-1)^{|f||g|} • (g ≫ f)`. -/
theorem homUnop_comp_of_mem {X Y Z : DGOpposite C} {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ grading i) (hg : g ∈ grading j) :
    homUnop (f ≫ g) = koszulSign (i * j) • (homUnop g ≫ homUnop f) := by
  rw [homUnop_comp, signedComp_of_mem (X := Z.unop) (Y := Y.unop) (Z := X.unop)
    (f := homUnop g) (g := homUnop f) hg hf, mul_comm]

/-- The opposite of a dg category is a dg category. -/
instance instDGCategory : DGCategory (DGOpposite C) where
  comp_mem' {X Y Z i j f g} hf hg := by
    rw [add_comm]
    exact signedComp_mem_grading (X := Z.unop) (Y := Y.unop) (Z := X.unop) hg hf
  id_mem' X := id_mem_grading X.unop
  d_comp' {X Y Z j} f g hg := d_signedComp (X := Z.unop) (Y := Y.unop) (Z := X.unop) hg f

end DGOpposite

end DG
