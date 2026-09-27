import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Quotient.Preadditive
import DG.Algebra.Basic

/-!
# Differential graded categories

A dg category is a preadditive category `C` whose Hom groups are dg abelian groups
(`DG.DGAddCommGroup (X ⟶ Y)`), such that composition is graded, identities have degree `0` and
the differential satisfies the Leibniz rule. Following `docs/CONVENTIONS.md` the Leibniz rule is
stated in diagrammatic order, with the sign carried by the second morphism:

  `d (f ≫ g) = f ≫ d g + (-1)^{|g|} (d f ≫ g)`   for `g` homogeneous,

which is the rule `d (g ∘ f) = d g ∘ f + (-1)^{|g|} g ∘ d f`. For the one-object category
`SingleObj A` of a ring (with `f ≫ g = g * f`) this is the Leibniz rule of `DG.DGRing`
(`DG.Category.SingleObj`).

## Main definitions

* `DG.DGCategory C`: the `Prop`-valued mixin, on top of `[Category C] [Preadditive C]` and
  `[∀ X Y : C, DGAddCommGroup (X ⟶ Y)]`.
* `DG.comp_mem_grading`, `DG.id_mem_grading`, `DG.d_comp`: the axioms; `DG.d_id`, the variants
  `DG.d_comp_of_d_eq_zero_left`, `DG.d_comp_of_d_eq_zero_right`, and the closure of cocycles and
  coboundaries under composition (`DG.comp_mem_cocycles`, `DG.comp_mem_coboundaries_left`,
  `DG.comp_mem_coboundaries_right`).
* `DG.DGCategory.Z0 C`: the category `Z⁰(C)` with the same objects and the degree-`0` cocycles
  as morphisms; it is preadditive, with a faithful additive functor `DG.DGCategory.Z0.forget` to
  `C`.
* `DG.DGCategory.H0 C`: the homotopy category `H⁰(C)`, the quotient of `Z⁰(C)` by the
  coboundaries (Mathlib's `CategoryTheory.Quotient`), a preadditive category, with the full
  essentially surjective additive functor `DG.DGCategory.H0.quotient C : Z⁰(C) ⥤ H⁰(C)`.
-/

open CategoryTheory

universe v u

namespace DG

/-- A differential graded category: a preadditive category whose Hom groups are dg abelian
groups, such that composition is graded (`(X ⟶ Y)ⁱ ≫ (Y ⟶ Z)ʲ ⊆ (X ⟶ Z)ⁱ⁺ʲ`), identities have
degree `0`, and the Leibniz rule `d (f ≫ g) = f ≫ d g + (-1)^{|g|} • (d f ≫ g)` holds for `g`
homogeneous of degree `|g|`. -/
class DGCategory (C : Type u) [Category.{v} C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] : Prop where
  comp_mem' : ∀ {X Y Z : C} {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z}, f ∈ grading i → g ∈ grading j →
    f ≫ g ∈ grading (i + j)
  id_mem' : ∀ X : C, 𝟙 X ∈ grading (M := X ⟶ X) 0
  d_comp' : ∀ {X Y Z : C} {j : ℤ} (f : X ⟶ Y) {g : Y ⟶ Z}, g ∈ grading j →
    d (f ≫ g) = f ≫ d g + koszulSign j • (d f ≫ g)

section DGCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

section Preadditive

omit [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- Composition commutes with the action of signs. -/
@[simp]
theorem comp_units_smul {X Y Z : C} (f : X ⟶ Y) (u : ℤˣ) (g : Y ⟶ Z) :
    f ≫ (u • g) = u • (f ≫ g) := by
  rw [Units.smul_def, Units.smul_def, Preadditive.comp_zsmul]

/-- Composition commutes with the action of signs. -/
@[simp]
theorem units_smul_comp {X Y Z : C} (u : ℤˣ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (u • f) ≫ g = u • (f ≫ g) := by
  rw [Units.smul_def, Units.smul_def, Preadditive.zsmul_comp]

end Preadditive

variable [DGCategory C]

theorem comp_mem_grading {X Y Z : C} {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : f ∈ grading i)
    (hg : g ∈ grading j) : f ≫ g ∈ grading (i + j) :=
  DGCategory.comp_mem' hf hg

theorem id_mem_grading (X : C) : 𝟙 X ∈ grading (M := X ⟶ X) 0 :=
  DGCategory.id_mem' X

/-- The Leibniz rule for composition, in diagrammatic order: the sign is that of the second
morphism. -/
theorem d_comp {X Y Z : C} {j : ℤ} (f : X ⟶ Y) {g : Y ⟶ Z} (hg : g ∈ grading j) :
    d (f ≫ g) = f ≫ d g + koszulSign j • (d f ≫ g) :=
  DGCategory.d_comp' f hg

theorem d_comp_of_even {X Y Z : C} {j : ℤ} (f : X ⟶ Y) {g : Y ⟶ Z} (hg : g ∈ grading j)
    (hj : Even j) : d (f ≫ g) = f ≫ d g + d f ≫ g := by
  rw [d_comp f hg, koszulSign_even hj, one_smul]

theorem d_comp_of_odd {X Y Z : C} {j : ℤ} (f : X ⟶ Y) {g : Y ⟶ Z} (hg : g ∈ grading j)
    (hj : Odd j) : d (f ≫ g) = f ≫ d g - d f ≫ g := by
  rw [d_comp f hg, koszulSign_odd hj, Units.neg_smul, one_smul, sub_eq_add_neg]

theorem d_comp_of_mem_zero {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} (hg : g ∈ grading 0) :
    d (f ≫ g) = f ≫ d g + d f ≫ g :=
  d_comp_of_even f hg Even.zero

/-- Identities are cocycles. -/
@[simp]
theorem d_id (X : C) : d (𝟙 X) = 0 := by
  have h := d_comp (𝟙 X) (id_mem_grading X)
  rw [Category.id_comp, Category.id_comp, Category.comp_id, koszulSign_zero, one_smul] at h
  exact left_eq_add.mp h

/-- If `f` is a cocycle then `d (f ≫ g) = f ≫ d g` for every `g`. -/
theorem d_comp_of_d_eq_zero_left {X Y Z : C} {f : X ⟶ Y} (hf : d f = 0) (g : Y ⟶ Z) :
    d (f ≫ g) = f ≫ d g := by
  induction g using induction_on with
  | h_zero => simp
  | h_homogeneous g => rw [d_comp f g.2, hf, Limits.zero_comp, smul_zero, add_zero]
  | h_add g g' hg hg' => rw [Preadditive.comp_add, d_add, hg, hg', d_add, Preadditive.comp_add]

/-- If `g` is a homogeneous cocycle of degree `j` then `d (f ≫ g) = (-1)^j • (d f ≫ g)`. -/
theorem d_comp_of_d_eq_zero_right {X Y Z : C} {j : ℤ} (f : X ⟶ Y) {g : Y ⟶ Z}
    (hg : g ∈ grading j) (hdg : d g = 0) : d (f ≫ g) = koszulSign j • (d f ≫ g) := by
  rw [d_comp f hg, hdg, Limits.comp_zero, zero_add]

/-- The differential of a composite of two cocycles vanishes. -/
theorem d_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : d f = 0) (hg : d g = 0) :
    d (f ≫ g) = 0 := by
  rw [d_comp_of_d_eq_zero_left hf, hg, Limits.comp_zero]

/-- Composition with a homogeneous morphism on the left commutes with taking homogeneous
components. -/
theorem decompose_comp_left {X Y Z : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (g : Y ⟶ Z)
    (j : ℤ) :
    (DirectSum.decompose (grading (M := X ⟶ Z)) (f ≫ g) (j + i) : X ⟶ Z) =
      f ≫ (DirectSum.decompose (grading (M := Y ⟶ Z)) g j : Y ⟶ Z) :=
  decompose_map (k := i) (Preadditive.leftComp Z f)
    (fun {n _} hg => by rw [add_comm]; exact comp_mem_grading hf hg) g j

/-- Composition with a homogeneous morphism on the right commutes with taking homogeneous
components. -/
theorem decompose_comp_right {X Y Z : C} {j : ℤ} (f : X ⟶ Y) {g : Y ⟶ Z} (hg : g ∈ grading j)
    (i : ℤ) :
    (DirectSum.decompose (grading (M := X ⟶ Z)) (f ≫ g) (i + j) : X ⟶ Z) =
      (DirectSum.decompose (grading (M := X ⟶ Y)) f i : X ⟶ Y) ≫ g :=
  decompose_map (k := j) (Preadditive.rightComp X g) (fun hf => comp_mem_grading hf hg) f i

/-! ### Cocycles and coboundaries -/

theorem id_mem_cocycles (X : C) : 𝟙 X ∈ cocycles (X ⟶ X) 0 :=
  ⟨id_mem_grading X, d_id X⟩

theorem comp_mem_cocycles {X Y Z : C} {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ cocycles (X ⟶ Y) i) (hg : g ∈ cocycles (Y ⟶ Z) j) :
    f ≫ g ∈ cocycles (X ⟶ Z) (i + j) :=
  ⟨comp_mem_grading hf.1 hg.1, d_comp_eq_zero hf.2 hg.2⟩

/-- A coboundary followed by a homogeneous cocycle is a coboundary. -/
theorem comp_mem_coboundaries_left {X Y Z : C} {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ coboundaries (X ⟶ Y) i) (hg : g ∈ cocycles (Y ⟶ Z) j) :
    f ≫ g ∈ coboundaries (X ⟶ Z) (i + j) := by
  obtain ⟨h, hh, rfl⟩ := hf
  refine ⟨koszulSign j • (h ≫ g), ?_, ?_⟩
  · have := comp_mem_grading hh hg.1
    rw [show i - 1 + j = i + j - 1 by ring] at this
    rw [Units.smul_def]
    exact zsmul_mem this _
  · rw [d_units_smul, d_comp_of_d_eq_zero_right h hg.1 hg.2, smul_smul, ← koszulSign_add,
      koszulSign_even (by simp), one_smul]

/-- A cocycle followed by a coboundary is a coboundary. -/
theorem comp_mem_coboundaries_right {X Y Z : C} {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ cocycles (X ⟶ Y) i) (hg : g ∈ coboundaries (Y ⟶ Z) j) :
    f ≫ g ∈ coboundaries (X ⟶ Z) (i + j) := by
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨f ≫ h, ?_, d_comp_of_d_eq_zero_left hf.2 h⟩
  have := comp_mem_grading hf.1 hh
  rwa [show i + (j - 1) = i + j - 1 by ring] at this

end DGCategory

/-! ### The category `Z⁰(C)` -/

namespace DGCategory

/-- The category `Z⁰(C)` of a dg category `C`: it has the objects of `C`, and its morphisms are
the degree-`0` cocycles of the Hom complexes of `C`. -/
@[ext]
structure Z0 (C : Type u) where
  /-- The object of `C` underlying an object of `Z⁰(C)`. -/
  as : C

namespace Z0

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-- The morphisms of `Z⁰(C)`: degree-`0` cocycles of the Hom complexes of `C`. -/
@[ext]
structure Hom (X Y : Z0 C) where
  /-- The underlying morphism of `C`. -/
  hom : X.as ⟶ Y.as
  mem_cocycles : hom ∈ cocycles (X.as ⟶ Y.as) 0

instance category : Category.{v} (Z0 C) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 X.as, id_mem_cocycles X.as⟩
  comp f g := ⟨f.hom ≫ g.hom, by simpa using comp_mem_cocycles f.mem_cocycles g.mem_cocycles⟩

theorem Hom.mem_grading {X Y : Z0 C} (f : X ⟶ Y) : f.hom ∈ grading 0 :=
  f.mem_cocycles.1

@[simp]
theorem Hom.d_hom {X Y : Z0 C} (f : X ⟶ Y) : d f.hom = 0 :=
  f.mem_cocycles.2

@[ext]
theorem hom_ext {X Y : Z0 C} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

theorem hom_injective {X Y : Z0 C} : Function.Injective (Hom.hom : (X ⟶ Y) → (X.as ⟶ Y.as)) :=
  fun _ _ h => hom_ext h

/-- A degree-`0` cocycle as a morphism of `Z⁰(C)`. -/
abbrev homMk {X Y : Z0 C} (f : X.as ⟶ Y.as) (hf : f ∈ cocycles (X.as ⟶ Y.as) 0) : X ⟶ Y :=
  ⟨f, hf⟩

@[simp]
theorem homMk_hom {X Y : Z0 C} (f : X.as ⟶ Y.as) (hf : f ∈ cocycles (X.as ⟶ Y.as) 0) :
    (homMk f hf).hom = f := rfl

@[simp]
theorem id_hom (X : Z0 C) : (𝟙 X : X ⟶ X).hom = 𝟙 X.as := rfl

@[simp]
theorem comp_hom {X Y Z : Z0 C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

section AddCommGroup

variable {X Y : Z0 C}

instance : Zero (X ⟶ Y) := ⟨⟨0, zero_mem _⟩⟩
instance : Add (X ⟶ Y) := ⟨fun f g => ⟨f.hom + g.hom, add_mem f.mem_cocycles g.mem_cocycles⟩⟩
instance : Neg (X ⟶ Y) := ⟨fun f => ⟨-f.hom, neg_mem f.mem_cocycles⟩⟩
instance : Sub (X ⟶ Y) := ⟨fun f g => ⟨f.hom - g.hom, sub_mem f.mem_cocycles g.mem_cocycles⟩⟩
instance : SMul ℕ (X ⟶ Y) := ⟨fun n f => ⟨n • f.hom, nsmul_mem f.mem_cocycles n⟩⟩
instance : SMul ℤ (X ⟶ Y) := ⟨fun n f => ⟨n • f.hom, zsmul_mem f.mem_cocycles n⟩⟩

@[simp] theorem add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl
@[simp] theorem zero_hom : (0 : X ⟶ Y).hom = 0 := rfl
@[simp] theorem neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl
@[simp] theorem sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl
@[simp] theorem zsmul_hom (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl
@[simp] theorem nsmul_hom (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

instance : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup Hom.hom hom_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end AddCommGroup

instance preadditive : Preadditive (Z0 C) where
  add_comp _ _ _ _ _ _ := hom_ext (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := hom_ext (Preadditive.comp_add _ _ _ _ _ _)

/-- The morphisms of `Z⁰(C)` from `X` to `Y` are the degree-`0` cocycles of `X.as ⟶ Y.as`. -/
def homAddEquiv (X Y : Z0 C) : (X ⟶ Y) ≃+ cocycles (X.as ⟶ Y.as) 0 where
  toFun f := ⟨f.hom, f.mem_cocycles⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_homAddEquiv_apply {X Y : Z0 C} (f : X ⟶ Y) :
    (homAddEquiv X Y f : X.as ⟶ Y.as) = f.hom :=
  rfl

variable (C) in
/-- The faithful functor `Z⁰(C) ⥤ C`. -/
@[simps]
def forget : Z0 C ⥤ C where
  obj X := X.as
  map f := f.hom

instance : (forget C).Faithful where
  map_injective h := hom_ext h

instance : (forget C).Additive where

/-! ### The homotopy category `H⁰(C)` -/

variable (C) in
/-- Two morphisms of `Z⁰(C)` are homotopic if their difference is a coboundary. -/
def homotopic : HomRel (Z0 C) :=
  fun X Y f g => f.hom - g.hom ∈ coboundaries (X.as ⟶ Y.as) 0

theorem homotopic_iff {X Y : Z0 C} (f g : X ⟶ Y) :
    homotopic C f g ↔ f.hom - g.hom ∈ coboundaries (X.as ⟶ Y.as) 0 :=
  Iff.rfl

instance : Congruence (homotopic C) where
  equivalence :=
    { refl := fun f => by simp [homotopic_iff, zero_mem]
      symm := fun {f g} h => by
        rw [homotopic_iff, ← neg_sub]
        exact neg_mem h
      trans := fun {f g h} h₁ h₂ => by
        rw [homotopic_iff, ← sub_add_sub_cancel]
        exact add_mem h₁ h₂ }
  compLeft f g g' h := by
    rw [homotopic_iff, comp_hom, comp_hom, ← Preadditive.comp_sub]
    simpa using comp_mem_coboundaries_right f.mem_cocycles h
  compRight g h := by
    rw [homotopic_iff, comp_hom, comp_hom, ← Preadditive.sub_comp]
    simpa using comp_mem_coboundaries_left h g.mem_cocycles

end Z0

variable (C : Type u) [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-- The homotopy category `H⁰(C)` of a dg category: the quotient of `Z⁰(C)` by the relation
identifying two degree-`0` cocycles whose difference is a coboundary. -/
def H0 : Type u :=
  CategoryTheory.Quotient (Z0.homotopic C)

namespace H0

instance category : Category.{v} (H0 C) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (Z0.homotopic C)))

instance preadditive : Preadditive (H0 C) :=
  Quotient.preadditive (Z0.homotopic C) fun _ _ _ _ _ _ h₁ h₂ => by
    rw [Z0.homotopic_iff, Z0.add_hom, Z0.add_hom, add_sub_add_comm]
    exact add_mem h₁ h₂

/-- The quotient functor `Z⁰(C) ⥤ H⁰(C)`. -/
def quotient : Z0 C ⥤ H0 C :=
  CategoryTheory.Quotient.functor _

instance : (quotient C).Full := Quotient.full_functor _

instance : (quotient C).EssSurj := Quotient.essSurj_functor _

instance : (quotient C).Additive where

variable {C}

/-- Two morphisms of `Z⁰(C)` become equal in `H⁰(C)` if and only if their difference is a
coboundary. -/
theorem quotient_map_eq_iff {X Y : Z0 C} (f g : X ⟶ Y) :
    (quotient C).map f = (quotient C).map g ↔ f.hom - g.hom ∈ coboundaries (X.as ⟶ Y.as) 0 :=
  Quotient.functor_map_eq_iff _ f g

theorem quotient_map_eq_zero_iff {X Y : Z0 C} (f : X ⟶ Y) :
    (quotient C).map f = 0 ↔ f.hom ∈ coboundaries (X.as ⟶ Y.as) 0 := by
  rw [← Functor.map_zero (quotient C) X Y, quotient_map_eq_iff, Z0.zero_hom, sub_zero]

end H0

end DGCategory

end DG
