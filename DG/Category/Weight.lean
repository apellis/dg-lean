import DG.Bigraded.Basic
import DG.Category.Functor
import DG.Module.Corner

/-!
# The dg category of a dg ring with an internal grading

For a dg ring `A` with an internal (weight) grading `A = ⨁ k, A⟨k⟩` (`DG.InternalGrading`,
`DG.BigradedDGRing`), the dg category `C_A = DG.WeightCategory A` has the integers as objects
and the weight components as Hom complexes,

  `C_A(k, l) = A⟨l - k⟩`,

each with the cohomological grading and the differential restricted from `A`
(`DG.InternalGrading.instDGAddCommGroupWgrading`). Composition is multiplication in the same
order as in `SingleObj A`, `f ≫ g = g * f` (weights add: `A⟨m - l⟩ * A⟨l - k⟩ ⊆ A⟨m - k⟩`), and
the identity of `k` is `1 ∈ A⟨0⟩`. A dg module over `C_A` is then the same as a bigraded dg
`A`-module.

## Main definitions

* `DG.InternalGrading.instDGAddCommGroupWgrading`: the weight components `M⟨k⟩` of a dg abelian
  group with an internal grading are dg abelian groups.
* `DG.WeightCategory A` (objects `⟨k⟩` for `k : ℤ`), with `Category`, `Preadditive` and
  `DGCategory` instances.
* `DG.WeightCategory.shiftFunctor s`: the dg functor `k ↦ k + s`, the identity on Hom complexes
  (`A⟨l - k⟩ = A⟨(l + s) - (k + s)⟩`), and `DG.WeightCategory.shiftEquiv s`, the corresponding
  dg autoequivalence of `C_A`.
-/

open CategoryTheory DirectSum

universe u

namespace DG

/-! ### Weight components as dg abelian groups -/

namespace InternalGrading

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [InternalGrading M]

/-- The weight component `M⟨k⟩` of a dg abelian group with an internal grading is a dg abelian
group, with the restricted cohomological grading and differential. -/
noncomputable instance instDGAddCommGroupWgrading (k : ℤ) :
    DGAddCommGroup (wgrading (M := M) k) :=
  DGAddCommGroup.ofInjective (AddSubgroupClass.subtype (wgrading (M := M) k))
    Subtype.val_injective
    (((d : M →+ M).comp (AddSubgroupClass.subtype _)).codRestrict _ fun m => d_mem_wgrading m.2)
    (fun _ => rfl) fun n m => ⟨⟨_, decompose_grading_mem_wgrading m.2 n⟩, rfl⟩

theorem mem_grading_wgrading_iff {k n : ℤ} {m : wgrading (M := M) k} :
    m ∈ grading n ↔ (m : M) ∈ grading n :=
  Iff.rfl

@[simp]
theorem coe_d_wgrading {k : ℤ} (m : wgrading (M := M) k) : ((d m : wgrading k) : M) = d (m : M) :=
  rfl

/-- The homogeneous components of an element of `M⟨k⟩` are those of the underlying element of
`M`. -/
theorem coe_decompose_wgrading {k : ℤ} (m : wgrading (M := M) k) (n : ℤ) :
    ((decompose (grading (M := wgrading (M := M) k)) m n : wgrading (M := M) k) : M) =
      decompose (grading (M := M)) (m : M) n :=
  DGAddCommGroup.ofInjective_coe_decompose (AddSubgroupClass.subtype (wgrading (M := M) k))
    Subtype.val_injective _ (fun _ => rfl) _ m n

end InternalGrading

/-! ### The dg category `C_A` -/

/-- The dg category `C_A` of a ring `A` with a dg structure and an internal grading: its objects
are the integers (written `⟨k⟩`), and `C_A(k, l) = A⟨l - k⟩`. -/
@[ext]
structure WeightCategory (A : Type u) where
  /-- The integer underlying an object of `C_A`. -/
  as : ℤ

namespace WeightCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]

/-- The dg category `C_A`: `C_A(k, l) = A⟨l - k⟩`, with `f ≫ g = g * f` and `𝟙 k = 1`. -/
instance category : Category.{u} (WeightCategory A) where
  Hom k l := wgrading (M := A) (l.as - k.as)
  id k := ⟨1, by simpa using one_mem_wgrading (A := A)⟩
  comp {k l m} f g := ⟨g.1 * f.1, by simpa using mul_mem_wgrading g.2 f.2⟩
  id_comp f := Subtype.ext (mul_one f.1)
  comp_id f := Subtype.ext (one_mul f.1)
  assoc f g h := Subtype.ext (mul_assoc h.1 g.1 f.1).symm

/-- An element of `A⟨l - k⟩` as a morphism `k ⟶ l` of `C_A`. -/
abbrev homMk {k l : WeightCategory A} (a : A) (ha : a ∈ wgrading (M := A) (l.as - k.as)) :
    k ⟶ l :=
  ⟨a, ha⟩

theorem hom_ext {k l : WeightCategory A} {f g : k ⟶ l} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

theorem mem_wgrading {k l : WeightCategory A} (f : k ⟶ l) : f.1 ∈ wgrading (M := A) (l.as - k.as) :=
  f.2

@[simp] theorem id_val (k : WeightCategory A) : (𝟙 k : k ⟶ k).1 = 1 := rfl

@[simp] theorem comp_val {k l m : WeightCategory A} (f : k ⟶ l) (g : l ⟶ m) :
    (f ≫ g).1 = g.1 * f.1 := rfl

instance (k l : WeightCategory A) : AddCommGroup (k ⟶ l) :=
  inferInstanceAs (AddCommGroup (wgrading (M := A) (l.as - k.as)))

@[simp] theorem add_val {k l : WeightCategory A} (f g : k ⟶ l) : (f + g).1 = f.1 + g.1 := rfl
@[simp] theorem neg_val {k l : WeightCategory A} (f : k ⟶ l) : (-f).1 = -f.1 := rfl
@[simp] theorem zero_val (k l : WeightCategory A) : (0 : k ⟶ l).1 = 0 := rfl
@[simp] theorem sub_val {k l : WeightCategory A} (f g : k ⟶ l) : (f - g).1 = f.1 - g.1 := rfl
@[simp] theorem zsmul_val {k l : WeightCategory A} (n : ℤ) (f : k ⟶ l) : (n • f).1 = n • f.1 :=
  rfl

instance preadditive : Preadditive (WeightCategory A) where
  add_comp _ _ _ f f' g := hom_ext (by simp only [comp_val, add_val, mul_add])
  comp_add _ _ _ f g g' := hom_ext (by simp only [comp_val, add_val, add_mul])

/-- The Hom complexes of `C_A` are the weight components of `A`. -/
noncomputable instance instDGAddCommGroupHom (k l : WeightCategory A) :
    DGAddCommGroup (k ⟶ l) :=
  inferInstanceAs (DGAddCommGroup (wgrading (M := A) (l.as - k.as)))

theorem mem_grading_iff {k l : WeightCategory A} {n : ℤ} {f : k ⟶ l} :
    f ∈ grading n ↔ f.1 ∈ grading (M := A) n :=
  Iff.rfl

@[simp]
theorem d_val {k l : WeightCategory A} (f : k ⟶ l) : (d f).1 = d f.1 := rfl

/-! ### The shift of objects -/

variable (A) in
/-- The shift `k ↦ k + s` of the objects of `C_A`, the identity on Hom complexes:
`A⟨l - k⟩ = A⟨(l + s) - (k + s)⟩`. -/
@[simps obj]
def shiftFunctor (s : ℤ) : WeightCategory A ⥤ WeightCategory A where
  obj k := ⟨k.as + s⟩
  map {k l} f := ⟨f.1, by simp [add_sub_add_right_eq_sub, f.2]⟩

@[simp]
theorem shiftFunctor_map_val (s : ℤ) {k l : WeightCategory A} (f : k ⟶ l) :
    ((shiftFunctor A s).map f).1 = f.1 := rfl

instance (s : ℤ) : (shiftFunctor A s).Additive where

instance (s : ℤ) : (shiftFunctor A s).IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

/-- The isomorphism `k ≅ l` in `C_A` for `k.as = l.as`, given by `1 ∈ A⟨0⟩`. -/
@[simps]
def isoOfEq {k l : WeightCategory A} (h : k.as = l.as) : k ≅ l where
  hom := ⟨1, by rw [h, sub_self]; exact one_mem_wgrading⟩
  inv := ⟨1, by rw [h, sub_self]; exact one_mem_wgrading⟩
  hom_inv_id := Subtype.ext (mul_one 1)
  inv_hom_id := Subtype.ext (mul_one 1)

variable (A) in
/-- The shift `k ↦ k + s` is an autoequivalence of `C_A`, with inverse the shift by `-s`. -/
def shiftEquiv (s : ℤ) : WeightCategory A ≌ WeightCategory A :=
  CategoryTheory.Equivalence.mk (shiftFunctor A s) (shiftFunctor A (-s))
    (NatIso.ofComponents (fun k => isoOfEq (by simp))
      fun f => Subtype.ext (by simp))
    (NatIso.ofComponents (fun k => isoOfEq (by simp))
      fun f => Subtype.ext (by simp))

@[simp]
theorem shiftEquiv_functor (s : ℤ) : (shiftEquiv A s).functor = shiftFunctor A s := rfl

@[simp]
theorem shiftEquiv_inverse (s : ℤ) : (shiftEquiv A s).inverse = shiftFunctor A (-s) := rfl

variable [DGRing A]

/-- `C_A` is a dg category. -/
instance instDGCategory : DGCategory (WeightCategory A) where
  comp_mem' {_ _ _ i j f g} hf hg := by
    rw [mem_grading_iff, comp_val, add_comm]
    exact mul_mem_grading hg hf
  id_mem' _ := one_mem_grading (A := A)
  d_comp' {_ _ _ j} f g hg := Subtype.ext (by
    change d (g.1 * f.1) = d g.1 * f.1 + (koszulSign j • (g.1 * d f.1))
    exact d_mul hg f.1)

end WeightCategory

end DG
