import DG.Graded.Regrading
import DG.Graded.ModuleCat
import Mathlib.CategoryTheory.Equivalence

universe v u

/-!
# The periodization equivalence of graded module categories

For a `ℤ/2`-graded ring `(B, ℬ)`, `ℤ/2`-graded `B`-modules are the same as `ℤ`-graded modules
over the 2-periodic ring `Periodize ℬ` of `DG.Graded.Regrading`:

* `DG.GradedModuleCat.periodize ℬ`: the functor `M ↦ Periodize M = ⨁ n : ℤ, M^{n mod 2}`;
* `DG.Unperiodize ℬ 𝒩 = N⁰ ⊕ N¹` for a `ℤ`-graded `Periodize ℬ`-module `(N, 𝒩)`: a `ℤ/2`-graded
  `B`-module, graded by `j ↦ N^{j.val}`, on which `b ∈ B^{i}` acts on `x ∈ N^{j.val}` as `b`
  placed in degree `(i + j).val - j.val` of `Periodize ℬ` (so through `u⁻¹`, the inverse of the
  periodicity unit, when `i = j = 1`); `DG.GradedModuleCat.unperiodize ℬ` is the functor;
* the unit `M ≅ (Periodize M)⁰ ⊕ (Periodize M)¹` (`DG.GradedModuleCat.unitIso`) and the counit
  `Periodize (N⁰ ⊕ N¹) ≅ N` (`DG.GradedModuleCat.counitIso`), which uses the isomorphisms
  `Nⁿ ≅ N^{n mod 2}` given by powers of the periodicity unit (`DG.Periodize.evenOne`);
* `DG.GradedModuleCat.periodizeEquivalence ℬ :
  GradedModuleCat ℬ ≌ GradedModuleCat (periodizeGrading ℬ)`.
-/

noncomputable section

namespace DG

open CategoryTheory DirectSum

section Unperiodize

variable {τ : Type*} (ℬ : ZMod 2 → τ) {N : Type*} [AddCommGroup N] (𝒩 : ℤ → AddSubgroup N)

/-- The degree-`j.val` piece of a `ℤ`-grading, for `j ∈ ℤ/2`: the pieces in degrees `0` and `1`. -/
def lowGrading (j : ZMod 2) : AddSubgroup N := 𝒩 (j.val : ℤ)

/-- The `ℤ/2`-graded `B`-module `N⁰ ⊕ N¹` attached to a `ℤ`-graded module `N` over the
periodization `Periodize ℬ` of a `ℤ/2`-graded ring `B`. It is graded by `j ∈ ℤ/2` with degree-`j`
piece `N^{j.val}`; an element `b ∈ B^{i}` acts on `x ∈ N^{j.val}` as `b` placed in degree
`(i + j).val - j.val` of `Periodize ℬ`, so that `b • x ∈ N^{(i + j).val}`. -/
@[nolint unusedArguments]
def Unperiodize (_ℬ : ZMod 2 → τ) (𝒩 : ℤ → AddSubgroup N) : Type _ :=
  ⨁ j : ZMod 2, ↥(lowGrading 𝒩 j)

instance : AddCommGroup (Unperiodize ℬ 𝒩) :=
  inferInstanceAs (AddCommGroup (⨁ j : ZMod 2, ↥(lowGrading 𝒩 j)))

namespace Unperiodize

theorem cast_sub_val (i j : ZMod 2) : ((((i + j).val : ℤ) - (j.val : ℤ) : ℤ) : ZMod 2) = i := by
  rw [Int.cast_sub, intCast_val_zmodTwo, intCast_val_zmodTwo, add_sub_cancel_right]

/-- The inclusion of the degree-`j` piece `N^{j.val}`. -/
def of (j : ZMod 2) : lowGrading 𝒩 j →+ Unperiodize ℬ 𝒩 :=
  DirectSum.of (fun j => ↥(lowGrading 𝒩 j)) j

variable {ℬ 𝒩}

@[elab_as_elim]
theorem induction_on {P : Unperiodize ℬ 𝒩 → Prop} (y : Unperiodize ℬ 𝒩) (zero : P 0)
    (of : ∀ (j : ZMod 2) (x : lowGrading 𝒩 j), P (of ℬ 𝒩 j x))
    (add : ∀ x y, P x → P y → P (x + y)) : P y :=
  DirectSum.induction_on (β := fun j => ↥(lowGrading 𝒩 j)) y zero of add

theorem addHom_ext {X : Type*} [AddCommMonoid X] {f g : Unperiodize ℬ 𝒩 →+ X}
    (h : ∀ (j : ZMod 2) (x : lowGrading 𝒩 j), f (of ℬ 𝒩 j x) = g (of ℬ 𝒩 j x)) : f = g :=
  DirectSum.addHom_ext (β := fun j => ↥(lowGrading 𝒩 j)) h

variable (ℬ 𝒩)

/-- The canonical `ℤ/2`-grading of `Unperiodize ℬ 𝒩`. -/
def grading (j : ZMod 2) : AddSubgroup (Unperiodize ℬ 𝒩) := summand (fun j => ↥(lowGrading 𝒩 j)) j

instance : Decomposition (grading ℬ 𝒩) :=
  inferInstanceAs (Decomposition (summand fun j => ↥(lowGrading 𝒩 j)))

variable {ℬ 𝒩}

theorem of_mem_grading (j : ZMod 2) (x : lowGrading 𝒩 j) : of ℬ 𝒩 j x ∈ grading ℬ 𝒩 j :=
  of_mem_summand (β := fun j => ↥(lowGrading 𝒩 j)) j x

theorem mem_grading_iff {j : ZMod 2} {y : Unperiodize ℬ 𝒩} :
    y ∈ grading ℬ 𝒩 j ↔ ∃ x, of ℬ 𝒩 j x = y := mem_summand

/-- The additive map `N⁰ ⊕ N¹ → N` summing the components. -/
def fold : Unperiodize ℬ 𝒩 →+ N :=
  DirectSum.toAddMonoid fun j => (lowGrading 𝒩 j).subtype

@[simp]
theorem fold_of (j : ZMod 2) (x : lowGrading 𝒩 j) : fold (of ℬ 𝒩 j x) = x := by
  exact DirectSum.toAddMonoid_of (fun j => (lowGrading 𝒩 j).subtype) j x

theorem fold_mem {j : ZMod 2} {y : Unperiodize ℬ 𝒩} (hy : y ∈ grading ℬ 𝒩 j) :
    fold y ∈ lowGrading 𝒩 j := by
  obtain ⟨x, rfl⟩ := mem_grading_iff.mp hy
  rw [fold_of]; exact x.2

variable {N' : Type*} [AddCommGroup N'] {𝒩' : ℤ → AddSubgroup N'}

variable (ℬ) in
/-- The map `N⁰ ⊕ N¹ → N'⁰ ⊕ N'¹` induced by maps on the pieces of degree `0` and `1`. -/
def map (f : ∀ j : ZMod 2, lowGrading 𝒩 j →+ lowGrading 𝒩' j) :
    Unperiodize ℬ 𝒩 →+ Unperiodize ℬ 𝒩' :=
  DirectSum.map f

@[simp]
theorem map_of (f : ∀ j : ZMod 2, lowGrading 𝒩 j →+ lowGrading 𝒩' j) (j : ZMod 2)
    (x : lowGrading 𝒩 j) : map ℬ f (of ℬ 𝒩 j x) = of ℬ 𝒩' j (f j x) :=
  DirectSum.map_of f j x

end Unperiodize

end Unperiodize

section Module

variable {B τ : Type*} [Ring B] [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ZMod 2 → τ)
  [GradedRing ℬ]
variable {N : Type*} [AddCommGroup N] [Module (Periodize ℬ) N] (𝒩 : ℤ → AddSubgroup N)
  [SetLike.GradedSMul (periodizeGrading ℬ) 𝒩]

namespace Unperiodize

variable {ℬ 𝒩}

theorem smul_mem_aux {i j : ZMod 2} {b : B} (hb : b ∈ ℬ i) {x : N} (hx : x ∈ lowGrading 𝒩 j) :
    Periodize.mk ℬ ((i + j).val - j.val) b (by rwa [cast_sub_val]) • x ∈ lowGrading 𝒩 (i + j) := by
  have := SetLike.GradedSMul.smul_mem (Periodize.mk_mem (ℳ := ℬ) ((i + j).val - j.val : ℤ)
    (m := b) (by rwa [cast_sub_val])) (B := 𝒩) (show x ∈ 𝒩 (j.val : ℤ) from hx)
  rwa [vadd_eq_add, sub_add_cancel] at this

variable (ℬ 𝒩)

/-- The graded action `B^{i} × N^{j.val} → N^{(i + j).val}`. -/
def gsmul (i j : ZMod 2) (b : ℬ i) (x : lowGrading 𝒩 j) : lowGrading 𝒩 (i + j) :=
  ⟨_, smul_mem_aux b.2 x.2⟩

instance gmodule : Gmodule (fun i => ↥(ℬ i)) (fun j => ↥(lowGrading 𝒩 j)) where
  smul {i j} b x := gsmul ℬ 𝒩 i j b x
  one_smul := by
    rintro ⟨j, x⟩
    refine Sigma.subtype_ext (zero_add j) ?_
    change Periodize.mk ℬ ((0 + j).val - j.val) 1 _ • (x : N) = x
    rw [Periodize.mk_congr (show ((0 + j).val : ℤ) - j.val = 0 by rw [zero_add, sub_self]) rfl _
      (by simpa using SetLike.GradedOne.one_mem (A := ℬ)), ← Periodize.one_eq_mk, one_smul]
  mul_smul := by
    rintro ⟨i, a⟩ ⟨i', a'⟩ ⟨j, x⟩
    refine Sigma.subtype_ext (add_assoc i i' j) ?_
    change Periodize.mk ℬ ((i + i' + j).val - j.val) ((a : B) * a') _ • (x : N) =
      Periodize.mk ℬ ((i + (i' + j)).val - (i' + j).val) (a : B) _ •
        Periodize.mk ℬ ((i' + j).val - j.val) (a' : B) _ • (x : N)
    rw [← mul_smul, Periodize.mk_mul_mk]
    congr 1
    exact Periodize.mk_congr (by rw [add_assoc]; ring) rfl _ _
  smul_add := by
    intro i j b x y
    exact Subtype.ext (smul_add _ (x : N) y)
  smul_zero := by
    intro i j b
    exact Subtype.ext (smul_zero _)
  add_smul := by
    intro i j b b' x
    refine Subtype.ext ?_
    change Periodize.mk ℬ _ ((b : B) + b') _ • (x : N) = Periodize.mk ℬ _ (b : B) _ • (x : N) +
      Periodize.mk ℬ _ (b' : B) _ • (x : N)
    rw [Periodize.mk_add, add_smul]
  zero_smul := by
    intro i j x
    refine Subtype.ext ?_
    change Periodize.mk ℬ _ (0 : B) _ • (x : N) = 0
    rw [Periodize.mk_zero, zero_smul]

instance moduleDirectSum : Module (⨁ i, ↥(ℬ i)) (Unperiodize ℬ 𝒩) :=
  inferInstanceAs (Module (⨁ i, ↥(ℬ i)) (⨁ j : ZMod 2, ↥(lowGrading 𝒩 j)))

instance module : Module B (Unperiodize ℬ 𝒩) :=
  Module.compHom _ (decomposeRingEquiv ℬ).toRingHom

variable {ℬ 𝒩}

theorem smul_of {i j : ZMod 2} {b : B} (hb : b ∈ ℬ i) (x : lowGrading 𝒩 j) :
    b • of ℬ 𝒩 j x = of ℬ 𝒩 (i + j) (gsmul ℬ 𝒩 i j ⟨b, hb⟩ x) := by
  change (decompose ℬ b) • (DirectSum.of (fun j => ↥(lowGrading 𝒩 j)) j x) = _
  rw [decompose_of_mem ℬ hb]
  exact DirectSum.Gmodule.of_smul_of _ _ _ _


instance : SetLike.GradedSMul ℬ (grading ℬ 𝒩) where
  smul_mem i j b y hb hy := by
    obtain ⟨x, rfl⟩ := mem_grading_iff.mp hy
    rw [smul_of hb]; exact of_mem_grading _ _


end Unperiodize

end Module


namespace Periodize

variable {B τ : Type*} [Ring B] [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ZMod 2 → τ)
  [SetLike.GradedMonoid ℬ]

theorem cast_sub_val_cast (n : ℤ) : ((n - ((n : ZMod 2).val : ℤ) : ℤ) : ZMod 2) = 0 := by
  rw [Int.cast_sub, intCast_val_zmodTwo, sub_self]

theorem cast_val_cast_sub (n : ℤ) : ((((n : ZMod 2).val : ℤ) - n : ℤ) : ZMod 2) = 0 := by
  rw [Int.cast_sub, intCast_val_zmodTwo, sub_self]

/-- The identity `1 ∈ B^{0̄}` placed in an even degree `k`, i.e. the power `u^(k/2)` of the
periodicity unit. -/
def evenOne (k : ℤ) (hk : (k : ZMod 2) = 0) : Periodize ℬ :=
  mk ℬ k 1 (by rw [hk]; exact SetLike.GradedOne.one_mem (A := ℬ))

variable {ℬ}

theorem evenOne_mul_evenOne {k l : ℤ} (hk : (k : ZMod 2) = 0) (hl : (l : ZMod 2) = 0) :
    evenOne ℬ k hk * evenOne ℬ l hl =
      evenOne ℬ (k + l) (by rw [Int.cast_add, hk, hl, add_zero]) := by
  rw [evenOne, evenOne, mk_mul_mk]; exact mk_congr rfl (one_mul 1) _ _

theorem evenOne_zero : evenOne ℬ 0 Int.cast_zero = 1 := rfl

theorem evenOne_eq_one {k : ℤ} (hk : (k : ZMod 2) = 0) (h : k = 0) : evenOne ℬ k hk = 1 := by
  subst h; rfl

theorem evenOne_mul_mk {k n : ℤ} (hk : (k : ZMod 2) = 0) {b : B} (hb : b ∈ ℬ n) :
    evenOne ℬ k hk * mk ℬ n b hb =
      mk ℬ (k + n) b (by rw [Int.cast_add, hk, zero_add]; exact hb) := by
  rw [evenOne, mk_mul_mk]; exact mk_congr rfl (one_mul b) _ _

end Periodize


namespace GradedModuleCat

variable {B : Type u} [Ring B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B] (ℬ : ZMod 2 → τ)
  [GradedRing ℬ]

/-! ### The periodization functor -/

/-- The periodization `Periodize ℳ = ⨁ n : ℤ, ℳ^{n mod 2}` of a `ℤ/2`-graded `B`-module, as a
`ℤ`-graded module over `Periodize ℬ`. -/
abbrev periodizeObj (M : GradedModuleCat.{v} ℬ) : GradedModuleCat.{v} (periodizeGrading ℬ) :=
  of (periodizeGrading ℬ) (Periodize M.grading) (periodizeGrading M.grading)

variable {ℬ}

/-- The componentwise map `Periodize M → Periodize N` induced by a morphism `M ⟶ N`. -/
def periodizeHom {M N : GradedModuleCat.{v} ℬ} (f : M ⟶ N) :
    Periodize M.grading →+ Periodize N.grading :=
  DirectSum.map fun n => f.restrict (n : ZMod 2)

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem periodizeHom_mk {M N : GradedModuleCat.{v} ℬ} (f : M ⟶ N) (n : ℤ) (m : M)
    (hm : m ∈ M.grading n) :
    periodizeHom f (Periodize.mk M.grading n m hm) =
      Periodize.mk N.grading n (f.hom m) (f.map_mem hm) :=
  DirectSum.map_of _ _ _

variable (ℬ)

/-- The periodization of a morphism. -/
def periodizeMap {M N : GradedModuleCat.{v} ℬ} (f : M ⟶ N) :
    periodizeObj ℬ M ⟶ periodizeObj ℬ N where
  hom :=
    { toFun := periodizeHom f
      map_add' := map_add _
      map_smul' := fun p x => by
        refine map_smul_of_homogeneous (periodizeGrading ℬ) (periodizeGrading M.grading)
          (periodizeHom f) (fun i j a m ha hm => ?_) p x
        obtain ⟨a, ha, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp ha
        obtain ⟨m, hm, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hm
        rw [Periodize.mk_smul_mk, periodizeHom_mk, periodizeHom_mk, Periodize.mk_smul_mk]
        exact Periodize.mk_congr rfl (f.hom.map_smul a m) _ _ }
  map_mem' := by
    intro i x hx
    obtain ⟨m, hm, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hx
    change periodizeHom f _ ∈ _
    rw [periodizeHom_mk]; exact Periodize.mk_mem _ _

@[simp]
theorem periodizeMap_hom_mk {M N : GradedModuleCat.{v} ℬ} (f : M ⟶ N) (n : ℤ) (m : M)
    (hm : m ∈ M.grading n) :
    (periodizeMap ℬ f).hom (Periodize.mk M.grading n m hm) =
      Periodize.mk N.grading n (f.hom m) (f.map_mem hm) :=
  periodizeHom_mk f n m hm

/-- The periodization functor from `ℤ/2`-graded `B`-modules to `ℤ`-graded modules over the
periodization `Periodize ℬ` of `B`. -/
def periodize : GradedModuleCat.{v} ℬ ⥤ GradedModuleCat.{v} (periodizeGrading ℬ) where
  obj := periodizeObj ℬ
  map := periodizeMap ℬ
  map_id M := by
    refine hom_ext_homogeneous fun i x hx => ?_
    obtain ⟨m, hm, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hx
    rw [periodizeMap_hom_mk]; rfl
  map_comp f g := by
    refine hom_ext_homogeneous fun i x hx => ?_
    obtain ⟨m, hm, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hx
    change _ = (periodizeMap ℬ g).hom ((periodizeMap ℬ f).hom _)
    rw [periodizeMap_hom_mk, periodizeMap_hom_mk, periodizeMap_hom_mk]; rfl

/-! ### The functor `N ↦ N⁰ ⊕ N¹` -/

/-- The `ℤ/2`-graded `B`-module `N⁰ ⊕ N¹` of a `ℤ`-graded `Periodize ℬ`-module `N`. -/
abbrev unperiodizeObj (N : GradedModuleCat.{v} (periodizeGrading ℬ)) : GradedModuleCat.{v} ℬ :=
  of ℬ (Unperiodize ℬ N.grading) (Unperiodize.grading ℬ N.grading)

/-- The map `N⁰ ⊕ N¹ → N'⁰ ⊕ N'¹` induced by a morphism `N ⟶ N'`. -/
def unperiodizeMap {N N' : GradedModuleCat.{v} (periodizeGrading ℬ)} (g : N ⟶ N') :
    unperiodizeObj ℬ N ⟶ unperiodizeObj ℬ N' where
  hom :=
    { toFun := Unperiodize.map ℬ fun j => g.restrict (j.val : ℤ)
      map_add' := map_add _
      map_smul' := fun b y => by
        refine map_smul_of_homogeneous ℬ (Unperiodize.grading ℬ N.grading)
          (Unperiodize.map ℬ fun j => g.restrict (j.val : ℤ)) (fun i j b y hb hy => ?_) b y
        obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
        rw [Unperiodize.smul_of hb, Unperiodize.map_of, Unperiodize.map_of, Unperiodize.smul_of hb]
        congr 1
        exact Subtype.ext (g.hom.map_smul _ (x : N)) }
  map_mem' := by
    intro j y hy
    obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
    change Unperiodize.map ℬ _ _ ∈ _
    rw [Unperiodize.map_of]; exact Unperiodize.of_mem_grading _ _

@[simp]
theorem unperiodizeMap_hom_of {N N' : GradedModuleCat.{v} (periodizeGrading ℬ)} (g : N ⟶ N')
    (j : ZMod 2) (x : lowGrading N.grading j) :
    (unperiodizeMap ℬ g).hom (Unperiodize.of ℬ N.grading j x) =
      Unperiodize.of ℬ N'.grading j (g.restrict (j.val : ℤ) x) :=
  Unperiodize.map_of _ j x

/-- The functor `N ↦ N⁰ ⊕ N¹` from `ℤ`-graded `Periodize ℬ`-modules to `ℤ/2`-graded
`B`-modules. -/
def unperiodize : GradedModuleCat.{v} (periodizeGrading ℬ) ⥤ GradedModuleCat.{v} ℬ where
  obj := unperiodizeObj ℬ
  map := unperiodizeMap ℬ
  map_id N := by
    refine hom_ext_homogeneous fun j y hy => ?_
    obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
    rw [unperiodizeMap_hom_of]; rfl
  map_comp f g := by
    refine hom_ext_homogeneous fun j y hy => ?_
    obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
    change _ = (unperiodizeMap ℬ g).hom ((unperiodizeMap ℬ f).hom _)
    rw [unperiodizeMap_hom_of, unperiodizeMap_hom_of, unperiodizeMap_hom_of]; rfl

/-! ### The unit `M ≅ (Periodize M)⁰ ⊕ (Periodize M)¹` -/

section Unit

variable {ℬ} (M : GradedModuleCat.{v} ℬ)

/-- The additive map `M → (Periodize M)⁰ ⊕ (Periodize M)¹` sending `m ∈ M^{j}` to `m` placed in
degree `j.val`. -/
def unitHom : M →+ Unperiodize ℬ (periodizeGrading M.grading) :=
  ∑ j : ZMod 2, (Unperiodize.of ℬ (periodizeGrading M.grading) j).comp
    ((Periodize.single M.grading (j.val : ℤ)).codRestrict _
      fun m => Periodize.single_mem (ℳ := M.grading) _ m)

variable {M}

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem unitHom_of_mem {j : ZMod 2} {m : M} (hm : m ∈ M.grading j) :
    unitHom M m = Unperiodize.of ℬ (periodizeGrading M.grading) j
      ⟨Periodize.mk M.grading (j.val : ℤ) m (by rwa [intCast_val_zmodTwo]),
        Periodize.mk_mem _ _⟩ := by
  simp only [unitHom, AddMonoidHom.finset_sum_apply, AddMonoidHom.comp_apply]
  rw [Finset.sum_eq_single j]
  · congr 1
    exact Subtype.ext (Periodize.single_of_mem _)
  · intro j' _ hj'
    have h0 : ((Periodize.single M.grading (j'.val : ℤ)).codRestrict
        (lowGrading (periodizeGrading M.grading) j')
        (fun m => Periodize.single_mem (ℳ := M.grading) _ m) m) = 0 :=
      Subtype.ext (Periodize.single_of_mem_ne hm (by rw [intCast_val_zmodTwo]; exact hj'.symm))
    rw [h0, map_zero]
  · simp

/-- The inverse of `unitHom`: sum the components and fold. -/
def unitInv : Unperiodize ℬ (periodizeGrading M.grading) →+ M :=
  (Periodize.fold M.grading).comp Unperiodize.fold

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem unitInv_unitHom (m : M) : unitInv (unitHom M m) = m := by
  induction m using Decomposition.inductionOn M.grading with
  | zero => simp
  | homogeneous m =>
    rw [unitHom_of_mem m.2, unitInv, AddMonoidHom.comp_apply, Unperiodize.fold_of]
    exact Periodize.fold_mk _ _ _ _
  | add m m' hm hm' => rw [map_add, map_add, hm, hm']

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem unitHom_unitInv (y : Unperiodize ℬ (periodizeGrading M.grading)) :
    unitHom M (unitInv y) = y := by
  induction y using Unperiodize.induction_on with
  | zero => simp
  | of j x =>
    obtain ⟨x, hx⟩ := x
    obtain ⟨m, hm, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp
      (show x ∈ periodizeGrading M.grading (j.val : ℤ) from hx)
    rw [unitInv, AddMonoidHom.comp_apply, Unperiodize.fold_of]
    change unitHom M (Periodize.fold M.grading (Periodize.mk M.grading _ m hm)) = _
    rw [Periodize.fold_mk, unitHom_of_mem (by rwa [intCast_val_zmodTwo] at hm)]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem unitHom_smul (b : B) (m : M) : unitHom M (b • m) = b • unitHom M m := by
  refine map_smul_of_homogeneous ℬ M.grading (unitHom M) (fun i j b m hb hm => ?_) b m
  rw [unitHom_of_mem (SetLike.GradedSMul.smul_mem hb hm), unitHom_of_mem hm,
    Unperiodize.smul_of hb]
  congr 1
  refine Subtype.ext ?_
  change _ = Periodize.mk ℬ _ b _ • Periodize.mk M.grading _ m _
  rw [Periodize.mk_smul_mk]
  exact Periodize.mk_congr (by rw [vadd_eq_add, sub_add_cancel]) rfl _ _

variable (M)

/-- The unit isomorphism `M ≅ (Periodize M)⁰ ⊕ (Periodize M)¹`. -/
def unitIso : M ≅ (periodize ℬ ⋙ unperiodize ℬ).obj M :=
  isoMk
    { toFun := unitHom M
      invFun := unitInv
      left_inv := unitInv_unitHom
      right_inv := unitHom_unitInv
      map_add' := map_add _
      map_smul' := unitHom_smul }
    (fun j m hm => by
      change unitHom M m ∈ _
      rw [unitHom_of_mem hm]; exact Unperiodize.of_mem_grading _ _)
    (fun j y hy => by
      obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
      obtain ⟨x, hx⟩ := x
      obtain ⟨m, hm, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp
        (show x ∈ periodizeGrading M.grading (j.val : ℤ) from hx)
      change unitInv (Unperiodize.of ℬ _ j ⟨Periodize.mk M.grading _ m hm, _⟩) ∈ _
      rw [unitInv, AddMonoidHom.comp_apply, Unperiodize.fold_of]
      change Periodize.fold M.grading (Periodize.mk M.grading _ m hm) ∈ _
      rw [Periodize.fold_mk]
      rwa [intCast_val_zmodTwo] at hm)

theorem unitIso_hom_hom_of_mem {j : ZMod 2} {m : M} (hm : m ∈ M.grading j) :
    (unitIso M).hom.hom m = Unperiodize.of ℬ (periodizeGrading M.grading) j
      ⟨Periodize.mk M.grading (j.val : ℤ) m (by rwa [intCast_val_zmodTwo]),
        Periodize.mk_mem _ _⟩ :=
  unitHom_of_mem hm

end Unit

/-! ### The counit `Periodize (N⁰ ⊕ N¹) ≅ N` -/

section Counit

variable {ℬ} (N : GradedModuleCat.{v} (periodizeGrading ℬ))

/-- The degree-`n` component of the counit: `y ∈ (N⁰ ⊕ N¹)^{n mod 2}`, placed in degree `n`, is
sent to `u^((n - n mod 2) / 2) • y ∈ Nⁿ`. -/
def counitHom : Periodize (Unperiodize.grading ℬ N.grading) →+ N :=
  DirectSum.toAddMonoid fun n : ℤ =>
    (DistribMulAction.toAddMonoidHom N
      (Periodize.evenOne ℬ (n - ((n : ZMod 2).val : ℤ)) (Periodize.cast_sub_val_cast n))).comp
      (Unperiodize.fold.comp (AddSubmonoidClass.subtype _))

variable {N}

theorem counitHom_mk (n : ℤ) (y : Unperiodize ℬ N.grading)
    (hy : y ∈ Unperiodize.grading ℬ N.grading n) :
    counitHom N (Periodize.mk _ n y hy) =
      Periodize.evenOne ℬ (n - ((n : ZMod 2).val : ℤ)) (Periodize.cast_sub_val_cast n) •
        Unperiodize.fold y :=
  DirectSum.toAddMonoid_of (β := fun n => ↥(periodicGrading (Unperiodize.grading ℬ N.grading) n))
    _ n ⟨y, hy⟩

theorem evenOne_smul_mem {k n : ℤ} (hk : (k : ZMod 2) = 0) {x : N} (hx : x ∈ N.grading n) :
    Periodize.evenOne ℬ k hk • x ∈ N.grading (k + n) :=
  SetLike.GradedSMul.smul_mem (Periodize.mk_mem k _) hx

theorem evenOne_smul_evenOne_smul {k l : ℤ} (hk : (k : ZMod 2) = 0) (hl : (l : ZMod 2) = 0)
    (h : k + l = 0) (x : N) : Periodize.evenOne ℬ k hk • Periodize.evenOne ℬ l hl • x = x := by
  rw [← mul_smul, Periodize.evenOne_mul_evenOne, Periodize.evenOne_eq_one _ h, one_smul]

variable (N)

/-- The inverse of the counit: `x ∈ Nⁿ` is sent to `u^((n mod 2 - n) / 2) • x ∈ N^{n mod 2}`,
placed in degree `n`. -/
def counitInv : N →+ Periodize (Unperiodize.grading ℬ N.grading) :=
  liftHomogeneous N.grading fun n =>
    (Periodize.ofHom (Unperiodize.grading ℬ N.grading) n).comp
      (((Unperiodize.of ℬ N.grading (n : ZMod 2)).codRestrict
          (periodicGrading (Unperiodize.grading ℬ N.grading) n)
          (Unperiodize.of_mem_grading _)).comp
        (((DistribMulAction.toAddMonoidHom N
            (Periodize.evenOne ℬ (((n : ZMod 2).val : ℤ) - n) (Periodize.cast_val_cast_sub n))).comp
          (N.grading n).subtype).codRestrict (lowGrading N.grading (n : ZMod 2)) fun x => by
            have := evenOne_smul_mem (Periodize.cast_val_cast_sub n) x.2
            rw [sub_add_cancel] at this
            exact this))

variable {N}

theorem counitInv_of_mem {n : ℤ} {x : N} (hx : x ∈ N.grading n) :
    counitInv N x = Periodize.mk _ n (Unperiodize.of ℬ N.grading (n : ZMod 2)
      ⟨Periodize.evenOne ℬ (((n : ZMod 2).val : ℤ) - n) (Periodize.cast_val_cast_sub n) • x,
        by
          have := evenOne_smul_mem (Periodize.cast_val_cast_sub n) hx
          rw [sub_add_cancel] at this
          exact this⟩) (Unperiodize.of_mem_grading _ _) := by
  rw [counitInv, liftHomogeneous_of_mem N.grading _ hx]; rfl

theorem counitHom_counitInv (x : N) : counitHom N (counitInv N x) = x := by
  induction x using Decomposition.inductionOn N.grading with
  | zero => simp
  | homogeneous x =>
    rw [counitInv_of_mem x.2, counitHom_mk, Unperiodize.fold_of]
    exact evenOne_smul_evenOne_smul _ _ (by ring) _
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']

theorem counitHom_mem {n : ℤ} {y : Unperiodize ℬ N.grading}
    (hy : y ∈ Unperiodize.grading ℬ N.grading n) :
    Periodize.evenOne ℬ (n - ((n : ZMod 2).val : ℤ)) (Periodize.cast_sub_val_cast n) •
      Unperiodize.fold y ∈ N.grading n := by
  have := evenOne_smul_mem (Periodize.cast_sub_val_cast n) (Unperiodize.fold_mem (ℬ := ℬ) hy)
  rwa [sub_add_cancel] at this

theorem counitInv_counitHom (z : Periodize (Unperiodize.grading ℬ N.grading)) :
    counitInv N (counitHom N z) = z := by
  induction z using Periodize.induction_on with
  | zero => simp
  | mk n y hy =>
    rw [counitHom_mk, counitInv_of_mem (counitHom_mem hy)]
    obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
    refine Periodize.mk_congr rfl (congrArg _ (Subtype.ext ?_)) _ _
    change Periodize.evenOne ℬ _ _ • Periodize.evenOne ℬ _ _ •
      Unperiodize.fold (Unperiodize.of ℬ N.grading _ x) = (x : N)
    rw [Unperiodize.fold_of]
    exact evenOne_smul_evenOne_smul _ _ (by ring) _
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

theorem counitHom_smul (p : Periodize ℬ) (z : Periodize (Unperiodize.grading ℬ N.grading)) :
    counitHom N (p • z) = p • counitHom N z := by
  refine map_smul_of_homogeneous (periodizeGrading ℬ)
    (periodizeGrading (Unperiodize.grading ℬ N.grading)) (counitHom N)
    (fun i j p z hp hz => ?_) p z
  obtain ⟨b, hb, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hp
  obtain ⟨y, hy, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hz
  obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
  rw [Periodize.mk_smul_mk, counitHom_mk, counitHom_mk]
  rw [Unperiodize.smul_of hb, Unperiodize.fold_of, Unperiodize.fold_of]
  change Periodize.evenOne ℬ _ _ • (Periodize.mk ℬ _ b _ • (x : N)) =
    Periodize.mk ℬ i b hb • Periodize.evenOne ℬ _ _ • (x : N)
  rw [← mul_smul, ← mul_smul, Periodize.evenOne, Periodize.evenOne, Periodize.mk_mul_mk,
    Periodize.mk_mul_mk]
  congr 1
  exact Periodize.mk_congr (by rw [Int.cast_add]; ring)
    ((one_mul b).trans (mul_one b).symm) _ _

variable (N)

/-- The counit as a linear equivalence. -/
def counitEquiv : Periodize (Unperiodize.grading ℬ N.grading) ≃ₗ[Periodize ℬ] N where
  toFun := counitHom N
  invFun := counitInv N
  left_inv := counitInv_counitHom
  right_inv := counitHom_counitInv
  map_add' := map_add _
  map_smul' := counitHom_smul

theorem counitEquiv_apply (z : Periodize (Unperiodize.grading ℬ N.grading)) :
    counitEquiv N z = counitHom N z := rfl

/-- The counit isomorphism `Periodize (N⁰ ⊕ N¹) ≅ N`. -/
def counitIso : periodizeObj ℬ (unperiodizeObj ℬ N) ≅ N :=
  isoMk (counitEquiv N)
    (fun n z hz => by
      obtain ⟨y, hy, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hz
      rw [counitEquiv_apply, counitHom_mk]; exact counitHom_mem hy)
    (fun n x hx => by
      change counitInv N x ∈ periodizeGrading (Unperiodize.grading ℬ N.grading) n
      rw [counitInv_of_mem hx]; exact Periodize.mk_mem _ _)

variable {N}

theorem counitIso_hom_hom_mk (n : ℤ) (y : Unperiodize ℬ N.grading)
    (hy : y ∈ Unperiodize.grading ℬ N.grading n) :
    (counitIso N).hom.hom (Periodize.mk _ n y hy) =
      Periodize.evenOne ℬ (n - ((n : ZMod 2).val : ℤ)) (Periodize.cast_sub_val_cast n) •
        Unperiodize.fold y :=
  counitHom_mk n y hy

end Counit

/-! ### The equivalence -/

/-- The unit of the periodization equivalence. -/
def periodizeUnitIso : 𝟭 (GradedModuleCat.{v} ℬ) ≅ periodize ℬ ⋙ unperiodize ℬ :=
  NatIso.ofComponents unitIso fun {M M'} f => by
    refine hom_ext_homogeneous fun j m hm => ?_
    change unitHom M' (f.hom m) =
      (unperiodizeMap ℬ (periodizeMap ℬ f)).hom (unitHom M m)
    rw [unitHom_of_mem (f.map_mem hm), unitHom_of_mem (M := M) hm, unperiodizeMap_hom_of]
    congr 1
    exact Subtype.ext (periodizeMap_hom_mk ℬ f _ m _).symm

/-- The counit of the periodization equivalence. -/
def periodizeCounitIso :
    unperiodize ℬ ⋙ periodize ℬ ≅ 𝟭 (GradedModuleCat.{v} (periodizeGrading ℬ)) :=
  NatIso.ofComponents counitIso fun {N N'} g => by
    refine hom_ext_homogeneous fun n z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Periodize.mem_periodizeGrading_iff.mp hz
    obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
    show counitHom N' ((periodizeMap ℬ (unperiodizeMap ℬ g)).hom
        (Periodize.mk _ n (Unperiodize.of ℬ N.grading _ x) hy)) =
      g.hom (counitHom N (Periodize.mk _ n (Unperiodize.of ℬ N.grading _ x) hy))
    rw [periodizeMap_hom_mk, counitHom_mk, counitHom_mk]
    change _ • Unperiodize.fold ((unperiodizeMap ℬ g).hom _) = _
    rw [unperiodizeMap_hom_of, Unperiodize.fold_of, Unperiodize.fold_of, map_smul]
    rfl

/-- **The periodization equivalence.** For a `ℤ/2`-graded ring `B`, the category of `ℤ/2`-graded
`B`-modules is equivalent to the category of `ℤ`-graded modules over the 2-periodic `ℤ`-graded
ring `Periodize ℬ`, by `M ↦ Periodize M = ⨁ n : ℤ, M^{n mod 2}` and `N ↦ N⁰ ⊕ N¹`. -/
def periodizeEquivalence :
    GradedModuleCat.{v} ℬ ≌ GradedModuleCat.{v} (periodizeGrading ℬ) :=
  CategoryTheory.Equivalence.mk (periodize ℬ) (unperiodize ℬ) (periodizeUnitIso ℬ)
    (periodizeCounitIso ℬ)

end GradedModuleCat

end DG

end
