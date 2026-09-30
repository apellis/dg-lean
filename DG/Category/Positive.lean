import DG.Category.Resolution.Generator

/-!
# Positive dg categories

A dg category `C` is *positive* (`DG.DGCategory.IsPositive C`) if

* (P1) its Hom complexes are non-negatively graded: `C(X, Y)ⁿ = 0` for `n < 0`;
* (P2) its degree-`0` category is semisimple (`DG.DGCategory.IsDegreeZeroSemisimple C`): for every
  object `X`, the identity `𝟙 X` is a finite sum of pairwise orthogonal *simple* degree-`0`
  idempotents;
* (P3) the differential vanishes on degree-`0` morphisms: `d (C(X, Y)⁰) = 0`.

This is the many-object form of Schnürer's positivity of a dg algebra [Sch, §1, (P1)–(P3)].

## Simple idempotents and the semisimplicity condition

Let `C⁰` be the degree-`0` category of `C` (the objects of `C` and the degree-`0` morphisms; under
(P3) it is `Z⁰(C)`), a preadditive category. A (left) `C⁰`-module is an additive functor
`C⁰ ⥤ Ab`; the representable ones are `C⁰(X, -)`, and their direct summands are the
`e · C⁰(X, -)` for idempotents `e ∈ C⁰(X, X)`. The module `e · C⁰(X, -)` is simple iff `e ≠ 0` and
every nonzero element `h ∈ e · C⁰(X, Y)` generates it, i.e. `e = h ≫ g` for some
`g ∈ C⁰(Y, X)`: this is `DG.DGCategory.Idempotent.IsSimple`. A decomposition
`𝟙 X = e₁ + ⋯ + eₖ` into pairwise orthogonal simple idempotents is a decomposition
`C⁰(X, -) = ⨁ᵢ eᵢ · C⁰(X, -)` into simple modules. Condition (P2) therefore says that every
representable `C⁰`-module is a finite direct sum of simple modules; since the representable
modules generate, this is the semisimplicity of the category of `C⁰`-modules. We state it in the
elementary form above, which is what the proof of Schnürer's theorem uses.

The two examples of interest:

* for the one-object dg category `SingleObj A` of a dg ring, `C⁰ = A⁰` and (P2) says that `A⁰` is
  a semisimple ring: `DG.DGCategory.isPositive_singleObj_iff` identifies `IsPositive (SingleObj A)`
  with `DG.IsPositive A`;
* for the weight dg category `C_A` of a bigraded dg ring (objects `ℤ`, `C_A(k, l) = A⟨l - k⟩`),
  `C⁰`-modules are the weight-graded `A⁰`-modules and (P2) says that `A⁰` is graded semisimple
  (`DG/Bigraded/Schnurer.lean`).

## Main definitions and results

* `DG.DGCategory.Idempotent.IsSimple`, `DG.DGCategory.Idempotent.Orthogonal`,
  `DG.DGCategory.Idempotent.listSum`: the sum of a list of pairwise orthogonal idempotents.
* `DG.DGCategory.IsDegreeZeroSemisimple C`, `DG.DGCategory.IsPositive C`.
* `DG.DGCategory.Idempotent.IsSimple.exists_inv`: Schur's lemma: a nonzero degree-`0` morphism
  `b ∈ f · C⁰(Y, X) · e` between simple idempotents is invertible.

## References

* [Sch] O. M. Schnürer, *Perfect derived categories of positively graded DG algebras*,
  Appl. Categ. Structures 19 (2011), 757–782; arXiv:0809.4782v2.
-/

open CategoryTheory

universe v u

namespace DG

namespace DGCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

namespace Idempotent

variable {X : C}

/-- A degree-`0` idempotent cocycle `e` of `X` is *simple* if `e ≠ 0` and every nonzero degree-`0`
morphism `h : X ⟶ Y` with `e ≫ h = h` satisfies `h ≫ g = e` for some degree-`0` `g : Y ⟶ X`: the
module `e · C⁰(X, -)` over the degree-`0` category is simple. -/
def IsSimple (e : Idempotent X) : Prop :=
  e.val ≠ 0 ∧ ∀ ⦃Y : C⦄ (h : X ⟶ Y), h ∈ grading 0 → e.val ≫ h = h → h ≠ 0 →
    ∃ g : Y ⟶ X, g ∈ grading 0 ∧ h ≫ g = e.val

/-- Two idempotents of `X` are orthogonal if both their composites vanish. -/
def Orthogonal (e f : Idempotent X) : Prop :=
  e.val ≫ f.val = 0 ∧ f.val ≫ e.val = 0

theorem Orthogonal.symm {e f : Idempotent X} (h : e.Orthogonal f) : f.Orthogonal e :=
  ⟨h.2, h.1⟩

/-- The sum of a list of pairwise orthogonal degree-`0` idempotent cocycles is a degree-`0`
idempotent cocycle. -/
def listSum (l : List (Idempotent X)) (hl : l.Pairwise Orthogonal) : Idempotent X where
  val := (l.map Idempotent.val).sum
  mem_cocycles := list_sum_mem fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
    exact e.mem_cocycles
  comp_self := by
    induction l with
    | nil => simp
    | cons e l ih =>
      obtain ⟨he, hl⟩ := List.pairwise_cons.mp hl
      have h1 : e.val ≫ (l.map Idempotent.val).sum = 0 := by
        change Preadditive.leftComp X e.val _ = 0
        rw [map_list_sum, List.map_map]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
        exact (he f hf).1
      have h2 : (l.map Idempotent.val).sum ≫ e.val = 0 := by
        change Preadditive.rightComp X e.val _ = 0
        rw [map_list_sum, List.map_map]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
        exact (he f hf).2
      simp only [List.map_cons, List.sum_cons, Preadditive.add_comp, Preadditive.comp_add,
        e.comp_self, h1, h2, ih hl, add_zero, zero_add]

@[simp]
theorem listSum_val (l : List (Idempotent X)) (hl : l.Pairwise Orthogonal) :
    (listSum l hl).val = (l.map Idempotent.val).sum :=
  rfl

/-- An idempotent orthogonal to all members of a list is orthogonal to their sum. -/
theorem orthogonal_listSum {e : Idempotent X} {l : List (Idempotent X)}
    (he : ∀ f ∈ l, e.Orthogonal f) (hl : l.Pairwise Orthogonal) :
    e.val ≫ (listSum l hl).val = 0 ∧ (listSum l hl).val ≫ e.val = 0 := by
  constructor
  · change Preadditive.leftComp X e.val (l.map Idempotent.val).sum = 0
    rw [map_list_sum, List.map_map]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    exact (he f hf).1
  · change Preadditive.rightComp X e.val (l.map Idempotent.val).sum = 0
    rw [map_list_sum, List.map_map]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    exact (he f hf).2

variable [DGCategory C]

/-- **Schur's lemma** for simple idempotents: if `e` (of `X`) and `f` (of `Y`) are simple and
`b : Y ⟶ X` is a nonzero degree-`0` morphism with `f ≫ b = b = b ≫ e`, then `b` is invertible
between the corners: there is a degree-`0` `c : X ⟶ Y` with `e ≫ c = c = c ≫ f`, `b ≫ c = f` and
`c ≫ b = e`. -/
theorem IsSimple.exists_inv {Y : C} {e : Idempotent X} {f : Idempotent Y} (he : e.IsSimple)
    (hf : f.IsSimple) {b : Y ⟶ X} (hb : b ∈ grading 0) (hfb : f.val ≫ b = b)
    (hbe : b ≫ e.val = b) (hb0 : b ≠ 0) :
    ∃ c : X ⟶ Y, c ∈ grading 0 ∧ e.val ≫ c = c ∧ c ≫ f.val = c ∧ b ≫ c = f.val ∧
      c ≫ b = e.val := by
  obtain ⟨g, hg, hbg⟩ := hf.2 b hb hfb hb0
  set c := e.val ≫ g ≫ f.val with hc
  have hc0 : c ∈ grading 0 := by
    have := comp_mem_grading e.mem_grading (comp_mem_grading hg f.mem_grading)
    simpa using this
  have hec : e.val ≫ c = c := by rw [hc, e.comp_self_assoc]
  have hcf : c ≫ f.val = c := by rw [hc, Category.assoc, Category.assoc, f.comp_self]
  have hbc : b ≫ c = f.val := by
    rw [hc, ← Category.assoc, hbe, ← Category.assoc, hbg, f.comp_self]
  have hcne : c ≠ 0 := fun h => hf.1 (by rw [← hbc, h, Limits.comp_zero])
  obtain ⟨g', -, hcg'⟩ := he.2 c hc0 hec hcne
  refine ⟨c, hc0, hec, hcf, hbc, ?_⟩
  calc c ≫ b = c ≫ b ≫ e.val := by rw [hbe]
    _ = c ≫ b ≫ c ≫ g' := by rw [hcg']
    _ = c ≫ g' := by rw [← Category.assoc b, hbc, ← Category.assoc, hcf]
    _ = e.val := hcg'

end Idempotent

variable (C)

/-- Condition (P2) of positivity: the degree-`0` category of `C` is semisimple, in the form that
for every object `X`, `𝟙 X` is the sum of a list of pairwise orthogonal simple degree-`0`
idempotent cocycles (so that every representable module over the degree-`0` category is a finite
direct sum of simple modules `e · C⁰(X, -)`). -/
def IsDegreeZeroSemisimple : Prop :=
  ∀ X : C, ∃ l : List (Idempotent X), (∀ e ∈ l, e.IsSimple) ∧ l.Pairwise Idempotent.Orthogonal ∧
    (l.map Idempotent.val).sum = 𝟙 X

/-- A dg category is *positive* (Schnürer's conditions (P1)–(P3), for dg categories): its Hom
complexes vanish in negative degrees, its degree-`0` category is semisimple, and the differential
vanishes on degree-`0` morphisms. -/
structure IsPositive : Prop where
  /-- (P1) The Hom complexes are non-negatively graded. -/
  eq_zero_of_neg : ∀ {X Y : C} {n : ℤ}, n < 0 → ∀ {f : X ⟶ Y}, f ∈ grading n → f = 0
  /-- (P2) The degree-`0` category is semisimple. -/
  semisimple : IsDegreeZeroSemisimple C
  /-- (P3) The differential vanishes on degree-`0` morphisms. -/
  d_eq_zero : ∀ {X Y : C} {f : X ⟶ Y}, f ∈ grading 0 → d f = 0

/-- The simple corners `(X, e)` of a dg category, indexing the cells of Schnürer's theorem. -/
abbrev SimpleCorner : Type (max u v) := {c : Σ X : C, Idempotent X // c.2.IsSimple}

variable {C}

end DGCategory

end DG
