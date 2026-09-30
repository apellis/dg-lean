import DG.Category.Resolution.Resolution

/-!
# Semi-free and finite-cell dg modules over a dg category

Let `C` be a dg category. A dg module over `C` is semi-free if it has an exhaustive increasing
filtration by dg submodules, starting at `0`, whose subquotients are direct sums of shifts
`C(X, -)⟦k⟧` of representable modules; it is finite-cell if it has a finite such filtration whose
subquotients are shifts `(e · C(X, -))⟦k⟧` of direct summands of representable modules cut out by
degree-`0` idempotent cocycles `e`. This file shows that both are K-projective, and that the
K-projective resolution `DG.CatModule.Resolution.colim M` of
`DG/Category/Resolution/Resolution.lean` is semi-free. It is a port of `DG.Homotopy.SemiFree` and of the semi-free part of
`DG.Derived.Resolution` (the case of a dg ring, i.e. of a one-object dg category, where the
representable module is the free module `A` of rank one).

## Main definitions

* `DG.CatModule.SemiFreeFiltration P`: a semi-free filtration of `P` (the subquotients are
  encoded by surjections `F (i + 1) ⟶ ⨁ b, C(X_b, -)⟦k_b⟧` with kernel `F i`, the representable
  modules being lifted to the universe of `P`).
* `DG.CatModule.FiniteCellFiltration P`: a finite-cell filtration, with subquotients
  `(eᵢ · C(Xᵢ, -))⟦kᵢ⟧`; `DG.CatModule.FiniteCellFiltration.IsOrdered`: the ordering condition
  `k₁ ≥ k₂ ≥ ⋯` on the shifts.
* `DG.CatModule.cornerFiniteCellFiltration e`: the finite-cell filtration `0 ⊆ e · C(X, -)` of
  length one.
* `DG.CatModule.Cochain.glue`: gluing a compatible family of cochains on the members of an
  exhaustive filtration by dg submodules; `DG.CatModule.Cochain.exists_of_filtration`: the
  corresponding telescope argument.
* `DG.CatModule.GradedSplitting.ofSection`: a graded splitting of `S → T → T / S` from a graded
  section.
* `DG.CatModule.shiftDirectSum`: the identification `(⨁ j, R j⟦k j⟧)⟦n⟧ ≅ ⨁ j, R j⟦n + k j⟧`.
* `DG.CatModule.Resolution.semiFreeFiltration M`: the semi-free filtration of the resolution by
  the images of its stages.

## Main results

* `DG.CatModule.SemiFreeFiltration.isKProjective`: semi-free dg modules are K-projective
  [Keller, Prop. 3.1 (b)], [BL 10.12.2.3], [Stacks 09KM].
* `DG.CatModule.FiniteCellFiltration.isKProjective`: finite-cell dg modules are K-projective.
* `DG.CatModule.IsCornerGenerator.exists_lift`, `DG.CatModule.Cochain.exists_lift_directSum`:
  modules with a corner generator, and direct sums of such, are projective as graded modules
  relative to objectwise surjective morphisms.
* `DG.CatModule.exists_semiFreeResolution`: every dg module `M` has an objectwise surjective
  quasi-isomorphism `P ⟶ M` from a semi-free dg module `P` [Keller, Thm. 3.1 (a)].

## Universes

The representable module `C(X, -)` takes values in the universe `v` of the Hom types of
`C : Type u`. A semi-free filtration `SemiFreeFiltration.{w} P` has its generators indexed by
types in the universe `w`, with cells `C(X, -)` lifted to the universe `max v w`
(`DG.CatModule.ulift`), so it is defined for `P : CatModule.{max v w} C`. For a small dg
category and modules in the universe `v` of its Hom types, take `w = v` (or `w = 0`).

## References

* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994), §3]
* [J. Bernstein, V. Lunts, *Equivariant sheaves and functors*, LNM 1578 (1994), §10.12]
* [The Stacks project, Tags 09KK, 09KM]
-/

open CategoryTheory DirectSum

universe w w' v u

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### Inclusions of dg submodules -/

namespace CatSubmodule

variable {M : CatModule.{w} C}

/-- The inclusion `S ⟶ T` of dg submodules with `S ⊆ T`. -/
noncomputable def inclusion {S T : CatSubmodule M} (h : ∀ X, S.carrier X ≤ T.carrier X) :
    S.toCatModule ⟶ T.toCatModule :=
  codRestrict S.subtype fun X m => h X m.2

@[simp]
theorem coe_inclusion_app {S T : CatSubmodule M} (h : ∀ X, S.carrier X ≤ T.carrier X) {X : C}
    (x : S.toCatModule.obj X) : ((inclusion h).app X x).1 = x.1 := rfl

/-- An increasing sequence of dg submodules, given by `F i ⊆ F (i + 1)`, is monotone. -/
theorem le_of_le_succ {F : ℕ → CatSubmodule M} (hF : ∀ i X, (F i).carrier X ≤ (F (i + 1)).carrier X)
    {i j : ℕ} (hij : i ≤ j) (X : C) : (F i).carrier X ≤ (F j).carrier X := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact ih.trans (hF j X)

end CatSubmodule

namespace CatModule

/-! ### Homogeneous preimages -/

/-- A surjective morphism of dg modules is surjective on homogeneous elements. -/
theorem Hom.exists_mem_grading_of_surjective {M N : CatModule.{w} C} (p : M ⟶ N) {X : C}
    (hp : Function.Surjective (p.app X)) {n : ℤ} {y : N.obj X} (hy : y ∈ grading n) :
    ∃ x ∈ grading n, p.app X x = y := by
  obtain ⟨x, rfl⟩ := hp y
  refine ⟨decompose (grading (M := M.obj X)) x n, SetLike.coe_mem _, ?_⟩
  rw [← coe_decompose_map_of_map_mem (p.app X) (fun h => p.map_mem h),
    decompose_of_mem_same _ hy]

/-! ### Gluing cochains along an exhaustive filtration -/

section Glue

variable {P N : CatModule.{w} C} {F : ℕ → CatSubmodule P}
  (hF : ∀ i X, (F i).carrier X ≤ (F (i + 1)).carrier X)
  (hex : ∀ X (x : P.obj X), ∃ i, x ∈ (F i).carrier X) {n : ℤ}
  (c : ∀ i, Cochain (F i).toCatModule N n)
  (hc : ∀ i {X : C} (x : (F i).toCatModule.obj X),
    (c (i + 1)).app X ((CatSubmodule.inclusion (hF i)).app X x) = (c i).app X x)

include hc in
theorem Cochain.glue_compat {i j : ℕ} (hij : i ≤ j) {X : C} (x : P.obj X)
    (hi : x ∈ (F i).carrier X) (hj : x ∈ (F j).carrier X) :
    (c j).app X ⟨x, hj⟩ = (c i).app X ⟨x, hi⟩ := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    rw [← ih (CatSubmodule.le_of_le_succ hF hij X hi), ← hc j]
    rfl

/-- The underlying functions of `DG.CatModule.Cochain.glue`. -/
noncomputable def Cochain.glueFun (X : C) (x : P.obj X) : N.obj X :=
  (c (hex X x).choose).app X ⟨x, (hex X x).choose_spec⟩

include hc in
theorem Cochain.glueFun_eq {i : ℕ} {X : C} {x : P.obj X} (hx : x ∈ (F i).carrier X) :
    glueFun hex c X x = (c i).app X ⟨x, hx⟩ := by
  have hk := (hex X x).choose_spec
  set k := (hex X x).choose
  change (c k).app X ⟨x, hk⟩ = (c i).app X ⟨x, hx⟩
  rw [← glue_compat hF c hc (le_max_left k i) x hk
      (CatSubmodule.le_of_le_succ hF (le_max_left k i) X hk),
    ← glue_compat hF c hc (le_max_right k i) x hx
      (CatSubmodule.le_of_le_succ hF (le_max_right k i) X hx)]

/-- A compatible family of cochains `c i : F i → N` on an exhaustive increasing filtration `F` of
`P` by dg submodules glues to a cochain `P → N`. -/
noncomputable def Cochain.glue : Cochain P N n where
  app X :=
    { toFun := glueFun hex c X
      map_zero' := by
        rw [glueFun_eq hF hex c hc (zero_mem ((F 0).carrier X))]
        exact map_zero ((c 0).app X)
      map_add' := fun x y => by
        obtain ⟨i, hi⟩ := hex X x
        obtain ⟨j, hj⟩ := hex X y
        have hi' := CatSubmodule.le_of_le_succ hF (le_max_left i j) X hi
        have hj' := CatSubmodule.le_of_le_succ hF (le_max_right i j) X hj
        rw [glueFun_eq hF hex c hc (add_mem hi' hj'), glueFun_eq hF hex c hc hi',
          glueFun_eq hF hex c hc hj', ← map_add]
        rfl }
  map_mem' {X k x} hx := by
    obtain ⟨i, hi⟩ := hex X x
    change glueFun hex c X x ∈ _
    rw [glueFun_eq hF hex c hc hi]
    exact (c i).map_mem (x := ⟨x, hi⟩) hx
  map_smul' {X Y k f} hf x := by
    obtain ⟨i, hi⟩ := hex X x
    change glueFun hex c Y (f • x) = _ • (f • glueFun hex c X x)
    rw [glueFun_eq hF hex c hc hi, glueFun_eq hF hex c hc ((F i).smul_mem f hi)]
    exact (c i).map_smul hf ⟨x, hi⟩

theorem Cochain.glue_apply {i : ℕ} {X : C} (x : (F i).toCatModule.obj X) :
    (glue hF hex c hc).app X x.1 = (c i).app X x :=
  glueFun_eq hF hex c hc x.2

include hex in
/-- Telescope argument: if the sets `S i` of cochains on `F i` are nonempty for `i = 0` and every
element of `S i` extends to an element of `S (i + 1)`, then there is a cochain on `P` whose
restriction to each `F i` lies in `S i`. -/
theorem Cochain.exists_of_filtration (S : ∀ i, Set (Cochain (F i).toCatModule N n))
    (h0 : (S 0).Nonempty)
    (hstep : ∀ i, ∀ c ∈ S i, ∃ c' ∈ S (i + 1), ∀ {X : C} (x : (F i).toCatModule.obj X),
      c'.app X ((CatSubmodule.inclusion (hF i)).app X x) = c.app X x) :
    ∃ c : Cochain P N n, ∀ i, c.comp (Cochain.ofHom (F i).subtype) (zero_add n) ∈ S i := by
  choose next hnext hcompat using hstep
  let seq : ∀ i, {c : Cochain (F i).toCatModule N n // c ∈ S i} := fun i =>
    Nat.rec (motive := fun i => {c : Cochain (F i).toCatModule N n // c ∈ S i})
      ⟨h0.some, h0.some_mem⟩ (fun i c => ⟨next i c.1 c.2, hnext i c.1 c.2⟩) i
  refine ⟨glue hF hex (fun i => (seq i).1) (fun i _ x => hcompat i _ _ x), fun i => ?_⟩
  convert (seq i).2 using 1
  ext X x
  exact glue_apply hF hex (fun i => (seq i).1) (fun i _ x => hcompat i _ _ x) x

end Glue

/-! ### Graded lifts out of modules with a corner generator -/

section Lift

namespace IsCornerGenerator

variable [DGCategory C] {R : CatModule.{w} C} {X : C} {e : DGCategory.Idempotent X} {k : ℤ}
  {g : R.obj X}

/-- Graded lifting property of a module with a corner generator: along an objectwise surjective
morphism `p : M ⟶ N`, every cochain `R → N` of degree `0` lifts to `M`. -/
theorem exists_lift (hg : IsCornerGenerator R e k g) {M N : CatModule.{w} C} (p : M ⟶ N)
    (hp : ∀ X, Function.Surjective (p.app X)) (f : Cochain R N 0) :
    ∃ f' : Cochain R M 0, (Cochain.ofHom p).comp f' (zero_add 0) = f := by
  obtain ⟨y, hy, hpy⟩ := p.exists_mem_grading_of_surjective (hp X) (hg.app_gen_mem f)
  refine ⟨hg.ofElement y hy, hg.ext_gen ?_⟩
  rw [Cochain.comp_apply, Cochain.ofHom_apply, hg.ofElement_gen, p.map_smul, hpy,
    hg.val_smul_app_gen]

end IsCornerGenerator

/-- Graded lifting property of a direct sum: if every cochain of degree `0` out of each summand
lifts along `p : M ⟶ N`, so does every cochain of degree `0` out of the direct sum. -/
theorem Cochain.exists_lift_directSum {J : Type w'} [DecidableEq J]
    {F : J → CatModule.{max w w'} C} {M N : CatModule.{max w w'} C} (p : M ⟶ N)
    (hF : ∀ j (f : Cochain (F j) N 0),
      ∃ f' : Cochain (F j) M 0, (Cochain.ofHom p).comp f' (zero_add 0) = f)
    (f : Cochain (directSum F) N 0) :
    ∃ f' : Cochain (directSum F) M 0, (Cochain.ofHom p).comp f' (zero_add 0) = f := by
  choose g hg using fun j => hF j (f.comp (Cochain.ofHom (directSumι F j)) (zero_add 0))
  refine ⟨Cochain.directSumDesc g, Cochain.directSum_ext fun j X x => ?_⟩
  have h := congrArg (fun z : Cochain (F j) N 0 => z.app X x) (hg j)
  simpa [directSumι_app] using h

end Lift

/-! ### Graded splittings of filtrations -/

section OfSection

variable {P Q : CatModule.{w} C}

/-- For dg submodules `S ⊆ T` of `P` and a morphism `π : T ⟶ Q` with kernel `S` admitting a
graded section `s`, the sequence `S → T → Q` is graded split, with retraction `x ↦ x - s (π x)`. -/
noncomputable def GradedSplitting.ofSection {S T : CatSubmodule P}
    (hST : ∀ X, S.carrier X ≤ T.carrier X) (π : T.toCatModule ⟶ Q)
    (hπ : ∀ X (x : T.toCatModule.obj X), π.app X x = 0 ↔ x.1 ∈ S.carrier X)
    (s : Cochain Q T.toCatModule 0) (hs : ∀ X (y : Q.obj X), π.app X (s.app X y) = y) :
    GradedSplitting (CatSubmodule.inclusion hST) π where
  r :=
    { app := fun X =>
        { toFun := fun x => ⟨(x - s.app X (π.app X x) : T.toCatModule.obj X).1,
            (hπ X _).mp (by rw [map_sub, hs, sub_self])⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => by
            have h : x + y - s.app X (π.app X (x + y)) =
                (x - s.app X (π.app X x)) + (y - s.app X (π.app X y)) := by
              rw [map_add, map_add]
              abel
            apply Subtype.ext
            change (x + y - s.app X (π.app X (x + y))).1 =
              (x - s.app X (π.app X x)).1 + (y - s.app X (π.app X y)).1
            rw [h]
            rfl }
      map_mem' := fun {X i x} hx => by
        have h1 := s.map_mem (π.map_mem hx)
        rw [add_zero] at h1 ⊢
        exact sub_mem hx h1
      map_smul' := fun {X Y i f} hf x => Subtype.ext (by
        change (f • x - s.app Y (π.app Y (f • x)) : T.toCatModule.obj Y).1 =
          (koszulSign (0 * i) • (f • (x - s.app X (π.app X x))) : T.toCatModule.obj Y).1
        rw [π.map_smul, s.map_smul hf, zero_mul, koszulSign_zero, one_smul, one_smul,
          smul_sub]) }
  s := s
  r_i x := Subtype.ext (by
    change ((CatSubmodule.inclusion hST).app _ x).1 -
      (s.app _ (π.app _ ((CatSubmodule.inclusion hST).app _ x))).1 = x.1
    rw [(hπ _ ((CatSubmodule.inclusion hST).app _ x)).mpr x.2, map_zero,
      ZeroMemClass.coe_zero, sub_zero, CatSubmodule.coe_inclusion_app])
  p_s := hs _
  i_r_add_s_p x := Subtype.ext (by
    change (x.1 - (s.app _ (π.app _ x)).1) + (s.app _ (π.app _ x)).1 = x.1
    rw [sub_add_cancel])

end OfSection

/-! ### Semi-free dg modules -/

section SemiFree

variable [DGCategory C]

/-- The cell `C(X, -)⟦k⟧` of a semi-free filtration, with the representable module lifted to the
universe `max v w`; it is free on the cocycle `𝟙 X`, of degree `-k`. -/
noncomputable abbrev semiFreeCell (k : ℤ) (X : C) : CatModule.{max v w} C :=
  shift k (ulift.{w} (representable X))

/-- The generator `𝟙 X` of the cell `C(X, -)⟦k⟧`. -/
theorem isCornerGenerator_semiFreeCell (k : ℤ) (X : C) :
    IsCornerGenerator (semiFreeCell.{w} k X) (DGCategory.Idempotent.id X) (0 - k)
      (shift.mk k (ULift.up (𝟙 X))) :=
  ((isCornerGenerator_representable X).ulift.{w}).shift k

variable (P : CatModule.{max v w} C)

/-- A semi-free filtration of a dg module `P` over `C`: an increasing exhaustive filtration
`0 = F 0 ⊆ F 1 ⊆ ⋯` of `P` by dg submodules whose subquotients `F (i + 1) / F i` are
isomorphic to direct sums of shifts `C(X, -)⟦k⟧` of representable modules. The subquotients are
encoded by objectwise surjective morphisms `π i : F (i + 1) ⟶ ⨁ b, C(X_b, -)⟦k_b⟧` with kernel
`F i`. The summand `C(X, -)⟦k⟧` is free on the cocycle `𝟙 X`, of degree `-k`.

A dg module is semi-free if it admits such a filtration [Keller, *Deriving DG categories*, §3.1;
Bernstein–Lunts 10.12.2; Stacks 09KK]. Equivalently, `P` is free as a graded module over `C` on a
family of homogeneous elements `e_b ∈ P X_b` indexed by a set `B` with an exhaustive filtration
`∅ = B₀ ⊆ B₁ ⊆ ⋯` such that `d e_b` lies in the submodule generated by `(e_{b'})_{b' ∈ Bᵢ}`
for `b ∈ Bᵢ₊₁`. The index types of the generators live in the universe `w`, a parameter of the
structure, and the representable modules are lifted to the universe `max v w` of `P`. -/
structure SemiFreeFiltration where
  /-- The filtration. -/
  F : ℕ → CatSubmodule P
  le_succ : ∀ i X, (F i).carrier X ≤ (F (i + 1)).carrier X
  eq_zero_of_mem_zero : ∀ X, ∀ x ∈ (F 0).carrier X, x = 0
  exists_mem : ∀ X (x : P.obj X), ∃ i, x ∈ (F i).carrier X
  /-- The index type of the free generators of `F (i + 1) / F i`. -/
  ι : ℕ → Type w
  /-- Decidable equality on the index types, used for the direct sums. -/
  [decEq : ∀ i, DecidableEq (ι i)]
  /-- The objects at which the generators live. -/
  obj : ∀ i, ι i → C
  /-- The shifts: the summand indexed by `b` is `C(obj i b, -)⟦deg i b⟧`, generated in degree
  `-deg i b`. -/
  deg : ∀ i, ι i → ℤ
  /-- The projection of `F (i + 1)` onto its subquotient `F (i + 1) / F i`. -/
  π : ∀ i, (F (i + 1)).toCatModule ⟶
    directSum.{max v w, w} fun b : ι i => semiFreeCell.{w} (deg i b) (obj i b)
  surjective_π : ∀ i X, Function.Surjective ((π i).app X)
  π_eq_zero_iff : ∀ i X (x : (F (i + 1)).toCatModule.obj X),
    (π i).app X x = 0 ↔ x.1 ∈ (F i).carrier X

namespace SemiFreeFiltration

attribute [instance] decEq

variable {P} (S : SemiFreeFiltration.{w} P)

theorem mono {i j : ℕ} (hij : i ≤ j) (X : C) : (S.F i).carrier X ≤ (S.F j).carrier X :=
  CatSubmodule.le_of_le_succ S.le_succ hij X

/-- The `i`-th subquotient `F (i + 1) / F i ≅ ⨁ b, C(X_b, -)⟦k_b⟧` of a semi-free filtration. -/
noncomputable abbrev subquotient (i : ℕ) : CatModule.{max v w} C :=
  directSum.{max v w, w} fun b : S.ι i => semiFreeCell.{w} (S.deg i b) (S.obj i b)

/-- The subquotients of a semi-free filtration are K-projective. -/
theorem isKProjective_subquotient (i : ℕ) : IsKProjective (S.subquotient i) :=
  IsKProjective.directSum fun _ => (isCornerGenerator_semiFreeCell _ _).isKProjective

/-- The subquotients of a semi-free filtration are projective as graded modules. -/
theorem exists_lift_subquotient (i : ℕ) {M N : CatModule.{max v w} C} (p : M ⟶ N)
    (hp : ∀ X, Function.Surjective (p.app X)) (f : Cochain (S.subquotient i) N 0) :
    ∃ f' : Cochain (S.subquotient i) M 0, (Cochain.ofHom p).comp f' (zero_add 0) = f :=
  Cochain.exists_lift_directSum p
    (fun _ f => (isCornerGenerator_semiFreeCell _ _).exists_lift p hp f) f

theorem exists_section (i : ℕ) :
    ∃ s : Cochain (S.subquotient i) (S.F (i + 1)).toCatModule 0,
      ∀ X y, (S.π i).app X (s.app X y) = y := by
  obtain ⟨s, hs⟩ := S.exists_lift_subquotient i (S.π i) (S.surjective_π i) (Cochain.id _)
  exact ⟨s, fun X y => congrArg (fun c : Cochain _ _ 0 => c.app X y) hs⟩

/-- The inclusion `F i ⟶ F (i + 1)` of a semi-free filtration is split as a map of graded
modules. -/
noncomputable def gradedSplitting (i : ℕ) :
    GradedSplitting (CatSubmodule.inclusion (S.le_succ i)) (S.π i) :=
  GradedSplitting.ofSection _ (S.π i) (S.π_eq_zero_iff i) (S.exists_section i).choose
    (S.exists_section i).choose_spec

include S in
/-- Semi-free dg modules are K-projective [Keller, *Deriving DG categories*, Prop. 3.1 (b)];
[Bernstein–Lunts 10.12.2.3]; [Stacks 09KM]. The null-homotopy of a morphism to an acyclic module
is constructed on `F i` by induction on `i`, each step extending the previous one along the
graded-split inclusion `F i → F (i + 1)` (`DG.CatModule.GradedSplitting.exists_extension`), and
the compatible family is glued on the union (`DG.CatModule.Cochain.glue`). -/
theorem isKProjective : IsKProjective P := by
  intro N hN f
  obtain ⟨h, hh⟩ := Cochain.exists_of_filtration S.le_succ S.exists_mem
    (fun i => {h : Cochain (S.F i).toCatModule N (-1) |
      Cochain.ofHom ((S.F i).subtype ≫ f) = δ (-1) 0 h})
    ⟨0, Cochain.ext fun X x => by
      obtain rfl : x = 0 := Subtype.ext (S.eq_zero_of_mem_zero X x.1 x.2)
      simp⟩
    (fun i h hh => (S.gradedSplitting i).exists_extension ((S.isKProjective_subquotient i) N hN)
      ((S.F (i + 1)).subtype ≫ f) h hh)
  refine homotopic_zero_iff_exists.mpr ⟨h, Cochain.ext fun X x => ?_⟩
  obtain ⟨i, hi⟩ := S.exists_mem X x
  have h1 := congrArg (fun z : Cochain (S.F i).toCatModule N 0 => z.app X ⟨x, hi⟩) (hh i)
  have h2 := congrArg (fun z : Cochain (S.F i).toCatModule N 0 => z.app X ⟨x, hi⟩)
    (δ_ofHom_comp (S.F i).subtype h 0)
  simp only [Cochain.ofHom_apply, comp_app, CatSubmodule.subtype_app, Cochain.comp_apply] at h1 h2
  rw [Cochain.ofHom_apply]
  exact h1.trans h2

end SemiFreeFiltration

end SemiFree

/-! ### Finite-cell dg modules -/

section FiniteCell

variable [DGCategory C] (P : CatModule.{max v w} C)

/-- A finite-cell filtration of a dg module `P` over `C`: a finite filtration
`0 = F 0 ⊆ F 1 ⊆ ⋯ ⊆ F length = P` by dg submodules whose subquotients `F (i + 1) / F i` are
isomorphic to shifts `(eᵢ · C(Xᵢ, -))⟦kᵢ⟧` of the direct summands `e · C(X, -)` of representable
modules attached to degree-`0` idempotent cocycles `eᵢ` of `Xᵢ` (`DG.CatModule.corner`, lifted to
the universe `max v w` of `P`). The subquotients are encoded by objectwise surjective morphisms
`π i : F (i + 1) ⟶ (eᵢ · C(Xᵢ, -))⟦kᵢ⟧` with kernel `F i`. The members `F j` with `j > length`
play no role.

No ordering of the shifts `kᵢ` is imposed; the predicate
`DG.CatModule.FiniteCellFiltration.IsOrdered` asks in addition `k₁ ≥ k₂ ≥ ⋯` (as in Schnürer's
category `dgFilt` for dg algebras). -/
structure FiniteCellFiltration where
  /-- The length of the filtration. -/
  length : ℕ
  /-- The filtration. -/
  F : ℕ → CatSubmodule P
  le_succ : ∀ i X, (F i).carrier X ≤ (F (i + 1)).carrier X
  eq_zero_of_mem_zero : ∀ X, ∀ x ∈ (F 0).carrier X, x = 0
  mem_length : ∀ X (x : P.obj X), x ∈ (F length).carrier X
  /-- The object of the `i`-th subquotient. -/
  obj : Fin length → C
  /-- The idempotent of the `i`-th subquotient. -/
  e : ∀ i, DGCategory.Idempotent (obj i)
  /-- The shift of the `i`-th subquotient. -/
  deg : Fin length → ℤ
  /-- The projection of `F (i + 1)` onto its subquotient
  `F (i + 1) / F i ≅ (eᵢ · C(Xᵢ, -))⟦kᵢ⟧`. -/
  π : ∀ i : Fin length, (F (i.1 + 1)).toCatModule ⟶ shift (deg i) (ulift.{w} (corner (e i)))
  surjective_π : ∀ i X, Function.Surjective ((π i).app X)
  π_eq_zero_iff : ∀ i X (x : (F (i.1 + 1)).toCatModule.obj X),
    (π i).app X x = 0 ↔ x.1 ∈ (F i.1).carrier X

namespace FiniteCellFiltration

variable {P} (S : FiniteCellFiltration.{w} P)

/-- The ordering condition `k₁ ≥ k₂ ≥ ⋯` on the shifts of a finite-cell filtration (the `i`-th
subquotient is generated in degree `-kᵢ`). -/
def IsOrdered : Prop := ∀ i j : Fin S.length, i ≤ j → S.deg j ≤ S.deg i

/-- The generator `e` of the `i`-th subquotient. -/
theorem isCornerGenerator (i : Fin S.length) :
    IsCornerGenerator (shift (S.deg i) (ulift.{w} (corner (S.e i)))) (S.e i) (0 - S.deg i)
      (shift.mk (S.deg i) (ULift.up (cornerGen (S.e i)))) :=
  ((isCornerGenerator_corner (S.e i)).ulift.{w}).shift (S.deg i)

theorem exists_section (i : Fin S.length) :
    ∃ s : Cochain (shift (S.deg i) (ulift.{w} (corner (S.e i)))) (S.F (i.1 + 1)).toCatModule 0,
      ∀ X y, (S.π i).app X (s.app X y) = y := by
  obtain ⟨s, hs⟩ := (S.isCornerGenerator i).exists_lift (S.π i) (S.surjective_π i)
    (Cochain.id _)
  exact ⟨s, fun X y => congrArg (fun c : Cochain _ _ 0 => c.app X y) hs⟩

/-- The inclusion `F i ⟶ F (i + 1)` of a finite-cell filtration is split as a map of graded
modules. -/
noncomputable def gradedSplitting (i : Fin S.length) :
    GradedSplitting (CatSubmodule.inclusion (S.le_succ i.1)) (S.π i) :=
  GradedSplitting.ofSection _ (S.π i) (S.π_eq_zero_iff i) (S.exists_section i).choose
    (S.exists_section i).choose_spec

theorem isKProjective_F {i : ℕ} (hi : i ≤ S.length) : IsKProjective (S.F i).toCatModule := by
  induction i with
  | zero =>
    intro N _ f
    refine Homotopic.of_eq (hom_ext fun X x => ?_)
    rw [show x = 0 from Subtype.ext (S.eq_zero_of_mem_zero X x.1 x.2), map_zero, map_zero]
  | succ i ih =>
    exact IsKProjective.of_gradedSplitting (S.gradedSplitting ⟨i, hi⟩) (ih (by omega))
      (S.isCornerGenerator ⟨i, hi⟩).isKProjective

include S in
/-- Finite-cell dg modules are K-projective (by induction on the filtration, each step an
extension split as graded modules with K-projective subquotient `(e · C(X, -))⟦k⟧`). -/
theorem isKProjective : IsKProjective P :=
  (S.isKProjective_F le_rfl).of_retract
    (CatSubmodule.codRestrict (𝟙 P) fun X x => S.mem_length X x) (S.F S.length).subtype
    (Homotopic.of_eq (CatSubmodule.codRestrict_comp_subtype _ _ _))

end FiniteCellFiltration

/-! #### `e · C(X, -)` is a finite-cell module -/

variable {X : C} (e : DGCategory.Idempotent X)

/-- The filtration `0 ⊆ e · C(X, -)` of the corner `e · C(X, -)` (lifted to the universe
`max v w`), with the zero submodule in degree `0` and the whole module in all positive
degrees. -/
noncomputable def cornerFiltration : ℕ → CatSubmodule (ulift.{w} (corner e))
  | 0 => Hom.ker (𝟙 _)
  | _ + 1 => Hom.ker (0 : ulift.{w} (corner e) ⟶ ulift.{w} (corner e))

theorem mem_cornerFiltration_zero {Y : C} {x : (ulift.{w} (corner e)).obj Y} :
    x ∈ (cornerFiltration e 0).carrier Y ↔ x = 0 := by
  simp only [cornerFiltration, Hom.mem_ker, id_app]

theorem mem_cornerFiltration_succ {n : ℕ} {Y : C} (x : (ulift.{w} (corner e)).obj Y) :
    x ∈ (cornerFiltration e (n + 1)).carrier Y := by
  simp only [cornerFiltration, Hom.mem_ker, zero_app]

/-- The corner `e · C(X, -)` is a finite-cell module, with the filtration `0 ⊆ e · C(X, -)` of
length one, whose only subquotient is `e · C(X, -) = (e · C(X, -))⟦0⟧`. In particular (for
`e = 𝟙 X`) the representable module `C(X, -)` is a finite-cell module. -/
noncomputable def cornerFiniteCellFiltration :
    FiniteCellFiltration.{w} (ulift.{w} (corner e)) where
  length := 1
  F := cornerFiltration e
  le_succ _ _ x _ := mem_cornerFiltration_succ e x
  eq_zero_of_mem_zero _ _ hx := (mem_cornerFiltration_zero e).mp hx
  mem_length _ x := mem_cornerFiltration_succ e x
  obj _ := X
  e _ := e
  deg _ := 0
  π _ := CatSubmodule.subtype _ ≫ (shiftZeroIso _).inv
  surjective_π _ _ y := ⟨⟨shift.unmk 0 y, mem_cornerFiltration_succ e _⟩, rfl⟩
  π_eq_zero_iff i Y x := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by omega
    rw [mem_cornerFiltration_zero]
    exact Iff.rfl

end FiniteCell

/-! ### Shifts of direct sums -/

section ShiftDirectSum

variable [DGCategory C] {J : Type w'} [DecidableEq J] (n : ℤ) (k : J → ℤ)
  (R : J → CatModule.{max w w'} C)

/-- The underlying map of `DG.CatModule.shiftDirectSum` at an object, on direct sums. -/
noncomputable def shiftDirectSumAddHom (X : C) :
    (⨁ j, (shift (k j) (R j)).obj X) →+ ⨁ j, (shift (n + k j) (R j)).obj X :=
  DirectSum.map fun j =>
    (shift.mk (M := R j) (X := X) (n + k j)).toAddMonoidHom.comp
      (shift.unmk (M := R j) (X := X) (k j)).toAddMonoidHom

omit [DecidableEq J] in
variable {n k R} in
theorem shiftDirectSumAddHom_apply {X : C} (y : ⨁ j, (shift (k j) (R j)).obj X) (j : J) :
    shiftDirectSumAddHom n k R X y j = shift.mk (n + k j) (shift.unmk (k j) (y j)) :=
  DirectSum.map_apply _ _ _

/-- The identification `(⨁ j, R j⟦k j⟧)⟦n⟧ ≅ ⨁ j, R j⟦n + k j⟧`, as a morphism (the identity of
the underlying groups). -/
noncomputable def shiftDirectSum :
    shift n (directSum fun j => shift (k j) (R j)) ⟶ directSum fun j => shift (n + k j) (R j) where
  app X := (shiftDirectSumAddHom n k R X).comp
    (shift.unmk (M := directSum fun j => shift (k j) (R j)) (X := X) n).toAddMonoidHom
  map_mem' {X i x} hx j := by
    obtain ⟨y, rfl⟩ : ∃ y : ⨁ j, (shift (k j) (R j)).obj X, shift.mk n y = x :=
      ⟨shift.unmk n x, rfl⟩
    change shiftDirectSumAddHom n k R X y j ∈ grading i
    rw [shiftDirectSumAddHom_apply, shift.mem_grading_iff, ← add_assoc]
    exact hx j
  map_d' {X} x := by
    obtain ⟨y, rfl⟩ : ∃ y : ⨁ j, (shift (k j) (R j)).obj X, shift.mk n y = x :=
      ⟨shift.unmk n x, rfl⟩
    refine DFinsupp.ext fun j => ?_
    change shiftDirectSumAddHom n k R X (koszulSign n • d y) j =
      d (shiftDirectSumAddHom n k R X y j)
    rw [shiftDirectSumAddHom_apply, shiftDirectSumAddHom_apply, Units.smul_def,
      DFinsupp.zsmul_apply, ← Units.smul_def, DG.DirectSum.coe_d_apply, shift.unmk_units_smul,
      shift.unmk_d, shift.d_mk, smul_smul, ← koszulSign_add]
  map_smul' {X Y} f x := by
    obtain ⟨y, rfl⟩ : ∃ y : ⨁ j, (shift (k j) (R j)).obj X, shift.mk n y = x :=
      ⟨shift.unmk n x, rfl⟩
    refine DFinsupp.ext fun j => ?_
    change shiftDirectSumAddHom n k R Y
        (DirectSum.map (fun j => (shift (k j) (R j)).act (twist n f)) y) j =
      f • shiftDirectSumAddHom n k R X y j
    rw [shiftDirectSumAddHom_apply, shiftDirectSumAddHom_apply, DirectSum.map_apply, act_apply,
      shift.unmk_smul_eq, shift.smul_mk_eq, twist_twist, add_comm (k j) n]

theorem bijective_shiftDirectSum_app (X : C) :
    Function.Bijective ((shiftDirectSum n k R).app X) := by
  let inv : (⨁ j, (shift (n + k j) (R j)).obj X) →+ (⨁ j, (shift (k j) (R j)).obj X) :=
    DirectSum.map fun j =>
      (shift.mk (M := R j) (X := X) (k j)).toAddMonoidHom.comp
        (shift.unmk (M := R j) (X := X) (n + k j)).toAddMonoidHom
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => shift.mk n (inv y), fun x => ?_, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y : ⨁ j, (shift (k j) (R j)).obj X, shift.mk n y = x :=
      ⟨shift.unmk n x, rfl⟩
    refine congrArg (shift.mk n) (DFinsupp.ext fun j => ?_)
    change inv (shiftDirectSumAddHom n k R X y) j = y j
    rw [DirectSum.map_apply]
    change shift.mk (k j) (shift.unmk (n + k j) (shiftDirectSumAddHom n k R X y j)) = y j
    rw [shiftDirectSumAddHom_apply]
    rfl
  · obtain ⟨z, rfl⟩ : ∃ z : ⨁ j, (shift (n + k j) (R j)).obj X, z = y := ⟨y, rfl⟩
    refine DFinsupp.ext fun j => ?_
    change shiftDirectSumAddHom n k R X (inv z) j = z j
    rw [shiftDirectSumAddHom_apply, DirectSum.map_apply]
    rfl

end ShiftDirectSum

/-! ### The resolution is semi-free -/

namespace Resolution

variable [DGCategory C] (M : CatModule.{max u v w} C)

/-- The `n`-th member of the filtration of the resolution: the image of the `n`-th stage. -/
noncomputable abbrev filtration (n : ℕ) : CatSubmodule (colim M) :=
  Hom.range (SeqColimit.of (obj M) (ι M) n)

/-- The `n`-th stage, mapped onto the `n`-th member of the filtration. -/
noncomputable def toFiltration (n : ℕ) : obj M n ⟶ (filtration M n).toCatModule :=
  CatSubmodule.codRestrict (SeqColimit.of (obj M) (ι M) n) fun _ m => ⟨m, rfl⟩

theorem bijective_toFiltration_app (n : ℕ) (X : C) :
    Function.Bijective ((toFiltration M n).app X) :=
  ⟨fun _ _ h => SeqColimit.of_injective (ι_injective M) n X (congrArg Subtype.val h),
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩

instance (n : ℕ) : IsIso (toFiltration M n) :=
  isIso_of_bijective _ (bijective_toFiltration_app M n)

/-- The `n`-th member of the filtration of the resolution, identified with the `n`-th stage. -/
noncomputable def toObj (n : ℕ) : (filtration M n).toCatModule ⟶ obj M n :=
  inv (toFiltration M n)

instance (n : ℕ) : IsIso (toObj M n) := by
  unfold toObj
  infer_instance

variable {M}

theorem of_toObj {n : ℕ} {X : C} (x : (filtration M n).toCatModule.obj X) :
    (SeqColimit.of (obj M) (ι M) n).app X ((toObj M n).app X x) = x.1 := by
  have h := congrArg (fun φ : (filtration M n).toCatModule ⟶ (filtration M n).toCatModule =>
    (φ.app X x).1) (IsIso.inv_hom_id (toFiltration M n))
  exact h

theorem toObj_eq {n : ℕ} {X : C} {x : (filtration M n).toCatModule.obj X} {y : (obj M n).obj X}
    (h : (SeqColimit.of (obj M) (ι M) n).app X y = x.1) : (toObj M n).app X x = y :=
  SeqColimit.of_injective (ι_injective M) n X (by rw [of_toObj, h])

variable (M)

theorem filtration_le_succ (n : ℕ) (X : C) :
    (filtration M n).carrier X ≤ (filtration M (n + 1)).carrier X := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(ι M n).app X y, SeqColimit.of_succ_ι n y⟩

/-- The projection of the `(n + 1)`-st member of the filtration onto the generators attached at
stage `n + 1`:
`Fₙ₊₁ ≅ cone (attach πₙ) ⟶ (⨁ c, C(X_c, -)⟦-deg c⟧)⟦1⟧ ≅ ⨁ c, C(X_c, -)⟦1 - deg c⟧`. -/
noncomputable def filtrationπ (n : ℕ) :
    (filtration M (n + 1)).toCatModule ⟶
      directSum.{max u v w, max u v w} fun c : Cell (stage M n).π =>
        semiFreeCell.{max u v w} (1 + -c.deg) c.X :=
  toObj M (n + 1) ≫ cone.fstHom (attach (stage M n).π) ≫
    shiftDirectSum.{max u v w, max u v w} 1 (fun c : Cell (stage M n).π => -c.deg)
      fun c => ulift.{max u v w} (representable c.X)

theorem surjective_filtrationπ (n : ℕ) (X : C) :
    Function.Surjective ((filtrationπ M n).app X) := by
  refine (bijective_shiftDirectSum_app _ _ _ X).2.comp
    (Function.Surjective.comp (fun y => ⟨cone.inlAddHom _ X y, cone.fstHom_inlAddHom y⟩) ?_)
  exact ((isIso_iff_bijective (toObj M (n + 1))).mp inferInstance X).2

theorem filtrationπ_eq_zero_iff (n : ℕ) (X : C)
    (x : (filtration M (n + 1)).toCatModule.obj X) :
    (filtrationπ M n).app X x = 0 ↔ x.1 ∈ (filtration M n).carrier X := by
  rw [filtrationπ, comp_app, comp_app,
    map_eq_zero_iff _ (bijective_shiftDirectSum_app _ _ _ X).1]
  constructor
  · intro h
    have hy : (toObj M (n + 1)).app X x = (ι M n).app X
        (cone.sndAddHom (attach (stage M n).π) X ((toObj M (n + 1)).app X x)) :=
      cone.ext (h.trans (cone.fstHom_inr _).symm) (cone.sndAddHom_inr _).symm
    refine ⟨cone.sndAddHom (attach (stage M n).π) X ((toObj M (n + 1)).app X x), ?_⟩
    rw [← SeqColimit.of_succ_ι, ← hy, of_toObj]
  · rintro ⟨y, hy⟩
    have h' : (toObj M (n + 1)).app X x = (ι M n).app X y :=
      toObj_eq (by rw [SeqColimit.of_succ_ι]; exact hy)
    rw [h']
    exact cone.fstHom_inr y

/-- The resolution is semi-free: the images of the stages form a semi-free filtration, the
subquotient `Fₙ₊₁ / Fₙ` being free on the cells attached at stage `n + 1`, a cell `c` giving
the summand `C(X_c, -)⟦1 - deg c⟧` generated in degree `deg c - 1`. -/
noncomputable def semiFreeFiltration : SemiFreeFiltration.{max u v w} (colim M) where
  F := filtration M
  le_succ := filtration_le_succ M
  eq_zero_of_mem_zero X x hx := by
    obtain ⟨y, rfl⟩ := hx
    have : Subsingleton ((obj M 0).obj X) :=
      inferInstanceAs (Subsingleton ((CatModule.zero.{max u v w} (C := C)).obj X))
    rw [Subsingleton.elim y 0, map_zero]
  exists_mem X x := by
    obtain ⟨n, y, rfl⟩ := SeqColimit.exists_of_eq x
    exact ⟨n, y, rfl⟩
  ι n := Cell (stage M n).π
  decEq _ := inferInstance
  obj _ c := c.X
  deg _ c := 1 + -c.deg
  π := filtrationπ M
  surjective_π := surjective_filtrationπ M
  π_eq_zero_iff := filtrationπ_eq_zero_iff M

end Resolution

/-! ### Existence of semi-free resolutions -/

variable [DGCategory C] in
/-- Every dg module `M` over a dg category `C` has a semi-free resolution: an objectwise
surjective quasi-isomorphism `P ⟶ M` from a semi-free dg module `P` [Keller, *Deriving DG
categories*, §3.1, Thm. 3.1 (a)]; [Bernstein–Lunts 10.12.2.4]; [Stacks 09KP]. For
`C : Type u` with Hom types in `Type v` and `M : CatModule.{max u v w} C`, the module `P` lives
in the same universe (`DG.CatModule.Resolution.colim`). -/
theorem exists_semiFreeResolution (M : CatModule.{max u v w} C) :
    ∃ (P : CatModule.{max u v w} C) (π : P ⟶ M), (∀ X, Function.Surjective (π.app X)) ∧
      IsQuasiIso π ∧ Nonempty (SemiFreeFiltration.{max u v w} P) :=
  ⟨_, Resolution.π M, Resolution.surjective_π M, Resolution.isQuasiIso_π M,
    ⟨Resolution.semiFreeFiltration M⟩⟩

end CatModule

end DG
