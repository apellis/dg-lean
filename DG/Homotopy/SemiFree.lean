import DG.Homotopy.KProjective
import DG.Module.CornerEnd
import DG.Module.Equiv
import DG.Module.Sub

/-!
# Semi-free and finite-cell dg modules

Let `A` be a dg ring. A dg module is semi-free if it has an exhaustive increasing filtration by
dg submodules, starting at `0`, whose subquotients are direct sums of shifts of `A`; it is
finite-cell if it has a finite such filtration whose subquotients are shifts `(A e)⟦n⟧` of the
dg modules `A e` attached to degree-`0` idempotent cocycles `e`. This file shows that both are
K-projective.

## Main definitions

* `DG.SemiFreeFiltration A P`: a semi-free filtration of `P` (the subquotients are encoded by
  surjections `F (i + 1) → ⨁ b, A⟦deg i b⟧` with kernel `F i`). See its docstring for the
  relation with the description by a filtered basis.
* `DG.FiniteCellFiltration A P`: a finite-cell filtration, with subquotients `(A eᵢ)⟦nᵢ⟧`;
  `DG.FiniteCellFiltration.IsOrdered`: Schnürer's ordering condition `n₁ ≥ n₂ ≥ ⋯`.
* `DG.DGIdempotent.finiteCellFiltration e`: the finite-cell filtration `0 ⊆ A e` of length one.
* `DG.Cochain.glue`: gluing a compatible family of cochains on the members of an exhaustive
  filtration; `DG.Cochain.exists_of_filtration`: the corresponding telescope argument.
* `DG.Cochain.shiftGen`, `DG.Cochain.leftCornerShiftGen`: graded maps out of `A⟦k⟧` and
  `(A e)⟦k⟧` given by the image of the generator.
* `DG.GradedSplitting.ofSection`: a graded splitting of `S → T → T / S` from a graded section.

## Main results

* `DG.SemiFreeFiltration.isKProjective`: semi-free dg modules are K-projective [Keller,
  Prop. 3.1], [BL 10.12.2.3], [Stacks 09KM].
* `DG.FiniteCellFiltration.isKProjective`: finite-cell dg modules are K-projective.
* `DG.Cochain.exists_lift_directSum_shift`, `DG.Cochain.exists_lift_shift_leftCorner`: direct
  sums of shifts of `A`, and shifts of `A e`, are projective as graded modules, relative to
  surjections of dg modules.

## References

* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994), §3]
* [J. Bernstein, V. Lunts, *Equivariant sheaves and functors*, LNM 1578 (1994), §10.12]
* [The Stacks project, Tags 09KK, 09KM]
* [O. M. Schnürer, *Perfect derived categories of positively graded DG algebras*,
  Appl. Categ. Structures 19 (2011); arXiv:0809.4782v2, §3]
-/

open DirectSum

universe w w'

namespace DG

/-! ### Inclusions of dg submodules -/

namespace DGSubmodule

variable {A : Type*} [Ring A] [DGAddCommGroup A] {M : Type*} [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]

/-- The inclusion `S → T` of dg submodules with `S ≤ T`, as a morphism of dg modules. -/
def inclusion {S T : DGSubmodule A M} (h : S ≤ T) : S →ᵈᵍ[A] T :=
  codRestrict S.subtype fun x => h x.2

@[simp]
theorem coe_inclusion_apply {S T : DGSubmodule A M} (h : S ≤ T) (x : S) :
    (inclusion h x : M) = x := rfl

end DGSubmodule

/-! ### Homogeneous preimages -/

theorem DGModuleHom.exists_mem_grading_of_surjective {A : Type*} [Ring A] [DGAddCommGroup A]
    {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] (p : M →ᵈᵍ[A] N) (hp : Function.Surjective p) {n : ℤ}
    {y : N} (hy : y ∈ grading n) : ∃ x ∈ grading n, p x = y := by
  obtain ⟨x, rfl⟩ := hp y
  refine ⟨decompose (grading (M := M)) x n, SetLike.coe_mem _, ?_⟩
  rw [← p.coe_decompose_apply, decompose_of_mem_same _ hy]

/-! ### Gluing cochains along an exhaustive filtration -/

section Glue

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P]
  {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  {F : ℕ → DGSubmodule A P} (hF : Monotone F) (hex : ∀ x, ∃ i, x ∈ F i) {n : ℤ}
  (c : ∀ i, Cochain A (F i) N n)
  (hc : ∀ i (x : F i), c (i + 1) (DGSubmodule.inclusion (hF i.le_succ) x) = c i x)

include hc in
theorem Cochain.glue_compat {i j : ℕ} (hij : i ≤ j) (x : F i) :
    c j (DGSubmodule.inclusion (hF hij) x) = c i x := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    rw [← ih, ← hc j]
    rfl

/-- The underlying function of `DG.Cochain.glue`. -/
noncomputable def Cochain.glueFun (x : P) : N :=
  c (hex x).choose ⟨x, (hex x).choose_spec⟩

include hc in
theorem Cochain.glueFun_eq {i : ℕ} {x : P} (hx : x ∈ F i) :
    glueFun hex c x = c i ⟨x, hx⟩ := by
  have hk := (hex x).choose_spec
  set k := (hex x).choose
  change c k ⟨x, hk⟩ = c i ⟨x, hx⟩
  rw [← glue_compat hF c hc (le_max_left k i), ← glue_compat hF c hc (le_max_right k i)]
  rfl

/-- A compatible family of cochains `c i : F i → N` on an exhaustive increasing filtration
`F` of `P` glues to a cochain `P → N`. -/
noncomputable def Cochain.glue : Cochain A P N n where
  toFun := glueFun hex c
  map_zero' := by rw [glueFun_eq hF hex c hc (zero_mem (F 0))]; exact map_zero (c 0)
  map_add' x y := by
    obtain ⟨i, hi⟩ := hex x
    obtain ⟨j, hj⟩ := hex y
    have hi' := hF (le_max_left i j) hi
    have hj' := hF (le_max_right i j) hj
    rw [glueFun_eq hF hex c hc (add_mem hi' hj'), glueFun_eq hF hex c hc hi',
      glueFun_eq hF hex c hc hj', ← map_add]
    rfl
  map_mem' k x hx := by
    obtain ⟨i, hi⟩ := hex x
    rw [glueFun_eq hF hex c hc hi]
    exact (c i).map_mem (i := k) hx
  map_smul' {k a} ha x := by
    obtain ⟨i, hi⟩ := hex x
    rw [glueFun_eq hF hex c hc hi, glueFun_eq hF hex c hc ((F i).toSubmodule.smul_mem a hi),
      ← (c i).map_smul ha]
    rfl

theorem Cochain.glue_apply {i : ℕ} (x : F i) : glue hF hex c hc x = c i x :=
  glueFun_eq hF hex c hc x.2

include hex in
/-- Telescope argument: if the sets `S i` of cochains on `F i` are nonempty for `i = 0` and every
element of `S i` extends to an element of `S (i + 1)`, then there is a cochain on `P` whose
restriction to each `F i` lies in `S i`. -/
theorem Cochain.exists_of_filtration (S : ∀ i, Set (Cochain A (F i) N n)) (h0 : (S 0).Nonempty)
    (hstep : ∀ i, ∀ c ∈ S i, ∃ c' ∈ S (i + 1),
      ∀ x, c' (DGSubmodule.inclusion (hF i.le_succ) x) = c x) :
    ∃ c : Cochain A P N n, ∀ i, c.comp (ofHom (F i).subtype) (zero_add n) ∈ S i := by
  choose next hnext hcompat using hstep
  let seq : ∀ i, {c : Cochain A (F i) N n // c ∈ S i} := fun i =>
    Nat.rec (motive := fun i => {c : Cochain A (F i) N n // c ∈ S i}) ⟨h0.some, h0.some_mem⟩
      (fun i c => ⟨next i c.1 c.2, hnext i c.1 c.2⟩) i
  refine ⟨glue hF hex (fun i => (seq i).1) (fun i x => hcompat i _ _ x), fun i => ?_⟩
  convert (seq i).2 using 1
  ext x
  exact glue_apply hF hex (fun i => (seq i).1) (fun i x => hcompat i _ _ x) x

end Glue

/-! ### Graded lifts out of shifts of `A` and of `A e` -/

section Generators

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

theorem Shift.twist_twist_self (k : ℤ) (a : A) : Shift.twist A k (Shift.twist A k a) = a := by
  rw [Shift.twist_twist]
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rename_i i
    rw [Shift.twist_of_mem a.2, koszulSign_even ⟨k * i, by ring⟩, one_smul]
  | h_add a a' ha ha' => rw [map_add, ha, ha']

/-- The generator `1 ∈ A⟦k⟧` (of degree `-k`) generates `A⟦k⟧`:
`y = (-1)^{k |y|} y • 1`. -/
theorem Shift.twist_unmk_smul_mk_one (k : ℤ) (y : Shift k A) :
    Shift.twist A k (Shift.unmk k y) • Shift.mk k (1 : A) = y := by
  rw [Shift.smul_mk_eq, Shift.twist_twist_self, smul_eq_mul, mul_one, Shift.mk_unmk]

/-- The idempotent `e ∈ (A e)⟦k⟧` (of degree `-k`) generates `(A e)⟦k⟧`. -/
theorem DGIdempotent.twist_unmk_smul_mk_idem (e : DGIdempotent A) (k : ℤ)
    (y : Shift k e.LeftCorner) :
    Shift.twist A k ((Shift.unmk k y : e.LeftCorner) : A) •
      Shift.mk k (DGIdempotent.LeftCorner.idem e) = y := by
  rw [Shift.smul_mk_eq, Shift.twist_twist_self, DGIdempotent.LeftCorner.smul_idem,
    Shift.mk_unmk]

variable {X Y : Type*} [AddCommGroup X] [DGAddCommGroup X] [Module A X] [DGModule A X]
  [AddCommGroup Y] [DGAddCommGroup Y] [Module A Y] [DGModule A Y]

namespace Cochain

/-- The graded `A`-linear map of degree `0` from `A⟦k⟧` to `X` sending the generator `1` (of
degree `-k`) to `x ∈ X^{-k}`: `y ↦ (-1)^{k |y|} y • x`. -/
def shiftGen (k : ℤ) (x : X) (hx : x ∈ grading (-k)) : Cochain A (Shift k A) X 0 where
  toFun y := Shift.twist A k (Shift.unmk k y) • x
  map_zero' := by rw [Shift.unmk_zero, map_zero, zero_smul]
  map_add' y y' := by rw [Shift.unmk_add, map_add, add_smul]
  map_mem' i y hy := by
    have := smul_mem_grading (Shift.twist_mem (n := k) (Shift.unmk_mem_grading hy)) hx
    rwa [add_neg_cancel_right, ← add_zero i] at this
  map_smul' {i b} hb y := by
    show Shift.twist A k (Shift.unmk k (b • y)) • x =
      koszulSign (0 * i) • (b • (Shift.twist A k (Shift.unmk k y) • x))
    rw [Shift.unmk_smul_eq, smul_eq_mul, map_mul, Shift.twist_twist_self, mul_smul, zero_mul,
      koszulSign_zero, one_smul]

theorem shiftGen_apply (k : ℤ) (x : X) (hx : x ∈ grading (-k)) (y : Shift k A) :
    shiftGen k x hx y = Shift.twist A k (Shift.unmk k y) • x := rfl

omit [DGModule A Y] in
/-- Graded lifting property of `A⟦k⟧`: along a surjective morphism of dg modules `p : X → Y`,
every graded `A`-linear map `A⟦k⟧ → Y` of degree `0` lifts to `X`. -/
theorem exists_lift_shift (p : X →ᵈᵍ[A] Y) (hp : Function.Surjective p) (k : ℤ)
    (f : Cochain A (Shift k A) Y 0) :
    ∃ g : Cochain A (Shift k A) X 0, (ofHom p).comp g (zero_add 0) = f := by
  have h1 : f (Shift.mk k 1) ∈ grading (-k) := by
    simpa using f.map_mem (Shift.mk_mem_grading (n := k) (one_mem_grading (A := A)))
  obtain ⟨x, hx, hpx⟩ := p.exists_mem_grading_of_surjective hp h1
  refine ⟨shiftGen k x hx, Cochain.ext fun y => ?_⟩
  rw [comp_apply, ofHom_apply, shiftGen_apply, _root_.map_smul, hpx,
    ← map_smul_of_degree_zero, Shift.twist_unmk_smul_mk_one]

omit [DGModule A Y] in
/-- Graded lifting property of a direct sum of shifts of `A`. -/
theorem exists_lift_directSum_shift {ι : Type*} [DecidableEq ι] (k : ι → ℤ)
    (p : X →ᵈᵍ[A] Y) (hp : Function.Surjective p) (f : Cochain A (⨁ b, Shift (k b) A) Y 0) :
    ∃ g : Cochain A (⨁ b, Shift (k b) A) X 0, (ofHom p).comp g (zero_add 0) = f := by
  choose g hg using fun b => exists_lift_shift p hp (k b)
    (f.comp (ofHom (DGModuleHom.lof A (fun b => Shift (k b) A) b)) (zero_add 0))
  refine ⟨directSumDesc g, directSum_ext fun b y => ?_⟩
  have h := congrArg (fun z : Cochain A (Shift (k b) A) Y 0 => z y) (hg b)
  simpa using h

/-- The graded `A`-linear map of degree `0` from `(A e)⟦k⟧` to `X` sending the generator `e` (of
degree `-k`) to `x ∈ X^{-k}`: `y ↦ (-1)^{k |y|} y • x`. -/
def leftCornerShiftGen (e : DGIdempotent A) (k : ℤ) (x : X) (hx : x ∈ grading (-k)) :
    Cochain A (Shift k e.LeftCorner) X 0 where
  toFun y := Shift.twist A k ((Shift.unmk k y : e.LeftCorner) : A) • x
  map_zero' := by rw [Shift.unmk_zero, ZeroMemClass.coe_zero, map_zero, zero_smul]
  map_add' y y' := by rw [Shift.unmk_add, Submodule.coe_add, map_add, add_smul]
  map_mem' i y hy := by
    have := smul_mem_grading (Shift.twist_mem (n := k) (Shift.unmk_mem_grading hy)) hx
    rwa [add_neg_cancel_right, ← add_zero i] at this
  map_smul' {i b} hb y := by
    show Shift.twist A k ((Shift.unmk k (b • y) : e.LeftCorner) : A) • x =
      koszulSign (0 * i) • (b • (Shift.twist A k ((Shift.unmk k y : e.LeftCorner) : A) • x))
    rw [Shift.unmk_smul_eq, Submodule.coe_smul, smul_eq_mul, map_mul, Shift.twist_twist_self,
      mul_smul, zero_mul, koszulSign_zero, one_smul]

theorem leftCornerShiftGen_apply (e : DGIdempotent A) (k : ℤ) (x : X) (hx : x ∈ grading (-k))
    (y : Shift k e.LeftCorner) :
    leftCornerShiftGen e k x hx y = Shift.twist A k ((Shift.unmk k y : e.LeftCorner) : A) • x := rfl

omit [DGModule A Y] in
/-- Graded lifting property of `(A e)⟦k⟧`. -/
theorem exists_lift_shift_leftCorner (e : DGIdempotent A) (p : X →ᵈᵍ[A] Y)
    (hp : Function.Surjective p) (k : ℤ) (f : Cochain A (Shift k e.LeftCorner) Y 0) :
    ∃ g : Cochain A (Shift k e.LeftCorner) X 0, (ofHom p).comp g (zero_add 0) = f := by
  have h1 : f (Shift.mk k (DGIdempotent.LeftCorner.idem e)) ∈ grading (-k) := by
    simpa using f.map_mem (Shift.mk_mem_grading (n := k)
      (DGIdempotent.LeftCorner.idem_mem_grading e))
  obtain ⟨x, hx, hpx⟩ := p.exists_mem_grading_of_surjective hp h1
  refine ⟨leftCornerShiftGen e k x hx, Cochain.ext fun y => ?_⟩
  rw [comp_apply, ofHom_apply, leftCornerShiftGen_apply, _root_.map_smul, hpx,
    ← map_smul_of_degree_zero, DGIdempotent.twist_unmk_smul_mk_idem]

end Cochain

end Generators

/-! ### Graded splittings of filtrations -/

section OfSection

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  {Q : Type*} [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q] [DGModule A Q]

/-- For dg submodules `S ≤ T` of `P` and a morphism `π : T → Q` with kernel `S` admitting a graded
section `s`, the sequence `S → T → Q` is graded split, with retraction `x ↦ x - s (π x)`. -/
def GradedSplitting.ofSection {S T : DGSubmodule A P} (hST : S ≤ T) (π : T →ᵈᵍ[A] Q)
    (hπ : ∀ x : T, π x = 0 ↔ (x : P) ∈ S) (s : Cochain A Q T 0) (hs : ∀ y, π (s y) = y) :
    GradedSplitting (DGSubmodule.inclusion hST) π where
  r :=
    { toFun := fun x => ⟨((x - s (π x) : T) : P), (hπ _).mp (by rw [map_sub, hs, sub_self])⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by
        ext
        simp only [map_add, DGSubmodule.coe_add, AddSubgroupClass.coe_sub]
        abel
      map_mem' := fun i x hx => by
        have h1 := s.map_mem (π.map_mem hx)
        rw [add_zero] at h1 ⊢
        exact sub_mem hx h1
      map_smul' := fun {i a} ha x => by
        ext
        simp only [_root_.map_smul, zero_mul, koszulSign_zero, one_smul,
          AddSubgroupClass.coe_sub, DGSubmodule.coe_smul, smul_sub]
        rw [Cochain.map_smul_of_degree_zero, DGSubmodule.coe_smul] }
  s := s
  r_i x := Subtype.ext (by
    change ((DGSubmodule.inclusion hST x : T) : P) - (s (π (DGSubmodule.inclusion hST x)) : P) = x
    rw [(hπ (DGSubmodule.inclusion hST x)).mpr x.2, map_zero, ZeroMemClass.coe_zero, sub_zero,
      DGSubmodule.coe_inclusion_apply])
  p_s := hs
  i_r_add_s_p x := Subtype.ext (by
    change ((x : P) - (s (π x) : P)) + (s (π x) : P) = x
    rw [sub_add_cancel])

end OfSection

/-! ### Semi-free dg modules -/

section SemiFree

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]
  (P : Type*) [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- A semi-free filtration of a dg module `P`: an increasing exhaustive filtration
`0 = F 0 ⊆ F 1 ⊆ ⋯` of `P` by dg submodules whose subquotients `F (i + 1) / F i` are
isomorphic, as dg modules, to direct sums of shifts `A⟦k⟧` of `A`. The subquotients are
encoded by surjective morphisms `π i : F (i + 1) → ⨁ b, A⟦deg i b⟧` with kernel `F i`. The
summand `A⟦k⟧` is free on the cocycle `1`, of degree `-k`.

A dg module is semi-free if it admits such a filtration [Keller, *Deriving DG categories*, §3.1;
Bernstein–Lunts 10.12.2; Stacks 09KK]. Equivalently, `P` is free as a graded `A`-module on a
family of homogeneous elements `(e_b)_{b ∈ B}` with an exhaustive filtration
`∅ = B₀ ⊆ B₁ ⊆ ⋯` of `B` such that `d e_b` lies in the span of `(e_{b'})_{b' ∈ Bᵢ}` for
`b ∈ Bᵢ₊₁`: given such a basis, take `F i` to be the span of `(e_b)_{b ∈ Bᵢ}`; conversely, lifts
of the generators of the subquotients form such a basis. The index types of the generators live
in the universe `w`, a parameter of the structure. -/
structure SemiFreeFiltration where
  /-- The filtration. -/
  F : ℕ → DGSubmodule A P
  mono : Monotone F
  eq_zero_of_mem_zero : ∀ x ∈ F 0, x = 0
  exists_mem : ∀ x, ∃ i, x ∈ F i
  /-- The index type of the free generators of `F (i + 1) / F i`. -/
  ι : ℕ → Type w
  /-- Decidable equality on the index types, used for the direct sums. -/
  [decEq : ∀ i, DecidableEq (ι i)]
  /-- The shifts: the summand indexed by `b` is `A⟦deg i b⟧`, generated in degree `-deg i b`. -/
  deg : ∀ i, ι i → ℤ
  /-- The projection of `F (i + 1)` onto its subquotient `F (i + 1) / F i`. -/
  π : ∀ i, F (i + 1) →ᵈᵍ[A] ⨁ b : ι i, Shift (deg i b) A
  surjective_π : ∀ i, Function.Surjective (π i)
  π_eq_zero_iff : ∀ i (x : F (i + 1)), π i x = 0 ↔ (x : P) ∈ F i

namespace SemiFreeFiltration

attribute [instance] decEq

variable {A P} (S : SemiFreeFiltration.{w} A P)

theorem exists_section (i : ℕ) :
    ∃ s : Cochain A (⨁ b : S.ι i, Shift (S.deg i b) A) (S.F (i + 1)) 0,
      ∀ y, S.π i (s y) = y := by
  obtain ⟨s, hs⟩ := Cochain.exists_lift_directSum_shift (S.deg i) (S.π i) (S.surjective_π i)
    (Cochain.id A _)
  exact ⟨s, fun y => congrArg (fun c : Cochain A _ _ 0 => c y) hs⟩

/-- The inclusion `F i → F (i + 1)` of a semi-free filtration is split as a map of graded
`A`-modules. -/
noncomputable def gradedSplitting (i : ℕ) :
    GradedSplitting (DGSubmodule.inclusion (S.mono i.le_succ)) (S.π i) :=
  GradedSplitting.ofSection _ (S.π i) (S.π_eq_zero_iff i) (S.exists_section i).choose
    (S.exists_section i).choose_spec

include S in
/-- Semi-free dg modules are K-projective [Keller, *Deriving DG categories*, Prop. 3.1 (b)];
[Bernstein–Lunts 10.12.2.3]; [Stacks 09KM]. The null-homotopy of a morphism to an acyclic module
is constructed on `F i` by induction on `i`, each step extending the previous one along the
graded-split inclusion `F i → F (i + 1)` (`DG.GradedSplitting.exists_extension`), and the
compatible family is glued on the union (`DG.Cochain.glue`). -/
theorem isKProjective : IsKProjective.{w'} A P := by
  intro N _ _ _ _ hN f
  have hQ : ∀ i, IsKProjective.{w'} A (⨁ b : S.ι i, Shift (S.deg i b) A) := fun i =>
    IsKProjective.directSum fun b => (isKProjective_self A).shift _
  obtain ⟨h, hh⟩ := Cochain.exists_of_filtration S.mono S.exists_mem
    (fun i => {h : Cochain A (S.F i) N (-1) |
      Cochain.ofHom (f.comp (S.F i).subtype) = δ (-1) 0 h})
    ⟨0, Cochain.ext fun x => by simp [S.eq_zero_of_mem_zero x x.2]⟩
    (fun i h hh => (S.gradedSplitting i).exists_extension (hQ i N hN)
      (f.comp (S.F (i + 1)).subtype) h hh)
  refine homotopic_zero_iff_exists.mpr ⟨h, Cochain.ext fun x => ?_⟩
  obtain ⟨i, hi⟩ := S.exists_mem x
  have h1 := congrArg (fun z : Cochain A (S.F i) N 0 => z ⟨x, hi⟩) (hh i)
  have h2 := congrArg (fun z : Cochain A (S.F i) N 0 => z ⟨x, hi⟩)
    (δ_ofHom_comp (S.F i).subtype h 0)
  simp only [Cochain.ofHom_apply, DGModuleHom.comp_apply, DGSubmodule.subtype_apply,
    Cochain.comp_apply] at h1 h2
  rw [Cochain.ofHom_apply, h1, h2]

end SemiFreeFiltration

end SemiFree

/-! ### Finite-cell dg modules -/

section FiniteCell

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]
  (P : Type*) [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- A finite-cell filtration of a dg module `P`: a finite filtration
`0 = F 0 ⊆ F 1 ⊆ ⋯ ⊆ F length = P` by dg submodules whose subquotients `F (i + 1) / F i` are
isomorphic, as dg modules, to shifts `(A eᵢ)⟦nᵢ⟧` of the dg modules `A eᵢ` attached to degree-`0`
idempotent cocycles `eᵢ` (`DG.DGIdempotent`). The subquotients are encoded by surjective
morphisms `π i : F (i + 1) → (A eᵢ)⟦nᵢ⟧` with kernel `F i`. The members `F j` with
`j > length` play no role.

No ordering of the shifts `nᵢ` is imposed; Schnürer's category `dgFilt` [Schnürer, *Perfect
derived categories of positively graded DG algebras*, §3] asks in addition `n₁ ≥ n₂ ≥ ⋯`, which is
the predicate `DG.FiniteCellFiltration.IsOrdered`. -/
structure FiniteCellFiltration where
  /-- The length of the filtration. -/
  length : ℕ
  /-- The filtration. -/
  F : ℕ → DGSubmodule A P
  mono : Monotone F
  eq_zero_of_mem_zero : ∀ x ∈ F 0, x = 0
  mem_length : ∀ x, x ∈ F length
  /-- The idempotent of the `i`-th subquotient. -/
  e : Fin length → DGIdempotent A
  /-- The shift of the `i`-th subquotient. -/
  shift : Fin length → ℤ
  /-- The projection of `F (i + 1)` onto its subquotient `F (i + 1) / F i ≅ (A eᵢ)⟦nᵢ⟧`. -/
  π : ∀ i : Fin length, F (i.1 + 1) →ᵈᵍ[A] Shift (shift i) (e i).LeftCorner
  surjective_π : ∀ i, Function.Surjective (π i)
  π_eq_zero_iff : ∀ i (x : F (i.1 + 1)), π i x = 0 ↔ (x : P) ∈ F i.1

namespace FiniteCellFiltration

variable {A P} (C : FiniteCellFiltration A P)

/-- The ordering condition `n₁ ≥ n₂ ≥ ⋯` on the shifts of a finite-cell filtration, required in
Schnürer's definition of `dgFilt` (the `i`-th subquotient is generated in degree `-nᵢ`). -/
def IsOrdered : Prop := ∀ i j : Fin C.length, i ≤ j → C.shift j ≤ C.shift i

theorem exists_section (i : Fin C.length) :
    ∃ s : Cochain A (Shift (C.shift i) (C.e i).LeftCorner) (C.F (i.1 + 1)) 0,
      ∀ y, C.π i (s y) = y := by
  obtain ⟨s, hs⟩ := Cochain.exists_lift_shift_leftCorner (C.e i) (C.π i) (C.surjective_π i)
    (C.shift i) (Cochain.id A _)
  exact ⟨s, fun y => congrArg (fun c : Cochain A _ _ 0 => c y) hs⟩

/-- The inclusion `F i → F (i + 1)` of a finite-cell filtration is split as a map of graded
`A`-modules. -/
noncomputable def gradedSplitting (i : Fin C.length) :
    GradedSplitting (DGSubmodule.inclusion (C.mono (Nat.le_succ i.1))) (C.π i) :=
  GradedSplitting.ofSection _ (C.π i) (C.π_eq_zero_iff i) (C.exists_section i).choose
    (C.exists_section i).choose_spec

theorem isKProjective_F {i : ℕ} (hi : i ≤ C.length) : IsKProjective.{w} A (C.F i) := by
  induction i with
  | zero =>
    intro N _ _ _ _ _ f
    refine Homotopic.of_eq (DGModuleHom.ext fun x => ?_)
    rw [show x = 0 from Subtype.ext (C.eq_zero_of_mem_zero x x.2), map_zero]
    rfl
  | succ i ih =>
    exact IsKProjective.of_gradedSplitting (C.gradedSplitting ⟨i, hi⟩) (ih (by omega))
      ((C.e ⟨i, hi⟩).isKProjective_leftCorner.shift _)

include C in
/-- Finite-cell dg modules are K-projective (by induction on the filtration, each step an
extension split as graded modules with K-projective subquotient `(A e)⟦n⟧`). -/
theorem isKProjective : IsKProjective.{w} A P :=
  (C.isKProjective_F le_rfl).of_retract (DGSubmodule.codRestrict DGModuleHom.id C.mem_length)
    (C.F C.length).subtype (Homotopic.of_eq (DGSubmodule.subtype_comp_codRestrict _ _))

end FiniteCellFiltration

end FiniteCell

/-! ### `A e` is a finite-cell module -/

namespace DGIdempotent

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] (e : DGIdempotent A)

/-- The filtration `0 ⊆ A e` of `A e`, with the zero submodule in degree `0` and `A e` in all
positive degrees. -/
def leftCornerFiltration : ℕ → DGSubmodule A e.LeftCorner
  | 0 => (DGModuleHom.id : e.LeftCorner →ᵈᵍ[A] e.LeftCorner).ker
  | _ + 1 => (0 : e.LeftCorner →ᵈᵍ[A] e.LeftCorner).ker

/-- `A e` is a finite-cell module, with the filtration `0 ⊆ A e` of length one, whose only
subquotient is `A e = (A e)⟦0⟧`. -/
noncomputable def finiteCellFiltration : FiniteCellFiltration A e.LeftCorner where
  length := 1
  F := e.leftCornerFiltration
  mono := by
    intro i j hij x hx
    cases i with
    | zero =>
      have hx0 : x = 0 := hx
      rw [hx0]
      exact zero_mem _
    | succ i =>
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact hx
  eq_zero_of_mem_zero _ hx := hx
  mem_length _ := rfl
  e _ := e
  shift _ := 0
  π _ := (Shift.zeroEquiv (A := A) (M := e.LeftCorner)).symm.toDGModuleHom.comp
    (DGSubmodule.subtype _)
  surjective_π _ y := ⟨⟨Shift.unmk 0 y, rfl⟩, rfl⟩
  π_eq_zero_iff i x := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by omega
    exact Iff.rfl

theorem finiteCellFiltration_isOrdered : e.finiteCellFiltration.IsOrdered :=
  fun _ _ _ => le_rfl

end DGIdempotent

end DG
