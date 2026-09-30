import DG.Category.Resolution.SemiFree

/-!
# The lifting property against surjective quasi-isomorphisms over a dg category

Let `C` be a dg category. A dg module `P` over `C` has the lifting property against surjective
quasi-isomorphisms (it is cofibrant in the projective model structure) if every morphism
`P ⟶ N` lifts along every objectwise surjective quasi-isomorphism `M ⟶ N`. This file shows that
this property is equivalent to `P` being K-projective *and* graded-projective, and that
semi-free and finite-cell dg modules have it. It is a port of `DG.Homotopy.Lifting` (the case
of a dg ring, i.e. of a one-object dg category).

## Main definitions

* `DG.CatModule.IsGradedProjective P`: cochains of degree `0` out of `P` (families of additive
  maps of degree `0` commuting with the action of `C`, not necessarily with the differentials)
  lift along objectwise surjective morphisms.
* `DG.CatModule.HasLiftingProperty P`: morphisms out of `P` lift along objectwise surjective
  quasi-isomorphisms.
* `DG.CatModule.Cochain.codRestrict`: a cochain with values in a dg submodule, as a cochain to
  it.

## Main results

* `DG.CatModule.hasLiftingProperty_iff`: `HasLiftingProperty P ↔ IsKProjective P ∧
  IsGradedProjective P`, with the two halves `DG.CatModule.HasLiftingProperty.isKProjective`,
  `DG.CatModule.HasLiftingProperty.isGradedProjective` and
  `DG.CatModule.IsKProjective.hasLiftingProperty`.
* `DG.CatModule.Hom.isAcyclic_ker`: the kernel of an objectwise surjective quasi-isomorphism is
  acyclic.
* `DG.CatModule.IsCornerGenerator.isGradedProjective`,
  `DG.CatModule.IsGradedProjective.directSum`, `DG.CatModule.IsGradedProjective.of_retract`,
  `DG.CatModule.IsGradedProjective.of_gradedSplitting`.
* `DG.CatModule.SemiFreeFiltration.isGradedProjective`,
  `DG.CatModule.SemiFreeFiltration.hasLiftingProperty`,
  `DG.CatModule.FiniteCellFiltration.isGradedProjective`,
  `DG.CatModule.FiniteCellFiltration.hasLiftingProperty`.

## K-projective versus the lifting property

Roadmap item 3.5 states that K-projectivity is *equivalent* to the lifting property against
surjective quasi-isomorphisms. This is false as stated, already for dg rings (the one-object
case, see `DG.hasLiftingProperty_iff`): the lifting property implies K-projectivity, but not
conversely, since K-projectivity is invariant under homotopy equivalence whereas the lifting
property forces graded projectivity. For instance, for the one-object dg category `SingleObj ℤ`
of the ring `ℤ` concentrated in degree `0`, the cone of the identity of `ℚ` (the complex
`ℚ → ℚ` in degrees `-1, 0`) is contractible, hence K-projective, but `ℚ` is not a projective
`ℤ`-module, so by `DG.CatModule.hasLiftingProperty_iff` it does not have the lifting property.
The correct statement is the equivalence `DG.CatModule.hasLiftingProperty_iff`; the cofibrant
dg modules are the K-projective dg modules which are projective as graded modules, and they are
the retracts of semi-free modules (`DG.CatModule.hasLiftingProperty_iff_exists_retract`).

## Universes

As for `DG.CatModule.IsKProjective`, the modules `M`, `N` in the definitions range over the
universe of `P`.
-/

open CategoryTheory DirectSum

universe w w' v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### Graded projectivity and the lifting property -/

section Defs

variable (P : CatModule.{w} C)

/-- A dg module `P` over `C` is graded-projective if cochains of degree `0` out of `P` lift
along objectwise surjective morphisms: for every morphism `p : M ⟶ N` of dg modules (in the
universe of `P`) which is surjective at every object, and every cochain `f : P → N` of degree
`0` (a family of additive maps of degree `0` commuting with the action of `C`, not necessarily
with the differentials), there is a cochain `g : P → M` of degree `0` with `p ∘ g = f`. This is
projectivity of `P` as a graded module over `C`, relative to the surjections of dg modules. -/
@[pp_with_univ]
def IsGradedProjective : Prop :=
  ∀ (M N : CatModule.{w} C) (p : M ⟶ N), (∀ X, Function.Surjective (p.app X)) →
    ∀ f : Cochain P N 0, ∃ g : Cochain P M 0, (Cochain.ofHom p).comp g (zero_add 0) = f

/-- A dg module `P` over `C` has the (left) lifting property with respect to surjective
quasi-isomorphisms if for every quasi-isomorphism `p : M ⟶ N` (in the universe of `P`) which is
surjective at every object, every morphism `f : P ⟶ N` lifts to a morphism `g : P ⟶ M`,
`g ≫ p = f`. These are the cofibrant objects of the projective model structure on dg modules
over `C`. -/
@[pp_with_univ]
def HasLiftingProperty : Prop :=
  ∀ (M N : CatModule.{w} C) (p : M ⟶ N), (∀ X, Function.Surjective (p.app X)) →
    IsQuasiIso p → ∀ f : P ⟶ N, ∃ g : P ⟶ M, g ≫ p = f

end Defs

/-! ### Cochains into dg submodules and kernels of surjective quasi-isomorphisms -/

section Kernel

variable {P M N : CatModule.{w} C}

/-- A cochain with values in a dg submodule `S`, as a cochain to `S`. -/
def Cochain.codRestrict {n : ℤ} (c : Cochain P M n) (S : CatSubmodule M)
    (h : ∀ X x, c.app X x ∈ S.carrier X) : Cochain P S.toCatModule n where
  app X := (c.app X).codRestrict _ (h X)
  map_mem' hx := c.map_mem hx
  map_smul' hf x := Subtype.ext (c.map_smul hf x)

@[simp]
theorem Cochain.coe_codRestrict_app {n : ℤ} (c : Cochain P M n) (S : CatSubmodule M)
    (h : ∀ X x, c.app X x ∈ S.carrier X) {X : C} (x : P.obj X) :
    ((c.codRestrict S h).app X x).1 = c.app X x := rfl

theorem Cochain.coe_δ_codRestrict {n : ℤ} (m : ℤ) (c : Cochain P M n) (S : CatSubmodule M)
    (h : ∀ X x, c.app X x ∈ S.carrier X) {X : C} (x : P.obj X) :
    ((δ n m (c.codRestrict S h)).app X x).1 = (δ n m c).app X x := by
  by_cases hnm : n + 1 = m
  · rw [δ_apply _ _ hnm, δ_apply _ _ hnm]
    rfl
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm]
    rfl

/-- The kernel of an objectwise surjective quasi-isomorphism is acyclic. -/
theorem Hom.isAcyclic_ker (p : M ⟶ N) (hp : ∀ X, Function.Surjective (p.app X))
    (hq : IsQuasiIso p) : IsAcyclic (Hom.ker p).toCatModule := by
  intro X
  refine DG.isAcyclic_iff.mpr fun n z hz hdz => ?_
  have hz' : z.1 ∈ grading n := hz
  have hdz' : d z.1 = 0 := congrArg Subtype.val hdz
  have hpz : p.app X z.1 = 0 := z.2
  obtain ⟨m, hm, hdm⟩ := (cohomologyMap_injective_iff p X n).mp (hq X n).1 _ hz' hdz'
    ⟨0, zero_mem _, by rw [d_zero, hpz]⟩
  have hdpm : d (p.app X m) = 0 := by rw [← p.map_d, hdm, hpz]
  obtain ⟨m', hm', hdm', y, hy, hdy⟩ := (cohomologyMap_surjective_iff p X (n - 1)).mp
    (hq X (n - 1)).2 (p.app X m) (p.map_mem hm) hdpm
  obtain ⟨y', hy', rfl⟩ := p.exists_mem_grading_of_surjective (hp X) hy
  refine ⟨⟨m - m' + d y', ?_⟩, ?_, Subtype.ext ?_⟩
  · change p.app X (m - m' + d y') = 0
    rw [map_add, map_sub, p.map_d, hdy]
    abel
  · change m - m' + d y' ∈ grading (n - 1)
    exact add_mem (sub_mem hm hm') (by simpa using d_mem hy')
  · change d (m - m' + d y') = z.1
    rw [d_add, d_sub, hdm, hdm', d_d, sub_zero, add_zero]

end Kernel

/-! ### The lifting property -/

section Lifting

variable [DGCategory C] {P : CatModule.{w} C}

/-- A dg module with the lifting property against surjective quasi-isomorphisms is K-projective:
for acyclic `N`, the projection `cone (𝟙 (N⟦-1⟧)) ⟶ N⟦-1⟧⟦1⟧ ≅ N` is a surjective
quasi-isomorphism from a contractible module. -/
theorem HasLiftingProperty.isKProjective (h : HasLiftingProperty P) : IsKProjective P := by
  intro N hN f
  let E := cone (𝟙 (shift (-1) N))
  let p : E ⟶ N := cone.fstHom (𝟙 (shift (-1) N)) ≫
    (shiftShiftIso N (-1) 1 0 (by norm_num)).inv ≫ (shiftZeroIso N).hom
  have hE : IsContractible E := cone.isContractible_id _
  have hp : ∀ X, Function.Surjective (p.app X) := fun X y =>
    ⟨cone.inlAddHom _ X ((shiftShiftIso N (-1) 1 0 (by norm_num)).hom.app X
      ((shiftZeroIso N).inv.app X y)), rfl⟩
  have hq : IsQuasiIso p := isQuasiIso_of_isAcyclic hE.isAcyclic hN p
  obtain ⟨g, hg⟩ := h E N p hp hq f
  rw [← hg]
  exact ((hE.homotopic_zero_of_right g).comp_right p).trans
    (Homotopic.of_eq Limits.zero_comp)

/-- A dg module with the lifting property against surjective quasi-isomorphisms is
graded-projective: a cochain `f : P → N` of degree `0` is the second component of the morphism
`P ⟶ cone (𝟙 N)` with components `(-δ f, f)`, and `cone (𝟙 M) ⟶ cone (𝟙 N)` is a surjective
quasi-isomorphism for an objectwise surjective `M ⟶ N`. -/
theorem HasLiftingProperty.isGradedProjective (h : HasLiftingProperty P) :
    IsGradedProjective P := by
  intro M N p hp f
  let q : cone (𝟙 M) ⟶ cone (𝟙 N) :=
    cone.map p p (by rw [Category.id_comp, Category.comp_id])
  have hq : ∀ X, Function.Surjective (q.app X) := by
    intro X y
    obtain ⟨a, ha⟩ := hp X (shift.unmk 1 ((cone.fstHom _).app X y))
    obtain ⟨b, hb⟩ := hp X (cone.sndAddHom _ X y)
    refine ⟨cone.inlAddHom _ X (shift.mk 1 a) + (cone.inr _).app X b, cone.ext ?_ ?_⟩
    · rw [cone.fstHom_map, map_add, map_add, cone.fstHom_inlAddHom, cone.fstHom_inr, map_zero,
        add_zero, shiftMap_app_mk, ha, shift.mk_unmk]
    · rw [cone.sndAddHom_map, map_add, map_add, cone.sndAddHom_inlAddHom, cone.sndAddHom_inr,
        map_zero, zero_add, hb]
  have hqq : IsQuasiIso q := isQuasiIso_of_isAcyclic
    (cone.isContractible_id M).isAcyclic (cone.isContractible_id N).isAcyclic q
  let α : Cocycle P N 1 := Cocycle.mk (-δ 0 1 f) 2 (by norm_num) (by rw [δ_neg, δ_δ, neg_zero])
  obtain ⟨G, hG⟩ := h _ _ q hq hqq (cone.lift (𝟙 N) α f (by
    ext X x
    simp [α]))
  refine ⟨(cone.snd (𝟙 M)).comp (Cochain.ofHom G) (zero_add 0), Cochain.ext fun X x => ?_⟩
  have h1 := congrArg (fun φ : P ⟶ cone (𝟙 N) => (cone.snd (𝟙 N)).app X (φ.app X x)) hG
  simp only [comp_app, cone.lift_snd_apply] at h1
  rw [Cochain.comp_apply, Cochain.comp_apply, Cochain.ofHom_apply, Cochain.ofHom_apply, ← h1]
  rfl

/-- A K-projective and graded-projective dg module has the lifting property against surjective
quasi-isomorphisms: a graded lift `g₀` of `f` differs from a morphism by the cocycle `δ g₀` with
values in the (acyclic) kernel of the surjection, which is a coboundary. -/
theorem IsKProjective.hasLiftingProperty (hK : IsKProjective P) (hG : IsGradedProjective P) :
    HasLiftingProperty P := by
  intro M N p hp hq f
  obtain ⟨g₀, hg₀⟩ := hG M N p hp (Cochain.ofHom f)
  have hpg : ∀ X x, p.app X (g₀.app X x) = f.app X x := fun X x =>
    congrArg (fun c : Cochain P N 0 => c.app X x) hg₀
  have hmem : ∀ X x, (δ 0 1 g₀).app X x ∈ (Hom.ker p).carrier X := fun X x => by
    rw [Hom.mem_ker, δ_zero_cochain_apply, map_sub, p.map_d, hpg, hpg, f.map_d, sub_self]
  have hc₁ : δ 1 (1 + 1) ((δ 0 1 g₀).codRestrict (Hom.ker p) hmem) = 0 :=
    Cochain.ext fun X x => Subtype.ext (by rw [Cochain.coe_δ_codRestrict, δ_δ]; rfl)
  obtain ⟨c₀, hc₀⟩ := exists_δ_eq_of_isAcyclic
    (hK.isAcyclic_hom (Hom.isAcyclic_ker p hp hq)) (zero_add 1) _ hc₁
  have hg : δ 0 1 (g₀ - (Cochain.ofHom (Hom.ker p).subtype).comp c₀ (zero_add 0)) = 0 := by
    rw [δ_sub, δ_comp_ofHom, hc₀, sub_eq_zero]
    ext X x
    rfl
  refine ⟨Cocycle.homOf (Cocycle.mk _ 1 (zero_add 1) hg), hom_ext fun X x => ?_⟩
  change p.app X (g₀.app X x - (c₀.app X x).1) = f.app X x
  rw [map_sub, hpg, show p.app X (c₀.app X x).1 = 0 from (c₀.app X x).2, sub_zero]

/-- The lifting property against surjective quasi-isomorphisms is equivalent to being both
K-projective and graded-projective. In particular it implies K-projectivity, but not
conversely: a contractible dg module is K-projective, but it has the lifting property only if it
is graded-projective (see the module docstring for a counterexample to the equivalence of
K-projectivity with the lifting property, as stated in roadmap item 3.5). -/
theorem hasLiftingProperty_iff :
    HasLiftingProperty P ↔ IsKProjective P ∧ IsGradedProjective P :=
  ⟨fun h => ⟨h.isKProjective, h.isGradedProjective⟩, fun h => h.1.hasLiftingProperty h.2⟩

end Lifting

/-! ### Graded projectivity: closure properties -/

section GradedProjective

variable {P Q : CatModule.{w} C}

/-- A retract of a graded-projective dg module is graded-projective. -/
theorem IsGradedProjective.of_retract (hP : IsGradedProjective P) (i : Q ⟶ P) (r : P ⟶ Q)
    (hri : i ≫ r = 𝟙 Q) : IsGradedProjective Q := by
  intro M N p hp f
  obtain ⟨g, hg⟩ := hP M N p hp (f.comp (Cochain.ofHom r) (zero_add 0))
  refine ⟨g.comp (Cochain.ofHom i) (zero_add 0), Cochain.ext fun X x => ?_⟩
  have h := congrArg (fun c : Cochain P N 0 => c.app X (i.app X x)) hg
  simp only [Cochain.comp_apply, Cochain.ofHom_apply] at h ⊢
  rw [h, ← comp_app, hri, id_app]

/-- Graded lifts extend along a graded-split monomorphism `i : F ⟶ G` whose cokernel `Q` is
graded-projective relative to `q`: if `g` lifts `f ∘ i` along `q`, then `f` has a lift along `q`
extending `g`. -/
theorem GradedSplitting.exists_lift_extension {F G : CatModule.{w} C} {i : F ⟶ G} {p : G ⟶ Q}
    (σ : GradedSplitting i p) {M N : CatModule.{w} C} {q : M ⟶ N}
    (hQ : ∀ f : Cochain Q N 0, ∃ g : Cochain Q M 0, (Cochain.ofHom q).comp g (zero_add 0) = f)
    (f : Cochain G N 0) (g : Cochain F M 0)
    (hg : (Cochain.ofHom q).comp g (zero_add 0) = f.comp (Cochain.ofHom i) (zero_add 0)) :
    ∃ g' : Cochain G M 0, (Cochain.ofHom q).comp g' (zero_add 0) = f ∧
      ∀ {X : C} (x : F.obj X), g'.app X (i.app X x) = g.app X x := by
  obtain ⟨gQ, hgQ⟩ := hQ (f.comp σ.s (zero_add 0))
  refine ⟨g.comp σ.r (zero_add 0) + gQ.comp (Cochain.ofHom p) (zero_add 0),
    Cochain.ext fun X x => ?_, fun {X} x => ?_⟩
  · have h1 := congrArg (fun c : Cochain F N 0 => c.app X (σ.r.app X x)) hg
    have h2 := congrArg (fun c : Cochain Q N 0 => c.app X (p.app X x)) hgQ
    simp only [Cochain.comp_apply, Cochain.ofHom_apply] at h1 h2
    simp only [Cochain.comp_apply, Cochain.ofHom_apply, Cochain.add_apply, map_add, h1, h2]
    rw [← map_add, σ.i_r_add_s_p]
  · simp [σ.r_i, σ.p_i]

/-- An extension of graded-projective dg modules, split as graded modules, is
graded-projective. -/
theorem IsGradedProjective.of_gradedSplitting {F G : CatModule.{w} C} {i : F ⟶ G} {p : G ⟶ Q}
    (σ : GradedSplitting i p) (hF : IsGradedProjective F) (hQ : IsGradedProjective Q) :
    IsGradedProjective G := by
  intro M N q hq f
  obtain ⟨gF, hgF⟩ := hF M N q hq (f.comp (Cochain.ofHom i) (zero_add 0))
  obtain ⟨g', hg', -⟩ := σ.exists_lift_extension (hQ M N q hq) f gF hgF
  exact ⟨g', hg'⟩

/-- A direct sum of graded-projective dg modules is graded-projective. -/
theorem IsGradedProjective.directSum {J : Type w'} [DecidableEq J]
    {F : J → CatModule.{max w w'} C} (h : ∀ j, IsGradedProjective (F j)) :
    IsGradedProjective (directSum F) :=
  fun M N p hp f => Cochain.exists_lift_directSum p (fun j => h j M N p hp) f

/-- A dg module with a corner generator (`R ≅ (e · C(X, -))⟦-k⟧`) is graded-projective. -/
theorem IsCornerGenerator.isGradedProjective [DGCategory C] {R : CatModule.{w} C} {X : C}
    {e : DGCategory.Idempotent X} {k : ℤ} {g : R.obj X} (hg : IsCornerGenerator R e k g) :
    IsGradedProjective R :=
  fun _ _ p hp f => hg.exists_lift p hp f

end GradedProjective

/-! ### Semi-free and finite-cell modules -/

section SemiFree

variable [DGCategory C]

namespace SemiFreeFiltration

variable {P : CatModule.{max v w} C} (S : SemiFreeFiltration.{w} P)

include S in
/-- Semi-free dg modules are graded-projective. -/
theorem isGradedProjective : IsGradedProjective P := by
  intro M N p hp f
  obtain ⟨g, hg⟩ := Cochain.exists_of_filtration S.le_succ S.exists_mem
    (fun i => {g : Cochain (S.F i).toCatModule M 0 | (Cochain.ofHom p).comp g (zero_add 0) =
      f.comp (Cochain.ofHom (S.F i).subtype) (zero_add 0)})
    ⟨0, Cochain.ext fun X x => by
      obtain rfl : x = 0 := Subtype.ext (S.eq_zero_of_mem_zero X x.1 x.2)
      simp⟩
    (fun i g hg => by
      obtain ⟨g', hg', hext⟩ := (S.gradedSplitting i).exists_lift_extension
        (S.exists_lift_subquotient i p hp) (f.comp (Cochain.ofHom (S.F (i + 1)).subtype)
          (zero_add 0)) g (by rw [hg]; rfl)
      exact ⟨g', hg', hext⟩)
  refine ⟨g, Cochain.ext fun X x => ?_⟩
  obtain ⟨i, hi⟩ := S.exists_mem X x
  exact congrArg (fun c : Cochain (S.F i).toCatModule N 0 => c.app X ⟨x, hi⟩) (hg i)

include S in
/-- Semi-free dg modules have the lifting property against surjective quasi-isomorphisms. -/
theorem hasLiftingProperty : HasLiftingProperty P :=
  S.isKProjective.hasLiftingProperty S.isGradedProjective

end SemiFreeFiltration

namespace FiniteCellFiltration

variable {P : CatModule.{max v w} C} (S : FiniteCellFiltration.{w} P)

theorem isGradedProjective_F {i : ℕ} (hi : i ≤ S.length) :
    IsGradedProjective (S.F i).toCatModule := by
  induction i with
  | zero =>
    intro M N p hp f
    refine ⟨0, Cochain.ext fun X x => ?_⟩
    obtain rfl : x = 0 := Subtype.ext (S.eq_zero_of_mem_zero X x.1 x.2)
    simp
  | succ i ih =>
    exact IsGradedProjective.of_gradedSplitting (S.gradedSplitting ⟨i, hi⟩) (ih (by omega))
      (S.isCornerGenerator ⟨i, hi⟩).isGradedProjective

include S in
/-- Finite-cell dg modules are graded-projective. -/
theorem isGradedProjective : IsGradedProjective P :=
  (S.isGradedProjective_F le_rfl).of_retract
    (CatSubmodule.codRestrict (𝟙 P) fun X x => S.mem_length X x) (S.F S.length).subtype
    (CatSubmodule.codRestrict_comp_subtype _ _ _)

include S in
/-- Finite-cell dg modules have the lifting property against surjective quasi-isomorphisms. -/
theorem hasLiftingProperty : HasLiftingProperty P :=
  S.isKProjective.hasLiftingProperty S.isGradedProjective

end FiniteCellFiltration

end SemiFree

end CatModule

end DG
