import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Retract
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Compact objects of a preadditive category

Let `C` be a preadditive category. An object `X` of `C` is *compact* (with respect to
coproducts indexed by types in the universe `w`) if for every family `Y : ι → C` with
`ι : Type w` admitting a coproduct, the canonical additive map

  `⨁ i, (X ⟶ Y i) ⟶ (X ⟶ ∐ Y)`,   `(fᵢ)ᵢ ↦ ∑ᵢ fᵢ ≫ Sigma.ι Y i`

is bijective (`DG.IsCompact`). Equivalently, every morphism `X ⟶ ∐ Y` factors uniquely as a
finite sum of morphisms `X ⟶ Y i` composed with the coproduct inclusions. This is
the notion of [Ne, Def. 4.2.7] (A. Neeman, *Triangulated categories*, Ann. Math. Studies 148),
formulated there for `Hom(X, -)` commuting with coproducts.

## Design

The domain of the comparison map is the direct sum `⨁ i, (X ⟶ Y i)` of the abelian groups of
morphisms (`DirectSum`), and the comparison map `DG.coproductComparison X Y` is the additive map
obtained from the maps `(X ⟶ Y i) →+ (X ⟶ ∐ Y)`, `f ↦ f ≫ Sigma.ι Y i`. Compactness is
bijectivity of this map. This formulation is stated in terms of additive maps between abelian
groups, so that closure properties (retracts, biproducts, and, in
`DG.Compact.Triangulated`, shifts and cones) are proved by elementwise arguments and the five
lemma for abelian groups.

The universe `w` of the indexing types is a parameter of `DG.IsCompact.{w}`; no global existence
of coproducts is assumed, only the existence of the coproduct of the family at hand, following
the conventions of `CategoryTheory.Limits.HasCoproducts.{w}`. The comparison map is built with
`DirectSum.toAddMonoid`, which takes a `DecidableEq` instance on the indexing type; `DG.IsCompact`
quantifies over all such instances (its truth does not depend on the choice).

## Main results

* `DG.IsCompact.of_retract`, `DG.IsCompact.of_iso`: compact objects are closed under retracts
  (direct summands) and under isomorphisms.
* `DG.IsCompact.of_isZero`: a zero object is compact.
* `DG.isCompact_biprod_iff`: `X ⊞ Y` is compact if and only if `X` and `Y` are.
* `DG.isCompact_iff_preservesColimitsOfShape`: `X` is compact if and only if the functor
  `Hom(X, -) : C ⥤ AddCommGrp` (`preadditiveCoyoneda.obj (op X)`) preserves coproducts indexed
  by types in `Type w`; this is the comparison with the categorical formulation.
* `DG.exact_directSum_map`: a direct sum of exact sequences of abelian groups is exact
  (used for the five-lemma arguments in `DG.Compact.Triangulated`).
-/

universe w v u

namespace DG

open CategoryTheory Limits

section DirectSum

variable {ι : Type*} {α β γ : ι → Type*}
  [∀ i, AddCommGroup (α i)] [∀ i, AddCommGroup (β i)] [∀ i, AddCommGroup (γ i)]

/-- A direct sum of exact sequences of abelian groups is exact. -/
theorem exact_directSum_map (f : ∀ i, α i →+ β i) (g : ∀ i, β i →+ γ i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.map f) (DirectSum.map g) := by
  classical
  intro y
  constructor
  · intro hy
    have hy' : ∀ i, y i ∈ Set.range (f i) := fun i =>
      (h i _).1 (by simpa using congrArg (fun z => z i) hy)
    refine ⟨DirectSum.mk α (DFinsupp.support y) (fun i => (hy' i).choose), ?_⟩
    ext i
    rw [DirectSum.map_apply]
    by_cases hi : i ∈ DFinsupp.support y
    · rw [DirectSum.mk_apply_of_mem hi, (hy' i).choose_spec]
    · rw [DirectSum.mk_apply_of_not_mem hi, map_zero]
      exact (DFinsupp.not_mem_support_iff.1 hi).symm
  · rintro ⟨x, rfl⟩
    ext i
    simp [(h i).apply_apply_eq_zero]

end DirectSum

variable {C : Type u} [Category.{v} C] [Preadditive C]

section comparison

variable {ι : Type w}

/-- Precomposition with `u : X' ⟶ X` on the direct sum `⨁ i, (X ⟶ Y i)`. -/
noncomputable def precompDirectSum (Y : ι → C) {X X' : C} (u : X' ⟶ X) :
    (DirectSum ι fun i => (X ⟶ Y i)) →+ DirectSum ι fun i => (X' ⟶ Y i) :=
  DirectSum.map fun i => Preadditive.leftComp (Y i) u

variable {Y : ι → C} {X X' : C}

@[simp]
theorem precompDirectSum_apply (u : X' ⟶ X) (a : DirectSum ι fun i => (X ⟶ Y i)) (i : ι) :
    precompDirectSum Y u a i = u ≫ a i :=
  DirectSum.map_apply _ _ _

theorem precompDirectSum_id (a : DirectSum ι fun i => (X ⟶ Y i)) :
    precompDirectSum Y (𝟙 X) a = a := by
  ext i; simp

theorem precompDirectSum_comp {X'' : C} (u : X'' ⟶ X') (v : X' ⟶ X)
    (a : DirectSum ι fun i => (X ⟶ Y i)) :
    precompDirectSum Y (u ≫ v) a = precompDirectSum Y u (precompDirectSum Y v a) := by
  ext i; simp

theorem precompDirectSum_add (u v : X' ⟶ X) (a : DirectSum ι fun i => (X ⟶ Y i)) :
    precompDirectSum Y (u + v) a = precompDirectSum Y u a + precompDirectSum Y v a := by
  ext i; simp [Preadditive.add_comp]

variable [DecidableEq ι]

@[simp]
theorem precompDirectSum_of (u : X' ⟶ X) (i : ι) (f : X ⟶ Y i) :
    precompDirectSum Y u (DirectSum.of _ i f) = DirectSum.of (fun i => (X' ⟶ Y i)) i (u ≫ f) :=
  DirectSum.map_of _ _ _

/-- The canonical additive map `⨁ i, (X ⟶ Y i) →+ (X ⟶ ∐ Y)` sending a finitely supported
family `(fᵢ)ᵢ` to `∑ᵢ fᵢ ≫ Sigma.ι Y i`. -/
noncomputable def coproductComparison (X : C) (Y : ι → C) [HasCoproduct Y] :
    (DirectSum ι fun i => (X ⟶ Y i)) →+ (X ⟶ ∐ Y) :=
  DirectSum.toAddMonoid fun i => Preadditive.rightComp X (Sigma.ι Y i)

@[simp]
theorem coproductComparison_of (X : C) (Y : ι → C) [HasCoproduct Y] (i : ι) (f : X ⟶ Y i) :
    coproductComparison X Y (DirectSum.of _ i f) = f ≫ Sigma.ι Y i :=
  DirectSum.toAddMonoid_of _ _ _

/-- Naturality of the comparison map in `X`, as an equality of additive maps. -/
theorem leftComp_comp_coproductComparison [HasCoproduct Y] (u : X' ⟶ X) :
    (Preadditive.leftComp (∐ Y) u).comp (coproductComparison X Y) =
      (coproductComparison X' Y).comp (precompDirectSum Y u) := by
  ext i f
  simp [Preadditive.leftComp]

/-- Naturality of the comparison map in `X`. -/
theorem coproductComparison_precompDirectSum [HasCoproduct Y] (u : X' ⟶ X)
    (a : DirectSum ι fun i => (X ⟶ Y i)) :
    coproductComparison X' Y (precompDirectSum Y u a) = u ≫ coproductComparison X Y a :=
  (DFunLike.congr_fun (leftComp_comp_coproductComparison u) a).symm

end comparison

/-- An object `X` of a preadditive category is *compact* (relative to the universe `w`) if for
every family `Y : ι → C` with `ι : Type w` admitting a coproduct, the canonical map
`⨁ i, (X ⟶ Y i) → (X ⟶ ∐ Y)` is bijective: every morphism `X ⟶ ∐ Y` is uniquely a finite sum
`∑ᵢ fᵢ ≫ Sigma.ι Y i`. See [Ne, Def. 4.2.7]. -/
def IsCompact (X : C) : Prop :=
  ∀ (ι : Type w) [DecidableEq ι] (Y : ι → C) [HasCoproduct Y],
    Function.Bijective (coproductComparison X Y)

namespace IsCompact

variable {X Y : C}

/-- A retract of a compact object is compact [Ne, Lemma 4.2.4 style]. -/
theorem of_retract (h : Retract X Y) (hY : IsCompact.{w} Y) : IsCompact.{w} X := by
  intro ι _ W _
  constructor
  · intro a b hab
    have h₁ : precompDirectSum W h.r a = precompDirectSum W h.r b := by
      apply (hY ι W).1
      rw [coproductComparison_precompDirectSum, coproductComparison_precompDirectSum, hab]
    have h₂ := congrArg (precompDirectSum W h.i) h₁
    rwa [← precompDirectSum_comp, ← precompDirectSum_comp, h.retract,
      precompDirectSum_id, precompDirectSum_id] at h₂
  · intro f
    obtain ⟨b, hb⟩ := (hY ι W).2 (h.r ≫ f)
    refine ⟨precompDirectSum W h.i b, ?_⟩
    rw [coproductComparison_precompDirectSum, hb, ← Category.assoc, h.retract, Category.id_comp]

/-- Compactness is invariant under isomorphism. -/
theorem of_iso (e : X ≅ Y) (hY : IsCompact.{w} Y) : IsCompact.{w} X :=
  of_retract ⟨e.hom, e.inv, e.hom_inv_id⟩ hY

theorem iff_of_iso (e : X ≅ Y) : IsCompact.{w} X ↔ IsCompact.{w} Y :=
  ⟨of_iso e.symm, of_iso e⟩

/-- A zero object is compact. -/
theorem of_isZero (hX : IsZero X) : IsCompact.{w} X := by
  intro ι _ W _
  exact ⟨fun a b _ => DirectSum.ext _ fun i => hX.eq_of_src _ _, fun f => ⟨0, hX.eq_of_src _ _⟩⟩

section biprod

variable [HasBinaryBiproduct X Y]

/-- A biproduct of two compact objects is compact. -/
theorem biprod (hX : IsCompact.{w} X) (hY : IsCompact.{w} Y) : IsCompact.{w} (X ⊞ Y) := by
  intro ι _ W _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have hl : precompDirectSum W biprod.inl a = 0 := by
      apply (hX ι W).1
      rw [coproductComparison_precompDirectSum, ha, map_zero, Limits.comp_zero]
    have hr : precompDirectSum W biprod.inr a = 0 := by
      apply (hY ι W).1
      rw [coproductComparison_precompDirectSum, ha, map_zero, Limits.comp_zero]
    rw [← precompDirectSum_id a, ← biprod.total, precompDirectSum_add, precompDirectSum_comp,
      precompDirectSum_comp, hl, hr, map_zero, map_zero, add_zero]
  · intro f
    obtain ⟨b, hb⟩ := (hX ι W).2 (biprod.inl ≫ f)
    obtain ⟨c, hc⟩ := (hY ι W).2 (biprod.inr ≫ f)
    refine ⟨precompDirectSum W biprod.fst b + precompDirectSum W biprod.snd c, ?_⟩
    rw [map_add, coproductComparison_precompDirectSum, coproductComparison_precompDirectSum, hb,
      hc, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, biprod.total,
      Category.id_comp]

/-- If `X ⊞ Y` is compact, so is `X`. -/
theorem of_biprod_left (h : IsCompact.{w} (X ⊞ Y)) : IsCompact.{w} X :=
  of_retract ⟨biprod.inl, biprod.fst, biprod.inl_fst⟩ h

/-- If `X ⊞ Y` is compact, so is `Y`. -/
theorem of_biprod_right (h : IsCompact.{w} (X ⊞ Y)) : IsCompact.{w} Y :=
  of_retract ⟨biprod.inr, biprod.snd, biprod.inr_snd⟩ h

end biprod

end IsCompact

/-- `X ⊞ Y` is compact if and only if both `X` and `Y` are compact. -/
theorem isCompact_biprod_iff (X Y : C) [HasBinaryBiproduct X Y] :
    IsCompact.{w} (X ⊞ Y) ↔ IsCompact.{w} X ∧ IsCompact.{w} Y :=
  ⟨fun h => ⟨h.of_biprod_left, h.of_biprod_right⟩, fun h => h.1.biprod h.2⟩

/-- The property of being compact is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_isCompact :
    ObjectProperty.IsClosedUnderIsomorphisms (IsCompact.{w} (C := C)) where
  of_iso e hX := hX.of_iso e.symm

section coyoneda

open Opposite

variable {ι : Type w} [DecidableEq ι] (X : C) (Y : ι → C) [HasCoproduct Y]

/-- If the comparison map of `X` for the family `Y` is bijective, the functor
`Hom(X, -) : C ⥤ AddCommGrp` preserves the coproduct of `Y`. -/
theorem preservesColimit_of_bijective (h : Function.Bijective (coproductComparison X Y)) :
    PreservesColimit (Discrete.functor Y) (preadditiveCoyoneda.obj (op X)) := by
  let e := AddEquiv.ofBijective _ h
  refine preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct Y) ?_
  refine
    { desc := fun s => AddCommGrp.ofHom
        ((DirectSum.toAddMonoid fun i => (s.ι.app ⟨i⟩).hom).comp e.symm.toAddMonoidHom)
      fac := ?_
      uniq := ?_ }
  · rintro s ⟨i⟩
    ext g
    change (DirectSum.toAddMonoid fun i => (s.ι.app ⟨i⟩).hom) (e.symm (g ≫ Sigma.ι Y i)) =
      (s.ι.app ⟨i⟩).hom g
    rw [show g ≫ Sigma.ι Y i = e (DirectSum.of _ i g) from (coproductComparison_of X Y i g).symm,
      e.symm_apply_apply, DirectSum.toAddMonoid_of]
    rfl
  · intro s m hm
    ext f
    obtain ⟨a, rfl⟩ := h.2 f
    change m.hom (e a) = (DirectSum.toAddMonoid fun i => (s.ι.app ⟨i⟩).hom) (e.symm (e a))
    rw [e.symm_apply_apply]
    have key : m.hom.comp e.toAddMonoidHom =
        DirectSum.toAddMonoid fun i => (s.ι.app ⟨i⟩).hom := by
      ext i g
      simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
      change m.hom (e (DirectSum.of (fun i => (X ⟶ Y i)) i g)) = (s.ι.app ⟨i⟩).hom g
      rw [← hm ⟨i⟩]
      change m.hom (coproductComparison X Y (DirectSum.of (fun i => (X ⟶ Y i)) i g)) =
        m.hom (g ≫ Sigma.ι Y i)
      rw [coproductComparison_of]
    exact DFunLike.congr_fun key a

/-- If the functor `Hom(X, -) : C ⥤ AddCommGrp` preserves the coproduct of `Y`, the comparison
map of `X` for the family `Y` is bijective. The injectivity uses the test cocones projecting onto
one summand, the surjectivity the test cocone with values in the quotient by the image. -/
theorem bijective_of_preservesColimit
    [PreservesColimit (Discrete.functor Y) (preadditiveCoyoneda.obj (op X))] :
    Function.Bijective (coproductComparison X Y) := by
  have hc : IsColimit ((preadditiveCoyoneda.obj (op X)).mapCocone (Cofan.mk _ (Sigma.ι Y))) :=
    isColimitOfPreserves _ (coproductIsCoproduct Y)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    ext j
    let t : Cocone (Discrete.functor Y ⋙ preadditiveCoyoneda.obj (op X)) :=
      { pt := AddCommGrp.of (X ⟶ Y j)
        ι := Discrete.natTrans fun ⟨i⟩ => AddCommGrp.ofHom
          (if h : i = j then Preadditive.rightComp X (eqToHom (congrArg Y h)) else 0) }
    let ev : (DirectSum ι fun i => (X ⟶ Y i)) →+ (X ⟶ Y j) :=
      { toFun := fun a => a j
        map_zero' := DirectSum.zero_apply _ j
        map_add' := fun a b => DirectSum.add_apply a b j }
    have key : (hc.desc t).hom.comp (coproductComparison X Y) = ev := by
      ext i g
      change (hc.desc t).hom (coproductComparison X Y (DirectSum.of (fun i => (X ⟶ Y i)) i g)) =
        (DirectSum.of (fun i => (X ⟶ Y i)) i g) j
      rw [coproductComparison_of]
      have := congrArg (fun φ => φ.hom g) (hc.fac t ⟨i⟩)
      change (hc.desc t).hom (g ≫ Sigma.ι Y i) = _ at this
      rw [this]
      by_cases hij : i = j
      · subst hij
        simp [t, Preadditive.rightComp]
      · simp [t, hij, DirectSum.of_eq_of_ne _ _ _ hij]
    have h4 : (hc.desc t).hom (coproductComparison X Y a) = a j := DFunLike.congr_fun key a
    rw [ha, map_zero] at h4
    rw [DirectSum.zero_apply]
    exact h4.symm

  · intro f
    let S := (coproductComparison X Y).range
    let t : Cocone (Discrete.functor Y ⋙ preadditiveCoyoneda.obj (op X)) :=
      { pt := AddCommGrp.of ((X ⟶ ∐ Y) ⧸ S)
        ι := Discrete.natTrans fun _ => 0 }
    have h1 : hc.desc t = AddCommGrp.ofHom (QuotientAddGroup.mk' S) := by
      symm
      apply hc.uniq t
      rintro ⟨i⟩
      ext g
      change QuotientAddGroup.mk' S (g ≫ Sigma.ι Y i) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨DirectSum.of _ i g, coproductComparison_of X Y i g⟩
    have h2 : hc.desc t = 0 := by
      refine (hc.uniq t 0 ?_).symm
      rintro ⟨i⟩
      simp [t]
    have h3 := congrArg (fun φ => φ.hom f) (h1.symm.trans h2)
    change QuotientAddGroup.mk' S f = 0 at h3
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h3
    exact h3

/-- `X` is compact if and only if the functor `Hom(X, -) : C ⥤ AddCommGrp` preserves coproducts
indexed by types in `Type w`. -/
theorem isCompact_iff_preservesColimitsOfShape (X : C) :
    IsCompact.{w} X ↔
      ∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) (preadditiveCoyoneda.obj (op X)) := by
  constructor
  · intro hX ι
    have : ∀ Y : ι → C,
        PreservesColimit (Discrete.functor Y) (preadditiveCoyoneda.obj (op X)) := by
      intro Y
      constructor
      intro c hc
      haveI : HasCoproduct Y := HasColimit.mk ⟨c, hc⟩
      classical
      exact (preservesColimit_of_bijective X Y (hX ι Y)).preserves hc
    exact preservesColimitsOfShape_of_discrete _
  · intro h ι _ Y _
    exact bijective_of_preservesColimit X Y

end coyoneda

end DG
