import DG.Category.Resolution.Lifting

/-!
# Uniqueness and functoriality of resolutions over a dg category

Let `C` be a dg category. This file shows that K-projective resolutions of a dg module `M` over
`C` (quasi-isomorphisms `P ⟶ M` from K-projective modules) are unique up to homotopy equivalence
over `M`, that cofibrant (e.g. semi-free) resolutions by surjective quasi-isomorphisms are
unique up to homotopy equivalence strictly over `M`, and that semi-free resolutions are
functorial up to homotopy. As a consequence, the dg modules with the lifting property against
surjective quasi-isomorphisms (the cofibrant ones) are the retracts of semi-free modules, and the
K-projective dg modules are those homotopy equivalent to semi-free modules. It is a port of the
corresponding part of `DG.Derived.Resolution` (the case of a dg ring, i.e. of a one-object dg
category).

## Main definitions and results

* `DG.CatModule.IsKProjective.homotopic_of_comp_eq`,
  `DG.CatModule.IsKProjective.exists_homotopic_comp`,
  `DG.CatModule.IsKProjective.homotopic_of_homotopic_comp`: maps out of a K-projective module
  factor through quasi-isomorphisms up to homotopy, uniquely up to homotopy.
* Uniqueness: `DG.CatModule.IsKProjective.exists_dgHomotopyEquiv` (K-projective resolutions
  are homotopy equivalent over `M` up to homotopy),
  `DG.CatModule.HasLiftingProperty.exists_dgHomotopyEquiv` (cofibrant resolutions by surjective
  quasi-isomorphisms are homotopy equivalent strictly over `M`),
  `DG.CatModule.SemiFreeResolution.dgHomotopyEquiv`.
* `DG.CatModule.SemiFreeResolution M`: a bundled semi-free resolution;
  `DG.CatModule.semiFreeResolution M` constructs one (`DG.CatModule.Resolution.colim`).
* Functoriality: `DG.CatModule.SemiFreeResolution.lift` (a morphism `M ⟶ N` lifts to
  resolutions, strictly over the augmentations), unique up to homotopy
  (`DG.CatModule.SemiFreeResolution.homotopic_lift`), compatible with homotopies, identities
  and composition up to homotopy (`DG.CatModule.SemiFreeResolution.lift_homotopic`,
  `DG.CatModule.SemiFreeResolution.lift_id`, `DG.CatModule.SemiFreeResolution.lift_comp`).
* `DG.CatModule.hasLiftingProperty_iff_exists_retract`: a dg module has the lifting property
  against surjective quasi-isomorphisms iff it is a retract of a semi-free dg module.
* `DG.CatModule.isKProjective_iff_exists_dgHomotopyEquiv`: a dg module is K-projective iff it is
  homotopy equivalent to a semi-free dg module.

## Universes

K-projectivity and the lifting property are stated for test modules in the universe of the
module, so the uniqueness and functoriality statements take all modules in one universe. The
standard resolution of `M : CatModule.{max u v w} C` (for `C : Type u` with Hom types in
`Type v`) lives in the same universe, which is therefore the universe of the characterizations
`DG.CatModule.hasLiftingProperty_iff_exists_retract` and
`DG.CatModule.isKProjective_iff_exists_dgHomotopyEquiv`.

## References

* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994), §3]
* [J. Bernstein, V. Lunts, *Equivariant sheaves and functors*, LNM 1578 (1994), §10.12]
* [The Stacks project, Tags 09KK, 09KP, 09KV]
-/

open CategoryTheory

universe w v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### Maps out of K-projective modules -/

section Uniqueness

variable {P Q N N' : CatModule.{w} C}

/-- Maps from a K-projective module to a module `Q` with an objectwise surjective
quasi-isomorphism `q : Q ⟶ N` are determined up to homotopy by their composite with `q`: if
`f₁ ≫ q = f₂ ≫ q`, then `f₁ ≃ f₂`, since `f₁ - f₂` lands in the acyclic kernel of `q`. -/
theorem IsKProjective.homotopic_of_comp_eq (hP : IsKProjective P) {q : Q ⟶ N}
    (hq : ∀ X, Function.Surjective (q.app X)) (hqq : IsQuasiIso q) {f₁ f₂ : P ⟶ Q}
    (h : f₁ ≫ q = f₂ ≫ q) : Homotopic f₁ f₂ := by
  rw [Homotopic.iff_sub]
  have hmem : ∀ X x, (f₁ - f₂).app X x ∈ (Hom.ker q).carrier X := fun X x => by
    rw [Hom.mem_ker, sub_app, map_sub, ← comp_app, h, comp_app, sub_self]
  have h1 := (hP _ (Hom.isAcyclic_ker q hq hqq)
    (CatSubmodule.codRestrict (f₁ - f₂) hmem)).comp_right (Hom.ker q).subtype
  rwa [CatSubmodule.codRestrict_comp_subtype, Limits.zero_comp] at h1

/-- For a K-projective `P` and a quasi-isomorphism `s : N ⟶ N'`, every morphism `P ⟶ N'` factors
through `s` up to homotopy. -/
theorem IsKProjective.exists_homotopic_comp [DGCategory C] (hP : IsKProjective P) {s : N ⟶ N'}
    (hs : IsQuasiIso s) (g : P ⟶ N') : ∃ f : P ⟶ N, Homotopic (f ≫ s) g := by
  obtain ⟨c, hc⟩ := (hP.bijective_postcompHomotopy hs).2 (QuotientAddGroup.mk g)
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [postcompHomotopy_mk, QuotientAddGroup.eq_iff_sub_mem] at hc
  exact ⟨f, homotopic_iff_sub_mem.mpr hc⟩

/-- For a K-projective `P` and a quasi-isomorphism `s : N ⟶ N'`, morphisms `f₁ f₂ : P ⟶ N` with
`f₁ ≫ s ≃ f₂ ≫ s` are homotopic. -/
theorem IsKProjective.homotopic_of_homotopic_comp [DGCategory C] (hP : IsKProjective P)
    {s : N ⟶ N'} (hs : IsQuasiIso s) {f₁ f₂ : P ⟶ N} (h : Homotopic (f₁ ≫ s) (f₂ ≫ s)) :
    Homotopic f₁ f₂ := by
  have h' : postcompHomotopy P s (QuotientAddGroup.mk f₁) =
      postcompHomotopy P s (QuotientAddGroup.mk f₂) := by
    rw [postcompHomotopy_mk, postcompHomotopy_mk, QuotientAddGroup.eq_iff_sub_mem,
      ← homotopic_iff_sub_mem]
    exact h
  exact homotopic_iff_sub_mem.mpr
    (QuotientAddGroup.eq_iff_sub_mem.mp ((hP.bijective_postcompHomotopy hs).1 h'))

end Uniqueness

/-! ### Uniqueness of resolutions up to homotopy equivalence -/

section HomotopyEquiv

variable [DGCategory C] {P P' M : CatModule.{w} C}

/-- Uniqueness of K-projective resolutions up to homotopy equivalence: if `p : P ⟶ M` and
`p' : P' ⟶ M` are quasi-isomorphisms from K-projective modules, there is a homotopy equivalence
`e : P ≃ P'` with `e.hom ≫ p' ≃ p` and `e.inv ≫ p ≃ p'`. -/
theorem IsKProjective.exists_dgHomotopyEquiv (hP : IsKProjective P) (hP' : IsKProjective P')
    {p : P ⟶ M} (hp : IsQuasiIso p) {p' : P' ⟶ M} (hp' : IsQuasiIso p') :
    ∃ e : DGHomotopyEquiv P P', Homotopic (e.hom ≫ p') p ∧ Homotopic (e.inv ≫ p) p' := by
  obtain ⟨φ, hφ⟩ := hP.exists_homotopic_comp hp' p
  obtain ⟨ψ, hψ⟩ := hP'.exists_homotopic_comp hp p'
  have h₁ : Homotopic (φ ≫ ψ) (𝟙 P) := hP.homotopic_of_homotopic_comp hp
    ((Homotopic.of_eq (Category.assoc _ _ _)).trans (((hψ.comp_left φ)).trans
      (hφ.trans (Homotopic.of_eq (Category.id_comp p).symm))))
  have h₂ : Homotopic (ψ ≫ φ) (𝟙 P') := hP'.homotopic_of_homotopic_comp hp'
    ((Homotopic.of_eq (Category.assoc _ _ _)).trans (((hφ.comp_left ψ)).trans
      (hψ.trans (Homotopic.of_eq (Category.id_comp p').symm))))
  exact ⟨⟨φ, ψ, h₁.some, h₂.some⟩, hφ, hψ⟩

/-- Uniqueness of cofibrant (e.g. semi-free) resolutions up to homotopy equivalence over `M`: if
`p : P ⟶ M` and `p' : P' ⟶ M` are objectwise surjective quasi-isomorphisms and `P`, `P'` have
the lifting property against surjective quasi-isomorphisms, there is a homotopy equivalence
`e : P ≃ P'` with `e.hom ≫ p' = p` and `e.inv ≫ p = p'`. -/
theorem HasLiftingProperty.exists_dgHomotopyEquiv (hP : HasLiftingProperty P)
    (hP' : HasLiftingProperty P') {p : P ⟶ M} (hps : ∀ X, Function.Surjective (p.app X))
    (hp : IsQuasiIso p) {p' : P' ⟶ M} (hps' : ∀ X, Function.Surjective (p'.app X))
    (hp' : IsQuasiIso p') :
    ∃ e : DGHomotopyEquiv P P', e.hom ≫ p' = p ∧ e.inv ≫ p = p' := by
  obtain ⟨φ, hφ⟩ := hP P' M p' hps' hp' p
  obtain ⟨ψ, hψ⟩ := hP' P M p hps hp p'
  have h₁ : Homotopic (φ ≫ ψ) (𝟙 P) := hP.isKProjective.homotopic_of_comp_eq hps hp
    (by rw [Category.assoc, hψ, hφ, Category.id_comp])
  have h₂ : Homotopic (ψ ≫ φ) (𝟙 P') := hP'.isKProjective.homotopic_of_comp_eq hps' hp'
    (by rw [Category.assoc, hφ, hψ, Category.id_comp])
  exact ⟨⟨φ, ψ, h₁.some, h₂.some⟩, hφ, hψ⟩

end HomotopyEquiv

/-! ### Bundled semi-free resolutions -/

section Bundled

variable [DGCategory C]

/-- A semi-free resolution of a dg module `M` over `C`: an objectwise surjective
quasi-isomorphism `π : P ⟶ M` from a dg module `P` (in the universe of `M`) with a chosen
semi-free filtration, whose generators are indexed by types in the universe `w`. -/
structure SemiFreeResolution (M : CatModule.{max v w} C) where
  /-- The resolving module. -/
  P : CatModule.{max v w} C
  /-- The augmentation `P ⟶ M`. -/
  π : P ⟶ M
  surjective_π : ∀ X, Function.Surjective (π.app X)
  isQuasiIso_π : IsQuasiIso π
  /-- A semi-free filtration of `P`. -/
  filtration : SemiFreeFiltration.{w} P

namespace SemiFreeResolution

variable {M N L : CatModule.{max v w} C}

/-- The resolving module of a semi-free resolution has the lifting property against surjective
quasi-isomorphisms. -/
theorem hasLiftingProperty (R : SemiFreeResolution.{w} M) : HasLiftingProperty R.P :=
  R.filtration.hasLiftingProperty

/-- The resolving module of a semi-free resolution is K-projective. -/
theorem isKProjective (R : SemiFreeResolution.{w} M) : IsKProjective R.P :=
  R.filtration.isKProjective

/-- Any two semi-free resolutions of `M` are homotopy equivalent over `M`. -/
theorem exists_dgHomotopyEquiv (R R' : SemiFreeResolution.{w} M) :
    ∃ e : DGHomotopyEquiv R.P R'.P, e.hom ≫ R'.π = R.π ∧ e.inv ≫ R.π = R'.π :=
  R.hasLiftingProperty.exists_dgHomotopyEquiv R'.hasLiftingProperty R.surjective_π
    R.isQuasiIso_π R'.surjective_π R'.isQuasiIso_π

/-- The homotopy equivalence over `M` between two semi-free resolutions of `M`. -/
noncomputable def dgHomotopyEquiv (R R' : SemiFreeResolution.{w} M) :
    DGHomotopyEquiv R.P R'.P :=
  (R.exists_dgHomotopyEquiv R').choose

@[simp]
theorem dgHomotopyEquiv_hom_comp_π (R R' : SemiFreeResolution.{w} M) :
    (R.dgHomotopyEquiv R').hom ≫ R'.π = R.π :=
  (R.exists_dgHomotopyEquiv R').choose_spec.1

@[simp]
theorem dgHomotopyEquiv_inv_comp_π (R R' : SemiFreeResolution.{w} M) :
    (R.dgHomotopyEquiv R').inv ≫ R.π = R'.π :=
  (R.exists_dgHomotopyEquiv R').choose_spec.2

/-- A morphism `g : M ⟶ N` lifts to semi-free resolutions:
`R.lift R' g ≫ R'.π = R.π ≫ g`. -/
noncomputable def lift (R : SemiFreeResolution.{w} M) (R' : SemiFreeResolution.{w} N)
    (g : M ⟶ N) : R.P ⟶ R'.P :=
  (R.hasLiftingProperty R'.P N R'.π R'.surjective_π R'.isQuasiIso_π (R.π ≫ g)).choose

@[simp, reassoc]
theorem lift_comp_π (R : SemiFreeResolution.{w} M) (R' : SemiFreeResolution.{w} N)
    (g : M ⟶ N) : R.lift R' g ≫ R'.π = R.π ≫ g :=
  (R.hasLiftingProperty R'.P N R'.π R'.surjective_π R'.isQuasiIso_π (R.π ≫ g)).choose_spec

/-- The lift of `g : M ⟶ N` to resolutions is unique up to homotopy: every `f : R.P ⟶ R'.P`
with `f ≫ R'.π ≃ R.π ≫ g` is homotopic to it. -/
theorem homotopic_lift (R : SemiFreeResolution.{w} M) (R' : SemiFreeResolution.{w} N)
    {g : M ⟶ N} {f : R.P ⟶ R'.P} (h : Homotopic (f ≫ R'.π) (R.π ≫ g)) :
    Homotopic f (R.lift R' g) :=
  R.isKProjective.homotopic_of_homotopic_comp R'.isQuasiIso_π
    (h.trans (Homotopic.of_eq (R.lift_comp_π R' g).symm))

/-- Homotopic morphisms have homotopic lifts. -/
theorem lift_homotopic (R : SemiFreeResolution.{w} M) (R' : SemiFreeResolution.{w} N)
    {g₁ g₂ : M ⟶ N} (h : Homotopic g₁ g₂) : Homotopic (R.lift R' g₁) (R.lift R' g₂) :=
  R.homotopic_lift R' ((Homotopic.of_eq (R.lift_comp_π R' g₁)).trans (h.comp_left R.π))

/-- The lift of the identity is homotopic to the identity. -/
theorem lift_id (R : SemiFreeResolution.{w} M) : Homotopic (R.lift R (𝟙 M)) (𝟙 R.P) :=
  (R.homotopic_lift R (f := 𝟙 R.P)
    (Homotopic.of_eq (by rw [Category.id_comp, Category.comp_id]))).symm

/-- Lifts to resolutions are compatible with composition up to homotopy. -/
theorem lift_comp (R : SemiFreeResolution.{w} M) (R' : SemiFreeResolution.{w} N)
    (R'' : SemiFreeResolution.{w} L) (g : M ⟶ N) (g' : N ⟶ L) :
    Homotopic (R.lift R'' (g ≫ g')) (R.lift R' g ≫ R'.lift R'' g') :=
  (R.homotopic_lift R'' (Homotopic.of_eq (by
    rw [Category.assoc, lift_comp_π, lift_comp_π_assoc]))).symm

end SemiFreeResolution

/-- The standard semi-free resolution of a dg module `M : CatModule.{max u v w} C`
(`DG.CatModule.Resolution.colim`). -/
noncomputable def semiFreeResolution (M : CatModule.{max u v w} C) :
    SemiFreeResolution.{max u v w} M where
  P := Resolution.colim M
  π := Resolution.π M
  surjective_π := Resolution.surjective_π M
  isQuasiIso_π := Resolution.isQuasiIso_π M
  filtration := Resolution.semiFreeFiltration M

end Bundled

/-! ### Cofibrant and K-projective modules via semi-free modules -/

section Cofibrant

variable [DGCategory C]

/-- The lifting property against surjective quasi-isomorphisms passes to retracts. -/
theorem HasLiftingProperty.of_retract {P Q : CatModule.{w} C} (hP : HasLiftingProperty P)
    (i : Q ⟶ P) (r : P ⟶ Q) (hri : i ≫ r = 𝟙 Q) : HasLiftingProperty Q :=
  hasLiftingProperty_iff.mpr ⟨(hasLiftingProperty_iff.mp hP).1.of_retract i r
    (Homotopic.of_eq hri), (hasLiftingProperty_iff.mp hP).2.of_retract i r hri⟩

variable {P : CatModule.{max u v w} C}

/-- The cofibrant dg modules over `C` (those with the lifting property against surjective
quasi-isomorphisms) are exactly the retracts of semi-free dg modules. The forward direction
lifts the identity of `P` along a semi-free resolution of `P`. -/
theorem hasLiftingProperty_iff_exists_retract :
    HasLiftingProperty P ↔
      ∃ (Q : CatModule.{max u v w} C) (_ : SemiFreeFiltration.{max u v w} Q) (i : P ⟶ Q)
        (r : Q ⟶ P), i ≫ r = 𝟙 P := by
  constructor
  · intro h
    let R := semiFreeResolution P
    obtain ⟨i, hi⟩ := h R.P P R.π R.surjective_π R.isQuasiIso_π (𝟙 P)
    exact ⟨R.P, R.filtration, i, R.π, hi⟩
  · rintro ⟨Q, S, i, r, hri⟩
    exact S.hasLiftingProperty.of_retract i r hri

/-- The K-projective dg modules over `C` are exactly the dg modules homotopy equivalent to
semi-free dg modules. -/
theorem isKProjective_iff_exists_dgHomotopyEquiv :
    IsKProjective P ↔
      ∃ (Q : CatModule.{max u v w} C) (_ : SemiFreeFiltration.{max u v w} Q),
        Nonempty (DGHomotopyEquiv P Q) := by
  constructor
  · intro h
    let R := semiFreeResolution P
    obtain ⟨e, -, -⟩ := h.exists_dgHomotopyEquiv R.isKProjective (p := 𝟙 P) (isQuasiIso_id P)
      R.isQuasiIso_π
    exact ⟨R.P, R.filtration, ⟨e⟩⟩
  · rintro ⟨Q, S, ⟨e⟩⟩
    exact S.isKProjective.of_dgHomotopyEquiv e

end Cofibrant

end CatModule

end DG
