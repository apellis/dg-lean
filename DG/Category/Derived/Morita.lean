import DG.Category.Corner
import DG.Category.Derived.Keller
import DG.Category.Derived.RestrictionIso

/-!
# Morita theory for idempotents in dg categories

## Derived induction along a quasi-fully faithful dg functor

Let `F : C ⥤ D` be a dg functor which is quasi-fully faithful (`DG.IsQuasiFullyFaithful F`). By
the first half of the proof of Keller's theorem, the unit of `LF_! ⊣ F^*` is an isomorphism, so
`LF_! : D(C) ⥤ D(D)` is fully faithful. It is an equivalence if and only if restriction along `F`
reflects acyclicity of dg modules (`DG.CatModule.DerivedCategory.restrict_isEquivalence_iff`),
and then `DG.CatModule.DerivedCategory.inductionEquivalence` is the equivalence.

A sufficient condition (`DG.IsSummandDense F`): every object `Y` of `D` is, in `H⁰(D)`, a direct
summand of a finite direct sum of objects `F X`, i.e. there are degree-`0` cocycles
`aₖ : Y ⟶ F Xₖ`, `bₖ : F Xₖ ⟶ Y` with `∑ₖ aₖ ≫ bₖ - 𝟙 Y` a coboundary. This generalizes the
essential surjectivity on `H⁰` in the definition of a quasi-equivalence.

## Idempotents

For a family `P` of degree-`0` cocycle idempotents `eᵢ : Xᵢ ⟶ Xᵢ` in a dg category `C`, with
corner dg category `P.Corner` (`P.Corner(i, j) = eᵢ C(Xᵢ, Xⱼ) eⱼ`, `DG.IdempotentFamily`), both
`C` and `P.Corner` embed into `P.augment.Corner` by dg functors which are isomorphisms on Hom
complexes (`P.inl`, `P.inr`). Each object `(Xᵢ, eᵢ)` is a direct summand of `P.inl Xᵢ`, so
`LP.inl_!` is always an equivalence. If the idempotents are *full up to homotopy*
(`DG.IdempotentFamily.IsFullH0`: every object `X` of `C` satisfies
`𝟙 X = ∑ₖ aₖ ≫ e_{iₖ} ≫ bₖ + d s` with `aₖ`, `bₖ` degree-`0` cocycles), then `LP.inr_!` is an
equivalence too, and

  `DG.IdempotentFamily.moritaEquivalence : D(P.Corner) ≌ D(C)`,

with functor `LP.inr_! ⋙ P.inl^*` and inverse `LP.inl_! ⋙ P.inr^*`, both triangulated. On a dg
`P.Corner`-module `M` the functor is (derived) `⊕ᵢ C(Xᵢ, -) eᵢ ⊗_{P.Corner} M`, i.e.
`C e ⊗_{eCe} -`; the inverse is (derived) `e C ⊗_C -`, i.e. `N ↦ (eᵢ N(Xᵢ))ᵢ`. More generally the
equivalence exists as soon as restriction along `P.inr` reflects acyclicity
(`DG.IdempotentFamily.moritaEquivalenceOfReflects`), and this condition is necessary for `P.inr^*`
to be an equivalence.

**Remark (the hypothesis).** The condition "the idempotents generate the unit ideal", i.e.
`𝟙 X = ∑ₖ aₖ ≫ e ≫ bₖ` with arbitrary (not necessarily closed) `aₖ`, `bₖ`, is *not* sufficient;
see `DG.Examples.MoritaCounterexample`.

## Main definitions and results

* `DG.IsQuasiFullyFaithful.of_bijective`, `DG.IsSummandDense`,
  `DG.CatModule.isAcyclic_of_isAcyclic_precomp_of_isSummandDense`.
* `DG.CatModule.DerivedCategory.restrict_isEquivalence_iff`.
* `DG.IdempotentFamily.IsFullH0`, `DG.IdempotentFamily.isSummandDense_inl`,
  `DG.IdempotentFamily.isSummandDense_inr`, `DG.IdempotentFamily.moritaEquivalenceOfReflects`,
  `DG.IdempotentFamily.moritaEquivalence`,
  `DG.IdempotentFamily.moritaEquivalence_functor_isTriangulated`.
-/

open CategoryTheory Limits Pretriangulated

universe t w₂ w v v₁ v₂ u u₁ u₂

set_option backward.isDefEq.respectTransparency false

namespace DG

section General

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

omit [DGCategory C] [DGCategory D] in
/-- A dg functor which is bijective on Hom groups and reflects the grading is quasi-fully
faithful. -/
theorem IsQuasiFullyFaithful.of_bijective
    (hbij : ∀ X X' : C, Function.Bijective (F.map : (X ⟶ X') → (F.obj X ⟶ F.obj X')))
    (hmem : ∀ {X X' : C} {n : ℤ} {f : X ⟶ X'}, F.map f ∈ grading n → f ∈ grading n) :
    IsQuasiFullyFaithful F where
  bijective_cohomology X X' n := by
    rw [Function.Bijective, cohomology.mapAddMonoidHom_injective_iff,
      cohomology.mapAddMonoidHom_surjective_iff]
    constructor
    · rintro x - - ⟨y, hy, hdy⟩
      obtain ⟨y', rfl⟩ := (hbij X X').2 y
      exact ⟨y', hmem hy, (hbij X X').1 ((F.map_d y').trans hdy)⟩
    · intro y hy hdy
      obtain ⟨x, rfl⟩ := (hbij X X').2 y
      refine ⟨x, hmem hy, (hbij X X').1 (by rw [F.map_d, hdy, F.map_zero]), ?_⟩
      change F.map x - F.map x ∈ _
      rw [sub_self]
      exact zero_mem _

/-- Every object `Y` of `D` is a direct summand in `H⁰(D)` of a finite direct sum of objects in
the image of `F`: there are degree-`0` cocycles `aₖ : Y ⟶ F Xₖ` and `bₖ : F Xₖ ⟶ Y` such that
`∑ₖ aₖ ≫ bₖ - 𝟙 Y` is a coboundary. -/
def IsSummandDense : Prop :=
  ∀ Y : D, ∃ (n : ℕ) (X : Fin n → C) (a : ∀ k, Y ⟶ F.obj (X k)) (b : ∀ k, F.obj (X k) ⟶ Y),
    (∀ k, a k ∈ cocycles (Y ⟶ F.obj (X k)) 0) ∧ (∀ k, b k ∈ cocycles (F.obj (X k) ⟶ Y) 0) ∧
      ∑ k, a k ≫ b k - 𝟙 Y ∈ coboundaries (Y ⟶ Y) 0

variable {F}

omit [DGCategory C] [DGCategory D] in
/-- A quasi-equivalence is summand-dense. -/
theorem IsQuasiEquivalence.isSummandDense (hF : IsQuasiEquivalence F) : IsSummandDense F := by
  intro Y
  obtain ⟨X, a, b, ha, hb, -, hba⟩ := hF.exists_iso Y
  exact ⟨1, fun _ => X, fun _ => b, fun _ => a, fun _ => hb, fun _ => ha, by simpa using hba⟩

namespace CatModule

omit [DGCategory C] [DGCategory D] in
/-- Restriction along a summand-dense dg functor reflects acyclicity: if `N(F X)` is acyclic for
every `X`, then `N` is acyclic. -/
theorem isAcyclic_of_isAcyclic_precomp_of_isSummandDense (hF : IsSummandDense F)
    {N : CatModule.{w} D} (h : IsAcyclic ((precomp F).obj N)) : IsAcyclic N := by
  intro Y
  obtain ⟨n, X, a, b, ha, hb, ht⟩ := hF Y
  obtain ⟨t, ht, hdt⟩ := mem_coboundaries.mp ht
  refine DG.isAcyclic_iff.mpr fun k y hy hdy => ?_
  have hay (i : Fin n) : ∃ z : N.obj (F.obj (X i)), z ∈ grading (k - 1) ∧ d z = a i • y := by
    have hday : d (a i • y) = 0 := by
      rw [d_smul (ha i).1, (ha i).2, hdy]
      simp
    exact DG.isAcyclic_iff.mp (h (X i)) k (a i • y)
      (by simpa using smul_mem_grading (ha i).1 hy) hday
  choose z hz hdz using hay
  refine ⟨∑ i, b i • z i - t • y, sub_mem (sum_mem fun i _ => by
    simpa using smul_mem_grading (hb i).1 (hz i))
    (by simpa [sub_eq_neg_add] using smul_mem_grading ht hy), ?_⟩
  have e1 (i : Fin n) : d (b i • z i) = (a i ≫ b i) • y := by
    rw [d_smul (hb i).1, (hb i).2, zero_smul, zero_add, koszulSign_zero, one_smul, hdz,
      comp_smul]
  have e2 : d (t • y) = (∑ i, a i ≫ b i) • y - y := by
    rw [d_smul ht, hdy, hdt, sub_smul, id_smul]
    simp
  rw [d_sub, map_sum, Finset.sum_congr rfl fun i _ => e1 i, e2, ← sum_smul]
  abel

end CatModule

namespace CatModule.DerivedCategory

variable [HasDerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C]
  [HasDerivedCategory.{w₂, max u₁ v₁ v₂ w} D]

variable (F) in
/-- For a quasi-fully faithful dg functor `F`, restriction `F^* : D(D) ⥤ D(C)` is an equivalence
if and only if restriction of dg modules along `F` reflects acyclicity. -/
theorem restrict_isEquivalence_iff (hF : IsQuasiFullyFaithful F) :
    (restrict F : DerivedCategory.{w₂, max u₁ v₁ v₂ w} D ⥤
      DerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C).IsEquivalence ↔
      ∀ N : CatModule.{max u₁ v₁ v₂ w} D, IsAcyclic ((precomp F).obj N) → IsAcyclic N := by
  refine ⟨fun _ N hN => ?_, fun hR => (inductionEquivalence.{w} hF hR).isEquivalence_inverse⟩
  rw [← isZero_Q_obj_iff (C := D)]
  refine IsZero.of_full_of_faithful_of_isZero (restrict F) _ ?_
  rw [← isZero_Q_obj_iff (C := C)] at hN
  have e : (restrict F).obj (Q.obj N) ≅
      (Q.obj ((precomp F).obj N) : DerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C) :=
    (QCompRestrictIso F).app N
  exact IsZero.of_iso hN e

/-- For a quasi-fully faithful, summand-dense dg functor `F`, derived induction
`LF_! : D(C) ≌ D(D)` is an equivalence, with quasi-inverse the restriction `F^*`. -/
noncomputable def inductionEquivalenceOfIsSummandDense (hF : IsQuasiFullyFaithful F)
    (hD : IsSummandDense F) :
    DerivedCategory.{max u₁ v₁ v₂ w, max u₁ v₁ v₂ w} C ≌ DerivedCategory.{w₂, max u₁ v₁ v₂ w} D :=
  inductionEquivalence hF fun _ => isAcyclic_of_isAcyclic_precomp_of_isSummandDense hD

end CatModule.DerivedCategory

end General

/-- Transport of a commutation isomorphism along an equivalence: if `G ⋙ E.inverse ≅ E.inverse ⋙ F`
then `E.functor ⋙ G ≅ F ⋙ E.functor`. -/
noncomputable def _root_.CategoryTheory.Equivalence.functorCompIsoOfInverseCompIso
    {𝒳 : Type*} {𝒴 : Type*} [Category 𝒳] [Category 𝒴] (E : 𝒳 ≌ 𝒴) {F : 𝒳 ⥤ 𝒳}
    {G : 𝒴 ⥤ 𝒴} (i : G ⋙ E.inverse ≅ E.inverse ⋙ F) : E.functor ⋙ G ≅ F ⋙ E.functor :=
  let i₁ : F ≅ E.symm.inverse ⋙ (G ⋙ E.inverse) :=
    Iso.isoInverseComp (i.symm : E.symm.functor ⋙ F ≅ G ⋙ E.inverse)
  let i₂ : F ≅ (E.functor ⋙ G) ⋙ E.symm.functor := i₁
  let i₃ : F ⋙ E.symm.inverse ≅ E.functor ⋙ G := Iso.compInverseIso i₂
  i₃.symm

/-! ### Idempotents -/

namespace IdempotentFamily

variable {ι : Type w} {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C] (P : IdempotentFamily ι C)

/-- The idempotents of `P` are *full up to homotopy*: for every object `X` of `C` there are
degree-`0` cocycles `aₖ : X ⟶ X_{iₖ}` and `bₖ : X_{iₖ} ⟶ X` such that
`∑ₖ aₖ ≫ e_{iₖ} ≫ bₖ - 𝟙 X` is a coboundary. Equivalently, `X` is a direct summand in `H⁰` of the
Karoubi envelope of a finite direct sum of the objects `(Xᵢ, eᵢ)`. For a dg ring `A` and a single
idempotent `e`, this says `1 ∈ Z⁰(A) e Z⁰(A) + B⁰(A)`, i.e. the class of `e` generates `H⁰(A)` as
a two-sided ideal. -/
def IsFullH0 : Prop :=
  ∀ X : C, ∃ (n : ℕ) (i : Fin n → ι) (a : ∀ k, X ⟶ P.obj (i k)) (b : ∀ k, P.obj (i k) ⟶ X),
    (∀ k, a k ∈ cocycles (X ⟶ P.obj (i k)) 0) ∧ (∀ k, b k ∈ cocycles (P.obj (i k) ⟶ X) 0) ∧
      ∑ k, a k ≫ P.idem (i k) ≫ b k - 𝟙 X ∈ coboundaries (X ⟶ X) 0

theorem isQuasiFullyFaithful_inl : IsQuasiFullyFaithful P.inl :=
  IsQuasiFullyFaithful.of_bijective _
    (fun _ _ => ⟨fun _ _ h => congrArg Subtype.val h, fun f => ⟨f.1, rfl⟩⟩) id

theorem isQuasiFullyFaithful_inr : IsQuasiFullyFaithful P.inr :=
  IsQuasiFullyFaithful.of_bijective _
    (fun _ _ => ⟨fun _ _ h => hom_ext (congrArg Subtype.val h), fun f => ⟨⟨f.1, f.2⟩, rfl⟩⟩) id

/-- Each object `(Xᵢ, eᵢ)` of `P.augment.Corner` is a direct summand of `P.inl Xᵢ`. -/
theorem isSummandDense_inl : IsSummandDense P.inl := by
  rintro ⟨X | i⟩
  · refine ⟨1, fun _ => X, fun _ => 𝟙 _, fun _ => 𝟙 _, fun _ => id_mem_cocycles _,
      fun _ => id_mem_cocycles _, ?_⟩
    simp
  · let a : (⟨.inr i⟩ : P.augment.Corner) ⟶ P.inl.obj (P.obj i) :=
      ⟨P.idem i, P.idem_comp_idem i, Category.comp_id _⟩
    let b : P.inl.obj (P.obj i) ⟶ (⟨.inr i⟩ : P.augment.Corner) :=
      ⟨P.idem i, Category.id_comp _, P.idem_comp_idem i⟩
    have hab : a ≫ b = 𝟙 _ := hom_ext (P.idem_comp_idem i)
    refine ⟨1, fun _ => P.obj i, fun _ => a, fun _ => b,
      fun _ => mem_cocycles_iff.mpr (P.idem_mem_cocycles i),
      fun _ => mem_cocycles_iff.mpr (P.idem_mem_cocycles i), ?_⟩
    simp [hab]

variable {P}

/-- If the idempotents are full up to homotopy, each object `P.inl X` of `P.augment.Corner` is a
direct summand in `H⁰` of a finite direct sum of objects `(Xᵢ, eᵢ)`. -/
theorem isSummandDense_inr (hP : P.IsFullH0) : IsSummandDense P.inr := by
  rintro ⟨X | i⟩
  · obtain ⟨n, i, a, b, ha, hb, ht⟩ := hP X
    obtain ⟨t, ht, hdt⟩ := mem_coboundaries.mp ht
    refine ⟨n, fun k => ⟨i k⟩,
      fun k => ⟨a k ≫ P.idem (i k), Category.id_comp _, by simp [inr]⟩,
      fun k => ⟨P.idem (i k) ≫ b k, by simp [inr], Category.comp_id _⟩,
      fun k => mem_cocycles_iff.mpr ?_, fun k => mem_cocycles_iff.mpr ?_, ?_⟩
    · exact comp_mem_cocycles (ha k) (P.idem_mem_cocycles (i k))
    · exact comp_mem_cocycles (P.idem_mem_cocycles (i k)) (hb k)
    · refine ⟨⟨t, Category.id_comp _, Category.comp_id _⟩, ht, hom_ext ?_⟩
      simp only [d_val, sub_val, sum_val, comp_val, id_val, Category.assoc,
        P.idem_comp_idem_assoc]
      exact hdt
  · refine ⟨1, fun _ => ⟨i⟩, fun _ => 𝟙 _, fun _ => 𝟙 _, fun _ => id_mem_cocycles _,
      fun _ => id_mem_cocycles _, ?_⟩
    simp

variable (P)

/-- Restriction along `P.inl : C ⥤ P.augment.Corner` reflects acyclicity. -/
theorem isAcyclic_of_isAcyclic_precomp_inl {N : CatModule.{t} P.augment.Corner}
    (h : CatModule.IsAcyclic ((CatModule.precomp P.inl).obj N)) : CatModule.IsAcyclic N :=
  CatModule.isAcyclic_of_isAcyclic_precomp_of_isSummandDense P.isSummandDense_inl h

variable {P}

/-- If the idempotents are full up to homotopy, restriction along
`P.inr : P.Corner ⥤ P.augment.Corner` reflects acyclicity: a dg module `N` over
`P.augment.Corner` such that every `N(Xᵢ, eᵢ)` (that is, `eᵢ N(Xᵢ)`) is acyclic is acyclic. -/
theorem isAcyclic_of_isAcyclic_precomp_inr (hP : P.IsFullH0) {N : CatModule.{t} P.augment.Corner}
    (h : CatModule.IsAcyclic ((CatModule.precomp P.inr).obj N)) : CatModule.IsAcyclic N :=
  CatModule.isAcyclic_of_isAcyclic_precomp_of_isSummandDense (isSummandDense_inr hP) h

section Equivalence

variable (P) [CatModule.HasDerivedCategory.{max u v w t, max u v w t} P.Corner]
  [CatModule.HasDerivedCategory.{max u v w t, max u v w t} C]
  [CatModule.HasDerivedCategory.{w₂, max u v w t} P.augment.Corner]

/-- Derived induction along `P.inl` is an equivalence `LP.inl_! : D(C) ≌ D(P.augment.Corner)`,
with quasi-inverse the restriction `P.inl^*`. -/
noncomputable def inlEquivalence :
    CatModule.DerivedCategory.{max u v w t, max u v w t} C ≌
      CatModule.DerivedCategory.{w₂, max u v w t} P.augment.Corner :=
  CatModule.DerivedCategory.inductionEquivalenceOfIsSummandDense.{w₂, max w t}
    P.isQuasiFullyFaithful_inl P.isSummandDense_inl

/-- **Morita theory for idempotents** (general form). If restriction along
`P.inr : P.Corner ⥤ P.augment.Corner` reflects acyclicity, then `D(P.Corner) ≌ D(C)`, with functor
`LP.inr_! ⋙ P.inl^*` and inverse `LP.inl_! ⋙ P.inr^*`, both triangulated. The hypothesis is also
necessary for `P.inr^*` to be an equivalence (`restrict_isEquivalence_iff`). -/
noncomputable def moritaEquivalenceOfReflects
    (hR : ∀ N : CatModule.{max u v w t} P.augment.Corner,
      CatModule.IsAcyclic ((CatModule.precomp P.inr).obj N) → CatModule.IsAcyclic N) :
    CatModule.DerivedCategory.{max u v w t, max u v w t} P.Corner ≌
      CatModule.DerivedCategory.{max u v w t, max u v w t} C :=
  (CatModule.DerivedCategory.inductionEquivalence.{max u t} P.isQuasiFullyFaithful_inr hR).trans
    (P.inlEquivalence.{t, w₂}).symm

variable {P}

/-- **Morita theory for idempotents in a dg category.** Let `P` be a family of degree-`0` cocycle
idempotents `eᵢ : Xᵢ ⟶ Xᵢ` in a dg category `C` which is full up to homotopy (every object `X` of
`C` has `𝟙 X = ∑ₖ aₖ ≫ e_{iₖ} ≫ bₖ + d s` with `aₖ`, `bₖ` degree-`0` cocycles). Then the derived
category of the corner dg category `P.Corner` (`P.Corner(i, j) = eᵢ C(Xᵢ, Xⱼ) eⱼ`) is equivalent to
that of `C`. The functor `LP.inr_! ⋙ P.inl^*` is derived `C e ⊗_{eCe} -` and its inverse
`LP.inl_! ⋙ P.inr^*` is derived `e C ⊗_C -`; both are triangulated
(`moritaEquivalence_functor`, `moritaEquivalence_inverse`). -/
noncomputable def moritaEquivalence (hP : P.IsFullH0) :
    CatModule.DerivedCategory.{max u v w t, max u v w t} P.Corner ≌
      CatModule.DerivedCategory.{max u v w t, max u v w t} C :=
  P.moritaEquivalenceOfReflects.{t, w₂} fun _ => isAcyclic_of_isAcyclic_precomp_inr hP

theorem moritaEquivalence_functor (hP : P.IsFullH0) :
    (moritaEquivalence.{t, w₂} hP).functor =
      (CatModule.DerivedCategory.induction.{max u v w t, w₂, max u t} P.inr :
        CatModule.DerivedCategory.{max u v w t, max u v w t} P.Corner ⥤
          CatModule.DerivedCategory.{w₂, max u v w t} P.augment.Corner) ⋙
        CatModule.DerivedCategory.restrict P.inl :=
  rfl

theorem moritaEquivalence_inverse (hP : P.IsFullH0) :
    (moritaEquivalence.{t, w₂} hP).inverse =
      (CatModule.DerivedCategory.induction.{max u v w t, w₂, max w t} P.inl :
        CatModule.DerivedCategory.{max u v w t, max u v w t} C ⥤
          CatModule.DerivedCategory.{w₂, max u v w t} P.augment.Corner) ⋙
        CatModule.DerivedCategory.restrict P.inr :=
  rfl

/-- The functor `LP.inr_! ⋙ P.inl^*` of the Morita equivalence is triangulated. -/
theorem moritaEquivalence_functor_isTriangulated :
    ((CatModule.DerivedCategory.induction.{max u v w t, w₂, max u t} P.inr :
      CatModule.DerivedCategory.{max u v w t, max u v w t} P.Corner ⥤
        CatModule.DerivedCategory.{w₂, max u v w t} P.augment.Corner) ⋙
      CatModule.DerivedCategory.restrict P.inl).IsTriangulated :=
  inferInstance

/-- The inverse `LP.inl_! ⋙ P.inr^*` of the Morita equivalence is triangulated. -/
theorem moritaEquivalence_inverse_isTriangulated :
    ((CatModule.DerivedCategory.induction.{max u v w t, w₂, max w t} P.inl :
      CatModule.DerivedCategory.{max u v w t, max u v w t} C ⥤
        CatModule.DerivedCategory.{w₂, max u v w t} P.augment.Corner) ⋙
      CatModule.DerivedCategory.restrict P.inr).IsTriangulated :=
  inferInstance

/-! #### Compatibility with dg endofunctors preserving the family -/

section Map

variable (σ : C ⥤ C) [σ.Additive] [σ.IsDGFunctor] (τ : ι → ι)
  (hobj : ∀ i, σ.obj (P.obj i) = P.obj (τ i))
  (hidem : ∀ i, eqToHom (hobj i).symm ≫ σ.map (P.idem i) ≫ eqToHom (hobj i) = P.idem (τ i))

/-- Restriction along `P.inl` commutes with restriction along `σ`. -/
noncomputable def restrictInlCommIso :
    CatModule.DerivedCategory.restrict (P.mapAugment σ τ hobj hidem) ⋙
        (CatModule.DerivedCategory.restrict P.inl :
          CatModule.DerivedCategory.{w₂, max u v w t} P.augment.Corner ⥤
            CatModule.DerivedCategory.{max u v w t, max u v w t} C) ≅
      CatModule.DerivedCategory.restrict P.inl ⋙ CatModule.DerivedCategory.restrict σ :=
  (CatModule.DerivedCategory.restrictCompIso P.inl _).symm ≪≫
    CatModule.DerivedCategory.restrictNatIso (P.inlCompMapAugmentIso σ τ hobj hidem)
      (fun _ => id_mem_grading _) (fun _ => d_id _) (fun _ => id_mem_grading _)
      (fun _ => d_id _) ≪≫
    CatModule.DerivedCategory.restrictCompIso σ P.inl

/-- Restriction along `P.inr` commutes with restriction along the induced endofunctors. -/
noncomputable def restrictInrCommIso :
    CatModule.DerivedCategory.restrict (P.mapAugment σ τ hobj hidem) ⋙
        (CatModule.DerivedCategory.restrict P.inr :
          CatModule.DerivedCategory.{w₂, max u v w t} P.augment.Corner ⥤
            CatModule.DerivedCategory.{max u v w t, max u v w t} P.Corner) ≅
      CatModule.DerivedCategory.restrict P.inr ⋙
        CatModule.DerivedCategory.restrict (P.mapCorner σ τ hobj hidem) :=
  (CatModule.DerivedCategory.restrictCompIso P.inr _).symm ≪≫
    CatModule.DerivedCategory.restrictNatIso (P.inrCompMapAugmentIso σ τ hobj hidem)
      (fun _ => id_mem_grading _) (fun _ => d_id _) (fun _ => id_mem_grading _)
      (fun _ => d_id _) ≪≫
    CatModule.DerivedCategory.restrictCompIso (P.mapCorner σ τ hobj hidem) P.inr

/-- **The Morita equivalence commutes with dg endofunctors preserving the family.** For a dg
endofunctor `σ` of `C` carrying `P` to itself, the Morita equivalence
`D(P.Corner) ≌ D(C)` intertwines restriction along `σ` and restriction along the induced dg
endofunctor `P.mapCorner σ τ` of `P.Corner`. (For the weight dg category of a bigraded dg ring
and `σ` the shift of weights, this is the compatibility with the internal shift.) -/
noncomputable def moritaEquivalenceFunctorCompRestrictIso (hP : P.IsFullH0) :
    (moritaEquivalence.{t, w₂} hP).functor ⋙ CatModule.DerivedCategory.restrict σ ≅
      CatModule.DerivedCategory.restrict (P.mapCorner σ τ hobj hidem) ⋙
        (moritaEquivalence.{t, w₂} hP).functor :=
  let E := CatModule.DerivedCategory.inductionEquivalence.{max u t, w₂} P.isQuasiFullyFaithful_inr
    fun _ => isAcyclic_of_isAcyclic_precomp_inr hP
  let j : E.functor ⋙ CatModule.DerivedCategory.restrict (P.mapAugment σ τ hobj hidem) ≅
      CatModule.DerivedCategory.restrict (P.mapCorner σ τ hobj hidem) ⋙ E.functor :=
    E.functorCompIsoOfInverseCompIso (P.restrictInrCommIso.{t, w₂} σ τ hobj hidem)
  Functor.isoWhiskerLeft E.functor (P.restrictInlCommIso.{t, w₂} σ τ hobj hidem).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight j (CatModule.DerivedCategory.restrict P.inl) ≪≫
    Functor.associator _ _ _

end Map

end Equivalence

end IdempotentFamily

end DG
