import DG.Bigraded.K0Basis
import DG.Positive.K0Basis

/-!
# Freeness of `K₀` of a positive bigraded dg ring over `ℤ[q, q⁻¹]`

Let `A` be a bigraded dg ring with weight dg category `C_A`, and `K₀(C_A) = K₀(D^c(C_A))`, a
`ℤ[q, q⁻¹]`-module with `qⁿ • [M] = [M⟨n⟩]`. This file proves Roadmap 7.2 (b).

## Graded simple modules are not isomorphic to their shifts over Artinian rings

Let `R = ⨁ₖ Rₖ` be a `ℤ`-graded ring which is (left) Artinian as a ring, e.g. semisimple. If `e` is
a nonzero idempotent of degree `0`, there are no `b ∈ e R_d e`, `c ∈ e R_{-d} e` with
`b c = e = c b` for `d ≠ 0` (`DG.eq_zero_of_mul_eq_of_mem`): the graded module `R e` is not
isomorphic to its shift `(R e)⟨d⟩`. Indeed, for `d > 0`, right multiplication by `e - b` is an
injective endomorphism of the Artinian module `R e` (compare top weight components), hence
surjective, so `y - y b = e` for some `y ∈ R e`; comparing the lowest and the highest weight
components of `y - y b` gives a contradiction.

This is where the hypothesis of (b) enters: for a graded positive `A` with `A⁰` merely graded
semisimple the statement fails, since over a graded division ring with a unit of weight `d ≠ 0`
the graded simple module is isomorphic to its shift `⟨d⟩`.

## Main results

* `DG.WeightCategory.eq_of_equiv`: for `A⁰` Artinian (in particular semisimple), the cells
  `e · C_A(k, -)` and `e · C_A(l, -)` of a nonzero idempotent `e ∈ A^{0,0}` are equivalent only if
  `k = l`.
* `DG.WeightCategory.ShiftEquiv e f`: idempotents `e`, `f ∈ A^{0,0}` whose graded modules `A⁰ e`,
  `A⁰ f` are isomorphic up to a shift of weights (`DG.WeightCategory.shiftEquiv_iff`: there are
  `b ∈ e A^{0,d} f`, `c ∈ f A^{0,-d} e` with `b c = e`, `c b = f`).
* `DG.laurentBasisOfShift`: a `ℤ`-basis `(b (a, n))` of a `ℤ[q, q⁻¹]`-module with
  `qⁿ • b (a, 0) = b (a, n)` gives the `ℤ[q, q⁻¹]`-basis `(b (a, 0))`.
* `DG.IsGradedPositive.laurentBasis`: **`K₀(C_A)` is free over `ℤ[q, q⁻¹]`** on the classes
  `[e · C_A(0, -)]` (the bigraded modules `A e`) of a set of representatives of the graded simple
  idempotents `e ∈ A^{0,0}` up to `ShiftEquiv`, i.e. of the graded simple `A⁰`-modules up to
  isomorphism and shift, when `A` is graded positive and `A⁰` is Artinian; this covers
  `DG.IsPositive` (`A⁰` semisimple, `DG.IsPositive.laurentBasis`).
* `DG.IsPositive.K0EquivLaurentOfDivisionRing`: `K₀(C_A) ≅ ℤ[q, q⁻¹]`, `[A] ↦ 1` (so
  `[A⟨n⟩] ↦ qⁿ`), when `A⁰` is a division ring; `DG.IsPositive.K0EquivLaurentOfField` for a dg
  algebra over a field `k` with `A⁰ = k` (e.g. `A = k` in bidegree `(0, 0)`).
-/

open CategoryTheory Limits DirectSum

universe w u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

/-! ### Graded modules over Artinian graded rings are not isomorphic to their shifts -/

section Graded

variable {R : Type*} [Ring R] (𝒜 : ℤ → AddSubgroup R) [GradedRing 𝒜]

/-- If `b` has degree `d > 0` and `b c = e` for an element `e` of degree `0`, then for `y` with
`y e = y`, `y - y b` is homogeneous only if `y = 0`: its lowest weight component is that of `y`,
and its highest one is `-(y_K b) ≠ 0` in weight `K + d`, `K` the top weight of `y`. -/
theorem eq_zero_of_sub_mul_mem {e b c y : R} {d j : ℤ} (hd : 0 < d) (he0 : e ∈ 𝒜 0)
    (hb : b ∈ 𝒜 d) (hbc : b * c = e) (hy : y * e = y) (hj : y - y * b ∈ 𝒜 j) : y = 0 := by
  classical
  by_contra hy0
  set S := (decompose 𝒜 y).support with hS
  have hmem : ∀ i, i ∈ S ↔ (decompose 𝒜 y i : R) ≠ 0 := fun i => by
    rw [hS, DFinsupp.mem_support_iff, ne_eq, ne_eq, ZeroMemClass.coe_eq_zero]
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hy0
    rw [← sum_support_decompose 𝒜 y, ← hS, h, Finset.sum_empty]
  set K := S.max' hSne
  set M := S.min' hSne
  have hK : K ∈ S := S.max'_mem hSne
  have hM : M ∈ S := S.min'_mem hSne
  have hgt : ∀ i, K < i → (decompose 𝒜 y i : R) = 0 := fun i hi => by
    by_contra h
    exact absurd (S.le_max' i ((hmem i).mpr h)) (not_le.mpr hi)
  have hlt : ∀ i, i < M → (decompose 𝒜 y i : R) = 0 := fun i hi => by
    by_contra h
    exact absurd (S.min'_le i ((hmem i).mpr h)) (not_le.mpr hi)
  have hmul : ∀ i, (decompose 𝒜 (y * b) (i + d) : R) = decompose 𝒜 y i * b := fun i =>
    coe_decompose_mul_add_of_right_mem 𝒜 hb
  have hzero : ∀ i, i ≠ j → (decompose 𝒜 (y - y * b) i : R) = 0 := fun i hi =>
    decompose_of_mem_ne 𝒜 hj (Ne.symm hi)
  have hyKe : (decompose 𝒜 y K : R) * e = decompose 𝒜 y K := by
    have h := coe_decompose_mul_add_of_right_mem 𝒜 (a := y) (i := K) he0
    rw [add_zero, hy] at h
    exact h.symm
  have hKb : (decompose 𝒜 y K : R) * b ≠ 0 := fun h =>
    (hmem K).mp hK (by rw [← hyKe, ← hbc, ← mul_assoc, h, zero_mul])
  have h1 : (decompose 𝒜 (y - y * b) (K + d) : R) = -(decompose 𝒜 y K * b) := by
    rw [decompose_sub, DirectSum.sub_apply, AddSubgroup.coe_sub, hgt (K + d) (by omega), hmul,
      zero_sub]
  have hKj : K + d = j := by
    by_contra h
    have h' := hzero _ h
    rw [h1] at h'
    exact hKb (neg_eq_zero.mp h')
  have hmM : (decompose 𝒜 (y * b) M : R) = 0 := by
    have h := hmul (M - d)
    rw [sub_add_cancel] at h
    rw [h, hlt (M - d) (by omega), zero_mul]
  have h2 : (decompose 𝒜 (y - y * b) M : R) = decompose 𝒜 y M := by
    rw [decompose_sub, DirectSum.sub_apply, AddSubgroup.coe_sub, hmM, sub_zero]
  have hMj : M = j := by
    by_contra h
    have h' := hzero _ h
    rw [h2] at h'
    exact (hmem M).mp hM h'
  have hMK : M ≤ K := S.min'_le K hK
  omega

theorem eq_zero_of_mul_eq_of_mem_of_pos [IsArtinianRing R] {e b c : R} {d : ℤ} (hd : 0 < d)
    (he0 : e ∈ 𝒜 0) (hne : e ≠ 0) (hb : b ∈ 𝒜 d) (hbe : b * e = b) (hce : c * e = c)
    (hbc : b * c = e) (hcb : c * b = e) : False := by
  have hee : IsIdempotentElem e := by
    calc e * e = c * (b * c) * b := by rw [← hcb, mul_assoc, mul_assoc, mul_assoc]
      _ = e := by rw [hbc, hce, hcb]
  have hI : ∀ x, x ∈ Submodule.span R {e} ↔ x * e = x := fun x =>
    mem_span_singleton_iff_mul_eq hee
  have hmem : ∀ x : Submodule.span R {e}, (x : R) * (e - b) ∈ Submodule.span R {e} := fun x =>
    (hI _).mpr (by rw [mul_assoc, sub_mul, hee.eq, hbe])
  let f : Submodule.span R {e} →ₗ[R] Submodule.span R {e} :=
    { toFun := fun x => ⟨x * (e - b), hmem x⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r x => Subtype.ext (mul_assoc _ _ _) }
  have hsub : ∀ x : Submodule.span R {e}, (x : R) * (e - b) = x - x * b := fun x => by
    rw [mul_sub, (hI _).mp x.2]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (x : R) - x * b = 0 := by
      rw [← hsub]
      exact congrArg Subtype.val hx
    exact Subtype.ext (eq_zero_of_sub_mul_mem 𝒜 hd he0 hb hbc ((hI _).mp x.2)
      (j := 0) (by rw [hx']; exact zero_mem _))
  obtain ⟨y, hy⟩ := IsArtinian.surjective_of_injective_endomorphism f hinj
    ⟨e, Submodule.mem_span_singleton_self e⟩
  have hy' : (y : R) - y * b = e := by
    rw [← hsub]
    exact congrArg Subtype.val hy
  have hy0 : (y : R) = 0 :=
    eq_zero_of_sub_mul_mem 𝒜 hd he0 hb hbc ((hI _).mp y.2) (hy' ▸ he0)
  exact hne (by rw [← hy', hy0, zero_mul, sub_zero])

/-- **A graded module `R e` over an Artinian graded ring is not isomorphic to a nonzero shift of
itself**: if `e ≠ 0` has degree `0` and `b ∈ R_d`, `c ∈ R_{-d}` satisfy `b e = b`, `c e = c`,
`b c = e = c b`, then `d = 0`. -/
theorem eq_zero_of_mul_eq_of_mem [IsArtinianRing R] {e b c : R} {d : ℤ} (he0 : e ∈ 𝒜 0)
    (hne : e ≠ 0) (hb : b ∈ 𝒜 d) (hc : c ∈ 𝒜 (-d)) (hbe : b * e = b) (hce : c * e = c)
    (hbc : b * c = e) (hcb : c * b = e) : d = 0 := by
  rcases lt_trichotomy d 0 with h | h | h
  · exact (eq_zero_of_mul_eq_of_mem_of_pos 𝒜 (neg_pos.mpr h) he0 hne hc hce hbe hcb hbc).elim
  · exact h
  · exact (eq_zero_of_mul_eq_of_mem_of_pos 𝒜 h he0 hne hb hbe hce hbc hcb).elim

end Graded

/-! ### Bases over `ℤ[q, q⁻¹]` from bases over `ℤ` -/

section Laurent

variable {M : Type*} [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] {κ : Type*}
  (b : Module.Basis (κ × ℤ) ℤ M)
  (hb : ∀ a n, (LaurentPolynomial.T n : LaurentPolynomial ℤ) • b (a, 0) = b (a, n))
include hb

theorem bijective_linearCombination_of_shift :
    Function.Bijective (Finsupp.linearCombination (LaurentPolynomial ℤ) fun a => b (a, 0)) := by
  let B := Finsupp.basis fun _ : κ => AddMonoidAlgebra.basis ℤ ℤ
  let e := B.equiv b (Equiv.sigmaEquivProd κ ℤ)
  suffices h : ∀ x, Finsupp.linearCombination (LaurentPolynomial ℤ) (fun a => b (a, 0)) x = e x by
    have : (Finsupp.linearCombination (LaurentPolynomial ℤ) fun a => b (a, 0) :
        (κ →₀ LaurentPolynomial ℤ) → M) = e := funext h
    rw [this]
    exact e.bijective
  intro x
  have hx : x ∈ Submodule.span ℤ (Set.range B) := B.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨a, n⟩, rfl⟩ := hy
    rw [Module.Basis.equiv_apply]
    simp only [B, Finsupp.coe_basis, AddMonoidAlgebra.basis_apply, Finsupp.linearCombination_single,
      Equiv.sigmaEquivProd_apply]
    exact hb a n
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul n x _ hx =>
    rw [map_smul e, ← hx]
    exact map_zsmul _ n x

/-- A `ℤ`-basis `(b (a, n))` of a `ℤ[q, q⁻¹]`-module with `qⁿ • b (a, 0) = b (a, n)` gives the
`ℤ[q, q⁻¹]`-basis `(b (a, 0))`. -/
def laurentBasisOfShift : Module.Basis κ (LaurentPolynomial ℤ) M :=
  Finsupp.basisSingleOne.map (LinearEquiv.ofBijective _
    (bijective_linearCombination_of_shift b hb))

@[simp]
theorem laurentBasisOfShift_apply (a : κ) : laurentBasisOfShift b hb a = b (a, 0) := by
  rw [laurentBasisOfShift, Module.Basis.map_apply, Finsupp.coe_basisSingleOne,
    LinearEquiv.ofBijective_apply, Finsupp.linearCombination_single, one_smul]

end Laurent

/-! ### Graded simple idempotents and graded ring isomorphisms -/

section GradedRingEquiv

variable {R S : Type*} [Ring R] [Ring S] {𝒜 : ℤ → AddSubgroup R} {𝒮 : ℤ → AddSubgroup S}
  (φ : R ≃+* S) (hφ : ∀ i x, φ x ∈ 𝒮 i ↔ x ∈ 𝒜 i)
include hφ

theorem isGradedSimpleIdempotent_ringEquiv_iff {e : R} :
    IsGradedSimpleIdempotent 𝒮 (φ e) ↔ IsGradedSimpleIdempotent 𝒜 e := by
  refine ⟨fun h => ?_, isGradedSimpleIdempotent_ringEquiv φ hφ⟩
  have hφ' : ∀ i y, φ.symm y ∈ 𝒜 i ↔ y ∈ 𝒮 i := fun i y => by
    rw [← hφ, RingEquiv.apply_symm_apply]
  simpa using isGradedSimpleIdempotent_ringEquiv φ.symm hφ' h

end GradedRingEquiv

/-! ### Dg functors preserve equivalence of idempotents -/

theorem DGCategory.Idempotent.Equiv.map {C : Type*} [Category C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] {D : Type*} [Category D] [Preadditive D]
    [∀ X Y : D, DGAddCommGroup (X ⟶ Y)] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor] {X Y : C}
    {e : DGCategory.Idempotent X} {f : DGCategory.Idempotent Y} (h : e.Equiv f) :
    (e.map F).Equiv (f.map F) := by
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨F.map b, F.map c, F.map_mem_grading hb, F.map_mem_grading hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [DGCategory.Idempotent.map_val, ← F.map_comp, h1, h2, h3, h4, h5, h6]

/-! ### Equivalent idempotents of `C_A` -/

namespace WeightCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A]

open DGCategory

omit [DGRing A] in
/-- Equivalence of idempotents of `C_A` only depends on the underlying elements of `A^{0,0}` and
on the difference of the objects. -/
theorem equiv_congr {k l k' l' : WeightCategory A} {e : Idempotent k} {f : Idempotent l}
    {e' : Idempotent k'} {f' : Idempotent l'} (he : e'.val.1 = e.val.1)
    (hf : f'.val.1 = f.val.1) (hkl : k'.as - l'.as = k.as - l.as) (h : e.Equiv f) :
    e'.Equiv f' := by
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨homMk b.1 (mem_wgrading_of_eq hkl.symm b.2),
    homMk c.1 (mem_wgrading_of_eq (by omega) c.2), hb, hc, hom_ext ?_, hom_ext ?_, hom_ext ?_,
    hom_ext ?_, hom_ext ?_, hom_ext ?_⟩
  · simpa [hf] using val_congr h1
  · simpa [he] using val_congr h2
  · simpa [he] using val_congr h3
  · simpa [hf] using val_congr h4
  · simpa [hf] using val_congr h5
  · simpa [he] using val_congr h6

/-- **No cell of `C_A` is equivalent to a nonzero shift of itself** when `A⁰` is Artinian (e.g.
semisimple): if `e · C_A(k, -)` and `e · C_A(l, -)` are equivalent for a nonzero idempotent
`e ∈ A^{0,0}`, then `k = l`. -/
theorem eq_of_equiv [IsArtinianRing (degreeZeroSubring A)] {k l : WeightCategory A}
    {e : Idempotent k} {e' : Idempotent l} (he : e'.val.1 = e.val.1) (hne : e.val ≠ 0)
    (h : e.Equiv e') : k = l := by
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := h
  have hd := eq_zero_of_mul_eq_of_mem (degreeZeroWGrading A) (e := idempotentToZero e)
    (b := ⟨b.1, hb⟩) (c := ⟨c.1, hc⟩) (d := k.as - l.as) (idempotentToZero_mem e)
    (fun h0 => hne (hom_ext (show e.val.1 = 0 from congrArg Subtype.val h0))) b.2
    (mem_wgrading_of_eq (by ring) c.2)
    (Subtype.ext (by simpa [he] using val_congr h1)) (Subtype.ext (by simpa using val_congr h3))
    (Subtype.ext (by simpa using val_congr h6)) (Subtype.ext (by simpa [he] using val_congr h5))
  exact WeightCategory.ext (by omega)

/-- Idempotents `e`, `f ∈ A^{0,0}` (degree-`0` idempotents of the object `0` of `C_A`) are
*equivalent up to shift* if `e · C_A(0, -)` is equivalent to `f · C_A(l, -)` for some `l`, i.e.
the graded `A⁰`-modules `A⁰ e` and `A⁰ f` are isomorphic up to a shift of weights
(`DG.WeightCategory.shiftEquiv_iff`). -/
def ShiftEquiv (e f : Idempotent (⟨0⟩ : WeightCategory A)) : Prop :=
  ∃ l : WeightCategory A, e.Equiv (idempotentAt f l)

omit [DGRing A] in
/-- `e` and `f` are equivalent up to shift iff there are `b ∈ e A^{0,d} f`, `c ∈ f A^{0,-d} e`
with `b c = e` and `c b = f`: right multiplication by `b` is then an isomorphism of graded
`A⁰`-modules `A⁰ e ≅ A⁰ f` shifting the weights by `d`. -/
theorem shiftEquiv_iff {e f : Idempotent (⟨0⟩ : WeightCategory A)} :
    ShiftEquiv e f ↔ ∃ (d : ℤ) (b c : A), b ∈ grading 0 ∧ b ∈ wgrading d ∧ c ∈ grading 0 ∧
      c ∈ wgrading (-d) ∧ e.val.1 * b = b ∧ b * f.val.1 = b ∧ f.val.1 * c = c ∧
      c * e.val.1 = c ∧ b * c = e.val.1 ∧ c * b = f.val.1 := by
  constructor
  · rintro ⟨l, b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩
    refine ⟨-l.as, b.1, c.1, hb, mem_wgrading_of_eq (by simp) b.2, hc,
      mem_wgrading_of_eq (by simp) c.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using val_congr h2
    · simpa using val_congr h1
    · simpa using val_congr h4
    · simpa using val_congr h3
    · simpa using val_congr h6
    · simpa using val_congr h5
  · rintro ⟨d, b, c, hb, hbw, hc, hcw, h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨-d⟩, homMk (k := ⟨-d⟩) (l := ⟨0⟩) b (mem_wgrading_of_eq (by simp) hbw),
      homMk (k := ⟨0⟩) (l := ⟨-d⟩) c (mem_wgrading_of_eq (by simp) hcw), hb, hc, hom_ext ?_,
      hom_ext ?_, hom_ext ?_, hom_ext ?_, hom_ext ?_, hom_ext ?_⟩
    · simpa using h2
    · simpa using h1
    · simpa using h4
    · simpa using h3
    · simpa using h6
    · simpa using h5

end WeightCategory

/-! ### Freeness of `K₀(C_A)` over `ℤ[q, q⁻¹]` -/

namespace IsGradedPositive

open CatModule CatModule.DerivedCategory DGCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A] (hA : IsGradedPositive A)

theorem idempotentToZero_map_projFunctor {k : WeightCategory A} (e : Idempotent k) :
    WeightCategory.idempotentToZero (e.map hA.projFunctor) =
      hA.degreeZeroRingEquiv (WeightCategory.idempotentToZero e) :=
  Subtype.ext (Subtype.ext (hA.projZero_apply_of_mem_zero e.mem_grading))

theorem isSimple_map_projFunctor_iff {k : WeightCategory A} (e : Idempotent k) :
    (e.map hA.projFunctor).IsSimple ↔ e.IsSimple := by
  rw [WeightCategory.idempotent_isSimple_iff, WeightCategory.idempotent_isSimple_iff,
    idempotentToZero_map_projFunctor]
  exact isGradedSimpleIdempotent_ringEquiv_iff hA.degreeZeroRingEquiv fun _ _ => Iff.rfl

theorem isSimple_map_inclFunctor_iff {k : WeightCategory hA.degreeZeroDGSubring}
    (e : Idempotent k) : (e.map hA.inclFunctor).IsSimple ↔ e.IsSimple := by
  rw [← hA.isSimple_map_projFunctor_iff, hA.map_inclFunctor_map_projFunctor]

/-- The Hom complexes of `C_{A⁰}` are concentrated in degree `0`. -/
theorem eq_zero_of_mem_grading_weightCategory {X Y : WeightCategory hA.degreeZeroDGSubring}
    {n : ℤ} (hn : 0 < n) {f : X ⟶ Y} (hf : f ∈ grading n) : f = 0 :=
  WeightCategory.hom_ext (hA.eq_zero_of_mem_grading_degreeZeroDGSubring (by omega) hf)

variable {κ : Type*} (s : κ → {e : Idempotent (⟨0⟩ : WeightCategory A) // e.IsSimple})

/-- The simple corner `e · C_{A⁰}(-n, -)` of `C_{A⁰}` attached to `(a, n)`, for `e = s a`. -/
def shiftCorner (p : κ × ℤ) : SimpleCorner (WeightCategory hA.degreeZeroDGSubring) :=
  ⟨⟨hA.projFunctor.obj ⟨-p.2⟩,
    (WeightCategory.idempotentAt (s p.1).1 ⟨-p.2⟩).map hA.projFunctor⟩,
    (hA.isSimple_map_projFunctor_iff _).mpr (WeightCategory.isSimple_idempotentAt (s p.1).2 _)⟩

variable [IsArtinianRing (degreeZeroSubring A)]
  (hs : ∀ a b, WeightCategory.ShiftEquiv (s a).1 (s b).1 → a = b)
  (hs' : ∀ e : {e : Idempotent (⟨0⟩ : WeightCategory A) // e.IsSimple},
    ∃ a, WeightCategory.ShiftEquiv e.1 (s a).1)
include hs

theorem shiftCorner_injective (p q : κ × ℤ)
    (h : (hA.shiftCorner s p).1.2.Equiv (hA.shiftCorner s q).1.2) : p = q := by
  obtain ⟨a, n⟩ := p
  obtain ⟨b, m⟩ := q
  have h' : (WeightCategory.idempotentAt (s a).1 ⟨-n⟩).Equiv
      (WeightCategory.idempotentAt (s b).1 ⟨-m⟩) := by
    refine WeightCategory.equiv_congr ?_ ?_ rfl (h.map hA.inclFunctor)
    · exact (hA.projZero_apply_of_mem_zero (s a).1.mem_grading).symm
    · exact (hA.projZero_apply_of_mem_zero (s b).1.mem_grading).symm
  have hab : a = b := by
    refine hs _ _ ⟨⟨n - m⟩, ?_⟩
    refine WeightCategory.equiv_congr ?_ ?_ ?_ h'
    · rfl
    · rfl
    · change (0 : ℤ) - (n - m) = -n - -m
      ring
  subst hab
  have hnm : (⟨-n⟩ : WeightCategory A) = ⟨-m⟩ :=
    WeightCategory.eq_of_equiv (e' := WeightCategory.idempotentAt (s a).1 ⟨-m⟩) rfl
      (WeightCategory.isSimple_idempotentAt (s a).2 ⟨-n⟩).1 h'
  have : n = m := by
    have := congrArg WeightCategory.as hnm
    change -n = -m at this
    omega
  rw [this]

include hs'

omit [IsArtinianRing (degreeZeroSubring A)] hs in
theorem exists_equiv_shiftCorner (c : SimpleCorner (WeightCategory hA.degreeZeroDGSubring)) :
    ∃ p, c.1.2.Equiv (hA.shiftCorner s p).1.2 := by
  obtain ⟨⟨X, e⟩, he⟩ := c
  have he' : (e.map hA.inclFunctor).IsSimple := (hA.isSimple_map_inclFunctor_iff e).mpr he
  obtain ⟨a, l, hl⟩ := hs' ⟨WeightCategory.idempotentAt (e.map hA.inclFunctor) ⟨0⟩,
    WeightCategory.isSimple_idempotentAt he' _⟩
  have h1 : (e.map hA.inclFunctor).Equiv
      (WeightCategory.idempotentAt (s a).1 ⟨l.as + X.as⟩) := by
    refine WeightCategory.equiv_congr ?_ ?_ ?_ hl
    · rfl
    · rfl
    · change X.as - (l.as + X.as) = 0 - l.as
      ring
  refine ⟨(a, -(l.as + X.as)), ?_⟩
  refine WeightCategory.equiv_congr ?_ ?_ ?_ (h1.map hA.projFunctor)
  · exact (Subtype.ext (hA.projZero_apply_of_mem_zero e.val.1.2)).symm
  · rfl
  · change X.as - -(-(l.as + X.as)) = X.as - (l.as + X.as)
    ring

variable
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory hA.degreeZeroDGSubring)]

/-- The `ℤ`-basis of `K₀(C_{A⁰})` given by the cells `e · C_{A⁰}(-n, -)`. -/
def zBasisDegreeZero :
    Module.Basis (κ × ℤ) ℤ
      (DGCategory.K0.{max u w, max u w} (WeightCategory hA.degreeZeroDGSubring)) :=
  hA.isGradedPositive_degreeZeroDGSubring.isPositive_weightCategory.basisOfConcentrated.{max u w}
    (fun hn _ hf => hA.eq_zero_of_mem_grading_weightCategory hn hf) (hA.shiftCorner s)
    (hA.shiftCorner_injective s hs) (hA.exists_equiv_shiftCorner s hs')

theorem zBasisDegreeZero_apply (p : κ × ℤ) :
    hA.zBasisDegreeZero s hs hs' p = DGCategory.K0.cell.{max u w} (hA.shiftCorner s p).1.2 0 :=
  DGCategory.IsPositive.basisOfConcentrated_apply.{max u w}
    hA.isGradedPositive_degreeZeroDGSubring.isPositive_weightCategory
    (fun hn _ hf => hA.eq_zero_of_mem_grading_weightCategory hn hf) (hA.shiftCorner s)
    (hA.shiftCorner_injective s hs) (hA.exists_equiv_shiftCorner s hs') p

variable [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]

/-- The `ℤ`-basis of `K₀(C_A)` given by the cells `e · C_A(-n, -)` (the bigraded modules
`(A e)⟨n⟩`), `e` running over a set of representatives of the graded simple idempotents up to
shift and `n ∈ ℤ`. -/
def zBasis : Module.Basis (κ × ℤ) ℤ (DGCategory.K0.{max u w, max u w} (WeightCategory A)) :=
  (hA.zBasisDegreeZero s hs hs').map hA.K0DegreeZeroEquiv.symm.toAddEquiv.toIntLinearEquiv

theorem zBasis_apply (p : κ × ℤ) :
    hA.zBasis s hs hs' p =
      DGCategory.K0.cell.{max u w} (WeightCategory.idempotentAt (s p.1).1 ⟨-p.2⟩) 0 := by
  rw [zBasis, Module.Basis.map_apply]
  refine (congrArg hA.K0DegreeZeroEquiv.symm (hA.zBasisDegreeZero_apply s hs hs' p)).trans ?_
  rw [K0DegreeZeroEquiv_symm_cell]
  exact congrArg (fun e => DGCategory.K0.cell.{max u w} e 0)
    (hA.map_projFunctor_map_inclFunctor (WeightCategory.idempotentAt (s p.1).1 ⟨-p.2⟩))

omit hs hs' [IsArtinianRing (degreeZeroSubring A)] in
theorem T_smul_cell_idempotentAt (e : Idempotent (⟨0⟩ : WeightCategory A)) (n : ℤ) :
    (LaurentPolynomial.T n : LaurentPolynomial ℤ) •
        DGCategory.K0.cell.{max u w} (WeightCategory.idempotentAt e ⟨-0⟩) 0 =
      DGCategory.K0.cell.{max u w} (WeightCategory.idempotentAt e ⟨-n⟩) 0 :=
  WeightCategory.T_smul_cell n _ _ (by simp) rfl

/-- **`K₀(C_A)` is free over `ℤ[q, q⁻¹]`** (Roadmap 7.2 (b)) for a graded positive bigraded dg
ring `A` with `A⁰` Artinian (e.g. semisimple, `DG.IsPositive.laurentBasis`): if `s` is a family
of graded simple idempotents `e ∈ A^{0,0}` containing exactly one representative of each class
up to equivalence up to shift (`DG.WeightCategory.ShiftEquiv`, i.e. of the graded simple
`A⁰`-modules `A⁰ e` up to isomorphism and shift), the classes `[e · C_A(0, -)]` (the bigraded
modules `A e`) form a basis of `K₀(C_A)`. -/
def laurentBasis :
    Module.Basis κ (LaurentPolynomial ℤ) (DGCategory.K0.{max u w, max u w} (WeightCategory A)) :=
  laurentBasisOfShift (hA.zBasis s hs hs') fun a n => by
    rw [zBasis_apply, zBasis_apply]
    exact T_smul_cell_idempotentAt (s a).1 n

theorem laurentBasis_apply (a : κ) :
    hA.laurentBasis s hs hs' a = DGCategory.K0.cell.{max u w} (s a).1 0 := by
  rw [laurentBasis, laurentBasisOfShift_apply, zBasis_apply]
  have h := WeightCategory.T_smul_cell.{max u w} 0 (s a).1
    (WeightCategory.idempotentAt (s a).1 ⟨-0⟩) (by simp) rfl
  rw [LaurentPolynomial.T_zero, one_smul] at h
  exact h.symm

end IsGradedPositive

/-! ### Positive bigraded dg rings -/

namespace IsPositive

open CatModule DGCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A] (hA : IsPositive A)

include hA in
omit [InternalGrading A] [BigradedDGRing A] in
/-- For a positive dg ring, `A⁰` is semisimple, hence Artinian. -/
theorem isArtinianRing_degreeZeroSubring : IsArtinianRing (degreeZeroSubring A) := by
  have := hA.isSemisimple
  infer_instance

variable {κ : Type*} (s : κ → {e : Idempotent (⟨0⟩ : WeightCategory A) // e.IsSimple})
  (hs : ∀ a b, WeightCategory.ShiftEquiv (s a).1 (s b).1 → a = b)
  (hs' : ∀ e : {e : Idempotent (⟨0⟩ : WeightCategory A) // e.IsSimple},
    ∃ a, WeightCategory.ShiftEquiv e.1 (s a).1)
  [CatModule.HasDerivedCategory.{max u w, max u w}
    (WeightCategory hA.isGradedPositive.degreeZeroDGSubring)]
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]

/-- **`K₀(C_A)` is free over `ℤ[q, q⁻¹]` for a positive bigraded dg ring** (Roadmap 7.2 (b),
`A⁰` semisimple as a ring): the classes `[e · C_A(0, -)]` (the bigraded modules `A e`) of a set
`s` of representatives of the graded simple idempotents `e ∈ A^{0,0}` up to equivalence up to
shift (i.e. of the graded simple `A⁰`-modules up to isomorphism and shift) form a basis. -/
def laurentBasis :
    Module.Basis κ (LaurentPolynomial ℤ) (DGCategory.K0.{max u w, max u w} (WeightCategory A)) :=
  haveI := hA.isArtinianRing_degreeZeroSubring
  hA.isGradedPositive.laurentBasis s hs hs'

theorem laurentBasis_apply (a : κ) :
    hA.laurentBasis s hs hs' a = DGCategory.K0.cell.{max u w} (s a).1 0 :=
  haveI := hA.isArtinianRing_degreeZeroSubring
  hA.isGradedPositive.laurentBasis_apply s hs hs' a

end IsPositive

/-! ### `A⁰` a division ring: `K₀(C_A) ≅ ℤ[q, q⁻¹]` -/

section DivisionRing

variable {R : Type*} [Ring R] (𝒜 : ℤ → AddSubgroup R) [GradedRing 𝒜]

/-- In a graded ring in which every nonzero element is a unit, `1` is a graded simple
idempotent. -/
theorem isGradedSimpleIdempotent_one [Nontrivial R] (hdiv : ∀ a : R, a ≠ 0 → IsUnit a) :
    IsGradedSimpleIdempotent 𝒜 1 := by
  refine ⟨one_ne_zero, fun j h hh _ hh0 => ?_⟩
  obtain ⟨u, rfl⟩ := hdiv h hh0
  refine ⟨decompose 𝒜 (↑u⁻¹ : R) (-j), SetLike.coe_mem _, ?_⟩
  have h1 := coe_decompose_mul_add_of_right_mem 𝒜 (a := (↑u⁻¹ : R)) (i := -j) hh
  rw [Units.inv_mul, neg_add_cancel, decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem] at h1
  exact h1.symm

end DivisionRing

namespace IsPositive

open CatModule DGCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A] (hA : IsPositive A)
  (hdiv : ∀ a : degreeZeroSubring A, a ≠ 0 → IsUnit a)
include hdiv

/-- If `A⁰` is a division ring, every simple idempotent of `C_A` is the identity. -/
theorem weight_val_eq_one_of_isSimple {k : WeightCategory A} {e : Idempotent k}
    (he : e.IsSimple) : e.val.1 = 1 := by
  have hne : WeightCategory.idempotentToZero e ≠ 0 := fun h =>
    he.1 (WeightCategory.hom_ext (show e.val.1 = 0 from congrArg Subtype.val h))
  have h : WeightCategory.idempotentToZero e * WeightCategory.idempotentToZero e =
      WeightCategory.idempotentToZero e * 1 := by
    rw [mul_one, (WeightCategory.isIdempotentElem_idempotentToZero e).eq]
  exact congrArg Subtype.val ((hdiv _ hne).mul_left_cancel h)

variable [Nontrivial A]

/-- If `A⁰` is a division ring, the identity of `0` is a simple idempotent of `C_A`. -/
theorem isSimple_id : (Idempotent.id (⟨0⟩ : WeightCategory A)).IsSimple := by
  rw [WeightCategory.idempotent_isSimple_iff]
  have h1 : WeightCategory.idempotentToZero (Idempotent.id (⟨0⟩ : WeightCategory A)) = 1 := rfl
  rw [h1]
  exact isGradedSimpleIdempotent_one _ hdiv

omit [Nontrivial A] in
theorem shiftEquiv_id (e : {e : Idempotent (⟨0⟩ : WeightCategory A) // e.IsSimple}) :
    WeightCategory.ShiftEquiv e.1 (Idempotent.id (⟨0⟩ : WeightCategory A)) := by
  refine ⟨⟨0⟩, WeightCategory.equiv_congr ?_ ?_ ?_ (Idempotent.Equiv.refl e.1)⟩
  · rfl
  · exact (weight_val_eq_one_of_isSimple hdiv e.2).symm
  · rfl

variable [CatModule.HasDerivedCategory.{max u w, max u w}
    (WeightCategory hA.isGradedPositive.degreeZeroDGSubring)]
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]

/-- If `A⁰` is a division ring, `K₀(C_A)` is free over `ℤ[q, q⁻¹]` on the single class
`[A] = [C_A(0, -)]`. -/
def laurentBasisOfDivisionRing :
    Module.Basis Unit (LaurentPolynomial ℤ)
      (DGCategory.K0.{max u w, max u w} (WeightCategory A)) :=
  hA.laurentBasis (fun _ => ⟨_, isSimple_id hdiv⟩) (fun _ _ _ => rfl)
    fun e => ⟨(), shiftEquiv_id hdiv e⟩

theorem laurentBasisOfDivisionRing_apply (a : Unit) :
    hA.laurentBasisOfDivisionRing hdiv a =
      DGCategory.K0.cell.{max u w} (Idempotent.id (⟨0⟩ : WeightCategory A)) 0 :=
  hA.laurentBasis_apply _ _ _ a

/-- **`K₀(C_A) ≅ ℤ[q, q⁻¹]` when `A⁰` is a division ring** (Roadmap 7.2 (b)), e.g. `A⁰ = k` a
field: an isomorphism of `ℤ[q, q⁻¹]`-modules with `[A] ↦ 1`, hence `[A⟨n⟩] = qⁿ [A] ↦ qⁿ`
(`DG.IsPositive.K0EquivLaurentOfDivisionRing_T_smul`). -/
def K0EquivLaurentOfDivisionRing :
    DGCategory.K0.{max u w, max u w} (WeightCategory A) ≃ₗ[LaurentPolynomial ℤ]
      LaurentPolynomial ℤ :=
  (hA.laurentBasisOfDivisionRing hdiv).equivFun.trans
    (LinearEquiv.funUnique Unit (LaurentPolynomial ℤ) (LaurentPolynomial ℤ))

theorem K0EquivLaurentOfDivisionRing_cell :
    hA.K0EquivLaurentOfDivisionRing hdiv
      (DGCategory.K0.cell.{max u w} (Idempotent.id (⟨0⟩ : WeightCategory A)) 0) = 1 := by
  rw [← hA.laurentBasisOfDivisionRing_apply hdiv (), K0EquivLaurentOfDivisionRing,
    LinearEquiv.trans_apply, LinearEquiv.funUnique_apply, Function.eval,
    Module.Basis.equivFun_self]
  rfl

/-- `[A⟨n⟩] = qⁿ [A] ↦ qⁿ`. -/
theorem K0EquivLaurentOfDivisionRing_T_smul (n : ℤ) :
    hA.K0EquivLaurentOfDivisionRing hdiv ((LaurentPolynomial.T n : LaurentPolynomial ℤ) •
      DGCategory.K0.cell.{max u w} (Idempotent.id (⟨0⟩ : WeightCategory A)) 0) =
      LaurentPolynomial.T n := by
  rw [map_smul, K0EquivLaurentOfDivisionRing_cell, smul_eq_mul, mul_one]

end IsPositive

namespace IsPositive

open CatModule DGCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [InternalGrading A]
  [BigradedDGRing A] (hA : IsPositive A) (k : Type*) [Field k] [Algebra k A] [DGAlgebra k A]
  (hk : ∀ a ∈ grading (M := A) 0, ∃ c : k, algebraMap k A c = a) [Nontrivial A]
  [CatModule.HasDerivedCategory.{max u w, max u w}
    (WeightCategory hA.isGradedPositive.degreeZeroDGSubring)]
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory A)]

/-- **`K₀(C_A) ≅ ℤ[q, q⁻¹]` for a positive bigraded dg algebra with `A⁰ = k`** a field
(Roadmap 7.2 (b)); for instance `A = k` in bidegree `(0, 0)`. The isomorphism of
`ℤ[q, q⁻¹]`-modules sends `[A⟨n⟩]` to `qⁿ`. -/
def K0EquivLaurentOfField :
    DGCategory.K0.{max u w, max u w} (WeightCategory A) ≃ₗ[LaurentPolynomial ℤ]
      LaurentPolynomial ℤ :=
  hA.K0EquivLaurentOfDivisionRing (isUnit_of_forall_eq_algebraMap k hk)

theorem K0EquivLaurentOfField_T_smul (n : ℤ) :
    hA.K0EquivLaurentOfField k hk ((LaurentPolynomial.T n : LaurentPolynomial ℤ) •
      DGCategory.K0.cell.{max u w} (Idempotent.id (⟨0⟩ : WeightCategory A)) 0) =
      LaurentPolynomial.T n :=
  hA.K0EquivLaurentOfDivisionRing_T_smul _ n

end IsPositive

end DG

end
