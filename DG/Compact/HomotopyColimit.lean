import DG.Compact.Triangulated
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Homotopy colimits of sequences in a pretriangulated category

Let `C` be a pretriangulated category, `X : ℕ → C` a sequence of objects and
`f n : X n ⟶ X (n + 1)` morphisms, and assume that the coproduct `∐ X` exists. The
*homotopy colimit* of the sequence (M. Bökstedt and A. Neeman, *Homotopy limits in
triangulated categories*, Compositio Math. 86 (1993); see also A. Neeman, *Triangulated
categories*, Ann. Math. Studies 148, §1.6, and [Stacks, Section 13.33]) is the third object of a
distinguished triangle

  `∐ X ⟶ ∐ X ⟶ hocolim X f ⟶ (∐ X)⟦1⟧`,

whose first morphism is `1 - shift`, where `shift : ∐ X ⟶ ∐ X` restricts to
`f n ≫ Sigma.ι X (n + 1)` on the summand `X n` (`DG.hocolimShift`, `DG.hocolimDiff`). The
triangle is chosen with `distinguished_cocone_triangle`, so `DG.hocolim X f` is well defined
up to non-unique isomorphism. It comes with morphisms `DG.hocolimι X f n : X n ⟶ hocolim X f`
compatible with the `f n` (`DG.f_comp_hocolimι`), and it is a weak colimit: every compatible
family of morphisms `X n ⟶ Y` extends (non-uniquely) to `hocolim X f ⟶ Y`
(`DG.hocolim_exists_desc`).

## Main results

For an object `K` which is compact with respect to countable coproducts (`DG.IsCompact.{0} K`,
coproducts indexed by `Type`), the functor `Hom(K, -)` takes the homotopy colimit to the
colimit of abelian groups `colim_n Hom(K, X n)` ([Stacks, Lemma 13.33.9, Tag 094A]); that is,
the canonical map `colim_n Hom(K, X n) ⟶ Hom(K, hocolim X f)` is surjective and injective:

* `DG.hocolim_exists_factor`: every morphism `K ⟶ hocolim X f` factors through `hocolimι X f n`
  for some `n`;
* `DG.hocolim_exists_eq_of_comp_eq`: if `u v : K ⟶ X n` agree after composition with
  `hocolimι X f n`, they agree after composition with the transition map `X n ⟶ X m` for some
  `m ≥ n`.

The proof: by compactness, `Hom(K, ∐ X) = ⨁ₙ Hom(K, X n)`, and on this direct sum `1 - shift`
becomes `(aₙ)ₙ ↦ (aₙ - aₙ₋₁ ≫ fₙ₋₁)ₙ` (`DG.directSumShift`), which is injective with the
colimit as cokernel. The long exact sequence of `Hom(K, -)` for the defining triangle (and for
its shift, using that `⟦1⟧` commutes with coproducts) then gives the two statements.

The transition maps `X n ⟶ X m` are `(Functor.ofSequence f).map (homOfLE h)`.
-/

universe v u

namespace DG

open CategoryTheory Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Shift

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X]

/-- The morphism `shift : ∐ X ⟶ ∐ X` whose restriction to `X n` is `f n ≫ Sigma.ι X (n + 1)`. -/
noncomputable def hocolimShift : ∐ X ⟶ ∐ X :=
  Sigma.desc fun n => f n ≫ Sigma.ι X (n + 1)

/-- The morphism `1 - shift : ∐ X ⟶ ∐ X` whose cone is the homotopy colimit. -/
noncomputable def hocolimDiff : ∐ X ⟶ ∐ X :=
  𝟙 _ - hocolimShift X f

omit [Preadditive C] in
@[reassoc (attr := simp)]
theorem ι_hocolimShift (n : ℕ) :
    Sigma.ι X n ≫ hocolimShift X f = f n ≫ Sigma.ι X (n + 1) :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
theorem ι_hocolimDiff (n : ℕ) :
    Sigma.ι X n ≫ hocolimDiff X f = Sigma.ι X n - f n ≫ Sigma.ι X (n + 1) := by
  simp [hocolimDiff, Preadditive.comp_sub]

end Shift

section DirectSum

variable {K : C} {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1))

/-- The shift on `⨁ n, (K ⟶ X n)`, sending `a ∈ (K ⟶ X n)` to `a ≫ f n ∈ (K ⟶ X (n + 1))`.
Under the comparison with `K ⟶ ∐ X` it corresponds to composition with `hocolimShift X f`. -/
noncomputable def directSumShift :
    (DirectSum ℕ fun n => (K ⟶ X n)) →+ DirectSum ℕ fun n => (K ⟶ X n) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun n => (K ⟶ X n)) (n + 1)).comp (Preadditive.rightComp K (f n))

@[simp]
theorem directSumShift_of (n : ℕ) (a : K ⟶ X n) :
    directSumShift f (DirectSum.of _ n a) = DirectSum.of (fun n => (K ⟶ X n)) (n + 1) (a ≫ f n) :=
  DirectSum.toAddMonoid_of _ _ _

theorem directSumShift_apply_zero (a : DirectSum ℕ fun n => (K ⟶ X n)) :
    directSumShift f a 0 = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n x => simp [DirectSum.of_apply]
  | add a b ha hb => simp [ha, hb]

theorem directSumShift_apply_succ (a : DirectSum ℕ fun n => (K ⟶ X n)) (n : ℕ) :
    directSumShift f a (n + 1) = a n ≫ f n := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m x =>
    rw [directSumShift_of]
    by_cases h : m = n
    · subst h; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h),
        Limits.zero_comp]
  | add a b ha hb => simp [ha, hb, Preadditive.add_comp]

/-- `1 - shift` is injective on `⨁ n, (K ⟶ X n)`. -/
theorem directSumShift_eq_self {a : DirectSum ℕ fun n => (K ⟶ X n)}
    (h : directSumShift f a = a) : a = 0 := by
  have key : ∀ n, a n = 0 := by
    intro n
    induction n with
    | zero => rw [← h, directSumShift_apply_zero]
    | succ n ih => rw [← h, directSumShift_apply_succ, ih, Limits.zero_comp]
  ext n
  simp [key n]

/-- If `a - shift a` is concentrated in degree `n` with value `w`, then `a` is concentrated in
degrees `≥ n` and `a m = w ≫ (X n ⟶ X m)` for `m ≥ n`. -/
theorem apply_eq_of_sub_directSumShift_eq {a : DirectSum ℕ fun n => (K ⟶ X n)} {n : ℕ}
    {w : K ⟶ X n} (h : a - directSumShift f a = DirectSum.of _ n w) {m : ℕ} (hnm : n ≤ m) :
    a m = w ≫ (Functor.ofSequence f).map (homOfLE hnm) := by
  have h' : ∀ k, a k = directSumShift f a k + DirectSum.of (fun n => (K ⟶ X n)) n w k := by
    intro k
    rw [← h, DirectSum.sub_apply, add_sub_cancel]
  have below : ∀ k, k < n → a k = 0 := by
    intro k hk
    induction k with
    | zero => rw [h', directSumShift_apply_zero, DirectSum.of_eq_of_ne _ _ _ (by omega), add_zero]
    | succ k ih =>
      rw [h', directSumShift_apply_succ, ih (by omega), Limits.zero_comp, zero_add,
        DirectSum.of_eq_of_ne _ _ _ (by omega)]
  induction m, hnm using Nat.le_induction with
  | base =>
    rw [h', DirectSum.of_eq_same]
    rcases n with _ | n
    · simp [directSumShift_apply_zero]
      exact (Category.comp_id w).symm
    · simp [directSumShift_apply_succ, below n (by omega)]
      exact (Category.comp_id w).symm
  | succ m hnm ih =>
    rw [h', directSumShift_apply_succ, ih, DirectSum.of_eq_of_ne _ _ _ (by omega), add_zero,
      ← homOfLE_comp hnm (Nat.le_succ m), Functor.map_comp, Functor.ofSequence_map_homOfLE_succ]
    exact Category.assoc _ _ _

end DirectSum

section Injective

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X] {K : C}

/-- Composition with `1 - shift` corresponds, under the comparison
`⨁ n, (K ⟶ X n) → (K ⟶ ∐ X)`, to `1 - directSumShift f`. -/
theorem coproductComparison_comp_hocolimDiff (a : DirectSum ℕ fun n => (K ⟶ X n)) :
    coproductComparison K X a ≫ hocolimDiff X f =
      coproductComparison K X (a - directSumShift f a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n x => simp [Preadditive.comp_sub]
  | add a b ha hb =>
    rw [map_add, Preadditive.add_comp, ha, hb, ← map_add, map_add (directSumShift f)]
    congr 1
    abel

/-- For `K` compact, composition with `1 - shift` is injective on `K ⟶ ∐ X`. -/
theorem hocolimDiff_injective (hK : IsCompact.{0} K) :
    Function.Injective fun φ : K ⟶ ∐ X => φ ≫ hocolimDiff X f := by
  change Function.Injective (Preadditive.rightComp K (hocolimDiff X f))
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  obtain ⟨a, rfl⟩ := (hK ℕ X).2 φ
  change coproductComparison K X a ≫ hocolimDiff X f = 0 at hφ
  rw [coproductComparison_comp_hocolimDiff, ← map_zero (coproductComparison K X)] at hφ
  rw [directSumShift_eq_self f (sub_eq_zero.1 ((hK ℕ X).1 hφ)).symm, map_zero]

section ShiftFunctor

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [HasCountableCoproducts C]

/-- Composition with `(1 - shift)⟦1⟧` is injective on `K ⟶ (∐ X)⟦1⟧` for `K` compact: the
shift functor commutes with coproducts, and `(1 - shift)⟦1⟧` corresponds to `1 - shift` for the
shifted sequence. -/
theorem hocolimDiff_shift_injective (hK : IsCompact.{0} K) :
    Function.Injective fun φ : K ⟶ (∐ X)⟦(1 : ℤ)⟧ => φ ≫ (hocolimDiff X f)⟦(1 : ℤ)⟧' := by
  let X' : ℕ → C := fun n => (X n)⟦(1 : ℤ)⟧
  let f' : ∀ n, X' n ⟶ X' (n + 1) := fun n => (f n)⟦(1 : ℤ)⟧'
  let e : ∐ X' ⟶ (∐ X)⟦(1 : ℤ)⟧ := sigmaComparison (shiftFunctor C (1 : ℤ)) X
  have comm : e ≫ (hocolimDiff X f)⟦(1 : ℤ)⟧' = hocolimDiff X' f' ≫ e := by
    ext n
    simp only [e, X', f', ι_comp_sigmaComparison_assoc, ι_hocolimDiff_assoc, ← Functor.map_comp,
      ι_hocolimDiff, Functor.map_sub, Preadditive.sub_comp, Category.assoc,
      ι_comp_sigmaComparison]
  intro φ ψ h
  simp only at h
  have h' : (φ ≫ inv e) ≫ hocolimDiff X' f' = (ψ ≫ inv e) ≫ hocolimDiff X' f' := by
    rw [← cancel_mono e, Category.assoc, Category.assoc, Category.assoc, Category.assoc, ← comm,
      IsIso.inv_hom_id_assoc, h]
  simpa using hocolimDiff_injective X' f' hK h'

end ShiftFunctor

end Injective

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

section Defs

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X]

/-- The *homotopy colimit* of the sequence `X 0 ⟶ X 1 ⟶ ⋯`: a chosen cone of
`1 - shift : ∐ X ⟶ ∐ X`. -/
noncomputable def hocolim : C :=
  (distinguished_cocone_triangle (hocolimDiff X f)).choose

/-- The morphism `∐ X ⟶ hocolim X f` of the defining triangle. -/
noncomputable def hocolimπ : ∐ X ⟶ hocolim X f :=
  (distinguished_cocone_triangle (hocolimDiff X f)).choose_spec.choose

/-- The morphism `hocolim X f ⟶ (∐ X)⟦1⟧` of the defining triangle. -/
noncomputable def hocolimδ : hocolim X f ⟶ (∐ X)⟦(1 : ℤ)⟧ :=
  (distinguished_cocone_triangle (hocolimDiff X f)).choose_spec.choose_spec.choose

/-- The defining triangle `∐ X ⟶ ∐ X ⟶ hocolim X f ⟶ (∐ X)⟦1⟧` of the homotopy colimit. -/
noncomputable def hocolimTriangle : Triangle C :=
  Triangle.mk (hocolimDiff X f) (hocolimπ X f) (hocolimδ X f)

theorem hocolimTriangle_distinguished : hocolimTriangle X f ∈ distTriang C :=
  (distinguished_cocone_triangle (hocolimDiff X f)).choose_spec.choose_spec.choose_spec

@[reassoc (attr := simp)]
theorem hocolimDiff_hocolimπ : hocolimDiff X f ≫ hocolimπ X f = 0 :=
  comp_distTriang_mor_zero₁₂ _ (hocolimTriangle_distinguished X f)

/-- The canonical morphism `X n ⟶ hocolim X f`. -/
noncomputable def hocolimι (n : ℕ) : X n ⟶ hocolim X f :=
  Sigma.ι X n ≫ hocolimπ X f

/-- The morphisms `X n ⟶ hocolim X f` are compatible with the transition maps. -/
@[reassoc (attr := simp)]
theorem f_comp_hocolimι (n : ℕ) : f n ≫ hocolimι X f (n + 1) = hocolimι X f n := by
  have h := Sigma.ι X n ≫= hocolimDiff_hocolimπ X f
  rw [ι_hocolimDiff_assoc, Preadditive.sub_comp, Limits.comp_zero, sub_eq_zero] at h
  simp only [hocolimι, ← Category.assoc] at h ⊢
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The morphisms `X n ⟶ hocolim X f` are compatible with the transition maps `X n ⟶ X m`. -/
@[reassoc]
theorem map_comp_hocolimι {n m : ℕ} (h : n ≤ m) :
    (Functor.ofSequence f).map (homOfLE h) ≫ hocolimι X f m = hocolimι X f n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [← homOfLE_comp hnm (Nat.le_succ m), Functor.map_comp, Category.assoc,
      Functor.ofSequence_map_homOfLE_succ, f_comp_hocolimι, ih]

set_option backward.isDefEq.respectTransparency false in
/-- The homotopy colimit is a weak colimit: a compatible family of morphisms `X n ⟶ Y` extends
to a morphism `hocolim X f ⟶ Y`. -/
theorem hocolim_exists_desc {Y : C} (p : ∀ n, X n ⟶ Y) (hp : ∀ n, f n ≫ p (n + 1) = p n) :
    ∃ g : hocolim X f ⟶ Y, ∀ n, hocolimι X f n ≫ g = p n := by
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (hocolimTriangle_distinguished X f) (Sigma.desc p)
    (by change hocolimDiff X f ≫ Sigma.desc p = 0; ext n; simp [hp])
  refine ⟨g, fun n => ?_⟩
  simp only [hocolimTriangle, Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂] at hg
  rw [hocolimι, Category.assoc, ← hg, Sigma.ι_comp_desc]

end Defs

section Compact

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X] {K : C}

set_option backward.isDefEq.respectTransparency false in
/-- For `a ∈ ⨁ n, (K ⟶ X n)`, the composition of the corresponding morphism `K ⟶ ∐ X` with
`∐ X ⟶ hocolim X f` factors through `hocolimι X f n` for some `n`. -/
theorem exists_coproductComparison_comp_hocolimπ (a : DirectSum ℕ fun n => (K ⟶ X n)) :
    ∃ (n : ℕ) (b : K ⟶ X n), coproductComparison K X a ≫ hocolimπ X f = b ≫ hocolimι X f n := by
  induction a using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | of n x => exact ⟨n, x, by simp [hocolimι]⟩
  | add a b ha hb =>
    obtain ⟨n, x, hx⟩ := ha
    obtain ⟨m, y, hy⟩ := hb
    refine ⟨max n m, x ≫ (Functor.ofSequence f).map (homOfLE (le_max_left n m)) +
      y ≫ (Functor.ofSequence f).map (homOfLE (le_max_right n m)), ?_⟩
    rw [map_add, Preadditive.add_comp, hx, hy, Preadditive.add_comp, Category.assoc,
      Category.assoc, map_comp_hocolimι, map_comp_hocolimι]

set_option backward.isDefEq.respectTransparency false in
/-- **Compact objects see homotopy colimits as colimits, II.** For `K` compact, if two morphisms
`u v : K ⟶ X n` become equal in the homotopy colimit, they become equal in some `X m`, `m ≥ n`
([Stacks, Tag 094A]). -/
theorem hocolim_exists_eq_of_comp_eq (hK : IsCompact.{0} K) {n : ℕ} (u v : K ⟶ X n)
    (h : u ≫ hocolimι X f n = v ≫ hocolimι X f n) :
    ∃ (m : ℕ) (hnm : n ≤ m), u ≫ (Functor.ofSequence f).map (homOfLE hnm) =
      v ≫ (Functor.ofSequence f).map (homOfLE hnm) := by
  classical
  have hT := hocolimTriangle_distinguished X f
  obtain ⟨ψ, hψ⟩ := Triangle.coyoneda_exact₂ _ hT ((u - v) ≫ Sigma.ι X n) (by
    simp only [hocolimTriangle, Triangle.mk_mor₂, Category.assoc, Preadditive.sub_comp]
    rw [← hocolimι, h, sub_self])
  obtain ⟨a, rfl⟩ := (hK ℕ X).2 ψ
  simp only [hocolimTriangle, Triangle.mk_mor₁] at hψ
  rw [coproductComparison_comp_hocolimDiff, ← coproductComparison_of] at hψ
  have ha := (hK ℕ X).1 hψ.symm
  obtain ⟨N, hN⟩ : ∃ N, ∀ m, N ≤ m → a m = 0 := by
    refine ⟨(DFinsupp.support a).sup id + 1, fun m hm => ?_⟩
    by_contra hne
    have := Finset.le_sup (f := id) (DFinsupp.mem_support_iff.2 hne)
    simp only [id] at this
    omega
  refine ⟨max n N, le_max_left n N, ?_⟩
  rw [← sub_eq_zero, ← Preadditive.sub_comp, ← apply_eq_of_sub_directSumShift_eq f ha,
    hN _ (le_max_right n N)]

variable [HasCountableCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- **Compact objects see homotopy colimits as colimits, I.** For `K` compact, every morphism
`K ⟶ hocolim X f` factors through `hocolimι X f n : X n ⟶ hocolim X f` for some `n`
([Stacks, Tag 094A]). -/
theorem hocolim_exists_factor (hK : IsCompact.{0} K) (a : K ⟶ hocolim X f) :
    ∃ (n : ℕ) (b : K ⟶ X n), a = b ≫ hocolimι X f n := by
  have hT := hocolimTriangle_distinguished X f
  have h₁ : a ≫ hocolimδ X f = 0 := by
    apply hocolimDiff_shift_injective X f hK
    have := comp_distTriang_mor_zero₃₁ _ hT
    simp only [hocolimTriangle, Triangle.mk_mor₃, Triangle.mk_mor₁] at this
    simp [this]
  obtain ⟨c, hc⟩ := Triangle.coyoneda_exact₃ _ hT a h₁
  obtain ⟨α, rfl⟩ := (hK ℕ X).2 c
  obtain ⟨n, b, hb⟩ := exists_coproductComparison_comp_hocolimπ X f α
  exact ⟨n, b, hc.trans hb⟩

end Compact

end DG
