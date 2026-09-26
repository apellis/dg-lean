import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Data.Int.Interval
import DG.K0.Abelian
import DG.K0.Triangulated

/-!
# The Euler characteristic of a bounded complex

Let `C` be an abelian category and `K` a cochain complex in `C` indexed by `ℤ`, with differential
of degree `+1`. The *Euler characteristic* of `K` is the element
`χ(K) = Σₙ (-1)ⁿ [Kⁿ]` of the Grothendieck group `K₀(C)` (`DG.AbelianK0`); it is defined when
`K` is bounded (see C. A. Weibel, *The K-book*, Chapter II, §6). The fundamental fact is that it
can also be computed from cohomology: `χ(K) = Σₙ (-1)ⁿ [Hⁿ(K)]`.

We define `DG.AbelianK0.eulerChar K` as the `finsum` `∑ᶠ n, (-1)ⁿ • [Kⁿ]`, the sign being the unit
`Int.negOnePow n : ℤˣ` acting on `K₀(C)`. For a strictly bounded complex (Mathlib's
`CochainComplex.IsStrictlyGE a` and `CochainComplex.IsStrictlyLE b`, i.e. `Kⁿ = 0` for `n < a`
and for `n > b`) this is the finite sum over `a ≤ n ≤ b` (`DG.AbelianK0.eulerChar_eq_sum_Icc`).
(By the convention of `finsum`, `eulerChar K = 0` when the family `n ↦ (-1)ⁿ • [Kⁿ]` has infinite
support; all results below assume strict boundedness.)

## Main results

* `DG.AbelianK0.eulerChar_eq_finsum_homology`: `χ(K) = Σₙ (-1)ⁿ [Hⁿ(K)]` for a strictly bounded
  complex `K`, with `Hⁿ(K) = HomologicalComplex.homology K n`. The proof combines, in each degree,
  the short exact sequences `0 ⟶ Zⁿ ⟶ Kⁿ ⟶ Bⁿ⁺¹ ⟶ 0` and `0 ⟶ Bⁿ ⟶ Zⁿ ⟶ Hⁿ ⟶ 0` and telescopes.
* `DG.AbelianK0.eulerChar_eq_zero_of_exactAt`: the alternating sum of the classes in a bounded
  exact sequence is `0`.
* `DG.AbelianK0.eulerChar_X₂`: `χ` is additive along short exact sequences of bounded complexes.
* `DG.AbelianK0.eulerChar_single`: `χ(X[-n]) = (-1)ⁿ [X]` for `X` placed in degree `n`.
* `DG.AbelianK0.eulerChar_eq_of_iso`, `DG.AbelianK0.eulerChar_eq_of_quasiIso`: invariance
  under isomorphisms and under quasi-isomorphisms of bounded complexes.

## Comparison with the derived category

Assume `[HasDerivedCategory C]`. The functor sending `X` to the complex `X` concentrated in
degree `0` sends short exact sequences to distinguished triangles of the derived category
(Mathlib's `ShortComplex.ShortExact.singleTriangle_distinguished`), so it induces a homomorphism
`DG.AbelianK0.toDerived : K₀(C) →+ K₀(D(C))` to the Grothendieck group `DG.K0` of the
pretriangulated category `DerivedCategory C`. Mathlib does not have the bounded derived category
`Dᵇ(C)` at the pinned version, so the inverse map `K₀(Dᵇ(C)) → K₀(C)`, `[K] ↦ χ(K)`, and the
isomorphism `K₀(C) ≅ K₀(Dᵇ(C))` are not formalized here. What is proved is the compatibility of the
two constructions:

* `DG.AbelianK0.toDerived_eulerChar`: for a strictly bounded complex `K`,
  `toDerived (χ(K)) = [Q K]` in `K₀(D(C))`, where `Q : CochainComplex C ℤ ⥤ DerivedCategory C`
  is the localization functor;
* `DG.K0.mk_Q_obj_eq_toDerived`: consequently `[Q K] = Σₙ (-1)ⁿ [Hⁿ(K)[0]]` in `K₀(D(C))`.
-/

namespace DG

open CategoryTheory Category Limits ZeroObject Pretriangulated

universe w v u

namespace AbelianK0

/-! ### Finite alternating sums -/

section telescope

variable {G : Type*} [AddCommGroup G]

/-- A `finsum` over `ℤ` of a family vanishing outside `[a, a + m)` is the sum over
`a, a + 1, …, a + m - 1`. -/
theorem finsum_eq_sum_range (f : ℤ → G) (a : ℤ) (m : ℕ)
    (hf : ∀ n, n < a ∨ a + m ≤ n → f n = 0) :
    ∑ᶠ n, f n = ∑ i ∈ Finset.range m, f (a + i) := by
  let e : ℕ ↪ ℤ := ⟨fun i => a + i, fun i j h => by simpa using h⟩
  rw [finsum_eq_sum_of_support_subset f (s := (Finset.range m).map e), Finset.sum_map]
  · rfl
  · intro n hn
    simp only [Function.mem_support, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Finset.mem_range] at hn ⊢
    refine ⟨(n - a).toNat, ?_, ?_⟩
    · by_contra h
      exact hn (hf n (by omega))
    · by_contra h
      exact hn (hf n (by simp [e] at h; omega))

/-- Telescoping of an alternating sum: if `x n = h n + c (n - 1) + c n` for all `n`, then
`Σᵢ (-1)^(a+i) x (a+i) = Σᵢ (-1)^(a+i) h (a+i) + (-1)^a c (a-1) - (-1)^(a+m) c (a+m-1)`,
the sums running over `0 ≤ i < m`. -/
theorem sum_range_negOnePow_telescope (x h c : ℤ → G) (hx : ∀ n, x n = h n + c (n - 1) + c n)
    (a : ℤ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (a + i).negOnePow • x (a + i) =
      ∑ i ∈ Finset.range m, (a + i).negOnePow • h (a + i) + a.negOnePow • c (a - 1) -
        (a + m).negOnePow • c (a + m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hx]
    have e : a + ((m + 1 : ℕ) : ℤ) = a + m + 1 := by omega
    rw [e, Int.negOnePow_succ, add_sub_cancel_right, Units.neg_smul]
    simp only [smul_add]
    abel

end telescope

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### The Euler characteristic -/

/-- The degreewise identity `[Kⁿ] = [Hⁿ(K)] + [Bⁿ] + [Bⁿ⁺¹]`, where `Bⁿ⁺¹ ≅ coim (dⁿ)` is the
image of the differential `dⁿ : Kⁿ ⟶ Kⁿ⁺¹`. -/
theorem mk_X_eq (K : CochainComplex C ℤ) (n : ℤ) :
    mk (K.X n) = mk (K.homology n) + mk (Abelian.coimage (K.d (n - 1) (n - 1 + 1))) +
      mk (Abelian.coimage (K.d n (n + 1))) := by
  have h := mk_X₂_eq_mk_homology_add (K.sc' (n - 1) n (n + 1))
  rw [mk_eq_of_iso (K.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)).symm] at h
  have e : n - 1 + 1 = n := by omega
  rw [e]
  exact h

variable (K : CochainComplex C ℤ)

/-- The Euler characteristic `χ(K) = Σₙ (-1)ⁿ [Kⁿ] ∈ K₀(C)` of a cochain complex `K` in an
abelian category `C` (Weibel, *The K-book*, II.6), defined as a `finsum` with the sign
`Int.negOnePow n : ℤˣ`. It is meaningful for bounded complexes, for which it is a finite sum
(`DG.AbelianK0.eulerChar_eq_sum_Icc`). -/
noncomputable def eulerChar : AbelianK0 C := ∑ᶠ n : ℤ, n.negOnePow • mk (K.X n)

theorem eulerChar_eq_sum_range (a : ℤ) (m : ℕ) (hK : ∀ n, n < a ∨ a + m ≤ n → IsZero (K.X n)) :
    eulerChar K = ∑ i ∈ Finset.range m, (a + i).negOnePow • mk (K.X (a + i)) :=
  finsum_eq_sum_range _ a m (fun n hn => by rw [mk_eq_zero_of_isZero (hK n hn), smul_zero])

/-- For a complex `K` with `Kⁿ = 0` for `n < a` and `n > b`, `χ(K) = Σ_{a ≤ n ≤ b} (-1)ⁿ [Kⁿ]`. -/
theorem eulerChar_eq_sum_Icc (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    eulerChar K = ∑ n ∈ Finset.Icc a b, n.negOnePow • mk (K.X n) := by
  refine finsum_eq_sum_of_support_subset _ (fun n hn => ?_)
  simp only [Function.mem_support, Finset.coe_Icc, Set.mem_Icc] at hn ⊢
  by_contra h
  apply hn
  rw [not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [mk_eq_zero_of_isZero (K.isZero_of_isStrictlyGE a n h), smul_zero]
  · rw [mk_eq_zero_of_isZero (K.isZero_of_isStrictlyLE b n h), smul_zero]

/-- **The Euler characteristic of a bounded complex is the alternating sum of the classes of its
cohomology objects**: if `Kⁿ = 0` for `n < a` and for `n > b`, then
`χ(K) = Σₙ (-1)ⁿ [Kⁿ] = Σₙ (-1)ⁿ [Hⁿ(K)]` in `K₀(C)`. -/
theorem eulerChar_eq_finsum_homology (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    eulerChar K = ∑ᶠ n : ℤ, n.negOnePow • mk (K.homology n) := by
  set m := (b + 1 - a).toNat
  have hK : ∀ n, n < a ∨ a + m ≤ n → IsZero (K.X n) := by
    rintro n (hn | hn)
    · exact K.isZero_of_isStrictlyGE a n hn
    · exact K.isZero_of_isStrictlyLE b n (by omega)
  rw [eulerChar_eq_sum_range K a m hK, finsum_eq_sum_range _ a m (fun n hn => by
    rw [mk_eq_zero_of_isZero (show IsZero (K.homology n) from
      ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) (hK n hn)), smul_zero]),
    sum_range_negOnePow_telescope _ _ (fun n => mk (Abelian.coimage (K.d n (n + 1))))
      (mk_X_eq K),
    mk_coimage_eq_zero_of_isZero_source _ (hK _ (Or.inl (by omega))),
    mk_coimage_eq_zero_of_isZero_target _ (hK _ (Or.inr (by omega))), smul_zero, smul_zero,
    add_zero, sub_zero]

/-- The alternating sum of the classes of the objects of a bounded exact sequence vanishes:
if `K` is strictly bounded and exact in every degree, then `χ(K) = 0`. -/
theorem eulerChar_eq_zero_of_exactAt (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n, K.ExactAt n) : eulerChar K = 0 := by
  rw [eulerChar_eq_finsum_homology K a b]
  exact finsum_eq_zero_of_forall_eq_zero (fun n => by
    rw [mk_eq_zero_of_isZero ((hK n).isZero_homology), smul_zero])

variable {K} in
/-- Isomorphic complexes have the same Euler characteristic. -/
theorem eulerChar_eq_of_iso {L : CochainComplex C ℤ} (e : K ≅ L) :
    eulerChar K = eulerChar L := by
  unfold eulerChar
  congr 1
  ext n
  rw [mk_eq_of_iso (show K.X n ≅ L.X n from (HomologicalComplex.eval C _ n).mapIso e)]

variable {K} in
/-- Quasi-isomorphic bounded complexes have the same Euler characteristic. -/
theorem eulerChar_eq_of_quasiIso {L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] (a' b' : ℤ) [L.IsStrictlyGE a']
    [L.IsStrictlyLE b'] : eulerChar K = eulerChar L := by
  rw [eulerChar_eq_finsum_homology K a b, eulerChar_eq_finsum_homology L a' b']
  congr 1
  ext n
  rw [mk_eq_of_iso (asIso (HomologicalComplex.homologyMap φ n))]

/-- The Euler characteristic of an object `X` placed in degree `n` is `(-1)ⁿ [X]`. -/
theorem eulerChar_single (n : ℤ) (X : C) :
    eulerChar ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj X) =
      n.negOnePow • mk X := by
  unfold eulerChar
  rw [finsum_eq_single _ n (fun i hi => by
    rw [mk_eq_zero_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi), smul_zero]),
    mk_eq_of_iso (HomologicalComplex.singleObjXSelf _ n X)]

/-- Additivity of the Euler characteristic along a short exact sequence of complexes
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0`, when `K₂ⁿ = 0` for `n < a` and for `n ≥ a + m`. -/
theorem eulerChar_X₂_of_isZero {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (a : ℤ) (m : ℕ) (h₂ : ∀ n, n < a ∨ a + m ≤ n → IsZero (S.X₂.X n)) :
    eulerChar S.X₂ = eulerChar S.X₁ + eulerChar S.X₃ := by
  have hS' := HomologicalComplex.shortExact_iff_degreewise_shortExact S |>.1 hS
  have h₁ : ∀ n, n < a ∨ a + m ≤ n → IsZero (S.X₁.X n) := fun n hn => by
    have := (hS' n).mono_f
    exact IsZero.of_mono (S.map (HomologicalComplex.eval C _ n)).f (h₂ n hn)
  have h₃ : ∀ n, n < a ∨ a + m ≤ n → IsZero (S.X₃.X n) := fun n hn => by
    have := (hS' n).epi_g
    exact IsZero.of_epi (S.map (HomologicalComplex.eval C _ n)).g (h₂ n hn)
  rw [eulerChar_eq_sum_range _ a m h₁, eulerChar_eq_sum_range _ a m h₂,
    eulerChar_eq_sum_range _ a m h₃, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← smul_add]
  exact congrArg _ (mk_X₂ (hS' _))

/-- **Additivity of the Euler characteristic**: for a short exact sequence of cochain complexes
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` with `K₂` strictly bounded (hence also `K₁` and `K₃`),
`χ(K₂) = χ(K₁) + χ(K₃)`. -/
theorem eulerChar_X₂ {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (a b : ℤ)
    [S.X₂.IsStrictlyGE a] [S.X₂.IsStrictlyLE b] :
    eulerChar S.X₂ = eulerChar S.X₁ + eulerChar S.X₃ :=
  eulerChar_X₂_of_isZero hS a (b + 1 - a).toNat (by
    rintro n (hn | hn)
    · exact S.X₂.isZero_of_isStrictlyGE a n hn
    · exact S.X₂.isZero_of_isStrictlyLE b n (by omega))

/-! ### Comparison with the Grothendieck group of the derived category -/

section Derived

variable [HasDerivedCategory.{w} C]

/-- The homomorphism `K₀(C) →+ K₀(D(C))`, `[X] ↦ [X[0]]`, induced by the functor
`DerivedCategory.singleFunctor C 0` placing an object in degree `0`: a short exact sequence in
`C` gives a distinguished triangle in `D(C)` (`ShortComplex.ShortExact.singleTriangle`). -/
noncomputable def toDerived : AbelianK0 C →+ K0 (DerivedCategory C) :=
  lift (fun X => K0.mk ((DerivedCategory.singleFunctor C 0).obj X))
    (fun _ hS => K0.mk_obj₂ _ hS.singleTriangle_distinguished)

@[simp]
theorem toDerived_mk (X : C) :
    toDerived (mk X) = K0.mk ((DerivedCategory.singleFunctor C 0).obj X) :=
  lift_mk _ _ X

/-- `[X[-n]] = (-1)ⁿ [X[0]]` in `K₀(D(C))`, for an object `X` of `C` placed in degree `n`. -/
theorem _root_.DG.K0.mk_singleFunctor (n : ℤ) (X : C) :
    K0.mk ((DerivedCategory.singleFunctor C n).obj X) =
      n.negOnePow • K0.mk ((DerivedCategory.singleFunctor C 0).obj X) := by
  have h := K0.mk_eq_of_iso (((DerivedCategory.singleFunctors C).shiftIso n 0 n
    (add_zero n)).app X)
  dsimp at h
  rw [← h, K0.mk_shift, smul_smul, ← Int.negOnePow_add, ← two_mul,
    Int.negOnePow_two_mul, one_smul]

theorem _root_.DG.K0.mk_Q_obj_single (n : ℤ) (X : C) :
    K0.mk (DerivedCategory.Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj X)) =
      n.negOnePow • toDerived (mk X) := by
  rw [toDerived_mk, ← K0.mk_singleFunctor]
  exact K0.mk_eq_of_iso (((SingleFunctors.evaluation _ _ n).mapIso
    (DerivedCategory.singleFunctorsPostcompQIso C)).app X).symm

/-- A short exact sequence of cochain complexes `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` gives
`[Q K₂] = [Q K₁] + [Q K₃]` in `K₀(D(C))` (`DerivedCategory.triangleOfSES_distinguished`). -/
theorem _root_.DG.K0.mk_Q_obj_X₂ {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    K0.mk (DerivedCategory.Q.obj S.X₂) =
      K0.mk (DerivedCategory.Q.obj S.X₁) + K0.mk (DerivedCategory.Q.obj S.X₃) :=
  K0.mk_obj₂ _ (DerivedCategory.triangleOfSES_distinguished hS)

/-- `toDerived (χ(K)) = [Q K]` for a complex `K` with `Kⁿ = 0` for `n < a` and for `n ≥ a + m`.
The proof is by induction on `m`, splitting off the lowest degree through the short exact
sequence `0 ⟶ K' ⟶ K ⟶ Kᵃ[-a] ⟶ 0`. -/
theorem toDerived_eulerChar_of_isZero (m : ℕ) (K : CochainComplex C ℤ) (a : ℤ)
    (hK : ∀ n, n < a ∨ a + m ≤ n → IsZero (K.X n)) :
    toDerived (eulerChar K) = K0.mk (DerivedCategory.Q.obj K) := by
  induction m generalizing K a with
  | zero =>
    have hK' : IsZero K := (IsZero.iff_id_eq_zero K).2 (by
      ext n
      exact (hK n (by omega)).eq_of_src _ _)
    rw [eulerChar_eq_sum_range K a 0 hK, Finset.sum_range_zero, map_zero,
      K0.mk_eq_zero_of_isZero (DerivedCategory.Q.map_isZero hK')]
  | succ m ih =>
    let π : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a) :=
      HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi =>
        (hK i (Or.inl (by simp at hi; omega))).eq_of_src _ _)
    have hπa : IsIso (π.f a) := by
      rw [HomologicalComplex.mkHomToSingle_f]
      infer_instance
    have hπ : ∀ i, Epi (π.f i) := fun i => by
      by_cases hi : i = a
      · subst hi
        infer_instance
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).epi _
    have : Epi π := HomologicalComplex.epi_of_epi_f π hπ
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (S.exact_of_f_is_kernel (kernelIsKernel π)) (by dsimp [S]; infer_instance) this
    have hS' := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
    have h₁ : ∀ n, n < a + 1 ∨ a + 1 + m ≤ n → IsZero ((kernel π).X n) := by
      intro n hn
      by_cases hna : n = a
      · subst hna
        exact (hS' n).isIso_g_iff.1 hπa
      · have := (hS' n).isIso_f_iff.2
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (K.X a) n hna)
        have : IsIso ((kernel.ι π).f n) := this
        exact IsZero.of_iso (hK n (by omega)) (asIso ((kernel.ι π).f n))
    have e₁ : eulerChar K = eulerChar (kernel π) + eulerChar
        ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a)) :=
      eulerChar_X₂_of_isZero hS a (m + 1) hK
    have e₂ : K0.mk (DerivedCategory.Q.obj K) = K0.mk (DerivedCategory.Q.obj (kernel π)) +
        K0.mk (DerivedCategory.Q.obj
          ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a))) :=
      K0.mk_Q_obj_X₂ hS
    rw [e₁, e₂, map_add, ih _ (a + 1) h₁, eulerChar_single, K0.mk_Q_obj_single,
      Units.smul_def, Units.smul_def, map_zsmul]

/-- **Compatibility of the Euler characteristic with the derived category**: for a strictly
bounded complex `K`, the image of `χ(K) ∈ K₀(C)` in `K₀(D(C))` is the class `[Q K]` of `K` in the
derived category. -/
theorem toDerived_eulerChar (K : CochainComplex C ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] : toDerived (eulerChar K) = K0.mk (DerivedCategory.Q.obj K) :=
  toDerived_eulerChar_of_isZero (b + 1 - a).toNat K a (by
    rintro n (hn | hn)
    · exact K.isZero_of_isStrictlyGE a n hn
    · exact K.isZero_of_isStrictlyLE b n (by omega))

/-- For a strictly bounded complex `K`, `[Q K] = Σₙ (-1)ⁿ [Hⁿ(K)[0]]` in `K₀(D(C))`. -/
theorem _root_.DG.K0.mk_Q_obj_eq_toDerived (K : CochainComplex C ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    K0.mk (DerivedCategory.Q.obj K) =
      toDerived (∑ᶠ n : ℤ, n.negOnePow • mk (K.homology n)) := by
  rw [← eulerChar_eq_finsum_homology K a b, toDerived_eulerChar K a b]

end Derived

end AbelianK0

end DG
