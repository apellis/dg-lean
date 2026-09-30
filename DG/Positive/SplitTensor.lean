import DG.Positive.K0Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor products of split semisimple algebras

Let `k` be a field and `R₁`, `R₂` semisimple `k`-algebras. An idempotent `e` of a `k`-algebra `R`
is *split* (`DG.IsSplitIdem k e`) if `e R e = k e`; for a simple idempotent this says that the
simple module `R e` has endomorphism ring `k` (it holds e.g. when `k` is algebraically closed
and `R` is finite-dimensional). If all simple idempotents of `R₁` and `R₂` are split
(`DG.IsSplitSemisimple k R`), then:

* for simple idempotents `e`, `f`, the left ideal `(R₁ ⊗ R₂) (e ⊗ f)` is simple
  (`DG.isSimpleModule_span_tmul`), by a density argument: the functionals `a ↦ c` with
  `e r a e = c e` separate the points of `R₁ e` (`DG.IsSplitIdem.exists_coeff_eq_one`), hence
  their tensor products separate the points of `R₁ e ⊗ R₂ f`
  (`DG.eq_zero_of_forall_tensorCoeff_eq_zero`);
* `R₁ ⊗ R₂` is semisimple (`DG.isSemisimpleRing_tensorProduct`), since `1 = ∑ eₐ ⊗ f_b` for
  decompositions `1 = ∑ eₐ`, `1 = ∑ f_b` into simple idempotents
  (`DG.exists_list_sum_eq_of_isSemisimpleRing`);
* `e ⊗ f` and `e' ⊗ f'` are equivalent iff `e ~ e'` and `f ~ f'`
  (`DG.idemEquiv_tmul_iff`), and every simple idempotent of `R₁ ⊗ R₂` is equivalent to some
  `e ⊗ f` (`DG.exists_idemEquiv_tmul`). So the simple `R₁ ⊗ R₂`-modules are the `S ⊗ T` for
  simple `R₁`-modules `S` and simple `R₂`-modules `T`.

Without the splitting hypothesis all three statements fail: `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ`, so the tensor
product of the simple modules `ℂ` is not simple; and for a purely inseparable extension
`K = k(t^{1/p})` of `k = 𝔽_p(t)`, `K ⊗_k K` is not reduced, hence not semisimple.
-/

open scoped TensorProduct

namespace DG

section Ring

variable {R : Type*} [Ring R]

theorem IdemEquiv.trans {e f g : R} (h₁ : IdemEquiv R e f) (h₂ : IdemEquiv R f g) :
    IdemEquiv R e g := by
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := h₁
  obtain ⟨b', c', h1', h2', h3', h4', h5', h6'⟩ := h₂
  refine ⟨b * b', c' * c, by rw [← mul_assoc, h1], by rw [mul_assoc, h2'],
    by rw [← mul_assoc, h3'], by rw [mul_assoc, h4], ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc b' c', h5', ← mul_assoc, h2, h5]
  · rw [mul_assoc, ← mul_assoc c b, h6, ← mul_assoc, h4', h6']

/-- In a ring, simple idempotents `e`, `f` which are not equivalent satisfy `e R f = 0` (Schur's
lemma). -/
theorem mul_mul_eq_zero_of_not_idemEquiv {e f : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hse : IsSimpleModule R (Submodule.span R {e}))
    (hsf : IsSimpleModule R (Submodule.span R {f})) (h : ¬ IdemEquiv R e f) (a : R) :
    e * a * f = 0 := by
  by_contra hb
  obtain ⟨c, h3, h4, h5, h6⟩ := exists_mul_eq_of_isSimpleModule he hf hse hsf
    (b := e * a * f) (by rw [← mul_assoc, ← mul_assoc, he.eq]) (by rw [mul_assoc, hf.eq]) hb
  exact h ⟨e * a * f, c, by rw [← mul_assoc, ← mul_assoc, he.eq], by rw [mul_assoc, hf.eq],
    h3, h4, h5, h6⟩

/-- In a semisimple ring, every idempotent is a finite sum of simple idempotents. -/
theorem exists_list_sum_eq_of_isSemisimpleRing [IsSemisimpleRing R] {g : R}
    (hg : IsIdempotentElem g) :
    ∃ l : List R, (∀ s ∈ l, IsIdempotentElem s ∧ IsSimpleModule R (Submodule.span R {s})) ∧
      l.sum = g := by
  have : IsArtinianRing R := inferInstance
  suffices H : ∀ N : Submodule R R, ∀ g : R, IsIdempotentElem g → Submodule.span R {g} = N →
      ∃ l : List R, (∀ s ∈ l, IsIdempotentElem s ∧ IsSimpleModule R (Submodule.span R {s})) ∧
        l.sum = g from H _ g hg rfl
  intro N
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  intro g hg hN
  by_cases h0 : Submodule.span R {g} = ⊥
  · exact ⟨[], by simp, by simpa using (Submodule.span_singleton_eq_bot.mp h0).symm⟩
  obtain ⟨s, t, hs, ht, -, -, hsum, hsimple, hlt⟩ :=
    exists_isSimpleModule_add_of_isSemisimpleRing hg h0
  obtain ⟨l, hl, hlsum⟩ := ih _ (hN ▸ hlt) t ht rfl
  refine ⟨s :: l, fun x hx => ?_, by rw [List.sum_cons, hlsum, hsum]⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨hs, hsimple⟩
  · exact hl x hx

end Ring

/-! ### Split idempotents -/

section Split

variable (k : Type*) [Field k] {R : Type*} [Ring R] [Algebra k R]

/-- An idempotent `e` of a `k`-algebra is *split* if `e R e = k e`. -/
def IsSplitIdem (e : R) : Prop :=
  ∀ a : R, ∃ c : k, e * a * e = c • e

/-- A `k`-algebra is *split semisimple* (for our purposes) if all its simple idempotents are
split, i.e. all its simple modules `R e` have endomorphism ring `k`. -/
def IsSplitSemisimple (R : Type*) [Ring R] [Algebra k R] : Prop :=
  ∀ e : R, IsIdempotentElem e → IsSimpleModule R (Submodule.span R {e}) → IsSplitIdem k e

variable {k}

namespace IsSplitIdem

variable {e : R} (he : IsSplitIdem k e) (he0 : e ≠ 0)

/-- The coefficient functional `a ↦ c`, where `e r a e = c e`. -/
noncomputable def coeff (r : R) : R →ₗ[k] k where
  toFun a := Classical.choose (he (r * a))
  map_add' a b := smul_left_injective k he0 (by
    change Classical.choose (he (r * (a + b))) • e =
      (Classical.choose (he (r * a)) + Classical.choose (he (r * b))) • e
    rw [add_smul, ← Classical.choose_spec (he (r * (a + b))),
      ← Classical.choose_spec (he (r * a)), ← Classical.choose_spec (he (r * b)), mul_add,
      mul_add, add_mul])
  map_smul' c a := smul_left_injective k he0 (by
    change Classical.choose (he (r * (c • a))) • e =
      (c * Classical.choose (he (r * a))) • e
    rw [mul_smul, ← Classical.choose_spec (he (r * (c • a))),
      ← Classical.choose_spec (he (r * a)), mul_smul_comm, mul_smul_comm, smul_mul_assoc])

theorem coeff_spec (r a : R) : e * (r * a) * e = he.coeff he0 r a • e :=
  Classical.choose_spec (he (r * a))

theorem coeff_mul_self (r a : R) (hidem : IsIdempotentElem e) :
    he.coeff he0 r (a * e) = he.coeff he0 r a := by
  refine smul_left_injective k he0 ?_
  change he.coeff he0 r (a * e) • e = he.coeff he0 r a • e
  rw [← coeff_spec, ← coeff_spec]
  simp only [mul_assoc, hidem.eq]

theorem coeff_self (hidem : IsIdempotentElem e) : he.coeff he0 e e = 1 := by
  refine smul_left_injective k he0 ?_
  change he.coeff he0 e e • e = (1 : k) • e
  rw [← coeff_spec, one_smul, hidem.eq, hidem.eq, hidem.eq]

/-- The coefficient functionals separate the points of the simple module `R e`. -/
theorem exists_coeff_eq_one (hidem : IsIdempotentElem e)
    (hs : IsSimpleModule R (Submodule.span R {e})) {a : R} (ha : a * e = a) (ha0 : a ≠ 0) :
    ∃ r, he.coeff he0 r a = 1 := by
  have hle : Submodule.span R {a} ≤ Submodule.span R {e} :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr ((mem_span_singleton_iff_mul_eq hidem).mpr ha)
  rcases (isSimpleModule_iff_isAtom.mp hs).le_iff.mp hle with h | h
  · exact absurd (Submodule.span_singleton_eq_bot.mp h) ha0
  · have hmem : e ∈ Submodule.span R {a} := h ▸ Submodule.subset_span rfl
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨r, smul_left_injective k he0 ?_⟩
    change he.coeff he0 r a • e = (1 : k) • e
    rw [← coeff_spec, ← smul_eq_mul r a, hr, one_smul, hidem.eq, hidem.eq]

end IsSplitIdem

end Split

/-! ### Tensor products -/

section Tensor

variable {k : Type*} [Field k] {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] [Algebra k R₁] [Algebra k R₂]

/-- The functional `a ⊗ b ↦ φ a * ψ b` on `R₁ ⊗ R₂`. -/
noncomputable def tensorCoeff (φ : R₁ →ₗ[k] k) (ψ : R₂ →ₗ[k] k) : R₁ ⊗[k] R₂ →ₗ[k] k :=
  TensorProduct.lift ((LinearMap.mul k k).compl₁₂ φ ψ)

@[simp]
theorem tensorCoeff_tmul (φ : R₁ →ₗ[k] k) (ψ : R₂ →ₗ[k] k) (a : R₁) (b : R₂) :
    tensorCoeff φ ψ (a ⊗ₜ b) = φ a * ψ b :=
  rfl

theorem rid_lTensor_mul (ψ : R₂ →ₗ[k] k) (e : R₁) (x : R₁ ⊗[k] R₂) :
    TensorProduct.rid k R₁ (ψ.lTensor R₁ (x * (e ⊗ₜ[k] (1 : R₂)))) =
      TensorProduct.rid k R₁ (ψ.lTensor R₁ x) * e := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [add_mul, map_add, map_add, hx, hy, map_add, map_add, add_mul]

theorem lid_rTensor_mul (φ : R₁ →ₗ[k] k) (f : R₂) (x : R₁ ⊗[k] R₂) :
    TensorProduct.lid k R₂ (φ.rTensor R₂ (x * ((1 : R₁) ⊗ₜ[k] f))) =
      TensorProduct.lid k R₂ (φ.rTensor R₂ x) * f := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [add_mul, map_add, map_add, hx, hy, map_add, map_add, add_mul]

theorem apply_lid_rTensor (φ : R₁ →ₗ[k] k) (ψ : R₂ →ₗ[k] k) (x : R₁ ⊗[k] R₂) :
    ψ (TensorProduct.lid k R₂ (φ.rTensor R₂ x)) = tensorCoeff φ ψ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

theorem apply_rid_lTensor (φ : R₁ →ₗ[k] k) (ψ : R₂ →ₗ[k] k) (x : R₁ ⊗[k] R₂) :
    φ (TensorProduct.rid k R₁ (ψ.lTensor R₁ x)) = tensorCoeff φ ψ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [mul_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

variable {e : R₁} {f : R₂} (hidem₁ : IsIdempotentElem e) (hidem₂ : IsIdempotentElem f)
  (hs₁ : IsSimpleModule R₁ (Submodule.span R₁ {e}))
  (hs₂ : IsSimpleModule R₂ (Submodule.span R₂ {f}))
  (he : IsSplitIdem k e) (hf : IsSplitIdem k f)

include hs₁ in
theorem ne_zero_of_simple₁ : e ≠ 0 := ne_zero_of_isSimpleModule hs₁

include hs₂ in
theorem ne_zero_of_simple₂ : f ≠ 0 := ne_zero_of_isSimpleModule hs₂

include hidem₁ hidem₂ hs₁ hs₂ in
/-- **Density**: the functionals `a ⊗ b ↦ c₁ c₂` (`e r₁ a e = c₁ e`, `f r₂ b f = c₂ f`) separate
the points of `R₁ e ⊗ R₂ f`. -/
theorem eq_zero_of_forall_tensorCoeff_eq_zero {x : R₁ ⊗[k] R₂} (hx : x * (e ⊗ₜ[k] f) = x)
    (h : ∀ r₁ r₂, tensorCoeff (he.coeff (ne_zero_of_simple₁ hs₁) r₁)
      (hf.coeff (ne_zero_of_simple₂ hs₂) r₂) x = 0) : x = 0 := by
  classical
  have he0 := ne_zero_of_simple₁ hs₁
  have hf0 := ne_zero_of_simple₂ hs₂
  have hxe : x * (e ⊗ₜ[k] (1 : R₂)) = x := by
    rw [← hx, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, hidem₁.eq, mul_one]
  have hxf : x * ((1 : R₁) ⊗ₜ[k] f) = x := by
    rw [← hx, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, hidem₂.eq, mul_one]
  let 𝒞 := Module.Basis.ofVectorSpace k R₂
  -- the coefficients `cᵢ ∈ R₁ e` of `x = ∑ cᵢ ⊗ 𝒞ᵢ`
  have hc : ∀ i, TensorProduct.rid k R₁ ((𝒞.coord i).lTensor R₁ x) = 0 := by
    intro i
    set c := TensorProduct.rid k R₁ ((𝒞.coord i).lTensor R₁ x)
    have hce : c * e = c := by
      change _ = TensorProduct.rid k R₁ ((𝒞.coord i).lTensor R₁ x)
      rw [← rid_lTensor_mul, hxe]
    by_contra hc0
    obtain ⟨r₁, hr₁⟩ := he.exists_coeff_eq_one he0 hidem₁ hs₁ hce hc0
    set y := TensorProduct.lid k R₂ ((he.coeff he0 r₁).rTensor R₂ x)
    have hyf : y * f = y := by
      change _ = TensorProduct.lid k R₂ ((he.coeff he0 r₁).rTensor R₂ x)
      rw [← lid_rTensor_mul, hxf]
    have hy0 : y = 0 := by
      by_contra hy0
      obtain ⟨r₂, hr₂⟩ := hf.exists_coeff_eq_one hf0 hidem₂ hs₂ hyf hy0
      rw [apply_lid_rTensor, h] at hr₂
      exact zero_ne_one hr₂
    have h1 : 𝒞.coord i (TensorProduct.lid k R₂ ((he.coeff he0 r₁).rTensor R₂ x)) = 1 := by
      rw [apply_lid_rTensor, ← apply_rid_lTensor, hr₁]
    change 𝒞.coord i y = 1 at h1
    rw [hy0, map_zero] at h1
    exact zero_ne_one h1
  have h0 : TensorProduct.equivFinsuppOfBasisRight 𝒞 x = 0 := by
    ext i
    rw [TensorProduct.equivFinsuppOfBasisRight_apply, hc i, Finsupp.zero_apply]
  exact (TensorProduct.equivFinsuppOfBasisRight 𝒞).map_eq_zero_iff.mp h0

theorem tmul_mul_mul_tmul (r₁ : R₁) (r₂ : R₂) (x : R₁ ⊗[k] R₂) (he0 : e ≠ 0) (hf0 : f ≠ 0) :
    (e ⊗ₜ[k] f) * ((r₁ ⊗ₜ[k] r₂) * x) * (e ⊗ₜ[k] f) =
      tensorCoeff (he.coeff he0 r₁) (hf.coeff hf0 r₂) x • (e ⊗ₜ[k] f) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, he.coeff_spec he0, hf.coeff_spec hf0,
      tensorCoeff_tmul, TensorProduct.smul_tmul_smul, mul_comm]
  | add x y hx hy => rw [mul_add, mul_add, add_mul, hx, hy, map_add, add_smul]

include hidem₁ hidem₂ hs₁ hs₂ he hf in
/-- For split simple idempotents `e`, `f`, the left ideal `(R₁ ⊗ R₂) (e ⊗ f)` is simple. -/
theorem isSimpleModule_span_tmul :
    IsSimpleModule (R₁ ⊗[k] R₂) (Submodule.span (R₁ ⊗[k] R₂) {e ⊗ₜ[k] f}) := by
  have he0 := ne_zero_of_simple₁ hs₁
  have hf0 := ne_zero_of_simple₂ hs₂
  have hg : IsIdempotentElem (e ⊗ₜ[k] f) := by
    rw [IsIdempotentElem, Algebra.TensorProduct.tmul_mul_tmul, hidem₁.eq, hidem₂.eq]
  have key : ∀ x ∈ Submodule.span (R₁ ⊗[k] R₂) {e ⊗ₜ[k] f}, x ≠ 0 →
      ∀ N : Submodule (R₁ ⊗[k] R₂) (R₁ ⊗[k] R₂), x ∈ N → e ⊗ₜ[k] f ∈ N := by
    intro x hx hx0 N hxN
    have hxg : x * (e ⊗ₜ[k] f) = x := (mem_span_singleton_iff_mul_eq hg).mp hx
    by_contra hgN
    apply hx0
    refine eq_zero_of_forall_tensorCoeff_eq_zero hidem₁ hidem₂ hs₁ hs₂ he hf hxg fun r₁ r₂ => ?_
    by_contra hc
    apply hgN
    have hmem : (e ⊗ₜ[k] f) * ((r₁ ⊗ₜ[k] r₂) * x) * (e ⊗ₜ[k] f) ∈ N := by
      rw [mul_assoc, mul_assoc, hxg, ← mul_assoc]
      exact N.smul_mem _ hxN
    rw [tmul_mul_mul_tmul he hf r₁ r₂ x he0 hf0] at hmem
    have := N.smul_of_tower_mem (tensorCoeff (he.coeff he0 r₁) (hf.coeff hf0 r₂) x)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  rw [isSimpleModule_iff_isAtom]
  refine ⟨fun h => ?_, fun N hN => ?_⟩
  · have hgmem : e ⊗ₜ[k] f ∈ Submodule.span (R₁ ⊗[k] R₂) {e ⊗ₜ[k] f} := Submodule.subset_span rfl
    have hgne : e ⊗ₜ[k] f ≠ 0 := by
      intro h0
      have := congrArg (tensorCoeff (he.coeff he0 e) (hf.coeff hf0 f)) h0
      rw [tensorCoeff_tmul, he.coeff_self he0 hidem₁, hf.coeff_self hf0 hidem₂, map_zero] at this
      simp at this
    rw [h] at hgmem
    exact hgne ((Submodule.mem_bot _).mp hgmem)
  · by_contra hN0
    obtain ⟨x, hxN, hx0⟩ := N.ne_bot_iff.mp hN0
    have := key x (hN.le hxN) hx0 N hxN
    exact hN.not_ge ((Submodule.span_singleton_le_iff_mem _ _).mpr this)

/-! ### Semisimplicity and simple modules of the tensor product -/

theorem list_sum_tmul_list_sum_mem (M : AddSubmonoid (R₁ ⊗[k] R₂)) (l₁ : List R₁) (l₂ : List R₂)
    (h : ∀ s ∈ l₁, ∀ t ∈ l₂, s ⊗ₜ[k] t ∈ M) : l₁.sum ⊗ₜ[k] l₂.sum ∈ M := by
  induction l₁ with
  | nil => rw [List.sum_nil, TensorProduct.zero_tmul]; exact M.zero_mem
  | cons s l₁ ih =>
    rw [List.sum_cons, TensorProduct.add_tmul]
    refine M.add_mem ?_ (ih fun s' hs' t ht => h s' (List.mem_cons_of_mem _ hs') t ht)
    clear ih
    induction l₂ with
    | nil => rw [List.sum_nil, TensorProduct.tmul_zero]; exact M.zero_mem
    | cons t l₂ ih =>
      rw [List.sum_cons, TensorProduct.tmul_add]
      exact M.add_mem (h s (List.mem_cons_self ..) t (List.mem_cons_self ..))
        (ih fun s' hs' t' ht' => h s' hs' t' (List.mem_cons_of_mem _ ht'))

theorem IdemEquiv.tmul {e e' : R₁} {f f' : R₂} (h : IdemEquiv R₁ e e') (h' : IdemEquiv R₂ f f') :
    IdemEquiv (R₁ ⊗[k] R₂) (e ⊗ₜ[k] f) (e' ⊗ₜ[k] f') := by
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨b', c', h1', h2', h3', h4', h5', h6'⟩ := h'
  refine ⟨b ⊗ₜ b', c ⊗ₜ c', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [Algebra.TensorProduct.tmul_mul_tmul] <;> congr 1

theorem not_idemEquiv_of_forall_mul_mul_eq_zero {R : Type*} [Ring R] {g g' : R} (hg0 : g ≠ 0)
    (h : ∀ y, g * y * g' = 0) : ¬ IdemEquiv R g g' := by
  rintro ⟨b, c, h1, h2, -, -, h5, -⟩
  apply hg0
  rw [← h5, ← h1, ← h2, ← mul_assoc, h b, zero_mul]

variable (k) in
/-- **The tensor product of split semisimple algebras is semisimple.** -/
theorem isSemisimpleRing_tensorProduct [IsSemisimpleRing R₁] [IsSemisimpleRing R₂]
    (h₁ : IsSplitSemisimple k R₁) (h₂ : IsSplitSemisimple k R₂) :
    IsSemisimpleRing (R₁ ⊗[k] R₂) := by
  obtain ⟨l₁, hl₁, hs₁⟩ := exists_list_sum_eq_of_isSemisimpleRing (R := R₁) IsIdempotentElem.one
  obtain ⟨l₂, hl₂, hs₂⟩ := exists_list_sum_eq_of_isSemisimpleRing (R := R₂) IsIdempotentElem.one
  refine IsSemisimpleModule.of_sSup_simples_eq_top (eq_top_iff.mpr fun x _ => ?_)
  set M := sSup {m : Submodule (R₁ ⊗[k] R₂) (R₁ ⊗[k] R₂) | IsSimpleModule (R₁ ⊗[k] R₂) m}
  have h1 : (1 : R₁ ⊗[k] R₂) ∈ M := by
    rw [Algebra.TensorProduct.one_def, ← hs₁, ← hs₂]
    refine list_sum_tmul_list_sum_mem M.toAddSubmonoid _ _ fun s hs t ht => ?_
    have hsimple := isSimpleModule_span_tmul (hl₁ s hs).1 (hl₂ t ht).1 (hl₁ s hs).2 (hl₂ t ht).2
      (h₁ s (hl₁ s hs).1 (hl₁ s hs).2) (h₂ t (hl₂ t ht).1 (hl₂ t ht).2)
    have hle : Submodule.span (R₁ ⊗[k] R₂) {s ⊗ₜ[k] t} ≤ M :=
      le_sSup (show Submodule.span (R₁ ⊗[k] R₂) {s ⊗ₜ[k] t} ∈
        {m : Submodule (R₁ ⊗[k] R₂) (R₁ ⊗[k] R₂) | IsSimpleModule (R₁ ⊗[k] R₂) m} from hsimple)
    exact hle (Submodule.subset_span rfl)
  simpa using M.smul_mem x h1

variable {e e' : R₁} {f f' : R₂}

/-- For simple split idempotents, `e ⊗ f ~ e' ⊗ f'` iff `e ~ e'` and `f ~ f'`. -/
theorem idemEquiv_tmul_iff (hidem₁ : IsIdempotentElem e) (hidem₁' : IsIdempotentElem e')
    (hidem₂ : IsIdempotentElem f) (hidem₂' : IsIdempotentElem f')
    (hs₁ : IsSimpleModule R₁ (Submodule.span R₁ {e}))
    (hs₁' : IsSimpleModule R₁ (Submodule.span R₁ {e'}))
    (hs₂ : IsSimpleModule R₂ (Submodule.span R₂ {f}))
    (hs₂' : IsSimpleModule R₂ (Submodule.span R₂ {f'}))
    (he : IsSplitIdem k e) (hf : IsSplitIdem k f) :
    IdemEquiv (R₁ ⊗[k] R₂) (e ⊗ₜ[k] f) (e' ⊗ₜ[k] f') ↔ IdemEquiv R₁ e e' ∧ IdemEquiv R₂ f f' := by
  refine ⟨fun h => ?_, fun h => h.1.tmul h.2⟩
  have hg0 : e ⊗ₜ[k] f ≠ 0 :=
    ne_zero_of_isSimpleModule (isSimpleModule_span_tmul hidem₁ hidem₂ hs₁ hs₂ he hf)
  constructor
  · by_contra hn
    refine not_idemEquiv_of_forall_mul_mul_eq_zero hg0 (fun y => ?_) h
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_mul_eq_zero_of_not_idemEquiv hidem₁ hidem₁' hs₁ hs₁' hn, TensorProduct.zero_tmul]
    | add x y hx hy => rw [mul_add, add_mul, hx, hy, add_zero]
  · by_contra hn
    refine not_idemEquiv_of_forall_mul_mul_eq_zero hg0 (fun y => ?_) h
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_mul_eq_zero_of_not_idemEquiv hidem₂ hidem₂' hs₂ hs₂' hn, TensorProduct.tmul_zero]
    | add x y hx hy => rw [mul_add, add_mul, hx, hy, add_zero]

/-- Every simple idempotent of `R₁ ⊗ R₂` is equivalent to some `s ⊗ t`, for any decompositions
`1 = ∑ s` and `1 = ∑ t` into simple split idempotents. -/
theorem exists_idemEquiv_tmul {g : R₁ ⊗[k] R₂} (hg : IsIdempotentElem g)
    (hsg : IsSimpleModule (R₁ ⊗[k] R₂) (Submodule.span (R₁ ⊗[k] R₂) {g}))
    {l₁ : List R₁} {l₂ : List R₂}
    (hl₁ : ∀ s ∈ l₁, IsIdempotentElem s ∧ IsSimpleModule R₁ (Submodule.span R₁ {s}) ∧
      IsSplitIdem k s)
    (hl₂ : ∀ t ∈ l₂, IsIdempotentElem t ∧ IsSimpleModule R₂ (Submodule.span R₂ {t}) ∧
      IsSplitIdem k t)
    (hs₁ : l₁.sum = 1) (hs₂ : l₂.sum = 1) :
    ∃ s ∈ l₁, ∃ t ∈ l₂, IdemEquiv (R₁ ⊗[k] R₂) g (s ⊗ₜ[k] t) := by
  by_contra H
  push Not at H
  apply ne_zero_of_isSimpleModule hsg
  have hmem : (1 : R₁ ⊗[k] R₂) ∈ AddMonoidHom.mker (AddMonoidHom.mulLeft g) := by
    rw [Algebra.TensorProduct.one_def, ← hs₁, ← hs₂]
    refine list_sum_tmul_list_sum_mem _ _ _ fun s hs t ht => ?_
    obtain ⟨hs, hss, hsp⟩ := hl₁ s hs
    obtain ⟨ht, hts, htp⟩ := hl₂ t ht
    have hst : IsIdempotentElem (s ⊗ₜ[k] t) := by
      rw [IsIdempotentElem, Algebra.TensorProduct.tmul_mul_tmul, hs.eq, ht.eq]
    have := mul_mul_eq_zero_of_not_idemEquiv hg hst hsg
      (isSimpleModule_span_tmul hs ht hss hts hsp htp) (H s ‹_› t ‹_›) 1
    rw [mul_one] at this
    exact this
  simpa using hmem

end Tensor

end DG
