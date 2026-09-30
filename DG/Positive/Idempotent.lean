import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# Simple idempotents of semisimple rings

Let `R` be a ring. For an idempotent `e ∈ R`, the left ideal `R e = R ∙ e` consists of the `x`
with `x e = x` (`DG.mem_span_singleton_iff_mul_eq`). We call `e` *simple* if `R e` is a simple
left `R`-module; for a semisimple ring these are the primitive idempotents, and the modules
`R e` are the simple modules.

* `DG.exists_mul_eq_of_isSimpleModule`: Schur's lemma for simple idempotents: a nonzero
  `b ∈ e R f` has an inverse `c ∈ f R e` with `b c = e` and `c b = f`.
* `DG.exists_isSimpleModule_add_of_isSemisimpleRing`: in a semisimple ring, an idempotent `g`
  with `R g ≠ 0` splits as a sum `g = s + t` of orthogonal idempotents with `R s` simple and
  `R t < R g`. Iterating (the lattice of left ideals is Artinian) decomposes every idempotent
  into a finite sum of orthogonal simple idempotents.

These facts are used for the degree-`0` part `A⁰` of a positive dg ring (Schnürer's simple
modules `L_x = e A⁰` [Sch, §2], here on the left: `L = A⁰ e`).
-/

namespace DG

variable {R : Type*} [Ring R]

theorem mem_span_singleton_iff_mul_eq {g x : R} (hg : IsIdempotentElem g) :
    x ∈ Submodule.span R {g} ↔ x * g = x := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [smul_eq_mul, mul_assoc, hg.eq]
  · intro h
    exact ⟨x, h⟩

theorem ne_zero_of_isSimpleModule {e : R} (he : IsSimpleModule R (Submodule.span R {e})) :
    e ≠ 0 := by
  rintro rfl
  rw [Set.singleton_zero, Submodule.span_zero] at he
  exact (isSimpleModule_iff_isAtom.mp he).1 rfl

/-- **Schur's lemma** for simple idempotents: if `R e` and `R f` are simple and `b ≠ 0` with
`e b = b = b f`, then right multiplication by `b` is an isomorphism `R e ≅ R f`, with inverse the
right multiplication by some `c` with `f c = c = c e`, `b c = e` and `c b = f`. -/
theorem exists_mul_eq_of_isSimpleModule {e f b : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hse : IsSimpleModule R (Submodule.span R {e}))
    (hsf : IsSimpleModule R (Submodule.span R {f})) (heb : e * b = b) (hbf : b * f = b)
    (hb : b ≠ 0) : ∃ c : R, f * c = c ∧ c * e = c ∧ b * c = e ∧ c * b = f := by
  let ρ : Submodule.span R {e} →ₗ[R] Submodule.span R {f} :=
    { toFun := fun x => ⟨x * b, (mem_span_singleton_iff_mul_eq hf).mpr (by
        rw [mul_assoc, hbf])⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun a x => Subtype.ext (mul_assoc _ _ _) }
  have hρ : ∀ x, (ρ x : R) = x * b := fun _ => rfl
  have heS : e ∈ Submodule.span R {e} := Submodule.subset_span rfl
  have hρ0 : ρ ≠ 0 := by
    intro h
    have := congrArg (fun φ : Submodule.span R {e} →ₗ[R] Submodule.span R {f} =>
      ((φ ⟨e, heS⟩ : Submodule.span R {f}) : R)) h
    simp only [hρ, heb, LinearMap.zero_apply, ZeroMemClass.coe_zero] at this
    exact hb this
  have hbij := LinearMap.bijective_of_ne_zero hρ0
  obtain ⟨⟨c, hc⟩, hcb⟩ := hbij.2 ⟨f, Submodule.subset_span rfl⟩
  have hcb' : c * b = f := congrArg Subtype.val hcb
  have hce : c * e = c := (mem_span_singleton_iff_mul_eq he).mp hc
  have hinj : ∀ x y : R, x * e = x → y * e = y → x * b = y * b → x = y := by
    intro x y hx hy hxy
    have := hbij.1 (a₁ := ⟨x, (mem_span_singleton_iff_mul_eq he).mpr hx⟩)
      (a₂ := ⟨y, (mem_span_singleton_iff_mul_eq he).mpr hy⟩) (Subtype.ext hxy)
    exact congrArg Subtype.val this
  refine ⟨c, ?_, hce, ?_, hcb'⟩
  · refine hinj _ _ (by rw [mul_assoc, hce]) hce ?_
    rw [mul_assoc, hcb', hf.eq]
  · refine hinj _ _ (by rw [mul_assoc, hce]) he.eq ?_
    rw [mul_assoc, hcb', hbf, heb]

/-- In a semisimple ring, an idempotent `g` with `R g ≠ 0` is the sum `g = s + t` of two
orthogonal idempotents with `R s` simple and `R t < R g`. -/
theorem exists_isSimpleModule_add_of_isSemisimpleRing [IsSemisimpleRing R] {g : R}
    (hg : IsIdempotentElem g) (hN : Submodule.span R {g} ≠ ⊥) :
    ∃ s t : R, IsIdempotentElem s ∧ IsIdempotentElem t ∧ s * t = 0 ∧ t * s = 0 ∧ s + t = g ∧
      IsSimpleModule R (Submodule.span R {s}) ∧
      Submodule.span R {t} < Submodule.span R {g} := by
  set N := Submodule.span R {g}
  obtain ⟨S, hSN, hS⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le N).resolve_left hN
  obtain ⟨S', hSS'⟩ := exists_isCompl S
  set T := S' ⊓ N
  have hST : S ⊓ T = ⊥ := by
    rw [← inf_assoc, hSS'.inf_eq_bot, bot_inf_eq]
  have hsup : S ⊔ T = N := by
    rw [← sup_inf_assoc_of_le _ hSN, hSS'.sup_eq_top, top_inf_eq]
  have hTN : T ≤ N := inf_le_right
  have hmemN : ∀ x ∈ N, x * g = x := fun x hx => (mem_span_singleton_iff_mul_eq hg).mp hx
  have hdisj : ∀ x, x ∈ S → x ∈ T → x = 0 := fun x hxS hxT => by
    have : x ∈ S ⊓ T := ⟨hxS, hxT⟩
    rwa [hST, Submodule.mem_bot] at this
  have hgN : g ∈ N := Submodule.subset_span rfl
  rw [← hsup] at hgN
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hgN
  -- `x = x s + x t` for `x ∈ N`, with `x s ∈ S` and `x t ∈ T`.
  have hsplit : ∀ x ∈ N, x * s + x * t = x := fun x hx => by
    rw [← mul_add, hst, hmemN x hx]
  have hsT : ∀ x, x * t ∈ T := fun x => T.smul_mem x ht
  have hsS : ∀ x, x * s ∈ S := fun x => S.smul_mem x hs
  have hs_ss : s * s = s ∧ s * t = 0 := by
    have h := hsplit s (hSN hs)
    have h0 : s * t = 0 := hdisj _ (by
      rw [eq_sub_of_add_eq' h]
      exact S.sub_mem hs (hsS s)) (hsT s)
    exact ⟨by rw [h0, add_zero] at h; exact h, h0⟩
  have ht_tt : t * t = t ∧ t * s = 0 := by
    have h := hsplit t (hTN ht)
    have h0 : t * s = 0 := hdisj _ (hsS t) (by
      rw [eq_sub_of_add_eq h]
      exact T.sub_mem ht (hsT t))
    exact ⟨by rw [h0, zero_add] at h; exact h, h0⟩
  have hsIdem : IsIdempotentElem s := hs_ss.1
  have htIdem : IsIdempotentElem t := ht_tt.1
  have hspanS : Submodule.span R {s} = S := by
    refine le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr hs) fun x hx => ?_
    rw [mem_span_singleton_iff_mul_eq hsIdem]
    have h := hsplit x (hSN hx)
    have h0 : x * t = 0 := hdisj _ (by
      rw [eq_sub_of_add_eq' h]
      exact S.sub_mem hx (hsS x)) (hsT x)
    rw [h0, add_zero] at h
    exact h
  refine ⟨s, t, hsIdem, htIdem, hs_ss.2, ht_tt.2, hst, hspanS ▸ hS, ?_⟩
  have hle : Submodule.span R {t} ≤ T := (Submodule.span_singleton_le_iff_mem _ _).mpr ht
  refine lt_of_le_of_ne (hle.trans hTN) fun heq => ?_
  have hSbot : S = ⊥ := by
    rw [← inf_eq_left.mpr (hSN.trans (heq.symm.le.trans hle)), hST]
  exact (isSimpleModule_iff_isAtom.mp hS).1 hSbot

end DG
