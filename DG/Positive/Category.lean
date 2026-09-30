import DG.Category.Positive
import DG.Category.SingleObj
import DG.Positive.Basic
import DG.Positive.Idempotent
import Mathlib.RingTheory.FiniteLength

/-!
# Positive dg rings as positive one-object dg categories

For a dg ring `A`, the one-object dg category `SingleObj A` is positive in the sense of
`DG.DGCategory.IsPositive` iff `A` is positive in the sense of Schnürer (`DG.IsPositive A`):
`DG.SingleObj.isPositive_iff`. The degree-`0` category of `SingleObj A` is the ring `A⁰`; a
degree-`0` idempotent `e` is simple in the categorical sense
(`DG.DGCategory.Idempotent.IsSimple`) iff the left ideal `A⁰ e` is a simple `A⁰`-module
(`DG.SingleObj.idempotent_isSimple_iff`), and `𝟙 = 1` decomposes into pairwise orthogonal simple
idempotents iff `A⁰` is a semisimple ring.

* `DG.exists_list_sum_eq_of_isSemisimpleRing`: in a semisimple ring, every idempotent `g` is the
  sum of a list of pairwise orthogonal idempotents `s` with `R s` simple (and `s g = s = g s`).
-/

open CategoryTheory

namespace DG

section Ring

variable {R : Type*} [Ring R]

/-- In a semisimple ring, every idempotent `g` is the sum of a list of pairwise orthogonal
idempotents `s` with `R s` simple, all satisfying `s g = s = g s`. -/
theorem exists_list_sum_eq_of_isSemisimpleRing [IsSemisimpleRing R] {g : R}
    (hg : IsIdempotentElem g) :
    ∃ l : List R, (∀ s ∈ l, IsIdempotentElem s ∧ IsSimpleModule R (Submodule.span R {s}) ∧
      s * g = s ∧ g * s = s) ∧ l.Pairwise (fun a b => a * b = 0 ∧ b * a = 0) ∧ l.sum = g := by
  have : IsArtinianRing R := inferInstance
  suffices H : ∀ N : Submodule R R, ∀ g : R, IsIdempotentElem g → Submodule.span R {g} = N →
      ∃ l : List R, (∀ s ∈ l, IsIdempotentElem s ∧ IsSimpleModule R (Submodule.span R {s}) ∧
        s * g = s ∧ g * s = s) ∧ l.Pairwise (fun a b => a * b = 0 ∧ b * a = 0) ∧ l.sum = g from
    H _ g hg rfl
  intro N
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  intro g hg hN
  by_cases h0 : Submodule.span R {g} = ⊥
  · exact ⟨[], by simp, List.Pairwise.nil, (Submodule.span_singleton_eq_bot.mp h0).symm⟩
  obtain ⟨s, t, hs, ht, hst, hts, hsum, hsimple, hlt⟩ :=
    exists_isSimpleModule_add_of_isSemisimpleRing hg h0
  obtain ⟨l, hl, hlp, hlsum⟩ := ih _ (hN ▸ hlt) t ht rfl
  have hsg : s * g = s := by rw [← hsum, mul_add, hs.eq, hst, add_zero]
  have hgs : g * s = s := by rw [← hsum, add_mul, hs.eq, hts, add_zero]
  refine ⟨s :: l, fun x hx => ?_, List.pairwise_cons.mpr ⟨fun x hx => ?_, hlp⟩, ?_⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hs, hsimple, hsg, hgs⟩
    · obtain ⟨hx1, hx2, hxt, htx⟩ := hl x hx
      have hxs : x * s = 0 := by rw [← hxt, mul_assoc, hts, mul_zero]
      have hsx : s * x = 0 := by rw [← htx, ← mul_assoc, hst, zero_mul]
      exact ⟨hx1, hx2, by rw [← hsum, mul_add, hxs, zero_add, hxt],
        by rw [← hsum, add_mul, hsx, zero_add, htx]⟩
  · obtain ⟨-, -, hxt, htx⟩ := hl x hx
    exact ⟨by rw [← htx, ← mul_assoc, hst, zero_mul], by rw [← hxt, mul_assoc, hts, mul_zero]⟩
  · rw [List.sum_cons, hlsum, hsum]

end Ring

namespace SingleObj

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- A degree-`0` idempotent cocycle of `SingleObj A` as an element of `A⁰`. -/
def idempotentToZero {X : SingleObj A} (e : DGCategory.Idempotent X) : degreeZeroSubring A :=
  ⟨e.val, e.mem_grading⟩

/-- A degree-`0` idempotent cocycle `e` of `SingleObj A` is simple (in the degree-`0` category)
iff `A⁰ e` is a simple left `A⁰`-module. -/
theorem idempotent_isSimple_iff {X : SingleObj A} (e : DGCategory.Idempotent X) :
    e.IsSimple ↔ IsSimpleModule (degreeZeroSubring A)
      (Submodule.span (degreeZeroSubring A) {idempotentToZero e}) := by
  have he : IsIdempotentElem (idempotentToZero e) := Subtype.ext e.comp_self
  rw [isSimpleModule_iff_isAtom]
  constructor
  · rintro ⟨hne, hs⟩
    refine ⟨fun h => hne (congrArg Subtype.val (Submodule.span_singleton_eq_bot.mp h)), ?_⟩
    intro b hb
    by_contra hb0
    obtain ⟨h, hhb, hh0⟩ := b.exists_mem_ne_zero_of_ne_bot hb0
    have hhe : h * idempotentToZero e = h :=
      (mem_span_singleton_iff_mul_eq he).mp (hb.le hhb)
    obtain ⟨g, hg, hge⟩ := hs (Y := X) h.1 h.2 (congrArg Subtype.val hhe)
      (fun h' => hh0 (Subtype.ext h'))
    apply hb.2
    rw [Submodule.span_singleton_le_iff_mem]
    have : idempotentToZero e = (⟨g, hg⟩ : degreeZeroSubring A) • h := Subtype.ext hge.symm
    rw [this]
    exact b.smul_mem _ hhb
  · intro hat
    refine ⟨fun h => hat.1 (by
      rw [Submodule.span_singleton_eq_bot]
      exact Subtype.ext h), ?_⟩
    intro Y h hh0 heh hne
    have hmem : (⟨h, hh0⟩ : degreeZeroSubring A) ∈
        Submodule.span (degreeZeroSubring A) {idempotentToZero e} :=
      (mem_span_singleton_iff_mul_eq he).mpr (Subtype.ext heh)
    have hle := (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
    rcases (hat.le_iff.mp hle) with h' | h'
    · exact absurd (Submodule.span_singleton_eq_bot.mp h') fun h'' =>
        hne (congrArg Subtype.val h'')
    · have : idempotentToZero e ∈ Submodule.span (degreeZeroSubring A)
          {(⟨h, hh0⟩ : degreeZeroSubring A)} := by
        rw [h']
        exact Submodule.mem_span_singleton_self _
      obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp this
      exact ⟨g.1, g.2, congrArg Subtype.val hg⟩

/-- The one-object dg category `SingleObj A` of a dg ring is positive (in the sense of
`DG.DGCategory.IsPositive`) iff `A` is positive in the sense of Schnürer: the degree-`0`
category of `SingleObj A` is semisimple iff `A⁰` is a semisimple ring. -/
theorem isPositive_iff : DGCategory.IsPositive (SingleObj A) ↔ IsPositive A := by
  constructor
  · intro h
    refine ⟨fun n hn => (AddSubgroup.eq_bot_iff_forall _).mpr fun f hf =>
        h.eq_zero_of_neg (X := SingleObj.star A) (Y := SingleObj.star A) hn hf, ?_,
      fun a ha => h.d_eq_zero (X := SingleObj.star A) (Y := SingleObj.star A) ha⟩
    obtain ⟨l, hs, -, hsum⟩ := h.semisimple (SingleObj.star A)
    refine isSemisimpleModule_of_isSemisimpleModule_submodule
      (s := {x | ∃ e ∈ l, idempotentToZero e = x})
      (p := fun x => Submodule.span (degreeZeroSubring A) {x}) ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      have := (idempotent_isSimple_iff e).mp (hs e he)
      infer_instance
    · rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span, Submodule.span_singleton_le_iff_mem]
      have h1 : (1 : degreeZeroSubring A) = (l.map idempotentToZero).sum := by
        apply Subtype.ext
        have := map_list_sum (degreeZeroSubring A).subtype (l.map idempotentToZero)
        rw [List.map_map] at this
        exact (this.trans hsum).symm
      rw [h1]
      refine list_sum_mem fun x hx => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact (Submodule.mem_iSup_of_mem (idempotentToZero e) (Submodule.mem_iSup_of_mem
        ⟨e, he, rfl⟩ (Submodule.mem_span_singleton_self _)))
  · intro hA
    refine ⟨fun hn f hf => ?_, fun X => ?_, fun hf => hA.d_eq_zero_of_mem_zero _ hf⟩
    · have := hA.grading_eq_bot _ hn
      rw [SingleObj.mem_grading_iff, this] at hf
      exact hf
    · have := hA.isSemisimple
      obtain ⟨l, hl, hlp, hlsum⟩ :=
        exists_list_sum_eq_of_isSemisimpleRing (R := degreeZeroSubring A) IsIdempotentElem.one
      let E : ∀ s ∈ l, DGCategory.Idempotent X := fun s hs =>
        { val := (s : A)
          mem_cocycles := ⟨s.2, hA.d_eq_zero_of_mem_zero _ s.2⟩
          comp_self := congrArg Subtype.val (hl s hs).1.eq }
      refine ⟨l.pmap E fun _ h => h, fun e he => ?_, ?_, ?_⟩
      · obtain ⟨s, hs, rfl⟩ := List.mem_pmap.mp he
        rw [idempotent_isSimple_iff]
        exact (hl s hs).2.1
      · rw [List.pairwise_pmap]
        refine hlp.imp_of_mem fun {a b} _ _ hab _ _ => ?_
        exact ⟨congrArg Subtype.val hab.2, congrArg Subtype.val hab.1⟩
      · rw [List.map_pmap]
        change (l.pmap (fun (s : degreeZeroSubring A) (_ : s ∈ l) => (s : A))
          fun _ h => h).sum = (1 : A)
        rw [List.pmap_eq_map]
        have := map_list_sum (degreeZeroSubring A).subtype l
        rw [hlsum] at this
        exact this.symm.trans (map_one _)

end SingleObj

end DG
