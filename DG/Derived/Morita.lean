import DG.Category.Derived.Comparison
import DG.Category.Derived.Morita
import DG.Positive.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Morita theory for an idempotent of a dg ring

Let `A` be a dg ring and `e ∈ A⁰` an idempotent cocycle (`DG.DGIdempotent A`), with corner dg ring
`e A e` (`DG.DGIdempotent.Corner e`). If `e` is *full up to homotopy*,

  `1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`, `s ∈ A⁻¹` (`DG.DGIdempotent.IsFullH0`),

i.e. the class of `e` generates `H⁰(A)` as a two-sided ideal, then the derived categories of
`e A e` and `A` are equivalent (`DG.DGIdempotent.moritaEquivalence : D(e A e) ≌ D(A)`). The
equivalence is the composite of the equivalences `D(e A e) ≌ D(SingleObj (e A e))` and
`D(SingleObj A) ≌ D(A)` of the one-object comparison, Keller's equivalence along the isomorphism
of dg categories `SingleObj (e A e) ≅ P.Corner` (`DG.DGIdempotent.cornerFunctor`), and the Morita
equivalence `D(P.Corner) ≌ D(SingleObj A)` for the family `P = DG.DGIdempotent.family e`
consisting of the single idempotent `e` of `SingleObj A`
(`DG.IdempotentFamily.moritaEquivalence`); each of these is an equivalence of triangulated
categories. Its functor is derived induction along the dg `(A, e A e)`-bimodule `A e`, i.e.
`A e ⊗^L_{eAe} -`, and its inverse is `e A ⊗^L_A - = e (-)`.

The hypothesis holds when `A e A = A` and `A` is non-negatively graded with `d (A⁰) = 0` (for
instance a positive dg ring in the sense of Schnürer), since the degree-`0` projection `A → A⁰` is
then multiplicative (`DG.DGIdempotent.isFullH0_of_one_mem_span`).

## Roadmap 7.3: the literal statement is false; counterexample and repair

*Literal statement.* For a dg algebra `A` and a degree-`0` idempotent `e` with `d e = 0` such that
`A e A = A`, the functors `A e ⊗_{eAe} -` and `e A ⊗_A -` induce `D(e A e) ≃ D(A)`.

*Counterexample.* Over a field `k`, let `V = k x ⊕ k y ⊕ k z` with `|x| = |z| = 0`, `|y| = 1`,
`d x = y`, `d y = d z = 0`, and `A = END_k(V)`, which is `M₃(k)` as a ring. The projection `e` onto
the subcomplex `k x ⊕ k y` along `k z` is a chain map, so `e ∈ Z⁰(A)`, and `A e A = A` since
`M₃(k)` is simple (explicitly `E_{zz} = E_{zx} e E_{xz}`; here `E_{xz}` is not a cocycle). But
`e A e = END(k x ⊕ k y)` is the endomorphism dg algebra of a contractible complex: the contracting
homotopy `h` (`h y = x`) satisfies `d h = e = 1_{eAe}`, so `e A e` is acyclic and `D(e A e) = 0`
(`DG.DerivedCategory.tfae_isZero`). On the other hand `H⁰(A)` is the ring of endomorphisms of `V`
up to homotopy, which is `k` (`V ≃ k z`); in particular `d a = 1` has no solution in `A` (apply
`1 = d a = d_V a + a d_V` to `z`: `z = d_V (a z)` is not a coboundary), so `D(A) ≠ 0`. This is
formalized, over any nontrivial commutative ring, in `DG.Examples.MoritaCounterexample`
(`DG.MoritaCounterexample.isEmpty_derivedEquivalence`, `DG.MoritaCounterexample.not_isFullH0`).

*Repair.* The decomposition `1 = ∑ₖ aₖ e bₖ` must be possible with cocycles `aₖ, bₖ ∈ Z⁰(A)` up to
a coboundary (`DG.DGIdempotent.IsFullH0`); this is the statement proved here. More generally,
`D(e A e) ≌ D(A)` as soon as `M ↦ e M` reflects acyclicity of dg `A`-modules, i.e. `A e` generates
`D(A)` (`DG.DGIdempotent.ReflectsAcyclic`, `DG.DGIdempotent.moritaEquivalenceOfReflects`); for
a family `P` of idempotents in a dg category, `D(P.Corner) ≌ D(C)` holds as soon as restriction
along the embedding `P.inr` of the corner category reflects acyclicity
(`DG.IdempotentFamily.moritaEquivalenceOfReflects`), and this condition is equivalent to `P.inr^*`
being an equivalence (`DG.CatModule.DerivedCategory.restrict_isEquivalence_iff`).

## Main definitions and results

* `DG.DGIdempotent.family`, `DG.DGIdempotent.IsFullH0`, `DG.DGIdempotent.isFullH0_family`,
  `DG.DGIdempotent.isFullH0_of_one_mem_span`.
* `DG.DGIdempotent.cornerFunctor`, `DG.DGIdempotent.isQuasiEquivalence_cornerFunctor`.
* `DG.DGIdempotent.ReflectsAcyclic`, `DG.DGIdempotent.moritaEquivalenceOfReflects`: the general
  form, for `e` such that `M ↦ e M` reflects acyclicity.
* `DG.DGIdempotent.moritaEquivalence : D(e A e) ≌ D(A)`, with triangulated functor
  (`DG.DGIdempotent.moritaEquivalence_functor_isTriangulated`), so that it induces an
  isomorphism of the Grothendieck groups of the compact objects, `K₀(e A e) ≅ K₀(A)`.
-/

open CategoryTheory

universe t w w₁ w₂ u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace DGIdempotent

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (e : DGIdempotent A)

/-- The family of idempotents of `SingleObj A` consisting of `e` alone. -/
def family : IdempotentFamily Unit (SingleObj A) where
  obj _ := SingleObj.star A
  idem _ := (e.val : A)
  idem_mem _ := e.mem_zero
  idem_comp_idem _ := e.mul_self
  d_idem _ := e.d_eq_zero

/-- The idempotent `e` is *full up to homotopy*: `1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ` cocycles of
degree `0`, i.e. the class of `e` generates `H⁰(A)` as a two-sided ideal. -/
def IsFullH0 : Prop :=
  ∃ (n : ℕ) (a b : Fin n → A), (∀ k, a k ∈ cocycles A 0) ∧ (∀ k, b k ∈ cocycles A 0) ∧
    ∑ k, a k * e.val * b k - 1 ∈ coboundaries A 0

omit [DGRing A] in
theorem isFullH0_family (he : e.IsFullH0) : e.family.IsFullH0 := by
  intro _
  obtain ⟨n, a, b, ha, hb, h⟩ := he
  refine ⟨n, fun _ => (), fun k => (b k : A), fun k => (a k : A), hb, ha, ?_⟩
  exact h

/-- If `A` is non-negatively graded with `d (A⁰) = 0` and `A e A = A`, then `e` is full up to
homotopy: the degree-`0` components of a decomposition `1 = ∑ₖ aₖ e bₖ` are cocycles. -/
theorem isFullH0_of_one_mem_span (hneg : ∀ n < 0, grading (M := A) n = ⊥)
    (hd : ∀ a ∈ grading (M := A) 0, d a = 0) (h : (1 : A) ∈ TwoSidedIdeal.span {e.val}) :
    e.IsFullH0 := by
  classical
  let π : A → A := fun a => DirectSum.decompose (grading (M := A)) a 0
  have hπ0 (a : A) : π a ∈ grading (M := A) 0 := (DirectSum.decompose (grading (M := A)) a 0).2
  -- every element of `A e A` is a finite sum `∑ₖ aₖ e bₖ`
  have key : ∀ z ∈ TwoSidedIdeal.span ({e.val} : Set A),
      ∃ (n : ℕ) (a b : Fin n → A), z = ∑ k, a k * e.val * b k := by
    intro z hz
    rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, ⟨a, -, e', he', rfl⟩, b, -, rfl⟩ := hx
      rw [Set.mem_singleton_iff] at he'
      exact ⟨1, fun _ => a, fun _ => b, by simp [he']⟩
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, b, rfl⟩ := hx
      obtain ⟨m, a', b', rfl⟩ := hy
      exact ⟨n + m, Fin.append a a', Fin.append b b', by simp [Fin.sum_univ_add]⟩
    | neg x _ hx =>
      obtain ⟨n, a, b, rfl⟩ := hx
      exact ⟨n, fun k => -a k, b, by simp [Finset.sum_neg_distrib]⟩
  obtain ⟨n, a, b, hab⟩ := key 1 h
  refine ⟨n, fun k => π (a k), fun k => π (b k), fun k => ⟨hπ0 _, hd _ (hπ0 _)⟩,
    fun k => ⟨hπ0 _, hd _ (hπ0 _)⟩, ?_⟩
  have hπmul (x y : A) : π (x * y) = π x * π y := coe_decompose_mul_zero hneg x y
  have hπe : π e.val = e.val := DirectSum.decompose_of_mem_same _ e.mem_zero
  have hπsum : π (∑ k, a k * e.val * b k) = ∑ k, π (a k) * e.val * π (b k) := by
    simp only [π, DirectSum.decompose_sum, DirectSum.sum_apply, AddSubgroup.val_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change π (a k * e.val * b k) = _
    rw [hπmul, hπmul, hπe]
  have hπ1 : π 1 = 1 := DirectSum.decompose_of_mem_same _ one_mem_grading
  rw [← hπsum, ← hab, hπ1, sub_self]
  exact zero_mem _

/-! ### The one-object comparison is triangulated -/

section SingleObj

variable (B : Type*) [Ring B] [DGAddCommGroup B] [DGRing B]
  [CatModule.HasDerivedCategory.{w₁, t} (SingleObj B)] [DG.HasDerivedCategory.{w₂, t} B]

noncomputable instance _root_.DG.CatModule.DerivedCategory.singleObjEquivalence_functor_commShift :
    (CatModule.DerivedCategory.singleObjEquivalence B).functor.CommShift ℤ :=
  inferInstanceAs ((CatModule.DerivedCategory.toDGDerivedCategory B).CommShift ℤ)

instance _root_.DG.CatModule.DerivedCategory.singleObjEquivalence_functor_isTriangulated :
    (CatModule.DerivedCategory.singleObjEquivalence B).functor.IsTriangulated :=
  inferInstanceAs (CatModule.DerivedCategory.toDGDerivedCategory B).IsTriangulated

end SingleObj

/-! ### The corner dg category of `e` and the one-object dg category of `e A e` -/

/-- The dg functor `SingleObj (e A e) ⥤ P.Corner` (for `P = e.family`), `x ↦ x`; it is an
isomorphism of dg categories. -/
def cornerFunctor : SingleObj e.Corner ⥤ e.family.Corner where
  obj _ := ⟨()⟩
  map x := ⟨((show e.Corner from x) : A), Corner.coe_mul_val e x, Corner.val_mul_coe e x⟩
  map_id _ := rfl
  map_comp _ _ := rfl

omit [DGRing A] in
@[simp]
theorem cornerFunctor_map_val {X Y : SingleObj e.Corner} (x : X ⟶ Y) :
    (e.cornerFunctor.map x).1 = ((show e.Corner from x) : A) :=
  rfl

instance : e.cornerFunctor.Additive where
  map_add := IdempotentFamily.hom_ext rfl

instance : e.cornerFunctor.IsDGFunctor where
  map_mem' hf := IdempotentFamily.mem_grading_iff.mpr ((Corner.mem_grading_iff e).mp hf)
  map_d' _ := IdempotentFamily.hom_ext rfl

omit [DGRing A] in
theorem cornerFunctor_map_bijective (X Y : SingleObj e.Corner) :
    Function.Bijective (e.cornerFunctor.map : (X ⟶ Y) → _) := by
  refine ⟨fun x y h => ?_, fun f => ?_⟩
  · have h' := congrArg Subtype.val h
    exact Corner.coe_injective e h'
  refine ⟨show e.Corner from ⟨f.1, (Corner.mem_iff e).mpr ⟨f.2.2, f.2.1⟩⟩, ?_⟩
  exact IdempotentFamily.hom_ext rfl

/-- The dg functor `SingleObj (e A e) ⥤ P.Corner` is a quasi-equivalence. -/
theorem isQuasiEquivalence_cornerFunctor : IsQuasiEquivalence e.cornerFunctor where
  toIsQuasiFullyFaithful := IsQuasiFullyFaithful.of_bijective _ e.cornerFunctor_map_bijective
    fun hf => (Corner.mem_grading_iff e).mpr (IdempotentFamily.mem_grading_iff.mp hf)
  exists_iso := by
    rintro ⟨⟨⟩⟩
    refine ⟨SingleObj.star _, 𝟙 _, 𝟙 _, id_mem_cocycles _, id_mem_cocycles _, ?_, ?_⟩ <;>
    · rw [Category.id_comp, sub_self]
      exact zero_mem _

/-! ### Reflection of acyclicity by `M ↦ e M` -/

/-- The functor `M ↦ e M` reflects acyclicity of dg modules over `SingleObj A` (i.e. of dg
`A`-modules) with values in `Type w`: if every cocycle `m = e m` of `M` is the differential of
some `m' = e m'`, then `M` is acyclic. Equivalently, `A e` generates `D(A)`. -/
def ReflectsAcyclic : Prop :=
  ∀ M : CatModule.{w} (SingleObj A),
    (∀ (n : ℤ) (m : M.obj (SingleObj.star A)), m ∈ grading n → d m = 0 →
      (show SingleObj.star A ⟶ SingleObj.star A from e.val) • m = m →
        ∃ m' ∈ grading (n - 1), (show SingleObj.star A ⟶ SingleObj.star A from e.val) • m' = m' ∧
          d m' = m) → CatModule.IsAcyclic M

/-- If `M ↦ e M` reflects acyclicity, then so does restriction along the embedding
`P.inr : P.Corner ⥤ P.augment.Corner` of the corner of `P = e.family`. -/
theorem isAcyclic_of_isAcyclic_precomp_inr_of_reflectsAcyclic (h : e.ReflectsAcyclic.{w})
    {N : CatModule.{w} e.family.augment.Corner}
    (hN : CatModule.IsAcyclic ((CatModule.precomp e.family.inr).obj N)) :
    CatModule.IsAcyclic N := by
  unfold ReflectsAcyclic at h
  rintro ⟨X | i⟩
  · -- the object `(A, 1)`: the `e`-part of `N(A, 1)` is a retract of `N(A, e)`
    let S : e.family.augment.Corner := ⟨.inl (SingleObj.star A)⟩
    let a : S ⟶ ⟨.inr ()⟩ := ⟨(e.val : A), Category.id_comp _, e.mul_self⟩
    let b : (⟨.inr ()⟩ : e.family.augment.Corner) ⟶ S :=
      ⟨(e.val : A), e.mul_self, Category.comp_id _⟩
    let ee : S ⟶ S := e.family.inl.map (show SingleObj.star A ⟶ SingleObj.star A from e.val)
    have hab : a ≫ b = ee := IdempotentFamily.hom_ext e.mul_self
    have hbe : b ≫ ee = b := IdempotentFamily.hom_ext e.mul_self
    have ha0 : a ∈ grading 0 := e.mem_zero
    have hb0 : b ∈ grading 0 := e.mem_zero
    have hda : d a = 0 := IdempotentFamily.hom_ext e.d_eq_zero
    have hdb : d b = 0 := IdempotentFamily.hom_ext e.d_eq_zero
    refine h ((CatModule.precomp e.family.inl).obj N) (fun n m hm hdm hem => ?_) X
    let m₀ : N.obj S := m
    have hm₀ : m₀ ∈ grading n := hm
    have hdm₀ : d m₀ = 0 := hdm
    have hdam : d (a • m₀) = 0 := by
      rw [CatModule.d_smul ha0, hda, hdm₀]
      simp
    obtain ⟨z, hz, hdz⟩ : ∃ z : N.obj ⟨.inr ()⟩, z ∈ grading (n - 1) ∧ d z = a • m₀ :=
      DG.isAcyclic_iff.mp (hN ⟨()⟩) n (a • m₀)
        (by simpa using CatModule.smul_mem_grading ha0 hm₀) hdam
    refine ⟨b • z, by simpa using CatModule.smul_mem_grading hb0 hz, ?_, ?_⟩
    · change ee • (b • z) = b • z
      rw [← CatModule.comp_smul, hbe]
    · change d (b • z) = m₀
      rw [CatModule.d_smul hb0, hdb, CatModule.zero_smul, zero_add, koszulSign_zero, one_smul,
        hdz, ← CatModule.comp_smul, hab]
      exact hem
  · exact hN ⟨i⟩

/-! ### The Morita equivalence -/

section

omit [DGRing A]

open Limits Pretriangulated in
/-- The composite of two equivalences with triangulated functors has a triangulated functor. -/
theorem _root_.DG.isTriangulated_trans_functor {C : Type*} {D : Type*} {E : Type*}
    [Category C] [Category D] [Category E] [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
    [Preadditive C] [Preadditive D] [Preadditive E] [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated C] [Pretriangulated D]
    [Pretriangulated E] (F : C ≌ D) (G : D ≌ E) [F.functor.CommShift ℤ] [G.functor.CommShift ℤ]
    (hF : F.functor.IsTriangulated) (hG : G.functor.IsTriangulated) :
    (F.trans G).functor.IsTriangulated :=
  inferInstanceAs (F.functor ⋙ G.functor).IsTriangulated

end

variable [DG.HasDerivedCategory.{w₁, max u t} e.Corner] [DG.HasDerivedCategory.{w₂, max u t} A]

/-- **Morita theory for an idempotent of a dg ring.** For a degree-`0` idempotent cocycle `e` of a
dg ring `A` which is full up to homotopy (`1 = ∑ₖ aₖ e bₖ + d s` with `aₖ, bₖ ∈ Z⁰(A)`), the
derived categories of `e A e` and `A` are equivalent. The equivalence is a composite of
triangulated equivalences; its functor is `A e ⊗^L_{eAe} -` and its inverse `e A ⊗^L_A -`.
The hypothesis cannot be weakened to `A e A = A` (see the module docstring). -/
noncomputable def moritaEquivalence (he : e.IsFullH0) :
    DG.DerivedCategory e.Corner ≌ DG.DerivedCategory A :=
  letI := CatModule.HasDerivedCategory.small.{max u t} (SingleObj e.Corner)
  letI := CatModule.HasDerivedCategory.small.{t} e.family.Corner
  letI := CatModule.HasDerivedCategory.small.{t} (SingleObj A)
  letI := CatModule.HasDerivedCategory.small.{t} e.family.augment.Corner
  (CatModule.DerivedCategory.singleObjEquivalence e.Corner).symm.trans
    ((CatModule.DerivedCategory.kellerEquivalence.{t} e.isQuasiEquivalence_cornerFunctor).trans
      ((e.family.moritaEquivalence.{t} (e.isFullH0_family he)).trans
        (CatModule.DerivedCategory.singleObjEquivalence A)))

/-- **Morita theory for an idempotent of a dg ring** (general form). If `M ↦ e M` reflects
acyclicity of dg `A`-modules (i.e. `A e` generates `D(A)`), then `D(e A e) ≌ D(A)`. -/
noncomputable def moritaEquivalenceOfReflects (h : e.ReflectsAcyclic.{max u t}) :
    DG.DerivedCategory e.Corner ≌ DG.DerivedCategory A :=
  letI := CatModule.HasDerivedCategory.small.{max u t} (SingleObj e.Corner)
  letI := CatModule.HasDerivedCategory.small.{t} e.family.Corner
  letI := CatModule.HasDerivedCategory.small.{t} (SingleObj A)
  letI := CatModule.HasDerivedCategory.small.{t} e.family.augment.Corner
  (CatModule.DerivedCategory.singleObjEquivalence e.Corner).symm.trans
    ((CatModule.DerivedCategory.kellerEquivalence.{t} e.isQuasiEquivalence_cornerFunctor).trans
      ((e.family.moritaEquivalenceOfReflects.{t}
          fun _ => e.isAcyclic_of_isAcyclic_precomp_inr_of_reflectsAcyclic h).trans
        (CatModule.DerivedCategory.singleObjEquivalence A)))

/-- The functor of the Morita equivalence `D(e A e) ≌ D(A)` commutes with the shifts. -/
noncomputable instance moritaEquivalence_functor_commShift (he : e.IsFullH0) :
    (e.moritaEquivalence.{t} he).functor.CommShift ℤ := by
  letI := CatModule.HasDerivedCategory.small.{max u t} (SingleObj e.Corner)
  letI := (CatModule.DerivedCategory.singleObjEquivalence e.Corner).commShiftInverse ℤ
  unfold moritaEquivalence
  infer_instance

/-- The functor of the Morita equivalence `D(e A e) ≌ D(A)` is triangulated. -/
instance moritaEquivalence_functor_isTriangulated (he : e.IsFullH0) :
    (e.moritaEquivalence.{t} he).functor.IsTriangulated := by
  let := CatModule.HasDerivedCategory.small.{max u t} (SingleObj e.Corner)
  let := (CatModule.DerivedCategory.singleObjEquivalence e.Corner).commShiftInverse ℤ
  have := (CatModule.DerivedCategory.singleObjEquivalence e.Corner).commShift_of_functor ℤ
  have : (CatModule.DerivedCategory.singleObjEquivalence e.Corner).IsTriangulated :=
    Equivalence.IsTriangulated.mk' _ inferInstance
  unfold moritaEquivalence
  exact isTriangulated_trans_functor _ _
    (inferInstanceAs
      (CatModule.DerivedCategory.singleObjEquivalence e.Corner).inverse.IsTriangulated)
    (isTriangulated_trans_functor _ _ inferInstance
      (isTriangulated_trans_functor _ _ inferInstance inferInstance))

end DGIdempotent

end DG
