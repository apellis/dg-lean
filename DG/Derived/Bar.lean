import DG.Derived.Resolution
import DG.Module.TensorProduct

/-!
# The bar resolution

Let `A` be a dg ring (a dg algebra over the ground ring `ℤ`) and `M` a left dg `A`-module. This
file constructs the unnormalized two-sided bar construction

`Bar(A, M) = ⨁_{n ≥ 0} A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M`

(all tensor products over `ℤ`, `DG.Module.TensorProduct`), a dg `A`-module with `A` acting on
the first factor, together with the augmentation `Bar(A, M) → M`, `a₀ [ ] m ↦ a₀ m`, and shows
that the augmentation is a surjective quasi-isomorphism, whose underlying map of dg abelian groups
is a homotopy equivalence. Elements of `A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M` are written
`a₀ [a₁ | ⋯ | aₙ] m = a₀ ⊗ (s a₁ ⊗ (⋯ ⊗ (s aₙ ⊗ m)))`, where `s a = Shift.mk 1 a` has degree
`|a| - 1`.

## Construction and signs

The levels `T n = (A⟦1⟧)^{⊗ n} ⊗ M` are defined recursively, `T 0 = M`, `T (n + 1) = A⟦1⟧ ⊗ T n`
(`DG.Bar.level`), each with a non-unital "action" `βₙ : A ⊗ T n → T n` of degree `0`
(`DG.Bar.IsAction`: a chain map, associative in the sense `β (a ⊗ β (a' ⊗ x)) = β (a a' ⊗ x)`):
`β₀ (a ⊗ m) = a m` (`DG.Bar.act`) and (`DG.Bar.stepHom`)

`βₙ₊₁ (a₀ ⊗ (s a₁ ⊗ x)) = (-1)^{|a₀|} (s (a₀ a₁) ⊗ x - s a₀ ⊗ βₙ (a₁ ⊗ x))`.

The `n`-th term of `Bar(A, M)` is `A ⊗ T n` with the tensor product differential (the internal
differential; `d_{A⟦1⟧} = -d_A`), and the bar differential `b : A ⊗ T (n + 1) → A ⊗ T n` is
`b = s⁻¹ ∘ βₙ₊₁` (`DG.Bar.barComp`), with `s⁻¹ (s a ⊗ x) = a ⊗ x` (`DG.Bar.desusp`). Unwinding
the recursion,

`b (a₀ [a₁ | ⋯ | aₙ] m) = ∑_{i < n} (-1)^{i + |a₀| + ⋯ + |aᵢ|} a₀ [a₁ | ⋯ | aᵢ aᵢ₊₁ | ⋯ | aₙ] m
  + (-1)^{n + |a₀| + ⋯ + |aₙ₋₁|} a₀ [a₁ | ⋯ | aₙ₋₁] aₙ m`,

i.e. the `i`-th term carries the Koszul sign `(-1)^{|a₀| + |s a₁| + ⋯ + |s aᵢ|}` of moving the
degree-`1` operator past `a₀, s a₁, …, s aᵢ`. The total differential is `d + b`; `d² = 0`
follows from `βₙ` being a chain map (`d b + b d = 0`) and associative (`b² = 0`, and
`ε ∘ b = 0` for the augmentation `ε = β₀` on `A ⊗ M`). The signs are the ones forced by the
contracting homotopy `h (a₀ [a₁ | ⋯ | aₙ] m) = 1 [a₀ | a₁ | ⋯ | aₙ] m` (`DG.Bar.homotopy`), which
satisfies `d h + h d = 1 - η ε` with `η m = 1 [ ] m` (`DG.Bar.d_homotopy_add_homotopy_d`); `h`
and `η` are additive but not `A`-linear. This is the standard bar resolution, e.g.
[Félix–Halperin–Thomas, *Rational homotopy theory*, §19] (there normalized, over a field).

## Main definitions and results

* `DG.Bar A M`: the bar construction, with `DG.Bar.instDGAddCommGroup` (total differential) and
  `DG.Bar.instDGModule` (`Bar(A, M)` is a dg `A`-module).
* `DG.Bar.augmentation A M : Bar A M →ᵈᵍ[A] M`, `DG.Bar.surjective_augmentation`,
  `DG.Bar.isQuasiIso_augmentation`, via `DG.DGModuleHom.isQuasiIso_of_contraction`.
* The filtration by the number of bars `DG.Bar.filtration A M n = ⨁_{k < n} A ⊗ T k`, whose
  inclusions are graded-split with subquotients `A ⊗ T n` (`DG.Bar.gradedSplitting`).
* `DG.IsKProjective.of_filtration`, `DG.IsGradedProjective.of_filtration`: exhaustive
  filtrations with graded-split steps and K-projective (graded-projective) subquotients.
* `DG.Bar.isKProjective`, `DG.Bar.hasLiftingProperty`: `Bar(A, M)` is K-projective (resp. has
  the lifting property against surjective quasi-isomorphisms) when every term `A ⊗ T n` is.
* `DG.Bar.semiFreeFiltration`, `DG.Bar.semiFreeResolution`: when every term `A ⊗ T n` is
  isomorphic to a direct sum of shifts of `A` (e.g. when each `T n` is free on homogeneous
  cocycles), the filtration by the number of bars is semi-free and `Bar(A, M) → M` is a
  semi-free resolution.
* `DG.Bar.exists_dgHomotopyEquiv_semiFreeResolution`: under the lifting-property hypothesis,
  `Bar(A, M)` is homotopy equivalent over `M` to the resolution `DG.semiFreeResolution A M`.

## Remarks

The ground ring is `ℤ`: the tensor products of dg abelian groups in the library are over `ℤ`.
The bar construction over a general commutative ground ring `R` (tensor products over `R`) is not
treated here. The filtration by the number of bars is not a semi-free filtration in general:
its subquotient `A ⊗ T n` carries the differential of `T n`, and is a direct sum of shifts of `A`
as a dg module only when `T n` is (up to isomorphism) free on cocycles, e.g. when `A` and `M` have
zero differential and are free graded abelian groups. For `A` and `M` free as graded abelian
groups but with nonzero differentials, `Bar(A, M)` is still cofibrant, but proving it requires
that complexes of free abelian groups are K-projective, which is not formalized here.

The levels are bundled (`DG.Bar.Level`) so that `T (n + 1)` is definitionally `A⟦1⟧ ⊗ T n`;
`A` and `M` live in the same universe.

## References

* [Y. Félix, S. Halperin, J.-C. Thomas, *Rational homotopy theory*, GTM 205 (2001), §19]
* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994), §3]
-/

open DirectSum TensorProduct

noncomputable section

namespace DG

namespace Bar

section Step

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {X : Type*} [AddCommGroup X] [DGAddCommGroup X]

/-- `(-1)^{n + 1} = -(-1)^n`. -/
theorem koszulSign_add_one (n : ℤ) : koszulSign (n + 1) = -koszulSign n :=
  Int.negOnePow_succ n

theorem koszulSign_sub_one (n : ℤ) : koszulSign (n - 1) = -koszulSign n := by
  rw [koszulSign, Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one]

theorem koszulSign_one : koszulSign 1 = -1 := Int.negOnePow_one

/-- The additive map `A ⊗ A⟦1⟧ → A⟦1⟧`, `a ⊗ s b ↦ s (a b)`. -/
def mulShift : A ⊗[ℤ] Shift 1 A →+ Shift 1 A :=
  TensorProduct.liftAddHom
    (((AddMonoidHom.mul : A →+ A →+ A).compr₂ (Shift.mk 1 : A ≃+ Shift 1 A).toAddMonoidHom).compl₂
      (Shift.unmk 1 : Shift 1 A ≃+ A).toAddMonoidHom)
    fun r a b => by
      simp only [AddMonoidHom.compl₂_apply, AddMonoidHom.compr₂_apply, AddMonoidHom.mul_apply,
        AddEquiv.coe_toAddMonoidHom, smul_mul_assoc, Shift.unmk_zsmul, mul_smul_comm]

omit [DGAddCommGroup A] [DGRing A] in
theorem mulShift_tmul (a b : A) :
    mulShift (a ⊗ₜ[ℤ] Shift.mk 1 b) = Shift.mk 1 (a * b) := rfl

variable (A X) in
/-- The suspension `A ⊗ X → A⟦1⟧ ⊗ X`, `a ⊗ x ↦ s a ⊗ x` (of degree `-1`, no sign). -/
def susp : A ⊗[ℤ] X →+ Shift 1 A ⊗[ℤ] X :=
  tensorMap (Shift.mk 1 : A ≃+ Shift 1 A).toAddMonoidHom (AddMonoidHom.id X)

variable (A X) in
/-- The desuspension `A⟦1⟧ ⊗ X → A ⊗ X`, `s a ⊗ x ↦ a ⊗ x`, inverse to `DG.Bar.susp`. -/
def desusp : Shift 1 A ⊗[ℤ] X →+ A ⊗[ℤ] X :=
  tensorMap (Shift.unmk 1 : Shift 1 A ≃+ A).toAddMonoidHom (AddMonoidHom.id X)

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup X] in
@[simp]
theorem susp_tmul (a : A) (x : X) : susp A X (a ⊗ₜ x) = Shift.mk 1 a ⊗ₜ x := rfl

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup X] in
@[simp]
theorem desusp_tmul (a : A) (x : X) : desusp A X (Shift.mk 1 a ⊗ₜ x) = a ⊗ₜ x := rfl

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup X] in
@[simp]
theorem desusp_susp (y : A ⊗[ℤ] X) : desusp A X (susp A X y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup X] in
@[simp]
theorem susp_desusp (y : Shift 1 A ⊗[ℤ] X) : susp A X (desusp A X y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']

/-- The auxiliary map of `DG.Bar.stepHom` before the sign:
`a₀ ⊗ (s a₁ ⊗ x) ↦ s (a₀ a₁) ⊗ x - s a₀ ⊗ f (a₁ ⊗ x)`. -/
def stepHomAux (f : A ⊗[ℤ] X →+ X) : A ⊗[ℤ] (Shift 1 A ⊗[ℤ] X) →+ Shift 1 A ⊗[ℤ] X :=
  (tensorMap mulShift (AddMonoidHom.id X)).comp
      (TensorProduct.assoc ℤ A (Shift 1 A) X).symm.toLinearMap.toAddMonoidHom -
    tensorMap (Shift.mk 1 : A ≃+ Shift 1 A).toAddMonoidHom (f.comp (desusp A X))

/-- The recursion step of the bar construction: from `f : A ⊗ X → X` the map
`A ⊗ (A⟦1⟧ ⊗ X) → A⟦1⟧ ⊗ X`,
`a₀ ⊗ (s a₁ ⊗ x) ↦ (-1)^{|a₀|} (s (a₀ a₁) ⊗ x - s a₀ ⊗ f (a₁ ⊗ x))`. -/
def stepHom (f : A ⊗[ℤ] X →+ X) : A ⊗[ℤ] (Shift 1 A ⊗[ℤ] X) →+ Shift 1 A ⊗[ℤ] X :=
  (stepHomAux f).comp (tensorMap (gradeInvolution A) (AddMonoidHom.id _))

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup X] in
theorem stepHomAux_tmul (f : A ⊗[ℤ] X →+ X) (a₀ a₁ : A) (x : X) :
    stepHomAux f (a₀ ⊗ₜ (Shift.mk 1 a₁ ⊗ₜ x)) =
      Shift.mk 1 (a₀ * a₁) ⊗ₜ x - Shift.mk 1 a₀ ⊗ₜ f (a₁ ⊗ₜ x) := rfl

omit [DGRing A] [DGAddCommGroup X] in
theorem stepHom_tmul_eq (f : A ⊗[ℤ] X →+ X) {i : ℤ} {a₀ : A} (ha₀ : a₀ ∈ grading i)
    (y : Shift 1 A ⊗[ℤ] X) : stepHom f (a₀ ⊗ₜ y) = koszulSign i • stepHomAux f (a₀ ⊗ₜ y) := by
  rw [stepHom, AddMonoidHom.comp_apply, tensorMap_tmul, gradeInvolution_of_mem ha₀,
    AddMonoidHom.id_apply, Units.smul_def, Units.smul_def, ← smul_tmul', map_zsmul]

omit [DGRing A] [DGAddCommGroup X] in
theorem stepHom_tmul (f : A ⊗[ℤ] X →+ X) {i : ℤ} {a₀ : A} (ha₀ : a₀ ∈ grading i) (a₁ : A)
    (x : X) : stepHom f (a₀ ⊗ₜ (Shift.mk 1 a₁ ⊗ₜ x)) =
      koszulSign i • (Shift.mk 1 (a₀ * a₁) ⊗ₜ x - Shift.mk 1 a₀ ⊗ₜ f (a₁ ⊗ₜ x)) := by
  rw [stepHom_tmul_eq f ha₀, stepHomAux_tmul]

omit [DGRing A] in
/-- Induction principle for `A ⊗ (A⟦1⟧ ⊗ X)` on tensors `a₀ ⊗ (s a₁ ⊗ x)` of homogeneous
elements. -/
theorem induction_on₃ {P : A ⊗[ℤ] (Shift 1 A ⊗[ℤ] X) → Prop} (y : A ⊗[ℤ] (Shift 1 A ⊗[ℤ] X))
    (zero : P 0)
    (tmul : ∀ {i j l : ℤ} {a₀ a₁ : A} {x : X}, a₀ ∈ grading i → a₁ ∈ grading j →
      x ∈ grading l → P (a₀ ⊗ₜ (Shift.mk 1 a₁ ⊗ₜ x)))
    (add : ∀ y y', P y → P y' → P (y + y')) : P y := by
  induction y using TensorProduct.induction_on with
  | zero => exact zero
  | add y y' hy hy' => exact add y y' hy hy'
  | tmul a₀ z =>
    induction z using tensor_induction_on with
    | zero => simpa using zero
    | add z z' hz hz' => rw [tmul_add]; exact add _ _ hz hz'
    | tmul s x =>
      induction a₀ using induction_on with
      | h_zero => simpa using zero
      | h_add a a' ha ha' => rw [add_tmul]; exact add _ _ ha ha'
      | h_homogeneous a₀ => exact tmul a₀.2 (Shift.unmk_mem_grading s.2) x.2

variable (A X) in
/-- A (non-unital) graded action `f : A ⊗ X → X`: of degree `0`, a chain map, and associative,
`f (a ⊗ f (a' ⊗ x)) = f (a a' ⊗ x)`. -/
structure IsAction (f : A ⊗[ℤ] X →+ X) : Prop where
  mem : ∀ {i j : ℤ} {a : A} {x : X}, a ∈ grading i → x ∈ grading j →
    f (a ⊗ₜ x) ∈ grading (i + j)
  map_d : ∀ y, f (d y) = d (f y)
  assoc : ∀ (a a' : A) (x : X), f (a ⊗ₜ f (a' ⊗ₜ x)) = f ((a * a') ⊗ₜ x)

theorem IsAction.step_d {f : A ⊗[ℤ] X →+ X} (hf : IsAction A X f)
    (y : A ⊗[ℤ] (Shift 1 A ⊗[ℤ] X)) : stepHom f (d y) = d (stepHom f y) := by
  induction y using induction_on₃ with
  | zero => simp
  | add y y' hy hy' => rw [d_add, map_add, hy, hy', map_add, d_add]
  | @tmul i j l a₀ a₁ x ha₀ ha₁ hx =>
    have hs : Shift.mk 1 a₁ ∈ grading (j - 1) := Shift.mk_mem_grading ha₁
    have hs0 : Shift.mk 1 (a₀ * a₁) ∈ grading (i + j - 1) :=
      Shift.mk_mem_grading (mul_mem_grading ha₀ ha₁)
    have hs1 : Shift.mk 1 a₀ ∈ grading (i - 1) := Shift.mk_mem_grading ha₀
    have hfd := hf.map_d (a₁ ⊗ₜ x)
    rw [d_tmul_of_mem ha₁] at hfd
    rw [d_tmul_of_mem ha₀, d_tmul_of_mem hs, stepHom_tmul f ha₀, map_add,
      stepHom_tmul f (d_mem ha₀),
      Shift.d_mk, d_units_smul, d_sub, d_tmul_of_mem hs0, d_tmul_of_mem hs1, Shift.d_mk,
      Shift.d_mk, d_mul ha₀, ← hfd]
    simp only [Units.smul_def, tmul_add, tmul_smul, ← smul_tmul', map_add, map_zsmul,
      Shift.mk_zsmul, mul_smul_comm, Shift.mk_add, add_tmul, stepHom_tmul f ha₀, smul_add, smul_sub]
    simp only [smul_smul, koszulSign_add_one, koszulSign_sub_one, koszulSign_add, koszulSign_one]
    rcases Int.units_eq_one_or (koszulSign i) with hi | hi <;>
    rcases Int.units_eq_one_or (koszulSign j) with hj | hj <;>
    simp only [hi, hj, Units.val_one, Units.val_neg, Units.val_mul, one_smul, neg_smul, mul_one,
      one_mul, mul_neg, neg_mul, neg_neg] <;> abel

theorem IsAction.step_mem {f : A ⊗[ℤ] X →+ X} (hf : IsAction A X f) {i k : ℤ} {a : A}
    {y : Shift 1 A ⊗[ℤ] X} (ha : a ∈ grading i) (hy : y ∈ grading k) :
    stepHom f (a ⊗ₜ y) ∈ grading (i + k) := by
  have h := map_mem_grading_of_tmul ((stepHom f).comp (tmulAddHom A _ a)) i
    (fun {j l s x} hs hx => by
      obtain ⟨a₁, rfl⟩ := Shift.mk_surjective s
      have ha₁ : a₁ ∈ grading (j + 1) := Shift.unmk_mem_grading hs
      rw [AddMonoidHom.comp_apply, tmulAddHom_apply, stepHom_tmul f ha, Units.smul_def]
      refine zsmul_mem (sub_mem ?_ ?_) _
      · have := tmul_mem_grading (Shift.mk_mem_grading (n := 1) (mul_mem_grading ha ha₁)) hx
        convert this using 2; ring
      · have := tmul_mem_grading (Shift.mk_mem_grading (n := 1) ha) (hf.mem ha₁ hx)
        convert this using 2; ring) hy
  rwa [add_comm k i] at h

theorem IsAction.step_assoc {f : A ⊗[ℤ] X →+ X} (hf : IsAction A X f) (a a' : A)
    (z : Shift 1 A ⊗[ℤ] X) : stepHom f (a ⊗ₜ stepHom f (a' ⊗ₜ z)) = stepHom f ((a * a') ⊗ₜ z) := by
  induction a using induction_on with
  | h_zero => simp
  | h_add a b ha hb => rw [add_tmul, map_add, ha, hb, add_mul, add_tmul, map_add]
  | h_homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i i
    induction a' using induction_on with
    | h_zero => simp
    | h_add a' b ha' hb => rw [add_tmul, map_add, tmul_add, map_add, ha', hb, mul_add, add_tmul,
        map_add]
    | h_homogeneous a' =>
      obtain ⟨a', ha'⟩ := a'
      rename_i i'
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => rw [tmul_add, map_add, tmul_add, map_add, hz, hz', tmul_add, map_add]
      | tmul s x =>
        obtain ⟨a₁, rfl⟩ := Shift.mk_surjective s
        simp only [stepHom_tmul f ha', stepHom_tmul f (mul_mem_grading ha ha'), Units.smul_def,
          tmul_smul, tmul_sub, map_zsmul, map_sub, stepHom_tmul f ha, hf.assoc, mul_assoc,
          smul_sub, smul_smul, koszulSign_add]
        rw [mul_comm (koszulSign i' : ℤ), Units.val_mul]
        abel

/-- The recursion step preserves actions. -/
theorem IsAction.step {f : A ⊗[ℤ] X →+ X} (hf : IsAction A X f) :
    IsAction A (Shift 1 A ⊗[ℤ] X) (stepHom f) where
  mem ha hy := hf.step_mem ha hy
  map_d := hf.step_d
  assoc := hf.step_assoc

/-- The desuspension of `stepHom f` is `A`-linear of degree `1`:
`s⁻¹ (stepHom f (a • y)) = (-1)^{|a|} a • s⁻¹ (stepHom f y)`. -/
theorem desusp_stepHom_smul (f : A ⊗[ℤ] X →+ X) {i : ℤ} {a : A} (ha : a ∈ grading i)
    (y : A ⊗[ℤ] (Shift 1 A ⊗[ℤ] X)) :
    desusp A X (stepHom f (a • y)) = koszulSign i • (a • desusp A X (stepHom f y)) := by
  induction y using induction_on₃ with
  | zero => simp
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', map_add, map_add, smul_add,
      smul_add]
  | @tmul i₀ j l a₀ a₁ x ha₀ _ _ =>
    rw [smul_tmul', smul_eq_mul, stepHom_tmul f (mul_mem_grading ha ha₀), stepHom_tmul f ha₀]
    simp only [Units.smul_def, map_zsmul, map_sub, desusp_tmul, smul_sub, smul_comm a (_ : ℤ),
      smul_smul, koszulSign_add, Units.val_mul]
    simp only [smul_tmul', smul_eq_mul, mul_assoc]

omit [DGRing A] in
/-- For an associative `f`, `f ∘ s⁻¹ ∘ stepHom f = 0`: the square of the bar differential
vanishes. -/
theorem IsAction.apply_desusp_stepHom {f : A ⊗[ℤ] X →+ X} (hf : IsAction A X f)
    (y : A ⊗[ℤ] (Shift 1 A ⊗[ℤ] X)) : f (desusp A X (stepHom f y)) = 0 := by
  induction y using induction_on₃ with
  | zero => simp
  | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy', add_zero]
  | tmul ha₀ _ _ =>
    rw [stepHom_tmul _ ha₀, map_units_zsmul, map_units_zsmul, map_sub, map_sub, desusp_tmul,
      desusp_tmul, hf.assoc, sub_self, smul_zero]

omit [DGAddCommGroup X] in
/-- The contracting homotopy: `s⁻¹ (stepHom f (1 ⊗ s y)) = y - 1 ⊗ f y`. -/
theorem desusp_stepHom_one_tmul (f : A ⊗[ℤ] X →+ X) (y : A ⊗[ℤ] X) :
    desusp A X (stepHom f (1 ⊗ₜ susp A X y)) = y - 1 ⊗ₜ f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => rw [map_add, tmul_add, map_add, map_add, hy, hy', map_add, tmul_add]; abel
  | tmul a x =>
    rw [susp_tmul, stepHom_tmul f one_mem_grading, koszulSign_zero, one_smul, map_sub, desusp_tmul,
      desusp_tmul, one_mul]

end Step

section Act

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- The action map `A ⊗ M → M`, `a ⊗ m ↦ a • m`. -/
def act : A ⊗[ℤ] M →+ M :=
  TensorProduct.liftAddHom (smulAddHom A M) fun r a m => by
    simp only [smulAddHom_apply, smul_assoc, smul_comm a r m]

variable {A M}

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup M] [DGModule A M] in
@[simp]
theorem act_tmul (a : A) (m : M) : act A M (a ⊗ₜ m) = a • m := rfl

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup M] [DGModule A M] in
theorem act_smul (a : A) (y : A ⊗[ℤ] M) : act A M (a • y) = a • act A M y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]
  | tmul a₀ m => rw [smul_tmul', act_tmul, act_tmul, smul_eq_mul, mul_smul]

omit [DGRing A] in
variable (A M) in
/-- The action map of a dg module is an action in the sense of `DG.Bar.IsAction`. -/
theorem isAction_act : IsAction A M (act A M) where
  mem ha hm := smul_mem_grading ha hm
  map_d y := by
    induction y using tensor_induction_on with
    | zero => simp
    | add y y' hy hy' => rw [d_add, map_add, hy, hy', map_add, d_add]
    | tmul a m =>
      rw [d_tmul_of_mem a.2, map_add, map_units_zsmul, act_tmul, act_tmul, act_tmul, d_smul a.2]
  assoc a a' m := by simp [mul_smul]

end Act

section Susp

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {X : Type*} [AddCommGroup X] [DGAddCommGroup X]

theorem desusp_mem {k : ℤ} {y : Shift 1 A ⊗[ℤ] X} (hy : y ∈ grading k) :
    desusp A X y ∈ grading (k + 1) :=
  map_mem_grading_of_tmul (desusp A X) 1 (fun {i j s x} hs hx => by
    obtain ⟨a, rfl⟩ := Shift.mk_surjective s
    have := tmul_mem_grading (Shift.unmk_mem_grading hs) hx
    rw [desusp_tmul]
    convert this using 2; ring) hy

theorem susp_mem {k : ℤ} {y : A ⊗[ℤ] X} (hy : y ∈ grading k) :
    susp A X y ∈ grading (k - 1) :=
  map_mem_grading_of_tmul (susp A X) (-1) (fun {i j a x} ha hx => by
    have := tmul_mem_grading (Shift.mk_mem_grading (n := 1) ha) hx
    rw [susp_tmul]
    convert this using 2; ring) hy

theorem desusp_d (y : Shift 1 A ⊗[ℤ] X) : desusp A X (d y) = -d (desusp A X y) := by
  induction y using tensor_induction_on with
  | zero => simp
  | add y y' hy hy' => rw [d_add, map_add, hy, hy', map_add, d_add, neg_add]
  | tmul s x =>
    obtain ⟨s, hs⟩ := s
    obtain ⟨a, rfl⟩ := Shift.mk_surjective s
    have ha : a ∈ grading (_ + 1) := Shift.unmk_mem_grading hs
    rw [d_tmul_of_mem hs, desusp_tmul, d_tmul_of_mem ha, Shift.d_mk, Shift.mk_units_smul,
      koszulSign_one]
    simp only [Units.smul_def, map_add, map_zsmul, ← smul_tmul', desusp_tmul, Units.val_neg,
      Units.val_one, neg_smul, one_smul, koszulSign_add_one, neg_tmul, map_neg, neg_neg]
    abel

theorem susp_d (y : A ⊗[ℤ] X) : susp A X (d y) = -d (susp A X y) := by
  have h := congrArg (susp A X) (desusp_d (susp A X y))
  rw [susp_desusp, desusp_susp, map_neg] at h
  rw [h, neg_neg]

theorem IsAction.map_mem {f : A ⊗[ℤ] X →+ X} (hf : IsAction A X f) {k : ℤ} {y : A ⊗[ℤ] X}
    (hy : y ∈ grading k) : f y ∈ grading k := by
  simpa using map_mem_grading_of_tmul f 0 (fun ha hx => by simpa using hf.mem ha hx) hy

end Susp

section Homotopy

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {X : Type*} [AddCommGroup X] [DGAddCommGroup X]

omit [DGAddCommGroup X] in
theorem homotopy_identity_zero (f : A ⊗[ℤ] X →+ X) (y : A ⊗[ℤ] X) :
    desusp A X (stepHom f (1 ⊗ₜ susp A X y)) + 1 ⊗ₜ f y = y := by
  rw [desusp_stepHom_one_tmul, sub_add_cancel]

theorem homotopy_identity_succ (f : A ⊗[ℤ] X →+ X) (y : A ⊗[ℤ] X)
    (z : A ⊗[ℤ] (Shift 1 A ⊗[ℤ] X)) :
    d ((1 : A) ⊗ₜ susp A X y) +
      desusp _ _ (stepHom (stepHom f) (1 ⊗ₜ susp _ _ z)) +
        (1 : A) ⊗ₜ susp A X (d y + desusp A X (stepHom f z)) = z := by
  rw [desusp_stepHom_one_tmul, map_add, susp_desusp, tmul_add, d_tmul_of_mem one_mem_grading,
    d_one, zero_tmul, zero_add, koszulSign_zero, one_smul, susp_d, tmul_neg]
  abel

end Homotopy

universe u

/-- A level of the bar construction: a dg abelian group `X` together with a non-unital graded
action `A ⊗ X → X` (`DG.Bar.IsAction`). -/
structure Level (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A] where
  /-- The underlying type. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [dgAddCommGroup : DGAddCommGroup carrier]
  /-- The action. -/
  act : A ⊗[ℤ] carrier →+ carrier
  isAction : IsAction A carrier act

attribute [instance] Level.addCommGroup Level.dgAddCommGroup

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type u) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

variable {A} in
/-- The next level: `A⟦1⟧ ⊗ X` with the action `DG.Bar.stepHom`. -/
def Level.next (L : Level A) : Level A where
  carrier := Shift 1 A ⊗[ℤ] L.carrier
  act := stepHom L.act
  isAction := L.isAction.step

/-- The levels `(A⟦1⟧)^{⊗ n} ⊗ M` of the bar construction, with their actions. -/
def level : ℕ → Level A
  | 0 => ⟨M, act A M, isAction_act A M⟩
  | n + 1 => (level n).next

/-- The underlying dg abelian group `(A⟦1⟧)^{⊗ n} ⊗ M` of the `n`-th level. -/
abbrev T (n : ℕ) : Type u := (level A M n).carrier

/-- The `n`-th term `A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M` of the bar construction. -/
abbrev Term (n : ℕ) : Type u := A ⊗[ℤ] T A M n

variable {A M}

/-- The component `A ⊗ T (n + 1) → A ⊗ T n` of the bar differential. -/
def barComp (n : ℕ) : Term A M (n + 1) →+ Term A M n :=
  (desusp A (T A M n)).comp (level A M (n + 1)).act

theorem barComp_apply (n : ℕ) (y : Term A M (n + 1)) :
    barComp n y = desusp A (T A M n) (stepHom (level A M n).act y) := rfl

theorem barComp_mem (n : ℕ) {k : ℤ} {y : Term A M (n + 1)} (hy : y ∈ grading k) :
    barComp n y ∈ grading (k + 1) :=
  desusp_mem ((level A M (n + 1)).isAction.map_mem hy)

theorem barComp_d (n : ℕ) (y : Term A M (n + 1)) : barComp n (d y) = -d (barComp n y) := by
  exact (congrArg (desusp A (T A M n)) ((level A M n).isAction.step_d y)).trans (desusp_d _)

theorem barComp_barComp (n : ℕ) (y : Term A M (n + 2)) : barComp n (barComp (n + 1) y) = 0 := by
  rw [barComp_apply, barComp_apply]
  exact (congrArg _ ((level A M (n + 1)).isAction.apply_desusp_stepHom y)).trans (map_zero _)

theorem barComp_smul (n : ℕ) {i : ℤ} {a : A} (ha : a ∈ grading i) (y : Term A M (n + 1)) :
    barComp n (a • y) = koszulSign i • (a • barComp n y) :=
  desusp_stepHom_smul _ ha y

end Bar


section Contraction

variable {A : Type*} [Ring A] [DGAddCommGroup A]
  {P M : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]

/-- A morphism of dg modules `p : P → M` with an additive section `η : M → P` of degree `0`
commuting with the differentials and an additive map `h : P → P` of degree `-1` with
`d h + h d + η p = 1` (a contraction of the underlying dg abelian groups onto `M`) is a
quasi-isomorphism. -/
theorem DGModuleHom.isQuasiIso_of_contraction (p : P →ᵈᵍ[A] M) (η : M →+ P)
    (hη : ∀ {k : ℤ} {m : M}, m ∈ grading k → η m ∈ grading k) (hηd : ∀ m, η (d m) = d (η m))
    (h : P →+ P) (hh : ∀ {k : ℤ} {x : P}, x ∈ grading k → h x ∈ grading (k - 1))
    (hid : ∀ x, d (h x) + h (d x) + η (p x) = x) (hpη : ∀ m, p (η m) = m) : p.IsQuasiIso :=
  fun k => by
  constructor
  · rw [cohomology.map_injective_iff]
    intro x hx hdx hpx
    obtain ⟨m, hm, hdm⟩ := mem_coboundaries.mp hpx
    refine mem_coboundaries.mpr ⟨h x + η m, add_mem (hh hx) (hη hm), ?_⟩
    have hx' := hid x
    rw [hdx, map_zero, add_zero] at hx'
    rw [d_add, ← hηd, hdm, hx']
  · rw [cohomology.map_surjective_iff]
    intro m hm hdm
    exact ⟨η m, hη hm, by rw [← hηd, hdm, map_zero], by rw [hpη, sub_self]; exact zero_mem _⟩

end Contraction

section Filtration

universe w

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  {Q : ℕ → Type*} [∀ i, AddCommGroup (Q i)] [∀ i, DGAddCommGroup (Q i)] [∀ i, Module A (Q i)]
  [∀ i, DGModule A (Q i)]
  {F : ℕ → DGSubmodule A P} (hF : Monotone F) (h0 : ∀ x ∈ F 0, x = 0) (hex : ∀ x, ∃ i, x ∈ F i)
  {π : ∀ i, F (i + 1) →ᵈᵍ[A] Q i}
  (σ : ∀ i, GradedSplitting (DGSubmodule.inclusion (hF i.le_succ)) (π i))

omit [DGRing A] in
include h0 hex σ in
/-- A dg module with an exhaustive filtration `0 = F 0 ⊆ F 1 ⊆ ⋯` by dg submodules whose
inclusions `F i → F (i + 1)` are graded-split with K-projective cokernels is K-projective (the
telescope argument of `DG.SemiFreeFiltration.isKProjective`). -/
theorem IsKProjective.of_filtration (hQ : ∀ i, IsKProjective.{w} A (Q i)) :
    IsKProjective.{w} A P := by
  intro N _ _ _ _ hN f
  obtain ⟨h, hh⟩ := Cochain.exists_of_filtration hF hex
    (fun i => {h : Cochain A (F i) N (-1) |
      Cochain.ofHom (f.comp (F i).subtype) = δ (-1) 0 h})
    ⟨0, Cochain.ext fun x => by simp [h0 x x.2]⟩
    (fun i h hh => (σ i).exists_extension (hQ i N hN) (f.comp (F (i + 1)).subtype) h hh)
  refine homotopic_zero_iff_exists.mpr ⟨h, Cochain.ext fun x => ?_⟩
  obtain ⟨i, hi⟩ := hex x
  have h1 := congrArg (fun z : Cochain A (F i) N 0 => z ⟨x, hi⟩) (hh i)
  have h2 := congrArg (fun z : Cochain A (F i) N 0 => z ⟨x, hi⟩)
    (δ_ofHom_comp (F i).subtype h 0)
  simp only [Cochain.ofHom_apply, DGModuleHom.comp_apply, DGSubmodule.subtype_apply,
    Cochain.comp_apply] at h1 h2
  rw [Cochain.ofHom_apply, h1, h2]

omit [DGRing A] [DGModule A P] [∀ (i : ℕ), DGModule A (Q i)] in
include h0 hex σ in
/-- A dg module with an exhaustive filtration `0 = F 0 ⊆ F 1 ⊆ ⋯` by dg submodules whose
inclusions `F i → F (i + 1)` are graded-split with graded-projective cokernels is
graded-projective. -/
theorem IsGradedProjective.of_filtration (hQ : ∀ i, IsGradedProjective.{w} A (Q i)) :
    IsGradedProjective.{w} A P := by
  intro M N _ _ _ _ _ _ _ _ p hp f
  obtain ⟨g, hg⟩ := Cochain.exists_of_filtration hF hex
    (fun i => {g : Cochain A (F i) M 0 | (Cochain.ofHom p).comp g (zero_add 0) =
      f.comp (Cochain.ofHom (F i).subtype) (zero_add 0)})
    ⟨0, Cochain.ext fun x => by simp [h0 x x.2]⟩
    (fun i g hg => by
      obtain ⟨gQ, hgQ⟩ := hQ i M N p hp
        ((f.comp (Cochain.ofHom (F (i + 1)).subtype) (zero_add 0)).comp (σ i).s (zero_add 0))
      refine ⟨g.comp (σ i).r (zero_add 0) + gQ.comp (Cochain.ofHom (π i)) (zero_add 0),
        Cochain.ext fun x => ?_, fun x => ?_⟩
      · have h1 := congrArg (fun c : Cochain A (F i) N 0 => c ((σ i).r x)) hg
        have h2 := congrArg (fun c : Cochain A _ N 0 => c (π i x)) hgQ
        have h3 := congrArg (fun y : F (i + 1) => (y : P)) ((σ i).i_r_add_s_p x)
        simp only [Cochain.comp_apply, Cochain.ofHom_apply, DGSubmodule.subtype_apply] at h1 h2
        simp only [Cochain.comp_apply, Cochain.ofHom_apply, Cochain.add_apply, map_add, h1, h2,
          DGSubmodule.subtype_apply]
        simp only [DGSubmodule.coe_add, DGSubmodule.coe_inclusion_apply] at h3
        rw [← map_add, h3]
      · simp [(σ i).r_i, (σ i).p_i])
  refine ⟨g, Cochain.ext fun x => ?_⟩
  obtain ⟨i, hi⟩ := hex x
  exact congrArg (fun c : Cochain A (F i) N 0 => c ⟨x, hi⟩) (hg i)

end Filtration

universe u

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type u) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- The (unnormalized) bar construction `Bar(A, M) = ⨁_{n ≥ 0} A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M`. -/
def Bar : Type u := ⨁ n : ℕ, Bar.Term A M n

namespace Bar

instance : AddCommGroup (Bar A M) := inferInstanceAs (AddCommGroup (⨁ n : ℕ, Term A M n))

instance : Module A (Bar A M) := inferInstanceAs (Module A (⨁ n : ℕ, Term A M n))

variable {A M}

/-- The `n`-th component of an element of the bar construction. -/
def coeff (n : ℕ) : Bar A M →+ Term A M n :=
  DFinsupp.evalAddMonoidHom (β := fun n => Term A M n) n

theorem ext {x y : Bar A M} (h : ∀ n, coeff n x = coeff n y) : x = y :=
  DFinsupp.ext h

variable (A M) in
/-- The inclusion of the `n`-th term. -/
def of (n : ℕ) : Term A M n →ₗ[A] Bar A M :=
  DirectSum.lof A ℕ (fun n => Term A M n) n

theorem coeff_of_same (n : ℕ) (y : Term A M n) : coeff n (of A M n y) = y :=
  DirectSum.of_eq_same n y

theorem coeff_of_ne {m n : ℕ} (h : m ≠ n) (y : Term A M m) : coeff n (of A M m y) = 0 :=
  DirectSum.of_eq_of_ne m n y h

theorem coeff_smul (n : ℕ) (a : A) (x : Bar A M) : coeff n (a • x) = a • coeff n x := rfl

/-- The bar differential `Bar(A, M) → Bar(A, M)`, of degree `1`, with components
`DG.Bar.barComp n : A ⊗ T (n + 1) → A ⊗ T n`. -/
def barD : Bar A M →+ Bar A M :=
  DirectSum.toAddMonoid fun n => match n with
    | 0 => 0
    | n + 1 => (of A M n).toAddMonoidHom.comp (barComp n)

theorem coeff_barD (x : Bar A M) (n : ℕ) : coeff n (barD x) = barComp n (coeff (n + 1) x) := by
  induction x using DirectSum.induction_on with
  | zero => simp [barD]
  | of m y =>
    change coeff n (barD (of A M m y)) = barComp n (coeff (n + 1) (of A M m y))
    cases m with
    | zero =>
      rw [coeff_of_ne (by omega), map_zero]
      exact congrArg (coeff n) (DirectSum.toAddMonoid_of _ 0 y)
    | succ m =>
      have h : barD (of A M (m + 1) y) = of A M m (barComp m y) :=
        DirectSum.toAddMonoid_of _ (m + 1) y
      rw [h]
      by_cases hmn : m = n
      · subst hmn
        rw [coeff_of_same, coeff_of_same]
      · rw [coeff_of_ne hmn, coeff_of_ne (by omega), map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The internal differential, componentwise. -/
def intD : Bar A M →+ Bar A M := DG.DirectSum.d (fun n => Term A M n)

theorem coeff_intD (x : Bar A M) (n : ℕ) : coeff n (intD x) = d (coeff n x) :=
  DG.DirectSum.d_apply _ x n

/-- The total differential: the internal differential plus the bar differential. -/
def totalD : Bar A M →+ Bar A M := intD + barD

theorem coeff_totalD (x : Bar A M) (n : ℕ) :
    coeff n (totalD x) = d (coeff n x) + barComp n (coeff (n + 1) x) := by
  rw [totalD, AddMonoidHom.add_apply, map_add, coeff_barD, coeff_intD]

theorem totalD_totalD (x : Bar A M) : totalD (totalD x) = 0 := by
  refine ext fun n => ?_
  rw [coeff_totalD, coeff_totalD, coeff_totalD, map_zero, d_add, d_d, map_add, barComp_barComp,
    barComp_d]
  abel

theorem barD_mem {k : ℤ} {x : Bar A M}
    (hx : x ∈ DG.DirectSum.grading (fun n => Term A M n) k) :
    barD x ∈ DG.DirectSum.grading (fun n => Term A M n) (k + 1) := fun n => by
  change coeff n (barD x) ∈ _
  rw [coeff_barD]
  exact barComp_mem n (hx (n + 1))

theorem totalD_mem {k : ℤ} {x : Bar A M}
    (hx : x ∈ DG.DirectSum.grading (fun n => Term A M n) k) :
    totalD x ∈ DG.DirectSum.grading (fun n => Term A M n) (k + 1) :=
  add_mem (d_mem (M := ⨁ n, Term A M n) hx) (barD_mem hx)

/-- The dg abelian group structure of `Bar(A, M)`: the grading of the direct sum and the total
differential `d + b`. -/
instance instDGAddCommGroup : DGAddCommGroup (Bar A M) where
  grading := DG.DirectSum.grading (fun n => Term A M n)
  decomposition := (DG.DirectSum.isInternal_grading _).chooseDecomposition
  d := totalD
  d_mem' := totalD_mem
  d_d' := totalD_totalD

theorem mem_grading_iff {k : ℤ} {x : Bar A M} : x ∈ grading k ↔ ∀ n, coeff n x ∈ grading k :=
  Iff.rfl

theorem coeff_d (x : Bar A M) (n : ℕ) :
    coeff n (d x) = d (coeff n x) + barComp n (coeff (n + 1) x) :=
  coeff_totalD x n

theorem of_mem_grading {k : ℤ} {n : ℕ} {y : Term A M n} (hy : y ∈ grading k) :
    of A M n y ∈ grading k :=
  DG.DirectSum.of_mem_grading _ n hy

/-- `Bar(A, M)` is a dg `A`-module, `A` acting on the first tensor factor. -/
instance instDGModule : DGModule A (Bar A M) where
  smul_mem {i k a x} ha hx n := by
    change coeff n (a • x) ∈ _
    rw [coeff_smul]
    exact smul_mem_grading ha (hx n)
  d_smul' {i a} ha x := by
    refine ext fun n => ?_
    rw [coeff_d, coeff_smul, coeff_smul, d_smul ha, barComp_smul n ha, map_add, coeff_smul,
      map_units_zsmul, coeff_smul, coeff_d, smul_add, smul_add]
    abel

/-! ### The augmentation and the contracting homotopy -/

theorem coeff_zero_d (x : Bar A M) :
    act A M (coeff 0 (d x)) = d (act A M (coeff 0 x)) := by
  rw [coeff_d, map_add, barComp_apply]
  have h1 : act A M (d (coeff 0 x)) = d (act A M (coeff 0 x)) := (isAction_act A M).map_d _
  have h2 : act A M (desusp A M (stepHom (act A M) (coeff 1 x))) = 0 :=
    (isAction_act A M).apply_desusp_stepHom _
  exact (congrArg₂ (· + ·) h1 h2).trans (add_zero _)

variable (A M) in
/-- The augmentation `Bar(A, M) → M`, `a₀ [ ] m ↦ a₀ m` on `A ⊗ M` and zero on the other
terms. -/
def augmentation : Bar A M →ᵈᵍ[A] M where
  toFun x := act A M (coeff 0 x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by rw [coeff_smul, act_smul]; rfl
  map_mem' hx := (isAction_act A M).map_mem (hx 0)
  map_d' := coeff_zero_d

theorem augmentation_apply (x : Bar A M) : augmentation A M x = act A M (coeff 0 x) := rfl

variable (A M) in
/-- The section `M → Bar(A, M)`, `m ↦ 1 [ ] m`; it is additive of degree `0` and commutes with
the differentials, but is not `A`-linear. -/
def unit : M →+ Bar A M :=
  (of A M 0).toAddMonoidHom.comp (tmulAddHom A M 1)

theorem unit_apply (m : M) : unit A M m = of A M 0 (1 ⊗ₜ m) := rfl

theorem augmentation_unit (m : M) : augmentation A M (unit A M m) = m := by
  rw [augmentation_apply, unit_apply, coeff_of_same, act_tmul, one_smul]

theorem unit_mem {k : ℤ} {m : M} (hm : m ∈ grading k) : unit A M m ∈ grading k := by
  rw [unit_apply]
  exact of_mem_grading (by simpa using tmul_mem_grading (one_mem_grading (A := A)) hm)

theorem d_one_tmul {X : Type*} [AddCommGroup X] [DGAddCommGroup X] (x : X) :
    d ((1 : A) ⊗ₜ[ℤ] x) = 1 ⊗ₜ d x := by
  rw [d_tmul_of_mem one_mem_grading, d_one, zero_tmul, zero_add, koszulSign_zero, one_smul]

theorem unit_d (m : M) : unit A M (d m) = d (unit A M m) := by
  refine ext fun n => ?_
  rw [coeff_d, unit_apply, unit_apply]
  rcases n with _ | n
  · rw [coeff_of_same, coeff_of_same, coeff_of_ne (by omega), map_zero, add_zero, d_one_tmul]
    rfl
  · rw [coeff_of_ne (by omega), coeff_of_ne (by omega), coeff_of_ne (by omega), map_zero,
      map_zero, add_zero]

/-- The contracting homotopy `a₀ [a₁ | ⋯ | aₙ] m ↦ 1 [a₀ | a₁ | ⋯ | aₙ] m`, additive of degree
`-1` (not `A`-linear). -/
def homotopy : Bar A M →+ Bar A M :=
  DirectSum.toAddMonoid fun n =>
    (of A M (n + 1)).toAddMonoidHom.comp
      ((tmulAddHom A (T A M (n + 1)) 1).comp (susp A (T A M n)))

theorem coeff_homotopy_zero (x : Bar A M) : coeff 0 (homotopy x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of m y =>
    change coeff 0 (homotopy (of A M m y)) = 0
    have h : homotopy (of A M m y) = of A M (m + 1) (1 ⊗ₜ susp A (T A M m) y) :=
      DirectSum.toAddMonoid_of _ m y
    rw [h, coeff_of_ne (by omega)]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem coeff_homotopy_succ (x : Bar A M) (n : ℕ) :
    coeff (n + 1) (homotopy x) = 1 ⊗ₜ susp A (T A M n) (coeff n x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of m y =>
    change coeff (n + 1) (homotopy (of A M m y)) = 1 ⊗ₜ susp A (T A M n) (coeff n (of A M m y))
    have h : homotopy (of A M m y) = of A M (m + 1) (1 ⊗ₜ susp A (T A M m) y) :=
      DirectSum.toAddMonoid_of _ m y
    rw [h]
    by_cases hmn : m = n
    · subst hmn
      rw [coeff_of_same, coeff_of_same]
    · rw [coeff_of_ne (by omega), coeff_of_ne hmn, map_zero, tmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, tmul_add]

theorem homotopy_mem {k : ℤ} {x : Bar A M} (hx : x ∈ grading k) :
    homotopy x ∈ grading (k - 1) := fun n => by
  change coeff n (homotopy x) ∈ _
  rcases n with _ | n
  · rw [coeff_homotopy_zero]; exact zero_mem _
  · rw [coeff_homotopy_succ]
    simpa using tmul_mem_grading (one_mem_grading (A := A)) (susp_mem (hx n))

/-- The contracting homotopy identity `d h + h d = 1 - η ε` on `Bar(A, M)`, where `η` is
`DG.Bar.unit` and `ε` the augmentation: the augmentation is a homotopy equivalence of the
underlying dg abelian groups. -/
theorem d_homotopy_add_homotopy_d (x : Bar A M) :
    d (homotopy x) + homotopy (d x) + unit A M (augmentation A M x) = x := by
  refine ext fun n => ?_
  rw [map_add, map_add, coeff_d, unit_apply, augmentation_apply]
  rcases n with _ | n
  · rw [coeff_homotopy_zero, coeff_homotopy_zero, coeff_homotopy_succ, coeff_of_same, map_zero,
      zero_add, add_zero, barComp_apply]
    exact homotopy_identity_zero _ _
  · rw [coeff_homotopy_succ, coeff_homotopy_succ, coeff_homotopy_succ, coeff_of_ne (by omega),
      coeff_d, add_zero, barComp_apply, barComp_apply]
    exact homotopy_identity_succ _ _ _

variable (A M) in
/-- The augmentation `Bar(A, M) → M` is surjective. -/
theorem surjective_augmentation : Function.Surjective (augmentation A M) :=
  fun m => ⟨unit A M m, augmentation_unit m⟩

variable (A M) in
/-- The augmentation `Bar(A, M) → M` is a quasi-isomorphism. -/
theorem isQuasiIso_augmentation : (augmentation A M).IsQuasiIso :=
  (augmentation A M).isQuasiIso_of_contraction (unit A M) unit_mem unit_d homotopy homotopy_mem
    d_homotopy_add_homotopy_d augmentation_unit

/-! ### The filtration by the number of bars -/

theorem coeff_mem {k : ℤ} {x : Bar A M} (hx : x ∈ grading k) (n : ℕ) : coeff n x ∈ grading k :=
  hx n

theorem coe_decompose_coeff (x : Bar A M) (n : ℕ) (k : ℤ) :
    (decompose (grading (M := Term A M n)) (coeff n x) k : Term A M n) =
      coeff n (decompose (grading (M := Bar A M)) x k : Bar A M) :=
  coe_decompose_map_of_map_mem (coeff n) (fun hx => coeff_mem hx n) x k

variable (A M) in
/-- The filtration of `Bar(A, M)` by the number of bars: `F n = ⨁_{k < n} A ⊗ T k`. -/
def filtration (n : ℕ) : DGSubmodule A (Bar A M) where
  carrier := {x | ∀ k, n ≤ k → coeff k x = 0}
  add_mem' hx hy k hk := by rw [map_add, hx k hk, hy k hk, add_zero]
  zero_mem' k _ := map_zero _
  smul_mem' a x hx k hk := by rw [coeff_smul, hx k hk, smul_zero]
  d_mem' {x} hx k hk := by
    rw [coeff_d, hx k hk, hx (k + 1) (by omega), d_zero, map_zero, add_zero]
  decompose_mem' j x hx k hk := by
    rw [← coe_decompose_coeff, hx k hk, decompose_zero, DirectSum.zero_apply,
      ZeroMemClass.coe_zero]

theorem mem_filtration_iff {n : ℕ} {x : Bar A M} :
    x ∈ filtration A M n ↔ ∀ k, n ≤ k → coeff k x = 0 :=
  Iff.rfl

theorem filtration_mono : Monotone (filtration A M) :=
  fun _ _ hmn _ hx k hk => hx k (hmn.trans hk)

theorem eq_zero_of_mem_filtration_zero (x : Bar A M) (hx : x ∈ filtration A M 0) : x = 0 :=
  ext fun n => (hx n (Nat.zero_le n)).trans (map_zero _).symm

theorem of_mem_filtration {n : ℕ} (y : Term A M n) : of A M n y ∈ filtration A M (n + 1) :=
  fun _ hk => coeff_of_ne (by omega) y

theorem exists_mem_filtration (x : Bar A M) : ∃ n, x ∈ filtration A M n := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | of n y => exact ⟨n + 1, of_mem_filtration y⟩
  | add x y hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨max i j, add_mem (filtration_mono (le_max_left i j) hi)
      (filtration_mono (le_max_right i j) hj)⟩

variable (A M) in
/-- The projection of `F (n + 1)` onto its subquotient `A ⊗ T n`. -/
def filtrationπ (n : ℕ) : filtration A M (n + 1) →ᵈᵍ[A] Term A M n where
  toFun x := coeff n (x : Bar A M)
  map_add' x y := map_add _ _ _
  map_smul' a x := coeff_smul n a (x : Bar A M)
  map_mem' hx := coeff_mem hx n
  map_d' x := by
    change coeff n (d (x : Bar A M)) = _
    rw [coeff_d, x.2 (n + 1) le_rfl, map_zero, add_zero]

theorem filtrationπ_apply (n : ℕ) (x : filtration A M (n + 1)) :
    filtrationπ A M n x = coeff n (x : Bar A M) := rfl

theorem filtrationπ_eq_zero_iff (n : ℕ) (x : filtration A M (n + 1)) :
    filtrationπ A M n x = 0 ↔ (x : Bar A M) ∈ filtration A M n := by
  rw [filtrationπ_apply]
  constructor
  · intro h k hk
    rcases hk.lt_or_eq with hk | rfl
    · exact x.2 k hk
    · exact h
  · intro h
    exact h n le_rfl

variable (A M) in
/-- The graded section `A ⊗ T n → F (n + 1)` of `DG.Bar.filtrationπ`. -/
def filtrationSection (n : ℕ) : Cochain A (Term A M n) (filtration A M (n + 1)) 0 :=
  Cochain.ofHoms ((of A M n).codRestrict (filtration A M (n + 1)).toSubmodule
    of_mem_filtration) (fun hy => of_mem_grading hy)

theorem filtrationπ_filtrationSection (n : ℕ) (y : Term A M n) :
    filtrationπ A M n (filtrationSection A M n y) = y :=
  coeff_of_same n y

variable (A M) in
/-- The inclusions `F n → F (n + 1)` of the filtration are split as maps of graded
`A`-modules, with cokernel `A ⊗ T n`. -/
def gradedSplitting (n : ℕ) :
    GradedSplitting (DGSubmodule.inclusion (filtration_mono (A := A) (M := M) n.le_succ))
      (filtrationπ A M n) :=
  GradedSplitting.ofSection _ (filtrationπ A M n) (filtrationπ_eq_zero_iff n)
    (filtrationSection A M n) (filtrationπ_filtrationSection n)

universe w

/-- If every term `A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M` is K-projective, so is `Bar(A, M)`. -/
theorem isKProjective (h : ∀ n, IsKProjective.{w} A (Term A M n)) :
    IsKProjective.{w} A (Bar A M) :=
  IsKProjective.of_filtration filtration_mono eq_zero_of_mem_filtration_zero exists_mem_filtration
    (gradedSplitting A M) h

/-- If every term `A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M` has the lifting property against surjective
quasi-isomorphisms, so has `Bar(A, M)`. -/
theorem hasLiftingProperty (h : ∀ n, HasLiftingProperty.{w} A (Term A M n)) :
    HasLiftingProperty.{w} A (Bar A M) :=
  (isKProjective fun n => (h n).isKProjective).hasLiftingProperty
    (IsGradedProjective.of_filtration filtration_mono eq_zero_of_mem_filtration_zero
      exists_mem_filtration (gradedSplitting A M) fun n => (h n).isGradedProjective)

theorem surjective_filtrationπ (n : ℕ) : Function.Surjective (filtrationπ A M n) :=
  fun y => ⟨filtrationSection A M n y, filtrationπ_filtrationSection n y⟩

/-! ### Semi-freeness and comparison with the standard semi-free resolution -/

/-- If every term `A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M` is isomorphic, as a dg module, to a direct sum of shifts
of `A`, then the filtration by the number of bars is a semi-free filtration of `Bar(A, M)`. -/
def semiFreeFiltration (ι : ℕ → Type u) [∀ n, DecidableEq (ι n)] (deg : ∀ n, ι n → ℤ)
    (e : ∀ n, Term A M n ≃ᵈᵍ[A] ⨁ b : ι n, Shift (deg n b) A) :
    SemiFreeFiltration.{u} A (Bar A M) where
  F := filtration A M
  mono := filtration_mono
  eq_zero_of_mem_zero := eq_zero_of_mem_filtration_zero
  exists_mem := exists_mem_filtration
  ι := ι
  deg := deg
  π n := (e n).toDGModuleHom.comp (filtrationπ A M n)
  surjective_π n := (e n).surjective.comp (surjective_filtrationπ n)
  π_eq_zero_iff n x := by
    rw [DGModuleHom.comp_apply, DGModuleEquiv.coe_toDGModuleHom,
      map_eq_zero_iff _ (e n).injective, filtrationπ_eq_zero_iff]

variable (A M) in
/-- The bar resolution `Bar(A, M) → M` as a semi-free resolution, when every term
`A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M` is isomorphic to a direct sum of shifts of `A`. -/
def semiFreeResolution (ι : ℕ → Type u) [∀ n, DecidableEq (ι n)] (deg : ∀ n, ι n → ℤ)
    (e : ∀ n, Term A M n ≃ᵈᵍ[A] ⨁ b : ι n, Shift (deg n b) A) : SemiFreeResolution A M where
  P := Bar A M
  π := augmentation A M
  surjective_π := surjective_augmentation A M
  isQuasiIso_π := isQuasiIso_augmentation A M
  filtration := semiFreeFiltration ι deg e

variable (A M) in
/-- Comparison with the resolution of `DG.semiFreeResolution`: if every term
`A ⊗ (A⟦1⟧)^{⊗ n} ⊗ M` has the lifting property against surjective quasi-isomorphisms (e.g. is
isomorphic to a direct sum of shifts of `A`), then `Bar(A, M)` and the standard semi-free
resolution are homotopy equivalent over `M`, strictly compatibly with the augmentations. -/
theorem exists_dgHomotopyEquiv_semiFreeResolution
    (h : ∀ n, HasLiftingProperty.{u} A (Term A M n)) :
    ∃ e : DGHomotopyEquiv A (Bar A M) (DG.semiFreeResolution.{u, u} A M).P,
      (DG.semiFreeResolution.{u, u} A M).π.comp e.hom = augmentation A M ∧
        (augmentation A M).comp e.inv = (DG.semiFreeResolution.{u, u} A M).π :=
  (hasLiftingProperty h).exists_dgHomotopyEquiv (DG.semiFreeResolution A M).hasLiftingProperty
    (surjective_augmentation A M) (isQuasiIso_augmentation A M)
    (DG.semiFreeResolution A M).surjective_π (DG.semiFreeResolution A M).isQuasiIso_π

end Bar

end DG

