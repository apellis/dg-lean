import DG.HalfGraded.SuperK0Linear
import DG.K0.Orthonormal
import DG.Category.Derived.Compact
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Half-graded dg modules over a field

Let `K` be a field, regarded as a half-graded dg ring concentrated in bidegree `(0, 0̄)` with zero
differential (`DG.HalfGradedDGRing.degreeZero K k`), for a differential of bidegree `(k, 1̄)` with
`k > 0` (main case `k = 2`). This file computes the Grothendieck groups of the compact objects of
the derived category `D(K)` of half-graded dg `K`-modules (roadmap item 7.4 (d)).

## The weight dg category

The regraded ring `K' = ⨁ (n, w), K^{w + n k, n}` has a copy of `K` exactly in the bidegrees
`(2m, -2mk)`, i.e. `K' = K[u, u⁻¹]` with `u` the periodicity unit. In the weight dg category `C`,
`C(i, j)` is `K` (placed in cohomological degree `n = (i - j) / k`) if `j - i + n k = 0` with `n`
even, i.e. `i ≡ j (mod 2k)`, and zero otherwise; the differential is zero. For `0 ≤ i, j < 2k`
this gives `C(i, j) = 0` for `i ≠ j` and `C(i, i) = K` in degree `0`.

## Main results

* `DG.HalfGradedDGRing.degreeZero A k`: a ring concentrated in bidegree `(0, 0̄)`.
* The representable modules `k_r = Q C(r, -)` for `r ∈ Fin (2k)` form an orthonormal generating
  family of the compact objects `D(K)^c` (`DG.HalfGradedDGRing.Field.isOrthonormalGenerating`),
  hence `K₀(D(K)^c) ≃+ (Fin (2k) → ℤ)`, free on the classes `[k_r]`
  (`DG.HalfGradedDGRing.Field.K0Equiv`).
* `K₀(D(K)^c)` is a `ℤ[q, q⁻¹]`-module with `qⁿ • [M] = [M⟨n⟩]` (tier 7.1); here
  `qˢ • [k_i] = [k_{i - s}]` (`DG.HalfGradedDGRing.Field.T_smul_cls`), `q²ᵏ` acts trivially
  (`DG.HalfGradedDGRing.Field.T_two_mul_smul`, from `Π Π ≅ 𝟭`), and
  `DG.HalfGradedDGRing.Field.K0LinearEquiv : K₀(D(K)^c) ≃ₗ[ℤ[q, q⁻¹]] ℤ[q, q⁻¹] ⧸ (q²ᵏ - 1)`,
  `[k] ↦ 1`, where `k = k_0` is the field itself. `DG.HalfGradedDGRing.Field.K0Basis`: the classes
  `qⁱ [k]`, `0 ≤ i < 2k`, form a `ℤ`-basis (`K0Basis_apply`).
* `[Π X] = -qᵏ [X]` (`DG.HalfGradedDGRing.Field.mk_parityShiftCompact'`), in particular
  `[Π k] = -qᵏ [k]` (`DG.HalfGradedDGRing.Field.cls_parityShift`).
* The super Grothendieck group: `DG.HalfGradedDGRing.Field.superK0Equiv :
  K₀^{super}(D(K)^c) ≃+ ℤ[q, q⁻¹] ⧸ (1 + qᵏ)`, `[k] ↦ 1`, from the comparison theorem
  `DG.HalfGradedDGRing.superK0cEquiv`; for `k = 2`,
  `DG.HalfGradedDGRing.GaussianQuot.equivGaussianInt : ℤ[q, q⁻¹] ⧸ (1 + q²) ≃+* ℤ[√-1]` and
  `DG.HalfGradedDGRing.Field.superK0EquivGaussianInt : K₀^{super}(D(K)^c) ≃+ ℤ[√-1]`.

## Remarks

The roadmap states the result for `K₀(D(K))`. The derived category has arbitrary coproducts, so
its Grothendieck group vanishes (Eilenberg swindle: `X ⊕ ∐ₙ X ≅ ∐ₙ X`); as in item 5.5
(`K₀(A) := K₀(D^c(A))`), the statement is about the compact objects `D(K)^c`.
-/

open CategoryTheory Category Limits Pretriangulated DirectSum

universe u

noncomputable section

namespace DG

namespace HalfGradedDGRing

/-! ### Rings concentrated in bidegree `(0, 0̄)` -/

section DegreeZero

variable (A : Type u) [Ring A]

/-- The `ℤ × ℤ/2`-grading of a ring concentrated in bidegree `(0, 0̄)`. -/
def degreeZeroGrading (p : ℤ × ZMod 2) : AddSubgroup A := if p = 0 then ⊤ else ⊥

variable {A}

theorem mem_degreeZeroGrading_iff {p : ℤ × ZMod 2} {a : A} :
    a ∈ degreeZeroGrading A p ↔ p = 0 ∨ a = 0 := by
  unfold degreeZeroGrading
  split_ifs with h <;> simp [h]

variable (A)

/-- The decomposition of a ring concentrated in bidegree `(0, 0̄)`. -/
def degreeZeroDecompose : A →+ ⨁ p, degreeZeroGrading A p :=
  (DirectSum.of (fun p => degreeZeroGrading A p) 0).comp
    { toFun := fun a => ⟨a, mem_degreeZeroGrading_iff.mpr (Or.inl rfl)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

instance : Decomposition (degreeZeroGrading A) :=
  Decomposition.ofAddHom _ (degreeZeroDecompose A)
    (AddMonoidHom.ext fun a => by
      simp [degreeZeroDecompose, DirectSum.coeAddMonoidHom_of])
    (DirectSum.addHom_ext fun p x => by
      obtain ⟨x, hx⟩ := x
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply,
        degreeZeroDecompose, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rcases mem_degreeZeroGrading_iff.mp hx with rfl | rfl
      · rfl
      · exact (map_zero (DirectSum.of (fun p => degreeZeroGrading A p) 0)).trans
          (map_zero (DirectSum.of (fun p => degreeZeroGrading A p) p)).symm)

instance : SetLike.GradedMonoid (degreeZeroGrading A) where
  one_mem := mem_degreeZeroGrading_iff.mpr (Or.inl rfl)
  mul_mem i j a b ha hb := by
    rcases mem_degreeZeroGrading_iff.mp ha with rfl | rfl
    · rcases mem_degreeZeroGrading_iff.mp hb with rfl | rfl
      · exact mem_degreeZeroGrading_iff.mpr (Or.inl (add_zero 0))
      · rw [mul_zero]; exact zero_mem _
    · rw [zero_mul]; exact zero_mem _

/-- A ring concentrated in bidegree `(0, 0̄)`, with zero differential, as a half-graded dg ring
with parameter `k`. -/
def degreeZero (k : ℤ) : HalfGradedDGRing A k where
  hgrading := degreeZeroGrading A
  hd := 0
  hd_mem _ := zero_mem _
  hd_hd _ := rfl
  hd_mul _ _ := by simp

variable {A}

@[simp]
theorem degreeZero_hd (k : ℤ) (a : A) : (degreeZero A k).hd a = 0 := rfl

theorem degreeZero_hgrading (k : ℤ) : (degreeZero A k).hgrading = degreeZeroGrading A := rfl

/-- The differential of the regraded ring of `degreeZero A k` is zero. -/
theorem d_regraded_degreeZero (k : ℤ) (x : (degreeZero A k).Regraded) : d x = 0 := by
  induction x using induction_on with
  | zero => exact d_zero
  | mk p a ha => rw [d_place]; exact (place_congr rfl (degreeZero_hd k a) _ _).trans (place_zero _)
  | add x y hx hy => rw [d_add, hx, hy, add_zero]

/-- The differential of the Hom complexes of the weight dg category of `degreeZero A k` is
zero. -/
theorem d_hom_degreeZero (k : ℤ) {i j : WeightCategory (degreeZero A k).Regraded} (f : i ⟶ j) :
    d f = 0 :=
  Subtype.ext (by rw [WeightCategory.d_val, d_regraded_degreeZero]; rfl)

theorem halfDegree_eq_zero_iff (k n w : ℤ) :
    halfDegree k (n, w) = 0 ↔ w + n * k = 0 ∧ (n : ZMod 2) = 0 := by
  simp [Prod.ext_iff]

/-- A homogeneous morphism of the weight dg category of `degreeZero A k` of degree `n`: it is
zero unless `j - i + n k = 0` and `n` is even, and it is then an element of `A` placed in bidegree
`(n, j - i)`. -/
theorem hom_eq_place (k : ℤ) {i j : WeightCategory (degreeZero A k).Regraded} {n : ℤ}
    {f : i ⟶ j} (hf : f ∈ grading n) :
    ∃ (a : A) (ha : a ∈ (degreeZero A k).hgrading (halfDegree k (n, j.as - i.as))),
      f.1 = (degreeZero A k).place (n, j.as - i.as) a ha := by
  let x : ⨁ p : ℤ × ℤ, ↥(halfGrading (degreeZero A k).hgrading k p) := f.1
  refine ⟨(x (n, j.as - i.as) : A), (x (n, j.as - i.as)).2, ?_⟩
  have hsupp : ∀ p, p ≠ (n, j.as - i.as) → x p = 0 := fun p hp => by
    by_cases h1 : p.1 = n
    · exact f.2 p (fun h2 => hp (Prod.ext h1 h2))
    · exact hf p h1
  change x = DirectSum.of _ (n, j.as - i.as) (x (n, j.as - i.as))
  ext p : 1
  by_cases hp : p = (n, j.as - i.as)
  · subst hp; rw [DirectSum.of_eq_same]
  · rw [hsupp p hp, DirectSum.of_eq_of_ne _ _ _ hp]

theorem hom_eq_zero_of_halfDegree_ne_zero (k : ℤ) {i j : WeightCategory (degreeZero A k).Regraded}
    {n : ℤ} {f : i ⟶ j} (hf : f ∈ grading n) (h : ¬ (j.as - i.as + n * k = 0 ∧ (n : ZMod 2) = 0)) :
    f = 0 := by
  obtain ⟨a, ha, e⟩ := hom_eq_place k hf
  rw [← halfDegree_eq_zero_iff] at h
  rcases mem_degreeZeroGrading_iff.mp ha with h' | rfl
  · exact absurd h' h
  · exact Subtype.ext (e.trans (place_zero _))

end DegreeZero

/-! ### The weight dg category over a field -/

namespace Field

variable (K : Type u) [Field K] (k : ℕ)

/-- The weight dg category of the field `K` in bidegree `(0, 0̄)`, for a differential of
bidegree `(k, 1̄)`. -/
abbrev Cat : Type := WeightCategory (degreeZero K (k : ℤ)).Regraded

variable {K k}

/-- The scalar `c ∈ K`, as an endomorphism of degree `0` of an object of `C`. -/
def scalar (X : Cat K k) (c : K) : X ⟶ X :=
  ⟨(degreeZero K (k : ℤ)).place 0 c (by
      rw [map_zero]; exact mem_degreeZeroGrading_iff.mpr (Or.inl rfl)), by
    rw [sub_self]; exact place_mem_wgrading (H := degreeZero K (k : ℤ)) 0 _⟩

theorem scalar_val (X : Cat K k) (c : K) :
    (scalar X c).1 = (degreeZero K (k : ℤ)).place 0 c (by
      rw [map_zero]; exact mem_degreeZeroGrading_iff.mpr (Or.inl rfl)) := rfl

theorem scalar_mem_grading (X : Cat K k) (c : K) : scalar X c ∈ grading 0 :=
  place_mem_grading (H := degreeZero K (k : ℤ)) 0 _

theorem scalar_comp (X : Cat K k) (c c' : K) : scalar X c ≫ scalar X c' = scalar X (c * c') :=
  WeightCategory.hom_ext (by
    rw [WeightCategory.comp_val, scalar_val, scalar_val, place_mul_place, scalar_val]
    exact place_congr (add_zero 0) (mul_comm c' c) _ _)

theorem scalar_one (X : Cat K k) : scalar X 1 = 𝟙 X :=
  WeightCategory.hom_ext rfl

theorem scalar_zero (X : Cat K k) : scalar X 0 = 0 :=
  WeightCategory.hom_ext ((place_congr rfl rfl _ (zero_mem _)).trans (place_zero _))

theorem scalar_add (X : Cat K k) (c c' : K) : scalar X (c + c') = scalar X c + scalar X c' :=
  WeightCategory.hom_ext (place_add _ _ _)

/-- A morphism `X ⟶ X` of degree `0` is a scalar. -/
theorem exists_eq_scalar {X : Cat K k} {f : X ⟶ X} (hf : f ∈ grading 0) :
    ∃ c : K, f = scalar X c := by
  obtain ⟨a, ha, e⟩ := hom_eq_place (k : ℤ) hf
  exact ⟨a, WeightCategory.hom_ext (e.trans (place_congr (by simp) rfl _ _))⟩

/-- Two integers in `[0, 2k)` which are congruent modulo `2k` in the sense
`r' - r + n k = 0` with `n` even are equal, and `n = 0`. -/
theorem eq_of_lt [NeZero k] {r r' n : ℤ} (hr : 0 ≤ r) (hr' : r < 2 * k) (hs : 0 ≤ r')
    (hs' : r' < 2 * k)
    (h : r' - r + n * k = 0 ∧ (n : ZMod 2) = 0) : n = 0 ∧ r = r' := by
  obtain ⟨h, hn⟩ := h
  obtain ⟨m, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).mp hn
  push_cast at h
  have hk : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hm : m = 0 := by
    rcases lt_trichotomy m 0 with hm | hm | hm
    · have : (m : ℤ) * k ≤ -k := by nlinarith
      nlinarith
    · exact hm
    · have : (m : ℤ) * k ≥ k := by nlinarith
      nlinarith
  subst hm
  constructor <;> linarith

/-! ### The representable modules -/

open CatModule CatModule.DerivedCategory

variable (K k)

/-- The representable dg module `C(i, -)` (the free module on a generator in internal degree `i`
and parity `0̄`). -/
abbrev rep (i : ℤ) : CatModule.{u} (Cat K k) :=
  representableW.{u} (Cat K k) (⟨i⟩ : Cat K k)

/-- The generator `𝟙 ∈ C(i, i)` of `C(i, -)`. -/
abbrev gen (i : ℤ) : (rep K k i).obj ⟨i⟩ := ULift.up (𝟙 _)

theorem isCornerGenerator_rep (i : ℤ) :
    IsCornerGenerator (rep K k i) (DGCategory.Idempotent.id _) 0 (gen K k i) :=
  isCornerGenerator_representableW.{u} _

variable {K k}

theorem d_rep {i : ℤ} {Y : Cat K k} (m : (rep K k i).obj Y) : d m = 0 :=
  ULift.ext _ _ (d_hom_degreeZero (k : ℤ) m.down)

theorem scalar_smul_gen_mem (i : ℤ) (c : K) :
    scalar (⟨i⟩ : Cat K k) c • gen K k i ∈ grading 0 := by
  simpa using CatModule.smul_mem_grading (M := rep K k i) (scalar_mem_grading _ c)
    (isCornerGenerator_rep K k i).mem_grading

/-- Multiplication by `c ∈ K` on `C(i, -)`, the endomorphism sending the generator to `c`. -/
def scalarHom (i : ℤ) (c : K) : rep K k i ⟶ rep K k i :=
  (isCornerGenerator_rep K k i).homOfCocycle _ (scalar_smul_gen_mem i c) (d_rep _)

theorem scalarHom_app_gen (i : ℤ) (c : K) :
    (scalarHom i c).app _ (gen K k i) = scalar (⟨i⟩ : Cat K k) c • gen K k i :=
  (isCornerGenerator_rep K k i).homOfCocycle_app_gen _ _ _

theorem scalarHom_comp (i : ℤ) (c c' : K) :
    scalarHom (k := k) i c' ≫ scalarHom i c = scalarHom i (c * c') := by
  refine (isCornerGenerator_rep K k i).ext_hom ?_
  rw [comp_app, scalarHom_app_gen, Hom.map_smul, scalarHom_app_gen, scalarHom_app_gen,
    ← comp_smul, scalar_comp, mul_comm]

theorem scalarHom_one (i : ℤ) : scalarHom (K := K) (k := k) i 1 = 𝟙 _ :=
  (isCornerGenerator_rep K k i).ext_hom (by rw [scalarHom_app_gen, scalar_one, id_smul]; rfl)

theorem scalarHom_zero (i : ℤ) : scalarHom (K := K) (k := k) i 0 = 0 :=
  (isCornerGenerator_rep K k i).ext_hom (by
    rw [scalarHom_app_gen, scalar_zero, CatModule.zero_smul]; rfl)

theorem scalarHom_add (i : ℤ) (c c' : K) :
    scalarHom (k := k) i (c + c') = scalarHom i c + scalarHom i c' :=
  (isCornerGenerator_rep K k i).ext_hom (by
    rw [scalarHom_app_gen, add_app, scalarHom_app_gen, scalarHom_app_gen, scalar_add,
      CatModule.add_smul])

variable [CatModule.HasDerivedCategory.{u, u} (Cat K k)]

variable (K k) in
/-- The object `k_i = Q C(i, -)` of the derived category. -/
abbrev obj (i : ℤ) : CatModule.DerivedCategory.{u, u} (Cat K k) := Q.obj (rep K k i)

variable (K k) in
/-- The action of `K` on `k_i` by the scalars. -/
def ρ (i : ℤ) : K →+* End (obj K k i) where
  toFun c := Q.map (scalarHom i c)
  map_one' := by rw [scalarHom_one, Q.map_id]; rfl
  map_mul' c c' := by
    rw [End.mul_def, ← Q.map_comp, scalarHom_comp]
  map_zero' := by rw [scalarHom_zero, Q.map_zero]
  map_add' c c' := by rw [scalarHom_add, Q.map_add]

/-! ### Morphisms out of `k_i` -/

/-- Every morphism `k_i ⟶ Q N` is the image of the morphism of dg modules sending the generator
to a cocycle `y ∈ N(i)` of degree `0`. -/
theorem exists_eq_Q_map {i : ℤ} {N : CatModule.{u} (Cat K k)} (f : obj K k i ⟶ Q.obj N) :
    ∃ (y : N.obj ⟨i⟩) (hy : y ∈ grading 0) (hdy : d y = 0),
      f = Q.map ((isCornerGenerator_rep K k i).homOfCocycle y hy hdy) := by
  obtain ⟨φ, rfl⟩ := exists_Q_map_eq (isCornerGenerator_rep K k i).isKProjective f
  refine ⟨φ.app _ (gen K k i), φ.map_mem (isCornerGenerator_rep K k i).mem_grading, ?_, ?_⟩
  · rw [← Hom.map_d, (isCornerGenerator_rep K k i).d_eq_zero, map_zero]
  · exact congrArg Q.map ((isCornerGenerator_rep K k i).ext_hom
      ((isCornerGenerator_rep K k i).homOfCocycle_app_gen _ _ _).symm)

omit [CatModule.HasDerivedCategory (Cat K k)] in
theorem homOfCocycle_zero {i : ℤ} {N : CatModule.{u} (Cat K k)} :
    (isCornerGenerator_rep K k i).homOfCocycle (0 : N.obj ⟨i⟩) (zero_mem _) d_zero = 0 :=
  (isCornerGenerator_rep K k i).ext_hom
    ((isCornerGenerator_rep K k i).homOfCocycle_app_gen _ _ _)

omit [CatModule.HasDerivedCategory (Cat K k)] in
theorem regraded_one_ne_zero : (1 : (degreeZero K (k : ℤ)).Regraded) ≠ 0 := by
  intro h
  have := congrArg (fun x : ⨁ p : ℤ × ℤ, ↥(halfGrading (degreeZero K (k : ℤ)).hgrading k p) =>
    ((x 0 : ↥(halfGrading (degreeZero K (k : ℤ)).hgrading k 0)) : K)) h
  simp only [one_eq_place, place, HalfRegrade.mk, DirectSum.of_eq_same] at this
  exact one_ne_zero this

variable [NeZero k]

variable (K k) in
/-- The shift `k_i⟦n⟧` is the image of the shifted representable module. -/
def objShiftIso (i n : ℤ) : (obj K k i)⟦n⟧ ≅ Q.obj (CatModule.shift n (rep K k i)) :=
  ((Q.commShiftIso n).app (rep K k i)).symm

omit [NeZero k] [CatModule.HasDerivedCategory (Cat K k)] in
theorem d_shift_rep {i n : ℤ} {Y : Cat K k} (m : (CatModule.shift n (rep K k i)).obj Y) :
    d m = 0 := by
  rw [← shift.mk_unmk (n := n) m, shift.d_mk, d_rep, _root_.smul_zero, map_zero]

omit [NeZero k] in
/-- `Hom(k_r, Q (C(i, -)⟦n⟧)) = 0` unless `r - i + n k = 0` with `n` even. -/
theorem hom_eq_zero_of_not {r i n : ℤ} (h : ¬ (r - i + n * k = 0 ∧ (n : ZMod 2) = 0))
    (f : obj K k r ⟶ Q.obj (CatModule.shift n (rep K k i))) : f = 0 := by
  obtain ⟨y, hy, hdy, hf⟩ := exists_eq_Q_map f
  have hg : ((shift.unmk n y).down : (⟨i⟩ : Cat K k) ⟶ ⟨r⟩) ∈ grading n := by
    have := (shift.mem_grading_iff' (n := n)).mp hy
    rw [zero_add] at this
    exact this
  have hg0 := hom_eq_zero_of_halfDegree_ne_zero (k : ℤ) hg h
  have hy0 : y = 0 := by
    have : shift.unmk n y = 0 := ULift.ext _ _ hg0
    rw [← shift.mk_unmk (n := n) y, this, map_zero]
  subst hy0
  rw [hf, homOfCocycle_zero, Q.map_zero]

/-- `Hom(k_r, k_{r'}⟦n⟧) = 0` for `0 ≤ r, r' < 2k` unless `r = r'` and `n = 0`. -/
theorem hom_obj_shift_eq_zero {r r' : ℤ} (hr : 0 ≤ r) (hr' : r < 2 * k) (hs : 0 ≤ r')
    (hs' : r' < 2 * k) (n : ℤ) (h : r ≠ r' ∨ n ≠ 0) (f : obj K k r ⟶ (obj K k r')⟦n⟧) :
    f = 0 := by
  have := hom_eq_zero_of_not (fun h' => by
    obtain ⟨h1, h2⟩ := eq_of_lt hs hs' hr hr' h'
    tauto) (f ≫ (objShiftIso K k r' n).hom)
  rwa [Preadditive.IsIso.comp_right_eq_zero] at this

omit [NeZero k] in
/-- The endomorphisms of `k_r` are the scalars. -/
theorem exists_eq_ρ (r : ℤ) (f : obj K k r ⟶ obj K k r) : ∃ c : K, f = ρ K k r c := by
  obtain ⟨y, hy, hdy, rfl⟩ := exists_eq_Q_map f
  obtain ⟨c, hc⟩ := exists_eq_scalar (X := (⟨r⟩ : Cat K k)) (f := y.down) hy
  refine ⟨c, congrArg Q.map ((isCornerGenerator_rep K k r).ext_hom ?_)⟩
  rw [(isCornerGenerator_rep K k r).homOfCocycle_app_gen, scalarHom_app_gen]
  exact ULift.ext _ _ (hc.trans (Category.id_comp _).symm)

omit [NeZero k] in
theorem not_isZero_obj (r : ℤ) : ¬ IsZero (obj K k r) := by
  intro h
  have h0 : Q.map (𝟙 (rep K k r)) = 0 := by rw [Q.map_id]; exact h.eq_of_src _ _
  have e : 𝟙 (rep K k r) = (isCornerGenerator_rep K k r).homOfCocycle (gen K k r)
      (isCornerGenerator_rep K k r).mem_grading (isCornerGenerator_rep K k r).d_eq_zero :=
    (isCornerGenerator_rep K k r).ext_hom
      ((isCornerGenerator_rep K k r).homOfCocycle_app_gen _ _ _).symm
  rw [e, Q_map_eq_zero_iff (isCornerGenerator_rep K k r).isKProjective,
    (isCornerGenerator_rep K k r).homotopic_zero_iff,
    (isCornerGenerator_rep K k r).homOfCocycle_app_gen] at h0
  obtain ⟨z, -, hz⟩ := h0
  rw [d_rep] at hz
  have := congrArg (fun m : (rep K k r).obj ⟨r⟩ => (m.down.1 : (degreeZero K (k : ℤ)).Regraded)) hz
  exact regraded_one_ne_zero this.symm

omit [NeZero k] in
/-- `Hom(k_r, Q (C(i, -)⟦n⟧))` is spanned over `K` by a single morphism. -/
theorem exists_span_hom (r i n : ℤ) :
    ∃ v : obj K k r ⟶ Q.obj (CatModule.shift n (rep K k i)),
      ∀ w : obj K k r ⟶ Q.obj (CatModule.shift n (rep K k i)), ∃ c : K, w = ρ K k r c ≫ v := by
  by_cases hP : r - i + n * k = 0 ∧ (n : ZMod 2) = 0
  · have hb : (1 : K) ∈ (degreeZero K (k : ℤ)).hgrading (halfDegree k (n, r - i)) :=
      mem_degreeZeroGrading_iff.mpr (Or.inl ((halfDegree_eq_zero_iff _ _ _).mpr hP))
    let b : (representable (⟨i⟩ : Cat K k)).obj ⟨r⟩ :=
      (⟨(degreeZero K (k : ℤ)).place (n, r - i) 1 hb, place_mem_wgrading (n, r - i) hb⟩ :
        (⟨i⟩ : Cat K k) ⟶ ⟨r⟩)
    have hb' : b ∈ grading n := place_mem_grading (n, r - i) hb
    let y₀ : (CatModule.shift n (rep K k i)).obj ⟨r⟩ := shift.mk n (ULift.up b)
    have hy₀ : y₀ ∈ grading 0 := shift.mem_grading_iff.mpr (by rw [zero_add]; exact hb')
    have hdy₀ : d y₀ = 0 := d_shift_rep y₀
    refine ⟨Q.map ((isCornerGenerator_rep K k r).homOfCocycle y₀ hy₀ hdy₀), fun w => ?_⟩
    obtain ⟨y, hy, hdy, rfl⟩ := exists_eq_Q_map w
    have hg : ((shift.unmk n y).down : (⟨i⟩ : Cat K k) ⟶ ⟨r⟩) ∈ grading n := by
      have := (shift.mem_grading_iff' (n := n)).mp hy
      rw [zero_add] at this
      exact this
    obtain ⟨a, ha, e⟩ := hom_eq_place (k : ℤ) hg
    have hya : y = scalar (⟨r⟩ : Cat K k) a • y₀ := by
      apply (shift.unmk (M := rep K k i) (X := ⟨r⟩) n).injective
      rw [shift.unmk_smul (scalar_mem_grading _ a), mul_zero, koszulSign_zero, one_smul]
      refine ULift.ext _ _ (WeightCategory.hom_ext ?_)
      change ((shift.unmk n y).down.1 : (degreeZero K (k : ℤ)).Regraded) =
        (degreeZero K (k : ℤ)).place 0 a _ * (degreeZero K (k : ℤ)).place (n, r - i) 1 hb
      rw [e, place_mul_place]
      exact place_congr (zero_add _).symm (mul_one a).symm _ _
    refine ⟨a, ?_⟩
    change _ = Q.map (scalarHom r a) ≫ _
    rw [← Q.map_comp]
    congr 1
    refine (isCornerGenerator_rep K k r).ext_hom ?_
    rw [(isCornerGenerator_rep K k r).homOfCocycle_app_gen, comp_app, scalarHom_app_gen,
      Hom.map_smul, (isCornerGenerator_rep K k r).homOfCocycle_app_gen, hya]
  · exact ⟨0, fun w => ⟨0, by rw [hom_eq_zero_of_not hP w, comp_zero]⟩⟩

omit [NeZero k] in
/-- `Hom(k_r, k_i⟦n⟧)` is finite-dimensional, of dimension at most `1`, and zero unless
`r - i + n k = 0` with `n` even. -/
theorem finiteDimensional_hom (r i n : ℤ) :
    FiniteDimensional K (HomK (ρ K k r) ((obj K k i)⟦n⟧)) ∧
      HomK.finrankHom (ρ K k r) ((obj K k i)⟦n⟧) ≤ 1 ∧
      (¬ (r - i + n * k = 0 ∧ (n : ZMod 2) = 0) →
        HomK.finrankHom (ρ K k r) ((obj K k i)⟦n⟧) = 0) := by
  let e := HomK.linearEquivOfIso (ρ K k r) (objShiftIso K k i n)
  obtain ⟨v, hv⟩ := exists_span_hom (K := K) (k := k) r i n
  let v' : HomK (ρ K k r) (Q.obj (CatModule.shift n (rep K k i))) := v
  have hspan : ∀ w : HomK (ρ K k r) ((obj K k i)⟦n⟧), ∃ c : K, c • e.symm v' = w := fun w => by
    obtain ⟨c, hc⟩ := hv (e w)
    refine ⟨c, e.injective ?_⟩
    rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
    exact hc.symm
  refine ⟨Module.Finite.of_surjective (LinearMap.toSpanSingleton K _ (e.symm v'))
    fun w => (hspan w).imp fun c hc => hc, finrank_le_one _ hspan, fun hP => ?_⟩
  have : Subsingleton (HomK (ρ K k r) ((obj K k i)⟦n⟧)) :=
      ⟨fun (w w' : obj K k r ⟶ (obj K k i)⟦n⟧) => by
    have h1 := hom_eq_zero_of_not hP (w ≫ (objShiftIso K k i n).hom)
    have h2 := hom_eq_zero_of_not hP (w' ≫ (objShiftIso K k i n).hom)
    rw [Preadditive.IsIso.comp_right_eq_zero] at h1 h2
    exact h1.trans h2.symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- The objects `k_i` have finite `k_r`-cohomology. -/
theorem isFin_obj (r i : ℤ) : HomK.IsFin (ρ K k r) (obj K k i) := by
  refine ⟨fun n => (finiteDimensional_hom r i n).1, ?_⟩
  refine Set.Subsingleton.finite fun n hn n' hn' => ?_
  have h1 := not_not.mp (mt (finiteDimensional_hom (K := K) (k := k) r i n).2.2 hn)
  have h2 := not_not.mp (mt (finiteDimensional_hom (K := K) (k := k) r i n').2.2 hn')
  have hk : (k : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have : n * k = n' * k := by linarith [h1.1, h2.1]
  exact mul_right_cancel₀ hk this

/-! ### Detection of zero objects -/

omit [NeZero k] [CatModule.HasDerivedCategory (Cat K k)] in
/-- The morphism `i ⟶ j` of degree `2m` given by `uᵐ` (the unit `1 ∈ K`), for `i = j + 2km`. -/
theorem exists_unitPow (i j m : ℤ) (h : i = j + 2 * k * m) :
    ∃ (e : (⟨i⟩ : Cat K k) ⟶ ⟨j⟩) (e' : (⟨j⟩ : Cat K k) ⟶ ⟨i⟩), e ∈ grading (2 * m) ∧
      e' ∈ grading (-(2 * m)) ∧ e ≫ e' = 𝟙 _ := by
  have h₁ : (1 : K) ∈ (degreeZero K (k : ℤ)).hgrading (halfDegree k (2 * m, j - i)) :=
    mem_degreeZeroGrading_iff.mpr (Or.inl ((halfDegree_eq_zero_iff _ _ _).mpr
      ⟨by rw [h]; ring, by push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]⟩))
  have h₂ : (1 : K) ∈ (degreeZero K (k : ℤ)).hgrading (halfDegree k (-(2 * m), i - j)) :=
    mem_degreeZeroGrading_iff.mpr (Or.inl ((halfDegree_eq_zero_iff _ _ _).mpr
      ⟨by rw [h]; ring, by push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, neg_zero]⟩))
  refine ⟨⟨_, place_mem_wgrading _ h₁⟩, ⟨_, place_mem_wgrading _ h₂⟩, place_mem_grading _ h₁,
    place_mem_grading _ h₂, WeightCategory.hom_ext ?_⟩
  rw [WeightCategory.comp_val, WeightCategory.id_val, place_mul_place, one_eq_place]
  exact place_congr (by ext <;> simp) (mul_one 1) _ _

omit [CatModule.HasDerivedCategory (Cat K k)] in
/-- A dg module whose values at `0 ≤ r < 2k` are acyclic is acyclic. -/
theorem isAcyclic_of_lt {N : CatModule.{u} (Cat K k)}
    (h : ∀ r : ℤ, 0 ≤ r → r < 2 * k → DG.IsAcyclic (N.obj ⟨r⟩)) : CatModule.IsAcyclic N := by
  intro X
  have hk : (0 : ℤ) < 2 * k := by
    have := Nat.pos_of_ne_zero (NeZero.ne k); omega
  obtain ⟨e, e', he, he', hee'⟩ := exists_unitPow (K := K) (k := k) X.as (X.as % (2 * k))
    (X.as / (2 * k)) (Int.emod_add_mul_ediv X.as (2 * k)).symm
  have hA := h (X.as % (2 * k)) (Int.emod_nonneg _ hk.ne') (Int.emod_lt_of_pos _ hk)
  refine DG.isAcyclic_iff.mpr fun p y hy hdy => ?_
  have hz : e • y ∈ grading (2 * (X.as / (2 * k)) + p) := CatModule.smul_mem_grading he hy
  have hdz : d (e • y) = 0 := by
    rw [CatModule.d_smul_of_d_eq_zero he (d_hom_degreeZero _ e), hdy, CatModule.smul_zero,
      _root_.smul_zero]
  obtain ⟨w, hw, hdw⟩ := hA.exists_d_eq hz hdz
  refine ⟨e' • w, ?_, ?_⟩
  · have := CatModule.smul_mem_grading he' hw
    rwa [show -(2 * (X.as / (2 * k))) + (2 * (X.as / (2 * k)) + p - 1) = p - 1 by ring] at this
  · rw [CatModule.d_smul_of_d_eq_zero he' (d_hom_degreeZero _ e'), hdw, ← comp_smul, hee',
      id_smul, show -(2 * (X.as / (2 * k))) = 2 * -(X.as / (2 * k)) by ring,
      koszulSign_even (even_two_mul _), one_smul]

/-- An object `X` of `D(K)` with `Hom(k_r, X⟦n⟧) = 0` for all `0 ≤ r < 2k` and all `n` is
zero. -/
theorem isZero_of_forall_hom_eq_zero (X : CatModule.DerivedCategory.{u, u} (Cat K k))
    (h : ∀ (r : ℤ), 0 ≤ r → r < 2 * k → ∀ (n : ℤ) (f : obj K k r ⟶ X⟦n⟧), f = 0) :
    IsZero X := by
  obtain ⟨N, ⟨eX⟩⟩ := exists_iso_Q_obj X
  refine IsZero.of_iso ((isZero_Q_obj_iff N).mpr (isAcyclic_of_lt fun r hr0 hr1 => ?_)) eX
  refine DG.isAcyclic_iff.mpr fun p y hy hdy => ?_
  let y' : (CatModule.shift p N).obj ⟨r⟩ := shift.mk p y
  have hy' : y' ∈ grading 0 := shift.mem_grading_iff.mpr (by rwa [zero_add])
  have hdy' : d y' = 0 := by
    change d (shift.mk p y : (CatModule.shift p N).obj ⟨r⟩) = 0
    rw [shift.d_mk, hdy, _root_.smul_zero, map_zero]
  let φ := (isCornerGenerator_rep K k r).homOfCocycle y' hy' hdy'
  have hφ : Q.map φ = 0 := by
    let E : Q.obj (CatModule.shift p N) ≅ X⟦p⟧ :=
      ((Q.commShiftIso p).app N) ≪≫ (shiftFunctor _ p).mapIso eX.symm
    have := congrArg (· ≫ E.inv) (h r hr0 hr1 p (Q.map φ ≫ E.hom))
    simpa using this
  rw [Q_map_eq_zero_iff (isCornerGenerator_rep K k r).isKProjective,
    (isCornerGenerator_rep K k r).homotopic_zero_iff,
    (isCornerGenerator_rep K k r).homOfCocycle_app_gen] at hφ
  obtain ⟨z, hz, hdz⟩ := hφ
  refine ⟨koszulSign p • shift.unmk p z, ?_, ?_⟩
  · have := (shift.mem_grading_iff' (n := p)).mp hz
    rw [show (0 : ℤ) - 1 + p = p - 1 by ring] at this
    exact units_smul_mem_grading _ this
  · have e := congrArg (shift.unmk (M := N) (X := ⟨r⟩) p) hdz
    rw [shift.unmk_d] at e
    rw [d_units_smul, e]
    rfl

/-! ### `K₀` of the compact objects -/

variable (K k) in
/-- The compact objects `D(K)^c` of the derived category of half-graded dg `K`-modules. -/
abbrev compacts : ObjectProperty (CatModule.DerivedCategory.{u, u} (Cat K k)) :=
  compactSubcategory.{u} (CatModule.DerivedCategory.{u, u} (Cat K k))

omit [NeZero k] in
theorem isCompact_obj (i : ℤ) : compacts K k (obj K k i) :=
  isCompact_Q_obj (isCornerGenerator_rep K k i)

/-- Compact objects have finite `k_r`-cohomology. -/
theorem isFin_of_isCompact (r : ℤ) {X : CatModule.DerivedCategory.{u, u} (Cat K k)}
    (hX : compacts K k X) : HomK.IsFin (ρ K k r) X := by
  have hX' : ThickClosure (fun Y : CatModule.DerivedCategory.{u, u} (Cat K k) =>
      ∃ X : Cat K k, Q.obj (representableW.{u} (Cat K k) X) = Y) X := by
    rw [thickClosure_representable_eq_isCompact]; exact hX
  refine thickClosure_le (HomK.isThick_isFin (ρ K k r)) ?_ X hX'
  rintro Y ⟨⟨i⟩, rfl⟩
  exact isFin_obj r i

variable (K k) in
/-- The objects `k_r = Q C(r, -)`, `0 ≤ r < 2k`, form an orthonormal generating family of the
compact objects of `D(K)`. -/
theorem isOrthonormalGenerating :
    IsOrthonormalGenerating (compacts K k) (fun r : Fin (2 * k) => obj K k r)
      (fun r => ρ K k r) where
  mem r := isCompact_obj _
  orth j j' n h f := hom_obj_shift_eq_zero (by positivity) (by exact_mod_cast j.2)
    (by positivity) (by exact_mod_cast j'.2) n
    (h.imp (fun h h' => h (Fin.ext (by exact_mod_cast h'))) id) f
  surj j f := exists_eq_ρ _ f
  nonzero j := not_isZero_obj _
  isFin X hX j := isFin_of_isCompact _ hX
  gen X _ h := isZero_of_forall_hom_eq_zero X fun r hr0 hr1 n f => by
    lift r to ℕ using hr0
    exact h ⟨r, by exact_mod_cast hr1⟩ n f

variable (K k) in
/-- **`K₀` of the compact derived category of half-graded dg modules over a field** (7.4 (d)):
`K₀(D(K)^c)` is free abelian on the classes `[k_r]`, `0 ≤ r < 2k`, the isomorphism being given
by the Euler characteristics `χ_r(X) = ∑ₙ (-1)ⁿ dim Hom(k_r, X⟦n⟧)`. -/
def K0Equiv : K0 (compacts K k).FullSubcategory ≃+ (Fin (2 * k) → ℤ) :=
  (isOrthonormalGenerating K k).K0Equiv

theorem K0Equiv_obj (r : Fin (2 * k)) :
    K0Equiv K k (K0.mk ⟨obj K k r, isCompact_obj _⟩) = Pi.single r 1 :=
  (isOrthonormalGenerating K k).K0Equiv_mk_G r

/-! ### The internal shift of the representable modules -/

omit [CatModule.HasDerivedCategory (Cat K k)] [NeZero k] in
/-- `C(a, b) ≃ C(c, d)` when `b - a = d - c`, the identity on values. -/
def homTransport {a b c d : ℤ} (h : b - a = d - c) :
    ((⟨a⟩ : Cat K k) ⟶ ⟨b⟩) ≃+ ((⟨c⟩ : Cat K k) ⟶ ⟨d⟩) where
  toFun f := ⟨f.1, by rw [show d - c = b - a from h.symm]; exact f.2⟩
  invFun f := ⟨f.1, by rw [h]; exact f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [CatModule.HasDerivedCategory (Cat K k)] [NeZero k] in
/-- The internal shift of a representable module: `C(i, -)⟨s⟩ ≅ C(i - s, -)`. -/
def repInternalShiftIso (i s : ℤ) :
    (internalShiftFunctor (degreeZero K (k : ℤ)) s).obj (rep K k i) ≅ rep K k (i - s) :=
  isoMk (fun Y =>
    { toFun := fun x => ULift.up (homTransport (K := K) (k := k)
        (a := i) (b := Y.as + s) (c := i - s) (d := Y.as) (by ring) x.down)
      invFun := fun x => ULift.up ((homTransport (K := K) (k := k)
        (a := i) (b := Y.as + s) (c := i - s) (d := Y.as) (by ring)).symm x.down)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl })
    Iff.rfl (fun _ => rfl) (fun _ _ => rfl)

variable (K k) in
/-- `k_i⟨s⟩ ≅ k_{i - s}` in `D(K)`. -/
def objInternalShiftIso (i s : ℤ) :
    (CatModule.DerivedCategory.internalShift (degreeZero K (k : ℤ)).Regraded s).obj
      (obj K k i) ≅ obj K k (i - s) :=
  (CatModule.DerivedCategory.QCompInternalShiftIso _ s).app (rep K k i) ≪≫
    Q.mapIso (repInternalShiftIso i s)

omit [NeZero k] in
/-- In `K₀(D(K)^c)`, `qˢ • [k_i] = [k_{i - s}]`. -/
theorem T_smul_mk_obj (i s : ℤ) :
    (LaurentPolynomial.T s : LaurentPolynomial ℤ) •
        K0.mk (⟨obj K k i, isCompact_obj i⟩ : (compacts K k).FullSubcategory) =
      K0.mk ⟨obj K k (i - s), isCompact_obj (i - s)⟩ := by
  rw [CatModule.DerivedCategory.T_smul_mk_compact]
  exact K0.mk_eq_of_iso ((compacts K k).fullyFaithfulι.preimageIso (objInternalShiftIso K k i s))

/-! ### `K₀(D(K)^c)` as a `ℤ[q, q⁻¹]`-module -/

open LaurentPolynomial

omit [NeZero k] in
/-- In `K₀(D(K)^c)`, `[Π X] = -q⁻ᵏ • [X]`. -/
theorem mk_parityShiftCompact (X : (compacts K k).FullSubcategory) :
    K0.mk (parityShiftCompact.{u, u} (degreeZero K (k : ℤ)) X) =
      -((T (-(k : ℤ)) : LaurentPolynomial ℤ) • K0.mk X) := by
  exact HalfGradedDGRing.mk_parityShiftCompact (degreeZero K (k : ℤ)) X

omit [NeZero k] in
/-- `q²ᵏ` acts trivially on `K₀(D(K)^c)`: `Π Π ≅ 𝟭` and `[Π X] = -q⁻ᵏ [X]`. -/
theorem T_two_mul_smul (x : K0 (compacts K k).FullSubcategory) :
    (T (2 * k : ℤ) : LaurentPolynomial ℤ) • x = x := by
  have h : ∀ x : K0 (compacts K k).FullSubcategory,
      (T (-(2 * k : ℤ)) : LaurentPolynomial ℤ) • x = x := by
    intro x
    induction x using K0.induction_on with
    | zero => exact smul_zero _
    | mk X =>
      have e := K0.mk_eq_of_iso ((compacts K k).fullyFaithfulι.preimageIso
        (X := parityShiftCompact.{u, u} (degreeZero K (k : ℤ))
          (parityShiftCompact.{u, u} (degreeZero K (k : ℤ)) X)) (Y := X)
        ((parityShiftDIso.{u, u} (degreeZero K (k : ℤ))).app X.obj))
      rw [mk_parityShiftCompact, mk_parityShiftCompact, _root_.smul_neg, neg_neg, smul_smul,
        ← T_add] at e
      rw [show -(2 * k : ℤ) = -(k : ℤ) + -(k : ℤ) by ring, e]
    | neg x hx => rw [_root_.smul_neg, hx]
    | add x y hx hy => rw [_root_.smul_add, hx, hy]
  conv_lhs => rw [← h x, smul_smul, ← T_add, add_neg_cancel, T_zero, one_smul]

omit [NeZero k] in
theorem T_mul_smul (m : ℤ) (x : K0 (compacts K k).FullSubcategory) :
    (T (2 * k * m : ℤ) : LaurentPolynomial ℤ) • x = x := by
  induction m using Int.induction_on generalizing x with
  | zero => rw [mul_zero, T_zero, one_smul]
  | succ m ih => rw [mul_add, mul_one, T_add, mul_smul, T_two_mul_smul, ih]
  | pred m ih =>
    have := T_two_mul_smul ((T (2 * k * (-(m : ℤ) - 1)) : LaurentPolynomial ℤ) • x)
    rw [smul_smul, ← T_add, show (2 * k : ℤ) + 2 * k * (-(m : ℤ) - 1) = 2 * k * -(m : ℤ) by ring,
      ih] at this
    exact this.symm

variable (K k) in
/-- The class of `k_i` in `K₀(D(K)^c)`. -/
abbrev cls (i : ℤ) : K0 (compacts K k).FullSubcategory :=
  K0.mk (⟨obj K k i, isCompact_obj i⟩ : (compacts K k).FullSubcategory)

omit [NeZero k] in
theorem T_smul_cls (i s : ℤ) :
    (T s : LaurentPolynomial ℤ) • cls K k i = cls K k (i - s) :=
  T_smul_mk_obj i s

omit [NeZero k] in
/-- `[k_i]` only depends on `i` modulo `2k`. -/
theorem cls_eq_of_sub_eq {i j m : ℤ} (h : i - j = 2 * k * m) : cls K k i = cls K k j := by
  rw [← T_mul_smul m (cls K k i), ← h, T_smul_cls, sub_sub_cancel]

omit [NeZero k] in
/-- The class of the parity shift: `[Π X] = -qᵏ [X]` in `K₀(D(K)^c)`. -/
theorem mk_parityShiftCompact' (X : (compacts K k).FullSubcategory) :
    K0.mk (parityShiftCompact.{u, u} (degreeZero K (k : ℤ)) X) =
      -((T (k : ℤ) : LaurentPolynomial ℤ) • K0.mk X) := by
  rw [mk_parityShiftCompact]
  congr 1
  conv_rhs => rw [← T_mul_smul (-1) (K0.mk X)]
  rw [smul_smul, ← T_add, show (k : ℤ) + 2 * k * -1 = -k by ring]

omit [NeZero k] in
/-- `[Π k] = -qᵏ [k]` for the field `k = k_0`. -/
theorem cls_parityShift :
    K0.mk (parityShiftCompact.{u, u} (degreeZero K (k : ℤ)) ⟨obj K k 0, isCompact_obj 0⟩) =
      -((T (k : ℤ) : LaurentPolynomial ℤ) • cls K k 0) :=
  mk_parityShiftCompact' _

variable (k) in
/-- The ideal `(q²ᵏ - 1)` of `ℤ[q, q⁻¹]`. -/
abbrev idealPeriod : Ideal (LaurentPolynomial ℤ) := Ideal.span {T (2 * k : ℤ) - 1}

omit [NeZero k] in
theorem T_sub_one_dvd (m : ℤ) :
    (T (2 * k : ℤ) - 1 : LaurentPolynomial ℤ) ∣ T (2 * k * m) - 1 := by
  have hn : ∀ n : ℕ, (T (2 * k : ℤ) - 1 : LaurentPolynomial ℤ) ∣ T (2 * k * n) - 1 := by
    intro n
    have := sub_dvd_pow_sub_pow (T (2 * k : ℤ) : LaurentPolynomial ℤ) 1 n
    rw [one_pow, T_pow] at this
    rwa [show (2 * k * n : ℤ) = n * (2 * k) by ring]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact hn n
  · have h : (T (2 * k * -(n : ℤ)) - 1 : LaurentPolynomial ℤ) =
        -T (2 * k * -(n : ℤ)) * (T (2 * k * n) - 1) := by
      rw [mul_sub, neg_mul, ← T_add, show 2 * (k : ℤ) * -(n : ℤ) + 2 * k * n = 0 by ring,
        T_zero]
      ring
    rw [h]
    exact Dvd.dvd.mul_left (hn n) _

omit [NeZero k] in
theorem mk_T_eq {a b m : ℤ} (h : a - b = 2 * k * m) :
    Submodule.Quotient.mk (p := idealPeriod k) (T a : LaurentPolynomial ℤ) =
      Submodule.Quotient.mk (T b) := by
  rw [Submodule.Quotient.eq]
  change _ ∈ Ideal.span _
  rw [Ideal.mem_span_singleton, show a = b + 2 * k * m by linarith, T_add, ← mul_sub_one]
  exact Dvd.dvd.mul_left (T_sub_one_dvd m) _

omit [NeZero k] in
theorem C_smul {M : Type*} [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] (a : ℤ) (x : M) :
    (C a : LaurentPolynomial ℤ) • x = a • x := by
  rw [show (C a : LaurentPolynomial ℤ) = a • 1 by
    rw [zsmul_eq_mul, mul_one]; exact map_intCast C a]
  rw [smul_assoc, one_smul]

variable (K k) in
/-- The quotient map `ℤ[q, q⁻¹] → ℤ[q, q⁻¹] ⧸ (q²ᵏ - 1)`. -/
abbrev πP : LaurentPolynomial ℤ →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ ⧸ idealPeriod k :=
  (idealPeriod k).mkQ

variable (K k) in
/-- The additive map `K₀(D(K)^c) → ℤ[q, q⁻¹] ⧸ (q²ᵏ - 1)`, `[k_r] ↦ q⁻ʳ`. -/
def toQuotAdd : K0 (compacts K k).FullSubcategory →+ LaurentPolynomial ℤ ⧸ idealPeriod k :=
  AddMonoidHom.mk' (fun x => ∑ r : Fin (2 * k), K0Equiv K k x r • πP k (T (-(r : ℤ))))
    fun x y => by simp only [map_add, Pi.add_apply, _root_.add_smul, Finset.sum_add_distrib]

theorem toQuotAdd_cls_fin (r : Fin (2 * k)) :
    toQuotAdd K k (cls K k r) = πP k (T (-(r : ℤ))) := by
  change ∑ r' : Fin (2 * k), K0Equiv K k (cls K k r) r' • πP k (T (-(r' : ℤ))) = _
  rw [K0Equiv_obj, Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem toQuotAdd_cls (i : ℤ) : toQuotAdd K k (cls K k i) = πP k (T (-i)) := by
  have hk : (0 : ℤ) < 2 * k := by
    have := Nat.pos_of_ne_zero (NeZero.ne k); omega
  let r : Fin (2 * k) := ⟨(i % (2 * k)).toNat, by
    have := Int.emod_lt_of_pos i hk
    have := Int.emod_nonneg i hk.ne'
    omega⟩
  have hr : ((r : ℕ) : ℤ) = i % (2 * k) := Int.toNat_of_nonneg (Int.emod_nonneg i hk.ne')
  have hir : i - (r : ℕ) = 2 * k * (i / (2 * k)) := by
    rw [hr]; have := Int.emod_add_mul_ediv i (2 * k); linarith
  rw [cls_eq_of_sub_eq hir, toQuotAdd_cls_fin]
  exact mk_T_eq (m := i / (2 * k)) (by linarith)

theorem toQuotAdd_T_smul (s : ℤ) (x : K0 (compacts K k).FullSubcategory) :
    toQuotAdd K k ((T s : LaurentPolynomial ℤ) • x) =
      (T s : LaurentPolynomial ℤ) • toQuotAdd K k x := by
  obtain ⟨v, rfl⟩ := (K0Equiv K k).symm.surjective x
  rw [K0Equiv, IsOrthonormalGenerating.K0Equiv_symm_apply, Finset.smul_sum, map_sum, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_comm, map_zsmul, map_zsmul, smul_comm]
  congr 1
  change toQuotAdd K k ((T s : LaurentPolynomial ℤ) • cls K k r) = _ • toQuotAdd K k (cls K k r)
  rw [T_smul_cls, toQuotAdd_cls, toQuotAdd_cls, ← LinearMap.map_smul, smul_eq_mul, ← T_add]
  congr 2
  ring

variable (K k) in
/-- The `ℤ[q, q⁻¹]`-linear map `K₀(D(K)^c) → ℤ[q, q⁻¹] ⧸ (q²ᵏ - 1)`. -/
def toQuot : K0 (compacts K k).FullSubcategory →ₗ[LaurentPolynomial ℤ]
    LaurentPolynomial ℤ ⧸ idealPeriod k where
  toFun := toQuotAdd K k
  map_add' := map_add _
  map_smul' p x := by
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [_root_.add_smul, map_add, hp, hq, RingHom.id_apply, RingHom.id_apply,
        RingHom.id_apply, _root_.add_smul]
    | C_mul_T n a =>
      rw [RingHom.id_apply, mul_smul, mul_smul, C_smul, C_smul, map_zsmul, toQuotAdd_T_smul]

variable (K k) in
/-- The `ℤ[q, q⁻¹]`-linear map `ℤ[q, q⁻¹] ⧸ (q²ᵏ - 1) → K₀(D(K)^c)`, `p ↦ p • [k]`. -/
def ofQuot : (LaurentPolynomial ℤ ⧸ idealPeriod k) →ₗ[LaurentPolynomial ℤ]
    K0 (compacts K k).FullSubcategory :=
  (idealPeriod k).liftQ (LinearMap.toSpanSingleton _ _ (cls K k 0))
    (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (LinearMap.mem_ker.mpr (by
      rw [LinearMap.toSpanSingleton_apply, _root_.sub_smul, one_smul, T_two_mul_smul,
        sub_self]))))

variable (K k) in
/-- **`K₀(D(K)^c) ≅ ℤ[q]/(q²ᵏ - 1)`** (roadmap 7.4 (d)) as `ℤ[q, q⁻¹]`-modules, where `q` acts on
`K₀` by the internal shift `⟨1⟩` (`qⁿ • [M] = [M⟨n⟩]`) and `[k] ↦ 1` for `k = k_0`, the field
itself. -/
def K0LinearEquiv : K0 (compacts K k).FullSubcategory ≃ₗ[LaurentPolynomial ℤ]
    LaurentPolynomial ℤ ⧸ idealPeriod k :=
  LinearEquiv.ofLinearMap (toQuot K k) (ofQuot K k)
    (Submodule.linearMap_qext _ (LinearMap.ext_ring (by
      change toQuotAdd K k ((1 : LaurentPolynomial ℤ) • cls K k 0) = _
      rw [one_smul, toQuotAdd_cls, neg_zero, T_zero]; rfl)))
    (by
      refine LinearMap.ext fun x => ?_
      obtain ⟨v, rfl⟩ := (K0Equiv K k).symm.surjective x
      rw [K0Equiv, IsOrthonormalGenerating.K0Equiv_symm_apply, map_sum, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [LinearMap.id_apply, map_zsmul]
      congr 1
      change ofQuot K k (toQuotAdd K k (cls K k r)) = cls K k r
      rw [toQuotAdd_cls]
      change (T (-(r : ℤ)) : LaurentPolynomial ℤ) • cls K k 0 = _
      rw [T_smul_cls, zero_sub, neg_neg])

theorem K0LinearEquiv_cls (i : ℤ) : K0LinearEquiv K k (cls K k i) = πP k (T (-i)) :=
  toQuotAdd_cls i

theorem K0LinearEquiv_symm_mk (p : LaurentPolynomial ℤ) :
    (K0LinearEquiv K k).symm (πP k p) = p • cls K k 0 := rfl

theorem cls_neg_fin (i : Fin (2 * k)) :
    cls K k (((-i : Fin (2 * k)) : ℕ) : ℤ) = cls K k (-(i : ℤ)) := by
  have hk : 0 < 2 * k := by have := Nat.pos_of_ne_zero (NeZero.ne k); omega
  rw [Fin.val_neg']
  by_cases hi : (i : ℕ) = 0
  · rw [hi, Nat.sub_zero, Nat.mod_self]
    simp only [Nat.cast_zero, neg_zero]
  · rw [Nat.mod_eq_of_lt (by omega)]
    refine cls_eq_of_sub_eq (m := 1) ?_
    push_cast [Nat.cast_sub i.2.le]
    ring

variable (K k) in
/-- `K₀(D(K)^c)` is free over `ℤ` on the classes `qⁱ [k]`, `0 ≤ i < 2k`. -/
def K0Basis : Module.Basis (Fin (2 * k)) ℤ (K0 (compacts K k).FullSubcategory) :=
  ((Pi.basisFun ℤ (Fin (2 * k))).map (K0Equiv K k).symm.toIntLinearEquiv).reindex
    (Equiv.neg (Fin (2 * k)))

theorem K0Basis_apply (i : Fin (2 * k)) :
    K0Basis K k i = (T (i : ℤ) : LaurentPolynomial ℤ) • cls K k 0 := by
  rw [K0Basis, Module.Basis.reindex_apply, Module.Basis.map_apply, Pi.basisFun_apply,
    Equiv.neg_symm, Equiv.neg_apply]
  change (K0Equiv K k).symm (Pi.single (-i) 1) = _
  rw [AddEquiv.symm_apply_eq, T_smul_cls, zero_sub, ← cls_neg_fin, K0Equiv_obj]

/-! ### The super Grothendieck group over a field -/

variable (k) in
/-- The ideal `(1 + qᵏ)` of `ℤ[q, q⁻¹]`. -/
abbrev idealSuper : Ideal (LaurentPolynomial ℤ) := Ideal.span {1 + T (k : ℤ)}

omit [NeZero k] in
theorem idealPeriod_le_idealSuper : idealPeriod k ≤ idealSuper k := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
  exact ⟨T (k : ℤ) - 1, by rw [show (2 * k : ℤ) = k + k by ring, T_add]; ring⟩

omit [NeZero k] in
theorem T_neg_add_one_mem : (T (-(k : ℤ)) + 1 : LaurentPolynomial ℤ) ∈ idealSuper k :=
  Ideal.mem_span_singleton.mpr ⟨T (-(k : ℤ)), by
    rw [add_mul, one_mul, ← T_add, add_neg_cancel, T_zero, add_comm]⟩

variable (K k) in
/-- The relations `[Π X] - [X]` in `K₀(D(K)^c)`. -/
abbrev parityRel : AddSubgroup (K0 (compacts K k).FullSubcategory) :=
  K0Rel.parityRelations (parityShiftCompact.{u, u} (degreeZero K (k : ℤ)))

omit [NeZero k] in
theorem smul_mem_parityRel (y : K0 (compacts K k).FullSubcategory) :
    (T (-(k : ℤ)) + 1 : LaurentPolynomial ℤ) • y ∈ parityRel K k := by
  induction y using K0.induction_on with
  | zero => rw [_root_.smul_zero]; exact zero_mem _
  | mk X =>
    have : (T (-(k : ℤ)) + 1 : LaurentPolynomial ℤ) • K0.mk X =
        -(K0.mk (parityShiftCompact.{u, u} (degreeZero K (k : ℤ)) X) - K0.mk X) := by
      rw [mk_parityShiftCompact, _root_.add_smul, one_smul]; abel
    rw [this]
    exact neg_mem (AddSubgroup.subset_closure ⟨X, rfl⟩)
  | neg x hx => rw [_root_.smul_neg]; exact neg_mem hx
  | add x y hx hy => rw [_root_.smul_add]; exact add_mem hx hy

variable (K k) in
/-- The additive map `K₀(D(K)^c) → ℤ[q, q⁻¹] ⧸ (1 + qᵏ)`, `p • [k] ↦ p`. -/
def toSuperQuot : K0 (compacts K k).FullSubcategory →+ LaurentPolynomial ℤ ⧸ idealSuper k :=
  (Ideal.Quotient.factor idealPeriod_le_idealSuper).toAddMonoidHom.comp
    (K0LinearEquiv K k).toAddMonoidHom

theorem toSuperQuot_smul_cls (p : LaurentPolynomial ℤ) :
    toSuperQuot K k (p • cls K k 0) = Ideal.Quotient.mk (idealSuper k) p := by
  change Ideal.Quotient.factor idealPeriod_le_idealSuper
    (K0LinearEquiv K k ((K0LinearEquiv K k).symm (πP k p))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem exists_eq_smul_cls (x : K0 (compacts K k).FullSubcategory) :
    ∃ p : LaurentPolynomial ℤ, x = p • cls K k 0 := by
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (K0LinearEquiv K k x)
  exact ⟨p, by rw [← K0LinearEquiv_symm_mk, ← (K0LinearEquiv K k).symm_apply_apply x, ← hp]; rfl⟩

theorem parityRel_le_ker : parityRel K k ≤ (toSuperQuot K k).ker := by
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro _ ⟨X, rfl⟩
  obtain ⟨p, hp⟩ := exists_eq_smul_cls (K0.mk X)
  have h : K0.mk (parityShiftCompact.{u, u} (degreeZero K (k : ℤ)) X) - K0.mk X =
      (-((T (-(k : ℤ)) + 1) * p) : LaurentPolynomial ℤ) • cls K k 0 := by
    rw [mk_parityShiftCompact, hp, _root_.neg_smul, mul_smul, _root_.add_smul, one_smul]; abel
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker, h, toSuperQuot_smul_cls,
    Ideal.Quotient.eq_zero_iff_mem]
  exact neg_mem (Ideal.mul_mem_right _ _ T_neg_add_one_mem)

variable (K k) in
/-- The additive map `K₀(D(K)^c) ⧸ ([Π X] - [X]) → ℤ[q, q⁻¹] ⧸ (1 + qᵏ)`. -/
def superToQuot : (K0 (compacts K k).FullSubcategory ⧸ parityRel K k) →+
    LaurentPolynomial ℤ ⧸ idealSuper k :=
  QuotientAddGroup.lift _ (toSuperQuot K k) parityRel_le_ker

theorem superToQuot_bijective : Function.Bijective (superToQuot K k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨p, rfl⟩ := exists_eq_smul_cls x
    change toSuperQuot K k (p • cls K k 0) = 0 at hz
    rw [toSuperQuot_smul_cls, Ideal.Quotient.eq_zero_iff_mem] at hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [QuotientAddGroup.eq_zero_iff]
    have : c * (1 + T (k : ℤ)) = (T (-(k : ℤ)) + 1) * (c * T (k : ℤ)) := by
      rw [add_mul, one_mul, mul_comm (T _), mul_assoc, ← T_add, add_neg_cancel, T_zero]; ring
    rw [this, mul_smul]
    exact smul_mem_parityRel _
  · intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨QuotientAddGroup.mk (p • cls K k 0), toSuperQuot_smul_cls p⟩

variable (K k) in
/-- **The super Grothendieck group of half-graded dg modules over a field** (roadmap 7.4 (d)):
`K₀^{super}(D(K)^c) ≅ ℤ[q, q⁻¹] ⧸ (1 + qᵏ)`, with `[k] ↦ 1`. It is obtained from the comparison
theorem 7.4 (c) (`DG.HalfGradedDGRing.superK0cEquiv`: the super `K₀` is `K₀ ⧸ ([Π X] = [X])`) and
`K₀(D(K)^c) ≅ ℤ[q, q⁻¹] ⧸ (q²ᵏ - 1)` with `[Π X] = -q^k [X]`. -/
def superK0Equiv : SuperK0c.{u, u} (degreeZero K (k : ℤ)) ≃+
    LaurentPolynomial ℤ ⧸ idealSuper k :=
  (superK0cEquiv.{u, u} (degreeZero K (k : ℤ))).trans
    (AddEquiv.ofBijective (superToQuot K k) superToQuot_bijective)

theorem superK0Equiv_cls :
    superK0Equiv K k (K0Rel.mk ⟨obj K k 0, isCompact_obj 0⟩) = 1 := by
  have := toSuperQuot_smul_cls (K := K) (k := k) 1
  rw [one_smul, map_one] at this
  exact this

variable (K k) in
/-- The field computation agrees with the canonical Laurent-linear quotient map. -/
theorem superK0Equiv_superK0cMk (x : CompactK0.{u, u} (degreeZero K (k : ℤ))) :
    superK0Equiv K k (superK0cMk (degreeZero K (k : ℤ)) x) = toSuperQuot K k x := by
  induction x using K0.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | mk X => rw [superK0cMk_mk]; rfl
  | neg x hx => simp only [map_neg, hx]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (K k) in
/-- The existing field super Grothendieck-group equivalence is Laurent-linear. -/
def superK0LinearEquiv : SuperK0c.{u, u} (degreeZero K (k : ℤ)) ≃ₗ[LaurentPolynomial ℤ]
    LaurentPolynomial ℤ ⧸ idealSuper k :=
  { superK0Equiv K k with
    map_smul' := fun p x => by
      change superK0Equiv K k (p • x) = p • superK0Equiv K k x
      obtain ⟨y, rfl⟩ := superK0cMk_surjective (degreeZero K (k : ℤ)) x
      rw [← map_smul, superK0Equiv_superK0cMk, superK0Equiv_superK0cMk]
      obtain ⟨q, rfl⟩ := exists_eq_smul_cls y
      rw [smul_smul, toSuperQuot_smul_cls, toSuperQuot_smul_cls]
      exact map_mul (Ideal.Quotient.mk (idealSuper k)) p q }

variable (K k) in
/-- The field computation is linear over the quotient coefficient ring itself. -/
def superK0QuotientLinearEquiv : SuperK0c.{u, u} (degreeZero K (k : ℤ)) ≃ₗ[
    LaurentPolynomial ℤ ⧸ idealSuper k] LaurentPolynomial ℤ ⧸ idealSuper k :=
  { superK0Equiv K k with
    map_smul' := fun p x => by
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective p
      exact (superK0LinearEquiv K k).map_smul q x }

variable (K k) in
@[simp]
theorem superK0LinearEquiv_apply (x : SuperK0c.{u, u} (degreeZero K (k : ℤ))) :
    superK0LinearEquiv K k x = superK0Equiv K k x := rfl

variable (K k) in
@[simp]
theorem superK0QuotientLinearEquiv_apply (x : SuperK0c.{u, u} (degreeZero K (k : ℤ))) :
    superK0QuotientLinearEquiv K k x = superK0Equiv K k x := rfl

/-- The quotient-linear field computation sends the regular module to `1`. -/
theorem superK0QuotientLinearEquiv_cls :
    superK0QuotientLinearEquiv K k (K0Rel.mk ⟨obj K k 0, isCompact_obj 0⟩) = 1 :=
  superK0Equiv_cls

end Field

/-! ### The Gaussian integers -/

namespace GaussianQuot

open LaurentPolynomial

/-- The unit `i = √-1` of the Gaussian integers. -/
def unitI : GaussianIntˣ where
  val := ⟨0, 1⟩
  inv := ⟨0, -1⟩
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

/-- `ℤ[q, q⁻¹] → ℤ[√-1]`, `q ↦ √-1`. -/
def evalI : LaurentPolynomial ℤ →+* GaussianInt := eval₂ (Int.castRingHom _) unitI

theorem evalI_C_add (a b : ℤ) : evalI (C a + C b * T 1) = ⟨a, b⟩ := by
  simp only [evalI, map_add, map_mul, eval₂_T, zpow_one, eq_intCast]
  ext <;> simp [unitI]

theorem evalI_surjective : Function.Surjective evalI := fun z =>
  ⟨C z.re + C z.im * T 1, by rw [evalI_C_add]⟩

theorem pow_sub_pow_mem {I : Ideal (LaurentPolynomial ℤ)} {x y : LaurentPolynomial ℤ}
    (h : x - y ∈ I) (n : ℕ) : x ^ n - y ^ n ∈ I := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow x y n
  rw [hc]; exact Ideal.mul_mem_right _ _ h

theorem T_two_mul_sub_mem (q : ℤ) :
    (T (2 * q) - (-1) ^ q.natAbs : LaurentPolynomial ℤ) ∈ Field.idealSuper 2 := by
  have h₁ : (T 2 - (-1) : LaurentPolynomial ℤ) ∈ Field.idealSuper 2 :=
    Ideal.subset_span (by rw [sub_neg_eq_add, add_comm]; rfl)
  have h₂ : (T (-2) - (-1) : LaurentPolynomial ℤ) ∈ Field.idealSuper 2 :=
    Ideal.mem_span_singleton.mpr ⟨T (-2), by
      rw [sub_neg_eq_add, add_mul, one_mul, ← T_add]; norm_num [T_zero]⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg q
  · have := pow_sub_pow_mem h₁ n
    rw [T_pow] at this
    convert this using 2
    · congr 1; ring
    · simp
  · have := pow_sub_pow_mem h₂ n
    rw [T_pow] at this
    convert this using 2
    · congr 1; ring
    · simp

theorem exists_reduce (p : LaurentPolynomial ℤ) :
    ∃ a b : ℤ, p - (C a + C b * T 1) ∈ Field.idealSuper 2 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, b, h⟩ := hp
    obtain ⟨a', b', h'⟩ := hq
    exact ⟨a + a', b + b', by convert add_mem h h' using 1; simp only [map_add]; ring⟩
  | C_mul_T n c =>
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ n = 2 * q + r :=
      ⟨n / 2, n % 2, Int.emod_two_eq_zero_or_one n, by
        rw [add_comm]; exact (Int.emod_add_mul_ediv n 2).symm⟩
    have hm := Ideal.mul_mem_left (Field.idealSuper 2) (C c * T r) (T_two_mul_sub_mem q)
    rcases hr with rfl | rfl
    · refine ⟨c * (-1) ^ q.natAbs, 0, ?_⟩
      convert hm using 1
      simp only [add_zero, T_zero, map_zero, zero_mul, mul_one, map_mul, map_pow, map_neg,
        map_one]
      ring
    · refine ⟨0, c * (-1) ^ q.natAbs, ?_⟩
      convert hm using 1
      rw [T_add]
      simp only [map_zero, zero_add, map_mul, map_pow, map_neg, map_one]
      ring

theorem ker_evalI : RingHom.ker evalI = Field.idealSuper 2 := by
  apply le_antisymm
  · intro p hp
    obtain ⟨a, b, h⟩ := exists_reduce p
    have hJ : Field.idealSuper 2 ≤ RingHom.ker evalI := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp only [evalI, map_add, map_one, eval₂_T]
      ext <;> simp [unitI, pow_two]
    have h' := hJ h
    rw [RingHom.mem_ker, map_sub, hp, zero_sub, neg_eq_zero, evalI_C_add] at h'
    have ha : a = 0 := congrArg Zsqrtd.re h'
    have hb : b = 0 := congrArg Zsqrtd.im h'
    rw [ha, hb, map_zero, zero_mul, add_zero, sub_zero] at h
    exact h
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    simp only [evalI, map_add, map_one, eval₂_T]
    ext <;> simp [unitI, pow_two]

/-- `ℤ[q, q⁻¹] ⧸ (1 + q²) ≅ ℤ[√-1]`, `q ↦ √-1`. -/
def equivGaussianInt : (LaurentPolynomial ℤ ⧸ Field.idealSuper 2) ≃+* GaussianInt :=
  (Ideal.quotEquivOfEq ker_evalI.symm).trans
    (RingHom.quotientKerEquivOfSurjective evalI_surjective)

end GaussianQuot

namespace Field

variable (K : Type u) [Field K] [CatModule.HasDerivedCategory.{u, u} (Cat K 2)]

/-- **For `k = 2`, the super Grothendieck group of half-graded dg modules over a field is the ring
of Gaussian integers**: `K₀^{super}(D(K)^c) ≅ ℤ[q, q⁻¹] ⧸ (1 + q²) ≅ ℤ[√-1]`, with `[k] ↦ 1`
and `q ↦ √-1`. -/
def superK0EquivGaussianInt : SuperK0c.{u, u} (degreeZero K ((2 : ℕ) : ℤ)) ≃+ GaussianInt :=
  (superK0Equiv K 2).trans GaussianQuot.equivGaussianInt.toAddEquiv

theorem superK0EquivGaussianInt_cls :
    superK0EquivGaussianInt K (K0Rel.mk ⟨obj K 2 0, isCompact_obj 0⟩) = 1 := by
  rw [superK0EquivGaussianInt, AddEquiv.trans_apply, superK0Equiv_cls]
  exact map_one GaussianQuot.equivGaussianInt

end Field

end HalfGradedDGRing

end DG

end
