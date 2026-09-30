import DG.Algebra.Regrading

/-!
# The periodization equivalence for dg modules

Let `(B, ℬ, dA)` be a `ℤ/2`-graded dg ring (`DG.IsZMod2DGRing`).

* `DG.Unperiodize.dHom`, `DG.Unperiodize.isZMod2DGModule`: for a dg module `N` over the
  periodization `Periodize ℬ` (`DG.IsPeriodicDGModule`), `N⁰ ⊕ N¹` is a `ℤ/2`-graded dg module
  with the differential `d : N⁰ → N¹` and `u⁻¹ ∘ d : N¹ → N² → N⁰`, `u` the periodicity unit.
* The unit and the counit of `DG.GradedModuleCat.periodizeEquivalence` commute with the
  differentials (`DG.GradedModuleCat.unitHom_d`, `DG.GradedModuleCat.counitHom_d`).
* `DG.GradedModuleCat.ZMod2DGModuleCat ℬ dA` and `DG.GradedModuleCat.PeriodicDGModuleCat ℬ hA`:
  the categories of `ℤ/2`-graded dg `B`-modules and of dg `Periodize ℬ`-modules (morphisms:
  degree-`0` linear maps commuting with the differentials), and
  `DG.GradedModuleCat.periodizeDGEquivalence hA` between them, lifting the equivalence of graded
  module categories.
-/

universe v

noncomputable section

namespace DG

open CategoryTheory DirectSum

variable {B τ : Type*} [Ring B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ZMod 2 → τ}
  [GradedRing ℬ] {dA : B →+ B}

variable {N : Type*} [AddCommGroup N] [Module (Periodize ℬ) N]

namespace Unperiodize

variable {𝒩 : ℤ → AddSubgroup N} [SetLike.GradedSMul (periodizeGrading ℬ) 𝒩]

theorem of_eq_of {j j' : ZMod 2} (h : j = j') {x : lowGrading 𝒩 j} {x' : lowGrading 𝒩 j'}
    (hx : (x : N) = x') : of ℬ 𝒩 j x = of ℬ 𝒩 j' x' := by
  subst h; congr; exact Subtype.ext hx

theorem coe_gsmul (i j : ZMod 2) (b : ℬ i) (x : lowGrading 𝒩 j) :
    (gsmul ℬ 𝒩 i j b x : N) = Periodize.mk ℬ ((i + j).val - j.val) (b : B)
      (by rw [cast_sub_val]; exact b.2) • (x : N) := rfl

/-- The exponent `(j + 1).val - j.val - 1 ∈ {0, -2}` used to bring `d x ∈ N^{j.val + 1}` back to
degree `(j + 1).val`. -/
def dShift (j : ZMod 2) : ℤ := ((j + 1).val : ℤ) - j.val - 1

theorem cast_dShift (j : ZMod 2) : (dShift j : ZMod 2) = 0 := by
  rw [dShift, Int.cast_sub, Int.cast_sub, intCast_val_zmodTwo, intCast_val_zmodTwo, Int.cast_one]
  ring

variable {hA : IsZMod2DGRing ℬ dA} {dN : N →+ N}

theorem dShift_smul_mem (hN : IsPeriodicDGModule hA 𝒩 dN) {j : ZMod 2} {x : N}
    (hx : x ∈ lowGrading 𝒩 j) :
    Periodize.evenOne ℬ (dShift j) (cast_dShift j) • dN x ∈ lowGrading 𝒩 (j + 1) := by
  have := SetLike.GradedSMul.smul_mem (Periodize.mk_mem (ℳ := ℬ) (dShift j)
    (m := (1 : B)) (by rw [cast_dShift]; exact SetLike.GradedOne.one_mem (A := ℬ)))
    (B := 𝒩) (hN.map_mem (show x ∈ 𝒩 (j.val : ℤ) from hx))
  rw [vadd_eq_add, show dShift j + ((j.val : ℤ) + 1) = (j + 1).val by rw [dShift]; ring]
    at this
  exact this

variable (ℬ 𝒩)

/-- The differential of `N⁰ ⊕ N¹` induced by the differential `dN` of a dg module `N` over
`Periodize ℬ`: `d x` for `x ∈ N⁰`, and `u⁻¹ • d x ∈ N⁰` for `x ∈ N¹`, where `u` is the periodicity
unit. -/
def dHom (hN : IsPeriodicDGModule hA 𝒩 dN) : Unperiodize ℬ 𝒩 →+ Unperiodize ℬ 𝒩 :=
  DirectSum.toAddMonoid (β := fun j => ↥(lowGrading 𝒩 j)) fun j =>
    (of ℬ 𝒩 (j + 1)).comp
      (((DistribSMul.toAddMonoidHom N
          (Periodize.evenOne ℬ (dShift j) (cast_dShift j))).comp
        (dN.comp (lowGrading 𝒩 j).subtype)).codRestrict _ fun x => dShift_smul_mem hN x.2)

variable {ℬ 𝒩}

theorem dHom_of (hN : IsPeriodicDGModule hA 𝒩 dN) (j : ZMod 2) (x : lowGrading 𝒩 j) :
    dHom ℬ 𝒩 hN (of ℬ 𝒩 j x) = of ℬ 𝒩 (j + 1) ⟨_, dShift_smul_mem hN x.2⟩ :=
  DirectSum.toAddMonoid_of (β := fun j => ↥(lowGrading 𝒩 j)) _ j x

theorem of_cast {j j' : ZMod 2} (h : j = j') (x : lowGrading 𝒩 j) :
    of ℬ 𝒩 j x = of ℬ 𝒩 j' ⟨x, h ▸ x.2⟩ := of_eq_of h rfl

theorem dHom_dHom (hN : IsPeriodicDGModule hA 𝒩 dN) (y : Unperiodize ℬ 𝒩) :
    dHom ℬ 𝒩 hN (dHom ℬ 𝒩 hN y) = 0 := by
  induction y using induction_on with
  | zero => simp
  | of j x =>
    rw [dHom_of, dHom_of]
    refine (of_eq_of rfl (x' := 0) ?_).trans (map_zero _)
    change Periodize.evenOne ℬ _ _ • dN (Periodize.evenOne ℬ _ _ • dN x) = 0
    rw [hN.d_evenOne_smul, hN.d_d, smul_zero, smul_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', add_zero]

theorem _root_.DG.Periodize.mk_mul_evenOne {n k : ℤ} (hk : (k : ZMod 2) = 0) {b : B}
    (hb : b ∈ ℬ n) : Periodize.mk ℬ n b hb * Periodize.evenOne ℬ k hk =
      Periodize.mk ℬ (n + k) b (by rw [Int.cast_add, hk, add_zero]; exact hb) := by
  rw [Periodize.evenOne, Periodize.mk_mul_mk]; exact Periodize.mk_congr rfl (mul_one b) _ _

theorem of_units_smul (j : ZMod 2) (z : ℤˣ) (x : lowGrading 𝒩 j) :
    z • of ℬ 𝒩 j x = of ℬ 𝒩 j ⟨z • (x : N), by
      rw [Units.smul_def]; exact zsmul_mem x.2 _⟩ := by
  rw [Units.smul_def, ← map_zsmul]; rfl

/-- **`N⁰ ⊕ N¹` of a dg module is a `ℤ/2`-graded dg module.** For a dg module `N` over the
periodization of a `ℤ/2`-graded dg ring `B`, the `ℤ/2`-graded `B`-module `N⁰ ⊕ N¹` with the
differential `DG.Unperiodize.dHom` is a `ℤ/2`-graded dg module. -/
theorem isZMod2DGModule (hN : IsPeriodicDGModule hA 𝒩 dN) :
    IsZMod2DGModule ℬ dA (grading ℬ 𝒩) (dHom ℬ 𝒩 hN) where
  map_mem := by
    intro j y hy
    obtain ⟨x, rfl⟩ := (mem_grading_iff (ℬ := ℬ)).mp hy
    rw [dHom_of]; exact of_mem_grading _ _
  d_d := dHom_dHom hN
  d_smul := by
    intro n b hb y
    induction y using induction_on with
    | zero => simp
    | of j x =>
      rw [smul_of hb, dHom_of, dHom_of, smul_of (hA.map_mem hb), smul_of hb,
        of_cast (add_right_comm (n : ZMod 2) 1 j), of_cast (add_assoc (n : ZMod 2) j 1).symm,
        of_units_smul, ← map_add]
      refine of_eq_of rfl ?_
      change Periodize.evenOne ℬ _ _ •
          dN (Periodize.mk ℬ (((n : ZMod 2) + j).val - j.val) b _ • (x : N)) =
        Periodize.mk ℬ (((n : ZMod 2) + 1 + j).val - j.val) (dA b) _ • (x : N) +
          koszulSign n • (Periodize.mk ℬ (((n : ZMod 2) + (j + 1)).val - (j + 1).val) b _ •
            Periodize.evenOne ℬ (dShift j) (cast_dShift j) • dN x)
      rw [hN.d_smul (Periodize.mk_mem _ _), Periodize.dHom_mk, smul_add, ← mul_smul,
        Periodize.evenOne_mul_mk, smul_comm, ← mul_smul, Periodize.evenOne_mul_mk, ← mul_smul,
        Periodize.mk_mul_evenOne, koszulSign_congr (cast_sub_val (n : ZMod 2) j)]
      congr 2
      · exact Periodize.mk_congr
          (by simp only [dShift]; rw [add_right_comm (n : ZMod 2) 1 j]; ring) rfl _ _
      · congr 1
        exact Periodize.mk_congr (by simp only [dShift]; rw [← add_assoc]; ring) rfl _ _
    | add y y' hy hy' =>
      rw [smul_add, map_add, hy, hy', map_add, smul_add, smul_add, smul_add]
      abel

end Unperiodize

/-! ### Compatibility of the unit and counit with the differentials -/

namespace Periodize

variable {M σ : Type*} [AddCommGroup M] [Module B M] [SetLike σ M] [AddSubgroupClass σ M]
  {ℳ : ZMod 2 → σ} [SetLike.GradedSMul ℬ ℳ]

theorem evenOne_smul_mk {k n : ℤ} (hk : (k : ZMod 2) = 0) {m : M} (hm : m ∈ ℳ n) :
    evenOne ℬ k hk • mk ℳ n m hm =
      mk ℳ (k + n) m (by rw [Int.cast_add, hk, zero_add]; exact hm) := by
  rw [evenOne, mk_smul_mk]; exact mk_congr rfl (one_smul B m) _ _

theorem evenOne_congr {k k' : ℤ} (h : k = k') (hk : (k : ZMod 2) = 0) (hk' : (k' : ZMod 2) = 0) :
    evenOne ℬ k hk = evenOne ℬ k' hk' := by
  subst h; rfl

end Periodize

namespace GradedModuleCat

variable (ℬ) in
/-- The category of `ℤ/2`-graded dg modules over a `ℤ/2`-graded dg ring `(B, ℬ, dA)`. -/
abbrev ZMod2DGModuleCat (dA : B →+ B) :=
  WithDifferential.{v} (𝒜 := ℬ) fun M d => IsZMod2DGModule ℬ dA M.grading d

variable (ℬ) in
/-- The category of (`ℤ`-graded) dg modules over the periodization `Periodize ℬ` of a
`ℤ/2`-graded dg ring `(B, ℬ, dA)`, with the dg ring structure `DG.Periodize.dgRing`. -/
abbrev PeriodicDGModuleCat (hA : IsZMod2DGRing ℬ dA) :=
  WithDifferential.{v} (𝒜 := periodizeGrading ℬ) fun N d => IsPeriodicDGModule hA N.grading d

variable (hA : IsZMod2DGRing ℬ dA)

/-- The periodization functor on dg modules. -/
def periodizeDG : ZMod2DGModuleCat.{v} ℬ dA ⥤ PeriodicDGModuleCat.{v} ℬ hA where
  obj X := ⟨(periodize ℬ).obj X.obj, Periodize.dHom X.obj.grading X.prop.toIsOddDifferential,
    Periodize.isPeriodicDGModule hA X.prop⟩
  map {X Y} f := ⟨(periodize ℬ).map f.hom, fun z => by
    change periodizeHom f.hom (Periodize.dHom _ X.prop.toIsOddDifferential z) =
      Periodize.dHom _ Y.prop.toIsOddDifferential (periodizeHom f.hom z)
    induction z using Periodize.induction_on with
    | zero => simp
    | mk n m hm =>
      rw [Periodize.dHom_mk, periodizeHom_mk, periodizeHom_mk, Periodize.dHom_mk]
      exact Periodize.mk_congr rfl (f.comm m) _ _
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]⟩
  map_id X := WithDifferential.hom_ext ((periodize ℬ).map_id X.obj)
  map_comp f g := WithDifferential.hom_ext ((periodize ℬ).map_comp f.hom g.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The functor `N ↦ N⁰ ⊕ N¹` on dg modules. -/
def unperiodizeDG : PeriodicDGModuleCat.{v} ℬ hA ⥤ ZMod2DGModuleCat.{v} ℬ dA where
  obj X := ⟨(unperiodize ℬ).obj X.obj, Unperiodize.dHom ℬ X.obj.grading X.prop,
    Unperiodize.isZMod2DGModule X.prop⟩
  map {X Y} g := ⟨(unperiodize ℬ).map g.hom, fun y => by
    change Unperiodize.map ℬ _ (Unperiodize.dHom ℬ _ X.prop y) =
      Unperiodize.dHom ℬ _ Y.prop (Unperiodize.map ℬ _ y)
    induction y using Unperiodize.induction_on with
    | zero => erw [map_zero, map_zero]
    | of j x =>
      rw [Unperiodize.dHom_of, Unperiodize.map_of, Unperiodize.map_of, Unperiodize.dHom_of]
      refine Unperiodize.of_eq_of rfl ?_
      change g.hom.hom (Periodize.evenOne ℬ _ _ • X.d x) =
        Periodize.evenOne ℬ _ _ • Y.d (g.hom.hom x)
      rw [map_smul, g.comm]
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add]⟩
  map_id X := WithDifferential.hom_ext ((unperiodize ℬ).map_id X.obj)
  map_comp f g := WithDifferential.hom_ext ((unperiodize ℬ).map_comp f.hom g.hom)

theorem unitHom_d (X : ZMod2DGModuleCat.{v} ℬ dA) (m : X.obj) :
    unitHom X.obj (X.d m) =
      Unperiodize.dHom ℬ _ (Periodize.isPeriodicDGModule hA X.prop) (unitHom X.obj m) := by
  induction m using Decomposition.inductionOn X.obj.grading with
  | zero => simp
  | homogeneous m =>
    obtain ⟨m, hm⟩ := m
    rename_i j
    rw [unitHom_of_mem (X.prop.map_mem hm), unitHom_of_mem hm, Unperiodize.dHom_of]
    refine Unperiodize.of_eq_of rfl ?_
    change Periodize.mk X.obj.grading ((j + 1).val : ℤ) (X.d m) _ =
      Periodize.evenOne ℬ (Unperiodize.dShift j) (Unperiodize.cast_dShift j) •
        Periodize.dHom X.obj.grading X.prop.toIsOddDifferential
          (Periodize.mk X.obj.grading (j.val : ℤ) m (by rwa [intCast_val_zmodTwo]))
    rw [Periodize.dHom_mk, Periodize.evenOne_smul_mk]
    exact Periodize.mk_congr (by rw [Unperiodize.dShift]; ring) rfl _ _
  | add m m' hm hm' => simp only [map_add, hm, hm']

theorem counitHom_d (X : PeriodicDGModuleCat.{v} ℬ hA)
    (z : Periodize (Unperiodize.grading ℬ X.obj.grading)) :
    counitHom X.obj (Periodize.dHom _ (Unperiodize.isZMod2DGModule X.prop).toIsOddDifferential z) =
      X.d (counitHom X.obj z) := by
  induction z using Periodize.induction_on with
  | zero => simp
  | mk n y hy =>
    obtain ⟨x, rfl⟩ := (Unperiodize.mem_grading_iff (ℬ := ℬ)).mp hy
    rw [Periodize.dHom_mk, counitHom_mk, counitHom_mk, Unperiodize.fold_of, Unperiodize.dHom_of,
      Unperiodize.fold_of, X.prop.d_evenOne_smul]
    change Periodize.evenOne ℬ _ _ • Periodize.evenOne ℬ _ _ • X.d x =
      Periodize.evenOne ℬ _ _ • X.d x
    rw [← mul_smul, Periodize.evenOne_mul_evenOne]
    congr 1
    refine Periodize.evenOne_congr ?_ _ _
    rw [Unperiodize.dShift, Int.cast_add, Int.cast_one]
    ring
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]

/-- The unit of the periodization equivalence on dg modules. -/
def periodizeDGUnitIso : 𝟭 (ZMod2DGModuleCat.{v} ℬ dA) ≅ periodizeDG hA ⋙ unperiodizeDG hA :=
  NatIso.ofComponents
    (fun X => WithDifferential.isoMk (unitIso X.obj) (unitHom_d hA X))
    (fun f => WithDifferential.hom_ext ((periodizeUnitIso ℬ).hom.naturality f.hom))

/-- The counit of the periodization equivalence on dg modules. -/
def periodizeDGCounitIso : unperiodizeDG hA ⋙ periodizeDG hA ≅ 𝟭 (PeriodicDGModuleCat.{v} ℬ hA) :=
  NatIso.ofComponents
    (fun X => WithDifferential.isoMk (counitIso X.obj) (counitHom_d hA X))
    (fun f => WithDifferential.hom_ext ((periodizeCounitIso ℬ).hom.naturality f.hom))

/-- **The periodization equivalence for dg modules.** For a `ℤ/2`-graded dg ring `B`, the
category of `ℤ/2`-graded dg `B`-modules is equivalent to the category of dg modules over the
periodization `Periodize ℬ`, by `M ↦ Periodize M` and `N ↦ N⁰ ⊕ N¹`, compatibly with the
periodization equivalence of graded modules `DG.GradedModuleCat.periodizeEquivalence`. -/
def periodizeDGEquivalence : ZMod2DGModuleCat.{v} ℬ dA ≌ PeriodicDGModuleCat.{v} ℬ hA :=
  CategoryTheory.Equivalence.mk (periodizeDG hA) (unperiodizeDG hA) (periodizeDGUnitIso hA)
    (periodizeDGCounitIso hA)

end GradedModuleCat

end DG
