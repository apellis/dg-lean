import DG.HalfGraded.DiagonalBimodule
import DG.Category.Tensor.Hom
import DG.Category.Homotopy.HomComp
import DG.Category.Homotopy.Precomp
import DG.Category.Derived.DGBimodule

/-!
# Hom modules of the diagonally regraded bimodule

Let `M` be a dg `(A, B)`-bimodule and `Mᵈ = DG.Diagonal.bimodule A B M` its diagonal regrading,
a dg bimodule over the weight dg categories `C_A`, `C_B` of the diagonal half-graded dg rings. For
`r : ℤ` let `ι_r : SingleObj A ⥤ C_A` be the inclusion at weight `r` (`DG.Diagonal.inclusion`,
the weight-zero inclusion followed by the shift `k ↦ k + r`), and similarly for `B`.

For every dg module `N` over `C_A`, restricting a cochain `Mᵈ(-, ⟨r⟩) → N` to the weight `r` and
precomposing with the inclusion of `M` as the weight-zero part of `Mᵈ(⟨r⟩, ⟨r⟩)`
(`DG.Diagonal.liftHom`) identifies the Hom complexes

`HOM_{C_A}(Mᵈ(-, ⟨r⟩), N) ≅ HOM_A(M, N(⟨r⟩))`,

compatibly with the actions of `B` (`DG.Diagonal.homRestrictIso`). The inverse extends a cochain
`w` on `M` to the weights `r + 4t` by `x ↦ u_t • w(x)`, `u_t` the periodic unit of degree `-2t`,
and by zero at the other weights (`DG.Diagonal.homExtend`). As `N` varies, this is a natural
isomorphism of dg modules over `SingleObj B`,

`ι_r^* ∘ HOM_{C_A}(Mᵈ, -) ≅ HOM_A(M, -) ∘ ι_r^*`   (`DG.Diagonal.homFunctorRestrictIso`).
-/

open CategoryTheory DirectSum MulOpposite

universe v

noncomputable section

namespace DG.Diagonal

set_option backward.isDefEq.respectTransparency false

/-! ### Preliminaries on the diagonal weight category -/

section Prelim

variable (A : Type v) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The inclusion `SingleObj A ⥤ C_A` at the weight `r`: the weight-zero inclusion followed by the
shift `k ↦ k + r`. -/
abbrev inclusion (r : ℤ) : SingleObj A ⥤ WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded :=
  scalarInclusion A 0 ⋙ WeightCategory.shiftFunctor _ r

/-- The periodic morphism `X ⟶ Y` of `C_A` for `Y - X = 4t`: the unit of `A` placed in bidegree
`(-2t, 4t)`. -/
def periodicHom {X Y : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded} (t : ℤ)
    (h : Y.as - X.as = 4 * t) : X ⟶ Y :=
  ⟨(periodicUnit A t).1, by rw [h]; simpa using (periodicUnit A t).2⟩

theorem periodicHom_mem {X Y : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded} (t : ℤ)
    (h : Y.as - X.as = 4 * t) : periodicHom A t h ∈ DG.grading (-2 * t) :=
  WeightCategory.mem_grading_iff.mpr (WeightCategory.mem_grading_iff.mp (periodicUnit_mem A t))

/-- The periodic morphisms factor every morphism between weights in the same class modulo `4`
through the original scalars. -/
theorem periodicHom_comp {r s t : ℤ} {X Y : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded}
    (hs : X.as - ((inclusion A r).obj (SingleObj.star A)).as = 4 * s)
    (ht : Y.as - ((inclusion A r).obj (SingleObj.star A)).as = 4 * t) (f : X ⟶ Y) :
    periodicHom A s (X := (inclusion A r).obj (SingleObj.star A)) hs ≫ f =
      (inclusion A r).map (show SingleObj.star A ⟶ SingleObj.star A from evaluation (M := A) f.1) ≫
        periodicHom A t (X := (inclusion A r).obj (SingleObj.star A)) ht := by
  let f' : (⟨4 * s⟩ : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) ⟶ ⟨4 * t⟩ :=
    ⟨f.1, by
      have h : Y.as - X.as = 4 * t - 4 * s := by omega
      simpa [h] using f.2⟩
  have e := congrArg Subtype.val (periodicUnit_comp A s t f')
  exact Subtype.ext e

/-- The weight-zero part of the regraded module: `m ∈ Mⁿ` placed in bidegree `(n, 0)`. -/
theorem weightZeroLift_val (M : DGModuleCat.{v} A) {n : ℤ} {m : M} (hm : m ∈ DG.grading n) :
    (weightZeroLift A M m).1 = HalfRegrade.mk (grading M) 2 (n, 0) m
      (by change m ∈ halfGrading (grading M) 2 (n, 0)
          rw [halfGrading_zero_weight]; exact hm) := by
  rw [weightZeroLift_homogeneous A M hm]
  rfl

/-- Every element of weight `4t` of the regraded module is the periodic unit times the weight-zero
lift of its evaluation. -/
theorem eq_periodicUnit_smul (M : DGModuleCat.{v} A) {t : ℤ} {y : RegradedModule M}
    (hy : y ∈ wgrading (4 * t)) :
    y = (periodicUnit A t).1 • (weightZeroLift A M (evaluation y)).1 := by
  refine HalfRegrade.weightGrading_induction
    (P := fun y => y = (periodicUnit A t).1 • (weightZeroLift A M (evaluation y)).1)
    (by simp) (fun n m hm => ?_) (fun x y hx hy => ?_) hy
  · have hm' : m ∈ DG.grading (n + 2 * t) := by
      change m ∈ halfGrading (grading (M : Type v)) 2 (n, 4 * t) at hm
      rwa [halfGrading_supported] at hm
    rw [evaluation_mk, weightZeroLift_val A M hm']
    change _ = (HalfGradedDGRing.ofDGRing A).place (-2 * t, 4 * t) 1 _ • _
    rw [place_smul_mk]
    refine HalfRegrade.mk_congr ?_ (one_smul A m).symm _ _
    ext <;> simp
  · rw [map_add, map_add, AddSubgroup.coe_add, smul_add, ← hx, ← hy]

/-- Evaluation of an element of bidegree `(i, 4t)` has the original degree `i + 2t`. -/
theorem evaluation_mem (M : DGModuleCat.{v} A) {i t w : ℤ} (hw : w = 4 * t)
    {y : RegradedModule M} (hy : y ∈ wgrading w) (hi : y ∈ DG.grading i) :
    evaluation y ∈ DG.grading (i + 2 * t) := by
  subst hw
  exact valueEvaluation_mem A M (x := (⟨y, hy⟩ : Value A M (4 * t))) hi

/-- At weights outside `4ℤ` the regraded module vanishes. -/
theorem eq_zero_of_not_dvd (M : DGModuleCat.{v} A) {w : ℤ} (hw : ¬ ∃ t : ℤ, w = 4 * t)
    {y : RegradedModule M} (hy : y ∈ wgrading w) : y = 0 := by
  exact congrArg Subtype.val ((value_subsingleton A M w hw).elim (⟨y, hy⟩ : Value A M w) 0)

end Prelim

/-! ### The weight-zero lift of a bimodule -/

section Lift

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] (r : ℤ)

theorem mem_wgrading_sub {a b : ℤ} (h : a = b) {y : RegradedModule M} (hy : y ∈ wgrading 0) :
    y ∈ wgrading (a - b) := by
  rw [h, sub_self]
  exact hy

omit [Module Bᵐᵒᵖ M] [DGBimodule A B M] in
/-- The weight-zero lift is compatible with the action of `A`. -/
theorem weightZeroLift_smul [DGModule A M] (a : A) (m : M) :
    (weightZeroLift A (DGModuleCat.of A M) (a • m)).1 =
      (scalarHom A 0 a).1 • (weightZeroLift A (DGModuleCat.of A M) m).1 := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_add a b ha hb =>
    rw [add_smul, map_add, AddSubgroup.coe_add, ha, hb, map_add, WeightCategory.add_val, add_smul]
  | @h_homogeneous n a =>
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add x y hx hy =>
      rw [smul_add, map_add, AddSubgroup.coe_add, hx, hy, map_add, AddSubgroup.coe_add, smul_add]
    | @h_homogeneous i m =>
      rw [weightZeroLift_val A (DGModuleCat.of A M) (smul_mem_grading a.2 m.2),
        weightZeroLift_val A (DGModuleCat.of A M) m.2, scalarHom_homogeneous A 0 n _ a.2,
        place_smul_mk]
      rfl

omit [Module Bᵐᵒᵖ M] [DGBimodule A B M] in
/-- The weight-zero lift commutes with the differentials. -/
theorem weightZeroLift_d [DGModule A M] (m : M) :
    (weightZeroLift A (DGModuleCat.of A M) (d m)).1 =
      d (weightZeroLift A (DGModuleCat.of A M) m).1 := by
  induction m using DG.induction_on with
  | h_zero => simp
  | h_add x y hx hy => rw [d_add, map_add, map_add, AddSubgroup.coe_add, AddSubgroup.coe_add,
      hx, hy, d_add]
  | @h_homogeneous i m =>
    rw [weightZeroLift_val A (DGModuleCat.of A M) (DG.d_mem m.2),
      weightZeroLift_val A (DGModuleCat.of A M) m.2]
    exact (HalfRegrade.mk_congr (by simp) rfl _ _).trans (d_mk (i, 0) (m : M) _).symm

/-- The left module `Mᵈ(-, ⟨r⟩)` over `C_A`. -/
abbrev leftAt : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  (bimodule A B M).left ((inclusion B r).obj (SingleObj.star B))

/-- The inclusion of `M` as the weight-zero part of `Mᵈ(⟨r⟩, ⟨r⟩)`, a morphism of dg modules over
`SingleObj A`. -/
def liftHom : (DGBimodule.catBimodule A B M).left (SingleObj.star B) ⟶
    (CatModule.precomp (inclusion A r)).obj (leftAt A B M r) where
  app _ := AddMonoidHom.mk'
    (fun m => ⟨(weightZeroLift A (DGModuleCat.of A M) m).1,
      mem_wgrading_sub M rfl (weightZeroLift A (DGModuleCat.of A M) m).2⟩)
    (fun m m' => Subtype.ext (by rw [map_add]; rfl))
  map_mem' {_ i m} hm := by
    change (weightZeroLift A (DGModuleCat.of A M) m).1 ∈ DG.grading i
    rw [weightZeroLift_val A (DGModuleCat.of A M) hm]
    exact HalfRegrade.mk_mem_cohGrading (i, 0) _
  map_d' m := Subtype.ext (weightZeroLift_d A M (show M from m))
  map_smul' {_ _} f m := Subtype.ext (weightZeroLift_smul A M (show A from f) (show M from m))

@[simp]
theorem liftHom_app_val (m : M) :
    ((liftHom A B M r).app (SingleObj.star A) m).1 = (weightZeroLift A (DGModuleCat.of A M) m).1 :=
  rfl

/-- The weight-zero lift as an additive map `M →+ Mᵈ(⟨r⟩, ⟨r⟩)`. -/
def liftAddHom : M →+ (leftAt A B M r).obj ((inclusion A r).obj (SingleObj.star A)) :=
  (liftHom A B M r).app (SingleObj.star A)

theorem liftAddHom_mem {i : ℤ} {m : M} (hm : m ∈ DG.grading i) :
    liftAddHom A B M r m ∈ DG.grading i :=
  (liftHom A B M r).map_mem hm

theorem liftAddHom_d (m : M) : liftAddHom A B M r (d m) = d (liftAddHom A B M r m) :=
  (liftHom A B M r).map_d m

/-- The weight-zero lift intertwines the right actions of `B`. -/
theorem liftHom_ract (b : B) (m : M) :
    (bimodule A B M).ract ((inclusion B r).map (show SingleObj.star B ⟶ SingleObj.star B from b))
        ((liftHom A B M r).app (SingleObj.star A) m) =
      (liftHom A B M r).app (SingleObj.star A) (op b • m) := Subtype.ext (by
  change rsmul (weightZeroLift A (DGModuleCat.of A M) m).1 (scalarHom B 0 b).1 =
    (weightZeroLift A (DGModuleCat.of A M) (op b • m)).1
  induction b using DG.induction_on with
  | h_zero => simp
  | h_add a b ha hb =>
    rw [map_add, WeightCategory.add_val, map_add, ha, hb, MulOpposite.op_add, add_smul, map_add]
    rfl
  | @h_homogeneous n b =>
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add x y hx hy => rw [map_add, AddSubgroup.coe_add, map_add, AddMonoidHom.add_apply, hx, hy,
        smul_add, map_add, AddSubgroup.coe_add]
    | @h_homogeneous i m =>
      rw [weightZeroLift_val A (DGModuleCat.of A M) m.2, scalarHom_homogeneous B 0 n _ b.2,
        rsmul_mk_place, weightZeroLift_val A (DGModuleCat.of A M) (op_smul_mem_grading b.2 m.2)]
      rfl)

end Lift

/-! ### Restriction and extension of cochains -/

section Cochains

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] (r : ℤ)
  (N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))

private theorem ks_eq {m n : ℤ} (k : ℤ) (h : m - n = 2 * k) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr ⟨k, by omega⟩

private theorem map_units {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (u : ℤˣ)
    (x : G) : f (u • x) = u • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- Restriction of a cochain `Mᵈ(-, ⟨r⟩) → N` to the weight-zero part of `Mᵈ(⟨r⟩, ⟨r⟩)`, a
cochain `M → N(⟨r⟩)` over `SingleObj A`. -/
def homRestrict (n : ℤ) :
    CatModule.Cochain (leftAt A B M r) N n →+
      CatModule.Cochain ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
        ((CatModule.precomp (inclusion A r)).obj N) n where
  toFun z := (z.precomp (inclusion A r)).comp (CatModule.Cochain.ofHom (liftHom A B M r))
    (zero_add n)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem homRestrict_app (n : ℤ) (z : CatModule.Cochain (leftAt A B M r) N n) (m : M) :
    (homRestrict A B M r N n z).app (SingleObj.star A) m =
      z.app ((inclusion A r).obj (SingleObj.star A)) (liftAddHom A B M r m) := rfl

/-- Whether the weight `X - r` lies in `4ℤ`. -/
abbrev WeightSupported (X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) : Prop :=
  X.as - ((inclusion A r).obj (SingleObj.star A)).as =
    4 * ((X.as - ((inclusion A r).obj (SingleObj.star A)).as) / 4)

theorem not_exists_of_not_supported {X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded}
    (h : ¬ WeightSupported A r X) : ¬ ∃ t : ℤ, X.as - (0 + r) = 4 * t := by
  rintro ⟨t, ht⟩
  exact h (by change X.as - (0 + r) = 4 * ((X.as - (0 + r)) / 4); omega)

/-- The extension of a cochain `w : M → N(⟨r⟩)` over `SingleObj A` to a cochain
`Mᵈ(-, ⟨r⟩) → N`: at a weight `X = r + 4t` it is `x ↦ u_t • w(x)`, `u_t` the periodic unit, and
it is zero at the other weights. -/
def homExtendApp {n : ℤ}
    (w : CatModule.Cochain ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
      ((CatModule.precomp (inclusion A r)).obj N) n)
    (X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :
    (leftAt A B M r).obj X →+ N.obj X :=
  if h : WeightSupported A r X then
    (N.act (periodicHom A _ (X := (inclusion A r).obj (SingleObj.star A)) h)).comp
      ((w.app (SingleObj.star A)).comp ((evaluation (M := M)).comp
        (AddSubgroupClass.subtype _)))
  else 0

theorem homExtendApp_pos {n : ℤ}
    (w : CatModule.Cochain ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
      ((CatModule.precomp (inclusion A r)).obj N) n)
    {X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded} (h : WeightSupported A r X)
    (x : (leftAt A B M r).obj X) :
    homExtendApp A B M r N w X x =
      N.act (periodicHom A _ (X := (inclusion A r).obj (SingleObj.star A)) h)
        (w.app (SingleObj.star A) (evaluation (M := M) x.1)) := by
  unfold homExtendApp
  split
  · rfl
  · contradiction

theorem homExtendApp_neg {n : ℤ}
    (w : CatModule.Cochain ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
      ((CatModule.precomp (inclusion A r)).obj N) n)
    {X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded} (h : ¬ WeightSupported A r X)
    (x : (leftAt A B M r).obj X) : homExtendApp A B M r N w X x = 0 := by
  unfold homExtendApp
  split
  · contradiction
  · rfl

theorem eq_zero_of_not_supported {X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded}
    (h : ¬ WeightSupported A r X) (x : (leftAt A B M r).obj X) : x = 0 :=
  Subtype.ext (eq_zero_of_not_dvd A (DGModuleCat.of A M) (not_exists_of_not_supported A r h) x.2)

theorem homExtendApp_mem {n : ℤ}
    (w : CatModule.Cochain ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
      ((CatModule.precomp (inclusion A r)).obj N) n)
    {X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded} {i : ℤ}
    {x : (leftAt A B M r).obj X} (hx : x ∈ DG.grading i) :
    homExtendApp A B M r N w X x ∈ DG.grading (i + n) := by
  by_cases h : WeightSupported A r X
  · rw [homExtendApp_pos A B M r N w h]
    have he := evaluation_mem A (DGModuleCat.of A M) h x.2 hx
    have hw := w.map_mem (X := SingleObj.star A) he
    have hu := N.act_mem' (periodicHom_mem A _ (X := (inclusion A r).obj (SingleObj.star A)) h) hw
    convert hu using 2
    ring
  · rw [homExtendApp_neg A B M r N w h]
    exact zero_mem _

theorem homExtendApp_smul {n : ℤ}
    (w : CatModule.Cochain ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
      ((CatModule.precomp (inclusion A r)).obj N) n)
    {X Y : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded} {k : ℤ} {f : X ⟶ Y}
    (hf : f ∈ DG.grading k) (x : (leftAt A B M r).obj X) :
    homExtendApp A B M r N w Y (f • x) = koszulSign (n * k) • (f • homExtendApp A B M r N w X x) := by
  by_cases hX : WeightSupported A r X
  · by_cases hY : WeightSupported A r Y
    · rw [homExtendApp_pos A B M r N w hY, homExtendApp_pos A B M r N w hX]
      have hX' : X.as - (0 + r) = 4 * ((X.as - (0 + r)) / 4) := hX
      have hY' : Y.as - (0 + r) = 4 * ((Y.as - (0 + r)) / 4) := hY
      have e1 : evaluation (M := M) (f • x).1 =
          evaluation (M := A) f.1 • evaluation (M := M) x.1 :=
        evaluation_smul A (DGModuleCat.of A M) f.1 x.1
      have hfw : f.1 ∈ wgrading (4 * ((Y.as - (0 + r)) / 4 - (X.as - (0 + r)) / 4)) := by
        have h' : Y.as - X.as = 4 * ((Y.as - (0 + r)) / 4 - (X.as - (0 + r)) / 4) := by omega
        exact (congrArg (fun w : ℤ => (f.1 : (HalfGradedDGRing.ofDGRing A).Regraded) ∈
          wgrading w) h').mp f.2
      have ha := evaluation_mem A (DGModuleCat.of A A) rfl hfw
        (WeightCategory.mem_grading_iff.mp hf)
      have hs := w.map_smul (X := SingleObj.star A) (Y := SingleObj.star A)
        (f := show SingleObj.star A ⟶ SingleObj.star A from evaluation (M := A) f.1) ha
        (evaluation (M := M) x.1)
      have hc := periodicHom_comp A hX hY f
      have hsign : koszulSign (n * (k + 2 * ((Y.as - (0 + r)) / 4 - (X.as - (0 + r)) / 4))) =
          koszulSign (n * k) :=
        ks_eq (n * ((Y.as - (0 + r)) / 4 - (X.as - (0 + r)) / 4)) (by ring)
      calc N.act (periodicHom A _ hY) (w.app (SingleObj.star A) (evaluation (M := M) (f • x).1))
          = N.act (periodicHom A _ hY) (w.app (SingleObj.star A)
              ((evaluation (M := A) f.1) • evaluation (M := M) x.1)) := by rw [e1]
        _ = N.act (periodicHom A _ hY)
              (koszulSign (n * (k + 2 * ((Y.as - (0 + r)) / 4 - (X.as - (0 + r)) / 4))) •
                N.act ((inclusion A r).map
                  (show SingleObj.star A ⟶ SingleObj.star A from evaluation (M := A) f.1))
                  (w.app (SingleObj.star A) (evaluation (M := M) x.1))) := congrArg _ hs
        _ = koszulSign (n * k) • N.act ((inclusion A r).map
                (show SingleObj.star A ⟶ SingleObj.star A from evaluation (M := A) f.1) ≫
                  periodicHom A _ hY)
              (w.app (SingleObj.star A) (evaluation (M := M) x.1)) := by
          rw [map_units, hsign, N.act_comp']
        _ = koszulSign (n * k) • N.act (periodicHom A _ hX ≫ f)
              (w.app (SingleObj.star A) (evaluation (M := M) x.1)) := by
          rw [hc]
        _ = koszulSign (n * k) • (f • N.act (periodicHom A _ hX)
              (w.app (SingleObj.star A) (evaluation (M := M) x.1))) := by
          rw [N.act_comp']
          rfl
    · rw [homExtendApp_neg A B M r N w hY]
      have hf0 : f = 0 := by
        have := weightHom_eq_zero A (s := X.as) (t := Y.as) f (fun ⟨t, ht⟩ => hY (by
          have hX' : X.as - (0 + r) = 4 * ((X.as - (0 + r)) / 4) := hX
          change Y.as - (0 + r) = 4 * ((Y.as - (0 + r)) / 4)
          omega))
        exact this
      subst hf0
      simp
  · have hx0 := eq_zero_of_not_supported A B M r hX x
    subst hx0
    simp

/-- The extension of a cochain `M → N(⟨r⟩)` to a cochain `Mᵈ(-, ⟨r⟩) → N`. -/
def homExtend (n : ℤ) :
    CatModule.Cochain ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
        ((CatModule.precomp (inclusion A r)).obj N) n →+
      CatModule.Cochain (leftAt A B M r) N n where
  toFun w :=
    { app := homExtendApp A B M r N w
      map_mem' := homExtendApp_mem A B M r N w
      map_smul' := homExtendApp_smul A B M r N w }
  map_zero' := by
    ext X x
    by_cases h : WeightSupported A r X
    · rw [homExtendApp_pos A B M r N _ h]
      simp
    · rw [homExtendApp_neg A B M r N _ h]
      rfl
  map_add' w w' := by
    ext X x
    by_cases h : WeightSupported A r X
    · change homExtendApp A B M r N (w + w') X x =
        homExtendApp A B M r N w X x + homExtendApp A B M r N w' X x
      rw [homExtendApp_pos A B M r N _ h, homExtendApp_pos A B M r N _ h,
        homExtendApp_pos A B M r N _ h, CatModule.Cochain.add_apply, map_add]
    · change homExtendApp A B M r N (w + w') X x =
        homExtendApp A B M r N w X x + homExtendApp A B M r N w' X x
      rw [homExtendApp_neg A B M r N _ h, homExtendApp_neg A B M r N _ h,
        homExtendApp_neg A B M r N _ h, add_zero]

/-- The periodic morphism between equal weights is the identity. -/
theorem periodicHom_self {X : WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded} {t : ℤ}
    (h : X.as - X.as = 4 * t) : periodicHom A t h = 𝟙 X := by
  have ht : t = 0 := by omega
  subst ht
  apply Subtype.ext
  change (periodicUnit A 0).1 = 1
  rw [periodicUnit_zero]
  rfl

theorem homRestrict_homExtend (n : ℤ)
    (w : CatModule.Cochain ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
      ((CatModule.precomp (inclusion A r)).obj N) n) :
    homRestrict A B M r N n (homExtend A B M r N n w) = w := by
  ext X m
  obtain rfl : X = SingleObj.star A := rfl
  rw [homRestrict_app]
  have h : WeightSupported A r ((inclusion A r).obj (SingleObj.star A)) := by
    change (0 + r) - (0 + r) = 4 * (((0 + r) - (0 + r)) / 4)
    simp
  change homExtendApp A B M r N w _ _ = _
  rw [homExtendApp_pos A B M r N w h, periodicHom_self A h]
  exact (N.act_id' _ _).trans
    (congrArg (w.app _) (valueEvaluation_weightZeroLift A (DGModuleCat.of A M) m))

theorem homExtend_homRestrict (n : ℤ) (z : CatModule.Cochain (leftAt A B M r) N n) :
    homExtend A B M r N n (homRestrict A B M r N n z) = z := by
  ext X x
  change homExtendApp A B M r N _ X x = _
  by_cases h : WeightSupported A r X
  · rw [homExtendApp_pos A B M r N _ h, homRestrict_app]
    have hx : x = (leftAt A B M r).act
        (periodicHom A _ (X := (inclusion A r).obj (SingleObj.star A)) h)
        ((liftHom A B M r).app (SingleObj.star A) (evaluation (M := M) x.1)) := by
      apply Subtype.ext
      exact eq_periodicUnit_smul A (DGModuleCat.of A M) (y := x.1) (h ▸ x.2)
    have e := z.map_smul (periodicHom_mem A _ h)
      ((liftHom A B M r).app (SingleObj.star A) (evaluation (M := M) x.1))
    rw [koszulSign_even ⟨-(n * ((X.as - ((inclusion A r).obj (SingleObj.star A)).as) / 4)),
      by ring⟩, one_smul] at e
    exact e.symm.trans (congrArg (z.app X) hx.symm)
  · rw [homExtendApp_neg A B M r N _ h, eq_zero_of_not_supported A B M r h x, map_zero]

theorem homRestrict_bijective (n : ℤ) : Function.Bijective (homRestrict A B M r N n) :=
  ⟨Function.LeftInverse.injective (homExtend_homRestrict A B M r N n),
    Function.RightInverse.surjective (homRestrict_homExtend A B M r N n)⟩

theorem homRestrict_δ (n m : ℤ) (z : CatModule.Cochain (leftAt A B M r) N n) :
    homRestrict A B M r N m (CatModule.δ n m z) =
      CatModule.δ n m (homRestrict A B M r N n z) := by
  by_cases hnm : n + 1 = m
  · ext X x
    obtain rfl : X = SingleObj.star A := rfl
    rw [homRestrict_app, CatModule.δ_apply _ _ hnm, CatModule.δ_apply _ _ hnm, homRestrict_app,
      homRestrict_app, show d (liftAddHom A B M r x) = liftAddHom A B M r (d x) from
        (liftAddHom_d A B M r x).symm]
    rfl
  · rw [CatModule.δ_shape _ _ hnm, CatModule.δ_shape _ _ hnm, map_zero]

/-- The weight-zero lift intertwines the right actions of `B` as cochains. -/
theorem liftAddHom_ractCochain {i : ℤ} {b : SingleObj.star B ⟶ SingleObj.star B}
    (hb : b ∈ DG.grading i) (m : M) :
    ((bimodule A B M).ractCochain ((inclusion B r).map b) ((inclusion B r).map_mem_grading hb)).app
        ((inclusion A r).obj (SingleObj.star A)) (liftAddHom A B M r m) =
      liftAddHom A B M r
        (((DGBimodule.catBimodule A B M).ractCochain b hb).app (SingleObj.star A) m) := by
  induction m using DG.induction_on with
  | h_zero => simp only [map_zero]
  | h_add x y hx hy => simp only [map_add, hx, hy]
  | @h_homogeneous j m =>
    rw [CatBimodule.ractCochain_app_of_mem _ (liftAddHom_mem A B M r m.2),
      CatBimodule.ractCochain_app_of_mem _ m.2, map_units]
    exact congrArg _ (liftHom_ract A B M r b m)

theorem homRestrict_comp_ractCochain {i j : ℤ} {b : SingleObj.star B ⟶ SingleObj.star B}
    (hb : b ∈ DG.grading i) (z : CatModule.Cochain (leftAt A B M r) N j) :
    homRestrict A B M r N (i + j) (z.comp ((bimodule A B M).ractCochain ((inclusion B r).map b)
        ((inclusion B r).map_mem_grading hb)) rfl) =
      (homRestrict A B M r N j z).comp
        ((DGBimodule.catBimodule A B M).ractCochain b hb) rfl := by
  ext X m
  obtain rfl : X = SingleObj.star A := rfl
  rw [homRestrict_app, CatModule.Cochain.comp_apply, CatModule.Cochain.comp_apply,
    homRestrict_app, liftAddHom_ractCochain]

/-- The restriction on Hom complexes, `HOM_{C_A}(Mᵈ(-, ⟨r⟩), N) → HOM_A(M, N(⟨r⟩))`. -/
abbrev homRestrictHOM : CatModule.HOM (leftAt A B M r) N →+
    CatModule.HOM ((DGBimodule.catBimodule A B M).left (SingleObj.star B))
      ((CatModule.precomp (inclusion A r)).obj N) :=
  DirectSum.map (homRestrict A B M r N)

theorem homRestrictHOM_mem {i : ℤ} {x : CatModule.HOM (leftAt A B M r) N}
    (hx : x ∈ DG.grading i) : homRestrictHOM A B M r N x ∈ DG.grading i := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨_, (DirectSum.map_of (homRestrict A B M r N) i z).symm⟩

theorem homRestrictHOM_d (x : CatModule.HOM (leftAt A B M r) N) :
    homRestrictHOM A B M r N (d x) = d (homRestrictHOM A B M r N x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
  | of n z =>
    rw [CatModule.HOM.d_of, DirectSum.map_of, DirectSum.map_of, CatModule.HOM.d_of,
      homRestrict_δ]

theorem homRestrictHOM_homAct (b : SingleObj.star B ⟶ SingleObj.star B)
    (x : CatModule.HOM (leftAt A B M r) N) :
    homRestrictHOM A B M r N ((bimodule A B M).homAct N ((inclusion B r).map b) x) =
      (DGBimodule.catBimodule A B M).homAct _ b (homRestrictHOM A B M r N x) := by
  induction b using DG.induction_on with
  | h_zero => simp only [Functor.map_zero, map_zero, AddMonoidHom.zero_apply]
  | h_add b b' hb hb' =>
    rw [Functor.map_add, map_add, AddMonoidHom.add_apply, map_add, hb, hb', map_add,
      AddMonoidHom.add_apply]
  | @h_homogeneous i b =>
    rw [CatBimodule.homAct_of_mem ((inclusion B r).map_mem_grading b.2),
      CatBimodule.homAct_of_mem b.2]
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | of j z =>
      rw [CatModule.HOM.precompCochain_of, map_units, DirectSum.map_of, DirectSum.map_of,
        CatModule.HOM.precompCochain_of, homRestrict_comp_ractCochain]

theorem homRestrictHOM_postcomp {N' : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)}
    (ψ : N ⟶ N') (x : CatModule.HOM (leftAt A B M r) N) :
    homRestrictHOM A B M r N' (CatModule.HOM.postcompCochain (CatModule.Cochain.ofHom ψ) x) =
      CatModule.HOM.postcompCochain
        (CatModule.Cochain.ofHom ((CatModule.precomp (inclusion A r)).map ψ))
        (homRestrictHOM A B M r N x) := by
  have h : (homRestrictHOM A B M r N').comp
        (CatModule.HOM.postcompCochain (CatModule.Cochain.ofHom ψ)) =
      (CatModule.HOM.postcompCochain
        (CatModule.Cochain.ofHom ((CatModule.precomp (inclusion A r)).map ψ))).comp
        (homRestrictHOM A B M r N) := by
    refine DirectSum.addHom_ext fun n z => ?_
    simp only [AddMonoidHom.comp_apply]
    rw [CatModule.HOM.postcompCochain_of, DirectSum.map_of, DirectSum.map_of,
      CatModule.HOM.postcompCochain_of]
    rfl
  exact DFunLike.congr_fun h x

end Cochains

/-! ### The isomorphism of Hom modules -/

section HomIso

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M] (r : ℤ)
  (N : CatModule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded))

/-- The restriction `ι_r^* HOM_{C_A}(Mᵈ, N) ⟶ HOM_A(M, ι_r^* N)` of dg modules over
`SingleObj B`. -/
def homRestrictHom :
    (CatModule.precomp (inclusion B r)).obj ((bimodule A B M).homObj N) ⟶
      (DGBimodule.catBimodule A B M).homObj ((CatModule.precomp (inclusion A r)).obj N) where
  app _ := homRestrictHOM A B M r N
  map_mem' hx := homRestrictHOM_mem A B M r N hx
  map_d' x := homRestrictHOM_d A B M r N x
  map_smul' b x := homRestrictHOM_homAct A B M r N b x

instance : IsIso (homRestrictHom A B M r N) := by
  rw [CatModule.isIso_iff_bijective]
  intro _
  exact ⟨(DirectSum.map_injective _).mpr fun n => (homRestrict_bijective A B M r N n).1,
    (DirectSum.map_surjective _).mpr fun n => (homRestrict_bijective A B M r N n).2⟩

/-- **The Hom modules of the diagonally regraded bimodule**: for every dg module `N` over `C_A`
and every weight `r`, restriction to the weight-zero part of `Mᵈ(⟨r⟩, ⟨r⟩)` is an isomorphism
of dg modules over `SingleObj B`, `ι_r^* HOM_{C_A}(Mᵈ, N) ≅ HOM_A(M, ι_r^* N)`, natural in
`N`. -/
def homFunctorRestrictIso :
    (bimodule A B M).homFunctor ⋙ CatModule.precomp (inclusion B r) ≅
      CatModule.precomp (inclusion A r) ⋙ (DGBimodule.catBimodule A B M).homFunctor :=
  NatIso.ofComponents (fun N => asIso (homRestrictHom A B M r N)) fun {N _} ψ =>
    CatModule.hom_ext fun _ x => homRestrictHOM_postcomp A B M r N ψ x

end HomIso

end DG.Diagonal
