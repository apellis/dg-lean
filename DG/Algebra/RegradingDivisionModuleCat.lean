import DG.Algebra.Regrading
import DG.Graded.RegradingDivisionModuleCat
import DG.Homotopy.ModuleCat

/-!
# The regrading equivalence for differentials of degree `k`

Let `k ≥ 1` and let `(A, 𝒜)` be a `ℤ`-graded ring concentrated in degrees divisible by `k`, with
a differential `dA` of degree `k` satisfying the Leibniz rule with the sign `(-1)^{|a| / k}`
(`DG.IsDivDGRing 𝒜 k dA`). The regraded ring `B = RegradeByDivision 𝒜 k 0 = ⨁ q, A^{q k}` is a
dg ring (`DG.RegradeByDivision.dgRing`), isomorphic to `A` as a ring by `DG.regradeRingEquiv`,
compatibly with the differentials (`DG.regradeRingHom_d`).

* `DG.IsRegradedDGModule hA 𝒩 dN`: a dg module over `B`, stated on data; it is equivalent to
  `DG.DGModule` for the dg ring structure `DG.RegradeByDivision.dgAddCommGroup` of `B`
  (`DG.IsRegradedDGModule.dgModule`, `DG.IsRegradedDGModule.of_dgModule`).
* `DG.GradedModuleCat.DivDGModuleCat 𝒜 k dA`: the category of `ℤ`-graded `A`-modules with a
  differential of degree `k` (`DG.IsDivDGModule`), and
  `DG.GradedModuleCat.RegradedDGModuleCat 𝒜 k hA`: the category of dg `B`-modules on data.
* `DG.GradedModuleCat.regradeDGEquivalence hA :
    DivDGModuleCat 𝒜 k dA ≌ (ZMod k → RegradedDGModuleCat 𝒜 k hA)`: a graded `A`-module with a
  differential of degree `k` is the same as a family, indexed by the residues `r ∈ ℤ/k`, of dg
  `B`-modules, lifting the equivalence of graded module categories
  `DG.GradedModuleCat.regradeEquivalence`.
* `DG.GradedModuleCat.regradedDGModuleCatEquivalence hA :
    RegradedDGModuleCat 𝒜 k hA ≌ DGModuleCat B` (an isomorphism of categories: the unit and
  counit are identities), and the composite
  `DG.GradedModuleCat.divDGModuleCatEquivalence hA :
    DivDGModuleCat 𝒜 k dA ≌ (ZMod k → DGModuleCat B)`.

For `k = 1` this says that the description of dg modules on data agrees with `DG.DGModuleCat`.
-/

universe v

noncomputable section

namespace DG

open CategoryTheory DirectSum

/-! ### Dg modules over the regraded ring, on data -/

section RegradedDGModule

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A] {𝒜 : ℤ → τ}
  [SetLike.GradedMonoid 𝒜] {k : ℤ} {dA : A →+ A}

variable {N : Type*} [AddCommGroup N] [Module (RegradeByDivision 𝒜 k 0) N]

/-- A dg module structure on a `ℤ`-graded module `N` over the regraded ring `⨁ q, A^{q k}` of a
graded ring `(A, 𝒜)` with a differential `dA` of degree `k`: a differential `dN` of degree `1`
with the signed Leibniz rule for the differential `DG.RegradeByDivision.dHom` of the regraded
ring. This is `DG.DGModule` for the dg ring structure `DG.RegradeByDivision.dgAddCommGroup`
(`DG.IsRegradedDGModule.dgModule`, `DG.IsRegradedDGModule.of_dgModule`). -/
structure IsRegradedDGModule (hA : IsDivDGRing 𝒜 k dA) (𝒩 : ℤ → AddSubgroup N) (dN : N →+ N) :
    Prop where
  map_mem : ∀ {n : ℤ} {x : N}, x ∈ 𝒩 n → dN x ∈ 𝒩 (n + 1)
  d_d : ∀ x, dN (dN x) = 0
  d_smul : ∀ {n : ℤ} {b : RegradeByDivision 𝒜 k 0}, b ∈ regradeGrading 𝒜 k 0 n → ∀ x : N,
    dN (b • x) =
      RegradeByDivision.dHom 𝒜 k 0 hA.toIsDifferentialOfDegree b • x + koszulSign n • (b • dN x)

namespace IsRegradedDGModule

variable {hA : IsDivDGRing 𝒜 k dA} {𝒩 : ℤ → AddSubgroup N} {dN : N →+ N}

/-- The dg abelian group structure on `N` given by its grading and `dN`. -/
@[instance_reducible]
def dgAddCommGroup (hN : IsRegradedDGModule hA 𝒩 dN) [Decomposition 𝒩] : DGAddCommGroup N where
  grading := 𝒩
  d := dN
  d_mem' := hN.map_mem
  d_d' := hN.d_d

theorem dgModule (hN : IsRegradedDGModule hA 𝒩 dN) [Decomposition 𝒩]
    [SetLike.GradedSMul (regradeGrading 𝒜 k 0) 𝒩] :
    letI := RegradeByDivision.dgAddCommGroup 𝒜 k 0 hA.toIsDifferentialOfDegree
    letI := hN.dgAddCommGroup
    DGModule (RegradeByDivision 𝒜 k 0) N :=
  letI := RegradeByDivision.dgAddCommGroup 𝒜 k 0 hA.toIsDifferentialOfDegree
  letI := hN.dgAddCommGroup
  { toGradedSMul := inferInstanceAs (SetLike.GradedSMul (regradeGrading 𝒜 k 0) 𝒩)
    d_smul' := fun hb x => hN.d_smul hb x }

theorem of_dgModule [Decomposition 𝒩] (hd : ∀ {n : ℤ} {x : N}, x ∈ 𝒩 n → dN x ∈ 𝒩 (n + 1))
    (hdd : ∀ x, dN (dN x) = 0)
    (h : letI := RegradeByDivision.dgAddCommGroup 𝒜 k 0 hA.toIsDifferentialOfDegree
      letI : DGAddCommGroup N := ⟨𝒩, dN, hd, hdd⟩
      DGModule (RegradeByDivision 𝒜 k 0) N) : IsRegradedDGModule hA 𝒩 dN where
  map_mem := hd
  d_d := hdd
  d_smul := fun hb x => @DGModule.d_smul' _ _ _ _ _ _ _ h _ _ hb x

end IsRegradedDGModule

variable {M σ : Type*} [AddCommGroup M] [Module A M] [SetLike σ M] [AddSubgroupClass σ M]
  {ℳ : ℤ → σ} [SetLike.GradedSMul 𝒜 ℳ] {dM : M →+ M}

/-- Each residue class of a graded module with a differential of degree `k` is a dg module over
the regraded ring, on data (`DG.RegradeByDivision.dgModule`). -/
theorem RegradeByDivision.isRegradedDGModule (hA : IsDivDGRing 𝒜 k dA)
    (hM : IsDivDGModule 𝒜 k dA ℳ dM) (r : ℤ) :
    IsRegradedDGModule hA (regradeGrading ℳ k r)
      (RegradeByDivision.dHom ℳ k r hM.toIsDifferentialOfDegree) where
  map_mem := by
    intro q x hx
    obtain ⟨m, hm, rfl⟩ := RegradeByDivision.mem_regradeGrading_iff.mp hx
    rw [RegradeByDivision.dHom_mk]; exact RegradeByDivision.mk_mem _ _
  d_d := RegradeByDivision.dHom_dHom _
  d_smul := fun hb x =>
    @DGModule.d_smul' _ _ _ (RegradeByDivision.dgAddCommGroup 𝒜 k 0 hA.toIsDifferentialOfDegree) _
      (RegradeByDivision.dgAddCommGroup ℳ k r hM.toIsDifferentialOfDegree) _
      (RegradeByDivision.dgModule hA hM r) _ _ hb x

end RegradedDGModule

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A] {𝒜 : ℤ → τ}
  [GradedRing 𝒜] {k : ℕ} [NeZero k] {dA : A →+ A}

/-! ### The ring isomorphism commutes with the differentials -/

section Ring

variable [IsConcentratedInMultiples 𝒜 k]

/-- The ring isomorphism `A ≃ ⨁ q, A^{q k}` of a graded ring concentrated in degrees divisible
by `k` intertwines a differential of degree `k` with the induced differential of degree `1`. -/
theorem regradeRingHom_d (hd : IsDifferentialOfDegree 𝒜 (k : ℤ) dA) (a : A) :
    regradeRingHom 𝒜 k (dA a) =
      RegradeByDivision.dHom 𝒜 (k : ℤ) 0 hd (regradeRingHom 𝒜 k a) := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    have ha := IsConcentratedInMultiples.mem_ediv k a.2
    rw [regradeRingHom_of_mem ha, RegradeByDivision.dHom_mk,
      regradeRingHom_of_mem (RegradeByDivision.map_mem_succ hd ha)]
  | add a a' ha ha' => rw [map_add, map_add, ha, ha', map_add, map_add]

end Ring

namespace GradedModuleCat

/-! ### The categories -/

variable (𝒜 k) in
/-- The category of `ℤ`-graded modules with a differential of degree `k` over a `ℤ`-graded ring
`(A, 𝒜)` with a differential `dA` of degree `k` (`DG.IsDivDGModule`). -/
abbrev DivDGModuleCat (dA : A →+ A) :=
  WithDifferential.{v} (𝒜 := 𝒜) fun M d => IsDivDGModule 𝒜 (k : ℤ) dA M.grading d

variable (𝒜 k) in
/-- The category of dg modules over the regraded ring `⨁ q, A^{q k}` (with the dg ring structure
`DG.RegradeByDivision.dgRing`), on data. -/
abbrev RegradedDGModuleCat (hA : IsDivDGRing 𝒜 (k : ℤ) dA) :=
  WithDifferential.{v} (𝒜 := regradeGrading 𝒜 (k : ℤ) 0) fun N d =>
    IsRegradedDGModule hA N.grading d

variable (hA : IsDivDGRing 𝒜 (k : ℤ) dA)

/-! ### The residue classes of a module with a differential of degree `k` -/

omit [AddSubgroupClass τ A] [GradedRing 𝒜] [NeZero k] in
theorem regradeMapAddHom_d (r : ZMod k) {X Y : DivDGModuleCat.{v} 𝒜 k dA} (f : X ⟶ Y)
    (x : RegradeByDivision X.obj.grading (k : ℤ) (r.val : ℤ)) :
    regradeMapAddHom r f.hom
        (RegradeByDivision.dHom _ _ _ X.prop.toIsDifferentialOfDegree x) =
      RegradeByDivision.dHom _ _ _ Y.prop.toIsDifferentialOfDegree
        (regradeMapAddHom r f.hom x) := by
  induction x using RegradeByDivision.induction_on with
  | zero => simp
  | mk q m hm =>
    rw [RegradeByDivision.dHom_mk, regradeMapAddHom_mk, regradeMapAddHom_mk,
      RegradeByDivision.dHom_mk]
    exact RegradeByDivision.mk_congr rfl (f.comm m) _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The residue class `r` of a graded module with a differential of degree `k`, as a dg module
over the regraded ring. -/
def regradeDGFunctor (r : ZMod k) :
    DivDGModuleCat.{v} 𝒜 k dA ⥤ RegradedDGModuleCat.{v} 𝒜 k hA where
  obj X := ⟨regradeObj 𝒜 k r X.obj,
    RegradeByDivision.dHom X.obj.grading (k : ℤ) (r.val : ℤ) X.prop.toIsDifferentialOfDegree,
    RegradeByDivision.isRegradedDGModule hA X.prop (r.val : ℤ)⟩
  map f := ⟨regradeMap r f.hom, regradeMapAddHom_d r f⟩
  map_id X := WithDifferential.hom_ext ((regradeFunctor 𝒜 k r).map_id X.obj)
  map_comp f g := WithDifferential.hom_ext ((regradeFunctor 𝒜 k r).map_comp f.hom g.hom)

/-- The functor from graded modules with a differential of degree `k` to families, indexed by
`ℤ/k`, of dg modules over the regraded ring: the residue classes. -/
def regradeDG : DivDGModuleCat.{v} 𝒜 k dA ⥤ (ZMod k → RegradedDGModuleCat.{v} 𝒜 k hA) :=
  Functor.pi' fun r => regradeDGFunctor hA r

/-! ### The direct sum of a family of dg modules over the regraded ring -/

section Unregrade

variable {hA} (N : ZMod k → RegradedDGModuleCat.{v} 𝒜 k hA)

/-- The differential of `⨁ r, N r` for a family `N` of dg modules over the regraded ring: the
direct sum of the differentials. -/
def unregradeD :
    (⨁ r : ZMod k, ((N r).obj : Type v)) →+ ⨁ r : ZMod k, ((N r).obj : Type v) :=
  DirectSum.map fun r => (N r).d

omit [NeZero k] in
theorem unregradeD_apply (x : ⨁ r : ZMod k, ((N r).obj : Type v)) (r : ZMod k) :
    unregradeD N x r = (N r).d (x r) :=
  DirectSum.map_apply _ _ _

omit [NeZero k] in
theorem unregradeD_of (r : ZMod k) (y : (N r).obj) :
    unregradeD N (DirectSum.of (fun r => ((N r).obj : Type v)) r y) =
      DirectSum.of (fun r => ((N r).obj : Type v)) r ((N r).d y) :=
  DirectSum.map_of _ _ _

omit [NeZero k] in
theorem units_smul_apply (u : ℤˣ) (x : ⨁ r : ZMod k, ((N r).obj : Type v)) (r : ZMod k) :
    (u • x) r = u • x r := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [one_smul, one_smul]
  · rw [Units.neg_smul, Units.neg_smul, one_smul, one_smul]; rfl

variable [IsConcentratedInMultiples 𝒜 k]

/-- **The direct sum of a family of dg modules over the regraded ring has a differential of
degree `k`.** For a family `N` of dg modules over `⨁ q, A^{q k}` indexed by `ℤ/k`, the graded
`A`-module `⨁ r, N r` (`DG.GradedModuleCat.unregradeObj`) with the direct sum of the
differentials satisfies `DG.IsDivDGModule`. -/
theorem isDivDGModule_unregrade :
    IsDivDGModule 𝒜 (k : ℤ) dA (unregradeGrading fun r => (N r).obj) (unregradeD N) where
  map_mem := by
    rintro n _ ⟨y, hy, rfl⟩
    have hk : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne k)
    have h : unregradeD N (DirectSum.of (fun r => ((N r).obj : Type v)) (n : ZMod k) y) ∈
        unregradeGrading (fun r => (N r).obj) (n + k) := by
      rw [unregradeD_of]
      exact of_mem_unregradeGrading (fun r => (N r).obj)
        (by rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero])
        (by rw [show n + (k : ℤ) = n + 1 * k by ring, Int.add_mul_ediv_right _ _ hk])
        ((N _).prop.map_mem hy)
    exact h
  d_d := fun x => DirectSum.ext fun r => by
    rw [unregradeD_apply, unregradeD_apply, (N r).prop.d_d, DirectSum.zero_apply]
  d_smul := by
    intro q a ha x
    have ha' : a ∈ 𝒜 (q * (k : ℤ) + 0) := by rwa [add_zero]
    refine DirectSum.ext fun r => ?_
    rw [DirectSum.add_apply, units_smul_apply, unregradeD_apply, unregrade_smul_def,
      unregrade_smul_def, unregrade_smul_def, DirectSum.smul_apply, DirectSum.smul_apply,
      DirectSum.smul_apply, unregradeD_apply,
      regradeRingHom_d hA.toIsDifferentialOfDegree, regradeRingHom_of_mem ha']
    exact (N r).prop.d_smul (RegradeByDivision.mk_mem q ha') (x r)

variable (hA) in
/-- The functor from families, indexed by `ℤ/k`, of dg modules over the regraded ring to graded
`A`-modules with a differential of degree `k`: `N ↦ ⨁ r, N r`. -/
def unregradeDG : (ZMod k → RegradedDGModuleCat.{v} 𝒜 k hA) ⥤ DivDGModuleCat.{v} 𝒜 k dA where
  obj N := ⟨unregradeObj fun r => (N r).obj, unregradeD N, isDivDGModule_unregrade N⟩
  map {N N'} g := ⟨unregradeMap fun r => (g r).hom, fun x => DirectSum.ext fun r => by
    change unregradeMapAddHom (N := fun r => (N r).obj) (N' := fun r => (N' r).obj)
        (fun r => (g r).hom) (unregradeD N x) r =
      unregradeD N' (unregradeMapAddHom (N := fun r => (N r).obj) (N' := fun r => (N' r).obj)
        (fun r => (g r).hom) x) r
    rw [unregradeMapAddHom_apply, unregradeD_apply, unregradeD_apply, unregradeMapAddHom_apply]
    exact (g r).comm (x r)⟩
  map_id N := WithDifferential.hom_ext ((unregrade 𝒜 k).map_id fun r => (N r).obj)
  map_comp {N₁ N₂ N₃} f g := WithDifferential.hom_ext
    ((unregrade 𝒜 k).map_comp (X := fun r => (N₁ r).obj) (Y := fun r => (N₂ r).obj)
      (Z := fun r => (N₃ r).obj) (fun r => (f r).hom) (fun r => (g r).hom))

end Unregrade

/-! ### The equivalence -/

section Equivalence

variable [IsConcentratedInMultiples 𝒜 k]

/-- The unit of the regrading equivalence commutes with the differentials
(`DG.residueEquiv_d`). -/
theorem regradeUnit_d (X : DivDGModuleCat.{v} 𝒜 k dA) (m : X.obj) :
    (regradeUnitIsoApp X.obj).hom.hom (X.d m) =
      unregradeD (fun r => (regradeDGFunctor hA r).obj X) ((regradeUnitIsoApp X.obj).hom.hom m) :=
  residueEquiv_d X.obj.grading k X.prop.toIsDifferentialOfDegree m

omit [NeZero k] [IsConcentratedInMultiples 𝒜 k] in
theorem counitAddHom_dHom_mk (N : ZMod k → RegradedDGModuleCat.{v} 𝒜 k hA) (r : ZMod k)
    (hd : IsDifferentialOfDegree (unregradeGrading fun r => (N r).obj) (k : ℤ) (unregradeD N))
    {q : ℤ} {x : ⨁ r : ZMod k, ((N r).obj : Type v)}
    (hx : x ∈ unregradeGrading (fun r => (N r).obj) (q * k + (r.val : ℤ))) :
    counitAddHom (fun r => (N r).obj) r
        (RegradeByDivision.dHom _ _ _ hd (RegradeByDivision.mk _ _ _ q x hx)) =
      (N r).d (counitAddHom (fun r => (N r).obj) r (RegradeByDivision.mk _ _ _ q x hx)) := by
  rw [RegradeByDivision.dHom_mk, counitAddHom_mk, counitAddHom_mk, unregradeD_apply]

/-- The counit of the regrading equivalence commutes with the differentials. -/
theorem counitAddHom_d (N : ZMod k → RegradedDGModuleCat.{v} 𝒜 k hA) (r : ZMod k)
    (z : RegradeByDivision (unregradeGrading fun r => (N r).obj) (k : ℤ) (r.val : ℤ)) :
    counitAddHom (fun r => (N r).obj) r
        (RegradeByDivision.dHom _ _ _ (isDivDGModule_unregrade N).toIsDifferentialOfDegree z) =
      (N r).d (counitAddHom (fun r => (N r).obj) r z) := by
  have hd := (isDivDGModule_unregrade (dA := dA) N).toIsDifferentialOfDegree
  have key : (counitAddHom (fun r => (N r).obj) r).comp (RegradeByDivision.dHom _ _ _ hd) =
      (N r).d.comp (counitAddHom (fun r => (N r).obj) r) :=
    DirectSum.addHom_ext fun _ x => counitAddHom_dHom_mk hA N r hd x.2
  exact DFunLike.congr_fun key z

/-- The unit of the regrading equivalence on modules with a differential of degree `k`. -/
def regradeDGUnitIso : 𝟭 (DivDGModuleCat.{v} 𝒜 k dA) ≅ regradeDG hA ⋙ unregradeDG hA :=
  NatIso.ofComponents
    (fun X => WithDifferential.isoMk (regradeUnitIsoApp X.obj) (regradeUnit_d hA X))
    (fun f => WithDifferential.hom_ext ((regradeUnitIso 𝒜 k).hom.naturality f.hom))

/-- The counit of the regrading equivalence on modules with a differential of degree `k`. -/
def regradeDGCounitIso :
    unregradeDG hA ⋙ regradeDG hA ≅ 𝟭 (ZMod k → RegradedDGModuleCat.{v} 𝒜 k hA) :=
  NatIso.ofComponents
    (fun N => Pi.isoMk fun r =>
      WithDifferential.isoMk (regradeCounitIsoApp (fun r => (N r).obj) r) (counitAddHom_d hA N r))
    (fun {N N'} g => funext fun r => WithDifferential.hom_ext
      (congrFun ((regradeCounitIso 𝒜 k).hom.naturality (X := fun r => (N r).obj)
        (Y := fun r => (N' r).obj) fun r => (g r).hom) r))

/-- **The regrading equivalence for differentials of degree `k`.** For a `ℤ`-graded ring `A`
concentrated in degrees divisible by `k ≥ 1`, with a differential of degree `k` satisfying the
Leibniz rule with the sign `(-1)^{|a| / k}`, the category of `ℤ`-graded `A`-modules with a
differential of degree `k` is equivalent to the category of families, indexed by `ℤ/k`, of dg
modules over the regraded dg ring `⨁ q, A^{q k}`, compatibly with the equivalence of graded
module categories `DG.GradedModuleCat.regradeEquivalence`. -/
def regradeDGEquivalence :
    DivDGModuleCat.{v} 𝒜 k dA ≌ (ZMod k → RegradedDGModuleCat.{v} 𝒜 k hA) :=
  CategoryTheory.Equivalence.mk (regradeDG hA) (unregradeDG hA) (regradeDGUnitIso hA)
    (regradeDGCounitIso hA)

end Equivalence

/-! ### Comparison with `DGModuleCat` -/

section DGModuleCat

/-- The category `DGModuleCat (⨁ q, A^{q k})` of dg modules over the regraded ring, for the dg
structure `DG.RegradeByDivision.dgAddCommGroup`. -/
abbrev RegradeDGModuleCat : Type _ :=
  letI := RegradeByDivision.dgAddCommGroup 𝒜 (k : ℤ) 0 hA.toIsDifferentialOfDegree
  DGModuleCat.{v} (RegradeByDivision 𝒜 (k : ℤ) 0)

/-- A dg module over the regraded ring on data, as an object of `DGModuleCat`. -/
def regradedToDGModuleCatObj (X : RegradedDGModuleCat.{v} 𝒜 k hA) : RegradeDGModuleCat.{v} hA :=
  letI := RegradeByDivision.dgAddCommGroup 𝒜 (k : ℤ) 0 hA.toIsDifferentialOfDegree
  letI := X.prop.dgAddCommGroup
  haveI := X.prop.dgModule
  DGModuleCat.of (RegradeByDivision 𝒜 (k : ℤ) 0) X.obj

/-- The functor from dg modules over the regraded ring on data to `DGModuleCat`: the identity on
underlying types, gradings, differentials and maps. -/
def regradedToDGModuleCat : RegradedDGModuleCat.{v} 𝒜 k hA ⥤ RegradeDGModuleCat.{v} hA where
  obj X := regradedToDGModuleCatObj hA X
  map {X Y} f :=
    letI := RegradeByDivision.dgAddCommGroup 𝒜 (k : ℤ) 0 hA.toIsDifferentialOfDegree
    letI := X.prop.dgAddCommGroup
    letI := Y.prop.dgAddCommGroup
    haveI := X.prop.dgModule
    haveI := Y.prop.dgModule
    DGModuleCat.ofHom (M := X.obj) (N := Y.obj)
      { toLinearMap := f.hom.hom
        map_mem' := fun hm => f.hom.map_mem hm
        map_d' := f.comm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A dg module over the regraded ring, as a dg module on data. -/
def dgModuleCatToRegradedObj (M : RegradeDGModuleCat.{v} hA) : RegradedDGModuleCat.{v} 𝒜 k hA :=
  letI := RegradeByDivision.dgAddCommGroup 𝒜 (k : ℤ) 0 hA.toIsDifferentialOfDegree
  haveI : SetLike.GradedSMul (regradeGrading 𝒜 (k : ℤ) 0) (DGAddCommGroup.grading (M := M)) :=
    DGModule.toGradedSMul (A := RegradeByDivision 𝒜 (k : ℤ) 0) (M := M)
  { obj := GradedModuleCat.of (regradeGrading 𝒜 (k : ℤ) 0) M (DGAddCommGroup.grading (M := M))
    d := d
    prop :=
      { map_mem := fun hm => d_mem hm
        d_d := fun x => d_d x
        d_smul := fun hb x => DGModule.d_smul' (A := RegradeByDivision 𝒜 (k : ℤ) 0) hb x } }

/-- The functor from `DGModuleCat` to dg modules over the regraded ring on data: the identity on
underlying types, gradings, differentials and maps. -/
def dgModuleCatToRegraded : RegradeDGModuleCat.{v} hA ⥤ RegradedDGModuleCat.{v} 𝒜 k hA where
  obj M := dgModuleCatToRegradedObj hA M
  map f :=
    letI := RegradeByDivision.dgAddCommGroup 𝒜 (k : ℤ) 0 hA.toIsDifferentialOfDegree
    { hom := ⟨f.hom.toLinearMap, fun hm => f.hom.map_mem hm⟩
      comm := fun x => f.hom.map_d x }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Dg modules over the regraded ring on data are its dg modules.** The category
`RegradedDGModuleCat 𝒜 k hA` is equivalent (indeed isomorphic, the unit and counit being
identities) to the category `DGModuleCat (⨁ q, A^{q k})`. -/
def regradedDGModuleCatEquivalence :
    RegradedDGModuleCat.{v} 𝒜 k hA ≌ RegradeDGModuleCat.{v} hA :=
  CategoryTheory.Equivalence.mk (regradedToDGModuleCat hA) (dgModuleCatToRegraded hA)
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- **Modules with a differential of degree `k` and dg modules over the regraded ring.** For a
`ℤ`-graded ring `A` concentrated in degrees divisible by `k ≥ 1`, with a differential of degree
`k` satisfying the Leibniz rule with the sign `(-1)^{|a| / k}`, the category of `ℤ`-graded
`A`-modules with a differential of degree `k` is equivalent to the category of families, indexed
by `ℤ/k`, of dg modules over the dg ring `⨁ q, A^{q k}`: `M ↦ (⨁ q, M^{q k + r})_r`. -/
def divDGModuleCatEquivalence [IsConcentratedInMultiples 𝒜 k] :
    DivDGModuleCat.{v} 𝒜 k dA ≌ (ZMod k → RegradeDGModuleCat.{v} hA) :=
  (regradeDGEquivalence hA).trans (Equivalence.pi fun _ => regradedDGModuleCatEquivalence hA)

end DGModuleCat

end GradedModuleCat

end DG
