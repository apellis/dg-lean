import Mathlib.CategoryTheory.Shift.Adjunction
import DG.Algebra.Constructions
import DG.Homotopy.ForgetTriangulated
import DG.Monoidal.ComplexSum

/-!
# Dg modules over a commutative ring are cochain complexes

Let `R` be a commutative ring, regarded as a dg ring concentrated in degree `0` with zero
differential (`DG.DGAddCommGroup.degreeZero R`, `DG.DGRing.degreeZero R`,
`DG.DGAlgebra.degreeZero R`; in this file these are the scoped instances of the namespace
`DG.DegreeZero`, enabled by `open scoped DG.DegreeZero`). A dg module over `R` is then exactly
a cochain complex of `R`-modules. This file makes this precise for the categories of dg modules
and for the homotopy categories.

## Main definitions and results

* `DG.Cochain.ofHomComplex`: a cochain of Mathlib's Hom complex of the underlying complexes of
  two dg modules over `R` as a cochain of the Hom complex `HOM_R(M, N)`; it is inverse to
  `DG.Cochain.toHomComplex` (`DG.Cochain.toHomComplex_ofHomComplex`,
  `DG.Cochain.toHomComplex_injective`).
* `DG.DGHomotopy.ofHomotopy`: a homotopy of the underlying complexes is a homotopy of dg
  modules, the converse of `DG.DGHomotopy.toHomotopy`; `DG.homotopic_iff_forget`.
* `DG.DGModuleCat.ofComplex R : CochainComplex (ModuleCat R) ℤ ⥤ DGModuleCat R`, sending `K` to
  `⨁ n, Kⁿ` (`DG.ComplexSum K`) with the componentwise action of `R`, and
  `DG.DGModuleCat.cochainComplexEquivalence R : DGModuleCat R ≌ CochainComplex (ModuleCat R) ℤ`,
  whose functor is the forgetful functor `DG.DGModuleCat.forget R R` and whose inverse is
  `ofComplex R`. Both functors are additive and commute with the shifts
  (`DG.DGModuleCat.forgetCommShift`, `DG.DGModuleCat.ofComplex_commShift`), and the equivalence
  is compatible with the shifts (`DG.DGModuleCat.cochainComplexEquivalence_commShift`). The
  compatibility with mapping cones is `DG.Cone.forgetIso` (for any dg algebra).
* `DG.HomotopyCategory.forget_isEquivalence`: the triangulated forgetful functor
  `DG.HomotopyCategory.forget R R` between the homotopy categories is an equivalence (full,
  faithful and essentially surjective), and `DG.HomotopyCategory.comparisonEquivalence R` is the
  resulting equivalence `DG.HomotopyCategory R ≌ HomotopyCategory (ModuleCat R) (up ℤ)`.

The derived categories are compared in `DG/Derived/Comparison.lean`.

## Universes

The inverse functor uses `DG.ComplexSum`, which requires the modules to live in the universe of
`R`; the equivalences are therefore stated for `DGModuleCat.{u} R` with `R : Type u`, as for
Mathlib's `ModuleCat.{u} R`.
-/

open CategoryTheory Category Limits

universe v u

namespace DG

namespace DegreeZero

variable (R : Type u) [CommRing R]

/-- `R` concentrated in degree `0`, as a dg abelian group (scoped instance). -/
scoped instance instDGAddCommGroup : DGAddCommGroup R := DGAddCommGroup.degreeZero R

/-- `R` concentrated in degree `0`, as a dg ring (scoped instance). -/
scoped instance instDGRing : DGRing R := DGRing.degreeZero R

/-- `R` concentrated in degree `0`, as a dg `R`-algebra (scoped instance). -/
scoped instance instDGAlgebra : DGAlgebra R R := DGAlgebra.degreeZero R

variable {R}

/-- The homogeneous elements of `R` concentrated in degree `0`: every element has degree `0`,
and only `0` has a nonzero degree. -/
theorem mem_grading_iff {n : ℤ} {r : R} : r ∈ grading (M := R) n ↔ n = 0 ∨ r = 0 :=
  mem_degreeZeroGrading_iff R

/-- The differential of `R` concentrated in degree `0` is zero. -/
@[simp]
theorem d_apply (r : R) : d r = 0 := rfl

end DegreeZero

open DegreeZero DGModuleCat DGModuleCat.Algebra

/-! ### Cochains and homotopies -/

variable {R : Type u} [CommRing R]

namespace Cochain

variable {M N : DGModuleCat.{v} R} {n : ℤ}

/-- The degree-`p` component of a cochain of Mathlib's Hom complex, as an additive map on
`Mᵖ`. -/
def ofHomComplexAux
    (z : CochainComplex.HomComplex.Cochain ((forget R R).obj M) ((forget R R).obj N) n)
    (p : ℤ) : grading (M := M) p →+ N where
  toFun x := ((z.v p (p + n) rfl).hom ⟨x.1, x.2⟩).1
  map_zero' := by
    change ((z.v p (p + n) rfl).hom 0).1 = 0
    rw [map_zero]
    rfl
  map_add' x y := by
    change ((z.v p (p + n) rfl).hom (⟨x.1, x.2⟩ + ⟨y.1, y.2⟩)).1 = _
    rw [map_add]
    rfl

@[simp]
theorem ofHomComplexAux_apply
    (z : CochainComplex.HomComplex.Cochain ((forget R R).obj M) ((forget R R).obj N) n)
    (p : ℤ) (x : grading (M := M) p) :
    ofHomComplexAux z p x = ((z.v p (p + n) rfl).hom ⟨x.1, x.2⟩).1 := rfl

/-- A cochain of Mathlib's Hom complex of the underlying complexes of two dg modules over `R`
(concentrated in degree `0`) as a cochain of the Hom complex `HOM_R(M, N)`: the inverse of
`DG.Cochain.toHomComplex`. -/
def ofHomComplex
    (z : CochainComplex.HomComplex.Cochain ((forget R R).obj M) ((forget R R).obj N) n) :
    Cochain R M N n where
  toAddMonoidHom := liftHomogeneous (grading (M := M)) (ofHomComplexAux z)
  map_mem' p x hx := by
    change liftHomogeneous (grading (M := M)) (ofHomComplexAux z) x ∈ _
    rw [liftHomogeneous_of_mem _ _ hx]
    exact ((z.v p (p + n) rfl).hom ⟨x, hx⟩).2
  map_smul' {i a} ha x := by
    change liftHomogeneous (grading (M := M)) (ofHomComplexAux z) (a • x) =
      _ • (a • liftHomogeneous (grading (M := M)) (ofHomComplexAux z) x)
    rcases DegreeZero.mem_grading_iff.mp ha with rfl | rfl
    · rw [mul_zero, koszulSign_zero, one_smul]
      induction x using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous p x =>
        have hx : a • (x : M) ∈ grading (M := M) p := by
          simpa using smul_mem_grading ha x.2
        rw [liftHomogeneous_of_mem _ _ hx, liftHomogeneous_coe]
        exact congrArg Subtype.val ((z.v p (p + n) rfl).hom.map_smul a ⟨x.1, x.2⟩)
      | h_add x y hx hy => simp only [smul_add, map_add, hx, hy]
    · simp

@[simp]
theorem ofHomComplex_apply_coe
    (z : CochainComplex.HomComplex.Cochain ((forget R R).obj M) ((forget R R).obj N) n)
    {p : ℤ} (x : grading (M := M) p) :
    ofHomComplex z x = ((z.v p (p + n) rfl).hom ⟨x.1, x.2⟩).1 :=
  liftHomogeneous_coe _ _ x

@[simp]
theorem toHomComplex_ofHomComplex
    (z : CochainComplex.HomComplex.Cochain ((forget R R).obj M) ((forget R R).obj N) n) :
    (ofHomComplex z).toHomComplex R = z :=
  toHomComplex_ext R fun p q hpq x => by
    subst hpq
    exact ofHomComplex_apply_coe z ⟨x.1, x.2⟩

end Cochain

/-- The cochains of the Hom complex embed into the cochains of Mathlib's Hom complex of the
underlying complexes. -/
theorem Cochain.toHomComplex_injective {A : Type*} [Ring A] [DGAddCommGroup A] [Algebra R A]
    [DGRing A] [DGAlgebra R A] {M N : DGModuleCat.{v} A} {n : ℤ} :
    Function.Injective (Cochain.toHomComplex (M := M) (N := N) (n := n) R) := by
  intro z₁ z₂ h
  ext x
  induction x using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous p x =>
    exact congrArg (fun z => (((z.v p (p + n) rfl).hom
      ⟨x.1, x.2⟩ : DGModule.gradingSubmodule R A N (p + n)) : N)) h
  | h_add x y hx hy => rw [map_add, map_add, hx, hy]

namespace DGModuleCat

variable {M N : DGModuleCat.{v} R}

/-- A morphism between the underlying complexes of two dg modules over `R` as a morphism of dg
modules (the preimage under the forgetful functor). -/
def homOfComplexHom (φ : (forget R R).obj M ⟶ (forget R R).obj N) : M ⟶ N :=
  ofHom (Cocycle.homOf ⟨Cochain.ofHomComplex (CochainComplex.HomComplex.Cochain.ofHom φ), by
    rw [Cocycle.mem_iff 1 (zero_add 1)]
    apply Cochain.toHomComplex_injective (R := R)
    rw [Cochain.toHomComplex_δ, Cochain.toHomComplex_ofHomComplex,
      CochainComplex.HomComplex.δ_ofHom, Cochain.toHomComplex_zero]⟩)

@[simp]
theorem forget_map_homOfComplexHom (φ : (forget R R).obj M ⟶ (forget R R).obj N) :
    (forget R R).map (homOfComplexHom φ) = φ := by
  apply CochainComplex.HomComplex.Cochain.ofHom_injective
  rw [← Cochain.toHomComplex_ofHom]
  exact Cochain.toHomComplex_ofHomComplex _

/-- The forgetful functor from dg modules over `R` to cochain complexes of `R`-modules is
full. -/
instance forget_full : (forget R R).Full where
  map_surjective φ := ⟨homOfComplexHom φ, forget_map_homOfComplexHom φ⟩

/-- The forgetful functor from dg modules over `R` to cochain complexes is fully faithful. -/
noncomputable def forgetFullyFaithful : (forget.{v} R R).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end DGModuleCat

/-- A homotopy between the underlying morphisms of complexes of two morphisms of dg modules
over `R` gives a homotopy of dg modules: the converse of `DG.DGHomotopy.toHomotopy`. -/
noncomputable def DGHomotopy.ofHomotopy {M N : DGModuleCat.{v} R} {f g : M ⟶ N}
    (h : Homotopy ((forget R R).map f) ((forget R R).map g)) : DGHomotopy f.hom g.hom where
  hom := Cochain.ofHomComplex (CochainComplex.HomComplex.Cochain.equivHomotopy _ _ h).1
  ofHom_eq := by
    apply Cochain.toHomComplex_injective (R := R)
    rw [Cochain.toHomComplex_add, Cochain.toHomComplex_δ, Cochain.toHomComplex_ofHomComplex,
      Cochain.toHomComplex_ofHom, Cochain.toHomComplex_ofHom]
    exact (CochainComplex.HomComplex.Cochain.equivHomotopy _ _ h).2

/-- Two morphisms of dg modules over `R` are homotopic iff their underlying morphisms of
cochain complexes are homotopic. -/
theorem homotopic_iff_forget {M N : DGModuleCat.{v} R} (f g : M ⟶ N) :
    Homotopic f.hom g.hom ↔ Nonempty (Homotopy ((forget R R).map f) ((forget R R).map g)) :=
  ⟨fun ⟨h⟩ => ⟨h.toHomotopy R⟩, fun ⟨h⟩ => ⟨DGHomotopy.ofHomotopy h⟩⟩

/-! ### The inverse functor: cochain complexes as dg modules over `R` -/

namespace ComplexSum

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The differential of `⨁ n, Kⁿ` is `R`-linear. -/
theorem d_smul (r : R) (z : ComplexSum K) : d (r • z) = r • d z := by
  induction z using ComplexSum.induction_on with
  | zero => simp
  | of n x =>
    rw [← map_smul, d_of, d_of, ← map_smul]
    congr 1
    exact (K.d n (n + 1)).hom.map_smul r x
  | add z z' hz hz' => rw [smul_add, d_add, hz, hz', d_add, smul_add]

/-- The external direct sum `⨁ n, Kⁿ` of a cochain complex of `R`-modules is a dg module over
`R` (concentrated in degree `0`), with the componentwise action. -/
instance instDGModule : DGModule R (ComplexSum K) where
  smul_mem i j r z hr hz := by
    obtain ⟨x, rfl⟩ := mem_grading_iff.mp hz
    rcases DegreeZero.mem_grading_iff.mp hr with rfl | rfl
    · rw [← map_smul, vadd_eq_add, zero_add]
      exact of_mem_grading j _
    · rw [zero_smul]
      exact zero_mem _
  d_smul' {n r} hr z := by
    rw [DegreeZero.d_apply, zero_smul, zero_add, d_smul]
    rcases DegreeZero.mem_grading_iff.mp hr with rfl | rfl
    · rw [koszulSign_zero, one_smul]
    · simp

/-- The action of `R` on `⨁ n, Kⁿ` is componentwise. -/
theorem algebraMap_smul_of (r : R) (n : ℤ) (x : K.X n) :
    algebraMap R R r • of K n x = of K n (r • x) :=
  (map_smul _ _ _).symm

end ComplexSum

namespace DGModuleCat

variable (R)

/-- A cochain complex of `R`-modules as a dg module over `R`: `K ↦ ⨁ n, Kⁿ`. This is the
inverse of the forgetful functor `DG.DGModuleCat.forget R R`. -/
@[simps obj]
noncomputable def ofComplex : CochainComplex (ModuleCat.{u} R) ℤ ⥤ DGModuleCat.{u} R where
  obj K := of R (ComplexSum K)
  map φ := ofHom
    { ComplexSum.map φ with
      map_mem' := ComplexSum.map_mem φ
      map_d' := ComplexSum.map_d φ }
  map_id _ := hom_ext_apply fun z => ComplexSum.map_id z
  map_comp φ ψ := hom_ext_apply fun z => ComplexSum.map_comp φ ψ z

@[simp]
theorem ofComplex_map_apply {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)
    (z : ComplexSum K) : (ofComplex R).map φ z = ComplexSum.map φ z := rfl

/-- The underlying complex of `⨁ n, Kⁿ` is `K`. -/
noncomputable def ofComplexCompForgetIso : ofComplex R ⋙ forget R R ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun K => ComplexSum.toComplexIso (A := R) (ComplexSum.algebraMap_smul_of K)) fun {K L} φ => by
      ext n ⟨_, x, rfl⟩
      change ComplexSum.component L n (ComplexSum.map φ (ComplexSum.of K n x)) =
        φ.f n (ComplexSum.component K n (ComplexSum.of K n x))
      rw [ComplexSum.map_of, ComplexSum.component_of_same, ComplexSum.component_of_same]

/-- Dg modules over a commutative ring `R` (concentrated in degree `0`) are the same as cochain
complexes of `R`-modules: the forgetful functor `DG.DGModuleCat.forget R R` is an equivalence
of categories, with inverse `K ↦ ⨁ n, Kⁿ` (`DG.DGModuleCat.ofComplex R`). -/
@[simps functor inverse]
noncomputable def cochainComplexEquivalence :
    DGModuleCat.{u} R ≌ CochainComplex (ModuleCat.{u} R) ℤ where
  functor := forget R R
  inverse := ofComplex R
  unitIso := NatIso.ofComponents
    (fun M => forgetFullyFaithful.preimageIso ((ofComplexCompForgetIso R).app _).symm)
    fun {M N} f => (forget R R).map_injective (by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        Functor.map_comp, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
        Iso.symm_hom, Iso.app_inv]
      exact (ofComplexCompForgetIso R).inv.naturality ((forget R R).map f))
  counitIso := ofComplexCompForgetIso R
  functor_unitIso_comp M := by
    simp only [Functor.id_obj, Functor.comp_obj, NatIso.ofComponents_hom_app,
      Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage, Iso.symm_hom,
      Iso.app_inv]
    exact (ofComplexCompForgetIso R).inv_hom_id_app _

/-- The forgetful functor `DGModuleCat R ⥤ CochainComplex (ModuleCat R) ℤ` is an equivalence. -/
instance forget_isEquivalence : (forget.{u} R R).IsEquivalence :=
  (cochainComplexEquivalence R).isEquivalence_functor

instance : (cochainComplexEquivalence R).functor.Additive :=
  inferInstanceAs (forget R R).Additive

noncomputable instance : (cochainComplexEquivalence R).functor.CommShift ℤ :=
  inferInstanceAs ((forget R R).CommShift ℤ)

/-- The functor `K ↦ ⨁ n, Kⁿ` is additive. -/
instance ofComplex_additive : (ofComplex R).Additive :=
  inferInstanceAs (cochainComplexEquivalence R).inverse.Additive

/-- The functor `K ↦ ⨁ n, Kⁿ` commutes with the shifts, with the structure induced from
`DG.DGModuleCat.forgetCommShift` along the equivalence `cochainComplexEquivalence R`. -/
noncomputable instance ofComplex_commShift : (ofComplex R).CommShift ℤ :=
  (cochainComplexEquivalence R).commShiftInverse ℤ

noncomputable instance : (cochainComplexEquivalence R).inverse.CommShift ℤ :=
  inferInstanceAs ((ofComplex R).CommShift ℤ)

/-- The equivalence `cochainComplexEquivalence R` is compatible with the shifts: its unit and
counit commute with the shifts. -/
instance cochainComplexEquivalence_commShift : (cochainComplexEquivalence R).CommShift ℤ :=
  (cochainComplexEquivalence R).commShift_of_functor ℤ

end DGModuleCat

/-! ### The homotopy categories -/

namespace HomotopyCategory

/-- The forgetful functor on homotopy categories is full. -/
instance forget_full : (forget.{v} R R).Full where
  map_surjective {X Y} φ := by
    obtain ⟨M, rfl⟩ := quotient_obj_surjective X
    obtain ⟨N, rfl⟩ := quotient_obj_surjective Y
    obtain ⟨ψ, rfl⟩ := (_root_.HomotopyCategory.quotient _ _).map_surjective
      (X := (DGModuleCat.forget R R).obj M) (Y := (DGModuleCat.forget R R).obj N) φ
    exact ⟨(quotient R).map (DGModuleCat.homOfComplexHom ψ), by
      rw [forget_map_quotient_map, DGModuleCat.forget_map_homOfComplexHom]⟩

/-- The forgetful functor on homotopy categories is faithful: homotopies of the underlying
complexes are homotopies of dg modules (`DG.DGHomotopy.ofHomotopy`). -/
instance forget_faithful : (forget.{v} R R).Faithful where
  map_injective {X Y f g} h := by
    obtain ⟨M, rfl⟩ := quotient_obj_surjective X
    obtain ⟨N, rfl⟩ := quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := (quotient R).map_surjective f
    obtain ⟨g, rfl⟩ := (quotient R).map_surjective g
    rw [forget_map_quotient_map, forget_map_quotient_map] at h
    exact eq_of_homotopy _ _ (DGHomotopy.ofHomotopy (_root_.HomotopyCategory.homotopyOfEq _ _ h))

/-- The forgetful functor on homotopy categories is essentially surjective. -/
instance forget_essSurj : (forget.{u} R R).EssSurj where
  mem_essImage Y := by
    obtain ⟨K, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective Y
    exact ⟨(quotient R).obj ((DGModuleCat.ofComplex R).obj K),
      ⟨(_root_.HomotopyCategory.quotient _ _).mapIso
        ((DGModuleCat.ofComplexCompForgetIso R).app K)⟩⟩

/-- The forgetful functor on homotopy categories is an equivalence. -/
instance forget_isEquivalence : (forget.{u} R R).IsEquivalence where

variable (R) in
/-- The homotopy category of dg modules over a commutative ring `R` (concentrated in degree `0`)
is equivalent to Mathlib's homotopy category of cochain complexes of `R`-modules, through the
forgetful functor `DG.HomotopyCategory.forget R R`; this is an equivalence of triangulated
categories (`DG.HomotopyCategory.forgetCommShift`, `DG.HomotopyCategory.forget_isTriangulated`).
-/
noncomputable def comparisonEquivalence :
    HomotopyCategory.{u} R ≌ _root_.HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  (forget R R).asEquivalence

@[simp]
theorem comparisonEquivalence_functor :
    (comparisonEquivalence R).functor = forget R R := rfl

end HomotopyCategory

end DG
