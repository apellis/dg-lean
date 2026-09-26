import Mathlib.CategoryTheory.Monoidal.Mon_
import DG.Algebra.Category
import DG.Monoidal.MonObj

/-!
# Dg algebras as monoid objects in cochain complexes

The category `CochainComplex (ModuleCat R) ℤ` of cochain complexes of `R`-modules is monoidal
(`DG.Monoidal.Complex`), with the differential of `K ⊗ L` given by
`d (x ⊗ y) = d x ⊗ y + (-1)^|x| x ⊗ d y`, which is the sign convention of the library. This file
proves that a dg `R`-algebra is the same as a monoid object in it.

## Main definitions

* `DG.DGAlgCat.toMon R : DGAlgCat R ⥤ Mon_ (CochainComplex (ModuleCat R) ℤ)`: a dg algebra `A`
  goes to its underlying complex `DG.DGAlgCat.complex A` (the complex
  `DG.DGModuleCat.toComplex R A` of `A` as a dg module over itself, with `Aⁿ` in degree `n`),
  with multiplication `μ : A ⊗ A ⟶ A` given by `Aⁱ ⊗ Aʲ → Aⁱ⁺ʲ, a ⊗ b ↦ a * b`
  (`DG.DGAlgCat.mul`; that it is a morphism of complexes is the graded Leibniz rule) and unit
  `η : 𝟙_ ⟶ A`, `r ↦ r • 1` (`DG.DGAlgCat.one`);
* `DG.DGAlgCat.ofMon R : Mon_ (CochainComplex (ModuleCat R) ℤ) ⥤ DGAlgCat R`: a monoid object
  `M` goes to the dg algebra `⨁ n, Mⁿ` of `DG.MonObj`;
* `DG.DGAlgCat.monEquivalence R : DGAlgCat R ≌ Mon_ (CochainComplex (ModuleCat R) ℤ)`, with unit
  the decomposition `A ≅ ⨁ n, Aⁿ` (`DG.DGAlgCat.unitIso`) and counit the identification of the
  underlying complex of `⨁ n, Mⁿ` with `M` (`DG.DGAlgCat.counitIso`).

## Universes

The monoidal structure of `ModuleCat.{u} R` requires `R : Type u`; accordingly the equivalence
is stated for `DGAlgCat.{u, u} R`, dg `R`-algebras with carriers in `Type u`.
-/

open CategoryTheory MonoidalCategory HomologicalComplex DirectSum

universe u

noncomputable section

namespace DG


/-! ### From dg algebras to monoid objects -/

namespace DGAlgCat

variable {R : Type u} [CommRing R]

open DGModuleCat.Algebra ComplexTensor

variable (A : DGAlgCat.{u, u} R)

/-- The underlying cochain complex of `R`-modules of a dg `R`-algebra `A`, i.e. of `A` as a dg
module over itself: its degree-`n` component is `Aⁿ`. -/
abbrev complex : CochainComplex (ModuleCat.{u} R) ℤ :=
  DGModuleCat.toComplex R (DGModuleCat.of A A)

/-- The unit `1 ∈ A⁰`, as an element of the underlying complex. -/
def oneX : (complex A).X 0 := ⟨1, one_mem_grading⟩

/-- The multiplication `Aᵖ × Aᑫ → Aⁿ` (`p + q = n`) as an `R`-bilinear map. -/
def mulBilin (p q n : ℤ) (h : p + q = n) :
    (complex A).X p →ₗ[R] (complex A).X q →ₗ[R] (complex A).X n :=
  LinearMap.mk₂ R (fun x y => ⟨x.1 * y.1, h ▸ mul_mem_grading x.2 y.2⟩)
    (fun x x' y => Subtype.ext (add_mul x.1 x'.1 y.1))
    (fun r x y => Subtype.ext (by
      show (algebraMap R A r * x.1) * y.1 = algebraMap R A r * (x.1 * y.1)
      rw [mul_assoc]))
    (fun x y y' => Subtype.ext (mul_add x.1 y.1 y'.1))
    (fun r x y => Subtype.ext (by
      show x.1 * (algebraMap R A r * y.1) = algebraMap R A r * (x.1 * y.1)
      rw [← mul_assoc, ← Algebra.commutes, mul_assoc]))

@[simp]
theorem coe_mulBilin_apply {p q n : ℤ} (h : p + q = n) (x : (complex A).X p)
    (y : (complex A).X q) : (mulBilin A p q n h x y).1 = x.1 * y.1 :=
  rfl

/-- The multiplication of a dg algebra as a morphism of complexes `A ⊗ A ⟶ A`; that it is a
morphism of complexes is the graded Leibniz rule. -/
def mul : complex A ⊗ complex A ⟶ complex A :=
  tensorDesc _ _ _ (mulBilin A) (by
    intro p q n h x y
    rw [DGModuleCat.toComplex_d, DGModuleCat.toComplex_d, DGModuleCat.toComplex_d]
    apply Subtype.ext
    change d (x.1 * y.1) = d x.1 * y.1 + ((p.negOnePow : ℤ) • (x.1 * d y.1))
    rw [d_mul x.2, Units.smul_def])

@[simp]
theorem coe_mul_f_tmul {p q n : ℤ} (h : p + q = n) (x : (complex A).X p)
    (y : (complex A).X q) : ((mul A).f n (tmul _ _ h x y)).1 = x.1 * y.1 := by
  rw [mul, tensorDesc_f_tmul]
  rfl

/-- The unit of a dg algebra as a morphism of complexes `𝟙_ ⟶ A`, `r ↦ r • 1`. -/
def one : 𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ complex A :=
  mkHomFromSingle (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (oneX A))) (by
    rintro _ rfl
    rw [DGModuleCat.toComplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun r => Subtype.ext ?_)
    change d (algebraMap R A r * 1) = 0
    rw [mul_one, d_algebraMap])

@[simp]
theorem one_f_unitOne : (one A).f 0 (unitOne R) = oneX A := by
  rw [one, mkHomFromSingle_f, ModuleCat.comp_apply, unitOne]
  erw [Iso.inv_hom_id_apply]
  exact one_smul R (oneX A)

/-- A dg `R`-algebra as a monoid object in the monoidal category of cochain complexes of
`R`-modules. -/
@[simps]
def toMonObj : Mon_ (CochainComplex (ModuleCat.{u} R) ℤ) where
  X := complex A
  one := one A
  mul := mul A
  one_mul := by
    ext n : 1
    refine unit_tensor_hom_ext fun x => Subtype.ext ?_
    rw [comp_f, ModuleCat.comp_apply, whiskerRight_f_tmul, one_f_unitOne, coe_mul_f_tmul,
      leftUnitor_hom_f_tmul]
    exact one_mul x.1
  mul_one := by
    ext n : 1
    refine tensor_unit_hom_ext fun x => Subtype.ext ?_
    rw [comp_f, ModuleCat.comp_apply, whiskerLeft_f_tmul, one_f_unitOne, coe_mul_f_tmul,
      rightUnitor_hom_f_tmul]
    exact mul_one x.1
  mul_assoc := by
    ext n : 1
    refine hom_ext₃ fun p q r h x y z => Subtype.ext ?_
    simp only [comp_f, ModuleCat.comp_apply, whiskerRight_f_tmul, associator_hom_f_tmul,
      whiskerLeft_f_tmul, coe_mul_f_tmul]
    exact mul_assoc x.1 y.1 z.1

@[simp]
theorem coe_toMonObj_mul_f_tmul {p q n : ℤ} (h : p + q = n) (x : (toMonObj A).X.X p)
    (y : (toMonObj A).X.X q) :
    ((toMonObj A).mul.f n (tmul (toMonObj A).X (toMonObj A).X h x y)).1 = x.1 * y.1 :=
  coe_mul_f_tmul A h x y

theorem toMonObj_one_f_unitOne : (toMonObj A).one.f 0 (unitOne R) = oneX A :=
  one_f_unitOne A

/-- The differential of the complex of `A` is the differential of `A`. -/
theorem toMonObj_X_d_apply {n : ℤ} (a : (toMonObj A).X.X n) :
    (toMonObj A).X.d n (n + 1) a = ⟨d a.1, d_mem a.2⟩ :=
  congrArg (fun φ => ModuleCat.Hom.hom φ a) (DGModuleCat.toComplex_d R (DGModuleCat.of A A) n)

variable {A} {B C : DGAlgCat.{u, u} R}

/-- A morphism of dg algebras restricted to the components of degree `n`. -/
def restrictX (f : A ⟶ B) (n : ℤ) : (complex A).X n →ₗ[R] (complex B).X n where
  toFun x := ⟨f.hom x.1, f.hom.map_mem x.2⟩
  map_add' x y := Subtype.ext (map_add f.hom x.1 y.1)
  map_smul' r x := Subtype.ext (by
    show f.hom (algebraMap R A r * x.1) = algebraMap R B r * f.hom x.1
    rw [map_mul, AlgHomClass.commutes])

@[simp]
theorem coe_restrictX_apply (f : A ⟶ B) (n : ℤ) (x : (complex A).X n) :
    (restrictX f n x).1 = f.hom x.1 :=
  rfl

/-- The morphism of underlying complexes induced by a morphism of dg algebras. -/
def complexMap (f : A ⟶ B) : complex A ⟶ complex B :=
  CochainComplex.ofHom _ _ _ _ _ _ (fun n => ModuleCat.ofHom (restrictX f n)) fun n => by
    ext x
    exact (f.hom.map_d x.1).symm

@[simp]
theorem coe_complexMap_f_apply (f : A ⟶ B) (n : ℤ) (x : (complex A).X n) :
    ((complexMap f).f n x).1 = f.hom x.1 :=
  rfl

/-- A morphism of dg algebras as a morphism of monoid objects. -/
@[simps]
def toMonMap (f : A ⟶ B) : toMonObj A ⟶ toMonObj B where
  hom := complexMap f
  one_hom := unit_hom_ext (Subtype.ext (by
    simp only [toMonObj_one, toMonObj_X, comp_f, ModuleCat.comp_apply, one_f_unitOne,
      coe_complexMap_f_apply]
    exact map_one f.hom))
  mul_hom := by
    ext n : 1
    refine ComplexTensor.hom_ext fun p q h x y => Subtype.ext ?_
    simp only [toMonObj_X, toMonObj_mul, comp_f, ModuleCat.comp_apply, coe_complexMap_f_apply,
      coe_mul_f_tmul, tensorHom_f_tmul]
    exact map_mul f.hom x.1 y.1

variable (R) in
/-- The functor from dg `R`-algebras to monoid objects in cochain complexes of `R`-modules. -/
@[simps]
def toMon : DGAlgCat.{u, u} R ⥤ Mon_ (CochainComplex (ModuleCat.{u} R) ℤ) where
  obj := toMonObj
  map := toMonMap
  map_id _ := by
    ext n : 3
    rfl
  map_comp _ _ := by
    ext n : 3
    rfl

end DGAlgCat


namespace DGAlgCat

variable {R : Type u} [CommRing R]

open ComplexTensor

/-- The dg `R`-algebra `⨁ n, Mⁿ` associated to a monoid object `M` in cochain complexes of
`R`-modules. -/
abbrev ofMonObj (M : Mon_ (CochainComplex (ModuleCat.{u} R) ℤ)) : DGAlgCat.{u, u} R :=
  of R (ComplexSum M.X)

variable {M N P : Mon_ (CochainComplex (ModuleCat.{u} R) ℤ)}

/-- The morphism of dg algebras induced by a morphism of monoid objects. -/
def ofMonMap (f : M ⟶ N) : ofMonObj M ⟶ ofMonObj N :=
  ofHom
    { toAlgHom := DirectSum.toAlgebra R (fun n : ℤ => (M.X.X n : Type u))
        (fun n => (ComplexSum.of N.X n).comp (f.hom.f n).hom) (by
          change ComplexSum.of N.X 0 (f.hom.f 0 (M.one.f 0 (unitOne R))) =
            ComplexSum.of N.X 0 (N.one.f 0 (unitOne R))
          rw [← ModuleCat.comp_apply, ← comp_f, f.one_hom]) (by
          intro i j x y
          change ComplexSum.of N.X (i + j) (f.hom.f (i + j) (M.mul.f (i + j) (tmul _ _ rfl x y))) =
            ComplexSum.of N.X i (f.hom.f i x) * ComplexSum.of N.X j (f.hom.f j y)
          rw [MonObj.of_mul_of, ← ModuleCat.comp_apply, ← comp_f, f.mul_hom, comp_f,
            ModuleCat.comp_apply, tensorHom_f_tmul])
      map_mem' := ComplexSum.map_mem f.hom
      map_d' := ComplexSum.map_d f.hom }

@[simp]
theorem ofMonMap_hom_apply (f : M ⟶ N) (z : ComplexSum M.X) :
    (ofMonMap f).hom z = ComplexSum.map f.hom z :=
  rfl

variable (R) in
/-- The functor from monoid objects in cochain complexes of `R`-modules to dg `R`-algebras,
`M ↦ ⨁ n, Mⁿ`. -/
@[simps]
def ofMon : Mon_ (CochainComplex (ModuleCat.{u} R) ℤ) ⥤ DGAlgCat.{u, u} R where
  obj := ofMonObj
  map := ofMonMap
  map_id M := hom_ext fun z => by
    rw [ofMonMap_hom_apply, hom_id, DGAlgHom.id_apply]
    exact ComplexSum.map_id z
  map_comp f g := hom_ext fun z => by
    rw [ofMonMap_hom_apply, hom_comp, DGAlgHom.comp_apply, ofMonMap_hom_apply,
      ofMonMap_hom_apply]
    exact ComplexSum.map_comp f.hom g.hom z

/-! ### The unit of the equivalence -/

section Unit

variable (A : DGAlgCat.{u, u} R)

/-- The decomposition `A → ⨁ n, Aⁿ` of a dg algebra into its homogeneous components. -/
def unitFun : A →+ ComplexSum (toMonObj A).X :=
  liftHomogeneous (grading (M := A)) fun n =>
    (ComplexSum.of ((toMonObj A).X) n).toAddMonoidHom.comp
      { toFun := fun x => ⟨x.1, x.2⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }

theorem unitFun_of_mem {n : ℤ} {a : A} (ha : a ∈ grading n) :
    unitFun A a = ComplexSum.of ((toMonObj A).X) n ⟨a, ha⟩ :=
  liftHomogeneous_of_mem _ _ ha

/-- The summation map `⨁ n, Aⁿ → A`. -/
def counitFun : ComplexSum (toMonObj A).X →+ A :=
  DirectSum.toAddMonoid fun n =>
    { toFun := fun x : ((toMonObj A).X).X n => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

@[simp]
theorem counitFun_of (n : ℤ) (x : ((toMonObj A).X).X n) :
    counitFun A (ComplexSum.of ((toMonObj A).X) n x) = x.1 :=
  DirectSum.toAddMonoid_of (β := fun n => ((toMonObj A).X).X n) _ n x

theorem counitFun_unitFun (a : A) : counitFun A (unitFun A a) = a := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a => rw [unitFun_of_mem A a.2, counitFun_of]
  | h_add a a' ha ha' => rw [map_add, map_add, ha, ha']

theorem unitFun_counitFun (z : ComplexSum (toMonObj A).X) : unitFun A (counitFun A z) = z := by
  induction z using ComplexSum.induction_on with
  | zero => simp
  | of n x =>
    rw [counitFun_of, unitFun_of_mem A x.2]
    rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

theorem unitFun_mul (a b : A) : unitFun A (a * b) = unitFun A a * unitFun A b := by
  induction a using DG.induction_on with
  | h_zero => rw [zero_mul, map_zero, zero_mul]
  | @h_homogeneous i a =>
    induction b using DG.induction_on with
    | h_zero => rw [mul_zero, map_zero, mul_zero]
    | @h_homogeneous j b =>
      rw [unitFun_of_mem A (mul_mem_grading a.2 b.2), unitFun_of_mem A a.2, unitFun_of_mem A b.2,
        MonObj.of_mul_of]
      congr 1
      exact Subtype.ext (coe_mul_f_tmul A rfl _ _).symm
    | h_add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
  | h_add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]

theorem unitFun_one : unitFun A 1 = 1 := by
  rw [unitFun_of_mem A one_mem_grading, MonObj.one_def]
  congr 1
  exact (one_f_unitOne A).symm

theorem unitFun_algebraMap (r : R) :
    unitFun A (algebraMap R A r) = algebraMap R (ComplexSum (toMonObj A).X) r := by
  rw [unitFun_of_mem A (algebraMap_mem_grading R r), MonObj.algebraMap_apply]
  congr 1
  apply Subtype.ext
  change algebraMap R A r = algebraMap R A r * ((one A).f 0 (unitOne R)).1
  rw [one_f_unitOne, oneX, mul_one]

theorem unitFun_d (a : A) : unitFun A (d a) = d (unitFun A a) := by
  induction a using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous n a =>
    rw [unitFun_of_mem A (d_mem a.2), unitFun_of_mem A a.2, ComplexSum.d_of]
    congr 1
    exact (congrArg (fun φ => ModuleCat.Hom.hom φ
      (⟨a.1, a.2⟩ : DGModule.gradingSubmodule R A (DGModuleCat.of A A) n))
      (DGModuleCat.toComplex_d R (DGModuleCat.of A A) n)).symm
  | h_add a a' ha ha' => rw [d_add, map_add, ha, ha', map_add, d_add]

/-- The decomposition of a dg algebra into its homogeneous components, as a morphism of dg
algebras `A ⟶ ⨁ n, Aⁿ`. -/
def unitHom : A ⟶ ofMonObj (toMonObj A) :=
  ⟨{ toFun := unitFun A
     map_one' := unitFun_one A
     map_mul' := unitFun_mul A
     map_zero' := map_zero _
     map_add' := map_add _
     commutes' := unitFun_algebraMap A
     map_mem' := fun ha => by
       rw [unitFun_of_mem A ha]
       exact ComplexSum.of_mem_grading _ _
     map_d' := unitFun_d A }⟩

/-- The summation map `⨁ n, Aⁿ ⟶ A`, a morphism of dg algebras. -/
def counitHom : ofMonObj (toMonObj A) ⟶ A :=
  ⟨{ toFun := counitFun A
     map_one' := by rw [← unitFun_one A, counitFun_unitFun]
     map_mul' := fun z z' => by
       rw [← unitFun_counitFun A z, ← unitFun_counitFun A z', ← unitFun_mul, counitFun_unitFun,
         counitFun_unitFun, counitFun_unitFun]
     map_zero' := map_zero _
     map_add' := map_add _
     commutes' := fun r => by rw [← unitFun_algebraMap A r, counitFun_unitFun]
     map_mem' := fun {n} {z} hz => by
       obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp hz
       rw [counitFun_of]
       exact x.2
     map_d' := fun z => by
       rw [← unitFun_counitFun A z, ← unitFun_d, counitFun_unitFun, counitFun_unitFun] }⟩

/-- A dg algebra is isomorphic to the dg algebra of its monoid object `⨁ n, Aⁿ`. -/
@[simps]
def unitIso : A ≅ ofMonObj (toMonObj A) where
  hom := unitHom A
  inv := counitHom A
  hom_inv_id := hom_ext fun a => counitFun_unitFun A a
  inv_hom_id := hom_ext fun z => unitFun_counitFun A z

end Unit

variable (R) in
/-- The unit of the equivalence between dg algebras and monoid objects: every dg algebra is
isomorphic to `⨁ n, Aⁿ`, naturally in `A`. -/
def unitNatIso : 𝟭 (DGAlgCat.{u, u} R) ≅ toMon R ⋙ ofMon R :=
  NatIso.ofComponents unitIso fun {A B} f => hom_ext fun a => by
    change unitFun B (f.hom a) = ComplexSum.map (toMonMap f).hom (unitFun A a)
    induction a using DG.induction_on with
    | h_zero => rw [map_zero, map_zero, map_zero, map_zero]
    | @h_homogeneous n a =>
      rw [unitFun_of_mem B (f.hom.map_mem a.2), unitFun_of_mem A a.2]
      exact (ComplexSum.map_of (toMonMap f).hom n _).symm
    | h_add a a' ha ha' => rw [map_add, map_add, ha, ha', map_add, map_add]

/-! ### The counit of the equivalence -/

section Counit

variable (M : Mon_ (CochainComplex (ModuleCat.{u} R) ℤ))

theorem algebraMap_smul_of (r : R) (n : ℤ) (x : M.X.X n) :
    algebraMap R (ComplexSum M.X) r • ComplexSum.of M.X n x = ComplexSum.of M.X n (r • x) := by
  rw [smul_eq_mul, MonObj.algebraMap_apply, MonObj.of_mul_of, of_f_tmul M.mul rfl (zero_add n),
    tmul_smul_left, map_smul, MonObj.one_mul_apply]

/-- The underlying complex of `⨁ n, Mⁿ` is `M`. -/
def counitIsoX : (toMonObj (ofMonObj M)).X ≅ M.X :=
  ComplexSum.toComplexIso (K := M.X) (A := ComplexSum M.X) (algebraMap_smul_of M)

theorem counitIsoX_hom_f_apply (n : ℤ) (z : (toMonObj (ofMonObj M)).X.X n) :
    (counitIsoX M).hom.f n z = ComplexSum.component M.X n z.1 :=
  rfl

/-- The monoid object of the dg algebra `⨁ n, Mⁿ` is isomorphic to `M`. -/
def counitIso : toMonObj (ofMonObj M) ≅ M :=
  Mon_.mkIso (counitIsoX M)
    (unit_hom_ext (by
      rw [comp_f, ModuleCat.comp_apply]
      erw [one_f_unitOne]
      exact ComplexSum.component_of_same 0 (MonObj.one M)))
    (by
      ext n : 1
      refine ComplexTensor.hom_ext fun p q h x y => ?_
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp hx
      obtain ⟨y, rfl⟩ := ComplexSum.mem_grading_iff.mp hy
      simp only [comp_f, ModuleCat.comp_apply, tensorHom_f_tmul, counitIsoX_hom_f_apply]
      erw [coe_mul_f_tmul]
      change ComplexSum.component M.X n (ComplexSum.of M.X p x * ComplexSum.of M.X q y) =
        M.mul.f n (tmul M.X M.X h (ComplexSum.component M.X p (ComplexSum.of M.X p x))
          (ComplexSum.component M.X q (ComplexSum.of M.X q y)))
      rw [MonObj.of_mul_of, of_f_tmul M.mul rfl h, ComplexSum.component_of_same,
        ComplexSum.component_of_same, ComplexSum.component_of_same])

end Counit

theorem counitIso_hom_hom_f_apply (M : Mon_ (CochainComplex (ModuleCat.{u} R) ℤ)) (n : ℤ)
    (z : (toMonObj (ofMonObj M)).X.X n) :
    (counitIso M).hom.hom.f n z = ComplexSum.component M.X n z.1 :=
  rfl

theorem counitIso_naturality (f : M ⟶ N) :
    toMonMap (ofMonMap f) ≫ (counitIso N).hom = (counitIso M).hom ≫ f := by
  refine Mon_.Hom.ext (HomologicalComplex.hom_ext _ _ fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
  obtain ⟨z, hz⟩ := z
  obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp hz
  simp only [Mon_.comp_hom', comp_f, ModuleCat.comp_apply, toMonMap_hom,
    counitIso_hom_hom_f_apply, coe_complexMap_f_apply, ofMonMap_hom_apply, ComplexSum.map_of,
    ComplexSum.component_of_same]
  exact (congrArg (ComplexSum.component N.X n)
    (coe_complexMap_f_apply (ofMonMap f) n ⟨_, hz⟩)).trans
    (by rw [ofMonMap_hom_apply, ComplexSum.map_of, ComplexSum.component_of_same])

variable (R) in
/-- The counit of the equivalence between dg algebras and monoid objects: every monoid object
`M` is isomorphic to the monoid object of `⨁ n, Mⁿ`, naturally in `M`. -/
def counitNatIso : ofMon R ⋙ toMon R ≅ 𝟭 (Mon_ (CochainComplex (ModuleCat.{u} R) ℤ)) :=
  NatIso.ofComponents counitIso fun f => counitIso_naturality f

variable (R) in
/-- **Dg algebras are monoid objects in cochain complexes.** The category of dg `R`-algebras is
equivalent to the category of monoid objects in the monoidal category of cochain complexes of
`R`-modules, via `A ↦ (A, μ, η)` (`DG.DGAlgCat.toMon`) and `M ↦ ⨁ n, Mⁿ`
(`DG.DGAlgCat.ofMon`). -/
def monEquivalence :
    DGAlgCat.{u, u} R ≌ Mon_ (CochainComplex (ModuleCat.{u} R) ℤ) :=
  CategoryTheory.Equivalence.mk (toMon R) (ofMon R) (unitNatIso R) (counitNatIso R)

end DGAlgCat

end DG
