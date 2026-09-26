import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import DG.Homotopy.Forget
import DG.Homotopy.HomotopyCategory
import DG.Module.HomShift

/-!
# The shift on dg modules and on the homotopy category

Let `A` be a dg ring. This file equips the category `DG.DGModuleCat A` of dg `A`-modules and
the homotopy category `DG.HomotopyCategory A` with shifts by `ℤ` (`CategoryTheory.HasShift`),
and shows that the forgetful functor to cochain complexes commutes with the shifts.

## Main definitions and results

* `DG.DGModuleCat.hasShift`: the shift on `DGModuleCat A`, built with Mathlib's `hasShiftMk`
  from `M ↦ DG.Shift n M` on objects and `DG.DGModuleHom.shift` on morphisms. The isomorphisms
  `M⟦0⟧ ≅ M` and `M⟦a + b⟧ ≅ M⟦a⟧⟦b⟧` are the identity on underlying elements
  (`DG.Shift.zeroEquiv`, `DG.Shift.shiftShiftEquiv`), so that all the coherences are checked
  elementwise. The shift functors are additive and, for a dg `R`-algebra, `R`-linear.
* `DG.DGHomotopy.shift`: a homotopy `h` from `f` to `g` gives a homotopy
  `(-1)ⁿ • h⟦n⟧` from `f⟦n⟧` to `g⟦n⟧` (Mathlib's `Homotopy.shift`, with the same sign).
* `DG.HomotopyCategory.hasShift`: the induced shift on the homotopy category
  (`CategoryTheory.HasShift.quotient`), for which the quotient functor commutes with the shift
  (`DG.HomotopyCategory.commShiftQuotient`).
* `DG.DGModuleCat.forgetCommShift`: the forgetful functor
  `DG.DGModuleCat.forget R A : DGModuleCat A ⥤ CochainComplex (ModuleCat R) ℤ` commutes with
  the shifts. In degree `i`, the component `(Shift n M)ⁱ = Mⁱ⁺ⁿ` is identified with
  `(K⟦n⟧).X i = K.X (i + n)`, and the differential `(-1)ⁿ d` of `Shift n M` is the differential
  `n.negOnePow • K.d` of Mathlib's shifted complex: this is the comparison of the sign
  conventions of `DG.Shift` and `CochainComplex.shiftFunctor`.
-/

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace DG

namespace Shift

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]

/-- The identification `M⟦c⟧ ≃ M⟦a⟧⟦b⟧` when `a + b = c`, the identity on underlying
elements. -/
def shiftShiftEquiv (a b c : ℤ) (h : a + b = c) : Shift c M ≃ᵈᵍ[A] Shift b (Shift a M) where
  toFun x := mk b (mk a (unmk c x))
  invFun y := mk c (unmk a (unmk b y))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change mk b (mk a (unmk c (r • x))) = r • mk b (mk a (unmk c x))
    rw [unmk_smul_eq, smul_mk_eq, smul_mk_eq, twist_twist, ← h]
  map_mem' {k x} hx := by
    rw [mem_grading_iff', ← h] at hx
    rw [mem_grading_iff, mem_grading_iff, add_assoc, add_comm b a]
    exact hx
  map_d' x := by
    rw [unmk_d, d_mk, d_mk, ← h, koszulSign_add, mul_comm, ← smul_smul]
    rfl

@[simp]
theorem shiftShiftEquiv_apply (a b c : ℤ) (h : a + b = c) (x : Shift c M) :
    shiftShiftEquiv (A := A) a b c h x = mk b (mk a (unmk c x)) := rfl

@[simp]
theorem shiftShiftEquiv_symm_apply (a b c : ℤ) (h : a + b = c) (y : Shift b (Shift a M)) :
    (shiftShiftEquiv (A := A) a b c h).symm y = mk c (unmk a (unmk b y)) := rfl

variable (R : Type*) [CommRing R] [Algebra R A] [DGAlgebra R A]

theorem twist_algebraMap (n : ℤ) (r : R) : twist A n (algebraMap R A r) = algebraMap R A r := by
  rw [twist_of_mem (algebraMap_mem_grading R r), mul_zero, koszulSign_zero, one_smul]

omit [DGAddCommGroup M] in
theorem algebraMap_smul_mk (n : ℤ) (r : R) (m : M) :
    algebraMap R A r • mk n m = mk n (algebraMap R A r • m) := by
  rw [smul_mk_eq, twist_algebraMap]

end Shift

/-- An isomorphism of dg modules as an isomorphism in `DGModuleCat A`. -/
@[simps]
def DGModuleEquiv.toDGModuleCatIso {A : Type u} [Ring A] [DGAddCommGroup A] {M N : Type v}
    [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (e : M ≃ᵈᵍ[A] N) :
    DGModuleCat.of A M ≅ DGModuleCat.of A N where
  hom := DGModuleCat.ofHom e.toDGModuleHom
  inv := DGModuleCat.ofHom e.symm.toDGModuleHom
  hom_inv_id := DGModuleCat.hom_ext_apply fun x => e.symm_apply_apply x
  inv_hom_id := DGModuleCat.hom_ext_apply fun x => e.apply_symm_apply x

/-! ### The shift on dg modules -/

namespace DGModuleCat

open Shift

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The shift functor `M ↦ Shift n M` on dg modules (auxiliary definition for
`DG.DGModuleCat.hasShift`; use `shiftFunctor (DGModuleCat A) n`). -/
@[simps obj]
def shiftFunctorAux (n : ℤ) : DGModuleCat.{v} A ⥤ DGModuleCat.{v} A where
  obj M := of A (Shift n M)
  map f := ofHom (f.hom.shift n)

/-- The shift by `0` is the identity (auxiliary definition for `DG.DGModuleCat.hasShift`). -/
def shiftFunctorZeroAux : shiftFunctorAux.{v} A 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => Shift.zeroEquiv.toDGModuleCatIso) fun _ => rfl

/-- The shift by `a + b` is the shift by `a` followed by the shift by `b` (auxiliary definition
for `DG.DGModuleCat.hasShift`). -/
def shiftFunctorAddAux (a b : ℤ) :
    shiftFunctorAux.{v} A (a + b) ≅ shiftFunctorAux A a ⋙ shiftFunctorAux A b :=
  NatIso.ofComponents (fun _ => (shiftShiftEquiv a b (a + b) rfl).toDGModuleCatIso) fun _ => rfl

theorem eqToHom_shift_apply {a b : ℤ} (h : a = b) (M : DGModuleCat.{v} A)
    (p : (shiftFunctorAux A a).obj M = (shiftFunctorAux A b).obj M) (x : Shift a M) :
    (eqToHom p) x = Shift.mk b (unmk a x) := by
  subst h
  rfl

/-- The shift on dg modules: `M⟦n⟧ = Shift n M`. -/
instance hasShift : HasShift (DGModuleCat.{v} A) ℤ :=
  hasShiftMk _ _
    { F := shiftFunctorAux A
      zero := shiftFunctorZeroAux A
      add := shiftFunctorAddAux A
      assoc_hom_app := fun m₁ m₂ m₃ X => hom_ext_apply fun x => by
        rw [comp_apply, comp_apply, comp_apply, eqToHom_shift_apply A (add_assoc m₁ m₂ m₃)]
        rfl
      zero_add_hom_app := fun n X => hom_ext_apply fun x => by
        rw [comp_apply]
        erw [eqToHom_shift_apply A (zero_add n)]
        rfl
      add_zero_hom_app := fun n X => hom_ext_apply fun x => by
        rw [comp_apply]
        erw [eqToHom_shift_apply A (add_zero n)]
        rfl }

variable {A}

@[simp]
theorem shiftFunctor_obj (n : ℤ) (M : DGModuleCat.{v} A) :
    (shiftFunctor (DGModuleCat.{v} A) n).obj M = of A (Shift n M) := rfl

@[simp]
theorem shiftFunctor_map_hom (n : ℤ) {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    ((shiftFunctor (DGModuleCat.{v} A) n).map f).hom = f.hom.shift n := rfl

theorem shiftFunctor_map_apply (n : ℤ) {M N : DGModuleCat.{v} A} (f : M ⟶ N) (x : Shift n M) :
    ((shiftFunctor (DGModuleCat.{v} A) n).map f) x = Shift.mk n (f (unmk n x)) := rfl

theorem shiftFunctorZero_hom_app_apply (M : DGModuleCat.{v} A) (x : Shift 0 M) :
    ((shiftFunctorZero (DGModuleCat.{v} A) ℤ).hom.app M) x = unmk 0 x := rfl

theorem shiftFunctorZero_inv_app_apply (M : DGModuleCat.{v} A) (x : M) :
    ((shiftFunctorZero (DGModuleCat.{v} A) ℤ).inv.app M) x = Shift.mk 0 x := rfl

theorem shiftFunctorAdd'_hom_app_apply (a b c : ℤ) (h : a + b = c) (M : DGModuleCat.{v} A)
    (x : Shift c M) :
    ((shiftFunctorAdd' (DGModuleCat.{v} A) a b c h).hom.app M) x =
      Shift.mk b (Shift.mk a (unmk c x)) := by
  subst h
  rfl

theorem shiftFunctorAdd'_inv_app_apply (a b c : ℤ) (h : a + b = c) (M : DGModuleCat.{v} A)
    (x : Shift b (Shift a M)) :
    ((shiftFunctorAdd' (DGModuleCat.{v} A) a b c h).inv.app M) x =
      Shift.mk c (unmk a (unmk b x)) := by
  subst h
  rfl

theorem shiftFunctorAdd_hom_app_apply (a b : ℤ) (M : DGModuleCat.{v} A) (x : Shift (a + b) M) :
    ((shiftFunctorAdd (DGModuleCat.{v} A) a b).hom.app M) x =
      Shift.mk b (Shift.mk a (unmk (a + b) x)) := rfl

theorem shiftFunctorAdd_inv_app_apply (a b : ℤ) (M : DGModuleCat.{v} A)
    (x : Shift b (Shift a M)) :
    ((shiftFunctorAdd (DGModuleCat.{v} A) a b).inv.app M) x =
      Shift.mk (a + b) (unmk a (unmk b x)) := rfl

theorem shiftFunctorComm_hom_app_apply (a b : ℤ) (M : DGModuleCat.{v} A)
    (x : Shift b (Shift a M)) :
    ((shiftFunctorComm (DGModuleCat.{v} A) a b).hom.app M) x =
      Shift.mk a (Shift.mk b (unmk a (unmk b x))) := by
  rw [shiftFunctorComm_eq _ a b _ rfl, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    comp_apply, shiftFunctorAdd'_inv_app_apply, shiftFunctorAdd'_hom_app_apply]
  rfl

instance (n : ℤ) : (shiftFunctor (DGModuleCat.{v} A) n).Additive where
  map_add := rfl

instance (priority := 100) shiftFunctor_linear (R : Type*) [CommRing R] [Algebra R A]
    [DGAlgebra R A] (n : ℤ) : (shiftFunctor (DGModuleCat.{v} A) n).Linear R where
  map_smul f r := hom_ext_apply fun x => (Shift.algebraMap_smul_mk R n r (f (unmk n x))).symm

end DGModuleCat

/-! ### Shifts of homotopies -/

namespace DGHomotopy

variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] {f g : M →ᵈᵍ[A] N}

/-- A homotopy `h` from `f` to `g` induces the homotopy `(-1)ⁿ • h⟦n⟧` from `f⟦n⟧` to `g⟦n⟧`
(Mathlib's `Homotopy.shift`, with the same sign). -/
@[simps]
def shift (h : DGHomotopy f g) (n : ℤ) : DGHomotopy (f.shift n) (g.shift n) where
  hom := koszulSign n • h.hom.shift n
  ofHom_eq := by
    rw [δ_units_smul, Cochain.δ_shift, smul_smul, Int.units_mul_self, one_smul,
      ← Cochain.shift_ofHom, ← Cochain.shift_ofHom, h.ofHom_eq, Cochain.shift_add]

end DGHomotopy

theorem Homotopic.shift {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] {f g : M →ᵈᵍ[A] N}
    (h : Homotopic f g) (n : ℤ) : Homotopic (f.shift n) (g.shift n) :=
  ⟨h.some.shift n⟩

/-! ### The shift on the homotopy category -/

namespace HomotopyCategory

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

instance : (DGModuleCat.homotopic.{v} A).IsCompatibleWithShift ℤ :=
  ⟨fun n _ _ _ _ h => Homotopic.shift h n⟩

/-- The shift on the homotopy category, induced by the shift on dg modules. -/
noncomputable instance hasShift : HasShift (HomotopyCategory.{v} A) ℤ := by
  dsimp only [HomotopyCategory]
  infer_instance

/-- The quotient functor from dg modules to the homotopy category commutes with the shift. -/
noncomputable instance commShiftQuotient : (quotient A).CommShift ℤ :=
  Quotient.functor_commShift (DGModuleCat.homotopic.{v} A) ℤ

instance (n : ℤ) : (shiftFunctor (HomotopyCategory.{v} A) n).Additive := by
  have : (quotient A ⋙ shiftFunctor _ n).Additive :=
    Functor.additive_of_iso ((quotient A).commShiftIso n)
  exact Functor.additive_of_full_essSurj_comp (quotient A) _

end HomotopyCategory

/-! ### The forgetful functor commutes with the shifts -/

namespace DGModuleCat

open Shift DGModuleCat.Algebra

variable (R : Type w) {A : Type u} [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]

theorem toComplex_d_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i + 1 = j)
    (x : DGModule.gradingSubmodule R A M i) :
    (((toComplex R M).d i j).hom x).1 = d (x : M) := by
  subst h
  rw [toComplex_d]
  rfl

theorem toComplex_XIsoOfEq_hom_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i = j)
    (x : DGModule.gradingSubmodule R A M i) :
    (((toComplex R M).XIsoOfEq h).hom.hom x).1 = x := by
  subst h
  rfl

theorem forget_obj_XIsoOfEq_hom_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i = j)
    (x : DGModule.gradingSubmodule R A M i) :
    ((((forget R A).obj M).XIsoOfEq h).hom.hom x).1 = x := by
  subst h
  rfl

theorem toComplex_XIsoOfEq_inv_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i = j)
    (x : DGModule.gradingSubmodule R A M j) :
    (((toComplex R M).XIsoOfEq h).inv.hom x).1 = x := by
  subst h
  rfl

/-- The homogeneous component `(M⟦n⟧)ⁱ = Mⁱ⁺ⁿ`, as an `R`-linear equivalence. -/
def shiftGradingLinearEquiv (M : DGModuleCat.{v} A) (n i : ℤ) :
    DGModule.gradingSubmodule R A ((shiftFunctor (DGModuleCat.{v} A) n).obj M) i ≃ₗ[R]
      DGModule.gradingSubmodule R A M (i + n) where
  toFun x := ⟨unmk n x.1, x.2⟩
  invFun y := ⟨Shift.mk n y.1, y.2⟩
  map_add' _ _ := rfl
  map_smul' r x := Subtype.ext (by
    have h := unmk_smul_eq (n := n) (M := M) (algebraMap R A r) x.1
    rw [twist_algebraMap] at h
    exact h)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The underlying cochain complex of `M⟦n⟧` is the shifted underlying cochain complex of `M`:
in degree `i` both are `Mⁱ⁺ⁿ`, and the differentials are `(-1)ⁿ d`. -/
def forgetShiftIso (n : ℤ) (M : DGModuleCat.{v} A) :
    (forget R A).obj ((shiftFunctor (DGModuleCat.{v} A) n).obj M) ≅
      (shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) n).obj ((forget R A).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (shiftGradingLinearEquiv R M n i).toModuleIso) (by
      rintro i j (rfl : i + 1 = j)
      refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
      have h1 := toComplex_d_apply R M (show i + n + 1 = i + 1 + n by ring)
        (shiftGradingLinearEquiv R M n i x)
      have h2 := toComplex_d_apply R ((shiftFunctor (DGModuleCat.{v} A) n).obj M) rfl x
      change n.negOnePow • (((toComplex R M).d (i + n) (i + 1 + n)).hom
          (shiftGradingLinearEquiv R M n i x)).1 =
        unmk n (((toComplex R ((shiftFunctor (DGModuleCat.{v} A) n).obj M)).d i (i + 1)).hom x).1
      rw [h1, h2]
      rfl)

theorem forgetShiftIso_hom_f_apply (n : ℤ) (M : DGModuleCat.{v} A) (i : ℤ)
    (x : DGModule.gradingSubmodule R A ((shiftFunctor (DGModuleCat.{v} A) n).obj M) i) :
    (((forgetShiftIso R n M).hom.f i).hom x).1 = unmk n x.1 := rfl

theorem forgetShiftIso_inv_f_apply (n : ℤ) (M : DGModuleCat.{v} A) (i : ℤ)
    (x : DGModule.gradingSubmodule R A M (i + n)) :
    (((forgetShiftIso R n M).inv.f i).hom x).1 = Shift.mk n x.1 := rfl

theorem forget_map_f_apply {M N : DGModuleCat.{v} A} (f : M ⟶ N) (i : ℤ)
    (x : DGModule.gradingSubmodule R A M i) :
    ((((forget R A).map f).f i).hom x).1 = f x.1 := rfl

/-- The commutation of the forgetful functor with the shifts. -/
def forgetCommShiftIso (n : ℤ) :
    shiftFunctor (DGModuleCat.{v} A) n ⋙ forget R A ≅
      forget R A ⋙ shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) n :=
  NatIso.ofComponents (forgetShiftIso R n) fun _ =>
    HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem forgetCommShiftIso_hom_app_f_apply (n : ℤ) (M : DGModuleCat.{v} A) (i : ℤ)
    (x : DGModule.gradingSubmodule R A ((shiftFunctor (DGModuleCat.{v} A) n).obj M) i) :
    ((((forgetCommShiftIso R n).hom.app M).f i).hom x).1 = unmk n x.1 := rfl

/-- The forgetful functor from dg modules to cochain complexes commutes with the shifts. -/
instance forgetCommShift : (forget R A).CommShift ℤ where
  iso := forgetCommShiftIso R
  zero := by
    ext M : 3
    rw [Functor.CommShift.isoZero_hom_app]
    ext i x : 3
    apply Subtype.ext
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CochainComplex.shiftFunctorZero_inv_app_f]
    exact (forget_obj_XIsoOfEq_hom_apply R M (show i = i + 0 by omega)
      ((((forget R A).map ((shiftFunctorZero (DGModuleCat.{v} A) ℤ).hom.app M)).f i).hom x)).symm
  add a b := by
    ext M : 3
    rw [Functor.CommShift.isoAdd_hom_app]
    ext i x : 3
    apply Subtype.ext
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CochainComplex.shiftFunctorAdd_inv_app_f]
    symm
    refine (forget_obj_XIsoOfEq_hom_apply R M _ _).trans ?_
    rfl

end DGModuleCat

end DG
