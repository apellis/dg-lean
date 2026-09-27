import Mathlib.CategoryTheory.Shift.Basic
import DG.Category.Homotopy.Hom
import DG.Module.Shift

/-!
# Shifts of dg modules over a dg category

Let `C` be a dg category. This file defines the shift `M⟦n⟧` of a dg module `M` over `C` and
equips `DG.CatModule C` with a shift by `ℤ` (`CategoryTheory.HasShift`). It is a port of
`DG.Module.Shift` and of the first part of `DG.Homotopy.Shift` (the case of a dg ring), with
the same conventions, which are those of Mathlib's `CochainComplex.shiftFunctor`:

* `DG.CatModule.shift n M`: the dg module with values `(M⟦n⟧) X = DG.Shift n (M X)`, i.e.
  `((M⟦n⟧) X)ᵏ = (M X)ᵏ⁺ⁿ` with the differential `(-1)ⁿ d`, and the action twisted by the Koszul
  sign, `f • m = (-1)^{n |f|} (f • m)` for `f` homogeneous. The values are the shifts
  `DG.Shift n (M.obj X)` of dg abelian groups of `DG.Module.Shift`, so that the identifications
  `DG.Shift.mk`, `DG.Shift.unmk` and their lemmas apply objectwise.
* `DG.CatModule.twist n : (X ⟶ Y) →+ (X ⟶ Y)`, `f ↦ (-1)^{n |f|} f` on homogeneous morphisms,
  compatible with composition and identities (`DG.CatModule.twist_comp`); the action of
  `M⟦n⟧` is the action of `M` precomposed with it.
* `DG.CatModule.shiftMap n φ : M⟦n⟧ ⟶ N⟦n⟧`, the same underlying maps.
* `DG.CatModule.shiftZeroIso M : M⟦0⟧ ≅ M` and
  `DG.CatModule.shiftShiftIso a b c h M : M⟦c⟧ ≅ M⟦a⟧⟦b⟧` for `a + b = c`, the identity on
  elements.
* `DG.CatModule.hasShift`: the shift on `CatModule C`, built with Mathlib's `hasShiftMk`; the
  shift functors are additive.

The shift of a dg module over `C` is written `shift n M` (a term of `CatModule C`) rather than
`Shift n M` (the dg-ring version's type synonym), whose values it is.
-/

open CategoryTheory DirectSum

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### The twist of the morphisms -/

section Twist

variable (n : ℤ) {X Y : C}

/-- The additive map `f ↦ (-1)^{n |f|} f` on a Hom group of `C`, `f` homogeneous of degree
`|f|`. -/
def twist : (X ⟶ Y) →+ (X ⟶ Y) :=
  (DirectSum.toAddMonoid fun i : ℤ =>
    (DistribMulAction.toAddMonoidHom (X ⟶ Y) (koszulSign (n * i))).comp
      (grading (M := X ⟶ Y) i).subtype).comp
    (decomposeAddEquiv (grading (M := X ⟶ Y))).toAddMonoidHom

variable {n}

theorem twist_of_mem {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) :
    twist n f = koszulSign (n * i) • f := by
  simp only [twist, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    decomposeAddEquiv_apply, decompose_of_mem _ hf, toAddMonoid_of]
  rfl

theorem twist_mem {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) : twist n f ∈ grading i := by
  rw [twist_of_mem hf]
  exact units_smul_mem_grading _ hf

@[simp]
theorem twist_zero_apply (f : X ⟶ Y) : twist 0 f = f := by
  induction f using induction_on with
  | h_zero => simp
  | h_homogeneous f => rw [twist_of_mem f.2, zero_mul, koszulSign, Int.negOnePow_zero, one_smul]
  | h_add f f' hf hf' => rw [map_add, hf, hf']

theorem twist_twist (m : ℤ) (f : X ⟶ Y) : twist m (twist n f) = twist (m + n) f := by
  induction f using induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rw [twist_of_mem f.2, Units.smul_def, map_zsmul, ← Units.smul_def, twist_of_mem f.2,
      twist_of_mem f.2, smul_smul, ← koszulSign_add, add_mul, add_comm]
  | h_add f f' hf hf' => rw [map_add, map_add, hf, hf', map_add]

variable [DGCategory C]

@[simp]
theorem twist_id (X : C) : twist n (𝟙 X) = 𝟙 X := by
  rw [twist_of_mem (id_mem_grading X), mul_zero, koszulSign_zero, one_smul]

theorem twist_comp {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : twist n (f ≫ g) = twist n f ≫ twist n g := by
  induction f using induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rename_i i
    induction g using induction_on with
    | h_zero => simp
    | h_homogeneous g =>
      rename_i j
      rw [twist_of_mem f.2, twist_of_mem g.2, twist_of_mem (comp_mem_grading f.2 g.2),
        comp_units_smul, units_smul_comp, smul_smul, ← koszulSign_add, mul_add, add_comm]
    | h_add g g' hg hg' => rw [Preadditive.comp_add, map_add, hg, hg', map_add,
        Preadditive.comp_add]
  | h_add f f' hf hf' => rw [Preadditive.add_comp, map_add, hf, hf', map_add, Preadditive.add_comp]

end Twist

/-! ### The shift of a dg module -/

section Shift

variable [DGCategory C]

open Shift

/-- The shift `M⟦n⟧` of a dg module over `C`: the values `DG.Shift n (M.obj X)`, with
`((M⟦n⟧) X)ᵏ = (M X)ᵏ⁺ⁿ`, the differential `(-1)ⁿ d`, and the action
`f • m = (-1)^{n |f|} (f • m)` for `f` homogeneous. -/
def shift (n : ℤ) (M : CatModule.{w} C) : CatModule.{w} C where
  obj X := Shift n (M.obj X)
  act :=
    { toFun := fun f => (Shift.mk n).toAddMonoidHom.comp
        ((M.act (twist n f)).comp (Shift.unmk n).toAddMonoidHom)
      map_zero' := by ext; simp
      map_add' := fun f g => by ext; simp [act_apply] }
  act_mem' {X Y i j f m} hf hm := by
    change twist n f • unmk n m ∈ grading (i + j + n)
    rw [add_assoc]
    exact smul_mem_grading (twist_mem hf) (unmk_mem_grading hm)
  act_id' X m := by
    change Shift.mk n (twist n (𝟙 X) • unmk n m) = m
    rw [twist_id, id_smul, mk_unmk]
  act_comp' f g m := by
    change Shift.mk n (twist n (f ≫ g) • unmk n m) = Shift.mk n (twist n g • twist n f • unmk n m)
    rw [twist_comp, comp_smul]
  d_act' {X Y i f} hf m := by
    obtain ⟨m, rfl⟩ := mk_surjective (n := n) m
    change d (Shift.mk n (twist n f • m)) =
      Shift.mk n (twist n (d f) • m) + koszulSign i • Shift.mk n (twist n f • (koszulSign n • d m))
    rw [twist_of_mem hf, twist_of_mem (d_mem hf)]
    simp only [d_mk, units_smul_smul, smul_units_smul, d_units_smul, d_smul hf, _root_.smul_add,
      smul_smul, ← koszulSign_add, ← mk_units_smul, ← mk_add, mk_inj]
    refine congrArg₂ (· + ·) (congrArg (· • _) (congrArg koszulSign (by ring)))
      (congrArg (· • _) (congrArg koszulSign (by ring)))

namespace shift

variable {n : ℤ} {M : CatModule.{w} C} {X : C}

theorem obj_eq (n : ℤ) (M : CatModule.{w} C) (X : C) :
    (shift n M).obj X = Shift n (M.obj X) := rfl

variable (n) in
/-- The identity `M X → (M⟦n⟧) X`, as an additive equivalence (the map `DG.Shift.mk n`). -/
def mk : M.obj X ≃+ (shift n M).obj X := Shift.mk n

variable (n) in
/-- The identity `(M⟦n⟧) X → M X`, as an additive equivalence (the map `DG.Shift.unmk n`). -/
def unmk : (shift n M).obj X ≃+ M.obj X := Shift.unmk n

@[simp] theorem unmk_mk (m : M.obj X) : unmk n (mk n m) = m := rfl
@[simp] theorem mk_unmk (m : (shift n M).obj X) : mk n (unmk n m) = m := rfl
@[simp] theorem mk_symm : (mk n (M := M) (X := X)).symm = unmk n := rfl
@[simp] theorem unmk_symm : (unmk n (M := M) (X := X)).symm = mk n := rfl

theorem mk_injective : Function.Injective (mk n (M := M) (X := X)) := (mk n).injective
theorem mk_surjective : Function.Surjective (mk n (M := M) (X := X)) := (mk n).surjective
theorem unmk_injective : Function.Injective (unmk n (M := M) (X := X)) := (unmk n).injective

@[simp] theorem mk_inj {m m' : M.obj X} : mk n m = mk n m' ↔ m = m' := (mk n).injective.eq_iff
@[simp] theorem unmk_inj {m m' : (shift n M).obj X} : unmk n m = unmk n m' ↔ m = m' :=
  (unmk n).injective.eq_iff

@[simp] theorem mk_units_smul (u : ℤˣ) (m : M.obj X) : mk n (u • m) = u • mk n m := rfl
@[simp] theorem unmk_units_smul (u : ℤˣ) (m : (shift n M).obj X) :
    unmk n (u • m) = u • unmk n m := rfl

theorem mem_grading_iff {k : ℤ} {m : M.obj X} : mk n m ∈ grading k ↔ m ∈ grading (k + n) :=
  Iff.rfl

theorem mem_grading_iff' {k : ℤ} {m : (shift n M).obj X} :
    m ∈ grading k ↔ unmk n m ∈ grading (k + n) := Iff.rfl

theorem mk_mem_grading {k : ℤ} {m : M.obj X} (hm : m ∈ grading k) : mk n m ∈ grading (k - n) :=
  mem_grading_iff.mpr (by rwa [sub_add_cancel])

theorem unmk_mem_grading {k : ℤ} {m : (shift n M).obj X} (hm : m ∈ grading k) :
    unmk n m ∈ grading (k + n) :=
  mem_grading_iff'.mp hm

@[simp] theorem d_mk (m : M.obj X) : d (mk n m) = mk n (koszulSign n • d m) := rfl
@[simp] theorem unmk_d (m : (shift n M).obj X) : unmk n (d m) = koszulSign n • d (unmk n m) :=
  rfl

theorem smul_mk_eq {Y : C} (f : X ⟶ Y) (m : M.obj X) :
    f • mk n m = mk (M := M) n (twist n f • m) := rfl

theorem unmk_smul_eq {Y : C} (f : X ⟶ Y) (m : (shift n M).obj X) :
    unmk n (f • m) = twist n f • unmk n m := rfl

theorem smul_mk {Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (m : M.obj X) :
    f • mk n m = mk (M := M) n (koszulSign (n * i) • (f • m)) := by
  rw [smul_mk_eq, twist_of_mem hf, units_smul_smul]

theorem unmk_smul {Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (m : (shift n M).obj X) :
    unmk n (f • m) = koszulSign (n * i) • (f • unmk n m) := by
  rw [unmk_smul_eq, twist_of_mem hf, units_smul_smul]

theorem mk_smul {Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (m : M.obj X) :
    mk (M := M) n (f • m) = koszulSign (n * i) • (f • mk n m) := by
  rw [smul_mk hf, mk_units_smul, smul_smul, ← koszulSign_add, ← two_mul,
    koszulSign_even (even_two_mul _), one_smul]

end shift

/-! ### The shift of a morphism -/

variable {n : ℤ} {M N P : CatModule.{w} C}

variable (n) in
/-- The shift of a morphism of dg modules: the same underlying maps `M⟦n⟧ → N⟦n⟧`. -/
def shiftMap (φ : M ⟶ N) : shift n M ⟶ shift n N where
  app X := (shift.mk (M := N) (X := X) n).toAddMonoidHom.comp
    ((φ.app X).comp (shift.unmk (M := M) (X := X) n).toAddMonoidHom)
  map_mem' hm := φ.map_mem hm
  map_d' {X} m := by
    change shift.mk n (φ.app X (shift.unmk n (d m))) = d (shift.mk n (φ.app X (shift.unmk n m)))
    rw [shift.unmk_d, shift.d_mk, Units.smul_def, map_zsmul, ← Units.smul_def, Hom.map_d]
  map_smul' {X Y} f m := by
    change shift.mk n (φ.app Y (shift.unmk n (f • m))) = f • shift.mk n (φ.app X (shift.unmk n m))
    rw [shift.unmk_smul_eq, shift.smul_mk_eq, Hom.map_smul]

@[simp]
theorem shiftMap_app_mk (φ : M ⟶ N) {X : C} (m : M.obj X) :
    (shiftMap n φ).app X (shift.mk n m) = shift.mk n (φ.app X m) := rfl

theorem unmk_shiftMap_app (φ : M ⟶ N) {X : C} (m : (shift n M).obj X) :
    shift.unmk n ((shiftMap n φ).app X m) = φ.app X (shift.unmk n m) := rfl

variable (n M) in
@[simp]
theorem shiftMap_id : shiftMap n (𝟙 M) = 𝟙 (shift n M) := rfl

@[simp]
theorem shiftMap_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    shiftMap n (φ ≫ ψ) = shiftMap n φ ≫ shiftMap n ψ := rfl

variable (n M N) in
@[simp] theorem shiftMap_zero : shiftMap n (0 : M ⟶ N) = 0 := rfl
@[simp] theorem shiftMap_add (φ ψ : M ⟶ N) : shiftMap n (φ + ψ) = shiftMap n φ + shiftMap n ψ :=
  rfl
@[simp] theorem shiftMap_neg (φ : M ⟶ N) : shiftMap n (-φ) = -shiftMap n φ := rfl
@[simp] theorem shiftMap_sub (φ ψ : M ⟶ N) : shiftMap n (φ - ψ) = shiftMap n φ - shiftMap n ψ :=
  rfl
@[simp] theorem shiftMap_units_smul (u : ℤˣ) (φ : M ⟶ N) :
    shiftMap n (u • φ) = u • shiftMap n φ := rfl

/-! ### The shift by `0` and the composition of shifts -/

variable (M) in
/-- The shift by `0` is the identity: `M⟦0⟧ ≅ M`, the identity on elements. -/
def shiftZeroIso : shift 0 M ≅ M :=
  isoMk (fun _ => shift.unmk 0) (fun {X k m} => by
      rw [shift.mem_grading_iff', add_zero])
    (fun m => by rw [shift.unmk_d, koszulSign_zero, one_smul])
    (fun f m => by rw [shift.unmk_smul_eq, twist_zero_apply])

@[simp]
theorem shiftZeroIso_hom_app {X : C} (m : (shift 0 M).obj X) :
    (shiftZeroIso M).hom.app X m = shift.unmk 0 m := rfl

@[simp]
theorem shiftZeroIso_inv_app {X : C} (m : M.obj X) :
    (shiftZeroIso M).inv.app X m = shift.mk 0 m := rfl

variable (M) in
/-- The identification `M⟦c⟧ ≅ M⟦a⟧⟦b⟧` when `a + b = c`, the identity on elements. -/
def shiftShiftIso (a b c : ℤ) (h : a + b = c) : shift c M ≅ shift b (shift a M) :=
  isoMk (fun _ => ((shift.unmk c).trans (shift.mk a)).trans (shift.mk b))
    (fun {X k m} => by
      change shift.mk b (shift.mk a (shift.unmk c m)) ∈ grading k ↔ m ∈ grading k
      rw [shift.mem_grading_iff, shift.mem_grading_iff, shift.mem_grading_iff' (n := c), ← h,
        add_assoc, add_comm b a])
    (fun m => by
      change shift.mk b (shift.mk a (shift.unmk c (d m))) =
        d (shift.mk b (shift.mk a (shift.unmk c m)))
      rw [shift.unmk_d, shift.d_mk, shift.d_mk, ← h, koszulSign_add, mul_comm, mul_smul]
      rfl)
    (fun f m => by
      change shift.mk b (shift.mk a (shift.unmk c (f • m))) =
        f • shift.mk b (shift.mk a (shift.unmk c m))
      rw [shift.unmk_smul_eq, shift.smul_mk_eq, shift.smul_mk_eq, twist_twist, ← h])

@[simp]
theorem shiftShiftIso_hom_app (a b c : ℤ) (h : a + b = c) {X : C} (m : (shift c M).obj X) :
    (shiftShiftIso M a b c h).hom.app X m = shift.mk b (shift.mk a (shift.unmk c m)) := rfl

@[simp]
theorem shiftShiftIso_inv_app (a b c : ℤ) (h : a + b = c) {X : C}
    (m : (shift b (shift a M)).obj X) :
    (shiftShiftIso M a b c h).inv.app X m = shift.mk c (shift.unmk a (shift.unmk b m)) := rfl

/-- The identification `M⟦a⟧⟦b⟧ ≅ M⟦b⟧⟦a⟧`, the identity on elements. -/
def shiftComm (a b : ℤ) : shift b (shift a M) ≅ shift a (shift b M) :=
  (shiftShiftIso M a b (a + b) rfl).symm ≪≫ shiftShiftIso M b a (a + b) (add_comm b a)

@[simp]
theorem shiftComm_hom_app (a b : ℤ) {X : C} (m : (shift b (shift a M)).obj X) :
    (shiftComm (M := M) a b).hom.app X m =
      shift.mk a (shift.mk b (shift.unmk a (shift.unmk b m))) := rfl

end Shift

/-! ### The shift on dg modules -/

section HasShift

variable (C) [DGCategory C]

/-- The shift functor `M ↦ M⟦n⟧` on dg modules (auxiliary definition for
`DG.CatModule.hasShift`; use `shiftFunctor (CatModule C) n`). -/
@[simps obj]
def shiftFunctorAux (n : ℤ) : CatModule.{w} C ⥤ CatModule.{w} C where
  obj M := shift n M
  map φ := shiftMap n φ

/-- The shift by `0` is the identity (auxiliary definition for `DG.CatModule.hasShift`). -/
def shiftFunctorZeroAux : shiftFunctorAux.{w} C 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => shiftZeroIso M) fun _ => rfl

/-- The shift by `a + b` is the shift by `a` followed by the shift by `b` (auxiliary definition
for `DG.CatModule.hasShift`). -/
def shiftFunctorAddAux (a b : ℤ) :
    shiftFunctorAux.{w} C (a + b) ≅ shiftFunctorAux C a ⋙ shiftFunctorAux C b :=
  NatIso.ofComponents (fun M => shiftShiftIso M a b (a + b) rfl) fun _ => rfl

variable {C} in
theorem eqToHom_shift_app {a b : ℤ} (h : a = b) (M : CatModule.{w} C)
    (p : (shiftFunctorAux C a).obj M = (shiftFunctorAux C b).obj M) {X : C}
    (x : (shift a M).obj X) :
    (eqToHom p).app X x = shift.mk b (shift.unmk a x) := by
  subst h
  rfl

/-- The shift on dg modules over `C`: `M⟦n⟧ = shift n M`. -/
instance hasShift : HasShift (CatModule.{w} C) ℤ :=
  hasShiftMk _ _
    { F := shiftFunctorAux C
      zero := shiftFunctorZeroAux C
      add := shiftFunctorAddAux C
      assoc_hom_app := fun m₁ m₂ m₃ M => hom_ext fun X x => by
        rw [comp_app, comp_app, comp_app, eqToHom_shift_app (add_assoc m₁ m₂ m₃)]
        rfl
      zero_add_hom_app := fun n M => hom_ext fun X x => by
        rw [comp_app]
        dsimp only [Functor.id_obj]
        rw [eqToHom_shift_app (zero_add n)]
        rfl
      add_zero_hom_app := fun n M => hom_ext fun X x => by
        rw [comp_app]
        dsimp only [Functor.id_obj]
        rw [eqToHom_shift_app (add_zero n)]
        rfl }

variable {C}

@[simp]
theorem shiftFunctor_obj (n : ℤ) (M : CatModule.{w} C) :
    (shiftFunctor (CatModule.{w} C) n).obj M = shift n M := rfl

@[simp]
theorem shiftFunctor_map (n : ℤ) {M N : CatModule.{w} C} (φ : M ⟶ N) :
    (shiftFunctor (CatModule.{w} C) n).map φ = shiftMap n φ := rfl

theorem shiftFunctorZero_hom_app_app (M : CatModule.{w} C) {X : C} (x : (shift 0 M).obj X) :
    ((shiftFunctorZero (CatModule.{w} C) ℤ).hom.app M).app X x = shift.unmk 0 x := rfl

theorem shiftFunctorZero_inv_app_app (M : CatModule.{w} C) {X : C} (x : M.obj X) :
    ((shiftFunctorZero (CatModule.{w} C) ℤ).inv.app M).app X x = shift.mk 0 x := rfl

theorem shiftFunctorAdd'_hom_app_app (a b c : ℤ) (h : a + b = c) (M : CatModule.{w} C)
    {X : C} (x : (shift c M).obj X) :
    ((shiftFunctorAdd' (CatModule.{w} C) a b c h).hom.app M).app X x =
      shift.mk b (shift.mk a (shift.unmk c x)) := by
  subst h
  rfl

theorem shiftFunctorAdd'_inv_app_app (a b c : ℤ) (h : a + b = c) (M : CatModule.{w} C)
    {X : C} (x : (shift b (shift a M)).obj X) :
    ((shiftFunctorAdd' (CatModule.{w} C) a b c h).inv.app M).app X x =
      shift.mk c (shift.unmk a (shift.unmk b x)) := by
  subst h
  rfl

theorem shiftFunctorComm_hom_app_app (a b : ℤ) (M : CatModule.{w} C) {X : C}
    (x : (shift b (shift a M)).obj X) :
    ((shiftFunctorComm (CatModule.{w} C) a b).hom.app M).app X x =
      shift.mk a (shift.mk b (shift.unmk a (shift.unmk b x))) := by
  rw [shiftFunctorComm_eq _ a b _ rfl, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    comp_app, shiftFunctorAdd'_inv_app_app, shiftFunctorAdd'_hom_app_app]
  rfl

theorem shiftFunctorComm_hom_app_eq (a b : ℤ) (M : CatModule.{w} C) :
    (shiftFunctorComm (CatModule.{w} C) a b).hom.app M = (shiftComm (M := M) a b).hom :=
  hom_ext fun _ x => shiftFunctorComm_hom_app_app a b M x

instance (n : ℤ) : (shiftFunctor (CatModule.{w} C) n).Additive where
  map_add := rfl

end HasShift

end CatModule

end DG
