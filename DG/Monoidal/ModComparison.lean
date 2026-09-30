import Mathlib.CategoryTheory.Monoidal.Mod
import DG.Monoidal.MonComparison

/-!
# Dg modules as module objects in cochain complexes

For a dg `R`-algebra `A`, with monoid object `(DG.DGAlgCat.toMon R).obj A` in the monoidal
category `CochainComplex (ModuleCat R) ℤ` (`DG.Monoidal.MonComparison`), this file proves that
dg `A`-modules are the same as module objects over it (Mathlib's `Mod`, with a left action
`A ⊗ N ⟶ N`).

## Main definitions

* `DG.DGModuleCat.toMod A : DGModuleCat A ⥤ Mod (CochainComplex (ModuleCat.{u} R) ℤ) ((DGAlgCat.toMon R).obj A).X`: a dg module `N`
  goes to its underlying complex `DG.DGModuleCat.toComplex R N`, with action `A ⊗ N ⟶ N` given
  by `Aⁱ ⊗ Nʲ → Nⁱ⁺ʲ, a ⊗ m ↦ a • m` (`DG.DGModuleCat.act`; that it is a morphism of complexes
  is the Leibniz rule of the action);
* `DG.DGModuleCat.ofMod A : Mod (CochainComplex (ModuleCat.{u} R) ℤ) ((DGAlgCat.toMon R).obj A).X ⥤ DGModuleCat A`: a module object
  `P` goes to `⨁ n, Pⁿ` (`DG.ComplexSum P.X`), on which `a ∈ Aⁱ` acts by
  `ι_j x ↦ ι_{i+j} (act (a ⊗ x))` (`DG.ModObj.smulHom`);
* `DG.DGModuleCat.modEquivalence A : DGModuleCat A ≌ Mod (CochainComplex (ModuleCat.{u} R) ℤ) ((DGAlgCat.toMon R).obj A).X`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory HomologicalComplex DirectSum
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace DG

variable {R : Type u} [CommRing R]

open DGModuleCat.Algebra ComplexTensor DGAlgCat

/-! ### The action of a module object -/

namespace ModObj

variable {A : DGAlgCat.{u, u} R}

/-- The action `A ⊗ P ⟶ P` of a module object `P` over the monoid object of `A`. -/
def act (P : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X) : (toMonObj A).X ⊗ P.X ⟶ P.X :=
  γ[(toMonObj A).X, P.X]

theorem act_one (P : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X) :
    η[(toMonObj A).X] ▷ P.X ≫ act P = (λ_ P.X).hom :=
  CategoryTheory.ModObj.one_smul (M := (toMonObj A).X) P.X

theorem act_assoc (P : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X) :
    μ[(toMonObj A).X] ▷ P.X ≫ act P =
      (α_ (toMonObj A).X (toMonObj A).X P.X).hom ≫ (toMonObj A).X ◁ act P ≫ act P :=
  CategoryTheory.ModObj.mul_smul (M := (toMonObj A).X) P.X

theorem act_hom {P Q : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X} (g : P ⟶ Q) :
    act P ≫ g.hom = (toMonObj A).X ◁ g.hom ≫ act Q :=
  g.isModHom.smul_hom

end ModObj

/-! ### From dg modules to module objects -/

namespace DGModuleCat

variable {A : DGAlgCat.{u, u} R} (N : DGModuleCat.{u} A)

/-- The action `Aᵖ × Nᑫ → Nⁿ` (`p + q = n`) as an `R`-bilinear map. -/
def actBilin (p q n : ℤ) (h : p + q = n) :
    (complex A).X p →ₗ[R] (toComplex R N).X q →ₗ[R] (toComplex R N).X n :=
  LinearMap.mk₂ R (fun a m => ⟨a.1 • m.1, h ▸ smul_mem_grading a.2 m.2⟩)
    (fun a a' m => Subtype.ext (add_smul a.1 a'.1 m.1))
    (fun r a m => Subtype.ext (by
      show (algebraMap R A r * a.1) • m.1 = algebraMap R A r • (a.1 • m.1)
      rw [mul_smul]))
    (fun a m m' => Subtype.ext (smul_add a.1 m.1 m'.1))
    (fun r a m => Subtype.ext (by
      show a.1 • (algebraMap R A r • m.1) = algebraMap R A r • (a.1 • m.1)
      rw [← mul_smul, ← Algebra.commutes, mul_smul]))

/-- The action satisfies the Leibniz rule `d (a • m) = d a • m + (-1)^p a • d m` on the
underlying complexes. -/
theorem actBilin_leibniz (p q n : ℤ) (h : p + q = n) (a : (complex A).X p)
    (m : (toComplex R N).X q) :
    (toComplex R N).d n (n + 1) (actBilin N p q n h a m) =
      actBilin N (p + 1) q (n + 1) (by omega) ((complex A).d p (p + 1) a) m +
        p.negOnePow •
          actBilin N p (q + 1) (n + 1) (by omega) a ((toComplex R N).d q (q + 1) m) := by
  rw [DGModuleCat.toComplex_d, DGModuleCat.toComplex_d, DGModuleCat.toComplex_d]
  apply Subtype.ext
  change d (a.1 • m.1) = d a.1 • m.1 + ((p.negOnePow : ℤ) • (a.1 • d m.1))
  rw [d_smul a.2, Units.smul_def]

/-- The action of a dg algebra on a dg module as a morphism of complexes `A ⊗ N ⟶ N`; that it
is a morphism of complexes is the Leibniz rule for the action (`actBilin_leibniz`). -/
def act : (toMonObj A).X ⊗ toComplex R N ⟶ toComplex R N :=
  tensorDesc (toMonObj A).X (toComplex R N) (toComplex R N) (actBilin N) (actBilin_leibniz N)

@[simp]
theorem coe_act_f_tmul {p q n : ℤ} (h : p + q = n) (a : (toMonObj A).X.X p)
    (m : (toComplex R N).X q) :
    ((act N).f n (tmul (toMonObj A).X (toComplex R N) h a m)).1 = a.1 • m.1 := by
  rw [act, tensorDesc_f_tmul]
  rfl

/-- The module object structure on the underlying complex of a dg `A`-module. -/
instance modObjToComplex : CategoryTheory.ModObj (toMonObj A).X (toComplex R N) where
  smul := act N
  one_smul := by
    change η[(toMonObj A).X] ▷ toComplex R N ≫ act N = (λ_ _).hom
    ext n : 1
    refine unit_tensor_hom_ext fun m => Subtype.ext ?_
    rw [comp_f, ModuleCat.comp_apply, whiskerRight_f_tmul, coe_act_f_tmul,
      leftUnitor_hom_f_tmul]
    erw [one_f_unitOne]
    exact one_smul A m.1
  mul_smul := by
    change μ[(toMonObj A).X] ▷ toComplex R N ≫ act N =
      (α_ _ _ _).hom ≫ (toMonObj A).X ◁ act N ≫ act N
    ext n : 1
    refine hom_ext₃ fun p q r h a b m => Subtype.ext ?_
    simp only [comp_f, ModuleCat.comp_apply, whiskerRight_f_tmul, associator_hom_f_tmul,
      whiskerLeft_f_tmul, coe_act_f_tmul]
    erw [coe_mul_f_tmul]
    exact mul_smul a.1 b.1 m.1

/-- A dg `A`-module as a module object over the monoid object of `A`. -/
@[simps]
def toModObj : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X where
  X := toComplex R N

theorem toModObj_act : ModObj.act (toModObj N) = act N := rfl

variable {N} {N' N'' : DGModuleCat.{u} A}

theorem coe_toComplexMap_f_apply (f : N ⟶ N') (n : ℤ) (m : (toComplex R N).X n) :
    ((toComplexMap R f).f n m).1 = f m.1 :=
  rfl

/-- A morphism of dg modules as a morphism of module objects. -/
@[simps]
def toModMap (f : N ⟶ N') : toModObj N ⟶ toModObj N' where
  hom := toComplexMap R f
  isModHom.smul_hom := by
    change act N ≫ toComplexMap R f = (toMonObj A).X ◁ toComplexMap R f ≫ act N'
    ext n : 1
    refine ComplexTensor.hom_ext fun p q h a m => Subtype.ext ?_
    simp only [comp_f, ModuleCat.comp_apply, whiskerLeft_f_tmul,
      coe_act_f_tmul, coe_toComplexMap_f_apply]
    exact f.hom.map_smul a.1 m.1

variable (A) in
/-- The functor from dg `A`-modules to module objects over the monoid object of `A`. -/
@[simps]
def toMod : DGModuleCat.{u} A ⥤ Mod (CochainComplex (ModuleCat.{u} R) ℤ) ((DGAlgCat.toMon R).obj A).X where
  obj := toModObj
  map := toModMap
  map_id _ := by
    ext n : 3
    rfl
  map_comp _ _ := by
    ext n : 3
    rfl

end DGModuleCat

/-! ### From module objects to dg modules -/

namespace ModObj

variable {A : DGAlgCat.{u, u} R} (P : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X)

/-- The unit axiom of a module object on elements: `act (1 ⊗ x) = x`. -/
theorem one_act_apply {n : ℤ} (x : P.X.X n) :
    (ModObj.act P).f n (tmul (toMonObj A).X P.X (zero_add n) (oneX A) x) = x := by
  have := congrArg (fun φ => φ.f n (tmul _ P.X (zero_add n) (unitOne R) x)) (ModObj.act_one P)
  simp only [comp_f, ModuleCat.comp_apply, whiskerRight_f_tmul, leftUnitor_hom_f_tmul] at this
  rw [toMonObj_one] at this
  erw [one_f_unitOne] at this
  exact this

/-- The associativity axiom of a module object on elements:
`act (μ (a ⊗ b) ⊗ x) = act (a ⊗ act (b ⊗ x))`. -/
theorem assoc_apply {p q r n : ℤ} (h : p + q + r = n) (a : (toMonObj A).X.X p)
    (b : (toMonObj A).X.X q) (x : P.X.X r) :
    (ModObj.act P).f n (tmul _ P.X h ((μ[(toMonObj A).X]).f (p + q) (tmul _ _ rfl a b)) x) =
      (ModObj.act P).f n (tmul (toMonObj A).X P.X (show p + (q + r) = n by omega) a
        ((ModObj.act P).f (q + r) (tmul (toMonObj A).X P.X rfl b x))) := by
  have := congrArg (fun φ => φ.f n (tmul _ P.X h (tmul (toMonObj A).X (toMonObj A).X rfl a b) x))
    (ModObj.act_assoc P)
  simpa only [comp_f, ModuleCat.comp_apply, whiskerRight_f_tmul, whiskerLeft_f_tmul,
    associator_hom_f_tmul] using this

/-- The action `Aⁱ × Pʲ → ⨁ n, Pⁿ`, `(a, x) ↦ ι_{i+j} (act (a ⊗ x))`, as a biadditive map. -/
def smulAux (i j : ℤ) : (toMonObj A).X.X i →+ P.X.X j →+ ComplexSum P.X where
  toFun a :=
    { toFun := fun x =>
        ComplexSum.of P.X (i + j) ((ModObj.act P).f (i + j) (tmul (toMonObj A).X P.X rfl a x))
      map_zero' := by rw [tmul_zero_right, map_zero, map_zero]
      map_add' := fun x x' => by rw [tmul_add_right, map_add, map_add] }
  map_zero' := AddMonoidHom.ext fun x => by
    show ComplexSum.of P.X (i + j) ((ModObj.act P).f (i + j) (tmul (toMonObj A).X P.X rfl 0 x)) = 0
    rw [tmul_zero_left, map_zero, map_zero]
  map_add' a a' := AddMonoidHom.ext fun x => by
    show ComplexSum.of P.X (i + j) ((ModObj.act P).f (i + j) (tmul (toMonObj A).X P.X rfl (a + a') x)) =
      ComplexSum.of P.X (i + j) ((ModObj.act P).f (i + j) (tmul (toMonObj A).X P.X rfl a x)) +
        ComplexSum.of P.X (i + j) ((ModObj.act P).f (i + j) (tmul (toMonObj A).X P.X rfl a' x))
    rw [tmul_add_left, map_add, map_add]

theorem smulAux_apply (i j : ℤ) (a : (toMonObj A).X.X i) (x : P.X.X j) :
    smulAux P i j a x =
      ComplexSum.of P.X (i + j) ((ModObj.act P).f (i + j) (tmul (toMonObj A).X P.X rfl a x)) :=
  rfl

/-- The inclusion of `Aⁱ` into the degree-`i` component of the complex of `A`. -/
def inclX (i : ℤ) : grading (M := A) i →+ (toMonObj A).X.X i where
  toFun a := ⟨a.1, a.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

set_option maxHeartbeats 800000 in
/-- The action of a homogeneous element `a ∈ Aⁱ` on `⨁ n, Pⁿ`: `ι_j x ↦ ι_{i+j} (act (a ⊗ x))`. -/
def smulHomogeneous (i : ℤ) : grading (M := A) i →+ ComplexSum P.X →+ ComplexSum P.X where
  toFun a := DirectSum.toAddMonoid fun j => smulAux P i j (inclX i a)
  map_zero' := ComplexSum.addHom_ext fun j x => by
    refine (DirectSum.toAddMonoid_of (β := fun n => P.X.X n) _ j x).trans ?_
    rw [map_zero, map_zero]
    rfl
  map_add' a a' := ComplexSum.addHom_ext fun j x => by
    refine (DirectSum.toAddMonoid_of (β := fun n => P.X.X n) _ j x).trans ?_
    rw [AddMonoidHom.map_add (inclX i) a a', AddMonoidHom.map_add (smulAux P i j),
      AddMonoidHom.add_apply, AddMonoidHom.add_apply]
    exact congrArg₂ (· + ·)
      (DirectSum.toAddMonoid_of (β := fun n => P.X.X n)
        (fun k => smulAux P i k (inclX i a)) j x).symm
      (DirectSum.toAddMonoid_of (β := fun n => P.X.X n)
        (fun k => smulAux P i k (inclX i a')) j x).symm

/-- The action of `A` on `⨁ n, Pⁿ`. -/
def smulHom : A →+ ComplexSum P.X →+ ComplexSum P.X :=
  liftHomogeneous (grading (M := A)) (smulHomogeneous P)

theorem smulHom_of_mem {i : ℤ} {a : A} (ha : a ∈ grading i) {j : ℤ} (x : P.X.X j) :
    smulHom P a (ComplexSum.of P.X j x) =
      ComplexSum.of P.X (i + j) ((ModObj.act P).f (i + j) (tmul (toMonObj A).X P.X rfl ⟨a, ha⟩ x)) := by
  rw [smulHom, liftHomogeneous_of_mem _ _ ha]
  exact DirectSum.toAddMonoid_of (β := fun n => P.X.X n) _ j x

theorem smulHom_one (z : ComplexSum P.X) : smulHom P 1 z = z :=
  DFunLike.congr_fun (ComplexSum.addHom_ext (f := smulHom P 1) (g := AddMonoidHom.id _)
    fun j x => by
      rw [smulHom_of_mem P one_mem_grading, of_f_tmul (ModObj.act P) rfl (zero_add j)]
      exact congrArg (ComplexSum.of P.X j) (one_act_apply P x)) z

theorem smulHom_mul_of_mem {i j : ℤ} {a b : A} (ha : a ∈ grading i) (hb : b ∈ grading j) {k : ℤ}
    (x : P.X.X k) :
    smulHom P (a * b) (ComplexSum.of P.X k x) =
      smulHom P a (smulHom P b (ComplexSum.of P.X k x)) := by
  rw [smulHom_of_mem P (mul_mem_grading ha hb), smulHom_of_mem P hb, smulHom_of_mem P ha,
    of_f_tmul (ModObj.act P) rfl (show i + j + k = i + (j + k) by omega)]
  refine congrArg (ComplexSum.of P.X _)
    (Eq.trans ?_ (assoc_apply P (show i + j + k = i + (j + k) by omega) _ _ x))
  congr 2
  exact Subtype.ext (coe_toMonObj_mul_f_tmul A rfl ⟨a, ha⟩ ⟨b, hb⟩).symm

theorem smulHom_mul_of_mem_left {i : ℤ} {a : A} (ha : a ∈ grading i) (b : A) {k : ℤ}
    (x : P.X.X k) :
    smulHom P (a * b) (ComplexSum.of P.X k x) =
      smulHom P a (smulHom P b (ComplexSum.of P.X k x)) :=
  DFunLike.congr_fun (decompose_addHom_ext (grading (M := A))
    (f := ((smulHom P).flip (ComplexSum.of P.X k x)).comp (AddMonoidHom.mulLeft a))
    (g := (smulHom P a).comp ((smulHom P).flip (ComplexSum.of P.X k x)))
    fun _ b => smulHom_mul_of_mem P ha b.2 x) b

theorem smulHom_mul_of (a b : A) {k : ℤ} (x : P.X.X k) :
    smulHom P (a * b) (ComplexSum.of P.X k x) =
      smulHom P a (smulHom P b (ComplexSum.of P.X k x)) :=
  DFunLike.congr_fun (decompose_addHom_ext (grading (M := A))
    (f := ((smulHom P).flip (ComplexSum.of P.X k x)).comp (AddMonoidHom.mulRight b))
    (g := (smulHom P).flip (smulHom P b (ComplexSum.of P.X k x)))
    fun _ a => smulHom_mul_of_mem_left P a.2 b x) a

theorem smulHom_mul (a b : A) (z : ComplexSum P.X) :
    smulHom P (a * b) z = smulHom P a (smulHom P b z) :=
  DFunLike.congr_fun (ComplexSum.addHom_ext (f := smulHom P (a * b))
    (g := (smulHom P a).comp (smulHom P b)) fun _ x => smulHom_mul_of P a b x) z

/-- The `A`-module structure on `⨁ n, Pⁿ` induced by the action of the module object `P`. -/
instance : Module A (ComplexSum P.X) where
  smul a z := smulHom P a z
  one_smul := smulHom_one P
  mul_smul := smulHom_mul P
  smul_zero a := map_zero (smulHom P a)
  smul_add a := map_add (smulHom P a)
  add_smul a b z := by
    change smulHom P (a + b) z = smulHom P a z + smulHom P b z
    rw [map_add, AddMonoidHom.add_apply]
  zero_smul z := by
    change smulHom P 0 z = 0
    rw [map_zero, AddMonoidHom.zero_apply]

/-- The action of `a ∈ Aⁱ` on the summand `Pʲ` of `⨁ n, Pⁿ`. -/
theorem smul_of_mem {i : ℤ} {a : A} (ha : a ∈ grading i) {j : ℤ} (x : P.X.X j) :
    a • ComplexSum.of P.X j x =
      ComplexSum.of P.X (i + j) ((ModObj.act P).f (i + j) (tmul (toMonObj A).X P.X rfl ⟨a, ha⟩ x)) :=
  smulHom_of_mem P ha x

theorem smul_mem {i j : ℤ} {a : A} {z : ComplexSum P.X} (ha : a ∈ grading i)
    (hz : z ∈ grading (M := ComplexSum P.X) j) : a • z ∈ grading (M := ComplexSum P.X) (i + j) := by
  obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp hz
  rw [smul_of_mem P ha]
  exact ComplexSum.of_mem_grading _ _

set_option maxHeartbeats 800000 in
theorem d_smul_of {n : ℤ} {a : A} (ha : a ∈ grading n) {j : ℤ} (x : P.X.X j) :
    d (a • ComplexSum.of P.X j x) =
      d a • ComplexSum.of P.X j x + koszulSign n • (a • d (ComplexSum.of P.X j x)) := by
  rw [smul_of_mem P ha, ComplexSum.d_of, ← Hom.comm_apply, d_tmul, map_add, map_add,
    toMonObj_X_d_apply, smul_of_mem P (d_mem ha), ComplexSum.d_of, smul_of_mem P ha,
    Units.smul_def, Units.smul_def, map_zsmul, map_zsmul,
    of_f_tmul (ModObj.act P) _ (rfl : n + 1 + j = _), of_f_tmul (ModObj.act P) _ (rfl : n + (j + 1) = _)]

set_option maxHeartbeats 800000 in
/-- The Leibniz rule for the action of `A` on `⨁ n, Pⁿ`. -/
theorem d_smul {n : ℤ} {a : A} (ha : a ∈ grading n) (z : ComplexSum P.X) :
    d (a • z) = d a • z + koszulSign n • (a • d z) := by
  induction z using ComplexSum.induction_on with
  | zero => rw [smul_zero, d_zero, smul_zero, smul_zero, smul_zero, add_zero]
  | of j x => exact d_smul_of P ha x
  | add z z' hz hz' =>
    rw [smul_add, d_add, hz, hz', d_add, smul_add, smul_add, smul_add, add_add_add_comm]

/-- `⨁ n, Pⁿ` is a dg `A`-module; the Leibniz rule is the statement that the action of `P` is a
morphism of complexes. -/
instance : DGModule A (ComplexSum P.X) where
  smul_mem _ _ _ _ ha hz := smul_mem P ha hz
  d_smul' ha z := d_smul P ha z

theorem algebraMap_smul_of (r : R) {n : ℤ} (x : P.X.X n) :
    algebraMap R A r • ComplexSum.of P.X n x = ComplexSum.of P.X n (r • x) := by
  rw [smul_of_mem P (algebraMap_mem_grading R r), of_f_tmul (ModObj.act P) rfl (zero_add n)]
  have : (⟨algebraMap R A r, algebraMap_mem_grading R r⟩ : (toMonObj A).X.X 0) = r • oneX A :=
    Subtype.ext (mul_one (algebraMap R A r)).symm
  rw [this, tmul_smul_left, map_smul, one_act_apply]

end ModObj

namespace DGModuleCat

variable {A : DGAlgCat.{u, u} R}

/-- The dg `A`-module `⨁ n, Pⁿ` associated to a module object `P` over the monoid object
of `A`. -/
abbrev ofModObj (P : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X) : DGModuleCat.{u} A :=
  DGModuleCat.of A (ComplexSum P.X)

variable {P Q S : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X}

theorem map_smul_of_mem (g : P ⟶ Q) {i : ℤ} {a : A} (ha : a ∈ grading i) {j : ℤ}
    (x : P.X.X j) :
    ComplexSum.map g.hom (a • ComplexSum.of P.X j x) =
      a • ComplexSum.map g.hom (ComplexSum.of P.X j x) := by
  rw [ModObj.smul_of_mem P ha, ComplexSum.map_of, ComplexSum.map_of, ModObj.smul_of_mem Q ha]
  congr 1
  have := congrArg (fun φ => φ.f (i + j) (tmul (toMonObj A).X P.X rfl ⟨a, ha⟩ x)) (ModObj.act_hom g)
  simpa only [comp_f, ModuleCat.comp_apply, whiskerLeft_f_tmul] using this

set_option maxHeartbeats 800000 in
theorem map_smul (g : P ⟶ Q) (a : A) (z : ComplexSum P.X) :
    ComplexSum.map g.hom (a • z) = a • ComplexSum.map g.hom z := by
  have h : ∀ {i : ℤ} {a : A}, a ∈ grading i →
      (ComplexSum.map g.hom).toAddMonoidHom.comp (ModObj.smulHom P a) =
        (ModObj.smulHom Q a).comp (ComplexSum.map g.hom).toAddMonoidHom := fun ha =>
    ComplexSum.addHom_ext fun _ x => map_smul_of_mem g ha x
  exact DFunLike.congr_fun (DFunLike.congr_fun (decompose_addHom_ext (grading (M := A))
    (f := AddMonoidHom.mk' (fun a => (ComplexSum.map g.hom).toAddMonoidHom.comp
      (ModObj.smulHom P a)) fun a b => by beta_reduce; rw [map_add, AddMonoidHom.comp_add])
    (g := AddMonoidHom.mk' (fun a => (ModObj.smulHom Q a).comp
      (ComplexSum.map g.hom).toAddMonoidHom) fun a b => by
        beta_reduce; rw [map_add, AddMonoidHom.add_comp])
    fun _ a => h a.2) a) z

/-- The morphism of dg modules induced by a morphism of module objects. -/
def ofModMap (g : P ⟶ Q) : ofModObj P ⟶ ofModObj Q :=
  ofHom
    { toFun := ComplexSum.map g.hom
      map_add' := map_add _
      map_smul' := map_smul g
      map_mem' := ComplexSum.map_mem g.hom
      map_d' := ComplexSum.map_d g.hom }

@[simp]
theorem ofModMap_apply (g : P ⟶ Q) (z : ComplexSum P.X) :
    ofModMap g z = ComplexSum.map g.hom z :=
  rfl

variable (A) in
/-- The functor from module objects over the monoid object of `A` to dg `A`-modules,
`P ↦ ⨁ n, Pⁿ`. -/
@[simps]
def ofMod : Mod (CochainComplex (ModuleCat.{u} R) ℤ) ((DGAlgCat.toMon R).obj A).X ⥤ DGModuleCat.{u} A where
  obj := ofModObj
  map := ofModMap
  map_id _ := hom_ext_apply fun z => ComplexSum.map_id z
  map_comp f g := hom_ext_apply fun z => ComplexSum.map_comp f.hom g.hom z

/-! ### The unit of the equivalence -/

section Unit

variable (N : DGModuleCat.{u} A)

/-- The decomposition `N → ⨁ n, Nⁿ` of a dg module into its homogeneous components. -/
def unitFun : N →+ ComplexSum (toModObj N).X :=
  liftHomogeneous (grading (M := N)) fun n =>
    (ComplexSum.of (toModObj N).X n).toAddMonoidHom.comp
      { toFun := fun x => ⟨x.1, x.2⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }

theorem unitFun_of_mem {n : ℤ} {m : N} (hm : m ∈ grading n) :
    unitFun N m = ComplexSum.of (toModObj N).X n ⟨m, hm⟩ :=
  liftHomogeneous_of_mem _ _ hm

/-- The summation map `⨁ n, Nⁿ → N`. -/
def counitFun : ComplexSum (toModObj N).X →+ N :=
  DirectSum.toAddMonoid fun n =>
    { toFun := fun x : (toModObj N).X.X n => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

@[simp]
theorem counitFun_of (n : ℤ) (x : (toModObj N).X.X n) :
    counitFun N (ComplexSum.of (toModObj N).X n x) = x.1 :=
  DirectSum.toAddMonoid_of (β := fun n => (toModObj N).X.X n) _ n x

theorem counitFun_unitFun (m : N) : counitFun N (unitFun N m) = m := by
  induction m using DG.induction_on with
  | h_zero => rw [map_zero, map_zero]
  | h_homogeneous m => rw [unitFun_of_mem N m.2, counitFun_of]
  | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']

theorem unitFun_counitFun (z : ComplexSum (toModObj N).X) : unitFun N (counitFun N z) = z := by
  induction z using ComplexSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n x =>
    rw [counitFun_of, unitFun_of_mem N x.2]
    rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

theorem unitFun_smul_of_mem {i : ℤ} {a : A} (ha : a ∈ grading i) {j : ℤ} {m : N}
    (hm : m ∈ grading j) : unitFun N (a • m) = a • unitFun N m := by
  rw [unitFun_of_mem N (smul_mem_grading ha hm), unitFun_of_mem N hm,
    ModObj.smul_of_mem _ ha]
  congr 1
  exact Subtype.ext (coe_act_f_tmul N rfl ⟨a, ha⟩ ⟨m, hm⟩).symm

theorem unitFun_smul (a : A) (m : N) : unitFun N (a • m) = a • unitFun N m := by
  have h : ∀ {i : ℤ} {a : A}, a ∈ grading i →
      (unitFun N).comp (DistribSMul.toAddMonoidHom N a) =
        (DistribSMul.toAddMonoidHom _ a).comp (unitFun N) := fun ha =>
    decompose_addHom_ext (grading (M := N)) fun _ m => unitFun_smul_of_mem N ha m.2
  exact DFunLike.congr_fun (DFunLike.congr_fun (decompose_addHom_ext (grading (M := A))
    (f := AddMonoidHom.mk' (fun a => (unitFun N).comp (DistribSMul.toAddMonoidHom N a))
      fun a b => by
        beta_reduce
        ext m
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply, add_smul,
          map_add, AddMonoidHom.add_apply])
    (g := AddMonoidHom.mk' (fun a => (DistribSMul.toAddMonoidHom _ a).comp (unitFun N))
      fun a b => by
        beta_reduce
        ext m
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply, add_smul,
          AddMonoidHom.add_apply])
    fun _ a => h a.2) a) m

theorem unitFun_d (m : N) : unitFun N (d m) = d (unitFun N m) := by
  induction m using DG.induction_on with
  | h_zero => rw [d_zero, map_zero, map_zero]
  | @h_homogeneous n m =>
    rw [unitFun_of_mem N (d_mem m.2), unitFun_of_mem N m.2, ComplexSum.d_of]
    congr 1
    exact (congrArg (fun φ => ModuleCat.Hom.hom φ
      (⟨m.1, m.2⟩ : DGModule.gradingSubmodule R A N n)) (toComplex_d R N n)).symm
  | h_add m m' hm hm' => rw [d_add, map_add, hm, hm', map_add, d_add]

/-- The decomposition of a dg module into its homogeneous components, as a morphism of dg
modules `N ⟶ ⨁ n, Nⁿ`. -/
def unitHom : N ⟶ ofModObj (toModObj N) :=
  ⟨{ toFun := unitFun N
     map_add' := map_add _
     map_smul' := unitFun_smul N
     map_mem' := fun hm => by
       rw [unitFun_of_mem N hm]
       exact ComplexSum.of_mem_grading _ _
     map_d' := unitFun_d N }⟩

/-- The summation map `⨁ n, Nⁿ ⟶ N`, a morphism of dg modules. -/
def counitHom : ofModObj (toModObj N) ⟶ N :=
  ⟨{ toFun := counitFun N
     map_add' := map_add _
     map_smul' := fun a z => by
       rw [← unitFun_counitFun N z, RingHom.id_apply, ← unitFun_smul, counitFun_unitFun,
         counitFun_unitFun]
     map_mem' := fun {n} {z} hz => by
       obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp hz
       rw [counitFun_of]
       exact x.2
     map_d' := fun z => by
       rw [← unitFun_counitFun N z, ← unitFun_d, counitFun_unitFun, counitFun_unitFun] }⟩

/-- A dg module is isomorphic to the dg module of its module object, `⨁ n, Nⁿ`. -/
@[simps]
def unitIso : N ≅ ofModObj (toModObj N) where
  hom := unitHom N
  inv := counitHom N
  hom_inv_id := hom_ext_apply fun m => counitFun_unitFun N m
  inv_hom_id := hom_ext_apply fun z => unitFun_counitFun N z

end Unit

variable (A) in
/-- The unit of the equivalence between dg modules and module objects: every dg module is
isomorphic to `⨁ n, Nⁿ`, naturally in `N`. -/
def unitNatIso : 𝟭 (DGModuleCat.{u} A) ≅ toMod A ⋙ ofMod A :=
  NatIso.ofComponents unitIso fun {N N'} f => hom_ext_apply fun m => by
    change unitFun N' (f m) = ComplexSum.map (toModMap f).hom (unitFun N m)
    induction m using DG.induction_on with
    | h_zero => rw [map_zero, map_zero, map_zero, map_zero]
    | @h_homogeneous n m =>
      rw [unitFun_of_mem N' (f.hom.map_mem m.2), unitFun_of_mem N m.2]
      exact (ComplexSum.map_of (toModMap f).hom n _).symm
    | h_add m m' hm hm' => rw [map_add, map_add, hm, hm', map_add, map_add]

/-! ### The counit of the equivalence -/

section Counit

variable (P : Mod (CochainComplex (ModuleCat.{u} R) ℤ) (toMonObj A).X)

/-- The underlying complex of `⨁ n, Pⁿ` is `P`. -/
def counitIsoX : (toModObj (ofModObj P)).X ≅ P.X :=
  ComplexSum.toComplexIso (K := P.X) (A := A) fun r _ x => ModObj.algebraMap_smul_of P r x

theorem counitIsoX_hom_f_apply (n : ℤ) (z : (toModObj (ofModObj P)).X.X n) :
    (counitIsoX P).hom.f n z = ComplexSum.component P.X n z.1 :=
  rfl

theorem coe_counitIsoX_inv_f_apply (n : ℤ) (x : P.X.X n) :
    ((counitIsoX P).inv.f n x).1 = ComplexSum.of P.X n x :=
  rfl

set_option maxHeartbeats 800000 in
/-- The module object of the dg module `⨁ n, Pⁿ` is isomorphic to `P`. -/
def counitIso : toModObj (ofModObj P) ≅ P where
  hom :=
    { hom := (counitIsoX P).hom
      isModHom.smul_hom := by
        change ModObj.act (toModObj (ofModObj P)) ≫ (counitIsoX P).hom =
          (toMonObj A).X ◁ (counitIsoX P).hom ≫ ModObj.act P
        ext n : 1
        refine ComplexTensor.hom_ext fun p q h a z => ?_
        obtain ⟨z, hz⟩ := z
        obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp hz
        simp only [comp_f, ModuleCat.comp_apply, whiskerLeft_f_tmul, counitIsoX_hom_f_apply,
          toModObj_act]
        erw [coe_act_f_tmul]
        rw [ModObj.smul_of_mem P a.2, of_f_tmul (ModObj.act P) rfl h, ComplexSum.component_of_same,
          ComplexSum.component_of_same]
        rfl }
  inv :=
    { hom := (counitIsoX P).inv
      isModHom.smul_hom := by
        change ModObj.act P ≫ (counitIsoX P).inv =
          (toMonObj A).X ◁ (counitIsoX P).inv ≫ ModObj.act (toModObj (ofModObj P))
        ext n : 1
        refine ComplexTensor.hom_ext fun p q h a x => Subtype.ext ?_
        simp only [comp_f, ModuleCat.comp_apply, whiskerLeft_f_tmul, coe_counitIsoX_inv_f_apply,
          toModObj_act]
        erw [coe_act_f_tmul]
        rw [coe_counitIsoX_inv_f_apply, ModObj.smul_of_mem P a.2, of_f_tmul (ModObj.act P) rfl h]
        rfl }
  hom_inv_id := Mod.hom_ext _ _ (counitIsoX P).hom_inv_id
  inv_hom_id := Mod.hom_ext _ _ (counitIsoX P).inv_hom_id

theorem counitIso_hom_hom_f_apply (n : ℤ) (z : (toModObj (ofModObj P)).X.X n) :
    (counitIso P).hom.hom.f n z = ComplexSum.component P.X n z.1 :=
  rfl

end Counit

theorem counitIso_naturality (g : P ⟶ Q) :
    toModMap (ofModMap g) ≫ (counitIso Q).hom = (counitIso P).hom ≫ g := by
  refine Mod.hom_ext _ _ (HomologicalComplex.hom_ext _ _ fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
  obtain ⟨z, hz⟩ := z
  obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp hz
  simp only [Mod.comp_hom', comp_f, ModuleCat.comp_apply, toModMap_hom,
    counitIso_hom_hom_f_apply, ComplexSum.component_of_same]
  exact (congrArg (ComplexSum.component Q.X n)
    (coe_toComplexMap_f_apply (ofModMap g) n ⟨_, hz⟩)).trans
    (by rw [ofModMap_apply, ComplexSum.map_of, ComplexSum.component_of_same])

variable (A) in
/-- The counit of the equivalence between dg modules and module objects: every module object
`P` is isomorphic to the module object of `⨁ n, Pⁿ`, naturally in `P`. -/
def counitNatIso : ofMod A ⋙ toMod A ≅ 𝟭 (Mod (CochainComplex (ModuleCat.{u} R) ℤ) ((DGAlgCat.toMon R).obj A).X) :=
  NatIso.ofComponents counitIso fun g => counitIso_naturality g

variable (A) in
/-- **Dg modules are module objects in cochain complexes.** For a dg `R`-algebra `A`, the
category of dg `A`-modules is equivalent to the category of module objects over the monoid
object `(DGAlgCat.toMon R).obj A` in the monoidal category of cochain complexes of `R`-modules,
via `N ↦ (N, act)` (`DG.DGModuleCat.toMod`) and `P ↦ ⨁ n, Pⁿ` (`DG.DGModuleCat.ofMod`). -/
def modEquivalence : DGModuleCat.{u} A ≌ Mod (CochainComplex (ModuleCat.{u} R) ℤ) ((DGAlgCat.toMon R).obj A).X :=
  CategoryTheory.Equivalence.mk (toMod A) (ofMod A) (unitNatIso A) (counitNatIso A)

end DGModuleCat

end DG

end
