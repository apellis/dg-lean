import DG.Algebra.Opposite
import DG.Graded.Basic
import DG.Module.Right

/-!
# Right dg modules as left dg modules over the opposite dg algebra

Let `A` be a dg `R`-algebra and `Aᵒᵖ = GradedOpposite (DGAlgebra.gradingSubmodule R A)` its
opposite dg algebra (`DG.Algebra.Opposite`). Following `docs/CONVENTIONS.md`, a right dg
`A`-module is the same as a left dg `Aᵒᵖ`-module. Right modules are encoded as in Mathlib, by
`Module Aᵐᵒᵖ M` (`DG.DGRightModule`); since the product of `Aᵒᵖ` is twisted by the Koszul sign
while that of `Aᵐᵒᵖ` is not, the two actions differ by the Koszul sign of the exchange of `a` and
`m`:

  `op a • m = (-1)^{|a||m|} • (m • a)` for homogeneous `a` and `m`.

## Main definitions and results

* `DG.koszulTwist f`: for a biadditive map `f : A →+ M →+ N` between graded abelian groups, the
  biadditive map `a ⊗ m ↦ (-1)^{|a||m|} • f a m` (on homogeneous elements); it is an involution
  (`DG.koszulTwist_koszulTwist`).
* `DG.DGRightModule.opModule`, `DG.DGRightModule.dgModule_opModule`: a right dg `A`-module is a
  left dg `Aᵒᵖ`-module.
* `DG.DGModule.mulOppositeModule`, `DG.DGModule.dgRightModule_mulOppositeModule`: a left dg
  `Aᵒᵖ`-module is a right dg `A`-module.
* `DG.rightModuleEquivOpModule`: the two constructions are mutually inverse, giving a bijection
  between right dg `A`-module structures and left dg `Aᵒᵖ`-module structures on a dg abelian
  group `M`.

## Implementation notes

The module structures are constructed as definitions, not instances, since each direction would
otherwise produce the other one and create instance loops; they are obtained from ring
homomorphisms into `AddMonoid.End M` via `Module.compHom`.
-/

noncomputable section

open DirectSum

namespace DG

private theorem ks_eq {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

/-! ### The Koszul twist of a biadditive map -/

private theorem units_smul_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N] (u : ℤˣ)
    (f : M →+ N) (m : M) : (u • f) m = u • f m := rfl

section Twist

variable {A M N : Type*} [AddCommGroup A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [AddCommGroup N]

/-- The Koszul twist of a biadditive map `f : A →+ M →+ N` between graded abelian groups: the
biadditive map given on homogeneous `a ∈ Aⁱ`, `m ∈ Mʲ` by `(-1)^{ij} • f a m`. -/
def koszulTwist (f : A →+ M →+ N) : A →+ M →+ N :=
  liftHomogeneous (grading (M := A)) fun i =>
    { toFun := fun a => liftHomogeneous (grading (M := M)) fun j =>
        { toFun := fun m => koszulSign (i * j) • f a m
          map_zero' := by rw [ZeroMemClass.coe_zero, map_zero, smul_zero]
          map_add' := fun m m' => by rw [AddSubgroup.coe_add, map_add, smul_add] }
      map_zero' := decompose_addHom_ext (grading (M := M)) fun j m => by
        simp
      map_add' := fun a a' => decompose_addHom_ext (grading (M := M)) fun j m => by
        simp [smul_add] }

theorem koszulTwist_apply_of_mem (f : A →+ M →+ N) {i j : ℤ} {a : A} {m : M}
    (ha : a ∈ grading i) (hm : m ∈ grading j) :
    koszulTwist f a m = koszulSign (i * j) • f a m := by
  rw [koszulTwist, liftHomogeneous_of_mem _ _ ha]
  change liftHomogeneous (grading (M := M)) _ m = _
  rw [liftHomogeneous_of_mem _ _ hm]
  rfl

@[simp]
theorem koszulTwist_koszulTwist (f : A →+ M →+ N) : koszulTwist (koszulTwist f) = f :=
  decompose_addHom_ext (grading (M := A)) fun _ a =>
    decompose_addHom_ext (grading (M := M)) fun _ m => by
      rw [koszulTwist_apply_of_mem _ a.2 m.2, koszulTwist_apply_of_mem _ a.2 m.2, smul_smul,
        Int.units_mul_self, one_smul]

end Twist

variable (R : Type*) {A M : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [DGRing A] [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M]

local notation "𝒜" => DGAlgebra.gradingSubmodule R A
local notation "Aᵒᵖ" => GradedOpposite (DGAlgebra.gradingSubmodule R A)

/-! ### From right modules to left modules over the opposite -/

namespace DGRightModule

variable [Module Aᵐᵒᵖ M]

variable (A M) in
/-- The right action as a biadditive map, `a ↦ m ↦ m • a`. -/
def actHom : A →+ M →+ M :=
  (smulAddHom Aᵐᵒᵖ M).comp (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddMonoidHom

omit [DGAddCommGroup A] [DGRing A] [DGAddCommGroup M] in
@[simp]
theorem actHom_apply (a : A) (m : M) : actHom A M a m = MulOpposite.op a • m := rfl

variable [DGRightModule A M]

theorem koszulTwist_actHom_mul_of_mem {i j : ℤ} {x y : Aᵒᵖ} (hx : x ∈ grading i)
    (hy : y ∈ grading j) (m : M) :
    koszulTwist (actHom A M) (GradedOpposite.unop 𝒜 (x * y)) m =
      koszulTwist (actHom A M) (GradedOpposite.unop 𝒜 x)
        (koszulTwist (actHom A M) (GradedOpposite.unop 𝒜 y) m) := by
  induction m using induction_on with
  | h_zero => simp only [map_zero]
  | h_homogeneous m =>
    obtain ⟨m, hm⟩ := m
    rename_i k
    have ha := (GradedOpposite.mem_dgGrading_iff (R := R)).mp hx
    have hb := (GradedOpposite.mem_dgGrading_iff (R := R)).mp hy
    rw [GradedOpposite.unop_mul 𝒜 hx hy, map_koszulSign_smul, units_smul_apply,
      koszulTwist_apply_of_mem _ (mul_mem_grading hb ha) hm, koszulTwist_apply_of_mem _ hb hm,
      map_koszulSign_smul,
      koszulTwist_apply_of_mem _ ha
        (show actHom A M _ m ∈ grading (k + j) from op_smul_mem_grading hb hm)]
    rw [actHom_apply, actHom_apply, actHom_apply, MulOpposite.op_mul]
    simp only [smul_smul, ← koszulSign_add]
    congr 2
    ring
  | h_add m m' hm hm' => simp only [map_add, hm, hm']

set_option backward.isDefEq.respectTransparency false in
/-- The left action of the opposite dg algebra on a right dg module, as a ring homomorphism
`Aᵒᵖ →+* AddMonoid.End M`: `op a ↦ (m ↦ (-1)^{|a||m|} • m • a)`. -/
def opRingHom : Aᵒᵖ →+* AddMonoid.End M where
  toFun x := koszulTwist (actHom A M) (GradedOpposite.unop 𝒜 x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]
  map_one' := DFunLike.ext _ _ fun m => by
    induction m using induction_on with
    | h_zero => rw [map_zero, map_zero]
    | h_homogeneous m =>
      rw [GradedOpposite.unop_one, koszulTwist_apply_of_mem _ (one_mem_grading (A := A)) m.2,
        zero_mul, koszulSign_zero, one_smul, actHom_apply, MulOpposite.op_one, one_smul,
        AddMonoid.End.coe_one, id]
    | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']
  map_mul' x y := by
    induction x using induction_on with
    | h_zero => simp only [zero_mul, map_zero]
    | h_homogeneous x =>
      induction y using induction_on with
      | h_zero => simp only [mul_zero, map_zero]
      | h_homogeneous y => exact DFunLike.ext _ _ (koszulTwist_actHom_mul_of_mem R x.2 y.2)
      | h_add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | h_add x x' hx hx' => simp only [add_mul, map_add, hx, hx']

/-- The left `Aᵒᵖ`-module structure on a right dg `A`-module `M`, given by the Koszul rule
`op a • m = (-1)^{|a||m|} • (m • a)`. -/
@[instance_reducible]
def opModule : Module Aᵒᵖ M := Module.compHom M (opRingHom R (A := A) (M := M))

theorem opModule_smul (x : Aᵒᵖ) (m : M) :
    (letI := opModule R (A := A) (M := M); x • m) =
      koszulTwist (actHom A M) (GradedOpposite.unop 𝒜 x) m :=
  rfl

theorem opModule_op_smul_of_mem {i j : ℤ} {a : A} {m : M} (ha : a ∈ grading i)
    (hm : m ∈ grading j) :
    (letI := opModule R (A := A) (M := M); GradedOpposite.op 𝒜 a • m) =
      koszulSign (i * j) • (MulOpposite.op a • m) :=
  koszulTwist_apply_of_mem (actHom A M) ha hm

/-- A right dg `A`-module is a left dg `Aᵒᵖ`-module for the action `DGRightModule.opModule`. -/
theorem dgModule_opModule :
    letI := opModule R (A := A) (M := M)
    DGModule Aᵒᵖ M :=
  letI := opModule R (A := A) (M := M)
  { smul_mem := fun i j x m hx hm => by
      rw [opModule_smul, koszulTwist_apply_of_mem _ ((GradedOpposite.mem_dgGrading_iff).mp hx) hm,
        Units.smul_def]
      refine zsmul_mem ?_ _
      rw [vadd_eq_add, add_comm]
      exact op_smul_mem_grading ((GradedOpposite.mem_dgGrading_iff).mp hx) hm
    d_smul' := fun {i x} hx m => by
      induction m using induction_on with
      | h_zero => simp only [smul_zero, d_zero, add_zero]
      | h_homogeneous m =>
        obtain ⟨m, hm⟩ := m
        rename_i k
        have ha := (GradedOpposite.mem_dgGrading_iff (R := R)).mp hx
        rw [opModule_smul, opModule_smul, opModule_smul, koszulTwist_apply_of_mem _ ha hm,
          ← GradedOpposite.d_unop, koszulTwist_apply_of_mem _ (d_mem ha) hm,
          koszulTwist_apply_of_mem _ ha (d_mem hm), d_units_smul, actHom_apply, actHom_apply,
          actHom_apply, d_op_smul hm]
        simp only [smul_add, smul_smul, ← koszulSign_add]
        rw [ks_eq (m := i * k + k) (n := (i + 1) * k) ⟨0, by ring⟩,
          ks_eq (m := i + i * (k + 1)) (n := i * k) ⟨i, by ring⟩, add_comm]
      | h_add m m' hm hm' => simp only [smul_add, d_add, hm, hm']; abel }

end DGRightModule

/-! ### From left modules over the opposite to right modules -/

namespace DGModule

variable [Module (GradedOpposite (DGAlgebra.gradingSubmodule R A)) M]

variable (A M) in
/-- The action of `Aᵒᵖ` as a biadditive map on `A`, `a ↦ m ↦ op a • m`. -/
def opActHom : A →+ M →+ M :=
  (smulAddHom (GradedOpposite (DGAlgebra.gradingSubmodule R A)) M).comp
    (GradedOpposite.op (DGAlgebra.gradingSubmodule R A)).toLinearMap.toAddMonoidHom

omit [DGAddCommGroup M] in
@[simp]
theorem opActHom_apply (a : A) (m : M) :
    opActHom R A M a m = GradedOpposite.op 𝒜 a • m := rfl

variable [DGModule (GradedOpposite (DGAlgebra.gradingSubmodule R A)) M]

theorem koszulTwist_opActHom_mul (a b : A) (m : M) :
    koszulTwist (opActHom R A M) (b * a) m =
      koszulTwist (opActHom R A M) a (koszulTwist (opActHom R A M) b m) := by
  induction a using induction_on generalizing m with
  | h_zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
  | h_homogeneous a =>
    obtain ⟨a, ha⟩ := a
    rename_i i
    induction b using induction_on generalizing m with
    | h_zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
    | h_homogeneous b =>
      obtain ⟨b, hb⟩ := b
      rename_i j
      induction m using induction_on with
      | h_zero => simp only [map_zero]
      | h_homogeneous m =>
        obtain ⟨m, hm⟩ := m
        rename_i k
        have hopb := (GradedOpposite.op_mem_dgGrading_iff (R := R)).mpr hb
        have hopa := (GradedOpposite.op_mem_dgGrading_iff (R := R)).mpr ha
        rw [koszulTwist_apply_of_mem _ (mul_mem_grading hb ha) hm, koszulTwist_apply_of_mem _ hb hm,
          map_koszulSign_smul,
          koszulTwist_apply_of_mem _ ha
            (show opActHom R A M b m ∈ grading (j + k) from smul_mem_grading hopb hm),
          opActHom_apply, opActHom_apply, opActHom_apply,
          ← mul_smul (GradedOpposite.op 𝒜 a) (GradedOpposite.op 𝒜 b) m,
          GradedOpposite.op_mul_op 𝒜 ha hb, Units.smul_def, Units.smul_def, smul_assoc,
          ← Units.smul_def, ← Units.smul_def]
        simp only [smul_smul, ← koszulSign_add]
        exact congrArg (· • _) (ks_eq ⟨-(i * j), by ring⟩)
      | h_add m m' hm hm' => simp only [map_add, hm, hm']
    | h_add b b' hb hb' => simp only [add_mul, map_add, AddMonoidHom.add_apply, hb, hb']
  | h_add a a' ha ha' => simp only [mul_add, map_add, AddMonoidHom.add_apply, ha, ha']

set_option backward.isDefEq.respectTransparency false in
/-- The right action of `A` on a left dg `Aᵒᵖ`-module, as a ring homomorphism
`Aᵐᵒᵖ →+* AddMonoid.End M`: `op a ↦ (m ↦ (-1)^{|a||m|} • op a • m)`. -/
def mulOppositeRingHom : Aᵐᵒᵖ →+* AddMonoid.End M where
  toFun x := koszulTwist (opActHom R A M) (MulOpposite.unop x)
  map_zero' := by rw [MulOpposite.unop_zero, map_zero]
  map_add' x y := by rw [MulOpposite.unop_add, map_add]
  map_one' := DFunLike.ext _ _ fun m => by
    induction m using induction_on with
    | h_zero => rw [map_zero, map_zero]
    | h_homogeneous m =>
      rw [MulOpposite.unop_one, koszulTwist_apply_of_mem _ (one_mem_grading (A := A)) m.2,
        zero_mul, koszulSign_zero, one_smul, opActHom_apply, GradedOpposite.op_one, one_smul,
        AddMonoid.End.coe_one, id]
    | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']
  map_mul' x y :=
    DFunLike.ext _ _ (koszulTwist_opActHom_mul R (MulOpposite.unop x) (MulOpposite.unop y))

/-- The right `A`-module structure on a left dg `Aᵒᵖ`-module `M`, given by the Koszul rule
`m • a = (-1)^{|a||m|} • (op a • m)`. -/
@[instance_reducible]
def mulOppositeModule : Module Aᵐᵒᵖ M := Module.compHom M (mulOppositeRingHom R (A := A) (M := M))

theorem mulOppositeModule_smul (x : Aᵐᵒᵖ) (m : M) :
    (letI := mulOppositeModule R (A := A) (M := M); x • m) =
      koszulTwist (opActHom R A M) (MulOpposite.unop x) m :=
  rfl

theorem mulOppositeModule_op_smul_of_mem {i j : ℤ} {a : A} {m : M} (ha : a ∈ grading i)
    (hm : m ∈ grading j) :
    (letI := mulOppositeModule R (A := A) (M := M); MulOpposite.op a • m) =
      koszulSign (i * j) • (GradedOpposite.op 𝒜 a • m) :=
  koszulTwist_apply_of_mem (opActHom R A M) ha hm

/-- A left dg `Aᵒᵖ`-module is a right dg `A`-module for the action
`DGModule.mulOppositeModule`. -/
theorem dgRightModule_mulOppositeModule :
    letI := mulOppositeModule R (A := A) (M := M)
    DGRightModule A M :=
  letI := mulOppositeModule R (A := A) (M := M)
  { op_smul_mem' := fun {i j a m} ha hm => by
      rw [mulOppositeModule_op_smul_of_mem R ha hm, Units.smul_def, add_comm]
      exact zsmul_mem (smul_mem_grading ((GradedOpposite.op_mem_dgGrading_iff).mpr ha) hm) _
    d_op_smul' := fun {j m} hm a => by
      induction a using induction_on with
      | h_zero => simp only [MulOpposite.op_zero, zero_smul, d_zero, smul_zero, add_zero]
      | h_homogeneous a =>
        obtain ⟨a, ha⟩ := a
        rename_i i
        have hopa := (GradedOpposite.op_mem_dgGrading_iff (R := R)).mpr ha
        rw [mulOppositeModule_op_smul_of_mem R ha hm, mulOppositeModule_op_smul_of_mem R ha
          (d_mem hm), mulOppositeModule_op_smul_of_mem R (d_mem ha) hm, d_units_smul,
          d_smul hopa, GradedOpposite.d_op]
        simp only [smul_add, smul_smul, ← koszulSign_add]
        rw [ks_eq (m := i * j + i) (n := i * (j + 1)) ⟨0, by ring⟩,
          ks_eq (m := j + (i + 1) * j) (n := i * j) ⟨j, by ring⟩, add_comm]
      | h_add a a' ha ha' =>
        simp only [MulOpposite.op_add, add_smul, d_add, ha, ha', smul_add]; abel }

end DGModule

/-! ### The correspondence -/

variable (A M)

/-- Right dg `A`-module structures on `M` correspond bijectively to left dg `Aᵒᵖ`-module
structures on `M` (with the same grading and differential), via the Koszul rule
`op a • m = (-1)^{|a||m|} • (m • a)`: the constructions `DGRightModule.opModule` and
`DGModule.mulOppositeModule` are mutually inverse. -/
def rightModuleEquivOpModule :
    {P : Module Aᵐᵒᵖ M // letI := P; DGRightModule A M} ≃
      {Q : Module (GradedOpposite (DGAlgebra.gradingSubmodule R A)) M //
        letI := Q; DGModule (GradedOpposite (DGAlgebra.gradingSubmodule R A)) M} where
  toFun P :=
    letI := P.1
    haveI := P.2
    ⟨DGRightModule.opModule R, DGRightModule.dgModule_opModule R⟩
  invFun Q :=
    letI := Q.1
    haveI := Q.2
    ⟨DGModule.mulOppositeModule R, DGModule.dgRightModule_mulOppositeModule R⟩
  left_inv P := by
    obtain ⟨P, hP⟩ := P
    refine Subtype.ext (Module.ext' _ _ fun x m => ?_)
    let := P
    change koszulTwist (koszulTwist (DGRightModule.actHom A M)) (MulOpposite.unop x) m = x • m
    rw [koszulTwist_koszulTwist]
    rfl
  right_inv Q := by
    obtain ⟨Q, hQ⟩ := Q
    refine Subtype.ext (Module.ext' _ _ fun x m => ?_)
    let := Q
    change koszulTwist (koszulTwist (DGModule.opActHom R A M))
      (GradedOpposite.unop (DGAlgebra.gradingSubmodule R A) x) m = x • m
    rw [koszulTwist_koszulTwist]
    rfl

end DG
