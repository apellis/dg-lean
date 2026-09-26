import DG.Module.End

/-!
# The Hom complex over a dg `R`-algebra is a complex of `R`-modules

Let `A` be a dg `R`-algebra and `M`, `N` dg `A`-modules whose `R`-module structures are
compatible with the `A`-actions (`IsScalarTower R A M`, `IsScalarTower R A N`). This file makes
the Hom complex `HOM_A(M, N)` a complex of `R`-modules and `END_A(M)` a dg `R`-algebra.

* `DG.Cochain.instModuleGround`: `Cochain A M N n` is an `R`-module, with `(r • f) x = r • f x`.
  Since `algebraMap R A r` is central and of degree `0`, `r • f` is again signed `A`-linear.
  For `R = ℤ` the action agrees definitionally with the `ℤ`-action of the additive group.
* `DG.Cochain.map_smul_ground`, `DG.Cochain.comp_smul`, `DG.Cochain.smul_comp`: cochains are
  `R`-linear, and composition is `R`-bilinear.
* `DG.δ_smul_ground`: the differential of the Hom complex is `R`-linear, and so is the
  differential of `HOM_A(M, N) = ⨁ n, Cochain A M N n` (`DG.DGModule.HOM.d_smul_ground`).
* `DG.DGModule.END.instAlgebra`, `DG.DGModule.END.instDGAlgebra`: `END_A(M)` is a dg
  `R`-algebra, with `algebraMap R (END A M) r` the identity of `M` multiplied by `r`, in
  degree `0` (`DG.DGModule.END.algebraMap_apply`).
-/

open DirectSum

namespace DG

section Cochain

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A] {M N P : Type*}
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] [Module R N]
  [IsScalarTower R A N]

namespace Cochain

variable {n : ℤ}

/-- The pointwise action of `R` on cochains, `(r • f) x = r • f x`. -/
instance instSMulGround : SMul R (Cochain A M N n) :=
  ⟨fun r f =>
    { toFun := fun x => r • f x
      map_zero' := by simp
      map_add' := fun x y => by simp [smul_add]
      map_mem' := fun _ _ hx => DGModule.ground_smul_mem A r (f.map_mem hx)
      map_smul' := fun {i a} ha x => by
        show r • f (a • x) = koszulSign (n * i) • (a • (r • f x))
        rw [f.map_smul ha, Units.smul_def, Units.smul_def, smul_comm r, smul_comm r a] }⟩

@[simp]
theorem coe_smul_ground (r : R) (f : Cochain A M N n) : ⇑(r • f) = r • ⇑f := rfl

theorem smul_ground_apply (r : R) (f : Cochain A M N n) (x : M) : (r • f) x = r • f x := rfl

/-- Cochains of degree `n` form an `R`-module. -/
instance instModuleGround : Module R (Cochain A M N n) :=
  Function.Injective.module R (⟨⟨DFunLike.coe, rfl⟩, fun _ _ => rfl⟩ : Cochain A M N n →+ M → N)
    DFunLike.coe_injective fun _ _ => rfl

variable [Module R M] [IsScalarTower R A M]

omit [DGModule A N] in
/-- Cochains are `R`-linear. -/
theorem map_smul_ground (f : Cochain A M N n) (r : R) (x : M) : f (r • x) = r • f x := by
  rw [← algebraMap_smul A r x, f.map_smul (algebraMap_mem_grading R r), mul_zero, koszulSign_zero,
    one_smul, algebraMap_smul]

variable [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P] [Module R P]
  [IsScalarTower R A P]

omit [DGModule A N] [Module R N] [IsScalarTower R A N] [Module R M] [IsScalarTower R A M] in
@[simp]
theorem smul_comp {n₁ n₂ n₁₂ : ℤ} (r : R) (z₁ : Cochain A M N n₁) (z₂ : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) : (r • z₂).comp z₁ h = r • z₂.comp z₁ h := rfl

omit [Module R M] [IsScalarTower R A M] in
@[simp]
theorem comp_smul {n₁ n₂ n₁₂ : ℤ} (r : R) (z₁ : Cochain A M N n₁) (z₂ : Cochain A N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (r • z₁) h = r • z₂.comp z₁ h :=
  ext fun x => map_smul_ground z₂ r (z₁ x)

end Cochain

variable [DGModule A M]

/-- The differential of the Hom complex is `R`-linear. -/
@[simp]
theorem δ_smul_ground (n m : ℤ) (r : R) (z : Cochain A M N n) : δ n m (r • z) = r • δ n m z := by
  by_cases hnm : n + 1 = m
  · ext x
    rw [Cochain.smul_ground_apply, δ_apply _ _ hnm, δ_apply _ _ hnm, Cochain.smul_ground_apply,
      Cochain.smul_ground_apply, d_ground_smul A, smul_sub, Units.smul_def, Units.smul_def,
      smul_comm r]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, smul_zero]

namespace DGModule.HOM

omit [DGModule A M] in
theorem smul_of (r : R) (n : ℤ) (f : Cochain A M N n) :
    r • (DirectSum.of (fun n => Cochain A M N n) n f : HOM A M N) =
      DirectSum.of (fun n => Cochain A M N n) n (r • f) := by
  rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, map_smul]

/-- The differential of `HOM_A(M, N)` is `R`-linear. -/
theorem d_smul_ground (r : R) (F : HOM A M N) : d (r • F) = r • d F := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of n f => rw [smul_of, d_of, d_of, δ_smul_ground, smul_of]
  | add F G hF hG => rw [smul_add, d_add, hF, hG, d_add, smul_add]

end DGModule.HOM

end Cochain

namespace DGModule.END

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A] (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [Module R M] [IsScalarTower R A M]

variable {R A M} in
theorem smul_of_mul_of (r : R) {m n : ℤ} (f : Cochain A M M m) (g : Cochain A M M n) :
    (r • DirectSum.of (fun n => Cochain A M M n) m f) * DirectSum.of _ n g =
      r • (DirectSum.of (fun n => Cochain A M M n) m f * DirectSum.of _ n g : END A M) := by
  rw [HOM.smul_of, of_mul_of, of_mul_of, HOM.smul_of]
  congr 1
  ext x
  simp only [Cochain.units_smul_apply, Cochain.comp_apply, Cochain.smul_ground_apply,
    Cochain.map_smul_ground, Units.smul_def, smul_comm r]

variable {R A M} in
theorem of_mul_smul_of (r : R) {m n : ℤ} (f : Cochain A M M m) (g : Cochain A M M n) :
    DirectSum.of (fun n => Cochain A M M n) m f * (r • DirectSum.of _ n g) =
      r • (DirectSum.of (fun n => Cochain A M M n) m f * DirectSum.of _ n g : END A M) := by
  rw [HOM.smul_of, of_mul_of, of_mul_of, HOM.smul_of]
  congr 1
  ext x
  simp only [Cochain.units_smul_apply, Cochain.comp_apply, Cochain.smul_ground_apply,
    Units.smul_def, smul_comm r]

variable {R A M} in
theorem smul_mul_assoc_ground (r : R) (F G : END A M) : (r • F) * G = r • (F * G) := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | add F F' hF hF' => rw [smul_add, add_mul, hF, hF', add_mul, smul_add]
  | of m f =>
    induction G using DirectSum.induction_on with
    | zero => simp
    | add G G' hG hG' => rw [mul_add, hG, hG', mul_add, smul_add]
    | of n g => exact smul_of_mul_of r f g

variable {R A M} in
theorem mul_smul_comm_ground (r : R) (F G : END A M) : F * (r • G) = r • (F * G) := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | add F F' hF hF' => rw [add_mul, hF, hF', add_mul, smul_add]
  | of m f =>
    induction G using DirectSum.induction_on with
    | zero => simp
    | add G G' hG hG' => rw [smul_add, mul_add, hG, hG', mul_add, smul_add]
    | of n g => exact of_mul_smul_of r f g

variable {R A M} in
theorem of_zero_smul_id (r : R) :
    DirectSum.of (fun n => Cochain A M M n) 0 (r • Cochain.id A M) = r • (1 : END A M) := by
  rw [one_def, HOM.smul_of]

/-- The structure map `R → END_A(M)`, `r ↦ r • id` in degree `0`. -/
noncomputable def algebraMapAux : R →+* END A M where
  toFun r := DirectSum.of (fun n => Cochain A M M n) 0 (r • Cochain.id A M)
  map_one' := by rw [one_smul, one_def]
  map_mul' r s := by
    change DirectSum.of _ 0 ((r * s) • Cochain.id A M) =
      DirectSum.of _ 0 (r • Cochain.id A M) * DirectSum.of _ 0 (s • Cochain.id A M)
    rw [of_zero_smul_id, of_zero_smul_id, of_zero_smul_id, smul_mul_assoc_ground, one_mul,
      mul_smul]
  map_zero' := by rw [zero_smul, map_zero]
  map_add' r s := by rw [add_smul, map_add]

/-- `END_A(M)` is an `R`-algebra, with `algebraMap R (END A M) r = r • id` in degree `0`. For
`R = ℤ` it agrees definitionally with the `ℤ`-algebra structure of the ring `END A M`. -/
noncomputable instance instAlgebra : Algebra R (END A M) where
  algebraMap := algebraMapAux R A M
  commutes' r F := by
    change DirectSum.of _ 0 (r • Cochain.id A M) * F = F * DirectSum.of _ 0 (r • Cochain.id A M)
    rw [of_zero_smul_id, smul_mul_assoc_ground, mul_smul_comm_ground, one_mul, mul_one]
  smul_def' r F := by
    change r • F = DirectSum.of _ 0 (r • Cochain.id A M) * F
    rw [of_zero_smul_id, smul_mul_assoc_ground, one_mul]

variable {R A M} in
theorem algebraMap_apply (r : R) :
    algebraMap R (END A M) r = DirectSum.of (fun n => Cochain A M M n) 0 (r • Cochain.id A M) :=
  rfl

/-- `END_A(M)` is a dg `R`-algebra. -/
noncomputable instance instDGAlgebra : DGAlgebra R (END A M) where
  algebraMap_mem' r := by
    rw [algebraMap_apply]
    exact of_mem_summand _ _
  d_algebraMap' r := by
    rw [Algebra.algebraMap_eq_smul_one, HOM.d_smul_ground, d_one, smul_zero]

end DGModule.END

end DG
