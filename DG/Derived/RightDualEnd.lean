import DG.Derived.RightDual
import DG.Module.End
import DG.Module.Opposite
import DG.Algebra.Opposite

/-!
# Transposition: the endomorphisms of a right dg module and of its dual

Let `A` be a dg `R`-algebra, `Aᵒᵖ` its graded opposite and `M` a right dg `A`-module, a left dg
`Aᵒᵖ`-module through the Koszul rule `op a • m = (-1)^{|a||m|} m a` (`DG.DGRightModule.opModule`).
Its graded dual `M^∨ = DG.RightDual A M` is a left dg `A`-module.

* `DG.Cochain.op_smul_of_opModule`: an `Aᵒᵖ`-linear cochain `f : M → M` of degree `n` is right
  `A`-linear without signs, `f (m a) = f(m) a`; conversely (`DG.RightDual.cochainOfRightLinear`)
  every right `A`-linear additive map of degree `n` is such a cochain.
* `DG.RightDual.transpose f`: the **transpose** of `f`, the cochain `M^∨ → M^∨` of degree `n`
  given on homogeneous `φ` by `f^∨(φ) = (-1)^{n |φ|} φ ∘ f` (`DG.RightDual.toHom_transpose`). It
  commutes with the differentials of the Hom complexes (`DG.RightDual.transpose_δ`) and reverses
  compositions (`DG.RightDual.transpose_comp`).
* `DG.RightDual.transposeRingHom`: hence `f ↦ f^∨` is a morphism of dg rings
  `END_{Aᵒᵖ}(M) → END_A(M^∨)ᵒᵖ` into the graded opposite of the endomorphism dg ring of `M^∨`
  (both endomorphism rings with the product of `DG.DGModule.END`).
* `DG.RightBasis.transposeEquiv`: **if `M` has a finite homogeneous basis, transposition is an
  isomorphism of dg `ℤ`-algebras** `END_{Aᵒᵖ}(M) ≃ END_A(M^∨)ᵒᵖ`: the inverse sends `F` to
  `m ↦ Σ_i b_i · (-1)^{n |b_i|} F(δ_i)(m)`, `δ_i` the dual basis (`DG.RightBasis.dualBasis`).

In terms of composition of functions: `END_{Aᵒᵖ}(M)` acting on `M` on the left and `END_A(M^∨)`
acting on `M^∨` on the right are isomorphic dg algebras; the graded opposite records that the
library's `END` uses the same (right action) convention for both.
-/

open MulOpposite DirectSum

set_option linter.unusedSectionVars false

namespace DG

noncomputable section

/-! ### Precomposition with a right-linear map -/

section CompHom

variable {A M : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [AddCommGroup M] [DGAddCommGroup M]
  [Module Aᵐᵒᵖ M] [DGRightModule A M]

namespace RightDual

/-- A right `A`-linear additive endomorphism of `M` of degree `n`. -/
structure IsRightHom (n : ℤ) (f : M →+ M) : Prop where
  map_op_smul : ∀ (a : A) (m : M), f (op a • m) = op a • f m
  map_mem : ∀ (i : ℤ) (m : M), m ∈ grading i → f m ∈ grading (i + n)

variable {n : ℤ} {f : M →+ M}

theorem comp_mem_dualPiece (hf : IsRightHom (A := A) n f) {k : ℤ} {g : M →+ A}
    (hg : g ∈ dualPiece A M k) : g.comp f ∈ dualPiece A M (k + n) :=
  ⟨fun a m => by
    change g (f (op a • m)) = g (f m) * a
    rw [hf.map_op_smul, hg.1], fun i m hm => by
    change g (f m) ∈ grading (i + (k + n))
    rw [show i + (k + n) = i + n + k by ring]
    exact hg.2 _ _ (hf.map_mem i m hm)⟩

theorem comp_mem_dualSubgroup (hf : IsRightHom (A := A) n f) {g : M →+ A}
    (hg : g ∈ dualSubgroup A M) : g.comp f ∈ dualSubgroup A M := by
  induction hg using AddSubgroup.iSup_induction' with
  | hp k g hg => exact AddSubgroup.mem_iSup_of_mem (k + n) (comp_mem_dualPiece hf hg)
  | h1 => exact zero_mem _
  | hadd g g' _ _ hg hg' => rw [AddMonoidHom.add_comp]; exact add_mem hg hg'

/-- Precomposition `φ ↦ φ ∘ f` on `M^∨`, for a right-linear homogeneous `f`. -/
def compHom (hf : IsRightHom (A := A) n f) : RightDual A M →+ RightDual A M where
  toFun φ := mk ((toHom φ).comp f) (comp_mem_dualSubgroup hf (toHom_mem φ))
  map_zero' := ext fun _ => rfl
  map_add' _ _ := ext fun _ => rfl

theorem toHom_compHom (hf : IsRightHom (A := A) n f) (φ : RightDual A M) (m : M) :
    toHom (compHom hf φ) m = toHom φ (f m) := rfl

theorem compHom_mem (hf : IsRightHom (A := A) n f) {k : ℤ} {φ : RightDual A M}
    (hφ : φ ∈ grading k) : compHom hf φ ∈ grading (k + n) :=
  (comp_mem_dualPiece hf (toHom_mem_dualPiece hφ)).2

theorem compHom_smul (hf : IsRightHom (A := A) n f) (a : A) (φ : RightDual A M) :
    compHom hf (a • φ) = a • compHom hf φ := ext fun _ => rfl

end RightDual

end CompHom

/-! ### Cochains over the opposite algebra are right-linear maps -/

section Opposite

variable (R : Type*) {A M : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [DGRing A] [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M]
  [DGRightModule A M]

local notation "𝒜" => DGAlgebra.gradingSubmodule R A
local notation "Aᵒᵖ" => GradedOpposite (DGAlgebra.gradingSubmodule R A)

attribute [local instance] DGRightModule.opModule

/-- `M` is a left dg `Aᵒᵖ`-module (`DGRightModule.dgModule_opModule`). -/
local instance instDGModuleOp : DGModule Aᵒᵖ M := DGRightModule.dgModule_opModule R

private theorem sign_cancel {X : Type*} [AddCommGroup X] (a b c : ℤ) (h : Even (a + b + c))
    (x : X) : koszulSign a • (koszulSign b • koszulSign c • x) = x := by
  rw [smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add, koszulSign_even h, one_smul]

/-- **An `Aᵒᵖ`-linear cochain is right `A`-linear** (without signs): `f (m a) = f(m) a`. -/
theorem Cochain.op_smul_of_opModule {n : ℤ} (f : Cochain Aᵒᵖ M M n) (a : A) (m : M) :
    f (op a • m) = op a • f m := by
  induction a using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, zero_smul, map_zero]
  | h_add a a' ha ha' => rw [op_add, add_smul, add_smul, map_add, ha, ha']
  | @h_homogeneous i a =>
    induction m using DG.induction_on with
    | h_zero => simp only [smul_zero, map_zero]
    | h_add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add]
    | @h_homogeneous j m =>
      have h1 := DGRightModule.opModule_op_smul_of_mem R a.2 m.2
      have h2 := DGRightModule.opModule_op_smul_of_mem R a.2 (f.map_mem m.2)
      have h3 := f.map_smul ((GradedOpposite.op_mem_dgGrading_iff (R := R)).mpr a.2) (m : M)
      rw [h1, f.map_units_smul, h2] at h3
      have h4 := congrArg (koszulSign (i * j) • ·) h3
      rw [smul_smul, Int.units_mul_self, one_smul] at h4
      rw [h4, sign_cancel]
      exact ⟨i * j + i * n, by ring⟩

variable {R}

/-- **A right `A`-linear additive map of degree `n` is an `Aᵒᵖ`-linear cochain.** -/
def RightDual.cochainOfRightLinear {n : ℤ} (f : M →+ M) (hf : RightDual.IsRightHom (A := A) n f) :
    Cochain Aᵒᵖ M M n where
  toFun := f
  map_zero' := map_zero f
  map_add' := map_add f
  map_mem' i m hm := hf.map_mem i m hm
  map_smul' {i x} hx m := by
    have ha : GradedOpposite.unop 𝒜 x ∈ grading i :=
      (GradedOpposite.mem_dgGrading_iff (R := R)).mp hx
    have hx' : x = GradedOpposite.op 𝒜 (GradedOpposite.unop 𝒜 x) := rfl
    induction m using DG.induction_on with
    | h_zero => rw [smul_zero, map_zero, smul_zero, smul_zero]
    | h_add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add, smul_add]
    | @h_homogeneous j m =>
      change f (x • (m : M)) = koszulSign (n * i) • (x • f m)
      rw [hx', DGRightModule.opModule_op_smul_of_mem R ha m.2,
        DGRightModule.opModule_op_smul_of_mem R ha (hf.map_mem j m m.2), Units.smul_def,
        map_zsmul, ← Units.smul_def, hf.map_op_smul, smul_smul, ← koszulSign_add]
      congr 1
      exact (Int.negOnePow_eq_iff _ _).mpr ⟨-(i * j) - i * n + i * j, by ring⟩

theorem RightDual.isRightHom_cochain {n : ℤ} (f : Cochain Aᵒᵖ M M n) :
    RightDual.IsRightHom (A := A) n (f : M →+ M) :=
  ⟨fun a m => Cochain.op_smul_of_opModule R f a m, fun _ _ hm => f.map_mem hm⟩

end Opposite

/-! ### The transpose -/

section Transpose

variable {R : Type*} {A M : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [DGRing A] [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M]
  [DGRightModule A M]

local notation "𝒜" => DGAlgebra.gradingSubmodule R A
local notation "Aᵒᵖ" => GradedOpposite (DGAlgebra.gradingSubmodule R A)

attribute [local instance] DGRightModule.opModule

local instance instDGModuleOp' : DGModule Aᵒᵖ M := DGRightModule.dgModule_opModule R

namespace RightDual

variable {n : ℤ}

private theorem ks_congr {a b : ℤ} (h : Even (a - b)) : koszulSign a = koszulSign b :=
  (Int.negOnePow_eq_iff a b).mpr h

/-- The underlying map of the transpose: `φ ↦ (-1)^n • ι_n(φ ∘ f)`, `ι_n` the grade sign. -/
def transposeFun (f : Cochain Aᵒᵖ M M n) (φ : RightDual A M) : RightDual A M :=
  koszulSign n • gradeSign (RightDual A M) n (compHom (isRightHom_cochain f) φ)

theorem transposeFun_of_mem (f : Cochain Aᵒᵖ M M n) {k : ℤ} {φ : RightDual A M}
    (hφ : φ ∈ grading k) :
    transposeFun f φ = koszulSign (n * k) • compHom (isRightHom_cochain f) φ := by
  rw [transposeFun, gradeSign_of_mem n (compHom_mem _ hφ), smul_smul, ← koszulSign_add]
  congr 1
  refine ks_congr ?_
  have := Int.even_mul_succ_self n
  convert this using 1
  ring

/-- **The transpose** `f^∨ : M^∨ → M^∨` of an `Aᵒᵖ`-linear cochain `f` of degree `n`, an `A`-linear
cochain of degree `n`: `f^∨(φ) = (-1)^{n |φ|} φ ∘ f` for homogeneous `φ`. -/
def transpose (f : Cochain Aᵒᵖ M M n) : Cochain A (RightDual A M) (RightDual A M) n where
  toFun := transposeFun f
  map_zero' := by simp [transposeFun]
  map_add' φ ψ := by simp [transposeFun, smul_add]
  map_mem' k φ hφ := by
    change transposeFun f φ ∈ grading (k + n)
    rw [transposeFun_of_mem f hφ]
    exact units_smul_mem_grading _ (compHom_mem _ hφ)
  map_smul' {i a} ha φ := by
    change transposeFun f (a • φ) = koszulSign (n * i) • (a • transposeFun f φ)
    rw [transposeFun, transposeFun, compHom_smul, gradeSign_smul n ha,
      Units.smul_def (koszulSign n),
      Units.smul_def (koszulSign n), smul_comm a ((koszulSign n : ℤˣ) : ℤ), ← Units.smul_def,
      ← Units.smul_def, smul_smul, smul_smul, mul_comm]

theorem transpose_apply (f : Cochain Aᵒᵖ M M n) (φ : RightDual A M) :
    transpose f φ = transposeFun f φ := rfl

/-- `f^∨(φ)(m) = (-1)^{n k} φ(f m)` for `φ` of degree `k`. -/
theorem toHom_transpose (f : Cochain Aᵒᵖ M M n) {k : ℤ} {φ : RightDual A M}
    (hφ : φ ∈ grading k) (m : M) :
    toHom (transpose f φ) m = koszulSign (n * k) • toHom φ (f m) := by
  rw [transpose_apply, transposeFun_of_mem f hφ, toHom_units_smul]
  rfl

private theorem hom_units_smul_apply (u : ℤˣ) (g : M →+ A) (x : M) : (u • g) x = u • g x := rfl

/-- `(δ f)^∨ = δ (f^∨)`: transposition commutes with the differentials of the Hom complexes. -/
theorem transpose_δ {m : ℤ} (hnm : n + 1 = m) (f : Cochain Aᵒᵖ M M n) :
    transpose (δ n m f) = δ n m (transpose f) := by
  subst hnm
  refine Cochain.ext fun φ => ?_
  induction φ using induction_on' with
  | zero => rw [map_zero, map_zero]
  | add φ ψ h h' => rw [map_add, map_add, h, h']
  | homogeneous k φ hφ =>
    refine ext fun x => ?_
    have e1 : koszulSign ((n + 1) * k) = koszulSign (n * k) * koszulSign k := by
      rw [← koszulSign_add]; congr 1; ring
    have e2 : koszulSign n * koszulSign (n * (k + 1)) = koszulSign (n * k) := by
      rw [← koszulSign_add]; exact ks_congr ⟨n, by ring⟩
    rw [toHom_transpose _ hφ, δ_apply n _ rfl, δ_apply n _ rfl, toHom_sub, AddMonoidHom.sub_apply,
      toHom_units_smul, hom_units_smul_apply, d_apply_of_mem ((transpose f).map_mem hφ),
      toHom_transpose _ hφ, toHom_transpose _ hφ, toHom_transpose _ (d_mem hφ),
      d_apply_of_mem hφ, d_units_smul, AddMonoidHom.map_sub,
      Units.smul_def (koszulSign n) (f (d x)),
      AddMonoidHom.map_zsmul, ← Units.smul_def]
    simp only [smul_sub, smul_smul, ← mul_assoc]
    rw [e1, e2, koszulSign_add k n]
    simp only [Units.smul_def, Units.val_mul]
    module

/-- **Transposition reverses compositions**: `(g ∘ f)^∨ = (-1)^{|f||g|} f^∨ ∘ g^∨`. -/
theorem transpose_comp {m : ℤ} (f : Cochain Aᵒᵖ M M m) (g : Cochain Aᵒᵖ M M n) :
    transpose (g.comp f rfl) =
      koszulSign (m * n) • (transpose f).comp (transpose g) (add_comm n m) := by
  refine Cochain.ext fun φ => ?_
  induction φ using induction_on' with
  | zero => rw [map_zero, map_zero]
  | add φ ψ h h' => rw [map_add, map_add, h, h']
  | homogeneous k φ hφ =>
    refine ext fun x => ?_
    rw [toHom_transpose _ hφ, Cochain.units_smul_apply, toHom_units_smul, hom_units_smul_apply,
      Cochain.comp_apply, Cochain.comp_apply, toHom_transpose _ ((transpose g).map_mem hφ),
      toHom_transpose _ hφ, smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add]
    congr 1
    exact ks_congr ⟨-(m * n), by ring⟩

/-- `id^∨ = id`. -/
theorem transpose_id : transpose (Cochain.id Aᵒᵖ M) = Cochain.id A (RightDual A M) := by
  refine Cochain.ext fun φ => ?_
  induction φ using induction_on' with
  | zero => rw [map_zero, map_zero]
  | add φ ψ h h' => rw [map_add, map_add, h, h']
  | homogeneous k φ hφ =>
    refine ext fun x => ?_
    rw [toHom_transpose _ hφ, zero_mul, koszulSign_zero, one_smul]
    rfl

theorem transpose_add (f g : Cochain Aᵒᵖ M M n) :
    transpose (f + g) = transpose f + transpose g := by
  refine Cochain.ext fun φ => ?_
  induction φ using induction_on' with
  | zero => rw [map_zero, map_zero]
  | add φ ψ h h' => rw [map_add, map_add, h, h']
  | homogeneous k φ hφ =>
    refine ext fun x => ?_
    rw [toHom_transpose _ hφ, Cochain.add_apply, Cochain.add_apply, toHom_add,
      AddMonoidHom.add_apply,
      toHom_transpose _ hφ, toHom_transpose _ hφ, map_add, smul_add]

theorem transpose_units_smul (u : ℤˣ) (f : Cochain Aᵒᵖ M M n) :
    transpose (u • f) = u • transpose f := by
  refine Cochain.ext fun φ => ?_
  induction φ using induction_on' with
  | zero => rw [map_zero, map_zero]
  | add φ ψ h h' => rw [map_add, map_add, h, h']
  | homogeneous k φ hφ =>
    refine ext fun x => ?_
    rw [toHom_transpose _ hφ, Cochain.units_smul_apply, Cochain.units_smul_apply,
      toHom_units_smul, hom_units_smul_apply, toHom_transpose _ hφ, Units.smul_def u, map_zsmul,
      ← Units.smul_def, smul_comm]

variable (A M n) in
/-- Transposition as an additive map. -/
def transposeHom : Cochain Aᵒᵖ M M n →+ Cochain A (RightDual A M) (RightDual A M) n where
  toFun := transpose
  map_zero' := by
    have h := transpose_add (0 : Cochain Aᵒᵖ M M n) 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  map_add' := transpose_add

/-! ### The morphism of dg rings `END_{Aᵒᵖ}(M) → END_A(M^∨)ᵒᵖ` -/

variable (R A M) in
/-- `END_{Aᵒᵖ}(M) → END_A(M^∨)`, transposition in each degree (an anti-homomorphism). -/
def transposeSum : DGModule.END Aᵒᵖ M →+ DGModule.END A (RightDual A M) :=
  DirectSum.map fun n => transposeHom A M n

theorem transposeSum_of (f : Cochain Aᵒᵖ M M n) :
    transposeSum R A M (DirectSum.of (fun n => Cochain Aᵒᵖ M M n) n f) =
      DirectSum.of (fun n => Cochain A (RightDual A M) (RightDual A M) n) n (transpose f) :=
  DirectSum.map_of _ _ _

theorem transposeSum_d (x : DGModule.END Aᵒᵖ M) :
    transposeSum R A M (d x) = d (transposeSum R A M x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n f =>
    rw [DGModule.HOM.d_of, transposeSum_of, transposeSum_of, DGModule.HOM.d_of, transpose_δ rfl]
  | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add]

local notation "Eᵒᵖ" =>
  GradedOpposite (DGAlgebra.gradingSubmodule ℤ (DGModule.END A (RightDual A M)))

theorem of_mem_gradingSubmodule_END {n : ℤ} (F : Cochain A (RightDual A M) (RightDual A M) n) :
    (DirectSum.of (fun n => Cochain A (RightDual A M) (RightDual A M) n) n F :
        DGModule.END A (RightDual A M)) ∈
      DGAlgebra.gradingSubmodule ℤ (DGModule.END A (RightDual A M)) n :=
  of_mem_summand _ _

theorem transposeSum_of_mul_of {m : ℤ} (f : Cochain Aᵒᵖ M M m) (g : Cochain Aᵒᵖ M M n) :
    GradedOpposite.op _ (transposeSum R A M (DirectSum.of (fun n => Cochain Aᵒᵖ M M n) m f *
        DirectSum.of (fun n => Cochain Aᵒᵖ M M n) n g)) =
      (GradedOpposite.op _ (transposeSum R A M (DirectSum.of (fun n => Cochain Aᵒᵖ M M n) m f)) *
        GradedOpposite.op _ (transposeSum R A M (DirectSum.of (fun n => Cochain Aᵒᵖ M M n) n g))
          : Eᵒᵖ) := by
  rw [DGModule.END.of_mul_of, transposeSum_of, transposeSum_of, transposeSum_of,
    GradedOpposite.op_mul_op _ (of_mem_gradingSubmodule_END _) (of_mem_gradingSubmodule_END _),
    DGModule.END.of_mul_of, transpose_units_smul, transpose_comp, smul_smul, Int.units_mul_self,
    one_smul, Units.smul_def (koszulSign (n * m)), map_zsmul, map_zsmul, ← Units.smul_def,
    smul_smul, mul_comm n m, Int.units_mul_self, one_smul]
  congr 1
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (Sigma.ext (add_comm m n) (Cochain.heq_of_forall (add_comm m n) fun _ => rfl))

variable (R A M) in
/-- **Transposition is a morphism of dg rings** `END_{Aᵒᵖ}(M) → END_A(M^∨)ᵒᵖ`,
`f ↦ op (f^∨)`. -/
def transposeRingHom : DGModule.END Aᵒᵖ M →+* Eᵒᵖ where
  toFun x := GradedOpposite.op _ (transposeSum R A M x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]
  map_one' := by
    rw [DGModule.END.one_def, transposeSum_of, transpose_id, ← DGModule.END.one_def,
      GradedOpposite.op_one]
  map_mul' x y := by
    induction x using DirectSum.induction_on with
    | zero => rw [zero_mul, map_zero, map_zero, zero_mul]
    | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', map_add, map_add, add_mul]
    | of m f =>
      induction y using DirectSum.induction_on with
      | zero => rw [mul_zero, map_zero, map_zero, mul_zero]
      | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', map_add, map_add, mul_add]
      | of n g => exact transposeSum_of_mul_of f g

theorem transposeRingHom_apply (x : DGModule.END Aᵒᵖ M) :
    transposeRingHom R A M x = GradedOpposite.op _ (transposeSum R A M x) := rfl

theorem transposeRingHom_mem {n : ℤ} {x : DGModule.END Aᵒᵖ M} (hx : x ∈ grading n) :
    transposeRingHom R A M x ∈ grading n := by
  rw [GradedOpposite.mem_dgGrading_iff (R := ℤ), transposeRingHom_apply, GradedOpposite.unop_op]
  obtain ⟨f, rfl⟩ := hx
  rw [transposeSum_of]
  exact of_mem_summand _ _

theorem transposeRingHom_d (x : DGModule.END Aᵒᵖ M) :
    transposeRingHom R A M (d x) = d (transposeRingHom R A M x) := by
  rw [transposeRingHom_apply, transposeRingHom_apply, transposeSum_d, GradedOpposite.d_op]

end RightDual

/-! ### Modules with a finite basis -/

namespace RightBasis

open RightDual

variable {ι : Type*} [Fintype ι] (B : RightBasis A M ι) {n : ℤ}

local notation "Eᵒᵖ" =>
  GradedOpposite (DGAlgebra.gradingSubmodule ℤ (DGModule.END A (RightDual A M)))

/-- The map `m ↦ Σ_i b_i · (-1)^{n |b_i|} F(δ_i)(m)` attached to a cochain `F` on `M^∨`. -/
def untransposeFun (F : Cochain A (RightDual A M) (RightDual A M) n) : M →+ M where
  toFun m := ∑ i, op (koszulSign (n * B.deg i) • toHom (F (B.δ i)) m) • B.b i
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, smul_add, op_add, add_smul, Finset.sum_add_distrib]

theorem untransposeFun_apply (F : Cochain A (RightDual A M) (RightDual A M) n) (m : M) :
    B.untransposeFun F m = ∑ i, op (koszulSign (n * B.deg i) • toHom (F (B.δ i)) m) • B.b i := rfl

theorem isRightHom_untransposeFun (F : Cochain A (RightDual A M) (RightDual A M) n) :
    IsRightHom (A := A) n (B.untransposeFun F) where
  map_op_smul a m := by
    rw [untransposeFun_apply, untransposeFun_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_op_smul, smul_smul, ← op_mul, smul_mul_assoc]
  map_mem j m hm := by
    rw [untransposeFun_apply]
    refine sum_mem fun i _ => ?_
    have h := op_smul_mem_grading
      (units_smul_mem_grading (koszulSign (n * B.deg i)) (apply_mem_grading
        (F.map_mem (B.δ_mem i)) hm)) (B.b_mem i)
    rwa [show B.deg i + (j + (-B.deg i + n)) = j + n by ring] at h

/-- The inverse of transposition, for `M` with a finite basis. -/
def untranspose (F : Cochain A (RightDual A M) (RightDual A M) n) : Cochain Aᵒᵖ M M n :=
  cochainOfRightLinear (R := R) (B.untransposeFun F) (B.isRightHom_untransposeFun F)

theorem untranspose_apply (F : Cochain A (RightDual A M) (RightDual A M) n) (m : M) :
    B.untranspose (R := R) F m = B.untransposeFun F m := rfl

/-- Two cochains on `M^∨` agreeing on the dual basis are equal. -/
theorem cochain_ext_δ {F G : Cochain A (RightDual A M) (RightDual A M) n}
    (h : ∀ i, F (B.δ i) = G (B.δ i)) : F = G := by
  refine Cochain.ext fun φ => ?_
  rw [← B.dualBasis.sum_coeff φ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dualBasis_b]
  induction B.dualBasis.coeff φ i using DG.induction_on with
  | h_zero => rw [zero_smul, map_zero, map_zero]
  | h_add a a' ha ha' => rw [add_smul, map_add, map_add, ha, ha']
  | h_homogeneous a => rw [F.map_smul a.2, G.map_smul a.2, h]

theorem transpose_untranspose (F : Cochain A (RightDual A M) (RightDual A M) n) :
    transpose (B.untranspose (R := R) F) = F := by
  classical
  refine B.cochain_ext_δ fun i => ext fun x => ?_
  rw [toHom_transpose _ (B.δ_mem i), untranspose_apply, toHom_δ, untransposeFun_apply,
    B.coeff_sum (fun l => koszulSign (n * B.deg l) • toHom (F (B.δ l)) x), smul_smul,
    ← koszulSign_add, show n * -B.deg i + n * B.deg i = 0 by ring, koszulSign_zero, one_smul]

theorem untranspose_transpose (f : Cochain Aᵒᵖ M M n) :
    B.untranspose (R := R) (transpose f) = f := by
  refine Cochain.ext fun m => ?_
  rw [untranspose_apply, untransposeFun_apply]
  conv_rhs => rw [← B.sum_coeff (f m)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toHom_transpose _ (B.δ_mem i), toHom_δ, smul_smul, ← koszulSign_add,
    show n * B.deg i + n * -B.deg i = 0 by ring, koszulSign_zero, one_smul]

include B in
theorem transposeRingHom_bijective : Function.Bijective (transposeRingHom R A M) := by
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h' : transposeSum R A M x = transposeSum R A M y := (GradedOpposite.op _).injective h
    refine (DirectSum.map_injective _).mpr (fun n => ?_) h'
    exact Function.LeftInverse.injective (g := B.untranspose (R := R))
      (fun f => B.untranspose_transpose f)
  · obtain ⟨y, rfl⟩ := (GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ
      (DGModule.END A (RightDual A M)))).surjective y
    induction y using DirectSum.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | of n F =>
      refine ⟨DirectSum.of (fun n => Cochain Aᵒᵖ M M n) n (B.untranspose (R := R) F), ?_⟩
      rw [transposeRingHom_apply, transposeSum_of, B.transpose_untranspose]
    | add y y' hy hy' =>
      obtain ⟨x, hx⟩ := hy
      obtain ⟨x', hx'⟩ := hy'
      exact ⟨x + x', by rw [map_add, hx, hx', map_add]⟩

variable (R) in
/-- **Transposition `END_{Aᵒᵖ}(M) ≃ END_A(M^∨)ᵒᵖ`** for a right dg module `M` with a finite
homogeneous basis: an isomorphism of dg `ℤ`-algebras, `f ↦ op (f^∨)`,
`f^∨(φ) = (-1)^{|f||φ|} φ ∘ f`. -/
def transposeEquiv : DGModule.END Aᵒᵖ M ≃ᵈᵍₐ[ℤ] Eᵒᵖ :=
  DGAlgEquiv.ofAlgEquiv
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (transposeRingHom R A M)
      B.transposeRingHom_bijective) fun r => by
        rw [eq_intCast (algebraMap ℤ (DGModule.END Aᵒᵖ M)) r, eq_intCast (algebraMap ℤ Eᵒᵖ) r]
        exact map_intCast _ r)
    (fun ha => transposeRingHom_mem ha) fun a => transposeRingHom_d a

theorem transposeEquiv_apply (x : DGModule.END Aᵒᵖ M) :
    B.transposeEquiv R x = transposeRingHom R A M x := rfl

end RightBasis

namespace RightDual

end RightDual

end Transpose

end

end DG
