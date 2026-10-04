import DG.Module.ExternalTensor
import DG.Homotopy.HomotopyCategory

/-!
# The external tensor product as a bifunctor, and homotopies

For dg rings `A`, `B`, the external tensor product `M ⊠ N = M ⊗[ℤ] N` (a dg module over
`A ⊗ B = A ᵍ⊗[ℤ] B`, `DG.ExternalTensor.instDGModule`) is a bifunctor
`DG.ExternalTensor.functor : DGModuleCat A ⥤ DGModuleCat B ⥤ DGModuleCat (A ⊗ B)`.

Cochains extend: a cochain `h` of degree `k` over `A` gives `h ⊠ 1`, `m ⊗ n ↦ h m ⊗ n`
(`DG.ExternalTensor.leftCochain`), and a cochain `h` over `B` gives `1 ⊠ h`,
`m ⊗ n ↦ (-1)^{k |m|} m ⊗ h n` (`DG.ExternalTensor.rightCochain`), both cochains over `A ⊗ B`.
Hence homotopies extend in each variable (`DG.ExternalTensor.homotopyLeft`,
`DG.ExternalTensor.homotopyRight`), and the bifunctor descends to homotopy categories
(`DG.ExternalTensor.homotopyFunctor : K(A) ⥤ K(B) ⥤ K(A ⊗ B)`).
-/

open CategoryTheory
open scoped TensorProduct

universe v u₁ u₂

noncomputable section

namespace DG

namespace ExternalTensor

private theorem ks_eq {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

variable {A : Type u₁} {B : Type u₂} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B]
  [DGAddCommGroup B] [DGRing B]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ

section Maps

variable {M M' : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup M'] [DGAddCommGroup M'] [Module A M'] [DGModule A M']
  {N N' : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']

/-- `f ⊠ g` as a morphism of dg modules over `A ⊗ B`. -/
def tensorDGHom (f : M →ᵈᵍ[A] M') (g : N →ᵈᵍ[B] N') : (M ⊗[ℤ] N) →ᵈᵍ[AB] (M' ⊗[ℤ] N') where
  toLinearMap := tensorLinearMap f.toLinearMap g.toLinearMap (fun h => f.map_mem h)
  map_mem' hx := tensorMap_mem f.toLinearMap.toAddMonoidHom g.toLinearMap.toAddMonoidHom
    (fun h => f.map_mem h) (fun h => g.map_mem h) hx
  map_d' x := tensorMap_d f.toLinearMap.toAddMonoidHom g.toLinearMap.toAddMonoidHom
    (fun h => f.map_mem h) (fun m => f.map_d m) (fun n => g.map_d n) x

omit [DGModule B N] [DGModule B N'] in
@[simp]
theorem tensorDGHom_tmul (f : M →ᵈᵍ[A] M') (g : N →ᵈᵍ[B] N') (m : M) (n : N) :
    tensorDGHom f g (m ⊗ₜ n) = f m ⊗ₜ g n := rfl

/-! ### Cochains -/

omit [DGAddCommGroup M] [DGAddCommGroup N] in
theorem units_tmul (u : ℤˣ) (m : M) (n : N) : (u • m) ⊗ₜ[ℤ] n = u • (m ⊗ₜ[ℤ] n) := by
  rw [Units.smul_def, Units.smul_def, TensorProduct.smul_tmul']

omit [DGAddCommGroup M] [DGAddCommGroup N] in
theorem tmul_units (u : ℤˣ) (m : M) (n : N) : m ⊗ₜ[ℤ] (u • n) = u • (m ⊗ₜ[ℤ] n) := by
  rw [Units.smul_def, Units.smul_def, TensorProduct.tmul_smul]

/-- Extension of a cochain over `A` and a cochain over `A ⊗ B` from its values on pure tensors
of homogeneous elements. -/
def cochainOfAddHom {k : ℤ} (F : M ⊗[ℤ] N →+ M' ⊗[ℤ] N')
    (hmem : ∀ {i j : ℤ} {m : M} {n : N}, m ∈ grading i → n ∈ grading j →
      F (m ⊗ₜ n) ∈ grading (i + j + k))
    (hsmul : ∀ {i₁ j₁ p : ℤ} {a : A} {b : B}, a ∈ grading i₁ → b ∈ grading j₁ → ∀ {m : M},
      m ∈ grading p → ∀ n : N,
        F ((a ᵍ⊗ₜ[ℤ] b : AB) • (m ⊗ₜ[ℤ] n)) =
          koszulSign (k * (i₁ + j₁)) • ((a ᵍ⊗ₜ[ℤ] b : AB) • F (m ⊗ₜ[ℤ] n))) :
    Cochain AB (M ⊗[ℤ] N) (M' ⊗[ℤ] N') k where
  toFun := F
  map_zero' := map_zero F
  map_add' := map_add F
  map_mem' _ _ hx := map_mem_grading_of_tmul F k hmem hx
  map_smul' {i x} hx y := by
    refine GradedTensorProduct.grading_induction 𝒜 ℬ hx
      (motive := fun x => F (x • y) = koszulSign (k * i) • (x • F y)) ?_ ?_ ?_
    · rw [zero_smul', map_zero, zero_smul', smul_zero]
    · intro i₁ j₁ a b hij
      subst hij
      induction y using tensor_induction_on with
      | zero => rw [smul_zero', map_zero, smul_zero', smul_zero]
      | add y y' hy hy' => rw [smul_add', map_add, hy, hy', map_add, smul_add', smul_add]
      | tmul m n =>
        obtain ⟨m, hm⟩ := m
        obtain ⟨n, -⟩ := n
        exact hsmul a.2 b.2 hm n
    · intro x x' hx hx'
      rw [add_smul', map_add, hx, hx', add_smul', smul_add]

variable (N) in
/-- `h ⊠ 1`: `m ⊗ n ↦ h m ⊗ n`, for a cochain `h` of degree `k` over `A`. -/
def leftCochain {k : ℤ} (h : Cochain A M M' k) : Cochain AB (M ⊗[ℤ] N) (M' ⊗[ℤ] N) k :=
  cochainOfAddHom (tensorMap (AddMonoidHomClass.toAddMonoidHom h) (AddMonoidHom.id N))
    (fun {i j m n} hm hn => by
      have := tmul_mem_grading (h.map_mem hm) hn
      rwa [show i + k + j = i + j + k by ring] at this)
    (fun {i₁ j₁ p a b} ha hb {m} hm n => by
      simp only [tensorMap_tmul, AddMonoidHom.id_apply]
      rw [tmul_smul_tmul a hb hm n, map_units_zsmul, tensorMap_tmul, AddMonoidHom.id_apply,
        AddMonoidHom.coe_coe, h.map_smul ha m, units_tmul,
        tmul_smul_tmul a hb (h.map_mem hm) n, smul_smul, smul_smul, ← koszulSign_add,
        ← koszulSign_add]
      congr 1
      exact ks_eq ⟨-(k * j₁), by ring⟩)

omit [DGModule B N] in
@[simp]
theorem leftCochain_tmul {k : ℤ} (h : Cochain A M M' k) (m : M) (n : N) :
    leftCochain (B := B) N h (m ⊗ₜ n) = h m ⊗ₜ n := rfl

variable (M) in
/-- `1 ⊠ h`: `m ⊗ n ↦ (-1)^{k |m|} m ⊗ h n`, for a cochain `h` of degree `k` over `B`. -/
def rightCochain {k : ℤ} (h : Cochain B N N' k) : Cochain AB (M ⊗[ℤ] N) (M ⊗[ℤ] N') k :=
  cochainOfAddHom (tensorMap (twist M k) (AddMonoidHomClass.toAddMonoidHom h))
    (fun {i j m n} hm hn => by
      rw [tensorMap_tmul, twist_of_mem k hm, units_tmul]
      refine units_smul_mem_grading _ ?_
      have := tmul_mem_grading hm (h.map_mem hn)
      rwa [show i + (j + k) = i + j + k by ring] at this)
    (fun {i₁ j₁ p a b} ha hb {m} hm n => by
      rw [tmul_smul_tmul a hb hm n, map_units_zsmul, tensorMap_tmul, tensorMap_tmul,
        twist_of_mem k (smul_mem_grading ha hm), twist_of_mem k hm,
        AddMonoidHom.coe_coe, h.map_smul hb n, units_tmul, tmul_units,
        units_tmul, smul_units_smul, tmul_smul_tmul a hb hm (h n), smul_smul, smul_smul,
        smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add, ← koszulSign_add,
        ← koszulSign_add]
      congr 1
      exact ks_eq ⟨0, by ring⟩)

omit [DGModule B N] [DGModule B N'] in
theorem rightCochain_tmul {k : ℤ} (h : Cochain B N N' k) {i : ℤ} {m : M} (hm : m ∈ grading i)
    (n : N) : rightCochain (A := A) M h (m ⊗ₜ n) = koszulSign (k * i) • (m ⊗ₜ h n) := by
  change tensorMap (twist M k) _ (m ⊗ₜ n) = _
  rw [tensorMap_tmul, twist_of_mem k hm, units_tmul, mul_comm]
  rfl

private theorem ks_val (n : ℤ) : (koszulSign n : ℤ) = if Even n then 1 else -1 := by
  split_ifs with h
  · rw [koszulSign, Int.negOnePow_even n h]; rfl
  · rw [koszulSign, Int.negOnePow_odd n (Int.not_even_iff_odd.mp h)]; rfl

/-! ### Homotopies -/

theorem cochain_units {X Y : Type*} [AddCommGroup X] [DGAddCommGroup X] [Module AB X]
    [AddCommGroup Y] [DGAddCommGroup Y] [Module AB Y] {k : ℤ} (c : Cochain AB X Y k) (u : ℤˣ)
    (x : X) : c (u • x) = u • c x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- A homotopy `f ≃ g` over `A` gives a homotopy `f ⊠ 1 ≃ g ⊠ 1`. -/
def homotopyLeft {f g : M →ᵈᵍ[A] M'} (h : DGHomotopy f g) :
    DGHomotopy (tensorDGHom f (DGModuleHom.id : N →ᵈᵍ[B] N))
      (tensorDGHom g (DGModuleHom.id : N →ᵈᵍ[B] N)) :=
  DGHomotopy.mk' (leftCochain N h.hom) fun x => by
    induction x using tensor_induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, hx, hy, d_add, map_add, d_add, map_add, map_add]
      abel
    | @tmul p q m n =>
      obtain ⟨m, hm⟩ := m
      obtain ⟨n, -⟩ := n
      change f m ⊗ₜ n = d (h.hom m ⊗ₜ n) + leftCochain N h.hom (d (m ⊗ₜ n)) + g m ⊗ₜ n
      rw [d_tmul_of_mem (h.hom.map_mem hm), d_tmul_of_mem hm, map_add, cochain_units,
        leftCochain_tmul, leftCochain_tmul, h.comm m]
      simp only [Units.smul_def, ks_val, TensorProduct.add_tmul]
      by_cases hp : Even p <;> simp [Int.even_add, hp] <;> abel

/-- A homotopy `f ≃ g` over `B` gives a homotopy `1 ⊠ f ≃ 1 ⊠ g`. -/
def homotopyRight {f g : N →ᵈᵍ[B] N'} (h : DGHomotopy f g) :
    DGHomotopy (tensorDGHom (DGModuleHom.id : M →ᵈᵍ[A] M) f)
      (tensorDGHom (DGModuleHom.id : M →ᵈᵍ[A] M) g) :=
  DGHomotopy.mk' (rightCochain M h.hom) fun x => by
    induction x using tensor_induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, hx, hy, d_add, map_add, d_add, map_add, map_add]
      abel
    | @tmul p q m n =>
      obtain ⟨m, hm⟩ := m
      obtain ⟨n, -⟩ := n
      change m ⊗ₜ f n = d (rightCochain M h.hom (m ⊗ₜ n)) +
        rightCochain M h.hom (d (m ⊗ₜ n)) + m ⊗ₜ g n
      rw [rightCochain_tmul h.hom hm, d_units_smul, d_tmul_of_mem hm, d_tmul_of_mem hm, map_add,
        cochain_units, rightCochain_tmul h.hom (d_mem hm), rightCochain_tmul h.hom hm, h.comm n]
      simp only [Units.smul_def, ks_val, TensorProduct.tmul_add, smul_add, smul_smul]
      by_cases hp : Even p <;> simp [Int.even_add, even_neg, hp] <;> abel

end Maps

/-! ### The bifunctor -/

section Functor

theorem tensorDGHom_ext {M M' : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [DGModule A M] [AddCommGroup M'] [DGAddCommGroup M'] [Module A M'] [DGModule A M']
    {N N' : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
    [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']
    {φ ψ : (M ⊗[ℤ] N) →ᵈᵍ[AB] (M' ⊗[ℤ] N')} (h : ∀ m n, φ (m ⊗ₜ n) = ψ (m ⊗ₜ n)) : φ = ψ :=
  DGModuleHom.ext fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul m n => exact h m n
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (A B)

/-- The external tensor product `M ⊠ N` as a bifunctor
`DGModuleCat A ⥤ DGModuleCat B ⥤ DGModuleCat (A ⊗ B)`. -/
def functor : DGModuleCat.{v} A ⥤ DGModuleCat.{v} B ⥤ DGModuleCat.{v} AB where
  obj M :=
    { obj N := DGModuleCat.of AB (M ⊗[ℤ] N)
      map g := DGModuleCat.ofHom (tensorDGHom DGModuleHom.id g.hom)
      map_id _ := DGModuleCat.hom_ext (tensorDGHom_ext fun _ _ => rfl)
      map_comp _ _ := DGModuleCat.hom_ext (tensorDGHom_ext fun _ _ => rfl) }
  map f :=
    { app _ := DGModuleCat.ofHom (tensorDGHom f.hom DGModuleHom.id)
      naturality _ _ _ := DGModuleCat.hom_ext (tensorDGHom_ext fun _ _ => rfl) }
  map_id _ := NatTrans.ext (funext fun _ => DGModuleCat.hom_ext (tensorDGHom_ext fun _ _ => rfl))
  map_comp _ _ :=
    NatTrans.ext (funext fun _ => DGModuleCat.hom_ext (tensorDGHom_ext fun _ _ => rfl))

variable {A B}

@[simp]
theorem functor_obj_obj (M : DGModuleCat.{v} A) (N : DGModuleCat.{v} B) :
    (((functor A B).obj M).obj N : Type v) = (M ⊗[ℤ] N) := rfl

theorem functor_obj_map_hom (M : DGModuleCat.{v} A) {N N' : DGModuleCat.{v} B} (g : N ⟶ N') :
    (((functor A B).obj M).map g).hom = tensorDGHom DGModuleHom.id g.hom := rfl

theorem functor_map_app_hom {M M' : DGModuleCat.{v} A} (f : M ⟶ M') (N : DGModuleCat.{v} B) :
    (((functor A B).map f).app N).hom = tensorDGHom f.hom DGModuleHom.id := rfl

variable (A B)

/-- For fixed `M`, `M ⊠ -` on homotopy categories. -/
def homotopyFunctorObj (M : DGModuleCat.{v} A) :
    HomotopyCategory.{v} B ⥤ HomotopyCategory.{v} AB :=
  CategoryTheory.Quotient.lift _ ((functor A B).obj M ⋙ HomotopyCategory.quotient AB)
    fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (homotopyRight h)

/-- `M ⊠ -` on homotopy categories, as a functor of `M`. -/
def homotopyFunctorAux : DGModuleCat.{v} A ⥤ (HomotopyCategory.{v} B ⥤ HomotopyCategory.{v} AB)
    where
  obj M := homotopyFunctorObj A B M
  map f := CategoryTheory.Quotient.natTransLift _
    { app N := (HomotopyCategory.quotient AB).map (((functor A B).map f).app N)
      naturality _ _ g := by
        change (HomotopyCategory.quotient AB).map _ ≫ _ = _ ≫ (HomotopyCategory.quotient AB).map _
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        exact congrArg (HomotopyCategory.quotient AB).map (((functor A B).map f).naturality g) }
  map_id M := by
    refine CategoryTheory.Quotient.natTrans_ext _ _ (NatTrans.ext (funext fun N => ?_))
    change (HomotopyCategory.quotient AB).map (((functor A B).map (𝟙 M)).app N) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id]
  map_comp f g := by
    refine CategoryTheory.Quotient.natTrans_ext _ _ (NatTrans.ext (funext fun N => ?_))
    change (HomotopyCategory.quotient AB).map (((functor A B).map (f ≫ g)).app N) =
      (HomotopyCategory.quotient AB).map (((functor A B).map f).app N) ≫
        (HomotopyCategory.quotient AB).map (((functor A B).map g).app N)
    rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app, CategoryTheory.Functor.map_comp]

/-- **The external tensor product on homotopy categories**, `K(A) ⥤ K(B) ⥤ K(A ⊗ B)`. -/
def homotopyFunctor :
    HomotopyCategory.{v} A ⥤ HomotopyCategory.{v} B ⥤ HomotopyCategory.{v} AB :=
  CategoryTheory.Quotient.lift _ (homotopyFunctorAux A B) fun M M' f f' ⟨h⟩ => by
    refine CategoryTheory.Quotient.natTrans_ext _ _ (NatTrans.ext (funext fun N => ?_))
    exact HomotopyCategory.eq_of_homotopy _ _ (homotopyLeft h)

variable {A B}

theorem homotopyFunctor_obj_obj (M : DGModuleCat.{v} A) (N : DGModuleCat.{v} B) :
    ((homotopyFunctor A B).obj ((HomotopyCategory.quotient A).obj M)).obj
      ((HomotopyCategory.quotient B).obj N) =
      (HomotopyCategory.quotient AB).obj (((functor A B).obj M).obj N) := rfl

end Functor

end ExternalTensor

end DG
