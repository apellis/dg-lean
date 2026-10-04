import DG.Homotopy.ExternalTensor
import DG.Derived.KProjective

/-!
# The derived external tensor product

For dg rings `A`, `B` and `A ⊗ B = A ᵍ⊗[ℤ] B`, the derived external tensor product
`- ⊠ᴸ - : D(A) ⥤ D(B) ⥤ D(A ⊗ B)` (`DG.DerivedCategory.externalTensor`) is computed on
K-projective resolutions in both variables: `D(A)` is equivalent to the full subcategory of
K-projective objects of the homotopy category `K(A)` (`DG.DerivedCategory.kProjectiveEquivalence`),
and the external tensor product on homotopy categories (`DG.ExternalTensor.homotopyFunctor`)
is applied there. No flatness hypothesis on `A` or `B` is needed.

On K-projective modules it is the underived external tensor product,
`Q P ⊠ᴸ Q P' ≅ Q (P ⊠ P')` (`DG.DerivedCategory.externalTensorObjIso`); in particular
`A ⊠ᴸ B ≅ A ⊗ B` on the regular modules (`DG.DerivedCategory.externalTensorRegularIso`).

All dg modules have carriers in the universe of the rings.
-/

open CategoryTheory
open scoped TensorProduct

universe w u

noncomputable section

namespace DG

namespace DerivedCategory

section KProjective

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w, u} A]

/-- The full subcategory of K-projective objects of the homotopy category. -/
abbrev KProjective := (HomotopyCategory.subcategoryKProjective.{u} A).FullSubcategory

/-- The localization functor restricted to K-projective objects. -/
abbrev kProjectiveFunctor : KProjective A ⥤ DerivedCategory.{w, u} A :=
  (HomotopyCategory.subcategoryKProjective.{u} A).ι ⋙ Qh

instance : (kProjectiveFunctor A).Full where
  map_surjective {X Y} f :=
    ⟨ObjectProperty.homMk (((ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated
      X.property Qh Y.obj).2 f).choose),
      ((ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated X.property Qh Y.obj).2 f).choose_spec⟩

instance : (kProjectiveFunctor A).Faithful where
  map_injective {X Y} _ _ h :=
    ObjectProperty.hom_ext _
      ((ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated X.property Qh Y.obj).1 h)

instance : (kProjectiveFunctor A).EssSurj where
  mem_essImage X := by
    obtain ⟨P, hP, ⟨e⟩⟩ := exists_isKProjective_iso.{w, u, u} X
    exact ⟨⟨(HomotopyCategory.quotient A).obj P,
      (HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩, ⟨e.symm⟩⟩

/-- **`D(A)` is equivalent to the K-projective objects of `K(A)`.** -/
def kProjectiveEquivalence : KProjective A ≌ DerivedCategory.{w, u} A :=
  haveI : (kProjectiveFunctor.{w} A).IsEquivalence := { }
  (kProjectiveFunctor A).asEquivalence

end KProjective

variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ

variable [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]
  [HasDerivedCategory.{w, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)]

variable (A B) in
/-- **The derived external tensor product** `- ⊠ᴸ - : D(A) ⥤ D(B) ⥤ D(A ⊗ B)`, computed on
K-projective resolutions in both variables. -/
def externalTensor : DerivedCategory.{w, u} A ⥤ DerivedCategory.{w, u} B ⥤
    DerivedCategory.{w, u} AB :=
  (kProjectiveEquivalence.{w} A).inverse ⋙ (HomotopyCategory.subcategoryKProjective A).ι ⋙
    ExternalTensor.homotopyFunctor A B ⋙
      (Functor.whiskeringLeft _ _ _).obj
        ((kProjectiveEquivalence.{w} B).inverse ⋙ (HomotopyCategory.subcategoryKProjective B).ι) ⋙
      (Functor.whiskeringRight _ _ _).obj Qh

/-- On K-projective modules, `Q P ⊠ᴸ Q P' ≅ Q (P ⊠ P')`. -/
def externalTensorObjIso {P : DGModuleCat.{u} A} (hP : IsKProjective.{u} A P)
    {P' : DGModuleCat.{u} B} (hP' : IsKProjective.{u} B P') :
    ((externalTensor A B).obj (Q.obj P)).obj (Q.obj P') ≅
      Q.obj (((ExternalTensor.functor A B).obj P).obj P') :=
  let X : KProjective A := ⟨(HomotopyCategory.quotient A).obj P,
    (HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  let X' : KProjective B := ⟨(HomotopyCategory.quotient B).obj P',
    (HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P').mpr hP'⟩
  Qh.mapIso ((((ExternalTensor.homotopyFunctor A B).mapIso
      ((HomotopyCategory.subcategoryKProjective A).ι.mapIso
        ((kProjectiveEquivalence.{w} A).unitIso.app X).symm)).app _) ≪≫
    ((ExternalTensor.homotopyFunctor A B).obj X.obj).mapIso
      ((HomotopyCategory.subcategoryKProjective B).ι.mapIso
        ((kProjectiveEquivalence.{w} B).unitIso.app X').symm))

section Regular

/-- The external tensor product of the regular modules is the regular module of `A ⊗ B`:
`a ⊗ b ↦ a ⊗ b`, which is `A ⊗ B`-linear by the sign rules of both. -/
def regularTensorHom : (A ⊗[ℤ] B) →ᵈᵍ[AB] AB where
  toFun := _root_.GradedTensorProduct.of ℤ 𝒜 ℬ
  map_add' := map_add _
  map_smul' x y := by
    change _ = x * _
    induction x using GradedTensorProduct.induction_on_tmul (R := ℤ) with
    | zero => rw [ExternalTensor.zero_smul', map_zero, zero_mul]
    | add x x' hx hx' => rw [ExternalTensor.add_smul', map_add, hx, hx', add_mul]
    | @tmul i j a ha b hb =>
      induction y using DG.tensor_induction_on with
      | zero => rw [ExternalTensor.smul_zero', map_zero, mul_zero]
      | add y y' hy hy' => rw [ExternalTensor.smul_add', map_add, hy, hy', map_add, mul_add]
      | @tmul p q a' b' =>
        rw [ExternalTensor.tmul_smul_tmul a hb a'.2 (b' : B), smul_eq_mul, smul_eq_mul,
          Units.smul_def, map_zsmul]
        change _ = (a ᵍ⊗ₜ[ℤ] b : AB) * ((a' : A) ᵍ⊗ₜ[ℤ] (b' : B))
        rw [GradedTensorProduct.tmul_mul_tmul 𝒜 ℬ a hb a'.2 (b' : B), Units.smul_def]
  map_mem' {n x} hx := by
    simpa using map_mem_grading_of_tmul (M := A) (N := B)
      (_root_.GradedTensorProduct.of ℤ 𝒜 ℬ).toLinearMap.toAddMonoidHom 0
      (fun {i j a b} ha hb => by
        simpa using GradedTensorProduct.tmul_mem_grading (R := ℤ) ha hb) hx
  map_d' x := by
    induction x using DG.tensor_induction_on with
    | zero => simp
    | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]
    | @tmul i j a b =>
      rw [d_tmul_of_mem a.2]
      change _ = d ((a : A) ᵍ⊗ₜ[ℤ] (b : B) : AB)
      rw [GradedTensorProduct.d_tmul a.2 (b : B), map_add, Units.smul_def, map_zsmul,
        Units.smul_def]

omit [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]
  [HasDerivedCategory.{w, u} (DGAlgebra.gradingSubmodule ℤ A ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ B)] in
theorem regularTensorHom_bijective :
    Function.Bijective (regularTensorHom (A := A) (B := B)) :=
  (_root_.GradedTensorProduct.of ℤ 𝒜 ℬ).bijective

/-- `A ⊠ B ≅ A ⊗ B` as dg modules over `A ⊗ B`. -/
def regularTensorIso :
    ((ExternalTensor.functor A B).obj (DGModuleCat.of A A)).obj (DGModuleCat.of B B) ≅
      DGModuleCat.of AB AB :=
  @asIso _ _ _ _ (DGModuleCat.ofHom (regularTensorHom (A := A) (B := B)))
    (DGModuleCat.isIso_of_bijective _ regularTensorHom_bijective)

/-- **`A ⊠ᴸ B ≅ A ⊗ B`** in `D(A ⊗ B)`. -/
def externalTensorRegularIso :
    ((externalTensor A B).obj (Q.obj (DGModuleCat.of A A))).obj (Q.obj (DGModuleCat.of B B)) ≅
      Q.obj (DGModuleCat.of AB AB) :=
  externalTensorObjIso (isKProjective_self A) (isKProjective_self B) ≪≫ Q.mapIso regularTensorIso

end Regular

end DerivedCategory

end DG
