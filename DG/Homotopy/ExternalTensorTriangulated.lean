import DG.Module.ExternalTensorCone
import DG.Homotopy.Pretriangulated

/-!
# The external tensor product is triangulated in each variable

For dg rings `A`, `B` and `A ⊗ B = A ᵍ⊗[ℤ] B`, the external tensor product
`DG.ExternalTensor.functor : DGModuleCat A ⥤ DGModuleCat B ⥤ DGModuleCat (A ⊗ B)` commutes with
the shifts in each variable:

* `- ⊠ N` via `M⟦n⟧ ⊠ N ≅ (M ⊠ N)⟦n⟧`, `mk m ⊗ x ↦ mk (m ⊗ x)` (`DG.ExternalTensor.commShiftLeft`);
* `M ⊠ -` via `M ⊠ N⟦n⟧ ≅ (M ⊠ N)⟦n⟧`, `m ⊗ mk x ↦ (-1)^{n|m|} mk (m ⊗ x)`
  (`DG.ExternalTensor.commShiftRight`),

and these are `CommShift` structures (compatible with `M⟦0⟧ ≅ M` and `M⟦a + b⟧ ≅ M⟦a⟧⟦b⟧`). With
these, both functors send the standard triangle of a morphism to the standard triangle of its
image (`DG.ExternalTensor.mapTriangleLeftIso`, `DG.ExternalTensor.mapTriangleRightIso`, from the
cone isomorphisms `DG.ExternalTensor.coneLeftEquiv`, `DG.ExternalTensor.coneRightEquiv`).

Hence on homotopy categories, `X ⊠ -` and `- ⊠ Y` are triangulated functors for all
`X ∈ K(A)` and `Y ∈ K(B)` (instances for `(DG.ExternalTensor.homotopyFunctor A B).obj X` and
`(DG.ExternalTensor.homotopyFunctor A B).flip.obj Y`).
-/

open CategoryTheory Pretriangulated
open scoped TensorProduct

universe v u₁ u₂

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DG

namespace ExternalTensor

variable {A : Type u₁} {B : Type u₂} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B]
  [DGAddCommGroup B] [DGRing B]

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ A
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ B
local notation "AB" => 𝒜 ᵍ⊗[ℤ] ℬ

open DGModuleCat

/-! ### Extensionality on pure tensors -/

theorem dgHom_ext_tmul {M N X : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [DGModule A M] [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
    [AddCommGroup X] [DGAddCommGroup X] [Module AB X] [DGModule AB X]
    {φ ψ : (M ⊗[ℤ] N) →ᵈᵍ[AB] X}
    (h : ∀ {i : ℤ} (m : M), m ∈ grading i → ∀ n : N, φ (m ⊗ₜ n) = ψ (m ⊗ₜ n)) : φ = ψ :=
  DGModuleHom.ext fun x => by
    induction x using DG.tensor_induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m n => exact h m.1 m.2 n.1
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Morphisms out of `M ⊠ N` agree if they agree on `m ⊗ n` with `m` homogeneous. -/
theorem hom_ext_tmul {M : DGModuleCat.{v} A} {N : DGModuleCat.{v} B} {X : DGModuleCat.{v} AB}
    {f g : ((functor A B).obj M).obj N ⟶ X}
    (h : ∀ {i : ℤ} (m : M), m ∈ grading i → ∀ n : N, f (m ⊗ₜ n) = g (m ⊗ₜ n)) : f = g :=
  DGModuleCat.hom_ext (dgHom_ext_tmul (A := A) (B := B) (M := M) (N := N) h)

/-! ### The first variable -/

section Left

variable (N : DGModuleCat.{v} B)

/-- `M⟦n⟧ ⊠ N ≅ (M ⊠ N)⟦n⟧` in `DGModuleCat (A ⊗ B)` (`DG.ExternalTensor.shiftLeftEquiv`). -/
def shiftLeftIso (n : ℤ) (M : DGModuleCat.{v} A) :
    (shiftFunctor (DGModuleCat.{v} A) n ⋙ (functor A B).flip.obj N).obj M ≅
      ((functor A B).flip.obj N ⋙ shiftFunctor (DGModuleCat.{v} AB) n).obj M :=
  (shiftLeftEquiv (A := A) (B := B) M N n).toDGModuleCatIso

theorem shiftLeftIso_hom_tmul (n : ℤ) (M : DGModuleCat.{v} A) (m : M) (x : N) :
    (shiftLeftIso N n M).hom ((Shift.mk n m : Shift n M) ⊗ₜ x) = Shift.mk n (m ⊗ₜ x) := rfl

/-- **`- ⊠ N` commutes with the shifts**, via `M⟦n⟧ ⊠ N ≅ (M ⊠ N)⟦n⟧` (no sign). -/
instance commShiftLeft : ((functor A B).flip.obj N).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (shiftLeftIso N n) fun _ => hom_ext_tmul fun _ _ _ => rfl
  commShiftIso_zero := by
    ext M : 3
    rw [Functor.CommShift.isoZero_hom_app]
    exact hom_ext_tmul fun _ _ _ => rfl
  commShiftIso_add a b := by
    ext M : 3
    rw [Functor.CommShift.isoAdd_hom_app]
    exact hom_ext_tmul fun _ _ _ => rfl

theorem commShiftLeft_hom_app (n : ℤ) (M : DGModuleCat.{v} A) :
    (((functor A B).flip.obj N).commShiftIso n).hom.app M = (shiftLeftIso N n M).hom := rfl

variable {N}

/-- The image of the standard triangle of `φ` under `- ⊠ N` is the standard triangle of
`φ ⊠ 1` (`DG.ExternalTensor.coneLeftEquiv`). -/
def mapTriangleLeftIso {M M' : DGModuleCat.{v} A} (φ : M ⟶ M') :
    ((functor A B).flip.obj N).mapTriangle.obj (Cone.triangle φ) ≅
      Cone.triangle (((functor A B).flip.obj N).map φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (coneLeftEquiv (A := A) (B := B) (f := φ.hom) N).toDGModuleCatIso
    (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (hom_ext_tmul (M := M') (N := N) fun {i} m hm n => by
      change coneLeftAddEquiv (B := B) N φ.hom ((Cone.inr φ.hom m) ⊗ₜ n) =
        Cone.inr (tensorDGHom φ.hom (DGModuleHom.id : N →ᵈᵍ[B] N)) (m ⊗ₜ n)
      rw [coneLeftAddEquiv_tmul]
      refine Prod.ext ?_ rfl
      change shiftLeftAddEquiv M N 1 ((0 : Shift 1 M) ⊗ₜ n) = 0
      rw [TensorProduct.zero_tmul, map_zero])
    (hom_ext_tmul (M := DGModuleCat.of A (Cone φ.hom)) (N := N) fun {i} p hp n => by
      change shiftLeftAddEquiv M N 1 ((-Cone.fstHom φ.hom p) ⊗ₜ n) =
        Shift.mk 1 (Shift.unmk 1
          (-(Cone.fstHom (tensorDGHom φ.hom (DGModuleHom.id : N →ᵈᵍ[B] N))
            (coneLeftAddEquiv (B := B) N φ.hom (p ⊗ₜ n)))))
      rw [coneLeftAddEquiv_tmul, TensorProduct.neg_tmul, map_neg]
      rfl)

end Left

/-! ### The second variable -/

section Right

variable (M : DGModuleCat.{v} A)

/-- `M ⊠ N⟦n⟧ ≅ (M ⊠ N)⟦n⟧` in `DGModuleCat (A ⊗ B)` (`DG.ExternalTensor.shiftRightEquiv`). -/
def shiftRightIso (n : ℤ) (N : DGModuleCat.{v} B) :
    (shiftFunctor (DGModuleCat.{v} B) n ⋙ (functor A B).obj M).obj N ≅
      ((functor A B).obj M ⋙ shiftFunctor (DGModuleCat.{v} AB) n).obj N :=
  (shiftRightEquiv (A := A) (B := B) M N n).toDGModuleCatIso

/-- **`M ⊠ -` commutes with the shifts**, via `M ⊠ N⟦n⟧ ≅ (M ⊠ N)⟦n⟧`,
`m ⊗ mk x ↦ (-1)^{n|m|} mk (m ⊗ x)`. -/
instance commShiftRight : ((functor A B).obj M).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (shiftRightIso M n) fun {N N'} g =>
    DGModuleCat.hom_ext (dgHom_ext_tmul (A := A) (B := B) (M := (M : Type v))
      (N := Shift n (N : Type v)) fun {i} m hm x => by
      obtain ⟨x, rfl⟩ := Shift.mk_surjective x
      change shiftRightEquiv (A := A) (B := B) M N' n (m ⊗ₜ Shift.mk n (g x)) =
        Shift.mk n (tensorDGHom (DGModuleHom.id : M →ᵈᵍ[A] M) g.hom
          (Shift.unmk n (shiftRightEquiv (A := A) (B := B) M N n (m ⊗ₜ Shift.mk n x))))
      rw [shiftRightEquiv_tmul n hm, shiftRightEquiv_tmul n hm, Shift.unmk_units_smul,
        Shift.unmk_mk]
      simp only [Units.smul_def, map_zsmul]
      rfl)
  commShiftIso_zero := by
    ext N : 3
    rw [Functor.CommShift.isoZero_hom_app]
    refine DGModuleCat.hom_ext (dgHom_ext_tmul (A := A) (B := B) (M := (M : Type v))
      (N := Shift 0 (N : Type v)) fun {i} m hm x => ?_)
    obtain ⟨x, rfl⟩ := Shift.mk_surjective x
    change shiftRightEquiv (A := A) (B := B) M N 0 (m ⊗ₜ Shift.mk 0 x) = Shift.mk 0 (m ⊗ₜ x)
    rw [shiftRightEquiv_tmul 0 hm, mul_zero, koszulSign_zero, one_smul]
  commShiftIso_add a b := by
    ext N : 3
    rw [Functor.CommShift.isoAdd_hom_app]
    refine DGModuleCat.hom_ext (dgHom_ext_tmul (A := A) (B := B) (M := (M : Type v))
      (N := Shift (a + b) (N : Type v)) fun {i} m hm x => ?_)
    obtain ⟨x, rfl⟩ := Shift.mk_surjective x
    change shiftRightEquiv (A := A) (B := B) M N (a + b) (m ⊗ₜ Shift.mk (a + b) x) =
      Shift.mk (a + b) (Shift.unmk a (shiftRightEquiv (A := A) (B := B) M N a
        (Shift.unmk b (shiftRightEquiv (A := A) (B := B) M (Shift a (N : Type v)) b
          (m ⊗ₜ Shift.mk b (Shift.mk a x))))))
    rw [shiftRightEquiv_tmul b hm, Shift.unmk_units_smul, Shift.unmk_mk, Units.smul_def,
      map_zsmul, shiftRightEquiv_tmul a hm, Shift.unmk_zsmul, Shift.unmk_units_smul,
      Shift.unmk_mk, Shift.mk_zsmul, Shift.mk_units_smul, shiftRightEquiv_tmul (a + b) hm]
    simp only [Units.smul_def]
    rw [smul_smul, ← Units.val_mul, ← koszulSign_add, show i * b + i * a = i * (a + b) by ring]

theorem commShiftRight_hom_app (n : ℤ) (N : DGModuleCat.{v} B) :
    (((functor A B).obj M).commShiftIso n).hom.app N = (shiftRightIso M n N).hom := rfl

variable {M}

/-- The image of the standard triangle of `ψ` under `M ⊠ -` is the standard triangle of
`1 ⊠ ψ` (`DG.ExternalTensor.coneRightEquiv`). -/
def mapTriangleRightIso {N N' : DGModuleCat.{v} B} (ψ : N ⟶ N') :
    ((functor A B).obj M).mapTriangle.obj (Cone.triangle ψ) ≅
      Cone.triangle (((functor A B).obj M).map ψ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (coneRightEquiv (A := A) (B := B) (g := ψ.hom) M).toDGModuleCatIso
    (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (hom_ext_tmul (M := M) (N := N') fun {i} m hm n => by
      change coneRightAddEquiv (A := A) M ψ.hom (m ⊗ₜ (Cone.inr ψ.hom n)) =
        Cone.inr (tensorDGHom (DGModuleHom.id : M →ᵈᵍ[A] M) ψ.hom) (m ⊗ₜ n)
      rw [coneRightAddEquiv_tmul]
      refine Prod.ext ?_ rfl
      change shiftRightAddEquiv M N 1 (m ⊗ₜ (0 : Shift 1 N)) = 0
      rw [TensorProduct.tmul_zero, map_zero])
    (hom_ext_tmul (M := M) (N := DGModuleCat.of B (Cone ψ.hom)) fun {i} m hm q => by
      change shiftRightAddEquiv M N 1 (m ⊗ₜ (-Cone.fstHom ψ.hom q)) =
        Shift.mk 1 (Shift.unmk 1
          (-(Cone.fstHom (tensorDGHom (DGModuleHom.id : M →ᵈᵍ[A] M) ψ.hom)
            (coneRightAddEquiv (A := A) M ψ.hom (m ⊗ₜ q)))))
      rw [coneRightAddEquiv_tmul, TensorProduct.tmul_neg, map_neg]
      rfl)

end Right

/-! ### Homotopy categories -/

section Homotopy

variable (A B)

/-- `- ⊠ N` on homotopy categories. -/
def homotopyFunctorFlipObj (N : DGModuleCat.{v} B) :
    HomotopyCategory.{v} A ⥤ HomotopyCategory.{v} AB :=
  CategoryTheory.Quotient.lift _ ((functor A B).flip.obj N ⋙ HomotopyCategory.quotient AB)
    fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (homotopyLeft h)

/-- `(X ⊠ -) (N)` as a functor of `X`, computed by `homotopyFunctorFlipObj`. -/
def homotopyFunctorFlipObjIso (N : DGModuleCat.{v} B) :
    (homotopyFunctor A B).flip.obj ((HomotopyCategory.quotient B).obj N) ≅
      homotopyFunctorFlipObj A B N :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {X Y} f => by
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective f
    exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {A B}

/-- `- ⊠ N` commutes with the shifts on homotopy categories. -/
noncomputable instance homotopyFunctorFlipObj_commShift (N : DGModuleCat.{v} B) :
    (homotopyFunctorFlipObj A B N).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift ((functor A B).flip.obj N ⋙ HomotopyCategory.quotient AB)
    (DGModuleCat.homotopic.{v} A) ℤ _

instance (N : DGModuleCat.{v} B) :
    NatTrans.CommShift (CategoryTheory.Quotient.lift.isLift (DGModuleCat.homotopic.{v} A)
      ((functor A B).flip.obj N ⋙ HomotopyCategory.quotient AB)
      (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (homotopyLeft h))).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility _ _ ℤ _

/-- `- ⊠ N` is a triangulated functor `K(A) ⥤ K(A ⊗ B)`. -/
instance homotopyFunctorFlipObj_isTriangulated (N : DGModuleCat.{v} B) :
    (homotopyFunctorFlipObj A B N).IsTriangulated where
  map_distinguished := by
    rintro T ⟨M, M', φ, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(homotopyFunctorFlipObj A B N).mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
      (Functor.mapTriangleIso (CategoryTheory.Quotient.lift.isLift
        (DGModuleCat.homotopic.{v} A)
        ((functor A B).flip.obj N ⋙ HomotopyCategory.quotient AB)
        (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (homotopyLeft h)))).app _ ≪≫
      (Functor.mapTriangleCompIso _ _).app _ ≪≫
      (HomotopyCategory.quotient AB).mapTriangle.mapIso (mapTriangleLeftIso φ)⟩⟩

/-- `M ⊠ -` commutes with the shifts on homotopy categories. -/
noncomputable instance homotopyFunctorObj_commShift (M : DGModuleCat.{v} A) :
    (homotopyFunctorObj A B M).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift ((functor A B).obj M ⋙ HomotopyCategory.quotient AB)
    (DGModuleCat.homotopic.{v} B) ℤ _

instance (M : DGModuleCat.{v} A) :
    NatTrans.CommShift (CategoryTheory.Quotient.lift.isLift (DGModuleCat.homotopic.{v} B)
      ((functor A B).obj M ⋙ HomotopyCategory.quotient AB)
      (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (homotopyRight h))).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility _ _ ℤ _

/-- `M ⊠ -` is a triangulated functor `K(B) ⥤ K(A ⊗ B)`. -/
instance homotopyFunctorObj_isTriangulated (M : DGModuleCat.{v} A) :
    (homotopyFunctorObj A B M).IsTriangulated where
  map_distinguished := by
    rintro T ⟨N, N', ψ, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(homotopyFunctorObj A B M).mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
      (Functor.mapTriangleIso (CategoryTheory.Quotient.lift.isLift
        (DGModuleCat.homotopic.{v} B)
        ((functor A B).obj M ⋙ HomotopyCategory.quotient AB)
        (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (homotopyRight h)))).app _ ≪≫
      (Functor.mapTriangleCompIso _ _).app _ ≪≫
      (HomotopyCategory.quotient AB).mapTriangle.mapIso (mapTriangleRightIso ψ)⟩⟩

/-- **`X ⊠ -` commutes with the shifts** on homotopy categories, for every `X ∈ K(A)`. -/
noncomputable instance homotopyFunctor_obj_commShift (X : HomotopyCategory.{v} A) :
    ((homotopyFunctor A B).obj X).CommShift ℤ :=
  inferInstanceAs ((homotopyFunctorObj A B X.as).CommShift ℤ)

/-- **`X ⊠ -` is a triangulated functor** `K(B) ⥤ K(A ⊗ B)`, for every `X ∈ K(A)`. -/
instance homotopyFunctor_obj_isTriangulated (X : HomotopyCategory.{v} A) :
    ((homotopyFunctor A B).obj X).IsTriangulated :=
  inferInstanceAs (homotopyFunctorObj A B X.as).IsTriangulated

/-- **`- ⊠ Y` commutes with the shifts** on homotopy categories, for every `Y ∈ K(B)`. -/
noncomputable instance homotopyFunctor_flip_obj_commShift (Y : HomotopyCategory.{v} B) :
    ((homotopyFunctor A B).flip.obj Y).CommShift ℤ :=
  Functor.CommShift.ofIso (homotopyFunctorFlipObjIso A B Y.as).symm ℤ

instance (Y : HomotopyCategory.{v} B) :
    NatTrans.CommShift (homotopyFunctorFlipObjIso A B Y.as).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility _ ℤ

/-- **`- ⊠ Y` is a triangulated functor** `K(A) ⥤ K(A ⊗ B)`, for every `Y ∈ K(B)`. -/
instance homotopyFunctor_flip_obj_isTriangulated (Y : HomotopyCategory.{v} B) :
    ((homotopyFunctor A B).flip.obj Y).IsTriangulated :=
  Functor.isTriangulated_of_iso (homotopyFunctorFlipObjIso A B Y.as).symm

end Homotopy

end ExternalTensor

end DG
