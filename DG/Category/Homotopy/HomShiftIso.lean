import DG.Category.Homotopy.HomotopyShift
import DG.Module.HomShiftIso

/-!
# The Hom complex into a shift, for dg modules over a dg category

Let `C` be a dg category and `M`, `N` dg modules over `C`. This file identifies the Hom
complexes of shifted dg modules with shifts of the Hom complex, as dg abelian groups, and
describes the morphisms into a shift in the homotopy category. It is a port of
`DG.Module.HomShiftIso` and `DG.Homotopy.HomShift` (the case of a dg ring), with the same
names in the namespace `DG.CatModule` and the same signs.

## Main definitions

* `DG.CatModule.HOM.rightShiftEquiv M N a : HOM_C(M, N⟦a⟧) ≅ HOM_C(M, N)⟦a⟧`, sending a
  cochain `z` of degree `k` from `M` to `N⟦a⟧` to the same maps, viewed as a cochain of degree
  `k + a` from `M` to `N` (`DG.CatModule.Cochain.rightUnshift`, no sign);
* `DG.CatModule.HOM.leftShiftEquiv M N a : HOM_C(M⟦a⟧, N) ≅ HOM_C(M, N)⟦-a⟧`, given by
  `DG.CatModule.Cochain.leftUnshift` (with Mathlib's sign `(-1)^{a n' + a (a - 1) / 2}`).

Both are isomorphisms of dg abelian groups (`DG.DGAddEquiv`): the shift `DG.Shift a` of a dg
abelian group has differential `(-1)^a d`, and the differential of the Hom complex commutes
with `rightUnshift` and `leftUnshift` up to the same sign (`DG.CatModule.Cochain.δ_rightUnshift`,
`DG.CatModule.Cochain.δ_leftUnshift`).

## Consequences

* `DG.CatModule.HOM.cohomologyRightShiftAddEquiv : Hᵏ(HOM_C(M, N⟦a⟧)) ≃+ Hˡ(HOM_C(M, N))` and
  `DG.CatModule.HOM.cohomologyLeftShiftAddEquiv : Hᵏ(HOM_C(M⟦a⟧, N)) ≃+ Hˡ(HOM_C(M, N))`;
* `DG.CatModule.Cocycle.homShiftAddEquiv M N n : (M ⟶ N⟦n⟧) ≃+ Cocycle M N n` and
  `DG.CatModule.HOM.homShiftAddEquivCocycles : (M ⟶ N⟦n⟧) ≃+ Zⁿ(HOM_C(M, N))`;
* `DG.CatModule.HomotopyCategory.homShiftAddEquivCohomology M N n :
    Hom_{H(C)}(M, N⟦n⟧) ≃+ Hⁿ(HOM_C(M, N))`, sending the class of a morphism of dg modules
  `f : M → N⟦n⟧` to the class of the `n`-cocycle `f`
  (`DG.CatModule.HomotopyCategory.homShiftAddEquivCohomology_quotient_map`).
-/

open CategoryTheory DirectSum

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

namespace HOM

variable (M N : CatModule.{w} C)

section Right

variable (a : ℤ)

/-- The additive map `HOM_C(M, N⟦a⟧) → HOM_C(M, N)⟦a⟧`, `Cochain.rightUnshift` on each
summand. -/
noncomputable def rightShiftAddHom : HOM M (shift a N) →+ Shift a (HOM M N) :=
  (Shift.mk a).toAddMonoidHom.comp (DirectSum.toAddMonoid fun k =>
    (DirectSum.of (fun n => Cochain M N n) (k + a)).comp
      (Cochain.rightShiftAddEquiv M N (k + a) a k rfl).symm.toAddMonoidHom)

/-- The additive map `HOM_C(M, N)⟦a⟧ → HOM_C(M, N⟦a⟧)`, `Cochain.rightShift` on each
summand. -/
noncomputable def rightUnshiftAddHom : Shift a (HOM M N) →+ HOM M (shift a N) :=
  (DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun k => Cochain M (shift a N) k) (n - a)).comp
      (Cochain.rightShiftAddEquiv M N n a (n - a) (sub_add_cancel n a)).toAddMonoidHom).comp
    (Shift.unmk a).toAddMonoidHom

variable {M N a}

theorem rightShiftAddHom_of (k : ℤ) (z : Cochain M (shift a N) k) :
    rightShiftAddHom M N a (DirectSum.of _ k z) =
      Shift.mk a (DirectSum.of _ (k + a) (z.rightUnshift (k + a) rfl)) := by
  simp [rightShiftAddHom]

theorem rightUnshiftAddHom_mk_of (n : ℤ) (z : Cochain M N n) :
    rightUnshiftAddHom M N a (Shift.mk a (DirectSum.of _ n z)) =
      DirectSum.of _ (n - a) (z.rightShift a (n - a) (sub_add_cancel n a)) := by
  simp [rightUnshiftAddHom]

variable (M N a)

/-- `HOM_C(M, N⟦a⟧) ≅ HOM_C(M, N)⟦a⟧` as dg abelian groups: a cochain of degree `k` from `M`
to `N⟦a⟧` is the same family of maps viewed as a cochain of degree `k + a` from `M` to `N`
(`DG.CatModule.Cochain.rightUnshift`). -/
noncomputable def rightShiftEquiv : DGAddEquiv (HOM M (shift a N)) (Shift a (HOM M N)) :=
  DGAddEquiv.ofAddMonoidHom (rightShiftAddHom M N a) (rightUnshiftAddHom M N a)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of k z =>
        rw [rightShiftAddHom_of, rightUnshiftAddHom_mk_of]
        exact of_congr (add_sub_cancel_right k a) fun _ _ => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun x => by
      obtain ⟨x, rfl⟩ := Shift.mk_surjective x
      induction x using DirectSum.induction_on with
      | zero => simp
      | of n z =>
        rw [rightUnshiftAddHom_mk_of, rightShiftAddHom_of]
        exact congrArg (Shift.mk a) (of_congr (sub_add_cancel n a) fun _ _ => rfl)
      | add x y hx hy => rw [Shift.mk_add, map_add, map_add, hx, hy])
    (by
      rintro k _ ⟨z, rfl⟩
      rw [rightShiftAddHom_of]
      exact of_mem_summand _ _)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of k z =>
        rw [d_of, rightShiftAddHom_of, rightShiftAddHom_of, Shift.d_mk, d_of,
          Cochain.δ_rightUnshift z (k + a) rfl (k + a + 1) (k + 1) (by omega), of_units_smul,
          smul_smul, Int.units_mul_self, one_smul]
        exact congrArg (Shift.mk a) (of_congr (by omega) fun _ _ => rfl)
      | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add])

@[simp]
theorem rightShiftEquiv_of (k : ℤ) (z : Cochain M (shift a N) k) :
    rightShiftEquiv M N a (DirectSum.of _ k z) =
      Shift.mk a (DirectSum.of _ (k + a) (z.rightUnshift (k + a) rfl)) :=
  rightShiftAddHom_of k z

@[simp]
theorem rightShiftEquiv_symm_mk_of (n : ℤ) (z : Cochain M N n) :
    (rightShiftEquiv M N a).symm (Shift.mk a (DirectSum.of _ n z)) =
      DirectSum.of _ (n - a) (z.rightShift a (n - a) (sub_add_cancel n a)) :=
  rightUnshiftAddHom_mk_of n z

end Right

section Left

variable (a : ℤ)

/-- The additive map `HOM_C(M⟦a⟧, N) → HOM_C(M, N)⟦-a⟧`, `Cochain.leftUnshift` on each
summand. -/
noncomputable def leftShiftAddHom : HOM (shift a M) N →+ Shift (-a) (HOM M N) :=
  (Shift.mk (-a)).toAddMonoidHom.comp (DirectSum.toAddMonoid fun k =>
    (DirectSum.of (fun n => Cochain M N n) (k + -a)).comp
      (Cochain.leftShiftAddEquiv M N (k + -a) a k (neg_add_cancel_right k a)).symm.toAddMonoidHom)

/-- The additive map `HOM_C(M, N)⟦-a⟧ → HOM_C(M⟦a⟧, N)`, `Cochain.leftShift` on each
summand. -/
noncomputable def leftUnshiftAddHom : Shift (-a) (HOM M N) →+ HOM (shift a M) N :=
  (DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun k => Cochain (shift a M) N k) (n + a)).comp
      (Cochain.leftShiftAddEquiv M N n a (n + a) rfl).toAddMonoidHom).comp
    (Shift.unmk (-a)).toAddMonoidHom

variable {M N a}

theorem leftShiftAddHom_of (k : ℤ) (z : Cochain (shift a M) N k) :
    leftShiftAddHom M N a (DirectSum.of _ k z) =
      Shift.mk (-a)
        (DirectSum.of _ (k + -a) (z.leftUnshift (k + -a) (neg_add_cancel_right k a))) := by
  simp [leftShiftAddHom]

theorem leftUnshiftAddHom_mk_of (n : ℤ) (z : Cochain M N n) :
    leftUnshiftAddHom M N a (Shift.mk (-a) (DirectSum.of _ n z)) =
      DirectSum.of _ (n + a) (z.leftShift a (n + a) rfl) := by
  simp [leftUnshiftAddHom]

variable (M N a)

/-- `HOM_C(M⟦a⟧, N) ≅ HOM_C(M, N)⟦-a⟧` as dg abelian groups: a cochain of degree `k` from
`M⟦a⟧` to `N` corresponds to the cochain `DG.CatModule.Cochain.leftUnshift` of degree `k - a`
from `M` to `N` (Mathlib's sign `(-1)^{a k + a (a - 1) / 2}`). -/
noncomputable def leftShiftEquiv : DGAddEquiv (HOM (shift a M) N) (Shift (-a) (HOM M N)) :=
  DGAddEquiv.ofAddMonoidHom (leftShiftAddHom M N a) (leftUnshiftAddHom M N a)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of k z =>
        rw [leftShiftAddHom_of, leftUnshiftAddHom_mk_of]
        refine of_congr (neg_add_cancel_right k a) fun X x => ?_
        obtain ⟨x, rfl⟩ := shift.mk_surjective x
        simp only [Cochain.leftShift_apply_mk, Cochain.leftUnshift_apply, neg_add_cancel_right,
          smul_smul, Int.units_mul_self, one_smul]
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun x => by
      obtain ⟨x, rfl⟩ := Shift.mk_surjective x
      induction x using DirectSum.induction_on with
      | zero => simp
      | of n z =>
        rw [leftUnshiftAddHom_mk_of, leftShiftAddHom_of]
        exact congrArg (Shift.mk (-a)) (of_congr (add_neg_cancel_right n a) fun X x => by
          rw [Cochain.leftUnshift_apply, Cochain.leftShift_apply_mk, smul_smul,
            Int.units_mul_self, one_smul])
      | add x y hx hy => rw [Shift.mk_add, map_add, map_add, hx, hy])
    (by
      rintro k _ ⟨z, rfl⟩
      rw [leftShiftAddHom_of]
      exact of_mem_summand _ _)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of k z =>
        rw [d_of, leftShiftAddHom_of, leftShiftAddHom_of, Shift.d_mk, d_of,
          Cochain.δ_leftUnshift z (k + -a) (neg_add_cancel_right k a) (k + -a + 1) (k + 1) (by omega),
          of_units_smul, smul_smul, koszulSign, Int.negOnePow_neg, ← koszulSign,
          Int.units_mul_self, one_smul]
        exact congrArg (Shift.mk (-a)) (of_congr (by omega) fun _ _ => rfl)
      | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add])

@[simp]
theorem leftShiftEquiv_of (k : ℤ) (z : Cochain (shift a M) N k) :
    leftShiftEquiv M N a (DirectSum.of _ k z) =
      Shift.mk (-a) (DirectSum.of _ (k + -a) (z.leftUnshift (k + -a) (neg_add_cancel_right k a))) :=
  leftShiftAddHom_of k z

@[simp]
theorem leftShiftEquiv_symm_mk_of (n : ℤ) (z : Cochain M N n) :
    (leftShiftEquiv M N a).symm (Shift.mk (-a) (DirectSum.of _ n z)) =
      DirectSum.of _ (n + a) (z.leftShift a (n + a) rfl) :=
  leftUnshiftAddHom_mk_of n z

end Left

/-- `Hᵏ(HOM_C(M, N⟦a⟧)) ≃+ Hˡ(HOM_C(M, N))` for `k + a = l`. -/
noncomputable def cohomologyRightShiftAddEquiv (a k l : ℤ) (h : k + a = l) :
    cohomology (HOM M (shift a N)) k ≃+ cohomology (HOM M N) l :=
  ((rightShiftEquiv M N a).cohomologyAddEquiv k).trans (cohomology.shiftAddEquiv _ a k l h)

/-- `Hᵏ(HOM_C(M⟦a⟧, N)) ≃+ Hˡ(HOM_C(M, N))` for `k = l + a`. -/
noncomputable def cohomologyLeftShiftAddEquiv (a k l : ℤ) (h : k + -a = l) :
    cohomology (HOM (shift a M) N) k ≃+ cohomology (HOM M N) l :=
  ((leftShiftEquiv M N a).cohomologyAddEquiv k).trans (cohomology.shiftAddEquiv _ (-a) k l h)

end HOM

/-! ### Morphisms into a shift -/

namespace Cocycle

variable (M N : CatModule.{w} C)

/-- Morphisms of dg modules `M → N⟦n⟧` are the `n`-cocycles of `HOM_C(M, N)`: a morphism is
sent to the same family of maps, viewed as a cochain of degree `n` from `M` to `N`. -/
def homShiftAddEquiv (n : ℤ) : (M ⟶ CatModule.shift n N) ≃+ Cocycle M N n :=
  (Cocycle.equivHom M (CatModule.shift n N)).trans
    { toFun := fun z => ⟨(z : Cochain M (CatModule.shift n N) 0).rightUnshift n (zero_add n), by
        rw [mem_iff (n + 1) rfl, Cochain.δ_rightUnshift _ n (zero_add n) (n + 1) 1 (by omega),
          δ_eq_zero, Cochain.rightUnshift_zero, _root_.smul_zero]⟩
      invFun := fun z => ⟨(z : Cochain M N n).rightShift n 0 (zero_add n), by
        rw [mem_iff 1 (zero_add 1), Cochain.δ_rightShift _ n 0 1 (zero_add n) (n + 1) (by omega), δ_eq_zero,
          Cochain.rightShift_zero, _root_.smul_zero]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

variable {M N}

@[simp]
theorem homShiftAddEquiv_apply (n : ℤ) (f : M ⟶ CatModule.shift n N) {X : C} (x : M.obj X) :
    (homShiftAddEquiv M N n f : Cochain M N n).app X x = shift.unmk n (f.app X x) := rfl

@[simp]
theorem homShiftAddEquiv_symm_apply (n : ℤ) (z : Cocycle M N n) {X : C} (x : M.obj X) :
    ((homShiftAddEquiv M N n).symm z).app X x = shift.mk n ((z : Cochain M N n).app X x) := rfl

end Cocycle

namespace HOM

variable (M N : CatModule.{w} C)

/-- Morphisms of dg modules `M → N⟦n⟧` are the `n`-cocycles of the Hom complex `HOM_C(M, N)`
(as a dg abelian group). -/
noncomputable def homShiftAddEquivCocycles (n : ℤ) :
    (M ⟶ shift n N) ≃+ cocycles (HOM M N) n :=
  (Cocycle.homShiftAddEquiv M N n).trans (cocyclesAddEquiv M N n)

@[simp]
theorem coe_homShiftAddEquivCocycles_apply (n : ℤ) (f : M ⟶ shift n N) :
    (homShiftAddEquivCocycles M N n f : HOM M N) =
      DirectSum.of (fun k => Cochain M N k) n (Cocycle.homShiftAddEquiv M N n f) :=
  rfl

end HOM

/-! ### Morphisms into a shift in the homotopy category -/

namespace HomotopyCategory

variable (M N : CatModule.{w} C)

/-- Composition with an isomorphism, as an additive equivalence of Hom groups (auxiliary). -/
private def compIsoAddEquiv {X Y Z : HomotopyCategory.{w} C} (e : Y ≅ Z) :
    (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := Preadditive.add_comp _ _ _ _ _ _

/-- `Hom_{H(C)}(M, N⟦n⟧) ≃+ Hⁿ(HOM_C(M, N))`: morphisms into a shift in the homotopy category
are the cohomology of the Hom complex. -/
noncomputable def homShiftAddEquivCohomology (n : ℤ) :
    ((quotient C).obj M ⟶ ((quotient C).obj N)⟦n⟧) ≃+ cohomology (HOM M N) n :=
  (compIsoAddEquiv (((quotient C).commShiftIso n).app N)).symm.trans
    ((homAddEquivCohomology M ((shiftFunctor (CatModule.{w} C) n).obj N)).trans
      (HOM.cohomologyRightShiftAddEquiv M N n 0 n (zero_add n)))

/-- `DG.CatModule.HomotopyCategory.homShiftAddEquivCohomology` sends the class of a morphism of
dg modules `f : M → N⟦n⟧` to the class of the `n`-cocycle `f` of `HOM_C(M, N)`. -/
theorem homShiftAddEquivCohomology_quotient_map (n : ℤ)
    (f : M ⟶ (shiftFunctor (CatModule.{w} C) n).obj N) :
    homShiftAddEquivCohomology M N n
        ((quotient C).map f ≫ ((quotient C).commShiftIso n).hom.app N) =
      cohomology.mk _ n (HOM.homShiftAddEquivCocycles M N n f) := by
  have h : (compIsoAddEquiv (((quotient C).commShiftIso n).app N)).symm
      ((quotient C).map f ≫ ((quotient C).commShiftIso n).hom.app N) = (quotient C).map f := by
    change ((quotient C).map f ≫ ((quotient C).commShiftIso n).hom.app N) ≫
      ((quotient C).commShiftIso n).inv.app N = _
    exact (Category.assoc _ _ _).trans
      ((congrArg _ (Iso.hom_inv_id_app _ _)).trans (Category.comp_id _))
  rw [homShiftAddEquivCohomology, AddEquiv.trans_apply]
  erw [AddEquiv.trans_apply, h]
  refine (congrArg (HOM.cohomologyRightShiftAddEquiv M N n 0 n (zero_add n))
    (homAddEquivCohomology_quotient_map M ((shiftFunctor (CatModule.{w} C) n).obj N) f)).trans
    ?_
  refine congrArg (cohomology.mk _ n) (Subtype.ext ?_)
  refine (congrArg (Shift.unmk n)
    (HOM.rightShiftEquiv_of M N n 0 (Cochain.ofHom f))).trans ?_
  exact HOM.of_congr (zero_add n)
    (f := Cochain.rightUnshift (N := N) (a := n) (Cochain.ofHom f) (0 + n) rfl)
    (g := (Cocycle.homShiftAddEquiv M N n f : Cochain M N n)) fun _ _ => rfl

end HomotopyCategory

end CatModule

end DG
