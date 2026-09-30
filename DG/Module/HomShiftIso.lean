import DG.Algebra.AddEquiv
import DG.Module.Cohomology
import DG.Module.HomShift

/-!
# The Hom complex into a shift

Let `A` be a dg ring and `M`, `N` dg `A`-modules. This file identifies the Hom complexes of
shifted dg modules with shifts of the Hom complex, as dg abelian groups:

* `DG.DGModule.HOM.rightShiftEquiv A M N a : HOM_A(M, N⟦a⟧) ≅ HOM_A(M, N)⟦a⟧`, sending a
  cochain `z` of degree `k` from `M` to `N⟦a⟧` to the same map, viewed as a cochain of degree
  `k + a` from `M` to `N` (`DG.Cochain.rightUnshift`, no sign);
* `DG.DGModule.HOM.leftShiftEquiv A M N a : HOM_A(M⟦a⟧, N) ≅ HOM_A(M, N)⟦-a⟧`, given by
  `DG.Cochain.leftUnshift` (with Mathlib's sign `(-1)^{a n' + a (a - 1) / 2}`).

Both are isomorphisms of dg abelian groups (`DG.DGAddEquiv`): of degree `0` and compatible with
the differentials. The shift of a dg abelian group has differential `(-1)^a d`
(`DG.Shift`), and the differential of the Hom complex commutes with `Cochain.rightUnshift` and
`Cochain.leftUnshift` up to the same sign `(-1)^a` (`DG.Cochain.δ_rightUnshift`,
`DG.Cochain.δ_leftUnshift`), so no further sign is needed.

Consequences on cocycles and cohomology:

* `DG.DGAddEquiv.cohomologyAddEquiv e n : Hⁿ(M) ≃+ Hⁿ(N)` for an isomorphism `e` of dg abelian
  groups, and `DG.cohomology.shiftAddEquiv X a k l : Hᵏ(X⟦a⟧) ≃+ Hˡ(X)` for `k + a = l`;
* `DG.DGModule.HOM.cohomologyRightShiftAddEquiv : Hᵏ(HOM_A(M, N⟦a⟧)) ≃+ Hˡ(HOM_A(M, N))` for
  `k + a = l`;
* `DG.Cocycle.homShiftAddEquiv A M N n : (M →ᵈᵍ[A] N⟦n⟧) ≃+ Cocycle A M N n`: morphisms of dg
  modules into `N⟦n⟧` are the `n`-cocycles of `HOM_A(M, N)`.
-/

open DirectSum

namespace DG

/-! ### Cohomology of isomorphic and of shifted dg abelian groups -/

namespace DGAddEquiv

variable {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of dg abelian groups induces isomorphisms on cohomology. -/
def cohomologyAddEquiv (e : DGAddEquiv M N) (n : ℤ) : cohomology M n ≃+ cohomology N n where
  toFun := cohomology.mapAddMonoidHom e.toAddEquiv.toAddMonoidHom e.map_mem' e.map_d' n
  invFun := cohomology.mapAddMonoidHom e.symm.toAddEquiv.toAddMonoidHom e.symm.map_mem'
    e.symm.map_d' n
  left_inv x := by
    induction x using cohomology.induction_on with
    | h z =>
      rw [cohomology.mapAddMonoidHom_mk, cohomology.mapAddMonoidHom_mk]
      exact congrArg _ (Subtype.ext (e.symm_apply_apply (z : M)))
  right_inv x := by
    induction x using cohomology.induction_on with
    | h z =>
      rw [cohomology.mapAddMonoidHom_mk, cohomology.mapAddMonoidHom_mk]
      exact congrArg _ (Subtype.ext (e.apply_symm_apply (z : N)))
  map_add' := map_add _

@[simp]
theorem cohomologyAddEquiv_mk (e : DGAddEquiv M N) (n : ℤ) (z : cocycles M n) :
    e.cohomologyAddEquiv n (cohomology.mk M n z) =
      cohomology.mk N n ⟨e z, e.map_mem z.2.1,
        show d (e (z : M)) = 0 by rw [← map_d, cocycles.d_eq_zero z, map_zero]⟩ :=
  cohomology.mapAddMonoidHom_mk e.toAddEquiv.toAddMonoidHom e.map_mem' e.map_d' n z

end DGAddEquiv

namespace cohomology

open Shift

variable (X : Type*) [AddCommGroup X] [DGAddCommGroup X]

variable {X} in
theorem d_unmk_eq_zero_iff (a : ℤ) (x : Shift a X) : d (unmk a x) = 0 ↔ d x = 0 := by
  constructor
  · intro h
    apply (unmk a).injective
    rw [unmk_d, h, smul_zero, unmk_zero]
  · intro h
    have h' := congrArg (unmk a) h
    rw [unmk_d, unmk_zero] at h'
    simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using
      congrArg (koszulSign a • ·) h'

/-- The cocycles of `X⟦a⟧` in degree `k` are the cocycles of `X` in degree `l = k + a`. -/
def shiftCocyclesAddEquiv (a k l : ℤ) (h : k + a = l) :
    cocycles (Shift a X) k ≃+ cocycles X l where
  toFun z := ⟨unmk a z, h ▸ z.2.1, (d_unmk_eq_zero_iff a _).mpr z.2.2⟩
  invFun z := ⟨Shift.mk a z, (h ▸ z.2.1 : (z : X) ∈ grading (k + a)),
    (d_unmk_eq_zero_iff a _).mp z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {X} in
theorem shiftCocyclesAddEquiv_mem_coboundaries_iff (a k l : ℤ) (h : k + a = l)
    (z : cocycles (Shift a X) k) :
    (shiftCocyclesAddEquiv X a k l h z : X) ∈ coboundaries X l ↔
      (z : Shift a X) ∈ coboundaries (Shift a X) k := by
  constructor
  · rintro ⟨y, hy, hyz⟩
    refine ⟨Shift.mk a (koszulSign a • y), ?_, ?_⟩
    · refine Shift.mem_grading_iff.mpr ?_
      convert units_smul_mem_grading (koszulSign a) hy using 2
      omega
    · rw [d_mk, d_units_smul, smul_smul, Int.units_mul_self, one_smul, hyz]
      rfl
  · rintro ⟨y, hy, hyz⟩
    refine ⟨koszulSign a • unmk a y, ?_, ?_⟩
    · have h' := units_smul_mem_grading (koszulSign a) (unmk_mem_grading hy)
      rwa [show k - 1 + a = l - 1 by omega] at h'
    · rw [d_units_smul, ← unmk_d, hyz]
      rfl

/-- `Hᵏ(X⟦a⟧) ≃+ Hˡ(X)` for `k + a = l`, induced by the identity of the underlying groups. -/
def shiftAddEquiv (a k l : ℤ) (h : k + a = l) : cohomology (Shift a X) k ≃+ cohomology X l :=
  QuotientAddGroup.congr _ _ (shiftCocyclesAddEquiv X a k l h) (by
    ext z
    rw [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (shiftCocyclesAddEquiv_mem_coboundaries_iff a k l h y).mpr
        (AddSubgroup.mem_addSubgroupOf.mp hy)
    · intro hz
      obtain ⟨y, rfl⟩ := (shiftCocyclesAddEquiv X a k l h).surjective z
      exact ⟨y, AddSubgroup.mem_addSubgroupOf.mpr
        ((shiftCocyclesAddEquiv_mem_coboundaries_iff a k l h y).mp hz), rfl⟩)

variable {X} in
@[simp]
theorem shiftAddEquiv_mk (a k l : ℤ) (h : k + a = l) (z : cocycles (Shift a X) k) :
    shiftAddEquiv X a k l h (mk _ k z) = mk X l (shiftCocyclesAddEquiv X a k l h z) :=
  rfl

end cohomology

/-! ### The Hom complex into a shift -/

namespace DGModule.HOM

open Shift Cochain

variable (A : Type*) (M N : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

section Right

variable (a : ℤ)

/-- The additive map `HOM_A(M, N⟦a⟧) → HOM_A(M, N)⟦a⟧`, `Cochain.rightUnshift` on each
summand. -/
noncomputable def rightShiftAddHom : HOM A M (Shift a N) →+ Shift a (HOM A M N) :=
  (Shift.mk a).toAddMonoidHom.comp (DirectSum.toAddMonoid fun k =>
    (DirectSum.of (fun n => Cochain A M N n) (k + a)).comp
      (rightShiftAddEquiv A M N (k + a) a k rfl).symm.toAddMonoidHom)

/-- The additive map `HOM_A(M, N)⟦a⟧ → HOM_A(M, N⟦a⟧)`, `Cochain.rightShift` on each
summand. -/
noncomputable def rightUnshiftAddHom : Shift a (HOM A M N) →+ HOM A M (Shift a N) :=
  (DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun k => Cochain A M (Shift a N) k) (n - a)).comp
      (rightShiftAddEquiv A M N n a (n - a) (sub_add_cancel n a)).toAddMonoidHom).comp
    (unmk a).toAddMonoidHom

variable {A M N a}

omit [DGModule A M] [DGModule A N] in
theorem rightShiftAddHom_of (k : ℤ) (z : Cochain A M (Shift a N) k) :
    rightShiftAddHom A M N a (DirectSum.of _ k z) =
      Shift.mk a (DirectSum.of _ (k + a) (z.rightUnshift (k + a) rfl)) := by
  simp [rightShiftAddHom]

omit [DGModule A M] [DGModule A N] in
theorem rightUnshiftAddHom_mk_of (n : ℤ) (z : Cochain A M N n) :
    rightUnshiftAddHom A M N a (Shift.mk a (DirectSum.of _ n z)) =
      DirectSum.of _ (n - a) (z.rightShift a (n - a) (sub_add_cancel n a)) := by
  simp [rightUnshiftAddHom]

variable (A M N a)

/-- `HOM_A(M, N⟦a⟧) ≅ HOM_A(M, N)⟦a⟧` as dg abelian groups: a cochain of degree `k` from `M`
to `N⟦a⟧` is the same map viewed as a cochain of degree `k + a` from `M` to `N`
(`DG.Cochain.rightUnshift`). -/
noncomputable def rightShiftEquiv : DGAddEquiv (HOM A M (Shift a N)) (Shift a (HOM A M N)) :=
  DGAddEquiv.ofAddMonoidHom (rightShiftAddHom A M N a) (rightUnshiftAddHom A M N a)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of k z =>
        rw [rightShiftAddHom_of, rightUnshiftAddHom_mk_of]
        exact of_congr (add_sub_cancel_right k a) fun _ => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun x => by
      obtain ⟨x, rfl⟩ := Shift.mk_surjective x
      induction x using DirectSum.induction_on with
      | zero => simp
      | of n z =>
        rw [rightUnshiftAddHom_mk_of, rightShiftAddHom_of]
        exact congrArg (Shift.mk a) (of_congr (sub_add_cancel n a) fun _ => rfl)
      | add x y hx hy => rw [mk_add, map_add, map_add, hx, hy])
    (by
      rintro k _ ⟨z, rfl⟩
      rw [rightShiftAddHom_of]
      exact of_mem_summand _ _)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of k z =>
        rw [d_of, rightShiftAddHom_of, rightShiftAddHom_of, d_mk, d_of,
          δ_rightUnshift z (k + a) rfl (k + a + 1) (k + 1) (by omega), of_units_smul,
          smul_smul, Int.units_mul_self, one_smul]
        exact congrArg (Shift.mk a) (of_congr (by omega) fun _ => rfl)
      | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add])

@[simp]
theorem rightShiftEquiv_of (k : ℤ) (z : Cochain A M (Shift a N) k) :
    rightShiftEquiv A M N a (DirectSum.of _ k z) =
      Shift.mk a (DirectSum.of _ (k + a) (z.rightUnshift (k + a) rfl)) :=
  rightShiftAddHom_of k z

@[simp]
theorem rightShiftEquiv_symm_mk_of (n : ℤ) (z : Cochain A M N n) :
    (rightShiftEquiv A M N a).symm (Shift.mk a (DirectSum.of _ n z)) =
      DirectSum.of _ (n - a) (z.rightShift a (n - a) (sub_add_cancel n a)) :=
  rightUnshiftAddHom_mk_of n z

end Right

section Left

variable (a : ℤ)

/-- The additive map `HOM_A(M⟦a⟧, N) → HOM_A(M, N)⟦-a⟧`, `Cochain.leftUnshift` on each
summand. -/
noncomputable def leftShiftAddHom : HOM A (Shift a M) N →+ Shift (-a) (HOM A M N) :=
  (Shift.mk (-a)).toAddMonoidHom.comp (DirectSum.toAddMonoid fun k =>
    (DirectSum.of (fun n => Cochain A M N n) (k + -a)).comp
      (leftShiftAddEquiv A M N (k + -a) a k (neg_add_cancel_right k a)).symm.toAddMonoidHom)

/-- The additive map `HOM_A(M, N)⟦-a⟧ → HOM_A(M⟦a⟧, N)`, `Cochain.leftShift` on each
summand. -/
noncomputable def leftUnshiftAddHom : Shift (-a) (HOM A M N) →+ HOM A (Shift a M) N :=
  (DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun k => Cochain A (Shift a M) N k) (n + a)).comp
      (leftShiftAddEquiv A M N n a (n + a) rfl).toAddMonoidHom).comp
    (unmk (-a)).toAddMonoidHom

variable {A M N a}

omit [DGModule A M] [DGModule A N] in
theorem leftShiftAddHom_of (k : ℤ) (z : Cochain A (Shift a M) N k) :
    leftShiftAddHom A M N a (DirectSum.of _ k z) =
      Shift.mk (-a)
        (DirectSum.of _ (k + -a) (z.leftUnshift (k + -a) (neg_add_cancel_right k a))) := by
  simp [leftShiftAddHom]

omit [DGModule A M] [DGModule A N] in
theorem leftUnshiftAddHom_mk_of (n : ℤ) (z : Cochain A M N n) :
    leftUnshiftAddHom A M N a (Shift.mk (-a) (DirectSum.of _ n z)) =
      DirectSum.of _ (n + a) (z.leftShift a (n + a) rfl) := by
  simp [leftUnshiftAddHom]

variable (A M N a)

/-- `HOM_A(M⟦a⟧, N) ≅ HOM_A(M, N)⟦-a⟧` as dg abelian groups: a cochain of degree `k` from
`M⟦a⟧` to `N` corresponds to the cochain `DG.Cochain.leftUnshift` of degree `k - a` from `M` to
`N` (Mathlib's sign `(-1)^{a k + a (a - 1) / 2}`). -/
noncomputable def leftShiftEquiv : DGAddEquiv (HOM A (Shift a M) N) (Shift (-a) (HOM A M N)) :=
  DGAddEquiv.ofAddMonoidHom (leftShiftAddHom A M N a) (leftUnshiftAddHom A M N a)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of k z =>
        rw [leftShiftAddHom_of, leftUnshiftAddHom_mk_of]
        exact of_congr (neg_add_cancel_right k a) fun x => by
          simp only [leftShift_apply, leftUnshift_apply, neg_add_cancel_right, mk_unmk, smul_smul,
            Int.units_mul_self, one_smul]
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun x => by
      obtain ⟨x, rfl⟩ := Shift.mk_surjective x
      induction x using DirectSum.induction_on with
      | zero => simp
      | of n z =>
        rw [leftUnshiftAddHom_mk_of, leftShiftAddHom_of]
        exact congrArg (Shift.mk (-a)) (of_congr (add_neg_cancel_right n a) fun x => by
          simp only [leftShift_apply, leftUnshift_apply, unmk_mk, smul_smul, Int.units_mul_self,
            one_smul])
      | add x y hx hy => rw [mk_add, map_add, map_add, hx, hy])
    (by
      rintro k _ ⟨z, rfl⟩
      rw [leftShiftAddHom_of]
      exact of_mem_summand _ _)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of k z =>
        rw [d_of, leftShiftAddHom_of, leftShiftAddHom_of, d_mk, d_of,
          δ_leftUnshift z (k + -a) (neg_add_cancel_right k a) (k + -a + 1) (k + 1) (by omega),
          of_units_smul, smul_smul, koszulSign, Int.negOnePow_neg, ← koszulSign,
          Int.units_mul_self, one_smul]
        exact congrArg (Shift.mk (-a)) (of_congr (by omega) fun _ => rfl)
      | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add])

@[simp]
theorem leftShiftEquiv_of (k : ℤ) (z : Cochain A (Shift a M) N k) :
    leftShiftEquiv A M N a (DirectSum.of _ k z) =
      Shift.mk (-a) (DirectSum.of _ (k + -a) (z.leftUnshift (k + -a) (neg_add_cancel_right k a))) :=
  leftShiftAddHom_of k z

@[simp]
theorem leftShiftEquiv_symm_mk_of (n : ℤ) (z : Cochain A M N n) :
    (leftShiftEquiv A M N a).symm (Shift.mk (-a) (DirectSum.of _ n z)) =
      DirectSum.of _ (n + a) (z.leftShift a (n + a) rfl) :=
  leftUnshiftAddHom_mk_of n z

end Left

/-- `Hᵏ(HOM_A(M, N⟦a⟧)) ≃+ Hˡ(HOM_A(M, N))` for `k + a = l`. -/
noncomputable def cohomologyRightShiftAddEquiv (a k l : ℤ) (h : k + a = l) :
    cohomology (HOM A M (Shift a N)) k ≃+ cohomology (HOM A M N) l :=
  ((rightShiftEquiv A M N a).cohomologyAddEquiv k).trans (cohomology.shiftAddEquiv _ a k l h)

/-- `Hᵏ(HOM_A(M⟦a⟧, N)) ≃+ Hˡ(HOM_A(M, N))` for `k = l + a`. -/
noncomputable def cohomologyLeftShiftAddEquiv (a k l : ℤ) (h : k + -a = l) :
    cohomology (HOM A (Shift a M) N) k ≃+ cohomology (HOM A M N) l :=
  ((leftShiftEquiv A M N a).cohomologyAddEquiv k).trans (cohomology.shiftAddEquiv _ (-a) k l h)

end DGModule.HOM

/-! ### Morphisms into a shift -/

namespace Cocycle

open Shift

variable (A : Type*) (M N : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

/-- Morphisms of dg modules `M → N⟦n⟧` are the `n`-cocycles of `HOM_A(M, N)`: a morphism is
sent to the same map, viewed as a cochain of degree `n` from `M` to `N`. -/
def homShiftAddEquiv (n : ℤ) : (M →ᵈᵍ[A] Shift n N) ≃+ Cocycle A M N n :=
  (Cocycle.equivHom A M (Shift n N)).trans
    { toFun := fun z => z.rightUnshift n (zero_add n)
      invFun := fun z => z.rightShift n 0 (zero_add n)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

variable {A M N}

@[simp]
theorem homShiftAddEquiv_apply (n : ℤ) (f : M →ᵈᵍ[A] Shift n N) (x : M) :
    (homShiftAddEquiv A M N n f : Cochain A M N n) x = unmk n (f x) := rfl

@[simp]
theorem homShiftAddEquiv_symm_apply (n : ℤ) (z : Cocycle A M N n) (x : M) :
    (homShiftAddEquiv A M N n).symm z x = Shift.mk n ((z : Cochain A M N n) x) := rfl

end Cocycle

end DG
