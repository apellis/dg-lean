import DG.Homotopy.CohomologyLinear
import DG.Homotopy.ForgetTriangulated
import DG.Homotopy.KProjective
import DG.Homotopy.ShiftLinear

/-!
# The homology functors on the homotopy category and the cohomology of dg modules

Let `A` be a dg `R`-algebra. The `n`-th cohomology functor
`DG.HomotopyCategory.homologyFunctor R A n : H(A) ⥤ ModuleCat R` is defined as Mathlib's
homology of the underlying cochain complex of `R`-modules. This file identifies it with the
library's cohomology `DG.cohomology M n = Zⁿ(M) ⧸ Bⁿ(M)`:

* `DG.DGModuleCat.cohomologyFunctor R A n : DGModuleCat A ⥤ ModuleCat R`,
  `M ↦ Hⁿ(M)` with the `R`-module structure `DG.DGModuleCat.Algebra.instModuleCohomology`, and
  `f ↦ DG.cohomology.map f n`;
* `DG.DGModuleCat.forgetCompHomologyFunctorIso R A n`: the homology of the underlying complex is
  naturally isomorphic to `cohomologyFunctor R A n` (from `DG.DGModuleCat.cohomologyLinearEquiv`);
* `DG.HomotopyCategory.quotientCompHomologyFunctorIso R A n :
    quotient A ⋙ homologyFunctor R A n ≅ DGModuleCat.cohomologyFunctor R A n`;
* `DG.HomotopyCategory.cohomologyFunctor R A n : H(A) ⥤ ModuleCat R`, the functor induced by
  `DGModuleCat.cohomologyFunctor R A n` on the homotopy category, and
  `DG.HomotopyCategory.homologyFunctorIso R A n : homologyFunctor R A n ≅ cohomologyFunctor R A n`;
* `DG.HomotopyCategory.isZero_homologyFunctor_obj_iff`:
  `IsZero ((homologyFunctor R A n).obj ((quotient A).obj M)) ↔ Subsingleton (cohomology M n)`,
  and `DG.HomotopyCategory.isAcyclic_iff_isZero_homologyFunctor_obj`;
* `DG.HomotopyCategory.homologyFunctor_linear`, `DG.HomotopyCategory.cohomologyFunctor_linear`:
  the cohomology functors on `H(A)` are `R`-linear.

We use the imported Mathlib theorem `ModuleCat.isZero_iff_subsingleton`, with the same
statement `IsZero X ↔ Subsingleton X`: a module is a zero object of `ModuleCat R` iff it is
a subsingleton. The theorem remains available to files importing this module.
-/

open CategoryTheory Limits

universe v u w

noncomputable section

namespace DG

namespace DGModuleCat

open DG.DGModuleCat.Algebra

variable (R : Type w) (A : Type u) [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]

/-- The `n`-th cohomology of dg `A`-modules as a functor to `R`-modules:
`M ↦ Hⁿ(M) = Zⁿ(M) ⧸ Bⁿ(M)` and `f ↦ DG.cohomology.map f n`. -/
@[simps obj]
def cohomologyFunctor (n : ℤ) : DGModuleCat.{v} A ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (cohomology M n)
  map f := ModuleCat.ofHom
    { toFun := cohomology.map f.hom n
      map_add' := map_add _
      map_smul' := cohomology_map_smul R f n }
  map_id M := ModuleCat.hom_ext (LinearMap.ext fun x => by
    change cohomology.map DGModuleHom.id n x = x
    rw [cohomology.map_id]
    rfl)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x =>
    cohomology.map_comp_apply g.hom f.hom n x)

variable {R A}

@[simp]
theorem cohomologyFunctor_map_apply (n : ℤ) {M N : DGModuleCat.{v} A} (f : M ⟶ N)
    (x : cohomology M n) : ((cohomologyFunctor R A n).map f).hom x = cohomology.map f.hom n x :=
  rfl

instance (n : ℤ) : (cohomologyFunctor.{v} R A n).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.ext fun x =>
    congrArg (fun φ => φ x) (cohomology.map_add f.hom g.hom n))

instance (n : ℤ) : (cohomologyFunctor.{v} R A n).Linear R where
  map_smul {M N} f r := ModuleCat.hom_ext (LinearMap.ext fun x => by
    induction x using cohomology.induction_on with
    | h z =>
      change cohomology.map (r • f).hom n (cohomology.mk M n z) =
        r • cohomology.map f.hom n (cohomology.mk M n z)
      rw [cohomology.map_mk, cohomology.map_mk]
      rfl)

variable (R A)

set_option backward.isDefEq.respectTransparency false in
/-- The homology of the underlying cochain complex of `R`-modules is naturally isomorphic to the
cohomology `Hⁿ(M) = Zⁿ(M) ⧸ Bⁿ(M)` of a dg module. -/
def forgetCompHomologyFunctorIso (n : ℤ) :
    forget R A ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n ≅
      cohomologyFunctor.{v} R A n :=
  NatIso.ofComponents (fun M => (cohomologyLinearEquiv R M n).toModuleIso.symm) fun {M N} f =>
    ModuleCat.hom_ext (LinearMap.ext fun x => by
      apply (cohomologyLinearEquiv R N n).injective
      change cohomologyLinearEquiv R N n ((cohomologyLinearEquiv R N n).symm
          ((HomologicalComplex.homologyMap ((forget R A).map f) n).hom x)) =
        cohomologyLinearEquiv R N n (cohomology.map f.hom n
          ((cohomologyLinearEquiv R M n).symm x))
      rw [LinearEquiv.apply_symm_apply, cohomologyLinearEquiv_apply,
        cohomologyAddEquiv_naturality, ← cohomologyLinearEquiv_apply, LinearEquiv.apply_symm_apply])

end DGModuleCat

namespace HomotopyCategory

variable (R : Type w) (A : Type u) [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]

/-- The cohomology functor on the homotopy category, composed with the quotient functor, is the
cohomology `M ↦ Hⁿ(M)` of dg modules. -/
def quotientCompHomologyFunctorIso (n : ℤ) :
    quotient A ⋙ homologyFunctor R A n ≅ DGModuleCat.cohomologyFunctor.{v} R A n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (forgetFactors R A) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (_root_.HomotopyCategory.homologyFunctorFactors _ _ n) ≪≫
    DGModuleCat.forgetCompHomologyFunctorIso R A n

/-- The cohomology `M ↦ Hⁿ(M)` of dg modules, as a functor on the homotopy category (the
cohomology maps of homotopic morphisms agree). -/
def cohomologyFunctor (n : ℤ) : HomotopyCategory.{v} A ⥤ ModuleCat.{v} R :=
  CategoryTheory.Quotient.lift _ (DGModuleCat.cohomologyFunctor.{v} R A n) fun M N f g h => by
    rw [← NatIso.naturality_1 (quotientCompHomologyFunctorIso R A n) f,
      ← NatIso.naturality_1 (quotientCompHomologyFunctorIso R A n) g, Functor.comp_map,
      Functor.comp_map, (quotient_map_eq_iff f g).mpr h]

/-- `cohomologyFunctor R A n` is induced by the cohomology of dg modules. -/
def quotientCompCohomologyFunctorIso (n : ℤ) :
    quotient A ⋙ cohomologyFunctor R A n ≅ DGModuleCat.cohomologyFunctor.{v} R A n :=
  CategoryTheory.Quotient.lift.isLift _ _ _

/-- The cohomology functor `homologyFunctor R A n` on the homotopy category (Mathlib's homology
of the underlying complex) is isomorphic to the functor induced by the cohomology
`M ↦ Hⁿ(M) = Zⁿ(M) ⧸ Bⁿ(M)` of dg modules. -/
def homologyFunctorIso (n : ℤ) : homologyFunctor R A n ≅ cohomologyFunctor.{v} R A n :=
  CategoryTheory.Quotient.natIsoLift _
    (quotientCompHomologyFunctorIso R A n ≪≫ (quotientCompCohomologyFunctorIso R A n).symm)

variable {R A}

/-- A dg module has vanishing `n`-th cohomology iff its image in the homotopy category is killed
by the `n`-th cohomology functor. -/
theorem isZero_homologyFunctor_obj_iff (n : ℤ) (M : DGModuleCat.{v} A) :
    IsZero ((homologyFunctor R A n).obj ((quotient A).obj M)) ↔ Subsingleton (cohomology M n) :=
  (((quotientCompHomologyFunctorIso R A n).app M).isZero_iff).trans
    ModuleCat.isZero_iff_subsingleton

variable (R A) in
/-- The cohomology functors on the homotopy category are `R`-linear. -/
instance homologyFunctor_linear (n : ℤ) : (homologyFunctor.{v} R A n).Linear R := by
  have : (quotient A ⋙ homologyFunctor.{v} R A n).Linear R :=
    Functor.linear_of_iso R (quotientCompHomologyFunctorIso R A n).symm
  exact Functor.linear_of_full_essSurj_comp (quotient A) _

variable (R A) in
instance cohomologyFunctor_linear (n : ℤ) : (cohomologyFunctor.{v} R A n).Linear R := by
  have : (quotient A ⋙ cohomologyFunctor.{v} R A n).Linear R :=
    Functor.linear_of_iso R (quotientCompCohomologyFunctorIso R A n).symm
  exact Functor.linear_of_full_essSurj_comp (quotient A) _

/-- A dg module is acyclic iff all cohomology functors vanish on it. -/
theorem isAcyclic_iff_isZero_homologyFunctor_obj (M : DGModuleCat.{v} A) :
    IsAcyclic M ↔ ∀ n : ℤ, IsZero ((homologyFunctor R A n).obj ((quotient A).obj M)) :=
  forall_congr' fun n => (isZero_homologyFunctor_obj_iff n M).symm

end HomotopyCategory

end DG
