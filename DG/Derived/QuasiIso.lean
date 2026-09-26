import Mathlib.Algebra.Homology.DerivedCategory.Basic
import DG.Compact.Thick
import DG.Homotopy.CohomologyComparison
import DG.Homotopy.ForgetTriangulated
import DG.Homotopy.HomologyFunctor
import DG.Homotopy.KProjective
import DG.Homotopy.Localization
import DG.Homotopy.Triangulated

/-!
# Quasi-isomorphisms and acyclic objects in the homotopy category

Let `A` be a dg ring. This file introduces the class of quasi-isomorphisms
`DG.HomotopyCategory.quasiIso A` in the homotopy category `DG.HomotopyCategory A` of dg
`A`-modules and the triangulated subcategory `DG.HomotopyCategory.subcategoryAcyclic A` of
acyclic dg modules, and shows that the quasi-isomorphisms are exactly the morphisms whose cone
is acyclic. Consequently the quasi-isomorphisms form a multiplicative system compatible with the
triangulation (Verdier), with a calculus of left and right fractions; this is what is needed to
construct the derived category `D(A) = H(A)[qis⁻¹]` (`DG/Derived/Basic.lean`).

## Main definitions and results

* `DG.HomotopyCategory.quasiIso A : MorphismProperty (HomotopyCategory A)`: the morphisms whose
  image under the forgetful functor to Mathlib's homotopy category of cochain complexes of
  abelian groups is a quasi-isomorphism. By `DG.HomotopyCategory.quotient_map_mem_quasiIso_iff`,
  the image of a morphism `f` of dg modules is in `quasiIso A` iff `f` is a quasi-isomorphism of
  dg modules (`DG.DGModuleHom.IsQuasiIso`: it induces bijections on all cohomology groups), and
  by `DG.HomotopyCategory.mem_quasiIso_iff_forget` the class does not depend on the ground ring
  used to form the underlying complexes.
* `DG.HomotopyCategory.subcategoryAcyclic A`: the acyclic objects, as the kernel of the
  homological functor `H⁰`, following Mathlib's `HomotopyCategory.subcategoryAcyclic`;
  `DG.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff`: it consists of the acyclic dg
  modules (`DG.IsAcyclic`); `DG.HomotopyCategory.isThick_subcategoryAcyclic`: it is thick.
* `DG.HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`: a morphism is a quasi-isomorphism iff
  its cone is acyclic; for morphisms of dg modules,
  `DG.HomotopyCategory.quotient_map_mem_quasiIso_iff_isAcyclic_cone`.
* Instances: `quasiIso A` is multiplicative, compatible with the shift and with the
  triangulation, and has a calculus of left and right fractions (from Mathlib's results on
  `Triangulated.Subcategory.W`).

## Implementation notes

The ground ring of the underlying complexes is `ℤ` (every dg ring is a dg `ℤ`-algebra,
`DG.DGAlgebra.int`), so that everything is stated for dg rings. For a dg `R`-algebra, the
comparison `DG.HomotopyCategory.mem_quasiIso_iff_forget` identifies `quasiIso A` with the
quasi-isomorphisms of the underlying complexes of `R`-modules.
-/

open CategoryTheory Limits Pretriangulated

universe w v u

namespace DG

namespace HomotopyCategory

section

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The quasi-isomorphisms in the homotopy category of dg `A`-modules: the morphisms inducing
isomorphisms on all cohomology groups, i.e. whose underlying morphism of complexes of abelian
groups is a quasi-isomorphism. -/
def quasiIso : MorphismProperty (HomotopyCategory.{v} A) := fun _ _ f =>
  _root_.HomotopyCategory.quasiIso (ModuleCat.{v} ℤ) (ComplexShape.up ℤ) ((forget ℤ A).map f)

/-- The triangulated subcategory of acyclic objects of the homotopy category of dg modules: the
kernel of the homological functor `H⁰` (`X` is acyclic iff `H⁰(X⟦n⟧) = 0` for all `n`). -/
def subcategoryAcyclic : Triangulated.Subcategory (HomotopyCategory.{v} A) :=
  (homologyFunctor ℤ A 0).homologicalKernel

instance : (subcategoryAcyclic.{v} A).P.IsClosedUnderIsomorphisms := by
  dsimp only [subcategoryAcyclic]
  infer_instance

variable {A}

theorem mem_quasiIso_iff {X Y : HomotopyCategory.{v} A} (f : X ⟶ Y) :
    quasiIso A f ↔ ∀ n : ℤ, IsIso ((homologyFunctor ℤ A n).map f) := Iff.rfl

/-- An object is acyclic iff its underlying complex is acyclic. -/
theorem mem_subcategoryAcyclic_iff_forget (X : HomotopyCategory.{v} A) :
    (subcategoryAcyclic A).P X ↔
      (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat.{v} ℤ)).P ((forget ℤ A).obj X) :=
  forall_congr' fun n =>
    ((_root_.HomotopyCategory.homologyFunctor _ _ 0).mapIso
      (((forget ℤ A).commShiftIso n).app X)).isZero_iff

/-- An object is acyclic iff all its cohomology groups vanish. -/
theorem mem_subcategoryAcyclic_iff (X : HomotopyCategory.{v} A) :
    (subcategoryAcyclic A).P X ↔ ∀ n : ℤ, IsZero ((homologyFunctor ℤ A n).obj X) :=
  (mem_subcategoryAcyclic_iff_forget X).trans
    (_root_.HomotopyCategory.mem_subcategoryAcyclic_iff _)

variable (A)

/-- A morphism of the homotopy category is a quasi-isomorphism iff its cone is acyclic, i.e.
the quasi-isomorphisms are the class of morphisms `W` attached to the triangulated subcategory
of acyclic objects. -/
theorem quasiIso_eq_subcategoryAcyclic_W : quasiIso.{v} A = (subcategoryAcyclic A).W := by
  ext X Y f
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  refine Iff.trans ?_ ((subcategoryAcyclic A).mem_W_iff_of_distinguished _ hT).symm
  rw [mem_subcategoryAcyclic_iff_forget]
  change _root_.HomotopyCategory.quasiIso _ _ ((forget ℤ A).map f) ↔ _
  rw [_root_.HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  exact (_root_.HomotopyCategory.subcategoryAcyclic _).mem_W_iff_of_distinguished _
    ((forget ℤ A).map_distinguished _ hT)

/-- The acyclic objects form a thick subcategory: it is triangulated and closed under direct
summands (retracts). -/
theorem isThick_subcategoryAcyclic : IsThick (subcategoryAcyclic.{v} A).P where
  zero := (subcategoryAcyclic A).zero
  shift := (subcategoryAcyclic A).shift
  ext₂ := (subcategoryAcyclic A).ext₂
  retract {X Y} e hY n := by
    have e' := e.map (shiftFunctor _ n ⋙ homologyFunctor ℤ A 0)
    rw [IsZero.iff_id_eq_zero]
    refine e'.retract.symm.trans ?_
    rw [(hY n).eq_of_src e'.r 0, comp_zero]

instance : (quasiIso.{v} A).RespectsIso := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{v} A).IsMultiplicative := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{v} A).IsCompatibleWithShift ℤ := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{v} A).IsCompatibleWithTriangulation := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{v} A).HasLeftCalculusOfFractions := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (quasiIso.{v} A).HasRightCalculusOfFractions := by
  rw [quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

end

/-! ### Concrete descriptions -/

section Concrete

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

variable (R : Type w) [CommRing R] [Algebra R A] [DGAlgebra R A]

/-- For a dg `R`-algebra `A`, a morphism of dg modules is a quasi-isomorphism iff its underlying
morphism of complexes of `R`-modules is a quasi-isomorphism. -/
theorem forget_map_quotient_map_mem_quasiIso_iff {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    _root_.HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)
      ((forget R A).map ((quotient A).map f)) ↔ f.hom.IsQuasiIso := by
  rw [forget_map_quotient_map, _root_.HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
  refine forall_congr' fun n => ?_
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  have h : ⇑(HomologicalComplex.homologyMap ((DGModuleCat.forget R A).map f) n) ∘
      ⇑(DGModuleCat.cohomologyAddEquiv R M n) =
      ⇑(DGModuleCat.cohomologyAddEquiv R N n) ∘ ⇑(cohomology.map f.hom n) :=
    funext fun x => (DGModuleCat.cohomologyAddEquiv_naturality R f n x).symm
  rw [← Function.Bijective.of_comp_iff _ (DGModuleCat.cohomologyAddEquiv R M n).bijective, h,
    Function.Bijective.of_comp_iff' (DGModuleCat.cohomologyAddEquiv R N n).bijective]

/-- The image of a morphism of dg modules in the homotopy category is a quasi-isomorphism iff it
is a quasi-isomorphism of dg modules. -/
theorem quotient_map_mem_quasiIso_iff {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    quasiIso A ((quotient A).map f) ↔ f.hom.IsQuasiIso :=
  forget_map_quotient_map_mem_quasiIso_iff ℤ f

/-- For a dg `R`-algebra `A`, the quasi-isomorphisms of `H(A)` are the morphisms whose
underlying morphism of complexes of `R`-modules is a quasi-isomorphism: the class
`quasiIso A` does not depend on the ground ring. -/
theorem mem_quasiIso_iff_forget {X Y : HomotopyCategory.{v} A} (f : X ⟶ Y) :
    quasiIso A f ↔ _root_.HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)
      ((forget R A).map f) := by
  obtain ⟨M, rfl⟩ := quotient_obj_surjective X
  obtain ⟨N, rfl⟩ := quotient_obj_surjective Y
  obtain ⟨f, rfl⟩ := (quotient A).map_surjective f
  rw [quotient_map_mem_quasiIso_iff, forget_map_quotient_map_mem_quasiIso_iff]

variable (A) in
/-- The cohomology functors `H(A) ⥤ ModuleCat R` invert quasi-isomorphisms. -/
theorem homologyFunctor_inverts_quasiIso (n : ℤ) :
    (quasiIso.{v} A).IsInvertedBy (homologyFunctor R A n) :=
  fun _ _ f hf => ((mem_quasiIso_iff_forget R f).mp hf) n

/-- A dg module is in the subcategory of acyclic objects iff it is acyclic. -/
theorem quotient_obj_mem_subcategoryAcyclic_iff (M : DGModuleCat.{v} A) :
    (subcategoryAcyclic A).P ((quotient A).obj M) ↔ IsAcyclic M := by
  rw [mem_subcategoryAcyclic_iff, isAcyclic_iff_isZero_homologyFunctor_obj (R := ℤ)]

/-- A morphism of dg modules becomes a quasi-isomorphism in the homotopy category iff its
mapping cone is acyclic. -/
theorem quotient_map_mem_quasiIso_iff_isAcyclic_cone {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    quasiIso A ((quotient A).map f) ↔ IsAcyclic (Cone f.hom) := by
  rw [quotient_map_mem_quasiIso_iff, DGModuleHom.isQuasiIso_iff_isAcyclic_cone]

end Concrete

end HomotopyCategory

namespace DGModuleCat

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The quasi-isomorphisms of dg modules, as a class of morphisms of `DGModuleCat A`. -/
def quasiIso : MorphismProperty (DGModuleCat.{v} A) := fun _ _ f => f.hom.IsQuasiIso

omit [DGRing A] in
/-- Homotopy equivalences are quasi-isomorphisms. -/
theorem homotopyEquivalences_le_quasiIso : homotopyEquivalences.{v} A ≤ quasiIso A := by
  rintro M N f ⟨e, he⟩
  rw [quasiIso, ← he]
  exact e.isQuasiIso_hom

/-- The quasi-isomorphisms of the homotopy category are the images of the quasi-isomorphisms of
dg modules. -/
theorem _root_.DG.HomotopyCategory.quasiIso_eq_quasiIso_map_quotient :
    HomotopyCategory.quasiIso.{v} A = (quasiIso A).map (HomotopyCategory.quotient A) := by
  ext ⟨M⟩ ⟨N⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective f
  constructor
  · intro hf
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨M', N', g, hg, ⟨e⟩⟩
    rw [quasiIso, ← HomotopyCategory.quotient_map_mem_quasiIso_iff] at hg
    exact ((HomotopyCategory.quasiIso A).arrow_mk_iso_iff e).1 hg

end DGModuleCat

end DG
