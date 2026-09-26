import Mathlib.CategoryTheory.Localization.Predicate
import DG.Homotopy.ConeCochain
import DG.Homotopy.HomotopyCategory
import DG.Module.Prod

/-!
# The homotopy category as a localization

Let `A` be a dg ring. This file shows that the quotient functor
`DG.HomotopyCategory.quotient A : DGModuleCat A ⥤ HomotopyCategory A` is a localization functor
for the class `DG.DGModuleCat.homotopyEquivalences A` of homotopy equivalences
(`DG.HomotopyCategory.quotient_isLocalization`), as Mathlib's
`ComplexShape.quotient_isLocalization` for homological complexes.

The key point is `DG.DGHomotopy.map_eq_of_inverts_homotopyEquivalences`: homotopic morphisms
`f g : M ⟶ N` become equal under any functor inverting homotopy equivalences. Instead of a
cylinder object we use `M × Cone(𝟙_M)`: the projection `p` to `M` is a homotopy equivalence
since `Cone(𝟙_M)` is contractible, it has the two sections `x ↦ (x, 0)` and
`x ↦ (x, inr x)`, and a homotopy `h : f ≃ g` gives a morphism `M × Cone(𝟙_M) → N`,
`(x, c) ↦ f x + k c` (with `k` built from `h`), restricting to `f` and `g` along the two
sections.
-/

open CategoryTheory

universe v u

namespace DG

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

namespace DGModuleCat

variable (A) in
/-- The homotopy equivalences of dg modules, as a class of morphisms of `DGModuleCat A`. -/
def homotopyEquivalences : MorphismProperty (DGModuleCat.{v} A) :=
  fun M N f => ∃ e : DGHomotopyEquiv A M N, e.hom = f.hom

omit [DGRing A] in
theorem homotopyEquivalences_of_equiv {M N : DGModuleCat.{v} A} (e : DGHomotopyEquiv A M N) :
    homotopyEquivalences A (ofHom e.hom) :=
  ⟨e, rfl⟩

end DGModuleCat

section Cylinder

variable {M N : DGModuleCat.{v} A} {f g : M ⟶ N} (h : DGHomotopy f.hom g.hom)

namespace DGHomotopy

/-- The auxiliary dg module `M × Cone(𝟙_M)`, playing the role of a cylinder of `M`. -/
abbrev cyl (M : DGModuleCat.{v} A) : DGModuleCat.{v} A :=
  DGModuleCat.of A (M × Cone (DGModuleHom.id : M →ᵈᵍ[A] M))

/-- The projection `M × Cone(𝟙_M) → M`, a homotopy equivalence. -/
def cylProj (M : DGModuleCat.{v} A) : cyl M →ᵈᵍ[A] M :=
  DGModuleHom.fst _ _

/-- The section `x ↦ (x, 0)` of `DG.DGHomotopy.cylProj M`. -/
def cylInl (M : DGModuleCat.{v} A) : M →ᵈᵍ[A] cyl M :=
  DGModuleHom.inl _ _

/-- The section `x ↦ (x, inr x)` of `DG.DGHomotopy.cylProj M`. -/
def cylInr (M : DGModuleCat.{v} A) : M →ᵈᵍ[A] cyl M :=
  DGModuleHom.inl _ _ + (DGModuleHom.inr _ _).comp (Cone.inr DGModuleHom.id)

theorem cylProj_comp_cylInl (M : DGModuleCat.{v} A) :
    (cylProj M).comp (cylInl M) = DGModuleHom.id :=
  DGModuleHom.ext fun _ => rfl

theorem cylProj_comp_cylInr (M : DGModuleCat.{v} A) :
    (cylProj M).comp (cylInr M) = DGModuleHom.id :=
  DGModuleHom.ext fun x => by simp [cylProj, cylInr]

/-- `M × Cone(𝟙_M) → M` is a homotopy equivalence. -/
noncomputable def cylProjHomotopyEquiv (M : DGModuleCat.{v} A) : DGHomotopyEquiv A (cyl M) M where
  hom := cylProj M
  inv := cylInl M
  homotopyHomInvId := by
    have h₀ := ((Cone.isContractible_id (A := A) (M : Type v)).comp_left
      (DGModuleHom.snd (A := A) (M : Type v) _)).comp_right
      (DGModuleHom.inr (A := A) (M : Type v) (Cone (DGModuleHom.id : M →ᵈᵍ[A] M)))
    have h₁ : Homotopic ((cylInl M).comp (cylProj M)) DGModuleHom.id := by
      rw [Homotopic.iff_sub]
      convert h₀.neg using 1 <;> ext x <;> simp [cylInl, cylProj]
    exact h₁.some
  homotopyInvHomId := DGHomotopy.ofEq (cylProj_comp_cylInl M)

/-- The morphism `M × Cone(𝟙_M) → N` restricting to `f` along `cylInl` and to `g` along
`cylInr`: `(x, c) ↦ f x + k c`, where `k : Cone(𝟙_M) → N` is built from the homotopy. -/
def cylDesc : cyl M →ᵈᵍ[A] N :=
  f.hom.comp (DGModuleHom.fst _ _) + (Cone.desc DGModuleHom.id h.symm.hom (g.hom - f.hom) (by
    rw [DGModuleHom.comp_id, Cochain.ofHom_sub, h.symm.ofHom_eq, add_sub_cancel_right])).comp
      (DGModuleHom.snd _ _)

theorem cylDesc_comp_cylInl : (cylDesc h).comp (cylInl M) = f.hom :=
  DGModuleHom.ext fun x => by simp [cylDesc, cylInl]

theorem cylDesc_comp_cylInr : (cylDesc h).comp (cylInr M) = g.hom :=
  DGModuleHom.ext fun x => by simp [cylDesc, cylInr]

include h in
/-- Homotopic morphisms of dg modules are identified by every functor inverting homotopy
equivalences. -/
theorem map_eq_of_inverts_homotopyEquivalences {E : Type*} [Category E]
    (F : DGModuleCat.{v} A ⥤ E) (hF : (DGModuleCat.homotopyEquivalences A).IsInvertedBy F) :
    F.map f = F.map g := by
  have := hF _ (DGModuleCat.homotopyEquivalences_of_equiv (cylProjHomotopyEquiv M))
  have h₀ : F.map (DGModuleCat.ofHom (cylInl M)) = F.map (DGModuleCat.ofHom (cylInr M)) := by
    rw [← cancel_mono (F.map (DGModuleCat.ofHom (cylProjHomotopyEquiv M).hom)), ← F.map_comp,
      ← F.map_comp, ← DGModuleCat.ofHom_comp, ← DGModuleCat.ofHom_comp]
    exact congrArg (fun φ => F.map (DGModuleCat.ofHom φ))
      ((cylProj_comp_cylInl M).trans (cylProj_comp_cylInr M).symm)
  rw [← DGModuleCat.ofHom_hom f, ← DGModuleCat.ofHom_hom g, ← cylDesc_comp_cylInl h,
    ← cylDesc_comp_cylInr h, DGModuleCat.ofHom_comp, DGModuleCat.ofHom_comp, F.map_comp,
    F.map_comp, h₀]

end DGHomotopy

end Cylinder

namespace HomotopyCategory

variable (A)

omit [DGRing A] in
/-- Homotopy equivalences become isomorphisms in the homotopy category. -/
theorem quotient_inverts_homotopyEquivalences :
    (DGModuleCat.homotopyEquivalences.{v} A).IsInvertedBy (quotient A) := by
  rintro M N f ⟨e, he⟩
  rw [← DGModuleCat.ofHom_hom f, ← he]
  exact (isoOfHomotopyEquiv e).isIso_hom

/-- The homotopy category satisfies the universal property of the localization of the category
of dg modules at the homotopy equivalences. -/
def strictUniversalPropertyFixedTargetQuotient (E : Type*) [Category E] :
    Localization.StrictUniversalPropertyFixedTarget (quotient A)
      (DGModuleCat.homotopyEquivalences.{v} A) E where
  inverts := quotient_inverts_homotopyEquivalences A
  lift F hF := CategoryTheory.Quotient.lift _ F fun _ _ _ _ h =>
    h.some.map_eq_of_inverts_homotopyEquivalences F hF
  fac _ _ := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

/-- The quotient functor `DGModuleCat A ⥤ HomotopyCategory A` is a localization functor for the
homotopy equivalences. -/
instance quotient_isLocalization :
    (quotient A).IsLocalization (DGModuleCat.homotopyEquivalences.{v} A) := by
  apply Functor.IsLocalization.mk'
  all_goals apply strictUniversalPropertyFixedTargetQuotient

end HomotopyCategory

end DG
