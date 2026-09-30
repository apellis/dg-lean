import DG
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Check every imported DG declaration, not only the headline sample.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.getRoot == `DG then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
  logInfo m!"Audited {count} DG declarations; all transitive axioms are allowed."

-- Check compatibility statements for declarations now supplied by Mathlib and
-- for the universe-safe derived-category wrappers.
open CategoryTheory Limits
universe w v u

example {R : Type w} [Ring R] {X : ModuleCat.{v} R} :
    IsZero X ↔ Subsingleton X := ModuleCat.isZero_iff_subsingleton

example {R : Type*} [Semiring R] {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    {F G : C ⥤ D} [F.Linear R] (e : F ≅ G) : G.Linear R :=
  Functor.linear_of_iso R e

example {R : Type*} [Semiring R] {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [CategoryTheory.Linear R E]
    (F : C ⥤ D) [F.Full] [F.EssSurj] [F.Linear R] (G : D ⥤ E)
    [(F ⋙ G).Linear R] : G.Linear R := Functor.linear_of_full_essSurj_comp F G

example {A : Type u} [Ring A] [DG.DGAddCommGroup A] [DG.DGRing A]
    (h : MorphismProperty.HasLocalization.{w} (DG.HomotopyCategory.quasiIso.{v} A)) :
    DG.HasDerivedCategory.{w, v} A := { toHasLocalization := h }
example {A : Type u} [Ring A] [DG.DGAddCommGroup A] [DG.DGRing A]
    [DG.HasDerivedCategory.{w, v} A] :
    MorphismProperty.HasLocalization.{w} (DG.HomotopyCategory.quasiIso.{v} A) := inferInstance

example {C : Type u} [Category.{v} C] [Preadditive C]
    [∀ X Y : C, DG.DGAddCommGroup (X ⟶ Y)] [DG.DGCategory C]
    (h : MorphismProperty.HasLocalization.{w} (DG.CatModule.HomotopyCategory.quasiIso.{v} C)) :
    DG.CatModule.HasDerivedCategory.{w, v} C := { toHasLocalization := h }
example {C : Type u} [Category.{v} C] [Preadditive C]
    [∀ X Y : C, DG.DGAddCommGroup (X ⟶ Y)] [DG.DGCategory C]
    [DG.CatModule.HasDerivedCategory.{w, v} C] :
    MorphismProperty.HasLocalization.{w} (DG.CatModule.HomotopyCategory.quasiIso.{v} C) :=
  inferInstance

#print axioms DG.CompactlyGenerates.isRepresentable
#print axioms DG.thickClosure_eq_isCompact
#print axioms DG.AbelianK0.eulerChar_eq_finsum_homology
#print axioms DG.K0.mk_shift
#print axioms DG.Triangulated.Subcategory.prop_iff_of_W_iff
#print axioms DG.DGAlgCat.monEquivalence
#print axioms DG.DGModuleCat.modEquivalence
#print axioms DG.HomotopyCategory.pretriangulated
#print axioms DG.HomotopyCategory.isTriangulated
#print axioms DG.DerivedCategory.isTriangulated
#print axioms DG.semiFreeResolution
#print axioms DG.Bar.isQuasiIso_augmentation
#print axioms DG.Bar.d_homotopy_add_homotopy_d
#print axioms DG.CatModule.weightEquivalence
#print axioms DG.CatModule.HasDerivedCategory
#print axioms CategoryTheory.Functor.linear_of_iso
#print axioms CategoryTheory.Functor.linear_of_full_essSurj_comp
#print axioms ModuleCat.isZero_iff_subsingleton
