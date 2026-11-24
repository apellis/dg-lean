import DG.Derived.Basic

/-! A module concentrated in degree zero identifies naturally with its degree-zero cohomology. -/

open CategoryTheory

noncomputable section

namespace DG.DerivedCategory

universe w u

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w, u} A]

private def degreeZeroCohomologyEquiv {X : Type u} [AddCommGroup X] [DGAddCommGroup X]
    (hX : ∀ x : X, x ∈ grading 0) (hd : ∀ x : X, d x = 0) :
    X ≃+ cohomology X 0 := by
  let i : X →+ cocycles X 0 := (AddMonoidHom.id X).codRestrict _
    (fun x => mem_cocycles.mpr ⟨hX x, hd x⟩)
  refine AddEquiv.ofBijective ((cohomology.mk X 0).comp i) ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero _).2
    intro x hx
    have hx' : cohomology.mk X 0 (i x) = 0 := hx
    obtain ⟨z, hz, hz'⟩ := mem_coboundaries.mp ((cohomology.mk_eq_zero_iff _).mp hx')
    change d z = x at hz'
    rw [hd] at hz'
    exact hz'.symm
  · intro x
    obtain ⟨z, rfl⟩ := cohomology.mk_surjective X 0 x
    exact ⟨z.1, rfl⟩

private theorem degreeZeroCohomologyEquiv_apply {X : Type u} [AddCommGroup X] [DGAddCommGroup X]
    (hX : ∀ x : X, x ∈ grading 0) (hd : ∀ x : X, d x = 0) (x : X) :
    degreeZeroCohomologyEquiv hX hd x = cohomology.mkOf (hX x) (hd x) := rfl

/-- Cohomology in degree zero of the image of a dg module concentrated in degree zero. -/
def degreeZeroHomologyQEquiv (X : DGModuleCat.{u} A)
    (hX : ∀ x : X, x ∈ grading 0) (hd : ∀ x : X, d x = 0) :
    X ≃+ (DG.DerivedCategory.homologyFunctor ℤ 0).obj (Q.obj X) :=
  (degreeZeroCohomologyEquiv hX hd).trans (cohomologyAddEquiv ℤ X 0)

theorem degreeZeroHomologyQEquiv_naturality {X Y : DGModuleCat.{u} A} (f : X ⟶ Y)
    (hX : ∀ x : X, x ∈ grading 0) (hdX : ∀ x : X, d x = 0)
    (hY : ∀ y : Y, y ∈ grading 0) (hdY : ∀ y : Y, d y = 0) (x : X) :
    (DG.DerivedCategory.homologyFunctor ℤ 0).map (Q.map f)
      (degreeZeroHomologyQEquiv X hX hdX x) = degreeZeroHomologyQEquiv Y hY hdY (f x) := by
  let e := homologyFunctorFactors (A := A) ℤ 0
  change (e.inv.app X ≫ (Q ⋙ homologyFunctor ℤ 0).map f)
      (degreeZeroCohomologyEquiv hX hdX x) =
    e.inv.app Y (degreeZeroCohomologyEquiv hY hdY (f x))
  rw [← e.inv.naturality f]
  rfl

end DG.DerivedCategory
