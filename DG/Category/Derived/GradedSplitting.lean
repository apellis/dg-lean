import DG.Category.Derived.Basic
import DG.Category.Resolution.KProjective

/-!
# Graded-split short exact sequences over a dg category give distinguished triangles

Let `C` be a dg category and `F →ⁱ G →ᵖ Q` a sequence of dg modules over `C` with a graded
splitting (`DG.CatModule.GradedSplitting i p`: cochains `r : G → F`, `s : Q → G` of degree `0`
with `r i = 1`, `p s = 1`, `i r + s p = 1`). The morphism `cone(i) → Q`, `(x, y) ↦ p y`, is a
quasi-isomorphism (`DG.CatModule.GradedSplitting.isQuasiIso_coneDesc`): at every object, the
value of `cone(i)` contracts onto that of `Q`. Hence `Q F → Q G → Q Q → (Q F)⟦1⟧` is a
distinguished triangle of `D(C)` for a suitable third morphism
(`DG.CatModule.GradedSplitting.exists_distinguished`). This is a port of
`DG.GradedSplitting.exists_distinguished` (the case of a dg ring).

The contraction uses the *twisting map* `τ = r ∘ (d s - s d)` of degree `1`, which measures the
failure of `s` to commute with the differentials: `d s = s d + i τ`.
-/

open CategoryTheory Limits Pretriangulated

universe w' w v u

namespace DG

namespace CatModule

namespace GradedSplitting

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {F G K : CatModule.{w} C} {i : F ⟶ G} {p : G ⟶ K} (σ : GradedSplitting i p)

include σ in
theorem i_injective (X : C) : Function.Injective (i.app X) := fun a b h => by
  rw [← σ.r_i a, ← σ.r_i b, h]

theorem r_s {X : C} (y : K.obj X) : σ.r.app X (σ.s.app X y) = 0 := by
  apply i_injective σ X
  have h := σ.i_r_add_s_p (σ.s.app X y)
  rw [σ.p_s, add_eq_right] at h
  rw [h, map_zero]

/-- The twisting map `τ = r ∘ (d s - s d)`, of degree `1`, at an object `X`. -/
def twist (X : C) : K.obj X →+ F.obj X :=
  (σ.r.app X).comp ((d : G.obj X →+ G.obj X).comp (σ.s.app X) - (σ.s.app X).comp d)

theorem twist_apply {X : C} (y : K.obj X) :
    σ.twist X y = σ.r.app X (d (σ.s.app X y) - σ.s.app X (d y)) := rfl

theorem i_twist {X : C} (y : K.obj X) :
    i.app X (σ.twist X y) = d (σ.s.app X y) - σ.s.app X (d y) := by
  have h := σ.i_r_add_s_p (d (σ.s.app X y) - σ.s.app X (d y))
  rw [map_sub (p.app X), p.map_d, σ.p_s, σ.p_s, sub_self, map_zero, add_zero] at h
  exact h

theorem d_s {X : C} (y : K.obj X) : d (σ.s.app X y) = σ.s.app X (d y) + i.app X (σ.twist X y) :=
  by rw [σ.i_twist, add_sub_cancel]

theorem twist_d {X : C} (y : K.obj X) : σ.twist X (d y) = -d (σ.twist X y) := by
  apply i_injective σ X
  have h1 := σ.d_s (d y)
  rw [d_d, map_zero, zero_add] at h1
  have h2 := congrArg d (σ.d_s y)
  rw [d_d, d_add, h1, ← i.map_d] at h2
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left h2.symm

theorem r_d {X : C} (x : G.obj X) :
    σ.r.app X (d x) = d (σ.r.app X x) + σ.twist X (p.app X x) := by
  conv_lhs => rw [← σ.i_r_add_s_p x]
  rw [d_add, ← i.map_d, σ.d_s, map_add (σ.r.app X), map_add (σ.r.app X), σ.r_i, σ.r_s, σ.r_i,
    zero_add]

theorem twist_mem {X : C} {k : ℤ} {y : K.obj X} (hy : y ∈ grading k) :
    σ.twist X y ∈ grading (k + 1) := by
  have h1 : d (σ.s.app X y) ∈ grading (k + 1) := d_mem (by simpa using σ.s.map_mem hy)
  have h2 : σ.s.app X (d y) ∈ grading (k + 1) := by simpa using σ.s.map_mem (d_mem hy)
  rw [twist_apply]
  simpa using σ.r.map_mem (sub_mem h1 h2)

include σ in
theorem i_comp_p : i ≫ p = 0 :=
  hom_ext fun X x => by rw [comp_app, σ.p_i]; rfl

variable [DGCategory C]

/-- The morphism `cone(i) → Q`, `(x, y) ↦ p y`. -/
noncomputable def coneDesc : cone i ⟶ K :=
  cone.desc i 0 p (by rw [i_comp_p σ, δ_zero]; rfl)

theorem coneDesc_apply {X : C} (c : (cone i).obj X) :
    σ.coneDesc.app X c = p.app X ((cone.snd i).app X c) := by
  rw [coneDesc, cone.desc_apply, Cochain.zero_apply, zero_add]

@[reassoc (attr := simp)]
theorem inr_coneDesc : cone.inr i ≫ σ.coneDesc = p :=
  cone.inr_desc _ _ _ _

/-- The section `Q → cone(i)`, `y ↦ (-τ y, s y)`, commuting with the differentials. -/
def coneSection (X : C) (y : K.obj X) : (cone i).obj X :=
  (cone.inl i).app X (-σ.twist X y) + (cone.inr i).app X (σ.s.app X y)

theorem coneSection_mem {X : C} {k : ℤ} {y : K.obj X} (hy : y ∈ grading k) :
    σ.coneSection X y ∈ grading k :=
  add_mem (by simpa using (cone.inl i).map_mem (neg_mem (σ.twist_mem hy)))
    ((cone.inr i).map_mem (by simpa using σ.s.map_mem hy))

theorem d_coneSection {X : C} (y : K.obj X) :
    d (σ.coneSection X y) = σ.coneSection X (d y) := by
  refine cone.ext_to ?_ ?_
  · simp only [coneSection, map_add, cone.d_fst_apply, cone.inl_fst_apply,
      cone.inr_fst_apply, add_zero, cone.inr_d_apply, σ.twist_d, d_neg]
  · simp only [coneSection, map_add, cone.d_snd_apply, cone.inl_fst_apply,
      cone.inl_snd_apply, cone.inr_snd_apply, cone.inr_d_apply, map_zero, add_zero, map_neg,
      σ.d_s]
    abel

theorem coneDesc_coneSection {X : C} (y : K.obj X) : σ.coneDesc.app X (σ.coneSection X y) = y := by
  simp [coneDesc_apply, coneSection, σ.p_s]

/-- The contracting homotopy of `cone(i)` onto `Q`, `(x, y) ↦ (r y, 0)`, of degree `-1`. -/
def coneHomotopy (X : C) (c : (cone i).obj X) : (cone i).obj X :=
  (cone.inl i).app X (σ.r.app X ((cone.snd i).app X c))

theorem coneHomotopy_mem {X : C} {k : ℤ} {c : (cone i).obj X} (hc : c ∈ grading k) :
    σ.coneHomotopy X c ∈ grading (k - 1) := by
  have := (cone.inl i).map_mem (σ.r.map_mem ((cone.snd i).map_mem hc))
  simpa [coneHomotopy, sub_eq_add_neg] using this

theorem coneHomotopy_zero {X : C} : σ.coneHomotopy X 0 = 0 := by
  simp [coneHomotopy]

theorem coneHomotopy_spec {X : C} (c : (cone i).obj X) :
    d (σ.coneHomotopy X c) + σ.coneHomotopy X (d c) + σ.coneSection X (σ.coneDesc.app X c) = c := by
  refine cone.ext_to ?_ ?_
  · simp only [coneHomotopy, coneSection, coneDesc_apply, map_add,
      cone.inl_fst_apply, cone.inr_fst_apply, cone.inl_d_apply, map_sub, cone.d_snd_apply,
      σ.r_i, σ.r_d, add_zero, map_neg]
    abel
  · simp only [coneHomotopy, coneSection, coneDesc_apply, map_add, cone.d_snd_apply,
      cone.inl_snd_apply, cone.inr_snd_apply, cone.inl_d_apply, map_sub, add_zero, zero_add,
      sub_zero]
    exact σ.i_r_add_s_p _

/-- `cone(i) → Q` is a quasi-isomorphism for a graded-split sequence `F → G → Q`. -/
theorem isQuasiIso_coneDesc : IsQuasiIso σ.coneDesc := by
  intro X k
  constructor
  · rw [cohomologyMap_injective_iff]
    rintro c hc hdc ⟨y, hy, hdy⟩
    refine ⟨σ.coneHomotopy X c + σ.coneSection X y,
      add_mem (σ.coneHomotopy_mem hc) (σ.coneSection_mem hy), ?_⟩
    have h := σ.coneHomotopy_spec c
    rw [hdc, coneHomotopy_zero, add_zero, ← hdy, ← σ.d_coneSection] at h
    rw [d_add, h]
  · rw [cohomologyMap_surjective_iff]
    intro y hy hdy
    refine ⟨σ.coneSection X y, σ.coneSection_mem hy, ?_, ?_⟩
    · rw [σ.d_coneSection, hdy]
      simp [coneSection, twist_apply]
    · rw [σ.coneDesc_coneSection, sub_self]
      exact zero_mem _

variable [HasDerivedCategory.{w', w} C]

open _root_.DG.CatModule.DerivedCategory

include σ in
/-- A graded-split short exact sequence `F → G → Q` of dg modules over a dg category gives a
distinguished triangle `Q F → Q G → Q Q → (Q F)⟦1⟧` in `D(C)`. -/
theorem exists_distinguished :
    ∃ δ : Q.obj K ⟶ (Q.obj F)⟦(1 : ℤ)⟧,
      Triangle.mk (Q.map i) (Q.map p) δ ∈ distTriang (DerivedCategory C) := by
  have : IsIso (Q.map σ.coneDesc) := (isIso_Q_map_iff _).mpr σ.isQuasiIso_coneDesc
  let T := Q.mapTriangle.obj (cone.triangle i)
  have hT : T ∈ distTriang (DerivedCategory C) :=
    (mem_distTriang_iff _).mpr ⟨_, _, _, ⟨Iso.refl _⟩⟩
  refine ⟨inv (Q.map σ.coneDesc) ≫ T.mor₃, isomorphic_distinguished T hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (Q.map σ.coneDesc)).symm
    (by simp [T]) ?_ (by
      dsimp
      erw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _)
  dsimp [T]
  rw [Category.id_comp, IsIso.comp_inv_eq, ← Functor.map_comp, σ.inr_coneDesc]

end GradedSplitting

end CatModule

end DG
