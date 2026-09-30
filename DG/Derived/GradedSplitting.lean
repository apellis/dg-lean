import DG.Derived.Bar
import DG.Derived.Basic

/-!
# Graded-split short exact sequences give distinguished triangles

Let `F →ⁱ G →ᵖ Q` be a sequence of dg modules over a dg ring `A` with a graded splitting
(`DG.GradedSplitting i p`: graded `A`-linear maps `r : G → F`, `s : Q → G` of degree `0` with
`r i = 1`, `p s = 1`, `i r + s p = 1`). The morphism `Cone(i) → Q`, `(x, y) ↦ p y`, is a
quasi-isomorphism (`DG.GradedSplitting.isQuasiIso_coneDesc`): the underlying dg abelian group of
`Cone(i)` contracts onto `Q`. Hence `Q F → Q G → Q Q → (Q F)⟦1⟧` is a distinguished triangle of
`D(A)` for a suitable third morphism (`DG.GradedSplitting.exists_distinguished`); this is the dg
counterpart of Mathlib's triangles attached to degreewise split short exact sequences of
complexes.

The contraction uses the *twisting map* `τ = r ∘ (d s - s d) : Q → F` of degree `1`, which
measures the failure of `s` to commute with the differentials: `d s = s d + i τ`.
-/

open CategoryTheory Limits Pretriangulated

universe w v u

namespace DG

namespace GradedSplitting

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  {F G Q : Type v} [AddCommGroup F] [DGAddCommGroup F] [Module A F] [DGModule A F]
  [AddCommGroup G] [DGAddCommGroup G] [Module A G] [DGModule A G]
  [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q] [DGModule A Q]
  {i : F →ᵈᵍ[A] G} {p : G →ᵈᵍ[A] Q} (σ : GradedSplitting i p)

/-- The twisting map `τ = r ∘ (d s - s d) : Q → F`, of degree `1`. -/
def twist (y : Q) : F := σ.r (d (σ.s y) - σ.s (d y))

omit [DGRing A] [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem twist_add (y y' : Q) : σ.twist (y + y') = σ.twist y + σ.twist y' := by
  simp only [twist]
  rw [map_add σ.s, d_add, d_add, map_add σ.s, ← map_add σ.r]
  congr 1
  abel

omit [DGRing A] [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem i_twist (y : Q) : i (σ.twist y) = d (σ.s y) - σ.s (d y) := by
  have h := σ.i_r_add_s_p (d (σ.s y) - σ.s (d y))
  rw [map_sub p, p.map_d, σ.p_s, σ.p_s, sub_self, map_zero, add_zero] at h
  exact h

omit [DGRing A] [DGModule A F] [DGModule A G] [DGModule A Q] in
include σ in
theorem i_injective : Function.Injective i := fun a b h => by
  rw [← σ.r_i a, ← σ.r_i b, h]

omit [DGRing A] [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem r_s (y : Q) : σ.r (σ.s y) = 0 := by
  apply σ.i_injective
  have h := σ.i_r_add_s_p (σ.s y)
  rw [σ.p_s, add_eq_right] at h
  rw [h, map_zero]

omit [DGRing A] [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem d_s (y : Q) : d (σ.s y) = σ.s (d y) + i (σ.twist y) := by
  rw [σ.i_twist, add_sub_cancel]

omit [DGRing A] [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem twist_d (y : Q) : σ.twist (d y) = -d (σ.twist y) := by
  apply σ.i_injective
  have h1 := σ.d_s (d y)
  rw [d_d, map_zero, zero_add] at h1
  have h2 := congrArg d (σ.d_s y)
  rw [d_d, d_add, h1, ← i.map_d] at h2
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left h2.symm

omit [DGRing A] [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem r_d (x : G) : σ.r (d x) = d (σ.r x) + σ.twist (p x) := by
  conv_lhs => rw [← σ.i_r_add_s_p x]
  rw [d_add, ← i.map_d, σ.d_s, map_add σ.r, map_add σ.r, σ.r_i, σ.r_s, σ.r_i, zero_add]

omit [DGRing A] [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem twist_mem {k : ℤ} {y : Q} (hy : y ∈ grading k) : σ.twist y ∈ grading (k + 1) := by
  have h1 : d (σ.s y) ∈ grading (k + 1) := d_mem (by simpa using σ.s.map_mem hy)
  have h2 : σ.s (d y) ∈ grading (k + 1) := by simpa using σ.s.map_mem (d_mem hy)
  have := σ.r.map_mem (sub_mem h1 h2)
  rw [add_zero] at this
  exact this

/-- The morphism `Cone(i) → Q`, `(x, y) ↦ p y`. -/
def coneDesc : Cone i →ᵈᵍ[A] Q where
  toFun c := p (Cone.sndLinear i c)
  map_add' _ _ := by simp only [map_add]
  map_smul' _ _ := by simp only [map_smul, RingHom.id_apply]
  map_mem' hc := p.map_mem (Cone.sndLinear_mem hc)
  map_d' c := by
    simp only [Cone.sndLinear_d, map_add, σ.p_i, zero_add, p.map_d]

omit [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem coneDesc_apply (c : Cone i) : σ.coneDesc c = p (Cone.sndLinear i c) := rfl

omit [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem coneDesc_comp_inr : σ.coneDesc.comp (Cone.inr i) = p :=
  DGModuleHom.ext fun _ => rfl

/-- The section `Q → Cone(i)`, `y ↦ (-τ y, s y)`, commuting with the differentials. -/
def coneSection : Q →+ Cone i where
  toFun y := Cone.inlLinear i (Shift.mk 1 (-σ.twist y)) + Cone.inr i (σ.s y)
  map_zero' := by
    have : σ.twist 0 = 0 := by simp [twist]
    simp [this]
  map_add' y y' := by
    rw [σ.twist_add, map_add σ.s, map_add (Cone.inr i), neg_add, Shift.mk_add, map_add]
    abel

/-- The contracting homotopy of `Cone(i)` onto `Q`, `(x, y) ↦ (r y, 0)`, of degree `-1`. -/
def coneHomotopy : Cone i →+ Cone i :=
  ((Cone.inlLinear i).toAddMonoidHom.comp (Shift.mk 1).toAddMonoidHom).comp
    (σ.r.toAddMonoidHom.comp (Cone.sndLinear i).toAddMonoidHom)

omit [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem coneHomotopy_apply (c : Cone i) :
    σ.coneHomotopy c = Cone.inlLinear i (Shift.mk 1 (σ.r (Cone.sndLinear i c))) := rfl

omit [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem d_coneSection (y : Q) : σ.coneSection (d y) = d (σ.coneSection y) := by
  simp only [coneSection, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Cone.d_inlLinear_add_inr]
  congr 2
  · rw [Shift.d_mk, σ.twist_d, d_neg, koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul]
  · rw [Shift.unmk_mk, σ.d_s, map_neg]
    abel

omit [DGModule A F] [DGModule A G] [DGModule A Q] in
theorem coneHomotopy_spec (c : Cone i) :
    d (σ.coneHomotopy c) + σ.coneHomotopy (d c) + σ.coneSection (σ.coneDesc c) = c := by
  refine Cone.ext ?_ ?_
  · apply Shift.unmk_inj.mp
    simp only [coneHomotopy_apply, coneSection, coneDesc_apply, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, map_add, Cone.fstHom_inlLinear, Cone.fstHom_inr, add_zero, Cone.fstHom_d,
      Cone.sndLinear_d, Shift.unmk_d, Shift.unmk_mk, σ.r_i, σ.r_d,
      koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul]
    abel
  · simp only [coneHomotopy_apply, coneSection, coneDesc_apply, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, map_add, Cone.sndLinear_inlLinear, Cone.sndLinear_inr, Cone.sndLinear_d,
      Cone.fstHom_inlLinear, Shift.unmk_mk, d_zero, add_zero]
    calc _ = i (σ.r (Cone.sndLinear i c)) + σ.s (p (Cone.sndLinear i c)) := by abel
      _ = _ := σ.i_r_add_s_p _

omit [DGModule A F] [DGModule A G] [DGModule A Q] in
/-- `Cone(i) → Q` is a quasi-isomorphism for a graded-split sequence `F → G → Q`. -/
theorem isQuasiIso_coneDesc : σ.coneDesc.IsQuasiIso := by
  refine DGModuleHom.isQuasiIso_of_contraction σ.coneDesc σ.coneSection ?_ σ.d_coneSection
    σ.coneHomotopy ?_ σ.coneHomotopy_spec ?_
  · intro k y hy
    refine add_mem (Cone.inlLinear_mem ?_) ((Cone.inr i).map_mem (by simpa using σ.s.map_mem hy))
    exact Shift.mem_grading_iff.mpr (neg_mem (σ.twist_mem hy))
  · intro k c hc
    refine Cone.inlLinear_mem (Shift.mem_grading_iff.mpr ?_)
    rw [sub_add_cancel]
    simpa using σ.r.map_mem (Cone.sndLinear_mem hc)
  · intro y
    simp [coneSection, coneDesc_apply, σ.p_s]

variable [HasDerivedCategory.{w, v} A]

include σ in
/-- A graded-split short exact sequence `F → G → Q` of dg modules gives a distinguished
triangle `Q F → Q G → Q Q → (Q F)⟦1⟧` in `D(A)`. -/
theorem exists_distinguished :
    ∃ δ : DerivedCategory.Q.obj (DGModuleCat.of A Q) ⟶
        (DerivedCategory.Q.obj (DGModuleCat.of A F))⟦(1 : ℤ)⟧,
      Triangle.mk (DerivedCategory.Q.map (DGModuleCat.ofHom i))
        (DerivedCategory.Q.map (DGModuleCat.ofHom p)) δ ∈ distTriang (DerivedCategory A) := by
  let φ : DGModuleCat.of A (Cone i) ⟶ DGModuleCat.of A Q := DGModuleCat.ofHom σ.coneDesc
  have : IsIso (DerivedCategory.Q.map φ) :=
    (DerivedCategory.isIso_Q_map_iff φ).mpr σ.isQuasiIso_coneDesc
  let T := DerivedCategory.Q.mapTriangle.obj
    (Cone.triangle (DGModuleCat.ofHom i : DGModuleCat.of A F ⟶ DGModuleCat.of A G))
  have hT : T ∈ distTriang (DerivedCategory A) :=
    (DerivedCategory.mem_distTriang_iff _).mpr ⟨_, _, _, ⟨Iso.refl _⟩⟩
  refine ⟨inv (DerivedCategory.Q.map φ) ≫ T.mor₃, isomorphic_distinguished T hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (DerivedCategory.Q.map φ)).symm
    (by simp [T]) ?_ (by
      dsimp
      erw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _)
  dsimp [T]
  rw [Category.id_comp, IsIso.comp_inv_eq, ← Functor.map_comp]
  rfl

end GradedSplitting

end DG
