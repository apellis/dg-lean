import DG.Module.TensorProductOver
import Mathlib.Algebra.Exact.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Balanced tensor product preserves right-exact sequences in the second variable. -/

open Function

namespace DG.TensorProductOver

variable {B M U V W : Type*} [Ring B] [AddCommGroup M] [Module Bᵐᵒᵖ M]
  [AddCommGroup U] [Module B U] [AddCommGroup V] [Module B V] [AddCommGroup W] [Module B W]

/-- Tensoring with a fixed right module preserves exact pairs whose second map is surjective. -/
theorem exact_map_id_of_surjective (f : U →ₗ[B] V) (g : V →ₗ[B] W)
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (map (LinearMap.id : M →ₗ[Bᵐᵒᵖ] M) f) (map LinearMap.id g) := by
  let L : TensorProductOver B M U →+ TensorProductOver B M V := map LinearMap.id f
  let R : TensorProductOver B M V →+ TensorProductOver B M W := map LinearMap.id g
  let Z := TensorProductOver B M V ⧸ L.range
  let q : TensorProductOver B M V →+ Z := QuotientAddGroup.mk' L.range
  let e := QuotientAddGroup.liftEquiv g.toAddMonoidHom.ker hg rfl
  have e_symm_apply (v : V) : e.symm (g v) = QuotientAddGroup.mk v := e.symm_apply_eq.mpr rfl
  let ff (m : M) : V →+ Z := q.comp (tmulAddHom B M V m)
  have balance_ker (m : M) : g.toAddMonoidHom.ker ≤ (ff m).ker := by
    intro v hv
    obtain ⟨u, rfl⟩ := (h v).mp hv
    change q (L (tmul B m u)) = 0
    exact (QuotientAddGroup.eq_zero_iff _).mpr (show L (tmul B m u) ∈ L.range from ⟨tmul B m u, rfl⟩)
  let F (m : M) : W →+ Z :=
    (QuotientAddGroup.lift _ (ff m) (balance_ker m)).comp e.symm.toAddMonoidHom
  have F_apply (m : M) (v : V) : F m (g v) = q (tmul B m v) := by
    change (QuotientAddGroup.lift _ (ff m) (balance_ker m)) (e.symm (g v)) = _
    rw [e_symm_apply]
    rfl
  let T : M →+ W →+ Z :=
    { toFun := F
      map_zero' := by
        ext w
        obtain ⟨v, rfl⟩ := hg w
        change F 0 (g v) = 0
        rw [F_apply, zero_tmul, map_zero]
      map_add' := by
        intro m m'
        ext w
        obtain ⟨v, rfl⟩ := hg w
        change F (m + m') (g v) = F m (g v) + F m' (g v)
        rw [F_apply, F_apply, F_apply, add_tmul, map_add] }
  let S : TensorProductOver B M W →+ Z := lift T fun b m w => by
    obtain ⟨v, rfl⟩ := hg w
    change F (MulOpposite.op b • m) (g v) = F m (b • g v)
    rw [← map_smul, F_apply, F_apply, op_smul_tmul]
  have hSq : S.comp R = q := by
    apply addHom_ext
    intro m v
    change F m (g v) = q (tmul B m v)
    exact F_apply m v
  have hRL : R.comp L = 0 := by
    apply addHom_ext
    intro m u
    change tmul B m (g (f u)) = 0
    rw [h.apply_apply_eq_zero, tmul_zero]
  intro v
  change R v = 0 ↔ v ∈ Set.range L
  constructor
  · intro hv
    have hq : q v = 0 := by rw [← hSq]; exact (congrArg S hv).trans (map_zero _)
    exact (QuotientAddGroup.eq_zero_iff _).mp hq
  · rintro ⟨u, rfl⟩
    exact DFunLike.congr_fun hRL u

end DG.TensorProductOver
