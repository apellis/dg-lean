import DG.Module.TensorProductOver

/-! The balanced tensor product distributes over a binary product in its second variable. -/

namespace DG.TensorProductOver

variable {B M N P : Type*} [Ring B] [AddCommGroup M] [Module Bᵐᵒᵖ M]
  [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]

private def prodRightTo :
    TensorProductOver B M (N × P) →+ TensorProductOver B M N × TensorProductOver B M P :=
  lift
    { toFun := fun m =>
        ((tmulAddHom B M N m).comp (AddMonoidHom.fst N P)).prod
          ((tmulAddHom B M P m).comp (AddMonoidHom.snd N P))
      map_zero' := by ext x <;> exact zero_tmul _
      map_add' := by intro m m'; ext x <;> exact add_tmul _ _ _ }
    (by intro b m x; exact Prod.ext (op_smul_tmul b m x.1) (op_smul_tmul b m x.2))

private def prodRightFromFst :
    TensorProductOver B M N →+ TensorProductOver B M (N × P) :=
  lift ((tmulAddHom B M (N × P)).compl₂ (AddMonoidHom.inl N P))
    (by intro b m x; simpa using op_smul_tmul b m (x, (0 : P)))

private def prodRightFromSnd :
    TensorProductOver B M P →+ TensorProductOver B M (N × P) :=
  lift ((tmulAddHom B M (N × P)).compl₂ (AddMonoidHom.inr N P))
    (by intro b m x; simpa using op_smul_tmul b m ((0 : N), x))

private def prodRightFrom :
    TensorProductOver B M N × TensorProductOver B M P →+ TensorProductOver B M (N × P) :=
  (prodRightFromFst (B := B) (M := M) (N := N) (P := P)).coprod prodRightFromSnd

/-- Balanced tensor product distributes over a binary product in its second variable. -/
def prodRightAddEquiv :
    TensorProductOver B M (N × P) ≃+ TensorProductOver B M N × TensorProductOver B M P where
  __ := prodRightTo
  invFun := prodRightFrom
  left_inv := by
    intro x
    change prodRightFrom (prodRightTo x) = x
    have h : (prodRightFrom (B := B) (M := M) (N := N) (P := P)).comp prodRightTo =
        AddMonoidHom.id _ := by
      apply addHom_ext
      intro m x
      change tmul B m (x.1, 0) + tmul B m (0, x.2) = tmul B m x
      rw [← tmul_add]
      simp
    exact DFunLike.congr_fun h x
  right_inv := by
    rintro ⟨x, y⟩
    change prodRightTo (prodRightFrom (x, y)) = (x, y)
    have hx : (prodRightTo (B := B) (M := M) (N := N) (P := P)).comp prodRightFromFst =
        AddMonoidHom.inl _ _ := by
      apply addHom_ext
      intro m n
      change (tmul B m n, tmul B m (0 : P)) = (tmul B m n, 0)
      rw [tmul_zero]
    have hy : (prodRightTo (B := B) (M := M) (N := N) (P := P)).comp prodRightFromSnd =
        AddMonoidHom.inr _ _ := by
      apply addHom_ext
      intro m p
      change (tmul B m (0 : N), tmul B m p) = (0, tmul B m p)
      rw [tmul_zero]
    change prodRightTo (prodRightFromFst x + prodRightFromSnd y) = (x, y)
    rw [map_add]
    change ((prodRightTo.comp prodRightFromFst) x) + ((prodRightTo.comp prodRightFromSnd) y) = _
    rw [hx, hy]
    simp

@[simp] theorem prodRightAddEquiv_tmul (m : M) (x : N × P) :
    prodRightAddEquiv (tmul B m x) = (tmul B m x.1, tmul B m x.2) := rfl

end DG.TensorProductOver
