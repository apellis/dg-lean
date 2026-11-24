import DG.Category.Tensor.Basic
import DG.Category.DoubleOpposite

/-!
# Symmetry of coends over degree-zero dg categories

Transposing the two tensor factors changes the dg category to its opposite.
On homogeneous tensors the map has the usual Koszul sign. The balancing
relations use the unchanged actions of degree-zero morphisms.
-/

noncomputable section

namespace DG.CatModule

open CategoryTheory DGOpposite
open scoped CatModule

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  (N : CatModule.{w} (DGOpposite C))

/-- The right action of a cohomological degree-zero morphism is the left
action of its opposite. -/
theorem ract_eq_op_smul_of_degree_zero {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ grading (0 : ℤ)) (n : N.obj (op Y)) :
    n <• f = homOp f • n := by
  induction n using DG.induction_on with
  | h_zero => simp
  | h_add n n' hn hn' => rw [add_ract, CatModule.smul_add, hn, hn']
  | h_homogeneous n =>
    simpa only [zero_mul, mul_zero, koszulSign_zero, one_smul] using ract_of_mem hf n.property

end DG.CatModule


namespace DG.CatTensorProduct

open CategoryTheory DGOpposite
open scoped CatModule TensorProduct

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  (N : CatModule.{w} (DGOpposite C)) (M : CatModule.{w} C)

/-- Read a left module as a right module over the dg opposite. -/
abbrev transposeLeftModule : CatModule.{w} (DGOpposite (DGOpposite C)) :=
  CatModule.precompObj (doubleUnopFunctor C) M

local notation "P" => transposeLeftModule M

private def transposeFamily (X : C) :
    N.obj (op X) →+ M.obj X →+ CatTensorProduct P N :=
  (DG.tmulAddHom _ _).compr₂
    (((mk P N).comp (ι P N (op X))).comp (tensorCommHom _ _))

private theorem transposeFamily_of_mem (X : C) {a b : ℤ} {n : N.obj (op X)} {m : M.obj X}
    (hn : n ∈ grading a) (hm : m ∈ grading b) :
    transposeFamily N M X n m = koszulSign (a*b) • tmul (op X) m n := by
  let F := (mk P N).comp (ι P N (op X))
  let m' : (P).obj (op (op X)) := m
  have hm' : m' ∈ grading b := hm
  change F (tensorCommHom _ _ (n ⊗ₜ[ℤ] m')) = _
  rw [tensorCommHom_tmul hn hm']
  exact map_units_zsmul F (koszulSign (a*b)) (m' ⊗ₜ[ℤ] n)

variable (h₀ : ∀ {X Y : C} (f : X ⟶ Y), f ∈ grading (0 : ℤ))

include h₀ in
private theorem transposeFamily_balanced : Balanced (transposeFamily N M) := by
  intro X Y f n m
  induction n using DG.induction_on with
  | h_zero => simp
  | h_add n n' hn hn' => simp only [map_add, AddMonoidHom.add_apply, hn, hn']
  | @h_homogeneous a n =>
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => simp only [CatModule.smul_add, map_add, hm, hm']
    | @h_homogeneous b m =>
      have hnf : n.val <• f ∈ grading a := by
        simpa only [add_zero] using CatModule.ract_mem_grading n.property (h₀ f)
      have hfm : f • m.val ∈ grading b := by
        simpa only [zero_add] using CatModule.smul_mem_grading (h₀ f) m.property
      have hop : homOp f ∈ grading (0 : ℤ) := h₀ f
      have hmop : (show (P).obj (op (op X)) from m.val) <• homOp f =
          (show (P).obj (op (op Y)) from f • m.val) :=
        CatModule.ract_eq_op_smul_of_degree_zero P hop m.val
      rw [transposeFamily_of_mem N M X hnf m.property,
        transposeFamily_of_mem N M Y n.property hfm,
        CatModule.ract_eq_op_smul_of_degree_zero N (h₀ f),
        ← ract_tmul (N := P) (M := N) (homOp f) m.val n.val, hmop]

/-- The signed exchange of factors on a dg coend over a degree-zero dg category. -/
def transposeHom : CatTensorProduct N M →+ CatTensorProduct P N :=
  lift (transposeFamily N M) (transposeFamily_balanced N M h₀)


private def untransposeFamily (Y : DGOpposite C) :
    (P).obj (op Y) →+ N.obj Y →+ CatTensorProduct N M :=
  (DG.tmulAddHom _ _).compr₂
    (((mk N M).comp (ι N M Y.unop)).comp (tensorCommHom _ _))

private theorem untransposeFamily_of_mem (Y : DGOpposite C) {a b : ℤ}
    {m : (P).obj (op Y)} {n : N.obj Y} (hm : m ∈ grading a) (hn : n ∈ grading b) :
    untransposeFamily N M Y m n = koszulSign (a*b) • tmul Y.unop n m := by
  let F := (mk N M).comp (ι N M Y.unop)
  let m' : M.obj Y.unop := m
  let n' : N.obj (op Y.unop) := n
  have hm' : m' ∈ grading a := hm
  have hn' : n' ∈ grading b := hn
  change F (tensorCommHom _ _ (m' ⊗ₜ[ℤ] n')) = _
  rw [tensorCommHom_tmul hm' hn']
  exact map_units_zsmul F (koszulSign (a*b)) (n' ⊗ₜ[ℤ] m')

include h₀ in
private theorem untransposeFamily_balanced : Balanced (untransposeFamily N M) := by
  intro X Y f m n
  induction m using DG.induction_on with
  | h_zero => simp
  | h_add m m' hm hm' => simp only [map_add, AddMonoidHom.add_apply, hm, hm']
  | @h_homogeneous a m =>
    induction n using DG.induction_on with
    | h_zero => simp
    | h_add n n' hn hn' => simp only [CatModule.smul_add, map_add, hn, hn']
    | @h_homogeneous b n =>
      have hfu : homUnop f ∈ grading (0 : ℤ) := h₀ (homUnop f)
      have hf : f ∈ grading (0 : ℤ) := hfu
      have hmf : m.val <• f ∈ grading a := by
        simpa only [add_zero] using CatModule.ract_mem_grading m.property hf
      have hfn : f • n.val ∈ grading b := by
        simpa only [zero_add] using CatModule.smul_mem_grading hf n.property
      let m' : M.obj Y.unop := m.val
      have hmu : m.val <• f = M.act (homUnop f) m' :=
        CatModule.ract_eq_op_smul_of_degree_zero P hf m.val
      have hnu : n.val <• homUnop f = f • n.val := by
        rw [CatModule.ract_eq_op_smul_of_degree_zero N hfu, homOp_homUnop]
      rw [untransposeFamily_of_mem N M X hmf n.property,
        untransposeFamily_of_mem N M Y m.property hfn,
        hmu, ← hnu]
      exact congrArg (fun z => koszulSign (a*b) • z)
        (ract_tmul (N := N) (M := M) (homUnop f) n.val m').symm

/-- Reverse the signed exchange on the transposed dg coend. -/
def untransposeHom : CatTensorProduct P N →+ CatTensorProduct N M :=
  lift (untransposeFamily N M) (untransposeFamily_balanced N M h₀)

include h₀ in
theorem transposeHom_tmul_of_mem (X : C) {a b : ℤ} {n : N.obj (op X)} {m : M.obj X}
    (hn : n ∈ grading a) (hm : m ∈ grading b) :
    transposeHom N M h₀ (tmul X n m) = koszulSign (a*b) • tmul (op X) m n := by
  exact (lift_tmul _ (transposeFamily_balanced N M h₀) X n m).trans
    (transposeFamily_of_mem N M X hn hm)

include h₀ in
theorem untransposeHom_tmul_of_mem (Y : DGOpposite C) {a b : ℤ}
    {m : (P).obj (op Y)} {n : N.obj Y} (hm : m ∈ grading a) (hn : n ∈ grading b) :
    untransposeHom N M h₀ (tmul Y m n) = koszulSign (a*b) • tmul Y.unop n m := by
  exact (lift_tmul _ (untransposeFamily_balanced N M h₀) Y m n).trans
    (untransposeFamily_of_mem N M Y hm hn)


include h₀ in
private theorem untranspose_transpose :
    (untransposeHom N M h₀).comp (transposeHom N M h₀) = AddMonoidHom.id _ := by
  apply addHom_ext
  intro X n m
  change untransposeHom N M h₀ (transposeHom N M h₀ (tmul X n m)) = tmul X n m
  induction n using DG.induction_on with
  | h_zero => simp
  | h_add n n' hn hn' => simp only [add_tmul, map_add, hn, hn']
  | @h_homogeneous a n =>
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => simp only [tmul_add, map_add, hm, hm']
    | @h_homogeneous b m =>
      rw [transposeHom_tmul_of_mem N M h₀ X n.property m.property, map_units_zsmul,
        untransposeHom_tmul_of_mem N M h₀ (op X) m.property n.property,
        mul_comm b a, smul_smul, Int.units_mul_self, one_smul]

include h₀ in
private theorem transpose_untranspose :
    (transposeHom N M h₀).comp (untransposeHom N M h₀) = AddMonoidHom.id _ := by
  apply addHom_ext
  intro Y m n
  change transposeHom N M h₀ (untransposeHom N M h₀ (tmul Y m n)) = tmul Y m n
  induction m using DG.induction_on with
  | h_zero => simp
  | h_add m m' hm hm' => simp only [add_tmul, map_add, hm, hm']
  | @h_homogeneous a m =>
    induction n using DG.induction_on with
    | h_zero => simp
    | h_add n n' hn hn' => simp only [tmul_add, map_add, hn, hn']
    | @h_homogeneous b n =>
      rw [untransposeHom_tmul_of_mem N M h₀ Y m.property n.property, map_units_zsmul,
        transposeHom_tmul_of_mem N M h₀ Y.unop n.property m.property,
        mul_comm b a, smul_smul, Int.units_mul_self, one_smul]

private theorem transposeFamily_mem (X : C) {a b : ℤ} {n : N.obj (op X)} {m : M.obj X}
    (hn : n ∈ grading a) (hm : m ∈ grading b) :
    transposeFamily N M X n m ∈ grading (a+b) := by
  rw [transposeFamily_of_mem N M X hn hm, Units.smul_def, add_comm]
  exact zsmul_mem (tmul_mem_grading hm hn) _

private theorem transposeFamily_d (X : C) {a : ℤ} {n : N.obj (op X)}
    (hn : n ∈ grading a) (m : M.obj X) :
    d (transposeFamily N M X n m) =
      transposeFamily N M X (d n) m + koszulSign a • transposeFamily N M X n (d m) := by
  let F := (mk P N).comp (ι P N (op X))
  let m' : (P).obj (op (op X)) := m
  let G := tensorCommHom (N.obj (op X)) ((P).obj (op (op X)))
  have hF (z : Summand P N (op X)) : d (F z) = F (d z) := by
    change d (mk P N (ι P N (op X) z)) = mk P N (ι P N (op X) (d z))
    rw [d_mk, d_ι]
  change d (F (G (n ⊗ₜ[ℤ] m'))) =
    F (G (d n ⊗ₜ[ℤ] m')) + koszulSign a • F (G (n ⊗ₜ[ℤ] d m'))
  rw [hF, ← tensorCommHom_d, DG.d_tmul_of_mem hn m', map_add, map_add,
    map_units_zsmul G, map_units_zsmul F]

/-- The signed exchange on dg coends over a category whose maps have
cohomological degree zero. -/
def transposeDGEquiv : DGAddEquiv (CatTensorProduct N M) (CatTensorProduct P N) where
  toAddEquiv := {
    toFun := transposeHom N M h₀
    invFun := untransposeHom N M h₀
    left_inv x := DFunLike.congr_fun (untranspose_transpose N M h₀) x
    right_inv x := DFunLike.congr_fun (transpose_untranspose N M h₀) x
    map_add' := map_add (transposeHom N M h₀) }
  map_mem' hx := lift_mem (transposeFamily N M) (transposeFamily_balanced N M h₀)
    (fun X _ _ _ _ hn hm => transposeFamily_mem N M X hn hm) hx
  map_d' := lift_d (transposeFamily N M) (transposeFamily_balanced N M h₀)
    (fun X _ _ hn => transposeFamily_d N M X hn)

end DG.CatTensorProduct

noncomputable section

namespace DG.CatTensorProduct
open CategoryTheory DGOpposite

universe w v u
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {N N' : CatModule.{w} (DGOpposite C)} {M M' : CatModule.{w} C}
  (f : N ⟶ N') (g : M ⟶ M')
  (h₀ : ∀ {X Y : C} (p : X ⟶ Y), p ∈ grading (0 : ℤ))

/-- The map between the restrictions along double unop. -/
def transposeLeftModuleMap (g : M ⟶ M') :
    transposeLeftModule M ⟶ transposeLeftModule M' :=
  (CatModule.precomp (doubleUnopFunctor C)).map g

/-- The signed coend exchange commutes with changes to either input module. -/
theorem transposeHom_natural :
    (transposeHom N' M' h₀).comp (map f g) =
      (map (transposeLeftModuleMap g) f).comp (transposeHom N M h₀) := by
  apply addHom_ext
  intro X n m
  simp only [AddMonoidHom.comp_apply, map_tmul]
  induction n using DG.induction_on with
  | h_zero => simp
  | h_add n n' hn hn' => simp only [map_add, add_tmul, ← hn, ← hn']
  | @h_homogeneous a n =>
    induction m using DG.induction_on with
    | h_zero => simp
    | h_add m m' hm hm' => simp only [map_add, tmul_add, ← hm, ← hm']
    | @h_homogeneous b m =>
      rw [transposeHom_tmul_of_mem N' M' h₀ X (f.map_mem n.property) (g.map_mem m.property),
        transposeHom_tmul_of_mem N M h₀ X n.property m.property]
      let F := map (transposeLeftModuleMap g) f
      have hmap : F (koszulSign (a*b) • tmul (op X) (M := N) m.val n.val) =
          koszulSign (a*b) • F (tmul (op X) (M := N) m.val n.val) :=
        map_units_zsmul F _ _
      rw [hmap]
      unfold F
      erw [map_tmul]
      rfl

end DG.CatTensorProduct
