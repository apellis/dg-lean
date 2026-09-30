import DG.Category.Homotopy.Hom
import DG.Category.Yoneda
import DG.Module.Opposite

/-!
# The dg Yoneda lemma for Hom complexes

For an object `X` of a dg category `C` and a dg module `M` over `C`, the Hom complex
`HOM_C(C(X, -), M)` (`DG.CatModule.HOM`) is isomorphic, as a dg abelian group, to `M(X)`:

  `DG.CatModule.yonedaHOM : HOM_C(C(X, -), M) ≅ M(X)`,   `z ↦ z (𝟙 X)`.

A cochain `z` of degree `n` is determined by its value at `𝟙 X`, since
`z (h) = z (h • 𝟙 X) = (-1)^{n |h|} • h • z (𝟙 X)`; conversely every `m ∈ M(X)ⁿ` defines the
cochain `h ↦ (-1)^{n |h|} • h • m` (`DG.CatModule.yonedaCochain`), the Koszul sign being that of
the exchange of `z` (of degree `n`) and `h`. Evaluation at `𝟙 X` commutes with the differentials
because `𝟙 X` is a cocycle. On degree-`0` cocycles this recovers the dg Yoneda lemma
`DG.CatModule.yonedaEquiv` (`DG.CatModule.yonedaHOM_ofHom`).
-/

open CategoryTheory DirectSum

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {X : C} {M : CatModule.{v} C}

/-- The components `h ↦ (-1)^{n |h|} • (h • m)` of `DG.CatModule.yonedaCochain`. -/
def yonedaCochainApp (m : M.obj X) (Y : C) : (X ⟶ Y) →+ M.obj Y :=
  (koszulTwist (M.act (X := X) (Y := Y))).flip m

omit [DGCategory C] in
theorem yonedaCochainApp_of_mem {n : ℤ} {m : M.obj X} (hm : m ∈ grading n) {Y : C} {i : ℤ}
    {h : X ⟶ Y} (hh : h ∈ grading i) :
    yonedaCochainApp m Y h = koszulSign (i * n) • (h • m) := by
  rw [yonedaCochainApp, AddMonoidHom.flip_apply]
  exact koszulTwist_apply_of_mem _ hh hm

theorem yonedaCochainApp_comp {n : ℤ} {m : M.obj X} (hm : m ∈ grading n) {Y Z : C} {i : ℤ}
    {f : Y ⟶ Z} (hf : f ∈ grading i) (h : X ⟶ Y) :
    yonedaCochainApp m Z (h ≫ f) = koszulSign (n * i) • (f • yonedaCochainApp m Y h) := by
  induction h using DG.induction_on with
  | h_zero => rw [Limits.zero_comp, map_zero, map_zero, smul_zero, _root_.smul_zero]
  | h_add h h' hh hh' =>
    rw [Preadditive.add_comp, map_add, hh, hh', map_add, smul_add, _root_.smul_add]
  | h_homogeneous h =>
    rw [yonedaCochainApp_of_mem hm (comp_mem_grading h.2 hf), yonedaCochainApp_of_mem hm h.2,
      smul_units_smul, smul_smul, ← koszulSign_add, comp_smul]
    congr 2
    ring

/-- The cochain `h ↦ (-1)^{n |h|} • (h • m)` of degree `n` from `C(X, -)` to `M` attached to
`m ∈ M(X)ⁿ`. -/
def yonedaCochain (n : ℤ) (m : grading (M := M.obj X) n) : Cochain (representable X) M n where
  app Y := yonedaCochainApp (m : M.obj X) Y
  map_mem' {Y i h} hh := by
    change yonedaCochainApp (m : M.obj X) Y h ∈ grading (i + n)
    rw [yonedaCochainApp_of_mem m.2 (hh : h ∈ grading (M := X ⟶ Y) i), Units.smul_def]
    exact zsmul_mem (smul_mem_grading hh m.2) _
  map_smul' {Y Z i f} hf h := yonedaCochainApp_comp m.2 hf h

@[simp]
theorem yonedaCochain_app_of_mem (n : ℤ) (m : grading (M := M.obj X) n) {Y : C} {i : ℤ}
    {h : X ⟶ Y} (hh : h ∈ grading i) :
    (yonedaCochain n m).app Y h = koszulSign (i * n) • (h • (m : M.obj X)) :=
  yonedaCochainApp_of_mem m.2 hh

theorem yonedaCochain_app_id (n : ℤ) (m : grading (M := M.obj X) n) :
    (yonedaCochain n m).app X (𝟙 X) = m := by
  rw [yonedaCochain_app_of_mem n m (id_mem_grading X), zero_mul, koszulSign_zero, one_smul]
  exact id_smul (M := M) _

/-- A cochain `z` from `C(X, -)` is determined by `z (𝟙 X)`:
`z (h) = (-1)^{n |h|} • (h • z (𝟙 X))`. -/
theorem yonedaCochain_eval {n : ℤ} (z : Cochain (representable X) M n) :
    yonedaCochain n ⟨z.app X (𝟙 X), by simpa using z.map_mem (id_mem_grading X)⟩ = z := by
  ext Y h
  induction h using DG.induction_on with
  | h_zero => rw [map_zero, map_zero]
  | h_add h h' hh hh' => rw [map_add, hh, hh', map_add]
  | h_homogeneous h =>
    rename_i i
    change yonedaCochainApp (z.app X (𝟙 X)) Y h.1 = z.app Y h.1
    rw [yonedaCochainApp_of_mem (by simpa using z.map_mem (id_mem_grading X)) h.2]
    have := z.map_smul h.2 (𝟙 X : (representable X).obj X)
    rw [representable_smul, Category.id_comp] at this
    rw [this, mul_comm]

variable (M X) in
/-- Evaluation at `𝟙 X`, on cochains of degree `n`. -/
def yonedaEvalHom (n : ℤ) : Cochain (representable X) M n →+ M.obj X where
  toFun z := z.app X (𝟙 X)
  map_zero' := rfl
  map_add' _ _ := rfl

variable (M X) in
/-- The dg Yoneda lemma for Hom complexes: `HOM_C(C(X, -), M) ≅ M(X)`, `z ↦ z (𝟙 X)`, an
isomorphism of dg abelian groups. Its inverse sends `m ∈ M(X)ⁿ` to the cochain
`h ↦ (-1)^{n |h|} • (h • m)`. -/
def yonedaHOM : DGAddEquiv (HOM (representable X) M) (M.obj X) :=
  DGAddEquiv.ofAddMonoidHom (DirectSum.toAddMonoid fun n => yonedaEvalHom X M n)
    (liftHomogeneous (grading (M := M.obj X)) fun n =>
      { toFun := fun m => DirectSum.of (fun n => Cochain (representable X) M n) n
          (yonedaCochain n m)
        map_zero' := by
          rw [← map_zero (DirectSum.of (fun n => Cochain (representable X) M n) n)]
          congr 1
          ext Y h
          change yonedaCochainApp (0 : M.obj X) Y h = 0
          rw [yonedaCochainApp, map_zero, AddMonoidHom.zero_apply]
        map_add' := fun m m' => by
          rw [← map_add]
          congr 1
          ext Y h
          change yonedaCochainApp ((m : M.obj X) + (m' : M.obj X)) Y h =
            yonedaCochainApp (m : M.obj X) Y h + yonedaCochainApp (m' : M.obj X) Y h
          rw [yonedaCochainApp, map_add, AddMonoidHom.add_apply]
          rfl })
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero]
      | of n z =>
        rw [DirectSum.toAddMonoid_of]
        change liftHomogeneous _ _ (z.app X (𝟙 X)) = _
        rw [liftHomogeneous_of_mem _ _ (by simpa using z.map_mem (id_mem_grading X))]
        exact congrArg (DirectSum.of (fun n => Cochain (representable X) M n) n)
          (yonedaCochain_eval z)
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun m => by
      induction m using DG.induction_on with
      | h_zero => rw [map_zero, map_zero]
      | h_homogeneous m =>
        rw [liftHomogeneous_coe]
        change DirectSum.toAddMonoid _ (DirectSum.of _ _ _) = _
        rw [DirectSum.toAddMonoid_of]
        exact yonedaCochain_app_id _ m
      | h_add m m' hm hm' => rw [map_add, map_add, hm, hm'])
    (fun {n x} hx => by
      obtain ⟨z, rfl⟩ := hx
      rw [DirectSum.toAddMonoid_of]
      simpa [yonedaEvalHom] using z.map_mem (id_mem_grading X))
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | of n z =>
        rw [HOM.d_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
        change (δ n (n + 1) z).app X (𝟙 X) = d (z.app X (𝟙 X))
        rw [δ_apply n (n + 1) rfl]
        change d (z.app X (𝟙 X)) - koszulSign n • z.app X (DGAddCommGroup.d (M := X ⟶ X) (𝟙 X)) =
          _
        rw [d_id, map_zero, _root_.smul_zero, sub_zero]
      | add x y hx hy => rw [d_add, map_add, map_add, hx, hy, d_add])

@[simp]
theorem yonedaHOM_of {n : ℤ} (z : Cochain (representable X) M n) :
    yonedaHOM X M (DirectSum.of (fun n => Cochain (representable X) M n) n z) = z.app X (𝟙 X) :=
  DirectSum.toAddMonoid_of _ _ _

theorem yonedaHOM_symm_of_mem {n : ℤ} {m : M.obj X} (hm : m ∈ grading n) :
    (yonedaHOM X M).symm m =
      DirectSum.of (fun n => Cochain (representable X) M n) n (yonedaCochain n ⟨m, hm⟩) :=
  liftHomogeneous_of_mem _ _ hm

/-- On degree-`0` cocycles, the Yoneda isomorphism for Hom complexes is the dg Yoneda lemma
`DG.CatModule.yonedaEquiv`. -/
theorem yonedaHOM_ofHom (φ : representable X ⟶ M) :
    yonedaHOM X M (DirectSum.of (fun n => Cochain (representable X) M n) 0 (Cochain.ofHom φ)) =
      (yonedaEquiv φ : M.obj X) :=
  yonedaHOM_of _

end CatModule

end DG
