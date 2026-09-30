import DG.Module.HomAction
import DG.Module.TensorProductOver

/-!
# The `HOM`–`⊗` adjunction

Let `A`, `B` be dg rings, `M` a dg `(A, B)`-bimodule, `N` a left dg `B`-module and `P` a left dg
`A`-module. Then `M ⊗_B N` is a left dg `A`-module (`DG.TensorProductOver.instDGModule`) and
`HOM_A(M, P)` is a left dg `B`-module (`DG.DGModule.HOM.LeftAction`, a scoped instance). This
file proves the adjunction between `M ⊗_B -` and `HOM_A(M, -)`, at the level of Hom complexes
and of morphisms of dg modules.

## Main definitions and results

* `DG.TensorProductOver.curry`: for a cochain `f` of degree `p` from `M ⊗_B N` to `P`, the
  cochain of degree `p` from `N` to `HOM_A(M, P)` with
  `curry f n m = (-1)^{|m||n|} • f (m ⊗ n)` (`DG.TensorProductOver.curry_apply_apply`); its
  inverse `DG.TensorProductOver.uncurry`, `uncurry g (m ⊗ n) = (-1)^{|m||n|} • g n m`
  (`DG.TensorProductOver.uncurry_tmul_of_mem`); `DG.TensorProductOver.curryAddEquiv`, and
  `DG.TensorProductOver.δ_curry`: currying commutes with the differentials of the Hom complexes.
* `DG.TensorProductOver.curryEquiv`: the isomorphism of dg abelian groups
  `HOM_A(M ⊗_B N, P) ≅ HOM_B(N, HOM_A(M, P))`.
* `DG.TensorProductOver.homEquiv : (M ⊗_B N →ᵈᵍ[A] P) ≃+ (N →ᵈᵍ[B] HOM_A(M, P))`: the
  adjunction on morphisms of dg modules, obtained from `curryEquiv` on degree-`0` cocycles
  through `DG.Cocycle.equivHom`; `DG.TensorProductOver.homEquiv_apply_apply` and
  `DG.TensorProductOver.homEquiv_symm_apply_tmul` give it on homogeneous elements.
* Naturality: `DG.TensorProductOver.homEquiv_comp_lTensor` (in `N`, with
  `DG.TensorProductOver.lTensor A M g = 1 ⊗ g`) and `DG.TensorProductOver.homEquiv_comp`
  (in `P`, with `DG.DGModule.HOM.LeftAction.postcomp`).

## Sign convention

The sign in `curry f n m = (-1)^{|m||n|} • f (m ⊗ n)` is the Koszul sign of the exchange of `m`
and `n`. Writing the sign as `(-1)^{ε(|m|, |n|, |f|)}`, the requirement that `curry f n` be
`A`-linear with the Koszul sign forces `ε = |m||n| + c(|n|, |f|)`; the requirement that
`curry f` be `B`-linear with the Koszul sign, for the action
`(b • g) m = (-1)^{|b|(|g| + |m|)} • g (m • b)` of `B` on `HOM_A(M, P)`, forces `c` to be
independent of `|n|`; and the compatibility `δ (curry f) = curry (δ f)` with the differentials
`δ f = d ∘ f - (-1)^{|f|} • f ∘ d` forces `c` to be independent of `|f|`. Thus the sign is
`(-1)^{|m||n|}` up to a global sign, which is taken to be `+1`.
-/

open DirectSum MulOpposite

noncomputable section

namespace DG

/-! ### The adjunction between `M ⊗_B -` and `HOM_A(M, -)` -/

namespace TensorProductOver

open DGModule DGModule.HOM DGModule.HOM.LeftAction

variable {A B : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [DGBimodule A B M]
  [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

section Curry

variable {p : ℤ} (f : Cochain A (TensorProductOver B M N) P p)

/-- For `f` of degree `p` on `M ⊗_B N` and `n ∈ Nʲ`, the cochain `m ↦ (-1)^{|m| j} f (m ⊗ n)` of
degree `j + p` on `M`. -/
def curryApply (j : ℤ) (n : grading (M := N) j) : Cochain A M P (j + p) where
  toAddMonoidHom := (f : TensorProductOver B M N →+ P).comp
    (((tmulAddHom B M N).flip (n : N)).comp (gradeSign M j))
  map_mem' i m hm := by
    have := f.map_mem (tmul_mem_grading (A := B) (gradeSign_mem j hm) n.2)
    rwa [add_assoc] at this
  map_smul' {l a} ha m := by
    show f (tmul B (gradeSign M j (a • m)) n) = _ • (a • f (tmul B (gradeSign M j m) n))
    rw [gradeSign_smul j ha, units_smul_tmul, Cochain.map_units_smul, ← smul_tmul,
      f.map_smul ha, smul_smul, ← koszulSign_add, add_mul]

theorem curryApply_apply (j : ℤ) (n : grading (M := N) j) (m : M) :
    curryApply f j n m = f (tmul B (gradeSign M j m) n) := rfl

theorem curryApply_apply_of_mem (j : ℤ) (n : grading (M := N) j) {i : ℤ} {m : M}
    (hm : m ∈ grading i) : curryApply f j n m = koszulSign (j * i) • f (tmul B m n) := by
  rw [curryApply_apply, gradeSign_of_mem j hm, units_smul_tmul, Cochain.map_units_smul]

/-- `DG.TensorProductOver.curryApply` as an additive map in `n`. -/
def curryApplyHom (j : ℤ) : grading (M := N) j →+ Cochain A M P (j + p) where
  toFun := curryApply f j
  map_zero' := Cochain.ext fun m => by simp [curryApply_apply]
  map_add' n n' := Cochain.ext fun m => by
    simp [curryApply_apply, tmul_add, Cochain.add_apply]

/-- The additive map `N →+ HOM_A(M, P)` underlying the currying of `f`. -/
def curryFun : N →+ HOM A M P :=
  liftHomogeneous (grading (M := N)) fun j =>
    (DirectSum.of (fun n => Cochain A M P n) (j + p)).comp (curryApplyHom f j)

theorem curryFun_of_mem {j : ℤ} {n : N} (hn : n ∈ grading j) :
    curryFun f n = DirectSum.of (fun n => Cochain A M P n) (j + p) (curryApply f j ⟨n, hn⟩) :=
  liftHomogeneous_of_mem _ _ hn

end Curry

section Curry

variable [DGModule A P] {p : ℤ} (f : Cochain A (TensorProductOver B M N) P p)

/-- The currying of a cochain `f` of degree `p` on `M ⊗_B N`: the cochain of degree `p` on `N`
with values in `HOM_A(M, P)` sending `n ∈ Nʲ` to the cochain `m ↦ (-1)^{|m| j} f (m ⊗ n)` of
degree `j + p`. The sign is the Koszul sign of the exchange of `m` and `n`. -/
def curry : Cochain B N (HOM A M P) p where
  toAddMonoidHom := curryFun f
  map_mem' j n hn := by
    show curryFun f n ∈ _
    rw [curryFun_of_mem f hn]
    exact of_mem_summand _ _
  map_smul' {l b} hb n := by
    show curryFun f (b • n) = _ • (b • curryFun f n)
    induction n using DG.induction_on with
    | h_zero => simp
    | @h_homogeneous j n =>
      rw [curryFun_of_mem f (smul_mem_grading hb n.2), curryFun_of_mem f n.2, smul_of hb,
        ← HOM.of_units_smul]
      refine HOM.of_congr (by ring) fun m => ?_
      induction m using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous i m =>
        rw [Cochain.units_smul_apply, Cochain.units_smul_apply, Cochain.comp_apply,
          DGBimodule.rightMulCochain_apply, DGBimodule.signedRightMul_of_mem _ _ m.2,
          Cochain.map_units_smul, curryApply_apply_of_mem _ _ _ m.2,
          curryApply_apply_of_mem _ _ _ (op_smul_mem_grading hb m.2), op_smul_tmul,
          smul_smul, smul_smul, smul_smul, ← koszulSign_add, ← koszulSign_add, ← koszulSign_add]
        exact koszulSign_smul_congr ⟨-(p * l + l * j), by ring⟩ _
      | h_add m m' hm hm' => rw [map_add, hm, hm', map_add]
    | h_add n n' hn hn' => rw [smul_add, map_add, hn, hn', map_add, smul_add, smul_add]

theorem curry_of_mem {j : ℤ} {n : N} (hn : n ∈ grading j) :
    curry f n = DirectSum.of (fun n => Cochain A M P n) (j + p) (curryApply f j ⟨n, hn⟩) :=
  curryFun_of_mem f hn

/-- The currying on homogeneous elements: for `n ∈ Nʲ` and `m ∈ Mⁱ`,
`curry f n m = (-1)^{i j} • f (m ⊗ n)`. -/
theorem curry_apply_apply {j i : ℤ} {n : N} (hn : n ∈ grading j) {m : M} (hm : m ∈ grading i) :
    curry f n (j + p) m = koszulSign (j * i) • f (tmul B m n) := by
  rw [curry_of_mem f hn, DirectSum.of_eq_same, curryApply_apply_of_mem _ _ _ hm]

end Curry

section Uncurry

variable [DGModule A P] {p : ℤ} (g : Cochain B N (HOM A M P) p)

/-- For `n ∈ Nʲ`, the additive map `m ↦ (-1)^{j |m|} • g n m`, where `g n` is viewed as a
cochain of degree `j + p`. -/
def uncurryAux (j : ℤ) : grading (M := N) j →+ (M →+ P) where
  toFun n := ((g n (j + p) : Cochain A M P (j + p)) : M →+ P).comp (gradeSign M j)
  map_zero' := by ext m; simp
  map_add' n n' := by ext m; simp

/-- The bi-additive map `N →+ M →+ P` underlying the uncurrying of `g`. -/
def uncurryBil : N →+ M →+ P :=
  liftHomogeneous (grading (M := N)) (uncurryAux g)

omit [DGModule B N] in
theorem uncurryBil_of_mem {j : ℤ} {n : N} (hn : n ∈ grading j) (m : M) :
    uncurryBil g n m = g n (j + p) (gradeSign M j m) := by
  rw [uncurryBil, liftHomogeneous_of_mem _ _ hn]
  rfl

omit [DGModule B N] in
theorem uncurryBil_of_mem_of_mem {j i : ℤ} {n : N} (hn : n ∈ grading j) {m : M}
    (hm : m ∈ grading i) : uncurryBil g n m = koszulSign (j * i) • g n (j + p) m := by
  rw [uncurryBil_of_mem g hn, gradeSign_of_mem j hm, Cochain.map_units_smul]

theorem uncurryBil_balanced (b : B) (m : M) (n : N) :
    uncurryBil g n (op b • m) = uncurryBil g (b • n) m := by
  induction b using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous l b =>
    induction n using DG.induction_on with
    | h_zero => simp
    | @h_homogeneous j n =>
      induction m using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous i m =>
        have hgn := HOM.eq_of_mem (g.map_mem n.2)
        have hgbn : g ((b : B) • (n : N)) = koszulSign (p * l) •
            ((b : B) • (DirectSum.of (fun n => Cochain A M P n) (j + p) (g n (j + p)) :
              HOM A M P)) := by
          rw [g.map_smul b.2, ← hgn]
        rw [uncurryBil_of_mem_of_mem g n.2 (op_smul_mem_grading b.2 m.2),
          uncurryBil_of_mem_of_mem g (smul_mem_grading b.2 n.2) m.2, hgbn, smul_of b.2,
          ← HOM.of_units_smul, add_assoc l j p, DirectSum.of_eq_same, Cochain.units_smul_apply,
          Cochain.units_smul_apply, Cochain.comp_apply, DGBimodule.rightMulCochain_apply,
          DGBimodule.signedRightMul_of_mem _ _ m.2, Cochain.map_units_smul, smul_smul, smul_smul,
          smul_smul, ← koszulSign_add, ← koszulSign_add, ← koszulSign_add]
        exact koszulSign_smul_congr ⟨-(i * l + l * p), by ring⟩ _
      | h_add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add]
    | h_add n n' hn hn' => rw [map_add, AddMonoidHom.add_apply, hn, hn', smul_add, map_add,
        AddMonoidHom.add_apply]
  | h_add b b' hb hb' => rw [op_add, add_smul, map_add, hb, hb', add_smul, map_add,
      AddMonoidHom.add_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The uncurrying of a cochain `g` of degree `p` on `N` with values in `HOM_A(M, P)`: the
cochain of degree `p` on `M ⊗_B N` sending `m ⊗ n`, for `m ∈ Mⁱ` and `n ∈ Nʲ`, to
`(-1)^{i j} • g n m`. It is inverse to `DG.TensorProductOver.curry`. -/
def uncurry : Cochain A (TensorProductOver B M N) P p where
  toAddMonoidHom := lift (uncurryBil g).flip fun b m n => uncurryBil_balanced g b m n
  map_mem' k t ht := lift_mem_add _ _ p (fun {i j m n} hm hn => by
    rw [AddMonoidHom.flip_apply, uncurryBil_of_mem g hn, add_assoc]
    exact (g n (j + p)).map_mem (gradeSign_mem j hm)) ht
  map_smul' {l a} ha t := by
    show lift _ _ (a • t) = _ • (a • lift _ _ t)
    induction t using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n =>
      rw [smul_tmul, lift_tmul, lift_tmul, AddMonoidHom.flip_apply, AddMonoidHom.flip_apply]
      induction n using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous j n =>
        rw [uncurryBil_of_mem g n.2, uncurryBil_of_mem g n.2, gradeSign_smul j ha,
          Cochain.map_units_smul, (g n (j + p)).map_smul ha, smul_smul, ← koszulSign_add]
        exact koszulSign_smul_congr ⟨j * l, by ring⟩ _
      | h_add n n' hn hn' => rw [map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, hn,
          hn', smul_add, smul_add]
    | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_add, smul_add]

theorem uncurry_tmul (m : M) (n : N) : uncurry g (tmul B m n) = uncurryBil g n m := rfl

/-- The uncurrying on homogeneous elements: for `m ∈ Mⁱ` and `n ∈ Nʲ`,
`uncurry g (m ⊗ n) = (-1)^{i j} • g n m`. -/
theorem uncurry_tmul_of_mem {i j : ℤ} {m : M} (hm : m ∈ grading i) {n : N}
    (hn : n ∈ grading j) : uncurry g (tmul B m n) = koszulSign (j * i) • g n (j + p) m :=
  uncurryBil_of_mem_of_mem g hn hm

end Uncurry

section Equiv

variable [DGModule A P] {p : ℤ}

@[simp]
theorem uncurry_curry (f : Cochain A (TensorProductOver B M N) P p) : uncurry (curry f) = f := by
  ext t
  induction t using TensorProductOver.induction_on with
  | zero => simp
  | tmul m n =>
    rw [uncurry_tmul]
    induction n using DG.induction_on with
    | h_zero => simp
    | @h_homogeneous j n =>
      induction m using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous i m =>
        rw [uncurryBil_of_mem_of_mem _ n.2 m.2, curry_apply_apply f n.2 m.2, smul_smul,
          Int.units_mul_self, one_smul]
      | h_add m m' hm hm' => rw [map_add, hm, hm', add_tmul, map_add]
    | h_add n n' hn hn' => rw [map_add, AddMonoidHom.add_apply, hn, hn', tmul_add, map_add]
  | add t t' ht ht' => rw [map_add, ht, ht', map_add]

@[simp]
theorem curry_uncurry (g : Cochain B N (HOM A M P) p) : curry (uncurry g) = g := by
  ext n : 1
  induction n using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j n =>
    rw [curry_of_mem _ n.2, HOM.eq_of_mem (g.map_mem n.2)]
    refine HOM.of_congr rfl fun m => ?_
    rw [curryApply_apply, uncurry_tmul, uncurryBil_of_mem g n.2, gradeSign_gradeSign]
  | h_add n n' hn hn' => rw [map_add, hn, hn', map_add]

theorem curry_add (f f' : Cochain A (TensorProductOver B M N) P p) :
    curry (f + f') = curry f + curry f' := by
  ext n : 1
  induction n using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j n =>
    rw [Cochain.add_apply, curry_of_mem _ n.2, curry_of_mem _ n.2, curry_of_mem _ n.2,
      ← map_add]
    exact HOM.of_congr rfl fun _ => rfl
  | h_add n n' hn hn' => simp only [map_add, hn, hn']

variable (A B M N P p)

/-- Currying, as an additive equivalence between the cochains of degree `p` from `M ⊗_B N` to
`P` over `A` and the cochains of degree `p` from `N` to `HOM_A(M, P)` over `B`. -/
def curryAddEquiv :
    Cochain A (TensorProductOver B M N) P p ≃+ Cochain B N (HOM A M P) p where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_add' := curry_add

variable {A B M N P p}

@[simp]
theorem curryAddEquiv_apply (f : Cochain A (TensorProductOver B M N) P p) :
    curryAddEquiv A B M N P p f = curry f := rfl

@[simp]
theorem curryAddEquiv_symm_apply (g : Cochain B N (HOM A M P) p) :
    (curryAddEquiv A B M N P p).symm g = uncurry g := rfl

/-- Currying commutes with the differentials of the Hom complexes. -/
theorem δ_curry (q : ℤ) (f : Cochain A (TensorProductOver B M N) P p) :
    δ p q (curry f) = curry (δ p q f) := by
  by_cases hpq : p + 1 = q
  swap
  · rw [δ_shape _ _ hpq, δ_shape _ _ hpq]
    exact (map_zero (curryAddEquiv A B M N P q)).symm
  subst hpq
  ext n : 1
  induction n using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j n =>
    rw [δ_apply _ _ rfl, curry_of_mem _ n.2, curry_of_mem _ n.2, curry_of_mem _ (d_mem n.2),
      HOM.d_of, HOM.of_congr (show j + p + 1 = j + (p + 1) by ring)
        (g := δ (j + p) (j + (p + 1)) (curryApply f j n)) (fun _ => by
          rw [δ_apply _ _ rfl, δ_apply _ _ (by ring)]),
      HOM.of_congr (show j + 1 + p = j + (p + 1) by ring)
        (g := (Cochain.id A P).comp (curryApply f (j + 1) ⟨d (n : N), d_mem n.2⟩) (by ring))
        (fun _ => rfl), ← HOM.of_units_smul, ← map_sub]
    congr 1
    ext m
    induction m using DG.induction_on with
    | h_zero => simp
    | @h_homogeneous i m =>
      rw [Cochain.sub_apply, Cochain.units_smul_apply, Cochain.comp_apply, Cochain.id_apply,
        δ_apply _ _ (by ring), curryApply_apply_of_mem _ _ _ m.2,
        curryApply_apply_of_mem _ _ _ (d_mem m.2), curryApply_apply_of_mem _ _ _ m.2,
        curryApply_apply_of_mem _ _ _ m.2, δ_apply _ _ rfl, d_tmul_of_mem m.2]
      simp only [map_add, Cochain.map_units_smul, smul_sub, smul_add,
        smul_smul, mul_add, add_mul, mul_one, one_mul, koszulSign_add, map_units_zsmul]
      rcases Int.units_eq_one_or (koszulSign (j * i)) with h₁ | h₁ <;>
      rcases Int.units_eq_one_or (koszulSign j) with h₂ | h₂ <;>
      rcases Int.units_eq_one_or (koszulSign p) with h₃ | h₃ <;>
      rcases Int.units_eq_one_or (koszulSign i) with h₄ | h₄ <;>
      simp [h₁, h₂, h₃, h₄] <;> abel
    | h_add m m' hm hm' => rw [map_add, hm, hm', map_add]
  | h_add n n' hn hn' => rw [map_add, hn, hn', map_add]

end Equiv

section HOMEquiv

variable [DGModule A P]

variable (A B M N P)

/-- The additive map `HOM_A(M ⊗_B N, P) →+ HOM_B(N, HOM_A(M, P))`, currying in each degree. -/
def curryHOM : HOM A (TensorProductOver B M N) P →+ HOM B N (HOM A M P) :=
  DirectSum.toAddMonoid fun p =>
    (DirectSum.of (fun p => Cochain B N (HOM A M P) p) p).comp
      (curryAddEquiv A B M N P p).toAddMonoidHom

/-- The additive map `HOM_B(N, HOM_A(M, P)) →+ HOM_A(M ⊗_B N, P)`, uncurrying in each degree. -/
def uncurryHOM : HOM B N (HOM A M P) →+ HOM A (TensorProductOver B M N) P :=
  DirectSum.toAddMonoid fun p =>
    (DirectSum.of (fun p => Cochain A (TensorProductOver B M N) P p) p).comp
      (curryAddEquiv A B M N P p).symm.toAddMonoidHom

variable {A B M N P}

@[simp]
theorem curryHOM_of {p : ℤ} (f : Cochain A (TensorProductOver B M N) P p) :
    curryHOM A B M N P (DirectSum.of _ p f) = DirectSum.of _ p (curry f) := by
  simp [curryHOM]

@[simp]
theorem uncurryHOM_of {p : ℤ} (g : Cochain B N (HOM A M P) p) :
    uncurryHOM A B M N P (DirectSum.of _ p g) = DirectSum.of _ p (uncurry g) := by
  simp [uncurryHOM]

variable (A B M N P)

/-- The `HOM`–`⊗` adjunction at the level of Hom complexes: for a dg `(A, B)`-bimodule `M`, a
left dg `B`-module `N` and a left dg `A`-module `P`, the isomorphism of dg abelian groups
`HOM_A(M ⊗_B N, P) ≅ HOM_B(N, HOM_A(M, P))` given by currying,
`f ↦ (n ↦ (m ↦ (-1)^{|m||n|} • f (m ⊗ n)))` (`DG.TensorProductOver.curry_apply_apply`). The
sign is the Koszul sign of the exchange of `m` and `n`; it is the unique sign of the form
`(-1)^{ε(|m|, |n|, |f|)}` making the curried map Koszul-linear in `m` and `n` and compatible
with the differentials, up to a global sign. -/
def curryEquiv :
    DGAddEquiv (HOM A (TensorProductOver B M N) P) (HOM B N (HOM A M P)) :=
  DGAddEquiv.ofAddMonoidHom (curryHOM A B M N P) (uncurryHOM A B M N P)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of p f => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of p g => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (by
      rintro k _ ⟨f, rfl⟩
      rw [curryHOM_of]
      exact of_mem_summand _ _)
    (fun x => by
      induction x using DirectSum.induction_on with
      | zero => simp
      | of p f => rw [HOM.d_of, curryHOM_of, curryHOM_of, HOM.d_of, δ_curry]
      | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add])

variable {A B M N P}

@[simp]
theorem curryEquiv_of {p : ℤ} (f : Cochain A (TensorProductOver B M N) P p) :
    curryEquiv A B M N P (DirectSum.of _ p f) = DirectSum.of _ p (curry f) :=
  curryHOM_of f

@[simp]
theorem curryEquiv_symm_of {p : ℤ} (g : Cochain B N (HOM A M P) p) :
    (curryEquiv A B M N P).symm (DirectSum.of _ p g) = DirectSum.of _ p (uncurry g) :=
  uncurryHOM_of g

end HOMEquiv

section HomEquiv

variable [DGModule A P]

/-- The currying of a `0`-cocycle is a `0`-cocycle. -/
theorem curry_mem_cocycle {f : Cochain A (TensorProductOver B M N) P 0}
    (hf : f ∈ cocycle A (TensorProductOver B M N) P 0) :
    curry f ∈ cocycle B N (HOM A M P) 0 := by
  rw [Cocycle.mem_iff 1 (zero_add 1)] at hf ⊢
  rw [δ_curry, hf]
  exact map_zero (curryAddEquiv A B M N P 1)

/-- The uncurrying of a `0`-cocycle is a `0`-cocycle. -/
theorem uncurry_mem_cocycle {g : Cochain B N (HOM A M P) 0}
    (hg : g ∈ cocycle B N (HOM A M P) 0) :
    uncurry g ∈ cocycle A (TensorProductOver B M N) P 0 := by
  rw [← curry_uncurry g] at hg
  rw [Cocycle.mem_iff 1 (zero_add 1)] at hg ⊢
  rw [δ_curry] at hg
  apply (curryAddEquiv A B M N P 1).injective
  rw [curryAddEquiv_apply, hg, map_zero]

variable (A B M N P)

/-- Currying restricted to `0`-cocycles. -/
def curryCocycleEquiv :
    Cocycle A (TensorProductOver B M N) P 0 ≃+ Cocycle B N (HOM A M P) 0 where
  toFun z := ⟨curry (z : Cochain A (TensorProductOver B M N) P 0), curry_mem_cocycle z.2⟩
  invFun z := ⟨uncurry (z : Cochain B N (HOM A M P) 0), uncurry_mem_cocycle z.2⟩
  left_inv z := Subtype.ext (uncurry_curry (z : Cochain A (TensorProductOver B M N) P 0))
  right_inv z := Subtype.ext (curry_uncurry (z : Cochain B N (HOM A M P) 0))
  map_add' z z' := Subtype.ext (curry_add (z : Cochain A (TensorProductOver B M N) P 0) z')

/-- The `HOM`–`⊗` adjunction for morphisms of dg modules: for a dg `(A, B)`-bimodule `M`, a left
dg `B`-module `N` and a left dg `A`-module `P`, morphisms of dg `A`-modules `M ⊗_B N → P`
correspond to morphisms of dg `B`-modules `N → HOM_A(M, P)`. A morphism `φ` corresponds to
`n ↦ (m ↦ (-1)^{|m||n|} • φ (m ⊗ n))` (`DG.TensorProductOver.homEquiv_apply_apply`). This is
the restriction of `DG.TensorProductOver.curryEquiv` to degree-`0` cocycles. -/
def homEquiv :
    (TensorProductOver B M N →ᵈᵍ[A] P) ≃+ (N →ᵈᵍ[B] HOM A M P) :=
  ((Cocycle.equivHom A (TensorProductOver B M N) P).trans
    (curryCocycleEquiv A B M N P)).trans (Cocycle.equivHom B N (HOM A M P)).symm

variable {A B M N P}

theorem homEquiv_apply (φ : TensorProductOver B M N →ᵈᵍ[A] P) (n : N) :
    homEquiv A B M N P φ n = curry (Cochain.ofHom φ) n := rfl

theorem homEquiv_symm_apply (ψ : N →ᵈᵍ[B] HOM A M P) (t : TensorProductOver B M N) :
    (homEquiv A B M N P).symm ψ t = uncurry (Cochain.ofHom ψ) t := rfl

/-- The morphism `N → HOM_A(M, P)` corresponding to `φ : M ⊗_B N → P`, on homogeneous
elements: for `n ∈ Nʲ` and `m ∈ Mⁱ`, `(homEquiv φ n) m = (-1)^{i j} • φ (m ⊗ n)`. -/
theorem homEquiv_apply_apply (φ : TensorProductOver B M N →ᵈᵍ[A] P) {j i : ℤ} {n : N}
    (hn : n ∈ grading j) {m : M} (hm : m ∈ grading i) :
    homEquiv A B M N P φ n j m = koszulSign (j * i) • φ (tmul B m n) := by
  rw [homEquiv_apply, curry_of_mem _ hn,
    HOM.of_congr (add_zero j) (g := (Cochain.id A P).comp (curryApply (Cochain.ofHom φ) j ⟨n, hn⟩)
      (by rw [add_zero, add_zero])) (fun _ => rfl),
    DirectSum.of_eq_same, Cochain.comp_apply, Cochain.id_apply, curryApply_apply_of_mem _ _ _ hm,
    Cochain.ofHom_apply]

/-- The morphism `M ⊗_B N → P` corresponding to `ψ : N → HOM_A(M, P)`, on homogeneous
elements: for `m ∈ Mⁱ` and `n ∈ Nʲ`, `homEquiv.symm ψ (m ⊗ n) = (-1)^{i j} • (ψ n) m`. -/
theorem homEquiv_symm_apply_tmul (ψ : N →ᵈᵍ[B] HOM A M P) {i j : ℤ} {m : M}
    (hm : m ∈ grading i) {n : N} (hn : n ∈ grading j) :
    (homEquiv A B M N P).symm ψ (tmul B m n) = koszulSign (j * i) • ψ n (j + 0) m := by
  rw [homEquiv_symm_apply, uncurry_tmul_of_mem _ hm hn, Cochain.ofHom_apply]

end HomEquiv

/-! ### Naturality -/

section Naturality

variable [DGModule A P]

variable (A M) in
/-- The map `1 ⊗ g : M ⊗_B N' → M ⊗_B N` induced by a morphism of dg `B`-modules `g`, as a
morphism of dg `A`-modules. -/
def lTensor {N' : Type*} [AddCommGroup N'] [DGAddCommGroup N'] [Module B N'] [DGModule B N']
    (g : N' →ᵈᵍ[B] N) : TensorProductOver B M N' →ᵈᵍ[A] TensorProductOver B M N where
  toFun := map (LinearMap.id : M →ₗ[Bᵐᵒᵖ] M) g.toLinearMap
  map_add' := map_add _
  map_smul' a t := by
    rw [RingHom.id_apply]
    induction t using induction_on with
    | zero => simp
    | tmul m n => rfl
    | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_add]
  map_mem' ht := map_mem _ _ (fun hm => hm) (fun hn => g.map_mem hn) ht
  map_d' t := map_d_of_dgModuleHom _ g (fun hm => hm) (fun _ => rfl) t

@[simp]
theorem lTensor_tmul {N' : Type*} [AddCommGroup N'] [DGAddCommGroup N'] [Module B N']
    [DGModule B N'] (g : N' →ᵈᵍ[B] N) (m : M) (n : N') :
    lTensor A M g (tmul B m n) = tmul B m (g n) := rfl

/-- Naturality of the `HOM`–`⊗` adjunction in `N`: for `g : N' → N`, the morphism corresponding
to `φ ∘ (1 ⊗ g)` is the composition of `g` with the morphism corresponding to `φ`. -/
theorem homEquiv_comp_lTensor {N' : Type*} [AddCommGroup N'] [DGAddCommGroup N'] [Module B N']
    [DGModule B N'] (φ : TensorProductOver B M N →ᵈᵍ[A] P) (g : N' →ᵈᵍ[B] N) :
    homEquiv A B M N' P (φ.comp (lTensor A M g)) = (homEquiv A B M N P φ).comp g := by
  ext n : 1
  rw [DGModuleHom.comp_apply, homEquiv_apply, homEquiv_apply]
  induction n using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j n =>
    rw [curry_of_mem _ n.2, curry_of_mem _ (g.map_mem n.2)]
    exact HOM.of_congr rfl fun _ => rfl
  | h_add n n' hn hn' => rw [map_add, hn, hn', map_add, map_add]

end Naturality

end TensorProductOver

namespace TensorProductOver

open DGModule DGModule.HOM DGModule.HOM.LeftAction

variable {A B : Type*} {M N P P' : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [DGBimodule A B M]
  [AddCommGroup N] [DGAddCommGroup N] [Module B N] [DGModule B N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  [AddCommGroup P'] [DGAddCommGroup P'] [Module A P'] [DGModule A P']

/-- Naturality of the `HOM`–`⊗` adjunction in `P`: for `h : P → P'`, the morphism corresponding
to `h ∘ φ` is the composition of the morphism corresponding to `φ` with
`h ∘ - : HOM_A(M, P) → HOM_A(M, P')`. -/
theorem homEquiv_comp (φ : TensorProductOver B M N →ᵈᵍ[A] P) (h : P →ᵈᵍ[A] P') :
    homEquiv A B M N P' (h.comp φ) = (postcomp B M h).comp (homEquiv A B M N P φ) := by
  ext n : 1
  rw [DGModuleHom.comp_apply, homEquiv_apply, homEquiv_apply]
  induction n using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous j n =>
    rw [curry_of_mem _ n.2, curry_of_mem _ n.2, postcomp_of]
    exact HOM.of_congr rfl fun _ => rfl
  | h_add n n' hn hn' => rw [map_add, hn, hn', map_add, map_add]

end TensorProductOver

end DG
