import Mathlib.Algebra.Module.GradedModule
import DG.Algebra.Hom
import DG.Module.EndBimodule
import DG.Module.Equiv

/-!
# Module structures on the Hom complex

Let `A` be a dg ring and `M`, `P` dg `A`-modules. This file makes the Hom complex `HOM_A(M, P)`
(`DG.DGModule.HOM A M P`) a left dg module over the endomorphism dg ring `END_A(M)` and, for a
dg `(A, B)`-bimodule `M`, a left dg `B`-module; it proves the Yoneda isomorphism
`HOM_A(A, P) ≅ P` for the regular bimodule.

## Main definitions and results

* `DG.DGModule.HOM.instGmodule`, `DG.DGModule.HOM.instDGModule`: `HOM_A(M, P)` is a left dg
  `END_A(M)`-module for the action `F • f = (-1)^{|F||f|} • f ∘ F` on homogeneous elements
  (`DG.DGModule.HOM.of_smul_of`), with the Leibniz rule `DG.DGModule.HOM.d_of_smul_of`. For
  `P = M` this is the product `f * g = (-1)^{|f||g|} • g ∘ f` of `END_A(M)`: the graded action
  agrees with Mathlib's `DirectSum.GSemiring.toGmodule`.
* `DG.DGBimodule.toENDDGRingHom`: for a dg `(A, B)`-bimodule `M`, the ring homomorphism
  `DG.DGBimodule.toEND : B →+* END_A(M)` as a morphism of dg rings.
* `DG.DGModule.HOM.LeftAction.instModule`, `DG.DGModule.HOM.LeftAction.instDGModule` (scoped):
  for a dg `(A, B)`-bimodule `M` and a left dg `A`-module `P`, `HOM_A(M, P)` is a left dg
  `B`-module by restriction of scalars along `B →ᵈᵍ+* END_A(M)`. Explicitly, for `b ∈ Bᵏ`, a
  cochain `f` of degree `n` and `x ∈ Mⁱ`, `(b • f) x = (-1)^{k (n + i)} • f (x • b)`
  (`DG.DGModule.HOM.LeftAction.smul_of_apply`).
* `DG.DGModule.HOM.postcompEND`, `DG.DGModule.HOM.LeftAction.postcomp`: postcomposition
  `f ↦ h ∘ f` with a morphism of dg modules `h : P → P'`, as a morphism of dg `END_A(M)`- and
  `B`-modules.
* `DG.DGModule.HOM.evalOneEquiv : HOM_A(A, P) ≃ᵈᵍ[A] P`: evaluation at `1` is an isomorphism of
  dg `A`-modules, `A` acting on `HOM_A(A, P)` through the right action of `A` on itself. The
  inverse sends `p ∈ Pⁿ` to the cochain `x ↦ (-1)^{n |x|} • (x • p)`.
* `DG.gradeSign M j`: the sign automorphism `x ↦ (-1)^{j |x|} • x` of a dg abelian group.

## Sign conventions

The sign in `(b • f) x = (-1)^{|b| (|f| + |x|)} • f (x • b)` is the Koszul sign of moving `b`
past `f` and `x`. It is forced, up to the choice of the global form, by the three requirements
(for a sign `(-1)^{ε}` with `ε` depending on `|b|`, `|f|`, `|x|`):

1. `b • f` is `A`-linear of degree `|b| + |f|` with the Koszul sign: this holds if and only if
   `ε = |b| |x| + c(|b|, |f|)`;
2. `(b b') • f = b • (b' • f)`: with `c = 0` the two sides differ by `(-1)^{|b||b'|}`, while
   `c(|b|, |f|) = |b| |f|` satisfies it;
3. the Leibniz rule `δ (b • f) = d b • f + (-1)^{|b|} • b • δ f`: it holds for
   `c(|b|, |f|) = |b| |f|` (and fails, for instance, for `c(|b|, |f|) = |b| |f| + |b|`).

Equivalently, `B` acts through `DG.DGBimodule.toEND`, which sends `b ∈ Bᵏ` to the cochain
`x ↦ (-1)^{k |x|} • (x • b)`, and `END_A(M)` acts by `F • f = (-1)^{|F||f|} • f ∘ F`, the
Koszul-signed precomposition.

## Implementation notes

The `B`-module structures are scoped instances (`open scoped DG.DGModule.HOM.LeftAction`): for
`B = END_A(M)`, with `M` a dg `(A, END_A(M))`-bimodule (`DG.DGModule.END.instDGBimodule`), they
would give a second `END_A(M)`-module structure on `HOM_A(M, P)`, equal to the one of
`DG.DGModule.HOM.instGmodule` only up to propositional equality.
-/

open DirectSum MulOpposite

noncomputable section

namespace DG

/-! ### Koszul signs attached to degrees -/

/-- Two Koszul signs whose degrees have the same parity act in the same way. -/
theorem koszulSign_smul_congr {X : Type*} [AddCommGroup X] {a b : ℤ} (h : Even (a - b))
    (x : X) : koszulSign a • x = koszulSign b • x := by
  rw [show koszulSign a = koszulSign b from (Int.negOnePow_eq_iff a b).mpr h]

section GradeSign

variable (M : Type*) [AddCommGroup M] [DGAddCommGroup M]

/-- The sign automorphism `x ↦ (-1)^{j |x|} • x` of a dg abelian group, for `j : ℤ`. For odd `j`
it is the grade involution `DG.gradeInvolution`, for even `j` the identity. -/
def gradeSign (j : ℤ) : M →+ M :=
  liftHomogeneous (grading (M := M)) fun i =>
    ((koszulSign (j * i) : ℤ) • (grading (M := M) i).subtype)

variable {M}

theorem gradeSign_of_mem (j : ℤ) {i : ℤ} {x : M} (hx : x ∈ grading i) :
    gradeSign M j x = koszulSign (j * i) • x := by
  rw [gradeSign, liftHomogeneous_of_mem _ _ hx, Units.smul_def]
  rfl

theorem gradeSign_mem (j : ℤ) {i : ℤ} {x : M} (hx : x ∈ grading i) :
    gradeSign M j x ∈ grading i := by
  rw [gradeSign_of_mem j hx]
  exact units_smul_mem_grading _ hx

@[simp]
theorem gradeSign_gradeSign (j : ℤ) (x : M) : gradeSign M j (gradeSign M j x) = x := by
  induction x using induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rw [gradeSign_of_mem j x.2, Units.smul_def, map_zsmul, gradeSign_of_mem j x.2,
      ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
  | h_add x y hx hy => rw [map_add, map_add, hx, hy]

theorem gradeSign_smul {A : Type*} [Ring A] [DGAddCommGroup A] [Module A M] [DGModule A M]
    (j : ℤ) {l : ℤ} {a : A} (ha : a ∈ grading l) (x : M) :
    gradeSign M j (a • x) = koszulSign (j * l) • (a • gradeSign M j x) := by
  induction x using induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rw [gradeSign_of_mem j (smul_mem_grading ha x.2), gradeSign_of_mem j x.2, smul_comm a,
      smul_smul, ← koszulSign_add, mul_add]
  | h_add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

end GradeSign

namespace DGModule.HOM

section Gmodule

variable (A : Type*) (M P : Type*) [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

/-- The cochains `Cochain A M P n` form a graded module over the graded ring of cochains
`Cochain A M M n` (the graded pieces of `END A M`), for the action
`F • f = (-1)^{|F||f|} • f ∘ F`. -/
instance instGmodule :
    DirectSum.Gmodule (fun n => Cochain A M M n) (fun n => Cochain A M P n) where
  smul {k n} F f := koszulSign (k * n) • f.comp F rfl
  one_smul f := Sigma.ext (zero_add _) (Cochain.heq_of_forall (zero_add _) fun x => by
    show koszulSign (0 * f.1) • f.2 x = f.2 x
    rw [zero_mul, koszulSign_zero, one_smul])
  mul_smul F G f := Sigma.ext (add_assoc _ _ _) (Cochain.heq_of_forall (add_assoc _ _ _)
    fun x => by
      show koszulSign ((F.1 + G.1) * f.1) • f.2 (koszulSign (F.1 * G.1) • G.2 (F.2 x)) =
        koszulSign (F.1 * (G.1 + f.1)) • (koszulSign (G.1 * f.1) • f.2 (G.2 (F.2 x)))
      rw [Cochain.map_units_smul, smul_smul, smul_smul, add_mul, mul_add, koszulSign_add,
        koszulSign_add]
      congr 1
      ac_rfl)
  smul_add F f g := by
    show koszulSign _ • (f + g).comp F rfl =
      koszulSign _ • f.comp F rfl + koszulSign _ • g.comp F rfl
    rw [Cochain.add_comp, smul_add]
  smul_zero F := by
    show koszulSign _ • (0 : Cochain A M P _).comp F rfl = 0
    rw [Cochain.zero_comp, smul_zero]
  add_smul F F' f := by
    show koszulSign _ • f.comp (F + F') rfl =
      koszulSign _ • f.comp F rfl + koszulSign _ • f.comp F' rfl
    rw [Cochain.comp_add, smul_add]
  zero_smul f := by
    show koszulSign _ • f.comp (0 : Cochain A M M _) rfl = 0
    rw [Cochain.comp_zero, smul_zero]

/-- For `P = M`, the graded action of `DG.DGModule.HOM.instGmodule` is the graded
multiplication of `END A M` (`DG.DGModule.END.instGRing`), through Mathlib's
`DirectSum.GSemiring.toGmodule`. -/
theorem instGmodule_eq_toGmodule :
    instGmodule A M M = DirectSum.GSemiring.toGmodule (fun n => Cochain A M M n) :=
  rfl

variable {A M P}

/-- The action of `END A M` on `HOM A M P` on homogeneous elements:
`F • f = (-1)^{|F||f|} • f ∘ F`. -/
theorem of_smul_of {k n : ℤ} (F : Cochain A M M k) (f : Cochain A M P n) :
    (DirectSum.of (fun n => Cochain A M M n) k F : END A M) •
        (DirectSum.of (fun n => Cochain A M P n) n f : HOM A M P) =
      DirectSum.of _ (k + n) (koszulSign (k * n) • f.comp F rfl) :=
  DirectSum.Gmodule.of_smul_of _ _ F f

end Gmodule

section DGModule

variable {A : Type*} {M P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- The Leibniz rule for the action of `END A M` on `HOM A M P`, on homogeneous elements. -/
theorem d_of_smul_of {k n : ℤ} (F : Cochain A M M k) (f : Cochain A M P n) :
    d ((DirectSum.of (fun n => Cochain A M M n) k F : END A M) •
        (DirectSum.of (fun n => Cochain A M P n) n f : HOM A M P)) =
      d (DirectSum.of (fun n => Cochain A M M n) k F : END A M) •
          (DirectSum.of (fun n => Cochain A M P n) n f : HOM A M P) +
        koszulSign k • ((DirectSum.of (fun n => Cochain A M M n) k F : END A M) •
          d (DirectSum.of (fun n => Cochain A M P n) n f : HOM A M P)) := by
  rw [of_smul_of, HOM.d_of, HOM.d_of, HOM.d_of, of_smul_of, of_smul_of,
    HOM.of_congr (show k + 1 + n = k + n + 1 by ring)
      (g := koszulSign ((k + 1) * n) • f.comp (δ k (k + 1) F) (by ring)) (fun _ => rfl),
    HOM.of_congr (show k + (n + 1) = k + n + 1 by ring)
      (g := koszulSign (k * (n + 1)) • (δ n (n + 1) f).comp F (by ring)) (fun _ => rfl),
    ← HOM.of_units_smul, ← map_add]
  congr 1
  rw [δ_units_smul, δ_comp F f rfl (k + 1) (n + 1) (k + n + 1) rfl rfl rfl]
  ext x
  simp only [Cochain.add_apply, Cochain.units_smul_apply, Cochain.comp_apply, smul_add,
    smul_smul, add_mul, mul_add, one_mul, mul_one, koszulSign_add]
  rw [mul_left_comm, Int.units_mul_self, mul_one, add_comm]

/-- A homogeneous element of `HOM_A(M, P)` of degree `k` is the image of its degree-`k`
component. -/
theorem eq_of_mem {k : ℤ} {x : HOM A M P} (hx : x ∈ grading k) :
    x = DirectSum.of (fun n => Cochain A M P n) k (x k) := by
  obtain ⟨c, rfl⟩ := hx
  rw [DirectSum.of_eq_same]

variable (A M P) in
/-- `HOM A M P` is a left dg module over the endomorphism dg ring `END A M`, for the action
`F • f = (-1)^{|F||f|} • f ∘ F` on homogeneous elements. -/
instance instDGModule : DGModule (END A M) (HOM A M P) where
  smul_mem := by
    rintro k n _ _ ⟨F, rfl⟩ ⟨f, rfl⟩
    rw [of_smul_of]
    exact of_mem_summand _ _
  d_smul' := by
    rintro k _ ⟨F, rfl⟩ y
    induction y using DirectSum.induction_on with
    | zero => simp
    | of n f => exact d_of_smul_of F f
    | add y y' hy hy' => rw [smul_add, d_add, hy, hy', d_add, smul_add, smul_add, smul_add]; abel

end DGModule

end DGModule.HOM

/-! ### The left action of `B` on `HOM_A(M, P)` for a dg `(A, B)`-bimodule `M` -/

namespace DGBimodule

variable (A : Type*) {B : Type*} (M : Type*) [Ring A] [DGAddCommGroup A] [Ring B]
  [DGAddCommGroup B] [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]

/-- The morphism of dg rings `B →ᵈᵍ+* END_A(M)` given by the right action of `B` on a dg
`(A, B)`-bimodule `M` (`DG.DGBimodule.toEND`). -/
def toENDDGRingHom : B →ᵈᵍ+* DGModule.END A M where
  __ := toEND A M
  map_mem' := toEND_mem_grading
  map_d' := toEND_d

@[simp]
theorem toENDDGRingHom_apply (b : B) : toENDDGRingHom A M b = toEND A M b := rfl

end DGBimodule

namespace DGModule.HOM

namespace LeftAction

variable {A B : Type*} {M P : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [DGBimodule A B M]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

/-- For a dg `(A, B)`-bimodule `M`, `B` acts on `HOM_A(M, P)` on the left through
`DG.DGBimodule.toEND : B →+* END_A(M)`. On homogeneous elements
`(b • f) x = (-1)^{|b|(|f| + |x|)} • f (x • b)`. -/
scoped instance instModule : Module B (HOM A M P) :=
  Module.compHom _ (DGBimodule.toENDDGRingHom A M).toRingHom

theorem smul_def (b : B) (f : HOM A M P) : b • f = DGBimodule.toEND A M b • f := rfl

/-- The action of a homogeneous `b ∈ Bᵏ` on a cochain `f` of degree `n`: `b • f` is the
cochain `(-1)^{k n} • f ∘ ρ_b` of degree `k + n`, where `ρ_b x = (-1)^{k |x|} • (x • b)`
(`DG.DGBimodule.rightMulCochain`). -/
theorem smul_of {k n : ℤ} {b : B} (hb : b ∈ grading k) (f : Cochain A M P n) :
    b • (DirectSum.of (fun n => Cochain A M P n) n f : HOM A M P) =
      DirectSum.of _ (k + n)
        (koszulSign (k * n) • f.comp (DGBimodule.rightMulCochain A M ⟨b, hb⟩) rfl) := by
  rw [smul_def, DGBimodule.toEND_of_mem hb, of_smul_of]

/-- The action of `B` on `HOM_A(M, P)`: for `b ∈ Bᵏ`, a cochain `f` of degree `n` and `x ∈ Mⁱ`,
`(b • f) x = (-1)^{k (n + i)} • f (x • b)`. -/
theorem smul_of_apply {k n i : ℤ} {b : B} (hb : b ∈ grading k) (f : Cochain A M P n) {x : M}
    (hx : x ∈ grading i) :
    (b • (DirectSum.of (fun n => Cochain A M P n) n f : HOM A M P)) (k + n) x =
      koszulSign (k * (n + i)) • f (op b • x) := by
  rw [smul_of hb, DirectSum.of_eq_same, Cochain.units_smul_apply, Cochain.comp_apply,
    DGBimodule.rightMulCochain_apply, DGBimodule.signedRightMul_of_mem _ _ hx,
    Cochain.map_units_smul, smul_smul, ← koszulSign_add, mul_add]

variable [DGModule A P]

/-- For a dg `(A, B)`-bimodule `M` and a left dg `A`-module `P`, `HOM_A(M, P)` is a left dg
`B`-module, by restriction of scalars along `B →ᵈᵍ+* END_A(M)`. -/
scoped instance instDGModule : DGModule B (HOM A M P) :=
  DGModule.compHom (DGBimodule.toENDDGRingHom A M) (HOM A M P)

end LeftAction

end DGModule.HOM

/-! ### Postcomposition -/

namespace DGModule.HOM

section Postcomp

variable {A : Type*} {M P P' : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  [AddCommGroup P'] [DGAddCommGroup P'] [Module A P'] [DGModule A P']

variable (M) in
/-- Postcomposition with a morphism of dg modules `h : P → P'`, as an additive map
`HOM_A(M, P) →+ HOM_A(M, P')`, `f ↦ h ∘ f`. -/
def postcompAddHom (h : P →ᵈᵍ[A] P') : HOM A M P →+ HOM A M P' :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun n => Cochain A M P' n) n).comp
      { toFun := fun f => (Cochain.ofHom h).comp f (add_zero n)
        map_zero' := Cochain.comp_zero _ _
        map_add' := fun f f' => Cochain.comp_add f f' _ _ }

omit [DGModule A M] [DGModule A P] [DGModule A P'] in
@[simp]
theorem postcompAddHom_of (h : P →ᵈᵍ[A] P') {n : ℤ} (f : Cochain A M P n) :
    postcompAddHom M h (DirectSum.of _ n f) =
      DirectSum.of _ n ((Cochain.ofHom h).comp f (add_zero n)) := by
  simp [postcompAddHom]

variable (M) in
/-- Postcomposition with a morphism of dg modules `h : P → P'`, as a morphism of dg
`END_A(M)`-modules `HOM_A(M, P) → HOM_A(M, P')`, `f ↦ h ∘ f`. -/
def postcompEND (h : P →ᵈᵍ[A] P') : HOM A M P →ᵈᵍ[END A M] HOM A M P' where
  toFun := postcompAddHom M h
  map_add' := map_add _
  map_smul' F x := by
    rw [RingHom.id_apply]
    induction F using DirectSum.induction_on with
    | zero => simp
    | of k F =>
      induction x using DirectSum.induction_on with
      | zero => simp
      | of n f =>
        rw [of_smul_of, postcompAddHom_of, postcompAddHom_of, of_smul_of,
          Cochain.comp_units_smul]
        rfl
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | add F G hF hG => rw [add_smul, map_add, hF, hG, add_smul]
  map_mem' := by
    rintro k _ ⟨f, rfl⟩
    rw [postcompAddHom_of]
    exact of_mem_summand _ _
  map_d' x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n f => rw [HOM.d_of, postcompAddHom_of, postcompAddHom_of, HOM.d_of, δ_comp_ofHom]
    | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

@[simp]
theorem postcompEND_of (h : P →ᵈᵍ[A] P') {n : ℤ} (f : Cochain A M P n) :
    postcompEND M h (DirectSum.of _ n f) =
      DirectSum.of _ n ((Cochain.ofHom h).comp f (add_zero n)) :=
  postcompAddHom_of h f

end Postcomp

namespace LeftAction

variable {A B : Type*} {M P P' : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [DGBimodule A B M]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  [AddCommGroup P'] [DGAddCommGroup P'] [Module A P'] [DGModule A P']

variable (B M) in
/-- Postcomposition with a morphism of dg modules `h : P → P'`, as a morphism of dg
`B`-modules `HOM_A(M, P) → HOM_A(M, P')` for a dg `(A, B)`-bimodule `M`. -/
def postcomp (h : P →ᵈᵍ[A] P') : HOM A M P →ᵈᵍ[B] HOM A M P' where
  toFun := postcompEND M h
  map_add' := map_add _
  map_smul' b x := (postcompEND M h).map_smul' (DGBimodule.toEND A M b) x
  map_mem' := (postcompEND M h).map_mem'
  map_d' := (postcompEND M h).map_d'

@[simp]
theorem postcomp_of (h : P →ᵈᵍ[A] P') {n : ℤ} (f : Cochain A M P n) :
    postcomp B M h (DirectSum.of _ n f) =
      DirectSum.of _ n ((Cochain.ofHom h).comp f (add_zero n)) :=
  postcompAddHom_of h f

end LeftAction

end DGModule.HOM

/-! ### The regular module: `HOM_A(A, P) ≅ P` -/

namespace DGModule.HOM

section Yoneda

variable {A : Type*} {P : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

open LeftAction

variable (A P) in
/-- Evaluation at `1`, `HOM_A(A, P) →+ P`, `f ↦ f 1`. -/
def evalOne : HOM A A P →+ P :=
  DirectSum.toAddMonoid fun n =>
    { toFun := fun f : Cochain A A P n => f 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

set_option backward.isDefEq.respectTransparency false in
omit [DGRing A] in
@[simp]
theorem evalOne_of {n : ℤ} (f : Cochain A A P n) :
    evalOne A P (DirectSum.of (fun n => Cochain A A P n) n f) = f 1 := by
  simp [evalOne]

theorem _root_.DG.Cochain.map_one_mem {n : ℤ} (f : Cochain A A P n) : f 1 ∈ grading (M := P) n := by
  have h := f.map_mem (one_mem_grading (A := A))
  rwa [zero_add] at h

omit [DGRing A] in
/-- A cochain `f` of degree `n` on the regular module is determined by `f 1`:
`f x = (-1)^{n i} • (x • f 1)` for `x ∈ Aⁱ`. -/
theorem _root_.DG.Cochain.apply_eq_smul_map_one {n : ℤ} (f : Cochain A A P n) {i : ℤ} {x : A}
    (hx : x ∈ grading i) : f x = koszulSign (n * i) • (x • f 1) := by
  rw [← f.map_smul hx, smul_eq_mul, mul_one]

variable [DGModule A P]

/-- For `p ∈ Pⁿ`, the cochain `x ↦ (-1)^{n |x|} • (x • p)` of degree `n` on the regular module;
it is the cochain with value `p` at `1`. -/
def smulRightCochain {n : ℤ} (p : grading (M := P) n) : Cochain A A P n where
  toAddMonoidHom := ((smulAddHom A P).flip (p : P)).comp (gradeSign A n)
  map_mem' i x hx := smul_mem_grading (gradeSign_mem n hx) p.2
  map_smul' {k a} ha x := by
    show gradeSign A n (a • x) • (p : P) = _ • (a • (gradeSign A n x • (p : P)))
    rw [gradeSign_smul n ha, smul_assoc, smul_eq_mul, mul_smul]

theorem smulRightCochain_apply {n : ℤ} (p : grading (M := P) n) (x : A) :
    smulRightCochain p x = gradeSign A n x • (p : P) := rfl

@[simp]
theorem smulRightCochain_apply_one {n : ℤ} (p : grading (M := P) n) :
    smulRightCochain (A := A) p 1 = p := by
  rw [smulRightCochain_apply, gradeSign_of_mem n (one_mem_grading (A := A)), mul_zero,
    koszulSign_zero, one_smul, one_smul]

variable (A P) in
/-- The inverse of evaluation at `1`: `p ∈ Pⁿ` is sent to the cochain
`x ↦ (-1)^{n |x|} • (x • p)` of degree `n`. -/
def coevalOne : P →+ HOM A A P :=
  liftHomogeneous (grading (M := P)) fun n =>
    (DirectSum.of (fun n => Cochain A A P n) n).comp
      { toFun := smulRightCochain
        map_zero' := Cochain.ext fun x => by simp [smulRightCochain_apply, Cochain.zero_apply]
        map_add' := fun p p' => Cochain.ext fun x => by
          simp [smulRightCochain_apply, Cochain.add_apply, smul_add] }

theorem coevalOne_of_mem {n : ℤ} {p : P} (hp : p ∈ grading n) :
    coevalOne A P p = DirectSum.of (fun n => Cochain A A P n) n (smulRightCochain ⟨p, hp⟩) :=
  liftHomogeneous_of_mem _ _ hp

theorem evalOne_coevalOne (p : P) : evalOne A P (coevalOne A P p) = p := by
  induction p using DG.induction_on with
  | h_zero => simp
  | h_homogeneous p => rw [coevalOne_of_mem p.2, evalOne_of, smulRightCochain_apply_one]
  | h_add p p' hp hp' => rw [map_add, map_add, hp, hp']

theorem coevalOne_evalOne (F : HOM A A P) : coevalOne A P (evalOne A P F) = F := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of n f =>
    rw [evalOne_of, coevalOne_of_mem (Cochain.map_one_mem f)]
    congr 1
    ext x
    induction x using DG.induction_on with
    | h_zero => simp
    | h_homogeneous x =>
      rw [smulRightCochain_apply, gradeSign_of_mem n x.2, Cochain.apply_eq_smul_map_one f x.2,
        smul_assoc]
    | h_add x y hx hy => rw [map_add, map_add, hx, hy]
  | add F G hF hG => rw [map_add, map_add, hF, hG]

omit [DGModule A P] in
theorem evalOne_smul (a : A) (F : HOM A A P) : evalOne A P (a • F) = a • evalOne A P F := by
  induction a using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous k a =>
    induction F using DirectSum.induction_on with
    | zero => simp
    | of n f =>
      rw [smul_of a.2, evalOne_of, evalOne_of, Cochain.units_smul_apply, Cochain.comp_apply,
        DGBimodule.rightMulCochain_apply,
        DGBimodule.signedRightMul_of_mem _ _ (one_mem_grading (A := A)), op_smul_eq_mul,
        one_mul, Cochain.map_units_smul, f.apply_eq_smul_map_one a.2, smul_smul, smul_smul,
        ← koszulSign_add, ← koszulSign_add]
      rw [koszulSign_smul_congr (b := 0) ⟨k * n, by ring⟩, koszulSign_zero, one_smul]
    | add F G hF hG => rw [smul_add, map_add, hF, hG, map_add, smul_add]
  | h_add a a' ha ha' => rw [add_smul, map_add, ha, ha', add_smul]

variable (A P)

/-- Yoneda for the regular module: evaluation at `1` is an isomorphism of dg `A`-modules
`HOM_A(A, P) ≅ P`, where `HOM_A(A, P)` is a left dg `A`-module through the right action of `A`
on itself (`DG.DGModule.HOM.LeftAction`). The inverse sends `p ∈ Pⁿ` to the cochain
`x ↦ (-1)^{n |x|} • (x • p)`. -/
def evalOneEquiv : HOM A A P ≃ᵈᵍ[A] P where
  toFun := evalOne A P
  invFun := coevalOne A P
  left_inv := coevalOne_evalOne
  right_inv := evalOne_coevalOne
  map_add' := map_add _
  map_smul' := evalOne_smul
  map_mem' := by
    rintro n _ ⟨f, rfl⟩
    rw [evalOne_of]
    exact Cochain.map_one_mem f
  map_d' F := by
    induction F using DirectSum.induction_on with
    | zero => simp
    | of n f =>
      rw [HOM.d_of, evalOne_of, evalOne_of, δ_apply _ _ rfl, d_one, map_zero, smul_zero,
        sub_zero]
    | add F G hF hG => rw [d_add, map_add, hF, hG, map_add, d_add]

variable {A P}

@[simp]
theorem evalOneEquiv_of {n : ℤ} (f : Cochain A A P n) :
    evalOneEquiv A P (DirectSum.of (fun n => Cochain A A P n) n f) = f 1 :=
  evalOne_of f

theorem evalOneEquiv_symm_of_mem {n : ℤ} {p : P} (hp : p ∈ grading n) :
    (evalOneEquiv A P).symm p =
      DirectSum.of (fun n => Cochain A A P n) n (smulRightCochain ⟨p, hp⟩) :=
  coevalOne_of_mem hp

end Yoneda

end DGModule.HOM

end DG
