import DG.HalfGraded.DiagonalAdjunction
import DG.HalfGraded.Derived
import DG.Category.Tensor.Bimodule
import DG.Category.Derived.Induction
import DG.Category.Derived.ExtendScalars
import DG.Module.Right

/-!
# The diagonal regrading of a dg bimodule

Let `A`, `B` be dg rings and `M` a dg `(A, B)`-bimodule (`DG.DGBimodule`). Placing `Mⁿ` in
internal degree `2n` and parity `n mod 2` (`DG.Diagonal.RegradedModule M`), the right action of
`B` induces a right action of the regraded ring of `HalfGradedDGRing.ofDGRing B`
(`DG.Diagonal.rsmul`: `m` placed in bidegree `p` times `b` placed in bidegree `q` is `m b`
placed in bidegree `p + q`), commuting with the left action of the regraded ring of `A`.

Splitting by weights gives the **diagonally regraded bimodule**
`DG.Diagonal.bimodule A B M`, a dg bimodule over the weight dg categories `C_A`, `C_B` of the
diagonal half-graded dg rings, with

`Mᵈ(⟨k⟩, ⟨l⟩) = (weight k - l component of the regraded module)`,

the weight dg category `C_A` acting on the left and `C_B` on the right. Its left modules are the
internal shifts of the diagonal module of `M` (`DG.Diagonal.bimodule_left`), so they are
K-projective when `M` is K-projective as a left dg `A`-module
(`DG.Diagonal.bimodule_left_isKProjective`).
-/

open CategoryTheory DirectSum MulOpposite

universe v

noncomputable section

namespace DG.Diagonal

set_option backward.isDefEq.respectTransparency false

/-! ### The right action on the diagonal grading -/

section RightAction

variable {B M : Type*} [Ring B] [DGAddCommGroup B] [AddCommGroup M] [DGAddCommGroup M]
  [Module Bᵐᵒᵖ M] [DGRightModule B M]

/-- The original right action respects the diagonal gradings. -/
theorem op_smul_mem {p q : ℤ × ZMod 2} {b : B} {m : M} (hb : b ∈ grading B p)
    (hm : m ∈ grading M q) : op b • m ∈ grading M (q + p) := by
  refine induction_on (P := fun x => op x • m ∈ grading M (q + p)) hb
    (by simp) (fun i b hb hi => ?_)
    (fun _ _ hx hy => by simpa only [MulOpposite.op_add, add_smul] using add_mem hx hy)
  refine induction_on (P := fun y => op b • y ∈ grading M (q + p)) hm
    (by simp) (fun j m hm hj => ?_)
    (fun _ _ hx hy => by simpa only [smul_add] using add_mem hx hy)
  rw [← hi, ← hj, ← map_add]
  exact mem_grading (op_smul_mem_grading hb hm)

/-- The right Leibniz rule has precisely the half-grading parity sign. -/
theorem d_op_smul {j n : ℤ} {m : M} (hm : m ∈ grading M (j, (n : ZMod 2))) (b : B) :
    d (op b • m) = op b • d m + koszulSign n • (op (d b) • m) := by
  refine induction_on hm (by simp) (fun i m hm hi => ?_)
    (fun _ _ hx hy => by
      simp only [smul_add, d_add, hx, hy]
      abel)
  rw [DG.d_op_smul hm, koszulSign_eq_of_cast_eq (congrArg Prod.snd hi)]

end RightAction

section Rsmul

variable {B M : Type*} [Ring B] [DGAddCommGroup B] [DGRing B] [AddCommGroup M] [DGAddCommGroup M]
  [Module Bᵐᵒᵖ M] [DGRightModule B M]

theorem rsmul_mem {p q : ℤ × ℤ} {m : M} {b : B} (hm : m ∈ grading M (halfDegree 2 p))
    (hb : b ∈ (HalfGradedDGRing.ofDGRing B).hgrading (halfDegree 2 q)) :
    op b • m ∈ grading M (halfDegree 2 (p + q)) := by
  rw [map_add]
  exact op_smul_mem hb hm

/-- The right action of the regraded ring on one placed element of the regraded module. -/
def rsmulComponent (p : ℤ × ℤ) (m : ↥(halfGrading (grading M) 2 p)) :
    (⨁ q : ℤ × ℤ, ↥(halfGrading (HalfGradedDGRing.ofDGRing B).hgrading 2 q)) →+
      RegradedModule M :=
  DirectSum.toAddMonoid fun q =>
    AddMonoidHom.mk' (fun b => HalfRegrade.mk (grading M) 2 (p + q) (op (b : B) • (m : M))
        (rsmul_mem m.2 b.2))
      fun b b' => by
        simp only [AddMemClass.coe_add, MulOpposite.op_add, add_smul]
        exact HalfRegrade.mk_add _ _ _

/-- **The right action** of the regraded ring of `HalfGradedDGRing.ofDGRing B` on the
regraded module: `m` placed in bidegree `p` times `b` placed in bidegree `q` is `m b` placed in
bidegree `p + q` (`DG.Diagonal.rsmul_mk_place`). -/
def rsmul : RegradedModule M →+ (HalfGradedDGRing.ofDGRing B).Regraded →+ RegradedModule M :=
  DirectSum.toAddMonoid fun p =>
    AddMonoidHom.mk' (rsmulComponent p) fun m m' =>
      DirectSum.addHom_ext (β := fun q => ↥(halfGrading (HalfGradedDGRing.ofDGRing B).hgrading 2 q))
        fun q b => by
          rw [AddMonoidHom.add_apply]
          simp only [rsmulComponent, DirectSum.toAddMonoid_of, AddMonoidHom.mk'_apply]
          simp only [AddMemClass.coe_add, smul_add]
          exact HalfRegrade.mk_add _ _ _

theorem rsmul_of (p : ℤ × ℤ) (m : ↥(halfGrading (grading M) 2 p)) :
    rsmul (B := B) (DirectSum.of (fun p => ↥(halfGrading (grading M) 2 p)) p m) =
      rsmulComponent p m := by
  unfold rsmul
  exact DirectSum.toAddMonoid_of _ _ _

theorem rsmulComponent_of (p q : ℤ × ℤ) (m : ↥(halfGrading (grading M) 2 p))
    (b : ↥(halfGrading (HalfGradedDGRing.ofDGRing B).hgrading 2 q)) :
    rsmulComponent p m
        (DirectSum.of (fun q => ↥(halfGrading (HalfGradedDGRing.ofDGRing B).hgrading 2 q)) q b) =
      HalfRegrade.mk (grading M) 2 (p + q) (op (b : B) • (m : M)) (rsmul_mem m.2 b.2) := by
  unfold rsmulComponent
  exact DirectSum.toAddMonoid_of _ _ _

@[simp]
theorem rsmul_mk_place (p q : ℤ × ℤ) (m : M) (hm : m ∈ grading M (halfDegree 2 p)) (b : B)
    (hb : b ∈ (HalfGradedDGRing.ofDGRing B).hgrading (halfDegree 2 q)) :
    rsmul (HalfRegrade.mk (grading M) 2 p m hm) ((HalfGradedDGRing.ofDGRing B).place q b hb) =
      HalfRegrade.mk (grading M) 2 (p + q) (op b • m) (rsmul_mem hm hb) := by
  change rsmul (B := B) (DirectSum.of (fun p => ↥(halfGrading (grading M) 2 p)) p ⟨m, hm⟩)
    (DirectSum.of (fun q => ↥(halfGrading (HalfGradedDGRing.ofDGRing B).hgrading 2 q)) q
      ⟨b, hb⟩) = _
  rw [rsmul_of]
  exact rsmulComponent_of p q ⟨m, hm⟩ ⟨b, hb⟩

private theorem mk_add_of_eq {p₁ p₂ p : ℤ × ℤ} (h₁ : p₁ = p) (h₂ : p₂ = p)
    {m m' : M} (hm : m ∈ grading M (halfDegree 2 p₁))
    (hm' : m' ∈ grading M (halfDegree 2 p₂)) :
    HalfRegrade.mk (grading M) 2 p₁ m hm + HalfRegrade.mk (grading M) 2 p₂ m' hm' =
      HalfRegrade.mk (grading M) 2 p (m + m')
        (by subst h₁ h₂; exact add_mem hm hm') := by
  subst h₁ h₂
  exact (HalfRegrade.mk_add _ hm hm').symm

theorem rsmul_one (x : RegradedModule M) : rsmul (B := B) x 1 = x := by
  rw [HalfGradedDGRing.one_eq_place]
  induction x using HalfRegrade.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | mk p m hm =>
    rw [rsmul_mk_place]
    exact HalfRegrade.mk_congr (add_zero p) (one_smul _ m) _ _

theorem rsmul_mul (x : RegradedModule M) (g g' : (HalfGradedDGRing.ofDGRing B).Regraded) :
    rsmul x (g * g') = rsmul (rsmul x g) g' := by
  induction g using HalfGradedDGRing.induction_on with
  | zero => simp
  | add g h hg hh => simp only [add_mul, map_add, AddMonoidHom.add_apply, hg, hh]
  | mk q b hb =>
    induction g' using HalfGradedDGRing.induction_on with
    | zero => simp
    | add g h hg hh => simp only [mul_add, map_add, hg, hh]
    | mk q' b' hb' =>
      rw [HalfGradedDGRing.place_mul_place]
      induction x using HalfRegrade.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
      | mk p m hm =>
        rw [rsmul_mk_place, rsmul_mk_place, rsmul_mk_place]
        exact HalfRegrade.mk_congr (add_assoc p q q').symm (mul_smul (op b') (op b) m) _ _

theorem rsmul_mem_cohGrading {j i : ℤ} {x : RegradedModule M}
    (hx : x ∈ HalfRegrade.cohGrading (grading M) 2 j) {g : (HalfGradedDGRing.ofDGRing B).Regraded}
    (hg : g ∈ DG.grading i) : rsmul x g ∈ HalfRegrade.cohGrading (grading M) 2 (j + i) := by
  refine HalfGradedDGRing.grading_induction
    (P := fun g => rsmul x g ∈ HalfRegrade.cohGrading (grading M) 2 (j + i))
    (by simp) (fun w b hb => ?_)
    (fun _ _ h h' => by rw [map_add]; exact add_mem h h') hg
  refine HalfRegrade.cohGrading_induction
    (P := fun x => rsmul x ((HalfGradedDGRing.ofDGRing B).place (i, w) b hb) ∈
      HalfRegrade.cohGrading (grading M) 2 (j + i))
    (by simp) (fun w' m hm => ?_)
    (fun _ _ h h' => by rw [map_add, AddMonoidHom.add_apply]; exact add_mem h h') hx
  rw [rsmul_mk_place]
  exact HalfRegrade.mk_mem_cohGrading ((j, w') + (i, w)) _

theorem rsmul_mem_weightGrading {j i : ℤ} {x : RegradedModule M}
    (hx : x ∈ HalfRegrade.weightGrading (grading M) 2 j)
    {g : (HalfGradedDGRing.ofDGRing B).Regraded} (hg : g ∈ wgrading i) :
    rsmul x g ∈ HalfRegrade.weightGrading (grading M) 2 (j + i) := by
  refine HalfGradedDGRing.wgrading_induction
    (P := fun g => rsmul x g ∈ HalfRegrade.weightGrading (grading M) 2 (j + i))
    (by simp) (fun n b hb => ?_)
    (fun _ _ h h' => by rw [map_add]; exact add_mem h h') hg
  refine HalfRegrade.weightGrading_induction
    (P := fun x => rsmul x ((HalfGradedDGRing.ofDGRing B).place (n, i) b hb) ∈
      HalfRegrade.weightGrading (grading M) 2 (j + i))
    (by simp) (fun n' m hm => ?_)
    (fun _ _ h h' => by rw [map_add, AddMonoidHom.add_apply]; exact add_mem h h') hx
  rw [rsmul_mk_place]
  exact HalfRegrade.mk_mem_weightGrading ((n', j) + (n, i)) _

/-- The right Leibniz rule for the regraded right action. -/
theorem d_rsmul {j : ℤ} {x : RegradedModule M}
    (hx : x ∈ HalfRegrade.cohGrading (grading M) 2 j)
    (g : (HalfGradedDGRing.ofDGRing B).Regraded) :
    d (rsmul x g) = rsmul (d x) g + koszulSign j • rsmul x (d g) := by
  induction g using HalfGradedDGRing.induction_on with
  | zero => simp
  | add g h hg hh =>
    rw [map_add, d_add, hg, hh, map_add, d_add, map_add, smul_add]
    abel
  | mk q b hb =>
    refine HalfRegrade.cohGrading_induction
      (P := fun x => d (rsmul x ((HalfGradedDGRing.ofDGRing B).place q b hb)) =
        rsmul (d x) ((HalfGradedDGRing.ofDGRing B).place q b hb) +
          koszulSign j • rsmul x (d ((HalfGradedDGRing.ofDGRing B).place q b hb)))
      (by simp) (fun w m hm => ?_)
      (fun x y h h' => by
        simp only [map_add, AddMonoidHom.add_apply, h, h', smul_add]
        abel) hx
    rw [rsmul_mk_place, d_mk, d_mk, HalfGradedDGRing.d_place, rsmul_mk_place, rsmul_mk_place,
      ← HalfRegrade.mk_units_smul]
    simp only [HalfGradedDGRing.ofDGRing_hd]
    have h₁ : (j, w) + (1, 0) + q = (j, w) + q + (1, 0) := by abel
    have h₂ : (j, w) + (q + (1, 0)) = (j, w) + q + (1, 0) := by abel
    rw [mk_add_of_eq h₁ h₂]
    refine HalfRegrade.mk_congr rfl ?_ _ _
    exact d_op_smul (n := j) (show m ∈ grading M (_, ((j : ℤ) : ZMod 2)) from hm) b

theorem smul_rsmul {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Module A M]
    [DGModule A M] [SMulCommClass A Bᵐᵒᵖ M] (a : (HalfGradedDGRing.ofDGRing A).Regraded) (x : RegradedModule M)
    (g : (HalfGradedDGRing.ofDGRing B).Regraded) :
    a • rsmul x g = rsmul (a • x) g := by
  induction a using HalfGradedDGRing.induction_on with
  | zero => simp
  | add a a' ha ha' => rw [add_smul, ha, ha', add_smul, map_add, AddMonoidHom.add_apply]
  | mk p a ha =>
    induction g using HalfGradedDGRing.induction_on with
    | zero => simp
    | add g h hg hh => rw [map_add, smul_add, hg, hh, map_add]
    | mk r b hb =>
      induction x using HalfRegrade.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, AddMonoidHom.add_apply, smul_add, hx, hy, smul_add, map_add,
          AddMonoidHom.add_apply]
      | mk q m hm =>
        rw [rsmul_mk_place, place_smul_mk, place_smul_mk, rsmul_mk_place]
        exact HalfRegrade.mk_congr (add_assoc p q r).symm (smul_comm a (op b) m) _ _

end Rsmul

/-! ### The diagonally regraded bimodule -/

section Bimodule

variable (A B : Type v) [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B]
  [DGRing B] (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [DGBimodule A B M]

/-- **The diagonally regraded bimodule** `Mᵈ` of a dg `(A, B)`-bimodule `M`: a dg bimodule over
the weight dg categories of the diagonal half-graded dg rings of `A` and `B`, with
`Mᵈ(⟨k⟩, ⟨l⟩)` the weight `k - l` component of the regraded module, `C_A` acting on the left by
the regraded action of `A` and `C_B` on the right by `DG.Diagonal.rsmul`. -/
def bimodule : CatBimodule.{v} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)
    (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded) where
  obj X Y := wgrading (M := RegradedModule M) (X.as - Y.as)
  lact {X X' Y} := AddMonoidHom.mk'
    (fun f => AddMonoidHom.mk'
      (fun x => ⟨f.1 • x.1, by
        have h := smul_mem_wgrading (A := (HalfGradedDGRing.ofDGRing A).Regraded) f.2 x.2
        rwa [sub_add_sub_cancel] at h⟩)
      fun x y => Subtype.ext (smul_add f.1 x.1 y.1))
    fun f g => by
      ext x
      exact add_smul f.1 g.1 x.1
  ract {X Y Y'} := AddMonoidHom.mk'
    (fun g => AddMonoidHom.mk'
      (fun x => ⟨rsmul x.1 g.1, by
        have h := rsmul_mem_weightGrading (B := B) x.2 g.2
        rwa [sub_add_sub_cancel] at h⟩)
      fun x y => Subtype.ext (by
        change rsmul (x.1 + y.1) g.1 = rsmul x.1 g.1 + rsmul y.1 g.1
        rw [map_add, AddMonoidHom.add_apply]))
    fun g g' => by
      ext x
      exact map_add (rsmul x.1) g.1 g'.1
  lact_mem' hf hx := smul_mem_grading (A := (HalfGradedDGRing.ofDGRing A).Regraded)
    (M := RegradedModule M) hf hx
  lact_id' _ _ x := Subtype.ext (one_smul _ x.1)
  lact_comp' f f' x := Subtype.ext (mul_smul f'.1 f.1 x.1)
  d_lact' {X X' Y i f} hf x := Subtype.ext (by
    change d (f.1 • x.1) = d f.1 • x.1 + ((koszulSign i : ℤ) • (f.1 • d x.1))
    rw [DG.d_smul (A := (HalfGradedDGRing.ofDGRing A).Regraded) (M := RegradedModule M)
      (a := f.1) hf, Units.smul_def])
  ract_mem' hg hx := rsmul_mem_cohGrading (B := B) (M := M) hx hg
  ract_id' _ _ x := Subtype.ext (rsmul_one x.1)
  ract_comp' g g' x := Subtype.ext (rsmul_mul x.1 g'.1 g.1)
  d_ract' {X Y Y' j x} hx g := Subtype.ext (by
    change d (rsmul x.1 g.1) = rsmul (d x.1) g.1 + ((koszulSign j : ℤ) • rsmul x.1 (d g.1))
    rw [d_rsmul (B := B) (M := M) (x := x.1) hx g.1, Units.smul_def])
  lact_ract' f g x := Subtype.ext (smul_rsmul f.1 x.1 g.1)

end Bimodule

/-! ### K-projectivity of the left modules -/

section KProjective

variable (A : Type v) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The diagonal module functor, on dg modules over `SingleObj A`, is left adjoint to restriction
along the weight-zero inclusion `SingleObj A ⥤ C_A`. -/
def toCatModuleAdjunction :
    (CatModule.singleObjEquivalence.{v} A).functor ⋙ toCatModule.{v} A ⊣
      CatModule.precomp (scalarInclusion A 0) :=
  ((CatModule.singleObjEquivalence.{v} A).toAdjunction.comp (diagonalAdjunction.{v} A)).ofNatIsoRight
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (CatModule.precomp (scalarInclusion A 0))
        (CatModule.singleObjEquivalence.{v} A).unitIso.symm ≪≫ Functor.rightUnitor _)

variable {A} in
/-- The diagonal module of a K-projective dg module is K-projective. -/
theorem isKProjective_toCatModule {P : DGModuleCat.{v} A} (hP : IsKProjective.{v} A P) :
    CatModule.IsKProjective ((toCatModule A).obj P) :=
  (CatModule.IsKProjective.of_adjunction (toCatModuleAdjunction A) (IsKProjective.toCatModuleObj hP)).of_iso
    ((toCatModule A).mapIso ((CatModule.singleObjEquivalence.{v} A).counitIso.app P)).symm

variable (B : Type v) [Ring B] [DGAddCommGroup B] [DGRing B] (M : Type v) [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [DGBimodule A B M]

/-- `Mᵈ(-, Y)` is the internal shift by `-Y` of the diagonal module of `M`. -/
def bimoduleLeftIso (Y : WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded) :
    (bimodule A B M).left Y ≅
      (HalfGradedDGRing.internalShiftFunctor (HalfGradedDGRing.ofDGRing A) (-Y.as)).obj
        ((toCatModule A).obj (DGModuleCat.of A M)) :=
  CatModule.isoMk (fun _ => AddEquiv.refl _) Iff.rfl (fun _ => rfl) (fun _ _ => rfl)

/-- If `M` is K-projective as a left dg `A`-module, every left module `Mᵈ(-, Y)` of the diagonally
regraded bimodule is K-projective. -/
theorem bimodule_left_isKProjective (hM : IsKProjective.{v} A M)
    (Y : WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded) :
    CatModule.IsKProjective ((bimodule A B M).left Y) :=
  (HalfGradedDGRing.isKProjective_internalShift
    (isKProjective_toCatModule (P := DGModuleCat.of A M) hM) (-Y.as)).of_iso
    (bimoduleLeftIso A B M Y)

end KProjective

end DG.Diagonal
