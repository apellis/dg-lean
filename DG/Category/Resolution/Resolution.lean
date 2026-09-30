import DG.Category.Resolution.KProjective
import DG.Category.Resolution.SeqColimit
import DG.Category.Homotopy.ConeCochain

/-!
# K-projective resolutions of dg modules over a dg category

Let `C` be a dg category. This file shows that every dg module `M` over `C` has a K-projective
resolution: a quasi-isomorphism `P ⟶ M`, objectwise surjective, from a K-projective dg module
`P` which is built from shifts of representable modules by iterated cones and a sequential
colimit [Keller, *Deriving DG categories*, §3.1, Thm. 3.1 (a)]. This is a port of
`DG.Derived.Resolution` (the case of a dg ring).

## The construction

The resolution is the colimit of a sequence of stages `P₀ = 0 ⟶ P₁ ⟶ P₂ ⟶ ⋯` over `M`
(`DG.CatModule.Resolution.stage`). Given a stage `πₙ : Pₙ ⟶ M`, a *cell*
(`DG.CatModule.Resolution.Cell`) is an object `X` of `C`, a homogeneous cocycle `z ∈ Pₙ X` of
degree `k` and an element `m ∈ M X` of degree `k - 1` with `πₙ z = d m`. The next stage attaches
all cells at once: it is the mapping cone `Pₙ₊₁ = cone (attach πₙ)` of the morphism
`⨁_c C(X_c, -)⟦-k_c⟧ ⟶ Pₙ` sending the generator `𝟙` of the cell `c` to `z_c`, mapped to `M`
by `πₙ` and the null-homotopy `generator of c ↦ m_c`. The resolution is the colimit
`DG.CatModule.Resolution.colim M` of the stages (`DG.CatModule.seqColimit`):

* each stage is K-projective (a cone of a morphism between K-projective modules), and the
  inclusions `Pₙ ⟶ Pₙ₊₁` are graded-split with K-projective cokernels, so the colimit is
  K-projective (`DG.CatModule.SeqColimit.isKProjective`, the telescope argument);
* the cells `(X, 0, m)` of `P₀ = 0` attach a cocycle over every cocycle `m` of `M`, so `π` is
  surjective on cohomology; the cells of `P₁` then attach a preimage of every homogeneous
  element of `M`, so `π` is objectwise surjective;
* a cocycle `z ∈ Pₙ X` with `π z` a coboundary `d m` is killed by the cell `(X, z, m)` in
  `Pₙ₊₁`, so `π` is injective on cohomology.

## Main definitions and results

* `DG.CatModule.SeqColimit.isKProjective`: the colimit of a sequence of graded-split
  monomorphisms with K-projective cokernels, starting at a K-projective module, is K-projective.
* `DG.CatModule.Resolution.colim M`, `DG.CatModule.Resolution.π M`: the resolution;
  `DG.CatModule.Resolution.isKProjective_colim`, `DG.CatModule.Resolution.isQuasiIso_π`,
  `DG.CatModule.Resolution.surjective_π`.
* `DG.CatModule.exists_kProjective_resolution`: every dg module `M` has a quasi-isomorphism
  `P ⟶ M`, objectwise surjective, with `P` K-projective.

## Universes

The generators of the resolution of `M` are indexed by objects of `C` and elements of `M` and
of earlier stages, and the representable modules take values in the universe `v` of the Hom
types of `C`. The resolution is therefore constructed for `M : CatModule.{max u v w} C`, where
`C : Type u` and `[Category.{v} C]`. For a small dg category (`u = v`) and modules in the
universe `v` this is `CatModule.{v} C`.
-/

open CategoryTheory DirectSum

universe w v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### The telescope argument -/

namespace SeqColimit

variable {S : ℕ → CatModule.{w} C} {ι : ∀ n, S n ⟶ S (n + 1)}

/-- The colimit of a sequence of monomorphisms `ι n : S n ⟶ S (n + 1)` which are split as
graded modules, with K-projective cokernels, starting at a K-projective module `S 0`, is
K-projective: null-homotopies of the restrictions of a morphism `f : colim S ⟶ N` to the `S n`
can be chosen compatibly (`DG.CatModule.GradedSplitting.exists_extension`), and then glued. -/
theorem isKProjective (h0 : IsKProjective (S 0))
    (hι : ∀ n, ∃ (Q : CatModule.{w} C) (p : S (n + 1) ⟶ Q),
      Nonempty (GradedSplitting (ι n) p) ∧ IsKProjective Q) :
    IsKProjective (seqColimit S ι) := by
  intro N hN f
  let P : ∀ n, Cochain (S n) N (-1) → Prop := fun n h =>
    Cochain.ofHom (of S ι n ≫ f) = δ (-1) 0 h
  have step : ∀ n (h : {h // P n h}), ∃ h' : {h // P (n + 1) h},
      ∀ {X : C} (x : (S n).obj X), h'.1.app X ((ι n).app X x) = h.1.app X x := by
    intro n h
    obtain ⟨Q, p, ⟨σ⟩, hQ⟩ := hι n
    obtain ⟨h', hh', hext⟩ := σ.exists_extension (hQ N hN) (of S ι (n + 1) ≫ f) h.1
      (by rw [ι_comp_of_assoc]; exact h.2)
    exact ⟨⟨h', hh'⟩, hext⟩
  choose F hF using step
  have h₀ : ∃ h, P 0 h := homotopic_zero_iff_exists.mp (h0 N hN (of S ι 0 ≫ f))
  let seq : ∀ n, {h // P n h} := fun n =>
    Nat.rec (motive := fun n => {h // P n h}) ⟨h₀.choose, h₀.choose_spec⟩ (fun n h => F n h) n
  let H : Cochain (seqColimit S ι) N (-1) :=
    descCochain (fun n => (seq n).1) (fun n _ x => hF n (seq n) x)
  refine homotopic_zero_iff_exists.mpr ⟨H, Cochain.ext fun X x => ?_⟩
  obtain ⟨n, y, rfl⟩ := exists_of_eq x
  have h1 := congrArg (fun z : Cochain (S n) N 0 => z.app X y) (seq n).2
  simp only [Cochain.ofHom_apply, comp_app, δ_neg_one_apply] at h1
  rw [Cochain.ofHom_apply, h1, δ_neg_one_apply, ← Hom.map_d]
  simp only [H, descCochain_of]

end SeqColimit

/-! ### Attaching cells -/

namespace Resolution

section Cells

variable [DGCategory C] {M S : CatModule.{max u v w} C}

/-- A cell to be attached to a dg module `S` over `M` (given by a morphism `p : S ⟶ M`): an
object `X`, a cocycle `z ∈ S X` of degree `deg` and an element `m ∈ M X` of degree `deg - 1`
with `p z = d m`. Attaching the cell adds a free generator `e` at `X` of degree `deg - 1` with
`d e = z`, mapped to `m`. -/
structure Cell (p : S ⟶ M) where
  /-- The object of `C` at which the cell is attached. -/
  X : C
  /-- The degree of the cocycle to be killed. -/
  deg : ℤ
  /-- The cocycle to be killed. -/
  z : S.obj X
  /-- The image in `M` of the new generator. -/
  m : M.obj X
  z_mem : z ∈ grading deg
  d_z : d z = 0
  m_mem : m ∈ grading (deg - 1)
  p_z : p.app X z = d m

variable (p : S ⟶ M)

noncomputable instance : DecidableEq (Cell p) := Classical.decEq _

/-- The free dg module `C(X_c, -)⟦-deg c⟧` (lifted to the universe of `M`) on a cell `c`. -/
noncomputable abbrev Cell.module (c : Cell p) : CatModule.{max u v w} C :=
  shift (-c.deg) (ulift.{max u w} (representable c.X))

/-- The free dg module `⨁ c, C(X_c, -)⟦-deg c⟧` on the cells. -/
noncomputable abbrev cells : CatModule.{max u v w} C :=
  directSum.{max u v w, max u v w} fun c : Cell p => c.module

variable {p}

/-- The generator of the free module on a cell, of degree `deg c`. -/
noncomputable def Cell.gen (c : Cell p) : c.module.obj c.X :=
  shift.mk (-c.deg) (ULift.up (𝟙 c.X))

theorem Cell.isCornerGenerator (c : Cell p) :
    IsCornerGenerator c.module (DGCategory.Idempotent.id c.X) (0 - -c.deg) c.gen :=
  ((isCornerGenerator_representable c.X).ulift.{max u w}).shift (-c.deg)

omit [DGCategory C] in
theorem Cell.z_mem' (c : Cell p) : c.z ∈ grading ((0 - -c.deg) + 0) := by
  rw [show (0 - -c.deg) + 0 = c.deg by ring]
  exact c.z_mem

omit [DGCategory C] in
theorem Cell.m_mem' (c : Cell p) : c.m ∈ grading ((0 - -c.deg) + -1) := by
  rw [show (0 - -c.deg) + -1 = c.deg - 1 by ring]
  exact c.m_mem

variable (p)

/-- The attaching map on a single cell, sending the generator to the cocycle `z`. -/
noncomputable def attachCell (c : Cell p) : c.module ⟶ S :=
  Cocycle.homOf (Cocycle.mk (c.isCornerGenerator.ofElement (n := 0) c.z c.z_mem') 1 (zero_add 1)
    (by
      rw [c.isCornerGenerator.δ_ofElement (zero_add 1) c.z c.z_mem'
          (by rw [c.d_z]; exact zero_mem _),
        c.isCornerGenerator.ofElement_congr c.d_z _ (zero_mem _)]
      exact c.isCornerGenerator.ofElement_zero))

/-- The attaching map `cells p ⟶ S`, sending the generator of a cell to its cocycle. -/
noncomputable def attach : cells p ⟶ S :=
  directSumDesc fun c => attachCell p c

/-- The cochain of degree `-1` on the cells sending the generator of a cell to its element of
`M`; it is a null-homotopy of `attach p ≫ p` (`DG.CatModule.Resolution.δ_homotopy`). -/
noncomputable def homotopy : Cochain (cells p) M (-1) :=
  Cochain.directSumDesc fun c => c.isCornerGenerator.ofElement (n := -1) c.m c.m_mem'

variable {p}

theorem attachCell_gen (c : Cell p) : (attachCell p c).app c.X c.gen = c.z := by
  change (c.isCornerGenerator.ofElement (n := 0) c.z c.z_mem').app c.X c.gen = c.z
  rw [IsCornerGenerator.ofElement_gen, DGCategory.Idempotent.id_val, id_smul]

@[simp]
theorem attach_gen (c : Cell p) :
    (attach p).app c.X ((directSumι _ c).app c.X c.gen) = c.z := by
  rw [← comp_app, attach, directSumι_desc, attachCell_gen]

@[simp]
theorem homotopy_gen (c : Cell p) :
    (homotopy p).app c.X ((directSumι _ c).app c.X c.gen) = c.m := by
  rw [homotopy, directSumι_app, Cochain.directSumDesc_app_of,
    IsCornerGenerator.ofElement_gen, DGCategory.Idempotent.id_val, id_smul]

variable (p)

theorem δ_homotopy : δ (-1) 0 (homotopy p) = Cochain.ofHom (attach p ≫ p) :=
  Cochain.directSum_ext fun c X x => by
    have key : (δ (-1) 0 (homotopy p)).comp (Cochain.ofHom (directSumι _ c)) (zero_add 0) =
        (Cochain.ofHom (attach p ≫ p)).comp (Cochain.ofHom (directSumι _ c)) (zero_add 0) := by
      refine c.isCornerGenerator.ext_gen ?_
      rw [Cochain.comp_apply, Cochain.comp_apply, Cochain.ofHom_apply, Cochain.ofHom_apply,
        δ_neg_one_apply, ← Hom.map_d, c.isCornerGenerator.d_eq_zero, map_zero, map_zero,
        add_zero, homotopy_gen, comp_app, attach_gen, c.p_z]
    exact congrArg (fun z : Cochain c.module M 0 => z.app X x) key

end Cells

/-! ### The stages -/

section Stages

variable [DGCategory C] (M : CatModule.{max u v w} C)

/-- A stage of the construction of the resolution: a dg module with a morphism to `M`. -/
structure Stage where
  /-- The dg module. -/
  obj : CatModule.{max u v w} C
  /-- The morphism to `M`. -/
  π : obj ⟶ M

variable {M}

/-- The next stage: the cone of the attaching map of all cells, `cone (attach π)`, with the
morphism to `M` given by `π` and the null-homotopy `homotopy π` of `attach π ≫ π`. -/
noncomputable def Stage.step (s : Stage M) : Stage M where
  obj := cone (attach s.π)
  π := cone.desc (attach s.π) (homotopy s.π) s.π (δ_homotopy s.π)

/-- Attaching a cell: a cocycle `z` of a stage whose image in `M` is a coboundary `d m` becomes
the coboundary of an element of the next stage mapped to `m`. -/
theorem Stage.exists_step (s : Stage M) {X : C} {j : ℤ} {z : s.obj.obj X} (hz : z ∈ grading j)
    (hdz : d z = 0) {m : M.obj X} (hm : m ∈ grading (j - 1)) (hpz : s.π.app X z = d m) :
    ∃ e : s.step.obj.obj X, e ∈ grading (j - 1) ∧ d e = (cone.inr (attach s.π)).app X z ∧
      s.step.π.app X e = m := by
  let c : Cell s.π := ⟨X, j, z, m, hz, hdz, hm, hpz⟩
  let g := (directSumι _ c).app c.X c.gen
  have hg : g ∈ grading j := by
    have := (directSumι _ c).map_mem c.isCornerGenerator.mem_grading
    rwa [show (0 : ℤ) - -j = j by ring] at this
  have hdg : d g = 0 := by
    rw [← Hom.map_d, c.isCornerGenerator.d_eq_zero, map_zero]
  refine ⟨(cone.inl (attach s.π)).app X g, ?_, ?_, ?_⟩
  · have h := (cone.inl (attach s.π)).map_mem hg
    rwa [← sub_eq_add_neg] at h
  · refine (cone.inl_d_apply g).trans ?_
    rw [hdg, map_zero, sub_zero]
    exact congrArg _ (attach_gen c)
  · exact (cone.inl_desc_apply _ _ _ (δ_homotopy s.π) _).trans (homotopy_gen c)

variable (M)

/-- The stages of the construction: `0`, then iterated attachment of all cells. -/
noncomputable def stage : ℕ → Stage M
  | 0 => ⟨zero, 0⟩
  | n + 1 => (stage n).step

/-- The underlying dg module of the `n`-th stage. -/
noncomputable abbrev obj (n : ℕ) : CatModule.{max u v w} C := (stage M n).obj

/-- The inclusion of the `n`-th stage into the next one. -/
noncomputable def ι (n : ℕ) : obj M n ⟶ obj M (n + 1) :=
  cone.inr (attach (stage M n).π)

theorem ι_injective (n : ℕ) (X : C) : Function.Injective ((ι M n).app X) := fun _ _ h =>
  congrArg (cone.sndAddHom (attach (stage M n).π) X) h

/-- The underlying dg module of the resolution: the colimit of the stages. -/
noncomputable abbrev colim : CatModule.{max u v w} C := seqColimit (obj M) (ι M)

theorem ι_comp_stage_succ_π (n : ℕ) : ι M n ≫ (stage M (n + 1)).π = (stage M n).π :=
  cone.inr_desc _ _ _ (δ_homotopy _)

/-- The augmentation of the resolution. -/
noncomputable def π : colim M ⟶ M :=
  SeqColimit.desc (fun n => (stage M n).π) (ι_comp_stage_succ_π M)

variable {M}

theorem π_of (n : ℕ) {X : C} (x : (obj M n).obj X) :
    (π M).app X ((SeqColimit.of _ _ n).app X x) = (stage M n).π.app X x :=
  SeqColimit.desc_of _ _ _ _

theorem exists_step (n : ℕ) {X : C} {j : ℤ} {z : (obj M n).obj X} (hz : z ∈ grading j)
    (hdz : d z = 0) {m : M.obj X} (hm : m ∈ grading (j - 1)) (hpz : (stage M n).π.app X z = d m) :
    ∃ e : (obj M (n + 1)).obj X, e ∈ grading (j - 1) ∧ d e = (ι M n).app X z ∧
      (stage M (n + 1)).π.app X e = m :=
  (stage M n).exists_step hz hdz hm hpz

/-- Every cocycle of `M` is the image of a cocycle of the first stage. -/
theorem exists_stage_one {X : C} {j : ℤ} {m : M.obj X} (hm : m ∈ grading j) (hdm : d m = 0) :
    ∃ e : (obj M 1).obj X, e ∈ grading j ∧ d e = 0 ∧ (stage M 1).π.app X e = m := by
  obtain ⟨e, he, hde, hpe⟩ := exists_step (M := M) 0 (j := j + 1) (z := 0) (zero_mem _) d_zero
    (m := m) (by rwa [add_sub_cancel_right]) (by rw [map_zero, hdm])
  rw [add_sub_cancel_right] at he
  rw [map_zero] at hde
  exact ⟨e, he, hde, hpe⟩

variable (M)

/-- The augmentation of the resolution is objectwise surjective. -/
theorem surjective_π (X : C) : Function.Surjective ((π M).app X) := by
  intro m
  induction m using DG.induction_on with
  | h_zero => exact ⟨0, map_zero _⟩
  | h_homogeneous m =>
    rename_i j
    obtain ⟨e₁, he₁, hde₁, hpe₁⟩ := exists_stage_one (M := M) (d_mem m.2) (d_d _)
    obtain ⟨e₂, -, -, hpe₂⟩ := exists_step 1 he₁ hde₁ (m := m)
      (by rw [add_sub_cancel_right]; exact m.2) hpe₁
    exact ⟨(SeqColimit.of _ _ 2).app X e₂, by rw [π_of, hpe₂]⟩
  | h_add m m' hm hm' =>
    obtain ⟨x, rfl⟩ := hm
    obtain ⟨y, rfl⟩ := hm'
    exact ⟨x + y, map_add _ _ _⟩

/-- The augmentation of the resolution is a quasi-isomorphism. -/
theorem isQuasiIso_π : IsQuasiIso (π M) := fun X j => by
  constructor
  · rw [cohomologyMap_injective_iff]
    intro x hx hdx hpx
    obtain ⟨n, y, rfl⟩ := SeqColimit.exists_of_eq x
    have hinj := SeqColimit.of_injective (ι_injective M) n X
    have hy : y ∈ grading j :=
      mem_grading_of_injective ((SeqColimit.of _ _ n).app X) (Hom.map_mem _) hinj hx
    have hdy : d y = 0 := hinj (by rw [Hom.map_d, hdx, map_zero])
    obtain ⟨m, hm, hdm⟩ := mem_coboundaries.mp hpx
    rw [π_of] at hdm
    obtain ⟨e, he, hde, -⟩ := exists_step n hy hdy hm hdm.symm
    exact mem_coboundaries.mpr ⟨(SeqColimit.of _ _ (n + 1)).app X e,
      (SeqColimit.of _ _ (n + 1)).map_mem he, by
        rw [← Hom.map_d, hde, SeqColimit.of_succ_ι]⟩
  · rw [cohomologyMap_surjective_iff]
    intro m hm hdm
    obtain ⟨e, he, hde, hpe⟩ := exists_stage_one (M := M) hm hdm
    exact ⟨(SeqColimit.of _ _ 1).app X e, (SeqColimit.of _ _ 1).map_mem he,
      by rw [← Hom.map_d, hde, map_zero], by rw [π_of, hpe, sub_self]; exact zero_mem _⟩

/-! ### K-projectivity -/

theorem isKProjective_cells {S : CatModule.{max u v w} C} (p : S ⟶ M) :
    IsKProjective (cells p) :=
  IsKProjective.directSum fun c => c.isCornerGenerator.isKProjective

theorem isKProjective_obj (n : ℕ) : IsKProjective (obj M n) := by
  induction n with
  | zero =>
    intro N _ f
    rw [show f = 0 from hom_ext fun X x => by
      have : Subsingleton ((obj M 0).obj X) :=
        inferInstanceAs (Subsingleton ((CatModule.zero.{max u v w} (C := C)).obj X))
      rw [Subsingleton.elim x 0, map_zero, map_zero]]
  | succ n ih => exact IsKProjective.cone (isKProjective_cells M _) ih

/-- The resolution is K-projective. -/
theorem isKProjective_colim : IsKProjective (colim M) :=
  SeqColimit.isKProjective (isKProjective_obj M 0) fun n =>
    ⟨_, _, ⟨cone.gradedSplitting (attach (stage M n).π)⟩, (isKProjective_cells M _).shift 1⟩

end Stages

end Resolution

/-! ### Existence of K-projective resolutions -/

variable [DGCategory C] in
/-- Every dg module `M` over a dg category `C` has a K-projective resolution: a quasi-isomorphism
`P ⟶ M`, objectwise surjective, from a K-projective dg module `P` [Keller, *Deriving DG
categories*, §3.1, Thm. 3.1 (a)]. The module `P` is built from shifts of representable modules
by iterated mapping cones and a sequential colimit (`DG.CatModule.Resolution.colim`). -/
theorem exists_kProjective_resolution (M : CatModule.{max u v w} C) :
    ∃ (P : CatModule.{max u v w} C) (π : P ⟶ M), IsKProjective P ∧ IsQuasiIso π ∧
      ∀ X, Function.Surjective (π.app X) :=
  ⟨_, Resolution.π M, Resolution.isKProjective_colim M, Resolution.isQuasiIso_π M,
    Resolution.surjective_π M⟩

end CatModule

end DG
