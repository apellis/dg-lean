import DG.Homotopy.Lifting
import DG.Homotopy.ModuleCat
import DG.Module.PUnit
import DG.Module.SeqColimit

/-!
# Semi-free resolutions

Let `A` be a dg ring. This file shows that every dg `A`-module `M` has a semi-free resolution,
a surjective quasi-isomorphism `P → M` from a semi-free dg module `P`, and that such resolutions
are unique up to homotopy equivalence over `M` and functorial up to homotopy. As a consequence,
the dg modules with the lifting property against surjective quasi-isomorphisms (the cofibrant
ones) are the retracts of semi-free modules, and the K-projective dg modules are those homotopy
equivalent to semi-free modules.

## The construction

The resolution is the colimit of a sequence of stages `P₀ = 0 → P₁ → P₂ → ⋯` over `M`
(`DG.Resolution.stage`). Given a stage `πₙ : Pₙ → M`, a *cell* (`DG.Resolution.Cell`) is a
homogeneous cocycle `z ∈ Pₙ` of degree `k` together with `m ∈ M` of degree `k - 1` such that
`πₙ z = d m`. The next stage attaches all cells at once: it is the mapping cone
`Pₙ₊₁ = Cone (attach πₙ)` of the map `⨁_c A⟦-k_c⟧ → Pₙ` sending the generator of the cell `c`
to `z_c`, mapped to `M` by `πₙ` and the null-homotopy `generator of c ↦ m_c`
(`DG.Resolution.Stage.step`). Thus `Pₙ₊₁` contains `Pₙ`, with quotient free on generators
`e_c` of degree `k_c - 1`, `d e_c = z_c` and `πₙ₊₁ e_c = m_c`. The resolution is the colimit
`DG.Resolution.Colim A M` of the stages (`DG.SeqColimit`):

* it is semi-free, filtered by the images of the stages (`DG.Resolution.semiFreeFiltration`);
* the cells `(0, m)` of `P₀ = 0` attach a cocycle over every cocycle `m` of `M`, so `π` is
  surjective on cohomology; the cells of `P₁` then attach a preimage of every homogeneous
  element of `M`, so `π` is surjective (`DG.Resolution.surjective_π`);
* a cocycle `z ∈ Pₙ` with `π z` a coboundary `d m` is killed by the cell `(z, m)` in `Pₙ₊₁`, so
  `π` is injective on cohomology (`DG.Resolution.isQuasiIso_π`).

## Main definitions and results

* `DG.exists_semiFreeResolution`: every dg module `M : Type v` over `A : Type u` has a
  surjective quasi-isomorphism `P → M` with `P : Type (max u v)` semi-free [Keller, *Deriving
  DG categories*, §3.1, Thm. 3.1 (a)]; [Bernstein–Lunts, §10.12.2]; [Stacks 09KP]. (Stacks
  only asks for a quasi-isomorphism; the resolution here is moreover surjective.)
* `DG.SemiFreeResolution A M`: a bundled semi-free resolution, with `P` in the universe of `M`;
  `DG.semiFreeResolution A M` constructs one when the universe of `M` contains that of `A`.
* Uniqueness: `DG.HasLiftingProperty.exists_dgHomotopyEquiv` (cofibrant resolutions by
  surjective quasi-isomorphisms are homotopy equivalent over `M`, strictly compatible with the
  augmentations), `DG.IsKProjective.exists_dgHomotopyEquiv` (K-projective resolutions by
  quasi-isomorphisms are homotopy equivalent over `M` up to homotopy),
  `DG.SemiFreeResolution.dgHomotopyEquiv`.
* Functoriality: `DG.SemiFreeResolution.lift` (a morphism `M → N` lifts to resolutions, strictly
  over the augmentations), unique up to homotopy (`DG.SemiFreeResolution.homotopic_lift`),
  compatible with homotopies, identities and composition up to homotopy
  (`DG.SemiFreeResolution.lift_homotopic`, `DG.SemiFreeResolution.lift_id`,
  `DG.SemiFreeResolution.lift_comp`). For K-projective sources, maps into a quasi-isomorphic
  target lift up to homotopy, uniquely up to homotopy
  (`DG.IsKProjective.exists_homotopic_comp`, `DG.IsKProjective.homotopic_of_homotopic_comp`).
* `DG.hasLiftingProperty_iff_exists_retract`: a dg module has the lifting property against
  surjective quasi-isomorphisms iff it is a retract of a semi-free dg module.
* `DG.isKProjective_iff_exists_dgHomotopyEquiv`: a dg module is K-projective iff it is homotopy
  equivalent to a semi-free dg module.

Together with `DG.IsKProjective.postcompHomotopyEquiv` and
`DG.quotientNullHomotopicAddEquivCohomology`, these are the inputs for the derived-category
statements `Hom_{D(A)}(M, N) ≅ Hom_{H(A)}(P_M, N) ≅ H⁰(HOM_A(P_M, N))` [Stacks 09KV] and the
equivalence of `D(A)` with the homotopy category of K-projective (or semi-free) modules.

## Universes

The generators of the resolution of `M : Type v` are indexed by pairs of elements of `M` and of
earlier stages, so the resolution lives in `Type (max u v)` for `A : Type u`. The lifting
property and K-projectivity are stated for test modules in a single universe; the uniqueness and
functoriality statements therefore take `P`, `P'`, `M`, `N` in one universe `w`, and the bundled
`DG.semiFreeResolution A M` requires `M : Type (max u v)`.

## References

* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994), §3]
* [J. Bernstein, V. Lunts, *Equivariant sheaves and functors*, LNM 1578 (1994), §10.12]
* [The Stacks project, Tags 09KK, 09KP, 09KV]
-/

open DirectSum

universe w w' u v

set_option backward.isDefEq.respectTransparency false

namespace DG

/-! ### Morphisms out of shifts of `A` -/

section Generators

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The twist `a ↦ (-1)^{n |a|} a` anticommutes with `d` up to the sign `(-1)^n`. -/
theorem Shift.d_twist (n : ℤ) (a : A) :
    d (Shift.twist A n a) = koszulSign n • Shift.twist A n (d a) := by
  induction a using DG.induction_on with
  | h_zero => simp
  | h_homogeneous a =>
    rename_i i
    rw [Shift.twist_of_mem a.2, d_units_smul, Shift.twist_of_mem (d_mem a.2), smul_smul,
      ← koszulSign_add]
    congr 1
    exact koszulSign_eq_of_sub_eq_two_mul (-n) (by ring)
  | h_add a a' ha ha' => rw [map_add, d_add, ha, ha', d_add, map_add, smul_add]

variable {X : Type*} [AddCommGroup X] [DGAddCommGroup X] [Module A X] [DGModule A X]

/-- The morphism `A⟦k⟧ → X` sending the generator `1` (of degree `-k`) to a cocycle `x` of
degree `-k`: `y ↦ (-1)^{k |y|} y • x`. -/
def DGModuleHom.shiftGen (k : ℤ) (x : X) (hx : x ∈ grading (-k)) (hdx : d x = 0) :
    Shift k A →ᵈᵍ[A] X :=
  Cocycle.homOf (Cocycle.mk (Cochain.shiftGen k x hx) 1 (zero_add 1) (Cochain.ext fun y => by
    rw [δ_zero_cochain_apply, Cochain.shiftGen_apply, Cochain.shiftGen_apply,
      d_smul_of_d_eq_zero_right hdx, Shift.unmk_d, Shift.d_twist, Units.smul_def,
      Units.smul_def, map_zsmul, sub_self, Cochain.zero_apply]))

theorem DGModuleHom.shiftGen_apply (k : ℤ) (x : X) (hx : x ∈ grading (-k)) (hdx : d x = 0)
    (y : Shift k A) :
    DGModuleHom.shiftGen k x hx hdx y = Shift.twist A k (Shift.unmk k y) • x := rfl

@[simp]
theorem DGModuleHom.shiftGen_mk_one (k : ℤ) (x : X) (hx : x ∈ grading (-k)) (hdx : d x = 0) :
    DGModuleHom.shiftGen (A := A) k x hx hdx (Shift.mk k 1) = x := by
  rw [shiftGen_apply, Shift.unmk_mk, map_one, one_smul]

@[simp]
theorem Cochain.shiftGen_mk_one (k : ℤ) (x : X) (hx : x ∈ grading (-k)) :
    Cochain.shiftGen (A := A) k x hx (Shift.mk k 1) = x := by
  rw [shiftGen_apply, Shift.unmk_mk, map_one, one_smul]

omit [DGModule A X] in
/-- A cochain of degree `0` out of a direct sum of shifts of `A` is determined by its values on
the generators. -/
theorem Cochain.ext_directSum_shift {ι : Type*} [DecidableEq ι] {k : ι → ℤ}
    {c c' : Cochain A (⨁ b, Shift (k b) A) X 0}
    (h : ∀ b, c (DirectSum.of _ b (Shift.mk (k b) 1)) = c' (DirectSum.of _ b (Shift.mk (k b) 1))) :
    c = c' := by
  refine Cochain.directSum_ext fun b y => ?_
  rw [← Shift.twist_unmk_smul_mk_one (k b) y, ← DirectSum.lof_eq_of A,
    _root_.map_smul (DirectSum.lof A ι (fun b => Shift (k b) A) b), map_smul_of_degree_zero,
    map_smul_of_degree_zero, DirectSum.lof_eq_of, h]

end Generators

/-! ### Shifts of direct sums of shifts of `A` -/

section ShiftDirectSum

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] {ι : Type*} [DecidableEq ι]
  (n : ℤ) (k : ι → ℤ)

/-- The identification `(⨁ b, A⟦k b⟧)⟦n⟧ = ⨁ b, A⟦n + k b⟧`, as an additive map (the identity
of the underlying groups). -/
def Shift.directSumAddHom : Shift n (⨁ b, Shift (k b) A) →+ ⨁ b, Shift (n + k b) A :=
  (DirectSum.map fun b =>
    (Shift.mk (n + k b)).toAddMonoidHom.comp (Shift.unmk (k b)).toAddMonoidHom).comp
    (Shift.unmk n).toAddMonoidHom

variable {n k}

omit [DGAddCommGroup A] [DGRing A] [DecidableEq ι] in
theorem Shift.directSumAddHom_apply (x : Shift n (⨁ b, Shift (k b) A)) (b : ι) :
    Shift.directSumAddHom n k x b = Shift.mk (n + k b) (Shift.unmk (k b) (Shift.unmk n x b)) :=
  DirectSum.map_apply _ _ _

variable (n k)

/-- The isomorphism `(⨁ b, A⟦k b⟧)⟦n⟧ ≅ ⨁ b, A⟦n + k b⟧` of dg modules, as a morphism (the
identity of the underlying groups). -/
def DGModuleHom.shiftDirectSum : Shift n (⨁ b, Shift (k b) A) →ᵈᵍ[A] ⨁ b, Shift (n + k b) A where
  toFun := Shift.directSumAddHom n k
  map_add' := map_add _
  map_smul' a x := by
    ext b
    rw [RingHom.id_apply, DirectSum.smul_apply, Shift.directSumAddHom_apply,
      Shift.directSumAddHom_apply, Shift.unmk_smul_eq, DirectSum.smul_apply, Shift.unmk_smul_eq,
      Shift.twist_twist, Shift.smul_mk_eq, add_comm (k b) n]
  map_mem' {i x} hx := by
    intro b
    rw [Shift.directSumAddHom_apply, Shift.mem_grading_iff, ← add_assoc]
    exact hx b
  map_d' x := by
    ext b
    rw [Shift.directSumAddHom_apply, DirectSum.coe_d_apply, Shift.directSumAddHom_apply,
      Shift.unmk_d, Units.smul_def, DFinsupp.zsmul_apply, DirectSum.coe_d_apply,
      ← Units.smul_def, Shift.unmk_units_smul,
      Shift.unmk_d, Shift.d_mk, smul_smul, ← koszulSign_add]

theorem DGModuleHom.shiftDirectSum_apply (x : Shift n (⨁ b, Shift (k b) A)) (b : ι) :
    DGModuleHom.shiftDirectSum (A := A) n k x b =
      Shift.mk (n + k b) (Shift.unmk (k b) (Shift.unmk n x b)) :=
  DirectSum.map_apply _ _ _

theorem DGModuleHom.shiftDirectSum_bijective :
    Function.Bijective (DGModuleHom.shiftDirectSum (A := A) n k) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => Shift.mk n (DirectSum.map (fun b =>
      (Shift.mk (k b)).toAddMonoidHom.comp (Shift.unmk (n + k b)).toAddMonoidHom) y),
      fun x => ?_, fun y => ?_⟩
  · apply (Shift.unmk n).injective
    ext b
    rw [Shift.unmk_mk, DirectSum.map_apply, DGModuleHom.shiftDirectSum_apply]
    rfl
  · ext b
    rw [DGModuleHom.shiftDirectSum_apply, Shift.unmk_mk, DirectSum.map_apply]
    rfl

end ShiftDirectSum

/-! ### Attaching cells -/

namespace Resolution

section Cells

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  {S : Type*} [AddCommGroup S] [DGAddCommGroup S] [Module A S] [DGModule A S]

/-- A cell to be attached to a dg module `S` over `M` (given by a morphism `p : S → M`): a
cocycle `z` of degree `deg` and an element `m` of degree `deg - 1` of `M` with `p z = d m`.
Attaching the cell adds a free generator `e` of degree `deg - 1` with `d e = z`, mapped to
`m`. -/
structure Cell (p : S →ᵈᵍ[A] M) where
  /-- The degree of the cocycle to be killed. -/
  deg : ℤ
  /-- The cocycle to be killed. -/
  z : S
  /-- The image in `M` of the new generator. -/
  m : M
  z_mem : z ∈ grading deg
  d_z : d z = 0
  m_mem : m ∈ grading (deg - 1)
  p_z : p z = d m

variable (p : S →ᵈᵍ[A] M)

noncomputable instance : DecidableEq (Cell p) := Classical.decEq _

/-- The free dg module `⨁ c, A⟦-deg c⟧` on the cells, generated by the cocycles
`1 ∈ A⟦-deg c⟧`, of degree `deg c`. -/
abbrev Cells : Type _ := ⨁ c : Cell p, Shift (-c.deg) A

variable {p}

/-- The generator of `Cells p` attached to a cell. -/
noncomputable def Cell.gen (c : Cell p) : Cells p :=
  DirectSum.of _ c (Shift.mk (-c.deg) 1)

omit [DGModule A M] [DGModule A S] in
theorem Cell.gen_mem (c : Cell p) : c.gen ∈ grading c.deg :=
  DirectSum.of_mem_grading _ c
    (by simpa using Shift.mk_mem_grading (n := -c.deg) (one_mem_grading (A := A)))

omit [DGModule A M] [DGModule A S] in
theorem Cell.d_gen (c : Cell p) : d c.gen = 0 := by
  rw [Cell.gen, DirectSum.d_of, Shift.d_mk, d_one, smul_zero, Shift.mk_zero, map_zero]

variable (p)

/-- The attaching map `Cells p → S`, sending the generator of a cell to its cocycle. -/
noncomputable def attach : Cells p →ᵈᵍ[A] S :=
  DGModuleHom.toModule fun c =>
    DGModuleHom.shiftGen (-c.deg) c.z (by rw [neg_neg]; exact c.z_mem) c.d_z

omit [DGRing A] [DGModule A M] [DGModule A S] in
theorem mk_m_mem (c : Cell p) : Shift.mk (-1) c.m ∈ grading (-(-c.deg)) := by
  have h := Shift.mk_mem_grading (n := -1) c.m_mem
  rwa [show c.deg - 1 - -1 = -(-c.deg) by ring] at h

/-- The cochain of degree `-1` on the cells sending the generator of a cell to its element of
`M`; it is a null-homotopy of `p ∘ attach p` (`DG.Resolution.δ_homotopy`). -/
noncomputable def homotopy : Cochain A (Cells p) M (-1) :=
  (Cochain.directSumDesc fun c : Cell p =>
    Cochain.shiftGen (-c.deg) (Shift.mk (-1) c.m) (mk_m_mem p c)).rightUnshift (-1) (zero_add _)

variable {p}

omit [DGModule A M] in
@[simp]
theorem attach_gen (c : Cell p) : attach p c.gen = c.z := by
  rw [Cell.gen, attach, DGModuleHom.toModule_lof, DGModuleHom.shiftGen_mk_one]

omit [DGModule A S] in
@[simp]
theorem homotopy_gen (c : Cell p) : homotopy p c.gen = c.m := by
  rw [homotopy, Cochain.rightUnshift_apply, Cell.gen, Cochain.directSumDesc_of,
    Cochain.shiftGen_mk_one, Shift.unmk_mk]

variable (p)

theorem δ_homotopy : δ (-1) 0 (homotopy p) = Cochain.ofHom (p.comp (attach p)) :=
  Cochain.ext_directSum_shift fun c => by
    change δ (-1) 0 (homotopy p) c.gen = Cochain.ofHom (p.comp (attach p)) c.gen
    rw [δ_neg_one_apply, Cell.d_gen, map_zero, add_zero, homotopy_gen, Cochain.ofHom_apply,
      DGModuleHom.comp_apply, attach_gen, c.p_z]

end Cells

section Stages

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- A stage of the construction of the resolution: a dg module with a morphism to `M`. -/
structure Stage where
  /-- The dg module. -/
  obj : DGModuleCat.{max u v} A
  /-- The morphism to `M`. -/
  π : obj →ᵈᵍ[A] M

variable {A M}

/-- The next stage: the cone of the attaching map of all cells, `Cone (attach π)`, with the
morphism to `M` given by `π` and the null-homotopy `homotopy π` of `π ∘ attach π`. -/
noncomputable def Stage.step (s : Stage A M) : Stage A M where
  obj := DGModuleCat.of A (Cone (attach s.π))
  π := Cone.desc (attach s.π) (homotopy s.π) s.π (δ_homotopy s.π)

/-- Attaching a cell: a cocycle `z` of a stage whose image in `M` is a coboundary `d m` becomes
the coboundary of an element of the next stage mapped to `m`. -/
theorem Stage.exists_step (s : Stage A M) {j : ℤ} {z : s.obj} (hz : z ∈ grading j)
    (hdz : d z = 0) {m : M} (hm : m ∈ grading (j - 1)) (hpz : s.π z = d m) :
    ∃ e : s.step.obj, e ∈ grading (j - 1) ∧ d e = Cone.inr (attach s.π) z ∧ s.step.π e = m := by
  let c : Cell s.π := ⟨j, z, m, hz, hdz, hm, hpz⟩
  refine ⟨Cone.inl (attach s.π) c.gen, ?_, ?_, ?_⟩
  · have h := (Cone.inl (attach s.π)).map_mem c.gen_mem
    rwa [← sub_eq_add_neg] at h
  · have h := Cone.inl_d_apply (f := attach s.π) c.gen
    rw [c.d_gen, map_zero, sub_zero, attach_gen] at h
    exact h
  · exact (Cone.inl_desc_apply _ _ _ (δ_homotopy s.π) _).trans (homotopy_gen c)

variable (A M)

/-- The stages of the construction: `0`, then iterated attachment of all cells. -/
noncomputable def stage : ℕ → Stage A M
  | 0 => ⟨DGModuleCat.of A PUnit, 0⟩
  | n + 1 => (stage n).step

/-- The underlying dg module of the `n`-th stage. -/
abbrev Obj (n : ℕ) : Type (max u v) := (stage A M n).obj

/-- The inclusion of the `n`-th stage into the next one. -/
noncomputable def ι (n : ℕ) : Obj A M n →ᵈᵍ[A] Obj A M (n + 1) :=
  Cone.inr (attach (stage A M n).π)

theorem ι_injective (n : ℕ) : Function.Injective (ι A M n) := fun _ _ h =>
  congrArg (Cone.sndLinear (attach (stage A M n).π)) h

/-- The underlying dg module of the resolution: the colimit of the stages. -/
abbrev Colim : Type (max u v) := SeqColimit (Obj A M) (ι A M)

theorem stage_succ_π_comp_ι (n : ℕ) : (stage A M (n + 1)).π.comp (ι A M n) = (stage A M n).π :=
  Cone.inr_desc _ _ _ (δ_homotopy _)

/-- The augmentation of the resolution. -/
noncomputable def π : Colim A M →ᵈᵍ[A] M :=
  SeqColimit.desc (fun n => (stage A M n).π) (stage_succ_π_comp_ι A M)

variable {A M}

theorem π_of (n : ℕ) (x : Obj A M n) : π A M (SeqColimit.of _ _ n x) = (stage A M n).π x :=
  SeqColimit.desc_of _ _ _ _

theorem exists_step (n : ℕ) {j : ℤ} {z : Obj A M n} (hz : z ∈ grading j) (hdz : d z = 0) {m : M}
    (hm : m ∈ grading (j - 1)) (hpz : (stage A M n).π z = d m) :
    ∃ e : Obj A M (n + 1), e ∈ grading (j - 1) ∧ d e = ι A M n z ∧ (stage A M (n + 1)).π e = m :=
  (stage A M n).exists_step hz hdz hm hpz

/-- Every cocycle of `M` is the image of a cocycle of the first stage. -/
theorem exists_stage_one {j : ℤ} {m : M} (hm : m ∈ grading j) (hdm : d m = 0) :
    ∃ e : Obj A M 1, e ∈ grading j ∧ d e = 0 ∧ (stage A M 1).π e = m := by
  obtain ⟨e, he, hde, hpe⟩ := exists_step (A := A) 0 (j := j + 1) (z := 0) (zero_mem _) d_zero
    (m := m) (by rwa [add_sub_cancel_right]) (by rw [map_zero, hdm])
  rw [add_sub_cancel_right] at he
  rw [map_zero] at hde
  exact ⟨e, he, hde, hpe⟩

variable (A M)

/-- The augmentation of the resolution is surjective. -/
theorem surjective_π : Function.Surjective (π A M) := by
  intro m
  induction m using DG.induction_on with
  | h_zero => exact ⟨0, map_zero _⟩
  | h_homogeneous m =>
    rename_i j
    obtain ⟨e₁, he₁, hde₁, hpe₁⟩ := exists_stage_one (A := A) (d_mem m.2) (d_d _)
    obtain ⟨e₂, -, -, hpe₂⟩ := exists_step 1 he₁ hde₁ (m := m)
      (by rw [add_sub_cancel_right]; exact m.2) hpe₁
    exact ⟨SeqColimit.of _ _ 2 e₂, by rw [π_of, hpe₂]⟩
  | h_add m m' hm hm' =>
    obtain ⟨x, rfl⟩ := hm
    obtain ⟨y, rfl⟩ := hm'
    exact ⟨x + y, map_add _ _ _⟩

/-- The augmentation of the resolution is a quasi-isomorphism. -/
theorem isQuasiIso_π : (π A M).IsQuasiIso := fun j => by
  constructor
  · rw [cohomology.map_injective_iff]
    intro x hx hdx hpx
    obtain ⟨n, y, rfl⟩ := SeqColimit.exists_of_eq x
    have hinj := SeqColimit.of_injective (ι_injective A M) n
    have hy : y ∈ grading j := (SeqColimit.of _ _ n).mem_grading_of_injective hinj hx
    have hdy : d y = 0 := hinj (by rw [DGModuleHom.map_d, hdx, map_zero])
    obtain ⟨m, hm, hdm⟩ := mem_coboundaries.mp hpx
    rw [π_of] at hdm
    obtain ⟨e, he, hde, -⟩ := exists_step n hy hdy hm hdm.symm
    exact mem_coboundaries.mpr ⟨SeqColimit.of _ _ (n + 1) e,
      (SeqColimit.of _ _ (n + 1)).map_mem he, by
        rw [← DGModuleHom.map_d, hde, SeqColimit.of_succ_ι]⟩
  · rw [cohomology.map_surjective_iff]
    intro m hm hdm
    obtain ⟨e, he, hde, hpe⟩ := exists_stage_one (A := A) hm hdm
    exact ⟨SeqColimit.of _ _ 1 e, (SeqColimit.of _ _ 1).map_mem he,
      by rw [← DGModuleHom.map_d, hde, map_zero], by rw [π_of, hpe, sub_self]; exact zero_mem _⟩

/-! ### The semi-free filtration -/

theorem bijective_rangeRestrict (n : ℕ) :
    Function.Bijective (SeqColimit.of (Obj A M) (ι A M) n).rangeRestrict :=
  ⟨fun _ _ h => SeqColimit.of_injective (ι_injective A M) n (congrArg Subtype.val h),
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩⟩

/-- The `n`-th member of the filtration of the resolution, identified with the `n`-th stage. -/
noncomputable def toObj (n : ℕ) :
    SeqColimit.filtration (S := Obj A M) (ι := ι A M) n →ᵈᵍ[A] Obj A M n :=
  (SeqColimit.of _ _ n).rangeRestrict.inverse (bijective_rangeRestrict A M n)

variable {A M}

theorem of_toObj {n : ℕ} (x : SeqColimit.filtration (S := Obj A M) (ι := ι A M) n) :
    SeqColimit.of _ _ n (toObj A M n x) = (x : SeqColimit (Obj A M) (ι A M)) :=
  congrArg Subtype.val (DGModuleHom.apply_inverse_apply _ (bijective_rangeRestrict A M n) x)

theorem toObj_eq {n : ℕ} {x : SeqColimit.filtration (S := Obj A M) (ι := ι A M) n}
    {y : Obj A M n} (h : SeqColimit.of _ _ n y = (x : SeqColimit (Obj A M) (ι A M))) :
    toObj A M n x = y :=
  SeqColimit.of_injective (ι_injective A M) n (by rw [of_toObj, h])

variable (A M)

/-- The projection of the `(n + 1)`-st member of the filtration onto the generators attached at
stage `n + 1`. -/
noncomputable def filtrationπ (n : ℕ) :
    SeqColimit.filtration (S := Obj A M) (ι := ι A M) (n + 1) →ᵈᵍ[A]
      ⨁ c : Cell (stage A M n).π, Shift (1 + -c.deg) A :=
  (DGModuleHom.shiftDirectSum 1 fun c : Cell (stage A M n).π => -c.deg).comp
    ((Cone.fstHom (attach (stage A M n).π)).comp (toObj A M (n + 1)))

theorem surjective_filtrationπ (n : ℕ) : Function.Surjective (filtrationπ A M n) := by
  refine (DGModuleHom.shiftDirectSum_bijective _ _).2.comp
    (Function.Surjective.comp (fun y => ⟨Cone.inlLinear _ y, Cone.fstHom_inlLinear y⟩) ?_)
  intro y
  exact ⟨⟨SeqColimit.of _ _ (n + 1) y, SeqColimit.of_mem_filtration (ι := ι A M) (n + 1) y⟩,
    toObj_eq rfl⟩

theorem filtrationπ_eq_zero_iff (n : ℕ)
    (x : SeqColimit.filtration (S := Obj A M) (ι := ι A M) (n + 1)) :
    filtrationπ A M n x = 0 ↔ (x : Colim A M) ∈ SeqColimit.filtration n := by
  rw [filtrationπ, DGModuleHom.comp_apply,
    map_eq_zero_iff _ (DGModuleHom.shiftDirectSum_bijective _ _).1, DGModuleHom.comp_apply]
  constructor
  · intro h
    have hy : toObj A M (n + 1) x =
        ι A M n (Cone.sndLinear (attach (stage A M n).π) (toObj A M (n + 1) x)) :=
      Cone.ext (h.trans (Cone.fstHom_inr _).symm) (Cone.sndLinear_inr _).symm
    refine ⟨Cone.sndLinear (attach (stage A M n).π) (toObj A M (n + 1) x), ?_⟩
    change SeqColimit.of _ _ n _ = _
    rw [← SeqColimit.of_succ_ι (ι := ι A M), ← hy, of_toObj]
  · rintro ⟨y, hy⟩
    have h' : toObj A M (n + 1) x = ι A M n y := toObj_eq (by rw [SeqColimit.of_succ_ι]; exact hy)
    exact (congrArg (Cone.fstHom (attach (stage A M n).π)) h').trans (Cone.fstHom_inr y)

/-- The resolution is semi-free: the images of the stages form a semi-free filtration, the
subquotient `Fₙ₊₁ / Fₙ` being free on the cells attached at stage `n + 1`. -/
noncomputable def semiFreeFiltration : SemiFreeFiltration.{max u v} A (Colim A M) where
  F := SeqColimit.filtration
  mono := SeqColimit.filtration_mono
  eq_zero_of_mem_zero x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact map_zero (SeqColimit.of (Obj A M) (ι A M) 0)
  exists_mem := SeqColimit.exists_mem_filtration
  ι n := Cell (stage A M n).π
  decEq _ := inferInstance
  deg _ c := 1 + -c.deg
  π := filtrationπ A M
  surjective_π := surjective_filtrationπ A M
  π_eq_zero_iff := filtrationπ_eq_zero_iff A M

end Stages

end Resolution

/-! ### Existence of semi-free resolutions -/

section Existence

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- Every dg module `M` has a semi-free resolution: a surjective quasi-isomorphism `P → M` from a
semi-free dg module `P` [Keller, *Deriving DG categories*, §3.1, Thm. 3.1 (a)];
[Bernstein–Lunts 10.12.2.4]; [Stacks 09KV]. For `A : Type u` and `M : Type v` the module `P`
lives in `Type (max u v)`: its generators are indexed by elements of `M` and of earlier stages
of the construction (`DG.Resolution.Colim`). -/
theorem exists_semiFreeResolution :
    ∃ (P : Type (max u v)) (_ : AddCommGroup P) (_ : DGAddCommGroup P) (_ : Module A P)
      (_ : DGModule A P) (π : P →ᵈᵍ[A] M), Function.Surjective π ∧ π.IsQuasiIso ∧
        Nonempty (SemiFreeFiltration.{max u v} A P) :=
  ⟨Resolution.Colim A M, inferInstance, inferInstance, inferInstance, inferInstance,
    Resolution.π A M, Resolution.surjective_π A M,
    Resolution.isQuasiIso_π A M, ⟨Resolution.semiFreeFiltration A M⟩⟩

end Existence

/-! ### Uniqueness and functoriality up to homotopy -/

section Uniqueness

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {P : Type*} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

omit [DGRing A] in
/-- Maps from a K-projective module to a module `Q` with a surjective quasi-isomorphism
`q : Q → N` are determined up to homotopy by their composite with `q`: if `q ∘ f₁ = q ∘ f₂`, then
`f₁ ≃ f₂`, since `f₁ - f₂` lands in the acyclic kernel of `q`. -/
theorem IsKProjective.homotopic_of_comp_eq {Q : Type w} [AddCommGroup Q] [DGAddCommGroup Q]
    [Module A Q] [DGModule A Q] {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]
    [DGModule A N] (hP : IsKProjective.{w} A P) {q : Q →ᵈᵍ[A] N} (hq : Function.Surjective q)
    (hqq : q.IsQuasiIso) {f₁ f₂ : P →ᵈᵍ[A] Q} (h : q.comp f₁ = q.comp f₂) : Homotopic f₁ f₂ := by
  rw [Homotopic.iff_sub]
  have hmem : ∀ x, (f₁ - f₂) x ∈ q.ker := fun x => by
    rw [DGModuleHom.mem_ker, DGModuleHom.sub_apply, map_sub, ← DGModuleHom.comp_apply, h,
      DGModuleHom.comp_apply, sub_self]
  have h1 := (hP q.ker (q.isAcyclic_ker hq hqq) (DGSubmodule.codRestrict (f₁ - f₂) hmem)).comp_right
    q.ker.subtype
  rwa [DGSubmodule.subtype_comp_codRestrict, DGModuleHom.comp_zero] at h1

variable {N N' : Type w} [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup N'] [DGAddCommGroup N'] [Module A N'] [DGModule A N']

/-- For a K-projective `P` and a quasi-isomorphism `s : N → N'`, every morphism `P → N'` factors
through `s` up to homotopy. -/
theorem IsKProjective.exists_homotopic_comp (hP : IsKProjective.{w} A P) {s : N →ᵈᵍ[A] N'}
    (hs : s.IsQuasiIso) (g : P →ᵈᵍ[A] N') : ∃ f : P →ᵈᵍ[A] N, Homotopic (s.comp f) g := by
  obtain ⟨c, hc⟩ := (hP.bijective_postcompHomotopy hs).2 (QuotientAddGroup.mk g)
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [DGModuleHom.postcompHomotopy_mk, QuotientAddGroup.eq_iff_sub_mem] at hc
  exact ⟨f, homotopic_iff_sub_mem.mpr hc⟩

/-- For a K-projective `P` and a quasi-isomorphism `s : N → N'`, morphisms `f₁ f₂ : P → N` with
`s ∘ f₁ ≃ s ∘ f₂` are homotopic. -/
theorem IsKProjective.homotopic_of_homotopic_comp (hP : IsKProjective.{w} A P)
    {s : N →ᵈᵍ[A] N'} (hs : s.IsQuasiIso) {f₁ f₂ : P →ᵈᵍ[A] N}
    (h : Homotopic (s.comp f₁) (s.comp f₂)) : Homotopic f₁ f₂ := by
  have h' : DGModuleHom.postcompHomotopy P s (QuotientAddGroup.mk f₁) =
      DGModuleHom.postcompHomotopy P s (QuotientAddGroup.mk f₂) := by
    rw [DGModuleHom.postcompHomotopy_mk, DGModuleHom.postcompHomotopy_mk,
      QuotientAddGroup.eq_iff_sub_mem, ← homotopic_iff_sub_mem]
    exact h
  exact homotopic_iff_sub_mem.mpr
    (QuotientAddGroup.eq_iff_sub_mem.mp ((hP.bijective_postcompHomotopy hs).1 h'))

end Uniqueness

section HomotopyEquiv

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {P P' M : Type w} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
  [AddCommGroup P'] [DGAddCommGroup P'] [Module A P'] [DGModule A P']
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- Uniqueness of K-projective resolutions up to homotopy equivalence: if `p : P → M` and
`p' : P' → M` are quasi-isomorphisms from K-projective modules, there is a homotopy equivalence
`e : P ≃ P'` with `p' ∘ e ≃ p` and `p ∘ e⁻¹ ≃ p'`. -/
theorem IsKProjective.exists_dgHomotopyEquiv (hP : IsKProjective.{w} A P)
    (hP' : IsKProjective.{w} A P')
    {p : P →ᵈᵍ[A] M} (hp : p.IsQuasiIso) {p' : P' →ᵈᵍ[A] M} (hp' : p'.IsQuasiIso) :
    ∃ e : DGHomotopyEquiv A P P', Homotopic (p'.comp e.hom) p ∧ Homotopic (p.comp e.inv) p' := by
  obtain ⟨φ, hφ⟩ := hP.exists_homotopic_comp hp' p
  obtain ⟨ψ, hψ⟩ := hP'.exists_homotopic_comp hp p'
  have h₁ : Homotopic (ψ.comp φ) DGModuleHom.id :=
    hP.homotopic_of_homotopic_comp hp ((hψ.comp_left φ).trans hφ)
  have h₂ : Homotopic (φ.comp ψ) DGModuleHom.id :=
    hP'.homotopic_of_homotopic_comp hp' ((hφ.comp_left ψ).trans hψ)
  exact ⟨⟨φ, ψ, h₁.some, h₂.some⟩, hφ, hψ⟩

/-- Uniqueness of cofibrant (e.g. semi-free) resolutions up to homotopy equivalence over `M`: if
`p : P → M` and `p' : P' → M` are surjective quasi-isomorphisms and `P`, `P'` have the lifting
property against surjective quasi-isomorphisms, there is a homotopy equivalence `e : P ≃ P'` with
`p' ∘ e = p` and `p ∘ e⁻¹ = p'`. -/
theorem HasLiftingProperty.exists_dgHomotopyEquiv (hP : HasLiftingProperty.{w} A P)
    (hP' : HasLiftingProperty.{w} A P') {p : P →ᵈᵍ[A] M} (hps : Function.Surjective p)
    (hp : p.IsQuasiIso) {p' : P' →ᵈᵍ[A] M} (hps' : Function.Surjective p')
    (hp' : p'.IsQuasiIso) :
    ∃ e : DGHomotopyEquiv A P P', p'.comp e.hom = p ∧ p.comp e.inv = p' := by
  obtain ⟨φ, hφ⟩ := hP P' M p' hps' hp' p
  obtain ⟨ψ, hψ⟩ := hP' P M p hps hp p'
  have h₁ : Homotopic (ψ.comp φ) DGModuleHom.id :=
    hP.isKProjective.homotopic_of_comp_eq hps hp (by rw [← DGModuleHom.comp_assoc, hψ, hφ]; rfl)
  have h₂ : Homotopic (φ.comp ψ) DGModuleHom.id :=
    hP'.isKProjective.homotopic_of_comp_eq hps' hp' (by rw [← DGModuleHom.comp_assoc, hφ, hψ]; rfl)
  exact ⟨⟨φ, ψ, h₁.some, h₂.some⟩, hφ, hψ⟩

end HomotopyEquiv

/-! ### Bundled semi-free resolutions -/

section Bundled

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type w) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- A semi-free resolution of a dg module `M`: a surjective quasi-isomorphism `π : P → M` from a
dg module `P` with a chosen semi-free filtration (whose generators are indexed by types in the
universe `w` of `M`). -/
structure SemiFreeResolution where
  /-- The underlying type of the resolving module. -/
  P : Type w
  [addCommGroup : AddCommGroup P]
  [dgAddCommGroup : DGAddCommGroup P]
  [module : Module A P]
  [dgModule : DGModule A P]
  /-- The augmentation `P → M`. -/
  π : P →ᵈᵍ[A] M
  surjective_π : Function.Surjective π
  isQuasiIso_π : π.IsQuasiIso
  /-- A semi-free filtration of `P`. -/
  filtration : SemiFreeFiltration.{w} A P

attribute [instance] SemiFreeResolution.addCommGroup SemiFreeResolution.dgAddCommGroup
  SemiFreeResolution.module SemiFreeResolution.dgModule

namespace SemiFreeResolution

variable {A M}

omit [DGModule A M] in
/-- The resolving module of a semi-free resolution has the lifting property against surjective
quasi-isomorphisms (for test modules in any universe). -/
theorem hasLiftingProperty (R : SemiFreeResolution A M) : HasLiftingProperty.{w'} A R.P :=
  R.filtration.hasLiftingProperty

omit [DGModule A M] in
/-- The resolving module of a semi-free resolution is K-projective. -/
theorem isKProjective (R : SemiFreeResolution A M) : IsKProjective.{w'} A R.P :=
  R.filtration.isKProjective

/-- Any two semi-free resolutions of `M` are homotopy equivalent over `M`. -/
theorem exists_dgHomotopyEquiv (R R' : SemiFreeResolution A M) :
    ∃ e : DGHomotopyEquiv A R.P R'.P, R'.π.comp e.hom = R.π ∧ R.π.comp e.inv = R'.π :=
  R.hasLiftingProperty.exists_dgHomotopyEquiv R'.hasLiftingProperty R.surjective_π
    R.isQuasiIso_π R'.surjective_π R'.isQuasiIso_π

/-- The homotopy equivalence over `M` between two semi-free resolutions of `M`. -/
noncomputable def dgHomotopyEquiv (R R' : SemiFreeResolution A M) : DGHomotopyEquiv A R.P R'.P :=
  (R.exists_dgHomotopyEquiv R').choose

@[simp]
theorem π_comp_dgHomotopyEquiv_hom (R R' : SemiFreeResolution A M) :
    R'.π.comp (R.dgHomotopyEquiv R').hom = R.π :=
  (R.exists_dgHomotopyEquiv R').choose_spec.1

@[simp]
theorem π_comp_dgHomotopyEquiv_inv (R R' : SemiFreeResolution A M) :
    R.π.comp (R.dgHomotopyEquiv R').inv = R'.π :=
  (R.exists_dgHomotopyEquiv R').choose_spec.2

variable {N L : Type w} [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup L] [DGAddCommGroup L] [Module A L] [DGModule A L]

omit [DGModule A M] in
/-- A morphism `g : M → N` lifts to semi-free resolutions: `R'.π ∘ R.lift R' g = g ∘ R.π`. -/
noncomputable def lift (R : SemiFreeResolution A M) (R' : SemiFreeResolution A N)
    (g : M →ᵈᵍ[A] N) : R.P →ᵈᵍ[A] R'.P :=
  (R.hasLiftingProperty R'.P N R'.π R'.surjective_π R'.isQuasiIso_π (g.comp R.π)).choose

omit [DGModule A M] in
@[simp]
theorem π_comp_lift (R : SemiFreeResolution A M) (R' : SemiFreeResolution A N)
    (g : M →ᵈᵍ[A] N) : R'.π.comp (R.lift R' g) = g.comp R.π :=
  (R.hasLiftingProperty R'.P N R'.π R'.surjective_π R'.isQuasiIso_π (g.comp R.π)).choose_spec

omit [DGModule A M] in
/-- The lift of `g : M → N` to resolutions is unique up to homotopy: every `f : R.P → R'.P`
with `R'.π ∘ f ≃ g ∘ R.π` is homotopic to it. -/
theorem homotopic_lift (R : SemiFreeResolution A M) (R' : SemiFreeResolution A N)
    {g : M →ᵈᵍ[A] N} {f : R.P →ᵈᵍ[A] R'.P} (h : Homotopic (R'.π.comp f) (g.comp R.π)) :
    Homotopic f (R.lift R' g) :=
  R.isKProjective.homotopic_of_homotopic_comp R'.isQuasiIso_π
    (h.trans (Homotopic.of_eq (R.π_comp_lift R' g).symm))

/-- Homotopic morphisms have homotopic lifts. -/
theorem lift_homotopic (R : SemiFreeResolution A M) (R' : SemiFreeResolution A N)
    {g₁ g₂ : M →ᵈᵍ[A] N} (h : Homotopic g₁ g₂) : Homotopic (R.lift R' g₁) (R.lift R' g₂) :=
  R.homotopic_lift R' ((Homotopic.of_eq (R.π_comp_lift R' g₁)).trans (h.comp_left R.π))

/-- The lift of the identity is homotopic to the identity. -/
theorem lift_id (R : SemiFreeResolution A M) : Homotopic (R.lift R DGModuleHom.id) DGModuleHom.id :=
  (R.homotopic_lift R (f := DGModuleHom.id) (Homotopic.refl _)).symm

omit [DGModule A M] in
/-- Lifts to resolutions are compatible with composition up to homotopy. -/
theorem lift_comp (R : SemiFreeResolution A M) (R' : SemiFreeResolution A N)
    (R'' : SemiFreeResolution A L) (g : M →ᵈᵍ[A] N) (g' : N →ᵈᵍ[A] L) :
    Homotopic (R.lift R'' (g'.comp g)) ((R'.lift R'' g').comp (R.lift R' g)) := by
  refine (R.homotopic_lift R'' (Homotopic.of_eq ?_)).symm
  rw [← DGModuleHom.comp_assoc, π_comp_lift, DGModuleHom.comp_assoc, π_comp_lift]
  rfl

end SemiFreeResolution

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type (max u v)) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- The standard semi-free resolution of a dg module `M` whose universe contains that of `A`
(`DG.Resolution.Colim`). -/
noncomputable def semiFreeResolution : SemiFreeResolution A M where
  P := Resolution.Colim A M
  π := Resolution.π A M
  surjective_π := Resolution.surjective_π A M
  isQuasiIso_π := Resolution.isQuasiIso_π A M
  filtration := Resolution.semiFreeFiltration A M

end Bundled

/-! ### Cofibrant and K-projective modules via semi-free modules -/

section Cofibrant

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The lifting property against surjective quasi-isomorphisms passes to retracts. -/
theorem HasLiftingProperty.of_retract {P Q : Type*} [AddCommGroup P] [DGAddCommGroup P]
    [Module A P] [DGModule A P] [AddCommGroup Q] [DGAddCommGroup Q] [Module A Q] [DGModule A Q]
    (hP : HasLiftingProperty.{w} A P) (i : Q →ᵈᵍ[A] P) (r : P →ᵈᵍ[A] Q)
    (hri : r.comp i = DGModuleHom.id) : HasLiftingProperty.{w} A Q :=
  hasLiftingProperty_iff.mpr ⟨(hasLiftingProperty_iff.mp hP).1.of_retract i r
    (Homotopic.of_eq hri), (hasLiftingProperty_iff.mp hP).2.of_retract i r hri⟩

variable {P : Type (max u v)} [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- The cofibrant dg modules (those with the lifting property against surjective
quasi-isomorphisms) are exactly the retracts of semi-free dg modules. The forward direction
lifts the identity of `P` along a semi-free resolution of `P`. -/
theorem hasLiftingProperty_iff_exists_retract :
    HasLiftingProperty.{max u v} A P ↔
      ∃ (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : DGAddCommGroup Q) (_ : Module A Q)
        (_ : DGModule A Q) (_ : SemiFreeFiltration.{max u v} A Q) (i : P →ᵈᵍ[A] Q)
        (r : Q →ᵈᵍ[A] P), r.comp i = DGModuleHom.id := by
  constructor
  · intro h
    let R := semiFreeResolution A P
    obtain ⟨i, hi⟩ := h R.P P R.π R.surjective_π R.isQuasiIso_π DGModuleHom.id
    exact ⟨R.P, inferInstance, inferInstance, inferInstance, inferInstance, R.filtration, i, R.π,
      hi⟩
  · rintro ⟨Q, _, _, _, _, S, i, r, hri⟩
    exact S.hasLiftingProperty.of_retract i r hri

/-- The K-projective dg modules are exactly the dg modules homotopy equivalent to semi-free dg
modules. -/
theorem isKProjective_iff_exists_dgHomotopyEquiv :
    IsKProjective.{max u v} A P ↔
      ∃ (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : DGAddCommGroup Q) (_ : Module A Q)
        (_ : DGModule A Q) (_ : SemiFreeFiltration.{max u v} A Q),
          Nonempty (DGHomotopyEquiv A P Q) := by
  constructor
  · intro h
    let R := semiFreeResolution A P
    obtain ⟨e, -, -⟩ := h.exists_dgHomotopyEquiv R.isKProjective (p := DGModuleHom.id)
      DGModuleHom.isQuasiIso_id R.isQuasiIso_π
    exact ⟨R.P, inferInstance, inferInstance, inferInstance, inferInstance, R.filtration, ⟨e⟩⟩
  · rintro ⟨Q, _, _, _, _, S, ⟨e⟩⟩
    exact S.isKProjective.of_dgHomotopyEquiv e

end Cofibrant

end DG
