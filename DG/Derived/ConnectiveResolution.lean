import DG.Derived.Resolution

/-!
# Semi-free resolutions in non-positive degrees

Let `A` be a dg ring concentrated in non-positive degrees (`Aⁿ = 0` for `n > 0`; such dg rings
are often called *connective*). This file shows that every dg `A`-module `M` concentrated in
non-positive degrees has a semi-free resolution `P → M` with `P` again concentrated in
non-positive degrees.

The construction is that of `DG/Derived/Resolution.lean` (attaching cells along a sequence of
stages), restricted to the cells of degree `≤ 1`, i.e. to new generators of degree `≤ 0`
(`DG.ConnectiveResolution.LowCell`). Since `A` is concentrated in non-positive degrees, so is
`A⟦-k⟧` for `k ≤ 0`, hence so is every stage. The restriction does not affect the proof that
the augmentation is a quasi-isomorphism: the cocycles of `M` to be hit, and the cocycles of the
stages to be killed, all have degree `≤ 0`.

## Main definitions and results

* `DG.IsNonposGraded M`: `Mⁿ = 0` for all `n > 0`.
* `DG.ConnectiveResolution.Colim A M`, `DG.ConnectiveResolution.π A M`: the resolution and its
  augmentation; `DG.ConnectiveResolution.isQuasiIso_π`,
  `DG.ConnectiveResolution.semiFreeFiltration`,
  `DG.ConnectiveResolution.isNonposGraded_colim`.
* `DG.exists_semiFreeResolution_of_isNonposGraded`: the existence statement.

This is the input for the truncation (t-)structure on the derived category of a dg ring
concentrated in non-positive degrees (`DG/Derived/TStructure.lean`): morphisms in `D(A)` from a
module concentrated in non-positive degrees to a module concentrated in positive degrees vanish.

## References

* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994), §3]
* [The Stacks project, Tag 09KK]
-/

open DirectSum

universe u v

set_option backward.isDefEq.respectTransparency false

namespace DG

/-! ### Dg abelian groups concentrated in non-positive degrees -/

section NonposGraded

/-- A dg abelian group (or dg ring, or dg module) is concentrated in non-positive degrees if
`Mⁿ = 0` for all `n > 0`. -/
def IsNonposGraded (M : Type*) [AddCommGroup M] [DGAddCommGroup M] : Prop :=
  ∀ n : ℤ, 0 < n → grading (M := M) n = ⊥

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M]

theorem IsNonposGraded.eq_zero (hM : IsNonposGraded M) {n : ℤ} (hn : 0 < n) {x : M}
    (hx : x ∈ grading n) : x = 0 := by
  rw [hM n hn] at hx
  exact hx

theorem isNonposGraded_iff :
    IsNonposGraded M ↔ ∀ ⦃n : ℤ⦄, 0 < n → ∀ ⦃x : M⦄, x ∈ grading n → x = 0 :=
  ⟨fun h _ hn _ hx => h.eq_zero hn hx, fun h _ hn => eq_bot_iff.mpr fun _ hx => h hn hx⟩

/-- A degree-`0` injective morphism into a module concentrated in non-positive degrees has
source concentrated in non-positive degrees. -/
theorem IsNonposGraded.of_injective {A : Type*} [Ring A] [DGAddCommGroup A] [Module A M]
    {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] (hN : IsNonposGraded N)
    (f : M →ᵈᵍ[A] N) (hf : Function.Injective f) : IsNonposGraded M :=
  isNonposGraded_iff.mpr fun _ hn _ hx => hf (by rw [hN.eq_zero hn (f.map_mem hx), map_zero])

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

omit [DGRing A] in
/-- `A⟦k⟧` is concentrated in non-positive degrees when `A` is and `k ≥ 0`. -/
theorem IsNonposGraded.shift (hA : IsNonposGraded A) {k : ℤ} (hk : 0 ≤ k) :
    IsNonposGraded (Shift k A) :=
  isNonposGraded_iff.mpr fun n hn x hx =>
    (Shift.unmk k).injective (by
      rw [hA.eq_zero (by omega) (Shift.unmk_mem_grading hx)]; rfl)

end NonposGraded

namespace ConnectiveResolution

open Resolution

/-! ### Attaching cells of degree at most `1` -/

section Cells

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  {S : Type*} [AddCommGroup S] [DGAddCommGroup S] [Module A S] [DGModule A S]

variable (p : S →ᵈᵍ[A] M)

/-- The cells of degree at most `1` over `p : S → M`: attaching such a cell adds a generator of
degree `≤ 0`. -/
abbrev LowCell : Type _ := {c : Cell p // c.deg ≤ 1}

/-- The free dg module `⨁ c, A⟦-deg c⟧` on the cells of degree at most `1`. -/
abbrev LowCells : Type _ := ⨁ c : LowCell p, Shift (-c.1.deg) A

variable {p}

/-- The generator of `LowCells p` attached to a cell. -/
noncomputable def LowCell.gen (c : LowCell p) : LowCells p :=
  DirectSum.of _ c (Shift.mk (-c.1.deg) 1)

omit [DGModule A M] [DGModule A S] in
theorem LowCell.gen_mem (c : LowCell p) : c.gen ∈ grading c.1.deg :=
  DirectSum.of_mem_grading _ c
    (by simpa using Shift.mk_mem_grading (n := -c.1.deg) (one_mem_grading (A := A)))

omit [DGModule A M] [DGModule A S] in
theorem LowCell.d_gen (c : LowCell p) : d c.gen = 0 := by
  rw [LowCell.gen, DirectSum.d_of, Shift.d_mk, d_one, smul_zero, Shift.mk_zero, map_zero]

variable (p)

/-- The attaching map `LowCells p → S`, sending the generator of a cell to its cocycle. -/
noncomputable def attach : LowCells p →ᵈᵍ[A] S :=
  DGModuleHom.toModule fun c =>
    DGModuleHom.shiftGen (-c.1.deg) c.1.z (by rw [neg_neg]; exact c.1.z_mem) c.1.d_z

/-- The null-homotopy of `p ∘ attach p` sending the generator of a cell to its element of
`M`. -/
noncomputable def homotopy : Cochain A (LowCells p) M (-1) :=
  (Cochain.directSumDesc fun c : LowCell p =>
    Cochain.shiftGen (-c.1.deg) (Shift.mk (-1) c.1.m) (mk_m_mem p c.1)).rightUnshift (-1)
      (zero_add _)

variable {p}

omit [DGModule A M] in
@[simp]
theorem attach_gen (c : LowCell p) : attach p c.gen = c.1.z := by
  rw [LowCell.gen, attach, DGModuleHom.toModule_lof, DGModuleHom.shiftGen_mk_one]

omit [DGModule A S] in
@[simp]
theorem homotopy_gen (c : LowCell p) : homotopy p c.gen = c.1.m := by
  rw [homotopy, Cochain.rightUnshift_apply, LowCell.gen, Cochain.directSumDesc_of,
    Cochain.shiftGen_mk_one, Shift.unmk_mk]

variable (p)

theorem δ_homotopy : δ (-1) 0 (homotopy p) = Cochain.ofHom (p.comp (attach p)) :=
  Cochain.ext_directSum_shift fun c => by
    change δ (-1) 0 (homotopy p) c.gen = Cochain.ofHom (p.comp (attach p)) c.gen
    rw [δ_neg_one_apply, LowCell.d_gen, map_zero, add_zero, homotopy_gen, Cochain.ofHom_apply,
      DGModuleHom.comp_apply, attach_gen, c.1.p_z]

omit [DGRing A] [DGModule A M] [DGModule A S] in
/-- `LowCells p` is concentrated in degrees `≤ 1` when `A` is concentrated in non-positive
degrees. -/
theorem eq_zero_of_mem_grading (hA : IsNonposGraded A) {n : ℤ} (hn : 1 < n) {x : LowCells p}
    (hx : x ∈ grading n) : x = 0 := by
  ext c
  have hc : x c ∈ grading n := hx c
  rw [DirectSum.zero_apply]
  exact (Shift.unmk _).injective (by
    rw [hA.eq_zero (by have := c.2; omega) (Shift.unmk_mem_grading hc)]; rfl)

end Cells

/-! ### The stages -/

section Stages

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

variable {A M} in
/-- The next stage: the cone of the attaching map of all cells of degree at most `1`. -/
noncomputable def lowStep (s : Stage A M) : Stage A M where
  obj := DGModuleCat.of A (Cone (attach s.π))
  π := Cone.desc (attach s.π) (homotopy s.π) s.π (δ_homotopy s.π)

variable {A M} in
/-- Attaching a cell of degree `j ≤ 1`. -/
theorem lowStep_exists (s : Stage A M) {j : ℤ} (hj : j ≤ 1) {z : s.obj} (hz : z ∈ grading j)
    (hdz : d z = 0) {m : M} (hm : m ∈ grading (j - 1)) (hpz : s.π z = d m) :
    ∃ e : (lowStep s).obj, e ∈ grading (j - 1) ∧ d e = Cone.inr (attach s.π) z ∧
      (lowStep s).π e = m := by
  let c : LowCell s.π := ⟨⟨j, z, m, hz, hdz, hm, hpz⟩, hj⟩
  refine ⟨Cone.inl (attach s.π) c.gen, ?_, ?_, ?_⟩
  · have h := (Cone.inl (attach s.π)).map_mem c.gen_mem
    rwa [← sub_eq_add_neg] at h
  · have h := Cone.inl_d_apply (f := attach s.π) c.gen
    rw [c.d_gen, map_zero, sub_zero, attach_gen] at h
    exact h
  · exact (Cone.inl_desc_apply _ _ _ (δ_homotopy s.π) _).trans (homotopy_gen c)

/-- The stages of the construction: `0`, then iterated attachment of the cells of degree at
most `1`. -/
noncomputable def stage : ℕ → Stage A M
  | 0 => ⟨DGModuleCat.of A PUnit, 0⟩
  | n + 1 => lowStep (stage n)

/-- The underlying dg module of the `n`-th stage. -/
abbrev Obj (n : ℕ) : Type (max u v) := (stage A M n).obj

/-- The inclusion of the `n`-th stage into the next one. -/
noncomputable def ι (n : ℕ) : Obj A M n →ᵈᵍ[A] Obj A M (n + 1) :=
  Cone.inr (attach (stage A M n).π)

theorem ι_injective (n : ℕ) : Function.Injective (ι A M n) := fun _ _ h =>
  congrArg (Cone.sndLinear (attach (stage A M n).π)) h

/-- The underlying dg module of the resolution: the colimit of the stages. -/
abbrev Colim : Type (max u v) := SeqColimit (Obj A M) (ι A M)

theorem stage_succ_π_comp_ι (n : ℕ) :
    (stage A M (n + 1)).π.comp (ι A M n) = (stage A M n).π :=
  Cone.inr_desc _ _ _ (δ_homotopy _)

/-- The augmentation of the resolution. -/
noncomputable def π : Colim A M →ᵈᵍ[A] M :=
  SeqColimit.desc (fun n => (stage A M n).π) (stage_succ_π_comp_ι A M)

variable {A M}

theorem π_of (n : ℕ) (x : Obj A M n) : π A M (SeqColimit.of _ _ n x) = (stage A M n).π x :=
  SeqColimit.desc_of _ _ _ _

theorem exists_step (n : ℕ) {j : ℤ} (hj : j ≤ 1) {z : Obj A M n} (hz : z ∈ grading j)
    (hdz : d z = 0) {m : M} (hm : m ∈ grading (j - 1)) (hpz : (stage A M n).π z = d m) :
    ∃ e : Obj A M (n + 1), e ∈ grading (j - 1) ∧ d e = ι A M n z ∧
      (stage A M (n + 1)).π e = m :=
  lowStep_exists (stage A M n) hj hz hdz hm hpz

/-- Every cocycle of `M` of degree `≤ 0` is the image of a cocycle of the first stage. -/
theorem exists_stage_one {j : ℤ} (hj : j ≤ 0) {m : M} (hm : m ∈ grading j) (hdm : d m = 0) :
    ∃ e : Obj A M 1, e ∈ grading j ∧ d e = 0 ∧ (stage A M 1).π e = m := by
  obtain ⟨e, he, hde, hpe⟩ := exists_step (A := A) 0 (j := j + 1) (by omega) (z := 0)
    (zero_mem _) d_zero (m := m) (by rwa [add_sub_cancel_right]) (by rw [map_zero, hdm])
  rw [add_sub_cancel_right] at he
  rw [map_zero] at hde
  exact ⟨e, he, hde, hpe⟩

variable (A M)

/-- Every stage is concentrated in non-positive degrees when `A` is. -/
theorem isNonposGraded_obj (hA : IsNonposGraded A) (n : ℕ) : IsNonposGraded (Obj A M n) := by
  induction n with
  | zero => exact isNonposGraded_iff.mpr fun _ _ _ _ => rfl
  | succ n ih =>
    refine isNonposGraded_iff.mpr fun k hk x hx => ?_
    obtain ⟨hx₁, hx₂⟩ := Cone.mem_grading_iff.mp hx
    refine Cone.ext ?_ (ih.eq_zero hk hx₂)
    exact (Shift.unmk 1).injective
      (eq_zero_of_mem_grading (p := (stage A M n).π) hA (n := k + 1) (by omega)
        (Shift.unmk_mem_grading hx₁))

/-- The resolution is concentrated in non-positive degrees when `A` is. -/
theorem isNonposGraded_colim (hA : IsNonposGraded A) : IsNonposGraded (Colim A M) :=
  isNonposGraded_iff.mpr fun k hk x hx => by
    obtain ⟨n, y, rfl⟩ := SeqColimit.exists_of_eq x
    have hinj := SeqColimit.of_injective (ι_injective A M) n
    rw [(isNonposGraded_obj A M hA n).eq_zero hk
      ((SeqColimit.of _ _ n).mem_grading_of_injective hinj hx), map_zero]

/-- The augmentation of the resolution is a quasi-isomorphism when `A` and `M` are concentrated
in non-positive degrees. -/
theorem isQuasiIso_π (hA : IsNonposGraded A) (hM : IsNonposGraded M) : (π A M).IsQuasiIso :=
  fun j => by
  constructor
  · rw [cohomology.map_injective_iff]
    intro x hx hdx hpx
    obtain ⟨n, y, rfl⟩ := SeqColimit.exists_of_eq x
    have hinj := SeqColimit.of_injective (ι_injective A M) n
    have hy : y ∈ grading j := (SeqColimit.of _ _ n).mem_grading_of_injective hinj hx
    have hdy : d y = 0 := hinj (by rw [DGModuleHom.map_d, hdx, map_zero])
    by_cases hj : 0 < j
    · rw [(isNonposGraded_obj A M hA n).eq_zero hj hy, map_zero]
      exact zero_mem _
    obtain ⟨m, hm, hdm⟩ := mem_coboundaries.mp hpx
    rw [π_of] at hdm
    obtain ⟨e, he, hde, -⟩ := exists_step n (by omega) hy hdy hm hdm.symm
    exact mem_coboundaries.mpr ⟨SeqColimit.of _ _ (n + 1) e,
      (SeqColimit.of _ _ (n + 1)).map_mem he, by
        rw [← DGModuleHom.map_d, hde, SeqColimit.of_succ_ι]⟩
  · rw [cohomology.map_surjective_iff]
    intro m hm hdm
    by_cases hj : 0 < j
    · refine ⟨0, zero_mem _, d_zero, ?_⟩
      rw [map_zero, hM.eq_zero hj hm, sub_zero]
      exact zero_mem _
    obtain ⟨e, he, hde, hpe⟩ := exists_stage_one (A := A) (by omega) hm hdm
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
      ⨁ c : LowCell (stage A M n).π, Shift (1 + -c.1.deg) A :=
  (DGModuleHom.shiftDirectSum 1 fun c : LowCell (stage A M n).π => -c.1.deg).comp
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
    have h' : toObj A M (n + 1) x = ι A M n y :=
      toObj_eq (by rw [SeqColimit.of_succ_ι]; exact hy)
    exact (congrArg (Cone.fstHom (attach (stage A M n).π)) h').trans (Cone.fstHom_inr y)

/-- The resolution is semi-free, filtered by the images of the stages. -/
noncomputable def semiFreeFiltration : SemiFreeFiltration.{max u v} A (Colim A M) where
  F := SeqColimit.filtration
  mono := SeqColimit.filtration_mono
  eq_zero_of_mem_zero x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact map_zero (SeqColimit.of (Obj A M) (ι A M) 0)
  exists_mem := SeqColimit.exists_mem_filtration
  ι n := LowCell (stage A M n).π
  decEq _ := inferInstance
  deg _ c := 1 + -c.1.deg
  π := filtrationπ A M
  surjective_π := surjective_filtrationπ A M
  π_eq_zero_iff := filtrationπ_eq_zero_iff A M

end Stages

end ConnectiveResolution

section Existence

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- Over a dg ring concentrated in non-positive degrees, every dg module concentrated in
non-positive degrees has a semi-free resolution concentrated in non-positive degrees. -/
theorem exists_semiFreeResolution_of_isNonposGraded (hA : IsNonposGraded A)
    (hM : IsNonposGraded M) :
    ∃ (P : Type (max u v)) (_ : AddCommGroup P) (_ : DGAddCommGroup P) (_ : Module A P)
      (_ : DGModule A P) (π : P →ᵈᵍ[A] M), π.IsQuasiIso ∧
        Nonempty (SemiFreeFiltration.{max u v} A P) ∧ IsNonposGraded P :=
  ⟨ConnectiveResolution.Colim A M, inferInstance, inferInstance, inferInstance, inferInstance,
    ConnectiveResolution.π A M, ConnectiveResolution.isQuasiIso_π A M hA hM,
    ⟨ConnectiveResolution.semiFreeFiltration A M⟩,
    ConnectiveResolution.isNonposGraded_colim A M hA⟩

end Existence

end DG
