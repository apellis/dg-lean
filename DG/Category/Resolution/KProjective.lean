import DG.Category.Coproducts
import DG.Category.Homotopy.Acyclic
import DG.Category.Homotopy.ConeCochain
import DG.Category.Resolution.Generator
import DG.Category.Tensor.YonedaHom

/-!
# K-projective dg modules over a dg category

Let `C` be a dg category. This file defines K-projective (homotopically projective) dg modules
over `C`, proves their basic closure properties, shows that the representable modules `C(X, -)`
(and more generally the modules with a corner generator, such as `e · C(X, -)`) are
K-projective, and that `HOM_C(P, -)` preserves quasi-isomorphisms when `P` is K-projective. It
is a port of `DG.Homotopy.KProjective` (the case of a dg ring, i.e. of a one-object dg
category): the free module `A` of rank one is replaced by the representable modules.

## Main definitions

* `DG.CatModule.IsKProjective P`: every morphism from `P` to an acyclic dg module (in the same
  universe) is null-homotopic.
* `DG.CatModule.GradedSplitting i p`: a splitting of a sequence `F → G → Q` of dg modules by
  families of additive maps of degree `0` commuting with the action of `C` (not necessarily
  with the differentials).
* `DG.CatModule.Cochain.directSumDesc`: cochains out of a direct sum.
* `DG.CatModule.HOM.postcomp P s`: postcomposition with `s : N ⟶ N'` on Hom complexes;
  `DG.CatModule.postcompHomotopy P s`: postcomposition on morphisms up to homotopy.

## Main results

* `DG.CatModule.isKProjective_iff_subsingleton_cohomology_hom` (`H⁰(HOM_C(P, N)) = 0` for all
  acyclic `N`) and `DG.CatModule.isKProjective_iff_isAcyclic_hom` (`HOM_C(P, N)` is acyclic for
  all acyclic `N`).
* `DG.CatModule.isKProjective_representable`: `C(X, -)` is K-projective, since
  `HOM_C(C(X, -), N) ≅ N X` (`DG.CatModule.yonedaHOM`) is acyclic for acyclic
  `N`; `DG.CatModule.IsCornerGenerator.isKProjective`, `DG.CatModule.isKProjective_corner`.
* Closure properties: `DG.CatModule.IsKProjective.shift`, `DG.CatModule.IsKProjective.of_retract`
  (homotopy retracts, in particular direct summands), `DG.CatModule.IsKProjective.of_iso`,
  `DG.CatModule.IsKProjective.of_dgHomotopyEquiv`, `DG.CatModule.IsKProjective.directSum`
  (arbitrary direct sums), `DG.CatModule.IsKProjective.of_gradedSplitting` (extensions split as
  graded modules), `DG.CatModule.IsKProjective.cone`, `DG.CatModule.IsContractible.isKProjective`.
* `DG.CatModule.GradedSplitting.exists_extension`: null-homotopies extend along a graded-split
  monomorphism whose cokernel admits no non-null-homotopic maps to the target (the inductive
  step for semi-free modules).
* `DG.CatModule.isQuasiIso_iff_isAcyclic_cone`: a morphism is a quasi-isomorphism iff its
  mapping cone is acyclic.
* `DG.CatModule.IsKProjective.bijective_cohomology_postcomp`: for K-projective `P`,
  `HOM_C(P, -)` preserves quasi-isomorphisms; `DG.CatModule.IsKProjective.postcompHomotopyEquiv`:
  for a quasi-isomorphism `N ⟶ N'`, `Hom_{H(C)}(P, N) ≃ Hom_{H(C)}(P, N')`.

## References

* [B. Keller, *Deriving DG categories*, Ann. Sci. ÉNS 27 (1994), §3]
* [The Stacks project, Tag 09KK and following]

## Universes

Morphisms of dg modules over `C` are only defined between modules with values in the same
universe, so `IsKProjective P` quantifies over acyclic modules in the universe of `P`.
-/

open CategoryTheory DirectSum

universe w w' v u

namespace DG

/-- A dg abelian group isomorphic to an acyclic one is acyclic. -/
theorem IsAcyclic.of_dgAddEquiv {M N : Type*} [AddCommGroup M] [DGAddCommGroup M]
    [AddCommGroup N] [DGAddCommGroup N] (e : DGAddEquiv M N) (h : IsAcyclic N) : IsAcyclic M := by
  refine DG.isAcyclic_iff.mpr fun n m hm hdm => ?_
  obtain ⟨y, hy, hdy⟩ := h.exists_d_eq (e.map_mem hm) (by rw [← e.map_d, hdm, map_zero])
  exact ⟨e.symm y, e.symm.map_mem hy, e.injective (by rw [e.map_d, e.apply_symm_apply, hdy])⟩

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### Acyclic modules and Hom complexes -/

section Acyclic

variable {M N P : CatModule.{w} C}

theorem IsAcyclic.exists_d_eq (h : IsAcyclic M) {X : C} {n : ℤ} {m : M.obj X}
    (hm : m ∈ grading n) (hdm : d m = 0) : ∃ m' ∈ grading (n - 1), d m' = m :=
  DG.IsAcyclic.exists_d_eq (h X) hm hdm

/-- Shifts of acyclic dg modules are acyclic. -/
theorem IsAcyclic.shift [DGCategory C] (h : IsAcyclic M) (k : ℤ) :
    IsAcyclic (CatModule.shift k M) :=
  fun X => DG.IsAcyclic.shift (h X) k

/-- The Hom complex `HOM_C(M, N)` is acyclic iff every cocycle of the Hom complex is a
coboundary. -/
theorem isAcyclic_hom_iff : DG.IsAcyclic (HOM M N) ↔
    ∀ (n m : ℤ), m + 1 = n → ∀ z : Cochain M N n, δ n (n + 1) z = 0 →
      ∃ y : Cochain M N m, δ m n y = z := by
  constructor
  · intro h n m hmn z hz
    have hsub := (HOM.cohomologyAddEquiv M N n).toEquiv.subsingleton_congr.mp (h n)
    have h0 : (QuotientAddGroup.mk (Cocycle.mk z (n + 1) rfl hz) :
        Cocycle M N n ⧸ Cocycle.coboundaries M N n) = 0 := Subsingleton.elim _ _
    rw [QuotientAddGroup.eq_zero_iff, Cocycle.mem_coboundaries_iff m hmn] at h0
    exact h0
  · intro h n
    refine (HOM.cohomologyAddEquiv M N n).toEquiv.subsingleton_congr.mpr ?_
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      rw [QuotientAddGroup.eq_zero_iff, Cocycle.mem_coboundaries_iff (n - 1) (sub_add_cancel n 1)]
      exact h n (n - 1) (sub_add_cancel n 1) z (Cocycle.δ_eq_zero z _)

/-- In an acyclic Hom complex, every cocycle is a coboundary. -/
theorem exists_δ_eq_of_isAcyclic (h : DG.IsAcyclic (HOM M N)) {n m : ℤ} (hmn : m + 1 = n)
    (z : Cochain M N n) (hz : δ n (n + 1) z = 0) : ∃ y : Cochain M N m, δ m n y = z :=
  isAcyclic_hom_iff.mp h n m hmn z hz

/-- A morphism is null-homotopic iff it is the differential of a `(-1)`-cochain. -/
theorem homotopic_zero_iff_exists {f : M ⟶ N} :
    Homotopic f 0 ↔ ∃ h : Cochain M N (-1), Cochain.ofHom f = δ (-1) 0 h :=
  mem_nullHomotopic_iff_exists

/-- A contractible dg module is acyclic. -/
theorem IsContractible.isAcyclic (hM : IsContractible M) : IsAcyclic M :=
  fun X n => hM.subsingleton_cohomology X n

end Acyclic

/-! ### K-projective dg modules -/

section KProjective

variable (P : CatModule.{w} C)

/-- A dg module `P` over `C` is K-projective (homotopically projective) if every morphism from
`P` to an acyclic dg module is null-homotopic, i.e. `Hom_{H(C)}(P, N) = 0` for every acyclic
`N`. -/
def IsKProjective : Prop :=
  ∀ N : CatModule.{w} C, IsAcyclic N → ∀ f : P ⟶ N, Homotopic f 0

variable {P}

theorem IsKProjective.homotopic_zero (hP : IsKProjective P) {N : CatModule.{w} C}
    (hN : IsAcyclic N) (f : P ⟶ N) : Homotopic f 0 :=
  hP N hN f

theorem subsingleton_quotient_nullHomotopic_iff {N : CatModule.{w} C} :
    Subsingleton ((P ⟶ N) ⧸ nullHomotopic P N) ↔ ∀ f : P ⟶ N, Homotopic f 0 := by
  constructor
  · intro h f
    have h0 : (QuotientAddGroup.mk f : (P ⟶ N) ⧸ nullHomotopic P N) = 0 := Subsingleton.elim _ _
    exact (QuotientAddGroup.eq_zero_iff f).mp h0
  · intro h
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using QuotientAddGroup.induction_on with
    | H f => exact (QuotientAddGroup.eq_zero_iff f).mpr (h f)

/-- `P` is K-projective iff `H⁰(HOM_C(P, N)) = 0` for every acyclic `N`. -/
theorem isKProjective_iff_subsingleton_cohomology_hom :
    IsKProjective P ↔ ∀ N : CatModule.{w} C, IsAcyclic N →
      Subsingleton (cohomology (HOM P N) 0) := by
  refine forall_congr' fun N => forall_congr' fun _ => ?_
  rw [← (quotientNullHomotopicAddEquivCohomology P N).toEquiv.subsingleton_congr,
    subsingleton_quotient_nullHomotopic_iff]

variable [DGCategory C]

/-- For a K-projective `P` and an acyclic `N`, the whole Hom complex `HOM_C(P, N)` is acyclic: a
cocycle `z` of degree `n` is a morphism `P ⟶ N⟦n⟧` (`Cochain.rightShift`), and `N⟦n⟧` is
acyclic. -/
theorem IsKProjective.isAcyclic_hom (hP : IsKProjective P) {N : CatModule.{w} C}
    (hN : IsAcyclic N) : DG.IsAcyclic (HOM P N) := by
  refine isAcyclic_hom_iff.mpr fun n m hmn z hz => ?_
  have hz' : δ 0 1 (z.rightShift n 0 (zero_add n)) = 0 := by
    rw [Cochain.δ_rightShift z n 0 1 (zero_add n) (n + 1) (add_comm 1 n), hz,
      Cochain.rightShift_zero, _root_.smul_zero]
  obtain ⟨h, hh⟩ := homotopic_zero_iff_exists.mp
    (hP (shift n N) (hN.shift n) (Cocycle.homOf (Cocycle.mk _ 1 (zero_add 1) hz')))
  refine ⟨koszulSign n • h.rightUnshift m (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift h m (by omega) n 0 (zero_add n), smul_smul,
    Int.units_mul_self, one_smul, ← hh, Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe,
    Cochain.rightUnshift_rightShift]

/-- `P` is K-projective iff `HOM_C(P, N)` is acyclic for every acyclic `N`. -/
theorem isKProjective_iff_isAcyclic_hom :
    IsKProjective P ↔ ∀ N : CatModule.{w} C, IsAcyclic N → DG.IsAcyclic (HOM P N) := by
  refine ⟨fun hP N hN => hP.isAcyclic_hom hN, fun h N hN f => ?_⟩
  obtain ⟨y, hy⟩ := exists_δ_eq_of_isAcyclic (h N hN) (neg_add_cancel 1) (Cochain.ofHom f)
    (δ_ofHom _)
  exact homotopic_zero_iff_exists.mpr ⟨y, hy.symm⟩

end KProjective

/-! ### Representable modules -/

section Representable

variable [DGCategory C]

/-- A dg module with a corner generator (`R ≅ (e · C(X, -))⟦-k⟧`) is K-projective: a morphism
`φ : R ⟶ N` is determined by the cocycle `φ g ∈ (N X)ᵏ`, which is a coboundary `d y` if `N` is
acyclic, and then `ofElement (e • y)` is a null-homotopy of `φ`. -/
theorem IsCornerGenerator.isKProjective {R : CatModule.{w} C} {X : C}
    {e : DGCategory.Idempotent X} {k : ℤ} {g : R.obj X} (hg : IsCornerGenerator R e k g) :
    IsKProjective R := by
  intro N hN φ
  have hφg : φ.app X g ∈ grading k := φ.map_mem hg.mem_grading
  have hdφg : d (φ.app X g) = 0 := by rw [← φ.map_d, hg.d_eq_zero, map_zero]
  obtain ⟨y, hy, hdy⟩ := hN.exists_d_eq hφg hdφg
  have hy' : e.val • y ∈ grading (k + -1) := by
    simpa [← sub_eq_add_neg] using smul_mem_grading e.mem_grading hy
  have hdey : d (e.val • y) = φ.app X g := by
    rw [d_smul_of_mem_zero e.mem_grading, e.d_val, zero_smul, zero_add, hdy, ← φ.map_smul,
      hg.val_smul]
  refine homotopic_zero_iff_exists.mpr ⟨hg.ofElement (e.val • y) hy', ?_⟩
  rw [hg.δ_ofElement (neg_add_cancel 1) _ hy' (by rw [hdey, add_zero]; exact hφg)]
  refine hg.ext_gen ?_
  rw [Cochain.ofHom_apply, hg.ofElement_gen, hdey, ← φ.map_smul, hg.val_smul]

/-- The representable module `C(X, -)` is K-projective: `HOM_C(C(X, -), N) ≅ N X`
(`DG.CatModule.yonedaHOM`) is acyclic when `N` is. -/
theorem isKProjective_representable (X : C) : IsKProjective (representable X) :=
  isKProjective_iff_isAcyclic_hom.mpr fun N hN =>
    (hN X).of_dgAddEquiv (yonedaHOM X N)

/-- The direct summand `e · C(X, -)` of a representable module is K-projective. -/
theorem isKProjective_corner {X : C} (e : DGCategory.Idempotent X) : IsKProjective (corner e) :=
  (isCornerGenerator_corner e).isKProjective

end Representable

/-! ### Closure properties -/

section Closure

variable {P Q : CatModule.{w} C}

/-- A homotopy retract of a K-projective dg module is K-projective: if `i ≫ r ≃ 𝟙` for
`i : Q ⟶ P` and `r : P ⟶ Q` and `P` is K-projective, so is `Q`. In particular direct summands
of K-projective modules are K-projective. -/
theorem IsKProjective.of_retract (hP : IsKProjective P) (i : Q ⟶ P) (r : P ⟶ Q)
    (hri : Homotopic (i ≫ r) (𝟙 Q)) : IsKProjective Q := by
  intro N hN f
  have h1 : Homotopic (i ≫ r ≫ f) 0 :=
    ((hP N hN (r ≫ f)).comp_left i).trans (Homotopic.of_eq Limits.comp_zero)
  exact ((Homotopic.of_eq (Category.id_comp f)).symm.trans
    ((hri.comp_right f).symm.trans (Homotopic.of_eq (Category.assoc _ _ _)))).trans h1

/-- K-projectivity is invariant under homotopy equivalence. -/
theorem IsKProjective.of_dgHomotopyEquiv (hP : IsKProjective P) (e : DGHomotopyEquiv Q P) :
    IsKProjective Q :=
  hP.of_retract e.hom e.inv e.homotopyHomInvId.homotopic

/-- K-projectivity is invariant under isomorphism. -/
theorem IsKProjective.of_iso (hP : IsKProjective P) (e : Q ≅ P) : IsKProjective Q :=
  hP.of_retract e.hom e.inv (Homotopic.of_eq e.hom_inv_id)

/-- A contractible dg module is K-projective. -/
theorem IsContractible.isKProjective (hP : IsContractible P) : IsKProjective P :=
  fun _ _ f => hP.homotopic_zero_of_left f

/-- Shifts of K-projective dg modules are K-projective: a morphism `P⟦k⟧ ⟶ N` is a cocycle of
degree `-k` of `HOM_C(P, N)` (`Cochain.leftUnshift`), which is a coboundary since
`HOM_C(P, N)` is acyclic. -/
theorem IsKProjective.shift [DGCategory C] (hP : IsKProjective P) (k : ℤ) :
    IsKProjective (CatModule.shift k P) := by
  intro N hN f
  have hz : δ (-k) (-k + 1) ((Cochain.ofHom f).leftUnshift (-k) (neg_add_cancel k)) = 0 := by
    rw [Cochain.δ_leftUnshift _ (-k) _ (-k + 1) 1 (by ring), δ_ofHom, Cochain.leftUnshift_zero,
      _root_.smul_zero]
  obtain ⟨y, hy⟩ := exists_δ_eq_of_isAcyclic (hP.isAcyclic_hom hN) (m := -k - 1) (by ring) _ hz
  refine homotopic_zero_iff_exists.mpr ⟨koszulSign k • y.leftShift k (-1) (by ring), ?_⟩
  rw [δ_units_smul, Cochain.δ_leftShift y k (-1) 0 (by ring) (-k) (neg_add_cancel k), hy,
    smul_smul, Int.units_mul_self, one_smul, Cochain.leftShift_leftUnshift]

end Closure

/-! ### Direct sums -/

section DirectSum

variable {J : Type w'} [DecidableEq J] {F : J → CatModule.{max w w'} C}
  {N : CatModule.{max w w'} C}

namespace Cochain

/-- The cochain out of a direct sum with prescribed restrictions `c j` to the summands. -/
def directSumDesc {n : ℤ} (c : ∀ j, Cochain (F j) N n) : Cochain (directSum F) N n where
  app X := DirectSum.toAddMonoid fun j => (c j).app X
  map_mem' {X i x} hx := by
    classical
    change DirectSum.toAddMonoid (fun j => (c j).app X) x ∈ _
    rw [← DirectSum.sum_support_of x, map_sum]
    refine sum_mem fun j _ => ?_
    rw [DirectSum.toAddMonoid_of]
    exact (c j).map_mem (hx j)
  map_smul' {X Y i f} hf x := by
    have h : (DirectSum.toAddMonoid fun j => (c j).app Y).comp
        (DirectSum.map fun j => (F j).act f) =
        ((koszulSign (n * i) : ℤ) • (N.act f).comp
          (DirectSum.toAddMonoid fun j => (c j).app X)) :=
      DirectSum.addHom_ext fun j y => by
        simp only [AddMonoidHom.comp_apply, DirectSum.map_of, DirectSum.toAddMonoid_of,
          AddMonoidHom.smul_apply]
        rw [← Units.smul_def]
        exact (c j).map_smul hf y
    rw [Units.smul_def]
    exact congrArg (fun χ : (⨁ j, (F j).obj X) →+ N.obj Y => χ x) h

@[simp]
theorem directSumDesc_app_ι {n : ℤ} (c : ∀ j, Cochain (F j) N n) (j : J) {X : C}
    (x : (F j).obj X) : (directSumDesc c).app X ((directSumι F j).app X x) = (c j).app X x :=
  show DirectSum.toAddMonoid (fun j => (c j).app X) (DirectSum.of (fun j => (F j).obj X) j x) = _
    from DirectSum.toAddMonoid_of _ _ _

@[simp]
theorem directSumDesc_comp_ofHom {n : ℤ} (c : ∀ j, Cochain (F j) N n) (j : J) :
    (directSumDesc c).comp (ofHom (directSumι F j)) (zero_add n) = c j :=
  Cochain.ext fun _ x => directSumDesc_app_ι c j x

/-- Two cochains out of a direct sum agreeing on the summands are equal. -/
theorem directSum_ext {n : ℤ} {c c' : Cochain (directSum F) N n}
    (h : ∀ j X (x : (F j).obj X), c.app X ((directSumι F j).app X x) =
      c'.app X ((directSumι F j).app X x)) : c = c' := by
  ext X x
  induction x using DirectSum.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | of j x => exact h j X x
  | add x y hx hy => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ _ _).symm)

end Cochain

/-- A direct sum of K-projective dg modules is K-projective. -/
theorem IsKProjective.directSum (h : ∀ j, IsKProjective (F j)) : IsKProjective (directSum F) := by
  intro N hN f
  choose c hc using fun j => homotopic_zero_iff_exists.mp (h j N hN (directSumι F j ≫ f))
  refine homotopic_zero_iff_exists.mpr ⟨Cochain.directSumDesc c,
    Cochain.directSum_ext fun j X x => ?_⟩
  have h1 := congrArg (fun z : Cochain (F j) N 0 => z.app X x)
    (δ_ofHom_comp (directSumι F j) (Cochain.directSumDesc c) 0)
  simp only [Cochain.comp_apply, Cochain.ofHom_apply, Cochain.directSumDesc_comp_ofHom] at h1
  rw [Cochain.ofHom_apply, ← h1, ← hc j]
  rfl

end DirectSum

/-! ### Extensions -/

section GradedSplitting

variable {F G Q : CatModule.{w} C}

/-- A graded splitting of a sequence `F → G → Q` of morphisms `i` and `p` of dg modules over `C`:
cochains of degree `0` (families of additive maps of degree `0` commuting with the action of
`C`, not necessarily with the differentials) `r : G → F` and `s : Q → G` with `r ∘ i = id`,
`p ∘ s = id` and `i ∘ r + s ∘ p = id`. Such data exist iff `0 → F → G → Q → 0` is a short
exact sequence of dg modules which splits as a sequence of graded modules over `C`. -/
structure GradedSplitting (i : F ⟶ G) (p : G ⟶ Q) where
  /-- The graded retraction of `i`. -/
  r : Cochain G F 0
  /-- The graded section of `p`. -/
  s : Cochain Q G 0
  r_i : ∀ {X : C} (x : F.obj X), r.app X (i.app X x) = x
  p_s : ∀ {X : C} (y : Q.obj X), p.app X (s.app X y) = y
  i_r_add_s_p : ∀ {X : C} (x : G.obj X), i.app X (r.app X x) + s.app X (p.app X x) = x

namespace GradedSplitting

variable {i : F ⟶ G} {p : G ⟶ Q} (σ : GradedSplitting i p)

include σ in
theorem p_i {X : C} (x : F.obj X) : p.app X (i.app X x) = 0 := by
  have h := σ.i_r_add_s_p (i.app X x)
  rw [σ.r_i, add_eq_left] at h
  rw [← σ.p_s (p.app X (i.app X x)), h, map_zero]

include σ in
/-- Null-homotopies extend along a graded-split monomorphism with K-projective cokernel: if
`f : G ⟶ N` restricts along `i` to a morphism null-homotopic via `h`, and every morphism
`Q ⟶ N` is null-homotopic, then `f` is null-homotopic via a homotopy extending `h`. -/
theorem exists_extension {N : CatModule.{w} C} (hQ : ∀ g : Q ⟶ N, Homotopic g 0) (f : G ⟶ N)
    (h : Cochain F N (-1)) (hh : Cochain.ofHom (i ≫ f) = δ (-1) 0 h) :
    ∃ h' : Cochain G N (-1), Cochain.ofHom f = δ (-1) 0 h' ∧
      ∀ {X : C} (x : F.obj X), h'.app X (i.app X x) = h.app X x := by
  set hr : Cochain G N (-1) := h.comp σ.r (zero_add _)
  set g : Cochain G N 0 := Cochain.ofHom f - δ (-1) 0 hr with hg
  have e1 : hr.comp (Cochain.ofHom i) (zero_add _) = h :=
    Cochain.ext fun X x => by simp [hr, σ.r_i]
  have hg_i : ∀ {X : C} (x : F.obj X), g.app X (i.app X x) = 0 := fun {X} x => by
    have h1 := congrArg (fun z : Cochain F N 0 => z.app X x) (δ_ofHom_comp i hr 0)
    have h2 := congrArg (fun z : Cochain F N 0 => z.app X x) hh
    simp only [Cochain.comp_apply, Cochain.ofHom_apply, e1, comp_app] at h1 h2
    simp only [hg, Cochain.sub_apply, Cochain.ofHom_apply, h1, h2, sub_self]
  have hg_d : ∀ {X : C} (x : G.obj X), d (g.app X x) = g.app X (d x) := fun {X} x => by
    have h1 : δ 0 1 g = 0 := by rw [hg, δ_sub, δ_ofHom, δ_δ, sub_zero]
    have h2 := congrArg (fun z : Cochain G N 1 => z.app X x) h1
    simpa [sub_eq_zero] using h2
  have hgs : δ 0 1 (g.comp σ.s (zero_add 0)) = 0 := by
    ext X y
    have hp : p.app X (d (σ.s.app X y) - σ.s.app X (d y)) = 0 := by
      rw [map_sub, Hom.map_d, σ.p_s, σ.p_s, sub_self]
    have hx := σ.i_r_add_s_p (d (σ.s.app X y) - σ.s.app X (d y))
    rw [hp, map_zero, add_zero] at hx
    rw [δ_zero_cochain_apply, Cochain.comp_apply, Cochain.comp_apply, hg_d, ← map_sub, ← hx,
      hg_i, Cochain.zero_apply]
  obtain ⟨k, hk⟩ := homotopic_zero_iff_exists.mp
    (hQ (Cocycle.homOf (Cocycle.mk _ 1 (zero_add 1) hgs)))
  rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe] at hk
  refine ⟨hr + k.comp (Cochain.ofHom p) (zero_add _), ?_, fun {X} x => ?_⟩
  · ext X x
    have h1 := congrArg (fun z : Cochain G N 0 => z.app X x) (δ_ofHom_comp p k 0)
    have h2 := congrArg (fun z : Cochain Q N 0 => z.app X (p.app X x)) hk
    simp only [Cochain.comp_apply, Cochain.ofHom_apply] at h1 h2
    have h3 : g.app X x = g.app X (σ.s.app X (p.app X x)) := by
      conv_lhs => rw [← σ.i_r_add_s_p x]
      rw [map_add, hg_i, zero_add]
    rw [δ_add, Cochain.add_apply, h1, ← h2, ← h3, hg, Cochain.sub_apply, add_sub_cancel]
  · simp [hr, σ.r_i, σ.p_i]

end GradedSplitting

/-- An extension of K-projective dg modules is K-projective: if `F → G → Q` is a graded-split
short exact sequence with `F` and `Q` K-projective, then `G` is K-projective. -/
theorem IsKProjective.of_gradedSplitting {i : F ⟶ G} {p : G ⟶ Q} (σ : GradedSplitting i p)
    (hF : IsKProjective F) (hQ : IsKProjective Q) : IsKProjective G := by
  intro N hN f
  obtain ⟨h, hh⟩ := homotopic_zero_iff_exists.mp (hF N hN (i ≫ f))
  obtain ⟨h', hh', -⟩ := σ.exists_extension (hQ N hN) f h hh
  exact homotopic_zero_iff_exists.mpr ⟨h', hh'⟩

end GradedSplitting

/-! ### Mapping cones -/

section Cone

variable [DGCategory C] {M N : CatModule.{w} C}

/-- The standard sequence `N → cone f → M⟦1⟧` of a mapping cone is graded-split. -/
def cone.gradedSplitting (f : M ⟶ N) : GradedSplitting (cone.inr f) (cone.fstHom f) where
  r := cone.snd f
  s := Cochain.ofHoms (cone.inlAddHom f) cone.inlAddHom_mem cone.inlAddHom_smul
  r_i _ := rfl
  p_s _ := rfl
  i_r_add_s_p x := by
    rw [add_comm]
    exact cone.inlAddHom_fstHom_add_inr_sndAddHom x

/-- The mapping cone of a morphism between K-projective dg modules is K-projective. -/
theorem IsKProjective.cone {f : M ⟶ N} (hM : IsKProjective M) (hN : IsKProjective N) :
    IsKProjective (cone f) :=
  IsKProjective.of_gradedSplitting (cone.gradedSplitting f) hN (hM.shift 1)

end Cone

/-! ### Quasi-isomorphisms and acyclic cones -/

section QuasiIso

variable {M N : CatModule.{w} C}

theorem cohomologyMap_injective_iff (s : M ⟶ N) (X : C) (n : ℤ) :
    Function.Injective (cohomologyMap s X n) ↔
      ∀ x ∈ grading n, d x = 0 → s.app X x ∈ coboundaries (N.obj X) n →
        x ∈ coboundaries (M.obj X) n :=
  cohomology.mapAddMonoidHom_injective_iff _ _ _ n

theorem cohomologyMap_surjective_iff (s : M ⟶ N) (X : C) (n : ℤ) :
    Function.Surjective (cohomologyMap s X n) ↔
      ∀ y ∈ grading n, d y = 0 →
        ∃ x ∈ grading n, d x = 0 ∧ s.app X x - y ∈ coboundaries (N.obj X) n :=
  cohomology.mapAddMonoidHom_surjective_iff _ _ _ n

/-- A morphism between acyclic dg modules is a quasi-isomorphism. -/
theorem isQuasiIso_of_isAcyclic (hM : IsAcyclic M) (hN : IsAcyclic N) (s : M ⟶ N) :
    IsQuasiIso s := fun X n =>
  ⟨fun _ _ _ => (hM X n).elim _ _, fun _ => ⟨0, (hN X n).elim _ _⟩⟩

variable [DGCategory C]

/-- A quasi-isomorphism has an acyclic mapping cone. -/
theorem IsQuasiIso.isAcyclic_cone {s : M ⟶ N} (hs : IsQuasiIso s) : IsAcyclic (cone s) := by
  intro X
  refine DG.isAcyclic_iff.mpr fun k p hp hdp => ?_
  have hx : (cone.fst s).1.app X p ∈ grading (k + 1) := (cone.fst s).1.map_mem hp
  have hy : (cone.snd s).app X p ∈ grading k := by simpa using (cone.snd s).map_mem hp
  have hdx : d ((cone.fst s).1.app X p) = 0 := by
    have h := congrArg ((cone.fst s).1.app X) hdp
    rwa [cone.d_fst_apply, map_zero, neg_eq_zero] at h
  have hsxy : s.app X ((cone.fst s).1.app X p) + d ((cone.snd s).app X p) = 0 := by
    have h := congrArg ((cone.snd s).app X) hdp
    rwa [cone.d_snd_apply, map_zero] at h
  obtain ⟨u, hu, hdu⟩ := (cohomologyMap_injective_iff s X (k + 1)).mp (hs X (k + 1)).1 _ hx hdx
    ⟨-(cone.snd s).app X p, by simpa using neg_mem hy,
      by rw [d_neg, neg_eq_iff_add_eq_zero, add_comm, hsxy]⟩
  have hu' : u ∈ grading k := by simpa using hu
  obtain ⟨w, hw, hdw, v, hv, hdv⟩ := (cohomologyMap_surjective_iff s X k).mp (hs X k).2
    ((cone.snd s).app X p + s.app X u) (add_mem hy (s.map_mem hu'))
    (by rw [d_add, ← s.map_d, hdu, add_comm, hsxy])
  refine ⟨(cone.inl s).app X (w - u) + (cone.inr s).app X (-v),
    add_mem ?_ ((cone.inr s).map_mem (neg_mem hv)), ?_⟩
  · simpa [sub_eq_add_neg] using (cone.inl s).map_mem (sub_mem hw hu')
  · refine cone.ext_to ?_ ?_
    · simp only [cone.d_fst_apply, map_add, cone.inl_fst_apply, cone.inr_fst_apply, add_zero,
        d_sub, hdw, hdu, zero_sub, neg_neg, d_zero, neg_zero]
    · simp only [cone.d_snd_apply, map_add, cone.inl_fst_apply, cone.inr_fst_apply,
        cone.inl_snd_apply, cone.inr_snd_apply, add_zero, zero_add, d_neg, hdv, map_sub,
        map_zero]
      abel

/-- A morphism with an acyclic mapping cone is a quasi-isomorphism. -/
theorem isQuasiIso_of_isAcyclic_cone {s : M ⟶ N} (h : IsAcyclic (cone s)) : IsQuasiIso s := by
  intro X n
  constructor
  · rw [cohomologyMap_injective_iff]
    rintro x hx hdx ⟨v, hv, hdv⟩
    have hp : (cone.inl s).app X x + (cone.inr s).app X (-v) ∈ grading (n - 1) :=
      add_mem (by simpa [sub_eq_add_neg] using (cone.inl s).map_mem hx)
        ((cone.inr s).map_mem (neg_mem hv))
    have hdp : d ((cone.inl s).app X x + (cone.inr s).app X (-v)) = 0 := by
      refine cone.ext_to ?_ ?_
      · simp only [cone.d_fst_apply, map_add, cone.inl_fst_apply, cone.inr_fst_apply, add_zero,
          hdx, neg_zero, map_zero]
      · simp only [cone.d_snd_apply, map_add, cone.inl_fst_apply, cone.inr_fst_apply,
          cone.inl_snd_apply, cone.inr_snd_apply, add_zero, zero_add, d_neg, hdv, add_neg_cancel,
          map_zero]
    obtain ⟨q, hq, hdq⟩ := h.exists_d_eq hp hdp
    refine ⟨-(cone.fst s).1.app X q, by simpa using neg_mem ((cone.fst s).1.map_mem hq), ?_⟩
    have h1 := congrArg ((cone.fst s).1.app X) hdq
    rw [cone.d_fst_apply, map_add, cone.inl_fst_apply, cone.inr_fst_apply, add_zero] at h1
    rw [d_neg, h1]
  · rw [cohomologyMap_surjective_iff]
    intro y hy hdy
    have hdp : d ((cone.inr s).app X y) = 0 := by rw [cone.inr_d_apply, hdy, map_zero]
    obtain ⟨q, hq, hdq⟩ := h.exists_d_eq ((cone.inr s).map_mem hy) hdp
    have h1 := congrArg ((cone.fst s).1.app X) hdq
    have h2 := congrArg ((cone.snd s).app X) hdq
    rw [cone.d_fst_apply, cone.inr_fst_apply, neg_eq_zero] at h1
    rw [cone.d_snd_apply, cone.inr_snd_apply] at h2
    refine ⟨(cone.fst s).1.app X q, by simpa using (cone.fst s).1.map_mem hq, h1,
      -(cone.snd s).app X q, by simpa using neg_mem ((cone.snd s).map_mem hq), ?_⟩
    rw [d_neg, ← h2]
    abel

/-- A morphism of dg modules over `C` is a quasi-isomorphism iff its mapping cone is
acyclic. -/
theorem isQuasiIso_iff_isAcyclic_cone (s : M ⟶ N) : IsQuasiIso s ↔ IsAcyclic (cone s) :=
  ⟨fun hs => (IsQuasiIso.isAcyclic_cone hs), isQuasiIso_of_isAcyclic_cone⟩

end QuasiIso

/-! ### `HOM_C(P, -)` for K-projective `P` -/

section HomQuasiIso

variable {P N N' : CatModule.{w} C}

namespace HOM

variable (P) in
/-- Postcomposition with a morphism `s : N ⟶ N'`, as a map of Hom complexes
`HOM_C(P, N) → HOM_C(P, N')`. -/
noncomputable def postcomp (s : N ⟶ N') : HOM P N →+ HOM P N' :=
  DirectSum.map fun n =>
    { toFun := fun z => (Cochain.ofHom s).comp z (add_zero n)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun z z' => Cochain.comp_add z z' _ _ }

theorem postcomp_of (s : N ⟶ N') (n : ℤ) (z : Cochain P N n) :
    postcomp P s (DirectSum.of _ n z) =
      DirectSum.of (fun n => Cochain P N' n) n ((Cochain.ofHom s).comp z (add_zero n)) :=
  DirectSum.map_of _ _ _

theorem postcomp_mem (s : N ⟶ N') {n : ℤ} {x : HOM P N} (hx : x ∈ grading n) :
    postcomp P s x ∈ grading n := by
  obtain ⟨z, rfl⟩ := mem_summand.mp hx
  rw [postcomp_of]
  exact of_mem_summand _ _

theorem postcomp_d (s : N ⟶ N') (x : HOM P N) : postcomp P s (d x) = d (postcomp P s x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n z => rw [d_of, postcomp_of, postcomp_of, d_of, δ_comp_ofHom]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

theorem of_mem_grading_iff {n : ℤ} {x : HOM P N} :
    x ∈ grading n ↔ ∃ z : Cochain P N n, DirectSum.of _ n z = x :=
  mem_summand

theorem d_of_eq_zero_iff {n : ℤ} (z : Cochain P N n) :
    d (DirectSum.of (fun n => Cochain P N n) n z : HOM P N) = 0 ↔ δ n (n + 1) z = 0 := by
  rw [d_of, ← map_zero (DirectSum.of (fun n => Cochain P N n) (n + 1))]
  exact (DirectSum.of_injective (β := fun n => Cochain P N n) (n + 1)).eq_iff

theorem of_mem_coboundaries_iff {n : ℤ} (z : Cochain P N n) (hz : δ n (n + 1) z = 0) :
    (DirectSum.of (fun n => Cochain P N n) n z : HOM P N) ∈ coboundaries (HOM P N) n ↔
      ∃ y : Cochain P N (n - 1), δ (n - 1) n y = z :=
  (cocyclesAddEquiv_mem_coboundaries_iff n (Cocycle.mk z (n + 1) rfl hz)).trans
    (Cocycle.mem_coboundaries_iff (n - 1) (sub_add_cancel n 1) _)

end HOM

variable (P) in
/-- Postcomposition with `s : N ⟶ N'`, as an additive map `(P ⟶ N) →+ (P ⟶ N')`. -/
@[simps]
def postcompAddHom (s : N ⟶ N') : (P ⟶ N) →+ (P ⟶ N') where
  toFun f := f ≫ s
  map_zero' := Limits.zero_comp
  map_add' f g := Preadditive.add_comp _ _ _ f g s

variable (P) in
/-- Postcomposition with `s : N ⟶ N'` on morphisms up to homotopy,
`Hom_{H(C)}(P, N) → Hom_{H(C)}(P, N')`. -/
def postcompHomotopy (s : N ⟶ N') :
    ((P ⟶ N) ⧸ nullHomotopic P N) →+ ((P ⟶ N') ⧸ nullHomotopic P N') :=
  QuotientAddGroup.map _ _ (postcompAddHom P s) fun _ hf => comp_mem_nullHomotopic hf s

@[simp]
theorem postcompHomotopy_mk (s : N ⟶ N') (f : P ⟶ N) :
    postcompHomotopy P s (QuotientAddGroup.mk f) = QuotientAddGroup.mk (f ≫ s) :=
  rfl

variable [DGCategory C]

/-- For a K-projective `P` and a quasi-isomorphism `s : N ⟶ N'`, every cocycle of
`HOM_C(P, N')` is cohomologous to `s ∘ α` for a cocycle `α` of `HOM_C(P, N)`. -/
theorem IsKProjective.exists_cocycle_of_isQuasiIso (hP : IsKProjective P) {s : N ⟶ N'}
    (hs : IsQuasiIso s) {n m : ℤ} (hmn : m + 1 = n) (z' : Cochain P N' n)
    (hz' : δ n (n + 1) z' = 0) :
    ∃ (α : Cochain P N n) (β : Cochain P N' m), δ n (n + 1) α = 0 ∧
      (Cochain.ofHom s).comp α (add_zero n) = z' - δ m n β := by
  have hC := hP.isAcyclic_hom (IsQuasiIso.isAcyclic_cone hs)
  have hw0 : δ n (n + 1) ((Cochain.ofHom (cone.inr s)).comp z' (add_zero n)) = 0 := by
    rw [δ_comp_ofHom, hz', Cochain.comp_zero]
  obtain ⟨w, hw⟩ := exists_δ_eq_of_isAcyclic hC hmn _ hw0
  have hw' : w = cone.liftCochain s ((cone.fst s).1.comp w hmn) ((cone.snd s).comp w
      (add_zero m)) hmn :=
    Cochain.ext fun X x => cone.ext_to (by simp) (by simp)
  rw [hw', cone.δ_liftCochain s _ _ hmn (n + 1) rfl] at hw
  refine ⟨(cone.fst s).1.comp w hmn, (cone.snd s).comp w (add_zero m), ?_, ?_⟩
  · ext X x
    have h := congrArg
      (fun c : Cochain P (CatModule.cone s) n => (cone.fst s).1.app X (c.app X x)) hw
    simpa using h
  · ext X x
    have h := congrArg (fun c : Cochain P (CatModule.cone s) n => (cone.snd s).app X (c.app X x)) hw
    simp only [Cochain.add_apply, Cochain.neg_apply, Cochain.comp_apply, Cochain.ofHom_apply,
      map_add, map_neg, cone.inl_snd_apply, cone.inr_snd_apply, neg_zero, zero_add] at h
    rw [Cochain.comp_apply, Cochain.ofHom_apply, Cochain.sub_apply, ← h]
    abel

/-- For a K-projective `P` and a quasi-isomorphism `s : N ⟶ N'`, a cocycle `z` of
`HOM_C(P, N)` such that `s ∘ z` is a coboundary is itself a coboundary. -/
theorem IsKProjective.exists_δ_eq_of_isQuasiIso (hP : IsKProjective P) {s : N ⟶ N'}
    (hs : IsQuasiIso s) {n m : ℤ} (hmn : m + 1 = n) (z : Cochain P N n)
    (hz : δ n (n + 1) z = 0) (y' : Cochain P N' m)
    (hy' : (Cochain.ofHom s).comp z (add_zero n) = δ m n y') :
    ∃ y : Cochain P N m, δ m n y = z := by
  subst hmn
  have hC := hP.isAcyclic_hom (IsQuasiIso.isAcyclic_cone hs)
  have hw : δ m (m + 1) (cone.liftCochain s z (-y') rfl) = 0 := by
    rw [cone.δ_liftCochain s _ _ rfl (m + 1 + 1) rfl, hz, δ_neg, hy', neg_add_cancel,
      Cochain.comp_zero, Cochain.comp_zero, neg_zero, add_zero]
  obtain ⟨u, hu⟩ := exists_δ_eq_of_isAcyclic hC (sub_add_cancel m 1) _ hw
  have hu' : u = cone.liftCochain s ((cone.fst s).1.comp u (sub_add_cancel m 1))
      ((cone.snd s).comp u (add_zero _)) (sub_add_cancel m 1) :=
    Cochain.ext fun X x => cone.ext_to (by simp) (by simp)
  rw [hu', cone.δ_liftCochain s _ _ (sub_add_cancel m 1) (m + 1) rfl] at hu
  refine ⟨-(cone.fst s).1.comp u (sub_add_cancel m 1), ?_⟩
  ext X x
  have h := congrArg (fun c : Cochain P (CatModule.cone s) m => (cone.fst s).1.app X (c.app X x)) hu
  simp only [Cochain.add_apply, Cochain.neg_apply, Cochain.comp_apply, Cochain.ofHom_apply,
    map_add, map_neg, cone.inl_fst_apply, cone.inr_fst_apply, add_zero,
    cone.liftCochain_fst_apply] at h
  rw [δ_neg, Cochain.neg_apply, h]

/-- For a K-projective `P`, `HOM_C(P, -)` preserves quasi-isomorphisms: if `s : N ⟶ N'` is a
quasi-isomorphism, then postcomposition with `s` induces isomorphisms
`Hⁿ(HOM_C(P, N)) ≅ Hⁿ(HOM_C(P, N'))` for all `n`. -/
theorem IsKProjective.bijective_cohomology_postcomp (hP : IsKProjective P) {s : N ⟶ N'}
    (hs : IsQuasiIso s) (n : ℤ) :
    Function.Bijective (cohomology.mapAddMonoidHom (HOM.postcomp P s)
      (HOM.postcomp_mem s) (HOM.postcomp_d s) n) := by
  constructor
  · rw [cohomology.mapAddMonoidHom_injective_iff]
    intro x hx hdx hsx
    obtain ⟨z, rfl⟩ := HOM.of_mem_grading_iff.mp hx
    rw [HOM.d_of_eq_zero_iff] at hdx
    have hsz : δ n (n + 1) ((Cochain.ofHom s).comp z (add_zero n)) = 0 := by
      rw [δ_comp_ofHom, hdx, Cochain.comp_zero]
    rw [HOM.postcomp_of, HOM.of_mem_coboundaries_iff _ hsz] at hsx
    obtain ⟨y', hy'⟩ := hsx
    obtain ⟨y, hy⟩ := hP.exists_δ_eq_of_isQuasiIso hs (sub_add_cancel n 1) z hdx y' hy'.symm
    exact (HOM.of_mem_coboundaries_iff z hdx).mpr ⟨y, hy⟩
  · rw [cohomology.mapAddMonoidHom_surjective_iff]
    intro y hy hdy
    obtain ⟨z', rfl⟩ := HOM.of_mem_grading_iff.mp hy
    rw [HOM.d_of_eq_zero_iff] at hdy
    obtain ⟨α, β, hα, hαβ⟩ := hP.exists_cocycle_of_isQuasiIso hs (sub_add_cancel n 1) z' hdy
    refine ⟨DirectSum.of _ n α, of_mem_summand _ _, (HOM.d_of_eq_zero_iff α).mpr hα, ?_⟩
    rw [HOM.postcomp_of, hαβ, ← map_sub, sub_sub_cancel_left,
      HOM.of_mem_coboundaries_iff _ (by rw [δ_neg, δ_δ, neg_zero])]
    exact ⟨-β, δ_neg _ _ β⟩

/-- For a K-projective `P` and a quasi-isomorphism `s : N ⟶ N'`, postcomposition with `s` is a
bijection `Hom_{H(C)}(P, N) ≅ Hom_{H(C)}(P, N')` on morphisms up to homotopy. -/
theorem IsKProjective.bijective_postcompHomotopy (hP : IsKProjective P) {s : N ⟶ N'}
    (hs : IsQuasiIso s) : Function.Bijective (postcompHomotopy P s) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using QuotientAddGroup.induction_on with
    | H f =>
      rw [postcompHomotopy_mk, QuotientAddGroup.eq_zero_iff, mem_nullHomotopic_iff_exists] at hc
      obtain ⟨y', hy'⟩ := hc
      obtain ⟨y, hy⟩ := hP.exists_δ_eq_of_isQuasiIso hs (neg_add_cancel 1) (Cochain.ofHom f)
        (δ_ofHom _) y' hy'
      exact (QuotientAddGroup.eq_zero_iff f).mpr (mem_nullHomotopic_iff_exists.mpr ⟨y, hy.symm⟩)
  · intro c
    induction c using QuotientAddGroup.induction_on with
    | H f' =>
      obtain ⟨α, β, hα, hαβ⟩ := hP.exists_cocycle_of_isQuasiIso hs (neg_add_cancel 1)
        (Cochain.ofHom f') (δ_ofHom _)
      refine ⟨QuotientAddGroup.mk (Cocycle.homOf (Cocycle.mk α 1 (zero_add 1) hα)), ?_⟩
      rw [postcompHomotopy_mk, QuotientAddGroup.eq_iff_sub_mem, mem_nullHomotopic_iff_exists]
      refine ⟨-β, ?_⟩
      rw [Cochain.ofHom_sub, Cochain.ofHom_comp, Cocycle.cochain_ofHom_homOf_eq_coe,
        Cocycle.mk_coe, hαβ, δ_neg]
      abel

/-- For a K-projective `P` and a quasi-isomorphism `s : N ⟶ N'`,
`Hom_{H(C)}(P, N) ≃ Hom_{H(C)}(P, N')`, induced by postcomposition with `s`. -/
noncomputable def IsKProjective.postcompHomotopyEquiv (hP : IsKProjective P) {s : N ⟶ N'}
    (hs : IsQuasiIso s) :
    ((P ⟶ N) ⧸ nullHomotopic P N) ≃+ ((P ⟶ N') ⧸ nullHomotopic P N') :=
  AddEquiv.ofBijective _ (hP.bijective_postcompHomotopy hs)

@[simp]
theorem IsKProjective.postcompHomotopyEquiv_mk (hP : IsKProjective P) {s : N ⟶ N'}
    (hs : IsQuasiIso s) (f : P ⟶ N) :
    hP.postcompHomotopyEquiv hs (QuotientAddGroup.mk f) = QuotientAddGroup.mk (f ≫ s) :=
  rfl

end HomQuasiIso

end CatModule

end DG
