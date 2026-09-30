import DG.Category.Derived.HomotopyCoproducts
import DG.Category.SubQuotient

/-!
# Sequential colimits of dg modules over a dg category

Let `C` be a category with dg Hom groups and let `S 0 → S 1 → S 2 → ⋯` be a sequence of
morphisms `ι n : S n ⟶ S (n + 1)` of dg modules over `C`. Its colimit is the quotient of the
direct sum `⨁ n, S n` by the image of the morphism `x ↦ x - ι n x` (for `x ∈ S n`), computed
objectwise. This is a port of `DG.SeqColimit` (the case of a dg ring).

## Main definitions

* `DG.CatModule.seqColimit S ι`: the colimit of the sequence.
* `DG.CatModule.SeqColimit.of S ι n`: the canonical morphisms `S n ⟶ seqColimit S ι`.
* `DG.CatModule.SeqColimit.desc`: the morphism out of the colimit determined by a compatible
  family of morphisms `S n ⟶ N`; `DG.CatModule.SeqColimit.descCochain`: the same for cochains.
* `DG.CatSubmodule.liftQCochain`: a cochain vanishing on a dg submodule factors through the
  quotient.

## Main results

* `DG.CatModule.SeqColimit.of_comp_ι`: `ι n ≫ of (n + 1) = of n`.
* `DG.CatModule.SeqColimit.exists_of_eq`: every element of the colimit comes from some `S n`.
* `DG.CatModule.SeqColimit.of_injective`: if all `ι n` are objectwise injective, so are the
  `of n`.
-/

open CategoryTheory DirectSum

universe w v u

set_option backward.isDefEq.respectTransparency false

namespace DG

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

namespace CatSubmodule

variable {M N : CatModule.{w} C} (S : CatSubmodule M)

/-- A cochain vanishing on a dg submodule `S` factors through the quotient `M ⧸ S`. -/
noncomputable def liftQCochain {n : ℤ} (c : CatModule.Cochain M N n)
    (h : ∀ X, ∀ m ∈ S.carrier X, c.app X m = 0) : CatModule.Cochain S.quotient N n where
  app X := QuotientAddGroup.lift _ (c.app X) fun m hm => h X m hm
  map_mem' := by
    rintro X i _ ⟨m, hm, rfl⟩
    exact c.map_mem hm
  map_smul' {X Y i f} hf y := by
    induction y using QuotientAddGroup.induction_on with
    | H m => exact c.map_smul hf m

@[simp]
theorem liftQCochain_app_mkQ {n : ℤ} (c : CatModule.Cochain M N n)
    (h : ∀ X, ∀ m ∈ S.carrier X, c.app X m = 0) {X : C} (m : M.obj X) :
    (S.liftQCochain c h).app X (S.mkQ.app X m) = c.app X m :=
  rfl

end CatSubmodule

namespace CatModule

variable (S : ℕ → CatModule.{w} C) (ι : ∀ n, S n ⟶ S (n + 1))

namespace SeqColimit

/-- The morphism `⨁ n, S n ⟶ ⨁ n, S n` given on `S n` by `x ↦ x - ι n x`; the colimit of the
sequence is its cokernel. -/
noncomputable def relHom : directSum S ⟶ directSum S :=
  directSumDesc fun n => directSumι S n - ι n ≫ directSumι S (n + 1)

/-- The components of `relHom`, as additive maps of direct sums. -/
noncomputable def relHomApp (X : C) : (⨁ n, (S n).obj X) →+ ⨁ n, (S n).obj X :=
  (relHom S ι).app X

variable {S}

theorem relHom_of {X : C} (n : ℕ) (x : (S n).obj X) :
    relHomApp S ι X (DirectSum.of (fun n => (S n).obj X) n x) =
      DirectSum.of (fun n => (S n).obj X) n x -
        DirectSum.of (fun n => (S n).obj X) (n + 1) ((ι n).app X x) :=
  DirectSum.toAddMonoid_of (fun n => (directSumι S n - ι n ≫ directSumι S (n + 1)).app X) n x

theorem relHom_apply_zero {X : C} y : relHomApp S ι X y 0 = y 0 := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero]
  | of n x =>
    rw [relHom_of, DirectSum.sub_apply, of_eq_of_ne _ _ _ (Nat.succ_ne_zero n).symm, sub_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy]

theorem relHom_apply_succ {X : C} y (k : ℕ) :
    relHomApp S ι X y (k + 1) = y (k + 1) - (ι k).app X (y k) := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero, sub_zero]
  | of n x =>
    rw [relHom_of, DirectSum.sub_apply]
    congr 1
    by_cases h : n = k
    · subst h
      rw [of_eq_same, of_eq_same]
    · rw [of_eq_of_ne _ _ _ (by omega), of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
  | add x y hx hy =>
    rw [map_add, DirectSum.add_apply, hx, hy, DirectSum.add_apply, DirectSum.add_apply, map_add]
    abel

end SeqColimit

/-- The colimit of a sequence `S 0 ⟶ S 1 ⟶ ⋯` of morphisms of dg modules over `C`: the quotient
of `⨁ n, S n` by the image of `x ↦ x - ι n x`. -/
noncomputable abbrev seqColimit : CatModule.{w} C :=
  (Hom.range (SeqColimit.relHom S ι)).quotient

namespace SeqColimit

/-- The canonical morphism `S n ⟶ seqColimit S ι`. -/
noncomputable def of (n : ℕ) : S n ⟶ seqColimit S ι :=
  directSumι S n ≫ (Hom.range (relHom S ι)).mkQ

variable {S ι}

theorem of_app (n : ℕ) {X : C} (x : (S n).obj X) :
    (of S ι n).app X x =
      (Hom.range (relHom S ι)).mkQ.app X (DirectSum.of (fun n => (S n).obj X) n x) :=
  rfl

theorem of_succ_ι (n : ℕ) {X : C} (x : (S n).obj X) :
    (of S ι (n + 1)).app X ((ι n).app X x) = (of S ι n).app X x := by
  rw [of_app, of_app, eq_comm, ← sub_eq_zero, ← map_sub, CatSubmodule.mkQ_eq_zero_iff,
    ← relHom_of]
  exact ⟨_, rfl⟩

@[simp, reassoc]
theorem ι_comp_of (n : ℕ) : ι n ≫ of S ι (n + 1) = of S ι n :=
  hom_ext fun _ x => of_succ_ι n x

/-- Every element of the colimit comes from some `S n`. -/
theorem exists_of_eq {X : C} (x : (seqColimit S ι).obj X) :
    ∃ n y, (of S ι n).app X y = x := by
  obtain ⟨y, rfl⟩ := (Hom.range (relHom S ι)).mkQ_surjective X x
  change ⨁ n, (S n).obj X at y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by rw [map_zero, map_zero]⟩
  | of n x => exact ⟨n, x, rfl⟩
  | add x y hx hy =>
    obtain ⟨i, a, ha⟩ := hx
    obtain ⟨j, b, hb⟩ := hy
    have key : ∀ (i : ℕ) (a : (S i).obj X) (m : ℕ), i ≤ m →
        ∃ a' : (S m).obj X, (of S ι m).app X a' = (of S ι i).app X a := by
      intro i a m him
      induction m, him using Nat.le_induction with
      | base => exact ⟨a, rfl⟩
      | succ m _ ih =>
        obtain ⟨a', ha'⟩ := ih
        exact ⟨(ι m).app X a', (of_succ_ι m a').trans ha'⟩
    obtain ⟨a', ha'⟩ := key i a (i + j) (Nat.le_add_right i j)
    obtain ⟨b', hb'⟩ := key j b (i + j) (Nat.le_add_left j i)
    refine ⟨i + j, a' + b', ?_⟩
    rw [map_add, ha', hb', ha, hb]
    rfl

/-- If the transition maps are injective, so are the canonical maps into the colimit. -/
theorem of_injective (hι : ∀ n X, Function.Injective ((ι n).app X)) (n : ℕ) (X : C) :
    Function.Injective ((of S ι n).app X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [of_app, CatSubmodule.mkQ_eq_zero_iff, Hom.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  change ⨁ n, (S n).obj X at y
  have hy' : ∀ k, relHomApp S ι X y k = (DirectSum.of (fun n => (S n).obj X) n x) k :=
    fun k => by rw [← hy]; rfl
  have h0 : ∀ k, k < n → y k = 0 := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h := relHom_apply_zero ι y
      rw [hy', of_eq_of_ne _ _ _ (by omega)] at h
      exact h.symm
    | succ k ih =>
      intro hk
      have h := relHom_apply_succ ι y k
      rw [hy', of_eq_of_ne _ _ _ (by omega), ih (by omega), map_zero, sub_zero] at h
      exact h.symm
  have hn : y n = x := by
    cases n with
    | zero =>
      have h := relHom_apply_zero ι y
      rw [hy', of_eq_same] at h
      exact h.symm
    | succ k =>
      have h := relHom_apply_succ ι y k
      rw [hy', of_eq_same, h0 k (by omega), map_zero, sub_zero] at h
      exact h.symm
  by_contra hx0
  have hne : ∀ j, y (n + j) ≠ 0 := by
    intro j
    induction j with
    | zero => exact hn ▸ hx0
    | succ j ih =>
      intro hj
      have h := relHom_apply_succ ι y (n + j)
      change y (n + j + 1) = 0 at hj
      rw [hy', of_eq_of_ne _ _ _ (by omega), hj, zero_sub, eq_comm, neg_eq_zero,
        map_eq_zero_iff _ (hι _ X)] at h
      exact ih h
  exact Set.infinite_of_injective_forall_mem (add_right_injective n) hne
    (DFinsupp.finite_support y)

section Desc

variable {N : CatModule.{w} C}

/-- The cochain out of the colimit determined by a compatible family of cochains
`c n : S n → N`. -/
noncomputable def descCochain {k : ℤ} (c : ∀ n, Cochain (S n) N k)
    (hc : ∀ n {X : C} (x : (S n).obj X), (c (n + 1)).app X ((ι n).app X x) = (c n).app X x) :
    Cochain (seqColimit S ι) N k :=
  CatSubmodule.liftQCochain _ (Cochain.directSumDesc c) (by
    rintro X _ ⟨y, rfl⟩
    change ⨁ n, (S n).obj X at y
    induction y using DirectSum.induction_on with
    | zero => exact (congrArg _ (map_zero _)).trans (map_zero _)
    | of n x =>
      change (Cochain.directSumDesc c).app X
        (relHomApp S ι X (DirectSum.of (fun n => (S n).obj X) n x)) = 0
      rw [relHom_of, map_sub, Cochain.directSumDesc_app_of, Cochain.directSumDesc_app_of, hc,
        sub_self]
    | add x y hx hy =>
      change (Cochain.directSumDesc c).app X (relHomApp S ι X (x + y)) = 0
      rw [map_add, map_add]
      exact (congrArg₂ (· + ·) hx hy).trans (add_zero 0))

@[simp]
theorem descCochain_of {k : ℤ} (c : ∀ n, Cochain (S n) N k)
    (hc : ∀ n {X : C} (x : (S n).obj X), (c (n + 1)).app X ((ι n).app X x) = (c n).app X x)
    (n : ℕ) {X : C} (x : (S n).obj X) :
    (descCochain c hc).app X ((of S ι n).app X x) = (c n).app X x :=
  Cochain.directSumDesc_app_of c n x

variable (g : ∀ n, S n ⟶ N) (hg : ∀ n, ι n ≫ g (n + 1) = g n)

include hg

/-- The morphism out of the colimit determined by a compatible family of morphisms
`g n : S n ⟶ N`. -/
noncomputable def desc : seqColimit S ι ⟶ N :=
  CatSubmodule.liftQ (directSumDesc g) (by
    rintro X _ ⟨y, rfl⟩
    have h : relHom S ι ≫ directSumDesc g = 0 := directSum_hom_ext (F := S) fun n => by
      dsimp only [relHom]
      rw [← Category.assoc, directSumι_desc, Preadditive.sub_comp, directSumι_desc,
        Category.assoc, directSumι_desc, hg, sub_self, Limits.comp_zero]
    exact congrArg (fun χ : directSum S ⟶ N => χ.app X y) h)

@[simp]
theorem desc_of (n : ℕ) {X : C} (x : (S n).obj X) :
    (desc g hg).app X ((of S ι n).app X x) = (g n).app X x :=
  DirectSum.toAddMonoid_of (fun n => (g n).app X) n x

@[simp, reassoc]
theorem of_comp_desc (n : ℕ) : of S ι n ≫ desc g hg = g n :=
  hom_ext fun _ x => desc_of g hg n x

end Desc

end SeqColimit

end CatModule

end DG
