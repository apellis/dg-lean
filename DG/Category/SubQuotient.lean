import DG.Category.Module
import DG.Module.Corner
import DG.Module.Quotient

/-!
# Submodules and quotients of dg modules over a dg category

A dg submodule `S` of a dg module `M` over `C` (`DG.CatSubmodule M`) is a family of subgroups
`S.carrier X ⊆ M.obj X` which are homogeneous (closed under taking homogeneous components),
stable under `d` and under the action of the morphisms of `C`. Then `X ↦ S.carrier X` is a dg
module (`DG.CatSubmodule.toCatModule`, with the restricted structures) and so is
`X ↦ M.obj X ⧸ S.carrier X` (`DG.CatSubmodule.quotient`, with the induced structures, as in
`DG.DGAddCommGroup.quotient`).

## Main definitions

* `DG.CatSubmodule.subtype`, `DG.CatSubmodule.codRestrict`: the inclusion and corestriction.
* `DG.CatSubmodule.mkQ`, `DG.CatSubmodule.liftQ`: the quotient map and the universal property.
* `DG.CatModule.Hom.ker`, `DG.CatModule.Hom.range`: kernel and image of a morphism.
-/

open CategoryTheory DirectSum

universe w v u

namespace DG

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- A dg submodule of a dg module `M` over `C`: subgroups `carrier X` of the `M.obj X` which
contain the homogeneous components of their elements and are stable under the differential and
under the action of the morphisms of `C`. -/
structure CatSubmodule (M : CatModule.{w} C) where
  /-- The subgroup at an object. -/
  carrier : ∀ X : C, AddSubgroup (M.obj X)
  decompose_mem' : ∀ {X : C} {m : M.obj X}, m ∈ carrier X → ∀ n : ℤ,
    (decompose (grading (M := M.obj X)) m n : M.obj X) ∈ carrier X
  d_mem' : ∀ {X : C} {m : M.obj X}, m ∈ carrier X → d m ∈ carrier X
  smul_mem' : ∀ {X Y : C} (f : X ⟶ Y) {m : M.obj X}, m ∈ carrier X → f • m ∈ carrier Y

namespace CatSubmodule

variable {M : CatModule.{w} C} (S : CatSubmodule M)

theorem decompose_mem {X : C} {m : M.obj X} (hm : m ∈ S.carrier X) (n : ℤ) :
    (decompose (grading (M := M.obj X)) m n : M.obj X) ∈ S.carrier X :=
  S.decompose_mem' hm n

theorem d_mem {X : C} {m : M.obj X} (hm : m ∈ S.carrier X) : d m ∈ S.carrier X :=
  S.d_mem' hm

theorem smul_mem {X Y : C} (f : X ⟶ Y) {m : M.obj X} (hm : m ∈ S.carrier X) :
    f • m ∈ S.carrier Y :=
  S.smul_mem' f hm

instance isDGAddSubgroup (X : C) : IsDGAddSubgroup (S.carrier X) where
  decompose_mem hm n := S.decompose_mem hm n
  d_mem hm := S.d_mem hm

/-! ### The submodule as a dg module -/

/-- The dg abelian group structure on `S.carrier X`, restricted from `M.obj X`. -/
noncomputable def dgAddCommGroup (X : C) : DGAddCommGroup (S.carrier X) :=
  DGAddCommGroup.ofInjective (AddSubgroupClass.subtype (S.carrier X)) Subtype.val_injective
    (((d : M.obj X →+ M.obj X).comp (AddSubgroupClass.subtype _)).codRestrict _
      fun m => S.d_mem m.2)
    (fun _ => rfl) fun n m => ⟨⟨_, S.decompose_mem m.2 n⟩, rfl⟩

/-- The action of `f : X ⟶ Y` on the submodule. -/
def actSub {X Y : C} : (X ⟶ Y) →+ S.carrier X →+ S.carrier Y :=
  AddMonoidHom.mk'
    (fun f => ((M.act f).comp (AddSubgroupClass.subtype _)).codRestrict _
      fun m => S.smul_mem f m.2)
    fun f g => by
      ext m
      exact CatModule.add_smul (M := M) f g (m : M.obj X)

/-- A dg submodule is a dg module. -/
noncomputable def toCatModule : CatModule.{w} C where
  obj X := S.carrier X
  isDGAddCommGroup X := S.dgAddCommGroup X
  act := S.actSub
  act_mem' hf hm := CatModule.smul_mem_grading (M := M) hf hm
  act_id' _ m := Subtype.ext (CatModule.id_smul (M := M) m.1)
  act_comp' f g m := Subtype.ext (CatModule.comp_smul (M := M) f g m.1)
  d_act' {X Y i f} hf m := Subtype.ext (by
    change d (f • (m : M.obj X)) = d f • (m : M.obj X) + ((koszulSign i : ℤ) • f • d (m : M.obj X))
    rw [CatModule.d_smul hf, Units.smul_def])

@[simp]
theorem coe_smul {X Y : C} (f : X ⟶ Y) (m : S.toCatModule.obj X) :
    (f • m : S.toCatModule.obj Y).1 = f • m.1 := rfl

@[simp]
theorem coe_d {X : C} (m : S.toCatModule.obj X) :
    (d m : S.toCatModule.obj X).1 = d m.1 := rfl

theorem mem_grading_iff {X : C} {n : ℤ} {m : S.toCatModule.obj X} :
    m ∈ grading n ↔ m.1 ∈ grading n :=
  Iff.rfl

/-- The inclusion of a dg submodule. -/
@[simps]
noncomputable def subtype : S.toCatModule ⟶ M where
  app X := AddSubgroupClass.subtype (S.carrier X)
  map_mem' hm := hm
  map_d' _ := rfl
  map_smul' _ _ := rfl

theorem subtype_injective (X : C) : Function.Injective (S.subtype.app X) :=
  Subtype.val_injective

variable {S} in
/-- Corestriction of a morphism to a dg submodule containing its image. -/
@[simps]
noncomputable def codRestrict {N : CatModule.{w} C} (φ : N ⟶ M)
    (h : ∀ X (m : N.obj X), φ.app X m ∈ S.carrier X) : N ⟶ S.toCatModule where
  app X := (φ.app X).codRestrict _ (h X)
  map_mem' hm := φ.map_mem hm
  map_d' m := Subtype.ext (φ.map_d m)
  map_smul' f m := Subtype.ext (φ.map_smul f m)

@[simp]
theorem codRestrict_comp_subtype {N : CatModule.{w} C} (φ : N ⟶ M)
    (h : ∀ X (m : N.obj X), φ.app X m ∈ S.carrier X) : codRestrict φ h ≫ S.subtype = φ :=
  rfl

/-! ### The quotient -/

/-- The action of `f : X ⟶ Y` on the quotient. -/
def actQuot {X Y : C} : (X ⟶ Y) →+ (M.obj X ⧸ S.carrier X) →+ (M.obj Y ⧸ S.carrier Y) :=
  AddMonoidHom.mk'
    (fun f => QuotientAddGroup.map _ _ (M.act f) fun m hm => S.smul_mem f hm)
    fun f g => by
      ext m
      exact congrArg (QuotientAddGroup.mk (s := S.carrier Y))
        (CatModule.add_smul (M := M) f g m)

/-- The quotient of a dg module by a dg submodule. -/
noncomputable def quotient : CatModule.{w} C where
  obj X := M.obj X ⧸ S.carrier X
  act := S.actQuot
  act_mem' {X Y i j f y} hf hy := by
    obtain ⟨m, hm, rfl⟩ := hy
    exact mk_mem_grading_quotient (CatModule.smul_mem_grading (M := M) hf hm)
  act_id' _ y := by
    induction y using QuotientAddGroup.induction_on with
    | H m => exact congrArg (QuotientAddGroup.mk (s := S.carrier _)) (CatModule.id_smul m)
  act_comp' f g y := by
    induction y using QuotientAddGroup.induction_on with
    | H m => exact congrArg (QuotientAddGroup.mk (s := S.carrier _)) (CatModule.comp_smul f g m)
  d_act' {X Y i f} hf y := by
    induction y using QuotientAddGroup.induction_on with
    | H m =>
      change (QuotientAddGroup.mk (d (f • m)) : M.obj Y ⧸ S.carrier Y) =
        QuotientAddGroup.mk (d f • m) + ((koszulSign i : ℤ) • QuotientAddGroup.mk (f • d m))
      rw [CatModule.d_smul hf, Units.smul_def, QuotientAddGroup.mk_add, QuotientAddGroup.mk_zsmul]

/-- The quotient map `M ⟶ M ⧸ S`. -/
@[simps]
noncomputable def mkQ : M ⟶ S.quotient where
  app X := QuotientAddGroup.mk' (S.carrier X)
  map_mem' hm := mk_mem_grading_quotient hm
  map_d' _ := rfl
  map_smul' _ _ := rfl

theorem mkQ_surjective (X : C) : Function.Surjective (S.mkQ.app X) :=
  QuotientAddGroup.mk'_surjective _

theorem mkQ_eq_zero_iff {X : C} {m : M.obj X} : S.mkQ.app X m = 0 ↔ m ∈ S.carrier X :=
  QuotientAddGroup.eq_zero_iff m

variable {S} in
/-- A morphism vanishing on `S` factors through the quotient `M ⧸ S`. -/
@[simps]
noncomputable def liftQ {N : CatModule.{w} C} (φ : M ⟶ N)
    (h : ∀ X, ∀ m ∈ S.carrier X, φ.app X m = 0) : S.quotient ⟶ N where
  app X := QuotientAddGroup.lift _ (φ.app X) fun m hm => h X m hm
  map_mem' := by
    rintro X n _ ⟨m, hm, rfl⟩
    exact φ.map_mem hm
  map_d' {X} y := by
    induction y using QuotientAddGroup.induction_on with
    | H m => exact φ.map_d m
  map_smul' f y := by
    induction y using QuotientAddGroup.induction_on with
    | H m => exact φ.map_smul f m

@[simp]
theorem mkQ_comp_liftQ {N : CatModule.{w} C} (φ : M ⟶ N)
    (h : ∀ X, ∀ m ∈ S.carrier X, φ.app X m = 0) : S.mkQ ≫ liftQ φ h = φ :=
  rfl

/-- Two morphisms out of `M ⧸ S` agreeing after composition with the quotient map are equal. -/
theorem quotient_hom_ext {N : CatModule.{w} C} {φ ψ : S.quotient ⟶ N}
    (h : S.mkQ ≫ φ = S.mkQ ≫ ψ) : φ = ψ :=
  CatModule.hom_ext fun X y => by
    obtain ⟨m, rfl⟩ := S.mkQ_surjective X y
    exact congrArg (fun χ : M ⟶ N => χ.app X m) h

end CatSubmodule

namespace CatModule.Hom

variable {M N : CatModule.{w} C} (φ : M ⟶ N)

/-- The kernel of a morphism of dg modules, as a dg submodule. -/
def ker : CatSubmodule M where
  carrier X := (φ.app X).ker
  decompose_mem' {X m} hm n := by
    rw [AddMonoidHom.mem_ker] at hm ⊢
    rw [← coe_decompose_map_of_map_mem (φ.app X) (fun h => φ.map_mem h) m n, hm,
      decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  d_mem' {X m} hm := by
    rw [AddMonoidHom.mem_ker] at hm ⊢
    rw [φ.map_d, hm, d_zero]
  smul_mem' f m hm := by
    rw [AddMonoidHom.mem_ker] at hm ⊢
    rw [φ.map_smul, hm, smul_zero]

@[simp]
theorem mem_ker {X : C} {m : M.obj X} : m ∈ (ker φ).carrier X ↔ φ.app X m = 0 :=
  AddMonoidHom.mem_ker

/-- The image of a morphism of dg modules, as a dg submodule. -/
def range : CatSubmodule N where
  carrier X := (φ.app X).range
  decompose_mem' := by
    rintro X _ ⟨m, rfl⟩ n
    exact ⟨_, (coe_decompose_map_of_map_mem (φ.app X) (fun h => φ.map_mem h) m n).symm⟩
  d_mem' := by
    rintro X _ ⟨m, rfl⟩
    exact ⟨d m, φ.map_d m⟩
  smul_mem' := by
    rintro X Y f _ ⟨m, rfl⟩
    exact ⟨f • m, φ.map_smul f m⟩

@[simp]
theorem mem_range {X : C} {n : N.obj X} : n ∈ (range φ).carrier X ↔ ∃ m, φ.app X m = n :=
  AddMonoidHom.mem_range

end CatModule.Hom

end DG
