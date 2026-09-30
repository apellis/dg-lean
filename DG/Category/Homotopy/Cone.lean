import DG.Category.Homotopy.Shift
import DG.Module.Prod

/-!
# Mapping cones of morphisms of dg modules over a dg category

Let `C` be a dg category. The mapping cone of a morphism `f : M ⟶ N` of dg modules over `C` is
the dg module `cone f` with values `(cone f) X = (M⟦1⟧) X × N X` (the product with the
componentwise action, the action on `M⟦1⟧` being the twisted one) and the differential

  `d (x, y) = (d_{M⟦1⟧} x, f x + d_N y) = (-d_M x, f x + d_N y)`,

objectwise. This is a port of `DG.Module.Cone` (the case of a dg ring), whose conventions are
those of Mathlib's `CochainComplex.mappingCone`.

* `DG.CatModule.coneObj f X`: the value at `X`, a type synonym for `(shift 1 M).obj X × N.obj X`
  with the cone differential; `DG.CatModule.cone f`: the mapping cone.
* `DG.CatModule.cone.inr f : N ⟶ cone f` and `DG.CatModule.cone.fstHom f : cone f ⟶ shift 1 M`,
  the morphisms of the standard triangle `M → N → cone f → M⟦1⟧`, with `inr ≫ fstHom = 0`.
* `DG.CatModule.cone.inlAddHom f X : (shift 1 M).obj X →+ (cone f).obj X` and
  `DG.CatModule.cone.sndAddHom f X : (cone f).obj X →+ N.obj X`, the other two structure maps,
  of degree `0` and commuting with the action but not with the differentials (the dg-ring
  version's `inlLinear` and `sndLinear`).
* `DG.CatModule.cone.map`: functoriality, a commutative square `f ≫ g = e ≫ f'` induces
  `cone f ⟶ cone f'`.

The cochain-level structure maps with Mathlib's names and degrees are in
`DG.Category.Homotopy.ConeCochain`. The cone is written `cone f` (a term of `CatModule C`)
rather than `Cone f` (the dg-ring version's type).
-/

open CategoryTheory

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {M N : CatModule.{w} C}

omit [DGCategory C] in
theorem Hom.map_units_smul (φ : M ⟶ N) {X : C} (u : ℤˣ) (m : M.obj X) :
    φ.app X (u • m) = u • φ.app X m := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- The value at `X` of the mapping cone of `f : M ⟶ N`: the abelian group
`(M⟦1⟧) X × N X`, with the differential `d (x, y) = (d x, f x + d y)`. -/
def coneObj (_f : M ⟶ N) (X : C) : Type w := (shift 1 M).obj X × N.obj X

namespace coneObj

variable (f : M ⟶ N) (X : C)

instance : AddCommGroup (coneObj f X) :=
  inferInstanceAs (AddCommGroup ((shift 1 M).obj X × N.obj X))

/-- The differential of the mapping cone, `d (x, y) = (d_{M⟦1⟧} x, f x + d y)`, as an additive
map. -/
def dAddMonoidHom : coneObj f X →+ coneObj f X :=
  ((d : (shift 1 M).obj X →+ (shift 1 M).obj X).comp
      (AddMonoidHom.fst ((shift 1 M).obj X) (N.obj X))).prod
    ((f.app X).comp ((shift.unmk 1).toAddMonoidHom.comp
        (AddMonoidHom.fst ((shift 1 M).obj X) (N.obj X))) +
      (d : N.obj X →+ N.obj X).comp (AddMonoidHom.snd ((shift 1 M).obj X) (N.obj X)))

instance : DGAddCommGroup (coneObj f X) where
  grading := grading (M := (shift 1 M).obj X × N.obj X)
  decomposition := DGAddCommGroup.decomposition (M := (shift 1 M).obj X × N.obj X)
  d := dAddMonoidHom f X
  d_mem' {k p} hp := by
    have hp' : p.1 ∈ grading k ∧ p.2 ∈ grading k := Prod.mem_grading.mp hp
    exact Prod.mem_grading.mpr ⟨d_mem hp'.1,
      add_mem (f.map_mem (shift.unmk_mem_grading hp'.1)) (d_mem hp'.2)⟩
  d_d' p := by
    apply Prod.ext
    · exact d_d (M := (shift 1 M).obj X) _
    · change f.app X (shift.unmk 1 (d p.1)) + d (f.app X (shift.unmk 1 p.1) + d p.2) = 0
      rw [shift.unmk_d, koszulSign, Int.negOnePow_one, Units.neg_smul, one_smul, map_neg, d_add,
        d_d, add_zero, ← Hom.map_d, neg_add_cancel]

end coneObj

set_option backward.isDefEq.respectTransparency false in
/-- The mapping cone of a morphism `f : M ⟶ N` of dg modules over `C`: the values
`(M⟦1⟧) X × N X` with the differential `d (x, y) = (-d x, f x + d y)` and the componentwise
action. -/
def cone (f : M ⟶ N) : CatModule.{w} C where
  obj X := coneObj f X
  act := AddMonoidHom.mk'
    (fun g => AddMonoidHom.prodMap ((shift 1 M).act g) (N.act g)) fun g g' => by
      ext <;> simp [AddMonoidHom.add_apply]
  act_mem' hg hp := Prod.mem_grading.mpr
    ⟨smul_mem_grading hg (Prod.mem_grading.mp hp).1, smul_mem_grading hg (Prod.mem_grading.mp hp).2⟩
  act_id' _ p := Prod.ext (id_smul (M := shift 1 M) p.1) (id_smul (M := N) p.2)
  act_comp' g g' p := Prod.ext (comp_smul (M := shift 1 M) g g' p.1) (comp_smul (M := N) g g' p.2)
  d_act' {X Y i g} hg p := by
    apply Prod.ext
    · exact d_smul (M := shift 1 M) hg p.1
    · change f.app Y (shift.unmk 1 (g • p.1)) + d (g • p.2) =
        (d g • p.2) + koszulSign i • (g • (f.app X (shift.unmk 1 p.1) + d p.2))
      rw [shift.unmk_smul hg, one_mul, Hom.map_units_smul, Hom.map_smul, d_smul hg, smul_add,
        _root_.smul_add]
      abel

namespace cone

variable (f : M ⟶ N)

/-- The inclusion of `(M⟦1⟧) X` into the cone, `x ↦ (x, 0)`: of degree `0` and commuting with
the action, but not with the differentials (see `DG.CatModule.cone.d_inlAddHom`). -/
def inlAddHom (X : C) : (shift 1 M).obj X →+ (cone f).obj X :=
  AddMonoidHom.inl ((shift 1 M).obj X) (N.obj X)

/-- The projection of the cone onto `N X`, `(x, y) ↦ y`: of degree `0` and commuting with the
action, but not with the differentials (see `DG.CatModule.cone.sndAddHom_d`). -/
def sndAddHom (X : C) : (cone f).obj X →+ N.obj X :=
  AddMonoidHom.snd ((shift 1 M).obj X) (N.obj X)

/-- The inclusion of `N` into the cone, `y ↦ (0, y)`, as a morphism of dg modules. -/
def inr : N ⟶ cone f where
  app X := AddMonoidHom.inr ((shift 1 M).obj X) (N.obj X)
  map_mem' hy := Prod.mem_grading.mpr ⟨zero_mem _, hy⟩
  map_d' {X} y := by
    apply Prod.ext
    · exact (d_zero (M := (shift 1 M).obj X)).symm
    · change d y = f.app X (shift.unmk 1 0) + d y
      rw [map_zero, map_zero, zero_add]
  map_smul' g y := Prod.ext (smul_zero (M := shift 1 M) g).symm rfl

/-- The projection of the cone onto `M⟦1⟧`, `(x, y) ↦ x`, as a morphism of dg modules. -/
def fstHom : cone f ⟶ shift 1 M where
  app X := AddMonoidHom.fst ((shift 1 M).obj X) (N.obj X)
  map_mem' hp := (Prod.mem_grading.mp hp).1
  map_d' _ := rfl
  map_smul' _ _ := rfl

/-! ### Evaluation lemmas -/

variable {f} {X : C}

@[simp] theorem fstHom_inlAddHom (x : (shift 1 M).obj X) :
    (fstHom f).app X (inlAddHom f X x) = x := rfl
@[simp] theorem sndAddHom_inlAddHom (x : (shift 1 M).obj X) :
    sndAddHom f X (inlAddHom f X x) = 0 := rfl
@[simp] theorem fstHom_inr (y : N.obj X) : (fstHom f).app X ((inr f).app X y) = 0 := rfl
@[simp] theorem sndAddHom_inr (y : N.obj X) : sndAddHom f X ((inr f).app X y) = y := rfl

@[ext]
theorem ext {p q : (cone f).obj X} (h₁ : (fstHom f).app X p = (fstHom f).app X q)
    (h₂ : sndAddHom f X p = sndAddHom f X q) : p = q :=
  Prod.ext h₁ h₂

theorem inlAddHom_fstHom_add_inr_sndAddHom (p : (cone f).obj X) :
    inlAddHom f X ((fstHom f).app X p) + (inr f).app X (sndAddHom f X p) = p :=
  ext (add_zero _) (zero_add _)

variable (f) in
@[simp]
theorem inr_comp_fstHom : inr f ≫ fstHom f = 0 := rfl

theorem mem_grading_iff {k : ℤ} {p : (cone f).obj X} :
    p ∈ grading k ↔ (fstHom f).app X p ∈ grading k ∧ sndAddHom f X p ∈ grading k :=
  Prod.mem_grading

theorem inlAddHom_mem {k : ℤ} {x : (shift 1 M).obj X} (hx : x ∈ grading k) :
    inlAddHom f X x ∈ grading k :=
  mem_grading_iff.mpr ⟨hx, zero_mem _⟩

theorem sndAddHom_mem {k : ℤ} {p : (cone f).obj X} (hp : p ∈ grading k) :
    sndAddHom f X p ∈ grading k :=
  (mem_grading_iff.mp hp).2

theorem inlAddHom_smul {Y : C} (g : X ⟶ Y) (x : (shift 1 M).obj X) :
    inlAddHom f Y (g • x) = g • inlAddHom f X x :=
  Prod.ext rfl (smul_zero (M := N) g).symm

theorem sndAddHom_smul {Y : C} (g : X ⟶ Y) (p : (cone f).obj X) :
    sndAddHom f Y (g • p) = g • sndAddHom f X p := rfl

/-- The first component of the differential of the cone: `fstHom` is a chain map. -/
theorem fstHom_d (p : (cone f).obj X) : (fstHom f).app X (d p) = d ((fstHom f).app X p) := rfl

/-- The second component of the differential of the cone. -/
theorem sndAddHom_d (p : (cone f).obj X) :
    sndAddHom f X (d p) = f.app X (shift.unmk 1 ((fstHom f).app X p)) + d (sndAddHom f X p) :=
  rfl

theorem d_inlAddHom (x : (shift 1 M).obj X) :
    d (inlAddHom f X x) = inlAddHom f X (d x) + (inr f).app X (f.app X (shift.unmk 1 x)) :=
  ext (by simp) (by simp [sndAddHom_d])

/-! ### Functoriality -/

section Map

variable {M' N' : CatModule.{w} C} {f' : M' ⟶ N'} (e : M ⟶ M') (g : N ⟶ N')

/-- A commutative square `f ≫ g = e ≫ f'` induces a morphism of mapping cones,
`(x, y) ↦ (e x, g y)`. -/
def map (h : f ≫ g = e ≫ f') : cone f ⟶ cone f' where
  app X := AddMonoidHom.prodMap ((shiftMap 1 e).app X) (g.app X)
  map_mem' hp := Prod.mem_grading.mpr
    ⟨(shiftMap 1 e).map_mem (Prod.mem_grading.mp hp).1, g.map_mem (Prod.mem_grading.mp hp).2⟩
  map_d' {X} p := by
    refine ext ?_ ?_
    · exact (shiftMap 1 e).map_d _
    · change g.app X (f.app X (shift.unmk 1 p.1) + d p.2) =
        f'.app X (shift.unmk 1 ((shiftMap 1 e).app X p.1)) + d (g.app X p.2)
      rw [map_add, Hom.map_d, unmk_shiftMap_app, ← comp_app, h, comp_app]
  map_smul' {X Y} k p := Prod.ext ((shiftMap 1 e).map_smul k p.1) (g.map_smul k p.2)

@[simp]
theorem fstHom_map (h : f ≫ g = e ≫ f') (p : (cone f).obj X) :
    (fstHom f').app X ((map e g h).app X p) = (shiftMap 1 e).app X ((fstHom f).app X p) := rfl

@[simp]
theorem sndAddHom_map (h : f ≫ g = e ≫ f') (p : (cone f).obj X) :
    sndAddHom f' X ((map e g h).app X p) = g.app X (sndAddHom f X p) := rfl

theorem inr_comp_map (h : f ≫ g = e ≫ f') : inr f ≫ map e g h = g ≫ inr f' :=
  hom_ext fun X _ => ext (map_zero ((shiftMap 1 e).app X)) rfl

theorem map_comp_fstHom (h : f ≫ g = e ≫ f') :
    map e g h ≫ fstHom f' = fstHom f ≫ shiftMap 1 e :=
  rfl

end Map

end cone

end CatModule

end DG
