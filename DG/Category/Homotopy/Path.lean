import DG.Category.Homotopy.Homotopy
import DG.Category.Homotopy.Precomp
import DG.Module.Prod

/-!
# The path object of a dg module over a dg category

Let `C` be a dg category. The path object of a dg module `N` over `C` is the dg module
`pathObj N` with values `N X × (N⟦-1⟧) X` (the product with the componentwise action, the
action on `N⟦-1⟧` being the twisted one) and the differential

  `d (a, b) = (d a, a + d_{N⟦-1⟧} b) = (d a, a - d b)`,

objectwise, together with the projection `pathObj.π N : pathObj N ⟶ N`, `(a, b) ↦ a`. A
morphism `f : M ⟶ N` is null-homotopic iff it factors through `pathObj.π N`: a null-homotopy
`h` of `f` gives the lift `x ↦ (f x, h x)` (`DG.CatModule.homotopic_zero_iff_exists_lift`).
The path object is compatible with restriction along a dg functor
(`DG.CatModule.pathObj.precompIso`); this is used to show that adjunctions whose right adjoint
is a restriction functor descend to homotopy categories.

## Main definitions and results

* `DG.CatModule.pathObj N`, `DG.CatModule.pathObj.π N`.
* `DG.CatModule.pathObj.homotopic_π_zero`: the projection is null-homotopic.
* `DG.CatModule.homotopic_zero_iff_exists_lift`: `f` is null-homotopic iff it factors through
  the projection.
* `DG.CatModule.pathObj.precompIso F N : (N ∘ F)ᴾ ≅ Nᴾ ∘ F`, compatible with the projections.
-/

open CategoryTheory

universe w v u v' u'

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {M N : CatModule.{w} C}

/-- The value at `X` of the path object of `N`: the abelian group `N X × (N⟦-1⟧) X`, with the
differential `d (a, b) = (d a, a + d b)`. -/
def pathObjObj (N : CatModule.{w} C) (X : C) : Type w := N.obj X × (shift (-1) N).obj X

namespace pathObjObj

variable (N : CatModule.{w} C) (X : C)

instance : AddCommGroup (pathObjObj N X) :=
  inferInstanceAs (AddCommGroup (N.obj X × (shift (-1) N).obj X))

/-- The differential of the path object, `d (a, b) = (d a, a + d b)`, as an additive map. -/
def dAddMonoidHom : pathObjObj N X →+ pathObjObj N X :=
  ((d : N.obj X →+ N.obj X).comp (AddMonoidHom.fst (N.obj X) ((shift (-1) N).obj X))).prod
    ((shift.mk (-1)).toAddMonoidHom.comp (AddMonoidHom.fst (N.obj X) ((shift (-1) N).obj X)) +
      (d : (shift (-1) N).obj X →+ (shift (-1) N).obj X).comp
        (AddMonoidHom.snd (N.obj X) ((shift (-1) N).obj X)))

instance : DGAddCommGroup (pathObjObj N X) where
  grading := grading (M := N.obj X × (shift (-1) N).obj X)
  decomposition := DGAddCommGroup.decomposition (M := N.obj X × (shift (-1) N).obj X)
  d := dAddMonoidHom N X
  d_mem' {k p} hp := by
    have hp' : p.1 ∈ grading k ∧ p.2 ∈ grading k := Prod.mem_grading.mp hp
    refine Prod.mem_grading.mpr ⟨d_mem hp'.1, add_mem ?_ (d_mem hp'.2)⟩
    have := shift.mk_mem_grading (n := -1) hp'.1
    rwa [sub_neg_eq_add] at this
  d_d' p := by
    apply Prod.ext
    · exact d_d (M := N.obj X) _
    · change shift.mk (-1) (d p.1) + d (shift.mk (-1) p.1 + d p.2) = 0
      rw [d_add, d_d, add_zero, shift.d_mk, koszulSign, Int.negOnePow_neg, Int.negOnePow_one,
        Units.neg_smul, one_smul, map_neg, add_neg_cancel]

end pathObjObj

set_option backward.isDefEq.respectTransparency false in
/-- The path object of a dg module `N` over `C`: the values `N X × (N⟦-1⟧) X` with the
differential `d (a, b) = (d a, a - d b)` and the componentwise action. -/
def pathObj (N : CatModule.{w} C) : CatModule.{w} C where
  obj X := pathObjObj N X
  act := AddMonoidHom.mk'
    (fun g => AddMonoidHom.prodMap (N.act g) ((shift (-1) N).act g)) fun g g' => by
      ext <;> simp [AddMonoidHom.add_apply]
  act_mem' hg hp := Prod.mem_grading.mpr
    ⟨smul_mem_grading hg (Prod.mem_grading.mp hp).1,
      smul_mem_grading hg (Prod.mem_grading.mp hp).2⟩
  act_id' _ p := Prod.ext (id_smul (M := N) p.1) (id_smul (M := shift (-1) N) p.2)
  act_comp' g g' p :=
    Prod.ext (comp_smul (M := N) g g' p.1) (comp_smul (M := shift (-1) N) g g' p.2)
  d_act' {X Y i g} hg p := by
    apply Prod.ext
    · exact d_smul (M := N) hg p.1
    · change shift.mk (-1) (g • p.1) + d (g • p.2) =
        (d g • p.2) + koszulSign i • (g • (shift.mk (-1) p.1 + d p.2))
      rw [d_smul (M := shift (-1) N) hg, smul_add, _root_.smul_add, shift.smul_mk hg,
        show (-1 : ℤ) * i = -i by ring,
        show koszulSign (-i) = koszulSign i from Int.negOnePow_neg i,
        shift.mk_units_smul, smul_smul, Int.units_mul_self, one_smul]
      abel

namespace pathObj

variable (N)

/-- The projection `pathObj N ⟶ N`, `(a, b) ↦ a`. -/
def π : pathObj N ⟶ N where
  app X := AddMonoidHom.fst (N.obj X) ((shift (-1) N).obj X)
  map_mem' hp := (Prod.mem_grading.mp hp).1
  map_d' _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem π_app {X : C} (p : (pathObj N).obj X) : (π N).app X p = p.1 := rfl

/-- The null-homotopy `(a, b) ↦ b` of the projection. -/
def homotopy : Cochain (pathObj N) N (-1) where
  app X := (shift.unmk (-1)).toAddMonoidHom.comp
    (AddMonoidHom.snd (N.obj X) ((shift (-1) N).obj X))
  map_mem' {X i p} hp := shift.unmk_mem_grading (Prod.mem_grading.mp hp).2
  map_smul' {X Y i g} hg p := by
    change shift.unmk (-1) (g • p.2) = _
    rw [shift.unmk_smul_eq, twist_of_mem hg, units_smul_smul, show -1 * i = i * -1 by ring]
    rfl

theorem homotopy_app {X : C} (p : (pathObj N).obj X) :
    (homotopy N).app X p = shift.unmk (-1) p.2 := rfl

theorem ofHom_π : Cochain.ofHom (π N) = δ (-1) 0 (homotopy N) := by
  ext X p
  rw [Cochain.ofHom_apply, δ_neg_one_apply, homotopy_app, homotopy_app, π_app]
  change p.1 = d (shift.unmk (-1) p.2) + shift.unmk (-1) (shift.mk (-1) p.1 + d p.2)
  rw [map_add, shift.unmk_mk, shift.unmk_d, koszulSign, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul]
  abel

/-- The projection of the path object is null-homotopic. -/
theorem homotopic_π_zero : Homotopic (π N) 0 :=
  mem_nullHomotopic_iff_exists.mpr ⟨homotopy N, ofHom_π N⟩

variable {N}

/-- The lift `x ↦ (f x, h x)` of a morphism `f` with a null-homotopy `h`. -/
def lift (f : M ⟶ N) (h : Cochain M N (-1)) (hh : Cochain.ofHom f = δ (-1) 0 h) :
    M ⟶ pathObj N where
  app X := (f.app X).prod ((shift.mk (-1)).toAddMonoidHom.comp (h.app X))
  map_mem' {X k x} hx := Prod.mem_grading.mpr ⟨f.map_mem hx, by
    have := shift.mk_mem_grading (n := -1) (h.map_mem hx)
    rwa [sub_neg_eq_add, neg_add_cancel_right] at this⟩
  map_d' {X} x := by
    have e := congrArg (fun z : Cochain M N 0 => z.app X x) hh
    simp only [Cochain.ofHom_apply, δ_neg_one_apply] at e
    apply Prod.ext
    · exact f.map_d x
    · change shift.mk (-1) (h.app X (d x)) =
        shift.mk (-1) (f.app X x) + d (shift.mk (-1) (h.app X x))
      rw [shift.d_mk, koszulSign, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul,
        one_smul, ← map_add, e]
      congr 1
      abel
  map_smul' {X Y} g x := by
    apply Prod.ext
    · exact f.map_smul g x
    · change shift.mk (-1) (h.app Y (g • x)) = g • shift.mk (-1) (h.app X x)
      rw [shift.smul_mk_eq]
      congr 1
      induction g using DG.induction_on with
      | h_zero => simp
      | h_homogeneous g =>
        rw [h.map_smul g.2, twist_of_mem g.2, units_smul_smul,
          show (-1 : ℤ) * _ = _ * -1 by ring]
      | h_add g g' hg hg' => rw [map_add, add_smul, map_add, add_smul, hg, hg']

@[simp, reassoc]
theorem lift_π (f : M ⟶ N) (h : Cochain M N (-1)) (hh : Cochain.ofHom f = δ (-1) 0 h) :
    lift f h hh ≫ π N = f :=
  rfl

end pathObj

/-- A morphism `f : M ⟶ N` is null-homotopic iff it factors through the projection
`pathObj N ⟶ N`. -/
theorem homotopic_zero_iff_exists_lift (f : M ⟶ N) :
    Homotopic f 0 ↔ ∃ H : M ⟶ pathObj N, H ≫ pathObj.π N = f := by
  constructor
  · intro hf
    obtain ⟨h, hh⟩ := mem_nullHomotopic_iff_exists.mp hf
    exact ⟨pathObj.lift f h hh, pathObj.lift_π f h hh⟩
  · rintro ⟨H, rfl⟩
    exact (Homotopic.comp_left (pathObj.homotopic_π_zero N) H).trans
      (Homotopic.of_eq Limits.comp_zero)

/-! ### Compatibility with restriction -/

section Precomp

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  [DGCategory D] (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

namespace pathObj

/-- The path object of a restricted module is the restriction of the path object. -/
def precompIso (N : CatModule.{w} D) :
    pathObj ((precomp F).obj N) ≅ (precomp F).obj (pathObj N) :=
  isoMk (fun _ => AddEquiv.refl _) (fun {_ _ _} => Iff.rfl) (fun _ => rfl)
    (fun {X Y} f p => Prod.ext rfl (by
      change shift.mk (-1) (N.act (F.map (twist (-1) f)) (shift.unmk (-1) p.2)) =
        shift.mk (-1) (N.act (twist (-1) (F.map f)) (shift.unmk (-1) p.2))
      rw [F.map_twist]))

@[reassoc (attr := simp)]
theorem precompIso_hom_π (N : CatModule.{w} D) :
    (precompIso F N).hom ≫ (precomp F).map (π N) = π ((precomp F).obj N) :=
  rfl

end pathObj

end Precomp

end CatModule

end DG
