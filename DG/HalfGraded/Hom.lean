import DG.HalfGraded.Basic
import DG.Bigraded.K0Map

/-!
# Morphisms of half-graded dg rings

A morphism `f : H → H'` of half-graded dg rings with the same parameter `k`
(`DG.HalfGradedDGRing.Hom`) is a ring homomorphism preserving the `ℤ × ℤ/2`-gradings and
commuting with the differentials. It induces a morphism of the regraded rings
(`DG.HalfGradedDGRing.Hom.regraded`, `a` placed in bidegree `(n, w)` going to `f a` placed in the
same bidegree), which is a morphism of dg rings preserving the weights, hence a dg functor between
the weight dg categories (`DG.HalfGradedDGRing.Hom.weightFunctor : C_H ⥤ C_{H'}`) and, by derived
induction, a `ℤ[q, q⁻¹]`-linear map of Grothendieck groups
`DG.HalfGradedDGRing.Hom.K0Map : K₀(C_H) →ₗ[ℤ[q, q⁻¹]] K₀(C_{H'})` (`qⁿ` acting by the internal
shift `⟨n⟩`; `DG.WeightCategory.K0LinearMap`).

## Main definitions

* `DG.HalfGradedDGRing.Hom H H'`, `DG.HalfGradedDGRing.Hom.id`, `DG.HalfGradedDGRing.Hom.comp`.
* `DG.HalfGradedDGRing.Hom.regraded f : H.Regraded →ᵈᵍ+* H'.Regraded`, with
  `DG.HalfGradedDGRing.Hom.regraded_place` and `regraded_mem_wgrading`.
* `DG.HalfGradedDGRing.Hom.weightFunctor f`, with `weightFunctor_comp` and `weightFunctor_id`.
* `DG.HalfGradedDGRing.Hom.K0Map f`.
-/

open CategoryTheory DirectSum

universe w u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace HalfGradedDGRing

variable {A A' A'' : Type u} [Ring A] [Ring A'] [Ring A''] {k : ℤ}

/-- A morphism of half-graded dg rings: a ring homomorphism preserving the `ℤ × ℤ/2`-gradings and
commuting with the differentials. -/
structure Hom (H : HalfGradedDGRing A k) (H' : HalfGradedDGRing A' k) extends A →+* A' where
  map_mem' : ∀ {p : ℤ × ZMod 2} {a : A}, a ∈ H.hgrading p → toFun a ∈ H'.hgrading p
  map_hd' : ∀ a : A, toFun (H.hd a) = H'.hd (toFun a)

namespace Hom

variable {H : HalfGradedDGRing A k} {H' : HalfGradedDGRing A' k} {H'' : HalfGradedDGRing A'' k}

instance : FunLike (Hom H H') A A' where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨⟨f, _⟩, _⟩, _, _⟩, _, _⟩ := f
    obtain ⟨⟨⟨⟨g, _⟩, _⟩, _, _⟩, _, _⟩ := g
    congr

instance : RingHomClass (Hom H H') A A' where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

theorem toRingHom_apply (f : Hom H H') (a : A) : f.toRingHom a = f a := rfl

theorem map_mem (f : Hom H H') {p : ℤ × ZMod 2} {a : A} (ha : a ∈ H.hgrading p) :
    f a ∈ H'.hgrading p :=
  f.map_mem' ha

theorem map_hd (f : Hom H H') (a : A) : f (H.hd a) = H'.hd (f a) :=
  f.map_hd' a

@[ext]
theorem ext {f g : Hom H H'} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.coe_injective (funext h)

variable (H) in
/-- The identity morphism. -/
def id : Hom H H where
  toRingHom := RingHom.id A
  map_mem' ha := ha
  map_hd' _ := rfl

@[simp] theorem id_apply (a : A) : Hom.id H a = a := rfl

/-- The composite of two morphisms. -/
def comp (g : Hom H' H'') (f : Hom H H') : Hom H H'' where
  toRingHom := g.toRingHom.comp f.toRingHom
  map_mem' ha := g.map_mem (f.map_mem ha)
  map_hd' a := by
    change g (f (H.hd a)) = H''.hd (g (f a))
    rw [f.map_hd, g.map_hd]

@[simp] theorem comp_apply (g : Hom H' H'') (f : Hom H H') (a : A) : g.comp f a = g (f a) := rfl

/-! ### The induced morphism of regraded rings -/

/-- The component `A^{halfDegree k p} → H'.Regraded` of the induced map of regraded rings. -/
def regradedComponent (f : Hom H H') (p : ℤ × ℤ) :
    ↥(halfGrading H.hgrading k p) →+ H'.Regraded where
  toFun a := H'.place p (f a) (f.map_mem a.2)
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact place_zero p
  map_add' a b := by
    simp only [AddMemClass.coe_add, map_add]
    exact place_add p _ _

/-- The morphism of regraded rings induced by a morphism of half-graded dg rings: `a` placed in
bidegree `(n, w)` goes to `f a` placed in bidegree `(n, w)`. -/
def regradedRingHom (f : Hom H H') : H.Regraded →+* H'.Regraded :=
  DirectSum.toSemiring (regradedComponent f)
    (by
      change H'.place 0 (f 1) _ = 1
      rw [one_eq_place]
      exact place_congr rfl (map_one f) _ _)
    (fun {p q} a b => by
      change H'.place (p + q) (f (a * b)) _ = H'.place p (f a) _ * H'.place q (f b) _
      rw [place_mul_place]
      exact place_congr rfl (map_mul f _ _) _ _)

theorem regradedRingHom_place (f : Hom H H') (p : ℤ × ℤ) (a : A)
    (ha : a ∈ H.hgrading (halfDegree k p)) :
    regradedRingHom f (H.place p a ha) = H'.place p (f a) (f.map_mem ha) := by
  change DirectSum.toSemiring (regradedComponent f) _ _
    (DirectSum.of (fun p => ↥(halfGrading H.hgrading k p)) p ⟨a, ha⟩) = _
  rw [DirectSum.toSemiring_of]
  rfl

theorem regradedRingHom_mem_grading (f : Hom H H') {n : ℤ} {x : H.Regraded}
    (hx : x ∈ grading n) : regradedRingHom f x ∈ grading (M := H'.Regraded) n := by
  refine grading_induction (P := fun x => regradedRingHom f x ∈ grading n) ?_ (fun w a ha => ?_)
    (fun x y hx hy => ?_) hx
  · rw [map_zero]; exact zero_mem _
  · rw [regradedRingHom_place]; exact place_mem_grading (H := H') (n, w) _
  · rw [map_add]; exact add_mem hx hy

theorem regradedRingHom_d (f : Hom H H') (x : H.Regraded) :
    regradedRingHom f (d x) = d (regradedRingHom f x) := by
  induction x using induction_on with
  | zero => simp only [map_zero]
  | mk p a ha =>
    rw [d_place, regradedRingHom_place, regradedRingHom_place, d_place]
    exact place_congr rfl (f.map_hd a) _ _
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

/-- The morphism of regraded rings induced by a morphism of half-graded dg rings, as a morphism of
dg rings. -/
def regraded (f : Hom H H') : H.Regraded →ᵈᵍ+* H'.Regraded where
  toRingHom := regradedRingHom f
  map_mem' := regradedRingHom_mem_grading f
  map_d' := regradedRingHom_d f

theorem regraded_apply (f : Hom H H') (x : H.Regraded) : f.regraded x = regradedRingHom f x :=
  rfl

theorem regraded_place (f : Hom H H') (p : ℤ × ℤ) (a : A)
    (ha : a ∈ H.hgrading (halfDegree k p)) :
    f.regraded (H.place p a ha) = H'.place p (f a) (f.map_mem ha) :=
  regradedRingHom_place f p a ha

/-- The induced morphism of regraded rings preserves the weights. -/
theorem regraded_mem_wgrading (f : Hom H H') {w : ℤ} {x : H.Regraded}
    (hx : x ∈ wgrading w) : f.regraded x ∈ wgrading (M := H'.Regraded) w := by
  refine wgrading_induction (P := fun x => f.regraded x ∈ wgrading w) ?_ (fun n a ha => ?_)
    (fun x y hx hy => ?_) hx
  · rw [map_zero]; exact zero_mem _
  · rw [regraded_place]; exact place_mem_wgrading (H := H') (n, w) _
  · rw [map_add]; exact add_mem hx hy

theorem regraded_comp (g : Hom H' H'') (f : Hom H H') (x : H.Regraded) :
    (g.comp f).regraded x = g.regraded (f.regraded x) := by
  induction x using induction_on with
  | zero => simp only [map_zero]
  | mk p a ha => rw [regraded_place, regraded_place, regraded_place]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem regraded_id (x : H.Regraded) : (Hom.id H).regraded x = x := by
  induction x using induction_on with
  | zero => simp only [map_zero]
  | mk p a ha => rw [regraded_place]; rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-! ### The induced dg functor and the map on `K₀` -/

/-- The dg functor `C_H ⥤ C_{H'}` between the weight dg categories induced by a morphism of
half-graded dg rings: the identity on objects. -/
abbrev weightFunctor (f : Hom H H') :
    WeightCategory H.Regraded ⥤ WeightCategory H'.Regraded :=
  WeightCategory.mapFunctor f.regraded f.regraded_mem_wgrading

theorem weightFunctor_comp (g : Hom H' H'') (f : Hom H H') :
    (g.comp f).weightFunctor = f.weightFunctor ⋙ g.weightFunctor :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ φ => by
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact WeightCategory.hom_ext (regraded_comp g f φ.1)

theorem weightFunctor_id : (Hom.id H).weightFunctor = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ φ => by
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact WeightCategory.hom_ext (regraded_id φ.1)

variable [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory H.Regraded)]
  [CatModule.HasDerivedCategory.{max u w, max u w} (WeightCategory H'.Regraded)]

/-- The `ℤ[q, q⁻¹]`-linear map `K₀(C_H) → K₀(C_{H'})` induced by a morphism of half-graded dg
rings (derived induction along `C_H ⥤ C_{H'}`; `qⁿ` acts by the internal shift `⟨n⟩`). -/
def K0Map (f : Hom H H') :
    DGCategory.K0.{max u w, max u w} (WeightCategory H.Regraded) →ₗ[LaurentPolynomial ℤ]
      DGCategory.K0.{max u w, max u w} (WeightCategory H'.Regraded) :=
  WeightCategory.K0LinearMap f.regraded f.regraded_mem_wgrading

theorem K0Map_apply (f : Hom H H')
    (x : DGCategory.K0.{max u w, max u w} (WeightCategory H.Regraded)) :
    f.K0Map x = DGCategory.K0.map.{max u w, max u w} f.weightFunctor x :=
  rfl

end Hom

end HalfGradedDGRing

end DG
