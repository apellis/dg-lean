import DG.Compact.Triangulated
import DG.K0.Triangulated
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Actions of `ℤ` by triangulated autoequivalences and `ℤ[q, q⁻¹]`-modules

Let `𝒯` be a pretriangulated category. A *(weak) action of `ℤ` on `𝒯` by triangulated functors*
(`DG.TriangulatedIntAction 𝒯`) is a family of triangulated functors `⟨n⟩ : 𝒯 ⥤ 𝒯`, `n : ℤ`,
with isomorphisms `⟨0⟩ ≅ 𝟭` and `⟨m + n⟩ ≅ ⟨m⟩ ⋙ ⟨n⟩`. No coherence between these isomorphisms is
required: the constructions below only use isomorphism classes of objects. The motivating
example is the internal shift `⟨1⟩` of the homotopy and derived categories of a dg ring with an
internal grading (`DG.Bigraded.Derived`).

## Main definitions and results

* `DG.TriangulatedIntAction.equivalence n`: each `⟨n⟩` is an autoequivalence of `𝒯`, with
  inverse `⟨-n⟩`.
* `DG.IsCompact.map_equivalence`: an additive equivalence of categories with coproducts
  preserves compact objects; hence `DG.TriangulatedIntAction.isCompact_functor_obj_iff`: `⟨n⟩`
  preserves and reflects compact objects.
* `DG.TriangulatedIntAction.compact`: the restriction of an action to the triangulated
  subcategory `DG.compactSubcategory` of compact objects.
* `DG.TriangulatedIntAction.K0Hom`: the action of the multiplicative group of `ℤ` on the
  Grothendieck group `K₀(𝒯)` (`DG.K0`), `n ↦ [X] ↦ [X⟨n⟩]`, and
  `DG.TriangulatedIntAction.laurentHom : ℤ[q, q⁻¹] →ₐ[ℤ] End(K₀(𝒯))` its extension to the group
  ring `ℤ[q, q⁻¹] = LaurentPolynomial ℤ`.
* `DG.TriangulatedIntAction.K0Module`: the resulting `ℤ[q, q⁻¹]`-module structure on `K₀(𝒯)`,
  with `qⁿ • [X] = [X⟨n⟩]` (`DG.TriangulatedIntAction.T_smul_mk`). It is a definition, not an
  instance, since it depends on the action; it is made an instance for specific categories.
-/

open CategoryTheory Category Limits Pretriangulated

universe w v v' u u'

namespace DG

/-! ### Compact objects and equivalences -/

section Compact

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- An additive equivalence of categories preserves compact objects. -/
theorem IsCompact.map_equivalence [HasCoproducts.{w} C] (e : C ≌ D) [e.functor.Additive]
    {X : C} (hX : IsCompact.{w} X) : IsCompact.{w} (e.functor.obj X) := by
  intro ι _ W _
  let adj : e.functor ⊣ e.inverse := e.toAdjunction
  let W' : ι → C := fun i => e.inverse.obj (W i)
  let sc : ∐ W' ⟶ e.inverse.obj (∐ W) := sigmaComparison e.inverse W
  let Φ : (DirectSum ι fun i => (e.functor.obj X ⟶ W i)) →+ DirectSum ι fun i => (X ⟶ W' i) :=
    DirectSum.map fun i => (adj.homAddEquiv X (W i)).toAddMonoidHom
  let ψ : (e.functor.obj X ⟶ ∐ W) →+ (X ⟶ ∐ W') :=
    (Preadditive.rightComp X (inv sc)).comp (adj.homAddEquiv X (∐ W)).toAddMonoidHom
  have hΦ : Function.Bijective Φ :=
    ⟨(DirectSum.map_injective _).2 fun i => (adj.homAddEquiv X (W i)).injective,
      (DirectSum.map_surjective _).2 fun i => (adj.homAddEquiv X (W i)).surjective⟩
  have hψ : Function.Bijective ψ := by
    change Function.Bijective (fun f => adj.homEquiv X (∐ W) f ≫ inv sc)
    exact ⟨fun f g h => (adj.homEquiv X _).injective ((cancel_mono (inv sc)).1 h),
      fun g => ⟨(adj.homEquiv X _).symm (g ≫ sc), by simp⟩⟩
  have comm : ψ.comp (coproductComparison (e.functor.obj X) W) =
      (coproductComparison X W').comp Φ := by
    ext i g
    simp only [AddMonoidHom.comp_apply, coproductComparison_of, DirectSum.map_of,
      AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Adjunction.homAddEquiv_apply, ψ, Φ]
    change adj.homEquiv X (∐ W) (g ≫ Sigma.ι W i) ≫ inv sc =
      adj.homEquiv X (W i) g ≫ Sigma.ι W' i
    rw [Adjunction.homEquiv_naturality_right, Category.assoc]
    congr 1
    rw [← ι_comp_sigmaComparison, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcomp : ψ ∘ coproductComparison (e.functor.obj X) W = coproductComparison X W' ∘ Φ := by
    rw [← AddMonoidHom.coe_comp, ← AddMonoidHom.coe_comp, comm]
  have : Function.Bijective (ψ ∘ coproductComparison (e.functor.obj X) W) := by
    rw [hcomp]
    exact (hX ι W').comp hΦ
  exact (Function.Bijective.of_comp_iff' hψ _).1 this

/-- An additive equivalence of categories preserves and reflects compact objects. -/
theorem isCompact_equivalence_functor_obj_iff [HasCoproducts.{w} C] [HasCoproducts.{w} D]
    (e : C ≌ D) [e.functor.Additive] (X : C) :
    IsCompact.{w} (e.functor.obj X) ↔ IsCompact.{w} X :=
  haveI : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  ⟨fun h => (IsCompact.map_equivalence e.symm h).of_iso (e.unitIso.app X),
    IsCompact.map_equivalence e⟩

end Compact

/-! ### Actions of `ℤ` by triangulated functors -/

variable (𝒯 : Type u) [Category.{v} 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ] [Preadditive 𝒯]
  [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]

/-- A (weak) action of the group `ℤ` on a pretriangulated category `𝒯` by triangulated
functors: triangulated functors `⟨n⟩ : 𝒯 ⥤ 𝒯` for `n : ℤ`, with isomorphisms `⟨0⟩ ≅ 𝟭` and
`⟨m + n⟩ ≅ ⟨m⟩ ⋙ ⟨n⟩`. No coherence between these isomorphisms is required. Each `⟨n⟩` is an
autoequivalence (`DG.TriangulatedIntAction.equivalence`). -/
structure TriangulatedIntAction where
  /-- The functor `⟨n⟩`. -/
  functor : ℤ → 𝒯 ⥤ 𝒯
  /-- `⟨n⟩` commutes with the shifts. -/
  [commShift : ∀ n, (functor n).CommShift ℤ]
  /-- `⟨n⟩` is a triangulated functor. -/
  [isTriangulated : ∀ n, (functor n).IsTriangulated]
  /-- The isomorphism `⟨0⟩ ≅ 𝟭`. -/
  zeroIso : functor 0 ≅ 𝟭 𝒯
  /-- The isomorphisms `⟨m + n⟩ ≅ ⟨m⟩ ⋙ ⟨n⟩`. -/
  addIso : ∀ m n, functor (m + n) ≅ functor m ⋙ functor n

attribute [instance] TriangulatedIntAction.commShift TriangulatedIntAction.isTriangulated

namespace TriangulatedIntAction

variable {𝒯} (σ : TriangulatedIntAction 𝒯)

/-- `⟨m⟩ ≅ ⟨n⟩` for `m = n`. -/
def isoOfEq {m n : ℤ} (h : m = n) : σ.functor m ≅ σ.functor n :=
  eqToIso (by rw [h])

/-- `⟨n⟩` is an autoequivalence of `𝒯`, with inverse `⟨-n⟩`. -/
noncomputable def equivalence (n : ℤ) : 𝒯 ≌ 𝒯 :=
  CategoryTheory.Equivalence.mk (σ.functor n) (σ.functor (-n))
    (σ.zeroIso.symm ≪≫ σ.isoOfEq (add_neg_cancel n).symm ≪≫ σ.addIso n (-n))
    ((σ.addIso (-n) n).symm ≪≫ σ.isoOfEq (neg_add_cancel n) ≪≫ σ.zeroIso)

@[simp]
theorem equivalence_functor (n : ℤ) : (σ.equivalence n).functor = σ.functor n := rfl

@[simp]
theorem equivalence_inverse (n : ℤ) : (σ.equivalence n).inverse = σ.functor (-n) := rfl

instance (n : ℤ) : (σ.equivalence n).functor.CommShift ℤ := σ.commShift n
instance (n : ℤ) : (σ.equivalence n).functor.IsTriangulated := σ.isTriangulated n
instance (n : ℤ) : (σ.equivalence n).inverse.CommShift ℤ := σ.commShift (-n)
instance (n : ℤ) : (σ.equivalence n).inverse.IsTriangulated := σ.isTriangulated (-n)

instance (n : ℤ) : (σ.functor n).IsEquivalence := (σ.equivalence n).isEquivalence_functor

/-! ### Compact objects -/

section Compact

variable [HasCoproducts.{w} 𝒯]

/-- The functors `⟨n⟩` preserve and reflect compact objects. -/
theorem isCompact_functor_obj_iff (n : ℤ) (X : 𝒯) :
    IsCompact.{w} ((σ.functor n).obj X) ↔ IsCompact.{w} X :=
  isCompact_equivalence_functor_obj_iff (σ.equivalence n) X

/-- The functor `⟨n⟩` restricted to the compact objects. -/
noncomputable def compactFunctor (n : ℤ) :
    (compactSubcategory.{w} 𝒯).FullSubcategory ⥤ (compactSubcategory.{w} 𝒯).FullSubcategory :=
  (compactSubcategory.{w} 𝒯).lift ((compactSubcategory.{w} 𝒯).ι ⋙ σ.functor n)
    (fun X => (σ.isCompact_functor_obj_iff n X.obj).2 X.property)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (n : ℤ) : (σ.compactFunctor.{w} n).CommShift ℤ := by
  unfold compactFunctor
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance (n : ℤ) : (σ.compactFunctor.{w} n).IsTriangulated := by
  unfold compactFunctor
  infer_instance

/-- The restriction of an action by triangulated functors to the triangulated subcategory of
compact objects (`DG.compactSubcategory`). -/
noncomputable def compact : TriangulatedIntAction (compactSubcategory.{w} 𝒯).FullSubcategory where
  functor n := σ.compactFunctor.{w} n
  zeroIso := ((compactSubcategory.{w} 𝒯).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (compactSubcategory.{w} 𝒯).ι σ.zeroIso ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
  addIso m n := ((compactSubcategory.{w} 𝒯).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (compactSubcategory.{w} 𝒯).ι (σ.addIso m n))

@[simp]
theorem compact_functor_obj_obj (n : ℤ) (X : (compactSubcategory.{w} 𝒯).FullSubcategory) :
    ((σ.compact.functor n).obj X).obj = (σ.functor n).obj X.obj := rfl

end Compact

/-! ### The action on `K₀` -/

/-- The action of `ℤ` (written multiplicatively) on the Grothendieck group `K₀(𝒯)`:
`n` acts by `K₀(⟨n⟩)`, `[X] ↦ [X⟨n⟩]`. -/
noncomputable def K0Hom : Multiplicative ℤ →* Module.End ℤ (K0 𝒯) where
  toFun n := (K0.map (σ.functor n.toAdd)).toIntLinearMap
  map_one' := LinearMap.ext fun x => by
    change K0.map (σ.functor 0) x = x
    rw [K0.map_eq_of_iso σ.zeroIso, K0.map_id, AddMonoidHom.id_apply]
  map_mul' m n := LinearMap.ext fun x => by
    change K0.map (σ.functor (m.toAdd + n.toAdd)) x =
      K0.map (σ.functor m.toAdd) (K0.map (σ.functor n.toAdd) x)
    rw [add_comm, K0.map_eq_of_iso (σ.addIso _ _), K0.map_comp_apply]

theorem K0Hom_apply (n : Multiplicative ℤ) (x : K0 𝒯) :
    σ.K0Hom n x = K0.map (σ.functor n.toAdd) x := rfl

/-- The `ℤ`-algebra map `ℤ[q, q⁻¹] → End(K₀(𝒯))` extending `DG.TriangulatedIntAction.K0Hom`,
`qⁿ ↦ K₀(⟨n⟩)`. -/
noncomputable def laurentHom : LaurentPolynomial ℤ →ₐ[ℤ] Module.End ℤ (K0 𝒯) :=
  AddMonoidAlgebra.lift ℤ (Module.End ℤ (K0 𝒯)) ℤ σ.K0Hom

@[simp]
theorem laurentHom_T (n : ℤ) :
    σ.laurentHom (LaurentPolynomial.T n) = σ.K0Hom (Multiplicative.ofAdd n) := by
  rw [laurentHom, LaurentPolynomial.T, AddMonoidAlgebra.lift_single, one_smul]

/-- The `ℤ[q, q⁻¹]`-module structure on `K₀(𝒯)` given by an action of `ℤ` by triangulated
functors: `qⁿ • [X] = [X⟨n⟩]` (`DG.TriangulatedIntAction.T_smul_mk`). -/
noncomputable abbrev K0Module : Module (LaurentPolynomial ℤ) (K0 𝒯) :=
  Module.compHom (K0 𝒯) σ.laurentHom.toRingHom

theorem smul_def (p : LaurentPolynomial ℤ) (x : K0 𝒯) :
    letI := σ.K0Module
    p • x = σ.laurentHom p x := rfl

theorem T_smul (n : ℤ) (x : K0 𝒯) :
    letI := σ.K0Module
    (LaurentPolynomial.T n : LaurentPolynomial ℤ) • x = K0.map (σ.functor n) x := by
  rw [smul_def, laurentHom_T, K0Hom_apply]
  rfl

/-- `qⁿ • [X] = [X⟨n⟩]`. -/
theorem T_smul_mk (n : ℤ) (X : 𝒯) :
    letI := σ.K0Module
    (LaurentPolynomial.T n : LaurentPolynomial ℤ) • K0.mk X = K0.mk ((σ.functor n).obj X) := by
  rw [T_smul, K0.map_mk]

end TriangulatedIntAction

end DG
