import DG.K0.Field

/-!
# Euler characteristics of homological functors

Let `C` be a pretriangulated category, `K` a division ring and `F : C ⥤ ModuleCat K` a
homological functor (`CategoryTheory.Functor.IsHomological`) with a shift sequence
`F.shift n` (`CategoryTheory.Functor.ShiftSequence`; e.g. the tautological one,
`F.shift n = shiftFunctor C n ⋙ F`). Each distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` gives a long
exact sequence `⋯ ⟶ Fⁿ X ⟶ Fⁿ Y ⟶ Fⁿ Z ⟶ Fⁿ⁺¹ X ⟶ ⋯` (Mathlib's
`CategoryTheory.Functor.homologySequence_exact₁`, `₂`, `₃`). This file defines the Euler
characteristic `χ_F(X) = ∑ₙ (-1)ⁿ dim_K Fⁿ(X)` of the objects for which it makes sense and proves
that it is additive on distinguished triangles, hence induces a homomorphism out of `K₀`.

## Main definitions and results

* `DG.Homological.finrankShift F n X = dim_K Fⁿ(X)`.
* `DG.Homological.HasFiniteRank F X`: every `Fⁿ(X)` is finite-dimensional and only finitely
  many are nonzero. These objects are closed under isomorphisms, shifts and extensions
  (`DG.Homological.HasFiniteRank.of_iso`, `.shift`, `.obj₂`).
* `DG.Homological.eulerChar F X = ∑ₙ (-1)ⁿ dim_K Fⁿ(X)` and its additivity
  `DG.Homological.eulerChar_obj₂`.
* `DG.Homological.eulerCharHom F P hP : K₀(P) →+ ℤ` for a triangulated subcategory `P` all of
  whose objects have finite rank.

The division ring is arbitrary (not necessarily commutative): this is used with the
endomorphism ring of a simple object, e.g. for the Hom functors `Hom(L, -)` out of a cell `L`
whose nonzero endomorphisms are invertible (`DG/K0/CellFamily.lean`).
-/

open CategoryTheory Limits Pretriangulated

universe w v' v u

namespace DG

namespace Homological

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
  {K : Type w} [DivisionRing K] (F : C ⥤ ModuleCat.{v'} K) [F.ShiftSequence ℤ]

/-! ### Linear algebra over a division ring -/

/-- For an exact sequence `U → V → W` of vector spaces over a division ring with `V`
finite-dimensional, `dim V = rank f + rank g`. -/
theorem finrank_eq_add_of_exact {U V W : ModuleCat.{v'} K} (f : U ⟶ V) (g : V ⟶ W)
    (h : LinearMap.range f.hom = LinearMap.ker g.hom) [FiniteDimensional K V] :
    Module.finrank K V =
      Module.finrank K (LinearMap.range f.hom) + Module.finrank K (LinearMap.range g.hom) := by
  rw [← LinearMap.finrank_range_add_finrank_ker g.hom, h, add_comm]

/-- The middle term of an exact sequence of vector spaces over a division ring with
finite-dimensional outer terms is finite-dimensional. -/
theorem finiteDimensional_of_exact {U V W : ModuleCat.{v'} K} (f : U ⟶ V) (g : V ⟶ W)
    (h : LinearMap.range f.hom = LinearMap.ker g.hom) [FiniteDimensional K U]
    [FiniteDimensional K W] : FiniteDimensional K V := by
  have h1 : ((⊤ : Submodule K V).map g.hom).FG := IsNoetherian.noetherian _
  have h2 : ((⊤ : Submodule K V) ⊓ LinearMap.ker g.hom).FG := by
    rw [top_inf_eq, ← h, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  exact ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g.hom h1 h2⟩

/-! ### Dimensions -/

/-- The dimension `dim_K Fⁿ(X)`. -/
noncomputable def finrankShift (n : ℤ) (X : C) : ℕ :=
  Module.finrank K ((F.shift n).obj X)

/-- The rank of a linear map between `K`-modules, as a morphism of `ModuleCat K`. -/
noncomputable def rank {U V : ModuleCat.{v'} K} (f : U ⟶ V) : ℕ :=
  Module.finrank K (LinearMap.range f.hom)

theorem rank_le_left {U V : ModuleCat.{v'} K} (f : U ⟶ V) [FiniteDimensional K U] :
    rank f ≤ Module.finrank K U :=
  LinearMap.finrank_range_le _

theorem rank_le_right {U V : ModuleCat.{v'} K} (f : U ⟶ V) [FiniteDimensional K V] :
    rank f ≤ Module.finrank K V :=
  Submodule.finrank_le _

theorem finrankShift_eq_of_iso (n : ℤ) {X Y : C} (e : X ≅ Y) :
    finrankShift F n X = finrankShift F n Y :=
  ((F.shift n).mapIso e).toLinearEquiv.finrank_eq

theorem finrankShift_shift (a n : ℤ) (X : C) :
    finrankShift F n (X⟦a⟧) = finrankShift F (a + n) X :=
  ((F.shiftIso a n (a + n) rfl).app X).toLinearEquiv.finrank_eq

/-- An object has *finite rank* for `F` if every `Fⁿ(X)` is finite-dimensional and only finitely
many of them are nonzero. -/
def HasFiniteRank (X : C) : Prop :=
  (∀ n : ℤ, FiniteDimensional K ((F.shift n).obj X)) ∧
    (Function.support fun n => finrankShift F n X).Finite

/-- The Euler characteristic `χ_F(X) = ∑ₙ (-1)ⁿ dim_K Fⁿ(X)` (meaningful for objects of finite
rank). -/
noncomputable def eulerChar (X : C) : ℤ :=
  ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (finrankShift F n X : ℤ)

theorem eulerChar_eq_of_iso {X Y : C} (e : X ≅ Y) : eulerChar F X = eulerChar F Y := by
  simp only [eulerChar, finrankShift_eq_of_iso F _ e]

/-! ### Closure properties -/

theorem HasFiniteRank.of_iso {X Y : C} (e : X ≅ Y) (hY : HasFiniteRank F Y) :
    HasFiniteRank F X := by
  refine ⟨fun n => ?_, ?_⟩
  · have := hY.1 n
    exact LinearEquiv.finiteDimensional ((F.shift n).mapIso e).toLinearEquiv.symm
  · convert hY.2 using 1
    ext n
    simp [Function.mem_support, finrankShift_eq_of_iso F n e]

theorem HasFiniteRank.shift {X : C} (hX : HasFiniteRank F X) (a : ℤ) :
    HasFiniteRank F (X⟦a⟧) := by
  refine ⟨fun n => ?_, ?_⟩
  · have := hX.1 (a + n)
    exact LinearEquiv.finiteDimensional ((F.shiftIso a n (a + n) rfl).app X).toLinearEquiv.symm
  · refine ((hX.2.image fun n => n - a)).subset fun n hn => ⟨a + n, ?_, by ring⟩
    simpa [Function.mem_support, finrankShift_shift] using hn

variable [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [F.IsHomological]

theorem HasFiniteRank.of_isZero {X : C} (hX : IsZero X) : HasFiniteRank F X := by
  have h : ∀ n : ℤ, Subsingleton ((F.shift n).obj X) := fun n =>
    (ModuleCat.isZero_iff_subsingleton).mp ((F.shift n).map_isZero hX)
  refine ⟨fun n => inferInstance, ?_⟩
  convert Set.finite_empty
  ext n
  simp [finrankShift, Module.finrank_zero_of_subsingleton]

section Triangle

variable {F} (T : Triangle C) (hT : T ∈ distTriang C)
include hT

theorem range_eq_ker₂ (n : ℤ) :
    LinearMap.range ((F.shift n).map T.mor₁).hom = LinearMap.ker ((F.shift n).map T.mor₂).hom :=
  (F.homologySequence_exact₂ T hT n).moduleCat_range_eq_ker

theorem range_eq_ker₃ (n : ℤ) :
    LinearMap.range ((F.shift n).map T.mor₂).hom =
      LinearMap.ker (F.homologySequenceδ T n (n + 1) rfl).hom :=
  (F.homologySequence_exact₃ T hT n (n + 1) rfl).moduleCat_range_eq_ker

theorem range_eq_ker₁ (n : ℤ) :
    LinearMap.range (F.homologySequenceδ T n (n + 1) rfl).hom =
      LinearMap.ker ((F.shift (n + 1)).map T.mor₁).hom :=
  (F.homologySequence_exact₁ T hT n (n + 1) rfl).moduleCat_range_eq_ker

variable (h₁ : ∀ n : ℤ, FiniteDimensional K ((F.shift n).obj T.obj₁))
  (h₃ : ∀ n : ℤ, FiniteDimensional K ((F.shift n).obj T.obj₃))

include h₁ h₃ in
theorem finiteDimensional_obj₂ (n : ℤ) : FiniteDimensional K ((F.shift n).obj T.obj₂) :=
  have := h₁ n
  have := h₃ n
  finiteDimensional_of_exact _ _ (range_eq_ker₂ T hT n)

include h₁ h₃ in
theorem finrankShift_obj₂ (n : ℤ) :
    finrankShift F n T.obj₂ = rank ((F.shift n).map T.mor₁) + rank ((F.shift n).map T.mor₂) :=
  have := finiteDimensional_obj₂ T hT h₁ h₃ n
  finrank_eq_add_of_exact _ _ (range_eq_ker₂ T hT n)

include h₃ in
theorem finrankShift_obj₃ (n : ℤ) :
    finrankShift F n T.obj₃ =
      rank ((F.shift n).map T.mor₂) + rank (F.homologySequenceδ T n (n + 1) rfl) :=
  have := h₃ n
  finrank_eq_add_of_exact _ _ (range_eq_ker₃ T hT n)

include h₁ in
theorem finrankShift_obj₁ (n : ℤ) :
    finrankShift F (n + 1) T.obj₁ =
      rank (F.homologySequenceδ T n (n + 1) rfl) + rank ((F.shift (n + 1)).map T.mor₁) :=
  have := h₁ (n + 1)
  finrank_eq_add_of_exact _ _ (range_eq_ker₁ T hT n)

end Triangle

theorem HasFiniteRank.obj₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : HasFiniteRank F T.obj₁) (h₃ : HasFiniteRank F T.obj₃) : HasFiniteRank F T.obj₂ := by
  refine ⟨fun n => finiteDimensional_obj₂ T hT h₁.1 h₃.1 n,
    (h₁.2.union h₃.2).subset fun n hn => ?_⟩
  by_contra hn'
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn'
  apply hn
  change finrankShift F n T.obj₂ = 0
  have := h₁.1 n
  have := h₃.1 n
  rw [finrankShift_obj₂ T hT h₁.1 h₃.1]
  have ha := rank_le_left ((F.shift n).map T.mor₁)
  have hb := rank_le_right ((F.shift n).map T.mor₂)
  change finrankShift F n T.obj₁ = 0 ∧ finrankShift F n T.obj₃ = 0 at hn'
  unfold finrankShift at hn'
  omega

/-- **Additivity of the Euler characteristic** on distinguished triangles of objects of finite
rank. -/
theorem eulerChar_obj₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : HasFiniteRank F T.obj₁) (h₃ : HasFiniteRank F T.obj₃) :
    eulerChar F T.obj₂ = eulerChar F T.obj₁ + eulerChar F T.obj₃ := by
  refine DerivedCategory.alternating_finsum_of_exact _ _ _
    (fun n => rank ((F.shift n).map T.mor₁)) (fun n => rank ((F.shift n).map T.mor₂))
    (fun n => rank (F.homologySequenceδ T n (n + 1) rfl))
    (h₁.2.subset fun n hn h => hn ?_) (h₃.2.subset fun n hn h => hn ?_)
    (h₃.2.subset fun n hn h => hn ?_) (finrankShift_obj₂ T hT h₁.1 h₃.1)
    (finrankShift_obj₃ T hT h₃.1) (finrankShift_obj₁ T hT h₁.1)
  · have := h₁.1 n
    have := rank_le_left ((F.shift n).map T.mor₁)
    change Module.finrank K _ = 0 at h
    change rank _ = 0
    omega
  · have := h₃.1 n
    have := rank_le_right ((F.shift n).map T.mor₂)
    change Module.finrank K _ = 0 at h
    change rank _ = 0
    omega
  · have := h₃.1 n
    have := rank_le_left (F.homologySequenceδ T n (n + 1) rfl)
    change Module.finrank K _ = 0 at h
    change rank _ = 0
    omega

/-! ### The homomorphism out of `K₀` -/

/-- The Euler characteristic as a homomorphism `K₀(P) →+ ℤ`, for a triangulated subcategory `P`
all of whose objects have finite rank. -/
noncomputable def eulerCharHom (P : ObjectProperty C) [P.IsTriangulated]
    (hP : ∀ X, P X → HasFiniteRank F X) : K0 P.FullSubcategory →+ ℤ :=
  K0.lift (fun X => eulerChar F X.obj) fun T hT =>
    eulerChar_obj₂ F (P.ι.mapTriangle.obj T) (P.ι.map_distinguished T hT)
      (hP _ T.obj₁.property) (hP _ T.obj₃.property)

@[simp]
theorem eulerCharHom_mk (P : ObjectProperty C) [P.IsTriangulated]
    (hP : ∀ X, P X → HasFiniteRank F X) (X : P.FullSubcategory) :
    eulerCharHom F P hP (K0.mk X) = eulerChar F X.obj :=
  K0.lift_mk _ _ X

end Homological

end DG
