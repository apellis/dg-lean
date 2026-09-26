import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Closed.Monoidal

/-!
# The monoidal category of cochain complexes of modules

Mathlib's `Mathlib/Algebra/Homology/Monoidal.lean` equips `HomologicalComplex C c` with a
monoidal structure when `c.TensorSigns` and `C` is a monoidal preadditive category in which the
relevant coproducts exist and are preserved by tensoring on either side. For
`C = ModuleCat.{u} R` over a commutative ring `R : Type u` and `c = ComplexShape.up ℤ`, two
instances needed for this are not found by Mathlib at the pinned revision:

* `(curriedTensor C).Additive` (tensoring on the right is additive in the left variable), which
  holds for any monoidal preadditive category
  (`CategoryTheory.MonoidalPreadditive.curriedTensor_additive`);
* the preservation of (small) colimits by `X ⊗ -` and `- ⊗ X` in `ModuleCat R`, which follows
  from the monoidal closed structure (`X ⊗ -` is a left adjoint) and the symmetry
  (`DG.ModuleCat.preservesColimits_curriedTensor_obj`,
  `DG.ModuleCat.preservesColimits_curriedTensor_flip_obj`).

With these, `CochainComplex (ModuleCat.{u} R) ℤ` is a monoidal category. This file then gives an
element-level description of its tensor product, in the namespace `DG.ComplexTensor`:

* `tmul K L h x y : (K ⊗ L).X n` for `x : K.X p`, `y : L.X q` and `h : p + q = n`, the image of
  `x ⊗ₜ y` under the inclusion of the summand `Kᵖ ⊗ Lᑫ`; it is bilinear, and two maps out of
  `(K ⊗ L).X n` agreeing on these elements are equal (`hom_ext`, and `hom_ext₃` for
  `(K ⊗ L) ⊗ M`);
* the differential: `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` (`d_tmul`). This is the sign
  convention of the library (`docs/CONVENTIONS.md`): Mathlib's total complex uses the signs
  `ComplexShape.ε₁ = 1` and `ComplexShape.ε₂ (p, q) = (ComplexShape.up ℤ).ε p = (-1)^p`;
* tensor products of morphisms, the associator and the unitors on these elements
  (`tensorHom_f_tmul`, `associator_hom_f_tmul`, `leftUnitor_hom_f_tmul`, ...), in terms of the
  generator `unitOne R` of the degree-`0` part of the unit complex;
* `tensorDesc`: a morphism of complexes `K ⊗ L ⟶ M` from a family of bilinear maps
  `Kᵖ × Lᑫ → Mᵖ⁺ᑫ` satisfying the Leibniz rule `d (f x y) = f (d x) y + (-1)^p f x (d y)`.
-/

open CategoryTheory MonoidalCategory Limits HomologicalComplex

universe u

/-- In a monoidal preadditive category, the tensor product is additive in its first
variable, as a functor to the (preadditive) category of functors. -/
instance CategoryTheory.MonoidalPreadditive.curriedTensor_additive {D : Type*} [Category D]
    [Preadditive D] [MonoidalCategory D] [MonoidalPreadditive D] :
    (curriedTensor D).Additive where
  map_add {X Y f g} := by ext Z; simp

namespace DG

variable {R : Type u} [CommRing R]

/-- Tensoring on the left with a module preserves colimits (it is a left adjoint). -/
noncomputable instance ModuleCat.preservesColimits_curriedTensor_obj (X : ModuleCat.{u} R) :
    PreservesColimitsOfSize.{0, 0} ((curriedTensor (ModuleCat.{u} R)).obj X) :=
  inferInstanceAs (PreservesColimitsOfSize.{0, 0} (tensorLeft X))

/-- Tensoring on the right with a module preserves colimits. -/
noncomputable instance ModuleCat.preservesColimits_curriedTensor_flip_obj
    (X : ModuleCat.{u} R) :
    PreservesColimitsOfSize.{0, 0} ((curriedTensor (ModuleCat.{u} R)).flip.obj X) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- Cochain complexes of `R`-modules form a monoidal category (Mathlib's
`HomologicalComplex.monoidalCategory`, whose hypotheses are met thanks to the instances
above). -/
noncomputable example : MonoidalCategory (CochainComplex (ModuleCat.{u} R) ℤ) := inferInstance

namespace ComplexTensor

variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The element `x ⊗ y` of `(K ⊗ L)ⁿ`, for `x ∈ Kᵖ`, `y ∈ Lᑫ` and `p + q = n`. -/
noncomputable def tmul {p q n : ℤ} (h : p + q = n) (x : K.X p) (y : L.X q) : (K ⊗ L).X n :=
  (ιTensorObj K L p q n h).hom (x ⊗ₜ y)

variable {K L}

@[simp]
theorem tmul_add_left {p q n : ℤ} (h : p + q = n) (x x' : K.X p) (y : L.X q) :
    tmul K L h (x + x') y = tmul K L h x y + tmul K L h x' y := by
  simp [tmul, TensorProduct.add_tmul]

@[simp]
theorem tmul_add_right {p q n : ℤ} (h : p + q = n) (x : K.X p) (y y' : L.X q) :
    tmul K L h x (y + y') = tmul K L h x y + tmul K L h x y' := by
  simp [tmul, TensorProduct.tmul_add]

@[simp]
theorem tmul_smul_left {p q n : ℤ} (h : p + q = n) (r : R) (x : K.X p) (y : L.X q) :
    tmul K L h (r • x) y = r • tmul K L h x y := by
  rw [tmul, tmul, ← TensorProduct.smul_tmul', map_smul]

@[simp]
theorem tmul_smul_right {p q n : ℤ} (h : p + q = n) (r : R) (x : K.X p) (y : L.X q) :
    tmul K L h x (r • y) = r • tmul K L h x y := by
  simp [tmul, TensorProduct.tmul_smul]

@[simp]
theorem tmul_zero_left {p q n : ℤ} (h : p + q = n) (y : L.X q) :
    tmul K L h (0 : K.X p) y = 0 := by
  simp [tmul]

@[simp]
theorem tmul_zero_right {p q n : ℤ} (h : p + q = n) (x : K.X p) :
    tmul K L h x (0 : L.X q) = 0 := by
  simp [tmul]

@[simp]
theorem tmul_units_smul_left {p q n : ℤ} (h : p + q = n) (e : ℤˣ) (x : K.X p) (y : L.X q) :
    tmul K L h (e • x) y = e • tmul K L h x y := by
  rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R, tmul_smul_left,
    Int.cast_smul_eq_zsmul]

@[simp]
theorem tmul_units_smul_right {p q n : ℤ} (h : p + q = n) (e : ℤˣ) (x : K.X p) (y : L.X q) :
    tmul K L h x (e • y) = e • tmul K L h x y := by
  rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul R, tmul_smul_right,
    Int.cast_smul_eq_zsmul]

/-- Two maps out of `(K ⊗ L)ⁿ` agreeing on the elements `x ⊗ y` are equal. -/
theorem hom_ext {M : ModuleCat.{u} R} {n : ℤ} {f g : (K ⊗ L).X n ⟶ M}
    (hfg : ∀ (p q : ℤ) (h : p + q = n) (x : K.X p) (y : L.X q),
      f (tmul K L h x y) = g (tmul K L h x y)) : f = g := by
  apply mapBifunctor.hom_ext
  intro p q h
  exact ModuleCat.MonoidalCategory.tensor_ext fun x y => hfg p q h x y

/-- The differential of the tensor product of complexes:
`d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y` for `x ∈ Kᵖ`. -/
theorem d_tmul {p q n : ℤ} (h : p + q = n) (x : K.X p) (y : L.X q) :
    (K ⊗ L).d n (n + 1) (tmul K L h x y) =
      tmul K L (show p + 1 + q = n + 1 by omega) (K.d p (p + 1) x) y +
        p.negOnePow • tmul K L (show p + (q + 1) = n + 1 by omega) x (L.d q (q + 1) y) := by
  have h1 : ιTensorObj K L p q n h ≫ (K ⊗ L).d n (n + 1) =
      (K.d p (p + 1) ▷ L.X q) ≫ ιTensorObj K L (p + 1) q (n + 1) (by omega) +
        p.negOnePow • ((K.X p ◁ L.d q (q + 1)) ≫ ιTensorObj K L p (q + 1) (n + 1) (by omega)) := by
    change ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorObj K L).d n (n + 1) = _
    rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) _ _
        (by dsimp; omega),
      mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) _
        (by dsimp; omega)]
    simp
  have h2 := congrArg (fun f => f.hom (x ⊗ₜ y)) h1
  simpa [tmul] using h2


variable {K' L' M : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The tensor product of morphisms sends `x ⊗ y` to `f x ⊗ g y`. -/
theorem tensorHom_f_tmul (f : K ⟶ K') (g : L ⟶ L') {p q n : ℤ} (h : p + q = n) (x : K.X p)
    (y : L.X q) : (f ⊗ g).f n (tmul K L h x y) = tmul K' L' h (f.f p x) (g.f q y) := by
  have e := congrArg (fun φ => φ.hom (x ⊗ₜ y))
    (ι_mapBifunctorMap f g (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) p q n h)
  exact e

theorem whiskerRight_f_tmul (f : K ⟶ K') {p q n : ℤ} (h : p + q = n) (x : K.X p)
    (y : L.X q) : (f ▷ L).f n (tmul K L h x y) = tmul K' L h (f.f p x) y :=
  tensorHom_f_tmul f (𝟙 L) h x y

theorem whiskerLeft_f_tmul (g : L ⟶ L') {p q n : ℤ} (h : p + q = n) (x : K.X p)
    (y : L.X q) : (K ◁ g).f n (tmul K L h x y) = tmul K L' h x (g.f q y) :=
  tensorHom_f_tmul (𝟙 K) g h x y

/-- The associator of complexes sends `(x ⊗ y) ⊗ z` to `x ⊗ (y ⊗ z)`. -/
theorem associator_hom_f_tmul {p q r pq n : ℤ} (hpq : p + q = pq) (h : pq + r = n) (x : K.X p)
    (y : L.X q) (z : M.X r) :
    (α_ K L M).hom.f n (tmul (K ⊗ L) M h (tmul K L hpq x y) z) =
      tmul K (L ⊗ M) (show p + (q + r) = n by omega) x (tmul L M rfl y z) := by
  have e1 := mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{u} R)) (curriedTensor _) K L M
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r pq n hpq h
  have e2 := ι_mapBifunctorAssociatorX_hom (curriedAssociatorNatIso (ModuleCat.{u} R)) K L M
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r n
    (by dsimp [ComplexShape.r]; omega)
  have e3 := mapBifunctor₂₃.ι_eq (curriedTensor (ModuleCat.{u} R)) (curriedTensor _) K L M
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r (q + r) n rfl
    (by dsimp; omega)
  have f1 := congrArg (fun φ => φ.hom (x ⊗ₜ y ⊗ₜ z)) e1
  have f2 := congrArg (fun φ => φ.hom (x ⊗ₜ y ⊗ₜ z)) e2
  have f3 := congrArg (fun φ => φ.hom (x ⊗ₜ (y ⊗ₜ z))) e3
  dsimp at f1 f2 f3
  refine Eq.trans ?_ (f2.trans f3)
  rw [f1]
  rfl

/-- Two maps out of `((K ⊗ L) ⊗ M)ⁿ` agreeing on the elements `(x ⊗ y) ⊗ z` are equal. -/
theorem hom_ext₃ {N : ModuleCat.{u} R} {n : ℤ} {f g : ((K ⊗ L) ⊗ M).X n ⟶ N}
    (hfg : ∀ (p q r : ℤ) (h : p + q + r = n) (x : K.X p) (y : L.X q) (z : M.X r),
      f (tmul (K ⊗ L) M h (tmul K L rfl x y) z) = g (tmul (K ⊗ L) M h (tmul K L rfl x y) z)) :
    f = g := by
  refine mapBifunctor₁₂.hom_ext (F₁₂ := curriedTensor (ModuleCat.{u} R))
    (G := curriedTensor (ModuleCat.{u} R)) (c₁₂ := ComplexShape.up ℤ) ?_
  intro p q r h
  rw [mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ p q r (p + q) n rfl h]
  refine ModuleCat.MonoidalCategory.tensor_ext₃' fun x y z => ?_
  exact hfg p q r h x y z

/-- The map `(K ⊗ L)ⁿ ⟶ N` induced by a family of bilinear maps `Kᵖ × Lᑫ → N`
(`p + q = n`). -/
noncomputable def descX {N : ModuleCat.{u} R} {n : ℤ}
    (f : ∀ (p q : ℤ), p + q = n → K.X p →ₗ[R] L.X q →ₗ[R] N) : (K ⊗ L).X n ⟶ N :=
  mapBifunctorDesc (fun p q h => ModuleCat.ofHom (TensorProduct.lift (f p q h)))

@[simp]
theorem descX_tmul {N : ModuleCat.{u} R} {n : ℤ}
    (f : ∀ (p q : ℤ), p + q = n → K.X p →ₗ[R] L.X q →ₗ[R] N) {p q : ℤ} (h : p + q = n)
    (x : K.X p) (y : L.X q) : descX f (tmul K L h x y) = f p q h x y :=
  congrArg (fun φ => φ.hom (x ⊗ₜ y))
    (ι_mapBifunctorDesc (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ)
      (fun p q h => ModuleCat.ofHom (TensorProduct.lift (f p q h))) p q h)

variable (K L M) in
/-- A morphism of complexes `K ⊗ L ⟶ M` from a family of bilinear maps `Kᵖ × Lᑫ → Mⁿ`
(`p + q = n`) satisfying the Leibniz rule
`d (f x y) = f (d x) y + (-1)^p f x (d y)`. -/
noncomputable def tensorDesc (f : ∀ (p q n : ℤ), p + q = n → K.X p →ₗ[R] L.X q →ₗ[R] M.X n)
    (hf : ∀ (p q n : ℤ) (h : p + q = n) (x : K.X p) (y : L.X q),
      M.d n (n + 1) (f p q n h x y) =
        f (p + 1) q (n + 1) (by omega) (K.d p (p + 1) x) y +
          p.negOnePow • f p (q + 1) (n + 1) (by omega) x (L.d q (q + 1) y)) :
    K ⊗ L ⟶ M where
  f n := descX (f · · n)
  comm' := by
    rintro n _ rfl
    apply hom_ext
    intro p q h x y
    simp only [ModuleCat.comp_apply, descX_tmul, d_tmul, map_add, hf, Units.smul_def,
      map_zsmul]

@[simp]
theorem tensorDesc_f_tmul (f : ∀ (p q n : ℤ), p + q = n → K.X p →ₗ[R] L.X q →ₗ[R] M.X n)
    (hf : ∀ (p q n : ℤ) (h : p + q = n) (x : K.X p) (y : L.X q),
      M.d n (n + 1) (f p q n h x y) =
        f (p + 1) q (n + 1) (by omega) (K.d p (p + 1) x) y +
          p.negOnePow • f p (q + 1) (n + 1) (by omega) x (L.d q (q + 1) y))
    {p q n : ℤ} (h : p + q = n) (x : K.X p) (y : L.X q) :
    (tensorDesc K L M f hf).f n (tmul K L h x y) = f p q n h x y :=
  descX_tmul (fun p q h => f p q n h) h x y

/-! ### The unit -/

variable (R) in
/-- The element `1` of the degree-`0` part of the unit complex. -/
noncomputable def unitOne : (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).X 0 :=
  (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv (1 : R)

/-- Every element of a zero module is zero. -/
theorem eq_zero_of_isZero {X : ModuleCat.{u} R} (hX : IsZero X) (x : X) : x = 0 := by
  have := congrArg (fun φ : X ⟶ X => φ x) (hX.eq_of_src (𝟙 X) 0)
  simpa using this

/-- The unit complex vanishes outside degree `0`. -/
theorem unit_X_eq_zero {p : ℤ} (hp : p ≠ 0) (u : (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).X p) :
    u = 0 :=
  eq_zero_of_isZero (isZero_single_obj_X (ComplexShape.up ℤ) 0 _ p hp) u

/-- The degree-`0` part of the unit complex is free on `unitOne R`. -/
theorem unit_X_zero_eq (u : (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).X 0) :
    u = ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).hom u : R) •
      unitOne R := by
  set e := singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))
  have h1 : u = e.inv (e.hom u) := (Iso.hom_inv_id_apply e u).symm
  have h2 : (e.hom u : R) = (e.hom u : R) • (1 : R) := by rw [smul_eq_mul, mul_one]
  rw [unitOne]
  conv_lhs => rw [h1, h2]
  exact map_smul e.inv.hom _ _

theorem leftUnitor_inv_f_apply (n : ℤ) (x : K.X n) :
    (λ_ K).inv.f n x = tmul _ K (zero_add n) (unitOne R) x := by
  have e := congrArg (fun φ => φ.hom x) (leftUnitor'_inv K n)
  exact e

/-- The left unitor sends `1 ⊗ x` to `x`. -/
theorem leftUnitor_hom_f_tmul (n : ℤ) (x : K.X n) :
    (λ_ K).hom.f n (tmul _ K (zero_add n) (unitOne R) x) = x := by
  rw [← leftUnitor_inv_f_apply, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    Iso.inv_hom_id, HomologicalComplex.id_f, ModuleCat.id_apply]

theorem rightUnitor_inv_f_apply (n : ℤ) (x : K.X n) :
    (ρ_ K).inv.f n x = tmul K _ (add_zero n) x (unitOne R) := by
  have e := congrArg (fun φ => φ.hom x) (rightUnitor'_inv K n)
  exact e

/-- The right unitor sends `x ⊗ 1` to `x`. -/
theorem rightUnitor_hom_f_tmul (n : ℤ) (x : K.X n) :
    (ρ_ K).hom.f n (tmul K _ (add_zero n) x (unitOne R)) = x := by
  rw [← rightUnitor_inv_f_apply, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    Iso.inv_hom_id, HomologicalComplex.id_f, ModuleCat.id_apply]

/-- Two maps out of `(𝟙_ ⊗ K)ⁿ` agreeing on the elements `1 ⊗ x` are equal. -/
theorem unit_tensor_hom_ext {N : ModuleCat.{u} R} {n : ℤ}
    {f g : (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ⊗ K).X n ⟶ N}
    (hfg : ∀ x : K.X n, f (tmul _ K (zero_add n) (unitOne R) x) =
      g (tmul _ K (zero_add n) (unitOne R) x)) : f = g := by
  refine hom_ext fun p q h u x => ?_
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = n := by omega
    rw [unit_X_zero_eq u, tmul_smul_left, map_smul, map_smul, hfg]
  · rw [unit_X_eq_zero hp u, tmul_zero_left, map_zero, map_zero]

/-- Two maps out of `(K ⊗ 𝟙_)ⁿ` agreeing on the elements `x ⊗ 1` are equal. -/
theorem tensor_unit_hom_ext {N : ModuleCat.{u} R} {n : ℤ}
    {f g : (K ⊗ 𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).X n ⟶ N}
    (hfg : ∀ x : K.X n, f (tmul K _ (add_zero n) x (unitOne R)) =
      g (tmul K _ (add_zero n) x (unitOne R))) : f = g := by
  refine hom_ext fun p q h x u => ?_
  by_cases hq : q = 0
  · subst hq
    obtain rfl : p = n := by omega
    rw [unit_X_zero_eq u, tmul_smul_right, map_smul, map_smul, hfg]
  · rw [unit_X_eq_zero hq u, tmul_zero_right, map_zero, map_zero]

/-- Two morphisms out of the unit complex agreeing on `unitOne R` are equal. -/
theorem unit_hom_ext {f g : 𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ K}
    (h : f.f 0 (unitOne R) = g.f 0 (unitOne R)) : f = g := by
  refine from_single_hom_ext (ModuleCat.hom_ext (LinearMap.ext fun u => ?_))
  rw [unit_X_zero_eq u, map_smul, map_smul]
  exact congrArg _ h

end ComplexTensor

/-- A morphism of cochain complexes commutes with the differentials, elementwise. -/
theorem _root_.HomologicalComplex.Hom.comm_apply {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : K ⟶ L) (n : ℤ) (x : K.X n) : φ.f (n + 1) (K.d n (n + 1) x) = L.d n (n + 1) (φ.f n x) := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.comm]

end DG
