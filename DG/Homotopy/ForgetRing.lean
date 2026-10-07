import DG.Homotopy.Comparison

/-!
# The underlying complex of a dg module over a ring in degree `0`

Let `S` be a ring, not necessarily commutative, regarded as a dg ring concentrated in degree `0`
(the scoped instances of `DG.DegreeZero`). For a dg module `M` over `S`, the homogeneous
components `Mⁿ` are `S`-submodules and the differential is `S`-linear, so `M` has an underlying
cochain complex of `S`-modules. (For a commutative ring this is `DG.DGModuleCat.forget S S`,
which uses `S` as a ground ring; for a non-commutative ring the action of `S` itself has to be
used.) This file constructs the functor

  `DG.DegreeZero.complexFunctor S : DGModuleCat S ⥤ CochainComplex (ModuleCat S) ℤ`

and shows, as for `DG.DGModuleCat.forget`, that it is faithful, commutes with the shifts, sends
homotopies to homotopies and mapping cones to Mathlib's mapping cones, so that the induced
functor on homotopy categories `DG.DegreeZero.homotopyFunctor S` is triangulated.

## Main definitions and results

* `DG.DegreeZero.gradingSubmodule S M n`: `Mⁿ` as an `S`-submodule; `DG.DegreeZero.toComplex`.
* `DG.DegreeZero.complexFunctor S`, faithful (`DG.DegreeZero.complexFunctor_faithful`), with
  `DG.DegreeZero.complexFunctorCommShift`.
* `DG.DegreeZero.toHomComplex`: cochains of `HOM_S(M, N)` as cochains of Mathlib's Hom complex,
  compatible with sums, composition, morphisms and differentials; `DG.DegreeZero.toHomotopy`.
* `DG.DegreeZero.coneIso φ`, `DG.DegreeZero.coneTriangleIso φ`: the underlying complex of the
  mapping cone is Mathlib's mapping cone, compatibly with the standard triangles.
* `DG.DegreeZero.homotopyFunctor S`, with `DG.DegreeZero.homotopyFunctor_isTriangulated`.
-/

open CategoryTheory Category Limits Pretriangulated

universe v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace DegreeZero

variable {S : Type u} [Ring S]

/-! ### The homogeneous components as `S`-modules -/

section Module

variable {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module S M] [DGModule S M]

/-- The elements of `S` have degree `0`. -/
theorem mem_grading_zero (s : S) : s ∈ grading (M := S) 0 :=
  mem_grading_iff.mpr (Or.inl rfl)

/-- The action of `S` preserves the homogeneous components of a dg module. -/
theorem ring_smul_mem (s : S) {n : ℤ} {m : M} (hm : m ∈ grading n) : s • m ∈ grading n := by
  simpa using smul_mem_grading (mem_grading_zero s) hm

/-- The differential of a dg module over `S` is `S`-linear. -/
theorem d_ring_smul (s : S) (m : M) : d (s • m) = s • d m := by
  rw [d_smul_of_mem_zero (mem_grading_zero s), d_apply, zero_smul, zero_add]

variable (S M) in
/-- The homogeneous component `Mⁿ` of a dg module over `S`, as an `S`-submodule. -/
def gradingSubmodule (n : ℤ) : Submodule S M where
  __ := grading (M := M) n
  smul_mem' s _ hm := ring_smul_mem s hm

@[simp]
theorem mem_gradingSubmodule {n : ℤ} {m : M} : m ∈ gradingSubmodule S M n ↔ m ∈ grading n :=
  Iff.rfl

variable (S M) in
/-- The differential of a dg module over `S` as an `S`-linear map. -/
def dLinear : M →ₗ[S] M where
  __ := (d : M →+ M)
  map_smul' := d_ring_smul

@[simp]
theorem dLinear_apply (m : M) : dLinear S M m = d m := rfl

end Module

/-! ### The underlying cochain complex -/

section Object

variable (S) (M : DGModuleCat.{v} S)

/-- The differential `Mⁿ → Mⁿ⁺¹` as an `S`-linear map. -/
def dRestrict (n : ℤ) : gradingSubmodule S M n →ₗ[S] gradingSubmodule S M (n + 1) :=
  (dLinear S M).restrict fun _ hm => d_mem hm

/-- The underlying cochain complex of `S`-modules of a dg module over `S`. -/
def toComplex : CochainComplex (ModuleCat.{v} S) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of S (gradingSubmodule S M n))
    (fun n => ModuleCat.ofHom (dRestrict S M n)) fun n => by
      ext m
      exact d_d (m : M)

@[simp]
theorem toComplex_X (n : ℤ) :
    (toComplex S M).X n = ModuleCat.of S (gradingSubmodule S M n) := rfl

theorem toComplex_d (n : ℤ) :
    (toComplex S M).d n (n + 1) = ModuleCat.ofHom (dRestrict S M n) :=
  CochainComplex.of_d (fun n => ModuleCat.of S (gradingSubmodule S M n))
    (fun n => ModuleCat.ofHom (dRestrict S M n)) n

variable {S}

theorem toComplex_d_apply {i j : ℤ} (h : i + 1 = j) (x : gradingSubmodule S M i) :
    (((toComplex S M).d i j).hom x).1 = d (x : M) := by
  subst h
  rw [toComplex_d]
  rfl

theorem toComplex_XIsoOfEq_hom_apply {i j : ℤ} (h : i = j) (x : gradingSubmodule S M i) :
    (((toComplex S M).XIsoOfEq h).hom.hom x).1 = x := by
  subst h
  rfl

theorem toComplex_XIsoOfEq_inv_apply {i j : ℤ} (h : i = j) (x : gradingSubmodule S M j) :
    (((toComplex S M).XIsoOfEq h).inv.hom x).1 = x := by
  subst h
  rfl

end Object

section Morphism

variable {M N : DGModuleCat.{v} S}

/-- A morphism of dg modules restricted to the homogeneous components of degree `n`. -/
def homRestrict (f : M ⟶ N) (n : ℤ) : gradingSubmodule S M n →ₗ[S] gradingSubmodule S N n :=
  f.hom.toLinearMap.restrict fun _ hm => f.hom.map_mem hm

@[simp]
theorem coe_homRestrict_apply (f : M ⟶ N) (n : ℤ) (m : gradingSubmodule S M n) :
    (homRestrict f n m : N) = f m := rfl

/-- The morphism of cochain complexes underlying a morphism of dg modules. -/
def toComplexMap (f : M ⟶ N) : toComplex S M ⟶ toComplex S N :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (homRestrict f n)) fun n => by
    rw [toComplex_d, toComplex_d]
    ext m
    exact Subtype.ext (f.hom.map_d m.1).symm

@[simp]
theorem toComplexMap_f (f : M ⟶ N) (n : ℤ) :
    (toComplexMap f).f n = ModuleCat.ofHom (homRestrict f n) := rfl

variable (S) in
/-- The functor from dg modules over a ring `S` in degree `0` to cochain complexes of
`S`-modules. -/
@[simps]
def complexFunctor : DGModuleCat.{v} S ⥤ CochainComplex (ModuleCat.{v} S) ℤ where
  obj M := toComplex S M
  map f := toComplexMap f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance complexFunctor_additive : (complexFunctor.{v} S).Additive where
  map_add := by intros; ext; rfl

theorem complexFunctor_map_f_apply (f : M ⟶ N) (i : ℤ) (x : gradingSubmodule S M i) :
    ((((complexFunctor S).map f).f i).hom x).1 = f x.1 := rfl

theorem complexFunctor_obj_d_apply (M : DGModuleCat.{v} S) {i j : ℤ} (h : i + 1 = j)
    (x : gradingSubmodule S M i) :
    ((((complexFunctor S).obj M).d i j).hom x).1 = d (x : M) :=
  toComplex_d_apply M h x

theorem complexFunctor_map_injective {f g : M ⟶ N}
    (h : (complexFunctor S).map f = (complexFunctor S).map g) : f = g := by
  refine DGModuleCat.hom_ext_apply fun m => ?_
  induction m using DG.induction_on with
  | h_zero => rw [map_zero, map_zero]
  | @h_homogeneous n m =>
    have h1 : homRestrict f n = homRestrict g n :=
      congrArg (fun φ : toComplex S M ⟶ toComplex S N => ModuleCat.Hom.hom (φ.f n)) h
    exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨m, m.2⟩)
  | h_add m m' hm hm' => rw [map_add, map_add, hm, hm']

/-- The functor to cochain complexes is faithful. -/
instance complexFunctor_faithful : (complexFunctor.{v} S).Faithful where
  map_injective h := complexFunctor_map_injective h

end Morphism

/-! ### Shifts -/

section Shift

open Shift

/-- The homogeneous component `(M⟦n⟧)ⁱ = Mⁱ⁺ⁿ`, as an `S`-linear equivalence. -/
def shiftGradingLinearEquiv (M : DGModuleCat.{v} S) (n i : ℤ) :
    gradingSubmodule S ((shiftFunctor (DGModuleCat.{v} S) n).obj M) i ≃ₗ[S]
      gradingSubmodule S M (i + n) where
  toFun x := ⟨unmk n x.1, x.2⟩
  invFun y := ⟨Shift.mk n y.1, y.2⟩
  map_add' _ _ := rfl
  map_smul' s x := Subtype.ext (by
    have h := unmk_smul (n := n) (M := M) (mem_grading_zero s) x.1
    rw [mul_zero, koszulSign_zero, one_smul] at h
    exact h)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The underlying cochain complex of `M⟦n⟧` is the shifted underlying cochain complex of `M`. -/
def complexFunctorShiftIso (n : ℤ) (M : DGModuleCat.{v} S) :
    (complexFunctor S).obj ((shiftFunctor (DGModuleCat.{v} S) n).obj M) ≅
      (shiftFunctor (CochainComplex (ModuleCat.{v} S) ℤ) n).obj ((complexFunctor S).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (shiftGradingLinearEquiv M n i).toModuleIso) (by
      rintro i j (rfl : i + 1 = j)
      refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
      have h1 := toComplex_d_apply M (show i + n + 1 = i + 1 + n by ring)
        (shiftGradingLinearEquiv M n i x)
      have h2 := toComplex_d_apply ((shiftFunctor (DGModuleCat.{v} S) n).obj M) rfl x
      change n.negOnePow • (((toComplex S M).d (i + n) (i + 1 + n)).hom
          (shiftGradingLinearEquiv M n i x)).1 =
        unmk n (((toComplex S ((shiftFunctor (DGModuleCat.{v} S) n).obj M)).d i (i + 1)).hom x).1
      rw [h1, h2]
      rfl)

/-- The functor to cochain complexes commutes with the shifts. -/
def complexFunctorCommShiftIso (n : ℤ) :
    shiftFunctor (DGModuleCat.{v} S) n ⋙ complexFunctor S ≅
      complexFunctor S ⋙ shiftFunctor (CochainComplex (ModuleCat.{v} S) ℤ) n :=
  NatIso.ofComponents (complexFunctorShiftIso n) fun _ =>
    HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The functor to cochain complexes commutes with the shifts. -/
instance complexFunctorCommShift : (complexFunctor.{v} S).CommShift ℤ where
  commShiftIso := complexFunctorCommShiftIso
  commShiftIso_zero := by
    ext M : 3
    rw [Functor.CommShift.isoZero_hom_app]
    ext i x : 3
    apply Subtype.ext
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CochainComplex.shiftFunctorZero_inv_app_f]
    exact (toComplex_XIsoOfEq_hom_apply M (show i = i + 0 by omega)
      ((((complexFunctor S).map ((shiftFunctorZero (DGModuleCat.{v} S) ℤ).hom.app M)).f i).hom
        x)).symm
  commShiftIso_add a b := by
    ext M : 3
    rw [Functor.CommShift.isoAdd_hom_app]
    ext i x : 3
    apply Subtype.ext
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CochainComplex.shiftFunctorAdd_inv_app_f]
    symm
    refine (toComplex_XIsoOfEq_hom_apply M _ _).trans ?_
    rfl

end Shift

/-! ### Cochains of the Hom complex -/

section Cochain

variable {M N P : DGModuleCat.{v} S} {n : ℤ}

/-- A cochain of degree `n` restricted to `Mᵖ → N^q`, `p + n = q`, as an `S`-linear map. -/
def cochainRestrict (z : Cochain S M N n) (p q : ℤ) (hpq : p + n = q) :
    gradingSubmodule S M p →ₗ[S] gradingSubmodule S N q where
  toFun x := ⟨z x.1, hpq ▸ z.map_mem x.2⟩
  map_add' x y := Subtype.ext (map_add z x.1 y.1)
  map_smul' s x := Subtype.ext (by
    change z (s • x.1) = s • z x.1
    rw [z.map_smul (mem_grading_zero s), mul_zero, koszulSign_zero, one_smul])

/-- A cochain of the Hom complex `HOM_S(M, N)` as a cochain of Mathlib's Hom complex of the
underlying cochain complexes of `S`-modules. -/
def toHomComplex (z : Cochain S M N n) :
    CochainComplex.HomComplex.Cochain ((complexFunctor S).obj M) ((complexFunctor S).obj N) n :=
  CochainComplex.HomComplex.Cochain.mk fun p q hpq => ModuleCat.ofHom (cochainRestrict z p q hpq)

@[simp]
theorem toHomComplex_v_apply (z : Cochain S M N n) (p q : ℤ) (hpq : p + n = q)
    (x : gradingSubmodule S M p) :
    (((toHomComplex z).v p q hpq).hom x).1 = z x.1 := rfl

theorem toHomComplex_ext {z₁ z₂ : CochainComplex.HomComplex.Cochain ((complexFunctor S).obj M)
      ((complexFunctor S).obj N) n}
    (h : ∀ p q hpq (x : gradingSubmodule S M p),
      ((z₁.v p q hpq).hom x).1 = ((z₂.v p q hpq).hom x).1) : z₁ = z₂ :=
  CochainComplex.HomComplex.Cochain.ext _ _ fun p q hpq =>
    ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (h p q hpq x))

@[simp]
theorem toHomComplex_add (z₁ z₂ : Cochain S M N n) :
    toHomComplex (z₁ + z₂) = toHomComplex z₁ + toHomComplex z₂ :=
  toHomComplex_ext fun _ _ _ _ => rfl

@[simp]
theorem toHomComplex_neg (z : Cochain S M N n) : toHomComplex (-z) = -toHomComplex z :=
  toHomComplex_ext fun _ _ _ _ => rfl

@[simp]
theorem toHomComplex_zero : toHomComplex (0 : Cochain S M N n) = 0 :=
  toHomComplex_ext fun _ _ _ _ => rfl

@[simp]
theorem toHomComplex_ofHom (f : M ⟶ N) :
    toHomComplex (Cochain.ofHom f.hom) =
      CochainComplex.HomComplex.Cochain.ofHom ((complexFunctor S).map f) :=
  toHomComplex_ext fun p q hpq x => by
    obtain rfl : q = p := by omega
    rw [CochainComplex.HomComplex.Cochain.ofHom_v]
    rfl

@[simp]
theorem toHomComplex_comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain S N P n₂) (z₁ : Cochain S M N n₁)
    (h : n₁ + n₂ = n₁₂) :
    toHomComplex (z₂.comp z₁ h) = (toHomComplex z₁).comp (toHomComplex z₂) h :=
  toHomComplex_ext fun p q hpq x => by
    rw [CochainComplex.HomComplex.Cochain.comp_v _ _ h p (p + n₁) q rfl (by omega)]
    rfl

private theorem ModuleCat.units_smul_apply {X Y : ModuleCat.{v} S} (k : ℤˣ) (φ : X ⟶ Y)
    (x : X) : (k • φ).hom x = k • φ.hom x := rfl

private theorem Submodule.coe_units_smul {X : Type*} [AddCommGroup X] [Module S X]
    (T : Submodule S X) (k : ℤˣ) (x : T) : ((k • x : T) : X) = k • (x : X) := rfl

theorem toHomComplex_δ (m : ℤ) (z : Cochain S M N n) :
    toHomComplex (δ n m z) = CochainComplex.HomComplex.δ n m (toHomComplex z) := by
  by_cases hnm : n + 1 = m
  · refine toHomComplex_ext fun p q hpq x => ?_
    rw [CochainComplex.HomComplex.δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl]
    simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.units_smul_apply, toHomComplex_v_apply]
    rw [δ_apply' n m hnm]
    erw [Submodule.coe_add, Submodule.coe_units_smul, complexFunctor_obj_d_apply,
      toHomComplex_v_apply, toHomComplex_v_apply, complexFunctor_obj_d_apply]
    all_goals omega
  · rw [δ_shape _ _ hnm, CochainComplex.HomComplex.δ_shape _ _ hnm, toHomComplex_zero]

/-- A homotopy between morphisms of dg modules gives a homotopy between the underlying morphisms
of cochain complexes of `S`-modules. -/
noncomputable def toHomotopy {f g : M ⟶ N} (h : DGHomotopy f.hom g.hom) :
    Homotopy ((complexFunctor S).map f) ((complexFunctor S).map g) :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm ⟨toHomComplex h.hom, by
    rw [← toHomComplex_ofHom, ← toHomComplex_ofHom, ← toHomComplex_δ, h.ofHom_eq,
      toHomComplex_add]⟩

end Cochain

/-! ### The mapping cone -/

section Cone

open Cone

variable {M N : DGModuleCat.{v} S} (φ : M ⟶ N)

theorem coneIso_inv_eq :
    CochainComplex.HomComplex.δ (-1) 0
        (toHomComplex (M := M) (N := DGModuleCat.of S (Cone φ.hom)) (inl φ.hom)) =
      CochainComplex.HomComplex.Cochain.ofHom
        ((complexFunctor S).map φ ≫ (complexFunctor S).map (DGModuleCat.ofHom (inr φ.hom))) := by
  rw [← toHomComplex_δ, δ_inl, ← Functor.map_comp, ← toHomComplex_ofHom]
  rfl

/-- The underlying cochain complex of the mapping cone of `φ` is Mathlib's mapping cone of the
underlying morphism of cochain complexes of `S`-modules. -/
noncomputable def coneIso :
    (complexFunctor S).obj (DGModuleCat.of S (Cone φ.hom)) ≅
      CochainComplex.mappingCone ((complexFunctor S).map φ) where
  hom := CochainComplex.mappingCone.lift _
    (CochainComplex.HomComplex.Cocycle.mk
      (toHomComplex (M := DGModuleCat.of S (Cone φ.hom)) (N := M) (fst φ.hom).1) 2 (by norm_num)
      (by rw [← toHomComplex_δ, Cocycle.δ_eq_zero, toHomComplex_zero]))
    (toHomComplex (M := DGModuleCat.of S (Cone φ.hom)) (N := N) (snd φ.hom)) (by
      rw [← toHomComplex_δ, δ_snd]
      rw [toHomComplex_neg, toHomComplex_comp, toHomComplex_ofHom]
      exact neg_add_cancel _)
  inv := CochainComplex.mappingCone.desc _
    (toHomComplex (M := M) (N := DGModuleCat.of S (Cone φ.hom)) (inl φ.hom))
    ((complexFunctor S).map (DGModuleCat.ofHom (inr φ.hom))) (coneIso_inv_eq φ)
  hom_inv_id := by
    ext n : 1
    rw [HomologicalComplex.comp_f,
      CochainComplex.mappingCone.lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
    erw [Submodule.coe_add]
    exact id_X (f := φ.hom) x.1
  inv_hom_id := by
    ext n : 1
    refine CochainComplex.mappingCone.ext_from _ (n + 1) n rfl ?_ ?_ <;>
      refine CochainComplex.mappingCone.ext_to _ n (n + 1) rfl ?_ ?_ <;>
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, comp_id, assoc,
        CochainComplex.mappingCone.lift_f_fst_v, CochainComplex.mappingCone.lift_f_snd_v,
        CochainComplex.mappingCone.inl_v_desc_f_assoc,
        CochainComplex.mappingCone.inr_f_desc_f_assoc, CochainComplex.mappingCone.inl_v_fst_v,
        CochainComplex.mappingCone.inl_v_snd_v, CochainComplex.mappingCone.inr_f_fst_v,
        CochainComplex.mappingCone.inr_f_snd_v] <;>
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl)

theorem inr_coneIso_inv :
    CochainComplex.mappingCone.inr ((complexFunctor S).map φ) ≫ (coneIso φ).inv =
      (complexFunctor S).map (DGModuleCat.ofHom (inr φ.hom)) :=
  CochainComplex.mappingCone.inr_desc _ _ _ (coneIso_inv_eq φ)

theorem inl_v_coneIso_inv_f (p q : ℤ) (h : p + (-1) = q) :
    (CochainComplex.mappingCone.inl ((complexFunctor S).map φ)).v p q h ≫ (coneIso φ).inv.f q =
      (toHomComplex (M := M) (N := DGModuleCat.of S (Cone φ.hom)) (inl φ.hom)).v p q h :=
  CochainComplex.mappingCone.inl_v_desc_f _ _ _ (coneIso_inv_eq φ) p q h

theorem inr_f_coneIso_inv_f (p : ℤ) :
    (CochainComplex.mappingCone.inr ((complexFunctor S).map φ)).f p ≫ (coneIso φ).inv.f p =
      ((complexFunctor S).map (DGModuleCat.ofHom (inr φ.hom))).f p :=
  CochainComplex.mappingCone.inr_f_desc_f _ _ _ (coneIso_inv_eq φ) p

/-- The image of the standard triangle of `φ` is Mathlib's standard triangle of the underlying
morphism of cochain complexes. -/
noncomputable def coneTriangleIso :
    (complexFunctor S).mapTriangle.obj (triangle φ) ≅
      CochainComplex.mappingCone.triangle ((complexFunctor S).map φ) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (coneIso φ) (by simp) ?_ ?_
  · rw [Iso.refl_hom, id_comp, ← cancel_mono (coneIso φ).inv, assoc, Iso.hom_inv_id,
      comp_id]
    exact (inr_coneIso_inv φ).symm
  · rw [Iso.refl_hom, CategoryTheory.Functor.map_id, comp_id, ← cancel_epi (coneIso φ).inv,
      Iso.inv_hom_id_assoc]
    ext n : 1
    refine CochainComplex.mappingCone.ext_from _ (n + 1) n rfl ?_ ?_
    · rw [CochainComplex.mappingCone.inl_v_triangle_mor₃_f, HomologicalComplex.comp_f,
        ← assoc, inl_v_coneIso_inv_f]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
      simp only [CochainComplex.shiftFunctorObjXIso]
      erw [ModuleCat.hom_neg, LinearMap.neg_apply, Submodule.coe_neg]
    · rw [CochainComplex.mappingCone.inr_f_triangle_mor₃_f, HomologicalComplex.comp_f,
        ← assoc, inr_f_coneIso_inv_f]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
      exact (neg_zero : -(0 : (M : Type v)) = 0)

end Cone

/-! ### The functor on homotopy categories -/

variable (S) in
/-- The functor from the homotopy category of dg modules over a ring `S` in degree `0` to
Mathlib's homotopy category of cochain complexes of `S`-modules. -/
noncomputable def homotopyFunctor :
    HomotopyCategory.{v} S ⥤ _root_.HomotopyCategory (ModuleCat.{v} S) (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _
    (complexFunctor S ⋙ _root_.HomotopyCategory.quotient _ _)
    (fun _ _ _ _ h => _root_.HomotopyCategory.eq_of_homotopy _ _ (toHomotopy h.some))

variable (S) in
/-- The functor on homotopy categories is induced by `DG.DegreeZero.complexFunctor S`. -/
noncomputable def homotopyFunctorFactors :
    HomotopyCategory.quotient S ⋙ homotopyFunctor.{v} S ≅
      complexFunctor S ⋙ _root_.HomotopyCategory.quotient _ _ :=
  CategoryTheory.Quotient.lift.isLift _ _ _

@[simp]
theorem homotopyFunctor_map_quotient_map {M N : DGModuleCat.{v} S} (f : M ⟶ N) :
    (homotopyFunctor S).map ((HomotopyCategory.quotient S).map f) =
      (_root_.HomotopyCategory.quotient _ _).map ((complexFunctor S).map f) :=
  rfl

instance : (homotopyFunctor.{v} S).Additive := by
  have := Functor.additive_of_iso (homotopyFunctorFactors.{v} S).symm
  exact Functor.additive_of_full_essSurj_comp (HomotopyCategory.quotient S) _

/-- The functor on homotopy categories commutes with the shifts. -/
noncomputable instance homotopyFunctorCommShift : (homotopyFunctor.{v} S).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift _ _ _ _

instance : NatTrans.CommShift (homotopyFunctorFactors.{v} S).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility _ _ _ _

/-- The image of the standard triangle `triangleh φ` is Mathlib's standard triangle of the
underlying morphism of cochain complexes. -/
noncomputable def mapTrianglehIso {M N : DGModuleCat.{v} S} (φ : M ⟶ N) :
    (homotopyFunctor S).mapTriangle.obj (Cone.triangleh φ) ≅
      CochainComplex.mappingCone.triangleh ((complexFunctor S).map φ) :=
  (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (Functor.mapTriangleIso (homotopyFunctorFactors S)).app _ ≪≫
    (Functor.mapTriangleCompIso _ _).app _ ≪≫
    (_root_.HomotopyCategory.quotient _ _).mapTriangle.mapIso (coneTriangleIso φ)

/-- The functor on homotopy categories is a triangulated functor. -/
instance homotopyFunctor_isTriangulated : (homotopyFunctor.{v} S).IsTriangulated where
  map_distinguished := by
    rintro T ⟨M, N, φ, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(homotopyFunctor S).mapTriangle.mapIso e ≪≫ mapTrianglehIso φ⟩⟩

end DegreeZero

end DG
