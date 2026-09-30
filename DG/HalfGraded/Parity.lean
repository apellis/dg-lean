import DG.HalfGraded.Basic
import DG.Category.Homotopy.Precomp
import DG.Category.WeightComparison

/-!
# The parity shift and odd morphisms of half-graded dg modules

Let `H` be a half-graded dg ring with parameter `k` (`DG.HalfGradedDGRing`) and let
`C_H = DG.WeightCategory H.Regraded` be the weight dg category of its regraded ring: its objects
are the integers `i`, and `C_H(i, j)` is the weight-`(j - i)` part of `H.Regraded`. A dg module
`M` over `C_H` is a half-graded dg module: the value `M(i)` in cohomological degree `n` is the
part of internal degree `i + n k` and parity `n mod 2`, and the differential `d : M(i)ⁿ → M(i)ⁿ⁺¹`
is the differential of bidegree `(k, 1̄)`.

## Conventions

* The internal shift `M⟨s⟩` is restriction along `i ↦ i + s`, `(M⟨s⟩)(i) = M(i + s)`, as in
  `DG.Bigraded.Derived`; on half-graded modules `(M⟨s⟩)^{j, ε} = M^{j + s, ε}`.
* The parity shift is `Π M = M⟨-k⟩⟦1⟧` (`DG.HalfGradedDGRing.parityShift`): its value at `i` in
  cohomological degree `n` is `M(i - k)ⁿ⁺¹`, the part of `M` of internal degree
  `i - k + (n + 1) k = i + n k` and parity `n + 1`. On half-graded modules it is the parity shift
  `(Π M)^{j, ε} = M^{j, ε + 1}`, with the differential `-d` and the action
  `a • m = (-1)^{|a|} a • m`: these are the sign conventions of the shift `⟦1⟧`
  (`docs/CONVENTIONS.md`). Consequently the translation `⟦1⟧` of dg modules over `C_H` is
  `M⟦1⟧ = Π (M⟨k⟩)`: **the translation of half-graded dg modules is the parity shift combined with
  the internal shift `⟨k⟩`**, with the sign conventions of the shift of `docs/CONVENTIONS.md`
  (in particular the mapping cone of `f : M → N` is `Π (M⟨k⟩) ⊕ N` with
  `d (x, y) = (-d x, f x + d y)`).
* The central unit `u` of bidegree `(2, -2k)` of `H.Regraded` gives, at every object, degree-`2`
  isomorphisms `u : i ⟶ i - 2k` of `C_H` (`DG.HalfGradedDGRing.unitHom`, inverse
  `DG.HalfGradedDGRing.unitInvHom`). They identify the two copies `M(i)ⁿ` and `M(i - 2k)ⁿ⁺²` of the
  part of internal degree `i + n k` and parity `n` of a half-graded module. Hence `Π Π M ≅ M`,
  by `m ↦ u⁻¹ • m` (`DG.HalfGradedDGRing.parityShiftIso`), naturally in `M`, with
  `Π (ε_M) = ε_{Π M}` (`DG.HalfGradedDGRing.parityShift_map_parityShiftIso`).

## Odd morphisms

A morphism of half-graded modules of bidegree `(0, 1̄)` (odd, of internal degree `0`) sends the
part of `M` of internal degree `i + n k` and parity `n` to the part of `N` of internal degree
`i + n k = (i - k) + (n + 1) k` and parity `n + 1`: it is a cochain of degree `1` of the Hom complex
`HOM_{C_H}(M, N⟨-k⟩)`, with the Koszul sign rule of an odd map. The `ℤ/2`-graded Hom complex
of half-graded modules in internal degree `0` is therefore
`HOM(M, N)^{0̄} = HOM_{C_H}(M, N)⁰` and `HOM(M, N)^{1̄} = HOM_{C_H}(M, N⟨-k⟩)¹`, with the
differential of the Hom complex (of bidegree `(k, 1̄)`, from `HOM(M, N⟨-k⟩)⁰`, the even maps of
internal degree `-k`, to the odd maps of internal degree `0`). Odd closed maps are the
cocycles `DG.HalfGradedDGRing.OddCocycle M N := Cocycle M N⟨-k⟩ 1`, and odd null-homotopic maps are
the coboundaries.

* `DG.HalfGradedDGRing.oddEquiv M N : OddCocycle M N ≃+ (M ⟶ Π N)`: odd closed maps `M → N` are the
  even closed maps `M → Π N` (the same underlying maps); `DG.HalfGradedDGRing.oddEquiv'`:
  odd closed maps `M → N` are the even closed maps `Π M → N` (`m ↦ u⁻¹ • f m`).
* Compatibility with homotopy: `DG.HalfGradedDGRing.mem_coboundaries_iff_homotopic_zero`, and
  `DG.HalfGradedDGRing.oddCohomologyEquiv`, odd closed maps up to homotopy are the morphisms
  `M → Π N` of the homotopy category.
* Compatibility with composition: the composite of an even map and an odd map
  (`DG.HalfGradedDGRing.oddEquiv_compEven`, `DG.HalfGradedDGRing.oddEquiv_evenComp`), and of two odd
  maps, which is even: `DG.HalfGradedDGRing.oddComp g f = u⁻¹ ∘ g⟨-k⟩ ∘ f`, and
  `DG.HalfGradedDGRing.oddComp_eq : oddComp g f = oddEquiv f ≫ Π (oddEquiv g) ≫ ε`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Category Limits

universe w u

noncomputable section

namespace DG

namespace HalfGradedDGRing

variable {A : Type u} [Ring A] {k : ℤ} (H : HalfGradedDGRing A k)

open CatModule WeightCategory

/-! ### The periodicity unit as morphisms of `C_H` -/

section Unit

/-- The periodicity unit `u` as a morphism `i ⟶ j` of `C_H` for `j = i - 2k`, of degree `2`. -/
def unitHom (i j : WeightCategory H.Regraded) (h : j.as = i.as + -2 * k) : i ⟶ j :=
  ⟨H.periodUnit, by rw [h, add_sub_cancel_left]; exact H.periodUnit_mem_wgrading⟩

/-- The inverse `u⁻¹` of the periodicity unit as a morphism `i ⟶ j` of `C_H` for `j = i + 2k`, of
degree `-2`. -/
def unitInvHom (i j : WeightCategory H.Regraded) (h : j.as = i.as + 2 * k) : i ⟶ j :=
  ⟨H.periodUnitInv, by rw [h, add_sub_cancel_left]; exact H.periodUnitInv_mem_wgrading⟩

variable {H}

@[simp]
theorem unitHom_val {i j : WeightCategory H.Regraded} (h : j.as = i.as + -2 * k) :
    (unitHom H i j h).1 = H.periodUnit := rfl

@[simp]
theorem unitInvHom_val {i j : WeightCategory H.Regraded} (h : j.as = i.as + 2 * k) :
    (unitInvHom H i j h).1 = H.periodUnitInv := rfl

theorem unitHom_mem_grading {i j : WeightCategory H.Regraded} (h : j.as = i.as + -2 * k) :
    unitHom H i j h ∈ grading 2 :=
  H.periodUnit_mem_grading

theorem unitInvHom_mem_grading {i j : WeightCategory H.Regraded} (h : j.as = i.as + 2 * k) :
    unitInvHom H i j h ∈ grading (-2) :=
  H.periodUnitInv_mem_grading

@[simp]
theorem d_unitHom {i j : WeightCategory H.Regraded} (h : j.as = i.as + -2 * k) :
    d (unitHom H i j h) = 0 :=
  Subtype.ext (by rw [d_val, unitHom_val, d_periodUnit]; rfl)

@[simp]
theorem d_unitInvHom {i j : WeightCategory H.Regraded} (h : j.as = i.as + 2 * k) :
    d (unitInvHom H i j h) = 0 :=
  Subtype.ext (by rw [d_val, unitInvHom_val, d_periodUnitInv]; rfl)

@[simp]
theorem unitHom_comp_unitInvHom {i j : WeightCategory H.Regraded} (h : j.as = i.as + -2 * k)
    (h' : i.as = j.as + 2 * k) : unitHom H i j h ≫ unitInvHom H j i h' = 𝟙 i :=
  hom_ext (by rw [comp_val, unitHom_val, unitInvHom_val, id_val, periodUnitInv_mul_periodUnit])

@[simp]
theorem unitInvHom_comp_unitHom {i j : WeightCategory H.Regraded} (h : j.as = i.as + 2 * k)
    (h' : i.as = j.as + -2 * k) : unitInvHom H i j h ≫ unitHom H j i h' = 𝟙 i :=
  hom_ext (by rw [comp_val, unitHom_val, unitInvHom_val, id_val, periodUnit_mul_periodUnitInv])

/-- The unit commutes with the morphisms of `C_H`. -/
theorem comp_unitHom {i j i' j' : WeightCategory H.Regraded} (f : i ⟶ j) (g : i' ⟶ j')
    (hfg : f.1 = g.1) (h : i'.as = i.as + -2 * k) (h' : j'.as = j.as + -2 * k) :
    f ≫ unitHom H j j' h' = unitHom H i i' h ≫ g :=
  hom_ext (by rw [comp_val, comp_val, unitHom_val, unitHom_val, hfg, periodUnit_mul_comm])

/-- The inverse of the unit commutes with the morphisms of `C_H`. -/
theorem comp_unitInvHom {i j i' j' : WeightCategory H.Regraded} (f : i ⟶ j) (g : i' ⟶ j')
    (hfg : f.1 = g.1) (h : i'.as = i.as + 2 * k) (h' : j'.as = j.as + 2 * k) :
    f ≫ unitInvHom H j j' h' = unitInvHom H i i' h ≫ g :=
  hom_ext (by rw [comp_val, comp_val, unitInvHom_val, unitInvHom_val, hfg, periodUnitInv_mul_comm])

end Unit

/-! ### The internal shift and the parity shift -/

section ParityShift

/-- The internal shift `M ↦ M⟨s⟩` of dg modules over `C_H`: restriction along `i ↦ i + s`. -/
abbrev internalShiftFunctor (s : ℤ) : CatModule.{w} (WeightCategory H.Regraded) ⥤
    CatModule.{w} (WeightCategory H.Regraded) :=
  CatModule.precomp (WeightCategory.shiftFunctor H.Regraded s)

/-- The parity shift `Π M = M⟨-k⟩⟦1⟧` of dg modules over `C_H`. On half-graded modules it is the
parity shift `(Π M)^{j, ε} = M^{j, ε + 1}`, with differential `-d` and action
`a • m = (-1)^{|a|} a • m`. -/
def parityShift : CatModule.{w} (WeightCategory H.Regraded) ⥤
    CatModule.{w} (WeightCategory H.Regraded) :=
  internalShiftFunctor H (-k) ⋙ shiftFunctor _ (1 : ℤ)

theorem parityShift_obj (M : CatModule.{w} (WeightCategory H.Regraded)) :
    (parityShift H).obj M = CatModule.shift 1 ((internalShiftFunctor H (-k)).obj M) := rfl

variable {H}

/-- The additive equivalence `M(i) ≃ M(j)` given by the action of an isomorphism `i ≅ j`. -/
def actEquiv (M : CatModule.{w} (WeightCategory H.Regraded)) {i j : WeightCategory H.Regraded}
    (f : i ⟶ j) (g : j ⟶ i) (hfg : f ≫ g = 𝟙 i) (hgf : g ≫ f = 𝟙 j) : M.obj i ≃+ M.obj j where
  toFun := M.act f
  invFun := M.act g
  left_inv m := by
    change g • f • m = m
    rw [← comp_smul, hfg, id_smul]
  right_inv m := by
    change f • g • m = m
    rw [← comp_smul, hgf, id_smul]
  map_add' := map_add _

/-- The object `i - 2k = (i - k) - k` of `C_H`, the value at `i` of `Π Π M` being `M(i - 2k)`. -/
abbrev twoBelow (i : WeightCategory H.Regraded) : WeightCategory H.Regraded :=
  (WeightCategory.shiftFunctor H.Regraded (-k)).obj
    ((WeightCategory.shiftFunctor H.Regraded (-k)).obj i)

theorem twoBelow_as (i : WeightCategory H.Regraded) : (twoBelow i).as + 2 * k = i.as := by
  change i.as + -k + -k + 2 * k = i.as
  ring

theorem twoBelow_as' (i : WeightCategory H.Regraded) : (twoBelow i).as = i.as + -2 * k := by
  change i.as + -k + -k = i.as + -2 * k
  ring

/-- The morphism `i - 2k ⟶ j - 2k` with the same value as `f : i ⟶ j`. -/
abbrev twoBelowMap {i j : WeightCategory H.Regraded} (f : i ⟶ j) : twoBelow i ⟶ twoBelow j :=
  homMk f.1 (by
    rw [show (twoBelow j).as - (twoBelow i).as = j.as - i.as by
      rw [twoBelow_as', twoBelow_as']; ring]
    exact f.2)

/-- The identification of `(Π Π M)(i)` with `M(i - 2k)`, the identity on elements (the
cohomological degree is shifted by `2`). -/
def unmkTwo (M : CatModule.{w} (WeightCategory H.Regraded)) (i : WeightCategory H.Regraded) :
    ((parityShift H).obj ((parityShift H).obj M)).obj i ≃+ M.obj (twoBelow i) :=
  (shift.unmk (M := (internalShiftFunctor H (-k)).obj ((parityShift H).obj M)) 1).trans
    (shift.unmk (M := (internalShiftFunctor H (-k)).obj M) 1)

theorem unmkTwo_mem_grading_iff (M : CatModule.{w} (WeightCategory H.Regraded))
    {i : WeightCategory H.Regraded} {n : ℤ}
    (m : ((parityShift H).obj ((parityShift H).obj M)).obj i) :
    unmkTwo M i m ∈ grading (n + 2) ↔ m ∈ grading n := by
  rw [shift.mem_grading_iff' (n := 1), show n + 2 = n + 1 + 1 by ring]
  exact shift.mem_grading_iff'.symm

theorem unmkTwo_d (M : CatModule.{w} (WeightCategory H.Regraded)) {i : WeightCategory H.Regraded}
    (m : ((parityShift H).obj ((parityShift H).obj M)).obj i) :
    unmkTwo M i (d m) = d (unmkTwo M i m) := by
  have h : unmkTwo M i (d m) = koszulSign 1 • koszulSign 1 • d (unmkTwo M i m) := rfl
  rw [h, smul_smul, Int.units_mul_self, one_smul]

/-- The action of a homogeneous morphism on `Π Π M`: the two signs cancel. -/
theorem unmkTwo_smul (M : CatModule.{w} (WeightCategory H.Regraded))
    {i j : WeightCategory H.Regraded} {p : ℤ} {f : i ⟶ j} (hf : f ∈ grading p)
    (m : ((parityShift H).obj ((parityShift H).obj M)).obj i) :
    unmkTwo M j (f • m) = twoBelowMap f • unmkTwo M i m := by
  let F := WeightCategory.shiftFunctor H.Regraded (-k)
  have h : unmkTwo M j (f • m) = F.map (twist 1 (F.map (twist 1 f))) • unmkTwo M i m := rfl
  have hF : ∀ {a b : WeightCategory H.Regraded} (u : ℤˣ) (g : a ⟶ b), F.map (u • g) = u • F.map g :=
    fun u g => by rw [Units.smul_def, Functor.map_zsmul, ← Units.smul_def]
  rw [h, twist_of_mem hf, hF, twist_of_mem (units_smul_mem_grading _ (F.map_mem_grading hf)),
    hF, hF, smul_smul, Int.units_mul_self, one_smul]
  rfl

/-- The component at `i` of the isomorphism `Π Π M ≅ M`: `m ↦ u⁻¹ • m`, from
`(Π Π M)(i) = M(i - 2k)` (with the cohomological degree shifted by `2`) to `M(i)`. -/
def parityShiftIsoApp (M : CatModule.{w} (WeightCategory H.Regraded))
    (i : WeightCategory H.Regraded) :
    ((parityShift H).obj ((parityShift H).obj M)).obj i ≃+ M.obj i :=
  (unmkTwo M i).trans
    (actEquiv M (unitInvHom H (twoBelow i) i (twoBelow_as i).symm)
      (unitHom H i (twoBelow i) (twoBelow_as' i))
      (unitInvHom_comp_unitHom _ _) (unitHom_comp_unitInvHom _ _))

theorem parityShiftIsoApp_apply (M : CatModule.{w} (WeightCategory H.Regraded))
    (i : WeightCategory H.Regraded) (m : ((parityShift H).obj ((parityShift H).obj M)).obj i) :
    parityShiftIsoApp M i m =
      unitInvHom H (twoBelow i) i (twoBelow_as i).symm • unmkTwo M i m :=
  rfl

theorem parityShiftIsoApp_symm_apply (M : CatModule.{w} (WeightCategory H.Regraded))
    (i : WeightCategory H.Regraded) (m : M.obj i) :
    (parityShiftIsoApp M i).symm m =
      (unmkTwo M i).symm (unitHom H i (twoBelow i) (twoBelow_as' i) • m) :=
  rfl

variable (H) in
/-- The isomorphism `Π Π M ≅ M`, `m ↦ u⁻¹ • m`. -/
def parityShiftIsoObj (M : CatModule.{w} (WeightCategory H.Regraded)) :
    (parityShift H).obj ((parityShift H).obj M) ≅ M :=
  isoMk (parityShiftIsoApp M)
    (fun {i n m} => by
      rw [parityShiftIsoApp_apply, ← unmkTwo_mem_grading_iff]
      constructor
      · intro h
        have := CatModule.smul_mem_grading (M := M)
          (unitHom_mem_grading (H := H) (twoBelow_as' i)) h
        rwa [← comp_smul, unitInvHom_comp_unitHom, id_smul, add_comm] at this
      · intro h
        have := CatModule.smul_mem_grading (M := M)
          (unitInvHom_mem_grading (H := H) (twoBelow_as i).symm) h
        rwa [show -2 + (n + 2) = n by ring] at this)
    (fun {i} m => by
      rw [parityShiftIsoApp_apply, parityShiftIsoApp_apply, unmkTwo_d,
        CatModule.d_smul_of_d_eq_zero (unitInvHom_mem_grading _) (d_unitInvHom _),
        show (-2 : ℤ) = 2 * -1 by ring, koszulSign_even (even_two_mul _), one_smul])
    (fun {i j} f m => by
      induction f using DG.induction_on with
      | h_zero => simp
      | h_homogeneous f =>
        rw [parityShiftIsoApp_apply, parityShiftIsoApp_apply, unmkTwo_smul _ f.2,
          ← comp_smul, ← comp_smul]
        congr 1
        exact comp_unitInvHom (twoBelowMap (f : i ⟶ j)) (f : i ⟶ j) rfl _ _
      | h_add f f' hf hf' => rw [CatModule.add_smul, CatModule.add_smul, map_add, hf, hf'])

@[simp]
theorem parityShiftIsoObj_hom_app (M : CatModule.{w} (WeightCategory H.Regraded))
    (i : WeightCategory H.Regraded) (m : ((parityShift H).obj ((parityShift H).obj M)).obj i) :
    (parityShiftIsoObj H M).hom.app i m =
      unitInvHom H (twoBelow i) i (twoBelow_as i).symm • unmkTwo M i m :=
  rfl

@[simp]
theorem parityShiftIsoObj_inv_app (M : CatModule.{w} (WeightCategory H.Regraded))
    (i : WeightCategory H.Regraded) (m : M.obj i) :
    (parityShiftIsoObj H M).inv.app i m =
      (unmkTwo M i).symm (unitHom H i (twoBelow i) (twoBelow_as' i) • m) :=
  rfl

variable (H) in
/-- The parity shift is an involution: `Π ∘ Π ≅ 𝟭`, by `m ↦ u⁻¹ • m`. -/
def parityShiftIso : parityShift.{w} H ⋙ parityShift H ≅ 𝟭 _ :=
  NatIso.ofComponents (parityShiftIsoObj H) fun {M N} φ => hom_ext fun i m => by
    change unitInvHom H (twoBelow i) i (twoBelow_as i).symm • φ.app (twoBelow i) (unmkTwo M i m) =
      φ.app i (unitInvHom H (twoBelow i) i (twoBelow_as i).symm • unmkTwo M i m)
    exact (φ.map_smul _ _).symm

@[simp]
theorem parityShiftIso_hom_app (M : CatModule.{w} (WeightCategory H.Regraded)) :
    (parityShiftIso H).hom.app M = (parityShiftIsoObj H M).hom :=
  rfl

@[simp]
theorem parityShiftIso_inv_app (M : CatModule.{w} (WeightCategory H.Regraded)) :
    (parityShiftIso H).inv.app M = (parityShiftIsoObj H M).inv :=
  rfl

/-- The involution `Π Π ≅ 𝟭` is compatible with `Π`: `Π (ε_M) = ε_{Π M}`. -/
theorem parityShift_map_parityShiftIso (M : CatModule.{w} (WeightCategory H.Regraded)) :
    (parityShift H).map ((parityShiftIsoObj H M).hom) =
      (parityShiftIsoObj H ((parityShift H).obj M)).hom := by
  refine hom_ext fun i m => ?_
  rw [parityShiftIsoObj_hom_app]
  apply (shift.unmk (M := (internalShiftFunctor H (-k)).obj M) 1).injective
  change (parityShiftIsoObj H M).hom.app _ (shift.unmk 1 m) = _
  rw [parityShiftIsoObj_hom_app, shift.unmk_smul (unitInvHom_mem_grading _),
    show (1 : ℤ) * -2 = 2 * -1 by ring, koszulSign_even (even_two_mul _), one_smul]
  rfl

end ParityShift

/-! ### The parity shift is an involution on morphisms -/

instance : (parityShift.{w} H).Additive := by
  unfold parityShift; infer_instance

section HomEquiv

variable {H} {M N : CatModule.{w} (WeightCategory H.Regraded)}

/-- Morphisms `Π M → N` correspond to morphisms `M → Π N`: `g ↦ ε_M⁻¹ ≫ Π g`. -/
def parityShiftHomEquiv :
    ((parityShift H).obj M ⟶ N) ≃+ (M ⟶ (parityShift H).obj N) where
  toFun g := (parityShiftIsoObj H M).inv ≫ (parityShift H).map g
  invFun f := (parityShift H).map f ≫ (parityShiftIsoObj H N).hom
  left_inv g := by
    dsimp only
    have h := (parityShiftIso H).hom.naturality g
    simp only [Functor.comp_map, Functor.id_map, parityShiftIso_hom_app] at h
    rw [Functor.map_comp, assoc, h, ← parityShift_map_parityShiftIso, ← assoc,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, id_comp]
  right_inv f := by
    dsimp only
    have h := (parityShiftIso H).hom.naturality f
    simp only [Functor.comp_map, Functor.id_map, parityShiftIso_hom_app] at h
    rw [Functor.map_comp, parityShift_map_parityShiftIso, h, Iso.inv_hom_id_assoc]
  map_add' g g' := by rw [Functor.map_add, Preadditive.comp_add]

theorem parityShiftHomEquiv_apply (g : (parityShift H).obj M ⟶ N) :
    parityShiftHomEquiv g = (parityShiftIsoObj H M).inv ≫ (parityShift H).map g := rfl

theorem parityShiftHomEquiv_symm_apply (f : M ⟶ (parityShift H).obj N) :
    parityShiftHomEquiv.symm f = (parityShift H).map f ≫ (parityShiftIsoObj H N).hom := rfl

/-- The parity shift preserves null-homotopic morphisms. -/
theorem parityShift_map_mem_nullHomotopic {f : M ⟶ N} (hf : f ∈ nullHomotopic M N) :
    (parityShift H).map f ∈ nullHomotopic ((parityShift H).obj M) ((parityShift H).obj N) := by
  obtain ⟨h, hh⟩ := mem_nullHomotopic_iff_exists.mp hf
  refine mem_nullHomotopic_iff_exists.mpr
    ⟨koszulSign 1 • (h.precomp (WeightCategory.shiftFunctor H.Regraded (-k))).shift 1, ?_⟩
  rw [CatModule.δ_units_smul, CatModule.Cochain.δ_shift, ← CatModule.Cochain.precomp_δ, ← hh,
    smul_smul, Int.units_mul_self, one_smul]
  rfl

/-- The parity shift preserves homotopy. -/
theorem homotopic_parityShift_map {f g : M ⟶ N} (h : Homotopic f g) :
    Homotopic ((parityShift H).map f) ((parityShift H).map g) := by
  rw [homotopic_iff_sub_mem, ← Functor.map_sub]
  exact parityShift_map_mem_nullHomotopic (homotopic_iff_sub_mem.mp h)

end HomEquiv

/-! ### Odd morphisms -/

section Odd

variable (M N : CatModule.{w} (WeightCategory H.Regraded))

/-- The odd closed maps `M → N` of internal degree `0` between half-graded dg modules: the
cocycles of degree `1` of the Hom complex `HOM_{C_H}(M, N⟨-k⟩)`. -/
abbrev OddCocycle : Type _ := CatModule.Cocycle M ((internalShiftFunctor H (-k)).obj N) 1

/-- Odd closed maps `M → N` are the even closed maps `M → Π N`, with the same underlying maps
(the right shift of cocycles, without sign). -/
def oddEquiv : OddCocycle H M N ≃+ (M ⟶ (parityShift H).obj N) where
  toFun z := (CatModule.Cocycle.homOf (z.rightShift 1 0 (zero_add 1)) :
    M ⟶ CatModule.shift 1 ((internalShiftFunctor H (-k)).obj N))
  invFun f := (CatModule.Cocycle.ofHom
    (N := CatModule.shift 1 ((internalShiftFunctor H (-k)).obj N)) f).rightUnshift 1 (zero_add 1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := hom_ext fun _ _ => rfl

variable {H M N}

@[simp]
theorem oddEquiv_apply_app (z : OddCocycle H M N) (i : WeightCategory H.Regraded) (x : M.obj i) :
    (oddEquiv H M N z).app i x = shift.mk 1 ((z : CatModule.Cochain M _ 1).app i x) :=
  rfl

@[simp]
theorem coe_oddEquiv_symm_app (f : M ⟶ (parityShift H).obj N) (i : WeightCategory H.Regraded)
    (x : M.obj i) :
    (((oddEquiv H M N).symm f : OddCocycle H M N) : CatModule.Cochain M _ 1).app i x =
      shift.unmk 1 (f.app i x) :=
  rfl

/-- An odd closed map is an odd coboundary iff the corresponding even map `M → Π N` is
null-homotopic. -/
theorem oddEquiv_mem_nullHomotopic_iff (z : OddCocycle H M N) :
    oddEquiv H M N z ∈ nullHomotopic M ((parityShift H).obj N) ↔
      z ∈ CatModule.Cocycle.coboundaries M ((internalShiftFunctor H (-k)).obj N) 1 := by
  let N' := (internalShiftFunctor H (-k)).obj N
  rw [mem_nullHomotopic_iff_exists, CatModule.Cocycle.mem_coboundaries_iff 0 (zero_add 1)]
  constructor
  · rintro ⟨h, hh⟩
    let h' : CatModule.Cochain M (CatModule.shift 1 N') (-1) := h
    refine ⟨koszulSign 1 • h'.rightUnshift 0 (neg_add_cancel 1), ?_⟩
    have e := CatModule.Cochain.δ_rightUnshift h' 0 (neg_add_cancel 1) 1 0 (zero_add 1)
    rw [CatModule.δ_units_smul, e, smul_smul, Int.units_mul_self, one_smul]
    change (CatModule.δ (-1) 0 h').rightUnshift 1 (zero_add 1) = _
    rw [← hh]
    rfl
  · rintro ⟨y, hy⟩
    refine ⟨koszulSign 1 • y.rightShift 1 (-1) (neg_add_cancel 1), ?_⟩
    rw [CatModule.δ_units_smul, CatModule.Cochain.δ_rightShift y 1 (-1) 0 (neg_add_cancel 1) 1
      (zero_add 1), smul_smul, Int.units_mul_self, one_smul, hy]
    rfl

variable (H M N) in
/-- Odd closed maps up to homotopy are even closed maps `M → Π N` up to homotopy. -/
def oddCohomologyEquiv :
    (OddCocycle H M N ⧸ CatModule.Cocycle.coboundaries M ((internalShiftFunctor H (-k)).obj N) 1)
      ≃+ ((M ⟶ (parityShift H).obj N) ⧸ nullHomotopic M ((parityShift H).obj N)) :=
  QuotientAddGroup.congr _ _ (oddEquiv H M N) (by
    ext f
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (oddEquiv_mem_nullHomotopic_iff z).mpr hz
    · intro hf
      refine ⟨(oddEquiv H M N).symm f, ?_, AddEquiv.apply_symm_apply _ _⟩
      rw [← oddEquiv_mem_nullHomotopic_iff, AddEquiv.apply_symm_apply]
      exact hf)

variable (H M N) in
/-- Odd closed maps `M → N` up to homotopy are the morphisms `M → Π N` of the homotopy category
`H(C_H)`. -/
def oddHomotopyEquiv :
    (OddCocycle H M N ⧸ CatModule.Cocycle.coboundaries M ((internalShiftFunctor H (-k)).obj N) 1)
      ≃+ ((HomotopyCategory.quotient _).obj M ⟶
        (HomotopyCategory.quotient _).obj ((parityShift H).obj N)) :=
  (oddCohomologyEquiv H M N).trans (HomotopyCategory.homAddEquivQuotient _ _).symm

theorem oddHomotopyEquiv_mk (z : OddCocycle H M N) :
    oddHomotopyEquiv H M N (QuotientAddGroup.mk z) =
      (HomotopyCategory.quotient _).map (oddEquiv H M N z) := by
  rw [oddHomotopyEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_eq,
    HomotopyCategory.homAddEquivQuotient_quotient_map]
  rfl

variable (H M N) in
/-- Odd closed maps `M → N` are the even closed maps `Π M → N`: `m ↦ u⁻¹ • z m`
(`DG.HalfGradedDGRing.oddEquiv'_apply_app`). -/
def oddEquiv' : OddCocycle H M N ≃+ ((parityShift H).obj M ⟶ N) :=
  (oddEquiv H M N).trans parityShiftHomEquiv.symm

theorem oddEquiv'_apply (z : OddCocycle H M N) :
    oddEquiv' H M N z = (parityShift H).map (oddEquiv H M N z) ≫ (parityShiftIsoObj H N).hom :=
  rfl

theorem oddEquiv'_apply_app (z : OddCocycle H M N) (i : WeightCategory H.Regraded)
    (x : M.obj ((WeightCategory.shiftFunctor H.Regraded (-k)).obj i)) :
    (oddEquiv' H M N z).app i (shift.mk 1 x) =
      N.act (unitInvHom H (twoBelow i) i (twoBelow_as i).symm) (z.1.app _ x) :=
  rfl

theorem oddEquiv_eq_parityShiftHomEquiv (z : OddCocycle H M N) :
    oddEquiv H M N z = parityShiftHomEquiv (oddEquiv' H M N z) :=
  (parityShiftHomEquiv.apply_symm_apply _).symm

/-- An odd closed map is an odd coboundary iff the corresponding even map `Π M → N` is
null-homotopic. -/
theorem oddEquiv'_mem_nullHomotopic_iff (z : OddCocycle H M N) :
    oddEquiv' H M N z ∈ nullHomotopic ((parityShift H).obj M) N ↔
      z ∈ CatModule.Cocycle.coboundaries M ((internalShiftFunctor H (-k)).obj N) 1 := by
  rw [← oddEquiv_mem_nullHomotopic_iff]
  constructor
  · intro h
    rw [oddEquiv_eq_parityShiftHomEquiv, parityShiftHomEquiv_apply]
    exact mem_nullHomotopic_comp (parityShift_map_mem_nullHomotopic h) _
  · intro h
    rw [oddEquiv'_apply]
    exact comp_mem_nullHomotopic (parityShift_map_mem_nullHomotopic h) _

/-! #### Composition -/

variable {P : CatModule.{w} (WeightCategory H.Regraded)}

/-- The composite `g ∘ z` of an odd closed map `z : M → N` and an even closed map
`g : N → P`, an odd closed map. -/
def compEven (z : OddCocycle H M N) (g : N ⟶ P) : OddCocycle H M P :=
  CatModule.Cocycle.mk ((CatModule.Cochain.ofHom ((internalShiftFunctor H (-k)).map g)).comp
    z.1 (add_zero 1)) 2 rfl (by
      rw [CatModule.δ_comp_ofHom, CatModule.Cocycle.δ_eq_zero,
        CatModule.Cochain.comp_zero])

/-- The composite `z ∘ f` of an even closed map `f : M → N` and an odd closed map
`z : N → P`, an odd closed map. -/
def evenComp (f : M ⟶ N) (z : OddCocycle H N P) : OddCocycle H M P :=
  CatModule.Cocycle.mk (z.1.comp (CatModule.Cochain.ofHom f)
    (zero_add 1)) 2 rfl (by
      rw [CatModule.δ_ofHom_comp, CatModule.Cocycle.δ_eq_zero,
        CatModule.Cochain.zero_comp])

theorem oddEquiv_compEven (z : OddCocycle H M N) (g : N ⟶ P) :
    oddEquiv H M P (compEven z g) = oddEquiv H M N z ≫ (parityShift H).map g :=
  hom_ext fun _ _ => rfl

theorem oddEquiv_evenComp (f : M ⟶ N) (z : OddCocycle H N P) :
    oddEquiv H M P (evenComp f z) = f ≫ oddEquiv H N P z :=
  hom_ext fun _ _ => rfl

variable (P) in
/-- The action of `u⁻¹`, as a cochain `P⟨-k⟩⟨-k⟩ → P` of degree `-2`. -/
def unitInvCochain : CatModule.Cochain ((internalShiftFunctor H (-k)).obj
    ((internalShiftFunctor H (-k)).obj P)) P (-2) where
  app i := P.act (unitInvHom H (twoBelow i) i (twoBelow_as i).symm)
  map_mem' {i n x} hx := by
    have := CatModule.smul_mem_grading (M := P) (unitInvHom_mem_grading (H := H)
      (twoBelow_as i).symm) hx
    rwa [add_comm] at this
  map_smul' {i j p f} hf x := by
    change P.act (unitInvHom H (twoBelow j) j _) (P.act (twoBelowMap f) x) =
      koszulSign (-2 * p) • P.act f (P.act (unitInvHom H (twoBelow i) i _) x)
    rw [show -2 * p = 2 * -p by ring, koszulSign_even (even_two_mul _), one_smul, act_apply,
      act_apply, act_apply, act_apply, ← comp_smul, ← comp_smul,
      comp_unitInvHom (twoBelowMap f) f rfl (twoBelow_as i).symm]

theorem δ_unitInvCochain : CatModule.δ (-2) (-1) (unitInvCochain (H := H) P) = 0 := by
  ext i x
  rw [CatModule.δ_apply _ _ (by norm_num)]
  change d (P.act (unitInvHom H (twoBelow i) i _) x) -
    koszulSign (-2) • P.act (unitInvHom H (twoBelow i) i _) (d x) = 0
  rw [act_apply, act_apply, CatModule.d_smul_of_d_eq_zero (unitInvHom_mem_grading _)
    (d_unitInvHom _), show (-2 : ℤ) = 2 * -1 by ring, koszulSign_even (even_two_mul _),
    one_smul]
  exact sub_self _

theorem δ_comp_eq_zero {M N P : CatModule.{w} (WeightCategory H.Regraded)} {n₁ n₂ n₁₂ : ℤ}
    (z₁ : CatModule.Cochain M N n₁) (z₂ : CatModule.Cochain N P n₂) (h : n₁ + n₂ = n₁₂) (m : ℤ)
    (h₁ : CatModule.δ n₁ (n₁ + 1) z₁ = 0) (h₂ : CatModule.δ n₂ (n₂ + 1) z₂ = 0) :
    CatModule.δ n₁₂ m (z₂.comp z₁ h) = 0 := by
  by_cases hm : n₁₂ + 1 = m
  · rw [CatModule.δ_comp z₁ z₂ h (n₁ + 1) (n₂ + 1) m hm rfl rfl, h₁, h₂,
      CatModule.Cochain.zero_comp, CatModule.Cochain.comp_zero, _root_.smul_zero, add_zero]
  · exact CatModule.δ_shape _ _ hm _

/-- The composite `z' ∘ z` of two odd closed maps `z : M → N` and `z' : N → P`: the even closed
map `u⁻¹ ∘ z'⟨-k⟩ ∘ z : M → P` (the underlying maps of `z` and `z'` composed, the result being
identified with a map of internal degree `0` and even parity through `u⁻¹`). -/
def oddComp (z : OddCocycle H M N) (z' : OddCocycle H N P) : M ⟶ P :=
  CatModule.Cocycle.homOf (CatModule.Cocycle.mk ((unitInvCochain P).comp
    ((z'.1.precomp (WeightCategory.shiftFunctor H.Regraded (-k))).comp
      z.1 (show (1 : ℤ) + 1 = 2 by norm_num))
      (show (2 : ℤ) + -2 = 0 by norm_num)) 1 (zero_add 1) (by
    refine δ_comp_eq_zero _ _ _ _ (δ_comp_eq_zero _ _ _ _ (CatModule.Cocycle.δ_eq_zero _ _) ?_)
      δ_unitInvCochain
    rw [← CatModule.Cochain.precomp_δ, CatModule.Cocycle.δ_eq_zero]
    rfl))

theorem oddComp_app (z : OddCocycle H M N) (z' : OddCocycle H N P)
    (i : WeightCategory H.Regraded) (x : M.obj i) :
    (oddComp z z').app i x = P.act (unitInvHom H (twoBelow i) i (twoBelow_as i).symm)
      (z'.1.app _ (z.1.app i x)) :=
  rfl

/-- The composite of two odd closed maps corresponds to the composite of the even closed maps
`M → Π N → Π Π P ≅ P`. -/
theorem oddComp_eq (z : OddCocycle H M N) (z' : OddCocycle H N P) :
    oddComp z z' = oddEquiv H M N z ≫ (parityShift H).map (oddEquiv H N P z') ≫
      (parityShiftIsoObj H P).hom :=
  hom_ext fun _ _ => rfl

/-- The composite of two odd closed maps is the composite `M → Π N → P` of the corresponding
even closed maps. -/
theorem oddComp_eq' (z : OddCocycle H M N) (z' : OddCocycle H N P) :
    oddComp z z' = oddEquiv H M N z ≫ oddEquiv' H N P z' := by
  rw [oddComp_eq, oddEquiv'_apply]

theorem oddEquiv'_compEven (z : OddCocycle H M N) (g : N ⟶ P) :
    oddEquiv' H M P (compEven z g) = oddEquiv' H M N z ≫ g := by
  rw [oddEquiv'_apply, oddEquiv'_apply, oddEquiv_compEven, Functor.map_comp, assoc, assoc]
  congr 1
  exact (parityShiftIso H).hom.naturality g

theorem oddEquiv'_evenComp (f : M ⟶ N) (z : OddCocycle H N P) :
    oddEquiv' H M P (evenComp f z) = (parityShift H).map f ≫ oddEquiv' H N P z := by
  rw [oddEquiv'_apply, oddEquiv'_apply, oddEquiv_evenComp, Functor.map_comp, assoc]

end Odd

end HalfGradedDGRing

end DG

end
