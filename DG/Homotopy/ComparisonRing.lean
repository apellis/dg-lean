import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import DG.Derived.QuasiIso
import DG.Homotopy.ForgetRing

/-!
# Dg modules over a ring in degree `0` are cochain complexes

Let `S` be a ring, not necessarily commutative, regarded as a dg ring concentrated in degree `0`
(the scoped instances of `DG.DegreeZero`). This file shows that the functor
`DG.DegreeZero.complexFunctor S : DGModuleCat S ⥤ CochainComplex (ModuleCat S) ℤ`
(`DG/Homotopy/ForgetRing.lean`) is an equivalence of categories, with inverse `K ↦ ⨁ n, Kⁿ`
(`DG.DGModuleCat.ofComplex S`), that the induced triangulated functor on homotopy categories is
an equivalence, and that it detects quasi-isomorphisms. This generalizes
`DG/Homotopy/Comparison.lean` (commutative rings, where the ring is also used as ground ring).

## Main definitions and results

* `DG.DegreeZero.ofHomComplex`: cochains of Mathlib's Hom complex of the underlying complexes as
  cochains of `HOM_S(M, N)`, inverse to `DG.DegreeZero.toHomComplex`;
  `DG.DegreeZero.homOfComplexHom`, `DG.DegreeZero.complexFunctor_full`,
  `DG.DegreeZero.ofHomotopy`, `DG.DegreeZero.homotopic_iff`.
* `DG.DegreeZero.complexEquivalence S : DGModuleCat S ≌ CochainComplex (ModuleCat S) ℤ`.
* `DG.DegreeZero.homotopyFunctor_isEquivalence`, `DG.DegreeZero.homotopyEquivalence S`.
* `DG.DegreeZero.cohomologyAddEquiv`: the cohomology of `M` is the homology of its underlying
  complex, naturally (`DG.DegreeZero.cohomologyAddEquiv_naturality`);
  `DG.DegreeZero.mem_quasiIso_iff`: a morphism of the homotopy category is a
  quasi-isomorphism iff its image is one.
-/

open CategoryTheory Category Limits

universe v u

set_option backward.isDefEq.respectTransparency false

namespace DG

namespace DegreeZero

variable {S : Type u} [Ring S]

/-! ### Cochains of the underlying complexes -/

section Cochain

variable {M N : DGModuleCat.{v} S} {n : ℤ}

/-- The degree-`p` component of a cochain of Mathlib's Hom complex, as an additive map on
`Mᵖ`. -/
def ofHomComplexAux
    (z : CochainComplex.HomComplex.Cochain ((complexFunctor S).obj M) ((complexFunctor S).obj N) n)
    (p : ℤ) : grading (M := M) p →+ N where
  toFun x := ((z.v p (p + n) rfl).hom ⟨x.1, x.2⟩).1
  map_zero' := by
    change ((z.v p (p + n) rfl).hom 0).1 = 0
    rw [map_zero]
    rfl
  map_add' x y := by
    change ((z.v p (p + n) rfl).hom (⟨x.1, x.2⟩ + ⟨y.1, y.2⟩)).1 = _
    rw [map_add]
    rfl

/-- A cochain of Mathlib's Hom complex of the underlying complexes of two dg modules over `S` as
a cochain of the Hom complex `HOM_S(M, N)`: the inverse of `DG.DegreeZero.toHomComplex`. -/
def ofHomComplex
    (z : CochainComplex.HomComplex.Cochain ((complexFunctor S).obj M) ((complexFunctor S).obj N)
      n) :
    Cochain S M N n where
  toAddMonoidHom := liftHomogeneous (grading (M := M)) (ofHomComplexAux z)
  map_mem' p x hx := by
    change liftHomogeneous (grading (M := M)) (ofHomComplexAux z) x ∈ _
    rw [liftHomogeneous_of_mem _ _ hx]
    exact ((z.v p (p + n) rfl).hom ⟨x, hx⟩).2
  map_smul' {i a} ha x := by
    change liftHomogeneous (grading (M := M)) (ofHomComplexAux z) (a • x) =
      _ • (a • liftHomogeneous (grading (M := M)) (ofHomComplexAux z) x)
    rcases mem_grading_iff.mp ha with rfl | rfl
    · rw [mul_zero, koszulSign_zero, one_smul]
      induction x using DG.induction_on with
      | h_zero => simp
      | @h_homogeneous p x =>
        have hx : a • (x : M) ∈ grading (M := M) p := ring_smul_mem a x.2
        rw [liftHomogeneous_of_mem _ _ hx, liftHomogeneous_coe]
        exact congrArg Subtype.val ((z.v p (p + n) rfl).hom.map_smul a ⟨x.1, x.2⟩)
      | h_add x y hx hy => simp only [smul_add, map_add, hx, hy]
    · simp

@[simp]
theorem ofHomComplex_apply_coe
    (z : CochainComplex.HomComplex.Cochain ((complexFunctor S).obj M) ((complexFunctor S).obj N)
      n) {p : ℤ} (x : grading (M := M) p) :
    ofHomComplex z x = ((z.v p (p + n) rfl).hom ⟨x.1, x.2⟩).1 :=
  liftHomogeneous_coe _ _ x

@[simp]
theorem toHomComplex_ofHomComplex
    (z : CochainComplex.HomComplex.Cochain ((complexFunctor S).obj M) ((complexFunctor S).obj N)
      n) :
    toHomComplex (ofHomComplex z) = z :=
  toHomComplex_ext fun p q hpq x => by
    subst hpq
    exact ofHomComplex_apply_coe z ⟨x.1, x.2⟩

theorem toHomComplex_injective :
    Function.Injective (toHomComplex (M := M) (N := N) (n := n)) := by
  intro z₁ z₂ h
  ext x
  induction x using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous p x =>
    exact congrArg (fun z => (((z.v p (p + n) rfl).hom
      ⟨x.1, x.2⟩ : gradingSubmodule S N (p + n)) : N)) h
  | h_add x y hx hy => rw [map_add, map_add, hx, hy]

/-- A morphism between the underlying complexes of two dg modules over `S` as a morphism of dg
modules (the preimage under `DG.DegreeZero.complexFunctor S`). -/
def homOfComplexHom (φ : (complexFunctor S).obj M ⟶ (complexFunctor S).obj N) : M ⟶ N :=
  DGModuleCat.ofHom (Cocycle.homOf ⟨ofHomComplex (CochainComplex.HomComplex.Cochain.ofHom φ), by
    rw [Cocycle.mem_iff 1 (zero_add 1)]
    apply toHomComplex_injective
    rw [toHomComplex_δ, toHomComplex_ofHomComplex, CochainComplex.HomComplex.δ_ofHom,
      toHomComplex_zero]⟩)

@[simp]
theorem complexFunctor_map_homOfComplexHom
    (φ : (complexFunctor S).obj M ⟶ (complexFunctor S).obj N) :
    (complexFunctor S).map (homOfComplexHom φ) = φ := by
  apply CochainComplex.HomComplex.Cochain.ofHom_injective
  rw [← toHomComplex_ofHom]
  exact toHomComplex_ofHomComplex _

/-- The functor to cochain complexes is full. -/
instance complexFunctor_full : (complexFunctor.{v} S).Full where
  map_surjective φ := ⟨homOfComplexHom φ, complexFunctor_map_homOfComplexHom φ⟩

/-- The functor to cochain complexes is fully faithful. -/
noncomputable def complexFunctorFullyFaithful : (complexFunctor.{v} S).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- A homotopy between the underlying morphisms of complexes of two morphisms of dg modules over
`S` gives a homotopy of dg modules: the converse of `DG.DegreeZero.toHomotopy`. -/
noncomputable def ofHomotopy {f g : M ⟶ N}
    (h : Homotopy ((complexFunctor S).map f) ((complexFunctor S).map g)) :
    DGHomotopy f.hom g.hom where
  hom := ofHomComplex (CochainComplex.HomComplex.Cochain.equivHomotopy _ _ h).1
  ofHom_eq := by
    apply toHomComplex_injective
    rw [toHomComplex_add, toHomComplex_δ, toHomComplex_ofHomComplex, toHomComplex_ofHom,
      toHomComplex_ofHom]
    exact (CochainComplex.HomComplex.Cochain.equivHomotopy _ _ h).2

/-- Two morphisms of dg modules over `S` are homotopic iff their underlying morphisms of cochain
complexes are homotopic. -/
theorem homotopic_iff (f g : M ⟶ N) :
    Homotopic f.hom g.hom ↔
      Nonempty (Homotopy ((complexFunctor S).map f) ((complexFunctor S).map g)) :=
  ⟨fun ⟨h⟩ => ⟨toHomotopy h⟩, fun ⟨h⟩ => ⟨ofHomotopy h⟩⟩

end Cochain

/-! ### The inverse functor -/

section Inverse

open DGModuleCat

variable (K : CochainComplex (ModuleCat.{u} S) ℤ)

/-- The degree-`n` component of the underlying complex of `⨁ n, Kⁿ` is `Kⁿ`. -/
noncomputable def ofComplexXEquiv (n : ℤ) :
    (toComplex S ((ofComplex S).obj K)).X n ≃ₗ[S] K.X n where
  toFun z := ComplexSum.component K n z.1
  map_add' z z' := map_add (ComplexSum.component K n) z.1 z'.1
  map_smul' s z := map_smul (ComplexSum.component K n) s z.1
  invFun x := ⟨ComplexSum.of K n x, ComplexSum.of_mem_grading n x⟩
  left_inv z := Subtype.ext (ComplexSum.of_component_of_mem z.2)
  right_inv x := ComplexSum.component_of_same n x

/-- The underlying complex of `⨁ n, Kⁿ` is `K`. -/
noncomputable def ofComplexIso : toComplex S ((ofComplex S).obj K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (ofComplexXEquiv K n).toModuleIso) (by
      rintro n _ rfl
      rw [toComplex_d]
      ext ⟨_, x, rfl⟩
      change K.d n (n + 1) (ComplexSum.component K n (ComplexSum.of K n x)) =
        ComplexSum.component K (n + 1) (d (ComplexSum.of K n x))
      rw [ComplexSum.d_of, ComplexSum.component_of_same, ComplexSum.component_of_same])

variable (S) in
/-- The underlying complex of `⨁ n, Kⁿ` is `K`, naturally in `K`. -/
noncomputable def ofComplexCompIso : ofComplex S ⋙ complexFunctor.{u} S ≅ 𝟭 _ :=
  NatIso.ofComponents ofComplexIso fun {K L} φ => by
    ext n ⟨_, x, rfl⟩
    change ComplexSum.component L n (ComplexSum.map φ (ComplexSum.of K n x)) =
      φ.f n (ComplexSum.component K n (ComplexSum.of K n x))
    rw [ComplexSum.map_of, ComplexSum.component_of_same, ComplexSum.component_of_same]

variable (S) in
/-- **Dg modules over a ring `S` concentrated in degree `0` are cochain complexes of
`S`-modules**: `DG.DegreeZero.complexFunctor S` is an equivalence of categories, with inverse
`K ↦ ⨁ n, Kⁿ`. -/
@[simps functor inverse]
noncomputable def complexEquivalence :
    DGModuleCat.{u} S ≌ CochainComplex (ModuleCat.{u} S) ℤ where
  functor := complexFunctor S
  inverse := ofComplex S
  unitIso := NatIso.ofComponents
    (fun M => complexFunctorFullyFaithful.preimageIso ((ofComplexCompIso S).app _).symm)
    fun {M N} f => (complexFunctor S).map_injective (by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
        Functor.FullyFaithful.map_preimage, Iso.symm_hom, Iso.app_inv]
      exact (ofComplexCompIso S).inv.naturality ((complexFunctor S).map f))
  counitIso := ofComplexCompIso S
  functor_unitIso_comp M := by
    simp only [Functor.id_obj, Functor.comp_obj, NatIso.ofComponents_hom_app,
      Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage, Iso.symm_hom,
      Iso.app_inv]
    exact (ofComplexCompIso S).inv_hom_id_app _

instance complexFunctor_isEquivalence : (complexFunctor.{u} S).IsEquivalence :=
  (complexEquivalence S).isEquivalence_functor

end Inverse

/-! ### The homotopy categories -/

section Homotopy

open _root_.DG.HomotopyCategory

/-- The functor on homotopy categories is full. -/
instance homotopyFunctor_full : (homotopyFunctor.{v} S).Full where
  map_surjective {X Y} φ := by
    obtain ⟨M, rfl⟩ := quotient_obj_surjective X
    obtain ⟨N, rfl⟩ := quotient_obj_surjective Y
    obtain ⟨ψ, rfl⟩ := (_root_.HomotopyCategory.quotient _ _).map_surjective
      (X := (complexFunctor S).obj M) (Y := (complexFunctor S).obj N) φ
    exact ⟨(quotient S).map (homOfComplexHom ψ), by
      rw [homotopyFunctor_map_quotient_map, complexFunctor_map_homOfComplexHom]⟩

/-- The functor on homotopy categories is faithful. -/
instance homotopyFunctor_faithful : (homotopyFunctor.{v} S).Faithful where
  map_injective {X Y f g} h := by
    obtain ⟨M, rfl⟩ := quotient_obj_surjective X
    obtain ⟨N, rfl⟩ := quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := (quotient S).map_surjective f
    obtain ⟨g, rfl⟩ := (quotient S).map_surjective g
    rw [homotopyFunctor_map_quotient_map, homotopyFunctor_map_quotient_map] at h
    exact eq_of_homotopy _ _ (ofHomotopy (_root_.HomotopyCategory.homotopyOfEq _ _ h))

/-- The functor on homotopy categories is essentially surjective. -/
instance homotopyFunctor_essSurj : (homotopyFunctor.{u} S).EssSurj where
  mem_essImage Y := by
    obtain ⟨K, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective Y
    exact ⟨(quotient S).obj ((DGModuleCat.ofComplex S).obj K),
      ⟨(_root_.HomotopyCategory.quotient _ _).mapIso ((ofComplexCompIso S).app K)⟩⟩

/-- The functor on homotopy categories is an equivalence. -/
instance homotopyFunctor_isEquivalence : (homotopyFunctor.{u} S).IsEquivalence where

variable (S) in
/-- The homotopy category of dg modules over a ring `S` concentrated in degree `0` is equivalent
to Mathlib's homotopy category of cochain complexes of `S`-modules; the functor is triangulated
(`DG.DegreeZero.homotopyFunctor_isTriangulated`). -/
noncomputable def homotopyEquivalence :
    HomotopyCategory.{u} S ≌ _root_.HomotopyCategory (ModuleCat.{u} S) (ComplexShape.up ℤ) :=
  (homotopyFunctor S).asEquivalence

@[simp]
theorem homotopyEquivalence_functor :
    (homotopyEquivalence S).functor = homotopyFunctor S := rfl

end Homotopy

/-! ### Cohomology and quasi-isomorphisms -/

section Cohomology

variable (M : DGModuleCat.{v} S)

set_option backward.isDefEq.respectTransparency false in
/-- The cocycles of degree `n` of `M` are the kernel of the differential of the short complex
`(toComplex S M).sc n`. -/
def cocyclesAddEquiv (n : ℤ) :
    cocycles M n ≃+ LinearMap.ker ((toComplex S M).sc n).g.hom where
  toFun z := ⟨⟨z, (cocycles.mem_grading z : _)⟩, Subtype.ext (by
    rw [ZeroMemClass.coe_zero]
    exact (toComplex_d_apply M (CochainComplex.next ℤ n).symm _).trans (cocycles.d_eq_zero z))⟩
  invFun y := ⟨y.1.1, y.1.2,
    (toComplex_d_apply M (CochainComplex.next ℤ n).symm y.1).symm.trans
      (congrArg Subtype.val y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem prev_add_one (n : ℤ) : (ComplexShape.up ℤ).prev n + 1 = n := by
  rw [CochainComplex.prev]; omega

theorem mem_map_cocyclesAddEquiv_iff (n : ℤ) (y : LinearMap.ker ((toComplex S M).sc n).g.hom) :
    y ∈ ((coboundaries M n).addSubgroupOf (cocycles M n)).map
      (cocyclesAddEquiv M n).toAddMonoidHom ↔
      y ∈ LinearMap.range ((toComplex S M).sc n).moduleCatToCycles := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨m, hm, hmz⟩ := AddSubgroup.mem_addSubgroupOf.mp hz
    refine ⟨⟨m, ?_⟩, Subtype.ext (Subtype.ext ?_)⟩
    · change m ∈ grading _
      rwa [CochainComplex.prev]
    · exact (toComplex_d_apply M (prev_add_one n) _).trans hmz
  · rintro ⟨⟨x, hx⟩, rfl⟩
    refine ⟨(cocyclesAddEquiv M n).symm (((toComplex S M).sc n).moduleCatToCycles ⟨x, hx⟩),
      AddSubgroup.mem_addSubgroupOf.mpr ⟨x, ?_, ?_⟩, (cocyclesAddEquiv M n).apply_symm_apply _⟩
    · change x ∈ grading _ at hx
      rwa [CochainComplex.prev] at hx
    · exact (toComplex_d_apply M (prev_add_one n) ⟨x, hx⟩).symm

/-- The comparison `Hⁿ(M) ≃+ Hⁿ(toComplex S M)` between the cohomology of a dg module over `S`
and the homology of its underlying cochain complex of `S`-modules. -/
noncomputable def cohomologyAddEquiv (n : ℤ) :
    cohomology M n ≃+ ((complexFunctor S).obj M).homology n :=
  (QuotientAddGroup.congr _ _ (cocyclesAddEquiv M n) (AddSubgroup.ext fun y =>
      (mem_map_cocyclesAddEquiv_iff M n y).trans Iff.rfl)).trans
    (((toComplex S M).sc n).moduleCatHomologyIso.symm.toLinearEquiv.toAddEquiv)

set_option backward.isDefEq.respectTransparency false in
theorem cohomologyAddEquiv_mk (n : ℤ) (z : cocycles M n) :
    cohomologyAddEquiv M n (cohomology.mk M n z) =
      (forget₂ (ModuleCat S) Ab).map (((complexFunctor S).obj M).homologyπ n)
        (((complexFunctor S).obj M).cyclesMk
          (⟨z, cocycles.mem_grading z⟩ : gradingSubmodule S M n) (n + 1)
          (CochainComplex.next ℤ n)
          (Subtype.ext ((toComplex_d_apply M rfl _).trans (cocycles.d_eq_zero z)))) := by
  change ((toComplex S M).sc n).moduleCatHomologyIso.inv
    (((toComplex S M).sc n).moduleCatLeftHomologyData.π (cocyclesAddEquiv M n z)) = _
  rw [← ShortComplex.moduleCatCyclesIso_inv_π_apply]
  change ((toComplex S M).sc n).homologyπ _ = ((toComplex S M).sc n).homologyπ _
  congr 1
  apply (ModuleCat.mono_iff_injective ((toComplex S M).iCycles n)).1 inferInstance
  change ((toComplex S M).sc n).iCycles _ = _
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_apply]
  exact (HomologicalComplex.i_cyclesMk (toComplex S M) _ _ _ _).symm

variable {M} {N : DGModuleCat.{v} S} (f : M ⟶ N)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison `Hⁿ(M) ≃+ Hⁿ(toComplex S M)` is natural in `M`. -/
theorem cohomologyAddEquiv_naturality (n : ℤ) (x : cohomology M n) :
    cohomologyAddEquiv N n (cohomology.map f.hom n x) =
      HomologicalComplex.homologyMap ((complexFunctor S).map f) n (cohomologyAddEquiv M n x) := by
  induction x using cohomology.induction_on with
  | h z =>
    rw [cohomology.map_mk, cohomologyAddEquiv_mk, cohomologyAddEquiv_mk]
    change _ = (((complexFunctor S).obj M).homologyπ n ≫
      HomologicalComplex.homologyMap ((complexFunctor S).map f) n) _
    rw [HomologicalComplex.homologyπ_naturality]
    change ((complexFunctor S).obj N).homologyπ n _ = ((complexFunctor S).obj N).homologyπ n _
    congr 1
    apply (ModuleCat.mono_iff_injective (((complexFunctor S).obj N).iCycles n)).1 inferInstance
    change _ = (HomologicalComplex.cyclesMap ((complexFunctor S).map f) n ≫
      ((complexFunctor S).obj N).iCycles n) _
    rw [HomologicalComplex.cyclesMap_i]
    refine (HomologicalComplex.i_cyclesMk ((complexFunctor S).obj N) _ _ _ _).trans ?_
    change _ = ((complexFunctor S).map f).f n
      ((forget₂ (ModuleCat S) Ab).map (((complexFunctor S).obj M).iCycles n) _)
    rw [HomologicalComplex.i_cyclesMk]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of dg modules over `S` is a quasi-isomorphism iff its underlying morphism of
complexes of `S`-modules is a quasi-isomorphism. -/
theorem homotopyFunctor_map_quotient_map_mem_quasiIso_iff :
    _root_.HomotopyCategory.quasiIso (ModuleCat.{v} S) (ComplexShape.up ℤ)
      ((homotopyFunctor S).map ((HomotopyCategory.quotient S).map f)) ↔ f.hom.IsQuasiIso := by
  rw [homotopyFunctor_map_quotient_map, _root_.HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
  refine forall_congr' fun n => ?_
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  have h : ⇑(HomologicalComplex.homologyMap ((complexFunctor S).map f) n) ∘
      ⇑(cohomologyAddEquiv M n) = ⇑(cohomologyAddEquiv N n) ∘ ⇑(cohomology.map f.hom n) :=
    funext fun x => (cohomologyAddEquiv_naturality f n x).symm
  rw [← Function.Bijective.of_comp_iff _ (cohomologyAddEquiv M n).bijective, h,
    Function.Bijective.of_comp_iff' (cohomologyAddEquiv N n).bijective]

/-- The quasi-isomorphisms of the homotopy category of dg modules over `S` are the morphisms
whose image in Mathlib's homotopy category of complexes of `S`-modules is a
quasi-isomorphism. -/
theorem mem_quasiIso_iff {X Y : HomotopyCategory.{v} S} (g : X ⟶ Y) :
    HomotopyCategory.quasiIso S g ↔ _root_.HomotopyCategory.quasiIso (ModuleCat.{v} S)
      (ComplexShape.up ℤ) ((homotopyFunctor S).map g) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient S).map_surjective g
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
    homotopyFunctor_map_quotient_map_mem_quasiIso_iff]

end Cohomology

end DegreeZero

end DG
