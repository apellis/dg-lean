import DG.Algebra.Hom
import DG.Module.Corner
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Constructions of dg rings: graded objects, ideals, quotients and subrings

* `DG.Decomposition.map`: transport of a `DirectSum.Decomposition` to the image under a
  surjective additive map with homogeneous kernel (the transport to a homogeneous subobject is
  `DG.DGAddCommGroup.ofInjective`).
* `DG.DGAddCommGroup.ofGraded`, `DG.DGRing.ofGradedRing`: a graded abelian group, resp. a
  graded ring, as a dg object with `d = 0`.
* `DG.degreeZeroGrading`, `DG.DGAddCommGroup.degreeZero`, `DG.DGRing.degreeZero`,
  `DG.DGAlgebra.degreeZero`: a ring `R` concentrated in degree `0`, as a dg `R`-algebra.
* `DG.DGIdeal A`: dg ideals (two-sided, homogeneous, `d`-stable), the quotient dg ring `A ⧸ I`
  with the quotient map `DG.DGIdeal.Quotient.mk`, the kernel `DG.DGRingHom.ker` of a morphism.
* `DG.DGSubring A`: dg subrings (homogeneous, `d`-stable) with the induced dg ring structure and
  the inclusion `DG.DGSubring.subtype`.
* `DG.cocyclesSubring A`, `DG.cocyclesDGSubring A`: the cocycles `Z(A) = ker d` form a dg
  subring with `d = 0`; `DG.coboundariesDGIdeal A`: the coboundaries `B(A) = im d` form a dg
  ideal of `Z(A)`.

The constructions producing `DGAddCommGroup` data are definitions, not instances, since the
underlying type may already carry a differential.
-/

open DirectSum

namespace DG

/-! ### Transport of decompositions -/

section Decomposition

variable {ι M N : Type*} [DecidableEq ι] [AddCommGroup M] [AddCommGroup N]
  (ℳ : ι → AddSubgroup M) (f : M →+ N)

/-- The map on direct sums induced by `f` on the graded pieces. -/
def Decomposition.mapAux : (⨁ i, ℳ i) →+ ⨁ i, (ℳ i).map f :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.of (fun i => (ℳ i).map f) i).comp
      (((f.comp (ℳ i).subtype).codRestrict ((ℳ i).map f)) fun x => ⟨x, x.2, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem Decomposition.mapAux_of (i : ι) (x : ℳ i) :
    Decomposition.mapAux ℳ f (DirectSum.of _ i x) =
      DirectSum.of (fun i => (ℳ i).map f) i ⟨f x, x, x.2, rfl⟩ := by
  simp [Decomposition.mapAux]

theorem Decomposition.coe_mapAux (z : ⨁ i, ℳ i) :
    (DirectSum.coeAddMonoidHom (fun i => (ℳ i).map f) (Decomposition.mapAux ℳ f z) : N) =
      f (DirectSum.coeAddMonoidHom ℳ z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of j x => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']

theorem Decomposition.mapAux_surjective : Function.Surjective (Decomposition.mapAux ℳ f) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of j y =>
    obtain ⟨y, x, hx, rfl⟩ := y
    exact ⟨DirectSum.of _ j ⟨x, hx⟩, by simp⟩
  | add y y' hy hy' =>
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨z', rfl⟩ := hy'
    exact ⟨z + z', map_add _ _ _⟩

variable [Decomposition ℳ]

theorem Decomposition.mapAux_decompose_eq_of_mem_ker (hker : SetLike.IsHomogeneous ℳ f.ker)
    {a : M} (ha : a ∈ f.ker) : Decomposition.mapAux ℳ f (decompose ℳ a) = 0 := by
  classical
  rw [← DirectSum.sum_support_of (decompose ℳ a), map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Decomposition.mapAux_of]
  have h0 : (⟨f (decompose ℳ a i), _, (decompose ℳ a i).2, rfl⟩ : (ℳ i).map f) = 0 :=
    Subtype.ext (AddMonoidHom.mem_ker.mp (hker i ha))
  rw [h0, map_zero]

theorem Decomposition.mapAux_decompose_eq (hker : SetLike.IsHomogeneous ℳ f.ker) {a b : M}
    (h : f a = f b) :
    Decomposition.mapAux ℳ f (decompose ℳ a) = Decomposition.mapAux ℳ f (decompose ℳ b) := by
  rw [← sub_eq_zero, ← map_sub, ← decompose_sub]
  exact Decomposition.mapAux_decompose_eq_of_mem_ker ℳ f hker
    (by rw [AddMonoidHom.mem_ker, map_sub, h, sub_self])

/-- The image of a graded abelian group under a surjective additive map with homogeneous kernel
is graded by the images of the graded pieces. -/
@[instance_reducible]
noncomputable def Decomposition.map (hf : Function.Surjective f)
    (hker : SetLike.IsHomogeneous ℳ f.ker) : Decomposition fun i => (ℳ i).map f where
  decompose' y := Decomposition.mapAux ℳ f (decompose ℳ (Function.surjInv hf y))
  left_inv y := by
    rw [Decomposition.coe_mapAux]
    change f ((decompose ℳ).symm (decompose ℳ _)) = y
    rw [Equiv.symm_apply_apply, Function.surjInv_eq hf]
  right_inv y := by
    obtain ⟨z, rfl⟩ := Decomposition.mapAux_surjective ℳ f y
    change Decomposition.mapAux ℳ f (decompose ℳ (Function.surjInv hf _)) = _
    refine (Decomposition.mapAux_decompose_eq ℳ f hker
      (b := DirectSum.coeAddMonoidHom ℳ z) ?_).trans ?_
    · rw [Function.surjInv_eq hf, Decomposition.coe_mapAux]
    · congr 1
      exact (decompose ℳ).apply_symm_apply z

end Decomposition

/-! ### Graded objects as dg objects with zero differential -/

section OfGraded

variable {M : Type*} [AddCommGroup M]

/-- A graded abelian group as a dg abelian group with `d = 0`. Not an instance, since `M` may
already carry a differential. -/
@[instance_reducible]
def DGAddCommGroup.ofGraded (ℳ : ℤ → AddSubgroup M) [Decomposition ℳ] : DGAddCommGroup M where
  grading := ℳ
  d := 0
  d_mem' _ := zero_mem _
  d_d' _ := rfl

@[simp]
theorem DGAddCommGroup.ofGraded_grading (ℳ : ℤ → AddSubgroup M) [Decomposition ℳ] :
    (DGAddCommGroup.ofGraded ℳ).grading = ℳ := rfl

@[simp]
theorem DGAddCommGroup.ofGraded_d (ℳ : ℤ → AddSubgroup M) [Decomposition ℳ] :
    (DGAddCommGroup.ofGraded ℳ).d = 0 := rfl

variable {A : Type*} [Ring A]

/-- A graded ring as a dg ring with `d = 0`. -/
theorem DGRing.ofGradedRing (𝒜 : ℤ → AddSubgroup A) [GradedRing 𝒜] :
    letI := DGAddCommGroup.ofGraded 𝒜
    DGRing A :=
  letI := DGAddCommGroup.ofGraded 𝒜
  { toGradedMonoid := inferInstanceAs (SetLike.GradedMonoid 𝒜)
    d_mul' := fun _ _ => by simp }

end OfGraded

/-! ### The ground ring in degree `0` -/

section DegreeZero

variable (R : Type*) [AddCommGroup R]

/-- The grading of `R` concentrated in degree `0`. -/
def degreeZeroGrading : ℤ → AddSubgroup R := fun n => if n = 0 then ⊤ else ⊥

@[simp]
theorem degreeZeroGrading_zero : degreeZeroGrading R 0 = ⊤ := ite_eq_left rfl

theorem degreeZeroGrading_of_ne {n : ℤ} (hn : n ≠ 0) : degreeZeroGrading R n = ⊥ := ite_eq_right hn

theorem mem_degreeZeroGrading_zero (r : R) : r ∈ degreeZeroGrading R 0 := by simp

theorem mem_degreeZeroGrading_iff {n : ℤ} {r : R} :
    r ∈ degreeZeroGrading R n ↔ n = 0 ∨ r = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · simp [degreeZeroGrading_of_ne R hn, hn]

/-- The inclusion of `R` as the degree-`0` piece of `degreeZeroGrading R`. -/
def degreeZeroGrading.ofHom : R →+ degreeZeroGrading R 0 :=
  (AddMonoidHom.id R).codRestrict _ (mem_degreeZeroGrading_zero R)

/-- The decomposition of `R` concentrated in degree `0`. -/
instance degreeZeroGrading.decomposition : Decomposition (degreeZeroGrading R) where
  decompose' := (DirectSum.of (fun n => degreeZeroGrading R n) 0).comp (degreeZeroGrading.ofHom R)
  left_inv r := by simp [degreeZeroGrading.ofHom]
  right_inv z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of n x =>
      obtain ⟨x, hx⟩ := x
      rcases (mem_degreeZeroGrading_iff R).mp hx with rfl | rfl
      · simp only [coeAddMonoidHom_of]
        rfl
      · rw [coeAddMonoidHom_of]
        exact (map_zero ((DirectSum.of (fun n => degreeZeroGrading R n) 0).comp
          (degreeZeroGrading.ofHom R))).trans
            (map_zero (DirectSum.of (fun n => degreeZeroGrading R n) n)).symm
    | add z z' hz hz' => simp only [map_add, hz, hz']

/-- `R` concentrated in degree `0`, as a dg abelian group with `d = 0`. Not an instance, since
`R` may already carry a grading. -/
@[instance_reducible]
def DGAddCommGroup.degreeZero : DGAddCommGroup R :=
  DGAddCommGroup.ofGraded (degreeZeroGrading R)

end DegreeZero

section DegreeZeroRing

variable (R : Type*) [Ring R]

/-- `R` concentrated in degree `0`, as a dg ring with `d = 0`. -/
theorem DGRing.degreeZero :
    letI := DGAddCommGroup.degreeZero R
    DGRing R :=
  letI := DGAddCommGroup.degreeZero R
  { one_mem := mem_degreeZeroGrading_zero R 1
    mul_mem := fun i j a b ha hb => by
      change a ∈ degreeZeroGrading R i at ha
      change b ∈ degreeZeroGrading R j at hb
      change a * b ∈ degreeZeroGrading R (i + j)
      rw [mem_degreeZeroGrading_iff] at ha hb ⊢
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · simp
        · simp
      · simp
    d_mul' := fun _ _ => by
      change (0 : R →+ R) _ = (0 : R →+ R) _ * _ + _ • (_ * (0 : R →+ R) _)
      simp }

/-- `R` concentrated in degree `0` is a dg `R`-algebra. -/
theorem DGAlgebra.degreeZero (R : Type*) [CommRing R] :
    letI := DGAddCommGroup.degreeZero R
    haveI := DGRing.degreeZero R
    DGAlgebra R R :=
  letI := DGAddCommGroup.degreeZero R
  haveI := DGRing.degreeZero R
  { algebraMap_mem' := fun _ => mem_degreeZeroGrading_zero R _
    d_algebraMap' := fun _ => rfl }

end DegreeZeroRing


/-! ### dg ideals and quotients -/

/-- A dg ideal of a dg ring `A`: a two-sided ideal which is homogeneous and stable under `d`. -/
structure DGIdeal (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] extends Ideal A where
  mul_mem_right' : ∀ {a : A} (b : A), a ∈ carrier → a * b ∈ carrier
  isHomogeneous' : Ideal.IsHomogeneous (grading (M := A)) toSubmodule
  d_mem' : ∀ {a : A}, a ∈ carrier → d a ∈ carrier

namespace DGIdeal

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The underlying (left) ideal of a dg ideal. -/
def toIdeal (I : DGIdeal A) : Ideal A := I.toSubmodule

instance : SetLike (DGIdeal A) A where
  coe I := I.toIdeal
  coe_injective I J h := by
    cases I
    cases J
    congr
    exact SetLike.coe_injective h

instance : PartialOrder (DGIdeal A) := .ofSetLike (DGIdeal A) A

@[simp]
theorem mem_toIdeal {I : DGIdeal A} {a : A} : a ∈ I.toIdeal ↔ a ∈ I := Iff.rfl

@[simp]
theorem coe_toIdeal (I : DGIdeal A) : (I.toIdeal : Set A) = I := rfl

theorem toIdeal_injective : Function.Injective (DGIdeal.toIdeal : DGIdeal A → Ideal A) :=
  fun _ _ h => SetLike.coe_injective (congrArg (fun J : Ideal A => (J : Set A)) h)

@[ext]
theorem ext {I J : DGIdeal A} (h : ∀ a, a ∈ I ↔ a ∈ J) : I = J :=
  SetLike.ext h

variable (I : DGIdeal A)

instance isTwoSided : I.toIdeal.IsTwoSided :=
  ⟨fun b ha => I.mul_mem_right' b ha⟩

theorem isHomogeneous : I.toIdeal.IsHomogeneous (grading (M := A)) :=
  I.isHomogeneous'

/-- A dg ideal as a homogeneous ideal. -/
def toHomogeneousIdeal : HomogeneousIdeal (grading (M := A)) :=
  ⟨I.toIdeal, I.isHomogeneous⟩

variable {I}

theorem zero_mem : (0 : A) ∈ I := I.toIdeal.zero_mem

theorem add_mem {a b : A} (ha : a ∈ I) (hb : b ∈ I) : a + b ∈ I := I.toIdeal.add_mem ha hb

theorem neg_mem {a : A} (ha : a ∈ I) : -a ∈ I := I.toIdeal.neg_mem ha

theorem mul_mem_left (a : A) {b : A} (hb : b ∈ I) : a * b ∈ I := I.toIdeal.mul_mem_left a hb

theorem mul_mem_right {a : A} (b : A) (ha : a ∈ I) : a * b ∈ I := I.mul_mem_right' b ha

theorem d_mem {a : A} (ha : a ∈ I) : d a ∈ I := I.d_mem' ha

theorem decompose_mem {a : A} (ha : a ∈ I) (n : ℤ) : (decompose (grading (M := A)) a n : A) ∈ I :=
  I.isHomogeneous n ha

instance : AddSubgroupClass (DGIdeal A) A where
  zero_mem _ := zero_mem
  add_mem := add_mem
  neg_mem := neg_mem

variable (I)

/-- The quotient of a dg ring by a dg ideal: the quotient ring `A ⧸ I.toIdeal`. -/
instance : HasQuotient A (DGIdeal A) := ⟨fun I => A ⧸ I.toIdeal⟩

namespace Quotient

instance instRing : Ring (A ⧸ I) := inferInstanceAs (Ring (A ⧸ I.toIdeal))

/-- The quotient map `A → A ⧸ I` as a ring homomorphism; see `DGIdeal.Quotient.mk` for the
morphism of dg rings. -/
abbrev mkRingHom : A →+* A ⧸ I := Ideal.Quotient.mk I.toIdeal

theorem mkRingHom_surjective : Function.Surjective (mkRingHom I) :=
  Ideal.Quotient.mk_surjective

theorem mkRingHom_eq_zero_iff_mem {a : A} : mkRingHom I a = 0 ↔ a ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

theorem isHomogeneous_ker :
    SetLike.IsHomogeneous (grading (M := A)) (mkRingHom I).toAddMonoidHom.ker := by
  intro n a ha
  have ha' : mkRingHom I a = 0 := ha
  show mkRingHom I _ = 0
  rw [mkRingHom_eq_zero_iff_mem] at ha' ⊢
  exact decompose_mem ha' n

/-- The differential of `A ⧸ I`, induced by `d`. -/
def dQuot : A ⧸ I →+ A ⧸ I :=
  QuotientAddGroup.lift I.toIdeal.toAddSubgroup ((mkRingHom I).toAddMonoidHom.comp d)
    fun a ha => by
      show mkRingHom I (d a) = 0
      rw [mkRingHom_eq_zero_iff_mem]
      exact d_mem ha

@[simp]
theorem dQuot_mk (a : A) : dQuot I (mkRingHom I a) = mkRingHom I (d a) := rfl

/-- The dg abelian group structure of `A ⧸ I`: graded by the images of the `Aⁿ`, with the
differential induced by `d`. -/
noncomputable instance dgAddCommGroup : DGAddCommGroup (A ⧸ I) where
  grading n := (grading (M := A) n).map (mkRingHom I).toAddMonoidHom
  decomposition := DG.Decomposition.map _ _ (mkRingHom_surjective I) (isHomogeneous_ker I)
  d := dQuot I
  d_mem' := by
    rintro n _ ⟨a, ha, rfl⟩
    exact ⟨d a, DG.d_mem ha, rfl⟩
  d_d' x := by
    obtain ⟨a, rfl⟩ := mkRingHom_surjective I x
    change dQuot I (dQuot I (mkRingHom I a)) = 0
    rw [dQuot_mk, dQuot_mk, d_d, map_zero]

theorem mem_grading_iff {n : ℤ} {x : A ⧸ I} :
    x ∈ grading n ↔ ∃ a ∈ grading (M := A) n, mkRingHom I a = x :=
  Iff.rfl

theorem mkRingHom_mem_grading {n : ℤ} {a : A} (ha : a ∈ grading n) :
    mkRingHom I a ∈ grading n :=
  ⟨a, ha, rfl⟩

@[simp]
theorem d_mkRingHom (a : A) : d (mkRingHom I a) = mkRingHom I (d a) := rfl

/-- The quotient of a dg ring by a dg ideal is a dg ring. -/
instance dgRing : DGRing (A ⧸ I) where
  one_mem := ⟨1, one_mem_grading, map_one (mkRingHom I)⟩
  mul_mem _ _ _ _ := by
    rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem_grading ha hb, map_mul (mkRingHom I) a b⟩
  d_mul' := by
    rintro n _ ⟨a, ha, rfl⟩ y
    obtain ⟨b, rfl⟩ := mkRingHom_surjective I y
    change d (mkRingHom I a * mkRingHom I b) =
      d (mkRingHom I a) * mkRingHom I b + koszulSign n • (mkRingHom I a * d (mkRingHom I b))
    rw [← map_mul, d_mkRingHom, d_mkRingHom, d_mkRingHom, d_mul ha, map_add, map_mul,
      Units.smul_def, map_zsmul, map_mul, Units.smul_def]

/-- The quotient map `A → A ⧸ I` as a morphism of dg rings. -/
def mk : A →ᵈᵍ+* A ⧸ I where
  __ := mkRingHom I
  map_mem' ha := mkRingHom_mem_grading I ha
  map_d' _ := rfl

@[simp]
theorem mk_apply (a : A) : mk I a = mkRingHom I a := rfl

theorem mk_surjective : Function.Surjective (mk I) := mkRingHom_surjective I

theorem mk_eq_zero_iff_mem {a : A} : mk I a = 0 ↔ a ∈ I := mkRingHom_eq_zero_iff_mem I

theorem mk_eq_mk_iff_sub_mem (a b : A) : mk I a = mk I b ↔ a - b ∈ I :=
  Ideal.Quotient.mk_eq_mk_iff_sub_mem a b

variable {I} {B : Type*} [Ring B] [DGAddCommGroup B]

/-- The universal property of the quotient: a morphism of dg rings vanishing on `I` factors
through `A ⧸ I`. -/
def lift (f : A →ᵈᵍ+* B) (hf : ∀ a ∈ I, f a = 0) : (A ⧸ I) →ᵈᵍ+* B where
  __ := Ideal.Quotient.lift I.toIdeal f.toRingHom hf
  map_mem' := by
    rintro n _ ⟨a, ha, rfl⟩
    exact f.map_mem ha
  map_d' x := by
    obtain ⟨a, rfl⟩ := mkRingHom_surjective I x
    change Ideal.Quotient.lift I.toIdeal f.toRingHom hf (Ideal.Quotient.mk I.toIdeal (d a)) =
      d (Ideal.Quotient.lift I.toIdeal f.toRingHom hf (Ideal.Quotient.mk I.toIdeal a))
    rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
    exact f.map_d a

@[simp]
theorem lift_mk (f : A →ᵈᵍ+* B) (hf : ∀ a ∈ I, f a = 0) (a : A) : lift f hf (mk I a) = f a :=
  Ideal.Quotient.lift_mk I.toIdeal f.toRingHom hf

end Quotient

end DGIdeal

/-- The kernel of a morphism of dg rings is a dg ideal. -/
def DGRingHom.ker {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B]
    [DGAddCommGroup B] (f : A →ᵈᵍ+* B) : DGIdeal A where
  __ := RingHom.ker f.toRingHom
  mul_mem_right' {a} b ha := by
    have ha' : f a = 0 := ha
    show f (a * b) = 0
    rw [map_mul, ha', zero_mul]
  isHomogeneous' n a ha := by
    rw [RingHom.mem_ker, DGRingHom.toRingHom_apply] at ha ⊢
    rw [← f.decompose_apply, ha, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  d_mem' {a} ha := by
    have ha' : f a = 0 := ha
    show f (d a) = 0
    rw [f.map_d, ha', d_zero]

@[simp]
theorem DGRingHom.mem_ker {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B]
    [DGAddCommGroup B] {f : A →ᵈᵍ+* B} {a : A} : a ∈ f.ker ↔ f a = 0 :=
  RingHom.mem_ker

/-! ### dg subrings -/

/-- A dg subring of a dg ring `A`: a subring which is homogeneous and stable under `d`. -/
structure DGSubring (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A] extends Subring A where
  isHomogeneous' : SetLike.IsHomogeneous (grading (M := A)) toSubring
  d_mem' : ∀ {a : A}, a ∈ carrier → d a ∈ carrier

namespace DGSubring

variable {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]

instance : SetLike (DGSubring A) A where
  coe S := S.toSubring
  coe_injective S T h := by
    cases S
    cases T
    congr
    exact SetLike.coe_injective h

instance : PartialOrder (DGSubring A) := .ofSetLike (DGSubring A) A

instance : SubringClass (DGSubring A) A where
  zero_mem S := S.toSubring.zero_mem
  one_mem S := S.toSubring.one_mem
  add_mem {S} := S.toSubring.add_mem
  mul_mem {S} := S.toSubring.mul_mem
  neg_mem {S} := S.toSubring.neg_mem

@[simp]
theorem mem_toSubring {S : DGSubring A} {a : A} : a ∈ S.toSubring ↔ a ∈ S := Iff.rfl

@[simp]
theorem coe_toSubring (S : DGSubring A) : (S.toSubring : Set A) = S := rfl

theorem toSubring_injective : Function.Injective (DGSubring.toSubring : DGSubring A → Subring A) :=
  fun _ _ h => SetLike.coe_injective (congrArg (fun T : Subring A => (T : Set A)) h)

@[ext]
theorem ext {S T : DGSubring A} (h : ∀ a, a ∈ S ↔ a ∈ T) : S = T :=
  SetLike.ext h

variable (S : DGSubring A)

theorem isHomogeneous : SetLike.IsHomogeneous (grading (M := A)) S := S.isHomogeneous'

variable {S}

theorem d_mem {a : A} (ha : a ∈ S) : d a ∈ S := S.d_mem' ha

theorem decompose_mem {a : A} (ha : a ∈ S) (n : ℤ) : (decompose (grading (M := A)) a n : A) ∈ S :=
  S.isHomogeneous n ha

variable (S)

/-- The dg abelian group structure of a dg subring: graded by `Sⁿ = S ∩ Aⁿ`, with the
restricted differential. -/
noncomputable instance dgAddCommGroup : DGAddCommGroup S :=
  DGAddCommGroup.ofInjective (AddSubgroupClass.subtype S) Subtype.val_injective
    (((d : A →+ A).comp (AddSubgroupClass.subtype S)).codRestrict S fun a => d_mem a.2)
    (fun _ => rfl) fun n a => ⟨⟨_, decompose_mem a.2 n⟩, rfl⟩

theorem mem_grading_iff {n : ℤ} {a : S} : a ∈ grading n ↔ (a : A) ∈ grading n := Iff.rfl

@[simp]
theorem coe_d (a : S) : ((d a : S) : A) = d (a : A) := rfl

/-- A dg subring is a dg ring. -/
instance dgRing : DGRing S where
  one_mem := by
    show ((1 : S) : A) ∈ grading (M := A) 0
    rw [OneMemClass.coe_one]
    exact one_mem_grading
  mul_mem _ _ a b ha hb := by
    show ((a * b : S) : A) ∈ grading (M := A) _
    rw [MulMemClass.coe_mul]
    exact mul_mem_grading ha hb
  d_mul' {n} a ha b := Subtype.ext <| by
    show d ((a * b : S) : A) = ((d a * b : S) : A) + ((koszulSign n • (a * d b) : S) : A)
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, Units.smul_def, AddSubgroupClass.coe_zsmul,
      MulMemClass.coe_mul, ← Units.smul_def]
    exact d_mul (A := A) ((mem_grading_iff S).mp ha) (b : A)

/-- The inclusion of a dg subring as a morphism of dg rings. -/
def subtype : S →ᵈᵍ+* A where
  __ := SubringClass.subtype S
  map_mem' ha := ha
  map_d' _ := rfl

@[simp]
theorem coe_subtype : ⇑(subtype S) = Subtype.val := rfl

@[simp]
theorem subtype_apply (a : S) : subtype S a = a := rfl

/-- The homogeneous components of an element of a dg subring are computed in `A`. -/
theorem coe_decompose (a : S) (n : ℤ) :
    ((decompose (grading (M := S)) a n : S) : A) = decompose (grading (M := A)) (a : A) n :=
  ((subtype S).decompose_apply a n).symm

end DGSubring

/-! ### Cocycles and coboundaries -/

section Cocycles

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]

/-- The cocycles `Z(A) = ker d` of a dg ring form a subring. -/
def cocyclesSubring : Subring A where
  carrier := (d : A →+ A).ker
  zero_mem' := AddMonoidHom.mem_ker.mpr d_zero
  add_mem' ha hb := AddMonoidHom.mem_ker.mpr (by
    rw [d_add, AddMonoidHom.mem_ker.mp ha, AddMonoidHom.mem_ker.mp hb, add_zero])
  neg_mem' ha := AddMonoidHom.mem_ker.mpr (by rw [d_neg, AddMonoidHom.mem_ker.mp ha, neg_zero])
  one_mem' := AddMonoidHom.mem_ker.mpr d_one
  mul_mem' ha hb := AddMonoidHom.mem_ker.mpr (by
    rw [d_mul_of_d_eq_zero_right (AddMonoidHom.mem_ker.mp hb), AddMonoidHom.mem_ker.mp ha,
      zero_mul])

@[simp]
theorem mem_cocyclesSubring {a : A} : a ∈ cocyclesSubring A ↔ d a = 0 := Iff.rfl

/-- The cocycles `Z(A) = ker d` of a dg ring form a dg subring (on which `d = 0`). -/
def cocyclesDGSubring : DGSubring A where
  __ := cocyclesSubring A
  isHomogeneous' := isHomogeneous_ker_d
  d_mem' _ := by simp

@[simp]
theorem mem_cocyclesDGSubring {a : A} : a ∈ cocyclesDGSubring A ↔ d a = 0 := Iff.rfl

theorem mem_grading_cocyclesDGSubring {n : ℤ} {a : cocyclesDGSubring A} :
    a ∈ grading n ↔ (a : A) ∈ cocycles A n :=
  ⟨fun ha => ⟨ha, a.2⟩, fun ha => ha.1⟩

@[simp]
theorem d_cocyclesDGSubring (a : cocyclesDGSubring A) : d a = 0 :=
  Subtype.ext a.2

/-- The coboundaries `B(A) = im d` form a dg ideal of the dg subring of cocycles `Z(A)`. -/
def coboundariesDGIdeal : DGIdeal (cocyclesDGSubring A) where
  carrier := {z | (z : A) ∈ (d : A →+ A).range}
  zero_mem' := ⟨0, d_zero⟩
  add_mem' := by
    rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by rw [d_add, hx, hy]; rfl⟩
  smul_mem' := by
    rintro z w ⟨x, hx⟩
    change (z : A) * (w : A) ∈ (d : A →+ A).range
    rw [← hx]
    refine induction_on_of_isHomogeneous (S := (d : A →+ A).ker) isHomogeneous_ker_d
      (P := fun a => a * d x ∈ (d : A →+ A).range) ?_ ?_ ?_ z.2
    · exact ⟨0, by simp⟩
    · intro n a ha hda
      refine ⟨koszulSign n • (a * x), ?_⟩
      rw [d_units_smul, d_mul ha, AddMonoidHom.mem_ker.mp hda, zero_mul, zero_add, smul_smul,
        ← koszulSign_add, koszulSign_even ⟨n, rfl⟩, one_smul]
    · rintro a b ⟨x', hx'⟩ ⟨y', hy'⟩
      exact ⟨x' + y', by rw [d_add, hx', hy', add_mul]⟩
  mul_mem_right' := by
    rintro w z ⟨x, hx⟩
    exact ⟨x * z, by rw [d_mul_of_d_eq_zero_right ((mem_cocyclesDGSubring A).mp z.2), hx]; rfl⟩
  isHomogeneous' n z hz := by
    show ((decompose (grading (M := cocyclesDGSubring A)) z n : cocyclesDGSubring A) : A) ∈
      (d : A →+ A).range
    rw [DGSubring.coe_decompose]
    exact isHomogeneous_range_d n hz
  d_mem' _ := ⟨0, by simp⟩

theorem mem_coboundariesDGIdeal {z : cocyclesDGSubring A} :
    z ∈ coboundariesDGIdeal A ↔ ∃ x : A, d x = z :=
  Iff.rfl

end Cocycles

end DG
