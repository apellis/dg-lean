import DG.Module.Basic

/-!
# Morphisms of dg rings and dg algebras; restriction of scalars

* `DGRingHom A B` (notation `A →ᵈᵍ+* B`): ring homomorphisms of degree `0` commuting with the
  differentials, the morphisms of dg rings.
* `DGAlgHom R A B` (notation `A →ᵈᵍₐ[R] B`): `R`-algebra homomorphisms of degree `0` commuting
  with the differentials, the morphisms of dg `R`-algebras.
* `RestrictScalars φ M`: restriction of scalars along `φ : A →ᵈᵍ+* B`. For a dg `B`-module `M`,
  the `A`-module `Module.compHom M φ.toRingHom` is a dg `A`-module (`DG.DGModule.compHom`);
  `RestrictScalars φ M` is a type synonym for `M` carrying this structure, and
  `DGModuleHom.restrictScalars φ` is the induced map on morphisms.

## Implementation notes

`RestrictScalars φ M` follows Mathlib's `RestrictScalars R S M`: a type synonym rather than a
local instance, so that `M` can carry its dg `B`-module structure and the restricted dg
`A`-module structure simultaneously without instance diamonds. Since the restriction is along
an explicit morphism `φ` rather than along an `Algebra` instance, the synonym is indexed by `φ`.
The underlying dg abelian group of `RestrictScalars φ M` is definitionally that of `M`.
-/

open DirectSum

namespace DG

/-- A morphism of dg rings: a ring homomorphism of degree `0` commuting with the
differentials. -/
structure DGRingHom (A B : Type*) [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
    extends A →+* B where
  map_mem' : ∀ {n : ℤ} {a : A}, a ∈ grading n → toFun a ∈ grading n
  map_d' : ∀ a : A, toFun (d a) = d (toFun a)

@[inherit_doc]
notation:25 A " →ᵈᵍ+* " B => DGRingHom A B

namespace DGRingHom

variable {A B C : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
  [Ring C] [DGAddCommGroup C]

instance : FunLike (A →ᵈᵍ+* B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : RingHomClass (A →ᵈᵍ+* B) A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[simp]
theorem coe_toRingHom (f : A →ᵈᵍ+* B) : ⇑f.toRingHom = f := rfl

@[simp]
theorem toRingHom_apply (f : A →ᵈᵍ+* B) (a : A) : f.toRingHom a = f a := rfl

@[ext]
theorem ext {f g : A →ᵈᵍ+* B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

theorem toRingHom_injective :
    Function.Injective (DGRingHom.toRingHom : (A →ᵈᵍ+* B) → A →+* B) :=
  fun _ _ h => ext fun a => congrArg (fun φ : A →+* B => φ a) h

theorem map_mem (f : A →ᵈᵍ+* B) {n : ℤ} {a : A} (ha : a ∈ grading n) : f a ∈ grading n :=
  f.map_mem' ha

@[simp]
theorem map_d (f : A →ᵈᵍ+* B) (a : A) : f (d a) = d (f a) :=
  f.map_d' a

/-- A morphism of dg rings commutes with taking homogeneous components. -/
theorem decompose_apply (f : A →ᵈᵍ+* B) (a : A) (n : ℤ) :
    (decompose (grading (M := B)) (f a) n : B) = f (decompose (grading (M := A)) a n : A) := by
  have h := decompose_map (k := 0) f.toRingHom.toAddMonoidHom
    (fun ha => by simpa using f.map_mem ha) a n
  rwa [add_zero] at h

/-- The identity morphism. -/
def id : A →ᵈᵍ+* A where
  __ := RingHom.id A
  map_mem' ha := ha
  map_d' _ := rfl

@[simp]
theorem id_apply (a : A) : (DGRingHom.id : A →ᵈᵍ+* A) a = a := rfl

/-- Composition of morphisms. -/
def comp (g : B →ᵈᵍ+* C) (f : A →ᵈᵍ+* B) : A →ᵈᵍ+* C where
  __ := g.toRingHom.comp f.toRingHom
  map_mem' ha := g.map_mem (f.map_mem ha)
  map_d' a := by simp

@[simp]
theorem comp_apply (g : B →ᵈᵍ+* C) (f : A →ᵈᵍ+* B) (a : A) : g.comp f a = g (f a) := rfl

@[simp]
theorem comp_id (f : A →ᵈᵍ+* B) : f.comp DGRingHom.id = f := rfl

@[simp]
theorem id_comp (f : A →ᵈᵍ+* B) : DGRingHom.id.comp f = f := rfl

theorem comp_assoc {D : Type*} [Ring D] [DGAddCommGroup D] (h : C →ᵈᵍ+* D) (g : B →ᵈᵍ+* C)
    (f : A →ᵈᵍ+* B) : (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- A morphism of dg rings maps cocycles to cocycles. -/
theorem map_cocycles (f : A →ᵈᵍ+* B) {n : ℤ} {a : A} (ha : a ∈ cocycles A n) :
    f a ∈ cocycles B n := by
  rw [mem_cocycles] at ha ⊢
  exact ⟨f.map_mem ha.1, by rw [← map_d, ha.2, map_zero]⟩

/-- A morphism of dg rings maps coboundaries to coboundaries. -/
theorem map_coboundaries (f : A →ᵈᵍ+* B) {n : ℤ} {a : A} (ha : a ∈ coboundaries A n) :
    f a ∈ coboundaries B n := by
  obtain ⟨a', ha', rfl⟩ := ha
  exact ⟨f a', f.map_mem ha', (map_d f a').symm⟩

end DGRingHom

/-- A morphism of dg `R`-algebras: an `R`-algebra homomorphism of degree `0` commuting with the
differentials. -/
structure DGAlgHom (R A B : Type*) [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
    [Ring B] [Algebra R B] [DGAddCommGroup B] extends A →ₐ[R] B where
  map_mem' : ∀ {n : ℤ} {a : A}, a ∈ grading n → toFun a ∈ grading n
  map_d' : ∀ a : A, toFun (d a) = d (toFun a)

@[inherit_doc]
notation:25 A " →ᵈᵍₐ[" R "] " B => DGAlgHom R A B

namespace DGAlgHom

variable {R A B C : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A]
  [Ring B] [Algebra R B] [DGAddCommGroup B] [Ring C] [Algebra R C] [DGAddCommGroup C]

instance : FunLike (A →ᵈᵍₐ[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : AlgHomClass (A →ᵈᵍₐ[R] B) R A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

@[simp]
theorem coe_toAlgHom (f : A →ᵈᵍₐ[R] B) : ⇑f.toAlgHom = f := rfl

@[simp]
theorem toAlgHom_apply (f : A →ᵈᵍₐ[R] B) (a : A) : f.toAlgHom a = f a := rfl

@[ext]
theorem ext {f g : A →ᵈᵍₐ[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

theorem toAlgHom_injective :
    Function.Injective (DGAlgHom.toAlgHom : (A →ᵈᵍₐ[R] B) → A →ₐ[R] B) :=
  fun _ _ h => ext fun a => congrArg (fun φ : A →ₐ[R] B => φ a) h

theorem map_mem (f : A →ᵈᵍₐ[R] B) {n : ℤ} {a : A} (ha : a ∈ grading n) : f a ∈ grading n :=
  f.map_mem' ha

@[simp]
theorem map_d (f : A →ᵈᵍₐ[R] B) (a : A) : f (d a) = d (f a) :=
  f.map_d' a

/-- The underlying morphism of dg rings. -/
def toDGRingHom (f : A →ᵈᵍₐ[R] B) : A →ᵈᵍ+* B where
  __ := f.toAlgHom.toRingHom
  map_mem' := f.map_mem'
  map_d' := f.map_d'

@[simp]
theorem coe_toDGRingHom (f : A →ᵈᵍₐ[R] B) : ⇑f.toDGRingHom = f := rfl

@[simp]
theorem toDGRingHom_apply (f : A →ᵈᵍₐ[R] B) (a : A) : f.toDGRingHom a = f a := rfl

theorem toDGRingHom_injective :
    Function.Injective (DGAlgHom.toDGRingHom : (A →ᵈᵍₐ[R] B) → A →ᵈᵍ+* B) :=
  fun _ _ h => ext fun a => congrArg (fun φ : A →ᵈᵍ+* B => φ a) h

/-- The identity morphism. -/
def id : A →ᵈᵍₐ[R] A where
  __ := AlgHom.id R A
  map_mem' ha := ha
  map_d' _ := rfl

@[simp]
theorem id_apply (a : A) : (DGAlgHom.id : A →ᵈᵍₐ[R] A) a = a := rfl

/-- Composition of morphisms. -/
def comp (g : B →ᵈᵍₐ[R] C) (f : A →ᵈᵍₐ[R] B) : A →ᵈᵍₐ[R] C where
  __ := g.toAlgHom.comp f.toAlgHom
  map_mem' ha := g.map_mem (f.map_mem ha)
  map_d' a := by simp

@[simp]
theorem comp_apply (g : B →ᵈᵍₐ[R] C) (f : A →ᵈᵍₐ[R] B) (a : A) : g.comp f a = g (f a) := rfl

@[simp]
theorem comp_id (f : A →ᵈᵍₐ[R] B) : f.comp DGAlgHom.id = f := rfl

@[simp]
theorem id_comp (f : A →ᵈᵍₐ[R] B) : DGAlgHom.id.comp f = f := rfl

theorem comp_assoc {D : Type*} [Ring D] [Algebra R D] [DGAddCommGroup D] (h : C →ᵈᵍₐ[R] D)
    (g : B →ᵈᵍₐ[R] C) (f : A →ᵈᵍₐ[R] B) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp]
theorem toDGRingHom_id : (DGAlgHom.id : A →ᵈᵍₐ[R] A).toDGRingHom = DGRingHom.id := rfl

@[simp]
theorem toDGRingHom_comp (g : B →ᵈᵍₐ[R] C) (f : A →ᵈᵍₐ[R] B) :
    (g.comp f).toDGRingHom = g.toDGRingHom.comp f.toDGRingHom := rfl

end DGAlgHom

/-! ### Restriction of scalars -/

section RestrictScalars

variable {A B : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]

/-- Restriction of scalars along a morphism of dg rings: for a dg `B`-module `M`, the `A`-module
`Module.compHom M φ.toRingHom` (with `a • m = φ a • m`) is a dg `A`-module. -/
theorem DGModule.compHom (φ : A →ᵈᵍ+* B) (M : Type*) [AddCommGroup M] [DGAddCommGroup M]
    [Module B M] [DGModule B M] :
    letI := Module.compHom M φ.toRingHom
    DGModule A M :=
  letI := Module.compHom M φ.toRingHom
  { smul_mem := fun _ _ _ _ ha hm => smul_mem_grading (A := B) (φ.map_mem ha) hm
    d_smul' := fun ha m => by
      change d (φ _ • m) = φ (d _) • m + _ • (φ _ • d m)
      rw [DGRingHom.map_d, d_smul (φ.map_mem ha)] }

/-- A type synonym for `M` carrying the dg `A`-module structure obtained by restricting scalars
along `φ : A →ᵈᵍ+* B`. The underlying dg abelian group is that of `M`. -/
@[nolint unusedArguments]
def RestrictScalars (_φ : A →ᵈᵍ+* B) (M : Type*) : Type _ := M

namespace RestrictScalars

section AddCommGroup

variable (φ : A →ᵈᵍ+* B) (M : Type*) [AddCommGroup M]

instance : AddCommGroup (RestrictScalars φ M) := inferInstanceAs (AddCommGroup M)

variable {M}

/-- The identity map `RestrictScalars φ M → M`, as an additive equivalence. -/
def addEquiv : RestrictScalars φ M ≃+ M := AddEquiv.refl M

@[simp]
theorem addEquiv_apply (m : RestrictScalars φ M) : addEquiv φ m = m := rfl

@[simp]
theorem addEquiv_symm_apply (m : M) : (addEquiv φ).symm m = m := rfl

end AddCommGroup

section Module

variable (φ : A →ᵈᵍ+* B) (M : Type*) [AddCommGroup M] [Module B M]

instance module : Module A (RestrictScalars φ M) := Module.compHom M φ.toRingHom

variable {M}

theorem smul_def (a : A) (m : RestrictScalars φ M) :
    a • m = (addEquiv φ).symm (φ a • addEquiv φ m) := rfl

end Module

variable (φ : A →ᵈᵍ+* B) (M : Type*) [AddCommGroup M] [DGAddCommGroup M] [Module B M]

instance dgAddCommGroup : DGAddCommGroup (RestrictScalars φ M) :=
  inferInstanceAs (DGAddCommGroup M)

instance dgModule [DGModule B M] : DGModule A (RestrictScalars φ M) :=
  DGModule.compHom φ M

end RestrictScalars

variable (φ : A →ᵈᵍ+* B) {M N P : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module B M]
  [AddCommGroup N] [DGAddCommGroup N] [Module B N] [AddCommGroup P] [DGAddCommGroup P]
  [Module B P]

/-- Restriction of scalars along `φ` on morphisms: a morphism of dg `B`-modules is a morphism of
the restricted dg `A`-modules. -/
def DGModuleHom.restrictScalars (f : M →ᵈᵍ[B] N) :
    RestrictScalars φ M →ᵈᵍ[A] RestrictScalars φ N where
  toFun := f
  map_add' := map_add f
  map_smul' a m := f.map_smul (φ a) m
  map_mem' := f.map_mem
  map_d' := f.map_d

@[simp]
theorem DGModuleHom.restrictScalars_apply (f : M →ᵈᵍ[B] N) (m : RestrictScalars φ M) :
    f.restrictScalars φ m = f m := rfl

@[simp]
theorem DGModuleHom.restrictScalars_id :
    (DGModuleHom.id : M →ᵈᵍ[B] M).restrictScalars φ = DGModuleHom.id := rfl

@[simp]
theorem DGModuleHom.restrictScalars_comp (g : N →ᵈᵍ[B] P) (f : M →ᵈᵍ[B] N) :
    (g.comp f).restrictScalars φ = (g.restrictScalars φ).comp (f.restrictScalars φ) := rfl

theorem DGModuleHom.restrictScalars_injective :
    Function.Injective (DGModuleHom.restrictScalars φ : (M →ᵈᵍ[B] N) → _) :=
  fun _ _ h => DGModuleHom.ext fun m => congrArg (fun g => g m) h

end RestrictScalars

end DG
