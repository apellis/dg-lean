import DG.Compact.Triangulated

/-!
# Thick subcategories and thick closures

Let `C` be a pretriangulated category. A property of objects `P : ObjectProperty C` is *thick*
(`DG.IsThick P`) if it contains the zero object, is stable under the shifts `⟦n⟧` for all
`n : ℤ`, satisfies the two-out-of-three property for distinguished triangles, and is closed under
retracts (direct summands). A thick property is closed under isomorphisms (an isomorphism is a
retract), so it defines a strictly full triangulated subcategory `DG.IsThick.subcategory`
(a `CategoryTheory.Triangulated.Subcategory C`) which is closed under direct summands: a *thick
(épaisse) subcategory* in the sense of Verdier and Rickard.

For an arbitrary property `S`, the *thick closure* of `S` is the smallest thick property
containing `S`. It is defined inductively (`DG.ThickClosure S`), so that statements about all
of its objects can be proved by induction on the constructors: objects of `S`, the zero object,
shifts, the middle term of a distinguished triangle whose outer terms are in the closure, and
retracts. Its packaging as a triangulated subcategory is `DG.thickClosure S`.

## Main results

* `DG.IsThick.of_iso`, `DG.IsThick.ext₁`, `DG.IsThick.ext₃`, `DG.IsThick.biprod`: a thick
  property is closed under isomorphisms, satisfies all three forms of the two-out-of-three
  property, and is closed under finite direct sums.
* `DG.isThick_thickClosure`, `DG.le_thickClosure`, `DG.thickClosure_le`: `DG.ThickClosure S` is
  the smallest thick property containing `S`.
* `DG.isThick_isCompact`: in a pretriangulated category with coproducts, the compact objects form
  a thick property; hence `DG.thickClosure_le_isCompact`: the thick closure of a set of compact
  objects consists of compact objects.
-/

universe w v u

namespace DG

open CategoryTheory Limits Pretriangulated ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A property of objects of a pretriangulated category is *thick* if it contains the zero
object, is stable under all shifts, contains the middle term of every distinguished triangle
whose outer terms it contains, and is closed under retracts. -/
structure IsThick (P : ObjectProperty C) : Prop where
  /-- A thick property contains the zero object. -/
  zero : P 0
  /-- A thick property is stable under shifts. -/
  shift (X : C) (n : ℤ) : P X → P (X⟦n⟧)
  /-- Two-out-of-three: extensions. -/
  ext₂ (T : Triangle C) : (T ∈ distTriang C) → P T.obj₁ → P T.obj₃ → P T.obj₂
  /-- A thick property is closed under retracts (direct summands). -/
  retract {X Y : C} : Retract X Y → P Y → P X

namespace IsThick

variable {P : ObjectProperty C} (hP : IsThick P)
include hP

/-- A thick property is closed under isomorphisms. -/
theorem of_iso {X Y : C} (e : X ≅ Y) (hY : P Y) : P X :=
  hP.retract ⟨e.hom, e.inv, e.hom_inv_id⟩ hY

theorem isClosedUnderIsomorphisms : P.IsClosedUnderIsomorphisms :=
  ⟨fun e hX => hP.of_iso e.symm hX⟩

/-- A thick property contains every zero object. -/
theorem of_isZero {X : C} (hX : IsZero X) : P X :=
  hP.of_iso hX.isoZero hP.zero

theorem shift_iff (X : C) (n : ℤ) : P (X⟦n⟧) ↔ P X :=
  ⟨fun h => hP.of_iso ((shiftEquiv C n).unitIso.app X) (hP.shift _ (-n) h), hP.shift X n⟩

/-- Two-out-of-three: cones. -/
theorem ext₃ (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : P T.obj₁) (h₂ : P T.obj₂) :
    P T.obj₃ :=
  hP.ext₂ T.rotate (rot_of_distTriang T hT) h₂ (hP.shift _ 1 h₁)

/-- Two-out-of-three: cocones. -/
theorem ext₁ (T : Triangle C) (hT : T ∈ distTriang C) (h₂ : P T.obj₂) (h₃ : P T.obj₃) :
    P T.obj₁ :=
  hP.ext₂ T.invRotate (inv_rot_of_distTriang T hT) (hP.shift _ (-1) h₃) h₂

/-- A thick property is closed under binary biproducts. -/
theorem biprod {X Y : C} (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  hP.ext₂ _ (binaryBiproductTriangle_distinguished X Y) hX hY

theorem biprod_iff (X Y : C) : P (X ⊞ Y) ↔ P X ∧ P Y :=
  ⟨fun h => ⟨hP.retract ⟨biprod.inl, biprod.fst, biprod.inl_fst⟩ h,
    hP.retract ⟨biprod.inr, biprod.snd, biprod.inr_snd⟩ h⟩, fun h => hP.biprod h.1 h.2⟩

/-- The strictly full triangulated subcategory defined by a thick property. -/
def subcategory : Triangulated.Subcategory C :=
  Triangulated.Subcategory.mk' P hP.zero hP.shift hP.ext₂

@[simp]
theorem subcategory_P : hP.subcategory.P = P := rfl

instance : hP.subcategory.P.IsClosedUnderIsomorphisms := hP.isClosedUnderIsomorphisms

end IsThick

/-- The *thick closure* of a property `S` of objects: the smallest thick property containing
`S`, defined inductively. See `DG.isThick_thickClosure` and `DG.thickClosure_le`. -/
inductive ThickClosure (S : ObjectProperty C) : C → Prop
  /-- Objects of `S` are in the thick closure. -/
  | of_mem {X : C} : S X → ThickClosure S X
  /-- The zero object is in the thick closure. -/
  | zero : ThickClosure S 0
  /-- The thick closure is stable under shifts. -/
  | shift {X : C} (n : ℤ) : ThickClosure S X → ThickClosure S (X⟦n⟧)
  /-- The thick closure is closed under extensions. -/
  | ext₂ (T : Triangle C) : (T ∈ distTriang C) → ThickClosure S T.obj₁ → ThickClosure S T.obj₃ →
      ThickClosure S T.obj₂
  /-- The thick closure is closed under retracts. -/
  | retract {X Y : C} : Retract X Y → ThickClosure S Y → ThickClosure S X

variable (S : ObjectProperty C)

/-- The thick closure of `S` is thick. -/
theorem isThick_thickClosure : IsThick (ThickClosure S) where
  zero := .zero
  shift _ n h := .shift n h
  ext₂ T hT h₁ h₃ := .ext₂ T hT h₁ h₃
  retract h hY := .retract h hY

/-- `S` is contained in its thick closure. -/
theorem le_thickClosure : S ≤ ThickClosure S := fun _ h => .of_mem h

variable {S}

/-- Minimality of the thick closure: it is contained in every thick property containing `S`. -/
theorem thickClosure_le {P : ObjectProperty C} (hP : IsThick P) (h : S ≤ P) :
    ThickClosure S ≤ P := by
  intro X hX
  induction hX with
  | of_mem hX => exact h _ hX
  | zero => exact hP.zero
  | shift n _ ih => exact hP.shift _ n ih
  | ext₂ T hT _ _ ih₁ ih₃ => exact hP.ext₂ T hT ih₁ ih₃
  | retract e _ ih => exact hP.retract e ih

theorem thickClosure_mono {S S' : ObjectProperty C} (h : S ≤ S') :
    ThickClosure S ≤ ThickClosure S' :=
  thickClosure_le (isThick_thickClosure S') (h.trans (le_thickClosure S'))

theorem thickClosure_le_iff {P : ObjectProperty C} (hP : IsThick P) :
    ThickClosure S ≤ P ↔ S ≤ P :=
  ⟨fun h => (le_thickClosure S).trans h, thickClosure_le hP⟩

variable (S)

/-- The thick closure of `S`, as a (strictly full, thick) triangulated subcategory of `C`: the
thick subcategory generated by `S`. -/
def thickClosure : Triangulated.Subcategory C :=
  (isThick_thickClosure S).subcategory

@[simp]
theorem thickClosure_P : (thickClosure S).P = ThickClosure S := rfl

instance : (thickClosure S).P.IsClosedUnderIsomorphisms :=
  (isThick_thickClosure S).isClosedUnderIsomorphisms

section compact

variable (C) in
/-- In a pretriangulated category with coproducts, the compact objects form a thick property
(`DG.compactSubcategory` together with `DG.IsCompact.of_retract`). -/
theorem isThick_isCompact [HasCoproducts.{w} C] : IsThick (IsCompact.{w} (C := C)) where
  zero := IsCompact.of_isZero (isZero_zero C)
  shift _ n h := h.shift n
  ext₂ T hT h₁ h₃ := IsCompact.ext₂ T hT h₁ h₃
  retract h hY := hY.of_retract h

variable {S}

/-- The thick closure of a property consisting of compact objects consists of compact objects. -/
theorem thickClosure_le_isCompact [HasCoproducts.{w} C] (h : S ≤ IsCompact.{w}) :
    ThickClosure S ≤ IsCompact.{w} :=
  thickClosure_le (isThick_isCompact C) h

end compact

end DG
