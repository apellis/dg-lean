import Mathlib.CategoryTheory.Shift.Quotient
import DG.Category.Homotopy.HomShift
import DG.Category.Homotopy.HomotopyCategory

/-!
# The shift on the homotopy category of dg modules over a dg category

Let `C` be a dg category. This file shows that the shift of dg modules over `C`
(`DG.CatModule.hasShift`) preserves homotopies, and equips the homotopy category
`DG.CatModule.HomotopyCategory C` with the induced shift. It is a port of the second part of
`DG.Homotopy.Shift` (the case of a dg ring).

## Main definitions and results

* `DG.CatModule.DGHomotopy.shift`: a homotopy `h` from `f` to `g` gives the homotopy
  `(-1)ⁿ • h⟦n⟧` from `f⟦n⟧` to `g⟦n⟧` (Mathlib's `Homotopy.shift`, with the same sign).
* `DG.CatModule.HomotopyCategory.hasShift`: the induced shift on the homotopy category
  (`CategoryTheory.HasShift.quotient`), for which the quotient functor commutes with the shift
  (`DG.CatModule.HomotopyCategory.commShiftQuotient`); the shift functors are additive.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

/-! ### Shifts of homotopies -/

namespace DGHomotopy

variable {M N : CatModule.{w} C} {f g : M ⟶ N}

/-- A homotopy `h` from `f` to `g` induces the homotopy `(-1)ⁿ • h⟦n⟧` from `f⟦n⟧` to `g⟦n⟧`
(Mathlib's `Homotopy.shift`, with the same sign). -/
@[simps]
def shift (h : DGHomotopy f g) (n : ℤ) : DGHomotopy (shiftMap n f) (shiftMap n g) where
  hom := koszulSign n • h.hom.shift n
  ofHom_eq := by
    rw [δ_units_smul, Cochain.δ_shift, smul_smul, Int.units_mul_self, one_smul,
      ← Cochain.shift_ofHom, ← Cochain.shift_ofHom, h.ofHom_eq, Cochain.shift_add]

end DGHomotopy

theorem Homotopic.shift {M N : CatModule.{w} C} {f g : M ⟶ N} (h : Homotopic f g) (n : ℤ) :
    Homotopic (shiftMap n f) (shiftMap n g) :=
  ⟨h.some.shift n⟩

/-! ### The shift on the homotopy category -/

namespace HomotopyCategory

variable (C)

instance : (homotopic.{w} C).IsCompatibleWithShift ℤ :=
  ⟨fun n _ _ _ _ h => Homotopic.shift h n⟩

/-- The shift on the homotopy category, induced by the shift on dg modules. -/
noncomputable instance hasShift : HasShift (HomotopyCategory.{w} C) ℤ := by
  dsimp only [HomotopyCategory]
  infer_instance

/-- The quotient functor from dg modules to the homotopy category commutes with the shift. -/
noncomputable instance commShiftQuotient : (quotient C).CommShift ℤ :=
  Quotient.functor_commShift (homotopic.{w} C) ℤ

instance (n : ℤ) : (shiftFunctor (HomotopyCategory.{w} C) n).Additive := by
  have : (quotient C ⋙ shiftFunctor _ n).Additive :=
    Functor.additive_of_iso ((quotient C).commShiftIso n)
  exact Functor.additive_of_full_essSurj_comp (quotient C) _

end HomotopyCategory

end CatModule

end DG
