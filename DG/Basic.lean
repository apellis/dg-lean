import Mathlib.Algebra.Ring.NegOnePow

/-!
# Conventions for the `DG` library

This file fixes the sign conventions used throughout the library; see `docs/CONVENTIONS.md`
for the full list.

* Gradings are cohomological and indexed by `ℤ`: differentials raise the degree by `1`.
* The Koszul sign attached to a homogeneous element of degree `n` is `(-1)^n`, written
  `Int.negOnePow n : ℤˣ` (Mathlib's `Int.negOnePow`); the parity of an element is its degree
  modulo `2`.
* The sign rule: whenever two homogeneous symbols of degrees `m` and `n` are exchanged, the
  expression is multiplied by `(-1)^(m * n)`.
-/

namespace DG

/-- The Koszul sign `(-1)^n` of a degree `n : ℤ`, as a unit of `ℤ`. -/
abbrev koszulSign (n : ℤ) : ℤˣ := Int.negOnePow n

theorem koszulSign_add (m n : ℤ) : koszulSign (m + n) = koszulSign m * koszulSign n :=
  Int.negOnePow_add m n

theorem koszulSign_even {n : ℤ} (h : Even n) : koszulSign n = 1 :=
  Int.negOnePow_even n h

theorem koszulSign_odd {n : ℤ} (h : Odd n) : koszulSign n = -1 :=
  Int.negOnePow_odd n h

end DG
