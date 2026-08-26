/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XiLab.Csordas

/-!
# Solution

The proof development lives in the `XiLab` library. This file restates the
Challenge definitions verbatim and bridges to the library's theorem.

The two `example`s below are the bridge: `CsordasCounterexample.Phi` and
`CsordasCounterexample.J` are *definitionally* equal to `XiLab.Phi` and
`XiLab.J`, so the theorem is discharged by the library result applied directly.
-/

namespace CsordasCounterexample

open Real

noncomputable def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
    Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))

noncomputable def Phi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm (n + 1) u

noncomputable def J (n : ℕ) (t : ℝ) : ℝ :=
  (iteratedDeriv n Phi t) ^ 2 - iteratedDeriv (n - 1) Phi t * iteratedDeriv (n + 1) Phi t

example : Phi = XiLab.Phi := rfl
example : J = XiLab.J := rfl

theorem J_nine_neg : J 9 0 < 0 := XiLab.J_nine_neg

end CsordasCounterexample
