/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Challenge: a log-concavity conjecture for the Riemann kernel fails

This file is the human-auditable statement. It imports only Mathlib.

**This file makes no claim about the Riemann hypothesis, in either direction.**

Riemann's kernel is
`Φ(u) = ∑_{n≥1} (4π²n⁴ e^{9u/2} − 6πn² e^{5u/2}) e^{−πn²e^{2u}}`,
the positive even function for which `ξ(½+w) = 2∫₀^∞ Φ(u) cosh(wu) du`
(Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1). Coffey and
Csordás (*On the log-concavity of a Jacobi theta function*, Math. Comp. 82
(2013), 2265–2272, Conjecture 2.5, where the quantity below is written `Sₙ`;
restated as Open Problem 4.13 of Csordás, Comput. Methods Funct. Theory 15
(2015), 373–391) conjectured that the Laguerre expressions

`Jₙ(t) = (Φ⁽ⁿ⁾(t))² − Φ⁽ⁿ⁻¹⁾(t)·Φ⁽ⁿ⁺¹⁾(t)`

are strictly positive for every `n ≥ 1` and every real `t`.

The advertised statement is that this fails: `J₉(0) < 0`. Since `Φ` is even,
`Φ⁽⁹⁾(0) = 0` and `J₉(0) = −Φ⁽⁸⁾(0)·Φ⁽¹⁰⁾(0)`, so the failure is exactly the
statement that `Φ⁽⁸⁾(0)` and `Φ⁽¹⁰⁾(0)` share a sign: the expected alternation
of the even-order derivatives at the origin breaks at order ten.

Convention note: some sources use the normalisation `Φ_C(r) = ½Φ(2r)`
(equivalently `e^{4r}` in place of `e^{2u}`). `Jₙ` is homogeneous of degree 2
in `Φ`, and the rescaling multiplies `Φ⁽²ʲ⁾(0)` by the positive factor
`2^{2j−1}`, so every sign statement here transfers to that normalisation
unchanged.
-/

namespace CsordasCounterexample

open Real

/-- The `n`-th summand of Riemann's kernel series,
`(4π²n⁴ e^{9u/2} − 6πn² e^{5u/2}) e^{−πn²e^{2u}}`. -/
noncomputable def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
    Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))

/-- **Riemann's kernel** `Φ(u) = ∑_{n≥1} (4π²n⁴ e^{9u/2} − 6πn² e^{5u/2}) e^{−πn²e^{2u}}`.

The sum is over `n ≥ 1`, written as a sum over `n : ℕ` of `phiTerm (n+1)`.
It is the positive, even, superexponentially decaying kernel of Riemann's
integral representation of `ξ`. -/
noncomputable def Phi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm (n + 1) u

/-- The `n`-th **Laguerre expression** of the kernel,
`Jₙ(t) = (Φ⁽ⁿ⁾(t))² − Φ⁽ⁿ⁻¹⁾(t)·Φ⁽ⁿ⁺¹⁾(t)`, with derivatives taken in the
sense of `iteratedDeriv`. -/
noncomputable def J (n : ℕ) (t : ℝ) : ℝ :=
  (iteratedDeriv n Phi t) ^ 2 - iteratedDeriv (n - 1) Phi t * iteratedDeriv (n + 1) Phi t

/-- **The Coffey–Csordás log-concavity conjecture is false.** Its instance at
`n = 9`, `t = 0` fails: `J₉(0) < 0`. -/
theorem J_nine_neg : J 9 0 < 0 := by
  sorry

end CsordasCounterexample
