import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RBM8D.Basic.Lattice

/-!
# The bound `B_{xy}` and the spectral domain

[I, (1.18)] and the domain `𝐃(κ, ε)` of [I, (1.25)–(1.27)], [I, Theorem 1.5].
-/

noncomputable section

namespace RBM8D

/-- `B_{xy} = W^{-2} (‖x - y‖_L + W)^{-(d-2)}` of [I, (1.18)], with the periodic `ℓ^∞`
distance `‖·‖_L`. -/
def bB (d L W : ℕ) (x y : Zd d L) : ℝ :=
  (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ))

/-- The spectral domain `𝐃(κ, ε) = {E + iη : |E| < 2 - κ, W²/L^{2-ε} ≤ η ≤ 1}`. -/
def specDom (κ ε : ℝ) (W L : ℕ) : Set ℂ :=
  {z | |z.re| < 2 - κ ∧ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ z.im ∧ z.im ≤ 1}

end RBM8D
