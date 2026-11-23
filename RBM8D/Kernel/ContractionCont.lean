module

public import RBM8D.Kernel.Profile

@[expose] public section

/-!
# The continuum contraction

The ℝ^d form of [I, (B.19)].
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The continuum symbol of `μ_m^{∗n} − (c/(1+c))^n δ₀`: `p ↦ A_ψ(p)^n − (c/(1+c))^n` with
`A_ψ(p) = (m² ψ(p) + c)/(1 + c)`. -/
def contSymbolPow {d : ℕ} (m : ℂ) (c : ℝ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (n : ℕ)
    (p : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((m ^ 2 * (ψ p : ℂ) + c) / (1 + c)) ^ n - ((c : ℂ) / (1 + c)) ^ n

section Witness

end Witness

end RBM8D
