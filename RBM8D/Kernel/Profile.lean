import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import RBM8D.Basic.Lattice
import RBM8D.Basic.Semicircle
import RBM8D.Prob.StochDom

/-!
# Profile hypotheses

The symbol bound `SymbolBound` and the profile shape `ProfileShape` ([I, Asm 1.2]).
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

/-- (H1)–(H2): `ψ` is a real Schwartz function with values in `[−1 + c′, 1]`, `c′ > 0`. -/
structure SymbolBound {d : ℕ} (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (c' : ℝ) : Prop where
  pos : 0 < c'
  range : ∀ p, -1 + c' ≤ ψ p ∧ ψ p ≤ 1

/-- The shape conditions of [I, Assumption 1.2 (i)–(ii)] and the symmetry of `ψ`. -/
structure ProfileShape {d : ℕ} (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) : Prop where
  pos : 0 < cψ
  at_zero : ψ 0 = 1
  le_max : ∀ p, ψ p ≤ max (1 - cψ * ‖p‖ ^ 2) (1 - cψ)
  symm : ∀ p, ψ (-p) = ψ p

end RBM8D
