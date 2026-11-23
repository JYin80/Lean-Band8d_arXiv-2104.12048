module

public import RBM8D.MainDefs
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# Stochastic domination along a filter

[I, Definition 2.3] for families indexed by parameters with their own probability spaces, along a filter `F` at scale `size`; the window adm(c₀, c₁) and the filter "W → ∞ inside adm"; the bridge to the explicit form with `L ≥ L₀`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

universe u v w

namespace RBM8D

/-! ## Stochastic domination along a filter ([I, Definition 2.3]) -/

/-- `W → ∞` inside `adm(c₀, c₁)`. -/
def admFilter (c₀ c₁ : ℝ) : Filter (ℕ × ℕ) := 𝓟 (adm c₀ c₁) ⊓ comap Prod.fst atTop

section StochDom

variable {Par : Type u} {Ω : Par → Type v} [∀ p, MeasurableSpace (Ω p)] {U : Par → Type w}

/-- **[I, Definition 2.3 (i)]** along a filter `F` at scale `size`: `ξ ≺ ζ` uniformly in `u` if
for all `τ, D > 0`, eventually in `F`, `P(∃ u, ξ(u) > size^τ ζ(u)) ≤ size^{-D}`. -/
def StochDom (F : Filter Par) (size : Par → ℝ) (P : ∀ p, Measure (Ω p))
    (ξ ζ : ∀ p, U p → Ω p → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ p in F,
    P p {ω | ∃ u, size p ^ τ * ζ p u ω < ξ p u ω} ≤ ENNReal.ofReal (size p ^ (-D))

end StochDom

theorem tendsto_fst_admFilter :
  ∀ c₀ c₁ : ℝ, Tendsto (fun p : ℕ × ℕ => (p.1 : ℝ)) (admFilter c₀ c₁) atTop := fun _ _ =>
  tendsto_natCast_atTop_atTop.comp (tendsto_comap.mono_left inf_le_right)

end RBM8D
