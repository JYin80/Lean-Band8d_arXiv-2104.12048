import RBM8D.Deloc.Eq113
import RBM8D.Deloc.Lemma81
import RBM8D.Joint.Main
import RBM8D.SelfEnergy.Assembly

/-!
# [I, Theorem 1.3]: the joint statement

`Thm13Stmt`: [I, Theorem 1.3] with (1.12) and (1.13) under one set of hypotheses and one
threshold `L₀`, one probability bound per event; it follows from the two statements
`Thm13_eq112Stmt` and `Thm13_eq113Stmt`.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Complex Matrix
open scoped ENNReal

namespace RBM8D

open Graphs

/-- **[I, Theorem 1.3]**, (1.12) and (1.13) jointly: for `d ≥ 8`, `ψ`, `c₀, c₁, κ > 0`,
`γ ∈ (0, 1]`, `K > 1` and all `τ, D > 0` there is one `L₀` such that for `L ≥ L₀`,
`W ≤ ℓ ≤ L^{1−c₀}` and `L^{c₁} ≤ W ≤ L`,
`P(∃ (u, λ) orthonormal eigenbasis of H, |𝓑_{γ,K,ℓ}| / N > W^τ (ℓ²/L² + W^{−d/2})) ≤ L^{−D}` and
`P(∃ λ ∈ (−2+κ, 2−κ), ∃ u, ‖u‖₂ = 1, H u = λ u, ‖u‖_∞ > W^{1+τ}/L) ≤ L^{−D}`. -/
def Thm13Stmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ γ K : ℝ, 0 < γ → γ ≤ 1 → 1 < K → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ (p : SizeL) (ℓ : ℝ), L₀ ≤ p.1.2 → (p.1.1 : ℝ) ≤ ℓ → ℓ ≤ (p.1.2 : ℝ) ^ (1 - c₀) →
    (p.1.2 : ℝ) ^ c₁ ≤ p.1.1 → p.1.1 ≤ p.1.2 →
    rbmLaw d P p {ω | ∃ (u : Zd d p.1.2 → Zd d p.1.2 → ℂ) (lam : Zd d p.1.2 → ℝ),
        IsOrthoEigenbasis (hmat ω) u lam ∧
        (p.1.1 : ℝ) ^ τ * (ℓ ^ 2 / (p.1.2 : ℝ) ^ 2 + (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)) <
          ((locSetB d p.1.2 κ γ K ℓ u lam).card : ℝ) / (p.1.2 : ℝ) ^ d}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D)) ∧
    rbmLaw d P p {ω | ∃ lam : ℝ, lam ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ u : Zd d p.1.2 → ℂ,
        ∑ x, ‖u x‖ ^ 2 = 1 ∧ hmat ω *ᵥ u = (lam : ℂ) • u ∧
        ∃ x, (p.1.1 : ℝ) ^ (1 + τ) / (p.1.2 : ℝ) < ‖u x‖}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))

/-- `Thm13Stmt` from (1.12) and (1.13), with `L₀` the larger of the two thresholds. -/
private theorem Thm13_of_parts (h12 : Thm13_eq112Stmt) (h13 : Thm13_eq113Stmt) : Thm13Stmt := by
  intro d hd P c₀ c₁ κ hc₀ hc₁ hκ γ K hγ hγ1 hK τ D hτ hD
  obtain ⟨L₁, h₁⟩ := h12 d hd P c₀ c₁ κ hc₀ hc₁ hκ γ K hγ hγ1 hK τ D hτ hD
  obtain ⟨L₂, h₂⟩ := h13 d hd P c₀ c₁ κ hc₀ hc₁ hκ γ K hγ hγ1 hK τ D hτ hD
  exact ⟨max L₁ L₂, fun p ℓ hL hWℓ hℓ hcW hWL =>
    ⟨h₁ p ℓ (le_trans (le_max_left _ _) hL) hWℓ hℓ hcW hWL,
      h₂ p ℓ (le_trans (le_max_right _ _) hL) hWℓ hℓ hcW hWL⟩⟩

end RBM8D
