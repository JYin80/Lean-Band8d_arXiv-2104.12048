import RBM8D.Prob.StochDom

/-!
# Nets in the spectral parameter

Stochastic domination on a set of spectral parameters from a fine net and Lipschitz continuity (the uniformity in z of [I, Theorem 2.16] and [II, Theorem 3.6]).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

universe u v w

namespace RBM8D

/-- Transfer from a net point `w` to a nearby point `z`, at scale `s ≥ 1`: if both functions are
`s ^ C₂`-Lipschitz, `‖z - w‖ ≤ s ^ (-C₁)`, `s ^ (-C₃) ≤ ζ(z)` with `C₂ + C₃ < C₁` and
`3 ≤ q := s ^ (τ / 2)`, then `ξ(w) ≤ q ζ(w)` implies `ξ(z) ≤ q² ζ(z)`. -/
private theorem net_transfer (s C₁ C₂ C₃ q ξz ξw ζz ζw d : ℝ) (hs : 1 ≤ s) (hC : C₂ + C₃ < C₁)
    (hq : 3 ≤ q) (hd : d ≤ s ^ (C₂ - C₁)) (hd0 : 0 ≤ d)
    (hlow : s ^ (-C₃) ≤ ζz) (hξ : |ξz - ξw| ≤ d) (hζ : |ζz - ζw| ≤ d)
    (hnet : ξw ≤ q * ζw) : ξz ≤ q * q * ζz := by
  have hs0 : 0 < s := by linarith
  have h1 : s ^ (C₂ - C₁) ≤ s ^ (-C₃) := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have hdz : d ≤ ζz := hd.trans (h1.trans hlow)
  have hζz : 0 ≤ ζz := hd0.trans hdz
  have hξ' : ξz ≤ ξw + d := by linarith [(abs_le.1 hξ).2]
  have hζ' : ζw ≤ ζz + d := by linarith [(abs_le.1 hζ).1]
  have h2 : q * ζw ≤ q * (2 * ζz) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : 0 ≤ (q * q - 2 * q - 1) * ζz := mul_nonneg (by nlinarith) hζz
  nlinarith

theorem StochDom.of_net :
  ∀ {Par : Type u} {Ω : Par → Type v} [∀ p, MeasurableSpace (Ω p)] {V : Par → Type w}
    (F : Filter Par) (size : Par → ℝ) (P : ∀ p, Measure (Ω p)) (Z : Par → Set ℂ)
    (net : Par → Finset ℂ) (ξ ζ : ∀ p, V p → ℂ → Ω p → ℝ) (C₁ C₂ C₃ : ℝ),
    Tendsto size F atTop → C₂ + C₃ < C₁ →
    (∀ᶠ p in F, ↑(net p) ⊆ Z p ∧ ∀ z ∈ Z p, ∃ w ∈ net p, ‖z - w‖ ≤ size p ^ (-C₁)) →
    (∀ᶠ p in F, ∀ v ω, ∀ z ∈ Z p, ∀ w ∈ Z p,
      |ξ p v z ω - ξ p v w ω| ≤ size p ^ C₂ * ‖z - w‖ ∧
      |ζ p v z ω - ζ p v w ω| ≤ size p ^ C₂ * ‖z - w‖) →
    (∀ᶠ p in F, ∀ v ω, ∀ z ∈ Z p, size p ^ (-C₃) ≤ ζ p v z ω) →
    StochDom F size P (fun p (q : V p × net p) ω => ξ p q.1 q.2 ω)
      (fun p (q : V p × net p) ω => ζ p q.1 q.2 ω) →
    StochDom F size P (fun p (q : V p × Z p) ω => ξ p q.1 q.2 ω)
      (fun p (q : V p × Z p) ω => ζ p q.1 q.2 ω) := by
  intro Par Ω _ V F size P Z net ξ ζ C₁ C₂ C₃ hsize hC hcov hLip hlow hnet τ hτ D hD
  have hτ2 : 0 < τ / 2 := by linarith
  have hq : ∀ᶠ p in F, 3 ≤ size p ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsize).eventually (eventually_ge_atTop 3)
  filter_upwards [hnet (τ / 2) hτ2 D hD, hsize.eventually (eventually_ge_atTop 1), hq, hcov,
    hLip, hlow] with p h1 hs hq3 hcp hLp hlp
  have hs0 : 0 < size p := by linarith
  refine le_trans (measure_mono ?_) h1
  rintro ω ⟨⟨v, z, hz⟩, hω⟩
  obtain ⟨w, hw, hzw⟩ := hcp.2 z hz
  have hwZ : (w : ℂ) ∈ Z p := hcp.1 (Finset.mem_coe.2 hw)
  refine ⟨⟨v, w, hw⟩, ?_⟩
  by_contra hcon
  have hnet' : ξ p v w ω ≤ size p ^ (τ / 2) * ζ p v w ω := not_lt.1 hcon
  have hd : size p ^ C₂ * ‖z - w‖ ≤ size p ^ (C₂ - C₁) := by
    calc size p ^ C₂ * ‖z - w‖ ≤ size p ^ C₂ * size p ^ (-C₁) :=
          mul_le_mul_of_nonneg_left hzw (Real.rpow_nonneg hs0.le _)
      _ = size p ^ (C₂ - C₁) := by rw [← Real.rpow_add hs0]; ring_nf
  have hd0 : 0 ≤ size p ^ C₂ * ‖z - w‖ :=
    mul_nonneg (Real.rpow_nonneg hs0.le _) (norm_nonneg _)
  obtain ⟨hL1, hL2⟩ := hLp v ω z hz w hwZ
  have hres := net_transfer (size p) C₁ C₂ C₃ (size p ^ (τ / 2)) (ξ p v z ω) (ξ p v w ω)
    (ζ p v z ω) (ζ p v w ω) _ hs hC hq3 hd hd0 (hlp v ω z hz) hL1 hL2 hnet'
  have hsq : size p ^ τ = size p ^ (τ / 2) * size p ^ (τ / 2) := by
    rw [← Real.rpow_add hs0]; ring_nf
  have hω' : size p ^ τ * ζ p v z ω < ξ p v z ω := hω
  rw [hsq] at hω'
  linarith

end RBM8D
