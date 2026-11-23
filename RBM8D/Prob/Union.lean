module

public import RBM8D.Prob.StochDom

@[expose] public section

/-!
# Union bounds and moments

Stochastic domination ([I, Definition 2.3]) from bounds for each index, by a union over at most
size^C indices: `StochDom.of_forall`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

universe u v w

namespace RBM8D

/-- Union bound over a finite index type: if each `A u` has measure at most `δ`, the union has
measure at most `#U · δ`. -/
private theorem union_bound_real {Ω : Type v} [MeasurableSpace Ω] {U : Type w} [Fintype U]
    (μ : Measure Ω) (A : U → Set Ω) (δ : ℝ)
    (h : ∀ u, μ (A u) ≤ ENNReal.ofReal δ) :
    μ (⋃ u, A u) ≤ ENNReal.ofReal ((Fintype.card U : ℝ) * δ) := by
  calc μ (⋃ u, A u) ≤ ∑ u, μ (A u) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _u : U, ENNReal.ofReal δ := Finset.sum_le_sum fun u _ => h u
    _ = ENNReal.ofReal ((Fintype.card U : ℝ) * δ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Union bound at scale `s`: at most `s ^ C` events, each of measure at most
`s ^ (-(D + max C 0))`, give a union of measure at most `s ^ (-D)`. -/
private theorem union_bound_size {Ω : Type v} [MeasurableSpace Ω] {U : Type w} [Fintype U]
    (μ : Measure Ω) (A : U → Set Ω) (s C D : ℝ) (hs : 1 ≤ s)
    (hcard : (Fintype.card U : ℝ) ≤ s ^ C)
    (h : ∀ u, μ (A u) ≤ ENNReal.ofReal (s ^ (-(D + max C 0)))) :
    μ (⋃ u, A u) ≤ ENNReal.ofReal (s ^ (-D)) := by
  have hs0 : 0 < s := by linarith
  refine le_trans (union_bound_real μ A _ h)
    (ENNReal.ofReal_le_ofReal ?_)
  have h1 : s ^ C ≤ s ^ (max C 0) := Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
  calc (Fintype.card U : ℝ) * s ^ (-(D + max C 0)) ≤ s ^ (max C 0) * s ^ (-(D + max C 0)) :=
        mul_le_mul_of_nonneg_right (hcard.trans h1) (Real.rpow_nonneg hs0.le _)
    _ = s ^ (-D) := by rw [← Real.rpow_add hs0]; ring_nf

theorem StochDom.of_forall :
  ∀ {Par : Type u} {Ω : Par → Type v} [∀ p, MeasurableSpace (Ω p)] {U : Par → Type w}
    [∀ p, Fintype (U p)] (F : Filter Par) (size : Par → ℝ) (P : ∀ p, Measure (Ω p))
    (ξ ζ : ∀ p, U p → Ω p → ℝ) (C : ℝ),
    Tendsto size F atTop → (∀ᶠ p in F, (Fintype.card (U p) : ℝ) ≤ size p ^ C) →
    (∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ p in F, ∀ u,
      P p {ω | size p ^ τ * ζ p u ω < ξ p u ω} ≤ ENNReal.ofReal (size p ^ (-D))) →
    StochDom F size P ξ ζ := by
  intro Par Ω _ U _ F size P ξ ζ C hsize hcard h τ hτ D hD
  have hD' : 0 < D + max C 0 := by have := le_max_right C 0; linarith
  filter_upwards [hsize.eventually (eventually_ge_atTop 1), hcard, h τ hτ _ hD'] with p hs hc hp
  have hset : {ω | ∃ u, size p ^ τ * ζ p u ω < ξ p u ω} =
      ⋃ u, {ω | size p ^ τ * ζ p u ω < ξ p u ω} := by ext ω; simp
  rw [hset]
  exact union_bound_size (P p) _ (size p) C D hs hc hp

end RBM8D
