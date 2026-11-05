import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw

/-!
# Linear forms of independent Gaussians; conditioning on an independent block

A finite real linear combination of independent centred Gaussians is a centred Gaussian whose
variance is the weighted sum of the variances (the Gaussian entries of [I, Assumption 1.1]).
For independent `U`, `V`, an expectation of `F(U, V)` is the iterated integral against the two
laws, which gives the partial expectations of [I, §1.4].

## Main statements

* `map_sum_const_mul_of_indep` : a finite linear form in independent centred Gaussians is a
  centred Gaussian of variance `∑ a_i² v_i`
-/

namespace RBM8D

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

section General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [DecidableEq ι]

set_option linter.unusedDecidableInType false in
/-- **A finite real linear form in an independent Gaussian family is a centred Gaussian**, with
variance `∑ a_i² v_i`.  Induction on the finite set: a scaled variable is independent of the sum
of the others, and Gaussians convolve. -/
theorem map_sum_const_mul_of_indep {X : ι → Ω → ℝ} {v : ι → ℝ≥0} (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P) (a : ι → ℝ)
    (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω)
      = gaussianReal 0 (∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
  classical
  have hmul : ∀ i, Measurable (fun ω => a i * X i ω) := fun i => (hmeas i).const_mul _
  have hindep' : iIndepFun (fun i ω => a i * X i ω) P :=
    hindep.comp (fun i => fun x : ℝ => a i * x) fun _ => by fun_prop
  have hlaw' : ∀ i, P.map (fun ω => a i * X i ω)
      = gaussianReal 0 (NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
    intro i
    have h : P.map (fun ω => a i * X i ω) = (P.map (X i)).map (fun x : ℝ => a i * x) := by
      rw [Measure.map_map (by fun_prop) (hmeas i)]
      rfl
    rw [h, hlaw i, gaussianReal_map_const_mul (a i)]
    simp
  induction s using Finset.induction with
  | empty => simp [Measure.map_const]
  | insert i₀ s hi₀ ih =>
    have hsum : Measurable (fun ω => ∑ i ∈ s, a i * X i ω) :=
      Finset.measurable_sum _ fun i _ => hmul i
    have hindep0 := hindep'.indepFun_finsetSum_of_notMem (fun i => hmul i) hi₀
    have hfun : (∑ j ∈ s, fun ω => a j * X j ω) = fun ω => ∑ i ∈ s, a i * X i ω := by
      funext ω
      simp [Finset.sum_apply]
    rw [hfun] at hindep0
    have hadd : (fun ω => ∑ i ∈ insert i₀ s, a i * X i ω)
        = (fun ω => a i₀ * X i₀ ω) + (fun ω => ∑ i ∈ s, a i * X i ω) := by
      funext ω
      simp [Finset.sum_insert hi₀]
    rw [hadd, (hindep0.symm).map_add_eq_map_conv_map (hmul i₀) hsum, ih, hlaw' i₀,
      gaussianReal_conv_gaussianReal, Finset.sum_insert hi₀]
    simp

end General

section Block

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

end Block

end RBM8D
