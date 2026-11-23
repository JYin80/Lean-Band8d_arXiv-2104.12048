module

public import RBM8D.MainDefs
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# The Gaussian model

The random band matrix of [I, Assumption 1.1] on a finite index set with a real symmetric variance matrix `S ≥ 0`: real coordinates (one per diagonal entry, two per unordered off-diagonal pair), the product Gaussian law and the Hermitian matrix `H(ω)`; diagonal entries are real with variance `s_xx`, off-diagonal real and imaginary parts have variance `s_xy/2` each.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

universe u v w

namespace RBM8D

/-! ## The model of [I, Assumption 1.1] -/

section Model

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The coordinates on which the entry `h_ab` depends. -/
def entryCoords (a b : ι) : Finset (Coord ι) :=
  Finset.univ.filter fun c =>
    (match c with
      | .inl x => decide (x = a ∧ x = b)
      | .inr (e, _) => decide ((e.1.1 = a ∧ e.1.2 = b) ∨ (e.1.1 = b ∧ e.1.2 = a))) = true

/-- The coordinates of row and column `x`: those of `h_xy`, `y ∈ ι`. -/
def rowCoords (x : ι) : Finset (Coord ι) := Finset.univ.biUnion (entryCoords x)

/-- Bounded measurable functions of the sample. -/
def BddMeas (F : Sample ι → ℂ) : Prop := Measurable F ∧ ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C

omit [DecidableEq ι] in
theorem idxKey_injective : Function.Injective (idxKey ι) := fun _ _ h =>
  (Fintype.equivFin ι).injective (Fin.val_injective h)

omit [DecidableEq ι] in
/-- `H(ω)` is Hermitian for every sample `ω`. -/
theorem hmat_isHermitian (ω : Sample ι) : (hmat ω).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, hmat, Matrix.of_apply]
  rcases lt_trichotomy (idxKey ι x) (idxKey ι y) with h | h | h
  · simp only [h, lt_asymm h, dite_true, dite_false, star_sub, star_mul', Complex.star_def,
      conj_ofReal, conj_I]
    ring
  · obtain rfl := idxKey_injective h
    simp
  · simp only [h, lt_asymm h, dite_true, dite_false, star_add, star_mul', Complex.star_def,
      conj_ofReal, conj_I]
    ring

omit [DecidableEq ι] in
instance gaussLaw_isProb (S : Matrix ι ι ℝ) : IsProbabilityMeasure (gaussLaw S) := by
  unfold gaussLaw; infer_instance

theorem isProbabilityMeasure_gaussLaw {ι : Type u} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) :
    IsProbabilityMeasure (gaussLaw S) := inferInstance

end Model

section Instance

end Instance

end RBM8D
