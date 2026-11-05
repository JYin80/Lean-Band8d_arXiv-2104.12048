import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

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

/-- An injective natural number key on a finite index type; it orients the off-diagonal pairs. -/
def idxKey (ι : Type u) [Fintype ι] (x : ι) : ℕ := (Fintype.equivFin ι x).val

/-- Off-diagonal pairs `(x, y)` with `idxKey x < idxKey y`: one per unordered pair `{x, y}`. -/
abbrev OffPair (ι : Type u) [Fintype ι] : Type u := {p : ι × ι // idxKey ι p.1 < idxKey ι p.2}

/-- Real coordinates of a Hermitian matrix: `h_xx` for each `x`, and `Re h_xy` (`true`),
`Im h_xy` (`false`) for each oriented off-diagonal pair. -/
abbrev Coord (ι : Type u) [Fintype ι] : Type u := ι ⊕ (OffPair ι × Bool)

/-- The sample space: one real number per coordinate. -/
abbrev Sample (ι : Type u) [Fintype ι] : Type u := Coord ι → ℝ

/-- Variance of a coordinate: `s_xx` on the diagonal, `s_xy / 2` for `Re h_xy` and `Im h_xy`
([I, Assumption 1.1], with a real diagonal of variance `s_xx`). -/
def coordVar (S : Matrix ι ι ℝ) : Coord ι → ℝ≥0
  | .inl x => (S x x).toNNReal
  | .inr (e, _) => (S e.1.1 e.1.2 / 2).toNNReal

/-- The law of [I, Assumption 1.1]: independent centred real Gaussians, one per coordinate. -/
def gaussLaw (S : Matrix ι ι ℝ) : Measure (Sample ι) :=
  Measure.pi fun c => gaussianReal 0 (coordVar S c)

/-- The Hermitian matrix `H(ω)`: `h_xy = Re + i Im` for `idxKey x < idxKey y`, `h_yx = conj h_xy`,
and `h_xx` real. -/
def hmat (ω : Sample ι) : Matrix ι ι ℂ :=
  Matrix.of fun x y =>
    if h : idxKey ι x < idxKey ι y then
      (ω (.inr (⟨(x, y), h⟩, true)) : ℂ) + I * (ω (.inr (⟨(x, y), h⟩, false)) : ℂ)
    else if h' : idxKey ι y < idxKey ι x then
      (ω (.inr (⟨(y, x), h'⟩, true)) : ℂ) - I * (ω (.inr (⟨(y, x), h'⟩, false)) : ℂ)
    else (ω (.inl x) : ℂ)

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
private instance gaussLaw_isProb (S : Matrix ι ι ℝ) : IsProbabilityMeasure (gaussLaw S) := by
  unfold gaussLaw; infer_instance

theorem isProbabilityMeasure_gaussLaw {ι : Type u} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) :
    IsProbabilityMeasure (gaussLaw S) := inferInstance

end Model

section Instance

end Instance

end RBM8D
