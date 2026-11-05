import RBM8D.LocalLaw.Defs
import RBM8D.LocalLaw.Eta1

/-!
# The continuity step [II, Lemma 7.3] = [I, Lemma 5.3]: a box sum of `B`

The bound `Σ_{‖y − x₀‖_L ≤ K} (B_{xy} + B_{yx}) ≤ C K²/W²` for `d ≥ 2` and integers
`K ∈ [W, L/2]`, from the weak norm of `B` at `(a, b) = (2, 2)`, as needed in the Bessel-inequality
step of [II, (7.6)].
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators
open MeasureTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

open Graphs

/-! ## A Bessel inequality for Gram matrices -/

/-- The box `{y : ‖y − x₀‖_L ≤ K}` of `Z_L^d`. -/
private def Continuity_box (d L : ℕ) [NeZero L] (x₀ : Zd d L) (K : ℕ) : Finset (Zd d L) :=
  Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K)

/-- For `d ≥ 2`: `Σ_{|y − x₀| ≤ K} (B_{xy} + B_{yx}) ≤ C K²/W²` for integers `K ∈ [W, L/2]`
(the weak norm of `B` at `(a, b) = (2, 2)`). -/
private theorem Continuity_boxB (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ K : ℕ, W ≤ K → 2 * K ≤ L → ∀ x x₀ : Zd d L,
      ∑ y ∈ Continuity_box d L x₀ K, (bB d L W x y + bB d L W y x) ≤
        C * (K : ℝ) ^ 2 / (W : ℝ) ^ 2 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, hC⟩ := weak_le_strong d 2 2 (by linarith) (by linarith)
  refine ⟨max C 0, le_max_right _ _, fun L W _ hW K hK1 hK2 x x₀ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hW.trans hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hweak : weakNorm d L W 2 2 (fun x y => bB d L W x y) ≤ max C 0 := by
    have h1 := hC L W hW (fun x y => bB d L W x y)
    rw [(bB_strongNorm d L W hW).1, mul_one] at h1
    exact h1.trans (le_max_left _ _)
  have hnb := (normBasic d L W hW 2 2 (fun x y => bB d L W x y)).2.1 K hK1 hK2 x x₀
  have hnn : ∀ x y : Zd d L, 0 ≤ bB d L W x y := fun x y => by unfold bB; positivity
  simp only [abs_of_nonneg (hnn _ _)] at hnb
  have hcoef : 0 ≤ (W : ℝ) ^ (-(2 : ℝ)) * (K : ℝ) ^ (-(2 * (d : ℝ) / 2 - 2)) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hweak hcoef
  have hKd : (0 : ℝ) < (K : ℝ) ^ d := by positivity
  have h3 : (∑ y ∈ Continuity_box d L x₀ K, (bB d L W x y + bB d L W y x)) / (K : ℝ) ^ d ≤
      (W : ℝ) ^ (-(2 : ℝ)) * (K : ℝ) ^ (-(2 * (d : ℝ) / 2 - 2)) * max C 0 := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hweak hcoef)
    exact hnb
  rw [div_le_iff₀ hKd] at h3
  refine h3.trans (le_of_eq ?_)
  have e1 : (K : ℝ) ^ (-(2 * (d : ℝ) / 2 - 2)) * (K : ℝ) ^ d = (K : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hK0, ← Real.rpow_natCast]
    congr 1
    push_cast; ring
  rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ((W : ℝ) ^ 2)⁻¹ * (K : ℝ) ^ (-(2 * (d : ℝ) / 2 - 2)) * max C 0 * (K : ℝ) ^ d
      = ((W : ℝ) ^ 2)⁻¹ * max C 0 * ((K : ℝ) ^ (-(2 * (d : ℝ) / 2 - 2)) * (K : ℝ) ^ d) := by ring
    _ = _ := by rw [e1]; field_simp

section

open scoped Matrix ComplexOrder

end

section

open scoped Matrix ComplexOrder

end

section

open scoped Matrix ComplexOrder

end

section

open scoped Matrix ComplexOrder

end

/-! ## The exponent rows -/

/-- `B_{xy} ≤ W^{−d}` for `W ≥ 1`, `d ≥ 2`. -/
private theorem Continuity_bB_le {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y ≤ ((W : ℝ) ^ (d : ℝ))⁻¹ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold bB
  have h1 : (((zdistInf d L (x - y) : ℝ) + W)) ^ (2 - (d : ℝ)) ≤ (W : ℝ) ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hW0 (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))])
      (by linarith)
  calc (W : ℝ) ^ (-2 : ℝ) * (((zdistInf d L (x - y) : ℝ) + W)) ^ (2 - (d : ℝ))
      ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hW0.le _)
    _ = ((W : ℝ) ^ (d : ℝ))⁻¹ := by
        rw [← Real.rpow_add hW0, ← Real.rpow_neg hW0.le]; congr 1; ring

end RBM8D
