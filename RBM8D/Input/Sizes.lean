import RBM8D.Prob.Model
import RBM8D.Prob.StochDom
import RBM8D.Prob.Partial
import RBM8D.Basic.Minor
import RBM8D.Basic.Domain
import RBM8D.Basic.Semicircle
import RBM8D.Profile.Basic

/-!
# Sizes and the filter `W → ∞` inside `adm(c₀, c₁)`

The parameter set of sizes `(W, L)` with `L ≠ 0`, the filter along which the input estimates
[I, Lemma 5.1] and [II, Lemma 8.9] are stated, the law of [I, Assumption 1.1] on `Z_L^d`, and the
explicit form of `≺` along this filter.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

/-- Sizes `(W, L)` with `L ≠ 0`: the parameter set of the model on `Z_L^d`. -/
abbrev SizeL : Type := {p : ℕ × ℕ // p.2 ≠ 0}

instance SizeL.neZero (p : SizeL) : NeZero p.1.2 := ⟨p.2⟩

/-- `W → ∞` inside `adm(c₀, c₁)`, on the sizes with `L ≠ 0`. -/
def admFilterL (c₀ c₁ : ℝ) : Filter SizeL := comap Subtype.val (admFilter c₀ c₁)

/-- The scale `W` of `≺`. -/
def sizeW (p : SizeL) : ℝ := p.1.1

/-- The law of [I, Assumption 1.1] on `Z_L^d` with the variance matrix `S_{xy} = f_{W,L}(x − y)`. -/
def rbmLaw (d : ℕ) (P : Profile d) (p : SizeL) : Measure (Sample (Zd d p.1.2)) :=
  gaussLaw (Smat P.ψ p.1.1 p.1.2)

/-- `W → ∞` along `admFilterL c₀ c₁`. -/
theorem tendsto_sizeW_admFilterL :
  ∀ c₀ c₁ : ℝ, Tendsto sizeW (admFilterL c₀ c₁) atTop := by
  intro c₀ c₁
  exact (tendsto_fst_admFilter c₀ c₁).comp tendsto_comap

/-- On `adm(c₀, c₁)`, `|Z_L^d| = L^d ≤ W^{d/c₁}`. -/
theorem card_Zd_le_adm :
  ∀ (d : ℕ) (c₀ c₁ : ℝ), 0 < c₁ → ∀ p : SizeL, p.1 ∈ adm c₀ c₁ →
    (Fintype.card (Zd d p.1.2) : ℝ) ≤ sizeW p ^ ((d : ℝ) / c₁) := by
  intro d c₀ c₁ hc₁ p hp
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  have hpos : 0 < (p.1.2 : ℝ) ^ c₁ := Real.rpow_pos_of_pos (by linarith) _
  have hW0 : (0 : ℝ) ≤ (p.1.1 : ℝ) := Nat.cast_nonneg _
  have hLW : (p.1.2 : ℝ) ≤ (p.1.1 : ℝ) ^ (1 / c₁) := by
    calc (p.1.2 : ℝ) = ((p.1.2 : ℝ) ^ c₁) ^ (1 / c₁) := by
          rw [← Real.rpow_mul (by linarith), mul_one_div_cancel hc₁.ne', Real.rpow_one]
      _ ≤ (p.1.1 : ℝ) ^ (1 / c₁) := Real.rpow_le_rpow hpos.le hp.1 (by positivity)
  have hcard : Fintype.card (Zd d p.1.2) = p.1.2 ^ d := card_Zd d p.1.2
  rw [hcard, Nat.cast_pow]
  calc (p.1.2 : ℝ) ^ d ≤ ((p.1.1 : ℝ) ^ (1 / c₁)) ^ d := pow_le_pow_left₀ (by linarith) hLW d
    _ = sizeW p ^ ((d : ℝ) / c₁) := by
        rw [sizeW, ← Real.rpow_natCast, ← Real.rpow_mul hW0]
        congr 1; ring

end RBM8D
