module

public import RBM8D.Deloc.Det

@[expose] public section

/-!
# [I, Theorem 1.3], (1.13), from the local law

The sup-norm bound of bulk eigenvectors from the local law [I, Theorem 1.4] and the eigenvector
bound.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Complex Matrix
open scoped ENNReal

namespace RBM8D

/-- (1.13) from the local law. -/
theorem thm13_eq113_ofLocalLaw : LocalLawStmt → Thm13_eq113Stmt := by
  intro hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ γ K hγ hγ1 hK τ D hτ hD
  have hcτ : 0 < c₁ * τ := mul_pos hc₁ hτ
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (c₁ * τ) c₀ := ⟨_, rfl⟩
  have hε : 0 < ε := hεdef ▸ lt_min hcτ hc₀
  have hεc : ε ≤ c₁ * τ := hεdef ▸ min_le_left _ _
  have hεc₀ : ε ≤ c₀ := hεdef ▸ min_le_right _ _
  obtain ⟨L₁, hL₁⟩ := hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ ε 1 (D + d + 1) hε one_pos (by positivity)
  refine ⟨max L₁ ⌈(2 : ℝ) ^ (1 / (c₁ * τ))⌉₊, fun p ℓ hL₀ hWℓ hℓL hLW hWL => ?_⟩
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.2
  have hL0 : (0 : ℝ) < (p.1.2 : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ (p.1.1 : ℝ) := (Real.one_le_rpow hL1 hc₁.le).trans hLW
  have hW0 : (0 : ℝ) < (p.1.1 : ℝ) := by linarith
  have hadm : p.1 ∈ adm c₀ c₁ := ⟨hLW, hWℓ.trans hℓL⟩
  -- `L^{c₁τ} ≤ W^τ`, `L^ε ≤ W^τ` and `2 ≤ W^τ`
  have hLcτ : (p.1.2 : ℝ) ^ (c₁ * τ) ≤ (p.1.1 : ℝ) ^ τ := by
    rw [Real.rpow_mul hL0.le]
    exact Real.rpow_le_rpow (by positivity) hLW hτ.le
  have hLε : (p.1.2 : ℝ) ^ ε ≤ (p.1.1 : ℝ) ^ τ :=
    (Real.rpow_le_rpow_of_exponent_le hL1 hεc).trans hLcτ
  have h2W : (2 : ℝ) ≤ (p.1.1 : ℝ) ^ τ := by
    have h1 : (2 : ℝ) ^ (1 / (c₁ * τ)) ≤ (p.1.2 : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hL₀)
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / (c₁ * τ))) ^ (c₁ * τ) := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hcτ.ne', Real.rpow_one]
      _ ≤ (p.1.2 : ℝ) ^ (c₁ * τ) := Real.rpow_le_rpow (by positivity) h1 hcτ.le
      _ ≤ _ := hLcτ
  -- `η₀ = W²/L^{2−ε}` lies in `(0, 1]` and `2η₀ ≤ (W^{1+τ}/L)²`
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : ℝ, η₀ = (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) := ⟨_, rfl⟩
  have hη₀pos : 0 < η₀ := by rw [hη₀]; positivity
  have hη₀1 : η₀ ≤ 1 := by
    rw [hη₀, div_le_one (by positivity)]
    calc (p.1.1 : ℝ) ^ 2 ≤ ((p.1.2 : ℝ) ^ (1 - c₀)) ^ 2 :=
          pow_le_pow_left₀ hW0.le (hWℓ.trans hℓL) 2
      _ = (p.1.2 : ℝ) ^ ((1 - c₀) * 2) := by rw [Real.rpow_mul hL0.le, Real.rpow_two]
      _ ≤ (p.1.2 : ℝ) ^ (2 - ε) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hkey : 2 * η₀ ≤ ((p.1.1 : ℝ) ^ (1 + τ) / (p.1.2 : ℝ)) ^ 2 := by
    have hLε0 : 0 ≤ (p.1.2 : ℝ) ^ ε := by positivity
    have hprod : 2 * (p.1.2 : ℝ) ^ ε ≤ (p.1.1 : ℝ) ^ τ * (p.1.1 : ℝ) ^ τ :=
      mul_le_mul h2W hLε hLε0 (by linarith)
    rw [hη₀, Real.rpow_sub hL0, Real.rpow_two, Real.rpow_add hW0, Real.rpow_one, div_pow,
      div_div_eq_mul_div, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    have hW2 : 0 ≤ (p.1.1 : ℝ) ^ 2 := by positivity
    nlinarith
  -- the local law at `W^τ B_xx` with `τ = 1`: `W B_xx = W^{1−d} ≤ 1`
  have hWB : ∀ x : Zd d p.1.2, (p.1.1 : ℝ) ^ (1 : ℝ) * bB d p.1.2 p.1.1 x x ≤ 1 := by
    intro x
    have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
    unfold bB
    rw [sub_self, (zdistInf_eq_zero_iff d _).2 rfl, Nat.cast_zero, zero_add, ← mul_assoc,
      ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  refine (measure_mono (μ := rbmLaw d P p) (?_ : _ ⊆ ⋃ x : Zd d p.1.2,
      {ω | ∃ E : ℝ, E ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ η : ℝ,
        (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) ≤ η ∧ η ≤ 1 ∧
        (p.1.1 : ℝ) ^ (1 : ℝ) * bB d p.1.2 p.1.1 x x <
          ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * I))
            (msc ((E : ℂ) + (η : ℂ) * I)) x x‖ ^ 2})).trans ?_
  · rintro ω ⟨lam, hlam, u, hu, hEig, x, hx⟩
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    by_contra hnot
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hnot
    have hErr := (hnot lam hlam η₀ hη₀.ge hη₀1).trans (hWB x)
    set z : ℂ := (lam : ℂ) + (η₀ : ℂ) * I with hz
    have hzim : 0 < z.im := by simp [z, hη₀pos]
    have hm : ‖msc z‖ < 1 := norm_msc_lt_one hzim
    rw [entryErr, ite_eq_left rfl] at hErr
    have hE1 : ‖green (hmat ω) z x x - msc z‖ ≤ 1 := by
      nlinarith [norm_nonneg (green (hmat ω) z x x - msc z)]
    have hG : ‖green (hmat ω) z x x‖ < 2 := by
      have h := norm_add_le (green (hmat ω) z x x - msc z) (msc z)
      rw [sub_add_cancel] at h
      linarith
    have hIm : (green (hmat ω) z x x).im < 2 := (Complex.im_le_norm _).trans_lt hG
    have hu2 : ‖u x‖ ^ 2 ≤ η₀ * (green (hmat ω) z x x).im :=
      eigvecBound (hmat ω) (hmat_isHermitian ω) lam η₀ hη₀pos u hu hEig x
    have hx2 : ((p.1.1 : ℝ) ^ (1 + τ) / (p.1.2 : ℝ)) ^ 2 < ‖u x‖ ^ 2 :=
      pow_lt_pow_left₀ hx (by positivity) two_ne_zero
    nlinarith
  · refine (measure_iUnion_fintype_le _ _).trans ?_
    calc _ ≤ ∑ x : Zd d p.1.2, ENNReal.ofReal ((p.1.2 : ℝ) ^ (-(D + d + 1))) :=
          Finset.sum_le_sum fun x _ => hL₁ p ((le_max_left _ _).trans hL₀) hadm x x
      _ = ENNReal.ofReal (((p.1.2 ^ d : ℕ) : ℝ) * (p.1.2 : ℝ) ^ (-(D + d + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_add hL0]
          exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

section Witness

open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

end RBM8D
