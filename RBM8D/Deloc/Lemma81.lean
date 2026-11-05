import RBM8D.Deloc.Det
import RBM8D.Deloc.Ward

/-!
# [I, Lemma 8.1] and [I, Theorem 1.3], (1.12), from the local law

The bound (8.1) on the number of bulk indices of `𝓑̃_{M,K,ℓ}` from the local law
[I, Theorem 1.4], (8.2) and the shell sum, and (1.12) from (8.1) and `𝓑 ⊂ 𝓑̃`.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Complex Matrix
open scoped ENNReal

namespace RBM8D

/-- The exponent algebra of the proof of [I, Lemma 8.1]: with
`ℓ̃ = ℓ^{M/(M+4)} L^{(d+4)/(M+4)}` and `A = (ℓ^{M/(M+4)} / L^{(M−d)/(M+4)})²`,
`ℓ̃² = A L²` and `(ℓ/ℓ̃)^{M/2} L^{d/2} = A`. -/
private theorem expAlg (ℓ L M : ℝ) (d : ℕ) (hℓ : 0 < ℓ) (hL : 0 < L) (hM : 0 < M + 4) :
    (ℓ ^ (M / (M + 4)) * L ^ (((d : ℝ) + 4) / (M + 4))) ^ 2 =
        (ℓ ^ (M / (M + 4)) / L ^ ((M - d) / (M + 4))) ^ 2 * L ^ 2 ∧
      (ℓ / (ℓ ^ (M / (M + 4)) * L ^ (((d : ℝ) + 4) / (M + 4)))) ^ (M / 2) *
          L ^ ((d : ℝ) / 2) =
        (ℓ ^ (M / (M + 4)) / L ^ ((M - d) / (M + 4))) ^ 2 := by
  obtain ⟨s, rfl⟩ : ∃ s, ℓ = Real.exp s := ⟨Real.log ℓ, (Real.exp_log hℓ).symm⟩
  obtain ⟨t, rfl⟩ : ∃ t, L = Real.exp t := ⟨Real.log L, (Real.exp_log hL).symm⟩
  simp only [← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add, ← Real.exp_nat_mul]
  constructor
  · congr 1; field_simp; ring
  · congr 1; field_simp; ring

/-- `ℓ ≤ ℓ̃ = ℓ^{M/(M+4)} L^{(d+4)/(M+4)}` for `0 < ℓ ≤ L`, `L ≥ 1`. -/
private theorem le_ellt (ℓ L M : ℝ) (d : ℕ) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) (hL1 : 1 ≤ L)
    (hM : 0 < M + 4) : ℓ ≤ ℓ ^ (M / (M + 4)) * L ^ (((d : ℝ) + 4) / (M + 4)) := by
  have hL : 0 < L := by linarith
  have hst : Real.log ℓ ≤ Real.log L := Real.log_le_log hℓ hℓL
  have ht : 0 ≤ Real.log L := Real.log_nonneg hL1
  obtain ⟨s, rfl⟩ : ∃ s, ℓ = Real.exp s := ⟨Real.log ℓ, (Real.exp_log hℓ).symm⟩
  obtain ⟨t, rfl⟩ : ∃ t, L = Real.exp t := ⟨Real.log L, (Real.exp_log hL).symm⟩
  simp only [Real.log_exp] at hst ht
  simp only [← Real.exp_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [mul_div_assoc', mul_div_assoc', ← add_div, le_div_iff₀ hM]
  nlinarith

/-- `(ℓ^{M/(M+4)} / L^{(M−d)/(M+4)})² ≤ L^c ℓ²/L²` for `ℓ, L ≥ 1` and `2d + 8 ≤ c (M + 4)`:
the comparison of (8.1) with (1.12) in the proof of [I, Theorem 1.3]. -/
private theorem A_le (ℓ L M c : ℝ) (d : ℕ) (hℓ1 : 1 ≤ ℓ) (hL1 : 1 ≤ L) (hM : 0 < M + 4)
    (hc : 2 * (d : ℝ) + 8 ≤ c * (M + 4)) :
    (ℓ ^ (M / (M + 4)) / L ^ ((M - d) / (M + 4))) ^ 2 ≤ L ^ c * (ℓ ^ 2 / L ^ 2) := by
  have hℓ : 0 < ℓ := by linarith
  have hL : 0 < L := by linarith
  have hs : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have ht : 0 ≤ Real.log L := Real.log_nonneg hL1
  obtain ⟨s, rfl⟩ : ∃ s, ℓ = Real.exp s := ⟨Real.log ℓ, (Real.exp_log hℓ).symm⟩
  obtain ⟨t, rfl⟩ : ∃ t, L = Real.exp t := ⟨Real.log L, (Real.exp_log hL).symm⟩
  simp only [Real.log_exp] at hs ht
  simp only [← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add, ← Real.exp_nat_mul,
    Real.exp_le_exp]
  have key : (2 : ℝ) * (s * (M / (M + 4)) - t * ((M - d) / (M + 4))) =
      t * c + (2 * s - 2 * t) - (t * (c * (M + 4) - (2 * d + 8)) + 8 * s) / (M + 4) := by
    field_simp; ring
  push_cast
  rw [key]
  have : 0 ≤ (t * (c * (M + 4) - (2 * d + 8)) + 8 * s) / (M + 4) := by
    apply div_nonneg _ hM.le; nlinarith
  linarith

open scoped Classical in
/-- The deterministic part of the proof of [I, Lemma 8.1]: if at `z = E + iη`, `0 < η ≤ 2 − κ`,
every entry obeys `|G_xy − m δ_xy|² ≤ W^{τ'} B_xy` for all `E ∈ (−2+κ, 2−κ)`, with `τ' ≤ 1`,
then `|𝓑̃_{M,K,ℓ}| ≤ N (100 δ + 16 Φ)` with `δ = K (ℓ/ℓ̃)^{M/2} L^{d/2}` and
`Φ = η (4 + W^{τ'} 2d 3^{d−1} ℓ̃² W^{−2})`, from `𝓑̃ ⊂ 𝒜_{δ,ℓ̃}`, (8.2) and the shell sum. -/
private theorem cardBound (d L W : ℕ) [NeZero L] (hd : 8 ≤ d) (hW : 1 ≤ W)
    (H : Matrix (Zd d L) (Zd d L) ℂ) (hH : H.IsHermitian) (u : Zd d L → Zd d L → ℂ)
    (lam : Zd d L → ℝ) (hu : IsOrthoEigenbasis H u lam) (κ η τ' ℓ ℓt M K : ℝ) (hκ : 0 < κ)
    (hη : 0 < η) (hηκ : η ≤ 2 - κ) (hτ' : τ' ≤ 1) (hℓ : 0 < ℓ) (hℓt : 0 < ℓt) (hM : 0 ≤ M)
    (hK : 0 ≤ K)
    (hgood : ∀ x y : Zd d L, ∀ E ∈ Set.Ioo (-2 + κ) (2 - κ),
      ‖entryErr (green H ((E : ℂ) + (η : ℂ) * I)) (msc ((E : ℂ) + (η : ℂ) * I)) x y‖ ^ 2 ≤
        (W : ℝ) ^ τ' * bB d L W x y) :
    ((locSetBt d L κ M K ℓ u lam).card : ℝ) ≤
      (L : ℝ) ^ d * (100 * (K * (ℓ / ℓt) ^ (M / 2) * (L : ℝ) ^ ((d : ℝ) / 2)) +
        16 * (η * (4 + (W : ℝ) ^ τ' * (2 * d * 3 ^ (d - 1) * ℓt ^ 2 * (W : ℝ) ^ (-2 : ℝ))))) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set δ := K * (ℓ / ℓt) ^ (M / 2) * (L : ℝ) ^ ((d : ℝ) / 2) with hδ
  set Φ := η * (4 + (W : ℝ) ^ τ' * (2 * d * 3 ^ (d - 1) * ℓt ^ 2 * (W : ℝ) ^ (-2 : ℝ)))
    with hΦ
  have hδ0 : 0 ≤ δ := by positivity
  have hΦ0 : 0 ≤ Φ := by positivity
  have hBdiag : ∀ x : Zd d L, (W : ℝ) ^ τ' * bB d L W x x ≤ 1 := by
    intro x
    have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
    unfold bB
    rw [sub_self, (zdistInf_eq_zero_iff d _).2 rfl, Nat.cast_zero, zero_add, ← mul_assoc,
      ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hyp82 : ∀ x, ∀ E ∈ Set.Ioo (-2 + κ) (2 - κ),
      (green H ((E : ℂ) + (η : ℂ) * I) x x).im ≤ 2 ∧
      η * ∑ y ∈ Finset.univ.filter (fun y => (zdistInf d L (y - x) : ℝ) < ℓt),
        ‖green H ((E : ℂ) + (η : ℂ) * I) y x‖ ^ 2 ≤ Φ := by
    intro x E hE
    set z : ℂ := (E : ℂ) + (η : ℂ) * I with hz
    have hzim : 0 < z.im := by simp [z, hη]
    have hm : ‖msc z‖ < 1 := norm_msc_lt_one hzim
    have hdiag := (hgood x x E hE).trans (hBdiag x)
    rw [entryErr, ite_eq_left rfl] at hdiag
    have hE1 : ‖green H z x x - msc z‖ ≤ 1 := by
      nlinarith [norm_nonneg (green H z x x - msc z)]
    have hG : ‖green H z x x‖ < 2 := by
      have h := norm_add_le (green H z x x - msc z) (msc z)
      rw [sub_add_cancel] at h
      linarith
    refine ⟨(Complex.im_le_norm _).trans hG.le, ?_⟩
    have hxmem : x ∈ Finset.univ.filter (fun y => (zdistInf d L (y - x) : ℝ) < ℓt) := by
      simp [sub_self, (zdistInf_eq_zero_iff d L).2 rfl, hℓt]
    have hshell : (Finset.univ.filter (fun y => (zdistInf d L (y - x) : ℝ) < ℓt)).erase x =
        Finset.univ.filter (fun y : Zd d L =>
          0 < zdistInf d L (y - x) ∧ (zdistInf d L (y - x) : ℝ) < ℓt) := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, hlt⟩
        refine ⟨Nat.pos_of_ne_zero fun h0 => hne ?_, hlt⟩
        exact sub_eq_zero.mp ((zdistInf_eq_zero_iff d L).mp h0)
      · rintro ⟨hpos, hlt⟩
        refine ⟨?_, hlt⟩
        rintro rfl
        rw [sub_self, (zdistInf_eq_zero_iff d L).2 rfl] at hpos
        exact lt_irrefl _ hpos
    rw [← Finset.add_sum_erase _ _ hxmem, hshell]
    have hoff : ∀ y ∈ Finset.univ.filter (fun y : Zd d L =>
        0 < zdistInf d L (y - x) ∧ (zdistInf d L (y - x) : ℝ) < ℓt),
        ‖green H z y x‖ ^ 2 ≤ (W : ℝ) ^ τ' * bB d L W x y := by
      intro y hy
      have hne : y ≠ x := by
        rintro rfl
        simp [sub_self, (zdistInf_eq_zero_iff d L).2 rfl] at hy
      have h := hgood y x E hE
      rw [entryErr, ite_eq_right hne, sub_zero] at h
      have hsym : bB d L W y x = bB d L W x y := by
        unfold bB; rw [← neg_sub, zdistInf_neg]
      rwa [hsym] at h
    have hsum := (Finset.sum_le_sum hoff).trans_eq (Finset.mul_sum _ _ _).symm
    have hsh := shellSum d L W (by omega) hW ℓt x
    have hx4 : ‖green H z x x‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (green H z x x)]
    have hWτ : 0 ≤ (W : ℝ) ^ τ' := by positivity
    rw [hΦ]
    refine mul_le_mul_of_nonneg_left (add_le_add hx4 (hsum.trans ?_)) hη.le
    exact mul_le_mul_of_nonneg_left hsh hWτ
  have h82 := eq82Det d L H hH u lam hu κ η ℓt δ Φ hκ hη hηκ hδ0 hyp82
  have hsub := btSubA d L u lam κ M K ℓ ℓt hℓ hℓt hM
  have hcard : ((locSetBt d L κ M K ℓ u lam).card : ℝ) ≤ (locSetA d L κ δ ℓt u lam).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hAN : ((locSetA d L κ δ ℓt u lam).card : ℝ) ≤ (L : ℝ) ^ d := by
    have h := Finset.card_le_univ (locSetA d L κ δ ℓt u lam)
    rw [card_Zd] at h
    exact_mod_cast h
  have hN : (0 : ℝ) ≤ (L : ℝ) ^ d := by positivity
  refine hcard.trans ?_
  rcases le_or_gt δ (1 / 100) with hδs | hδl
  · have hs2 : Real.sqrt (2 * Real.pi) < 3 := by
      have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
      have h2 := Real.sqrt_nonneg (2 * Real.pi)
      nlinarith [Real.pi_le_four]
    have hc : 1 / 4 ≤ Real.pi / 4 - 6 * Real.sqrt (2 * Real.pi) * δ := by
      nlinarith [Real.two_le_pi, Real.sqrt_nonneg (2 * Real.pi)]
    have hA0 : (0 : ℝ) ≤ (locSetA d L κ δ ℓt u lam).card := Nat.cast_nonneg _
    have h4 : (4 - 2 * κ) * (L : ℝ) ^ d * Φ ≤ 4 * (L : ℝ) ^ d * Φ := by
      have := mul_nonneg hN hΦ0
      nlinarith
    nlinarith [mul_nonneg hN hδ0]
  · nlinarith [mul_nonneg hN hΦ0]

/-- (8.1) from the local law. -/
theorem lemma81_ofLocalLaw : LocalLawStmt → Lemma81Stmt := by
  intro hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ M K hM hK τ D hτ hD
  by_cases hκ2 : 2 ≤ κ
  · refine ⟨0, fun p ℓ _ _ _ _ _ => ?_⟩
    refine le_of_eq_of_le (measure_mono_null (fun ω hω => ?_) measure_empty) zero_le
    obtain ⟨u, lam, -, hlt⟩ := hω
    have hempty : locSetBt d p.1.2 κ M K ℓ u lam = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun α hα => ?_
      simp only [locSetBt, Finset.mem_filter, Set.mem_Ioo] at hα
      linarith [hα.2.1.1, hα.2.1.2]
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div] at hlt
    have : 0 ≤ (p.1.1 : ℝ) ^ τ * ((ℓ ^ (M / (M + 4)) / (p.1.2 : ℝ) ^ ((M - d) / (M + 4))) ^ 2 +
        (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)) := by positivity
    exact absurd hlt (not_lt.mpr this)
  rw [not_le] at hκ2
  have h2κ : 0 < 2 - κ := by linarith
  have hcτ : 0 < c₁ * τ := mul_pos hc₁ hτ
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (c₁ * τ / 4) c₀ := ⟨_, rfl⟩
  have hε : 0 < ε := hεdef ▸ lt_min (by positivity) hc₀
  have hεc : ε ≤ c₁ * τ / 4 := hεdef ▸ min_le_left _ _
  have hεc₀ : ε ≤ c₀ := hεdef ▸ min_le_right _ _
  obtain ⟨τ', hτ'def⟩ : ∃ τ' : ℝ, τ' = min (τ / 4) 1 := ⟨_, rfl⟩
  have hτ' : 0 < τ' := hτ'def ▸ lt_min (by positivity) one_pos
  have hτ'τ : τ' ≤ τ / 4 := hτ'def ▸ min_le_left _ _
  have hτ'1 : τ' ≤ 1 := hτ'def ▸ min_le_right _ _
  obtain ⟨L₁, hL₁⟩ := hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ ε τ' (D + 2 * d) hε hτ' (by positivity)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * (d : ℝ) * 3 ^ (d - 1) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC ▸ by positivity
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 100 * K + 16 * (4 + C) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; nlinarith
  refine ⟨max L₁ (max ⌈Q ^ (2 / (c₁ * τ))⌉₊ ⌈(2 - κ) ^ (-1 / c₀)⌉₊),
    fun p ℓ hL₀ hWℓ hℓL hLW hWL => ?_⟩
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.2
  have hL0 : (0 : ℝ) < (p.1.2 : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ (p.1.1 : ℝ) := (Real.one_le_rpow hL1 hc₁.le).trans hLW
  have hW0 : (0 : ℝ) < (p.1.1 : ℝ) := by linarith
  have hℓ1 : (1 : ℝ) ≤ ℓ := hW1.trans hWℓ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hℓL' : ℓ ≤ (p.1.2 : ℝ) :=
    hℓL.trans (Real.rpow_le_self_of_one_le hL1 (by linarith))
  have hadm : p.1 ∈ adm c₀ c₁ := ⟨hLW, hWℓ.trans hℓL⟩
  have hM4 : 0 < M + 4 := by linarith
  -- powers of `W` and `L`
  have hWτ'4 : (p.1.1 : ℝ) ^ τ' ≤ (p.1.1 : ℝ) ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hW1 hτ'τ
  have hLε4 : (p.1.2 : ℝ) ^ ε ≤ (p.1.1 : ℝ) ^ (τ / 4) := by
    calc (p.1.2 : ℝ) ^ ε ≤ (p.1.2 : ℝ) ^ (c₁ * (τ / 4)) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = ((p.1.2 : ℝ) ^ c₁) ^ (τ / 4) := Real.rpow_mul hL0.le _ _
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hLW (by positivity)
  have hhalf : (p.1.1 : ℝ) ^ (τ / 4) * (p.1.1 : ℝ) ^ (τ / 4) = (p.1.1 : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hhalf2 : (p.1.1 : ℝ) ^ (τ / 2) * (p.1.1 : ℝ) ^ (τ / 2) = (p.1.1 : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hY : (p.1.1 : ℝ) ^ τ' * (p.1.2 : ℝ) ^ ε ≤ (p.1.1 : ℝ) ^ (τ / 2) := by
    rw [← hhalf]; exact mul_le_mul hWτ'4 hLε4 (by positivity) (by positivity)
  have hWτ'1 : (1 : ℝ) ≤ (p.1.1 : ℝ) ^ τ' := Real.one_le_rpow hW1 hτ'.le
  have hW2τ1 : (1 : ℝ) ≤ (p.1.1 : ℝ) ^ (τ / 2) := Real.one_le_rpow hW1 (by positivity)
  have hQW : Q ≤ (p.1.1 : ℝ) ^ (τ / 2) := by
    have hn : ⌈Q ^ (2 / (c₁ * τ))⌉₊ ≤ p.1.2 :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hL₀)
    have h1 : Q ^ (2 / (c₁ * τ)) ≤ (p.1.2 : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    calc Q = (Q ^ (2 / (c₁ * τ))) ^ (c₁ * (τ / 2)) := by
          rw [← Real.rpow_mul hQ0, show 2 / (c₁ * τ) * (c₁ * (τ / 2)) = 1 by field_simp,
            Real.rpow_one]
      _ ≤ (p.1.2 : ℝ) ^ (c₁ * (τ / 2)) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = ((p.1.2 : ℝ) ^ c₁) ^ (τ / 2) := Real.rpow_mul hL0.le _ _
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hLW (by positivity)
  -- `η₀ = W²/L^{2−ε}` lies in `(0, min(1, 2 − κ)]`
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : ℝ, η₀ = (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) := ⟨_, rfl⟩
  have hη₀pos : 0 < η₀ := by rw [hη₀]; positivity
  have hη₀c : η₀ ≤ (p.1.2 : ℝ) ^ (-c₀) := by
    rw [hη₀, div_le_iff₀ (by positivity), ← Real.rpow_add hL0]
    calc (p.1.1 : ℝ) ^ 2 ≤ ((p.1.2 : ℝ) ^ (1 - c₀)) ^ 2 :=
          pow_le_pow_left₀ hW0.le (hWℓ.trans hℓL) 2
      _ = (p.1.2 : ℝ) ^ ((1 - c₀) * 2) := by rw [Real.rpow_mul hL0.le, Real.rpow_two]
      _ ≤ (p.1.2 : ℝ) ^ (-c₀ + (2 - ε)) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hη₀1 : η₀ ≤ 1 := hη₀c.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  have hη₀κ : η₀ ≤ 2 - κ := by
    refine hη₀c.trans ?_
    have hn : ⌈(2 - κ) ^ (-1 / c₀)⌉₊ ≤ p.1.2 :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hL₀)
    have h1 : (2 - κ) ^ (-1 / c₀) ≤ (p.1.2 : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h2 : (2 - κ)⁻¹ ≤ (p.1.2 : ℝ) ^ c₀ := by
      calc (2 - κ)⁻¹ = ((2 - κ) ^ (-1 / c₀)) ^ c₀ := by
            rw [← Real.rpow_mul h2κ.le, show -1 / c₀ * c₀ = -1 by field_simp,
              Real.rpow_neg_one]
        _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 hc₀.le
    rw [Real.rpow_neg hL0.le]
    exact inv_le_of_inv_le₀ h2κ h2
  -- `ℓ̃` and `A`
  obtain ⟨ℓt, hℓt⟩ : ∃ ℓt : ℝ,
      ℓt = ℓ ^ (M / (M + 4)) * (p.1.2 : ℝ) ^ (((d : ℝ) + 4) / (M + 4)) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ,
      A = (ℓ ^ (M / (M + 4)) / (p.1.2 : ℝ) ^ ((M - d) / (M + 4))) ^ 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ sq_nonneg _
  obtain ⟨hℓt2, hδA⟩ := expAlg ℓ (p.1.2 : ℝ) M d hℓ0 hL0 hM4
  rw [← hℓt, ← hA] at hℓt2 hδA
  have hℓℓt : ℓ ≤ ℓt := hℓt ▸ le_ellt ℓ (p.1.2 : ℝ) M d hℓ0 hℓL' hL1 hM4
  have hℓt0 : 0 < ℓt := by linarith
  have hR : η₀ * (ℓt ^ 2 * (p.1.1 : ℝ) ^ (-2 : ℝ)) = (p.1.2 : ℝ) ^ ε * A := by
    rw [hη₀, hℓt2, Real.rpow_neg hW0.le, Real.rpow_two, Real.rpow_sub hL0, Real.rpow_two]
    field_simp
  have hR1 : 1 ≤ ℓt ^ 2 * (p.1.1 : ℝ) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hW0.le, Real.rpow_two, ← div_eq_mul_inv, one_le_div (by positivity)]
    exact pow_le_pow_left₀ hW0.le (hWℓ.trans hℓℓt) 2
  have hηX : η₀ ≤ (p.1.2 : ℝ) ^ ε * A := by
    rw [← hR]; nlinarith
  -- the deterministic bound on the event where every entry obeys the local law at `η₀`
  have hdet : ∀ ω : Sample (Zd d p.1.2), ∀ (u : Zd d p.1.2 → Zd d p.1.2 → ℂ)
      (lam : Zd d p.1.2 → ℝ), IsOrthoEigenbasis (hmat ω) u lam →
      (∀ x y : Zd d p.1.2, ∀ E ∈ Set.Ioo (-2 + κ) (2 - κ),
        ‖entryErr (green (hmat ω) ((E : ℂ) + (η₀ : ℂ) * I))
          (msc ((E : ℂ) + (η₀ : ℂ) * I)) x y‖ ^ 2 ≤
          (p.1.1 : ℝ) ^ τ' * bB d p.1.2 p.1.1 x y) →
      ((locSetBt d p.1.2 κ M K ℓ u lam).card : ℝ) / (p.1.2 : ℝ) ^ d ≤ (p.1.1 : ℝ) ^ τ * A := by
    intro ω u lam hu hgood
    have h := cardBound d p.1.2 p.1.1 hd (by exact_mod_cast hW1) (hmat ω) (hmat_isHermitian ω)
      u lam hu κ η₀ τ' ℓ ℓt M K hκ hη₀pos hη₀κ hτ'1 hℓ0 hℓt0 (by linarith) (by linarith)
      hgood
    rw [mul_assoc K, hδA] at h
    rw [div_le_iff₀ (by positivity), mul_comm _ ((p.1.2 : ℝ) ^ d)]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hsplit : η₀ * (4 + (p.1.1 : ℝ) ^ τ' * (2 * d * 3 ^ (d - 1) * ℓt ^ 2 *
        (p.1.1 : ℝ) ^ (-2 : ℝ))) =
        4 * η₀ + C * ((p.1.1 : ℝ) ^ τ' * (η₀ * (ℓt ^ 2 * (p.1.1 : ℝ) ^ (-2 : ℝ)))) := by
      rw [hC]; ring
    rw [hsplit, hR]
    have hX0 : 0 ≤ (p.1.2 : ℝ) ^ ε * A := by positivity
    have hYA : (p.1.1 : ℝ) ^ τ' * ((p.1.2 : ℝ) ^ ε * A) ≤ (p.1.1 : ℝ) ^ (τ / 2) * A := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hY hA0
    have hXY : (p.1.2 : ℝ) ^ ε * A ≤ (p.1.1 : ℝ) ^ τ' * ((p.1.2 : ℝ) ^ ε * A) :=
      le_mul_of_one_le_left hX0 hWτ'1
    have hKA : 100 * (K * A) ≤ 100 * K * ((p.1.1 : ℝ) ^ (τ / 2) * A) := by
      have : A ≤ (p.1.1 : ℝ) ^ (τ / 2) * A := le_mul_of_one_le_left hA0 hW2τ1
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hη2 : η₀ ≤ (p.1.1 : ℝ) ^ (τ / 2) * A := hηX.trans (hXY.trans hYA)
    have hCY : C * ((p.1.1 : ℝ) ^ τ' * ((p.1.2 : ℝ) ^ ε * A)) ≤
        C * ((p.1.1 : ℝ) ^ (τ / 2) * A) := mul_le_mul_of_nonneg_left hYA hC0
    calc 100 * (K * A) + 16 * (4 * η₀ + C * ((p.1.1 : ℝ) ^ τ' * ((p.1.2 : ℝ) ^ ε * A)))
        ≤ 100 * K * ((p.1.1 : ℝ) ^ (τ / 2) * A) +
          16 * (4 * ((p.1.1 : ℝ) ^ (τ / 2) * A) + C * ((p.1.1 : ℝ) ^ (τ / 2) * A)) := by
          linarith
      _ = Q * ((p.1.1 : ℝ) ^ (τ / 2) * A) := by rw [hQ]; ring
      _ ≤ (p.1.1 : ℝ) ^ (τ / 2) * ((p.1.1 : ℝ) ^ (τ / 2) * A) :=
          mul_le_mul_of_nonneg_right hQW (by positivity)
      _ = (p.1.1 : ℝ) ^ τ * A := by rw [← mul_assoc, hhalf2]
  refine (measure_mono (μ := rbmLaw d P p) (?_ : _ ⊆ ⋃ q : Zd d p.1.2 × Zd d p.1.2,
      {ω | ∃ E : ℝ, E ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ η : ℝ,
        (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) ≤ η ∧ η ≤ 1 ∧
        (p.1.1 : ℝ) ^ τ' * bB d p.1.2 p.1.1 q.1 q.2 <
          ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * I))
            (msc ((E : ℂ) + (η : ℂ) * I)) q.1 q.2‖ ^ 2})).trans ?_
  · rintro ω ⟨u, lam, hu, hlt⟩
    by_contra hnot
    have hgood : ∀ x y : Zd d p.1.2, ∀ E ∈ Set.Ioo (-2 + κ) (2 - κ),
        ‖entryErr (green (hmat ω) ((E : ℂ) + (η₀ : ℂ) * I))
          (msc ((E : ℂ) + (η₀ : ℂ) * I)) x y‖ ^ 2 ≤
          (p.1.1 : ℝ) ^ τ' * bB d p.1.2 p.1.1 x y := by
      intro x y E hE
      by_contra hc
      exact hnot (Set.mem_iUnion.mpr ⟨(x, y), E, hE, η₀, hη₀.ge, hη₀1, not_le.mp hc⟩)
    have hb := hdet ω u lam hu hgood
    rw [← hA, mul_add] at hlt
    have hpos : 0 < (p.1.1 : ℝ) ^ τ * (p.1.1 : ℝ) ^ (-(d : ℝ) / 2) := by positivity
    linarith
  · refine (measure_iUnion_fintype_le _ _).trans ?_
    calc _ ≤ ∑ q : Zd d p.1.2 × Zd d p.1.2,
          ENNReal.ofReal ((p.1.2 : ℝ) ^ (-(D + 2 * d))) :=
          Finset.sum_le_sum fun q _ => hL₁ p ((le_max_left _ _).trans hL₀) hadm q.1 q.2
      _ = ENNReal.ofReal (((p.1.2 ^ d * p.1.2 ^ d : ℕ) : ℝ) *
            (p.1.2 : ℝ) ^ (-(D + 2 * d))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, card_Zd, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D)) := by
          congr 1
          rw [Nat.cast_mul, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_add hL0,
            ← Real.rpow_add hL0]
          congr 1; ring

/-- (1.12) from the local law. -/
theorem thm13_eq112_ofLocalLaw : LocalLawStmt → Thm13_eq112Stmt := by
  intro hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ γ K hγ hγ1 hK τ D hτ hD
  have hcτ : 0 < c₁ * τ := mul_pos hc₁ hτ
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (⌈4 * ((d : ℝ) + 4) / (c₁ * τ)⌉₊ : ℝ) + 1 := ⟨_, rfl⟩
  have hceil : 4 * ((d : ℝ) + 4) / (c₁ * τ) ≤ ⌈4 * ((d : ℝ) + 4) / (c₁ * τ)⌉₊ := Nat.le_ceil _
  have hceil1 : (1 : ℝ) ≤ ⌈4 * ((d : ℝ) + 4) / (c₁ * τ)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr (by positivity)
  have hM1 : 1 < M := by rw [hMdef]; linarith
  have hM4 : 0 < M + 4 := by linarith
  have hMc : 2 * (d : ℝ) + 8 ≤ c₁ * (τ / 2) * (M + 4) := by
    have h1 : 4 * ((d : ℝ) + 4) ≤ c₁ * τ * M := by
      rw [div_le_iff₀ hcτ] at hceil
      rw [hMdef]; nlinarith
    nlinarith
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = (2 : ℝ) ^ M * (1 + (⌈M / γ⌉₊).factorial) * K := ⟨_, rfl⟩
  have hK' : 1 < K' := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ M := Real.one_le_rpow (by norm_num) (by linarith)
    have hf : (1 : ℝ) ≤ (⌈M / γ⌉₊).factorial := Nat.one_le_cast.mpr (Nat.factorial_pos _)
    rw [hK'def]
    have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ M * (1 + (⌈M / γ⌉₊).factorial) := by nlinarith
    nlinarith
  obtain ⟨L₀, hL₀⟩ := lemma81_ofLocalLaw hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ M K' hM1 hK' (τ / 2) D
    (by positivity) hD
  refine ⟨L₀, fun p ℓ hL hWℓ hℓL hLW hWL =>
    (measure_mono fun ω hω => ?_).trans (hL₀ p ℓ hL hWℓ hℓL hLW hWL)⟩
  obtain ⟨u, lam, hu, hlt⟩ := hω
  refine ⟨u, lam, hu, ?_⟩
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.2
  have hL0 : (0 : ℝ) < (p.1.2 : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ (p.1.1 : ℝ) := (Real.one_le_rpow hL1 hc₁.le).trans hLW
  have hW0 : (0 : ℝ) < (p.1.1 : ℝ) := by linarith
  have hℓ1 : (1 : ℝ) ≤ ℓ := hW1.trans hWℓ
  have hcard : ((locSetB d p.1.2 κ γ K ℓ u lam).card : ℝ) ≤
      (locSetBt d p.1.2 κ M K' ℓ u lam).card := by
    rw [hK'def]
    exact_mod_cast Finset.card_le_card
      (bsubBt d p.1.2 u lam κ γ K ℓ M hγ (by linarith) (by linarith))
  have hA := A_le ℓ (p.1.2 : ℝ) M (c₁ * (τ / 2)) d hℓ1 hL1 hM4 hMc
  have hLW2 : (p.1.2 : ℝ) ^ (c₁ * (τ / 2)) ≤ (p.1.1 : ℝ) ^ (τ / 2) := by
    rw [Real.rpow_mul hL0.le]
    exact Real.rpow_le_rpow (by positivity) hLW (by positivity)
  have hhalf2 : (p.1.1 : ℝ) ^ (τ / 2) * (p.1.1 : ℝ) ^ (τ / 2) = (p.1.1 : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hWτ : (p.1.1 : ℝ) ^ (τ / 2) ≤ (p.1.1 : ℝ) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hq0 : 0 ≤ ℓ ^ 2 / (p.1.2 : ℝ) ^ 2 := by positivity
  have hA' : (ℓ ^ (M / (M + 4)) / (p.1.2 : ℝ) ^ ((M - d) / (M + 4))) ^ 2 ≤
      (p.1.1 : ℝ) ^ (τ / 2) * (ℓ ^ 2 / (p.1.2 : ℝ) ^ 2) :=
    hA.trans (mul_le_mul_of_nonneg_right hLW2 hq0)
  have hWd : 0 ≤ (p.1.1 : ℝ) ^ (-(d : ℝ) / 2) := by positivity
  have hWh : 0 ≤ (p.1.1 : ℝ) ^ (τ / 2) := by positivity
  have key : (p.1.1 : ℝ) ^ (τ / 2) *
      ((ℓ ^ (M / (M + 4)) / (p.1.2 : ℝ) ^ ((M - d) / (M + 4))) ^ 2 +
        (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)) ≤
      (p.1.1 : ℝ) ^ τ * (ℓ ^ 2 / (p.1.2 : ℝ) ^ 2 + (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)) := by
    rw [mul_add, mul_add]
    refine add_le_add ?_ (mul_le_mul_of_nonneg_right hWτ hWd)
    rw [← hhalf2, mul_assoc]
    exact mul_le_mul_of_nonneg_left hA' hWh
  exact key.trans_lt (hlt.trans_le (div_le_div_of_nonneg_right hcard (by positivity)))

section Witness

open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

end RBM8D
