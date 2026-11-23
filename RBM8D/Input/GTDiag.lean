module

public import RBM8D.Prob.Model
public import RBM8D.Prob.StochDom
public import RBM8D.Prob.Partial
public import RBM8D.Basic.Minor
public import RBM8D.Basic.Domain
public import RBM8D.Basic.Semicircle
public import RBM8D.Profile.Basic
public import RBM8D.Input.GT

@[expose] public section

/-!
# The diagonal input estimate [I, (5.3)] and the local law at `η = 1`

[I, (5.3)] = [II, (7.3)] for any family of spectral parameters in `𝐃(κ, ε)`, and [II, (8.51)]
at `η = 1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

/-! ## Four good events -/

/-- `ξ ≺ ζ` from four relations `ξ_k ≺ ζ_k`, if for each `τ > 0` there is `τ' > 0` such that,
eventually, the four bounds `ξ_k ≤ size^{τ'} ζ_k` for all indices imply `ξ ≤ size^τ ζ` for all
indices. -/
private theorem gtDiag_of_four {Par : Type*} {Ω : Par → Type*} [∀ p, MeasurableSpace (Ω p)]
    {U U₁ U₂ U₃ U₄ : Par → Type*} (F : Filter Par) (size : Par → ℝ) (P : ∀ p, Measure (Ω p))
    (hsize : Tendsto size F atTop) (ξ ζ : ∀ p, U p → Ω p → ℝ)
    (ξ₁ ζ₁ : ∀ p, U₁ p → Ω p → ℝ) (ξ₂ ζ₂ : ∀ p, U₂ p → Ω p → ℝ)
    (ξ₃ ζ₃ : ∀ p, U₃ p → Ω p → ℝ) (ξ₄ ζ₄ : ∀ p, U₄ p → Ω p → ℝ)
    (h₁ : StochDom F size P ξ₁ ζ₁) (h₂ : StochDom F size P ξ₂ ζ₂)
    (h₃ : StochDom F size P ξ₃ ζ₃) (h₄ : StochDom F size P ξ₄ ζ₄)
    (hdet : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ p in F, ∀ ω,
      (∀ u, ξ₁ p u ω ≤ size p ^ τ' * ζ₁ p u ω) → (∀ u, ξ₂ p u ω ≤ size p ^ τ' * ζ₂ p u ω) →
      (∀ u, ξ₃ p u ω ≤ size p ^ τ' * ζ₃ p u ω) → (∀ u, ξ₄ p u ω ≤ size p ^ τ' * ζ₄ p u ω) →
        ∀ u, ξ p u ω ≤ size p ^ τ * ζ p u ω) :
    StochDom F size P ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hd⟩ := hdet τ hτ
  filter_upwards [hd, h₁ τ' hτ' (D + 1) (by linarith), h₂ τ' hτ' (D + 1) (by linarith),
    h₃ τ' hτ' (D + 1) (by linarith), h₄ τ' hτ' (D + 1) (by linarith),
    hsize.eventually (eventually_ge_atTop 4)] with p hp hp₁ hp₂ hp₃ hp₄ h4
  have hsub : {ω | ∃ u, size p ^ τ * ζ p u ω < ξ p u ω} ⊆
      {ω | ∃ u, size p ^ τ' * ζ₁ p u ω < ξ₁ p u ω} ∪ {ω | ∃ u, size p ^ τ' * ζ₂ p u ω < ξ₂ p u ω} ∪
      {ω | ∃ u, size p ^ τ' * ζ₃ p u ω < ξ₃ p u ω} ∪
      {ω | ∃ u, size p ^ τ' * ζ₄ p u ω < ξ₄ p u ω} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hc
    obtain ⟨u, hu⟩ := hω
    exact absurd (hp ω hc.1.1.1 hc.1.1.2 hc.1.2 hc.2 u) (not_le.2 hu)
  have hs : 0 < size p := by linarith
  have hw0 : 0 ≤ size p ^ (-(D + 1)) := (Real.rpow_pos_of_pos hs _).le
  have hexp : size p ^ (-(D + 1)) = size p ^ (-D) * (size p)⁻¹ := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hs, Real.rpow_neg_one]
  have hinv : (size p)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h4
  have hle : size p ^ (-(D + 1)) + size p ^ (-(D + 1)) + size p ^ (-(D + 1)) +
      size p ^ (-(D + 1)) ≤ size p ^ (-D) := by
    have h0 : 0 ≤ size p ^ (-D) := (Real.rpow_pos_of_pos hs _).le
    rw [hexp]; nlinarith
  calc P p {ω | ∃ u, size p ^ τ * ζ p u ω < ξ p u ω}
      ≤ P p ({ω | ∃ u, size p ^ τ' * ζ₁ p u ω < ξ₁ p u ω} ∪
          {ω | ∃ u, size p ^ τ' * ζ₂ p u ω < ξ₂ p u ω} ∪
          {ω | ∃ u, size p ^ τ' * ζ₃ p u ω < ξ₃ p u ω} ∪
          {ω | ∃ u, size p ^ τ' * ζ₄ p u ω < ξ₄ p u ω}) := measure_mono hsub
    _ ≤ P p {ω | ∃ u, size p ^ τ' * ζ₁ p u ω < ξ₁ p u ω} +
          P p {ω | ∃ u, size p ^ τ' * ζ₂ p u ω < ξ₂ p u ω} +
          P p {ω | ∃ u, size p ^ τ' * ζ₃ p u ω < ξ₃ p u ω} +
          P p {ω | ∃ u, size p ^ τ' * ζ₄ p u ω < ξ₄ p u ω} := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (size p ^ (-(D + 1))) + ENNReal.ofReal (size p ^ (-(D + 1))) +
          ENNReal.ofReal (size p ^ (-(D + 1))) + ENNReal.ofReal (size p ^ (-(D + 1))) := by
        gcongr
    _ = ENNReal.ofReal (size p ^ (-(D + 1)) + size p ^ (-(D + 1)) + size p ^ (-(D + 1)) +
          size p ^ (-(D + 1))) := by
        rw [ENNReal.ofReal_add (by positivity) hw0, ENNReal.ofReal_add (by positivity) hw0,
          ENNReal.ofReal_add hw0 hw0]
    _ ≤ ENNReal.ofReal (size p ^ (-D)) := ENNReal.ofReal_le_ofReal hle

/-! ## Lipschitz bounds in the spectral parameter -/

/-- `|G_{ij}(z) − G_{ij}(w)| ≤ |z − w| / (Im z · Im w)`, from the resolvent identity and the Ward
identity. -/
private theorem gtDiag_green_lip {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (i j : ι) :
    ‖green H z i j - green H w i j‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) (green_sub_green hH hz.ne' hw.ne')
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
  rw [h, norm_mul]
  have hrow := sum_norm_sq_green_row hH hz i
  have hcol := sum_norm_sq_green_col hH hw j
  have hgi : (green H z i i).im ≤ (z.im)⁻¹ := by
    have := norm_green_entry_le hH hz.ne' i i
    rw [abs_of_pos hz] at this
    exact (Complex.im_le_norm _).trans this
  have hgj : (green H w j j).im ≤ (w.im)⁻¹ := by
    have := norm_green_entry_le hH hw.ne' j j
    rw [abs_of_pos hw] at this
    exact (Complex.im_le_norm _).trans this
  have hA : ∑ k, ‖green H z i k‖ ^ 2 ≤ (z.im)⁻¹ ^ 2 := by
    rw [hrow, div_eq_mul_inv, sq]
    exact mul_le_mul_of_nonneg_right hgi (inv_nonneg.2 hz.le)
  have hB : ∑ k, ‖green H w k j‖ ^ 2 ≤ (w.im)⁻¹ ^ 2 := by
    rw [hcol, div_eq_mul_inv, sq]
    exact mul_le_mul_of_nonneg_right hgj (inv_nonneg.2 hw.le)
  have hsum : ‖∑ k, green H z i k * green H w k j‖ ≤ (z.im)⁻¹ * (w.im)⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    simp_rw [norm_mul]
    refine le_of_sq_le_sq ?_ (by positivity)
    calc (∑ k, ‖green H z i k‖ * ‖green H w k j‖) ^ 2
        ≤ (∑ k, ‖green H z i k‖ ^ 2) * ∑ k, ‖green H w k j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (z.im)⁻¹ ^ 2 * (w.im)⁻¹ ^ 2 :=
          mul_le_mul hA hB (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
      _ = ((z.im)⁻¹ * (w.im)⁻¹) ^ 2 := by ring
  calc ‖z - w‖ * ‖∑ k, green H z i k * green H w k j‖
      ≤ ‖z - w‖ * ((z.im)⁻¹ * (w.im)⁻¹) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖z - w‖ / (z.im * w.im) := by field_simp

/-- `1 − |m(z)| ≥ Im z / 4` for `0 < Im z ≤ 1`. -/
private theorem gtDiag_one_sub_norm_msc {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    z.im / 4 ≤ 1 - ‖msc z‖ := by
  have him := msc_im_pos hz
  have hlt := norm_msc_lt_one hz
  have hm0 : msc z ≠ 0 := msc_ne_zero z
  have hinv : msc z + z = -(msc z)⁻¹ := msc_add_eq_neg_inv z
  have hN : 0 < Complex.normSq (msc z) := Complex.normSq_pos.mpr hm0
  have key : ((msc z).im + z.im) * Complex.normSq (msc z) = (msc z).im := by
    have := congrArg Complex.im hinv
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at this
    rw [this]
    field_simp
  rw [Complex.normSq_eq_norm_sq] at key
  have hle : (msc z).im ≤ ‖msc z‖ := Complex.im_le_norm _
  have hn0 := norm_nonneg (msc z)
  nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (sub_nonneg.2 hlt.le)]

/-- `|m(z) − m(w)| ≤ 4 |z − w| / Im z` for `0 < Im z ≤ 1` and `Im w > 0`. -/
private theorem gtDiag_msc_lip {z w : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hw : 0 < w.im) :
    ‖msc z - msc w‖ ≤ 4 * ‖z - w‖ / z.im := by
  have hm := msc_mul z
  have hm' := msc_mul w
  have key : (msc z - msc w) * (1 - msc z * msc w) = (z - w) * (msc z * msc w) := by
    linear_combination (-msc w) * hm + msc z * hm'
  have h1 := gtDiag_one_sub_norm_msc hz hz1
  have hl := norm_msc_lt_one hz
  have hl' := norm_msc_lt_one hw
  have hn0 := norm_nonneg (msc z)
  have hn0' := norm_nonneg (msc w)
  have hlow : z.im / 4 ≤ ‖1 - msc z * msc w‖ := by
    have : 1 - ‖msc z * msc w‖ ≤ ‖1 - msc z * msc w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (msc z * msc w)
      simpa using this
    rw [norm_mul] at this
    nlinarith
  have hn := congrArg norm key
  rw [norm_mul, norm_mul, norm_mul] at hn
  have hprod : ‖msc z‖ * ‖msc w‖ ≤ 1 := by nlinarith
  have hzw := norm_nonneg (z - w)
  have hle : ‖msc z - msc w‖ * (z.im / 4) ≤ ‖z - w‖ := by
    calc ‖msc z - msc w‖ * (z.im / 4) ≤ ‖msc z - msc w‖ * ‖1 - msc z * msc w‖ :=
          mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = ‖z - w‖ * (‖msc z‖ * ‖msc w‖) := hn
      _ ≤ ‖z - w‖ * 1 := mul_le_mul_of_nonneg_left hprod hzw
      _ = ‖z - w‖ := mul_one _
  rw [le_div_iff₀ hz]
  nlinarith

/-! ## Deterministic steps -/

/-- `|(G' − m')_{xy}| ≤ |(G − m)_{xy}| + |G'_{xy} − G_{xy}| + |m' − m|`. -/
private theorem gtDiag_entryErr_le {ι : Type*} [DecidableEq ι] (G G' : Matrix ι ι ℂ)
    (m m' : ℂ) (x y : ι) :
    ‖entryErr G' m' x y‖ ≤ ‖entryErr G m x y‖ + (‖G' x y - G x y‖ + ‖m' - m‖) := by
  unfold entryErr
  split_ifs
  · calc ‖G' x y - m'‖ = ‖(G x y - m) + (G' x y - G x y) - (m' - m)‖ := by ring_nf
      _ ≤ ‖(G x y - m) + (G' x y - G x y)‖ + ‖m' - m‖ := norm_sub_le _ _
      _ ≤ ‖G x y - m‖ + ‖G' x y - G x y‖ + ‖m' - m‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by ring
  · simp only [sub_zero]
    calc ‖G' x y‖ = ‖G x y + (G' x y - G x y)‖ := by ring_nf
      _ ≤ ‖G x y‖ + ‖G' x y - G x y‖ := norm_add_le _ _
      _ ≤ _ := by have := norm_nonneg (m' - m); linarith

/-- The deterministic step of [I, (5.3)] at a nearby parameter: if `|G_{ij}(z') − G_{ij}(z)| +
|m(z') − m(z)| ≤ e`, `‖G(z) − m(z)‖_max ≤ δ`, and the hypotheses of `diagDet` hold at `z'` with
`δ + e` and `Λ ≥ 2Λ₀ + 2e²`, where `Σ_k s_{ik} |G_{kj}(z)|² ≤ Λ₀`, then
`|G_{ii}(z) − m(z)| ≤ 100 K Φ Λ^{1/2} + e`. -/
private theorem gtDiag_core {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (S : Matrix ι ι ℝ) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ i, ∑ k, S i k = 1) (hS2 : ∀ k, ∑ i, S i k ≤ 1) (z z' : ℂ) (hz' : 0 < z'.im)
    (hz'3 : ‖z'‖ ≤ 3) (e δ Φ Λ₀ Λ K : ℝ)
    (he : ∀ i j, ‖green H z' i j - green H z i j‖ + ‖msc z' - msc z‖ ≤ e)
    (hA : GoodEvent (green H z) (msc z) δ) (hδ : δ + e ≤ 1 / 8) (hK : 0 ≤ K)
    (hKδ : K * (δ + e) ≤ 1 / 2) (hΦ : 1 ≤ Φ) (hQ : LDEQuad H (green H z') S Φ)
    (hD : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) (hT : ∀ i j, ∑ k, S i k * ‖green H z k j‖ ^ 2 ≤ Λ₀)
    (hΛ : 2 * Λ₀ + 2 * e ^ 2 ≤ Λ) (hSΛ : ∀ i j, S i j ≤ Λ) (hst : Stable S (msc z' ^ 2) K)
    (i : ι) : ‖green H z i i - msc z‖ ≤ 100 * K * Φ * Real.sqrt Λ + e := by
  have hm4 : 1 / 4 ≤ ‖msc z'‖ := norm_msc_ge_quarter z' hz' hz'3
  have hm1 : ‖msc z'‖ ≤ 1 := (norm_msc_lt_one hz').le
  have hG : GoodEvent (green H z') (msc z') (δ + e) := by
    intro x y
    have h1 := gtDiag_entryErr_le (green H z) (green H z') (msc z) (msc z') x y
    have h2 := hA x y
    have h3 := he x y
    linarith
  have hdG : ∀ k j, ‖green H z' k j - green H z k j‖ ≤ e := fun k j =>
    le_trans (le_add_of_nonneg_right (norm_nonneg _)) (he k j)
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hdG i i)
  have hΛ' : ∀ i j, ∑ k, S i k * ‖green H z' k j‖ ^ 2 ≤ Λ := by
    intro a j
    have hpt : ∀ k, S a k * ‖green H z' k j‖ ^ 2 ≤
        2 * (S a k * ‖green H z k j‖ ^ 2) + 2 * e ^ 2 * S a k := by
      intro k
      have hk : ‖green H z' k j‖ ≤ ‖green H z k j‖ + e := by
        have := norm_le_norm_add_norm_sub' (green H z' k j) (green H z k j)
        linarith [hdG k j]
      have hk2 : ‖green H z' k j‖ ^ 2 ≤ 2 * ‖green H z k j‖ ^ 2 + 2 * e ^ 2 := by
        have := norm_nonneg (green H z' k j)
        nlinarith [sq_nonneg (‖green H z k j‖ - e)]
      have := hS0 a k
      nlinarith
    calc ∑ k, S a k * ‖green H z' k j‖ ^ 2
        ≤ ∑ k, (2 * (S a k * ‖green H z k j‖ ^ 2) + 2 * e ^ 2 * S a k) :=
          Finset.sum_le_sum fun k _ => hpt k
      _ = 2 * ∑ k, S a k * ‖green H z k j‖ ^ 2 + 2 * e ^ 2 * ∑ k, S a k := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * Λ₀ + 2 * e ^ 2 := by rw [hS1 a, mul_one]; linarith [hT a j]
      _ ≤ Λ := hΛ
  have hdet := diagDet H z' (msc z') S (δ + e) Φ Λ K hH hz' (msc_mul z') hm4 hm1 hG
    (by linarith) (by linarith) hS0 hS1 hS2 hΦ hQ hD hΛ' hSΛ hst hK hKδ i
  have hsplit : green H z i i - msc z =
      (green H z' i i - msc z') - (green H z' i i - green H z i i) + (msc z' - msc z) := by ring
  rw [hsplit]
  calc ‖(green H z' i i - msc z') - (green H z' i i - green H z i i) + (msc z' - msc z)‖
      ≤ ‖green H z' i i - msc z'‖ + ‖green H z' i i - green H z i i‖ + ‖msc z' - msc z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 100 * K * Φ * Real.sqrt Λ + e := by linarith [he i i]

/-- The deterministic step of [II, (8.51)] at `η = 1` at a nearby parameter: if
`|G_{ij}(z') − G_{ij}(z)| + |m(z') − m(z)| ≤ e` and the hypotheses of `eta1Det` hold at `z'`, then
`|G_{ij}(z) − δ_{ij} m(z)| ≤ 18 (Φ σ)^{1/2} + e`. -/
private theorem gtDiag_eta1_core {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (S : Matrix ι ι ℝ) (σ Φ e : ℝ) (z z' : ℂ) (hz'1 : z'.im = 1)
    (hz'2 : |z'.re| ≤ 2) (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k = 1)
    (hSσ : ∀ i k, S i k ≤ σ) (hΦ : 1 ≤ Φ) (hΦσ : Φ * σ ≤ 1) (hR : LDERow H (green H z') S Φ)
    (hQ : LDEQuad H (green H z') S Φ) (hD : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i)
    (he : ∀ i j, ‖green H z' i j - green H z i j‖ + ‖msc z' - msc z‖ ≤ e) (i j : ι) :
    ‖entryErr (green H z) (msc z) i j‖ ≤ 18 * Real.sqrt (Φ * σ) + e := by
  have h1 := eta1Det H z' S σ Φ hH hz'1 hz'2 hS0 hS1 hSσ hΦ hΦσ hR hQ hD i j
  have h2 := gtDiag_entryErr_le (green H z') (green H z) (msc z') (msc z) i j
  rw [norm_sub_rev (green H z i j), norm_sub_rev (msc z)] at h2
  linarith [he i j]

/-! ## Nets and exponents -/

/-- `h ⌊x/h⌋ ≤ x < h ⌊x/h⌋ + h` for `h > 0`. -/
private theorem gtDiag_floor {h : ℝ} (hh : 0 < h) (x : ℝ) :
    h * ⌊x / h⌋ ≤ x ∧ x - h < h * ⌊x / h⌋ := by
  have h1 := Int.floor_le (x / h)
  have h2 := Int.lt_floor_add_one (x / h)
  have hx : h * (x / h) = x := by field_simp
  constructor
  · calc h * ⌊x / h⌋ ≤ h * (x / h) := mul_le_mul_of_nonneg_left h1 hh.le
      _ = x := hx
  · have : h * (x / h) < h * (⌊x / h⌋ + 1) := mul_lt_mul_of_pos_left h2 hh
    linarith

/-- `(W^{−d/2})² = W^{−d}`. -/
private theorem gtDiag_sq_rpow {W : ℝ} (hW : 0 < W) (d : ℝ) : (W ^ (-d / 2)) ^ 2 = (W ^ d)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le, ← Real.rpow_neg hW.le]
  congr 1
  push_cast
  ring

/-- `W^{−(2a + d + 1)} = (W^{−a})² W^{−1} W^{−d}`. -/
private theorem gtDiag_h_eq {W : ℝ} (hW : 0 < W) (a d : ℝ) :
    (W ^ (2 * a + d + 1))⁻¹ = ((W ^ a)⁻¹) ^ 2 * W⁻¹ * (W ^ d)⁻¹ := by
  rw [show 2 * a + d + 1 = a + a + d + 1 by ring, Real.rpow_add hW, Real.rpow_add hW,
    Real.rpow_add hW, Real.rpow_one]
  have h1 : W ^ a ≠ 0 := (Real.rpow_pos_of_pos hW a).ne'
  have h2 : W ^ d ≠ 0 := (Real.rpow_pos_of_pos hW d).ne'
  field_simp

/-- For `α < β`, eventually `C W^α ≤ W^β` as `W → ∞`. -/
private theorem gtDiag_rpow_ev (C α β : ℝ) (h : α < β) :
    ∀ᶠ W : ℝ in atTop, C * W ^ α ≤ W ^ β := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.2 h)).eventually (eventually_ge_atTop C),
    eventually_gt_atTop 0] with W h1 h0
  have hα : 0 < W ^ α := Real.rpow_pos_of_pos h0 α
  have : W ^ β = W ^ (β - α) * W ^ α := by rw [← Real.rpow_add h0]; congr 1; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right h1 hα.le

/-- Eventually along `admFilterL c₀ c₁`, `(W, L) ∈ adm(c₀, c₁)`. -/
private theorem gtDiag_eventually_adm (c₀ c₁ : ℝ) :
    ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ := by
  have h : ∀ᶠ q in admFilter c₀ c₁, q ∈ adm c₀ c₁ :=
    inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _)
  exact tendsto_comap.eventually h

/-- On `adm(c₀, c₁)` with `W ≥ 1`: `W²/L^{2−ε} ≥ W^{−|2−ε|/c₁}`, so every `z ∈ 𝐃(κ, ε)` has
`Im z ≥ W^{−|2−ε|/c₁}`. -/
private theorem gtDiag_eta_lower {c₀ c₁ : ℝ} (ε : ℝ) (hc₁ : 0 < c₁) (p : SizeL)
    (hp : p.1 ∈ adm c₀ c₁) (hW : 1 ≤ sizeW p) :
    (sizeW p ^ (|2 - ε| / c₁))⁻¹ ≤ (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) := by
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  have hW1 : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW
  have hLpos : 0 < (p.1.2 : ℝ) ^ (2 - ε) := Real.rpow_pos_of_pos (by linarith) _
  have hcpos : 0 < (p.1.2 : ℝ) ^ c₁ := Real.rpow_pos_of_pos (by linarith) _
  have h1 : (p.1.2 : ℝ) ^ (2 - ε) ≤ (p.1.2 : ℝ) ^ |2 - ε| :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self _)
  have h2 : (p.1.2 : ℝ) ^ |2 - ε| ≤ sizeW p ^ (|2 - ε| / c₁) := by
    calc (p.1.2 : ℝ) ^ |2 - ε| = ((p.1.2 : ℝ) ^ c₁) ^ (|2 - ε| / c₁) := by
          rw [← Real.rpow_mul (by linarith), mul_div_cancel₀ _ hc₁.ne']
      _ ≤ sizeW p ^ (|2 - ε| / c₁) :=
          Real.rpow_le_rpow hcpos.le hp.1 (div_nonneg (abs_nonneg _) hc₁.le)
  have hW2 : (1 : ℝ) ≤ (p.1.1 : ℝ) ^ 2 := one_le_pow₀ hW1
  rw [le_div_iff₀ hLpos]
  have hpos : 0 < sizeW p ^ (|2 - ε| / c₁) := Real.rpow_pos_of_pos (by linarith) _
  calc (sizeW p ^ (|2 - ε| / c₁))⁻¹ * (p.1.2 : ℝ) ^ (2 - ε)
      ≤ (sizeW p ^ (|2 - ε| / c₁))⁻¹ * sizeW p ^ (|2 - ε| / c₁) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.2 hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'
    _ ≤ (p.1.1 : ℝ) ^ 2 := hW2

/-- The number of net points per axis, `M = ⌈3 W^c⌉`. -/
private def gtDiag_M (c : ℝ) (p : SizeL) : ℕ := ⌈3 * sizeW p ^ c⌉₊

/-- The index set `{−M, …, M} × {1, …, M}` of the net in `z`. -/
private abbrev gtDiag_netZ (c : ℝ) (p : SizeL) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(gtDiag_M c p : ℤ)) (gtDiag_M c p) ×ˢ Finset.Icc (1 : ℤ) (gtDiag_M c p)

/-- The net point `W^{−c} (n₁ + i n₂)`. -/
private def gtDiag_zN (c : ℝ) (p : SizeL) (n : gtDiag_netZ c p) : ℂ :=
  (((sizeW p ^ c)⁻¹ * n.1.1 : ℝ) : ℂ) + (((sizeW p ^ c)⁻¹ * n.1.2 : ℝ) : ℂ) * I

/-- The index set `{−M, …, M}` of the net in `E`. -/
private abbrev gtDiag_netE (c : ℝ) (p : SizeL) : Finset ℤ :=
  Finset.Icc (-(gtDiag_M c p : ℤ)) (gtDiag_M c p)

/-- The net point `W^{−c} n + i`. -/
private def gtDiag_zE (c : ℝ) (p : SizeL) (n : gtDiag_netE c p) : ℂ :=
  (((sizeW p ^ c)⁻¹ * n.1 : ℝ) : ℂ) + I

private theorem gtDiag_card_Icc (M : ℕ) : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
  rw [Int.card_Icc]; omega

private theorem gtDiag_card_Icc_one (M : ℕ) : (Finset.Icc (1 : ℤ) M).card = M := by
  rw [Int.card_Icc]; omega

/-- `M ≤ 4 W^c` for `W ≥ 1`, `c ≥ 0`. -/
private theorem gtDiag_M_le (c : ℝ) (hc : 0 ≤ c) (p : SizeL) (hW : 1 ≤ sizeW p) :
    (gtDiag_M c p : ℝ) ≤ 4 * sizeW p ^ c := by
  have h1 : 1 ≤ sizeW p ^ c := Real.one_le_rpow hW hc
  have := Nat.ceil_lt_add_one (show 0 ≤ 3 * sizeW p ^ c by positivity)
  unfold gtDiag_M
  linarith

/-- The net in `z` has at most `W^{2c + 6}` points for `W ≥ 2`. -/
private theorem gtDiag_card_netZ (c : ℝ) (hc : 0 ≤ c) (p : SizeL) (hW : 2 ≤ sizeW p) :
    (Fintype.card (gtDiag_netZ c p) : ℝ) ≤ sizeW p ^ (2 * c + 6) := by
  have hW0 : 0 < sizeW p := by linarith
  have hM := gtDiag_M_le c hc p (by linarith)
  have h1 : 1 ≤ sizeW p ^ c := Real.one_le_rpow (by linarith) hc
  rw [Fintype.card_coe, Finset.card_product, gtDiag_card_Icc, gtDiag_card_Icc_one]
  push_cast
  have h6 : (64 : ℝ) ≤ sizeW p ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ sizeW p ^ 6 := pow_le_pow_left₀ (by norm_num) hW 6
  rw [show 2 * c + 6 = c + c + 6 by ring, Real.rpow_add hW0, Real.rpow_add hW0]
  have hM0 : (0 : ℝ) ≤ gtDiag_M c p := Nat.cast_nonneg _
  nlinarith [mul_le_mul h6 (le_refl (sizeW p ^ c * sizeW p ^ c)) (by positivity) (by positivity)]

/-- The net in `E` has at most `W^{c + 4}` points for `W ≥ 2`. -/
private theorem gtDiag_card_netE (c : ℝ) (hc : 0 ≤ c) (p : SizeL) (hW : 2 ≤ sizeW p) :
    (Fintype.card (gtDiag_netE c p) : ℝ) ≤ sizeW p ^ (c + 4) := by
  have hW0 : 0 < sizeW p := by linarith
  have hM := gtDiag_M_le c hc p (by linarith)
  have h1 : 1 ≤ sizeW p ^ c := Real.one_le_rpow (by linarith) hc
  rw [Fintype.card_coe, gtDiag_card_Icc]
  push_cast
  have h4 : (16 : ℝ) ≤ sizeW p ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ sizeW p ^ 4 := pow_le_pow_left₀ (by norm_num) hW 4
  rw [Real.rpow_add hW0]
  nlinarith [mul_le_mul h4 (le_refl (sizeW p ^ c)) (by positivity) (by positivity)]

/-- `W⁻¹ ≤ κ/4` for `W ≥ 4/κ`. -/
private theorem gtDiag_inv_le {W κ : ℝ} (hκ : 0 < κ) (hW : 4 / κ ≤ W) : W⁻¹ ≤ κ / 4 := by
  have h0 : 0 < 4 / κ := by positivity
  have hW0 : 0 < W := h0.trans_le hW
  rw [inv_eq_one_div, div_le_iff₀ hW0]
  have := (div_le_iff₀ hκ).1 hW
  linarith

/-- The rows of [I, (5.3)] with `τ' = min(τ, δ₀)/4`: eventually as `W → ∞`, `W ≥ 4`,
`W^{−1} ≤ κ/4`, `W^{τ'} W^{−δ₀} + 12 W^{−1} ≤ 1/(8(K + 1))` and
`(100 K B^{1/2} + 12) W^{2τ'} ≤ W^τ`. -/
private theorem gtDiag_rows (τ δ₀ K B κ : ℝ) (hτ : 0 < τ) (hδ₀ : 0 < δ₀) (hK : 0 ≤ K)
    (hκ : 0 < κ) :
    ∀ᶠ W : ℝ in atTop, 4 ≤ W ∧ W⁻¹ ≤ κ / 4 ∧
      W ^ (min τ δ₀ / 4) * W ^ (-δ₀) + 12 * W⁻¹ ≤ 1 / (8 * (K + 1)) ∧
      (100 * K * Real.sqrt B + 12) * (W ^ (min τ δ₀ / 4) * W ^ (min τ δ₀ / 4)) ≤ W ^ τ := by
  set t := min τ δ₀ / 4 with ht_def
  have hmin := lt_min hτ hδ₀
  have htτ : t ≤ τ / 4 := by have := min_le_left τ δ₀; linarith
  have htδ : t ≤ δ₀ / 4 := by have := min_le_right τ δ₀; linarith
  filter_upwards [gtDiag_rpow_ev (16 * (K + 1)) (t - δ₀) 0 (by linarith),
    gtDiag_rpow_ev (100 * K * Real.sqrt B + 12) (2 * t) τ (by linarith),
    eventually_ge_atTop (max 4 (max (4 / κ) (192 * (K + 1)))), eventually_gt_atTop 0]
    with W h1 h2 h3 h0
  have hW4 : 4 ≤ W := (le_max_left _ _).trans h3
  have hWκ : 4 / κ ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans h3
  have hWK : 192 * (K + 1) ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans h3
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨hW4, gtDiag_inv_le hκ hWκ, ?_, ?_⟩
  · rw [← Real.rpow_add h0, show t + -δ₀ = t - δ₀ by ring]
    rw [Real.rpow_zero] at h1
    have ha : W ^ (t - δ₀) ≤ 1 / (16 * (K + 1)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hb : 12 * W⁻¹ ≤ 1 / (16 * (K + 1)) := by
      rw [le_div_iff₀ (by positivity)]
      have : 12 * W⁻¹ * (16 * (K + 1)) = 192 * (K + 1) / W := by field_simp; ring
      rw [this, div_le_one h0]
      exact hWK
    calc W ^ (t - δ₀) + 12 * W⁻¹ ≤ 1 / (16 * (K + 1)) + 1 / (16 * (K + 1)) := add_le_add ha hb
      _ = 1 / (8 * (K + 1)) := by field_simp; ring
  · rw [← Real.rpow_add h0, show t + t = 2 * t by ring]
    exact h2

/-- The rows of [II, (8.51)] at `η = 1` with `τ' = min(τ, 1)/2`: eventually as `W → ∞`, `W ≥ 4`,
`W^{−1} ≤ κ/4`, `W^{τ'} C W^{−1} ≤ 1` and `(18 C^{1/2} + 5) W^{τ'} ≤ W^τ`. -/
private theorem gtDiag_rows_eta (τ C κ : ℝ) (hτ : 0 < τ) (hκ : 0 < κ) :
    ∀ᶠ W : ℝ in atTop, 4 ≤ W ∧ W⁻¹ ≤ κ / 4 ∧ W ^ (min τ 1 / 2) * (C * W⁻¹) ≤ 1 ∧
      (18 * Real.sqrt C + 5) * W ^ (min τ 1 / 2) ≤ W ^ τ := by
  set t := min τ 1 / 2 with ht_def
  have hmin := lt_min hτ one_pos
  have htτ : t ≤ τ / 2 := by have := min_le_left τ 1; linarith
  have ht1 : t ≤ 1 / 2 := by have := min_le_right τ 1; linarith
  filter_upwards [gtDiag_rpow_ev C (t - 1) 0 (by linarith),
    gtDiag_rpow_ev (18 * Real.sqrt C + 5) t τ (by linarith),
    eventually_ge_atTop (max 4 (4 / κ)), eventually_gt_atTop 0] with W h1 h2 h3 h0
  refine ⟨(le_max_left _ _).trans h3, gtDiag_inv_le hκ ((le_max_right _ _).trans h3), ?_, h2⟩
  rw [Real.rpow_zero] at h1
  have : W ^ t * (C * W⁻¹) = C * W ^ (t - 1) := by
    rw [sub_eq_add_neg, Real.rpow_add h0, Real.rpow_neg_one]; ring
  rw [this]; exact h1

private theorem gtDiag_zN_re (c : ℝ) (p : SizeL) (n : gtDiag_netZ c p) :
    (gtDiag_zN c p n).re = (sizeW p ^ c)⁻¹ * n.1.1 := by
  simp [gtDiag_zN]

private theorem gtDiag_zN_im (c : ℝ) (p : SizeL) (n : gtDiag_netZ c p) :
    (gtDiag_zN c p n).im = (sizeW p ^ c)⁻¹ * n.1.2 := by
  simp [gtDiag_zN]

private theorem gtDiag_zE_re (c : ℝ) (p : SizeL) (n : gtDiag_netE c p) :
    (gtDiag_zE c p n).re = (sizeW p ^ c)⁻¹ * n.1 := by
  simp [gtDiag_zE]

private theorem gtDiag_zE_im (c : ℝ) (p : SizeL) (n : gtDiag_netE c p) :
    (gtDiag_zE c p n).im = 1 := by
  simp [gtDiag_zE]

/-- `3 ≤ W^{−c} M`. -/
private theorem gtDiag_three_le (c : ℝ) (p : SizeL) (hW : 0 < sizeW p) :
    3 ≤ (sizeW p ^ c)⁻¹ * gtDiag_M c p := by
  have hpos : 0 < sizeW p ^ c := Real.rpow_pos_of_pos hW c
  have hM : 3 * sizeW p ^ c ≤ gtDiag_M c p := Nat.le_ceil _
  rw [← div_eq_inv_mul, le_div_iff₀ hpos]
  linarith

/-- An integer `n` with `|W^{−c} n| ≤ 3` lies in `{−M, …, M}`. -/
private theorem gtDiag_mem_Icc (c : ℝ) (p : SizeL) (hW : 0 < sizeW p) (n : ℤ)
    (hn : |(sizeW p ^ c)⁻¹ * n| ≤ 3) : n ∈ Finset.Icc (-(gtDiag_M c p : ℤ)) (gtDiag_M c p) := by
  have hpos : 0 < (sizeW p ^ c)⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos hW c)
  have h3 := gtDiag_three_le c p hW
  have hn' := abs_le.mp hn
  have h1 : (n : ℝ) ≤ (gtDiag_M c p : ℝ) := le_of_mul_le_mul_left (by linarith) hpos
  have h2 : (-(gtDiag_M c p : ℝ)) ≤ (n : ℝ) := by
    refine le_of_mul_le_mul_left ?_ hpos
    linarith
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast h2
  · exact_mod_cast h1

/-- Rounding `z ∈ 𝐃(κ, ε)` with `Im z ≥ ρ ≥ 2 W^{−c}` down to the net in `z`: the net point `z'`
has `|Re z'| < 2 − κ/2`, `Im z / 2 ≤ Im z' ≤ 1`, `|z'| ≤ 3` and `|z − z'| ≤ 2 W^{−c}`. -/
private theorem gtDiag_netZ_point (c : ℝ) (p : SizeL) (hW : 0 < sizeW p) {κ ρ : ℝ}
    (hhρ : 2 * (sizeW p ^ c)⁻¹ ≤ ρ) (hhκ : (sizeW p ^ c)⁻¹ ≤ κ / 2) (z : ℂ)
    (hre : |z.re| < 2 - κ) (hρ : ρ ≤ z.im)
    (hz1 : z.im ≤ 1) :
    ∃ n : gtDiag_netZ c p, |(gtDiag_zN c p n).re| < 2 - κ / 2 ∧ 0 < (gtDiag_zN c p n).im ∧
      (gtDiag_zN c p n).im ≤ 1 ∧ z.im / 2 ≤ (gtDiag_zN c p n).im ∧ ‖gtDiag_zN c p n‖ ≤ 3 ∧
      ‖z - gtDiag_zN c p n‖ ≤ 2 * (sizeW p ^ c)⁻¹ := by
  set h := (sizeW p ^ c)⁻¹ with h_def
  have hpos : 0 < h := inv_pos.2 (Real.rpow_pos_of_pos hW c)
  obtain ⟨a1, a2⟩ := gtDiag_floor hpos z.re
  obtain ⟨b1, b2⟩ := gtDiag_floor hpos z.im
  have hre' := abs_lt.mp hre
  have hκ2 : 0 ≤ κ / 2 := hpos.le.trans hhκ
  have hm1 := gtDiag_mem_Icc c p hW ⌊z.re / h⌋ (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hm2' : ⌊z.im / h⌋ ∈ Finset.Icc (-(gtDiag_M c p : ℤ)) (gtDiag_M c p) :=
    gtDiag_mem_Icc c p hW _ (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hn2 : (1 : ℝ) ≤ (⌊z.im / h⌋ : ℝ) := by
    refine le_of_mul_le_mul_left ?_ hpos
    linarith
  have hm2 : ⌊z.im / h⌋ ∈ Finset.Icc (1 : ℤ) (gtDiag_M c p) := by
    rw [Finset.mem_Icc] at hm2' ⊢
    exact ⟨by exact_mod_cast hn2, hm2'.2⟩
  have hmem : (⌊z.re / h⌋, ⌊z.im / h⌋) ∈ gtDiag_netZ c p := Finset.mem_product.2 ⟨hm1, hm2⟩
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [gtDiag_zN_re, gtDiag_zN_im]
  simp only
  have hre2 : |h * (⌊z.re / h⌋ : ℝ)| < 2 - κ / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  refine ⟨hre2, by linarith, by linarith, by linarith, ?_, ?_⟩
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [gtDiag_zN_re, gtDiag_zN_im, abs_of_pos (by linarith : (0 : ℝ) < h * ⌊z.im / h⌋)]
    simp only
    linarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, gtDiag_zN_re, gtDiag_zN_im]
    simp only
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z.re - h * ⌊z.re / h⌋),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ z.im - h * ⌊z.im / h⌋)]
    linarith

/-- Rounding `E` with `|E| < 2 − κ` down to the net in `E`: the net point `z'` has `|Re z'| ≤ 2`
and `|E + i − z'| ≤ W^{−c}`, for `W^{−c} ≤ κ`. -/
private theorem gtDiag_netE_point (c : ℝ) (p : SizeL) (hW : 0 < sizeW p) {κ : ℝ}
    (hhκ : (sizeW p ^ c)⁻¹ ≤ κ) (E : ℝ) (hE : |E| < 2 - κ) :
    ∃ n : gtDiag_netE c p, |(gtDiag_zE c p n).re| ≤ 2 ∧
      ‖((E : ℂ) + I) - gtDiag_zE c p n‖ ≤ (sizeW p ^ c)⁻¹ := by
  set h := (sizeW p ^ c)⁻¹ with h_def
  have hpos : 0 < h := inv_pos.2 (Real.rpow_pos_of_pos hW c)
  obtain ⟨a1, a2⟩ := gtDiag_floor hpos E
  have hE' := abs_lt.mp hE
  have hm := gtDiag_mem_Icc c p hW ⌊E / h⌋ (abs_le.mpr ⟨by linarith, by linarith⟩)
  refine ⟨⟨_, hm⟩, ?_, ?_⟩
  · rw [gtDiag_zE_re]
    exact abs_le.mpr ⟨by simp only; linarith, by simp only; linarith⟩
  · have : ((E : ℂ) + I) - gtDiag_zE c p ⟨_, hm⟩ = ((E - h * ⌊E / h⌋ : ℝ) : ℂ) := by
      simp [gtDiag_zE, h_def]
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith

/-- `s_{ij} ≤ |C₀| W^{−d}` from the bound `|f_{W,L}| ≤ C₀ W^{−d}` on `adm(c₀, c₁)`. -/
private theorem gtDiag_S_le {d : ℕ} (P : Profile d) {c₀ c₁ C₀ : ℝ}
    (hC₀ : ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → ∀ x : Zd d L,
      ((zdistInf d L x : ℝ) / W) ^ 0 * |fWL P.ψ W L x| ≤ C₀ / (W : ℝ) ^ d)
    (p : SizeL) (hp : p.1 ∈ adm c₀ c₁) (hW : 0 < sizeW p) (i j : Zd d p.1.2) :
    Smat P.ψ p.1.1 p.1.2 i j ≤ |C₀| * (sizeW p ^ (d : ℝ))⁻¹ := by
  have h := hC₀ p.1.1 p.1.2 hp (i - j)
  rw [pow_zero, one_mul] at h
  have hS : Smat P.ψ p.1.1 p.1.2 i j = fWL P.ψ p.1.1 p.1.2 (i - j) := by simp [Smat]
  have hd : (0 : ℝ) < (p.1.1 : ℝ) ^ d := pow_pos hW d
  rw [hS, Real.rpow_natCast, ← div_eq_mul_inv]
  calc fWL P.ψ p.1.1 p.1.2 (i - j) ≤ |fWL P.ψ p.1.1 p.1.2 (i - j)| := le_abs_self _
    _ ≤ C₀ / (p.1.1 : ℝ) ^ d := h
    _ ≤ |C₀| / sizeW p ^ d := div_le_div_of_nonneg_right (le_abs_self _) hd.le

/-! ## [I, (5.3)] -/

/-- The pointwise step of [I, (5.3)]: at a spectral parameter `z` with `ρ ≤ Im z ≤ 1`, on the good
events at factor `Φ_L ≥ 1` (`‖G − m‖_max ≤ δ`, `T ≤ Φ_L Φ²`, `|h_{ii}|² ≤ Φ_L s_{ii}`, and the
quadratic large deviation bound at every point of a net), given a net point `z'` within
`2h = 2ρ² w q₂` of `z` where `1 − m(z')² S` is stable with constant `K`, and `s_{ij} ≤ C q₂` with
`q₂ ≤ Φ²`: `|G_{ii}(z) − m(z)| ≤ W_τ Φ` whenever `δ + 12 w ≤ 1/(8(K + 1))` and
`(100 K (320 + C)^{1/2} + 12) Φ_L² ≤ W_τ`. -/
private theorem gtDiag_step {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (S : Matrix ι ι ℝ) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ i, ∑ k, S i k = 1) (hS2 : ∀ k, ∑ i, S i k ≤ 1)
    (K C Φl Wτ δ Φv ρ w q2 : ℝ) (hK0 : 0 ≤ K) (hC0 : 0 ≤ C) (hΦl : 1 ≤ Φl)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hw0 : 0 < w) (hw4 : w ≤ 1 / 4) (hq20 : 0 < q2)
    (hq2Φ : q2 ≤ Φv) (hq2Φ2 : q2 ≤ Φv ^ 2) (hq21 : q2 ≤ 1)
    (hδrow : δ + 12 * w ≤ 1 / (8 * (K + 1)))
    (hfin : (100 * K * Real.sqrt (320 + C) + 12) * (Φl * Φl) ≤ Wτ)
    (z : ℂ) (hρη : ρ ≤ z.im) (hz1 : z.im ≤ 1) (hz3 : ‖z‖ ≤ 3)
    {N : Type} (zN : N → ℂ)
    (hnet : ∃ n, 0 < (zN n).im ∧ z.im / 2 ≤ (zN n).im ∧ ‖zN n‖ ≤ 3 ∧
      ‖z - zN n‖ ≤ 2 * (ρ ^ 2 * w * q2) ∧ Stable S (msc (zN n) ^ 2) K)
    (hQ : ∀ n, LDEQuad H (green H (zN n)) S Φl)
    (hA : GoodEvent (green H z) (msc z) δ)
    (hT : ∀ i j, Tvar S (green H z) (msc z) i j ≤ Φl * Φv ^ 2)
    (hD : ∀ i, ‖H i i‖ ^ 2 ≤ Φl * S i i) (hSle : ∀ i j, S i j ≤ C * q2) (i : ι) :
    ‖green H z i i - msc z‖ ≤ Wτ * Φv := by
  obtain ⟨n, him'0, him'2, hz'3, hzz', hst⟩ := hnet
  have hηpos : 0 < z.im := hρ0.trans_le hρη
  have hΦ0 : 0 ≤ Φv := hq20.le.trans hq2Φ
  set e := 12 * w * q2 with he_def
  have hwq : w * q2 ≤ w := mul_le_of_le_one_right hw0.le hq21
  have hwqΦ : w * q2 ≤ Φv := by
    have : w * q2 ≤ 1 * q2 := mul_le_mul_of_nonneg_right (by linarith) hq20.le
    linarith
  have he12 : e ≤ 12 * Φv := by rw [he_def, mul_assoc]; linarith
  have he12w : e ≤ 12 * w := by rw [he_def, mul_assoc]; linarith
  -- transfer from `z` to the net point
  have he : ∀ a b, ‖green H (zN n) a b - green H z a b‖ + ‖msc (zN n) - msc z‖ ≤ e := by
    intro a b
    have h1 := gtDiag_green_lip hH him'0 hηpos a b
    have h2 := gtDiag_msc_lip hηpos hz1 him'0
    rw [norm_sub_rev (msc z)] at h2
    have hprod : ρ ^ 2 / 2 ≤ (zN n).im * z.im := by
      have : ρ * ρ ≤ z.im * z.im := mul_le_mul hρη hρη hρ0.le hηpos.le
      nlinarith
    have hρ2 : 0 < ρ ^ 2 / 2 := by positivity
    have e1 : ‖zN n - z‖ / ((zN n).im * z.im) ≤ 4 * w * q2 := by
      rw [div_le_iff₀ (hρ2.trans_le hprod), norm_sub_rev]
      calc ‖z - zN n‖ ≤ 2 * (ρ ^ 2 * w * q2) := hzz'
        _ = 4 * w * q2 * (ρ ^ 2 / 2) := by ring
        _ ≤ 4 * w * q2 * ((zN n).im * z.im) := mul_le_mul_of_nonneg_left hprod (by positivity)
    have e2 : 4 * ‖z - zN n‖ / z.im ≤ 8 * w * q2 := by
      rw [div_le_iff₀ hηpos]
      calc 4 * ‖z - zN n‖ ≤ 4 * (2 * (ρ ^ 2 * w * q2)) := by linarith
        _ = 8 * w * q2 * (ρ * ρ) := by ring
        _ ≤ 8 * w * q2 * (1 * z.im) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul hρ1 hρη hρ0.le zero_le_one
        _ = 8 * w * q2 * z.im := by ring
    linarith
  -- the inputs of the deterministic step
  have hm4 : 1 / 4 ≤ ‖msc z‖ := norm_msc_ge_quarter z hηpos hz3
  have hT' : ∀ a b, ∑ k, S a k * ‖green H z k b‖ ^ 2 ≤ 16 * (Φl * Φv ^ 2) := by
    intro a b
    have hb := hT a b
    simp only [Tvar] at hb
    have hsum0 : 0 ≤ ∑ k, S a k * ‖green H z k b‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 a k) (sq_nonneg _)
    have hm2 : 1 / 16 ≤ ‖msc z‖ ^ 2 := by nlinarith
    have : (1 / 16) * ∑ k, S a k * ‖green H z k b‖ ^ 2 ≤
        ‖msc z‖ ^ 2 * ∑ k, S a k * ‖green H z k b‖ ^ 2 := mul_le_mul_of_nonneg_right hm2 hsum0
    linarith
  set B := 320 + C with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hΦ2 : 0 ≤ Φv ^ 2 := sq_nonneg _
  have hΦlΦ : Φv ^ 2 ≤ Φl * Φv ^ 2 := le_mul_of_one_le_left hΦ2 hΦl
  have hΛ : 2 * (16 * (Φl * Φv ^ 2)) + 2 * e ^ 2 ≤ B * Φl * Φv ^ 2 := by
    have he2 : e ^ 2 ≤ 144 * Φv ^ 2 := by
      have he0 : 0 ≤ e := by positivity
      nlinarith
    have hC2 : 0 ≤ C * (Φl * Φv ^ 2) := mul_nonneg hC0 (mul_nonneg (by linarith) hΦ2)
    have : B * Φl * Φv ^ 2 = 320 * (Φl * Φv ^ 2) + C * (Φl * Φv ^ 2) := by rw [hB_def]; ring
    rw [this]
    linarith
  have hSΛ : ∀ a b, S a b ≤ B * Φl * Φv ^ 2 := by
    intro a b
    have h2 : C * q2 ≤ C * (Φl * Φv ^ 2) := mul_le_mul_of_nonneg_left (hq2Φ2.trans hΦlΦ) hC0
    have : B * Φl * Φv ^ 2 = 320 * (Φl * Φv ^ 2) + C * (Φl * Φv ^ 2) := by rw [hB_def]; ring
    have h3 : 0 ≤ 320 * (Φl * Φv ^ 2) := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ Φl) hΦ2; linarith
    linarith [hSle a b]
  have hK1 : 0 < K + 1 := by linarith
  have hδ8 : 1 / (8 * (K + 1)) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδe : δ + e ≤ 1 / (8 * (K + 1)) := by linarith
  have hKδ : K * (δ + e) ≤ 1 / 2 := by
    have h1 : K * (δ + e) ≤ K * (1 / (8 * (K + 1))) := mul_le_mul_of_nonneg_left hδe hK0
    have h2 : K * (1 / (8 * (K + 1))) ≤ 1 / 8 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    linarith
  have hcore := gtDiag_core H hH S hS0 hS1 hS2 z (zN n) him'0 hz'3 e δ Φl (16 * (Φl * Φv ^ 2))
    (B * Φl * Φv ^ 2) K he hA (by linarith) hK0 hKδ hΦl (hQ n) hD hT' hΛ hSΛ hst i
  -- the final row
  have hsq : Real.sqrt (B * Φl * Φv ^ 2) ≤ Real.sqrt B * Φl * Φv := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, Real.sq_sqrt hB0]
    have h1 : Φl ≤ Φl ^ 2 := by nlinarith
    have h2 : B * Φl ≤ B * Φl ^ 2 := mul_le_mul_of_nonneg_left h1 hB0
    exact mul_le_mul_of_nonneg_right h2 hΦ2
  have hsB := Real.sqrt_nonneg B
  have hWtt : 1 ≤ Φl * Φl := by nlinarith
  have hA1 : 100 * K * Φl * Real.sqrt (B * Φl * Φv ^ 2) ≤
      100 * K * Φl * (Real.sqrt B * Φl * Φv) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hA2 : e ≤ 12 * Φv * (Φl * Φl) := by
    have : 12 * Φv ≤ 12 * Φv * (Φl * Φl) := le_mul_of_one_le_right (by positivity) hWtt
    linarith
  calc ‖green H z i i - msc z‖
      ≤ 100 * K * Φl * Real.sqrt (B * Φl * Φv ^ 2) + e := hcore
    _ ≤ 100 * K * Φl * (Real.sqrt B * Φl * Φv) + 12 * Φv * (Φl * Φl) := add_le_add hA1 hA2
    _ = (100 * K * Real.sqrt B + 12) * (Φl * Φl) * Φv := by ring
    _ ≤ Wτ * Φv := mul_le_mul_of_nonneg_right hfin hΦ0

/-- **[I, Lemma 5.1, (5.3)]** = [II, Lemma 7.1, (7.3)]: under [I, (5.1)] for any family of spectral
parameters in `𝐃(κ, ε)`, `|G_{xx} − m| ≺ Φ` uniformly in `x` and `u`. -/
theorem diagGT :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ), 0 < c₀ → 0 < c₁ →
  ∀ (κ ε δ₀ : ℝ), 0 < κ → 0 < δ₀ →
  ∀ (U : SizeL → Type) (z : ∀ p, U p → ℂ) (Φ : ∀ p, U p → ℝ),
    GTParams d c₀ c₁ κ ε δ₀ U z Φ → InitialGT d P c₀ c₁ δ₀ U z Φ →
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P) (U := fun p => U p × Zd d p.1.2)
      (fun p v ω => ‖green (hmat ω) (z p v.1) v.2 v.2 - msc (z p v.1)‖) (fun p v _ => Φ p v.1) := by
  intro d P c₀ c₁ hc₀ hc₁ κ ε δ₀ hκ hδ₀ U z Φ hpar hI
  obtain ⟨K, W₁, hK0, hstab⟩ := stable_Smat_strip d P c₀ c₁ hc₀ hc₁ (κ / 2) (by linarith)
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  obtain ⟨C₀, hC₀⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  have ha : 0 ≤ |2 - ε| / c₁ := div_nonneg (abs_nonneg _) hc₁.le
  have hc : 0 ≤ 2 * (|2 - ε| / c₁) + d + 1 := by positivity
  have hsz := tendsto_sizeW_admFilterL c₀ c₁
  have hcard : ∀ᶠ p in admFilterL c₀ c₁,
      (Fintype.card (gtDiag_netZ (2 * (|2 - ε| / c₁) + d + 1) p) : ℝ) ≤
        sizeW p ^ (2 * (2 * (|2 - ε| / c₁) + d + 1) + 6) := by
    filter_upwards [hsz.eventually (eventually_ge_atTop 2)] with p hp
    exact gtDiag_card_netZ _ hc p hp
  have him : ∀ᶠ p in admFilterL c₀ c₁, ∀ n,
      0 < (gtDiag_zN (2 * (|2 - ε| / c₁) + d + 1) p n).im := by
    filter_upwards [hsz.eventually (eventually_ge_atTop 1)] with p hp n
    rw [gtDiag_zN_im]
    have h1 : (1 : ℝ) ≤ (n.1.2 : ℝ) := by
      have := (Finset.mem_product.1 n.2).2
      exact_mod_cast (Finset.mem_Icc.1 this).1
    have h2 : 0 < (sizeW p ^ (2 * (|2 - ε| / c₁) + d + 1))⁻¹ :=
      inv_pos.2 (Real.rpow_pos_of_pos (by linarith) _)
    positivity
  have hQ := ldeQuadDom d P c₀ c₁ (2 * (2 * (|2 - ε| / c₁) + d + 1) + 6) hc₀ hc₁
    (fun p => gtDiag_netZ (2 * (|2 - ε| / c₁) + d + 1) p)
    (gtDiag_zN (2 * (|2 - ε| / c₁) + d + 1)) hcard him
  refine gtDiag_of_four _ _ _ hsz _ _ _ _ _ _ _ _ _ _ hI.1 hI.2 hQ (ldeDiagDom d P c₀ c₁ hc₀ hc₁) ?_
  intro τ hτ
  have ht : 0 < min τ δ₀ / 4 := by have := lt_min hτ hδ₀; positivity
  refine ⟨min τ δ₀ / 4, ht, ?_⟩
  filter_upwards [gtDiag_eventually_adm c₀ c₁, hpar,
    hsz.eventually (eventually_ge_atTop (max W₁ W₂)),
    hsz.eventually (gtDiag_rows τ δ₀ K (320 + |C₀|) κ hτ hδ₀ hK0 hκ)] with
    p hp hparp hW hrow ω hA hB hQp hD v
  obtain ⟨u, x⟩ := v
  obtain ⟨hW4, hWκ, hδrow, hfin⟩ := hrow
  dsimp only
  have hW0 : 0 < sizeW p := by linarith
  have hW1 : 1 ≤ sizeW p := by linarith
  have hds' := hds p.1.1 p.1.2 hp ((le_max_right _ _).trans hW)
  obtain ⟨⟨hre, himlo, him1⟩, hΦlo, -⟩ := hparp u
  have hρ0 : 0 < (sizeW p ^ (|2 - ε| / c₁))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos hW0 _)
  have hρ1 : (sizeW p ^ (|2 - ε| / c₁))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hW1 ha)
  have hρη := (gtDiag_eta_lower ε hc₁ p hp hW1).trans himlo
  have hq0 : 0 < sizeW p ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos hW0 _
  have hq1 : sizeW p ^ (-(d : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  have hqq : (sizeW p ^ (-(d : ℝ) / 2)) ^ 2 = (sizeW p ^ (d : ℝ))⁻¹ := gtDiag_sq_rpow hW0 d
  have hq20 : 0 < (sizeW p ^ (d : ℝ))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos hW0 _)
  have hq2q : (sizeW p ^ (d : ℝ))⁻¹ ≤ sizeW p ^ (-(d : ℝ) / 2) := by
    rw [← hqq, sq]; exact mul_le_of_le_one_left hq0.le hq1
  have hq2Φ2 : (sizeW p ^ (d : ℝ))⁻¹ ≤ Φ p u ^ 2 := by
    rw [← hqq]; exact pow_le_pow_left₀ hq0.le hΦlo 2
  have hw0 : 0 < (sizeW p)⁻¹ := inv_pos.2 hW0
  have hw4 : (sizeW p)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW4
  have hh := gtDiag_h_eq hW0 (|2 - ε| / c₁) d
  have hq21 : (sizeW p ^ (d : ℝ))⁻¹ ≤ 1 := hq2q.trans hq1
  have hρρ : ((sizeW p ^ (|2 - ε| / c₁))⁻¹) ^ 2 ≤ (sizeW p ^ (|2 - ε| / c₁))⁻¹ := by
    rw [sq]; exact mul_le_of_le_one_left hρ0.le hρ1
  have hwq : (sizeW p)⁻¹ * (sizeW p ^ (d : ℝ))⁻¹ ≤ (sizeW p)⁻¹ :=
    mul_le_of_le_one_right hw0.le hq21
  have hhw : (sizeW p ^ (2 * (|2 - ε| / c₁) + d + 1))⁻¹ ≤ κ / 2 := by
    rw [hh, mul_assoc]
    have : ((sizeW p ^ (|2 - ε| / c₁))⁻¹) ^ 2 * ((sizeW p)⁻¹ * (sizeW p ^ (d : ℝ))⁻¹) ≤
        1 * (sizeW p)⁻¹ := mul_le_mul (hρρ.trans hρ1) hwq (by positivity) zero_le_one
    linarith
  have hhρ : 2 * (sizeW p ^ (2 * (|2 - ε| / c₁) + d + 1))⁻¹ ≤ (sizeW p ^ (|2 - ε| / c₁))⁻¹ := by
    rw [hh, mul_assoc]
    have : ((sizeW p ^ (|2 - ε| / c₁))⁻¹) ^ 2 * ((sizeW p)⁻¹ * (sizeW p ^ (d : ℝ))⁻¹) ≤
        (sizeW p ^ (|2 - ε| / c₁))⁻¹ * (1 / 4) :=
      mul_le_mul hρρ (hwq.trans hw4) (by positivity) hρ0.le
    linarith
  have hz3 : ‖z p u‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im (z p u)
    rw [abs_of_pos (hρ0.trans_le hρη)] at this
    linarith [(abs_lt.mp hre).2]
  have hnet : ∃ n, 0 < (gtDiag_zN (2 * (|2 - ε| / c₁) + d + 1) p n).im ∧
      (z p u).im / 2 ≤ (gtDiag_zN (2 * (|2 - ε| / c₁) + d + 1) p n).im ∧
      ‖gtDiag_zN (2 * (|2 - ε| / c₁) + d + 1) p n‖ ≤ 3 ∧
      ‖z p u - gtDiag_zN (2 * (|2 - ε| / c₁) + d + 1) p n‖ ≤
        2 * (((sizeW p ^ (|2 - ε| / c₁))⁻¹) ^ 2 * (sizeW p)⁻¹ * (sizeW p ^ (d : ℝ))⁻¹) ∧
      Stable (Smat P.ψ p.1.1 p.1.2)
        (msc (gtDiag_zN (2 * (|2 - ε| / c₁) + d + 1) p n) ^ 2) K := by
    obtain ⟨n, hre', him'0, him'1, him'2, hz'3, hzz'⟩ :=
      gtDiag_netZ_point _ p hW0 hhρ hhw (z p u) hre hρη him1
    refine ⟨n, him'0, him'2, hz'3, ?_, ?_⟩
    · rw [← hh]; exact hzz'
    · exact hstab p.1.1 p.1.2 hp ((le_max_left _ _).trans hW) _ hre' him'0 him'1
  exact gtDiag_step (hmat ω) (hmat_isHermitian ω) (Smat P.ψ p.1.1 p.1.2)
    (fun i k => nonneg_of_mem_doublyStochastic hds') (sum_row_of_mem_doublyStochastic hds')
    (fun k => (sum_col_of_mem_doublyStochastic hds' k).le) K |C₀|
    (sizeW p ^ (min τ δ₀ / 4)) (sizeW p ^ τ) (sizeW p ^ (min τ δ₀ / 4) * sizeW p ^ (-δ₀))
    (Φ p u) _ _ _ hK0 (abs_nonneg _) (Real.one_le_rpow hW1 ht.le) hρ0 hρ1 hw0 hw4 hq20
    (hq2q.trans hΦlo) hq2Φ2 hq21 hδrow hfin (z p u) hρη him1 hz3 _ hnet (fun n i => hQp (n, i))
    (fun a b => hA (u, a, b)) (fun a b => hB (u, a, b)) hD (gtDiag_S_le P hC₀ p hp hW0) x

/-! ## [II, (8.51)] at `η = 1` -/

/-- The pointwise step of [II, (8.51)] at `η = 1`: at `z` with `Im z = 1`, on the good events at
factor `Φ_L ≥ 1` (row and quadratic large deviation bounds at every point of a net,
`|h_{ii}|² ≤ Φ_L s_{ii}`), given a net point `z'` with `Im z' = 1`, `|Re z'| ≤ 2` and
`|z − z'| ≤ w q²`, and `s_{ij} ≤ C q²` with `q² ≤ w ≤ 1`:
`|G_{ij}(z) − δ_{ij} m(z)| ≤ W_τ q` whenever `Φ_L C w ≤ 1` and `(18 C^{1/2} + 5) Φ_L ≤ W_τ`. -/
private theorem gtDiag_eta1_step {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (S : Matrix ι ι ℝ) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ i, ∑ k, S i k = 1) (C Φl Wτ w q : ℝ) (hC0 : 0 ≤ C) (hΦl : 1 ≤ Φl)
    (hw1 : w ≤ 1) (hq0 : 0 < q) (hq2w : q ^ 2 ≤ w) (hΦσ : Φl * (C * w) ≤ 1)
    (hfin : (18 * Real.sqrt C + 5) * Φl ≤ Wτ) (z : ℂ) (hz1 : z.im = 1) {N : Type}
    (zN : N → ℂ)
    (hnet : ∃ n, (zN n).im = 1 ∧ |(zN n).re| ≤ 2 ∧ ‖z - zN n‖ ≤ w * q ^ 2)
    (hR : ∀ n, LDERow H (green H (zN n)) S Φl) (hQ : ∀ n, LDEQuad H (green H (zN n)) S Φl)
    (hD : ∀ i, ‖H i i‖ ^ 2 ≤ Φl * S i i) (hSle : ∀ i j, S i j ≤ C * q ^ 2) (i j : ι) :
    ‖entryErr (green H z) (msc z) i j‖ ≤ Wτ * q := by
  obtain ⟨n, him', hre', hzz'⟩ := hnet
  have hz0 : 0 < z.im := by rw [hz1]; exact one_pos
  have hz'0 : 0 < (zN n).im := by rw [him']; exact one_pos
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq1 : q ≤ 1 := by
    have : q ^ 2 ≤ 1 := hq2w.trans hw1
    nlinarith
  have hΦσ' : Φl * (C * q ^ 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq2w hC0) (by linarith)).trans hΦσ
  have he : ∀ a b, ‖green H (zN n) a b - green H z a b‖ + ‖msc (zN n) - msc z‖ ≤
      5 * (w * q ^ 2) := by
    intro a b
    have h1 := gtDiag_green_lip hH hz'0 hz0 a b
    have h2 := gtDiag_msc_lip hz0 hz1.le hz'0
    rw [him', hz1, mul_one, div_one, norm_sub_rev (zN n)] at h1
    rw [hz1, div_one, norm_sub_rev (msc z)] at h2
    linarith
  have hcore := gtDiag_eta1_core H hH S (C * q ^ 2) Φl (5 * (w * q ^ 2)) z (zN n) him' hre'
    hS0 hS1 hSle hΦl hΦσ' (hR n) (hQ n) hD he i j
  have hsq : Real.sqrt (Φl * (C * q ^ 2)) ≤ Real.sqrt C * Φl * q := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, Real.sq_sqrt hC0]
    have h1 : Φl ≤ Φl ^ 2 := by nlinarith
    have : Φl * (C * q ^ 2) = C * Φl * q ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC0) hq2
  have he5 : 5 * (w * q ^ 2) ≤ 5 * (Φl * q) := by
    have h1 : w * q ^ 2 ≤ q := by
      have : w * q ^ 2 ≤ 1 * q := by
        rw [sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by nlinarith) hq0.le
      linarith
    have h2 : q ≤ Φl * q := le_mul_of_one_le_left hq0.le hΦl
    linarith
  have hsC := Real.sqrt_nonneg C
  calc ‖entryErr (green H z) (msc z) i j‖ ≤ 18 * Real.sqrt (Φl * (C * q ^ 2)) + 5 * (w * q ^ 2) :=
        hcore
    _ ≤ 18 * (Real.sqrt C * Φl * q) + 5 * (Φl * q) := by linarith
    _ = (18 * Real.sqrt C + 5) * Φl * q := by ring
    _ ≤ Wτ * q := mul_le_mul_of_nonneg_right hfin hq0.le

/-- `‖G(E + i) − m(E + i)‖_max ≤ 2`. -/
private theorem gtDiag_entryErr_le_two {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (E : ℝ) (x y : ι) :
    ‖entryErr (green H ((E : ℂ) + I)) (msc ((E : ℂ) + I)) x y‖ ≤ 2 := by
  have hz : 0 < ((E : ℂ) + I).im := by simp
  have hG : ‖green H ((E : ℂ) + I) x y‖ ≤ 1 := by
    have := norm_green_entry_le hH hz.ne' x y
    simpa using this
  have hm := norm_msc_lt_one hz
  unfold entryErr
  split_ifs
  · exact (norm_sub_le _ _).trans (by linarith)
  · rw [sub_zero]; linarith

/-- **[II, Lemma 8.9, (8.51)] at `η = 1`**:
`max_{x,y} |G_{xy}(E + i) − δ_{xy} m(E + i)| ≺ W^{−d/2}`, uniformly in `x, y` and `|E| < 2 − κ`. -/
theorem eta1Law :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ), 0 < c₀ → 0 < c₁ → ∀ κ : ℝ, 0 < κ →
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
      (U := fun p => {E : ℝ // |E| < 2 - κ} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) ((v.1.1 : ℂ) + I)) (msc ((v.1.1 : ℂ) + I))
        v.2.1 v.2.2‖)
      (fun p _ _ => sizeW p ^ (-(d : ℝ) / 2)) := by
  intro d P c₀ c₁ hc₀ hc₁ κ hκ
  have hsz := tendsto_sizeW_admFilterL c₀ c₁
  have hDg := ldeDiagDom d P c₀ c₁ hc₀ hc₁
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: the entries are bounded by `2`
    refine gtDiag_of_four _ _ _ hsz _ _ _ _ _ _ _ _ _ _ hDg hDg hDg hDg ?_
    intro τ hτ
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [hsz.eventually ((tendsto_rpow_atTop hτ).eventually (eventually_ge_atTop 2))]
      with p h2 ω _ _ _ _ v
    have h0 : sizeW p ^ (-(d : ℝ) / 2) = 1 := by simp [hd]
    simp only [h0, mul_one]
    exact (gtDiag_entryErr_le_two (hmat ω) (hmat_isHermitian ω) _ _ _).trans h2
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  obtain ⟨C₀, hC₀⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  have hc : 0 ≤ (d : ℝ) + 1 := by positivity
  have hcard : ∀ᶠ p in admFilterL c₀ c₁,
      (Fintype.card (gtDiag_netE ((d : ℝ) + 1) p) : ℝ) ≤ sizeW p ^ ((d : ℝ) + 1 + 4) := by
    filter_upwards [hsz.eventually (eventually_ge_atTop 2)] with p hp
    exact gtDiag_card_netE _ hc p hp
  have him : ∀ᶠ p in admFilterL c₀ c₁, ∀ n, 0 < (gtDiag_zE ((d : ℝ) + 1) p n).im :=
    Eventually.of_forall fun p n => by rw [gtDiag_zE_im]; exact one_pos
  have hR := ldeRowDom d P c₀ c₁ ((d : ℝ) + 1 + 4) hc₀ hc₁
    (fun p => gtDiag_netE ((d : ℝ) + 1) p) (gtDiag_zE ((d : ℝ) + 1)) hcard him
  have hQ := ldeQuadDom d P c₀ c₁ ((d : ℝ) + 1 + 4) hc₀ hc₁
    (fun p => gtDiag_netE ((d : ℝ) + 1) p) (gtDiag_zE ((d : ℝ) + 1)) hcard him
  refine gtDiag_of_four _ _ _ hsz _ _ _ _ _ _ _ _ _ _ hR hQ hDg hDg ?_
  intro τ hτ
  have ht : 0 < min τ 1 / 2 := by have := lt_min hτ one_pos; positivity
  refine ⟨min τ 1 / 2, ht, ?_⟩
  filter_upwards [gtDiag_eventually_adm c₀ c₁, hsz.eventually (eventually_ge_atTop W₂),
    hsz.eventually (gtDiag_rows_eta τ |C₀| κ hτ hκ)] with p hp hW hrow ω hRp hQp hD _ v
  obtain ⟨⟨E, hE⟩, x, y⟩ := v
  obtain ⟨hW4, hWκ, hΦσ, hfin⟩ := hrow
  dsimp only
  have hW0 : 0 < sizeW p := by linarith
  have hW1 : 1 ≤ sizeW p := by linarith
  have hds' := hds p.1.1 p.1.2 hp hW
  have hw0 : 0 < (sizeW p)⁻¹ := inv_pos.2 hW0
  have hw1 : (sizeW p)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have hqq : (sizeW p ^ (-(d : ℝ) / 2)) ^ 2 = (sizeW p ^ (d : ℝ))⁻¹ := gtDiag_sq_rpow hW0 d
  have hq2w : (sizeW p ^ (d : ℝ))⁻¹ ≤ (sizeW p)⁻¹ := by
    have h1 : sizeW p ^ (1 : ℝ) ≤ sizeW p ^ (d : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by exact_mod_cast hd)
    rw [Real.rpow_one] at h1
    exact inv_anti₀ hW0 h1
  have hh : (sizeW p ^ ((d : ℝ) + 1))⁻¹ = (sizeW p)⁻¹ * (sizeW p ^ (-(d : ℝ) / 2)) ^ 2 := by
    rw [hqq, Real.rpow_add hW0, Real.rpow_one, mul_inv, mul_comm]
  have hhκ : (sizeW p ^ ((d : ℝ) + 1))⁻¹ ≤ κ := by
    rw [hh, hqq]
    have : (sizeW p)⁻¹ * (sizeW p ^ (d : ℝ))⁻¹ ≤ (sizeW p)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (hq2w.trans hw1) hw0.le
    linarith
  have hnet : ∃ n, (gtDiag_zE ((d : ℝ) + 1) p n).im = 1 ∧
      |(gtDiag_zE ((d : ℝ) + 1) p n).re| ≤ 2 ∧
      ‖((E : ℂ) + I) - gtDiag_zE ((d : ℝ) + 1) p n‖ ≤
        (sizeW p)⁻¹ * (sizeW p ^ (-(d : ℝ) / 2)) ^ 2 := by
    obtain ⟨n, hre', hzz'⟩ := gtDiag_netE_point _ p hW0 hhκ E hE
    exact ⟨n, gtDiag_zE_im _ p n, hre', by rw [← hh]; exact hzz'⟩
  refine gtDiag_eta1_step (hmat ω) (hmat_isHermitian ω) (Smat P.ψ p.1.1 p.1.2)
    (fun i k => nonneg_of_mem_doublyStochastic hds') (sum_row_of_mem_doublyStochastic hds')
    |C₀| (sizeW p ^ (min τ 1 / 2)) (sizeW p ^ τ) (sizeW p)⁻¹ (sizeW p ^ (-(d : ℝ) / 2))
    (abs_nonneg _) (Real.one_le_rpow hW1 ht.le) hw1 (Real.rpow_pos_of_pos hW0 _)
    (by rw [hqq]; exact hq2w) hΦσ hfin _ (by simp) _ hnet (fun n i j => hRp (n, i, j))
    (fun n i => hQp (n, i)) hD ?_ x y
  intro i j
  rw [hqq]
  exact gtDiag_S_le P hC₀ p hp hW0 i j

section Witness

open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

section Instances

end Instances

end RBM8D
