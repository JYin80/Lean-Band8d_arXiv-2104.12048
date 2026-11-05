import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The semicircle Stieltjes transform

`msc z` is the Stieltjes transform `m(z)` of the semicircle law of [I, (1.15)]: the root of
`m² + z m + 1 = 0` with `Im m > 0` when `Im z > 0`.  `mE E` is the
corresponding root of `m (m + E) = -1` for real `E` with `|E| ≤ 2`; for `|E| < 2` it has positive
imaginary part and modulus `1`.
-/

namespace RBM8D

open Complex

/-- The boundary value `(-E + i √(4 - E²)) / 2` of `m` at a real energy `E`. -/
noncomputable def mE (E : ℝ) : ℂ := (-E + Real.sqrt (4 - E ^ 2) * I) / 2

theorem mE_re (E : ℝ) : (mE E).re = -E / 2 := by simp [mE]

theorem mE_im (E : ℝ) : (mE E).im = Real.sqrt (4 - E ^ 2) / 2 := by simp [mE]

private theorem sq_sqrt_four_sub {E : ℝ} (hE : |E| ≤ 2) :
    Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := by
  refine Real.sq_sqrt ?_
  have := abs_le.mp hE
  nlinarith

theorem mE_mul {E : ℝ} (hE : |E| ≤ 2) : mE E * (mE E + E) = -1 := by
  have hs : ((Real.sqrt (4 - E ^ 2) : ℝ) : ℂ) ^ 2 = 4 - (E : ℂ) ^ 2 := by
    exact_mod_cast sq_sqrt_four_sub hE
  have hI : I ^ 2 = -1 := I_sq
  simp only [mE]
  linear_combination ((Real.sqrt (4 - E ^ 2) : ℂ) ^ 2 / 4) * hI - (1 / 4 : ℂ) * hs

theorem mE_im_pos {E : ℝ} (hE : |E| < 2) : 0 < (mE E).im := by
  rw [mE_im]
  have := abs_lt.mp hE
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

theorem norm_mE {E : ℝ} (hE : |E| ≤ 2) : ‖mE E‖ = 1 := by
  have h2 : ‖mE E‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mE_re, mE_im]
    have := sq_sqrt_four_sub hE
    nlinarith
  have := norm_nonneg (mE E)
  nlinarith

/-- A chosen square root of `z² - 4`. -/
noncomputable def mscDisc (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

theorem mscDisc_sq (z : ℂ) : mscDisc z ^ 2 = z ^ 2 - 4 :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

/-- The root `(-z + √(z² - 4)) / 2` of `m² + z m + 1 = 0`. -/
noncomputable def mscRoot₁ (z : ℂ) : ℂ := (-z + mscDisc z) / 2

/-- The root `(-z - √(z² - 4)) / 2` of `m² + z m + 1 = 0`. -/
noncomputable def mscRoot₂ (z : ℂ) : ℂ := (-z - mscDisc z) / 2

/-- The Stieltjes transform `m(z)` of the semicircle law, [I, (1.15)]: the root of
`m² + z m + 1 = 0` with positive imaginary part when `Im z > 0`. -/
noncomputable def msc (z : ℂ) : ℂ := if 0 < (mscRoot₁ z).im then mscRoot₁ z else mscRoot₂ z

theorem msc_mul (z : ℂ) : msc z * (msc z + z) = -1 := by
  have hd := mscDisc_sq z
  unfold msc mscRoot₁ mscRoot₂
  split_ifs <;> linear_combination (1 / 4 : ℂ) * hd

theorem msc_ne_zero (z : ℂ) : msc z ≠ 0 := by
  intro h
  have := msc_mul z
  rw [h] at this
  simp at this

theorem msc_add_eq_neg_inv (z : ℂ) : msc z + z = -(msc z)⁻¹ := by
  have hm0 := msc_ne_zero z
  field_simp
  linear_combination msc_mul z

theorem msc_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (msc z).im := by
  have hd := mscDisc_sq z
  unfold msc
  split_ifs with h
  · exact h
  · push Not at h
    set r₁ := mscRoot₁ z
    set r₂ := mscRoot₂ z
    have hmul : r₁ * r₂ = 1 := by
      simp only [r₁, r₂, mscRoot₁, mscRoot₂]
      linear_combination (-1 / 4 : ℂ) * hd
    have hsum : r₁.im + r₂.im = -z.im := by
      have : r₁ + r₂ = -z := by simp only [r₁, r₂, mscRoot₁, mscRoot₂]; ring
      simpa using congrArg Complex.im this
    have hr₁ : r₁ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
    have hr₂ : r₂ = r₁⁻¹ := eq_inv_of_mul_eq_one_right hmul
    have hN : 0 < Complex.normSq r₁ := Complex.normSq_pos.mpr hr₁
    have him : r₂.im * Complex.normSq r₁ = -r₁.im := by
      rw [hr₂, Complex.inv_im]
      field_simp
    by_contra hneg
    push Not at hneg
    have h1 : r₂.im * Complex.normSq r₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hN.le
    have h2 : r₁.im = 0 := by linarith
    have h3 : r₂.im < 0 := by linarith
    have h4 : r₂.im * Complex.normSq r₁ < 0 := mul_neg_of_neg_of_pos h3 hN
    linarith

theorem norm_msc_lt_one {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ < 1 := by
  have hm := msc_mul z
  have him := msc_im_pos hz
  set m := msc z
  have hm0 : m ≠ 0 := msc_ne_zero z
  have hinv : m + z = -m⁻¹ := msc_add_eq_neg_inv z
  have hN : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm0
  have key : (m.im + z.im) * Complex.normSq m = m.im := by
    have := congrArg Complex.im hinv
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at this
    rw [this]
    field_simp
  have hN1 : Complex.normSq m < 1 := by nlinarith
  have h2 : ‖m‖ ^ 2 < 1 := by rwa [Complex.sq_norm]
  have := norm_nonneg m
  nlinarith

end RBM8D
