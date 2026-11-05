import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import RBM8D.Basic.Lattice
import RBM8D.Basic.Semicircle
import RBM8D.Prob.StochDom

/-!
# The propagators `Θ`, `S^±`, `b`

[I, (1.16)], [I, (2.1)], [I, (3.4)], and the spectral parameter in the bulk.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complexification of a real kernel. -/
def cmat (S : Matrix ι ι ℝ) : Matrix ι ι ℂ := S.map ((↑) : ℝ → ℂ)

/-- `Θ = |m|² S (1 − |m|² S)⁻¹`, [I, (1.16)]. -/
def Theta (m : ℂ) (S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (‖m‖ ^ 2 • S) * Ring.inverse (1 - ‖m‖ ^ 2 • S)

/-- `S^+ = m² S (1 − m² S)⁻¹`, [I, (2.1)]. -/
def Splus (m : ℂ) (S : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  (m ^ 2 • cmat S) * Ring.inverse (1 - m ^ 2 • cmat S)

/-- `S^- = conj S^+`, [I, (2.1)]. -/
def Sminus (m : ℂ) (S : Matrix ι ι ℝ) : Matrix ι ι ℂ := (Splus m S).map (starRingEnd ℂ)

/-- The inverse of a symmetric matrix is symmetric. -/
private theorem transpose_ringInverse {R : Type*} [CommRing R] (B : Matrix ι ι R) (hB : Bᵀ = B) :
    (Ring.inverse B)ᵀ = Ring.inverse B := by
  rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv, hB]

/-- `A` commutes with `Ring.inverse (1 - A)`. -/
private theorem commute_ringInverse_one_sub {R : Type*} [Ring R] (A : R) :
    A * Ring.inverse (1 - A) = Ring.inverse (1 - A) * A := by
  by_cases h : IsUnit (1 - A)
  · obtain ⟨u, hu⟩ := h
    have h1 : (1 - A) * Ring.inverse (1 - A) = 1 := by
      rw [← hu, Ring.mul_inverse_cancel _ u.isUnit]
    have h2 : Ring.inverse (1 - A) * (1 - A) = 1 := by
      rw [← hu, Ring.inverse_mul_cancel _ u.isUnit]
    rw [sub_mul, one_mul] at h1
    rw [mul_sub, mul_one] at h2
    exact sub_right_inj.mp (h1.trans h2.symm)
  · rw [Ring.inverse_non_unit _ h]; simp

private theorem transpose_mul_ringInverse {R : Type*} [CommRing R] (A : Matrix ι ι R)
    (hA : Aᵀ = A) : (A * Ring.inverse (1 - A))ᵀ = A * Ring.inverse (1 - A) := by
  have h1 : (1 - A)ᵀ = 1 - A := by rw [transpose_sub, transpose_one, hA]
  rw [transpose_mul, transpose_ringInverse _ h1, hA]
  exact (commute_ringInverse_one_sub A).symm

/-- `S^+`, `S^-` and `Θ` are symmetric when `S` is, [I, (1.16)], [I, (2.1)]. -/
theorem transpose_propagators :
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (hS : Sᵀ = S) (m : ℂ),
    (Splus m S)ᵀ = Splus m S ∧ (Sminus m S)ᵀ = Sminus m S ∧ (Theta m S)ᵀ = Theta m S := by
  intro ι _ _ S hS m
  have hc : (cmat S)ᵀ = cmat S := by
    ext i j
    have := congrFun (congrFun hS i) j
    simp only [cmat, transpose_apply, map_apply] at this ⊢
    rw [this]
  have h1 : (Splus m S)ᵀ = Splus m S := by
    have := transpose_mul_ringInverse (m ^ 2 • cmat S) (by rw [transpose_smul, hc])
    exact this
  refine ⟨h1, ?_, ?_⟩
  · rw [Sminus, ← transpose_map, h1]
  · exact transpose_mul_ringInverse (‖m‖ ^ 2 • S) (by rw [transpose_smul, hS])

/-- For `S` nonnegative with row sums one and `|m| < 1`, `Θ = Σ_{k ≥ 1} |m|^{2k} S^k`
(the series after [I, (1.30)]). -/
theorem Theta_hasSum :
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) (m : ℂ) (hm : ‖m‖ < 1),
    HasSum (fun k : ℕ => ‖m‖ ^ (2 * (k + 1)) • S ^ (k + 1)) (Theta m S) := by
  intro ι _ _ S hS0 hS1 m hm
  let : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  have hS : ‖S‖ ≤ 1 := by
    rw [Matrix.linfty_opNorm_def]
    have : (Finset.univ.sup fun i => ∑ j, ‖S i j‖₊) ≤ 1 := by
      refine Finset.sup_le fun i _ => ?_
      rw [← NNReal.coe_le_coe]
      push_cast
      simp only [Real.norm_eq_abs, abs_of_nonneg (hS0 _ _)]
      rw [hS1 i]
    exact_mod_cast this
  set r : ℝ := ‖m‖ ^ 2 with hr
  have hr1 : r < 1 := by
    rw [hr]; nlinarith [norm_nonneg m]
  have hr0 : 0 ≤ r := by positivity
  have hrS : ‖r • S‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    nlinarith [norm_nonneg S]
  have h := (hasSum_geom_series_inverse (r • S) hrS).mul_left (r • S)
  have h2 : HasSum (fun k : ℕ => ‖m‖ ^ (2 * (k + 1)) • S ^ (k + 1)) (Theta m S) := by
    have e : (fun k : ℕ => ‖m‖ ^ (2 * (k + 1)) • S ^ (k + 1)) =
        fun k : ℕ => r • S * (r • S) ^ k := by
      funext k
      rw [smul_pow, smul_mul_smul_comm, ← pow_succ', ← pow_succ' S k, hr, ← pow_mul]
    rw [e]
    exact h
  exact h2

/-- `√(2κ)/5 ≤ N` follows from `2κ ≤ 25 N²` for `N ≥ 0`. -/
private theorem sqrt_div_five_le {κ N : ℝ} (hκ : 0 < κ) (h : 2 * κ ≤ 25 * N ^ 2) (hN : 0 ≤ N) :
    Real.sqrt (2 * κ) / 5 ≤ N := by
  have h1 : Real.sqrt (2 * κ) ^ 2 = 2 * κ := Real.sq_sqrt (by positivity)
  have h2 := Real.sqrt_nonneg (2 * κ)
  by_contra hlt
  push Not at hlt
  nlinarith

/-- In the bulk `|Re z| ≤ 2 − κ`, `Im z > 0`: `|m(z)| ≤ 1` and `|1 − m(z)²| ≥ √(2κ)/5`
([I, Lemma 2.2], [II, Lemma 2.1]). -/
theorem msc_bulk :
  ∀ (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz : 0 < z.im) (hE : |z.re| ≤ 2 - κ),
    ‖msc z‖ ≤ 1 ∧ Real.sqrt (2 * κ) / 5 ≤ ‖1 - msc z ^ 2‖ := by
  intro κ hκ z hz hE
  set m := msc z with hmdef
  have hm1 : ‖m‖ < 1 := norm_msc_lt_one hz
  refine ⟨hm1.le, ?_⟩
  have hmz : m * (m + z) = -1 := msc_mul z
  have hq : m ^ 2 + z * m + 1 = 0 := by linear_combination hmz
  have h1 : (1 - m ^ 2) ^ 2 = m ^ 2 * ((z - 2) * (z + 2)) := by
    linear_combination (m ^ 2 + 1 - m * z) * hq
  have hN : ‖1 - m ^ 2‖ ^ 2 = ‖m‖ ^ 2 * (‖z - 2‖ * ‖z + 2‖) := by
    have := congrArg norm h1
    simp only [norm_pow, norm_mul] at this
    exact this
  set a := ‖z - 2‖ with ha
  set b := ‖z + 2‖ with hb
  set t := ‖z‖ with ht
  have hm0 : 0 ≤ ‖m‖ := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have ht0 : 0 ≤ t := norm_nonneg _
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg z.re]
  -- `‖m‖ (1 + ‖z‖) ≥ 1`
  have hm2 : 1 ≤ ‖m‖ * (1 + t) := by
    have h := congrArg norm hmz
    rw [norm_mul, norm_neg, norm_one] at h
    have h3 : ‖m + z‖ ≤ 1 + t := by
      calc ‖m + z‖ ≤ ‖m‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 + t := by linarith
    calc (1 : ℝ) = ‖m‖ * ‖m + z‖ := h.symm
      _ ≤ ‖m‖ * (1 + t) := mul_le_mul_of_nonneg_left h3 hm0
  -- lower bounds on `a`, `b`
  have haκ : κ ≤ a := by
    have : |(z - 2).re| ≤ a := Complex.abs_re_le_norm _
    have h2 : (z - 2).re = z.re - 2 := by simp
    rw [h2] at this
    have : 2 - z.re ≤ |z.re - 2| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith [abs_le.mp (show |z.re| ≤ 2 - κ from hE), le_abs_self z.re, neg_abs_le z.re]
  have hbκ : κ ≤ b := by
    have h3 : |(z + 2).re| ≤ b := Complex.abs_re_le_norm _
    have h2 : (z + 2).re = z.re + 2 := by simp
    rw [h2] at h3
    have h4 : z.re + 2 ≤ |z.re + 2| := le_abs_self _
    linarith [abs_le.mp (show |z.re| ≤ 2 - κ from hE)]
  have hab8 : 8 ≤ a ^ 2 + b ^ 2 := by
    have e1 : a ^ 2 = (z.re - 2) ^ 2 + z.im ^ 2 := by
      rw [ha, Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have e2 : b ^ 2 = (z.re + 2) ^ 2 + z.im ^ 2 := by
      rw [hb, Complex.sq_norm, Complex.normSq_apply]; simp; ring
    rw [e1, e2]; nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hab : 2 * κ ≤ a * b := by
    by_cases hA : 2 ≤ a
    · nlinarith
    · have hB : 2 ≤ b := by
        by_contra hB
        push Not at hB hA
        nlinarith
      nlinarith
  have hNnn : 0 ≤ ‖1 - m ^ 2‖ := norm_nonneg _
  apply sqrt_div_five_le hκ _ hNnn
  rw [hN]
  by_cases ht4 : t ≤ 4
  · have hm5 : 1 ≤ ‖m‖ * 5 := by nlinarith
    have : 1 ≤ ‖m‖ ^ 2 * 25 := by nlinarith
    nlinarith [mul_nonneg ha0 hb0]
  · push Not at ht4
    have hta : t ≤ a + 2 := by
      calc t = ‖(z - 2) + 2‖ := by rw [sub_add_cancel]
        _ ≤ a + ‖(2 : ℂ)‖ := norm_add_le _ _
        _ = a + 2 := by simp
    have htb : t ≤ b + 2 := by
      calc t = ‖(z + 2) + (-2)‖ := by rw [add_neg_cancel_right]
        _ ≤ b + ‖(-2 : ℂ)‖ := norm_add_le _ _
        _ = b + 2 := by simp
    have hab4 : t ^ 2 / 4 ≤ a * b := by
      have h1 : t / 2 ≤ a := by linarith
      have h3 : t / 2 ≤ b := by linarith
      nlinarith [mul_le_mul h1 h3 (by linarith) ha0]
    have hP : 1 ≤ ‖m‖ ^ 2 * (1 + t) ^ 2 := by nlinarith
    have hpos : 0 < (1 + t) ^ 2 := by positivity
    have hQ : 4 / 25 * (1 + t) ^ 2 ≤ (‖m‖ ^ 2 * (a * b)) * (1 + t) ^ 2 := by
      have : a * b ≤ (‖m‖ ^ 2 * (1 + t) ^ 2) * (a * b) :=
        le_mul_of_one_le_left (mul_nonneg ha0 hb0) hP
      nlinarith
    have := le_of_mul_le_mul_right hQ hpos
    linarith

/-- For `|E| ≤ 2 − κ`: `|m(E)| = 1` and `|1 − m(E)²| ≥ √(2κ)/5`. -/
theorem mE_bulk :
  ∀ (κ : ℝ) (hκ : 0 < κ) (E : ℝ) (hE : |E| ≤ 2 - κ),
    ‖mE E‖ = 1 ∧ Real.sqrt (2 * κ) / 5 ≤ ‖1 - mE E ^ 2‖ := by
  intro κ hκ E hE
  have hE2 : |E| ≤ 2 := by linarith
  refine ⟨norm_mE hE2, ?_⟩
  have hsq : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := by
    apply Real.sq_sqrt
    have := abs_le.mp hE2
    nlinarith
  have hw : 1 - mE E ^ 2 = ((4 - E ^ 2 + Real.sqrt (4 - E ^ 2) ^ 2) / 4 : ℝ) +
      ((E * Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [mE, pow_two] <;> nlinarith [hsq]
  have hN : ‖1 - mE E ^ 2‖ ^ 2 = 4 - E ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hw]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, zero_add, mul_im]
    nlinarith [hsq]
  have hkE : 2 * κ ≤ 4 - E ^ 2 := by
    have h1 : E ^ 2 = |E| ^ 2 := (sq_abs E).symm
    have h0 := abs_nonneg E
    nlinarith
  exact sqrt_div_five_le hκ (by nlinarith [norm_nonneg (1 - mE E ^ 2)]) (norm_nonneg _)

section Witness

end Witness

end RBM8D
