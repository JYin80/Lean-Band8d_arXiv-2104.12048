module

public import RBM8D.MainDefs
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The resolvent of a Hermitian matrix

For a Hermitian matrix `H` and `z` off the real axis, `green H z = (H - z)⁻¹` is the Green
function `G(z)` of the paper.  The basic estimate is `|Im z| ‖v‖ ≤ ‖T v - z v‖` for a symmetric
operator `T`, which gives invertibility of `H - z`, the entry bound `|G_{xy}| ≤ |Im z|⁻¹`, the
resolvent identity, and the Ward identity `∑_y |G_{xy}|² = Im G_{xx} / Im z`
([I, Lemma 5.5]).  The norm used on vectors is the `ℓ²` norm of `EuclideanSpace ℂ n`.
-/

namespace RBM8D

open RCLike ComplexConjugate
open scoped ComplexInnerProductSpace

section Symmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For a symmetric operator the quadratic form is real. -/
theorem im_inner_self_symm {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (v : E) :
    (⟪v, T v⟫).im = 0 := by
  have h : conj ⟪v, T v⟫ = ⟪v, T v⟫ := by
    rw [inner_conj_symm, hT v v]
  exact Complex.conj_eq_iff_im.mp h

/-- For symmetric `T`, `|Im z| ‖v‖ ≤ ‖T v - z v‖`. -/
theorem norm_sub_smul_ge {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (z : ℂ) (v : E) :
    |z.im| * ‖v‖ ≤ ‖T v - z • v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hinner : ⟪v, T v - z • v⟫ = ⟪v, T v⟫ - z * ⟪v, v⟫ := by
    rw [inner_sub_right, inner_smul_right]
  have hre : (⟪v, v⟫ : ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  have him : (⟪v, T v - z • v⟫).im = -(z.im * ‖v‖ ^ 2) := by
    rw [hinner, Complex.sub_im, Complex.mul_im, im_inner_self_symm hT v,
      show (⟪v, v⟫ : ℂ).im = 0 from inner_self_im (𝕜 := ℂ) v, hre]
    ring
  have h1 : |z.im| * ‖v‖ ^ 2 = |(⟪v, T v - z • v⟫).im| := by
    rw [him, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖ ^ 2)]
  have h2 : |(⟪v, T v - z • v⟫).im| ≤ ‖v‖ * ‖T v - z • v‖ := by
    refine le_trans ?_ (norm_inner_le_norm (𝕜 := ℂ) v (T v - z • v))
    exact Complex.abs_im_le_norm (⟪v, T v - z • v⟫)
  have h3 : |z.im| * ‖v‖ ^ 2 ≤ ‖v‖ * ‖T v - z • v‖ := h1 ▸ h2
  have h4 : |z.im| * ‖v‖ * ‖v‖ ≤ ‖T v - z • v‖ * ‖v‖ := by nlinarith
  exact le_of_mul_le_mul_right h4 hvpos

/-- `T - z` is injective off the real axis. -/
theorem injective_sub_smul {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Injective fun v => T v - z • v := by
  intro u v huv
  have h : T (u - v) - z • (u - v) = 0 := by
    simp only [map_sub, smul_sub] at *
    rw [sub_sub_sub_comm] at *
    simpa [sub_eq_zero] using huv
  have := norm_sub_smul_ge hT z (u - v)
  rw [h, norm_zero] at this
  have habs : 0 < |z.im| := abs_pos.mpr hz
  have : ‖u - v‖ ≤ 0 := by nlinarith [norm_nonneg (u - v)]
  have : u - v = 0 := by
    simpa using norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
  exact sub_eq_zero.mp this

/-- A solution of `T u - z u = w` obeys `‖u‖ ≤ |Im z|⁻¹ ‖w‖`. -/
theorem norm_le_of_sub_smul_eq {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {z : ℂ} (hz : z.im ≠ 0)
    {u w : E} (h : T u - z • u = w) : ‖u‖ ≤ |z.im|⁻¹ * ‖w‖ := by
  have habs : 0 < |z.im| := abs_pos.mpr hz
  have := norm_sub_smul_ge hT z u
  rw [h] at this
  rw [inv_mul_eq_div, le_div_iff₀ habs]
  linarith [this]

end Symmetric

open Matrix in
/-- Off the real axis, `H - z` is invertible. -/
theorem isUnit_sub_smul_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (H - z • (1 : Matrix n n ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hv0⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hmul : Matrix.toEuclideanLin H (WithLp.toLp 2 v) - z • (WithLp.toLp 2 v) = 0 := by
    have : (H - z • (1 : Matrix n n ℂ)) *ᵥ v = H *ᵥ v - z • v := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [this] at hv0
    ext i
    simpa [Matrix.toLpLin_apply] using congrFun hv0 i
  have hinj := injective_sub_smul (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) hz
  have : WithLp.toLp 2 v = 0 := by
    have h0 : (fun w => Matrix.toEuclideanLin H w - z • w) (WithLp.toLp 2 v)
        = (fun w => Matrix.toEuclideanLin H w - z • w) 0 := by simpa using hmul
    simpa using hinj h0
  exact hv (by simpa using congrArg (WithLp.ofLp) this)

open Matrix in
/-- The entry bound `|((H - z)⁻¹)_{xy}| ≤ |Im z|⁻¹`, stated with `Ring.inverse`. -/
theorem norm_inverse_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (x y : n) :
    ‖Ring.inverse (H - z • (1 : Matrix n n ℂ)) x y‖ ≤ |z.im|⁻¹ := by
  set G := Ring.inverse (H - z • (1 : Matrix n n ℂ)) with hG
  set e : n → ℂ := Pi.single y 1 with he
  have hunit := isUnit_sub_smul_of_isHermitian hH hz
  have hsol : (H - z • (1 : Matrix n n ℂ)) *ᵥ (G *ᵥ e) = e := by
    rw [Matrix.mulVec_mulVec, hG, Ring.mul_inverse_cancel _ hunit, Matrix.one_mulVec]
  have hEuclid : Matrix.toEuclideanLin H (WithLp.toLp 2 (G *ᵥ e)) - z • WithLp.toLp 2 (G *ᵥ e)
      = WithLp.toLp 2 e := by
    have hrw : (H - z • (1 : Matrix n n ℂ)) *ᵥ (G *ᵥ e) = H *ᵥ (G *ᵥ e) - z • (G *ᵥ e) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hrw] at hsol
    ext i
    simpa [Matrix.toLpLin_apply] using congrFun hsol i
  have hnorm := norm_le_of_sub_smul_eq (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) hz hEuclid
  have hone : ‖WithLp.toLp 2 e‖ = 1 := by
    simp [he, PiLp.norm_single]
  rw [hone, mul_one] at hnorm
  have hcoord : ‖(G *ᵥ e) x‖ ≤ ‖WithLp.toLp 2 (G *ᵥ e)‖ := by
    simpa using PiLp.norm_apply_le (WithLp.toLp 2 (G *ᵥ e)) x
  have hentry : (G *ᵥ e) x = G x y := by
    simp [he, Matrix.mulVec_single]
  rw [hentry] at hcoord
  exact le_trans hcoord hnorm

section Green

variable {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}

theorem green_mul_sub (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
  Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_sub_smul_of_isHermitian hH hz))

theorem sub_mul_green (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix n n ℂ)) * green H z = 1 :=
  Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_sub_smul_of_isHermitian hH hz))

/-- The entries of the Green function are bounded by `|Im z|⁻¹`. -/
theorem norm_green_entry_le (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (x y : n) :
    ‖green H z x y‖ ≤ |z.im|⁻¹ := by
  unfold green
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact norm_inverse_entry_le hH hz x y

/-- The resolvent identity `G(z) - G(w) = (z - w) G(z) G(w)`. -/
theorem green_sub_green (hH : H.IsHermitian) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    green H z - green H w = (z - w) • (green H z * green H w) := by
  have h1 := green_mul_sub hH hz
  have h2 := sub_mul_green hH hw
  have hB : (H - w • (1 : Matrix n n ℂ)) = (H - z • (1 : Matrix n n ℂ)) + (z - w) • 1 := by
    rw [sub_smul]; abel
  have key : green H z * (H - w • (1 : Matrix n n ℂ)) * green H w = green H z := by
    rw [mul_assoc, h2, mul_one]
  rw [hB, mul_add, add_mul, h1, mul_smul_comm, mul_one, smul_mul_assoc, one_mul] at key
  exact sub_eq_of_eq_add' key.symm

/-- `G(z)ᴴ = G(z̄)`. -/
theorem green_conjTranspose (hH : H.IsHermitian) (z : ℂ) :
    Matrix.conjTranspose (green H z) = green H (starRingEnd ℂ z) := by
  unfold green
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hH.eq]
  rfl

private theorem green_conj_apply (hH : H.IsHermitian) (z : ℂ) (x : n) :
    green H (starRingEnd ℂ z) x x = starRingEnd ℂ (green H z x x) := by
  rw [← green_conjTranspose hH z]
  simp [Matrix.conjTranspose_apply]

private theorem mul_star_self_eq (a : ℂ) : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def]
  push_cast
  exact Complex.mul_conj' a

private theorem star_mul_self_eq (a : ℂ) : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]
  exact mul_star_self_eq a

private theorem sum_norm_sq_eq {z : ℂ} (hz : 0 < z.im) (x : n)
    (S : ℝ) (hS : green H z x x - starRingEnd ℂ (green H z x x) = 2 * z.im * Complex.I * S) :
    S = (green H z x x).im / z.im := by
  rw [Complex.sub_conj] at hS
  have h := congrArg Complex.im hS
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im] at h
  rw [eq_div_iff hz.ne']
  simp at h
  nlinarith

theorem sum_norm_sq_green_row (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x : n) :
    ∑ y, ‖green H z x y‖ ^ 2 = (green H z x x).im / z.im := by
  refine sum_norm_sq_eq hz x _ ?_
  have hw : (starRingEnd ℂ z).im ≠ 0 := by simpa using hz.ne'
  have h := congrArg (fun M : Matrix n n ℂ => M x x) (green_sub_green hH hz.ne' hw)
  simp only [Matrix.sub_apply] at h
  rw [green_conj_apply hH z x] at h
  rw [h, ← green_conjTranspose hH z, Complex.sub_conj]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [mul_star_self_eq]
  push_cast
  ring

theorem sum_norm_sq_green_col (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x : n) :
    ∑ y, ‖green H z y x‖ ^ 2 = (green H z x x).im / z.im := by
  refine sum_norm_sq_eq hz x _ ?_
  have hw : (starRingEnd ℂ z).im ≠ 0 := by simpa using hz.ne'
  have h := congrArg (fun M : Matrix n n ℂ => M x x)
    (green_sub_green hH hw hz.ne')
  simp only [Matrix.sub_apply] at h
  rw [green_conj_apply hH z x] at h
  have h' : green H z x x - starRingEnd ℂ (green H z x x) =
      ((z - starRingEnd ℂ z) • (green H (starRingEnd ℂ z) * green H z)) x x := by
    rw [← neg_sub, h, ← neg_sub z, neg_smul]
    simp [Matrix.neg_apply]
  rw [h', ← green_conjTranspose hH z, Complex.sub_conj]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [star_mul_self_eq]
  push_cast
  ring

end Green

end RBM8D
