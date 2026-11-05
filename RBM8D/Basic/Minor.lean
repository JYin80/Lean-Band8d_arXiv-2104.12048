import RBM8D.Basic.Resolvent

/-!
# Resolvent minors and the Schur complement formula

For an invertible matrix `M` with inverse `G` and `G i i ≠ 0`, the matrix
`minorGreen G i = (G_{jk} - G_{ji} G_{ik} / G_{ii})_{j,k ≠ i}` is the inverse of the minor
`minorMat M i` obtained by deleting row and column `i`.  For the resolvent of a Hermitian matrix
this gives `G^(i) = (H^(i) - z)⁻¹` ([II, §4.4]), the Schur complement formula for `G_ii`, the
formula `G_ij = -G_ii ∑_{k ≠ i} h_ik G^(i)_kj`, and the identities [II, (4.17)] and [II, (4.20)]
(`green_eq_greenMinor_add`).
-/

namespace RBM8D

open Matrix Finset

section Field

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Field R]

/-- Summing over every index different from `i` is summing over everything and
subtracting the `i`-th term. -/
theorem sum_subtype_ne (i : n) (f : n → R) :
    ∑ k : {a : n // a ≠ i}, f k.1 = (∑ k, f k) - f i := by
  have h1 : ∑ k ∈ Finset.univ.erase i, f k = ∑ k : {a : n // a ≠ i}, f k.1 :=
    Finset.sum_subtype _ (fun x => by simp) f
  rw [← h1, Finset.sum_erase_eq_sub (Finset.mem_univ i)]

/-- The minor `M^(i)`: delete row `i` and column `i`. -/
def minorMat (M : Matrix n n R) (i : n) : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R :=
  M.submatrix Subtype.val Subtype.val

/-- The candidate inverse of the minor of `M`, in terms of `G = M⁻¹`:
`G_{jk} - G_{ji} G_{ik} / G_{ii}` for `j, k ≠ i` ([II, (4.20)]). -/
def minorGreen (G : Matrix n n R) (i : n) : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R :=
  Matrix.of fun j k => G j.1 k.1 - G j.1 i * G i k.1 / G i i

omit [Fintype n] [DecidableEq n] [Field R] in
@[simp] theorem minorMat_apply (M : Matrix n n R) (i : n) (j k : {a : n // a ≠ i}) :
    minorMat M i j k = M j.1 k.1 := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem minorGreen_apply (G : Matrix n n R) (i : n) (j k : {a : n // a ≠ i}) :
    minorGreen G i j k = G j.1 k.1 - G j.1 i * G i k.1 / G i i := rfl

variable {M G : Matrix n n R}

/-- Row identity coming from `G * M = 1`, with the `i`-th term split off. -/
theorem sum_ne_green_mul (hGM : G * M = 1) (i : n) (a l : n) :
    ∑ k : {b : n // b ≠ i}, G a k.1 * M k.1 l = (if a = l then (1 : R) else 0) - G a i * M i l := by
  rw [sum_subtype_ne i (fun k => G a k * M k l)]
  have h : ∑ k, G a k * M k l = (if a = l then (1 : R) else 0) := by
    have h2 := congrArg (fun X : Matrix n n R => X a l) hGM
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2
  rw [h]

/-- Row identity coming from `M * G = 1`, with the `i`-th term split off. -/
theorem sum_ne_mul_green (hMG : M * G = 1) (i : n) (a b : n) :
    ∑ k : {c : n // c ≠ i}, M a k.1 * G k.1 b = (if a = b then (1 : R) else 0) - M a i * G i b := by
  rw [sum_subtype_ne i (fun k => M a k * G k b)]
  have h : ∑ k, M a k * G k b = (if a = b then (1 : R) else 0) := by
    have h2 := congrArg (fun X : Matrix n n R => X a b) hMG
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2
  rw [h]

/-- `minorGreen G i` is a left inverse of the minor `minorMat M i` ([II, (4.20)]). Only
`G i i ≠ 0` is needed; invertibility of the minor is a conclusion. -/
theorem minorGreen_mul_minorMat (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0) :
    minorGreen G i * minorMat M i = 1 := by
  ext j l
  have hil : (i : n) ≠ l.1 := fun h => l.2 h.symm
  have hjl : ((1 : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R) j l)
      = (if j.1 = l.1 then (1 : R) else 0) := by
    by_cases h : j = l
    · subst h
      simp [Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h, ite_eq_right (fun hh => h (Subtype.ext hh))]
  rw [hjl, Matrix.mul_apply]
  have hsplit : ∑ k : {a : n // a ≠ i}, minorGreen G i j k * minorMat M i k l
      = (∑ k : {a : n // a ≠ i}, G j.1 k.1 * M k.1 l.1)
        - (G j.1 i / G i i) * ∑ k : {a : n // a ≠ i}, G i k.1 * M k.1 l.1 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [minorGreen_apply, minorMat_apply]
    ring
  rw [hsplit, sum_ne_green_mul hGM i j.1 l.1, sum_ne_green_mul hGM i i l.1, ite_eq_right hil]
  have hcancel : G j.1 i / G i i * ((0 : R) - G i i * M i l.1) = -(G j.1 i * M i l.1) := by
    rw [zero_sub, mul_neg, neg_inj]
    field_simp
  rw [hcancel]
  ring

/-- The inverse of the minor is given by the explicit formula `minorGreen G i`. -/
theorem inv_minorMat (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0) :
    (minorMat M i)⁻¹ = minorGreen G i :=
  Matrix.inv_eq_left_inv (minorGreen_mul_minorMat hGM i hGii)

/-- The column sum `∑_{l ≠ i} G^(i)_{kl} M_{li} = -G_{ki} / G_{ii}`. -/
theorem sum_minorGreen_col (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0)
    (k : {a : n // a ≠ i}) :
    ∑ l : {a : n // a ≠ i}, minorGreen G i k l * M l.1 i = -(G k.1 i / G i i) := by
  have hsplit : ∑ l : {a : n // a ≠ i}, minorGreen G i k l * M l.1 i
      = (∑ l : {a : n // a ≠ i}, G k.1 l.1 * M l.1 i)
        - (G k.1 i / G i i) * ∑ l : {a : n // a ≠ i}, G i l.1 * M l.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [minorGreen_apply]
    ring
  rw [hsplit, sum_ne_green_mul hGM i k.1 i, sum_ne_green_mul hGM i i i,
    ite_eq_right k.2, ite_eq_left rfl]
  field_simp
  ring

/-- The Schur complement formula for the diagonal entry of an inverse matrix:
`G_ii = (M_ii - ∑_{k,l ≠ i} M_ik G^(i)_kl M_li)⁻¹`. -/
theorem green_diag_eq (hGM : G * M = 1) (hMG : M * G = 1) (i : n) (hGii : G i i ≠ 0) :
    G i i = (M i i - ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        M i k.1 * minorGreen G i k l * M l.1 i)⁻¹ := by
  have hinner : ∀ k : {a : n // a ≠ i},
      (∑ l : {a : n // a ≠ i}, M i k.1 * minorGreen G i k l * M l.1 i)
        = M i k.1 * -(G k.1 i / G i i) := by
    intro k
    rw [← sum_minorGreen_col hGM i hGii k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have hstep : (∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
      M i k.1 * minorGreen G i k l * M l.1 i)
      = ∑ k : {a : n // a ≠ i}, M i k.1 * -(G k.1 i / G i i) :=
    Finset.sum_congr rfl fun k _ => hinner k
  have hcol : ∑ k : {a : n // a ≠ i}, M i k.1 * G k.1 i = 1 - M i i * G i i := by
    rw [sum_ne_mul_green hMG i i i, ite_eq_left rfl]
  have houter : ∑ k : {a : n // a ≠ i}, M i k.1 * -(G k.1 i / G i i)
      = -(1 / G i i) * (1 - M i i * G i i) := by
    rw [← hcol, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hval : M i i - -(1 / G i i) * (1 - M i i * G i i) = (G i i)⁻¹ := by
    field_simp
    ring
  rw [hstep, houter, hval, inv_inv]

/-- Row `i` of `M * minorGreen G i`: `∑_{k ≠ i} M_ik G^(i)_{kj} = -G_ij / G_ii` for `j ≠ i`. -/
private theorem sum_mul_minorGreen_row (hMG : M * G = 1) (i : n) (hGii : G i i ≠ 0)
    (j : {a : n // a ≠ i}) :
    ∑ k : {a : n // a ≠ i}, M i k.1 * minorGreen G i k j = -(G i j.1 / G i i) := by
  have hij : (i : n) ≠ j.1 := fun h => j.2 h.symm
  have hsplit : ∑ k : {a : n // a ≠ i}, M i k.1 * minorGreen G i k j
      = (∑ k : {a : n // a ≠ i}, M i k.1 * G k.1 j.1)
        - (G i j.1 / G i i) * ∑ k : {a : n // a ≠ i}, M i k.1 * G k.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [minorGreen_apply]
    ring
  rw [hsplit, sum_ne_mul_green hMG i i j.1, sum_ne_mul_green hMG i i i, ite_eq_right hij,
    ite_eq_left rfl]
  field_simp
  ring

end Field

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} {z : ℂ}

omit [Fintype n] in
theorem sub_smul_one_apply_self (H : Matrix n n ℂ) (z : ℂ) (i : n) :
    (H - z • (1 : Matrix n n ℂ)) i i = H i i - z := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]

omit [Fintype n] in
theorem sub_smul_one_apply_ne (H : Matrix n n ℂ) (z : ℂ) {i k : n} (h : i ≠ k) :
    (H - z • (1 : Matrix n n ℂ)) i k = H i k := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h]

omit [Fintype n] in
/-- The minor of `H - z` is `H^(i) - z`. -/
theorem minorMat_sub_smul_one (H : Matrix n n ℂ) (z : ℂ) (i : n) :
    minorMat (H - z • (1 : Matrix n n ℂ)) i
      = H.submatrix Subtype.val Subtype.val - z • 1 := by
  ext j k
  by_cases h : j = k
  · subst h
    simp [minorMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · have h' : j.1 ≠ k.1 := fun hh => h (Subtype.ext hh)
    simp [minorMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h,
      Matrix.one_apply_ne h']

/-- The diagonal entries of the Green function of a Hermitian matrix are nonzero for
`0 < Im z`: by the Ward identity ([I, Lemma 5.5]), `G_ii = 0` would force row `i` of `G` to
vanish, contradicting `G (H - z) = 1`. -/
theorem green_diag_ne_zero (hH : H.IsHermitian) (hz : 0 < z.im) (i : n) :
    green H z i i ≠ 0 := by
  intro h0
  have hward := sum_norm_sq_green_row hH hz i
  rw [h0] at hward
  simp only [Complex.zero_im, zero_div] at hward
  have hrow : ∀ y, green H z i y = 0 := by
    intro y
    have hnn : ∀ y ∈ (Finset.univ : Finset n), 0 ≤ ‖green H z i y‖ ^ 2 :=
      fun y _ => by positivity
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hward y (Finset.mem_univ y)
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
  have h1 := congrArg (fun X : Matrix n n ℂ => X i i) (green_mul_sub hH hz.ne')
  simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

/-- `G^(i) = (H^(i) - z)⁻¹` is given by `minorGreen (green H z) i` ([II, §4.4]). -/
theorem inv_minor_resolvent (hH : H.IsHermitian) (hz : 0 < z.im) (i : n) :
    (H.submatrix Subtype.val Subtype.val - z • (1 : Matrix {a : n // a ≠ i} _ ℂ))⁻¹
      = minorGreen (green H z) i := by
  rw [← minorMat_sub_smul_one H z i]
  exact inv_minorMat (green_mul_sub hH hz.ne') i (green_diag_ne_zero hH hz i)

/-- The Schur complement formula for the diagonal Green function entry:
`G_ii = (h_ii - z - ∑_{k,l ≠ i} h_ik G^(i)_kl h_li)⁻¹`. -/
theorem green_diag_schur (hH : H.IsHermitian) (hz : 0 < z.im) (i : n) :
    green H z i i = (H i i - z - ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        H i k.1 * minorGreen (green H z) i k l * H l.1 i)⁻¹ := by
  have hsum : (∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        (H - z • (1 : Matrix n n ℂ)) i k.1 * minorGreen (green H z) i k l
          * (H - z • (1 : Matrix n n ℂ)) l.1 i)
      = ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        H i k.1 * minorGreen (green H z) i k l * H l.1 i := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hik : (i : n) ≠ k.1 := fun hh => k.2 hh.symm
    have hli : l.1 ≠ (i : n) := l.2
    rw [sub_smul_one_apply_ne H z hik, sub_smul_one_apply_ne H z hli]
  rw [green_diag_eq (green_mul_sub hH hz.ne') (sub_mul_green hH hz.ne') i
    (green_diag_ne_zero hH hz i), sub_smul_one_apply_self H z i, hsum]

/-- For `j ≠ i`: `G_ij = -G_ii ∑_{k ≠ i} h_ik G^(i)_kj`. -/
theorem green_offdiag_eq (hH : H.IsHermitian) (hz : 0 < z.im) {i j : n} (hji : j ≠ i) :
    green H z i j
      = -(green H z i i) * ∑ k : {a : n // a ≠ i}, H i k.1 * minorGreen (green H z) i k ⟨j, hji⟩ := by
  have hGii := green_diag_ne_zero hH hz i
  have hsum : (∑ k : {a : n // a ≠ i},
        (H - z • (1 : Matrix n n ℂ)) i k.1 * minorGreen (green H z) i k ⟨j, hji⟩)
      = ∑ k : {a : n // a ≠ i}, H i k.1 * minorGreen (green H z) i k ⟨j, hji⟩ := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hik : (i : n) ≠ k.1 := fun hh => k.2 hh.symm
    rw [sub_smul_one_apply_ne H z hik]
  rw [← hsum, sum_mul_minorGreen_row (sub_mul_green hH hz.ne') i hGii ⟨j, hji⟩]
  field_simp

end Resolvent

section Core

/-- The entries `G^(i)_{kl}` of the resolvent minor, written on the full index set:
`G_{kl} - G_{ki} G_{il} / G_{ii}`. For `k, l ≠ i` this is `minorGreen G i k l`. -/
noncomputable def greenMinor {n : Type*} (G : Matrix n n ℂ) (i k l : n) : ℂ :=
  G k l - G k i * G i l / G i i

theorem minorGreen_eq_greenMinor {n : Type*} (G : Matrix n n ℂ) (i : n) (k l : {a : n // a ≠ i}) :
    minorGreen G i k l = greenMinor G i k.1 l.1 := rfl

/-- [II, (4.17)]. -/
theorem green_eq_greenMinor_add {n : Type*} (G : Matrix n n ℂ) (i k l : n) :
    G k l = greenMinor G i k l + G k i * G i l / G i i := by
  rw [greenMinor]; ring

end Core

end RBM8D
