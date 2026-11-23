module

public import RBM8D.Kernel.ThetaDecay
public import RBM8D.Kernel.Decay

@[expose] public section

/-!
# Torus versus `ℤ^d`

[I, Claim 7.8], [I, Lemma 7.2] (7.8) and (Theta-wh), and [I, (7.5)] as a theorem.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

/-! ## The semicircle law: `m(z)` against `m(E)` -/

section Semicircle

/-- `η |m|² = Im m (1 - |m|²)` for `m = m(z)`, from `m (m + z) = -1`. -/
private theorem InfLimit_im_identity (z : ℂ) :
    z.im * ‖msc z‖ ^ 2 = (msc z).im * (1 - ‖msc z‖ ^ 2) := by
  have h := msc_mul z
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.one_re, Complex.one_im] at h1 h2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  linear_combination (-(msc z).im) * h1 + (msc z).re * h2

/-- `1 - |m(z)|² ≥ η/2` for `0 < η ≤ 1`. -/
private theorem InfLimit_one_sub_ge {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    z.im / 2 ≤ 1 - ‖msc z‖ ^ 2 := by
  have hid := InfLimit_im_identity z
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hm0 : 0 ≤ ‖msc z‖ := norm_nonneg _
  have him : (msc z).im ≤ ‖msc z‖ := Complex.im_le_norm _
  have him0 : 0 < (msc z).im := msc_im_pos hz
  set a := ‖msc z‖ ^ 2 with ha
  have ha1 : a < 1 := by rw [ha]; nlinarith
  have ha0 : 0 ≤ a := by positivity
  rcases le_or_gt (1 / 2) a with h | h
  · have : z.im * a ≤ 1 - a := by
      rw [hid]
      have : (msc z).im ≤ 1 := by linarith
      nlinarith
    nlinarith
  · linarith

/-- `|m(z)|² < 1` for `η > 0`. -/
private theorem InfLimit_sq_lt_one {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ ^ 2 < 1 := by
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hm0 : 0 ≤ ‖msc z‖ := norm_nonneg _
  nlinarith

/-- `|m(E + iη) - m(E)| ≤ η / Im m(E)` for `|E| < 2`, `η > 0`: from
`(m - m_E)(m + m_E + E) = -iη m` and `Im (m + m_E + E) ≥ Im m_E`. -/
private theorem InfLimit_msc_sub_mE {z : ℂ} (hz : 0 < z.im) (hE : |z.re| < 2) :
    ‖msc z - mE z.re‖ ≤ z.im / (mE z.re).im := by
  set m := msc z with hm
  set e := mE z.re with he
  have hm1 : ‖m‖ < 1 := norm_msc_lt_one hz
  have hmi : 0 < m.im := msc_im_pos hz
  have hei : 0 < e.im := mE_im_pos hE
  have hmz := msc_mul z
  have hme := mE_mul hE.le
  rw [← hm] at hmz
  rw [← he] at hme
  have hzE : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  have key : (m - e) * (m + e + (z.re : ℂ)) = -((z.im : ℂ) * I) * m := by
    rw [hzE] at hmz
    linear_combination hmz - hme
  have hq : e.im ≤ ‖m + e + (z.re : ℂ)‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
    rw [abs_of_pos (by linarith)]
    linarith
  have hq0 : 0 < ‖m + e + (z.re : ℂ)‖ := lt_of_lt_of_le hei hq
  have h1 := congrArg norm key
  rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hz] at h1
  rw [le_div_iff₀ hei]
  have : ‖m - e‖ * e.im ≤ ‖m - e‖ * ‖m + e + (z.re : ℂ)‖ :=
    mul_le_mul_of_nonneg_left hq (norm_nonneg _)
  nlinarith [norm_nonneg m]

/-- `Im m(E) ≥ √(2κ)/2` for `|E| < 2 - κ`. -/
private theorem InfLimit_mE_im_ge {κ E : ℝ} (hκ : 0 < κ) (hE : |E| < 2 - κ) :
    Real.sqrt (2 * κ) / 2 ≤ (mE E).im := by
  rw [mE_im]
  gcongr
  have h1 : |E| ^ 2 = E ^ 2 := sq_abs E
  have h0 := abs_nonneg E
  nlinarith

/-- `|m(z)² - m(E)²| ≤ 2 |m(z) - m(E)|` and `1 - |m(z)|² ≤ 2 |m(z) - m(E)|` for `|E| ≤ 2`. -/
private theorem InfLimit_sq_sub_le {z : ℂ} (hz : 0 < z.im) (hE : |z.re| ≤ 2) :
    ‖msc z ^ 2 - mE z.re ^ 2‖ ≤ 2 * ‖msc z - mE z.re‖ ∧
      1 - ‖msc z‖ ^ 2 ≤ 2 * ‖msc z - mE z.re‖ := by
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have he1 : ‖mE z.re‖ = 1 := norm_mE hE
  constructor
  · have e : msc z ^ 2 - mE z.re ^ 2 = (msc z - mE z.re) * (msc z + mE z.re) := by ring
    rw [e, norm_mul]
    have : ‖msc z + mE z.re‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
    nlinarith [norm_nonneg (msc z - mE z.re)]
  · have h1 : 1 - ‖msc z‖ ≤ ‖msc z - mE z.re‖ := by
      have := norm_sub_norm_le (mE z.re) (msc z)
      rw [he1, norm_sub_rev] at this
      linarith
    have h0 := norm_nonneg (msc z)
    nlinarith

end Semicircle

/-! ## Elementary bounds on the symbols -/

section Symbols

/-- `|G_w(t) - G_{w'}(t')| ≤ (|w - w'| |t| + |w'| |t - t'|)/c²` for `G_w(t) = w t/(1 - w t)`,
when `|1 - w t|, |1 - w' t'| ≥ c > 0`. -/
private theorem InfLimit_G_sub_le {w w' t t' : ℂ} {c : ℝ} (hc : 0 < c) (h1 : c ≤ ‖1 - w * t‖)
    (h2 : c ≤ ‖1 - w' * t'‖) :
    ‖w * t / (1 - w * t) - w' * t' / (1 - w' * t')‖ ≤
      (‖w - w'‖ * ‖t‖ + ‖w'‖ * ‖t - t'‖) / c ^ 2 := by
  have hne1 : (1 : ℂ) - w * t ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have hne2 : (1 : ℂ) - w' * t' ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; linarith
  have e : w * t / (1 - w * t) - w' * t' / (1 - w' * t') =
      ((w - w') * t + w' * (t - t')) / ((1 - w * t) * (1 - w' * t')) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul]
  have hnum : ‖(w - w') * t + w' * (t - t')‖ ≤ ‖w - w'‖ * ‖t‖ + ‖w'‖ * ‖t - t'‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  have hden : c ^ 2 ≤ ‖1 - w * t‖ * ‖1 - w' * t'‖ := by
    rw [sq]; exact mul_le_mul h1 h2 hc.le (by positivity)
  calc ‖(w - w') * t + w' * (t - t')‖ / (‖1 - w * t‖ * ‖1 - w' * t'‖)
      ≤ (‖w - w'‖ * ‖t‖ + ‖w'‖ * ‖t - t'‖) / (‖1 - w * t‖ * ‖1 - w' * t'‖) := by gcongr
    _ ≤ (‖w - w'‖ * ‖t‖ + ‖w'‖ * ‖t - t'‖) / c ^ 2 := by
        gcongr

/-- `|1 - w t| ≥ min(δ/4, c′/2)` for real `t ∈ [-1 + c′/2, 1 + e]`, `|w| ≤ 1`, `|1 - w| ≥ δ > 0`
and `e ≤ δ/4`. -/
private theorem InfLimit_one_sub_mul_ge {w : ℂ} (hw : ‖w‖ ≤ 1) {δ c' e : ℝ} (hδ : 0 < δ)
    (hδw : δ ≤ ‖1 - w‖) (hc' : 0 < c') (he : e ≤ δ / 4) {t : ℝ} (ht0 : -1 + c' / 2 ≤ t)
    (ht1 : t ≤ 1 + e) : min (δ / 4) (c' / 2) ≤ ‖1 - w * (t : ℂ)‖ := by
  have hδ2 : δ ≤ 2 := by
    refine hδw.trans ((norm_sub_le _ _).trans ?_)
    rw [norm_one]; linarith
  have hlow : ∀ u : ℝ, 0 ≤ u → u * ‖1 - w‖ - |1 - u| ≤ ‖1 - w * (u : ℂ)‖ := by
    intro u hu
    have e1 : (1 : ℂ) - w * (u : ℂ) = ((1 - u : ℝ) : ℂ) + (u : ℂ) * (1 - w) := by
      push_cast; ring
    rw [e1]
    have h := norm_sub_norm_le ((u : ℂ) * (1 - w)) (-((1 - u : ℝ) : ℂ))
    rw [sub_neg_eq_add, add_comm, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] at h
    linarith
  rcases lt_or_ge t 0 with h0 | h0
  · -- `t < 0`: `|1 - w t| ≥ 1 - |t| ≥ c′/2`
    have h := norm_sub_norm_le (1 : ℂ) (w * (t : ℂ))
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg h0] at h
    have : ‖w‖ * -t ≤ -t := by nlinarith [norm_nonneg w]
    exact (min_le_right _ _).trans (by linarith)
  · rcases le_or_gt t 1 with h1 | h1
    · rcases le_or_gt (δ / 4) (1 - t) with h2 | h2
      · have h := norm_sub_norm_le (1 : ℂ) (w * (t : ℂ))
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at h
        have : ‖w‖ * t ≤ t := by nlinarith [norm_nonneg w]
        exact (min_le_left _ _).trans (by linarith)
      · have h := hlow t h0
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)] at h
        have : t * δ ≤ t * ‖1 - w‖ := mul_le_mul_of_nonneg_left hδw h0
        refine (min_le_left _ _).trans ?_
        nlinarith
    · have h := hlow t h0
      rw [abs_of_neg (by linarith : 1 - t < 0)] at h
      have : t * δ ≤ t * ‖1 - w‖ := mul_le_mul_of_nonneg_left hδw h0
      refine (min_le_left _ _).trans ?_
      nlinarith

end Symbols

/-! ## Kernels on the torus from their symbols -/

section TorusKernel

variable {d L : ℕ}

/-- `|L^{-d} Σ_k f(k) e_k(-x)| ≤ L^{-d} Σ_k |f(k)|`. -/
private theorem InfLimit_norm_avg_le_avg [NeZero L] (f : Zd d L → ℂ) (x : Zd d L) :
    ‖((L : ℂ) ^ d)⁻¹ * ∑ k, f k * zchar k (-x)‖ ≤ ((L : ℝ) ^ d)⁻¹ * ∑ k, ‖f k‖ := by
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, norm_zchar, mul_one]

/-- A translation-invariant kernel is `K_{0x} = L^{-d} Σ_k K̂(k) e_k(-x)`. -/
private theorem InfLimit_kernel_eq [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K)
    (x : Zd d L) : K 0 x = ((L : ℂ) ^ d)⁻¹ * ∑ k, symbol K k * zchar k (-x) := by
  rw [kernel_inversion K hK 0 x, zero_sub]

/-- The symbol of a real symmetric translation-invariant kernel is real. -/
private theorem InfLimit_symbol_real [NeZero L] {S : Matrix (Zd d L) (Zd d L) ℝ}
    (hS : IsSymKernel S) (k : Zd d L) :
    symbol (cmat S) k = (((symbol (cmat S) k).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [symbol_cmat_im S hS.symm hS.transInv k])

/-- `S^+_{0x} = L^{-d} Σ_k G_{m²}(Ŝ(k)) e_k(-x)` when `m² Ŝ(k) ≠ 1` for every `k`. -/
private theorem InfLimit_Splus_eq [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS : IsSymKernel S) (m : ℂ) (hm : ∀ k, m ^ 2 * symbol (cmat S) k ≠ 1) (x : Zd d L) :
    Splus m S 0 x = ((L : ℂ) ^ d)⁻¹ * ∑ k, m ^ 2 * symbol (cmat S) k /
      (1 - m ^ 2 * symbol (cmat S) k) * zchar k (-x) := by
  rw [InfLimit_kernel_eq _ (TransInv_propagators S hS.transInv m).1 x]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [symbol_Splus S hS.transInv m hm k]

end TorusKernel

/-! ## Consequences of `(W, L) ∈ adm(c₀, c₁)` and `z ∈ 𝐃(κ, ε)` -/

section Window

variable {d L : ℕ}

/-- `1 ≤ L`, `W ≤ L`, `L^{c₁} ≤ W` and `η ≥ L^{-2}`, `0 < η ≤ 1` for `(W, L) ∈ adm(c₀, c₁)`,
`W ≥ 1`, `z ∈ 𝐃(κ, ε)`. -/
private theorem InfLimit_window {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hε : 0 < ε) {W L : ℕ}
    [NeZero L] (hadm : (W, L) ∈ adm c₀ c₁) (hW1 : (1 : ℝ) ≤ W) {z : ℂ}
    (hz : z ∈ specDom κ ε W L) :
    (1 : ℝ) ≤ L ∧ (W : ℝ) ≤ L ∧ (L : ℝ) ^ c₁ ≤ W ∧ 1 / (L : ℝ) ^ 2 ≤ z.im ∧ 0 < z.im ∧
      z.im ≤ 1 := by
  obtain ⟨hre, hη, hη1⟩ := hz
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hWL : (W : ℝ) ≤ L := hadm.2.trans (Real.rpow_le_self_of_one_le hL1 (by linarith))
  have hηL : 1 / (L : ℝ) ^ 2 ≤ z.im := by
    refine le_trans ?_ hη
    have h1 : (L : ℝ) ^ (2 - ε) ≤ (L : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    rw [Real.rpow_two] at h1
    have h0 : 0 < (L : ℝ) ^ (2 - ε) := by positivity
    calc 1 / (L : ℝ) ^ 2 ≤ 1 / (L : ℝ) ^ (2 - ε) := one_div_le_one_div_of_le h0 h1
      _ ≤ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) := by gcongr; nlinarith
  exact ⟨hL1, hWL, hadm.1, hηL, lt_of_lt_of_le (by positivity) hηL, hη1⟩

/-- `⟨x⟩ = ‖x‖_L + W ≤ 2L` for `W ≤ L`. -/
private theorem InfLimit_bracket_le [NeZero L] {W : ℕ} (hWL : (W : ℝ) ≤ L) (x : Zd d L) :
    (zdistInf d L x : ℝ) + W ≤ 2 * L := by
  have h1 : zdistInf d L x ≤ L := (zdistInf_le_half d L x).trans (Nat.div_le_self L 2)
  have h2 : (zdistInf d L x : ℝ) ≤ L := by exact_mod_cast h1
  linarith

/-- `(2L)^{-D} ≤ ⟨x⟩^{-D}` for `1 ≤ W ≤ L`, `D ≥ 0`. -/
private theorem InfLimit_two_L_rpow_le [NeZero L] {W : ℕ} (hW1 : (1 : ℝ) ≤ W)
    (hWL : (W : ℝ) ≤ L) {D : ℝ} (hD : 0 ≤ D) (x : Zd d L) :
    2 ^ (-D) * (L : ℝ) ^ (-D) ≤ ((zdistInf d L x : ℝ) + W) ^ (-D) := by
  have hX : 0 < (zdistInf d L x : ℝ) + W := by positivity
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos hX (InfLimit_bracket_le hWL x) (by linarith)

/-- `A L^{-(D+1)} ≤ (2L)^{-D}` for `2^D A ≤ L`, `L > 0`. -/
private theorem InfLimit_absorb {A Lr D : ℝ} (hL : 0 < Lr) (hA : 2 ^ D * A ≤ Lr) :
    A * Lr ^ (-(D + 1)) ≤ 2 ^ (-D) * Lr ^ (-D) := by
  have e : Lr ^ (-D) = Lr ^ (-(D + 1)) * Lr := by
    rw [show -D = -(D + 1) + 1 by ring, Real.rpow_add hL, Real.rpow_one]
  rw [e]
  have h2 : 0 < (2 : ℝ) ^ D := by positivity
  have h3 : (2 : ℝ) ^ (-D) * 2 ^ D = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have h4 : 0 < Lr ^ (-(D + 1)) := by positivity
  have h5 : A ≤ 2 ^ (-D) * Lr := by
    calc A = 2 ^ (-D) * (2 ^ D * A) := by rw [← mul_assoc, h3, one_mul]
      _ ≤ 2 ^ (-D) * Lr := by gcongr
  calc A * Lr ^ (-(D + 1)) ≤ 2 ^ (-D) * Lr * Lr ^ (-(D + 1)) := by gcongr
    _ = 2 ^ (-D) * (Lr ^ (-(D + 1)) * Lr) := by ring

/-- `L^{e} ≤ W^{n}` for `L^{c₁} ≤ W`, `e ≤ c₁ n`, `1 ≤ L`. -/
private theorem InfLimit_L_rpow_le_W_pow {Lr Wr c₁ e : ℝ} (hc₁ : 0 < c₁) (hL1 : 1 ≤ Lr)
    (hLc : Lr ^ c₁ ≤ Wr) {n : ℕ} (hn : e ≤ c₁ * n) : Lr ^ e ≤ Wr ^ n := by
  calc Lr ^ e ≤ Lr ^ (c₁ * n) := Real.rpow_le_rpow_of_exponent_le hL1 hn
    _ = (Lr ^ c₁) ^ n := Real.rpow_mul_natCast (by linarith) _ _
    _ ≤ Wr ^ n := pow_le_pow_left₀ (by positivity) hLc n

/-- `D + 1 ≤ c₁ ⌈(D + 1)/c₁⌉`. -/
private theorem InfLimit_ceil_spec {c₁ X : ℝ} (hc₁ : 0 < c₁) : X ≤ c₁ * (⌈X / c₁⌉₊ : ℕ) := by
  have := Nat.le_ceil (X / c₁)
  rw [div_le_iff₀ hc₁] at this
  linarith

end Window

/-! ## Lifts and periodisation -/

section Lift

variable {d L : ℕ}

/-- `|[x]_L|_∞ = ‖x‖_L`. -/
private theorem InfLimit_zdInf_zlift [NeZero L] (x : Zd d L) :
    zdInf (zlift x) = zdistInf d L x := by
  simp only [zdInf, zlift, zdistInf, zdist_eq_natAbs_valMinAbs]

/-- The `ℓ^∞` norm of a nonzero point of `ℤ^d` is positive. -/
private theorem InfLimit_zdInf_pos {n : Fin d → ℤ} (hn : n ≠ 0) : 0 < zdInf n := by
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have : (n j).natAbs ≤ zdInf n := Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ j)
  have : 0 < (n j).natAbs := Int.natAbs_pos.mpr hj
  omega

/-- The weight `|n|_∞^{-M}` is summable over `ℤ^d` for `M > d` (and vanishes at `n = 0`). -/
private theorem InfLimit_summable_zdInf_inv_pow (d M : ℕ) (hM : d < M) :
    Summable fun n : Fin d → ℤ => (((zdInf n : ℕ) : ℝ) ^ M)⁻¹ := by
  let Λ : Submodule ℤ (Fin d → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))
  have hΛ : ∀ n : Fin d → ℤ, (fun i => (n i : ℝ)) ∈ Λ := by
    intro n
    refine ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ _).mpr fun i => ⟨n i, ?_⟩
    simp
  let g : (Fin d → ℤ) → Λ := fun n => ⟨fun i => (n i : ℝ), hΛ n⟩
  have hg : Function.Injective g := by
    intro a b hab
    funext i
    have := congrFun (congrArg Subtype.val hab) i
    simp only [g] at this
    exact_mod_cast this
  have hrank : Module.finrank ℤ Λ = d := by
    rw [ZLattice.rank ℝ Λ]
    simp
  have hs := ZLattice.summable_norm_rpow Λ (-(M : ℝ))
    (by rw [hrank]; exact_mod_cast (by omega : -(M : ℤ) < -d))
  have hcomp := hs.comp_injective hg
  refine hcomp.congr fun n => ?_
  have hnorm : ‖g n‖ = ((zdInf n : ℕ) : ℝ) := by
    have h1 : ‖g n‖ = ‖(fun i => (n i : ℝ))‖ := rfl
    rw [h1]
    refine le_antisymm ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr fun i => ?_
      rw [Real.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs]
      exact_mod_cast Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ i)
    · refine (Nat.floor_le (norm_nonneg _)).trans' ?_
      refine Nat.cast_le.mpr (Finset.sup_le fun i _ => Nat.le_floor ?_)
      have h2 : (((n i).natAbs : ℕ) : ℝ) = ‖(n i : ℝ)‖ := by simp
      rw [h2]
      exact norm_le_pi_norm (fun i => (n i : ℝ)) i
  simp only [Function.comp, hnorm]
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]

/-- A kernel on `ℤ^d` with `|f(z)| ≤ A (1 + |z|_∞/R)^{-M}`, `M > d`, is absolutely summable. -/
private theorem InfLimit_summable_of_le {f : (Fin d → ℤ) → ℂ} {A R : ℝ} {M : ℕ} (hM : d < M)
    (hR : 0 < R) (hf : ∀ z, ‖f z‖ ≤ A * ((1 + (zdInf z : ℝ) / R) ^ M)⁻¹) :
    Summable fun z => ‖f z‖ := by
  have hs := (InfLimit_summable_zdInf_inv_pow d M hM).mul_left (|A| * R ^ M)
  refine Summable.of_norm_bounded_eventually hs ?_
  refine (Filter.eventually_cofinite_ne 0).mono fun z hz0 => ?_
  have hpos : (0 : ℝ) < zdInf z := by exact_mod_cast InfLimit_zdInf_pos hz0
  rw [norm_norm]
  refine (hf z).trans ?_
  have h1 : ((zdInf z : ℝ) / R) ^ M ≤ (1 + (zdInf z : ℝ) / R) ^ M :=
    pow_le_pow_left₀ (by positivity) (by linarith) M
  have h2 : ((1 + (zdInf z : ℝ) / R) ^ M)⁻¹ ≤ (((zdInf z : ℝ) / R) ^ M)⁻¹ :=
    inv_anti₀ (by positivity) h1
  calc A * ((1 + (zdInf z : ℝ) / R) ^ M)⁻¹ ≤ |A| * ((1 + (zdInf z : ℝ) / R) ^ M)⁻¹ := by
        gcongr; exact le_abs_self A
    _ ≤ |A| * (((zdInf z : ℝ) / R) ^ M)⁻¹ := by gcongr
    _ = |A| * R ^ M * (((zdInf z : ℕ) : ℝ) ^ M)⁻¹ := by
        rw [div_pow]; field_simp

/-- `‖Σ_n K([x]_L + L n) - K([x]_L)‖ ≤ Σ_{n ≠ 0} b(n)` for `‖K([x]_L + L n)‖ ≤ b(n)`,
`n ≠ 0`. -/
private theorem InfLimit_periodize_sub_le [NeZero L] (K : (Fin d → ℤ) → ℂ)
    (hK : Summable fun z => ‖K z‖) (x : Zd d L) (b : {n : Fin d → ℤ // n ≠ 0} → ℝ)
    (hb : Summable b) (hKb : ∀ n : {n : Fin d → ℤ // n ≠ 0}, ‖K (zlift x + (L : ℤ) • n.1)‖ ≤ b n) :
    ‖periodize L K x - K (zlift x)‖ ≤ ∑' n, b n := by
  have hinj : Function.Injective fun n : Fin d → ℤ => zlift x + (L : ℤ) • n := by
    intro n₁ n₂ h
    have hL' : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
    funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
    exact mul_left_cancel₀ hL' this
  set f : (Fin d → ℤ) → ℂ := fun n => K (zlift x + (L : ℤ) • n) with hfdef
  have hf : Summable fun n => ‖f n‖ := hK.comp_injective hinj
  have hsplit := hf.of_norm.tsum_subtype_add_tsum_subtype_compl {0}
  rw [tsum_singleton (0 : Fin d → ℤ) f] at hsplit
  have hf0 : f 0 = K (zlift x) := by simp [hfdef]
  unfold periodize
  rw [← hfdef, ← hsplit, hf0, add_sub_cancel_left]
  have hf' : Summable fun n : {n : Fin d → ℤ // n ≠ 0} => ‖f n.1‖ := hf.subtype _
  calc ‖∑' n : ↑(({0} : Set (Fin d → ℤ))ᶜ), f n‖ ≤ ∑' n : ↑(({0} : Set (Fin d → ℤ))ᶜ), ‖f n‖ :=
        norm_tsum_le_tsum_norm (hf.subtype _)
    _ = ∑' n : {n : Fin d → ℤ // n ≠ 0}, ‖f n.1‖ := rfl
    _ ≤ ∑' n, b n := hf'.tsum_le_tsum hKb hb

/-- Termwise bound for `n ≠ 0`:
`(1 + |[x]_L + L n|/R)^{-M} ≤ 2^M (R/L)^M |n|_∞^{-M}`. -/
private theorem InfLimit_term_le [NeZero L] (M : ℕ) (R : ℝ) (hR : 0 < R) (x : Zd d L)
    (n : Fin d → ℤ) (hn : n ≠ 0) :
    ((1 + (zdInf (zlift x + (L : ℤ) • n) : ℝ) / R) ^ M)⁻¹ ≤
      2 ^ M * (R / L) ^ M * (((zdInf n : ℕ) : ℝ) ^ M)⁻¹ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have ha : (0 : ℝ) < ((zdInf n : ℕ) : ℝ) := by exact_mod_cast InfLimit_zdInf_pos hn
  have hge : (L : ℝ) * ((zdInf n : ℕ) : ℝ) ≤ 2 * ((zdInf (zlift x + (L : ℤ) • n) : ℕ) : ℝ) := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
      (by
        obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
          by_contra h
          push Not at h
          exact hn (funext h)
        exact ⟨j, Finset.mem_univ j⟩) (fun i => (n i).natAbs)
    have hni : (n i).natAbs = zdInf n := hi.symm
    have hv : 2 * (zlift x i).natAbs ≤ L := by
      have := ZMod.natAbs_valMinAbs_le (x i)
      simp only [zlift]
      omega
    have hle : ((zlift x + (L : ℤ) • n) i).natAbs ≤ zdInf (zlift x + (L : ℤ) • n) :=
      Finset.le_sup (f := fun i => ((zlift x + (L : ℤ) • n) i).natAbs) (Finset.mem_univ i)
    have hn1 : 1 ≤ (n i).natAbs := by rw [hni]; exact InfLimit_zdInf_pos hn
    have hmain : L * (n i).natAbs ≤ 2 * ((zlift x + (L : ℤ) • n) i).natAbs := by
      have e1 : ((zlift x + (L : ℤ) • n) i) = zlift x i + (L : ℤ) * n i := by simp
      rw [e1]
      have e2 : ((L : ℤ) * n i).natAbs = L * (n i).natAbs := by
        rw [Int.natAbs_mul]; simp
      have h3 := Int.natAbs_add_le (zlift x i + (L : ℤ) * n i) (-(zlift x i))
      have e3 : zlift x i + (L : ℤ) * n i + -zlift x i = (L : ℤ) * n i := by ring
      rw [e3, Int.natAbs_neg, e2] at h3
      nlinarith
    have : L * zdInf n ≤ 2 * zdInf (zlift x + (L : ℤ) • n) := by rw [← hni]; omega
    exact_mod_cast this
  set b : ℝ := (L : ℝ) * ((zdInf n : ℕ) : ℝ) / (2 * R) with hb
  have hbpos : 0 < b := by positivity
  have hb1 : b ≤ 1 + (zdInf (zlift x + (L : ℤ) • n) : ℝ) / R := by
    have h1 : b ≤ ((zdInf (zlift x + (L : ℤ) • n) : ℕ) : ℝ) / R := by
      rw [hb, div_le_div_iff₀ (by positivity) hR]
      nlinarith
    have : (0 : ℝ) ≤ 1 := zero_le_one
    linarith
  calc ((1 + (zdInf (zlift x + (L : ℤ) • n) : ℝ) / R) ^ M)⁻¹ ≤ (b ^ M)⁻¹ :=
        inv_anti₀ (pow_pos hbpos M) (pow_le_pow_left₀ hbpos.le hb1 M)
    _ = 2 ^ M * (R / L) ^ M * (((zdInf n : ℕ) : ℝ) ^ M)⁻¹ := by
        have h2 : ((zdInf n : ℕ) : ℝ) = b * 2 * (R / L) := by
          rw [hb]
          field_simp
        have hRL : (0 : ℝ) < R / L := by positivity
        rw [h2, mul_pow, mul_pow]
        field_simp

/-- The terms `(1 + |[x]_L + L n|/R)^{-M}`, `n ≠ 0`, are summable for `M ≥ d + 1`. -/
private theorem InfLimit_term_summable [NeZero L] (M : ℕ) (hM : d + 1 ≤ M) (R : ℝ)
    (hR : 0 < R) (x : Zd d L) :
    Summable fun n : {n : Fin d → ℤ // n ≠ 0} =>
      ((1 + (zdInf (zlift x + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹ := by
  have hs := InfLimit_summable_zdInf_inv_pow d M (by omega)
  have hsub : Summable fun n : {n : Fin d → ℤ // n ≠ 0} => (((zdInf n.1 : ℕ) : ℝ) ^ M)⁻¹ :=
    hs.subtype _
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => InfLimit_term_le M R hR x n.1 n.2) (hsub.mul_left (2 ^ M * (R / L) ^ M))

end Lift

/-! ## Fourier series of the kernels on `ℤ^d` -/

section Series

variable {d : ℕ}

private theorem InfLimit_measurableSet_cubePi : MeasurableSet (cubePi d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

private theorem InfLimit_isCompact_cubePi : IsCompact (cubePi d) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem InfLimit_continuous_zexp (y : Fin d → ℤ) :
    Continuous fun p : Fin d → ℝ => zexp p y := by
  unfold zexp; fun_prop

private theorem InfLimit_integrableOn_mul_zexp {F : (Fin d → ℝ) → ℂ}
    (hF : IntegrableOn F (cubePi d)) (x : Fin d → ℤ) :
    IntegrableOn (fun p => F p * zexp p (-x)) (cubePi d) :=
  hF.mul_continuousOn (InfLimit_continuous_zexp _).continuousOn InfLimit_isCompact_cubePi

private theorem InfLimit_latticeFourier_add {F G : (Fin d → ℝ) → ℂ}
    (hF : IntegrableOn F (cubePi d)) (hG : IntegrableOn G (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => F p + G p) x = latticeFourier F x + latticeFourier G x := by
  unfold latticeFourier
  rw [← mul_add, ← integral_add (InfLimit_integrableOn_mul_zexp hF x)
    (InfLimit_integrableOn_mul_zexp hG x)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only; ring

private theorem InfLimit_latticeFourier_const_mul (c : ℂ) (F : (Fin d → ℝ) → ℂ)
    (x : Fin d → ℤ) : latticeFourier (fun p => c * F p) x = c * latticeFourier F x := by
  unfold latticeFourier
  simp_rw [mul_assoc c]
  rw [integral_const_mul]; ring

private theorem InfLimit_latticeFourier_congr {F G : (Fin d → ℝ) → ℂ}
    (h : ∀ p ∈ cubePi d, F p = G p) (x : Fin d → ℤ) : latticeFourier F x = latticeFourier G x := by
  unfold latticeFourier
  congr 1
  exact setIntegral_congr_fun InfLimit_measurableSet_cubePi fun p hp => by simp only [h p hp]

/-- Multiplying the symbol by the Fourier series of a summable kernel `K` convolves with `K`. -/
private theorem InfLimit_latticeFourier_zdSeries_mul {K : (Fin d → ℤ) → ℂ}
    (hsum : Summable fun y => ‖K y‖) {Φ : (Fin d → ℝ) → ℂ} (hΦ : IntegrableOn Φ (cubePi d))
    (x : Fin d → ℤ) :
    latticeFourier (fun p => zdSeries K p * Φ p) x = ∑' y, K y * latticeFourier Φ (x - y) := by
  unfold latticeFourier
  set F : (Fin d → ℤ) → (Fin d → ℝ) → ℂ := fun y p => K y * (Φ p * zexp p (-(x - y)))
  have hF : ∀ y, Integrable (F y) (volume.restrict (cubePi d)) := fun y =>
    (InfLimit_integrableOn_mul_zexp hΦ (x - y)).const_mul _
  have hnorm : ∀ y, ∫ p in cubePi d, ‖F y p‖ = ‖K y‖ * ∫ p in cubePi d, ‖Φ p‖ := by
    intro y
    simp only [F, norm_mul, norm_zexp, mul_one]
    rw [integral_const_mul]
  have hsumm : Summable fun y => ∫ p in cubePi d, ‖F y p‖ := by
    simp_rw [hnorm]; exact hsum.mul_right _
  have h := integral_tsum_of_summable_integral_norm hF hsumm
  have hpt : ∀ p, zdSeries K p * Φ p * zexp p (-x) = ∑' y, F y p := by
    intro p
    unfold zdSeries
    rw [mul_assoc, ← tsum_mul_right]
    refine tsum_congr fun y => ?_
    simp only [F]
    have : zexp p (-(x - y)) = zexp p y * zexp p (-x) := by
      rw [← zexp_add]; congr 1; abel
    rw [this]; ring
  simp_rw [hpt]
  rw [← h, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  simp only [F]
  rw [integral_const_mul]; ring

/-- The Fourier series of a convolution of summable kernels is the product of their Fourier
series. -/
private theorem InfLimit_zdSeries_conv {K₁ K₂ : (Fin d → ℤ) → ℂ}
    (h₁ : Summable fun y => ‖K₁ y‖) (h₂ : Summable fun y => ‖K₂ y‖) (p : Fin d → ℝ) :
    ∑' x, (∑' y, K₁ y * K₂ (x - y)) * zexp p x = zdSeries K₁ p * zdSeries K₂ p := by
  have hn₁ : Summable fun y => ‖K₁ y * zexp p y‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using h₁
  have hn₂ : Summable fun y => ‖K₂ y * zexp p y‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using h₂
  have hprod := tsum_mul_tsum_of_summable_norm (f := fun y => K₁ y * zexp p y)
    (g := fun y => K₂ y * zexp p y) hn₁ hn₂
  set G : (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun q => K₁ q.1 * zexp p q.1 * (K₂ q.2 * zexp p q.2)
  have hG : Summable G := summable_mul_of_summable_norm (f := fun y => K₁ y * zexp p y)
    (g := fun y => K₂ y * zexp p y) hn₁ hn₂
  set e : (Fin d → ℤ) × (Fin d → ℤ) ≃ (Fin d → ℤ) × (Fin d → ℤ) :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := fun q => by simp
      right_inv := fun q => by simp } with he
  have hGe : Summable (G ∘ e) := e.summable_iff.2 hG
  have hval : ∀ q : (Fin d → ℤ) × (Fin d → ℤ),
      G (e q) = K₁ q.2 * K₂ (q.1 - q.2) * zexp p q.1 := by
    intro q
    simp only [G, he, Equiv.coe_fn_mk]
    have : zexp p q.2 * zexp p (q.1 - q.2) = zexp p q.1 := by rw [← zexp_add]; congr 1; abel
    rw [← this]; ring
  have hGe' : Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      K₁ q.2 * K₂ (q.1 - q.2) * zexp p q.1 := hGe.congr hval
  unfold zdSeries
  rw [hprod, ← e.tsum_eq G, tsum_congr hval, hGe'.tsum_prod]
  refine tsum_congr fun x => ?_
  rw [← tsum_mul_right]

/-- If the kernel `K` with symbol `F = w ŝ/(1 - w ŝ)` is summable, then its Fourier series is
`F` on `[-π, π]^d`; this uses `K = w s + w s * K`. -/
private theorem InfLimit_series {s : (Fin d → ℤ) → ℝ} (hss : Summable s) {K₀ : ℝ}
    (hcd : Continuous (zdSymbol s)) (hK0 : ∀ p, ‖zdSymbol s p‖ ≤ K₀) (w : ℂ)
    (hKs : Summable fun z =>
      ‖latticeFourier (fun p => w * zdSymbol s p / (1 - w * zdSymbol s p)) z‖)
    (hFi : IntegrableOn (fun p => w * zdSymbol s p / (1 - w * zdSymbol s p)) (cubePi d))
    (hden : ∀ p ∈ cubePi d, (1 : ℂ) - w * zdSymbol s p ≠ 0) :
    ∀ p ∈ cubePi d, zdSeries (latticeFourier fun p => w * zdSymbol s p / (1 - w * zdSymbol s p))
      p = w * zdSymbol s p / (1 - w * zdSymbol s p) := by
  set F : (Fin d → ℝ) → ℂ := fun p => w * zdSymbol s p / (1 - w * zdSymbol s p) with hF
  set K : (Fin d → ℤ) → ℂ := latticeFourier F with hK
  have hsn : Summable fun y => ‖((s y : ℝ) : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using summable_abs_iff.2 hss
  have hsym : ∀ p ∈ cubePi d, F p = w * zdSymbol s p + w * (zdSymbol s p * F p) := by
    intro p hp
    have hne := hden p hp
    simp only [hF]
    field_simp
    ring
  have hscont : IntegrableOn (zdSymbol s) (cubePi d) :=
    hcd.continuousOn.integrableOn_compact InfLimit_isCompact_cubePi
  have hsF : IntegrableOn (fun p => zdSymbol s p * F p) (cubePi d) :=
    Integrable.bdd_mul (c := K₀) hFi hcd.aestronglyMeasurable
      (Filter.Eventually.of_forall hK0)
  have hreal : ∀ x, K x = w * (s x : ℂ) + w * ∑' y, (s y : ℂ) * K (x - y) := by
    intro x
    have h1 : K x = latticeFourier (fun p => w * zdSymbol s p + w * (zdSymbol s p * F p)) x :=
      InfLimit_latticeFourier_congr hsym x
    rw [h1, InfLimit_latticeFourier_add (F := fun p => w * zdSymbol s p)
      (G := fun p => w * (zdSymbol s p * F p)) (hscont.const_mul _) (hsF.const_mul _),
      InfLimit_latticeFourier_const_mul, InfLimit_latticeFourier_const_mul
        (F := fun p => zdSymbol s p * F p)]
    have h2 : latticeFourier (zdSymbol s) x = (s x : ℂ) := latticeFourier_zdSeries _ hsn x
    have h3 : latticeFourier (fun p => zdSymbol s p * F p) x =
        ∑' y, (s y : ℂ) * K (x - y) :=
      InfLimit_latticeFourier_zdSeries_mul hsn hFi x
    rw [h2, h3]
  intro p hp
  have hd := hden p hp
  have hsz : Summable fun x => ‖(s x : ℂ) * zexp p x‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using hsn
  have hKz : Summable fun x => ‖K x * zexp p x‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using hKs
  have hsplit : ∀ x, K x * zexp p x = w * ((s x : ℂ) * zexp p x) +
      w * ((∑' y, (s y : ℂ) * K (x - y)) * zexp p x) := fun x => by
    rw [hreal x]; ring
  have hA : Summable fun x => w * ((s x : ℂ) * zexp p x) := hsz.of_norm.mul_left _
  have hB : Summable fun x => w * ((∑' y, (s y : ℂ) * K (x - y)) * zexp p x) :=
    (hKz.of_norm.sub hA).congr fun x => by rw [hsplit x]; ring
  have hconv := InfLimit_zdSeries_conv hsn hKs p
  have hkey : zdSeries K p = w * zdSymbol s p + w * (zdSymbol s p * zdSeries K p) := by
    calc zdSeries K p = ∑' x, K x * zexp p x := rfl
      _ = _ := by
        rw [tsum_congr hsplit, hA.tsum_add hB, tsum_mul_left, tsum_mul_left, hconv]
        rfl
  change zdSeries K p = F p
  simp only [hF]
  rw [eq_div_iff hd]
  linear_combination hkey

end Series

/-! ## A Riemann sum of `|ψ(W·)|` on the torus -/

section Riemann

private theorem InfLimit_sum_range_le (W : ℝ) (hW : 1 ≤ W) (M : ℕ) :
    ∑ n ∈ Finset.range M, ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ ≤ W - W ^ 2 / (W + M) := by
  induction M with
  | zero =>
    have : W ^ 2 / (W + ((0 : ℕ) : ℝ)) = W := by
      rw [Nat.cast_zero, add_zero, sq, mul_div_assoc, div_self (by linarith), mul_one]
    simp only [Finset.range_zero, Finset.sum_empty, this, sub_self, le_refl]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0 : ℝ) ≤ M := M.cast_nonneg
    have key : ((1 + ((M : ℝ) + 1) / W) ^ 2)⁻¹ ≤
        W ^ 2 / (W + M) - W ^ 2 / (W + ((M + 1 : ℕ) : ℝ)) := by
      push_cast
      have h1 : 0 < W + M := by linarith
      have h2 : 0 < W + (M + 1) := by linarith
      have e : ((1 + ((M : ℝ) + 1) / W) ^ 2)⁻¹ = W ^ 2 / (W + (M + 1)) ^ 2 := by
        field_simp
      rw [e, div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg W, mul_pos h1 h2]
    linarith

/-- The one-dimensional weight `(1 + |m|/R)^{-2}`. -/
private def InfLimit_wt (R : ℝ) (m : ℤ) : ℝ := ((1 + |(m : ℝ)| / R) ^ 2)⁻¹

private theorem InfLimit_wt_nonneg (R : ℝ) (hR : 1 ≤ R) (m : ℤ) : 0 ≤ InfLimit_wt R m := by
  unfold InfLimit_wt; have : 0 ≤ |(m : ℝ)| / R := by positivity
  positivity

private theorem InfLimit_summable_wt (R : ℝ) (hR : 1 ≤ R) :
    Summable (InfLimit_wt R) ∧ ∑' m, InfLimit_wt R m ≤ 1 + 2 * R := by
  have hpos : ∀ n : ℕ, 0 ≤ ((1 + ((n : ℝ) + 1) / R) ^ 2)⁻¹ := fun n => by
    have : 0 ≤ ((n : ℝ) + 1) / R := by positivity
    positivity
  have hsr : ∀ n, ∑ i ∈ Finset.range n, ((1 + ((i : ℝ) + 1) / R) ^ 2)⁻¹ ≤ R := fun n => by
    have := InfLimit_sum_range_le R hR n
    have : 0 ≤ R ^ 2 / (R + n) := by positivity
    linarith
  have hA := summable_of_sum_range_le hpos hsr
  have e1 : (fun n : ℕ => InfLimit_wt R ((n + 1 : ℕ) : ℤ)) =
      fun n : ℕ => ((1 + ((n : ℝ) + 1) / R) ^ 2)⁻¹ := by
    funext n; unfold InfLimit_wt; push_cast
    rw [abs_of_nonneg (by positivity)]
  have e2 : (fun n : ℕ => InfLimit_wt R (-((n : ℤ) + 1))) =
      fun n : ℕ => ((1 + ((n : ℝ) + 1) / R) ^ 2)⁻¹ := by
    funext n; unfold InfLimit_wt; push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hnat : Summable fun n : ℕ => InfLimit_wt R n := by
    rw [← summable_nat_add_iff 1]
    exact_mod_cast (e1 ▸ hA : Summable fun n : ℕ => InfLimit_wt R ((n + 1 : ℕ) : ℤ))
  have hneg : Summable fun n : ℕ => InfLimit_wt R (-((n : ℤ) + 1)) := by rw [e2]; exact hA
  refine ⟨hnat.of_nat_of_neg_add_one hneg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add, e2]
  have e0 : InfLimit_wt R ((0 : ℕ) : ℤ) = 1 := by simp [InfLimit_wt]
  have e1' : (∑' n : ℕ, InfLimit_wt R ((n + 1 : ℕ) : ℤ)) =
      ∑' n : ℕ, ((1 + ((n : ℝ) + 1) / R) ^ 2)⁻¹ := by
    rw [e1]
  rw [e0, e1']
  have := Real.tsum_le_of_sum_range_le hpos hsr
  linarith

/-- `Σ_{u ∈ ℤ/L} (1 + |u|/R)^{-2} ≤ 3R` for `R ≥ 1`, with `|u|` the centred representative. -/
private theorem InfLimit_sum_zmod_wt_le (L : ℕ) [NeZero L] (R : ℝ) (hR : 1 ≤ R) :
    ∑ u : ZMod L, InfLimit_wt R u.valMinAbs ≤ 3 * R := by
  obtain ⟨hs, hB⟩ := InfLimit_summable_wt R hR
  have hinj : Set.InjOn (fun u : ZMod L => u.valMinAbs) (Finset.univ : Finset (ZMod L)) :=
    fun a _ b _ h => ZMod.valMinAbs_inj.mp h
  rw [← Finset.sum_image (f := InfLimit_wt R) hinj]
  refine (hs.sum_le_tsum _ fun m _ => InfLimit_wt_nonneg R hR m).trans ?_
  linarith

/-- The Riemann sum `L^{-d} Σ_k |ψ(W p_k)|` over the frequencies of `T_L^d` is `O(W^{-d})`,
uniformly in `1 ≤ W ≤ L`. -/
private theorem InfLimit_riemann {d : ℕ} (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (W L : ℕ) [NeZero L], (1 : ℝ) ≤ W → (W : ℝ) ≤ L →
      ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, |ψ ((W : ℝ) • zfreq k)| ≤ A / (W : ℝ) ^ d := by
  set A₀ : ℝ := 2 ^ (2 * d) *
    ((Finset.Iic (2 * d, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ with hA₀
  have hA : ∀ q, (1 + ‖q‖) ^ (2 * d) * |ψ q| ≤ A₀ := fun q => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2 * d, 0)) (k := 2 * d)
      (n := 0) le_rfl le_rfl ψ q
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hA0 : 0 ≤ A₀ := (mul_nonneg (by positivity) (abs_nonneg _)).trans (hA 0)
  refine ⟨A₀ * 3 ^ d, by positivity, ?_⟩
  intro W L _ hW1 hWL
  have hW0 : (0 : ℝ) < W := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  set R : ℝ := L / W with hR
  have hR1 : 1 ≤ R := by rw [hR, le_div_iff₀ hW0]; linarith
  have hpt : ∀ k : Zd d L, |ψ ((W : ℝ) • zfreq k)| ≤
      A₀ * ∏ i, InfLimit_wt R (k i).valMinAbs := by
    intro k
    set N : ℝ := ‖(W : ℝ) • zfreq k‖ with hN
    have hcomp : ∀ i, (1 + |((k i).valMinAbs : ℝ)| / R) ^ 2 ≤ (1 + N) ^ 2 := by
      intro i
      have h1 : ‖((W : ℝ) • zfreq k) i‖ ≤ N := PiLp.norm_apply_le _ i
      have e : ((W : ℝ) • zfreq k) i = (W : ℝ) * (2 * Real.pi * ((k i).valMinAbs : ℝ) / L) := by
        simp [zfreq]
      rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos hW0, abs_div, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hL0] at h1
      have h2 : |((k i).valMinAbs : ℝ)| / R ≤ N := by
        refine le_trans ?_ h1
        have hp : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
        have hv := abs_nonneg ((k i).valMinAbs : ℝ)
        have e2 : |((k i).valMinAbs : ℝ)| / R = (W : ℝ) * (|((k i).valMinAbs : ℝ)| / L) := by
          rw [hR]; field_simp
        rw [e2]
        gcongr
        nlinarith
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hprod : ∏ i, (1 + |((k i).valMinAbs : ℝ)| / R) ^ 2 ≤ (1 + N) ^ (2 * d) := by
      calc ∏ i, (1 + |((k i).valMinAbs : ℝ)| / R) ^ 2 ≤ ∏ _i : Fin d, (1 + N) ^ 2 :=
            Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => hcomp i
        _ = (1 + N) ^ (2 * d) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    have hp0 : 0 < ∏ i, (1 + |((k i).valMinAbs : ℝ)| / R) ^ 2 :=
      Finset.prod_pos fun i _ => by positivity
    have e : ∏ i, InfLimit_wt R (k i).valMinAbs =
        (∏ i, (1 + |((k i).valMinAbs : ℝ)| / R) ^ 2)⁻¹ := by
      simp only [InfLimit_wt, Finset.prod_inv_distrib]
    rw [e, ← div_eq_mul_inv, le_div_iff₀ hp0]
    calc |ψ ((W : ℝ) • zfreq k)| * ∏ i, (1 + |((k i).valMinAbs : ℝ)| / R) ^ 2
        ≤ |ψ ((W : ℝ) • zfreq k)| * (1 + N) ^ (2 * d) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ ≤ A₀ := by rw [mul_comm]; exact hA _
  have hsum : ∑ k : Zd d L, ∏ i, InfLimit_wt R (k i).valMinAbs =
      ∏ _i : Fin d, ∑ u : ZMod L, InfLimit_wt R u.valMinAbs := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have h1 : ∑ k : Zd d L, |ψ ((W : ℝ) • zfreq k)| ≤ A₀ * (3 * R) ^ d := by
    calc ∑ k : Zd d L, |ψ ((W : ℝ) • zfreq k)| ≤
          ∑ k : Zd d L, A₀ * ∏ i, InfLimit_wt R (k i).valMinAbs :=
          Finset.sum_le_sum fun k _ => hpt k
      _ = A₀ * ∏ _i : Fin d, ∑ u : ZMod L, InfLimit_wt R u.valMinAbs := by
          rw [← Finset.mul_sum, hsum]
      _ ≤ A₀ * ∏ _i : Fin d, (3 * R) := by
          gcongr with i
          · exact fun i _ => Finset.sum_nonneg fun u _ => InfLimit_wt_nonneg R hR1 _
          · exact InfLimit_sum_zmod_wt_le L R hR1
      _ = A₀ * (3 * R) ^ d := by simp
  calc ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, |ψ ((W : ℝ) • zfreq k)| ≤ ((L : ℝ) ^ d)⁻¹ *
        (A₀ * (3 * R) ^ d) := by gcongr
    _ = A₀ * 3 ^ d / (W : ℝ) ^ d := by
        rw [hR, mul_pow, div_pow]; field_simp

end Riemann

/-! ## Exponent bookkeeping -/

section Bookkeeping

/-- `R/L ≤ 2 L^{-ε/2}` for `R = W/σ`, `σ² ≥ W²/(2 L^{2-ε})`. -/
private theorem InfLimit_R_div_L_le {Lr Wr σ ε : ℝ} (hL1 : 1 ≤ Lr) (hW : 0 < Wr) (hσ : 0 < σ)
    (hσ2 : Wr ^ 2 / Lr ^ (2 - ε) / 2 ≤ σ ^ 2) : Wr / σ / Lr ≤ 2 * Lr ^ (-(ε / 2)) := by
  have hL0 : 0 < Lr := by linarith
  have hq0 : 0 ≤ Wr / σ / Lr := by positivity
  have h2 : 0 ≤ 2 * Lr ^ (-(ε / 2)) := by positivity
  refine (pow_le_pow_iff_left₀ hq0 h2 (two_ne_zero)).mp ?_
  have e1 : (2 * Lr ^ (-(ε / 2))) ^ 2 = 4 * Lr ^ (-ε) := by
    rw [mul_pow, ← Real.rpow_natCast (Lr ^ (-(ε / 2))), ← Real.rpow_mul hL0.le]
    norm_num
  have e2 : Lr ^ (2 - ε) = Lr ^ 2 * Lr ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hL0, Real.rpow_two]
  rw [e2, div_div, div_le_iff₀ (by positivity)] at hσ2
  have hLe : 0 < Lr ^ (-ε) := by positivity
  rw [e1, div_pow, div_pow, div_div, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg σ, sq_nonneg Lr]

/-- `(R/L)^M ≤ 2^M L^{-(D+1)}` for `R/L ≤ 2 L^{-e}`, `D + 1 ≤ e M`. -/
private theorem InfLimit_RL_pow_le {Lr q e D : ℝ} (hL1 : 1 ≤ Lr) (hq : 0 ≤ q)
    (hqL : q ≤ 2 * Lr ^ (-e)) {M : ℕ} (hM : D + 1 ≤ e * M) :
    q ^ M ≤ 2 ^ M * Lr ^ (-(D + 1)) := by
  have hL0 : 0 < Lr := by linarith
  calc q ^ M ≤ (2 * Lr ^ (-e)) ^ M := pow_le_pow_left₀ hq hqL M
    _ = 2 ^ M * Lr ^ (-e * M) := by rw [mul_pow, Real.rpow_mul_natCast hL0.le]
    _ ≤ 2 ^ M * Lr ^ (-(D + 1)) := by
        gcongr
        linarith

/-- `2 L^{-ε/2} ≤ 1` for `L ≥ 2^{2/ε}`. -/
private theorem InfLimit_two_rpow_le_one {Lr ε : ℝ} (hε : 0 < ε) (hL : (2 : ℝ) ^ (2 / ε) ≤ Lr) :
    2 * Lr ^ (-(ε / 2)) ≤ 1 := by
  have h0 : 0 < (2 : ℝ) ^ (2 / ε) := by positivity
  have hL0 : 0 < Lr := lt_of_lt_of_le h0 hL
  have h1 : (2 : ℝ) ≤ Lr ^ (ε / 2) := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul (by norm_num), show 2 / ε * (ε / 2) = 1 by field_simp,
            Real.rpow_one]
      _ ≤ Lr ^ (ε / 2) := Real.rpow_le_rpow h0.le hL (by positivity)
  rw [Real.rpow_neg hL0.le]
  have : 0 < Lr ^ (ε / 2) := by positivity
  rw [← div_eq_mul_inv, div_le_one this]
  exact h1

/-- `A ≤ W^τ` for `W ≥ A^{1/τ}`. -/
private theorem InfLimit_le_rpow {A Wr τ : ℝ} (hτ : 0 < τ) (hA : 0 ≤ A)
    (hW : A ^ (1 / τ) ≤ Wr) : A ≤ Wr ^ τ := by
  calc A = (A ^ (1 / τ)) ^ τ := by
        rw [← Real.rpow_mul hA, show 1 / τ * τ = 1 by field_simp, Real.rpow_one]
    _ ≤ Wr ^ τ := Real.rpow_le_rpow (by positivity) hW hτ.le

/-- `W^{-d} 1(y ≤ W^{1+τ}) + (y + W)^{-M} ≤ (2^M W^{τM} + 1)(1 + y/W)^{-M}` for `W ≥ 1`. -/
private theorem InfLimit_decay_weight {d : ℕ} {Wr y τ : ℝ} (hW : 1 ≤ Wr) (hy : 0 ≤ y)
    (hτ : 0 < τ) (M : ℕ) :
    (if y ≤ Wr ^ (1 + τ) then (Wr ^ d)⁻¹ else 0) + (y + Wr) ^ (-(M : ℝ)) ≤
      (2 ^ M * (Wr ^ τ) ^ M + 1) * ((1 + y / Wr) ^ M)⁻¹ := by
  have hW0 : 0 < Wr := by linarith
  have hb : 0 < 1 + y / Wr := by positivity
  have hrp : (y + Wr) ^ (-(M : ℝ)) ≤ ((1 + y / Wr) ^ M)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ hb.le ?_ M)
    have e : y + Wr = Wr * (1 + y / Wr) := by field_simp; ring
    rw [e]
    nlinarith
  have hWt : 1 ≤ Wr ^ τ := Real.one_le_rpow hW hτ.le
  split_ifs with h
  · have h1 : (Wr ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW)
    have h2 : 1 ≤ 2 ^ M * (Wr ^ τ) ^ M * ((1 + y / Wr) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul, ← mul_pow]
      refine pow_le_pow_left₀ hb.le ?_ M
      have : y / Wr ≤ Wr ^ τ := by
        rw [div_le_iff₀ hW0]
        calc y ≤ Wr ^ (1 + τ) := h
          _ = Wr ^ τ * Wr := by rw [Real.rpow_add hW0, Real.rpow_one, mul_comm]
      linarith
    nlinarith
  · have : 0 ≤ 2 ^ M * (Wr ^ τ) ^ M * ((1 + y / Wr) ^ M)⁻¹ := by positivity
    nlinarith

/-- `W^{c₀M/2} (W/L)^M ≤ L^{-D}` for `W ≤ L^{1-c₀}`, `1 ≤ L`, `D ≤ c₀ M/2`. -/
private theorem InfLimit_wrap_exp {c₀ Wr Lr D : ℝ} {M : ℕ} (hc₀ : 0 < c₀) (hL1 : 1 ≤ Lr)
    (hW0 : 0 < Wr) (hWL : Wr ≤ Lr ^ (1 - c₀)) (hM : D ≤ c₀ / 2 * M) :
    (Wr ^ (c₀ / 2)) ^ M * (Wr / Lr) ^ M ≤ Lr ^ (-D) := by
  have hL0 : 0 < Lr := by linarith
  have hq : Wr ^ (c₀ / 2) * (Wr / Lr) ≤ Lr ^ (-(c₀ / 2)) := by
    have hexp : (1 - c₀) * (1 + c₀ / 2) ≤ 1 - c₀ / 2 := by nlinarith [sq_nonneg c₀]
    have h1 : Wr ^ (1 + c₀ / 2) ≤ Lr ^ (1 - c₀ / 2) := by
      calc Wr ^ (1 + c₀ / 2) ≤ (Lr ^ (1 - c₀)) ^ (1 + c₀ / 2) :=
            Real.rpow_le_rpow hW0.le hWL (by positivity)
        _ = Lr ^ ((1 - c₀) * (1 + c₀ / 2)) := (Real.rpow_mul hL0.le _ _).symm
        _ ≤ Lr ^ (1 - c₀ / 2) := Real.rpow_le_rpow_of_exponent_le hL1 hexp
    have e1 : Wr ^ (c₀ / 2) * (Wr / Lr) = Wr ^ (1 + c₀ / 2) / Lr := by
      rw [Real.rpow_add hW0, Real.rpow_one]; ring
    have e2 : Lr ^ (-(c₀ / 2)) = Lr ^ (1 - c₀ / 2) / Lr := by
      rw [Real.rpow_sub hL0, Real.rpow_one, Real.rpow_neg hL0.le]
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right h1 hL0.le
  rw [← mul_pow]
  calc (Wr ^ (c₀ / 2) * (Wr / Lr)) ^ M ≤ (Lr ^ (-(c₀ / 2))) ^ M :=
        pow_le_pow_left₀ (by positivity) hq M
    _ = Lr ^ (-(c₀ / 2) * M) := (Real.rpow_mul_natCast hL0.le _ _).symm
    _ ≤ Lr ^ (-D) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

/-- The frequencies `2πk/L` of `T_L^d` lie in `[-π, π]^d`. -/
private theorem InfLimit_zfreqPi_mem {d L : ℕ} [NeZero L] (k : Zd d L) : zfreqPi k ∈ cubePi d := by
  intro i _
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨h1, h2⟩ := (k i).valMinAbs_mem_Ioc
  have h1' : -(L : ℝ) < ((k i).valMinAbs : ℝ) * 2 := by exact_mod_cast h1
  have h2' : ((k i).valMinAbs : ℝ) * 2 ≤ L := by exact_mod_cast h2
  have hpi := Real.pi_pos
  simp only [zfreqPi, Set.mem_Icc]
  constructor
  · rw [le_div_iff₀ hL]; nlinarith
  · rw [div_le_iff₀ hL]; nlinarith

end Bookkeeping

/-! ## [I, Claim 7.8]: two kernels with close symbols -/

/-- The symbol of a symmetric kernel close to `ψ(W·)` lies in `[-1 + c′/2, 1]` for
`W ≥ 2|C₁|/c′`. -/
private theorem InfLimit_symbol_range {d L : ℕ} [NeZero L] {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)}
    {c' : ℝ} (hψ : SymbolBound ψ c') {C : ℕ → ℝ} {W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ}
    (hS : IsSymKernel S) (hSc : SymbolClose ψ C W S) (hW0 : (0 : ℝ) < W)
    (hW : 2 * |C 1| / c' ≤ W) (k : Zd d L) :
    -1 + c' / 2 ≤ (symbol (cmat S) k).re ∧ (symbol (cmat S) k).re ≤ 1 := by
  have hc' := hψ.pos
  constructor
  · have h1 := hSc 1 k
    rw [pow_one] at h1
    have h2 := (hψ.range ((W : ℝ) • zfreq k)).1
    have h3 : |(symbol (cmat S) k - (ψ ((W : ℝ) • zfreq k) : ℂ)).re| ≤
        ‖symbol (cmat S) k - (ψ ((W : ℝ) • zfreq k) : ℂ)‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at h3
    have h4 : C 1 / (W : ℝ) ≤ c' / 2 := by
      rw [div_le_iff₀ hW0]
      rw [div_le_iff₀ hc'] at hW
      nlinarith [le_abs_self (C 1)]
    have := (abs_le.mp h3).1
    linarith
  · exact (Complex.re_le_norm _).trans (hS.norm_symbol_le k)

/-! ## [I, Lemma 7.2] (7.8): `S^+` against `S^+_∞` -/

/-- [I, Lemma 7.2], (7.8) = (S+xy2): for `W ≥ W₀`, uniformly in `(W, L) ∈ adm(c₀, c₁)`, in
symmetric kernels `S` on `Z_L^d` and kernels `s` on `ℤ^d` whose symbols are both close to
`ψ(W·)` with the constants `C`, in `z = E + iη ∈ 𝐃(κ, ε)` and in `x ∈ Z_L^d`:
`|(S^+_∞)_{0[x]_L}(E) - S^+_{0x}(z)| ≤ K (η W^{-d} 1(‖x‖_L ≤ W^{1+τ}) + ⟨x⟩^{-D})`, with
`S^+_∞(E)` taken at `m(E)`, `[x]_L` the centred representative of `x` in `ℤ^d` and
`⟨x⟩ = ‖x‖_L + W`; here `ψ` satisfies (H1)–(H2) with `c′`. -/
theorem Splus_sub_SplusInf :
  ∀ (d : ℕ) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (c' : ℝ) (hψ : SymbolBound ψ c') (C : ℕ → ℝ) (κ ε τ D : ℝ) (hκ : 0 < κ) (hε : 0 < ε)
    (hτ : 0 < τ) (hD : 0 < D),
    ∃ K W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsSymKernel S → SymbolClose ψ C W S →
      ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        ‖SplusInf (mE z.re) s (zlift x) - Splus (msc z) S 0 x‖ ≤
          K * (z.im * (if (zdistInf d L x : ℝ) ≤ (W : ℝ) ^ (1 + τ) then ((W : ℝ) ^ d)⁻¹ else 0) +
            ((zdistInf d L x : ℝ) + W) ^ (-D)) := by
  intro d c₀ c₁ hc₀ hc₁ ψ c' hψ C κ ε τ D hκ hε hτ hD
  have hc' := hψ.pos
  set δ : ℝ := Real.sqrt (2 * κ) / 5 with hδ
  have hδ0 : 0 < δ := by positivity
  set c : ℝ := min (δ / 4) (c' / 2) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  set M : ℕ := max (d + 1) ⌈2 * D / c₀⌉₊ with hM
  have hMd : d + 1 ≤ M := le_max_left _ _
  have hMc : D ≤ c₀ / 2 * M := by
    have h1 : (⌈2 * D / c₀⌉₊ : ℝ) ≤ M := by exact_mod_cast le_max_right _ _
    have h2 := Nat.le_ceil (2 * D / c₀)
    rw [div_le_iff₀ hc₀] at h2
    nlinarith
  have hM0 : (0 : ℝ) < M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    linarith
  set D' : ℕ := ⌈D / c₁⌉₊ with hD'
  obtain ⟨K₁, Wa, ha⟩ := SplusInf_decay d ψ c' hψ C κ (c₀ / 2) M hκ (by positivity) hM0
  obtain ⟨K₃, Wb, hb⟩ := SplusInf_decay d ψ c' hψ C κ τ D hκ hτ hD
  obtain ⟨K₄, Wc, hc4⟩ := Splus_decay_msc d c₀ c₁ hc₀ hc₁ ψ c' hψ C κ τ D hκ hτ hD
  obtain ⟨Wg, hWg⟩ := zdSymbol_ge d ψ c' hψ C
  obtain ⟨K₀, hK₀⟩ := zdSymbol_smooth d ψ C 0
  obtain ⟨AR, hAR0, hAR⟩ := InfLimit_riemann ψ
  obtain ⟨CT, hCT⟩ := tsum_periodize_le d M hMd
  set Kκ : ℝ := 4 / Real.sqrt (2 * κ) with hKκ
  set Kmain : ℝ := Kκ * AR / c ^ 2 with hKmain
  set Ktiny : ℝ := 2 ^ D * (|K₁| * (2 ^ M + 1) * |CT| + (Kκ + 2) * |C D'| / c ^ 2) with hKtiny
  set Kfar : ℝ := |K₃| + |K₄| with hKfar
  have hKmain0 : 0 ≤ Kmain := by positivity
  have hKtiny0 : 0 ≤ Ktiny := by positivity
  have hKfar0 : 0 ≤ Kfar := by positivity
  refine ⟨Kmain + Ktiny + Kfar, max (max (max 1 Wa) (max Wb Wc))
    (max Wg (max (2 * |C 1| / c') (4 * |C 1| / δ))), ?_⟩
  intro W L _ hadm hW S hS hSc s hs z hz x
  have hW1 : (1 : ℝ) ≤ W := le_trans (by simp) hW
  have hWa : Wa ≤ (W : ℝ) := le_trans (by simp) hW
  have hWb : Wb ≤ (W : ℝ) := le_trans (by simp) hW
  have hWc : Wc ≤ (W : ℝ) := le_trans (by simp) hW
  have hWg' : Wg ≤ (W : ℝ) := le_trans (by simp) hW
  have hWC1 : 2 * |C 1| / c' ≤ (W : ℝ) := le_trans (by simp) hW
  have hWC2 : 4 * |C 1| / δ ≤ (W : ℝ) := le_trans (by simp) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hL1, hWL, hLc, hηL, hηpos, hη1⟩ := InfLimit_window hc₀ hε hadm hW1 hz
  have hL0 : (0 : ℝ) < L := by linarith
  set X : ℝ := (zdistInf d L x : ℝ) + W with hX
  have hX0 : 0 < X := by positivity
  have hz0 : zdInf (zlift x) = zdistInf d L x := InfLimit_zdInf_zlift x
  have hE2 : |z.re| < 2 := by linarith [hz.1]
  by_cases hin : (zdistInf d L x : ℝ) ≤ (W : ℝ) ^ (1 + τ)
  swap
  · -- far from the origin: both kernels are `O(⟨x⟩^{-D})`
    simp only [hin, ↓reduceIte, mul_zero, zero_add]
    have h1 := (hb W hWb s hs z.re hz.1.le (zlift x)).1
    rw [hz0] at h1
    simp only [hin, ↓reduceIte, zero_add] at h1
    have h2 := (hc4 W L hadm hWc S hS hSc z hηpos hz.1 0 x).1
    unfold splusBound at h2
    rw [zero_sub, zdistInf_neg] at h2
    simp only [hin, ↓reduceIte, zero_add] at h2
    have hXD : 0 ≤ X ^ (-D) := by positivity
    calc ‖SplusInf (mE z.re) s (zlift x) - Splus (msc z) S 0 x‖ ≤
          ‖SplusInf (mE z.re) s (zlift x)‖ + ‖Splus (msc z) S 0 x‖ := norm_sub_le _ _
      _ ≤ |K₃| * X ^ (-D) + |K₄| * X ^ (-D) := by
          gcongr
          · exact h1.trans (by gcongr; exact le_abs_self _)
          · exact h2.trans (by gcongr; exact le_abs_self _)
      _ = Kfar * X ^ (-D) := by rw [hKfar]; ring
      _ ≤ (Kmain + Ktiny + Kfar) * X ^ (-D) := by gcongr; linarith
  simp only [hin, ↓reduceIte]
  -- the symbols
  set m := msc z with hm
  set e := mE z.re with he
  obtain ⟨hm1, hmδ⟩ := msc_bulk κ hκ z hηpos hz.1.le
  obtain ⟨he1, heδ⟩ := mE_bulk κ hκ z.re hz.1.le
  have hw1 : ‖m ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm1
  have hwE1 : ‖e ^ 2‖ ≤ 1 := by rw [norm_pow, he1, one_pow]
  have hss : Summable s := by
    by_contra h
    have := hs.sum_one
    rw [tsum_eq_zero_of_not_summable h] at this
    exact zero_ne_one this
  obtain ⟨hcd, -, hK0⟩ := hK₀ W hWn s hs
  have hK0' : ∀ p, ‖zdSymbol s p‖ ≤ K₀ := fun p => by
    have := hK0 p
    rwa [norm_iteratedFDeriv_zero, pow_zero, mul_one] at this
  have hcont : Continuous (zdSymbol s) := hcd.continuous
  have hsim : ∀ p, (zdSymbol s p).im = 0 := zdSymbol_im s hs.symm hss
  have hsreal : ∀ p, zdSymbol s p = (((zdSymbol s p).re : ℝ) : ℂ) := fun p =>
    Complex.ext (by simp) (by simp [hsim p])
  have heC : |C 1| / (W : ℝ) ≤ δ / 4 := by
    rw [div_le_iff₀ hW0]
    rw [div_le_iff₀ hδ0] at hWC2
    linarith
  have hsr : ∀ p ∈ cubePi d, -1 + c' / 2 ≤ (zdSymbol s p).re ∧
      (zdSymbol s p).re ≤ 1 + |C 1| / W := by
    intro p hp
    refine ⟨hWg W hWg' s hs p hp, ?_⟩
    have h1 := hs.close 1 p hp
    rw [pow_one] at h1
    have h2 := (hψ.range ((W : ℝ) • WithLp.toLp 2 p)).2
    have h3 : |(zdSymbol s p - (ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ)).re| ≤
        ‖zdSymbol s p - (ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ)‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at h3
    have h4 : C 1 / (W : ℝ) ≤ |C 1| / W := div_le_div_of_nonneg_right (le_abs_self _) hW0.le
    have := (abs_le.mp h3).2
    linarith
  have hlowE : ∀ p ∈ cubePi d, c ≤ ‖1 - e ^ 2 * zdSymbol s p‖ := by
    intro p hp
    obtain ⟨h1, h2⟩ := hsr p hp
    rw [hsreal p]
    exact InfLimit_one_sub_mul_ge hwE1 hδ0 heδ hc' heC h1 h2
  have hlowS : ∀ k, c ≤ ‖1 - m ^ 2 * symbol (cmat S) k‖ := by
    intro k
    obtain ⟨h1, h2⟩ := InfLimit_symbol_range hψ hS hSc hW0 hWC1 k
    rw [InfLimit_symbol_real hS k]
    exact InfLimit_one_sub_mul_ge hw1 hδ0 hmδ hc' (by positivity : (0 : ℝ) ≤ δ / 4) h1
      (by linarith)
  have hneS : ∀ k, m ^ 2 * symbol (cmat S) k ≠ 1 := by
    intro k h
    have := hlowS k
    rw [h, sub_self, norm_zero] at this
    linarith
  have hdenE : ∀ p ∈ cubePi d, (1 : ℂ) - e ^ 2 * zdSymbol s p ≠ 0 := by
    intro p hp h
    have := hlowE p hp
    rw [h, norm_zero] at this
    linarith
  -- the kernel `S^+_∞(E)`: decay, summability and Fourier series
  set F : (Fin d → ℝ) → ℂ := fun p => e ^ 2 * zdSymbol s p / (1 - e ^ 2 * zdSymbol s p) with hF
  have hKE : SplusInf e s = latticeFourier F := rfl
  set B : ℝ := |K₁| * (2 ^ M * ((W : ℝ) ^ (c₀ / 2)) ^ M + 1) with hB
  have hKb : ∀ y, ‖SplusInf e s y‖ ≤ B * ((1 + (zdInf y : ℝ) / W) ^ M)⁻¹ := by
    intro y
    have h1 := (ha W hWa s hs z.re hz.1.le y).1
    have h2 := InfLimit_decay_weight (d := d) hW1 (Nat.cast_nonneg (zdInf y)) (by positivity :
      0 < c₀ / 2) M
    have h0 : 0 ≤ (if (zdInf y : ℝ) ≤ (W : ℝ) ^ (1 + c₀ / 2) then ((W : ℝ) ^ d)⁻¹ else 0) +
        ((zdInf y : ℝ) + W) ^ (-(M : ℝ)) := by
      have : 0 ≤ (if (zdInf y : ℝ) ≤ (W : ℝ) ^ (1 + c₀ / 2) then ((W : ℝ) ^ d)⁻¹ else 0) := by
        split_ifs <;> positivity
      positivity
    calc ‖SplusInf e s y‖ ≤ |K₁| * ((if (zdInf y : ℝ) ≤ (W : ℝ) ^ (1 + c₀ / 2) then
          ((W : ℝ) ^ d)⁻¹ else 0) + ((zdInf y : ℝ) + W) ^ (-(M : ℝ))) :=
          h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) h0)
      _ ≤ |K₁| * ((2 ^ M * ((W : ℝ) ^ (c₀ / 2)) ^ M + 1) * ((1 + (zdInf y : ℝ) / W) ^ M)⁻¹) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = B * ((1 + (zdInf y : ℝ) / W) ^ M)⁻¹ := by rw [hB]; ring
  have hKs : Summable fun y => ‖SplusInf e s y‖ := InfLimit_summable_of_le (by omega) hW0 hKb
  have hFi : IntegrableOn F (cubePi d) := by
    refine ContinuousOn.integrableOn_compact InfLimit_isCompact_cubePi ?_
    exact ((continuous_const.mul hcont).continuousOn).div
      ((continuous_const.sub (continuous_const.mul hcont)).continuousOn) hdenE
  have hser := InfLimit_series hss hcont hK0' (e ^ 2) hKs hFi hdenE
  -- the main term: `L^{-d} Σ_k (G_{m(E)²}(ŝ(p_k)) - G_{m²}(Ŝ(k))) e_k(-x)`
  have hper : periodize L (SplusInf e s) x =
      ((L : ℂ) ^ d)⁻¹ * ∑ k, F (zfreqPi k) * zchar k (-x) := by
    rw [periodize_eq _ hKs x]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hKE, hser _ (InfLimit_zfreqPi_mem k)]
  have hSp := InfLimit_Splus_eq S hS m hneS x
  have hclose : ∀ k, ‖zdSymbol s (zfreqPi k) - symbol (cmat S) k‖ ≤ 2 * |C D'| / (W : ℝ) ^ D' ∧
      ‖zdSymbol s (zfreqPi k)‖ ≤ |ψ ((W : ℝ) • zfreq k)| + |C D'| / (W : ℝ) ^ D' := by
    intro k
    have h1 := hSc D' k
    have h2 := hs.close D' (zfreqPi k) (InfLimit_zfreqPi_mem k)
    have e1 : zfreq k = WithLp.toLp 2 (zfreqPi k) := rfl
    rw [e1] at h1
    rw [← e1] at h2 h1
    have h3 : C D' / (W : ℝ) ^ D' ≤ |C D'| / (W : ℝ) ^ D' :=
      div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
    constructor
    · calc ‖zdSymbol s (zfreqPi k) - symbol (cmat S) k‖ =
            ‖(zdSymbol s (zfreqPi k) - (ψ ((W : ℝ) • zfreq k) : ℂ)) -
              (symbol (cmat S) k - (ψ ((W : ℝ) • zfreq k) : ℂ))‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
        _ ≤ 2 * |C D'| / (W : ℝ) ^ D' := by rw [mul_div_assoc]; linarith
    · calc ‖zdSymbol s (zfreqPi k)‖ ≤ ‖(ψ ((W : ℝ) • zfreq k) : ℂ)‖ +
            ‖zdSymbol s (zfreqPi k) - (ψ ((W : ℝ) • zfreq k) : ℂ)‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ |ψ ((W : ℝ) • zfreq k)| + |C D'| / (W : ℝ) ^ D' := by
            rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hww : ‖e ^ 2 - m ^ 2‖ ≤ Kκ * z.im := by
    have h1 := (InfLimit_sq_sub_le hηpos hE2.le).1
    have h2 := InfLimit_msc_sub_mE hηpos hE2
    have h3 := InfLimit_mE_im_ge hκ hz.1
    have h4 : 0 < Real.sqrt (2 * κ) := by positivity
    have h5 : z.im / (mE z.re).im ≤ z.im / (Real.sqrt (2 * κ) / 2) :=
      div_le_div_of_nonneg_left hηpos.le (by positivity) h3
    have e2 : Kκ * z.im = 2 * (z.im / (Real.sqrt (2 * κ) / 2)) := by
      rw [hKκ]; field_simp; ring
    rw [norm_sub_rev, e2]
    linarith
  have hterm : ∀ k, ‖F (zfreqPi k) - m ^ 2 * symbol (cmat S) k / (1 - m ^ 2 * symbol (cmat S) k)‖
      ≤ (Kκ * z.im * |ψ ((W : ℝ) • zfreq k)| + (Kκ + 2) * |C D'| / (W : ℝ) ^ D') / c ^ 2 := by
    intro k
    obtain ⟨hk1, hk2⟩ := hclose k
    refine (InfLimit_G_sub_le hc0 (hlowE _ (InfLimit_zfreqPi_mem k)) (hlowS k)).trans ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hKκ0 : 0 ≤ Kκ := by positivity
    set t : ℝ := |C D'| / (W : ℝ) ^ D' with ht
    have ht0 : 0 ≤ t := by positivity
    have a1 : ‖e ^ 2 - m ^ 2‖ * ‖zdSymbol s (zfreqPi k)‖ ≤
        Kκ * z.im * |ψ ((W : ℝ) • zfreq k)| + Kκ * z.im * t := by
      rw [← mul_add]
      exact mul_le_mul hww hk2 (norm_nonneg _) (by positivity)
    have a2 : ‖m ^ 2‖ * ‖zdSymbol s (zfreqPi k) - symbol (cmat S) k‖ ≤ 2 * t := by
      refine (mul_le_of_le_one_left (norm_nonneg _) hw1).trans ?_
      rw [ht, ← mul_div_assoc]; exact hk1
    have a3 : Kκ * z.im * t ≤ Kκ * t := by
      have := mul_le_mul_of_nonneg_left hη1 hKκ0
      rw [mul_one] at this
      exact mul_le_mul_of_nonneg_right this ht0
    have e3 : (Kκ + 2) * |C D'| / (W : ℝ) ^ D' = Kκ * t + 2 * t := by rw [ht]; ring
    rw [e3]
    linarith
  have hmain : ‖periodize L (SplusInf e s) x - Splus m S 0 x‖ ≤
      Kmain * (z.im * ((W : ℝ) ^ d)⁻¹) + (Kκ + 2) * |C D'| / c ^ 2 / (W : ℝ) ^ D' := by
    rw [hper, hSp, ← mul_sub, ← Finset.sum_sub_distrib]
    have e4 : ∑ k, (F (zfreqPi k) * zchar k (-x) - m ^ 2 * symbol (cmat S) k /
        (1 - m ^ 2 * symbol (cmat S) k) * zchar k (-x)) = ∑ k, (F (zfreqPi k) -
        m ^ 2 * symbol (cmat S) k / (1 - m ^ 2 * symbol (cmat S) k)) * zchar k (-x) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e4]
    refine (InfLimit_norm_avg_le_avg _ x).trans ?_
    have hR := hAR W L hW1 hWL
    have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
    calc ((L : ℝ) ^ d)⁻¹ * ∑ k, ‖F (zfreqPi k) -
          m ^ 2 * symbol (cmat S) k / (1 - m ^ 2 * symbol (cmat S) k)‖
        ≤ ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, (Kκ * z.im * |ψ ((W : ℝ) • zfreq k)| +
          (Kκ + 2) * |C D'| / (W : ℝ) ^ D') / c ^ 2 := by
          gcongr with k
          exact hterm k
      _ = Kκ * z.im / c ^ 2 * (((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, |ψ ((W : ℝ) • zfreq k)|) +
          (Kκ + 2) * |C D'| / c ^ 2 / (W : ℝ) ^ D' := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          field_simp
      _ ≤ Kκ * z.im / c ^ 2 * (AR / (W : ℝ) ^ d) + (Kκ + 2) * |C D'| / c ^ 2 / (W : ℝ) ^ D' := by
          gcongr
      _ = Kmain * (z.im * ((W : ℝ) ^ d)⁻¹) + (Kκ + 2) * |C D'| / c ^ 2 / (W : ℝ) ^ D' := by
          rw [hKmain]; ring
  -- the images `n ≠ 0` of the periodisation
  have hwrap : ‖SplusInf e s (zlift x) - periodize L (SplusInf e s) x‖ ≤
      |K₁| * (2 ^ M + 1) * |CT| * (L : ℝ) ^ (-D) := by
    rw [norm_sub_rev]
    have hbs := (InfLimit_term_summable M hMd (W : ℝ) hW0 x).mul_left B
    refine (InfLimit_periodize_sub_le _ hKs x _ hbs fun n => hKb _).trans ?_
    rw [tsum_mul_left]
    have hT := hCT L (W : ℝ) hW0 hWL x
    have hWt : 1 ≤ (W : ℝ) ^ (c₀ / 2) := Real.one_le_rpow hW1 (by positivity)
    have hB' : B ≤ |K₁| * (2 ^ M + 1) * ((W : ℝ) ^ (c₀ / 2)) ^ M := by
      rw [hB, mul_assoc]
      have : 1 ≤ ((W : ℝ) ^ (c₀ / 2)) ^ M := one_le_pow₀ hWt
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      linarith
    have hqM := InfLimit_wrap_exp hc₀ hL1 hW0 hadm.2 hMc
    have hWL1 : (W : ℝ) / L ≤ 1 := by rw [div_le_one hL0]; exact hWL
    calc B * ∑' n : {n : Fin d → ℤ // n ≠ 0},
          ((1 + (zdInf (zlift x + (L : ℤ) • n.1) : ℝ) / W) ^ M)⁻¹
        ≤ (|K₁| * (2 ^ M + 1) * ((W : ℝ) ^ (c₀ / 2)) ^ M) * (|CT| * (W / L) ^ M) :=
          mul_le_mul hB' (hT.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
            (tsum_nonneg fun n => by positivity) (by positivity)
      _ = |K₁| * (2 ^ M + 1) * |CT| * (((W : ℝ) ^ (c₀ / 2)) ^ M * (W / L) ^ M) := by ring
      _ ≤ |K₁| * (2 ^ M + 1) * |CT| * (L : ℝ) ^ (-D) :=
          mul_le_mul_of_nonneg_left hqM (by positivity)
  -- assembly
  have hLX : (L : ℝ) ^ (-D) ≤ 2 ^ D * X ^ (-D) := by
    have h := InfLimit_two_L_rpow_le hW1 hWL hD.le x
    rw [← hX] at h
    have h2 : (2 : ℝ) ^ D * 2 ^ (-D) = 1 := by
      rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
    have h3 : 0 < (2 : ℝ) ^ D := by positivity
    calc (L : ℝ) ^ (-D) = 2 ^ D * (2 ^ (-D) * (L : ℝ) ^ (-D)) := by rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 ^ D * X ^ (-D) := mul_le_mul_of_nonneg_left h h3.le
  have hWD' : (Kκ + 2) * |C D'| / c ^ 2 / (W : ℝ) ^ D' ≤
      (Kκ + 2) * |C D'| / c ^ 2 * (L : ℝ) ^ (-D) := by
    have hLW : (L : ℝ) ^ D ≤ (W : ℝ) ^ D' :=
      InfLimit_L_rpow_le_W_pow hc₁ hL1 hLc (by
        have := InfLimit_ceil_spec (X := D) hc₁; rw [← hD'] at this; exact this)
    rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hLW
  have htri : ‖SplusInf e s (zlift x) - Splus m S 0 x‖ ≤
      ‖SplusInf e s (zlift x) - periodize L (SplusInf e s) x‖ +
        ‖periodize L (SplusInf e s) x - Splus m S 0 x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hXD : 0 ≤ X ^ (-D) := by positivity
  have hηW : 0 ≤ z.im * ((W : ℝ) ^ d)⁻¹ := by positivity
  have hfin : |K₁| * (2 ^ M + 1) * |CT| * (L : ℝ) ^ (-D) +
      (Kκ + 2) * |C D'| / c ^ 2 * (L : ℝ) ^ (-D) ≤ Ktiny * X ^ (-D) := by
    calc |K₁| * (2 ^ M + 1) * |CT| * (L : ℝ) ^ (-D) + (Kκ + 2) * |C D'| / c ^ 2 * (L : ℝ) ^ (-D)
        = (|K₁| * (2 ^ M + 1) * |CT| + (Kκ + 2) * |C D'| / c ^ 2) * (L : ℝ) ^ (-D) := by ring
      _ ≤ (|K₁| * (2 ^ M + 1) * |CT| + (Kκ + 2) * |C D'| / c ^ 2) * (2 ^ D * X ^ (-D)) :=
          mul_le_mul_of_nonneg_left hLX (by positivity)
      _ = Ktiny * X ^ (-D) := by rw [hKtiny]; ring
  have hK1 := mul_nonneg hKmain0 hXD
  have hK2 := mul_nonneg hKtiny0 hηW
  have hK3 := mul_nonneg hKfar0 (add_nonneg hηW hXD)
  calc ‖SplusInf e s (zlift x) - Splus m S 0 x‖ ≤
        Kmain * (z.im * ((W : ℝ) ^ d)⁻¹) + Ktiny * X ^ (-D) := by
        linarith [htri, hwrap, hmain, hWD', hfin]
    _ ≤ (Kmain + Ktiny + Kfar) * (z.im * ((W : ℝ) ^ d)⁻¹ + X ^ (-D)) := by
        linarith [hK1, hK2, hK3]

/-! ## [I, Lemma 7.2] (Theta-wh): `Θ` against `Θ_∞` -/

/-- [I, Lemma 7.2], (Theta-wh) = (7.9): for `d ≥ 5` and `W ≥ W₀`, uniformly in
`(W, L) ∈ adm(c₀, c₁)`, in symmetric kernels `S` on `Z_L^d` and kernels `s` on `ℤ^d` whose
symbols are both close to `ψ(W·)` with the constants `C`, in `z ∈ 𝐃(κ, ε)` and in
`x ∈ Z_L^d`: `|Θ_∞([x]_L) - Θ_{0x}(z)| ≤ η / (W⁴ ⟨x⟩^{d-4-τ}) + ⟨x⟩^{-D}`, with `[x]_L` the
centred representative of `x` in `ℤ^d`, `η = Im z` and `⟨x⟩ = ‖x‖_L + W`. -/
theorem Theta_sub_ThetaInf :
  ∀ (d : ℕ) (hd : 5 ≤ d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ)
    (κ ε τ D : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (hτ : 0 < τ) (hD : 0 < D),
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsSymKernel S → SymbolClose ψ C W S →
      ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        ‖ThetaInf s (zlift x) - (Theta (msc z) S 0 x : ℂ)‖ ≤
          z.im / ((W : ℝ) ^ 4 * ((zdistInf d L x : ℝ) + W) ^ ((d : ℝ) - 4 - τ)) +
            ((zdistInf d L x : ℝ) + W) ^ (-D) := by
  intro d hd c₀ c₁ hc₀ hc₁ ψ cψ hψ C κ ε τ D hκ hε hτ hD
  obtain ⟨Wr, hrep⟩ := Theta_sub_periodize d (by omega) c₀ c₁ hc₀ hc₁ ψ cψ hψ C κ ε (D + 1)
    hκ hε (by linarith)
  set M : ℕ := max (d + 1) ⌈2 * (D + 1) / ε⌉₊ with hM
  have hMd : d + 1 ≤ M := le_max_left _ _
  have hMε : D + 1 ≤ ε / 2 * M := by
    have h1 : (⌈2 * (D + 1) / ε⌉₊ : ℝ) ≤ M := by exact_mod_cast le_max_right _ _
    have h2 := Nat.le_ceil (2 * (D + 1) / ε)
    rw [div_le_iff₀ hε] at h2
    nlinarith
  obtain ⟨C₀, Wd, hdec⟩ := ThetaZd_decay d (by omega) ψ cψ hψ C M
  obtain ⟨C₅, W₅, hsub⟩ := ThetaZd_sub_decay d hd ψ cψ hψ C
  obtain ⟨CT, hCT⟩ := tsum_periodize_le d M hMd
  set A : ℝ := |C₀| * |CT| * 2 ^ M with hA
  set Kκ : ℝ := 4 / Real.sqrt (2 * κ) with hKκ
  refine ⟨max (max (max Wr Wd) (max W₅ 2))
    (max (2 ^ D * (2 * A)) (max ((|C₅| * Kκ) ^ (1 / τ)) (2 ^ (2 / ε)))), ?_⟩
  intro W L _ hadm hW S hS hSc s hs z hz x
  have hWr : Wr ≤ (W : ℝ) := le_trans (by simp) hW
  have hWd : Wd ≤ (W : ℝ) := le_trans (by simp) hW
  have hW5 : W₅ ≤ (W : ℝ) := le_trans (by simp) hW
  have hW2 : (2 : ℝ) ≤ W := le_trans (by simp) hW
  have hWA : 2 ^ D * (2 * A) ≤ (W : ℝ) := le_trans (by simp) hW
  have hWC : (|C₅| * Kκ) ^ (1 / τ) ≤ (W : ℝ) := le_trans (by simp) hW
  have hWe : (2 : ℝ) ^ (2 / ε) ≤ W := le_trans (by simp) hW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hL1, hWL, hLc, hηL, hηpos, hη1⟩ := InfLimit_window hc₀ hε hadm hW1 hz
  have hL0 : (0 : ℝ) < L := by linarith
  have ha0 : 0 ≤ ‖msc z‖ ^ 2 := by positivity
  have ha1 := InfLimit_sq_lt_one hηpos
  have hgap := InfLimit_one_sub_ge hηpos hη1
  set a : ℝ := ‖msc z‖ ^ 2 with ha
  set σ : ℝ := Real.sqrt (1 - a) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by linarith)
  have hσ2 : σ ^ 2 = 1 - a := Real.sq_sqrt (by linarith)
  obtain ⟨-, hb⟩ := hdec W hWd s hs a ha0 ha1.le
  -- the scale `R = W (1 - a)^{-1/2}`
  set R : ℝ := W / σ with hR
  have hR0 : 0 < R := by positivity
  have hRL : R / L ≤ 2 * (L : ℝ) ^ (-(ε / 2)) := by
    refine InfLimit_R_div_L_le hL1 hW0 hσ0 ?_
    rw [hσ2]
    have := hz.2.1
    linarith
  have h2L : 2 * (L : ℝ) ^ (-(ε / 2)) ≤ 1 := InfLimit_two_rpow_le_one hε (hWe.trans hWL)
  have hRleL : R ≤ L := by
    have := hRL.trans h2L
    rwa [div_le_one hL0] at this
  have hrpow : (R / L) ^ M ≤ 2 ^ M * (L : ℝ) ^ (-(D + 1)) :=
    InfLimit_RL_pow_le hL1 (by positivity) hRL hMε
  have hden1 : ∀ v : Fin d → ℤ, 1 ≤ (W : ℝ) ^ 2 * ((zdInf v : ℝ) + W) ^ (d - 2) := fun v =>
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1)
      (one_le_pow₀ (by linarith [(Nat.cast_nonneg (zdInf v) : (0 : ℝ) ≤ zdInf v)]))
  have hterm2 : ∀ v : Fin d → ℤ, ‖ThetaZd a s v‖ ≤ |C₀| * ((1 + (zdInf v : ℝ) / R) ^ M)⁻¹ := by
    intro v
    have e : (zdInf v : ℝ) / R = (zdInf v : ℝ) * σ / W := by rw [hR]; field_simp
    rw [e]
    have h := hb v
    rw [← le_div_iff₀ (by positivity)] at h
    refine h.trans ?_
    rw [div_eq_mul_inv _ ((1 + _) ^ M)]
    gcongr
    exact (div_le_div_of_nonneg_right (le_abs_self C₀) (by positivity)).trans
      (div_le_self (abs_nonneg _) (hden1 v))
  have hΘs : Summable fun v => ‖ThetaZd a s v‖ :=
    InfLimit_summable_of_le (by omega) hR0 hterm2
  -- the images `n ≠ 0` of the periodisation
  have hwrap : ‖periodize L (ThetaZd a s) x - ThetaZd a s (zlift x)‖ ≤
      A * (L : ℝ) ^ (-(D + 1)) := by
    have hbs := (InfLimit_term_summable M hMd R hR0 x).mul_left |C₀|
    refine (InfLimit_periodize_sub_le _ hΘs x _ hbs fun n => hterm2 _).trans ?_
    rw [tsum_mul_left]
    have hT := hCT L R hR0 hRleL x
    have hq : 0 ≤ (R / L) ^ M := by positivity
    calc |C₀| * ∑' n : {n : Fin d → ℤ // n ≠ 0},
          ((1 + (zdInf (zlift x + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹
        ≤ |C₀| * (|CT| * (2 ^ M * (L : ℝ) ^ (-(D + 1)))) := by
          gcongr
          calc _ ≤ CT * (R / L) ^ M := hT
            _ ≤ |CT| * (R / L) ^ M := by gcongr; exact le_abs_self _
            _ ≤ _ := by gcongr
      _ = A * (L : ℝ) ^ (-(D + 1)) := by rw [hA]; ring
  -- the replacement `Θ ↔ Σ_n Θ_{ℤ^d}(· + L n)`
  have hP1 := hrep W L hadm hWr S hS hSc s hs z hz x
  -- the main term `Θ_∞ - Θ_{ℤ^d}(a)` at `[x]_L`
  set X : ℝ := (zdistInf d L x : ℝ) + W with hX
  have hX0 : 0 < X := by positivity
  have hXW : (W : ℝ) ≤ X := by rw [hX]; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L x)]
  have hz0 : zdInf (zlift x) = zdistInf d L x := InfLimit_zdInf_zlift x
  have hE2 : |z.re| < 2 := by linarith [hz.1]
  have h1a : 1 - a ≤ Kκ * z.im := by
    have h1 := (InfLimit_sq_sub_le hηpos hE2.le).2
    have h2 := InfLimit_msc_sub_mE hηpos hE2
    have h3 := InfLimit_mE_im_ge hκ hz.1
    have h4 : 0 < Real.sqrt (2 * κ) := by positivity
    have h5 : z.im / (mE z.re).im ≤ z.im / (Real.sqrt (2 * κ) / 2) :=
      div_le_div_of_nonneg_left hηpos.le (by positivity) h3
    have e : Kκ * z.im = 2 * (z.im / (Real.sqrt (2 * κ) / 2)) := by
      rw [hKκ]; field_simp; ring
    rw [e]
    linarith
  have hmain : ‖ThetaInf s (zlift x) - ThetaZd a s (zlift x)‖ ≤
      z.im / ((W : ℝ) ^ 4 * X ^ ((d : ℝ) - 4 - τ)) := by
    have h := hsub W hW5 s hs a ha0 ha1.le (zlift x)
    rw [hz0, ← hX] at h
    refine h.trans ?_
    have hKκ0 : 0 ≤ Kκ := by positivity
    have hCK : |C₅| * Kκ ≤ X ^ τ :=
      (InfLimit_le_rpow hτ (by positivity) hWC).trans
        (Real.rpow_le_rpow hW0.le hXW hτ.le)
    have e : X ^ ((d : ℝ) - 4 - τ) = X ^ (d - 4) / X ^ τ := by
      rw [Real.rpow_sub hX0, show (d : ℝ) - 4 = ((d - 4 : ℕ) : ℝ) by
        rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast]
    rw [e]
    have hXd : 0 < X ^ (d - 4) := by positivity
    have hXt : 0 < X ^ τ := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : C₅ * (1 - a) ≤ |C₅| * (Kκ * z.im) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C₅) (by linarith)).trans
        (mul_le_mul_of_nonneg_left h1a (abs_nonneg _))
    have h2 : |C₅| * (Kκ * z.im) ≤ X ^ τ * z.im := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCK hηpos.le
    have hW4 : 0 < (W : ℝ) ^ 4 := by positivity
    calc C₅ * (1 - a) * ((W : ℝ) ^ 4 * (X ^ (d - 4) / X ^ τ))
        = C₅ * (1 - a) * ((W : ℝ) ^ 4 * X ^ (d - 4)) / X ^ τ := by ring
      _ ≤ X ^ τ * z.im * ((W : ℝ) ^ 4 * X ^ (d - 4)) / X ^ τ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity))
            hXt.le
      _ = z.im * ((W : ℝ) ^ 4 * X ^ (d - 4)) := by field_simp
  -- the two small terms
  have hhalf : X ^ (-(D + 1)) ≤ X ^ (-D) / 2 := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hX0, Real.rpow_neg_one, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by norm_num) (hW2.trans hXW)) (by positivity)
  have hAbs := InfLimit_absorb (A := 2 * A) hL0 (hWA.trans hWL)
  have h2L' := InfLimit_two_L_rpow_le hW1 hWL hD.le x
  rw [← hX] at h2L'
  have htri : ‖ThetaInf s (zlift x) - (Theta (msc z) S 0 x : ℂ)‖ ≤
      ‖ThetaInf s (zlift x) - ThetaZd a s (zlift x)‖ +
        ‖periodize L (ThetaZd a s) x - ThetaZd a s (zlift x)‖ +
          ‖(Theta (msc z) S 0 x : ℂ) - periodize L (ThetaZd a s) x‖ := by
    have e : ThetaInf s (zlift x) - (Theta (msc z) S 0 x : ℂ) =
        (ThetaInf s (zlift x) - ThetaZd a s (zlift x)) -
          (periodize L (ThetaZd a s) x - ThetaZd a s (zlift x)) -
            ((Theta (msc z) S 0 x : ℂ) - periodize L (ThetaZd a s) x) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact norm_sub_le _ _
  have hAL : 0 ≤ A * (L : ℝ) ^ (-(D + 1)) := by positivity
  linarith

section Limit

variable {d : ℕ}

end Limit

section Witness

end Witness

end RBM8D
