import RBM8D.TExp.Defs
import RBM8D.Kernel.ThetaDecay
import RBM8D.Kernel.ZdCancel
import RBM8D.Profile.Symbol
import RBM8D.Input.Entry
import RBM8D.Input.Sizes
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Base
import RBM8D.Bound.GraphAbs
import RBM8D.Bound.AuxTree
import RBM8D.Bound.Chain
import RBM8D.Kernel.Decay

/-!
# Deterministic graphs ([I, Cor 6.12, 6.13] = [II, Lemma 8.5])
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

/-! ## Elementary facts on `⟨x - y⟩` and `B` -/

section Elem

/-- `⟨x - y⟩ > 0` for `W ≥ 1`. -/
private theorem brk_pos {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    0 < brk d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold brk; positivity

/-- `W ≤ ⟨x - y⟩`. -/
private theorem le_brk {d L W : ℕ} [NeZero L] (x y : Zd d L) : (W : ℝ) ≤ brk d L W x y := by
  unfold brk; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]

/-- `B_{xy} = W^{-2} ⟨x - y⟩^{-(d-2)}`. -/
private theorem bB_eq {d L W : ℕ} [NeZero L] (x y : Zd d L) :
    bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) := rfl

/-- `B_{xy} > 0` for `W ≥ 1`. -/
private theorem bB_pos {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    0 < bB d L W x y := by
  have := brk_pos (d := d) (L := L) hW x y
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  rw [bB_eq]; positivity

/-- `W^d B_{xy} = (W/⟨x - y⟩)^{d-2}`. -/
private theorem rpow_mul_bB_eq {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    (W : ℝ) ^ (d : ℝ) * bB d L W x y = ((W : ℝ) / brk d L W x y) ^ ((d : ℝ) - 2) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht := brk_pos (d := d) (L := L) hW x y
  rw [bB_eq, Real.div_rpow hW0.le ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le, ← mul_assoc,
    ← Real.rpow_add hW0]
  congr 2; ring

/-- `0 ≤ W^d B_{xy} ≤ 1` for `d ≥ 2`, `W ≥ 1`. -/
private theorem rpow_mul_bB_mem {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) :
    0 ≤ (W : ℝ) ^ (d : ℝ) * bB d L W x y ∧ (W : ℝ) ^ (d : ℝ) * bB d L W x y ≤ 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht := brk_pos (d := d) (L := L) hW x y
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [rpow_mul_bB_eq hW]
  refine ⟨by positivity, Real.rpow_le_one (by positivity) ((div_le_one ht).2 (le_brk x y))
    (by linarith)⟩

/-- `W^d B̃_{xy} = (W/⟨x - y⟩)^{d-4}` for `B̃_{xy} = W^{-4} ⟨x - y⟩^{-(d-4)}`. -/
private theorem rpow_mul_bT_eq {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    (W : ℝ) ^ (d : ℝ) * ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))) =
      ((W : ℝ) / brk d L W x y) ^ ((d : ℝ) - 4) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht := brk_pos (d := d) (L := L) hW x y
  rw [Real.div_rpow hW0.le ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le, ← mul_assoc,
    ← Real.rpow_add hW0]
  congr 2

/-- `0 ≤ W^d B̃_{xy} ≤ 1` for `d ≥ 4`, `W ≥ 1`. -/
private theorem rpow_mul_bT_mem {d L W : ℕ} [NeZero L] (hd : 4 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) :
    0 ≤ (W : ℝ) ^ (d : ℝ) * ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))) ∧
      (W : ℝ) ^ (d : ℝ) * ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))) ≤ 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht := brk_pos (d := d) (L := L) hW x y
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  rw [rpow_mul_bT_eq hW]
  refine ⟨by positivity, Real.rpow_le_one (by positivity) ((div_le_one ht).2 (le_brk x y))
    (by linarith)⟩

/-- `(W/t)^b = W^b t^{-b}` for `W, t > 0`. -/
private theorem div_rpow_eq {Wr t : ℝ} (hW : 0 < Wr) (ht : 0 < t) (b : ℝ) :
    (Wr / t) ^ b = Wr ^ b * t ^ (-b) := by
  rw [Real.div_rpow hW.le ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le]

/-- A strong norm is at most `1` when every weighted entry is. -/
private theorem strongNorm_le_one {d L W : ℕ} [NeZero L] (a b : ℝ)
    (A : Matrix (Zd d L) (Zd d L) ℝ)
    (h : ∀ x y, ((W : ℝ) / brk d L W x y) ^ b * brk d L W x y ^ (a * d / 2) * |A x y| ≤ 1) :
    strongNorm d L W a b A ≤ 1 :=
  Real.iSup_le (fun x => Real.iSup_le (fun y => h x y) zero_le_one) zero_le_one

/-- `‖B‖_{s;(2,4)} ≤ 1` for `W ≥ 1`: the weighted entries are `(W/⟨x - y⟩)²`. -/
private theorem strongNorm24_bB {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) :
    strongNorm d L W 2 4 (fun x y => bB d L W x y) ≤ 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  refine strongNorm_le_one 2 4 _ fun x y => ?_
  have ht := brk_pos (d := d) (L := L) hW x y
  have hB := bB_pos (d := d) (L := L) hW x y
  have e : ((W : ℝ) / brk d L W x y) ^ (4 : ℝ) * brk d L W x y ^ ((2 : ℝ) * d / 2) *
      |bB d L W x y| = ((W : ℝ) / brk d L W x y) ^ (2 : ℝ) := by
    rw [abs_of_pos hB, bB_eq, div_rpow_eq hW0 ht, div_rpow_eq hW0 ht]
    calc (W : ℝ) ^ (4 : ℝ) * brk d L W x y ^ (-(4 : ℝ)) * brk d L W x y ^ ((2 : ℝ) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)))
        = ((W : ℝ) ^ (4 : ℝ) * (W : ℝ) ^ (-2 : ℝ)) * (brk d L W x y ^ (-(4 : ℝ)) *
            brk d L W x y ^ ((2 : ℝ) * d / 2) * brk d L W x y ^ (2 - (d : ℝ))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add ht, ← Real.rpow_add ht]
        congr 2 <;> ring
  rw [e]
  exact Real.rpow_le_one (by positivity) ((div_le_one ht).2 (le_brk x y)) (by norm_num)

/-- `‖B̃‖_{s;(2,4)} ≤ 1` for `W ≥ 1`, `B̃_{xy} = W^{-4} ⟨x - y⟩^{-(d-4)}`: the weighted entries
are `1`. -/
private theorem strongNorm24_bT {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) :
    strongNorm d L W 2 4
      (fun x y => (W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))) ≤ 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  refine strongNorm_le_one 2 4 _ fun x y => le_of_eq ?_
  have ht := brk_pos (d := d) (L := L) hW x y
  rw [abs_of_pos (by positivity), div_rpow_eq hW0 ht]
  calc (W : ℝ) ^ (4 : ℝ) * brk d L W x y ^ (-(4 : ℝ)) * brk d L W x y ^ ((2 : ℝ) * d / 2) *
        ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4)))
      = ((W : ℝ) ^ (4 : ℝ) * (W : ℝ) ^ (-4 : ℝ)) * (brk d L W x y ^ (-(4 : ℝ)) *
          brk d L W x y ^ ((2 : ℝ) * d / 2) * brk d L W x y ^ (-((d : ℝ) - 4))) := by ring
    _ = 1 := by
      rw [← Real.rpow_add hW0, ← Real.rpow_add ht, ← Real.rpow_add ht]
      simp only [show (4 : ℝ) + -4 = 0 by norm_num,
        show -(4 : ℝ) + 2 * d / 2 + -((d : ℝ) - 4) = 0 by ring, Real.rpow_zero, mul_one]

end Elem

/-! ## Coefficients -/

/-- A coefficient is bounded in the bulk: there is `C` with `|p(m(z))| ≤ C` for every `z` with
`|Re z| < 2 - κ` and `0 < Im z ≤ 1`. -/
private theorem coeff_bound (κ : ℝ) (hκ : 0 < κ) (p : Coeff) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, 0 < z.im → |z.re| < 2 - κ → z.im ≤ 1 → ‖p.eval (msc z)‖ ≤ C := by
  set R : ℝ := 4 + 5 / Real.sqrt (2 * κ) with hRdef
  have hsq : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  have hR1 : 1 ≤ R := by
    have : 0 ≤ 5 / Real.sqrt (2 * κ) := by positivity
    linarith
  have hR : ∀ z : ℂ, 0 < z.im → |z.re| < 2 - κ → z.im ≤ 1 → ∀ v, ‖CVar.eval (msc z) v‖ ≤ R := by
    intro z hz hre him v
    obtain ⟨hm1, hm2⟩ := msc_bulk κ hκ z hz hre.le
    have hinv : ‖(msc z)⁻¹‖ ≤ 4 := by
      have h1 : (msc z)⁻¹ = -(msc z + z) := by rw [msc_add_eq_neg_inv]; ring
      rw [h1, norm_neg]
      have h2 := Complex.norm_le_abs_re_add_abs_im z
      have h3 : |z.im| ≤ 1 := by rw [abs_of_pos hz]; exact him
      have h4 : |z.re| ≤ 2 := by linarith
      calc ‖msc z + z‖ ≤ ‖msc z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 + (2 + 1) := by linarith
        _ = 4 := by norm_num
    have hr : ‖(1 - msc z ^ 2)⁻¹‖ ≤ 5 / Real.sqrt (2 * κ) := by
      rw [norm_inv]
      have hpos : 0 < ‖1 - msc z ^ 2‖ := lt_of_lt_of_le (by positivity) hm2
      rw [inv_le_comm₀ hpos (by positivity)]
      calc (5 / Real.sqrt (2 * κ))⁻¹ = Real.sqrt (2 * κ) / 5 := by rw [inv_div]
        _ ≤ ‖1 - msc z ^ 2‖ := hm2
    have h5 : (0 : ℝ) ≤ 5 / Real.sqrt (2 * κ) := by positivity
    cases v with
    | m => simp only [CVar.eval]; linarith
    | mInv => simp only [CVar.eval]; linarith
    | r => simp only [CVar.eval]; linarith
    | mBar => simp only [CVar.eval, norm_star]; linarith
    | mBarInv => simp only [CVar.eval, norm_inv, norm_star]; rw [← norm_inv]; linarith
    | rBar =>
      simp only [CVar.eval]
      have : (1 - star (msc z) ^ 2) = star (1 - msc z ^ 2) := by simp [star_sub, star_pow]
      rw [this, norm_inv, norm_star, ← norm_inv]; linarith
  refine ⟨∑ s ∈ p.support, ‖p.coeff s‖ * ∏ i ∈ s.support, R ^ s i, by positivity,
    fun z hz hre him => ?_⟩
  unfold Coeff.eval
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul, norm_prod]
  gcongr with i
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hR z hz hre him i) _

/-! ## Waved edges -/

section Wave

/-- `t^{-D} ≤ W^{-d} (W/t)^e` for `t ≥ W ≥ 1` and `e ≤ D`, `d ≤ D`. -/
private theorem tail_le (d : ℕ) (Wr t e D : ℝ) (hW : 1 ≤ Wr) (ht : Wr ≤ t) (hdD : (d : ℝ) ≤ D)
    (he : e ≤ D) :
    t ^ (-D) ≤ Wr ^ (-(d : ℝ)) * (Wr / t) ^ e := by
  have hW0 : 0 < Wr := by linarith
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < Wr / t := by positivity
  have hu1 : Wr / t ≤ 1 := (div_le_one ht0).2 ht
  have h1 : (Wr / t) ^ D ≤ (Wr / t) ^ e := Real.rpow_le_rpow_of_exponent_ge hu0 hu1 he
  have h2 : t ^ (-D) ≤ Wr ^ (-(d : ℝ)) * (Wr / t) ^ D := by
    rw [Real.div_rpow hW0.le ht0.le, Real.rpow_neg ht0.le, ← mul_div_assoc, div_eq_mul_inv,
      ← Real.rpow_add hW0]
    have : 1 ≤ Wr ^ (-(d : ℝ) + D) := Real.one_le_rpow hW (by linarith)
    have hp : 0 < (t ^ D)⁻¹ := by positivity
    nlinarith
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))

/-- From [I, (1.8)] with `k = 0` and `k = 2d`: `|f_{W,L}(x)| ≤ (|C₀| + |C_k|) 2^{2d} W^{-d}
(W/⟨x⟩)^{2d}`, with `⟨x⟩ = ‖x‖_L + W`. -/
private theorem f_le_of_subpoly {d W : ℕ} (hW1n : 1 ≤ W) (f : ℝ) (r C0 Ck : ℝ) (hr0 : 0 ≤ r)
    (h0 : f ≤ C0 / (W : ℝ) ^ d) (hk : (r / W) ^ (2 * d) * f ≤ Ck / (W : ℝ) ^ d) (hf : 0 ≤ f) :
    f ≤ (|C0| + |Ck|) * 2 ^ (2 * d) * ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) / (r + W)) ^ (2 * d) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have ht : 0 < r + W := by linarith
  set u := (W : ℝ) / (r + W) with hu
  have hu0 : 0 ≤ u := by positivity
  have hWi : 0 < ((W : ℝ) ^ d)⁻¹ := by positivity
  have hA : 0 ≤ |C0| * 2 ^ (2 * d) * ((W : ℝ) ^ d)⁻¹ * u ^ (2 * d) := by positivity
  have hB : 0 ≤ |Ck| * 2 ^ (2 * d) * ((W : ℝ) ^ d)⁻¹ * u ^ (2 * d) := by positivity
  have hsplit : (|C0| + |Ck|) * 2 ^ (2 * d) * ((W : ℝ) ^ d)⁻¹ * u ^ (2 * d) =
      |C0| * 2 ^ (2 * d) * ((W : ℝ) ^ d)⁻¹ * u ^ (2 * d) +
        |Ck| * 2 ^ (2 * d) * ((W : ℝ) ^ d)⁻¹ * u ^ (2 * d) := by ring
  rw [hsplit]
  by_cases hrW : r ≤ W
  · have hu2 : 1 ≤ 2 * u := by
      rw [hu, ← mul_div_assoc, le_div_iff₀ ht]; linarith
    have hu2' : 1 ≤ 2 ^ (2 * d) * u ^ (2 * d) := by
      rw [← mul_pow]; exact one_le_pow₀ hu2
    have h1 : f ≤ |C0| * ((W : ℝ) ^ d)⁻¹ := by
      rw [div_eq_mul_inv] at h0
      exact h0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hWi.le)
    have h2 : |C0| * ((W : ℝ) ^ d)⁻¹ ≤ |C0| * 2 ^ (2 * d) * ((W : ℝ) ^ d)⁻¹ * u ^ (2 * d) := by
      calc |C0| * ((W : ℝ) ^ d)⁻¹ ≤ |C0| * ((W : ℝ) ^ d)⁻¹ * (2 ^ (2 * d) * u ^ (2 * d)) :=
            le_mul_of_one_le_right (by positivity) hu2'
        _ = _ := by ring
    linarith
  · push Not at hrW
    have hru : 1 ≤ (r / W) * (2 * u) := by
      have h' : (r / W) * (2 * u) = 2 * r / (r + W) := by rw [hu]; field_simp
      rw [h', le_div_iff₀ ht]; linarith
    have hru' : 1 ≤ (r / W) ^ (2 * d) * (2 * u) ^ (2 * d) := by
      rw [← mul_pow]; exact one_le_pow₀ hru
    have h1 : f ≤ (r / W) ^ (2 * d) * f * (2 * u) ^ (2 * d) := by
      calc f ≤ f * ((r / W) ^ (2 * d) * (2 * u) ^ (2 * d)) := le_mul_of_one_le_right hf hru'
        _ = _ := by ring
    have h2 : (r / W) ^ (2 * d) * f * (2 * u) ^ (2 * d) ≤ Ck / (W : ℝ) ^ d * (2 * u) ^ (2 * d) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    have h3 : Ck / (W : ℝ) ^ d * (2 * u) ^ (2 * d) ≤
        |Ck| * 2 ^ (2 * d) * ((W : ℝ) ^ d)⁻¹ * u ^ (2 * d) := by
      rw [div_eq_mul_inv, mul_pow]
      have : Ck * ((W : ℝ) ^ d)⁻¹ ≤ |Ck| * ((W : ℝ) ^ d)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hWi.le
      calc Ck * ((W : ℝ) ^ d)⁻¹ * (2 ^ (2 * d) * u ^ (2 * d))
          ≤ |Ck| * ((W : ℝ) ^ d)⁻¹ * (2 ^ (2 * d) * u ^ (2 * d)) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring
    linarith

/-- The near part of `splusBound`: `W^{-d} ≤ 2^e W^τ W^{-d} (W/t)^e` when
`t = r + W ≤ W + W^{1+τ'}` and `τ' e ≤ τ`. -/
private theorem near_le (Wr t r τ τ' e : ℝ) (hW : 1 ≤ Wr) (hr0 : 0 ≤ r) (htr : t = r + Wr)
    (hr : r ≤ Wr ^ (1 + τ')) (hτ' : 0 ≤ τ') (he0 : 0 ≤ e) (hτ'e : τ' * e ≤ τ) (Wd : ℝ)
    (hWd : 0 ≤ Wd) :
    Wd ≤ 2 ^ e * Wr ^ τ * (Wd * (Wr / t) ^ e) := by
  have hW0 : 0 < Wr := by linarith
  have h1τ : 1 ≤ Wr ^ τ' := Real.one_le_rpow hW hτ'
  have hWτ' : Wr ^ (1 + τ') = Wr * Wr ^ τ' := by rw [Real.rpow_add hW0, Real.rpow_one]
  have ht : 0 < t := by linarith
  have htle : t ≤ 2 * Wr * Wr ^ τ' := by rw [htr]; nlinarith
  have h2u : 1 ≤ 2 * Wr ^ τ' * (Wr / t) := by
    rw [← mul_div_assoc, le_div_iff₀ ht]; linarith
  have h2ue : 1 ≤ (2 * Wr ^ τ' * (Wr / t)) ^ e := Real.one_le_rpow h2u he0
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hW0.le] at h2ue
  have hle : Wr ^ (τ' * e) ≤ Wr ^ τ := Real.rpow_le_rpow_of_exponent_le hW hτ'e
  calc Wd ≤ Wd * (2 ^ e * Wr ^ (τ' * e) * (Wr / t) ^ e) := le_mul_of_one_le_right hWd h2ue
    _ ≤ Wd * (2 ^ e * Wr ^ τ * (Wr / t) ^ e) := by gcongr
    _ = _ := by ring

/-- [I, Lemma 2.2] for the waved edges `S^±` at `D = 2d`: `splusBound ≤ (2^e + 1) W^τ X`, with
`X = W^{-d} (W/⟨x - y⟩)^e`, for `0 ≤ e ≤ 2d` and `τ' e ≤ τ`. -/
private theorem splusBound_le {d L W : ℕ} [NeZero L] (hW1n : 1 ≤ W) (τ τ' e : ℝ) (hτ : 0 ≤ τ)
    (hτ' : 0 ≤ τ') (he0 : 0 ≤ e) (he2 : e ≤ 2 * (d : ℝ)) (hτ'e : τ' * e ≤ τ) (p q : Zd d L) :
    splusBound W τ' (2 * (d : ℝ)) p q ≤ (2 ^ e + 1) * (W : ℝ) ^ τ *
      ((W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ e) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have htt : (zdistInf d L (p - q) : ℝ) + W = brk d L W p q := rfl
  set t := brk d L W p q with htdef
  have hWt : (W : ℝ) ≤ t := le_brk p q
  set X := (W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / t) ^ e with hX
  have hX0 : 0 ≤ X := by
    have : 0 < t := by linarith
    positivity
  have hWτ : 1 ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ
  unfold splusBound
  rw [htt]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have htail : t ^ (-(2 * (d : ℝ))) ≤ X :=
    tail_le d (W : ℝ) t e (2 * (d : ℝ)) hW1 hWt (by linarith) he2
  have hnear : (if (zdistInf d L (p - q) : ℝ) ≤ (W : ℝ) ^ (1 + τ') then ((W : ℝ) ^ d)⁻¹ else 0)
      ≤ 2 ^ e * (W : ℝ) ^ τ * X := by
    split_ifs with hr
    · have hWd : (W : ℝ) ^ (-(d : ℝ)) = ((W : ℝ) ^ d)⁻¹ := by
        rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
      rw [hX, hWd]
      exact near_le (W : ℝ) t _ τ τ' e hW1 (Nat.cast_nonneg _) htt.symm hr hτ' he0 hτ'e _
        (by positivity)
    · positivity
  have h3 : X ≤ (W : ℝ) ^ τ * X := le_mul_of_one_le_left hX0 hWτ
  have h4 : (2 ^ e + 1) * (W : ℝ) ^ τ * X = 2 ^ e * (W : ℝ) ^ τ * X + (W : ℝ) ^ τ * X := by ring
  rw [h4]
  linarith

/-- [I, (1.8)] and [I, Lemma 2.2] for the waved edges: for every `τ > 0` there are `K ≥ 1` and
`W₀` such that along `adm(c₀, c₁)`, for `W ≥ W₀` and `z` in the bulk,
`|s_{xy}|, |S^±_{xy}| ≤ K W^τ W^{-d} (W/⟨x - y⟩)^{2(d-2)} = K W^τ W^d B_{xy}²`. -/
private theorem wave_bound (d : ℕ) (hd : 2 ≤ d) (P : Profile d) (c₀ c₁ κ : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ K W₀ : ℝ, 1 ≤ K ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → 1 ≤ W →
      ∀ z : ℂ, 0 < z.im → |z.re| < 2 - κ → ∀ p q : Zd d L,
        ‖cmat (Smat P.ψ W L) p q‖ ≤ K * (W : ℝ) ^ τ *
            ((W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ (2 * ((d : ℝ) - 2))) ∧
        ‖Splus (msc z) (Smat P.ψ W L) p q‖ ≤ K * (W : ℝ) ^ τ *
            ((W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ (2 * ((d : ℝ) - 2))) ∧
        ‖Sminus (msc z) (Smat P.ψ W L) p q‖ ≤ K * (W : ℝ) ^ τ *
            ((W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ (2 * ((d : ℝ) - 2))) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set e : ℝ := 2 * ((d : ℝ) - 2) with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  have he2 : e ≤ 2 * (d : ℝ) := by rw [he]; linarith
  set τ' : ℝ := τ / (e + 1) with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'e : τ' * e ≤ τ := by
    rw [hτ', div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨C0, hC0⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨Ck, hCk⟩ := subpoly_adm d P c₀ c₁ hc₀ (2 * d)
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨C, hC⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨W₁, h1⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨Ks, W₂, hS⟩ := Splus_decay_msc d c₀ c₁ hc₀ hc₁ P.ψ c' hc' C κ τ' (2 * (d : ℝ)) hκ
    hτ'0 (by linarith)
  set K₁ : ℝ := (|C0| + |Ck|) * 2 ^ (2 * d) with hK₁
  set K₂ : ℝ := |Ks| * (2 ^ e + 1) with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨1 + K₁ + K₂, max W₁ W₂, by linarith, fun W L _ hadm hW hW1n z hz hre p q => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have ht := brk_pos (d := d) (L := L) hW1n p q
  set X := (W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ e with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hWτ : 1 ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have hτX : X ≤ (W : ℝ) ^ τ * X := le_mul_of_one_le_left hX0 hWτ
  have hfin : ∀ v : ℝ, (v ≤ K₁ * X ∨ v ≤ K₂ * ((W : ℝ) ^ τ * X)) →
      v ≤ (1 + K₁ + K₂) * (W : ℝ) ^ τ * X := by
    intro v hv
    have e1 : (1 + K₁ + K₂) * (W : ℝ) ^ τ * X =
        (W : ℝ) ^ τ * X + K₁ * ((W : ℝ) ^ τ * X) + K₂ * ((W : ℝ) ^ τ * X) := by ring
    have e2 : K₁ * X ≤ K₁ * ((W : ℝ) ^ τ * X) := mul_le_mul_of_nonneg_left hτX hK₁0
    have e3 : 0 ≤ K₁ * ((W : ℝ) ^ τ * X) := by positivity
    have e4 : 0 ≤ K₂ * ((W : ℝ) ^ τ * X) := by positivity
    have e5 : 0 ≤ (W : ℝ) ^ τ * X := by positivity
    rw [e1]
    rcases hv with hv | hv <;> linarith
  -- the variance entries
  have hs : ‖cmat (Smat P.ψ W L) p q‖ ≤ K₁ * X := by
    have hval : ‖cmat (Smat P.ψ W L) p q‖ = |fWL P.ψ W L (p - q)| := by
      simp [cmat, Smat, Complex.norm_real, Real.norm_eq_abs]
    have h0 := hC0 W L hadm (p - q)
    rw [pow_zero, one_mul] at h0
    have key := f_le_of_subpoly (d := d) hW1n _ _ C0 Ck (Nat.cast_nonneg _) h0
      (hCk W L hadm (p - q)) (abs_nonneg _)
    have htt : (zdistInf d L (p - q) : ℝ) + W = brk d L W p q := rfl
    rw [htt] at key
    have hu0 : 0 < (W : ℝ) / brk d L W p q := by positivity
    have hu1 : (W : ℝ) / brk d L W p q ≤ 1 := (div_le_one ht).2 (le_brk p q)
    have hupow : ((W : ℝ) / brk d L W p q) ^ (2 * d) ≤ ((W : ℝ) / brk d L W p q) ^ e := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by push_cast; linarith)
    have hWd : (W : ℝ) ^ (-(d : ℝ)) = ((W : ℝ) ^ d)⁻¹ := by
      rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
    rw [hval, hXdef, hWd]
    calc |fWL P.ψ W L (p - q)| ≤ K₁ * ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) / brk d L W p q) ^ (2 * d) := key
      _ ≤ K₁ * ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) / brk d L W p q) ^ e :=
          mul_le_mul_of_nonneg_left hupow (by positivity)
      _ = _ := by ring
  have hsb := splusBound_le (L := L) hW1n τ τ' e hτ.le hτ'0.le he0 he2 hτ'e p q
  have hsb0 : 0 ≤ splusBound W τ' (2 * (d : ℝ)) p q := by unfold splusBound; positivity
  have hKs : ∀ v : ℝ, v ≤ Ks * splusBound W τ' (2 * (d : ℝ)) p q → v ≤ K₂ * ((W : ℝ) ^ τ * X) := by
    intro v hv
    have h1 : Ks * splusBound W τ' (2 * (d : ℝ)) p q ≤ |Ks| * ((2 ^ e + 1) * (W : ℝ) ^ τ * X) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hsb0).trans
        (mul_le_mul_of_nonneg_left hsb (abs_nonneg _))
    have h2 : |Ks| * ((2 ^ e + 1) * (W : ℝ) ^ τ * X) = K₂ * ((W : ℝ) ^ τ * X) := by ring
    linarith
  obtain ⟨hp, hm⟩ := hS W L hadm (le_trans (le_max_right _ _) hW) _
    (h1 W L hadm (le_trans (le_max_left _ _) hW)) (hC W L hadm) z hz hre p q
  exact ⟨hfin _ (Or.inl hs), hfin _ (Or.inr (hKs _ hp)), hfin _ (Or.inr (hKs _ hm))⟩

/-- `W^{-d} (W/⟨x - y⟩)^{2(d-2)} = W^{-d} (W^d B_{xy})²`. -/
private theorem wave_shape {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (p q : Zd d L) :
    (W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ (2 * ((d : ℝ) - 2)) =
      (W : ℝ) ^ (-(d : ℝ)) * (((W : ℝ) ^ (d : ℝ) * bB d L W p q) *
        ((W : ℝ) ^ (d : ℝ) * bB d L W p q)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht := brk_pos (d := d) (L := L) hW p q
  rw [rpow_mul_bB_eq hW, ← Real.rpow_add (by positivity)]
  congr 2; ring

end Wave

/-! ## Bounds on one component -/

/-- The bound of one component with ends labelled `p`, `q` and scaling order `q₀`:
`K W^{-q₀ d/2}` times `W^d B_{pq}` on a black edge and `W^d |A_j(p, q)|` on a blue edge. -/
private def compBnd (d L W : ℕ) [NeZero L] (K : ℝ) (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (j : ℕ)
    (q₀ : ℝ) (p q : Zd d L) (bk bu : Prop) [Decidable bk] [Decidable bu] : ℝ :=
  K * (W : ℝ) ^ (-q₀ * d / 2) * (if bk then (W : ℝ) ^ (d : ℝ) * bB d L W p q else 1) *
    (if bu then (W : ℝ) ^ (d : ℝ) * |A j p q| else 1)

/-- A component in at most one of the two trees: from `v ≤ P c` and, on a black edge,
`v ≤ P a`, with `a, c ∈ [0, 1]`, the value `v` is at most `P` times its black and blue factors. -/
private theorem flag_one (v P a c : ℝ) (hP : 0 ≤ P) (hc1 : c ≤ 1) (bk bu : Prop) [Decidable bk]
    [Decidable bu] (hv : v ≤ P * c) (hvb : bk → v ≤ P * a) (hboth : bk → bu → False) :
    v ≤ P * (if bk then a else 1) * (if bu then c else 1) := by
  split_ifs with h1 h2
  · exact (hboth h1 h2).elim
  · simpa using hvb h1
  · simpa using hv
  · calc v ≤ P * c := hv
      _ ≤ P * 1 := mul_le_mul_of_nonneg_left hc1 hP
      _ = _ := by ring

/-- A waved edge, possibly in both trees: from `v ≤ P a²` with `a ∈ [0, 1]`, the value `v` is at
most `P` times its black and blue factors, both equal to `a`. -/
private theorem flag_two (v P a : ℝ) (hP : 0 ≤ P) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (bk bu : Prop)
    [Decidable bk] [Decidable bu] (hv : v ≤ P * (a * a)) :
    v ≤ P * (if bk then a else 1) * (if bu then a else 1) := by
  have haa : a * a ≤ a := by nlinarith
  have ha1' : a * a ≤ 1 := by nlinarith
  have h1 : P * (a * a) ≤ P * a := mul_le_mul_of_nonneg_left haa hP
  have h2 : P * (a * a) ≤ P * 1 := mul_le_mul_of_nonneg_left ha1' hP
  split_ifs
  · linarith [show P * (a * a) = P * a * a by ring]
  · linarith [show P * a * 1 = P * a by ring]
  · linarith [show P * 1 * a = P * a by ring]
  · linarith [show P * 1 * 1 = P * 1 by ring]

/-- The waved edges at the labelling `id`: their values are the entries of `s`, `S^+`, `S^-`. -/
private theorem waved_val {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) (w : Wave)
    {V : Type*} (σ : V → ι) (x y : V) (mi : List V) (lab : Option (PQ × V)) :
    Comp.val D σ (⟨.waved w, x, y, mi, lab⟩ : Comp V) =
      Comp.val D id (mkC (.waved w) (σ x) (σ y) : Comp ι) := by
  cases w <;> rfl

/-- The bound of one component of a deterministic graph ([II, Def 2.7 (i)]) without dotted edge,
from the bounds on the waved edges and on the labelled `Θ` edges, the blue matrices being `B`. -/
private theorem comp_det {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (D : Data (Zd d L))
    (N : ℕ) (K : ℝ) (hK : 1 ≤ K)
    (hwav : ∀ (w : Wave) (p q : Zd d L), ‖Comp.val D id (mkC (.waved w) p q : Comp (Zd d L))‖ ≤
      K * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ (d : ℝ) * bB d L W p q) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q)))
    {V : Type*} (σ : V → Zd d L) (c : Comp V)
    (hth : ∀ o, c.kind = .theta o → ∀ p q, ‖D.chain o p q‖ ≤
      K * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q))
    (hc : c.isDetKind N = true) (hdot : c.kind ≠ .dot) (bk bu : Prop) [Decidable bk]
    [Decidable bu] (hbk : bk → c.kind.isDiffusive = true ∨ ∃ w, c.kind = .waved w)
    (hbu : bu → c.kind.isDiffusive = true ∨ c.kind.isBlue = true ∨ ∃ w, c.kind = .waved w)
    (hboth : bk → bu → ∃ w, c.kind = .waved w) :
    ‖Comp.val D σ c‖ ≤ compBnd d L W K (fun _ p q => bB d L W p q) 0 (c.kind.ord : ℝ)
      (σ c.x) (σ c.y) bk bu := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨κ, x, y, mi, lab⟩ := c
  have ha := rpow_mul_bB_mem hd hW (σ x) (σ y)
  have hB0 := (bB_pos hW (σ x) (σ y)).le
  unfold compBnd
  simp only [abs_of_nonneg hB0]
  cases κ with
  | waved w =>
    rw [waved_val]
    have hord : (((Kind.waved w).ord : ℤ) : ℝ) = 2 := by simp [Kind.ord]
    simp only [hord]
    exact flag_two _ _ _ (by positivity) ha.1 ha.2 bk bu (hwav w _ _)
  | theta o =>
    have hval : Comp.val D σ (⟨.theta o, x, y, mi, lab⟩ : Comp V) = D.chain o (σ x) (σ y) := rfl
    rw [hval]
    have h := hth o rfl (σ x) (σ y)
    exact flag_one _ _ _ _ (by positivity) ha.2 bk bu h (fun _ => h)
      (fun h1 h2 => by obtain ⟨w, hw⟩ := hboth h1 h2; cases hw)
  | xdot =>
    have hbk' : ¬ bk := fun h => by
      rcases hbk h with h' | ⟨w, hw⟩
      · simp [Kind.isDiffusive] at h'
      · cases hw
    have hbu' : ¬ bu := fun h => by
      rcases hbu h with h' | h' | ⟨w, hw⟩
      · simp [Kind.isDiffusive] at h'
      · simp [Kind.isBlue] at h'
      · cases hw
    have hval : ‖Comp.val D σ (⟨.xdot, x, y, mi, lab⟩ : Comp V)‖ ≤ 1 := by
      simp only [Comp.val]
      split_ifs <;> simp
    simp only [hbk', hbu', ↓reduceIte, mul_one]
    have hord : ((Kind.xdot.ord : ℤ) : ℝ) = 0 := by simp [Kind.ord]
    rw [hord]
    simp only [neg_zero, zero_mul, zero_div, Real.rpow_zero, mul_one]
    linarith
  | dot => exact (hdot rfl).elim
  | G _ => simp [Comp.isDetKind] at hc
  | weight _ => simp [Comp.isDetKind] at hc
  | light _ => simp [Comp.isDetKind] at hc
  | inv _ => simp [Comp.isDetKind] at hc
  | wD _ _ => simp [Comp.isDetKind] at hc
  | thetaErr _ _ => simp [Comp.isDetKind] at hc
  | ghost => simp [Comp.isDetKind] at hc
  | aux _ _ _ => simp [Comp.isDetKind] at hc

/-- The index of the blue matrix of a component: `t j` for an auxiliary edge of index `j`, `0`
otherwise. -/
private def cidx {V : Type*} (t : ℕ → ℕ) (c : Comp V) : ℕ :=
  match c.kind with
  | .aux j _ _ => t j
  | _ => 0

/-- The bound of one component of a graph of [I, Cor 6.13] (waved and diffusive auxiliary edges of
order `2`), from the bounds on the waved edges and on the auxiliary matrices: the blue matrix of
the auxiliary edge of index `j` is `A_{t j}`, that of a waved edge is `A_0 = B`; on a black edge
the blue index is `0`. -/
private theorem comp_aux {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (D : Data (Zd d L))
    (K : ℝ) (hK : 1 ≤ K) (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (t : ℕ → ℕ)
    (hA0 : ∀ p q, A 0 p q = bB d L W p q)
    (hA1 : ∀ j p q, (W : ℝ) ^ (d : ℝ) * |A j p q| ≤ 1)
    (hwav : ∀ (w : Wave) (p q : Zd d L), ‖Comp.val D id (mkC (.waved w) p q : Comp (Zd d L))‖ ≤
      K * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ (d : ℝ) * bB d L W p q) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q)))
    (haux : ∀ j p q, ‖D.aux j p q‖ ≤
      K * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * ((W : ℝ) ^ (d : ℝ) * |A (t j) p q|))
    {V : Type*} (σ : V → Zd d L) (c : Comp V) (hc : c.isBKind = true) (bk bu : Prop)
    [Decidable bk] [Decidable bu] (hbk0 : bk → cidx t c = 0)
    (hboth : bk → bu → ∃ w, c.kind = .waved w) :
    ‖Comp.val D σ c‖ ≤ compBnd d L W K A (cidx t c) (c.kind.ord : ℝ) (σ c.x) (σ c.y) bk bu := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨κ, x, y, mi, lab⟩ := c
  have ha := rpow_mul_bB_mem hd hW (σ x) (σ y)
  have hB0 := (bB_pos hW (σ x) (σ y)).le
  unfold compBnd
  cases κ with
  | waved w =>
    rw [waved_val]
    have hord : (((Kind.waved w).ord : ℤ) : ℝ) = 2 := by simp [Kind.ord]
    have hc0 : cidx t (⟨.waved w, x, y, mi, lab⟩ : Comp V) = 0 := rfl
    simp only [hord, hc0, hA0, abs_of_nonneg hB0]
    exact flag_two _ _ _ (by positivity) ha.1 ha.2 bk bu (hwav w _ _)
  | aux j r b =>
    have hr : r = 2 := by
      simp only [Graphs.Comp.isBKind, Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.2.1
    subst hr
    have hval : Comp.val D σ (⟨.aux j 2 b, x, y, mi, lab⟩ : Comp V) = D.aux j (σ x) (σ y) := rfl
    have hord : (((Kind.aux j 2 b).ord : ℤ) : ℝ) = 2 := by simp [Kind.ord]
    have hci : cidx t (⟨.aux j 2 b, x, y, mi, lab⟩ : Comp V) = t j := rfl
    rw [hval]
    simp only [hord, hci]
    have h := haux j (σ x) (σ y)
    refine flag_one _ _ _ _ (by positivity) (hA1 _ _ _) bk bu h (fun h1 => ?_)
      (fun h1 h2 => by obtain ⟨w, hw⟩ := hboth h1 h2; cases hw)
    have h0 : t j = 0 := hbk0 h1
    rw [h0, hA0, abs_of_nonneg hB0] at h
    exact h
  | dot => simp [Graphs.Comp.isBKind] at hc
  | xdot => simp [Graphs.Comp.isBKind] at hc
  | theta _ => simp [Graphs.Comp.isBKind] at hc
  | G _ => simp [Graphs.Comp.isBKind] at hc
  | weight _ => simp [Graphs.Comp.isBKind] at hc
  | light _ => simp [Graphs.Comp.isBKind] at hc
  | inv _ => simp [Graphs.Comp.isBKind] at hc
  | wD _ _ => simp [Graphs.Comp.isBKind] at hc
  | thetaErr _ _ => simp [Graphs.Comp.isBKind] at hc
  | ghost => simp [Graphs.Comp.isBKind] at hc

/-! ## The product over the components -/

/-- `(Π_{i ∈ l} c f(i)) = c^{|l|} Π_{i ∈ l} f(i)`. -/
private theorem list_prod_map_const_mul {ι : Type*} (l : List ι) (c : ℝ) (f : ι → ℝ) :
    (l.map fun i => c * f i).prod = c ^ l.length * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]; ring

/-- The product of the bounds `compBnd` over the components factors into the constant part, the
black edges and the blue edges. -/
private theorem prod_compBnd {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (K : ℝ)
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) {k n : ℕ} (Γ : Graph k n) (idx : Comp (Atom k n) → ℕ)
    (bl bu : List (Fin Γ.comps.length)) (hbl : bl.Nodup) (hbu : bu.Nodup)
    (σ : Atom k n → Zd d L) :
    ∏ i : Fin Γ.comps.length, compBnd d L W K A (idx Γ.comps[i]) (Γ.comps[i].kind.ord : ℝ)
        (σ Γ.comps[i].x) (σ Γ.comps[i].y) (i ∈ bl) (i ∈ bu) =
      K ^ Γ.comps.length *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length) *
        ((bl.map fun i => bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y)).prod *
          (bu.map fun i => |A (idx Γ.comps[i]) (σ Γ.comps[i].x) (σ Γ.comps[i].y)|).prod) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold compBnd
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have h1 : ∏ i : Fin Γ.comps.length, (if i ∈ bl then (W : ℝ) ^ (d : ℝ) *
      bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y) else 1) =
      ((W : ℝ) ^ (d : ℝ)) ^ bl.length *
        (bl.map fun i => bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y)).prod := by
    simp_rw [← List.mem_toFinset (l := bl)]
    rw [Finset.prod_ite_mem, Finset.univ_inter, List.prod_toFinset _ hbl, list_prod_map_const_mul]
  have h2 : ∏ i : Fin Γ.comps.length, (if i ∈ bu then (W : ℝ) ^ (d : ℝ) *
      |A (idx Γ.comps[i]) (σ Γ.comps[i].x) (σ Γ.comps[i].y)| else 1) =
      ((W : ℝ) ^ (d : ℝ)) ^ bu.length *
        (bu.map fun i => |A (idx Γ.comps[i]) (σ Γ.comps[i].x) (σ Γ.comps[i].y)|).prod := by
    simp_rw [← List.mem_toFinset (l := bu)]
    rw [Finset.prod_ite_mem, Finset.univ_inter, List.prod_toFinset _ hbu, list_prod_map_const_mul]
  rw [h1, h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_sum_of_pos hW0]
  ring

/-- The absolute-value graph is at most `|coeff| K^{|Γ|} W^{-Σ q d/2} (W^d)^{|bl|} (W^d)^{|bu|}`
times the sum over the internal labels of the product of `B` over the black edges and of `|A_j|`
over the blue edges, when every component is bounded by `compBnd` at every labelling. -/
private theorem absVal_le {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) {k n : ℕ} (Γ : Graph k n)
    (D : Data (Zd d L)) (K : ℝ) (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ)
    (idx : Comp (Atom k n) → ℕ) (bl bu : List (Fin Γ.comps.length)) (hbl : bl.Nodup)
    (hbu : bu.Nodup)
    (hcomp : ∀ (σ : Atom k n → Zd d L) (i : Fin Γ.comps.length), ‖Comp.val D σ Γ.comps[i]‖ ≤
      compBnd d L W K A (idx Γ.comps[i]) (Γ.comps[i].kind.ord : ℝ) (σ Γ.comps[i].x)
        (σ Γ.comps[i].y) (i ∈ bl) (i ∈ bu))
    (e : Fin k → Zd d L) :
    Γ.absVal D e ≤ ‖Γ.coeff.eval D.m‖ * (K ^ Γ.comps.length *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length)) *
      ∑ s : Fin n → Zd d L,
        ((bl.map fun i => bB d L W (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y)).prod *
          (bu.map fun i => |A (idx Γ.comps[i]) (Sum.elim e s Γ.comps[i].x)
            (Sum.elim e s Γ.comps[i].y)|).prod) := by
  unfold Graph.absVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 : (Γ.comps.map fun c => ‖Comp.val D (Sum.elim e s) c‖).prod ≤
      ∏ i : Fin Γ.comps.length, compBnd d L W K A (idx Γ.comps[i]) (Γ.comps[i].kind.ord : ℝ)
        (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y) (i ∈ bl) (i ∈ bu) := by
    rw [← Fin.prod_univ_fun_getElem]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hcomp _ i)
  rw [prod_compBnd hW K A Γ idx bl bu hbl hbu (Sum.elim e s)] at h1
  calc ‖Γ.coeff.eval D.m‖ * (Γ.comps.map fun c => ‖Comp.val D (Sum.elim e s) c‖).prod
      ≤ ‖Γ.coeff.eval D.m‖ * _ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := by ring

/-! ## Spanning trees from the doubly connected property -/

/-- A reachability in `G₁` maps to a reachability in `G₂` under `ψ` if every edge does. -/
private theorem reach_lift {X Y : Type*} {G₁ : SimpleGraph X} {G₂ : SimpleGraph Y} (ψ : X → Y)
    (h : ∀ x y, G₁.Adj x y → G₂.Reachable (ψ x) (ψ y)) {x y : X} (hr : G₁.Reachable x y) :
    G₂.Reachable (ψ x) (ψ y) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- A connected graph whose edges are given by indices in `S` contains a spanning tree of indexed
edges: a list of distinct indices in `S` whose edges form a spanning tree. -/
private theorem exists_tree {V ι : Type*} [Fintype V] (e : ι → V × V) (S : Set ι)
    (h : (SimpleGraph.fromRel fun u v => ∃ i ∈ S, e i = (u, v)).Connected) :
    ∃ l : List ι, l.Nodup ∧ (∀ i ∈ l, i ∈ S) ∧ TreeEdges (l.map e) := by
  classical
  obtain ⟨T, hTle, hT⟩ := h.exists_isTree_le
  have hreal : ∀ t ∈ T.edgeFinset, ∃ i ∈ S, s((e i).1, (e i).2) = t := by
    intro t ht
    induction t using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at ht
      have h1 := hTle ht
      rw [SimpleGraph.fromRel_adj] at h1
      rcases h1.2 with ⟨i, hi, he⟩ | ⟨i, hi, he⟩
      · exact ⟨i, hi, by rw [he]⟩
      · exact ⟨i, hi, by rw [he, Sym2.eq_swap]⟩
  choose idx hidxS hidx using hreal
  set l := T.edgeFinset.toList.pmap idx (fun t ht => Finset.mem_toList.1 ht) with hl
  refine ⟨l, ?_, ?_, ?_, ?_⟩
  · refine (Finset.nodup_toList _).pmap fun a ha b hb hab => ?_
    rw [← hidx a ha, ← hidx b hb, hab]
  · intro i hi
    obtain ⟨t, ht, rfl⟩ := List.mem_pmap.1 hi
    exact hidxS t _
  · rw [List.length_map, hl, List.length_pmap, Finset.length_toList]
    exact hT.card_edgeFinset
  · refine (hT.connected.mono ?_).preconnected
    intro u v huv
    rw [SimpleGraph.fromRel_adj]
    refine ⟨T.ne_of_adj huv, ?_⟩
    have ht : s(u, v) ∈ T.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact huv
    have h1 := hidx _ ht
    have hmem : e (idx s(u, v) ht) ∈ l.map e :=
      List.mem_map.2 ⟨_, List.mem_pmap.2 ⟨_, Finset.mem_toList.2 ht, rfl⟩, rfl⟩
    have h2 : s((e (idx s(u, v) ht)).1, (e (idx s(u, v) ht)).2) = s((u, v).1, (u, v).2) := h1
    rcases Sym2.mk_eq_mk_iff.1 h2 with h3 | h3
    · left; rw [← h3]; exact hmem
    · right; rw [show (v, u) = (u, v).swap from rfl, ← h3]; exact hmem

/-- The atoms of `Γ` as atoms of `Γ.internalize`. -/
private def intAtom (k n : ℕ) : Atom k n → Atom 0 (k + n) :=
  Sum.elim (fun a => Sum.inr (Fin.castAdd n a)) (fun b => Sum.inr (Fin.natAdd k b))

/-- The atoms of `Γ.internalize` as atoms of `Γ`. -/
private def extAtom (k n : ℕ) : Atom 0 (k + n) → Atom k n :=
  Sum.elim (fun a => a.elim0) (fun j => finSumFinEquiv.symm j)

/-- `intAtom` is `finSumFinEquiv` on the internal side. -/
private theorem intAtom_eq {k n : ℕ} (u : Atom k n) :
    intAtom k n u = Sum.inr (finSumFinEquiv u) := by
  cases u <;> rfl

/-- `extAtom` inverts `intAtom`. -/
private theorem extAtom_intAtom {k n : ℕ} (u : Atom k n) : extAtom k n (intAtom k n u) = u := by
  rw [intAtom_eq]; simp [extAtom]

/-- The components of the internal form are the images of the components. -/
private theorem internalize_comps {k n : ℕ} (Γ : Graph k n) :
    Γ.internalize.comps = Γ.comps.map (Comp.map (intAtom k n)) := rfl

/-- The component of the internal form with index `j` is the image of the component with the
same index. -/
private theorem internalize_getElem {k n : ℕ} (Γ : Graph k n) (j : Fin Γ.internalize.comps.length)
    (i : Fin Γ.comps.length) (h : j.1 = i.1) :
    Γ.internalize.comps[j] = Comp.map (intAtom k n) Γ.comps[i] := by
  have hj : j.1 < (Γ.comps.map (Comp.map (intAtom k n))).length := j.2
  change (Γ.comps.map (Comp.map (intAtom k n)))[j.1] = _
  rw [List.getElem_map]
  congr 2

/-- Under `Regular`, the internal form of a graph has no dotted edge, hence neither has `Γ`. -/
private theorem no_dot {k n C : ℕ} (Γ : Graph k n) (hR : Γ.internalize.Regular C) :
    ∀ c ∈ Γ.comps, c.kind ≠ .dot := by
  intro c hc hd
  have h := hR.noIntDot (Comp.map (intAtom k n) c)
    (by rw [internalize_comps]; exact List.mem_map_of_mem hc) hd
  simp only [Comp.map, intAtom_eq, Sum.isLeft_inr, Bool.false_eq_true, or_self] at h

/-- A net spanning the internal form of `Γ` together with the waved edges connects the atoms of
`Γ`. -/
private theorem conn_of_spans {k n : ℕ} (hk : 0 < k) (Γ : Graph k n) (C : ℕ)
    (hR : Γ.internalize.Regular C) (B : Finset (Fin Γ.internalize.comps.length))
    (hB : Γ.internalize.Spans B) :
    (SimpleGraph.fromRel fun u v => ∃ i ∈ {i : Fin Γ.comps.length | (∃ j ∈ B, j.1 = i.1) ∨
      ∃ w, Γ.comps[i].kind = .waved w}, (Γ.comps[i].x, Γ.comps[i].y) = (u, v)).Connected := by
  set S := {i : Fin Γ.comps.length | (∃ j ∈ B, j.1 = i.1) ∨ ∃ w, Γ.comps[i].kind = .waved w}
    with hS
  set H := SimpleGraph.fromRel fun u v => ∃ i ∈ S, (Γ.comps[i].x, Γ.comps[i].y) = (u, v) with hH
  have hadj : ∀ i ∈ S, H.Reachable Γ.comps[i].x Γ.comps[i].y := by
    intro i hi
    by_cases h : Γ.comps[i].x = Γ.comps[i].y
    · rw [h]
    · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨i, hi, rfl⟩⟩)
  have hmol : ∀ u v, Γ.internalize.molGraph.Adj u v →
      H.Reachable (extAtom k n u) (extAtom k n v) := by
    have one : ∀ u v, (∃ c ∈ Γ.internalize.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) →
        H.Reachable (extAtom k n u) (extAtom k n v) := by
      rintro u v ⟨c, hc, hj, rfl, rfl⟩
      rw [internalize_comps] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc₀
      simp only [Comp.map, extAtom_intAtom]
      have hw : ∃ w, Γ.comps[i].kind = .waved w := by
        have hnd := no_dot Γ hR _ hc₀
        have hj' : Γ.comps[i].kind.joinsMol = true := hj
        revert hj' hnd
        cases Γ.comps[i].kind <;> simp [Kind.joinsMol]
      exact hadj ⟨i, hi⟩ (Or.inr hw)
    intro u v huv
    rw [Graph.molGraph, SimpleGraph.fromRel_adj] at huv
    rcases huv.2 with h | h
    · exact one u v h
    · exact (one v u h).symm
  have hnet : ∀ a b, (Γ.internalize.net B).Adj a b →
      H.Reachable (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
    have one : ∀ a b, (Γ.internalize.SameMol (.inr a) (.inr b) ∨ ∃ i ∈ B,
        Γ.internalize.comps[i].x = .inr a ∧ Γ.internalize.comps[i].y = .inr b) →
        H.Reachable (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
      rintro a b (h | ⟨j, hj, hx, hy⟩)
      · rcases h with h | ⟨-, -, h⟩
        · rw [Sum.inr_injective h]
        · exact reach_lift (extAtom k n) hmol h
      · have hlen : Γ.internalize.comps.length = Γ.comps.length := by
          rw [internalize_comps, List.length_map]
        have hjl : j.1 < Γ.comps.length := lt_of_lt_of_eq j.2 hlen
        have hji := internalize_getElem Γ j ⟨j.1, hjl⟩ rfl
        rw [hji] at hx hy
        simp only [Comp.map, intAtom_eq, Sum.inr.injEq] at hx hy
        have hx' : Γ.comps[(⟨j.1, hjl⟩ : Fin Γ.comps.length)].x = finSumFinEquiv.symm a := by
          rw [← hx]; simp
        have hy' : Γ.comps[(⟨j.1, hjl⟩ : Fin Γ.comps.length)].y = finSumFinEquiv.symm b := by
          rw [← hy]; simp
        rw [← hx', ← hy']
        exact hadj ⟨j.1, hjl⟩ (Or.inl ⟨j, hj, rfl⟩)
    intro a b hab
    rw [Graph.net, SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with h | h
    · exact one a b h
    · exact (one b a h).symm
  have : Nonempty (Atom k n) := ⟨Sum.inl ⟨0, hk⟩⟩
  refine ⟨fun u v => ?_⟩
  have := reach_lift (fun a => finSumFinEquiv.symm a) hnet
    (hB (finSumFinEquiv u) (finSumFinEquiv v))
  simpa using this

/-- [I, Def 6.5] for the internal form of `Γ`, read on the atoms of `Γ`: there are a black and a
blue list of distinct components, each forming a spanning tree of the atoms, the black ones
diffusive or waved edges, the blue ones diffusive, blue or waved edges, and a component in both
lists is a waved edge. -/
private theorem dc_trees {k n : ℕ} (hk : 0 < k) (Γ : Graph k n) (C : ℕ)
    (hR : Γ.internalize.Regular C) (hDC : Γ.internalize.DoublyConnected) :
    ∃ bl bu : List (Fin Γ.comps.length), bl.Nodup ∧ bu.Nodup ∧
      (∀ i ∈ bl, Γ.comps[i].kind.isDiffusive = true ∨ ∃ w, Γ.comps[i].kind = .waved w) ∧
      (∀ i ∈ bu, Γ.comps[i].kind.isDiffusive = true ∨ Γ.comps[i].kind.isBlue = true ∨
        ∃ w, Γ.comps[i].kind = .waved w) ∧
      (∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w) ∧
      TreeEdges (bl.map fun i => (Γ.comps[i].x, Γ.comps[i].y)) ∧
      TreeEdges (bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y)) := by
  obtain ⟨black, blue, hdisj, hbk, hbu, hsb, hsu⟩ := hDC
  have hkind : ∀ (j : Fin Γ.internalize.comps.length) (i : Fin Γ.comps.length), j.1 = i.1 →
      Γ.internalize.comps[j].kind = Γ.comps[i].kind := fun j i h => by
    rw [internalize_getElem Γ j i h]; rfl
  obtain ⟨bl, hbl, hblS, hblT⟩ := exists_tree (fun i : Fin Γ.comps.length =>
    (Γ.comps[i].x, Γ.comps[i].y)) _ (conn_of_spans hk Γ C hR black hsb)
  obtain ⟨bu, hbu', hbuS, hbuT⟩ := exists_tree (fun i : Fin Γ.comps.length =>
    (Γ.comps[i].x, Γ.comps[i].y)) _ (conn_of_spans hk Γ C hR blue hsu)
  refine ⟨bl, bu, hbl, hbu', ?_, ?_, ?_, hblT, hbuT⟩
  · intro i hi
    rcases hblS i hi with ⟨j, hj, hji⟩ | hw
    · exact Or.inl (by rw [← hkind j i hji]; exact hbk j hj)
    · exact Or.inr hw
  · intro i hi
    rcases hbuS i hi with ⟨j, hj, hji⟩ | hw
    · rcases hbu j hj with h | h
      · exact Or.inl (by rw [← hkind j i hji]; exact h)
      · exact Or.inr (Or.inl (by rw [← hkind j i hji]; exact h))
    · exact Or.inr (Or.inr hw)
  · intro i h1 h2
    rcases hblS i h1 with ⟨j, hj, hji⟩ | hw
    · rcases hbuS i h2 with ⟨j', hj', hji'⟩ | hw
      · exfalso
        have : j = j' := Fin.ext (hji.trans hji'.symm)
        subst this
        exact Finset.disjoint_left.1 hdisj hj hj'
      · exact hw
    · exact hw

/-- A spanning tree of the atoms of a graph with `k` external and `n` internal atoms has
`k + n - 1` edges. -/
private theorem tree_length {k n : ℕ} {ι : Type*} (l : List ι) (f : ι → Atom k n × Atom k n)
    (h : TreeEdges (l.map f)) : l.length + 1 = k + n := by
  have := h.1
  rw [List.length_map] at this
  simpa [Fintype.card_sum] using this

/-! ## The auxiliary graph and the scaling order -/

/-- The auxiliary graph of [I, Claim 6.11] with the black and blue lists of components of `Γ`,
the blue edge of a component `c` reading the matrix of index `idx c`. -/
private def auxOf {n : ℕ} (Γ : Graph 2 n) (idx : Comp (Atom 2 n) → ℕ)
    (bl bu : List (Fin Γ.comps.length)) : AuxGraph n :=
  ⟨bl.map fun i => (Γ.comps[i].x, Γ.comps[i].y),
    bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y, idx Γ.comps[i])⟩

/-- The value of `auxOf` at `(x, y)` is the sum over the internal labels of the product of `B`
over the black list and of `|A_j|` over the blue list. -/
private theorem auxOf_val {d L W n : ℕ} [NeZero L] (Γ : Graph 2 n) (idx : Comp (Atom 2 n) → ℕ)
    (bl bu : List (Fin Γ.comps.length)) (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (x y : Zd d L) :
    (auxOf Γ idx bl bu).val d L W A x y = ∑ s : Fin n → Zd d L,
      ((bl.map fun i => bB d L W (Sum.elim ![x, y] s Γ.comps[i].x)
          (Sum.elim ![x, y] s Γ.comps[i].y)).prod *
        (bu.map fun i => |A (idx Γ.comps[i]) (Sum.elim ![x, y] s Γ.comps[i].x)
          (Sum.elim ![x, y] s Γ.comps[i].y)|).prod) := by
  simp [AuxGraph.val, auxOf, List.map_map, Function.comp_def]

/-- The blue edges of `auxOf` form the tree of the blue list. -/
private theorem auxOf_blue {n : ℕ} (Γ : Graph 2 n) (idx : Comp (Atom 2 n) → ℕ)
    (bl bu : List (Fin Γ.comps.length)) :
    ((auxOf Γ idx bl bu).blue.map fun e => (e.1, e.2.1)) =
      bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y) := by
  simp [auxOf, List.map_map, Function.comp_def]

/-- `n_Γ = Σ_i q_i - 2n`, as reals. -/
private theorem ord_eq_sum {k n : ℕ} (Γ : Graph k n) :
    (Γ.ord : ℝ) = ∑ i : Fin Γ.comps.length, (Γ.comps[i].kind.ord : ℝ) - 2 * n := by
  unfold Graph.ord
  push_cast
  congr 1
  rw [List.map_map]
  exact (Fin.sum_univ_fun_getElem Γ.comps (fun c => ((c.kind.ord : ℤ) : ℝ))).symm

/-- `Σ_i (-q_i d/2) = -(Σ_i q_i) d/2`. -/
private theorem sum_expo {ι : Type*} (s : Finset ι) (q : ι → ℝ) (d : ℝ) :
    ∑ i ∈ s, (-(q i) * d / 2) = -(∑ i ∈ s, q i) * d / 2 := by
  rw [← Finset.sum_div, ← Finset.sum_mul, Finset.sum_neg_distrib]

/-- The bound of the absolute-value graph by the normalized auxiliary graph: if every component
is bounded by `compBnd` and the black and blue lists are spanning trees, then
`|𝒢^{abs}_{xy}| ≤ C K^{|Γ|} W^{-(n_{xy}-4)d/2} B_{xy} 𝒜_{xy}` with `𝒜` the normalized value of
`auxOf` at `a = 2` ([I, (6.31)]). -/
private theorem absVal_le_normVal {d L W n : ℕ} [NeZero L] (hW : 1 ≤ W) (Γ : Graph 2 n)
    (D : Data (Zd d L)) (K Cc : ℝ) (hK : 0 ≤ K) (hCc : ‖Γ.coeff.eval D.m‖ ≤ Cc)
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (idx : Comp (Atom 2 n) → ℕ)
    (bl bu : List (Fin Γ.comps.length)) (hbl : bl.Nodup) (hbu : bu.Nodup)
    (hlb : bl.length = n + 1) (hlu : bu.length = n + 1)
    (hcomp : ∀ (σ : Atom 2 n → Zd d L) (i : Fin Γ.comps.length), ‖Comp.val D σ Γ.comps[i]‖ ≤
      compBnd d L W K A (idx Γ.comps[i]) (Γ.comps[i].kind.ord : ℝ) (σ Γ.comps[i].x)
        (σ Γ.comps[i].y) (i ∈ bl) (i ∈ bu))
    (x y : Zd d L) :
    Γ.absVal D ![x, y] ≤ Cc * K ^ Γ.comps.length * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) *
      bB d L W x y * (auxOf Γ idx bl bu).normVal d L W 2 A x y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hB := bB_pos (d := d) (L := L) hW x y
  have h := absVal_le hW Γ D K A idx bl bu hbl hbu hcomp ![x, y]
  rw [← auxOf_val Γ idx bl bu A x y, hlb, hlu] at h
  set V := (auxOf Γ idx bl bu).val d L W A x y with hV
  have hV0 : 0 ≤ V := by
    rw [hV, auxOf_val]
    refine Finset.sum_nonneg fun s _ => mul_nonneg (List.prod_nonneg fun a ha => ?_)
      (List.prod_nonneg fun a ha => ?_)
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      exact (bB_pos hW _ _).le
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      exact abs_nonneg _
  have hnorm : (auxOf Γ idx bl bu).normVal d L W 2 A x y =
      (W : ℝ) ^ (2 * (n : ℝ) * d / 2) * V / bB d L W x y := rfl
  have hexp : (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * ((W : ℝ) ^ (d : ℝ)) ^ (n + 1)) =
      (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (2 * (n : ℝ) * d / 2) := by
    rw [← Real.rpow_natCast ((W : ℝ) ^ (d : ℝ)), ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0,
      ← Real.rpow_add hW0, ← Real.rpow_add hW0, sum_expo, ord_eq_sum]
    congr 1
    push_cast
    ring
  have hrest : 0 ≤ K ^ Γ.comps.length *
      (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * ((W : ℝ) ^ (d : ℝ)) ^ (n + 1)) := by positivity
  refine h.trans ?_
  calc ‖Γ.coeff.eval D.m‖ * (K ^ Γ.comps.length *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * ((W : ℝ) ^ (d : ℝ)) ^ (n + 1))) * V
      ≤ Cc * (K ^ Γ.comps.length *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * ((W : ℝ) ^ (d : ℝ)) ^ (n + 1))) * V := by gcongr
    _ = Cc * K ^ Γ.comps.length * ((W : ℝ) ^ (∑ i : Fin Γ.comps.length,
          (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * ((W : ℝ) ^ (d : ℝ)) ^ (n + 1))) * V := by ring
    _ = Cc * K ^ Γ.comps.length * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) *
          bB d L W x y * ((W : ℝ) ^ (2 * (n : ℝ) * d / 2) * V / bB d L W x y) := by
        rw [hexp]; field_simp
    _ = _ := by rw [hnorm]

/-! ## Closing the estimates -/

/-- `0 < Im z` on the spectral domain for `W ≥ 1`. -/
private theorem im_pos_of_specDom {κ ε : ℝ} {W L : ℕ} [NeZero L] (hW : 1 ≤ W) {z : ℂ}
    (hz : z ∈ specDom κ ε W L) : 0 < z.im := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact lt_of_lt_of_le (by positivity) hz.2.1

/-- [I, (6.13)] for the normalized auxiliary graph: `𝒜_{xy} ≤ W^{-b} ⟨x - y⟩^{-(d - b)} S` when
`‖𝒜‖_{s;(2,b)} ≤ S`. -/
private theorem normVal_le {d L W n : ℕ} [NeZero L] (hW : 1 ≤ W) (b : ℝ) (Γa : AuxGraph n)
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (S : ℝ)
    (h : strongNorm d L W 2 b (Γa.normVal d L W 2 A) ≤ S) (x y : Zd d L) :
    Γa.normVal d L W 2 A x y ≤ (W : ℝ) ^ (-b) * brk d L W x y ^ (-(2 * (d : ℝ) / 2 - b)) * S := by
  have h1 := (normBasic d L W hW 2 b (Γa.normVal d L W 2 A)).2.2 x y
  have ht := brk_pos (d := d) (L := L) hW x y
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  calc _ ≤ |Γa.normVal d L W 2 A x y| := le_abs_self _
    _ ≤ _ := h1
    _ ≤ _ := by gcongr

/-- The constant `M` is at most `W^{τ/4}` for `W ≥ max(1, M)^{4/τ}`. -/
private theorem const_le_rpow (M τ Wr : ℝ) (hτ : 0 < τ) (hW : (max 1 M) ^ (4 / τ) ≤ Wr) :
    M ≤ Wr ^ (τ / 4) := by
  have h1 : (1 : ℝ) ≤ max 1 M := le_max_left _ _
  calc M ≤ max 1 M := le_max_right _ _
    _ = ((max 1 M) ^ (4 / τ)) ^ (τ / 4) := by
        rw [← Real.rpow_mul (by linarith), show 4 / τ * (τ / 4) = 1 by field_simp, Real.rpow_one]
    _ ≤ Wr ^ (τ / 4) := Real.rpow_le_rpow (by positivity) hW (by positivity)

/-- `C_c (K_w W^{τ₁})^ℓ W^{τ/4} ≤ W^τ` for `C_c K_w^ℓ ≤ W^{τ/4}` and `τ₁ ℓ ≤ τ/4`. -/
private theorem close_le (Cc Kw Wr τ τ₁ : ℝ) (ℓ : ℕ) (hW : 1 ≤ Wr) (hτ : 0 < τ)
    (hM : Cc * Kw ^ ℓ ≤ Wr ^ (τ / 4)) (hτ₁ℓ : τ₁ * ℓ ≤ τ / 4) :
    Cc * (Kw * Wr ^ τ₁) ^ ℓ * Wr ^ (τ / 4) ≤ Wr ^ τ := by
  have hW0 : 0 < Wr := by linarith
  have h1 : (Kw * Wr ^ τ₁) ^ ℓ = Kw ^ ℓ * Wr ^ (τ₁ * ℓ) := by
    rw [mul_pow, ← Real.rpow_natCast (Wr ^ τ₁), ← Real.rpow_mul hW0.le]
  have h2 : Wr ^ (τ₁ * ℓ) ≤ Wr ^ (τ / 4) := Real.rpow_le_rpow_of_exponent_le hW hτ₁ℓ
  have h3 : Wr ^ (τ / 4) * Wr ^ (τ / 4) * Wr ^ (τ / 4) ≤ Wr ^ τ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  rw [h1]
  calc Cc * (Kw ^ ℓ * Wr ^ (τ₁ * ℓ)) * Wr ^ (τ / 4)
      = (Cc * Kw ^ ℓ) * Wr ^ (τ₁ * ℓ) * Wr ^ (τ / 4) := by ring
    _ ≤ Wr ^ (τ / 4) * Wr ^ (τ / 4) * Wr ^ (τ / 4) := by gcongr
    _ ≤ Wr ^ τ := h3

/-- From `v ≤ c We B N`, `N ≤ X W'` and `c W' ≤ Wτ`: `v ≤ Wτ We B X`. -/
private theorem final_step (v c We B N X W' Wτ : ℝ) (hc : 0 ≤ c) (hWe : 0 ≤ We) (hB : 0 ≤ B)
    (hX : 0 ≤ X) (hv : v ≤ c * We * B * N) (hN : N ≤ X * W') (hcW : c * W' ≤ Wτ) :
    v ≤ Wτ * We * B * X := by
  have h0 : 0 ≤ We * B * X := by positivity
  calc v ≤ c * We * B * N := hv
    _ ≤ c * We * B * (X * W') := by gcongr
    _ = (c * W') * (We * B * X) := by ring
    _ ≤ Wτ * (We * B * X) := mul_le_mul_of_nonneg_right hcW h0
    _ = _ := by ring

/-- At most one index of a list satisfies `p` when the filter has length `1`. -/
private theorem filter_unique {α : Type*} (l : List α) (p : α → Bool)
    (h : (l.filter p).length = 1) (i j : Fin l.length) (hi : p l[i] = true)
    (hj : p l[j] = true) : i = j := by
  have hsum : ∀ l' : List α, (l'.map fun c => if p c = true then 1 else 0).sum =
      (l'.filter p).length := by
    intro l'
    induction l' with
    | nil => simp
    | cons a l' ih =>
      by_cases ha : p a = true
      · simp [ha, ih, add_comm]
      · simp [ha, ih]
  by_contra hij
  simp only [Fin.getElem_fin] at hi hj
  have h2 : 2 ≤ ∑ k : Fin l.length, (if p l[k.1] = true then 1 else 0) := by
    calc 2 = ∑ k ∈ ({i, j} : Finset (Fin l.length)), (if p l[k.1] = true then 1 else 0) := by
          rw [Finset.sum_pair hij]; simp [hi, hj]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
  rw [Fin.sum_univ_fun_getElem l (fun c => if p c = true then 1 else 0), hsum, h] at h2
  omega

/-- A component of a graph of [I, Cor 6.13] with blue index `t j₀ = 1` (`t j = 0` for `j ≠ j₀`) is
the auxiliary edge of index `j₀`. -/
private theorem cidx_ne_zero {V : Type*} (j₀ : ℕ) (c : Comp V) (hc : c.isBKind = true)
    (h : cidx (fun j => if j = j₀ then 1 else 0) c ≠ 0) : c.kind = .aux j₀ 2 true := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ with
  | aux j r b =>
    simp only [Graphs.Comp.isBKind, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hj : j = j₀ := by
      by_contra hj
      exact h (by simp [cidx, hj])
    rw [hj, hc.2.1, hc.2.2]
  | _ => exact (h rfl).elim

/-- `K W^{-d} (W^d |X|) = K X` for `X ≥ 0`. -/
private theorem scale_eq (Wr : ℝ) (hW : 0 < Wr) (d : ℕ) (K X : ℝ) (hX : 0 ≤ X) :
    K * Wr ^ (-(2 : ℝ) * d / 2) * (Wr ^ (d : ℝ) * |X|) = K * X := by
  rw [abs_of_nonneg hX, show -(2 : ℝ) * d / 2 = -(d : ℝ) by ring, Real.rpow_neg hW.le]
  have : Wr ^ (d : ℝ) ≠ 0 := by positivity
  field_simp

/-- `W^τ B_{xy} B̃_{xy} ≤ W^{-6} ⟨x - y⟩^{-(2d-6-τ)}` for `τ ≥ 0`, with
`B̃_{xy} = W^{-4} ⟨x - y⟩^{-(d-4)}`. -/
private theorem bB_bT_le {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (τ : ℝ) (hτ : 0 ≤ τ)
    (x y : Zd d L) :
    (W : ℝ) ^ τ * (bB d L W x y * ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4)))) ≤
      (W : ℝ) ^ (-6 : ℝ) * brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht := brk_pos (d := d) (L := L) hW x y
  have h1 : (W : ℝ) ^ τ ≤ brk d L W x y ^ τ := Real.rpow_le_rpow hW0.le (le_brk x y) hτ
  rw [bB_eq]
  calc (W : ℝ) ^ τ * ((W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) *
        ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))))
      = ((W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-4 : ℝ)) * ((W : ℝ) ^ τ *
          (brk d L W x y ^ (2 - (d : ℝ)) * brk d L W x y ^ (-((d : ℝ) - 4)))) := by ring
    _ ≤ ((W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-4 : ℝ)) * (brk d L W x y ^ τ *
          (brk d L W x y ^ (2 - (d : ℝ)) * brk d L W x y ^ (-((d : ℝ) - 4)))) := by gcongr
    _ = _ := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add ht, ← Real.rpow_add ht]
        congr 2 <;> ring

/-- The bounds on the waved edges of a data record with the deterministic fields of `detData`:
`|s_{pq}|, |S^±_{pq}| ≤ K W^{-d} (W^d B_{pq})²` from `wave_bound`. -/
private theorem wave_data {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (P : Profile d) (z : ℂ)
    (D : Data (Zd d L)) (hS : D.S = cmat (Smat P.ψ W L))
    (hSp : D.Sp = Splus (msc z) (Smat P.ψ W L)) (hSm : D.Sm = Sminus (msc z) (Smat P.ψ W L))
    (Kw τ₁ : ℝ)
    (hw : ∀ p q : Zd d L,
        ‖cmat (Smat P.ψ W L) p q‖ ≤ Kw * (W : ℝ) ^ τ₁ *
            ((W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ (2 * ((d : ℝ) - 2))) ∧
        ‖Splus (msc z) (Smat P.ψ W L) p q‖ ≤ Kw * (W : ℝ) ^ τ₁ *
            ((W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ (2 * ((d : ℝ) - 2))) ∧
        ‖Sminus (msc z) (Smat P.ψ W L) p q‖ ≤ Kw * (W : ℝ) ^ τ₁ *
            ((W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ (2 * ((d : ℝ) - 2))))
    (w : Wave) (p q : Zd d L) :
    ‖Comp.val D id (mkC (.waved w) p q : Comp (Zd d L))‖ ≤
      Kw * (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ (d : ℝ) * bB d L W p q) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q)) := by
  obtain ⟨hs, hp, hm⟩ := hw p q
  rw [wave_shape hW] at hs hp hm
  have e : Kw * (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
      (((W : ℝ) ^ (d : ℝ) * bB d L W p q) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q)) =
      Kw * (W : ℝ) ^ τ₁ * ((W : ℝ) ^ (-(d : ℝ)) *
        (((W : ℝ) ^ (d : ℝ) * bB d L W p q) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q))) := by
    rw [show -(2 : ℝ) * d / 2 = -(d : ℝ) by ring]; ring
  rw [e]
  cases w
  · change ‖D.S p q‖ ≤ _; rw [hS]; exact hs
  · change ‖D.Sp p q‖ ≤ _; rw [hSp]; exact hp
  · change ‖D.Sm p q‖ ≤ _; rw [hSm]; exact hm

/-! ## Deterministic graphs -/

/-- [I, Cor 6.12, (6.41)] = [II, Lemma 8.5, (8.17)]: for `d ≥ 6` and a deterministic graph `Γ`
(waved and labelled `Θ` edges with labels in `[4, N]`) with two external atoms whose internal
form is normal regular and doubly connected: for every `τ > 0` there is `W₀` with
`|𝒢^{abs}_{xy}| ≤ W^τ W^{-(n_{xy}-4)d/2} B_{xy}²` for `W ≥ W₀` along `adm(c₀, c₁)` and
`z ∈ 𝐃(κ, ε)`. -/
theorem detBound :
  ∀ (d : ℕ), 6 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (n C : ℕ) (Γ : Graph 2 n), Γ.internalize.Normal C → Γ.internalize.DoublyConnected →
      Γ.comps.all (Comp.isDetKind N) = true → ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ,
        ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
          ∀ x y : Zd d L,
            Γ.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, y] ≤
              (W : ℝ) ^ τ * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * bB d L W x y ^ 2 := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n C Γ hNo hDC hDet τ hτ
  obtain ⟨bl, bu, hbl, hbu', hbk, hbu, hboth, hTb, hTu⟩ := dc_trees (by norm_num) Γ C hNo.1 hDC
  have hlb : bl.length = n + 1 := by have := tree_length bl _ hTb; omega
  have hlu : bu.length = n + 1 := by have := tree_length bu _ hTu; omega
  have hdot := no_dot Γ hNo.1
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hDi : ∀ i : Fin Γ.comps.length, Γ.comps[i].isDetKind N = true := fun i =>
    List.all_eq_true.1 hDet _ (List.getElem_mem _)
  set τ₁ : ℝ := τ / (4 * ((Γ.comps.length : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁ℓ : τ₁ * Γ.comps.length ≤ τ / 4 := by
    rw [hτ₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨Kw, Ww, hKw, hw⟩ := wave_bound d (by omega) P c₀ c₁ κ hc₀ hc₁ hκ τ₁ hτ₁0
  have hth : ∀ i : Fin Γ.comps.length, ∃ W₀ : ℝ, ∀ o, Γ.comps[i].kind = .theta o →
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ x y : Zd d L,
          ‖(detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)).chain o x y‖ ≤
            (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              bB d L W x y := by
    intro i
    by_cases h : ∃ o, Γ.comps[i].kind = .theta o
    · obtain ⟨o, ho⟩ := h
      have hl : labelOK N o = true := by
        have := hDi i
        simp only [Comp.isDetKind, ho, Bool.and_eq_true] at this
        exact this.2
      have hK : ∀ l ∈ o,
          KerSymm (sigKer (smatVar P) Sig) l ∧ KerBound (sigKer (smatVar P) Sig) l := by
        intro l hlo
        simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          at hl
        obtain ⟨⟨h4, hN⟩, h2⟩ := hl l hlo
        have hse := hSig l h4 hN (Nat.even_iff.2 h2)
        exact ⟨hse.2.1, hse.2.2⟩
      obtain ⟨W₀, hW₀⟩ := chain d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε _ o hK τ₁ hτ₁0
      obtain ⟨W₁, hW₁⟩ := detData_smatVar_eq_on_adm d P Sig c₀ c₁ hc₀ hc₁
      refine ⟨max W₀ W₁, fun o' ho' => ?_⟩
      rw [ho] at ho'
      cases ho'
      intro W L _ hadm hW z hz x y
      rw [← hW₁ W L hadm ((le_max_right _ _).trans hW) z]
      exact hW₀ W L hadm ((le_max_left _ _).trans hW) z hz x y
    · exact ⟨0, fun o ho => (h ⟨o, ho⟩).elim⟩
  choose Wth hWth using hth
  obtain ⟨Cc, hCc0, hCc⟩ := coeff_bound κ hκ Γ.coeff
  obtain ⟨W₂, hW₂⟩ := auxTreeStrong d 2 2 (by omega) two_pos two_pos (by linarith) c₀ c₁ hc₀ hc₁
    n (auxOf Γ (fun _ => 0) bl bu) hTb (by rw [auxOf_blue]; exact hTu) (τ / 4) (by positivity)
  refine ⟨max (max 1 (max Ww (∑ i, |Wth i|))) (max W₂ ((max 1 (Cc * Kw ^ Γ.comps.length)) ^
    (4 / τ))), fun W L _ hadm hW z hz x y => ?_⟩
  have hWa : max 1 (max Ww (∑ i, |Wth i|)) ≤ (W : ℝ) := (le_max_left _ _).trans hW
  have hWb : max W₂ ((max 1 (Cc * Kw ^ Γ.comps.length)) ^ (4 / τ)) ≤ (W : ℝ) :=
    (le_max_right _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hWa
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hW1n hz
  set S := Smat P.ψ W L with hSdef
  set D := detData S z (sigMat Sig S z) with hD
  set K := Kw * (W : ℝ) ^ τ₁ with hKdef
  have hWτ₁ : 1 ≤ (W : ℝ) ^ τ₁ := Real.one_le_rpow hW1 hτ₁0.le
  have hK1 : 1 ≤ K := by rw [hKdef]; nlinarith
  have hwav : ∀ (w : Wave) (p q : Zd d L),
      ‖Comp.val D id (mkC (.waved w) p q : Comp (Zd d L))‖ ≤ K * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ (d : ℝ) * bB d L W p q) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q)) := by
    intro w p q
    obtain ⟨hs, hp, hm⟩ := hw W L hadm ((le_max_left _ _).trans ((le_max_right _ _).trans hWa))
      hW1n z him hz.1 p q
    rw [wave_shape hW1n] at hs hp hm
    have e : K * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ (d : ℝ) * bB d L W p q) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q)) =
        Kw * (W : ℝ) ^ τ₁ * ((W : ℝ) ^ (-(d : ℝ)) *
          (((W : ℝ) ^ (d : ℝ) * bB d L W p q) * ((W : ℝ) ^ (d : ℝ) * bB d L W p q))) := by
      rw [hKdef, show -(2 : ℝ) * d / 2 = -(d : ℝ) by ring]; ring
    rw [e]
    cases w
    · exact hs
    · exact hp
    · exact hm
  have hcomp : ∀ (σ : Atom 2 n → Zd d L) (i : Fin Γ.comps.length),
      ‖Comp.val D σ Γ.comps[i]‖ ≤ compBnd d L W K (fun _ p q => bB d L W p q)
        ((fun _ => 0 : Comp (Atom 2 n) → ℕ) Γ.comps[i]) (Γ.comps[i].kind.ord : ℝ)
        (σ Γ.comps[i].x) (σ Γ.comps[i].y) (i ∈ bl) (i ∈ bu) := by
    intro σ i
    refine comp_det (by omega) hW1n D N K hK1 hwav σ Γ.comps[i] ?_ (hDi i)
      (hdot _ (List.getElem_mem _)) _ _ (hbk i) (hbu i) (hboth i)
    intro o ho p q
    have hWi : Wth i ≤ (W : ℝ) := by
      refine le_trans ?_ ((le_max_right _ _).trans ((le_max_right _ _).trans hWa))
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Wth j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ _))
    have h1 := hWth i o ho W L hadm hWi z hz p q
    have hdata : D.chain o =
        (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)).chain o := rfl
    rw [hdata]
    refine h1.trans ?_
    have hexp : (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) =
        (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) * (W : ℝ) ^ (d : ℝ) := by
      rw [← Real.rpow_add hW0]; ring_nf
    rw [hexp]
    have hB0 : 0 ≤ bB d L W p q := (bB_pos hW1n p q).le
    have : (W : ℝ) ^ τ₁ ≤ K := by rw [hKdef]; exact le_mul_of_one_le_left (by positivity) hKw
    calc (W : ℝ) ^ τ₁ * ((W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) * (W : ℝ) ^ (d : ℝ)) *
          bB d L W p q
        = (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
            ((W : ℝ) ^ (d : ℝ) * bB d L W p q) := by ring
      _ ≤ K * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
            ((W : ℝ) ^ (d : ℝ) * bB d L W p q) := by gcongr
  have hmain := absVal_le_normVal hW1n Γ D K Cc (by positivity)
    (by rw [hD]; exact hCc z him hz.1 hz.2.2) (fun _ p q => bB d L W p q) (fun _ => 0) bl bu
    hbl hbu' hlb hlu hcomp x y
  have hAn : ∀ j : ℕ, strongNorm d L W 2 2
      ((fun (_ : ℕ) (p q : Zd d L) => bB d L W p q) j) ≤ 1 :=
    fun _ => (bB_strongNorm d L W hW1n).1.le
  have haux := hW₂ W L hadm ((le_max_left _ _).trans hWb) _ hAn
  have hnv := normVal_le hW1n 2 _ _ _ haux x y
  have hX : (W : ℝ) ^ (-(2 : ℝ)) * brk d L W x y ^ (-(2 * (d : ℝ) / 2 - 2)) = bB d L W x y := by
    rw [bB_eq]; congr 2; ring
  rw [hX] at hnv
  have hclose := close_le Cc Kw W τ τ₁ Γ.comps.length hW1 hτ
    (const_le_rpow _ τ W hτ ((le_max_right _ _).trans hWb)) hτ₁ℓ
  have hB0 := (bB_pos hW1n x y).le
  have := final_step _ _ _ _ _ _ _ _ (by positivity) (by positivity) hB0 hB0 hmain hnv hclose
  rw [sq]
  calc _ ≤ _ := this
    _ = _ := by ring

/-- [I, Cor 6.13, (6.43)]: as `detAux`, with exactly one auxiliary edge, of index `j₀`,
bounded by `W^{τ'} B̃`, `B̃_{uv} = W^{-4} ⟨u - v⟩^{-(d-4)}`:
`|𝒢''^{abs}_{xy}| ≤ W^{-(n''_{xy}-4)d/2} W^{-6} ⟨x - y⟩^{-(2d-6-τ)}`. -/
theorem detAuxTilde :
  ∀ (d : ℕ), 6 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (n C : ℕ) (Γ : Graph 2 n) (j₀ : ℕ), Γ.internalize.Normal C →
      Γ.internalize.DoublyConnected → Γ.comps.all Comp.isBKind = true →
      (Γ.comps.filter fun c => decide (c.kind = .aux j₀ 2 true)).length = 1 →
      ∀ τ : ℝ, 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
        (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
          ∀ M : ℕ → Matrix (Zd d L) (Zd d L) ℂ,
            (∀ j u v, j ≠ j₀ → ‖M j u v‖ ≤ (W : ℝ) ^ τ' * bB d L W u v) →
            (∀ u v, ‖M j₀ u v‖ ≤
              (W : ℝ) ^ τ' * ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))) →
            ∀ x y : Zd d L,
              Γ.absVal (auxData (Smat P.ψ W L) z M) ![x, y] ≤
                (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
                  brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ)) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n C Γ j₀ hNo hDC hBK hone τ hτ
  have hBi : ∀ i : Fin Γ.comps.length, Γ.comps[i].isBKind = true := fun i =>
    List.all_eq_true.1 hBK _ (List.getElem_mem _)
  set t : ℕ → ℕ := fun j => if j = j₀ then 1 else 0 with ht
  -- the black tree avoids the edge of index `j₀` (exchanging the two nets if needed)
  obtain ⟨bl, bu, hbl, hbu', hboth, hTb, hTu, hbk0⟩ : ∃ bl bu : List (Fin Γ.comps.length),
      bl.Nodup ∧ bu.Nodup ∧ (∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w) ∧
      TreeEdges (bl.map fun (i : Fin Γ.comps.length) => (Γ.comps[i].x, Γ.comps[i].y)) ∧
      TreeEdges (bu.map fun (i : Fin Γ.comps.length) => (Γ.comps[i].x, Γ.comps[i].y)) ∧
      ∀ i ∈ bl, cidx t Γ.comps[i] = 0 := by
    obtain ⟨bl₀, bu₀, hbl₀, hbu₀, -, -, hboth₀, hTb₀, hTu₀⟩ :=
      dc_trees (by norm_num) Γ C hNo.1 hDC
    by_cases hb : ∀ i ∈ bl₀, cidx t Γ.comps[i] = 0
    · exact ⟨bl₀, bu₀, hbl₀, hbu₀, hboth₀, hTb₀, hTu₀, hb⟩
    · push Not at hb
      obtain ⟨i₀, hi₀, hne₀⟩ := hb
      refine ⟨bu₀, bl₀, hbu₀, hbl₀, fun i h1 h2 => hboth₀ i h2 h1, ?_, ?_, fun i hi => ?_⟩
      · exact hTu₀
      · exact hTb₀
      by_contra hne
      have k₀ := cidx_ne_zero j₀ _ (hBi i₀) hne₀
      have k₁ := cidx_ne_zero j₀ _ (hBi i) hne
      have hii := filter_unique Γ.comps (fun c => decide (c.kind = .aux j₀ 2 true)) hone i i₀
        (by simpa using k₁) (by simpa using k₀)
      subst hii
      obtain ⟨w, hw⟩ := hboth₀ i hi₀ hi
      rw [k₀] at hw
      cases hw
  have hlb : bl.length = n + 1 := by have := tree_length bl _ hTb; omega
  have hlu : bu.length = n + 1 := by have := tree_length bu _ hTu; omega
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  set τ₁ : ℝ := τ / (4 * ((Γ.comps.length : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁ℓ : τ₁ * Γ.comps.length ≤ τ / 4 := by
    rw [hτ₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨Kw, Ww, hKw, hw⟩ := wave_bound d (by omega) P c₀ c₁ κ hc₀ hc₁ hκ τ₁ hτ₁0
  obtain ⟨Cc, hCc0, hCc⟩ := coeff_bound κ hκ Γ.coeff
  obtain ⟨W₂, hW₂⟩ := auxTreeStrong d 2 4 (by omega) two_pos (by norm_num) (by linarith) c₀ c₁
    hc₀ hc₁ n (auxOf Γ (cidx t) bl bu) hTb (by rw [auxOf_blue]; exact hTu) (τ / 4)
    (by positivity)
  refine ⟨τ₁, hτ₁0, max (max 1 Ww) (max W₂ ((max 1 (Cc * Kw ^ Γ.comps.length)) ^ (4 / τ))),
    fun W L _ hadm hW z hz M hM hM₀ x y => ?_⟩
  have hWa : max 1 Ww ≤ (W : ℝ) := (le_max_left _ _).trans hW
  have hWb : max W₂ ((max 1 (Cc * Kw ^ Γ.comps.length)) ^ (4 / τ)) ≤ (W : ℝ) :=
    (le_max_right _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hWa
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hW1n hz
  set D := auxData (Smat P.ψ W L) z M with hD
  set K := Kw * (W : ℝ) ^ τ₁ with hKdef
  have hWτ₁ : 1 ≤ (W : ℝ) ^ τ₁ := Real.one_le_rpow hW1 hτ₁0.le
  have hK1 : 1 ≤ K := by rw [hKdef]; nlinarith
  have hτK : (W : ℝ) ^ τ₁ ≤ K := by rw [hKdef]; exact le_mul_of_one_le_left (by positivity) hKw
  set A : ℕ → Matrix (Zd d L) (Zd d L) ℝ := fun j p q => if j = 1 then
    (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4)) else bB d L W p q with hA
  have hT0 : ∀ p q : Zd d L, 0 ≤ (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4)) :=
    fun p q => by have := brk_pos (d := d) (L := L) hW1n p q; positivity
  have hwav := wave_data hW1n P z D rfl rfl rfl Kw τ₁
    (hw W L hadm ((le_max_right _ _).trans hWa) hW1n z him hz.1)
  have hA0 : ∀ p q, A 0 p q = bB d L W p q := fun p q => by
    simp only [hA, zero_ne_one, ↓reduceIte]
  have hA1 : ∀ j p q, (W : ℝ) ^ (d : ℝ) * |A j p q| ≤ 1 := fun j p q => by
    by_cases hj : j = 1
    · simp only [hA, hj, ↓reduceIte]
      rw [abs_of_nonneg (hT0 p q)]; exact (rpow_mul_bT_mem (by omega) hW1n p q).2
    · simp only [hA, hj, ↓reduceIte]
      rw [abs_of_nonneg (bB_pos hW1n p q).le]; exact (rpow_mul_bB_mem (by omega) hW1n p q).2
  have haux : ∀ j p q, ‖D.aux j p q‖ ≤
      K * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * ((W : ℝ) ^ (d : ℝ) * |A (t j) p q|) := by
    intro j p q
    by_cases hj : j = j₀
    · have e : A (t j) p q = (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4)) := by
        simp only [hA, ht, hj, ↓reduceIte]
      rw [e, scale_eq _ hW0 d K _ (hT0 p q), hj]
      exact (hM₀ p q).trans (mul_le_mul_of_nonneg_right hτK (hT0 p q))
    · have e : A (t j) p q = bB d L W p q := by
        simp only [hA, ht, hj, ↓reduceIte, zero_ne_one]
      rw [e, scale_eq _ hW0 d K _ (bB_pos hW1n p q).le]
      exact (hM j p q hj).trans (mul_le_mul_of_nonneg_right hτK (bB_pos hW1n p q).le)
  have hcomp : ∀ (σ : Atom 2 n → Zd d L) (i : Fin Γ.comps.length),
      ‖Comp.val D σ Γ.comps[i]‖ ≤ compBnd d L W K A (cidx t Γ.comps[i])
        (Γ.comps[i].kind.ord : ℝ) (σ Γ.comps[i].x) (σ Γ.comps[i].y) (i ∈ bl) (i ∈ bu) :=
    fun σ i => comp_aux (by omega) hW1n D K hK1 A t hA0 hA1 hwav haux σ Γ.comps[i] (hBi i) _ _
      (hbk0 i) (hboth i)
  have hmain := absVal_le_normVal hW1n Γ D K Cc (by positivity)
    (by rw [hD]; exact hCc z him hz.1 hz.2.2) A (cidx t) bl bu hbl hbu' hlb hlu hcomp x y
  have hAn : ∀ j : ℕ, strongNorm d L W 2 4 (A j) ≤ 1 := by
    intro j
    by_cases hj : j = 1
    · have e : A j = fun p q => (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4)) := by
        funext p q; simp only [hA, hj, ↓reduceIte]
      rw [e]; exact strongNorm24_bT hW1n
    · have e : A j = fun p q => bB d L W p q := by
        funext p q; simp only [hA, hj, ↓reduceIte]
      rw [e]; exact strongNorm24_bB hW1n
  have haux2 := hW₂ W L hadm ((le_max_left _ _).trans hWb) _ hAn
  have hnv := normVal_le hW1n 4 _ _ _ haux2 x y
  have hX : (W : ℝ) ^ (-(4 : ℝ)) * brk d L W x y ^ (-(2 * (d : ℝ) / 2 - 4)) =
      (W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4)) := by
    congr 2; ring
  rw [hX] at hnv
  have hclose := close_le Cc Kw W τ τ₁ Γ.comps.length hW1 hτ
    (const_le_rpow _ τ W hτ ((le_max_right _ _).trans hWb)) hτ₁ℓ
  have hB0 := (bB_pos hW1n x y).le
  have h1 := final_step _ _ _ _ _ _ _ _ (by positivity) (by positivity) hB0 (hT0 x y) hmain hnv
    hclose
  have h2 := bB_bT_le (L := L) hW1n τ hτ.le x y
  have hWe : 0 ≤ (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) := by positivity
  calc _ ≤ _ := h1
    _ = (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * ((W : ℝ) ^ τ * (bB d L W x y *
          ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))))) := by ring
    _ ≤ (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) *
          ((W : ℝ) ^ (-6 : ℝ) * brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ))) :=
        mul_le_mul_of_nonneg_left h2 hWe
    _ = _ := by ring

section Instances

namespace G9

end G9

section Witness
open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

end Instances

end RBM8D
