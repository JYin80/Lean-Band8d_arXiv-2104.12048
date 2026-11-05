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
# Doubly connected graphs ([I, Lemma 6.10] = [II, Lemma 8.4])

Deterministic bounds on the absolute-value graph of a doubly connected normal regular graph in terms
of `Λ ≥ ‖G − m‖`, the form with one fixed atom, and the stochastic domination form [I, (6.40)].
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

section Elem

variable {d L W : ℕ} [NeZero L]

omit [NeZero L] in
/-- `⟨x - y⟩ > 0` for `W ≥ 1`. -/
private theorem brk_pos₁ (hW : 1 ≤ W) (x y : Zd d L) : 0 < brk d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold brk; positivity

omit [NeZero L] in
/-- `W ≤ ⟨x - y⟩`. -/
private theorem le_brk₁ (x y : Zd d L) : (W : ℝ) ≤ brk d L W x y := by
  unfold brk; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]

omit [NeZero L] in
/-- `B_{xy} > 0` for `W ≥ 1`. -/
private theorem bB_pos₁ (hW : 1 ≤ W) (x y : Zd d L) : 0 < bB d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold bB; positivity

omit [NeZero L] in
/-- `B_{xy} ≤ W^{-d}` for `d ≥ 2`, `W ≥ 1`. -/
private theorem bB_le_rpow (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y ≤ (W : ℝ) ^ (-(d : ℝ)) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : brk d L W x y ^ (2 - (d : ℝ)) ≤ (W : ℝ) ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hW0 (le_brk₁ x y) (by linarith)
  calc bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) := rfl
    _ ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (W : ℝ) ^ (-(d : ℝ)) := by rw [← Real.rpow_add hW0]; ring_nf

omit [NeZero L] in
/-- `W^{d/2} B_{xy}^{1/2} ≤ 1` for `d ≥ 2`, `W ≥ 1`. -/
private theorem rpow_mul_sqrt_bB_le (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) :
    (W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W x y) ≤ 1 := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have h1 : Real.sqrt (bB d L W x y) ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) := by
    rw [Real.sqrt_le_left (by positivity)]
    calc bB d L W x y ≤ (W : ℝ) ^ (-(d : ℝ)) := bB_le_rpow hd hW x y
      _ = ((W : ℝ) ^ (-((d : ℝ) / 2))) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  calc (W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W x y)
      ≤ (W : ℝ) ^ ((d : ℝ) / 2) * (W : ℝ) ^ (-((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by rw [← Real.rpow_add hW0]; simp

/-- The index set of the dyadic scales of `weakNorm` is finite. -/
private theorem finite_scales (L W : ℕ) : Finite {K : ℕ // W ≤ K ∧ 2 * K ≤ L} :=
  Finite.of_injective (fun K => (⟨K.1, by have := K.2.2; omega⟩ : Fin (L + 1)))
    (fun p q h => Subtype.ext (by simpa using h))

/-- If `|A_{xy}| ≤ c |B_{xy}|` for all `x, y` with `c ≥ 0`, then
`‖A‖_{w;(a,b)} ≤ c ‖B‖_{w;(a,b)}`. -/
private theorem weakNorm_le_mul (a b c : ℝ) (hc : 0 ≤ c) (A B : Matrix (Zd d L) (Zd d L) ℝ)
    (h : ∀ x y, |A x y| ≤ c * |B x y|) :
    weakNorm d L W a b A ≤ c * weakNorm d L W a b B := by
  have := finite_scales L W
  unfold weakNorm
  rw [mul_add]
  apply add_le_add
  · rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.mul_iSup_of_nonneg hc]
    refine ciSup_mono (Set.finite_range _).bddAbove fun x => ?_
    rw [Real.mul_iSup_of_nonneg hc]
    exact ciSup_mono (Set.finite_range _).bddAbove fun y => h x y
  · rw [Real.mul_iSup_of_nonneg hc]
    refine ciSup_mono (Set.finite_range _).bddAbove fun K => ?_
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.mul_iSup_of_nonneg hc]
    refine ciSup_mono (Set.finite_range _).bddAbove fun x => ?_
    rw [Real.mul_iSup_of_nonneg hc]
    refine ciSup_mono (Set.finite_range _).bddAbove fun x₀ => ?_
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => by
      have h1 := h x y; have h2 := h y x; linarith

/-- If `|A_{xy}| ≤ c |B_{xy}|` for all `x, y` with `c ≥ 0`, then
`‖A‖_{s;(a,b)} ≤ c ‖B‖_{s;(a,b)}`. -/
private theorem strongNorm_le_mul (hW : 1 ≤ W) (a b c : ℝ) (hc : 0 ≤ c)
    (A B : Matrix (Zd d L) (Zd d L) ℝ) (h : ∀ x y, |A x y| ≤ c * |B x y|) :
    strongNorm d L W a b A ≤ c * strongNorm d L W a b B := by
  have hW0 : (0 : ℝ) < W := by have : (1 : ℝ) ≤ W := by exact_mod_cast hW
                               linarith
  unfold strongNorm
  rw [Real.mul_iSup_of_nonneg hc]
  refine ciSup_mono (Set.finite_range _).bddAbove fun x => ?_
  rw [Real.mul_iSup_of_nonneg hc]
  refine ciSup_mono (Set.finite_range _).bddAbove fun y => ?_
  have ht := brk_pos₁ (d := d) (L := L) hW x y
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h x y) (by positivity)

end Elem

/-! ## The blue matrix of `Θ` and waved edges -/

/-- The matrix `B^{1/2}/C₀` has strong-`(1,1)` and weak-`(1,2)` norms at most `1` for a constant
`C₀ ≥ 1` depending on `d ≥ 8` only. -/
private theorem sqrtB_norms (d : ℕ) (hd : 8 ≤ d) : ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W →
      weakNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y) / C₀) ≤ 1 ∧
        strongNorm d L W 1 1 (fun x y => Real.sqrt (bB d L W x y) / C₀) ≤ 1 := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, hC⟩ := weak_le_strong d 1 2 (by linarith) (by linarith)
  refine ⟨max 1 C, le_max_left _ _, fun L W _ hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set C₀ := max 1 C with hC₀
  have hC₀1 : 1 ≤ C₀ := le_max_left _ _
  have hC₀0 : 0 < C₀ := by linarith
  have h11 := (bB_strongNorm d L W hW).2
  have habs : ∀ x y, |Real.sqrt (bB d L W x y) / C₀| ≤ C₀⁻¹ * |Real.sqrt (bB d L W x y)| := by
    intro x y
    rw [abs_div, abs_of_pos hC₀0, div_eq_inv_mul]
  -- the strong `(1,2)` norm of `B^{1/2}` is at most its strong `(1,1)` norm
  have h12 : strongNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y)) ≤ 1 := by
    refine le_trans ?_ h11.le
    unfold strongNorm
    refine ciSup_mono (Set.finite_range _).bddAbove fun x => ?_
    refine ciSup_mono (Set.finite_range _).bddAbove fun y => ?_
    have ht := brk_pos₁ (d := d) (L := L) hW x y
    have hle := le_brk₁ (d := d) (L := L) (W := W) x y
    have hq0 : 0 < (W : ℝ) / brk d L W x y := by positivity
    have hq1 : (W : ℝ) / brk d L W x y ≤ 1 := (div_le_one ht).2 hle
    have : ((W : ℝ) / brk d L W x y) ^ (2 : ℝ) ≤ ((W : ℝ) / brk d L W x y) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by norm_num)
    gcongr
  have hS0 : 0 ≤ strongNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y)) :=
    Real.iSup_nonneg fun x => Real.iSup_nonneg fun y => by
      have := brk_pos₁ (d := d) (L := L) hW x y; positivity
  refine ⟨?_, ?_⟩
  · calc weakNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y) / C₀)
        ≤ C₀⁻¹ * weakNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y)) :=
          weakNorm_le_mul 1 2 _ (by positivity) _ _ habs
      _ ≤ C₀⁻¹ * (C * strongNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y))) :=
          mul_le_mul_of_nonneg_left (hC L W hW _) (by positivity)
      _ ≤ C₀⁻¹ * (C₀ * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc C * strongNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y))
              ≤ C₀ * strongNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y)) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hS0
            _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left h12 hC₀0.le
      _ = 1 := by field_simp
  · calc strongNorm d L W 1 1 (fun x y => Real.sqrt (bB d L W x y) / C₀)
        ≤ C₀⁻¹ * strongNorm d L W 1 1 (fun x y => Real.sqrt (bB d L W x y)) :=
          strongNorm_le_mul hW 1 1 _ (by positivity) _ _ habs
      _ = C₀⁻¹ := by rw [h11, mul_one]
      _ ≤ 1 := inv_le_one_of_one_le₀ hC₀1

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

variable {d L W : ℕ}

/-- `B_{xy} · W^{d/2} B_{xy}^{1/2} = W^{-d} (W/⟨x - y⟩)^{3(d-2)/2}`. -/
private theorem bB_mul_sqrt_eq (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y * ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W x y)) =
      (W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W x y) ^ (3 * ((d : ℝ) - 2) / 2) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have ht := brk_pos₁ (d := d) (L := L) hW x y
  set t := brk d L W x y with htdef
  have hB : bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * t ^ (2 - (d : ℝ)) := rfl
  have hsq : Real.sqrt (bB d L W x y) = (W : ℝ) ^ (-1 : ℝ) * t ^ ((2 - (d : ℝ)) / 2) := by
    rw [hB, Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hW0.le, ← Real.rpow_mul ht.le]
    congr 2 <;> ring
  have hdiv : (W : ℝ) ^ (3 * ((d : ℝ) - 2) / 2) / t ^ (3 * ((d : ℝ) - 2) / 2) =
      (W : ℝ) ^ (3 * ((d : ℝ) - 2) / 2) * t ^ (-(3 * ((d : ℝ) - 2) / 2)) := by
    rw [Real.rpow_neg ht.le, div_eq_mul_inv]
  rw [hsq, hB, Real.div_rpow hW0.le ht.le, hdiv]
  calc (W : ℝ) ^ (-2 : ℝ) * t ^ (2 - (d : ℝ)) *
        ((W : ℝ) ^ ((d : ℝ) / 2) * ((W : ℝ) ^ (-1 : ℝ) * t ^ ((2 - (d : ℝ)) / 2)))
      = ((W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ ((d : ℝ) / 2) * (W : ℝ) ^ (-1 : ℝ)) *
          (t ^ (2 - (d : ℝ)) * t ^ ((2 - (d : ℝ)) / 2)) := by ring
    _ = (W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) ^ (3 * ((d : ℝ) - 2) / 2) *
          t ^ (-(3 * ((d : ℝ) - 2) / 2))) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add ht, ← mul_assoc,
          ← Real.rpow_add hW0]
        congr 2 <;> ring

/-- `t^{-D} ≤ W^{-d} (W/t)^e` for `t ≥ W ≥ 1` and `0 ≤ e ≤ D - d`. -/
private theorem tail_le (Wr t e D : ℝ) (hW : 1 ≤ Wr) (ht : Wr ≤ t) (hdD : (d : ℝ) ≤ D)
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
private theorem f_le_of_subpoly [NeZero L] (hW1n : 1 ≤ W) (f : ℝ) (r C0 Ck : ℝ) (hr0 : 0 ≤ r)
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

/-- [I, Lemma 2.2] for the waved edges `S^±`: `splusBound ≤ (2^e + 1) W^τ X`, with
`X = W^{-d} (W/⟨x - y⟩)^e`, `e = 3(d-2)/2`, at `D = 2d` and `τ' e ≤ τ`. -/
private theorem splusBound_le [NeZero L] (hd : 2 ≤ d) (hW1n : 1 ≤ W) (τ τ' : ℝ) (hτ : 0 ≤ τ)
    (hτ' : 0 ≤ τ') (hτ'e : τ' * (3 * ((d : ℝ) - 2) / 2) ≤ τ) (p q : Zd d L) :
    splusBound W τ' (2 * (d : ℝ)) p q ≤ (2 ^ (3 * ((d : ℝ) - 2) / 2) + 1) * (W : ℝ) ^ τ *
      ((W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / brk d L W p q) ^ (3 * ((d : ℝ) - 2) / 2)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  set e : ℝ := 3 * ((d : ℝ) - 2) / 2 with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  have he2 : e ≤ 2 * (d : ℝ) := by rw [he]; linarith
  have htt : (zdistInf d L (p - q) : ℝ) + W = brk d L W p q := rfl
  set t := brk d L W p q with htdef
  have hWt : (W : ℝ) ≤ t := le_brk₁ p q
  set X := (W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / t) ^ e with hX
  have hX0 : 0 ≤ X := by
    have : 0 < t := by linarith
    positivity
  have hWτ : 1 ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ
  unfold splusBound
  rw [htt]
  have htail : t ^ (-(2 * (d : ℝ))) ≤ X :=
    tail_le (W : ℝ) t e (2 * (d : ℝ)) hW1 hWt (by linarith) he2
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

/-- [I, (1.8)] and [I, Lemma 2.2] for the waved edges: for every `τ > 0` there are
`K ≥ 1` and `W₀` such that along `adm(c₀, c₁)`, for `W ≥ W₀` and `z` in the bulk,
`|s_{xy}|, |S^±_{xy}| ≤ K W^τ B_{xy} · W^{d/2} B_{xy}^{1/2}`. -/
private theorem wave_bound (d : ℕ) (hd : 2 ≤ d) (P : Profile d) (c₀ c₁ κ : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ K W₀ : ℝ, 1 ≤ K ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → 1 ≤ W →
      ∀ z : ℂ, 0 < z.im → |z.re| < 2 - κ → ∀ p q : Zd d L,
        ‖cmat (Smat P.ψ W L) p q‖ ≤ K * (W : ℝ) ^ τ *
            (bB d L W p q * ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))) ∧
        ‖Splus (msc z) (Smat P.ψ W L) p q‖ ≤ K * (W : ℝ) ^ τ *
            (bB d L W p q * ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))) ∧
        ‖Sminus (msc z) (Smat P.ψ W L) p q‖ ≤ K * (W : ℝ) ^ τ *
            (bB d L W p q * ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set e : ℝ := 3 * ((d : ℝ) - 2) / 2 with he
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
  have hX := bB_mul_sqrt_eq (L := L) hW1n p q
  set X := bB d L W p q * ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) with hXdef
  have hX0 : 0 ≤ X := by
    have := brk_pos₁ (d := d) (L := L) hW1n p q
    rw [hX]; positivity
  have hWτ : 1 ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have hτX : X ≤ (W : ℝ) ^ τ * X := le_mul_of_one_le_left hX0 hWτ
  have hWτX : 0 ≤ (W : ℝ) ^ τ * X := by positivity
  have hfin : ∀ v : ℝ, (v ≤ K₁ * X ∨ v ≤ K₂ * ((W : ℝ) ^ τ * X)) →
      v ≤ (1 + K₁ + K₂) * (W : ℝ) ^ τ * X := by
    intro v hv
    have e1 : (1 + K₁ + K₂) * (W : ℝ) ^ τ * X =
        (W : ℝ) ^ τ * X + K₁ * ((W : ℝ) ^ τ * X) + K₂ * ((W : ℝ) ^ τ * X) := by ring
    have e2 : K₁ * X ≤ K₁ * ((W : ℝ) ^ τ * X) := mul_le_mul_of_nonneg_left hτX hK₁0
    have e3 : 0 ≤ K₁ * ((W : ℝ) ^ τ * X) := by positivity
    have e4 : 0 ≤ K₂ * ((W : ℝ) ^ τ * X) := by positivity
    rw [e1]
    rcases hv with hv | hv <;> linarith
  -- the variance entries
  have hs : ‖cmat (Smat P.ψ W L) p q‖ ≤ K₁ * X := by
    have hval : ‖cmat (Smat P.ψ W L) p q‖ = |fWL P.ψ W L (p - q)| := by
      simp [cmat, Smat, Complex.norm_real, Real.norm_eq_abs]
    have h0 := hC0 W L hadm (p - q)
    rw [pow_zero, one_mul] at h0
    have key := f_le_of_subpoly (L := L) hW1n _ _ C0 Ck (Nat.cast_nonneg _) h0
      (hCk W L hadm (p - q)) (abs_nonneg _)
    have htt : (zdistInf d L (p - q) : ℝ) + W = brk d L W p q := rfl
    rw [htt] at key
    have ht := brk_pos₁ (d := d) (L := L) hW1n p q
    have hu0 : 0 < (W : ℝ) / brk d L W p q := by positivity
    have hu1 : (W : ℝ) / brk d L W p q ≤ 1 := (div_le_one ht).2 (le_brk₁ p q)
    have hupow : ((W : ℝ) / brk d L W p q) ^ (2 * d) ≤ ((W : ℝ) / brk d L W p q) ^ e := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by push_cast; linarith)
    have hWd : (W : ℝ) ^ (-(d : ℝ)) = ((W : ℝ) ^ d)⁻¹ := by
      rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
    rw [hval, hX, hWd]
    calc |fWL P.ψ W L (p - q)| ≤ K₁ * ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) / brk d L W p q) ^ (2 * d) := key
      _ ≤ K₁ * ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) / brk d L W p q) ^ e :=
          mul_le_mul_of_nonneg_left hupow (by positivity)
      _ = _ := by ring
  have hsb := splusBound_le (L := L) hd hW1n τ τ' hτ.le hτ'0.le hτ'e p q
  rw [← hX] at hsb
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

end Wave

/-! ## Bounds on one component -/

/-- The power of `Λ` carried by a component: `1` for solid edges and light weights, `0`
otherwise. -/
private def lamW {V : Type*} (c : Comp V) : ℕ :=
  match c.kind with
  | .G _ => 1
  | .light _ => 1
  | _ => 0

/-- The index of the blue matrix of a component: `1` for solid edges, `0` otherwise. -/
private def blueIdx {V : Type*} (c : Comp V) : ℕ := if c.kind.isSolid then 1 else 0

/-- The blue matrices: `B^{1/2}/C₀` at index `0` and `E/Λ` at the other indices. -/
private def blueMat (d L W : ℕ) (C₀ Λ : ℝ) (E : Matrix (Zd d L) (Zd d L) ℝ) :
    ℕ → Matrix (Zd d L) (Zd d L) ℝ :=
  fun j p q => if j = 0 then Real.sqrt (bB d L W p q) / C₀ else E p q / Λ

/-- The bound of one component at the labelling `σ`: `K Λ^{g} W^{-q d/2}` times `W^d B` on a
black edge and `W^{d/2} |A_j|` on a blue edge, with `q` the scaling order of the component. -/
private def compBnd (d L W : ℕ) (K C₀ Λ : ℝ) (E : Matrix (Zd d L) (Zd d L) ℝ) {V : Type*}
    (σ : V → Zd d L) (c : Comp V) (bk bu : Prop) [Decidable bk] [Decidable bu] : ℝ :=
  K * Λ ^ lamW c * (W : ℝ) ^ (-(c.kind.ord : ℝ) * d / 2) *
    (if bk then (W : ℝ) ^ (d : ℝ) * bB d L W (σ c.x) (σ c.y) else 1) *
    (if bu then (W : ℝ) ^ ((d : ℝ) / 2) *
      |blueMat d L W C₀ Λ E (blueIdx c) (σ c.x) (σ c.y)| else 1)

/-- The four cases of a waved edge: a value `v ≤ K₁ P b a` with `b = a²`, `0 ≤ a ≤ 1`, is at
most `K P` times `b` on a black edge and `a/C₀` on a blue edge. -/
private theorem flag_waved (v K₁ C₀ P a : ℝ) (hK₁ : 0 ≤ K₁) (hC₀ : 1 ≤ C₀) (hP : 0 ≤ P)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hv : v ≤ K₁ * P * (a * a * a)) (bk bu : Prop) [Decidable bk]
    [Decidable bu] :
    v ≤ 2 * C₀ * K₁ * P * (if bk then a * a else 1) * (if bu then a / C₀ else 1) := by
  have hC0 : 0 < C₀ := by linarith
  have haa : a * a ≤ 1 := by nlinarith
  have haaa : a * a * a ≤ a * a := by nlinarith
  have haaa' : a * a * a ≤ a := by nlinarith
  have hKP : 0 ≤ K₁ * P := mul_nonneg hK₁ hP
  have hCa : a / C₀ * C₀ = a := by field_simp
  split_ifs
  · calc v ≤ K₁ * P * (a * a * a) := hv
      _ ≤ 2 * (K₁ * P * (a * a * a)) := by
          nlinarith [mul_nonneg hKP (by positivity : 0 ≤ a * a * a)]
      _ = 2 * C₀ * K₁ * P * (a * a) * (a / C₀) := by field_simp
  · calc v ≤ K₁ * P * (a * a) := hv.trans (mul_le_mul_of_nonneg_left haaa hKP)
      _ ≤ 2 * C₀ * K₁ * P * (a * a) * 1 := by
          have : K₁ * P * (a * a) ≤ 2 * C₀ * (K₁ * P * (a * a)) := by
            have : 0 ≤ K₁ * P * (a * a) := by positivity
            nlinarith
          linarith
  · calc v ≤ K₁ * P * a := hv.trans (mul_le_mul_of_nonneg_left haaa' hKP)
      _ ≤ 2 * (K₁ * P * a) := by nlinarith [mul_nonneg hKP ha0]
      _ = 2 * C₀ * K₁ * P * 1 * (a / C₀) := by field_simp
  · calc v ≤ K₁ * P * 1 := hv.trans (mul_le_mul_of_nonneg_left (haaa.trans haa) hKP)
      _ ≤ 2 * C₀ * K₁ * P * 1 * 1 := by
          have : K₁ * P ≤ 2 * C₀ * (K₁ * P) := by nlinarith
          linarith

/-- The three cases of a `Θ` edge: a value `v ≤ K₁ P b` with `b = a²`, `0 ≤ a ≤ 1`, is at most
`K P` times `b` on a black edge and `a/C₀` on a blue edge, the edge being not both. -/
private theorem flag_theta (v K₁ C₀ P a : ℝ) (hK₁ : 0 ≤ K₁) (hC₀ : 1 ≤ C₀) (hP : 0 ≤ P)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hv : v ≤ K₁ * P * (a * a)) (bk bu : Prop) [Decidable bk]
    [Decidable bu] (hboth : bk → bu → False) :
    v ≤ 2 * C₀ * K₁ * P * (if bk then a * a else 1) * (if bu then a / C₀ else 1) := by
  have hC0 : 0 < C₀ := by linarith
  have haa : a * a ≤ 1 := by nlinarith
  have haa' : a * a ≤ a := by nlinarith
  have hKP : 0 ≤ K₁ * P := mul_nonneg hK₁ hP
  split_ifs with h1 h2
  · exact (hboth h1 h2).elim
  · calc v ≤ K₁ * P * (a * a) := hv
      _ ≤ 2 * C₀ * K₁ * P * (a * a) * 1 := by
          have : K₁ * P * (a * a) ≤ 2 * C₀ * (K₁ * P * (a * a)) := by
            have : 0 ≤ K₁ * P * (a * a) := by positivity
            nlinarith
          linarith
  · calc v ≤ K₁ * P * a := hv.trans (mul_le_mul_of_nonneg_left haa' hKP)
      _ ≤ 2 * (K₁ * P * a) := by nlinarith [mul_nonneg hKP ha0]
      _ = 2 * C₀ * K₁ * P * 1 * (a / C₀) := by field_simp
  · calc v ≤ K₁ * P * 1 := hv.trans (mul_le_mul_of_nonneg_left haa hKP)
      _ ≤ 2 * C₀ * K₁ * P * 1 * 1 := by
          have : K₁ * P ≤ 2 * C₀ * (K₁ * P) := by nlinarith
          linarith

/-- The bound of one component of a graph with the kinds of [II, Def 3.2 (2)] and no dotted edge,
from the pointwise bounds on `G - m`, on the waved edges and on the labelled `Θ` edges: for a
labelling `σ` under which a solid edge joins distinct points, the factor of the component is at
most `compBnd` with `K = 2 C₀ K₁`. -/
private theorem comp_le {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (D : Data (Zd d L)) (N : ℕ)
    (E : Matrix (Zd d L) (Zd d L) ℝ) (K₁ C₀ Λ : ℝ) (hK₁ : 1 ≤ K₁) (hC₀ : 1 ≤ C₀) (hΛ : 1 ≤ Λ)
    (hm : ‖D.m‖ ≤ 1)
    (hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = E p q)
    (hE : ∀ p q, E p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ)
    (hΛW : (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ ≤ 1)
    (hwav : ∀ (w : Wave) (p q : Zd d L), ‖Comp.val D id (⟨.waved w, p, q, [], none⟩ : Comp _)‖ ≤
      K₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    {V : Type*} (σ : V → Zd d L) (c : Comp V)
    (hth : ∀ o, c.kind = .theta o → ∀ p q, ‖D.chain o p q‖ ≤
      K₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    (hc : c.isTKind N = true) (hdot : c.kind ≠ .dot)
    (hgood : c.kind.isSolid = true → σ c.x ≠ σ c.y)
    (bk bu : Prop) [Decidable bk] [Decidable bu]
    (hbk : bk → (∃ o, c.kind = .theta o) ∨ ∃ w, c.kind = .waved w)
    (hbu : bu → (∃ o, c.kind = .theta o) ∨ (∃ ch, c.kind = .G ch) ∨ ∃ w, c.kind = .waved w)
    (hboth : bk → bu → ∃ w, c.kind = .waved w) :
    ‖Comp.val D σ c‖ ≤ compBnd d L W (2 * C₀ * K₁) C₀ Λ E σ c bk bu := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hC0 : 0 < C₀ := by linarith
  obtain ⟨κ, x, y, mi, lab⟩ := c
  have hmi : mi = [] := by
    simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at hc
    exact hc.1
  subst hmi
  set p := σ x with hp
  set q := σ y with hq
  set a := (W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := rpow_mul_sqrt_bB_le hd hW p q
  have hb : (W : ℝ) ^ (d : ℝ) * bB d L W p q = a * a := by
    rw [ha, mul_mul_mul_comm, Real.mul_self_sqrt (bB_pos₁ hW p q).le, ← Real.rpow_add hW0]
    ring_nf
  have hab : (W : ℝ) ^ ((d : ℝ) / 2) * |Real.sqrt (bB d L W p q) / C₀| = a / C₀ := by
    rw [abs_of_nonneg (by positivity), ha]; ring
  have hG : ∀ ch : Charge, ∀ u : ℂ, ‖ch.apply u‖ = ‖u‖ := by
    intro ch u; cases ch <;> simp [Charge.apply]
  have hG0 : D.Gm (([] : List V).map σ).toFinset = D.Gm ∅ := by simp
  have hP1 : (W : ℝ) ^ (-(1 : ℝ) * d / 2) * (W : ℝ) ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hW0]; ring_nf; exact Real.rpow_zero _
  have hK₁0 : (0 : ℝ) ≤ K₁ := by linarith
  have hEnn : ∀ p q, 0 ≤ E p q := fun p q => by rw [← hEeq]; exact norm_nonneg _
  cases κ with
  | G ch =>
    have hbk' : ¬ bk := fun h => by
      rcases hbk h with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
    have hne : p ≠ q := hgood rfl
    have hval : ‖Comp.val D σ (⟨.G ch, x, y, [], lab⟩ : Comp V)‖ = E p q := by
      simp only [Comp.val, hG0]
      rw [hG ch, ← hEeq]; simp [hne]
      rfl
    rw [hval]
    unfold compBnd
    simp only [lamW, blueIdx, Kind.isSolid, hbk', ↓reduceIte, mul_one, pow_one]
    have hord : (((Kind.G ch).ord : ℤ) : ℝ) = 1 := by simp [Kind.ord]
    rw [hord]
    split_ifs with hbu'
    · simp only [blueMat, one_ne_zero, ↓reduceIte]
      rw [abs_of_nonneg (div_nonneg (hEnn p q) (by linarith))]
      have hΛ0 : 0 < Λ := by linarith
      calc E p q = (W : ℝ) ^ (-(1 : ℝ) * d / 2) * (W : ℝ) ^ ((d : ℝ) / 2) * E p q := by
            rw [hP1, one_mul]
        _ ≤ 2 * C₀ * K₁ * ((W : ℝ) ^ (-(1 : ℝ) * d / 2) * (W : ℝ) ^ ((d : ℝ) / 2) * E p q) := by
            rw [hP1, one_mul]
            have : 1 ≤ 2 * C₀ * K₁ := by nlinarith
            nlinarith [hEnn p q]
        _ = 2 * C₀ * K₁ * Λ * (W : ℝ) ^ (-(1 : ℝ) * d / 2) *
              ((W : ℝ) ^ ((d : ℝ) / 2) * (E p q / Λ)) := by field_simp
    · have h1 := hE p q
      have : 1 ≤ 2 * C₀ * K₁ := by nlinarith
      have h2 : 0 ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ := by positivity
      calc E p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ := h1
        _ ≤ 2 * C₀ * K₁ * ((W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ) := le_mul_of_one_le_left h2 this
        _ = _ := by ring
  | weight ch =>
    have hbk' : ¬ bk := fun h => by
      rcases hbk h with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
    have hbu' : ¬ bu := fun h => by
      rcases hbu h with ⟨o, ho⟩ | ⟨c', hc'⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hc' | cases hw
    have hval : ‖Comp.val D σ (⟨.weight ch, x, y, [], lab⟩ : Comp V)‖ ≤ 2 := by
      simp only [Comp.val, hG0]
      rw [hG ch]
      have h1 := hEeq p p
      simp only [↓reduceIte] at h1
      have h2 := hE p p
      calc ‖D.Gm ∅ p p‖ = ‖(D.Gm ∅ p p - D.m) + D.m‖ := by ring_nf
        _ ≤ ‖D.Gm ∅ p p - D.m‖ + ‖D.m‖ := norm_add_le _ _
        _ ≤ 2 := by linarith
    refine hval.trans ?_
    unfold compBnd
    simp only [lamW, hbk', hbu', ↓reduceIte, mul_one, pow_zero]
    have hord : (((Kind.weight ch).ord : ℤ) : ℝ) = 0 := by simp [Kind.ord]
    rw [hord]
    simp only [neg_zero, zero_mul, zero_div, Real.rpow_zero, mul_one]
    nlinarith
  | light ch =>
    have hbk' : ¬ bk := fun h => by
      rcases hbk h with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
    have hbu' : ¬ bu := fun h => by
      rcases hbu h with ⟨o, ho⟩ | ⟨c', hc'⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hc' | cases hw
    have hval : ‖Comp.val D σ (⟨.light ch, x, y, [], lab⟩ : Comp V)‖ = E p p := by
      simp only [Comp.val, hG0]
      rw [hG ch, ← hEeq]
      simp
      rfl
    rw [hval]
    unfold compBnd
    simp only [lamW, hbk', hbu', ↓reduceIte, mul_one, pow_one]
    have hord : (((Kind.light ch).ord : ℤ) : ℝ) = 1 := by simp [Kind.ord]
    rw [hord]
    have : 1 ≤ 2 * C₀ * K₁ := by nlinarith
    have h2 : 0 ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ := by positivity
    calc E p p ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ := hE p p
      _ ≤ 2 * C₀ * K₁ * ((W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ) := le_mul_of_one_le_left h2 this
      _ = _ := by ring
  | waved w =>
    have hval : ‖Comp.val D σ (⟨.waved w, x, y, [], lab⟩ : Comp V)‖ =
        ‖Comp.val D id (⟨.waved w, p, q, [], none⟩ : Comp _)‖ := by
      cases w <;> rfl
    rw [hval]
    unfold compBnd
    simp only [lamW, blueIdx, Kind.isSolid, Bool.false_eq_true, ↓reduceIte, pow_zero, mul_one]
    have hord : (((Kind.waved w).ord : ℤ) : ℝ) = 2 := by simp [Kind.ord]
    rw [hord]
    simp only [blueMat, ↓reduceIte]
    rw [hb, hab]
    exact flag_waved _ K₁ C₀ _ a hK₁0 hC₀ (by positivity) ha0 ha1 (hwav w p q) bk bu
  | theta o =>
    have hl : labelOK N o = true := by
      simp only [Comp.isTKind, Bool.and_eq_true] at hc
      exact hc.2
    have hval : ‖Comp.val D σ (⟨.theta o, x, y, [], lab⟩ : Comp V)‖ = ‖D.chain o p q‖ := rfl
    rw [hval]
    unfold compBnd
    simp only [lamW, blueIdx, Kind.isSolid, Bool.false_eq_true, ↓reduceIte, pow_zero, mul_one]
    simp only [blueMat, ↓reduceIte]
    rw [hb, hab]
    exact flag_theta _ K₁ C₀ _ a hK₁0 hC₀ (by positivity) ha0 ha1 (hth o rfl p q) bk bu
      (fun h1 h2 => by obtain ⟨w, hw⟩ := hboth h1 h2; cases hw)
  | thetaErr n D' => simp [Comp.isTKind] at hc
  | ghost => simp [Comp.isTKind] at hc
  | inv c => simp [Comp.isTKind] at hc
  | wD c D' => simp [Comp.isTKind] at hc
  | aux j r b => simp [Comp.isTKind] at hc
  | dot => exact (hdot rfl).elim
  | xdot =>
    have hbk' : ¬ bk := fun h => by
      rcases hbk h with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
    have hbu' : ¬ bu := fun h => by
      rcases hbu h with ⟨o, ho⟩ | ⟨c', hc'⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hc' | cases hw
    have hval : ‖Comp.val D σ (⟨.xdot, x, y, [], lab⟩ : Comp V)‖ ≤ 1 := by
      simp only [Comp.val]
      split_ifs <;> simp
    refine hval.trans ?_
    unfold compBnd
    simp only [lamW, hbk', hbu', ↓reduceIte, mul_one, pow_zero]
    have hord : ((Kind.xdot.ord : ℤ) : ℝ) = 0 := by simp [Kind.ord]
    rw [hord]
    simp only [neg_zero, zero_mul, zero_div, Real.rpow_zero, mul_one]
    nlinarith

/-- `compBnd` is nonnegative. -/
private theorem compBnd_nonneg {d L W : ℕ} (K C₀ Λ : ℝ) (hK : 0 ≤ K) (hΛ : 0 ≤ Λ)
    (E : Matrix (Zd d L) (Zd d L) ℝ) {V : Type*} (σ : V → Zd d L) (c : Comp V) (bk bu : Prop)
    [Decidable bk] [Decidable bu] : 0 ≤ compBnd d L W K C₀ Λ E σ c bk bu := by
  unfold compBnd
  have h1 : 0 ≤ (if bk then (W : ℝ) ^ (d : ℝ) * bB d L W (σ c.x) (σ c.y) else 1) := by
    split_ifs
    · unfold bB; positivity
    · norm_num
  have h2 : 0 ≤ (if bu then (W : ℝ) ^ ((d : ℝ) / 2) *
      |blueMat d L W C₀ Λ E (blueIdx c) (σ c.x) (σ c.y)| else 1) := by
    split_ifs
    · positivity
    · norm_num
  have h3 : 0 ≤ K * Λ ^ lamW c * (W : ℝ) ^ (-(c.kind.ord : ℝ) * d / 2) := by positivity
  exact mul_nonneg (mul_nonneg h3 h1) h2

/-- `(Π_{i ∈ l} c f(i)) = c^{|l|} Π_{i ∈ l} f(i)`. -/
private theorem list_prod_map_const_mul {ι : Type*} (l : List ι) (c : ℝ) (f : ι → ℝ) :
    (l.map fun i => c * f i).prod = c ^ l.length * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]; ring

/-- The product of the factors of all components at the labelling `σ` is at most the product of
the bounds `compBnd`, the black and blue flags being membership in the lists `bl`, `bu`. A
labelling under which a solid edge joins equal points gives `0`, by its `×`-dotted edge. -/
private theorem prod_le {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (D : Data (Zd d L))
    (N : ℕ) (E : Matrix (Zd d L) (Zd d L) ℝ) (K₁ C₀ Λ : ℝ) (hK₁ : 1 ≤ K₁) (hC₀ : 1 ≤ C₀)
    (hΛ : 1 ≤ Λ) (hm : ‖D.m‖ ≤ 1)
    (hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = E p q)
    (hE : ∀ p q, E p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ)
    (hΛW : (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ ≤ 1)
    (hwav : ∀ (w : Wave) (p q : Zd d L), ‖Comp.val D id (⟨.waved w, p, q, [], none⟩ : Comp _)‖ ≤
      K₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    {k n : ℕ} (Γ : Graph k n)
    (hth : ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ p q, ‖D.chain o p q‖ ≤
      K₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    (hT : Γ.TKinds N) (hdot : ∀ c ∈ Γ.comps, c.kind ≠ .dot)
    (hxd : ∀ c ∈ Γ.comps, c.kind.isSolid = true → ∃ c' ∈ Γ.comps, c'.kind = .xdot ∧
      ((c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)))
    (bl bu : List (Fin Γ.comps.length))
    (hbk : ∀ i ∈ bl, (∃ o, Γ.comps[i].kind = .theta o) ∨ ∃ w, Γ.comps[i].kind = .waved w)
    (hbu : ∀ i ∈ bu, (∃ o, Γ.comps[i].kind = .theta o) ∨ (∃ ch, Γ.comps[i].kind = .G ch) ∨
      ∃ w, Γ.comps[i].kind = .waved w)
    (hboth : ∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w)
    (σ : Atom k n → Zd d L) :
    (Γ.comps.map fun c => ‖Comp.val D σ c‖).prod ≤
      ∏ i : Fin Γ.comps.length,
        compBnd d L W (2 * C₀ * K₁) C₀ Λ E σ Γ.comps[i] (i ∈ bl) (i ∈ bu) := by
  have hK0 : 0 ≤ 2 * C₀ * K₁ := by nlinarith
  by_cases hgood : ∀ c ∈ Γ.comps, c.kind.isSolid = true → σ c.x ≠ σ c.y
  · rw [← Fin.prod_univ_fun_getElem]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    have hTi : Γ.comps[i].isTKind N = true := by
      unfold Graph.TKinds at hT; rw [List.all_eq_true] at hT; exact hT _ hmem
    exact comp_le hd hW D N E K₁ C₀ Λ hK₁ hC₀ hΛ hm hEeq hE hΛW hwav σ Γ.comps[i]
      (hth _ hmem) hTi
      (hdot _ hmem) (hgood _ hmem) (i ∈ bl) (i ∈ bu) (hbk i) (hbu i) (hboth i)
  · push Not at hgood
    obtain ⟨c, hc, hsol, heq⟩ := hgood
    obtain ⟨c', hc', hk', hxy⟩ := hxd c hc hsol
    have h0 : ‖Comp.val D σ c'‖ = 0 := by
      have heq' : σ c'.x = σ c'.y := by
        rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact heq
        · rw [h1, h2]; exact heq.symm
      obtain ⟨κ, x, y, mi, lab⟩ := c'
      simp only at hk' heq'
      subst hk'
      simp [Comp.val, heq']
    have hzero : (Γ.comps.map fun c => ‖Comp.val D σ c‖).prod = 0 :=
      List.prod_eq_zero (List.mem_map.2 ⟨c', hc', h0⟩)
    rw [hzero]
    exact Finset.prod_nonneg fun i _ =>
      compBnd_nonneg _ _ _ hK0 (by linarith) E σ _ _ _

/-- The product of the bounds `compBnd` over the components factors into the constant part, the
black edges and the blue edges. -/
private theorem prod_compBnd {d L W : ℕ} (hW : 1 ≤ W) (K C₀ Λ : ℝ)
    (E : Matrix (Zd d L) (Zd d L) ℝ) {k n : ℕ} (Γ : Graph k n) (bl bu : List (Fin Γ.comps.length))
    (hbl : bl.Nodup) (hbu : bu.Nodup) (σ : Atom k n → Zd d L) :
    ∏ i : Fin Γ.comps.length, compBnd d L W K C₀ Λ E σ Γ.comps[i] (i ∈ bl) (i ∈ bu) =
      K ^ Γ.comps.length * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length) *
        ((bl.map fun i => bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y)).prod *
          (bu.map fun i => |blueMat d L W C₀ Λ E (blueIdx Γ.comps[i]) (σ Γ.comps[i].x)
            (σ Γ.comps[i].y)|).prod) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold compBnd
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  have h1 : ∏ i : Fin Γ.comps.length, (if i ∈ bl then (W : ℝ) ^ (d : ℝ) *
      bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y) else 1) =
      ((W : ℝ) ^ (d : ℝ)) ^ bl.length *
        (bl.map fun i => bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y)).prod := by
    simp_rw [← List.mem_toFinset (l := bl)]
    rw [Finset.prod_ite_mem, Finset.univ_inter, List.prod_toFinset _ hbl, list_prod_map_const_mul]
  have h2 : ∏ i : Fin Γ.comps.length, (if i ∈ bu then (W : ℝ) ^ ((d : ℝ) / 2) *
      |blueMat d L W C₀ Λ E (blueIdx Γ.comps[i]) (σ Γ.comps[i].x) (σ Γ.comps[i].y)| else 1) =
      ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length *
        (bu.map fun i => |blueMat d L W C₀ Λ E (blueIdx Γ.comps[i]) (σ Γ.comps[i].x)
          (σ Γ.comps[i].y)|).prod := by
    simp_rw [← List.mem_toFinset (l := bu)]
    rw [Finset.prod_ite_mem, Finset.univ_inter, List.prod_toFinset _ hbu, list_prod_map_const_mul]
  rw [h1, h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum,
    ← Real.rpow_sum_of_pos hW0]
  ring

/-- The absolute-value graph is at most `|coeff| (2 C₀ K₁)^{|Γ|} Λ^{Σ g} W^{-Σ q d/2} (W^d)^{|bl|}
(W^{d/2})^{|bu|}` times the sum over the internal labels of the product of `B` over the black
edges and of `|A_j|` over the blue edges. -/
private theorem absVal_le {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (D : Data (Zd d L))
    (N : ℕ) (E : Matrix (Zd d L) (Zd d L) ℝ) (K₁ C₀ Λ : ℝ) (hK₁ : 1 ≤ K₁) (hC₀ : 1 ≤ C₀)
    (hΛ : 1 ≤ Λ) (hm : ‖D.m‖ ≤ 1)
    (hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = E p q)
    (hE : ∀ p q, E p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ)
    (hΛW : (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ ≤ 1)
    (hwav : ∀ (w : Wave) (p q : Zd d L), ‖Comp.val D id (⟨.waved w, p, q, [], none⟩ : Comp _)‖ ≤
      K₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    {k n : ℕ} (Γ : Graph k n)
    (hth : ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ p q, ‖D.chain o p q‖ ≤
      K₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    (hT : Γ.TKinds N) (hdot : ∀ c ∈ Γ.comps, c.kind ≠ .dot)
    (hxd : ∀ c ∈ Γ.comps, c.kind.isSolid = true → ∃ c' ∈ Γ.comps, c'.kind = .xdot ∧
      ((c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)))
    (bl bu : List (Fin Γ.comps.length)) (hbl : bl.Nodup) (hbu' : bu.Nodup)
    (hbk : ∀ i ∈ bl, (∃ o, Γ.comps[i].kind = .theta o) ∨ ∃ w, Γ.comps[i].kind = .waved w)
    (hbu : ∀ i ∈ bu, (∃ o, Γ.comps[i].kind = .theta o) ∨ (∃ ch, Γ.comps[i].kind = .G ch) ∨
      ∃ w, Γ.comps[i].kind = .waved w)
    (hboth : ∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w)
    (e : Fin k → Zd d L) :
    Γ.absVal D e ≤ ‖Γ.coeff.eval D.m‖ *
      ((2 * C₀ * K₁) ^ Γ.comps.length * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length)) *
      ∑ s : Fin n → Zd d L,
        ((bl.map fun i => bB d L W (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y)).prod *
          (bu.map fun i => |blueMat d L W C₀ Λ E (blueIdx Γ.comps[i]) (Sum.elim e s Γ.comps[i].x)
            (Sum.elim e s Γ.comps[i].y)|).prod) := by
  unfold Graph.absVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 := prod_le hd hW D N E K₁ C₀ Λ hK₁ hC₀ hΛ hm hEeq hE hΛW hwav Γ hth hT hdot hxd bl bu
    hbk hbu hboth (Sum.elim e s)
  have hW' : 1 ≤ W := hW
  rw [prod_compBnd hW' _ C₀ Λ E Γ bl bu hbl hbu' (Sum.elim e s)] at h1
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

private theorem intAtom_eq {k n : ℕ} (u : Atom k n) :
    intAtom k n u = Sum.inr (finSumFinEquiv u) := by
  cases u <;> rfl

private theorem extAtom_intAtom {k n : ℕ} (u : Atom k n) : extAtom k n (intAtom k n u) = u := by
  rw [intAtom_eq]; simp [extAtom]

private theorem intAtom_injective {k n : ℕ} : Function.Injective (intAtom k n) := fun u v h => by
  rw [← extAtom_intAtom u, ← extAtom_intAtom v, h]

private theorem internalize_comps {k n : ℕ} (Γ : Graph k n) :
    Γ.internalize.comps = Γ.comps.map (Comp.map (intAtom k n)) := rfl

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

/-- Under `Normal`, every solid edge of `Γ` joins distinct atoms that are also joined by a
`×`-dotted edge. -/
private theorem xdot_of_normal {k n C : ℕ} (Γ : Graph k n) (hN : Γ.internalize.Normal C) :
    ∀ c ∈ Γ.comps, c.kind.isSolid = true → ∃ c' ∈ Γ.comps, c'.kind = .xdot ∧
      ((c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)) := by
  intro c hc hs
  obtain ⟨-, h2, h3⟩ := hN
  have hmem : Comp.map (intAtom k n) c ∈ Γ.internalize.comps := by
    rw [internalize_comps]; exact List.mem_map_of_mem hc
  have hne : intAtom k n c.x ≠ intAtom k n c.y := h2 _ hmem hs
  obtain ⟨c'', hc'', hk, hxy⟩ := (h3 _ _ hne).2 ⟨_, hmem, hs, Or.inl ⟨rfl, rfl⟩⟩
  rw [internalize_comps] at hc''
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc''
  refine ⟨c', hc', hk, ?_⟩
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨intAtom_injective h1, intAtom_injective h2⟩
  · exact Or.inr ⟨intAtom_injective h1, intAtom_injective h2⟩

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

/-- A diffusive component with the kinds of [II, Def 3.2 (2)] is a `Θ` edge. -/
private theorem tkind_diff {V : Type*} {N : ℕ} (c : Comp V) (h : c.isTKind N = true)
    (hd : c.kind.isDiffusive = true) : ∃ o, c.kind = .theta o := by
  obtain ⟨κ, x, y, m, l⟩ := c
  cases κ <;> simp_all [Comp.isTKind, Kind.isDiffusive]

/-- A blue component with the kinds of [II, Def 3.2 (2)] is a solid edge. -/
private theorem tkind_blue {V : Type*} {N : ℕ} (c : Comp V) (h : c.isTKind N = true)
    (hb : c.kind.isBlue = true) : ∃ ch, c.kind = .G ch := by
  obtain ⟨κ, x, y, m, l⟩ := c
  cases κ <;> simp_all [Comp.isTKind, Kind.isBlue]

/-- [I, Def 6.5] for the internal form of `Γ`, read on the atoms of `Γ`: there are a black and a
blue list of distinct components, each forming a spanning tree of the atoms, the black ones `Θ` or
waved edges, the blue ones `Θ`, solid or waved edges, and a component in both lists is a waved
edge. -/
private theorem dc_trees {k n : ℕ} (hk : 0 < k) (Γ : Graph k n) (C N : ℕ)
    (hNo : Γ.internalize.Normal C) (hDC : Γ.internalize.DoublyConnected) (hT : Γ.TKinds N) :
    ∃ bl bu : List (Fin Γ.comps.length), bl.Nodup ∧ bu.Nodup ∧
      (∀ i ∈ bl, (∃ o, Γ.comps[i].kind = .theta o) ∨ ∃ w, Γ.comps[i].kind = .waved w) ∧
      (∀ i ∈ bu, (∃ o, Γ.comps[i].kind = .theta o) ∨ (∃ ch, Γ.comps[i].kind = .G ch) ∨
        ∃ w, Γ.comps[i].kind = .waved w) ∧
      (∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w) ∧
      TreeEdges (bl.map fun i => (Γ.comps[i].x, Γ.comps[i].y)) ∧
      TreeEdges (bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y)) := by
  obtain ⟨black, blue, hdisj, hbk, hbu, hsb, hsu⟩ := hDC
  have hR := hNo.1
  have hkind : ∀ (j : Fin Γ.internalize.comps.length) (i : Fin Γ.comps.length), j.1 = i.1 →
      Γ.internalize.comps[j].kind = Γ.comps[i].kind := fun j i h => by
    rw [internalize_getElem Γ j i h]; rfl
  have hTi : ∀ i : Fin Γ.comps.length, Γ.comps[i].isTKind N = true := by
    intro i
    unfold Graph.TKinds at hT
    rw [List.all_eq_true] at hT
    exact hT _ (List.getElem_mem _)
  obtain ⟨bl, hbl, hblS, hblT⟩ := exists_tree (fun i : Fin Γ.comps.length =>
    (Γ.comps[i].x, Γ.comps[i].y)) _ (conn_of_spans hk Γ C hR black hsb)
  obtain ⟨bu, hbu', hbuS, hbuT⟩ := exists_tree (fun i : Fin Γ.comps.length =>
    (Γ.comps[i].x, Γ.comps[i].y)) _ (conn_of_spans hk Γ C hR blue hsu)
  refine ⟨bl, bu, hbl, hbu', ?_, ?_, ?_, hblT, hbuT⟩
  · intro i hi
    rcases hblS i hi with ⟨j, hj, hji⟩ | hw
    · exact Or.inl (tkind_diff _ (hTi i) (by rw [← hkind j i hji]; exact hbk j hj))
    · exact Or.inr hw
  · intro i hi
    rcases hbuS i hi with ⟨j, hj, hji⟩ | hw
    · rcases hbu j hj with h | h
      · exact Or.inl (tkind_diff _ (hTi i) (by rw [← hkind j i hji]; exact h))
      · exact Or.inr (Or.inl (tkind_blue _ (hTi i) (by rw [← hkind j i hji]; exact h)))
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

/-! ## Counting the powers of `Λ` -/

/-- A label of entries at least `4` has sum at least `4` times its length. -/
private theorem four_mul_length_le (o : List ℕ) (h : ∀ j ∈ o, 4 ≤ j) : 4 * o.length ≤ o.sum := by
  induction o with
  | nil => simp
  | cons a o ih =>
    have ha := h a (by simp)
    have := ih fun j hj => h j (by simp [hj])
    simp only [List.length_cons, List.sum_cons]
    omega

/-- A component with the kinds of [II, Def 3.2 (2)] has scaling order at least its power of `Λ`,
and at least `2` (with no power of `Λ`) if it is a `Θ` or a waved edge. -/
private theorem lamW_le_ord {V : Type*} {N : ℕ} (c : Comp V) (h : c.isTKind N = true) :
    (lamW c : ℝ) ≤ (c.kind.ord : ℝ) ∧
      (((∃ o, c.kind = .theta o) ∨ ∃ w, c.kind = .waved w) →
        lamW c = 0 ∧ (2 : ℝ) ≤ (c.kind.ord : ℝ)) := by
  obtain ⟨κ, x, y, m, l⟩ := c
  cases κ with
  | theta o =>
    have hl : labelOK N o = true := by
      simp only [Comp.isTKind, Bool.and_eq_true] at h; exact h.2
    have h4 : ∀ j ∈ o, 4 ≤ j := by
      intro j hj
      simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hl
      exact (hl j hj).1.1
    have := four_mul_length_le o h4
    have h2 : (2 : ℤ) ≤ (Kind.theta o).ord := by simp only [Kind.ord]; omega
    have h2' : (2 : ℝ) ≤ ((Kind.theta o).ord : ℝ) := by exact_mod_cast h2
    refine ⟨?_, fun _ => ⟨rfl, h2'⟩⟩
    simp only [lamW, Nat.cast_zero]; linarith
  | waved w =>
    have h2 : ((Kind.waved w).ord : ℝ) = 2 := by simp [Kind.ord]
    exact ⟨by simp only [lamW, h2]; norm_num, fun _ => ⟨rfl, h2.ge⟩⟩
  | G ch =>
    refine ⟨by simp [lamW, Kind.ord], fun h' => ?_⟩
    rcases h' with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
  | weight ch =>
    refine ⟨by simp [lamW, Kind.ord], fun h' => ?_⟩
    rcases h' with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
  | light ch =>
    refine ⟨by simp [lamW, Kind.ord], fun h' => ?_⟩
    rcases h' with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
  | dot =>
    refine ⟨by simp [lamW, Kind.ord], fun h' => ?_⟩
    rcases h' with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
  | xdot =>
    refine ⟨by simp [lamW, Kind.ord], fun h' => ?_⟩
    rcases h' with ⟨o, ho⟩ | ⟨w, hw⟩ <;> first | cases ho | cases hw
  | thetaErr n D' => simp [Comp.isTKind] at h
  | ghost => simp [Comp.isTKind] at h
  | inv c => simp [Comp.isTKind] at h
  | wD c D' => simp [Comp.isTKind] at h
  | aux j r b => simp [Comp.isTKind] at h

/-- The scaling orders of the components exceed twice the number of black edges plus the total
power of `Λ`: `Σ_i q_i ≥ 2 |bl| + Σ_i g_i`. -/
private theorem count_le {k n N : ℕ} (Γ : Graph k n) (hT : Γ.TKinds N)
    (bl : List (Fin Γ.comps.length)) (hbl : bl.Nodup)
    (hbk : ∀ i ∈ bl, (∃ o, Γ.comps[i].kind = .theta o) ∨ ∃ w, Γ.comps[i].kind = .waved w) :
    2 * (bl.length : ℝ) + ∑ i : Fin Γ.comps.length, (lamW Γ.comps[i] : ℝ) ≤
      ∑ i : Fin Γ.comps.length, (Γ.comps[i].kind.ord : ℝ) := by
  classical
  have hTi : ∀ i : Fin Γ.comps.length, Γ.comps[i].isTKind N = true := by
    intro i
    unfold Graph.TKinds at hT
    rw [List.all_eq_true] at hT
    exact hT _ (List.getElem_mem _)
  have hpt : ∀ i : Fin Γ.comps.length,
      (lamW Γ.comps[i] : ℝ) + (if i ∈ bl.toFinset then 2 else 0) ≤ (Γ.comps[i].kind.ord : ℝ) := by
    intro i
    obtain ⟨h1, h2⟩ := lamW_le_ord _ (hTi i)
    split_ifs with hi
    · obtain ⟨h3, h4⟩ := h2 (hbk i (List.mem_toFinset.1 hi))
      rw [h3, Nat.cast_zero]; linarith
    · linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    List.toFinset_card_of_nodup hbl, nsmul_eq_mul] at hsum
  linarith

/-! ## The inputs on the data record `gData` -/

/-- `0 < Im z` on the spectral domain for `W ≥ 1`. -/
private theorem im_pos_of_specDom {κ ε : ℝ} {W L : ℕ} [NeZero L] (hW : 1 ≤ W) {z : ℂ}
    (hz : z ∈ specDom κ ε W L) : 0 < z.im := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact lt_of_lt_of_le (by positivity) hz.2.1

/-- `(W^{d/2} B^{1/2})² = W^d B`. -/
private theorem sq_half_eq {d L W : ℕ} (hW : 1 ≤ W) (p q : Zd d L) :
    ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
        ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) =
      (W : ℝ) ^ (d : ℝ) * bB d L W p q := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [mul_mul_mul_comm, Real.mul_self_sqrt (bB_pos₁ hW p q).le, ← Real.rpow_add hW0]
  ring_nf

/-- The pointwise inputs on `gData`: for every `τ₁ > 0` there are `K ≥ 1` and `W₀ ≥ 1` such that
along `adm(c₀, c₁)`, for `W ≥ W₀`, `z ∈ 𝐃(κ, ε)` and every matrix `G`, with `a = W^{d/2} B^{1/2}`:
`|s_{xy}|, |S^±_{xy}| ≤ K W^{τ₁} W^{-d} a³` and, for the labelled `Θ` edges of `Γ` of scaling
order `k`, `|(Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ)_{xy}| ≤ K W^{τ₁} W^{-kd/2} a²` ([I, (1.8)],
[I, Lemma 2.2] and [I, Lemma 6.2]). -/
private theorem gData_inputs (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (Sig : ℕ → Expansion 2)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) {k n : ℕ} (Γ : Graph k n) (hT : Γ.TKinds N)
    (τ₁ : ℝ) (hτ₁ : 0 < τ₁) :
    ∃ K W₀ : ℝ, 1 ≤ K ∧ 1 ≤ W₀ ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
        (∀ (w : Wave) (p q : Zd d L),
          ‖Comp.val (gData (Smat P.ψ W L) z Sig G) id (⟨.waved w, p, q, [], none⟩ : Comp _)‖ ≤
            K * (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
              (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
                ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
                ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)))) ∧
        (∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ p q,
          ‖(gData (Smat P.ψ W L) z Sig G).chain o p q‖ ≤
            K * (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
              (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
                ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)))) := by
  obtain ⟨Kw, Ww, hKw, hw⟩ := wave_bound d (by omega) P c₀ c₁ κ hc₀ hc₁ hκ τ₁ hτ₁
  have hth : ∀ i : Fin Γ.comps.length, ∃ W₀ : ℝ, ∀ o, Γ.comps[i].kind = .theta o →
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ x y : Zd d L,
          ‖(detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)).chain o x y‖ ≤
            (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              bB d L W x y := by
    intro i
    by_cases h : ∃ o, Γ.comps[i].kind = .theta o
    · obtain ⟨o, ho⟩ := h
      have hTi : Γ.comps[i].isTKind N = true := by
        unfold Graph.TKinds at hT
        rw [List.all_eq_true] at hT
        exact hT _ (List.getElem_mem _)
      have hl : labelOK N o = true := by
        simp only [Comp.isTKind, ho, Bool.and_eq_true] at hTi; exact hTi.2
      have hK : ∀ l ∈ o,
          KerSymm (sigKer (smatVar P) Sig) l ∧ KerBound (sigKer (smatVar P) Sig) l := by
        intro l hlo
        simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          at hl
        obtain ⟨⟨h4, hN⟩, h2⟩ := hl l hlo
        have hse := hSig l h4 hN (Nat.even_iff.2 h2)
        exact ⟨hse.2.1, hse.2.2⟩
      obtain ⟨W₀, hW₀⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε _ o hK τ₁ hτ₁
      obtain ⟨W₁, hW₁⟩ := detData_smatVar_eq_on_adm d P Sig c₀ c₁ hc₀ hc₁
      refine ⟨max W₀ W₁, fun o' ho' => ?_⟩
      rw [ho] at ho'
      cases ho'
      intro W L _ hadm hW z hz x y
      rw [← hW₁ W L hadm ((le_max_right _ _).trans hW) z]
      exact hW₀ W L hadm ((le_max_left _ _).trans hW) z hz x y
    · exact ⟨0, fun o ho => (h ⟨o, ho⟩).elim⟩
  choose Wth hWth using hth
  refine ⟨Kw, max 1 (max Ww (∑ i, |Wth i|)), hKw, le_max_left _ _,
    fun W L _ hadm hW z hz G => ⟨fun w p q => ?_, fun c hc o ho p q => ?_⟩⟩
  · have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hW
    have hW1n : 1 ≤ W := by exact_mod_cast hW1
    have hW0 : (0 : ℝ) < W := by linarith
    have him := im_pos_of_specDom hW1n hz
    obtain ⟨hs, hp, hm⟩ := hw W L hadm ((le_max_left _ _).trans ((le_max_right _ _).trans hW))
      hW1n z him hz.1 p q
    have hkey : bB d L W p q * ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) =
        (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
          (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
            ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
            ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))) := by
      have h1 : (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (W : ℝ) ^ (d : ℝ) = 1 := by
        rw [← Real.rpow_add hW0, show -(2 : ℝ) * d / 2 + d = 0 by ring, Real.rpow_zero]
      rw [sq_half_eq hW1n]
      calc bB d L W p q * ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))
          = ((W : ℝ) ^ (-(2 : ℝ) * d / 2) * (W : ℝ) ^ (d : ℝ)) * bB d L W p q *
              ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) := by rw [h1, one_mul]
        _ = _ := by ring
    rw [mul_assoc (Kw * (W : ℝ) ^ τ₁), ← hkey]
    cases w
    · exact hs
    · exact hp
    · exact hm
  · have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hW
    have hW1n : 1 ≤ W := by exact_mod_cast hW1
    have hW0 : (0 : ℝ) < W := by linarith
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hWi : Wth ⟨i, hi⟩ ≤ (W : ℝ) := by
      refine le_trans ?_ ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Wth j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ _))
    have h1 := hWth ⟨i, hi⟩ o ho W L hadm hWi z hz p q
    have hdata : (gData (Smat P.ψ W L) z Sig G).chain o =
        (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)).chain o := rfl
    rw [hdata]
    refine h1.trans ?_
    rw [sq_half_eq hW1n]
    have hexp : (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) =
        (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) * (W : ℝ) ^ (d : ℝ) := by
      rw [← Real.rpow_add hW0]; ring_nf
    rw [hexp]
    have hB0 : 0 ≤ bB d L W p q := (bB_pos₁ hW1n p q).le
    have : (W : ℝ) ^ τ₁ ≤ Kw * (W : ℝ) ^ τ₁ := le_mul_of_one_le_left (by positivity) hKw
    calc (W : ℝ) ^ τ₁ * ((W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) * (W : ℝ) ^ (d : ℝ)) *
          bB d L W p q
        = (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
            ((W : ℝ) ^ (d : ℝ) * bB d L W p q) := by ring
      _ ≤ Kw * (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
            ((W : ℝ) ^ (d : ℝ) * bB d L W p q) := by gcongr

/-! ## The deterministic bound on the absolute-value graph -/

/-- The sum over the internal labels of the products over the black and blue edges is
nonnegative. -/
private theorem treeSum_nonneg {d L W : ℕ} [NeZero L] {k n : ℕ} (Γ : Graph k n)
    (bl bu : List (Fin Γ.comps.length)) (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ)
    (e : Fin k → Zd d L) :
    (0 : ℝ) ≤ ∑ s : Fin n → Zd d L,
      ((bl.map fun i => bB d L W (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y)).prod *
        (bu.map fun i => |A (blueIdx Γ.comps[i]) (Sum.elim e s Γ.comps[i].x)
          (Sum.elim e s Γ.comps[i].y)|).prod) := by
  refine Finset.sum_nonneg fun s _ => mul_nonneg (List.prod_nonneg fun a ha => ?_)
    (List.prod_nonneg fun a ha => ?_)
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
    unfold bB; positivity
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
    exact abs_nonneg _

/-- The deterministic bound on the absolute-value graph of [I, Lemma 6.10] before the summation of
[I, Claim 6.11]: for every `τ₁ > 0` there are `M ≥ 0` and `W₀ ≥ 1` such that along `adm(c₀, c₁)`,
for `W ≥ W₀`, `z ∈ 𝐃(κ, ε)`, `1 ≤ Λ ≤ W^{d/2}` and `|G_{xy} - δ_{xy} m| ≤ W^{-d/2} Λ`, the
absolute-value graph is at most `M W^{τ₁ |Γ|} Λ^{Σ g} W^{-Σ q d/2} (W^d)^{|bl|} (W^{d/2})^{|bu|}`
times the sum over the internal labels of the product of `B` over the black edges and of `|A_j|`
over the blue edges, with the blue matrices `A_0 = B^{1/2}/C₀`, `A_1 = |G - m|/Λ`. -/
private theorem dc_main (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (Sig : ℕ → Expansion 2)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) {k n : ℕ} (Γ : Graph k n) (hT : Γ.TKinds N)
    (hdot : ∀ c ∈ Γ.comps, c.kind ≠ .dot)
    (hxd : ∀ c ∈ Γ.comps, c.kind.isSolid = true → ∃ c' ∈ Γ.comps, c'.kind = .xdot ∧
      ((c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)))
    (bl bu : List (Fin Γ.comps.length)) (hbl : bl.Nodup) (hbu' : bu.Nodup)
    (hbk : ∀ i ∈ bl, (∃ o, Γ.comps[i].kind = .theta o) ∨ ∃ w, Γ.comps[i].kind = .waved w)
    (hbu : ∀ i ∈ bu, (∃ o, Γ.comps[i].kind = .theta o) ∨ (∃ ch, Γ.comps[i].kind = .G ch) ∨
      ∃ w, Γ.comps[i].kind = .waved w)
    (hboth : ∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (τ₁ : ℝ) (hτ₁ : 0 < τ₁) :
    ∃ M W₀ : ℝ, 0 ≤ M ∧ 1 ≤ W₀ ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) (Λ : ℝ), 1 ≤ Λ →
        Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) →
        (∀ p q, errAbs G z p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ) → ∀ e : Fin k → Zd d L,
          Γ.absVal (gData (Smat P.ψ W L) z Sig G) e ≤
            M * (W : ℝ) ^ (τ₁ * Γ.comps.length) *
              Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
              (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
              (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length) *
              ∑ s : Fin n → Zd d L,
                ((bl.map fun i => bB d L W (Sum.elim e s Γ.comps[i].x)
                    (Sum.elim e s Γ.comps[i].y)).prod *
                  (bu.map fun i => |blueMat d L W C₀ Λ (errAbs G z) (blueIdx Γ.comps[i])
                    (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y)|).prod) := by
  obtain ⟨K, W₀, hK, hW₀, hin⟩ := gData_inputs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig Γ hT
    τ₁ hτ₁
  obtain ⟨Cc, hCc0, hCc⟩ := coeff_bound κ hκ Γ.coeff
  refine ⟨Cc * (2 * C₀ * K) ^ Γ.comps.length, W₀, by positivity, hW₀,
    fun W L _ hadm hW z hz G Λ hΛ hΛW hE e => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := hW₀.trans hW
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hW1n hz
  obtain ⟨hwav, hth⟩ := hin W L hadm hW z hz G
  set D := gData (Smat P.ψ W L) z Sig G with hD
  have hm : ‖D.m‖ ≤ 1 := (norm_msc_lt_one him).le
  have hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = errAbs G z p q :=
    fun p q => rfl
  have hΛW' : (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ ≤ 1 := by
    calc (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ
        ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * (W : ℝ) ^ ((d : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hΛW (by positivity)
      _ = 1 := by
          rw [← Real.rpow_add hW0, show -(1 : ℝ) * d / 2 + d / 2 = 0 by ring, Real.rpow_zero]
  have hK₁ : 1 ≤ K * (W : ℝ) ^ τ₁ := by
    have := Real.one_le_rpow hW1 hτ₁.le; nlinarith
  have h := absVal_le (by omega) hW1n D N (errAbs G z) (K * (W : ℝ) ^ τ₁) C₀ Λ hK₁ hC₀ hΛ hm hEeq
    hE hΛW' hwav Γ hth hT hdot hxd bl bu hbl hbu' hbk hbu hboth e
  have hcoeff : ‖Γ.coeff.eval D.m‖ ≤ Cc := hCc z him hz.1 hz.2.2
  have hS0 := treeSum_nonneg (W := W) Γ bl bu (blueMat d L W C₀ Λ (errAbs G z)) e
  have hrest : 0 ≤ (2 * C₀ * (K * (W : ℝ) ^ τ₁)) ^ Γ.comps.length *
      Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
      (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length) := by
    have : (0 : ℝ) ≤ Λ := by linarith
    have : (0 : ℝ) ≤ C₀ := by linarith
    have : (0 : ℝ) ≤ K := by linarith
    positivity
  have hpow : (2 * C₀ * (K * (W : ℝ) ^ τ₁)) ^ Γ.comps.length =
      (2 * C₀ * K) ^ Γ.comps.length * (W : ℝ) ^ (τ₁ * Γ.comps.length) := by
    rw [show 2 * C₀ * (K * (W : ℝ) ^ τ₁) = (2 * C₀ * K) * (W : ℝ) ^ τ₁ by ring, mul_pow,
      ← Real.rpow_natCast ((W : ℝ) ^ τ₁), ← Real.rpow_mul hW0.le]
  refine h.trans ?_
  calc ‖Γ.coeff.eval D.m‖ * ((2 * C₀ * (K * (W : ℝ) ^ τ₁)) ^ Γ.comps.length *
          Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
          (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length)) * _
      ≤ Cc * ((2 * C₀ * (K * (W : ℝ) ^ τ₁)) ^ Γ.comps.length *
          Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
          (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length)) * _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hrest) hS0
    _ = _ := by rw [hpow]; ring

/-! ## Bookkeeping for the statements -/

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

/-- A spanning tree of the atoms of a graph with `k` external and `n` internal atoms has
`k + n - 1` edges. -/
private theorem tree_length {k n : ℕ} {ι : Type*} (l : List ι) (f : ι → Atom k n × Atom k n)
    (h : TreeEdges (l.map f)) : l.length + 1 = k + n := by
  have := h.1
  rw [List.length_map] at this
  simpa [Fintype.card_sum] using this

/-- `W^a W^b (W^d)^T (W^{d/2})^T = W^{a + b + dT + (d/2)T}`. -/
private theorem rpow_combine (W : ℝ) (hW : 0 < W) (a b d : ℝ) (T : ℕ) :
    W ^ a * W ^ b * ((W ^ d) ^ T * (W ^ (d / 2)) ^ T) = W ^ (a + b + d * T + d / 2 * T) := by
  rw [← Real.rpow_natCast (W ^ d), ← Real.rpow_mul hW.le, ← Real.rpow_natCast (W ^ (d / 2)),
    ← Real.rpow_mul hW.le, ← Real.rpow_add hW, ← Real.rpow_add hW, ← Real.rpow_add hW]
  ring_nf

/-- The entrywise bound `|G_{xy} - δ_{xy} m| ≤ W^{-d/2} ‖G - m‖_{w;(1,2)}` ([I, (6.11)]). -/
private theorem errAbs_le_weak {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (z : ℂ) (Λ : ℝ) (h : weakNorm d L W 1 2 (errAbs G z) ≤ Λ) (p q : Zd d L) :
    errAbs G z p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ := by
  have h1 := (normBasic d L W hW 1 2 (errAbs G z)).1 p q
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hnn : 0 ≤ errAbs G z p q := norm_nonneg _
  rw [abs_of_nonneg hnn] at h1
  rw [show -(1 : ℝ) * d / 2 = -(1 * d / 2) by ring]
  exact h1.trans (mul_le_mul_of_nonneg_left h (by positivity))

/-- The blue matrices have weak-`(1,2)` norm at most `1` when `‖G - m‖_{w;(1,2)} ≤ Λ`. -/
private theorem blueMat_weak {d L W : ℕ} [NeZero L] (C₀ Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hC₀ : weakNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y) / C₀) ≤ 1)
    (E : Matrix (Zd d L) (Zd d L) ℝ) (hE : weakNorm d L W 1 2 E ≤ Λ) (j : ℕ) :
    weakNorm d L W 1 2 (blueMat d L W C₀ Λ E j) ≤ 1 := by
  by_cases hj : j = 0
  · subst hj
    have h0 : blueMat d L W C₀ Λ E 0 = fun x y => Real.sqrt (bB d L W x y) / C₀ := by
      funext x y; simp [blueMat]
    rw [h0]; exact hC₀
  · have hΛ0 : 0 < Λ := by linarith
    have h1 : weakNorm d L W 1 2 (blueMat d L W C₀ Λ E j) ≤ Λ⁻¹ * weakNorm d L W 1 2 E := by
      refine weakNorm_le_mul 1 2 _ (by positivity) _ _ fun x y => ?_
      simp only [blueMat, hj, ↓reduceIte, abs_div, abs_of_pos hΛ0]
      rw [div_eq_inv_mul]
    calc _ ≤ Λ⁻¹ * weakNorm d L W 1 2 E := h1
      _ ≤ Λ⁻¹ * Λ := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 1 := inv_mul_cancel₀ hΛ0.ne'

/-- The blue matrices have strong-`(1,1)` norm at most `1` when `‖G - m‖_{s;(1,1)} ≤ Λ`. -/
private theorem blueMat_strong {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (C₀ Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hC₀ : strongNorm d L W 1 1 (fun x y => Real.sqrt (bB d L W x y) / C₀) ≤ 1)
    (E : Matrix (Zd d L) (Zd d L) ℝ) (hE : strongNorm d L W 1 1 E ≤ Λ) (j : ℕ) :
    strongNorm d L W 1 1 (blueMat d L W C₀ Λ E j) ≤ 1 := by
  by_cases hj : j = 0
  · subst hj
    have h0 : blueMat d L W C₀ Λ E 0 = fun x y => Real.sqrt (bB d L W x y) / C₀ := by
      funext x y; simp [blueMat]
    rw [h0]; exact hC₀
  · have hΛ0 : 0 < Λ := by linarith
    have h1 : strongNorm d L W 1 1 (blueMat d L W C₀ Λ E j) ≤ Λ⁻¹ * strongNorm d L W 1 1 E := by
      refine strongNorm_le_mul hW 1 1 _ (by positivity) _ _ fun x y => ?_
      simp only [blueMat, hj, ↓reduceIte, abs_div, abs_of_pos hΛ0]
      rw [div_eq_inv_mul]
    calc _ ≤ Λ⁻¹ * strongNorm d L W 1 1 E := h1
      _ ≤ Λ⁻¹ * Λ := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 1 := inv_mul_cancel₀ hΛ0.ne'

/-- The auxiliary graph of [I, Claim 6.11] with the black and blue lists of components of `Γ`. -/
private def auxOf {n : ℕ} (Γ : Graph 2 n) (bl bu : List (Fin Γ.comps.length)) : AuxGraph n :=
  ⟨bl.map fun i => (Γ.comps[i].x, Γ.comps[i].y),
    bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y, blueIdx Γ.comps[i])⟩

/-- The value of `auxOf` at `(x, y)` is the sum over the internal labels of the product of `B`
over the black list and of `|A_j|` over the blue list. -/
private theorem auxOf_val {d L W n : ℕ} [NeZero L] (Γ : Graph 2 n)
    (bl bu : List (Fin Γ.comps.length))
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (x y : Zd d L) :
    (auxOf Γ bl bu).val d L W A x y = ∑ s : Fin n → Zd d L,
      ((bl.map fun i => bB d L W (Sum.elim ![x, y] s Γ.comps[i].x)
          (Sum.elim ![x, y] s Γ.comps[i].y)).prod *
        (bu.map fun i => |A (blueIdx Γ.comps[i]) (Sum.elim ![x, y] s Γ.comps[i].x)
          (Sum.elim ![x, y] s Γ.comps[i].y)|).prod) := by
  simp [AuxGraph.val, auxOf, List.map_map, Function.comp_def]

/-- The blue edges of `auxOf` form the tree of the blue list. -/
private theorem auxOf_blue {n : ℕ} (Γ : Graph 2 n) (bl bu : List (Fin Γ.comps.length)) :
    ((auxOf Γ bl bu).blue.map fun e => (e.1, e.2.1)) =
      bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y) := by
  simp [auxOf, List.map_map, Function.comp_def]

/-- If the absolute-value graph is at most `c Λ^g W^{-Σ q d/2} (W^d)^{n+1} (W^{d/2})^{n+1}` times
the value of `auxOf`, then `W^{(n_{xy}-3)d/2} |𝒢^{abs}_{xy}| / B_{xy}` is at most `c Λ^g` times
the normalized value `W^{nd/2} Γ̃_{xy} / B_{xy}` of `auxOf`. -/
private theorem normGraph2_le {d L W n : ℕ} [NeZero L] (hW : 1 ≤ W) (Γ : Graph 2 n)
    (bl bu : List (Fin Γ.comps.length)) (hbl : bl.length = n + 1) (hbu : bu.length = n + 1)
    (D : Data (Zd d L)) (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (c : ℝ) (Λ : ℝ) (g : ℕ)
    (h : ∀ x y : Zd d L, Γ.absVal D ![x, y] ≤ c * Λ ^ g *
      (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length) *
      (auxOf Γ bl bu).val d L W A x y) (x y : Zd d L) :
    normGraph2 d L W Γ D x y ≤ c * Λ ^ g * (auxOf Γ bl bu).normVal d L W 1 A x y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hB := bB_pos₁ (d := d) (L := L) hW x y
  unfold normGraph2 AuxGraph.normVal
  rw [hbl, hbu] at h
  have hexp : (W : ℝ) ^ (((Γ.ord : ℝ) - 3) * d / 2) *
      ((W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ (n + 1))) =
      (W : ℝ) ^ (1 * (n : ℝ) * d / 2) := by
    rw [← mul_assoc, rpow_combine _ hW0, sum_expo, ord_eq_sum]
    congr 1
    push_cast
    ring
  calc (W : ℝ) ^ (((Γ.ord : ℝ) - 3) * d / 2) * Γ.absVal D ![x, y] / bB d L W x y
      ≤ (W : ℝ) ^ (((Γ.ord : ℝ) - 3) * d / 2) * (c * Λ ^ g *
          (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ (n + 1)) *
          (auxOf Γ bl bu).val d L W A x y) / bB d L W x y := by
        gcongr; exact h x y
    _ = c * Λ ^ g * ((W : ℝ) ^ (((Γ.ord : ℝ) - 3) * d / 2) *
          ((W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
            (((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ (n + 1)))) *
          (auxOf Γ bl bu).val d L W A x y / bB d L W x y := by ring
    _ = _ := by rw [hexp]; ring

/-- The constant `M` is at most `W^{τ/4}` for `W ≥ max(1, M)^{4/τ}`. -/
private theorem const_le_rpow (M τ Wr : ℝ) (hτ : 0 < τ) (hW : (max 1 M) ^ (4 / τ) ≤ Wr) :
    M ≤ Wr ^ (τ / 4) := by
  have h1 : (1 : ℝ) ≤ max 1 M := le_max_left _ _
  calc M ≤ max 1 M := le_max_right _ _
    _ = ((max 1 M) ^ (4 / τ)) ^ (τ / 4) := by
        rw [← Real.rpow_mul (by linarith), show 4 / τ * (τ / 4) = 1 by field_simp, Real.rpow_one]
    _ ≤ Wr ^ (τ / 4) := Real.rpow_le_rpow (by positivity) hW (by positivity)

/-- `M W^{τ₁ ℓ} Λ^{g} W^{τ/4} ≤ W^τ Λ^{p}` for `M ≤ W^{τ/4}`, `τ₁ ℓ ≤ τ/4`, `g ≤ p`, `Λ ≥ 1`. -/
private theorem final_le (M Wr Λ τ τ₁ ℓ p : ℝ) (g : ℕ) (hW : 1 ≤ Wr) (hτ : 0 < τ) (hM0 : 0 ≤ M)
    (hM : M ≤ Wr ^ (τ / 4)) (hτ₁ : τ₁ * ℓ ≤ τ / 4) (hΛ : 1 ≤ Λ) (hg : (g : ℝ) ≤ p) (X : ℝ)
    (hX : X ≤ Wr ^ (τ / 4)) :
    M * Wr ^ (τ₁ * ℓ) * Λ ^ g * X ≤ Wr ^ τ * Λ ^ p := by
  have hW0 : 0 < Wr := by linarith
  have h1 : Wr ^ (τ₁ * ℓ) ≤ Wr ^ (τ / 4) := Real.rpow_le_rpow_of_exponent_le hW hτ₁
  have h2 : Λ ^ g ≤ Λ ^ p := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hΛ hg
  have h3 : Wr ^ (τ / 4) * Wr ^ (τ / 4) * Wr ^ (τ / 4) ≤ Wr ^ τ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have hX0 : M * Wr ^ (τ₁ * ℓ) * Λ ^ g * X ≤ M * Wr ^ (τ₁ * ℓ) * Λ ^ g * Wr ^ (τ / 4) := by
    by_cases hX0 : 0 ≤ X
    · exact mul_le_mul_of_nonneg_left hX (by positivity)
    · push Not at hX0
      have : M * Wr ^ (τ₁ * ℓ) * Λ ^ g * X ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hX0.le
      exact this.trans (by positivity)
  refine hX0.trans ?_
  calc M * Wr ^ (τ₁ * ℓ) * Λ ^ g * Wr ^ (τ / 4)
      ≤ Wr ^ (τ / 4) * Wr ^ (τ / 4) * Λ ^ p * Wr ^ (τ / 4) := by
        gcongr
    _ = Wr ^ (τ / 4) * Wr ^ (τ / 4) * Wr ^ (τ / 4) * Λ ^ p := by ring
    _ ≤ Wr ^ τ * Λ ^ p := by gcongr

/-- [I, Lemma 6.10, (6.19)] = [II, Lemma 8.4, (8.14)], deterministic form. For `d ≥ 8`, a
profile `P`, the parameters `c₀, c₁, κ, ε`, self-energies `Sig` of orders `4, …, N`, and a graph
`Γ` with two external atoms `x, y` whose internal form is normal regular and doubly connected
([I, Def 6.5] = [II, Def 2.12]), with the kinds of [II, Def 3.2 (2)]: for every `τ > 0` there is
`W₀` such that for `W ≥ W₀` along `adm(c₀, c₁)`, `z ∈ 𝐃(κ, ε)`, every matrix `G` and every
`1 ≤ Λ ≤ W^{d/2}` with `‖G - m‖_{w;(1,2)} ≤ Λ`:
`‖W^{(n_{xy}-3)d/2} |𝒢^{abs}_{xy}| / B_{xy}‖_{w;(1,2)} ≤ W^τ Λ^{n_{xy} - 2}`, i.e.
`|𝒢^{abs}_{xy}| ≤ W^{-(n_{xy}-3)d/2} B_{xy} 𝒜_{xy}` with `‖𝒜‖_{w;(1,2)} ≤ W^τ Λ^{n_{xy}-2}`. -/
theorem dcWeak :
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (n C : ℕ) (Γ : Graph 2 n), Γ.internalize.Normal C → Γ.internalize.DoublyConnected →
      Γ.TKinds N → ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ →
        W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) (Λ : ℝ), 1 ≤ Λ →
          Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) → weakNorm d L W 1 2 (errAbs G z) ≤ Λ →
            weakNorm d L W 1 2 (normGraph2 d L W Γ (gData (Smat P.ψ W L) z Sig G)) ≤
              (W : ℝ) ^ τ * Λ ^ ((Γ.ord : ℝ) - 2) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n C Γ hNo hDC hT τ hτ
  obtain ⟨bl, bu, hbl, hbu', hbk, hbu, hboth, hTb, hTu⟩ := dc_trees (by norm_num) Γ C N hNo hDC hT
  have hlb : bl.length = n + 1 := by have := tree_length bl _ hTb; omega
  have hlu : bu.length = n + 1 := by have := tree_length bu _ hTu; omega
  obtain ⟨C₀, hC₀, hC₀n⟩ := sqrtB_norms d hd
  have hdot := no_dot Γ hNo.1
  have hxd := xdot_of_normal Γ hNo
  set τ₁ : ℝ := τ / (4 * ((Γ.comps.length : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁ℓ : τ₁ * Γ.comps.length ≤ τ / 4 := by
    rw [hτ₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨M, W₁, hM, hW₁, hmain⟩ := dc_main d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig Γ hT
    hdot hxd bl bu hbl hbu' hbk hbu hboth C₀ hC₀ τ₁ hτ₁0
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨W₂, hW₂⟩ := auxTreeWeak d 1 2 (by omega) one_pos two_pos (by linarith) c₀ c₁ hc₀ hc₁ n
    (auxOf Γ bl bu) hTb (by rw [auxOf_blue]; exact hTu) (τ / 4) (by positivity)
  refine ⟨max (max W₁ W₂) ((max 1 M) ^ (4 / τ)), fun W L _ hadm hW z hz G Λ hΛ hΛW hEw => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := hW₁.trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hE := errAbs_le_weak hW1n G z Λ hEw
  set A := blueMat d L W C₀ Λ (errAbs G z) with hA
  have hAn : ∀ j, weakNorm d L W 1 2 (A j) ≤ 1 :=
    blueMat_weak C₀ Λ hΛ (hC₀n L W hW1n).1 _ hEw
  have haux := hW₂ W L hadm ((le_max_right _ _).trans ((le_max_left _ _).trans hW)) A hAn
  have hpt : ∀ x y, normGraph2 d L W Γ (gData (Smat P.ψ W L) z Sig G) x y ≤
      (M * (W : ℝ) ^ (τ₁ * Γ.comps.length)) * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
        (auxOf Γ bl bu).normVal d L W 1 A x y := by
    refine normGraph2_le hW1n Γ bl bu hlb hlu _ A _ Λ _ (fun x y => ?_)
    rw [auxOf_val]
    exact hmain W L hadm ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) z hz G Λ hΛ hΛW
      hE ![x, y]
  have hng0 : ∀ x y, 0 ≤ normGraph2 d L W Γ (gData (Smat P.ψ W L) z Sig G) x y := by
    intro x y
    unfold normGraph2 Graph.absVal
    have := bB_pos₁ (d := d) (L := L) hW1n x y
    have : (0 : ℝ) ≤ ∑ s : Fin n → Zd d L, ‖Γ.coeff.eval (gData (Smat P.ψ W L) z Sig G).m‖ *
        (Γ.comps.map fun c =>
          ‖Comp.val (gData (Smat P.ψ W L) z Sig G) (Sum.elim ![x, y] s) c‖).prod :=
      Finset.sum_nonneg fun s _ => mul_nonneg (norm_nonneg _) (List.prod_nonneg fun a ha => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha; exact norm_nonneg _)
    positivity
  have hcst : 0 ≤ (M * (W : ℝ) ^ (τ₁ * Γ.comps.length)) *
      Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) := by
    have : (0 : ℝ) ≤ Λ := by linarith
    positivity
  have hmono := weakNorm_le_mul (W := W) 1 2 _ hcst _ ((auxOf Γ bl bu).normVal d L W 1 A)
    (fun x y => by
      rw [abs_of_nonneg (hng0 x y)]
      exact (hpt x y).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hcst))
  have hcount := count_le Γ hT bl hbl hbk
  have hg : ((∑ i : Fin Γ.comps.length, lamW Γ.comps[i] : ℕ) : ℝ) ≤ (Γ.ord : ℝ) - 2 := by
    rw [ord_eq_sum, hlb] at *
    push_cast at hcount ⊢
    linarith
  refine hmono.trans ?_
  rw [mul_assoc (M * (W : ℝ) ^ (τ₁ * Γ.comps.length))]
  have := final_le M W Λ τ τ₁ Γ.comps.length ((Γ.ord : ℝ) - 2) _ hW1 hτ hM
    (const_le_rpow M τ W hτ ((le_max_right _ _).trans hW)) hτ₁ℓ hΛ hg _ haux
  calc M * (W : ℝ) ^ (τ₁ * Γ.comps.length) * (Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
        weakNorm d L W 1 2 ((auxOf Γ bl bu).normVal d L W 1 A))
      = M * (W : ℝ) ^ (τ₁ * Γ.comps.length) * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
        weakNorm d L W 1 2 ((auxOf Γ bl bu).normVal d L W 1 A) := by ring
    _ ≤ _ := this

/-- `B_{xy}^{1/2} = W^{-1} ⟨x - y⟩^{-(d-2)/2}`. -/
private theorem sqrt_bB_eq {d L W : ℕ} (hW : 1 ≤ W) (x y : Zd d L) :
    Real.sqrt (bB d L W x y) = (W : ℝ) ^ (-1 : ℝ) * brk d L W x y ^ ((2 - (d : ℝ)) / 2) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht := brk_pos₁ (d := d) (L := L) hW x y
  have hB : bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) := rfl
  rw [hB, Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hW0.le, ← Real.rpow_mul ht.le]
  congr 2 <;> ring

/-- The entrywise bound `|G_{xy} - δ_{xy} m| ≤ W^{-d/2} ‖G - m‖_{s;(1,1)}` ([I, (6.13)]). -/
private theorem errAbs_le_strong {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (z : ℂ) (Λ : ℝ) (h : strongNorm d L W 1 1 (errAbs G z) ≤ Λ)
    (p q : Zd d L) : errAbs G z p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ := by
  have h1 := (normBasic d L W hW 1 1 (errAbs G z)).2.2 p q
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hnn : 0 ≤ errAbs G z p q := norm_nonneg _
  rw [abs_of_nonneg hnn] at h1
  have ht := brk_pos₁ (d := d) (L := L) hW p q
  have h2 : brk d L W p q ^ (-(1 * (d : ℝ) / 2 - 1)) ≤ (W : ℝ) ^ (-(1 * (d : ℝ) / 2 - 1)) :=
    Real.rpow_le_rpow_of_nonpos hW0 (le_brk₁ p q) (by linarith)
  have h3 : (W : ℝ) ^ (-(1 : ℝ)) * (W : ℝ) ^ (-(1 * (d : ℝ) / 2 - 1)) =
      (W : ℝ) ^ (-(1 : ℝ) * d / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hS0 : 0 ≤ strongNorm d L W 1 1 (errAbs G z) :=
    Real.iSup_nonneg fun x => Real.iSup_nonneg fun y => by
      have := brk_pos₁ (d := d) (L := L) hW x y; positivity
  calc errAbs G z p q ≤ (W : ℝ) ^ (-(1 : ℝ)) * brk d L W p q ^ (-(1 * (d : ℝ) / 2 - 1)) *
        strongNorm d L W 1 1 (errAbs G z) := h1
    _ ≤ (W : ℝ) ^ (-(1 : ℝ)) * (W : ℝ) ^ (-(1 * (d : ℝ) / 2 - 1)) * Λ := by
        gcongr
    _ = _ := by rw [h3]

/-- `|𝒢^{abs}_{xy}| = W^{-(n_{xy}-3)d/2} B_{xy} (W^{(n_{xy}-3)d/2} |𝒢^{abs}_{xy}| / B_{xy})`. -/
private theorem absVal_eq_normGraph2 {d L W n : ℕ} [NeZero L] (hW : 1 ≤ W) (Γ : Graph 2 n)
    (D : Data (Zd d L)) (x y : Zd d L) :
    Γ.absVal D ![x, y] = normGraph2 d L W Γ D x y * bB d L W x y *
      (W : ℝ) ^ (-(((Γ.ord : ℝ) - 3) * d / 2)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hB := bB_pos₁ (d := d) (L := L) hW x y
  unfold normGraph2
  rw [Real.rpow_neg hW0.le]
  have : (W : ℝ) ^ (((Γ.ord : ℝ) - 3) * d / 2) ≠ 0 := by positivity
  field_simp

/-- [I, Lemma 6.10, (6.20)] = [II, Lemma 8.4, (8.15)], deterministic form: under the hypotheses
of `dcWeak` with `‖G - m‖_{s;(1,1)} ≤ Λ` in place of the weak norm,
`|𝒢^{abs}_{xy}| ≤ W^τ Λ^{n_{xy}-2} W^{-(n_{xy}-3)d/2} B_{xy}^{3/2}`. -/
theorem dcStrong :
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (n C : ℕ) (Γ : Graph 2 n), Γ.internalize.Normal C → Γ.internalize.DoublyConnected →
      Γ.TKinds N → ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ →
        W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) (Λ : ℝ), 1 ≤ Λ →
          Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) → strongNorm d L W 1 1 (errAbs G z) ≤ Λ →
            ∀ x y : Zd d L, Γ.absVal (gData (Smat P.ψ W L) z Sig G) ![x, y] ≤
              (W : ℝ) ^ τ * Λ ^ ((Γ.ord : ℝ) - 2) * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 3) * d / 2)) *
                bB d L W x y ^ ((3 : ℝ) / 2) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n C Γ hNo hDC hT τ hτ
  obtain ⟨bl, bu, hbl, hbu', hbk, hbu, hboth, hTb, hTu⟩ := dc_trees (by norm_num) Γ C N hNo hDC hT
  have hlb : bl.length = n + 1 := by have := tree_length bl _ hTb; omega
  have hlu : bu.length = n + 1 := by have := tree_length bu _ hTu; omega
  obtain ⟨C₀, hC₀, hC₀n⟩ := sqrtB_norms d hd
  have hdot := no_dot Γ hNo.1
  have hxd := xdot_of_normal Γ hNo
  set τ₁ : ℝ := τ / (4 * ((Γ.comps.length : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁ℓ : τ₁ * Γ.comps.length ≤ τ / 4 := by
    rw [hτ₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨M, W₁, hM, hW₁, hmain⟩ := dc_main d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig Γ hT
    hdot hxd bl bu hbl hbu' hbk hbu hboth C₀ hC₀ τ₁ hτ₁0
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨W₂, hW₂⟩ := auxTreeStrong d 1 1 (by omega) one_pos one_pos (by linarith) c₀ c₁ hc₀ hc₁
    n (auxOf Γ bl bu) hTb (by rw [auxOf_blue]; exact hTu) (τ / 4) (by positivity)
  refine ⟨max (max W₁ W₂) ((max 1 M) ^ (4 / τ)),
    fun W L _ hadm hW z hz G Λ hΛ hΛW hEs x y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := hW₁.trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hE := errAbs_le_strong (by omega) hW1n G z Λ hEs
  set A := blueMat d L W C₀ Λ (errAbs G z) with hA
  have hAn : ∀ j, strongNorm d L W 1 1 (A j) ≤ 1 :=
    blueMat_strong hW1n C₀ Λ hΛ (hC₀n L W hW1n).2 _ hEs
  have haux := hW₂ W L hadm ((le_max_right _ _).trans ((le_max_left _ _).trans hW)) A hAn
  have hnv : (auxOf Γ bl bu).normVal d L W 1 A x y ≤
      (W : ℝ) ^ (τ / 4) * Real.sqrt (bB d L W x y) := by
    have h1 := (normBasic d L W hW1n 1 1 ((auxOf Γ bl bu).normVal d L W 1 A)).2.2 x y
    rw [sqrt_bB_eq hW1n]
    have h2 : (W : ℝ) ^ (-(1 : ℝ)) * brk d L W x y ^ (-(1 * (d : ℝ) / 2 - 1)) =
        (W : ℝ) ^ (-1 : ℝ) * brk d L W x y ^ ((2 - (d : ℝ)) / 2) := by
      congr 2; ring
    rw [h2] at h1
    have ht := brk_pos₁ (d := d) (L := L) hW1n x y
    calc (auxOf Γ bl bu).normVal d L W 1 A x y ≤ |(auxOf Γ bl bu).normVal d L W 1 A x y| :=
          le_abs_self _
      _ ≤ _ := h1
      _ ≤ (W : ℝ) ^ (-1 : ℝ) * brk d L W x y ^ ((2 - (d : ℝ)) / 2) * (W : ℝ) ^ (τ / 4) := by
          gcongr
      _ = _ := by ring
  have hpt := normGraph2_le hW1n Γ bl bu hlb hlu (gData (Smat P.ψ W L) z Sig G) A
    (M * (W : ℝ) ^ (τ₁ * Γ.comps.length)) Λ _ (fun x y => by
      rw [auxOf_val]
      exact hmain W L hadm ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) z hz G Λ hΛ hΛW
        hE ![x, y]) x y
  have hcount := count_le Γ hT bl hbl hbk
  have hg : ((∑ i : Fin Γ.comps.length, lamW Γ.comps[i] : ℕ) : ℝ) ≤ (Γ.ord : ℝ) - 2 := by
    rw [ord_eq_sum, hlb] at *
    push_cast at hcount ⊢
    linarith
  have hfin := final_le M W Λ τ τ₁ Γ.comps.length ((Γ.ord : ℝ) - 2) _ hW1 hτ hM
    (const_le_rpow M τ W hτ ((le_max_right _ _).trans hW)) hτ₁ℓ hΛ hg _ le_rfl
  have hB := bB_pos₁ (d := d) (L := L) hW1n x y
  have hB32 : bB d L W x y ^ ((3 : ℝ) / 2) = Real.sqrt (bB d L W x y) * bB d L W x y := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hB.ne']; norm_num
  have hcst : 0 ≤ M * (W : ℝ) ^ (τ₁ * Γ.comps.length) *
      Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) := by
    have : (0 : ℝ) ≤ Λ := by linarith
    positivity
  rw [absVal_eq_normGraph2 hW1n, hB32]
  have hWe : 0 ≤ (W : ℝ) ^ (-(((Γ.ord : ℝ) - 3) * d / 2)) := by positivity
  calc normGraph2 d L W Γ (gData (Smat P.ψ W L) z Sig G) x y * bB d L W x y *
        (W : ℝ) ^ (-(((Γ.ord : ℝ) - 3) * d / 2))
      ≤ (M * (W : ℝ) ^ (τ₁ * Γ.comps.length) * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
          ((W : ℝ) ^ (τ / 4) * Real.sqrt (bB d L W x y))) * bB d L W x y *
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 3) * d / 2)) := by
        gcongr
        exact hpt.trans (mul_le_mul_of_nonneg_left hnv hcst)
    _ = (M * (W : ℝ) ^ (τ₁ * Γ.comps.length) * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
          (W : ℝ) ^ (τ / 4)) * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 3) * d / 2)) *
          (Real.sqrt (bB d L W x y) * bB d L W x y) := by ring
    _ ≤ (W : ℝ) ^ τ * Λ ^ ((Γ.ord : ℝ) - 2) * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 3) * d / 2)) *
          (Real.sqrt (bB d L W x y) * bB d L W x y) := by
        gcongr

/-! ## One fixed atom -/

/-- The atoms of a graph with one external atom as atoms of a graph with two external atoms. -/
private def emb12 (n : ℕ) : Atom 1 n → Atom 2 n := Sum.map (fun _ => 0) id

private theorem emb12_injective (n : ℕ) : Function.Injective (emb12 n) := by
  intro u v h
  rcases u with a | a <;> rcases v with b | b
  · rw [Subsingleton.elim a b]
  · simp [emb12] at h
  · simp [emb12] at h
  · simpa [emb12] using h

/-- `σ ∘ emb12 = σ'` for the labellings `σ = (x, x, s)` and `σ' = (x, s)`. -/
private theorem elim_emb12 {ι : Type*} {n : ℕ} (x : ι) (s : Fin n → ι) (u : Atom 1 n) :
    Sum.elim ![x, x] s (emb12 n u) = Sum.elim ![x] s u := by
  rcases u with a | a
  · simp [emb12]
  · simp [emb12]

/-- A spanning tree of the atoms of a graph with one external atom, with the second external atom
attached to the first by one edge, is a spanning tree of the atoms with two external atoms. -/
private theorem tree_augment {n : ℕ} (es : List (Atom 1 n × Atom 1 n)) (h : TreeEdges es) :
    TreeEdges ((Sum.inl 0, Sum.inl 1) :: es.map fun e => (emb12 n e.1, emb12 n e.2)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin] at h1 ⊢
    simp only [List.length_cons, List.length_map]
    omega
  · set G' := SimpleGraph.fromRel fun u v =>
      (u, v) ∈ (Sum.inl 0, Sum.inl 1) :: es.map fun e => (emb12 n e.1, emb12 n e.2) with hG'
    have hlift : ∀ a b, (SimpleGraph.fromRel fun u v => (u, v) ∈ es).Adj a b →
        G'.Reachable (emb12 n a) (emb12 n b) := by
      intro a b hab
      rw [SimpleGraph.fromRel_adj] at hab
      refine SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
        ⟨fun h => hab.1 (emb12_injective n h), ?_⟩)
      rcases hab.2 with h | h
      · exact Or.inl (List.mem_cons_of_mem _ (List.mem_map.2 ⟨(a, b), h, rfl⟩))
      · exact Or.inr (List.mem_cons_of_mem _ (List.mem_map.2 ⟨(b, a), h, rfl⟩))
    have hr : ∀ u, G'.Reachable (Sum.inl 0) u := by
      intro u
      rcases u with i | j
      · fin_cases i
        · rfl
        · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
            ⟨by simp, Or.inl (List.mem_cons_self ..)⟩)
      · exact reach_lift (emb12 n) hlift (h2 (Sum.inl 0) (Sum.inr j))
    exact fun u v => (hr u).symm.trans (hr v)

/-- The auxiliary graph of the second external atom attached to the trees of a graph with one
external atom by a black and a blue edge. -/
private def auxOf1 {n : ℕ} (Γ : Graph 1 n) (bl bu : List (Fin Γ.comps.length)) : AuxGraph n :=
  ⟨(Sum.inl 0, Sum.inl 1) :: bl.map fun i => (emb12 n Γ.comps[i].x, emb12 n Γ.comps[i].y),
    (Sum.inl 0, Sum.inl 1, 0) ::
      bu.map fun i => (emb12 n Γ.comps[i].x, emb12 n Γ.comps[i].y, blueIdx Γ.comps[i])⟩

/-- The value of `auxOf1` at `x = y` is `B_{xx} |A_0(x, x)|` times the sum over the internal
labels of the product of `B` over the black list and of `|A_j|` over the blue list. -/
private theorem auxOf1_val {d L W n : ℕ} [NeZero L] (Γ : Graph 1 n)
    (bl bu : List (Fin Γ.comps.length)) (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (x : Zd d L) :
    (auxOf1 Γ bl bu).val d L W A x x = bB d L W x x * |A 0 x x| * ∑ s : Fin n → Zd d L,
      ((bl.map fun i => bB d L W (Sum.elim ![x] s Γ.comps[i].x)
          (Sum.elim ![x] s Γ.comps[i].y)).prod *
        (bu.map fun i => |A (blueIdx Γ.comps[i]) (Sum.elim ![x] s Γ.comps[i].x)
          (Sum.elim ![x] s Γ.comps[i].y)|).prod) := by
  simp only [AuxGraph.val, auxOf1, List.map_cons, List.prod_cons, List.map_map,
    Function.comp_def, elim_emb12, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The black and blue edges of `auxOf1` are spanning trees. -/
private theorem auxOf1_trees {n : ℕ} (Γ : Graph 1 n) (bl bu : List (Fin Γ.comps.length))
    (hb : TreeEdges (bl.map fun i => (Γ.comps[i].x, Γ.comps[i].y)))
    (hu : TreeEdges (bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y))) :
    TreeEdges (auxOf1 Γ bl bu).black ∧
      TreeEdges ((auxOf1 Γ bl bu).blue.map fun e => (e.1, e.2.1)) := by
  have h1 := tree_augment _ hb
  have h2 := tree_augment _ hu
  simp only [List.map_map, Function.comp_def] at h1 h2
  refine ⟨h1, ?_⟩
  simpa [auxOf1, List.map_map, Function.comp_def] using h2

/-- [I, Lemma 6.10, (6.21)] = [II, Lemma 8.4, (8.16)], deterministic form with one fixed atom:
for a graph `Γ` with one external atom `x` whose internal form is normal regular and doubly
connected, `|𝒢^{abs}_x| ≤ W^τ Λ^{ord(𝒢_x)} W^{-ord(𝒢_x) d/2}` when `‖G - m‖_{w;(1,2)} ≤ Λ`. -/
theorem dcSingle :
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (n C : ℕ) (Γ : Graph 1 n), Γ.internalize.Normal C → Γ.internalize.DoublyConnected →
      Γ.TKinds N → ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ →
        W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) (Λ : ℝ), 1 ≤ Λ →
          Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) → weakNorm d L W 1 2 (errAbs G z) ≤ Λ →
            ∀ x : Zd d L, Γ.absVal (gData (Smat P.ψ W L) z Sig G) ![x] ≤
              (W : ℝ) ^ τ * Λ ^ (Γ.ord : ℝ) * (W : ℝ) ^ (-((Γ.ord : ℝ) * d / 2)) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n C Γ hNo hDC hT τ hτ
  obtain ⟨bl, bu, hbl, hbu', hbk, hbu, hboth, hTb, hTu⟩ := dc_trees (by norm_num) Γ C N hNo hDC hT
  have hlb : bl.length = n := by have := tree_length bl _ hTb; omega
  have hlu : bu.length = n := by have := tree_length bu _ hTu; omega
  obtain ⟨C₀, hC₀, hC₀n⟩ := sqrtB_norms d hd
  have hdot := no_dot Γ hNo.1
  have hxd := xdot_of_normal Γ hNo
  set τ₁ : ℝ := τ / (4 * ((Γ.comps.length : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁ℓ : τ₁ * Γ.comps.length ≤ τ / 4 := by
    rw [hτ₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨M, W₁, hM, hW₁, hmain⟩ := dc_main d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig Γ hT
    hdot hxd bl bu hbl hbu' hbk hbu hboth C₀ hC₀ τ₁ hτ₁0
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hTa, hUa⟩ := auxOf1_trees Γ bl bu hTb hTu
  obtain ⟨W₂, hW₂⟩ := auxTreeWeak d 1 2 (by omega) one_pos two_pos (by linarith) c₀ c₁ hc₀ hc₁ n
    (auxOf1 Γ bl bu) hTa hUa (τ / 4) (by positivity)
  refine ⟨max (max W₁ W₂) ((max 1 (M * C₀)) ^ (4 / τ)),
    fun W L _ hadm hW z hz G Λ hΛ hΛW hEw x => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := hW₁.trans ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hE := errAbs_le_weak hW1n G z Λ hEw
  set A := blueMat d L W C₀ Λ (errAbs G z) with hA
  have hAn : ∀ j, weakNorm d L W 1 2 (A j) ≤ 1 :=
    blueMat_weak C₀ Λ hΛ (hC₀n L W hW1n).1 _ hEw
  have haux := hW₂ W L hadm ((le_max_right _ _).trans ((le_max_left _ _).trans hW)) A hAn
  -- the sum over the internal labels
  set F := ∑ s : Fin n → Zd d L,
      ((bl.map fun i => bB d L W (Sum.elim ![x] s Γ.comps[i].x)
          (Sum.elim ![x] s Γ.comps[i].y)).prod *
        (bu.map fun i => |A (blueIdx Γ.comps[i]) (Sum.elim ![x] s Γ.comps[i].x)
          (Sum.elim ![x] s Γ.comps[i].y)|).prod) with hF
  have hbrk : brk d L W x x = W := by
    unfold brk; simp [(zdistInf_eq_zero_iff d L).2 rfl]
  have hsq : Real.sqrt (bB d L W x x) = (W : ℝ) ^ (-((d : ℝ) / 2)) := by
    rw [sqrt_bB_eq hW1n, hbrk, ← Real.rpow_add hW0]; ring_nf
  have hBxx := bB_pos₁ (d := d) (L := L) hW1n x x
  have hA0 : |A 0 x x| = (W : ℝ) ^ (-((d : ℝ) / 2)) / C₀ := by
    have hC0 : 0 < C₀ := by linarith
    simp only [hA, blueMat, ↓reduceIte, hsq]
    rw [abs_of_nonneg (by positivity)]
  have hnv := (normBasic d L W hW1n 1 2 ((auxOf1 Γ bl bu).normVal d L W 1 A)).1 x x
  have hnv' : (auxOf1 Γ bl bu).normVal d L W 1 A x x ≤
      (W : ℝ) ^ (-((d : ℝ) / 2)) * (W : ℝ) ^ (τ / 4) := by
    calc _ ≤ |(auxOf1 Γ bl bu).normVal d L W 1 A x x| := le_abs_self _
      _ ≤ _ := hnv
      _ ≤ (W : ℝ) ^ (-(1 * (d : ℝ) / 2)) * (W : ℝ) ^ (τ / 4) := by gcongr
      _ = _ := by ring_nf
  have hnvF : (auxOf1 Γ bl bu).normVal d L W 1 A x x =
      (W : ℝ) ^ (1 * (n : ℝ) * d / 2) * ((W : ℝ) ^ (-((d : ℝ) / 2)) / C₀) * F := by
    unfold AuxGraph.normVal
    rw [auxOf1_val, hA0, ← hF]
    field_simp
  have hFb : F ≤ C₀ * (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (-(1 * (n : ℝ) * d / 2)) := by
    have hC0 : 0 < C₀ := by linarith
    have hpos : 0 < (W : ℝ) ^ (1 * (n : ℝ) * d / 2) * ((W : ℝ) ^ (-((d : ℝ) / 2)) / C₀) := by
      positivity
    rw [hnvF] at hnv'
    have h1 : F ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) * (W : ℝ) ^ (τ / 4) /
        ((W : ℝ) ^ (1 * (n : ℝ) * d / 2) * ((W : ℝ) ^ (-((d : ℝ) / 2)) / C₀)) := by
      rw [le_div_iff₀ hpos]; linarith
    refine h1.trans (le_of_eq ?_)
    rw [Real.rpow_neg hW0.le (1 * (n : ℝ) * d / 2)]
    field_simp
  have hmain' := hmain W L hadm ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) z hz G Λ
    hΛ hΛW hE ![x]
  rw [hlb, hlu, ← hF] at hmain'
  have hcount := count_le Γ hT bl hbl hbk
  have hg : ((∑ i : Fin Γ.comps.length, lamW Γ.comps[i] : ℕ) : ℝ) ≤ (Γ.ord : ℝ) := by
    rw [ord_eq_sum, hlb] at *
    push_cast at hcount ⊢
    linarith
  have hfin := final_le (M * C₀) W Λ τ τ₁ Γ.comps.length (Γ.ord : ℝ) _ hW1 hτ
    (mul_nonneg hM (by linarith)) (const_le_rpow (M * C₀) τ W hτ ((le_max_right _ _).trans hW))
    hτ₁ℓ hΛ hg _ le_rfl
  have hexp : (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ n * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ n) *
      (W : ℝ) ^ (-(1 * (n : ℝ) * d / 2)) = (W : ℝ) ^ (-((Γ.ord : ℝ) * d / 2)) := by
    rw [mul_comm, ← mul_assoc, rpow_combine _ hW0, sum_expo, ord_eq_sum]
    congr 1
    ring
  have hcst : 0 ≤ M * (W : ℝ) ^ (τ₁ * Γ.comps.length) *
      Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
      (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ n * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ n) := by
    have : (0 : ℝ) ≤ Λ := by linarith
    positivity
  calc Γ.absVal (gData (Smat P.ψ W L) z Sig G) ![x]
      ≤ M * (W : ℝ) ^ (τ₁ * Γ.comps.length) * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
          (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ n * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ n) * F := hmain'
    _ ≤ M * (W : ℝ) ^ (τ₁ * Γ.comps.length) * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
          (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ n * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ n) *
          (C₀ * (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (-(1 * (n : ℝ) * d / 2))) :=
        mul_le_mul_of_nonneg_left hFb hcst
    _ = (M * C₀) * (W : ℝ) ^ (τ₁ * Γ.comps.length) *
          Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) * (W : ℝ) ^ (τ / 4) *
          ((W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(Γ.comps[i].kind.ord : ℝ) * d / 2)) *
            (((W : ℝ) ^ (d : ℝ)) ^ n * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ n) *
            (W : ℝ) ^ (-(1 * (n : ℝ) * d / 2))) := by ring
    _ = (M * C₀) * (W : ℝ) ^ (τ₁ * Γ.comps.length) *
          Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) * (W : ℝ) ^ (τ / 4) *
          (W : ℝ) ^ (-((Γ.ord : ℝ) * d / 2)) := by rw [hexp]
    _ ≤ (W : ℝ) ^ τ * Λ ^ (Γ.ord : ℝ) * (W : ℝ) ^ (-((Γ.ord : ℝ) * d / 2)) := by
        gcongr

/-! ## Stochastic domination -/

/-- [I, (6.40)], the form of [I, Lemma 6.10] used in [II, (8.21), (8.33)], as stochastic
domination along `W → ∞` inside `adm(c₀, c₁)` at scale `W`: for random matrices `G(u)` and
spectral parameters `z(u) ∈ 𝐃(κ, ε)` indexed by `u`, and `0 ≤ ε₀ < d/2`,
`‖G - m‖_{w;(1,2)} ≺ W^{ε₀}` uniformly in `u` implies
`‖W^{(n_{xy}-3)d/2} |𝒢^{abs}_{xy}| / B_{xy}‖_{w;(1,2)} ≺ W^{(n_{xy}-2)ε₀}` uniformly in `u`. -/
theorem dcWeakDom :
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (n C : ℕ) (Γ : Graph 2 n), Γ.internalize.Normal C → Γ.internalize.DoublyConnected →
      Γ.TKinds N → ∀ ε₀ : ℝ, 0 ≤ ε₀ → ε₀ < (d : ℝ) / 2 →
      ∀ (Ω : SizeL → Type) [∀ p, MeasurableSpace (Ω p)] (Pr : ∀ p, Measure (Ω p))
        (U : SizeL → Type) (z : ∀ p, U p → ℂ)
        (G : ∀ p, U p → Ω p → Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ),
        (∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) →
        StochDom (admFilterL c₀ c₁) sizeW Pr
            (fun p u ω => weakNorm d p.1.2 p.1.1 1 2 (errAbs (G p u ω) (z p u)))
            (fun p _ _ => sizeW p ^ ε₀) →
          StochDom (admFilterL c₀ c₁) sizeW Pr
            (fun p u ω => weakNorm d p.1.2 p.1.1 1 2
              (normGraph2 d p.1.2 p.1.1 Γ (gData (Smat P.ψ p.1.1 p.1.2) (z p u) Sig (G p u ω))))
            (fun p _ _ => sizeW p ^ (((Γ.ord : ℝ) - 2) * ε₀)) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n C Γ hNo hDC hT ε₀ hε₀ hε₀d Ω _ Pr U z G
    hz hdom τ hτ D hD
  have hord2 : (2 : ℤ) ≤ Γ.ord := two_le_ord n C N Γ hNo.1 hT
  set q : ℝ := (Γ.ord : ℝ) - 2 with hq
  have hq0 : 0 ≤ q := by
    have : (2 : ℝ) ≤ (Γ.ord : ℝ) := by exact_mod_cast hord2
    linarith
  set τ₁ : ℝ := min (τ / (2 * (q + 1))) (((d : ℝ) / 2 - ε₀) / 2) with hτ₁
  have hτ₁0 : 0 < τ₁ := lt_min (by positivity) (by linarith)
  have hτ₁q : q * τ₁ ≤ τ / 2 := by
    have h1 : τ₁ ≤ τ / (2 * (q + 1)) := min_le_left _ _
    have h2 : q * τ₁ ≤ q * (τ / (2 * (q + 1))) := mul_le_mul_of_nonneg_left h1 hq0
    have h3 : q * (τ / (2 * (q + 1))) ≤ τ / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hτ₁d : ε₀ + τ₁ ≤ (d : ℝ) / 2 := by
    have : τ₁ ≤ ((d : ℝ) / 2 - ε₀) / 2 := min_le_right _ _
    linarith
  obtain ⟨W₀, hW₀⟩ := dcWeak d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n C Γ hNo hDC hT
    (τ / 2) (by positivity)
  have h1 := hdom τ₁ hτ₁0 D hD
  have h2 : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ :=
    Filter.Eventually.comap (inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _)) _
  have h3 : ∀ᶠ p in admFilterL c₀ c₁, max W₀ 1 ≤ sizeW p :=
    (tendsto_sizeW_admFilterL c₀ c₁).eventually (eventually_ge_atTop _)
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  refine le_trans (measure_mono ?_) hp1
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  by_contra hne
  have hne' : ∀ u, weakNorm d p.1.2 p.1.1 1 2 (errAbs (G p u ω) (z p u)) ≤
      sizeW p ^ τ₁ * sizeW p ^ ε₀ := by
    intro u'
    by_contra h
    exact hne ⟨u', lt_of_not_ge h⟩
  have hW1 : (1 : ℝ) ≤ sizeW p := (le_max_right _ _).trans hp3
  have hW0 : (0 : ℝ) < sizeW p := by linarith
  have hΛ : sizeW p ^ τ₁ * sizeW p ^ ε₀ = sizeW p ^ (τ₁ + ε₀) := (Real.rpow_add hW0 _ _).symm
  have hΛ1 : 1 ≤ sizeW p ^ τ₁ * sizeW p ^ ε₀ := by
    rw [hΛ]; exact Real.one_le_rpow hW1 (by linarith)
  have hΛd : sizeW p ^ τ₁ * sizeW p ^ ε₀ ≤ (p.1.1 : ℝ) ^ ((d : ℝ) / 2) := by
    rw [hΛ]; exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hb := hW₀ p.1.1 p.1.2 hp2 ((le_max_left _ _).trans hp3) (z p u) (hz p u) (G p u ω) _ hΛ1
    hΛd (hne' u)
  have hpow : (p.1.1 : ℝ) ^ (τ / 2) * (sizeW p ^ τ₁ * sizeW p ^ ε₀) ^ q ≤
      sizeW p ^ τ * sizeW p ^ (q * ε₀) := by
    have e1 : (p.1.1 : ℝ) = sizeW p := rfl
    rw [e1, hΛ, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
  exact absurd (hb.trans hpow) (not_le.2 hu)

section Instances

namespace G9

end G9

section Witness
open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

end Instances

end RBM8D
