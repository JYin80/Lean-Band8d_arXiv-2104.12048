import RBM8D.Bound.KeySum
import Batteries.Tactic.OpenPrivate

/-!
# The two-net key sums [II, §9.3]

Private lemmas on the kernel `⟨x − y⟩` and its dyadic shells, for the summation estimates over
internal atoms of the two-net graphs of [II, §9.3]: the symmetry `⟨x − y⟩ = ⟨y − x⟩`, the dyadic
shell index around a point, the counting bound for a set of points by shells, and the bound
`Σ_y ⟨x − y⟩^{-d} ≤ C (log₂(L/W) + 2)`, deterministic for `W ≥ 1`, `L ≥ 2 W`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace RBM8D

open private KeySum_card_ball KeySum_zdistInf_comm KeySum_bB_eq KeySum_le_brk KeySum_brk_pos
  KeySum_bB_pos KeySum_brk_tri KeySum_brk_two KeySum_logF_two KeySum_gamma_pos
  from RBM8D.Bound.KeySum

section Geometry

variable (d L W : ℕ) [NeZero L]

/-- `⟨x - y⟩ = ⟨y - x⟩`. -/
private theorem AvgKeySum_brk_comm (x y : Zd d L) : brk d L W x y = brk d L W y x := by
  unfold brk
  rw [KeySum_zdistInf_comm]

end Geometry

section Shells

variable (d L W : ℕ) [NeZero L]

/-- The dyadic shell index of `x` around `u`: `2^n W ≤ ‖x - u‖_L + W < 2^{n+1} W`. -/
private def AvgKeySum_idx (u x : Zd d L) : ℕ :=
  Nat.log 2 ((zdistInf d L (x - u) + W) / W)

private theorem AvgKeySum_idx_bounds (hW : 1 ≤ W) (u x : Zd d L) :
    2 ^ AvgKeySum_idx d L W u x * W ≤ zdistInf d L (x - u) + W ∧
      zdistInf d L (x - u) + W < 2 ^ (AvgKeySum_idx d L W u x + 1) * W := by
  have hW0 : 0 < W := hW
  have hpos : 0 < (zdistInf d L (x - u) + W) / W := Nat.div_pos (by omega) hW0
  refine ⟨?_, ?_⟩
  · exact (Nat.le_div_iff_mul_le hW0).1 (Nat.pow_log_le_self 2 hpos.ne')
  · exact (Nat.div_lt_iff_lt_mul hW0).1 (Nat.lt_pow_succ_log_self (by norm_num) _)

private theorem AvgKeySum_idx_le (_hW : 1 ≤ W) (hWL : 2 * W ≤ L) (u x : Zd d L) :
    AvgKeySum_idx d L W u x ≤ Nat.log 2 (L / W) := by
  unfold AvgKeySum_idx
  refine Nat.log_mono_right (Nat.div_le_div_right ?_)
  have := zdistInf_le_half d L (x - u)
  omega

/-- Dyadic decomposition: for a set `S` of points whose shell indices around `u` lie in
`[a, b]`, `Σ_{x ∈ S} ⟨x - u⟩^{-p} ≤ Σ_{n ∈ [a, b]} (2^n W)^{-p} (6 · 2^n W)^d`. -/
private theorem AvgKeySum_dyadic (hW : 1 ≤ W) (p : ℕ) (u : Zd d L) (S : Finset (Zd d L))
    (a b : ℕ) (hS : ∀ x ∈ S, a ≤ AvgKeySum_idx d L W u x ∧ AvgKeySum_idx d L W u x ≤ b) :
    ∑ x ∈ S, (brk d L W x u ^ p)⁻¹ ≤
      ∑ n ∈ Finset.Ico a (b + 1), (((2 : ℝ) ^ n * W) ^ p)⁻¹ * (6 * ((2 : ℝ) ^ n * W)) ^ d := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.Ico a (b + 1))
    (g := AvgKeySum_idx d L W u) (fun x hx => by
      have := hS x hx
      simp only [Finset.mem_Ico]; omega)]
  refine Finset.sum_le_sum fun n hn => ?_
  have hX : (1 : ℝ) ≤ (2 : ℝ) ^ n * W := by
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hcard : ((S.filter fun x => AvgKeySum_idx d L W u x = n).card : ℝ) ≤
      (6 * ((2 : ℝ) ^ n * W)) ^ d := by
    have h1 : (S.filter fun x => AvgKeySum_idx d L W u x = n).card ≤
        (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - u) ≤ 2 ^ (n + 1) * W)).card := by
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_filter] at hx ⊢
      have := (AvgKeySum_idx_bounds d L W hW u x).2
      rw [hx.2] at this
      exact ⟨Finset.mem_univ _, by omega⟩
    have h2 := KeySum_card_ball d L u (2 ^ (n + 1) * W)
    have h3 : ((S.filter fun x => AvgKeySum_idx d L W u x = n).card : ℝ) ≤
        ((2 * (2 ^ (n + 1) * W) + 1 : ℕ) : ℝ) ^ d := by
      exact_mod_cast h1.trans h2
    refine h3.trans (pow_le_pow_left₀ (by positivity) ?_ d)
    push_cast
    rw [pow_succ]
    nlinarith
  have hpt : ∀ x ∈ S.filter (fun x => AvgKeySum_idx d L W u x = n),
      (brk d L W x u ^ p)⁻¹ ≤ (((2 : ℝ) ^ n * W) ^ p)⁻¹ := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    have h := (AvgKeySum_idx_bounds d L W hW u x).1
    rw [hx.2] at h
    have h' : (2 : ℝ) ^ n * W ≤ brk d L W x u := by
      unfold brk
      exact_mod_cast h
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h' p)
  calc ∑ x ∈ S.filter (fun x => AvgKeySum_idx d L W u x = n), (brk d L W x u ^ p)⁻¹
      ≤ ∑ x ∈ S.filter (fun x => AvgKeySum_idx d L W u x = n), (((2 : ℝ) ^ n * W) ^ p)⁻¹ :=
        Finset.sum_le_sum hpt
    _ = ((S.filter fun x => AvgKeySum_idx d L W u x = n).card : ℝ) * (((2 : ℝ) ^ n * W) ^ p)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (6 * ((2 : ℝ) ^ n * W)) ^ d * (((2 : ℝ) ^ n * W) ^ p)⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := mul_comm _ _

end Shells

section OnePoint

variable (d L W : ℕ) [NeZero L]

/-- `Nat.log 2 (L / W) + 1 ≤ log₂(L/W) + 2`. -/
private theorem AvgKeySum_log_le (hW : 1 ≤ W) (hWL : 2 * W ≤ L) :
    ((Nat.log 2 (L / W) : ℕ) : ℝ) + 1 ≤ logF L W := by
  have hW0 : 0 < W := hW
  set N := Nat.log 2 (L / W) with hN
  unfold logF
  have hLW0 : L / W ≠ 0 := by
    have : 0 < L / W := Nat.div_pos (by omega) hW0
    omega
  have h1 : 2 ^ N ≤ L / W := Nat.pow_log_le_self 2 hLW0
  have h2 : ((2 : ℝ)) ^ N ≤ (L : ℝ) / W := by
    have h := (by exact_mod_cast h1 : ((2 ^ N : ℕ) : ℝ) ≤ ((L / W : ℕ) : ℝ)).trans
      Nat.cast_div_le
    simpa using h
  have h3 : (N : ℝ) ≤ Real.logb 2 ((L : ℝ) / W) := by
    have hpos : (0 : ℝ) < (L : ℝ) / W := by
      have : (1 : ℝ) ≤ W := by exact_mod_cast hW
      have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
      positivity
    rw [Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast]
    exact h2
  linarith

/-- `Σ_x ⟨x - u⟩^{-d} ≤ 6^d (log₂(L/W) + 2)`. -/
private theorem AvgKeySum_log (hW : 1 ≤ W) (hWL : 2 * W ≤ L) (u : Zd d L) :
    ∑ x, (brk d L W x u ^ d)⁻¹ ≤ 6 ^ d * logF L W := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : 0 < W := hW
  set N := Nat.log 2 (L / W) with hN
  have h1 := AvgKeySum_dyadic d L W hW d u Finset.univ 0 N (fun x _ =>
    ⟨Nat.zero_le _, AvgKeySum_idx_le d L W hW hWL u x⟩)
  refine h1.trans ?_
  have h2 : ∑ n ∈ Finset.Ico 0 (N + 1), (((2 : ℝ) ^ n * W) ^ d)⁻¹ * (6 * ((2 : ℝ) ^ n * W)) ^ d =
      ∑ n ∈ Finset.Ico 0 (N + 1), (6 : ℝ) ^ d := by
    refine Finset.sum_congr rfl fun n _ => ?_
    have hX : (0 : ℝ) < (2 : ℝ) ^ n * W := by positivity
    rw [mul_pow 6 ((2 : ℝ) ^ n * W) d]
    field_simp
  rw [h2, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have := AvgKeySum_log_le L W hW hWL
  rw [Nat.sub_zero]
  push_cast
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 6) d]

end OnePoint

section Conv

variable (d L W : ℕ) [NeZero L]

end Conv

section Kernels

variable (d : ℕ)

end Kernels

section Cells

variable (d L W : ℕ) [NeZero L]

end Cells

section Examples

end Examples

end RBM8D
