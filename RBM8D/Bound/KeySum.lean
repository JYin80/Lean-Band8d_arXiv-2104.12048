module

public import RBM8D.TExp.Defs
public import RBM8D.Kernel.ThetaDecay
public import RBM8D.Kernel.ZdCancel
public import RBM8D.Profile.Symbol
public import RBM8D.Input.Entry
public import RBM8D.Input.Sizes
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import RBM8D.Bound.Norm

@[expose] public section

/-!
# The summation estimates [II, Claim 8.3]

[II, (8.10)–(8.12)] = [I, (6.32)–(6.33), (6.37)] with explicit logarithmic factors.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

/-- The ball `{y : ‖y - x₀‖_L ≤ ρ}` of `Z_L^d` has at most `(2ρ + 1)^d` points. -/
private theorem KeySum_card_ball (d L : ℕ) [NeZero L] (x₀ : Zd d L) (ρ : ℕ) :
    (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ ρ)).card ≤ (2 * ρ + 1) ^ d := by
  have h : (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(ρ : ℤ)) ρ).card = (2 * ρ + 1) ^ d := by
    rw [Fintype.card_piFinset]
    simp [Int.card_Icc]
    congr 1; omega
  rw [← h]
  refine Finset.card_le_card_of_injOn (fun y i => (y - x₀) i |>.valMinAbs) ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 := zdist_le_zdistInf d L (y - x₀) i
    rw [zdist_eq_natAbs_valMinAbs] at h1
    omega
  · intro y _ z _ hyz
    have : y - x₀ = z - x₀ := funext fun i => ZMod.valMinAbs_inj.1 (congrFun hyz i)
    exact sub_left_injective this

/-- `‖x - y‖_L = ‖y - x‖_L`. -/
private theorem KeySum_zdistInf_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← zdistInf_neg d L (x - y), neg_sub]

/-- `B_{xy} = W^{-2} ⟨x - y⟩^{-(d-2)}`. -/
private theorem KeySum_bB_eq (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) := rfl

/-- `W ≤ ⟨x - y⟩`. -/
private theorem KeySum_le_brk (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    (W : ℝ) ≤ brk d L W x y := by
  unfold brk; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]

/-- `⟨x - y⟩ > 0` for `W ≥ 1`. -/
private theorem KeySum_brk_pos (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    0 < brk d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  exact lt_of_lt_of_le (by linarith) (KeySum_le_brk d L W x y)

/-- `B_{xy} > 0` for `W ≥ 1`. -/
private theorem KeySum_bB_pos (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    0 < bB d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  rw [KeySum_bB_eq]
  have := KeySum_brk_pos d L W hW x y
  positivity

/-- `⟨p - q⟩ + W ≤ ⟨y - p⟩ + ⟨y - q⟩`. -/
private theorem KeySum_brk_tri (d L W : ℕ) [NeZero L] (y p q : Zd d L) :
    brk d L W p q + W ≤ brk d L W y p + brk d L W y q := by
  have h1 : zdistInf d L (p - q) ≤ zdistInf d L (p - y) + zdistInf d L (y - q) := by
    have := zdistInf_add_le d L (p - y) (y - q)
    rwa [sub_add_sub_cancel] at this
  rw [KeySum_zdistInf_comm d L p y] at h1
  have h2 : (zdistInf d L (p - q) : ℝ) ≤ zdistInf d L (y - p) + zdistInf d L (y - q) := by
    exact_mod_cast h1
  unfold brk
  rw [KeySum_zdistInf_comm d L p q] at h2 ⊢
  linarith [h2]

/-- If `x` is at least as close to `p` as to `q`, then `⟨p - q⟩ ≤ 2 ⟨x - q⟩`. -/
private theorem KeySum_brk_two (d L W : ℕ) [NeZero L] (x p q : Zd d L)
    (h : zdistInf d L (x - p) ≤ zdistInf d L (x - q)) :
    brk d L W p q ≤ 2 * brk d L W x q := by
  have h1 : zdistInf d L (p - q) ≤ zdistInf d L (p - x) + zdistInf d L (x - q) := by
    have := zdistInf_add_le d L (p - x) (x - q)
    rwa [sub_add_sub_cancel] at this
  rw [KeySum_zdistInf_comm d L p x] at h1
  have h2 : (zdistInf d L (p - q) : ℝ) ≤ 2 * zdistInf d L (x - q) := by
    have : zdistInf d L (p - q) ≤ 2 * zdistInf d L (x - q) := by omega
    exact_mod_cast this
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  unfold brk
  linarith

/-- Dyadic shells around `y`: if the ball sums of a nonnegative `g` satisfy
`2^q K^{-q} Σ_{‖x - y‖_L ≤ K} g(x) ≤ c` for all integers `K ∈ [W, L/2]`, then
`Σ_x g(x) ⟨x - y⟩^{-q} ≤ (log₂(L/W) + 2) c`, for `q ≥ 0`, `W ≥ 1`, `L ≥ 2W`. -/
private theorem KeySum_shell (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (hWL : 2 * W ≤ L)
    (y : Zd d L) (q c : ℝ) (hq : 0 ≤ q) (g : Zd d L → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hc : ∀ K : ℕ, W ≤ K → 2 * K ≤ L →
      (2 : ℝ) ^ q * (K : ℝ) ^ (-q) *
        ∑ x ∈ Finset.univ.filter (fun x : Zd d L => zdistInf d L (x - y) ≤ K), g x ≤ c) :
    ∑ x, g x * brk d L W x y ^ (-q) ≤ logF L W * c := by
  have hW0 : 0 < W := hW
  set H := L / 2 with hH
  have hWH : W ≤ H := by omega
  set ρ : ℕ → ℕ := fun n => min (2 ^ n * W) H with hρ
  have hρW : ∀ n, W ≤ ρ n := fun n =>
    le_min (Nat.le_mul_of_pos_left _ (by positivity)) hWH
  have hρH : ∀ n, ρ n ≤ H := fun n => min_le_right _ _
  have hρ2 : ∀ n, 2 * ρ n ≤ L := fun n => by have := hρH n; omega
  have hρs : ∀ n, ρ (n + 1) ≤ 2 * ρ n := fun n => by
    have e : 2 ^ (n + 1) * W = 2 * (2 ^ n * W) := by ring
    simp only [hρ, e]
    generalize 2 ^ n * W = X
    omega
  have hρ0 : ρ 0 ≤ W := by simp [hρ]
  set N := Nat.log 2 (L / W) with hN
  have hLW : L < 2 ^ (N + 1) * W :=
    (Nat.div_lt_iff_lt_mul hW0).1 (Nat.lt_pow_succ_log_self (by norm_num) _)
  have hρN : ρ N = H := by
    have e : 2 ^ (N + 1) * W = 2 * (2 ^ N * W) := by ring
    have : H ≤ 2 ^ N * W := by omega
    exact min_eq_right this
  have hN1 : ((N : ℝ) + 1) ≤ logF L W := by
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
  have hcover : ∀ n x, zdistInf d L (x - y) ≤ ρ n →
      ∃ m ≤ n, zdistInf d L (x - y) ≤ ρ m ∧ ρ m ≤ 2 * (zdistInf d L (x - y) + W) := by
    intro n
    induction n with
    | zero => exact fun x hx => ⟨0, le_rfl, hx, by omega⟩
    | succ n ih =>
      intro x hx
      by_cases h : zdistInf d L (x - y) ≤ ρ n
      · obtain ⟨m, hm, h1, h2⟩ := ih x h
        exact ⟨m, by omega, h1, h2⟩
      · refine ⟨n + 1, le_rfl, hx, ?_⟩
        have := hρs n
        omega
  have hc0 : 0 ≤ c := by
    refine le_trans ?_ (hc W le_rfl hWL)
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Finset.sum_nonneg fun x _ => hg x)
  have hpt : ∀ x, g x * brk d L W x y ^ (-q) ≤ ∑ n ∈ Finset.range (N + 1),
      ((2 : ℝ) ^ q * (ρ n : ℝ) ^ (-q)) *
        (if zdistInf d L (x - y) ≤ ρ n then g x else 0) := by
    intro x
    obtain ⟨m, hm, hxm, hρm⟩ := hcover N x (by rw [hρN]; exact zdistInf_le_half d L (x - y))
    have hρpos : (0 : ℝ) < ρ m := by
      have : (1 : ℝ) ≤ W := by exact_mod_cast hW
      have : (W : ℝ) ≤ ρ m := by exact_mod_cast hρW m
      linarith
    have hb : (ρ m : ℝ) / 2 ≤ brk d L W x y := by
      unfold brk
      have : (ρ m : ℝ) ≤ 2 * ((zdistInf d L (x - y) : ℝ) + W) := by exact_mod_cast hρm
      linarith
    have h1 : brk d L W x y ^ (-q) ≤ (2 : ℝ) ^ q * (ρ m : ℝ) ^ (-q) := by
      refine (Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)).trans (le_of_eq ?_)
      rw [Real.div_rpow hρpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]
    have hterm : ∀ n ∈ Finset.range (N + 1), 0 ≤ ((2 : ℝ) ^ q * (ρ n : ℝ) ^ (-q)) *
        (if zdistInf d L (x - y) ≤ ρ n then g x else 0) := by
      intro n _
      refine mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
      split_ifs
      · exact hg x
      · exact le_rfl
    refine le_trans ?_ (Finset.single_le_sum hterm (Finset.mem_range.2 (by omega : m < N + 1)))
    simp only [hxm, ite_true]
    rw [mul_comm (g x)]
    exact mul_le_mul_of_nonneg_right h1 (hg x)
  calc ∑ x, g x * brk d L W x y ^ (-q)
      ≤ ∑ x, ∑ n ∈ Finset.range (N + 1), ((2 : ℝ) ^ q * (ρ n : ℝ) ^ (-q)) *
          (if zdistInf d L (x - y) ≤ ρ n then g x else 0) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ n ∈ Finset.range (N + 1), ((2 : ℝ) ^ q * (ρ n : ℝ) ^ (-q)) *
          ∑ x ∈ Finset.univ.filter (fun x : Zd d L => zdistInf d L (x - y) ≤ ρ n), g x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.mul_sum, Finset.sum_filter]
    _ ≤ ∑ n ∈ Finset.range (N + 1), c :=
        Finset.sum_le_sum fun n _ => hc (ρ n) (hρW n) (hρ2 n)
    _ = ((N : ℝ) + 1) * c := by simp
    _ ≤ logF L W * c := mul_le_mul_of_nonneg_right hN1 hc0

/-- For `p ≥ d`, `Σ_z ⟨z - x⟩^{-p} ≤ C (log₂(L/W) + 2) W^{d-p}` with `C` depending on `d, p`
only, for `W ≥ 1` and `L ≥ 2W`. -/
private theorem KeySum_tail (d : ℕ) (p : ℝ) (hp : (d : ℝ) ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L → ∀ x : Zd d L,
      ∑ z, brk d L W z x ^ (-p) ≤ C * logF L W * (W : ℝ) ^ ((d : ℝ) - p) := by
  have hp0 : 0 ≤ p := le_trans (Nat.cast_nonneg _) hp
  refine ⟨2 ^ p * 3 ^ d, by positivity, fun L W _ hW hWL x => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have key := KeySum_shell d L W hW hWL x p ((2 : ℝ) ^ p * 3 ^ d * (W : ℝ) ^ ((d : ℝ) - p)) hp0
    (fun _ => 1) (fun _ => zero_le_one) (fun K hK1 hK2 => ?_)
  · simp only [one_mul] at key
    calc _ ≤ _ := key
      _ = _ := by ring
  · have hK1' : (W : ℝ) ≤ K := by exact_mod_cast hK1
    have hK0 : (0 : ℝ) < K := by linarith
    have hcard : ((Finset.univ.filter (fun z : Zd d L => zdistInf d L (z - x) ≤ K)).card : ℝ) ≤
        (3 * K) ^ d := by
      calc _ ≤ ((2 * K + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast KeySum_card_ball d L x K
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by push_cast; linarith) d
    have hKp : (K : ℝ) ^ (-p) * (K : ℝ) ^ d = (K : ℝ) ^ ((d : ℝ) - p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hK0]; congr 1; ring
    have hKW : (K : ℝ) ^ ((d : ℝ) - p) ≤ (W : ℝ) ^ ((d : ℝ) - p) :=
      Real.rpow_le_rpow_of_nonpos hW0 hK1' (by linarith)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    calc (2 : ℝ) ^ p * (K : ℝ) ^ (-p) * _ ≤ (2 : ℝ) ^ p * (K : ℝ) ^ (-p) * (3 * K) ^ d :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = (2 : ℝ) ^ p * 3 ^ d * ((K : ℝ) ^ (-p) * (K : ℝ) ^ d) := by rw [mul_pow]; ring
      _ ≤ _ := by
          rw [hKp]
          exact mul_le_mul_of_nonneg_left hKW (by positivity)

/-- The weak norm is nonnegative for `W ≥ 1`. -/
private theorem KeySum_weak_nonneg (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (a b : ℝ)
    (A : Matrix (Zd d L) (Zd d L) ℝ) : 0 ≤ weakNorm d L W a b A := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h := (normBasic d L W hW a b A).1 0 0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).1 ((abs_nonneg _).trans h)

/-- The strong norm is nonnegative for `W ≥ 1`. -/
private theorem KeySum_strong_nonneg (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (a b : ℝ)
    (A : Matrix (Zd d L) (Zd d L) ℝ) : 0 ≤ strongNorm d L W a b A := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h := (normBasic d L W hW a b A).2.2 0 0
  have ht := KeySum_brk_pos d L W hW (0 : Zd d L) 0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).1 ((abs_nonneg _).trans h)

/-- The one-point sum `Σ_x |A_{xβ}| B_{xy} ≤ C (log₂(L/W) + 2) W^{-ad/2} ‖A‖_{w;(a,b)}` for
`d ≥ 2` and `ad/2 - b - 2 ≥ 0`, with `C` depending on `d` only. -/
private theorem KeySum_one (d : ℕ) (a b : ℝ) (hd : 2 ≤ d) (he : 0 ≤ a * d / 2 - b - 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L →
      ∀ (A : Matrix (Zd d L) (Zd d L) ℝ) (β y : Zd d L),
        ∑ x, |A x β| * bB d L W x y ≤
          C * logF L W * (W : ℝ) ^ (-(a * d / 2)) * weakNorm d L W a b A := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨2 ^ ((d : ℝ) - 2), by positivity, fun L W _ hW hWL A β y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hw0 := KeySum_weak_nonneg d L W hW a b A
  have hnorm := normBasic d L W hW a b A
  have key := KeySum_shell d L W hW hWL y ((d : ℝ) - 2)
    ((2 : ℝ) ^ ((d : ℝ) - 2) * ((W : ℝ) ^ (-b) * (W : ℝ) ^ (2 - (a * d / 2 - b)) *
      weakNorm d L W a b A)) (by linarith) (fun x => |A x β|) (fun x => abs_nonneg _)
    (fun K hK1 hK2 => ?_)
  · have hB : ∀ x, |A x β| * bB d L W x y =
        (W : ℝ) ^ (-2 : ℝ) * (|A x β| * brk d L W x y ^ (-((d : ℝ) - 2))) := by
      intro x
      rw [KeySum_bB_eq, show -((d : ℝ) - 2) = 2 - (d : ℝ) by ring]
      ring
    rw [Finset.sum_congr rfl fun x _ => hB x, ← Finset.mul_sum]
    have hW2 : 0 ≤ (W : ℝ) ^ (-2 : ℝ) := by positivity
    have hexp : (W : ℝ) ^ (-2 : ℝ) * ((W : ℝ) ^ (-b) * (W : ℝ) ^ (2 - (a * d / 2 - b))) =
        (W : ℝ) ^ (-(a * d / 2)) := by
      rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring
    calc (W : ℝ) ^ (-2 : ℝ) * ∑ x, |A x β| * brk d L W x y ^ (-((d : ℝ) - 2))
        ≤ (W : ℝ) ^ (-2 : ℝ) * (logF L W * ((2 : ℝ) ^ ((d : ℝ) - 2) *
          ((W : ℝ) ^ (-b) * (W : ℝ) ^ (2 - (a * d / 2 - b)) * weakNorm d L W a b A))) :=
          mul_le_mul_of_nonneg_left key hW2
      _ = _ := by rw [← hexp]; ring
  · have hK1' : (W : ℝ) ≤ K := by exact_mod_cast hK1
    have hK0 : (0 : ℝ) < K := by linarith
    have hball := hnorm.2.1 K hK1 hK2 β y
    rw [div_le_iff₀ (by positivity)] at hball
    have hsum : ∑ x ∈ Finset.univ.filter (fun x : Zd d L => zdistInf d L (x - y) ≤ K), |A x β| ≤
        (W : ℝ) ^ (-b) * (K : ℝ) ^ (-(a * d / 2 - b)) * weakNorm d L W a b A * (K : ℝ) ^ d := by
      refine le_trans ?_ hball
      exact Finset.sum_le_sum fun x _ => by linarith [abs_nonneg (A β x)]
    have hKe : (K : ℝ) ^ (-((d : ℝ) - 2)) * (K : ℝ) ^ (-(a * d / 2 - b)) * (K : ℝ) ^ d =
        (K : ℝ) ^ (2 - (a * d / 2 - b)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hK0, ← Real.rpow_add hK0]; congr 1; ring
    have hKW : (K : ℝ) ^ (2 - (a * d / 2 - b)) ≤ (W : ℝ) ^ (2 - (a * d / 2 - b)) :=
      Real.rpow_le_rpow_of_nonpos hW0 hK1' (by linarith)
    have hq : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * (K : ℝ) ^ (-((d : ℝ) - 2)) := by positivity
    calc (2 : ℝ) ^ ((d : ℝ) - 2) * (K : ℝ) ^ (-((d : ℝ) - 2)) *
          ∑ x ∈ Finset.univ.filter (fun x : Zd d L => zdistInf d L (x - y) ≤ K), |A x β|
        ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * (K : ℝ) ^ (-((d : ℝ) - 2)) *
          ((W : ℝ) ^ (-b) * (K : ℝ) ^ (-(a * d / 2 - b)) * weakNorm d L W a b A * (K : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hsum hq
      _ = (2 : ℝ) ^ ((d : ℝ) - 2) * ((W : ℝ) ^ (-b) * weakNorm d L W a b A *
          ((K : ℝ) ^ (-((d : ℝ) - 2)) * (K : ℝ) ^ (-(a * d / 2 - b)) * (K : ℝ) ^ d)) := by ring
      _ ≤ _ := by
          rw [hKe]
          have := mul_le_mul_of_nonneg_left hKW (by positivity :
            (0 : ℝ) ≤ (W : ℝ) ^ (-b) * weakNorm d L W a b A)
          calc _ ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * ((W : ℝ) ^ (-b) * weakNorm d L W a b A *
              (W : ℝ) ^ (2 - (a * d / 2 - b))) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring

/-- The nearest of the points `y_i` to `x` dominates the product: `Π_i B_{x y_i} ≤ 2^{(d-2)k}
Σ_s B_{x y_s} Π_{j ≠ s} B_{y_s y_j}`, for `d ≥ 2`, `k ≥ 1`. -/
private theorem KeySum_prod_le (d L W : ℕ) [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) {k : ℕ}
    (hk : 1 ≤ k) (y : Fin k → Zd d L) (x : Zd d L) :
    ∏ i, bB d L W x (y i) ≤ ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k *
      ∑ s, bB d L W x (y s) * ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨s, -, hs⟩ := Finset.exists_min_image Finset.univ (fun i => zdistInf d L (x - y i)) hne
  set lam : ℝ := (2 : ℝ) ^ ((d : ℝ) - 2) with hlamdef
  have hlam : 1 ≤ lam := Real.one_le_rpow (by norm_num) (by linarith)
  have hj : ∀ j, bB d L W x (y j) ≤ lam * bB d L W (y s) (y j) := by
    intro j
    have h2 := KeySum_brk_two d L W x (y s) (y j) (hs j (Finset.mem_univ _))
    have hpos1 := KeySum_brk_pos d L W hW (y s) (y j)
    have hpos2 := KeySum_brk_pos d L W hW x (y j)
    have h3 : (2 * brk d L W x (y j)) ^ (2 - (d : ℝ)) ≤
        brk d L W (y s) (y j) ^ (2 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hpos1 h2 (by linarith)
    rw [Real.mul_rpow (by norm_num) hpos2.le] at h3
    have h4 : (2 : ℝ) ^ (2 - (d : ℝ)) * lam = 1 := by
      rw [hlamdef, ← Real.rpow_add (by norm_num)]; simp
    have h5 : brk d L W x (y j) ^ (2 - (d : ℝ)) ≤
        lam * brk d L W (y s) (y j) ^ (2 - (d : ℝ)) := by
      calc _ = (2 ^ (2 - (d : ℝ)) * lam) * brk d L W x (y j) ^ (2 - (d : ℝ)) := by
            rw [h4, one_mul]
        _ = lam * ((2 : ℝ) ^ (2 - (d : ℝ)) * brk d L W x (y j) ^ (2 - (d : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by linarith)
    rw [KeySum_bB_eq, KeySum_bB_eq]
    calc _ ≤ (W : ℝ) ^ (-2 : ℝ) * (lam * brk d L W (y s) (y j) ^ (2 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring
  have hprod : ∏ j ∈ Finset.univ.erase s, bB d L W x (y j) ≤
      lam ^ k * ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j) := by
    calc _ ≤ ∏ j ∈ Finset.univ.erase s, (lam * bB d L W (y s) (y j)) :=
          Finset.prod_le_prod₀ (fun j _ => (KeySum_bB_pos d L W hW _ _).le) fun j _ => hj j
      _ = lam ^ ((Finset.univ.erase s).card) *
            ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlam ?_)
            (Finset.prod_nonneg fun j _ => (KeySum_bB_pos d L W hW _ _).le)
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          omega
  have hterm : ∀ t ∈ (Finset.univ : Finset (Fin k)), 0 ≤ bB d L W x (y t) *
      ∏ j ∈ Finset.univ.erase t, bB d L W (y t) (y j) := fun t _ =>
    mul_nonneg (KeySum_bB_pos d L W hW _ _).le
      (Finset.prod_nonneg fun j _ => (KeySum_bB_pos d L W hW _ _).le)
  calc ∏ i, bB d L W x (y i) = bB d L W x (y s) * ∏ j ∈ Finset.univ.erase s, bB d L W x (y j) :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ s)).symm
    _ ≤ bB d L W x (y s) * (lam ^ k * ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j)) :=
        mul_le_mul_of_nonneg_left hprod (KeySum_bB_pos d L W hW _ _).le
    _ = lam ^ k * (bB d L W x (y s) * ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j)) := by ring
    _ ≤ lam ^ k * ∑ t, bB d L W x (y t) * ∏ j ∈ Finset.univ.erase t, bB d L W (y t) (y j) :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum hterm (Finset.mem_univ s))
          (by positivity)

/-- `log₂(L/W) + 2 ≥ 2` for `1 ≤ W ≤ L`. -/
private theorem KeySum_logF_two (L W : ℕ) (hW : 1 ≤ W) (hWL : W ≤ L) : 2 ≤ logF L W := by
  unfold logF
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have : (1 : ℝ) ≤ (L : ℝ) / W := by
    rw [le_div_iff₀ hW0, one_mul]; exact_mod_cast hWL
  have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) this
  linarith

/-- `Γ(y) > 0` for `W ≥ 1` and `k ≥ 1`. -/
private theorem KeySum_gamma_pos (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) {k : ℕ} (hk : 1 ≤ k)
    (y : Fin k → Zd d L) : 0 < gammaB d L W y := by
  unfold gammaB
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun i _ => Finset.prod_pos fun j _ => KeySum_bB_pos d L W hW _ _) hne

/-- The one-point estimate summed over `k` points: for `d ≥ 2` and `ad/2 - b - 2 ≥ 0`,
`Σ_x |A_{xβ}| Π_i B_{x y_i} ≤ C (log₂(L/W) + 2) W^{-ad/2} Γ(y) ‖A‖_{w;(a,b)}`. -/
private theorem KeySum_obs3 (d : ℕ) (a b : ℝ) (hd : 2 ≤ d) (he : 0 ≤ a * d / 2 - b - 2)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L →
      ∀ (A : Matrix (Zd d L) (Zd d L) ℝ) (β : Zd d L) (y : Fin k → Zd d L),
        ∑ x, |A x β| * ∏ i, bB d L W x (y i) ≤
          C * logF L W * (W : ℝ) ^ (-(a * d / 2)) * gammaB d L W y * weakNorm d L W a b A := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₁, hC₁, h1⟩ := KeySum_one d a b hd he
  refine ⟨((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * C₁, by positivity, fun L W _ hW hWL A β y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hw0 := KeySum_weak_nonneg d L W hW a b A
  set X : ℝ := C₁ * logF L W * (W : ℝ) ^ (-(a * d / 2)) * weakNorm d L W a b A with hX
  have hΓ : ∀ s : Fin k, 0 ≤ ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j) := fun s =>
    Finset.prod_nonneg fun j _ => (KeySum_bB_pos d L W hW _ _).le
  calc ∑ x, |A x β| * ∏ i, bB d L W x (y i)
      ≤ ∑ x, ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * ∑ s, (∏ j ∈ Finset.univ.erase s,
          bB d L W (y s) (y j)) * (|A x β| * bB d L W x (y s)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        calc _ ≤ |A x β| * (((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * ∑ s, bB d L W x (y s) *
              ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j)) :=
              mul_le_mul_of_nonneg_left (KeySum_prod_le d L W hd hW hk y x) (abs_nonneg _)
          _ = _ := by
              simp only [Finset.mul_sum]
              exact Finset.sum_congr rfl fun s _ => by ring
    _ = ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * ∑ s, (∏ j ∈ Finset.univ.erase s,
          bB d L W (y s) (y j)) * ∑ x, |A x β| * bB d L W x (y s) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * ∑ s, (∏ j ∈ Finset.univ.erase s,
          bB d L W (y s) (y j)) * X := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (h1 L W hW hWL A β (y s)) (hΓ s)
    _ = _ := by
        rw [← Finset.sum_mul]
        unfold gammaB
        rw [hX]; ring

/-- [II, (8.10)] = [I, (6.32)]: for `d ≥ 2`, `a, b > 0` with `ad/2 - b - 2 ≥ 0` ([II, (8.9)])
and `k ≥ 1`, `Σ_x |A_{xβ}| Π_i B_{x y_i} ≤ C (log₂(L/W) + 2)^k W^{-ad/2} Γ(y) ‖A‖_{w;(a,b)}`
for `W ≥ 1`, `L ≥ 2W`. -/
theorem keyobs3 :
  ∀ (d : ℕ) (a b : ℝ), 2 ≤ d → 0 < a → 0 < b → 0 ≤ a * d / 2 - b - 2 →
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ,
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L →
      ∀ (A : Matrix (Zd d L) (Zd d L) ℝ) (β : Zd d L) (y : Fin k → Zd d L),
        ∑ x, |A x β| * ∏ i, bB d L W x (y i) ≤
          C * logF L W ^ k * (W : ℝ) ^ (-(a * d / 2)) * gammaB d L W y * weakNorm d L W a b A := by
  intro d a b hd _ _ he k hk
  obtain ⟨C, hC, h⟩ := KeySum_obs3 d a b hd he k hk
  refine ⟨C, fun L W _ hW hWL A β y => ?_⟩
  refine (h L W hW hWL A β y).trans ?_
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hw0 := KeySum_weak_nonneg d L W hW a b A
  have hΓ0 := (KeySum_gamma_pos d L W hW hk y).le
  have hlog := KeySum_logF_two L W hW (by omega)
  have hle : logF L W ≤ logF L W ^ k := le_self_pow₀ (by linarith) (by omega)
  have : 0 ≤ (W : ℝ) ^ (-(a * d / 2)) := by positivity
  gcongr

/-- For positive `u, v` and `s, t ≥ 0`, `u^{-s} v^{-t} ≤ u^{-(s+t)} + v^{-(s+t)}`. -/
private theorem KeySum_min_pow {u v s t r : ℝ} (hu : 0 < u) (hv : 0 < v) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hr : s + t = r) : u ^ (-s) * v ^ (-t) ≤ u ^ (-r) + v ^ (-r) := by
  have e1 : u ^ (-r) = u ^ (-s) * u ^ (-t) := by
    rw [← Real.rpow_add hu]; congr 1; linarith
  have e2 : v ^ (-r) = v ^ (-s) * v ^ (-t) := by
    rw [← Real.rpow_add hv]; congr 1; linarith
  have hu1 : 0 ≤ u ^ (-r) := Real.rpow_nonneg hu.le _
  have hv1 : 0 ≤ v ^ (-r) := Real.rpow_nonneg hv.le _
  rcases le_total u v with h | h
  · have : v ^ (-t) ≤ u ^ (-t) := Real.rpow_le_rpow_of_nonpos hu h (by linarith)
    calc _ ≤ u ^ (-s) * u ^ (-t) := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hu.le _)
      _ ≤ _ := by rw [← e1]; linarith
  · have : u ^ (-s) ≤ v ^ (-s) := Real.rpow_le_rpow_of_nonpos hv h (by linarith)
    calc _ ≤ v ^ (-s) * v ^ (-t) := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hv.le _)
      _ ≤ _ := by rw [← e2]; linarith

/-- If `D ≤ 2 v` then `v^{-e} ≤ 2^e D^{-e}`, for `e ≥ 0`. -/
private theorem KeySum_half_pow {D v e : ℝ} (hD : 0 < D) (he : 0 ≤ e) (h : D ≤ 2 * v) :
    v ^ (-e) ≤ 2 ^ e * D ^ (-e) := by
  have hv : 0 < v := by linarith
  have h1 : v ^ (-e) ≤ (D / 2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  refine h1.trans (le_of_eq ?_)
  rw [Real.div_rpow hD.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul, mul_comm]

/-- If `D ≤ u + v` then `u^{-e} v^{-e} ≤ 2^e D^{-e} (u^{-e} + v^{-e})`, for `e ≥ 0`. -/
private theorem KeySum_prod_pow {D u v e : ℝ} (hD : 0 < D) (hu : 0 < u) (hv : 0 < v)
    (he : 0 ≤ e) (h : D ≤ u + v) :
    u ^ (-e) * v ^ (-e) ≤ 2 ^ e * D ^ (-e) * (u ^ (-e) + v ^ (-e)) := by
  have hu1 : 0 ≤ u ^ (-e) := Real.rpow_nonneg hu.le _
  have hv1 : 0 ≤ v ^ (-e) := Real.rpow_nonneg hv.le _
  have hc : 0 ≤ (2 : ℝ) ^ e * D ^ (-e) := by positivity
  rcases le_total u v with h' | h'
  · have := KeySum_half_pow hD he (by linarith : D ≤ 2 * v)
    nlinarith [mul_le_mul_of_nonneg_left this hu1]
  · have := KeySum_half_pow hD he (by linarith : D ≤ 2 * u)
    nlinarith [mul_le_mul_of_nonneg_left this hv1]

/-- `Σ_x ⟨x - α⟩^{-e} ⟨x - β⟩^{-e} B_{xy} ≤ C (log₂(L/W) + 2) W^{-e} ⟨α - β⟩^{-e}` for `d ≥ 2`
and `e ≥ 2`, with `C` depending on `d, e` only. -/
private theorem KeySum_two (d : ℕ) (e : ℝ) (hd : 2 ≤ d) (he : 2 ≤ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L → ∀ α β y : Zd d L,
      ∑ x, brk d L W x α ^ (-e) * brk d L W x β ^ (-e) * bB d L W x y ≤
        C * logF L W * (W : ℝ) ^ (-e) * brk d L W α β ^ (-e) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨CT, hCT, hT⟩ := KeySum_tail d ((d : ℝ) + e - 2) (by linarith)
  refine ⟨4 * 2 ^ e * CT, by positivity, fun L W _ hW hWL α β y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hlog := KeySum_logF_two L W hW (by omega)
  set D := brk d L W α β with hD
  have hD0 : 0 < D := KeySum_brk_pos d L W hW α β
  -- pointwise bound for `⟨x - α⟩^{-e} B_{xy}`
  have hone : ∀ z x : Zd d L, brk d L W x z ^ (-e) * bB d L W x y ≤
      (W : ℝ) ^ (-2 : ℝ) * (brk d L W x z ^ (-((d : ℝ) + e - 2)) +
        brk d L W x y ^ (-((d : ℝ) + e - 2))) := by
    intro z x
    have := KeySum_min_pow (KeySum_brk_pos d L W hW x z) (KeySum_brk_pos d L W hW x y)
      (by linarith : 0 ≤ e) (by linarith : 0 ≤ (d : ℝ) - 2)
      (by ring : e + ((d : ℝ) - 2) = (d : ℝ) + e - 2)
    rw [KeySum_bB_eq, show (2 - (d : ℝ)) = -((d : ℝ) - 2) by ring]
    calc _ = (W : ℝ) ^ (-2 : ℝ) * (brk d L W x z ^ (-e) * brk d L W x y ^ (-((d : ℝ) - 2))) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have hpt : ∀ x : Zd d L, brk d L W x α ^ (-e) * brk d L W x β ^ (-e) * bB d L W x y ≤
      2 ^ e * D ^ (-e) * ((W : ℝ) ^ (-2 : ℝ) * ((brk d L W x α ^ (-((d : ℝ) + e - 2)) +
        brk d L W x y ^ (-((d : ℝ) + e - 2))) + (brk d L W x β ^ (-((d : ℝ) + e - 2)) +
        brk d L W x y ^ (-((d : ℝ) + e - 2))))) := by
    intro x
    have h1 := KeySum_prod_pow hD0 (KeySum_brk_pos d L W hW x α) (KeySum_brk_pos d L W hW x β)
      (by linarith : 0 ≤ e) (by have := KeySum_brk_tri d L W x α β; linarith)
    have hB0 := (KeySum_bB_pos d L W hW x y).le
    calc _ ≤ 2 ^ e * D ^ (-e) * (brk d L W x α ^ (-e) + brk d L W x β ^ (-e)) *
          bB d L W x y := mul_le_mul_of_nonneg_right h1 hB0
      _ = 2 ^ e * D ^ (-e) * (brk d L W x α ^ (-e) * bB d L W x y +
          brk d L W x β ^ (-e) * bB d L W x y) := by ring
      _ ≤ 2 ^ e * D ^ (-e) * ((W : ℝ) ^ (-2 : ℝ) * (brk d L W x α ^ (-((d : ℝ) + e - 2)) +
          brk d L W x y ^ (-((d : ℝ) + e - 2))) + (W : ℝ) ^ (-2 : ℝ) *
          (brk d L W x β ^ (-((d : ℝ) + e - 2)) + brk d L W x y ^ (-((d : ℝ) + e - 2)))) :=
          mul_le_mul_of_nonneg_left (add_le_add (hone α x) (hone β x)) (by positivity)
      _ = _ := by ring
  have hTα := hT L W hW hWL α
  have hTβ := hT L W hW hWL β
  have hTy := hT L W hW hWL y
  have hexp : (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ ((d : ℝ) - ((d : ℝ) + e - 2)) = (W : ℝ) ^ (-e) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  calc ∑ x, brk d L W x α ^ (-e) * brk d L W x β ^ (-e) * bB d L W x y
      ≤ ∑ x, 2 ^ e * D ^ (-e) * ((W : ℝ) ^ (-2 : ℝ) * ((brk d L W x α ^ (-((d : ℝ) + e - 2)) +
        brk d L W x y ^ (-((d : ℝ) + e - 2))) + (brk d L W x β ^ (-((d : ℝ) + e - 2)) +
        brk d L W x y ^ (-((d : ℝ) + e - 2))))) := Finset.sum_le_sum fun x _ => hpt x
    _ = 2 ^ e * D ^ (-e) * ((W : ℝ) ^ (-2 : ℝ) *
        ((∑ x, brk d L W x α ^ (-((d : ℝ) + e - 2)) + ∑ x, brk d L W x y ^ (-((d : ℝ) + e - 2))) +
        (∑ x, brk d L W x β ^ (-((d : ℝ) + e - 2)) +
          ∑ x, brk d L W x y ^ (-((d : ℝ) + e - 2))))) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 ^ e * D ^ (-e) * ((W : ℝ) ^ (-2 : ℝ) *
        ((CT * logF L W * (W : ℝ) ^ ((d : ℝ) - ((d : ℝ) + e - 2)) +
          CT * logF L W * (W : ℝ) ^ ((d : ℝ) - ((d : ℝ) + e - 2))) +
        (CT * logF L W * (W : ℝ) ^ ((d : ℝ) - ((d : ℝ) + e - 2)) +
          CT * logF L W * (W : ℝ) ^ ((d : ℝ) - ((d : ℝ) + e - 2))))) := by
        gcongr
    _ = _ := by
        rw [← hexp]; ring

/-- [II, (8.11)] with `⟨α - β⟩` (the strong form of [I, (6.33)]): under the conditions of
`keyobs3`, `Σ_x |A¹_{xα}| |A²_{xβ}| Π_i B_{x y_i} ≤ C (log₂(L/W) + 2)^{k+2} W^{-ad/2} Γ(y)
W^{-b} ⟨α - β⟩^{-(ad/2 - b)} ‖A¹‖_{s;(a,b)} ‖A²‖_{s;(a,b)}`. -/
theorem keyobs2Strong :
  ∀ (d : ℕ) (a b : ℝ), 2 ≤ d → 0 < a → 0 < b → 0 ≤ a * d / 2 - b - 2 →
    ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ,
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L →
      ∀ (A₁ A₂ : Matrix (Zd d L) (Zd d L) ℝ) (α β : Zd d L) (y : Fin k → Zd d L),
        ∑ x, |A₁ x α| * |A₂ x β| * ∏ i, bB d L W x (y i) ≤
          C * logF L W ^ (k + 2) * (W : ℝ) ^ (-(a * d / 2)) * gammaB d L W y *
            ((W : ℝ) ^ (-b) * brk d L W α β ^ (-(a * d / 2 - b))) *
            strongNorm d L W a b A₁ * strongNorm d L W a b A₂ := by
  intro d a b hd _ _ he k hk
  obtain ⟨C₂, hC₂, h2⟩ := KeySum_two d (a * d / 2 - b) hd (by linarith)
  refine ⟨((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * C₂, fun L W _ hW hWL A₁ A₂ α β y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hs₁ := KeySum_strong_nonneg d L W hW a b A₁
  have hs₂ := KeySum_strong_nonneg d L W hW a b A₂
  have hn₁ := (normBasic d L W hW a b A₁).2.2
  have hn₂ := (normBasic d L W hW a b A₂).2.2
  have hlog := KeySum_logF_two L W hW (by omega)
  have hΓ0 := (KeySum_gamma_pos d L W hW hk y).le
  have hD0 := KeySum_brk_pos d L W hW α β
  set e : ℝ := a * d / 2 - b with he_def
  set Q : ℝ := (W : ℝ) ^ (-b) * (W : ℝ) ^ (-b) * (strongNorm d L W a b A₁ *
    strongNorm d L W a b A₂) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hpt : ∀ x : Zd d L, |A₁ x α| * |A₂ x β| ≤
      Q * (brk d L W x α ^ (-e) * brk d L W x β ^ (-e)) := by
    intro x
    have e1 := hn₁ x α
    have e2 := hn₂ x β
    calc _ ≤ ((W : ℝ) ^ (-b) * brk d L W x α ^ (-e) * strongNorm d L W a b A₁) *
          ((W : ℝ) ^ (-b) * brk d L W x β ^ (-e) * strongNorm d L W a b A₂) :=
          mul_le_mul e1 e2 (abs_nonneg _) (mul_nonneg (mul_nonneg (by positivity)
            (Real.rpow_nonneg (KeySum_brk_pos d L W hW x α).le _)) hs₁)
      _ = _ := by rw [hQ]; ring
  have hΓs : ∀ s : Fin k, 0 ≤ ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j) := fun s =>
    Finset.prod_nonneg fun j _ => (KeySum_bB_pos d L W hW _ _).le
  set Y : ℝ := C₂ * logF L W * (W : ℝ) ^ (-e) * brk d L W α β ^ (-e) with hY
  have hexp : (W : ℝ) ^ (-b) * (W : ℝ) ^ (-b) * (W : ℝ) ^ (-e) =
      (W : ℝ) ^ (-(a * d / 2)) * (W : ℝ) ^ (-b) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; rw [he_def]; ring
  have hle : logF L W ≤ logF L W ^ (k + 2) := le_self_pow₀ (by linarith) (by omega)
  have hW' : 0 ≤ (W : ℝ) ^ (-(a * d / 2)) := by positivity
  have hD' : 0 ≤ brk d L W α β ^ (-e) := Real.rpow_nonneg hD0.le _
  calc ∑ x, |A₁ x α| * |A₂ x β| * ∏ i, bB d L W x (y i)
      ≤ ∑ x, Q * (((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * ∑ s, (∏ j ∈ Finset.univ.erase s,
          bB d L W (y s) (y j)) * (brk d L W x α ^ (-e) * brk d L W x β ^ (-e) *
            bB d L W x (y s))) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have hprod := KeySum_prod_le d L W hd hW hk y x
        have hu := Real.rpow_nonneg (KeySum_brk_pos d L W hW x α).le (-e)
        have hv := Real.rpow_nonneg (KeySum_brk_pos d L W hW x β).le (-e)
        calc _ ≤ (Q * (brk d L W x α ^ (-e) * brk d L W x β ^ (-e))) *
              (((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * ∑ s, bB d L W x (y s) *
                ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j)) :=
              mul_le_mul (hpt x) hprod (Finset.prod_nonneg fun i _ =>
                (KeySum_bB_pos d L W hW _ _).le) (by positivity)
          _ = _ := by
              have hsw : (brk d L W x α ^ (-e) * brk d L W x β ^ (-e)) *
                  ∑ s, bB d L W x (y s) * ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j) =
                  ∑ s, (∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j)) *
                    (brk d L W x α ^ (-e) * brk d L W x β ^ (-e) * bB d L W x (y s)) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun s _ => by ring
              calc _ = Q * (((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k *
                    ((brk d L W x α ^ (-e) * brk d L W x β ^ (-e)) * ∑ s, bB d L W x (y s) *
                      ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j))) := by ring
                _ = _ := by rw [hsw]
    _ = Q * (((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * ∑ s, (∏ j ∈ Finset.univ.erase s,
          bB d L W (y s) (y j)) * ∑ x, brk d L W x α ^ (-e) * brk d L W x β ^ (-e) *
            bB d L W x (y s)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
        simp only [← Finset.mul_sum]
    _ ≤ Q * (((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * ∑ s, (∏ j ∈ Finset.univ.erase s,
          bB d L W (y s) (y j)) * Y) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h2 L W hW hWL α β (y s))
            (hΓs s)) (by positivity)) hQ0
    _ = ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * C₂ * logF L W *
          ((W : ℝ) ^ (-(a * d / 2)) * gammaB d L W y * ((W : ℝ) ^ (-b) * brk d L W α β ^ (-e)) *
            strongNorm d L W a b A₁ * strongNorm d L W a b A₂) := by
        have hG : (∑ s, ∏ j ∈ Finset.univ.erase s, bB d L W (y s) (y j)) = gammaB d L W y := rfl
        rw [← Finset.sum_mul, hG, hQ, hY]
        linear_combination (((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * C₂ * logF L W * gammaB d L W y *
          brk d L W α β ^ (-e) * strongNorm d L W a b A₁ * strongNorm d L W a b A₂) * hexp
    _ ≤ ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ k * C₂ * logF L W ^ (k + 2) *
          ((W : ℝ) ^ (-(a * d / 2)) * gammaB d L W y * ((W : ℝ) ^ (-b) * brk d L W α β ^ (-e)) *
            strongNorm d L W a b A₁ * strongNorm d L W a b A₂) := by
        gcongr
    _ = _ := by ring

end RBM8D
