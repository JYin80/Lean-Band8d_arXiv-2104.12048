module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import RBM8D.Basic.Lattice
public import RBM8D.Basic.Semicircle
public import RBM8D.Prob.StochDom
public import RBM8D.Kernel.Fourier
public import RBM8D.Kernel.Propagator
public import RBM8D.Kernel.Profile

@[expose] public section

/-!
# Dyadic shells in `p`

The smooth partition of the cube into a high part, dyadic shells and a core, with derivative
bounds and shell sums.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d : ℕ}

/-- The low-pass profile: `1` on `t ≤ 1`, `0` on `t ≥ 4`, smooth. -/
def lowPass (t : ℝ) : ℝ := Real.smoothTransition ((4 - t) / 3)

/-- `|p|² = Σ_i p_i²`. -/
def sqNorm (p : Fin d → ℝ) : ℝ := ∑ i, p i ^ 2

/-- The shell `|Wp| ∼ 2^{-j}`: `lowPass(4^j W²|p|²) - lowPass(4^{j+1} W²|p|²)`, supported on
`4^{-j-1} < W²|p|² < 4^{1-j}`. -/
def shellCut (W j : ℕ) (p : Fin d → ℝ) : ℝ :=
  lowPass (4 ^ j * (W : ℝ) ^ 2 * sqNorm p) - lowPass (4 ^ (j + 1) * (W : ℝ) ^ 2 * sqNorm p)

/-- The core `|Wp| ≲ 2^{-J}`: `lowPass(4^J W²|p|²)`. -/
def coreCut (W J : ℕ) (p : Fin d → ℝ) : ℝ := lowPass (4 ^ J * (W : ℝ) ^ 2 * sqNorm p)

/-- The high part `|Wp| ≳ 1`: `1 - lowPass(W²|p|²)`. -/
def highCut (W : ℕ) (p : Fin d → ℝ) : ℝ := 1 - lowPass ((W : ℝ) ^ 2 * sqNorm p)

/-- The number `J` of shells at `|m|² = a`: the least `J` with `4^J ≥ ⌈(1 - a)⁻¹⌉`. -/
def shellCount (a : ℝ) : ℕ := Nat.clog 4 ⌈(1 - a)⁻¹⌉₊

private theorem lowPass_eq_one {t : ℝ} (h : t ≤ 1) : lowPass t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem lowPass_eq_zero {t : ℝ} (h : 4 ≤ t) : lowPass t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem lowPass_nonneg (t : ℝ) : 0 ≤ lowPass t := Real.smoothTransition.nonneg _

private theorem lowPass_le_one (t : ℝ) : lowPass t ≤ 1 := Real.smoothTransition.le_one _

private theorem sqNorm_nonneg (p : Fin d → ℝ) : 0 ≤ sqNorm p :=
  Finset.sum_nonneg fun i _ => sq_nonneg (p i)

/-- A sum `∑_{j ∈ S} b^j` with `0 ≤ b ≤ 1/2` over an arbitrary finite set of exponents is at most
twice a common upper bound `c` of its terms. -/
private theorem sum_pow_le_two_mul_of_le_half {S : Finset ℕ} {b c : ℝ} (hb0 : 0 ≤ b)
    (hb : b ≤ 1 / 2) (hc : 0 ≤ c) (h : ∀ j ∈ S, b ^ j ≤ c) : ∑ j ∈ S, b ^ j ≤ 2 * c := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]; linarith
  set m := S.min' hne with hm
  set M := S.max' hne with hM
  have hsub : S ⊆ Finset.Ico m (M + 1) := by
    intro j hj
    rw [Finset.mem_Ico]
    exact ⟨S.min'_le j hj, Nat.lt_succ_of_le (S.le_max' j hj)⟩
  have hgeo : ∑ i ∈ Finset.range (M + 1 - m), b ^ i ≤ 2 := by
    calc ∑ i ∈ Finset.range (M + 1 - m), b ^ i
        ≤ ∑ i ∈ Finset.range (M + 1 - m), (1 / (2 : ℝ)) ^ i :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hb0 hb i
      _ ≤ 2 := sum_geometric_two_le _
  calc ∑ j ∈ S, b ^ j ≤ ∑ j ∈ Finset.Ico m (M + 1), b ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => pow_nonneg hb0 i
    _ = ∑ i ∈ Finset.range (M + 1 - m), b ^ (m + i) := Finset.sum_Ico_eq_sum_range _ _ _
    _ = b ^ m * ∑ i ∈ Finset.range (M + 1 - m), b ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_add b m i
    _ ≤ b ^ m * 2 := mul_le_mul_of_nonneg_left hgeo (pow_nonneg hb0 m)
    _ ≤ c * 2 := by nlinarith [h m (S.min'_mem hne), pow_nonneg hb0 m]
    _ = 2 * c := by ring

/-- `∑_{j ≤ n} b^j ≤ 2 b^n` for `b ≥ 2`. -/
private theorem sum_range_succ_pow_le {b : ℝ} (hb : 2 ≤ b) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), b ^ j ≤ 2 * b ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < b) n]

/-- A sum `∑_{j ∈ S} b^j` with `b ≥ 2` over an arbitrary finite set of exponents is at most
twice a common upper bound `c` of its terms. -/
private theorem sum_pow_le_two_mul_of_two_le {S : Finset ℕ} {b c : ℝ} (hb : 2 ≤ b)
    (hc : 0 ≤ c) (h : ∀ j ∈ S, b ^ j ≤ c) : ∑ j ∈ S, b ^ j ≤ 2 * c := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]; linarith
  have hsub : S ⊆ Finset.range (S.max' hne + 1) := by
    intro j hj
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (S.le_max' j hj)
  calc ∑ j ∈ S, b ^ j ≤ ∑ j ∈ Finset.range (S.max' hne + 1), b ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => pow_nonneg (by linarith) i
    _ ≤ 2 * b ^ S.max' hne := sum_range_succ_pow_le hb _
    _ ≤ 2 * c := by linarith [h _ (S.max'_mem hne)]

private theorem sqNorm_smul (c : ℝ) (p : Fin d → ℝ) : sqNorm (c • p) = c ^ 2 * sqNorm p := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

private theorem contDiff_sqNorm {n : WithTop ℕ∞} : ContDiff ℝ n (sqNorm : (Fin d → ℝ) → ℝ) :=
  ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ : Fin d => ℝ) i).pow 2

private theorem contDiff_lowPass : ContDiff ℝ (⊤ : ℕ∞) lowPass :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const 3)

/-- The profile `q ↦ lowPass(|q|²)` is smooth. -/
private theorem contDiff_lowPass_sqNorm :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin d → ℝ => lowPass (sqNorm q)) :=
  contDiff_lowPass.comp (contDiff_sqNorm)

/-- The profile `q ↦ lowPass(|q|²)` vanishes outside the closed ball of radius `2`. -/
private theorem hasCompactSupport_lowPass_sqNorm :
    HasCompactSupport (fun q : Fin d → ℝ => lowPass (sqNorm q)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) 2) fun q hq => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)] at hq
  rw [not_forall] at hq
  obtain ⟨i, hi⟩ := hq
  have h1 : (2 : ℝ) < |q i| := by simpa using hi
  have h2 : 4 < q i ^ 2 := by nlinarith [abs_nonneg (q i), sq_abs (q i)]
  have h3 : q i ^ 2 ≤ sqNorm q :=
    Finset.single_le_sum (f := fun i => q i ^ 2) (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)
  exact lowPass_eq_zero (by linarith)

/-- The profile `q ↦ lowPass(|c q|²)` rescaled by `c`. -/
private def lowPassScaled (c : ℝ) (q : Fin d → ℝ) : ℝ := lowPass (sqNorm (c • q))

/-- Derivatives of the rescaled profile of order `n` are bounded by `B |c|^n`, with `B` depending
only on `d` and `n`. -/
private theorem norm_iteratedFDeriv_lowPassScaled_le (d n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ℝ) (p : Fin d → ℝ),
      ‖iteratedFDeriv ℝ n (lowPassScaled c) p‖ ≤ B * |c| ^ n := by
  have hcd : ContDiff ℝ (n : WithTop ℕ∞) (fun q : Fin d → ℝ => lowPass (sqNorm q)) :=
    contDiff_lowPass_sqNorm.of_le (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := (hasCompactSupport_lowPass_sqNorm.iteratedFDeriv n).exists_bound_of_continuous
    (hcd.continuous_iteratedFDeriv le_rfl)
  refine ⟨B, (norm_nonneg _).trans (hB 0), fun c p => ?_⟩
  have h := congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) c hcd) p
  have e : lowPassScaled c = fun z : Fin d → ℝ => lowPass (sqNorm (c • z)) := rfl
  rw [e, h, norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _) (by positivity)

private theorem coreCut_eq (W J : ℕ) :
    coreCut (d := d) W J = lowPassScaled (2 ^ J * (W : ℝ)) := by
  funext p
  simp only [coreCut, lowPassScaled, sqNorm_smul]
  congr 1
  rw [mul_pow, ← pow_mul, mul_comm J 2, pow_mul]
  norm_num

private theorem shellCut_eq (W j : ℕ) :
    shellCut (d := d) W j = coreCut W j - coreCut W (j + 1) := rfl

private theorem highCut_eq (W : ℕ) :
    highCut (d := d) W = (fun _ => (1 : ℝ)) - lowPassScaled (W : ℝ) := by
  funext p
  simp [highCut, lowPassScaled, sqNorm_smul]

private theorem contDiff_lowPassScaled (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (lowPassScaled (d := d) c) :=
  contDiff_lowPass_sqNorm.comp (contDiff_id.const_smul c)

/-- The partition of unity on the cube: the high part, the shells `j < J` and the core at scale `J`
sum to `1`. This is the dyadic decomposition in `p` of the decay estimate [I, (1.17)]. -/
theorem shellCut_partition :
  ∀ {d : ℕ} (W J : ℕ) (p : Fin d → ℝ),
    highCut W p + ∑ j ∈ Finset.range J, shellCut W j p + coreCut W J p = 1 := by
  intro d W J p
  have h : ∑ j ∈ Finset.range J, shellCut W j p =
      lowPass (4 ^ 0 * (W : ℝ) ^ 2 * sqNorm p) - lowPass (4 ^ J * (W : ℝ) ^ 2 * sqNorm p) :=
    Finset.sum_range_sub' (fun j => lowPass (4 ^ j * (W : ℝ) ^ 2 * sqNorm p)) J
  rw [h]
  simp only [highCut, coreCut, pow_zero, one_mul]
  ring

/-- The shell `j` vanishes outside the open window `4^{-j-1} < W²|p|² < 4^{1-j}`. -/
theorem shellCut_support :
  ∀ {d : ℕ} (W j : ℕ) (p : Fin d → ℝ), shellCut W j p ≠ 0 →
    ((4 : ℝ) ^ (j + 1))⁻¹ < (W : ℝ) ^ 2 * sqNorm p ∧ (W : ℝ) ^ 2 * sqNorm p < 4 / 4 ^ j := by
  intro d W j p h
  have hu : 0 ≤ (W : ℝ) ^ 2 * sqNorm p := mul_nonneg (sq_nonneg _) (sqNorm_nonneg p)
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  have h4' : (4 : ℝ) ^ (j + 1) = 4 * 4 ^ j := by rw [pow_succ]; ring
  have e1 : (4 : ℝ) ^ j * (W : ℝ) ^ 2 * sqNorm p = 4 ^ j * ((W : ℝ) ^ 2 * sqNorm p) := by ring
  have e2 : (4 : ℝ) ^ (j + 1) * (W : ℝ) ^ 2 * sqNorm p =
      4 * (4 ^ j * ((W : ℝ) ^ 2 * sqNorm p)) := by rw [h4']; ring
  unfold shellCut at h
  rw [e1, e2] at h
  set x : ℝ := 4 ^ j * ((W : ℝ) ^ 2 * sqNorm p) with hx
  have hx0 : 0 ≤ x := mul_nonneg h4.le hu
  constructor
  · by_contra hc
    rw [not_lt] at hc
    have : x ≤ 1 / 4 := by
      have hc' : (W : ℝ) ^ 2 * sqNorm p ≤ ((4 : ℝ) * 4 ^ j)⁻¹ := by rw [← h4']; exact hc
      calc 4 ^ j * ((W : ℝ) ^ 2 * sqNorm p) ≤ 4 ^ j * ((4 * 4 ^ j)⁻¹) :=
            mul_le_mul_of_nonneg_left hc' h4.le
        _ = 1 / 4 := by field_simp
    exact h (by rw [lowPass_eq_one (by linarith), lowPass_eq_one (by linarith)]; ring)
  · by_contra hc
    rw [not_lt, div_le_iff₀ h4] at hc
    have hc' : 4 ≤ x := by rw [hx]; nlinarith
    exact h (by rw [lowPass_eq_zero hc', lowPass_eq_zero (by linarith)]; ring)

/-- Scale-uniform derivative bounds `‖∂ⁿ χ‖ ≤ C_n (2^j W)ⁿ` for the shell `j` and the core at scale
`j`, and `‖∂ⁿ χ‖ ≤ C_n Wⁿ` for the high part, with `C_n` depending only on `d` and `n`. -/
theorem norm_iteratedFDeriv_cut_le :
  ∀ (d n : ℕ), ∃ C : ℝ, ∀ (W j : ℕ) (p : Fin d → ℝ),
    ‖iteratedFDeriv ℝ n (shellCut (d := d) W j) p‖ ≤ C * (2 ^ j * (W : ℝ)) ^ n ∧
    ‖iteratedFDeriv ℝ n (coreCut (d := d) W j) p‖ ≤ C * (2 ^ j * (W : ℝ)) ^ n ∧
    ‖iteratedFDeriv ℝ n (highCut (d := d) W) p‖ ≤ C * (W : ℝ) ^ n := by
  intro d n
  obtain ⟨B, hB0, hB⟩ := norm_iteratedFDeriv_lowPassScaled_le d n
  refine ⟨(1 + 2 ^ n) * B + 1, fun W j p => ?_⟩
  have hc0 : (0 : ℝ) ≤ 2 ^ j * (W : ℝ) := by positivity
  have hcn : (0 : ℝ) ≤ (2 ^ j * (W : ℝ)) ^ n := pow_nonneg hc0 n
  have hCB : B ≤ (1 + 2 ^ n) * B + 1 := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
  have hdiff : ∀ c : ℝ, ContDiffAt ℝ (n : WithTop ℕ∞) (lowPassScaled (d := d) c) p := fun c =>
    ((contDiff_lowPassScaled c).of_le (by exact_mod_cast le_top)).contDiffAt
  have hcore : ∀ c : ℝ, ‖iteratedFDeriv ℝ n (lowPassScaled c) p‖ ≤ B * |c| ^ n := fun c => hB c p
  refine ⟨?_, ?_, ?_⟩
  · rw [shellCut_eq, coreCut_eq, coreCut_eq, iteratedFDeriv_sub_apply (hdiff _) (hdiff _)]
    have h2 : |(2 : ℝ) ^ (j + 1) * (W : ℝ)| ^ n = 2 ^ n * (2 ^ j * (W : ℝ)) ^ n := by
      rw [abs_of_nonneg (by positivity), pow_succ, mul_comm ((2 : ℝ) ^ j) 2, mul_assoc, mul_pow]
    calc _ ≤ ‖iteratedFDeriv ℝ n (lowPassScaled ((2 : ℝ) ^ j * (W : ℝ))) p‖ +
          ‖iteratedFDeriv ℝ n (lowPassScaled ((2 : ℝ) ^ (j + 1) * (W : ℝ))) p‖ := norm_sub_le _ _
      _ ≤ B * |(2 : ℝ) ^ j * (W : ℝ)| ^ n + B * |(2 : ℝ) ^ (j + 1) * (W : ℝ)| ^ n :=
          add_le_add (hcore _) (hcore _)
      _ = ((1 + 2 ^ n) * B) * (2 ^ j * (W : ℝ)) ^ n := by
          rw [h2, abs_of_nonneg hc0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hcn
  · rw [coreCut_eq]
    calc _ ≤ B * |(2 : ℝ) ^ j * (W : ℝ)| ^ n := hcore _
      _ ≤ _ := by
        rw [abs_of_nonneg hc0]
        exact mul_le_mul_of_nonneg_right hCB hcn
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [norm_iteratedFDeriv_zero]
      simp only [pow_zero, mul_one]
      have h1 := lowPass_nonneg ((W : ℝ) ^ 2 * sqNorm p)
      have h2 := lowPass_le_one ((W : ℝ) ^ 2 * sqNorm p)
      rw [Real.norm_eq_abs, abs_le]
      unfold highCut
      constructor <;> linarith
    · rw [highCut_eq, iteratedFDeriv_sub_apply contDiffAt_const (hdiff _),
        iteratedFDeriv_const_of_ne hn.ne']
      simp only [Pi.zero_apply, zero_sub, norm_neg]
      calc _ ≤ B * |(W : ℝ)| ^ n := hcore _
        _ ≤ _ := by
          rw [abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_right hCB (by positivity)

/-- For `0 ≤ a < 1` the number of shells `J = shellCount a` satisfies
`(1 - a)⁻¹ ≤ 4^J < 4((1 - a)⁻¹ + 1)`. -/
theorem shellCount_spec :
  ∀ (a : ℝ), 0 ≤ a → a < 1 →
    (1 - a)⁻¹ ≤ (4 : ℝ) ^ shellCount a ∧ (4 : ℝ) ^ shellCount a < 4 * ((1 - a)⁻¹ + 1) := by
  intro a ha0 ha1
  have hpos : 0 < 1 - a := by linarith
  have hx : 1 ≤ (1 - a)⁻¹ := one_le_inv₀ hpos |>.2 (by linarith)
  set x : ℝ := (1 - a)⁻¹ with hxdef
  set m : ℕ := ⌈x⌉₊ with hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le (by linarith) (Nat.le_ceil x)
    exact_mod_cast this
  have hxm : x ≤ m := Nat.le_ceil x
  have hmx : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hJ : m ≤ 4 ^ shellCount a := Nat.le_pow_clog (by norm_num) m
  have hJ' : (m : ℝ) ≤ (4 : ℝ) ^ shellCount a := by exact_mod_cast hJ
  refine ⟨hxm.trans hJ', ?_⟩
  rcases Nat.eq_zero_or_pos (shellCount a) with h0 | hpos'
  · rw [h0]; norm_num; linarith
  · have hlt : 4 ^ (shellCount a - 1) < m := by
      have h1 : 1 < m := by
        by_contra hc
        have : m = 1 := by omega
        have : shellCount a = 0 := by
          rw [shellCount, ← hm, this]; simp
        omega
      exact Nat.pow_pred_clog_lt_self (by norm_num) h1
    have hlt' : ((4 : ℝ) ^ (shellCount a - 1)) < m := by exact_mod_cast hlt
    have : (4 : ℝ) ^ shellCount a = 4 * 4 ^ (shellCount a - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; linarith

/-- The dyadic shell sum `∑_{j<J} 2^{-j(d-2)} (1 + t/2^j)^{-M} ≤ C (1 + t)^{-(d-2)}` for `d ≥ 3` and
`M > d - 2`, with `C` independent of `J` and `t ≥ 0`; it gives the decay `⟨x⟩^{-(d-2)}` of
[I, (1.17)]. -/
theorem sum_shell_le :
  ∀ (d M : ℕ) (hd : 3 ≤ d) (hM : d - 2 < M), ∃ C : ℝ, ∀ (J : ℕ) (t : ℝ), 0 ≤ t →
    ∑ j ∈ Finset.range J, (((2 : ℝ) ^ j) ^ (d - 2))⁻¹ * ((1 + t / 2 ^ j) ^ M)⁻¹ ≤
      C * ((1 + t) ^ (d - 2))⁻¹ := by
  intro d M hd hM
  refine ⟨4, fun J t ht => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, d - 2 = k := ⟨_, rfl⟩
  rw [hk] at hM ⊢
  have hk1 : 1 ≤ k := by omega
  obtain ⟨r, rfl⟩ : ∃ r, M = k + r := ⟨M - k, by omega⟩
  have hr : 1 ≤ r := by omega
  set s : ℝ := 1 + t with hsdef
  have hs : 1 ≤ s := by rw [hsdef]; linarith
  have hs0 : 0 < s := by linarith
  have hsk : 0 < s ^ k := pow_pos hs0 k
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range J) (fun j => (2 : ℝ) ^ j ≤ s)]
  have hA : ∑ j ∈ (Finset.range J).filter (fun j => (2 : ℝ) ^ j ≤ s),
      (((2 : ℝ) ^ j) ^ k)⁻¹ * ((1 + t / 2 ^ j) ^ (k + r))⁻¹ ≤ 2 * (s ^ k)⁻¹ := by
    have key : ∀ j ∈ (Finset.range J).filter (fun j => (2 : ℝ) ^ j ≤ s),
        (((2 : ℝ) ^ j) ^ k)⁻¹ * ((1 + t / 2 ^ j) ^ (k + r))⁻¹ ≤
          ((2 : ℝ) ^ r) ^ j * (s ^ (k + r))⁻¹ := by
      intro j _
      have h2 : (0 : ℝ) < 2 ^ j := by positivity
      have h21 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hlow : s / 2 ^ j ≤ 1 + t / 2 ^ j := by
        rw [hsdef, add_div]
        have : (1 : ℝ) / 2 ^ j ≤ 1 := by rw [div_le_one h2]; exact h21
        linarith
      have hpos : 0 < s / 2 ^ j := div_pos hs0 h2
      have hpow : (s / 2 ^ j) ^ (k + r) ≤ (1 + t / 2 ^ j) ^ (k + r) :=
        pow_le_pow_left₀ hpos.le hlow _
      have hinv : ((1 + t / 2 ^ j) ^ (k + r))⁻¹ ≤ ((s / 2 ^ j) ^ (k + r))⁻¹ :=
        inv_anti₀ (pow_pos hpos _) hpow
      calc (((2 : ℝ) ^ j) ^ k)⁻¹ * ((1 + t / 2 ^ j) ^ (k + r))⁻¹
          ≤ (((2 : ℝ) ^ j) ^ k)⁻¹ * ((s / 2 ^ j) ^ (k + r))⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = ((2 : ℝ) ^ r) ^ j * (s ^ (k + r))⁻¹ := by
            rw [div_pow, inv_div, ← pow_mul, ← pow_mul, ← pow_mul, pow_add]
            field_simp
            ring
    refine le_trans (Finset.sum_le_sum key) ?_
    rw [← Finset.sum_mul]
    have hbd : ∑ j ∈ (Finset.range J).filter (fun j => (2 : ℝ) ^ j ≤ s), ((2 : ℝ) ^ r) ^ j ≤
        2 * s ^ r := by
      refine sum_pow_le_two_mul_of_two_le ?_ (by positivity) fun j hj => ?_
      · calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
      · rw [← pow_mul, mul_comm, pow_mul]
        exact pow_le_pow_left₀ (by positivity) (Finset.mem_filter.mp hj).2 r
    calc (∑ j ∈ (Finset.range J).filter (fun j => (2 : ℝ) ^ j ≤ s), ((2 : ℝ) ^ r) ^ j) *
          (s ^ (k + r))⁻¹ ≤ (2 * s ^ r) * (s ^ (k + r))⁻¹ :=
          mul_le_mul_of_nonneg_right hbd (by positivity)
      _ = 2 * (s ^ k)⁻¹ := by
          rw [pow_add]; field_simp
  have hB : ∑ j ∈ (Finset.range J).filter (fun j => ¬ (2 : ℝ) ^ j ≤ s),
      (((2 : ℝ) ^ j) ^ k)⁻¹ * ((1 + t / 2 ^ j) ^ (k + r))⁻¹ ≤ 2 * (s ^ k)⁻¹ := by
    have key : ∀ j ∈ (Finset.range J).filter (fun j => ¬ (2 : ℝ) ^ j ≤ s),
        (((2 : ℝ) ^ j) ^ k)⁻¹ * ((1 + t / 2 ^ j) ^ (k + r))⁻¹ ≤ ((2 ^ k : ℝ)⁻¹) ^ j := by
      intro j _
      have h2 : (0 : ℝ) < 2 ^ j := by positivity
      have hb : (1 : ℝ) ≤ (1 + t / 2 ^ j) ^ (k + r) :=
        one_le_pow₀ (by have : 0 ≤ t / 2 ^ j := by positivity
                        linarith)
      have hinv : ((1 + t / 2 ^ j) ^ (k + r))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
      calc (((2 : ℝ) ^ j) ^ k)⁻¹ * ((1 + t / 2 ^ j) ^ (k + r))⁻¹
          ≤ (((2 : ℝ) ^ j) ^ k)⁻¹ * 1 := mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = ((2 ^ k : ℝ)⁻¹) ^ j := by
            rw [mul_one, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
    refine le_trans (Finset.sum_le_sum key) ?_
    refine sum_pow_le_two_mul_of_le_half (by positivity) ?_ (by positivity) fun j hj => ?_
    · have h2k : (2 : ℝ) ≤ 2 ^ k := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
      calc ((2 : ℝ) ^ k)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2k
        _ = 1 / 2 := by norm_num
    · have hgt : s < 2 ^ j := lt_of_not_ge (Finset.mem_filter.mp hj).2
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul]
      exact inv_anti₀ hsk (pow_le_pow_left₀ hs0.le hgt.le k)
  linarith

end RBM8D
