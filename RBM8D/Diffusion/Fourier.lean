import RBM8D.Diffusion.Defs
import RBM8D.Diffusion.ThetaM

/-!
# The symbol of `Θ^{(M)}` near `p = 0`

`symbolThetaMStmt` ([I, (1.33)] in quantified form): for `d ≥ 8` and `|p| ≤ W^{−1−δ}`,
`Θ̂^{(M)}(p) = r(E)(1 + u)/(η + W² p·𝒟_eff^{(M)} p + e)` with `|u| ≤ C(η + W²|p|²)` and
`|e| ≤ C(η² + W^{−d+τ}η + W³|p|³)`.

The proof writes `Θ̂^{(M)}(p) = |m|²Ŝ(p)/(1 − |m|²Ŝ(p)(1 + Σ̂(p)))`, multiplies numerator and
denominator by `η + Im m` (using `|m|²(η + Im m) = Im m`), and expands `Ŝ` and `Σ̂ = Σ_{l=4}^M Σ̂_l`
to second order in the phase `p·[x]_L`. The remainders are controlled by the moments of `S`
([I, (1.8)]), by the bound (1.26) on `Σ_l(0, x)` (third moment of `B²`, which is finite for
`d ≥ 8`) and by (1.27) for `Σ̂_l(0)`.
-/

noncomputable section

open scoped BigOperators
open Matrix Complex

namespace RBM8D

open Graphs

namespace ThetaMSymbol

/-! ## Lattice sums -/

private theorem sum_val_le (L : ℕ) [NeZero L] (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ t : ZMod L, f t.val ≤ ∑ k ∈ Finset.range L, f k := by
  rw [← Finset.sum_image (f := f) (g := ZMod.val) fun a _ b _ h => ZMod.val_injective L h]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hf k
  intro k hk
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hk
  exact Finset.mem_range.2 (ZMod.val_lt t)

private theorem sum_zdist_le (L : ℕ) [NeZero L] (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hg : Antitone g) : ∑ t : ZMod L, g (zdist L t) ≤ 2 * ∑ n ∈ Finset.range L, g n := by
  have hpt : ∀ t : ZMod L, g (zdist L t) ≤ g t.val + g (L - t.val) := by
    intro t
    unfold zdist
    rcases le_total t.val (L - t.val) with h | h
    · rw [min_eq_left h]; linarith [hg0 (L - t.val)]
    · rw [min_eq_right h]; linarith [hg0 t.val]
  have h1 := sum_val_le L g hg0
  have h2 : ∑ t : ZMod L, g (L - t.val) ≤ ∑ n ∈ Finset.range L, g n := by
    refine (sum_val_le L (fun k => g (L - k)) fun k => hg0 _).trans ?_
    rw [← Finset.sum_range_reflect (fun k => g (L - k)) L]
    refine Finset.sum_le_sum fun k hk => ?_
    have := Finset.mem_range.1 hk
    exact hg (by omega)
  calc ∑ t : ZMod L, g (zdist L t) ≤ ∑ t : ZMod L, (g t.val + g (L - t.val)) :=
        Finset.sum_le_sum fun t _ => hpt t
    _ = ∑ t : ZMod L, g t.val + ∑ t : ZMod L, g (L - t.val) := Finset.sum_add_distrib
    _ ≤ _ := by linarith

private theorem sum_inv_sq_le (W : ℝ) (hW : 1 ≤ W) (N : ℕ) :
    ∑ n ∈ Finset.range N, (((n : ℝ) + W) ^ 2)⁻¹ ≤ 2 / W - 2 / ((N : ℝ) + W) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h0 : 0 < (N : ℝ) + W := by positivity
    have h1 : 0 < (N : ℝ) + 1 + W := by positivity
    have key : (((N : ℝ) + W) ^ 2)⁻¹ ≤ 2 / ((N : ℝ) + W) - 2 / ((N : ℝ) + 1 + W) := by
      have e : 2 / ((N : ℝ) + W) - 2 / ((N : ℝ) + 1 + W) =
          2 / (((N : ℝ) + W) * ((N : ℝ) + 1 + W)) := by
        field_simp
        ring
      rw [e, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

private theorem sum_zdist_inv_sq (L : ℕ) [NeZero L] (W : ℝ) (hW : 1 ≤ W) :
    ∑ t : ZMod L, (((zdist L t : ℝ) + W) ^ 2)⁻¹ ≤ 4 / W := by
  have hW0 : 0 < W := by linarith
  refine (sum_zdist_le L (fun n => (((n : ℝ) + W) ^ 2)⁻¹) (fun n => by positivity)
    fun a b hab => ?_).trans ?_
  · have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only
    gcongr
  · have := sum_inv_sq_le W hW L
    have : 0 ≤ 2 / ((L : ℝ) + W) := by positivity
    have : 4 / W = 2 * (2 / W) := by ring
    linarith

private theorem sum_zdist_inv (L : ℕ) [NeZero L] (W : ℝ) (hW : 1 ≤ W) :
    ∑ t : ZMod L, ((zdist L t : ℝ) + W)⁻¹ ≤ 2 + 2 * Real.log L := by
  have hW0 : 0 < W := by linarith
  refine (sum_zdist_le L (fun n => ((n : ℝ) + W)⁻¹) (fun n => by positivity)
    fun a b hab => ?_).trans ?_
  · have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only
    gcongr
  · have hH : ∑ k ∈ Finset.range L, ((k : ℝ) + 1)⁻¹ ≤ 1 + Real.log L := by
      have h := harmonic_le_one_add_log L
      have e : ((harmonic L : ℚ) : ℝ) = ∑ k ∈ Finset.range L, ((k : ℝ) + 1)⁻¹ := by
        simp [harmonic]
      rw [e] at h
      exact h
    have : ∑ n ∈ Finset.range L, ((n : ℝ) + W)⁻¹ ≤ ∑ k ∈ Finset.range L, ((k : ℝ) + 1)⁻¹ :=
      Finset.sum_le_sum fun n _ => inv_anti₀ (by positivity) (by linarith)
    linarith

/-- `Σ_x (‖x‖_L + W)^{−jd} ≤ (Σ_{t ∈ Z_L} (‖t‖_L + W)^{−j})^d`. -/
private theorem sum_pow_le (d L : ℕ) [NeZero L] (W : ℝ) (hW : 1 ≤ W) (j : ℕ) :
    ∑ x : Zd d L, (((zdistInf d L x : ℝ) + W) ^ (j * d))⁻¹ ≤
      (∑ t : ZMod L, (((zdist L t : ℝ) + W) ^ j)⁻¹) ^ d := by
  have hW0 : 0 < W := by linarith
  set h : ZMod L → ℝ := fun t => (((zdist L t : ℝ) + W) ^ j)⁻¹ with hh
  have hpt : ∀ x : Zd d L, (((zdistInf d L x : ℝ) + W) ^ (j * d))⁻¹ ≤ ∏ i, h (x i) := by
    intro x
    simp only [hh]
    rw [Finset.prod_inv_distrib]
    refine inv_anti₀ (Finset.prod_pos fun i _ => by positivity) ?_
    calc ∏ i, ((zdist L (x i) : ℝ) + W) ^ j ≤ ∏ _i : Fin d, ((zdistInf d L x : ℝ) + W) ^ j := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
          have : (zdist L (x i) : ℝ) ≤ zdistInf d L x := by
            exact_mod_cast zdist_le_zdistInf d L x i
          gcongr
      _ = ((zdistInf d L x : ℝ) + W) ^ (j * d) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  calc ∑ x : Zd d L, (((zdistInf d L x : ℝ) + W) ^ (j * d))⁻¹ ≤ ∑ x : Zd d L, ∏ i, h (x i) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∏ _i : Fin d, ∑ t : ZMod L, h t := by
        rw [← Finset.sum_prod_piFinset (Finset.univ : Finset (ZMod L)) fun _ t => h t,
          Fintype.piFinset_univ]
    _ = (∑ t : ZMod L, h t) ^ d := by simp

/-! ## The phase `p·[x]_L` and the expansion of `cos` -/

/-- The phase `t_x = p·[x]_L` at `p = 2πk/L`. -/
private def phase {d L : ℕ} (k x : Zd d L) : ℝ := inner ℝ (zfreq k) (zrep x)

private theorem zchar_eq_phase {d L : ℕ} [NeZero L] (k x : Zd d L) :
    zchar k x = cexp ((phase k x : ℂ) * I) := by
  rw [zchar_eq_cexp, phase, mul_comm]

private theorem zchar_neg_mul {d L : ℕ} [NeZero L] (k x : Zd d L) :
    zchar k (-x) * zchar k x = 1 := by
  rw [← zchar_add, neg_add_cancel]
  simp [zchar]

/-- For an even `f`, `Σ_x f(x) e^{i p·x} = Σ_x f(x) cos t_x`. -/
private theorem sum_even_eq {d L : ℕ} [NeZero L] (f : Zd d L → ℂ) (hf : ∀ x, f (-x) = f x)
    (k : Zd d L) : ∑ x, f x * zchar k x = ∑ x, f x * (Real.cos (phase k x) : ℂ) := by
  have h1 : ∑ x, f x * zchar k x = ∑ x, f x * zchar k (-x) :=
    Fintype.sum_equiv (Equiv.neg _) _ _ fun x => by simp [hf]
  have hc : ∀ x, zchar k x + zchar k (-x) = 2 * (Real.cos (phase k x) : ℂ) := by
    intro x
    have hn : zchar k (-x) = cexp (-((phase k x : ℂ) * I)) := by
      rw [Complex.exp_neg, ← zchar_eq_phase]
      exact eq_inv_of_mul_eq_one_left (zchar_neg_mul k x)
    rw [hn, zchar_eq_phase, Complex.ofReal_cos, Complex.cos]
    ring_nf
  have h2 : 2 * ∑ x, f x * zchar k x = 2 * ∑ x, f x * (Real.cos (phase k x) : ℂ) := by
    calc 2 * ∑ x, f x * zchar k x = ∑ x, f x * zchar k x + ∑ x, f x * zchar k (-x) := by
          rw [← h1]; ring
      _ = ∑ x, f x * (zchar k x + zchar k (-x)) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by rw [hc]; ring
  exact mul_left_cancel₀ two_ne_zero h2

private theorem abs_cos_sub_one_le (t : ℝ) : |Real.cos t - 1| ≤ t ^ 2 / 2 := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := t)
  have h2 := Real.cos_le_one t
  rw [abs_of_nonpos (by linarith)]
  linarith

private theorem abs_cos_taylor_le (t : ℝ) : |Real.cos t - 1 + t ^ 2 / 2| ≤ |t| ^ 3 := by
  rcases le_or_gt |t| 1 with h | h
  · have h1 := Real.cos_bound h
    have e : Real.cos t - 1 + t ^ 2 / 2 = Real.cos t - (1 - t ^ 2 / 2) := by ring
    rw [e]
    refine h1.trans ?_
    have h0 := abs_nonneg t
    have : |t| ^ 4 ≤ |t| ^ 3 := pow_le_pow_of_le_one h0 h (by norm_num)
    nlinarith [pow_nonneg h0 3]
  · have h1 := abs_cos_sub_one_le t
    have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    calc |Real.cos t - 1 + t ^ 2 / 2| ≤ |Real.cos t - 1| + |t ^ 2 / 2| := abs_add_le _ _
      _ ≤ t ^ 2 / 2 + t ^ 2 / 2 := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)]; linarith
      _ = |t| ^ 2 := by rw [ht2]; ring
      _ ≤ |t| ^ 3 := pow_le_pow_right₀ h.le (by norm_num)

/-- `|t_x| ≤ d |p| ‖x‖_L`. -/
private theorem abs_phase_le {d L : ℕ} [NeZero L] (k x : Zd d L) :
    |phase k x| ≤ ‖zfreq k‖ * (d * (zdistInf d L x : ℝ)) := by
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hi : ∀ i, ‖(zrep x).ofLp i‖ ^ 2 ≤ (zdistInf d L x : ℝ) ^ 2 := by
    intro i
    have h1 : ‖(zrep x).ofLp i‖ = (zdist L (x i) : ℝ) := by
      simp only [zrep, Real.norm_eq_abs, zdist_eq_natAbs_valMinAbs, Nat.cast_natAbs,
        Int.cast_abs]
    rw [h1]
    have : (zdist L (x i) : ℝ) ≤ zdistInf d L x := by exact_mod_cast zdist_le_zdistInf d L x i
    gcongr
  calc ∑ i, ‖(zrep x).ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, (zdistInf d L x : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => hi i
    _ = d * (zdistInf d L x : ℝ) ^ 2 := by simp
    _ ≤ ((d : ℝ) * zdistInf d L x) ^ 2 := by
        have : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h
            nlinarith
        nlinarith [sq_nonneg (zdistInf d L x : ℝ)]

/-- `|Σ f cos t − Σ f| ≤ Σ |f| t²/2` and `|Σ f cos t − Σ f + Σ f t²/2| ≤ Σ |f| |t|³`. -/
private theorem cos_sum_bounds {d L : ℕ} [NeZero L] (f : Zd d L → ℂ) (k : Zd d L) :
    ‖∑ x, f x * (Real.cos (phase k x) : ℂ) - ∑ x, f x‖ ≤
      ∑ x, ‖f x‖ * (phase k x ^ 2 / 2) ∧
    ‖∑ x, f x * (Real.cos (phase k x) : ℂ) - ∑ x, f x +
        ∑ x, f x * ((phase k x ^ 2 / 2 : ℝ) : ℂ)‖ ≤ ∑ x, ‖f x‖ * |phase k x| ^ 3 := by
  constructor
  · have e : ∑ x, f x * (Real.cos (phase k x) : ℂ) - ∑ x, f x =
        ∑ x, f x * ((Real.cos (phase k x) - 1 : ℝ) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by push_cast; ring
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_cos_sub_one_le _) (norm_nonneg _)
  · have e : ∑ x, f x * (Real.cos (phase k x) : ℂ) - ∑ x, f x +
        ∑ x, f x * ((phase k x ^ 2 / 2 : ℝ) : ℂ) =
        ∑ x, f x * ((Real.cos (phase k x) - 1 + phase k x ^ 2 / 2 : ℝ) : ℂ) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by push_cast; ring
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_cos_taylor_le _) (norm_nonneg _)

/-- `Σ |f| t²/2 ≤ (d²|p|²/2) Σ |f| ‖x‖_L²` and `Σ |f| |t|³ ≤ d³|p|³ Σ |f| ‖x‖_L³`. -/
private theorem phase_sum_bounds {d L : ℕ} [NeZero L] (f : Zd d L → ℂ) (k : Zd d L) :
    ∑ x, ‖f x‖ * (phase k x ^ 2 / 2) ≤
      (d : ℝ) ^ 2 * ‖zfreq k‖ ^ 2 / 2 * ∑ x, ‖f x‖ * (zdistInf d L x : ℝ) ^ 2 ∧
    ∑ x, ‖f x‖ * |phase k x| ^ 3 ≤
      (d : ℝ) ^ 3 * ‖zfreq k‖ ^ 3 * ∑ x, ‖f x‖ * (zdistInf d L x : ℝ) ^ 3 := by
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h := abs_phase_le k x
    have h2 : phase k x ^ 2 ≤ (‖zfreq k‖ * (d * (zdistInf d L x : ℝ))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have := norm_nonneg (f x)
    calc ‖f x‖ * (phase k x ^ 2 / 2) ≤ ‖f x‖ * ((‖zfreq k‖ * (d * (zdistInf d L x : ℝ))) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) this
      _ = _ := by ring
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h := abs_phase_le k x
    have h3 : |phase k x| ^ 3 ≤ (‖zfreq k‖ * (d * (zdistInf d L x : ℝ))) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) h 3
    calc ‖f x‖ * |phase k x| ^ 3 ≤ ‖f x‖ * (‖zfreq k‖ * (d * (zdistInf d L x : ℝ))) ^ 3 :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = _ := by ring

/-! ## Moments of `S` and of `B²` -/

/-- `(a + b)^n ≤ 2^n (a^n + b^n)` for `a, b ≥ 0`. -/
private theorem add_pow_le_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rcases le_total a b with h | h
  · calc (a + b) ^ n ≤ (2 * b) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * b ^ n := mul_pow _ _ _
      _ ≤ _ := by have := pow_nonneg ha n; nlinarith
  · calc (a + b) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ _ := by have := pow_nonneg hb n; nlinarith

/-- The moments of `S` ([I, (1.8)]): `Σ_x |S_{0x}| ‖x‖_L^k ≤ C W^k` on `adm(c₀, c₁)`. -/
private theorem moment_S (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → 1 ≤ W →
      ∑ x : Zd d L, |Smat P.ψ W L 0 x| * (zdistInf d L x : ℝ) ^ k ≤ C * (W : ℝ) ^ k := by
  obtain ⟨C₀, hC₀⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨C₁, hC₁⟩ := subpoly_adm d P c₀ c₁ hc₀ (k + 2 * d)
  set n := k + 2 * d with hn
  set K : ℝ := 2 ^ n * (|C₀| + |C₁|) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * 4 ^ d, by positivity, fun W L _ hadm hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have hpt : ∀ x : Zd d L, |Smat P.ψ W L 0 x| * (zdistInf d L x : ℝ) ^ k ≤
      K * (W : ℝ) ^ (k + d) * (((zdistInf d L x : ℝ) + W) ^ (2 * d))⁻¹ := by
    intro x
    set ρ : ℝ := (zdistInf d L x : ℝ) with hρdef
    have hf : |Smat P.ψ W L 0 x| = |fWL P.ψ W L (-x)| := by simp [Smat]
    have hρ : (zdistInf d L (-x) : ℝ) = ρ := by rw [zdistInf_neg]
    have h0 := hC₀ W L hadm (-x)
    have h1 := hC₁ W L hadm (-x)
    rw [hρ, ← hf] at h0 h1
    set f := |Smat P.ψ W L 0 x| with hfdef
    have hρ0 : 0 ≤ ρ := Nat.cast_nonneg _
    have hy : 0 < ρ + W := by linarith
    have hf0 : 0 ≤ f := abs_nonneg _
    have e0 : f * (W : ℝ) ^ d ≤ |C₀| := by
      rw [pow_zero, one_mul, le_div_iff₀ hWd] at h0
      exact h0.trans (le_abs_self _)
    have e1 : ρ ^ n * f * (W : ℝ) ^ d ≤ |C₁| * (W : ℝ) ^ n := by
      rw [div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hWd] at h1
      have : C₁ * (W : ℝ) ^ n ≤ |C₁| * (W : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      linarith
    have hA : f * (ρ + W) ^ n * (W : ℝ) ^ d ≤ K * (W : ℝ) ^ n := by
      have hmax := add_pow_le_two ρ W hρ0 hW0.le n
      have hWn : (0 : ℝ) ≤ (W : ℝ) ^ n := by positivity
      calc f * (ρ + W) ^ n * (W : ℝ) ^ d ≤ f * (2 ^ n * (ρ ^ n + (W : ℝ) ^ n)) * (W : ℝ) ^ d := by
            gcongr
        _ = 2 ^ n * (ρ ^ n * f * (W : ℝ) ^ d + (W : ℝ) ^ n * (f * (W : ℝ) ^ d)) := by ring
        _ ≤ 2 ^ n * (|C₁| * (W : ℝ) ^ n + (W : ℝ) ^ n * |C₀|) := by gcongr
        _ = K * (W : ℝ) ^ n := by rw [hK]; ring
    have hyk : ρ ^ k ≤ (ρ + W) ^ k := pow_le_pow_left₀ hρ0 (by linarith) k
    have hyn : (ρ + W) ^ n = (ρ + W) ^ k * (ρ + W) ^ (2 * d) := by rw [hn, pow_add]
    have hy2 : 0 < (ρ + W) ^ (2 * d) := by positivity
    have hWn : (W : ℝ) ^ n = (W : ℝ) ^ (k + d) * (W : ℝ) ^ d := by
      rw [hn, ← pow_add]; ring_nf
    rw [hyn, hWn] at hA
    have hB : f * (ρ + W) ^ k * (ρ + W) ^ (2 * d) ≤ K * (W : ℝ) ^ (k + d) := by
      have := le_of_mul_le_mul_right (by nlinarith : f * ((ρ + W) ^ k * (ρ + W) ^ (2 * d)) *
        (W : ℝ) ^ d ≤ K * (W : ℝ) ^ (k + d) * (W : ℝ) ^ d) hWd
      linarith
    calc f * ρ ^ k ≤ f * (ρ + W) ^ k := mul_le_mul_of_nonneg_left hyk hf0
      _ = f * (ρ + W) ^ k * (ρ + W) ^ (2 * d) * ((ρ + W) ^ (2 * d))⁻¹ := by
          field_simp
      _ ≤ K * (W : ℝ) ^ (k + d) * ((ρ + W) ^ (2 * d))⁻¹ :=
          mul_le_mul_of_nonneg_right hB (by positivity)
  have hsum := sum_pow_le d L W hW1 2
  have h4 := sum_zdist_inv_sq L W hW1
  calc ∑ x : Zd d L, |Smat P.ψ W L 0 x| * (zdistInf d L x : ℝ) ^ k
      ≤ ∑ x : Zd d L, K * (W : ℝ) ^ (k + d) * (((zdistInf d L x : ℝ) + W) ^ (2 * d))⁻¹ :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = K * (W : ℝ) ^ (k + d) * ∑ x : Zd d L, (((zdistInf d L x : ℝ) + W) ^ (2 * d))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ K * (W : ℝ) ^ (k + d) * (4 / W) ^ d := by
        gcongr
        exact hsum.trans (pow_le_pow_left₀ (Finset.sum_nonneg fun t _ => by positivity) h4 d)
    _ = K * 4 ^ d * (W : ℝ) ^ k := by
        rw [div_pow, pow_add]; field_simp

/-- `‖x‖_L^k B_{0x}² ≤ W^{k−d} (‖x‖_L + W)^{−d}` for `k + 4 ≤ d`. -/
private theorem moment_B2_pt (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (k : ℕ) (hk : k + 4 ≤ d)
    (x : Zd d L) :
    (zdistInf d L x : ℝ) ^ k * bB d L W 0 x ^ 2 ≤
      (W : ℝ) ^ ((k : ℝ) - d) * (((zdistInf d L x : ℝ) + W) ^ (1 * d))⁻¹ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set ρ : ℝ := (zdistInf d L x : ℝ) with hρdef
  have hρ0 : 0 ≤ ρ := Nat.cast_nonneg _
  have hy : 0 < ρ + W := by linarith
  have hb : bB d L W 0 x = (W : ℝ) ^ (-2 : ℝ) * (ρ + W) ^ (2 - (d : ℝ)) := by
    simp only [bB, zero_sub, zdistInf_neg, hρdef]
  have hk' : (k : ℝ) + 4 ≤ d := by exact_mod_cast hk
  have e2 : bB d L W 0 x ^ 2 = (W : ℝ) ^ (-4 : ℝ) * (ρ + W) ^ (4 - 2 * (d : ℝ)) := by
    rw [hb, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast ((ρ + W) ^ (2 - (d : ℝ))),
      ← Real.rpow_mul hW0.le, ← Real.rpow_mul hy.le]
    congr 2 <;> push_cast <;> ring
  have e3 : (ρ + W) ^ (k : ℝ) * (ρ + W) ^ (4 - 2 * (d : ℝ)) =
      (ρ + W) ^ ((k : ℝ) + 4 - d) * (ρ + W) ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add hy, ← Real.rpow_add hy]; ring_nf
  have e4 : (ρ + W) ^ ((k : ℝ) + 4 - d) ≤ (W : ℝ) ^ ((k : ℝ) + 4 - d) :=
    Real.rpow_le_rpow_of_nonpos hW0 (by linarith) (by linarith)
  have e5 : (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ ((k : ℝ) + 4 - d) = (W : ℝ) ^ ((k : ℝ) - d) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have e6 : (ρ + W) ^ (-(d : ℝ)) = ((ρ + W) ^ (1 * d))⁻¹ := by
    rw [Real.rpow_neg hy.le, Real.rpow_natCast, one_mul]
  have hyk : ρ ^ k ≤ (ρ + W) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]; exact pow_le_pow_left₀ hρ0 (by linarith) k
  rw [e2]
  calc ρ ^ k * ((W : ℝ) ^ (-4 : ℝ) * (ρ + W) ^ (4 - 2 * (d : ℝ)))
      ≤ (ρ + W) ^ (k : ℝ) * ((W : ℝ) ^ (-4 : ℝ) * (ρ + W) ^ (4 - 2 * (d : ℝ))) :=
        mul_le_mul_of_nonneg_right hyk (by positivity)
    _ = (W : ℝ) ^ (-4 : ℝ) * ((ρ + W) ^ ((k : ℝ) + 4 - d) * (ρ + W) ^ (-(d : ℝ))) := by
        rw [← e3]; ring
    _ ≤ (W : ℝ) ^ (-4 : ℝ) * ((W : ℝ) ^ ((k : ℝ) + 4 - d) * (ρ + W) ^ (-(d : ℝ))) := by
        gcongr
    _ = (W : ℝ) ^ ((k : ℝ) - d) * ((ρ + W) ^ (1 * d))⁻¹ := by
        rw [← e6, ← e5]; ring

/-- `Σ_x |Σ_{l=4}^M g_l(x)| ‖x‖_L^k ≤ M A W^{k−d} (2 + 2 log L)^d` when
`|g_l(x)| ≤ A W^{−(l−4)d/2} B_{0x}² + D_l 1_{x=0}` for `4 ≤ l ≤ M`, `1 ≤ k`, `k + 4 ≤ d`. -/
private theorem moment_sig (d L W M : ℕ) [NeZero L] (hW : 1 ≤ W) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k + 4 ≤ d) (A : ℝ) (hA : 0 ≤ A) (g : ℕ → Zd d L → ℂ) (D : ℕ → ℝ)
    (hg : ∀ l, 4 ≤ l → l ≤ M → ∀ x, ‖g l x‖ ≤
      A * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
        (if x = 0 then D l else 0)) :
    ∑ x : Zd d L, ‖∑ l ∈ Finset.Icc 4 M, g l x‖ * (zdistInf d L x : ℝ) ^ k ≤
      M * A * (W : ℝ) ^ ((k : ℝ) - d) * (2 + 2 * Real.log L) ^ d := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hcard : ((Finset.Icc 4 M).card : ℝ) ≤ M := by
    rw [Nat.card_Icc]; exact_mod_cast (by omega : M + 1 - 4 ≤ M)
  have hpt : ∀ x : Zd d L, ‖∑ l ∈ Finset.Icc 4 M, g l x‖ * (zdistInf d L x : ℝ) ^ k ≤
      M * A * ((W : ℝ) ^ ((k : ℝ) - d) * (((zdistInf d L x : ℝ) + W) ^ (1 * d))⁻¹) := by
    intro x
    have hρk : 0 ≤ (zdistInf d L x : ℝ) ^ k := by positivity
    have hB := moment_B2_pt d L W hW k hk x
    have hl : ∀ l ∈ Finset.Icc 4 M, ‖g l x‖ * (zdistInf d L x : ℝ) ^ k ≤
        A * ((zdistInf d L x : ℝ) ^ k * bB d L W 0 x ^ 2) := by
      intro l hl
      obtain ⟨hl4, hlM⟩ := Finset.mem_Icc.1 hl
      have h1 := hg l hl4 hlM x
      have hw : (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos hW1 ?_
        have : (4 : ℝ) ≤ l := by exact_mod_cast hl4
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith
      have hite : (if x = 0 then D l else 0) * (zdistInf d L x : ℝ) ^ k = 0 := by
        split_ifs with hx
        · rw [hx]
          have : zdistInf d L (0 : Zd d L) = 0 := (zdistInf_eq_zero_iff d L).2 rfl
          rw [this]; simp; omega
        · simp
      have hb0 : 0 ≤ bB d L W 0 x ^ 2 := by positivity
      calc ‖g l x‖ * (zdistInf d L x : ℝ) ^ k
          ≤ (A * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
              (if x = 0 then D l else 0)) * (zdistInf d L x : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h1 hρk
        _ = A * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 *
              (zdistInf d L x : ℝ) ^ k := by rw [add_mul, hite, add_zero]
        _ ≤ A * 1 * bB d L W 0 x ^ 2 * (zdistInf d L x : ℝ) ^ k := by gcongr
        _ = _ := by ring
    calc ‖∑ l ∈ Finset.Icc 4 M, g l x‖ * (zdistInf d L x : ℝ) ^ k
        ≤ (∑ l ∈ Finset.Icc 4 M, ‖g l x‖) * (zdistInf d L x : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) hρk
      _ = ∑ l ∈ Finset.Icc 4 M, ‖g l x‖ * (zdistInf d L x : ℝ) ^ k := Finset.sum_mul _ _ _
      _ ≤ ∑ _l ∈ Finset.Icc 4 M, A * ((zdistInf d L x : ℝ) ^ k * bB d L W 0 x ^ 2) :=
          Finset.sum_le_sum hl
      _ = (Finset.Icc 4 M).card * (A * ((zdistInf d L x : ℝ) ^ k * bB d L W 0 x ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * (A * ((W : ℝ) ^ ((k : ℝ) - d) * (((zdistInf d L x : ℝ) + W) ^ (1 * d))⁻¹)) := by
          gcongr
      _ = _ := by ring
  have hsum := sum_pow_le d L W hW1 1
  simp only [pow_one, one_mul] at hsum
  have h2 := sum_zdist_inv L W hW1
  calc ∑ x : Zd d L, ‖∑ l ∈ Finset.Icc 4 M, g l x‖ * (zdistInf d L x : ℝ) ^ k
      ≤ ∑ x : Zd d L, M * A * ((W : ℝ) ^ ((k : ℝ) - d) *
          (((zdistInf d L x : ℝ) + W) ^ (1 * d))⁻¹) := Finset.sum_le_sum fun x _ => hpt x
    _ = M * A * (W : ℝ) ^ ((k : ℝ) - d) *
          ∑ x : Zd d L, (((zdistInf d L x : ℝ) + W) ^ (1 * d))⁻¹ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ M * A * (W : ℝ) ^ ((k : ℝ) - d) * (2 + 2 * Real.log L) ^ d := by
        rw [one_mul]
        gcongr
        exact hsum.trans (pow_le_pow_left₀ (Finset.sum_nonneg fun t _ => by positivity) h2 d)

/-- For `d ≥ 8` and `c > 0`, `M L^c (2 + 2 log L)^d ≤ L^{cd}` for all large `L`. -/
private theorem slack (d : ℕ) (hd : 8 ≤ d) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L →
      M * (L : ℝ) ^ c * (2 + 2 * Real.log L) ^ d ≤ (L : ℝ) ^ (c * d) := by
  set K₀ : ℝ := 2 + 8 / c with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨max 1 ⌈(M * K₀ ^ d) ^ c⁻¹⌉₊, fun L hL => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_left _ _) hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hlog : 2 + 2 * Real.log L ≤ K₀ * (L : ℝ) ^ (c / 4) := by
    have h1 := Real.log_le_rpow_div hL0.le (by positivity : 0 < c / 4)
    have h2 : (1 : ℝ) ≤ (L : ℝ) ^ (c / 4) := Real.one_le_rpow hL1 (by positivity)
    have e : (L : ℝ) ^ (c / 4) / (c / 4) = 4 / c * (L : ℝ) ^ (c / 4) := by field_simp
    rw [e] at h1
    rw [hK₀]
    have e2 : (2 + 8 / c) * (L : ℝ) ^ (c / 4) = 2 * (L : ℝ) ^ (c / 4) +
        2 * (4 / c * (L : ℝ) ^ (c / 4)) := by ring
    rw [e2]
    linarith
  have hlog0 : 0 ≤ 2 + 2 * Real.log L := by linarith [Real.log_nonneg hL1]
  have hpow : (2 + 2 * Real.log L) ^ d ≤ K₀ ^ d * (L : ℝ) ^ (c * d / 4) := by
    calc (2 + 2 * Real.log L) ^ d ≤ (K₀ * (L : ℝ) ^ (c / 4)) ^ d :=
          pow_le_pow_left₀ hlog0 hlog d
      _ = K₀ ^ d * (L : ℝ) ^ (c * d / 4) := by
          rw [mul_pow, ← Real.rpow_natCast ((L : ℝ) ^ (c / 4)), ← Real.rpow_mul hL0.le]
          ring_nf
  have hMK : M * K₀ ^ d ≤ (L : ℝ) ^ c := by
    have h1 : (M * K₀ ^ d) ^ c⁻¹ ≤ (L : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hL)
    have := Real.rpow_le_rpow (by positivity) h1 hc.le
    rwa [Real.rpow_inv_rpow (by positivity) hc.ne'] at this
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  calc M * (L : ℝ) ^ c * (2 + 2 * Real.log L) ^ d
      ≤ M * (L : ℝ) ^ c * (K₀ ^ d * (L : ℝ) ^ (c * d / 4)) := by gcongr
    _ = (M * K₀ ^ d) * ((L : ℝ) ^ c * (L : ℝ) ^ (c * d / 4)) := by ring
    _ ≤ (L : ℝ) ^ c * ((L : ℝ) ^ c * (L : ℝ) ^ (c * d / 4)) := by gcongr
    _ = (L : ℝ) ^ (2 * c + c * d / 4) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; ring_nf
    _ ≤ (L : ℝ) ^ (c * d) := Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)

/-! ## The semicircle law -/

/-- `Im m = |m|² (η + Im m)`, the imaginary part of `1/m = −z − m` ([I, (1.15)]). -/
private theorem im_msc_eq (z : ℂ) : (msc z).im = ‖msc z‖ ^ 2 * (z.im + (msc z).im) := by
  have h := congrArg Complex.im (msc_add_eq_neg_inv z)
  simp only [Complex.add_im, Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at h
  have hn : Complex.normSq (msc z) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; exact msc_ne_zero z
  rw [← Complex.normSq_eq_norm_sq, add_comm z.im, h]
  field_simp

/-- `|Im m(E + iη) − r(E)| ≤ η / r(E)` for `|E| < 2`, `η > 0`: from
`(m − m_E)(m + m_E + E) = −iη m` and `Im (m + m_E + E) ≥ Im m_E = r(E)`. -/
private theorem msc_im_sub_le {z : ℂ} (hz : 0 < z.im) (hE : |z.re| < 2) :
    |(msc z).im - rE z.re| ≤ z.im / rE z.re := by
  set m := msc z with hm
  set e := mE z.re with he
  have hre : e.im = rE z.re := by rw [he, mE_im, rE]
  have hm1 : ‖m‖ < 1 := norm_msc_lt_one hz
  have hei : 0 < e.im := mE_im_pos hE
  have hmz := msc_mul z
  have hme := mE_mul hE.le
  rw [← hm] at hmz
  rw [← he] at hme
  have hzE : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  have key : (m - e) * (m + e + (z.re : ℂ)) = -((z.im : ℂ) * I) * m := by
    rw [hzE] at hmz
    linear_combination hmz - hme
  have hmi : 0 < m.im := msc_im_pos hz
  have hq : e.im ≤ ‖m + e + (z.re : ℂ)‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
    rw [abs_of_pos (by linarith)]
    linarith
  have h1 := congrArg norm key
  rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hz] at h1
  have h2 : ‖m - e‖ ≤ z.im / e.im := by
    rw [le_div_iff₀ hei]
    have : ‖m - e‖ * e.im ≤ ‖m - e‖ * ‖m + e + (z.re : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hq (norm_nonneg _)
    nlinarith [norm_nonneg m]
  rw [← hre]
  refine le_trans ?_ h2
  have := Complex.abs_im_le_norm (m - e)
  simpa using this

/-- `r(E) ≥ √(2κ)/2` for `|E| < 2 − κ`. -/
private theorem rE_ge {κ E : ℝ} (hκ : 0 < κ) (hE : |E| < 2 - κ) :
    Real.sqrt (2 * κ) / 2 ≤ rE E := by
  rw [rE]
  gcongr
  have h1 : |E| ^ 2 = E ^ 2 := sq_abs E
  have h0 := abs_nonneg E
  nlinarith

/-! ## The quadratic form `W² p·𝒟 p` -/

private theorem phase_eq {d L : ℕ} [NeZero L] (k x : Zd d L) :
    phase k x = ∑ i, zfreq k i * ((x i).valMinAbs : ℝ) := by
  simp only [phase, zrep, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `W² p·A p` for `A_{ij} = c Σ_x ([x]_i [x]_j / W²) g(x)` is `c Σ_x g(x) t_x²`. -/
private theorem qform_moment {d L : ℕ} [NeZero L] (W : ℕ) (hW : W ≠ 0) (k : Zd d L) (c : ℂ)
    (g : Zd d L → ℂ) :
    qform W k (Matrix.of fun i j => c * ∑ x : Zd d L,
      ((((x i).valMinAbs : ℝ) * ((x j).valMinAbs : ℝ) / (W : ℝ) ^ 2 : ℝ) : ℂ) * g x) =
    c * ∑ x, g x * ((phase k x ^ 2 : ℝ) : ℂ) := by
  have hW' : ((W : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hW
  calc qform W k (Matrix.of fun i j => c * ∑ x : Zd d L,
        ((((x i).valMinAbs : ℝ) * ((x j).valMinAbs : ℝ) / (W : ℝ) ^ 2 : ℝ) : ℂ) * g x)
      = ∑ i, ∑ j, ∑ x : Zd d L, c * g x * (((zfreq k i * ((x i).valMinAbs : ℝ)) *
          (zfreq k j * ((x j).valMinAbs : ℝ)) : ℝ) : ℂ) := by
        simp only [qform, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun x _ => ?_
        push_cast
        field_simp
    _ = ∑ x : Zd d L, ∑ i, ∑ j, c * g x * (((zfreq k i * ((x i).valMinAbs : ℝ)) *
          (zfreq k j * ((x j).valMinAbs : ℝ)) : ℝ) : ℂ) := by
        refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
        exact Finset.sum_comm
    _ = c * ∑ x, g x * ((phase k x ^ 2 : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [phase_eq, sq, Finset.sum_mul_sum]
        push_cast
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem qform_add {d L : ℕ} (W : ℕ) (k : Zd d L) (A B : Matrix (Fin d) (Fin d) ℂ) :
    qform W k (A + B) = qform W k A + qform W k B := by
  simp only [qform, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private theorem qform_smul {d L : ℕ} (W : ℕ) (k : Zd d L) (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    qform W k (c • A) = c * qform W k A := by
  simp only [qform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem qform_sum {d L : ℕ} (W : ℕ) (k : Zd d L) (s : Finset ℕ)
    (A : ℕ → Matrix (Fin d) (Fin d) ℂ) :
    qform W k (∑ l ∈ s, A l) = ∑ l ∈ s, qform W k (A l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qform]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qform_add, ih]

/-- `W² p·𝒟_eff^{(M)} p = r(E) Σ_x S_{0x} t_x²/2 + r(E) Σ_x Σ̃^{(M)}_{0x} t_x²/2`. -/
private theorem qform_diffEff {d : ℕ} (P : Profile d) (Sg : SigmaFam d) (M W L : ℕ) [NeZero L]
    (hW : W ≠ 0) (z : ℂ) (k : Zd d L) :
    qform W k (diffEff P Sg M W L z) =
      (rE z.re : ℂ) * ∑ x, ((Smat P.ψ W L 0 x : ℝ) : ℂ) * ((phase k x ^ 2 / 2 : ℝ) : ℂ) +
      (rE z.re : ℂ) * ∑ x, sigTildeM Sg M W L z 0 x * ((phase k x ^ 2 / 2 : ℝ) : ℂ) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  have hD : diffD (Smat P.ψ W L) W z.re = Matrix.of fun i j => ((rE z.re / 2 : ℝ) : ℂ) *
      ∑ x : Zd d L, ((((x i).valMinAbs : ℝ) * ((x j).valMinAbs : ℝ) / (W : ℝ) ^ 2 : ℝ) : ℂ) *
        ((Smat P.ψ W L 0 x : ℝ) : ℂ) := by
    ext i j
    simp only [diffD, Matrix.of_apply]
    push_cast
    rfl
  have hw : ∀ l : ℕ, (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) *
      (((W : ℝ) ^ (((l : ℝ) - 2) * d / 2) / 2 : ℝ) : ℂ) = 1 / 2 := by
    intro l
    rw [← Complex.ofReal_mul, Real.rpow_neg hW0.le]
    have : (W : ℝ) ^ (((l : ℝ) - 2) * d / 2) ≠ 0 := (Real.rpow_pos_of_pos hW0 _).ne'
    rw [show ((W : ℝ) ^ (((l : ℝ) - 2) * d / 2))⁻¹ * ((W : ℝ) ^ (((l : ℝ) - 2) * d / 2) / 2) =
      1 / 2 by field_simp]
    push_cast; ring
  rw [diffEff, qform_add, qform_smul, qform_sum, hD, qform_moment W hW]
  simp only [qform_smul, diffDl, qform_moment W hW]
  have e1 : ∑ l ∈ Finset.Icc 4 M, (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) *
      ((((W : ℝ) ^ (((l : ℝ) - 2) * d / 2) / 2 : ℝ) : ℂ) *
        ∑ x, Sg l W L z 0 x * ((phase k x ^ 2 : ℝ) : ℂ)) =
      ∑ x, sigTildeM Sg M W L z 0 x * ((phase k x ^ 2 / 2 : ℝ) : ℂ) := by
    simp only [← mul_assoc, hw, sigTildeM, Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  rw [e1, Finset.mul_sum, Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast; ring

/-! ## The expansion of the denominator -/

/-- The bounds of [I, (1.33)] from the bounds of the symbols: with `Ŝ = Sh`, `Σ̂ = Sg`,
`Σ̂(0) = Sg0`, `Qs = Σ_x S_{0x} t_x²/2`, `Qg = Σ_x Σ̃_{0x} t_x²/2`, `Y = W|p|`, `a(η + μ) = μ` and
`|μ − r| ≤ η/r`: `u = μŜ/r − 1` and `e = (η + μ)(1 − aŜ(1 + Σ̂)) − η − r(Qs + Qg)` satisfy
`|u| ≤ C(η + Y²)` and `|e| ≤ C(η² + Vη + Y³)`. -/
private theorem assemble (μ r r₀ η a Y V M A₂ A₃ B₂ B₃ : ℝ) (Sh Sg Sg0 Qs Qg : ℂ)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hη : 0 < η)
    (hμr : |μ - r| ≤ η / r) (ha : a * (η + μ) = μ)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) (hV : 0 ≤ V) (hM : 0 ≤ M) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃)
    (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hSh : ‖Sh‖ ≤ 1) (h1 : ‖Sh - 1‖ ≤ A₂ * Y ^ 2) (hQs : ‖Qs‖ ≤ A₂ * Y ^ 2)
    (h2 : ‖Sh - 1 + Qs‖ ≤ A₃ * Y ^ 3)
    (hQg : ‖Qg‖ ≤ B₂ * Y ^ 2) (h3 : ‖Sg - Sg0 + Qg‖ ≤ B₃ * Y ^ 3) (h0 : ‖Sg0‖ ≤ M * V * η) :
    ‖(μ : ℂ) * Sh / r - 1‖ ≤ (1 / r₀ ^ 2 + A₂) * (η + Y ^ 2) ∧
    ‖((η : ℂ) + μ) * (1 - (a : ℂ) * Sh * (1 + Sg)) - η - ((r : ℂ) * Qs + (r : ℂ) * Qg)‖ ≤
      (A₃ + A₂ / r₀ + B₃ + M + B₂ / r₀ + A₂ * M + A₂ * B₂ + A₂ * B₃) *
        (η ^ 2 + V * η + Y ^ 3) := by
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hμr' : |μ - r| ≤ η / r₀ := hμr.trans (div_le_div_of_nonneg_left hη.le hr₀ hr)
  have hY2 : Y ^ 2 ≤ 1 := pow_le_one₀ hY0 hY1
  have hY43 : Y ^ 4 ≤ Y ^ 3 := pow_le_pow_of_le_one hY0 hY1 (by norm_num)
  have hY53 : Y ^ 5 ≤ Y ^ 3 := pow_le_pow_of_le_one hY0 hY1 (by norm_num)
  have hηY : η * Y ^ 2 ≤ η ^ 2 + Y ^ 3 := by nlinarith [sq_nonneg (η - Y ^ 2)]
  constructor
  · have e : (μ : ℂ) * Sh / r - 1 = (((μ - r) / r : ℝ) : ℂ) * Sh + (Sh - 1) := by
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      push_cast
      field_simp
      ring
    rw [e]
    have hq : |μ - r| / r ≤ η / r₀ ^ 2 := by
      rw [div_le_iff₀ hr0]
      calc |μ - r| ≤ η / r := hμr
        _ = η / r₀ ^ 2 * (r₀ ^ 2 / r) := by field_simp
        _ ≤ η / r₀ ^ 2 * r := by
            gcongr
            rw [div_le_iff₀ hr0]; nlinarith
    calc ‖(((μ - r) / r : ℝ) : ℂ) * Sh + (Sh - 1)‖ ≤ |μ - r| / r * 1 + A₂ * Y ^ 2 := by
          refine (norm_add_le _ _).trans (add_le_add ?_ h1)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hr0]
          gcongr
      _ ≤ η / r₀ ^ 2 + A₂ * Y ^ 2 := by linarith
      _ ≤ (1 / r₀ ^ 2 + A₂) * (η + Y ^ 2) := by
          have : 0 ≤ 1 / r₀ ^ 2 * Y ^ 2 := by positivity
          have : 0 ≤ A₂ * η := by positivity
          have e2 : η / r₀ ^ 2 = 1 / r₀ ^ 2 * η := by ring
          nlinarith
  · have haC : (a : ℂ) * ((η : ℂ) + μ) = μ := by exact_mod_cast ha
    have e : ((η : ℂ) + μ) * (1 - (a : ℂ) * Sh * (1 + Sg)) - η - ((r : ℂ) * Qs + (r : ℂ) * Qg) =
        -((μ : ℂ) * (Sh - 1 + Qs)) + ((μ - r : ℝ) : ℂ) * Qs - (μ : ℂ) * (Sg - Sg0 + Qg) -
          (μ : ℂ) * Sg0 + ((μ - r : ℝ) : ℂ) * Qg - (μ : ℂ) * ((Sh - 1) * Sg) := by
      push_cast
      linear_combination (-(Sh * (1 + Sg))) * haC
    rw [e]
    set T := η ^ 2 + V * η + Y ^ 3 with hT
    have hT1 : η ^ 2 ≤ T := by have := mul_nonneg hV hη.le; have := pow_nonneg hY0 3; linarith
    have hT2 : V * η ≤ T := by have := sq_nonneg η; have := pow_nonneg hY0 3; linarith
    have hT3 : Y ^ 3 ≤ T := by have := sq_nonneg η; have := mul_nonneg hV hη.le; linarith
    have hT0 : 0 ≤ T := le_trans (pow_nonneg hY0 3) hT3
    have hμn : ∀ X : ℂ, ‖(μ : ℂ) * X‖ ≤ ‖X‖ := fun X => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ0]
      exact mul_le_of_le_one_left (norm_nonneg _) hμ1
    have hmr : ∀ X : ℂ, ‖((μ - r : ℝ) : ℂ) * X‖ ≤ η / r₀ * ‖X‖ := fun X => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hμr' (norm_nonneg _)
    have t1 : ‖-((μ : ℂ) * (Sh - 1 + Qs))‖ ≤ A₃ * T := by
      rw [norm_neg]; exact (hμn _).trans (h2.trans (mul_le_mul_of_nonneg_left hT3 hA₃))
    have t2 : ‖((μ - r : ℝ) : ℂ) * Qs‖ ≤ A₂ / r₀ * T := by
      refine (hmr _).trans ?_
      calc η / r₀ * ‖Qs‖ ≤ η / r₀ * (A₂ * Y ^ 2) := by gcongr
        _ = A₂ / r₀ * (η * Y ^ 2) := by ring
        _ ≤ A₂ / r₀ * (η ^ 2 + Y ^ 3) := by gcongr
        _ ≤ A₂ / r₀ * T := by gcongr; linarith [mul_nonneg hV hη.le]
    have t3 : ‖(μ : ℂ) * (Sg - Sg0 + Qg)‖ ≤ B₃ * T :=
      (hμn _).trans (h3.trans (mul_le_mul_of_nonneg_left hT3 hB₃))
    have t4 : ‖(μ : ℂ) * Sg0‖ ≤ M * T := by
      refine (hμn _).trans (h0.trans ?_)
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hT2 hM
    have t5 : ‖((μ - r : ℝ) : ℂ) * Qg‖ ≤ B₂ / r₀ * T := by
      refine (hmr _).trans ?_
      calc η / r₀ * ‖Qg‖ ≤ η / r₀ * (B₂ * Y ^ 2) := by gcongr
        _ = B₂ / r₀ * (η * Y ^ 2) := by ring
        _ ≤ B₂ / r₀ * (η ^ 2 + Y ^ 3) := by gcongr
        _ ≤ B₂ / r₀ * T := by gcongr; linarith [mul_nonneg hV hη.le]
    have hSg : ‖Sg‖ ≤ M * V * η + B₂ * Y ^ 2 + B₃ * Y ^ 3 := by
      have e3 : Sg = Sg0 - Qg + (Sg - Sg0 + Qg) := by ring
      rw [e3]
      calc ‖Sg0 - Qg + (Sg - Sg0 + Qg)‖ ≤ ‖Sg0‖ + ‖Qg‖ + ‖Sg - Sg0 + Qg‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ _ := by linarith
    have t6 : ‖(μ : ℂ) * ((Sh - 1) * Sg)‖ ≤ (A₂ * M + A₂ * B₂ + A₂ * B₃) * T := by
      refine (hμn _).trans ?_
      rw [norm_mul]
      have hY2' : 0 ≤ Y ^ 2 := sq_nonneg Y
      have hMV : 0 ≤ M * V * η := by positivity
      calc ‖Sh - 1‖ * ‖Sg‖ ≤ A₂ * Y ^ 2 * (M * V * η + B₂ * Y ^ 2 + B₃ * Y ^ 3) := by
            gcongr
        _ = A₂ * M * (Y ^ 2 * (V * η)) + A₂ * B₂ * Y ^ 4 + A₂ * B₃ * Y ^ 5 := by ring
        _ ≤ A₂ * M * (V * η) + A₂ * B₂ * Y ^ 3 + A₂ * B₃ * Y ^ 3 := by
            have hVη : 0 ≤ V * η := by positivity
            have i1 := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hVη hY2)
              (mul_nonneg hA₂ hM)
            have i2 := mul_le_mul_of_nonneg_left hY43 (mul_nonneg hA₂ hB₂)
            have i3 := mul_le_mul_of_nonneg_left hY53 (mul_nonneg hA₂ hB₃)
            linarith
        _ ≤ (A₂ * M + A₂ * B₂ + A₂ * B₃) * T := by
            have := mul_le_mul_of_nonneg_left hT2 (mul_nonneg hA₂ hM)
            have := mul_le_mul_of_nonneg_left hT3 (mul_nonneg hA₂ hB₂)
            have := mul_le_mul_of_nonneg_left hT3 (mul_nonneg hA₂ hB₃)
            nlinarith
    calc _ ≤ ‖-((μ : ℂ) * (Sh - 1 + Qs))‖ + ‖((μ - r : ℝ) : ℂ) * Qs‖ +
          ‖(μ : ℂ) * (Sg - Sg0 + Qg)‖ + ‖(μ : ℂ) * Sg0‖ + ‖((μ - r : ℝ) : ℂ) * Qg‖ +
          ‖(μ : ℂ) * ((Sh - 1) * Sg)‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_add_le _ _
      _ ≤ A₃ * T + A₂ / r₀ * T + B₃ * T + M * T + B₂ / r₀ * T +
          (A₂ * M + A₂ * B₂ + A₂ * B₃) * T := by gcongr
      _ = _ := by ring

/-- `|Σ_x f(x) t_x²/2| ≤ Σ_x |f(x)| t_x²/2`. -/
private theorem norm_Q_le {d L : ℕ} [NeZero L] (f : Zd d L → ℂ) (k : Zd d L) :
    ‖∑ x, f x * ((phase k x ^ 2 / 2 : ℝ) : ℂ)‖ ≤ ∑ x, ‖f x‖ * (phase k x ^ 2 / 2) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- `W^{−(l−2)d/2} ≤ W^{−d}` for `W ≥ 1`, `l ≥ 4`. -/
private theorem rpow_order_le (W : ℝ) (hW : 1 ≤ W) (d l : ℕ) (hl : 4 ≤ l) :
    W ^ (-(((l : ℝ) - 2) * d / 2)) ≤ W ^ (-(d : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le hW ?_
  have : (4 : ℝ) ≤ l := by exact_mod_cast hl
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

/-- `|p| ≤ d · 2π ‖k‖_L / L` for `p = 2πk/L`. -/
private theorem norm_zfreq_le {d L : ℕ} [NeZero L] (k : Zd d L) :
    ‖zfreq k‖ ≤ d * (2 * Real.pi * zdistInf d L k / L) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  set c : ℝ := 2 * Real.pi * zdistInf d L k / L with hc
  have hi : ∀ i, ‖(zfreq k).ofLp i‖ ^ 2 ≤ c ^ 2 := by
    intro i
    have h1 : ‖(zfreq k).ofLp i‖ = 2 * Real.pi * (zdist L (k i) : ℝ) / L := by
      simp only [zfreq, Real.norm_eq_abs, zdist_eq_natAbs_valMinAbs, Nat.cast_natAbs,
        Int.cast_abs]
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        abs_of_pos hL0]
    rw [h1]
    have : (zdist L (k i) : ℝ) ≤ zdistInf d L k := by exact_mod_cast zdist_le_zdistInf d L k i
    rw [hc]
    gcongr
  calc ∑ i, ‖(zfreq k).ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, c ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = d * c ^ 2 := by simp
    _ ≤ ((d : ℝ) * c) ^ 2 := by
        have : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h
            nlinarith
        nlinarith [sq_nonneg c]

end ThetaMSymbol

open ThetaMSymbol in
/-- **[I, (1.33)]** in quantified form: for `d ≥ 8`, the self-energies `Σ_l` of `SigmaOf`, an
order `M` and `δ, τ > 0`, there are `C`, `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)`,
`|E| < 2 − κ`, `η ∈ [W²/L^{2−ε}, W^{−δ}]` and `|p| ≤ W^{−1−δ}`:
`Θ̂^{(M)}(p) = r(E)(1 + u)/(η + W² p·𝒟_eff^{(M)} p + e)` with `|u| ≤ C(η + W²|p|²)`,
`|e| ≤ C(η² + W^{−d+τ}η + W³|p|³)` and a nonzero denominator. -/
theorem symbolThetaM : symbolThetaMStmt := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig hSE Sg hSg M δ τ hδ hτ
  set τ' : ℝ := c₁ * min τ 1 with hτ'
  have hτ'0 : 0 < τ' := mul_pos hc₁ (lt_min hτ one_pos)
  obtain ⟨L₀', hL₀'⟩ := thetaMBounds d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig hSE Sg hSg M M le_rfl
    τ' hτ'0
  obtain ⟨W₁, hW₁⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, hW₂⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  obtain ⟨C₂, hC₂0, hC₂⟩ := moment_S d P c₀ c₁ hc₀ 2
  obtain ⟨C₃, hC₃0, hC₃⟩ := moment_S d P c₀ c₁ hc₀ 3
  obtain ⟨L₁, hL₁⟩ := slack d hd c₁ M hc₁ (Nat.cast_nonneg M)
  set r₀ : ℝ := Real.sqrt (2 * κ) / 2 with hr₀
  have hr₀0 : 0 < r₀ := by rw [hr₀]; have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ); linarith
  set A₂ : ℝ := (d : ℝ) ^ 2 * C₂ / 2 with hA₂
  set A₃ : ℝ := (d : ℝ) ^ 3 * C₃ with hA₃
  set B₂ : ℝ := (d : ℝ) ^ 2 / 2 with hB₂
  set B₃ : ℝ := (d : ℝ) ^ 3 with hB₃
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hA₃0 : 0 ≤ A₃ := by positivity
  have hB₂0 : 0 ≤ B₂ := by positivity
  have hB₃0 : 0 ≤ B₃ := by positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set Cu : ℝ := 1 / r₀ ^ 2 + A₂ with hCu
  set Ce : ℝ := A₃ + A₂ / r₀ + B₃ + M + B₂ / r₀ + A₂ * M + A₂ * B₂ + A₂ * B₃ with hCe
  have hCu0 : 0 ≤ Cu := by positivity
  have hCe0 : 0 ≤ Ce := by positivity
  set Wt : ℝ := max (max W₁ W₂) 1 with hWt
  have hWt0 : 0 < Wt := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Cu + Ce, max L₀' (max L₁ (max 1 ⌈Wt ^ c₁⁻¹⌉₊)),
    fun W L _ hL hadm E η hE hη1 hη2 k hk => ?_⟩
  have hL0' : L₀' ≤ L := le_trans (le_max_left _ _) hL
  have hL1' : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hL
  have hLc : ⌈Wt ^ c₁⁻¹⌉₊ ≤ L := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hL
  have hWtL : Wt ≤ (L : ℝ) ^ c₁ := by
    have h1 : Wt ^ c₁⁻¹ ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hLc)
    have := Real.rpow_le_rpow (by positivity) h1 hc₁.le
    rwa [Real.rpow_inv_rpow hWt0.le hc₁.ne'] at this
  have hW : Wt ≤ (W : ℝ) := hWtL.trans hadm.1
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hWne : W ≠ 0 := by omega
  set z : ℂ := (E : ℂ) + η * I with hzdef
  have hzre : z.re = E := by simp [hzdef]
  have hzim : z.im = η := by simp [hzdef]
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  have hηle : η ≤ 1 := hη2.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (neg_nonpos.2 hδ.le))
  have hz : z ∈ specDom κ ε W L := ⟨by rw [hzre]; exact hE, by rw [hzim]; exact hη1,
    by rw [hzim]; exact hηle⟩
  obtain ⟨hU, -, h126, h127, -, -⟩ := hL₀' W L hL0' hadm z hz
  obtain ⟨hSs, hS0⟩ := hW₁ W L hadm (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW)
  have hDS := hW₂ W L hadm (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW)
  have hS1 : ∑ x, Smat P.ψ W L 0 x = 1 := sum_row_of_mem_doublyStochastic hDS 0
  -- the matrices and their symbols
  set S := Smat P.ψ W L with hSdef
  set σ := sigTildeM Sg M W L z with hσdef
  have hσx : ∀ x, σ 0 x = ∑ l ∈ Finset.Icc 4 M, Sg l W L z 0 x := fun x =>
    Matrix.sum_apply _ _ _ _
  have hTS : TransInv (cmat S) := fun x y a => by
    simp only [cmat, Matrix.map_apply, hSdef, Smat_transInv d L P.ψ W x y a]
  have hTA : TransInv (amat S z) := fun x y a => by
    simp only [amat, Matrix.smul_apply, hTS x y a]
  have hTl : ∀ l ∈ Finset.Icc 4 M, TransInv (Sg l W L z) := by
    intro l hl x y a
    have hl4 := (Finset.mem_Icc.1 hl).1
    have h1 := (hSg.2.2 l hl4 W L z (x + a) (y - x)).1
    have h2 := (hSg.2.2 l hl4 W L z x (y - x)).1
    rw [show x + a + (y - x) = y + a by abel] at h1
    rw [show x + (y - x) = y by abel] at h2
    rw [h1, h2]
  have hTσ : TransInv σ := fun x y a => by
    simp only [hσdef, sigTildeM, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun l hl => hTl l hl x y a
  have hTX : TransInv (1 + σ) := fun x y a => by
    simp only [Matrix.add_apply, Matrix.one_apply, add_left_inj, hTσ x y a]
  have hTAX : TransInv (amat S z * (1 + σ)) := TransInv_mul _ _ hTA hTX
  have hT1 : TransInv (1 - amat S z * (1 + σ)) := fun x y a => by
    simp only [Matrix.sub_apply, Matrix.one_apply, add_left_inj, hTAX x y a]
  set Sh := symbol (cmat S) k with hShdef
  set Sgh := symbol σ k with hSghdef
  set μ := (msc z).im with hμdef
  set a := ‖msc z‖ ^ 2 with hadef
  set r := rE E with hrdef
  have hAh : symbol (amat S z) k = (a : ℂ) * Sh := (symbol_add_smul (cmat S) (cmat S) _ k).2
  have hXh : symbol (1 + σ) k = 1 + Sgh := by rw [(symbol_add_smul 1 σ 1 k).1, symbol_one]
  have h1AX : symbol (1 - amat S z * (1 + σ)) k = 1 - (a : ℂ) * Sh * (1 + Sgh) := by
    have : symbol (1 - amat S z * (1 + σ)) k = symbol 1 k - symbol (amat S z * (1 + σ)) k := by
      simp only [symbol, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [this, symbol_one, symbol_mul _ _ hTA hTX, hAh, hXh]
  have hDne : 1 - (a : ℂ) * Sh * (1 + Sgh) ≠ 0 := by
    rw [← h1AX]; exact (isUnit_iff_symbol _ hT1).1 hU k
  have hTh : symbol (thetaM S (1 + σ) z) k = (a : ℂ) * Sh / (1 - (a : ℂ) * Sh * (1 + Sgh)) := by
    unfold thetaM
    rw [G16.symbol_inv_mul _ _ hTA hTX hU k, hAh, hXh]
  -- evenness and the cosine form
  have hSe : ∀ x : Zd d L, S 0 (-x) = S 0 x := by
    intro x
    have h1 := hSs.apply 0 x
    simp only [hSdef, Smat, Matrix.of_apply, zero_sub, sub_zero, neg_neg] at h1 ⊢
    exact h1
  have hσe : ∀ x : Zd d L, σ 0 (-x) = σ 0 x := by
    intro x
    rw [hσx, hσx]
    exact Finset.sum_congr rfl fun l hl =>
      ((hSg.2.2 l (Finset.mem_Icc.1 hl).1 W L z 0 x).2).symm
  have hShc : Sh = ∑ x, ((S 0 x : ℝ) : ℂ) * (Real.cos (phase k x) : ℂ) := by
    rw [hShdef]
    simp only [symbol, cmat, Matrix.map_apply]
    exact sum_even_eq (fun x => ((S 0 x : ℝ) : ℂ)) (fun x => by simp only [hSe]) k
  have hSgc : Sgh = ∑ x, σ 0 x * (Real.cos (phase k x) : ℂ) := by
    rw [hSghdef]
    exact sum_even_eq (fun x => σ 0 x) hσe k
  -- the cosine expansions and the moments
  obtain ⟨cs1, cs2⟩ := cos_sum_bounds (fun x => ((S 0 x : ℝ) : ℂ)) k
  obtain ⟨cg1, cg2⟩ := cos_sum_bounds (fun x => σ 0 x) k
  obtain ⟨ps2, ps3⟩ := phase_sum_bounds (fun x => ((S 0 x : ℝ) : ℂ)) k
  obtain ⟨pg2, pg3⟩ := phase_sum_bounds (fun x => σ 0 x) k
  have qs := norm_Q_le (fun x => ((S 0 x : ℝ) : ℂ)) k
  have qg := norm_Q_le (fun x => σ 0 x) k
  have hnS : ∀ x, ‖((S 0 x : ℝ) : ℂ)‖ = |S 0 x| := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [hnS] at cs1 cs2 ps2 ps3 qs
  have m2 := hC₂ W L hadm hWn
  have m3 := hC₃ W L hadm hWn
  set p := ‖zfreq k‖ with hpdef
  have hp0 : 0 ≤ p := norm_nonneg _
  set Y : ℝ := (W : ℝ) * p with hYdef
  have hY0 : 0 ≤ Y := by positivity
  have hY1 : Y ≤ 1 := by
    have h1 : (W : ℝ) * p ≤ (W : ℝ) * (W : ℝ) ^ (-1 - δ) := mul_le_mul_of_nonneg_left hk hW0.le
    have h2 : (W : ℝ) * (W : ℝ) ^ (-1 - δ) = (W : ℝ) ^ (-δ) := by
      rw [← Real.rpow_one_add' hW0.le (by ring_nf; exact neg_ne_zero.2 hδ.ne')]; ring_nf
    rw [hYdef]
    exact h1.trans (h2.le.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (neg_nonpos.2 hδ.le)))
  -- the slack in the self-energy terms
  have hsl : (M : ℝ) * (L : ℝ) ^ τ' * (2 + 2 * Real.log L) ^ d ≤ (W : ℝ) ^ d := by
    have h1 := hL₁ L hL1'
    have hτc : τ' ≤ c₁ := mul_le_of_le_one_right hc₁.le (min_le_right τ 1)
    have h2 : (L : ℝ) ^ τ' ≤ (L : ℝ) ^ c₁ := Real.rpow_le_rpow_of_exponent_le hL1 hτc
    have h3 : (L : ℝ) ^ (c₁ * d) ≤ (W : ℝ) ^ d := by
      rw [Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
      exact pow_le_pow_left₀ (by positivity) hadm.1 d
    have h4 : 0 ≤ (2 + 2 * Real.log L) ^ d :=
      pow_nonneg (add_nonneg zero_le_two (mul_nonneg zero_le_two (Real.log_nonneg hL1))) d
    calc (M : ℝ) * (L : ℝ) ^ τ' * (2 + 2 * Real.log L) ^ d
        ≤ (M : ℝ) * (L : ℝ) ^ c₁ * (2 + 2 * Real.log L) ^ d := by gcongr
      _ ≤ _ := h1.trans h3
  have hσm : ∀ kk : ℕ, 1 ≤ kk → kk + 4 ≤ d →
      ∑ x, ‖σ 0 x‖ * (zdistInf d L x : ℝ) ^ kk ≤ (W : ℝ) ^ kk := by
    intro kk hk1 hk4
    have h := moment_sig d L W M hWn kk hk1 hk4 ((L : ℝ) ^ τ') (by positivity)
      (fun l x => Sg l W L z 0 x) (fun l => (L : ℝ) ^ τ' * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)))
      h126
    simp only [← hσx] at h
    refine h.trans ?_
    have e : (W : ℝ) ^ ((kk : ℝ) - d) * (W : ℝ) ^ d = (W : ℝ) ^ kk := by
      rw [← Real.rpow_natCast W d, ← Real.rpow_add hW0, ← Real.rpow_natCast]; ring_nf
    calc (M : ℝ) * (L : ℝ) ^ τ' * (W : ℝ) ^ ((kk : ℝ) - d) * (2 + 2 * Real.log L) ^ d
        = (W : ℝ) ^ ((kk : ℝ) - d) * ((M : ℝ) * (L : ℝ) ^ τ' * (2 + 2 * Real.log L) ^ d) := by
          ring
      _ ≤ (W : ℝ) ^ ((kk : ℝ) - d) * (W : ℝ) ^ d := by gcongr
      _ = _ := e
  have hσ2 := hσm 2 (by norm_num) (by omega)
  have hσ3 := hσm 3 (by norm_num) (by omega)
  -- [I, (1.27)]
  set V : ℝ := (W : ℝ) ^ (-(d : ℝ) + τ) with hVdef
  have hV0 : 0 ≤ V := by positivity
  set Sg0 : ℂ := ∑ x, σ 0 x with hSg0
  have h0 : ‖Sg0‖ ≤ M * V * η := by
    have e : Sg0 = ∑ l ∈ Finset.Icc 4 M, ∑ x, Sg l W L z 0 x := by
      rw [hSg0]; simp only [hσx]; exact Finset.sum_comm
    have hLW : (L : ℝ) ^ τ' ≤ (W : ℝ) ^ τ := by
      have h1 : (L : ℝ) ^ τ' = ((L : ℝ) ^ c₁) ^ min τ 1 := by
        rw [hτ', Real.rpow_mul (Nat.cast_nonneg _)]
      rw [h1]
      calc ((L : ℝ) ^ c₁) ^ min τ 1 ≤ (W : ℝ) ^ min τ 1 :=
            Real.rpow_le_rpow (by positivity) hadm.1 (le_min hτ.le zero_le_one)
        _ ≤ (W : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _)
    have hl : ∀ l ∈ Finset.Icc 4 M, ‖∑ x, Sg l W L z 0 x‖ ≤ V * η := by
      intro l hl
      obtain ⟨hl4, hlM⟩ := Finset.mem_Icc.1 hl
      refine (h127 l hl4 hlM).trans ?_
      rw [hzim]
      have hw := rpow_order_le W hW1 d l hl4
      have eV : V = (W : ℝ) ^ τ * (W : ℝ) ^ (-(d : ℝ)) := by
        rw [hVdef, ← Real.rpow_add hW0]; ring_nf
      rw [eV]
      calc (L : ℝ) ^ τ' * η * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))
          ≤ (W : ℝ) ^ τ * η * (W : ℝ) ^ (-(d : ℝ)) := by gcongr
        _ = _ := by ring
    have hcard : ((Finset.Icc 4 M).card : ℝ) ≤ M := by
      rw [Nat.card_Icc]; exact_mod_cast (by omega : M + 1 - 4 ≤ M)
    rw [e]
    calc ‖∑ l ∈ Finset.Icc 4 M, ∑ x, Sg l W L z 0 x‖
        ≤ ∑ l ∈ Finset.Icc 4 M, ‖∑ x, Sg l W L z 0 x‖ := norm_sum_le _ _
      _ ≤ ∑ _l ∈ Finset.Icc 4 M, V * η := Finset.sum_le_sum hl
      _ = (Finset.Icc 4 M).card * (V * η) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * (V * η) := by gcongr
      _ = M * V * η := by ring
  -- the symbols of `S` and of `Σ̃^{(M)}`
  set Qs : ℂ := ∑ x, ((S 0 x : ℝ) : ℂ) * ((phase k x ^ 2 / 2 : ℝ) : ℂ) with hQsdef
  set Qg : ℂ := ∑ x, σ 0 x * ((phase k x ^ 2 / 2 : ℝ) : ℂ) with hQgdef
  have hsumS : ∑ x, ((S 0 x : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hS1, Complex.ofReal_one]
  have hSabs : ∀ x, |S 0 x| = S 0 x := fun x => abs_of_nonneg (hS0 0 x)
  have hm2 : ∑ x, |S 0 x| * (zdistInf d L x : ℝ) ^ 2 ≤ C₂ * (W : ℝ) ^ 2 := m2
  have hm3 : ∑ x, |S 0 x| * (zdistInf d L x : ℝ) ^ 3 ≤ C₃ * (W : ℝ) ^ 3 := m3
  have hY2 : A₂ * Y ^ 2 = (d : ℝ) ^ 2 * p ^ 2 / 2 * (C₂ * (W : ℝ) ^ 2) := by
    rw [hA₂, hYdef]; ring
  have hY3 : A₃ * Y ^ 3 = (d : ℝ) ^ 3 * p ^ 3 * (C₃ * (W : ℝ) ^ 3) := by
    rw [hA₃, hYdef]; ring
  have hSh : ‖Sh‖ ≤ 1 := by
    rw [hShc]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x, ‖((S 0 x : ℝ) : ℂ) * (Real.cos (phase k x) : ℂ)‖ ≤ ∑ x, S 0 x := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [norm_mul, hnS, hSabs, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_right (hS0 0 x) (Real.abs_cos_le_one _)
      _ = 1 := hS1
  have h1 : ‖Sh - 1‖ ≤ A₂ * Y ^ 2 := by
    rw [hShc, ← hsumS, hY2]
    refine cs1.trans (ps2.trans ?_)
    gcongr
  have hQs : ‖Qs‖ ≤ A₂ * Y ^ 2 := by
    rw [hY2]
    refine qs.trans (ps2.trans ?_)
    gcongr
  have h2 : ‖Sh - 1 + Qs‖ ≤ A₃ * Y ^ 3 := by
    rw [hShc, ← hsumS, hY3]
    refine cs2.trans (ps3.trans ?_)
    gcongr
  have hQg : ‖Qg‖ ≤ B₂ * Y ^ 2 := by
    refine qg.trans (pg2.trans ?_)
    rw [hB₂, hYdef]
    calc (d : ℝ) ^ 2 * p ^ 2 / 2 * ∑ x, ‖σ 0 x‖ * (zdistInf d L x : ℝ) ^ 2
        ≤ (d : ℝ) ^ 2 * p ^ 2 / 2 * (W : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have h3 : ‖Sgh - Sg0 + Qg‖ ≤ B₃ * Y ^ 3 := by
    rw [hSgc]
    refine cg2.trans (pg3.trans ?_)
    rw [hB₃, hYdef]
    calc (d : ℝ) ^ 3 * p ^ 3 * ∑ x, ‖σ 0 x‖ * (zdistInf d L x : ℝ) ^ 3
        ≤ (d : ℝ) ^ 3 * p ^ 3 * (W : ℝ) ^ 3 := by gcongr
      _ = _ := by ring
  -- the semicircle law
  have hzim0 : 0 < z.im := by rw [hzim]; exact hη0
  have hμ0 : 0 < μ := msc_im_pos hzim0
  have hμ1 : μ ≤ 1 := (Complex.im_le_norm _).trans (norm_msc_lt_one hzim0).le
  have ha : a * (η + μ) = μ := by
    have := im_msc_eq z
    rw [hzim] at this
    exact this.symm
  have hμr : |μ - r| ≤ η / r := by
    have := msc_im_sub_le hzim0 (by rw [hzre]; exact hE.trans (sub_lt_self 2 hκ))
    rwa [hzre, hzim] at this
  have hr : r₀ ≤ r := rE_ge hκ hE
  obtain ⟨hu, he⟩ := assemble μ r r₀ η a Y V M A₂ A₃ B₂ B₃ Sh Sgh Sg0 Qs Qg hr₀0 hr hμ0 hμ1
    hη0 hμr ha hY0 hY1 hV0 hM0 hA₂0 hA₃0 hB₂0 hB₃0 hSh h1 hQs h2 hQg h3 h0
  -- the identity
  have hq : qform W k (diffEff P Sg M W L z) = (r : ℂ) * Qs + (r : ℂ) * Qg := by
    rw [qform_diffEff P Sg M W L hWne z k, hzre]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hr₀0 hr).ne'
  have hημ : ((η : ℂ) + μ) ≠ 0 := by exact_mod_cast (add_pos hη0 hμ0).ne'
  have hden : (η : ℂ) + ((r : ℂ) * Qs + (r : ℂ) * Qg) +
      (((η : ℂ) + μ) * (1 - (a : ℂ) * Sh * (1 + Sgh)) - η - ((r : ℂ) * Qs + (r : ℂ) * Qg)) =
      ((η : ℂ) + μ) * (1 - (a : ℂ) * Sh * (1 + Sgh)) := by ring
  have hX : 0 ≤ η + (W : ℝ) ^ 2 * p ^ 2 := by positivity
  have hT : 0 ≤ η ^ 2 + V * η + (W : ℝ) ^ 3 * p ^ 3 := by positivity
  refine ⟨(μ : ℂ) * Sh / r - 1,
    ((η : ℂ) + μ) * (1 - (a : ℂ) * Sh * (1 + Sgh)) - η - ((r : ℂ) * Qs + (r : ℂ) * Qg),
    ?_, ?_, ?_, ?_⟩
  · refine hu.trans ?_
    rw [hYdef, mul_pow]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCe0) hX
  · refine he.trans ?_
    rw [hYdef, mul_pow]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCu0) hT
  · rw [hq, hden]
    exact mul_ne_zero hημ hDne
  · rw [hTh, hq, hden]
    have haC : (a : ℂ) * ((η : ℂ) + μ) = μ := by exact_mod_cast ha
    have e1 : (r : ℂ) * (1 + ((μ : ℂ) * Sh / r - 1)) = (a : ℂ) * ((η : ℂ) + μ) * Sh := by
      rw [haC]; field_simp; ring
    rw [e1, div_eq_div_iff hDne (mul_ne_zero hημ hDne)]
    ring

end RBM8D
