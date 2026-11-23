module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import RBM8D.Kernel.PropagatorSymbol
public import RBM8D.Kernel.ContractionCont

@[expose] public section

/-!
# Contraction on the torus

[I, (B.19)] in the n-th power form and [I, (B.20)].
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `A_c = (m² S + c)/(1 + c)` of [I, (B.19)]. -/
def Ashift (m : ℂ) (c : ℝ) (S : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  ((1 + c : ℂ))⁻¹ • (m ^ 2 • cmat S + (c : ℂ) • 1)

/-- The `ℓ^∞ → ℓ^∞` operator norm `max_x Σ_y |A_{xy}|`. -/
def opNormInf (A : Matrix ι ι ℂ) : ℝ :=
  ((Finset.univ.sup fun x => ∑ y, ‖A x y‖₊ : NNReal) : ℝ)

/-- `opNormInf` is Mathlib's `ℓ^∞` operator norm on matrices. -/
theorem opNormInf_eq :
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    opNormInf A = @Norm.norm _ Matrix.linftyOpNormedAddCommGroup.toNorm A := by
  intro ι _ _ A
  rw [Matrix.linfty_opNorm_def]
  rfl

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

omit [DecidableEq ι] in
/-- `opNormInf` is bounded by any common bound of the row sums. -/
private theorem opNormInf_le_of_rows (A : Matrix ι ι ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x, ∑ y, ‖A x y‖ ≤ r) : opNormInf A ≤ r := by
  have hs : (Finset.univ.sup fun x => ∑ y, ‖A x y‖₊) ≤ (⟨r, hr⟩ : NNReal) := by
    refine Finset.sup_le fun x _ => ?_
    refine NNReal.coe_le_coe.mp ?_
    rw [NNReal.coe_sum]
    exact h x
  exact NNReal.coe_le_coe.mpr hs

/-- `‖1‖ ≤ 1` for the `ℓ^∞` operator norm. -/
private theorem opNorm_one_le : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  rw [← opNormInf_eq]
  refine opNormInf_le_of_rows _ zero_le_one fun x => ?_
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [Matrix.one_apply_ne' hy]) (by simp)]
  simp

/-- `‖A^k‖ ≤ 1` when `‖A‖ ≤ 1`. -/
private theorem opNorm_pow_le_one {A : Matrix ι ι ℂ} (hA : ‖A‖ ≤ 1) (k : ℕ) : ‖A ^ k‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]; exact opNorm_one_le
  · exact (norm_pow_le' A hk).trans (pow_le_one₀ (norm_nonneg _) hA)

/-- `‖A_c‖_{∞→∞} ≤ (|m|² + c)/(1 + c)` for a nonnegative kernel with row sums one and
`c ≥ 0`. -/
private theorem opNormInf_Ashift_le_aux (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) (m : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    opNormInf (Ashift m c S) ≤ (‖m‖ ^ 2 + c) / (1 + c) := by
  have h1c : 0 < 1 + c := by linarith
  have h1cC : ((1 : ℂ) + c) = ((1 + c : ℝ) : ℂ) := by push_cast; ring
  refine opNormInf_le_of_rows _ (by positivity) fun x => ?_
  have hentry : ∀ y, ‖Ashift m c S x y‖ ≤
      (1 + c)⁻¹ * (‖m‖ ^ 2 * S x y + c * (if x = y then 1 else 0)) := by
    intro y
    simp only [Ashift, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, cmat,
      Matrix.map_apply, smul_eq_mul, norm_mul]
    rw [h1cC, norm_inv, Complex.norm_real, Real.norm_of_nonneg h1c.le]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hS0 x y), norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hc]
    gcongr
    split_ifs <;> simp
  calc ∑ y, ‖Ashift m c S x y‖
      ≤ ∑ y, (1 + c)⁻¹ * (‖m‖ ^ 2 * S x y + c * (if x = y then 1 else 0)) :=
        Finset.sum_le_sum fun y _ => hentry y
    _ = (1 + c)⁻¹ * (‖m‖ ^ 2 + c) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hS1 x, Finset.sum_ite_eq]
        simp
    _ = (‖m‖ ^ 2 + c) / (1 + c) := by rw [inv_mul_eq_div]

/-- `‖A_c‖_{∞→∞} ≤ 1` for a nonnegative kernel `S` with row sums one, `|m| ≤ 1` and `c ≥ 0`
([I, (B.19)]). -/
theorem opNormInf_Ashift_le :
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) (m : ℂ) (hm : ‖m‖ ≤ 1) (c : ℝ) (hc : 0 ≤ c),
    opNormInf (Ashift m c S) ≤ 1 := by
  intro ι _ _ S hS0 hS1 m hm c hc
  have h1c : 0 < 1 + c := by linarith
  have hm2 : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm
  refine (opNormInf_Ashift_le_aux S hS0 hS1 m c hc).trans ?_
  rw [div_le_one h1c]; linarith

/-- From `‖A‖_{∞→∞} ≤ 1` and `‖A^n‖_{∞→∞} ≤ q`: `‖A^k‖_{∞→∞} ≤ q^{⌊k/n⌋}` for every `k`. -/
theorem opNormInf_pow_le :
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (n : ℕ) (q : ℝ)
    (hA : opNormInf A ≤ 1) (hn : opNormInf (A ^ n) ≤ q) (k : ℕ), opNormInf (A ^ k) ≤ q ^ (k / n)
    := by
  intro ι _ _ A n q hA hn k
  rw [opNormInf_eq] at hA hn ⊢
  have hq : 0 ≤ q := (norm_nonneg _).trans hn
  have hpow : ‖(A ^ n) ^ (k / n)‖ ≤ q ^ (k / n) := by
    rcases Nat.eq_zero_or_pos (k / n) with h0 | hpos
    · rw [h0, pow_zero, pow_zero]; exact opNorm_one_le
    · exact (norm_pow_le' _ hpos).trans (pow_le_pow_left₀ (norm_nonneg _) hn _)
  calc ‖A ^ k‖ = ‖(A ^ n) ^ (k / n) * A ^ (k % n)‖ := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≤ ‖(A ^ n) ^ (k / n)‖ * ‖A ^ (k % n)‖ := norm_mul_le _ _
    _ ≤ q ^ (k / n) * 1 :=
        mul_le_mul hpow (opNorm_pow_le_one hA _) (norm_nonneg _) (pow_nonneg hq _)
    _ = q ^ (k / n) := mul_one _

/-! ## Bounds on the continuum symbol `A_ψ^n − (c/(1+c))^n` -/

section ContBounds

/-- The spectral bound behind [I, (B.19)]: for `|m| ≤ 1`, `|1 − m²| ≥ δ` and `t ∈ [−1 + c′, 1]`,
`|(m²t + c)/(1 + c)| ≤ ρ` for one `ρ < 1` with `c/(1 + c) ≤ ρ`. -/
private lemma torusCont_spectral {c c' δ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hδ : 0 < δ) :
    ∃ ρ : ℝ, ρ < 1 ∧ c / (1 + c) ≤ ρ ∧ ∀ m : ℂ, ‖m‖ ≤ 1 → δ ≤ ‖1 - m ^ 2‖ →
      ∀ t : ℝ, -1 + c' ≤ t → t ≤ 1 → ‖(m ^ 2 * (t : ℂ) + c) / (1 + c)‖ ≤ ρ := by
  have h1c : 0 < 1 + c := by linarith
  set a := c / (1 + c) with ha
  set q := 1 - c * δ ^ 2 / (1 + c) ^ 2 with hq
  refine ⟨max (max (Real.sqrt q) a) (1 - c' / (1 + c)), ?_, ?_, ?_⟩
  · refine max_lt (max_lt ?_ ?_) ?_
    · rw [Real.sqrt_lt' one_pos, one_pow]
      have : 0 < c * δ ^ 2 / (1 + c) ^ 2 := by positivity
      linarith
    · rw [ha, div_lt_one h1c]; linarith
    · have : 0 < c' / (1 + c) := by positivity
      linarith
  · exact le_max_of_le_left (le_max_right _ _)
  intro m hm hδm t ht0 ht1
  set w := m ^ 2 with hw
  have hw1 : ‖w‖ ≤ 1 := by rw [hw, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm
  have hnorm : ‖(w * (t : ℂ) + c) / (1 + c)‖ = ‖w * (t : ℂ) + c‖ / (1 + c) := by
    rw [norm_div]
    congr 1
    rw [show ((1 : ℂ) + c) = ((1 + c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg h1c.le]
  rw [hnorm, div_le_iff₀ h1c]
  rcases le_or_gt 0 t with ht | ht
  · -- `t ∈ [0, 1]`: `|wt + c|² ≤ (1 − t)c² + t((1 + c)² − cδ²)`
    have hsq : ‖w * (t : ℂ) + c‖ ^ 2 ≤ (max (Real.sqrt q) a * (1 + c)) ^ 2 := by
      have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
        have := Complex.sq_norm w
        rw [Complex.normSq_apply] at this
        nlinarith [norm_nonneg w]
      have hδ2 : δ ^ 2 ≤ (1 - w.re) ^ 2 + w.im ^ 2 := by
        have h := Complex.sq_norm (1 - w)
        rw [Complex.normSq_apply] at h
        simp only [sub_re, one_re, sub_im, one_im, zero_sub] at h
        nlinarith [norm_nonneg (1 - w)]
      have hval : ‖w * (t : ℂ) + c‖ ^ 2 = (w.re * t + c) ^ 2 + (w.im * t) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, add_im, mul_im,
          add_zero]
        ring
      have hmax : (max (Real.sqrt q) a * (1 + c)) ^ 2 ≥ max (q * (1 + c) ^ 2) (c ^ 2) := by
        have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
        rw [mul_pow]
        refine max_le ?_ ?_
        · rcases le_or_gt 0 q with hq0 | hq0
          · have : q ≤ max (Real.sqrt q) a ^ 2 :=
              calc q = Real.sqrt q ^ 2 := (Real.sq_sqrt hq0).symm
                _ ≤ _ := pow_le_pow_left₀ hs (le_max_left _ _) 2
            exact mul_le_mul_of_nonneg_right this (by positivity)
          · nlinarith [sq_nonneg (max (Real.sqrt q) a), sq_nonneg (1 + c)]
        · have ha0 : 0 ≤ a := by positivity
          have : a ^ 2 ≤ max (Real.sqrt q) a ^ 2 := pow_le_pow_left₀ ha0 (le_max_right _ _) 2
          have hac : a * (1 + c) = c := by rw [ha, div_mul_cancel₀ _ h1c.ne']
          calc c ^ 2 = (a * (1 + c)) ^ 2 := by rw [hac]
            _ = a ^ 2 * (1 + c) ^ 2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)
      have hq' : q * (1 + c) ^ 2 = (1 + c) ^ 2 - c * δ ^ 2 := by
        rw [hq]; field_simp
      rw [hval]
      refine le_trans ?_ hmax
      rw [hq']
      have hre : 2 * w.re ≤ 2 - δ ^ 2 := by nlinarith
      have key : (w.re * t + c) ^ 2 + (w.im * t) ^ 2 ≤
          (1 - t) * c ^ 2 + t * ((1 + c) ^ 2 - c * δ ^ 2) := by
        have e : (w.re * t + c) ^ 2 + (w.im * t) ^ 2 =
            t ^ 2 * (w.re ^ 2 + w.im ^ 2) + t * c * (2 * w.re) + c ^ 2 := by ring
        rw [e]
        have h1 : t ^ 2 * (w.re ^ 2 + w.im ^ 2) ≤ t := by nlinarith
        have h2 : t * c * (2 * w.re) ≤ t * c * (2 - δ ^ 2) :=
          mul_le_mul_of_nonneg_left hre (by positivity)
        nlinarith
      calc _ ≤ (1 - t) * c ^ 2 + t * ((1 + c) ^ 2 - c * δ ^ 2) := key
        _ ≤ (1 - t) * max ((1 + c) ^ 2 - c * δ ^ 2) (c ^ 2) +
            t * max ((1 + c) ^ 2 - c * δ ^ 2) (c ^ 2) := by
          gcongr <;> first | exact le_max_right _ _ | exact le_max_left _ _
        _ = _ := by ring
    have h0 : 0 ≤ max (Real.sqrt q) a * (1 + c) :=
      mul_nonneg (le_max_of_le_left (Real.sqrt_nonneg q)) h1c.le
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp hsq
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) h1c.le
  · -- `t ∈ [−1 + c′, 0)`: `|wt + c| ≤ −t + c ≤ 1 − c′ + c`
    calc ‖w * (t : ℂ) + c‖ ≤ ‖w * (t : ℂ)‖ + ‖(c : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 * (-t) + c := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc.le,
            Real.norm_eq_abs, abs_of_neg ht]
          gcongr
          linarith
      _ ≤ (1 - c' / (1 + c)) * (1 + c) := by
          rw [sub_mul, div_mul_cancel₀ _ h1c.ne']; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) h1c.le

/-- The derivatives of `t ↦ K (a + bt)^j` on `ℝ`. -/
private lemma torusCont_iteratedDeriv (a b K : ℂ) (j l : ℕ) :
    iteratedDeriv l (fun t : ℝ => K * (a + b * t) ^ j) =
      fun t : ℝ => K * (j.descFactorial l : ℂ) * b ^ l * (a + b * t) ^ (j - l) := by
  induction l with
  | zero => funext t; simp
  | succ l ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h1 : HasDerivAt (fun t : ℝ => a + b * (t : ℂ)) (b * 1) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul b).const_add a
    have h : HasDerivAt
        (fun t : ℝ => K * (j.descFactorial l : ℂ) * b ^ l * (a + b * t) ^ (j - l))
        (K * (j.descFactorial l : ℂ) * b ^ l *
          (((j - l : ℕ) : ℂ) * (a + b * t) ^ (j - l - 1) * (b * 1))) t :=
      (h1.fun_pow (j - l)).const_mul _
    rw [h.deriv, Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

/-- `G_n(t) = Σ_{j<n} b a^{n−1−j} (a + bt)^j`, so that `t G_n(t) = (a + bt)^n − a^n`. -/
private def torusContG (a b : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, b * a ^ (n - 1 - j) * (a + b * t) ^ j

/-- `G_n` is smooth. -/
private lemma torusContG_contDiff (a b : ℂ) (n : ℕ) :
    ContDiff ℝ ⊤ (torusContG a b n) := by
  have hof : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  unfold torusContG
  fun_prop

/-- `t G_n(t) = (a + bt)^n − a^n`. -/
private lemma torusContG_mul (a b : ℂ) (n : ℕ) (t : ℝ) :
    (t : ℂ) * torusContG a b n t = (a + b * t) ^ n - a ^ n := by
  rw [← geom_sum₂_mul, torusContG, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `|G_n^{(l)}(t)| ≤ n^{l+1} ρ^{n−1−l}` when `|a|, |a + bt| ≤ ρ` and `|b| ≤ 1`. -/
private lemma torusContG_bound (a b : ℂ) (n l : ℕ) {ρ : ℝ} (ha : ‖a‖ ≤ ρ) (hb : ‖b‖ ≤ 1)
    (t : ℝ) (ht : ‖a + b * t‖ ≤ ρ) :
    ‖iteratedFDeriv ℝ l (torusContG a b n) t‖ ≤ (n : ℝ) ^ (l + 1) * ρ ^ (n - 1 - l) := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans ha
  have hfun : torusContG a b n =
      fun t : ℝ => ∑ j ∈ Finset.range n, b * a ^ (n - 1 - j) * (a + b * t) ^ j := rfl
  have hof : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  rw [hfun, iteratedFDeriv_fun_sum_apply (fun j _ =>
    (by fun_prop :
      ContDiff ℝ ⊤ (fun t : ℝ => b * a ^ (n - 1 - j) * (a + b * t) ^ j)).contDiffAt.of_le
      le_top)]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ j ∈ Finset.range n,
      ‖iteratedFDeriv ℝ l (fun t : ℝ => b * a ^ (n - 1 - j) * (a + b * t) ^ j) t‖ ≤
        (n : ℝ) ^ l * ρ ^ (n - 1 - l) := by
    intro j hj
    have hjn := Finset.mem_range.mp hj
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, torusCont_iteratedDeriv]
    rcases lt_or_ge j l with hjl | hlj
    · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hjl]
      simp only [Nat.cast_zero, mul_zero, zero_mul, norm_zero]
      positivity
    · simp only [norm_mul, norm_pow, Complex.norm_natCast]
      have hd : ((j.descFactorial l : ℕ) : ℝ) ≤ (n : ℝ) ^ l := by
        have := (Nat.descFactorial_le_pow j l).trans (Nat.pow_le_pow_left hjn.le l)
        exact_mod_cast this
      have hexp : ρ ^ (n - 1 - j) * ρ ^ (j - l) = ρ ^ (n - 1 - l) := by
        rw [← pow_add]; congr 1; omega
      have h1 : ‖a‖ ^ (n - 1 - j) ≤ ρ ^ (n - 1 - j) := pow_le_pow_left₀ (norm_nonneg _) ha _
      have h2 : ‖a + b * t‖ ^ (j - l) ≤ ρ ^ (j - l) := pow_le_pow_left₀ (norm_nonneg _) ht _
      have h3 : ‖b‖ ^ l ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
      calc ‖b‖ * ‖a‖ ^ (n - 1 - j) * (j.descFactorial l : ℝ) * ‖b‖ ^ l * ‖a + b * t‖ ^ (j - l)
          ≤ 1 * ρ ^ (n - 1 - j) * (n : ℝ) ^ l * 1 * ρ ^ (j - l) := by gcongr
        _ = (n : ℝ) ^ l * ρ ^ (n - 1 - l) := by rw [← hexp]; ring
  calc _ ≤ ∑ j ∈ Finset.range n, (n : ℝ) ^ l * ρ ^ (n - 1 - l) := Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `n^{i+1} ρ^{n−1−i}` is monotone in `i` for `n ≥ 1`, `0 ≤ ρ ≤ 1`. -/
private lemma torusCont_beta_mono {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {i j : ℕ} (hij : i ≤ j) :
    (n : ℝ) ^ (i + 1) * ρ ^ (n - 1 - i) ≤ (n : ℝ) ^ (j + 1) * ρ ^ (n - 1 - j) :=
  mul_le_mul (pow_le_pow_right₀ (by exact_mod_cast hn) (by omega))
    (pow_le_pow_of_le_one hρ0 hρ1 (by omega)) (by positivity) (by positivity)

/-- The derivatives of `G_n ∘ ψ`, by the chain rule bound for iterated derivatives. -/
private lemma torusContH_bound {d : ℕ} (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (a b : ℂ)
    (n j : ℕ) {ρ : ℝ} (ha : ‖a‖ ≤ ρ) (hb : ‖b‖ ≤ 1) (hρ1 : ρ ≤ 1) (hn : 1 ≤ n)
    (hψ : ∀ x, ‖a + b * (ψ x : ℂ)‖ ≤ ρ) {D : ℝ} (hD1 : 1 ≤ D)
    (hD : ∀ l ≤ j, SchwartzMap.seminorm ℝ 0 l ψ ≤ D) (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ j (torusContG a b n ∘ ψ) x‖ ≤
      (j.factorial : ℝ) * ((n : ℝ) ^ (j + 1) * ρ ^ (n - 1 - j)) * D ^ j := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans ha
  refine norm_iteratedFDeriv_comp_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((torusContG_contDiff a b n).of_le le_top) (ψ.smooth ⊤) (by exact_mod_cast le_top) x
    (fun i hi => ?_) (fun i hi1 hij => ?_)
  · exact (torusContG_bound a b n i ha hb _ (hψ x)).trans
      (torusCont_beta_mono hn hρ0 hρ1 hi)
  · calc ‖iteratedFDeriv ℝ i ψ x‖ ≤ SchwartzMap.seminorm ℝ 0 i ψ :=
          SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ψ i x
      _ ≤ D := hD i hij
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)

/-- The constant `i! D_i^i Σ_{l ≤ i} C(i, l) ‖ψ‖_{k,l}`, `D_i = 1 + Σ_{l ≤ i} ‖ψ‖_{0,l}`. -/
private def torusContQ {d : ℕ} (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (k i : ℕ) : ℝ :=
  (i.factorial : ℝ) * (1 + ∑ l ∈ Finset.range (i + 1), SchwartzMap.seminorm ℝ 0 l ψ) ^ i *
    ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * SchwartzMap.seminorm ℝ k l ψ

/-- `torusContQ` is nonnegative. -/
private lemma torusContQ_nonneg {d : ℕ} (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (k i : ℕ) :
    0 ≤ torusContQ ψ k i := by
  unfold torusContQ
  have : 0 ≤ ∑ l ∈ Finset.range (i + 1), SchwartzMap.seminorm ℝ 0 l ψ :=
    Finset.sum_nonneg fun l _ => apply_nonneg _ _
  have : 0 ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * SchwartzMap.seminorm ℝ k l ψ :=
    Finset.sum_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  positivity

/-- `A_ψ^n − a^n = ψ · (G_n ∘ ψ)` with `a = c/(1 + c)`, `b = m²/(1 + c)`. -/
private lemma torusSymbolPow_eq {d : ℕ} (m : ℂ) (c : ℝ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (n : ℕ) : contSymbolPow m c ψ n = fun y => (ψ y : ℂ) *
      (torusContG ((c : ℂ) / (1 + c)) (m ^ 2 / (1 + c)) n ∘ ψ) y := by
  funext y
  rw [Function.comp_apply, torusContG_mul, contSymbolPow]
  congr 2
  ring

/-- The Schwartz bound `‖p‖^k |∂^i(A_ψ^n − a^n)(p)| ≤ Q_{k,i} n^{i+1} ρ^{n−1−i}`, uniform in `m`,
by the Leibniz rule applied to `ψ · (G_n ∘ ψ)`. -/
private lemma torusSymbolPow_bound {d : ℕ} (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (m : ℂ) (c : ℝ)
    (n : ℕ) {ρ : ℝ} (ha : ‖(c : ℂ) / (1 + c)‖ ≤ ρ) (hb : ‖m ^ 2 / (1 + c)‖ ≤ 1) (hρ1 : ρ ≤ 1)
    (hn : 1 ≤ n) (hψ : ∀ x, ‖(c : ℂ) / (1 + c) + m ^ 2 / (1 + c) * (ψ x : ℂ)‖ ≤ ρ)
    (k i : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ i (contSymbolPow m c ψ n) x‖ ≤
      torusContQ ψ k i * ((n : ℝ) ^ (i + 1) * ρ ^ (n - 1 - i)) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans ha
  set G := torusContG ((c : ℂ) / (1 + c)) (m ^ 2 / (1 + c)) n with hG
  set D := 1 + ∑ l ∈ Finset.range (i + 1), SchwartzMap.seminorm ℝ 0 l ψ with hDdef
  have hD0 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SchwartzMap.seminorm ℝ 0 l ψ :=
    Finset.sum_nonneg fun l _ => apply_nonneg _ _
  have hD1 : 1 ≤ D := by rw [hDdef]; linarith
  have hDl : ∀ l ≤ i, SchwartzMap.seminorm ℝ 0 l ψ ≤ D := by
    intro l hl
    have : SchwartzMap.seminorm ℝ 0 l ψ ≤
        ∑ l ∈ Finset.range (i + 1), SchwartzMap.seminorm ℝ 0 l ψ :=
      Finset.single_le_sum (f := fun l => SchwartzMap.seminorm ℝ 0 l ψ)
        (fun l _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
    rw [hDdef]; linarith
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (ψ y : ℂ)) :=
    ofRealCLM.contDiff.comp (ψ.smooth ⊤)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G ∘ ψ) :=
    ((torusContG_contDiff _ _ n).of_le le_top).comp (ψ.smooth ⊤)
  rw [torusSymbolPow_eq, ← hG]
  have hL := norm_iteratedFDeriv_mul_le hf hg x (n := i) (by exact_mod_cast le_top)
  have hψl : ∀ l, ‖iteratedFDeriv ℝ l (fun y => (ψ y : ℂ)) x‖ = ‖iteratedFDeriv ℝ l ψ x‖ :=
    fun l => ofRealLI.norm_iteratedFDeriv_comp_left (ψ.smooth ⊤).contDiffAt
      (by exact_mod_cast le_top)
  have hH : ∀ l ∈ Finset.range (i + 1), ‖iteratedFDeriv ℝ (i - l) (G ∘ ψ) x‖ ≤
      (i.factorial : ℝ) * ((n : ℝ) ^ (i + 1) * ρ ^ (n - 1 - i)) * D ^ i := by
    intro l hl
    have hli := Finset.mem_range.mp hl
    refine (torusContH_bound ψ _ _ n (i - l) ha hb hρ1 hn hψ hD1
      (fun l' hl' => hDl l' (by omega)) x).trans ?_
    have hβ0 : 0 ≤ (n : ℝ) ^ (i - l + 1) * ρ ^ (n - 1 - (i - l)) := by positivity
    exact mul_le_mul (mul_le_mul (by exact_mod_cast Nat.factorial_le (Nat.sub_le i l))
      (torusCont_beta_mono hn hρ0 hρ1 (Nat.sub_le i l)) hβ0 (by positivity))
      (pow_le_pow_right₀ hD1 (Nat.sub_le i l)) (by positivity) (by positivity)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ i (fun y => (ψ y : ℂ) * (G ∘ ψ) y) x‖
      ≤ ‖x‖ ^ k * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
          ‖iteratedFDeriv ℝ l (fun y => (ψ y : ℂ)) x‖ *
          ‖iteratedFDeriv ℝ (i - l) (G ∘ ψ) x‖ := by gcongr
    _ = ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ l ψ x‖) * ‖iteratedFDeriv ℝ (i - l) (G ∘ ψ) x‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hψl]; ring
    _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * SchwartzMap.seminorm ℝ k l ψ *
          ((i.factorial : ℝ) * ((n : ℝ) ^ (i + 1) * ρ ^ (n - 1 - i)) * D ^ i) := by
        refine Finset.sum_le_sum fun l hl => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℝ k l ψ x
        · exact hH l hl
    _ = _ := by
        rw [← Finset.sum_mul, torusContQ, ← hDdef]; ring

/-- The symbol `A_ψ^n − a^n` is smooth. -/
private lemma torusSymbolPow_contDiff {d : ℕ} (m : ℂ) (c : ℝ)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (contSymbolPow m c ψ n) := by
  rw [torusSymbolPow_eq]
  exact (ofRealCLM.contDiff.comp (ψ.smooth ⊤)).mul
    (((torusContG_contDiff _ _ n).of_le le_top).comp (ψ.smooth ⊤))

/-- The `L¹` norm of `𝓕⁻ F` is controlled by finitely many Schwartz seminorms of `F`. -/
private lemma torusCont_L1 (d : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ F : 𝓢(EuclideanSpace ℝ (Fin d), ℂ),
      ∫ y, ‖(𝓕⁻ F) y‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin d)) ℂ)) F := by
  let T : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) →L[ℂ]
      Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (SchwartzMap.toLpCLM ℂ ℂ 1 volume).comp
      (FourierTransform.fourierInvCLM ℂ 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
  let q : Seminorm ℂ 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    (normSeminorm ℂ (Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, -, hC⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin d)) ℂ) q hq
  refine ⟨s, C, C.2, fun F => ?_⟩
  have h := hC F
  rw [← SchwartzMap.norm_toLp_one]
  exact h

/-- A power `n ≥ N + 1` with `a^n + K n^{N+1} ρ^{n−1−N} ≤ 1/2`, for `a, ρ ∈ (0, 1)`. -/
private lemma torusCont_exists_n {ar ρ K : ℝ} (N : ℕ) (ha0 : 0 ≤ ar) (ha1 : ar < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ n : ℕ, N + 1 ≤ n ∧ ar ^ n + K * ((n : ℝ) ^ (N + 1) * ρ ^ (n - 1 - N)) ≤ 1 / 2 := by
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  have h2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one (N + 1)
    (by rw [abs_of_pos hρ0]; exact hρ1)
  have h3 : Filter.Tendsto (fun n : ℕ => ar ^ n + K * ((n : ℝ) ^ (N + 1) * ρ ^ n) *
      (ρ ^ (N + 1))⁻¹) Filter.atTop (nhds 0) := by
    simpa using h1.add ((h2.const_mul K).mul_const (ρ ^ (N + 1))⁻¹)
  obtain ⟨n, hn1, hn2⟩ := ((h3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
    (Filter.eventually_ge_atTop (N + 1))).exists
  refine ⟨n, hn2, le_of_lt ?_⟩
  have he : ρ ^ (n - 1 - N) = ρ ^ n * (ρ ^ (N + 1))⁻¹ := by
    rw [show n - 1 - N = n - (N + 1) by omega, pow_sub₀ ρ hρ0.ne' hn2]
  rw [he]
  calc _ = ar ^ n + K * ((n : ℝ) ^ (N + 1) * ρ ^ n) * (ρ ^ (N + 1))⁻¹ := by ring
    _ < 1 / 2 := hn1

end ContBounds

/-! ## Smoothed kernels on `Z_L^d` -/

section Torus1
variable {L : ℕ} [NeZero L]

/-- `conj ψ(x) = ψ(−x)` for the standard character of `ZMod L`. -/
private theorem conj_stdAddChar (x : ZMod L) :
    conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  have h1 : (ZMod.stdAddChar x : ℂ) * ZMod.stdAddChar (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hn : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := AddChar.norm_apply _ _
  have h2 : conj (ZMod.stdAddChar x : ℂ) * ZMod.stdAddChar x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hne : (ZMod.stdAddChar x : ℂ) ≠ 0 := by
    intro h; rw [h] at hn; simp at hn
  exact mul_left_cancel₀ hne (by rw [h1, mul_comm, h2])

/-- Orthogonality: `Σ_w ψ(b w) = L·1(b = 0)`. -/
private theorem sum_stdAddChar_mul (b : ZMod L) :
    ∑ w : ZMod L, (ZMod.stdAddChar (b * w) : ℂ) = if b = 0 then (L : ℂ) else 0 := by
  have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar (N := L))) b
    (ZMod.isPrimitive_stdAddChar L)
  simpa [mul_comm, ZMod.card] using this

/-- Parseval for a sum of characters with distinct frequencies mod `L` and unimodular weights:
`Σ_w |Σ_{i∈P} φ(i) e^{2πi i w/L}|² = L·|P|`. -/
private theorem sum_norm_sq_charSum (P : Finset ℤ)
    (hP : ∀ i ∈ P, ∀ i' ∈ P, ((i : ZMod L)) = (i' : ZMod L) → i = i')
    (φ : ℤ → ℂ) (hφ : ∀ j, ‖φ j‖ = 1) :
    ∑ w : ZMod L, ‖∑ i ∈ P, φ i * ZMod.stdAddChar ((i : ZMod L) * w)‖ ^ 2 =
      (L : ℝ) * P.card := by
  have key : ((∑ w : ZMod L, ‖∑ i ∈ P, φ i * ZMod.stdAddChar ((i : ZMod L) * w)‖ ^ 2 : ℝ) : ℂ)
      = (L : ℂ) * P.card := by
    push_cast
    have hX : ∀ X : ℂ, ((‖X‖ : ℂ)) ^ 2 = X * conj X := by
      intro X; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    simp_rw [hX, map_sum, map_mul, conj_stdAddChar, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hin : ∀ i ∈ P, ∑ w : ZMod L, ∑ i' ∈ P, φ i * ZMod.stdAddChar ((i : ZMod L) * w) *
        (conj (φ i') * ZMod.stdAddChar (-((i' : ZMod L) * w))) = (L : ℂ) := by
      intro i hi
      rw [Finset.sum_comm]
      have : ∀ i' ∈ P, ∑ w : ZMod L, φ i * ZMod.stdAddChar ((i : ZMod L) * w) *
          (conj (φ i') * ZMod.stdAddChar (-((i' : ZMod L) * w))) =
          if i' = i then (L : ℂ) else 0 := by
        intro i' hi'
        have hs : ∀ w : ZMod L, φ i * ZMod.stdAddChar ((i : ZMod L) * w) *
            (conj (φ i') * ZMod.stdAddChar (-((i' : ZMod L) * w))) =
            φ i * conj (φ i') * ZMod.stdAddChar (((i : ZMod L) - (i' : ZMod L)) * w) := by
          intro w
          rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
          ring
        simp_rw [hs]
        rw [← Finset.mul_sum, sum_stdAddChar_mul]
        by_cases h : i' = i
        · subst h
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hφ]
          simp
        · have : ((i : ZMod L) - (i' : ZMod L)) ≠ 0 := by
            intro h0
            exact h (hP i' hi' i hi (sub_eq_zero.mp h0).symm)
          simp [this, h]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' P i]
      simp [hi]
    rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact_mod_cast key

/-- The trapezoidal weight `χ_M(j) = M⁻¹ #{b ∈ [0, M) : |j − b| ≤ 2M}`: the convolution of the
indicator of `[−2M, 2M]` with the uniform probability on `[0, M)`. -/
private def vpWeight (M : ℕ) (j : ℤ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ b ∈ Finset.Ico (0 : ℤ) M, if |j - b| ≤ 2 * M then (1 : ℝ) else 0

private theorem vpWeight_eq_one {M : ℕ} (hM : 1 ≤ M) {j : ℤ} (hj : |j| ≤ M) :
    vpWeight M j = 1 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  unfold vpWeight
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) fun b hb => by
    rw [Finset.mem_Ico] at hb
    have : |j - b| ≤ 2 * M := by
      rw [abs_le] at hj ⊢
      constructor <;> omega
    simp [this]]
  simp [hM']

private theorem vpWeight_nonneg (M : ℕ) (j : ℤ) : 0 ≤ vpWeight M j := by
  unfold vpWeight
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => ?_)
  split_ifs <;> norm_num

private theorem vpWeight_le_one (M : ℕ) (j : ℤ) : vpWeight M j ≤ 1 := by
  unfold vpWeight
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  calc (M : ℝ)⁻¹ * ∑ b ∈ Finset.Ico (0 : ℤ) M, (if |j - b| ≤ 2 * M then (1 : ℝ) else 0)
      ≤ (M : ℝ)⁻¹ * ∑ b ∈ Finset.Ico (0 : ℤ) M, (1 : ℝ) := by
        gcongr with b
        split_ifs <;> norm_num
    _ = 1 := by
        rw [Finset.sum_const, Int.card_Ico, sub_zero, Int.toNat_natCast, nsmul_eq_mul, mul_one,
          inv_mul_cancel₀ hM'.ne']

private theorem vpWeight_support {M : ℕ} {j : ℤ} (h : vpWeight M j ≠ 0) :
    j ∈ Finset.Icc (-2 * (M : ℤ)) (3 * M) := by
  unfold vpWeight at h
  obtain ⟨b, hb, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h)
  rw [Finset.mem_Ico] at hb
  have : |j - b| ≤ 2 * M := by by_contra hc; exact hne (by simp [hc])
  rw [abs_le] at this
  rw [Finset.mem_Icc]
  constructor <;> omega

/-- A sum over `ZMod L` of a function of `valMinAbs` equals the sum over `ℤ` when the function
is supported in a finite set of integers in `(−L/2, L/2]`. -/
private theorem sum_valMinAbs_eq (J : Finset ℤ) (hJ : ∀ j ∈ J, -(L : ℤ) < j * 2 ∧ j * 2 ≤ L)
    (G : ℤ → ℂ) (hG : ∀ j, G j ≠ 0 → j ∈ J) :
    ∑ κ : ZMod L, G κ.valMinAbs = ∑ j ∈ J, G j := by
  refine Finset.sum_bij_ne_zero (fun κ _ _ => κ.valMinAbs) (fun κ _ h => hG _ h)
    (fun κ _ _ κ' _ _ h => ZMod.valMinAbs_inj.mp h) (fun j hj hGj => ?_) (fun _ _ _ => rfl)
  refine ⟨(j : ZMod L), Finset.mem_univ _, ?_, ?_⟩
  · rwa [((ZMod.valMinAbs_spec _ j).mpr ⟨rfl, hJ j hj⟩)]
  · exact (ZMod.valMinAbs_spec _ j).mpr ⟨rfl, hJ j hj⟩

omit [NeZero L] in
/-- Integers at distance less than `L` are distinct modulo `L`. -/
private theorem intCast_inj_of_abs {i i' : ℤ} (h : |i - i'| < L)
    (he : (i : ZMod L) = (i' : ZMod L)) : i = i' := by
  have hd : (L : ℤ) ∣ i - i' := (ZMod.intCast_eq_intCast_iff_dvd_sub i' i L).mp he.symm
  have := Int.eq_zero_of_abs_lt_dvd hd h
  omega

/-- The `ℓ¹` bound for the smoothed one-dimensional kernel with a real phase:
`Σ_w |L⁻¹ Σ_κ χ_M(κ) φ(κ) e^{2πi κ w/L}| ≤ 3`, for `8M ≤ L` and a unimodular multiplicative `φ`. -/
private theorem sum_norm_vpKernel_le {M : ℕ} (hM : 1 ≤ M) (hML : 8 * M ≤ L) (φ : ℤ → ℂ)
    (hφm : ∀ a b, φ (a + b) = φ a * φ b) (hφ : ∀ j, ‖φ j‖ = 1) :
    ∑ w : ZMod L, ‖(L : ℂ)⁻¹ * ∑ κ : ZMod L, (vpWeight M κ.valMinAbs : ℂ) * φ κ.valMinAbs *
      ZMod.stdAddChar (κ * w)‖ ≤ 3 := by
  set ω : ZMod L → ℤ → ℂ := fun w j => φ j * ZMod.stdAddChar ((j : ZMod L) * w) with hω
  have hωm : ∀ w a b, ω w (a + b) = ω w a * ω w b := by
    intro w a b
    simp only [hω, hφm, Int.cast_add, add_mul, AddChar.map_add_eq_mul]
    ring
  set PA := Finset.Icc (-2 * (M : ℤ)) (2 * M) with hPA
  set PB := Finset.Ico (0 : ℤ) M with hPB
  set A : ZMod L → ℂ := fun w => ∑ i ∈ PA, ω w i with hA
  set B : ZMod L → ℂ := fun w => ∑ b ∈ PB, ω w b with hB
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hLR : (0 : ℝ) < L := by exact_mod_cast (NeZero.pos L)
  -- the inner sum factorises
  have hfac : ∀ w : ZMod L, ∑ κ : ZMod L, (vpWeight M κ.valMinAbs : ℂ) * φ κ.valMinAbs *
      ZMod.stdAddChar (κ * w) = (M : ℂ)⁻¹ * (A w * B w) := by
    intro w
    have h1 : ∀ κ : ZMod L, (vpWeight M κ.valMinAbs : ℂ) * φ κ.valMinAbs *
        ZMod.stdAddChar (κ * w) = (vpWeight M κ.valMinAbs : ℂ) * ω w κ.valMinAbs := by
      intro κ
      simp only [hω, ZMod.coe_valMinAbs]
      ring
    simp_rw [h1]
    rw [sum_valMinAbs_eq (Finset.Icc (-2 * (M : ℤ)) (3 * M)) (fun j hj => by
        rw [Finset.mem_Icc] at hj; constructor <;> omega)
      (fun j => (vpWeight M j : ℂ) * ω w j) (fun j hj => by
        apply vpWeight_support
        intro h0; apply hj; rw [h0]; simp)]
    simp only [vpWeight, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_sum, mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm, hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_Ico] at hb
    simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hfil : (Finset.Icc (-2 * (M : ℤ)) (3 * M)).filter (fun j => |j - b| ≤ 2 * M) =
        (PA).map (addRightEmbedding b) := by
      rw [hPA, Finset.map_add_right_Icc]
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, abs_le]
      constructor
      · intro h; constructor <;> omega
      · intro h; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
    rw [hfil, Finset.sum_map]
    simp only [hA, addRightEmbedding_apply, hωm, Finset.sum_mul]
  -- Parseval for `A` and `B`
  have hAs : ∑ w : ZMod L, ‖A w‖ ^ 2 = (L : ℝ) * (4 * M + 1) := by
    rw [sum_norm_sq_charSum PA (fun i hi i' hi' he => intCast_inj_of_abs (by
        rw [hPA, Finset.mem_Icc] at hi hi'
        rw [abs_lt]; constructor <;> omega) he) φ hφ]
    rw [hPA, Int.card_Icc]
    congr 1
    have : (2 * (M : ℤ) + 1 - -2 * M).toNat = 4 * M + 1 := by omega
    rw [this]; push_cast; ring
  have hBs : ∑ w : ZMod L, ‖B w‖ ^ 2 = (L : ℝ) * M := by
    rw [sum_norm_sq_charSum PB (fun i hi i' hi' he => intCast_inj_of_abs (by
        rw [hPB, Finset.mem_Ico] at hi hi'
        rw [abs_lt]; constructor <;> omega) he) φ hφ]
    rw [hPB, Int.card_Ico, sub_zero, Int.toNat_natCast]
  -- Cauchy–Schwarz
  have hCS : (∑ w : ZMod L, ‖A w‖ * ‖B w‖) ^ 2 ≤
      (∑ w : ZMod L, ‖A w‖ ^ 2) * ∑ w : ZMod L, ‖B w‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hAB : ∑ w : ZMod L, ‖A w‖ * ‖B w‖ ≤ 3 * L * M := by
    rw [hAs, hBs] at hCS
    have h0 : 0 ≤ 3 * (L : ℝ) * M := by positivity
    have : (∑ w : ZMod L, ‖A w‖ * ‖B w‖) ^ 2 ≤ (3 * (L : ℝ) * M) ^ 2 := by
      refine hCS.trans ?_
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      have : (4 * (M : ℝ) + 1) * M ≤ 9 * M * M := by nlinarith
      nlinarith [sq_nonneg (L : ℝ)]
    exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun w _ => by positivity) h0
      two_ne_zero).mp this
  calc ∑ w : ZMod L, ‖(L : ℂ)⁻¹ * ∑ κ : ZMod L, (vpWeight M κ.valMinAbs : ℂ) * φ κ.valMinAbs *
        ZMod.stdAddChar (κ * w)‖
      = ∑ w : ZMod L, ((L : ℝ) * M)⁻¹ * (‖A w‖ * ‖B w‖) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hfac w, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_natCast,
          Complex.norm_natCast, mul_inv]
        ring
    _ = ((L : ℝ) * M)⁻¹ * ∑ w : ZMod L, ‖A w‖ * ‖B w‖ := by rw [Finset.mul_sum]
    _ ≤ ((L : ℝ) * M)⁻¹ * (3 * L * M) := by gcongr
    _ = 3 := by field_simp

end Torus1

section TorusD
variable {d L : ℕ} [NeZero L]

/-- The phase `j ↦ e^{2πi t j}` on `ℤ`. -/
private def phase (t : ℝ) (j : ℤ) : ℂ := cexp (((2 * Real.pi * (t * j) : ℝ) : ℂ) * I)

private theorem phase_add (t : ℝ) (a b : ℤ) : phase t (a + b) = phase t a * phase t b := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_phase (t : ℝ) (j : ℤ) : ‖phase t j‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The product weight `χ(k) = Π_i χ_M(k_i)` on `Z_L^d`. -/
private def vpWeightD (M : ℕ) (k : Zd d L) : ℝ := ∏ i, vpWeight M (k i).valMinAbs

omit [NeZero L] in
/-- `⟨v, W p_k⟩ = Σ_i (2π W v_i / L) k_i`. -/
private theorem inner_smul_zfreq (v : EuclideanSpace ℝ (Fin d)) (W : ℕ) (k : Zd d L) :
    inner ℝ v ((W : ℝ) • zfreq k) =
      ∑ i, (v i * W / L) * ((k i).valMinAbs : ℝ) * (2 * Real.pi) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((W : ℝ) • zfreq k) i = W * (2 * Real.pi * ((k i).valMinAbs : ℝ) / L) := rfl
  rw [this, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp only [RCLike.re_to_real]
  ring

/-- The smoothed Dirichlet kernel on `Z_L^d` shifted by the real vector `2πW v`:
`D(v, z) = L^{−d} Σ_k χ(k) e^{−2πi ⟨v, W p_k⟩} e^{i p_k·z}`. -/
private def smoothKernel (M W : ℕ) (v : EuclideanSpace ℝ (Fin d)) (z : Zd d L) : ℂ :=
  ((L : ℂ) ^ d)⁻¹ * ∑ k : Zd d L, (vpWeightD M k : ℂ) *
    cexp (((2 * Real.pi * -inner ℝ v ((W : ℝ) • zfreq k) : ℝ) : ℂ) * I) * zchar k z

/-- `Σ_z |D(v, z)| ≤ 3^d`, uniformly in `v`, for `8M ≤ L`, `M ≥ 1`. -/
private theorem sum_norm_smoothKernel_le {M : ℕ} (hM : 1 ≤ M) (hML : 8 * M ≤ L) (W : ℕ)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∑ z : Zd d L, ‖smoothKernel M W v z‖ ≤ 3 ^ d := by
  set t : Fin d → ℝ := fun i => -(v i * W / L * (2 * Real.pi)) with ht
  set D1 : Fin d → ZMod L → ℂ := fun i w => (L : ℂ)⁻¹ * ∑ κ : ZMod L,
    (vpWeight M κ.valMinAbs : ℂ) * phase (t i) κ.valMinAbs * ZMod.stdAddChar (κ * w) with hD1
  have hfac : ∀ z : Zd d L, smoothKernel M W v z = ∏ i, D1 i (z i) := by
    intro z
    simp only [hD1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fintype.prod_sum, smoothKernel, inv_pow]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [vpWeightD, zchar, Complex.ofReal_prod, inner_smul_zfreq]
    congr 1
    congr 1
    simp only [phase]
    rw [← Complex.exp_sum]
    congr 1
    simp only [ht]
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1 : ∀ i, ∑ w : ZMod L, ‖D1 i w‖ ≤ 3 := fun i =>
    sum_norm_vpKernel_le hM hML (phase (t i)) (phase_add (t i)) (norm_phase (t i))
  calc ∑ z : Zd d L, ‖smoothKernel M W v z‖ = ∑ z : Zd d L, ∏ i, ‖D1 i (z i)‖ := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hfac, norm_prod]
    _ = ∏ i, ∑ w : ZMod L, ‖D1 i w‖ := (Fintype.prod_sum (fun i w => ‖D1 i w‖)).symm
    _ ≤ ∏ _i : Fin d, (3 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun w _ => norm_nonneg _)
          fun i _ => h1 i
    _ = 3 ^ d := by simp

/-- The shifted kernel is continuous in the shift. -/
private theorem continuous_smoothKernel (M W : ℕ) (z : Zd d L) :
    Continuous fun v : EuclideanSpace ℝ (Fin d) => smoothKernel M W v z := by
  unfold smoothKernel
  fun_prop

/-- A Schwartz function as the Fourier transform of its inverse transform, written with the
complex exponential. -/
private theorem schwartz_eq_integral (F : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (q : EuclideanSpace ℝ (Fin d)) :
    F q = ∫ v, cexp (((2 * Real.pi * -inner ℝ v q : ℝ) : ℂ) * I) * (𝓕⁻ F) v := by
  have h0 : (𝓕 (𝓕⁻ F) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) = F :=
    FourierTransform.fourier_fourierInv_eq F
  have h : (𝓕 (𝓕⁻ F) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) q = F q := by rw [h0]
  rw [← h, SchwartzMap.fourier_coe, Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]

/-- The main term: the lattice kernel with symbol `χ(k) F(W p_k)` has `ℓ¹` norm at most
`3^d ‖𝓕⁻ F‖_{L¹}`, for `8M ≤ L`, `M ≥ 1`. -/
private theorem rowL1_main_le {M : ℕ} (hM : 1 ≤ M) (hML : 8 * M ≤ L) (W : ℕ)
    (F : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    ∑ z : Zd d L, ‖((L : ℂ) ^ d)⁻¹ * ∑ k : Zd d L,
      (vpWeightD M k : ℂ) * F ((W : ℝ) • zfreq k) * zchar k z‖ ≤
      3 ^ d * ∫ v, ‖(𝓕⁻ F) v‖ := by
  set g := 𝓕⁻ F with hg
  have hgi : Integrable (fun v => g v) := g.integrable
  have hbd : ∀ v z, ‖smoothKernel M W v z‖ ≤ 3 ^ d := fun v z =>
    (Finset.single_le_sum (f := fun z => ‖smoothKernel M W v z‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ z)).trans (sum_norm_smoothKernel_le hM hML W v)
  have hint : ∀ z, Integrable (fun v => smoothKernel M W v z * g v) := fun z =>
    hgi.bdd_mul (continuous_smoothKernel M W z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => hbd v z)
  have hintn : ∀ z, Integrable (fun v => ‖g v‖ * ‖smoothKernel M W v z‖) := fun z => by
    refine (hint z).norm.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [norm_mul, mul_comm]
  have hrep : ∀ z, ((L : ℂ) ^ d)⁻¹ * ∑ k : Zd d L,
      (vpWeightD M k : ℂ) * F ((W : ℝ) • zfreq k) * zchar k z =
      ∫ v, smoothKernel M W v z * g v := by
    intro z
    have hterm : ∀ k : Zd d L, Integrable (fun v => (vpWeightD M k : ℂ) *
        cexp (((2 * Real.pi * -inner ℝ v ((W : ℝ) • zfreq k) : ℝ) : ℂ) * I) * zchar k z *
          g v) := by
      intro k
      refine hgi.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun v => ?_)
      rw [norm_mul, norm_mul, norm_zchar, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
        vpWeightD, Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => vpWeight_nonneg _ _)]
      simpa using Finset.prod_le_one₀ (fun i _ => vpWeight_nonneg _ _)
        (fun i _ => vpWeight_le_one M _)
    simp only [smoothKernel]
    simp_rw [mul_assoc ((L : ℂ) ^ d)⁻¹, Finset.sum_mul]
    rw [integral_const_mul, integral_finsetSum _ fun k _ => hterm k]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [schwartz_eq_integral F, ← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hg]
    ring
  calc ∑ z : Zd d L, ‖((L : ℂ) ^ d)⁻¹ * ∑ k : Zd d L,
        (vpWeightD M k : ℂ) * F ((W : ℝ) • zfreq k) * zchar k z‖
      = ∑ z : Zd d L, ‖∫ v, smoothKernel M W v z * g v‖ := by simp only [hrep]
    _ ≤ ∑ z : Zd d L, ∫ v, ‖g v‖ * ‖smoothKernel M W v z‖ := by
        refine Finset.sum_le_sum fun z _ => (norm_integral_le_integral_norm _).trans_eq ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only [norm_mul, mul_comm]
    _ = ∫ v, ‖g v‖ * ∑ z : Zd d L, ‖smoothKernel M W v z‖ := by
        rw [← integral_finsetSum _ fun z _ => hintn z]
        simp only [Finset.mul_sum]
    _ ≤ ∫ v, ‖g v‖ * 3 ^ d := by
        refine integral_mono ?_ (hgi.norm.mul_const _) fun v => ?_
        · exact (integrable_finsetSum Finset.univ fun z _ => hintn z).congr
            (Filter.Eventually.of_forall fun v => by simp only [Finset.mul_sum])
        · exact mul_le_mul_of_nonneg_left (sum_norm_smoothKernel_le hM hML W v) (norm_nonneg _)
    _ = 3 ^ d * ∫ v, ‖g v‖ := by rw [integral_mul_const, mul_comm]

/-- The `ℓ¹` norm `Σ_z |L^{−d} Σ_k F(k) e^{i p_k·z}|` of the lattice kernel with symbol `F`. -/
private def rowL1 (F : Zd d L → ℂ) : ℝ :=
  ∑ z : Zd d L, ‖((L : ℂ) ^ d)⁻¹ * ∑ k : Zd d L, F k * zchar k z‖

private theorem rowL1_add_le (F G : Zd d L → ℂ) : rowL1 (F + G) ≤ rowL1 F + rowL1 G := by
  unfold rowL1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  exact norm_add_le _ _

private theorem rowL1_const (a : ℂ) : rowL1 (fun _ : Zd d L => a) = ‖a‖ := by
  have hL : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  unfold rowL1
  have h : ∀ z : Zd d L, ∑ k : Zd d L, a * zchar k z = if z = 0 then a * (L : ℂ) ^ d else 0 := by
    intro z
    rw [← Finset.mul_sum]
    simp_rw [zchar_comm _ z]
    rw [sum_zchar]
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_eq_single (0 : Zd d L) (fun z _ hz => by simp [hz]) (by simp)]
  simp only [↓reduceIte]
  rw [mul_comm a, ← mul_assoc, inv_mul_cancel₀ hL, one_mul]

/-- The `ℓ²` bound: `(Σ_z |L^{−d} Σ_k E(k) e^{i p_k·z}|)² ≤ L^d sup_k |E(k)|²`. -/
private theorem rowL1_sq_le (E : Zd d L → ℂ) {B : ℝ} (hE : ∀ k, ‖E k‖ ≤ B) :
    rowL1 E ^ 2 ≤ (L : ℝ) ^ d * B ^ 2 := by
  have hL : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  have hLR : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (by exact_mod_cast NeZero.pos L) d
  have hB : 0 ≤ B := (norm_nonneg _).trans (hE 0)
  set f : Zd d L → ℂ := fun z => ((L : ℂ) ^ d)⁻¹ * ∑ k : Zd d L, E k * zchar k z with hf
  have hzdft : ∀ k', zdft f k' = E (-k') := by
    intro k'
    simp only [zdft, hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ k : Zd d L, ∑ z : Zd d L, zchar k' z * (((L : ℂ) ^ d)⁻¹ * (E k * zchar k z)) =
        ((L : ℂ) ^ d)⁻¹ * E k * (if k' + k = 0 then (L : ℂ) ^ d else 0) := by
      intro k
      rw [← sum_zchar (k' + k), Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [zchar_comm (k' + k) z, zchar_add, zchar_comm z k', zchar_comm z k]
      ring
    simp_rw [this]
    have hk : ∀ k : Zd d L, (k' + k = 0) ↔ (-k' = k) := fun k =>
      ⟨fun h => neg_eq_of_add_eq_zero_right h, fun h => by rw [← h, add_neg_cancel]⟩
    simp_rw [hk]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [mul_comm _ (E _), mul_assoc, inv_mul_cancel₀ hL, mul_one]
  have hpl : ∑ z, ‖f z‖ ^ 2 ≤ B ^ 2 := by
    rw [zdft_plancherel]
    simp_rw [hzdft]
    calc ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, ‖E (-k)‖ ^ 2
        ≤ ((L : ℝ) ^ d)⁻¹ * ∑ _k : Zd d L, B ^ 2 := by
          gcongr with k
          exact hE _
      _ = B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          field_simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Zd d L))
    (fun _ => (1 : ℝ)) (fun z => ‖f z‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul,
    mul_one] at hcs
  push_cast at hcs
  calc rowL1 E ^ 2 = (∑ z, ‖f z‖) ^ 2 := rfl
    _ ≤ (L : ℝ) ^ d * ∑ z, ‖f z‖ ^ 2 := hcs
    _ ≤ (L : ℝ) ^ d * B ^ 2 := by gcongr

end TorusD

/-! ## Translation-invariant kernels and `A_c` -/

section TorusMatrix

variable {d L : ℕ} [NeZero L]

/-- The operator norm of a translation-invariant kernel is at most the `ℓ¹` norm of the kernel
recovered from its symbol. -/
private theorem opNormInf_le_rowL1 (X : Matrix (Zd d L) (Zd d L) ℂ) (hX : TransInv X) :
    opNormInf X ≤ rowL1 (symbol X) := by
  refine opNormInf_le_of_rows _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  unfold rowL1
  refine le_of_eq (Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y => ?_)
  rw [kernel_inversion X hX x y]
  rfl

omit [NeZero L] in
private theorem transInv_Ashift (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : TransInv S) (m : ℂ)
    (c : ℝ) : TransInv (Ashift m c S) := by
  intro x y a
  simp only [Ashift, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, cmat,
    Matrix.map_apply, hS x y a, add_left_inj]

private theorem symbol_Ashift (S : Matrix (Zd d L) (Zd d L) ℝ) (m : ℂ) (c : ℝ) (k : Zd d L) :
    symbol (Ashift m c S) k = (m ^ 2 * symbol (cmat S) k + c) / (1 + c) := by
  rw [Ashift, (symbol_add_smul _ 0 _ k).2, (symbol_add_smul _ _ 0 k).1,
    (symbol_add_smul (cmat S) 0 _ k).2, (symbol_add_smul (1 : Matrix (Zd d L) (Zd d L) ℂ) 0 _ k).2,
    symbol_one]
  ring

private theorem transInv_pow_symbol (A : Matrix (Zd d L) (Zd d L) ℂ) (hA : TransInv A) (n : ℕ) :
    TransInv (A ^ n) ∧ ∀ k, symbol (A ^ n) k = symbol A k ^ n := by
  induction n with
  | zero =>
    refine ⟨fun x y a => ?_, fun k => by rw [pow_zero, pow_zero, symbol_one]⟩
    simp only [pow_zero, Matrix.one_apply, add_left_inj]
  | succ n ih =>
    refine ⟨?_, fun k => ?_⟩
    · rw [pow_succ]; exact TransInv_mul _ _ ih.1 hA
    · rw [pow_succ, symbol_mul _ _ ih.1 hA, ih.2 k, pow_succ]

end TorusMatrix

/-- `|x^n − y^n| ≤ n |x − y|` for `|x|, |y| ≤ 1`. -/
private theorem norm_pow_sub_pow_le {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * ‖x - y‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range n, ‖x ^ i * y ^ (n - 1 - i)‖ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_pow, norm_pow]
        simpa using mul_le_mul (pow_le_one₀ (norm_nonneg _) hx) (pow_le_one₀ (norm_nonneg _) hy)
          (by positivity) zero_le_one
    _ = n := by simp

/-- A frequency with some coordinate `|k_i| > M ≥ L/8 − 1` has `|W p_k| ≥ W/2`. -/
private theorem half_le_norm_smul_zfreq {d L : ℕ} [NeZero L] {M : ℕ} (hLM : L < 8 * (M + 1))
    (W : ℕ) (k : Zd d L) (i : Fin d) (hi : (M : ℤ) < |(k i).valMinAbs|) :
    (W : ℝ) / 2 ≤ ‖(W : ℝ) • zfreq k‖ := by
  have hcoord : |((W : ℝ) • zfreq k) i| ≤ ‖(W : ℝ) • zfreq k‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ((W : ℝ) • zfreq k) i
  refine le_trans ?_ hcoord
  have hqi : ((W : ℝ) • zfreq k) i = W * (2 * Real.pi * ((k i).valMinAbs : ℝ) / L) := rfl
  have hLpos : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hk1 : ((M : ℝ) + 1) ≤ |((k i).valMinAbs : ℝ)| := by
    have : (M : ℤ) + 1 ≤ |(k i).valMinAbs| := hi
    rw [← Int.cast_abs]; exact_mod_cast this
  have hLM' : (L : ℝ) < 8 * ((M : ℝ) + 1) := by exact_mod_cast hLM
  have hpi := Real.two_le_pi
  have hL4 : (L : ℝ) ≤ 4 * Real.pi * |((k i).valMinAbs : ℝ)| := by nlinarith
  rw [hqi, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ W), abs_div, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hLpos]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_assoc]
  have : 1 ≤ 2 * Real.pi * |((k i).valMinAbs : ℝ)| / L * 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hLpos]; linarith
  calc (W : ℝ) = W * 1 := (mul_one _).symm
    _ ≤ W * (2 * Real.pi * |((k i).valMinAbs : ℝ)| / L * 2) := by gcongr

/-- The pointwise error of the decomposition `Â^n = a^n + χ ĝ_n(W p) + E` on the torus:
`|E(k)| ≤ (n |C_{D′}| + n ‖ψ‖_{D′,0} 2^{D′}) W^{−D′}`. -/
private theorem torusError_le {d L : ℕ} [NeZero L] (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (c' : ℝ) (hψ : SymbolBound ψ c') (C : ℕ → ℝ) (W : ℕ) (hW : (0 : ℝ) < W)
    (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : IsSymKernel S) (hSC : SymbolClose ψ C W S)
    (m : ℂ) (hm : ‖m‖ ≤ 1) (c : ℝ) (hc : 0 < c) (n D' M : ℕ) (hM : 1 ≤ M)
    (hLM : L < 8 * (M + 1)) (k : Zd d L) :
    ‖((m ^ 2 * symbol (cmat S) k + c) / (1 + c)) ^ n - ((c : ℂ) / (1 + c)) ^ n -
        (vpWeightD M k : ℂ) * contSymbolPow m c ψ n ((W : ℝ) • zfreq k)‖ ≤
      (n * |C D'| + n * (SchwartzMap.seminorm ℝ D' 0 ψ * 2 ^ D')) / (W : ℝ) ^ D' := by
  have h1c : 0 < 1 + c := by linarith
  have h1cC : ((1 : ℂ) + c) = ((1 + c : ℝ) : ℂ) := by push_cast; ring
  set Sψ := SchwartzMap.seminorm ℝ D' 0 ψ with hSψ
  set q : EuclideanSpace ℝ (Fin d) := (W : ℝ) • zfreq k with hq
  set a : ℂ := (c : ℂ) / (1 + c) with ha
  set Ah : ℂ := (m ^ 2 * symbol (cmat S) k + c) / (1 + c) with hAh
  set Aψ : ℂ := (m ^ 2 * (ψ q : ℂ) + c) / (1 + c) with hAψ
  have hnormdiv : ∀ z : ℂ, ‖z / (1 + c)‖ = ‖z‖ / (1 + c) := fun z => by
    rw [norm_div, h1cC, Complex.norm_real, Real.norm_of_nonneg h1c.le]
  have hm2 : ‖m ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm
  have hAh1 : ‖Ah‖ ≤ 1 := by
    rw [hAh, hnormdiv, div_le_one h1c]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    have := mul_le_mul hm2 (hS.norm_symbol_le k) (norm_nonneg _) zero_le_one
    linarith
  have hψq : |ψ q| ≤ 1 := abs_le.mpr ⟨by linarith [(hψ.range q).1, hψ.pos], (hψ.range q).2⟩
  have hAψ1 : ‖Aψ‖ ≤ 1 := by
    rw [hAψ, hnormdiv, div_le_one h1c]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc.le,
      Real.norm_eq_abs]
    have := mul_le_mul hm2 hψq (abs_nonneg _) zero_le_one
    linarith
  have ha1' : ‖a‖ ≤ 1 := by
    rw [ha, h1cC, ← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_le_one h1c]
    linarith
  have hEeq : Ah ^ n - a ^ n - (vpWeightD M k : ℂ) * contSymbolPow m c ψ n q =
      (Ah ^ n - Aψ ^ n) + (1 - (vpWeightD M k : ℂ)) * (Aψ ^ n - a ^ n) := by
    simp only [contSymbolPow, hAψ, ha]
    ring
  rw [hEeq]
  -- `|Â^n − Â_ψ^n| ≤ n |C_{D′}| W^{−D′}`
  have h1 : ‖Ah ^ n - Aψ ^ n‖ ≤ n * |C D'| / (W : ℝ) ^ D' := by
    refine (norm_pow_sub_pow_le hAh1 hAψ1 n).trans ?_
    have hd : ‖Ah - Aψ‖ ≤ |C D'| / (W : ℝ) ^ D' := by
      have : Ah - Aψ = m ^ 2 * (symbol (cmat S) k - (ψ q : ℂ)) / (1 + c) := by
        rw [hAh, hAψ]; ring
      rw [this, hnormdiv, norm_mul]
      calc ‖m ^ 2‖ * ‖symbol (cmat S) k - (ψ q : ℂ)‖ / (1 + c)
          ≤ 1 * ‖symbol (cmat S) k - (ψ q : ℂ)‖ / 1 := by
            gcongr
            linarith
        _ = ‖symbol (cmat S) k - (ψ q : ℂ)‖ := by ring
        _ ≤ C D' / (W : ℝ) ^ D' := hSC D' k
        _ ≤ |C D'| / (W : ℝ) ^ D' := by gcongr; exact le_abs_self _
    calc (n : ℝ) * ‖Ah - Aψ‖ ≤ n * (|C D'| / (W : ℝ) ^ D') := by gcongr
      _ = n * |C D'| / (W : ℝ) ^ D' := by ring
  -- the cut-off tail, where `|W p_k| ≥ W/2`
  have h2 : ‖(1 - (vpWeightD M k : ℂ)) * (Aψ ^ n - a ^ n)‖ ≤
      n * (Sψ * 2 ^ D') / (W : ℝ) ^ D' := by
    have hχ0 : 0 ≤ vpWeightD M k := Finset.prod_nonneg fun i _ => vpWeight_nonneg _ _
    have hχ1 : vpWeightD M k ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => vpWeight_nonneg _ _) fun i _ => vpWeight_le_one M _
    have hSψ0 : 0 ≤ Sψ := apply_nonneg _ _
    by_cases hall : ∀ i, |(k i).valMinAbs| ≤ (M : ℤ)
    · have : vpWeightD M k = 1 :=
        Finset.prod_eq_one fun i _ => vpWeight_eq_one hM (hall i)
      rw [this]
      simp only [Complex.ofReal_one, sub_self, zero_mul, norm_zero]
      positivity
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hqi : (W : ℝ) / 2 ≤ ‖q‖ := half_le_norm_smul_zfreq hLM W k i hi
    have hψdecay : |ψ q| ≤ Sψ * 2 ^ D' / (W : ℝ) ^ D' := by
      have hdec := SchwartzMap.norm_pow_mul_le_seminorm ℝ ψ D' q
      rw [Real.norm_eq_abs] at hdec
      have hqD : ((W : ℝ) / 2) ^ D' ≤ ‖q‖ ^ D' := pow_le_pow_left₀ (by positivity) hqi D'
      rw [le_div_iff₀ (by positivity)]
      have e : (W : ℝ) ^ D' = ((W : ℝ) / 2) ^ D' * 2 ^ D' := by
        rw [div_pow, div_mul_cancel₀ _ (by positivity)]
      calc |ψ q| * (W : ℝ) ^ D' = |ψ q| * ((W : ℝ) / 2) ^ D' * 2 ^ D' := by rw [e]; ring
        _ ≤ |ψ q| * ‖q‖ ^ D' * 2 ^ D' := by gcongr
        _ = ‖q‖ ^ D' * |ψ q| * 2 ^ D' := by ring
        _ ≤ Sψ * 2 ^ D' := by gcongr
    have hdiff : ‖Aψ ^ n - a ^ n‖ ≤ n * |ψ q| := by
      refine (norm_pow_sub_pow_le hAψ1 ha1' n).trans ?_
      gcongr
      have : Aψ - a = m ^ 2 * (ψ q : ℂ) / (1 + c) := by rw [hAψ, ha]; ring
      rw [this, hnormdiv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖m ^ 2‖ * |ψ q| / (1 + c) ≤ 1 * |ψ q| / 1 := by
            gcongr
            linarith
        _ = |ψ q| := by ring
    have h1χ : ‖(1 : ℂ) - (vpWeightD M k : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_le]
      constructor <;> linarith
    calc ‖(1 - (vpWeightD M k : ℂ)) * (Aψ ^ n - a ^ n)‖
        ≤ 1 * (n * |ψ q|) := by rw [norm_mul]; gcongr
      _ ≤ n * (Sψ * 2 ^ D' / (W : ℝ) ^ D') := by rw [one_mul]; gcongr
      _ = n * (Sψ * 2 ^ D') / (W : ℝ) ^ D' := by ring
  calc _ ≤ ‖Ah ^ n - Aψ ^ n‖ + ‖(1 - (vpWeightD M k : ℂ)) * (Aψ ^ n - a ^ n)‖ :=
        norm_add_le _ _
    _ ≤ n * |C D'| / (W : ℝ) ^ D' + n * (Sψ * 2 ^ D') / (W : ℝ) ^ D' := add_le_add h1 h2
    _ = _ := by ring

/-- The `ℓ¹` norm of the error kernel is at most `1/4` once `L^d ≤ W^{2D′−1}` and
`W ≥ 16 K² + 1`. -/
private theorem torusRowL1_error_le {d L : ℕ} [NeZero L] (E : Zd d L → ℂ) {W : ℕ} {Kc : ℝ}
    {D' : ℕ} (hD' : 1 ≤ D') (hEk : ∀ k, ‖E k‖ ≤ Kc / (W : ℝ) ^ D')
    (hLd : (L : ℝ) ^ d ≤ (W : ℝ) ^ (2 * D' - 1)) (hWK : 16 * Kc ^ 2 + 1 ≤ (W : ℝ)) :
    rowL1 E ≤ 1 / 4 := by
  have hWpos : (0 : ℝ) < W := by nlinarith [sq_nonneg Kc]
  have hsq := rowL1_sq_le E hEk
  have h0 : 0 ≤ rowL1 E := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hWD : (0 : ℝ) < (W : ℝ) ^ D' := by positivity
  have hpow : (W : ℝ) ^ (2 * D' - 1) * W = ((W : ℝ) ^ D') ^ 2 := by
    rw [← pow_succ, ← pow_mul]; congr 1; omega
  have : rowL1 E ^ 2 ≤ (1 / 4) ^ 2 := by
    refine hsq.trans ?_
    calc (L : ℝ) ^ d * (Kc / (W : ℝ) ^ D') ^ 2
        ≤ (W : ℝ) ^ (2 * D' - 1) * (Kc / (W : ℝ) ^ D') ^ 2 := by gcongr
      _ = Kc ^ 2 / W := by
          rw [div_pow, ← hpow]; field_simp
      _ ≤ (1 / 4) ^ 2 := by
          rw [div_le_iff₀ hWpos]; nlinarith
  exact (pow_le_pow_iff_left₀ h0 (by norm_num) two_ne_zero).mp this

/-- On `adm(c₀, c₁)` with `W ≥ 8`: `L ≥ 8` and `L^d ≤ W^{2D′−1}` when `d/c₁ ≤ 2D′ − 1`. -/
private theorem adm_bounds {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) {W L : ℕ} [NeZero L]
    (hadm : (W, L) ∈ adm c₀ c₁) (hW8 : (8 : ℝ) ≤ W) (d D' : ℕ)
    (hD'd : (d : ℝ) / c₁ ≤ ((2 * D' - 1 : ℕ) : ℝ)) :
    8 ≤ L ∧ (L : ℝ) ^ d ≤ (W : ℝ) ^ (2 * D' - 1) := by
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hWpos : (0 : ℝ) < W := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  have hWL : (W : ℝ) ≤ L := by
    refine hadm.2.trans ?_
    calc (L : ℝ) ^ (1 - c₀) ≤ (L : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L := Real.rpow_one _
  refine ⟨by exact_mod_cast hW8.trans hWL, ?_⟩
  have hLW : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁) := by
    have := Real.rpow_le_rpow (by positivity) hadm.1 (le_of_lt (one_div_pos.mpr hc₁))
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hc₁.ne', Real.rpow_one] at this
  calc (L : ℝ) ^ d ≤ ((W : ℝ) ^ (1 / c₁)) ^ d := pow_le_pow_left₀ (by positivity) hLW d
    _ = (W : ℝ) ^ ((d : ℝ) / c₁) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
        congr 1; ring
    _ ≤ (W : ℝ) ^ (((2 * D' - 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hW1 hD'd
    _ = (W : ℝ) ^ (2 * D' - 1) := Real.rpow_natCast _ _

/-- The continuum symbol `A_ψ^n − (c/(1+c))^n` as a Schwartz function, with the bound
`‖𝓕⁻(A_ψ^n − (c/(1+c))^n)‖_{L¹} ≤ K₀ Q n^{N+1} ρ^{n−1−N}`. -/
private theorem torusSymbol_schwartz {d : ℕ} (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (m : ℂ)
    (c : ℝ) (n : ℕ) {ρ : ℝ} (hac : ‖(c : ℂ) / (1 + c)‖ ≤ ρ) (hb : ‖m ^ 2 / (1 + c)‖ ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hψρ : ∀ x, ‖(c : ℂ) / (1 + c) + m ^ 2 / (1 + c) * (ψ x : ℂ)‖ ≤ ρ)
    (s : Finset (ℕ × ℕ)) (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
    (hK : ∀ F : 𝓢(EuclideanSpace ℝ (Fin d), ℂ),
      ∫ y, ‖(𝓕⁻ F) y‖ ≤ K₀ * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin d)) ℂ)) F)
    (hnN : s.sup Prod.snd + 1 ≤ n) :
    ∃ F : 𝓢(EuclideanSpace ℝ (Fin d), ℂ), (∀ q, F q = contSymbolPow m c ψ n q) ∧
      ∫ y, ‖(𝓕⁻ F) y‖ ≤ K₀ * (∑ x ∈ s, torusContQ ψ x.1 x.2) *
        ((n : ℝ) ^ (s.sup Prod.snd + 1) * ρ ^ (n - 1 - s.sup Prod.snd)) := by
  set N := s.sup Prod.snd with hN
  set Q := ∑ x ∈ s, torusContQ ψ x.1 x.2 with hQ
  have hn : 1 ≤ n := by omega
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun x _ => torusContQ_nonneg ψ x.1 x.2
  have hbd := torusSymbolPow_bound ψ m c n hac hb hρ1.le hn hψρ
  let F : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    ⟨contSymbolPow m c ψ n, torusSymbolPow_contDiff m c ψ n, fun k i => ⟨_, hbd k i⟩⟩
  refine ⟨F, fun q => rfl, ?_⟩
  have hβ0 : 0 ≤ (n : ℝ) ^ (N + 1) * ρ ^ (n - 1 - N) := by positivity
  have hsup : (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin d)) ℂ)) F ≤
      Q * ((n : ℝ) ^ (N + 1) * ρ ^ (n - 1 - N)) := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hQ0 hβ0) fun x hx => ?_
    obtain ⟨k, i⟩ := x
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    refine SchwartzMap.seminorm_le_bound ℂ k i F (mul_nonneg hQ0 hβ0) fun y => ?_
    refine (hbd k i y).trans ?_
    refine mul_le_mul ?_ (torusCont_beta_mono hn hρ0.le hρ1.le ?_) (by positivity) hQ0
    · exact Finset.single_le_sum (f := fun x : ℕ × ℕ => torusContQ ψ x.1 x.2)
        (fun x _ => torusContQ_nonneg ψ x.1 x.2) hx
    · exact Finset.le_sup (f := Prod.snd) hx
  calc ∫ y, ‖(𝓕⁻ F) y‖
      ≤ K₀ * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin d)) ℂ)) F := hK F
    _ ≤ K₀ * (Q * ((n : ℝ) ^ (N + 1) * ρ ^ (n - 1 - N))) :=
        mul_le_mul_of_nonneg_left hsup hK₀
    _ = _ := by ring

/-- [I, (B.19)] on the torus in `n`-th power form: for `ψ` with (H1)–(H2), `δ > 0` and `c > 0`
there are `n ≥ 1`, `c₁′ > 0` and `W₀` such that `‖A_c^n‖_{∞→∞} ≤ 1 − c₁′` for every
`(W, L) ∈ adm(c₀, c₁)` with `W ≥ W₀`, every symmetric translation-invariant kernel `S` with
`|Ŝ| ≤ 1` satisfying (H3) with the constants `C`, and every `m` with `|m| ≤ 1`, `|1 − m²| ≥ δ`. -/
theorem contraction_torus :
  ∀ (d : ℕ) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (c' : ℝ) (hψ : SymbolBound ψ c') (C : ℕ → ℝ) (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c),
    ∃ n : ℕ, 1 ≤ n ∧ ∃ c₁' : ℝ, 0 < c₁' ∧ ∃ W₀ : ℝ,
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsSymKernel S → SymbolClose ψ C W S →
      ∀ m : ℂ, ‖m‖ ≤ 1 → δ ≤ ‖1 - m ^ 2‖ → opNormInf (Ashift m c S ^ n) ≤ 1 - c₁' := by
  intro d c₀ c₁ hc₀ hc₁ ψ c' hψ C δ c hδ hc
  obtain ⟨ρ, hρ1, haρ, hspec⟩ := torusCont_spectral hc hψ.pos hδ
  have h1c : 0 < 1 + c := by linarith
  have ha0 : 0 < c / (1 + c) := by positivity
  have ha1 : c / (1 + c) < 1 := (div_lt_one h1c).mpr (by linarith)
  have hρ0 : 0 < ρ := ha0.trans_le haρ
  obtain ⟨s, K₀, hK₀, hK⟩ := torusCont_L1 d
  set N := s.sup Prod.snd with hN
  set Q := ∑ x ∈ s, torusContQ ψ x.1 x.2 with hQ
  obtain ⟨n, hnN, hnb⟩ := torusCont_exists_n (K := 3 ^ d * K₀ * Q) N ha0.le ha1 hρ0 hρ1
  have hn : 1 ≤ n := by omega
  -- the decay exponent `D′` with `d/c₁ ≤ 2D′ − 1`
  set D' : ℕ := ⌈(d : ℝ) / c₁⌉₊ + 1 with hD'
  have hD'd : (d : ℝ) / c₁ ≤ ((2 * D' - 1 : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil ((d : ℝ) / c₁)
    have : 2 * D' - 1 = 2 * ⌈(d : ℝ) / c₁⌉₊ + 1 := by omega
    rw [this]; push_cast
    have : (0 : ℝ) ≤ ⌈(d : ℝ) / c₁⌉₊ := Nat.cast_nonneg _
    linarith
  set Kc : ℝ := n * |C D'| + n * (SchwartzMap.seminorm ℝ D' 0 ψ * 2 ^ D') with hKc
  refine ⟨n, hn, 1 / 4, by norm_num, max 8 (16 * Kc ^ 2 + 1), ?_⟩
  intro W L _ hadm hW S hS hSC m hm hδm
  have hW8 : (8 : ℝ) ≤ W := (le_max_left _ _).trans hW
  have hWK : 16 * Kc ^ 2 + 1 ≤ (W : ℝ) := (le_max_right _ _).trans hW
  obtain ⟨hL8, hLd⟩ := adm_bounds hc₀ hc₁ hadm hW8 d D' hD'd
  set M := L / 8 with hMdef
  have hM : 1 ≤ M := by omega
  have hML : 8 * M ≤ L := by omega
  have hLM : L < 8 * (M + 1) := by omega
  -- the continuum symbol as a Schwartz function
  have h1cC : ((1 : ℂ) + c) = ((1 + c : ℝ) : ℂ) := by push_cast; ring
  have hac : ‖(c : ℂ) / (1 + c)‖ ≤ ρ := by
    rw [h1cC, ← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg ha0.le]
    exact haρ
  have hb : ‖m ^ 2 / (1 + c)‖ ≤ 1 := by
    rw [h1cC, norm_div, Complex.norm_real, Real.norm_of_nonneg h1c.le, norm_pow,
      div_le_one h1c]
    have : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm
    linarith
  have hψρ : ∀ x, ‖(c : ℂ) / (1 + c) + m ^ 2 / (1 + c) * (ψ x : ℂ)‖ ≤ ρ := fun x => by
    have := hspec m hm hδm (ψ x) (hψ.range x).1 (hψ.range x).2
    rwa [show (m ^ 2 * (ψ x : ℂ) + c) / (1 + c) = (c : ℂ) / (1 + c) + m ^ 2 / (1 + c) * ψ x by
      ring] at this
  obtain ⟨F, hFapp, hL1F⟩ :=
    torusSymbol_schwartz ψ m c n hac hb hρ0 hρ1 hψρ s K₀ hK₀ hK hnN
  -- the symbol of `A_c^n` and its decomposition
  set A := Ashift m c S with hAdef
  obtain ⟨hTAn, hsymn⟩ := transInv_pow_symbol A (transInv_Ashift S hS.transInv m c) n
  set a : ℂ := (c : ℂ) / (1 + c) with ha
  set Gm : Zd d L → ℂ := fun k => (vpWeightD M k : ℂ) * F ((W : ℝ) • zfreq k) with hGm
  set E : Zd d L → ℂ := fun k => symbol (A ^ n) k - a ^ n - Gm k with hE
  have hsplit : symbol (A ^ n) = (fun _ => a ^ n) + Gm + E := by
    funext k; simp only [Pi.add_apply, hE]; ring
  have hnorm_a : ‖a ^ n‖ = (c / (1 + c)) ^ n := by
    rw [norm_pow, ha, h1cC, ← Complex.ofReal_div, Complex.norm_real,
      Real.norm_of_nonneg ha0.le]
  have hEk : ∀ k, ‖E k‖ ≤ Kc / (W : ℝ) ^ D' := by
    intro k
    have := torusError_le ψ c' hψ C W (by linarith) S hS hSC m hm c hc n D' M hM hLM k
    calc ‖E k‖ = ‖((m ^ 2 * symbol (cmat S) k + c) / (1 + c)) ^ n - ((c : ℂ) / (1 + c)) ^ n -
          (vpWeightD M k : ℂ) * contSymbolPow m c ψ n ((W : ℝ) • zfreq k)‖ := by
          rw [hE]; dsimp only; rw [hsymn k, hAdef, symbol_Ashift, hGm]; dsimp only; rw [hFapp]
      _ ≤ _ := this
  have hEl1 : rowL1 E ≤ 1 / 4 := torusRowL1_error_le E (by omega) hEk hLd hWK
  have hGl1 : rowL1 Gm ≤ 3 ^ d * (K₀ * Q * ((n : ℝ) ^ (N + 1) * ρ ^ (n - 1 - N))) :=
    (rowL1_main_le hM hML W F).trans (by gcongr)
  calc opNormInf (A ^ n) ≤ rowL1 (symbol (A ^ n)) := opNormInf_le_rowL1 _ hTAn
    _ = rowL1 ((fun _ => a ^ n) + Gm + E) := by rw [hsplit]
    _ ≤ rowL1 (fun _ => a ^ n) + rowL1 Gm + rowL1 E := by
        refine (rowL1_add_le _ _).trans ?_
        gcongr
        exact rowL1_add_le _ _
    _ ≤ (c / (1 + c)) ^ n + 3 ^ d * (K₀ * Q * ((n : ℝ) ^ (N + 1) * ρ ^ (n - 1 - N))) + 1 / 4 := by
        rw [rowL1_const, hnorm_a]
        gcongr
    _ = (c / (1 + c)) ^ n + 3 ^ d * K₀ * Q * ((n : ℝ) ^ (N + 1) * ρ ^ (n - 1 - N)) + 1 / 4 := by
        ring
    _ ≤ 1 / 2 + 1 / 4 := by gcongr
    _ = 1 - 1 / 4 := by norm_num

/-- The geometric decay used in [I, (B.20)]: under the hypotheses of `contraction_torus` with a
variance kernel `S`, `‖A_c^k‖_{∞→∞} ≤ (1 − c₁′)^{⌊k/n⌋}` for every `k`. -/
theorem contraction_torus_pow :
  ∀ (d : ℕ) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (c' : ℝ) (hψ : SymbolBound ψ c') (C : ℕ → ℝ) (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c),
    ∃ n : ℕ, 1 ≤ n ∧ ∃ c₁' : ℝ, 0 < c₁' ∧ ∃ W₀ : ℝ,
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsVarKernel S → SymbolClose ψ C W S →
      ∀ m : ℂ, ‖m‖ ≤ 1 → δ ≤ ‖1 - m ^ 2‖ →
      ∀ k : ℕ, opNormInf (Ashift m c S ^ k) ≤ (1 - c₁') ^ (k / n) := by
  intro d c₀ c₁ hc₀ hc₁ ψ c' hψ C δ c hδ hc
  obtain ⟨n, hn, c₁', hc₁', W₀, h⟩ := contraction_torus d c₀ c₁ hc₀ hc₁ ψ c' hψ C δ c hδ hc
  refine ⟨n, hn, c₁', hc₁', W₀, fun W L _ hadm hW S hS hSC m hm hδm k => ?_⟩
  exact opNormInf_pow_le _ n _ (opNormInf_Ashift_le S hS.nonneg hS.rowSum m hm c hc.le)
    (h W L hadm hW S (IsVarKernel_isSymKernel S hS) hSC m hm hδm) k

section Witness

end Witness

end RBM8D
