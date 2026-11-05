import RBM8D.Profile.Norm
import RBM8D.Kernel.Profile

/-!
# The density `φ` and the symbol bounds

`f_{W,L} ≥ 0` for all `W, L` iff `φ ≥ 0`; `φ` is a probability density; `ψ > −1`; (H1)–(H2) and the shape conditions from the profile.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

namespace RBM8D

section Aux

variable {d : ℕ}

/-- `f_{W,L}` before normalisation is `W^{−d} φ([x]_L / W)` ([I, (1.6)]). -/
private theorem fRaw_eq (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) (hW : 1 ≤ W)
    (x : Zd d L) :
    fRaw ψ W L x = ((W : ℝ) ^ d)⁻¹ * profPhi ψ ((W : ℝ)⁻¹ • zrep x) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [fRaw, profInt_scale d ψ (W : ℝ) hW' (zrep x), profPhi]
  have h : (((W : ℝ) : ℂ) ^ d)⁻¹ = ((((W : ℝ) ^ d)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.re_ofReal_mul]

/-- The density `φ` is continuous. -/
private theorem continuous_profPhi (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    Continuous (profPhi ψ) := by
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin d)) (2 * Real.pi)
      h2pi).toContinuousLinearEquiv
  let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
      (SchwartzMap.postcompCLM (Complex.ofRealCLM) ψ)
  have hprof : profInt ψ 1 = 𝓕⁻ (G : EuclideanSpace ℝ (Fin d) → ℂ) := by
    funext y
    rw [profInt_eq_fourierInv d ψ 1 y]
    simp only [mul_one]
    congr 1
  have hc : Continuous (profInt ψ 1) := by
    rw [hprof, ← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ G).continuous
  exact Complex.continuous_re.comp hc

end Aux

/-- [I, Assumption 1.2]: for a real Schwartz `ψ` with `ψ(0) = 1`, the function `f_{W,L}` of
[I, (1.6)] is nonnegative for every `W ≥ 1` and `L ≥ 1` if and only if the density
`φ(y) = (2π)^{−d} ∫ ψ(q) e^{i q·y} dq` is nonnegative. The forward direction uses
`Z_{W,L} → 1` ([I, (1.10)]) along `W → ∞`, `L ≥ W²`. -/
theorem fWL_nonneg_iff :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (h0 : ψ 0 = 1),
    (∀ (W L : ℕ) [NeZero L], 1 ≤ W → ∀ x : Zd d L, 0 ≤ fWL ψ W L x) ↔ ∀ y, 0 ≤ profPhi ψ y := by
  intro d ψ h0
  constructor
  · intro hf y
    by_contra hneg'
    have hneg := not_le.mp hneg'
    -- a ball around `y` on which `φ < 0`
    have hev : ∀ᶠ z in nhds y, profPhi ψ z < 0 :=
      (continuous_profPhi ψ).continuousAt.eventually_lt continuousAt_const hneg
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨C, hC⟩ := ZWL_close d ψ h0 1 one_pos 1
    -- the scale `W = n`
    set n : ℕ := ⌈max C ((d : ℝ) / δ ^ 2)⌉₊ + 1 with hn
    have hn1 : 1 ≤ n := by omega
    have hnR : max C ((d : ℝ) / δ ^ 2) < n := by
      rw [hn]; push_cast; linarith [Nat.le_ceil (max C ((d : ℝ) / δ ^ 2))]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnC : C < n := lt_of_le_of_lt (le_max_left _ _) hnR
    have hnd : (d : ℝ) / δ ^ 2 < n := lt_of_le_of_lt (le_max_right _ _) hnR
    -- the lattice point `x̃_i = round(n y_i)` and the side `L = n² + 2M + 1`
    set k : Fin d → ℤ := fun i => round ((n : ℝ) * y i) with hk
    set M : ℕ := ∑ i, (k i).natAbs with hM
    set L : ℕ := n ^ 2 + 2 * M + 1 with hL
    have : NeZero L := ⟨by omega⟩
    let x : Zd d L := fun i => ((k i : ℤ) : ZMod L)
    have hkM : ∀ i, (k i).natAbs ≤ M := fun i =>
      Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have hx : ∀ i, (x i).valMinAbs = k i := by
      intro i
      rw [ZMod.valMinAbs_spec]
      refine ⟨rfl, ?_, ?_⟩
      · have h1 := hkM i
        have h2 : -((k i).natAbs : ℤ) ≤ k i := by omega
        have h3 : (0 : ℤ) ≤ (n : ℤ) ^ 2 := by positivity
        push_cast [hL]
        omega
      · have h1 := hkM i
        have h2 : k i ≤ ((k i).natAbs : ℤ) := Int.le_natAbs
        have h3 : (0 : ℤ) ≤ (n : ℤ) ^ 2 := by positivity
        push_cast [hL]
        omega
    have hzrep : ∀ i, zrep x i = (k i : ℝ) := by
      intro i
      simp [zrep, hx i]
    -- `L ≥ n^{1+1}`
    have hWL : (n : ℝ) ^ (1 + (1 : ℝ)) ≤ (L : ℝ) := by
      rw [show (1 + (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hL]; push_cast
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg _
      linarith
    -- `Z_{n,L} > 0`
    have hZ : 0 < ZWL ψ n L := by
      have h1 := hC n L hn1 hWL
      rw [pow_one] at h1
      have h2 : C / n < 1 := (div_lt_one hn0).mpr hnC
      have h3 := (abs_le.mp h1).1
      linarith
    -- `φ(x̃/n) ≥ 0`
    have hfx := hf n L hn1 x
    rw [fWL, fRaw_eq ψ n L hn1 x] at hfx
    have hphi : 0 ≤ profPhi ψ ((n : ℝ)⁻¹ • zrep x) := by
      have h1 : 0 < (ZWL ψ n L)⁻¹ * ((n : ℝ) ^ d)⁻¹ := by positivity
      have h2 : 0 ≤ ((ZWL ψ n L)⁻¹ * ((n : ℝ) ^ d)⁻¹) * profPhi ψ ((n : ℝ)⁻¹ • zrep x) := by
        rw [mul_assoc]; exact hfx
      exact (mul_nonneg_iff_of_pos_left h1).mp h2
    -- `x̃/n` is within `δ` of `y`
    have hdist : dist ((n : ℝ)⁻¹ • zrep x) y < δ := by
      rw [dist_eq_norm]
      have hco : ∀ i, ‖((n : ℝ)⁻¹ • zrep x - y) i‖ ^ 2 ≤ ((n : ℝ)⁻¹) ^ 2 := by
        intro i
        have h1 : ((n : ℝ)⁻¹ • zrep x - y) i = (n : ℝ)⁻¹ * ((k i : ℝ) - n * y i) := by
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hzrep i]
          field_simp
        rw [h1, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hn0), mul_pow]
        have h2 : |(k i : ℝ) - n * y i| ≤ 1 / 2 := by
          rw [abs_sub_comm]; exact abs_sub_round _
        have h3 : |(k i : ℝ) - n * y i| ^ 2 ≤ 1 := by
          have := abs_nonneg ((k i : ℝ) - n * y i)
          nlinarith
        have h4 : (0 : ℝ) ≤ ((n : ℝ)⁻¹) ^ 2 := by positivity
        nlinarith
      have hsq : ‖(n : ℝ)⁻¹ • zrep x - y‖ ^ 2 < δ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        calc ∑ i, ‖((n : ℝ)⁻¹ • zrep x - y) i‖ ^ 2 ≤ ∑ _i : Fin d, ((n : ℝ)⁻¹) ^ 2 :=
              Finset.sum_le_sum fun i _ => hco i
          _ = d * ((n : ℝ)⁻¹) ^ 2 := by simp
          _ ≤ d * (n : ℝ)⁻¹ := by
              have h1 : ((n : ℝ)⁻¹) ^ 2 ≤ (n : ℝ)⁻¹ := by
                have : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn1)
                have : 0 ≤ (n : ℝ)⁻¹ := by positivity
                nlinarith
              exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
          _ < δ ^ 2 := by
              rw [← div_eq_mul_inv, div_lt_iff₀ hn0]
              rw [div_lt_iff₀ (by positivity)] at hnd
              linarith
      exact lt_of_pow_lt_pow_left₀ 2 hδ.le hsq
    exact absurd (hball hdist) (not_lt.mpr hphi)
  · intro hφ W L _ hW x
    have hraw : ∀ z : Zd d L, 0 ≤ fRaw ψ W L z := by
      intro z
      rw [fRaw_eq ψ W L hW z]
      exact mul_nonneg (by positivity) (hφ _)
    exact mul_nonneg (inv_nonneg.mpr (Finset.sum_nonneg fun z _ => hraw z)) (hraw x)

/-- Under [I, Assumption 1.2], `φ(y) = (2π)^{−d} ∫ ψ(q) e^{i q·y} dq` is a probability density:
`φ ≥ 0` and `∫ φ = ψ(0) = 1`. -/
theorem profPhi_prob :
  ∀ (d : ℕ) (P : Profile d), (∀ y, 0 ≤ profPhi P.ψ y) ∧ ∫ y, profPhi P.ψ y = 1 := by
  intro d P
  refine ⟨(fWL_nonneg_iff d P.ψ P.at_zero).mp fun W L _ => P.f_nonneg W L, ?_⟩
  obtain ⟨hint, hinv⟩ := fourier_profInt d P.ψ
  have h1 := hinv 0
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    mul_one] at h1
  have h2 := integral_re hint
  simp only [RCLike.re_to_complex] at h2
  simp only [profPhi]
  rw [h2, h1, P.at_zero, Complex.ofReal_one, Complex.one_re]

/-- Under [I, Assumption 1.2], `ψ(p) = ∫ φ(y) cos(p·y) dy > −1` for every `p`, since `φ` is a
continuous probability density. -/
theorem psi_gt_neg_one :
  ∀ (d : ℕ) (P : Profile d) (p : EuclideanSpace ℝ (Fin d)), -1 < P.ψ p := by
  intro d P p
  obtain ⟨hφ0, hφ1⟩ := profPhi_prob d P
  obtain ⟨hint, hinv⟩ := fourier_profInt d P.ψ
  set ph := profPhi P.ψ with hφdef
  have hφc : Continuous ph := continuous_profPhi P.ψ
  have hreal : ∀ y, profInt P.ψ 1 y = (ph y : ℂ) := by
    intro y
    apply Complex.ext
    · simp [hφdef, profPhi]
    · simp [profInt_im d P.ψ P.symm 1 y]
  have hφint : Integrable ph := hint.re
  -- `ψ(p) = ∫ φ(y) cos(p·y) dy`
  set c : EuclideanSpace ℝ (Fin d) → ℝ := fun y => Real.cos (inner ℝ p y) with hcdef
  have hcc : Continuous c := Real.continuous_cos.comp (continuous_const.inner continuous_id)
  have hcb : ∀ y, ‖c y‖ ≤ 1 := fun y => by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hφcint : Integrable (fun y => ph y * c y) :=
    hφint.mul_bdd hcc.aestronglyMeasurable (Filter.Eventually.of_forall hcb)
  have hF : Integrable (fun y => profInt P.ψ 1 y * cexp (-(I * (inner ℝ p y : ℝ)))) := by
    refine hint.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    rw [show -(I * ((inner ℝ p y : ℝ) : ℂ)) = (((-(inner ℝ p y)) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hψ : P.ψ p = ∫ y, ph y * c y := by
    have h1 := integral_re hF
    simp only [RCLike.re_to_complex] at h1
    rw [hinv p, Complex.ofReal_re] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hreal y, hcdef]
    rw [show -(I * ((inner ℝ p y : ℝ) : ℂ)) = (((-(inner ℝ p y)) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  -- `1 + ψ(p) = ∫ g` with `g = φ (1 + cos(p·y)) ≥ 0` continuous
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ph y * (1 + c y) with hgdef
  have hgint : Integrable g := by
    have : g = fun y => ph y + ph y * c y := by funext y; simp only [hgdef]; ring
    rw [this]; exact hφint.add hφcint
  have hg : 1 + P.ψ p = ∫ y, g y := by
    have : g = fun y => ph y + ph y * c y := by funext y; simp only [hgdef]; ring
    rw [this, integral_add hφint hφcint, hψ, ← hφ1]
  have hg0 : 0 ≤ g := fun y => mul_nonneg (hφ0 y) (by
    have := Real.neg_one_le_cos (inner ℝ p y); simp only [hcdef]; linarith)
  have hgc : Continuous g := hφc.mul (continuous_const.add hcc)
  -- a point where `g > 0`
  have hy₀ : ∃ y₀, 0 < ph y₀ := by
    by_contra h'
    have h : ∀ y, ph y ≤ 0 := fun y => not_lt.mp fun hy => h' ⟨y, hy⟩
    have : ph = 0 := funext fun y => le_antisymm (h y) (hφ0 y)
    rw [this] at hφ1
    simp at hφ1
  obtain ⟨y₀, hy₀⟩ := hy₀
  have hpt : ∃ y₁, 0 < g y₁ := by
    by_cases hc : c y₀ = -1
    · -- move along `p` to leave the zero set of `1 + cos`
      have hU : IsOpen {y | 0 < ph y} := isOpen_lt continuous_const hφc
      obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
      have hp : p ≠ 0 := by
        rintro rfl
        simp [hcdef] at hc
        norm_num at hc
      have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
      set s : ℝ := min (η * ‖p‖ / 2) (Real.pi / 2) with hs
      have hs0 : 0 < s := lt_min (by positivity) (by positivity)
      have hs1 : s ≤ Real.pi / 2 := min_le_right _ _
      set t : ℝ := s / ‖p‖ ^ 2 with ht
      refine ⟨y₀ + t • p, mul_pos (hball ?_) ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        have : s ≤ η * ‖p‖ / 2 := min_le_left _ _
        rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      · have hin : inner ℝ p (y₀ + t • p) = inner ℝ p y₀ + s := by
          rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ht,
            div_mul_cancel₀ _ (by positivity)]
        have hsin : Real.sin (inner ℝ p y₀) = 0 := by
          have := Real.sin_sq_add_cos_sq (inner ℝ p y₀)
          simp only [hcdef] at hc
          rw [hc] at this
          nlinarith
        have hcs : Real.cos s < 1 := by
          have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl hs1 hs0
          rwa [Real.cos_zero] at this
        simp only [hcdef, hin, Real.cos_add, hsin]
        simp only [hcdef] at hc
        rw [hc]
        linarith
    · refine ⟨y₀, mul_pos hy₀ ?_⟩
      have := Real.neg_one_le_cos (inner ℝ p y₀)
      have hne : c y₀ ≠ -1 := hc
      have : -1 < c y₀ := lt_of_le_of_ne this (Ne.symm hne)
      linarith
  obtain ⟨y₁, hy₁⟩ := hpt
  have hpos : 0 < ∫ y, g y := by
    rw [integral_pos_iff_support_of_nonneg hg0 hgint]
    exact hgc.isOpen_support.measure_pos volume ⟨y₁, hy₁.ne'⟩
  linarith

/-- (H1)–(H2): under [I, Assumption 1.2] there is `c′ > 0` with `−1 + c′ ≤ ψ ≤ 1`. The constant
is `c′ = min(1/2, 1 + min_{|p| ≤ R} ψ)`, where `|ψ| ≤ 1/2` outside the ball of radius `R`. -/
theorem symbolBound_of_profile :
  ∀ (d : ℕ) (P : Profile d), ∃ c' : ℝ, SymbolBound P.ψ c' := by
  intro d P
  set C₁ := SchwartzMap.seminorm ℝ 1 0 P.ψ with hC₁
  have hC₁0 : 0 ≤ C₁ := apply_nonneg _ _
  set R : ℝ := 2 * C₁ + 1 with hR
  have hfar : ∀ p, R ≤ ‖p‖ → -(1 / 2) ≤ P.ψ p := by
    intro p hp
    have h1 := SchwartzMap.norm_pow_mul_le_seminorm ℝ P.ψ 1 p
    rw [pow_one, Real.norm_eq_abs] at h1
    have hp0 : 0 < ‖p‖ := by linarith
    have h2 : |P.ψ p| ≤ 1 / 2 := by
      by_contra h'
      have h := not_le.mp h'
      have : ‖p‖ * (1 / 2) < ‖p‖ * |P.ψ p| := mul_lt_mul_of_pos_left h hp0
      nlinarith
    exact (abs_le.mp h2).1
  obtain ⟨p₀, -, hp₀⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self (by positivity)⟩ P.ψ.continuous.continuousOn
  have hm := psi_gt_neg_one d P p₀
  refine ⟨min (1 / 2) (1 + P.ψ p₀), ⟨lt_min (by norm_num) (by linarith), fun p => ⟨?_, ?_⟩⟩⟩
  · rcases le_total ‖p‖ R with h | h
    · have : P.ψ p₀ ≤ P.ψ p := hp₀ (by rw [Metric.mem_closedBall, dist_zero_right]; exact h)
      have := min_le_right (1 / 2 : ℝ) (1 + P.ψ p₀)
      linarith
    · have := hfar p h
      have := min_le_left (1 / 2 : ℝ) (1 + P.ψ p₀)
      linarith
  · exact (abs_le.mp (P.abs_le_one p)).2

/-- The shape conditions [I, Assumption 1.2 (i)–(ii)] and the symmetry of `ψ`, for the profile
`ψ` with its constant `c_ψ`. -/
theorem profileShape_of_profile :
  ∀ (d : ℕ) (P : Profile d), ProfileShape P.ψ P.cψ := by
  intro d P
  exact ⟨P.cψ_pos, P.at_zero, P.le_max, P.symm⟩

section Witness

end Witness

end RBM8D
