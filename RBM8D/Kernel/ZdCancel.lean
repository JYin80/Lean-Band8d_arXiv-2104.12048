module

public import RBM8D.Kernel.ShellKernel

@[expose] public section

/-!
# Cancellation on `ℤ^d`

[I, Lemma 7.3] and its `ℤ^d` form for every `a ∈ [0, 1]`, and the difference bound used for (Theta-wh).
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d : ℕ}

open scoped ContDiff

/-! ## Elementary facts -/

section Elementary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem sqNorm_nonneg' (p : Fin d → ℝ) : 0 ≤ sqNorm p :=
  Finset.sum_nonneg fun i _ => sq_nonneg (p i)

/-- The sup norm is at most the Euclidean norm: `‖p‖² ≤ |p|²`. -/
private theorem norm_sq_le_sqNorm (p : Fin d → ℝ) : ‖p‖ ^ 2 ≤ sqNorm p := by
  have h : ‖p‖ ≤ Real.sqrt (sqNorm p) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => p i ^ 2)
      (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))
  calc ‖p‖ ^ 2 ≤ Real.sqrt (sqNorm p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sqNorm p := Real.sq_sqrt (sqNorm_nonneg' p)

/-- A point with `W² |p|² ≤ 4` and `W ≥ 1` lies in the cube. -/
private theorem mem_cubePi_of_sqNorm_le {W : ℝ} (hW : 1 ≤ W) {p : Fin d → ℝ}
    (hp : W ^ 2 * sqNorm p ≤ 4) : p ∈ cubePi d := by
  intro i _
  have h1 : p i ^ 2 ≤ sqNorm p :=
    Finset.single_le_sum (f := fun i => p i ^ 2) (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  have hW2 : 1 ≤ W ^ 2 := one_le_pow₀ hW
  have h2 : sqNorm p ≤ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hW2 (sqNorm_nonneg' p)]
  have h3 : |p i| ≤ 2 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (p i ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  constructor <;> linarith [abs_le.1 h3]

/-- The iterated derivatives of a function vanishing near `x` vanish at `x`. -/
private theorem iteratedFDeriv_eq_zero_of_eventuallyEq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {x : E} (h : f =ᶠ[nhds x] 0) (n : ℕ) :
    iteratedFDeriv ℝ n f x = 0 := by
  have := (h.iteratedFDeriv ℝ n).eq_of_nhds
  rw [this]
  have : (0 : E → F) = fun _ => (0 : F) := rfl
  rw [this]
  cases n with
  | zero => ext; simp
  | succ n => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]; rfl

/-- Leibniz bound: if `‖D^i f‖ ≤ A L^i` and `‖D^i g‖ ≤ B L^i` at `x` for `i ≤ n`, then
`‖D^n (f g)(x)‖ ≤ 2^n A B L^n`. -/
private theorem norm_iteratedFDeriv_mul_le_of {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : E → A} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : E) (n : ℕ) {A B L : ℝ} (hL : 0 ≤ L)
    (hA : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ A * L ^ i)
    (hB : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ B * L ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2 ^ n * A * B * L ^ n := by
  refine (norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast le_top)).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
      ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ (n.choose i : ℝ) * (A * B * L ^ n) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := hA i hi'
    have h2 := hB (n - i) (Nat.sub_le n i)
    have h1' : 0 ≤ A * L ^ i := (norm_nonneg _).trans h1
    have hLn : L ^ i * L ^ (n - i) = L ^ n := by rw [← pow_add, Nat.add_sub_cancel' hi']
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
        ≤ (n.choose i : ℝ) * (A * L ^ i) * (B * L ^ (n - i)) := by
          gcongr
      _ = (n.choose i : ℝ) * (A * B * (L ^ i * L ^ (n - i))) := by ring
      _ = (n.choose i : ℝ) * (A * B * L ^ n) := by rw [hLn]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [this]; ring


/-- Derivatives of an affine image `c₀ + c₁ f`. -/
private theorem norm_iteratedFDeriv_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (c₀ c₁ : ℝ) {k : ℕ} (hk : k ≠ 0) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => c₀ + c₁ * f y) x‖ = |c₁| * ‖iteratedFDeriv ℝ k f x‖ := by
  have he : (fun y => c₀ + c₁ * f y) = (fun _ => c₀) + c₁ • f := by
    funext y; simp [smul_eq_mul]
  have h2 : ContDiffAt ℝ k (c₁ • f) x :=
    (show ContDiff ℝ ∞ (c₁ • f) from hf.const_smul c₁).contDiffAt.of_le
      (by exact_mod_cast le_top)
  rw [he, iteratedFDeriv_add_apply (f := fun _ => c₀) (g := c₁ • f) contDiffAt_const h2,
    iteratedFDeriv_const_of_ne hk, Pi.zero_apply, zero_add,
    iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
    Real.norm_eq_abs]


end Elementary

/-! ## The symbol of an `InfKernel` -/

section Symbol

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ} {W : ℕ} {s : (Fin d → ℤ) → ℝ}

private theorem InfKernel.summable_s (hs : InfKernel ψ C W s) : Summable s := by
  by_contra h
  have := hs.sum_one
  rw [tsum_eq_zero_of_not_summable h] at this
  exact zero_ne_one this

private theorem InfKernel.im_eq (hs : InfKernel ψ C W s) (p : Fin d → ℝ) :
    (zdSymbol s p).im = 0 :=
  zdSymbol_im s hs.symm hs.summable_s p

private theorem zexp_neg_left (p : Fin d → ℝ) (x : Fin d → ℤ) : zexp (-p) x = conj (zexp p x) := by
  unfold zexp
  rw [← Complex.exp_conj]
  congr 1
  simp [Finset.sum_neg_distrib]

private theorem InfKernel.zdSymbol_neg (hs : InfKernel ψ C W s) (p : Fin d → ℝ) :
    zdSymbol s (-p) = zdSymbol s p := by
  have h1 : zdSymbol s (-p) = conj (zdSymbol s p) := by
    unfold zdSymbol zdSeries
    rw [Complex.conj_tsum]
    refine tsum_congr fun x => ?_
    rw [map_mul, Complex.conj_ofReal, zexp_neg_left]
  rw [h1, Complex.conj_eq_iff_im.2 (hs.im_eq p)]

/-- The symbol is even, so its derivative vanishes at `0`. -/
private theorem InfKernel.fderiv_zero (hs : InfKernel ψ C W s)
    (hd : DifferentiableAt ℝ (zdSymbol s) 0) : fderiv ℝ (zdSymbol s) 0 = 0 := by
  set f := zdSymbol s with hf
  have h0 : HasFDerivAt f (fderiv ℝ f 0) (-(0 : Fin d → ℝ)) := by
    rw [neg_zero]; exact hd.hasFDerivAt
  have h1 : HasFDerivAt (fun p => f (-p))
      ((fderiv ℝ f 0).comp (-ContinuousLinearMap.id ℝ (Fin d → ℝ))) 0 :=
    h0.comp 0 (hasFDerivAt_id (0 : Fin d → ℝ)).neg
  have h2 : (fun p => f (-p)) = f := funext fun p => hs.zdSymbol_neg p
  rw [h2] at h1
  have h3 := h1.fderiv
  have h4 : (fderiv ℝ f 0).comp (-ContinuousLinearMap.id ℝ (Fin d → ℝ)) = -fderiv ℝ f 0 := by
    ext v; simp
  rw [h4] at h3
  ext v
  have hv := congrArg (fun T : (Fin d → ℝ) →L[ℝ] ℂ => T v) h3
  simp only [_root_.neg_apply] at hv
  simp only [_root_.zero_apply]
  linear_combination hv / 2

/-- Mean value bound for the derivative: `‖Df(p)‖ ≤ K ‖p‖` when `Df(0) = 0` and `‖D²f‖ ≤ K`. -/
private theorem norm_fderiv_le_of_zero {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (h0 : fderiv ℝ f 0 = 0) {K : ℝ} (h2 : ∀ q, ‖iteratedFDeriv ℝ 2 f q‖ ≤ K) (p : E) :
    ‖fderiv ℝ f p‖ ≤ K * ‖p‖ := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ f) (s := Set.univ)
    (x := 0) (y := p) (fun x _ => hd x) (fun q _ => by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact h2 q)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  rwa [h0, sub_zero, sub_zero] at this


end Symbol

/-! ## Cutoffs -/

section Cutoffs

/-- `W ‖p‖ < 2 / 2^j` when `W² |p|² < 4 / 4^j`. -/
private theorem norm_lt_of_sqNorm_lt {W : ℝ} (hW : 0 < W) (j : ℕ) {p : Fin d → ℝ}
    (hp : W ^ 2 * sqNorm p < 4 / 4 ^ j) : ‖p‖ < 2 / (2 ^ j * W) := by
  have h1 : (W * ‖p‖) ^ 2 < (2 / 2 ^ j) ^ 2 := by
    calc (W * ‖p‖) ^ 2 = W ^ 2 * ‖p‖ ^ 2 := by ring
      _ ≤ W ^ 2 * sqNorm p := mul_le_mul_of_nonneg_left (norm_sq_le_sqNorm p) (by positivity)
      _ < 4 / 4 ^ j := hp
      _ = (2 / 2 ^ j) ^ 2 := by
          rw [div_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have h2 : W * ‖p‖ < 2 / 2 ^ j :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
  rw [lt_div_iff₀ (by positivity)]
  calc ‖p‖ * (2 ^ j * W) = 2 ^ j * (W * ‖p‖) := by ring
    _ < 2 ^ j * (2 / 2 ^ j) := mul_lt_mul_of_pos_left h2 (by positivity)
    _ = 2 := by field_simp

private theorem contDiff_lowPass' : ContDiff ℝ ∞ lowPass :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const 3)

private theorem contDiff_sqNorm' : ContDiff ℝ ∞ (sqNorm : (Fin d → ℝ) → ℝ) :=
  ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ : Fin d => ℝ) i).pow 2

private theorem continuous_sqNorm' : Continuous (sqNorm : (Fin d → ℝ) → ℝ) :=
  contDiff_sqNorm'.continuous

private theorem contDiff_coreCut (W J : ℕ) : ContDiff ℝ ∞ (coreCut (d := d) W J) :=
  contDiff_lowPass'.comp (contDiff_const.mul contDiff_sqNorm')

private theorem contDiff_shellCut (W j : ℕ) : ContDiff ℝ ∞ (shellCut (d := d) W j) :=
  (contDiff_lowPass'.comp (contDiff_const.mul contDiff_sqNorm')).sub
    (contDiff_lowPass'.comp (contDiff_const.mul contDiff_sqNorm'))

private theorem contDiff_highCut (W : ℕ) : ContDiff ℝ ∞ (highCut (d := d) W) :=
  contDiff_const.sub (contDiff_lowPass'.comp (contDiff_const.mul contDiff_sqNorm'))

private theorem lowPass_eq_zero' {t : ℝ} (h : 4 ≤ t) : lowPass t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem lowPass_mem_Icc (t : ℝ) : 0 ≤ lowPass t ∧ lowPass t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The core at scale `J` vanishes where `W²|p|² > 4/4^J`. -/
private theorem coreCut_eq_zero {W J : ℕ} {p : Fin d → ℝ}
    (hp : 4 / 4 ^ J < (W : ℝ) ^ 2 * sqNorm p) : coreCut W J p = 0 := by
  unfold coreCut
  apply lowPass_eq_zero'
  rw [div_lt_iff₀ (by positivity)] at hp
  nlinarith

private theorem shellCut_eventually_zero {W j : ℕ} {p : Fin d → ℝ}
    (hp : ¬ (((4 : ℝ) ^ (j + 1))⁻¹ ≤ (W : ℝ) ^ 2 * sqNorm p ∧
      (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ j)) : shellCut (d := d) W j =ᶠ[nhds p] 0 := by
  have hcont : Continuous fun q : Fin d → ℝ => (W : ℝ) ^ 2 * sqNorm q :=
    continuous_const.mul continuous_sqNorm'
  have hopen : IsOpen {q : Fin d → ℝ | (W : ℝ) ^ 2 * sqNorm q < ((4 : ℝ) ^ (j + 1))⁻¹ ∨
      4 / 4 ^ j < (W : ℝ) ^ 2 * sqNorm q} :=
    (isOpen_lt hcont continuous_const).union (isOpen_lt continuous_const hcont)
  have hmem : p ∈ {q : Fin d → ℝ | (W : ℝ) ^ 2 * sqNorm q < ((4 : ℝ) ^ (j + 1))⁻¹ ∨
      4 / 4 ^ j < (W : ℝ) ^ 2 * sqNorm q} := by
    simp only [Set.mem_ofPred_eq]
    by_contra h
    push Not at h
    exact hp h
  filter_upwards [hopen.mem_nhds hmem] with q hq
  by_contra hne
  have := shellCut_support W j q hne
  rcases hq with hq | hq <;> linarith [this.1, this.2]

private theorem coreCut_eventually_zero {W J : ℕ} {p : Fin d → ℝ}
    (hp : ¬ (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ J) : coreCut (d := d) W J =ᶠ[nhds p] 0 := by
  have hcont : Continuous fun q : Fin d → ℝ => (W : ℝ) ^ 2 * sqNorm q :=
    continuous_const.mul continuous_sqNorm'
  push Not at hp
  filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hp] with q hq
  exact coreCut_eq_zero hq

/-- On `[-π, π]^d`, `1 - a Re ŝ ≥ min(c, 1) min(W²|p|², 1)` for `a ∈ [0, 1]`, from
`1 - Re ŝ ≥ c min(W²|p|², 1)`. -/
private theorem one_sub_mul_ge {c a σ X : ℝ} (hc : 0 < c) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hX : 0 ≤ X) (h : c * min X 1 ≤ 1 - σ) : min c 1 * min X 1 ≤ 1 - a * σ := by
  have hm1 : min X 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 ≤ min X 1 := le_min hX zero_le_one
  have hc1 : min c 1 ≤ c := min_le_left _ _
  have hc1' : min c 1 ≤ 1 := min_le_right _ _
  rcases le_or_gt σ 0 with hσ | hσ
  · have : a * σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 hσ
    nlinarith
  · have : a * σ ≤ σ := by nlinarith
    nlinarith

/-- The derivative of the symbol of an `InfKernel` at `p` is at most `K_2 W² ‖p‖`. -/
private theorem InfKernel.norm_fderiv_le {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ}
    {W : ℕ} {s : (Fin d → ℤ) → ℝ} (hs : InfKernel ψ C W s) (hcd : ContDiff ℝ ∞ (zdSymbol s))
    {K₂ : ℝ} (h2 : ∀ p, ‖iteratedFDeriv ℝ 2 (zdSymbol s) p‖ ≤ K₂ * (W : ℝ) ^ 2)
    (p : Fin d → ℝ) : ‖fderiv ℝ (zdSymbol s) p‖ ≤ K₂ * (W : ℝ) ^ 2 * ‖p‖ :=
  norm_fderiv_le_of_zero hcd (hs.fderiv_zero (hcd.differentiable (by simp) 0)) h2 p

/-- `1 - a σ ≥ (1 - a)/2` for `σ ≤ 1` and `0 ≤ a ≤ 1`. -/
private theorem one_sub_mul_ge_half {a σ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hσ : σ ≤ 1) :
    (1 - a) / 2 ≤ 1 - a * σ := by
  rcases le_or_gt (1 / 2) σ with h | h
  · nlinarith
  · rcases le_or_gt 0 σ with h' | h'
    · nlinarith
    · nlinarith


end Cutoffs

/-! ## Fourier coefficients on the cube -/

section Linear

private theorem measurableSet_cubePi' : MeasurableSet (cubePi d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

private theorem isCompact_cubePi'' : IsCompact (cubePi d) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem continuous_zexp' (y : Fin d → ℤ) : Continuous fun p : Fin d → ℝ => zexp p y := by
  unfold zexp; fun_prop

private theorem integrableOn_mul_zexp {F : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (x : Fin d → ℤ) : IntegrableOn (fun p => F p * zexp p (-x)) (cubePi d) :=
  hF.mul_continuousOn (continuous_zexp' _).continuousOn isCompact_cubePi''

private theorem latticeFourier_add {F G : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (hG : IntegrableOn G (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => F p + G p) x = latticeFourier F x + latticeFourier G x := by
  unfold latticeFourier
  rw [← mul_add, ← integral_add (integrableOn_mul_zexp hF x) (integrableOn_mul_zexp hG x)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only; ring

private theorem latticeFourier_sub {F G : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (hG : IntegrableOn G (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => F p - G p) x = latticeFourier F x - latticeFourier G x := by
  unfold latticeFourier
  rw [← mul_sub, ← integral_sub (integrableOn_mul_zexp hF x) (integrableOn_mul_zexp hG x)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only; ring

private theorem latticeFourier_const_mul (c : ℂ) (F : (Fin d → ℝ) → ℂ) (x : Fin d → ℤ) :
    latticeFourier (fun p => c * F p) x = c * latticeFourier F x := by
  unfold latticeFourier
  simp_rw [mul_assoc c]
  rw [integral_const_mul]; ring

private theorem latticeFourier_finset_sum {ι : Type*} (S : Finset ι)
    {F : ι → (Fin d → ℝ) → ℂ} (hF : ∀ n ∈ S, IntegrableOn (F n) (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => ∑ n ∈ S, F n p) x = ∑ n ∈ S, latticeFourier (F n) x := by
  unfold latticeFourier
  rw [← Finset.mul_sum, ← integral_finsetSum S fun n hn => integrableOn_mul_zexp (hF n hn) x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Finset.sum_mul]

private theorem latticeFourier_congr {F G : (Fin d → ℝ) → ℂ}
    (h : ∀ p ∈ cubePi d, F p = G p) (x : Fin d → ℤ) : latticeFourier F x = latticeFourier G x := by
  unfold latticeFourier
  congr 1
  exact setIntegral_congr_fun measurableSet_cubePi' fun p hp => by simp only [h p hp]

private theorem natAbs_le_zdInf' (x : Fin d → ℤ) (j : Fin d) :
    |((x j : ℤ) : ℝ)| ≤ (zdInf x : ℝ) := by
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ j)

private theorem ae_coord_ne_zero :
    ∀ᵐ p ∂(volume : Measure (Fin d → ℝ)), ∀ i, p i ≠ 0 := by
  rw [ae_iff]
  have : {p : Fin d → ℝ | ¬ ∀ i, p i ≠ 0} = ⋃ i, {p | p i = 0} := by
    ext p; simp
  rw [this, measure_iUnion_null_iff]
  intro i
  rw [volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i 0

private theorem norm_latticeFourier_le (F : (Fin d → ℝ) → ℂ) (x : Fin d → ℤ) :
    ‖latticeFourier F x‖ ≤ ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖F p‖ := by
  unfold latticeFourier
  rw [norm_mul]
  have hc : ‖((2 * Real.pi : ℂ) ^ d)⁻¹‖ = ((2 * Real.pi) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hc]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext p
  rw [norm_mul, norm_zexp, mul_one]

private theorem abs_cut_le_one {W j J : ℕ} (p : Fin d → ℝ) :
    |highCut W p| ≤ 1 ∧ |shellCut W j p| ≤ 1 ∧ |coreCut W J p| ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have := lowPass_mem_Icc ((W : ℝ) ^ 2 * sqNorm p)
    unfold highCut; rw [abs_le]; constructor <;> linarith
  · have h1 := lowPass_mem_Icc (4 ^ j * (W : ℝ) ^ 2 * sqNorm p)
    have h2 := lowPass_mem_Icc (4 ^ (j + 1) * (W : ℝ) ^ 2 * sqNorm p)
    unfold shellCut; rw [abs_le]; constructor <;> linarith
  · have := lowPass_mem_Icc (4 ^ J * (W : ℝ) ^ 2 * sqNorm p)
    unfold coreCut; rw [abs_le]; constructor <;> linarith

private theorem integrableOn_cut_mul {F : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    {χ : (Fin d → ℝ) → ℝ} (hχ : Continuous χ) (hb : ∀ p, |χ p| ≤ 1) :
    IntegrableOn (fun p => (χ p : ℂ) * F p) (cubePi d) := by
  refine Integrable.bdd_mul (c := 1) hF
    (Complex.continuous_ofReal.comp hχ).aestronglyMeasurable (Filter.Eventually.of_forall
      fun p => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact hb p

/-- The dyadic decomposition of a kernel: high part, shells `j < J`, core at scale `J`. -/
private theorem latticeFourier_decomp {F : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (W J : ℕ) (x : Fin d → ℤ) :
    latticeFourier F x = latticeFourier (fun p => (highCut W p : ℂ) * F p) x +
      ∑ j ∈ Finset.range J, latticeFourier (fun p => (shellCut W j p : ℂ) * F p) x +
      latticeFourier (fun p => (coreCut W J p : ℂ) * F p) x := by
  have hh := integrableOn_cut_mul hF (contDiff_highCut (d := d) W).continuous
    fun p => (abs_cut_le_one (W := W) (j := 0) (J := J) p).1
  have hs : ∀ j ∈ Finset.range J, IntegrableOn (fun p => (shellCut W j p : ℂ) * F p) (cubePi d) :=
    fun j _ => integrableOn_cut_mul hF (contDiff_shellCut (d := d) W j).continuous
      fun p => (abs_cut_le_one (W := W) (j := j) (J := J) p).2.1
  have hc := integrableOn_cut_mul hF (contDiff_coreCut (d := d) W J).continuous
    fun p => (abs_cut_le_one (W := W) (j := 0) (J := J) p).2.2
  have hsum : IntegrableOn (fun p => ∑ j ∈ Finset.range J, (shellCut W j p : ℂ) * F p)
      (cubePi d) := by
    exact integrable_finsetSum (Finset.range J) hs
  have hpt : ∀ p ∈ cubePi d, F p = ((highCut W p : ℂ) * F p +
      ∑ j ∈ Finset.range J, (shellCut W j p : ℂ) * F p) + (coreCut W J p : ℂ) * F p := by
    intro p _
    have h := shellCut_partition (d := d) W J p
    have hc' : ((highCut W p + ∑ j ∈ Finset.range J, shellCut W j p + coreCut W J p : ℝ) : ℂ) =
        1 := by
      rw [h]; simp
    push_cast at hc'
    rw [← Finset.sum_mul, ← add_mul, ← add_mul, hc', one_mul]
  rw [latticeFourier_congr hpt x,
    latticeFourier_add (F := fun p => (highCut W p : ℂ) * F p +
      ∑ j ∈ Finset.range J, (shellCut W j p : ℂ) * F p)
      (G := fun p => (coreCut W J p : ℂ) * F p) (hh.add hsum) hc,
    latticeFourier_add (F := fun p => (highCut W p : ℂ) * F p)
      (G := fun p => ∑ j ∈ Finset.range J, (shellCut W j p : ℂ) * F p) hh hsum,
    latticeFourier_finset_sum (F := fun j p => (shellCut W j p : ℂ) * F p) _ hs]

/-- Absorbing a weight: from `X (1 + u)^{M+e} ≤ B` and `w ≤ κ (1 + u)^M`,
`X w ≤ κ B (1 + u)^{-e}`. -/
private theorem absorb_weight {X u w B κ : ℝ} {M e : ℕ} (hX : 0 ≤ X) (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (h : X * (1 + u) ^ (M + e) ≤ B) (hw : w ≤ κ * (1 + u) ^ M) :
    X * w ≤ κ * B * ((1 + u) ^ e)⁻¹ := by
  have hpos : 0 < (1 + u) ^ e := pow_pos (by linarith) e
  calc X * w ≤ X * (κ * (1 + u) ^ M) := mul_le_mul_of_nonneg_left hw hX
    _ = κ * (X * (1 + u) ^ (M + e)) * ((1 + u) ^ e)⁻¹ := by
        rw [pow_add]; field_simp
    _ ≤ κ * B * ((1 + u) ^ e)⁻¹ := by gcongr

/-- The core at scale `J` tends to `0` pointwise away from `0`. -/
private theorem tendsto_coreCut {W : ℕ} (hW : 1 ≤ W) {p : Fin d → ℝ} (hp : p ≠ 0) :
    Filter.Tendsto (fun J => coreCut W J p) Filter.atTop (nhds 0) := by
  have hsq : 0 < sqNorm p := by
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra h; push Not at h; exact hp (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => p i ^ 2)
      (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hX : 0 < (W : ℝ) ^ 2 * sqNorm p := by positivity
  have hev : ∀ᶠ J in Filter.atTop, 4 / ((W : ℝ) ^ 2 * sqNorm p) ≤ (4 : ℝ) ^ J :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).eventually_ge_atTop _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with J hJ
  symm
  unfold coreCut
  apply lowPass_eq_zero'
  rw [div_le_iff₀ hX] at hJ
  linarith

/-- `(1 + |x| (1 - a)^{1/2}/W)^M ≤ 3^M (1 + |x|/(2^j W))^M` for `j ≤ shellCount a`, `a < 1`. -/
private theorem weight_le_shell {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {j : ℕ}
    (hj : j ≤ shellCount a) (X W : ℝ) (hX : 0 ≤ X) (hW : 0 < W) (M : ℕ) :
    (1 + X * Real.sqrt (1 - a) / W) ^ M ≤ 3 ^ M * (1 + X / (2 ^ j * W)) ^ M := by
  obtain ⟨-, hJ2⟩ := shellCount_spec a ha0 ha1
  have hpos : 0 < 1 - a := by linarith
  have h4j : (4 : ℝ) ^ j ≤ 4 ^ shellCount a := pow_le_pow_right₀ (by norm_num) hj
  have h1 : (1 - a) * 4 ^ shellCount a ≤ 8 := by
    have := mul_lt_mul_of_pos_left hJ2 hpos
    have e : (1 - a) * (4 * ((1 - a)⁻¹ + 1)) = 4 + 4 * (1 - a) := by field_simp
    rw [e] at this; linarith
  have h2 : 1 - a ≤ (3 / 2 ^ j) ^ 2 := by
    have e2 : (3 / (2 : ℝ) ^ j) ^ 2 = 9 / 4 ^ j := by
      rw [div_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
    rw [e2, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h4j hpos.le]
  have hsq : Real.sqrt (1 - a) ≤ 3 / 2 ^ j :=
    Real.sqrt_le_iff.2 ⟨by positivity, h2⟩
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have : X * Real.sqrt (1 - a) / W ≤ 3 * (X / (2 ^ j * W)) := by
    calc X * Real.sqrt (1 - a) / W ≤ X * (3 / 2 ^ j) / W := by gcongr
      _ = 3 * (X / (2 ^ j * W)) := by field_simp
  have : 0 ≤ X / (2 ^ j * W) := by positivity
  linarith


end Linear

/-! ## Second differences and the factor `cos(p·y) - 1` -/

section SecondDifference

/-- Multiplying the symbol by `e^{ip·y}` translates the kernel by `y`. -/
private theorem latticeFourier_mul_zexp (F : (Fin d → ℝ) → ℂ) (x y : Fin d → ℤ) :
    latticeFourier (fun p => F p * zexp p y) x = latticeFourier F (x - y) := by
  unfold latticeFourier
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  rw [mul_assoc, ← zexp_add]
  congr 2
  abel

/-- The linear form `p ↦ p·y` on `ℝ^d`. -/
private def dotL (y : Fin d → ℤ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ j, ((y j : ℤ) : ℝ) • ContinuousLinearMap.proj j

private theorem dotL_apply (y : Fin d → ℤ) (p : Fin d → ℝ) :
    dotL y p = ∑ j, p j * (y j : ℝ) := by
  simp [dotL, mul_comm]

private theorem norm_dotL_le (y : Fin d → ℤ) : ‖dotL y‖ ≤ d * (zdInf y : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  rw [dotL_apply, Real.norm_eq_abs]
  calc |∑ j, p j * (y j : ℝ)| ≤ ∑ j, |p j * (y j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, ‖p‖ * (zdInf y : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm p j)
          (natAbs_le_zdInf' y j) (abs_nonneg _) (norm_nonneg _)
    _ = d * (zdInf y : ℝ) * ‖p‖ := by simp; ring

/-- The factor `cos(p·y) - 1` of the second difference in the direction `y`. -/
private def cosM (y : Fin d → ℤ) (p : Fin d → ℝ) : ℝ := Real.cos (dotL y p) - 1

private theorem cosM_eq (y : Fin d → ℤ) (p : Fin d → ℝ) :
    ((cosM y p : ℝ) : ℂ) = (zexp p y + zexp p (-y)) / 2 - 1 := by
  have h2 : zexp p y = Complex.exp (((dotL y p : ℝ) : ℂ) * I) := by
    unfold zexp; rw [dotL_apply]
  have h1 : zexp p (-y) = Complex.exp (-((dotL y p : ℝ) : ℂ) * I) := by
    unfold zexp; rw [dotL_apply]; congr 1; push_cast
    rw [← Finset.sum_neg_distrib]; congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.neg_apply, Int.cast_neg]; ring
  rw [cosM, Complex.ofReal_sub, Complex.ofReal_cos, Complex.cos, h1, h2]
  push_cast
  ring

private theorem contDiff_cosM (y : Fin d → ℤ) : ContDiff ℝ ∞ (cosM y) :=
  (Real.contDiff_cos.comp (dotL y).contDiff).sub contDiff_const

private theorem abs_cosM_le_two (y : Fin d → ℤ) (p : Fin d → ℝ) : |cosM y p| ≤ 2 := by
  unfold cosM
  have := Real.neg_one_le_cos (dotL y p)
  have := Real.cos_le_one (dotL y p)
  rw [abs_le]; constructor <;> linarith

/-- `|cos(p·y) - 1| ≤ (d |y| ‖p‖)²/2`. -/
private theorem abs_cosM_le (y : Fin d → ℤ) (p : Fin d → ℝ) :
    |cosM y p| ≤ ((d : ℝ) * zdInf y * ‖p‖) ^ 2 / 2 := by
  unfold cosM
  have h1 := Real.one_sub_sq_div_two_le_cos (x := dotL y p)
  have h2 := Real.cos_le_one (dotL y p)
  have h3 : |dotL y p| ≤ (d : ℝ) * zdInf y * ‖p‖ := by
    rw [← Real.norm_eq_abs]
    exact ((dotL y).le_opNorm p).trans (mul_le_mul_of_nonneg_right (norm_dotL_le y)
      (norm_nonneg _))
  have h4 : (dotL y p) ^ 2 ≤ ((d : ℝ) * zdInf y * ‖p‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- `‖D(cos(p·y) - 1)‖ ≤ (d |y|)² ‖p‖`. -/
private theorem norm_fderiv_cosM_le (y : Fin d → ℤ) (p : Fin d → ℝ) :
    ‖fderiv ℝ (cosM y) p‖ ≤ ((d : ℝ) * zdInf y) ^ 2 * ‖p‖ := by
  have hd : HasFDerivAt (cosM y) ((-Real.sin (dotL y p)) • dotL y) p := by
    have := ((Real.hasDerivAt_cos (dotL y p)).comp_hasFDerivAt p (dotL y).hasFDerivAt).sub_const
      (1 : ℝ)
    exact this
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, abs_neg]
  have h1 : |Real.sin (dotL y p)| ≤ |dotL y p| := Real.abs_sin_le_abs
  have h3 : |dotL y p| ≤ (d : ℝ) * zdInf y * ‖p‖ := by
    rw [← Real.norm_eq_abs]
    exact ((dotL y).le_opNorm p).trans (mul_le_mul_of_nonneg_right (norm_dotL_le y)
      (norm_nonneg _))
  calc |Real.sin (dotL y p)| * ‖dotL y‖ ≤ ((d : ℝ) * zdInf y * ‖p‖) * ((d : ℝ) * zdInf y) :=
        mul_le_mul (h1.trans h3) (norm_dotL_le y) (norm_nonneg _) (by positivity)
    _ = ((d : ℝ) * zdInf y) ^ 2 * ‖p‖ := by ring

/-- `‖D^k(cos(p·y) - 1)‖ ≤ (d |y|)^k` for `k ≥ 1`. -/
private theorem norm_iteratedFDeriv_cosM_le (y : Fin d → ℤ) {k : ℕ} (hk : k ≠ 0)
    (p : Fin d → ℝ) : ‖iteratedFDeriv ℝ k (cosM y) p‖ ≤ ((d : ℝ) * zdInf y) ^ k := by
  have he : cosM y = fun q => (-1 : ℝ) + 1 * (Real.cos ∘ dotL y) q := by
    funext q; simp [cosM]; ring
  have hc : ContDiff ℝ ∞ (Real.cos ∘ dotL y) := Real.contDiff_cos.comp (dotL y).contDiff
  rw [he, norm_iteratedFDeriv_affine hc _ _ hk, abs_one, one_mul,
    (dotL y).iteratedFDeriv_comp_right Real.contDiff_cos p (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hcos : ‖iteratedFDeriv ℝ k Real.cos (dotL y p)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_cos_le_one k _
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ‖iteratedFDeriv ℝ k Real.cos (dotL y p)‖ * ‖dotL y‖ ^ k ≤ 1 * ((d : ℝ) * zdInf y) ^ k :=
        mul_le_mul hcos (pow_le_pow_left₀ (norm_nonneg _) (norm_dotL_le y) k) (by positivity)
          zero_le_one
    _ = _ := one_mul _

/-- The second difference of a kernel: the symbol `(cos(p·y) - 1) F(p)` has the kernel
`(K(x + y) + K(x - y))/2 - K(x)`, `K` the kernel of `F`. -/
private theorem latticeFourier_cosM_mul {F : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (y x : Fin d → ℤ) :
    latticeFourier (fun p => ((cosM y p : ℝ) : ℂ) * F p) x =
      (latticeFourier F (x + y) + latticeFourier F (x - y)) / 2 - latticeFourier F x := by
  have hi : ∀ z : Fin d → ℤ, IntegrableOn (fun p => F p * zexp p z) (cubePi d) := fun z =>
    hF.mul_continuousOn (continuous_zexp' z).continuousOn isCompact_cubePi''
  have he : (fun p => ((cosM y p : ℝ) : ℂ) * F p) =
      fun p => ((1 / 2 : ℂ) * (F p * zexp p y + F p * zexp p (-y))) - F p := by
    funext p; rw [cosM_eq]; ring
  have hs : IntegrableOn (fun p => (1 / 2 : ℂ) * (F p * zexp p y + F p * zexp p (-y)))
      (cubePi d) := ((hi y).add (hi (-y))).const_mul _
  rw [he, latticeFourier_sub (F := fun p => (1 / 2 : ℂ) * (F p * zexp p y + F p * zexp p (-y)))
      (G := F) hs hF,
    latticeFourier_const_mul,
    latticeFourier_add (F := fun p => F p * zexp p y) (G := fun p => F p * zexp p (-y)) (hi y)
      (hi (-y)), latticeFourier_mul_zexp, latticeFourier_mul_zexp, sub_neg_eq_add]
  ring

end SecondDifference

/-! ## The rescaled cutoff `(L/|y|)² χ (cos(p·y) - 1)` -/

section CancelCut

/-- The cutoff `(L/|y|)² χ(p) (cos(p·y) - 1)` of the second difference at scale `L ≥ |y|`. -/
private def cancelCut (L : ℝ) (y : Fin d → ℤ) (χ : (Fin d → ℝ) → ℝ) (p : Fin d → ℝ) : ℝ :=
  (L / zdInf y) ^ 2 * (χ p * cosM y p)

private theorem contDiff_cancelCut (L : ℝ) (y : Fin d → ℤ) {χ : (Fin d → ℝ) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (cancelCut L y χ) :=
  contDiff_const.mul (hχ.mul (contDiff_cosM y))

/-- At a point with `‖p‖ ≤ 2/L` and `|y| ≤ L`: `‖D^i (cos(p·y) - 1)‖ ≤ E (|y|/L)² L^i` for
`i ≤ n`, with `E = 2 max(d, 1)^{n+2}`. -/
private theorem norm_iteratedFDeriv_cosM_scaled (n : ℕ) {L : ℝ} (hL : 0 < L) (y : Fin d → ℤ)
    (hyL : (zdInf y : ℝ) ≤ L) {p : Fin d → ℝ} (hp : ‖p‖ ≤ 2 / L) :
    ∀ i ≤ n, ‖iteratedFDeriv ℝ i (cosM y) p‖ ≤
      (2 * (max (d : ℝ) 1) ^ (n + 2) * ((zdInf y : ℝ) / L) ^ 2) * L ^ i := by
  intro i hi
  set Y : ℝ := (zdInf y : ℝ) with hY
  set D' : ℝ := max (d : ℝ) 1 with hD'
  have hD1 : 1 ≤ D' := le_max_right _ _
  have hdD : (d : ℝ) ≤ D' := le_max_left _ _
  have hY0 : 0 ≤ Y := Nat.cast_nonneg _
  have hdY : (d : ℝ) * Y ≤ D' * Y := mul_le_mul_of_nonneg_right hdD hY0
  have hpow : ∀ m ≤ n + 2, D' ^ m ≤ D' ^ (n + 2) := fun m hm => pow_le_pow_right₀ hD1 hm
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · rcases Nat.lt_or_ge i 1 with h1 | h1
    · have hi0 : i = 0 := by omega
      subst hi0
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one]
      refine (abs_cosM_le y p).trans ?_
      have h3 : (d : ℝ) * Y * ‖p‖ ≤ D' * Y * (2 / L) :=
        mul_le_mul hdY hp (norm_nonneg _) (by positivity)
      have h4 : ((d : ℝ) * Y * ‖p‖) ^ 2 ≤ (D' * Y * (2 / L)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
      have h5 : D' ^ 2 ≤ D' ^ (n + 2) := hpow 2 (by omega)
      calc ((d : ℝ) * Y * ‖p‖) ^ 2 / 2 ≤ (D' * Y * (2 / L)) ^ 2 / 2 := by linarith
        _ = 2 * D' ^ 2 * (Y / L) ^ 2 := by field_simp
        _ ≤ 2 * D' ^ (n + 2) * (Y / L) ^ 2 := by gcongr
    · have hi1 : i = 1 := by omega
      subst hi1
      rw [norm_iteratedFDeriv_one, pow_one]
      refine (norm_fderiv_cosM_le y p).trans ?_
      have h3 : ((d : ℝ) * Y) ^ 2 ≤ (D' * Y) ^ 2 := pow_le_pow_left₀ (by positivity) hdY 2
      have h5 : D' ^ 2 ≤ D' ^ (n + 2) := hpow 2 (by omega)
      calc ((d : ℝ) * Y) ^ 2 * ‖p‖ ≤ (D' * Y) ^ 2 * (2 / L) :=
            mul_le_mul h3 hp (norm_nonneg _) (by positivity)
        _ = 2 * D' ^ 2 * (Y / L) ^ 2 * L := by field_simp
        _ ≤ 2 * D' ^ (n + 2) * (Y / L) ^ 2 * L := by gcongr
  · refine (norm_iteratedFDeriv_cosM_le y (by omega) p).trans ?_
    have h3 : ((d : ℝ) * Y) ^ i ≤ (D' * Y) ^ i := pow_le_pow_left₀ (by positivity) hdY i
    have hYi : Y ^ i ≤ Y ^ 2 * L ^ (i - 2) := by
      have : Y ^ i = Y ^ 2 * Y ^ (i - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY0 hyL _) (by positivity)
    have hLi : L ^ i = L ^ 2 * L ^ (i - 2) := by rw [← pow_add]; congr 1; omega
    have h5 : D' ^ i ≤ D' ^ (n + 2) := hpow i (by omega)
    calc ((d : ℝ) * Y) ^ i ≤ (D' * Y) ^ i := h3
      _ = D' ^ i * Y ^ i := mul_pow _ _ _
      _ ≤ D' ^ (n + 2) * (Y ^ 2 * L ^ (i - 2)) :=
          mul_le_mul h5 hYi (by positivity) (by positivity)
      _ ≤ 2 * D' ^ (n + 2) * (Y / L) ^ 2 * L ^ i := by
          rw [hLi, div_pow]
          have : 0 ≤ D' ^ (n + 2) * (Y ^ 2 * L ^ (i - 2)) := by positivity
          field_simp
          nlinarith

/-- Scale-uniform derivative bounds of `cancelCut`: if `‖D^i χ‖ ≤ Cχ_i L^i`, `χ` vanishes off
`‖p‖ < 2/L` and `1 ≤ |y| ≤ L`, then `‖D^n cancelCut‖ ≤ B L^n`, with `B` depending only on `d`,
`Cχ` and `n`. -/
private theorem cancelCut_deriv_le (Cχ : ℕ → ℝ) (n : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ (L : ℝ) (y : Fin d → ℤ) (χ : (Fin d → ℝ) → ℝ), 0 < L → 1 ≤ zdInf y →
      (zdInf y : ℝ) ≤ L → ContDiff ℝ ∞ χ → (∀ i p, ‖iteratedFDeriv ℝ i χ p‖ ≤ Cχ i * L ^ i) →
      (∀ p, χ p ≠ 0 → ‖p‖ < 2 / L) →
      ∀ p, ‖iteratedFDeriv ℝ n (cancelCut L y χ) p‖ ≤ B * L ^ n := by
  set Cs : ℝ := ∑ i ∈ Finset.range (n + 1), |Cχ i| with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun i _ => abs_nonneg _
  set E : ℝ := 2 * (max (d : ℝ) 1) ^ (n + 2) with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨2 ^ n * Cs * E, by positivity, ?_⟩
  intro L y χ hL hy1 hyL hχ hCχ hsupp p
  have hY1 : (1 : ℝ) ≤ zdInf y := by exact_mod_cast hy1
  have hY0 : (0 : ℝ) < zdInf y := by linarith
  by_cases hp : 2 / L < ‖p‖
  · have hz : cancelCut L y χ =ᶠ[nhds p] 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hp] with q hq
      have : χ q = 0 := by
        by_contra h
        have := hsupp q h
        exact lt_irrefl _ (hq.trans this)
      simp [cancelCut, this]
    rw [iteratedFDeriv_eq_zero_of_eventuallyEq hz, norm_zero]
    positivity
  push Not at hp
  have hA : ∀ i ≤ n, ‖iteratedFDeriv ℝ i χ p‖ ≤ Cs * L ^ i := by
    intro i hi
    refine (hCχ i p).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Cχ i|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
  have hB := norm_iteratedFDeriv_cosM_scaled n hL y hyL hp
  have hprod := norm_iteratedFDeriv_mul_le_of hχ (contDiff_cosM y) p n hL.le hA hB
  have he : cancelCut L y χ = ((L / zdInf y) ^ 2) • fun q => χ q * cosM y q := by
    funext q; simp [cancelCut, smul_eq_mul]
  rw [he, iteratedFDeriv_const_smul_apply
    (((hχ.mul (contDiff_cosM y)).contDiffAt).of_le (by exact_mod_cast le_top)), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (L / zdInf y) ^ 2 * ‖iteratedFDeriv ℝ n (fun q => χ q * cosM y q) p‖
      ≤ (L / zdInf y) ^ 2 * (2 ^ n * Cs * (E * ((zdInf y : ℝ) / L) ^ 2) * L ^ n) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 2 ^ n * Cs * E * L ^ n := by
        field_simp

end CancelCut

/-! ## Pieces of the second difference -/

section Pieces

/-- The symbol `a ŝ/(1 - a ŝ)` of `Θ_{ℤ^d}(a)`. -/
private def thetaSym (a : ℝ) (s : (Fin d → ℤ) → ℝ) (p : Fin d → ℝ) : ℂ :=
  (a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p)

/-- The symbol `(cos(p·y) - 1) a ŝ(p)/(1 - a ŝ(p))` of the second difference of `Θ_{ℤ^d}(a)` in
the direction `y`. -/
private def cancelSym (a : ℝ) (s : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) (p : Fin d → ℝ) : ℂ :=
  ((cosM y p : ℝ) : ℂ) * thetaSym a s p

private theorem latticeFourier_cancelCut (L : ℝ) (y : Fin d → ℤ) (χ : (Fin d → ℝ) → ℝ)
    (F : (Fin d → ℝ) → ℂ) (x : Fin d → ℤ) :
    latticeFourier (fun p => (cancelCut L y χ p : ℂ) * F p) x =
      (((L / zdInf y) ^ 2 : ℝ) : ℂ) *
        latticeFourier (fun p => (χ p : ℂ) * (((cosM y p : ℝ) : ℂ) * F p)) x := by
  rw [← latticeFourier_const_mul]
  congr 1
  funext p
  simp only [cancelCut]
  push_cast
  ring

private theorem norm_mul_sq_cast {z : ℂ} {r : ℝ} : ‖((r ^ 2 : ℝ) : ℂ) * z‖ = r ^ 2 * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- One dyadic shell of the second difference in the direction `y`, `1 ≤ |y| ≤ 2^j W`,
uniformly in `a ∈ [0, 1]`: `|K(x)| (2^j W/|y|)² (1 + |x|/(2^j W))^M ≤ C₀ 4^j (2^j W)^{-d}`,
where `K` has symbol `χ_j(p) (cos(p·y) - 1) a ŝ(p)/(1 - a ŝ(p))`. -/
private theorem shell_cancel_bound (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) (M : ℕ) :
    ∃ C₀ W₀ : ℝ, 0 ≤ C₀ ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ (a : ℝ), 0 ≤ a → a ≤ 1 → ∀ (j : ℕ) (y : Fin d → ℤ), 1 ≤ zdInf y →
        (zdInf y : ℝ) ≤ 2 ^ j * W → ∀ x : Fin d → ℤ,
          ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x‖ *
            ((2 ^ j * W) / zdInf y) ^ 2 * (1 + (zdInf x : ℝ) / (2 ^ j * W)) ^ M ≤
              C₀ * 4 ^ j / (2 ^ j * (W : ℝ)) ^ d := by
  choose K hK using fun i => zdSymbol_smooth d ψ C i
  choose Cc hCc using norm_iteratedFDeriv_cut_le d
  choose B hB0 hB using fun n => cancelCut_deriv_le (d := d) Cc n
  obtain ⟨c, W₁, hc, hW₁⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  have hc1 : 0 < min c 1 := lt_min hc one_pos
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    shellKernel_piece_kernel_bound (d := d) K B (b := min c 1 / 4) (by positivity) M
  refine ⟨C₀, max 1 W₁, hC₀0, ?_⟩
  intro W hW s hs a ha0 ha1 j y hy1 hyL x
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set L : ℝ := 2 ^ j * W with hL
  have hL0 : 0 < L := by positivity
  have hcd := (hK 0 W hWn s hs).1
  have hKall : ∀ i p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ K i * (W : ℝ) ^ i :=
    fun i p => (hK i W hWn s hs).2.2 p
  have hK2 := hs.norm_fderiv_le hcd (fun q => hKall 2 q)
  set R : Set (Fin d → ℝ) := {p | ((4 : ℝ) ^ (j + 1))⁻¹ ≤ (W : ℝ) ^ 2 * sqNorm p ∧
      (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ j} with hRdef
  have hR : ∀ p ∈ R, (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ j ∧
      min c 1 / 4 ≤ 4 ^ j * (1 - a * (zdSymbol s p).re) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨hp2, ?_⟩
    have h4 : (4 : ℝ) / 4 ^ j ≤ 4 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have hcube := mem_cubePi_of_sqNorm_le hW1 (hp2.trans h4)
    obtain ⟨-, hge⟩ := hW₁ W (le_trans (le_max_right _ _) hW) s hs p hcube
    have hX : 0 ≤ (W : ℝ) ^ 2 * sqNorm p := mul_nonneg (by positivity) (sqNorm_nonneg' p)
    have h1 := one_sub_mul_ge hc ha0 ha1 hX hge
    have hmin : ((4 : ℝ) ^ (j + 1))⁻¹ ≤ min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
      le_min hp1 (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
    have h2 : min c 1 * ((4 : ℝ) ^ (j + 1))⁻¹ ≤ 1 - a * (zdSymbol s p).re :=
      (mul_le_mul_of_nonneg_left hmin hc1.le).trans h1
    calc min c 1 / 4 = 4 ^ j * (min c 1 * ((4 : ℝ) ^ (j + 1))⁻¹) := by
          rw [pow_succ]; field_simp
      _ ≤ 4 ^ j * (1 - a * (zdSymbol s p).re) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsuppχ : ∀ p, shellCut (d := d) W j p ≠ 0 → ‖p‖ < 2 / L := fun p hp =>
    norm_lt_of_sqNorm_lt hW0 j (shellCut_support W j p hp).2
  have hχc : ContDiff ℝ ∞ (cancelCut L y (shellCut (d := d) W j)) :=
    contDiff_cancelCut L y (contDiff_shellCut W j)
  have hχd : ∀ i p, ‖iteratedFDeriv ℝ i (cancelCut L y (shellCut (d := d) W j)) p‖ ≤
      B i * (2 ^ j * (W : ℝ)) ^ i := fun i p =>
    hB i L y (shellCut W j) hL0 hy1 hyL (contDiff_shellCut W j) (fun i p => (hCc i W j p).1)
      hsuppχ p
  have hRχ : ∀ p ∉ R, cancelCut L y (shellCut (d := d) W j) =ᶠ[nhds p] 0 := fun p hp => by
    filter_upwards [shellCut_eventually_zero hp] with q hq
    simp only [Pi.zero_apply] at hq
    simp [cancelCut, hq]
  have hsupp : ∀ p, cancelCut L y (shellCut (d := d) W j) p ≠ 0 →
      (W : ℝ) ^ 2 * sqNorm p < 4 / 4 ^ j := fun p hp => by
    have : shellCut (d := d) W j p ≠ 0 := by intro h; apply hp; simp [cancelCut, h]
    exact (shellCut_support W j p this).2
  have h := hC₀ W j a s (cancelCut L y (shellCut W j)) R hW1 ha0 ha1 hcd hs.im_eq hKall hK2 hχc
    hχd hRχ hR hsupp x
  have he := latticeFourier_cancelCut L y (shellCut (d := d) W j) (thetaSym a s) x
  simp only [thetaSym] at he
  rw [he, norm_mul_sq_cast] at h
  simp only [cancelSym, thetaSym]
  refine le_of_eq_of_le ?_ h
  ring

/-- The core of the second difference at `J = shellCount a`, `a < 1`, `1 ≤ |y| ≤ 2^J W`:
`|K(x)| (2^J W/|y|)² (1 + |x|/(2^J W))^M ≤ C₀ 4^J (2^J W)^{-d}`, where `K` has symbol
`χ_core(p) (cos(p·y) - 1) a ŝ(p)/(1 - a ŝ(p))`. -/
private theorem core_cancel_bound (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) (M : ℕ) :
    ∃ C₀ W₀ : ℝ, 0 ≤ C₀ ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ (a : ℝ), 0 ≤ a → a < 1 → ∀ (y : Fin d → ℤ), 1 ≤ zdInf y →
        (zdInf y : ℝ) ≤ 2 ^ shellCount a * W → ∀ x : Fin d → ℤ,
          ‖latticeFourier (fun p => (coreCut W (shellCount a) p : ℂ) * cancelSym a s y p) x‖ *
            ((2 ^ shellCount a * W) / zdInf y) ^ 2 *
              (1 + (zdInf x : ℝ) / (2 ^ shellCount a * W)) ^ M ≤
              C₀ * 4 ^ shellCount a / (2 ^ shellCount a * (W : ℝ)) ^ d := by
  choose K hK using fun i => zdSymbol_smooth d ψ C i
  choose Cc hCc using norm_iteratedFDeriv_cut_le d
  choose B hB0 hB using fun n => cancelCut_deriv_le (d := d) Cc n
  obtain ⟨c, W₁, hc, hW₁⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    shellKernel_piece_kernel_bound (d := d) K B (b := 1 / 2) (by norm_num) M
  refine ⟨C₀, max 1 W₁, hC₀0, ?_⟩
  intro W hW s hs a ha0 ha y hy1 hyL x
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set J := shellCount a with hJ
  obtain ⟨hJ1, -⟩ := shellCount_spec a ha0 ha
  set L : ℝ := 2 ^ J * W with hL
  have hL0 : 0 < L := by positivity
  have hcd := (hK 0 W hWn s hs).1
  have hKall : ∀ i p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ K i * (W : ℝ) ^ i :=
    fun i p => (hK i W hWn s hs).2.2 p
  have hK2 := hs.norm_fderiv_le hcd (fun q => hKall 2 q)
  set R : Set (Fin d → ℝ) := {p | (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ J} with hRdef
  have hR : ∀ p ∈ R, (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ J ∧
      1 / 2 ≤ 4 ^ J * (1 - a * (zdSymbol s p).re) := by
    intro p hp
    refine ⟨hp, ?_⟩
    have h4 : (4 : ℝ) / 4 ^ J ≤ 4 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have hcube := mem_cubePi_of_sqNorm_le hW1 ((show (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ J
      from hp).trans h4)
    obtain ⟨-, hge⟩ := hW₁ W (le_trans (le_max_right _ _) hW) s hs p hcube
    have hX : 0 ≤ min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
      le_min (mul_nonneg (by positivity) (sqNorm_nonneg' p)) zero_le_one
    have hσ1 : (zdSymbol s p).re ≤ 1 := by nlinarith
    have h1 := one_sub_mul_ge_half ha0 ha.le hσ1
    have hpos : 0 < 1 - a := by linarith
    have h2 : 1 ≤ (4 : ℝ) ^ J * (1 - a) := by
      rw [inv_le_iff_one_le_mul₀ hpos] at hJ1; linarith
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) J]
  have hcsupp : ∀ p, coreCut (d := d) W J p ≠ 0 → (W : ℝ) ^ 2 * sqNorm p < 4 / 4 ^ J := by
    intro p hp
    by_contra hle
    push Not at hle
    apply hp
    unfold coreCut
    apply lowPass_eq_zero'
    rw [div_le_iff₀ (by positivity)] at hle
    nlinarith
  have hsuppχ : ∀ p, coreCut (d := d) W J p ≠ 0 → ‖p‖ < 2 / L := fun p hp =>
    norm_lt_of_sqNorm_lt hW0 J (hcsupp p hp)
  have hχc : ContDiff ℝ ∞ (cancelCut L y (coreCut (d := d) W J)) :=
    contDiff_cancelCut L y (contDiff_coreCut W J)
  have hχd : ∀ i p, ‖iteratedFDeriv ℝ i (cancelCut L y (coreCut (d := d) W J)) p‖ ≤
      B i * (2 ^ J * (W : ℝ)) ^ i := fun i p =>
    hB i L y (coreCut W J) hL0 hy1 hyL (contDiff_coreCut W J) (fun i p => (hCc i W J p).2.1)
      hsuppχ p
  have hRχ : ∀ p ∉ R, cancelCut L y (coreCut (d := d) W J) =ᶠ[nhds p] 0 := fun p hp => by
    filter_upwards [coreCut_eventually_zero hp] with q hq
    simp only [Pi.zero_apply] at hq
    simp [cancelCut, hq]
  have hsupp : ∀ p, cancelCut L y (coreCut (d := d) W J) p ≠ 0 →
      (W : ℝ) ^ 2 * sqNorm p < 4 / 4 ^ J := fun p hp => by
    have : coreCut (d := d) W J p ≠ 0 := by intro h; apply hp; simp [cancelCut, h]
    exact hcsupp p this
  have h := hC₀ W J a s (cancelCut L y (coreCut W J)) R hW1 ha0 ha.le hcd hs.im_eq hKall hK2 hχc
    hχd hRχ hR hsupp x
  have he := latticeFourier_cancelCut L y (coreCut (d := d) W J) (thetaSym a s) x
  simp only [thetaSym] at he
  rw [he, norm_mul_sq_cast] at h
  simp only [cancelSym, thetaSym]
  refine le_of_eq_of_le ?_ h
  ring

end Pieces

/-! ## The second difference far from the origin -/

section Single

/-- Crude bound for a second difference far from the origin: if `|k(x)| (1 + |x|/L)^N ≤ A` and
`2|y| ≤ |x₀|`, then `|(k(x₀ + y) + k(x₀ - y))/2 - k(x₀)| ≤ 2 A (2L/|x₀|)^N`. -/
private theorem crude_second_diff {k : (Fin d → ℤ) → ℂ} {A L : ℝ} {N : ℕ} (hL : 0 < L)
    (hk : ∀ x, ‖k x‖ * (1 + (zdInf x : ℝ) / L) ^ N ≤ A) (x₀ y : Fin d → ℤ)
    (hX : 0 < (zdInf x₀ : ℝ)) (hy : 2 * (zdInf y : ℝ) ≤ zdInf x₀) :
    ‖(k (x₀ + y) + k (x₀ - y)) / 2 - k x₀‖ ≤ 2 * A * (2 * L / zdInf x₀) ^ N := by
  set X : ℝ := (zdInf x₀ : ℝ) with hXdef
  have hpt : ∀ z : Fin d → ℤ, X / 2 ≤ zdInf z → ‖k z‖ ≤ A * (2 * L / X) ^ N := by
    intro z hz
    have hw : (X / (2 * L)) ^ N ≤ (1 + (zdInf z : ℝ) / L) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      have : X / (2 * L) ≤ (zdInf z : ℝ) / L := by
        rw [div_le_div_iff₀ (by positivity) hL]; nlinarith
      have : (0 : ℝ) ≤ 1 := zero_le_one
      linarith
    have hpos : 0 < (X / (2 * L)) ^ N := by positivity
    have h1 : ‖k z‖ * (X / (2 * L)) ^ N ≤ A :=
      (mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans (hk z)
    have e : (2 * L / X) ^ N = ((X / (2 * L)) ^ N)⁻¹ := by rw [← inv_pow, inv_div]
    rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos]; exact h1
  have h1 : X / 2 ≤ zdInf (x₀ + y) := by
    have h := zdInf_add_le (x₀ + y) (-y)
    rw [add_neg_cancel_right, zdInf_neg] at h
    have : X ≤ zdInf (x₀ + y) + zdInf y := by rw [hXdef]; exact_mod_cast h
    linarith
  have h2 : X / 2 ≤ zdInf (x₀ - y) := by
    have h := zdInf_add_le (x₀ - y) y
    rw [sub_add_cancel] at h
    have : X ≤ zdInf (x₀ - y) + zdInf y := by rw [hXdef]; exact_mod_cast h
    linarith
  have h3 : X / 2 ≤ zdInf x₀ := by rw [← hXdef]; linarith
  calc ‖(k (x₀ + y) + k (x₀ - y)) / 2 - k x₀‖
      ≤ (‖k (x₀ + y)‖ + ‖k (x₀ - y)‖) / 2 + ‖k x₀‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_div, Complex.norm_two]
        gcongr
        exact norm_add_le _ _
    _ ≤ (A * (2 * L / X) ^ N + A * (2 * L / X) ^ N) / 2 + A * (2 * L / X) ^ N := by
        gcongr
        · exact hpt _ h1
        · exact hpt _ h2
        · exact hpt _ h3
    _ = 2 * A * (2 * L / X) ^ N := by ring

end Single

section SingleBound

/-- The crude part: `3K · 2A (2K/X)^N ≤ (Y/X)² X^{-D}` for `1 ≤ Y`, `1 ≤ K ≤ X^{1/(1+c)}`,
`6 A 2^N ≤ X` and `N ≥ (4 + D)(1 + c)/c`. -/
private theorem crude_total_le {A c D K X Y : ℝ} {N : ℕ} (hA : 0 ≤ A) (hc : 0 < c) (hD : 0 < D)
    (hN : (4 + D) * (1 + c) / c ≤ N) (hK1 : 1 ≤ K) (hX1 : 1 ≤ X) (hY1 : 1 ≤ Y)
    (hKX : K ≤ X ^ (1 / (1 + c))) (hAX : 6 * A * 2 ^ N ≤ X) :
    3 * K * (2 * A * (2 * K / X) ^ N) ≤ (Y / X) ^ 2 * X ^ (-D) := by
  have hX0 : 0 < X := by linarith
  have hc1 : 0 < 1 + c := by linarith
  have hNc : (4 + D) * (1 + c) ≤ N * c := by rwa [div_le_iff₀ hc] at hN
  set e : ℝ := ((N : ℝ) + 1) / (1 + c) + 2 + D with he
  have hexp : e ≤ (N : ℝ) - 1 := by
    rw [he]
    have : ((N : ℝ) + 1) / (1 + c) ≤ N - 3 - D := by
      rw [div_le_iff₀ hc1]; nlinarith
    linarith
  have hKN : K ^ (N + 1) ≤ X ^ (((N : ℝ) + 1) / (1 + c)) := by
    calc K ^ (N + 1) ≤ (X ^ (1 / (1 + c))) ^ (N + 1) := pow_le_pow_left₀ (by linarith) hKX _
      _ = X ^ (((N : ℝ) + 1) / (1 + c)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; push_cast; ring_nf
  have hXe : X ^ (((N : ℝ) + 1) / (1 + c)) * X ^ (2 : ℕ) * X ^ D = X ^ e := by
    rw [he, Real.rpow_add hX0, Real.rpow_add hX0, ← Real.rpow_natCast]; push_cast; ring
  have hXN : X * X ^ e ≤ X ^ N := by
    calc X * X ^ e ≤ X * X ^ ((N : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 hexp) hX0.le
      _ = X ^ N := by
          rw [← Real.rpow_natCast, mul_comm, ← Real.rpow_add_one hX0.ne']; ring_nf
  have hXD : 0 < X ^ D := Real.rpow_pos_of_pos hX0 D
  have hmain : 6 * A * 2 ^ N * K ^ (N + 1) * (X ^ 2 * X ^ D) ≤ X ^ N := by
    calc 6 * A * 2 ^ N * K ^ (N + 1) * (X ^ 2 * X ^ D)
        ≤ X * X ^ (((N : ℝ) + 1) / (1 + c)) * (X ^ 2 * X ^ D) := by
          gcongr
      _ = X * X ^ e := by rw [← hXe]; ring
      _ ≤ X ^ N := hXN
  have hlhs : 3 * K * (2 * A * (2 * K / X) ^ N) = 6 * A * 2 ^ N * K ^ (N + 1) / X ^ N := by
    rw [div_pow, mul_pow, pow_succ]; field_simp; ring
  have hrhs : 1 / (X ^ 2 * X ^ D) ≤ (Y / X) ^ 2 * X ^ (-D) := by
    rw [Real.rpow_neg hX0.le, div_pow]
    have : 1 ≤ Y ^ 2 := one_le_pow₀ hY1
    have h2 : 1 / (X ^ 2 * X ^ D) = 1 / X ^ 2 * (X ^ D)⁻¹ := by field_simp
    rw [h2]
    gcongr
  rw [hlhs]
  refine le_trans ?_ hrhs
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

end SingleBound

section SingleBound2

/-- The main part: `C₀ Y² W^{-(d+2)} (1 + X/W)^{-d} ≤ (Y/X)² C₀ W^{-2} (X + W)^{-(d-2)}`. -/
private theorem main_conv_le {C₀ X Y W : ℝ} {d : ℕ} (hd : 2 ≤ d) (hC : 0 ≤ C₀) (hX : 0 < X)
    (hW : 0 < W) :
    C₀ * Y ^ 2 / W ^ (d + 2) * ((1 + X / W) ^ d)⁻¹ ≤
      (Y / X) ^ 2 * (C₀ / (W ^ 2 * (X + W) ^ (d - 2))) := by
  have e1 : W ^ (d + 2) * (1 + X / W) ^ d = W ^ 2 * (X + W) ^ d := by
    rw [show 1 + X / W = (X + W) / W by field_simp; ring, div_pow, pow_add]
    field_simp
  have e2 : (X + W) ^ d = (X + W) ^ 2 * (X + W) ^ (d - 2) := by
    rw [← pow_add]; congr 1; omega
  have hXW : X ^ 2 ≤ (X + W) ^ 2 := pow_le_pow_left₀ hX.le (by linarith) 2
  calc C₀ * Y ^ 2 / W ^ (d + 2) * ((1 + X / W) ^ d)⁻¹
      = C₀ * Y ^ 2 / (W ^ 2 * (X + W) ^ 2 * (X + W) ^ (d - 2)) := by
        have h3 : W ^ 2 * (X + W) ^ 2 * (X + W) ^ (d - 2) = W ^ (d + 2) * (1 + X / W) ^ d := by
          rw [e1, e2]; ring
        rw [h3]
        simp only [div_eq_mul_inv, mul_inv]
        ring
    _ ≤ C₀ * Y ^ 2 / (W ^ 2 * X ^ 2 * (X + W) ^ (d - 2)) := by
        gcongr
    _ = (Y / X) ^ 2 * (C₀ / (W ^ 2 * (X + W) ^ (d - 2))) := by
        field_simp

end SingleBound2

section SingleDirection

/-- The second difference of `Θ_{ℤ^d}(a)` in one direction `y`, `1 ≤ |y| ≤ K`, at a point `x₀`
with `K^{1+c} ≤ |x₀|`, uniformly in `a ∈ [0, 1]`:
`|(Θ(x₀ + y) + Θ(x₀ - y))/2 - Θ(x₀)| ≤ (|y|/|x₀|)² (C₀ W^{-2} (|x₀| + W)^{-(d-2)}
(1 + |x₀| (1 - a)^{1/2}/W)^{-M} + |x₀|^{-D})`. -/
private theorem cancel_single (d : ℕ) (hd : 3 ≤ d) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (cψ : ℝ) (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) (c D : ℝ) (hc : 0 < c) (hD : 0 < D)
    (M : ℕ) :
    ∃ C₀ W₀ : ℝ, 0 ≤ C₀ ∧ 1 ≤ W₀ ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel ψ C W s → ∀ (a : ℝ), 0 ≤ a → a ≤ 1 → IntegrableOn (thetaSym a s) (cubePi d) ∧
        ∀ (K : ℕ), W ≤ K → ∀ (y x₀ : Fin d → ℤ), 1 ≤ zdInf y → zdInf y ≤ K →
          (K : ℝ) ^ (1 + c) ≤ zdInf x₀ →
          ‖latticeFourier (cancelSym a s y) x₀‖ ≤
            ((zdInf y : ℝ) / zdInf x₀) ^ 2 *
              (C₀ / ((W : ℝ) ^ 2 * ((zdInf x₀ : ℝ) + W) ^ (d - 2)) /
                  (1 + (zdInf x₀ : ℝ) * Real.sqrt (1 - a) / W) ^ M +
                (zdInf x₀ : ℝ) ^ (-D)) := by
  obtain ⟨Ci, Wi, hint⟩ := ThetaZd_decay d hd ψ cψ hψ C 0
  obtain ⟨C₁, W₁, hC₁0, hsc⟩ := shell_cancel_bound d ψ cψ hψ C (M + (d + 1))
  obtain ⟨C₂, W₂, hC₂0, hcc⟩ := core_cancel_bound d ψ cψ hψ C (M + (d + 1))
  set N : ℕ := ⌈(4 + D) * (1 + c) / c⌉₊ with hNdef
  have hN : (4 + D) * (1 + c) / c ≤ N := Nat.le_ceil _
  obtain ⟨Ch1, Wh1, hsh⟩ := shellKernel_bound d ψ cψ hψ C N
  obtain ⟨Ch2, Wh2, hch⟩ := coreKernel_bound d ψ cψ hψ C N
  obtain ⟨CS, hCS⟩ := sum_shell_le (d + 2) (d + 1) (by omega) (by omega)
  have hCS' : ∀ (J : ℕ) (t : ℝ), 0 ≤ t →
      ∑ j ∈ Finset.range J, (((2 : ℝ) ^ j) ^ d)⁻¹ * ((1 + t / 2 ^ j) ^ (d + 1))⁻¹ ≤
        CS * ((1 + t) ^ d)⁻¹ := by
    intro J t ht
    have := hCS J t ht
    simpa using this
  set A : ℝ := |Ch1| + |Ch2| with hA
  have hA0 : 0 ≤ A := by positivity
  set C₀ : ℝ := 3 ^ M * (C₁ * |CS| + C₂) with hC₀
  set W₀ : ℝ := max (max (max Wi W₁) (max W₂ Wh1))
    (max (max Wh2 1) (max ((2 : ℝ) ^ (1 / c)) (6 * A * 2 ^ N))) with hW₀
  refine ⟨C₀, W₀, by positivity, by simp [hW₀], ?_⟩
  intro W hW s hs a ha0 ha1
  have hWi : Wi ≤ (W : ℝ) := le_trans (by simp [hW₀]) hW
  have hW1' : W₁ ≤ (W : ℝ) := le_trans (by simp [hW₀]) hW
  have hW2' : W₂ ≤ (W : ℝ) := le_trans (by simp [hW₀]) hW
  have hWh1 : Wh1 ≤ (W : ℝ) := le_trans (by simp [hW₀]) hW
  have hWh2 : Wh2 ≤ (W : ℝ) := le_trans (by simp [hW₀]) hW
  have hW1 : (1 : ℝ) ≤ W := le_trans (by simp [hW₀]) hW
  have hW2c : (2 : ℝ) ^ (1 / c) ≤ W := le_trans (by simp [hW₀]) hW
  have hWA : 6 * A * 2 ^ N ≤ (W : ℝ) := le_trans (by simp [hW₀]) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hFi : IntegrableOn (thetaSym a s) (cubePi d) := (hint W hWi s hs a ha0 ha1).1
  refine ⟨hFi, ?_⟩
  intro K hK y x₀ hy1 hyK hKX
  set X : ℝ := (zdInf x₀ : ℝ) with hXdef
  set Y : ℝ := (zdInf y : ℝ) with hYdef
  have hWK : (W : ℝ) ≤ K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := hW1.trans hWK
  have hKc : (K : ℝ) ≤ (K : ℝ) ^ (1 + c) := by
    calc (K : ℝ) = (K : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (K : ℝ) ^ (1 + c) := Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  have hKX' : (K : ℝ) ≤ X := hKc.trans hKX
  have hX1 : 1 ≤ X := hK1.trans hKX'
  have hX0 : 0 < X := by linarith
  have hY1 : (1 : ℝ) ≤ Y := by rw [hYdef]; exact_mod_cast hy1
  have hYK : Y ≤ K := by rw [hYdef]; exact_mod_cast hyK
  have h2K : 2 * (K : ℝ) ≤ X := by
    have hKc2 : (2 : ℝ) ≤ (K : ℝ) ^ c := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / c)) ^ c := by
            rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
        _ ≤ (K : ℝ) ^ c := Real.rpow_le_rpow (by positivity) (hW2c.trans hWK) hc.le
    calc 2 * (K : ℝ) ≤ (K : ℝ) ^ c * K := by nlinarith
      _ = (K : ℝ) ^ (1 + c) := by
          rw [Real.rpow_add (by positivity), Real.rpow_one]; ring
      _ ≤ X := hKX
  have h2Y : 2 * Y ≤ X := by linarith
  have hKroot : (K : ℝ) ≤ X ^ (1 / (1 + c)) := by
    calc (K : ℝ) = ((K : ℝ) ^ (1 + c)) ^ (1 / (1 + c)) := by
          rw [← Real.rpow_mul (by positivity), mul_one_div_cancel (by linarith), Real.rpow_one]
      _ ≤ X ^ (1 / (1 + c)) := Real.rpow_le_rpow (by positivity) hKX (by positivity)
  have hAX : 6 * A * 2 ^ N ≤ X := hWA.trans (hWK.trans hKX')
  set Q : ℝ := 2 * A * (2 * K / X) ^ N with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hcrude : 3 * K * Q ≤ (Y / X) ^ 2 * X ^ (-D) :=
    crude_total_le hA0 hc hD hN hK1 hX1 hY1 hKroot hAX
  set t : ℝ := X / W with ht
  have ht0 : 0 ≤ t := by positivity
  have hu : ∀ j : ℕ, X / (2 ^ j * W) = t / 2 ^ j := fun j => by rw [ht]; field_simp
  -- the symbol of the second difference and the pieces
  have hFyi : IntegrableOn (cancelSym a s y) (cubePi d) := by
    refine Integrable.bdd_mul (c := 2) hFi
      (Complex.continuous_ofReal.comp (contDiff_cosM y).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_cosM_le_two y p
  have hpiece : ∀ χ : (Fin d → ℝ) → ℝ, Continuous χ → (∀ p, |χ p| ≤ 1) →
      latticeFourier (fun p => (χ p : ℂ) * cancelSym a s y p) x₀ =
        (latticeFourier (fun p => (χ p : ℂ) * thetaSym a s p) (x₀ + y) +
          latticeFourier (fun p => (χ p : ℂ) * thetaSym a s p) (x₀ - y)) / 2 -
          latticeFourier (fun p => (χ p : ℂ) * thetaSym a s p) x₀ := by
    intro χ hχ hb
    rw [← latticeFourier_cosM_mul (integrableOn_cut_mul hFi hχ hb) y x₀]
    congr 1
    funext p
    simp only [cancelSym]
    ring
  -- crude pieces
  have hhigh : ‖latticeFourier (fun p => (highCut W p : ℂ) * cancelSym a s y p) x₀‖ ≤ Q := by
    rw [hpiece _ (contDiff_highCut W).continuous
      fun p => (abs_cut_le_one (W := W) (j := 0) (J := 0) p).1]
    have hk : ∀ x, ‖latticeFourier (fun p => (highCut W p : ℂ) * thetaSym a s p) x‖ *
        (1 + (zdInf x : ℝ) / W) ^ N ≤ A := by
      intro x
      refine ((hch W hWh2 s hs a ha0 ha1 x).2).trans ?_
      calc Ch2 / (W : ℝ) ^ d ≤ |Ch2| / (W : ℝ) ^ d :=
            div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |Ch2| := div_le_self (abs_nonneg _) (one_le_pow₀ hW1)
        _ ≤ A := by rw [hA]; linarith [abs_nonneg Ch1]
    refine (crude_second_diff hW0 hk x₀ y hX0 h2Y).trans ?_
    rw [hQ]
    gcongr
  have hshell_crude : ∀ j : ℕ, ¬ Y ≤ 2 ^ j * W →
      ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖ ≤ Q := by
    intro j hj
    push Not at hj
    rw [hpiece _ (contDiff_shellCut W j).continuous
      fun p => (abs_cut_le_one (W := W) (j := j) (J := 0) p).2.1]
    have hk : ∀ x, ‖latticeFourier (fun p => (shellCut W j p : ℂ) * thetaSym a s p) x‖ *
        (1 + (zdInf x : ℝ) / (2 ^ j * W)) ^ N ≤ A := by
      intro x
      have h := hsh W hWh1 s hs a ha0 ha1 j x
      refine h.trans ?_
      have h4 : (4 : ℝ) ^ j ≤ (2 ^ j * (W : ℝ)) ^ d := by
        calc (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          _ ≤ ((2 : ℝ) ^ j) ^ d := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
          _ ≤ (2 ^ j * (W : ℝ)) ^ d := pow_le_pow_left₀ (by positivity)
              (le_mul_of_one_le_right (by positivity) hW1) d
      calc Ch1 * 4 ^ j / (2 ^ j * (W : ℝ)) ^ d ≤ |Ch1| * 4 ^ j / (2 ^ j * (W : ℝ)) ^ d := by
            gcongr; exact le_abs_self _
        _ ≤ |Ch1| := by
            rw [mul_div_assoc]
            exact mul_le_of_le_one_right (abs_nonneg _) ((div_le_one (by positivity)).2 h4)
        _ ≤ A := by rw [hA]; linarith [abs_nonneg Ch2]
    refine (crude_second_diff (by positivity) hk x₀ y hX0 h2Y).trans ?_
    rw [hQ]
    gcongr
    linarith
  -- the cancelling shells
  have hshell_canc : ∀ j : ℕ, Y ≤ 2 ^ j * W → ∀ w : ℝ, 0 ≤ w →
      w ≤ 3 ^ M * (1 + t / 2 ^ j) ^ M →
      ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖ * w ≤
        3 ^ M * C₁ * Y ^ 2 / (W : ℝ) ^ (d + 2) *
          ((((2 : ℝ) ^ j) ^ d)⁻¹ * ((1 + t / 2 ^ j) ^ (d + 1))⁻¹) := by
    intro j hj w hw0 hw
    have h := hsc W hW1' s hs a ha0 ha1 j y hy1 hj x₀
    rw [hu j] at h
    have hY0 : (0 : ℝ) < Y := by linarith
    have hL0 : (0 : ℝ) < 2 ^ j * W := by positivity
    have hab := absorb_weight (X := ‖latticeFourier (fun p => (shellCut W j p : ℂ) *
        cancelSym a s y p) x₀‖ * ((2 ^ j * W) / Y) ^ 2) (by positivity) (by positivity)
      (by positivity) h hw
    have hq : (0 : ℝ) < ((2 ^ j * W) / Y) ^ 2 := by positivity
    have e : ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖ * w =
        (‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖ *
          ((2 ^ j * W) / Y) ^ 2 * w) / ((2 ^ j * W) / Y) ^ 2 := by
      field_simp
    rw [e, div_le_iff₀ hq]
    refine hab.trans (le_of_eq ?_)
    have h4 : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    field_simp
    ring
  have hshells_canc : ∀ (J : ℕ) (w : ℝ), 0 ≤ w → (∀ j < J, w ≤ 3 ^ M * (1 + t / 2 ^ j) ^ M) →
      (∑ j ∈ (Finset.range J).filter (fun j => Y ≤ 2 ^ j * W),
        ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖) * w ≤
        3 ^ M * C₁ * |CS| * Y ^ 2 / (W : ℝ) ^ (d + 2) * ((1 + t) ^ d)⁻¹ := by
    intro J w hw0 hw
    rw [Finset.sum_mul]
    calc ∑ j ∈ (Finset.range J).filter (fun j => Y ≤ 2 ^ j * W),
          ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖ * w
        ≤ ∑ j ∈ (Finset.range J).filter (fun j => Y ≤ 2 ^ j * W),
          3 ^ M * C₁ * Y ^ 2 / (W : ℝ) ^ (d + 2) *
            ((((2 : ℝ) ^ j) ^ d)⁻¹ * ((1 + t / 2 ^ j) ^ (d + 1))⁻¹) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨hjJ, hjY⟩ := Finset.mem_filter.1 hj
          exact hshell_canc j hjY w hw0 (hw j (Finset.mem_range.1 hjJ))
      _ ≤ ∑ j ∈ Finset.range J, 3 ^ M * C₁ * Y ^ 2 / (W : ℝ) ^ (d + 2) *
            ((((2 : ℝ) ^ j) ^ d)⁻¹ * ((1 + t / 2 ^ j) ^ (d + 1))⁻¹) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => by positivity
      _ = 3 ^ M * C₁ * Y ^ 2 / (W : ℝ) ^ (d + 2) *
            ∑ j ∈ Finset.range J, (((2 : ℝ) ^ j) ^ d)⁻¹ * ((1 + t / 2 ^ j) ^ (d + 1))⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ 3 ^ M * C₁ * Y ^ 2 / (W : ℝ) ^ (d + 2) * (|CS| * ((1 + t) ^ d)⁻¹) := by
          gcongr
          exact (hCS' J t ht0).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      _ = 3 ^ M * C₁ * |CS| * Y ^ 2 / (W : ℝ) ^ (d + 2) * ((1 + t) ^ d)⁻¹ := by ring
  have hshells_crude : ∀ J : ℕ,
      ∑ j ∈ (Finset.range J).filter (fun j => ¬ Y ≤ 2 ^ j * W),
        ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖ ≤ K * Q := by
    intro J
    have hsub : (Finset.range J).filter (fun j => ¬ Y ≤ 2 ^ j * W) ⊆
        Finset.range (zdInf y) := by
      intro j hj
      have hj' := (Finset.mem_filter.1 hj).2
      push Not at hj'
      have h1 : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
      have h2 : (2 : ℝ) ^ j ≤ 2 ^ j * W := le_mul_of_one_le_right (by positivity) hW1
      have : (j : ℝ) < zdInf y := by rw [← hYdef]; linarith
      exact Finset.mem_range.2 (by exact_mod_cast this)
    have hcard : (((Finset.range J).filter (fun j => ¬ Y ≤ 2 ^ j * W)).card : ℝ) ≤ K := by
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      have : (((Finset.range J).filter (fun j => ¬ Y ≤ 2 ^ j * W)).card : ℝ) ≤ zdInf y := by
        exact_mod_cast this
      linarith
    calc ∑ j ∈ (Finset.range J).filter (fun j => ¬ Y ≤ 2 ^ j * W),
          ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖
        ≤ ((Finset.range J).filter (fun j => ¬ Y ≤ 2 ^ j * W)).card • Q :=
          Finset.sum_le_card_nsmul _ _ _ fun j hj => hshell_crude j (Finset.mem_filter.1 hj).2
      _ ≤ K * Q := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard hQ0
  -- the decomposition
  have hdecomp : ∀ J : ℕ, ‖latticeFourier (cancelSym a s y) x₀‖ ≤
      ‖latticeFourier (fun p => (highCut W p : ℂ) * cancelSym a s y p) x₀‖ +
      (∑ j ∈ (Finset.range J).filter (fun j => Y ≤ 2 ^ j * W),
        ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖) +
      (∑ j ∈ (Finset.range J).filter (fun j => ¬ Y ≤ 2 ^ j * W),
        ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖) +
      ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym a s y p) x₀‖ := by
    intro J
    rw [latticeFourier_decomp hFyi W J x₀]
    have hs := Finset.sum_filter_add_sum_filter_not (Finset.range J) (fun j => Y ≤ 2 ^ j * W)
      (fun j => ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖)
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add_left (norm_add_le _ _) _).trans ?_
    have := norm_sum_le (Finset.range J)
      (fun j => latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀)
    rw [← hs] at this
    linarith
  have hmainconv := main_conv_le (C₀ := C₀) (Y := Y) (d := d) (by omega) (by positivity) hX0 hW0
  rw [← ht] at hmainconv
  set Main : ℝ := (Y / X) ^ 2 * (C₀ / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2))) with hMain
  have hMain0 : 0 ≤ Main := by positivity
  have hQK : Q ≤ K * Q := le_mul_of_one_le_left hQ0 hK1
  have hC₁C₀ : 3 ^ M * C₁ * |CS| ≤ C₀ := by
    have h3 : (0 : ℝ) ≤ 3 ^ M * C₂ := mul_nonneg (by positivity) hC₂0
    have e : C₀ = 3 ^ M * C₁ * |CS| + 3 ^ M * C₂ := by rw [hC₀]; ring
    linarith
  rcases lt_or_eq_of_le ha1 with ha | ha
  · -- `a < 1`: shells `j < J` and the core at `J = shellCount a`
    set J := shellCount a with hJ
    set w : ℝ := (1 + X * Real.sqrt (1 - a) / W) ^ M with hw
    have hw1 : 1 ≤ w := one_le_pow₀ (by
      have : 0 ≤ X * Real.sqrt (1 - a) / W := by positivity
      linarith)
    have hw0 : 0 < w := by linarith
    have hwj : ∀ j ≤ J, w ≤ 3 ^ M * (1 + t / 2 ^ j) ^ M := fun j hj => by
      have := weight_le_shell ha0 ha hj X W hX0.le hW0 M
      rwa [hu j] at this
    have hsum := hshells_canc J w hw0.le fun j hj => hwj j hj.le
    have hcr := hshells_crude J
    have hfinal : ‖latticeFourier (cancelSym a s y) x₀‖ ≤ Main / w + 3 * K * Q := by
      refine (hdecomp J).trans ?_
      by_cases hcase : Y ≤ 2 ^ J * W
      · have h := hcc W hW2' s hs a ha0 ha y hy1 hcase x₀
        rw [← hJ, hu J] at h
        have hY0 : (0 : ℝ) < Y := by linarith
        have hab := absorb_weight (X := ‖latticeFourier (fun p => (coreCut W J p : ℂ) *
            cancelSym a s y p) x₀‖ * ((2 ^ J * W) / Y) ^ 2) (by positivity) (by positivity)
          (by positivity) h (hwj J le_rfl)
        have hq : (0 : ℝ) < ((2 ^ J * W) / Y) ^ 2 := by positivity
        have hcore : ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym a s y p) x₀‖ *
            w ≤ 3 ^ M * C₂ * Y ^ 2 / (W : ℝ) ^ (d + 2) * ((1 + t) ^ d)⁻¹ := by
          have e : ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym a s y p) x₀‖ * w =
              (‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym a s y p) x₀‖ *
                ((2 ^ J * W) / Y) ^ 2 * w) / ((2 ^ J * W) / Y) ^ 2 := by
            field_simp
          rw [e, div_le_iff₀ hq]
          refine hab.trans ?_
          have hkey : (((2 : ℝ) ^ J) ^ d)⁻¹ * ((1 + t / 2 ^ J) ^ (d + 1))⁻¹ ≤ ((1 + t) ^ d)⁻¹ := by
            rw [← mul_inv]
            apply inv_anti₀ (by positivity)
            have h2J : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
            have hb : 1 ≤ 1 + t / 2 ^ J := le_add_of_nonneg_right (by positivity)
            calc (1 + t) ^ d ≤ ((2 : ℝ) ^ J * (1 + t / 2 ^ J)) ^ d := by
                  apply pow_le_pow_left₀ (by positivity)
                  rw [mul_add, mul_one, mul_div_cancel₀ _ (by positivity)]; linarith
              _ = ((2 : ℝ) ^ J) ^ d * (1 + t / 2 ^ J) ^ d := mul_pow _ _ _
              _ ≤ ((2 : ℝ) ^ J) ^ d * (1 + t / 2 ^ J) ^ (d + 1) :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by omega)) (by positivity)
          have h4 : (4 : ℝ) ^ J = ((2 : ℝ) ^ J) ^ 2 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          calc 3 ^ M * (C₂ * 4 ^ J / (2 ^ J * (W : ℝ)) ^ d) * ((1 + t / 2 ^ J) ^ (d + 1))⁻¹
              = 3 ^ M * C₂ * Y ^ 2 / (W : ℝ) ^ (d + 2) *
                  ((((2 : ℝ) ^ J) ^ d)⁻¹ * ((1 + t / 2 ^ J) ^ (d + 1))⁻¹) *
                  ((2 ^ J * W) / Y) ^ 2 := by
                rw [h4]; field_simp; ring
            _ ≤ 3 ^ M * C₂ * Y ^ 2 / (W : ℝ) ^ (d + 2) * ((1 + t) ^ d)⁻¹ *
                  ((2 ^ J * W) / Y) ^ 2 := by gcongr
        have hm : ((∑ j ∈ (Finset.range J).filter (fun j => Y ≤ 2 ^ j * W),
            ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖) +
            ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym a s y p) x₀‖) * w ≤
            C₀ * Y ^ 2 / (W : ℝ) ^ (d + 2) * ((1 + t) ^ d)⁻¹ := by
          rw [add_mul]
          refine (add_le_add hsum hcore).trans (le_of_eq ?_)
          rw [hC₀]; ring
        have hm' : (∑ j ∈ (Finset.range J).filter (fun j => Y ≤ 2 ^ j * W),
            ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖) +
            ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym a s y p) x₀‖ ≤
            Main / w := by
          rw [le_div_iff₀ hw0]; exact hm.trans hmainconv
        linarith
      · have hcore : ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym a s y p) x₀‖ ≤
            Q := by
          push Not at hcase
          rw [hpiece _ (contDiff_coreCut W J).continuous
            fun p => (abs_cut_le_one (W := W) (j := 0) (J := J) p).2.2]
          have hk : ∀ x, ‖latticeFourier (fun p => (coreCut W J p : ℂ) * thetaSym a s p) x‖ *
              (1 + (zdInf x : ℝ) / (2 ^ J * W)) ^ N ≤ A := by
            intro x
            have h := (hch W hWh2 s hs a ha0 ha1 x).1 ha
            rw [← hJ] at h
            refine h.trans ?_
            have h4 : (4 : ℝ) ^ J ≤ (2 ^ J * (W : ℝ)) ^ d := by
              calc (4 : ℝ) ^ J = ((2 : ℝ) ^ J) ^ 2 := by
                    rw [← pow_mul, mul_comm, pow_mul]; norm_num
                _ ≤ ((2 : ℝ) ^ J) ^ d := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
                _ ≤ (2 ^ J * (W : ℝ)) ^ d := pow_le_pow_left₀ (by positivity)
                    (le_mul_of_one_le_right (by positivity) hW1) d
            calc Ch2 * 4 ^ J / (2 ^ J * (W : ℝ)) ^ d ≤ |Ch2| * 4 ^ J / (2 ^ J * (W : ℝ)) ^ d := by
                  gcongr; exact le_abs_self _
              _ ≤ |Ch2| := by
                  rw [mul_div_assoc]
                  exact mul_le_of_le_one_right (abs_nonneg _) ((div_le_one (by positivity)).2 h4)
              _ ≤ A := by rw [hA]; linarith [abs_nonneg Ch1]
          refine (crude_second_diff (by positivity) hk x₀ y hX0 h2Y).trans ?_
          rw [hQ]
          gcongr
          linarith
        have hsum' : (∑ j ∈ (Finset.range J).filter (fun j => Y ≤ 2 ^ j * W),
            ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym a s y p) x₀‖) ≤
            Main / w := by
          rw [le_div_iff₀ hw0]
          refine hsum.trans (le_trans ?_ hmainconv)
          gcongr
        linarith
    refine hfinal.trans ?_
    have : Main / w + (Y / X) ^ 2 * X ^ (-D) = (Y / X) ^ 2 *
        (C₀ / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) / w + X ^ (-D)) := by
      rw [hMain]; ring
    rw [← this]
    linarith
  · -- `a = 1`: all shells, the core tends to `0`
    subst ha
    have hw1 : (1 + X * Real.sqrt (1 - 1) / W) ^ M = 1 := by simp
    rw [hw1, div_one]
    have hstep : ∀ J : ℕ, ‖latticeFourier (cancelSym 1 s y) x₀‖ ≤
        Main + 3 * K * Q +
          ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym 1 s y p) x₀‖ := by
      intro J
      have hsum := hshells_canc J 1 zero_le_one fun j _ => by
        have : (1 : ℝ) ≤ (1 + t / 2 ^ j) ^ M := one_le_pow₀ (by
          have : 0 ≤ t / 2 ^ j := by positivity
          linarith)
        exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) this
      rw [mul_one] at hsum
      have hsum' : (∑ j ∈ (Finset.range J).filter (fun j => Y ≤ 2 ^ j * W),
          ‖latticeFourier (fun p => (shellCut W j p : ℂ) * cancelSym 1 s y p) x₀‖) ≤ Main := by
        refine hsum.trans (le_trans ?_ hmainconv)
        gcongr
      have hcr := hshells_crude J
      linarith [hdecomp J]
    have hd1 : 1 ≤ d := by omega
    have hDC : Filter.Tendsto
        (fun J : ℕ => ∫ p in cubePi d, ‖(coreCut W J p : ℂ) * cancelSym 1 s y p‖)
        Filter.atTop (nhds 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (cubePi d))
        (F := fun (J : ℕ) p => ‖(coreCut W J p : ℂ) * cancelSym 1 s y p‖) (f := fun _ => (0 : ℝ))
        (fun p => ‖cancelSym 1 s y p‖)
        (fun J => (integrableOn_cut_mul hFyi (contDiff_coreCut (d := d) W J).continuous
          fun p => (abs_cut_le_one (W := W) (j := 0) (J := J) p).2.2).norm.aestronglyMeasurable)
        hFyi.norm
        (fun J => Filter.Eventually.of_forall fun p => by
          rw [norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (abs_cut_le_one (W := W) (j := 0) (J := J) p).2.2)
        (by
          filter_upwards [ae_restrict_of_ae (s := cubePi d) (ae_coord_ne_zero (d := d))]
            with p hp
          have hp0 : p ≠ 0 := by
            intro h0
            exact hp ⟨0, by omega⟩ (by rw [h0]; rfl)
          have h1 := tendsto_coreCut hWn hp0
          have h2 : Filter.Tendsto (fun J => ‖((coreCut W J p : ℝ) : ℂ) * cancelSym 1 s y p‖)
              Filter.atTop (nhds ‖((0 : ℝ) : ℂ) * cancelSym 1 s y p‖) :=
            ((Complex.continuous_ofReal.tendsto 0).comp h1 |>.mul_const _).norm
          simpa using h2)
      simpa using this
    have hcore0 : Filter.Tendsto
        (fun J : ℕ => ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym 1 s y p) x₀‖)
        Filter.atTop (nhds 0) := by
      have h2 := hDC.const_mul ((2 * Real.pi) ^ d)⁻¹
      rw [mul_zero] at h2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
        (fun J => norm_nonneg _) (fun J => norm_latticeFourier_le _ x₀)
    have hlim : Filter.Tendsto
        (fun J : ℕ => Main + 3 * K * Q +
          ‖latticeFourier (fun p => (coreCut W J p : ℂ) * cancelSym 1 s y p) x₀‖)
        Filter.atTop (nhds (Main + 3 * K * Q + 0)) := tendsto_const_nhds.add hcore0
    rw [add_zero] at hlim
    have hle : ‖latticeFourier (cancelSym 1 s y) x₀‖ ≤ Main + 3 * K * Q :=
      ge_of_tendsto' hlim hstep
    refine hle.trans ?_
    have : Main + (Y / X) ^ 2 * X ^ (-D) = (Y / X) ^ 2 *
        (C₀ / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) + X ^ (-D)) := by
      rw [hMain]; ring
    rw [← this]
    linarith

end SingleDirection

/-! ## The cancellation lemma on `ℤ^d` -/

section Cancel

private theorem zdInf_le_of_mem_boxZ {K : ℕ} {y : Fin d → ℤ} (hy : y ∈ boxZ d K) :
    zdInf y ≤ K := by
  refine Finset.sup_le fun i _ => ?_
  have h := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hy i)
  omega

private theorem eq_zero_of_zdInf_eq_zero {y : Fin d → ℤ} (hy : zdInf y = 0) : y = 0 := by
  funext i
  have h : (y i).natAbs ≤ zdInf y := Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ i)
  rw [hy] at h
  simpa using h

private theorem neg_mem_boxZ {K : ℕ} {y : Fin d → ℤ} (hy : y ∈ boxZ d K) : -y ∈ boxZ d K := by
  refine Fintype.mem_piFinset.2 fun i => ?_
  have h := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hy i)
  simp only [Pi.neg_apply, Finset.mem_Icc]
  omega

/-- For `g` symmetric with box sum zero, `Σ_y Θ(x₀ + y) g(y) = Σ_y g(y) Δ_y Θ(x₀)`, with the
second difference `Δ_y Θ(x₀) = (Θ(x₀ + y) + Θ(x₀ - y))/2 - Θ(x₀)`. -/
private theorem sum_eq_sum_second_diff (Θ : (Fin d → ℤ) → ℂ) (K : ℕ) (g : (Fin d → ℤ) → ℝ)
    (hg : ∀ y, g (-y) = g y) (hg0 : ∑ y ∈ boxZ d K, g y = 0) (x₀ : Fin d → ℤ) :
    ∑ y ∈ boxZ d K, Θ (x₀ + y) * g y =
      ∑ y ∈ boxZ d K, (g y : ℂ) * ((Θ (x₀ + y) + Θ (x₀ - y)) / 2 - Θ x₀) := by
  have hneg : ∑ y ∈ boxZ d K, Θ (x₀ - y) * g y = ∑ y ∈ boxZ d K, Θ (x₀ + y) * g y := by
    refine Finset.sum_nbij' (fun y => -y) (fun y => -y) (fun y hy => neg_mem_boxZ hy)
      (fun y hy => neg_mem_boxZ hy) (fun y _ => neg_neg y) (fun y _ => neg_neg y) fun y _ => ?_
    simp only [hg, sub_eq_add_neg]
  have hz : ∑ y ∈ boxZ d K, (g y : ℂ) = 0 := by exact_mod_cast hg0
  have he : ∑ y ∈ boxZ d K, (g y : ℂ) * ((Θ (x₀ + y) + Θ (x₀ - y)) / 2 - Θ x₀) =
      (∑ y ∈ boxZ d K, Θ (x₀ + y) * g y) / 2 + (∑ y ∈ boxZ d K, Θ (x₀ - y) * g y) / 2 -
        Θ x₀ * ∑ y ∈ boxZ d K, (g y : ℂ) := by
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [he, hneg, hz]
  ring

/-- The cancellation lemma on `ℤ^d`, uniformly in `a ∈ [0, 1]` (the `ℤ^d` part of
[I, Lemma 6.1]; at `a = 1` it gives [I, Lemma 7.3]): for `g` symmetric with
`Σ_{|y| ≤ K} g(y) = 0`,
`K ≥ W` and `|x₀| ≥ K^{1+c}`,
`|Σ_{|y| ≤ K} Θ_{ℤ^d}(a)(x₀ + y) g(y)| ≤ Σ_y (|y|/|x₀|)² |g(y)| ·
(C₀ W^{-2} (|x₀| + W)^{-(d-2)} (1 + |x₀| (1 - a)^{1/2}/W)^{-M} + |x₀|^{-D})`,
with `|·|` the `ℓ^∞` norm. -/
theorem ThetaZd_cancel :
  ∀ (d : ℕ) (hd : 3 ≤ d) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) (c D : ℝ) (hc : 0 < c) (hD : 0 < D) (M : ℕ),
    ∃ C₀ W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ (a : ℝ), 0 ≤ a → a ≤ 1 → ∀ (K : ℕ), W ≤ K → ∀ g : (Fin d → ℤ) → ℝ,
        (∀ y, g (-y) = g y) → ∑ y ∈ boxZ d K, g y = 0 →
        ∀ x₀ : Fin d → ℤ, (K : ℝ) ^ (1 + c) ≤ zdInf x₀ →
          ‖∑ y ∈ boxZ d K, ThetaZd a s (x₀ + y) * g y‖ ≤
            (∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x₀) ^ 2 * |g y|) *
              (C₀ / ((W : ℝ) ^ 2 * ((zdInf x₀ : ℝ) + W) ^ (d - 2)) /
                  (1 + (zdInf x₀ : ℝ) * Real.sqrt (1 - a) / W) ^ M +
                (zdInf x₀ : ℝ) ^ (-D)) := by
  intro d hd ψ cψ hψ C c D hc hD M
  obtain ⟨C₀, W₀, hC₀0, hW₀1, h⟩ := cancel_single d hd ψ cψ hψ C c D hc hD M
  refine ⟨C₀, W₀, ?_⟩
  intro W hW s hs a ha0 ha1 K hK g hg hg0 x₀ hKX
  obtain ⟨hFi, hb⟩ := h W hW s hs a ha0 ha1
  set X : ℝ := (zdInf x₀ : ℝ) with hXdef
  set Br : ℝ := C₀ / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) /
      (1 + X * Real.sqrt (1 - a) / W) ^ M + X ^ (-D) with hBr
  have hW1 : (1 : ℝ) ≤ W := hW₀1.trans hW
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hBr0 : 0 ≤ Br := by positivity
  have hΔ : ∀ y : Fin d → ℤ, latticeFourier (cancelSym a s y) x₀ =
      (ThetaZd a s (x₀ + y) + ThetaZd a s (x₀ - y)) / 2 - ThetaZd a s x₀ :=
    fun y => latticeFourier_cosM_mul hFi y x₀
  rw [sum_eq_sum_second_diff (ThetaZd a s) K g hg hg0 x₀]
  simp_rw [← hΔ]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun y hy => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hy0 : zdInf y = 0
  · have hy' : y = 0 := eq_zero_of_zdInf_eq_zero hy0
    have : latticeFourier (cancelSym a s y) x₀ = 0 := by
      rw [hΔ, hy', add_zero, sub_zero]; ring
    rw [this, norm_zero, mul_zero]
    positivity
  · have hy1 : 1 ≤ zdInf y := Nat.one_le_iff_ne_zero.2 hy0
    have := hb K hK y x₀ hy1 (zdInf_le_of_mem_boxZ hy) hKX
    calc |g y| * ‖latticeFourier (cancelSym a s y) x₀‖ ≤ |g y| * (((zdInf y : ℝ) / X) ^ 2 * Br) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = ((zdInf y : ℝ) / X) ^ 2 * |g y| * Br := by ring

/-- [I, Lemma 7.3]: for `g` symmetric with `Σ_{|y| ≤ K} g(y) = 0`, `K ≥ W`, `|x₀| ≥ K^{1+c}`
and `W ≥ W₀`,
`|Σ_{|y| ≤ K} (Θ_∞)_{0,x₀+y} g(y)| ≤ Σ_y (|y|/|x₀|)² |g(y)| · W^{-2} |x₀|^{-(d-2-τ)}`,
with `|·|` the `ℓ^∞` norm. -/
theorem ThetaInf_cancel :
  ∀ (d : ℕ) (hd : 3 ≤ d) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ),
    ∃ W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ (K : ℕ), W ≤ K → ∀ g : (Fin d → ℤ) → ℝ,
        (∀ y, g (-y) = g y) → ∑ y ∈ boxZ d K, g y = 0 →
        ∀ x₀ : Fin d → ℤ, (K : ℝ) ^ (1 + c) ≤ zdInf x₀ →
          ‖∑ y ∈ boxZ d K, ThetaInf s (x₀ + y) * g y‖ ≤
            (∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x₀) ^ 2 * |g y|) *
              (1 / ((W : ℝ) ^ 2 * (zdInf x₀ : ℝ) ^ ((d : ℝ) - 2 - τ))) := by
  intro d hd ψ cψ hψ C c τ hc hτ
  obtain ⟨C₀, W₀, h⟩ := ThetaZd_cancel d hd ψ cψ hψ C c d hc (by positivity) 0
  refine ⟨max (max W₀ 1) (max ((2 * |C₀|) ^ (1 / τ)) ((2 : ℝ) ^ (1 / τ))), ?_⟩
  intro W hW s hs K hK g hg hg0 x₀ hKX
  have hW₀ : W₀ ≤ (W : ℝ) := le_trans (by simp) hW
  have hW1 : (1 : ℝ) ≤ W := le_trans (by simp) hW
  have hWC : (2 * |C₀|) ^ (1 / τ) ≤ (W : ℝ) := le_trans (by simp) hW
  have hW2 : (2 : ℝ) ^ (1 / τ) ≤ (W : ℝ) := le_trans (by simp) hW
  have hb := h W hW₀ s hs 1 zero_le_one le_rfl K hK g hg hg0 x₀ hKX
  have hT : ∀ z, ThetaInf s z = ThetaZd 1 s z := fun z => rfl
  simp_rw [hT]
  refine hb.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun y _ => by positivity)
  set X : ℝ := (zdInf x₀ : ℝ) with hXdef
  have hWK : (W : ℝ) ≤ K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := hW1.trans hWK
  have hKc : (K : ℝ) ≤ (K : ℝ) ^ (1 + c) := by
    calc (K : ℝ) = (K : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (K : ℝ) ^ (1 + c) := Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  have hWX : (W : ℝ) ≤ X := hWK.trans (hKc.trans hKX)
  have hX0 : 0 < X := by linarith
  set P : ℝ := X ^ τ with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hX0 τ
  have hτW : ∀ B : ℝ, 0 ≤ B → B ^ (1 / τ) ≤ (W : ℝ) → B ≤ P := by
    intro B hB hBW
    calc B = (B ^ (1 / τ)) ^ τ := by
          rw [← Real.rpow_mul hB, one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ τ := Real.rpow_le_rpow (by positivity) hBW hτ.le
      _ ≤ P := Real.rpow_le_rpow (by positivity) hWX hτ.le
  have hPC : 2 * |C₀| ≤ P := hτW _ (by positivity) hWC
  have hP2 : 2 ≤ P := hτW _ (by norm_num) hW2
  set E : ℝ := X ^ ((d : ℝ) - 2 - τ) with hE
  have hE0 : 0 < E := Real.rpow_pos_of_pos hX0 _
  have hd2 : X ^ (d - 2) = E * P := by
    rw [hE, hP, ← Real.rpow_add hX0, ← Real.rpow_natCast, Nat.cast_sub (by omega)]
    congr 1; push_cast; ring
  have hdd : X ^ (d : ℝ) = E * P * X ^ 2 := by
    rw [Real.rpow_natCast, show d = (d - 2) + 2 by omega, pow_add, hd2]
  rw [pow_zero, div_one, Real.rpow_neg hX0.le, hdd]
  have h1 : C₀ / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) ≤ (1 / 2) / ((W : ℝ) ^ 2 * E) := by
    have hXW : X ^ (d - 2) ≤ (X + W) ^ (d - 2) := pow_le_pow_left₀ hX0.le (by linarith) _
    calc C₀ / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) ≤ |C₀| / ((W : ℝ) ^ 2 * (E * P)) := by
          rw [← hd2]
          apply div_le_div₀ (abs_nonneg _) (le_abs_self _) (by positivity)
          exact mul_le_mul_of_nonneg_left hXW (by positivity)
      _ ≤ (1 / 2) / ((W : ℝ) ^ 2 * E) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 < (W : ℝ) ^ 2 * E := by positivity
          nlinarith
  have h2 : (E * P * X ^ 2)⁻¹ ≤ (1 / 2) / ((W : ℝ) ^ 2 * E) := by
    rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hWX2 : (W : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hWX 2
    have : 0 < E * X ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hWX2 hE0.le]
  have : (1 / 2) / ((W : ℝ) ^ 2 * E) + (1 / 2) / ((W : ℝ) ^ 2 * E) = 1 / ((W : ℝ) ^ 2 * E) := by
    ring
  linarith

end Cancel

/-! ## Lattice sums -/

section LatticeSums

/-- The `ℓ^∞` sphere of radius `n` in `ℤ^d` has at most `2d (2n + 1)^{d-1}` points. -/
private theorem card_sphere_le (hd : 1 ≤ d) (R n : ℕ) :
    ((((boxZ d R).filter fun z => zdInf z = n).card : ℕ) : ℝ) ≤
      2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) := by
  classical
  set T : Fin d → Fin d → Finset ℤ := fun i j =>
    if j = i then ({(n : ℤ), -(n : ℤ)} : Finset ℤ) else Finset.Icc (-(n : ℤ)) n with hT
  have hsub : ((boxZ d R).filter fun z => zdInf z = n) ⊆
      Finset.univ.biUnion fun i => Fintype.piFinset (T i) := by
    intro z hz
    have hzn := (Finset.mem_filter.1 hz).2
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
      Finset.univ_nonempty fun i => (z i).natAbs
    have hle : ∀ j, (z j).natAbs ≤ n := fun j => by
      rw [← hzn]; exact Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ j)
    have hin : (z i).natAbs = n := by rw [← hzn]; exact hi.symm
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Fintype.mem_piFinset.2 fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [hT, ite_true, Finset.mem_insert, Finset.mem_singleton]
      omega
    · simp only [hT, hj, ite_false, Finset.mem_Icc]
      have := hle j
      omega
  have hcard : ∀ i, ((Fintype.piFinset (T i)).card : ℝ) ≤ 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := by
    intro i
    rw [Fintype.card_piFinset, Nat.cast_prod]
    have hfac : ∀ j, (((T i j).card : ℕ) : ℝ) ≤ if j = i then 2 else 2 * (n : ℝ) + 1 := by
      intro j
      by_cases hj : j = i
      · simp only [hT, hj, ite_true]
        exact_mod_cast Finset.card_le_two
      · simp only [hT, hj, ite_false, Int.card_Icc]
        have : (n : ℤ) + 1 - -(n : ℤ) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this, Int.toNat_natCast]
        push_cast; rfl
    calc ∏ j, (((T i j).card : ℕ) : ℝ) ≤ ∏ j, (if j = i then (2 : ℝ) else 2 * (n : ℝ) + 1) :=
          Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => hfac j
      _ = 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := by
          rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
          have h1 : ∀ j ∈ Finset.univ \ {i},
              (if j = i then (2 : ℝ) else 2 * (n : ℝ) + 1) = 2 * (n : ℝ) + 1 := by
            intro j hj
            have : j ≠ i := by simpa using (Finset.mem_sdiff.1 hj).2
            simp [this]
          rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_univ_sdiff,
            Fintype.card_fin, Finset.card_singleton]
          simp
  calc ((((boxZ d R).filter fun z => zdInf z = n).card : ℕ) : ℝ)
      ≤ ((Finset.univ.biUnion fun i => Fintype.piFinset (T i)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i, ((Fintype.piFinset (T i)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := Finset.sum_le_sum fun i _ => hcard i
    _ = 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) := by simp; ring

/-- Sums over `ℤ^d` of functions of the `ℓ^∞` norm, by spheres. -/
private theorem summable_zdInf (hd : 1 ≤ d) {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {B : ℝ}
    (hB : ∀ R : ℕ, ∑ n ∈ Finset.range (R + 1), 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) * f n ≤ B) :
    Summable (fun z : Fin d → ℤ => f (zdInf z)) ∧ ∑' z : Fin d → ℤ, f (zdInf z) ≤ B := by
  classical
  have hu : ∀ u : Finset (Fin d → ℤ), ∑ z ∈ u, f (zdInf z) ≤ B := by
    intro u
    set R : ℕ := u.sup zdInf with hR
    have hsub : u ⊆ boxZ d R := by
      intro z hz
      refine Fintype.mem_piFinset.2 fun i => ?_
      have h1 : (z i).natAbs ≤ zdInf z :=
        Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ i)
      have h2 : zdInf z ≤ R := Finset.le_sup (f := zdInf) hz
      rw [Finset.mem_Icc]
      omega
    have hmaps : ∀ z ∈ boxZ d R, zdInf z ∈ Finset.range (R + 1) := fun z hz =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.sup_le fun i _ => by
        have h := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hz i)
        omega))
    calc ∑ z ∈ u, f (zdInf z) ≤ ∑ z ∈ boxZ d R, f (zdInf z) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hf _
      _ = ∑ n ∈ Finset.range (R + 1), ∑ z ∈ (boxZ d R).filter fun z => zdInf z = n,
            f (zdInf z) := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ n ∈ Finset.range (R + 1),
            (((boxZ d R).filter fun z => zdInf z = n).card : ℝ) * f n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.1 hz).2],
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.range (R + 1), 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) * f n :=
          Finset.sum_le_sum fun n _ =>
            mul_le_mul_of_nonneg_right (card_sphere_le hd R n) (hf n)
      _ ≤ B := hB R
  exact ⟨summable_of_sum_le (fun z => hf _) hu, Real.tsum_le_of_sum_le (fun z => hf _) hu⟩

/-- `Σ_{n < R} (n + r + 1)^{-2} ≤ r^{-1}` for `r > 0`. -/
private theorem sum_inv_sq_le {r : ℝ} (hr : 0 < r) (R : ℕ) :
    ∑ n ∈ Finset.range R, (((n : ℝ) + r + 1) ^ 2)⁻¹ ≤ r⁻¹ := by
  have hterm : ∀ n : ℕ, (((n : ℝ) + r + 1) ^ 2)⁻¹ ≤
      ((n : ℝ) + r)⁻¹ - (((n + 1 : ℕ) : ℝ) + r)⁻¹ := by
    intro n
    push_cast
    have h1 : 0 < (n : ℝ) + r := by positivity
    rw [inv_sub_inv h1.ne' (by positivity), ← one_div, div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  calc ∑ n ∈ Finset.range R, (((n : ℝ) + r + 1) ^ 2)⁻¹
      ≤ ∑ n ∈ Finset.range R, (((n : ℝ) + r)⁻¹ - (((n + 1 : ℕ) : ℝ) + r)⁻¹) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = ((0 : ℕ) + r)⁻¹ - (((R : ℕ) : ℝ) + r)⁻¹ :=
        Finset.sum_range_sub' (fun n : ℕ => ((n : ℝ) + r)⁻¹) R
    _ ≤ r⁻¹ := by
        have : 0 ≤ (((R : ℕ) : ℝ) + r)⁻¹ := by positivity
        simp only [Nat.cast_zero, zero_add]; linarith

end LatticeSums

section LatticeConv

/-- The lattice convolution of `(|z| + W)^{-(d-2)}` with itself, `d ≥ 5`:
`Σ_z (|z| + W)^{-(d-2)} (|x - z| + W)^{-(d-2)} ≤ C_d (|x| + W)^{-(d-4)}`, `C_d` depending only
on `d`. -/
private theorem conv_sum_le (hd : 5 ≤ d) {W : ℝ} (hW : 1 ≤ W) (x : Fin d → ℤ) :
    Summable (fun z : Fin d → ℤ => (((zdInf z : ℝ) + W) ^ (d - 2))⁻¹ *
      (((zdInf (x - z) : ℝ) + W) ^ (d - 2))⁻¹) ∧
    ∑' z : Fin d → ℤ, (((zdInf z : ℝ) + W) ^ (d - 2))⁻¹ *
        (((zdInf (x - z) : ℝ) + W) ^ (d - 2))⁻¹ ≤
      2 * (d * 2 ^ (2 * d - 2) * 2 ^ (d - 4)) * (((zdInf x : ℝ) + W) ^ (d - 4))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 5 := ⟨d - 5, by omega⟩
  have e2 : k + 5 - 2 = k + 3 := by omega
  have e4 : k + 5 - 4 = k + 1 := by omega
  have e1 : k + 5 - 1 = k + 4 := by omega
  have e22 : 2 * (k + 5) - 2 = 2 * k + 8 := by omega
  simp only [e2, e4]
  rw [e22]
  have hW0 : 0 < W := by linarith
  set R' : ℝ := ((zdInf x : ℝ) + W) / 2 with hR'
  have hR'0 : 0 < R' := by positivity
  set φ : ℕ → ℝ := fun n => (((n : ℝ) + W) ^ (k + 3))⁻¹ *
    ((((n : ℝ) + W + R') / 2) ^ (k + 3))⁻¹ with hφ
  have hφ0 : ∀ n, 0 ≤ φ n := fun n => by simp only [hφ]; positivity
  have hd1 : 1 ≤ k + 5 := by omega
  have hB : ∀ R : ℕ, ∑ n ∈ Finset.range (R + 1),
      2 * ((k + 5 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) ^ (k + 5 - 1) * φ n ≤
        ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (R' ^ (k + 1))⁻¹ := by
    intro R
    have hterm : ∀ n : ℕ, 2 * ((k + 5 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) ^ (k + 5 - 1) * φ n ≤
        ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (R' ^ k)⁻¹ *
          (((n : ℝ) + (W + R' - 1) + 1) ^ 2)⁻¹ := by
      intro n
      rw [e1]
      set m : ℝ := (n : ℝ) + W with hm
      have hm1 : 1 ≤ m := by rw [hm]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hm0 : 0 < m := by linarith
      have h21 : 2 * (n : ℝ) + 1 ≤ 2 * m := by rw [hm]; linarith
      have hpow : (2 * (n : ℝ) + 1) ^ (k + 4) ≤ (2 * m) ^ (k + 4) :=
        pow_le_pow_left₀ (by positivity) h21 _
      have he : (n : ℝ) + (W + R' - 1) + 1 = m + R' := by rw [hm]; ring
      rw [he]
      have hφn : φ n = 2 ^ (k + 3) * ((m ^ (k + 3))⁻¹ * ((m + R') ^ (k + 3))⁻¹) := by
        simp only [hφ, ← hm]
        rw [div_pow, inv_div]
        field_simp
      rw [hφn]
      have hmR : m ≤ m + R' := by linarith
      have hR'k : R' ^ k ≤ (m + R') ^ k := pow_le_pow_left₀ hR'0.le (by linarith) k
      calc 2 * ((k + 5 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) ^ (k + 4) *
            (2 ^ (k + 3) * ((m ^ (k + 3))⁻¹ * ((m + R') ^ (k + 3))⁻¹))
          ≤ 2 * ((k + 5 : ℕ) : ℝ) * (2 * m) ^ (k + 4) *
            (2 ^ (k + 3) * ((m ^ (k + 3))⁻¹ * ((m + R') ^ (k + 3))⁻¹)) := by gcongr
        _ = ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (m / (m + R') ^ (k + 3)) := by
            rw [mul_pow, pow_succ m (k + 3)]
            field_simp
            ring
        _ ≤ ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (((m + R') ^ k)⁻¹ * ((m + R') ^ 2)⁻¹) := by
            gcongr
            rw [div_le_iff₀ (by positivity)]
            have : (m + R') ^ (k + 3) = (m + R') ^ k * (m + R') ^ 2 * (m + R') := by ring
            rw [this]
            field_simp
            exact hmR
        _ ≤ ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * ((R' ^ k)⁻¹ * ((m + R') ^ 2)⁻¹) := by
            gcongr
        _ = _ := by ring
    have hr : 0 < W + R' - 1 := by linarith
    calc ∑ n ∈ Finset.range (R + 1),
          2 * ((k + 5 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) ^ (k + 5 - 1) * φ n
        ≤ ∑ n ∈ Finset.range (R + 1), ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (R' ^ k)⁻¹ *
            (((n : ℝ) + (W + R' - 1) + 1) ^ 2)⁻¹ := Finset.sum_le_sum fun n _ => hterm n
      _ = ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (R' ^ k)⁻¹ *
            ∑ n ∈ Finset.range (R + 1), (((n : ℝ) + (W + R' - 1) + 1) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (R' ^ k)⁻¹ * (W + R' - 1)⁻¹ := by
          gcongr
          exact sum_inv_sq_le hr (R + 1)
      _ ≤ ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (R' ^ k)⁻¹ * R'⁻¹ := by
          gcongr
          linarith
      _ = ((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (R' ^ (k + 1))⁻¹ := by
          rw [pow_succ R' k, mul_inv]; ring
  obtain ⟨hs1, ht1⟩ := summable_zdInf hd1 hφ0 hB
  have hs2 : Summable fun z : Fin (k + 5) → ℤ => φ (zdInf (x - z)) :=
    (Equiv.subLeft x).summable_iff.2 hs1
  have ht2 : ∑' z : Fin (k + 5) → ℤ, φ (zdInf (x - z)) = ∑' z : Fin (k + 5) → ℤ, φ (zdInf z) :=
    (Equiv.subLeft x).tsum_eq (fun z => φ (zdInf z))
  have hpt : ∀ z : Fin (k + 5) → ℤ, (((zdInf z : ℝ) + W) ^ (k + 3))⁻¹ *
      (((zdInf (x - z) : ℝ) + W) ^ (k + 3))⁻¹ ≤ φ (zdInf z) + φ (zdInf (x - z)) := by
    intro z
    set A : ℝ := (zdInf z : ℝ) + W with hA
    set B : ℝ := (zdInf (x - z) : ℝ) + W with hB'
    have hA0 : 0 < A := by positivity
    have hB0 : 0 < B := by positivity
    have hAB : 2 * R' ≤ A + B := by
      have h := zdInf_add_le z (x - z)
      rw [add_sub_cancel] at h
      have : (zdInf x : ℝ) ≤ zdInf z + zdInf (x - z) := by exact_mod_cast h
      rw [hR', hA, hB']; linarith
    have hφz : φ (zdInf z) = (A ^ (k + 3))⁻¹ * (((A + R') / 2) ^ (k + 3))⁻¹ := by
      simp only [hφ, hA]
    have hφxz : φ (zdInf (x - z)) = (B ^ (k + 3))⁻¹ * (((B + R') / 2) ^ (k + 3))⁻¹ := by
      simp only [hφ, hB']
    rw [hφz, hφxz]
    rcases le_total A B with h | h
    · have hBge : (A + R') / 2 ≤ B := by linarith
      have : (A ^ (k + 3))⁻¹ * (B ^ (k + 3))⁻¹ ≤
          (A ^ (k + 3))⁻¹ * (((A + R') / 2) ^ (k + 3))⁻¹ := by
        gcongr
      have h0 : 0 ≤ (B ^ (k + 3))⁻¹ * (((B + R') / 2) ^ (k + 3))⁻¹ := by positivity
      linarith
    · have hAge : (B + R') / 2 ≤ A := by linarith
      have : (A ^ (k + 3))⁻¹ * (B ^ (k + 3))⁻¹ ≤
          (B ^ (k + 3))⁻¹ * (((B + R') / 2) ^ (k + 3))⁻¹ := by
        rw [mul_comm]
        gcongr
      have h0 : 0 ≤ (A ^ (k + 3))⁻¹ * (((A + R') / 2) ^ (k + 3))⁻¹ := by positivity
      linarith
  have hsum : Summable fun z : Fin (k + 5) → ℤ => φ (zdInf z) + φ (zdInf (x - z)) := hs1.add hs2
  have hS : Summable fun z : Fin (k + 5) → ℤ => (((zdInf z : ℝ) + W) ^ (k + 3))⁻¹ *
      (((zdInf (x - z) : ℝ) + W) ^ (k + 3))⁻¹ :=
    Summable.of_nonneg_of_le (fun z => by positivity) hpt hsum
  refine ⟨hS, ?_⟩
  calc ∑' z : Fin (k + 5) → ℤ, (((zdInf z : ℝ) + W) ^ (k + 3))⁻¹ *
        (((zdInf (x - z) : ℝ) + W) ^ (k + 3))⁻¹
      ≤ ∑' z : Fin (k + 5) → ℤ, (φ (zdInf z) + φ (zdInf (x - z))) :=
        Summable.tsum_le_tsum hpt hS hsum
    _ = 2 * ∑' z : Fin (k + 5) → ℤ, φ (zdInf z) := by rw [hs1.tsum_add hs2, ht2]; ring
    _ ≤ 2 * (((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * (R' ^ (k + 1))⁻¹) := by gcongr
    _ = 2 * (((k + 5 : ℕ) : ℝ) * 2 ^ (2 * k + 8) * 2 ^ (k + 1)) *
          (((zdInf x : ℝ) + W) ^ (k + 1))⁻¹ := by
        rw [hR', div_pow]; field_simp

end LatticeConv

/-! ## Convolutions on `ℤ^d` -/

section Convolution

/-- Multiplying the symbol by the Fourier series of a summable kernel `K` convolves with `K`:
`(2π)^{-d} ∫ K̂ Φ e^{-ip·x} = Σ_y K(y) (2π)^{-d} ∫ Φ e^{-ip·(x-y)}`. -/
private theorem latticeFourier_zdSeries_mul {K : (Fin d → ℤ) → ℂ}
    (hsum : Summable fun y => ‖K y‖) {Φ : (Fin d → ℝ) → ℂ} (hΦ : IntegrableOn Φ (cubePi d))
    (x : Fin d → ℤ) :
    latticeFourier (fun p => zdSeries K p * Φ p) x = ∑' y, K y * latticeFourier Φ (x - y) := by
  unfold latticeFourier
  set F : (Fin d → ℤ) → (Fin d → ℝ) → ℂ := fun y p => K y * (Φ p * zexp p (-(x - y)))
  have hF : ∀ y, Integrable (F y) (volume.restrict (cubePi d)) := fun y =>
    (integrableOn_mul_zexp hΦ (x - y)).const_mul _
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
private theorem zdSeries_conv {K₁ K₂ : (Fin d → ℤ) → ℂ} (h₁ : Summable fun y => ‖K₁ y‖)
    (h₂ : Summable fun y => ‖K₂ y‖) (p : Fin d → ℝ) :
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
  have hval : ∀ q : (Fin d → ℤ) × (Fin d → ℤ), G (e q) = K₁ q.2 * K₂ (q.1 - q.2) * zexp p q.1 := by
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

end Convolution

/-! ## The Fourier series of `Θ_{ℤ^d}(a)` for `a < 1` -/

section ThetaSeries

private theorem latticeFourier_congr_ae {F G : (Fin d → ℝ) → ℂ}
    (h : ∀ᵐ p ∂(volume.restrict (cubePi d)), F p = G p) (x : Fin d → ℤ) :
    latticeFourier F x = latticeFourier G x := by
  unfold latticeFourier
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with p hp
  rw [hp]

/-- For `a < 1`, `Θ_{ℤ^d}(a)` is summable and its Fourier series is its symbol
`a ŝ/(1 - a ŝ)` on `[-π, π]^d`; this uses `Θ = a s + a s * Θ`. -/
private theorem theta_series (d : ℕ) (hd : 3 ≤ d) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (cψ : ℝ) (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) :
    ∃ W₀ : ℝ, 1 ≤ W₀ ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ (a : ℝ), 0 ≤ a → a < 1 →
        Summable (fun z => ‖ThetaZd a s z‖) ∧
        ∀ p ∈ cubePi d, zdSeries (ThetaZd a s) p = thetaSym a s p := by
  obtain ⟨C₁, W₁, h1⟩ := ThetaZd_decay d hd ψ cψ hψ C (d + 1)
  obtain ⟨c, W₂, hc, hW₂⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  obtain ⟨K₀, hK₀⟩ := zdSymbol_smooth d ψ C 0
  refine ⟨max (max W₁ W₂) 1, le_max_right _ _, ?_⟩
  intro W hW s hs a ha0 ha
  have hW1' : W₁ ≤ (W : ℝ) := le_trans (by simp) hW
  have hW2' : W₂ ≤ (W : ℝ) := le_trans (by simp) hW
  have hW1 : (1 : ℝ) ≤ W := le_trans (by simp) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hFi, hb⟩ := h1 W hW1' s hs a ha0 ha.le
  -- summability of `Θ_{ℤ^d}(a)`
  set κ : ℝ := Real.sqrt (1 - a) / W with hκ
  have hκ0 : 0 < κ := by
    have : 0 < Real.sqrt (1 - a) := Real.sqrt_pos.2 (by linarith)
    positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one hW0]
    exact (Real.sqrt_le_one.2 (by linarith)).trans hW1
  set f : ℕ → ℝ := fun n => |C₁| * ((1 + κ * n) ^ (d + 1))⁻¹ with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; positivity
  have hfz : ∀ z, ‖ThetaZd a s z‖ ≤ f (zdInf z) := by
    intro z
    have h := hb z
    have hw : (1 + (zdInf z : ℝ) * Real.sqrt (1 - a) / W) = 1 + κ * zdInf z := by
      rw [hκ]; ring
    rw [hw] at h
    have hden : 1 ≤ (W : ℝ) ^ 2 * ((zdInf z : ℝ) + W) ^ (d - 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) (one_le_pow₀ (by linarith [
        (Nat.cast_nonneg (zdInf z) : (0 : ℝ) ≤ zdInf z)]))
    have h2 : ‖ThetaZd a s z‖ * (1 + κ * zdInf z) ^ (d + 1) ≤ |C₁| :=
      h.trans ((div_le_self (abs_nonneg _) hden).trans' (div_le_div_of_nonneg_right
        (le_abs_self _) (by positivity)))
    simp only [hf]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h2
  have hB : ∀ R : ℕ, ∑ n ∈ Finset.range (R + 1), 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) * f n ≤
      2 * d * 2 ^ (d - 1) * |C₁| * (2 / κ) ^ (d + 1) := by
    intro R
    have hterm : ∀ n : ℕ, 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) * f n ≤
        2 * d * 2 ^ (d - 1) * |C₁| * (2 / κ) ^ (d + 1) * (((n : ℝ) + 1 + 1) ^ 2)⁻¹ := by
      intro n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1' : 2 * (n : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1 + 1) := by linarith
      have h2' : κ * ((n : ℝ) + 1 + 1) / 2 ≤ 1 + κ * n := by nlinarith
      have hp1 : (2 * (n : ℝ) + 1) ^ (d - 1) ≤ 2 ^ (d - 1) * ((n : ℝ) + 1 + 1) ^ (d - 1) := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1' _
      have hp2 : ((1 + κ * n) ^ (d + 1))⁻¹ ≤
          (2 / κ) ^ (d + 1) * (((n : ℝ) + 1 + 1) ^ (d + 1))⁻¹ := by
        rw [← inv_pow, ← inv_pow, ← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        rw [show 2 / κ * ((n : ℝ) + 1 + 1)⁻¹ = (κ * ((n : ℝ) + 1 + 1) / 2)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) h2'
      have e : ((n : ℝ) + 1 + 1) ^ (d - 1) * (((n : ℝ) + 1 + 1) ^ (d + 1))⁻¹ =
          (((n : ℝ) + 1 + 1) ^ 2)⁻¹ := by
        have : ((n : ℝ) + 1 + 1) ^ (d + 1) =
            ((n : ℝ) + 1 + 1) ^ (d - 1) * ((n : ℝ) + 1 + 1) ^ 2 := by
          rw [← pow_add]; congr 1; omega
        rw [this, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      calc 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) * f n
          ≤ 2 * d * (2 ^ (d - 1) * ((n : ℝ) + 1 + 1) ^ (d - 1)) *
              (|C₁| * ((2 / κ) ^ (d + 1) * (((n : ℝ) + 1 + 1) ^ (d + 1))⁻¹)) := by
            simp only [hf]; gcongr
        _ = 2 * d * 2 ^ (d - 1) * |C₁| * (2 / κ) ^ (d + 1) *
              (((n : ℝ) + 1 + 1) ^ (d - 1) * (((n : ℝ) + 1 + 1) ^ (d + 1))⁻¹) := by ring
        _ = _ := by rw [e]
    calc ∑ n ∈ Finset.range (R + 1), 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) * f n
        ≤ ∑ n ∈ Finset.range (R + 1), 2 * d * 2 ^ (d - 1) * |C₁| * (2 / κ) ^ (d + 1) *
            (((n : ℝ) + 1 + 1) ^ 2)⁻¹ := Finset.sum_le_sum fun n _ => hterm n
      _ = 2 * d * 2 ^ (d - 1) * |C₁| * (2 / κ) ^ (d + 1) *
            ∑ n ∈ Finset.range (R + 1), (((n : ℝ) + 1 + 1) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 * d * 2 ^ (d - 1) * |C₁| * (2 / κ) ^ (d + 1) * 1 := by
          gcongr
          have := sum_inv_sq_le (r := 1) one_pos (R + 1)
          rwa [inv_one] at this
      _ = _ := mul_one _
  obtain ⟨hfs, -⟩ := summable_zdInf hd1 hf0 hB
  have hΘs : Summable fun z => ‖ThetaZd a s z‖ :=
    Summable.of_nonneg_of_le (fun z => norm_nonneg _) hfz hfs
  refine ⟨hΘs, ?_⟩
  -- the identity `Θ = a s + a s * Θ`
  obtain ⟨hcd, -, hK0⟩ := hK₀ W hWn s hs
  have hsn : Summable fun y => ‖((s y : ℝ) : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using summable_abs_iff.2 hs.summable_s
  have hsym : ∀ p ∈ cubePi d, thetaSym a s p =
      (a : ℂ) * zdSymbol s p + (a : ℂ) * (zdSymbol s p * thetaSym a s p) := by
    intro p hp
    obtain ⟨him, hge⟩ := hW₂ W hW2' s hs p hp
    set σ := (zdSymbol s p).re with hσ
    have hse : zdSymbol s p = (σ : ℂ) := Complex.ext (by simp [hσ]) (by simp [him])
    have hσ1 : σ ≤ 1 := by
      have : 0 ≤ c * min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
        mul_nonneg hc.le (le_min (mul_nonneg (by positivity) (sqNorm_nonneg' p)) zero_le_one)
      linarith
    have hpos : 0 < 1 - a * σ := by
      have := one_sub_mul_ge_half ha0 ha.le hσ1; linarith
    have hne : (1 : ℂ) - (a : ℂ) * (σ : ℂ) ≠ 0 := by
      have : ((1 - a * σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      simpa using this
    simp only [thetaSym, hse]
    field_simp
    ring
  have hscont : IntegrableOn (zdSymbol s) (cubePi d) :=
    hcd.continuous.continuousOn.integrableOn_compact isCompact_cubePi''
  have hsF : IntegrableOn (fun p => zdSymbol s p * thetaSym a s p) (cubePi d) := by
    refine Integrable.bdd_mul (c := K₀) hFi hcd.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have := hK0 p
    rwa [norm_iteratedFDeriv_zero, pow_zero, mul_one] at this
  have hreal : ∀ x, ThetaZd a s x =
      (a : ℂ) * (s x : ℂ) + (a : ℂ) * ∑' y, (s y : ℂ) * ThetaZd a s (x - y) := by
    intro x
    have h1 : ThetaZd a s x = latticeFourier (fun p => (a : ℂ) * zdSymbol s p +
        (a : ℂ) * (zdSymbol s p * thetaSym a s p)) x := latticeFourier_congr hsym x
    rw [h1, latticeFourier_add (F := fun p => (a : ℂ) * zdSymbol s p)
      (G := fun p => (a : ℂ) * (zdSymbol s p * thetaSym a s p)) (hscont.const_mul _)
      (hsF.const_mul _), latticeFourier_const_mul,
      latticeFourier_const_mul (F := fun p => zdSymbol s p * thetaSym a s p)]
    have h2 : latticeFourier (zdSymbol s) x = (s x : ℂ) := latticeFourier_zdSeries _ hsn x
    have h3 : latticeFourier (fun p => zdSymbol s p * thetaSym a s p) x =
        ∑' y, (s y : ℂ) * ThetaZd a s (x - y) := latticeFourier_zdSeries_mul hsn hFi x
    rw [h2, h3]
  intro p hp
  have hden : (1 : ℂ) - (a : ℂ) * zdSymbol s p ≠ 0 := by
    obtain ⟨him, hge⟩ := hW₂ W hW2' s hs p hp
    set σ := (zdSymbol s p).re with hσ
    have hse : zdSymbol s p = (σ : ℂ) := Complex.ext (by simp [hσ]) (by simp [him])
    have hσ1 : σ ≤ 1 := by
      have : 0 ≤ c * min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
        mul_nonneg hc.le (le_min (mul_nonneg (by positivity) (sqNorm_nonneg' p)) zero_le_one)
      linarith
    have hpos : 0 < 1 - a * σ := by
      have := one_sub_mul_ge_half ha0 ha.le hσ1; linarith
    rw [hse]
    have : ((1 - a * σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    simpa using this
  have hsz : Summable fun x => ‖(s x : ℂ) * zexp p x‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using hsn
  have hΘz : Summable fun x => ‖ThetaZd a s x * zexp p x‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using hΘs
  have hsplit : ∀ x, ThetaZd a s x * zexp p x = (a : ℂ) * ((s x : ℂ) * zexp p x) +
      (a : ℂ) * ((∑' y, (s y : ℂ) * ThetaZd a s (x - y)) * zexp p x) := fun x => by
    rw [hreal x]; ring
  have hA : Summable fun x => (a : ℂ) * ((s x : ℂ) * zexp p x) := hsz.of_norm.mul_left _
  have hB : Summable fun x =>
      (a : ℂ) * ((∑' y, (s y : ℂ) * ThetaZd a s (x - y)) * zexp p x) :=
    (hΘz.of_norm.sub hA).congr fun x => by rw [hsplit x]; ring
  have hconv := zdSeries_conv hsn hΘs p
  have hkey : zdSeries (ThetaZd a s) p =
      (a : ℂ) * zdSymbol s p + (a : ℂ) * (zdSymbol s p * zdSeries (ThetaZd a s) p) := by
    calc zdSeries (ThetaZd a s) p = ∑' x, ThetaZd a s x * zexp p x := rfl
      _ = _ := by
        rw [tsum_congr hsplit, hA.tsum_add hB, tsum_mul_left, tsum_mul_left, hconv]
        rfl
  simp only [thetaSym]
  rw [eq_div_iff hden]
  linear_combination hkey

end ThetaSeries

/-! ## The difference `Θ_∞ - Θ_{ℤ^d}(a)` -/

section Difference

/-- The `ℤ^d` part of the difference bound [I, (7.9)] of [I, Lemma 7.2], `d ≥ 5`, uniformly in
`a ∈ [0, 1]`:
`|Θ_∞(x) - Θ_{ℤ^d}(a)(x)| ≤ C₀ (1 - a) W^{-4} (|x| + W)^{-(d-4)}`. It follows from
`Θ_∞ - Θ_{ℤ^d}(a) = (1 - a)(Θ_∞ + Θ_∞ * Θ_{ℤ^d}(a))` (the symbol identity
`ŝ/(1 - ŝ) - a ŝ/(1 - a ŝ) = (1 - a) ŝ/((1 - ŝ)(1 - a ŝ))`) and the lattice convolution of
`(|z| + W)^{-(d-2)}` with itself. -/
theorem ThetaZd_sub_decay :
  ∀ (d : ℕ) (hd : 5 ≤ d) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ), ∃ C₀ W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W →
      ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s → ∀ (a : ℝ), 0 ≤ a → a ≤ 1 →
        ∀ x : Fin d → ℤ,
          ‖ThetaInf s x - ThetaZd a s x‖ ≤
            C₀ * (1 - a) / ((W : ℝ) ^ 4 * ((zdInf x : ℝ) + W) ^ (d - 4)) := by
  intro d hd ψ cψ hψ C
  have hd3 : 3 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀', W₀', h0⟩ := ThetaZd_decay d hd3 ψ cψ hψ C 0
  obtain ⟨Wt, hWt1, ht⟩ := theta_series d hd3 ψ cψ hψ C
  obtain ⟨c, W₂, hc, hW₂⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  obtain ⟨K₀, hK₀⟩ := zdSymbol_smooth d ψ C 0
  set Cd : ℝ := 2 * (d * 2 ^ (2 * d - 2) * 2 ^ (d - 4)) with hCd
  have hCd0 : 0 ≤ Cd := by positivity
  refine ⟨|C₀'| + C₀' ^ 2 * Cd, max (max W₀' Wt) W₂, ?_⟩
  intro W hW s hs a ha0 ha1 x
  have hW0' : W₀' ≤ (W : ℝ) := le_trans (by simp) hW
  have hWt : Wt ≤ (W : ℝ) := le_trans (by simp) hW
  have hW2' : W₂ ≤ (W : ℝ) := le_trans (by simp) hW
  have hW1 : (1 : ℝ) ≤ W := hWt1.trans hWt
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  rcases eq_or_lt_of_le ha1 with rfl | ha
  · have : ThetaInf s x - ThetaZd 1 s x = 0 := sub_eq_zero.2 rfl
    rw [this, norm_zero, sub_self, mul_zero, zero_div]
  -- the bounds `|Θ(z)| ≤ C W^{-2} (|z| + W)^{-(d-2)}`
  have hbd : ∀ (b : ℝ), 0 ≤ b → b ≤ 1 → ∀ z, ‖ThetaZd b s z‖ ≤
      |C₀'| / (W : ℝ) ^ 2 * (((zdInf z : ℝ) + W) ^ (d - 2))⁻¹ := by
    intro b hb0 hb1 z
    have h := (h0 W hW0' s hs b hb0 hb1).2 z
    rw [pow_zero, mul_one] at h
    refine h.trans ?_
    have e : |C₀'| / (W : ℝ) ^ 2 * (((zdInf z : ℝ) + W) ^ (d - 2))⁻¹ =
        |C₀'| / ((W : ℝ) ^ 2 * ((zdInf z : ℝ) + W) ^ (d - 2)) := by ring
    rw [e]
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  obtain ⟨hF1, -⟩ := h0 W hW0' s hs 1 zero_le_one le_rfl
  obtain ⟨hFa, -⟩ := h0 W hW0' s hs a ha0 ha1
  obtain ⟨hΘs, hser⟩ := ht W hWt s hs a ha0 ha
  obtain ⟨hcd, -, hK0⟩ := hK₀ W hWn s hs
  -- `Θ_{ℤ^d}(a)` is bounded on the cube
  have hFab : ∀ p ∈ cubePi d, ‖thetaSym a s p‖ ≤ 2 * |K₀| / (1 - a) := by
    intro p hp
    obtain ⟨him, hge⟩ := hW₂ W hW2' s hs p hp
    set σ := (zdSymbol s p).re with hσ
    have hse : zdSymbol s p = (σ : ℂ) := Complex.ext (by simp [hσ]) (by simp [him])
    have hσ1 : σ ≤ 1 := by
      have : 0 ≤ c * min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
        mul_nonneg hc.le (le_min (mul_nonneg (by positivity) (sqNorm_nonneg' p)) zero_le_one)
      linarith
    have hhalf := one_sub_mul_ge_half ha0 ha.le hσ1
    have h1a : 0 < 1 - a := by linarith
    have hσK : |σ| ≤ |K₀| := by
      have := hK0 p
      rw [norm_iteratedFDeriv_zero, pow_zero, mul_one, hse, Complex.norm_real,
        Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have hcast : thetaSym a s p = ((a * σ / (1 - a * σ) : ℝ) : ℂ) := by
      simp only [thetaSym, hse]; push_cast; rfl
    have hv : 0 < 1 - a * σ := by linarith
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hv,
      div_le_div_iff₀ hv h1a, abs_mul, abs_of_nonneg ha0]
    have h3 : a * |σ| ≤ |K₀| := by
      calc a * |σ| ≤ 1 * |K₀| := mul_le_mul ha1 hσK (abs_nonneg _) zero_le_one
        _ = |K₀| := one_mul _
    have h4 : 1 - a ≤ 2 * (1 - a * σ) := by linarith
    calc a * |σ| * (1 - a) ≤ |K₀| * (2 * (1 - a * σ)) :=
          mul_le_mul h3 h4 h1a.le (abs_nonneg _)
      _ = 2 * |K₀| * (1 - a * σ) := by ring
  have hFaF1 : IntegrableOn (fun p => thetaSym a s p * thetaSym 1 s p) (cubePi d) := by
    refine Integrable.bdd_mul (c := 2 * |K₀| / (1 - a)) hF1 hFa.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_cubePi'] with p hp
    exact hFab p hp
  -- the convolution `Θ_∞ * Θ_{ℤ^d}(a)`
  have hconv : latticeFourier (fun p => thetaSym a s p * thetaSym 1 s p) x =
      ∑' z, ThetaZd a s z * ThetaInf s (x - z) := by
    rw [latticeFourier_congr (G := fun p => zdSeries (ThetaZd a s) p * thetaSym 1 s p)
      (fun p hp => by rw [hser p hp]) x]
    exact latticeFourier_zdSeries_mul hΘs hF1 x
  -- the identity `Θ_∞ - Θ_{ℤ^d}(a) = (1 - a)(Θ_∞ + Θ_{ℤ^d}(a) * Θ_∞)`
  have hae : ∀ᵐ p ∂(volume.restrict (cubePi d)), thetaSym 1 s p - thetaSym a s p =
      ((1 - a : ℝ) : ℂ) * (thetaSym 1 s p + thetaSym a s p * thetaSym 1 s p) := by
    filter_upwards [ae_restrict_mem measurableSet_cubePi',
      ae_restrict_of_ae (s := cubePi d) (ae_coord_ne_zero (d := d))] with p hp hp0
    obtain ⟨him, hge⟩ := hW₂ W hW2' s hs p hp
    set σ := (zdSymbol s p).re with hσ
    have hse : zdSymbol s p = (σ : ℂ) := Complex.ext (by simp [hσ]) (by simp [him])
    have hsq : 0 < sqNorm p := by
      have h0 : p ⟨0, by omega⟩ ≠ 0 := hp0 _
      exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => p i ^ 2)
        (fun j _ => sq_nonneg (p j)) (Finset.mem_univ ⟨0, by omega⟩))
    have hu : 0 < 1 - σ := by
      have : 0 < c * min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
        mul_pos hc (lt_min (by positivity) one_pos)
      linarith
    have hσ1 : σ ≤ 1 := by linarith
    have hv : 0 < 1 - a * σ := by
      have := one_sub_mul_ge_half ha0 ha.le hσ1; linarith
    have hu' : (1 : ℂ) - (1 : ℝ) * (σ : ℂ) ≠ 0 := by
      have : ((1 - σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
      simpa using this
    have hv' : (1 : ℂ) - (a : ℂ) * (σ : ℂ) ≠ 0 := by
      have : ((1 - a * σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
      simpa using this
    have c1 : thetaSym 1 s p = ((σ / (1 - σ) : ℝ) : ℂ) := by
      simp only [thetaSym, hse]; push_cast; ring
    have c2 : thetaSym a s p = ((a * σ / (1 - a * σ) : ℝ) : ℂ) := by
      simp only [thetaSym, hse]; push_cast; ring
    have hr : σ / (1 - σ) - a * σ / (1 - a * σ) =
        (1 - a) * (σ / (1 - σ) + a * σ / (1 - a * σ) * (σ / (1 - σ))) := by
      have hu1 : 1 - σ ≠ 0 := hu.ne'
      have hv1 : 1 - a * σ ≠ 0 := hv.ne'
      have hv2 : 1 - σ * a ≠ 0 := by rw [mul_comm]; exact hv1
      field_simp
      ring
    rw [c1, c2]
    exact_mod_cast hr
  have hid : ThetaInf s x - ThetaZd a s x = ((1 - a : ℝ) : ℂ) *
      (ThetaInf s x + ∑' z, ThetaZd a s z * ThetaInf s (x - z)) := by
    have e1 : ThetaInf s x - ThetaZd a s x =
        latticeFourier (fun p => thetaSym 1 s p - thetaSym a s p) x :=
      (latticeFourier_sub hF1 hFa x).symm
    rw [e1, latticeFourier_congr_ae hae x, latticeFourier_const_mul,
      latticeFourier_add (F := thetaSym 1 s) (G := fun p => thetaSym a s p * thetaSym 1 s p)
        hF1 hFaF1, hconv]
    rfl
  -- the bound
  obtain ⟨hcs, hct⟩ := conv_sum_le (d := d) hd hW1 x
  set g : (Fin d → ℤ) → ℝ := fun z => (((zdInf z : ℝ) + W) ^ (d - 2))⁻¹ *
    (((zdInf (x - z) : ℝ) + W) ^ (d - 2))⁻¹ with hg
  have hpt : ∀ z, ‖ThetaZd a s z * ThetaInf s (x - z)‖ ≤ (|C₀'| / (W : ℝ) ^ 2) ^ 2 * g z := by
    intro z
    rw [norm_mul]
    have h1 := hbd a ha0 ha1 z
    have h2 := hbd 1 zero_le_one le_rfl (x - z)
    calc ‖ThetaZd a s z‖ * ‖ThetaInf s (x - z)‖
        ≤ (|C₀'| / (W : ℝ) ^ 2 * (((zdInf z : ℝ) + W) ^ (d - 2))⁻¹) *
          (|C₀'| / (W : ℝ) ^ 2 * (((zdInf (x - z) : ℝ) + W) ^ (d - 2))⁻¹) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (|C₀'| / (W : ℝ) ^ 2) ^ 2 * g z := by simp only [hg]; ring
  have hsn : Summable fun z => ‖ThetaZd a s z * ThetaInf s (x - z)‖ :=
    Summable.of_nonneg_of_le (fun z => norm_nonneg _) hpt (hcs.mul_left _)
  have hsum : ‖∑' z, ThetaZd a s z * ThetaInf s (x - z)‖ ≤
      (|C₀'| / (W : ℝ) ^ 2) ^ 2 * (Cd * (((zdInf x : ℝ) + W) ^ (d - 4))⁻¹) := by
    refine (norm_tsum_le_tsum_norm hsn).trans ?_
    refine (Summable.tsum_le_tsum hpt hsn (hcs.mul_left _)).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hct (by positivity)
  have hx1 : ‖ThetaInf s x‖ ≤ |C₀'| / (W : ℝ) ^ 4 * (((zdInf x : ℝ) + W) ^ (d - 4))⁻¹ := by
    refine (hbd 1 zero_le_one le_rfl x).trans ?_
    have e : ((zdInf x : ℝ) + W) ^ (d - 2) =
        ((zdInf x : ℝ) + W) ^ 2 * ((zdInf x : ℝ) + W) ^ (d - 4) := by
      rw [← pow_add]; congr 1; omega
    have hWx : (W : ℝ) ^ 2 ≤ ((zdInf x : ℝ) + W) ^ 2 :=
      pow_le_pow_left₀ hW0.le (by linarith [(Nat.cast_nonneg (zdInf x) : (0 : ℝ) ≤ zdInf x)]) 2
    set Z : ℝ := (zdInf x : ℝ) + W with hZ
    have e3 : |C₀'| / (W : ℝ) ^ 2 * (Z ^ 2 * Z ^ (d - 4))⁻¹ =
        |C₀'| * ((W : ℝ) ^ 2 * Z ^ 2 * Z ^ (d - 4))⁻¹ := by ring_nf
    have e4 : |C₀'| / (W : ℝ) ^ 4 * (Z ^ (d - 4))⁻¹ =
        |C₀'| * ((W : ℝ) ^ 2 * (W : ℝ) ^ 2 * Z ^ (d - 4))⁻¹ := by ring
    have hZ0 : 0 < Z := by positivity
    rw [e, e3, e4]
    gcongr
  have h1a : (0 : ℝ) ≤ 1 - a := by linarith
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1a]
  have htot : ‖ThetaInf s x + ∑' z, ThetaZd a s z * ThetaInf s (x - z)‖ ≤
      (|C₀'| + C₀' ^ 2 * Cd) / ((W : ℝ) ^ 4 * ((zdInf x : ℝ) + W) ^ (d - 4)) := by
    refine (norm_add_le _ _).trans ((add_le_add hx1 hsum).trans (le_of_eq ?_))
    rw [div_pow, sq_abs]
    field_simp
  calc (1 - a) * ‖ThetaInf s x + ∑' z, ThetaZd a s z * ThetaInf s (x - z)‖
      ≤ (1 - a) * ((|C₀'| + C₀' ^ 2 * Cd) / ((W : ℝ) ^ 4 * ((zdInf x : ℝ) + W) ^ (d - 4))) :=
        mul_le_mul_of_nonneg_left htot h1a
    _ = (|C₀'| + C₀' ^ 2 * Cd) * (1 - a) / ((W : ℝ) ^ 4 * ((zdInf x : ℝ) + W) ^ (d - 4)) := by
        ring

end Difference


section Witness

end Witness

end RBM8D
