import RBM8D.Kernel.Lattice
import RBM8D.Kernel.Dyadic
import RBM8D.Kernel.Circulant

/-!
# The symbol of an `InfKernel`

Kernels on `ℤ^d` close to the profile `ψ(W·)`: smoothness of the symbol, the lower bound of `1 - ŝ` near `0` (the role of [I, (1.31)]), integration by parts on the cube.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d : ℕ}

/-- A kernel on `ℤ^d` at band width `W` with the constants `C`: symmetric, with sum one, the
decay `|s(x)| ≤ C_k W^{-d} (1 + |x|/W)^{-k}` of [I, (1.8)], and symbol close to `ψ(W·)` on
`[-π, π]^d`: `|ŝ(p) - ψ(Wp)| ≤ C_{D′} W^{-D′}`. -/
structure InfKernel (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (C : ℕ → ℝ) (W : ℕ)
    (s : (Fin d → ℤ) → ℝ) : Prop where
  symm : ∀ x, s (-x) = s x
  sum_one : ∑' x, s x = 1
  decay : ∀ (k : ℕ) (x : Fin d → ℤ), |s x| * (1 + (zdInf x : ℝ) / W) ^ k ≤ C k / (W : ℝ) ^ d
  close : ∀ (D' : ℕ) (p : Fin d → ℝ), p ∈ cubePi d →
    ‖zdSymbol s p - (ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ)‖ ≤ C D' / (W : ℝ) ^ D'


/-! ## Plane waves -/

private theorem natAbs_le_zdInf (x : Fin d → ℤ) (j : Fin d) :
    |((x j : ℤ) : ℝ)| ≤ (zdInf x : ℝ) := by
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ j)

/-- The real-linear form `p ↦ i (p·x)` on `ℝ^d`. -/
private def linI (x : Fin d → ℤ) : (Fin d → ℝ) →L[ℝ] ℂ :=
  Complex.I • (Complex.ofRealCLM.comp (∑ j, ((x j : ℤ) : ℝ) • ContinuousLinearMap.proj j))

private theorem linI_apply (x : Fin d → ℤ) (p : Fin d → ℝ) :
    linI x p = ((∑ j, p j * (x j : ℝ) : ℝ) : ℂ) * I := by
  simp [linI, mul_comm]

private theorem zexp_eq (p : Fin d → ℝ) (x : Fin d → ℤ) : zexp p x = Complex.exp (linI x p) := by
  rw [linI_apply]; rfl

private theorem norm_linI_le (x : Fin d → ℤ) : ‖linI x‖ ≤ d * (zdInf x : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  rw [linI_apply, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc |∑ j, p j * (x j : ℝ)| ≤ ∑ j, |p j * (x j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, ‖p‖ * (zdInf x : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm p j)
          (natAbs_le_zdInf x j) (abs_nonneg _) (norm_nonneg _)
    _ = d * (zdInf x : ℝ) * ‖p‖ := by simp; ring

private theorem norm_iteratedFDeriv_cexp (k : ℕ) (z : ℂ) (hz : z.re = 0) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖ = ‖iteratedFDeriv ℝ k Complex.exp 0‖ := by
  have h1 : iteratedFDeriv ℝ k Complex.exp z =
      iteratedFDeriv ℝ k (fun w => Complex.exp (w + z)) 0 := by
    rw [iteratedFDeriv_comp_add_right, zero_add]
  have h2 : (fun w => Complex.exp (w + z)) = fun w => Complex.exp z • Complex.exp w := by
    funext w; rw [Complex.exp_add, smul_eq_mul, mul_comm]
  rw [h1, h2, iteratedFDeriv_const_smul_apply' (Complex.contDiff_exp.contDiffAt), norm_smul,
    Complex.norm_exp, hz, Real.exp_zero, one_mul]

private theorem contDiff_zexp (x : Fin d → ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun p : Fin d → ℝ => zexp p x := by
  simp_rw [zexp_eq]
  exact Complex.contDiff_exp.comp (linI x).contDiff

private theorem norm_iteratedFDeriv_zexp_le (k : ℕ) (x : Fin d → ℤ) (p : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ k (fun p : Fin d → ℝ => zexp p x) p‖ ≤
      ‖iteratedFDeriv ℝ k Complex.exp 0‖ * ((d : ℝ) * zdInf x) ^ k := by
  have e : (fun p : Fin d → ℝ => zexp p x) = Complex.exp ∘ linI x := by
    funext p; rw [zexp_eq]; rfl
  rw [e, (linI x).iteratedFDeriv_comp_right Complex.contDiff_exp p (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_cexp k _ (by simp [linI_apply]), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  gcongr
  exact norm_linI_le x

private theorem zexp_add_single (p : Fin d → ℝ) (x : Fin d → ℤ) (i : Fin d) :
    zexp (p + Pi.single i (2 * Real.pi)) x = zexp p x := by
  unfold zexp
  have h : ∑ j, (p + Pi.single i (2 * Real.pi) : Fin d → ℝ) j * (x j : ℝ) =
      (∑ j, p j * (x j : ℝ)) + 2 * Real.pi * (x i : ℝ) := by
    simp [add_mul, Finset.sum_add_distrib, Pi.single_apply]
  rw [h]
  push_cast
  rw [add_mul, Complex.exp_add]
  have : Complex.exp (2 * (Real.pi : ℂ) * ((x i : ℤ) : ℂ) * I) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * ((x i : ℤ) : ℂ) * I = ((x i : ℤ) : ℂ) * (2 * Real.pi * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [this, mul_one]



/-! ## Integration by parts on the cube -/

private theorem cubePi_eq_Icc :
    cubePi d = Set.Icc (fun _ : Fin d => -Real.pi) (fun _ => Real.pi) := by
  unfold cubePi
  rw [← Set.pi_univ_Icc]

private theorem isCompact_cubePi' : IsCompact (cubePi d) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem insertNth_add_single {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) i (-Real.pi) y + Pi.single i (2 * Real.pi) =
      Fin.insertNth (α := fun _ => ℝ) i Real.pi y := by
  funext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
  · simp only [Pi.add_apply, Fin.insertNth_apply_same, Pi.single_eq_same]; ring
  · simp [Fin.insertNth_apply_succAbove, Fin.succAbove_ne]

/-- A `C^1` function `2π`-periodic in the coordinate `i` has `∫_{[-π,π]^d} ∂_i G = 0`. -/
private theorem integral_fderiv_single_eq_zero {n : ℕ} (G : (Fin (n + 1) → ℝ) → ℂ)
    (hG : ContDiff ℝ 1 G) (i : Fin (n + 1))
    (hper : ∀ p, G (p + Pi.single i (2 * Real.pi)) = G p) :
    ∫ p in cubePi (n + 1), fderiv ℝ G p (Pi.single i 1) = 0 := by
  classical
  set a : Fin (n + 1) → ℝ := fun _ => -Real.pi
  set b : Fin (n + 1) → ℝ := fun _ => Real.pi
  have hab : a ≤ b := fun _ => by simp only [a, b]; linarith [Real.pi_pos]
  set f : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ := fun j => if j = i then G else fun _ => 0
  set f' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℂ :=
    fun j p => if j = i then fderiv ℝ G p else 0
  have hsum : ∀ p, ∑ j, f' j p (Pi.single j 1) = fderiv ℝ G p (Pi.single i 1) := by
    intro p
    rw [Finset.sum_eq_single i]
    · simp [f']
    · intro j _ hj; simp [f', hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hcont : Continuous fun p => fderiv ℝ G p (Pi.single i 1) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab f f' ∅
    Set.countable_empty
    (fun j => by
      by_cases hj : j = i
      · simp only [f, hj, ite_true]; exact hG.continuous.continuousOn
      · simp only [f, hj, ite_false]; exact continuousOn_const)
    (fun p _ j => by
      by_cases hj : j = i
      · simp only [f, f', hj, ite_true]
        exact (hG.differentiable one_ne_zero p).hasFDerivAt
      · simp only [f, f', hj, ite_false]; exact hasFDerivAt_const _ _)
    (by
      simp_rw [hsum]
      exact hcont.continuousOn.integrableOn_compact isCompact_Icc)
  simp_rw [hsum] at h
  rw [cubePi_eq_Icc, h]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp only [f, ite_true, b, a]
    rw [sub_eq_zero]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [← insertNth_add_single, hper]
  · simp [f, hj]

/-- One integration by parts in the coordinate `i` against `e^{-ip·x}`. -/
private theorem integral_fderiv_mul_zexp {n : ℕ} (H : (Fin (n + 1) → ℝ) → ℂ)
    (hH : ContDiff ℝ 1 H) (i : Fin (n + 1))
    (hper : ∀ p, H (p + Pi.single i (2 * Real.pi)) = H p) (x : Fin (n + 1) → ℤ) :
    ∫ p in cubePi (n + 1), fderiv ℝ H p (Pi.single i 1) * zexp p (-x) =
      ((x i : ℂ) * I) * ∫ p in cubePi (n + 1), H p * zexp p (-x) := by
  set G : (Fin (n + 1) → ℝ) → ℂ := fun p => H p * zexp p (-x)
  have hz : ContDiff ℝ 1 fun p : Fin (n + 1) → ℝ => zexp p (-x) :=
    (contDiff_zexp (-x)).of_le (by exact_mod_cast le_top)
  have hG : ContDiff ℝ 1 G := hH.mul hz
  have hGper : ∀ p, G (p + Pi.single i (2 * Real.pi)) = G p := fun p => by
    simp only [G, hper, zexp_add_single]
  have hderz : ∀ p, HasFDerivAt (fun p : Fin (n + 1) → ℝ => zexp p (-x))
      (zexp p (-x) • linI (-x)) p := fun p => by
    simp_rw [zexp_eq]
    exact (linI (-x)).hasFDerivAt.cexp
  have hfd : ∀ p, fderiv ℝ G p (Pi.single i 1) =
      fderiv ℝ H p (Pi.single i 1) * zexp p (-x) - ((x i : ℂ) * I) * (H p * zexp p (-x)) := by
    intro p
    have hH' := (hH.differentiable one_ne_zero p).hasFDerivAt
    have := (hH'.mul' (hderz p)).fderiv
    have e : (H * fun p : Fin (n + 1) → ℝ => zexp p (-x)) = G := rfl
    rw [e] at this
    rw [this]
    simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, linI_apply]
    simp [Pi.single_apply, MulOpposite.smul_eq_mul_unop]
    ring
  have h0 := integral_fderiv_single_eq_zero G hG i hGper
  simp_rw [hfd] at h0
  have hc1 : Continuous fun p => fderiv ℝ H p (Pi.single i 1) * zexp p (-x) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hz.continuous
  have hc2 : Continuous fun p => ((x i : ℂ) * I) * (H p * zexp p (-x)) :=
    continuous_const.mul (hH.continuous.mul hz.continuous)
  rw [integral_sub (hc1.continuousOn.integrableOn_compact isCompact_cubePi')
    (hc2.continuousOn.integrableOn_compact isCompact_cubePi'), integral_const_mul,
    sub_eq_zero] at h0
  exact h0

/-- `N` integrations by parts in the coordinate `i` against `e^{-ip·x}`. -/
private theorem integral_iteratedFDeriv_mul_zexp {n N : ℕ} (F : (Fin (n + 1) → ℝ) → ℂ)
    (hF : ContDiff ℝ N F) (i : Fin (n + 1))
    (hper : ∀ p, F (p + Pi.single i (2 * Real.pi)) = F p) (x : Fin (n + 1) → ℤ) :
    ∀ k ≤ N, ∫ p in cubePi (n + 1),
        iteratedFDeriv ℝ k F p (fun _ => Pi.single i 1) * zexp p (-x) =
      ((x i : ℂ) * I) ^ k * ∫ p in cubePi (n + 1), F p * zexp p (-x) := by
  intro k
  induction k with
  | zero => intro _; simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro hk
    set H : (Fin (n + 1) → ℝ) → ℂ := fun p => iteratedFDeriv ℝ k F p (fun _ => Pi.single i 1)
    have hk' : (1 : WithTop ℕ∞) + (k : WithTop ℕ∞) ≤ (N : WithTop ℕ∞) := by
      exact_mod_cast (by omega : 1 + k ≤ N)
    have hD : ContDiff ℝ 1 (iteratedFDeriv ℝ k F) := hF.iteratedFDeriv_right hk'
    have hH : ContDiff ℝ 1 H :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin (n + 1) → ℝ) ℂ
        (fun _ => Pi.single i 1)).contDiff.comp hD
    have hHper : ∀ p, H (p + Pi.single i (2 * Real.pi)) = H p := by
      intro p
      simp only [H]
      rw [← iteratedFDeriv_comp_add_right]
      have : (fun z => F (z + Pi.single i (2 * Real.pi))) = F := funext hper
      rw [this]
    have hfd : ∀ p, fderiv ℝ H p (Pi.single i 1) =
        iteratedFDeriv ℝ (k + 1) F p (fun _ => Pi.single i 1) := by
      intro p
      rw [iteratedFDeriv_succ_apply_left]
      exact fderiv_continuousMultilinear_apply_const_apply (hD.differentiable one_ne_zero p) _ _
    have h := integral_fderiv_mul_zexp H hH i hHper x
    simp_rw [hfd] at h
    rw [h, ih (by omega), pow_succ]
    ring

/-- Integration by parts on `[-π, π]^d` for a `C^N` function `F` that is `2π`-periodic in each
coordinate: `|x|^N |(2π)^{-d} ∫ F(p) e^{-ip·x} dp| ≤ (2π)^{-d} ∫ ‖D^N F(p)‖ dp`, with `|x|` the
`ℓ^∞` norm (the role of [I, Appendix B]). -/
theorem norm_latticeFourier_mul_pow_le :
  ∀ {d : ℕ} (N : ℕ) (F : (Fin d → ℝ) → ℂ) (hF : ContDiff ℝ N F)
    (hper : ∀ (i : Fin d) (p : Fin d → ℝ), F (p + Pi.single i (2 * Real.pi)) = F p)
    (x : Fin d → ℤ),
    ‖latticeFourier F x‖ * (zdInf x : ℝ) ^ N ≤
      ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖iteratedFDeriv ℝ N F p‖ := by
  intro d N F hF hper x
  have hnormc : ‖((2 * Real.pi : ℂ) ^ d)⁻¹‖ = ((2 * Real.pi) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow]
    congr 2
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hRHS0 : 0 ≤ ∫ p in cubePi d, ‖iteratedFDeriv ℝ N F p‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hcont : Continuous fun p => ‖iteratedFDeriv ℝ N F p‖ :=
    (hF.continuous_iteratedFDeriv le_rfl).norm
  by_cases hx : zdInf x = 0
  · cases N with
    | zero =>
      simp only [pow_zero, mul_one]
      unfold latticeFourier
      rw [norm_mul, hnormc]
      gcongr
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      congr 1
      funext p
      rw [norm_mul, norm_zexp, mul_one, norm_iteratedFDeriv_zero]
    | succ N =>
      rw [hx]
      simp only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, zero_pow, mul_zero]
      positivity
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := by
      cases d with
      | zero => exact absurd (by simp [zdInf]) hx
      | succ n => exact ⟨n, rfl⟩
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun j => (x j).natAbs
    have hxi : (zdInf x : ℝ) = ‖((x i : ℂ) * I)‖ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
      unfold zdInf
      rw [hi, Nat.cast_natAbs, Int.cast_abs]
    have key := integral_iteratedFDeriv_mul_zexp F hF i (hper i) x N le_rfl
    unfold latticeFourier
    rw [norm_mul, hnormc, mul_assoc]
    gcongr
    rw [hxi, ← norm_pow, mul_comm, ← norm_mul, ← key]
    refine norm_integral_le_of_norm_le (hcont.continuousOn.integrableOn_compact isCompact_cubePi')
      (ae_of_all _ fun p => ?_)
    rw [norm_mul, norm_zexp, mul_one]
    refine ((iteratedFDeriv ℝ N F p).le_opNorm _).trans (le_of_eq ?_)
    simp [Pi.norm_single]

/-! ## Moments of an `InfKernel` -/

private theorem sum_range_le (W : ℝ) (hW : 1 ≤ W) (M : ℕ) :
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

/-- The one-dimensional weight `(1 + |m|/W)^{-2}`. -/
private def wt (W : ℝ) (m : ℤ) : ℝ := ((1 + |(m : ℝ)| / W) ^ 2)⁻¹

private theorem wt_nonneg (W : ℝ) (hW : 1 ≤ W) (m : ℤ) : 0 ≤ wt W m := by
  unfold wt; have : 0 ≤ |(m : ℝ)| / W := by positivity
  positivity

private theorem summable_wt (W : ℝ) (hW : 1 ≤ W) : Summable (wt W) ∧ ∑' m, wt W m ≤ 1 + 2 * W := by
  have hpos : ∀ n : ℕ, 0 ≤ ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ := fun n => by
    have : 0 ≤ ((n : ℝ) + 1) / W := by positivity
    positivity
  have hsr : ∀ n, ∑ i ∈ Finset.range n, ((1 + ((i : ℝ) + 1) / W) ^ 2)⁻¹ ≤ W := fun n => by
    have := sum_range_le W hW n
    have : 0 ≤ W ^ 2 / (W + n) := by positivity
    linarith
  have hA := summable_of_sum_range_le hpos hsr
  have hAle := Real.tsum_le_of_sum_range_le hpos hsr
  have e1 : (fun n : ℕ => wt W ((n + 1 : ℕ) : ℤ)) =
      fun n : ℕ => ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ := by
    funext n; unfold wt; push_cast
    rw [abs_of_nonneg (by positivity)]
  have e2 : (fun n : ℕ => wt W (-((n : ℤ) + 1))) =
      fun n : ℕ => ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ := by
    funext n; unfold wt; push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hnat : Summable fun n : ℕ => wt W n := by
    rw [← summable_nat_add_iff 1]
    have : (fun n : ℕ => wt W ((n + 1 : ℕ) : ℤ)) = fun n : ℕ => wt W (((n + 1 : ℕ) : ℤ)) := rfl
    exact_mod_cast (e1 ▸ hA : Summable fun n : ℕ => wt W ((n + 1 : ℕ) : ℤ))
  have hneg : Summable fun n : ℕ => wt W (-((n : ℤ) + 1)) := by rw [e2]; exact hA
  refine ⟨hnat.of_nat_of_neg_add_one hneg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add, e2]
  have e0 : wt W ((0 : ℕ) : ℤ) = 1 := by simp [wt]
  have e1' : (∑' n : ℕ, wt W ((n + 1 : ℕ) : ℤ)) = ∑' n : ℕ, ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ := by
    rw [e1]
  rw [e0, e1']
  linarith


private theorem summable_of_le_prod (f : (Fin d → ℤ) → ℝ) (g : ℤ → ℝ) (A B : ℝ) (hA : 0 ≤ A)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ m, 0 ≤ g m) (hg : Summable g) (hgB : ∑' m, g m ≤ B)
    (hfg : ∀ x, f x ≤ A * ∏ j, g (x j)) : Summable f ∧ ∑' x, f x ≤ A * B ^ d := by
  classical
  have hu : ∀ u : Finset (Fin d → ℤ), ∑ x ∈ u, f x ≤ A * B ^ d := by
    intro u
    set T : Fin d → Finset ℤ := fun j => u.image fun x => x j
    have hsub : u ⊆ Fintype.piFinset T := fun x hx =>
      Fintype.mem_piFinset.2 fun j => Finset.mem_image_of_mem _ hx
    have hT : ∀ j, ∑ m ∈ T j, g m ≤ B := fun j =>
      (hg.sum_le_tsum _ fun m _ => hg0 m).trans hgB
    have hT0 : ∀ j, 0 ≤ ∑ m ∈ T j, g m := fun j => Finset.sum_nonneg fun m _ => hg0 m
    calc ∑ x ∈ u, f x ≤ ∑ x ∈ Fintype.piFinset T, f x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hf0 x
      _ ≤ ∑ x ∈ Fintype.piFinset T, A * ∏ j, g (x j) := Finset.sum_le_sum fun x _ => hfg x
      _ = A * ∏ j, ∑ m ∈ T j, g m := by
          rw [← Finset.mul_sum, Finset.prod_univ_sum]
      _ ≤ A * ∏ _j : Fin d, B := by
          exact mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun j _ => hT0 j) fun j _ => hT j) hA
      _ = A * B ^ d := by simp
  exact ⟨summable_of_sum_le (fun x => hf0 x) hu, Real.tsum_le_of_sum_le (fun x => hf0 x) hu⟩

private theorem InfKernel.C_nonneg {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ} {W : ℕ}
    {s : (Fin d → ℤ) → ℝ} (hW : 1 ≤ W) (hs : InfKernel ψ C W s) (k : ℕ) : 0 ≤ C k := by
  have h := hs.decay k 0
  have hW' : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have : 0 ≤ |s 0| * (1 + (zdInf (0 : Fin d → ℤ) : ℝ) / W) ^ k := by
    have : 0 ≤ (zdInf (0 : Fin d → ℤ) : ℝ) / W := by positivity
    positivity
  have := this.trans h
  rwa [le_div_iff₀ hW', zero_mul] at this

/-- The moment bound `Σ_x |s(x)| |x|^k ≤ 3^d C_{k+2d} W^k`. -/
private theorem InfKernel.moment {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ} {W : ℕ}
    {s : (Fin d → ℤ) → ℝ} (hW : 1 ≤ W) (hs : InfKernel ψ C W s) (k : ℕ) :
    Summable (fun x => |s x| * (zdInf x : ℝ) ^ k) ∧
      ∑' x, |s x| * (zdInf x : ℝ) ^ k ≤ 3 ^ d * C (k + 2 * d) * (W : ℝ) ^ k := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hC := hs.C_nonneg hW (k + 2 * d)
  obtain ⟨hg, hgB⟩ := summable_wt (W : ℝ) hW1
  have hA : 0 ≤ C (k + 2 * d) * (W : ℝ) ^ k / (W : ℝ) ^ d := by positivity
  have hpt : ∀ x : Fin d → ℤ, |s x| * (zdInf x : ℝ) ^ k ≤
      C (k + 2 * d) * (W : ℝ) ^ k / (W : ℝ) ^ d * ∏ j, wt W (x j) := by
    intro x
    set z : ℝ := (zdInf x : ℝ)
    have hz : 0 ≤ z := Nat.cast_nonneg _
    set t : ℝ := 1 + z / W
    have ht : 1 ≤ t := by have : 0 ≤ z / W := by positivity
                          linarith
    have ht0 : 0 < t := by linarith
    have hzt : z ≤ W * t := by
      simp only [t]; rw [mul_add, mul_div_cancel₀ _ hW0.ne']; linarith
    have hdec := hs.decay (k + 2 * d) x
    have hprod : (t ^ (2 * d))⁻¹ ≤ ∏ j, wt W (x j) := by
      have : ∀ j, (t ^ 2)⁻¹ ≤ wt W (x j) := by
        intro j
        unfold wt
        have h1 : 0 ≤ |((x j : ℤ) : ℝ)| / W := by positivity
        have h2 : 1 + |((x j : ℤ) : ℝ)| / W ≤ t := by
          simp only [t]; gcongr; exact natAbs_le_zdInf x j
        gcongr
      calc (t ^ (2 * d))⁻¹ = ∏ _j : Fin d, (t ^ 2)⁻¹ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow, pow_mul, inv_pow]
        _ ≤ ∏ j, wt W (x j) := Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => this j
    calc |s x| * z ^ k ≤ |s x| * ((W : ℝ) ^ k * t ^ k) := by
          rw [← mul_pow]; gcongr
      _ = (W : ℝ) ^ k * (|s x| * t ^ (k + 2 * d)) * (t ^ (2 * d))⁻¹ := by
          rw [pow_add]; field_simp
      _ ≤ (W : ℝ) ^ k * (C (k + 2 * d) / (W : ℝ) ^ d) * ∏ j, wt W (x j) := by
          gcongr
      _ = _ := by ring
  have := summable_of_le_prod (fun x => |s x| * (zdInf x : ℝ) ^ k) (wt W) _ (1 + 2 * W) hA
    (fun x => by positivity) (wt_nonneg W hW1) hg hgB hpt
  refine ⟨this.1, this.2.trans ?_⟩
  calc C (k + 2 * d) * (W : ℝ) ^ k / (W : ℝ) ^ d * (1 + 2 * W) ^ d
      ≤ C (k + 2 * d) * (W : ℝ) ^ k / (W : ℝ) ^ d * (3 * W) ^ d := by
        gcongr; linarith
    _ = 3 ^ d * C (k + 2 * d) * (W : ℝ) ^ k := by
        rw [mul_pow]; field_simp

/-! ## Smoothness of the symbol -/

/-- The symbol of an `InfKernel` with `W ≥ 1` is smooth and `2π`-periodic in each coordinate,
with `‖D^n ŝ(p)‖ ≤ K_n W^n`, `K_n` depending only on `d`, `C` and `n` (from the decay
[I, (1.8)]). -/
theorem zdSymbol_smooth :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (C : ℕ → ℝ) (n : ℕ), ∃ K : ℝ,
    ∀ (W : ℕ) (hW : 1 ≤ W) (s : (Fin d → ℤ) → ℝ), InfKernel ψ C W s →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (zdSymbol s) ∧
      (∀ (i : Fin d) (p : Fin d → ℝ), zdSymbol s (p + Pi.single i (2 * Real.pi)) = zdSymbol s p) ∧
      ∀ p, ‖iteratedFDeriv ℝ n (zdSymbol s) p‖ ≤ K * (W : ℝ) ^ n := by
  intro d ψ C n
  refine ⟨‖iteratedFDeriv ℝ n Complex.exp 0‖ * (d : ℝ) ^ n * (3 ^ d * C (n + 2 * d)), ?_⟩
  intro W hW s hs
  set f : (Fin d → ℤ) → (Fin d → ℝ) → ℂ := fun x p => s x • zexp p x with hf
  have hsym : zdSymbol s = fun p => ∑' x, f x p := by
    funext p
    simp only [zdSymbol, zdSeries, hf, Complex.real_smul]
  set v : ℕ → (Fin d → ℤ) → ℝ := fun k x =>
    ‖iteratedFDeriv ℝ k Complex.exp 0‖ * (d : ℝ) ^ k * (|s x| * (zdInf x : ℝ) ^ k) with hv
  have hfc : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f x) := fun x =>
    (contDiff_zexp x).const_smul (s x)
  have hvs : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) → Summable (v k) := fun k _ =>
    ((hs.moment hW k).1.mul_left _)
  have hfv : ∀ (k : ℕ) (x : Fin d → ℤ) (p : Fin d → ℝ), (k : ℕ∞) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ k (f x) p‖ ≤ v k x := by
    intro k x p _
    have : f x = fun p => s x • zexp p x := rfl
    rw [this, iteratedFDeriv_const_smul_apply' ((contDiff_zexp x).contDiffAt.of_le
      (by exact_mod_cast le_top)), norm_smul, Real.norm_eq_abs]
    calc |s x| * ‖iteratedFDeriv ℝ k (fun p => zexp p x) p‖
        ≤ |s x| * (‖iteratedFDeriv ℝ k Complex.exp 0‖ * ((d : ℝ) * zdInf x) ^ k) := by
          gcongr; exact norm_iteratedFDeriv_zexp_le k x p
      _ = v k x := by simp only [hv]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hsym]
    exact contDiff_tsum hfc hvs hfv
  · intro i p
    simp only [zdSymbol, zdSeries, zexp_add_single]
  · intro p
    rw [hsym, iteratedFDeriv_tsum_apply hfc hvs hfv (by exact_mod_cast le_top)]
    have hsum := (hvs n le_top).hasSum
    refine (tsum_of_norm_bounded hsum fun x => hfv n x p le_top).trans ?_
    have hm := (hs.moment hW n).2
    have hc : 0 ≤ ‖iteratedFDeriv ℝ n Complex.exp 0‖ * (d : ℝ) ^ n := by positivity
    calc ∑' x, v n x = ‖iteratedFDeriv ℝ n Complex.exp 0‖ * (d : ℝ) ^ n *
          ∑' x, |s x| * (zdInf x : ℝ) ^ n := by
          simp only [hv]; rw [tsum_mul_left]
      _ ≤ ‖iteratedFDeriv ℝ n Complex.exp 0‖ * (d : ℝ) ^ n *
          (3 ^ d * C (n + 2 * d) * (W : ℝ) ^ n) := by gcongr
      _ = _ := by ring

/-! ## Lower bounds for the symbol -/

private theorem norm_smul_toLp_sq (W : ℝ) (p : Fin d → ℝ) :
    ‖W • WithLp.toLp 2 p‖ ^ 2 = W ^ 2 * sqNorm p := by
  rw [norm_smul, mul_pow, EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rfl

/-- Closeness at `D′ = 1` on the real part: `|Re ŝ(p) - ψ(Wp)| ≤ C_1 / W`. -/
private theorem InfKernel.abs_re_sub_le {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ}
    {W : ℕ} {s : (Fin d → ℤ) → ℝ} (hs : InfKernel ψ C W s) (p : Fin d → ℝ) (hp : p ∈ cubePi d) :
    |(zdSymbol s p).re - ψ ((W : ℝ) • WithLp.toLp 2 p)| ≤ C 1 / W := by
  have h := hs.close 1 p hp
  rw [pow_one] at h
  refine le_trans ?_ h
  have := Complex.abs_re_le_norm (zdSymbol s p - (ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ))
  simpa using this

private theorem InfKernel.summable {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ}
    {W : ℕ} {s : (Fin d → ℤ) → ℝ} (hW : 1 ≤ W) (hs : InfKernel ψ C W s) : Summable s := by
  have h := (hs.moment hW 0).1
  simp only [pow_zero, mul_one] at h
  exact h.of_abs

private theorem abs_cos_sub_le (v : ℝ) : |Real.cos v - (1 - v ^ 2 / 2)| ≤ 3 * v ^ 4 := by
  have h4 : |v| ^ 4 = v ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rcases le_or_gt |v| 1 with h | h
  · have := Real.cos_bound h
    rw [h4] at this
    nlinarith [pow_two_nonneg (v ^ 2)]
  · have hv2 : 1 ≤ v ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
    have hv4 : v ^ 2 ≤ v ^ 4 := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [Real.neg_one_le_cos v, Real.cos_le_one v]

private theorem abs_cos_compare_le (u a : ℝ) (ha : 0 < a) :
    |(1 - Real.cos u) - (1 - Real.cos (a * u)) / a ^ 2| ≤ 3 * (1 + a ^ 2) * u ^ 4 := by
  have e1 := abs_cos_sub_le u
  have e2 := abs_cos_sub_le (a * u)
  have ha2 : 0 < a ^ 2 := by positivity
  have hrw : (1 - Real.cos u) - (1 - Real.cos (a * u)) / a ^ 2 =
      -(Real.cos u - (1 - u ^ 2 / 2)) + (Real.cos (a * u) - (1 - (a * u) ^ 2 / 2)) / a ^ 2 := by
    field_simp; ring
  rw [hrw]
  have h3 : |(Real.cos (a * u) - (1 - (a * u) ^ 2 / 2)) / a ^ 2| ≤ 3 * a ^ 2 * u ^ 4 := by
    rw [abs_div, abs_of_pos ha2, div_le_iff₀ ha2]
    calc _ ≤ 3 * (a * u) ^ 4 := e2
      _ = _ := by ring
  calc _ ≤ |-(Real.cos u - (1 - u ^ 2 / 2))| +
        |(Real.cos (a * u) - (1 - (a * u) ^ 2 / 2)) / a ^ 2| := abs_add_le _ _
    _ ≤ 3 * u ^ 4 + 3 * a ^ 2 * u ^ 4 := by rw [abs_neg]; exact add_le_add e1 h3
    _ = _ := by ring

private theorem sq_dot_le (p : Fin d → ℝ) (x : Fin d → ℤ) :
    (∑ j, p j * (x j : ℝ)) ^ 2 ≤ d * sqNorm p * (zdInf x : ℝ) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p fun j => ((x j : ℤ) : ℝ)
  have hx : ∑ j, ((x j : ℤ) : ℝ) ^ 2 ≤ d * (zdInf x : ℝ) ^ 2 := by
    calc ∑ j, ((x j : ℤ) : ℝ) ^ 2 ≤ ∑ _j : Fin d, (zdInf x : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (natAbs_le_zdInf x j) 2
      _ = _ := by simp
  have hq : 0 ≤ sqNorm p := Finset.sum_nonneg fun j _ => sq_nonneg (p j)
  calc _ ≤ (∑ j, p j ^ 2) * ∑ j, ((x j : ℤ) : ℝ) ^ 2 := h
    _ ≤ sqNorm p * (d * (zdInf x : ℝ) ^ 2) := by
        gcongr
        exact le_of_eq rfl
    _ = _ := by ring

private theorem InfKernel.one_sub_re_eq {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ}
    {W : ℕ} {s : (Fin d → ℤ) → ℝ} (hW : 1 ≤ W) (hs : InfKernel ψ C W s) (p : Fin d → ℝ) :
    Summable (fun x => s x * (1 - Real.cos (∑ j, p j * (x j : ℝ)))) ∧
      1 - (zdSymbol s p).re = ∑' x, s x * (1 - Real.cos (∑ j, p j * (x j : ℝ))) := by
  have hsum := hs.summable hW
  have hc : Summable fun x => s x * Real.cos (∑ j, p j * (x j : ℝ)) :=
    hsum.abs.of_norm_bounded fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hz : Summable fun x => (s x : ℂ) * zexp p x :=
    (hsum.abs).of_norm_bounded fun x => by
      rw [norm_mul, norm_zexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hre : (zdSymbol s p).re = ∑' x, s x * Real.cos (∑ j, p j * (x j : ℝ)) := by
    unfold zdSymbol zdSeries
    rw [Complex.re_tsum hz]
    refine tsum_congr fun x => ?_
    rw [Complex.re_ofReal_mul]
    unfold zexp
    rw [Complex.exp_ofReal_mul_I_re]
  have e : (fun x => s x * (1 - Real.cos (∑ j, p j * (x j : ℝ)))) =
      fun x => s x - s x * Real.cos (∑ j, p j * (x j : ℝ)) := by
    funext x; ring
  refine ⟨e ▸ hsum.sub hc, ?_⟩
  rw [e, hsum.tsum_sub hc, hs.sum_one, hre]

/-- Comparison of `1 - Re ŝ` at `p` and at `a p` through the second-order Taylor expansion of
`cos`, with the fourth moment as error. -/
private theorem InfKernel.compare {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ}
    {W : ℕ} {s : (Fin d → ℤ) → ℝ} (hW : 1 ≤ W) (hs : InfKernel ψ C W s) (p : Fin d → ℝ)
    (a : ℝ) (ha : 0 < a) :
    (1 - (zdSymbol s (a • p)).re) / a ^ 2 -
        3 * (1 + a ^ 2) * ((d : ℝ) ^ 2 * sqNorm p ^ 2 * (3 ^ d * C (4 + 2 * d) * (W : ℝ) ^ 4)) ≤
      1 - (zdSymbol s p).re := by
  obtain ⟨h1s, h1⟩ := hs.one_sub_re_eq hW p
  obtain ⟨has, ha'⟩ := hs.one_sub_re_eq hW (a • p)
  have hdot : ∀ x : Fin d → ℤ, ∑ j, (a • p) j * (x j : ℝ) = a * ∑ j, p j * (x j : ℝ) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [hdot] at has ha'
  obtain ⟨hm, hmle⟩ := hs.moment hW 4
  set K : ℝ := 3 * (1 + a ^ 2) * ((d : ℝ) ^ 2 * sqNorm p ^ 2)
  have hK : 0 ≤ K := by positivity
  set T : (Fin d → ℤ) → ℝ := fun x => s x * (1 - Real.cos (∑ j, p j * (x j : ℝ))) -
    s x * (1 - Real.cos (a * ∑ j, p j * (x j : ℝ))) / a ^ 2
  have hT : Summable T := h1s.sub (has.div_const _)
  have hTeq : ∑' x, T x = (1 - (zdSymbol s p).re) - (1 - (zdSymbol s (a • p)).re) / a ^ 2 := by
    rw [h1, ha', ← tsum_div_const, ← h1s.tsum_sub (has.div_const _)]
  have hTlow : ∀ x, -(K * (|s x| * (zdInf x : ℝ) ^ 4)) ≤ T x := by
    intro x
    have hu := sq_dot_le p x
    have hc := abs_cos_compare_le (∑ j, p j * (x j : ℝ)) a ha
    have hu4 : (∑ j, p j * (x j : ℝ)) ^ 4 ≤ (d : ℝ) ^ 2 * sqNorm p ^ 2 * (zdInf x : ℝ) ^ 4 := by
      calc (∑ j, p j * (x j : ℝ)) ^ 4 = ((∑ j, p j * (x j : ℝ)) ^ 2) ^ 2 := by ring
        _ ≤ (d * sqNorm p * (zdInf x : ℝ) ^ 2) ^ 2 := by gcongr
        _ = _ := by ring
    have hT' : T x = s x * ((1 - Real.cos (∑ j, p j * (x j : ℝ))) -
        (1 - Real.cos (a * ∑ j, p j * (x j : ℝ))) / a ^ 2) := by
      simp only [T]; ring
    rw [hT']
    have := abs_mul (s x) ((1 - Real.cos (∑ j, p j * (x j : ℝ))) -
        (1 - Real.cos (a * ∑ j, p j * (x j : ℝ))) / a ^ 2)
    have hb : |s x * ((1 - Real.cos (∑ j, p j * (x j : ℝ))) -
        (1 - Real.cos (a * ∑ j, p j * (x j : ℝ))) / a ^ 2)| ≤ K * (|s x| * (zdInf x : ℝ) ^ 4) := by
      rw [this]
      calc _ ≤ |s x| * (3 * (1 + a ^ 2) * (∑ j, p j * (x j : ℝ)) ^ 4) := by gcongr
        _ ≤ |s x| * (3 * (1 + a ^ 2) * ((d : ℝ) ^ 2 * sqNorm p ^ 2 * (zdInf x : ℝ) ^ 4)) := by
            gcongr
        _ = _ := by simp only [K]; ring
    exact (abs_le.1 hb).1
  have hsum_low := (hm.mul_left K).neg.tsum_le_tsum hTlow hT
  rw [tsum_neg, tsum_mul_left, hTeq] at hsum_low
  have : K * ∑' x, |s x| * (zdInf x : ℝ) ^ 4 ≤ K * (3 ^ d * C (4 + 2 * d) * (W : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_left hmle hK
  have e : K * (3 ^ d * C (4 + 2 * d) * (W : ℝ) ^ 4) =
      3 * (1 + a ^ 2) * ((d : ℝ) ^ 2 * sqNorm p ^ 2 * (3 ^ d * C (4 + 2 * d) * (W : ℝ) ^ 4)) := by
    simp only [K]; ring
  linarith

private theorem ProfileShape.one_sub_ge {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {cψ : ℝ}
    (hψ : ProfileShape ψ cψ) (q : EuclideanSpace ℝ (Fin d)) :
    cψ * min (‖q‖ ^ 2) 1 ≤ 1 - ψ q := by
  have h := hψ.le_max q
  have hc := hψ.pos
  rcases le_total (‖q‖ ^ 2) 1 with hq | hq
  · rw [min_eq_left hq]
    rw [max_eq_left (by nlinarith)] at h
    linarith
  · rw [min_eq_right hq]
    rw [max_eq_right (by nlinarith)] at h
    linarith

/-- For `W ≥ W₀`, the symbol of an `InfKernel` is real on `[-π, π]^d` and satisfies
`1 - ŝ(p) ≥ c min(W²|p|², 1)` ([I, Assumption 1.2 (ii)] transferred to `ŝ`; the role of
[I, (1.31)]). -/
theorem one_sub_zdSymbol_ge :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ)
    (C : ℕ → ℝ), ∃ c W₀ : ℝ, 0 < c ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel ψ C W s → ∀ p ∈ cubePi d,
        (zdSymbol s p).im = 0 ∧ c * min ((W : ℝ) ^ 2 * sqNorm p) 1 ≤ 1 - (zdSymbol s p).re := by
  intro d ψ cψ hψ C
  have hcψ := hψ.pos
  set B : ℝ := (d : ℝ) ^ 2 * (3 ^ d * |C (4 + 2 * d)|) with hBdef
  have hB : 0 ≤ B := by positivity
  set ρ : ℝ := min 1 (cψ / (24 * B + 1)) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρB : 6 * B * ρ ≤ cψ / 4 := by
    have h := min_le_right 1 (cψ / (24 * B + 1))
    rw [← hρdef, le_div_iff₀ (by positivity)] at h
    nlinarith
  refine ⟨cψ * ρ / 2, max 1 (4 * |C 1| / (cψ * ρ)), by positivity, ?_⟩
  intro W hW s hs p hp
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hε : C 1 / W ≤ cψ * ρ / 4 := by
    have h2 : 4 * |C 1| / (cψ * ρ) ≤ W := le_trans (le_max_right _ _) hW
    rw [div_le_iff₀ (by positivity)] at h2
    rw [div_le_iff₀ hW0]
    nlinarith [le_abs_self (C 1)]
  refine ⟨zdSymbol_im s hs.symm (hs.summable hWn) p, ?_⟩
  have hprof : ∀ p' ∈ cubePi d, cψ * min ((W : ℝ) ^ 2 * sqNorm p') 1 - C 1 / W ≤
      1 - (zdSymbol s p').re := by
    intro p' hp'
    have h1 := hψ.one_sub_ge ((W : ℝ) • WithLp.toLp 2 p')
    rw [norm_smul_toLp_sq] at h1
    have h2 := (abs_le.1 (hs.abs_re_sub_le p' hp')).2
    linarith
  set q := sqNorm p with hqdef
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun j _ => sq_nonneg (p j)
  rcases le_or_gt ρ ((W : ℝ) ^ 2 * q) with hlarge | hsmall
  · have h := hprof p hp
    have hmin : ρ ≤ min ((W : ℝ) ^ 2 * q) 1 := le_min hlarge hρ1
    have hmin1 : min ((W : ℝ) ^ 2 * q) 1 ≤ 1 := min_le_right _ _
    rw [← hqdef] at h
    have e1 : cψ * ρ ≤ cψ * min ((W : ℝ) ^ 2 * q) 1 := mul_le_mul_of_nonneg_left hmin hcψ.le
    have e2 : cψ * ρ / 2 * min ((W : ℝ) ^ 2 * q) 1 ≤ cψ * ρ / 2 :=
      mul_le_of_le_one_right (by positivity) hmin1
    have e3 : 0 < cψ * ρ := by positivity
    linarith
  · have hX1 : (W : ℝ) ^ 2 * q ≤ 1 := by linarith
    rw [min_eq_left hX1]
    rcases eq_or_lt_of_le hq0 with hq | hq
    · rw [← hq, mul_zero, mul_zero]
      obtain ⟨-, h⟩ := hs.one_sub_re_eq hWn p
      rw [h]
      have : ∀ x : Fin d → ℤ, s x * (1 - Real.cos (∑ j, p j * (x j : ℝ))) = 0 := by
        intro x
        have hu := sq_dot_le p x
        rw [← hqdef, ← hq, mul_zero, zero_mul] at hu
        have : ∑ j, p j * (x j : ℝ) = 0 := by nlinarith [sq_nonneg (∑ j, p j * (x j : ℝ))]
        rw [this, Real.cos_zero, sub_self, mul_zero]
      simp [this]
    · set X : ℝ := (W : ℝ) ^ 2 * q with hX
      have hXpos : 0 < X := by positivity
      set a : ℝ := Real.sqrt (ρ / X) with ha
      have ha2 : a ^ 2 = ρ / X := Real.sq_sqrt (by positivity)
      have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
      have hap : a • p ∈ cubePi d := by
        intro j _
        have hj : (a * p j) ^ 2 ≤ 1 := by
          have h1 : (p j) ^ 2 ≤ q := by
            rw [hqdef, sqNorm]
            exact Finset.single_le_sum (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _)
              (Finset.mem_univ j)
          have h2 : a ^ 2 * q = ρ / (W : ℝ) ^ 2 := by
            rw [ha2, hX]; field_simp
          have h3 : ρ / (W : ℝ) ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith
          calc (a * p j) ^ 2 = a ^ 2 * p j ^ 2 := by ring
            _ ≤ a ^ 2 * q := by gcongr
            _ ≤ 1 := h2 ▸ h3
        have hj' : |a * p j| ≤ 1 := by
          rw [← sq_le_one_iff_abs_le_one]; exact hj
        have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
        simp only [Pi.smul_apply, smul_eq_mul, Set.mem_Icc]
        constructor <;> linarith [abs_le.1 hj']
      have hsq : sqNorm (a • p) = a ^ 2 * q := by
        simp only [sqNorm, Pi.smul_apply, smul_eq_mul, hqdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hΦa := hprof (a • p) hap
      have hXa : (W : ℝ) ^ 2 * sqNorm (a • p) = ρ := by
        rw [hsq, ha2, hX]; field_simp
      rw [hXa, min_eq_left hρ1] at hΦa
      have hcomp := hs.compare hWn p a ha0
      set Φa := 1 - (zdSymbol s (a • p)).re
      have h1 : 3 / 4 * cψ * X ≤ Φa / a ^ 2 := by
        rw [le_div_iff₀ (by positivity), ha2]
        have : 3 / 4 * cψ * X * (ρ / X) = 3 / 4 * cψ * ρ := by field_simp
        rw [this]; linarith
      have hR : 3 * (1 + a ^ 2) * ((d : ℝ) ^ 2 * q ^ 2 * (3 ^ d * C (4 + 2 * d) * (W : ℝ) ^ 4))
          ≤ cψ / 4 * X := by
        have hC : (d : ℝ) ^ 2 * q ^ 2 * (3 ^ d * C (4 + 2 * d) * (W : ℝ) ^ 4) ≤ B * X ^ 2 := by
          rw [hBdef, hX]
          have : C (4 + 2 * d) ≤ |C (4 + 2 * d)| := le_abs_self _
          have h0 : 0 ≤ (d : ℝ) ^ 2 * q ^ 2 * (3 ^ d * (W : ℝ) ^ 4) := by positivity
          nlinarith
        have h1a : 0 ≤ 3 * (1 + a ^ 2) := by positivity
        calc _ ≤ 3 * (1 + a ^ 2) * (B * X ^ 2) := mul_le_mul_of_nonneg_left hC h1a
          _ = 3 * B * X * X + 3 * B * X * (a ^ 2 * X) := by ring
          _ = 3 * B * X * X + 3 * B * X * ρ := by
              rw [ha2]; field_simp
          _ ≤ 3 * B * X * ρ + 3 * B * X * ρ := by
              gcongr
          _ = 6 * B * ρ * X := by ring
          _ ≤ cψ / 4 * X := by gcongr
      have hc : cψ * ρ / 2 * X ≤ cψ / 2 * X := by
        have : cψ * ρ / 2 ≤ cψ / 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hXpos.le
      linarith

/-- For `W ≥ W₀`, the symbol of an `InfKernel` satisfies `Re ŝ ≥ -1 + c′/2` on `[-π, π]^d`
(from the lower bound `ψ ≥ -1 + c′` of (H2)). -/
theorem zdSymbol_ge :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (c' : ℝ) (hψ : SymbolBound ψ c')
    (C : ℕ → ℝ), ∃ W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel ψ C W s → ∀ p ∈ cubePi d, -1 + c' / 2 ≤ (zdSymbol s p).re := by
  intro d ψ c' hψ C
  refine ⟨max 1 (2 * |C 1| / c'), fun W hW s hs p hp => ?_⟩
  have hc' := hψ.pos
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have h2 : 2 * |C 1| / c' ≤ W := le_trans (le_max_right _ _) hW
  have hε : C 1 / W ≤ c' / 2 := by
    rw [div_le_iff₀ hW0]
    rw [div_le_iff₀ hc'] at h2
    nlinarith [le_abs_self (C 1)]
  have h1 := hs.abs_re_sub_le p hp
  have h3 := (hψ.range ((W : ℝ) • WithLp.toLp 2 p)).1
  have := (abs_le.1 h1).1
  linarith

section Witness

end Witness

end RBM8D
