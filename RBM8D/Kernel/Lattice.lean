import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import RBM8D.Basic.Lattice
import RBM8D.Basic.Semicircle
import RBM8D.Prob.StochDom
import RBM8D.Kernel.Fourier
import RBM8D.Kernel.Propagator
import RBM8D.Kernel.Profile
import RBM8D.Kernel.Circulant

/-!
# Kernels on `ℤ^d`

The ℓ^∞ norm, plane waves, Fourier series and coefficients on the cube `[-π, π]^d`, and the kernels `Θ_{ℤ^d}`, `Θ_∞`, `S^±_∞` defined by their symbols ([I, (7.4)–(7.5)]).
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d : ℕ}

/-- The `ℓ^∞` norm `|x| = max_i |x_i|` on `ℤ^d`. -/
def zdInf (x : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-- The plane wave `e^{i p·x}`, `p ∈ ℝ^d`, `x ∈ ℤ^d`. -/
def zexp (p : Fin d → ℝ) (x : Fin d → ℤ) : ℂ :=
  Complex.exp (((∑ i, p i * (x i : ℝ) : ℝ) : ℂ) * I)

/-- The cube `[-π, π]^d`. -/
def cubePi (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Icc (-Real.pi) Real.pi

/-- The box `⟦-K, K⟧^d` of `ℤ^d`. -/
def boxZ (d K : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ)) K

/-- The kernel on `ℤ^d` with symbol `F`: `(2π)^{-d} ∫_{[-π,π]^d} F(p) e^{-ip·x} dp`. -/
def latticeFourier (F : (Fin d → ℝ) → ℂ) (x : Fin d → ℤ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ d)⁻¹ * ∫ p in cubePi d, F p * zexp p (-x)

/-- The Fourier series `K̂(p) = Σ_x K(x) e^{ip·x}` of a kernel on `ℤ^d`. -/
def zdSeries (K : (Fin d → ℤ) → ℂ) (p : Fin d → ℝ) : ℂ := ∑' x, K x * zexp p x

/-- The symbol `ŝ(p) = Σ_x s(x) e^{ip·x}` of a real kernel on `ℤ^d`. -/
def zdSymbol (s : (Fin d → ℤ) → ℝ) (p : Fin d → ℝ) : ℂ := zdSeries (fun x => (s x : ℂ)) p

/-- The kernel on `ℤ^d` whose symbol is `F(ŝ)`. -/
def zdKernel (F : ℂ → ℂ) (s : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℂ :=
  latticeFourier (fun p => F (zdSymbol s p)) x

/-- The propagator on `ℤ^d` at `|m|² = a`: the kernel with symbol `a ŝ / (1 - a ŝ)`. -/
def ThetaZd (a : ℝ) (s : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℂ :=
  zdKernel (fun t => (a : ℂ) * t / (1 - (a : ℂ) * t)) s x

/-- `Θ_∞` of [I, (7.5)], as the absolutely convergent integral
`(2π)^{-d} ∫_{[-π,π]^d} ŝ(p)/(1 - ŝ(p)) e^{-ip·x} dp` (`d ≥ 3`); it does not depend on `E`. -/
def ThetaInf (s : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℂ := ThetaZd 1 s x

/-- `S^+_∞ = m² S_∞ (1 - m² S_∞)⁻¹` of [I, (7.4)], as the kernel with symbol
`m² ŝ / (1 - m² ŝ)`; [I, (7.4)] takes `m = m(E)`. -/
def SplusInf (m : ℂ) (s : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℂ :=
  zdKernel (fun t => m ^ 2 * t / (1 - m ^ 2 * t)) s x

/-- `S^-_∞ = conj S^+_∞` of [I, (7.4)]. -/
def SminusInf (m : ℂ) (s : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℂ := conj (SplusInf m s x)

/-- The `ℓ^∞` norm on `ℤ^d` satisfies the triangle inequality. -/
theorem zdInf_add_le :
  ∀ {d : ℕ} (x y : Fin d → ℤ), zdInf (x + y) ≤ zdInf x + zdInf y := by
  intro d x y
  refine Finset.sup_le fun i _ => ?_
  calc ((x + y) i).natAbs = (x i + y i).natAbs := rfl
    _ ≤ (x i).natAbs + (y i).natAbs := Int.natAbs_add_le _ _
    _ ≤ zdInf x + zdInf y :=
      add_le_add (Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i))
        (Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ i))

/-- The `ℓ^∞` norm on `ℤ^d` is symmetric. -/
theorem zdInf_neg :
  ∀ {d : ℕ} (x : Fin d → ℤ), zdInf (-x) = zdInf x := by
  intro d x
  simp [zdInf]

/-- Plane waves have modulus one. -/
theorem norm_zexp :
  ∀ {d : ℕ} (p : Fin d → ℝ) (x : Fin d → ℤ), ‖zexp p x‖ = 1 := by
  intro d p x
  exact Complex.norm_exp_ofReal_mul_I _

/-- Plane waves are additive in the space variable. -/
theorem zexp_add :
  ∀ {d : ℕ} (p : Fin d → ℝ) (x y : Fin d → ℤ), zexp p (x + y) = zexp p x * zexp p y := by
  intro d p x y
  unfold zexp
  rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_add]

private theorem zexp_eq_prod (p : Fin d → ℝ) (k : Fin d → ℤ) :
    zexp p k = ∏ i, Complex.exp (((p i * (k i : ℝ) : ℝ) : ℂ) * I) := by
  unfold zexp
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]

private theorem integral_exp_int (k : ℤ) :
    ∫ t in Set.Icc (-Real.pi) Real.pi, Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * I) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  by_cases hk : k = 0
  · subst hk
    simp
    ring
  · simp only [hk, ↓reduceIte]
    have hc : ((k : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    have h : ∀ t : ℝ, Complex.exp (((t * (k : ℝ) : ℝ) : ℂ) * I) =
        Complex.exp (((k : ℂ) * I) * (t : ℂ)) := fun t => by
      congr 1
      push_cast
      ring
    simp_rw [h]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (((k : ℂ) * I) * ((Real.pi : ℝ) : ℂ)) =
        Complex.exp (((k : ℂ) * I) * ((-Real.pi : ℝ) : ℂ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨k, ?_⟩
      push_cast
      ring
    rw [h1, sub_self, zero_div]

private theorem volume_cubePi : volume (cubePi d) = ENNReal.ofReal ((2 * Real.pi) ^ d) := by
  have : cubePi d = Set.Icc (fun _ : Fin d => -Real.pi) (fun _ => Real.pi) := by
    unfold cubePi
    rw [← Set.pi_univ_Icc]
  rw [this, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity)]

private theorem integral_cubePi_zexp (k : Fin d → ℤ) :
    ∫ p in cubePi d, zexp p k = if k = 0 then (((2 * Real.pi) ^ d : ℝ) : ℂ) else 0 := by
  have hmeas : (volume : Measure (Fin d → ℝ)).restrict (cubePi d) =
      Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Set.Icc (-Real.pi) Real.pi) := by
    unfold cubePi
    rw [volume_pi, Measure.restrict_pi_pi]
  simp_rw [zexp_eq_prod]
  rw [hmeas, integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => Complex.exp (((t * (k i : ℝ) : ℝ) : ℂ) * I))]
  simp_rw [integral_exp_int]
  by_cases hk : k = 0
  · subst hk
    simp
  · obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (funext h)
    simp only [hk, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- Orthogonality on `[-π, π]^d`: `(2π)^{-d} ∫ e^{ip·y} e^{-ip·x} dp = δ_{xy}`. -/
theorem latticeFourier_zexp :
  ∀ {d : ℕ} (x y : Fin d → ℤ), latticeFourier (fun p => zexp p y) x = if x = y then 1 else 0 := by
  intro d x y
  unfold latticeFourier
  simp_rw [← zexp_add]
  rw [integral_cubePi_zexp]
  have hxy : y + -x = 0 ↔ x = y := by
    rw [add_neg_eq_zero]
    exact eq_comm
  have hne : ((2 * Real.pi : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.two_pi_pos.ne')
  by_cases h : x = y
  · subst h
    simp only [add_neg_cancel, ↓reduceIte]
    push_cast
    exact inv_mul_cancel₀ hne
  · have h2 : ¬ y + -x = 0 := fun h' => h (hxy.mp h')
    simp only [h2, h, ↓reduceIte, mul_zero]

private theorem continuous_zexp_left (k : Fin d → ℤ) : Continuous fun p : Fin d → ℝ => zexp p k := by
  unfold zexp
  fun_prop

private theorem isCompact_cubePi : IsCompact (cubePi d) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem integrableOn_cubePi_zexp (c : ℂ) (k : Fin d → ℤ) :
    Integrable (fun p : Fin d → ℝ => c * zexp p k) (volume.restrict (cubePi d)) := by
  have hc : Continuous fun p : Fin d → ℝ => c * zexp p k :=
    continuous_const.mul (continuous_zexp_left k)
  exact hc.continuousOn.integrableOn_compact isCompact_cubePi

private theorem zexp_neg (p : Fin d → ℝ) (x : Fin d → ℤ) : zexp p (-x) = conj (zexp p x) := by
  unfold zexp
  rw [← Complex.exp_conj]
  congr 1
  simp [Finset.sum_neg_distrib]

/-- Fourier inversion on `ℤ^d` for a summable kernel. -/
theorem latticeFourier_zdSeries :
  ∀ {d : ℕ} (K : (Fin d → ℤ) → ℂ) (hK : Summable fun x => ‖K x‖) (x : Fin d → ℤ),
    latticeFourier (zdSeries K) x = K x := by
  intro d K hK x
  have hint : ∀ y : Fin d → ℤ,
      Integrable (fun p : Fin d → ℝ => K y * zexp p (y + -x)) (volume.restrict (cubePi d)) :=
    fun y => integrableOn_cubePi_zexp _ _
  have hnorm : ∀ y : Fin d → ℤ,
      ∫ p in cubePi d, ‖K y * zexp p (y + -x)‖ = ‖K y‖ * (2 * Real.pi) ^ d := by
    intro y
    simp only [norm_mul, norm_zexp, mul_one]
    rw [setIntegral_const, Measure.real, volume_cubePi, ENNReal.toReal_ofReal (by positivity)]
    simp [mul_comm]
  have hsum : Summable fun y : Fin d → ℤ => ∫ p in cubePi d, ‖K y * zexp p (y + -x)‖ := by
    simp_rw [hnorm]
    exact hK.mul_right _
  have h := integral_tsum_of_summable_integral_norm hint hsum
  have hfun : ∀ p : Fin d → ℝ, zdSeries K p * zexp p (-x) = ∑' y, K y * zexp p (y + -x) := by
    intro p
    unfold zdSeries
    rw [← tsum_mul_right]
    refine tsum_congr fun y => ?_
    rw [zexp_add, mul_assoc]
  unfold latticeFourier
  simp_rw [hfun]
  rw [← h]
  have hy : ∀ y : Fin d → ℤ, ∫ p in cubePi d, K y * zexp p (y + -x) =
      if y = x then K y * (((2 * Real.pi) ^ d : ℝ) : ℂ) else 0 := by
    intro y
    rw [integral_const_mul, integral_cubePi_zexp]
    by_cases hyx : y = x
    · subst hyx
      simp
    · have : ¬ y + -x = 0 := fun h' => hyx (add_neg_eq_zero.mp h')
      simp [this, hyx]
  simp_rw [hy]
  rw [tsum_ite_eq]
  have hne : ((2 * Real.pi : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.two_pi_pos.ne')
  push_cast
  field_simp

/-- The symbol of a symmetric real kernel on `ℤ^d` is real. -/
theorem zdSymbol_im :
  ∀ {d : ℕ} (s : (Fin d → ℤ) → ℝ) (hs : ∀ x, s (-x) = s x) (hsum : Summable s)
    (p : Fin d → ℝ), (zdSymbol s p).im = 0 := by
  intro d s hs hsum p
  have h : conj (zdSymbol s p) = zdSymbol s p := by
    unfold zdSymbol zdSeries
    have h1 : conj (∑' x, (s x : ℂ) * zexp p x) = ∑' x, conj ((s x : ℂ) * zexp p x) :=
      tsum_star
    rw [h1]
    rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq (fun x => (s x : ℂ) * zexp p x)]
    refine tsum_congr fun x => ?_
    simp only [Equiv.neg_apply, map_mul, Complex.conj_ofReal, zexp_neg, hs]
  exact Complex.conj_eq_iff_im.mp h

section Witness

end Witness

end RBM8D
