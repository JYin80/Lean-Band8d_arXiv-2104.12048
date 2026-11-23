module

public import RBM8D.MainDefs
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import RBM8D.Basic.Lattice
public import RBM8D.Basic.Semicircle
public import RBM8D.Prob.StochDom
public import RBM8D.Kernel.Fourier

@[expose] public section

/-!
# The profile, `f_{W,L}`, `Z_{W,L}` and `S`

[I, Asm 1.1–1.2], (1.5)–(1.6): the profile `ψ` with `f ≥ 0` and torus symmetry in the regime of the
model, the kernel `f_{W,L}`, its normaliser and the variance matrix.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

namespace RBM8D

section Profile

variable {d : ℕ}

/-- A point of `ℤ^d` as a point of `ℝ^d`. -/
def intVec (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => (n i : ℝ)

/-- The density `φ(y) = (2π)^{−d} ∫ ψ(q) e^{i q·y} dq`, so that `ψ(p) = ∫ φ(y) e^{−i p·y} dy`. -/
def profPhi (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (profInt ψ 1 y).re

end Profile

/-- The integral of [I, (1.6)] in Mathlib's convention: `𝓕⁻ g (y) = ∫ e^{2πi⟨w,y⟩} g(w) dw`
applied to `g(w) = ψ(2πW w)`; it holds for every real `W` and every `d`. -/
theorem profInt_eq_fourierInv :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (y : EuclideanSpace ℝ (Fin d)),
    profInt ψ W y = 𝓕⁻ (fun w : EuclideanSpace ℝ (Fin d) => (ψ ((2 * Real.pi * W) • w) : ℂ)) y := by
  intro d ψ W y
  rw [Real.fourierInv_eq']
  have hpt : ∀ w : EuclideanSpace ℝ (Fin d),
      (fun p : EuclideanSpace ℝ (Fin d) => (ψ (W • p) : ℂ) * cexp (I * (inner ℝ p y : ℝ)))
        ((2 * Real.pi) • w) =
      cexp (((2 * Real.pi * (inner ℝ w y : ℝ) : ℝ) : ℂ) * I) • (ψ ((2 * Real.pi * W) • w) : ℂ) := by
    intro w
    simp only [smul_eq_mul, real_inner_smul_left, smul_smul]
    rw [mul_comm W, mul_comm _ (cexp _), mul_comm I]
  simp_rw [← hpt]
  rw [Measure.integral_comp_smul volume
    (fun p : EuclideanSpace ℝ (Fin d) => (ψ (W • p) : ℂ) * cexp (I * (inner ℝ p y : ℝ))) (2 * Real.pi),
    finrank_euclideanSpace_fin]
  unfold profInt
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [abs_of_pos (inv_pos.mpr (pow_pos hpi d)), Complex.real_smul]
  push_cast
  rfl

/-- Scaling: `(2π)^{−d} ∫ ψ(Wp) e^{i p·y} dp = W^{−d} φ(y/W)` for `W > 0`, where
`φ(y) = (2π)^{−d} ∫ ψ(q) e^{i q·y} dq` (complex form). -/
theorem profInt_scale :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (hW : 0 < W)
    (y : EuclideanSpace ℝ (Fin d)),
    profInt ψ W y = ((W : ℂ) ^ d)⁻¹ * profInt ψ 1 (W⁻¹ • y) := by
  intro d ψ W hW y
  unfold profInt
  have hpt : ∀ p : EuclideanSpace ℝ (Fin d),
      (fun q : EuclideanSpace ℝ (Fin d) =>
        (ψ ((1 : ℝ) • q) : ℂ) * cexp (I * (inner ℝ q (W⁻¹ • y) : ℝ))) (W • p) =
      (ψ (W • p) : ℂ) * cexp (I * (inner ℝ p y : ℝ)) := by
    intro p
    simp only [one_smul, real_inner_smul_left, real_inner_smul_right]
    rw [inv_mul_cancel_left₀ hW.ne']
  simp_rw [← hpt]
  rw [Measure.integral_comp_smul volume
    (fun q : EuclideanSpace ℝ (Fin d) =>
        (ψ ((1 : ℝ) • q) : ℂ) * cexp (I * (inner ℝ q (W⁻¹ • y) : ℝ))) W,
    finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hW d)), Complex.real_smul]
  push_cast
  ring

/-- For a symmetric `ψ` the integral `(2π)^{−d} ∫ ψ(Wp) e^{i p·y} dp` of [I, (1.6)] is real. -/
theorem profInt_im :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (hψ : ∀ p, ψ (-p) = ψ p) (W : ℝ)
    (y : EuclideanSpace ℝ (Fin d)), (profInt ψ W y).im = 0 := by
  intro d ψ hψ W y
  unfold profInt
  set J : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun p => (ψ (W • p) : ℂ) * cexp (I * (inner ℝ p y : ℝ)) with hJ
  have hconj : ∀ p, (starRingEnd ℂ) (J p) = J (-p) := by
    intro p
    simp only [hJ, map_mul, Complex.conj_ofReal, smul_neg, hψ, inner_neg_left, Complex.ofReal_neg,
      mul_neg, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring_nf
  have h1 : (starRingEnd ℂ) (∫ p, J p) = ∫ p, J p := by
    rw [← integral_conj]
    simp_rw [hconj]
    exact integral_neg_eq_self J volume
  have h2 : (∫ p, J p).im = 0 := Complex.conj_eq_iff_im.mp h1
  have h3 : ((2 * Real.pi : ℂ) ^ d)⁻¹ = ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h3, Complex.im_ofReal_mul, h2, mul_zero]

/-- Fourier inversion in the convention of [I, (1.6)]: `φ(y) = (2π)^{−d} ∫ ψ(q) e^{i q·y} dq`
is integrable and `ψ(p) = ∫ φ(y) e^{−i p·y} dy`. -/
theorem fourier_profInt :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)),
    Integrable (profInt ψ 1) ∧ ∀ p : EuclideanSpace ℝ (Fin d),
      ∫ y, profInt ψ 1 y * cexp (-(I * (inner ℝ p y : ℝ))) = (ψ p : ℂ) := by
  intro d ψ
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin d)) (2 * Real.pi)
      h2pi).toContinuousLinearEquiv
  let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
      (SchwartzMap.postcompCLM (Complex.ofRealCLM) ψ)
  have hG : ∀ w, G w = (ψ ((2 * Real.pi) • w) : ℂ) := fun w => rfl
  have hprof : profInt ψ 1 = 𝓕⁻ (G : EuclideanSpace ℝ (Fin d) → ℂ) := by
    funext y
    rw [profInt_eq_fourierInv d ψ 1 y]
    simp only [mul_one]
    congr 1
  rw [hprof]
  refine ⟨?_, fun p => ?_⟩
  · rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ G).integrable
  · have hinv : 𝓕 (𝓕⁻ (G : EuclideanSpace ℝ (Fin d) → ℂ)) = (G : EuclideanSpace ℝ (Fin d) → ℂ) := by
      rw [← SchwartzMap.fourierInv_coe, ← SchwartzMap.fourier_coe,
        FourierInvPair.fourier_fourierInv_eq]
    have h1 := congrFun hinv ((2 * Real.pi)⁻¹ • p)
    rw [Real.fourier_eq', hG, smul_smul, mul_inv_cancel₀ h2pi, one_smul] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm, real_inner_smul_right, real_inner_comm y p]
    congr 2
    push_cast
    field_simp

/-- `Σ_x f_{W,L}(x) = 1` whenever the normalisation `Z_{W,L}` of [I, (1.6)] is nonzero. -/
theorem sum_fWL :
  ∀ (d L : ℕ) [NeZero L] (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) (hZ : ZWL ψ W L ≠ 0),
    ∑ x : Zd d L, fWL ψ W L x = 1 := by
  intro d L _ ψ W hZ
  simp only [fWL, ← Finset.mul_sum]
  exact inv_mul_cancel₀ hZ

section Witness

end Witness

end RBM8D
