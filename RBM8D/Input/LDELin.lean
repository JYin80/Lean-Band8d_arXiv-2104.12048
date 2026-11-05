import RBM8D.Prob.Model
import RBM8D.Prob.StochDom
import RBM8D.Prob.Partial
import RBM8D.Basic.Minor
import RBM8D.Basic.Domain
import RBM8D.Basic.Semicircle
import RBM8D.Profile.Basic
import RBM8D.Prob.Stein
import RBM8D.Prob.LinearForm

/-!
# Large deviation bounds for linear forms and diagonal entries

Tail bounds, for a fixed finite index set, for the row sum `Σ_{k≠x} h_{xk} c_k` with coefficients
independent of row `x`, and for the diagonal entry `h_{xx}` of the Gaussian model of
[I, Assumption 1.1].
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

/-! ## Moments of a centred real Gaussian -/

section Moments

/-- Every polynomial is integrable against a real Gaussian. -/
private theorem ldeLin_integrable_pow (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Integrability against a centred Gaussian, transferred to the product with its density. -/
private theorem ldeLin_integrable_mul_pdf {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

/-- The recursion `E[X^{2p+2}] = (2p+1) v E[X^{2p}]` for `X ~ N(0, v)`. -/
private theorem ldeLin_integral_pow_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := ldeLin_integrable_mul_pdf hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((ldeLin_integrable_pow v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    ldeLin_integrable_mul_pdf hv
      ((ldeLin_integrable_pow v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    ldeLin_integrable_mul_pdf hv (ldeLin_integrable_pow v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- The double factorial `(2p-1)!! = ∏_{i<p} (2i+1)`, the `2p`-th moment of a standard
Gaussian. -/
private def ldeLin_dfac (p : ℕ) : ℝ := ∏ i ∈ Finset.range p, (2 * (i : ℝ) + 1)

/-- The even moments of a centred real Gaussian: `E[X^{2p}] = (2p-1)!! v^p`. -/
private theorem ldeLin_integral_pow (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) = ldeLin_dfac p * (v : ℝ) ^ p := by
  induction p with
  | zero => simp [ldeLin_dfac]
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 2 from by ring, ldeLin_integral_pow_succ, ih]
    simp only [ldeLin_dfac, Finset.prod_range_succ] at *
    ring

end Moments


/-- The pointwise bound `(x² + y²)^p ≤ 2^p (x^{2p} + y^{2p})`. -/
private theorem ldeLin_sq_add_sq_pow_le' (x y : ℝ) (p : ℕ) :
    (x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by
  have hx0 : 0 ≤ x ^ 2 := by positivity
  have hy0 : 0 ≤ y ^ 2 := by positivity
  have hmax : x ^ 2 + y ^ 2 ≤ 2 * max (x ^ 2) (y ^ 2) := by
    rcases le_total (x ^ 2) (y ^ 2) with h | h
    · simp [max_eq_right h]; linarith
    · simp [max_eq_left h]; linarith
  have h1 : (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p :=
    pow_le_pow_left₀ (by positivity) hmax p
  have h3 : max (x ^ 2) (y ^ 2) ^ p ≤ (x ^ 2) ^ p + (y ^ 2) ^ p := by
    rcases le_total (x ^ 2) (y ^ 2) with h | h
    · rw [max_eq_right h]
      have : (0 : ℝ) ≤ (x ^ 2) ^ p := by positivity
      linarith
    · rw [max_eq_left h]
      have : (0 : ℝ) ≤ (y ^ 2) ^ p := by positivity
      linarith
  calc (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p := h1
    _ = 2 ^ p * max (x ^ 2) (y ^ 2) ^ p := by rw [mul_pow]
    _ ≤ 2 ^ p * ((x ^ 2) ^ p + (y ^ 2) ^ p) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by rw [← pow_mul, ← pow_mul]

/-! ## Moments of a linear form in independent Gaussians -/

section LinearForm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : Type*} {X : κ → Ω → ℝ} {v : κ → ℝ≥0}
  (hmeas : ∀ i, Measurable (X i)) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
  (hindep : iIndepFun X P)
include hmeas hlaw hindep

/-- The law of the linear form `∑ a_i X_i` of an independent centred Gaussian family. -/
private theorem ldeLin_map_lin (a : κ → ℝ) (s : Finset κ) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω)
      = gaussianReal 0 (∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
  classical
  exact map_sum_const_mul_of_indep hmeas hlaw hindep a s

/-- All even moments of a linear form exist. -/
private theorem ldeLin_integrable_pow_lin (a : κ → ℝ) (s : Finset κ) (p : ℕ) :
    Integrable (fun ω => (∑ i ∈ s, a i * X i ω) ^ (2 * p)) P := by
  have hm : Measurable fun ω => ∑ i ∈ s, a i * X i ω :=
    Finset.measurable_sum _ fun i _ => (hmeas i).const_mul _
  have h := ldeLin_integrable_pow (∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) (2 * p)
  rw [← ldeLin_map_lin hmeas hlaw hindep a s] at h
  exact (integrable_map_measure ((measurable_id.pow_const (2 * p)).aestronglyMeasurable)
    hm.aemeasurable).1 h

/-- The even moments of a linear form: `E[(∑ a_i X_i)^{2p}] = (2p-1)!! (∑ a_i² v_i)^p`. -/
private theorem ldeLin_integral_pow_lin (a : κ → ℝ) (s : Finset κ) (p : ℕ) :
    ∫ ω, (∑ i ∈ s, a i * X i ω) ^ (2 * p) ∂P
      = ldeLin_dfac p * (∑ i ∈ s, a i ^ 2 * (v i : ℝ)) ^ p := by
  have hm : Measurable fun ω => ∑ i ∈ s, a i * X i ω :=
    Finset.measurable_sum _ fun i _ => (hmeas i).const_mul _
  have h := integral_map (μ := P) (φ := fun ω => ∑ i ∈ s, a i * X i ω)
    (f := fun y : ℝ => y ^ (2 * p)) hm.aemeasurable
    ((measurable_id.pow_const (2 * p)).aestronglyMeasurable)
  rw [ldeLin_map_lin hmeas hlaw hindep a s] at h
  rw [← h, ldeLin_integral_pow]
  push_cast
  rfl

/-- The modulus `(Y² + Y'²)^p` of a pair of linear forms is integrable. -/
private theorem ldeLin_integrable_sq_add_sq_pow (a b : κ → ℝ) (s : Finset κ) (p : ℕ) :
    Integrable (fun ω => ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p) P := by
  have hia := ldeLin_integrable_pow_lin hmeas hlaw hindep a s p
  have hib := ldeLin_integrable_pow_lin hmeas hlaw hindep b s p
  have hma : Measurable fun ω => ∑ i ∈ s, a i * X i ω :=
    Finset.measurable_sum _ fun i _ => (hmeas i).const_mul _
  have hmb : Measurable fun ω => ∑ i ∈ s, b i * X i ω :=
    Finset.measurable_sum _ fun i _ => (hmeas i).const_mul _
  refine ((hia.add hib).const_mul (2 ^ p)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((hma.pow_const 2).add (hmb.pow_const 2)).pow_const p).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact ldeLin_sq_add_sq_pow_le' _ _ p

/-- The moment bound for the modulus of a complex linear form with real part `∑ a_i X_i` and
imaginary part `∑ b_i X_i`: `E[(Y² + Y'²)^p] ≤ 2^p (2p-1)!! (V_a^p + V_b^p)`. -/
private theorem ldeLin_integral_sq_add_sq_pow_le (a b : κ → ℝ) (s : Finset κ) (p : ℕ) :
    ∫ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p ∂P
      ≤ 2 ^ p * (ldeLin_dfac p * ((∑ i ∈ s, a i ^ 2 * (v i : ℝ)) ^ p
        + (∑ i ∈ s, b i ^ 2 * (v i : ℝ)) ^ p)) := by
  have hia := ldeLin_integrable_pow_lin hmeas hlaw hindep a s p
  have hib := ldeLin_integrable_pow_lin hmeas hlaw hindep b s p
  have hint : Integrable (fun ω => 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p)
      + (∑ i ∈ s, b i * X i ω) ^ (2 * p))) P := (hia.add hib).const_mul _
  have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hint
    (Filter.Eventually.of_forall fun ω => ldeLin_sq_add_sq_pow_le' _ _ p)
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add hia hib, ldeLin_integral_pow_lin hmeas hlaw hindep,
    ldeLin_integral_pow_lin hmeas hlaw hindep]
  ring

end LinearForm


/-! ## The row of `H(ω)` as a linear form in independent coordinates -/

section Row

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The real coordinate of `Re h_{xk}` (`b = true`) or `Im h_{xk}` (`b = false`), `k ≠ x`. -/
private def ldeLin_co (x : ι) (k : {a : ι // a ≠ x}) (b : Bool) : Coord ι :=
  if h : idxKey ι x < idxKey ι k.1 then .inr (⟨(x, k.1), h⟩, b)
  else .inr (⟨(k.1, x), lt_of_le_of_ne (not_lt.1 h) fun e => k.2 (idxKey_injective e)⟩, b)

/-- The sign of the imaginary part of `h_{xk}` in the coordinates `ldeLin_co`. -/
private def ldeLin_eps (x : ι) (k : {a : ι // a ≠ x}) : ℝ :=
  if idxKey ι x < idxKey ι k.1 then 1 else -1

omit [DecidableEq ι] in
private theorem ldeLin_eps_sq (x : ι) (k : {a : ι // a ≠ x}) : ldeLin_eps x k ^ 2 = 1 := by
  unfold ldeLin_eps; split_ifs <;> norm_num

omit [DecidableEq ι] in
private theorem ldeLin_co_inj (x : ι) :
    Function.Injective fun p : {a : ι // a ≠ x} × Bool => ldeLin_co x p.1 p.2 := by
  rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨k', hk'⟩, b'⟩ h
  simp only [ldeLin_co] at h
  split_ifs at h with h1 h2 h2 <;>
    simp only [Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
  · obtain ⟨⟨-, rfl⟩, rfl⟩ := h; rfl
  · obtain ⟨⟨rfl, -⟩, -⟩ := h; exact absurd rfl hk'
  · obtain ⟨⟨rfl, -⟩, -⟩ := h; exact absurd rfl hk
  · obtain ⟨⟨rfl, -⟩, rfl⟩ := h; rfl

private theorem ldeLin_co_mem (x : ι) (k : {a : ι // a ≠ x}) (b : Bool) :
    ldeLin_co x k b ∈ rowCoords x := by
  simp only [rowCoords, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨k.1, ?_⟩
  simp only [ldeLin_co, entryCoords]
  split_ifs <;> simp

omit [DecidableEq ι] in
/-- The entry `h_{xk}` in the coordinates `ldeLin_co`. -/
private theorem ldeLin_hmat (x : ι) (k : {a : ι // a ≠ x}) (ω : Sample ι) :
    hmat ω x k.1 = (ω (ldeLin_co x k true) : ℂ)
      + I * ((ldeLin_eps x k * ω (ldeLin_co x k false) : ℝ) : ℂ) := by
  simp only [ldeLin_co, ldeLin_eps, hmat, Matrix.of_apply]
  split_ifs with h1 h2
  · simp
  · simp [sub_eq_add_neg]
  · exact absurd (lt_of_le_of_ne (not_lt.1 h1) fun e => k.2 (idxKey_injective e)) h2

/-- The entries `h_{xk}` of row `x` read only the coordinates of row `x`. -/
private theorem ldeLin_hmat_piecewise (x : ι) (ω η : Sample ι) (k : {a : ι // a ≠ x}) :
    hmat ((rowCoords x).piecewise η ω) x k.1 = hmat η x k.1 := by
  rw [ldeLin_hmat, ldeLin_hmat,
    Finset.piecewise_eq_of_mem _ _ _ (ldeLin_co_mem x k true),
    Finset.piecewise_eq_of_mem _ _ _ (ldeLin_co_mem x k false)]

omit [DecidableEq ι] in
/-- The variance of the coordinates `ldeLin_co x k b` is `s_{xk} / 2`. -/
private theorem ldeLin_var (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ a b, 0 ≤ S a b) (x : ι)
    (k : {a : ι // a ≠ x}) (b : Bool) : (coordVar S (ldeLin_co x k b) : ℝ) = S x k.1 / 2 := by
  simp only [ldeLin_co]
  split_ifs
  · simp only [coordVar]
    exact Real.coe_toNNReal _ (by have := hnn x k.1; positivity)
  · simp only [coordVar]
    rw [Real.coe_toNNReal _ (by have := hnn k.1 x; positivity), hS.apply x k.1]

omit [DecidableEq ι] in
private theorem ldeLin_measurable_hmat (x : ι) (k : {a : ι // a ≠ x}) :
    Measurable fun ω : Sample ι => hmat ω x k.1 := by
  classical
  have h : (fun ω : Sample ι => hmat ω x k.1) = fun ω =>
      (ω (ldeLin_co x k true) : ℂ) + I * ((ldeLin_eps x k * ω (ldeLin_co x k false) : ℝ) : ℂ) :=
    funext (ldeLin_hmat x k)
  rw [h]
  have h1 : Measurable fun ω : Sample ι => ω (ldeLin_co x k true) := measurable_pi_apply _
  have h2 : Measurable fun ω : Sample ι => ω (ldeLin_co x k false) := measurable_pi_apply _
  exact (Complex.measurable_ofReal.comp h1).add (measurable_const.mul
    (Complex.measurable_ofReal.comp (h2.const_mul _)))


/-- The moments of the row sum with constant coefficients `cs`: integrability of `|Z|^{2p}` and
`E|Z|^{2p} ≤ 2 (2p-1)!! (Σ_k s_{xk} |cs_k|²)^p`, where `Z = Σ_k h_{xk} cs_k`. -/
private theorem ldeLin_row_moment (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ a b, 0 ≤ S a b)
    (x : ι) (cs : {a : ι // a ≠ x} → ℂ) (p : ℕ) :
    Integrable (fun η => ‖∑ k, hmat η x k.1 * cs k‖ ^ (2 * p)) (gaussLaw S) ∧
    ∫ η, ‖∑ k, hmat η x k.1 * cs k‖ ^ (2 * p) ∂(gaussLaw S) ≤
      2 * ldeLin_dfac p * (∑ k, S x k.1 * ‖cs k‖ ^ 2) ^ p := by
  have := isProbabilityMeasure_gaussLaw S
  -- the coordinates of the row, as an independent Gaussian family indexed by `K × Bool`
  set X : {a : ι // a ≠ x} × Bool → Sample ι → ℝ := fun j η => η (ldeLin_co x j.1 j.2) with hX
  set v : {a : ι // a ≠ x} × Bool → ℝ≥0 := fun j => coordVar S (ldeLin_co x j.1 j.2) with hv
  have hmeas : ∀ j, Measurable (X j) := fun j => measurable_pi_apply _
  have hlaw : ∀ j, (gaussLaw S).map (X j) = gaussianReal 0 (v j) := fun j =>
    (measurePreserving_eval (fun c => gaussianReal 0 (coordVar S c))
      (ldeLin_co x j.1 j.2)).map_eq
  have hindep : iIndepFun X (gaussLaw S) :=
    (iIndepFun_pi (μ := fun c => gaussianReal 0 (coordVar S c))
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)).precomp
      (g := fun j : {a : ι // a ≠ x} × Bool => ldeLin_co x j.1 j.2) (ldeLin_co_inj x)
  -- real and imaginary parts of `Z` as linear forms
  set αR : {a : ι // a ≠ x} × Bool → ℝ := fun j =>
    if j.2 then (cs j.1).re else -((cs j.1).im * ldeLin_eps x j.1) with hαR
  set αI : {a : ι // a ≠ x} × Bool → ℝ := fun j =>
    if j.2 then (cs j.1).im else (cs j.1).re * ldeLin_eps x j.1 with hαI
  have hRe : ∀ η, (∑ k, hmat η x k.1 * cs k).re = ∑ j ∈ Finset.univ, αR j * X j η := by
    intro η
    simp only [Complex.re_sum, ldeLin_hmat, Fintype.sum_prod_type, Fintype.sum_bool, hαR, hX]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
    ring
  have hIm : ∀ η, (∑ k, hmat η x k.1 * cs k).im = ∑ j ∈ Finset.univ, αI j * X j η := by
    intro η
    simp only [Complex.im_sum, ldeLin_hmat, Fintype.sum_prod_type, Fintype.sum_bool, hαI, hX]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
    ring
  have hpt : ∀ η, ‖∑ k, hmat η x k.1 * cs k‖ ^ (2 * p)
      = ((∑ j ∈ Finset.univ, αR j * X j η) ^ 2 + (∑ j ∈ Finset.univ, αI j * X j η) ^ 2) ^ p := by
    intro η
    rw [pow_mul, Complex.sq_norm, Complex.normSq_apply, ← hRe, ← hIm]
    ring
  -- the variances of the two linear forms are `V / 2`
  have hvR : ∑ j ∈ Finset.univ, αR j ^ 2 * (v j : ℝ) = (∑ k, S x k.1 * ‖cs k‖ ^ 2) / 2 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, hαR, hv, ldeLin_var S hS hnn,
      Finset.sum_div, ite_true, Bool.false_eq_true, ite_false, neg_sq, mul_pow,
      ldeLin_eps_sq, Complex.sq_norm, Complex.normSq_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hvI : ∑ j ∈ Finset.univ, αI j ^ 2 * (v j : ℝ) = (∑ k, S x k.1 * ‖cs k‖ ^ 2) / 2 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, hαI, hv, ldeLin_var S hS hnn,
      Finset.sum_div, ite_true, Bool.false_eq_true, ite_false, mul_pow,
      ldeLin_eps_sq, Complex.sq_norm, Complex.normSq_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [hpt]
  refine ⟨ldeLin_integrable_sq_add_sq_pow hmeas hlaw hindep αR αI Finset.univ p, ?_⟩
  refine (ldeLin_integral_sq_add_sq_pow_le hmeas hlaw hindep αR αI Finset.univ p).trans ?_
  rw [hvR, hvI]
  have h2 : (2 : ℝ) ^ p * ((∑ k, S x k.1 * ‖cs k‖ ^ 2) / 2) ^ p
      = (∑ k, S x k.1 * ‖cs k‖ ^ 2) ^ p := by
    rw [← mul_pow]; congr 1; ring
  refine le_of_eq ?_
  calc (2 : ℝ) ^ p * (ldeLin_dfac p * (((∑ k, S x k.1 * ‖cs k‖ ^ 2) / 2) ^ p
        + ((∑ k, S x k.1 * ‖cs k‖ ^ 2) / 2) ^ p))
      = 2 * ldeLin_dfac p * (2 ^ p * ((∑ k, S x k.1 * ‖cs k‖ ^ 2) / 2) ^ p) := by ring
    _ = _ := by rw [h2]


end Row

/-! ## The tail bound from a moment bound -/

section Tail

/-- Markov at order `p ≥ 1`: if `E|f|^{2p} ≤ K V^p` with `V ≥ 0`, then `P(t V < |f|²) ≤ K / t^p`.
For `V = 0` the moment bound makes `f` vanish almost surely. -/
private theorem ldeLin_markov {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : Ω → E) (K : ℝ) {p : ℕ} (hp : 1 ≤ p)
    {t V : ℝ} (ht : 0 < t) (hV0 : 0 ≤ V) (hint : Integrable (fun η => ‖f η‖ ^ (2 * p)) P)
    (hmom : ∫ η, ‖f η‖ ^ (2 * p) ∂P ≤ K * V ^ p) :
    P {η | t * V < ‖f η‖ ^ 2} ≤ ENNReal.ofReal (K / t ^ p) := by
  rcases hV0.lt_or_eq with hVpos | hVzero
  · set ε : ℝ := (t * V) ^ p with hε
    have hεpos : 0 < ε := pow_pos (mul_pos ht hVpos) _
    have hsub : {η | t * V < ‖f η‖ ^ 2} ⊆ {η | ε ≤ ‖f η‖ ^ (2 * p)} := by
      intro η hη
      simp only [Set.mem_ofPred_eq] at hη ⊢
      rw [pow_mul, hε]
      exact pow_le_pow_left₀ (mul_pos ht hVpos).le hη.le _
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Eventually.of_forall fun η => by positivity) hint ε
    set m := P.real {η | ε ≤ ‖f η‖ ^ (2 * p)} with hm
    have hreal : m ≤ K / t ^ p := by
      rw [le_div_iff₀ (pow_pos ht _)]
      have h1 : t ^ p * m * V ^ p ≤ K * V ^ p := by
        have h2 : ε * m ≤ K * V ^ p := hmk.trans hmom
        calc t ^ p * m * V ^ p = ε * m := by rw [hε, mul_pow]; ring
          _ ≤ _ := h2
      have := le_of_mul_le_mul_right h1 (pow_pos hVpos _)
      linarith
    calc P {η | t * V < ‖f η‖ ^ 2}
        ≤ P {η | ε ≤ ‖f η‖ ^ (2 * p)} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {η | ε ≤ ‖f η‖ ^ (2 * p)}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (K / t ^ p) := ENNReal.ofReal_le_ofReal hreal
  · have hmom' : ∫ η, ‖f η‖ ^ (2 * p) ∂P ≤ 0 := by
      rw [← hVzero, zero_pow (by omega), mul_zero] at hmom
      exact hmom
    have hz : ∫ η, ‖f η‖ ^ (2 * p) ∂P = 0 :=
      le_antisymm hmom' (integral_nonneg fun η => by positivity)
    rw [integral_eq_zero_iff_of_nonneg (fun η => by positivity) hint] at hz
    have hnull : P {η | t * V < ‖f η‖ ^ 2} = 0 := by
      refine measure_mono_null (fun η hη => ?_) (ae_iff.1 hz)
      simp only [Set.mem_ofPred_eq, ← hVzero, mul_zero] at hη
      simp only [Set.mem_ofPred_eq, Pi.zero_apply]
      have : 0 < ‖f η‖ ^ (2 * p) := by
        have h0 : 0 < ‖f η‖ := by
          by_contra hcon
          have : ‖f η‖ = 0 := le_antisymm (not_lt.1 hcon) (norm_nonneg _)
          rw [this] at hη
          norm_num at hη
        positivity
      exact this.ne'
    rw [hnull]
    exact zero_le


end Tail

/-! ## Conditioning on the coordinates off row `x` -/

section Cond

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `(ω, η) ↦ A.piecewise η ω`, which takes `η` on `A` and `ω` off `A`, is measurable. -/
private theorem ldeLin_measurable_piecewise (A : Finset (Coord ι)) :
    Measurable fun p : Sample ι × Sample ι => A.piecewise p.2 p.1 := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ A
  · simp only [Finset.piecewise_eq_of_mem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_snd
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_fst

/-- Overwriting a sample on `A` by an independent copy has again the law of the sample. -/
private theorem ldeLin_measurePreserving_piecewise (S : Matrix ι ι ℝ) (A : Finset (Coord ι)) :
    MeasurePreserving (fun p : Sample ι × Sample ι => A.piecewise p.2 p.1)
      ((gaussLaw S).prod (gaussLaw S)) (gaussLaw S) := by
  refine ⟨ldeLin_measurable_piecewise A, ?_⟩
  unfold gaussLaw
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (ldeLin_measurable_piecewise A) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : Sample ι × Sample ι => A.piecewise p.2 p.1) ⁻¹' Set.univ.pi s
      = Set.univ.pi (fun c => if c ∈ A then Set.univ else s c) ×ˢ
        Set.univ.pi (fun c => if c ∈ A then s c else Set.univ) := by
    ext ⟨ω, η⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun c => ?_, fun c => ?_⟩
      · by_cases hc : c ∈ A
        · simp [hc]
        · have := h c
          simpa [Finset.piecewise_eq_of_notMem _ _ _ hc, hc] using this
      · by_cases hc : c ∈ A
        · have := h c
          simpa [Finset.piecewise_eq_of_mem _ _ _ hc, hc] using this
        · simp [hc]
    · rintro ⟨h1, h2⟩ c
      by_cases hc : c ∈ A
      · have := h2 c
        simpa [Finset.piecewise_eq_of_mem _ _ _ hc, hc] using this
      · have := h1 c
        simpa [Finset.piecewise_eq_of_notMem _ _ _ hc, hc] using this
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  by_cases hc : c ∈ A <;> simp [hc]

end Cond

/-- The row sum: for `S` symmetric and `≥ 0`, coefficients `c_k`, `k ≠ x`, measurable, bounded and
independent of row `x`, and `t > 0`: `P(t Σ_k s_{xk} |c_k|² < |Σ_k h_{xk} c_k|²) ≤ C_p t^{−p}`. -/
theorem ldeLinTail :
  ∀ p : ℕ, ∃ C : ℝ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ), S.IsSymm →
    (∀ a b, 0 ≤ S a b) → ∀ (x : ι) (c : Sample ι → {a : ι // a ≠ x} → ℂ),
    (∀ k, Measurable fun ω => c ω k) → (∀ k, FreeOf (rowCoords x) fun ω => c ω k) →
    (∃ M : ℝ, ∀ ω k, ‖c ω k‖ ≤ M) → ∀ t : ℝ, 0 < t →
    gaussLaw S {ω | t * ∑ k, S x k.1 * ‖c ω k‖ ^ 2 < ‖∑ k, hmat ω x k.1 * c ω k‖ ^ 2} ≤
      ENNReal.ofReal (C / t ^ p) := by
  intro p
  cases p with
  | zero =>
    refine ⟨1, fun {ι} _ _ S _ _ x c _ _ _ t _ => ?_⟩
    have := isProbabilityMeasure_gaussLaw S
    rw [pow_zero, div_one, ENNReal.ofReal_one]
    exact prob_le_one
  | succ q =>
    refine ⟨2 * ldeLin_dfac (q + 1), fun {ι} _ _ S hS hnn x c hcm hcf _ t ht => ?_⟩
    have := isProbabilityMeasure_gaussLaw S
    set φ : Sample ι × Sample ι → Sample ι := fun p => (rowCoords x).piecewise p.2 p.1 with hφ
    set E := {ω : Sample ι | t * ∑ k, S x k.1 * ‖c ω k‖ ^ 2 <
        ‖∑ k, hmat ω x k.1 * c ω k‖ ^ 2} with hE
    have hmE : MeasurableSet E := by
      refine measurableSet_lt ?_ ?_
      · exact Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
          measurable_const.mul ((hcm k).norm.pow_const 2)) t
      · exact (Finset.measurable_sum _ fun k _ =>
          (ldeLin_measurable_hmat x k).mul (hcm k)).norm.pow_const 2
    have hmp := ldeLin_measurePreserving_piecewise S (rowCoords x)
    -- the slice of the pulled-back event at `ω` is the event with the constant coefficients `c ω`
    have hslice : ∀ ω : Sample ι, Prod.mk ω ⁻¹' (φ ⁻¹' E)
        = {η | t * ∑ k, S x k.1 * ‖c ω k‖ ^ 2 < ‖∑ k, hmat η x k.1 * c ω k‖ ^ 2} := by
      intro ω
      ext η
      have hc : ∀ k, c ((rowCoords x).piecewise η ω) k = c ω k := fun k => hcf k ω η
      simp only [Set.mem_preimage, hφ, hE, Set.mem_ofPred_eq, hc, ldeLin_hmat_piecewise x ω η]
    calc gaussLaw S E = ((gaussLaw S).prod (gaussLaw S)) (φ ⁻¹' E) :=
          (hmp.measure_preimage hmE.nullMeasurableSet).symm
      _ = ∫⁻ ω, gaussLaw S (Prod.mk ω ⁻¹' (φ ⁻¹' E)) ∂(gaussLaw S) :=
          Measure.prod_apply (hmp.measurable hmE)
      _ ≤ ∫⁻ _ω, ENNReal.ofReal (2 * ldeLin_dfac (q + 1) / t ^ (q + 1)) ∂(gaussLaw S) := by
          refine lintegral_mono fun ω => ?_
          rw [hslice ω]
          have hV0 : 0 ≤ ∑ k, S x k.1 * ‖c ω k‖ ^ 2 :=
            Finset.sum_nonneg fun k _ => mul_nonneg (hnn _ _) (by positivity)
          obtain ⟨hint, hmom⟩ := ldeLin_row_moment S hS hnn x (c ω) (q + 1)
          exact ldeLin_markov (P := gaussLaw S) (fun η => ∑ k, hmat η x k.1 * c ω k)
            (2 * ldeLin_dfac (q + 1)) (by omega) ht hV0 hint hmom
      _ = ENNReal.ofReal (2 * ldeLin_dfac (q + 1) / t ^ (q + 1)) := by
          rw [lintegral_const, measure_univ, mul_one]

/-- The diagonal entry: `P(t s_{xx} < |h_{xx}|²) ≤ C_p t^{−p}` for `t > 0`. -/
theorem ldeDiagTail :
  ∀ p : ℕ, ∃ C : ℝ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ),
    (∀ a b, 0 ≤ S a b) → ∀ (x : ι) (t : ℝ), 0 < t →
    gaussLaw S {ω | t * S x x < ‖hmat ω x x‖ ^ 2} ≤ ENNReal.ofReal (C / t ^ p) := by
  intro p
  cases p with
  | zero =>
    refine ⟨1, fun {ι} _ _ S _ x t _ => ?_⟩
    have := isProbabilityMeasure_gaussLaw S
    rw [pow_zero, div_one, ENNReal.ofReal_one]
    exact prob_le_one
  | succ q =>
    refine ⟨ldeLin_dfac (q + 1), fun {ι} _ _ S hnn x t ht => ?_⟩
    have := isProbabilityMeasure_gaussLaw S
    have hmp : MeasurePreserving (fun ω : Sample ι => ω (.inl x)) (gaussLaw S)
        (gaussianReal 0 (coordVar S (.inl x))) :=
      measurePreserving_eval (fun c => gaussianReal 0 (coordVar S c)) (.inl x)
    have hpt : ∀ ω : Sample ι, ‖hmat ω x x‖ ^ (2 * (q + 1)) = (ω (.inl x)) ^ (2 * (q + 1)) := by
      intro ω
      have h : hmat ω x x = (ω (.inl x) : ℂ) := by simp [hmat]
      rw [h, Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs, ← pow_mul]
    have hmeas : AEStronglyMeasurable (fun r : ℝ => r ^ (2 * (q + 1)))
        ((gaussLaw S).map fun ω : Sample ι => ω (.inl x)) := by fun_prop
    have hint : Integrable (fun ω : Sample ι => ‖hmat ω x x‖ ^ (2 * (q + 1))) (gaussLaw S) := by
      simp only [hpt]
      refine (integrable_map_measure hmeas hmp.measurable.aemeasurable).1 ?_
      rw [hmp.map_eq]
      exact ldeLin_integrable_pow _ _
    have hmom : ∫ ω, ‖hmat ω x x‖ ^ (2 * (q + 1)) ∂(gaussLaw S)
        ≤ ldeLin_dfac (q + 1) * (S x x) ^ (q + 1) := by
      simp only [hpt]
      rw [← integral_map hmp.measurable.aemeasurable hmeas, hmp.map_eq, ldeLin_integral_pow]
      simp only [coordVar]
      rw [Real.coe_toNNReal _ (hnn x x)]
    exact ldeLin_markov (P := gaussLaw S) (fun ω => hmat ω x x) (ldeLin_dfac (q + 1)) (by omega)
      ht (hnn x x) hint hmom


section Instance

end Instance

end RBM8D
