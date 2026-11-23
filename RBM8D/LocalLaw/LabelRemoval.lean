module

public import RBM8D.LocalLaw.Defs
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# The removal of the `P`/`Q` labels by the resampled row

`labelRemovalErr : labelRemovalErrStmt`: the bound of a graph of `Err_{n,D}` with `P`/`Q` labels by
the values of its label-free graphs `Γ_S` at single matrices with the bounds of
[II, Notation 8.8], the step used in the proofs of [II, Claim 8.6] (8.24) and [II, Claim 8.7].

* `P_x F(ω) = ∫ F(ω^{[x,η]}) dη` is an integral over an independent copy `η` of row `x`; the
  resampled sample `ω^{[x,η]}` has the law of `ω` (`LabelRemoval.measurePreserving_piecewise`).
* The resolvent minor `G^{(x)}` is the same for `ω` and `ω^{[x,η]}`, which gives the Schur
  complement identity
  `G^{[x]}_{ab} = G_{ab} − G_{ax} G_{xb} / G_{xx} + G^{[x]}_{ax} G^{[x]}_{xb} / G^{[x]}_{xx}`
  for `a, b ≠ x`, and the large deviation bound for the resampled row
  `G^{[x]}_{xa} = −G^{[x]}_{xx} Σ_{k ≠ x} h^{[x]}_{xk} G^{(x)}_{ka}` with the conditional variance
  `Σ_{k ≠ x} s_{xk} |G^{(x)}_{ka}|²`, which does not depend on `η`; the large deviation bounds hold
  at every spectral parameter of a family by a net in `z`.
* Under [II, (7.7), (7.8), (8.1)] with `0 ≤ Φ̃ ≤ W^{−δ}`, and [II, Lemma 7.1], with high probability
  the matrix `G̃` built from `|G − m|`, the conditional standard deviations of the resampled rows
  and columns and the rank-one Schur terms at the external indices satisfies the two bounds of
  [II, Notation 8.8]: the entry bound and the averaged bound of the weak `(1, 2)` norm (with the
  band of `S` for the averages over the resampled index). The modulus of every factor of the
  labelled graph at a resampled sample is at most the corresponding factor of `Γ`, plus the path
  term of `Γ_S`, at `G̃`; Markov's inequality in `η` controls the remaining samples.
-/
noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

open Graphs

/-! ## Resampling one row -/

section Resample

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `(ω, η) ↦ A.piecewise η ω` is measurable. -/
private lemma LabelRemoval_measurable_piecewise (A : Finset (Coord ι)) :
    Measurable fun p : Sample ι × Sample ι => A.piecewise p.2 p.1 := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ A
  · simp only [Finset.piecewise_eq_of_mem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_snd
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_fst

/-- Overwriting a sample of the law of [I, Assumption 1.1] on a set `A` of coordinates by an
independent copy gives again a sample of this law: `(ω, η) ↦ ω^{[A,η]}` maps the product law to
the law. -/
theorem LabelRemoval.measurePreserving_piecewise (S : Matrix ι ι ℝ) (A : Finset (Coord ι)) :
    MeasurePreserving (fun p : Sample ι × Sample ι => A.piecewise p.2 p.1)
      ((gaussLaw S).prod (gaussLaw S)) (gaussLaw S) := by
  refine ⟨LabelRemoval_measurable_piecewise A, ?_⟩
  unfold gaussLaw
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (LabelRemoval_measurable_piecewise A) (MeasurableSet.univ_pi hs)]
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

/-- The sample `ω^{[x,η]}`: row and column `x` of `ω` replaced by those of `η`. -/
private def LabelRemoval_res (x : ι) (η ω : Sample ι) : Sample ι := (rowCoords x).piecewise η ω

/-- The preimage of any set under a measure preserving map has at most its outer measure. -/
private lemma LabelRemoval_preimage_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν) (s : Set β) :
    μ (f ⁻¹' s) ≤ ν s := by
  calc μ (f ⁻¹' s) ≤ μ (f ⁻¹' toMeasurable ν s) :=
        measure_mono (Set.preimage_mono (subset_toMeasurable ν s))
    _ = ν (toMeasurable ν s) :=
        hf.measure_preimage (measurableSet_toMeasurable ν s).nullMeasurableSet
    _ = ν s := measure_toMeasurable s

/-- Markov's inequality in the second variable: for any set `B` of the product, the samples `ω`
for which the measurable hull of `B` has a section of measure more than `t` have measure at most
`P(B)/t`. -/
private lemma LabelRemoval_markov {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] [SFinite μ] (B : Set (α × β)) (t : ℝ≥0∞)
    (ht : t ≠ 0) (ht' : t ≠ ∞) :
    μ {a | t ≤ ν (Prod.mk a ⁻¹' toMeasurable (μ.prod ν) B)} ≤ μ.prod ν B / t := by
  have hT := measurableSet_toMeasurable (μ.prod ν) B
  have hmeas : Measurable fun a => ν (Prod.mk a ⁻¹' toMeasurable (μ.prod ν) B) :=
    measurable_measure_prodMk_left hT
  calc μ {a | t ≤ ν (Prod.mk a ⁻¹' toMeasurable (μ.prod ν) B)}
      ≤ (∫⁻ a, ν (Prod.mk a ⁻¹' toMeasurable (μ.prod ν) B) ∂μ) / t :=
        meas_ge_le_lintegral_div hmeas.aemeasurable ht ht'
    _ = μ.prod ν B / t := by rw [← Measure.prod_apply hT, measure_toMeasurable]

end Resample

/-! ## Polynomial moments off the event of the label removal -/

/-- The absolute moment `E|Z|^q` of a standard real Gaussian `Z`. -/
def LabelRemoval.gaussMoment (q : ℕ) : ℝ := ∫ x, |x| ^ q ∂(gaussianReal 0 1)

/-- The bound `M_q(ω, y) = (1 + ‖ω‖)^q + 2^q (1 + E|Z|^q) |rowCoords y|` of the moment
`E_η (1 + ‖ω^{[y,η]}‖)^q` of the sample with row and column `y` resampled, for coordinate
variances at most `1` (`‖·‖` the sup norm of the coordinates). -/
def LabelRemoval.momBound {ι : Type} [Fintype ι] [DecidableEq ι] (q : ℕ) (ω : Sample ι)
    (y : ι) : ℝ :=
  (1 + ‖ω‖) ^ q + 2 ^ q * (1 + LabelRemoval.gaussMoment q) * (rowCoords y).card

section Moments

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `|x|^q` is integrable for a centred real Gaussian. -/
private lemma LabelRemoval_integrable_abs_pow (v : ℝ≥0) (q : ℕ) :
    Integrable (fun x : ℝ => |x| ^ q) (gaussianReal 0 v) := by
  have h : MemLp (id : ℝ → ℝ) (q : ℝ≥0) (gaussianReal 0 v) := memLp_id_gaussianReal (q : ℝ≥0)
  rw [ENNReal.coe_natCast] at h
  simpa [Real.norm_eq_abs] using h.integrable_norm_pow'

/-- `E|X|^q ≤ E|Z|^q` for a centred real Gaussian `X` of variance `v ≤ 1`. -/
private lemma LabelRemoval_gaussMoment_le (v : ℝ≥0) (hv : v ≤ 1) (q : ℕ) :
    ∫ x, |x| ^ q ∂(gaussianReal 0 v) ≤ LabelRemoval.gaussMoment q := by
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.2]
  have h0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  have h1 : Real.sqrt v ≤ 1 := by
    rw [Real.sqrt_le_one]; exact_mod_cast hv
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, mul_pow, abs_of_nonneg h0]
  rw [integral_const_mul]
  unfold LabelRemoval.gaussMoment
  have hI : 0 ≤ ∫ x, |x| ^ q ∂(gaussianReal 0 1) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) q
  calc Real.sqrt v ^ q * ∫ x, |x| ^ q ∂(gaussianReal 0 1)
      ≤ 1 * ∫ x, |x| ^ q ∂(gaussianReal 0 1) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ h0 h1) hI
    _ = _ := one_mul _

/-- `(1 + t)^q ≤ 2^q (1 + t^q)` for `t ≥ 0`. -/
private lemma LabelRemoval_one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (q : ℕ) :
    (1 + t) ^ q ≤ 2 ^ q * (1 + t ^ q) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ ≤ 2 ^ q * (1 + t ^ q) :=
        le_mul_of_one_le_right (by positivity) (by have := pow_nonneg ht q; linarith)
  · calc (1 + t) ^ q ≤ (2 * t) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * t ^ q := mul_pow _ _ _
      _ ≤ 2 ^ q * (1 + t ^ q) := by gcongr; linarith

/-- `E(1 + |η_c|)^q ≤ 2^q (1 + E|Z|^q)` for a coordinate of variance at most `1`. -/
private lemma LabelRemoval_coord_moment (S : Matrix ι ι ℝ) (c : Coord ι)
    (hc : coordVar S c ≤ 1) (q : ℕ) :
    ∫ η, (1 + |η c|) ^ q ∂(gaussLaw S) ≤ 2 ^ q * (1 + LabelRemoval.gaussMoment q) := by
  have hmp : MeasurePreserving (fun η : Sample ι => η c) (gaussLaw S)
      (gaussianReal 0 (coordVar S c)) :=
    measurePreserving_eval (fun c => gaussianReal 0 (coordVar S c)) c
  have hint := LabelRemoval_integrable_abs_pow (coordVar S c) q
  have e : ∫ η, (1 + |η c|) ^ q ∂(gaussLaw S) =
      ∫ x, (1 + |x|) ^ q ∂(gaussianReal 0 (coordVar S c)) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)]
  rw [e]
  calc ∫ x, (1 + |x|) ^ q ∂(gaussianReal 0 (coordVar S c))
      ≤ ∫ x, 2 ^ q * (1 + |x| ^ q) ∂(gaussianReal 0 (coordVar S c)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          (((integrable_const 1).add hint).const_mul _) (Eventually.of_forall fun x => ?_)
        exact LabelRemoval_one_add_pow_le _ (abs_nonneg x) q
    _ = 2 ^ q * (1 + ∫ x, |x| ^ q ∂(gaussianReal 0 (coordVar S c))) := by
        rw [integral_const_mul, integral_add (integrable_const 1) hint, integral_const]
        simp
    _ ≤ 2 ^ q * (1 + LabelRemoval.gaussMoment q) := by
        gcongr
        exact LabelRemoval_gaussMoment_le _ hc q

/-- The norm of the resampled sample: `(1 + ‖A.piecewise η ω‖)^q ≤ (1 + ‖ω‖)^q +
Σ_{c ∈ A} (1 + |η_c|)^q`. -/
private lemma LabelRemoval_pow_piecewise_le (A : Finset (Coord ι)) (η ω : Sample ι) (q : ℕ) :
    (1 + ‖A.piecewise η ω‖) ^ q ≤ (1 + ‖ω‖) ^ q + ∑ c ∈ A, (1 + |η c|) ^ q := by
  have hs : 0 ≤ ∑ c ∈ A, (1 + |η c|) ^ q := Finset.sum_nonneg fun c _ => by positivity
  have hω : 0 ≤ (1 + ‖ω‖) ^ q := by positivity
  by_cases hne : Nonempty (Coord ι)
  · obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun b => ‖(A.piecewise η ω) b‖₊)
    have hn : ‖A.piecewise η ω‖ ≤ ‖A.piecewise η ω c‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => by
        have := Finset.le_sup (f := fun b => ‖(A.piecewise η ω) b‖₊) (Finset.mem_univ b)
        rw [hc] at this
        exact_mod_cast this
    refine (pow_le_pow_left₀ (by positivity)
      (by linarith : 1 + ‖A.piecewise η ω‖ ≤ 1 + ‖A.piecewise η ω c‖) q).trans ?_
    by_cases hcA : c ∈ A
    · rw [Finset.piecewise_eq_of_mem _ _ _ hcA, Real.norm_eq_abs]
      have := Finset.single_le_sum (f := fun c => (1 + |η c|) ^ q)
        (fun c _ => by positivity) hcA
      linarith
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hcA]
      have : (1 + ‖ω c‖) ^ q ≤ (1 + ‖ω‖) ^ q :=
        pow_le_pow_left₀ (by positivity) (by linarith [norm_le_pi_norm ω c]) q
      linarith
  · have : A.piecewise η ω = 0 := funext fun c => absurd ⟨c⟩ hne
    rw [this, norm_zero, add_zero, one_pow]
    have : (1 : ℝ) ≤ (1 + ‖ω‖) ^ q := one_le_pow₀ (by linarith [norm_nonneg ω])
    linarith

/-- `η ↦ (1 + ‖A.piecewise η ω‖)^q` is measurable and integrable. -/
private lemma LabelRemoval_integrable_piecewise (S : Matrix ι ι ℝ) (A : Finset (Coord ι))
    (ω : Sample ι) (q : ℕ) :
    Integrable (fun η : Sample ι => (1 + ‖A.piecewise η ω‖) ^ q) (gaussLaw S) := by
  have hm : Measurable fun η : Sample ι => A.piecewise η ω :=
    (LabelRemoval_measurable_piecewise A).comp measurable_prodMk_left
  have hpoly : PolyMeas fun η : Sample ι => (((1 + ‖A.piecewise η ω‖) ^ q : ℝ) : ℂ) := by
    refine ⟨by fun_prop, (1 + ‖ω‖) ^ q, q, fun η => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ q
    have h : ‖A.piecewise η ω‖ ≤ ‖ω‖ + ‖η‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c => ?_
      by_cases hc : c ∈ A
      · rw [Finset.piecewise_eq_of_mem _ _ _ hc]
        linarith [norm_le_pi_norm η c, norm_nonneg ω]
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hc]
        linarith [norm_le_pi_norm ω c, norm_nonneg η]
    nlinarith [norm_nonneg ω, norm_nonneg η]
  have := (integrable_of_polyMeas S _ hpoly).norm
  refine this.congr (Eventually.of_forall fun η => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

/-- `E_η (1 + ‖ω^{[y,η]}‖)^q ≤ M_q(ω, y)` for coordinate variances at most `1`. -/
private lemma LabelRemoval_moment_res (S : Matrix ι ι ℝ) (hS : ∀ c, coordVar S c ≤ 1) (y : ι)
    (ω : Sample ι) (q : ℕ) :
    ∫ η, (1 + ‖(rowCoords y).piecewise η ω‖) ^ q ∂(gaussLaw S) ≤
      LabelRemoval.momBound q ω y := by
  have := isProbabilityMeasure_gaussLaw S
  have hint : ∀ c, Integrable (fun η : Sample ι => (1 + |η c|) ^ q) (gaussLaw S) := by
    intro c
    have hpoly : PolyMeas fun η : Sample ι => (((1 + |η c|) ^ q : ℝ) : ℂ) := by
      refine ⟨by fun_prop, 1, q, fun η => ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
      exact pow_le_pow_left₀ (by positivity) (by
        have := norm_le_pi_norm η c; rw [Real.norm_eq_abs] at this; linarith) q
    refine (integrable_of_polyMeas S _ hpoly).norm.congr (Eventually.of_forall fun η => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  calc ∫ η, (1 + ‖(rowCoords y).piecewise η ω‖) ^ q ∂(gaussLaw S)
      ≤ ∫ η, ((1 + ‖ω‖) ^ q + ∑ c ∈ rowCoords y, (1 + |η c|) ^ q) ∂(gaussLaw S) :=
        integral_mono_of_nonneg (Eventually.of_forall fun η => by positivity)
          ((integrable_const _).add (integrable_finsetSum _ fun c _ => hint c))
          (Eventually.of_forall fun η => LabelRemoval_pow_piecewise_le _ η ω q)
    _ = (1 + ‖ω‖) ^ q + ∑ c ∈ rowCoords y, ∫ η, (1 + |η c|) ^ q ∂(gaussLaw S) := by
        rw [integral_add (integrable_const _) (integrable_finsetSum _ fun c _ => hint c),
          integral_finsetSum _ fun c _ => hint c, integral_const]
        simp
    _ ≤ (1 + ‖ω‖) ^ q + ∑ _c ∈ rowCoords y, 2 ^ q * (1 + LabelRemoval.gaussMoment q) := by
        gcongr with c
        exact LabelRemoval_coord_moment S c (hS c) q
    _ = LabelRemoval.momBound q ω y := by
        rw [Finset.sum_const, nsmul_eq_mul, LabelRemoval.momBound]; ring

/-- `∫_T h ≤ √P(T) √(E h²)` for `h ≥ 0` with `h²` integrable. -/
private lemma LabelRemoval_setIntegral_le (S : Matrix ι ι ℝ) (T : Set (Sample ι))
    (hT : MeasurableSet T) (h : Sample ι → ℝ) (h0 : ∀ η, 0 ≤ h η)
    (hi : Integrable h (gaussLaw S)) (hi2 : Integrable (fun η => h η ^ 2) (gaussLaw S)) :
    ∫ η in T, h η ∂(gaussLaw S) ≤
      Real.sqrt (gaussLaw S T).toReal * Real.sqrt (∫ η, h η ^ 2 ∂(gaussLaw S)) := by
  have := isProbabilityMeasure_gaussLaw S
  set P := (gaussLaw S T).toReal with hP
  set E := ∫ η, h η ^ 2 ∂(gaussLaw S) with hE
  have hE0 : 0 ≤ E := integral_nonneg fun η => sq_nonneg _
  by_cases hP0 : P = 0
  · have hT0 : gaussLaw S T = 0 := by
      rw [hP, ENNReal.toReal_eq_zero_iff] at hP0
      exact hP0.resolve_right (measure_ne_top _ _)
    rw [setIntegral_measure_zero _ hT0]
    positivity
  by_cases hEz : E = 0
  · -- `h = 0` almost everywhere
    have hae : (fun η => h η ^ 2) =ᵐ[gaussLaw S] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun η => sq_nonneg _) hi2).1 hEz
    have hae' : h =ᵐ[gaussLaw S] 0 := hae.mono fun η hη => by simpa using hη
    rw [setIntegral_congr_ae hT (hae'.mono fun η hη _ => hη)]
    simp only [Pi.zero_apply, integral_zero]
    positivity
  have hPp : 0 < P := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hP0)
  have hEp : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hEz)
  set lam := Real.sqrt E / Real.sqrt P with hlam
  have hlam0 : 0 < lam := div_pos (Real.sqrt_pos.2 hEp) (Real.sqrt_pos.2 hPp)
  have hpt : ∀ η, T.indicator h η ≤ (lam * T.indicator (fun _ => (1 : ℝ)) η + h η ^ 2 / lam) / 2 := by
    intro η
    by_cases hη : η ∈ T
    · rw [Set.indicator_of_mem hη, Set.indicator_of_mem hη]
      have : 0 ≤ (lam - h η) ^ 2 / lam := div_nonneg (sq_nonneg _) hlam0.le
      have e : (lam - h η) ^ 2 / lam = lam - 2 * h η + h η ^ 2 / lam := by
        field_simp; ring
      linarith
    · rw [Set.indicator_of_notMem hη, Set.indicator_of_notMem hη]
      have : 0 ≤ h η ^ 2 / lam := div_nonneg (sq_nonneg _) hlam0.le
      linarith
  rw [← integral_indicator hT]
  calc ∫ η, T.indicator h η ∂(gaussLaw S)
      ≤ ∫ η, (lam * T.indicator (fun _ => (1 : ℝ)) η + h η ^ 2 / lam) / 2 ∂(gaussLaw S) :=
        integral_mono_of_nonneg (Eventually.of_forall fun η => Set.indicator_nonneg
          (fun η _ => h0 η) η)
          (((((integrable_const 1).indicator hT).const_mul lam).add
            (hi2.div_const lam)).div_const 2) (Eventually.of_forall hpt)
    _ = (lam * P + E / lam) / 2 := by
        rw [integral_div, integral_add (((integrable_const 1).indicator hT).const_mul lam)
          (hi2.div_const lam), integral_const_mul, integral_indicator hT, setIntegral_const,
          integral_div]
        simp [Measure.real, hP, hE]
    _ = Real.sqrt P * Real.sqrt E := by
        have hsP := Real.sq_sqrt hPp.le
        have hsE := Real.sq_sqrt hEp.le
        have h1 : 0 < Real.sqrt P := Real.sqrt_pos.2 hPp
        have h2 : 0 < Real.sqrt E := Real.sqrt_pos.2 hEp
        rw [hlam]
        field_simp
        nlinarith [hsP, hsE]

end Moments

/-- **The partial expectation off a good event, by polynomial moments** (the bound used for the
labels of [II, Claim 8.6] (8.24) and of the error graphs of the `Q`-expansions of [II, Claim 8.7]
on the weights `W_d` of [II, (4.21)], which have no deterministic bound): for coordinate variances
at most `1`, if `|F(ω^{[y,η]})| ≤ B` for `η` outside a measurable set `T` and
`|F(ω')| ≤ K (1 + ‖ω'‖)^p` everywhere, then
`|P_y F(ω)| ≤ B + K M_{2p}(ω, y)^{1/2} P(T)^{1/2}` (`LabelRemoval.momBound`). -/
theorem LabelRemoval.pexp_norm_le_of_good {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : ∀ c, coordVar S c ≤ 1) (y : ι) (F : Sample ι → ℂ) (ω : Sample ι)
    (T : Set (Sample ι)) (hT : MeasurableSet T) (B K : ℝ) (p : ℕ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgood : ∀ η, η ∉ T → ‖F ((rowCoords y).piecewise η ω)‖ ≤ B)
    (hall : ∀ ω', ‖F ω'‖ ≤ K * (1 + ‖ω'‖) ^ p) :
    ‖Pexp S y F ω‖ ≤ B + K * Real.sqrt (LabelRemoval.momBound (2 * p) ω y) *
      Real.sqrt (gaussLaw S T).toReal := by
  have := isProbabilityMeasure_gaussLaw S
  set A := rowCoords y with hA
  set h : Sample ι → ℝ := fun η => (1 + ‖A.piecewise η ω‖) ^ p with hh
  have h0 : ∀ η, 0 ≤ h η := fun η => by positivity
  have hi := LabelRemoval_integrable_piecewise S A ω p
  have hi2 : Integrable (fun η => h η ^ 2) (gaussLaw S) := by
    have := LabelRemoval_integrable_piecewise S A ω (2 * p)
    refine this.congr (Eventually.of_forall fun η => ?_)
    simp only [hh]
    ring
  have hle : ∀ η, ‖F (A.piecewise η ω)‖ ≤ B + K * T.indicator h η := by
    intro η
    by_cases hη : η ∈ T
    · rw [Set.indicator_of_mem hη]; linarith [hall (A.piecewise η ω)]
    · rw [Set.indicator_of_notMem hη, mul_zero, add_zero]; exact hgood η hη
  have hE : ∫ η, h η ^ 2 ∂(gaussLaw S) ≤ LabelRemoval.momBound (2 * p) ω y := by
    refine le_of_eq_of_le ?_ (LabelRemoval_moment_res S hS y ω (2 * p))
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only [hh]
    ring
  unfold Pexp partialExp
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ η, ‖F (A.piecewise η ω)‖ ∂(gaussLaw S)
      ≤ ∫ η, (B + K * T.indicator h η) ∂(gaussLaw S) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((integrable_const B).add ((hi.indicator hT).const_mul K)) (Eventually.of_forall hle)
    _ = B + K * ∫ η in T, (1 + ‖A.piecewise η ω‖) ^ p ∂(gaussLaw S) := by
        rw [integral_add (integrable_const B) ((hi.indicator hT).const_mul K), integral_const,
          integral_const_mul, integral_indicator hT]
        simp
    _ ≤ B + K * (Real.sqrt (gaussLaw S T).toReal *
          Real.sqrt (LabelRemoval.momBound (2 * p) ω y)) := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hK)
        exact (LabelRemoval_setIntegral_le S T hT h h0 hi hi2).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-! ## The resolvent at two spectral parameters and after resampling a row -/

section Resolvent

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `|G(z)_{ab} − G(w)_{ab}| ≤ |z − w| / (Im z Im w)` for a Hermitian `H`, from the resolvent
identity, the Cauchy–Schwarz inequality and the Ward identity. -/
private lemma LabelRemoval_green_lip {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (a b : ι) :
    ‖green H z a b - green H w a b‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M a b) (green_sub_green hH hz.ne' hw.ne')
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
  rw [h, norm_mul]
  have hrow := sum_norm_sq_green_row hH hz a
  have hcol := sum_norm_sq_green_col hH hw b
  have hza : (green H z a a).im ≤ (z.im)⁻¹ := by
    have := norm_green_entry_le hH hz.ne' a a
    rw [abs_of_pos hz] at this
    exact (Complex.im_le_norm _).trans this
  have hwb : (green H w b b).im ≤ (w.im)⁻¹ := by
    have := norm_green_entry_le hH hw.ne' b b
    rw [abs_of_pos hw] at this
    exact (Complex.im_le_norm _).trans this
  have hcs : ‖∑ c, green H z a c * green H w c b‖ ≤ (z.im)⁻¹ * (w.im)⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul]
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun c => ‖green H z a c‖) (fun c => ‖green H w c b‖)
    have hA : ∑ c, ‖green H z a c‖ ^ 2 ≤ (z.im)⁻¹ ^ 2 := by
      rw [hrow, div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_right hza (inv_nonneg.2 hz.le)
    have hB : ∑ c, ‖green H w c b‖ ^ 2 ≤ (w.im)⁻¹ ^ 2 := by
      rw [hcol, div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_right hwb (inv_nonneg.2 hw.le)
    have hA' : Real.sqrt (∑ c, ‖green H z a c‖ ^ 2) ≤ (z.im)⁻¹ :=
      Real.sqrt_le_iff.2 ⟨inv_nonneg.2 hz.le, hA⟩
    have hB' : Real.sqrt (∑ c, ‖green H w c b‖ ^ 2) ≤ (w.im)⁻¹ :=
      Real.sqrt_le_iff.2 ⟨inv_nonneg.2 hw.le, hB⟩
    calc ∑ c, ‖green H z a c‖ * ‖green H w c b‖
        ≤ Real.sqrt (∑ c, ‖green H z a c‖ ^ 2) * Real.sqrt (∑ c, ‖green H w c b‖ ^ 2) := h1
      _ ≤ (z.im)⁻¹ * (w.im)⁻¹ :=
          mul_le_mul hA' hB' (Real.sqrt_nonneg _) (inv_nonneg.2 hz.le)
  calc ‖z - w‖ * ‖∑ c, green H z a c * green H w c b‖ ≤ ‖z - w‖ * ((z.im)⁻¹ * (w.im)⁻¹) :=
        mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
    _ = ‖z - w‖ / (z.im * w.im) := by field_simp

/-- The minor entries `G^{(x)}_{kl}(z)` are Lipschitz in `z` with the same constant. -/
private lemma LabelRemoval_greenMinor_lip {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (x k l : ι) :
    ‖greenMinor (green H z) x k l - greenMinor (green H w) x k l‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have hzero : ∀ v : ℂ, 0 < v.im → (k = x ∨ l = x) → greenMinor (green H v) x k l = 0 := by
    intro v hv hkl
    have hne := green_diag_ne_zero hH hv x
    rcases hkl with rfl | rfl
    · unfold greenMinor; field_simp; ring
    · unfold greenMinor; field_simp; ring
  by_cases hkl : k = x ∨ l = x
  · rw [hzero z hz hkl, hzero w hw hkl, sub_zero, norm_zero]; positivity
  obtain ⟨hk, hl⟩ := not_or.mp hkl
  have key : ∀ v : ℂ, 0 < v.im → greenMinor (green H v) x k l =
      green (H.submatrix (Subtype.val : {a : ι // a ≠ x} → ι) Subtype.val) v ⟨k, hk⟩ ⟨l, hl⟩ := by
    intro v hv
    rw [← minorGreen_eq_greenMinor _ x ⟨k, hk⟩ ⟨l, hl⟩, ← inv_minor_resolvent hH hv x]
    rfl
  rw [key z hz, key w hw]
  exact LabelRemoval_green_lip (hH.submatrix _) hz hw _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The Schur complement identity for a matrix `G'` with the same minor at `y` as `G`:
`G'_{ab} = G_{ab} − G_{ay} G_{yb} / G_{yy} + G'_{ay} G'_{yb} / G'_{yy}`. -/
private lemma LabelRemoval_schur (G G' : Matrix ι ι ℂ) (y a b : ι)
    (h : greenMinor G' y a b = greenMinor G y a b) :
    G' a b = G a b - G a y * G y b / G y y + G' a y * G' y b / G' y y := by
  rw [green_eq_greenMinor_add G' y a b, h, greenMinor]

omit [Fintype ι] [DecidableEq ι] in
/-- The bound `|G'_{ab}| ≤ |G_{ab}| + 8 (|G_{ay}| |G_{yb}| + |G'_{ay}| |G'_{yb}|)` from the Schur
complement identity when `|G_{yy}|, |G'_{yy}| ≥ 1/8`. -/
private lemma LabelRemoval_schur_le (G G' : Matrix ι ι ℂ) (y a b : ι)
    (h : greenMinor G' y a b = greenMinor G y a b) (h1 : 1 / 8 ≤ ‖G y y‖)
    (h2 : 1 / 8 ≤ ‖G' y y‖) :
    ‖G' a b‖ ≤ ‖G a b‖ + 8 * (‖G a y‖ * ‖G y b‖ + ‖G' a y‖ * ‖G' y b‖) := by
  rw [LabelRemoval_schur G G' y a b h]
  have hG0 : 0 < ‖G y y‖ := by linarith
  have hG'0 : 0 < ‖G' y y‖ := by linarith
  have e1 : ‖G a y * G y b / G y y‖ ≤ 8 * (‖G a y‖ * ‖G y b‖) := by
    rw [norm_div, norm_mul, div_le_iff₀ hG0]
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (norm_nonneg (G a y)) (norm_nonneg (G y b)))
    nlinarith [mul_nonneg (norm_nonneg (G a y)) (norm_nonneg (G y b))]
  have e2 : ‖G' a y * G' y b / G' y y‖ ≤ 8 * (‖G' a y‖ * ‖G' y b‖) := by
    rw [norm_div, norm_mul, div_le_iff₀ hG'0]
    have := mul_le_mul_of_nonneg_left h2
      (mul_nonneg (norm_nonneg (G' a y)) (norm_nonneg (G' y b)))
    nlinarith [mul_nonneg (norm_nonneg (G' a y)) (norm_nonneg (G' y b))]
  calc ‖G a b - G a y * G y b / G y y + G' a y * G' y b / G' y y‖
      ≤ ‖G a b‖ + ‖G a y * G y b / G y y‖ + ‖G' a y * G' y b / G' y y‖ := by
        have := norm_sub_le (G a b) (G a y * G y b / G y y)
        have := norm_add_le (G a b - G a y * G y b / G y y) (G' a y * G' y b / G' y y)
        linarith
    _ ≤ _ := by linarith

end Resolvent

/-! ## Sizes along the filter -/

/-- Eventually along `admFilterL c₀ c₁`: `(W, L) ∈ adm(c₀, c₁)`, `W ≥ 2`, and `S` is doubly
stochastic. -/
private lemma LabelRemoval_ev (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ ∧ 2 ≤ sizeW p ∧
      Smat P.ψ p.1.1 p.1.2 ∈ doublyStochastic ℝ (Zd d p.1.2) := by
  obtain ⟨W₀, hW₀⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  have hadm : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ :=
    tendsto_comap.eventually (inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _))
  filter_upwards [hadm, (tendsto_sizeW_admFilterL c₀ c₁).eventually
    (eventually_ge_atTop (max 2 W₀))] with p hp hW
  exact ⟨hp, (le_max_left _ _).trans hW, hW₀ p.1.1 p.1.2 hp ((le_max_right _ _).trans hW)⟩

/-- On `adm(c₀, c₁)` with `W ≥ 1`, every `z ∈ 𝐃(κ, ε)` has `Im z ≥ W^{−|2 − ε|/c₁}`. -/
private lemma LabelRemoval_im_ge {c₀ c₁ κ ε : ℝ} (hc₁ : 0 < c₁) (p : SizeL)
    (hp : p.1 ∈ adm c₀ c₁) (hW : 1 ≤ sizeW p) (z : ℂ) (hz : z ∈ specDom κ ε p.1.1 p.1.2) :
    sizeW p ^ (-(|2 - ε| / c₁)) ≤ z.im := by
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  have hW0 : 0 < sizeW p := by linarith
  have h1 : (p.1.2 : ℝ) ^ (2 - ε) ≤ (p.1.2 : ℝ) ^ |2 - ε| :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self _)
  have h2 : (p.1.2 : ℝ) ^ |2 - ε| ≤ sizeW p ^ (|2 - ε| / c₁) := by
    have e : (p.1.2 : ℝ) ^ |2 - ε| = ((p.1.2 : ℝ) ^ c₁) ^ (|2 - ε| / c₁) := by
      rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp
    rw [e]
    exact Real.rpow_le_rpow (by positivity) hp.1 (by positivity)
  have hpos : 0 < (p.1.2 : ℝ) ^ (2 - ε) := Real.rpow_pos_of_pos (by linarith) _
  have hW2 : (1 : ℝ) ≤ (p.1.1 : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW
    nlinarith
  calc sizeW p ^ (-(|2 - ε| / c₁)) = (sizeW p ^ (|2 - ε| / c₁))⁻¹ := Real.rpow_neg hW0.le _
    _ ≤ ((p.1.2 : ℝ) ^ (2 - ε))⁻¹ := inv_anti₀ hpos (h1.trans h2)
    _ ≤ (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) := by
        rw [div_eq_mul_inv]; exact le_mul_of_one_le_left (inv_nonneg.2 hpos.le) hW2
    _ ≤ z.im := hz.2.1

/-! ## The large deviation bounds at every spectral parameter of a family -/

/-- The number of net points per axis, `M = ⌈3 W^c⌉`. -/
private def LabelRemoval_M (c : ℝ) (p : SizeL) : ℕ := ⌈3 * sizeW p ^ c⌉₊

/-- The index set `{−M, …, M} × {1, …, M}` of the net in `z`. -/
private abbrev LabelRemoval_net (c : ℝ) (p : SizeL) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(LabelRemoval_M c p : ℤ)) (LabelRemoval_M c p) ×ˢ
    Finset.Icc (1 : ℤ) (LabelRemoval_M c p)

/-- The net point `W^{−c} (n₁ + i n₂)`. -/
private def LabelRemoval_pt (c : ℝ) (p : SizeL) (n : LabelRemoval_net c p) : ℂ :=
  (((sizeW p ^ c)⁻¹ * n.1.1 : ℝ) : ℂ) + (((sizeW p ^ c)⁻¹ * n.1.2 : ℝ) : ℂ) * I

/-- The net has at most `W^{2c + 6}` points for `W ≥ 2`, `c ≥ 0`. -/
private lemma LabelRemoval_card_net (c : ℝ) (hc : 0 ≤ c) (p : SizeL) (hW : 2 ≤ sizeW p) :
    (Fintype.card (LabelRemoval_net c p) : ℝ) ≤ sizeW p ^ (2 * c + 6) := by
  have hW0 : 0 < sizeW p := by linarith
  have h1 : 1 ≤ sizeW p ^ c := Real.one_le_rpow (by linarith) hc
  have hM : (LabelRemoval_M c p : ℝ) ≤ 4 * sizeW p ^ c := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 3 * sizeW p ^ c by positivity)
    unfold LabelRemoval_M
    linarith
  rw [Fintype.card_coe, Finset.card_product, Int.card_Icc, Int.card_Icc]
  have e1 : ((LabelRemoval_M c p : ℤ) + 1 - -(LabelRemoval_M c p : ℤ)).toNat =
      2 * LabelRemoval_M c p + 1 := by omega
  have e2 : ((LabelRemoval_M c p : ℤ) + 1 - 1).toNat = LabelRemoval_M c p := by omega
  rw [e1, e2]
  push_cast
  have h6 : (64 : ℝ) ≤ sizeW p ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ sizeW p ^ 6 := pow_le_pow_left₀ (by norm_num) hW 6
  rw [show 2 * c + 6 = c + c + 6 by ring, Real.rpow_add hW0, Real.rpow_add hW0]
  have hM0 : (0 : ℝ) ≤ LabelRemoval_M c p := Nat.cast_nonneg _
  nlinarith [mul_le_mul h6 (le_refl (sizeW p ^ c * sizeW p ^ c)) (by positivity) (by positivity)]

/-- An integer `n` with `|W^{−c} n| ≤ 3` lies in `{−M, …, M}`. -/
private lemma LabelRemoval_mem_Icc (c : ℝ) (p : SizeL) (hW : 0 < sizeW p) (n : ℤ)
    (hn : |(sizeW p ^ c)⁻¹ * n| ≤ 3) :
    n ∈ Finset.Icc (-(LabelRemoval_M c p : ℤ)) (LabelRemoval_M c p) := by
  have hpos0 : 0 < sizeW p ^ c := Real.rpow_pos_of_pos hW c
  have hpos : 0 < (sizeW p ^ c)⁻¹ := inv_pos.2 hpos0
  have h3 : 3 ≤ (sizeW p ^ c)⁻¹ * LabelRemoval_M c p := by
    have hM : 3 * sizeW p ^ c ≤ LabelRemoval_M c p := Nat.le_ceil _
    rw [← div_eq_inv_mul, le_div_iff₀ hpos0]
    linarith
  have hn' := abs_le.mp hn
  have h1 : (n : ℝ) ≤ (LabelRemoval_M c p : ℝ) := le_of_mul_le_mul_left (by linarith) hpos
  have h2 : (-(LabelRemoval_M c p : ℝ)) ≤ (n : ℝ) := by
    refine le_of_mul_le_mul_left ?_ hpos
    linarith
  rw [Finset.mem_Icc]
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩

/-- Rounding `z` with `|Re z| ≤ 2`, `0 < Im z ≤ 1` to the net, the imaginary part rounded up: the
net point `w` has `Im w ≥ Im z` and `|z − w| ≤ 2 W^{−c}`, for `W^{−c} ≤ 1`. -/
private lemma LabelRemoval_net_point (c : ℝ) (p : SizeL) (hW : 0 < sizeW p)
    (hh : (sizeW p ^ c)⁻¹ ≤ 1) (z : ℂ) (hre : |z.re| ≤ 2) (him : 0 < z.im) (him1 : z.im ≤ 1) :
    ∃ n : LabelRemoval_net c p, z.im ≤ (LabelRemoval_pt c p n).im ∧
      ‖z - LabelRemoval_pt c p n‖ ≤ 2 * (sizeW p ^ c)⁻¹ := by
  set h := (sizeW p ^ c)⁻¹ with h_def
  have hpos : 0 < h := inv_pos.2 (Real.rpow_pos_of_pos hW c)
  have hx : h * (z.re / h) = z.re := by field_simp
  have hy : h * (z.im / h) = z.im := by field_simp
  have a1 : h * ⌊z.re / h⌋ ≤ z.re := by
    calc h * ⌊z.re / h⌋ ≤ h * (z.re / h) := mul_le_mul_of_nonneg_left (Int.floor_le _) hpos.le
      _ = z.re := hx
  have a2 : z.re - h < h * ⌊z.re / h⌋ := by
    have : h * (z.re / h) < h * (⌊z.re / h⌋ + 1) :=
      mul_lt_mul_of_pos_left (Int.lt_floor_add_one _) hpos
    rw [hx] at this; linarith
  have b1 : z.im ≤ h * ⌈z.im / h⌉ := by
    calc z.im = h * (z.im / h) := hy.symm
      _ ≤ h * ⌈z.im / h⌉ := mul_le_mul_of_nonneg_left (Int.le_ceil _) hpos.le
  have b2 : h * ⌈z.im / h⌉ < z.im + h := by
    have : h * (⌈z.im / h⌉ : ℝ) < h * (z.im / h + 1) :=
      mul_lt_mul_of_pos_left (Int.ceil_lt_add_one _) hpos
    rw [mul_add, hy] at this; linarith
  have hre' := abs_le.mp hre
  have hm1 := LabelRemoval_mem_Icc c p hW ⌊z.re / h⌋ (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hm2' := LabelRemoval_mem_Icc c p hW ⌈z.im / h⌉ (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hn2 : (1 : ℤ) ≤ ⌈z.im / h⌉ := Int.one_le_ceil_iff.2 (div_pos him hpos)
  have hm2 : ⌈z.im / h⌉ ∈ Finset.Icc (1 : ℤ) (LabelRemoval_M c p) := by
    rw [Finset.mem_Icc] at hm2' ⊢
    exact ⟨hn2, hm2'.2⟩
  have hmem : (⌊z.re / h⌋, ⌈z.im / h⌉) ∈ LabelRemoval_net c p := Finset.mem_product.2 ⟨hm1, hm2⟩
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · simp [LabelRemoval_pt, ← h_def]; exact b1
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [LabelRemoval_pt, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, ← h_def]
    simp only [mul_zero, sub_zero, mul_one, zero_mul, add_zero, zero_add]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z.re - h * ⌊z.re / h⌋),
      abs_of_nonpos (by linarith : z.im - h * ⌈z.im / h⌉ ≤ (0 : ℝ))]
    linarith

/-- `√(Σ s_k b_k²) ≤ √(Σ s_k a_k²) + e` if `0 ≤ b_k ≤ a_k + e`, `s ≥ 0` and `Σ s ≤ 1`. -/
private lemma LabelRemoval_sqrt_wsum_le {κ : Type*} [Fintype κ] (s a b : κ → ℝ)
    (hs : ∀ k, 0 ≤ s k) (hs1 : ∑ k, s k ≤ 1) (ha : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k) (e : ℝ)
    (he : 0 ≤ e) (hb : ∀ k, b k ≤ a k + e) :
    Real.sqrt (∑ k, s k * b k ^ 2) ≤ Real.sqrt (∑ k, s k * a k ^ 2) + e := by
  set R := ∑ k, s k * a k ^ 2 with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun k _ => mul_nonneg (hs k) (sq_nonneg _)
  have hcs : ∑ k, s k * a k ≤ Real.sqrt R := by
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => Real.sqrt (s k))
      (fun k => Real.sqrt (s k) * a k)
    have e1 : ∀ k, Real.sqrt (s k) * (Real.sqrt (s k) * a k) = s k * a k := fun k => by
      rw [← mul_assoc, Real.mul_self_sqrt (hs k)]
    have e2 : ∀ k, Real.sqrt (s k) ^ 2 = s k := fun k => Real.sq_sqrt (hs k)
    have e3 : ∀ k, (Real.sqrt (s k) * a k) ^ 2 = s k * a k ^ 2 := fun k => by
      rw [mul_pow, Real.sq_sqrt (hs k)]
    simp only [e1, e2, e3] at h1
    calc ∑ k, s k * a k ≤ Real.sqrt (∑ k, s k) * Real.sqrt R := h1
      _ ≤ 1 * Real.sqrt R := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_one]; exact hs1
      _ = Real.sqrt R := one_mul _
  have hsum : ∑ k, s k * b k ^ 2 ≤ (Real.sqrt R + e) ^ 2 := by
    have hterm : ∀ k, s k * b k ^ 2 ≤ s k * a k ^ 2 + 2 * e * (s k * a k) + e ^ 2 * s k := by
      intro k
      have := pow_le_pow_left₀ (hb0 k) (hb k) 2
      nlinarith [mul_le_mul_of_nonneg_left this (hs k)]
    calc ∑ k, s k * b k ^ 2
        ≤ ∑ k, (s k * a k ^ 2 + 2 * e * (s k * a k) + e ^ 2 * s k) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = R + 2 * e * ∑ k, s k * a k + e ^ 2 * ∑ k, s k := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ R + 2 * e * Real.sqrt R + e ^ 2 * 1 := by
          have := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ 2 * e)
          have := mul_le_mul_of_nonneg_left hs1 (sq_nonneg e)
          linarith
      _ = (Real.sqrt R + e) ^ 2 := by rw [add_sq, Real.sq_sqrt hR0]; ring
  calc Real.sqrt (∑ k, s k * b k ^ 2) ≤ Real.sqrt ((Real.sqrt R + e) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt R + e := Real.sqrt_sq (by positivity)

/-- The transfer of a large deviation bound from a net point: `A_z ≤ A_w + e`, `D_w ≤ D_z + e`,
`A_w ≤ D_w √t ρ_w` and `ρ_w ≤ ρ_z + e` give `A_z ≤ (D_z + 1) √t (ρ_z + 2e)` for `e ≤ 1 ≤ √t`. -/
private lemma LabelRemoval_transfer {Az Aw Dz Dw ρz ρw t e : ℝ} (hDz : 0 ≤ Dz) (hρz : 0 ≤ ρz)
    (hDw : 0 ≤ Dw) (hρw : 0 ≤ ρw) (he : 0 ≤ e) (he1 : e ≤ 1) (ht : 1 ≤ Real.sqrt t)
    (hA : Az ≤ Aw + e) (hD : Dw ≤ Dz + e) (hAw : Aw ≤ Dw * Real.sqrt t * ρw)
    (hρ : ρw ≤ ρz + e) : Az ≤ (Dz + 1) * Real.sqrt t * (ρz + 2 * e) := by
  have h1 : Dw * Real.sqrt t * ρw ≤ (Dz + 1) * Real.sqrt t * (ρz + e) := by
    have hD' : Dw ≤ Dz + 1 := by linarith
    have := mul_le_mul hD' hρ hρw (by linarith)
    have hst : 0 ≤ Real.sqrt t := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hst]
  have h2 : e ≤ (Dz + 1) * Real.sqrt t * e := by
    have : 1 ≤ (Dz + 1) * Real.sqrt t := by nlinarith
    nlinarith
  nlinarith

section Transfer

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Dropping the term `i` from a sum of nonnegative terms decreases it. -/
private lemma LabelRemoval_sum_subtype_le (F : ι → ℝ) (hF : ∀ k, 0 ≤ F k) (i : ι) :
    ∑ k : {a : ι // a ≠ i}, F k.1 ≤ ∑ k, F k := by
  rw [sum_subtype_ne i F]
  linarith [hF i]

/-- The row large deviation bound at `w` gives, at a nearby `z`,
`|G_{xy}(z)| ≤ (|G_{xx}(z)| + 1) √t ((Σ_{k≠x} s_{xk} |G^{(x)}_{ky}(z)|²)^{1/2} + 2e)`. -/
private lemma LabelRemoval_transfer_row {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (S : Matrix ι ι ℝ) (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k ≤ 1) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (e : ℝ) (he : ‖z - w‖ / (z.im * w.im) ≤ e) (he1 : e ≤ 1)
    (t : ℝ) (ht : 1 ≤ Real.sqrt t) (x y : ι) (hxy : x ≠ y)
    (hL : ldeRowLHS H (green H w) x y ≤ t * ldeRowRHS S (green H w) x y) :
    ‖green H z x y‖ ≤ (‖green H z x x‖ + 1) * Real.sqrt t *
      (Real.sqrt (ldeRowRHS S (green H z) x y) + 2 * e) := by
  have he0 : 0 ≤ e := (div_nonneg (norm_nonneg _) (mul_pos hz hw).le).trans he
  have hyx : y ≠ x := fun h => hxy h.symm
  have hoff := green_offdiag_eq hH hw hyx
  have hAw : ‖green H w x y‖ ≤ ‖green H w x x‖ * Real.sqrt t *
      Real.sqrt (ldeRowRHS S (green H w) x y) := by
    have e1 : ‖green H w x y‖ = ‖green H w x x‖ * Real.sqrt (ldeRowLHS H (green H w) x y) := by
      rw [hoff, norm_mul, norm_neg, ldeRowLHS, Real.sqrt_sq (norm_nonneg _)]
      rfl
    rw [e1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have ht0 : 0 ≤ t := by
      by_contra h; rw [Real.sqrt_eq_zero'.2 (by linarith)] at ht; linarith
    rw [← Real.sqrt_mul ht0]
    exact Real.sqrt_le_sqrt hL
  have hlip := LabelRemoval_green_lip hH hz hw
  have hA : ‖green H z x y‖ ≤ ‖green H w x y‖ + e := by
    have := norm_sub_norm_le (green H z x y) (green H w x y)
    linarith [hlip x y]
  have hD : ‖green H w x x‖ ≤ ‖green H z x x‖ + e := by
    have := norm_sub_norm_le (green H w x x) (green H z x x)
    rw [norm_sub_rev] at this
    linarith [hlip x x]
  have hρ : Real.sqrt (ldeRowRHS S (green H w) x y) ≤
      Real.sqrt (ldeRowRHS S (green H z) x y) + e := by
    refine LabelRemoval_sqrt_wsum_le (fun k : {a : ι // a ≠ x} => S x k.1)
      (fun k => ‖greenMinor (green H z) x k.1 y‖) (fun k => ‖greenMinor (green H w) x k.1 y‖)
      (fun k => hS0 x k.1) ?_ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) e he0 ?_
    · exact (LabelRemoval_sum_subtype_le (S x) (hS0 x) x).trans (hS1 x)
    · intro k
      have h1 := LabelRemoval_greenMinor_lip hH hz hw x k.1 y
      have := norm_sub_norm_le (greenMinor (green H w) x k.1 y) (greenMinor (green H z) x k.1 y)
      rw [norm_sub_rev (greenMinor (green H w) x k.1 y)] at this
      linarith
  exact LabelRemoval_transfer (norm_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _)
    (Real.sqrt_nonneg _) he0 he1 ht hA hD hAw hρ

/-- The column form: the column large deviation bound at `w` gives, at a nearby `z`,
`|G_{yx}(z)| ≤ (|G_{xx}(z)| + 1) √t ((Σ_{k≠x} s_{xk} |G^{(x)}_{yk}(z)|²)^{1/2} + 2e)`. -/
private lemma LabelRemoval_transfer_col {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (S : Matrix ι ι ℝ) (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k ≤ 1) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (e : ℝ) (he : ‖z - w‖ / (z.im * w.im) ≤ e) (he1 : e ≤ 1)
    (t : ℝ) (ht : 1 ≤ Real.sqrt t) (x y : ι) (hxy : x ≠ y)
    (hL : ldeColLHS H (green H w) x y ≤ t * ldeColRHS S (green H w) x y) :
    ‖green H z y x‖ ≤ (‖green H z x x‖ + 1) * Real.sqrt t *
      (Real.sqrt (ldeColRHS S (green H z) x y) + 2 * e) := by
  have he0 : 0 ≤ e := (div_nonneg (norm_nonneg _) (mul_pos hz hw).le).trans he
  have hGii : green H w x x ≠ 0 := green_diag_ne_zero hH hw x
  have hcol : green H w y x = -(green H w x x) * ∑ k : {a : ι // a ≠ x},
      greenMinor (green H w) x y k.1 * H k.1 x := by
    have h1 := sum_minorGreen_col (green_mul_sub hH hw.ne') x hGii
      (⟨y, fun h => hxy h.symm⟩ : {a : ι // a ≠ x})
    have h2 : ∑ l : {a : ι // a ≠ x}, minorGreen (green H w) x ⟨y, fun h => hxy h.symm⟩ l *
          (H - w • (1 : Matrix ι ι ℂ)) l.1 x
        = ∑ k : {a : ι // a ≠ x}, greenMinor (green H w) x y k.1 * H k.1 x := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_smul_one_apply_ne H w k.2]
      rfl
    rw [h2] at h1
    rw [h1]
    field_simp
  have hAw : ‖green H w y x‖ ≤ ‖green H w x x‖ * Real.sqrt t *
      Real.sqrt (ldeColRHS S (green H w) x y) := by
    have e1 : ‖green H w y x‖ = ‖green H w x x‖ * Real.sqrt (ldeColLHS H (green H w) x y) := by
      rw [hcol, norm_mul, norm_neg, ldeColLHS, Real.sqrt_sq (norm_nonneg _)]
    rw [e1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have ht0 : 0 ≤ t := by
      by_contra h; rw [Real.sqrt_eq_zero'.2 (by linarith)] at ht; linarith
    rw [← Real.sqrt_mul ht0]
    exact Real.sqrt_le_sqrt hL
  have hlip := LabelRemoval_green_lip hH hz hw
  have hA : ‖green H z y x‖ ≤ ‖green H w y x‖ + e := by
    have := norm_sub_norm_le (green H z y x) (green H w y x)
    linarith [hlip y x]
  have hD : ‖green H w x x‖ ≤ ‖green H z x x‖ + e := by
    have := norm_sub_norm_le (green H w x x) (green H z x x)
    rw [norm_sub_rev] at this
    linarith [hlip x x]
  have hρ : Real.sqrt (ldeColRHS S (green H w) x y) ≤
      Real.sqrt (ldeColRHS S (green H z) x y) + e := by
    refine LabelRemoval_sqrt_wsum_le (fun k : {a : ι // a ≠ x} => S x k.1)
      (fun k => ‖greenMinor (green H z) x y k.1‖) (fun k => ‖greenMinor (green H w) x y k.1‖)
      (fun k => hS0 x k.1) ?_ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) e he0 ?_
    · exact (LabelRemoval_sum_subtype_le (S x) (hS0 x) x).trans (hS1 x)
    · intro k
      have h1 := LabelRemoval_greenMinor_lip hH hz hw x y k.1
      have := norm_sub_norm_le (greenMinor (green H w) x y k.1) (greenMinor (green H z) x y k.1)
      rw [norm_sub_rev (greenMinor (green H w) x y k.1)] at this
      linarith
  exact LabelRemoval_transfer (norm_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _)
    (Real.sqrt_nonneg _) he0 he1 ht hA hD hAw hρ

end Transfer

/-- The constant of the net transfer: for `W ≥ 2`, a net of mesh `2 W^{−c}` with
`c = 2a + max(C_f, 0) + 3`, and `Im z, Im w ≥ W^{−a}`, the transfer error
`e = |z − w| / (Im z Im w)` has `e ≤ W^{−max(C_f, 0)}/4`. -/
private lemma LabelRemoval_net_err {W a Cf : ℝ} (hW : 2 ≤ W) {z w : ℂ}
    (hz : W ^ (-a) ≤ z.im) (hw : W ^ (-a) ≤ w.im)
    (hzw : ‖z - w‖ ≤ 2 * (W ^ (2 * a + max Cf 0 + 3))⁻¹) :
    ‖z - w‖ / (z.im * w.im) ≤ W ^ (-max Cf 0) / 4 := by
  have hW0 : 0 < W := by linarith
  have ha' : 0 < W ^ (-a) := Real.rpow_pos_of_pos hW0 _
  have hprod : W ^ (-a) * W ^ (-a) ≤ z.im * w.im := mul_le_mul hz hw ha'.le (ha'.le.trans hz)
  have e1 : (W ^ (2 * a + max Cf 0 + 3))⁻¹ =
      W ^ (-a) * W ^ (-a) * (W ^ (-max Cf 0) * W ^ (-3 : ℝ)) := by
    rw [← Real.rpow_neg hW0.le, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    congr 1; ring
  have h3 : W ^ (-3 : ℝ) ≤ 1 / 8 := by
    rw [Real.rpow_neg hW0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_eq_one_div]
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hW 3
    exact one_div_le_one_div_of_le (by norm_num) (by norm_num at this ⊢; linarith)
  have hpos : 0 < z.im * w.im := lt_of_lt_of_le (mul_pos ha' ha') hprod
  have hmC0 : 0 ≤ W ^ (-max Cf 0) := Real.rpow_nonneg hW0.le _
  rw [div_le_iff₀ hpos]
  calc ‖z - w‖ ≤ 2 * (W ^ (-a) * W ^ (-a) * (W ^ (-max Cf 0) * W ^ (-3 : ℝ))) := by
        rw [← e1]; exact hzw
    _ ≤ 2 * (W ^ (-a) * W ^ (-a) * (W ^ (-max Cf 0) * (1 / 8))) := by gcongr
    _ = W ^ (-max Cf 0) / 4 * (W ^ (-a) * W ^ (-a)) := by ring
    _ ≤ W ^ (-max Cf 0) / 4 * (z.im * w.im) := mul_le_mul_of_nonneg_left hprod (by positivity)

/-- The net point near a spectral parameter of `𝐃(κ, ε)` on `adm(c₀, c₁)` at `W ≥ 2`, with the
constants of `LabelRemoval_net_err`. -/
private lemma LabelRemoval_near {c₀ c₁ κ ε Cf : ℝ} (hc₁ : 0 < c₁) (hκ : 0 < κ) (p : SizeL)
    (hp : p.1 ∈ adm c₀ c₁) (hW : 2 ≤ sizeW p) (z : ℂ) (hz : z ∈ specDom κ ε p.1.1 p.1.2) :
    ∃ n : LabelRemoval_net (2 * (|2 - ε| / c₁) + max Cf 0 + 3) p, 0 < z.im ∧
      0 < (LabelRemoval_pt (2 * (|2 - ε| / c₁) + max Cf 0 + 3) p n).im ∧
      ‖z - LabelRemoval_pt (2 * (|2 - ε| / c₁) + max Cf 0 + 3) p n‖ /
        (z.im * (LabelRemoval_pt (2 * (|2 - ε| / c₁) + max Cf 0 + 3) p n).im) ≤
          sizeW p ^ (-max Cf 0) / 4 := by
  set a := |2 - ε| / c₁ with ha
  have ha0 : 0 ≤ a := div_nonneg (abs_nonneg _) hc₁.le
  set c := 2 * a + max Cf 0 + 3 with hc
  have hc0 : 0 ≤ c := by have := le_max_right Cf 0; positivity
  have hW0 : 0 < sizeW p := by linarith
  have hlow := LabelRemoval_im_ge hc₁ p hp (by linarith) z hz
  have him : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hlow
  have hh : (sizeW p ^ c)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) hc0)
  obtain ⟨n, hn1, hn2⟩ := LabelRemoval_net_point c p hW0 hh z
    (by have := hz.1; rw [abs_lt] at this; rw [abs_le]; constructor <;> linarith) him hz.2.2
  exact ⟨n, him, him.trans_le hn1,
    LabelRemoval_net_err hW hlow (hlow.trans hn1) hn2⟩

/-- **The row large deviation bound at every spectral parameter of a family**: for any family
`z(u) ∈ 𝐃(κ, ε)`, `1_{x≠y} |G_{xy}| ≺ (|G_{xx}| + 1)((Σ_{k≠x} s_{xk} |G^{(x)}_{ky}|²)^{1/2} +
W^{−C_f})` uniformly in `u`, `x`, `y`. -/
private lemma LabelRemoval_ldeRow (d : ℕ) (P : Profile d) (c₀ c₁ κ ε Cf : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (U : SizeL → Type) (z : ∀ p, U p → ℂ)
    (hz : ∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) :
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P) (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => if v.2.1 = v.2.2 then 0 else ‖green (hmat ω) (z p v.1) v.2.1 v.2.2‖)
      (fun p v ω => (‖green (hmat ω) (z p v.1) v.2.1 v.2.1‖ + 1) *
        (Real.sqrt (ldeRowRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) v.2.1 v.2.2) +
          sizeW p ^ (-Cf))) := by
  set c := 2 * (|2 - ε| / c₁) + max Cf 0 + 3 with hc
  have hc0 : 0 ≤ c := by
    have := le_max_right Cf 0; have := div_nonneg (abs_nonneg (2 - ε)) hc₁.le; positivity
  intro τ hτ D hD
  have hcard : ∀ᶠ p in admFilterL c₀ c₁,
      (Fintype.card (LabelRemoval_net c p) : ℝ) ≤ sizeW p ^ (2 * c + 6) := by
    filter_upwards [LabelRemoval_ev d P c₀ c₁ hc₀] with p hp
    exact LabelRemoval_card_net c hc0 p hp.2.1
  have him : ∀ᶠ p in admFilterL c₀ c₁, ∀ n : LabelRemoval_net c p,
      0 < (LabelRemoval_pt c p n).im := by
    filter_upwards [LabelRemoval_ev d P c₀ c₁ hc₀] with p hp n
    have hW0 : 0 < sizeW p := by linarith [hp.2.1]
    have h1 : (1 : ℤ) ≤ n.1.2 := (Finset.mem_Icc.1 (Finset.mem_product.1 n.2).2).1
    have h1' : (1 : ℝ) ≤ (n.1.2 : ℝ) := by exact_mod_cast h1
    simp only [LabelRemoval_pt, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    exact mul_pos (inv_pos.2 (Real.rpow_pos_of_pos hW0 _)) (by linarith)
  have hnet := ldeRowDom d P c₀ c₁ (2 * c + 6) hc₀ hc₁ (fun p => LabelRemoval_net c p)
    (fun p n => LabelRemoval_pt c p n) hcard him (τ / 2) (by linarith) D hD
  filter_upwards [hnet, LabelRemoval_ev d P c₀ c₁ hc₀] with p h1 hp
  obtain ⟨hadm, hW, hds⟩ := hp
  have hW0 : 0 < sizeW p := by linarith
  have hS0 : ∀ i k, 0 ≤ Smat P.ψ p.1.1 p.1.2 i k := fun i k => nonneg_of_mem_doublyStochastic hds
  have hS1 : ∀ i, ∑ k, Smat P.ψ p.1.1 p.1.2 i k ≤ 1 := fun i =>
    (sum_row_of_mem_doublyStochastic hds i).le
  refine le_trans (measure_mono ?_) h1
  rintro ω ⟨⟨u, x, y⟩, hlt⟩
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hcon
  have hζ0 : 0 ≤ (‖green (hmat ω) (z p u) x x‖ + 1) *
      (Real.sqrt (ldeRowRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
        sizeW p ^ (-Cf)) := by positivity
  simp only at hlt
  split_ifs at hlt with hxy
  · exact absurd hlt (not_lt.2 (mul_nonneg (Real.rpow_nonneg hW0.le _) hζ0))
  obtain ⟨n, hzim, hwim, he⟩ := LabelRemoval_near (Cf := Cf) hc₁ hκ p hadm hW (z p u) (hz p u)
  have hmax1 : sizeW p ^ (-max Cf 0) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [le_max_right Cf 0])
  have hmaxC : sizeW p ^ (-max Cf 0) ≤ sizeW p ^ (-Cf) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [le_max_left Cf 0])
  have hst : Real.sqrt (sizeW p ^ (τ / 2)) = sizeW p ^ (τ / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]; ring_nf
  have ht1 : 1 ≤ Real.sqrt (sizeW p ^ (τ / 2)) := by
    rw [hst]; exact Real.one_le_rpow (by linarith) (by linarith)
  have hkey := LabelRemoval_transfer_row (hmat_isHermitian ω) _ hS0 hS1 hzim hwim _ he
    (by linarith) _ ht1 x y hxy (hcon (n, x, y))
  have htτ : sizeW p ^ (τ / 4) ≤ sizeW p ^ τ :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have : ‖green (hmat ω) (z p u) x y‖ ≤ sizeW p ^ τ *
      ((‖green (hmat ω) (z p u) x x‖ + 1) *
        (Real.sqrt (ldeRowRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
          sizeW p ^ (-Cf))) := by
    refine hkey.trans ?_
    rw [hst]
    have hA : 0 ≤ ‖green (hmat ω) (z p u) x x‖ + 1 := by positivity
    have hB : Real.sqrt (ldeRowRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
        2 * (sizeW p ^ (-max Cf 0) / 4) ≤
        Real.sqrt (ldeRowRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
          sizeW p ^ (-Cf) := by
      have := Real.rpow_nonneg hW0.le (-max Cf 0); linarith
    calc (‖green (hmat ω) (z p u) x x‖ + 1) * sizeW p ^ (τ / 4) *
          (Real.sqrt (ldeRowRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
            2 * (sizeW p ^ (-max Cf 0) / 4))
        ≤ (‖green (hmat ω) (z p u) x x‖ + 1) * sizeW p ^ τ *
          (Real.sqrt (ldeRowRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
            sizeW p ^ (-Cf)) := by
          gcongr
      _ = _ := by ring
  exact absurd hlt (not_lt.2 this)

/-- **The column large deviation bound at every spectral parameter of a family**:
`1_{x≠y} |G_{yx}| ≺ (|G_{xx}| + 1)((Σ_{k≠x} s_{xk} |G^{(x)}_{yk}|²)^{1/2} + W^{−C_f})` uniformly
in `u`, `x`, `y`. -/
private lemma LabelRemoval_ldeCol (d : ℕ) (P : Profile d) (c₀ c₁ κ ε Cf : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (U : SizeL → Type) (z : ∀ p, U p → ℂ)
    (hz : ∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) :
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P) (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => if v.2.1 = v.2.2 then 0 else ‖green (hmat ω) (z p v.1) v.2.2 v.2.1‖)
      (fun p v ω => (‖green (hmat ω) (z p v.1) v.2.1 v.2.1‖ + 1) *
        (Real.sqrt (ldeColRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) v.2.1 v.2.2) +
          sizeW p ^ (-Cf))) := by
  set c := 2 * (|2 - ε| / c₁) + max Cf 0 + 3 with hc
  have hc0 : 0 ≤ c := by
    have := le_max_right Cf 0; have := div_nonneg (abs_nonneg (2 - ε)) hc₁.le; positivity
  intro τ hτ D hD
  have hcard : ∀ᶠ p in admFilterL c₀ c₁,
      (Fintype.card (LabelRemoval_net c p) : ℝ) ≤ sizeW p ^ (2 * c + 6) := by
    filter_upwards [LabelRemoval_ev d P c₀ c₁ hc₀] with p hp
    exact LabelRemoval_card_net c hc0 p hp.2.1
  have him : ∀ᶠ p in admFilterL c₀ c₁, ∀ n : LabelRemoval_net c p,
      0 < (LabelRemoval_pt c p n).im := by
    filter_upwards [LabelRemoval_ev d P c₀ c₁ hc₀] with p hp n
    have hW0 : 0 < sizeW p := by linarith [hp.2.1]
    have h1 : (1 : ℤ) ≤ n.1.2 := (Finset.mem_Icc.1 (Finset.mem_product.1 n.2).2).1
    have h1' : (1 : ℝ) ≤ (n.1.2 : ℝ) := by exact_mod_cast h1
    simp only [LabelRemoval_pt, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    exact mul_pos (inv_pos.2 (Real.rpow_pos_of_pos hW0 _)) (by linarith)
  have hnet := ldeColDom d P c₀ c₁ (2 * c + 6) hc₀ hc₁ (fun p => LabelRemoval_net c p)
    (fun p n => LabelRemoval_pt c p n) hcard him (τ / 2) (by linarith) D hD
  filter_upwards [hnet, LabelRemoval_ev d P c₀ c₁ hc₀] with p h1 hp
  obtain ⟨hadm, hW, hds⟩ := hp
  have hW0 : 0 < sizeW p := by linarith
  have hS0 : ∀ i k, 0 ≤ Smat P.ψ p.1.1 p.1.2 i k := fun i k => nonneg_of_mem_doublyStochastic hds
  have hS1 : ∀ i, ∑ k, Smat P.ψ p.1.1 p.1.2 i k ≤ 1 := fun i =>
    (sum_row_of_mem_doublyStochastic hds i).le
  refine le_trans (measure_mono ?_) h1
  rintro ω ⟨⟨u, x, y⟩, hlt⟩
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hcon
  have hζ0 : 0 ≤ (‖green (hmat ω) (z p u) x x‖ + 1) *
      (Real.sqrt (ldeColRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
        sizeW p ^ (-Cf)) := by positivity
  simp only at hlt
  split_ifs at hlt with hxy
  · exact absurd hlt (not_lt.2 (mul_nonneg (Real.rpow_nonneg hW0.le _) hζ0))
  obtain ⟨n, hzim, hwim, he⟩ := LabelRemoval_near (Cf := Cf) hc₁ hκ p hadm hW (z p u) (hz p u)
  have hmax1 : sizeW p ^ (-max Cf 0) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [le_max_right Cf 0])
  have hmaxC : sizeW p ^ (-max Cf 0) ≤ sizeW p ^ (-Cf) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [le_max_left Cf 0])
  have hst : Real.sqrt (sizeW p ^ (τ / 2)) = sizeW p ^ (τ / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]; ring_nf
  have ht1 : 1 ≤ Real.sqrt (sizeW p ^ (τ / 2)) := by
    rw [hst]; exact Real.one_le_rpow (by linarith) (by linarith)
  have hkey := LabelRemoval_transfer_col (hmat_isHermitian ω) _ hS0 hS1 hzim hwim _ he
    (by linarith) _ ht1 x y hxy (hcon (n, x, y))
  have htτ : sizeW p ^ (τ / 4) ≤ sizeW p ^ τ :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have : ‖green (hmat ω) (z p u) y x‖ ≤ sizeW p ^ τ *
      ((‖green (hmat ω) (z p u) x x‖ + 1) *
        (Real.sqrt (ldeColRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
          sizeW p ^ (-Cf))) := by
    refine hkey.trans ?_
    rw [hst]
    have hB : Real.sqrt (ldeColRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
        2 * (sizeW p ^ (-max Cf 0) / 4) ≤
        Real.sqrt (ldeColRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
          sizeW p ^ (-Cf) := by
      have := Real.rpow_nonneg hW0.le (-max Cf 0); linarith
    calc (‖green (hmat ω) (z p u) x x‖ + 1) * sizeW p ^ (τ / 4) *
          (Real.sqrt (ldeColRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
            2 * (sizeW p ^ (-max Cf 0) / 4))
        ≤ (‖green (hmat ω) (z p u) x x‖ + 1) * sizeW p ^ τ *
          (Real.sqrt (ldeColRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) x y) +
            sizeW p ^ (-Cf)) := by
          gcongr
      _ = _ := by ring
  exact absurd hlt (not_lt.2 this)

/-! ## Stochastic domination: monotonicity and the filter of the local law -/

/-- `ξ ≺ ζ` and eventually `ζ ≤ ζ'` give `ξ ≺ ζ'`. -/
private lemma LabelRemoval_sd_mono {Par : Type} {Ω : Par → Type} [∀ p, MeasurableSpace (Ω p)]
    {V : Par → Type} {F : Filter Par} {size : Par → ℝ} {P : ∀ p, Measure (Ω p)}
    {ξ ζ ζ' : ∀ p, V p → Ω p → ℝ} (h : StochDom F size P ξ ζ)
    (hsize : ∀ᶠ p in F, 0 ≤ size p) (hle : ∀ᶠ p in F, ∀ v ω, ζ p v ω ≤ ζ' p v ω) :
    StochDom F size P ξ ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hsize, hle] with p hp hs hl
  refine le_trans (measure_mono ?_) hp
  rintro ω ⟨v, hv⟩
  refine ⟨v, lt_of_le_of_lt ?_ hv⟩
  exact mul_le_mul_of_nonneg_left (hl v ω) (Real.rpow_nonneg hs _)

/-- A domination along `F ⊓ 𝓟 T` is a domination along `F` for the family restricted to the
parameters in `T` (empty outside `T`). -/
private lemma LabelRemoval_sd_restrict {Par : Type} {Ω : Par → Type} [∀ p, MeasurableSpace (Ω p)]
    {U X : Par → Type} {F : Filter Par} {T : Set Par} {size : Par → ℝ} {P : ∀ p, Measure (Ω p)}
    {ξ ζ : ∀ p, U p × X p → Ω p → ℝ} (h : StochDom (F ⊓ 𝓟 T) size P ξ ζ) :
    StochDom F size P (U := fun p => {u : U p // p ∈ T} × X p)
      (fun p v ω => ξ p (v.1.1, v.2) ω) (fun p v ω => ζ p (v.1.1, v.2) ω) := by
  intro τ hτ D hD
  have h1 := h τ hτ D hD
  rw [eventually_inf_principal] at h1
  filter_upwards [h1] with p hp
  by_cases hT : p ∈ T
  · refine le_trans (measure_mono ?_) (hp hT)
    rintro ω ⟨v, hv⟩
    exact ⟨(v.1.1, v.2), hv⟩
  · have hempty : {ω | ∃ v : {u : U p // p ∈ T} × X p,
        size p ^ τ * ζ p (v.1.1, v.2) ω < ξ p (v.1.1, v.2) ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun v => absurd v.1.2 hT
    rw [hempty, measure_empty]
    simp

/-- The converse of `LabelRemoval_sd_restrict`. -/
private lemma LabelRemoval_sd_extend {Par : Type} {Ω : Par → Type} [∀ p, MeasurableSpace (Ω p)]
    {U X : Par → Type} {F : Filter Par} {T : Set Par} {size : Par → ℝ} {P : ∀ p, Measure (Ω p)}
    {ξ ζ : ∀ p, U p × X p → Ω p → ℝ}
    (h : StochDom F size P (U := fun p => {u : U p // p ∈ T} × X p)
      (fun p v ω => ξ p (v.1.1, v.2) ω) (fun p v ω => ζ p (v.1.1, v.2) ω)) :
    StochDom (F ⊓ 𝓟 T) size P ξ ζ := by
  intro τ hτ D hD
  rw [eventually_inf_principal]
  filter_upwards [h τ hτ D hD] with p hp hT
  refine le_trans (measure_mono ?_) hp
  rintro ω ⟨v, hv⟩
  exact ⟨(⟨v.1, hT⟩, v.2), hv⟩

/-- `B_{xy} ≤ W^{−d}` for `d ≥ 2`, `W ≥ 1`. -/
private lemma LabelRemoval_bB_le {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W)
    (x y : Zd d L) : bB d L W x y ≤ (W : ℝ) ^ (-(d : ℝ)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold bB
  have h1 : ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) ≤ (W : ℝ) ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hW0 (by
      have := Nat.cast_nonneg (α := ℝ) (zdistInf d L (x - y)); linarith) (by linarith)
  calc (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ))
      ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hW0.le _)
    _ = (W : ℝ) ^ (-(d : ℝ)) := by rw [← Real.rpow_add hW0]; ring_nf

/-- **[II, Lemma 7.1, (7.3)] along the filter of the local law**: under [II, (7.7)] and [II, (8.1)]
with `0 ≤ Φ̃ ≤ W^{−δ}`, `|G_{xx} − m| ≺ W^{−d/2} + Φ̃` uniformly in `u` and `x`. -/
private lemma LabelRemoval_diag (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hκ : 0 < κ) (n : ℕ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀d : ε₀ < (d : ℝ) / 20)
    (U : SizeL → Type) (z : ∀ p, U p → ℂ) (hz : ∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2)
    (h77 : StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => ‖entryErr (green (hmat ω) (z p v.1)) (msc (z p v.1)) v.2.1 v.2.2‖)
      (fun p _ _ => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)))
    (Φ : ∀ p, U p → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hΦ : ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ u, 0 ≤ Φ p u ∧ Φ p u ≤ (p.1.1 : ℝ) ^ (-δ))
    (h81 : StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) (msc (z p v.1))
        v.2.1 v.2.2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2 + Φ p v.1 ^ 2)) :
    StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P) (U := fun p => U p × Zd d p.1.2)
      (fun p v ω => ‖green (hmat ω) (z p v.1) v.2 v.2 - msc (z p v.1)‖)
      (fun p v _ => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) + Φ p v.1) := by
  have hd0 : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set T := thrSet d n c₀T with hT
  set U' : SizeL → Type := fun p => {u : U p // p ∈ T} with hU'
  set δ₀ := min ((d : ℝ) / 2 - ε₀) δ / 2 with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    have : 0 < (d : ℝ) / 2 - ε₀ := by linarith
    have := lt_min this hδ; positivity
  have hδ₀1 : δ₀ ≤ ((d : ℝ) / 2 - ε₀) / 2 := by
    have := min_le_left ((d : ℝ) / 2 - ε₀) δ; linarith
  have hδ₀2 : δ₀ ≤ δ / 2 := by have := min_le_right ((d : ℝ) / 2 - ε₀) δ; linarith
  have hsz := tendsto_sizeW_admFilterL c₀ c₁
  have hW1 : ∀ᶠ p in admFilterL c₀ c₁, 1 ≤ sizeW p := hsz.eventually (eventually_ge_atTop 1)
  have hΦ' := hΦ
  simp only [llFilter, eventually_inf_principal] at hΦ'
  -- the window of `Φ' = W^{−d/2} + Φ`
  have h2W : ∀ᶠ p in admFilterL c₀ c₁, (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) + (p.1.1 : ℝ) ^ (-δ) ≤
      (p.1.1 : ℝ) ^ (-δ₀) := by
    have hA : ∀ᶠ W : ℝ in atTop, W ^ (-((d : ℝ) / 2 - δ₀)) ≤ 1 / 2 :=
      (tendsto_rpow_neg_atTop (by linarith)).eventually (ge_mem_nhds (by norm_num))
    have hB : ∀ᶠ W : ℝ in atTop, W ^ (-(δ - δ₀)) ≤ 1 / 2 :=
      (tendsto_rpow_neg_atTop (by linarith)).eventually (ge_mem_nhds (by norm_num))
    filter_upwards [hsz.eventually hA, hsz.eventually hB, hW1] with p ha hb h1
    have hW0 : 0 < (p.1.1 : ℝ) := lt_of_lt_of_le one_pos h1
    have e1 : (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) =
        (p.1.1 : ℝ) ^ (-((d : ℝ) / 2 - δ₀)) * (p.1.1 : ℝ) ^ (-δ₀) := by
      rw [← Real.rpow_add hW0]; ring_nf
    have e2 : (p.1.1 : ℝ) ^ (-δ) = (p.1.1 : ℝ) ^ (-(δ - δ₀)) * (p.1.1 : ℝ) ^ (-δ₀) := by
      rw [← Real.rpow_add hW0]; ring_nf
    have hp0 : 0 ≤ (p.1.1 : ℝ) ^ (-δ₀) := Real.rpow_nonneg hW0.le _
    rw [e1, e2]
    change sizeW p ^ _ ≤ _ at ha
    change sizeW p ^ _ ≤ _ at hb
    simp only [sizeW] at ha hb
    nlinarith
  have hpar : GTParams d c₀ c₁ κ ε δ₀ U' (fun p u => z p u.1)
      (fun p u => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) + Φ p u.1) := by
    filter_upwards [hΦ', h2W] with p hp h2 u
    obtain ⟨h0, h1⟩ := hp u.2 u.1
    refine ⟨hz p u.1, ?_, ?_⟩
    · simp only [sizeW, neg_div]; linarith
    · simp only [sizeW]; linarith
  have hI1 := LabelRemoval_sd_restrict (T := T) (X := fun p => Zd d p.1.2 × Zd d p.1.2) h77
  have hI2 := LabelRemoval_sd_restrict (T := T) (X := fun p => Zd d p.1.2 × Zd d p.1.2) h81
  have hI : InitialGT d P c₀ c₁ δ₀ U' (fun p u => z p u.1)
      (fun p u => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) + Φ p u.1) := by
    refine ⟨LabelRemoval_sd_mono hI1 (hW1.mono fun p h => by linarith) ?_,
      LabelRemoval_sd_mono hI2 (hW1.mono fun p h => by linarith) ?_⟩
    · filter_upwards [hW1] with p h1 v ω
      simp only [sizeW]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    · filter_upwards [hW1, hΦ'] with p h1 hp v ω
      have hW1' : 1 ≤ p.1.1 := by have : (1 : ℝ) ≤ p.1.1 := h1; exact_mod_cast this
      have hB := LabelRemoval_bB_le (L := p.1.2) (by omega) hW1' v.2.1 v.2.2
      have hΦ0 := (hp v.1.2 v.1.1).1
      have hW0 : 0 < (p.1.1 : ℝ) := lt_of_lt_of_le one_pos h1
      have hsq : ((p.1.1 : ℝ) ^ (-((d : ℝ) / 2))) ^ 2 = (p.1.1 : ℝ) ^ (-(d : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
      have hpos : 0 ≤ (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg hW0.le _
      nlinarith
  have hmain := diagGT d P c₀ c₁ hc₀ hc₁ κ ε δ₀ hκ hδ₀pos U' (fun p u => z p u.1)
    (fun p u => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) + Φ p u.1) hpar hI
  exact LabelRemoval_sd_extend (T := T) (X := fun p => Zd d p.1.2)
    (ξ := fun p v ω => ‖green (hmat ω) (z p v.1) v.2 v.2 - msc (z p v.1)‖)
    (ζ := fun p v _ => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) + Φ p v.1) hmain

/-! ## The weak `(1, 2)` norm from box sums -/

section Box

variable {d L : ℕ} [NeZero L]

/-- The box `{y : ‖y − x₀‖_L ≤ K}`. -/
private abbrev LabelRemoval_box (x₀ : Zd d L) (K : ℕ) : Finset (Zd d L) :=
  Finset.univ.filter fun y => zdistInf d L (y - x₀) ≤ K

/-- The box of radius `K` has at most `(2K + 1)^d` points. -/
private lemma LabelRemoval_card_box (x₀ : Zd d L) (K : ℕ) :
    (LabelRemoval_box x₀ K).card ≤ (2 * K + 1) ^ d := by
  have h : (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(K : ℤ)) K).card = (2 * K + 1) ^ d := by
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

/-- The box of radius `K ≥ 1` has at most `(3K)^d` points. -/
private lemma LabelRemoval_card_box_le (x₀ : Zd d L) (K : ℕ) (hK : 1 ≤ K) :
    ((LabelRemoval_box x₀ K).card : ℝ) ≤ (3 * (K : ℝ)) ^ d := by
  have h := LabelRemoval_card_box x₀ K
  have h' : ((LabelRemoval_box x₀ K).card : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) ^ d := by
    exact_mod_cast h
  refine h'.trans (pow_le_pow_left₀ (by positivity) ?_ d)
  push_cast
  have : (1 : ℝ) ≤ K := by exact_mod_cast hK
  linarith

/-- The box sums of `A` at the scale of [II, Notation 8.8]: for all `x`, `x₀` and `K ∈ [W, L/2]`,
`Σ_{|y − x₀| ≤ K} (A_{xy} + A_{yx}) ≤ M W^{e − 2} K^{2 + d/2}`. -/
private def LabelRemoval_BoxCtl (W : ℕ) (e : ℝ) (A : Matrix (Zd d L) (Zd d L) ℝ) (M : ℝ) :
    Prop :=
  ∀ x x₀ : Zd d L, ∀ K : ℕ, W ≤ K → 2 * K ≤ L →
    ∑ y ∈ LabelRemoval_box x₀ K, (A x y + A y x) ≤
      M * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2))

private lemma LabelRemoval_BoxCtl.add {W : ℕ} {e : ℝ} {A B : Matrix (Zd d L) (Zd d L) ℝ}
    {M N : ℝ} (hA : LabelRemoval_BoxCtl W e A M) (hB : LabelRemoval_BoxCtl W e B N) :
    LabelRemoval_BoxCtl W e (A + B) (M + N) := by
  intro x x₀ K h1 h2
  have := hA x x₀ K h1 h2
  have := hB x x₀ K h1 h2
  simp only [Matrix.add_apply]
  calc ∑ y ∈ LabelRemoval_box x₀ K, (A x y + B x y + (A y x + B y x))
      = ∑ y ∈ LabelRemoval_box x₀ K, (A x y + A y x) +
          ∑ y ∈ LabelRemoval_box x₀ K, (B x y + B y x) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ _ := by linarith

private lemma LabelRemoval_BoxCtl.mono {W : ℕ} {e : ℝ} {A B : Matrix (Zd d L) (Zd d L) ℝ}
    {M M' : ℝ} (hB : LabelRemoval_BoxCtl W e B M) (hAB : ∀ x y, A x y ≤ B x y) (hM : M ≤ M') :
    LabelRemoval_BoxCtl W e A M' := by
  intro x x₀ K h1 h2
  have hpos : 0 ≤ (W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2) := by positivity
  calc ∑ y ∈ LabelRemoval_box x₀ K, (A x y + A y x)
      ≤ ∑ y ∈ LabelRemoval_box x₀ K, (B x y + B y x) :=
        Finset.sum_le_sum fun y _ => add_le_add (hAB x y) (hAB y x)
    _ ≤ M * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) := hB x x₀ K h1 h2
    _ ≤ M' * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hM hpos

private lemma LabelRemoval_BoxCtl.smul {W : ℕ} {e : ℝ} {A : Matrix (Zd d L) (Zd d L) ℝ}
    {M : ℝ} (hA : LabelRemoval_BoxCtl W e A M) (c : ℝ) (hc : 0 ≤ c) :
    LabelRemoval_BoxCtl W e (c • A) (c * M) := by
  intro x x₀ K h1 h2
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc ∑ y ∈ LabelRemoval_box x₀ K, (c * A x y + c * A y x)
      = c * ∑ y ∈ LabelRemoval_box x₀ K, (A x y + A y x) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ c * (M * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (hA x x₀ K h1 h2) hc
    _ = c * M * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) := by ring

/-- Box sums from square box sums (Cauchy–Schwarz): if
`Σ_{|y − x₀| ≤ K} (A_{xy}² + A_{yx}²) ≤ Q W^{2e − 4} K⁴` with `A ≥ 0`, then the box sums of `A` are
at most `(2 Q)^{1/2} 3^{d/2} W^{e − 2} K^{2 + d/2}`. -/
private lemma LabelRemoval_BoxCtl.of_sq {W : ℕ} {e : ℝ} {A : Matrix (Zd d L) (Zd d L) ℝ}
    {Q : ℝ} (hA : ∀ x y, 0 ≤ A x y) (hQ : 0 ≤ Q) (hW : 1 ≤ W)
    (h : ∀ x x₀ : Zd d L, ∀ K : ℕ, W ≤ K → 2 * K ≤ L →
      ∑ y ∈ LabelRemoval_box x₀ K, (A x y ^ 2 + A y x ^ 2) ≤
        Q * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4)) :
    LabelRemoval_BoxCtl W e A (Real.sqrt (2 * Q) * Real.sqrt (3 ^ d)) := by
  intro x x₀ K h1 h2
  have hK1 : 1 ≤ K := hW.trans h1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set s := LabelRemoval_box x₀ K
  have hcs : (∑ y ∈ s, (A x y + A y x)) ^ 2 ≤ (s.card : ℝ) * ∑ y ∈ s, (A x y + A y x) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsq : ∑ y ∈ s, (A x y + A y x) ^ 2 ≤ 2 * ∑ y ∈ s, (A x y ^ 2 + A y x ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => by nlinarith [sq_nonneg (A x y - A y x)]
  have hcard := LabelRemoval_card_box_le x₀ K hK1
  have hS0 : 0 ≤ ∑ y ∈ s, (A x y + A y x) :=
    Finset.sum_nonneg fun y _ => add_nonneg (hA x y) (hA y x)
  have hbound : (∑ y ∈ s, (A x y + A y x)) ^ 2 ≤
      (3 * (K : ℝ)) ^ d * (2 * (Q * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4))) := by
    refine hcs.trans ?_
    have h3 := h x x₀ K h1 h2
    have hsum0 : 0 ≤ ∑ y ∈ s, (A x y + A y x) ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
    calc (s.card : ℝ) * ∑ y ∈ s, (A x y + A y x) ^ 2
        ≤ (3 * (K : ℝ)) ^ d * ∑ y ∈ s, (A x y + A y x) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard hsum0
      _ ≤ (3 * (K : ℝ)) ^ d * (2 * (Q * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
  have hrhs : (3 * (K : ℝ)) ^ d * (2 * (Q * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4))) =
      (Real.sqrt (2 * Q) * Real.sqrt (3 ^ d) * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)))
        ^ 2 := by
    have hw : ((W : ℝ) ^ (e - 2)) ^ 2 = (W : ℝ) ^ (2 * e - 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have hk : ((K : ℝ) ^ (2 + (d : ℝ) / 2)) ^ 2 = (K : ℝ) ^ 4 * (K : ℝ) ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le, ← Real.rpow_natCast (K : ℝ) d,
        ← Real.rpow_natCast (K : ℝ) 4, ← Real.rpow_add hK0]
      congr 1; push_cast; ring
    calc (3 * (K : ℝ)) ^ d * (2 * (Q * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4)))
        = (2 * Q) * 3 ^ d * ((W : ℝ) ^ (2 * e - 4) * ((K : ℝ) ^ 4 * (K : ℝ) ^ d)) := by
          rw [mul_pow]; ring
      _ = Real.sqrt (2 * Q) ^ 2 * Real.sqrt (3 ^ d) ^ 2 *
          (((W : ℝ) ^ (e - 2)) ^ 2 * ((K : ℝ) ^ (2 + (d : ℝ) / 2)) ^ 2) := by
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hw, hk]
      _ = _ := by ring
  rw [hrhs] at hbound
  exact abs_le_of_sq_le_sq' hbound (by positivity) |>.2

/-- **The weak `(1, 2)` norm from the maximum and the box sums**: for `A ≥ 0` with entries at
most `M_∞` and box sums controlled by `M`, `‖A‖_{w;(1,2)} ≤ W^{d/2} M_∞ + M W^e`. -/
private lemma LabelRemoval_weakNorm_le {W : ℕ} {e : ℝ} (hW : 1 ≤ W)
    {A : Matrix (Zd d L) (Zd d L) ℝ} {Mx M : ℝ} (hA : ∀ x y, 0 ≤ A x y)
    (hmax : ∀ x y, A x y ≤ Mx) (hbox : LabelRemoval_BoxCtl W e A M) (hM : 0 ≤ M) :
    weakNorm d L W 1 2 A ≤ (W : ℝ) ^ ((d : ℝ) / 2) * Mx + M * (W : ℝ) ^ e := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hMx : 0 ≤ Mx := (hA 0 0).trans (hmax 0 0)
  unfold weakNorm
  refine add_le_add ?_ ?_
  · rw [one_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.iSup_le (fun x => Real.iSup_le (fun y => by
      rw [abs_of_nonneg (hA x y)]; exact hmax x y) hMx) hMx
  · refine Real.iSup_le (fun K => ?_) (by positivity)
    obtain ⟨K, h1, h2⟩ := K
    have hK1 : 1 ≤ K := hW.trans h1
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
    have hin : (⨆ x, ⨆ x₀ : Zd d L,
        (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
          (K : ℝ) ^ d) ≤ M * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) / (K : ℝ) ^ d := by
      have hpos : 0 ≤ M * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) / (K : ℝ) ^ d := by
        positivity
      refine Real.iSup_le (fun x => Real.iSup_le (fun x₀ => ?_) hpos) hpos
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have := hbox x x₀ K h1 h2
      simp only [abs_of_nonneg (hA _ _)]
      exact this
    calc ((W : ℝ) / K) ^ (2 : ℝ) * (K : ℝ) ^ (1 * (d : ℝ) / 2) *
          (⨆ x, ⨆ x₀ : Zd d L,
            (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
              (K : ℝ) ^ d)
        ≤ ((W : ℝ) / K) ^ (2 : ℝ) * (K : ℝ) ^ (1 * (d : ℝ) / 2) *
          (M * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) / (K : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = M * (W : ℝ) ^ e := by
          rw [Real.div_rpow hW0.le hK0.le, Real.rpow_two, Real.rpow_two,
            Real.rpow_sub hW0, Real.rpow_add hK0, Real.rpow_two, Real.rpow_two]
          have hKd : (K : ℝ) ^ d = (K : ℝ) ^ ((d : ℝ) / 2) * (K : ℝ) ^ ((d : ℝ) / 2) := by
            rw [← Real.rpow_add hK0, ← Real.rpow_natCast]; ring_nf
          rw [hKd, one_mul]
          have h1 : (0 : ℝ) < (K : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hK0 _
          field_simp

end Box

/-! ## The bounds on one resolvent -/

section Hyp

variable {d L : ℕ} [NeZero L]

/-- The bounds that hold with high probability for the resolvent `G`, and for every resolvent
with one row resampled, at the scale `t = W^{τ}`: [II, (7.7)], [II, (7.8)],
[II, Lemma 7.1, (7.3)], the row and column large deviation bounds with the floor `f`, and
[II, (8.1)]. -/
private structure LabelRemoval_Hyp (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (m : ℂ)
    (e t Φ f : ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ) : Prop where
  entry : ∀ x y, ‖entryErr G m x y‖ ≤ t * (W : ℝ) ^ (-((d : ℝ) / 2) + e)
  box : ∀ x x₀ : Zd d L, ∀ K : ℕ, W ≤ K → 2 * K ≤ L →
    boxAvg d L G x x₀ K ≤ t * ((W : ℝ) ^ (2 * e) * (W : ℝ) ^ (-4 : ℝ) * (K : ℝ) ^ (4 - (d : ℝ)))
  diag : ∀ x, ‖G x x - m‖ ≤ t * ((W : ℝ) ^ (-((d : ℝ) / 2)) + Φ)
  row : ∀ x y, x ≠ y → ‖G x y‖ ≤ t * ((‖G x x‖ + 1) * (Real.sqrt (ldeRowRHS S G x y) + f))
  col : ∀ x y, x ≠ y → ‖G y x‖ ≤ t * ((‖G x x‖ + 1) * (Real.sqrt (ldeColRHS S G x y) + f))
  tvar : ∀ x y, Tvar S G m x y ≤ t * (bB d L W x y + Φ ^ 2)

/-- `|a − b|² ≤ 2|a|² + 2|b|²`. -/
private lemma LabelRemoval_norm_sub_sq (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

omit [NeZero L] in
/-- `|G^{(x)}_{ab}|² ≤ 2 |G_{ab}|² + 128 |G_{ax}|² |G_{xb}|²` when `|G_{xx}| ≥ 1/8`. -/
private lemma LabelRemoval_greenMinor_sq (G : Matrix (Zd d L) (Zd d L) ℂ) (x a b : Zd d L)
    (hx : 1 / 8 ≤ ‖G x x‖) :
    ‖greenMinor G x a b‖ ^ 2 ≤ 2 * ‖G a b‖ ^ 2 + 128 * (‖G a x‖ ^ 2 * ‖G x b‖ ^ 2) := by
  unfold greenMinor
  refine (LabelRemoval_norm_sub_sq _ _).trans ?_
  have hx0 : 0 < ‖G x x‖ := by linarith
  have h1 : ‖G a x * G x b / G x x‖ ≤ 8 * (‖G a x‖ * ‖G x b‖) := by
    rw [norm_div, norm_mul, div_le_iff₀ hx0]
    nlinarith [mul_nonneg (norm_nonneg (G a x)) (norm_nonneg (G x b))]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith

variable {W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ} {m : ℂ} {e t Φ f : ℝ}
  {G : Matrix (Zd d L) (Zd d L) ℂ}

/-- The elementary consequences of [II, (7.7)] when `δ₁ = t W^{−d/2+e} ≤ 1/8` and
`1/4 ≤ |m| ≤ 1`: `|G_{xy}| ≤ δ₁` for `x ≠ y`, `|G_{xx} − m| ≤ δ₁`, `1/8 ≤ |G_{xx}| ≤ 2`, and
`|G_{xy}| ≤ 2`. -/
private lemma LabelRemoval_Hyp.basic (h : LabelRemoval_Hyp W S m e t Φ f G)
    (hδ : t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) ≤ 1 / 8) (hm : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) :
    (∀ x y, x ≠ y → ‖G x y‖ ≤ t * (W : ℝ) ^ (-((d : ℝ) / 2) + e)) ∧
    (∀ x, ‖G x x - m‖ ≤ t * (W : ℝ) ^ (-((d : ℝ) / 2) + e)) ∧
    (∀ x, 1 / 8 ≤ ‖G x x‖) ∧ (∀ x, ‖G x x‖ ≤ 2) ∧ (∀ x y, ‖G x y‖ ≤ 2) := by
  have hoff : ∀ x y, x ≠ y → ‖G x y‖ ≤ t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) := by
    intro x y hxy
    have := h.entry x y
    simpa [entryErr, hxy] using this
  have hdd : ∀ x, ‖G x x - m‖ ≤ t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) := by
    intro x
    have := h.entry x x
    simpa [entryErr] using this
  have hlow : ∀ x, 1 / 8 ≤ ‖G x x‖ := by
    intro x
    have := norm_sub_norm_le m (G x x)
    rw [norm_sub_rev] at this
    linarith [hdd x]
  have hup : ∀ x, ‖G x x‖ ≤ 2 := by
    intro x
    have := norm_sub_norm_le (G x x) m
    linarith [hdd x]
  refine ⟨hoff, hdd, hlow, hup, fun x y => ?_⟩
  by_cases hxy : x = y
  · subst hxy; exact hup x
  · linarith [hoff x y hxy]

/-- The square box sums of `G` from [II, (7.8)]:
`Σ_{|y − x₀| ≤ K} (|G_{xy}|² + |G_{yx}|²) ≤ t W^{2e − 4} K⁴`. -/
private lemma LabelRemoval_Hyp.boxSum (h : LabelRemoval_Hyp W S m e t Φ f G) (hW : 1 ≤ W)
    (x x₀ : Zd d L) (K : ℕ) (h1 : W ≤ K) (h2 : 2 * K ≤ L) :
    ∑ y ∈ LabelRemoval_box x₀ K, (‖G x y‖ ^ 2 + ‖G y x‖ ^ 2) ≤
      t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) := by
  have hK0 : (0 : ℝ) < K := by have : 1 ≤ K := hW.trans h1; exact_mod_cast this
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hb := h.box x x₀ K h1 h2
  unfold boxAvg at hb
  rw [div_le_iff₀ (by positivity)] at hb
  refine hb.trans (le_of_eq ?_)
  have e1 : (W : ℝ) ^ (2 * e) * (W : ℝ) ^ (-4 : ℝ) = (W : ℝ) ^ (2 * e - 4) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have e2 : (K : ℝ) ^ (4 - (d : ℝ)) * (K : ℝ) ^ d = (K : ℝ) ^ 4 := by
    rw [← Real.rpow_natCast (K : ℝ) d, ← Real.rpow_add hK0]
    norm_num
  rw [← e1, mul_assoc t, mul_assoc, mul_assoc, e2]
  ring

/-- **The off-diagonal bound** ([II, (7.2)] with [II, (8.1)]): with `δ₁ = t W^{−d/2+e}`,
`36 t δ₁ ≤ 1/2`, `t ≥ 1`, `Φ ≥ 0`, `f ≤ B_{xy}^{1/2}`, `|G_{xy}| ≤ 72 t² (B_{xy}^{1/2} + Φ)` for
`x ≠ y`. -/
private lemma LabelRemoval_Hyp.offdiag (h : LabelRemoval_Hyp W S m e t Φ f G)
    (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : ∀ x, ∑ y, S x y ≤ 1)
    (hδ : t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) ≤ 1 / 8)
    (hδt : 36 * t * (t * (W : ℝ) ^ (-((d : ℝ) / 2) + e)) ≤ 1 / 2) (ht : 1 ≤ t) (hΦ : 0 ≤ Φ)
    (hm : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (x y : Zd d L) (hxy : x ≠ y)
    (hf : f ≤ Real.sqrt (bB d L W x y)) (hf0 : 0 ≤ f) :
    ‖G x y‖ ≤ 72 * t ^ 2 * (Real.sqrt (bB d L W x y) + Φ) := by
  obtain ⟨hoff, hdd, hlow, hup, hall⟩ := h.basic hδ hm hm1
  set δ₁ := t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) with hδ₁
  have hδ0 : 0 ≤ δ₁ := by
    have := (norm_nonneg _).trans (hoff x y hxy); exact this
  set T := Tvar S G m x y with hT
  have hsum : ∑ k, S x k * ‖G k y‖ ^ 2 ≤ 16 * T := by
    have hm2 : (1 : ℝ) / 16 ≤ ‖m‖ ^ 2 := by nlinarith
    have h0 : 0 ≤ ∑ k, S x k * ‖G k y‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 x k) (sq_nonneg _)
    rw [hT, Tvar]; nlinarith
  have hrhs : ldeRowRHS S G x y ≤ 32 * T + 128 * δ₁ ^ 2 * ‖G x y‖ ^ 2 := by
    unfold ldeRowRHS
    have hterm : ∀ k : {a : Zd d L // a ≠ x}, S x k.1 * ‖greenMinor G x k.1 y‖ ^ 2 ≤
        S x k.1 * (2 * ‖G k.1 y‖ ^ 2) + S x k.1 * (128 * δ₁ ^ 2 * ‖G x y‖ ^ 2) := by
      intro k
      have h1 := LabelRemoval_greenMinor_sq G x k.1 y (hlow x)
      have h2 : ‖G k.1 x‖ ^ 2 ≤ δ₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hoff _ _ k.2) 2
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left (h1.trans ?_) (hS0 x k.1)
      nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖G x y‖)]
    calc ∑ k : {a : Zd d L // a ≠ x}, S x k.1 * ‖greenMinor G x k.1 y‖ ^ 2
        ≤ ∑ k : {a : Zd d L // a ≠ x},
            (S x k.1 * (2 * ‖G k.1 y‖ ^ 2) + S x k.1 * (128 * δ₁ ^ 2 * ‖G x y‖ ^ 2)) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = 2 * ∑ k : {a : Zd d L // a ≠ x}, S x k.1 * ‖G k.1 y‖ ^ 2 +
            (∑ k : {a : Zd d L // a ≠ x}, S x k.1) * (128 * δ₁ ^ 2 * ‖G x y‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ 2 * (16 * T) + 1 * (128 * δ₁ ^ 2 * ‖G x y‖ ^ 2) := by
          have a1 := LabelRemoval_sum_subtype_le (fun k => S x k * ‖G k y‖ ^ 2)
            (fun k => mul_nonneg (hS0 x k) (sq_nonneg _)) x
          have a2 := (LabelRemoval_sum_subtype_le (S x) (hS0 x) x).trans (hS1 x)
          have a3 : 0 ≤ 128 * δ₁ ^ 2 * ‖G x y‖ ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right a2 a3]
      _ = 32 * T + 128 * δ₁ ^ 2 * ‖G x y‖ ^ 2 := by ring
  have hT0 : 0 ≤ T := by
    rw [hT, Tvar]; exact mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun k _ => mul_nonneg (hS0 x k) (sq_nonneg _))
  have hsqrt : Real.sqrt (ldeRowRHS S G x y) ≤ 6 * Real.sqrt T + 12 * δ₁ * ‖G x y‖ := by
    rw [Real.sqrt_le_left (by positivity)]
    refine hrhs.trans ?_
    have := Real.sq_sqrt hT0
    nlinarith [Real.sqrt_nonneg T, norm_nonneg (G x y),
      mul_nonneg (Real.sqrt_nonneg T) (mul_nonneg hδ0 (norm_nonneg (G x y)))]
  have hrow := h.row x y hxy
  have hG3 : ‖G x x‖ + 1 ≤ 3 := by linarith [hup x]
  have hstep : ‖G x y‖ ≤ 3 * t * (6 * Real.sqrt T + 12 * δ₁ * ‖G x y‖ + f) := by
    refine hrow.trans ?_
    have h0 : 0 ≤ Real.sqrt (ldeRowRHS S G x y) + f := by positivity
    calc t * ((‖G x x‖ + 1) * (Real.sqrt (ldeRowRHS S G x y) + f))
        ≤ t * (3 * (Real.sqrt (ldeRowRHS S G x y) + f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hG3 h0) (by linarith)
      _ ≤ t * (3 * (6 * Real.sqrt T + 12 * δ₁ * ‖G x y‖ + f)) := by
          gcongr
      _ = 3 * t * (6 * Real.sqrt T + 12 * δ₁ * ‖G x y‖ + f) := by ring
  have habs : ‖G x y‖ ≤ 6 * t * (6 * Real.sqrt T + f) := by
    have : 36 * t * δ₁ * ‖G x y‖ ≤ 1 / 2 * ‖G x y‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    nlinarith
  have hTle : Real.sqrt T ≤ t * (Real.sqrt (bB d L W x y) + Φ) := by
    have hB0 : 0 ≤ bB d L W x y := by
      unfold bB; positivity
    rw [Real.sqrt_le_left (by positivity)]
    refine (h.tvar x y).trans ?_
    have hsB := Real.sq_sqrt hB0
    have : t ≤ t ^ 2 := by nlinarith
    nlinarith [Real.sqrt_nonneg (bB d L W x y), mul_nonneg (Real.sqrt_nonneg (bB d L W x y)) hΦ,
      mul_le_mul_of_nonneg_right this (add_nonneg hB0 (sq_nonneg Φ))]
  calc ‖G x y‖ ≤ 6 * t * (6 * Real.sqrt T + f) := habs
    _ ≤ 6 * t * (6 * (t * (Real.sqrt (bB d L W x y) + Φ)) + Real.sqrt (bB d L W x y)) := by
        gcongr
    _ ≤ 72 * t ^ 2 * (Real.sqrt (bB d L W x y) + Φ) := by
        nlinarith [Real.sqrt_nonneg (bB d L W x y), mul_nonneg (by linarith : (0 : ℝ) ≤ t)
          (Real.sqrt_nonneg (bB d L W x y)), mul_nonneg (by linarith : (0 : ℝ) ≤ t) hΦ]

end Hyp

/-! ## Box sums of the conditional variances of the resampled rows -/

section Smear

variable {d L : ℕ} [NeZero L]

/-- **The smeared box sum**: for `s ≥ 0` with column sums at most `1` and `s_{yk} ≤ s_b` at
distance at least `R`, and `0 ≤ g ≤ g_M`,
`Σ_k (Σ_{|y − x₀| ≤ K} s_{yk}) g_k ≤ Σ_{|k − x₀| ≤ min(K + R, L/2)} g_k + L^{2d} s_b g_M`. -/
private lemma LabelRemoval_smear (S : Matrix (Zd d L) (Zd d L) ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hcol : ∀ k, ∑ y, S y k ≤ 1) (R : ℕ) (sb : ℝ) (hsb : 0 ≤ sb)
    (hband : ∀ y k, R ≤ zdistInf d L (y - k) → S y k ≤ sb) (g : Zd d L → ℝ) (gM : ℝ)
    (hg0 : ∀ k, 0 ≤ g k) (hg1 : ∀ k, g k ≤ gM) (x₀ : Zd d L) (K : ℕ) :
    ∑ k, (∑ y ∈ LabelRemoval_box x₀ K, S y k) * g k ≤
      ∑ k ∈ LabelRemoval_box x₀ (min (K + R) (L / 2)), g k +
        ((L : ℝ) ^ d) ^ 2 * sb * gM := by
  have hgM : 0 ≤ gM := (hg0 x₀).trans (hg1 x₀)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun k => zdistInf d L (k - x₀) ≤ min (K + R) (L / 2))]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun k _ => ?_
    have h1 : ∑ y ∈ LabelRemoval_box x₀ K, S y k ≤ 1 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun y _ _ => hS0 y k).trans (hcol k)
    nlinarith [hg0 k, Finset.sum_nonneg fun y (_ : y ∈ LabelRemoval_box x₀ K) => hS0 y k]
  · have hfar : ∀ k ∈ Finset.univ.filter
        (fun k => ¬ zdistInf d L (k - x₀) ≤ min (K + R) (L / 2)),
        (∑ y ∈ LabelRemoval_box x₀ K, S y k) * g k ≤ (L : ℝ) ^ d * sb * gM := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
      have hhalf := zdistInf_le_half d L (k - x₀)
      have hKR : K + R < zdistInf d L (k - x₀) := by
        rcases le_total (K + R) (L / 2) with h | h
        · rw [min_eq_left h] at hk; exact hk
        · rw [min_eq_right h] at hk; omega
      have hS : ∑ y ∈ LabelRemoval_box x₀ K, S y k ≤ (L : ℝ) ^ d * sb := by
        calc ∑ y ∈ LabelRemoval_box x₀ K, S y k ≤ ∑ _y ∈ LabelRemoval_box x₀ K, sb := by
              refine Finset.sum_le_sum fun y hy => hband y k ?_
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
              have h1 := zdistInf_add_le d L (k - y) (y - x₀)
              rw [show k - y + (y - x₀) = k - x₀ by abel] at h1
              have h2 : zdistInf d L (y - k) = zdistInf d L (k - y) := by
                rw [← zdistInf_neg d L (k - y), neg_sub]
              omega
          _ = ((LabelRemoval_box x₀ K).card : ℝ) * sb := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (L : ℝ) ^ d * sb := by
              refine mul_le_mul_of_nonneg_right ?_ hsb
              have := Finset.card_le_univ (LabelRemoval_box x₀ K)
              rw [card_Zd] at this
              exact_mod_cast this
      exact mul_le_mul hS (hg1 k) (hg0 k) (by positivity)
    calc ∑ k ∈ Finset.univ.filter (fun k => ¬ zdistInf d L (k - x₀) ≤ min (K + R) (L / 2)),
          (∑ y ∈ LabelRemoval_box x₀ K, S y k) * g k
        ≤ ∑ _k ∈ Finset.univ.filter (fun k => ¬ zdistInf d L (k - x₀) ≤ min (K + R) (L / 2)),
          (L : ℝ) ^ d * sb * gM := Finset.sum_le_sum hfar
      _ ≤ ∑ _k : Zd d L, (L : ℝ) ^ d * sb * gM :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => by positivity
      _ = ((L : ℝ) ^ d) ^ 2 * sb * gM := by
          rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]; push_cast; ring

variable {W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ} {m : ℂ} {e t Φ f : ℝ}
  {G : Matrix (Zd d L) (Zd d L) ℂ}

/-- The conditions on `S`, `W`, `L` used for the box sums: `s ≥ 0` doubly stochastic, `s_{yk} ≤
s_b` at distance at least `R`, `(K + R)⁴ ≤ ρ_b K⁴` for `K ≥ W`, `4 L^{2d} s_b ≤ 1`, `e ≥ 0`, `W ≥ 1`
and `t ≥ 1`. -/
private structure LabelRemoval_SCond (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (e t R sb ρb : ℝ)
    (Rn : ℕ) : Prop where
  nonneg : ∀ x y, 0 ≤ S x y
  row : ∀ x, ∑ y, S x y = 1
  col : ∀ y, ∑ x, S x y = 1
  band : ∀ y k, Rn ≤ zdistInf d L (y - k) → S y k ≤ sb
  sb0 : 0 ≤ sb
  sbL : 4 * ((L : ℝ) ^ d) ^ 2 * sb ≤ 1
  grow : ∀ K : ℕ, W ≤ K → ((K : ℝ) + Rn) ^ 4 ≤ ρb * (K : ℝ) ^ 4
  ρb1 : 1 ≤ ρb
  e0 : 0 ≤ e
  W1 : 1 ≤ W
  t1 : 1 ≤ t

omit [NeZero L] in
/-- For `K ≥ W ≥ 1` and `e ≥ 0`, `W^{2e − 4} K⁴ ≥ 1`. -/
private lemma LabelRemoval_one_le_scale {W K : ℕ} {e : ℝ} (hW : 1 ≤ W) (hK : W ≤ K)
    (he : 0 ≤ e) : 1 ≤ (W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4 := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWK : (W : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : (W : ℝ) ^ (2 * e - 4) * (W : ℝ) ^ 4 ≤ (W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0.le hWK 4) (by positivity)
  have h2 : (W : ℝ) ^ (2 * e - 4) * (W : ℝ) ^ 4 = (W : ℝ) ^ (2 * e) := by
    rw [← Real.rpow_natCast (W : ℝ) 4, ← Real.rpow_add hW0]; norm_num
  rw [h2] at h1
  exact (Real.one_le_rpow hW1 (by linarith)).trans h1

/-- The smeared box sum of a row or a column of `G`: for `g_k = |G_{kx}|²` or `|G_{xk}|²`,
`Σ_k (Σ_{|y − x₀| ≤ K} s_{yk}) g_k ≤ 2 ρ_b t W^{2e − 4} K⁴`. -/
private lemma LabelRemoval_smear_G (h : LabelRemoval_Hyp W S m e t Φ f G)
    {R sb ρb : ℝ} {Rn : ℕ} (hS : LabelRemoval_SCond W S e t R sb ρb Rn)
    (hall : ∀ x y, ‖G x y‖ ≤ 2) (g : Zd d L → ℝ) (x : Zd d L) (hg : g = (fun k => ‖G k x‖ ^ 2) ∨
      g = (fun k => ‖G x k‖ ^ 2)) (x₀ : Zd d L) (K : ℕ) (h1 : W ≤ K) (h2 : 2 * K ≤ L) :
    ∑ k, (∑ y ∈ LabelRemoval_box x₀ K, S y k) * g k ≤
      2 * ρb * t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) := by
  have hg0 : ∀ k, 0 ≤ g k := by rcases hg with rfl | rfl <;> intro k <;> positivity
  have hg4 : ∀ k, g k ≤ 4 := by
    rcases hg with rfl | rfl <;> intro k <;> simp only <;>
      nlinarith [hall k x, hall x k, norm_nonneg (G k x), norm_nonneg (G x k)]
  have hsm := LabelRemoval_smear S hS.nonneg (fun k => (hS.col k).le) Rn sb hS.sb0 hS.band g 4
    hg0 hg4 x₀ K
  set K₂ := min (K + Rn) (L / 2) with hK₂
  have hK₂W : W ≤ K₂ := le_min (h1.trans (Nat.le_add_right _ _)) (h1.trans (by omega))
  have hK₂L : 2 * K₂ ≤ L := by have := min_le_right (K + Rn) (L / 2); omega
  have hbox : ∑ k ∈ LabelRemoval_box x₀ K₂, g k ≤ t * ((W : ℝ) ^ (2 * e - 4) * (K₂ : ℝ) ^ 4) := by
    have := h.boxSum hS.W1 x x₀ K₂ hK₂W hK₂L
    refine le_trans ?_ this
    refine Finset.sum_le_sum fun k _ => ?_
    rcases hg with rfl | rfl
    · nlinarith [sq_nonneg ‖G x k‖]
    · nlinarith [sq_nonneg ‖G k x‖]
  have hK₂4 : (K₂ : ℝ) ^ 4 ≤ ρb * (K : ℝ) ^ 4 := by
    have hle : (K₂ : ℝ) ≤ (K : ℝ) + Rn := by
      have : K₂ ≤ K + Rn := min_le_left _ _
      exact_mod_cast this
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hle 4).trans (hS.grow K h1)
  have hsc := LabelRemoval_one_le_scale hS.W1 h1 hS.e0
  have hWe : 0 ≤ (W : ℝ) ^ (2 * e - 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ht1 := hS.t1
  calc ∑ k, (∑ y ∈ LabelRemoval_box x₀ K, S y k) * g k
      ≤ ∑ k ∈ LabelRemoval_box x₀ K₂, g k + ((L : ℝ) ^ d) ^ 2 * sb * 4 := hsm
    _ ≤ t * ((W : ℝ) ^ (2 * e - 4) * (ρb * (K : ℝ) ^ 4)) +
          (W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4 := by
        refine add_le_add (hbox.trans ?_) ?_
        · gcongr
        · nlinarith [hS.sbL]
    _ ≤ 2 * ρb * t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) := by
        have hρ := hS.ρb1
        have hX : 0 ≤ (W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hρ ht1) hX]

/-- `Σ_{k≠i} s_{ik} |G^{(i)}_{kj}|² ≤ 2 Σ_k s_{ik} |G_{kj}|² + 128 δ₁² |G_{ij}|²`. -/
private lemma LabelRemoval_rowRHS_le (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : ∀ x, ∑ y, S x y = 1)
    {δ₁ : ℝ} (hoff : ∀ x y, x ≠ y → ‖G x y‖ ≤ δ₁) (hlow : ∀ x, 1 / 8 ≤ ‖G x x‖) (i j : Zd d L) :
    ldeRowRHS S G i j ≤ 2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 128 * δ₁ ^ 2 * ‖G i j‖ ^ 2 := by
  unfold ldeRowRHS
  have hterm : ∀ k : {a : Zd d L // a ≠ i}, S i k.1 * ‖greenMinor G i k.1 j‖ ^ 2 ≤
      2 * (S i k.1 * ‖G k.1 j‖ ^ 2) + S i k.1 * (128 * δ₁ ^ 2 * ‖G i j‖ ^ 2) := by
    intro k
    have h1 := LabelRemoval_greenMinor_sq G i k.1 j (hlow i)
    have h2 : ‖G k.1 i‖ ^ 2 ≤ δ₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hoff _ _ k.2) 2
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖G i j‖)
    have := mul_le_mul_of_nonneg_left h1 (hS0 i k.1)
    nlinarith [hS0 i k.1]
  calc ∑ k : {a : Zd d L // a ≠ i}, S i k.1 * ‖greenMinor G i k.1 j‖ ^ 2
      ≤ ∑ k : {a : Zd d L // a ≠ i},
          (2 * (S i k.1 * ‖G k.1 j‖ ^ 2) + S i k.1 * (128 * δ₁ ^ 2 * ‖G i j‖ ^ 2)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 2 * ∑ k : {a : Zd d L // a ≠ i}, S i k.1 * ‖G k.1 j‖ ^ 2 +
          (∑ k : {a : Zd d L // a ≠ i}, S i k.1) * (128 * δ₁ ^ 2 * ‖G i j‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 1 * (128 * δ₁ ^ 2 * ‖G i j‖ ^ 2) := by
        have a1 := LabelRemoval_sum_subtype_le (fun k => S i k * ‖G k j‖ ^ 2)
          (fun k => mul_nonneg (hS0 i k) (sq_nonneg _)) i
        have a2 := (LabelRemoval_sum_subtype_le (S i) (hS0 i) i).trans (hS1 i).le
        have a3 : 0 ≤ 128 * δ₁ ^ 2 * ‖G i j‖ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right a2 a3]
    _ = _ := by ring

/-- `Σ_{k≠i} s_{ik} |G^{(i)}_{jk}|² ≤ 2 Σ_k s_{ik} |G_{jk}|² + 128 δ₁² |G_{ji}|²`. -/
private lemma LabelRemoval_colRHS_le (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : ∀ x, ∑ y, S x y = 1)
    {δ₁ : ℝ} (hoff : ∀ x y, x ≠ y → ‖G x y‖ ≤ δ₁) (hlow : ∀ x, 1 / 8 ≤ ‖G x x‖) (i j : Zd d L) :
    ldeColRHS S G i j ≤ 2 * ∑ k, S i k * ‖G j k‖ ^ 2 + 128 * δ₁ ^ 2 * ‖G j i‖ ^ 2 := by
  unfold ldeColRHS
  have hterm : ∀ k : {a : Zd d L // a ≠ i}, S i k.1 * ‖greenMinor G i j k.1‖ ^ 2 ≤
      2 * (S i k.1 * ‖G j k.1‖ ^ 2) + S i k.1 * (128 * δ₁ ^ 2 * ‖G j i‖ ^ 2) := by
    intro k
    have h1 := LabelRemoval_greenMinor_sq G i j k.1 (hlow i)
    have h2 : ‖G i k.1‖ ^ 2 ≤ δ₁ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hoff _ _ fun h => k.2 h.symm) 2
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖G j i‖)
    have := mul_le_mul_of_nonneg_left h1 (hS0 i k.1)
    nlinarith [hS0 i k.1]
  calc ∑ k : {a : Zd d L // a ≠ i}, S i k.1 * ‖greenMinor G i j k.1‖ ^ 2
      ≤ ∑ k : {a : Zd d L // a ≠ i},
          (2 * (S i k.1 * ‖G j k.1‖ ^ 2) + S i k.1 * (128 * δ₁ ^ 2 * ‖G j i‖ ^ 2)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 2 * ∑ k : {a : Zd d L // a ≠ i}, S i k.1 * ‖G j k.1‖ ^ 2 +
          (∑ k : {a : Zd d L // a ≠ i}, S i k.1) * (128 * δ₁ ^ 2 * ‖G j i‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2 * ∑ k, S i k * ‖G j k‖ ^ 2 + 1 * (128 * δ₁ ^ 2 * ‖G j i‖ ^ 2) := by
        have a1 := LabelRemoval_sum_subtype_le (fun k => S i k * ‖G j k‖ ^ 2)
          (fun k => mul_nonneg (hS0 i k) (sq_nonneg _)) i
        have a2 := (LabelRemoval_sum_subtype_le (S i) (hS0 i) i).trans (hS1 i).le
        have a3 : 0 ≤ 128 * δ₁ ^ 2 * ‖G j i‖ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right a2 a3]
    _ = _ := by ring

/-- The fixed-row box sum `Σ_{|y − x₀| ≤ K} Σ_k s_{ik} |G_{ky}|² ≤ t W^{2e−4} K⁴` (and with
`|G_{yk}|²`), since every row of `s` sums to `1`. -/
private lemma LabelRemoval_rowsum_box (h : LabelRemoval_Hyp W S m e t Φ f G)
    (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : ∀ x, ∑ y, S x y = 1) (hW : 1 ≤ W) (i x₀ : Zd d L) (K : ℕ)
    (h1 : W ≤ K) (h2 : 2 * K ≤ L) :
    ∑ y ∈ LabelRemoval_box x₀ K, ∑ k, S i k * (‖G k y‖ ^ 2 + ‖G y k‖ ^ 2) ≤
      t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) := by
  rw [Finset.sum_comm]
  calc ∑ k, ∑ y ∈ LabelRemoval_box x₀ K, S i k * (‖G k y‖ ^ 2 + ‖G y k‖ ^ 2)
      = ∑ k, S i k * ∑ y ∈ LabelRemoval_box x₀ K, (‖G k y‖ ^ 2 + ‖G y k‖ ^ 2) := by
        refine Finset.sum_congr rfl fun k _ => ?_; rw [Finset.mul_sum]
    _ ≤ ∑ k, S i k * (t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4)) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (h.boxSum hW k x₀ K h1 h2) (hS0 i k)
    _ = t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) := by rw [← Finset.sum_mul, hS1 i, one_mul]

/-- **The box sums of the conditional variances**: with `ρ^R_{xy} = (Σ_{k≠x} s_{xk}
|G^{(x)}_{ky}|²)^{1/2}` and `ρ^C_{xy} = (Σ_{k≠y} s_{yk} |G^{(y)}_{xk}|²)^{1/2}`,
`Σ_{|y − x₀| ≤ K} ((ρ_{xy})² + (ρ_{yx})²) ≤ 10 ρ_b t W^{2e−4} K⁴` for both. -/
private lemma LabelRemoval_rho_sq (h : LabelRemoval_Hyp W S m e t Φ f G)
    {R sb ρb : ℝ} {Rn : ℕ} (hS : LabelRemoval_SCond W S e t R sb ρb Rn)
    (hδ : t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) ≤ 1 / 8) (hm : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1)
    (x x₀ : Zd d L) (K : ℕ) (h1 : W ≤ K) (h2 : 2 * K ≤ L) :
    ∑ y ∈ LabelRemoval_box x₀ K, (ldeRowRHS S G x y + ldeRowRHS S G y x) ≤
        10 * ρb * t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) ∧
      ∑ y ∈ LabelRemoval_box x₀ K, (ldeColRHS S G y x + ldeColRHS S G x y) ≤
        10 * ρb * t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) := by
  obtain ⟨hoff, -, hlow, -, hall⟩ := h.basic hδ hm hm1
  set δ₁ := t * (W : ℝ) ^ (-((d : ℝ) / 2) + e)
  have hδ0 : 0 ≤ δ₁ := by
    have := hS.t1; have : (0 : ℝ) ≤ (W : ℝ) ^ (-((d : ℝ) / 2) + e) := by positivity
    positivity
  have hδ2 : 128 * δ₁ ^ 2 ≤ 2 := by nlinarith
  set X := (W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4 with hX
  have hX0 : 0 ≤ X := by positivity
  have hbs := h.boxSum hS.W1 x x₀ K h1 h2
  have hrs := LabelRemoval_rowsum_box h hS.nonneg hS.row hS.W1 x x₀ K h1 h2
  have ht := hS.t1
  have hρ := hS.ρb1
  have hsc : ∑ k, (∑ y ∈ LabelRemoval_box x₀ K, S y k) * ‖G k x‖ ^ 2 ≤ 2 * ρb * t * X :=
    LabelRemoval_smear_G h hS hall _ x (Or.inl rfl) x₀ K h1 h2
  have hsr : ∑ k, (∑ y ∈ LabelRemoval_box x₀ K, S y k) * ‖G x k‖ ^ 2 ≤ 2 * ρb * t * X :=
    LabelRemoval_smear_G h hS hall _ x (Or.inr rfl) x₀ K h1 h2
  have hcomm : ∀ g : Zd d L → ℝ, ∑ y ∈ LabelRemoval_box x₀ K, ∑ k, S y k * g k =
      ∑ k, (∑ y ∈ LabelRemoval_box x₀ K, S y k) * g k := by
    intro g; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
  have hsplit : ∀ g₁ g₂ : Zd d L → ℝ, ∑ y ∈ LabelRemoval_box x₀ K, (g₁ y + g₂ y) =
      ∑ y ∈ LabelRemoval_box x₀ K, g₁ y + ∑ y ∈ LabelRemoval_box x₀ K, g₂ y :=
    fun g₁ g₂ => Finset.sum_add_distrib
  have hGx : ∑ y ∈ LabelRemoval_box x₀ K, ‖G x y‖ ^ 2 ≤ t * X :=
    le_trans (Finset.sum_le_sum fun y _ => by nlinarith [sq_nonneg ‖G y x‖]) hbs
  have hGy : ∑ y ∈ LabelRemoval_box x₀ K, ‖G y x‖ ^ 2 ≤ t * X :=
    le_trans (Finset.sum_le_sum fun y _ => by nlinarith [sq_nonneg ‖G x y‖]) hbs
  have hA : ∑ y ∈ LabelRemoval_box x₀ K, ∑ k, S x k * ‖G k y‖ ^ 2 ≤ t * X :=
    le_trans (Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖G y k‖]) (hS.nonneg x k)) hrs
  have hB : ∑ y ∈ LabelRemoval_box x₀ K, ∑ k, S x k * ‖G y k‖ ^ 2 ≤ t * X :=
    le_trans (Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖G k y‖]) (hS.nonneg x k)) hrs
  have hδX : 128 * δ₁ ^ 2 * (t * X) ≤ 2 * (t * X) :=
    mul_le_mul_of_nonneg_right hδ2 (by positivity)
  have hρtX : 0 ≤ (ρb - 1) * (t * X) := mul_nonneg (by linarith) (by positivity)
  constructor
  · calc ∑ y ∈ LabelRemoval_box x₀ K, (ldeRowRHS S G x y + ldeRowRHS S G y x)
        ≤ ∑ y ∈ LabelRemoval_box x₀ K,
            ((2 * ∑ k, S x k * ‖G k y‖ ^ 2 + 128 * δ₁ ^ 2 * ‖G x y‖ ^ 2) +
              (2 * ∑ k, S y k * ‖G k x‖ ^ 2 + 128 * δ₁ ^ 2 * ‖G y x‖ ^ 2)) :=
          Finset.sum_le_sum fun y _ => add_le_add
            (LabelRemoval_rowRHS_le hS.nonneg hS.row hoff hlow x y)
            (LabelRemoval_rowRHS_le hS.nonneg hS.row hoff hlow y x)
      _ = 2 * ∑ y ∈ LabelRemoval_box x₀ K, ∑ k, S x k * ‖G k y‖ ^ 2 +
            128 * δ₁ ^ 2 * ∑ y ∈ LabelRemoval_box x₀ K, ‖G x y‖ ^ 2 +
            2 * ∑ k, (∑ y ∈ LabelRemoval_box x₀ K, S y k) * ‖G k x‖ ^ 2 +
            128 * δ₁ ^ 2 * ∑ y ∈ LabelRemoval_box x₀ K, ‖G y x‖ ^ 2 := by
          rw [← hcomm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ 2 * (t * X) + 128 * δ₁ ^ 2 * (t * X) + 2 * (2 * ρb * t * X) +
            128 * δ₁ ^ 2 * (t * X) := by
          gcongr
      _ ≤ 10 * ρb * t * X := by nlinarith [hρtX]
  · calc ∑ y ∈ LabelRemoval_box x₀ K, (ldeColRHS S G y x + ldeColRHS S G x y)
        ≤ ∑ y ∈ LabelRemoval_box x₀ K,
            ((2 * ∑ k, S y k * ‖G x k‖ ^ 2 + 128 * δ₁ ^ 2 * ‖G x y‖ ^ 2) +
              (2 * ∑ k, S x k * ‖G y k‖ ^ 2 + 128 * δ₁ ^ 2 * ‖G y x‖ ^ 2)) :=
          Finset.sum_le_sum fun y _ => add_le_add
            (LabelRemoval_colRHS_le hS.nonneg hS.row hoff hlow y x)
            (LabelRemoval_colRHS_le hS.nonneg hS.row hoff hlow x y)
      _ = 2 * ∑ k, (∑ y ∈ LabelRemoval_box x₀ K, S y k) * ‖G x k‖ ^ 2 +
            128 * δ₁ ^ 2 * ∑ y ∈ LabelRemoval_box x₀ K, ‖G x y‖ ^ 2 +
            2 * ∑ y ∈ LabelRemoval_box x₀ K, ∑ k, S x k * ‖G y k‖ ^ 2 +
            128 * δ₁ ^ 2 * ∑ y ∈ LabelRemoval_box x₀ K, ‖G y x‖ ^ 2 := by
          rw [← hcomm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ 2 * (2 * ρb * t * X) + 128 * δ₁ ^ 2 * (t * X) + 2 * (t * X) +
            128 * δ₁ ^ 2 * (t * X) := by
          gcongr
      _ ≤ 10 * ρb * t * X := by nlinarith [hρtX]

end Smear

/-! ## The majorant -/

section Majorant

variable {d L : ℕ} [NeZero L]

/-- The conditional standard deviation `ρ^R_{xy} = (Σ_{k≠x} s_{xk} |G^{(x)}_{ky}|²)^{1/2}` of the
entry `G^{[x]}_{xy}` of the resolvent with row `x` resampled. -/
private def LabelRemoval_ρR (S : Matrix (Zd d L) (Zd d L) ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (x y : Zd d L) : ℝ := Real.sqrt (ldeRowRHS S G x y)

/-- The conditional standard deviation `ρ^C_{xy} = (Σ_{k≠y} s_{yk} |G^{(y)}_{xk}|²)^{1/2}` of the
entry `G^{[y]}_{xy}` of the resolvent with row `y` resampled. -/
private def LabelRemoval_ρC (S : Matrix (Zd d L) (Zd d L) ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (x y : Zd d L) : ℝ := Real.sqrt (ldeColRHS S G y x)

/-- The parameters of the majorant: the scale `t`, the bound `δ₁ = t W^{−d/2+e}` of [II, (7.7)],
the window `Φ` and the floor `f`. -/
structure LabelRemoval_Par where
  t : ℝ
  δ₁ : ℝ
  Φ : ℝ
  f : ℝ

/-- The entry bound `72 t² (B_{xy}^{1/2} + Φ)` of the off-diagonal entries. -/
private def LabelRemoval_E0 (W : ℕ) (q : LabelRemoval_Par) (x y : Zd d L) : ℝ :=
  72 * q.t ^ 2 * (Real.sqrt (bB d L W x y) + q.Φ)

/-- The bound of `|G^{[e]}_{xy}|` for `x, y ≠ e` from the Schur complement identity:
`|G_{xy}| + 8 (|G_{xe}| |G_{ey}| + 9 t² (ρ^C_{xe} + f)(ρ^R_{ey} + f))`. -/
private def LabelRemoval_Esch (S : Matrix (Zd d L) (Zd d L) ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (q : LabelRemoval_Par) (e x y : Zd d L) : ℝ :=
  ‖G x y‖ + 8 * (‖G x e‖ * ‖G e y‖ +
    9 * q.t ^ 2 * ((LabelRemoval_ρC S G x e + q.f) * (LabelRemoval_ρR S G e y + q.f)))

/-- The part of the majorant at the external index `e`: the bound of `|G^{[e]}_{xy}|` for
`x, y ≠ e`, `x ≠ y`. -/
private def LabelRemoval_Ep (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (q : LabelRemoval_Par) (e x y : Zd d L) : ℝ :=
  if x = e ∨ y = e then 0 else
    min (LabelRemoval_E0 W q x y) (min q.δ₁ (LabelRemoval_Esch S G q e x y))

/-- **The majorant** `Ω`: on the diagonal `min(t (W^{−d/2} + Φ), δ₁)`; off the diagonal `|G_{xy}|`,
the bounds of the resampled-row entry `G^{[x]}_{xy}` and of the resampled-column entry
`G^{[y]}_{xy}`, and the bounds of `G^{[a]}_{xy}`, `G^{[b]}_{xy}` at the external indices `a`, `b`;
each bound is the least of the entry bound, the bound `δ₁` of [II, (7.7)] and the bound from the
conditional standard deviations. -/
private def LabelRemoval_Om (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (q : LabelRemoval_Par) (a b : Zd d L) :
    Matrix (Zd d L) (Zd d L) ℝ := fun x y =>
  if x = y then min (q.t * ((W : ℝ) ^ (-((d : ℝ) / 2)) + q.Φ)) q.δ₁ else
    ‖G x y‖ + min (LabelRemoval_E0 W q x y) (min q.δ₁ (3 * q.t * (LabelRemoval_ρR S G x y + q.f))) +
      min (LabelRemoval_E0 W q x y) (min q.δ₁ (3 * q.t * (LabelRemoval_ρC S G x y + q.f))) +
      LabelRemoval_Ep W S G q a x y + LabelRemoval_Ep W S G q b x y

/-- The single matrix `G̃` of [II, Notation 8.8]: `3 (Ω_{xy} + ε)` off the diagonal and
`m + (m/|m|) 3 (Ω_{xx} + ε)` on the diagonal. -/
private def LabelRemoval_Gt (m : ℂ) (ε : ℝ) (Om : Matrix (Zd d L) (Zd d L) ℝ) :
    Matrix (Zd d L) (Zd d L) ℂ := fun x y =>
  if x = y then m + m / (‖m‖ : ℂ) * ((3 * (Om x x + ε) : ℝ) : ℂ)
  else ((3 * (Om x y + ε) : ℝ) : ℂ)

/-- The entries of `G̃ − m`: `|G̃_{xy} − δ_{xy} m| = 3 (Ω_{xy} + ε)`; on the diagonal
`|G̃_{xx}| = |m| + 3 (Ω_{xx} + ε)`. -/
private lemma LabelRemoval_Gt_entry (m : ℂ) (hm : m ≠ 0) (ε : ℝ) (hε : 0 ≤ ε)
    (Om : Matrix (Zd d L) (Zd d L) ℝ) (hOm : ∀ x y, 0 ≤ Om x y) (x y : Zd d L) :
    ‖entryErr (LabelRemoval_Gt m ε Om) m x y‖ = 3 * (Om x y + ε) ∧
      ‖LabelRemoval_Gt m ε Om x x‖ = ‖m‖ + 3 * (Om x x + ε) := by
  have hm0 : (0 : ℝ) < ‖m‖ := norm_pos_iff.2 hm
  have hr : ∀ x y, 0 ≤ 3 * (Om x y + ε) := fun x y => by have := hOm x y; positivity
  have hunit : ‖m / (‖m‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0, div_self hm0.ne']
  constructor
  · unfold entryErr LabelRemoval_Gt
    by_cases hxy : x = y
    · subst hxy
      simp only [ite_true, add_sub_cancel_left, norm_mul, hunit, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      rw [← abs_mul]; exact abs_of_nonneg (hr x x)
    · simp only [hxy, ite_false, sub_zero, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (hr x y)
  · unfold LabelRemoval_Gt
    simp only [ite_true]
    have e1 : m + m / (‖m‖ : ℂ) * ((3 * (Om x x + ε) : ℝ) : ℂ) =
        m / (‖m‖ : ℂ) * (((‖m‖ + 3 * (Om x x + ε)) : ℝ) : ℂ) := by
      have : (‖m‖ : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
      push_cast
      field_simp
    rw [e1, norm_mul, hunit, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hr x x])]

variable {W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ} {G : Matrix (Zd d L) (Zd d L) ℂ}
  {q : LabelRemoval_Par}

/-- The majorant is nonnegative. -/
private lemma LabelRemoval_Om_nonneg (ht : 0 ≤ q.t) (hδ : 0 ≤ q.δ₁) (hΦ : 0 ≤ q.Φ)
    (hf : 0 ≤ q.f) (a b : Zd d L) (x y : Zd d L) : 0 ≤ LabelRemoval_Om W S G q a b x y := by
  have hE : ∀ x y : Zd d L, 0 ≤ LabelRemoval_E0 W q x y := fun x y => by
    unfold LabelRemoval_E0; positivity
  have hEp : ∀ e x y : Zd d L, 0 ≤ LabelRemoval_Ep W S G q e x y := by
    intro e x y
    unfold LabelRemoval_Ep LabelRemoval_Esch LabelRemoval_ρC LabelRemoval_ρR
    split_ifs
    · exact le_rfl
    · exact le_min (hE x y) (le_min hδ (by positivity))
  unfold LabelRemoval_Om
  split_ifs
  · exact le_min (by positivity) hδ
  · have h1 : 0 ≤ min (LabelRemoval_E0 W q x y)
        (min q.δ₁ (3 * q.t * (LabelRemoval_ρR S G x y + q.f))) :=
      le_min (hE x y) (le_min hδ (by unfold LabelRemoval_ρR; positivity))
    have h2 : 0 ≤ min (LabelRemoval_E0 W q x y)
        (min q.δ₁ (3 * q.t * (LabelRemoval_ρC S G x y + q.f))) :=
      le_min (hE x y) (le_min hδ (by unfold LabelRemoval_ρC; positivity))
    have := hEp a x y; have := hEp b x y
    positivity

/-- The majorant is at most `5 δ₁` (the maximum part of [II, Notation 8.8]). -/
private lemma LabelRemoval_Om_le_max {m : ℂ} {e : ℝ}
    (h : LabelRemoval_Hyp W S m e q.t q.Φ q.f G)
    (hδq : q.δ₁ = q.t * (W : ℝ) ^ (-((d : ℝ) / 2) + e)) (hδ : q.δ₁ ≤ 1 / 8)
    (hm : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (a b x y : Zd d L) :
    LabelRemoval_Om W S G q a b x y ≤ 5 * q.δ₁ := by
  obtain ⟨hoff, -, -, -, -⟩ := h.basic (hδq ▸ hδ) hm hm1
  rw [← hδq] at hoff
  have hδ0 : 0 ≤ q.δ₁ := by rw [hδq]; exact (norm_nonneg _).trans (h.entry x y)
  have hEp : ∀ e', LabelRemoval_Ep W S G q e' x y ≤ q.δ₁ := by
    intro e'
    unfold LabelRemoval_Ep
    split_ifs
    · exact hδ0
    · exact (min_le_right _ _).trans (min_le_left _ _)
  unfold LabelRemoval_Om
  split_ifs with hxy
  · linarith [min_le_right (q.t * ((W : ℝ) ^ (-((d : ℝ) / 2)) + q.Φ)) q.δ₁]
  · have h1 := hoff x y hxy
    have h2 := (min_le_right (LabelRemoval_E0 W q x y)
      (min q.δ₁ (3 * q.t * (LabelRemoval_ρR S G x y + q.f)))).trans (min_le_left _ _)
    have h3 := (min_le_right (LabelRemoval_E0 W q x y)
      (min q.δ₁ (3 * q.t * (LabelRemoval_ρC S G x y + q.f)))).trans (min_le_left _ _)
    linarith [hEp a, hEp b]

/-- The entry bound of the majorant: `Ω_{xy} ≤ 5 E₀_{xy}` off the diagonal and
`Ω_{xx} ≤ t (W^{−d/2} + Φ)`. -/
private lemma LabelRemoval_Om_le_entry {m : ℂ} {e : ℝ}
    (h : LabelRemoval_Hyp W S m e q.t q.Φ q.f G) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y ≤ 1) (hδq : q.δ₁ = q.t * (W : ℝ) ^ (-((d : ℝ) / 2) + e))
    (hδ : q.δ₁ ≤ 1 / 8) (hδt : 36 * q.t * q.δ₁ ≤ 1 / 2) (ht : 1 ≤ q.t) (hΦ : 0 ≤ q.Φ)
    (hm : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hf : ∀ x y, q.f ≤ Real.sqrt (bB d L W x y))
    (hf0 : 0 ≤ q.f) (a b x y : Zd d L) :
    (x ≠ y → LabelRemoval_Om W S G q a b x y ≤ 5 * LabelRemoval_E0 W q x y) ∧
      LabelRemoval_Om W S G q a b x x ≤ q.t * ((W : ℝ) ^ (-((d : ℝ) / 2)) + q.Φ) := by
  have hδ0 : 0 ≤ q.δ₁ := by rw [hδq]; exact (norm_nonneg _).trans (h.entry x y)
  have hEp : ∀ e', LabelRemoval_Ep W S G q e' x y ≤ LabelRemoval_E0 W q x y := by
    intro e'
    unfold LabelRemoval_Ep
    split_ifs
    · unfold LabelRemoval_E0; positivity
    · exact min_le_left _ _
  constructor
  · intro hxy
    have h1 : ‖G x y‖ ≤ LabelRemoval_E0 W q x y :=
      h.offdiag hS0 hS1 (hδq ▸ hδ) (hδq ▸ (by linarith)) ht hΦ hm hm1 x y hxy (hf x y) hf0
    unfold LabelRemoval_Om
    rw [if_neg hxy]
    have h2 := min_le_left (LabelRemoval_E0 W q x y)
      (min q.δ₁ (3 * q.t * (LabelRemoval_ρR S G x y + q.f)))
    have h3 := min_le_left (LabelRemoval_E0 W q x y)
      (min q.δ₁ (3 * q.t * (LabelRemoval_ρC S G x y + q.f)))
    linarith [hEp a, hEp b]
  · unfold LabelRemoval_Om
    rw [if_pos rfl]
    exact min_le_left _ _

/-- `(ρ^R_{xy})² = Σ_{k≠x} s_{xk} |G^{(x)}_{ky}|²` for `s ≥ 0`. -/
private lemma LabelRemoval_ρR_sq (hS0 : ∀ x y, 0 ≤ S x y) (x y : Zd d L) :
    LabelRemoval_ρR S G x y ^ 2 = ldeRowRHS S G x y :=
  Real.sq_sqrt (Finset.sum_nonneg fun k _ => mul_nonneg (hS0 _ _) (sq_nonneg _))

/-- `(ρ^C_{xy})² = Σ_{k≠y} s_{yk} |G^{(y)}_{xk}|²` for `s ≥ 0`. -/
private lemma LabelRemoval_ρC_sq (hS0 : ∀ x y, 0 ≤ S x y) (x y : Zd d L) :
    LabelRemoval_ρC S G x y ^ 2 = ldeColRHS S G y x :=
  Real.sq_sqrt (Finset.sum_nonneg fun k _ => mul_nonneg (hS0 _ _) (sq_nonneg _))

omit [NeZero L] in
/-- `K^{d/2} ≤ W^{e − 2} K^{2 + d/2}` for `K ≥ W ≥ 1`, `e ≥ 0`. -/
private lemma LabelRemoval_half_le_scale {W K : ℕ} {e : ℝ} (hW : 1 ≤ W) (hK : W ≤ K)
    (he : 0 ≤ e) : (K : ℝ) ^ ((d : ℝ) / 2) ≤ (W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWK : (W : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have e1 : (W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2) =
      (W : ℝ) ^ e * ((K : ℝ) ^ 2 / (W : ℝ) ^ 2) * (K : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.rpow_sub hW0, Real.rpow_add hK0, Real.rpow_two, Real.rpow_two]; ring
  rw [e1]
  have h1 : 1 ≤ (W : ℝ) ^ e := Real.one_le_rpow hW1 he
  have h2 : 1 ≤ (K : ℝ) ^ 2 / (W : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]; nlinarith
  have h3 : 0 ≤ (K : ℝ) ^ ((d : ℝ) / 2) := by positivity
  nlinarith [one_le_mul_of_one_le_of_one_le h1 h2]

set_option maxHeartbeats 2000000 in
/-- **The box sums of the majorant** ([II, Notation 8.8], averaged part): under the bounds of
`LabelRemoval_Hyp` and the conditions on `S`,
`Σ_{|y − x₀| ≤ K} (Ω_{xy} + Ω_{yx}) ≤ 7000 · 3^{d/2} t³ ρ_b W^{e−2} K^{2+d/2}`. -/
private lemma LabelRemoval_Om_box {m : ℂ} {e : ℝ}
    (h : LabelRemoval_Hyp W S m e q.t q.Φ q.f G) {R sb ρb : ℝ} {Rn : ℕ}
    (hS : LabelRemoval_SCond W S e q.t R sb ρb Rn)
    (hδq : q.δ₁ = q.t * (W : ℝ) ^ (-((d : ℝ) / 2) + e)) (hδ : q.δ₁ ≤ 1 / 8)
    (hΦ : 0 ≤ q.Φ) (hm : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hf0 : 0 ≤ q.f)
    (hfL : 3 ^ d * (L : ℝ) ^ d * q.f ≤ 1) (a b : Zd d L) :
    LabelRemoval_BoxCtl W e (LabelRemoval_Om W S G q a b)
      (7000 * Real.sqrt (3 ^ d) * q.t ^ 3 * ρb) := by
  obtain ⟨hoff, -, hlow, -, hall⟩ := h.basic (hδq ▸ hδ) hm hm1
  rw [← hδq] at hoff
  have ht := hS.t1
  have hρ := hS.ρb1
  have hW := hS.W1
  have hδ0 : 0 ≤ q.δ₁ := by rw [hδq]; positivity
  have hf1 : q.f ≤ 1 := by
    have h3 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    have hL0 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hL : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ hL0
    nlinarith [mul_le_mul h3 hL zero_le_one (by positivity)]
  have hs3 : (1 : ℝ) ≤ Real.sqrt (3 ^ d) := Real.one_le_sqrt.2 (one_le_pow₀ (by norm_num))
  -- the pieces
  set M1 : Matrix (Zd d L) (Zd d L) ℝ := fun x y => ‖G x y‖ with hM1
  set MR : Matrix (Zd d L) (Zd d L) ℝ := fun x y => LabelRemoval_ρR S G x y with hMR
  set MC : Matrix (Zd d L) (Zd d L) ℝ := fun x y => LabelRemoval_ρC S G x y with hMC
  set MF : Matrix (Zd d L) (Zd d L) ℝ := fun _ _ => q.f with hMF
  set MD : Matrix (Zd d L) (Zd d L) ℝ := fun x y => if x = y then q.δ₁ else 0 with hMD
  set MU : Zd d L → Matrix (Zd d L) (Zd d L) ℝ := fun e' x y => ‖G x e'‖ * ‖G e' y‖ with hMU
  set MV : Zd d L → Matrix (Zd d L) (Zd d L) ℝ := fun e' x y =>
    (LabelRemoval_ρC S G x e' + q.f) * (LabelRemoval_ρR S G e' y + q.f) with hMV
  have hρR0 : ∀ x y, 0 ≤ LabelRemoval_ρR S G x y := fun x y => Real.sqrt_nonneg _
  have hρC0 : ∀ x y, 0 ≤ LabelRemoval_ρC S G x y := fun x y => Real.sqrt_nonneg _
  have hrs := fun x x₀ K h1 h2 =>
    LabelRemoval_rho_sq h hS (hδq ▸ hδ) hm hm1 x x₀ K h1 h2
  -- the bounds `ρ ≤ 4`
  have hρR4 : ∀ x y, LabelRemoval_ρR S G x y ≤ 4 := by
    intro x y
    refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    refine (LabelRemoval_rowRHS_le hS.nonneg hS.row hoff hlow x y).trans ?_
    have h1 : ∑ k, S x k * ‖G k y‖ ^ 2 ≤ 4 := by
      calc ∑ k, S x k * ‖G k y‖ ^ 2 ≤ ∑ k, S x k * 4 :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
              (by nlinarith [hall k y, norm_nonneg (G k y)]) (hS.nonneg x k)
        _ = 4 := by rw [← Finset.sum_mul, hS.row x, one_mul]
    have h2 : ‖G x y‖ ^ 2 ≤ 4 := by nlinarith [hall x y, norm_nonneg (G x y)]
    have h3 : 128 * q.δ₁ ^ 2 ≤ 2 := by nlinarith
    nlinarith
  have hρC4 : ∀ x y, LabelRemoval_ρC S G x y ≤ 4 := by
    intro x y
    refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    refine (LabelRemoval_colRHS_le hS.nonneg hS.row hoff hlow y x).trans ?_
    have h1 : ∑ k, S y k * ‖G x k‖ ^ 2 ≤ 4 := by
      calc ∑ k, S y k * ‖G x k‖ ^ 2 ≤ ∑ k, S y k * 4 :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
              (by nlinarith [hall x k, norm_nonneg (G x k)]) (hS.nonneg y k)
        _ = 4 := by rw [← Finset.sum_mul, hS.row y, one_mul]
    have h2 : ‖G x y‖ ^ 2 ≤ 4 := by nlinarith [hall x y, norm_nonneg (G x y)]
    have h3 : 128 * q.δ₁ ^ 2 ≤ 2 := by nlinarith
    nlinarith
  -- `|box| f² ≤ X`
  have hboxf : ∀ (x₀ : Zd d L) (K : ℕ), W ≤ K → 2 * K ≤ L →
      ((LabelRemoval_box x₀ K).card : ℝ) * q.f ^ 2 ≤ (W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4 := by
    intro x₀ K h1 h2
    have hK1 : 1 ≤ K := hW.trans h1
    have hc := LabelRemoval_card_box_le x₀ K hK1
    have hKL : (K : ℝ) ≤ L := by exact_mod_cast (show K ≤ L by omega)
    have h3 : (3 * (K : ℝ)) ^ d ≤ 3 ^ d * (L : ℝ) ^ d := by
      rw [mul_pow]; gcongr
    have hsc := LabelRemoval_one_le_scale hW h1 hS.e0
    have hff : q.f ^ 2 ≤ q.f := by nlinarith
    calc ((LabelRemoval_box x₀ K).card : ℝ) * q.f ^ 2 ≤ 3 ^ d * (L : ℝ) ^ d * q.f :=
          mul_le_mul (hc.trans h3) hff (sq_nonneg _) (by positivity)
      _ ≤ _ := hfL.trans hsc
  -- box control of each piece
  have c1 : LabelRemoval_BoxCtl W e M1 (Real.sqrt (2 * q.t) * Real.sqrt (3 ^ d)) :=
    LabelRemoval_BoxCtl.of_sq (fun _ _ => norm_nonneg _) (by linarith) hW
      fun x x₀ K h1 h2 => h.boxSum hW x x₀ K h1 h2
  have cR : LabelRemoval_BoxCtl W e MR (Real.sqrt (2 * (10 * ρb * q.t)) * Real.sqrt (3 ^ d)) := by
    refine LabelRemoval_BoxCtl.of_sq hρR0 (by positivity) hW fun x x₀ K h1 h2 => ?_
    simp only [hMR, LabelRemoval_ρR_sq hS.nonneg]
    exact (hrs x x₀ K h1 h2).1
  have cC : LabelRemoval_BoxCtl W e MC (Real.sqrt (2 * (10 * ρb * q.t)) * Real.sqrt (3 ^ d)) := by
    refine LabelRemoval_BoxCtl.of_sq hρC0 (by positivity) hW fun x x₀ K h1 h2 => ?_
    simp only [hMC, LabelRemoval_ρC_sq hS.nonneg]
    exact (hrs x x₀ K h1 h2).2
  have cF : LabelRemoval_BoxCtl W e MF 2 := by
    intro x x₀ K h1 h2
    have hK1 : 1 ≤ K := hW.trans h1
    have hc := LabelRemoval_card_box_le x₀ K hK1
    have hKL : (K : ℝ) ≤ L := by exact_mod_cast (show K ≤ L by omega)
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
    have hKd : (K : ℝ) ^ d = (K : ℝ) ^ ((d : ℝ) / 2) * (K : ℝ) ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_add hK0, ← Real.rpow_natCast]; ring_nf
    have hKh : (K : ℝ) ^ ((d : ℝ) / 2) ≤ (L : ℝ) ^ d := by
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
      calc (K : ℝ) ^ ((d : ℝ) / 2) ≤ (L : ℝ) ^ ((d : ℝ) / 2) :=
            Real.rpow_le_rpow hK0.le hKL (by positivity)
        _ ≤ (L : ℝ) ^ (d : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by
            have := Nat.cast_nonneg (α := ℝ) d; linarith)
        _ = (L : ℝ) ^ d := Real.rpow_natCast _ _
    have hsc := LabelRemoval_half_le_scale (d := d) hW h1 hS.e0
    simp only [hMF]
    calc ∑ y ∈ LabelRemoval_box x₀ K, (q.f + q.f) = 2 * q.f * (LabelRemoval_box x₀ K).card := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * q.f * (3 ^ d * ((K : ℝ) ^ ((d : ℝ) / 2) * (K : ℝ) ^ ((d : ℝ) / 2))) := by
          rw [← hKd, ← mul_pow]; exact mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ 2 * (3 ^ d * (L : ℝ) ^ d * q.f) * (K : ℝ) ^ ((d : ℝ) / 2) := by
          have := mul_le_mul_of_nonneg_left hKh (by positivity :
            (0 : ℝ) ≤ 2 * q.f * 3 ^ d * (K : ℝ) ^ ((d : ℝ) / 2))
          nlinarith
      _ ≤ 2 * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) := by
          have h0 : 0 ≤ (K : ℝ) ^ ((d : ℝ) / 2) := by positivity
          nlinarith [mul_le_mul hfL hsc h0 zero_le_one]
  have cD : LabelRemoval_BoxCtl W e MD (2 * q.δ₁) := by
    intro x x₀ K h1 h2
    have hsc := LabelRemoval_one_le_scale hW h1 hS.e0
    have hsc' : 1 ≤ (W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2) := by
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hW.trans h1
      have := LabelRemoval_half_le_scale (d := d) hW h1 hS.e0
      exact (Real.one_le_rpow hK1 (by positivity)).trans this
    have hMD0 : ∀ x y, 0 ≤ MD x y := fun x y => by simp only [hMD]; split_ifs <;> linarith
    calc ∑ y ∈ LabelRemoval_box x₀ K, (MD x y + MD y x)
        ≤ ∑ y, (MD x y + MD y x) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun y _ _ => add_nonneg (hMD0 x y) (hMD0 y x)
      _ = 2 * q.δ₁ := by
          simp only [hMD, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true]
          ring
      _ ≤ 2 * q.δ₁ * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) := by nlinarith
  have cU : ∀ e', LabelRemoval_BoxCtl W e (MU e')
      (Real.sqrt (2 * (8 * q.t)) * Real.sqrt (3 ^ d)) := by
    intro e'
    refine LabelRemoval_BoxCtl.of_sq (fun _ _ => by positivity) (by positivity) hW
      fun x x₀ K h1 h2 => ?_
    have hb := h.boxSum hW e' x₀ K h1 h2
    have hterm : ∀ y, (MU e' x y) ^ 2 + (MU e' y x) ^ 2 ≤
        4 * (‖G e' y‖ ^ 2 + ‖G y e'‖ ^ 2) := by
      intro y
      simp only [hMU, mul_pow]
      have a1 : ‖G x e'‖ ^ 2 ≤ 4 := by nlinarith [hall x e', norm_nonneg (G x e')]
      have a2 : ‖G e' x‖ ^ 2 ≤ 4 := by nlinarith [hall e' x, norm_nonneg (G e' x)]
      nlinarith [mul_le_mul_of_nonneg_right a1 (sq_nonneg ‖G e' y‖),
        mul_le_mul_of_nonneg_left a2 (sq_nonneg ‖G y e'‖)]
    calc ∑ y ∈ LabelRemoval_box x₀ K, ((MU e' x y) ^ 2 + (MU e' y x) ^ 2)
        ≤ ∑ y ∈ LabelRemoval_box x₀ K, 4 * (‖G e' y‖ ^ 2 + ‖G y e'‖ ^ 2) :=
          Finset.sum_le_sum fun y _ => hterm y
      _ ≤ 4 * (q.t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4)) := by
          rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hb (by norm_num)
      _ ≤ 8 * q.t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) := by
          have : 0 ≤ q.t * ((W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4) := by positivity
          nlinarith
  have cV : ∀ e', LabelRemoval_BoxCtl W e (MV e')
      (Real.sqrt (2 * (1100 * ρb * q.t)) * Real.sqrt (3 ^ d)) := by
    intro e'
    refine LabelRemoval_BoxCtl.of_sq (fun x y => mul_nonneg (add_nonneg (hρC0 _ _) hf0)
      (add_nonneg (hρR0 _ _) hf0)) (by positivity) hW fun x x₀ K h1 h2 => ?_
    set X := (W : ℝ) ^ (2 * e - 4) * (K : ℝ) ^ 4 with hX
    have hX0 : 0 ≤ X := by positivity
    have hr := hrs e' x₀ K h1 h2
    have hR : ∑ y ∈ LabelRemoval_box x₀ K, (LabelRemoval_ρR S G e' y) ^ 2 ≤ 10 * ρb * q.t * X := by
      refine le_trans ?_ hr.1
      refine Finset.sum_le_sum fun y _ => ?_
      rw [LabelRemoval_ρR_sq hS.nonneg]
      have : 0 ≤ ldeRowRHS S G y e' := Finset.sum_nonneg fun k _ =>
        mul_nonneg (hS.nonneg _ _) (sq_nonneg _)
      linarith
    have hC : ∑ y ∈ LabelRemoval_box x₀ K, (LabelRemoval_ρC S G y e') ^ 2 ≤ 10 * ρb * q.t * X := by
      refine le_trans ?_ hr.2
      refine Finset.sum_le_sum fun y _ => ?_
      rw [LabelRemoval_ρC_sq hS.nonneg]
      have : 0 ≤ ldeColRHS S G y e' := Finset.sum_nonneg fun k _ =>
        mul_nonneg (hS.nonneg _ _) (sq_nonneg _)
      linarith
    have hfb := hboxf x₀ K h1 h2
    have hu5 : LabelRemoval_ρC S G x e' + q.f ≤ 5 := by linarith [hρC4 x e']
    have hv5 : LabelRemoval_ρR S G e' x + q.f ≤ 5 := by linarith [hρR4 e' x]
    have hterm : ∀ y, (MV e' x y) ^ 2 + (MV e' y x) ^ 2 ≤
        25 * (2 * (LabelRemoval_ρR S G e' y) ^ 2 + 2 * q.f ^ 2) +
          25 * (2 * (LabelRemoval_ρC S G y e') ^ 2 + 2 * q.f ^ 2) := by
      intro y
      simp only [hMV, mul_pow]
      have a1 : (LabelRemoval_ρC S G x e' + q.f) ^ 2 ≤ 25 :=
        pow_le_pow_left₀ (add_nonneg (hρC0 x e') hf0) hu5 2 |>.trans (by norm_num)
      have a2 : (LabelRemoval_ρR S G e' x + q.f) ^ 2 ≤ 25 :=
        pow_le_pow_left₀ (add_nonneg (hρR0 e' x) hf0) hv5 2 |>.trans (by norm_num)
      have b1 : (LabelRemoval_ρR S G e' y + q.f) ^ 2 ≤ 2 * (LabelRemoval_ρR S G e' y) ^ 2 +
          2 * q.f ^ 2 := by nlinarith [sq_nonneg (LabelRemoval_ρR S G e' y - q.f)]
      have b2 : (LabelRemoval_ρC S G y e' + q.f) ^ 2 ≤ 2 * (LabelRemoval_ρC S G y e') ^ 2 +
          2 * q.f ^ 2 := by nlinarith [sq_nonneg (LabelRemoval_ρC S G y e' - q.f)]
      have c1' : (LabelRemoval_ρC S G x e' + q.f) ^ 2 * (LabelRemoval_ρR S G e' y + q.f) ^ 2 ≤
          25 * (2 * (LabelRemoval_ρR S G e' y) ^ 2 + 2 * q.f ^ 2) :=
        mul_le_mul a1 b1 (sq_nonneg _) (by norm_num)
      have c2' : (LabelRemoval_ρC S G y e' + q.f) ^ 2 * (LabelRemoval_ρR S G e' x + q.f) ^ 2 ≤
          25 * (2 * (LabelRemoval_ρC S G y e') ^ 2 + 2 * q.f ^ 2) := by
        rw [mul_comm]; exact mul_le_mul a2 b2 (sq_nonneg _) (by norm_num)
      exact add_le_add c1' c2'
    calc ∑ y ∈ LabelRemoval_box x₀ K, ((MV e' x y) ^ 2 + (MV e' y x) ^ 2)
        ≤ ∑ y ∈ LabelRemoval_box x₀ K, (50 * (LabelRemoval_ρR S G e' y) ^ 2 +
          50 * (LabelRemoval_ρC S G y e') ^ 2 + 100 * q.f ^ 2) :=
          Finset.sum_le_sum fun y _ => (hterm y).trans (le_of_eq (by ring))
      _ = 50 * ∑ y ∈ LabelRemoval_box x₀ K, (LabelRemoval_ρR S G e' y) ^ 2 +
          50 * ∑ y ∈ LabelRemoval_box x₀ K, (LabelRemoval_ρC S G y e') ^ 2 +
          100 * ((LabelRemoval_box x₀ K).card * q.f ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 50 * (10 * ρb * q.t * X) + 50 * (10 * ρb * q.t * X) + 100 * X := by
          linarith [hR, hC, hfb]
      _ ≤ 1100 * ρb * q.t * X := by
          have h' : X ≤ ρb * q.t * X :=
            le_mul_of_one_le_left hX0 (one_le_mul_of_one_le_of_one_le hρ ht)
          linarith
  -- the sum of the pieces dominates the majorant
  set Bsum : Matrix (Zd d L) (Zd d L) ℝ :=
    M1 + (3 * q.t) • (MR + MF) + (3 * q.t) • (MC + MF) +
      (M1 + (8 : ℝ) • MU a + (72 * q.t ^ 2) • MV a) +
      (M1 + (8 : ℝ) • MU b + (72 * q.t ^ 2) • MV b) + MD with hBsum
  have hEpB : ∀ e' x y, LabelRemoval_Ep W S G q e' x y ≤
      M1 x y + 8 * MU e' x y + 72 * q.t ^ 2 * MV e' x y := by
    intro e' x y
    have hV0 : 0 ≤ MV e' x y := mul_nonneg (add_nonneg (hρC0 _ _) hf0) (add_nonneg (hρR0 _ _) hf0)
    have h0 : 0 ≤ M1 x y + 8 * MU e' x y + 72 * q.t ^ 2 * MV e' x y := by
      have : 0 ≤ MU e' x y := by simp only [hMU]; positivity
      have : 0 ≤ M1 x y := norm_nonneg _
      positivity
    unfold LabelRemoval_Ep
    split_ifs
    · exact h0
    · refine ((min_le_right _ _).trans (min_le_right _ _)).trans (le_of_eq ?_)
      simp only [LabelRemoval_Esch, hM1, hMU, hMV]; ring
  have hdom : ∀ x y, LabelRemoval_Om W S G q a b x y ≤ Bsum x y := by
    intro x y
    have hpos : ∀ x y, 0 ≤ M1 x y ∧ 0 ≤ MR x y ∧ 0 ≤ MC x y ∧ 0 ≤ MF x y ∧ 0 ≤ MD x y ∧
        (∀ e', 0 ≤ MU e' x y) ∧ (∀ e', 0 ≤ MV e' x y) := by
      intro x y
      refine ⟨norm_nonneg _, hρR0 x y, hρC0 x y, hf0, ?_, fun e' => by simp only [hMU]; positivity,
        fun e' => mul_nonneg (add_nonneg (hρC0 _ _) hf0) (add_nonneg (hρR0 _ _) hf0)⟩
      simp only [hMD]; split_ifs <;> linarith
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpos x y
    simp only [hBsum, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    unfold LabelRemoval_Om
    split_ifs with hxy
    · have : MD x y = q.δ₁ := by simp [hMD, hxy]
      have hmin := min_le_right (q.t * ((W : ℝ) ^ (-((d : ℝ) / 2)) + q.Φ)) q.δ₁
      have := p6 a; have := p6 b; have := p7 a; have := p7 b
      nlinarith
    · have : MD x y = 0 := by simp [hMD, hxy]
      have m1 := (min_le_right (LabelRemoval_E0 W q x y)
        (min q.δ₁ (3 * q.t * (LabelRemoval_ρR S G x y + q.f)))).trans (min_le_right _ _)
      have m2 := (min_le_right (LabelRemoval_E0 W q x y)
        (min q.δ₁ (3 * q.t * (LabelRemoval_ρC S G x y + q.f)))).trans (min_le_right _ _)
      have ea := hEpB a x y
      have eb := hEpB b x y
      simp only [hMR, hMC, hMF] at m1 m2 ⊢
      nlinarith
  have hB : LabelRemoval_BoxCtl W e Bsum
      (Real.sqrt (2 * q.t) * Real.sqrt (3 ^ d) +
        3 * q.t * (Real.sqrt (2 * (10 * ρb * q.t)) * Real.sqrt (3 ^ d) + 2) +
        3 * q.t * (Real.sqrt (2 * (10 * ρb * q.t)) * Real.sqrt (3 ^ d) + 2) +
        (Real.sqrt (2 * q.t) * Real.sqrt (3 ^ d) +
          8 * (Real.sqrt (2 * (8 * q.t)) * Real.sqrt (3 ^ d)) +
          72 * q.t ^ 2 * (Real.sqrt (2 * (1100 * ρb * q.t)) * Real.sqrt (3 ^ d))) +
        (Real.sqrt (2 * q.t) * Real.sqrt (3 ^ d) +
          8 * (Real.sqrt (2 * (8 * q.t)) * Real.sqrt (3 ^ d)) +
          72 * q.t ^ 2 * (Real.sqrt (2 * (1100 * ρb * q.t)) * Real.sqrt (3 ^ d))) +
        2 * q.δ₁) := by
    have h3t : (0 : ℝ) ≤ 3 * q.t := by linarith
    have h72 : (0 : ℝ) ≤ 72 * q.t ^ 2 := by positivity
    have d1 := (cR.add cF).smul _ h3t
    have d2 := (cC.add cF).smul _ h3t
    have d3 := (c1.add ((cU a).smul 8 (by norm_num))).add ((cV a).smul _ h72)
    have d4 := (c1.add ((cU b).smul 8 (by norm_num))).add ((cV b).smul _ h72)
    exact ((((c1.add d1).add d2).add d3).add d4).add cD
  refine hB.mono hdom ?_
  -- the constant
  have s1 : Real.sqrt (2 * q.t) ≤ 2 * q.t := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have s2 : Real.sqrt (2 * (10 * ρb * q.t)) ≤ 5 * (ρb * q.t) :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [one_le_mul_of_one_le_of_one_le hρ ht]⟩
  have s3 : Real.sqrt (2 * (8 * q.t)) ≤ 4 * q.t := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have s4 : Real.sqrt (2 * (1100 * ρb * q.t)) ≤ 47 * (ρb * q.t) :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [one_le_mul_of_one_le_of_one_le hρ ht]⟩
  set r := Real.sqrt (3 ^ d)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hρt : 1 ≤ ρb * q.t := one_le_mul_of_one_le_of_one_le hρ ht
  have ht2 : q.t ≤ q.t ^ 2 := by nlinarith
  have ht3 : q.t ^ 2 ≤ q.t ^ 3 := by nlinarith
  have k1 : Real.sqrt (2 * q.t) * r ≤ 2 * q.t * r := mul_le_mul_of_nonneg_right s1 hr0
  have k2 : Real.sqrt (2 * (10 * ρb * q.t)) * r ≤ 5 * (ρb * q.t) * r :=
    mul_le_mul_of_nonneg_right s2 hr0
  have k3 : Real.sqrt (2 * (8 * q.t)) * r ≤ 4 * q.t * r := mul_le_mul_of_nonneg_right s3 hr0
  have k4 : Real.sqrt (2 * (1100 * ρb * q.t)) * r ≤ 47 * (ρb * q.t) * r :=
    mul_le_mul_of_nonneg_right s4 hr0
  have hfin : q.t * r ≤ q.t ^ 3 * ρb * r := by
    have : q.t ≤ q.t ^ 3 * ρb := by nlinarith
    exact mul_le_mul_of_nonneg_right this hr0
  have hfin2 : q.t ^ 2 * (ρb * q.t) * r = q.t ^ 3 * ρb * r := by ring
  have hfin3 : q.t * (ρb * q.t) * r ≤ q.t ^ 3 * ρb * r := by
    have : q.t * (ρb * q.t) ≤ q.t ^ 3 * ρb := by nlinarith
    exact mul_le_mul_of_nonneg_right this hr0
  have hfin4 : q.t ≤ q.t ^ 3 * ρb * r := by nlinarith
  have hfin5 : 1 ≤ q.t ^ 3 * ρb * r := by nlinarith
  have h3t : (0 : ℝ) ≤ 3 * q.t := by linarith
  have h72 : (0 : ℝ) ≤ 72 * q.t ^ 2 := by positivity
  have l2 := mul_le_mul_of_nonneg_left k2 h3t
  have l4 := mul_le_mul_of_nonneg_left k4 h72
  have l3 := mul_le_mul_of_nonneg_left k3 (by norm_num : (0 : ℝ) ≤ 8)
  nlinarith

/-- The common hypotheses of the comparison of the entries of `G` and of the resampled resolvents
with `G̃`. -/
private structure LabelRemoval_Cmp (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (m : ℂ) (e : ℝ)
    (q : LabelRemoval_Par) : Prop where
  S0 : ∀ x y, 0 ≤ S x y
  S1 : ∀ x, ∑ y, S x y ≤ 1
  δq : q.δ₁ = q.t * (W : ℝ) ^ (-((d : ℝ) / 2) + e)
  δ8 : q.δ₁ ≤ 1 / 8
  δt : 36 * q.t * q.δ₁ ≤ 1 / 2
  t1 : 1 ≤ q.t
  Φ0 : 0 ≤ q.Φ
  m4 : 1 / 4 ≤ ‖m‖
  m1 : ‖m‖ ≤ 1
  fB : ∀ x y, q.f ≤ Real.sqrt (bB d L W x y)
  f0 : 0 ≤ q.f

/-- If the minors at `y` of `G` and `G'` agree, so do the conditional variances of row and column
`y`. -/
private lemma LabelRemoval_rhs_congr {S : Matrix (Zd d L) (Zd d L) ℝ}
    {G G' : Matrix (Zd d L) (Zd d L) ℂ} (y : Zd d L)
    (hmin : ∀ k l, greenMinor G' y k l = greenMinor G y k l) (a : Zd d L) :
    ldeRowRHS S G' y a = ldeRowRHS S G y a ∧ ldeColRHS S G' y a = ldeColRHS S G y a := by
  unfold ldeRowRHS ldeColRHS
  simp only [hmin]
  exact ⟨trivial, trivial⟩

/-- **The entries of a resampled resolvent against the majorant**: for `G'` with the bounds of
`LabelRemoval_Hyp` and the same minor at `y` as `G`: `|G'_{yb}| ≤ Ω_{yb}`, `|G'_{ay}| ≤ Ω_{ay}`,
`|G'_{xx} − m| ≤ Ω_{xx}`, the Schur bound `|G'_{ab}| ≤ Ω_{ab} + 8 Ω_{ay} Ω_{yb}` for distinct
`a, b ≠ y`, and `|G'_{ab}| ≤ Ω_{ab}` if `y` is one of the external indices. -/
private lemma LabelRemoval_dom_res {m : ℂ} {e : ℝ} (hc : LabelRemoval_Cmp W S m e q)
    (hG : LabelRemoval_Hyp W S m e q.t q.Φ q.f G) {G' : Matrix (Zd d L) (Zd d L) ℂ}
    (hG' : LabelRemoval_Hyp W S m e q.t q.Φ q.f G') (y : Zd d L)
    (hmin : ∀ k l, greenMinor G' y k l = greenMinor G y k l) (a₀ b₀ : Zd d L) :
    (∀ b, b ≠ y → ‖G' y b‖ ≤ LabelRemoval_Om W S G q a₀ b₀ y b) ∧
    (∀ a, a ≠ y → ‖G' a y‖ ≤ LabelRemoval_Om W S G q a₀ b₀ a y) ∧
    (∀ x, ‖G' x x - m‖ ≤ LabelRemoval_Om W S G q a₀ b₀ x x) ∧
    (∀ a b, a ≠ b → a ≠ y → b ≠ y → ‖G' a b‖ ≤ LabelRemoval_Om W S G q a₀ b₀ a b +
      8 * (LabelRemoval_Om W S G q a₀ b₀ a y * LabelRemoval_Om W S G q a₀ b₀ y b)) ∧
    ((y = a₀ ∨ y = b₀) → ∀ a b, a ≠ b → a ≠ y → b ≠ y →
      ‖G' a b‖ ≤ LabelRemoval_Om W S G q a₀ b₀ a b) := by
  have hδ' : q.t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) ≤ 1 / 8 := hc.δq ▸ hc.δ8
  obtain ⟨hoff, hdd, hlow, hup, hall⟩ := hG.basic hδ' hc.m4 hc.m1
  obtain ⟨hoff', hdd', hlow', hup', hall'⟩ := hG'.basic hδ' hc.m4 hc.m1
  rw [← hc.δq] at hoff hdd hoff' hdd'
  have hδ0 : 0 ≤ q.δ₁ := (norm_nonneg _).trans (hdd y)
  have ht0 : 0 ≤ q.t := by linarith [hc.t1]
  have hOm0 := fun x y => LabelRemoval_Om_nonneg (W := W) (S := S) (G := G) ht0 hδ0 hc.Φ0 hc.f0
    a₀ b₀ x y
  have hE0 : ∀ x y, x ≠ y → ‖G' x y‖ ≤ LabelRemoval_E0 W q x y := fun x y hxy =>
    hG'.offdiag hc.S0 hc.S1 hδ' (hc.δq ▸ (by linarith [hc.δt])) hc.t1 hc.Φ0 hc.m4 hc.m1 x y hxy
      (hc.fB x y) hc.f0
  have hEp0 : ∀ e' x y, 0 ≤ LabelRemoval_Ep W S G q e' x y := by
    intro e' x y
    unfold LabelRemoval_Ep LabelRemoval_Esch
    split_ifs
    · exact le_rfl
    · refine le_min (by unfold LabelRemoval_E0; have := hc.Φ0; positivity) (le_min hδ0 ?_)
      have := hc.f0
      have : 0 ≤ LabelRemoval_ρC S G x e' := Real.sqrt_nonneg _
      have : 0 ≤ LabelRemoval_ρR S G e' y := Real.sqrt_nonneg _
      positivity
  have hρR0 : ∀ x z : Zd d L, 0 ≤ LabelRemoval_ρR S G x z := fun _ _ => Real.sqrt_nonneg _
  have hρC0 : ∀ x z : Zd d L, 0 ≤ LabelRemoval_ρC S G x z := fun _ _ => Real.sqrt_nonneg _
  have hEnn : ∀ x z : Zd d L, 0 ≤ LabelRemoval_E0 W q x z := fun x z => by
    unfold LabelRemoval_E0; have := hc.Φ0; positivity
  have hminR : ∀ x z : Zd d L, 0 ≤ min (LabelRemoval_E0 W q x z)
      (min q.δ₁ (3 * q.t * (LabelRemoval_ρR S G x z + q.f))) := fun x z =>
    le_min (hEnn x z) (le_min hδ0 (by have := hρR0 x z; have := hc.f0; positivity))
  have hminC : ∀ x z : Zd d L, 0 ≤ min (LabelRemoval_E0 W q x z)
      (min q.δ₁ (3 * q.t * (LabelRemoval_ρC S G x z + q.f))) := fun x z =>
    le_min (hEnn x z) (le_min hδ0 (by have := hρC0 x z; have := hc.f0; positivity))
  -- the resampled row and column
  have hrow : ∀ b, b ≠ y → ‖G' y b‖ ≤ 3 * q.t * (LabelRemoval_ρR S G y b + q.f) := by
    intro b hb
    have h1 := hG'.row y b (Ne.symm hb)
    rw [(LabelRemoval_rhs_congr (S := S) y hmin b).1] at h1
    have h3 : ‖G' y y‖ + 1 ≤ 3 := by linarith [hup' y]
    have h0 : 0 ≤ LabelRemoval_ρR S G y b + q.f := add_nonneg (Real.sqrt_nonneg _) hc.f0
    calc ‖G' y b‖ ≤ q.t * ((‖G' y y‖ + 1) * (LabelRemoval_ρR S G y b + q.f)) := h1
      _ ≤ q.t * (3 * (LabelRemoval_ρR S G y b + q.f)) := by gcongr
      _ = _ := by ring
  have hcol : ∀ a, a ≠ y → ‖G' a y‖ ≤ 3 * q.t * (LabelRemoval_ρC S G a y + q.f) := by
    intro a ha
    have h1 := hG'.col y a (Ne.symm ha)
    rw [(LabelRemoval_rhs_congr (S := S) y hmin a).2] at h1
    have h3 : ‖G' y y‖ + 1 ≤ 3 := by linarith [hup' y]
    have h0 : 0 ≤ LabelRemoval_ρC S G a y + q.f := add_nonneg (Real.sqrt_nonneg _) hc.f0
    calc ‖G' a y‖ ≤ q.t * ((‖G' y y‖ + 1) * (LabelRemoval_ρC S G a y + q.f)) := h1
      _ ≤ q.t * (3 * (LabelRemoval_ρC S G a y + q.f)) := by gcongr
      _ = _ := by ring
  -- the pieces of `Ω` off the diagonal
  have hOm_off : ∀ x z, x ≠ z → LabelRemoval_Om W S G q a₀ b₀ x z =
      ‖G x z‖ +
        min (LabelRemoval_E0 W q x z) (min q.δ₁ (3 * q.t * (LabelRemoval_ρR S G x z + q.f))) +
        min (LabelRemoval_E0 W q x z) (min q.δ₁ (3 * q.t * (LabelRemoval_ρC S G x z + q.f))) +
        LabelRemoval_Ep W S G q a₀ x z + LabelRemoval_Ep W S G q b₀ x z := by
    intro x z hxz; unfold LabelRemoval_Om; rw [if_neg hxz]
  have hR : ∀ b, b ≠ y → ‖G y b‖ + ‖G' y b‖ ≤ LabelRemoval_Om W S G q a₀ b₀ y b := by
    intro b hb
    rw [hOm_off y b (Ne.symm hb)]
    have h1 : ‖G' y b‖ ≤ min (LabelRemoval_E0 W q y b)
        (min q.δ₁ (3 * q.t * (LabelRemoval_ρR S G y b + q.f))) :=
      le_min (hE0 y b (Ne.symm hb)) (le_min (hoff' y b (Ne.symm hb)) (hrow b hb))
    have h2 := hminC y b
    linarith [hEp0 a₀ y b, hEp0 b₀ y b]
  have hC : ∀ a, a ≠ y → ‖G a y‖ + ‖G' a y‖ ≤ LabelRemoval_Om W S G q a₀ b₀ a y := by
    intro a ha
    rw [hOm_off a y ha]
    have h1 : ‖G' a y‖ ≤ min (LabelRemoval_E0 W q a y)
        (min q.δ₁ (3 * q.t * (LabelRemoval_ρC S G a y + q.f))) :=
      le_min (hE0 a y ha) (le_min (hoff' a y ha) (hcol a ha))
    have h2 := hminR a y
    linarith [hEp0 a₀ a y, hEp0 b₀ a y]
  have hGab : ∀ a b, a ≠ b → ‖G a b‖ ≤ LabelRemoval_Om W S G q a₀ b₀ a b := by
    intro a b hab
    rw [hOm_off a b hab]
    have h2 := hminR a b
    have h3 := hminC a b
    linarith [hEp0 a₀ a b, hEp0 b₀ a b]
  refine ⟨fun b hb => by linarith [hR b hb, norm_nonneg (G y b)],
    fun a ha => by linarith [hC a ha, norm_nonneg (G a y)], ?_, ?_, ?_⟩
  · intro x
    unfold LabelRemoval_Om
    rw [if_pos rfl]
    exact le_min (hG'.diag x) (hdd' x)
  · intro a b hab ha hb
    have hs := LabelRemoval_schur_le G G' y a b (hmin a b) (hlow y) (hlow' y)
    have h1 := hC a ha
    have h2 := hR b hb
    have h3 := hGab a b hab
    have hp : ‖G a y‖ * ‖G y b‖ + ‖G' a y‖ * ‖G' y b‖ ≤
        LabelRemoval_Om W S G q a₀ b₀ a y * LabelRemoval_Om W S G q a₀ b₀ y b := by
      have := mul_le_mul h1 h2 (by positivity) (hOm0 a y)
      nlinarith [norm_nonneg (G a y), norm_nonneg (G y b), norm_nonneg (G' a y),
        norm_nonneg (G' y b)]
    linarith
  · intro hy a b hab ha hb
    have hs := LabelRemoval_schur_le G G' y a b (hmin a b) (hlow y) (hlow' y)
    have hEp : ‖G' a b‖ ≤ LabelRemoval_Ep W S G q y a b := by
      unfold LabelRemoval_Ep
      rw [if_neg (by tauto)]
      refine le_min (hE0 a b hab) (le_min (hoff' a b hab) ?_)
      unfold LabelRemoval_Esch
      have hc1 := hcol a ha
      have hr1 := hrow b hb
      have hp : ‖G' a y‖ * ‖G' y b‖ ≤
          9 * q.t ^ 2 * ((LabelRemoval_ρC S G a y + q.f) * (LabelRemoval_ρR S G y b + q.f)) := by
        have := mul_le_mul hc1 hr1 (norm_nonneg _) (by
          have := hc.f0; have : 0 ≤ LabelRemoval_ρC S G a y := Real.sqrt_nonneg _; positivity)
        nlinarith
      linarith
    rw [hOm_off a b hab]
    have h2 := hminR a b
    have h3 := hminC a b
    rcases hy with rfl | rfl
    · linarith [hEp0 b₀ a b, norm_nonneg (G a b)]
    · linarith [hEp0 a₀ a b, norm_nonneg (G a b)]

end Majorant

/-! ## The data record of the model and the data record at a single matrix -/

section Data

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `(Ring.inverse B)` commutes with the complexification of a real matrix. -/
private lemma LabelRemoval_cmat_ringInverse (B : Matrix ι ι ℝ) :
    cmat (Ring.inverse B) = Ring.inverse (cmat B) := by
  let f : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  change f (Ring.inverse B) = Ring.inverse (f B)
  by_cases h : IsUnit B
  · obtain ⟨u, rfl⟩ := h
    have : f (u : Matrix ι ι ℝ) = ((Units.map f.toMonoidHom u : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) :=
      rfl
    rw [this, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have h' : ¬ IsUnit (f B) := by
      intro h2
      apply h
      rw [Matrix.isUnit_iff_isUnit_det] at h2 ⊢
      rw [isUnit_iff_ne_zero] at h2 ⊢
      intro h0
      apply h2
      have := RingHom.map_det Complex.ofRealHom B
      change Complex.ofRealHom B.det = (f B).det at this
      rw [← this, h0, map_zero]
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h']
    ext i j
    simp

/-- `cmat Θ = |m|² S (1 − |m|² S)⁻¹` over `ℂ`. -/
private lemma LabelRemoval_cmat_Theta (S : Matrix ι ι ℝ) (m : ℂ) :
    cmat (Theta m S) =
      (((‖m‖ : ℂ) ^ 2) • cmat S) * Ring.inverse (1 - ((‖m‖ : ℂ) ^ 2) • cmat S) := by
  have h1 : ∀ T : Matrix ι ι ℝ, cmat (‖m‖ ^ 2 • T) = ((‖m‖ : ℂ) ^ 2) • cmat T := fun T => by
    ext i j
    simp [cmat]
  have h2 : cmat (1 - ‖m‖ ^ 2 • S) = 1 - ((‖m‖ : ℂ) ^ 2) • cmat S := by
    ext i j
    simp only [cmat, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
    split_ifs <;> simp
  have h3 : ∀ A B : Matrix ι ι ℝ, cmat (A * B) = cmat A * cmat B := fun A B =>
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [Theta, h3, LabelRemoval_cmat_ringInverse, h1, h2]

end Data

/-- The deterministic fields of the data record of the model are those of the data record at a
single matrix, and its resolvent field without minor is `G(ω)`: every component of the kinds of
[II, Def 3.2], and every weight `W_d` without minor, has the same value on `rbmData` and on
`gData` at `G = G(ω)`. -/
private lemma LabelRemoval_val_rbm {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (ω : Sample (Zd d L)) {V : Type*} (σ : V → Zd d L) (N : ℕ) (c : Comp V)
    (hc : c.isTKind N = true ∨ (c.minor = [] ∧ c.kind.isWD = true)) :
    Comp.val (rbmData d P Sig W L z ω) σ c =
      Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) σ c := by
  have hmin : c.minor = [] := by
    rcases hc with hc | ⟨hc, -⟩
    · have := hc; simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at this
      exact this.1
    · exact hc
  have hGm : (rbmData d P Sig W L z ω).Gm ((c.minor.map σ).toFinset) = green (hmat ω) z := by
    rw [hmin]
    simp only [rbmData, modelData, List.map_nil, List.toFinset_nil]
    rw [dif_neg]
    rintro ⟨x, hx⟩
    exact (Finset.singleton_ne_empty x) hx.symm
  have hSp : (rbmData d P Sig W L z ω).Sp = (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).Sp := by
    simp only [rbmData, modelData, gData, detData, Splus, cmat, Matrix.nonsing_inv_eq_ringInverse]
  have hTh : (rbmData d P Sig W L z ω).Theta =
      (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).Theta := by
    simp only [rbmData, modelData, gData, detData]
    rw [LabelRemoval_cmat_Theta, Matrix.nonsing_inv_eq_ringInverse]
    push_cast
    rfl
  have hSig : (rbmData d P Sig W L z ω).Sig = (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).Sig :=
    rfl
  have hchain : ∀ o, (rbmData d P Sig W L z ω).chain o =
      (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).chain o := by
    intro o; unfold Data.chain; rw [hTh, hSig]
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ with
  | G ch => simp only [Comp.val] at hGm ⊢; rw [hGm]; rfl
  | weight ch => simp only [Comp.val] at hGm ⊢; rw [hGm]; rfl
  | light ch => simp only [Comp.val] at hGm ⊢; rw [hGm]; rfl
  | waved w =>
    cases w with
    | s => rfl
    | plus => simp only [Comp.val]; rw [hSp]
    | minus =>
      have hSm : (rbmData d P Sig W L z ω).Sm =
          (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).Sm := by
        simp only [rbmData, modelData, gData, detData, Sminus, Splus, cmat,
          Matrix.nonsing_inv_eq_ringInverse]
        rfl
      simp only [Comp.val]; rw [hSm]
  | theta o => simp only [Comp.val]; rw [hchain]
  | dot => rfl
  | xdot => rfl
  | inv ch => rcases hc with hc | ⟨-, hc⟩ <;> simp [Comp.isTKind, Kind.isWD] at hc
  | wD ch D => simp only [Comp.val] at hGm ⊢; rw [hGm]; rfl
  | thetaErr n D => rcases hc with hc | ⟨-, hc⟩ <;> simp [Comp.isTKind, Kind.isWD] at hc
  | ghost => rcases hc with hc | ⟨-, hc⟩ <;> simp [Comp.isTKind, Kind.isWD] at hc
  | aux j r b => rcases hc with hc | ⟨-, hc⟩ <;> simp [Comp.isTKind, Kind.isWD] at hc

/-! ## One component: the resampled resolvent against the single matrix -/

section Comp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The charge does not change the modulus. -/
private lemma LabelRemoval_norm_apply (ch : Charge) (w : ℂ) : ‖ch.apply w‖ = ‖w‖ := by
  cases ch
  · rfl
  · exact norm_star w

/-- The path term of a component of `Γ` at the labelling `σ`: for a component replaced by the path
through its label atom `v` (`Graph.pathEligB`), the product of the moduli of the factors of
`Comp.pathVia`; otherwise `0`. -/
private def LabelRemoval_Y {n : ℕ} (Γ : Graph 3 n) (D : Data ι) (σ : Atom 3 n → ι)
    (c : Comp (Atom 3 n)) : ℝ :=
  match c.label with
  | some (_, v) =>
    if Γ.pathEligB c = true then ((c.pathVia v).map fun c' => ‖Comp.val D σ c'‖).prod else 0
  | none => 0

private lemma LabelRemoval_Y_nonneg {n : ℕ} (Γ : Graph 3 n) (D : Data ι) (σ : Atom 3 n → ι)
    (c : Comp (Atom 3 n)) : 0 ≤ LabelRemoval_Y Γ D σ c := by
  unfold LabelRemoval_Y
  rcases c.label with _ | ⟨_, v⟩
  · exact le_rfl
  · simp only
    split_ifs
    · exact List.prod_nonneg fun a ha => by
        obtain ⟨c', -, rfl⟩ := List.mem_map.1 ha; exact norm_nonneg _
    · exact le_rfl

/-- A deterministic component has the same value at any two matrices. -/
private lemma LabelRemoval_val_det (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2)
    (G₁ G₂ : Matrix ι ι ℂ) {V : Type*} (σ : V → ι) (c : Comp V) (hc : c.kind.isRandom = false) :
    Comp.val (gData S z Sig G₁) σ c = Comp.val (gData S z Sig G₂) σ c := by
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> (try cases ‹Wave›) <;> first | rfl | simp [Kind.isRandom] at hc

/-- **The comparison of one component** at two matrices: if `|G₁_{ab}| ≤ |G₂_{ab}|` and
`|G₁_{aa} − m| ≤ |G₂_{aa} − m|`, then the factor at `G₁` is at most the factor at `G₂`. -/
private lemma LabelRemoval_val_mono (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2)
    (G₁ G₂ : Matrix ι ι ℂ) (h1 : ∀ a b, ‖G₁ a b‖ ≤ ‖G₂ a b‖)
    (h2 : ∀ a, ‖G₁ a a - msc z‖ ≤ ‖G₂ a a - msc z‖) {V : Type*} (σ : V → ι) (N : ℕ)
    (c : Comp V) (hc : c.isTKind N = true) :
    ‖Comp.val (gData S z Sig G₁) σ c‖ ≤ ‖Comp.val (gData S z Sig G₂) σ c‖ := by
  by_cases hr : c.kind.isRandom = true
  · obtain ⟨κ, x, y, mi, l⟩ := c
    cases κ with
    | G ch => simp only [Comp.val, gData, LabelRemoval_norm_apply]; exact h1 _ _
    | weight ch => simp only [Comp.val, gData, LabelRemoval_norm_apply]; exact h1 _ _
    | light ch => simp only [Comp.val, gData, detData, LabelRemoval_norm_apply]; exact h2 _
    | _ => simp [Comp.isTKind, Kind.isRandom] at hc hr
  · rw [LabelRemoval_val_det S z Sig G₁ G₂ σ c (by simpa using hr)]

/-- **The comparison of a labelled component with the resampled resolvent**: for a component with
the label atom `v` and `y = σ(v)`, if `G'` satisfies the bounds of `LabelRemoval_dom_res` against
`G̃` (diagonal, row `y`, column `y`, the Schur bound off row and column `y`, and the bound without
path term when the label atom is dotted to an external atom), then the factor at `G'` is at most
the factor at `G̃` plus the path term at `G̃`. -/
private lemma LabelRemoval_val_res {n : ℕ} (Γ : Graph 3 n) (S : Matrix ι ι ℝ) (z : ℂ)
    (Sig : ℕ → Expansion 2) (G' Gt : Matrix ι ι ℂ) (σ : Atom 3 n → ι) (N : ℕ)
    (c : Comp (Atom 3 n)) (hc : c.isTKind N = true) (pq : PQ) (v : Atom 3 n)
    (hl : c.label = some (pq, v))
    (h1 : ∀ a, ‖G' a a‖ ≤ ‖Gt a a‖) (h2 : ∀ a, ‖G' a a - msc z‖ ≤ ‖Gt a a - msc z‖)
    (h3 : ∀ b, b ≠ σ v → ‖G' (σ v) b‖ ≤ ‖Gt (σ v) b‖)
    (h4 : ∀ a, a ≠ σ v → ‖G' a (σ v)‖ ≤ ‖Gt a (σ v)‖)
    (h5 : ∀ a b, a ≠ b → a ≠ σ v → b ≠ σ v → ‖G' a b‖ ≤ ‖Gt a b‖ + ‖Gt a (σ v)‖ * ‖Gt (σ v) b‖)
    (h6 : Γ.labelFixedB v = true → ∀ a b, a ≠ b → a ≠ σ v → b ≠ σ v → ‖G' a b‖ ≤ ‖Gt a b‖) :
    ‖Comp.val (gData S z Sig G') σ c‖ ≤
      ‖Comp.val (gData S z Sig Gt) σ c‖ + LabelRemoval_Y Γ (gData S z Sig Gt) σ c := by
  have hY := LabelRemoval_Y_nonneg Γ (gData S z Sig Gt) σ c
  by_cases hr : c.kind.isRandom = true
  · obtain ⟨κ, x, y, mi, l⟩ := c
    simp only at hl
    subst hl
    cases κ with
    | G ch =>
      have hval : ∀ G : Matrix ι ι ℂ, Comp.val (gData S z Sig G) σ
          ⟨.G ch, x, y, mi, some (pq, v)⟩ = ch.apply (G (σ x) (σ y)) := fun G => rfl
      rw [hval, hval, LabelRemoval_norm_apply, LabelRemoval_norm_apply]
      by_cases hab : σ x = σ y
      · rw [hab]; linarith [h1 (σ y)]
      by_cases ha : σ x = σ v
      · rw [ha]; linarith [h3 (σ y) (by rw [← ha]; exact Ne.symm hab)]
      by_cases hb : σ y = σ v
      · rw [hb]; linarith [h4 (σ x) (by rw [← hb]; exact hab)]
      by_cases hp : Γ.pathEligB ⟨.G ch, x, y, mi, some (pq, v)⟩ = true
      · have hYv : LabelRemoval_Y Γ (gData S z Sig Gt) σ ⟨.G ch, x, y, mi, some (pq, v)⟩ =
            ‖Gt (σ x) (σ v)‖ * ‖Gt (σ v) (σ y)‖ := by
          unfold LabelRemoval_Y
          have e1 : Comp.val (gData S z Sig Gt) σ (⟨.G ch, x, v, [], none⟩ : Comp (Atom 3 n)) =
              ch.apply (Gt (σ x) (σ v)) := rfl
          have e2 : Comp.val (gData S z Sig Gt) σ (⟨.G ch, v, y, [], none⟩ : Comp (Atom 3 n)) =
              ch.apply (Gt (σ v) (σ y)) := rfl
          have e3 : Comp.val (gData S z Sig Gt) σ (⟨.xdot, x, v, [], none⟩ : Comp (Atom 3 n)) =
              if σ x = σ v then 0 else 1 := rfl
          have e4 : Comp.val (gData S z Sig Gt) σ (⟨.xdot, v, y, [], none⟩ : Comp (Atom 3 n)) =
              if σ v = σ y then 0 else 1 := rfl
          simp only [hp, if_true, Comp.pathVia, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil, e1, e2, e3, e4, LabelRemoval_norm_apply, if_neg ha,
            if_neg (Ne.symm hb), norm_one, mul_one]
        rw [hYv]
        exact h5 _ _ hab ha hb
      · have hfix : Γ.labelFixedB v = true := by
          by_contra hf
          apply hp
          simp only [Graph.pathEligB, Kind.isRandom, Bool.true_and, Bool.and_eq_true,
            Bool.not_eq_true', bne_iff_ne, ne_eq]
          refine ⟨⟨by simpa using hf, fun h => ha (by rw [h])⟩, fun h => hb (by rw [h])⟩
        linarith [h6 hfix _ _ hab ha hb]
    | weight ch =>
      have hval : ∀ G : Matrix ι ι ℂ, Comp.val (gData S z Sig G) σ
          ⟨.weight ch, x, y, mi, some (pq, v)⟩ = ch.apply (G (σ x) (σ x)) := fun G => rfl
      rw [hval, hval, LabelRemoval_norm_apply, LabelRemoval_norm_apply]; linarith [h1 (σ x)]
    | light ch =>
      have hval : ∀ G : Matrix ι ι ℂ, Comp.val (gData S z Sig G) σ
          ⟨.light ch, x, y, mi, some (pq, v)⟩ = ch.apply (G (σ x) (σ x) - msc z) := fun G => rfl
      rw [hval, hval, LabelRemoval_norm_apply, LabelRemoval_norm_apply]; linarith [h2 (σ x)]
    | _ => simp [Comp.isTKind, Kind.isRandom] at hc hr
  · rw [LabelRemoval_val_det S z Sig G' Gt σ c (by simpa using hr)]
    linarith

/-- The factor of a random component is at most `M` if `|G_{ab}| ≤ M − 1` and `|m| ≤ 1`. -/
private lemma LabelRemoval_val_le_M (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2)
    (G : Matrix ι ι ℂ) (M : ℝ) (hG : ∀ a b, ‖G a b‖ ≤ M - 1) (hm : ‖msc z‖ ≤ 1)
    {V : Type*} (σ : V → ι) (N : ℕ) (c : Comp V) (hc : c.isTKind N = true)
    (hr : c.kind.isRandom = true) : ‖Comp.val (gData S z Sig G) σ c‖ ≤ M := by
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ with
  | G ch => simp only [Comp.val, gData, LabelRemoval_norm_apply]; linarith [hG (σ x) (σ y)]
  | weight ch => simp only [Comp.val, gData, LabelRemoval_norm_apply]; linarith [hG (σ x) (σ x)]
  | light ch =>
    simp only [Comp.val, gData, detData, LabelRemoval_norm_apply]
    linarith [norm_sub_le (G (σ x) (σ x)) (msc z), hG (σ x) (σ x)]
  | _ => simp [Comp.isTKind, Kind.isRandom] at hc hr

/-- The factor of a random component at `G̃` is at least `lo` if all `|G̃_{ab}|` and
`|G̃_{aa} − m|` are. -/
private lemma LabelRemoval_val_ge (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2)
    (G : Matrix ι ι ℂ) (lo : ℝ) (h1 : ∀ a b, lo ≤ ‖G a b‖) (h2 : ∀ a, lo ≤ ‖G a a - msc z‖)
    {V : Type*} (σ : V → ι) (N : ℕ) (c : Comp V) (hc : c.isTKind N = true)
    (hr : c.kind.isRandom = true) : lo ≤ ‖Comp.val (gData S z Sig G) σ c‖ := by
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ with
  | G ch => simp only [Comp.val, gData, LabelRemoval_norm_apply]; exact h1 _ _
  | weight ch => simp only [Comp.val, gData, LabelRemoval_norm_apply]; exact h1 _ _
  | light ch => simp only [Comp.val, gData, detData, LabelRemoval_norm_apply]; exact h2 _
  | _ => simp [Comp.isTKind, Kind.isRandom] at hc hr

/-- A deterministic component is not a weight `W_d` and is its own light weight. -/
private lemma LabelRemoval_det_wD {V : Type*} (c : Comp V) (h : c.kind.isRandom = false) :
    c.kind.isWD = false ∧ c.kind.wDDeg = 0 ∧ c.wDLight = c := by
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> simp_all [Kind.isRandom, Kind.isWD, Kind.wDDeg, Comp.wDLight, Kind.wDL]

/-- The light weight of a random component is random. -/
private lemma LabelRemoval_light_random {V : Type*} (c : Comp V) (h : c.kind.isRandom = true) :
    c.wDLight.kind.isRandom = true := by
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> simp_all [Kind.isRandom, Comp.wDLight, Kind.wDL]

/-- The components of the kinds of `Err` (`Graph.TKindsErr`): a kind of [II, Def 3.2], or a
weight `W_d` without minor. -/
private lemma LabelRemoval_errKind {k n : ℕ} {Γ : Graph k n} {N : ℕ} (h : Γ.TKindsErr N)
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) :
    c.isTKind N = true ∨ (c.minor = [] ∧ c.kind.isWD = true) := by
  have := List.all_eq_true.1 h c hc
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> simp_all [Comp.isTKind, Kind.isWD]

/-- The light weight of a component of the kinds of `Err` has a kind of [II, Def 3.2]. -/
private lemma LabelRemoval_light_tKind {V : Type*} {N : ℕ} {c : Comp V}
    (h : c.isTKind N = true ∨ (c.minor = [] ∧ c.kind.isWD = true)) :
    c.wDLight.isTKind N = true := by
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> simp_all [Comp.isTKind, Kind.isWD, Comp.wDLight, Kind.wDL]

/-- The constant `2 |m|^{−(d+2)}` of a weight `W_d` (`1` for the other kinds) is at least `1`
for `1/4 ≤ |m| ≤ 1`, and at most `2 · 4^{d+2}`. -/
private lemma LabelRemoval_Cc (z : ℂ) (hm : ‖msc z‖ ≤ 1) (hm4 : 1 / 4 ≤ ‖msc z‖) (κ : Kind) :
    1 ≤ (if κ.isWD then 2 * ‖msc z‖⁻¹ ^ (κ.wDDeg + 2) else 1) ∧
      (if κ.isWD then 2 * ‖msc z‖⁻¹ ^ (κ.wDDeg + 2) else 1) ≤
        (if κ.isWD then 2 * 4 ^ (κ.wDDeg + 2) else 1) := by
  have hm0 : 0 < ‖msc z‖ := by linarith
  have h1 : 1 ≤ ‖msc z‖⁻¹ := by rw [le_inv_comm₀ one_pos hm0, inv_one]; exact hm
  have h4 : ‖msc z‖⁻¹ ≤ 4 := by rw [inv_le_comm₀ hm0 (by norm_num)]; linarith
  split_ifs
  · refine ⟨?_, ?_⟩
    · have := one_le_pow₀ (n := κ.wDDeg + 2) h1; linarith
    · have := pow_le_pow_left₀ (by positivity) h4 (κ.wDDeg + 2); linarith
  · exact ⟨le_rfl, le_rfl⟩

/-- **A weight `W_d` against its light weight** at a single matrix with `|G_{xx} − m| ≤ 1/8` and
`|m| ≥ 1/4`: `|c| ≤ C_c |c.wDLight|^{d+1}` with `C_c = 2 |m|^{−(d+2)}` for `W_d` (`wDMajorant`),
and `C_c = 1`, `d = 0` otherwise. -/
private lemma LabelRemoval_wd_le (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2)
    (G : Matrix ι ι ℂ) (hm4 : 1 / 4 ≤ ‖msc z‖) (hG8 : ∀ a, ‖G a a - msc z‖ ≤ 1 / 8) {V : Type*}
    (σ : V → ι) (c : Comp V) :
    ‖Comp.val (gData S z Sig G) σ c‖ ≤
      (if c.kind.isWD then 2 * ‖msc z‖⁻¹ ^ (c.kind.wDDeg + 2) else 1) *
        ‖Comp.val (gData S z Sig G) σ c.wDLight‖ ^ (c.kind.wDDeg + 1) := by
  have hm0 : msc z ≠ 0 := fun h => by rw [h, norm_zero] at hm4; norm_num at hm4
  refine G11.wD_val_le (gData S z Sig G) σ c hm0 fun hc => ?_
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> simp [Kind.isWD] at hc
  simp only [Comp.wDLight, Kind.wDL, Comp.val, gData, detData, LabelRemoval_norm_apply]
  linarith [hG8 (σ x)]

/-- **The factor of a random component on all samples**: with `|G_{ab}| ≤ M − 1`,
`|(G_{aa})⁻¹| ≤ M r` (`r ≥ 1`) and `1/4 ≤ |m| ≤ 1`, a random component of the kinds of `Err` has
`|c| ≤ M_b^{d+1} r` if `M ≤ M_b` and, for a weight `W_d`,
`M + 4 (d + 1) (4M)^d ≤ M_b^{d+1}`. -/
private lemma LabelRemoval_val_bad (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2)
    (G : Matrix ι ι ℂ) (M Mb r : ℝ) (hM1 : 1 ≤ M) (hr : 1 ≤ r) (hG : ∀ a b, ‖G a b‖ ≤ M - 1)
    (hinv : ∀ a, ‖(G a a)⁻¹‖ ≤ M * r) (hm : ‖msc z‖ ≤ 1) (hm4 : 1 / 4 ≤ ‖msc z‖) {V : Type*}
    (σ : V → ι) (N : ℕ) (c : Comp V) (hc : c.isTKind N = true ∨ (c.minor = [] ∧ c.kind.isWD = true))
    (hrand : c.kind.isRandom = true) (hMb : M ≤ Mb)
    (hMbw : c.kind.isWD = true →
      M + 4 * ((c.kind.wDDeg : ℝ) + 1) * (4 * M) ^ c.kind.wDDeg ≤ Mb ^ (c.kind.wDDeg + 1)) :
    ‖Comp.val (gData S z Sig G) σ c‖ ≤ Mb ^ (c.kind.wDDeg + 1) * r := by
  have hm0 : 0 < ‖msc z‖ := by linarith
  by_cases hw : c.kind.isWD = true
  · obtain ⟨κ, x, y, mi, l⟩ := c
    cases κ <;> simp [Kind.isWD] at hw
    rename_i ch dd
    have hMbw' := hMbw rfl
    simp only [Kind.wDDeg] at hMbw' ⊢
    simp only [Comp.val, gData, detData, LabelRemoval_norm_apply]
    set g := G (σ x) (σ x)
    set m := msc z
    have hr' : ‖-(g - m) / m‖ ≤ 4 * M := by
      rw [norm_div, norm_neg, div_le_iff₀ hm0]
      have := norm_sub_le g m
      have := hG (σ x) (σ x)
      nlinarith
    have hsum : ‖∑ j ∈ Finset.range (dd + 1), (-(g - m) / m) ^ j‖ ≤
        ((dd : ℝ) + 1) * (4 * M) ^ dd := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ j ∈ Finset.range (dd + 1), ‖(-(g - m) / m) ^ j‖ ≤ (4 * M) ^ dd := by
        intro j hj
        rw [norm_pow]
        calc ‖-(g - m) / m‖ ^ j ≤ (4 * M) ^ j := pow_le_pow_left₀ (norm_nonneg _) hr' j
          _ ≤ (4 * M) ^ dd :=
            pow_le_pow_right₀ (by linarith) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
      simp
    have hmi : ‖m⁻¹‖ ≤ 4 := by rw [norm_inv, inv_le_comm₀ hm0 (by norm_num)]; linarith
    have hP0 : (0 : ℝ) ≤ (4 * M) ^ dd := by positivity
    calc ‖g⁻¹ - m⁻¹ * ∑ j ∈ Finset.range (dd + 1), (-(g - m) / m) ^ j‖
        ≤ ‖g⁻¹‖ + ‖m⁻¹‖ * ‖∑ j ∈ Finset.range (dd + 1), (-(g - m) / m) ^ j‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ M * r + 4 * (((dd : ℝ) + 1) * (4 * M) ^ dd) := by
          gcongr
          · exact hinv (σ x)
      _ ≤ (M + 4 * ((dd : ℝ) + 1) * (4 * M) ^ dd) * r := by
          have : 0 ≤ 4 * ((dd : ℝ) + 1) * (4 * M) ^ dd := by positivity
          nlinarith
      _ ≤ Mb ^ (dd + 1) * r := mul_le_mul_of_nonneg_right hMbw' (by linarith)
  · have hT : c.isTKind N = true := hc.resolve_right fun h => hw h.2
    have hdeg : c.kind.wDDeg = 0 := by
      obtain ⟨κ, x, y, mi, l⟩ := c
      cases κ <;> simp_all [Kind.isWD, Kind.wDDeg]
    rw [hdeg, zero_add, pow_one]
    have := LabelRemoval_val_le_M S z Sig G M hG hm σ N c hT hrand
    nlinarith

end Comp

/-! ## Products over lists -/

section Lists

/-- Monotonicity of a product of nonnegative factors. -/
private lemma LabelRemoval_prod_mono {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ c ∈ l, 0 ≤ f c ∧ f c ≤ g c) : (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.prod_cons]
    have hc := h c List.mem_cons_self
    have ih' := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    have h0 : 0 ≤ (l.map f).prod :=
      List.prod_nonneg fun a ha => by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 ha; exact (h c' (List.mem_cons_of_mem _ hc')).1
    exact mul_le_mul hc.2 ih' h0 (hc.1.trans hc.2)

/-- Removing factors in `[0, 1]` does not decrease a product of nonnegative factors. -/
private lemma LabelRemoval_prod_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → ℝ)
    (h0 : ∀ c ∈ l, 0 ≤ f c) (h1 : ∀ c ∈ l, p c = false → f c ≤ 1) :
    (l.map f).prod ≤ ((l.filter p).map f).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have ih' := ih (fun c' hc' => h0 c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => h1 c' (List.mem_cons_of_mem _ hc'))
    have hpos : 0 ≤ (l.map f).prod :=
      List.prod_nonneg fun a ha => by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 ha; exact h0 c' (List.mem_cons_of_mem _ hc')
    have hc0 := h0 c List.mem_cons_self
    by_cases hp : p c = true
    · simp only [List.filter_cons, hp, if_true, List.map_cons, List.prod_cons]
      exact mul_le_mul_of_nonneg_left ih' hc0
    · simp only [List.filter_cons, hp, List.map_cons, List.prod_cons]
      have hc1 := h1 c List.mem_cons_self (by simpa using hp)
      simp only [Bool.false_eq_true, if_false]
      nlinarith

/-- `Π B_c · q^{Σ e_c} ≤ Π Z_c` if `0 ≤ B_c` and `B_c q^{e_c} ≤ Z_c` for every factor. -/
private lemma LabelRemoval_prod_pow {α : Type*} (l : List α) (B Z : α → ℝ) (e : α → ℕ) (q : ℝ)
    (hq : 0 ≤ q) (h : ∀ c ∈ l, 0 ≤ B c ∧ B c * q ^ e c ≤ Z c) :
    (l.map B).prod * q ^ (l.map e).sum ≤ (l.map Z).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    have hc := h c List.mem_cons_self
    have ih' := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    have h0 : 0 ≤ (l.map B).prod * q ^ (l.map e).sum :=
      mul_nonneg (List.prod_nonneg fun a ha => by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 ha; exact (h c' (List.mem_cons_of_mem _ hc')).1)
        (pow_nonneg hq _)
    calc B c * (l.map B).prod * (q ^ e c * q ^ (l.map e).sum) =
          (B c * q ^ e c) * ((l.map B).prod * q ^ (l.map e).sum) := by
          ring
      _ ≤ Z c * (l.map Z).prod :=
          mul_le_mul hc.2 ih' h0 ((mul_nonneg hc.1 (pow_nonneg hq _)).trans hc.2)

/-- **The factors grouped by labels**: the product of the unlabelled factors times the product
over the distinct labels of the product of the factors with that label is the product of all
factors. -/
private lemma LabelRemoval_prod_groups {α β : Type*} [DecidableEq β] (l : List α)
    (lab : α → Option β) (Dl : List β) (hD : Dl.Nodup)
    (hcov : ∀ c ∈ l, ∀ b, lab c = some b → b ∈ Dl) (f : α → ℝ) :
    ((l.filter fun c => (lab c).isNone).map f).prod *
        (Dl.map fun b => ((l.filter fun c => decide (lab c = some b)).map f).prod).prod =
      (l.map f).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have ih' := ih fun c' hc' b hb => hcov c' (List.mem_cons_of_mem _ hc') b hb
    rcases hc : lab c with _ | b₀
    · have e1 : ∀ b, (decide ((none : Option β) = some b)) = false := fun b => by simp
      simp only [List.filter_cons, hc, Option.isNone_none, if_true, List.map_cons, List.prod_cons,
        e1, Bool.false_eq_true, if_false]
      rw [mul_assoc, ih']
    · have hb₀ : b₀ ∈ Dl := hcov c List.mem_cons_self b₀ hc
      have e1 : ∀ b, (decide (some b₀ = some b)) = decide (b₀ = b) := fun b => by simp
      simp only [List.filter_cons, hc, Option.isNone_some, Bool.false_eq_true, if_false, e1]
      have e2 : (Dl.map fun b => ((if decide (b₀ = b) = true then
            c :: l.filter fun c => decide (lab c = some b)
          else l.filter fun c => decide (lab c = some b)).map f).prod) =
          Dl.map fun b => (if b = b₀ then f c else 1) *
            ((l.filter fun c => decide (lab c = some b)).map f).prod := by
        refine List.map_congr_left fun b _ => ?_
        by_cases hb : b = b₀
        · subst hb; simp
        · simp [Ne.symm hb, hb]
      rw [e2, List.prod_map_mul]
      have e3 : (Dl.map fun b => if b = b₀ then f c else 1).prod = f c := by
        rw [← List.prod_toFinset _ hD, Finset.prod_ite_eq']
        simp [List.mem_toFinset.2 hb₀]
      rw [e3, List.map_cons, List.prod_cons, ← ih']
      ring

end Lists

/-! ## One label group -/

section Group

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bounds of a resampled resolvent `G'` (row `y` resampled) against the single matrix `G̃`
that `LabelRemoval_val_res` uses; the last one is required only under `fix`. -/
private def LabelRemoval_ResDom (G' Gt : Matrix ι ι ℂ) (z : ℂ) (y : ι) (fix : Prop) : Prop :=
  (∀ a, ‖G' a a‖ ≤ ‖Gt a a‖) ∧ (∀ a, ‖G' a a - msc z‖ ≤ ‖Gt a a - msc z‖) ∧
    (∀ b, b ≠ y → ‖G' y b‖ ≤ ‖Gt y b‖) ∧ (∀ a, a ≠ y → ‖G' a y‖ ≤ ‖Gt a y‖) ∧
    (∀ a b, a ≠ b → a ≠ y → b ≠ y → ‖G' a b‖ ≤ ‖Gt a b‖ + ‖Gt a y‖ * ‖Gt y b‖) ∧
    (fix → ∀ a b, a ≠ b → a ≠ y → b ≠ y → ‖G' a b‖ ≤ ‖Gt a b‖)

end Group

/-- The factor of a component at `G̃` in the label removal: for a weight `W_d`,
`2 |m|^{−(d+2)} (X + Y)^{d+1}` with `X` the factor and `Y` the path term of its light weight
at `G̃`; for the other components `X_c + Y_c`. -/
private def LabelRemoval_Z {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (Γ : Graph 3 n)
    (D : Data ι) (σ : Atom 3 n → ι) (c : Comp (Atom 3 n)) : ℝ :=
  (if c.kind.isWD then 2 * ‖D.m‖⁻¹ ^ (c.kind.wDDeg + 2) else 1) *
    (‖Comp.val D σ c.wDLight‖ + LabelRemoval_Y Γ D σ c.wDLight) ^ (c.kind.wDDeg + 1)

private lemma LabelRemoval_Z_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (Γ : Graph 3 n) (D : Data ι) (σ : Atom 3 n → ι) (c : Comp (Atom 3 n)) :
    0 ≤ LabelRemoval_Z Γ D σ c := by
  unfold LabelRemoval_Z
  refine mul_nonneg ?_ (pow_nonneg (add_nonneg (norm_nonneg _) (LabelRemoval_Y_nonneg _ _ _ _)) _)
  split_ifs <;> positivity

/-- **One component at a matrix dominated by `G̃`**: if `|G_{ab}| ≤ |G̃_{ab}|`,
`|G_{aa} − m| ≤ |G̃_{aa} − m|` and `|G_{aa} − m| ≤ 1/8`, a component of the kinds of `Err` has
`|c(G)| ≤ Z_c`. -/
private lemma LabelRemoval_Z_ge_dom {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (Γ : Graph 3 n) (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2) (G Gt : Matrix ι ι ℂ)
    (hm4 : 1 / 4 ≤ ‖msc z‖) (h1 : ∀ a b, ‖G a b‖ ≤ ‖Gt a b‖)
    (h2 : ∀ a, ‖G a a - msc z‖ ≤ ‖Gt a a - msc z‖) (h8 : ∀ a, ‖G a a - msc z‖ ≤ 1 / 8)
    (σ : Atom 3 n → ι) (N : ℕ) (c : Comp (Atom 3 n))
    (hc : c.isTKind N = true ∨ (c.minor = [] ∧ c.kind.isWD = true)) :
    ‖Comp.val (gData S z Sig G) σ c‖ ≤ LabelRemoval_Z Γ (gData S z Sig Gt) σ c := by
  have hC0 : 0 ≤ (if c.kind.isWD then 2 * ‖msc z‖⁻¹ ^ (c.kind.wDDeg + 2) else 1) := by
    split_ifs <;> positivity
  refine (LabelRemoval_wd_le S z Sig G hm4 h8 σ c).trans ?_
  unfold LabelRemoval_Z
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ _) hC0
  exact (LabelRemoval_val_mono S z Sig G Gt h1 h2 σ N _ (LabelRemoval_light_tKind hc)).trans
    (le_add_of_nonneg_right (LabelRemoval_Y_nonneg _ _ _ _))

/-- **One label group** `(pq, v)` at the labelling `σ`, with `y = σ(v)`: if outside a measurable
set `T` of `η` the resolvent with row `y` resampled satisfies `LabelRemoval_ResDom` against `G̃`
and `|G'_{aa} − m| ≤ 1/8`, `G(ω)` is dominated by `G̃` with `|G_{aa}(ω) − m| ≤ 1/8`, every random
factor on every sample is at most `M_b^{d+1} (1 + ‖ω'‖)²`, the random factors of the light weights
at `G̃` are at least `lo`, and `M_{4R'}(ω, y)^{1/2} P(T)^{1/2} ≤ (lo/M_b)^{R'}` with `R'` the number
of components of `Γ.wDLights`, then the modulus of `P_y` or `Q_y` applied to the product of the
factors of the group is at most `3 Π Z_c` (`LabelRemoval_Z`). -/
private lemma LabelRemoval_group {n : ℕ} (Γ : Graph 3 n) {d : ℕ} (P : Profile d)
    (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (z : ℂ) (N : ℕ) (hΓ : Γ.TKindsErr N)
    (Gt : Matrix (Zd d L) (Zd d L) ℂ) (σ : Atom 3 n → Zd d L) (ω : Sample (Zd d L)) (pq : PQ)
    (v : Atom 3 n) (T : Set (Sample (Zd d L))) (hTm : MeasurableSet T) (Mb lo : ℝ) (hlo : 0 ≤ lo)
    (hloM : lo ≤ Mb) (hMb : 0 < Mb)
    (hbad : ∀ (ω' : Sample (Zd d L)) (c : Comp (Atom 3 n)), c ∈ Γ.comps →
      c.kind.isRandom = true →
      ‖Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω') z)) σ c‖ ≤
        Mb ^ (c.kind.wDDeg + 1) * (1 + ‖ω'‖) ^ 2)
    (hm : ‖msc z‖ ≤ 1) (hm4 : 1 / 4 ≤ ‖msc z‖) (hGt1 : ∀ a b, lo ≤ ‖Gt a b‖)
    (hGt2 : ∀ a, lo ≤ ‖Gt a a - msc z‖)
    (hG1 : ∀ a b, ‖green (hmat ω) z a b‖ ≤ ‖Gt a b‖)
    (hG2 : ∀ a, ‖green (hmat ω) z a a - msc z‖ ≤ ‖Gt a a - msc z‖)
    (hG8 : ∀ a, ‖green (hmat ω) z a a - msc z‖ ≤ 1 / 8)
    (hgood : ∀ η, η ∉ T → LabelRemoval_ResDom
      (green (hmat (LabelRemoval_res (σ v) η ω)) z) Gt z (σ v) (Γ.labelFixedB v = true) ∧
      ∀ a, ‖green (hmat (LabelRemoval_res (σ v) η ω)) z a a - msc z‖ ≤ 1 / 8)
    (hS1 : ∀ c, coordVar (Smat P.ψ W L) c ≤ 1)
    (hP : Real.sqrt (LabelRemoval.momBound (2 * (2 * Γ.wDLights.comps.length)) ω (σ v)) *
      Real.sqrt (gaussLaw (Smat P.ψ W L) T).toReal ≤ (lo / Mb) ^ Γ.wDLights.comps.length) :
    ‖PFamily.op ⟨Pexp (Smat P.ψ W L)⟩ pq (σ v) (fun ω' =>
        ((Γ.comps.filter fun c => decide (c.label = some (pq, v))).map
          (Comp.val (rbmData d P Sig W L z ω') σ)).prod) ω‖ ≤
      3 * ((Γ.comps.filter fun c => decide (c.label = some (pq, v))).map
        (LabelRemoval_Z Γ (gData (Smat P.ψ W L) z Sig Gt) σ)).prod := by
  set S := Smat P.ψ W L with hS
  set lst := Γ.comps.filter fun c => decide (c.label = some (pq, v)) with hlst
  set Dt := gData S z Sig Gt with hDt
  set Z : Comp (Atom 3 n) → ℝ := LabelRemoval_Z Γ Dt σ with hZ
  set R' := Γ.wDLights.comps.length with hR'
  set F : Sample (Zd d L) → ℂ := fun ω' => (lst.map (Comp.val (rbmData d P Sig W L z ω') σ)).prod
  have hmem : ∀ c ∈ lst, c ∈ Γ.comps := fun c hc => List.mem_of_mem_filter hc
  have hEK : ∀ c ∈ lst, c.isTKind N = true ∨ (c.minor = [] ∧ c.kind.isWD = true) :=
    fun c hc => LabelRemoval_errKind hΓ (hmem c hc)
  have hlab : ∀ c ∈ lst, c.label = some (pq, v) := fun c hc => by
    simpa using (List.mem_filter.1 hc).2
  have hZ0 : ∀ c, 0 ≤ Z c := fun c => LabelRemoval_Z_nonneg Γ Dt σ c
  have hZp : 0 ≤ (lst.map Z).prod := List.prod_nonneg fun a ha => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha; exact hZ0 c
  have hnormF : ∀ ω', ‖F ω'‖ ≤
      (lst.map fun c => ‖Comp.val (gData S z Sig (green (hmat ω') z)) σ c‖).prod := by
    intro ω'
    refine (List.norm_prod_le _).trans (le_of_eq ?_)
    rw [List.map_map]
    refine congrArg List.prod (List.map_congr_left fun c hc => ?_)
    simp only [Function.comp, LabelRemoval_val_rbm P Sig W L z ω' σ N c (hEK c hc)]
    rfl
  -- the good samples
  have hgoodF : ∀ η, η ∉ T → ‖F (LabelRemoval_res (σ v) η ω)‖ ≤ (lst.map Z).prod := by
    intro η hη
    refine (hnormF _).trans (LabelRemoval_prod_mono _ _ _ fun c hc => ⟨norm_nonneg _, ?_⟩)
    obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, g8⟩ := hgood η hη
    have hC0 : 0 ≤ (if c.kind.isWD then 2 * ‖msc z‖⁻¹ ^ (c.kind.wDDeg + 2) else 1) := by
      split_ifs <;> positivity
    refine (LabelRemoval_wd_le S z Sig _ hm4 g8 σ c).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ _) hC0
    exact LabelRemoval_val_res Γ S z Sig _ Gt σ N c.wDLight (LabelRemoval_light_tKind (hEK c hc))
      pq v (hlab c hc) g1 g2 g3 g4 g5 g6
  -- all samples
  set Bh : Comp (Atom 3 n) → ℝ := fun c =>
    if c.kind.isRandom = true then Mb ^ (c.kind.wDDeg + 1) else ‖Comp.val Dt σ c‖ with hBh
  have hBh0 : ∀ c, 0 ≤ Bh c := fun c => by
    simp only [hBh]; split_ifs
    · positivity
    · exact norm_nonneg _
  have hB0 : 0 ≤ (lst.map Bh).prod := List.prod_nonneg fun a ha => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha; exact hBh0 c
  have hallF : ∀ ω', ‖F ω'‖ ≤ (lst.map Bh).prod * (1 + ‖ω'‖) ^ (2 * R') := by
    intro ω'
    have hr1 : (1 : ℝ) ≤ (1 + ‖ω'‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg ω'])
    refine (hnormF _).trans ?_
    refine (LabelRemoval_prod_mono _ _ (fun c => Bh c * (1 + ‖ω'‖) ^ 2)
      fun c hc => ⟨norm_nonneg _, ?_⟩).trans ?_
    · simp only [hBh]
      split_ifs with hr
      · exact hbad ω' c (hmem c hc) hr
      · rw [LabelRemoval_val_det S z Sig _ Gt σ c (by simpa using hr)]
        exact le_mul_of_one_le_right (norm_nonneg _) hr1
    · rw [List.prod_map_mul, List.map_const', List.prod_replicate, ← pow_mul]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg ω']) ?_) hB0
      have h1 : lst.length ≤ Γ.comps.length := List.length_filter_le _ _
      have h2 : Γ.comps.length ≤ R' := by rw [hR', G11.wDLights_length]; omega
      omega
  -- the bad part
  have hq0 : 0 ≤ lo / Mb := div_nonneg hlo hMb.le
  have hq1 : lo / Mb ≤ 1 := (div_le_one hMb).2 hloM
  have hBZ : (lst.map Bh).prod * (lo / Mb) ^ (lst.map fun c => c.kind.wDDeg + 1).sum ≤
      (lst.map Z).prod := by
    refine LabelRemoval_prod_pow lst Bh Z (fun c => c.kind.wDDeg + 1) (lo / Mb) hq0
      fun c hc => ⟨hBh0 c, ?_⟩
    simp only [hBh]
    split_ifs with hr
    · rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hMb.ne')]
      have hlight : lo ≤ ‖Comp.val Dt σ c.wDLight‖ := by
        exact LabelRemoval_val_ge S z Sig Gt lo hGt1 hGt2 σ N _
          (LabelRemoval_light_tKind (hEK c hc)) (LabelRemoval_light_random c hr)
      have hC1 := (LabelRemoval_Cc z hm hm4 c.kind).1
      simp only [hZ, LabelRemoval_Z]
      calc lo ^ (c.kind.wDDeg + 1)
          ≤ (‖Comp.val Dt σ c.wDLight‖ + LabelRemoval_Y Γ Dt σ c.wDLight) ^ (c.kind.wDDeg + 1) :=
            pow_le_pow_left₀ hlo (hlight.trans (le_add_of_nonneg_right
              (LabelRemoval_Y_nonneg _ _ _ _))) _
        _ ≤ _ := le_mul_of_one_le_left (pow_nonneg (add_nonneg (norm_nonneg _)
            (LabelRemoval_Y_nonneg _ _ _ _)) _) hC1
    · obtain ⟨hw, hdeg, hl⟩ := LabelRemoval_det_wD c (by simpa using hr)
      simp only [hZ, LabelRemoval_Z, hw, hdeg, hl, zero_add, pow_one, Bool.false_eq_true,
        if_false, one_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hq1).trans
        (le_add_of_nonneg_right (LabelRemoval_Y_nonneg _ _ _ _))
  have hsum : (lst.map fun c => c.kind.wDDeg + 1).sum ≤ R' := by
    have h1 : (lst.map fun c => c.kind.wDDeg + 1).sum ≤
        (Γ.comps.map fun c => c.kind.wDDeg + 1).sum :=
      ((List.filter_sublist).map _).sum_le_sum fun _ _ => Nat.zero_le _
    have h2 : (Γ.comps.map fun c => c.kind.wDDeg + 1).sum = R' := by
      rw [hR', G11.wDLights_length, List.sum_map_add]
      simp [add_comm]
    omega
  have hbadP : (lst.map Bh).prod *
      Real.sqrt (LabelRemoval.momBound (2 * (2 * R')) ω (σ v)) *
        Real.sqrt (gaussLaw S T).toReal ≤ (lst.map Z).prod := by
    calc (lst.map Bh).prod * Real.sqrt (LabelRemoval.momBound (2 * (2 * R')) ω (σ v)) *
          Real.sqrt (gaussLaw S T).toReal
        = (lst.map Bh).prod * (Real.sqrt (LabelRemoval.momBound (2 * (2 * R')) ω (σ v)) *
          Real.sqrt (gaussLaw S T).toReal) := by ring
      _ ≤ (lst.map Bh).prod * (lo / Mb) ^ R' := mul_le_mul_of_nonneg_left hP hB0
      _ ≤ (lst.map Bh).prod * (lo / Mb) ^ (lst.map fun c => c.kind.wDDeg + 1).sum :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 hsum) hB0
      _ ≤ (lst.map Z).prod := hBZ
  have hPexp : ‖Pexp S (σ v) F ω‖ ≤ 2 * (lst.map Z).prod := by
    have := LabelRemoval.pexp_norm_le_of_good S hS1 (σ v) F ω T hTm (lst.map Z).prod
      (lst.map Bh).prod (2 * R') hZp hB0 hgoodF hallF
    linarith
  have hFω : ‖F ω‖ ≤ (lst.map Z).prod := by
    refine (hnormF ω).trans (LabelRemoval_prod_mono _ _ _ fun c hc => ⟨norm_nonneg _, ?_⟩)
    exact LabelRemoval_Z_ge_dom Γ S z Sig _ Gt hm4 hG1 hG2 hG8 σ N c (hEK c hc)
  cases pq with
  | P =>
    change ‖Pexp S (σ v) F ω‖ ≤ _
    linarith
  | Q =>
    change ‖F ω - Pexp S (σ v) F ω‖ ≤ _
    linarith [norm_sub_le (F ω) (Pexp S (σ v) F ω)]

/-! ## Dotted blocks and the labelled value of a graph at one labelling -/

section Blocks

variable {V : Type*} [DecidableEq V]

/-- The relation "joined by a dotted component". -/
private def LabelRemoval_dotRel (cs : List (Comp V)) : V → V → Prop :=
  fun u v => ∃ c ∈ cs, c.kind = .dot ∧ c.x = u ∧ c.y = v

omit [DecidableEq V] in
private lemma LabelRemoval_dotRel_mono {cs cs' : List (Comp V)} (h : ∀ c ∈ cs, c ∈ cs') :
    LabelRemoval_dotRel cs ≤ LabelRemoval_dotRel cs' := by
  rintro u v ⟨c, hc, hk, hx, hy⟩
  exact ⟨c, h c hc, hk, hx, hy⟩

private lemma LabelRemoval_dotBlocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) =
      if c.kind = .dot then joinBlocks (dotBlocks as cs) c.x c.y else dotBlocks as cs := by
  simp [dotBlocks, List.foldl_append]

/-- Two atoms of one dotted block are joined by a path of dotted components. -/
private lemma LabelRemoval_dotBlocks_conn (as : List V) (cs : List (Comp V)) :
    ∀ B ∈ dotBlocks as cs, ∀ u ∈ B, ∀ v ∈ B, Relation.EqvGen (LabelRemoval_dotRel cs) u v := by
  induction cs using List.reverseRecOn with
  | nil =>
    intro B hB u hu v hv
    simp only [dotBlocks, List.foldl_nil, List.mem_map] at hB
    obtain ⟨a, -, rfl⟩ := hB
    simp only [List.mem_singleton] at hu hv
    subst hu; subst hv
    exact Relation.EqvGen.refl _
  | append_singleton cs c ih =>
    have hmono : ∀ u v, Relation.EqvGen (LabelRemoval_dotRel cs) u v →
        Relation.EqvGen (LabelRemoval_dotRel (cs ++ [c])) u v := fun u v h =>
      Relation.EqvGen.mono (LabelRemoval_dotRel_mono fun c' hc' => List.mem_append_left _ hc')
        u v h
    intro B hB u hu v hv
    rw [LabelRemoval_dotBlocks_snoc] at hB
    split_ifs at hB with hk
    · unfold joinBlocks at hB
      rw [List.mem_append] at hB
      rcases hB with hB | hB
      · exact hmono _ _ (ih B (List.mem_of_mem_filter hB) u hu v hv)
      · rw [List.mem_singleton] at hB
        subst hB
        have hxy : Relation.EqvGen (LabelRemoval_dotRel (cs ++ [c])) c.x c.y :=
          Relation.EqvGen.rel _ _ ⟨c, List.mem_append_right _ (List.mem_singleton_self _), hk,
            rfl, rfl⟩
        have key : ∀ w ∈ (dotBlocks as cs).filter (fun B => B.contains c.x || B.contains c.y),
            ∀ z ∈ w, Relation.EqvGen (LabelRemoval_dotRel (cs ++ [c])) z c.x := by
          intro w hw z hz
          have hw' := List.mem_filter.1 hw
          have hcont := hw'.2
          simp only [Bool.or_eq_true, List.contains_iff_mem] at hcont
          rcases hcont with hx | hy
          · exact hmono _ _ (ih w hw'.1 z hz _ hx)
          · exact (hmono _ _ (ih w hw'.1 z hz _ hy)).trans _ _ _ hxy.symm
        rw [List.mem_flatten] at hu hv
        obtain ⟨w₁, hw₁, hu⟩ := hu
        obtain ⟨w₂, hw₂, hv⟩ := hv
        exact (key w₁ hw₁ u hu).trans _ _ _ (key w₂ hw₂ v hv).symm
    · exact hmono _ _ (ih B hB u hu v hv)

omit [DecidableEq V] in
private lemma LabelRemoval_eqvGen_eq {ι : Type*} {cs : List (Comp V)} (σ : V → ι)
    (hz : ∀ c ∈ cs, c.kind = .dot → σ c.x = σ c.y) {u v : V}
    (h : Relation.EqvGen (LabelRemoval_dotRel cs) u v) : σ u = σ v := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact hz c hc hk
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

end Blocks

/-- A label atom whose dotted block contains an external atom takes the value of an external atom
at every labelling that agrees on the ends of the dotted components. -/
private lemma LabelRemoval_labelFixed {n : ℕ} (Γ : Graph 3 n) {ι : Type*} (σ : Atom 3 n → ι)
    (hz : ∀ c ∈ Γ.comps, c.kind = .dot → σ c.x = σ c.y) (v : Atom 3 n)
    (hv : Γ.labelFixedB v = true) : ∃ j, σ v = σ (Sum.inl j) := by
  unfold Graph.labelFixedB at hv
  obtain ⟨B, hB, hBv⟩ := List.any_eq_true.1 hv
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.any_eq_true] at hBv
  obtain ⟨hvB, w, hwB, hw⟩ := hBv
  obtain ⟨j, rfl⟩ : ∃ j, w = Sum.inl j := by
    rcases w with j | j
    · exact ⟨j, rfl⟩
    · simp at hw
  exact ⟨j, LabelRemoval_eqvGen_eq σ hz (LabelRemoval_dotBlocks_conn _ _ B hB v hvB _ hwB)⟩

/-- The value of a labelled graph at a labelling that does not agree on the ends of a dotted
component is `0`. -/
private lemma LabelRemoval_termR_zero {n : ℕ} (Γ : Graph 3 n) {ι : Type} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) (D : Sample ι → Data ι) (σ : Atom 3 n → ι)
    (ω : Sample ι) (c : Comp (Atom 3 n)) (hc : c ∈ Γ.comps) (hk : c.kind = .dot)
    (hne : σ c.x ≠ σ c.y) : Γ.termR ⟨Pexp S⟩ D σ ω = 0 := by
  have hval : ∀ ω', Comp.val (D ω') σ c = 0 := by
    intro ω'
    obtain ⟨κ, x, y, mi, l⟩ := c
    simp only at hk; subst hk
    simp only [Comp.val]
    exact if_neg hne
  unfold Graph.termR
  rcases hl : c.label with _ | ℓ
  · have : ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl]⟩, hval ω⟩)
    rw [this, mul_zero, zero_mul]
  · have hzero : (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) = fun _ => 0 := by
      funext ω'
      exact List.prod_eq_zero (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl]⟩, hval ω'⟩)
    have hℓ : ℓ ∈ Γ.labels := by
      unfold Graph.labels
      rw [List.mem_dedup, List.mem_filterMap]
      exact ⟨c, hc, hl⟩
    have hP0 : ∀ x : ι, Pexp S x (fun _ => 0) ω = 0 := fun x => by
      simp [Pexp, partialExp]
    have : (Γ.labels.map fun ℓ => PFamily.op ⟨Pexp S⟩ ℓ.1 (σ ℓ.2)
        (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (D ω') σ)).prod) ω).prod = 0 := by
      refine List.prod_eq_zero (List.mem_map.2 ⟨ℓ, hℓ, ?_⟩)
      rw [hzero]
      rcases ℓ with ⟨pq, v⟩
      cases pq
      · exact hP0 (σ v)
      · change (fun _ => (0 : ℂ)) ω - Pexp S (σ v) (fun _ => 0) ω = 0
        rw [hP0]; simp
    rw [this, mul_zero]

/-- **The labelled value at one labelling**: under the hypotheses of `LabelRemoval_group` for every
row `y` (with the bound without path term when `y` is the value of an external atom),
`|termR| ≤ 3^{#labels} |coeff| Π_c Z_c`. -/
private lemma LabelRemoval_termR_le {n : ℕ} (Γ : Graph 3 n) {d : ℕ} (P : Profile d)
    (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (z : ℂ) (N : ℕ) (hΓ : Γ.TKindsErr N)
    (Gt : Matrix (Zd d L) (Zd d L) ℂ) (σ : Atom 3 n → Zd d L) (ω : Sample (Zd d L))
    (T : Set (Sample (Zd d L))) (hTm : MeasurableSet T) (Mb lo : ℝ) (hlo : 0 ≤ lo)
    (hloM : lo ≤ Mb) (hMb : 0 < Mb)
    (hbad : ∀ (ω' : Sample (Zd d L)) (c : Comp (Atom 3 n)), c ∈ Γ.comps →
      c.kind.isRandom = true →
      ‖Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω') z)) σ c‖ ≤
        Mb ^ (c.kind.wDDeg + 1) * (1 + ‖ω'‖) ^ 2)
    (hm : ‖msc z‖ ≤ 1) (hm4 : 1 / 4 ≤ ‖msc z‖) (hGt1 : ∀ a b, lo ≤ ‖Gt a b‖)
    (hGt2 : ∀ a, lo ≤ ‖Gt a a - msc z‖)
    (hG1 : ∀ a b, ‖green (hmat ω) z a b‖ ≤ ‖Gt a b‖)
    (hG2 : ∀ a, ‖green (hmat ω) z a a - msc z‖ ≤ ‖Gt a a - msc z‖)
    (hG8 : ∀ a, ‖green (hmat ω) z a a - msc z‖ ≤ 1 / 8)
    (hgood : ∀ y η, η ∉ T → LabelRemoval_ResDom
      (green (hmat (LabelRemoval_res y η ω)) z) Gt z y (∃ j, y = σ (Sum.inl j)) ∧
      ∀ a, ‖green (hmat (LabelRemoval_res y η ω)) z a a - msc z‖ ≤ 1 / 8)
    (hS1 : ∀ c, coordVar (Smat P.ψ W L) c ≤ 1)
    (hP : ∀ y, Real.sqrt (LabelRemoval.momBound (2 * (2 * Γ.wDLights.comps.length)) ω y) *
      Real.sqrt (gaussLaw (Smat P.ψ W L) T).toReal ≤ (lo / Mb) ^ Γ.wDLights.comps.length) :
    ‖Γ.termR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) σ ω‖ ≤
      3 ^ Γ.labels.length * (‖Γ.coeff.eval (msc z)‖ *
        (Γ.comps.map (LabelRemoval_Z Γ (gData (Smat P.ψ W L) z Sig Gt) σ)).prod) := by
  set S := Smat P.ψ W L with hS
  set Dt := gData S z Sig Gt with hDt
  set Z : Comp (Atom 3 n) → ℝ := LabelRemoval_Z Γ Dt σ with hZ
  have hZ0 : ∀ c, 0 ≤ Z c := fun c => LabelRemoval_Z_nonneg Γ Dt σ c
  have hRHS : 0 ≤ 3 ^ Γ.labels.length * (‖Γ.coeff.eval (msc z)‖ * (Γ.comps.map Z).prod) :=
    mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (List.prod_nonneg fun a ha => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha; exact hZ0 c))
  by_cases hz : ∀ c ∈ Γ.comps, c.kind = .dot → σ c.x = σ c.y
  swap
  · push_neg at hz
    obtain ⟨c, hc, hk, hne⟩ := hz
    rw [LabelRemoval_termR_zero Γ S _ σ ω c hc hk hne, norm_zero]
    exact hRHS
  have hEK : ∀ c ∈ Γ.comps, c.isTKind N = true ∨ (c.minor = [] ∧ c.kind.isWD = true) :=
    fun c hc => LabelRemoval_errKind hΓ hc
  unfold Graph.termR
  rw [norm_mul, norm_mul]
  have hm' : (rbmData d P Sig W L z ω).m = msc z := rfl
  rw [hm']
  -- the unlabelled factors
  have hA : ‖((Γ.comps.filter fun c => c.label.isNone).map
      (Comp.val (rbmData d P Sig W L z ω) σ)).prod‖ ≤
      ((Γ.comps.filter fun c => c.label.isNone).map Z).prod := by
    refine (List.norm_prod_le _).trans ?_
    rw [List.map_map]
    refine LabelRemoval_prod_mono _ _ _ fun c hc => ⟨norm_nonneg _, ?_⟩
    have hcT := hEK c (List.mem_of_mem_filter hc)
    simp only [Function.comp, LabelRemoval_val_rbm P Sig W L z ω σ N c hcT]
    exact LabelRemoval_Z_ge_dom Γ S z Sig _ Gt hm4 hG1 hG2 hG8 σ N c hcT
  -- the label groups
  have hB : ‖(Γ.labels.map fun ℓ => PFamily.op ⟨Pexp S⟩ ℓ.1 (σ ℓ.2)
      (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (rbmData d P Sig W L z ω') σ)).prod) ω).prod‖ ≤
      (Γ.labels.map fun ℓ => 3 * ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
        Z).prod).prod := by
    refine (List.norm_prod_le _).trans ?_
    rw [List.map_map]
    refine LabelRemoval_prod_mono _ _ _ fun ℓ _ => ⟨norm_nonneg _, ?_⟩
    obtain ⟨pq, v⟩ := ℓ
    refine LabelRemoval_group Γ P Sig W L z N hΓ Gt σ ω pq v T hTm Mb lo hlo hloM hMb hbad hm hm4
      hGt1 hGt2 hG1 hG2 hG8 (fun η hη => ?_) hS1 (hP (σ v))
    obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, g8⟩ := hgood (σ v) η hη
    exact ⟨⟨g1, g2, g3, g4, g5, fun hf => g6 (LabelRemoval_labelFixed Γ σ hz v hf)⟩, g8⟩
  have hgrp := LabelRemoval_prod_groups Γ.comps Comp.label Γ.labels (List.nodup_dedup _)
    (fun c hc b hb => by
      unfold Graph.labels; rw [List.mem_dedup, List.mem_filterMap]; exact ⟨c, hc, hb⟩) Z
  have h3 : (Γ.labels.map fun ℓ => 3 * ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
      Z).prod).prod = 3 ^ Γ.labels.length * (Γ.labels.map fun ℓ =>
        ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map Z).prod).prod := by
    rw [List.prod_map_mul, List.map_const', List.prod_replicate]
  have hA0 : 0 ≤ ((Γ.comps.filter fun c => c.label.isNone).map Z).prod :=
    List.prod_nonneg fun a ha => by obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha; exact hZ0 c
  calc ‖Γ.coeff.eval (msc z)‖ * ‖((Γ.comps.filter fun c => c.label.isNone).map
        (Comp.val (rbmData d P Sig W L z ω) σ)).prod‖ * ‖(Γ.labels.map fun ℓ =>
          PFamily.op ⟨Pexp S⟩ ℓ.1 (σ ℓ.2)
          (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
            (Comp.val (rbmData d P Sig W L z ω') σ)).prod) ω).prod‖
      ≤ ‖Γ.coeff.eval (msc z)‖ * ((Γ.comps.filter fun c => c.label.isNone).map Z).prod *
          (Γ.labels.map fun ℓ => 3 * ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
            Z).prod).prod := by
        gcongr
    _ = 3 ^ Γ.labels.length * (‖Γ.coeff.eval (msc z)‖ * (Γ.comps.map Z).prod) := by
        rw [h3, ← hgrp]; ring

/-! ## The expansion into the label-free graphs `Γ_S` -/

section Expand

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A component has the same value without its label. -/
private lemma LabelRemoval_val_unlabel {V : Type*} (D : Data ι) (σ : V → ι) (c : Comp V) :
    Comp.val D σ { c with label := none } = Comp.val D σ c := rfl

/-- **The expansion of the product of `X_c + Y_c`** over the components of `Γ` into the products
over the components of the label-free graphs `Γ_S`, `S ⊆` the replaceable components. -/
private lemma LabelRemoval_expand {n : ℕ} (Γ : Graph 3 n) (D : Data ι) (σ : Atom 3 n → ι) :
    (Γ.comps.map fun c => ‖Comp.val D σ c‖ + LabelRemoval_Y Γ D σ c).prod ≤
      ∑ t ∈ Γ.pathElig.powerset, ((Γ.pathRepl t).comps.map fun c => ‖Comp.val D σ c‖).prod := by
  set len := Γ.comps.length
  set X : Fin len → ℝ := fun i => ‖Comp.val D σ Γ.comps[i]‖ with hX
  set Y : Fin len → ℝ := fun i => LabelRemoval_Y Γ D σ Γ.comps[i] with hY
  have hlist : (Γ.comps.map fun c => ‖Comp.val D σ c‖ + LabelRemoval_Y Γ D σ c).prod =
      ∏ i, (Y i + X i) := by
    conv_lhs => rw [← List.ofFn_getElem (xs := Γ.comps)]
    rw [List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => by
      simp only [Function.comp, hX, hY, Fin.getElem_fin]; ring
  rw [hlist, Finset.prod_add]
  -- only the sets of replaceable components contribute
  have hY0 : ∀ i, i ∉ Γ.pathElig → Y i = 0 := by
    intro i hi
    simp only [Graph.pathElig, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hY, LabelRemoval_Y]
    rcases hl : Γ.comps[i].label with _ | ⟨_, v⟩
    · rfl
    · simp only; rw [if_neg hi]
  rw [← Finset.sum_subset (Finset.powerset_mono.2 (Finset.subset_univ Γ.pathElig))]
  swap
  · intro t _ ht
    rw [Finset.mem_powerset, Finset.not_subset] at ht
    obtain ⟨i, hit, hi⟩ := ht
    rw [Finset.prod_eq_zero hit (hY0 i hi), zero_mul]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  -- the product over the unfiltered list of `Γ_t`
  set cs : List (Comp (Atom 3 n)) := (List.finRange len).flatMap fun i =>
    match Γ.comps[i].label with
    | some (_, v) => if i ∈ t then Γ.comps[i].pathVia v else [{ Γ.comps[i] with label := none }]
    | none => [Γ.comps[i]] with hcs
  have hcsprod : (cs.map fun c => ‖Comp.val D σ c‖).prod =
      (∏ i ∈ t, Y i) * ∏ i ∈ Finset.univ \ t, X i := by
    rw [hcs, List.flatMap_def, List.map_flatten, List.prod_flatten, List.map_map, List.map_map,
      ← List.ofFn_eq_map, List.prod_ofFn]
    rw [← Finset.prod_mul_prod_compl t]
    rw [Finset.compl_eq_univ_sdiff]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hpe : Γ.pathEligB Γ.comps[i.1] = true := by
        have := ht hi
        simpa [Graph.pathElig] using this
      simp only [Function.comp, hY, LabelRemoval_Y, Fin.getElem_fin] at hpe ⊢
      rcases hl : Γ.comps[i.1].label with _ | ⟨_, v⟩
      · simp [Graph.pathEligB, hl] at hpe
      · simp only [hl, if_pos hi, if_pos hpe]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hi' : i ∉ t := (Finset.mem_sdiff.1 hi).2
      simp only [Function.comp, hX, Fin.getElem_fin]
      rcases hl : Γ.comps[i.1].label with _ | ⟨_, v⟩
      · simp [hl]
      · simp only [hl, if_neg hi', List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, LabelRemoval_val_unlabel]
  rw [← hcsprod]
  unfold Graph.pathRepl
  simp only
  refine LabelRemoval_prod_filter cs _ _ (fun c _ => norm_nonneg _) fun c _ hp => ?_
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hk, -⟩, -⟩ := hp
  obtain ⟨κ, x, y, mi, l⟩ := c
  simp only at hk; subst hk
  simp only [Comp.val]
  split_ifs <;> simp

end Expand

/-- **The labelled value of `Γ` at `(𝔞, 𝔟, 𝔟)`** against the label-free graphs `Γ'_S` of the graph
`Γ' = Γ.wDLights` (every weight `W_d` replaced by `d + 1` light weights) at the single matrix `G̃`:
under the hypotheses of `LabelRemoval_termR_le` (with the bound without path term when the
resampled row is `𝔞` or `𝔟`),
`|Γ_{𝔞,𝔟𝔟}| ≤ 3^{#labels} C_Γ Σ_{S ⊆ pathElig(Γ')} |(Γ'_S)^{abs}_{𝔞,𝔟𝔟}(G̃)|` with
`C_Γ = Π_{W_d} 2 · 4^{d+2}` (`G11.wDConst`). -/
private lemma LabelRemoval_valR_le {n : ℕ} (Γ : Graph 3 n) {d : ℕ} (P : Profile d)
    (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (z : ℂ) (N : ℕ) (hΓ : Γ.TKindsErr N)
    (Gt : Matrix (Zd d L) (Zd d L) ℂ) (ω : Sample (Zd d L))
    (T : Set (Sample (Zd d L))) (hTm : MeasurableSet T) (Mb lo : ℝ) (hlo : 0 ≤ lo)
    (hloM : lo ≤ Mb) (hMb : 0 < Mb)
    (hbad : ∀ (σ : Atom 3 n → Zd d L) (ω' : Sample (Zd d L)) (c : Comp (Atom 3 n)),
      c ∈ Γ.comps → c.kind.isRandom = true →
      ‖Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω') z)) σ c‖ ≤
        Mb ^ (c.kind.wDDeg + 1) * (1 + ‖ω'‖) ^ 2)
    (hm : ‖msc z‖ ≤ 1) (hm4 : 1 / 4 ≤ ‖msc z‖) (hGt1 : ∀ a b, lo ≤ ‖Gt a b‖)
    (hGt2 : ∀ a, lo ≤ ‖Gt a a - msc z‖)
    (hG1 : ∀ a b, ‖green (hmat ω) z a b‖ ≤ ‖Gt a b‖)
    (hG2 : ∀ a, ‖green (hmat ω) z a a - msc z‖ ≤ ‖Gt a a - msc z‖)
    (hG8 : ∀ a, ‖green (hmat ω) z a a - msc z‖ ≤ 1 / 8) (a b : Zd d L)
    (hgood : ∀ y η, η ∉ T → LabelRemoval_ResDom
      (green (hmat (LabelRemoval_res y η ω)) z) Gt z y (y = a ∨ y = b) ∧
      ∀ a, ‖green (hmat (LabelRemoval_res y η ω)) z a a - msc z‖ ≤ 1 / 8)
    (hS1 : ∀ c, coordVar (Smat P.ψ W L) c ≤ 1)
    (hP : ∀ y, Real.sqrt (LabelRemoval.momBound (2 * (2 * Γ.wDLights.comps.length)) ω y) *
      Real.sqrt (gaussLaw (Smat P.ψ W L) T).toReal ≤ (lo / Mb) ^ Γ.wDLights.comps.length) :
    ‖Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω‖ ≤
      3 ^ Γ.labels.length * (G11.wDConst Γ * ∑ t ∈ Γ.wDLights.pathElig.powerset,
        (Γ.wDLights.pathRepl t).absVal (gData (Smat P.ψ W L) z Sig Gt) ![a, b, b]) := by
  set Dt := gData (Smat P.ψ W L) z Sig Gt with hDt
  set Γ' := Γ.wDLights with hΓ'
  have hY : ∀ (σ : Atom 3 n → Zd d L) (c : Comp (Atom 3 n)),
      LabelRemoval_Y Γ' Dt σ c = LabelRemoval_Y Γ Dt σ c := by
    intro σ c
    unfold LabelRemoval_Y
    rw [hΓ', G11.wDLights_pathEligB]
  have hDm : Dt.m = msc z := rfl
  -- `Π_Γ Z_c ≤ C_Γ Π_{Γ'} (X + Y)`
  have hZprod : ∀ s : Fin n → Zd d L,
      (Γ.comps.map (LabelRemoval_Z Γ Dt (Sum.elim ![a, b, b] s))).prod ≤
        G11.wDConst Γ * (Γ'.comps.map fun c => ‖Comp.val Dt (Sum.elim ![a, b, b] s) c‖ +
          LabelRemoval_Y Γ' Dt (Sum.elim ![a, b, b] s) c).prod := by
    intro s
    set σ := Sum.elim ![a, b, b] s
    rw [hΓ', G11.wDLights_prod]
    simp only [← hΓ', hY]
    unfold LabelRemoval_Z G11.wDConst
    rw [← List.prod_map_mul]
    refine LabelRemoval_prod_mono _ _ _ fun c _ => ⟨?_, ?_⟩
    · refine mul_nonneg ?_ (pow_nonneg (add_nonneg (norm_nonneg _)
        (LabelRemoval_Y_nonneg _ _ _ _)) _)
      split_ifs <;> positivity
    · rw [hDm]
      exact mul_le_mul_of_nonneg_right (LabelRemoval_Cc z hm hm4 c.kind).2
        (pow_nonneg (add_nonneg (norm_nonneg _) (LabelRemoval_Y_nonneg _ _ _ _)) _)
  have hC0 : 0 ≤ G11.wDConst Γ := zero_le_one.trans (G11.one_le_wDConst Γ)
  unfold Graph.valR
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ s : Fin n → Zd d L,
      ‖Γ.termR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) (Sum.elim ![a, b, b] s) ω‖ ≤
        3 ^ Γ.labels.length * (G11.wDConst Γ * ∑ t ∈ Γ'.pathElig.powerset,
          ‖Γ'.coeff.eval (msc z)‖ *
            ((Γ'.pathRepl t).comps.map fun c => ‖Comp.val Dt (Sum.elim ![a, b, b] s) c‖).prod) := by
    intro s
    refine (LabelRemoval_termR_le Γ P Sig W L z N hΓ Gt _ ω T hTm Mb lo hlo hloM hMb (hbad _) hm
      hm4 hGt1 hGt2 hG1 hG2 hG8 (fun y η hη => ?_) hS1 hP).trans ?_
    · obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, g8⟩ := hgood y η hη
      refine ⟨⟨g1, g2, g3, g4, g5, fun ⟨j, hj⟩ => g6 ?_⟩, g8⟩
      fin_cases j
      · left; simpa using hj
      · right; simpa using hj
      · right; simpa using hj
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← Finset.mul_sum, show Γ'.coeff = Γ.coeff from rfl, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (hZprod s).trans (mul_le_mul_of_nonneg_left (LabelRemoval_expand Γ' Dt _) hC0)
  refine (Finset.sum_le_sum fun s _ => hterm s).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  rfl

/-! ## The single matrix `G̃` dominates `G` and the resampled resolvents -/

section Dom

variable {d L : ℕ} [NeZero L] {W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ}
  {G : Matrix (Zd d L) (Zd d L) ℂ} {q : LabelRemoval_Par}

/-- The entries of `G̃`: `|G̃_{xy} − δ_{xy} m| = 3 (Ω_{xy} + ε)`, `|G̃_{xx}| = |m| + 3(Ω_{xx} + ε)`,
`|G̃_{xy}| = 3 (Ω_{xy} + ε)` for `x ≠ y`, and all these are at least `3ε`. -/
private lemma LabelRemoval_Gt_facts {m : ℂ} (hm : m ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    {Om : Matrix (Zd d L) (Zd d L) ℝ} (hOm : ∀ x y, 0 ≤ Om x y) :
    (∀ x, ‖LabelRemoval_Gt m ε Om x x - m‖ = 3 * (Om x x + ε)) ∧
    (∀ x, ‖LabelRemoval_Gt m ε Om x x‖ = ‖m‖ + 3 * (Om x x + ε)) ∧
    (∀ x y, x ≠ y → ‖LabelRemoval_Gt m ε Om x y‖ = 3 * (Om x y + ε)) := by
  refine ⟨fun x => ?_, fun x => (LabelRemoval_Gt_entry m hm ε hε Om hOm x x).2, fun x y hxy => ?_⟩
  · have := (LabelRemoval_Gt_entry m hm ε hε Om hOm x x).1
    simpa [entryErr] using this
  · have := (LabelRemoval_Gt_entry m hm ε hε Om hOm x y).1
    simpa [entryErr, hxy] using this

/-- `G` itself is dominated by `G̃`. -/
private lemma LabelRemoval_domG {z : ℂ} {e : ℝ} (hc : LabelRemoval_Cmp W S (msc z) e q)
    (hG : LabelRemoval_Hyp W S (msc z) e q.t q.Φ q.f G) (hm0 : msc z ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) (a₀ b₀ : Zd d L) :
    (∀ a b, ‖G a b‖ ≤ ‖LabelRemoval_Gt (msc z) ε (LabelRemoval_Om W S G q a₀ b₀) a b‖) ∧
    (∀ a, ‖G a a - msc z‖ ≤
      ‖LabelRemoval_Gt (msc z) ε (LabelRemoval_Om W S G q a₀ b₀) a a - msc z‖) := by
  have hδ' : q.t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) ≤ 1 / 8 := hc.δq ▸ hc.δ8
  obtain ⟨hoff, hdd, -, -, -⟩ := hG.basic hδ' hc.m4 hc.m1
  rw [← hc.δq] at hoff hdd
  have hδ0 : 0 ≤ q.δ₁ := (norm_nonneg _).trans (hdd a₀)
  have hOm0 := fun x y => LabelRemoval_Om_nonneg (W := W) (S := S) (G := G)
    (by linarith [hc.t1]) hδ0 hc.Φ0 hc.f0 a₀ b₀ x y
  obtain ⟨f1, f2, f3⟩ := LabelRemoval_Gt_facts hm0 hε hOm0
  have hdiag : ∀ a, ‖G a a - msc z‖ ≤ LabelRemoval_Om W S G q a₀ b₀ a a := by
    intro a; unfold LabelRemoval_Om; rw [if_pos rfl]; exact le_min (hG.diag a) (hdd a)
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · by_cases hab : a = b
    · subst hab
      rw [f2]
      have := norm_sub_norm_le (G a a) (msc z)
      linarith [hdiag a, hε, hOm0 a a]
    · rw [f3 a b hab]
      have h := LabelRemoval_dom_res hc hG hG a (fun _ _ => rfl) a₀ b₀
      -- `Ω_{ab} ≥ |G_{ab}|` off the diagonal
      have hge : ‖G a b‖ ≤ LabelRemoval_Om W S G q a₀ b₀ a b := h.1 b (Ne.symm hab)
      linarith [hOm0 a b]
  · rw [f1]; linarith [hdiag a, hOm0 a a]

/-- A resolvent with row `y` resampled (same minor at `y`, the bounds of `LabelRemoval_Hyp`) is
dominated by `G̃` in the sense of `LabelRemoval_ResDom`, with the bound without path term when `y`
is one of the external indices `a₀`, `b₀`. -/
private lemma LabelRemoval_resdom {z : ℂ} {e : ℝ} (hc : LabelRemoval_Cmp W S (msc z) e q)
    (hG : LabelRemoval_Hyp W S (msc z) e q.t q.Φ q.f G) {G' : Matrix (Zd d L) (Zd d L) ℂ}
    (hG' : LabelRemoval_Hyp W S (msc z) e q.t q.Φ q.f G') (y : Zd d L)
    (hmin : ∀ k l, greenMinor G' y k l = greenMinor G y k l) (hm0 : msc z ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) (a₀ b₀ : Zd d L) :
    LabelRemoval_ResDom G' (LabelRemoval_Gt (msc z) ε (LabelRemoval_Om W S G q a₀ b₀)) z y
      (y = a₀ ∨ y = b₀) := by
  have hδ' : q.t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) ≤ 1 / 8 := hc.δq ▸ hc.δ8
  obtain ⟨-, hdd, -, -, -⟩ := hG.basic hδ' hc.m4 hc.m1
  rw [← hc.δq] at hdd
  have hδ0 : 0 ≤ q.δ₁ := (norm_nonneg _).trans (hdd a₀)
  have hOm0 := fun x y => LabelRemoval_Om_nonneg (W := W) (S := S) (G := G)
    (by linarith [hc.t1]) hδ0 hc.Φ0 hc.f0 a₀ b₀ x y
  obtain ⟨f1, f2, f3⟩ := LabelRemoval_Gt_facts hm0 hε hOm0
  obtain ⟨r1, r2, r3, r4, r5⟩ := LabelRemoval_dom_res hc hG hG' y hmin a₀ b₀
  refine ⟨fun a => ?_, fun a => ?_, fun b hb => ?_, fun a ha => ?_, fun a b hab ha hb => ?_,
    fun hy a b hab ha hb => ?_⟩
  · rw [f2]
    have := norm_sub_norm_le (G' a a) (msc z)
    linarith [r3 a, hOm0 a a]
  · rw [f1]; linarith [r3 a, hOm0 a a]
  · rw [f3 y b (Ne.symm hb)]; linarith [r1 b hb, hOm0 y b]
  · rw [f3 a y ha]; linarith [r2 a ha, hOm0 a y]
  · rw [f3 a b hab, f3 a y ha, f3 y b (Ne.symm hb)]
    have h1 := r4 a b hab ha hb
    have h2 := mul_le_mul (show LabelRemoval_Om W S G q a₀ b₀ a y ≤
      LabelRemoval_Om W S G q a₀ b₀ a y + ε by linarith)
      (show LabelRemoval_Om W S G q a₀ b₀ y b ≤ LabelRemoval_Om W S G q a₀ b₀ y b + ε by linarith)
      (hOm0 y b) (by linarith [hOm0 a y])
    nlinarith [hOm0 a y, hOm0 y b, hOm0 a b]
  · rw [f3 a b hab]; linarith [r5 hy a b hab ha hb, hOm0 a b]

omit [NeZero L] in
/-- `B_{xx} = W^{−d}`. -/
private lemma LabelRemoval_bB_self [NeZero L] {W : ℕ} (hW : 1 ≤ W) (x : Zd d L) :
    bB d L W x x = (W : ℝ) ^ (-(d : ℝ)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold bB
  rw [sub_self, (zdistInf_eq_zero_iff d L).2 rfl, Nat.cast_zero, zero_add, ← Real.rpow_add hW0]
  ring_nf

omit [NeZero L] in
/-- Box sums of a constant matrix `c` with `3^d L^d c ≤ 1`. -/
private lemma LabelRemoval_BoxCtl_const [NeZero L] {W : ℕ} {e c : ℝ} (hc : 0 ≤ c)
    (hcL : 3 ^ d * (L : ℝ) ^ d * c ≤ 1) (hW : 1 ≤ W) (he : 0 ≤ e) :
    LabelRemoval_BoxCtl W e (fun (_ _ : Zd d L) => c) 2 := by
  intro x x₀ K h1 h2
  have hK1 : 1 ≤ K := hW.trans h1
  have hcard := LabelRemoval_card_box_le x₀ K hK1
  have hKL : (K : ℝ) ≤ L := by exact_mod_cast (show K ≤ L by omega)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKd : (K : ℝ) ^ d = (K : ℝ) ^ ((d : ℝ) / 2) * (K : ℝ) ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_add hK0, ← Real.rpow_natCast]; ring_nf
  have hKh : (K : ℝ) ^ ((d : ℝ) / 2) ≤ (L : ℝ) ^ d := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    calc (K : ℝ) ^ ((d : ℝ) / 2) ≤ (L : ℝ) ^ ((d : ℝ) / 2) :=
          Real.rpow_le_rpow hK0.le hKL (by positivity)
      _ ≤ (L : ℝ) ^ (d : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by
          have := Nat.cast_nonneg (α := ℝ) d; linarith)
      _ = (L : ℝ) ^ d := Real.rpow_natCast _ _
  have hsc := LabelRemoval_half_le_scale (d := d) hW h1 he
  calc ∑ y ∈ LabelRemoval_box x₀ K, (c + c) = 2 * c * (LabelRemoval_box x₀ K).card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * c * (3 ^ d * ((K : ℝ) ^ ((d : ℝ) / 2) * (K : ℝ) ^ ((d : ℝ) / 2))) := by
        rw [← hKd, ← mul_pow]; exact mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ 2 * (3 ^ d * (L : ℝ) ^ d * c) * (K : ℝ) ^ ((d : ℝ) / 2) := by
        have := mul_le_mul_of_nonneg_left hKh (by positivity :
          (0 : ℝ) ≤ 2 * c * 3 ^ d * (K : ℝ) ^ ((d : ℝ) / 2))
        nlinarith
    _ ≤ 2 * ((W : ℝ) ^ (e - 2) * (K : ℝ) ^ (2 + (d : ℝ) / 2)) := by
        have h0 : 0 ≤ (K : ℝ) ^ ((d : ℝ) / 2) := by positivity
        nlinarith [mul_le_mul hcL hsc h0 zero_le_one]

/-- **`G̃` satisfies the two bounds of [II, Notation 8.8]**: `‖G̃ − m‖_{w;(1,2)} ≤ W^{e+τ'}` and
`|G̃_{xy} − δ_{xy} m| ≤ W^{τ'} (B_{xy}^{1/2} + Φ)`, under the numerical conditions `hN1`, `hN2`. -/
private lemma LabelRemoval_admissible {z : ℂ} {e : ℝ} (hc : LabelRemoval_Cmp W S (msc z) e q)
    (hG : LabelRemoval_Hyp W S (msc z) e q.t q.Φ q.f G) {R sb ρb : ℝ} {Rn : ℕ}
    (hS : LabelRemoval_SCond W S e q.t R sb ρb Rn) (hm0 : msc z ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hεB : ∀ x y, ε ≤ Real.sqrt (bB d L W x y)) (hεL : 3 ^ d * (L : ℝ) ^ d * ε ≤ 1)
    (hfL : 3 ^ d * (L : ℝ) ^ d * q.f ≤ 1) (a₀ b₀ : Zd d L) (τ' : ℝ)
    (hN1 : (W : ℝ) ^ ((d : ℝ) / 2) * (3 * (5 * q.δ₁ + ε)) +
      3 * (7000 * Real.sqrt (3 ^ d) * q.t ^ 3 * ρb + 2) * (W : ℝ) ^ e ≤ (W : ℝ) ^ (e + τ'))
    (hN2 : 1080 * q.t ^ 2 + 3 ≤ (W : ℝ) ^ τ') :
    weakNorm d L W 1 2 (errAbs (LabelRemoval_Gt (msc z) ε (LabelRemoval_Om W S G q a₀ b₀)) z) ≤
        (W : ℝ) ^ (e + τ') ∧
      ∀ x y, ‖entryErr (LabelRemoval_Gt (msc z) ε (LabelRemoval_Om W S G q a₀ b₀)) (msc z) x y‖ ≤
        (W : ℝ) ^ τ' * (Real.sqrt (bB d L W x y) + q.Φ) := by
  have hδ' : q.t * (W : ℝ) ^ (-((d : ℝ) / 2) + e) ≤ 1 / 8 := hc.δq ▸ hc.δ8
  have hδ0 : 0 ≤ q.δ₁ := by rw [hc.δq]; have := hc.t1; positivity
  set Om := LabelRemoval_Om W S G q a₀ b₀ with hOmd
  have hOm0 : ∀ x y, 0 ≤ Om x y := fun x y => LabelRemoval_Om_nonneg (W := W) (S := S) (G := G)
    (by linarith [hc.t1]) hδ0 hc.Φ0 hc.f0 a₀ b₀ x y
  have hentry : ∀ x y, ‖entryErr (LabelRemoval_Gt (msc z) ε Om) (msc z) x y‖ = 3 * (Om x y + ε) :=
    fun x y => (LabelRemoval_Gt_entry (msc z) hm0 ε hε Om hOm0 x y).1
  constructor
  · set Cε : Matrix (Zd d L) (Zd d L) ℝ := fun _ _ => ε with hCε
    have hA : errAbs (LabelRemoval_Gt (msc z) ε Om) z = (3 : ℝ) • (Om + Cε) := by
      ext x y
      simp only [errAbs, hentry, Matrix.smul_apply, smul_eq_mul]
      rfl
    have hbox := ((LabelRemoval_Om_box hG hS hc.δq hc.δ8 hc.Φ0 hc.m4 hc.m1 hc.f0 hfL a₀ b₀).add
      (LabelRemoval_BoxCtl_const hε hεL hS.W1 hS.e0)).smul 3 (by norm_num)
    rw [hA]
    refine (LabelRemoval_weakNorm_le (Mx := 3 * (5 * q.δ₁ + ε)) hS.W1 (fun x y => ?_)
      (fun x y => ?_) hbox (by have := hS.t1; have := hS.ρb1; positivity)).trans ?_
    · change 0 ≤ 3 * (Om x y + ε)
      have := hOm0 x y; positivity
    · change 3 * (Om x y + ε) ≤ _
      have := LabelRemoval_Om_le_max hG hc.δq hc.δ8 hc.m4 hc.m1 a₀ b₀ x y
      linarith
    · linarith
  · intro x y
    rw [hentry]
    have hB0 : 0 ≤ Real.sqrt (bB d L W x y) := Real.sqrt_nonneg _
    have hΦ := hc.Φ0
    have ht := hc.t1
    obtain ⟨e1, e2⟩ := LabelRemoval_Om_le_entry hG hc.S0 hc.S1 hc.δq hc.δ8 hc.δt hc.t1 hc.Φ0
      hc.m4 hc.m1 hc.fB hc.f0 a₀ b₀ x y
    by_cases hxy : x = y
    · subst hxy
      have hBx : Real.sqrt (bB d L W x x) = (W : ℝ) ^ (-((d : ℝ) / 2)) := by
        rw [LabelRemoval_bB_self hS.W1, Real.sqrt_eq_iff_mul_self_eq (by positivity)
          (by positivity), ← Real.rpow_add (by exact_mod_cast hS.W1)]
        ring_nf
      rw [hBx] at hB0 ⊢
      have hεx := hεB x x
      rw [hBx] at hεx
      have h1 : 3 * (Om x x + ε) ≤ (3 * q.t + 3) * ((W : ℝ) ^ (-((d : ℝ) / 2)) + q.Φ) := by
        nlinarith
      have h2 : 3 * q.t + 3 ≤ (W : ℝ) ^ τ' := by nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
    · have h0 := e1 hxy
      unfold LabelRemoval_E0 at h0
      have hεx := hεB x y
      have h1 : 3 * (Om x y + ε) ≤ (1080 * q.t ^ 2 + 3) * (Real.sqrt (bB d L W x y) + q.Φ) := by
        nlinarith
      exact h1.trans (mul_le_mul_of_nonneg_right hN2 (by positivity))

end Dom

/-! ## The numerical conditions along the filter -/

/-- `∀ᶠ W in atTop, W^α ≤ c` for `α < 0`, `c > 0`. -/
private lemma LabelRemoval_ev_small {α c : ℝ} (hα : α < 0) (hc : 0 < c) :
    ∀ᶠ W : ℝ in atTop, W ^ α ≤ c := by
  have := (tendsto_rpow_neg_atTop (by linarith : 0 < -α)).eventually (ge_mem_nhds hc)
  filter_upwards [this] with W hW
  simpa using hW

/-- `∀ᶠ W in atTop, C ≤ W^α` for `α > 0`. -/
private lemma LabelRemoval_ev_large {α : ℝ} (hα : 0 < α) (C : ℝ) :
    ∀ᶠ W : ℝ in atTop, C ≤ W ^ α :=
  (tendsto_rpow_atTop hα).eventually (eventually_ge_atTop C)

/-- On `adm(c₀, c₁)` with `W ≥ 1`: `W ≤ L`, `L ≤ W^{1/c₁}` and `L^d ≤ W^{d/c₁}`. -/
private lemma LabelRemoval_L_le {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (p : SizeL)
    (hp : p.1 ∈ adm c₀ c₁) (hW : 1 ≤ sizeW p) (d : ℕ) :
    sizeW p ≤ (p.1.2 : ℝ) ∧ (p.1.2 : ℝ) ≤ sizeW p ^ (1 / c₁) ∧
      (p.1.2 : ℝ) ^ d ≤ sizeW p ^ ((d : ℝ) / c₁) := by
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  have hW0 : 0 < sizeW p := by linarith
  have h1 : sizeW p ≤ (p.1.2 : ℝ) := by
    have := hp.2
    refine this.trans ?_
    exact Real.rpow_le_self_of_one_le hL1 (by linarith) |>.trans le_rfl
  have h2 : (p.1.2 : ℝ) ≤ sizeW p ^ (1 / c₁) := by
    have h := hp.1
    have : (p.1.2 : ℝ) = ((p.1.2 : ℝ) ^ c₁) ^ (1 / c₁) := by
      rw [← Real.rpow_mul (by linarith), mul_one_div_cancel hc₁.ne', Real.rpow_one]
    rw [this]
    exact Real.rpow_le_rpow (by positivity) h (by positivity)
  refine ⟨h1, h2, ?_⟩
  calc (p.1.2 : ℝ) ^ d ≤ (sizeW p ^ (1 / c₁)) ^ d := pow_le_pow_left₀ (by linarith) h2 d
    _ = sizeW p ^ ((d : ℝ) / c₁) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf

/-- The lower bound `B_{xy} ≥ W^{−2} (2L)^{2−d}` for `1 ≤ W ≤ L`, `d ≥ 2`. -/
private lemma LabelRemoval_bB_ge {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (hWL : W ≤ L)
    (x y : Zd d L) : (W : ℝ) ^ (-2 : ℝ) * (2 * (L : ℝ)) ^ (2 - (d : ℝ)) ≤ bB d L W x y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold bB
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hW0.le _)
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  have h1 : (zdistInf d L (x - y) : ℝ) ≤ L := by
    have := zdistInf_le_half d L (x - y)
    exact_mod_cast this.trans (Nat.div_le_self _ _)
  have h2 : (W : ℝ) ≤ L := by exact_mod_cast hWL
  linarith

/-- The band of `S` on `adm(c₀, c₁)` ([I, (1.8)]): for every `k` there is `C ≥ 0` with
`s_{yk} ≤ C W^{−d} (W^{τ_b})^{−k}` at distance at least `W^{1 + τ_b}`. -/
private lemma LabelRemoval_band (d : ℕ) (P : Profile d) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (τb : ℝ)
    (hτb : 0 ≤ τb) (ks : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : SizeL, p.1 ∈ adm c₀ c₁ → 1 ≤ sizeW p →
      ∀ y k : Zd d p.1.2, sizeW p ^ (1 + τb) ≤ zdistInf d p.1.2 (y - k) →
        Smat P.ψ p.1.1 p.1.2 y k ≤ C * sizeW p ^ (-(d : ℝ)) / (sizeW p ^ τb) ^ ks := by
  obtain ⟨C, hC⟩ := subpoly_adm d P c₀ c₁ hc₀ ks
  refine ⟨|C|, abs_nonneg _, fun p hp hW y k hyk => ?_⟩
  have hW0 : 0 < sizeW p := by linarith
  have h := hC p.1.1 p.1.2 hp (y - k)
  have hτ : sizeW p ^ τb ≤ (zdistInf d p.1.2 (y - k) : ℝ) / sizeW p := by
    rw [le_div_iff₀ hW0]
    calc sizeW p ^ τb * sizeW p = sizeW p ^ (1 + τb) := by
          rw [Real.rpow_add hW0, Real.rpow_one, mul_comm]
      _ ≤ _ := hyk
  have hpos : 0 < (sizeW p ^ τb) ^ ks := by positivity
  have hpow : (sizeW p ^ τb) ^ ks ≤ ((zdistInf d p.1.2 (y - k) : ℝ) / p.1.1) ^ ks :=
    pow_le_pow_left₀ (by positivity) hτ ks
  have hS : Smat P.ψ p.1.1 p.1.2 y k ≤ |fWL P.ψ p.1.1 p.1.2 (y - k)| := le_abs_self _
  rw [le_div_iff₀ hpos]
  have hWd : sizeW p ^ (-(d : ℝ)) = 1 / (p.1.1 : ℝ) ^ d := by
    rw [Real.rpow_neg hW0.le, Real.rpow_natCast, one_div]; rfl
  rw [hWd]
  calc Smat P.ψ p.1.1 p.1.2 y k * (sizeW p ^ τb) ^ ks
      ≤ |fWL P.ψ p.1.1 p.1.2 (y - k)| * ((zdistInf d p.1.2 (y - k) : ℝ) / p.1.1) ^ ks := by
        refine mul_le_mul hS hpow hpos.le (abs_nonneg _)
    _ = ((zdistInf d p.1.2 (y - k) : ℝ) / p.1.1) ^ ks * |fWL P.ψ p.1.1 p.1.2 (y - k)| := by ring
    _ ≤ C / (p.1.1 : ℝ) ^ d := h
    _ ≤ |C| * (1 / (p.1.1 : ℝ) ^ d) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (le_abs_self C) (by positivity)

/-- `W^{−C} ≤ 1/16` for `W ≥ 2`, `C ≥ 4`. -/
private lemma LabelRemoval_num_f {W C : ℝ} (hW : 2 ≤ W) (hC : 4 ≤ C) : W ^ (-C) ≤ 1 / 16 := by
  have hW0 : 0 < W := by linarith
  have : W ^ (-C) ≤ W ^ (-4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  refine this.trans ?_
  rw [Real.rpow_neg hW0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    inv_eq_one_div]
  have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hW 4
  exact one_div_le_one_div_of_le (by norm_num) (by norm_num at this ⊢; linarith)

/-- The floor `W^{−C_f}`, `C_f = 3d + d/c₁ + 4`, is at most `B_{xy}^{1/2}` when `2 ≤ W ≤ L ≤
W^{1/c₁}`. -/
private lemma LabelRemoval_num_fB {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hW : (2 : ℝ) ≤ W) (hWL : W ≤ L) (hL : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁)) (x y : Zd d L) :
    (W : ℝ) ^ (-(3 * (d : ℝ) + d / c₁ + 4)) ≤ Real.sqrt (bB d L W x y) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hB := LabelRemoval_bB_ge hd hWn hWL x y
  refine Real.le_sqrt_of_sq_le (le_trans ?_ hB)
  have h2L : 2 * (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁ + 1) := by
    rw [Real.rpow_add hW0, Real.rpow_one]; nlinarith [Real.rpow_nonneg hW0.le (1 / c₁)]
  have hpow : (W : ℝ) ^ ((1 / c₁ + 1) * (2 - (d : ℝ))) ≤ (2 * (L : ℝ)) ^ (2 - (d : ℝ)) := by
    rw [Real.rpow_mul hW0.le]
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h2L (by linarith)
  have hsq : ((W : ℝ) ^ (-(3 * (d : ℝ) + d / c₁ + 4))) ^ 2 =
      (W : ℝ) ^ (-2 * (3 * (d : ℝ) + d / c₁ + 4)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  rw [hsq]
  have hexp : -2 * (3 * (d : ℝ) + d / c₁ + 4) ≤ -2 + (1 / c₁ + 1) * (2 - (d : ℝ)) := by
    have e1 : (1 / c₁) * (d : ℝ) = (d : ℝ) / c₁ := by ring
    have e2 : 0 ≤ 1 / c₁ := by positivity
    nlinarith
  calc (W : ℝ) ^ (-2 * (3 * (d : ℝ) + d / c₁ + 4))
      ≤ (W : ℝ) ^ (-2 + (1 / c₁ + 1) * (2 - (d : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le hW1 hexp
    _ = (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ ((1 / c₁ + 1) * (2 - (d : ℝ))) := Real.rpow_add hW0 _ _
    _ ≤ (W : ℝ) ^ (-2 : ℝ) * (2 * (L : ℝ)) ^ (2 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hW0.le _)

/-- `3^d L^d W^{−C_f} ≤ 1` when `W ≥ 2`, `L^d ≤ W^{d/c₁}`. -/
private lemma LabelRemoval_num_fL {d : ℕ} {W L c₁ : ℝ} (hW : 2 ≤ W) (hL0 : 0 ≤ L)
    (hLd : L ^ d ≤ W ^ ((d : ℝ) / c₁)) :
    3 ^ d * L ^ d * W ^ (-(3 * (d : ℝ) + d / c₁ + 4)) ≤ 1 := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have h3 : (3 : ℝ) ^ d ≤ W ^ (2 * (d : ℝ)) := by
    rw [show 2 * (d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by nlinarith) d
  calc 3 ^ d * L ^ d * W ^ (-(3 * (d : ℝ) + d / c₁ + 4))
      ≤ W ^ (2 * (d : ℝ)) * W ^ ((d : ℝ) / c₁) * W ^ (-(3 * (d : ℝ) + d / c₁ + 4)) := by
        gcongr
    _ = W ^ (-(d : ℝ) - 4) := by rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by
        have := Nat.cast_nonneg (α := ℝ) d; linarith)

/-- The weak-norm condition `hN1` of `LabelRemoval_admissible` at `t = W^{τ₁}`, `ρ_b = 81 W^{4τ₁}`,
`ε = W^{−C_f}`, given `1701024 · 3^{d/2} ≤ W^{τ' − 7τ₁}`. -/
private lemma LabelRemoval_num_N1 {d : ℕ} {W τ₁ τ' ε₀ c₁ : ℝ} (hW : 1 ≤ W) (hτ₁ : 0 < τ₁)
    (hd : (8 : ℝ) ≤ d) (hε₀ : 0 < ε₀) (hc₁ : 0 < c₁)
    (h6 : 1701024 * Real.sqrt (3 ^ d) ≤ W ^ (τ' - 7 * τ₁)) :
    W ^ ((d : ℝ) / 2) * (3 * (5 * (W ^ τ₁ * W ^ (-((d : ℝ) / 2) + ε₀)) +
        W ^ (-(3 * (d : ℝ) + d / c₁ + 4)))) +
      3 * (7000 * Real.sqrt (3 ^ d) * (W ^ τ₁) ^ 3 * (81 * W ^ (4 * τ₁)) + 2) * W ^ ε₀ ≤
        W ^ (ε₀ + τ') := by
  have hW0 : 0 < W := by linarith
  have hrw : ∀ a b : ℝ, W ^ a * W ^ b = W ^ (a + b) := fun a b => (Real.rpow_add hW0 a b).symm
  have ha : W ^ ((d : ℝ) / 2) * (W ^ τ₁ * W ^ (-((d : ℝ) / 2) + ε₀)) = W ^ τ₁ * W ^ ε₀ := by
    rw [hrw, hrw, hrw]; ring_nf
  have hb : W ^ ((d : ℝ) / 2) * W ^ (-(3 * (d : ℝ) + d / c₁ + 4)) ≤ W ^ ε₀ := by
    rw [hrw]; exact Real.rpow_le_rpow_of_exponent_le hW (by
      have : 0 ≤ (d : ℝ) / c₁ := by positivity
      linarith)
  have hc : (W ^ τ₁) ^ 3 * (81 * W ^ (4 * τ₁)) = 81 * W ^ (7 * τ₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, mul_left_comm, hrw]; push_cast; ring_nf
  have h7τ : W ^ τ₁ ≤ W ^ (7 * τ₁) := Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have h7 : 1 ≤ W ^ (7 * τ₁) := Real.one_le_rpow hW (by linarith)
  have hs3 : 1 ≤ Real.sqrt (3 ^ d) := Real.one_le_sqrt.2 (one_le_pow₀ (by norm_num))
  have hWe : 0 < W ^ ε₀ := Real.rpow_pos_of_pos hW0 _
  have h6' : 1701024 * Real.sqrt (3 ^ d) * W ^ (7 * τ₁) ≤ W ^ τ' := by
    have := mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hW0.le (7 * τ₁))
    rwa [hrw, show τ' - 7 * τ₁ + 7 * τ₁ = τ' by ring] at this
  rw [← hrw ε₀ τ']
  have e1 : W ^ ((d : ℝ) / 2) * (3 * (5 * (W ^ τ₁ * W ^ (-((d : ℝ) / 2) + ε₀)) +
      W ^ (-(3 * (d : ℝ) + d / c₁ + 4)))) =
      15 * (W ^ ((d : ℝ) / 2) * (W ^ τ₁ * W ^ (-((d : ℝ) / 2) + ε₀))) +
        3 * (W ^ ((d : ℝ) / 2) * W ^ (-(3 * (d : ℝ) + d / c₁ + 4))) := by ring
  have e2 : 7000 * Real.sqrt (3 ^ d) * (W ^ τ₁) ^ 3 * (81 * W ^ (4 * τ₁)) =
      7000 * Real.sqrt (3 ^ d) * ((W ^ τ₁) ^ 3 * (81 * W ^ (4 * τ₁))) := by ring
  rw [e1, ha, e2, hc]
  have key : 15 * W ^ τ₁ + 3 + 3 * (7000 * Real.sqrt (3 ^ d) * (81 * W ^ (7 * τ₁)) + 2) ≤
      W ^ τ' := by
    nlinarith [mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ Real.sqrt (3 ^ d))]
  have := mul_le_mul_of_nonneg_left key hWe.le
  nlinarith

/-- The conditions on `S` (`LabelRemoval_SCond`) at `ρ_b = 81 W^{4τ₁}`, `R = ⌈W^{1+τ₁}⌉` and
`s_b = C_b W^{−d} / (W^{τ₁})^{k}`. -/
private lemma LabelRemoval_num_S {d : ℕ} (P : Profile d) {c₀ c₁ ε₀ τ₁ : ℝ} (hc₀ : 0 < c₀)
    (hε₀ : 0 < ε₀) (hτ₁ : 0 < τ₁) {Cb : ℝ} (hCb : 0 ≤ Cb) {ks : ℕ} (p : SizeL)
    (hadm : p.1 ∈ adm c₀ c₁) (hW : 2 ≤ sizeW p)
    (hds : Smat P.ψ p.1.1 p.1.2 ∈ doublyStochastic ℝ (Zd d p.1.2))
    (hband : ∀ y k : Zd d p.1.2, sizeW p ^ (1 + τ₁) ≤ zdistInf d p.1.2 (y - k) →
      Smat P.ψ p.1.1 p.1.2 y k ≤ Cb * sizeW p ^ (-(d : ℝ)) / (sizeW p ^ τ₁) ^ ks)
    (hsbL : 4 * ((p.1.2 : ℝ) ^ d) ^ 2 * (Cb * sizeW p ^ (-(d : ℝ)) / (sizeW p ^ τ₁) ^ ks) ≤ 1) :
    LabelRemoval_SCond p.1.1 (Smat P.ψ p.1.1 p.1.2) ε₀ (sizeW p ^ τ₁) 0
      (Cb * sizeW p ^ (-(d : ℝ)) / (sizeW p ^ τ₁) ^ ks) (81 * sizeW p ^ (4 * τ₁))
      ⌈sizeW p ^ (1 + τ₁)⌉₊ := by
  have hW1 : (1 : ℝ) ≤ sizeW p := by linarith
  have hW0 : (0 : ℝ) < sizeW p := by linarith
  have hWn : 1 ≤ p.1.1 := by have : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW1; exact_mod_cast this
  refine ⟨fun x y => nonneg_of_mem_doublyStochastic hds,
    fun x => sum_row_of_mem_doublyStochastic hds x,
    fun y => sum_col_of_mem_doublyStochastic hds y, fun y k hyk => hband y k
      ((Nat.le_ceil _).trans (by exact_mod_cast hyk)), by positivity, hsbL, ?_, ?_, hε₀.le, hWn,
    Real.one_le_rpow hW1 hτ₁.le⟩
  · intro K hK
    have hK0 : sizeW p ≤ (K : ℝ) := by
      have : (p.1.1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      exact this
    have ht1 : 1 ≤ sizeW p ^ τ₁ := Real.one_le_rpow hW1 hτ₁.le
    have hR : (⌈sizeW p ^ (1 + τ₁)⌉₊ : ℝ) ≤ 2 * sizeW p ^ τ₁ * K := by
      have h1' : (⌈sizeW p ^ (1 + τ₁)⌉₊ : ℝ) ≤ sizeW p ^ (1 + τ₁) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have h2' : sizeW p ^ (1 + τ₁) = sizeW p ^ τ₁ * sizeW p := by
        rw [Real.rpow_add hW0, Real.rpow_one, mul_comm]
      nlinarith
    have hKR : (K : ℝ) + ⌈sizeW p ^ (1 + τ₁)⌉₊ ≤ 3 * sizeW p ^ τ₁ * K := by nlinarith
    have h4 : (3 * sizeW p ^ τ₁ * K) ^ 4 = 81 * sizeW p ^ (4 * τ₁) * (K : ℝ) ^ 4 := by
      rw [mul_pow, mul_pow, ← Real.rpow_natCast (sizeW p ^ τ₁), ← Real.rpow_mul hW0.le]
      push_cast; ring_nf
    rw [← h4]
    exact pow_le_pow_left₀ (by positivity) hKR 4
  · have := Real.one_le_rpow hW1 (by linarith : 0 ≤ 4 * τ₁); linarith

/-! ## The product space -/

/-- The pairs `(ω, η)` for which some resampled sample `ω^{[y,η]}` is outside a set `G` have
product measure at most `|Z_L^d|` times the outer measure of the complement of `G`. -/
private lemma LabelRemoval_prod_bad {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (Gd : Set (Sample ι)) :
    (gaussLaw S).prod (gaussLaw S) {q | ∃ y, LabelRemoval_res y q.2 q.1 ∉ Gd} ≤
      (Fintype.card ι : ℝ≥0∞) * gaussLaw S Gdᶜ := by
  have hsub : {q : Sample ι × Sample ι | ∃ y, LabelRemoval_res y q.2 q.1 ∉ Gd} ⊆
      ⋃ y, (fun q : Sample ι × Sample ι => (rowCoords y).piecewise q.2 q.1) ⁻¹' Gdᶜ := by
    rintro q ⟨y, hy⟩
    exact Set.mem_iUnion.2 ⟨y, hy⟩
  calc (gaussLaw S).prod (gaussLaw S) {q | ∃ y, LabelRemoval_res y q.2 q.1 ∉ Gd}
      ≤ (gaussLaw S).prod (gaussLaw S)
          (⋃ y, (fun q : Sample ι × Sample ι => (rowCoords y).piecewise q.2 q.1) ⁻¹' Gdᶜ) :=
        measure_mono hsub
    _ ≤ ∑ y, (gaussLaw S).prod (gaussLaw S)
          ((fun q : Sample ι × Sample ι => (rowCoords y).piecewise q.2 q.1) ⁻¹' Gdᶜ) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _y : ι, gaussLaw S Gdᶜ := Finset.sum_le_sum fun y _ =>
        LabelRemoval_preimage_le (LabelRemoval.measurePreserving_piecewise S (rowCoords y)) _
    _ = (Fintype.card ι : ℝ≥0∞) * gaussLaw S Gdᶜ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## The deterministic bounds off the event and the norm of the sample -/

section OffEvent

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `|h_ab(ω)| ≤ 2 ‖ω‖`. -/
private lemma LabelRemoval_norm_hmat_le (ω : Sample ι) (a b : ι) : ‖hmat ω a b‖ ≤ 2 * ‖ω‖ := by
  have h1 : ∀ c : Coord ι, ‖((ω c : ℝ) : ℂ)‖ ≤ ‖ω‖ := fun c => by
    rw [Complex.norm_real]; exact norm_le_pi_norm ω c
  have hI : ∀ c : Coord ι, ‖I * ((ω c : ℝ) : ℂ)‖ ≤ ‖ω‖ := fun c => by
    rw [norm_mul, Complex.norm_I, one_mul]; exact h1 c
  unfold hmat
  simp only [Matrix.of_apply]
  split_ifs
  · linarith [norm_add_le ((ω (.inr (⟨(a, b), ‹_›⟩, true)) : ℝ) : ℂ)
      (I * ((ω (.inr (⟨(a, b), ‹_›⟩, false)) : ℝ) : ℂ)), h1 (.inr (⟨(a, b), ‹_›⟩, true)),
      hI (.inr (⟨(a, b), ‹_›⟩, false))]
  · linarith [norm_sub_le ((ω (.inr (⟨(b, a), ‹_›⟩, true)) : ℝ) : ℂ)
      (I * ((ω (.inr (⟨(b, a), ‹_›⟩, false)) : ℝ) : ℂ)), h1 (.inr (⟨(b, a), ‹_›⟩, true)),
      hI (.inr (⟨(b, a), ‹_›⟩, false))]
  · linarith [h1 (.inl a), norm_nonneg ω]

/-- `|(G_aa)⁻¹| ≤ (2 + |z| + |ι|² · 4/Im z) (1 + ‖ω‖)²`, by the Schur complement formula
`(G_aa)⁻¹ = h_aa − z − Σ_{k,l ≠ a} h_ak G^{(a)}_kl h_la`. -/
private lemma LabelRemoval_inv_diag_le {z : ℂ} (hz : 0 < z.im) (ω : Sample ι) (a : ι) :
    ‖(green (hmat ω) z a a)⁻¹‖ ≤
      (2 + ‖z‖ + (Fintype.card ι : ℝ) ^ 2 * (4 * z.im⁻¹)) * (1 + ‖ω‖) ^ 2 := by
  set N : ℕ := Fintype.card {b : ι // b ≠ a}
  have hNc : (N : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_subtype_le _
  set c : ℝ := z.im⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hH := hmat_isHermitian ω
  have hmg : ∀ k l : {b : ι // b ≠ a}, ‖minorGreen (green (hmat ω) z) a k l‖ ≤ c := by
    intro k l
    rw [← inv_minor_resolvent hH hz a]
    have h : ‖green ((hmat ω).submatrix (Subtype.val : {b // b ≠ a} → ι) Subtype.val) z k l‖ ≤
        |z.im|⁻¹ := norm_green_entry_le (hH.submatrix _) hz.ne' k l
    rw [abs_of_pos hz] at h
    exact h
  rw [green_diag_schur hH hz a, inv_inv]
  have hr : 0 ≤ ‖ω‖ := norm_nonneg _
  have hp : (1 : ℝ) ≤ (1 + ‖ω‖) ^ 2 := one_le_pow₀ (by linarith)
  have hterm : ∀ k l : {b : ι // b ≠ a},
      ‖hmat ω a k.1 * minorGreen (green (hmat ω) z) a k l * hmat ω l.1 a‖
        ≤ 4 * c * (1 + ‖ω‖) ^ 2 := by
    intro k l
    rw [norm_mul, norm_mul]
    have e1 := LabelRemoval_norm_hmat_le ω a k.1
    have e2 := LabelRemoval_norm_hmat_le ω l.1 a
    have e3 := hmg k l
    calc ‖hmat ω a k.1‖ * ‖minorGreen (green (hmat ω) z) a k l‖ * ‖hmat ω l.1 a‖
        ≤ (2 * ‖ω‖) * c * (2 * ‖ω‖) := by gcongr
      _ = 4 * c * ‖ω‖ ^ 2 := by ring
      _ ≤ 4 * c * (1 + ‖ω‖) ^ 2 := by gcongr; linarith
  have hsum : ‖∑ k : {b : ι // b ≠ a}, ∑ l : {b : ι // b ≠ a},
      hmat ω a k.1 * minorGreen (green (hmat ω) z) a k l * hmat ω l.1 a‖
        ≤ (N : ℝ) ^ 2 * (4 * c * (1 + ‖ω‖) ^ 2) := by
    calc _ ≤ ∑ k : {b : ι // b ≠ a}, ∑ l : {b : ι // b ≠ a},
          ‖hmat ω a k.1 * minorGreen (green (hmat ω) z) a k l * hmat ω l.1 a‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
      _ ≤ ∑ k : {b : ι // b ≠ a}, ∑ l : {b : ι // b ≠ a}, 4 * c * (1 + ‖ω‖) ^ 2 :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
      _ = (N : ℝ) ^ 2 * (4 * c * (1 + ‖ω‖) ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hd : ‖hmat ω a a‖ ≤ 2 * (1 + ‖ω‖) ^ 2 := by
    nlinarith [LabelRemoval_norm_hmat_le ω a a]
  have hN2 : (N : ℝ) ^ 2 ≤ (Fintype.card ι : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hNc 2
  calc ‖hmat ω a a - z - ∑ k : {b : ι // b ≠ a}, ∑ l : {b : ι // b ≠ a},
        hmat ω a k.1 * minorGreen (green (hmat ω) z) a k l * hmat ω l.1 a‖
      ≤ ‖hmat ω a a‖ + ‖z‖ + ‖∑ k : {b : ι // b ≠ a}, ∑ l : {b : ι // b ≠ a},
        hmat ω a k.1 * minorGreen (green (hmat ω) z) a k l * hmat ω l.1 a‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * (1 + ‖ω‖) ^ 2 + ‖z‖ * (1 + ‖ω‖) ^ 2 + (N : ℝ) ^ 2 * (4 * c * (1 + ‖ω‖) ^ 2) :=
        add_le_add (add_le_add hd (le_mul_of_one_le_right (norm_nonneg _) hp)) hsum
    _ ≤ 2 * (1 + ‖ω‖) ^ 2 + ‖z‖ * (1 + ‖ω‖) ^ 2 +
          (Fintype.card ι : ℝ) ^ 2 * (4 * c * (1 + ‖ω‖) ^ 2) := by gcongr
    _ = (2 + ‖z‖ + (Fintype.card ι : ℝ) ^ 2 * (4 * c)) * (1 + ‖ω‖) ^ 2 := by ring

/-- The number of coordinates of the sample: `|Coord ι| ≤ 3 |ι|²`. -/
private lemma LabelRemoval_card_coord :
    (Fintype.card (Coord ι) : ℝ) ≤ 3 * (Fintype.card ι : ℝ) ^ 2 := by
  have h1 : Fintype.card (OffPair ι) ≤ Fintype.card ι ^ 2 := by
    have := Fintype.card_subtype_le (fun p : ι × ι => idxKey ι p.1 < idxKey ι p.2)
    rwa [Fintype.card_prod, ← pow_two] at this
  have h2 : Fintype.card ι ≤ Fintype.card ι ^ 2 := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · rw [h]; norm_num
    · exact Nat.le_self_pow (by norm_num) _
  have : Fintype.card (Coord ι) ≤ 3 * Fintype.card ι ^ 2 := by
    simp only [Coord, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
    omega
  exact_mod_cast this

/-- The coordinate variances of a doubly stochastic matrix are at most `1`. -/
private lemma LabelRemoval_coordVar_le (S : Matrix ι ι ℝ) (hS : S ∈ doublyStochastic ℝ ι)
    (c : Coord ι) : coordVar S c ≤ 1 := by
  have h1 : ∀ x y, S x y ≤ 1 := fun x y => le_one_of_mem_doublyStochastic hS
  have h0 : ∀ x y, 0 ≤ S x y := fun x y => nonneg_of_mem_doublyStochastic hS
  rcases c with x | ⟨e, _⟩
  · simp only [coordVar]
    rw [Real.toNNReal_le_one]; exact h1 x x
  · simp only [coordVar]
    rw [Real.toNNReal_le_one]; linarith [h1 e.1.1 e.1.2, h0 e.1.1 e.1.2]

/-- **The norm of the sample**: `P(‖ω‖ > t) ≤ |Coord ι| E|Z|^k / t^k` for coordinate variances at
most `1` (Markov's inequality on every coordinate). -/
private lemma LabelRemoval_norm_tail (S : Matrix ι ι ℝ) (hS : ∀ c, coordVar S c ≤ 1) (t : ℝ)
    (ht : 0 < t) (k : ℕ) :
    (gaussLaw S).real {ω | t < ‖ω‖} ≤
      Fintype.card (Coord ι) * LabelRemoval.gaussMoment k / t ^ k := by
  have := isProbabilityMeasure_gaussLaw S
  have hsub : {ω : Sample ι | t < ‖ω‖} ⊆ ⋃ c, {ω | t ^ k ≤ |ω c| ^ k} := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hno
    have : ‖ω‖ ≤ t := (pi_norm_le_iff_of_nonneg ht.le).2 fun c => by
      rw [Real.norm_eq_abs]
      by_contra h
      exact absurd (hno c) (not_lt.2 (pow_le_pow_left₀ ht.le (le_of_lt (not_le.1 h)) k))
    exact absurd hω (not_lt.2 this)
  have hc : ∀ c : Coord ι, (gaussLaw S).real {ω | t ^ k ≤ |ω c| ^ k} ≤
      LabelRemoval.gaussMoment k / t ^ k := by
    intro c
    have hmp : MeasurePreserving (fun η : Sample ι => η c) (gaussLaw S)
        (gaussianReal 0 (coordVar S c)) :=
      measurePreserving_eval (fun c => gaussianReal 0 (coordVar S c)) c
    have hint0 := LabelRemoval_integrable_abs_pow (coordVar S c) k
    have hint : Integrable (fun η : Sample ι => |η c| ^ k) (gaussLaw S) := by
      rw [← hmp.map_eq] at hint0
      exact hint0.comp_measurable hmp.measurable
    have hI : ∫ η, |η c| ^ k ∂(gaussLaw S) ≤ LabelRemoval.gaussMoment k := by
      have e : ∫ η, |η c| ^ k ∂(gaussLaw S) =
          ∫ x, |x| ^ k ∂(gaussianReal 0 (coordVar S c)) := by
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)]
      rw [e]
      exact LabelRemoval_gaussMoment_le (coordVar S c) (hS c) k
    have hM := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun η => by positivity)
      hint (t ^ k)
    have htk : 0 < t ^ k := pow_pos ht k
    rw [le_div_iff₀ htk, mul_comm]
    exact hM.trans hI
  calc (gaussLaw S).real {ω | t < ‖ω‖} ≤ (gaussLaw S).real (⋃ c, {ω | t ^ k ≤ |ω c| ^ k}) :=
        measureReal_mono hsub
    _ ≤ ∑ c, (gaussLaw S).real {ω | t ^ k ≤ |ω c| ^ k} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : Coord ι, LabelRemoval.gaussMoment k / t ^ k := Finset.sum_le_sum fun c _ => hc c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end OffEvent

/-- The bound `M = 6 |Z_L^d|² (W^a + 1)` of the resolvent entries and of `(Im z)⁻¹`-weighted inverse
diagonal entries off the event, for `Im z ≥ W^{−a}`. -/
private def LabelRemoval_Mres (d L : ℕ) (W a : ℝ) : ℝ := 6 * ((L : ℝ) ^ d) ^ 2 * (W ^ a + 1)

/-- The bound `M_b = 8 (R + 1) 4^R M` of the random factors off the event, `R` the number of
components of `Γ.wDLights`. -/
private def LabelRemoval_Mb (R d L : ℕ) (W a : ℝ) : ℝ :=
  8 * ((R : ℝ) + 1) * 4 ^ R * LabelRemoval_Mres d L W a

/-- `M + 4 (d + 1) (4M)^d ≤ (8 (R + 1) 4^R M)^{d+1}` for `M ≥ 1` and `d ≤ R`. -/
private lemma LabelRemoval_Mb_pow (M : ℝ) (hM : 1 ≤ M) (R dd : ℕ) (hdd : dd ≤ R) :
    M + 4 * ((dd : ℝ) + 1) * (4 * M) ^ dd ≤ (8 * ((R : ℝ) + 1) * 4 ^ R * M) ^ (dd + 1) := by
  set Mb := 8 * ((R : ℝ) + 1) * 4 ^ R * M with hMb
  have hdd' : (dd : ℝ) ≤ R := by exact_mod_cast hdd
  have h4 : (4 : ℝ) ^ dd ≤ 4 ^ R := pow_le_pow_right₀ (by norm_num) hdd
  have h41 : (1 : ℝ) ≤ 4 ^ dd := one_le_pow₀ (by norm_num)
  have h1 : 8 * ((dd : ℝ) + 1) * 4 ^ dd * M ≤ Mb := by
    rw [hMb]; gcongr
  have hK : (1 : ℝ) ≤ 8 * ((dd : ℝ) + 1) * 4 ^ dd := by
    have : (0 : ℝ) ≤ dd := Nat.cast_nonneg _
    nlinarith
  have h2 : M ≤ Mb := le_trans (le_mul_of_one_le_left (by linarith) hK) h1
  have hMd : (1 : ℝ) ≤ M ^ dd := one_le_pow₀ hM
  have h3 : M ^ dd ≤ Mb ^ dd := pow_le_pow_left₀ (by linarith) h2 dd
  have hA : (0 : ℝ) ≤ 4 * ((dd : ℝ) + 1) * 4 ^ dd := by positivity
  calc M + 4 * ((dd : ℝ) + 1) * (4 * M) ^ dd
      = M + 4 * ((dd : ℝ) + 1) * 4 ^ dd * M ^ dd := by rw [mul_pow]; ring
    _ ≤ 8 * ((dd : ℝ) + 1) * 4 ^ dd * M * M ^ dd := by
        have e1 : M ≤ 4 * ((dd : ℝ) + 1) * 4 ^ dd * M * M ^ dd := by
          have : (1 : ℝ) ≤ 4 * ((dd : ℝ) + 1) * 4 ^ dd := by nlinarith
          have : M ≤ 4 * ((dd : ℝ) + 1) * 4 ^ dd * M :=
            le_mul_of_one_le_left (by linarith) this
          nlinarith
        have e2 : 4 * ((dd : ℝ) + 1) * 4 ^ dd * M ^ dd ≤
            4 * ((dd : ℝ) + 1) * 4 ^ dd * M * M ^ dd := by
          have := mul_le_mul_of_nonneg_left hM (mul_nonneg hA (by positivity : (0:ℝ) ≤ M ^ dd))
          nlinarith
        nlinarith
    _ ≤ Mb * Mb ^ dd := mul_le_mul h1 h3 (by positivity) (by linarith)
    _ = Mb ^ (dd + 1) := by ring

/-! ## One sample: the labelled value against an admissible single matrix -/

/-- **One sample `ω` and one spectral parameter `z`**: if `G(ω)` and every resampled resolvent
`G(ω^{[y,η]})`, `η` outside `T`, satisfy the bounds of `LabelRemoval_Hyp`,
`M_{4R'}(ω, y)^{1/2} P(T)^{1/2}` is small, and the numerical conditions hold, then the single
matrix `G̃` built from `G(ω)` satisfies the two bounds of [II, Notation 8.8] and
`|Γ_{𝔞,𝔟𝔟}(ω)| ≤ 3^{#labels} C_Γ Σ_S |(Γ'_S)^{abs}_{𝔞,𝔟𝔟}(G̃)|` with `Γ' = Γ.wDLights`. -/
private lemma LabelRemoval_step {d : ℕ} (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2)
    {nI : ℕ} (Γ : Graph 3 nI) (N : ℕ) (hΓ : Γ.TKindsErr N) (W L : ℕ) [NeZero L] (z : ℂ)
    (hzim : 0 < z.im) (hz3 : ‖z‖ ≤ 3) (ε₀ τ' t Cf a Φ : ℝ) (hΦ : 0 ≤ Φ) {sb ρb : ℝ} {Rn : ℕ}
    (hS : LabelRemoval_SCond W (Smat P.ψ W L) ε₀ t 0 sb ρb Rn)
    (hδ8 : t * (W : ℝ) ^ (-((d : ℝ) / 2) + ε₀) ≤ 1 / 8)
    (hδt : 36 * t * (t * (W : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ≤ 1 / 2)
    (hfB : ∀ x y : Zd d L, (W : ℝ) ^ (-Cf) ≤ Real.sqrt (bB d L W x y))
    (hfL : 3 ^ d * (L : ℝ) ^ d * (W : ℝ) ^ (-Cf) ≤ 1)
    (hN1 : (W : ℝ) ^ ((d : ℝ) / 2) * (3 * (5 * (t * (W : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) +
        (W : ℝ) ^ (-Cf))) + 3 * (7000 * Real.sqrt (3 ^ d) * t ^ 3 * ρb + 2) * (W : ℝ) ^ ε₀ ≤
        (W : ℝ) ^ (ε₀ + τ'))
    (hN2 : 1080 * t ^ 2 + 3 ≤ (W : ℝ) ^ τ') (hf3 : 3 * (W : ℝ) ^ (-Cf) ≤ 1)
    (hima : (W : ℝ) ^ (-a) ≤ z.im) (ω : Sample (Zd d L)) (T : Set (Sample (Zd d L)))
    (hTm : MeasurableSet T)
    (hGω : LabelRemoval_Hyp W (Smat P.ψ W L) (msc z) ε₀ t Φ ((W : ℝ) ^ (-Cf))
      (green (hmat ω) z))
    (hGres : ∀ y η, η ∉ T → LabelRemoval_Hyp W (Smat P.ψ W L) (msc z) ε₀ t Φ ((W : ℝ) ^ (-Cf))
      (green (hmat (LabelRemoval_res y η ω)) z))
    (hS1 : ∀ c, coordVar (Smat P.ψ W L) c ≤ 1)
    (hP : ∀ y, Real.sqrt (LabelRemoval.momBound (2 * (2 * Γ.wDLights.comps.length)) ω y) *
      Real.sqrt (gaussLaw (Smat P.ψ W L) T).toReal ≤
        (3 * (W : ℝ) ^ (-Cf) / LabelRemoval_Mb Γ.wDLights.comps.length d L W a) ^
          Γ.wDLights.comps.length) (a₀ b₀ : Zd d L) :
    ∃ Gt : Matrix (Zd d L) (Zd d L) ℂ,
      (weakNorm d L W 1 2 (errAbs Gt z) ≤ (W : ℝ) ^ (ε₀ + τ') ∧
        ∀ x y, ‖entryErr Gt (msc z) x y‖ ≤ (W : ℝ) ^ τ' * (Real.sqrt (bB d L W x y) + Φ)) ∧
      ‖Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a₀, b₀, b₀] ω‖ ≤
        3 ^ Γ.labels.length * (G11.wDConst Γ * ∑ S ∈ Γ.wDLights.pathElig.powerset,
          (Γ.wDLights.pathRepl S).absVal (gData (Smat P.ψ W L) z Sig Gt) ![a₀, b₀, b₀]) := by
  set Sm := Smat P.ψ W L with hSm
  set f := (W : ℝ) ^ (-Cf) with hf
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hS.W1
  have hW0 : (0 : ℝ) < W := by linarith
  have hf0 : 0 ≤ f := Real.rpow_nonneg hW0.le _
  have ht1 := hS.t1
  set q : LabelRemoval_Par := ⟨t, t * (W : ℝ) ^ (-((d : ℝ) / 2) + ε₀), Φ, f⟩ with hq
  have hm4 : 1 / 4 ≤ ‖msc z‖ := norm_msc_ge_quarter z hzim hz3
  have hm1 : ‖msc z‖ ≤ 1 := (norm_msc_lt_one hzim).le
  have hm0 : msc z ≠ 0 := msc_ne_zero z
  have hc : LabelRemoval_Cmp W Sm (msc z) ε₀ q :=
    ⟨hS.nonneg, fun x => (hS.row x).le, rfl, hδ8, by simpa [hq] using hδt, ht1, hΦ, hm4, hm1,
      hfB, hf0⟩
  set Om := LabelRemoval_Om W Sm (green (hmat ω) z) q a₀ b₀ with hOm
  set Gt := LabelRemoval_Gt (msc z) f Om with hGt
  refine ⟨Gt, LabelRemoval_admissible hc hGω hS hm0 hf0 hfB hfL hfL a₀ b₀ τ' hN1 hN2, ?_⟩
  -- the inputs of `LabelRemoval_valR_le`
  have hδ0 : 0 ≤ q.δ₁ := by simp only [hq]; positivity
  have hOm0 : ∀ x y, 0 ≤ Om x y := fun x y => LabelRemoval_Om_nonneg (W := W) (S := Sm)
    (G := green (hmat ω) z) (by linarith) hδ0 hΦ hf0 a₀ b₀ x y
  obtain ⟨g1, g2, g3⟩ := LabelRemoval_Gt_facts hm0 hf0 hOm0
  obtain ⟨hG1, hG2⟩ := LabelRemoval_domG hc hGω hm0 hf0 a₀ b₀
  have h8 : ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
      LabelRemoval_Hyp W Sm (msc z) ε₀ t Φ f G → ∀ x, ‖G x x - msc z‖ ≤ 1 / 8 := by
    intro G hG x
    have := hG.entry x x
    simp only [entryErr, if_true] at this
    linarith
  set M := LabelRemoval_Mres d L W a with hM
  have hLd : (1 : ℝ) ≤ ((L : ℝ) ^ d) ^ 2 := one_le_pow₀ (one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)))
  have hWa : 0 ≤ (W : ℝ) ^ a := Real.rpow_nonneg hW0.le _
  have hM1 : 1 ≤ M := by rw [hM, LabelRemoval_Mres]; nlinarith
  have hima' : z.im⁻¹ ≤ (W : ℝ) ^ a := by
    rw [inv_le_comm₀ hzim (by positivity), ← Real.rpow_neg hW0.le]; exact hima
  have hall : ∀ (ω' : Sample (Zd d L)) (x y : Zd d L), ‖green (hmat ω') z x y‖ ≤ M - 1 := by
    intro ω' x y
    have h1 := norm_green_entry_le (hmat_isHermitian ω') hzim.ne' x y
    rw [abs_of_pos hzim] at h1
    rw [hM, LabelRemoval_Mres]
    nlinarith
  have hinv : ∀ (ω' : Sample (Zd d L)) (x : Zd d L),
      ‖(green (hmat ω') z x x)⁻¹‖ ≤ M * (1 + ‖ω'‖) ^ 2 := by
    intro ω' x
    refine (LabelRemoval_inv_diag_le hzim ω' x).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [card_Zd, hM, LabelRemoval_Mres]
    push_cast
    have : ((L : ℝ) ^ d) ^ 2 * (4 * z.im⁻¹) ≤ ((L : ℝ) ^ d) ^ 2 * (4 * (W : ℝ) ^ a) := by gcongr
    nlinarith
  set R' := Γ.wDLights.comps.length with hR'
  set Mb := LabelRemoval_Mb R' d L W a with hMb
  have hMbM : 8 * ((R' : ℝ) + 1) * 4 ^ R' * M = Mb := rfl
  have hMMb : M ≤ Mb := by
    rw [← hMbM]
    have : (1 : ℝ) ≤ 8 * ((R' : ℝ) + 1) * 4 ^ R' := by
      have := one_le_pow₀ (n := R') (by norm_num : (1 : ℝ) ≤ 4); nlinarith
    exact le_mul_of_one_le_left (by linarith) this
  have hbad : ∀ (σ : Atom 3 nI → Zd d L) (ω' : Sample (Zd d L)) (c : Comp (Atom 3 nI)),
      c ∈ Γ.comps → c.kind.isRandom = true →
      ‖Comp.val (gData Sm z Sig (green (hmat ω') z)) σ c‖ ≤
        Mb ^ (c.kind.wDDeg + 1) * (1 + ‖ω'‖) ^ 2 := by
    intro σ ω' c hc hr
    refine LabelRemoval_val_bad Sm z Sig _ M Mb _ hM1 (one_le_pow₀ (by
      linarith [norm_nonneg ω'])) (hall ω') (hinv ω') hm1 hm4 σ N c
      (LabelRemoval_errKind hΓ hc) hr hMMb fun _ => ?_
    rw [← hMbM]
    refine LabelRemoval_Mb_pow M hM1 R' _ ?_
    rw [hR', G11.wDLights_length]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun c => c.kind.wDDeg) hc)
    omega
  have hlo : ∀ x y, 3 * f ≤ ‖Gt x y‖ := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; rw [g2]; linarith [hOm0 x x, norm_nonneg (msc z)]
    · rw [g3 x y hxy]; linarith [hOm0 x y]
  have hlo2 : ∀ x, 3 * f ≤ ‖Gt x x - msc z‖ := by
    intro x; rw [g1]; linarith [hOm0 x x]
  have hMb0 : 0 < Mb := by linarith
  have hloM : 3 * f ≤ Mb := by linarith
  refine LabelRemoval_valR_le Γ P Sig W L z N hΓ Gt ω T hTm Mb (3 * f) (by positivity) hloM hMb0
    hbad hm1 hm4 hlo hlo2 hG1 hG2 (h8 _ hGω) a₀ b₀ (fun y η hη => ⟨?_, h8 _ (hGres y η hη)⟩)
    hS1 hP
  have hmin : ∀ k l, greenMinor (green (hmat (LabelRemoval_res y η ω)) z) y k l =
      greenMinor (green (hmat ω) z) y k l :=
    fun k l => freeOf_greenMinor z hzim y k l ω η
  exact LabelRemoval_resdom hc hGω (hGres y η hη) y hmin hm0 hf0 a₀ b₀

/-! ## The label removal -/

/-- The removal of the `P`/`Q` labels for the graphs of `Err` ([II, Def 3.2 (8)]: they may carry
weights `W_d` of [II, (4.21)] and `P`/`Q` labels): the hypotheses of the label removal bound of the module description, for a graph
`Γ` with the kinds of `Err` (`Graph.TKindsErr`) and a bound `β` of the label-free graphs `Γ'_S` of
the graph `Γ' = Γ.wDLights`, in which every weight `W_d` is replaced by `d + 1` light weights,
give `|Γ_{𝔞,𝔟𝔟}| ≺ β + W^{−D'}` uniformly in `u`, `𝔞`, `𝔟`. -/
def labelRemovalErrStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → 0 < c₀T →
    ∀ (n : ℕ) (Sig : ℕ → Expansion 2),
      ∀ ε₀ : ℝ, 0 < ε₀ → ((n : ℝ) - 1) * ε₀ < c₀T → ε₀ < (d : ℝ) / 20 →
      ∀ (U : SizeL → Type) (z : ∀ p, U p → ℂ), (∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) →
      StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
        (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
        (fun p v ω => ‖entryErr (green (hmat ω) (z p v.1)) (msc (z p v.1)) v.2.1 v.2.2‖)
        (fun p _ _ => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) →
      StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
        (U := fun p => {v : U p × Zd d p.1.2 × Zd d p.1.2 × ℕ //
          p.1.1 ≤ v.2.2.2 ∧ 2 * v.2.2.2 ≤ p.1.2})
        (fun p v ω => boxAvg d p.1.2 (green (hmat ω) (z p v.1.1)) v.1.2.1 v.1.2.2.1 v.1.2.2.2)
        (fun p v _ => (p.1.1 : ℝ) ^ (2 * ε₀) * (p.1.1 : ℝ) ^ (-4 : ℝ) *
          (v.1.2.2.2 : ℝ) ^ (4 - (d : ℝ))) →
      ∀ (Φ : ∀ p, U p → ℝ) (δ : ℝ), 0 < δ →
        (∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ u, 0 ≤ Φ p u ∧ Φ p u ≤ (p.1.1 : ℝ) ^ (-δ)) →
        StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
          (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
          (fun p v ω => Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) (msc (z p v.1))
            v.2.1 v.2.2)
          (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2 + Φ p v.1 ^ 2) →
        ∀ (N nI : ℕ) (Γ : Graph 3 nI), Γ.TKindsErr N →
        ∀ τ' : ℝ, 0 < τ' → ∀ β : ∀ p : SizeL, U p → Zd d p.1.2 → Zd d p.1.2 → ℝ,
          (∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ (u : U p) (a b : Zd d p.1.2)
              (G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ),
            weakNorm d p.1.2 p.1.1 1 2 (errAbs G (z p u)) ≤ (p.1.1 : ℝ) ^ (ε₀ + τ') →
            (∀ x y, ‖entryErr G (msc (z p u)) x y‖ ≤
              (p.1.1 : ℝ) ^ τ' * (Real.sqrt (bB d p.1.2 p.1.1 x y) + Φ p u)) →
            ∑ S ∈ Γ.wDLights.pathElig.powerset, (Γ.wDLights.pathRepl S).absVal
                (gData (Smat P.ψ p.1.1 p.1.2) (z p u) Sig G) ![a, b, b] ≤ β p u a b) →
          ∀ D' : ℝ, 0 < D' →
            StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
              (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
              (fun p v ω => ‖Γ.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩
                (rbmData d P Sig p.1.1 p.1.2 (z p v.1)) ![v.2.1, v.2.2, v.2.2] ω‖)
              (fun p v _ => β p v.1 v.2.1 v.2.2 + (p.1.1 : ℝ) ^ (-D'))

set_option maxHeartbeats 4000000 in
/-- **The removal of the `P`/`Q` labels for the graphs of `Err`** (the step of the proofs of
[II, Claim 8.6] (8.24) and [II, Claim 8.7] for the labelled graphs, with the weights `W_d` of
[II, (4.21)] under the labels by [II, Lemma 4.15], (4.19), (4.21)): on the joint event of `ω` and
of every resampled `ω^{[y,η]}` (law preservation and a union bound over `y`) every weight `W_d` is
at most `2 |m|^{−(d+2)} |G_{xx} − m|^{d+1}` (`wDMajorant`), which is `d + 1` light weights at the
single matrix `G̃`; off that event the polynomial moments `|G_{xy}| ≤ (Im z)⁻¹` and
`|(G_{xx})⁻¹| ≤ C (1 + ‖ω‖)²` bound the partial expectations
(`LabelRemoval.pexp_norm_le_of_good`), on the event `‖ω‖ ≤ W` of probability `1 − O(W^{−D})`. -/
theorem labelRemovalErr : labelRemovalErrStmt := by
  intro d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T n Sig ε₀ hε₀ hε₀n hε₀d U z hz h77 h78 Φ δ hδ
    hΦ h81 N nI Γ hΓ τ' hτ' β hβ D' hD' τ hτ D hD
  -- constants
  set τ₁ : ℝ := min τ' 1 / 16 with hτ₁
  have hτ₁0 : 0 < τ₁ := by have := lt_min hτ' one_pos; positivity
  have hτ₁τ : τ₁ ≤ τ' / 16 := by have := min_le_left τ' 1; linarith
  have hτ₁1 : τ₁ ≤ 1 / 16 := by have := min_le_right τ' 1; linarith
  set Cf : ℝ := 3 * (d : ℝ) + d / c₁ + 4 with hCf
  set a : ℝ := |2 - ε| / c₁ with ha
  have ha0 : 0 ≤ a := div_nonneg (abs_nonneg _) hc₁.le
  set R := Γ.wDLights.comps.length with hR
  set kL := Γ.labels.length with hkL
  have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hdc : 0 ≤ (d : ℝ) / c₁ := by positivity
  have hCf4 : 4 ≤ Cf := by rw [hCf]; linarith
  set e₁ : ℝ := d / c₁ with he₁
  have he₁0 : 0 ≤ e₁ := by rw [he₁]; positivity
  set Xq : ℝ := 2 * R * (Cf + 2 * e₁ + a + 1) + 4 * R + 2 * e₁ + 1 with hXq
  have hXq0 : 0 ≤ Xq := by rw [hXq]; positivity
  set D₂ : ℝ := D + 4 + e₁ + Xq with hD₂
  have hD₂0 : 0 < D₂ := by rw [hD₂]; positivity
  set pk : ℕ := ⌈D₂ + 2 * e₁ + 1⌉₊ with hpk
  have hpk' : D₂ + 2 * e₁ + 1 ≤ pk := Nat.le_ceil _
  set Gk : ℝ := LabelRemoval.gaussMoment pk with hGk
  set G4 : ℝ := LabelRemoval.gaussMoment (2 * (2 * R)) with hG4
  set ks : ℕ := ⌈(2 * (d : ℝ) / c₁ + 1) / τ₁⌉₊ with hks
  have hksτ : (2 * (d : ℝ) / c₁ + 1) ≤ τ₁ * ks := by
    have := Nat.le_ceil ((2 * (d : ℝ) / c₁ + 1) / τ₁)
    rw [div_le_iff₀ hτ₁0] at this; linarith
  obtain ⟨Cb, hCb0, hband⟩ := LabelRemoval_band (c₁ := c₁) d P hc₀ τ₁ hτ₁0.le ks
  -- the six dominations at the scale `τ₁`
  have hdg := LabelRemoval_diag d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hκ n ε₀ hε₀ hε₀d U z hz h77 Φ δ hδ
    hΦ h81
  have hrw := LabelRemoval_ldeRow d P c₀ c₁ κ ε Cf hc₀ hc₁ hκ U z hz
  have hcl := LabelRemoval_ldeCol d P c₀ c₁ κ ε Cf hc₀ hc₁ hκ U z hz
  have E1 := h77 τ₁ hτ₁0 D₂ hD₂0
  have E2 := h78 τ₁ hτ₁0 D₂ hD₂0
  have E3 := hdg τ₁ hτ₁0 D₂ hD₂0
  have E4 := (hrw τ₁ hτ₁0 D₂ hD₂0).filter_mono (inf_le_left : llFilter d n c₀ c₁ c₀T ≤ _)
  have E5 := (hcl τ₁ hτ₁0 D₂ hD₂0).filter_mono (inf_le_left : llFilter d n c₀ c₁ c₀T ≤ _)
  have E6 := h81 τ₁ hτ₁0 D₂ hD₂0
  -- the numerical conditions
  have hsz := tendsto_sizeW_admFilterL c₀ c₁
  have Nall : ∀ᶠ p in admFilterL c₀ c₁, (p.1 ∈ adm c₀ c₁ ∧ 2 ≤ sizeW p ∧
      Smat P.ψ p.1.1 p.1.2 ∈ doublyStochastic ℝ (Zd d p.1.2)) ∧
      sizeW p ^ (τ₁ + (-((d : ℝ) / 2) + ε₀)) ≤ 1 / 8 ∧
      sizeW p ^ (2 * τ₁ + (-((d : ℝ) / 2) + ε₀)) ≤ 1 / 72 ∧
      sizeW p ^ (-(d : ℝ) - 1) ≤ 1 / (4 * (Cb + 1)) ∧
      1701024 * Real.sqrt (3 ^ d) ≤ sizeW p ^ (τ' - 7 * τ₁) ∧
      1083 ≤ sizeW p ^ (τ' - 2 * τ₁) ∧ (3 : ℝ) ^ kL * G11.wDConst Γ ≤ sizeW p ^ τ ∧
      96 * ((R : ℝ) + 1) * 4 ^ R ≤ sizeW p ^ (1 : ℝ) ∧
      2 ^ (2 * (2 * R)) * (1 + 3 * (1 + G4)) ≤ sizeW p ^ (1 : ℝ) ∧
      3 * Gk ≤ sizeW p ^ (1 : ℝ) := by
    filter_upwards [LabelRemoval_ev d P c₀ c₁ hc₀,
      hsz.eventually (LabelRemoval_ev_small (α := τ₁ + (-((d : ℝ) / 2) + ε₀)) (by linarith)
        (by norm_num : (0 : ℝ) < 1 / 8)),
      hsz.eventually (LabelRemoval_ev_small (α := 2 * τ₁ + (-((d : ℝ) / 2) + ε₀)) (by linarith)
        (by norm_num : (0 : ℝ) < 1 / 72)),
      hsz.eventually (LabelRemoval_ev_small (α := -(d : ℝ) - 1) (by linarith)
        (by positivity : (0 : ℝ) < 1 / (4 * (Cb + 1)))),
      hsz.eventually (LabelRemoval_ev_large (α := τ' - 7 * τ₁) (by linarith)
        (1701024 * Real.sqrt (3 ^ d))),
      hsz.eventually (LabelRemoval_ev_large (α := τ' - 2 * τ₁) (by linarith) 1083),
      hsz.eventually (LabelRemoval_ev_large (α := τ) hτ ((3 : ℝ) ^ kL * G11.wDConst Γ)),
      hsz.eventually (LabelRemoval_ev_large (α := 1) one_pos (96 * ((R : ℝ) + 1) * 4 ^ R)),
      hsz.eventually (LabelRemoval_ev_large (α := 1) one_pos
        (2 ^ (2 * (2 * R)) * (1 + 3 * (1 + G4)))),
      hsz.eventually (LabelRemoval_ev_large (α := 1) one_pos (3 * Gk))] with p h0 h1 h2 h3 h4 h5
        h6 h7 h8 h9
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  filter_upwards [E1, E2, E3, E4, E5, E6, hβ, hΦ,
    Nall.filter_mono (inf_le_left : llFilter d n c₀ c₁ c₀T ≤ _)] with p e1 e2 e3 e4 e5 e6 hβp hΦp
    hN
  obtain ⟨⟨hadm, hW2, hds⟩, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hN
  rw [Real.rpow_one] at n7 n8 n9
  have hW1 : (1 : ℝ) ≤ sizeW p := by linarith
  have hW0 : (0 : ℝ) < sizeW p := by linarith
  have hWn : 1 ≤ p.1.1 := by have : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW1; exact_mod_cast this
  obtain ⟨hWL, hL1c, hLd⟩ := LabelRemoval_L_le hc₀ hc₁ p hadm hW1 d
  have hrwW : ∀ x y : ℝ, sizeW p ^ x * sizeW p ^ y = sizeW p ^ (x + y) :=
    fun x y => (Real.rpow_add hW0 x y).symm
  set S := Smat P.ψ p.1.1 p.1.2 with hS
  set μ := rbmLaw d P p with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw S
  -- the numerical inputs of `LabelRemoval_step`
  have hδ8 : sizeW p ^ τ₁ * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀) ≤ 1 / 8 := by
    change sizeW p ^ τ₁ * sizeW p ^ (-((d : ℝ) / 2) + ε₀) ≤ 1 / 8; rw [hrwW]; exact n1
  have hδt : 36 * sizeW p ^ τ₁ * (sizeW p ^ τ₁ * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ≤ 1 / 2 := by
    change 36 * sizeW p ^ τ₁ * (sizeW p ^ τ₁ * sizeW p ^ (-((d : ℝ) / 2) + ε₀)) ≤ 1 / 2
    rw [hrwW, mul_assoc, hrwW, show τ₁ + (τ₁ + (-((d : ℝ) / 2) + ε₀)) =
      2 * τ₁ + (-((d : ℝ) / 2) + ε₀) by ring]
    linarith
  have hfB := LabelRemoval_num_fB (d := d) (L := p.1.2) (W := p.1.1) (by omega) hc₁ hW2
    (by have : (p.1.1 : ℝ) ≤ (p.1.2 : ℝ) := hWL; exact_mod_cast this) hL1c
  have hfL := LabelRemoval_num_fL (d := d) hW2 (Nat.cast_nonneg p.1.2) hLd
  have hsbL :
      4 * ((p.1.2 : ℝ) ^ d) ^ 2 * (Cb * sizeW p ^ (-(d : ℝ)) / (sizeW p ^ τ₁) ^ ks) ≤ 1 := by
    have hpow : (sizeW p ^ τ₁) ^ ks = sizeW p ^ (τ₁ * ks) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    have hL2 : ((p.1.2 : ℝ) ^ d) ^ 2 ≤ sizeW p ^ (2 * (d : ℝ) / c₁) := by
      calc ((p.1.2 : ℝ) ^ d) ^ 2 ≤ (sizeW p ^ ((d : ℝ) / c₁)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hLd 2
        _ = sizeW p ^ (2 * (d : ℝ) / c₁) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
    have hτk : sizeW p ^ (2 * (d : ℝ) / c₁ + 1) ≤ sizeW p ^ (τ₁ * ks) :=
      Real.rpow_le_rpow_of_exponent_le hW1 hksτ
    have hpos : 0 < sizeW p ^ (τ₁ * ks) := Real.rpow_pos_of_pos hW0 _
    rw [hpow, mul_div_assoc', div_le_iff₀ hpos, one_mul]
    calc 4 * ((p.1.2 : ℝ) ^ d) ^ 2 * (Cb * sizeW p ^ (-(d : ℝ)))
        ≤ 4 * sizeW p ^ (2 * (d : ℝ) / c₁) * (Cb * sizeW p ^ (-(d : ℝ))) := by gcongr
      _ = 4 * Cb * (sizeW p ^ (-(d : ℝ) - 1) * sizeW p ^ (2 * (d : ℝ) / c₁ + 1)) := by
          rw [hrwW (-(d : ℝ) - 1), show -(d : ℝ) - 1 + (2 * (d : ℝ) / c₁ + 1) =
            2 * (d : ℝ) / c₁ + -(d : ℝ) by ring, ← hrwW]; ring
      _ ≤ 4 * Cb * (1 / (4 * (Cb + 1)) * sizeW p ^ (2 * (d : ℝ) / c₁ + 1)) := by gcongr
      _ ≤ sizeW p ^ (τ₁ * ks) := by
          have hX : 0 ≤ sizeW p ^ (2 * (d : ℝ) / c₁ + 1) := by positivity
          have : 4 * Cb * (1 / (4 * (Cb + 1))) ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]; linarith
          nlinarith
  have hSC := LabelRemoval_num_S P hc₀ hε₀ hτ₁0 hCb0 p hadm hW2 hds (hband p hadm hW1) hsbL
  have hN1 := LabelRemoval_num_N1 (c₁ := c₁) hW1 hτ₁0 hd8 hε₀ hc₁ n4
  have hN2 : 1080 * (sizeW p ^ τ₁) ^ 2 + 3 ≤ sizeW p ^ τ' := by
    have h1 : 1083 * sizeW p ^ (2 * τ₁) ≤ sizeW p ^ τ' := by
      have := mul_le_mul_of_nonneg_right n5 (Real.rpow_nonneg hW0.le (2 * τ₁))
      rwa [hrwW, show τ' - 2 * τ₁ + 2 * τ₁ = τ' by ring] at this
    have hsq : (sizeW p ^ τ₁) ^ 2 = sizeW p ^ (2 * τ₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
    have h0 : 1 ≤ sizeW p ^ (2 * τ₁) := Real.one_le_rpow hW1 (by linarith)
    rw [hsq]; linarith
  have hf3 : 3 * sizeW p ^ (-Cf) ≤ 1 := by
    have := LabelRemoval_num_f hW2 hCf4; linarith
  -- the bad samples of the six bounds at the scale `τ₁`
  obtain ⟨B1, hB1⟩ : ∃ B : Set (Sample (Zd d p.1.2)), B = {ω | ∃ u : U p × Zd d p.1.2 × Zd d p.1.2,
      sizeW p ^ τ₁ * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀) <
        ‖entryErr (green (hmat ω) (z p u.1)) (msc (z p u.1)) u.2.1 u.2.2‖} := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B : Set (Sample (Zd d p.1.2)), B = {ω |
      ∃ u : {v : U p × Zd d p.1.2 × Zd d p.1.2 × ℕ // p.1.1 ≤ v.2.2.2 ∧ 2 * v.2.2.2 ≤ p.1.2},
      sizeW p ^ τ₁ * ((p.1.1 : ℝ) ^ (2 * ε₀) * (p.1.1 : ℝ) ^ (-4 : ℝ) *
        (u.1.2.2.2 : ℝ) ^ (4 - (d : ℝ))) <
        boxAvg d p.1.2 (green (hmat ω) (z p u.1.1)) u.1.2.1 u.1.2.2.1 u.1.2.2.2} := ⟨_, rfl⟩
  obtain ⟨B3, hB3⟩ : ∃ B : Set (Sample (Zd d p.1.2)), B = {ω | ∃ u : U p × Zd d p.1.2,
      sizeW p ^ τ₁ * ((p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) + Φ p u.1) <
        ‖green (hmat ω) (z p u.1) u.2 u.2 - msc (z p u.1)‖} := ⟨_, rfl⟩
  obtain ⟨B4, hB4⟩ : ∃ B : Set (Sample (Zd d p.1.2)), B = {ω | ∃ u : U p × Zd d p.1.2 × Zd d p.1.2,
      sizeW p ^ τ₁ * ((‖green (hmat ω) (z p u.1) u.2.1 u.2.1‖ + 1) *
        (Real.sqrt (ldeRowRHS S (green (hmat ω) (z p u.1)) u.2.1 u.2.2) + sizeW p ^ (-Cf))) <
        if u.2.1 = u.2.2 then 0 else ‖green (hmat ω) (z p u.1) u.2.1 u.2.2‖} := ⟨_, rfl⟩
  obtain ⟨B5, hB5⟩ : ∃ B : Set (Sample (Zd d p.1.2)), B = {ω | ∃ u : U p × Zd d p.1.2 × Zd d p.1.2,
      sizeW p ^ τ₁ * ((‖green (hmat ω) (z p u.1) u.2.1 u.2.1‖ + 1) *
        (Real.sqrt (ldeColRHS S (green (hmat ω) (z p u.1)) u.2.1 u.2.2) + sizeW p ^ (-Cf))) <
        if u.2.1 = u.2.2 then 0 else ‖green (hmat ω) (z p u.1) u.2.2 u.2.1‖} := ⟨_, rfl⟩
  obtain ⟨B6, hB6⟩ : ∃ B : Set (Sample (Zd d p.1.2)), B = {ω | ∃ u : U p × Zd d p.1.2 × Zd d p.1.2,
      sizeW p ^ τ₁ * (bB d p.1.2 p.1.1 u.2.1 u.2.2 + Φ p u.1 ^ 2) <
        Tvar S (green (hmat ω) (z p u.1)) (msc (z p u.1)) u.2.1 u.2.2} := ⟨_, rfl⟩
  have e1' : μ B1 ≤ ENNReal.ofReal (sizeW p ^ (-D₂)) := by rw [hB1]; exact e1
  have e2' : μ B2 ≤ ENNReal.ofReal (sizeW p ^ (-D₂)) := by rw [hB2]; exact e2
  have e3' : μ B3 ≤ ENNReal.ofReal (sizeW p ^ (-D₂)) := by rw [hB3]; exact e3
  have e4' : μ B4 ≤ ENNReal.ofReal (sizeW p ^ (-D₂)) := by rw [hB4]; exact e4
  have e5' : μ B5 ≤ ENNReal.ofReal (sizeW p ^ (-D₂)) := by rw [hB5]; exact e5
  have e6' : μ B6 ≤ ENNReal.ofReal (sizeW p ^ (-D₂)) := by rw [hB6]; exact e6
  obtain ⟨Good, hGood⟩ : ∃ Gd : Set (Sample (Zd d p.1.2)),
      Gd = (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6)ᶜ := ⟨_, rfl⟩
  have hHyp : ∀ ω ∈ Good, ∀ u : U p, LabelRemoval_Hyp p.1.1 S (msc (z p u)) ε₀ (sizeW p ^ τ₁)
      (Φ p u) ((p.1.1 : ℝ) ^ (-Cf)) (green (hmat ω) (z p u)) := by
    intro ω hω u
    rw [hGood] at hω
    simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hω
    obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩ := hω
    rw [hB1, Set.mem_ofPred_eq, not_exists] at g1
    rw [hB2, Set.mem_ofPred_eq, not_exists] at g2
    rw [hB3, Set.mem_ofPred_eq, not_exists] at g3
    rw [hB4, Set.mem_ofPred_eq, not_exists] at g4
    rw [hB5, Set.mem_ofPred_eq, not_exists] at g5
    rw [hB6, Set.mem_ofPred_eq, not_exists] at g6
    have f1 : ∀ x y, ‖entryErr (green (hmat ω) (z p u)) (msc (z p u)) x y‖ ≤
        sizeW p ^ τ₁ * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀) := by
      intro x y; have := g1 (u, x, y); simp only at this; exact not_lt.1 this
    have f2 : ∀ (x x₀ : Zd d p.1.2) (K : ℕ), p.1.1 ≤ K → 2 * K ≤ p.1.2 →
        boxAvg d p.1.2 (green (hmat ω) (z p u)) x x₀ K ≤ sizeW p ^ τ₁ * ((p.1.1 : ℝ) ^ (2 * ε₀) *
          (p.1.1 : ℝ) ^ (-4 : ℝ) * (K : ℝ) ^ (4 - (d : ℝ))) := by
      intro x x₀ K h1 h2; have := g2 ⟨(u, x, x₀, K), h1, h2⟩; simp only at this
      exact not_lt.1 this
    have f3 : ∀ x, ‖green (hmat ω) (z p u) x x - msc (z p u)‖ ≤
        sizeW p ^ τ₁ * ((p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) + Φ p u) := by
      intro x; have := g3 (u, x); simp only at this; exact not_lt.1 this
    have f4 : ∀ x y, x ≠ y → ‖green (hmat ω) (z p u) x y‖ ≤ sizeW p ^ τ₁ *
        ((‖green (hmat ω) (z p u) x x‖ + 1) *
          (Real.sqrt (ldeRowRHS S (green (hmat ω) (z p u)) x y) + (p.1.1 : ℝ) ^ (-Cf))) := by
      intro x y hxy
      have := g4 (u, x, y); simp only [if_neg hxy] at this; exact not_lt.1 this
    have f5 : ∀ x y, x ≠ y → ‖green (hmat ω) (z p u) y x‖ ≤ sizeW p ^ τ₁ *
        ((‖green (hmat ω) (z p u) x x‖ + 1) *
          (Real.sqrt (ldeColRHS S (green (hmat ω) (z p u)) x y) + (p.1.1 : ℝ) ^ (-Cf))) := by
      intro x y hxy
      have := g5 (u, x, y); simp only [if_neg hxy] at this; exact not_lt.1 this
    have f6 : ∀ x y, Tvar S (green (hmat ω) (z p u)) (msc (z p u)) x y ≤
        sizeW p ^ τ₁ * (bB d p.1.2 p.1.1 x y + Φ p u ^ 2) := by
      intro x y; have := g6 (u, x, y); simp only at this; exact not_lt.1 this
    exact ⟨f1, f2, f3, f4, f5, f6⟩
  have hGc : μ Goodᶜ ≤ ENNReal.ofReal (6 * sizeW p ^ (-D₂)) := by
    rw [hGood, compl_compl]
    have h0 : 0 ≤ sizeW p ^ (-D₂) := Real.rpow_nonneg hW0.le _
    have hA : ENNReal.ofReal (6 * sizeW p ^ (-D₂)) =
        ENNReal.ofReal (sizeW p ^ (-D₂)) + ENNReal.ofReal (sizeW p ^ (-D₂)) +
          ENNReal.ofReal (sizeW p ^ (-D₂)) + ENNReal.ofReal (sizeW p ^ (-D₂)) +
          ENNReal.ofReal (sizeW p ^ (-D₂)) + ENNReal.ofReal (sizeW p ^ (-D₂)) := by
      rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0,
        ← ENNReal.ofReal_add (by positivity) h0, ← ENNReal.ofReal_add (by positivity) h0,
        ← ENNReal.ofReal_add (by positivity) h0]
      congr 1; ring
    rw [hA]
    refine (measure_union_le _ _).trans (add_le_add ?_ e6')
    refine (measure_union_le _ _).trans (add_le_add ?_ e5')
    refine (measure_union_le _ _).trans (add_le_add ?_ e4')
    refine (measure_union_le _ _).trans (add_le_add ?_ e3')
    exact (measure_union_le _ _).trans (add_le_add e1' e2')
  -- the resampled samples outside `Good` and Markov's inequality in `η`
  obtain ⟨Bp, hBp⟩ : ∃ B : Set (Sample (Zd d p.1.2) × Sample (Zd d p.1.2)),
      B = {q | ∃ y, LabelRemoval_res y q.2 q.1 ∉ Good} := ⟨_, rfl⟩
  have hBpμ : μ.prod μ Bp ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ d * (6 * sizeW p ^ (-D₂))) := by
    rw [hBp]
    refine (LabelRemoval_prod_bad S Good).trans ?_
    rw [card_Zd, ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (le_of_eq ?_) hGc
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  -- the constants off the event
  have hS1 : ∀ c, coordVar S c ≤ 1 := LabelRemoval_coordVar_le S hds
  set Wr : ℝ := (p.1.1 : ℝ) with hWr
  have hWr1 : (1 : ℝ) ≤ Wr := hW1
  have hWr0 : (0 : ℝ) < Wr := hW0
  have hsW : sizeW p = Wr := rfl
  rw [hsW] at hGc hBpμ
  have hrw' : ∀ x y : ℝ, Wr ^ x * Wr ^ y = Wr ^ (x + y) :=
    fun x y => (Real.rpow_add hWr0 x y).symm
  set Lw : ℝ := (p.1.2 : ℝ) ^ d with hLw
  have hLw1 : (1 : ℝ) ≤ Lw := one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2)
  have hLwe : Lw ≤ Wr ^ e₁ := hLd
  set Kc : ℝ := (Fintype.card (Coord (Zd d p.1.2)) : ℝ) with hKc
  have hKc3 : Kc ≤ 3 * Lw ^ 2 := by
    have := LabelRemoval_card_coord (ι := Zd d p.1.2)
    rwa [card_Zd, Nat.cast_pow] at this
  set Mb := LabelRemoval_Mb R d p.1.2 Wr a with hMb
  set lo : ℝ := 3 * Wr ^ (-Cf) with hlo
  set Mw : ℝ := (1 + Wr) ^ (2 * (2 * R)) + 2 ^ (2 * (2 * R)) * (1 + G4) * Kc with hMw
  have hG40 : 0 ≤ G4 := integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hGk0 : 0 ≤ Gk := integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hWa1 : 1 ≤ Wr ^ a := Real.one_le_rpow hWr1 ha0
  have hMb0 : 0 < Mb := by
    rw [hMb, LabelRemoval_Mb, LabelRemoval_Mres]; positivity
  have hMw0 : 0 < Mw := by rw [hMw]; positivity
  have hlo0 : 0 < lo := by rw [hlo]; positivity
  -- `M_b ≤ W^{2 e₁ + a + 1}`
  have hMbW : Mb ≤ Wr ^ (2 * e₁ + a + 1) := by
    have hL2 : Lw ^ 2 ≤ Wr ^ (2 * e₁) := by
      calc Lw ^ 2 ≤ (Wr ^ e₁) ^ 2 := pow_le_pow_left₀ (by linarith) hLwe 2
        _ = Wr ^ (2 * e₁) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hWr0.le]; ring_nf
    rw [hMb, LabelRemoval_Mb, LabelRemoval_Mres]
    calc 8 * ((R : ℝ) + 1) * 4 ^ R * (6 * Lw ^ 2 * (Wr ^ a + 1))
        ≤ 8 * ((R : ℝ) + 1) * 4 ^ R * (6 * Wr ^ (2 * e₁) * (2 * Wr ^ a)) := by
          gcongr; linarith
      _ = 96 * ((R : ℝ) + 1) * 4 ^ R * (Wr ^ (2 * e₁) * Wr ^ a) := by ring
      _ ≤ Wr * (Wr ^ (2 * e₁) * Wr ^ a) := mul_le_mul_of_nonneg_right n7 (by positivity)
      _ = Wr ^ (2 * e₁ + a + 1) := by
          rw [hrw', show Wr ^ (2 * e₁ + a + 1) = Wr ^ (2 * e₁ + a) * Wr ^ (1 : ℝ) by
            rw [hrw'], Real.rpow_one]; ring
  -- `lo / M_b ≥ W^{−(C_f + 2 e₁ + a + 1)}`
  have hqlow : Wr ^ (-(Cf + 2 * e₁ + a + 1)) ≤ lo / Mb := by
    rw [le_div_iff₀ hMb0]
    calc Wr ^ (-(Cf + 2 * e₁ + a + 1)) * Mb ≤ Wr ^ (-(Cf + 2 * e₁ + a + 1)) *
          Wr ^ (2 * e₁ + a + 1) := mul_le_mul_of_nonneg_left hMbW (by positivity)
      _ = Wr ^ (-Cf) := by rw [hrw']; ring_nf
      _ ≤ lo := by rw [hlo]; have : 0 ≤ Wr ^ (-Cf) := by positivity
                   linarith
  -- `M_w ≤ W^{4R + 2 e₁ + 1}`
  have hMwW : Mw ≤ Wr ^ ((4 * R : ℝ) + 2 * e₁ + 1) := by
    have h1 : (1 + Wr) ^ (2 * (2 * R)) ≤ 2 ^ (2 * (2 * R)) * Wr ^ ((4 * R : ℝ) + 2 * e₁) := by
      calc (1 + Wr) ^ (2 * (2 * R)) ≤ (2 * Wr) ^ (2 * (2 * R)) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 2 ^ (2 * (2 * R)) * Wr ^ ((4 * R : ℝ)) := by
            rw [mul_pow, ← Real.rpow_natCast Wr]; push_cast; ring_nf
        _ ≤ 2 ^ (2 * (2 * R)) * Wr ^ ((4 * R : ℝ) + 2 * e₁) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hWr1 (by linarith))
              (by positivity)
    have h2 : Kc ≤ 3 * Wr ^ ((4 * R : ℝ) + 2 * e₁) := by
      have hL2 : Lw ^ 2 ≤ Wr ^ (2 * e₁) := by
        calc Lw ^ 2 ≤ (Wr ^ e₁) ^ 2 := pow_le_pow_left₀ (by linarith) hLwe 2
          _ = Wr ^ (2 * e₁) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hWr0.le]; ring_nf
      have : Wr ^ (2 * e₁) ≤ Wr ^ ((4 * R : ℝ) + 2 * e₁) :=
        Real.rpow_le_rpow_of_exponent_le hWr1 (by have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
                                                  linarith)
      linarith
    have hX : 0 ≤ Wr ^ ((4 * R : ℝ) + 2 * e₁) := by positivity
    calc Mw ≤ 2 ^ (2 * (2 * R)) * Wr ^ ((4 * R : ℝ) + 2 * e₁) +
          2 ^ (2 * (2 * R)) * (1 + G4) * (3 * Wr ^ ((4 * R : ℝ) + 2 * e₁)) := by
          rw [hMw]; gcongr
      _ = 2 ^ (2 * (2 * R)) * (1 + 3 * (1 + G4)) * Wr ^ ((4 * R : ℝ) + 2 * e₁) := by ring
      _ ≤ Wr * Wr ^ ((4 * R : ℝ) + 2 * e₁) := mul_le_mul_of_nonneg_right n8 hX
      _ = Wr ^ ((4 * R : ℝ) + 2 * e₁ + 1) := by
          rw [show Wr ^ ((4 * R : ℝ) + 2 * e₁ + 1) = Wr ^ ((4 * R : ℝ) + 2 * e₁) * Wr ^ (1 : ℝ)
            by rw [hrw'], Real.rpow_one]; ring
  -- the threshold `q₀ = (lo / M_b)^{2R} / M_w ≥ W^{−X_q}`
  set q₀ : ℝ := (lo / Mb) ^ (2 * R) / Mw with hq₀
  have hq₀0 : 0 < q₀ := by rw [hq₀]; positivity
  have hq₀ge : Wr ^ (-Xq) ≤ q₀ := by
    rw [hq₀, le_div_iff₀ hMw0]
    have e1 : Wr ^ (-(Cf + 2 * e₁ + a + 1) * (2 * R : ℝ)) =
        (Wr ^ (-(Cf + 2 * e₁ + a + 1))) ^ (2 * R) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWr0.le]; push_cast; ring_nf
    calc Wr ^ (-Xq) * Mw ≤ Wr ^ (-Xq) * Wr ^ ((4 * R : ℝ) + 2 * e₁ + 1) :=
          mul_le_mul_of_nonneg_left hMwW (by positivity)
      _ = Wr ^ (-(Cf + 2 * e₁ + a + 1) * (2 * R : ℝ)) := by rw [hrw', hXq]; ring_nf
      _ = (Wr ^ (-(Cf + 2 * e₁ + a + 1))) ^ (2 * R) := e1
      _ ≤ (lo / Mb) ^ (2 * R) := pow_le_pow_left₀ (by positivity) hqlow _
  -- the resampled samples outside `Good` and Markov's inequality in `η`
  set hull := toMeasurable (μ.prod μ) Bp with hhull
  have hMB := LabelRemoval_markov μ μ Bp (ENNReal.ofReal q₀)
    (by simpa using hq₀0) ENNReal.ofReal_ne_top
  obtain ⟨MB, hMBd⟩ : ∃ M : Set (Sample (Zd d p.1.2)),
      M = {ω | ENNReal.ofReal q₀ ≤ μ (Prod.mk ω ⁻¹' hull)} := ⟨_, rfl⟩
  rw [← hMBd] at hMB
  -- the samples of large norm
  obtain ⟨B7, hB7⟩ : ∃ B : Set (Sample (Zd d p.1.2)), B = {ω | Wr < ‖ω‖} := ⟨_, rfl⟩
  -- the target set is in `Goodᶜ ∪ B7 ∪ MB`
  have hincl : {ω | ∃ v : U p × Zd d p.1.2 × Zd d p.1.2,
      sizeW p ^ τ * (β p v.1 v.2.1 v.2.2 + (p.1.1 : ℝ) ^ (-D')) <
        ‖Γ.valR ⟨Pexp S⟩ (rbmData d P Sig p.1.1 p.1.2 (z p v.1)) ![v.2.1, v.2.2, v.2.2] ω‖} ⊆
      Goodᶜ ∪ B7 ∪ MB := by
    rintro ω ⟨⟨u, a₀, b₀⟩, hv⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨⟨hωG, hω7⟩, hωM⟩ := hcon
    rw [hMBd, Set.mem_ofPred_eq, not_le] at hωM
    rw [hB7, Set.mem_ofPred_eq, not_lt] at hω7
    set T := Prod.mk ω ⁻¹' hull with hT
    have hTm : MeasurableSet T := measurable_prodMk_left (measurableSet_toMeasurable _ _)
    have hGres : ∀ y η, η ∉ T → LabelRemoval_Hyp p.1.1 S (msc (z p u)) ε₀ (sizeW p ^ τ₁)
        (Φ p u) ((p.1.1 : ℝ) ^ (-Cf)) (green (hmat (LabelRemoval_res y η ω)) (z p u)) := by
      intro y η hη
      have h1 : (ω, η) ∉ Bp := fun h => hη (subset_toMeasurable _ _ h)
      rw [hBp, Set.mem_ofPred_eq, not_exists] at h1
      exact hHyp _ (not_not.1 (h1 y)) u
    have hPT : (gaussLaw S T).toReal ≤ q₀ :=
      ENNReal.toReal_le_of_le_ofReal hq₀0.le hωM.le
    have hP' : ∀ y, Real.sqrt (LabelRemoval.momBound (2 * (2 * R)) ω y) *
        Real.sqrt (gaussLaw S T).toReal ≤ (lo / Mb) ^ R := by
      intro y
      have hmb : LabelRemoval.momBound (2 * (2 * R)) ω y ≤ Mw := by
        rw [LabelRemoval.momBound, hMw]
        gcongr
        rw [hKc]
        exact_mod_cast Finset.card_le_univ (rowCoords y)
      rw [← Real.sqrt_mul (by unfold LabelRemoval.momBound; positivity)]
      calc Real.sqrt (LabelRemoval.momBound (2 * (2 * R)) ω y * (gaussLaw S T).toReal)
          ≤ Real.sqrt (Mw * q₀) := Real.sqrt_le_sqrt (mul_le_mul hmb hPT
            ENNReal.toReal_nonneg hMw0.le)
        _ = (lo / Mb) ^ R := by
            rw [hq₀, mul_div_cancel₀ _ hMw0.ne', pow_mul', Real.sqrt_sq (by positivity)]
    have hzu := hz p u
    have hima := LabelRemoval_im_ge hc₁ p hadm hW1 (z p u) hzu
    have hzim : 0 < (z p u).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hima
    have hz3 : ‖z p u‖ ≤ 3 := by
      have h1 := hzu.1; have h2 := hzu.2.2
      have := Complex.norm_le_abs_re_add_abs_im (z p u)
      rw [abs_of_pos hzim] at this
      linarith [abs_nonneg (z p u).re]
    obtain ⟨Gt, ⟨hw, he⟩, hval⟩ := LabelRemoval_step hd P Sig Γ N hΓ p.1.1 p.1.2 (z p u) hzim hz3
      ε₀ τ' (sizeW p ^ τ₁) Cf a (Φ p u) (hΦp u).1 hSC hδ8 hδt hfB hfL hN1 hN2 hf3 hima ω T hTm
      (hHyp ω hωG u) hGres hS1 hP' a₀ b₀
    have hβ' := hβp u a₀ b₀ Gt hw he
    have hsum0 : 0 ≤ ∑ S' ∈ Γ.wDLights.pathElig.powerset, (Γ.wDLights.pathRepl S').absVal
        (gData S (z p u) Sig Gt) ![a₀, b₀, b₀] :=
      Finset.sum_nonneg fun S' _ => Finset.sum_nonneg fun s _ =>
        mul_nonneg (norm_nonneg _) (List.prod_nonneg fun x hx => by
          obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _)
    have hβ0 : 0 ≤ β p u a₀ b₀ := hsum0.trans hβ'
    have h3 : (0 : ℝ) ≤ 3 ^ kL * G11.wDConst Γ :=
      mul_nonneg (by positivity) (zero_le_one.trans (G11.one_le_wDConst Γ))
    have hfin : ‖Γ.valR ⟨Pexp S⟩ (rbmData d P Sig p.1.1 p.1.2 (z p u)) ![a₀, b₀, b₀] ω‖ ≤
        sizeW p ^ τ * (β p u a₀ b₀ + (p.1.1 : ℝ) ^ (-D')) := by
      calc _ ≤ 3 ^ kL * (G11.wDConst Γ * ∑ S' ∈ Γ.wDLights.pathElig.powerset,
            (Γ.wDLights.pathRepl S').absVal (gData S (z p u) Sig Gt) ![a₀, b₀, b₀]) := hval
        _ = 3 ^ kL * G11.wDConst Γ * ∑ S' ∈ Γ.wDLights.pathElig.powerset,
            (Γ.wDLights.pathRepl S').absVal (gData S (z p u) Sig Gt) ![a₀, b₀, b₀] := by ring
        _ ≤ 3 ^ kL * G11.wDConst Γ * β p u a₀ b₀ := mul_le_mul_of_nonneg_left hβ' h3
        _ ≤ sizeW p ^ τ * β p u a₀ b₀ := mul_le_mul_of_nonneg_right n6 hβ0
        _ ≤ sizeW p ^ τ * (β p u a₀ b₀ + (p.1.1 : ℝ) ^ (-D')) := by
            have : 0 ≤ (p.1.1 : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
            have : 0 ≤ sizeW p ^ τ := Real.rpow_nonneg hW0.le _
            nlinarith
    exact absurd hv (not_lt.2 hfin)
  refine (measure_mono hincl).trans (((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl)).trans ?_)
  -- the arithmetic
  have hD4 : Wr ^ (-D - 4) ≤ Wr ^ (-D) / 16 := by
    rw [show -D - 4 = -D + -4 by ring, ← hrw', div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (LabelRemoval_num_f hW2 (le_refl (4 : ℝ)))
      (Real.rpow_nonneg hW0.le _)
  have hD₂4 : Wr ^ (-D₂) ≤ Wr ^ (-D - 4) := Real.rpow_le_rpow_of_exponent_le hWr1 (by
    rw [hD₂]; linarith)
  have hMB' : μ MB ≤ ENNReal.ofReal (6 * Wr ^ (-D - 4)) := by
    refine hMB.trans ((ENNReal.div_le_div_right hBpμ _).trans ?_)
    rw [← ENNReal.ofReal_div_of_pos hq₀0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hq₀0]
    have h1 : Lw * (6 * Wr ^ (-D₂)) ≤ 6 * (Wr ^ e₁ * Wr ^ (-D₂)) := by
      have := mul_le_mul_of_nonneg_right hLwe (by positivity : (0 : ℝ) ≤ 6 * Wr ^ (-D₂))
      linarith
    have h2 : Wr ^ e₁ * Wr ^ (-D₂) = Wr ^ (-D - 4) * Wr ^ (-Xq) := by
      rw [hrw', hrw', hD₂]; ring_nf
    have h3 : Wr ^ (-D - 4) * Wr ^ (-Xq) ≤ Wr ^ (-D - 4) * q₀ :=
      mul_le_mul_of_nonneg_left hq₀ge (by positivity)
    change Lw * (6 * Wr ^ (-D₂)) ≤ 6 * Wr ^ (-D - 4) * q₀
    calc Lw * (6 * Wr ^ (-D₂)) ≤ 6 * (Wr ^ e₁ * Wr ^ (-D₂)) := h1
      _ = 6 * (Wr ^ (-D - 4) * Wr ^ (-Xq)) := by rw [h2]
      _ ≤ 6 * (Wr ^ (-D - 4) * q₀) := by linarith [h3]
      _ = 6 * Wr ^ (-D - 4) * q₀ := by ring
  have hB7' : μ B7 ≤ ENNReal.ofReal (Wr ^ (-D₂)) := by
    rw [← ofReal_measureReal (μ := μ) (s := B7)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hB7]
    refine (LabelRemoval_norm_tail S hS1 Wr hWr0 pk).trans ?_
    have hpkW : Wr ^ (pk : ℝ) = Wr ^ pk := Real.rpow_natCast _ _
    have hWpk : 0 < Wr ^ pk := pow_pos hWr0 pk
    rw [div_le_iff₀ hWpk, ← hpkW]
    have hL2 : Kc ≤ 3 * Wr ^ (2 * e₁) := by
      have : Lw ^ 2 ≤ Wr ^ (2 * e₁) := by
        calc Lw ^ 2 ≤ (Wr ^ e₁) ^ 2 := pow_le_pow_left₀ (by linarith) hLwe 2
          _ = Wr ^ (2 * e₁) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hWr0.le]; ring_nf
      linarith
    calc Kc * Gk ≤ 3 * Wr ^ (2 * e₁) * Gk := mul_le_mul_of_nonneg_right hL2 hGk0
      _ = Wr ^ (2 * e₁) * (3 * Gk) := by ring
      _ ≤ Wr ^ (2 * e₁) * Wr := mul_le_mul_of_nonneg_left n9 (by positivity)
      _ = Wr ^ (2 * e₁ + 1) := by
          rw [show Wr ^ (2 * e₁ + 1) = Wr ^ (2 * e₁) * Wr ^ (1 : ℝ) by rw [hrw'],
            Real.rpow_one]
      _ ≤ Wr ^ (-D₂ + pk) := Real.rpow_le_rpow_of_exponent_le hWr1 (by linarith)
      _ = Wr ^ (-D₂) * Wr ^ (pk : ℝ) := by rw [hrw']
  have hGc' : μ Goodᶜ ≤ ENNReal.ofReal (6 * Wr ^ (-D - 4)) :=
    hGc.trans (ENNReal.ofReal_le_ofReal (by linarith))
  refine (add_le_add (add_le_add hGc' hB7') hMB').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  change 6 * Wr ^ (-D - 4) + Wr ^ (-D₂) + 6 * Wr ^ (-D - 4) ≤ Wr ^ (-D)
  have h0 : 0 ≤ Wr ^ (-D) := by positivity
  linarith

end RBM8D
