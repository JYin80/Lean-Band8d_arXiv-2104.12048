import RBM8D.LocalLaw.Defs
import RBM8D.LocalLaw.LabelRemoval
import RBM8D.Kernel.ThetaDecay
import RBM8D.Kernel.Propagator
import RBM8D.Profile.Decay
import RBM8D.Profile.Symbol
import RBM8D.Profile.Density
import RBM8D.Input.EntryDiag
import RBM8D.Prob.Union
import RBM8D.Prob.Net
import RBM8D.Bound.Doubly

/-!
# The local law at `η = 1`

`eta1Step_of : eta1Step_ofStmt`: [II, Lemma 7.2] = [I, Lemma 5.2], `|G_{xy}(E + i) − δ_{xy} m(E + i)|²
≺ B_{xy}` uniformly in `|E| < 2 − κ` and `x, y`, along `W → ∞` inside `adm(c₀, c₁)`.

* The second order `T`-expansion `secondOrderT` ([I, Lemma 2.5], [II, (3.8)–(3.10)]) at
  `e = (a, b, b)` on the Gaussian model writes `T_{ab}` as `m Θ_{ab} Ḡ_{bb}`, the two graphs of
  `A^{(>2)}` and the four graphs of `Q^{(2)}`, the last with the partial expectations `P_x` of
  [I, §1.4] read as integrals over a resampled row and column.
* The high moment bound [II, (8.26)–(8.28)] for `T_{ab}`: the leading term and the graphs of `A`
  are bounded by `‖G − m‖_max ≺ W^{−d/2}` (the bound [II, (8.51)] at `η = 1`), `|G_{xy}|² ≺ T_{xy}`
  ([I, (5.2)]) and the decay of `Θ` ([I, (1.17)]); the graphs of `Q` by the self-adjointness of
  `P_x` and the change of `T_{ab}` under the resampling of the row and column `x` (the Schur
  complement identity for the resolvent minor), whose resampled sample has the law of the sample.
  The moment recursion is closed in the largest normalised moment `max_{x,y} E (T_{xy}/B_{xy})^q`,
  without an induction in `Φ̃`.
* The Markov inequality, the union bound over a finite net in `E`, and the Lipschitz continuity of
  `|G_{xy} − δ_{xy} m|²` in `z`.

The statement takes the doubly connected bound `dcWeakDomStmt` ([I, (6.40)]) as a hypothesis;
the proof uses only the bounds above, so that this hypothesis is not read.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open MeasureTheory Filter Complex Topology

namespace RBM8D

open Graphs

section Resample

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sample `ω` with the coordinates of row and column `x` replaced by those of `η`. -/
private def eta1Rs (x : ι) (ω η : Sample ι) : Sample ι := (rowCoords x).piecewise η ω

private lemma eta1Rs_meas_pair (x : ι) :
    Measurable fun p : Sample ι × Sample ι => eta1Rs x p.1 p.2 := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ rowCoords x
  · simp only [eta1Rs, Finset.piecewise_eq_of_mem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_snd
  · simp only [eta1Rs, Finset.piecewise_eq_of_notMem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_fst

private lemma eta1Rs_meas_right (x : ι) (ω : Sample ι) :
    Measurable fun η : Sample ι => eta1Rs x ω η :=
  (eta1Rs_meas_pair x).comp measurable_prodMk_left

private lemma eta1Rs_mp (S : Matrix ι ι ℝ) (x : ι) :
    MeasurePreserving (fun p : Sample ι × Sample ι => eta1Rs x p.1 p.2)
      ((gaussLaw S).prod (gaussLaw S)) (gaussLaw S) :=
  LabelRemoval.measurePreserving_piecewise S (rowCoords x)

omit [DecidableEq ι] in
private lemma eta1_integrable_bdd (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : BddMeas F) :
    Integrable F (gaussLaw S) := by
  classical
  have := isProbabilityMeasure_gaussLaw S
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- `∫ X (F - P_x F) = ∫ (X - P_x X) F` for bounded measurable `X`, `F`. -/
private theorem eta1_E_mul_Q (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ x y, 0 ≤ S x y) (x : ι)
    {X F : Sample ι → ℂ} (hX : BddMeas X) (hF : BddMeas F) :
    ∫ ω, X ω * (F ω - Pexp S x F ω) ∂(gaussLaw S) =
      ∫ ω, (X ω - Pexp S x X ω) * F ω ∂(gaussLaw S) := by
  have := isProbabilityMeasure_gaussLaw S
  have hl := pqLaws_Pexp S hS hnn
  have hPX : BddMeas (Pexp S x X) := hl.adm_P x X hX
  have hPF : BddMeas (Pexp S x F) := hl.adm_P x F hF
  have iXF : Integrable (X * F) (gaussLaw S) := eta1_integrable_bdd S (hl.adm_mul X F hX hF)
  have iXPF : Integrable (X * Pexp S x F) (gaussLaw S) :=
    eta1_integrable_bdd S (hl.adm_mul X _ hX hPF)
  have iPXF : Integrable (Pexp S x X * F) (gaussLaw S) :=
    eta1_integrable_bdd S (hl.adm_mul _ F hPX hF)
  -- `∫ X · P_x F = ∫ P_x X · P_x F`
  have e1 : ∫ ω, (X * Pexp S x F) ω ∂(gaussLaw S) =
      ∫ ω, (Pexp S x F * Pexp S x X) ω ∂(gaussLaw S) := by
    have h1 := hl.E_P x (X * Pexp S x F) (hl.adm_mul X _ hX hPF)
    have h2 : Pexp S x (X * Pexp S x F) = Pexp S x F * Pexp S x X := by
      rw [mul_comm X (Pexp S x F)]
      exact hl.P_mul_free x X (Pexp S x F) (hl.free_P x F)
    rw [← h1, h2]
  have e2 : ∫ ω, (Pexp S x X * F) ω ∂(gaussLaw S) =
      ∫ ω, (Pexp S x X * Pexp S x F) ω ∂(gaussLaw S) := by
    have h1 := hl.E_P x (Pexp S x X * F) (hl.adm_mul _ F hPX hF)
    have h2 : Pexp S x (Pexp S x X * F) = Pexp S x X * Pexp S x F :=
      hl.P_mul_free x F (Pexp S x X) (hl.free_P x X)
    rw [← h1, h2]
  have lhs : ∫ ω, X ω * (F ω - Pexp S x F ω) ∂(gaussLaw S) =
      ∫ ω, (X * F) ω ∂(gaussLaw S) - ∫ ω, (X * Pexp S x F) ω ∂(gaussLaw S) := by
    rw [← integral_sub iXF iXPF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [mul_sub]
  have rhs : ∫ ω, (X ω - Pexp S x X ω) * F ω ∂(gaussLaw S) =
      ∫ ω, (X * F) ω ∂(gaussLaw S) - ∫ ω, (Pexp S x X * F) ω ∂(gaussLaw S) := by
    rw [← integral_sub iXF iPXF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [sub_mul]
  rw [lhs, rhs, e1, e2]
  congr 2
  funext ω
  simp [mul_comm]

/-- The partial expectation is an integral over the resampled row. -/
private theorem eta1_Pexp_eq (S : Matrix ι ι ℝ) (x : ι) (F : Sample ι → ℂ) (ω : Sample ι) :
    Pexp S x F ω = ∫ η, F (eta1Rs x ω η) ∂(gaussLaw S) := rfl

/-- `‖X - P_x X‖ ≤ ∫ ‖X ω - X ω^{[x,η]}‖ dη`. -/
private theorem eta1_norm_Q_le (S : Matrix ι ι ℝ) (x : ι) {X : Sample ι → ℂ} (hX : BddMeas X)
    (ω : Sample ι) :
    ‖X ω - Pexp S x X ω‖ ≤ ∫ η, ‖X ω - X (eta1Rs x ω η)‖ ∂(gaussLaw S) := by
  have := isProbabilityMeasure_gaussLaw S
  obtain ⟨hm, C, hC⟩ := hX
  have hint : Integrable (fun η => X (eta1Rs x ω η)) (gaussLaw S) :=
    Integrable.of_bound (hm.comp (eta1Rs_meas_right x ω)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun η => hC _)
  have h : X ω - Pexp S x X ω = ∫ η, (X ω - X (eta1Rs x ω η)) ∂(gaussLaw S) := by
    rw [integral_sub (integrable_const _) hint, integral_const]
    simp [eta1_Pexp_eq]
  rw [h]
  exact norm_integral_le_integral_norm _

omit [DecidableEq ι] in
private lemma eta1_bdd_prod_integrable (S : Matrix ι ι ℝ) {a : Sample ι × Sample ι → ℝ}
    (hm : Measurable a) (C : ℝ) (hC : ∀ p, |a p| ≤ C) :
    Integrable a ((gaussLaw S).prod (gaussLaw S)) := by
  classical
  have := isProbabilityMeasure_gaussLaw S
  exact Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hC p)

/-- `|∫ X (F - P_x F)| ≤ ∫∫ ‖X ω - X ω^{[x,η]}‖ ‖F ω‖`. -/
private theorem eta1_E_mul_Q_le (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ x y, 0 ≤ S x y) (x : ι)
    {X F : Sample ι → ℂ} (hX : BddMeas X) (hF : BddMeas F) :
    ‖∫ ω, X ω * (F ω - Pexp S x F ω) ∂(gaussLaw S)‖ ≤
      ∫ p, ‖X p.1 - X (eta1Rs x p.1 p.2)‖ * ‖F p.1‖ ∂((gaussLaw S).prod (gaussLaw S)) := by
  have := isProbabilityMeasure_gaussLaw S
  have hl := pqLaws_Pexp S hS hnn
  obtain ⟨hXm, CX, hCX⟩ := hX
  obtain ⟨hFm, CF, hCF⟩ := hF
  have hX' : BddMeas X := ⟨hXm, CX, hCX⟩
  have hF' : BddMeas F := ⟨hFm, CF, hCF⟩
  have hPX := hl.adm_P x X hX'
  rw [eta1_E_mul_Q S hS hnn x hX' hF']
  set a : Sample ι × Sample ι → ℝ := fun p => ‖X p.1 - X (eta1Rs x p.1 p.2)‖ * ‖F p.1‖ with ha
  have ham : Measurable a := by
    refine Measurable.mul ?_ ?_
    · exact (hXm.comp measurable_fst |>.sub (hXm.comp (eta1Rs_meas_pair x))).norm
    · exact (hFm.comp measurable_fst).norm
  have hCa : ∀ p, |a p| ≤ (CX + CX) * CF := by
    intro p
    have h1 : ‖X p.1 - X (eta1Rs x p.1 p.2)‖ ≤ CX + CX :=
      (norm_sub_le _ _).trans (add_le_add (hCX _) (hCX _))
    have h0 : 0 ≤ ‖F p.1‖ := norm_nonneg _
    rw [ha]
    simp only
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) h0)]
    exact mul_le_mul h1 (hCF _) h0 ((norm_nonneg _).trans h1)
  have hai := eta1_bdd_prod_integrable S ham _ hCa
  have hgi : Integrable (fun ω => ∫ η, a (ω, η) ∂(gaussLaw S)) (gaussLaw S) := hai.integral_prod_left
  calc ‖∫ ω, (X ω - Pexp S x X ω) * F ω ∂(gaussLaw S)‖
      ≤ ∫ ω, ‖(X ω - Pexp S x X ω) * F ω‖ ∂(gaussLaw S) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ∫ η, a (ω, η) ∂(gaussLaw S) ∂(gaussLaw S) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hgi
          (Filter.Eventually.of_forall fun ω => ?_)
        simp only
        rw [norm_mul]
        have h1 := eta1_norm_Q_le S x hX' ω
        have h2 : ∫ η, a (ω, η) ∂(gaussLaw S) =
            (∫ η, ‖X ω - X (eta1Rs x ω η)‖ ∂(gaussLaw S)) * ‖F ω‖ := by
          rw [ha]
          simp only
          exact integral_mul_const _ _
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ∫ p, a p ∂((gaussLaw S).prod (gaussLaw S)) := (integral_prod a hai).symm

/-- `|∫ X (F - P_x F)| ≤ ∫∫ ‖X ω‖ ‖F ω - F ω^{[x,η]}‖`. -/
private theorem eta1_E_mul_Q_le' (S : Matrix ι ι ℝ) (x : ι)
    {X F : Sample ι → ℂ} (hX : BddMeas X) (hF : BddMeas F) :
    ‖∫ ω, X ω * (F ω - Pexp S x F ω) ∂(gaussLaw S)‖ ≤
      ∫ p, ‖X p.1‖ * ‖F p.1 - F (eta1Rs x p.1 p.2)‖ ∂((gaussLaw S).prod (gaussLaw S)) := by
  have := isProbabilityMeasure_gaussLaw S
  obtain ⟨hXm, CX, hCX⟩ := hX
  obtain ⟨hFm, CF, hCF⟩ := hF
  have hF' : BddMeas F := ⟨hFm, CF, hCF⟩
  set a : Sample ι × Sample ι → ℝ := fun p => ‖X p.1‖ * ‖F p.1 - F (eta1Rs x p.1 p.2)‖ with ha
  have ham : Measurable a := by
    refine Measurable.mul ?_ ?_
    · exact (hXm.comp measurable_fst).norm
    · exact (hFm.comp measurable_fst |>.sub (hFm.comp (eta1Rs_meas_pair x))).norm
  have hCa : ∀ p, |a p| ≤ CX * (CF + CF) := by
    intro p
    have h1 : ‖F p.1 - F (eta1Rs x p.1 p.2)‖ ≤ CF + CF :=
      (norm_sub_le _ _).trans (add_le_add (hCF _) (hCF _))
    have h0 : 0 ≤ ‖X p.1‖ := norm_nonneg _
    rw [ha]
    simp only
    rw [abs_of_nonneg (mul_nonneg h0 (norm_nonneg _))]
    exact mul_le_mul (hCX p.1) h1 (norm_nonneg _) ((norm_nonneg _).trans (hCX p.1))
  have hai := eta1_bdd_prod_integrable S ham _ hCa
  have hgi : Integrable (fun ω => ∫ η, a (ω, η) ∂(gaussLaw S)) (gaussLaw S) := hai.integral_prod_left
  calc ‖∫ ω, X ω * (F ω - Pexp S x F ω) ∂(gaussLaw S)‖
      ≤ ∫ ω, ‖X ω * (F ω - Pexp S x F ω)‖ ∂(gaussLaw S) := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ∫ η, a (ω, η) ∂(gaussLaw S) ∂(gaussLaw S) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hgi
          (Filter.Eventually.of_forall fun ω => ?_)
        simp only
        rw [norm_mul]
        have h1 := eta1_norm_Q_le S x hF' ω
        have h2 : ∫ η, a (ω, η) ∂(gaussLaw S) =
            ‖X ω‖ * ∫ η, ‖F ω - F (eta1Rs x ω η)‖ ∂(gaussLaw S) := by
          rw [ha]
          simp only
          exact integral_const_mul _ _
        rw [h2]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ∫ p, a p ∂((gaussLaw S).prod (gaussLaw S)) := (integral_prod a hai).symm

/-- Law preservation: `∫ g(ω^{[x,η]}) = ∫ g`. -/
private theorem eta1_integral_rs (S : Matrix ι ι ℝ) (x : ι) {g : Sample ι → ℝ} (hg : Measurable g) :
    ∫ p, g (eta1Rs x p.1 p.2) ∂((gaussLaw S).prod (gaussLaw S)) = ∫ ω, g ω ∂(gaussLaw S) := by
  have hmp := eta1Rs_mp S x
  have h := integral_map (μ := (gaussLaw S).prod (gaussLaw S)) hmp.measurable.aemeasurable
    (f := g) hg.aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

/-- Law preservation for events. -/
private theorem eta1_measure_rs (S : Matrix ι ι ℝ) (x : ι) {A : Set (Sample ι)} (hA : MeasurableSet A) :
    ((gaussLaw S).prod (gaussLaw S)) ((fun p : Sample ι × Sample ι => eta1Rs x p.1 p.2) ⁻¹' A) =
      gaussLaw S A :=
  (eta1Rs_mp S x).measure_preimage hA.nullMeasurableSet

end Resample


section Perturb

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `θ_a(G, v) = (Σ_α s_{aα} |G_{αv}|²)^{1/2}`. -/
private def eta1Th (S : Matrix ι ι ℝ) (a : ι) (G : Matrix ι ι ℂ) (v : ι) : ℝ :=
  Real.sqrt (∑ α, S a α * ‖G α v‖ ^ 2)

private lemma eta1Th_nonneg (S : Matrix ι ι ℝ) (a : ι) (G : Matrix ι ι ℂ) (v : ι) : 0 ≤ eta1Th S a G v :=
  Real.sqrt_nonneg _

/-- Cauchy–Schwarz with the weights `s_{aα}`. -/
private lemma eta1_cs (S : Matrix ι ι ℝ) (hnn : ∀ x y, 0 ≤ S x y) (a : ι) (p q : ι → ℝ) :
    ∑ α, S a α * (p α * q α) ≤
      Real.sqrt (∑ α, S a α * p α ^ 2) * Real.sqrt (∑ α, S a α * q α ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun α => Real.sqrt (S a α) * p α) (fun α => Real.sqrt (S a α) * q α)
  have e1 : ∀ α, Real.sqrt (S a α) * p α * (Real.sqrt (S a α) * q α) = S a α * (p α * q α) := by
    intro α
    have := Real.mul_self_sqrt (hnn a α)
    calc _ = (Real.sqrt (S a α) * Real.sqrt (S a α)) * (p α * q α) := by ring
      _ = _ := by rw [this]
  have e2 : ∀ (r : ι → ℝ) α, (Real.sqrt (S a α) * r α) ^ 2 = S a α * r α ^ 2 := by
    intro r α
    rw [mul_pow, Real.sq_sqrt (hnn a α)]
  simp only [e1, e2] at h
  exact h

/-- The change of `T_{ab}` under the replacement of the row and column `x`. -/
private theorem eta1_dT (S : Matrix ι ι ℝ) (hnn : ∀ x y, 0 ≤ S x y) (G G' : Matrix ι ι ℂ) (m : ℂ)
    (hm : (1 : ℝ) / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (δ : ℝ) (hδ : δ ≤ 1 / 20)
    (hG : ∀ k l, ‖entryErr G m k l‖ ≤ δ) (hG' : ∀ k l, ‖entryErr G' m k l‖ ≤ δ)
    (a b x : ι) (hxb : x ≠ b)
    (hschur : ∀ α, α ≠ x →
      G α b - G α x * G x b / G x x = G' α b - G' α x * G' x b / G' x x) :
    |Tvar S G m a b - Tvar S G' m a b| ≤
      5 * ((‖G x b‖ * eta1Th S a G x + ‖G' x b‖ * eta1Th S a G' x) *
          (eta1Th S a G b + eta1Th S a G' b)) +
        S a x * (‖G x b‖ ^ 2 + ‖G' x b‖ ^ 2) := by
  -- diagonal entries are bounded below
  have hd1 : ∀ k, (1 : ℝ) / 5 ≤ ‖G k k‖ := by
    intro k
    have h1 := hG k k
    simp only [entryErr, ite_true] at h1
    have h2 : ‖m‖ - ‖G k k‖ ≤ ‖G k k - m‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    linarith
  have hd1' : ∀ k, (1 : ℝ) / 5 ≤ ‖G' k k‖ := by
    intro k
    have h1 := hG' k k
    simp only [entryErr, ite_true] at h1
    have h2 : ‖m‖ - ‖G' k k‖ ≤ ‖G' k k - m‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    linarith
  set u : ι → ℝ := fun α => ‖G α b‖ with hu
  set u' : ι → ℝ := fun α => ‖G' α b‖ with hu'
  set p : ι → ℝ := fun α => ‖G α x‖ with hp
  set p' : ι → ℝ := fun α => ‖G' α x‖ with hp'
  have hnorm0 : 0 ≤ ‖G x b‖ := norm_nonneg _
  have hnorm0' : 0 ≤ ‖G' x b‖ := norm_nonneg _
  -- the pointwise bound for each `α`
  have hpt : ∀ α, S a α * |u α ^ 2 - u' α ^ 2| ≤
      (if α = x then S a x * (u x ^ 2 + u' x ^ 2) else 0) +
        5 * (‖G x b‖ * (S a α * (p α * (u α + u' α))) +
          ‖G' x b‖ * (S a α * (p' α * (u α + u' α)))) := by
    intro α
    have hs0 := hnn a α
    have hup : 0 ≤ u α := norm_nonneg _
    have hup' : 0 ≤ u' α := norm_nonneg _
    have hnn5 : 0 ≤ 5 * (‖G x b‖ * (S a α * (p α * (u α + u' α))) +
          ‖G' x b‖ * (S a α * (p' α * (u α + u' α)))) := by
      have : 0 ≤ p α := norm_nonneg _
      have : 0 ≤ p' α := norm_nonneg _
      positivity
    by_cases hαx : α = x
    · subst hαx
      rw [ite_eq_left rfl]
      have : |u α ^ 2 - u' α ^ 2| ≤ u α ^ 2 + u' α ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u α), sq_nonneg (u' α)]
      have := mul_le_mul_of_nonneg_left this hs0
      linarith
    · rw [ite_eq_right hαx, zero_add]
      have hsch := hschur α hαx
      have hdiff : G α b - G' α b = G α x * G x b / G x x - G' α x * G' x b / G' x x := by
        linear_combination hsch
      have hbd : ‖G α b - G' α b‖ ≤ 5 * (p α * ‖G x b‖ + p' α * ‖G' x b‖) := by
        rw [hdiff]
        refine (norm_sub_le _ _).trans ?_
        have e1 : ‖G α x * G x b / G x x‖ ≤ 5 * (p α * ‖G x b‖) := by
          rw [norm_div, norm_mul, div_le_iff₀ (by linarith [hd1 x])]
          have := hd1 x
          have h0 : 0 ≤ ‖G α x‖ * ‖G x b‖ := by positivity
          nlinarith
        have e2 : ‖G' α x * G' x b / G' x x‖ ≤ 5 * (p' α * ‖G' x b‖) := by
          rw [norm_div, norm_mul, div_le_iff₀ (by linarith [hd1' x])]
          have := hd1' x
          have h0 : 0 ≤ ‖G' α x‖ * ‖G' x b‖ := by positivity
          nlinarith
        linarith
      have h2 : |u α ^ 2 - u' α ^ 2| ≤ ‖G α b - G' α b‖ * (u α + u' α) := by
        have : u α ^ 2 - u' α ^ 2 = (u α - u' α) * (u α + u' α) := by ring
        rw [this, abs_mul, abs_of_nonneg (by linarith : 0 ≤ u α + u' α)]
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact abs_norm_sub_norm_le _ _
      have h3 : |u α ^ 2 - u' α ^ 2| ≤ 5 * (p α * ‖G x b‖ + p' α * ‖G' x b‖) * (u α + u' α) :=
        h2.trans (mul_le_mul_of_nonneg_right hbd (by linarith))
      have := mul_le_mul_of_nonneg_left h3 hs0
      refine this.trans (le_of_eq ?_)
      ring
  -- sum
  have hsum : ∑ α, S a α * |u α ^ 2 - u' α ^ 2| ≤
      S a x * (u x ^ 2 + u' x ^ 2) +
        5 * (‖G x b‖ * ∑ α, S a α * (p α * (u α + u' α)) +
          ‖G' x b‖ * ∑ α, S a α * (p' α * (u α + u' α))) := by
    refine (Finset.sum_le_sum fun α _ => hpt α).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ x, ite_eq_left (Finset.mem_univ x),
      ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Cauchy–Schwarz
  have hcs1 : ∑ α, S a α * (p α * (u α + u' α)) ≤
      eta1Th S a G x * (eta1Th S a G b + eta1Th S a G' b) := by
    have e : ∀ α, S a α * (p α * (u α + u' α)) =
        S a α * (p α * u α) + S a α * (p α * u' α) := fun α => by ring
    simp only [e, Finset.sum_add_distrib]
    have h1 := eta1_cs S hnn a p u
    have h2 := eta1_cs S hnn a p u'
    unfold eta1Th
    simp only [hp, hu, hu'] at h1 h2 ⊢
    nlinarith [h1, h2]
  have hcs2 : ∑ α, S a α * (p' α * (u α + u' α)) ≤
      eta1Th S a G' x * (eta1Th S a G b + eta1Th S a G' b) := by
    have e : ∀ α, S a α * (p' α * (u α + u' α)) =
        S a α * (p' α * u α) + S a α * (p' α * u' α) := fun α => by ring
    simp only [e, Finset.sum_add_distrib]
    have h1 := eta1_cs S hnn a p' u
    have h2 := eta1_cs S hnn a p' u'
    unfold eta1Th
    simp only [hp', hu, hu'] at h1 h2 ⊢
    nlinarith [h1, h2]
  -- the difference of `T`
  have hT : |Tvar S G m a b - Tvar S G' m a b| ≤ ∑ α, S a α * |u α ^ 2 - u' α ^ 2| := by
    have hm2 : ‖m‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg m]
    have e : Tvar S G m a b - Tvar S G' m a b =
        ‖m‖ ^ 2 * ∑ α, S a α * (u α ^ 2 - u' α ^ 2) := by
      unfold Tvar
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [hu, hu']
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖m‖ ^ 2)]
    have h1 : |∑ α, S a α * (u α ^ 2 - u' α ^ 2)| ≤ ∑ α, S a α * |u α ^ 2 - u' α ^ 2| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [abs_mul, abs_of_nonneg (hnn a α)]
    have h0 : 0 ≤ ∑ α, S a α * |u α ^ 2 - u' α ^ 2| :=
      Finset.sum_nonneg fun α _ => mul_nonneg (hnn a α) (abs_nonneg _)
    calc ‖m‖ ^ 2 * |∑ α, S a α * (u α ^ 2 - u' α ^ 2)|
        ≤ 1 * ∑ α, S a α * |u α ^ 2 - u' α ^ 2| :=
          mul_le_mul hm2 h1 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine hT.trans (hsum.trans ?_)
  have := mul_le_mul_of_nonneg_left hcs1 hnorm0
  have := mul_le_mul_of_nonneg_left hcs2 hnorm0'
  simp only [hu, hu']
  nlinarith

end Perturb



section Identity

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Green function at the sample `ω`. -/
private abbrev eG (z : ℂ) (ω : Sample ι) : Matrix ι ι ℂ := green (hmat ω) z

/-- `T_{ab}` at the sample `ω`. -/
private def eT (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (ω : Sample ι) : ℝ :=
  Tvar S (eG z ω) (msc z) a b

private def eF1 (z : ℂ) (b x : ι) : Sample ι → ℂ := fun ω => eG z ω x b * star (eG z ω x b)
private def eF2 (z : ℂ) (b : ι) : Sample ι → ℂ := fun ω => star (eG z ω b b)
private def eF3 (z : ℂ) (b x y : ι) : Sample ι → ℂ :=
  fun ω => (eG z ω y y - msc z) * (eG z ω x b * star (eG z ω x b))
private def eF4 (z : ℂ) (b x y : ι) : Sample ι → ℂ :=
  fun ω => star (eG z ω x x) * (eG z ω y b * star (eG z ω y b))

private lemma Gm_empty' (S : Matrix ι ι ℝ) (z : ℂ) (ω : Sample ι) :
    (modelData S z hmat ω).Gm ∅ = green (hmat ω) z := by
  have h : ¬ ∃ x : ι, (∅ : Finset ι) = {x} := by
    rintro ⟨x, hx⟩
    exact Finset.singleton_ne_empty x hx.symm
  simp only [modelData, dite_eq_right h]

private lemma sum_fin_two_fun'' (f : (Fin 2 → ι) → ℂ) :
    ∑ s, f s = ∑ a, ∑ b, f ![a, b] := by
  rw [← (piFinTwoEquiv fun _ => ι).symm.sum_comp, Fintype.sum_prod_type]
  rfl

private lemma sum_fin_one_fun'' (f : (Fin 1 → ι) → ℂ) :
    ∑ s, f s = ∑ a, f ![a] := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun s => ?_
  congr 1
  funext i
  fin_cases i
  rfl

private lemma eta1_map_ringInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) :
    (Ring.inverse B).map ((↑) : ℝ → ℂ) = Ring.inverse (B.map ((↑) : ℝ → ℂ)) := by
  let f : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  change f (Ring.inverse B) = Ring.inverse (f B)
  by_cases h : IsUnit B
  · obtain ⟨u, rfl⟩ := h
    have : f (u : Matrix ι ι ℝ) = ((Units.map f.toMonoidHom u : (Matrix ι ι ℂ)ˣ) :
        Matrix ι ι ℂ) := rfl
    rw [this, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have h' : ¬ IsUnit (f B) := by
      rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
      have e : (f B).det = Complex.ofRealHom B.det := (RingHom.map_det _ _).symm
      rw [e]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0; apply hu; rw [h0, map_zero]
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]

private lemma eta1_theta_eq (S : Matrix ι ι ℝ) (z : ℂ) (H : Sample ι → Matrix ι ι ℂ)
    (ω : Sample ι) : (modelData S z H ω).Theta = cmat (Theta (msc z) S) := by
  simp only [modelData, cmat, Theta]
  rw [Matrix.nonsing_inv_eq_ringInverse]
  have e1 : ((‖msc z‖ ^ 2 • S) * Ring.inverse (1 - ‖msc z‖ ^ 2 • S)).map ((↑) : ℝ → ℂ) =
      (‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) *
        (Ring.inverse (1 - ‖msc z‖ ^ 2 • S)).map ((↑) : ℝ → ℂ) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [e1, eta1_map_ringInverse]
  have e2 : (‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) =
      ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ) := by
    ext i j; simp
  have e3 : (1 - ‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) =
      1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ) := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [e2, e3]

/-- **[I, Lemma 2.5]** at `e = (a, b, b)`, on the Gaussian model, written with the partial
expectations. -/
private theorem eta1_identity (S : Matrix ι ι ℝ) (z : ℂ) (hS : S.IsSymm) (hnn : ∀ x y, 0 ≤ S x y)
    (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) (a b : ι) (ω : Sample ι) :
    ((eT S z a b ω : ℝ) : ℂ) =
      msc z * ((Theta (msc z) S a b : ℝ) : ℂ) * star (eG z ω b b) +
      ∑ x, ∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * ((S x y : ℂ) *
          ((eG z ω y y - msc z) * (eG z ω x b * star (eG z ω x b))))) +
      ∑ x, ∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * ((S x y : ℂ) *
          ((star (eG z ω x x) - star (msc z)) * (eG z ω y b * star (eG z ω y b))))) +
      (∑ x, ((Theta (msc z) S a x : ℝ) : ℂ) * (eF1 z b x ω - Pexp S x (eF1 z b x) ω) +
        (-(msc z * ((Theta (msc z) S a b : ℝ) : ℂ) * (eF2 z b ω - Pexp S b (eF2 z b) ω)) +
          (-∑ x, ∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * (S x y : ℂ)) *
              (eF3 z b x y ω - Pexp S x (eF3 z b x y) ω) +
            -∑ x, ∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * (S x y : ℂ)) *
              (eF4 z b x y ω - Pexp S x (eF4 z b x y) ω)))) := by
  obtain ⟨A⟩ := modelAdm_gauss ι S z hS hnn hrow hz
  have h := secondOrderT (Sample ι) ι ⟨Pexp S⟩ (modelData S z hmat) ⟨A⟩ ![a, b, b]
  have h2 := congrFun h ω
  simp [Expansion.valR, Graph.valR, Graph.termR, Graph.labels, secondOrderExp, tGraph, mkC,
    labelQs, Comp.labelQ, Comp.val, Coeff.eval, cm, cmb, Charge.apply, Data.chain,
    sum_fin_two_fun'', sum_fin_one_fun'', Kind.isRandom, CVar.eval, Gm_empty', PFamily.op] at h2
  have hθ : ∀ x y, (modelData S z hmat ω).Theta x y = ((Theta (msc z) S x y : ℝ) : ℂ) := by
    intro x y
    rw [eta1_theta_eq]
    rfl
  have hm : (modelData S z hmat ω).m = msc z := rfl
  have hS' : ∀ x y, (modelData S z hmat ω).S x y = (S x y : ℂ) := fun x y => rfl
  have hm' : ∀ ω', (modelData S z hmat ω').m = msc z := fun ω' => rfl
  simp only [hθ, hm, hm', hS'] at h2
  have hT : ((eT S z a b ω : ℝ) : ℂ) =
      ∑ x, msc z * (starRingEnd ℂ) (msc z) * (↑(S a x) * (green (hmat ω) z x b *
        (starRingEnd ℂ) (green (hmat ω) z x b))) := by
    unfold eT Tvar
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hT]
  unfold eF1 eF2 eF3 eF4
  simp only [eG, Complex.star_def]
  linear_combination (-1 : ℂ) * h2

end Identity



section Meas

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private lemma eta1_testFn_sum {α : Type*} (s : Finset α) (f : α → Sample ι → ℂ)
    (hf : ∀ a ∈ s, TestFn (f a)) : TestFn (fun ω => ∑ a ∈ s, f a ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using testFn_closed.1 (0 : ℂ)
  | insert a s ha ih =>
    have h := testFn_closed.2.1 _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
    convert h using 1
    funext ω
    simp [Finset.sum_insert ha]

private lemma eta1_testFn_pow (F : Sample ι → ℂ) (hF : TestFn F) (k : ℕ) :
    TestFn (fun ω => F ω ^ k) := by
  induction k with
  | zero => simpa using testFn_closed.1 (1 : ℂ)
  | succ k ih =>
    have h := testFn_closed.2.2.1 _ _ ih hF
    convert h using 1
    funext ω
    simp [pow_succ]

private lemma eta1_testFn_mul {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G) :
    TestFn (fun ω => F ω * G ω) := testFn_closed.2.2.1 _ _ hF hG

private lemma eta1_testFn_add {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G) :
    TestFn (fun ω => F ω + G ω) := testFn_closed.2.1 _ _ hF hG

private lemma eta1_testFn_star {F : Sample ι → ℂ} (hF : TestFn F) :
    TestFn (fun ω => star (F ω)) := testFn_closed.2.2.2.1 _ hF

private lemma eta1_testFn_const (c : ℂ) : TestFn (fun _ : Sample ι => c) := testFn_closed.1 c

private lemma eta1_testFn_sub {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G) :
    TestFn (fun ω => F ω - G ω) := by
  have h := eta1_testFn_add hF (eta1_testFn_mul (eta1_testFn_const (-1 : ℂ)) hG)
  convert h using 1
  funext ω
  ring

private theorem eta1_eG_test (z : ℂ) (hz : 0 < z.im) (k l : ι) :
    TestFn (fun ω : Sample ι => eG z ω k l) := testFn_green z hz.ne' k l

private theorem eta1_eT_test (S : Matrix ι ι ℝ) (z : ℂ) (hz : 0 < z.im) (a b : ι) :
    TestFn (fun ω : Sample ι => ((eT S z a b ω : ℝ) : ℂ)) := by
  have h : ∀ ω : Sample ι, ((eT S z a b ω : ℝ) : ℂ) =
      ((‖msc z‖ ^ 2 : ℝ) : ℂ) * ∑ α, (S a α : ℂ) * (eG z ω α b * star (eG z ω α b)) := by
    intro ω
    unfold eT Tvar
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hα : ∀ α ∈ (Finset.univ : Finset ι), TestFn (fun ω : Sample ι =>
      (S a α : ℂ) * (eG z ω α b * star (eG z ω α b))) := fun α _ =>
    eta1_testFn_mul (eta1_testFn_const _)
      (eta1_testFn_mul (eta1_eG_test z hz α b) (eta1_testFn_star (eta1_eG_test z hz α b)))
  have h2 := eta1_testFn_mul (eta1_testFn_const (((‖msc z‖ ^ 2 : ℝ)) : ℂ))
    (eta1_testFn_sum Finset.univ _ hα)
  convert h2 using 1
  funext ω
  exact h ω

private theorem eta1_eF1_test (z : ℂ) (hz : 0 < z.im) (b x : ι) : TestFn (eF1 z b x) :=
  eta1_testFn_mul (eta1_eG_test z hz x b) (eta1_testFn_star (eta1_eG_test z hz x b))

private theorem eta1_eF2_test (z : ℂ) (hz : 0 < z.im) (b : ι) : TestFn (eF2 z b) :=
  eta1_testFn_star (eta1_eG_test z hz b b)

private theorem eta1_eF3_test (z : ℂ) (hz : 0 < z.im) (b x y : ι) : TestFn (eF3 z b x y) :=
  eta1_testFn_mul (eta1_testFn_sub (eta1_eG_test z hz y y) (eta1_testFn_const _))
    (eta1_testFn_mul (eta1_eG_test z hz x b) (eta1_testFn_star (eta1_eG_test z hz x b)))

private theorem eta1_eF4_test (z : ℂ) (hz : 0 < z.im) (b x y : ι) : TestFn (eF4 z b x y) :=
  eta1_testFn_mul (eta1_testFn_star (eta1_eG_test z hz x x))
    (eta1_testFn_mul (eta1_eG_test z hz y b) (eta1_testFn_star (eta1_eG_test z hz y b)))

/-- A test function is bounded and measurable. -/
private theorem eta1_bdd_of_test {F : Sample ι → ℂ} (hF : TestFn F) : BddMeas F :=
  testFn_closed.2.2.2.2.2 F hF

end Meas



section Pieces

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The leading term `m Θ_{ab} Ḡ_{bb}`. -/
private def eLead (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (ω : Sample ι) : ℂ :=
  msc z * ((Theta (msc z) S a b : ℝ) : ℂ) * star (eG z ω b b)

/-- The first graph of `A`. -/
private def eA1 (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (ω : Sample ι) : ℂ :=
  ∑ x, ∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * ((S x y : ℂ) *
    ((eG z ω y y - msc z) * (eG z ω x b * star (eG z ω x b)))))

/-- The second graph of `A`. -/
private def eA2 (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (ω : Sample ι) : ℂ :=
  ∑ x, ∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * ((S x y : ℂ) *
    ((star (eG z ω x x) - star (msc z)) * (eG z ω y b * star (eG z ω y b)))))

/-- The `Q`-graphs. -/
private def eV (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (ω : Sample ι) : ℂ :=
  ∑ x, ((Theta (msc z) S a x : ℝ) : ℂ) * (eF1 z b x ω - Pexp S x (eF1 z b x) ω) +
        (-(msc z * ((Theta (msc z) S a b : ℝ) : ℂ) * (eF2 z b ω - Pexp S b (eF2 z b) ω)) +
          (-∑ x, ∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * (S x y : ℂ)) *
              (eF3 z b x y ω - Pexp S x (eF3 z b x y) ω) +
            -∑ x, ∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * (S x y : ℂ)) *
              (eF4 z b x y ω - Pexp S x (eF4 z b x y) ω)))

private theorem eta1_identity' (S : Matrix ι ι ℝ) (z : ℂ) (hS : S.IsSymm) (hnn : ∀ x y, 0 ≤ S x y)
    (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) (a b : ι) (ω : Sample ι) :
    ((eT S z a b ω : ℝ) : ℂ) = eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω + eV S z a b ω :=
  eta1_identity S z hS hnn hrow hz a b ω

/-! ## The hypotheses of the moment bound -/

/-- The data of the moment bound at one spectral parameter: the variance matrix, the kernel `B`,
the good event `Gd` and the numerical parameters. -/
private structure Eta1Hyp (S : Matrix ι ι ℝ) (z : ℂ) (B : ι → ι → ℝ) (δ w δs κ₁ κ₂ ε : ℝ)
    (Gd : Set (Sample ι)) : Prop where
  hS : S.IsSymm
  hnn : ∀ x y, 0 ≤ S x y
  hrow : ∀ x, ∑ y, S x y = 1
  hz : z.im = 1
  hm0 : (1 : ℝ) / 4 ≤ ‖msc z‖
  hδ0 : 0 ≤ δ
  hδ : δ ≤ 1 / 20
  hw : 1 ≤ w
  hδs0 : 0 ≤ δs
  hSle : ∀ x y, S x y ≤ δs
  hκ1 : 0 ≤ κ₁
  hκ2 : 0 ≤ κ₂
  hε0 : 0 ≤ ε
  hB : ∀ a b, 0 < B a b
  hΘ0 : ∀ a x, 0 ≤ Theta (msc z) S a x
  hΘ1 : ∀ a, ∑ x, Theta (msc z) S a x ≤ 1
  hΘ2 : ∀ a b, Theta (msc z) S a b ≤ κ₁ * B a b
  hΘ3 : ∀ a b, ∑ x, Theta (msc z) S a x * (B x b / B a b) ^ 2 ≤ κ₂
  hGdm : MeasurableSet Gd
  hGd1 : ∀ ω ∈ Gd, ∀ k l, ‖entryErr (eG z ω) (msc z) k l‖ ≤ δ
  hGd2 : ∀ ω ∈ Gd, ∀ k l, k ≠ l → ‖eG z ω k l‖ ^ 2 ≤ w * eT S z k l ω
  hGd3 : gaussLaw S Gdᶜ ≤ ENNReal.ofReal ε

variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

private theorem Eta1Hyp.hz0 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) : 0 < z.im := by
  rw [h.hz]; exact one_pos

private theorem Eta1Hyp.hm1 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) : ‖msc z‖ ≤ 1 :=
  (norm_msc_lt_one h.hz0).le

private theorem Eta1Hyp.G1 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (k l : ι) :
    ‖eG z ω k l‖ ≤ 1 := by
  have := norm_green_entry_le (hmat_isHermitian ω) h.hz0.ne' k l
  rw [h.hz] at this
  simpa using this

private theorem Eta1Hyp.T0 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (a b : ι) :
    0 ≤ eT S z a b ω :=
  mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun α _ => mul_nonneg (h.hnn a α) (sq_nonneg _))

private theorem Eta1Hyp.T1 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (a b : ι) :
    eT S z a b ω ≤ 1 := by
  unfold eT Tvar
  have h0 : 0 ≤ ∑ α, S a α * ‖eG z ω α b‖ ^ 2 :=
    Finset.sum_nonneg fun α _ => mul_nonneg (h.hnn a α) (sq_nonneg _)
  have h1 : ∑ α, S a α * ‖eG z ω α b‖ ^ 2 ≤ ∑ α, S a α * 1 :=
    Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left
      (by have := h.G1 ω α b; nlinarith [norm_nonneg (eG z ω α b)]) (h.hnn a α)
  rw [← Finset.sum_mul, h.hrow a, one_mul] at h1
  have h2 : ‖msc z‖ ^ 2 ≤ 1 := by
    have := norm_nonneg (msc z); have := h.hm1; nlinarith
  calc ‖msc z‖ ^ 2 * ∑ α, S a α * ‖eG z ω α b‖ ^ 2 ≤ 1 * 1 :=
        mul_le_mul h2 h1 h0 zero_le_one
    _ = 1 := one_mul _

/-- `Σ_y s_{xy} |G_{yb}|² = T_{xb} / |m|²`. -/
private theorem Eta1Hyp.sumsG2 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (x b : ι) :
    ∑ y, S x y * ‖eG z ω y b‖ ^ 2 = eT S z x b ω / ‖msc z‖ ^ 2 := by
  have hm : 0 < ‖msc z‖ ^ 2 := by
    have : (0 : ℝ) < ‖msc z‖ := lt_of_lt_of_le (by norm_num) h.hm0
    positivity
  unfold eT Tvar
  rw [eq_div_iff hm.ne']
  ring

/-- On the good event, `Σ_α s_{aα} |G_{αv}|² ≤ δ_s + δ²`. -/
private theorem Eta1Hyp.theta_sq (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) {ω : Sample ι} (hω : ω ∈ Gd)
    (a v : ι) : ∑ α, S a α * ‖eG z ω α v‖ ^ 2 ≤ δs + δ ^ 2 := by
  have hpt : ∀ α, S a α * ‖eG z ω α v‖ ^ 2 ≤
      S a α * δ ^ 2 + (if α = v then S a v else 0) := by
    intro α
    by_cases hα : α = v
    · subst hα
      rw [ite_eq_left rfl]
      have := mul_le_mul_of_nonneg_left (show ‖eG z ω α α‖ ^ 2 ≤ 1 by
        have := h.G1 ω α α; nlinarith [norm_nonneg (eG z ω α α)]) (h.hnn a α)
      nlinarith [mul_nonneg (h.hnn a α) (sq_nonneg δ)]
    · rw [ite_eq_right hα, add_zero]
      have h1 : ‖eG z ω α v‖ ≤ δ := by
        have := h.hGd1 ω hω α v
        simpa [entryErr, hα] using this
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (h.hnn a α)
  calc ∑ α, S a α * ‖eG z ω α v‖ ^ 2
      ≤ ∑ α, (S a α * δ ^ 2 + (if α = v then S a v else 0)) := Finset.sum_le_sum fun α _ => hpt α
    _ = δ ^ 2 + S a v := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v, ite_eq_left (Finset.mem_univ v),
          ← Finset.sum_mul, h.hrow a, one_mul]
    _ ≤ δs + δ ^ 2 := by linarith [h.hSle a v]

private theorem Eta1Hyp.eta1Th_sq (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (a v : ι) :
    eta1Th S a (eG z ω) v ^ 2 = ∑ α, S a α * ‖eG z ω α v‖ ^ 2 := by
  unfold eta1Th
  exact Real.sq_sqrt (Finset.sum_nonneg fun α _ => mul_nonneg (h.hnn a α) (sq_nonneg _))

end Pieces



section Apieces

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

/-- `Σ_x Θ_{ax} T_{xb}`. -/
private def eY (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (ω : Sample ι) : ℝ :=
  ∑ x, Theta (msc z) S a x * eT S z x b ω

private theorem Eta1Hyp.Y0 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (a b : ι) :
    0 ≤ eY S z a b ω :=
  Finset.sum_nonneg fun x _ => mul_nonneg (h.hΘ0 a x) (h.T0 ω x b)

private theorem Eta1Hyp.lead_le (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (a b : ι) :
    ‖eLead S z a b ω‖ ≤ Theta (msc z) S a b := by
  unfold eLead
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.hΘ0 a b),
    norm_star]
  have h1 := h.G1 ω b b
  have h2 := h.hm1
  have h3 := h.hΘ0 a b
  have h4 : 0 ≤ ‖eG z ω b b‖ := norm_nonneg _
  have h5 : 0 ≤ ‖msc z‖ := norm_nonneg _
  calc ‖msc z‖ * Theta (msc z) S a b * ‖eG z ω b b‖ ≤ 1 * Theta (msc z) S a b * 1 := by
        gcongr
    _ = _ := by ring

/-- The bound of `A₁` from a bound `r` on the diagonal errors. -/
private theorem Eta1Hyp.A1_le (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (a b : ι) (r : ℝ)
    (hr : ∀ y, ‖eG z ω y y - msc z‖ ≤ r) :
    ‖eA1 S z a b ω‖ ≤ r * ∑ x, Theta (msc z) S a x * ‖eG z ω x b‖ ^ 2 := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr b)
  unfold eA1
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * ((S x y : ℂ) *
        ((eG z ω y y - msc z) * (eG z ω x b * star (eG z ω x b)))))‖
      ≤ ∑ x, ∑ y, Theta (msc z) S a x * (S x y * (r * ‖eG z ω x b‖ ^ 2)) := by
        refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h.hΘ0 a x), abs_of_nonneg (h.hnn x y),
          norm_star, ← sq]
        have h1 := h.hm1
        have h2 := hr y
        have h3 := h.hΘ0 a x
        have h4 := h.hnn x y
        have h5 : 0 ≤ ‖eG z ω x b‖ ^ 2 := sq_nonneg _
        have h6 : 0 ≤ ‖msc z‖ := norm_nonneg _
        have h7 : 0 ≤ ‖eG z ω y y - msc z‖ := norm_nonneg _
        calc ‖msc z‖ * (Theta (msc z) S a x * (S x y * (‖eG z ω y y - msc z‖ * ‖eG z ω x b‖ ^ 2)))
            ≤ 1 * (Theta (msc z) S a x * (S x y * (r * ‖eG z ω x b‖ ^ 2))) := by gcongr
          _ = _ := one_mul _
    _ = r * ∑ x, Theta (msc z) S a x * ‖eG z ω x b‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have : ∑ y, Theta (msc z) S a x * (S x y * (r * ‖eG z ω x b‖ ^ 2)) =
            Theta (msc z) S a x * (r * ‖eG z ω x b‖ ^ 2) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, h.hrow x, one_mul]
        rw [this]; ring

/-- The bound of `A₂` from a bound `r` on the diagonal errors. -/
private theorem Eta1Hyp.A2_le (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (a b : ι) (r : ℝ)
    (hr : ∀ x, ‖eG z ω x x - msc z‖ ≤ r) :
    ‖eA2 S z a b ω‖ ≤ r * ∑ x, Theta (msc z) S a x * ∑ y, S x y * ‖eG z ω y b‖ ^ 2 := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr b)
  unfold eA2
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖∑ y, msc z * (((Theta (msc z) S a x : ℝ) : ℂ) * ((S x y : ℂ) *
        ((star (eG z ω x x) - star (msc z)) * (eG z ω y b * star (eG z ω y b)))))‖
      ≤ ∑ x, ∑ y, Theta (msc z) S a x * (S x y * (r * ‖eG z ω y b‖ ^ 2)) := by
        refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h.hΘ0 a x), abs_of_nonneg (h.hnn x y),
          norm_star, ← sq]
        have h1 := h.hm1
        have h2 : ‖star (eG z ω x x) - star (msc z)‖ ≤ r := by
          rw [← star_sub, norm_star]; exact hr x
        have h3 := h.hΘ0 a x
        have h4 := h.hnn x y
        have h5 : 0 ≤ ‖eG z ω y b‖ ^ 2 := sq_nonneg _
        have h6 : 0 ≤ ‖msc z‖ := norm_nonneg _
        have h7 : 0 ≤ ‖star (eG z ω x x) - star (msc z)‖ := norm_nonneg _
        calc ‖msc z‖ * (Theta (msc z) S a x * (S x y *
              (‖star (eG z ω x x) - star (msc z)‖ * ‖eG z ω y b‖ ^ 2)))
            ≤ 1 * (Theta (msc z) S a x * (S x y * (r * ‖eG z ω y b‖ ^ 2))) := by gcongr
          _ = _ := one_mul _
    _ = r * ∑ x, Theta (msc z) S a x * ∑ y, S x y * ‖eG z ω y b‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have : ∑ y, Theta (msc z) S a x * (S x y * (r * ‖eG z ω y b‖ ^ 2)) =
            r * (Theta (msc z) S a x * ∑ y, S x y * ‖eG z ω y b‖ ^ 2) := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
        rw [this]

private theorem Eta1Hyp.A_le (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (ω : Sample ι) (a b : ι) :
    ‖eA1 S z a b ω‖ + ‖eA2 S z a b ω‖ ≤
      δ * Theta (msc z) S a b + (w + 16) * δ * eY S z a b ω +
        Set.indicator Gdᶜ (fun _ => (4 : ℝ)) ω := by
  have hY := h.Y0 ω a b
  have hΘb := h.hΘ0 a b
  have hδ0 := h.hδ0
  have hw := h.hw
  have hm2 : 0 < ‖msc z‖ ^ 2 := by
    have : (0 : ℝ) < ‖msc z‖ := lt_of_lt_of_le (by norm_num) h.hm0
    positivity
  have hm16 : 1 / ‖msc z‖ ^ 2 ≤ 16 := by
    have h4 : (1 : ℝ) / 4 ≤ ‖msc z‖ := h.hm0
    rw [div_le_iff₀ hm2]
    nlinarith
  have hind : 0 ≤ Set.indicator Gdᶜ (fun _ => (4 : ℝ)) ω :=
    Set.indicator_nonneg (fun _ _ => by norm_num) ω
  by_cases hω : ω ∈ Gd
  · have hωc : ω ∉ Gdᶜ := fun hh => hh hω
    rw [Set.indicator_of_notMem hωc, add_zero]
    have hr : ∀ y, ‖eG z ω y y - msc z‖ ≤ δ := fun y => by
      have := h.hGd1 ω hω y y
      simpa [entryErr] using this
    have h1 := h.A1_le ω a b δ hr
    have h2 := h.A2_le ω a b δ hr
    have e1 : ∑ x, Theta (msc z) S a x * ‖eG z ω x b‖ ^ 2 ≤
        Theta (msc z) S a b + w * eY S z a b ω := by
      unfold eY
      rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ b),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
      have hb : Theta (msc z) S a b * ‖eG z ω b b‖ ^ 2 ≤
          Theta (msc z) S a b + w * (Theta (msc z) S a b * eT S z b b ω) := by
        have := h.G1 ω b b
        have h0 := h.T0 ω b b
        have hsq : ‖eG z ω b b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (eG z ω b b)]
        have h8 := mul_le_mul_of_nonneg_left hsq hΘb
        nlinarith [mul_nonneg hΘb (mul_nonneg (by linarith : 0 ≤ w) h0)]
      have hrest : ∑ x ∈ Finset.univ.erase b, Theta (msc z) S a x * ‖eG z ω x b‖ ^ 2 ≤
          ∑ x ∈ Finset.univ.erase b, w * (Theta (msc z) S a x * eT S z x b ω) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hxb : x ≠ b := Finset.ne_of_mem_erase hx
        have := h.hGd2 ω hω x b hxb
        have h3 := h.hΘ0 a x
        nlinarith
      linarith
    have e2 : ∑ x, Theta (msc z) S a x * ∑ y, S x y * ‖eG z ω y b‖ ^ 2 ≤
        16 * eY S z a b ω := by
      unfold eY
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [h.sumsG2 ω x b]
      have h3 := h.hΘ0 a x
      have h4 := h.T0 ω x b
      have : eT S z x b ω / ‖msc z‖ ^ 2 ≤ 16 * eT S z x b ω := by
        rw [div_eq_mul_one_div]
        nlinarith
      nlinarith
    nlinarith
  · rw [Set.indicator_of_mem (show ω ∈ Gdᶜ from hω)]
    have hr : ∀ y, ‖eG z ω y y - msc z‖ ≤ 2 := fun y => by
      have h1 := h.G1 ω y y
      have h2 := h.hm1
      have := norm_sub_le (eG z ω y y) (msc z)
      linarith
    have h1 := h.A1_le ω a b 2 hr
    have h2 := h.A2_le ω a b 2 hr
    have e1 : ∑ x, Theta (msc z) S a x * ‖eG z ω x b‖ ^ 2 ≤ 1 := by
      calc _ ≤ ∑ x, Theta (msc z) S a x * 1 := Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (by
              have := h.G1 ω x b; nlinarith [norm_nonneg (eG z ω x b)]) (h.hΘ0 a x)
        _ ≤ 1 := by simpa using h.hΘ1 a
    have e2 : ∑ x, Theta (msc z) S a x * ∑ y, S x y * ‖eG z ω y b‖ ^ 2 ≤ 1 := by
      calc _ ≤ ∑ x, Theta (msc z) S a x * 1 := Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (by
              calc ∑ y, S x y * ‖eG z ω y b‖ ^ 2 ≤ ∑ y, S x y * 1 :=
                    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (by
                      have := h.G1 ω y b; nlinarith [norm_nonneg (eG z ω y b)]) (h.hnn x y)
                _ = 1 := by simp [h.hrow x]) (h.hΘ0 a x)
        _ ≤ 1 := by simpa using h.hΘ1 a
    have h5 : 0 ≤ δ * Theta (msc z) S a b := mul_nonneg hδ0 hΘb
    have h6 : 0 ≤ (w + 16) * δ * eY S z a b ω := by
      have : 0 ≤ (w + 16) * δ := by positivity
      exact mul_nonneg this hY
    nlinarith

end Apieces



section Weights

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

/-- `|u^{n+1} - v^{n+1}| ≤ (n+1) c^n |u - v|` for `0 ≤ u, v ≤ c`. -/
private theorem eta1_pow_sub_pow (n : ℕ) {u v c : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huc : u ≤ c) (hvc : v ≤ c) :
    |u ^ (n + 1) - v ^ (n + 1)| ≤ (n + 1) * c ^ n * |u - v| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : 0 ≤ c := hu.trans huc
    have e : u ^ (n + 1 + 1) - v ^ (n + 1 + 1) =
        u * (u ^ (n + 1) - v ^ (n + 1)) + v ^ (n + 1) * (u - v) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg (pow_nonneg hv _)]
    have h1 : u * |u ^ (n + 1) - v ^ (n + 1)| ≤ c * ((n + 1) * c ^ n * |u - v|) :=
      mul_le_mul huc ih (abs_nonneg _) hc
    have h2 : v ^ (n + 1) * |u - v| ≤ c ^ (n + 1) * |u - v| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv hvc _) (abs_nonneg _)
    have h3 : c * ((n + 1) * c ^ n * |u - v|) = (n + 1) * c ^ (n + 1) * |u - v| := by
      rw [pow_succ]; ring
    push_cast
    nlinarith [h1, h2, h3]

/-- The weight of the `Q`-graphs at the atom `x`. -/
private def eW (S : Matrix ι ι ℝ) (z : ℂ) (b x : ι) (ω : Sample ι) : ℝ :=
  ‖eF1 z b x ω‖ + ‖msc z‖ * (∑ y, S x y * ‖eF3 z b x y ω‖) +
    ‖msc z‖ * (∑ y, S x y * ‖eF4 z b x y ω‖)

private theorem eta1_norm_F1 (z : ℂ) (b x : ι) (ω : Sample ι) :
    ‖eF1 z b x ω‖ = ‖eG z ω x b‖ ^ 2 := by
  unfold eF1
  rw [norm_mul, norm_star, sq]

private theorem eta1_norm_F3 (z : ℂ) (b x y : ι) (ω : Sample ι) :
    ‖eF3 z b x y ω‖ = ‖eG z ω y y - msc z‖ * ‖eG z ω x b‖ ^ 2 := by
  unfold eF3
  rw [norm_mul, norm_mul, norm_star, sq]

private theorem eta1_norm_F4 (z : ℂ) (b x y : ι) (ω : Sample ι) :
    ‖eF4 z b x y ω‖ = ‖eG z ω x x‖ * ‖eG z ω y b‖ ^ 2 := by
  unfold eF4
  rw [norm_mul, norm_mul, norm_star, norm_star, sq]

private theorem Eta1Hyp.W0 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (b x : ι) (ω : Sample ι) :
    0 ≤ eW S z b x ω := by
  unfold eW
  exact add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn x y) (norm_nonneg _))))
    (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn x y) (norm_nonneg _)))

private theorem Eta1Hyp.W_crude (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (b x : ι) (ω : Sample ι) :
    eW S z b x ω ≤ 4 := by
  unfold eW
  have h1 : ‖eF1 z b x ω‖ ≤ 1 := by
    rw [eta1_norm_F1]; have := h.G1 ω x b; nlinarith [norm_nonneg (eG z ω x b)]
  have h3 : ∑ y, S x y * ‖eF3 z b x y ω‖ ≤ 2 := by
    calc _ ≤ ∑ y, S x y * 2 := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (by
          rw [eta1_norm_F3]
          have h1 := h.G1 ω y y
          have h2 := h.hm1
          have h3 := norm_sub_le (eG z ω y y) (msc z)
          have h4 := h.G1 ω x b
          have h5 : ‖eG z ω x b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (eG z ω x b)]
          have h6 : 0 ≤ ‖eG z ω y y - msc z‖ := norm_nonneg _
          nlinarith) (h.hnn x y)
      _ = 2 := by rw [← Finset.sum_mul, h.hrow x, one_mul]
  have h4 : ∑ y, S x y * ‖eF4 z b x y ω‖ ≤ 1 := by
    calc _ ≤ ∑ y, S x y * 1 := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (by
          rw [eta1_norm_F4]
          have h1 := h.G1 ω x x
          have h2 := h.G1 ω y b
          have h3 : ‖eG z ω y b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (eG z ω y b)]
          have h5 : 0 ≤ ‖eG z ω y b‖ ^ 2 := sq_nonneg _
          nlinarith [norm_nonneg (eG z ω x x)]) (h.hnn x y)
      _ = 1 := by rw [← Finset.sum_mul, h.hrow x, one_mul]
  have hm := h.hm1
  have hm0 := norm_nonneg (msc z)
  have e3 : 0 ≤ ∑ y, S x y * ‖eF3 z b x y ω‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn x y) (norm_nonneg _)
  have e4 : 0 ≤ ∑ y, S x y * ‖eF4 z b x y ω‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn x y) (norm_nonneg _)
  nlinarith

private theorem Eta1Hyp.W_good (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) {ω : Sample ι} (hω : ω ∈ Gd)
    {b x : ι} (hxb : x ≠ b) : eW S z b x ω ≤ 18 * w * eT S z x b ω := by
  unfold eW
  have hT := h.T0 ω x b
  have hw := h.hw
  have hδ := h.hδ
  have hδ0 := h.hδ0
  have hm := h.hm1
  have hm0 := norm_nonneg (msc z)
  have hm2 : 0 < ‖msc z‖ ^ 2 := by
    have : (0 : ℝ) < ‖msc z‖ := lt_of_lt_of_le (by norm_num) h.hm0
    positivity
  have hm16 : 1 / ‖msc z‖ ^ 2 ≤ 16 := by
    have h4 : (1 : ℝ) / 4 ≤ ‖msc z‖ := h.hm0
    rw [div_le_iff₀ hm2]
    nlinarith
  have hG2 := h.hGd2 ω hω x b hxb
  have h1 : ‖eF1 z b x ω‖ ≤ w * eT S z x b ω := by rw [eta1_norm_F1]; exact hG2
  have h3 : ∑ y, S x y * ‖eF3 z b x y ω‖ ≤ δ * (w * eT S z x b ω) := by
    calc _ ≤ ∑ y, S x y * (δ * (w * eT S z x b ω)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (by
            rw [eta1_norm_F3]
            have hr : ‖eG z ω y y - msc z‖ ≤ δ := by
              have := h.hGd1 ω hω y y
              simpa [entryErr] using this
            exact mul_le_mul hr hG2 (sq_nonneg _) hδ0) (h.hnn x y)
      _ = _ := by rw [← Finset.sum_mul, h.hrow x, one_mul]
  have h4 : ∑ y, S x y * ‖eF4 z b x y ω‖ ≤ 16 * eT S z x b ω := by
    calc _ ≤ ∑ y, S x y * (1 * ‖eG z ω y b‖ ^ 2) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (by
            rw [eta1_norm_F4]
            exact mul_le_mul_of_nonneg_right (h.G1 ω x x) (sq_nonneg _)) (h.hnn x y)
      _ = eT S z x b ω / ‖msc z‖ ^ 2 := by
          rw [← h.sumsG2 ω x b]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ ≤ 16 * eT S z x b ω := by
          rw [div_eq_mul_one_div]
          nlinarith
  have e3 : 0 ≤ ∑ y, S x y * ‖eF3 z b x y ω‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn x y) (norm_nonneg _)
  have e4 : 0 ≤ ∑ y, S x y * ‖eF4 z b x y ω‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn x y) (norm_nonneg _)
  have hwT : 0 ≤ w * eT S z x b ω := mul_nonneg (by linarith) hT
  nlinarith [mul_nonneg hδ0 hwT, mul_nonneg hm0 e3, mul_nonneg hm0 e4,
    mul_le_mul_of_nonneg_left h3 hm0, mul_le_mul_of_nonneg_left h4 hm0]

/-- The weight of the `Q`-graphs at the atom `b` (the atom `x = b`). -/
private def eC (S : Matrix ι ι ℝ) (z : ℂ) (b : ι) (ω ω' : Sample ι) : ℝ :=
  ‖eF1 z b b ω - eF1 z b b ω'‖ + ‖msc z‖ * (∑ y, S b y * ‖eF3 z b b y ω - eF3 z b b y ω'‖) +
    ‖msc z‖ * (∑ y, S b y * ‖eF4 z b b y ω - eF4 z b b y ω'‖) +
    ‖msc z‖ * ‖eF2 z b ω - eF2 z b ω'‖

private theorem Eta1Hyp.C0 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (b : ι) (ω ω' : Sample ι) :
    0 ≤ eC S z b ω ω' := by
  unfold eC
  have e3 : 0 ≤ ∑ y, S b y * ‖eF3 z b b y ω - eF3 z b b y ω'‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn b y) (norm_nonneg _)
  have e4 : 0 ≤ ∑ y, S b y * ‖eF4 z b b y ω - eF4 z b b y ω'‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn b y) (norm_nonneg _)
  have := norm_nonneg (msc z)
  have := norm_nonneg (eF1 z b b ω - eF1 z b b ω')
  have := norm_nonneg (eF2 z b ω - eF2 z b ω')
  positivity

private theorem Eta1Hyp.C_crude (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (b : ι) (ω ω' : Sample ι) :
    eC S z b ω ω' ≤ 10 := by
  unfold eC
  have hm := h.hm1
  have hm0 := norm_nonneg (msc z)
  have hF1 : ∀ ω'' : Sample ι, ‖eF1 z b b ω''‖ ≤ 1 := fun ω'' => by
    rw [eta1_norm_F1]; have := h.G1 ω'' b b; nlinarith [norm_nonneg (eG z ω'' b b)]
  have hF2 : ∀ ω'' : Sample ι, ‖eF2 z b ω''‖ ≤ 1 := fun ω'' => by
    unfold eF2; rw [norm_star]; exact h.G1 ω'' b b
  have hF3 : ∀ (ω'' : Sample ι) y, ‖eF3 z b b y ω''‖ ≤ 2 := fun ω'' y => by
    rw [eta1_norm_F3]
    have h1 := h.G1 ω'' y y
    have h3 := norm_sub_le (eG z ω'' y y) (msc z)
    have h4 := h.G1 ω'' b b
    have h5 : ‖eG z ω'' b b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (eG z ω'' b b)]
    have h6 : 0 ≤ ‖eG z ω'' y y - msc z‖ := norm_nonneg _
    nlinarith
  have hF4 : ∀ (ω'' : Sample ι) y, ‖eF4 z b b y ω''‖ ≤ 1 := fun ω'' y => by
    rw [eta1_norm_F4]
    have h1 := h.G1 ω'' b b
    have h2 := h.G1 ω'' y b
    have h3 : ‖eG z ω'' y b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (eG z ω'' y b)]
    have h5 : 0 ≤ ‖eG z ω'' y b‖ ^ 2 := sq_nonneg _
    nlinarith [norm_nonneg (eG z ω'' b b)]
  have d1 : ‖eF1 z b b ω - eF1 z b b ω'‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [hF1 ω, hF1 ω'])
  have d2 : ‖eF2 z b ω - eF2 z b ω'‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [hF2 ω, hF2 ω'])
  have d3 : ∑ y, S b y * ‖eF3 z b b y ω - eF3 z b b y ω'‖ ≤ 4 := by
    calc _ ≤ ∑ y, S b y * 4 := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans (by linarith [hF3 ω y, hF3 ω' y])) (h.hnn b y)
      _ = 4 := by rw [← Finset.sum_mul, h.hrow b, one_mul]
  have d4 : ∑ y, S b y * ‖eF4 z b b y ω - eF4 z b b y ω'‖ ≤ 2 := by
    calc _ ≤ ∑ y, S b y * 2 := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans (by linarith [hF4 ω y, hF4 ω' y])) (h.hnn b y)
      _ = 2 := by rw [← Finset.sum_mul, h.hrow b, one_mul]
  have e3 : 0 ≤ ∑ y, S b y * ‖eF3 z b b y ω - eF3 z b b y ω'‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn b y) (norm_nonneg _)
  have e4 : 0 ≤ ∑ y, S b y * ‖eF4 z b b y ω - eF4 z b b y ω'‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn b y) (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left d3 hm0, mul_le_mul_of_nonneg_left d4 hm0,
    mul_le_mul_of_nonneg_left d2 hm0, mul_nonneg hm0 e3, mul_nonneg hm0 e4]

private theorem Eta1Hyp.C_good (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (b : ι) {ω ω' : Sample ι}
    (hω : ω ∈ Gd) (hω' : ω' ∈ Gd) :
    eC S z b ω ω' ≤ 8 * δ + 2 * δs + 2 * δ ^ 2 := by
  unfold eC
  have hm := h.hm1
  have hm0 := norm_nonneg (msc z)
  have hδ0 := h.hδ0
  have hδs0 := h.hδs0
  have hdiff : ‖eG z ω b b - eG z ω' b b‖ ≤ 2 * δ := by
    have h1 := h.hGd1 ω hω b b
    have h2 := h.hGd1 ω' hω' b b
    simp only [entryErr, ite_true] at h1 h2
    have : eG z ω b b - eG z ω' b b = (eG z ω b b - msc z) - (eG z ω' b b - msc z) := by ring
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  have hGb : ∀ ω'' : Sample ι, ‖eG z ω'' b b‖ ≤ 1 := fun ω'' => h.G1 ω'' b b
  have d1 : ‖eF1 z b b ω - eF1 z b b ω'‖ ≤ 4 * δ := by
    unfold eF1
    have e : eG z ω b b * star (eG z ω b b) - eG z ω' b b * star (eG z ω' b b) =
        (eG z ω b b - eG z ω' b b) * star (eG z ω b b) +
          eG z ω' b b * star (eG z ω b b - eG z ω' b b) := by
      simp only [star_sub]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_star, norm_star]
    have h1 := hGb ω
    have h2 := hGb ω'
    have h3 := norm_nonneg (eG z ω b b)
    have h4 := norm_nonneg (eG z ω' b b)
    have h5 := norm_nonneg (eG z ω b b - eG z ω' b b)
    nlinarith [mul_le_mul hdiff h1 h3 (by linarith), mul_le_mul h2 hdiff h5 zero_le_one]
  have d2 : ‖eF2 z b ω - eF2 z b ω'‖ ≤ 2 * δ := by
    unfold eF2
    rw [← star_sub, norm_star]; exact hdiff
  have d3 : ∑ y, S b y * ‖eF3 z b b y ω - eF3 z b b y ω'‖ ≤ 2 * δ := by
    calc _ ≤ ∑ y, S b y * (2 * δ) := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (by
          refine (norm_sub_le _ _).trans ?_
          have hr : ∀ ω'' : Sample ι, ω'' ∈ Gd → ‖eF3 z b b y ω''‖ ≤ δ := fun ω'' hω'' => by
            rw [eta1_norm_F3]
            have hr : ‖eG z ω'' y y - msc z‖ ≤ δ := by
              have := h.hGd1 ω'' hω'' y y
              simpa [entryErr] using this
            have := hGb ω''
            have h5 : ‖eG z ω'' b b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (eG z ω'' b b)]
            nlinarith [norm_nonneg (eG z ω'' y y - msc z)]
          linarith [hr ω hω, hr ω' hω']) (h.hnn b y)
      _ = 2 * δ := by rw [← Finset.sum_mul, h.hrow b, one_mul]
  have d4 : ∑ y, S b y * ‖eF4 z b b y ω - eF4 z b b y ω'‖ ≤ 2 * (δs + δ ^ 2) := by
    calc _ ≤ ∑ y, (S b y * ‖eG z ω y b‖ ^ 2 + S b y * ‖eG z ω' y b‖ ^ 2) :=
          Finset.sum_le_sum fun y _ => by
            have h0 := h.hnn b y
            have hb : ∀ ω'' : Sample ι, ‖eF4 z b b y ω''‖ ≤ ‖eG z ω'' y b‖ ^ 2 := fun ω'' => by
              rw [eta1_norm_F4]
              have := hGb ω''
              have h5 : 0 ≤ ‖eG z ω'' y b‖ ^ 2 := sq_nonneg _
              nlinarith [norm_nonneg (eG z ω'' b b)]
            have := (norm_sub_le (eF4 z b b y ω) (eF4 z b b y ω')).trans
              (add_le_add (hb ω) (hb ω'))
            nlinarith
      _ = (∑ y, S b y * ‖eG z ω y b‖ ^ 2) + ∑ y, S b y * ‖eG z ω' y b‖ ^ 2 := by
          rw [Finset.sum_add_distrib]
      _ ≤ 2 * (δs + δ ^ 2) := by
          linarith [h.theta_sq hω b b, h.theta_sq hω' b b]
  have e3 : 0 ≤ ∑ y, S b y * ‖eF3 z b b y ω - eF3 z b b y ω'‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn b y) (norm_nonneg _)
  have e4 : 0 ≤ ∑ y, S b y * ‖eF4 z b b y ω - eF4 z b b y ω'‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (h.hnn b y) (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left d3 hm0, mul_le_mul_of_nonneg_left d4 hm0,
    mul_le_mul_of_nonneg_left d2 hm0, mul_nonneg hm0 e3, mul_nonneg hm0 e4,
    mul_nonneg hm0 hδ0, mul_nonneg hm0 hδs0, mul_nonneg hm0 (sq_nonneg δ)]

end Weights



section Vbound

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

/-- Finite sums of bounded measurable functions are bounded measurable. -/
private theorem eta1_bdd_sum {α : Type*} (s : Finset α) (f : α → Sample ι → ℂ)
    (hf : ∀ a ∈ s, BddMeas (f a)) : BddMeas (fun ω => ∑ a ∈ s, f a ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨measurable_const, 0, fun ω => by simp⟩
  | insert a s ha ih =>
    obtain ⟨hm1, C1, h1⟩ := hf a (Finset.mem_insert_self a s)
    obtain ⟨hm2, C2, h2⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    refine ⟨?_, C1 + C2, fun ω => ?_⟩
    · have := hm1.add hm2
      convert this using 1
      funext ω
      simp [Finset.sum_insert ha]
    · show ‖∑ a' ∈ insert a s, f a' ω‖ ≤ C1 + C2
      rw [Finset.sum_insert ha]
      exact (norm_add_le _ _).trans (add_le_add (h1 ω) (h2 ω))

private theorem eta1_bdd_mul {F G : Sample ι → ℂ} (hF : BddMeas F) (hG : BddMeas G) :
    BddMeas (fun ω => F ω * G ω) := by
  obtain ⟨hFm, C, hC⟩ := hF
  obtain ⟨hGm, D, hD⟩ := hG
  refine ⟨hFm.mul hGm, C * D, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC ω) (hD ω) (norm_nonneg _) ((norm_nonneg _).trans (hC ω))

private theorem eta1_bdd_sub {F G : Sample ι → ℂ} (hF : BddMeas F) (hG : BddMeas G) :
    BddMeas (fun ω => F ω - G ω) := by
  obtain ⟨hFm, C, hC⟩ := hF
  obtain ⟨hGm, D, hD⟩ := hG
  exact ⟨hFm.sub hGm, C + D, fun ω => (norm_sub_le _ _).trans (add_le_add (hC ω) (hD ω))⟩

private theorem eta1_bdd_const (c : ℂ) : BddMeas (fun _ : Sample ι => c) := ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

/-- `F - P_x F` is bounded measurable. -/
private theorem eta1_bdd_Q (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ x y, 0 ≤ S x y) (x : ι)
    {F : Sample ι → ℂ} (hF : BddMeas F) : BddMeas (fun ω => F ω - Pexp S x F ω) :=
  eta1_bdd_sub hF ((pqLaws_Pexp S hS hnn).adm_P x F hF)

/-- The generic bound for a finite linear combination of terms `F_k - P_{x_k} F_k`. -/
private theorem eta1_Q_comb (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ x y, 0 ≤ S x y)
    {κ : Type*} [Fintype κ] (c : κ → ℂ) (xs : κ → ι) (F : κ → Sample ι → ℂ)
    (hF : ∀ k, BddMeas (F k)) {X : Sample ι → ℂ} (hX : BddMeas X) :
    BddMeas (fun ω => ∑ k, c k * (F k ω - Pexp S (xs k) (F k) ω)) ∧
    ‖∫ ω, X ω * ∑ k, c k * (F k ω - Pexp S (xs k) (F k) ω) ∂(gaussLaw S)‖ ≤
      ∑ k, ‖c k‖ * ‖∫ ω, X ω * (F k ω - Pexp S (xs k) (F k) ω) ∂(gaussLaw S)‖ := by
  have := isProbabilityMeasure_gaussLaw S
  have hQ : ∀ k, BddMeas (fun ω => F k ω - Pexp S (xs k) (F k) ω) :=
    fun k => eta1_bdd_Q S hS hnn (xs k) (hF k)
  have hterm : ∀ k, BddMeas (fun ω => X ω * (c k * (F k ω - Pexp S (xs k) (F k) ω))) := fun k =>
    eta1_bdd_mul hX (eta1_bdd_mul (eta1_bdd_const _) (hQ k))
  refine ⟨eta1_bdd_sum Finset.univ _ fun k _ => eta1_bdd_mul (eta1_bdd_const _) (hQ k), ?_⟩
  have e1 : ∀ ω, X ω * ∑ k, c k * (F k ω - Pexp S (xs k) (F k) ω) =
      ∑ k, X ω * (c k * (F k ω - Pexp S (xs k) (F k) ω)) := fun ω => by rw [Finset.mul_sum]
  simp only [e1]
  rw [integral_finsetSum _ fun k _ => eta1_integrable_bdd S (hterm k)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have e2 : ∫ ω, X ω * (c k * (F k ω - Pexp S (xs k) (F k) ω)) ∂(gaussLaw S) =
      c k * ∫ ω, X ω * (F k ω - Pexp S (xs k) (F k) ω) ∂(gaussLaw S) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    ring
  rw [e2, norm_mul]

/-- The power `T^k` as a complex function. -/
private def eXc (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (k : ℕ) (ω : Sample ι) : ℂ :=
  ((eT S z a b ω : ℝ) : ℂ) ^ k

private theorem eta1_eXc_bdd (S : Matrix ι ι ℝ) (z : ℂ) (hz : 0 < z.im) (a b : ι) (k : ℕ) :
    BddMeas (eXc S z a b k) :=
  eta1_bdd_of_test (eta1_testFn_pow _ (eta1_eT_test S z hz a b) k)

private theorem eta1_eXc_norm (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (k : ℕ) (ω : Sample ι) :
    ‖eXc S z a b k ω‖ = (eT S z a b ω) ^ k := by
  unfold eXc
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.T0 ω a b)]

/-- `‖∫ T^k (F - P_x F)‖`. -/
private def eQI (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (k : ℕ) (x : ι) (F : Sample ι → ℂ) : ℝ :=
  ‖∫ ω, eXc S z a b k ω * (F ω - Pexp S x F ω) ∂(gaussLaw S)‖

private theorem eta1_V_integral_bound (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (k : ℕ) :
    ‖∫ ω, eXc S z a b k ω * eV S z a b ω ∂(gaussLaw S)‖ ≤
      ∑ x, Theta (msc z) S a x * eQI S z a b k x (eF1 z b x) +
      (‖msc z‖ * Theta (msc z) S a b * eQI S z a b k b (eF2 z b) +
      (∑ x, ∑ y, ‖msc z‖ * (Theta (msc z) S a x * S x y) * eQI S z a b k x (eF3 z b x y) +
       ∑ x, ∑ y, ‖msc z‖ * (Theta (msc z) S a x * S x y) * eQI S z a b k x (eF4 z b x y))) := by
  have := isProbabilityMeasure_gaussLaw S
  have hz := h.hz0
  have hX := eta1_eXc_bdd S z hz a b k
  have hb1 : ∀ x, BddMeas (eF1 z b x) := fun x => eta1_bdd_of_test (eta1_eF1_test z hz b x)
  have hb2 : BddMeas (eF2 z b) := eta1_bdd_of_test (eta1_eF2_test z hz b)
  have hb3 : ∀ p : ι × ι, BddMeas (eF3 z b p.1 p.2) := fun p =>
    eta1_bdd_of_test (eta1_eF3_test z hz b p.1 p.2)
  have hb4 : ∀ p : ι × ι, BddMeas (eF4 z b p.1 p.2) := fun p =>
    eta1_bdd_of_test (eta1_eF4_test z hz b p.1 p.2)
  -- the four pieces
  have hA := eta1_Q_comb S h.hS h.hnn (fun x : ι => ((Theta (msc z) S a x : ℝ) : ℂ)) id
    (fun x => eF1 z b x) hb1 hX
  have hB := eta1_Q_comb S h.hS h.hnn (fun _ : Unit => -(msc z * ((Theta (msc z) S a b : ℝ) : ℂ)))
    (fun _ => b) (fun _ => eF2 z b) (fun _ => hb2) hX
  have hC := eta1_Q_comb S h.hS h.hnn
    (fun p : ι × ι => -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))))
    (fun p => p.1) (fun p => eF3 z b p.1 p.2) hb3 hX
  have hD := eta1_Q_comb S h.hS h.hnn
    (fun p : ι × ι => -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))))
    (fun p => p.1) (fun p => eF4 z b p.1 p.2) hb4 hX
  set VA : Sample ι → ℂ := fun ω => ∑ x : ι, ((Theta (msc z) S a x : ℝ) : ℂ) *
    (eF1 z b x ω - Pexp S (id x) (eF1 z b x) ω) with hVA
  set VB : Sample ι → ℂ := fun ω => ∑ _k : Unit, -(msc z * ((Theta (msc z) S a b : ℝ) : ℂ)) *
    (eF2 z b ω - Pexp S b (eF2 z b) ω) with hVB
  set VC : Sample ι → ℂ := fun ω => ∑ p : ι × ι,
    -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))) *
      (eF3 z b p.1 p.2 ω - Pexp S p.1 (eF3 z b p.1 p.2) ω) with hVC
  set VD : Sample ι → ℂ := fun ω => ∑ p : ι × ι,
    -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))) *
      (eF4 z b p.1 p.2 ω - Pexp S p.1 (eF4 z b p.1 p.2) ω) with hVD
  have hV : ∀ ω, eV S z a b ω = VA ω + (VB ω + (VC ω + VD ω)) := by
    intro ω
    simp only [eV, hVA, hVB, hVC, hVD, id, Finset.univ_unique, Finset.sum_singleton,
      Fintype.sum_prod_type]
    simp only [neg_mul, Finset.sum_neg_distrib]
  have hVAm := hA.1
  have hVBm := hB.1
  have hVCm := hC.1
  have hVDm := hD.1
  have iA : Integrable (fun ω => eXc S z a b k ω * VA ω) (gaussLaw S) :=
    eta1_integrable_bdd S (eta1_bdd_mul hX hVAm)
  have iB : Integrable (fun ω => eXc S z a b k ω * VB ω) (gaussLaw S) :=
    eta1_integrable_bdd S (eta1_bdd_mul hX hVBm)
  have iC : Integrable (fun ω => eXc S z a b k ω * VC ω) (gaussLaw S) :=
    eta1_integrable_bdd S (eta1_bdd_mul hX hVCm)
  have iD : Integrable (fun ω => eXc S z a b k ω * VD ω) (gaussLaw S) :=
    eta1_integrable_bdd S (eta1_bdd_mul hX hVDm)
  have e : ∫ ω, eXc S z a b k ω * eV S z a b ω ∂(gaussLaw S) =
      ∫ ω, eXc S z a b k ω * VA ω ∂(gaussLaw S) + (∫ ω, eXc S z a b k ω * VB ω ∂(gaussLaw S) +
        (∫ ω, eXc S z a b k ω * VC ω ∂(gaussLaw S) + ∫ ω, eXc S z a b k ω * VD ω ∂(gaussLaw S))) := by
    have iCD : Integrable (fun ω => eXc S z a b k ω * VC ω + eXc S z a b k ω * VD ω)
        (gaussLaw S) := iC.add iD
    have iBCD : Integrable (fun ω => eXc S z a b k ω * VB ω +
        (eXc S z a b k ω * VC ω + eXc S z a b k ω * VD ω)) (gaussLaw S) := iB.add iCD
    calc ∫ ω, eXc S z a b k ω * eV S z a b ω ∂(gaussLaw S)
        = ∫ ω, (eXc S z a b k ω * VA ω + (eXc S z a b k ω * VB ω +
            (eXc S z a b k ω * VC ω + eXc S z a b k ω * VD ω))) ∂(gaussLaw S) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp only [hV, mul_add]
      _ = _ := by
          rw [integral_add iA iBCD, integral_add iB iCD, integral_add iC iD]
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_add_le _ _).trans (add_le_add ?_
    ((norm_add_le _ _).trans (add_le_add ?_ ?_)))))
  · refine hA.2.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [id, eQI, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.hΘ0 a x)]
  · refine hB.2.trans (le_of_eq ?_)
    simp only [Finset.univ_unique, Finset.sum_singleton, eQI, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.hΘ0 a b)]
  · refine hC.2.trans (le_of_eq ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [eQI, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h.hΘ0 a x), abs_of_nonneg (h.hnn x y)]
  · refine hD.2.trans (le_of_eq ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [eQI, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h.hΘ0 a x), abs_of_nonneg (h.hnn x y)]

end Vbound



section Vnu

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

private theorem eta1_int_D (S : Matrix ι ι ℝ) {X F : Sample ι → ℂ} (hX : BddMeas X) (hF : BddMeas F)
    (x : ι) :
    Integrable (fun p : Sample ι × Sample ι => ‖X p.1 - X (eta1Rs x p.1 p.2)‖ * ‖F p.1‖)
      ((gaussLaw S).prod (gaussLaw S)) := by
  obtain ⟨hXm, CX, hCX⟩ := hX
  obtain ⟨hFm, CF, hCF⟩ := hF
  refine eta1_bdd_prod_integrable S ?_ ((CX + CX) * CF) fun p => ?_
  · exact (((hXm.comp measurable_fst).sub (hXm.comp (eta1Rs_meas_pair x))).norm).mul
      (hFm.comp measurable_fst).norm
  · have h1 : ‖X p.1 - X (eta1Rs x p.1 p.2)‖ ≤ CX + CX :=
      (norm_sub_le _ _).trans (add_le_add (hCX _) (hCX _))
    have h0 : 0 ≤ ‖F p.1‖ := norm_nonneg _
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) h0)]
    exact mul_le_mul h1 (hCF _) h0 ((norm_nonneg _).trans h1)

private theorem eta1_int_C (S : Matrix ι ι ℝ) {X F : Sample ι → ℂ} (hX : BddMeas X) (hF : BddMeas F)
    (x : ι) :
    Integrable (fun p : Sample ι × Sample ι => ‖X p.1‖ * ‖F p.1 - F (eta1Rs x p.1 p.2)‖)
      ((gaussLaw S).prod (gaussLaw S)) := by
  obtain ⟨hXm, CX, hCX⟩ := hX
  obtain ⟨hFm, CF, hCF⟩ := hF
  refine eta1_bdd_prod_integrable S ?_ (CX * (CF + CF)) fun p => ?_
  · exact (hXm.comp measurable_fst).norm.mul
      (((hFm.comp measurable_fst).sub (hFm.comp (eta1Rs_meas_pair x))).norm)
  · have h1 : ‖F p.1 - F (eta1Rs x p.1 p.2)‖ ≤ CF + CF :=
      (norm_sub_le _ _).trans (add_le_add (hCF _) (hCF _))
    have h0 : 0 ≤ ‖X p.1‖ := norm_nonneg _
    rw [abs_of_nonneg (mul_nonneg h0 (norm_nonneg _))]
    exact mul_le_mul (hCX p.1) h1 (norm_nonneg _) ((norm_nonneg _).trans (hCX p.1))

private theorem eta1_nu_lin {α : Type*} (S : Matrix ι ι ℝ) (s : Finset α) (c : α → ℝ)
    (g : α → Sample ι × Sample ι → ℝ)
    (hg : ∀ a ∈ s, Integrable (g a) ((gaussLaw S).prod (gaussLaw S))) :
    ∫ p, ∑ a ∈ s, c a * g a p ∂((gaussLaw S).prod (gaussLaw S)) =
      ∑ a ∈ s, c a * ∫ p, g a p ∂((gaussLaw S).prod (gaussLaw S)) := by
  rw [integral_finsetSum _ fun a ha => (hg a ha).const_mul (c a)]
  exact Finset.sum_congr rfl fun a _ => integral_const_mul _ _

/-- `‖T^k(ω) - T^k(ω^{[x,η]})‖`. -/
private def eD (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (k : ℕ) (x : ι) (p : Sample ι × Sample ι) : ℝ :=
  ‖eXc S z a b k p.1 - eXc S z a b k (eta1Rs x p.1 p.2)‖

/-- `J1 x = ∫∫ ‖T^k(ω) - T^k(ω^{[x,η]})‖ · W_x(ω)`. -/
private def eJ1 (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (k : ℕ) (x : ι) : ℝ :=
  ∫ p, eD S z a b k x p * eW S z b x p.1 ∂((gaussLaw S).prod (gaussLaw S))

/-- `J2 = ∫∫ T^k(ω) · C(ω, ω^{[b,η]})`. -/
private def eJ2 (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (k : ℕ) : ℝ :=
  ∫ p, ‖eXc S z a b k p.1‖ * eC S z b p.1 (eta1Rs b p.1 p.2) ∂((gaussLaw S).prod (gaussLaw S))

private theorem eta1_QI_D (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (k : ℕ) (x : ι)
    {F : Sample ι → ℂ} (hF : BddMeas F) :
    eQI S z a b k x F ≤ ∫ p, eD S z a b k x p * ‖F p.1‖
      ∂((gaussLaw S).prod (gaussLaw S)) :=
  eta1_E_mul_Q_le S h.hS h.hnn x (eta1_eXc_bdd S z h.hz0 a b k) hF

private theorem eta1_QI_C (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (k : ℕ) (x : ι)
    {F : Sample ι → ℂ} (hF : BddMeas F) :
    eQI S z a b k x F ≤ ∫ p, ‖eXc S z a b k p.1‖ * ‖F p.1 - F (eta1Rs x p.1 p.2)‖
      ∂((gaussLaw S).prod (gaussLaw S)) :=
  eta1_E_mul_Q_le' S x (eta1_eXc_bdd S z h.hz0 a b k) hF

/-- The total of the `Q`-terms at the atom `x`. -/
private def eTx (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (k : ℕ) (x : ι) : ℝ :=
  Theta (msc z) S a x * eQI S z a b k x (eF1 z b x) +
    (∑ y, ‖msc z‖ * (Theta (msc z) S a x * S x y) * eQI S z a b k x (eF3 z b x y) +
      ∑ y, ‖msc z‖ * (Theta (msc z) S a x * S x y) * eQI S z a b k x (eF4 z b x y))

private theorem eta1_Tx_le (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (k : ℕ) (x : ι) :
    eTx S z a b k x ≤ Theta (msc z) S a x * eJ1 S z a b k x := by
  have hz := h.hz0
  have hX := eta1_eXc_bdd S z hz a b k
  have hb1 : BddMeas (eF1 z b x) := eta1_bdd_of_test (eta1_eF1_test z hz b x)
  have hb3 : ∀ y, BddMeas (eF3 z b x y) := fun y => eta1_bdd_of_test (eta1_eF3_test z hz b x y)
  have hb4 : ∀ y, BddMeas (eF4 z b x y) := fun y => eta1_bdd_of_test (eta1_eF4_test z hz b x y)
  have hΘ := h.hΘ0 a x
  have hm0 := norm_nonneg (msc z)
  have i1 : Integrable (fun p : Sample ι × Sample ι => eD S z a b k x p * ‖eF1 z b x p.1‖)
      ((gaussLaw S).prod (gaussLaw S)) := eta1_int_D S hX hb1 x
  have i3 : ∀ y ∈ Finset.univ, Integrable (fun p : Sample ι × Sample ι =>
      eD S z a b k x p * ‖eF3 z b x y p.1‖) ((gaussLaw S).prod (gaussLaw S)) :=
    fun y _ => eta1_int_D S hX (hb3 y) x
  have i4 : ∀ y ∈ Finset.univ, Integrable (fun p : Sample ι × Sample ι =>
      eD S z a b k x p * ‖eF4 z b x y p.1‖) ((gaussLaw S).prod (gaussLaw S)) :=
    fun y _ => eta1_int_D S hX (hb4 y) x
  have e3 := eta1_nu_lin S Finset.univ (fun y => S x y)
    (fun y p => eD S z a b k x p * ‖eF3 z b x y p.1‖) i3
  have e4 := eta1_nu_lin S Finset.univ (fun y => S x y)
    (fun y p => eD S z a b k x p * ‖eF4 z b x y p.1‖) i4
  have iS3 : Integrable (fun p : Sample ι × Sample ι =>
      ∑ y, S x y * (eD S z a b k x p * ‖eF3 z b x y p.1‖)) ((gaussLaw S).prod (gaussLaw S)) :=
    integrable_finsetSum _ fun y hy => (i3 y hy).const_mul _
  have iS4 : Integrable (fun p : Sample ι × Sample ι =>
      ∑ y, S x y * (eD S z a b k x p * ‖eF4 z b x y p.1‖)) ((gaussLaw S).prod (gaussLaw S)) :=
    integrable_finsetSum _ fun y hy => (i4 y hy).const_mul _
  have hsw : ∀ (f : ι → ℝ) (p : Sample ι × Sample ι),
      eD S z a b k x p * (‖msc z‖ * ∑ y, S x y * f y) =
        ‖msc z‖ * ∑ y, S x y * (eD S z a b k x p * f y) := by
    intro f p
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hpt : ∀ p : Sample ι × Sample ι, eD S z a b k x p * eW S z b x p.1 =
      eD S z a b k x p * ‖eF1 z b x p.1‖ +
        (‖msc z‖ * ∑ y, S x y * (eD S z a b k x p * ‖eF3 z b x y p.1‖) +
          ‖msc z‖ * ∑ y, S x y * (eD S z a b k x p * ‖eF4 z b x y p.1‖)) := by
    intro p
    unfold eW
    rw [mul_add, mul_add, hsw (fun y => ‖eF3 z b x y p.1‖) p, hsw (fun y => ‖eF4 z b x y p.1‖) p]
    ring
  have hJ : eJ1 S z a b k x = ∫ p, eD S z a b k x p * ‖eF1 z b x p.1‖ ∂((gaussLaw S).prod (gaussLaw S)) +
      (‖msc z‖ * ∑ y, S x y * ∫ p, eD S z a b k x p * ‖eF3 z b x y p.1‖ ∂((gaussLaw S).prod (gaussLaw S)) +
        ‖msc z‖ * ∑ y, S x y * ∫ p, eD S z a b k x p * ‖eF4 z b x y p.1‖ ∂((gaussLaw S).prod (gaussLaw S))) := by
    unfold eJ1
    simp only [hpt]
    have iS3' : Integrable (fun p : Sample ι × Sample ι => ‖msc z‖ *
        ∑ y, S x y * (eD S z a b k x p * ‖eF3 z b x y p.1‖)) ((gaussLaw S).prod (gaussLaw S)) :=
      iS3.const_mul _
    have iS4' : Integrable (fun p : Sample ι × Sample ι => ‖msc z‖ *
        ∑ y, S x y * (eD S z a b k x p * ‖eF4 z b x y p.1‖)) ((gaussLaw S).prod (gaussLaw S)) :=
      iS4.const_mul _
    have iS34 : Integrable (fun p : Sample ι × Sample ι => ‖msc z‖ *
        ∑ y, S x y * (eD S z a b k x p * ‖eF3 z b x y p.1‖) + ‖msc z‖ *
        ∑ y, S x y * (eD S z a b k x p * ‖eF4 z b x y p.1‖)) ((gaussLaw S).prod (gaussLaw S)) :=
      iS3'.add iS4'
    rw [integral_add i1 iS34, integral_add iS3' iS4', integral_const_mul, integral_const_mul,
      e3, e4]
  rw [hJ]
  unfold eTx
  have q1 := eta1_QI_D h a b k x (hb1)
  have q3 : ∀ y, eQI S z a b k x (eF3 z b x y) ≤ ∫ p, eD S z a b k x p * ‖eF3 z b x y p.1‖
      ∂((gaussLaw S).prod (gaussLaw S)) := fun y => eta1_QI_D h a b k x (hb3 y)
  have q4 : ∀ y, eQI S z a b k x (eF4 z b x y) ≤ ∫ p, eD S z a b k x p * ‖eF4 z b x y p.1‖
      ∂((gaussLaw S).prod (gaussLaw S)) := fun y => eta1_QI_D h a b k x (hb4 y)
  have s3 : ∑ y, ‖msc z‖ * (Theta (msc z) S a x * S x y) * eQI S z a b k x (eF3 z b x y) ≤
      Theta (msc z) S a x * (‖msc z‖ * ∑ y, S x y * ∫ p, eD S z a b k x p * ‖eF3 z b x y p.1‖
        ∂((gaussLaw S).prod (gaussLaw S))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    have := mul_le_mul_of_nonneg_left (q3 y) (mul_nonneg hm0 (mul_nonneg hΘ (h.hnn x y)))
    nlinarith
  have s4 : ∑ y, ‖msc z‖ * (Theta (msc z) S a x * S x y) * eQI S z a b k x (eF4 z b x y) ≤
      Theta (msc z) S a x * (‖msc z‖ * ∑ y, S x y * ∫ p, eD S z a b k x p * ‖eF4 z b x y p.1‖
        ∂((gaussLaw S).prod (gaussLaw S))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    have := mul_le_mul_of_nonneg_left (q4 y) (mul_nonneg hm0 (mul_nonneg hΘ (h.hnn x y)))
    nlinarith
  have := mul_le_mul_of_nonneg_left q1 hΘ
  nlinarith

private theorem eta1_Tb_le (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (k : ℕ) :
    eTx S z a b k b + ‖msc z‖ * Theta (msc z) S a b * eQI S z a b k b (eF2 z b) ≤
      Theta (msc z) S a b * eJ2 S z a b k := by
  have hz := h.hz0
  have hX := eta1_eXc_bdd S z hz a b k
  have hb1 : BddMeas (eF1 z b b) := eta1_bdd_of_test (eta1_eF1_test z hz b b)
  have hb2 : BddMeas (eF2 z b) := eta1_bdd_of_test (eta1_eF2_test z hz b)
  have hb3 : ∀ y, BddMeas (eF3 z b b y) := fun y => eta1_bdd_of_test (eta1_eF3_test z hz b b y)
  have hb4 : ∀ y, BddMeas (eF4 z b b y) := fun y => eta1_bdd_of_test (eta1_eF4_test z hz b b y)
  have hΘ := h.hΘ0 a b
  have hm0 := norm_nonneg (msc z)
  have i1 := eta1_int_C S hX hb1 b
  have i2 := eta1_int_C S hX hb2 b
  have i3 : ∀ y ∈ Finset.univ, Integrable (fun p : Sample ι × Sample ι =>
      ‖eXc S z a b k p.1‖ * ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖)
      ((gaussLaw S).prod (gaussLaw S)) := fun y _ => eta1_int_C S hX (hb3 y) b
  have i4 : ∀ y ∈ Finset.univ, Integrable (fun p : Sample ι × Sample ι =>
      ‖eXc S z a b k p.1‖ * ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖)
      ((gaussLaw S).prod (gaussLaw S)) := fun y _ => eta1_int_C S hX (hb4 y) b
  have e3 := eta1_nu_lin S Finset.univ (fun y => S b y)
    (fun y p => ‖eXc S z a b k p.1‖ * ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖) i3
  have e4 := eta1_nu_lin S Finset.univ (fun y => S b y)
    (fun y p => ‖eXc S z a b k p.1‖ * ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖) i4
  have iS3 : Integrable (fun p : Sample ι × Sample ι => ‖msc z‖ * ∑ y, S b y *
      (‖eXc S z a b k p.1‖ * ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖))
      ((gaussLaw S).prod (gaussLaw S)) :=
    (integrable_finsetSum _ fun y hy => (i3 y hy).const_mul _).const_mul _
  have iS4 : Integrable (fun p : Sample ι × Sample ι => ‖msc z‖ * ∑ y, S b y *
      (‖eXc S z a b k p.1‖ * ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖))
      ((gaussLaw S).prod (gaussLaw S)) :=
    (integrable_finsetSum _ fun y hy => (i4 y hy).const_mul _).const_mul _
  have iS2 : Integrable (fun p : Sample ι × Sample ι => ‖msc z‖ *
      (‖eXc S z a b k p.1‖ * ‖eF2 z b p.1 - eF2 z b (eta1Rs b p.1 p.2)‖))
      ((gaussLaw S).prod (gaussLaw S)) := i2.const_mul _
  have hsw : ∀ (f : ι → ℝ) (p : Sample ι × Sample ι),
      ‖eXc S z a b k p.1‖ * (‖msc z‖ * ∑ y, S b y * f y) =
        ‖msc z‖ * ∑ y, S b y * (‖eXc S z a b k p.1‖ * f y) := by
    intro f p
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hpt : ∀ p : Sample ι × Sample ι,
      ‖eXc S z a b k p.1‖ * eC S z b p.1 (eta1Rs b p.1 p.2) =
        ‖eXc S z a b k p.1‖ * ‖eF1 z b b p.1 - eF1 z b b (eta1Rs b p.1 p.2)‖ +
          (‖msc z‖ * ∑ y, S b y * (‖eXc S z a b k p.1‖ *
              ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖) +
            (‖msc z‖ * ∑ y, S b y * (‖eXc S z a b k p.1‖ *
              ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖) +
            ‖msc z‖ * (‖eXc S z a b k p.1‖ * ‖eF2 z b p.1 - eF2 z b (eta1Rs b p.1 p.2)‖))) := by
    intro p
    unfold eC
    have := hsw (fun y => ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖) p
    have := hsw (fun y => ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖) p
    simp only [mul_add]
    rw [hsw (fun y => ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖) p,
      hsw (fun y => ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖) p]
    ring
  have iS34 : Integrable (fun p : Sample ι × Sample ι =>
      ‖msc z‖ * ∑ y, S b y * (‖eXc S z a b k p.1‖ *
          ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖) +
        ‖msc z‖ * (‖eXc S z a b k p.1‖ * ‖eF2 z b p.1 - eF2 z b (eta1Rs b p.1 p.2)‖))
      ((gaussLaw S).prod (gaussLaw S)) := iS4.add iS2
  have iS234 : Integrable (fun p : Sample ι × Sample ι =>
      ‖msc z‖ * ∑ y, S b y * (‖eXc S z a b k p.1‖ *
          ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖) +
        (‖msc z‖ * ∑ y, S b y * (‖eXc S z a b k p.1‖ *
          ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖) +
        ‖msc z‖ * (‖eXc S z a b k p.1‖ * ‖eF2 z b p.1 - eF2 z b (eta1Rs b p.1 p.2)‖)))
      ((gaussLaw S).prod (gaussLaw S)) := iS3.add iS34
  have hJ : eJ2 S z a b k =
      ∫ p, ‖eXc S z a b k p.1‖ * ‖eF1 z b b p.1 - eF1 z b b (eta1Rs b p.1 p.2)‖
        ∂((gaussLaw S).prod (gaussLaw S)) +
      (‖msc z‖ * ∑ y, S b y * ∫ p, ‖eXc S z a b k p.1‖ *
          ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖ ∂((gaussLaw S).prod (gaussLaw S)) +
        (‖msc z‖ * ∑ y, S b y * ∫ p, ‖eXc S z a b k p.1‖ *
          ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖ ∂((gaussLaw S).prod (gaussLaw S)) +
        ‖msc z‖ * ∫ p, ‖eXc S z a b k p.1‖ * ‖eF2 z b p.1 - eF2 z b (eta1Rs b p.1 p.2)‖
          ∂((gaussLaw S).prod (gaussLaw S)))) := by
    unfold eJ2
    simp only [hpt]
    rw [integral_add i1 iS234, integral_add iS3 iS34, integral_add iS4 iS2,
      integral_const_mul, integral_const_mul, integral_const_mul, e3, e4]
  rw [hJ]
  unfold eTx
  have q1 := eta1_QI_C h a b k b hb1
  have q2 := eta1_QI_C h a b k b hb2
  have q3 : ∀ y, eQI S z a b k b (eF3 z b b y) ≤ ∫ p, ‖eXc S z a b k p.1‖ *
      ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖ ∂((gaussLaw S).prod (gaussLaw S)) :=
    fun y => eta1_QI_C h a b k b (hb3 y)
  have q4 : ∀ y, eQI S z a b k b (eF4 z b b y) ≤ ∫ p, ‖eXc S z a b k p.1‖ *
      ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖ ∂((gaussLaw S).prod (gaussLaw S)) :=
    fun y => eta1_QI_C h a b k b (hb4 y)
  have s3 : ∑ y, ‖msc z‖ * (Theta (msc z) S a b * S b y) * eQI S z a b k b (eF3 z b b y) ≤
      Theta (msc z) S a b * (‖msc z‖ * ∑ y, S b y * ∫ p, ‖eXc S z a b k p.1‖ *
        ‖eF3 z b b y p.1 - eF3 z b b y (eta1Rs b p.1 p.2)‖ ∂((gaussLaw S).prod (gaussLaw S))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    have := mul_le_mul_of_nonneg_left (q3 y) (mul_nonneg hm0 (mul_nonneg hΘ (h.hnn b y)))
    nlinarith
  have s4 : ∑ y, ‖msc z‖ * (Theta (msc z) S a b * S b y) * eQI S z a b k b (eF4 z b b y) ≤
      Theta (msc z) S a b * (‖msc z‖ * ∑ y, S b y * ∫ p, ‖eXc S z a b k p.1‖ *
        ‖eF4 z b b y p.1 - eF4 z b b y (eta1Rs b p.1 p.2)‖ ∂((gaussLaw S).prod (gaussLaw S))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    have := mul_le_mul_of_nonneg_left (q4 y) (mul_nonneg hm0 (mul_nonneg hΘ (h.hnn b y)))
    nlinarith
  have t1 := mul_le_mul_of_nonneg_left q1 hΘ
  have t2 := mul_le_mul_of_nonneg_left q2 (mul_nonneg hm0 hΘ)
  nlinarith

private theorem eta1_V_nu_bound (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (k : ℕ) :
    ‖∫ ω, eXc S z a b k ω * eV S z a b ω ∂(gaussLaw S)‖ ≤
      ∑ x ∈ Finset.univ.erase b, Theta (msc z) S a x * eJ1 S z a b k x +
        Theta (msc z) S a b * eJ2 S z a b k := by
  refine (eta1_V_integral_bound h a b k).trans ?_
  have e : ∑ x, Theta (msc z) S a x * eQI S z a b k x (eF1 z b x) +
      (‖msc z‖ * Theta (msc z) S a b * eQI S z a b k b (eF2 z b) +
        (∑ x, ∑ y, ‖msc z‖ * (Theta (msc z) S a x * S x y) * eQI S z a b k x (eF3 z b x y) +
          ∑ x, ∑ y, ‖msc z‖ * (Theta (msc z) S a x * S x y) * eQI S z a b k x (eF4 z b x y))) =
      ∑ x, eTx S z a b k x + ‖msc z‖ * Theta (msc z) S a b * eQI S z a b k b (eF2 z b) := by
    unfold eTx
    simp only [Finset.sum_add_distrib]
    ring
  rw [e, ← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
  have h1 : ∑ x ∈ Finset.univ.erase b, eTx S z a b k x ≤
      ∑ x ∈ Finset.univ.erase b, Theta (msc z) S a x * eJ1 S z a b k x :=
    Finset.sum_le_sum fun x _ => eta1_Tx_le h a b k x
  have h2 := eta1_Tb_le h a b k
  linarith

end Vnu



section Pointwise

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

/-- The Schur complement identity for the resampled sample. -/
private theorem eta1_schur (z : ℂ) (hz : 0 < z.im) (x b : ι) (ω η : Sample ι) :
    ∀ α : ι, eG z ω α b - eG z ω α x * eG z ω x b / eG z ω x x =
      eG z (eta1Rs x ω η) α b - eG z (eta1Rs x ω η) α x * eG z (eta1Rs x ω η) x b /
        eG z (eta1Rs x ω η) x x := by
  intro α
  have := freeOf_greenMinor z hz x α b ω η
  exact this.symm

/-- `‖T^k(ω) - T^k(ω')‖ = |T(ω)^k - T(ω')^k|`. -/
private theorem eta1_eXc_diff (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) (k : ℕ) (ω ω' : Sample ι) :
    ‖eXc S z a b k ω - eXc S z a b k ω'‖ = |(eT S z a b ω) ^ k - (eT S z a b ω') ^ k| := by
  unfold eXc
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

private theorem eta1_prod_le {u v U V : ℝ} (hU : u ^ 2 ≤ U) (hV : v ^ 2 ≤ V) :
    u * v ≤ (U + V) / 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- The largest of the four normalised values. -/
private def eZ (S : Matrix ι ι ℝ) (z : ℂ) (B : ι → ι → ℝ) (a b x : ι) (ω ω' : Sample ι) : ℝ :=
  max (max (eT S z a b ω / B a b) (eT S z a b ω' / B a b))
    (max (eT S z x b ω / B x b) (eT S z x b ω' / B x b))

private theorem Eta1Hyp.Z0 (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b x : ι) (ω ω' : Sample ι) :
    0 ≤ eZ S z B a b x ω ω' := by
  unfold eZ
  have := h.T0 ω a b
  have := h.hB a b
  exact le_max_of_le_left (le_max_of_le_left (div_nonneg (h.T0 ω a b) (h.hB a b).le))

private theorem Eta1Hyp.Z_X (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b x : ι) (ω ω' : Sample ι) :
    eT S z a b ω ≤ B a b * eZ S z B a b x ω ω' ∧ eT S z a b ω' ≤ B a b * eZ S z B a b x ω ω' ∧
    eT S z x b ω ≤ B x b * eZ S z B a b x ω ω' ∧ eT S z x b ω' ≤ B x b * eZ S z B a b x ω ω' := by
  unfold eZ
  have hB := h.hB a b
  have hB' := h.hB x b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← div_le_iff₀' hB]; exact le_max_of_le_left (le_max_left _ _)
  · rw [← div_le_iff₀' hB]; exact le_max_of_le_left (le_max_right _ _)
  · rw [← div_le_iff₀' hB']; exact le_max_of_le_right (le_max_left _ _)
  · rw [← div_le_iff₀' hB']; exact le_max_of_le_right (le_max_right _ _)

/-- The algebra of the perturbation bound. -/
private theorem eta1_pw_alg {u u' v v' θ θ' δ₃ s δs w Bab Bxb Z : ℝ} (hu : 0 ≤ u) (hu' : 0 ≤ u')
    (hv : 0 ≤ v) (hv' : 0 ≤ v') (hθ : 0 ≤ θ) (hθ' : 0 ≤ θ') (hδ₃ : 0 ≤ δ₃) (hs : 0 ≤ s)
    (hδs : 0 ≤ δs) (hw : 1 ≤ w) (hZ : 0 ≤ Z) (hBab : 0 < Bab) (hBxb : 0 < Bxb)
    (hu2 : u ^ 2 ≤ w * (Bxb * Z)) (hu'2 : u' ^ 2 ≤ w * (Bxb * Z))
    (hv2 : v ^ 2 ≤ 16 * (Bab * Z)) (hv'2 : v' ^ 2 ≤ 16 * (Bab * Z))
    (hθδ : θ ≤ δ₃) (hθ'δ : θ' ≤ δ₃) (hsδ : s ≤ δs) :
    5 * ((u * θ + u' * θ') * (v + v')) + s * (u ^ 2 + u' ^ 2) ≤
      (160 * δ₃ * w * (Bab + Bxb) + 2 * δs * w * Bxb) * Z := by
  have p1 := eta1_prod_le hu2 hv2
  have p2 := eta1_prod_le hu2 hv'2
  have p3 := eta1_prod_le hu'2 hv2
  have p4 := eta1_prod_le hu'2 hv'2
  have hprod : (u + u') * (v + v') ≤ 2 * (w * (Bxb * Z) + 16 * (Bab * Z)) := by
    have e : (u + u') * (v + v') = u * v + u * v' + u' * v + u' * v' := by ring
    rw [e]; linarith
  have hfirst : (u * θ + u' * θ') * (v + v') ≤ δ₃ * ((u + u') * (v + v')) := by
    have h1 : u * θ ≤ u * δ₃ := mul_le_mul_of_nonneg_left hθδ hu
    have h2 : u' * θ' ≤ u' * δ₃ := mul_le_mul_of_nonneg_left hθ'δ hu'
    have h3 : 0 ≤ v + v' := by linarith
    calc (u * θ + u' * θ') * (v + v') ≤ (u * δ₃ + u' * δ₃) * (v + v') :=
          mul_le_mul_of_nonneg_right (add_le_add h1 h2) h3
      _ = δ₃ * ((u + u') * (v + v')) := by ring
  have hsecond : s * (u ^ 2 + u' ^ 2) ≤ δs * (2 * (w * (Bxb * Z))) := by
    have hsum : u ^ 2 + u' ^ 2 ≤ 2 * (w * (Bxb * Z)) := by linarith
    have hs' : 0 ≤ u ^ 2 + u' ^ 2 := by positivity
    calc s * (u ^ 2 + u' ^ 2) ≤ δs * (u ^ 2 + u' ^ 2) := mul_le_mul_of_nonneg_right hsδ hs'
      _ ≤ δs * (2 * (w * (Bxb * Z))) := mul_le_mul_of_nonneg_left hsum hδs
  have e1 : 5 * ((u * θ + u' * θ') * (v + v')) ≤ 10 * δ₃ * (w * (Bxb * Z) + 16 * (Bab * Z)) := by
    have := mul_le_mul_of_nonneg_left hprod hδ₃
    nlinarith
  have hwB : (w * Bxb + 16 * Bab) * Z ≤ 16 * w * (Bab + Bxb) * Z := by
    have : w * Bxb + 16 * Bab ≤ 16 * w * (Bab + Bxb) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hZ
  have e2 : 10 * δ₃ * (w * (Bxb * Z) + 16 * (Bab * Z)) ≤ 160 * δ₃ * w * (Bab + Bxb) * Z := by
    have e : w * (Bxb * Z) + 16 * (Bab * Z) = (w * Bxb + 16 * Bab) * Z := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hwB (by positivity : (0 : ℝ) ≤ 10 * δ₃)
    nlinarith
  nlinarith

/-- The final multiplication. -/
private theorem eta1_pw_mul {D eW X X' Bab Bxb Z w δ₃ δs : ℝ} (n : ℕ) (hD : D ≤ ((n : ℝ) + 1) * (Bab * Z) ^ n * |X - X'|)
    (hXX : |X - X'| ≤ (160 * δ₃ * w * (Bab + Bxb) + 2 * δs * w * Bxb) * Z)
    (hW : eW ≤ 18 * w * (Bxb * Z)) (hD0 : 0 ≤ D) (hW0 : 0 ≤ eW) (hw : 1 ≤ w) (hZ : 0 ≤ Z)
    (hBab : 0 < Bab) (hBxb : 0 < Bxb) (hδ₃ : 0 ≤ δ₃) (hδs : 0 ≤ δs) :
    D * eW ≤ 18 * ((n : ℝ) + 1) * w ^ 2 * (320 * δ₃ + 2 * δs) * Bab ^ n * (Bab ^ 2 + Bxb ^ 2) *
      Z ^ (n + 2) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hBZ : 0 ≤ (Bab * Z) ^ n := by positivity
  have hρ : 0 ≤ (160 * δ₃ * w * (Bab + Bxb) + 2 * δs * w * Bxb) * Z := by positivity
  have h1 : D ≤ ((n : ℝ) + 1) * (Bab * Z) ^ n *
      ((160 * δ₃ * w * (Bab + Bxb) + 2 * δs * w * Bxb) * Z) :=
    hD.trans (mul_le_mul_of_nonneg_left hXX (by positivity))
  have h2 : D * eW ≤ (((n : ℝ) + 1) * (Bab * Z) ^ n *
      ((160 * δ₃ * w * (Bab + Bxb) + 2 * δs * w * Bxb) * Z)) * (18 * w * (Bxb * Z)) :=
    mul_le_mul h1 hW hW0 (by positivity)
  refine h2.trans ?_
  have e : (((n : ℝ) + 1) * (Bab * Z) ^ n *
      ((160 * δ₃ * w * (Bab + Bxb) + 2 * δs * w * Bxb) * Z)) * (18 * w * (Bxb * Z)) =
      18 * ((n : ℝ) + 1) * w ^ 2 * Bab ^ n * Bxb *
        (160 * δ₃ * (Bab + Bxb) + 2 * δs * Bxb) * Z ^ (n + 2) := by
    rw [mul_pow]; ring
  rw [e]
  have hZn : 0 ≤ Z ^ (n + 2) := by positivity
  have hcoef : 0 ≤ 18 * ((n : ℝ) + 1) * w ^ 2 * Bab ^ n * Z ^ (n + 2) := by positivity
  have hin : Bxb * (160 * δ₃ * (Bab + Bxb) + 2 * δs * Bxb) ≤
      (320 * δ₃ + 2 * δs) * (Bab ^ 2 + Bxb ^ 2) := by
    nlinarith [sq_nonneg (Bab - Bxb), mul_nonneg hδ₃ (sq_nonneg (Bab - Bxb)), mul_nonneg hδ₃ hBab.le,
      mul_nonneg hδ₃ hBxb.le, mul_nonneg hδs (sq_nonneg Bab)]
  calc 18 * ((n : ℝ) + 1) * w ^ 2 * Bab ^ n * Bxb *
        (160 * δ₃ * (Bab + Bxb) + 2 * δs * Bxb) * Z ^ (n + 2)
      = (18 * ((n : ℝ) + 1) * w ^ 2 * Bab ^ n * Z ^ (n + 2)) *
        (Bxb * (160 * δ₃ * (Bab + Bxb) + 2 * δs * Bxb)) := by ring
    _ ≤ (18 * ((n : ℝ) + 1) * w ^ 2 * Bab ^ n * Z ^ (n + 2)) *
        ((320 * δ₃ + 2 * δs) * (Bab ^ 2 + Bxb ^ 2)) := mul_le_mul_of_nonneg_left hin hcoef
    _ = _ := by ring

private theorem eta1_pw (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b x : ι) (hx : x ≠ b) (n : ℕ)
    {ω ω' : Sample ι} (hω : ω ∈ Gd) (hω' : ω' ∈ Gd)
    (hsch : ∀ α : ι, eG z ω α b - eG z ω α x * eG z ω x b / eG z ω x x =
      eG z ω' α b - eG z ω' α x * eG z ω' x b / eG z ω' x x) :
    |(eT S z a b ω) ^ (n + 1) - (eT S z a b ω') ^ (n + 1)| * eW S z b x ω ≤
      18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs) * (B a b) ^ n *
        ((B a b) ^ 2 + (B x b) ^ 2) * (eZ S z B a b x ω ω') ^ (n + 2) := by
  obtain ⟨hX, hX', hT3, hT4⟩ := h.Z_X a b x ω ω'
  have hZ0 := h.Z0 a b x ω ω'
  have hBpos := h.hB a b
  have hB'pos := h.hB x b
  have hw := h.hw
  have hδ₃0 : 0 ≤ Real.sqrt (δs + δ ^ 2) := Real.sqrt_nonneg _
  have hX0 : 0 ≤ eT S z a b ω := h.T0 ω a b
  have hX'0 : 0 ≤ eT S z a b ω' := h.T0 ω' a b
  have hm0 := h.hm0
  have hm2 : 0 < ‖msc z‖ ^ 2 := by
    have : (0 : ℝ) < ‖msc z‖ := lt_of_lt_of_le (by norm_num) hm0
    positivity
  have hm16 : 1 / ‖msc z‖ ^ 2 ≤ 16 := by
    rw [div_le_iff₀ hm2]; nlinarith
  have hdT := eta1_dT S h.hnn (eG z ω) (eG z ω') (msc z) hm0 h.hm1 δ h.hδ
    (fun k l => h.hGd1 ω hω k l) (fun k l => h.hGd1 ω' hω' k l) a b x hx (fun α _ => hsch α)
  have hu2 : ‖eG z ω x b‖ ^ 2 ≤ w * (B x b * eZ S z B a b x ω ω') :=
    (h.hGd2 ω hω x b hx).trans (mul_le_mul_of_nonneg_left hT3 (by linarith))
  have hu'2 : ‖eG z ω' x b‖ ^ 2 ≤ w * (B x b * eZ S z B a b x ω ω') :=
    (h.hGd2 ω' hω' x b hx).trans (mul_le_mul_of_nonneg_left hT4 (by linarith))
  have hv2 : eta1Th S a (eG z ω) b ^ 2 ≤ 16 * (B a b * eZ S z B a b x ω ω') := by
    rw [h.eta1Th_sq, h.sumsG2 ω a b, div_eq_mul_one_div]
    have := mul_le_mul hX hm16 (by positivity) (by positivity)
    nlinarith
  have hv'2 : eta1Th S a (eG z ω') b ^ 2 ≤ 16 * (B a b * eZ S z B a b x ω ω') := by
    rw [h.eta1Th_sq, h.sumsG2 ω' a b, div_eq_mul_one_div]
    have := mul_le_mul hX' hm16 (by positivity) (by positivity)
    nlinarith
  have hθx : eta1Th S a (eG z ω) x ≤ Real.sqrt (δs + δ ^ 2) := by
    unfold eta1Th; exact Real.sqrt_le_sqrt (h.theta_sq hω a x)
  have hθx' : eta1Th S a (eG z ω') x ≤ Real.sqrt (δs + δ ^ 2) := by
    unfold eta1Th; exact Real.sqrt_le_sqrt (h.theta_sq hω' a x)
  have hXX : |eT S z a b ω - eT S z a b ω'| ≤
      (160 * Real.sqrt (δs + δ ^ 2) * w * (B a b + B x b) + 2 * δs * w * B x b) *
        eZ S z B a b x ω ω' :=
    hdT.trans (eta1_pw_alg (norm_nonneg _) (norm_nonneg _) (eta1Th_nonneg _ _ _ _)
      (eta1Th_nonneg _ _ _ _) (eta1Th_nonneg _ _ _ _) (eta1Th_nonneg _ _ _ _) hδ₃0
      (h.hnn a x) h.hδs0 hw hZ0 hBpos hB'pos hu2 hu'2 hv2 hv'2 hθx hθx' (h.hSle a x))
  have hD : |(eT S z a b ω) ^ (n + 1) - (eT S z a b ω') ^ (n + 1)| ≤
      ((n : ℝ) + 1) * (B a b * eZ S z B a b x ω ω') ^ n * |eT S z a b ω - eT S z a b ω'| :=
    eta1_pow_sub_pow n hX0 hX'0 hX hX'
  have hW := h.W_good hω hx
  have hW' : eW S z b x ω ≤ 18 * w * (B x b * eZ S z B a b x ω ω') :=
    hW.trans (by
      have := mul_le_mul_of_nonneg_left hT3 (by linarith : (0 : ℝ) ≤ 18 * w)
      linarith)
  exact eta1_pw_mul n hD hXX hW' (abs_nonneg _) (h.W0 b x ω) hw hZ0 hBpos hB'pos hδ₃0 h.hδs0

end Pointwise



section Integrate

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

private theorem eta1_eT_meas (S : Matrix ι ι ℝ) (z : ℂ) (hz : 0 < z.im) (a b : ι) :
    Measurable (fun ω : Sample ι => eT S z a b ω) := by
  have h := (eta1_bdd_of_test (eta1_eT_test S z hz a b)).1
  have h2 := Complex.measurable_re.comp h
  convert h2 using 1
  funext ω
  simp

/-- `∫ g(ω) dν = ∫ g dμ` for a bounded measurable `g` of the first coordinate. -/
private theorem eta1_integral_fst (S : Matrix ι ι ℝ) {g : Sample ι → ℝ} (hg : Measurable g) (C : ℝ)
    (hC : ∀ ω, |g ω| ≤ C) :
    ∫ p, g p.1 ∂((gaussLaw S).prod (gaussLaw S)) = ∫ ω, g ω ∂(gaussLaw S) := by
  have := isProbabilityMeasure_gaussLaw S
  have hi : Integrable (fun p : Sample ι × Sample ι => g p.1) ((gaussLaw S).prod (gaussLaw S)) :=
    eta1_bdd_prod_integrable S (hg.comp measurable_fst) C fun p => hC _
  rw [integral_prod _ hi]
  simp

/-- The set where the sample or the resampled sample is bad. -/
private theorem eta1_bad_measure (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (x : ι) :
    ((gaussLaw S).prod (gaussLaw S)) {p : Sample ι × Sample ι |
        ¬ (p.1 ∈ Gd ∧ eta1Rs x p.1 p.2 ∈ Gd)} ≤ ENNReal.ofReal (2 * ε) := by
  have := isProbabilityMeasure_gaussLaw S
  have hsub : {p : Sample ι × Sample ι | ¬ (p.1 ∈ Gd ∧ eta1Rs x p.1 p.2 ∈ Gd)} ⊆
      (Prod.fst ⁻¹' Gdᶜ) ∪ ((fun p : Sample ι × Sample ι => eta1Rs x p.1 p.2) ⁻¹' Gdᶜ) := by
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at hc
    exact hp ⟨hc.1, hc.2⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have h1 : ((gaussLaw S).prod (gaussLaw S)) (Prod.fst ⁻¹' Gdᶜ) = gaussLaw S Gdᶜ := by
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
  have h2 := eta1_measure_rs S x h.hGdm.compl
  rw [h1, h2]
  calc gaussLaw S Gdᶜ + gaussLaw S Gdᶜ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε :=
        add_le_add h.hGd3 h.hGd3
    _ = ENNReal.ofReal (2 * ε) := by
        rw [← ENNReal.ofReal_add h.hε0 h.hε0]; congr 1; ring

private theorem eta1_max_pow {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (q : ℕ) :
    (max (max a b) (max c d)) ^ q ≤ a ^ q + b ^ q + c ^ q + d ^ q := by
  have h1 := pow_nonneg ha q
  have h2 := pow_nonneg hb q
  have h3 := pow_nonneg hc q
  have h4 := pow_nonneg hd q
  rcases max_choice (max a b) (max c d) with h | h <;> rw [h]
  · rcases max_choice a b with h' | h' <;> rw [h'] <;> linarith
  · rcases max_choice c d with h' | h' <;> rw [h'] <;> linarith

/-- The integrals over the product space of the normalised `q`-th powers. -/
private theorem eta1_int_pow (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (u v x : ι) (Bv : ℝ) (hBv : 0 < Bv)
    (q : ℕ) :
    Integrable (fun p : Sample ι × Sample ι => (eT S z u v p.1 / Bv) ^ q)
        ((gaussLaw S).prod (gaussLaw S)) ∧
    Integrable (fun p : Sample ι × Sample ι => (eT S z u v (eta1Rs x p.1 p.2) / Bv) ^ q)
        ((gaussLaw S).prod (gaussLaw S)) ∧
    ∫ p, (eT S z u v p.1 / Bv) ^ q ∂((gaussLaw S).prod (gaussLaw S)) =
      ∫ ω, (eT S z u v ω / Bv) ^ q ∂(gaussLaw S) ∧
    ∫ p, (eT S z u v (eta1Rs x p.1 p.2) / Bv) ^ q ∂((gaussLaw S).prod (gaussLaw S)) =
      ∫ ω, (eT S z u v ω / Bv) ^ q ∂(gaussLaw S) := by
  have hmeas : Measurable (fun ω : Sample ι => (eT S z u v ω / Bv) ^ q) :=
    ((eta1_eT_meas S z h.hz0 u v).div_const Bv).pow_const q
  have hbd : ∀ ω, |(eT S z u v ω / Bv) ^ q| ≤ (1 / Bv) ^ q := fun ω => by
    have h0 := h.T0 ω u v
    have h1 := h.T1 ω u v
    rw [abs_of_nonneg (pow_nonneg (div_nonneg h0 hBv.le) _)]
    exact pow_le_pow_left₀ (div_nonneg h0 hBv.le) (div_le_div_of_nonneg_right h1 hBv.le) q
  refine ⟨?_, ?_, eta1_integral_fst S hmeas _ hbd, eta1_integral_rs S x hmeas⟩
  · exact eta1_bdd_prod_integrable S (hmeas.comp measurable_fst) _ fun p => hbd _
  · exact eta1_bdd_prod_integrable S (hmeas.comp (eta1Rs_meas_pair x)) _ fun p => hbd _

private theorem eta1_J1_bound (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b x : ι) (hx : x ≠ b) (n : ℕ)
    (M : ℝ) (hM : ∀ u v, ∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S) ≤ M * (B u v) ^ (n + 2)) :
    eJ1 S z a b (n + 1) x ≤
      4 * (18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs)) * M *
        ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2)) + 8 * ε := by
  have := isProbabilityMeasure_gaussLaw S
  have hBpos := h.hB a b
  have hB'pos := h.hB x b
  set ν := (gaussLaw S).prod (gaussLaw S) with hν
  set Cx : ℝ := 18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs) with hCx
  have hCx0 : 0 ≤ Cx := by
    have := h.hw
    have := h.hδs0
    positivity
  set K : ℝ := Cx * ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2)) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨i1, i2, e1, e2⟩ := eta1_int_pow h a b x (B a b) hBpos (n + 2)
  obtain ⟨i3, i4, e3, e4⟩ := eta1_int_pow h x b x (B x b) hB'pos (n + 2)
  set S4 : Sample ι × Sample ι → ℝ := fun p =>
    (eT S z a b p.1 / B a b) ^ (n + 2) + (eT S z a b (eta1Rs x p.1 p.2) / B a b) ^ (n + 2) +
      (eT S z x b p.1 / B x b) ^ (n + 2) + (eT S z x b (eta1Rs x p.1 p.2) / B x b) ^ (n + 2)
    with hS4
  have iS4 : Integrable S4 ν := ((i1.add i2).add i3).add i4
  set N : Set (Sample ι × Sample ι) := {p | ¬ (p.1 ∈ Gd ∧ eta1Rs x p.1 p.2 ∈ Gd)} with hN
  have hNm : MeasurableSet N := by
    have hm1 : MeasurableSet {p : Sample ι × Sample ι | p.1 ∈ Gd} := measurable_fst h.hGdm
    have hm2 : MeasurableSet {p : Sample ι × Sample ι | eta1Rs x p.1 p.2 ∈ Gd} :=
      (eta1Rs_meas_pair x) h.hGdm
    have : N = ({p : Sample ι × Sample ι | p.1 ∈ Gd} ∩ {p | eta1Rs x p.1 p.2 ∈ Gd})ᶜ := by
      ext p; simp [hN]
    rw [this]; exact (hm1.inter hm2).compl
  have hind : Integrable (fun p : Sample ι × Sample ι => N.indicator (fun _ => (1 : ℝ)) p) ν :=
    (integrable_const (1 : ℝ)).indicator hNm
  -- the pointwise majorant
  have hpt : ∀ p : Sample ι × Sample ι,
      eD S z a b (n + 1) x p * eW S z b x p.1 ≤ K * S4 p + 4 * N.indicator (fun _ => (1 : ℝ)) p := by
    intro p
    have hS40 : 0 ≤ S4 p := by
      simp only [hS4]
      have := h.T0 p.1 a b
      have := h.T0 (eta1Rs x p.1 p.2) a b
      have := h.T0 p.1 x b
      have := h.T0 (eta1Rs x p.1 p.2) x b
      positivity
    by_cases hp : p ∈ N
    · rw [Set.indicator_of_mem hp]
      have hD1 : eD S z a b (n + 1) x p ≤ 1 := by
        unfold eD
        rw [eta1_eXc_diff]
        have h0 := h.T0 p.1 a b
        have h1 := h.T1 p.1 a b
        have h0' := h.T0 (eta1Rs x p.1 p.2) a b
        have h1' := h.T1 (eta1Rs x p.1 p.2) a b
        rw [abs_le]
        have a1 := pow_nonneg h0 (n + 1)
        have a2 := pow_nonneg h0' (n + 1)
        have a3 : (eT S z a b p.1) ^ (n + 1) ≤ 1 := pow_le_one₀ h0 h1
        have a4 : (eT S z a b (eta1Rs x p.1 p.2)) ^ (n + 1) ≤ 1 := pow_le_one₀ h0' h1'
        constructor <;> linarith
      have := h.W_crude b x p.1
      have h2 := h.W0 b x p.1
      have h3 : eD S z a b (n + 1) x p * eW S z b x p.1 ≤ 1 * 4 :=
        mul_le_mul hD1 this h2 zero_le_one
      linarith [mul_nonneg hK0 hS40]
    · have hp' : p.1 ∈ Gd ∧ eta1Rs x p.1 p.2 ∈ Gd := by simpa [hN] using hp
      rw [Set.indicator_of_notMem hp, mul_zero, add_zero]
      have hsch := eta1_schur z h.hz0 x b p.1 p.2
      have hpw := eta1_pw h a b x hx n hp'.1 hp'.2 hsch
      have hD : eD S z a b (n + 1) x p = |(eT S z a b p.1) ^ (n + 1) -
          (eT S z a b (eta1Rs x p.1 p.2)) ^ (n + 1)| := by
        unfold eD; rw [eta1_eXc_diff]
      rw [hD]
      refine hpw.trans ?_
      have hZ : (eZ S z B a b x p.1 (eta1Rs x p.1 p.2)) ^ (n + 2) ≤ S4 p := by
        unfold eZ
        refine (eta1_max_pow (div_nonneg (h.T0 _ _ _) hBpos.le) (div_nonneg (h.T0 _ _ _) hBpos.le)
          (div_nonneg (h.T0 _ _ _) hB'pos.le) (div_nonneg (h.T0 _ _ _) hB'pos.le) (n + 2)).trans ?_
        simp only [hS4]; exact le_rfl
      have e : 18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs) * (B a b) ^ n *
          ((B a b) ^ 2 + (B x b) ^ 2) = K := by
        simp only [hK, hCx]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hZ hK0
  -- the integrals
  have hnorm : ∀ u v : ι, ∫ ω, (eT S z u v ω / B u v) ^ (n + 2) ∂(gaussLaw S) ≤ M := by
    intro u v
    have hBuv := h.hB u v
    have : ∫ ω, (eT S z u v ω / B u v) ^ (n + 2) ∂(gaussLaw S) =
        (∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S)) / (B u v) ^ (n + 2) := by
      rw [← integral_div]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [div_pow]
    rw [this, div_le_iff₀ (pow_pos hBuv _)]
    exact hM u v
  have hI4 : ∫ p, S4 p ∂ν ≤ 4 * M := by
    have iA : Integrable (fun p : Sample ι × Sample ι =>
        (eT S z a b p.1 / B a b) ^ (n + 2) + (eT S z a b (eta1Rs x p.1 p.2) / B a b) ^ (n + 2)) ν :=
      i1.add i2
    have iB : Integrable (fun p : Sample ι × Sample ι =>
        (eT S z a b p.1 / B a b) ^ (n + 2) + (eT S z a b (eta1Rs x p.1 p.2) / B a b) ^ (n + 2) +
          (eT S z x b p.1 / B x b) ^ (n + 2)) ν := iA.add i3
    have : ∫ p, S4 p ∂ν = ∫ p, (eT S z a b p.1 / B a b) ^ (n + 2) ∂ν +
        ∫ p, (eT S z a b (eta1Rs x p.1 p.2) / B a b) ^ (n + 2) ∂ν +
        ∫ p, (eT S z x b p.1 / B x b) ^ (n + 2) ∂ν +
        ∫ p, (eT S z x b (eta1Rs x p.1 p.2) / B x b) ^ (n + 2) ∂ν := by
      simp only [hS4]
      rw [integral_add iB i4, integral_add iA i3, integral_add i1 i2]
    rw [this, e1, e2, e3, e4]
    linarith [hnorm a b, hnorm x b]
  have hIn : ∫ p, N.indicator (fun _ => (1 : ℝ)) p ∂ν ≤ 2 * ε := by
    rw [integral_indicator_const _ hNm]
    simp only [smul_eq_mul, mul_one]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith [h.hε0]) (eta1_bad_measure h x)
  have hmono : ∫ p, eD S z a b (n + 1) x p * eW S z b x p.1 ∂ν ≤
      ∫ p, (K * S4 p + 4 * N.indicator (fun _ => (1 : ℝ)) p) ∂ν := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_)
      ((iS4.const_mul K).add (hind.const_mul 4)) (Filter.Eventually.of_forall hpt)
    exact mul_nonneg (norm_nonneg _) (h.W0 b x p.1)
  have hsum : ∫ p, (K * S4 p + 4 * N.indicator (fun _ => (1 : ℝ)) p) ∂ν =
      K * ∫ p, S4 p ∂ν + 4 * ∫ p, N.indicator (fun _ => (1 : ℝ)) p ∂ν := by
    rw [integral_add (iS4.const_mul K) (hind.const_mul 4), integral_const_mul, integral_const_mul]
  unfold eJ1
  have := mul_le_mul_of_nonneg_left hI4 hK0
  calc _ ≤ _ := hmono
    _ = _ := hsum
    _ ≤ 4 * (18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs)) * M *
        ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2)) + 8 * ε := by
        simp only [hK, hCx] at this ⊢
        nlinarith

private theorem eta1_J2_bound (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (n : ℕ) :
    eJ2 S z a b (n + 1) ≤ (8 * δ + 2 * δs + 2 * δ ^ 2) * ∫ ω, (eT S z a b ω) ^ (n + 1) ∂(gaussLaw S) +
      20 * ε := by
  have := isProbabilityMeasure_gaussLaw S
  set ν := (gaussLaw S).prod (gaussLaw S) with hν
  set cb : ℝ := 8 * δ + 2 * δs + 2 * δ ^ 2 with hcb
  have hcb0 : 0 ≤ cb := by
    have := h.hδ0; have := h.hδs0; positivity
  set N : Set (Sample ι × Sample ι) := {p | ¬ (p.1 ∈ Gd ∧ eta1Rs b p.1 p.2 ∈ Gd)} with hN
  have hNm : MeasurableSet N := by
    have hm1 : MeasurableSet {p : Sample ι × Sample ι | p.1 ∈ Gd} := measurable_fst h.hGdm
    have hm2 : MeasurableSet {p : Sample ι × Sample ι | eta1Rs b p.1 p.2 ∈ Gd} :=
      (eta1Rs_meas_pair b) h.hGdm
    have : N = ({p : Sample ι × Sample ι | p.1 ∈ Gd} ∩ {p | eta1Rs b p.1 p.2 ∈ Gd})ᶜ := by
      ext p; simp [hN]
    rw [this]; exact (hm1.inter hm2).compl
  have hind : Integrable (fun p : Sample ι × Sample ι => N.indicator (fun _ => (1 : ℝ)) p) ν :=
    (integrable_const (1 : ℝ)).indicator hNm
  have hmeas : Measurable (fun ω : Sample ι => (eT S z a b ω) ^ (n + 1)) :=
    (eta1_eT_meas S z h.hz0 a b).pow_const _
  have hbd : ∀ ω, |(eT S z a b ω) ^ (n + 1)| ≤ 1 := fun ω => by
    rw [abs_of_nonneg (pow_nonneg (h.T0 ω a b) _)]
    exact pow_le_one₀ (h.T0 ω a b) (h.T1 ω a b)
  have iX : Integrable (fun p : Sample ι × Sample ι => (eT S z a b p.1) ^ (n + 1)) ν :=
    eta1_bdd_prod_integrable S (hmeas.comp measurable_fst) 1 fun p => hbd _
  have hpt : ∀ p : Sample ι × Sample ι,
      ‖eXc S z a b (n + 1) p.1‖ * eC S z b p.1 (eta1Rs b p.1 p.2) ≤
        cb * (eT S z a b p.1) ^ (n + 1) + 10 * N.indicator (fun _ => (1 : ℝ)) p := by
    intro p
    rw [eta1_eXc_norm h]
    have hX0 : 0 ≤ (eT S z a b p.1) ^ (n + 1) := pow_nonneg (h.T0 p.1 a b) _
    have hX1 : (eT S z a b p.1) ^ (n + 1) ≤ 1 := pow_le_one₀ (h.T0 p.1 a b) (h.T1 p.1 a b)
    by_cases hp : p ∈ N
    · rw [Set.indicator_of_mem hp]
      have := h.C_crude b p.1 (eta1Rs b p.1 p.2)
      have h0 := h.C0 b p.1 (eta1Rs b p.1 p.2)
      have := mul_le_mul hX1 this h0 zero_le_one
      nlinarith [mul_nonneg hcb0 hX0]
    · have hp' : p.1 ∈ Gd ∧ eta1Rs b p.1 p.2 ∈ Gd := by simpa [hN] using hp
      rw [Set.indicator_of_notMem hp, mul_zero, add_zero]
      have := mul_le_mul_of_nonneg_left (h.C_good b hp'.1 hp'.2) hX0
      linarith
  have hmono : ∫ p, ‖eXc S z a b (n + 1) p.1‖ * eC S z b p.1 (eta1Rs b p.1 p.2) ∂ν ≤
      ∫ p, (cb * (eT S z a b p.1) ^ (n + 1) + 10 * N.indicator (fun _ => (1 : ℝ)) p) ∂ν := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_)
      ((iX.const_mul cb).add (hind.const_mul 10)) (Filter.Eventually.of_forall hpt)
    exact mul_nonneg (norm_nonneg _) (h.C0 b _ _)
  have hsum : ∫ p, (cb * (eT S z a b p.1) ^ (n + 1) + 10 * N.indicator (fun _ => (1 : ℝ)) p) ∂ν =
      cb * ∫ p, (eT S z a b p.1) ^ (n + 1) ∂ν +
        10 * ∫ p, N.indicator (fun _ => (1 : ℝ)) p ∂ν := by
    rw [integral_add (iX.const_mul cb) (hind.const_mul 10), integral_const_mul, integral_const_mul]
  have hIn : ∫ p, N.indicator (fun _ => (1 : ℝ)) p ∂ν ≤ 2 * ε := by
    rw [integral_indicator_const _ hNm]
    simp only [smul_eq_mul, mul_one]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith [h.hε0]) (eta1_bad_measure h b)
  have hfst := eta1_integral_fst S hmeas 1 hbd
  unfold eJ2
  calc _ ≤ _ := hmono
    _ = _ := hsum
    _ ≤ cb * ∫ ω, (eT S z a b ω) ^ (n + 1) ∂(gaussLaw S) + 20 * ε := by
        rw [hfst]; linarith

end Integrate



section Master

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

private theorem eta1_eLead_test (S : Matrix ι ι ℝ) (z : ℂ) (hz : 0 < z.im) (a b : ι) :
    TestFn (eLead S z a b) :=
  eta1_testFn_mul (eta1_testFn_const _) (eta1_testFn_star (eta1_eG_test z hz b b))

private theorem eta1_eA1_test (S : Matrix ι ι ℝ) (z : ℂ) (hz : 0 < z.im) (a b : ι) :
    TestFn (eA1 S z a b) := by
  have h : ∀ x y : ι, TestFn (fun ω : Sample ι => msc z * (((Theta (msc z) S a x : ℝ) : ℂ) *
      ((S x y : ℂ) * ((eG z ω y y - msc z) * (eG z ω x b * star (eG z ω x b)))))) := fun x y =>
    eta1_testFn_mul (eta1_testFn_const _) (eta1_testFn_mul (eta1_testFn_const _)
      (eta1_testFn_mul (eta1_testFn_const _) (eta1_testFn_mul
        (eta1_testFn_sub (eta1_eG_test z hz y y) (eta1_testFn_const _))
        (eta1_testFn_mul (eta1_eG_test z hz x b) (eta1_testFn_star (eta1_eG_test z hz x b))))))
  exact eta1_testFn_sum Finset.univ _ fun x _ => eta1_testFn_sum Finset.univ _ fun y _ => h x y

private theorem eta1_eA2_test (S : Matrix ι ι ℝ) (z : ℂ) (hz : 0 < z.im) (a b : ι) :
    TestFn (eA2 S z a b) := by
  have h : ∀ x y : ι, TestFn (fun ω : Sample ι => msc z * (((Theta (msc z) S a x : ℝ) : ℂ) *
      ((S x y : ℂ) * ((star (eG z ω x x) - star (msc z)) * (eG z ω y b * star (eG z ω y b)))))) :=
    fun x y =>
    eta1_testFn_mul (eta1_testFn_const _) (eta1_testFn_mul (eta1_testFn_const _)
      (eta1_testFn_mul (eta1_testFn_const _) (eta1_testFn_mul
        (eta1_testFn_sub (eta1_testFn_star (eta1_eG_test z hz x x)) (eta1_testFn_const _))
        (eta1_testFn_mul (eta1_eG_test z hz y b) (eta1_testFn_star (eta1_eG_test z hz y b))))))
  exact eta1_testFn_sum Finset.univ _ fun x _ => eta1_testFn_sum Finset.univ _ fun y _ => h x y

private theorem eta1_eV_bdd (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) : BddMeas (eV S z a b) := by
  have hz := h.hz0
  have hb1 : ∀ x, BddMeas (eF1 z b x) := fun x => eta1_bdd_of_test (eta1_eF1_test z hz b x)
  have hb2 : BddMeas (eF2 z b) := eta1_bdd_of_test (eta1_eF2_test z hz b)
  have hb3 : ∀ p : ι × ι, BddMeas (eF3 z b p.1 p.2) := fun p =>
    eta1_bdd_of_test (eta1_eF3_test z hz b p.1 p.2)
  have hb4 : ∀ p : ι × ι, BddMeas (eF4 z b p.1 p.2) := fun p =>
    eta1_bdd_of_test (eta1_eF4_test z hz b p.1 p.2)
  have hX : BddMeas (fun _ : Sample ι => (1 : ℂ)) := eta1_bdd_const 1
  have hA := (eta1_Q_comb S h.hS h.hnn (fun x : ι => ((Theta (msc z) S a x : ℝ) : ℂ)) id
    (fun x => eF1 z b x) hb1 hX).1
  have hB := (eta1_Q_comb S h.hS h.hnn (fun _ : Unit => -(msc z * ((Theta (msc z) S a b : ℝ) : ℂ)))
    (fun _ => b) (fun _ => eF2 z b) (fun _ => hb2) hX).1
  have hC := (eta1_Q_comb S h.hS h.hnn
    (fun p : ι × ι => -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))))
    (fun p => p.1) (fun p => eF3 z b p.1 p.2) hb3 hX).1
  have hD := (eta1_Q_comb S h.hS h.hnn
    (fun p : ι × ι => -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))))
    (fun p => p.1) (fun p => eF4 z b p.1 p.2) hb4 hX).1
  have hV : ∀ ω, eV S z a b ω =
      (∑ x : ι, ((Theta (msc z) S a x : ℝ) : ℂ) * (eF1 z b x ω - Pexp S (id x) (eF1 z b x) ω)) +
      ((∑ _k : Unit, -(msc z * ((Theta (msc z) S a b : ℝ) : ℂ)) *
          (eF2 z b ω - Pexp S b (eF2 z b) ω)) +
        ((∑ p : ι × ι, -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))) *
          (eF3 z b p.1 p.2 ω - Pexp S p.1 (eF3 z b p.1 p.2) ω)) +
        ∑ p : ι × ι, -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))) *
          (eF4 z b p.1 p.2 ω - Pexp S p.1 (eF4 z b p.1 p.2) ω))) := by
    intro ω
    simp only [eV, id, Finset.univ_unique, Finset.sum_singleton, Fintype.sum_prod_type]
    simp only [neg_mul, Finset.sum_neg_distrib]
  have e : eV S z a b = fun ω => (∑ x : ι, ((Theta (msc z) S a x : ℝ) : ℂ) *
        (eF1 z b x ω - Pexp S (id x) (eF1 z b x) ω)) +
      ((∑ _k : Unit, -(msc z * ((Theta (msc z) S a b : ℝ) : ℂ)) *
          (eF2 z b ω - Pexp S b (eF2 z b) ω)) +
        ((∑ p : ι × ι, -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))) *
          (eF3 z b p.1 p.2 ω - Pexp S p.1 (eF3 z b p.1 p.2) ω)) +
        ∑ p : ι × ι, -(msc z * (((Theta (msc z) S a p.1 : ℝ) : ℂ) * (S p.1 p.2 : ℂ))) *
          (eF4 z b p.1 p.2 ω - Pexp S p.1 (eF4 z b p.1 p.2) ω))) := funext hV
  rw [e]
  obtain ⟨hAm, CA, hAC⟩ := hA
  obtain ⟨hBm, CB, hBC⟩ := hB
  obtain ⟨hCm, CC, hCC⟩ := hC
  obtain ⟨hDm, CD, hDC⟩ := hD
  refine ⟨hAm.add (hBm.add (hCm.add hDm)), CA + (CB + (CC + CD)), fun ω => ?_⟩
  refine (norm_add_le _ _).trans (add_le_add (hAC ω) ((norm_add_le _ _).trans
    (add_le_add (hBC ω) ((norm_add_le _ _).trans (add_le_add (hCC ω) (hDC ω))))))

private theorem eta1_young (n : ℕ) {K X : ℝ} (hK : 0 ≤ K) (hX : 0 ≤ X) :
    K * X ^ (n + 1) ≤ X ^ (n + 2) / 2 + 2 ^ (n + 1) * K ^ (n + 2) := by
  have h0 : 0 ≤ X ^ (n + 2) := pow_nonneg hX _
  have h1 : 0 ≤ K ^ (n + 2) := pow_nonneg hK _
  by_cases hKX : K ≤ X / 2
  · have h2 : K * X ^ (n + 1) ≤ (X / 2) * X ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hKX (pow_nonneg hX _)
    have e : (X / 2) * X ^ (n + 1) = X ^ (n + 2) / 2 := by ring
    have : 0 ≤ 2 ^ (n + 1) * K ^ (n + 2) := by positivity
    linarith
  · have hXK : X ≤ 2 * K := by linarith
    have h2 : X ^ (n + 1) ≤ (2 * K) ^ (n + 1) := pow_le_pow_left₀ hX hXK _
    have h3 : K * X ^ (n + 1) ≤ K * (2 * K) ^ (n + 1) := mul_le_mul_of_nonneg_left h2 hK
    have e : K * (2 * K) ^ (n + 1) = 2 ^ (n + 1) * K ^ (n + 2) := by ring
    linarith

private theorem eta1_norm_moment (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (n : ℕ) (M : ℝ)
    (hM : ∀ u v, ∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S) ≤ M * (B u v) ^ (n + 2)) (u v : ι) :
    ∫ ω, (eT S z u v ω / B u v) ^ (n + 2) ∂(gaussLaw S) ≤ M := by
  have := isProbabilityMeasure_gaussLaw S
  have hBuv := h.hB u v
  have : ∫ ω, (eT S z u v ω / B u v) ^ (n + 2) ∂(gaussLaw S) =
      (∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S)) / (B u v) ^ (n + 2) := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [div_pow]
  rw [this, div_le_iff₀ (pow_pos hBuv _)]
  exact hM u v

private theorem eta1_integrable_real {f : Sample ι → ℝ} (S : Matrix ι ι ℝ) (hm : Measurable f) (C : ℝ)
    (hC : ∀ ω, |f ω| ≤ C) : Integrable f (gaussLaw S) := by
  have := isProbabilityMeasure_gaussLaw S
  exact Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hC ω)

private theorem eta1_uv_le (n : ℕ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ (n + 1) * v ≤ u ^ (n + 2) + v ^ (n + 2) := by
  have h1 := pow_nonneg hu (n + 2)
  have h2 := pow_nonneg hv (n + 2)
  by_cases huv : v ≤ u
  · have : u ^ (n + 1) * v ≤ u ^ (n + 1) * u := mul_le_mul_of_nonneg_left huv (pow_nonneg hu _)
    have e : u ^ (n + 1) * u = u ^ (n + 2) := by ring
    linarith
  · have hvu : u ≤ v := by linarith
    have : u ^ (n + 1) ≤ v ^ (n + 1) := pow_le_pow_left₀ hu hvu _
    have h3 : u ^ (n + 1) * v ≤ v ^ (n + 1) * v :=
      mul_le_mul_of_nonneg_right this hv
    have e : v ^ (n + 1) * v = v ^ (n + 2) := by ring
    linarith

private theorem eta1_pow_ratio_le {X B : ℝ} (hX : 0 ≤ X) (hX1 : X ≤ 1) (hB : 0 < B) (q : ℕ) :
    (X / B) ^ q ≤ (1 / B) ^ q :=
  pow_le_pow_left₀ (div_nonneg hX hB.le) (div_le_div_of_nonneg_right hX1 hB.le) q

/-- `∫ T_{ab}^{n+1} T_{xb} ≤ 2 M B_{ab}^{n+1} B_{xb}`. -/
private theorem eta1_int_XT (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (n : ℕ) (M : ℝ)
    (hM : ∀ u v, ∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S) ≤ M * (B u v) ^ (n + 2)) (a b x : ι) :
    ∫ ω, (eT S z a b ω) ^ (n + 1) * eT S z x b ω ∂(gaussLaw S) ≤
      2 * M * ((B a b) ^ (n + 1) * B x b) := by
  have := isProbabilityMeasure_gaussLaw S
  have hBpos := h.hB a b
  have hB'pos := h.hB x b
  have hm1 : ∀ u v : ι, Measurable (fun ω : Sample ι => (eT S z u v ω / B u v) ^ (n + 2)) :=
    fun u v => ((eta1_eT_meas S z h.hz0 u v).div_const _).pow_const _
  have hint : ∀ u v : ι, Integrable (fun ω : Sample ι => (eT S z u v ω / B u v) ^ (n + 2))
      (gaussLaw S) := fun u v =>
    eta1_integrable_real S (hm1 u v) ((1 / B u v) ^ (n + 2)) fun ω => by
      have h0 := h.T0 ω u v
      rw [abs_of_nonneg (pow_nonneg (div_nonneg h0 (h.hB u v).le) _)]
      exact eta1_pow_ratio_le h0 (h.T1 ω u v) (h.hB u v) _
  have hpt : ∀ ω : Sample ι, (eT S z a b ω) ^ (n + 1) * eT S z x b ω ≤
      (B a b) ^ (n + 1) * B x b * ((eT S z a b ω / B a b) ^ (n + 2) +
        (eT S z x b ω / B x b) ^ (n + 2)) := by
    intro ω
    have h0 := h.T0 ω a b
    have h0' := h.T0 ω x b
    have := eta1_uv_le n (div_nonneg h0 hBpos.le) (div_nonneg h0' hB'pos.le)
    have e : (eT S z a b ω) ^ (n + 1) * eT S z x b ω =
        (B a b) ^ (n + 1) * B x b * ((eT S z a b ω / B a b) ^ (n + 1) *
          (eT S z x b ω / B x b)) := by
      rw [div_pow]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hmXT : Measurable (fun ω : Sample ι => (eT S z a b ω) ^ (n + 1) * eT S z x b ω) :=
    ((eta1_eT_meas S z h.hz0 a b).pow_const (n + 1)).mul (eta1_eT_meas S z h.hz0 x b)
  have hX := eta1_integrable_real S hmXT 1 fun ω => by
      have h0 := h.T0 ω a b
      have h1 := h.T1 ω a b
      have h0' := h.T0 ω x b
      have h1' := h.T1 ω x b
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg h0 _) h0')]
      calc _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ h0 h1) h1' h0' zero_le_one
        _ = 1 := one_mul _
  calc ∫ ω, (eT S z a b ω) ^ (n + 1) * eT S z x b ω ∂(gaussLaw S)
      ≤ ∫ ω, (B a b) ^ (n + 1) * B x b * ((eT S z a b ω / B a b) ^ (n + 2) +
        (eT S z x b ω / B x b) ^ (n + 2)) ∂(gaussLaw S) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
          (((hint a b).add (hint x b)).const_mul _) (Filter.Eventually.of_forall hpt)
        exact mul_nonneg (pow_nonneg (h.T0 ω a b) _) (h.T0 ω x b)
    _ = (B a b) ^ (n + 1) * B x b * (∫ ω, (eT S z a b ω / B a b) ^ (n + 2) ∂(gaussLaw S) +
        ∫ ω, (eT S z x b ω / B x b) ^ (n + 2) ∂(gaussLaw S)) := by
        rw [integral_const_mul, integral_add (hint a b) (hint x b)]
    _ ≤ (B a b) ^ (n + 1) * B x b * (M + M) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (eta1_norm_moment h n M hM a b)
          (eta1_norm_moment h n M hM x b)) (by positivity)
    _ = 2 * M * ((B a b) ^ (n + 1) * B x b) := by ring

end Master



section Master2

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

/-- The constant of the self-improving moment bound. -/
private def eGam (n : ℕ) (δ w δs κ₂ : ℝ) : ℝ :=
  (2 * (w + 16) * δ + 4 * (18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs))) *
    (1 + κ₂)

/-- The constant of the leading term. -/
private def eKap (δ δs κ₁ : ℝ) : ℝ := 2 * (1 + δ + (8 * δ + 2 * δs + 2 * δ ^ 2)) * κ₁

private theorem Eta1Hyp.ratio_sum (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (a b : ι) (n : ℕ) :
    ∑ x, Theta (msc z) S a x * ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2)) ≤
      (B a b) ^ (n + 2) * (1 + κ₂) := by
  have hB := h.hB a b
  have h1 := h.hΘ1 a
  have h3 := h.hΘ3 a b
  have e : ∀ x, Theta (msc z) S a x * ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2)) =
      (B a b) ^ (n + 2) * (Theta (msc z) S a x + Theta (msc z) S a x * (B x b / B a b) ^ 2) := by
    intro x
    field_simp
    ring
  simp only [e, ← Finset.mul_sum, Finset.sum_add_distrib]
  have : 0 ≤ (B a b) ^ (n + 2) := by positivity
  nlinarith

private theorem eta1_Vint_bound (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (n : ℕ) (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ u v, ∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S) ≤ M * (B u v) ^ (n + 2)) (a b : ι) :
    ‖∫ ω, eXc S z a b (n + 1) ω * eV S z a b ω ∂(gaussLaw S)‖ ≤
      4 * (18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs)) * M *
          ((B a b) ^ (n + 2) * (1 + κ₂)) + 8 * ε +
        Theta (msc z) S a b * ((8 * δ + 2 * δs + 2 * δ ^ 2) *
          ∫ ω, (eT S z a b ω) ^ (n + 1) ∂(gaussLaw S) + 20 * ε) := by
  refine (eta1_V_nu_bound h a b (n + 1)).trans ?_
  set Cx : ℝ := 18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs) with hCx
  have hCx0 : 0 ≤ Cx := by
    have := h.hw; have := h.hδs0; positivity
  have hΘb := h.hΘ0 a b
  have hJ2 := eta1_J2_bound h a b n
  have h2 : Theta (msc z) S a b * eJ2 S z a b (n + 1) ≤ Theta (msc z) S a b *
      ((8 * δ + 2 * δs + 2 * δ ^ 2) * ∫ ω, (eT S z a b ω) ^ (n + 1) ∂(gaussLaw S) + 20 * ε) :=
    mul_le_mul_of_nonneg_left hJ2 hΘb
  have h1 : ∑ x ∈ Finset.univ.erase b, Theta (msc z) S a x * eJ1 S z a b (n + 1) x ≤
      4 * Cx * M * ((B a b) ^ (n + 2) * (1 + κ₂)) + 8 * ε := by
    calc ∑ x ∈ Finset.univ.erase b, Theta (msc z) S a x * eJ1 S z a b (n + 1) x
        ≤ ∑ x ∈ Finset.univ.erase b, (4 * Cx * M * (Theta (msc z) S a x *
            ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2))) + 8 * ε * Theta (msc z) S a x) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hxb : x ≠ b := Finset.ne_of_mem_erase hx
          have := mul_le_mul_of_nonneg_left (eta1_J1_bound h a b x hxb n M hM) (h.hΘ0 a x)
          simp only [hCx] at this ⊢
          nlinarith
      _ ≤ ∑ x, (4 * Cx * M * (Theta (msc z) S a x *
            ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2))) + 8 * ε * Theta (msc z) S a x) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun x _ _ => ?_
          have h0 := h.hΘ0 a x
          have hBa := h.hB a b
          have hBx := h.hB x b
          have : 0 ≤ 4 * Cx * M := by positivity
          have h5 : 0 ≤ 8 * ε * Theta (msc z) S a x := mul_nonneg (by linarith [h.hε0]) h0
          have h6 : 0 ≤ 4 * Cx * M * (Theta (msc z) S a x *
              ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2))) := by positivity
          linarith
      _ = 4 * Cx * M * ∑ x, Theta (msc z) S a x * ((B a b) ^ n * ((B a b) ^ 2 + (B x b) ^ 2)) +
            8 * ε * ∑ x, Theta (msc z) S a x := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
          have hr := h.ratio_sum a b n
          have hs := h.hΘ1 a
          have : 0 ≤ 4 * Cx * M := by positivity
          have h7 := mul_le_mul_of_nonneg_left hr this
          have h8 := mul_le_mul_of_nonneg_left hs (by linarith [h.hε0] : 0 ≤ 8 * ε)
          linarith
  linarith

private theorem eta1_R_bound (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (n : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, ∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S) ≤ M * (B u v) ^ (n + 2)) (a b : ι) :
    ‖∫ ω, eXc S z a b (n + 1) ω * (eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω)
        ∂(gaussLaw S)‖ ≤
      (1 + δ) * Theta (msc z) S a b * ∫ ω, (eT S z a b ω) ^ (n + 1) ∂(gaussLaw S) +
        2 * (w + 16) * δ * M * ((B a b) ^ (n + 2) * (1 + κ₂)) + 4 * ε := by
  have := isProbabilityMeasure_gaussLaw S
  have hz := h.hz0
  have hΘb := h.hΘ0 a b
  have hδ0 := h.hδ0
  have hw := h.hw
  have hBpos := h.hB a b
  set μ := gaussLaw S with hμ
  have hmX : Measurable (fun ω : Sample ι => (eT S z a b ω) ^ (n + 1)) :=
    (eta1_eT_meas S z hz a b).pow_const _
  have hX1 : ∀ ω, (eT S z a b ω) ^ (n + 1) ≤ 1 := fun ω =>
    pow_le_one₀ (h.T0 ω a b) (h.T1 ω a b)
  have hX0 : ∀ ω, 0 ≤ (eT S z a b ω) ^ (n + 1) := fun ω => pow_nonneg (h.T0 ω a b) _
  have iX : Integrable (fun ω : Sample ι => (eT S z a b ω) ^ (n + 1)) μ :=
    eta1_integrable_real S hmX 1 fun ω => by rw [abs_of_nonneg (hX0 ω)]; exact hX1 ω
  have hmXT : ∀ x, Measurable (fun ω : Sample ι => (eT S z a b ω) ^ (n + 1) * eT S z x b ω) :=
    fun x => ((eta1_eT_meas S z hz a b).pow_const _).mul (eta1_eT_meas S z hz x b)
  have iXT : ∀ x, Integrable (fun ω : Sample ι => (eT S z a b ω) ^ (n + 1) * eT S z x b ω) μ :=
    fun x => eta1_integrable_real S (hmXT x) 1 fun ω => by
      rw [abs_of_nonneg (mul_nonneg (hX0 ω) (h.T0 ω x b))]
      calc _ ≤ 1 * 1 := mul_le_mul (hX1 ω) (h.T1 ω x b) (h.T0 ω x b) zero_le_one
        _ = 1 := one_mul _
  have hGm : MeasurableSet Gdᶜ := h.hGdm.compl
  have iind : Integrable (fun ω : Sample ι => Gdᶜ.indicator (fun _ => (4 : ℝ)) ω) μ :=
    (integrable_const (4 : ℝ)).indicator hGm
  have iXY : Integrable (fun ω : Sample ι => (eT S z a b ω) ^ (n + 1) * eY S z a b ω) μ := by
    have : ∀ ω : Sample ι, (eT S z a b ω) ^ (n + 1) * eY S z a b ω =
        ∑ x, Theta (msc z) S a x * ((eT S z a b ω) ^ (n + 1) * eT S z x b ω) := by
      intro ω; unfold eY; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [this]
    exact integrable_finsetSum _ fun x _ => (iXT x).const_mul _
  -- the pointwise majorant
  have hpt : ∀ ω : Sample ι, ‖eXc S z a b (n + 1) ω *
      (eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω)‖ ≤
      (1 + δ) * Theta (msc z) S a b * (eT S z a b ω) ^ (n + 1) +
        (w + 16) * δ * ((eT S z a b ω) ^ (n + 1) * eY S z a b ω) +
          Gdᶜ.indicator (fun _ => (4 : ℝ)) ω := by
    intro ω
    rw [norm_mul, eta1_eXc_norm h]
    have h1 := h.lead_le ω a b
    have h2 := h.A_le ω a b
    have hn : ‖eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω‖ ≤
        ‖eLead S z a b ω‖ + ‖eA1 S z a b ω‖ + ‖eA2 S z a b ω‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _ |>.trans' (by
        have := norm_add_le (eLead S z a b ω + eA1 S z a b ω) (eA2 S z a b ω)
        have := norm_add_le (eLead S z a b ω) (eA1 S z a b ω)
        linarith))
    have hx0 := hX0 ω
    have hx1 := hX1 ω
    have hind0 : 0 ≤ Gdᶜ.indicator (fun _ => (4 : ℝ)) ω :=
      Set.indicator_nonneg (fun _ _ => by norm_num) ω
    have hY0 := h.Y0 ω a b
    calc (eT S z a b ω) ^ (n + 1) * ‖eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω‖
        ≤ (eT S z a b ω) ^ (n + 1) * (Theta (msc z) S a b + (δ * Theta (msc z) S a b +
            (w + 16) * δ * eY S z a b ω + Gdᶜ.indicator (fun _ => (4 : ℝ)) ω)) := by
          refine mul_le_mul_of_nonneg_left (hn.trans ?_) hx0
          linarith
      _ = (1 + δ) * Theta (msc z) S a b * (eT S z a b ω) ^ (n + 1) +
          (w + 16) * δ * ((eT S z a b ω) ^ (n + 1) * eY S z a b ω) +
          (eT S z a b ω) ^ (n + 1) * Gdᶜ.indicator (fun _ => (4 : ℝ)) ω := by ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_right hx1 hind0
          linarith
  -- the integrals of the pieces
  have hXY : ∫ ω, (eT S z a b ω) ^ (n + 1) * eY S z a b ω ∂μ ≤
      2 * M * ((B a b) ^ (n + 2) * (1 + κ₂)) := by
    have e : ∀ ω : Sample ι, (eT S z a b ω) ^ (n + 1) * eY S z a b ω =
        ∑ x, Theta (msc z) S a x * ((eT S z a b ω) ^ (n + 1) * eT S z x b ω) := by
      intro ω; unfold eY; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [e]
    rw [integral_finsetSum _ fun x _ => (iXT x).const_mul _]
    have hterm : ∀ x, ∫ ω, Theta (msc z) S a x * ((eT S z a b ω) ^ (n + 1) * eT S z x b ω) ∂μ ≤
        2 * M * ((B a b) ^ (n + 2) * (Theta (msc z) S a x * (B x b / B a b))) := by
      intro x
      rw [integral_const_mul]
      have := mul_le_mul_of_nonneg_left (eta1_int_XT h n M hM a b x) (h.hΘ0 a x)
      have e2 : (B a b) ^ (n + 2) * (Theta (msc z) S a x * (B x b / B a b)) =
          Theta (msc z) S a x * ((B a b) ^ (n + 1) * B x b) := by
        field_simp; ring
      rw [e2]; linarith
    calc _ ≤ ∑ x, 2 * M * ((B a b) ^ (n + 2) * (Theta (msc z) S a x * (B x b / B a b))) :=
          Finset.sum_le_sum fun x _ => hterm x
      _ = 2 * M * ((B a b) ^ (n + 2) * ∑ x, Theta (msc z) S a x * (B x b / B a b)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * M * ((B a b) ^ (n + 2) * (1 + κ₂)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (by positivity)
          calc ∑ x, Theta (msc z) S a x * (B x b / B a b)
              ≤ ∑ x, (Theta (msc z) S a x + Theta (msc z) S a x * (B x b / B a b) ^ 2) :=
                Finset.sum_le_sum fun x _ => by
                  have h0 := h.hΘ0 a x
                  have : B x b / B a b ≤ 1 + (B x b / B a b) ^ 2 := by
                    nlinarith [sq_nonneg (B x b / B a b - 1)]
                  nlinarith
            _ = ∑ x, Theta (msc z) S a x + ∑ x, Theta (msc z) S a x * (B x b / B a b) ^ 2 :=
                Finset.sum_add_distrib
            _ ≤ 1 + κ₂ := add_le_add (h.hΘ1 a) (h.hΘ3 a b)
  have hind : ∫ ω, Gdᶜ.indicator (fun _ => (4 : ℝ)) ω ∂μ ≤ 4 * ε := by
    rw [integral_indicator_const _ hGm]
    simp only [smul_eq_mul]
    have : μ.real Gdᶜ ≤ ε := ENNReal.toReal_le_of_le_ofReal h.hε0 h.hGd3
    linarith
  have iA : Integrable (fun ω : Sample ι => (1 + δ) * Theta (msc z) S a b *
      (eT S z a b ω) ^ (n + 1)) μ := iX.const_mul _
  have iB : Integrable (fun ω : Sample ι => (w + 16) * δ *
      ((eT S z a b ω) ^ (n + 1) * eY S z a b ω)) μ := iXY.const_mul _
  have iAB : Integrable (fun ω : Sample ι => (1 + δ) * Theta (msc z) S a b *
      (eT S z a b ω) ^ (n + 1) + (w + 16) * δ * ((eT S z a b ω) ^ (n + 1) * eY S z a b ω)) μ :=
    iA.add iB
  have hint : Integrable (fun ω : Sample ι => (1 + δ) * Theta (msc z) S a b *
      (eT S z a b ω) ^ (n + 1) + (w + 16) * δ * ((eT S z a b ω) ^ (n + 1) * eY S z a b ω) +
        Gdᶜ.indicator (fun _ => (4 : ℝ)) ω) μ := iAB.add iind
  have hmono : ∫ ω, ‖eXc S z a b (n + 1) ω * (eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω)‖
      ∂μ ≤ ∫ ω, ((1 + δ) * Theta (msc z) S a b * (eT S z a b ω) ^ (n + 1) +
        (w + 16) * δ * ((eT S z a b ω) ^ (n + 1) * eY S z a b ω) +
          Gdᶜ.indicator (fun _ => (4 : ℝ)) ω) ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hint
      (Filter.Eventually.of_forall hpt)
  have hsum : ∫ ω, ((1 + δ) * Theta (msc z) S a b * (eT S z a b ω) ^ (n + 1) +
        (w + 16) * δ * ((eT S z a b ω) ^ (n + 1) * eY S z a b ω) +
          Gdᶜ.indicator (fun _ => (4 : ℝ)) ω) ∂μ =
      (1 + δ) * Theta (msc z) S a b * ∫ ω, (eT S z a b ω) ^ (n + 1) ∂μ +
        (w + 16) * δ * ∫ ω, (eT S z a b ω) ^ (n + 1) * eY S z a b ω ∂μ +
          ∫ ω, Gdᶜ.indicator (fun _ => (4 : ℝ)) ω ∂μ := by
    rw [integral_add iAB iind, integral_add iA iB, integral_const_mul, integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (hmono.trans ?_)
  rw [hsum]
  have hc : 0 ≤ (w + 16) * δ := by positivity
  have := mul_le_mul_of_nonneg_left hXY hc
  nlinarith

private theorem eta1_master (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (n : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u v, ∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S) ≤ M * (B u v) ^ (n + 2)) (a b : ι) :
    ∫ ω, (eT S z a b ω) ^ (n + 2) ∂(gaussLaw S) ≤
      (B a b) ^ (n + 2) * (eKap δ δs κ₁ ^ (n + 2) + 2 * eGam n δ w δs κ₂ * M) + 64 * ε := by
  have := isProbabilityMeasure_gaussLaw S
  have hz := h.hz0
  set μ := gaussLaw S with hμ
  have hΘb := h.hΘ0 a b
  have hΘ1 : Theta (msc z) S a b ≤ 1 :=
    (Finset.single_le_sum (f := fun x => Theta (msc z) S a x) (fun x _ => h.hΘ0 a x)
      (Finset.mem_univ b)).trans (h.hΘ1 a)
  have hδ0 := h.hδ0
  have hδs0 := h.hδs0
  have hw := h.hw
  have hBpos := h.hB a b
  have hε0 := h.hε0
  set E1 := ∫ ω, (eT S z a b ω) ^ (n + 1) ∂μ with hE1
  set E2 := ∫ ω, (eT S z a b ω) ^ (n + 2) ∂μ with hE2
  have hX0 : ∀ k : ℕ, ∀ ω, 0 ≤ (eT S z a b ω) ^ k := fun k ω => pow_nonneg (h.T0 ω a b) _
  have hX1 : ∀ k : ℕ, ∀ ω, (eT S z a b ω) ^ k ≤ 1 := fun k ω =>
    pow_le_one₀ (h.T0 ω a b) (h.T1 ω a b)
  have hmX : ∀ k : ℕ, Measurable (fun ω : Sample ι => (eT S z a b ω) ^ k) :=
    fun k => (eta1_eT_meas S z hz a b).pow_const _
  have iXk : ∀ k : ℕ, Integrable (fun ω : Sample ι => (eT S z a b ω) ^ k) μ := fun k =>
    eta1_integrable_real S (hmX k) 1 fun ω => by rw [abs_of_nonneg (hX0 k ω)]; exact hX1 k ω
  -- (I) the identity
  have hE2eq : E2 = (∫ ω, ((((eT S z a b ω) ^ (n + 2) : ℝ)) : ℂ) ∂μ).re := by
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hkey : ∀ ω, ((((eT S z a b ω) ^ (n + 2) : ℝ)) : ℂ) =
      eXc S z a b (n + 1) ω * (eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω) +
        eXc S z a b (n + 1) ω * eV S z a b ω := by
    intro ω
    have := eta1_identity' S z h.hS h.hnn h.hrow hz a b ω
    unfold eXc
    push_cast
    rw [← mul_add, ← this]
    ring
  have hRbdd : BddMeas (fun ω => eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω) :=
    eta1_bdd_of_test (eta1_testFn_add (eta1_testFn_add (eta1_eLead_test S z hz a b)
      (eta1_eA1_test S z hz a b)) (eta1_eA2_test S z hz a b))
  have hXbdd := eta1_eXc_bdd S z hz a b (n + 1)
  have i1 := eta1_integrable_bdd S (eta1_bdd_mul hXbdd hRbdd)
  have i2 := eta1_integrable_bdd S (eta1_bdd_mul hXbdd (eta1_eV_bdd h a b))
  have hI : E2 ≤ ‖∫ ω, eXc S z a b (n + 1) ω * (eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω)
        ∂μ‖ + ‖∫ ω, eXc S z a b (n + 1) ω * eV S z a b ω ∂μ‖ := by
    rw [hE2eq]
    have : ∫ ω, ((((eT S z a b ω) ^ (n + 2) : ℝ)) : ℂ) ∂μ =
        ∫ ω, eXc S z a b (n + 1) ω * (eLead S z a b ω + eA1 S z a b ω + eA2 S z a b ω) ∂μ +
          ∫ ω, eXc S z a b (n + 1) ω * eV S z a b ω ∂μ := by
      rw [← integral_add i1 i2]
      exact integral_congr_ae (Filter.Eventually.of_forall hkey)
    rw [this]
    exact (Complex.re_le_norm _).trans (norm_add_le _ _)
  have hII := eta1_R_bound h n M hM0 hM a b
  have hIII := eta1_Vint_bound h n M hM0 hM a b
  -- (IV) Young
  set cb : ℝ := 8 * δ + 2 * δs + 2 * δ ^ 2 with hcb
  have hcb0 : 0 ≤ cb := by positivity
  set K' : ℝ := Theta (msc z) S a b * (1 + δ + cb) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hyoung : K' * E1 ≤ E2 / 2 + 2 ^ (n + 1) * K' ^ (n + 2) := by
    have hint : Integrable (fun ω : Sample ι => (eT S z a b ω) ^ (n + 2) / 2 +
        2 ^ (n + 1) * K' ^ (n + 2)) μ := ((iXk (n + 2)).div_const 2).add (integrable_const _)
    have := integral_mono ((iXk (n + 1)).const_mul K') hint (fun ω => by
      exact eta1_young n hK'0 (h.T0 ω a b))
    rw [integral_const_mul] at this
    rw [integral_add ((iXk (n + 2)).div_const 2) (integrable_const _), integral_div,
      integral_const, probReal_univ] at this
    simpa [hE2, hE1] using this
  -- combine
  have hK'B : K' ≤ (1 + δ + cb) * κ₁ * B a b := by
    have := h.hΘ2 a b
    have h1 : 0 ≤ 1 + δ + cb := by positivity
    calc K' = (1 + δ + cb) * Theta (msc z) S a b := by simp only [hK']; ring
      _ ≤ (1 + δ + cb) * (κ₁ * B a b) := mul_le_mul_of_nonneg_left this h1
      _ = _ := by ring
  have hK'pow : K' ^ (n + 2) ≤ ((1 + δ + cb) * κ₁ * B a b) ^ (n + 2) :=
    pow_le_pow_left₀ hK'0 hK'B _
  have hE1' : (1 + δ) * Theta (msc z) S a b * E1 + Theta (msc z) S a b * (cb * E1) = K' * E1 := by
    simp only [hK']; ring
  have hc20 : Theta (msc z) S a b * (20 * ε) ≤ 20 * ε := by
    have : 0 ≤ 20 * ε := by positivity
    nlinarith
  have hγ : eGam n δ w δs κ₂ * M * (B a b) ^ (n + 2) =
      (2 * (w + 16) * δ * M * ((B a b) ^ (n + 2) * (1 + κ₂)) +
        4 * (18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs)) * M *
          ((B a b) ^ (n + 2) * (1 + κ₂))) := by
    unfold eGam; ring
  have hmain : E2 / 2 ≤ 2 ^ (n + 1) * K' ^ (n + 2) + eGam n δ w δs κ₂ * M * (B a b) ^ (n + 2) +
      32 * ε := by
    have h1 : E2 ≤ (1 + δ) * Theta (msc z) S a b * E1 + 2 * (w + 16) * δ * M *
          ((B a b) ^ (n + 2) * (1 + κ₂)) + 4 * ε +
        (4 * (18 * ((n : ℝ) + 1) * w ^ 2 * (320 * Real.sqrt (δs + δ ^ 2) + 2 * δs)) * M *
          ((B a b) ^ (n + 2) * (1 + κ₂)) + 8 * ε +
        Theta (msc z) S a b * (cb * E1 + 20 * ε)) := by
      have := hI.trans (add_le_add hII hIII)
      simp only [hcb] at this ⊢
      linarith
    have e2 : Theta (msc z) S a b * (cb * E1 + 20 * ε) =
        Theta (msc z) S a b * (cb * E1) + Theta (msc z) S a b * (20 * ε) := by ring
    rw [e2] at h1
    linarith
  have hKfin : 2 ^ (n + 2) * K' ^ (n + 2) ≤ (B a b) ^ (n + 2) * eKap δ δs κ₁ ^ (n + 2) := by
    calc 2 ^ (n + 2) * K' ^ (n + 2) ≤ 2 ^ (n + 2) * ((1 + δ + cb) * κ₁ * B a b) ^ (n + 2) :=
          mul_le_mul_of_nonneg_left hK'pow (by positivity)
      _ = (B a b) ^ (n + 2) * eKap δ δs κ₁ ^ (n + 2) := by
          unfold eKap; simp only [hcb]; rw [← mul_pow]; rw [← mul_pow]; ring
  have hpow : 2 ^ (n + 2) * K' ^ (n + 2) = 2 * (2 ^ (n + 1) * K' ^ (n + 2)) := by ring
  nlinarith

/-- The closed moment bound: if `2 Γ ≤ 1/2` and `64 ε ≤ B^{n+2}`, then
`E T_{ab}^{n+2} ≤ 2 (K^{n+2} + 1) B_{ab}^{n+2}` for all `a, b`. -/
private theorem eta1_moment_closed [Nonempty ι] (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (n : ℕ)
    (hγ : 2 * eGam n δ w δs κ₂ ≤ 1 / 2) (hεB : ∀ a b, 64 * ε ≤ (B a b) ^ (n + 2)) (a b : ι) :
    ∫ ω, (eT S z a b ω) ^ (n + 2) ∂(gaussLaw S) ≤
      2 * (eKap δ δs κ₁ ^ (n + 2) + 1) * (B a b) ^ (n + 2) := by
  have := isProbabilityMeasure_gaussLaw S
  classical
  set r : ι × ι → ℝ := fun p => (∫ ω, (eT S z p.1 p.2 ω) ^ (n + 2) ∂(gaussLaw S)) /
    (B p.1 p.2) ^ (n + 2) with hr
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_max_image (Finset.univ : Finset (ι × ι)) r
    ⟨(Classical.arbitrary ι, Classical.arbitrary ι), Finset.mem_univ _⟩
  set M := r p₀ with hMdef
  have hBp : ∀ u v, 0 < (B u v) ^ (n + 2) := fun u v => pow_pos (h.hB u v) _
  have hM0 : 0 ≤ M := by
    refine div_nonneg (integral_nonneg fun ω => pow_nonneg (h.T0 ω _ _) _) (hBp _ _).le
  have hM : ∀ u v, ∫ ω, (eT S z u v ω) ^ (n + 2) ∂(gaussLaw S) ≤ M * (B u v) ^ (n + 2) := by
    intro u v
    have := hp₀ (u, v) (Finset.mem_univ _)
    simp only [hr] at this
    rw [div_le_iff₀ (hBp u v)] at this
    exact this
  have hmaster := eta1_master h n M hM0 hM p₀.1 p₀.2
  have hMeq : ∫ ω, (eT S z p₀.1 p₀.2 ω) ^ (n + 2) ∂(gaussLaw S) = M * (B p₀.1 p₀.2) ^ (n + 2) := by
    simp only [hMdef, hr]
    field_simp [(hBp p₀.1 p₀.2).ne']
  rw [hMeq] at hmaster
  have hB0 := hBp p₀.1 p₀.2
  have hε := hεB p₀.1 p₀.2
  have hε1 : 64 * ε ≤ (B p₀.1 p₀.2) ^ (n + 2) * 1 := by linarith
  have hK0 : 0 ≤ eKap δ δs κ₁ ^ (n + 2) := by
    have h1 := h.hδ0
    have h2 := h.hδs0
    have h3 := h.hκ1
    unfold eKap
    positivity
  have hM2 : M ≤ 2 * (eKap δ δs κ₁ ^ (n + 2) + 1) := by
    have h1 : M * (B p₀.1 p₀.2) ^ (n + 2) ≤ (B p₀.1 p₀.2) ^ (n + 2) *
        (eKap δ δs κ₁ ^ (n + 2) + 2 * eGam n δ w δs κ₂ * M) + (B p₀.1 p₀.2) ^ (n + 2) * 1 := by
      linarith
    have h2 : M ≤ eKap δ δs κ₁ ^ (n + 2) + 2 * eGam n δ w δs κ₂ * M + 1 := by
      have : (B p₀.1 p₀.2) ^ (n + 2) * M ≤ (B p₀.1 p₀.2) ^ (n + 2) *
          (eKap δ δs κ₁ ^ (n + 2) + 2 * eGam n δ w δs κ₂ * M + 1) := by nlinarith
      exact le_of_mul_le_mul_left this hB0
    have h3 : 2 * eGam n δ w δs κ₂ * M ≤ 1 / 2 * M := mul_le_mul_of_nonneg_right hγ hM0
    linarith
  calc ∫ ω, (eT S z a b ω) ^ (n + 2) ∂(gaussLaw S) ≤ M * (B a b) ^ (n + 2) := hM a b
    _ ≤ 2 * (eKap δ δs κ₁ ^ (n + 2) + 1) * (B a b) ^ (n + 2) :=
        mul_le_mul_of_nonneg_right hM2 (hBp a b).le

end Master2


section Kernel

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The entries of `S^k` are nonnegative. -/
private theorem eta1_pow_nonneg (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y) (k : ℕ) :
    ∀ x y, 0 ≤ (S ^ k) x y := by
  induction k with
  | zero => intro x y; by_cases h : x = y <;> simp [h]
  | succ k ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun α _ => mul_nonneg (ih x α) (hS0 α y)

/-- `Θ` has nonnegative entries. -/
private theorem eta1_Theta_nonneg (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : ∀ x, ∑ y, S x y = 1)
    (m : ℂ) (hm : ‖m‖ < 1) (x y : ι) : 0 ≤ Theta m S x y := by
  have h := Theta_hasSum S hS0 hS1 m hm
  have h2 : HasSum (fun k : ℕ => (‖m‖ ^ (2 * (k + 1)) • S ^ (k + 1)) x y) (Theta m S x y) :=
    Pi.hasSum.mp (Pi.hasSum.mp h x) y
  refine h2.nonneg fun k => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (eta1_pow_nonneg S hS0 (k + 1) x y)

/-- `B_{xy}` as a natural power. -/
private theorem eta1_bB_pow {d L : ℕ} (hd : 2 ≤ d) (W : ℕ) (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y = (W : ℝ) ^ (-2 : ℝ) / ((zdistInf d L (x - y) : ℝ) + W) ^ (d - 2) := by
  have hρ : 0 < (zdistInf d L (x - y) : ℝ) + W := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  unfold bB
  have : (2 : ℝ) - d = -((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd]; push_cast; ring
  rw [this, Real.rpow_neg hρ.le, Real.rpow_natCast, div_eq_mul_inv]

private theorem eta1_bB_pos {d L : ℕ} (W : ℕ) (hW : 1 ≤ W) (x y : Zd d L) : 0 < bB d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold bB; positivity

private theorem eta1_bB_ratio {d L : ℕ} (hd : 2 ≤ d) (W : ℕ) (hW : 1 ≤ W) (a b x : Zd d L) :
    bB d L W x b / bB d L W a b =
      (((zdistInf d L (a - b) : ℝ) + W) / ((zdistInf d L (x - b) : ℝ) + W)) ^ (d - 2) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1 : 0 < (zdistInf d L (a - b) : ℝ) + W := by positivity
  have h2 : 0 < (zdistInf d L (x - b) : ℝ) + W := by positivity
  rw [eta1_bB_pow hd W hW, eta1_bB_pow hd W hW, div_pow]
  have h3 : (0 : ℝ) < (W : ℝ) ^ (-2 : ℝ) := by positivity
  field_simp

private theorem eta1_ratio_near {d L : ℕ} [NeZero L] (hd2 : 2 ≤ d) (W : ℕ) (hW : 1 ≤ W) {τ : ℝ} (hτ : 0 ≤ τ)
    (a b x : Zd d L) (hnear : (zdistInf d L (a - x) : ℝ) ≤ (W : ℝ) ^ (1 + τ)) :
    (bB d L W x b / bB d L W a b) ^ 2 ≤ (2 * (W : ℝ) ^ τ) ^ (2 * (d - 2)) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hr := eta1_bB_ratio hd2 W hW a b x
  have hρxb : (W : ℝ) ≤ (zdistInf d L (x - b) : ℝ) + W := by
    have := (Nat.cast_nonneg (zdistInf d L (x - b)) : (0 : ℝ) ≤ _); linarith
  have hρxb0 : 0 < (zdistInf d L (x - b) : ℝ) + W := by linarith
  have htri : (zdistInf d L (a - b) : ℝ) ≤ (zdistInf d L (a - x) : ℝ) +
      (zdistInf d L (x - b) : ℝ) := by
    have := zdistInf_add_le d L (a - x) (x - b)
    rw [sub_add_sub_cancel] at this
    exact_mod_cast this
  have hWpow : (W : ℝ) ^ (1 + τ) = (W : ℝ) * (W : ℝ) ^ τ := by
    rw [Real.rpow_add hW0, Real.rpow_one]
  have hWτ : (1 : ℝ) ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ
  have h2 : (zdistInf d L (a - x) : ℝ) ≤ ((zdistInf d L (x - b) : ℝ) + W) * (W : ℝ) ^ τ := by
    calc (zdistInf d L (a - x) : ℝ) ≤ (W : ℝ) * (W : ℝ) ^ τ := hWpow ▸ hnear
      _ ≤ ((zdistInf d L (x - b) : ℝ) + W) * (W : ℝ) ^ τ :=
          mul_le_mul_of_nonneg_right hρxb (by linarith)
  have h1 : (zdistInf d L (a - b) : ℝ) + W ≤ 2 * (W : ℝ) ^ τ *
      ((zdistInf d L (x - b) : ℝ) + W) := by
    have h5 : ((zdistInf d L (x - b) : ℝ) + W) ≤ ((zdistInf d L (x - b) : ℝ) + W) * (W : ℝ) ^ τ := by
      nlinarith
    nlinarith
  have h3 : ((zdistInf d L (a - b) : ℝ) + W) / ((zdistInf d L (x - b) : ℝ) + W) ≤
      2 * (W : ℝ) ^ τ := by
    rw [div_le_iff₀ hρxb0]; linarith
  rw [hr]
  have h4a : (((zdistInf d L (a - b) : ℝ) + W) / ((zdistInf d L (x - b) : ℝ) + W)) ^ (d - 2) ≤
      (2 * (W : ℝ) ^ τ) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) h3 _
  calc ((((zdistInf d L (a - b) : ℝ) + W) / ((zdistInf d L (x - b) : ℝ) + W)) ^ (d - 2)) ^ 2
      ≤ ((2 * (W : ℝ) ^ τ) ^ (d - 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h4a 2
    _ = (2 * (W : ℝ) ^ τ) ^ (2 * (d - 2)) := by rw [← pow_mul, Nat.mul_comm]

private theorem eta1_ratio_far {d L : ℕ} [NeZero L] (hd2 : 2 ≤ d) (W : ℕ) (hW : 1 ≤ W) (hWL : (W : ℝ) ≤ L)
    (a b x : Zd d L) :
    (bB d L W x b / bB d L W a b) ^ 2 ≤ (2 * (L : ℝ)) ^ (2 * (d - 2)) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hr := eta1_bB_ratio hd2 W hW a b x
  have hρxb : (W : ℝ) ≤ (zdistInf d L (x - b) : ℝ) + W := by
    have := (Nat.cast_nonneg (zdistInf d L (x - b)) : (0 : ℝ) ≤ _); linarith
  have hρxb0 : 0 < (zdistInf d L (x - b) : ℝ) + W := by linarith
  have hρle : (zdistInf d L (a - b) : ℝ) + W ≤ 2 * L := by
    have := zdistInf_le_half d L (a - b)
    have h2 : (zdistInf d L (a - b) : ℝ) ≤ L := by
      have : zdistInf d L (a - b) ≤ L := this.trans (Nat.div_le_self _ _)
      exact_mod_cast this
    linarith
  have h3 : ((zdistInf d L (a - b) : ℝ) + W) / ((zdistInf d L (x - b) : ℝ) + W) ≤ 2 * L := by
    rw [div_le_iff₀ hρxb0]
    have : 0 ≤ (2 * (L : ℝ)) := by linarith
    nlinarith
  rw [hr]
  have h4a : (((zdistInf d L (a - b) : ℝ) + W) / ((zdistInf d L (x - b) : ℝ) + W)) ^ (d - 2) ≤
      (2 * (L : ℝ)) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) h3 _
  calc ((((zdistInf d L (a - b) : ℝ) + W) / ((zdistInf d L (x - b) : ℝ) + W)) ^ (d - 2)) ^ 2
      ≤ ((2 * (L : ℝ)) ^ (d - 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h4a 2
    _ = (2 * (L : ℝ)) ^ (2 * (d - 2)) := by rw [← pow_mul, Nat.mul_comm]

private theorem eta1_kernel (d : ℕ) (hd : 3 ≤ d) (P : Profile d) (c₀ c₁ κ ε₁ τ : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε₁ : 0 < ε₁) (hτ : 0 < τ) :
    ∃ W₀ Cs : ℝ, 0 ≤ Cs ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ((Smat P.ψ W L).IsSymm ∧ (∀ x y, 0 ≤ Smat P.ψ W L x y) ∧
        (∀ x, ∑ y, Smat P.ψ W L x y = 1) ∧ (∀ x y, Smat P.ψ W L x y ≤ Cs / (W : ℝ) ^ d)) ∧
      ∀ z ∈ specDom κ ε₁ W L, z.im = 1 →
        (∀ a x, 0 ≤ Theta (msc z) (Smat P.ψ W L) a x) ∧
        (∀ a, ∑ x, Theta (msc z) (Smat P.ψ W L) a x ≤ 1) ∧
        (∀ a b, Theta (msc z) (Smat P.ψ W L) a b ≤ 2 * (W : ℝ) ^ τ * bB d L W a b) ∧
        (∀ a b, ∑ x, Theta (msc z) (Smat P.ψ W L) a x * (bB d L W x b / bB d L W a b) ^ 2 ≤
          (2 * (W : ℝ) ^ τ) ^ (2 * (d - 2)) + 1) := by
  obtain ⟨W₁, hsn⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  obtain ⟨W₃, hsk⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨C, hC⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨Cs, hCs⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set D : ℝ := 3 * d / c₁ + d with hD
  have hD0 : 0 < D := by positivity
  obtain ⟨W₄, hth⟩ := Theta_decay d hd c₀ c₁ hc₀ hc₁ P.ψ P.cψ (profileShape_of_profile d P) C κ ε₁ τ
    D hκ hε₁ hτ hD0
  refine ⟨max (max (max W₁ W₂) (max W₃ W₄)) 4, max Cs 0, le_max_right _ _, ?_⟩
  intro W L _ hadm hW
  have hW1 : W₁ ≤ (W : ℝ) := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hW
  have hW2 : W₂ ≤ (W : ℝ) := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hW
  have hW3 : W₃ ≤ (W : ℝ) := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hW
  have hW4 : W₄ ≤ (W : ℝ) := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hW
  have hW4' : (4 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
  have hW1' : (1 : ℝ) ≤ W := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  obtain ⟨hsymm, hnn⟩ := hsn W L hadm hW1
  have hds' := hds W L hadm hW2
  have hrow : ∀ x, ∑ y, Smat P.ψ W L x y = 1 := fun x => sum_row_of_mem_doublyStochastic hds' x
  have hsk' := hsk W L hadm hW3
  refine ⟨⟨hsymm, hnn, hrow, fun x y => ?_⟩, ?_⟩
  · have h := hCs W L hadm (x - y)
    simp only [pow_zero, one_mul] at h
    have := hnn x y
    have e : Smat P.ψ W L x y = fWL P.ψ W L (x - y) := rfl
    rw [e] at this ⊢
    exact (le_abs_self _).trans (h.trans (div_le_div_of_nonneg_right (le_max_left _ _)
      (by positivity)))
  intro z hz hzim
  have hz0 : 0 < z.im := by rw [hzim]; exact one_pos
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz0
  have hΘ0 := eta1_Theta_nonneg (Smat P.ψ W L) hnn hrow (msc z) hm1
  have hrs : ∀ a, ∑ x, Theta (msc z) (Smat P.ψ W L) a x ≤ 1 := by
    intro a
    rw [Theta_rowSum (Smat P.ψ W L) hsk' hrow z hz0 a, hzim, div_one]
    exact (Complex.im_le_norm _).trans hm1.le
  have hdec := hth W L hadm hW4 (Smat P.ψ W L) hsk' (hC W L hadm) z hz
  have hdec' : ∀ a x, Theta (msc z) (Smat P.ψ W L) a x ≤
      (if (zdistInf d L (a - x) : ℝ) ≤ (W : ℝ) ^ (1 + τ) then (W : ℝ) ^ τ * bB d L W a x else 0) +
        ((zdistInf d L (a - x) : ℝ) + W) ^ (-D) := by
    intro a x
    have := (le_abs_self _).trans (hdec a x)
    unfold thetaBound at this
    rw [hzim, Real.one_rpow, one_mul] at this
    exact this
  refine ⟨hΘ0, hrs, ?_, ?_⟩
  · -- the bound of `Θ_{ab}`
    intro a b
    have h1 := hdec' a b
    have hρ : (W : ℝ) ≤ (zdistInf d L (a - b) : ℝ) + W := by
      have := (Nat.cast_nonneg (zdistInf d L (a - b)) : (0 : ℝ) ≤ _); linarith
    have hρ0 : 0 < (zdistInf d L (a - b) : ℝ) + W := by linarith
    have htail : ((zdistInf d L (a - b) : ℝ) + W) ^ (-D) ≤ bB d L W a b := by
      unfold bB
      have hρ1 : (1 : ℝ) ≤ (zdistInf d L (a - b) : ℝ) + W := by linarith
      have hDd : (d : ℝ) ≤ D := by
        rw [hD]; have : 0 ≤ 3 * (d : ℝ) / c₁ := by positivity
        linarith
      calc ((zdistInf d L (a - b) : ℝ) + W) ^ (-D)
          = ((zdistInf d L (a - b) : ℝ) + W) ^ (-2 : ℝ) *
            ((zdistInf d L (a - b) : ℝ) + W) ^ (2 - D) := by
            rw [← Real.rpow_add hρ0]; congr 1; ring
        _ ≤ (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (a - b) : ℝ) + W) ^ (2 - (d : ℝ)) := by
            refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hW0 hρ (by norm_num))
              (Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)) (by positivity) (by positivity)
    have hWτ : (1 : ℝ) ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1' hτ.le
    have hB := eta1_bB_pos (d := d) (L := L) W hWn a b
    have hite : (if (zdistInf d L (a - b) : ℝ) ≤ (W : ℝ) ^ (1 + τ) then
        (W : ℝ) ^ τ * bB d L W a b else 0) ≤ (W : ℝ) ^ τ * bB d L W a b := by
      split_ifs
      · exact le_rfl
      · positivity
    nlinarith
  · intro a b
    have hd2 : 2 ≤ d := by omega
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hLW : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁) := by
      have h1 := Real.rpow_le_rpow (by positivity) hadm.1 (by positivity : (0 : ℝ) ≤ 1 / c₁)
      rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hc₁.ne', Real.rpow_one] at h1
    have hWL : (W : ℝ) ≤ L := by
      have h1 := hadm.2
      have h2 : (L : ℝ) ^ (1 - c₀) ≤ (L : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      rw [Real.rpow_one] at h2
      exact h1.trans h2
    set A : ℝ := (2 * (W : ℝ) ^ τ) ^ (2 * (d - 2)) with hA
    set Tf : ℝ := ((W : ℝ) ^ (1 + τ)) ^ (-D) * (2 * (L : ℝ)) ^ (2 * (d - 2)) with hTf
    have hWτ : (1 : ℝ) ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1' hτ.le
    have hWτ1 : (0 : ℝ) < (W : ℝ) ^ (1 + τ) := by positivity
    have hTf0 : 0 ≤ Tf := by positivity
    have hA0 : 0 ≤ A := by positivity
    have hpt : ∀ x : Zd d L, Theta (msc z) (Smat P.ψ W L) a x *
        (bB d L W x b / bB d L W a b) ^ 2 ≤ A * Theta (msc z) (Smat P.ψ W L) a x + Tf := by
      intro x
      have hr := eta1_bB_ratio hd2 W hWn a b x
      have hΘx := hΘ0 a x
      by_cases hnear : (zdistInf d L (a - x) : ℝ) ≤ (W : ℝ) ^ (1 + τ)
      · have h4 := eta1_ratio_near hd2 W hWn hτ.le a b x hnear
        have := mul_le_mul_of_nonneg_left h4 hΘx
        nlinarith
      · have hΘle : Theta (msc z) (Smat P.ψ W L) a x ≤ ((W : ℝ) ^ (1 + τ)) ^ (-D) := by
          have h1 := hdec' a x
          rw [ite_eq_right hnear, zero_add] at h1
          refine h1.trans ?_
          have : (W : ℝ) ^ (1 + τ) ≤ (zdistInf d L (a - x) : ℝ) + W := by
            have := (not_le.mp hnear)
            have := (Nat.cast_nonneg (W) : (0 : ℝ) ≤ W)
            linarith
          exact Real.rpow_le_rpow_of_nonpos hWτ1 this (by linarith [hD0])
        have h4 := eta1_ratio_far hd2 W hWn hWL a b x
        have h5 : Theta (msc z) (Smat P.ψ W L) a x * (bB d L W x b / bB d L W a b) ^ 2 ≤ Tf := by
          rw [hTf]
          exact mul_le_mul hΘle h4 (by positivity) (by positivity)
        have : 0 ≤ A * Theta (msc z) (Smat P.ψ W L) a x := mul_nonneg hA0 hΘx
        linarith
    have hsum : ∑ x, Theta (msc z) (Smat P.ψ W L) a x * (bB d L W x b / bB d L W a b) ^ 2 ≤
        A * ∑ x, Theta (msc z) (Smat P.ψ W L) a x + (L : ℝ) ^ d * Tf := by
      calc _ ≤ ∑ x : Zd d L, (A * Theta (msc z) (Smat P.ψ W L) a x + Tf) :=
            Finset.sum_le_sum fun x _ => hpt x
        _ = A * ∑ x, Theta (msc z) (Smat P.ψ W L) a x + (L : ℝ) ^ d * Tf := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              card_Zd, nsmul_eq_mul]
            push_cast; ring
    have hLT : (L : ℝ) ^ d * Tf ≤ 1 := by
      have e1 : ((W : ℝ) ^ (1 + τ)) ^ (-D) ≤ (W : ℝ) ^ (-D) := by
        rw [← Real.rpow_mul hW0.le]
        exact Real.rpow_le_rpow_of_exponent_le hW1' (by nlinarith [hD0])
      have e2 : (L : ℝ) ^ d * (2 * (L : ℝ)) ^ (2 * (d - 2)) ≤ 4 ^ d * (L : ℝ) ^ (3 * d) := by
        have : (L : ℝ) ^ d * (2 * (L : ℝ)) ^ (2 * (d - 2)) =
            2 ^ (2 * (d - 2)) * (L : ℝ) ^ (d + 2 * (d - 2)) := by
          rw [mul_pow, pow_add]; ring
        rw [this]
        have h2 : (2 : ℝ) ^ (2 * (d - 2)) ≤ 4 ^ d := by
          calc (2 : ℝ) ^ (2 * (d - 2)) = 4 ^ (d - 2) := by rw [pow_mul]; norm_num
            _ ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
        have h3 : (L : ℝ) ^ (d + 2 * (d - 2)) ≤ (L : ℝ) ^ (3 * d) :=
          pow_le_pow_right₀ hL1 (by omega)
        exact mul_le_mul h2 h3 (by positivity) (by positivity)
      have e3 : (L : ℝ) ^ (3 * d) ≤ (W : ℝ) ^ (3 * (d : ℝ) / c₁) := by
        calc (L : ℝ) ^ (3 * d) ≤ ((W : ℝ) ^ (1 / c₁)) ^ (3 * d) :=
              pow_le_pow_left₀ (by positivity) hLW _
          _ = (W : ℝ) ^ (3 * (d : ℝ) / c₁) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
              congr 1; push_cast; ring
      have e4 : (W : ℝ) ^ (3 * (d : ℝ) / c₁) * (W : ℝ) ^ (-D) = (W : ℝ) ^ (-(d : ℝ)) := by
        rw [← Real.rpow_add hW0]; congr 1; rw [hD]; ring
      have e5 : (4 : ℝ) ^ d * (W : ℝ) ^ (-(d : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg hW0.le, Real.rpow_natCast, ← div_eq_mul_inv, ← div_pow]
        exact pow_le_one₀ (by positivity) ((div_le_one hW0).2 hW4')
      calc (L : ℝ) ^ d * Tf = ((W : ℝ) ^ (1 + τ)) ^ (-D) *
            ((L : ℝ) ^ d * (2 * (L : ℝ)) ^ (2 * (d - 2))) := by rw [hTf]; ring
        _ ≤ (W : ℝ) ^ (-D) * (4 ^ d * (L : ℝ) ^ (3 * d)) :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
        _ ≤ (W : ℝ) ^ (-D) * (4 ^ d * (W : ℝ) ^ (3 * (d : ℝ) / c₁)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 (by positivity)) (by positivity)
        _ = 4 ^ d * ((W : ℝ) ^ (3 * (d : ℝ) / c₁) * (W : ℝ) ^ (-D)) := by ring
        _ ≤ 1 := by rw [e4]; exact e5
    have := mul_le_mul_of_nonneg_left (hrs a) hA0
    linarith

end Kernel



section Tail

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The good event: the entries of `G - m` are at most `δ`, and `|G_{kl}|² ≤ w T_{kl}` off the
diagonal. -/
private def eGd (S : Matrix ι ι ℝ) (z : ℂ) (δ w : ℝ) : Set (Sample ι) :=
  {ω | (∀ k l, ‖entryErr (eG z ω) (msc z) k l‖ ≤ δ) ∧
    ∀ k l, k ≠ l → ‖eG z ω k l‖ ^ 2 ≤ w * eT S z k l ω}

private theorem eta1_eGd_meas (S : Matrix ι ι ℝ) (z : ℂ) (hz : 0 < z.im) (δ w : ℝ) :
    MeasurableSet (eGd S z δ w) := by
  have hEnt : ∀ k l : ι, Measurable (fun ω : Sample ι => eG z ω k l) := fun k l =>
    (eta1_bdd_of_test (eta1_eG_test z hz k l)).1
  have h1 : ∀ k l : ι, MeasurableSet {ω : Sample ι | ‖entryErr (eG z ω) (msc z) k l‖ ≤ δ} := by
    intro k l
    have : Measurable (fun ω : Sample ι => ‖entryErr (eG z ω) (msc z) k l‖) := by
      unfold entryErr
      exact ((hEnt k l).sub measurable_const).norm
    exact measurableSet_le this measurable_const
  have h2 : ∀ k l : ι, MeasurableSet {ω : Sample ι | k ≠ l → ‖eG z ω k l‖ ^ 2 ≤ w * eT S z k l ω} := by
    intro k l
    by_cases hkl : k = l
    · simp [hkl]
    · simp only [ne_eq, hkl, not_false_eq_true, forall_true_left]
      exact measurableSet_le ((hEnt k l).norm.pow_const 2)
        ((eta1_eT_meas S z hz k l).const_mul w)
  have : eGd S z δ w = (⋂ k, ⋂ l, {ω | ‖entryErr (eG z ω) (msc z) k l‖ ≤ δ}) ∩
      ⋂ k, ⋂ l, {ω | k ≠ l → ‖eG z ω k l‖ ^ 2 ≤ w * eT S z k l ω} := by
    ext ω; simp [eGd]
  rw [this]
  exact (MeasurableSet.iInter fun k => MeasurableSet.iInter fun l => h1 k l).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun l => h2 k l)

variable {S : Matrix ι ι ℝ} {z : ℂ} {B : ι → ι → ℝ} {δ w δs κ₁ κ₂ ε : ℝ} {Gd : Set (Sample ι)}

/-- Markov's inequality for the `q`-th moment of `T_{xy}`. -/
private theorem Eta1Hyp.markov (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (x y : ι) (q : ℕ) (c : ℝ)
    (hc : 0 < c) (Mq : ℝ) (hMq : ∫ ω, (eT S z x y ω) ^ q ∂(gaussLaw S) ≤ Mq) :
    gaussLaw S {ω | c < eT S z x y ω} ≤ ENNReal.ofReal (Mq / c ^ q) := by
  have := isProbabilityMeasure_gaussLaw S
  have hmX : Measurable (fun ω : Sample ι => (eT S z x y ω) ^ q) :=
    (eta1_eT_meas S z h.hz0 x y).pow_const _
  have hint : Integrable (fun ω : Sample ι => (eT S z x y ω) ^ q) (gaussLaw S) :=
    eta1_integrable_real S hmX 1 fun ω => by
      rw [abs_of_nonneg (pow_nonneg (h.T0 ω x y) _)]
      exact pow_le_one₀ (h.T0 ω x y) (h.T1 ω x y)
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := gaussLaw S)
    (Filter.Eventually.of_forall fun ω => pow_nonneg (h.T0 ω x y) q) hint (c ^ q)
  have hsub : {ω | c < eT S z x y ω} ⊆ {ω | c ^ q ≤ (eT S z x y ω) ^ q} := fun ω hω =>
    pow_le_pow_left₀ hc.le (le_of_lt hω) q
  have hcq : 0 < c ^ q := pow_pos hc q
  have h1 : (gaussLaw S).real {ω | c < eT S z x y ω} ≤ Mq / c ^ q := by
    rw [le_div_iff₀ hcq, mul_comm]
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hcq.le).trans (hmk.trans hMq)
  calc gaussLaw S {ω | c < eT S z x y ω}
      = ENNReal.ofReal ((gaussLaw S).real {ω | c < eT S z x y ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Mq / c ^ q) := ENNReal.ofReal_le_ofReal h1

private theorem eta1_tail_entry [Nonempty ι] (h : Eta1Hyp S z B δ w δs κ₁ κ₂ ε Gd) (n : ℕ)
    (hγ : 2 * eGam n δ w δs κ₂ ≤ 1 / 2) (hεB : ∀ a b, 64 * ε ≤ (B a b) ^ (n + 2))
    (Θ Θ' : ℝ) (hΘ' : 0 < Θ') (hwΘ : w * Θ' ≤ Θ) (hδΘ : ∀ x, δ ^ 2 ≤ Θ * B x x)
    (hGd : Gd = eGd S z δ w) (x y : ι) :
    gaussLaw S {ω | Θ * B x y < ‖entryErr (eG z ω) (msc z) x y‖ ^ 2} ≤
      ENNReal.ofReal ε + ENNReal.ofReal (2 * (eKap δ δs κ₁ ^ (n + 2) + 1) / Θ' ^ (n + 2)) := by
  have := isProbabilityMeasure_gaussLaw S
  have hBxy := h.hB x y
  by_cases hxy : x = y
  · subst hxy
    have hsub : {ω | Θ * B x x < ‖entryErr (eG z ω) (msc z) x x‖ ^ 2} ⊆ Gdᶜ := by
      intro ω hω hGdω
      have h1 : ‖entryErr (eG z ω) (msc z) x x‖ ≤ δ := by rw [hGd] at hGdω; exact hGdω.1 x x
      have h0 := norm_nonneg (entryErr (eG z ω) (msc z) x x)
      have : ‖entryErr (eG z ω) (msc z) x x‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ h0 h1 2
      have h5 := hδΘ x
      have hω' : Θ * B x x < ‖entryErr (eG z ω) (msc z) x x‖ ^ 2 := hω
      linarith
    exact ((measure_mono hsub).trans h.hGd3).trans le_self_add
  · have hsub : {ω | Θ * B x y < ‖entryErr (eG z ω) (msc z) x y‖ ^ 2} ⊆
        Gdᶜ ∪ {ω | Θ' * B x y < eT S z x y ω} := by
      intro ω hω
      by_cases hGdω : ω ∈ Gd
      · right
        by_contra hc
        simp only [Set.mem_ofPred_eq, not_lt] at hc
        have h1 : ‖eG z ω x y‖ ^ 2 ≤ w * eT S z x y ω := by
          rw [hGd] at hGdω; exact hGdω.2 x y hxy
        have h2 : entryErr (eG z ω) (msc z) x y = eG z ω x y := by simp [entryErr, hxy]
        have hω' : Θ * B x y < ‖entryErr (eG z ω) (msc z) x y‖ ^ 2 := hω
        rw [h2] at hω'
        have h3 : w * eT S z x y ω ≤ w * (Θ' * B x y) :=
          mul_le_mul_of_nonneg_left hc (by linarith [h.hw])
        have h4 : w * (Θ' * B x y) ≤ Θ * B x y := by
          have := mul_le_mul_of_nonneg_right hwΘ hBxy.le
          linarith
        linarith
      · left; exact hGdω
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h.hGd3 ?_))
    have hmom := eta1_moment_closed h n hγ hεB x y
    have hmk := h.markov x y (n + 2) (Θ' * B x y) (mul_pos hΘ' hBxy)
      (2 * (eKap δ δs κ₁ ^ (n + 2) + 1) * (B x y) ^ (n + 2)) hmom
    refine hmk.trans (le_of_eq ?_)
    congr 1
    rw [mul_pow]
    field_simp

end Tail



section Numeric

/-- The size of `Γ` at the parameters of the model. -/
private theorem eta1_gam_le (d n : ℕ) (hd : 8 ≤ d) (Cs : ℝ) (hCs : 0 ≤ Cs) (W τ₁ : ℝ) (hW : 1 ≤ W)
    (hτ₁ : 0 ≤ τ₁) (hτ₁' : τ₁ ≤ 1 / 20) :
    eGam n (W ^ τ₁ * W ^ (-(d : ℝ) / 2)) (W ^ τ₁) (Cs / W ^ d)
        ((2 * W ^ τ₁) ^ (2 * (d - 2)) + 1) ≤
      (3 * 4 ^ d * (34 + 72 * ((n : ℝ) + 1) * (320 * (Real.sqrt Cs + 1) + 2 * Cs))) *
        W ^ (-(d : ℝ) / 4) := by
  have hW0 : 0 < W := by linarith
  set Y : ℝ := W ^ τ₁ with hY
  set V : ℝ := W ^ (-(d : ℝ) / 2) with hV
  have hY1 : 1 ≤ Y := Real.one_le_rpow hW hτ₁
  have hV0 : 0 < V := by positivity
  have hV1 : V ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)
  have hVsq : Cs / W ^ d = Cs * V ^ 2 := by
    have h2 : V ^ 2 = W ^ (-(d : ℝ)) := by
      rw [hV, ← Real.rpow_natCast (W ^ (-(d : ℝ) / 2)) 2, ← Real.rpow_mul hW0.le]
      congr 1; push_cast; ring
    rw [h2, Real.rpow_neg hW0.le, Real.rpow_natCast, div_eq_mul_inv]
  rw [hVsq]
  have hδ₃ : Real.sqrt (Cs * V ^ 2 + (Y * V) ^ 2) ≤ V * Y * (Real.sqrt Cs + 1) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hs := Real.sq_sqrt hCs
    set a := Real.sqrt Cs with ha
    have ha0 : 0 ≤ a := Real.sqrt_nonneg Cs
    have hY2 : 1 ≤ Y ^ 2 := by nlinarith
    have hA : 0 ≤ a ^ 2 * V ^ 2 * (Y ^ 2 - 1) :=
      mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg V)) (sub_nonneg.2 hY2)
    have hB : 0 ≤ 2 * V ^ 2 * Y ^ 2 * a := by positivity
    have hs2 : Cs * V ^ 2 = a ^ 2 * V ^ 2 := by rw [hs]
    nlinarith [hA, hB, hs2]
  have hδ : (Y * V) ≤ V * Y * (Real.sqrt Cs + 1) := by
    have := Real.sqrt_nonneg Cs
    nlinarith [mul_nonneg (mul_nonneg hV0.le (by linarith : (0 : ℝ) ≤ Y)) this]
  have hκ : 1 + ((2 * Y) ^ (2 * (d - 2)) + 1) ≤ 3 * (4 ^ d * Y ^ (2 * d)) := by
    have h1 : (2 * Y) ^ (2 * (d - 2)) ≤ 4 ^ d * Y ^ (2 * d) := by
      rw [mul_pow]
      have : (2 : ℝ) ^ (2 * (d - 2)) ≤ 4 ^ d := by
        calc (2 : ℝ) ^ (2 * (d - 2)) = 4 ^ (d - 2) := by rw [pow_mul]; norm_num
          _ ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
      exact mul_le_mul this (pow_le_pow_right₀ hY1 (by omega)) (by positivity) (by positivity)
    have h2 : (1 : ℝ) ≤ 4 ^ d * Y ^ (2 * d) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hY1)
    linarith
  unfold eGam
  set a := Real.sqrt Cs with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg Cs
  set Ca : ℝ := 34 + 72 * ((n : ℝ) + 1) * (320 * (a + 1) + 2 * Cs) with hCa
  have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hY3 : Y ≤ Y ^ 3 := by nlinarith [sq_nonneg Y]
  have hY2 : Y ^ 2 ≤ Y ^ 3 := by nlinarith [sq_nonneg Y]
  have hVV : V ^ 2 ≤ V := by nlinarith
  have hF1 : 2 * (Y + 16) * (Y * V) + 4 * (18 * ((n : ℝ) + 1) * Y ^ 2 *
      (320 * Real.sqrt (Cs * V ^ 2 + (Y * V) ^ 2) + 2 * (Cs * V ^ 2))) ≤ Ca * (Y ^ 3 * V) := by
    have e1 : 2 * (Y + 16) * (Y * V) ≤ 34 * (Y ^ 3 * V) := by
      have : Y + 16 ≤ 17 * Y := by linarith
      nlinarith [mul_nonneg hV0.le (by linarith : (0 : ℝ) ≤ Y), mul_nonneg hV0.le (sq_nonneg Y)]
    have e2 : 320 * Real.sqrt (Cs * V ^ 2 + (Y * V) ^ 2) ≤ 320 * (V * Y * (a + 1)) :=
      mul_le_mul_of_nonneg_left hδ₃ (by norm_num)
    have e3 : 4 * (18 * ((n : ℝ) + 1) * Y ^ 2 *
        (320 * Real.sqrt (Cs * V ^ 2 + (Y * V) ^ 2) + 2 * (Cs * V ^ 2))) ≤
        72 * ((n : ℝ) + 1) * (320 * (a + 1) + 2 * Cs) * (Y ^ 3 * V) := by
      have hc : 0 ≤ 72 * ((n : ℝ) + 1) * Y ^ 2 := by positivity
      have h1 : 320 * Real.sqrt (Cs * V ^ 2 + (Y * V) ^ 2) + 2 * (Cs * V ^ 2) ≤
          (320 * (a + 1) + 2 * Cs) * (V * Y) := by
        have : 2 * (Cs * V ^ 2) ≤ 2 * Cs * (V * Y) := by
          have : V ^ 2 ≤ V * Y := by nlinarith
          nlinarith
        nlinarith
      calc 4 * (18 * ((n : ℝ) + 1) * Y ^ 2 *
            (320 * Real.sqrt (Cs * V ^ 2 + (Y * V) ^ 2) + 2 * (Cs * V ^ 2)))
          = 72 * ((n : ℝ) + 1) * Y ^ 2 * (320 * Real.sqrt (Cs * V ^ 2 + (Y * V) ^ 2) +
              2 * (Cs * V ^ 2)) := by ring
        _ ≤ 72 * ((n : ℝ) + 1) * Y ^ 2 * ((320 * (a + 1) + 2 * Cs) * (V * Y)) :=
            mul_le_mul_of_nonneg_left h1 hc
        _ = 72 * ((n : ℝ) + 1) * (320 * (a + 1) + 2 * Cs) * (Y ^ 3 * V) := by ring
    simp only [hCa]
    nlinarith
  have hYV : Y ^ (2 * d + 3) * V ≤ W ^ (-(d : ℝ) / 4) := by
    have h1 : Y ^ (2 * d + 3) ≤ W ^ ((d : ℝ) / 4) := by
      rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      refine Real.rpow_le_rpow_of_exponent_le hW ?_
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
    calc Y ^ (2 * d + 3) * V ≤ W ^ ((d : ℝ) / 4) * W ^ (-(d : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h1 hV0.le
      _ = W ^ (-(d : ℝ) / 4) := by rw [← Real.rpow_add hW0]; congr 1; ring
  have hFac : 0 ≤ Ca := by simp only [hCa]; positivity
  calc _ ≤ (Ca * (Y ^ 3 * V)) * (3 * (4 ^ d * Y ^ (2 * d))) := by
        refine mul_le_mul hF1 hκ (by positivity) (by positivity)
    _ = (3 * 4 ^ d * Ca) * (Y ^ (2 * d + 3) * V) := by ring
    _ ≤ (3 * 4 ^ d * Ca) * W ^ (-(d : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hYV (by positivity)

private theorem eta1_bB_diag {d L : ℕ} (W : ℕ) (hW : 1 ≤ W) (x : Zd d L) [NeZero L] :
    bB d L W x x = (W : ℝ) ^ (-(d : ℝ)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold bB
  have h0 : zdistInf d L (x - x) = 0 := by
    rw [sub_self]; exact (zdistInf_eq_zero_iff d L).2 rfl
  rw [h0]
  simp only [Nat.cast_zero, zero_add]
  rw [← Real.rpow_add hW0]
  congr 1; ring

/-- `B_{xy} ≥ W^{-C₃}` on `adm(c₀, c₁)`. -/
private theorem eta1_bB_lower {d L : ℕ} [NeZero L] (hd : 2 ≤ d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (W : ℕ) (hadm : (W, L) ∈ adm c₀ c₁) (hW : 2 ≤ W) (x y : Zd d L) :
    (W : ℝ) ^ (-(2 + ((d : ℝ) - 2) * (1 + 1 / c₁))) ≤ bB d L W x y := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLW : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁) := by
    have h1 := Real.rpow_le_rpow (by positivity) hadm.1 (by positivity : (0 : ℝ) ≤ 1 / c₁)
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hc₁.ne', Real.rpow_one] at h1
  have hWL : (W : ℝ) ≤ L := by
    have h1 := hadm.2
    have h2 : (L : ℝ) ^ (1 - c₀) ≤ (L : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    rw [Real.rpow_one] at h2
    exact h1.trans h2
  rw [eta1_bB_pow hd W hWn]
  have hρ : (zdistInf d L (x - y) : ℝ) + W ≤ 2 * (W : ℝ) ^ (1 / c₁) := by
    have := zdistInf_le_half d L (x - y)
    have h2 : (zdistInf d L (x - y) : ℝ) ≤ L := by
      have : zdistInf d L (x - y) ≤ L := this.trans (Nat.div_le_self _ _)
      exact_mod_cast this
    linarith
  have hρ0 : 0 < (zdistInf d L (x - y) : ℝ) + W := by
    have := (Nat.cast_nonneg (zdistInf d L (x - y)) : (0 : ℝ) ≤ _); linarith
  set N : ℕ := d - 2 with hN
  set X : ℝ := ((d : ℝ) - 2) * (1 + 1 / c₁) with hX
  have hNa : (N : ℝ) = (d : ℝ) - 2 := by rw [hN, Nat.cast_sub hd]; push_cast; ring
  have hpow : ((zdistInf d L (x - y) : ℝ) + W) ^ N ≤ (W : ℝ) ^ X := by
    have e1 : (W : ℝ) ^ N = (W : ℝ) ^ (N : ℝ) := (Real.rpow_natCast _ _).symm
    have e2 : ((W : ℝ) ^ (1 / c₁)) ^ N = (W : ℝ) ^ (1 / c₁ * (N : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    have e3 : (W : ℝ) ^ (N : ℝ) * (W : ℝ) ^ (1 / c₁ * (N : ℝ)) = (W : ℝ) ^ X := by
      rw [← Real.rpow_add hW0, hX, ← hNa]; congr 1; ring
    calc ((zdistInf d L (x - y) : ℝ) + W) ^ N ≤ (2 * (W : ℝ) ^ (1 / c₁)) ^ N :=
          pow_le_pow_left₀ hρ0.le hρ _
      _ = 2 ^ N * ((W : ℝ) ^ (1 / c₁)) ^ N := mul_pow _ _ _
      _ ≤ (W : ℝ) ^ N * ((W : ℝ) ^ (1 / c₁)) ^ N :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hW2 _) (by positivity)
      _ = (W : ℝ) ^ X := by rw [e1, e2, e3]
  have hρN : 0 < ((zdistInf d L (x - y) : ℝ) + W) ^ N := pow_pos hρ0 _
  have hWX : 0 < (W : ℝ) ^ X := by positivity
  calc (W : ℝ) ^ (-(2 + X)) = (W : ℝ) ^ (-2 : ℝ) / (W : ℝ) ^ X := by
        rw [show -(2 + X) = (-2 : ℝ) + (-X) by ring, Real.rpow_add hW0, Real.rpow_neg hW0.le X,
          div_eq_mul_inv]
    _ ≤ (W : ℝ) ^ (-2 : ℝ) / ((zdistInf d L (x - y) : ℝ) + W) ^ N :=
        div_le_div_of_nonneg_left (by positivity) hρN hpow

end Numeric



section TailZ

set_option maxHeartbeats 4000000 in
private theorem eta1_tail_z (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (τ D : ℝ) (hτ : 0 < τ) (hD : 0 < D) :
    ∃ τ₁ D₁ W₀ : ℝ, 0 < τ₁ ∧ 0 < D₁ ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z : ℂ, z.im = 1 → |z.re| < 2 - κ →
      gaussLaw (Smat P.ψ W L) {ω | ¬ ∀ k l, ‖entryErr (green (hmat ω) z) (msc z) k l‖ ≤
        (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(d : ℝ) / 2)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D₁)) →
      gaussLaw (Smat P.ψ W L) {ω | ¬ ∀ k l, k ≠ l → ‖green (hmat ω) z k l‖ ^ 2 ≤
        (W : ℝ) ^ τ₁ * Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) k l} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D₁)) →
      ∀ x y : Zd d L, gaussLaw (Smat P.ψ W L) {ω | (W : ℝ) ^ τ * bB d L W x y <
        ‖entryErr (green (hmat ω) z) (msc z) x y‖ ^ 2} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  set τ₁ : ℝ := min (τ / 8) (1 / 20) with hτ₁
  have hτ₁0 : 0 < τ₁ := lt_min (by positivity) (by norm_num)
  have hτ₁a : τ₁ ≤ τ / 8 := min_le_left _ _
  have hτ₁b : τ₁ ≤ 1 / 20 := min_le_right _ _
  set n : ℕ := ⌈4 * (D + 3) / τ⌉₊ with hn
  have hnτ : D + 3 ≤ (n : ℝ) * τ / 4 := by
    have h1 : 4 * (D + 3) / τ ≤ n := Nat.le_ceil _
    rw [div_le_iff₀ hτ] at h1
    linarith
  set C₃ : ℝ := 2 + ((d : ℝ) - 2) * (1 + 1 / c₁) with hC₃
  have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hC₃0 : 0 ≤ C₃ := by
    have : 0 ≤ 1 / c₁ := by positivity
    rw [hC₃]; nlinarith
  set D₁ : ℝ := C₃ * ((n : ℝ) + 2) + D + 4 with hD₁
  have hD₁0 : 0 < D₁ := by
    have : 0 ≤ C₃ * ((n : ℝ) + 2) := by positivity
    rw [hD₁]; linarith
  obtain ⟨W_K, Cs, hCs0, hK⟩ := eta1_kernel d (by omega) P c₀ c₁ κ c₀ τ₁ hc₀ hc₁ hκ hc₀ hτ₁0
  set CΓ : ℝ := 2 * (3 * 4 ^ d * (34 + 72 * ((n : ℝ) + 1) * (320 * (Real.sqrt Cs + 1) + 2 * Cs)))
    with hCΓ
  have hev : ∀ᶠ W : ℝ in atTop, 128 ≤ W ∧ 7 ≤ W ^ τ₁ ∧ Cs ≤ W ∧ 20 * Cs ≤ W ∧
      CΓ * W ^ (-((d : ℝ) / 4)) < 1 / 4 := by
    refine (eventually_ge_atTop 128).and ((((tendsto_rpow_atTop hτ₁0).eventually_ge_atTop 7)).and
      ((eventually_ge_atTop Cs).and ((eventually_ge_atTop (20 * Cs)).and ?_)))
    have ht : Tendsto (fun W : ℝ => CΓ * W ^ (-((d : ℝ) / 4))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < (d : ℝ) / 4)).const_mul CΓ
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨W_n, hWn⟩ := Filter.eventually_atTop.mp hev
  refine ⟨τ₁, D₁, max W_K W_n, hτ₁0, hD₁0, ?_⟩
  intro W L _ hadm hW z hzim hzre hP1 hP2 x y
  have hWK : W_K ≤ W := (le_max_left _ _).trans hW
  have hWn' : W_n ≤ W := (le_max_right _ _).trans hW
  obtain ⟨h128, h7, hCsW, h20Cs, hΓ⟩ := hWn (W : ℝ) hWn'
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hWnat : 2 ≤ W := by exact_mod_cast (by linarith : (2 : ℝ) ≤ W)
  have hWn1 : 1 ≤ W := by omega
  have hz0 : 0 < z.im := by rw [hzim]; exact one_pos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  -- the spectral domain
  have hspec : z ∈ specDom κ c₀ W L := by
    refine ⟨hzre, ?_, le_of_eq hzim⟩
    rw [hzim, div_le_one (by positivity)]
    have h1 : (W : ℝ) ^ 2 ≤ ((L : ℝ) ^ (1 - c₀)) ^ 2 :=
      pow_le_pow_left₀ hW0.le hadm.2 2
    have h2 : ((L : ℝ) ^ (1 - c₀)) ^ 2 = (L : ℝ) ^ (2 - 2 * c₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
    have h3 : (L : ℝ) ^ (2 - 2 * c₀) ≤ (L : ℝ) ^ (2 - c₀) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    exact h1.trans (h2 ▸ h3)
  obtain ⟨⟨hsymm, hnn, hrow, hSle⟩, hker⟩ := hK W L hadm hWK
  obtain ⟨hΘ0, hΘ1, hΘ2, hΘ3⟩ := hker z hspec hzim
  set δ : ℝ := (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(d : ℝ) / 2) with hδ
  set w : ℝ := (W : ℝ) ^ τ₁ with hw
  set δs : ℝ := Cs / (W : ℝ) ^ d with hδs
  have hw1 : 1 ≤ w := Real.one_le_rpow hW1 hτ₁0.le
  have hδ0 : 0 ≤ δ := by positivity
  have hδle : δ ≤ 1 / 128 := by
    rw [hδ, ← Real.rpow_add hW0]
    calc (W : ℝ) ^ (τ₁ + -(d : ℝ) / 2) ≤ (W : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = (W : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 128 := by
          rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h128
  have hδs0 : 0 ≤ δs := by positivity
  have hδsle : δs ≤ 1 / 20 := by
    have h1 : (W : ℝ) ≤ (W : ℝ) ^ d := by
      calc (W : ℝ) = (W : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (W : ℝ) ^ d := pow_le_pow_right₀ hW1 (by omega)
    calc δs = Cs / (W : ℝ) ^ d := rfl
      _ ≤ Cs / W := div_le_div_of_nonneg_left hCs0 hW0 h1
      _ ≤ 1 / 20 := by rw [div_le_iff₀ hW0]; linarith
  have hgam := eta1_gam_le d n hd Cs hCs0 (W : ℝ) τ₁ hW1 hτ₁0.le hτ₁b
  have hγ : 2 * eGam n δ w δs ((2 * w) ^ (2 * (d - 2)) + 1) ≤ 1 / 2 := by
    have e : (-(d : ℝ) / 4) = -((d : ℝ) / 4) := by ring
    rw [e] at hgam
    have : 2 * eGam n δ w δs ((2 * w) ^ (2 * (d - 2)) + 1) ≤ CΓ * (W : ℝ) ^ (-((d : ℝ) / 4)) := by
      simp only [hCΓ]
      linarith
    linarith
  have hzn : ‖z‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [hzim, abs_one] at this
    have := hκ
    linarith [abs_nonneg z.re]
  have hεW : 0 ≤ 2 * (W : ℝ) ^ (-D₁) := by positivity
  have hhyp : Eta1Hyp (Smat P.ψ W L) z (bB d L W) δ w δs (2 * w) ((2 * w) ^ (2 * (d - 2)) + 1)
      (2 * (W : ℝ) ^ (-D₁)) (eGd (Smat P.ψ W L) z δ w) := by
    refine ⟨hsymm, hnn, hrow, hzim, norm_msc_ge_quarter z hz0 hzn, hδ0, by linarith, hw1, hδs0,
      hSle, by positivity, by positivity, hεW, fun a b => eta1_bB_pos W hWn1 a b, hΘ0, hΘ1, hΘ2,
      hΘ3, eta1_eGd_meas _ z hz0 δ w, fun ω hω => hω.1, fun ω hω => hω.2, ?_⟩
    have hsub : (eGd (Smat P.ψ W L) z δ w)ᶜ ⊆
        {ω | ¬ ∀ k l, ‖entryErr (green (hmat ω) z) (msc z) k l‖ ≤ δ} ∪
        {ω | ¬ ∀ k l, k ≠ l → ‖green (hmat ω) z k l‖ ^ 2 ≤
          w * Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) k l} := by
      intro ω hω
      by_contra hc
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
      exact hω ⟨hc.1, hc.2⟩
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    calc _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-D₁)) + ENNReal.ofReal ((W : ℝ) ^ (-D₁)) :=
          add_le_add hP1 hP2
      _ = ENNReal.ofReal (2 * (W : ℝ) ^ (-D₁)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  -- the lower bound of `B`
  have hBlow : ∀ a b : Zd d L, (W : ℝ) ^ (-C₃) ≤ bB d L W a b := fun a b =>
    eta1_bB_lower (by omega) c₀ c₁ hc₀ hc₁ W hadm hWnat a b
  have hinv : (W : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 128 := by
    rw [Real.rpow_neg_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h128
  have hsmall : ∀ t : ℝ, 1 ≤ t → 128 * (W : ℝ) ^ (-t) ≤ 1 := by
    intro t ht
    have : (W : ℝ) ^ (-t) ≤ (W : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    linarith
  have hεB : ∀ a b : Zd d L, 64 * (2 * (W : ℝ) ^ (-D₁)) ≤ (bB d L W a b) ^ (n + 2) := by
    intro a b
    have h1 : ((W : ℝ) ^ (-C₃)) ^ (n + 2) ≤ (bB d L W a b) ^ (n + 2) :=
      pow_le_pow_left₀ (by positivity) (hBlow a b) _
    have h2 : ((W : ℝ) ^ (-C₃)) ^ (n + 2) = (W : ℝ) ^ (-C₃ * ((n : ℝ) + 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have e : (W : ℝ) ^ (-D₁) = (W : ℝ) ^ (-C₃ * ((n : ℝ) + 2)) * (W : ℝ) ^ (-(D + 4)) := by
      rw [← Real.rpow_add hW0]; congr 1; rw [hD₁]; ring
    have h3 := hsmall (D + 4) (by linarith)
    have h4 : 0 < (W : ℝ) ^ (-C₃ * ((n : ℝ) + 2)) := by positivity
    calc 64 * (2 * (W : ℝ) ^ (-D₁)) = (W : ℝ) ^ (-C₃ * ((n : ℝ) + 2)) *
          (128 * (W : ℝ) ^ (-(D + 4))) := by rw [e]; ring
      _ ≤ (W : ℝ) ^ (-C₃ * ((n : ℝ) + 2)) * 1 := mul_le_mul_of_nonneg_left h3 h4.le
      _ ≤ _ := by rw [mul_one, ← h2]; exact h1
  have hV2 : ((W : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (W : ℝ) ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  have hY2 : ((W : ℝ) ^ τ₁) ^ 2 ≤ (W : ℝ) ^ τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by push_cast; linarith)
  have hδΘ : ∀ a : Zd d L, δ ^ 2 ≤ (W : ℝ) ^ τ * bB d L W a a := by
    intro a
    rw [eta1_bB_diag W hWn1, hδ, mul_pow, hV2]
    exact mul_le_mul_of_nonneg_right hY2 (by positivity)
  have hwΘ : w * (W : ℝ) ^ (τ / 2) ≤ (W : ℝ) ^ τ := by
    rw [hw, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have htail := eta1_tail_entry hhyp n hγ hεB ((W : ℝ) ^ τ) ((W : ℝ) ^ (τ / 2)) (by positivity) hwΘ
    hδΘ rfl x y
  have hK0 : 0 ≤ eKap δ δs (2 * w) := by
    have h1 := hδ0
    have h2 := hδs0
    have h3 := hw1
    unfold eKap
    positivity
  have hq0 : 0 ≤ 2 * (eKap δ δs (2 * w) ^ (n + 2) + 1) / ((W : ℝ) ^ (τ / 2)) ^ (n + 2) := by
    have := pow_nonneg hK0 (n + 2)
    positivity
  refine htail.trans ?_
  rw [← ENNReal.ofReal_add hεW hq0]
  refine ENNReal.ofReal_le_ofReal ?_
  set Q : ℝ := (n : ℝ) + 2 with hQ
  have hK : eKap δ δs (2 * w) ≤ w ^ 2 := by
    have h1 : 1 + δ + (8 * δ + 2 * δs + 2 * δ ^ 2) ≤ 6 / 5 := by nlinarith
    unfold eKap
    have : 2 * (1 + δ + (8 * δ + 2 * δs + 2 * δ ^ 2)) * (2 * w) ≤ 2 * (6 / 5) * (2 * w) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have hKq : eKap δ δs (2 * w) ^ (n + 2) ≤ (W : ℝ) ^ (2 * τ₁ * Q) := by
    calc eKap δ δs (2 * w) ^ (n + 2) ≤ (w ^ 2) ^ (n + 2) := pow_le_pow_left₀ hK0 hK _
      _ = (W : ℝ) ^ (2 * τ₁ * Q) := by
          have hw2 : w ^ 2 = (W : ℝ) ^ (2 * τ₁) := by
            rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
          rw [hw2, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
          congr 1; rw [hQ]; push_cast; ring
  have hΘq : ((W : ℝ) ^ (τ / 2)) ^ (n + 2) = (W : ℝ) ^ (τ / 2 * Q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; rw [hQ]; push_cast; ring
  have hWQ : (1 : ℝ) ≤ (W : ℝ) ^ (2 * τ₁ * Q) :=
    Real.one_le_rpow hW1 (by rw [hQ]; positivity)
  have hΘQ : 0 < (W : ℝ) ^ (τ / 2 * Q) := by positivity
  have hQn : (n : ℝ) ≤ Q := by rw [hQ]; linarith
  have hexp : 2 * τ₁ * Q - τ / 2 * Q ≤ -(D + 3) := by
    have h1 : 2 * τ₁ ≤ τ / 4 := by linarith
    have h2 : 2 * τ₁ * Q ≤ τ / 4 * Q := mul_le_mul_of_nonneg_right h1 (by rw [hQ]; positivity)
    have h3 : τ * (n : ℝ) / 4 ≤ τ * Q / 4 := by
      have := mul_le_mul_of_nonneg_left hQn hτ.le
      linarith
    nlinarith
  have hrat : 2 * (eKap δ δs (2 * w) ^ (n + 2) + 1) / ((W : ℝ) ^ (τ / 2)) ^ (n + 2) ≤
      4 * (W : ℝ) ^ (-(D + 3)) := by
    rw [hΘq, div_le_iff₀ hΘQ]
    have h1 : 2 * (eKap δ δs (2 * w) ^ (n + 2) + 1) ≤ 4 * (W : ℝ) ^ (2 * τ₁ * Q) := by
      linarith
    have h2 : (W : ℝ) ^ (2 * τ₁ * Q) ≤ (W : ℝ) ^ (-(D + 3)) * (W : ℝ) ^ (τ / 2 * Q) := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    calc 2 * (eKap δ δs (2 * w) ^ (n + 2) + 1) ≤ 4 * (W : ℝ) ^ (2 * τ₁ * Q) := h1
      _ ≤ 4 * ((W : ℝ) ^ (-(D + 3)) * (W : ℝ) ^ (τ / 2 * Q)) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 4 * (W : ℝ) ^ (-(D + 3)) * (W : ℝ) ^ (τ / 2 * Q) := by ring
  have hε1 : 2 * (W : ℝ) ^ (-D₁) ≤ 2 * (W : ℝ) ^ (-(D + 4)) := by
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1 ?_) (by norm_num)
    have : 0 ≤ C₃ * ((n : ℝ) + 2) := by positivity
    rw [hD₁]; linarith
  have e3 : (W : ℝ) ^ (-(D + 3)) = (W : ℝ) ^ (-D) * (W : ℝ) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have e4 : (W : ℝ) ^ (-(D + 4)) = (W : ℝ) ^ (-D) * (W : ℝ) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have h3 : (W : ℝ) ^ (-(3 : ℝ)) ≤ 1 / 128 := by
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num : (-3 : ℝ) ≤ -1)) hinv
  have h4 : (W : ℝ) ^ (-(4 : ℝ)) ≤ 1 / 128 := by
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num : (-4 : ℝ) ≤ -1)) hinv
  have hWD : 0 < (W : ℝ) ^ (-D) := by positivity
  calc 2 * (W : ℝ) ^ (-D₁) + 2 * (eKap δ δs (2 * w) ^ (n + 2) + 1) / ((W : ℝ) ^ (τ / 2)) ^ (n + 2)
      ≤ 2 * (W : ℝ) ^ (-(D + 4)) + 4 * (W : ℝ) ^ (-(D + 3)) := add_le_add hε1 hrat
    _ = (W : ℝ) ^ (-D) * (2 * (W : ℝ) ^ (-(4 : ℝ)) + 4 * (W : ℝ) ^ (-(3 : ℝ))) := by
        rw [e3, e4]; ring
    _ ≤ (W : ℝ) ^ (-D) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hWD.le
        linarith
    _ = (W : ℝ) ^ (-D) := mul_one _

end TailZ



section SDutil

variable {Par : Type*} {Ω : Par → Type*} [∀ p, MeasurableSpace (Ω p)] {F : Filter Par}
  {size : Par → ℝ} {Pr : ∀ p, Measure (Ω p)}

/-- Reindexing of a stochastic domination. -/
private theorem eta1_sd_comp {U U' : Par → Type*} (f : ∀ p, U' p → U p) {ξ ζ : ∀ p, U p → Ω p → ℝ}
    {ξ' ζ' : ∀ p, U' p → Ω p → ℝ} (hξ : ∀ p u' ω, ξ' p u' ω = ξ p (f p u') ω)
    (hζ : ∀ p u' ω, ζ' p u' ω = ζ p (f p u') ω) (h : StochDom F size Pr ξ ζ) :
    StochDom F size Pr ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with p hp
  refine le_trans (measure_mono ?_) hp
  rintro ω ⟨u', hu'⟩
  exact ⟨f p u', by rw [← hξ, ← hζ]; exact hu'⟩

/-- Monotonicity in the comparison function. -/
private theorem eta1_sd_mono {U : Par → Type*} {ξ ζ ζ' : ∀ p, U p → Ω p → ℝ}
    (hs : ∀ᶠ p in F, 0 ≤ size p) (hζ : ∀ᶠ p in F, ∀ u ω, ζ p u ω ≤ ζ' p u ω)
    (h : StochDom F size Pr ξ ζ) : StochDom F size Pr ξ ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hs, hζ] with p hp hs0 hζp
  refine le_trans (measure_mono ?_) hp
  rintro ω ⟨u, hu⟩
  refine ⟨u, lt_of_le_of_lt ?_ hu⟩
  exact mul_le_mul_of_nonneg_left (hζp u ω) (Real.rpow_nonneg hs0 τ)

/-- Stochastic domination from a deterministic implication. -/
private theorem eta1_sd_det {U U₁ : Par → Type*} {ξ ζ : ∀ p, U p → Ω p → ℝ} {ξ₁ ζ₁ : ∀ p, U₁ p → Ω p → ℝ}
    (h₁ : StochDom F size Pr ξ₁ ζ₁)
    (hdet : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ p in F, ∀ ω,
      (∀ u₁, ξ₁ p u₁ ω ≤ size p ^ τ' * ζ₁ p u₁ ω) → ∀ u, ξ p u ω ≤ size p ^ τ * ζ p u ω) :
    StochDom F size Pr ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hd⟩ := hdet τ hτ
  filter_upwards [hd, h₁ τ' hτ' D hD] with p hp hp₁
  refine le_trans (measure_mono ?_) hp₁
  rintro ω ⟨u, hu⟩
  by_contra hcon
  have : ∀ u₁, ξ₁ p u₁ ω ≤ size p ^ τ' * ζ₁ p u₁ ω := by
    intro u₁
    by_contra h1
    exact hcon ⟨u₁, not_le.1 h1⟩
  exact absurd (hp ω this u) (not_le.2 hu)

end SDutil

section Net

/-- The number of grid points. -/
private def eta1N (a C₁ W : ℝ) : ℕ := ⌈2 * a * W ^ C₁⌉₊ + 1

/-- The grid of spectral parameters on `(-a, a)`. -/
private def eta1Grid (a C₁ W : ℝ) : Finset ℝ :=
  (Finset.range (eta1N a C₁ W)).image fun k : ℕ =>
    -a + ((k : ℝ) + 1 / 2) * (2 * a / (eta1N a C₁ W : ℝ))

private theorem eta1Grid_mem {a C₁ W : ℝ} (ha : 0 < a) {E : ℝ} (hE : E ∈ eta1Grid a C₁ W) :
    |E| < a := by
  unfold eta1Grid at hE
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hE
  have hk' : k < eta1N a C₁ W := Finset.mem_range.mp hk
  have hN : (0 : ℝ) < (eta1N a C₁ W : ℝ) := by
    have : 1 ≤ eta1N a C₁ W := by unfold eta1N; omega
    exact_mod_cast this
  have hkN : (k : ℝ) + 1 ≤ (eta1N a C₁ W : ℝ) := by exact_mod_cast hk'
  have hh : 0 < 2 * a / (eta1N a C₁ W : ℝ) := by positivity
  rw [abs_lt]
  constructor
  · have : 0 < ((k : ℝ) + 1 / 2) * (2 * a / (eta1N a C₁ W : ℝ)) := by positivity
    linarith
  · have h1 : ((k : ℝ) + 1 / 2) * (2 * a / (eta1N a C₁ W : ℝ)) <
        (eta1N a C₁ W : ℝ) * (2 * a / (eta1N a C₁ W : ℝ)) :=
      mul_lt_mul_of_pos_right (by linarith) hh
    have h2 : (eta1N a C₁ W : ℝ) * (2 * a / (eta1N a C₁ W : ℝ)) = 2 * a := by
      field_simp
    linarith

private theorem eta1Grid_cover {a C₁ W : ℝ} (ha : 0 < a) (hW : 0 < W) {E : ℝ} (hE : |E| < a) :
    ∃ E' ∈ eta1Grid a C₁ W, |E - E'| ≤ W ^ (-C₁) := by
  have hN1 : 1 ≤ eta1N a C₁ W := by unfold eta1N; omega
  have hN : (0 : ℝ) < (eta1N a C₁ W : ℝ) := by exact_mod_cast hN1
  set N := eta1N a C₁ W with hNdef
  set h : ℝ := 2 * a / (N : ℝ) with hh
  have hh0 : 0 < h := by positivity
  have hNge : 2 * a * W ^ C₁ < (N : ℝ) := by
    have := Nat.le_ceil (2 * a * W ^ C₁)
    have h2 : (N : ℝ) = (⌈2 * a * W ^ C₁⌉₊ : ℝ) + 1 := by
      rw [hNdef]; unfold eta1N; push_cast; ring
    linarith
  have hhW : h ≤ W ^ (-C₁) := by
    rw [hh, div_le_iff₀ hN, Real.rpow_neg hW.le]
    have hWC : 0 < W ^ C₁ := by positivity
    rw [inv_mul_eq_div, le_div_iff₀ hWC]
    nlinarith
  rw [abs_lt] at hE
  set t : ℝ := (E + a) / h with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) hh0.le
  have htN : t < (N : ℝ) := by
    rw [ht, div_lt_iff₀ hh0, hh]
    have : (N : ℝ) * (2 * a / (N : ℝ)) = 2 * a := by field_simp
    linarith
  set k : ℕ := ⌊t⌋₊ with hk
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht0
  have htk : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  have hkN : k < N := by
    have : (k : ℝ) < (N : ℝ) := lt_of_le_of_lt hkt htN
    exact_mod_cast this
  refine ⟨-a + ((k : ℝ) + 1 / 2) * h, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkN, rfl⟩, ?_⟩
  have e1 : E = -a + t * h := by rw [ht]; field_simp; ring
  rw [e1]
  have : -a + t * h - (-a + ((k : ℝ) + 1 / 2) * h) = (t - (k : ℝ) - 1 / 2) * h := by ring
  rw [this, abs_mul, abs_of_pos hh0]
  have h3 : |t - (k : ℝ) - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  calc |t - (k : ℝ) - 1 / 2| * h ≤ (1 / 2) * h := mul_le_mul_of_nonneg_right h3 hh0.le
    _ ≤ h := by linarith
    _ ≤ W ^ (-C₁) := hhW

private theorem eta1Grid_card (a C₁ W : ℝ) : (eta1Grid a C₁ W).card ≤ eta1N a C₁ W := by
  unfold eta1Grid
  exact Finset.card_image_le.trans (by simp)

private theorem eta1N_le {a C₁ W : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) (hW : 1 ≤ W) (hC : 0 ≤ C₁) :
    (eta1N a C₁ W : ℝ) ≤ 6 * W ^ C₁ := by
  unfold eta1N
  have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * a * W ^ C₁)
  have h2 : (1 : ℝ) ≤ W ^ C₁ := Real.one_le_rpow hW hC
  have h3 : a * W ^ C₁ ≤ 2 * W ^ C₁ := mul_le_mul_of_nonneg_right ha2 (by positivity)
  push_cast
  linarith

end Net



section NetModel

private theorem eta1_ev_adm (c₀ c₁ : ℝ) : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ := by
  have h : ∀ᶠ q in admFilter c₀ c₁, q ∈ adm c₀ c₁ :=
    inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _)
  exact tendsto_comap.eventually h

/-- `z = E + i` with `|E| < 2 - κ` lies in `𝐃(κ, ε)` for `ε ≤ 2 c₀` on `adm(c₀, c₁)`. -/
private theorem eta1_specDom_of {W L : ℕ} [NeZero L] {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hε : ε ≤ 2 * c₀)
    (hadm : (W, L) ∈ adm c₀ c₁) (hW : 1 ≤ W) {z : ℂ} (hzim : z.im = 1) (hzre : |z.re| < 2 - κ) :
    z ∈ specDom κ ε W L := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨hzre, ?_, le_of_eq hzim⟩
  rw [hzim, div_le_one (by positivity)]
  have h1 : (W : ℝ) ^ 2 ≤ ((L : ℝ) ^ (1 - c₀)) ^ 2 :=
    pow_le_pow_left₀ hW0.le hadm.2 2
  have h2 : ((L : ℝ) ^ (1 - c₀)) ^ 2 = (L : ℝ) ^ (2 - 2 * c₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
  have h3 : (L : ℝ) ^ (2 - 2 * c₀) ≤ (L : ℝ) ^ (2 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  exact h1.trans (h2 ▸ h3)

/-- The net of spectral parameters at the size `p`. -/
private def eta1Net (κ C₁ : ℝ) (p : SizeL) : Finset ℂ :=
  (eta1Grid (2 - κ) C₁ (sizeW p)).image fun E : ℝ => (E : ℂ) + I

private theorem eta1Net_prop {κ C₁ : ℝ} (hκ : κ < 2) {p : SizeL} {w : ℂ}
    (hw : w ∈ eta1Net κ C₁ p) : w.im = 1 ∧ |w.re| < 2 - κ ∧ w = (w.re : ℂ) + I := by
  unfold eta1Net at hw
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hw
  refine ⟨by simp, ?_, by simp⟩
  have := eta1Grid_mem (by linarith : 0 < 2 - κ) hE
  simpa using this

private theorem eta1Net_cover {κ C₁ : ℝ} (hκ : κ < 2) {p : SizeL} (hW : 0 < sizeW p) {z : ℂ}
    (hzim : z.im = 1) (hzre : |z.re| < 2 - κ) : ∃ w ∈ eta1Net κ C₁ p, ‖z - w‖ ≤ sizeW p ^ (-C₁) := by
  obtain ⟨E', hE', hd⟩ := eta1Grid_cover (by linarith : 0 < 2 - κ) hW hzre (C₁ := C₁)
  refine ⟨(E' : ℂ) + I, Finset.mem_image.mpr ⟨E', hE', rfl⟩, ?_⟩
  have : z - ((E' : ℂ) + I) = ((z.re - E' : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hzim]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hd

private theorem eta1Net_card {κ C₁ : ℝ} (hκ : κ < 2) (hκ0 : 0 < κ) (hC : 0 ≤ C₁) {p : SizeL}
    (hW : 1 ≤ sizeW p) : ((eta1Net κ C₁ p).card : ℝ) ≤ 6 * sizeW p ^ C₁ := by
  unfold eta1Net
  have h1 : ((Finset.image (fun E : ℝ => (E : ℂ) + I) (eta1Grid (2 - κ) C₁ (sizeW p))).card : ℝ) ≤
      (eta1Grid (2 - κ) C₁ (sizeW p)).card := by
    exact_mod_cast Finset.card_image_le
  have h2 : ((eta1Grid (2 - κ) C₁ (sizeW p)).card : ℝ) ≤ (eta1N (2 - κ) C₁ (sizeW p) : ℝ) := by
    exact_mod_cast eta1Grid_card _ _ _
  exact h1.trans (h2.trans (eta1N_le (by linarith) (by linarith) hW hC))

end NetModel



section NetProb

/-- [II, (8.51)] at `η = 1`, indexed by the net. -/
private theorem eta1_S1 (d : ℕ) (P : Profile d) (c₀ c₁ κ C₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hκ : 0 < κ) (hκ2 : κ < 2) :
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
      (U := fun p => ↥(eta1Net κ C₁ p) × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖)
      (fun p _ _ => sizeW p ^ (-(d : ℝ) / 2)) := by
  have h := eta1Law d P c₀ c₁ hc₀ hc₁ κ hκ
  refine eta1_sd_comp (U := fun p => {E : ℝ // |E| < 2 - κ} × Zd d p.1.2 × Zd d p.1.2)
    (fun p v => (⟨v.1.1.re, (eta1Net_prop hκ2 v.1.2).2.1⟩, v.2.1, v.2.2)) ?_ ?_ h
  · intro p v ω
    obtain ⟨⟨w, hw⟩, x, y⟩ := v
    have hweq := (eta1Net_prop hκ2 hw).2.2
    show ‖entryErr (green (hmat ω) w) (msc w) x y‖ =
      ‖entryErr (green (hmat ω) ((w.re : ℂ) + I)) (msc ((w.re : ℂ) + I)) x y‖
    rw [← hweq]
  · intro p v ω
    rfl

private theorem eta1_T_small {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (hnn : ∀ x y, 0 ≤ S x y) (hrow : ∀ x, ∑ y, S x y = 1) (G : Matrix ι ι ℂ) (m : ℂ)
    (hm : ‖m‖ ≤ 1) (a s₀ : ℝ) (x y : ι) (hs : S x y ≤ s₀)
    (hG : ∀ α, ‖entryErr G m α y‖ ≤ a) : Tvar S G m x y ≤ 2 * a ^ 2 + 2 * s₀ := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hG y)
  have hpt : ∀ α, S x α * ‖G α y‖ ^ 2 ≤ S x α * (2 * a ^ 2) + (if α = y then 2 * S x y else 0) := by
    intro α
    by_cases hαy : α = y
    · subst hαy
      rw [ite_eq_left rfl]
      have h1 : ‖G α α‖ ≤ a + 1 := by
        have h2 := hG α
        simp only [entryErr, ite_true] at h2
        have : G α α = (G α α - m) + m := by ring
        calc ‖G α α‖ = ‖(G α α - m) + m‖ := by rw [← this]
          _ ≤ ‖G α α - m‖ + ‖m‖ := norm_add_le _ _
          _ ≤ a + 1 := by linarith
      have h3' : ‖G α α‖ ^ 2 ≤ (a + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : ‖G α α‖ ^ 2 ≤ 2 * a ^ 2 + 2 := by nlinarith [sq_nonneg (a - 1)]
      have := mul_le_mul_of_nonneg_left h3 (hnn x α)
      nlinarith
    · rw [ite_eq_right hαy, add_zero]
      have h2 := hG α
      have : ‖G α y‖ = ‖entryErr G m α y‖ := by simp [entryErr, hαy]
      have h3 : ‖G α y‖ ^ 2 ≤ 2 * a ^ 2 := by
        rw [this]; nlinarith [norm_nonneg (entryErr G m α y)]
      exact mul_le_mul_of_nonneg_left h3 (hnn x α)
  have hsum : ∑ α, S x α * ‖G α y‖ ^ 2 ≤ 2 * a ^ 2 + 2 * S x y := by
    calc ∑ α, S x α * ‖G α y‖ ^ 2 ≤ ∑ α, (S x α * (2 * a ^ 2) + (if α = y then 2 * S x y else 0)) :=
          Finset.sum_le_sum fun α _ => hpt α
      _ = 2 * a ^ 2 + 2 * S x y := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ y, ite_eq_left (Finset.mem_univ y),
            ← Finset.sum_mul, hrow x, one_mul]
  unfold Tvar
  have h0 : 0 ≤ ∑ α, S x α * ‖G α y‖ ^ 2 :=
    Finset.sum_nonneg fun α _ => mul_nonneg (hnn x α) (sq_nonneg _)
  have hm2 : ‖m‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg m]
  calc ‖m‖ ^ 2 * ∑ α, S x α * ‖G α y‖ ^ 2 ≤ 1 * (2 * a ^ 2 + 2 * S x y) :=
        mul_le_mul hm2 hsum h0 zero_le_one
    _ ≤ 2 * a ^ 2 + 2 * s₀ := by linarith

private theorem eta1_S2 (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ C₁ : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (hκ2 : κ < 2) (hC₁ : 0 ≤ C₁) :
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
      (U := fun p => ↥(eta1Net κ C₁ p) × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => if v.2.1 = v.2.2 then 0 else ‖green (hmat ω) v.1.1 v.2.1 v.2.2‖ ^ 2)
      (fun p v ω => Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2) := by
  have hS1 := eta1_S1 d P c₀ c₁ κ C₁ hc₀ hc₁ hκ hκ2
  have hsz := tendsto_sizeW_admFilterL c₀ c₁
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨W_K, Cs, hCs0, hK⟩ := eta1_kernel d (by omega) P c₀ c₁ κ c₀ 1 hc₀ hc₁ hκ hc₀ one_pos
  refine offDiagGT d P c₀ c₁ hc₀ hc₁ κ c₀ ((d : ℝ) / 4) (C₁ + 3) hκ (by positivity)
    (fun p => ↥(eta1Net κ C₁ p)) (fun p u => u.1) (fun p _ => sizeW p ^ (-(d : ℝ) / 2)) ?_ ?_ ?_
  · -- the cardinality
    filter_upwards [hsz.eventually (eventually_ge_atTop 6)] with p hp
    rw [Fintype.card_coe]
    refine (eta1Net_card hκ2 hκ hC₁ (by linarith)).trans ?_
    have hW0 : (0 : ℝ) < sizeW p := by linarith
    calc 6 * sizeW p ^ C₁ ≤ sizeW p ^ (3 : ℝ) * sizeW p ^ C₁ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : (6 : ℝ) ≤ sizeW p := hp
          calc (6 : ℝ) ≤ sizeW p := this
            _ = sizeW p ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ sizeW p ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = sizeW p ^ (C₁ + 3) := by rw [← Real.rpow_add hW0]; congr 1; ring
  · -- the parameters
    filter_upwards [eta1_ev_adm c₀ c₁, hsz.eventually (eventually_ge_atTop 1)] with p hp hW u
    have hW0 : (0 : ℝ) < sizeW p := by linarith
    obtain ⟨him, hre, -⟩ := eta1Net_prop hκ2 u.2
    have hWn : 1 ≤ p.1.1 := by
      have h1 : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW
      exact_mod_cast h1
    refine ⟨eta1_specDom_of hc₀ (by linarith) hp hWn him hre, le_rfl, ?_⟩
    exact Real.rpow_le_rpow_of_exponent_le hW (by
      have : (0 : ℝ) < d := hd0
      linarith)
  · refine ⟨?_, ?_⟩
    · refine eta1_sd_mono (hsz.eventually (eventually_ge_atTop 0)) ?_ hS1
      filter_upwards [hsz.eventually (eventually_ge_atTop 1)] with p hp u ω
      exact Real.rpow_le_rpow_of_exponent_le hp (by
        have : (0 : ℝ) < d := hd0
        linarith)
    · refine eta1_sd_det hS1 ?_
      intro τ hτ
      refine ⟨τ / 4, by positivity, ?_⟩
      have hev : ∀ᶠ W : ℝ in atTop, 2 + 2 * Cs ≤ W ^ (τ / 2) := 
        (tendsto_rpow_atTop (by positivity : 0 < τ / 2)).eventually_ge_atTop _
      filter_upwards [eta1_ev_adm c₀ c₁, hsz.eventually (eventually_ge_atTop W_K),
        hsz.eventually (eventually_ge_atTop 1), hsz.eventually hev] with p hp hWK hW1 hWτ ω hω v
      obtain ⟨u, x, y⟩ := v
      obtain ⟨⟨hsymm, hnn, hrow, hSle⟩, -⟩ := hK p.1.1 p.1.2 hp hWK
      have hW0 : (0 : ℝ) < sizeW p := by linarith
      obtain ⟨him, hre, -⟩ := eta1Net_prop hκ2 u.2
      have hm1 : ‖msc u.1‖ ≤ 1 := (norm_msc_lt_one (by rw [him]; exact one_pos)).le
      have hT := eta1_T_small (Smat P.ψ p.1.1 p.1.2) hnn hrow (green (hmat ω) u.1) (msc u.1) hm1
        (sizeW p ^ (τ / 4) * sizeW p ^ (-(d : ℝ) / 2)) (Cs / (sizeW p) ^ d) x y (hSle x y)
        (fun α => hω (u, α, y))
      refine hT.trans ?_
      have hV2 : (sizeW p ^ (-(d : ℝ) / 2)) ^ 2 = sizeW p ^ (-(d : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
      have hCsV : Cs / (sizeW p) ^ d = Cs * (sizeW p ^ (-(d : ℝ) / 2)) ^ 2 := by
        rw [hV2, Real.rpow_neg hW0.le, Real.rpow_natCast, div_eq_mul_inv]
      have hy2 : (sizeW p ^ (τ / 4)) ^ 2 = sizeW p ^ (τ / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
      have hyy : sizeW p ^ τ = (sizeW p ^ (τ / 2)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
      have hV0 : 0 ≤ (sizeW p ^ (-(d : ℝ) / 2)) ^ 2 := sq_nonneg _
      rw [hCsV, mul_pow, hy2, hyy]
      set y := sizeW p ^ (τ / 2) with hy
      set V2 := (sizeW p ^ (-(d : ℝ) / 2)) ^ 2 with hV2'
      have hy0 : 2 + 2 * Cs ≤ y := hWτ
      have h1 : 2 * y + 2 * Cs ≤ y ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 hV0]

end NetProb



section NetSD

private theorem eta1_netSD (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ C₁ : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (hκ2 : κ < 2) (hC₁ : 0 ≤ C₁) :
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
      (U := fun p => (Zd d p.1.2 × Zd d p.1.2) × ↥(eta1Net κ C₁ p))
      (fun p q ω => ‖entryErr (green (hmat ω) q.2.1) (msc q.2.1) q.1.1 q.1.2‖ ^ 2)
      (fun p q _ => bB d p.1.2 p.1.1 q.1.1 q.1.2) := by
  have hsz := tendsto_sizeW_admFilterL c₀ c₁
  have hS1 := eta1_S1 d P c₀ c₁ κ C₁ hc₀ hc₁ hκ hκ2
  have hS2 := eta1_S2 d hd P c₀ c₁ κ C₁ hc₀ hc₁ hκ hκ2 hC₁
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine StochDom.of_forall _ _ _ _ _ (C₁ + 2 * (d : ℝ) / c₁ + 3) hsz ?_ ?_
  · -- the cardinality
    filter_upwards [hsz.eventually (eventually_ge_atTop 6), eta1_ev_adm c₀ c₁] with p hp hadm
    have hW0 : (0 : ℝ) < sizeW p := by linarith
    have hL1 : (1 : ℝ) ≤ p.1.2 := by exact_mod_cast Nat.pos_of_ne_zero p.2
    have hLW : (p.1.2 : ℝ) ≤ sizeW p ^ (1 / c₁) := by
      have h1 := Real.rpow_le_rpow (by positivity) hadm.1 (by positivity : (0 : ℝ) ≤ 1 / c₁)
      rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hc₁.ne', Real.rpow_one] at h1
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, card_Zd]
    push_cast
    have h1 := eta1Net_card hκ2 hκ hC₁ (p := p) (by linarith)
    have hLd : (p.1.2 : ℝ) ^ d * (p.1.2 : ℝ) ^ d ≤ sizeW p ^ (2 * (d : ℝ) / c₁) := by
      calc (p.1.2 : ℝ) ^ d * (p.1.2 : ℝ) ^ d ≤ (sizeW p ^ (1 / c₁)) ^ d * (sizeW p ^ (1 / c₁)) ^ d :=
            mul_le_mul (pow_le_pow_left₀ (by positivity) hLW _) (pow_le_pow_left₀ (by positivity) hLW _)
              (by positivity) (by positivity)
        _ = sizeW p ^ (2 * (d : ℝ) / c₁) := by
            rw [← pow_two, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
            congr 1; push_cast; ring
    have h3 : (6 : ℝ) ≤ sizeW p ^ (3 : ℝ) := by
      calc (6 : ℝ) ≤ sizeW p := hp
        _ = sizeW p ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ sizeW p ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc ((p.1.2 : ℝ) ^ d * (p.1.2 : ℝ) ^ d) * ((eta1Net κ C₁ p).card : ℝ)
        ≤ sizeW p ^ (2 * (d : ℝ) / c₁) * (6 * sizeW p ^ C₁) :=
          mul_le_mul hLd h1 (by positivity) (by positivity)
      _ ≤ sizeW p ^ (2 * (d : ℝ) / c₁) * (sizeW p ^ (3 : ℝ) * sizeW p ^ C₁) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity)
      _ = sizeW p ^ (C₁ + 2 * (d : ℝ) / c₁ + 3) := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring
  · intro τ hτ D hD
    obtain ⟨τ₁, D₁, W₀, hτ₁, hD₁, hmain⟩ := eta1_tail_z d hd P c₀ c₁ κ hc₀ hc₁ hκ τ D hτ hD
    filter_upwards [hS1 τ₁ hτ₁ D₁ hD₁, hS2 τ₁ hτ₁ D₁ hD₁, eta1_ev_adm c₀ c₁,
      hsz.eventually (eventually_ge_atTop (max W₀ 1))] with p h1 h2 hadm hW u
    obtain ⟨⟨x, y⟩, w, hw⟩ := u
    obtain ⟨him, hre, -⟩ := eta1Net_prop hκ2 hw
    have hW₀ : W₀ ≤ (p.1.1 : ℝ) := (le_max_left _ _).trans hW
    have hP1 : gaussLaw (Smat P.ψ p.1.1 p.1.2) {ω | ¬ ∀ k l,
        ‖entryErr (green (hmat ω) w) (msc w) k l‖ ≤ (p.1.1 : ℝ) ^ τ₁ * (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)} ≤
        ENNReal.ofReal ((p.1.1 : ℝ) ^ (-D₁)) := by
      refine le_trans (measure_mono ?_) h1
      intro ω hω
      simp only [Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨k, l, hkl⟩ := hω
      exact ⟨(⟨w, hw⟩, k, l), hkl⟩
    have hP2 : gaussLaw (Smat P.ψ p.1.1 p.1.2) {ω | ¬ ∀ k l, k ≠ l → ‖green (hmat ω) w k l‖ ^ 2 ≤
        (p.1.1 : ℝ) ^ τ₁ * Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) w) (msc w) k l} ≤
        ENNReal.ofReal ((p.1.1 : ℝ) ^ (-D₁)) := by
      refine le_trans (measure_mono ?_) h2
      intro ω hω
      simp only [Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨k, l, hkl, hlt⟩ := hω
      refine ⟨(⟨w, hw⟩, k, l), ?_⟩
      show (p.1.1 : ℝ) ^ τ₁ * Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) w) (msc w) k l <
        if k = l then 0 else ‖green (hmat ω) w k l‖ ^ 2
      rw [ite_eq_right hkl]; exact hlt
    exact hmain p.1.1 p.1.2 hadm hW₀ w him hre hP1 hP2 x y

end NetSD



section Lip

/-- `|G_{ij}(z) − G_{ij}(w)| ≤ |z − w| / (Im z · Im w)`. -/
private theorem eta1_green_lip {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (i j : ι) :
    ‖green H z i j - green H w i j‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) (green_sub_green hH hz.ne' hw.ne')
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
  rw [h, norm_mul]
  have hrow := sum_norm_sq_green_row hH hz i
  have hcol := sum_norm_sq_green_col hH hw j
  have hgi : (green H z i i).im ≤ (z.im)⁻¹ := by
    have := norm_green_entry_le hH hz.ne' i i
    rw [abs_of_pos hz] at this
    exact (Complex.im_le_norm _).trans this
  have hgj : (green H w j j).im ≤ (w.im)⁻¹ := by
    have := norm_green_entry_le hH hw.ne' j j
    rw [abs_of_pos hw] at this
    exact (Complex.im_le_norm _).trans this
  have hA : ∑ k, ‖green H z i k‖ ^ 2 ≤ (z.im)⁻¹ ^ 2 := by
    rw [hrow, div_eq_mul_inv, sq]
    exact mul_le_mul_of_nonneg_right hgi (inv_nonneg.2 hz.le)
  have hB : ∑ k, ‖green H w k j‖ ^ 2 ≤ (w.im)⁻¹ ^ 2 := by
    rw [hcol, div_eq_mul_inv, sq]
    exact mul_le_mul_of_nonneg_right hgj (inv_nonneg.2 hw.le)
  have hsum : ‖∑ k, green H z i k * green H w k j‖ ≤ (z.im)⁻¹ * (w.im)⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    simp_rw [norm_mul]
    refine le_of_sq_le_sq ?_ (by positivity)
    calc (∑ k, ‖green H z i k‖ * ‖green H w k j‖) ^ 2
        ≤ (∑ k, ‖green H z i k‖ ^ 2) * ∑ k, ‖green H w k j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (z.im)⁻¹ ^ 2 * (w.im)⁻¹ ^ 2 :=
          mul_le_mul hA hB (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
      _ = ((z.im)⁻¹ * (w.im)⁻¹) ^ 2 := by ring
  calc ‖z - w‖ * ‖∑ k, green H z i k * green H w k j‖
      ≤ ‖z - w‖ * ((z.im)⁻¹ * (w.im)⁻¹) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖z - w‖ / (z.im * w.im) := by field_simp

/-- `1 − |m(z)| ≥ Im z / 4` for `0 < Im z ≤ 1`. -/
private theorem eta1_one_sub_norm_msc {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    z.im / 4 ≤ 1 - ‖msc z‖ := by
  have him := msc_im_pos hz
  have hlt := norm_msc_lt_one hz
  have hm0 : msc z ≠ 0 := msc_ne_zero z
  have hinv : msc z + z = -(msc z)⁻¹ := msc_add_eq_neg_inv z
  have hN : 0 < Complex.normSq (msc z) := Complex.normSq_pos.mpr hm0
  have key : ((msc z).im + z.im) * Complex.normSq (msc z) = (msc z).im := by
    have := congrArg Complex.im hinv
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at this
    rw [this]
    field_simp
  rw [Complex.normSq_eq_norm_sq] at key
  have hle : (msc z).im ≤ ‖msc z‖ := Complex.im_le_norm _
  have hn0 := norm_nonneg (msc z)
  nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (sub_nonneg.2 hlt.le)]

/-- `|m(z) − m(w)| ≤ 4 |z − w| / Im z` for `0 < Im z ≤ 1` and `Im w > 0`. -/
private theorem eta1_msc_lip {z w : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hw : 0 < w.im) :
    ‖msc z - msc w‖ ≤ 4 * ‖z - w‖ / z.im := by
  have hm := msc_mul z
  have hm' := msc_mul w
  have key : (msc z - msc w) * (1 - msc z * msc w) = (z - w) * (msc z * msc w) := by
    linear_combination (-msc w) * hm + msc z * hm'
  have h1 := eta1_one_sub_norm_msc hz hz1
  have hl := norm_msc_lt_one hz
  have hl' := norm_msc_lt_one hw
  have hn0 := norm_nonneg (msc z)
  have hn0' := norm_nonneg (msc w)
  have hlow : z.im / 4 ≤ ‖1 - msc z * msc w‖ := by
    have : 1 - ‖msc z * msc w‖ ≤ ‖1 - msc z * msc w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (msc z * msc w)
      simpa using this
    rw [norm_mul] at this
    nlinarith
  have hn := congrArg norm key
  rw [norm_mul, norm_mul, norm_mul] at hn
  have hprod : ‖msc z‖ * ‖msc w‖ ≤ 1 := by nlinarith
  have hzw := norm_nonneg (z - w)
  have hle : ‖msc z - msc w‖ * (z.im / 4) ≤ ‖z - w‖ := by
    calc ‖msc z - msc w‖ * (z.im / 4) ≤ ‖msc z - msc w‖ * ‖1 - msc z * msc w‖ :=
          mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = ‖z - w‖ * (‖msc z‖ * ‖msc w‖) := hn
      _ ≤ ‖z - w‖ * 1 := mul_le_mul_of_nonneg_left hprod hzw
      _ = ‖z - w‖ := mul_one _
  rw [le_div_iff₀ hz]
  nlinarith

/-- The Lipschitz bound of `|G_{xy} − δ_{xy} m|²` on the line `Im z = 1`. -/
private theorem eta1_xi_lip {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z w : ℂ} (hz : z.im = 1) (hw : w.im = 1) (x y : ι) :
    |‖entryErr (green H z) (msc z) x y‖ ^ 2 - ‖entryErr (green H w) (msc w) x y‖ ^ 2| ≤
      20 * ‖z - w‖ := by
  have hz0 : 0 < z.im := by rw [hz]; exact one_pos
  have hw0 : 0 < w.im := by rw [hw]; exact one_pos
  have h1 := eta1_green_lip hH hz0 hw0 x y
  rw [hz, hw, one_mul, div_one] at h1
  have h2 := eta1_msc_lip hz0 (le_of_eq hz) hw0
  rw [hz, div_one] at h2
  have hG : ∀ v : ℂ, v.im = 1 → ‖green H v x y‖ ≤ 1 := fun v hv => by
    have := norm_green_entry_le hH (by rw [hv]; exact one_ne_zero) x y
    rw [hv] at this; simpa using this
  have hm : ∀ v : ℂ, v.im = 1 → ‖msc v‖ ≤ 1 := fun v hv =>
    (norm_msc_lt_one (by rw [hv]; exact one_pos)).le
  have ha : ‖entryErr (green H z) (msc z) x y‖ ≤ 2 := by
    unfold entryErr
    split_ifs
    · exact (norm_sub_le _ _).trans (by linarith [hG z hz, hm z hz])
    · rw [sub_zero]; linarith [hG z hz]
  have hb : ‖entryErr (green H w) (msc w) x y‖ ≤ 2 := by
    unfold entryErr
    split_ifs
    · exact (norm_sub_le _ _).trans (by linarith [hG w hw, hm w hw])
    · rw [sub_zero]; linarith [hG w hw]
  have hab : |‖entryErr (green H z) (msc z) x y‖ - ‖entryErr (green H w) (msc w) x y‖| ≤
      5 * ‖z - w‖ := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have e : entryErr (green H z) (msc z) x y - entryErr (green H w) (msc w) x y =
        (green H z x y - green H w x y) - (if x = y then msc z - msc w else 0) := by
      unfold entryErr; split_ifs <;> ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    split_ifs
    · linarith
    · simp only [norm_zero]; linarith [norm_nonneg (z - w)]
  have e2 : ‖entryErr (green H z) (msc z) x y‖ ^ 2 - ‖entryErr (green H w) (msc w) x y‖ ^ 2 =
      (‖entryErr (green H z) (msc z) x y‖ - ‖entryErr (green H w) (msc w) x y‖) *
        (‖entryErr (green H z) (msc z) x y‖ + ‖entryErr (green H w) (msc w) x y‖) := by ring
  rw [e2, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖entryErr (green H z) (msc z) x y‖ +
    ‖entryErr (green H w) (msc w) x y‖)]
  have := mul_le_mul hab (by linarith : ‖entryErr (green H z) (msc z) x y‖ +
    ‖entryErr (green H w) (msc w) x y‖ ≤ 4) (by positivity) (by positivity)
  nlinarith

end Lip



section Final

/-- **[II, Lemma 7.2] = [I, Lemma 5.2]**: the local law at `η = 1`. -/
theorem eta1Step_of : eta1Step_ofStmt := by
  intro _hdc d hd P c₀ c₁ κ hc₀ hc₁ hc hκ
  by_cases hκ2 : 2 ≤ κ
  · intro τ hτ D hD
    refine Filter.Eventually.of_forall fun p => ?_
    have hempty : {ω | ∃ u : {E : ℝ // |E| < 2 - κ} × Zd d p.1.2 × Zd d p.1.2,
        sizeW p ^ τ * bB d p.1.2 p.1.1 u.2.1 u.2.2 <
          ‖entryErr (green (hmat ω) ((u.1.1 : ℂ) + I)) (msc ((u.1.1 : ℂ) + I)) u.2.1 u.2.2‖ ^ 2} =
        (∅ : Set (Sample (Zd d p.1.2))) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      rintro ⟨⟨E, hE⟩, x, y⟩
      exfalso
      have := abs_nonneg E
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · push Not at hκ2
    have hsz := tendsto_sizeW_admFilterL c₀ c₁
    have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
    obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = 2 + ((d : ℝ) - 2) * (1 + 1 / c₁) := ⟨_, rfl⟩
    have hC₃0 : 0 ≤ C₃ := by
      have : 0 ≤ 1 / c₁ := by positivity
      rw [hC₃]; nlinarith
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = C₃ + 2 := ⟨_, rfl⟩
    have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; linarith
    have hnet := eta1_netSD d hd P c₀ c₁ κ C₁ hc₀ hc₁ hκ hκ2 hC₁0
    have hof := StochDom.of_net (V := fun p => Zd d p.1.2 × Zd d p.1.2) (admFilterL c₀ c₁) sizeW
      (rbmLaw d P) (fun p => {z : ℂ | z.im = 1 ∧ |z.re| < 2 - κ}) (eta1Net κ C₁)
      (fun p v z ω => ‖entryErr (green (hmat ω) z) (msc z) v.1 v.2‖ ^ 2)
      (fun p v z _ => bB d p.1.2 p.1.1 v.1 v.2) C₁ 1 C₃ hsz (by rw [hC₁]; linarith) ?_ ?_ ?_ hnet
    · refine eta1_sd_comp
        (U := fun p => (Zd d p.1.2 × Zd d p.1.2) × ↥{z : ℂ | z.im = 1 ∧ |z.re| < 2 - κ})
        (fun p u => ((u.2.1, u.2.2), ⟨(u.1.1 : ℂ) + I, by simpa using u.1.2⟩)) ?_ ?_ hof
      · intro p u ω; rfl
      · intro p u ω; rfl
    · filter_upwards [hsz.eventually (eventually_ge_atTop 1)] with p hp
      refine ⟨fun w hw => ?_, fun z hz => ?_⟩
      · obtain ⟨h1, h2, -⟩ := eta1Net_prop hκ2 hw
        exact ⟨h1, h2⟩
      · exact eta1Net_cover hκ2 (by linarith) hz.1 hz.2
    · filter_upwards [hsz.eventually (eventually_ge_atTop 20)] with p hp v ω z hz w hw
      refine ⟨?_, ?_⟩
      · have h := eta1_xi_lip (hmat_isHermitian ω) hz.1 hw.1 v.1 v.2
        refine h.trans ?_
        have : (20 : ℝ) ≤ sizeW p ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact hp
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      · simp only [sub_self, abs_zero]; positivity
    · filter_upwards [hsz.eventually (eventually_ge_atTop 2), eta1_ev_adm c₀ c₁] with p hp hadm v ω z hz
      have hp2 : 2 ≤ p.1.1 := by
        have h1 : (2 : ℝ) ≤ (p.1.1 : ℝ) := hp
        exact_mod_cast h1
      rw [hC₃]
      exact eta1_bB_lower (by omega) c₀ c₁ hc₀ hc₁ p.1.1 hadm hp2 v.1 v.2

end Final

end RBM8D
