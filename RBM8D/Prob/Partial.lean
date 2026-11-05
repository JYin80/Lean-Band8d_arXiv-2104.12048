import RBM8D.Prob.Model

/-!
# Partial expectations

The partial expectations P_x and Q_x = 1 − P_x of [I, §1.4] in the Gaussian model: integration over the coordinates of row and column x with the others frozen, and the laws they satisfy on bounded measurable functions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

universe u v w

namespace RBM8D

/-! ## Partial expectations ([I, §1.4]) -/

section Partial

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Integration over the coordinates in `A`, the others frozen at `ω`:
`P_A F (ω) = ∫ F(ω outside A, η on A) dP(η)`. -/
def partialExp (S : Matrix ι ι ℝ) (A : Finset (Coord ι)) (F : Sample ι → ℂ) (ω : Sample ι) :
    ℂ :=
  ∫ η, F (A.piecewise η ω) ∂(gaussLaw S)

/-- `F` does not depend on the coordinates in `A`. -/
def FreeOf (A : Finset (Coord ι)) (F : Sample ι → ℂ) : Prop :=
  ∀ ω η : Sample ι, F (A.piecewise η ω) = F ω

/-- `P_x`: the partial expectation over row and column `x` ([I, §1.4]). -/
def Pexp (S : Matrix ι ι ℝ) (x : ι) (F : Sample ι → ℂ) : Sample ι → ℂ :=
  partialExp S (rowCoords x) F

end Partial

/-- The laws of an expectation `E` and of partial expectations `P x` on a class `Adm` of
random variables; `Free x F` says that `F` does not depend on row `x`. -/
structure PQLaws {Ω : Type u} {ι : Type v} (Adm : (Ω → ℂ) → Prop) (E : (Ω → ℂ) → ℂ)
    (P : ι → (Ω → ℂ) → Ω → ℂ) (Free : ι → (Ω → ℂ) → Prop) : Prop where
  adm_const : ∀ c : ℂ, Adm fun _ => c
  adm_add : ∀ F G, Adm F → Adm G → Adm (F + G)
  adm_mul : ∀ F G, Adm F → Adm G → Adm (F * G)
  adm_conj : ∀ F, Adm F → Adm fun ω => star (F ω)
  adm_P : ∀ x F, Adm F → Adm (P x F)
  P_add : ∀ x F G, Adm F → Adm G → P x (F + G) = P x F + P x G
  P_const_mul : ∀ x (c : ℂ) F, P x (fun ω => c * F ω) = fun ω => c * P x F ω
  P_mul_free : ∀ x F g, Free x g → P x (g * F) = g * P x F
  P_of_free : ∀ x F, Free x F → P x F = F
  free_P : ∀ x F, Free x (P x F)
  P_comm : ∀ x y F, Adm F → P x (P y F) = P y (P x F)
  E_add : ∀ F G, Adm F → Adm G → E (F + G) = E F + E G
  E_P : ∀ x F, Adm F → E (P x F) = E F

/-! ## Integration over a set of coordinates -/

section Laws

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- `(ω, η) ↦ A.piecewise η ω`, which takes `η` on `A` and `ω` off `A`, is measurable. -/
private lemma measurable_piecewise (A : Finset (Coord ι)) :
    Measurable fun p : Sample ι × Sample ι => A.piecewise p.2 p.1 := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ A
  · simp only [Finset.piecewise_eq_of_mem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_snd
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_fst

private lemma measurable_piecewise_right (A : Finset (Coord ι)) (ω : Sample ι) :
    Measurable fun η : Sample ι => A.piecewise η ω :=
  (measurable_piecewise A).comp measurable_prodMk_left

/-- Overwriting twice on `A`: the second overwrite wins. -/
private lemma piecewise_piecewise_self (A : Finset (Coord ι)) (ω η η' : Sample ι) :
    A.piecewise η' (A.piecewise η ω) = A.piecewise η' ω := by
  funext c
  by_cases h : c ∈ A <;> simp [Finset.piecewise, h]

/-- Overwriting `ω` on `A` by `η` and then on `B` by `η'` is overwriting `η` on `B` by `η'` and the
result on `A ∪ B`. -/
private lemma piecewise_piecewise_union (A B : Finset (Coord ι)) (ω η η' : Sample ι) :
    B.piecewise η' (A.piecewise η ω) = (A ∪ B).piecewise (B.piecewise η' η) ω := by
  funext c
  by_cases hA : c ∈ A <;> by_cases hB : c ∈ B <;> simp [Finset.piecewise, hA, hB]

private lemma bddMeas_piecewise_right {F : Sample ι → ℂ} (hF : BddMeas F) (A : Finset (Coord ι))
    (ω : Sample ι) : BddMeas fun η => F (A.piecewise η ω) := by
  obtain ⟨hm, C, hC⟩ := hF
  exact ⟨hm.comp (measurable_piecewise_right A ω), C, fun η => hC _⟩

/-- Overwriting a sample on `A` by an independent copy has again the law of the sample. -/
private lemma measurePreserving_piecewise (S : Matrix ι ι ℝ) (A : Finset (Coord ι)) :
    MeasurePreserving (fun p : Sample ι × Sample ι => A.piecewise p.2 p.1)
      ((gaussLaw S).prod (gaussLaw S)) (gaussLaw S) := by
  refine ⟨measurable_piecewise A, ?_⟩
  unfold gaussLaw
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_piecewise A) (MeasurableSet.univ_pi hs)]
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

private lemma integrable_comp_piecewise (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : BddMeas F)
    (A : Finset (Coord ι)) :
    Integrable (fun p : Sample ι × Sample ι => F (A.piecewise p.2 p.1))
      ((gaussLaw S).prod (gaussLaw S)) := by
  have := isProbabilityMeasure_gaussLaw S
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound (hm.comp (measurable_piecewise A)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => hC _)

omit [DecidableEq ι] in
private lemma integrable_bddMeas (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : BddMeas F) :
    Integrable F (gaussLaw S) := by
  classical
  have := isProbabilityMeasure_gaussLaw S
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

private lemma integral_prod_piecewise (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : BddMeas F)
    (A : Finset (Coord ι)) :
    ∫ p, F (A.piecewise p.2 p.1) ∂((gaussLaw S).prod (gaussLaw S)) = ∫ ζ, F ζ ∂(gaussLaw S) := by
  have hmp := measurePreserving_piecewise S A
  have h := integral_map (μ := (gaussLaw S).prod (gaussLaw S)) hmp.measurable.aemeasurable
    (f := F) hF.1.aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

private lemma bddMeas_partialExp (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : BddMeas F)
    (A : Finset (Coord ι)) : BddMeas (partialExp S A F) := by
  have := isProbabilityMeasure_gaussLaw S
  obtain ⟨hm, C, hC⟩ := hF
  refine ⟨?_, C, fun ω => ?_⟩
  · have hs : StronglyMeasurable fun p : Sample ι × Sample ι => F (A.piecewise p.2 p.1) :=
      (hm.comp (measurable_piecewise A)).stronglyMeasurable
    exact (hs.integral_prod_right' (ν := gaussLaw S)).measurable
  · have h := norm_integral_le_of_norm_le_const (μ := gaussLaw S)
      (f := fun η => F (A.piecewise η ω)) (C := C) (Filter.Eventually.of_forall fun η => hC _)
    simpa [partialExp] using h

/-- `P_A P_B = P_{A ∪ B}` for bounded measurable `F`, with the hypotheses of the model dropped. -/
private lemma partialExp_partialExp_aux (S : Matrix ι ι ℝ) (A B : Finset (Coord ι))
    {F : Sample ι → ℂ} (hF : BddMeas F) :
    partialExp S A (partialExp S B F) = partialExp S (A ∪ B) F := by
  have := isProbabilityMeasure_gaussLaw S
  funext ω
  have hH : BddMeas fun ζ => F ((A ∪ B).piecewise ζ ω) := bddMeas_piecewise_right hF _ ω
  calc partialExp S A (partialExp S B F) ω
      = ∫ η, ∫ η', F ((A ∪ B).piecewise (B.piecewise η' η) ω) ∂(gaussLaw S) ∂(gaussLaw S) := by
        simp only [partialExp, piecewise_piecewise_union]
    _ = ∫ p, F ((A ∪ B).piecewise (B.piecewise p.2 p.1) ω) ∂((gaussLaw S).prod (gaussLaw S)) :=
        (integral_prod (fun p : Sample ι × Sample ι => F ((A ∪ B).piecewise
          (B.piecewise p.2 p.1) ω)) (integrable_comp_piecewise S hH B)).symm
    _ = ∫ ζ, F ((A ∪ B).piecewise ζ ω) ∂(gaussLaw S) := integral_prod_piecewise S hH B
    _ = partialExp S (A ∪ B) F ω := rfl

end Laws

/-- The partial expectations `P_x` of the model satisfy the laws of [I, §1.4] on bounded
measurable functions: linearity, `P_x (g F) = g P_x F` for `g` free of row `x`, `P_x F = F` for `F`
free of row `x`, `P_x P_y = P_y P_x` and `E P_x = E`. -/
theorem pqLaws_Pexp :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ), S.IsSymm → (∀ x y, 0 ≤ S x y) →
    PQLaws BddMeas (fun F => ∫ ω, F ω ∂(gaussLaw S)) (Pexp S)
      (fun x => FreeOf (rowCoords x)) := by
  intro ι _ _ S hS hnn
  have := isProbabilityMeasure_gaussLaw S
  refine
    { adm_const := fun c => ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
      adm_add := ?_
      adm_mul := ?_
      adm_conj := ?_
      adm_P := fun x F hF => bddMeas_partialExp S hF (rowCoords x)
      P_add := ?_
      P_const_mul := ?_
      P_mul_free := ?_
      P_of_free := ?_
      free_P := ?_
      P_comm := ?_
      E_add := ?_
      E_P := ?_ }
  · rintro F G ⟨hF, C, hC⟩ ⟨hG, D, hD⟩
    exact ⟨hF.add hG, C + D, fun ω => (norm_add_le _ _).trans (add_le_add (hC ω) (hD ω))⟩
  · rintro F G ⟨hF, C, hC⟩ ⟨hG, D, hD⟩
    refine ⟨hF.mul hG, C * D, fun ω => ?_⟩
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC ω) (hD ω) (norm_nonneg _) ((norm_nonneg _).trans (hC ω))
  · rintro F ⟨hF, C, hC⟩
    exact ⟨continuous_star.measurable.comp hF, C, fun ω => by simpa using hC ω⟩
  · intro x F G hF hG
    funext ω
    simp only [Pexp, partialExp, Pi.add_apply]
    exact integral_add (integrable_bddMeas S (bddMeas_piecewise_right hF _ ω))
      (integrable_bddMeas S (bddMeas_piecewise_right hG _ ω))
  · intro x c F
    funext ω
    simp only [Pexp, partialExp]
    exact integral_const_mul c _
  · intro x F g hg
    funext ω
    simp only [Pexp, partialExp, Pi.mul_apply, hg ω]
    exact integral_const_mul (g ω) _
  · intro x F hF
    funext ω
    simp only [Pexp, partialExp, hF ω]
    simp
  · intro x F ω η
    simp only [Pexp, partialExp, piecewise_piecewise_self]
  · intro x y F hF
    simp only [Pexp]
    rw [partialExp_partialExp_aux S _ _ hF, partialExp_partialExp_aux S _ _ hF, Finset.union_comm]
  · intro F G hF hG
    exact integral_add (integrable_bddMeas S hF) (integrable_bddMeas S hG)
  · intro x F hF
    change ∫ ω, partialExp S (rowCoords x) F ω ∂(gaussLaw S) = ∫ ω, F ω ∂(gaussLaw S)
    unfold partialExp
    rw [← integral_prod (fun p : Sample ι × Sample ι => F ((rowCoords x).piecewise p.2 p.1))
      (integrable_comp_piecewise S hF _)]
    exact integral_prod_piecewise S hF _

section Instance

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

end Instance

end RBM8D
