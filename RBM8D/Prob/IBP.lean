module

public import RBM8D.Prob.Partial
public import RBM8D.Prob.Wirtinger
public import RBM8D.Prob.Stein

@[expose] public section

/-!
# Gaussian integration by parts

The complex Gaussian integration by parts of [I, Lemma 2.4] in the model: E[h_ab F] = s_ab E[∂_{h_ba} F], also inside a partial expectation over a set of coordinates containing those of h_ab.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

universe u v w

namespace RBM8D

/-! ## One coordinate of the product law -/

/-- The one-dimensional Stein identity `E[X f(X)] = v E[f'(X)]` for a centred Gaussian of any
variance `v ≥ 0`, the degenerate case `v = 0` included. -/
private lemma stein_complex (var : ℝ≥0) {f f' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) :
    ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)
      = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  by_cases hv : var = 0
  · subst hv
    simp [gaussianReal_zero_var]
  · exact integral_mul_gaussianReal_complex hv hf hf'c hb hb'

section Coordinate

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Replacing the coordinate `c` of a sample by an independent copy: `(ω, t) ↦ ω` with `ω c`
replaced by `t` maps the law times the `c`-th Gaussian factor to the law. -/
private lemma measurePreserving_update (S : Matrix ι ι ℝ) (c : Coord ι) :
    MeasurePreserving (fun p : Sample ι × ℝ => Function.update p.1 c p.2)
      ((gaussLaw S).prod (gaussianReal 0 (coordVar S c))) (gaussLaw S) := by
  have hm : Measurable (fun p : Sample ι × ℝ => Function.update p.1 c p.2) := by
    refine Measurable.of_eval fun d => ?_
    by_cases hd : d = c
    · subst hd
      simpa using measurable_snd
    · simp only [Function.update_of_ne hd]
      exact (measurable_pi_apply d).comp measurable_fst
  refine ⟨hm, ?_⟩
  unfold gaussLaw
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : Sample ι × ℝ => Function.update p.1 c p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi (Function.update s c Set.univ) ×ˢ s c := by
    ext ⟨ω, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun d => ?_, by simpa using h c⟩
      by_cases hd : d = c
      · subst hd; simp
      · simpa [Function.update_of_ne hd] using h d
    · rintro ⟨h1, h2⟩ d
      by_cases hd : d = c
      · subst hd; simpa using h2
      · simpa [Function.update_of_ne hd] using h1 d
  have hprod : (fun d => gaussianReal 0 (coordVar S d) (Function.update s c Set.univ d))
      = Function.update (fun d => gaussianReal 0 (coordVar S d) (s d)) c 1 := by
    funext d
    by_cases hd : d = c
    · subst hd; simp
    · simp [Function.update_of_ne hd]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, hprod,
    Finset.prod_update_of_mem (Finset.mem_univ c),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ c)]
  ring

/-- Integration against the law, one coordinate at a time. -/
private lemma integral_update (S : Matrix ι ι ℝ) (c : Coord ι) {h : Sample ι → ℂ}
    (hh : Integrable h (gaussLaw S)) :
    ∫ ω, h ω ∂(gaussLaw S)
      = ∫ ω, ∫ t, h (Function.update ω c t) ∂(gaussianReal 0 (coordVar S c)) ∂(gaussLaw S) := by
  have hmp := measurePreserving_update S c
  have h1 := integral_map (μ := (gaussLaw S).prod (gaussianReal 0 (coordVar S c)))
    hmp.measurable.aemeasurable (f := h) (by rw [hmp.map_eq]; exact hh.aestronglyMeasurable)
  rw [hmp.map_eq] at h1
  rw [h1, integral_prod (fun p : Sample ι × ℝ => h (Function.update p.1 c p.2))
    ((hmp.integrable_comp hh.aestronglyMeasurable).mpr hh)]

private lemma hasDerivAt_update (ω : Sample ι) (c : Coord ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Function.update ω c s) (Pi.single c 1) t := by
  rw [hasDerivAt_pi]
  intro j
  by_cases h : j = c
  · subst h
    simpa using hasDerivAt_id' t
  · simpa [Function.update_of_ne h, Pi.single_eq_of_ne h] using hasDerivAt_const t (ω j)

/-- For a differentiable `F`, `∂_c F` is the derivative in the direction of the `c`-th unit
vector. -/
private lemma partialCoord_eq_fderiv {F : Sample ι → ℂ} (hF : Differentiable ℝ F) (c : Coord ι)
    (ω : Sample ι) : partialCoord c F ω = fderiv ℝ F ω (Pi.single c 1) := by
  unfold partialCoord
  have h1 : HasFDerivAt F (fderiv ℝ F ω) (Function.update ω c (ω c)) := by
    rw [Function.update_eq_self]; exact (hF ω).hasFDerivAt
  exact (h1.comp_hasDerivAt (ω c) (hasDerivAt_update ω c (ω c))).deriv

omit [DecidableEq ι] in
private lemma integrable_coord_mul (S : Matrix ι ι ℝ) (c : Coord ι) {G : Sample ι → ℂ} {C : ℝ}
    (hG : Continuous G) (hb : ∀ ω, ‖G ω‖ ≤ C) :
    Integrable (fun ω : Sample ι => (ω c : ℂ) * G ω) (gaussLaw S) := by
  have hmp := measurePreserving_eval (fun d => gaussianReal 0 (coordVar S d)) c
  have hc : Integrable (fun ω : Sample ι => ω c) (gaussLaw S) :=
    (hmp.integrable_comp measurable_id.aestronglyMeasurable).mpr integrable_id_gaussianReal
  refine (hc.ofReal.bdd_mul hG.aestronglyMeasurable (Eventually.of_forall hb)).congr
    (Eventually.of_forall fun ω => ?_)
  exact mul_comm _ _

/-- Stein's identity in the coordinate `c` of the law: `E[ω_c G] = σ_c² E[∂_c G]` for `G` of
class `C¹`, bounded with bounded derivative. -/
private lemma integral_coord_mul (S : Matrix ι ι ℝ) (c : Coord ι) {G : Sample ι → ℂ} {C : ℝ}
    (hG : ContDiff ℝ 1 G) (hb : ∀ ω, ‖G ω‖ ≤ C) (hb' : ∀ ω, ‖fderiv ℝ G ω‖ ≤ C) :
    ∫ ω, (ω c : ℂ) * G ω ∂(gaussLaw S)
      = ((coordVar S c : ℝ) : ℂ) * ∫ ω, partialCoord c G ω ∂(gaussLaw S) := by
  have : IsProbabilityMeasure (gaussLaw S) := by unfold gaussLaw; infer_instance
  have hd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hcd : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  set v : Sample ι := Pi.single c 1
  set K : ℝ := max C (C * ‖v‖)
  have hK : ∀ ω, ‖fderiv ℝ G ω v‖ ≤ K := fun ω =>
    ((fderiv ℝ G ω).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_right (hb' ω) (norm_nonneg v)).trans (le_max_right _ _))
  have hK0 : ∀ ω, ‖G ω‖ ≤ K := fun ω => (hb ω).trans (le_max_left _ _)
  have hdv : Continuous fun ω => fderiv ℝ G ω v :=
    (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp hcd
  have hint2 : Integrable (fun ω => fderiv ℝ G ω v) (gaussLaw S) :=
    Integrable.of_bound hdv.aestronglyMeasurable K (Eventually.of_forall hK)
  have hpc : partialCoord c G = fun ω => fderiv ℝ G ω v := funext (partialCoord_eq_fderiv hd c)
  rw [hpc, integral_update S c (integrable_coord_mul S c hd.continuous hb),
    integral_update S c hint2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Function.update_self]
  refine stein_complex _ (f := fun t => G (Function.update ω c t))
    (f' := fun t => fderiv ℝ G (Function.update ω c t) v) (C := K) (fun t => ?_) ?_
    (fun t => hK0 _) (fun t => hK _)
  · exact (hd _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update ω c t)
  · exact hdv.comp (continuous_const.update c continuous_id)

omit [DecidableEq ι] in
private lemma coordVar_inr (S : Matrix ι ι ℝ) (hnn : ∀ x y, 0 ≤ S x y) (e : OffPair ι)
    (β : Bool) : (coordVar S (.inr (e, β)) : ℝ) = S e.1.1 e.1.2 / 2 := by
  simp only [coordVar]
  exact Real.coe_toNNReal _ (by have := hnn e.1.1 e.1.2; positivity)

omit [DecidableEq ι] in
private lemma coordVar_inl (S : Matrix ι ι ℝ) (hnn : ∀ x y, 0 ≤ S x y) (x : ι) :
    (coordVar S (.inl x) : ℝ) = S x x :=
  Real.coe_toNNReal _ (hnn x x)

/-- `E[h_ab G] = s_ab E[∂_{h_ba} G]` for `G` of class `C¹`, bounded with bounded derivative. -/
private lemma integral_hmat_mul_aux (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ x y, 0 ≤ S x y)
    (a b : ι) {G : Sample ι → ℂ} {C : ℝ}
    (hG : ContDiff ℝ 1 G) (hb : ∀ ω, ‖G ω‖ ≤ C) (hb' : ∀ ω, ‖fderiv ℝ G ω‖ ≤ C) :
    ∫ ω, hmat ω a b * G ω ∂(gaussLaw S) = (S a b : ℂ) * ∫ ω, dh b a G ω ∂(gaussLaw S) := by
  have : IsProbabilityMeasure (gaussLaw S) := by unfold gaussLaw; infer_instance
  have hd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hcd : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hI : ∀ c : Coord ι, Integrable (fun ω : Sample ι => (ω c : ℂ) * G ω) (gaussLaw S) :=
    fun c => integrable_coord_mul S c hd.continuous hb
  have hP : ∀ c : Coord ι, Integrable (fun ω => partialCoord c G ω) (gaussLaw S) := by
    intro c
    have hpc : (fun ω => partialCoord c G ω) = fun ω => fderiv ℝ G ω (Pi.single c 1) :=
      funext (partialCoord_eq_fderiv hd c)
    rw [hpc]
    refine Integrable.of_bound ((ContinuousLinearMap.apply ℝ ℂ _).continuous.comp
      hcd).aestronglyMeasurable (C * ‖(Pi.single c 1 : Sample ι)‖)
      (Eventually.of_forall fun ω => ?_)
    exact ((fderiv ℝ G ω).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hb' ω) (norm_nonneg _))
  have key := fun c => integral_coord_mul S c hG hb hb'
  rcases lt_trichotomy (idxKey ι a) (idxKey ι b) with h | h | h
  · have hdh : ∀ ω, dh b a G ω = (1 / 2 : ℂ) * (partialCoord (.inr (⟨(a, b), h⟩, true)) G ω +
        I * partialCoord (.inr (⟨(a, b), h⟩, false)) G ω) := fun ω => by
      simp [dh, h, lt_asymm h]
    have hh : ∀ ω, hmat ω a b * G ω = (ω (.inr (⟨(a, b), h⟩, true)) : ℂ) * G ω +
        I * ((ω (.inr (⟨(a, b), h⟩, false)) : ℂ) * G ω) := fun ω => by
      simp only [hmat, Matrix.of_apply, h, dite_true]
      ring
    simp only [hh, hdh]
    rw [integral_add (hI _) ((hI _).const_mul I), integral_const_mul, integral_const_mul,
      integral_add (hP _) ((hP _).const_mul I), integral_const_mul, key, key,
      coordVar_inr S hnn, coordVar_inr S hnn]
    push_cast
    ring
  · obtain rfl := idxKey_injective h
    have hdh : ∀ ω, dh a a G ω = partialCoord (.inl a) G ω := fun ω => by simp [dh]
    have hh : ∀ ω, hmat ω a a * G ω = (ω (.inl a) : ℂ) * G ω := fun ω => by simp [hmat]
    simp only [hh, hdh]
    rw [key, coordVar_inl S hnn]
  · have hdh : ∀ ω, dh b a G ω = (1 / 2 : ℂ) * (partialCoord (.inr (⟨(b, a), h⟩, true)) G ω -
        I * partialCoord (.inr (⟨(b, a), h⟩, false)) G ω) := fun ω => by
      simp [dh, h]
    have hh : ∀ ω, hmat ω a b * G ω = (ω (.inr (⟨(b, a), h⟩, true)) : ℂ) * G ω -
        I * ((ω (.inr (⟨(b, a), h⟩, false)) : ℂ) * G ω) := fun ω => by
      simp only [hmat, Matrix.of_apply, h, lt_asymm h, dite_true, dite_false]
      ring
    simp only [hh, hdh]
    rw [integral_sub (hI _) ((hI _).const_mul I), integral_const_mul, integral_const_mul,
      integral_sub (hP _) ((hP _).const_mul I), integral_const_mul, key, key,
      coordVar_inr S hnn, coordVar_inr S hnn]
    simp only [hS.apply a b]
    push_cast
    ring

end Coordinate

/-! ## Restriction to a set of coordinates -/

section Restrict

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Keep the coordinates in `A` and set the others to zero. -/
private def restrictCLM (A : Finset (Coord ι)) : Sample ι →L[ℝ] Sample ι :=
  ContinuousLinearMap.pi fun c => if c ∈ A then ContinuousLinearMap.proj c else 0

private lemma restrictCLM_apply (A : Finset (Coord ι)) (η : Sample ι) (c : Coord ι) :
    restrictCLM A η c = if c ∈ A then η c else 0 := by
  simp only [restrictCLM, ContinuousLinearMap.pi_apply]
  split_ifs <;> simp

private lemma piecewise_eq_add (A : Finset (Coord ι)) (η ω : Sample ι) :
    A.piecewise η ω = restrictCLM A η + restrictCLM Aᶜ ω := by
  funext c
  simp only [Pi.add_apply, restrictCLM_apply, Finset.mem_compl, Finset.piecewise]
  split_ifs <;> simp

private lemma piecewise_update {A : Finset (Coord ι)} {c : Coord ι} (hc : c ∈ A)
    (η ω : Sample ι) (t : ℝ) :
    A.piecewise (Function.update η c t) ω = Function.update (A.piecewise η ω) c t := by
  funext d
  by_cases hd : d = c
  · subst hd
    simp [Finset.piecewise_eq_of_mem _ _ _ hc]
  · by_cases hdA : d ∈ A <;> simp [Finset.piecewise, hd, hdA]

private lemma partialCoord_piecewise {A : Finset (Coord ι)} {c : Coord ι} (hc : c ∈ A)
    (F : Sample ι → ℂ) (η ω : Sample ι) :
    partialCoord c (fun η' => F (A.piecewise η' ω)) η = partialCoord c F (A.piecewise η ω) := by
  simp only [partialCoord]
  rw [Finset.piecewise_eq_of_mem _ _ _ hc]
  congr 1
  funext t
  rw [piecewise_update hc]

private lemma entryCoords_comm (a b : ι) : entryCoords a b = entryCoords b a := by
  ext c
  rcases c with x | ⟨e, β⟩ <;> simp [entryCoords] <;> tauto

/-- `h_ab` depends only on the coordinates in `entryCoords a b`. -/
private lemma hmat_congr {ω ω' : Sample ι} (a b : ι)
    (h : ∀ c ∈ entryCoords a b, ω c = ω' c) : hmat ω a b = hmat ω' a b := by
  simp only [hmat, Matrix.of_apply]
  split_ifs with h1 h2
  · rw [h _ (by simp [entryCoords]), h _ (by simp [entryCoords])]
  · rw [h _ (by simp [entryCoords]), h _ (by simp [entryCoords])]
  · obtain rfl : a = b := idxKey_injective (le_antisymm (not_lt.1 h2) (not_lt.1 h1))
    rw [h _ (by simp [entryCoords])]

/-- `∂_{h_ab}` reads only the partial derivatives along the coordinates in `entryCoords a b`. -/
private lemma dh_congr {F G : Sample ι → ℂ} {ω ω' : Sample ι} (a b : ι)
    (h : ∀ c ∈ entryCoords a b, partialCoord c F ω = partialCoord c G ω') :
    dh a b F ω = dh a b G ω' := by
  simp only [dh]
  split_ifs with h1 h2
  · rw [h _ (by simp [entryCoords]), h _ (by simp [entryCoords])]
  · rw [h _ (by simp [entryCoords]), h _ (by simp [entryCoords])]
  · obtain rfl : a = b := idxKey_injective (le_antisymm (not_lt.1 h2) (not_lt.1 h1))
    rw [h _ (by simp [entryCoords])]

omit [DecidableEq ι] in
/-- A test function is of class `C¹`, bounded, with bounded derivative. -/
private lemma testFn_c1 {F : Sample ι → ℂ} (hF : TestFn F) :
    ∃ C : ℝ, ContDiff ℝ 1 F ∧ (∀ ω, ‖F ω‖ ≤ C) ∧ ∀ ω, ‖fderiv ℝ F ω‖ ≤ C := by
  obtain ⟨C₀, h₀⟩ := (hF 0).2
  obtain ⟨C₁, h₁⟩ := (hF 1).2
  refine ⟨max C₀ C₁, by simpa using (hF 1).1, fun ω => ?_, fun ω => ?_⟩
  · have := h₀ ω
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_max_left _ _)
  · have := h₁ ω
    rw [← zero_add 1, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
    exact this.trans (le_max_right _ _)

end Restrict

section Shift

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

end Shift

/-! ## Integration by parts ([I, Lemma 2.4]) -/

/-- **Integration by parts inside a partial expectation** (the Gaussian integration by parts in
the proof of [I, Lemma 2.4]): if `A` contains the coordinates of `h_ab`, then
`P_A[h_ab F] = s_ab P_A[∂_{h_ba} F]`, for all `a, b`, including `a = b`. -/
theorem partialExp_hmat_mul :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ), S.IsSymm → (∀ x y, 0 ≤ S x y) →
    ∀ (A : Finset (Coord ι)) (a b : ι), entryCoords a b ⊆ A → ∀ F : Sample ι → ℂ, TestFn F →
      ∀ ω, partialExp S A (fun ω' => hmat ω' a b * F ω') ω =
        (S a b : ℂ) * partialExp S A (dh b a F) ω := by
  intro ι _ _ S hS hnn A a b hA F hF ω
  obtain ⟨C, hF1, hb, hb'⟩ := testFn_c1 hF
  have hGeq : (fun η => F (A.piecewise η ω)) =
      fun η => F (restrictCLM A η + restrictCLM Aᶜ ω) :=
    funext fun η => by rw [piecewise_eq_add]
  have hG1 : ContDiff ℝ 1 fun η => F (A.piecewise η ω) := by
    rw [hGeq]
    exact hF1.comp ((restrictCLM A).contDiff.add contDiff_const)
  have hGd : ∀ η, HasFDerivAt (fun η => F (A.piecewise η ω))
      ((fderiv ℝ F (A.piecewise η ω)).comp (restrictCLM A)) η := by
    intro η
    rw [hGeq, piecewise_eq_add]
    exact ((hF1.differentiable one_ne_zero) _).hasFDerivAt.comp η
      ((restrictCLM A).hasFDerivAt.add_const _)
  have hGb' : ∀ η, ‖fderiv ℝ (fun η => F (A.piecewise η ω)) η‖ ≤ C * ‖restrictCLM A‖ :=
    fun η => by
      rw [(hGd η).fderiv]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hb' _) (norm_nonneg _))
  have key := integral_hmat_mul_aux S hS hnn a b hG1 (C := max C (C * ‖restrictCLM A‖))
    (fun η => (hb _).trans (le_max_left _ _)) (fun η => (hGb' η).trans (le_max_right _ _))
  have e1 : ∀ η, hmat (A.piecewise η ω) a b * F (A.piecewise η ω) =
      hmat η a b * F (A.piecewise η ω) := fun η => by
    rw [hmat_congr a b fun c hc => Finset.piecewise_eq_of_mem _ _ _ (hA hc)]
  have e2 : ∀ η, dh b a F (A.piecewise η ω) = dh b a (fun η' => F (A.piecewise η' ω)) η :=
    fun η => (dh_congr b a fun c hc =>
      partialCoord_piecewise (hA (entryCoords_comm a b ▸ hc)) F η ω).symm
  simp only [partialExp, e1, e2]
  exact key

/-- **Integration by parts** (the Gaussian integration by parts in the proof of
[I, Lemma 2.4]): `E[h_ab F] = s_ab E[∂_{h_ba} F]`, for all `a, b`, including `a = b`. -/
theorem integral_hmat_mul :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ), S.IsSymm → (∀ x y, 0 ≤ S x y) →
    ∀ (a b : ι) (F : Sample ι → ℂ), TestFn F →
      ∫ ω, hmat ω a b * F ω ∂(gaussLaw S) = (S a b : ℂ) * ∫ ω, dh b a F ω ∂(gaussLaw S) := by
  intro ι _ _ S hS hnn a b F hF
  obtain ⟨C, hF1, hb, hb'⟩ := testFn_c1 hF
  exact integral_hmat_mul_aux S hS hnn a b hF1 hb hb'

section Instance

end Instance

end RBM8D
