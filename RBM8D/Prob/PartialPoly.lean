import RBM8D.Prob.Partial
import RBM8D.Prob.Wirtinger
import RBM8D.Basic.Minor

/-!
# Functions of polynomial growth

The class `PolyMeas` of measurable functions of polynomial growth on the Gaussian sample space, and the laws of the partial expectations `P_x` of [I, §1.4] on it (`pqLaws_Pexp` covers bounded functions only).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal BigOperators

universe u v w

namespace RBM8D

section PolyGrowth

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Measurable functions of polynomial growth: `‖F ω‖ ≤ C (1 + ‖ω‖)^k`, with `‖ω‖` the sup norm
of the real coordinates of the sample. -/
def PolyMeas (F : Sample ι → ℂ) : Prop :=
  Measurable F ∧ ∃ (C : ℝ) (k : ℕ), ∀ ω, ‖F ω‖ ≤ C * (1 + ‖ω‖) ^ k

end PolyGrowth

/-! ## Elementary members of the class -/

section Elementary

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The constant of a polynomial growth bound is non-negative (evaluate at `ω = 0`). -/
private lemma polyMeas_bound {F : Sample ι → ℂ} (hF : PolyMeas F) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ ω, ‖F ω‖ ≤ C * (1 + ‖ω‖) ^ k := by
  obtain ⟨-, C, k, hC⟩ := hF
  refine ⟨C, k, ?_, hC⟩
  have h0 := hC 0
  rw [norm_zero, add_zero, one_pow, mul_one] at h0
  exact (norm_nonneg _).trans h0

omit [DecidableEq ι] in
private lemma one_le_one_add_norm (ω : Sample ι) : (1 : ℝ) ≤ 1 + ‖ω‖ :=
  le_add_of_nonneg_right (norm_nonneg _)

omit [DecidableEq ι] in
/-- Every entry `h_ab` is `s ω_c + t ω_d` for two coordinates `c, d` and `|s|, |t| ≤ 1`. -/
private lemma hmat_entry_form (a b : ι) :
    ∃ (c d : Coord ι) (s t : ℂ), ‖s‖ ≤ 1 ∧ ‖t‖ ≤ 1 ∧
      ∀ ω : Sample ι, hmat ω a b = s * (ω c : ℂ) + t * (ω d : ℂ) := by
  by_cases h : idxKey ι a < idxKey ι b
  · exact ⟨.inr (⟨(a, b), h⟩, true), .inr (⟨(a, b), h⟩, false), 1, I, by simp, by simp,
      fun ω => by simp [hmat, h]⟩
  · by_cases h' : idxKey ι b < idxKey ι a
    · exact ⟨.inr (⟨(b, a), h'⟩, true), .inr (⟨(b, a), h'⟩, false), 1, -I, by simp, by simp,
        fun ω => by simp [hmat, h, h', sub_eq_add_neg]⟩
    · exact ⟨.inl a, .inl a, 1, 0, by simp, by simp, fun ω => by simp [hmat, h, h']⟩

omit [DecidableEq ι] in
/-- `|h_ab(ω)| ≤ 2 ‖ω‖`. -/
private lemma norm_hmat_le (ω : Sample ι) (a b : ι) : ‖hmat ω a b‖ ≤ 2 * ‖ω‖ := by
  classical
  obtain ⟨c, d, s, t, hs, ht, he⟩ := hmat_entry_form a b
  rw [he ω]
  calc ‖s * (ω c : ℂ) + t * (ω d : ℂ)‖ ≤ ‖s‖ * ‖ω c‖ + ‖t‖ * ‖ω d‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    _ ≤ 1 * ‖ω‖ + 1 * ‖ω‖ :=
        add_le_add (mul_le_mul hs (norm_le_pi_norm ω c) (norm_nonneg _) zero_le_one)
          (mul_le_mul ht (norm_le_pi_norm ω d) (norm_nonneg _) zero_le_one)
    _ = 2 * ‖ω‖ := by ring

omit [DecidableEq ι] in
private lemma measurable_hmat_entry (a b : ι) : Measurable fun ω : Sample ι => hmat ω a b := by
  obtain ⟨c, d, s, t, -, -, he⟩ := hmat_entry_form a b
  simp only [he]
  fun_prop

end Elementary

/-- A bounded measurable function has polynomial growth, of degree `0`. -/
theorem polyMeas_of_bddMeas :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (F : Sample ι → ℂ), BddMeas F → PolyMeas F := by
  intro ι _ _ F hF
  obtain ⟨hm, C, hC⟩ := hF
  exact ⟨hm, C, 0, fun ω => by rw [pow_zero, mul_one]; exact hC ω⟩

/-- A test function (smooth, every derivative bounded) has polynomial growth. -/
theorem polyMeas_of_testFn :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (F : Sample ι → ℂ), TestFn F → PolyMeas F := by
  intro ι _ _ F hF
  exact polyMeas_of_bddMeas F (testFn_closed.2.2.2.2.2 F hF)

/-- The entries `h_ab` of `H(ω)` ([I, Assumption 1.1]) have polynomial growth of degree `1`:
`|h_ab(ω)| ≤ 2 (1 + ‖ω‖)`. -/
theorem polyMeas_hmat :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (a b : ι), PolyMeas fun ω : Sample ι => hmat ω a b := by
  intro ι _ _ a b
  refine ⟨measurable_hmat_entry a b, 2, 1, fun ω => ?_⟩
  rw [pow_one]
  linarith [norm_hmat_le ω a b]

/-! ## Integrability -/

section Integrability

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every coordinate of the sample has finite moments of every order. -/
private lemma coord_memLp_nat (S : Matrix ι ι ℝ) (c : Coord ι) (k : ℕ) :
    MemLp (fun ω : Sample ι => ω c) k (gaussLaw S) := by
  have h : MemLp (id : ℝ → ℝ) (k : ℝ≥0) (gaussianReal 0 (coordVar S c)) :=
    memLp_id_gaussianReal (k : ℝ≥0)
  rw [ENNReal.coe_natCast] at h
  exact h.comp_measurePreserving (measurePreserving_eval (fun c => gaussianReal 0 (coordVar S c)) c)

omit [DecidableEq ι] in
/-- `(1 + ‖ω‖)^k` is integrable for the law of [I, Assumption 1.1]. -/
private lemma integrable_one_add_norm_pow (S : Matrix ι ι ℝ) (k : ℕ) :
    Integrable (fun ω : Sample ι => (1 + ‖ω‖) ^ k) (gaussLaw S) := by
  classical
  have := isProbabilityMeasure_gaussLaw S
  have hg : MemLp (fun ω : Sample ι => 1 + ∑ c, ‖ω c‖) k (gaussLaw S) :=
    (memLp_const 1).add (memLp_finsetSum _ fun c _ => (coord_memLp_nat S c k).norm)
  refine hg.integrable_norm_pow'.mono' (by fun_prop) (Eventually.of_forall fun ω => ?_)
  have hsum : ‖ω‖ ≤ ∑ c, ‖ω c‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c =>
      Finset.single_le_sum (f := fun c => ‖ω c‖) (fun c _ => norm_nonneg _) (Finset.mem_univ c)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  gcongr

end Integrability

/-- A function of polynomial growth is integrable for the law of [I, Assumption 1.1], for every
variance matrix `S`: the coordinates of the sample have Gaussian moments of every order. -/
theorem integrable_of_polyMeas :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (F : Sample ι → ℂ),
    PolyMeas F → Integrable F (gaussLaw S) := by
  intro ι _ _ S F hF
  obtain ⟨hm, C, k, hC⟩ := hF
  exact ((integrable_one_add_norm_pow S k).const_mul C).mono' hm.aestronglyMeasurable
    (Eventually.of_forall hC)

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

/-- `1 + ‖A.piecewise η ω‖ ≤ (1 + ‖ω‖)(1 + ‖η‖)`. -/
private lemma one_add_norm_piecewise_le (A : Finset (Coord ι)) (η ω : Sample ι) :
    1 + ‖A.piecewise η ω‖ ≤ (1 + ‖ω‖) * (1 + ‖η‖) := by
  have h : ‖A.piecewise η ω‖ ≤ ‖ω‖ + ‖η‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c => ?_
    by_cases hc : c ∈ A
    · rw [Finset.piecewise_eq_of_mem _ _ _ hc]
      linarith [norm_le_pi_norm η c, norm_nonneg ω]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hc]
      linarith [norm_le_pi_norm ω c, norm_nonneg η]
  nlinarith [norm_nonneg ω, norm_nonneg η]

/-- The growth bound of `η ↦ F (A.piecewise η ω)`, uniform in `ω` up to `(1 + ‖ω‖)^k`. -/
private lemma norm_comp_piecewise_le {F : Sample ι → ℂ} {C : ℝ} {k : ℕ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖F ω‖ ≤ C * (1 + ‖ω‖) ^ k) (A : Finset (Coord ι)) (η ω : Sample ι) :
    ‖F (A.piecewise η ω)‖ ≤ C * (1 + ‖ω‖) ^ k * (1 + ‖η‖) ^ k := by
  calc ‖F (A.piecewise η ω)‖ ≤ C * (1 + ‖A.piecewise η ω‖) ^ k := hC _
    _ ≤ C * ((1 + ‖ω‖) * (1 + ‖η‖)) ^ k := by
        gcongr
        exact one_add_norm_piecewise_le A η ω
    _ = C * (1 + ‖ω‖) ^ k * (1 + ‖η‖) ^ k := by rw [mul_pow, mul_assoc]

private lemma polyMeas_piecewise_right {F : Sample ι → ℂ} (hF : PolyMeas F)
    (A : Finset (Coord ι)) (ω : Sample ι) : PolyMeas fun η => F (A.piecewise η ω) := by
  obtain ⟨C, k, hC0, hC⟩ := polyMeas_bound hF
  exact ⟨hF.1.comp (measurable_piecewise_right A ω), C * (1 + ‖ω‖) ^ k, k,
    fun η => norm_comp_piecewise_le hC0 hC A η ω⟩

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

private lemma integrable_comp_piecewise (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : PolyMeas F)
    (A : Finset (Coord ι)) :
    Integrable (fun p : Sample ι × Sample ι => F (A.piecewise p.2 p.1))
      ((gaussLaw S).prod (gaussLaw S)) :=
  ((measurePreserving_piecewise S A).integrable_comp hF.1.aestronglyMeasurable).2
    (integrable_of_polyMeas S F hF)

private lemma integral_prod_piecewise (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : Measurable F)
    (A : Finset (Coord ι)) :
    ∫ p, F (A.piecewise p.2 p.1) ∂((gaussLaw S).prod (gaussLaw S)) = ∫ ζ, F ζ ∂(gaussLaw S) := by
  have hmp := measurePreserving_piecewise S A
  have h := integral_map (μ := (gaussLaw S).prod (gaussLaw S)) hmp.measurable.aemeasurable
    (f := F) hF.aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

/-- `P_A F` has polynomial growth with the degree of `F`. -/
private lemma polyMeas_partialExp (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : PolyMeas F)
    (A : Finset (Coord ι)) : PolyMeas (partialExp S A F) := by
  have := isProbabilityMeasure_gaussLaw S
  obtain ⟨C, k, hC0, hC⟩ := polyMeas_bound hF
  refine ⟨?_, C * ∫ η, (1 + ‖η‖) ^ k ∂(gaussLaw S), k, fun ω => ?_⟩
  · have hs : StronglyMeasurable fun p : Sample ι × Sample ι => F (A.piecewise p.2 p.1) :=
      (hF.1.comp (measurable_piecewise A)).stronglyMeasurable
    exact (hs.integral_prod_right' (ν := gaussLaw S)).measurable
  · have h := norm_integral_le_of_norm_le
      ((integrable_one_add_norm_pow S k).const_mul (C * (1 + ‖ω‖) ^ k))
      (Eventually.of_forall fun η => norm_comp_piecewise_le hC0 hC A η ω)
    rw [integral_const_mul] at h
    calc ‖partialExp S A F ω‖ ≤ C * (1 + ‖ω‖) ^ k * ∫ η, (1 + ‖η‖) ^ k ∂(gaussLaw S) := h
      _ = C * (∫ η, (1 + ‖η‖) ^ k ∂(gaussLaw S)) * (1 + ‖ω‖) ^ k := by ring

/-- `P_A P_B = P_{A ∪ B}` on functions of polynomial growth. -/
private lemma partialExp_partialExp_poly (S : Matrix ι ι ℝ) (A B : Finset (Coord ι))
    {F : Sample ι → ℂ} (hF : PolyMeas F) :
    partialExp S A (partialExp S B F) = partialExp S (A ∪ B) F := by
  have := isProbabilityMeasure_gaussLaw S
  funext ω
  have hH : PolyMeas fun ζ => F ((A ∪ B).piecewise ζ ω) := polyMeas_piecewise_right hF _ ω
  calc partialExp S A (partialExp S B F) ω
      = ∫ η, ∫ η', F ((A ∪ B).piecewise (B.piecewise η' η) ω) ∂(gaussLaw S) ∂(gaussLaw S) := by
        simp only [partialExp, piecewise_piecewise_union]
    _ = ∫ p, F ((A ∪ B).piecewise (B.piecewise p.2 p.1) ω) ∂((gaussLaw S).prod (gaussLaw S)) :=
        (integral_prod (fun p : Sample ι × Sample ι => F ((A ∪ B).piecewise
          (B.piecewise p.2 p.1) ω)) (integrable_comp_piecewise S hH B)).symm
    _ = ∫ ζ, F ((A ∪ B).piecewise ζ ω) ∂(gaussLaw S) := integral_prod_piecewise S hH.1 B
    _ = partialExp S (A ∪ B) F ω := rfl

end Laws

/-- The partial expectations `P_x` of [I, §1.4] satisfy the laws `PQLaws` on functions of
polynomial growth, with `E` the Gaussian integral and `Free x` the functions that do not depend on
row and column `x`: the class is closed under constants, sums, products, conjugation and `P_x`;
`P_x` is linear, `P_x (g F) = g P_x F` for `g` free of row `x`, `P_x F = F` for `F` free of row
`x`, `P_x F` is free of row `x`, `P_x P_y = P_y P_x`, and `E P_x = E`. -/
theorem pqLaws_Pexp_poly :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ), S.IsSymm → (∀ x y, 0 ≤ S x y) →
    PQLaws PolyMeas (fun F => ∫ ω, F ω ∂(gaussLaw S)) (Pexp S) (fun x => FreeOf (rowCoords x)) := by
  intro ι _ _ S _ _
  have := isProbabilityMeasure_gaussLaw S
  refine
    { adm_const := fun c => ⟨measurable_const, ‖c‖, 0, fun _ => by simp⟩
      adm_add := ?_
      adm_mul := ?_
      adm_conj := ?_
      adm_P := fun x F hF => polyMeas_partialExp S hF (rowCoords x)
      P_add := ?_
      P_const_mul := ?_
      P_mul_free := ?_
      P_of_free := ?_
      free_P := ?_
      P_comm := ?_
      E_add := ?_
      E_P := ?_ }
  · intro F G hF hG
    obtain ⟨C, k, hC0, hC⟩ := polyMeas_bound hF
    obtain ⟨D, m, hD0, hD⟩ := polyMeas_bound hG
    refine ⟨hF.1.add hG.1, C + D, max k m, fun ω => ?_⟩
    have h1 : (1 + ‖ω‖) ^ k ≤ (1 + ‖ω‖) ^ max k m :=
      pow_le_pow_right₀ (one_le_one_add_norm ω) (le_max_left _ _)
    have h2 : (1 + ‖ω‖) ^ m ≤ (1 + ‖ω‖) ^ max k m :=
      pow_le_pow_right₀ (one_le_one_add_norm ω) (le_max_right _ _)
    calc ‖(F + G) ω‖ ≤ ‖F ω‖ + ‖G ω‖ := norm_add_le _ _
      _ ≤ C * (1 + ‖ω‖) ^ k + D * (1 + ‖ω‖) ^ m := add_le_add (hC ω) (hD ω)
      _ ≤ C * (1 + ‖ω‖) ^ max k m + D * (1 + ‖ω‖) ^ max k m :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hC0) (mul_le_mul_of_nonneg_left h2 hD0)
      _ = (C + D) * (1 + ‖ω‖) ^ max k m := by ring
  · intro F G hF hG
    obtain ⟨C, k, hC0, hC⟩ := polyMeas_bound hF
    obtain ⟨D, m, hD0, hD⟩ := polyMeas_bound hG
    refine ⟨hF.1.mul hG.1, C * D, k + m, fun ω => ?_⟩
    rw [Pi.mul_apply, norm_mul]
    calc ‖F ω‖ * ‖G ω‖ ≤ (C * (1 + ‖ω‖) ^ k) * (D * (1 + ‖ω‖) ^ m) :=
          mul_le_mul (hC ω) (hD ω) (norm_nonneg _) (by positivity)
      _ = C * D * (1 + ‖ω‖) ^ (k + m) := by ring
  · rintro F ⟨hF, C, k, hC⟩
    exact ⟨continuous_star.measurable.comp hF, C, k, fun ω => by simpa using hC ω⟩
  · intro x F G hF hG
    funext ω
    simp only [Pexp, partialExp, Pi.add_apply]
    exact integral_add (integrable_of_polyMeas S _ (polyMeas_piecewise_right hF _ ω))
      (integrable_of_polyMeas S _ (polyMeas_piecewise_right hG _ ω))
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
    rw [partialExp_partialExp_poly S _ _ hF, partialExp_partialExp_poly S _ _ hF,
      Finset.union_comm]
  · intro F G hF hG
    exact integral_add (integrable_of_polyMeas S F hF) (integrable_of_polyMeas S G hG)
  · intro x F hF
    change ∫ ω, partialExp S (rowCoords x) F ω ∂(gaussLaw S) = ∫ ω, F ω ∂(gaussLaw S)
    unfold partialExp
    rw [← integral_prod (fun p : Sample ι × Sample ι => F ((rowCoords x).piecewise p.2 p.1))
      (integrable_comp_piecewise S hF _)]
    exact integral_prod_piecewise S hF.1 _

/-! ## Resolvent entries -/

section Resolvent

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private lemma measurable_green_entry {z : ℂ} (hz : 0 < z.im) (a b : ι) :
    Measurable fun ω : Sample ι => green (hmat ω) z a b :=
  (testFn_closed.2.2.2.2.2 _ (testFn_green z hz.ne' a b)).1

/-- For `a, b ≠ x`, `|G^{(x)}_{ab}| ≤ (Im z)⁻¹`, since `G^{(x)} = (H^{(x)} - z)⁻¹` with `H^{(x)}`
Hermitian. -/
private lemma norm_minorGreen_le {z : ℂ} (hz : 0 < z.im) (ω : Sample ι) (x : ι)
    (k l : {a : ι // a ≠ x}) : ‖minorGreen (green (hmat ω) z) x k l‖ ≤ |z.im|⁻¹ := by
  rw [← inv_minor_resolvent (hmat_isHermitian ω) hz x]
  exact norm_green_entry_le ((hmat_isHermitian ω).submatrix _) hz.ne' k l

end Resolvent

/-- The resolvent minor entries `G^{(x)}_{ab}` of [II, (4.17)], written on the full index set,
have polynomial growth: they are bounded by `(Im z)⁻¹` (and vanish when `a = x` or `b = x`). -/
theorem polyMeas_greenMinor :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (z : ℂ), 0 < z.im → ∀ x a b : ι,
    PolyMeas fun ω : Sample ι => greenMinor (green (hmat ω) z) x a b := by
  intro ι _ _ z hz x a b
  refine ⟨?_, |z.im|⁻¹, 0, fun ω => ?_⟩
  · simp only [greenMinor]
    have := measurable_green_entry (ι := ι) hz
    fun_prop
  · change ‖greenMinor (green (hmat ω) z) x a b‖ ≤ |z.im|⁻¹ * (1 + ‖ω‖) ^ 0
    rw [pow_zero, mul_one]
    have hxx := green_diag_ne_zero (hmat_isHermitian ω) hz x
    by_cases ha : a = x
    · subst ha
      simp only [greenMinor, mul_div_cancel_left₀ _ hxx, sub_self, norm_zero]
      positivity
    by_cases hb : b = x
    · subst hb
      simp only [greenMinor, mul_div_cancel_right₀ _ hxx, sub_self, norm_zero]
      positivity
    rw [← minorGreen_eq_greenMinor _ x ⟨a, ha⟩ ⟨b, hb⟩]
    exact norm_minorGreen_le hz ω x _ _

/-- `(G_aa)⁻¹` has polynomial growth of degree `2`, by the Schur complement formula
`(G_aa)⁻¹ = h_aa - z - ∑_{k,l ≠ a} h_ak G^{(a)}_kl h_la` ([II, §4.4]), `|h_ab| ≤ 2 ‖ω‖` and
`|G^{(a)}_kl| ≤ (Im z)⁻¹`. -/
theorem polyMeas_inv_green_diag :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (z : ℂ), 0 < z.im → ∀ a : ι,
    PolyMeas fun ω : Sample ι => (green (hmat ω) z a a)⁻¹ := by
  intro ι _ _ z hz a
  set N : ℕ := Fintype.card {b : ι // b ≠ a}
  set c : ℝ := |z.im|⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨(measurable_green_entry hz a a).inv, 2 + ‖z‖ + (N : ℝ) ^ 2 * (4 * c), 2,
    fun ω => ?_⟩
  change ‖(green (hmat ω) z a a)⁻¹‖ ≤ _
  have hH := hmat_isHermitian ω
  rw [green_diag_schur hH hz a, inv_inv]
  have hr : 0 ≤ ‖ω‖ := norm_nonneg _
  have hp : (1 : ℝ) ≤ (1 + ‖ω‖) ^ 2 := one_le_pow₀ (one_le_one_add_norm ω)
  have hterm : ∀ k l : {b : ι // b ≠ a},
      ‖hmat ω a k.1 * minorGreen (green (hmat ω) z) a k l * hmat ω l.1 a‖
        ≤ 4 * c * (1 + ‖ω‖) ^ 2 := by
    intro k l
    rw [norm_mul, norm_mul]
    have e1 := norm_hmat_le ω a k.1
    have e2 := norm_hmat_le ω l.1 a
    have e3 := norm_minorGreen_le hz ω a k l
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
    nlinarith [norm_hmat_le ω a a]
  calc ‖hmat ω a a - z - ∑ k : {b : ι // b ≠ a}, ∑ l : {b : ι // b ≠ a},
        hmat ω a k.1 * minorGreen (green (hmat ω) z) a k l * hmat ω l.1 a‖
      ≤ ‖hmat ω a a‖ + ‖z‖ + ‖∑ k : {b : ι // b ≠ a}, ∑ l : {b : ι // b ≠ a},
        hmat ω a k.1 * minorGreen (green (hmat ω) z) a k l * hmat ω l.1 a‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * (1 + ‖ω‖) ^ 2 + ‖z‖ * (1 + ‖ω‖) ^ 2 + (N : ℝ) ^ 2 * (4 * c * (1 + ‖ω‖) ^ 2) :=
        add_le_add (add_le_add hd (le_mul_of_one_le_right (norm_nonneg _) hp)) hsum
    _ = (2 + ‖z‖ + (N : ℝ) ^ 2 * (4 * c)) * (1 + ‖ω‖) ^ 2 := by ring

section Instance

end Instance

end RBM8D
