module

public import RBM8D.Prob.Model
public import RBM8D.Prob.StochDom
public import RBM8D.Prob.Partial
public import RBM8D.Basic.Minor
public import RBM8D.Basic.Domain
public import RBM8D.Basic.Semicircle
public import RBM8D.Profile.Basic
public import RBM8D.Input.Chaos

@[expose] public section

/-!
# Large deviation tail for quadratic forms

The tail bound, for a fixed finite index set, for the centred quadratic form
`Σ_{k,l≠x} h_{xk} B_{kl} h_{lx} − Σ_{k≠x} s_{xk} B_{kk}` with coefficients independent of row `x`
(the Hanson–Wright type bound used in the proof of [I, Lemma 5.1]).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

section Const

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The real coordinate of `Re h_{xk}` (`b = true`) or `Im h_{xk}` (`b = false`), `k ≠ x`. -/
private def ldeQuad_co (x : ι) (k : {a : ι // a ≠ x}) (b : Bool) : Coord ι :=
  if h : idxKey ι x < idxKey ι k.1 then .inr (⟨(x, k.1), h⟩, b)
  else .inr (⟨(k.1, x), lt_of_le_of_ne (not_lt.1 h) fun e => k.2 (idxKey_injective e)⟩, b)

/-- The sign of the imaginary part of `h_{xk}` in the coordinates `ldeQuad_co`. -/
private def ldeQuad_eps (x : ι) (k : {a : ι // a ≠ x}) : ℝ :=
  if idxKey ι x < idxKey ι k.1 then 1 else -1

omit [DecidableEq ι] in
private theorem ldeQuad_co_inj (x : ι) :
    Function.Injective fun p : {a : ι // a ≠ x} × Bool => ldeQuad_co x p.1 p.2 := by
  rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨k', hk'⟩, b'⟩ h
  simp only [ldeQuad_co] at h
  split_ifs at h with h1 h2 h2 <;>
    simp only [Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
  · obtain ⟨⟨-, rfl⟩, rfl⟩ := h; rfl
  · obtain ⟨⟨rfl, -⟩, -⟩ := h; exact absurd rfl hk'
  · obtain ⟨⟨rfl, -⟩, -⟩ := h; exact absurd rfl hk
  · obtain ⟨⟨rfl, -⟩, rfl⟩ := h; rfl

private theorem ldeQuad_co_mem (x : ι) (k : {a : ι // a ≠ x}) (b : Bool) :
    ldeQuad_co x k b ∈ rowCoords x := by
  simp only [rowCoords, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨k.1, ?_⟩
  simp only [ldeQuad_co, entryCoords]
  split_ifs <;> simp

/-- The row chaos of row `x` of `H(ω)` with the constant coefficient matrix `b`. -/
private def ldeQuad_chaos (S : Matrix ι ι ℝ) (x : ι)
    (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) : chaos_RowChaos S {a : ι // a ≠ x} where
  co := ldeQuad_co x
  co_inj := ldeQuad_co_inj x
  gvar_tag k := by unfold ldeQuad_co; split_ifs <;> rfl
  eps := ldeQuad_eps x
  eps_sq k := by unfold ldeQuad_eps; split_ifs <;> norm_num
  r := 1
  B _ := b
  B_cont _ _ := continuous_const
  Bbd := ∑ k, ∑ l, ‖b k l‖
  B_bdd _ k l := (Finset.single_le_sum (f := fun l => ‖b k l‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ l)).trans (Finset.single_le_sum (f := fun k => ∑ l, ‖b k l‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  Ifree := ∅
  Ifree_free _ _ := Finset.notMem_empty _
  B_free _ _ _ := rfl

private theorem ldeQuad_chaos_h (S : Matrix ι ι ℝ) (x : ι)
    (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) (ω : Sample ι) (k : {a : ι // a ≠ x}) :
    (ldeQuad_chaos S x b).h ω k = hmat ω x k.1 := by
  simp only [chaos_RowChaos.h, ldeQuad_chaos, ldeQuad_co, ldeQuad_eps, hmat, Matrix.of_apply]
  split_ifs with h1 h2
  · simp
  · simp [sub_eq_add_neg]
  · exact absurd (lt_of_le_of_ne (not_lt.1 h1) fun e => k.2 (idxKey_injective e)) h2

private theorem ldeQuad_chaos_sg (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ a b, 0 ≤ S a b)
    (x : ι) (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) (k : {a : ι // a ≠ x}) :
    (ldeQuad_chaos S x b).sg k = S x k.1 := by
  simp only [chaos_RowChaos.sg, chaos_RowChaos.w, ldeQuad_chaos, ldeQuad_co]
  split_ifs
  · simp only [coordVar]
    rw [Real.coe_toNNReal _ (by have := hnn x k.1; positivity)]
    ring
  · simp only [coordVar]
    rw [Real.coe_toNNReal _ (by have := hnn k.1 x; positivity), hS.apply x k.1]
    ring

/-- The centred quadratic form of row `x` with the coefficient matrix `b`, written with
`h_{lx} = conj h_{xl}`. -/
private def ldeQuad_Q (S : Matrix ι ι ℝ) (x : ι) (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ)
    (ω : Sample ι) : ℂ :=
  ∑ k, ∑ l, hmat ω x k.1 * b k l * (starRingEnd ℂ) (hmat ω x l.1) - ∑ k, (S x k.1 : ℂ) * b k k

/-- The variance bound `Σ_{k,l} s_{xk} |b_{kl}|² s_{lx}`. -/
private def ldeQuad_V (S : Matrix ι ι ℝ) (x : ι) (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) :
    ℝ :=
  ∑ k, ∑ l, S x k.1 * ‖b k l‖ ^ 2 * S l.1 x

private theorem ldeQuad_chaos_chaos (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ a b, 0 ≤ S a b)
    (x : ι) (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) (ω : Sample ι) :
    (ldeQuad_chaos S x b).chaos ω = ldeQuad_Q S x b ω := by
  simp only [chaos_RowChaos.chaos, chaos_RowChaos.cen, ldeQuad_chaos_h, ldeQuad_chaos_sg S hS hnn,
    ldeQuad_Q]
  rfl

private theorem ldeQuad_chaos_Vq (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ a b, 0 ≤ S a b)
    (x : ι) (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) (ω : Sample ι) :
    (ldeQuad_chaos S x b).Vq ω = ldeQuad_V S x b := by
  simp only [chaos_RowChaos.Vq, ldeQuad_chaos_sg S hS hnn, ldeQuad_V]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hS.apply x l.1]
  rfl

/-- The constant `((2q+1)(4q+2))^{q+1}` of the moment bound at order `q + 1`. -/
private def ldeQuad_hw (q : ℕ) : ℝ := ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1)

private theorem ldeQuad_mom_le (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ a b, 0 ≤ S a b)
    (x : ι) (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) (q : ℕ) :
    ∫ ω, ‖ldeQuad_Q S x b ω‖ ^ (2 * (q + 1)) ∂(gaussLaw S) ≤
      ldeQuad_hw q * ldeQuad_V S x b ^ (q + 1) := by
  have := isProbabilityMeasure_gaussLaw S
  have h := (ldeQuad_chaos S x b).mom_le_momVpow (gaussPoly_gaussIBP S) q
  simp only [chaos_RowChaos.mom, chaos_RowChaos.momVpow, ldeQuad_chaos_chaos S hS hnn,
    ldeQuad_chaos_Vq S hS hnn, integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact h

private theorem ldeQuad_integrable (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ a b, 0 ≤ S a b)
    (x : ι) (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) (q : ℕ) :
    Integrable (fun ω => ‖ldeQuad_Q S x b ω‖ ^ (2 * q)) (gaussLaw S) := by
  have h := (ldeQuad_chaos S x b).integrable_norm_pow (gaussPoly_gaussIBP S) q
  simpa only [ldeQuad_chaos_chaos S hS hnn] using h

private theorem ldeQuad_V_nonneg (S : Matrix ι ι ℝ) (hnn : ∀ a b, 0 ≤ S a b) (x : ι)
    (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) : 0 ≤ ldeQuad_V S x b :=
  Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (hnn _ _) (by positivity)) (hnn _ _)

/-- The tail bound for a constant coefficient matrix, at the moment order `q + 1`. -/
private theorem ldeQuad_const_tail (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hnn : ∀ a b, 0 ≤ S a b)
    (x : ι) (b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ) (q : ℕ) {t : ℝ} (ht : 0 < t) :
    gaussLaw S {η | t * ldeQuad_V S x b < ‖ldeQuad_Q S x b η‖ ^ 2} ≤
      ENNReal.ofReal (ldeQuad_hw q / t ^ (q + 1)) := by
  have := isProbabilityMeasure_gaussLaw S
  set V := ldeQuad_V S x b with hV
  set Q := ldeQuad_Q S x b with hQ
  have hV0 : 0 ≤ V := ldeQuad_V_nonneg S hnn x b
  rcases hV0.lt_or_eq with hVpos | hVzero
  · -- Markov at order `q + 1`
    set ε : ℝ := (t * V) ^ (q + 1) with hε
    have hεpos : 0 < ε := pow_pos (mul_pos ht hVpos) _
    have hsub : {η | t * V < ‖Q η‖ ^ 2} ⊆ {η | ε ≤ ‖Q η‖ ^ (2 * (q + 1))} := by
      intro η hη
      simp only [Set.mem_ofPred_eq] at hη ⊢
      rw [pow_mul, hε]
      exact pow_le_pow_left₀ (mul_pos ht hVpos).le hη.le _
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := gaussLaw S)
      (Eventually.of_forall fun η => by positivity) (ldeQuad_integrable S hS hnn x b (q + 1)) ε
    have hmom := ldeQuad_mom_le S hS hnn x b q
    set m := (gaussLaw S).real {η | ε ≤ ‖Q η‖ ^ (2 * (q + 1))} with hm
    have hreal : m ≤ ldeQuad_hw q / t ^ (q + 1) := by
      rw [le_div_iff₀ (pow_pos ht _)]
      have h1 : t ^ (q + 1) * m * V ^ (q + 1) ≤ ldeQuad_hw q * V ^ (q + 1) := by
        have h2 : ε * m ≤ ldeQuad_hw q * V ^ (q + 1) := hmk.trans hmom
        calc t ^ (q + 1) * m * V ^ (q + 1) = ε * m := by rw [hε, mul_pow]; ring
          _ ≤ _ := h2
      have := le_of_mul_le_mul_right h1 (pow_pos hVpos _)
      linarith
    calc gaussLaw S {η | t * V < ‖Q η‖ ^ 2}
        ≤ gaussLaw S {η | ε ≤ ‖Q η‖ ^ (2 * (q + 1))} := measure_mono hsub
      _ = ENNReal.ofReal ((gaussLaw S).real {η | ε ≤ ‖Q η‖ ^ (2 * (q + 1))}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (ldeQuad_hw q / t ^ (q + 1)) := ENNReal.ofReal_le_ofReal hreal
  · -- `V = 0`: the second moment vanishes, so `Q = 0` almost surely
    have hmom : ∫ η, ‖Q η‖ ^ (2 * 1) ∂(gaussLaw S) ≤ 0 := by
      have h := ldeQuad_mom_le S hS hnn x b 0
      rw [← hV, ← hVzero, zero_pow (by norm_num), mul_zero] at h
      exact h
    have hint : Integrable (fun η => ‖Q η‖ ^ (2 * 1)) (gaussLaw S) :=
      ldeQuad_integrable S hS hnn x b 1
    have hz : ∫ η, ‖Q η‖ ^ (2 * 1) ∂(gaussLaw S) = 0 :=
      le_antisymm hmom (integral_nonneg fun η => by positivity)
    rw [integral_eq_zero_iff_of_nonneg (fun η => by positivity) hint] at hz
    have hnull : gaussLaw S {η | t * V < ‖Q η‖ ^ 2} = 0 := by
      refine measure_mono_null (fun η hη => ?_) (ae_iff.1 hz)
      simp only [Set.mem_ofPred_eq, ← hVzero, mul_zero] at hη
      simp only [Set.mem_ofPred_eq, Pi.zero_apply]
      intro h0
      rw [mul_one] at h0
      exact (ne_of_gt hη) h0
    rw [hnull]
    exact zero_le

end Const

section Cond

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `(ω, η) ↦ A.piecewise η ω`, which takes `η` on `A` and `ω` off `A`, is measurable. -/
private lemma ldeQuad_measurable_piecewise (A : Finset (Coord ι)) :
    Measurable fun p : Sample ι × Sample ι => A.piecewise p.2 p.1 := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ A
  · simp only [Finset.piecewise_eq_of_mem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_snd
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_fst

/-- Overwriting a sample on `A` by an independent copy has again the law of the sample. -/
private lemma ldeQuad_measurePreserving_piecewise (S : Matrix ι ι ℝ) (A : Finset (Coord ι)) :
    MeasurePreserving (fun p : Sample ι × Sample ι => A.piecewise p.2 p.1)
      ((gaussLaw S).prod (gaussLaw S)) (gaussLaw S) := by
  refine ⟨ldeQuad_measurable_piecewise A, ?_⟩
  unfold gaussLaw
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (ldeQuad_measurable_piecewise A) (MeasurableSet.univ_pi hs)]
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

/-- The entries `h_{xk}` of row `x` read only the coordinates of row `x`. -/
private lemma ldeQuad_hmat_piecewise (S : Matrix ι ι ℝ) (x : ι) (ω η : Sample ι)
    (k : {a : ι // a ≠ x}) :
    hmat ((rowCoords x).piecewise η ω) x k.1 = hmat η x k.1 := by
  let b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ := fun _ _ => 0
  rw [← ldeQuad_chaos_h S x b, ← ldeQuad_chaos_h S x b]
  simp only [chaos_RowChaos.h, ldeQuad_chaos,
    Finset.piecewise_eq_of_mem _ _ _ (ldeQuad_co_mem x k true),
    Finset.piecewise_eq_of_mem _ _ _ (ldeQuad_co_mem x k false)]

omit [DecidableEq ι] in
private lemma ldeQuad_measurable_hmat (x : ι) (k : {a : ι // a ≠ x}) :
    Measurable fun ω : Sample ι => hmat ω x k.1 := by
  classical
  let b : {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ := fun _ _ => 0
  have h := ((ldeQuad_chaos (0 : Matrix ι ι ℝ) x b).tameh k).cont.measurable
  simpa only [ldeQuad_chaos_h] using h

end Cond

/-- The quadratic form: for a matrix `B_{kl}`, `k, l ≠ x`, measurable, bounded and independent of
row `x`, and `t > 0`: `P(t Σ_{k,l} s_{xk} |B_{kl}|² s_{lx} < |Σ_{k,l} h_{xk} B_{kl} h_{lx} −
Σ_k s_{xk} B_{kk}|²) ≤ C_p t^{−p}`. -/
theorem ldeQuadTail :
  ∀ p : ℕ, ∃ C : ℝ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ), S.IsSymm →
    (∀ a b, 0 ≤ S a b) → ∀ (x : ι) (B : Sample ι → {a : ι // a ≠ x} → {a : ι // a ≠ x} → ℂ),
    (∀ k l, Measurable fun ω => B ω k l) → (∀ k l, FreeOf (rowCoords x) fun ω => B ω k l) →
    (∃ M : ℝ, ∀ ω k l, ‖B ω k l‖ ≤ M) → ∀ t : ℝ, 0 < t →
    gaussLaw S {ω | t * ∑ k, ∑ l, S x k.1 * ‖B ω k l‖ ^ 2 * S l.1 x <
        ‖∑ k, ∑ l, hmat ω x k.1 * B ω k l * hmat ω l.1 x - ∑ k, (S x k.1 : ℂ) * B ω k k‖ ^ 2} ≤
      ENNReal.ofReal (C / t ^ p) := by
  intro p
  cases p with
  | zero =>
    refine ⟨1, fun {ι} _ _ S _ _ x B _ _ _ t _ => ?_⟩
    have := isProbabilityMeasure_gaussLaw S
    rw [pow_zero, div_one, ENNReal.ofReal_one]
    exact prob_le_one
  | succ q =>
    refine ⟨ldeQuad_hw q, fun {ι} _ _ S hS hnn x B hBm hBf _ t ht => ?_⟩
    have := isProbabilityMeasure_gaussLaw S
    set φ : Sample ι × Sample ι → Sample ι := fun p => (rowCoords x).piecewise p.2 p.1 with hφ
    set E := {ω : Sample ι | t * ∑ k, ∑ l, S x k.1 * ‖B ω k l‖ ^ 2 * S l.1 x <
        ‖∑ k, ∑ l, hmat ω x k.1 * B ω k l * hmat ω l.1 x - ∑ k, (S x k.1 : ℂ) * B ω k k‖ ^ 2}
      with hE
    -- the pinned form of the event, in the notation of the constant-coefficient bound
    have hEeq : E = {ω | t * ldeQuad_V S x (B ω) < ‖ldeQuad_Q S x (B ω) ω‖ ^ 2} := by
      ext ω
      simp only [hE, Set.mem_ofPred_eq, ldeQuad_V, ldeQuad_Q]
      have e : ∀ k l : {a : ι // a ≠ x}, hmat ω x k.1 * B ω k l * hmat ω l.1 x
          = hmat ω x k.1 * B ω k l * (starRingEnd ℂ) (hmat ω x l.1) := by
        intro k l
        rw [← (hmat_isHermitian ω).apply l.1 x]
        rfl
      simp only [e]
    have hmE : MeasurableSet E := by
      have hh : ∀ k : {a : ι // a ≠ x}, Measurable fun ω : Sample ι => hmat ω x k.1 :=
        ldeQuad_measurable_hmat x
      have hh' : ∀ l : {a : ι // a ≠ x}, Measurable fun ω : Sample ι => hmat ω l.1 x := by
        intro l
        have e : (fun ω : Sample ι => hmat ω l.1 x)
            = fun ω => (starRingEnd ℂ) (hmat ω x l.1) := by
          funext ω
          rw [← (hmat_isHermitian ω).apply l.1 x]
          rfl
        rw [e]
        exact Complex.continuous_conj.measurable.comp (hh l)
      refine measurableSet_lt ?_ ?_
      · refine Measurable.const_mul ?_ t
        refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
        exact (measurable_const.mul (((hBm k l).norm).pow_const 2)).mul measurable_const
      · refine (Measurable.sub ?_ ?_).norm.pow_const 2
        · refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
          exact ((hh k).mul (hBm k l)).mul (hh' l)
        · exact Finset.measurable_sum _ fun k _ => measurable_const.mul (hBm k k)
    have hmp := ldeQuad_measurePreserving_piecewise S (rowCoords x)
    -- the slice of the pulled-back event at `ω` is the event with the constant matrix `B ω`
    have hslice : ∀ ω : Sample ι, Prod.mk ω ⁻¹' (φ ⁻¹' E)
        = {η | t * ldeQuad_V S x (B ω) < ‖ldeQuad_Q S x (B ω) η‖ ^ 2} := by
      intro ω
      ext η
      have hB : B ((rowCoords x).piecewise η ω) = B ω := by
        funext k l
        exact hBf k l ω η
      simp only [Set.mem_preimage, hφ, hEeq, Set.mem_ofPred_eq, hB, ldeQuad_Q,
        ldeQuad_hmat_piecewise S x ω η]
    calc gaussLaw S E = ((gaussLaw S).prod (gaussLaw S)) (φ ⁻¹' E) :=
          (hmp.measure_preimage hmE.nullMeasurableSet).symm
      _ = ∫⁻ ω, gaussLaw S (Prod.mk ω ⁻¹' (φ ⁻¹' E)) ∂(gaussLaw S) :=
          Measure.prod_apply (hmp.measurable hmE)
      _ ≤ ∫⁻ _ω, ENNReal.ofReal (ldeQuad_hw q / t ^ (q + 1)) ∂(gaussLaw S) := by
          refine lintegral_mono fun ω => ?_
          rw [hslice ω]
          exact ldeQuad_const_tail S hS hnn x (B ω) q ht
      _ = ENNReal.ofReal (ldeQuad_hw q / t ^ (q + 1)) := by
          rw [lintegral_const, measure_univ, mul_one]

section Instance

end Instance

end RBM8D
