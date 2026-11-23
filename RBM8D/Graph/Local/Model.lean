module

public import RBM8D.Prob.IBP
public import RBM8D.Graph.Local.Basic
public import Mathlib.LinearAlgebra.Matrix.Gershgorin

@[expose] public section

/-!
# The model relations in the Gaussian model

The bridge from `PQLaws` to `PFamily.Laws`, conjugation and freeness of the partial expectations, the Wirtinger derivative on test functions, and the data fields `S^+`, `Θ` of `modelData` ([I, (1.16), (2.1)]).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal BigOperators

universe u v w

namespace RBM8D.Graphs

/-! ## Private helpers -/

section Helpers

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

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

/-- The coordinates of `h_kl` with `k, l ≠ x` are not coordinates of row `x`. -/
private lemma notMem_rowCoords_of_mem_entryCoords {x k l : ι} (hk : k ≠ x) (hl : l ≠ x)
    {c : Coord ι} (hc : c ∈ entryCoords k l) : c ∉ rowCoords x := by
  intro hx
  simp only [rowCoords, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
  obtain ⟨y, hy⟩ := hx
  rcases c with w | ⟨e, β⟩
  · simp only [entryCoords, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      at hc hy
    exact hk (hc.1.symm.trans hy.1)
  · simp only [entryCoords, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      at hc hy
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hk (h1.symm.trans h3)
    · exact hl (h2.symm.trans h4)
    · exact hl (h1.symm.trans h3)
    · exact hk (h2.symm.trans h4)


private lemma hasDerivAt_updateCoord (ω : Sample ι) (c : Coord ι) :
    HasDerivAt (fun t : ℝ => Function.update ω c t) (Pi.single c 1) (ω c) := by
  rw [hasDerivAt_pi]
  intro j
  by_cases h : j = c
  · subst h
    simpa using hasDerivAt_id' (ω j)
  · simpa [Function.update_of_ne h, Pi.single_eq_of_ne h] using hasDerivAt_const (ω c) (ω j)

/-- A test function is differentiable along every coordinate line. -/
private lemma differentiableAt_update {F : Sample ι → ℂ} (hF : TestFn F) (ω : Sample ι)
    (c : Coord ι) : DifferentiableAt ℝ (fun t : ℝ => F (Function.update ω c t)) (ω c) := by
  have hd : Differentiable ℝ F := (hF 1).1.differentiable (by norm_num)
  have h1 : HasFDerivAt F (fderiv ℝ F ω) (Function.update ω c (ω c)) := by
    rw [Function.update_eq_self]; exact (hd ω).hasFDerivAt
  exact (h1.comp_hasDerivAt (ω c) (hasDerivAt_updateCoord ω c)).differentiableAt

private lemma partialCoord_add {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G)
    (c : Coord ι) (ω : Sample ι) :
    partialCoord c (F + G) ω = partialCoord c F ω + partialCoord c G ω := by
  unfold partialCoord
  exact deriv_add (differentiableAt_update hF ω c) (differentiableAt_update hG ω c)

private lemma partialCoord_mul {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G)
    (c : Coord ι) (ω : Sample ι) :
    partialCoord c (F * G) ω = partialCoord c F ω * G ω + F ω * partialCoord c G ω := by
  unfold partialCoord
  have := deriv_mul (differentiableAt_update hF ω c) (differentiableAt_update hG ω c)
  simp only [Function.update_eq_self] at this
  exact this

end Helpers

/-! ## The laws of the partial expectations -/

/-- The laws `PQLaws` of an expectation and of partial expectations give the laws
`PFamily.Laws` of [I, §1.4] used by the graph values, when constants are free of every row. -/
theorem pqLaws_toLaws :
  ∀ {Ω : Type u} {ι : Type v} {Adm : (Ω → ℂ) → Prop} {E : (Ω → ℂ) → ℂ}
    {P : ι → (Ω → ℂ) → Ω → ℂ} {Free : ι → (Ω → ℂ) → Prop},
    PQLaws Adm E P Free → (∀ x (a : ℂ), Free x fun _ => a) →
      PFamily.Laws (⟨P⟩ : PFamily Ω ι) E Free Adm := by
  intro Ω ι Adm E P Free h hc
  exact
    { good_add := h.adm_add
      good_mul := h.adm_mul
      good_const := h.adm_const
      good_P := h.adm_P
      add := fun x f g hf hg => h.P_add x f g hf hg
      smul := fun x a f _ => h.P_const_mul x a f
      of_meas := fun x f _ hfx => h.P_of_free x f hfx
      mul_left := fun x f g _ _ hfx => h.P_mul_free x g f hfx
      meas_P := fun x f _ => h.free_P x f
      meas_const := hc
      E_P := fun x f hf => h.E_P x f hf
      E_add := fun f g hf hg => h.E_add f g hf hg }

/-- Functions free of a set of coordinates: constants, sums and products. -/
theorem freeOf_closed :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (A : Finset (Coord ι)),
    (∀ a : ℂ, FreeOf A fun _ : Sample ι => a) ∧
    (∀ F G : Sample ι → ℂ, FreeOf A F → FreeOf A G → FreeOf A (F + G)) ∧
    (∀ F G : Sample ι → ℂ, FreeOf A F → FreeOf A G → FreeOf A (F * G)) := by
  intro ι _ _ A
  refine ⟨fun a _ _ => rfl, fun F G hF hG ω η => ?_, fun F G hF hG ω η => ?_⟩
  · simp only [Pi.add_apply, hF ω η, hG ω η]
  · simp only [Pi.mul_apply, hF ω η, hG ω η]

/-- A partial expectation commutes with complex conjugation. -/
theorem partialExp_star :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (A : Finset (Coord ι))
    (F : Sample ι → ℂ),
    partialExp S A (fun ω => star (F ω)) = fun ω => star (partialExp S A F ω) := by
  intro ι _ _ S A F
  funext ω
  exact integral_conj (𝕜 := ℂ) (f := fun η => F (A.piecewise η ω))

/-- The resolvent minor entries `G^{(x)}_{ab}` ([II, (4.17)]) do not depend on row and column
`x` of `H` (for `a = x` or `b = x` they vanish). -/
theorem freeOf_greenMinor :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (z : ℂ), 0 < z.im → ∀ x a b : ι,
    FreeOf (rowCoords x) fun ω : Sample ι => greenMinor (green (hmat ω) z) x a b := by
  intro ι _ _ z hz x a b ω η
  have hzero : ∀ ω' : Sample ι, (a = x ∨ b = x) → greenMinor (green (hmat ω') z) x a b = 0 := by
    intro ω' hab
    have hne := green_diag_ne_zero (hmat_isHermitian ω') hz x
    rcases hab with rfl | rfl
    · unfold greenMinor
      field_simp
      ring
    · unfold greenMinor
      field_simp
      ring
  change greenMinor (green (hmat ((rowCoords x).piecewise η ω)) z) x a b =
    greenMinor (green (hmat ω) z) x a b
  by_cases hab : a = x ∨ b = x
  · rw [hzero _ hab, hzero _ hab]
  · obtain ⟨ha, hb⟩ := not_or.mp hab
    have key : ∀ ω' : Sample ι, greenMinor (green (hmat ω') z) x a b =
        (((hmat ω').submatrix Subtype.val Subtype.val -
          z • (1 : Matrix {k : ι // k ≠ x} {k : ι // k ≠ x} ℂ) :
            Matrix {k : ι // k ≠ x} {k : ι // k ≠ x} ℂ)⁻¹) ⟨a, ha⟩ ⟨b, hb⟩ := fun ω' => by
      rw [inv_minor_resolvent (hmat_isHermitian ω') hz x]
      rfl
    have hsub : (hmat ((rowCoords x).piecewise η ω)).submatrix
          (Subtype.val : {k : ι // k ≠ x} → ι) (Subtype.val : {k : ι // k ≠ x} → ι) =
        (hmat ω).submatrix (Subtype.val : {k : ι // k ≠ x} → ι)
          (Subtype.val : {k : ι // k ≠ x} → ι) := by
      ext k l
      exact hmat_congr k.1 l.1 fun c hc =>
        Finset.piecewise_eq_of_notMem _ _ _ (notMem_rowCoords_of_mem_entryCoords k.2 l.2 hc)
    rw [key, key, hsub]

/-! ## The Wirtinger derivative on test functions -/

/-- `∂_{h_ab}` vanishes on constants. -/
theorem dh_const :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (a b : ι) (c : ℂ),
    dh a b (fun _ : Sample ι => c) = 0 := by
  intro ι _ _ a b c
  funext ω
  simp [dh, partialCoord]

/-- `∂_{h_ab}` is additive on test functions. -/
theorem dh_add :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (a b : ι) (F G : Sample ι → ℂ), TestFn F →
    TestFn G → dh a b (F + G) = dh a b F + dh a b G := by
  intro ι _ _ a b F G hF hG
  funext ω
  simp only [dh, Pi.add_apply]
  split_ifs
  · rw [partialCoord_add hF hG, partialCoord_add hF hG]
    ring
  · rw [partialCoord_add hF hG, partialCoord_add hF hG]
    ring
  · exact partialCoord_add hF hG _ ω

/-- `∂_{h_ab}` satisfies the product rule on test functions. -/
theorem dh_mul :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (a b : ι) (F G : Sample ι → ℂ), TestFn F →
    TestFn G → dh a b (F * G) = dh a b F * G + F * dh a b G := by
  intro ι _ _ a b F G hF hG
  funext ω
  simp only [dh, Pi.add_apply, Pi.mul_apply]
  split_ifs
  · rw [partialCoord_mul hF hG, partialCoord_mul hF hG]
    ring
  · rw [partialCoord_mul hF hG, partialCoord_mul hF hG]
    ring
  · exact partialCoord_mul hF hG _ ω

/-- The coordinates of `h_ab` are coordinates of row and column `x` when `a = x` or `b = x`. -/
theorem entryCoords_subset_rowCoords :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (x a b : ι), (a = x ∨ b = x) →
    entryCoords a b ⊆ rowCoords x := by
  intro ι _ _ x a b hab
  rcases hab with rfl | rfl
  · exact Finset.subset_biUnion_of_mem (entryCoords a) (Finset.mem_univ b)
  · rw [entryCoords_comm]
    exact Finset.subset_biUnion_of_mem (entryCoords b) (Finset.mem_univ a)

/-! ## The data fields `S^+` and `Θ` of `modelData` -/

/-- `1 - c S` is invertible for `S ≥ 0` with row sums `1` and `‖c‖ < 1`: it is strictly
diagonally dominant, with slack `1 - ‖c‖` in every row. -/
private lemma det_one_sub_smul_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (c : ℂ) (hc : ‖c‖ < 1) (hnn : ∀ x y, 0 ≤ S x y) (hrow : ∀ x, ∑ y, S x y = 1) :
    (1 - c • S.map fun r => (r : ℂ)).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  have hoff : ∀ j ∈ Finset.univ.erase k,
      ‖(1 - c • S.map fun r => (r : ℂ)) k j‖ = ‖c‖ * S k j := by
    intro j hj
    have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
    simp [Matrix.one_apply_ne hjk, abs_of_nonneg (hnn k j)]
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum]
  have hsum : ∑ j ∈ Finset.univ.erase k, S k j = 1 - S k k := by
    rw [← hrow k, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    ring
  have hdiag : 1 - ‖c‖ * S k k ≤ ‖(1 - c • S.map fun r => (r : ℂ)) k k‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (c * (S k k : ℂ))
    have e : (1 - c • S.map fun r => (r : ℂ)) k k = 1 - c * (S k k : ℂ) := by
      simp
    rw [e]
    simpa [abs_of_nonneg (hnn k k)] using h
  rw [hsum]
  have := hnn k k
  nlinarith

/-- `(1 - m² S)(1 + S⁺) = 1` ([I, (2.1)]) for the data record of the model, with `S ≥ 0` of row
sums `1` and `Im z > 0`: `1 - m² S` is invertible since `|m| < 1`. -/
theorem modelData_Sp :
  ∀ {Ω ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ)
    (H : Ω → Matrix ι ι ℂ) (ω : Ω), (∀ x y, 0 ≤ S x y) → (∀ x, ∑ y, S x y = 1) → 0 < z.im →
      (1 - msc z ^ 2 • (modelData S z H ω).S) * (1 + (modelData S z H ω).Sp) = 1 := by
  intro Ω ι _ _ S z H ω hnn hrow hz
  have hm := norm_msc_lt_one hz
  have hdet := det_one_sub_smul_ne_zero S (msc z ^ 2)
    (by rw [norm_pow]; nlinarith [norm_nonneg (msc z)]) hnn hrow
  have hu : IsUnit (1 - msc z ^ 2 • S.map fun r => (r : ℂ)).det := isUnit_iff_ne_zero.mpr hdet
  change (1 - msc z ^ 2 • S.map fun r => (r : ℂ)) *
      (1 + (msc z ^ 2 • S.map fun r => (r : ℂ)) *
        (1 - msc z ^ 2 • S.map fun r => (r : ℂ))⁻¹) = 1
  generalize (msc z ^ 2 • S.map fun r => (r : ℂ)) = A at hu ⊢
  have hcomm : (1 - A) * A = A * (1 - A) := by rw [mul_sub, sub_mul, one_mul, mul_one]
  rw [mul_add, mul_one, ← mul_assoc, hcomm, mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one,
    sub_add_cancel]

/-- `Θ (1 - |m|² S) = |m|² S` ([I, (1.16)]) for the data record of the model, with `S ≥ 0` of row
sums `1` and `Im z > 0`: `1 - |m|² S` is invertible since `|m| < 1`. -/
theorem modelData_Theta :
  ∀ {Ω ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ)
    (H : Ω → Matrix ι ι ℂ) (ω : Ω), (∀ x y, 0 ≤ S x y) → (∀ x, ∑ y, S x y = 1) → 0 < z.im →
      (modelData S z H ω).Theta * (1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • (modelData S z H ω).S) =
        ((‖msc z‖ ^ 2 : ℝ) : ℂ) • (modelData S z H ω).S := by
  intro Ω ι _ _ S z H ω hnn hrow hz
  have hm := norm_msc_lt_one hz
  have hdet := det_one_sub_smul_ne_zero S ((‖msc z‖ ^ 2 : ℝ) : ℂ)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [norm_nonneg (msc z)]) hnn hrow
  have hu : IsUnit (1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ)).det :=
    isUnit_iff_ne_zero.mpr hdet
  change (((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ)) *
      (1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ))⁻¹ *
      (1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ)) =
    ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ)
  generalize (((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ)) = B at hu ⊢
  rw [mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one]

section Instance

end Instance

end RBM8D.Graphs
