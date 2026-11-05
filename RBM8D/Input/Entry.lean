import RBM8D.Prob.Model
import RBM8D.Prob.StochDom
import RBM8D.Prob.Partial
import RBM8D.Basic.Minor
import RBM8D.Basic.Domain
import RBM8D.Basic.Semicircle
import RBM8D.Profile.Basic

/-!
# Entry bounds from the Schur complement formula

The variables `T_{xy}` of [I, (1.21)] and their column form, the event `‖G − m‖_max ≤ δ`, the
large deviation bounds as inequalities, stability of `1 − ξ S`, and the deterministic bounds behind
[I, (5.2)] and its column form.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

section Entry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G_{xy} − δ_{xy} m`. -/
def entryErr (G : Matrix ι ι ℂ) (m : ℂ) (x y : ι) : ℂ := G x y - if x = y then m else 0

/-- `T_{xy} = |m|² Σ_α s_{xα} |G_{αy}|²` ([I, (1.21)]). -/
def Tvar (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ) (m : ℂ) (x y : ι) : ℝ :=
  ‖m‖ ^ 2 * ∑ α, S x α * ‖G α y‖ ^ 2

/-- The column form `|m|² Σ_α s_{xα} |G_{yα}|²`, which is `T_{xy}` at `z̄`. -/
def TvarCol (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ) (m : ℂ) (x y : ι) : ℝ :=
  ‖m‖ ^ 2 * ∑ α, S x α * ‖G y α‖ ^ 2

/-- The event `‖G − m‖_max ≤ δ`, for one matrix. -/
def GoodEvent (G : Matrix ι ι ℂ) (m : ℂ) (δ : ℝ) : Prop :=
  ∀ x y, ‖entryErr G m x y‖ ≤ δ

/-- `|Σ_{k≠i} h_{ik} G^{(i)}_{kj}|²`, the row sum of the Schur complement formula
`G_{ij} = −G_{ii} Σ_{k≠i} h_{ik} G^{(i)}_{kj}`. -/
def ldeRowLHS (H G : Matrix ι ι ℂ) (i j : ι) : ℝ :=
  ‖∑ k : {a : ι // a ≠ i}, H i k * greenMinor G i k j‖ ^ 2

/-- `Σ_{k≠i} s_{ik} |G^{(i)}_{kj}|²`, the conditional variance of the row sum. -/
def ldeRowRHS (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ) (i j : ι) : ℝ :=
  ∑ k : {a : ι // a ≠ i}, S i k * ‖greenMinor G i k j‖ ^ 2

/-- `|Σ_{k≠i} G^{(i)}_{jk} h_{ki}|²`, the column sum of
`G_{ji} = −G_{ii} Σ_{k≠i} G^{(i)}_{jk} h_{ki}`. -/
def ldeColLHS (H G : Matrix ι ι ℂ) (i j : ι) : ℝ :=
  ‖∑ k : {a : ι // a ≠ i}, greenMinor G i j k * H k i‖ ^ 2

/-- `Σ_{k≠i} s_{ik} |G^{(i)}_{jk}|²`. -/
def ldeColRHS (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ) (i j : ι) : ℝ :=
  ∑ k : {a : ι // a ≠ i}, S i k * ‖greenMinor G i j k‖ ^ 2

/-- `|Σ_{k,l≠i} h_{ik} G^{(i)}_{kl} h_{li} − Σ_{k≠i} s_{ik} G^{(i)}_{kk}|²`, the centred quadratic
form of the Schur complement formula for `1/G_{ii}`. -/
def ldeQuadLHS (H G : Matrix ι ι ℂ) (S : Matrix ι ι ℝ) (i : ι) : ℝ :=
  ‖∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, H i k * greenMinor G i k l * H l i
    - ∑ k : {a : ι // a ≠ i}, (S i k : ℂ) * greenMinor G i k k‖ ^ 2

/-- `Σ_{k,l≠i} s_{ik} |G^{(i)}_{kl}|² s_{li}`. -/
def ldeQuadRHS (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ) (i : ι) : ℝ :=
  ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, S i k * ‖greenMinor G i k l‖ ^ 2 * S l i

/-- The row large deviation bound with factor `Φ`, for all `i, j`. -/
def LDERow (H G : Matrix ι ι ℂ) (S : Matrix ι ι ℝ) (Φ : ℝ) : Prop :=
  ∀ i j, ldeRowLHS H G i j ≤ Φ * ldeRowRHS S G i j

/-- The column large deviation bound with factor `Φ`, for all `i, j`. -/
def LDECol (H G : Matrix ι ι ℂ) (S : Matrix ι ι ℝ) (Φ : ℝ) : Prop :=
  ∀ i j, ldeColLHS H G i j ≤ Φ * ldeColRHS S G i j

/-- The quadratic large deviation bound with factor `Φ`, for all `i`. -/
def LDEQuad (H G : Matrix ι ι ℂ) (S : Matrix ι ι ℝ) (Φ : ℝ) : Prop :=
  ∀ i, ldeQuadLHS H G S i ≤ Φ * ldeQuadRHS S G i

/-- Stability of `1 − ξ S` in `ℓ^∞ → ℓ^∞` with constant `K`: `|v_i − ξ (S v)_i| ≤ B` for all `i`
implies `|v_i| ≤ K B` for all `i`. -/
def Stable (S : Matrix ι ι ℝ) (ξ : ℂ) (K : ℝ) : Prop :=
  ∀ (v : ι → ℂ) (B : ℝ), (∀ i, ‖v i - ξ * ∑ k, (S i k : ℂ) * v k‖ ≤ B) → ∀ i, ‖v i‖ ≤ K * B

end Entry

/-- Dropping the term `i` from a sum of nonnegative terms decreases it. -/
private theorem entry_sum_subtype_le {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℝ)
    (hF : ∀ k, 0 ≤ F k) (i : ι) : ∑ k : {a : ι // a ≠ i}, F k.1 ≤ ∑ k, F k := by
  rw [sum_subtype_ne i F]
  linarith [hF i]

/-- The absorption step: with `|a|² ≤ 4 |m|²`, `|b_k| ≤ δ`, row sums of `s` at most `1` and
`4 Φ δ² ≤ 1`, the bound `|c|² ≤ Φ Σ s_k |a g_k − b_k c|²` gives `|c|² ≤ 16 Φ |m|² Σ s_k |g_k|²`. -/
private theorem entry_absorb {κ : Type*} [Fintype κ] (a c : ℂ) (g b : κ → ℂ) (s : κ → ℝ)
    (mn δ Φ : ℝ) (hs : ∀ k, 0 ≤ s k) (hs1 : ∑ k, s k ≤ 1) (hb : ∀ k, ‖b k‖ ≤ δ)
    (ha : ‖a‖ ^ 2 ≤ 4 * mn ^ 2) (hΦ : 0 ≤ Φ) (hδ : 4 * Φ * δ ^ 2 ≤ 1)
    (h : ‖c‖ ^ 2 ≤ Φ * ∑ k, s k * ‖a * g k - b k * c‖ ^ 2) :
    ‖c‖ ^ 2 ≤ 16 * Φ * (mn ^ 2 * ∑ k, s k * ‖g k‖ ^ 2) := by
  have hterm : ∀ k, s k * ‖a * g k - b k * c‖ ^ 2 ≤
      s k * (8 * mn ^ 2 * ‖g k‖ ^ 2) + s k * (2 * δ ^ 2 * ‖c‖ ^ 2) := by
    intro k
    have h0 : ‖a * g k - b k * c‖ ≤ ‖a * g k‖ + ‖b k * c‖ := norm_sub_le _ _
    have h1 : ‖a * g k - b k * c‖ ^ 2 ≤ 2 * ‖a * g k‖ ^ 2 + 2 * ‖b k * c‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h0 2
      nlinarith [sq_nonneg (‖a * g k‖ - ‖b k * c‖)]
    have h2 : ‖a * g k‖ ^ 2 ≤ 4 * mn ^ 2 * ‖g k‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right ha (by positivity)
    have hbk : ‖b k‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb k) 2
    have h3 : ‖b k * c‖ ^ 2 ≤ δ ^ 2 * ‖c‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right hbk (by positivity)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (hs k)
  have hsum : ∑ k, s k * ‖a * g k - b k * c‖ ^ 2 ≤
      (8 * mn ^ 2) * ∑ k, s k * ‖g k‖ ^ 2 + (2 * δ ^ 2 * ‖c‖ ^ 2) * ∑ k, s k := by
    calc ∑ k, s k * ‖a * g k - b k * c‖ ^ 2
        ≤ ∑ k, (s k * (8 * mn ^ 2 * ‖g k‖ ^ 2) + s k * (2 * δ ^ 2 * ‖c‖ ^ 2)) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = (8 * mn ^ 2) * ∑ k, s k * ‖g k‖ ^ 2 + (2 * δ ^ 2 * ‖c‖ ^ 2) * ∑ k, s k := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
  have hB : 0 ≤ 2 * δ ^ 2 * ‖c‖ ^ 2 := by positivity
  have hsum' : ∑ k, s k * ‖a * g k - b k * c‖ ^ 2 ≤
      (8 * mn ^ 2) * ∑ k, s k * ‖g k‖ ^ 2 + 2 * δ ^ 2 * ‖c‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs1 hB]
  have h5 : ‖c‖ ^ 2 ≤ Φ * ((8 * mn ^ 2) * ∑ k, s k * ‖g k‖ ^ 2) + 2 * Φ * δ ^ 2 * ‖c‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsum' hΦ]
  have h6 : 2 * Φ * δ ^ 2 * ‖c‖ ^ 2 ≤ ‖c‖ ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hδ (sq_nonneg ‖c‖)]
  nlinarith

/-- `‖G_{ii}‖ ≤ 2 ‖m‖` on the event `‖G − m‖_max ≤ δ ≤ ‖m‖`. -/
private theorem entry_diag_sq {ι : Type*} [DecidableEq ι] {G : Matrix ι ι ℂ} {m : ℂ} {δ : ℝ}
    (hG : GoodEvent G m δ) (hδm : δ ≤ ‖m‖) (i : ι) : ‖G i i‖ ^ 2 ≤ 4 * ‖m‖ ^ 2 := by
  have h1 : ‖G i i - m‖ ≤ δ := by simpa [entryErr] using hG i i
  have h2 : ‖G i i‖ ≤ 2 * ‖m‖ := by
    have h3 : ‖G i i‖ ≤ ‖m‖ + ‖G i i - m‖ := by
      calc ‖G i i‖ = ‖m + (G i i - m)‖ := by rw [add_sub_cancel]
        _ ≤ ‖m‖ + ‖G i i - m‖ := norm_add_le _ _
    linarith
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h2 2]

/-- Off-diagonal entries are at most `δ` on the event. -/
private theorem entry_offdiag_le {ι : Type*} [DecidableEq ι] {G : Matrix ι ι ℂ} {m : ℂ} {δ : ℝ}
    (hG : GoodEvent G m δ) {x y : ι} (h : x ≠ y) : ‖G x y‖ ≤ δ := by
  simpa [entryErr, h] using hG x y

/-- The bound behind [I, (5.2)]: on `‖G − m‖_max ≤ δ ≤ |m|`, with `S ≥ 0` of row sums `≤ 1`, the
row large deviation bound with factor `Φ` and `4 Φ δ² ≤ 1`, `|G_{ij}|² ≤ 16 Φ T_{ij}` for
`i ≠ j`. -/
theorem offDiagDet :
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z m : ℂ) (S : Matrix ι ι ℝ)
    (δ Φ : ℝ), H.IsHermitian → 0 < z.im → GoodEvent (green H z) m δ → δ ≤ ‖m‖ →
    (∀ i k, 0 ≤ S i k) → (∀ i, ∑ k, S i k ≤ 1) → 0 ≤ Φ → 4 * Φ * δ ^ 2 ≤ 1 →
    LDERow H (green H z) S Φ →
    ∀ i j, i ≠ j → ‖green H z i j‖ ^ 2 ≤ 16 * Φ * Tvar S (green H z) m i j := by
  intro ι _ _ H z m S δ Φ hH hz hG hδm hS0 hS1 hΦ h4 hL i j hij
  have hGii : green H z i i ≠ 0 := green_diag_ne_zero hH hz i
  have hrow : green H z i j = -(green H z i i) * ∑ k : {a : ι // a ≠ i},
      H i k.1 * greenMinor (green H z) i k.1 j := green_offdiag_eq hH hz (i := i) (j := j) hij.symm
  have hL' := hL i j
  have hid : ∀ k : {a : ι // a ≠ i},
      green H z i i * greenMinor (green H z) i k.1 j
        = green H z i i * green H z k.1 j - green H z k.1 i * green H z i j := by
    intro k
    unfold greenMinor
    field_simp
  have hmain : ‖green H z i j‖ ^ 2 ≤ Φ * ∑ k : {a : ι // a ≠ i},
      S i k.1 * ‖green H z i i * green H z k.1 j - green H z k.1 i * green H z i j‖ ^ 2 := by
    have e1 : ‖green H z i j‖ ^ 2 = ‖green H z i i‖ ^ 2 * ldeRowLHS H (green H z) i j := by
      rw [hrow, norm_mul, norm_neg, mul_pow]
      rfl
    rw [e1]
    calc ‖green H z i i‖ ^ 2 * ldeRowLHS H (green H z) i j
        ≤ ‖green H z i i‖ ^ 2 * (Φ * ldeRowRHS S (green H z) i j) :=
          mul_le_mul_of_nonneg_left hL' (by positivity)
      _ = Φ * ∑ k : {a : ι // a ≠ i},
          S i k.1 * ‖green H z i i * green H z k.1 j - green H z k.1 i * green H z i j‖ ^ 2 := by
          unfold ldeRowRHS
          rw [mul_left_comm, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← hid k, norm_mul, mul_pow]
          ring
  have habs := entry_absorb (green H z i i) (green H z i j)
    (fun k : {a : ι // a ≠ i} => green H z k.1 j)
    (fun k : {a : ι // a ≠ i} => green H z k.1 i) (fun k => S i k.1) ‖m‖ δ Φ (fun k => hS0 i k.1)
    ((entry_sum_subtype_le (fun k => S i k) (hS0 i) i).trans (hS1 i))
    (fun k => entry_offdiag_le hG k.2) (entry_diag_sq hG hδm i) hΦ h4 hmain
  refine habs.trans ?_
  have hle := entry_sum_subtype_le (fun α => S i α * ‖green H z α j‖ ^ 2)
    (fun α => mul_nonneg (hS0 i α) (by positivity)) i
  unfold Tvar
  have := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖m‖)
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 16 * Φ)]


/-- The column form: under the hypotheses of `offDiagDet` with the column large deviation
bound, `|G_{ji}|² ≤ 16 Φ |m|² Σ_α s_{iα} |G_{jα}|²` for `i ≠ j`. -/
theorem offDiagColDet :
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z m : ℂ) (S : Matrix ι ι ℝ)
    (δ Φ : ℝ), H.IsHermitian → 0 < z.im → GoodEvent (green H z) m δ → δ ≤ ‖m‖ →
    (∀ i k, 0 ≤ S i k) → (∀ i, ∑ k, S i k ≤ 1) → 0 ≤ Φ → 4 * Φ * δ ^ 2 ≤ 1 →
    LDECol H (green H z) S Φ →
    ∀ i j, i ≠ j → ‖green H z j i‖ ^ 2 ≤ 16 * Φ * TvarCol S (green H z) m i j := by
  intro ι _ _ H z m S δ Φ hH hz hG hδm hS0 hS1 hΦ h4 hL i j hij
  have hGii : green H z i i ≠ 0 := green_diag_ne_zero hH hz i
  have hcol : green H z j i = -(green H z i i) * ∑ k : {a : ι // a ≠ i},
      greenMinor (green H z) i j k.1 * H k.1 i := by
    have h1 := sum_minorGreen_col (green_mul_sub hH hz.ne') i hGii
      (⟨j, hij.symm⟩ : {a : ι // a ≠ i})
    have h2 : ∑ l : {a : ι // a ≠ i}, minorGreen (green H z) i ⟨j, hij.symm⟩ l *
          (H - z • (1 : Matrix ι ι ℂ)) l.1 i
        = ∑ k : {a : ι // a ≠ i}, greenMinor (green H z) i j k.1 * H k.1 i := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_smul_one_apply_ne H z k.2]
      rfl
    rw [h2] at h1
    rw [h1]
    field_simp
  have hL' := hL i j
  have hid : ∀ k : {a : ι // a ≠ i},
      green H z i i * greenMinor (green H z) i j k.1
        = green H z i i * green H z j k.1 - green H z i k.1 * green H z j i := by
    intro k
    unfold greenMinor
    field_simp
  have hmain : ‖green H z j i‖ ^ 2 ≤ Φ * ∑ k : {a : ι // a ≠ i},
      S i k.1 * ‖green H z i i * green H z j k.1 - green H z i k.1 * green H z j i‖ ^ 2 := by
    have e1 : ‖green H z j i‖ ^ 2 = ‖green H z i i‖ ^ 2 * ldeColLHS H (green H z) i j := by
      rw [hcol, norm_mul, norm_neg, mul_pow]
      rfl
    rw [e1]
    calc ‖green H z i i‖ ^ 2 * ldeColLHS H (green H z) i j
        ≤ ‖green H z i i‖ ^ 2 * (Φ * ldeColRHS S (green H z) i j) :=
          mul_le_mul_of_nonneg_left hL' (by positivity)
      _ = Φ * ∑ k : {a : ι // a ≠ i},
          S i k.1 * ‖green H z i i * green H z j k.1 - green H z i k.1 * green H z j i‖ ^ 2 := by
          unfold ldeColRHS
          rw [mul_left_comm, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← hid k, norm_mul, mul_pow]
          ring
  have habs := entry_absorb (green H z i i) (green H z j i)
    (fun k : {a : ι // a ≠ i} => green H z j k.1)
    (fun k : {a : ι // a ≠ i} => green H z i k.1) (fun k => S i k.1) ‖m‖ δ Φ (fun k => hS0 i k.1)
    ((entry_sum_subtype_le (fun k => S i k) (hS0 i) i).trans (hS1 i))
    (fun k => entry_offdiag_le hG k.2.symm) (entry_diag_sq hG hδm i) hΦ h4 hmain
  refine habs.trans ?_
  have hle := entry_sum_subtype_le (fun α => S i α * ‖green H z j α‖ ^ 2)
    (fun α => mul_nonneg (hS0 i α) (by positivity)) i
  unfold TvarCol
  have := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖m‖)
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 16 * Φ)]


section Instances

end Instances

end RBM8D
