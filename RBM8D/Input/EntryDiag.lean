module

public import RBM8D.Prob.Model
public import RBM8D.Prob.StochDom
public import RBM8D.Prob.Partial
public import RBM8D.Basic.Minor
public import RBM8D.Basic.Domain
public import RBM8D.Basic.Semicircle
public import RBM8D.Profile.Basic
public import RBM8D.Profile.Symbol
public import RBM8D.Input.Entry
public import RBM8D.Kernel.Contraction

@[expose] public section

/-!
# Diagonal entries, the law at `η = 1`, and stability on the bulk strip

The deterministic bound behind [I, (5.3)], the bound behind [II, (8.51)] at `η = 1`, lower bounds
for `|m(z)|` and `|1 − m(z)²|`, and the stability of `1 − m(z)² S` on the bulk strip
([I, (B.19)]).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

/-- `|m(z)| ≥ 1/4` for `Im z > 0`, `|z| ≤ 3`. -/
theorem norm_msc_ge_quarter :
  ∀ z : ℂ, 0 < z.im → ‖z‖ ≤ 3 → 1 / 4 ≤ ‖msc z‖ := by
  intro z hz hz3
  have h1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have h2 : ‖msc z‖ * ‖msc z + z‖ = 1 := by
    rw [← norm_mul, msc_mul]; simp
  have h3 : ‖msc z + z‖ ≤ ‖msc z‖ + ‖z‖ := norm_add_le _ _
  have h4 := norm_nonneg (msc z)
  nlinarith

/-- `|1 − m(z)²| ≥ (2κ)^{1/2}/4` on the strip `|Re z| < 2 − κ`, `0 < Im z ≤ 1`. -/
theorem norm_one_sub_msc_sq_ge :
  ∀ κ : ℝ, 0 < κ → ∀ z : ℂ, |z.re| < 2 - κ → 0 < z.im → z.im ≤ 1 →
    Real.sqrt (2 * κ) / 4 ≤ ‖1 - msc z ^ 2‖ := by
  intro κ hκ z hre him him1
  have hz3 : ‖z‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him] at this
    linarith
  have hm4 := norm_msc_ge_quarter z him hz3
  have hmm := msc_mul z
  set m := msc z with hmdef
  have hs2 : (2 * m + z) ^ 2 = z ^ 2 - 4 := by linear_combination 4 * hmm
  have hone : 1 - m ^ 2 = -(m * (2 * m + z)) := by linear_combination hmm
  have hz2 : ‖2 * m + z‖ ^ 2 = ‖z - 2‖ * ‖z + 2‖ := by
    rw [← norm_pow, hs2, show z ^ 2 - 4 = (z - 2) * (z + 2) by ring, norm_mul]
  have hre' := abs_lt.mp hre
  have hprod : 2 * κ ≤ ‖z - 2‖ * ‖z + 2‖ := by
    have hA : z.re + 2 ≤ ‖z + 2‖ := by
      have := Complex.re_le_norm (z + 2)
      simpa using this
    have hB : 2 - z.re ≤ ‖z - 2‖ := by
      have := Complex.re_le_norm (2 - z)
      rw [norm_sub_rev] at this
      simpa using this
    have hA0 := norm_nonneg (z + 2)
    have hB0 := norm_nonneg (z - 2)
    rcases le_total 0 z.re with h | h
    · nlinarith
    · nlinarith
  have hs : Real.sqrt (2 * κ) ≤ ‖2 * m + z‖ := by
    rw [Real.sqrt_le_left (norm_nonneg _)]
    nlinarith
  rw [hone, norm_neg, norm_mul]
  have hs0 := Real.sqrt_nonneg (2 * κ)
  nlinarith [norm_nonneg (2 * m + z)]

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The centred quadratic form `Σ_{k,l≠i} h_{ik} G^{(i)}_{kl} h_{li} − Σ_{k≠i} s_{ik} G^{(i)}_{kk}`
of the Schur complement formula for `1/G_{ii}`; its squared norm is `ldeQuadLHS`. -/
private def entryDiagZ (H G : Matrix ι ι ℂ) (S : Matrix ι ι ℝ) (i : ι) : ℂ :=
  ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, H i k * greenMinor G i k l * H l i
    - ∑ k : {a : ι // a ≠ i}, (S i k : ℂ) * greenMinor G i k k

private theorem entryDiagZ_sq (H G : Matrix ι ι ℂ) (S : Matrix ι ι ℝ) (i : ι) :
    ldeQuadLHS H G S i = ‖entryDiagZ H G S i‖ ^ 2 := rfl

/-- The error `e_i = h_{ii} − Z_i + G_{ii}^{-1} Σ_k s_{ik} G_{ki} G_{ik}` in
`1/G_{ii} + z + Σ_k s_{ik} G_{kk} = e_i`. -/
private def entryDiagErr (H G : Matrix ι ι ℂ) (S : Matrix ι ι ℝ) (i : ι) : ℂ :=
  H i i - entryDiagZ H G S i + (G i i)⁻¹ * ∑ k, (S i k : ℂ) * (G k i * G i k)

/-- The algebra of the self-consistent equation: `g⁻¹ = e − z − A − m` and `m (m + z) = −1`
give `g − m = m g (A − e)`. -/
private theorem entryDiag_alg {g m z A e : ℂ} (hg : g ≠ 0) (h1 : g⁻¹ = e - z - A - m)
    (hm : m * (m + z) = -1) : g - m = m * g * (A - e) := by
  have h2 : g * (e - z - A - m) = 1 := by rw [← h1]; exact mul_inv_cancel₀ hg
  linear_combination m * h2 + g * hm

/-- The self-consistent equation for `v_i = G_{ii} − m`: `v_i = m G_{ii} ((S v)_i − e_i)`. -/
private theorem entryDiag_selfcons {H : Matrix ι ι ℂ} {z m : ℂ} {S : Matrix ι ι ℝ}
    (hH : H.IsHermitian) (hz : 0 < z.im) (hm : m * (m + z) = -1) (hS : ∀ i, ∑ k, S i k = 1)
    (i : ι) :
    green H z i i - m = m * green H z i i *
      (∑ k, (S i k : ℂ) * (green H z k k - m) - entryDiagErr H (green H z) S i) := by
  set G := green H z with hG
  have hg : G i i ≠ 0 := green_diag_ne_zero hH hz i
  have hschur := green_diag_schur hH hz i
  rw [← hG] at hschur
  have hinv : (G i i)⁻¹ = H i i - z - ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i},
      H i k.1 * greenMinor G i k.1 l.1 * H l.1 i := by
    rw [hschur, inv_inv]; rfl
  have hQ : ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i},
      H i k.1 * greenMinor G i k.1 l.1 * H l.1 i =
      entryDiagZ H G S i + ∑ k : {a : ι // a ≠ i}, (S i k : ℂ) * greenMinor G i k.1 k.1 := by
    unfold entryDiagZ; ring
  set F : ι → ℂ := fun k => (S i k : ℂ) * G k k - (G i i)⁻¹ * ((S i k : ℂ) * (G k i * G i k))
    with hF
  have hFi : F i = 0 := by
    simp only [hF]
    field_simp
    ring
  have hFsum : ∑ k : {a : ι // a ≠ i}, (S i k : ℂ) * greenMinor G i k.1 k.1 =
      ∑ k, F k := by
    have h1 : ∑ k : {a : ι // a ≠ i}, (S i k : ℂ) * greenMinor G i k.1 k.1 =
        ∑ k : {a : ι // a ≠ i}, F k.1 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hF, greenMinor]
      field_simp
    rw [h1, sum_subtype_ne i F, hFi, sub_zero]
  have hF2 : ∑ k, F k =
      ∑ k, (S i k : ℂ) * G k k - (G i i)⁻¹ * ∑ k, (S i k : ℂ) * (G k i * G i k) := by
    simp only [hF, Finset.sum_sub_distrib, Finset.mul_sum]
  have hrow : ∑ k, (S i k : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hS i]; simp
  have hA : ∑ k, (S i k : ℂ) * (G k k - m) = ∑ k, (S i k : ℂ) * G k k - m := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul]
  refine entryDiag_alg (z := z) hg ?_ hm
  rw [hA, hinv, hQ, hFsum, hF2]
  unfold entryDiagErr
  ring

/-- Dropping the term `i` from a sum of nonnegative terms decreases it. -/
private theorem entryDiag_sum_subtype_le (F : ι → ℝ) (hF : ∀ k, 0 ≤ F k) (i : ι) :
    ∑ k : {a : ι // a ≠ i}, F k.1 ≤ ∑ k, F k := by
  rw [sum_subtype_ne i F]
  linarith [hF i]

omit [Fintype ι] in
/-- On the event `‖G − m‖_max ≤ δ`, `δ ≤ |m|/2`, `|m| ≥ 1/4`: `|G_{ii}| ≥ 1/8`. -/
private theorem entryDiag_diag_lower {G : Matrix ι ι ℂ} {m : ℂ} {δ : ℝ} (hG : GoodEvent G m δ)
    (hm4 : 1 / 4 ≤ ‖m‖) (hδ : δ ≤ ‖m‖ / 2) (i : ι) : 1 / 8 ≤ ‖G i i‖ := by
  have h1 : ‖G i i - m‖ ≤ δ := by simpa [entryErr] using hG i i
  have h2 : ‖m‖ ≤ ‖G i i‖ + ‖G i i - m‖ := by
    calc ‖m‖ = ‖G i i - (G i i - m)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖G i i‖ + ‖G i i - m‖ := norm_sub_le _ _
  linarith

omit [Fintype ι] in
/-- On the event, `|G_{ii}| ≤ |m| + δ`. -/
private theorem entryDiag_diag_upper {G : Matrix ι ι ℂ} {m : ℂ} {δ : ℝ} (hG : GoodEvent G m δ)
    (i : ι) : ‖G i i‖ ≤ ‖m‖ + δ := by
  have h1 : ‖G i i - m‖ ≤ δ := by simpa [entryErr] using hG i i
  have h2 : ‖G i i‖ ≤ ‖m‖ + ‖G i i - m‖ := by
    calc ‖G i i‖ = ‖m + (G i i - m)‖ := by rw [add_sub_cancel]
      _ ≤ ‖m‖ + ‖G i i - m‖ := norm_add_le _ _
  linarith

omit [Fintype ι] in
/-- Off-diagonal entries are at most `δ` on the event. -/
private theorem entryDiag_offdiag_le {G : Matrix ι ι ℂ} {m : ℂ} {δ : ℝ} (hG : GoodEvent G m δ)
    {x y : ι} (h : x ≠ y) : ‖G x y‖ ≤ δ := by
  simpa [entryErr, h] using hG x y

omit [Fintype ι] [DecidableEq ι] in
/-- `|G^{(i)}_{kl}|² ≤ 2 |G_{kl}|² + 128 |G_{ki}|² |G_{il}|²` when `|G_{ii}| ≥ 1/8`. -/
private theorem entryDiag_minor_sq {G : Matrix ι ι ℂ} {i : ι} (hlow : 1 / 8 ≤ ‖G i i‖) (k l : ι) :
    ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 128 * (‖G k i‖ ^ 2 * ‖G i l‖ ^ 2) := by
  unfold greenMinor
  set a := G k l with ha
  set b := G k i * G i l / G i i with hb
  have h1 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have := norm_sub_le a b
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a - b), norm_nonneg a, norm_nonneg b]
  have h2 : ‖b‖ ^ 2 ≤ 64 * (‖G k i‖ ^ 2 * ‖G i l‖ ^ 2) := by
    have hpos : 0 < ‖G i i‖ := by linarith
    have hx : 0 ≤ ‖G k i‖ ^ 2 * ‖G i l‖ ^ 2 := by positivity
    have hy : 1 / 64 ≤ ‖G i i‖ ^ 2 := by nlinarith
    rw [hb, norm_div, norm_mul, div_pow, mul_pow, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- The quadratic variance `Σ_{k,l≠i} s_{ik} |G^{(i)}_{kl}|² s_{li}` is at most `34 Λ` on the
event with `δ ≤ |m|/2 ≤ 1/2`. -/
private theorem entryDiag_quadRHS_le {G : Matrix ι ι ℂ} {S : Matrix ι ι ℝ} {m : ℂ} {δ Λ : ℝ}
    (hG : GoodEvent G m δ) (hm4 : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hδ : δ ≤ ‖m‖ / 2)
    (hS0 : ∀ i k, 0 ≤ S i k) (hS2 : ∀ k, ∑ i, S i k ≤ 1)
    (hΛ : ∀ i j, ∑ k, S i k * ‖G k j‖ ^ 2 ≤ Λ) (hΛ0 : 0 ≤ Λ) (i : ι) :
    ldeQuadRHS S G i ≤ 34 * Λ := by
  have hlow := entryDiag_diag_lower hG hm4 hδ i
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hG i i)
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hpt : ∀ k l : {a : ι // a ≠ i}, S i k * ‖greenMinor G i k l‖ ^ 2 * S l i ≤
      2 * (S i k * ‖G k l‖ ^ 2 * S l i) +
        128 * ((S i k * ‖G k i‖ ^ 2) * (‖G i l‖ ^ 2 * S l i)) := by
    intro k l
    have := entryDiag_minor_sq hlow k l
    have h0 : 0 ≤ S i k := hS0 i k
    have h1 : 0 ≤ S l i := hS0 l i
    have := mul_le_mul_of_nonneg_left this (mul_nonneg h0 h1)
    nlinarith
  have hT1 : ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, S i k * ‖G k l‖ ^ 2 * S l i ≤ Λ := by
    rw [Finset.sum_comm]
    calc ∑ l : {a : ι // a ≠ i}, ∑ k : {a : ι // a ≠ i}, S i k * ‖G k l‖ ^ 2 * S l i
        = ∑ l : {a : ι // a ≠ i}, (∑ k : {a : ι // a ≠ i}, S i k * ‖G k l‖ ^ 2) * S l i := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
      _ ≤ ∑ l : {a : ι // a ≠ i}, Λ * S l i := by
          refine Finset.sum_le_sum fun l _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (hS0 l i)
          exact (entryDiag_sum_subtype_le (fun k => S i k * ‖G k l‖ ^ 2)
            (fun k => mul_nonneg (hS0 i k) (by positivity)) i).trans (hΛ i l)
      _ = Λ * ∑ l : {a : ι // a ≠ i}, S l i := by rw [Finset.mul_sum]
      _ ≤ Λ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hΛ0
          exact (entryDiag_sum_subtype_le (fun l => S l i) (fun l => hS0 l i) i).trans (hS2 i)
      _ = Λ := mul_one _
  have hT2a : ∑ k : {a : ι // a ≠ i}, S i k * ‖G k i‖ ^ 2 ≤ Λ :=
    (entryDiag_sum_subtype_le (fun k => S i k * ‖G k i‖ ^ 2)
      (fun k => mul_nonneg (hS0 i k) (by positivity)) i).trans (hΛ i i)
  have hT2b : ∑ l : {a : ι // a ≠ i}, ‖G i l‖ ^ 2 * S l i ≤ 1 / 4 := by
    calc ∑ l : {a : ι // a ≠ i}, ‖G i l‖ ^ 2 * S l i
        ≤ ∑ l : {a : ι // a ≠ i}, δ ^ 2 * S l i := by
          refine Finset.sum_le_sum fun l _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (hS0 l i)
          exact pow_le_pow_left₀ (norm_nonneg _) (entryDiag_offdiag_le hG (Ne.symm l.2)) 2
      _ = δ ^ 2 * ∑ l : {a : ι // a ≠ i}, S l i := by rw [Finset.mul_sum]
      _ ≤ δ ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact (entryDiag_sum_subtype_le (fun l => S l i) (fun l => hS0 l i) i).trans (hS2 i)
      _ ≤ 1 / 4 := by linarith
  have hT2 : ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i},
      (S i k * ‖G k i‖ ^ 2) * (‖G i l‖ ^ 2 * S l i) ≤ Λ * (1 / 4) := by
    rw [← Finset.sum_mul_sum]
    have h0 : 0 ≤ ∑ k : {a : ι // a ≠ i}, S i k * ‖G k i‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 i k) (by positivity)
    have h1 : 0 ≤ ∑ l : {a : ι // a ≠ i}, ‖G i l‖ ^ 2 * S l i :=
      Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (hS0 l i)
    exact mul_le_mul hT2a hT2b h1 hΛ0
  unfold ldeQuadRHS
  calc ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, S i k * ‖greenMinor G i k l‖ ^ 2 * S l i
      ≤ ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i},
          (2 * (S i k * ‖G k l‖ ^ 2 * S l i) +
            128 * ((S i k * ‖G k i‖ ^ 2) * (‖G i l‖ ^ 2 * S l i))) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hpt k l
    _ = 2 * ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, S i k * ‖G k l‖ ^ 2 * S l i +
          128 * ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i},
            (S i k * ‖G k i‖ ^ 2) * (‖G i l‖ ^ 2 * S l i) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 34 * Λ := by nlinarith

/-- The term `G_{ii}^{-1} Σ_k s_{ik} G_{ki} G_{ik}` is at most `12 Λ^{1/2}` on the event. -/
private theorem entryDiag_minor_le {G : Matrix ι ι ℂ} {S : Matrix ι ι ℝ} {m : ℂ} {δ Λ : ℝ}
    (hG : GoodEvent G m δ) (hm4 : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hδ : δ ≤ ‖m‖ / 2)
    (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k = 1)
    (hΛ : ∀ i j, ∑ k, S i k * ‖G k j‖ ^ 2 ≤ Λ) (i : ι) :
    ‖(G i i)⁻¹ * ∑ k, (S i k : ℂ) * (G k i * G i k)‖ ≤ 12 * Real.sqrt Λ := by
  have hlow := entryDiag_diag_lower hG hm4 hδ i
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hG i i)
  have hpos : 0 < ‖G i i‖ := by linarith
  have hGik : ∀ k, ‖G i k‖ ≤ 3 / 2 := by
    intro k
    by_cases hk : i = k
    · subst hk
      have := entryDiag_diag_upper hG i
      linarith
    · have := entryDiag_offdiag_le hG hk
      linarith
  have hCS : (∑ k, S i k * ‖G k i‖) ^ 2 ≤ Λ := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
      (r := fun k => S i k * ‖G k i‖) (f := fun k => S i k) (g := fun k => S i k * ‖G k i‖ ^ 2)
      (fun k _ => hS0 i k) (fun k _ => mul_nonneg (hS0 i k) (by positivity))
      (fun k _ => by
        have := hS0 i k
        nlinarith [mul_nonneg this this, sq_nonneg ‖G k i‖])
    rw [hS1 i, one_mul] at h
    exact h.trans (hΛ i i)
  have hsq : ∑ k, S i k * ‖G k i‖ ≤ Real.sqrt Λ :=
    (le_abs_self _).trans (Real.abs_le_sqrt hCS)
  have hT : ‖∑ k, (S i k : ℂ) * (G k i * G i k)‖ ≤ 3 / 2 * Real.sqrt Λ := by
    calc ‖∑ k, (S i k : ℂ) * (G k i * G i k)‖
        ≤ ∑ k, ‖(S i k : ℂ) * (G k i * G i k)‖ := norm_sum_le _ _
      _ ≤ ∑ k, 3 / 2 * (S i k * ‖G k i‖) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS0 i k)]
          have := hGik k
          have h0 := hS0 i k
          have h1 := norm_nonneg (G k i)
          nlinarith [mul_nonneg h0 h1]
      _ = 3 / 2 * ∑ k, S i k * ‖G k i‖ := by rw [Finset.mul_sum]
      _ ≤ 3 / 2 * Real.sqrt Λ := by linarith
  rw [norm_mul, norm_inv]
  have hinv : (‖G i i‖)⁻¹ ≤ 8 := by
    rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  have h0 := Real.sqrt_nonneg Λ
  calc (‖G i i‖)⁻¹ * ‖∑ k, (S i k : ℂ) * (G k i * G i k)‖
      ≤ 8 * (3 / 2 * Real.sqrt Λ) :=
        mul_le_mul hinv hT (norm_nonneg _) (by norm_num)
    _ = 12 * Real.sqrt Λ := by ring

/-- At `Im z = 1` the Ward identity for the minor resolvent gives
`Σ_l |G^{(i)}_{kl}|² ≤ 1` and `Σ_k |G^{(i)}_{kl}|² ≤ 1`, for `k, l ≠ i`. -/
private theorem entryDiag_ward {H : Matrix ι ι ℂ} {z : ℂ} (hH : H.IsHermitian) (hz : z.im = 1)
    (i : ι) :
    (∀ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, ‖greenMinor (green H z) i k.1 l.1‖ ^ 2 ≤ 1) ∧
    (∀ l : {a : ι // a ≠ i},
      ∑ k : {a : ι // a ≠ i}, ‖greenMinor (green H z) i k.1 l.1‖ ^ 2 ≤ 1) := by
  have hz0 : 0 < z.im := by rw [hz]; exact one_pos
  have hHerm : (H.submatrix (Subtype.val : {a : ι // a ≠ i} → ι) Subtype.val).IsHermitian :=
    hH.submatrix _
  have hGr : green (H.submatrix (Subtype.val : {a : ι // a ≠ i} → ι) Subtype.val) z =
      minorGreen (green H z) i := inv_minor_resolvent hH hz0 i
  have e : ∀ k l : {a : ι // a ≠ i},
      green (H.submatrix (Subtype.val : {a : ι // a ≠ i} → ι) Subtype.val) z k l =
        greenMinor (green H z) i k.1 l.1 := fun k l => by rw [hGr]; rfl
  have hdiag : ∀ k : {a : ι // a ≠ i},
      (green (H.submatrix (Subtype.val : {a : ι // a ≠ i} → ι) Subtype.val) z k k).im ≤ 1 := by
    intro k
    calc _ ≤ ‖green (H.submatrix (Subtype.val : {a : ι // a ≠ i} → ι) Subtype.val) z k k‖ :=
          Complex.im_le_norm _
      _ ≤ |z.im|⁻¹ := norm_green_entry_le hHerm hz0.ne' k k
      _ = 1 := by rw [hz]; simp
  refine ⟨fun k => ?_, fun l => ?_⟩
  · have h := sum_norm_sq_green_row hHerm hz0 k
    rw [hz, div_one] at h
    simp only [e] at h
    rw [h, ← e k k]
    exact hdiag k
  · have h := sum_norm_sq_green_col hHerm hz0 l
    rw [hz, div_one] at h
    simp only [e] at h
    rw [h, ← e l l]
    exact hdiag l

/-- `Im m = |m|² / (1 − |m|²)` at `Im z = 1` gives `|m|² + |m| ≤ 1` and `|m| ≤ 0.6183`. -/
private theorem entryDiag_norm_msc_le {z : ℂ} (hz : z.im = 1) : ‖msc z‖ ≤ 6183 / 10000 := by
  have hz0 : 0 < z.im := by rw [hz]; exact one_pos
  have hmm := msc_mul z
  have him := msc_im_pos hz0
  have hlt := norm_msc_lt_one hz0
  have hm0 := msc_ne_zero z
  set m := msc z with hmdef
  have h1 := congrArg Complex.re hmm
  have h2 := congrArg Complex.im hmm
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, hz,
    Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im] at h1 h2
  have hkey : (m.im + 1) * (m.re ^ 2 + m.im ^ 2) = m.im := by
    linear_combination (-m.im) * h1 + m.re * h2
  have hr2 : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hr0 : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  have hb : m.im ≤ ‖m‖ := Complex.im_le_norm m
  have h3 : ‖m‖ ^ 2 ≤ ‖m‖ * (1 - ‖m‖ ^ 2) := by
    have hq : 0 ≤ 1 - ‖m‖ ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right hb hq
    rw [hr2] at this ⊢
    nlinarith
  have h4 : ‖m‖ ≤ 1 - ‖m‖ ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hr0
    nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

/-- The row large deviation bound turns into `|Σ_{k≠i} h_{ik} G^{(i)}_{kj}|² ≤ Φ σ`, for `j ≠ i`,
when `s ≤ σ` and `Σ_{k≠i} |G^{(i)}_{kj}|² ≤ 1`. -/
private theorem entryDiag_rowLHS_le {H G : Matrix ι ι ℂ} {S : Matrix ι ι ℝ} {σ Φ : ℝ}
    (hSσ : ∀ i k, S i k ≤ σ) (hσ0 : 0 ≤ σ) (hΦ : 0 ≤ Φ) (hL : LDERow H G S Φ) (i j : ι)
    (hwc : ∑ k : {a : ι // a ≠ i}, ‖greenMinor G i k.1 j‖ ^ 2 ≤ 1) :
    ldeRowLHS H G i j ≤ Φ * σ := by
  have h2 : ldeRowRHS S G i j ≤ σ := by
    unfold ldeRowRHS
    calc ∑ k : {a : ι // a ≠ i}, S i k * ‖greenMinor G i k j‖ ^ 2
        ≤ ∑ k : {a : ι // a ≠ i}, σ * ‖greenMinor G i k j‖ ^ 2 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hSσ i k) (sq_nonneg _)
      _ = σ * ∑ k : {a : ι // a ≠ i}, ‖greenMinor G i k j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ σ * 1 := mul_le_mul_of_nonneg_left hwc hσ0
      _ = σ := mul_one _
  exact (hL i j).trans (mul_le_mul_of_nonneg_left h2 hΦ)

/-- The quadratic variance is at most `σ` when `s ≤ σ`, the row sums of `s` are `1` and
`Σ_{l≠i} |G^{(i)}_{kl}|² ≤ 1`. -/
private theorem entryDiag_quadRHS_eta {G : Matrix ι ι ℂ} {S : Matrix ι ι ℝ} {σ : ℝ}
    (hS0 : ∀ i k, 0 ≤ S i k) (hSσ : ∀ i k, S i k ≤ σ) (hS1 : ∀ i, ∑ k, S i k = 1) (i : ι)
    (hwr : ∀ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, ‖greenMinor G i k.1 l.1‖ ^ 2 ≤ 1) :
    ldeQuadRHS S G i ≤ σ := by
  have hσ0 : 0 ≤ σ := (hS0 i i).trans (hSσ i i)
  unfold ldeQuadRHS
  calc ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i}, S i k * ‖greenMinor G i k l‖ ^ 2 * S l i
      ≤ ∑ k : {a : ι // a ≠ i}, ∑ l : {a : ι // a ≠ i},
          σ * (S i k * ‖greenMinor G i k l‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        have h0 : 0 ≤ S i k * ‖greenMinor G i k l‖ ^ 2 := mul_nonneg (hS0 i k) (sq_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left (hSσ l i) h0]
    _ = σ * ∑ k : {a : ι // a ≠ i}, S i k * ∑ l : {a : ι // a ≠ i}, ‖greenMinor G i k l‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ σ * ∑ k : {a : ι // a ≠ i}, S i k * 1 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hσ0
        exact mul_le_mul_of_nonneg_left (hwr k) (hS0 i k)
    _ ≤ σ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hσ0
        simp only [mul_one]
        exact (entryDiag_sum_subtype_le (fun k => S i k) (hS0 i) i).trans (hS1 i).le
    _ = σ := mul_one _

omit [DecidableEq ι] in
/-- At `Im z = 1`: `|G_{ii}^{-1} Σ_k s_{ik} G_{ki} G_{ik}| ≤ 2 ρ` when `|G_{xy}| ≤ 1`,
`|G_{ik}| ≤ ρ |G_{ii}|` for `k ≠ i`, and `s_{ii} ≤ σ ≤ ρ`. -/
private theorem entryDiag_minor_eta {G : Matrix ι ι ℂ} {S : Matrix ι ι ℝ} {σ ρ : ℝ} (i : ι)
    (hS0 : ∀ i k, 0 ≤ S i k) (hSσ : ∀ i k, S i k ≤ σ) (hS1 : ∀ i, ∑ k, S i k = 1)
    (hσρ : σ ≤ ρ) (hG1 : ∀ x y, ‖G x y‖ ≤ 1) (hGii : G i i ≠ 0)
    (hrow : ∀ k, k ≠ i → ‖G i k‖ ≤ ‖G i i‖ * ρ) :
    ‖(G i i)⁻¹ * ∑ k, (S i k : ℂ) * (G k i * G i k)‖ ≤ 2 * ρ := by
  classical
  have hpos : 0 < ‖G i i‖ := norm_pos_iff.mpr hGii
  have hρ0 : 0 ≤ ρ := by
    have h := hrow
    by_cases hι : ∃ k, k ≠ i
    · obtain ⟨k, hk⟩ := hι
      have := h k hk
      have h0 := norm_nonneg (G i k)
      nlinarith
    · have : 0 ≤ σ := (hS0 i i).trans (hSσ i i)
      linarith
  have hterm : ∀ k, ‖(G i i)⁻¹ * (G k i * G i k)‖ ≤ ρ + if k = i then 1 else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [ite_eq_left rfl, norm_mul, norm_mul, norm_inv]
      have := hG1 k k
      have h0 : ρ ≥ 0 := hρ0
      field_simp
      linarith
    · rw [ite_eq_right hk, add_zero, norm_mul, norm_mul, norm_inv]
      have h1 := hG1 k i
      have h2 := hrow k hk
      have h3 := norm_nonneg (G k i)
      have h4 := norm_nonneg (G i k)
      rw [inv_mul_le_iff₀ hpos]
      calc ‖G k i‖ * ‖G i k‖ ≤ 1 * (‖G i i‖ * ρ) := mul_le_mul h1 h2 h4 zero_le_one
        _ = ‖G i i‖ * ρ := one_mul _
  calc ‖(G i i)⁻¹ * ∑ k, (S i k : ℂ) * (G k i * G i k)‖
      = ‖∑ k, (S i k : ℂ) * ((G i i)⁻¹ * (G k i * G i k))‖ := by
        rw [Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ ∑ k, ‖(S i k : ℂ) * ((G i i)⁻¹ * (G k i * G i k))‖ := norm_sum_le _ _
    _ ≤ ∑ k, S i k * (ρ + if k = i then 1 else 0) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS0 i k)]
        exact mul_le_mul_of_nonneg_left (hterm k) (hS0 i k)
    _ = ρ + S i i := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hS1 i, one_mul,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ ≤ 2 * ρ := by linarith [hSσ i i]

end Core

/-- The bound behind [I, (5.3)]: with `m(m + z) = −1`, `1/4 ≤ |m| ≤ 1`, `‖G − m‖_max ≤ δ`,
`δ ≤ |m|/2`, `δ ≤ 1`, `S ≥ 0` with row sums `1` and column sums `≤ 1`, the quadratic and diagonal
large deviation bounds with factor `Φ ≥ 1`, `Σ_k s_{ik} |G_{kj}|² ≤ Λ` and `s_{ij} ≤ Λ`, and
stability of `1 − m² S` with constant `K ≥ 0`, `Kδ ≤ 1/2`: `|G_{ii} − m| ≤ 100 K Φ Λ^{1/2}`. -/
theorem diagDet :
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z m : ℂ) (S : Matrix ι ι ℝ)
    (δ Φ Λ K : ℝ), H.IsHermitian → 0 < z.im → m * (m + z) = -1 → 1 / 4 ≤ ‖m‖ → ‖m‖ ≤ 1 →
    GoodEvent (green H z) m δ → δ ≤ ‖m‖ / 2 → δ ≤ 1 →
    (∀ i k, 0 ≤ S i k) → (∀ i, ∑ k, S i k = 1) → (∀ k, ∑ i, S i k ≤ 1) → 1 ≤ Φ →
    LDEQuad H (green H z) S Φ → (∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) →
    (∀ i j, ∑ k, S i k * ‖green H z k j‖ ^ 2 ≤ Λ) → (∀ i j, S i j ≤ Λ) →
    Stable S (m ^ 2) K → 0 ≤ K → K * δ ≤ 1 / 2 →
    ∀ i, ‖green H z i i - m‖ ≤ 100 * K * Φ * Real.sqrt Λ := by
  intro ι _ _ H z m S δ Φ Λ K hH hz hm hm4 hm1 hG hδm hδ1 hS0 hS1 hS2 hΦ hQ hdiag hΛ hΛS hstab
    hK hKδ i
  set G := green H z with hGdef
  have hΛ0 : 0 ≤ Λ := (hS0 i i).trans (hΛS i i)
  set r := Real.sqrt Λ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = Λ := Real.sq_sqrt hΛ0
  have hΦ0 : 0 ≤ Φ := by linarith
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hG i i)
  have hδ12 : δ ≤ 1 / 2 := by linarith
  have hS1' : ∀ k, ∑ j, S k j ≤ 1 := fun k => (hS1 k).le
  -- the error `e_k` is at most `19 Φ Λ^{1/2}`
  have he : ∀ k, ‖entryDiagErr H G S k‖ ≤ 19 * Φ * r := by
    intro k
    have h1 : ‖H k k‖ ≤ Φ * r := by
      refine le_of_sq_le_sq ?_ (by positivity)
      calc ‖H k k‖ ^ 2 ≤ Φ * S k k := hdiag k
        _ ≤ Φ * Λ := mul_le_mul_of_nonneg_left (hΛS k k) hΦ0
        _ = Φ * r ^ 2 := by rw [hr2]
        _ ≤ (Φ * r) ^ 2 := by nlinarith [sq_nonneg r]
    have h2 : ‖entryDiagZ H G S k‖ ≤ 6 * Φ * r := by
      refine le_of_sq_le_sq ?_ (by positivity)
      have hq := hQ k
      rw [entryDiagZ_sq] at hq
      have hr' := entryDiag_quadRHS_le hG hm4 hm1 hδm hS0 hS2 hΛ hΛ0 k
      calc ‖entryDiagZ H G S k‖ ^ 2 ≤ Φ * ldeQuadRHS S G k := hq
        _ ≤ Φ * (34 * Λ) := mul_le_mul_of_nonneg_left hr' hΦ0
        _ = 34 * Φ * r ^ 2 := by rw [hr2]; ring
        _ ≤ (6 * Φ * r) ^ 2 := by nlinarith [sq_nonneg r, mul_nonneg hΦ0 (sq_nonneg r)]
    have h3 := entryDiag_minor_le hG hm4 hm1 hδm hS0 hS1 hΛ k
    have h4 : 12 * r ≤ 12 * Φ * r := by nlinarith
    calc ‖entryDiagErr H G S k‖
        ≤ ‖H k k‖ + ‖entryDiagZ H G S k‖ + ‖(G k k)⁻¹ * ∑ j, (S k j : ℂ) * (G j k * G k j)‖ := by
          unfold entryDiagErr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 19 * Φ * r := by linarith
  -- the maximum of `|v_k|`, `v_k = G_{kk} − m`
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun k => ‖G k k - m‖) ⟨i, Finset.mem_univ i⟩
  set V := ‖G k₀ k₀ - m‖ with hV
  have hv : ∀ k, ‖G k k - m‖ ≤ V := fun k => hk₀ k (Finset.mem_univ k)
  have hV0 : 0 ≤ V := norm_nonneg _
  have hSv : ∀ k, ‖∑ j, (S k j : ℂ) * (G j j - m)‖ ≤ V := by
    intro k
    calc ‖∑ j, (S k j : ℂ) * (G j j - m)‖ ≤ ∑ j, ‖(S k j : ℂ) * (G j j - m)‖ := norm_sum_le _ _
      _ ≤ ∑ j, S k j * V := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS0 k j)]
          exact mul_le_mul_of_nonneg_left (hv j) (hS0 k j)
      _ = V := by rw [← Finset.sum_mul, hS1 k, one_mul]
  have hvk : ∀ k, ‖G k k - m‖ ≤ δ := by
    intro k
    simpa [entryErr] using hG k k
  have hB : ∀ k, ‖(G k k - m) - m ^ 2 * ∑ j, (S k j : ℂ) * (G j j - m)‖ ≤
      3 / 2 * (19 * Φ * r) + δ * V := by
    intro k
    have hsc := entryDiag_selfcons hH hz hm hS1 k
    rw [← hGdef] at hsc
    set A := ∑ j, (S k j : ℂ) * (G j j - m) with hA
    set e := entryDiagErr H G S k with he'
    have hGk : G k k = m + (G k k - m) := by ring
    have hid : (G k k - m) - m ^ 2 * A = -(m ^ 2 * e) + m * (G k k - m) * (A - e) := by
      have : G k k - m = m * (m + (G k k - m)) * (A - e) := by
        rw [← hGk]; exact hsc
      linear_combination this
    rw [hid]
    have hm2 : ‖m ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm1
    have hek := he k
    have h1 : ‖m ^ 2 * e‖ ≤ 19 * Φ * r := by
      rw [norm_mul]
      calc ‖m ^ 2‖ * ‖e‖ ≤ 1 * (19 * Φ * r) :=
            mul_le_mul hm2 hek (norm_nonneg _) zero_le_one
        _ = 19 * Φ * r := one_mul _
    have h2 : ‖m * (G k k - m) * (A - e)‖ ≤ δ * (V + 19 * Φ * r) := by
      rw [norm_mul, norm_mul]
      have hAe : ‖A - e‖ ≤ V + 19 * Φ * r := (norm_sub_le _ _).trans (add_le_add (hSv k) hek)
      calc ‖m‖ * ‖G k k - m‖ * ‖A - e‖ ≤ 1 * δ * (V + 19 * Φ * r) := by
            refine mul_le_mul (mul_le_mul hm1 (hvk k) (norm_nonneg _) zero_le_one) hAe
              (norm_nonneg _) (by positivity)
        _ = δ * (V + 19 * Φ * r) := by ring
    calc ‖-(m ^ 2 * e) + m * (G k k - m) * (A - e)‖
        ≤ ‖-(m ^ 2 * e)‖ + ‖m * (G k k - m) * (A - e)‖ := norm_add_le _ _
      _ ≤ 19 * Φ * r + δ * (V + 19 * Φ * r) := by rw [norm_neg]; exact add_le_add h1 h2
      _ ≤ 3 / 2 * (19 * Φ * r) + δ * V := by
          have : 0 ≤ 19 * Φ * r := by positivity
          nlinarith
  have hst := hstab (fun k => G k k - m) _ hB k₀
  have hV3 : V ≤ 3 * K * (19 * Φ * r) := by
    have h1 : K * (3 / 2 * (19 * Φ * r) + δ * V) =
        3 / 2 * K * (19 * Φ * r) + (K * δ) * V := by ring
    have h2 : (K * δ) * V ≤ 1 / 2 * V := mul_le_mul_of_nonneg_right hKδ hV0
    change V ≤ K * (3 / 2 * (19 * Φ * r) + δ * V) at hst
    nlinarith
  calc ‖G i i - m‖ ≤ V := hv i
    _ ≤ 3 * K * (19 * Φ * r) := hV3
    _ ≤ 100 * K * Φ * r := by
        have : 0 ≤ K * Φ * r := by positivity
        nlinarith

/-- The bound behind [II, (8.51)] at `η = 1`: with `Im z = 1`, `|Re z| ≤ 2`, `S ≥ 0` with row sums
`1` and entries `≤ σ`, the row, quadratic and diagonal large deviation bounds with factor `Φ ≥ 1`
and `Φ σ ≤ 1`: `|G_{ij} − δ_{ij} m(z)| ≤ 18 (Φ σ)^{1/2}`. -/
theorem eta1Det :
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) (S : Matrix ι ι ℝ)
    (σ Φ : ℝ), H.IsHermitian → z.im = 1 → |z.re| ≤ 2 →
    (∀ i k, 0 ≤ S i k) → (∀ i, ∑ k, S i k = 1) → (∀ i k, S i k ≤ σ) → 1 ≤ Φ → Φ * σ ≤ 1 →
    LDERow H (green H z) S Φ → LDEQuad H (green H z) S Φ → (∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) →
    ∀ i j, ‖entryErr (green H z) (msc z) i j‖ ≤ 18 * Real.sqrt (Φ * σ) := by
  intro ι _ _ H z S σ Φ hH hz1 _hre hS0 hS1 hSσ hΦ hΦσ hRow hQuad hdiag i j
  have hz : 0 < z.im := by rw [hz1]; exact one_pos
  set G := green H z with hGdef
  set m := msc z with hmdef
  have hmm : m * (m + z) = -1 := msc_mul z
  have hσ0 : 0 ≤ σ := (hS0 i i).trans (hSσ i i)
  have hΦ0 : 0 ≤ Φ := by linarith
  have hσ1 : σ ≤ 1 := by nlinarith
  set ρ := Real.sqrt (Φ * σ) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = Φ * σ := Real.sq_sqrt (mul_nonneg hΦ0 hσ0)
  have hσρ : σ ≤ ρ := by
    refine le_of_sq_le_sq ?_ hρ0
    nlinarith
  have hG1 : ∀ x y, ‖G x y‖ ≤ 1 := by
    intro x y
    have := norm_green_entry_le hH hz.ne' x y
    rwa [hz1, abs_one, inv_one] at this
  have hGne : ∀ k, G k k ≠ 0 := fun k => green_diag_ne_zero hH hz k
  -- off-diagonal entries: `|G_{kj}| ≤ |G_{kk}| ρ` for `j ≠ k`
  have hoff : ∀ k j, j ≠ k → ‖G k j‖ ≤ ‖G k k‖ * ρ := by
    intro k j hjk
    have hrowle : ldeRowLHS H G k j ≤ Φ * σ :=
      entryDiag_rowLHS_le hSσ hσ0 hΦ0 hRow k j ((entryDiag_ward hH hz1 k).2 ⟨j, hjk⟩)
    have hform : G k j = -(G k k) * ∑ l : {a : ι // a ≠ k}, H k l.1 * greenMinor G k l.1 j :=
      green_offdiag_eq hH hz hjk
    have e1 : ‖G k j‖ ^ 2 = ‖G k k‖ ^ 2 * ldeRowLHS H G k j := by
      rw [hform, norm_mul, norm_neg, mul_pow]
      rfl
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [e1, mul_pow, hρ2]
    exact mul_le_mul_of_nonneg_left hrowle (sq_nonneg _)
  -- the error `e_k` is at most `4 ρ`
  have he : ∀ k, ‖entryDiagErr H G S k‖ ≤ 4 * ρ := by
    intro k
    have h1 : ‖H k k‖ ≤ ρ := by
      refine le_of_sq_le_sq ?_ hρ0
      calc ‖H k k‖ ^ 2 ≤ Φ * S k k := hdiag k
        _ ≤ Φ * σ := mul_le_mul_of_nonneg_left (hSσ k k) hΦ0
        _ = ρ ^ 2 := hρ2.symm
    have h2 : ‖entryDiagZ H G S k‖ ≤ ρ := by
      refine le_of_sq_le_sq ?_ hρ0
      have hq := hQuad k
      rw [entryDiagZ_sq] at hq
      calc ‖entryDiagZ H G S k‖ ^ 2 ≤ Φ * ldeQuadRHS S G k := hq
        _ ≤ Φ * σ := mul_le_mul_of_nonneg_left
            (entryDiag_quadRHS_eta hS0 hSσ hS1 k (entryDiag_ward hH hz1 k).1) hΦ0
        _ = ρ ^ 2 := hρ2.symm
    have h3 := entryDiag_minor_eta k hS0 hSσ hS1 hσρ hG1 (hGne k) (fun l hl => hoff k l hl)
    calc ‖entryDiagErr H G S k‖
        ≤ ‖H k k‖ + ‖entryDiagZ H G S k‖ + ‖(G k k)⁻¹ * ∑ j, (S k j : ℂ) * (G j k * G k j)‖ := by
          unfold entryDiagErr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 4 * ρ := by linarith
  by_cases hij : i = j
  · subst hij
    -- the diagonal entry: contraction at `Im z = 1`
    have hr := entryDiag_norm_msc_le hz1
    have hr0 := norm_nonneg m
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
      (fun k => ‖G k k - m‖) ⟨i, Finset.mem_univ i⟩
    set V := ‖G k₀ k₀ - m‖ with hV
    have hv : ∀ k, ‖G k k - m‖ ≤ V := fun k => hk₀ k (Finset.mem_univ k)
    have hV0 : 0 ≤ V := norm_nonneg _
    have hSv : ‖∑ j, (S k₀ j : ℂ) * (G j j - m)‖ ≤ V := by
      calc ‖∑ j, (S k₀ j : ℂ) * (G j j - m)‖ ≤ ∑ j, ‖(S k₀ j : ℂ) * (G j j - m)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j, S k₀ j * V := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS0 k₀ j)]
            exact mul_le_mul_of_nonneg_left (hv j) (hS0 k₀ j)
        _ = V := by rw [← Finset.sum_mul, hS1 k₀, one_mul]
    have hsc := entryDiag_selfcons hH hz hmm hS1 k₀
    rw [← hGdef] at hsc
    have hV1 : V ≤ ‖m‖ * (V + 4 * ρ) := by
      change ‖G k₀ k₀ - m‖ ≤ _
      rw [hsc, norm_mul, norm_mul]
      have hAe : ‖∑ j, (S k₀ j : ℂ) * (G j j - m) - entryDiagErr H G S k₀‖ ≤ V + 4 * ρ :=
        (norm_sub_le _ _).trans (add_le_add hSv (he k₀))
      calc ‖m‖ * ‖G k₀ k₀‖ * ‖∑ j, (S k₀ j : ℂ) * (G j j - m) - entryDiagErr H G S k₀‖
          ≤ ‖m‖ * 1 * (V + 4 * ρ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hG1 k₀ k₀) hr0) hAe (norm_nonneg _)
              (by positivity)
        _ = ‖m‖ * (V + 4 * ρ) := by ring
    have hV2 : V ≤ 162 / 100 * (4 * ρ) := by
      have h1 : (1 - 6183 / 10000) * V ≤ (1 - ‖m‖) * V :=
        mul_le_mul_of_nonneg_right (by linarith) hV0
      nlinarith
    have hentry : ‖entryErr G m i i‖ = ‖G i i - m‖ := by simp [entryErr]
    rw [hentry]
    calc ‖G i i - m‖ ≤ V := hv i
      _ ≤ 162 / 100 * (4 * ρ) := hV2
      _ ≤ 18 * ρ := by linarith
  · have hent : ‖entryErr G m i j‖ = ‖G i j‖ := by simp [entryErr, hij]
    rw [hent]
    have h1 := hoff i j (Ne.symm hij)
    have h2 := hG1 i i
    calc ‖G i j‖ ≤ ‖G i i‖ * ρ := h1
      _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right h2 hρ0
      _ ≤ 18 * ρ := by linarith

section Stability

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Each row sum of `A` is at most `opNormInf A`. -/
private theorem entryDiag_row_le_opNormInf (A : Matrix ι ι ℂ) (x : ι) :
    ∑ y, ‖A x y‖ ≤ opNormInf A := by
  unfold opNormInf
  have := NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun x => ∑ y, ‖A x y‖₊) (Finset.mem_univ x))
  simpa only [NNReal.coe_sum, coe_nnnorm] using this

omit [DecidableEq ι] in
/-- A matrix acts on bounded vectors with the bound `opNormInf`. -/
private theorem entryDiag_mulVec_le (M : Matrix ι ι ℂ) (w : ι → ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hw : ∀ j, ‖w j‖ ≤ b) (i : ι) : ‖(M *ᵥ w) i‖ ≤ opNormInf M * b := by
  classical
  calc ‖(M *ᵥ w) i‖ = ‖∑ j, M i j * w j‖ := rfl
    _ ≤ ∑ j, ‖M i j * w j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * b := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hw j) (norm_nonneg _)
    _ = (∑ j, ‖M i j‖) * b := by rw [Finset.sum_mul]
    _ ≤ opNormInf M * b := mul_le_mul_of_nonneg_right (entryDiag_row_le_opNormInf M i) hb

/-- `A_1 v = (m² S v + v) / 2`, with `A_1 = (m² S + 1) / 2`. -/
private theorem entryDiag_Ashift_mulVec (S : Matrix ι ι ℝ) (m : ℂ) (v : ι → ℂ) (k : ι) :
    (Ashift m 1 S *ᵥ v) k = (1 / 2 : ℂ) * (m ^ 2 * ∑ j, (S k j : ℂ) * v j + v k) := by
  have h : ∀ x, (Ashift m 1 S) k x * v x =
      (1 / 2 : ℂ) * (m ^ 2 * ((S k x : ℂ) * v x)) + (1 / 2 : ℂ) * (if k = x then v x else 0) := by
    intro x
    simp only [Ashift, Matrix.smul_apply, Matrix.add_apply, cmat, Matrix.map_apply,
      Matrix.one_apply, smul_eq_mul, Complex.ofReal_one]
    split_ifs <;> ring
  simp only [Matrix.mulVec, dotProduct, h, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- Stability of `1 − m² S` from the decay `‖A_1^k‖ ≤ (1 − c)^{⌊k/n⌋}` of the powers of
`A_1 = (m² S + 1)/2`, with constant `n/c`. -/
private theorem entryDiag_stable_of_pow (S : Matrix ι ι ℝ) (m : ℂ) {n : ℕ} {c : ℝ} (hc : 0 < c)
    (hpow : ∀ k, opNormInf (Ashift m 1 S ^ k) ≤ (1 - c) ^ (k / n)) (hn : 1 ≤ n) :
    Stable S (m ^ 2) (n / c) := by
  intro v B hB i
  set A := Ashift m 1 S with hA
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i)
  set w : ι → ℂ := (1 - A) *ᵥ v with hw
  have hwk : ∀ k, ‖w k‖ ≤ B / 2 := by
    intro k
    have : w k = (1 / 2 : ℂ) * (v k - m ^ 2 * ∑ j, (S k j : ℂ) * v j) := by
      rw [hw, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, hA, entryDiag_Ashift_mulVec]
      ring
    rw [this, norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h12]
    linarith [hB k]
  have hdecomp : v = A ^ n *ᵥ v + (∑ k ∈ Finset.range n, A ^ k) *ᵥ w := by
    rw [hw, Matrix.mulVec_mulVec, geom_sum_mul_neg, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun k => ‖v k‖) ⟨i, Finset.mem_univ i⟩
  set V := ‖v k₀‖ with hV
  have hv : ∀ k, ‖v k‖ ≤ V := fun k => hk₀ k (Finset.mem_univ k)
  have hV0 : 0 ≤ V := norm_nonneg _
  have h1 : ‖(A ^ n *ᵥ v) k₀‖ ≤ (1 - c) * V := by
    refine (entryDiag_mulVec_le _ v hV0 hv k₀).trans ?_
    have := hpow n
    rw [Nat.div_self (by omega), pow_one] at this
    exact mul_le_mul_of_nonneg_right this hV0
  have h2 : ‖((∑ k ∈ Finset.range n, A ^ k) *ᵥ w) k₀‖ ≤ n * (B / 2) := by
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    calc ‖∑ k ∈ Finset.range n, (A ^ k *ᵥ w) k₀‖
        ≤ ∑ k ∈ Finset.range n, ‖(A ^ k *ᵥ w) k₀‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range n, B / 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkn : k < n := Finset.mem_range.mp hk
          refine (entryDiag_mulVec_le _ w (by linarith) hwk k₀).trans ?_
          have := hpow k
          rw [Nat.div_eq_of_lt hkn, pow_zero] at this
          calc opNormInf (A ^ k) * (B / 2) ≤ 1 * (B / 2) :=
                mul_le_mul_of_nonneg_right this (by linarith)
            _ = B / 2 := one_mul _
      _ = n * (B / 2) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h3 : V ≤ (1 - c) * V + n * (B / 2) := by
    have h := congrFun hdecomp k₀
    calc V = ‖v k₀‖ := rfl
      _ = ‖(A ^ n *ᵥ v) k₀ + ((∑ k ∈ Finset.range n, A ^ k) *ᵥ w) k₀‖ := by
          conv_lhs => rw [h]
          rfl
      _ ≤ ‖(A ^ n *ᵥ v) k₀‖ + ‖((∑ k ∈ Finset.range n, A ^ k) *ᵥ w) k₀‖ := norm_add_le _ _
      _ ≤ (1 - c) * V + n * (B / 2) := add_le_add h1 h2
  have h4 : c * V ≤ n * (B / 2) := by linarith
  have h5 : V ≤ n / c * B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact (hv i).trans h5

end Stability

/-- [I, (B.19)] in the form used: on `adm(c₀, c₁)` for `W ≥ W₀`, `1 − m(z)² S` is stable with a
constant `K` uniform in `z` on the strip `|Re z| < 2 − κ`, `0 < Im z ≤ 1`. -/
theorem stable_Smat_strip :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ), 0 < c₀ → 0 < c₁ → ∀ κ : ℝ, 0 < κ →
    ∃ K W₀ : ℝ, 0 ≤ K ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z : ℂ, |z.re| < 2 - κ → 0 < z.im → z.im ≤ 1 → Stable (Smat P.ψ W L) (msc z ^ 2) K := by
  intro d P c₀ c₁ hc₀ hc₁ κ hκ
  obtain ⟨⟨c', hc'⟩, -, ⟨C, hC⟩, W₁, hW₁⟩ := discharge d P c₀ c₁ hc₀ hc₁
  have hδ₀ : 0 < Real.sqrt (2 * κ) / 4 := by positivity
  obtain ⟨n, hn, c₁', hc₁', W₂, hcon⟩ :=
    contraction_torus_pow d c₀ c₁ hc₀ hc₁ P.ψ c' hc' C _ 1 hδ₀ one_pos
  refine ⟨n / c₁', max W₁ W₂, by positivity, ?_⟩
  intro W L _ hadm hW z hre him him1
  have hvar := (hW₁ W L hadm ((le_max_left _ _).trans hW)).2
  have hm1 : ‖msc z‖ ≤ 1 := (norm_msc_lt_one him).le
  have hδ := norm_one_sub_msc_sq_ge κ hκ z hre him him1
  exact entryDiag_stable_of_pow _ _ hc₁'
    (hcon W L hadm ((le_max_right _ _).trans hW) _ hvar (hC W L hadm) _ hm1 hδ) hn

section Instances

end Instances

section Witness

open scoped SchwartzMap Nat ContDiff FourierTransform

end Witness

end RBM8D
