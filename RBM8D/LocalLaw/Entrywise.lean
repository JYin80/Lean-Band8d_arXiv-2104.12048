import RBM8D.LocalLaw.Defs
import RBM8D.Prob.Net
import RBM8D.Prob.PartialPoly
import RBM8D.Profile.Decay

/-!
# The entrywise bound on `T` [II, Lemma 7.4] = [I, Lemma 5.4]: base case

Facts for the proof of [II, Lemma 7.4] from the high moment bound [II, Lemma 8.1]:

* the sizes `(W, L)` lie in `adm(c₀, c₁)` and `W → ∞` eventually along `llFilter`;
* the exponent `c = min(c₀ᵀ − (n − 1) ε₀, d/4 − ε₀/2)` of [II, Lemma 8.1] and the sequence
  `Φ̃_k = W^{−d/2+ε₀−kc/2}`, so that `Φ̃₀ = W^{−d/2+ε₀}` and `Φ̃_{k+1}² = W^{−c} Φ̃_k²`;
* the base case: [II, (7.7)] with `Σ_α s_{xα} = 1` and `s_{xy} ≤ C B_{xy}` gives [II, (8.1)] at
  `Φ̃₀`, from `T_{xy} ≤ 2 X² + 2 s_{xy}` when `‖G − m‖_max ≤ X`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

open Graphs

/-! ## Deterministic steps -/

/-- Eventually along the filter, `(W, L) ∈ adm(c₀, c₁)`. -/
private lemma Entrywise_ev_adm (d n : ℕ) (c₀ c₁ c₀T : ℝ) :
    ∀ᶠ p in llFilter d n c₀ c₁ c₀T, p.1 ∈ adm c₀ c₁ :=
  (tendsto_comap.eventually (inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _))
    : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁).filter_mono inf_le_left

/-- `W → ∞` along the filter. -/
private lemma Entrywise_tendsto (d n : ℕ) (c₀ c₁ c₀T : ℝ) :
    Tendsto sizeW (llFilter d n c₀ c₁ c₀T) atTop :=
  (tendsto_sizeW_admFilterL c₀ c₁).mono_left inf_le_left

/-- Eventually along the filter, `S` is symmetric, nonnegative, with row sums `1`. -/
private lemma Entrywise_ev_Smat (d n : ℕ) (P : Profile d) (c₀ c₁ c₀T : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) : ∀ᶠ p in llFilter d n c₀ c₁ c₀T, (Smat P.ψ p.1.1 p.1.2).IsSymm ∧
      (∀ x y, 0 ≤ Smat P.ψ p.1.1 p.1.2 x y) ∧ (∀ x, ∑ y, Smat P.ψ p.1.1 p.1.2 x y = 1) := by
  obtain ⟨W₁, h₁⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, h₂⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  filter_upwards [Entrywise_ev_adm d n c₀ c₁ c₀T,
    (Entrywise_tendsto d n c₀ c₁ c₀T).eventually (eventually_ge_atTop (max W₁ W₂))] with p hp hW
  change max W₁ W₂ ≤ (p.1.1 : ℝ) at hW
  obtain ⟨hs, hn⟩ := h₁ p.1.1 p.1.2 hp ((le_max_left _ _).trans hW)
  obtain ⟨-, hrow, -⟩ :=
    mem_doublyStochastic_iff_sum.mp (h₂ p.1.1 p.1.2 hp ((le_max_right _ _).trans hW))
  exact ⟨hs, hn, hrow⟩

/-! ## The profile bound `s_{xy} ≤ C B_{xy}` -/

/-- Real inequality behind `s_{xy} ≤ C B_{xy}`: from `f (1 + (r/W)^m) ≤ A / W^{m+2}`,
`f ≤ 2^m A W^{−2} (r + W)^{−m}`. -/
private lemma Entrywise_decay_alg {W r f A : ℝ} (m : ℕ) (hW : 0 < W) (hr : 0 ≤ r) (hf : 0 ≤ f)
    (h : f * (1 + (r / W) ^ m) ≤ A / W ^ (m + 2)) :
    f ≤ 2 ^ m * A * (W ^ (-2 : ℝ) * (r + W) ^ (-(m : ℝ))) := by
  have hrW : 0 ≤ r / W := div_nonneg hr hW.le
  have hpow : (r + W) ^ m ≤ 2 ^ m * W ^ m * (1 + (r / W) ^ m) := by
    have e1 : (r + W) ^ m = W ^ m * (r / W + 1) ^ m := by
      rw [← mul_pow]; congr 1; field_simp
    have e2 := add_pow_le hrW zero_le_one m
    have e3 : (2 : ℝ) ^ (m - 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le m 1)
    rw [one_pow] at e2
    rw [e1]
    have e4 : (r / W + 1) ^ m ≤ 2 ^ m * ((r / W) ^ m + 1) :=
      e2.trans (mul_le_mul_of_nonneg_right e3 (by positivity))
    calc W ^ m * (r / W + 1) ^ m ≤ W ^ m * (2 ^ m * ((r / W) ^ m + 1)) :=
          mul_le_mul_of_nonneg_left e4 (by positivity)
      _ = 2 ^ m * W ^ m * (1 + (r / W) ^ m) := by ring
  have hWm : 0 < W ^ m := pow_pos hW m
  have hW2 : 0 < W ^ 2 := pow_pos hW 2
  have hrWm : 0 < (r + W) ^ m := pow_pos (by linarith) m
  have hA : f * (r + W) ^ m ≤ 2 ^ m * A / W ^ 2 := by
    calc f * (r + W) ^ m ≤ f * (2 ^ m * W ^ m * (1 + (r / W) ^ m)) :=
          mul_le_mul_of_nonneg_left hpow hf
      _ = 2 ^ m * W ^ m * (f * (1 + (r / W) ^ m)) := by ring
      _ ≤ 2 ^ m * W ^ m * (A / W ^ (m + 2)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 ^ m * A / W ^ 2 := by
          rw [pow_add]; field_simp
  have e5 : W ^ (-2 : ℝ) = (W ^ 2)⁻¹ := by
    rw [Real.rpow_neg hW.le]; norm_cast
  have e6 : (r + W) ^ (-(m : ℝ)) = ((r + W) ^ m)⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
  rw [e5, e6]
  have : 2 ^ m * A * ((W ^ 2)⁻¹ * ((r + W) ^ m)⁻¹) = 2 ^ m * A / W ^ 2 / (r + W) ^ m := by
    field_simp
  rw [this, le_div_iff₀ hrWm]
  exact hA

/-- [I, (1.8)] with `k = 0` and `k = d − 2`: `s_{xy} ≤ C B_{xy}` on `adm(c₀, c₁)`. -/
private lemma Entrywise_S_le_bB {d : ℕ} (hd : 2 ≤ d) (P : Profile d) (c₀ c₁ : ℝ)
    (hc₀ : 0 < c₀) : ∃ C : ℝ, ∀ p : SizeL, p.1 ∈ adm c₀ c₁ → 1 ≤ sizeW p →
      ∀ x y : Zd d p.1.2, Smat P.ψ p.1.1 p.1.2 x y ≤ C * bB d p.1.2 p.1.1 x y := by
  obtain ⟨C₀, h0⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨C₂, h2⟩ := subpoly_adm d P c₀ c₁ hc₀ (d - 2)
  refine ⟨2 ^ (d - 2) * (|C₀| + |C₂|), fun p hp hW x y => ?_⟩
  have hW0 : 0 < sizeW p := by linarith
  have hS : Smat P.ψ p.1.1 p.1.2 x y = fWL P.ψ p.1.1 p.1.2 (x - y) := by simp [Smat]
  rw [hS]
  have hb0 := h0 p.1.1 p.1.2 hp (x - y)
  have hb2 := h2 p.1.1 p.1.2 hp (x - y)
  set f := |fWL P.ψ p.1.1 p.1.2 (x - y)| with hf
  set r : ℝ := (zdistInf d p.1.2 (x - y) : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hWd : (0 : ℝ) < (p.1.1 : ℝ) ^ d := pow_pos hW0 d
  have hcomb : f * (1 + (r / (p.1.1 : ℝ)) ^ (d - 2)) ≤
      (|C₀| + |C₂|) / (p.1.1 : ℝ) ^ (d - 2 + 2) := by
    rw [Nat.sub_add_cancel hd]
    rw [pow_zero, one_mul] at hb0
    have : f * (1 + (r / (p.1.1 : ℝ)) ^ (d - 2)) = f + (r / (p.1.1 : ℝ)) ^ (d - 2) * f := by ring
    rw [this, add_div]
    exact add_le_add (hb0.trans (div_le_div_of_nonneg_right (le_abs_self _) hWd.le))
      (hb2.trans (div_le_div_of_nonneg_right (le_abs_self _) hWd.le))
  have h := Entrywise_decay_alg (d - 2) hW0 hr0 (abs_nonneg _) hcomb
  have hsz : sizeW p = (p.1.1 : ℝ) := rfl
  rw [hsz] at h
  have e : (2 - (d : ℝ)) = -((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd]; push_cast; ring
  have hB : bB d p.1.2 p.1.1 x y = (p.1.1 : ℝ) ^ (-2 : ℝ) * (r + p.1.1) ^ (-((d - 2 : ℕ) : ℝ)) := by
    unfold bB; rw [e]
  rw [hB]
  refine (le_abs_self _).trans (h.trans (le_of_eq ?_))
  ring

/-! ## The scale of the rounds -/

/-- `c = min(c₀ᵀ − (n − 1) ε₀, d/4 − ε₀/2)` of [II, Lemma 8.1]. -/
private def Entrywise_c (d n : ℕ) (c₀T ε₀ : ℝ) : ℝ :=
  min (c₀T - ((n : ℝ) - 1) * ε₀) ((d : ℝ) / 4 - ε₀ / 2)

/-- `Φ̃_k = W^{−d/2+ε₀−kc/2}`, so `Φ̃₀ = W^{−d/2+ε₀}` and `Φ̃_{k+1}² = W^{−c} Φ̃_k²`. -/
private def Entrywise_Phi (d n : ℕ) (c₀T ε₀ : ℝ) (k : ℕ) (p : SizeL) : ℝ :=
  (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀ - (k : ℝ) * Entrywise_c d n c₀T ε₀ / 2)

private lemma Entrywise_Phi_zero (d n : ℕ) (c₀T ε₀ : ℝ) (p : SizeL) :
    Entrywise_Phi d n c₀T ε₀ 0 p = (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀) := by
  simp [Entrywise_Phi]

private lemma Entrywise_Phi_nonneg (d n : ℕ) (c₀T ε₀ : ℝ) (k : ℕ) (p : SizeL) :
    0 ≤ Entrywise_Phi d n c₀T ε₀ k p := Real.rpow_nonneg (Nat.cast_nonneg _) _

/-! ## The base case: [II, (7.7)] gives [II, (8.1)] at `Φ̃₀` -/

/-- `T_{xy} ≤ 2 X² + 2 s_{xy}` when `‖G − m‖_max ≤ X`, `|m| ≤ 1` and `S` has row sums `1`. -/
private lemma Entrywise_T_base {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : ∀ x, ∑ y, S x y = 1) (G : Matrix ι ι ℂ) (m : ℂ)
    (hm : ‖m‖ ≤ 1) {X : ℝ} (hX : ∀ x y, ‖entryErr G m x y‖ ≤ X) (x y : ι) :
    Tvar S G m x y ≤ 2 * X ^ 2 + 2 * S x y := by
  have hG : ∀ α, ‖G α y‖ ^ 2 ≤ 2 * X ^ 2 + 2 * (if α = y then 1 else 0) := fun α => by
    have h1 : G α y = entryErr G m α y + (if α = y then m else 0) := by
      unfold entryErr; ring
    have h2 : ‖G α y‖ ≤ ‖entryErr G m α y‖ + ‖(if α = y then m else 0)‖ := by
      rw [h1]; exact norm_add_le _ _
    have h3 : ‖(if α = y then m else 0)‖ ^ 2 ≤ (if α = y then (1 : ℝ) else 0) := by
      split_ifs
      · nlinarith [norm_nonneg m]
      · simp
    have h4 : ‖entryErr G m α y‖ ^ 2 ≤ X ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hX α y) 2
    have h5 : 0 ≤ ‖(if α = y then m else 0)‖ := norm_nonneg _
    have h6 : 0 ≤ ‖G α y‖ := norm_nonneg _
    have h7 : ‖G α y‖ ^ 2 ≤ (‖entryErr G m α y‖ + ‖(if α = y then m else 0)‖) ^ 2 :=
      pow_le_pow_left₀ h6 h2 2
    nlinarith [sq_nonneg (‖entryErr G m α y‖ - ‖(if α = y then m else 0)‖)]
  unfold Tvar
  have hm2 : ‖m‖ ^ 2 ≤ 1 := by
    have := norm_nonneg m
    nlinarith
  have hsum : ∑ α, S x α * ‖G α y‖ ^ 2 ≤ 2 * X ^ 2 + 2 * S x y := by
    calc ∑ α, S x α * ‖G α y‖ ^ 2
        ≤ ∑ α, (2 * X ^ 2 * S x α + 2 * (S x α * (if α = y then 1 else 0))) := by
          refine Finset.sum_le_sum fun α _ => ?_
          have := mul_le_mul_of_nonneg_left (hG α) (hS0 x α)
          linarith
      _ = 2 * X ^ 2 + 2 * S x y := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS1 x]
          simp
  have hs0 : 0 ≤ ∑ α, S x α * ‖G α y‖ ^ 2 :=
    Finset.sum_nonneg fun α _ => mul_nonneg (hS0 x α) (sq_nonneg _)
  calc ‖m‖ ^ 2 * ∑ α, S x α * ‖G α y‖ ^ 2 ≤ 1 * (2 * X ^ 2 + 2 * S x y) :=
        mul_le_mul hm2 hsum hs0 zero_le_one
    _ = _ := one_mul _

/-- [II, (7.7)] gives [II, (8.1)] at `Φ̃₀ = W^{−d/2+ε₀}`. -/
private lemma Entrywise_base {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε c₀T ε₀ : ℝ} {n : ℕ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    {U' : SizeL → Type} (z' : ∀ p, U' p → ℂ)
    (hz' : ∀ p u, z' p u ∈ specDom κ ε p.1.1 p.1.2)
    (h77 : StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => U' p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => ‖entryErr (green (hmat ω) (z' p v.1)) (msc (z' p v.1)) v.2.1 v.2.2‖)
      (fun p _ _ => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀))) :
    StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => U' p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z' p v.1)) (msc (z' p v.1))
        v.2.1 v.2.2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2 + Entrywise_Phi d n c₀T ε₀ 0 p ^ 2) := by
  intro τ hτ D hD
  obtain ⟨C', hC'⟩ := Entrywise_S_le_bB (by omega) P c₀ c₁ hc₀
  have h7 := h77 (τ / 4) (by linarith) D hD
  have hsz := Entrywise_tendsto d n c₀ c₁ c₀T
  filter_upwards [h7, Entrywise_ev_adm d n c₀ c₁ c₀T,
    Entrywise_ev_Smat d n P c₀ c₁ c₀T hc₀ hc₁, hsz.eventually (eventually_ge_atTop 1),
    ((tendsto_rpow_atTop (show 0 < τ / 2 by linarith)).comp hsz).eventually
      (eventually_ge_atTop 2),
    ((tendsto_rpow_atTop hτ).comp hsz).eventually (eventually_ge_atTop (2 * |C'|))] with
    p hp hadm hS hW1 hWh hWt
  refine le_trans (measure_mono ?_) hp
  rintro ω ⟨⟨u, x, y⟩, hω⟩
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hcon
  change (1 : ℝ) ≤ p.1.1 at hW1
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have him : 0 < (z' p u).im := by
    refine lt_of_lt_of_le ?_ (hz' p u).2.1
    exact div_pos (by positivity)
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero p.2) _)
  have hX : ∀ a b : Zd d p.1.2, ‖entryErr (green (hmat ω) (z' p u)) (msc (z' p u)) a b‖ ≤
      (p.1.1 : ℝ) ^ (τ / 4) * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀) := fun a b => hcon (u, a, b)
  have hT := Entrywise_T_base (Smat P.ψ p.1.1 p.1.2) hS.2.1 hS.2.2 (green (hmat ω) (z' p u))
    (msc (z' p u)) (norm_msc_lt_one him).le hX x y
  have hSxy := hC' p hadm hW1 x y
  have hB0 : 0 ≤ bB d p.1.2 p.1.1 x y := by
    unfold bB; positivity
  have hΦ0 := Entrywise_Phi_zero d n c₀T ε₀ p
  have hsq : ((p.1.1 : ℝ) ^ (τ / 4) * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ^ 2 =
      (p.1.1 : ℝ) ^ (τ / 2) * ((p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    congr 2; norm_num; ring
  have hWτ : (p.1.1 : ℝ) ^ τ = (p.1.1 : ℝ) ^ (τ / 2) * (p.1.1 : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  change (2 : ℝ) ≤ (p.1.1 : ℝ) ^ (τ / 2) at hWh
  change 2 * |C'| ≤ (p.1.1 : ℝ) ^ τ at hWt
  have hΦ2 : 0 ≤ ((p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ^ 2 := sq_nonneg _
  have hCb : C' * bB d p.1.2 p.1.1 x y ≤ |C'| * bB d p.1.2 p.1.1 x y :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hB0
  have hfinal : Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z' p u)) (msc (z' p u)) x y ≤
      (p.1.1 : ℝ) ^ τ * (bB d p.1.2 p.1.1 x y + ((p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ^ 2) := by
    rw [hsq] at hT
    have e1 : 2 * (p.1.1 : ℝ) ^ (τ / 2) * ((p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ^ 2 ≤
        (p.1.1 : ℝ) ^ τ * ((p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ hΦ2
      rw [hWτ]; nlinarith
    have e2 : 2 * |C'| * bB d p.1.2 p.1.1 x y ≤ (p.1.1 : ℝ) ^ τ * bB d p.1.2 p.1.1 x y :=
      mul_le_mul_of_nonneg_right hWt hB0
    nlinarith
  rw [hΦ0] at hω
  exact absurd hω (not_lt.2 hfinal)


end RBM8D
