module

public import RBM8D.LocalLaw.Cutoff.Defs

@[expose] public section

/-!
# The improvement on the cutoff event and the pair event

The Gaussian conditional bounds of the cutoff-moment argument for the local law.

* `cutImprove : cutImproveStmt`: on `Y ≤ W^β` and `max_{ab} X_{ab} ≤ 2W^α`, the
  bound `Y ≤ W^{α/2+γ}` holds outside probability `W^{−D_m}`.
* `cutPair : cutPairStmt`: for the sample `H'_y` with row and column `y`
  resampled, `C(H) > 0` implies `Y(H'_y) ≤ W^β` and
  `|X_{ab}(H) − X_{ab}(H'_y)| ≤ W^{4β}(B_{ay}^{1/2} + B_{by}^{1/2})` outside probability `W^{−D_m}`.

Both proofs are deterministic on the event where the large deviation bounds of [I, Lemma 5.1]
hold with factor `t = W^{c}` (rows, columns, quadratic forms and diagonal entries), followed by a
union bound over the tails of these bounds. The deterministic part uses the Schur complement bounds
behind [I, (5.2)–(5.3)] (`offDiagDet`, `offDiagColDet`, `diagDet`), the stability of `1 − m² S`
([I, (B.19)], `stable_Smat_strip`), the profile bounds `s ≤ C B` and `S B ≤ C B` ([I, (1.8)]),
and the product bound `B_{ky} B_{yl} ≤ 2^{d−2} B_{kl}(B_{ky} + B_{yl})`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Complex

namespace RBM8D

/-! ## The profile: `s ≤ C B`, `S B ≤ C B` and the product bound on `B` -/

section Profile

private theorem Resample_sum_val_le (L : ℕ) [NeZero L] (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ t : ZMod L, f t.val ≤ ∑ k ∈ Finset.range L, f k := by
  rw [← Finset.sum_image (f := f) (g := ZMod.val) fun a _ b _ h => ZMod.val_injective L h]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hf k
  intro k hk
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hk
  exact Finset.mem_range.2 (ZMod.val_lt t)

private theorem Resample_sum_zdist_le (L : ℕ) [NeZero L] (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hg : Antitone g) : ∑ t : ZMod L, g (zdist L t) ≤ 2 * ∑ n ∈ Finset.range L, g n := by
  have hpt : ∀ t : ZMod L, g (zdist L t) ≤ g t.val + g (L - t.val) := by
    intro t
    unfold zdist
    rcases le_total t.val (L - t.val) with h | h
    · rw [min_eq_left h]; linarith [hg0 (L - t.val)]
    · rw [min_eq_right h]; linarith [hg0 t.val]
  have h1 := Resample_sum_val_le L g hg0
  have h2 : ∑ t : ZMod L, g (L - t.val) ≤ ∑ n ∈ Finset.range L, g n := by
    refine (Resample_sum_val_le L (fun k => g (L - k)) fun k => hg0 _).trans ?_
    rw [← Finset.sum_range_reflect (fun k => g (L - k)) L]
    refine Finset.sum_le_sum fun k hk => ?_
    have := Finset.mem_range.1 hk
    exact hg (by omega)
  calc ∑ t : ZMod L, g (zdist L t) ≤ ∑ t : ZMod L, (g t.val + g (L - t.val)) :=
        Finset.sum_le_sum fun t _ => hpt t
    _ = ∑ t : ZMod L, g t.val + ∑ t : ZMod L, g (L - t.val) := Finset.sum_add_distrib
    _ ≤ _ := by linarith

private theorem Resample_sum_inv_sq_le (W : ℝ) (hW : 1 ≤ W) (N : ℕ) :
    ∑ n ∈ Finset.range N, (((n : ℝ) + W) ^ 2)⁻¹ ≤ 2 / W - 2 / ((N : ℝ) + W) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h0 : 0 < (N : ℝ) + W := by positivity
    have h1 : 0 < (N : ℝ) + 1 + W := by positivity
    have key : (((N : ℝ) + W) ^ 2)⁻¹ ≤ 2 / ((N : ℝ) + W) - 2 / ((N : ℝ) + 1 + W) := by
      have e : 2 / ((N : ℝ) + W) - 2 / ((N : ℝ) + 1 + W) =
          2 / (((N : ℝ) + W) * ((N : ℝ) + 1 + W)) := by
        field_simp
        ring
      rw [e, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

/-- `Σ_{t ∈ Z_L} (‖t‖_L + W)^{−2} ≤ 4/W`. -/
private theorem Resample_sum_zdist_inv_sq (L : ℕ) [NeZero L] (W : ℝ) (hW : 1 ≤ W) :
    ∑ t : ZMod L, (((zdist L t : ℝ) + W) ^ 2)⁻¹ ≤ 4 / W := by
  have hW0 : 0 < W := by linarith
  refine (Resample_sum_zdist_le L (fun n => (((n : ℝ) + W) ^ 2)⁻¹) (fun n => by positivity)
    fun a b hab => ?_).trans ?_
  · have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only
    gcongr
  · have := Resample_sum_inv_sq_le W hW L
    have : 0 ≤ 2 / ((L : ℝ) + W) := by positivity
    have : 4 / W = 2 * (2 / W) := by ring
    linarith

/-- `(1 + t)^M ≤ 2^M (1 + t^M)` for `t ≥ 0`. -/
private theorem Resample_one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (M : ℕ) :
    (1 + t) ^ M ≤ 2 ^ M * (1 + t ^ M) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ ≤ 2 ^ M * (1 + t ^ M) := by
          have : 0 ≤ t ^ M := pow_nonneg ht M
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) M]
  · calc (1 + t) ^ M ≤ (2 * t) ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ = 2 ^ M * t ^ M := mul_pow _ _ _
      _ ≤ 2 ^ M * (1 + t ^ M) := by
          have := pow_pos (by norm_num : (0 : ℝ) < 2) M
          nlinarith

/-- `B_{xy} (1 + ‖x − y‖_L/W)^{d−2} W^d = 1` for `d ≥ 2`, `W > 0`. -/
private theorem Resample_bB_mul {d L W : ℕ} (hd : 2 ≤ d) (hW : (0 : ℝ) < W) (x y : Zd d L) :
    bB d L W x y * ((1 + (zdistInf d L (x - y) : ℝ) / W) ^ (d - 2) * (W : ℝ) ^ d) = 1 := by
  set r : ℝ := (zdistInf d L (x - y) : ℝ)
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hrW : 0 < r + W := by linarith
  have e1 : (r + W) ^ ((2 : ℝ) - d) = ((r + W) ^ (d - 2))⁻¹ := by
    rw [show (2 : ℝ) - d = -((d - 2 : ℕ) : ℝ) by rw [Nat.cast_sub hd]; push_cast; ring,
      Real.rpow_neg hrW.le, Real.rpow_natCast]
  have e2 : (W : ℝ) ^ (-2 : ℝ) = ((W : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hW.le]; norm_cast
  have e3 : (1 + r / W) ^ (d - 2) * (W : ℝ) ^ d = (r + W) ^ (d - 2) * (W : ℝ) ^ 2 := by
    have : (1 + r / W) = (r + W) / W := by field_simp; ring
    rw [this, div_pow]
    obtain ⟨k, hk⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    have hk' : d - 2 = k := by omega
    rw [hk', hk, pow_add]
    field_simp
  unfold bB
  rw [e1, e2, e3]
  have : (0 : ℝ) < (r + W) ^ (d - 2) := pow_pos hrW _
  field_simp

/-- `0 < B_{xy}` for `W ≥ 1`. -/
private theorem Resample_bB_pos {d L W : ℕ} (hW : 1 ≤ W) (x y : Zd d L) : 0 < bB d L W x y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold bB
  have : (0 : ℝ) < (zdistInf d L (x - y) : ℝ) + W := by positivity
  positivity

/-- `B_{xy} = B_{yx}`. -/
private theorem Resample_bB_symm {d L W : ℕ} [NeZero L] (x y : Zd d L) :
    bB d L W x y = bB d L W y x := by
  unfold bB
  rw [← zdistInf_neg d L (x - y), neg_sub]

/-- The product bound on `B`: `B_{ky} B_{yl} ≤ 2^{d−2} B_{kl} (B_{ky} + B_{yl})`. -/
private theorem Resample_bB_prod {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (k y l : Zd d L) :
    bB d L W k y * bB d L W y l ≤ 2 ^ (d - 2) * bB d L W k l * (bB d L W k y + bB d L W y l) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set n := d - 2
  set u₁ : ℝ := 1 + (zdistInf d L (k - y) : ℝ) / W with hu₁
  set u₂ : ℝ := 1 + (zdistInf d L (y - l) : ℝ) / W with hu₂
  set u : ℝ := 1 + (zdistInf d L (k - l) : ℝ) / W with hu
  have h₁ := Resample_bB_mul hd hW0 k y
  have h₂ := Resample_bB_mul hd hW0 y l
  have h₃ := Resample_bB_mul hd hW0 k l
  rw [← hu₁] at h₁
  rw [← hu₂] at h₂
  rw [← hu] at h₃
  have hu₁1 : 1 ≤ u₁ := by rw [hu₁]; have : 0 ≤ (zdistInf d L (k - y) : ℝ) / W := by positivity
                           linarith
  have hu₂1 : 1 ≤ u₂ := by rw [hu₂]; have : 0 ≤ (zdistInf d L (y - l) : ℝ) / W := by positivity
                           linarith
  have htri : u ≤ 2 * max u₁ u₂ := by
    have h := zdistInf_add_le d L (k - y) (y - l)
    rw [sub_add_sub_cancel] at h
    have h' : (zdistInf d L (k - l) : ℝ) ≤ zdistInf d L (k - y) + zdistInf d L (y - l) := by
      exact_mod_cast h
    have : (zdistInf d L (k - l) : ℝ) / W ≤ (zdistInf d L (k - y) : ℝ) / W +
        (zdistInf d L (y - l) : ℝ) / W := by
      rw [← add_div]; exact div_le_div_of_nonneg_right h' hW0.le
    rw [hu]
    have := le_max_left u₁ u₂
    have := le_max_right u₁ u₂
    linarith
  have hu0 : 0 < u := by rw [hu]; positivity
  have hpow : u ^ n ≤ 2 ^ n * (u₁ ^ n + u₂ ^ n) := by
    calc u ^ n ≤ (2 * max u₁ u₂) ^ n := pow_le_pow_left₀ hu0.le htri n
      _ = 2 ^ n * (max u₁ u₂) ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (u₁ ^ n + u₂ ^ n) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases le_total u₁ u₂ with h | h
          · rw [max_eq_right h]; have := pow_nonneg (by linarith : (0 : ℝ) ≤ u₁) n; linarith
          · rw [max_eq_left h]; have := pow_nonneg (by linarith : (0 : ℝ) ≤ u₂) n; linarith
  -- write each `B` as `1 / (u^n W^d)`
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hW0 d
  have p₁ : 0 < u₁ ^ n := pow_pos (by linarith) n
  have p₂ : 0 < u₂ ^ n := pow_pos (by linarith) n
  have p₃ : 0 < u ^ n := pow_pos hu0 n
  have e₁ : bB d L W k y = 1 / (u₁ ^ n * (W : ℝ) ^ d) := by
    rw [eq_div_iff (by positivity)]; exact h₁
  have e₂ : bB d L W y l = 1 / (u₂ ^ n * (W : ℝ) ^ d) := by
    rw [eq_div_iff (by positivity)]; exact h₂
  have e₃ : bB d L W k l = 1 / (u ^ n * (W : ℝ) ^ d) := by
    rw [eq_div_iff (by positivity)]; exact h₃
  rw [e₁, e₂, e₃, ← sub_nonneg]
  have e : 2 ^ n * (1 / (u ^ n * (W : ℝ) ^ d)) *
        (1 / (u₁ ^ n * (W : ℝ) ^ d) + 1 / (u₂ ^ n * (W : ℝ) ^ d)) -
        1 / (u₁ ^ n * (W : ℝ) ^ d) * (1 / (u₂ ^ n * (W : ℝ) ^ d)) =
      (2 ^ n * (u₁ ^ n + u₂ ^ n) - u ^ n) /
        (u ^ n * u₁ ^ n * u₂ ^ n * (W : ℝ) ^ d * (W : ℝ) ^ d) := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (by linarith) (by positivity)

/-- The profile bounds of [I, (1.8)]: on `adm(c₀, c₁)` with `W ≥ 1`, `s_{xy} ≤ C B_{xy}` and
`Σ_α |s_{xα}| B_{αy} ≤ C B_{xy}`. -/
private theorem Resample_profile {d : ℕ} (hd : 2 ≤ d) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → 1 ≤ W →
      (∀ x y : Zd d L, Smat P.ψ W L x y ≤ C * bB d L W x y) ∧
      ∀ x y : Zd d L, ∑ α, |Smat P.ψ W L x α| * bB d L W α y ≤ C * bB d L W x y := by
  obtain ⟨C₀, h0⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨CM, hM⟩ := subpoly_adm d P c₀ c₁ hc₀ (3 * d)
  set K : ℝ := 2 ^ (3 * d) * (|C₀| + |CM|) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * 4 ^ d, by positivity, fun W L _ hp hW1' => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  set g : ZMod L → ℝ := fun v => ((1 + (zdist L v : ℝ) / W) ^ 2)⁻¹ with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => by rw [hg]; positivity
  have hg1' : ∀ v, g v ≤ 1 := fun v => by
    rw [hg]
    refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
    have : 0 ≤ (zdist L v : ℝ) / W := by positivity
    linarith
  -- the pointwise bound
  have hpt : ∀ u : Zd d L, |fWL P.ψ W L u| *
      (1 + (zdistInf d L u : ℝ) / W) ^ (d - 2) ≤ K / (W : ℝ) ^ d * ∏ i, g (u i) := by
    intro u
    set t : ℝ := (zdistInf d L u : ℝ) / W with ht
    have ht0 : 0 ≤ t := by positivity
    have hti : ∀ i, 0 < (1 + (zdist L (u i) : ℝ) / W) ^ 2 := fun i => by positivity
    have hprod : ∏ i, (1 + (zdist L (u i) : ℝ) / W) ^ 2 ≤ (1 + t) ^ (2 * d) := by
      calc ∏ i, (1 + (zdist L (u i) : ℝ) / W) ^ 2 ≤ ∏ _i : Fin d, (1 + t) ^ 2 := by
            refine Finset.prod_le_prod₀ (fun i _ => (hti i).le) fun i _ => ?_
            have : (zdist L (u i) : ℝ) ≤ zdistInf d L u := by
              exact_mod_cast zdist_le_zdistInf d L u i
            have : (zdist L (u i) : ℝ) / W ≤ t := div_le_div_of_nonneg_right this hW0.le
            gcongr
        _ = (1 + t) ^ (2 * d) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    have hP0 : 0 < ∏ i, (1 + (zdist L (u i) : ℝ) / W) ^ 2 :=
      Finset.prod_pos fun i _ => hti i
    have hgprod : ∏ i, g (u i) = (∏ i, (1 + (zdist L (u i) : ℝ) / W) ^ 2)⁻¹ := by
      simp only [hg]
      exact Finset.prod_inv_distrib _
    rw [hgprod, ← div_eq_mul_inv, le_div_iff₀ hP0]
    have hf0 := h0 W L hp u
    have hfM := hM W L hp u
    rw [pow_zero, one_mul] at hf0
    have hfa : 0 ≤ |fWL P.ψ W L u| := abs_nonneg _
    have h1t : 1 ≤ 1 + t := by linarith
    calc |fWL P.ψ W L u| * (1 + t) ^ (d - 2) * ∏ i, (1 + (zdist L (u i) : ℝ) / W) ^ 2
        ≤ |fWL P.ψ W L u| * (1 + t) ^ (d - 2) * (1 + t) ^ (2 * d) := by gcongr
      _ = |fWL P.ψ W L u| * (1 + t) ^ (d - 2 + 2 * d) := by rw [mul_assoc, ← pow_add]
      _ ≤ |fWL P.ψ W L u| * (1 + t) ^ (3 * d) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1t (by omega)) hfa
      _ ≤ |fWL P.ψ W L u| * (2 ^ (3 * d) * (1 + t ^ (3 * d))) :=
          mul_le_mul_of_nonneg_left (Resample_one_add_pow_le ht0 _) hfa
      _ = 2 ^ (3 * d) * (|fWL P.ψ W L u| + t ^ (3 * d) * |fWL P.ψ W L u|) := by ring
      _ ≤ 2 ^ (3 * d) * (C₀ / (W : ℝ) ^ d + CM / (W : ℝ) ^ d) := by gcongr
      _ ≤ K / (W : ℝ) ^ d := by
          rw [hK, mul_div_assoc, ← add_div]
          gcongr
          · exact le_abs_self _
          · exact le_abs_self _
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hW0 d
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · -- `s_{xy} ≤ K B_{xy} ≤ K 4^d B_{xy}`
    have hS : Smat P.ψ W L x y = fWL P.ψ W L (x - y) := by simp [Smat]
    have hB := Resample_bB_mul hd hW0 x y
    have hprod1 : ∏ i, g ((x - y) i) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => hg0 _) fun i _ => hg1' _
    have h1 := (hpt (x - y)).trans
      (mul_le_of_le_one_right (div_nonneg hK0 hWd.le) hprod1)
    set u := (1 + (zdistInf d L (x - y) : ℝ) / W) ^ (d - 2)
    have hu : 0 < u := pow_pos (by positivity) _
    have hB0 := Resample_bB_pos hW1' x y
    have h2 : |fWL P.ψ W L (x - y)| ≤ K * bB d L W x y := by
      have e : bB d L W x y = 1 / (u * (W : ℝ) ^ d) := by
        rw [eq_div_iff (by positivity)]; exact hB
      rw [e]
      rw [le_div_iff₀ hWd] at h1
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h4 : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
    rw [hS]
    calc fWL P.ψ W L (x - y) ≤ |fWL P.ψ W L (x - y)| := le_abs_self _
      _ ≤ K * bB d L W x y := h2
      _ ≤ K * 4 ^ d * bB d L W x y := by
          have := mul_le_mul_of_nonneg_left h4 (mul_nonneg hK0 hB0.le)
          nlinarith
  · -- the convolution
    have hg1 : ∑ v : ZMod L, g v ≤ 4 * W := by
      have h := Resample_sum_zdist_inv_sq L W hW1
      have e : ∀ v : ZMod L, g v = W ^ 2 * (((zdist L v : ℝ) + W) ^ 2)⁻¹ := by
        intro v
        rw [hg]
        simp only
        have : (0 : ℝ) < (zdist L v : ℝ) + W := by positivity
        field_simp
        ring
      rw [Finset.sum_congr rfl fun v _ => e v, ← Finset.mul_sum]
      calc (W : ℝ) ^ 2 * ∑ v : ZMod L, (((zdist L v : ℝ) + W) ^ 2)⁻¹ ≤ W ^ 2 * (4 / W) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 4 * W := by field_simp
    have hsumg : ∑ u : Zd d L, ∏ i, g (u i) ≤ (4 * W) ^ d := by
      rw [← Fintype.prod_sum (fun (_ : Fin d) (v : ZMod L) => g v)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun v _ => hg0 v) hg1 d
    have hB0 : 0 ≤ bB d L W x y := (Resample_bB_pos hW1' x y).le
    have hshift : ∀ α, bB d L W α y ≤
        bB d L W x y * (1 + (zdistInf d L (x - α) : ℝ) / W) ^ (d - 2) := by
      intro α
      have hBa := Resample_bB_mul hd hW0 α y
      have hBx := Resample_bB_mul hd hW0 x y
      set r₁ : ℝ := (zdistInf d L (x - α) : ℝ)
      set r₂ : ℝ := (zdistInf d L (α - y) : ℝ)
      set r : ℝ := (zdistInf d L (x - y) : ℝ)
      have htri : r ≤ r₁ + r₂ := by
        have h := zdistInf_add_le d L (x - α) (α - y)
        rw [sub_add_sub_cancel] at h
        have h' : (zdistInf d L (x - y) : ℝ) ≤ zdistInf d L (x - α) + zdistInf d L (α - y) := by
          exact_mod_cast h
        exact h'
      have hr₁ : 0 ≤ r₁ := Nat.cast_nonneg _
      have hr₂ : 0 ≤ r₂ := Nat.cast_nonneg _
      have hmono : 1 + r / W ≤ (1 + r₂ / W) * (1 + r₁ / W) := by
        have : r / W ≤ r₁ / W + r₂ / W := by
          rw [← add_div]; exact div_le_div_of_nonneg_right htri hW0.le
        have : 0 ≤ r₁ / W * (r₂ / W) := by positivity
        nlinarith
      have hpw : (1 + r / W) ^ (d - 2) ≤ (1 + r₂ / W) ^ (d - 2) * (1 + r₁ / W) ^ (d - 2) := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hmono _
      have p₁ : 0 < (1 + r₂ / W) ^ (d - 2) := pow_pos (by positivity) _
      have p₂ : 0 < (1 + r / W) ^ (d - 2) := pow_pos (by positivity) _
      have e₁ : bB d L W α y = 1 / ((1 + r₂ / W) ^ (d - 2) * (W : ℝ) ^ d) := by
        rw [eq_div_iff (by positivity)]; exact hBa
      have e₂ : bB d L W x y = 1 / ((1 + r / W) ^ (d - 2) * (W : ℝ) ^ d) := by
        rw [eq_div_iff (by positivity)]; exact hBx
      rw [e₁, e₂, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right hpw hWd.le
      nlinarith
    calc ∑ α, |Smat P.ψ W L x α| * bB d L W α y
        ≤ ∑ α, |fWL P.ψ W L (x - α)| *
            (bB d L W x y * (1 + (zdistInf d L (x - α) : ℝ) / W) ^ (d - 2)) := by
          refine Finset.sum_le_sum fun α _ => ?_
          have hS : Smat P.ψ W L x α = fWL P.ψ W L (x - α) := by simp [Smat]
          rw [hS]
          exact mul_le_mul_of_nonneg_left (hshift α) (abs_nonneg _)
      _ = bB d L W x y * ∑ α, |fWL P.ψ W L (x - α)| *
            (1 + (zdistInf d L (x - α) : ℝ) / W) ^ (d - 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun α _ => by ring
      _ ≤ bB d L W x y * ∑ α : Zd d L, K / (W : ℝ) ^ d * ∏ i, g ((x - α) i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => hpt (x - α)) hB0
      _ = bB d L W x y * (K / (W : ℝ) ^ d * ∑ u : Zd d L, ∏ i, g (u i)) := by
          rw [← Finset.mul_sum]
          congr 2
          exact (Equiv.subLeft x).sum_comp (fun u => ∏ i, g (u i))
      _ ≤ bB d L W x y * (K / (W : ℝ) ^ d * (4 * W) ^ d) := by gcongr
      _ = K * 4 ^ d * bB d L W x y := by
          rw [mul_pow]
          field_simp

end Profile

/-! ## The deterministic part of the improvement on the cutoff event -/

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The large deviation bounds of [I, Lemma 5.1] with factor `t`: rows, columns, quadratic forms
and diagonal entries. -/
private def Resample_LDE (H G : Matrix ι ι ℂ) (S : Matrix ι ι ℝ) (t : ℝ) : Prop :=
  LDERow H G S t ∧ LDECol H G S t ∧ LDEQuad H G S t ∧ ∀ i, ‖H i i‖ ^ 2 ≤ t * S i i

omit [Fintype ι] in
/-- `|G_{ii}|² ≤ 4` on `‖G − m‖_max ≤ δ ≤ |m| ≤ 1`. -/
private theorem Resample_diag_sq {G : Matrix ι ι ℂ} {m : ℂ} {δ : ℝ} (hG : GoodEvent G m δ)
    (hδm : δ ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (i : ι) : ‖G i i‖ ^ 2 ≤ 4 := by
  have h1 : ‖G i i - m‖ ≤ δ := by simpa [entryErr] using hG i i
  have h3 : ‖G i i‖ ≤ ‖m‖ + ‖G i i - m‖ := by
    calc ‖G i i‖ = ‖m + (G i i - m)‖ := by rw [add_sub_cancel]
      _ ≤ ‖m‖ + ‖G i i - m‖ := norm_add_le _ _
  have h2 : ‖G i i‖ ≤ 2 := by linarith
  nlinarith [norm_nonneg (G i i)]

/-- The Schur column bound: `P_{ab} = Σ_i s_{ai} |G_{ib}|² ≤ (4 C_s + 16 t A) B_{ab}` from the
column large deviation bound, `s ≤ C_s B` and `D^s_{ab} ≤ A B_{ab}`. -/
private theorem Resample_P_le (H : Matrix ι ι ℂ) (z m : ℂ) (S : Matrix ι ι ℝ) (B : ι → ι → ℝ)
    (Cs t A δ : ℝ) (hH : H.IsHermitian) (hz : 0 < z.im) (hm1 : ‖m‖ ≤ 1)
    (hG : GoodEvent (green H z) m δ) (hδm : δ ≤ ‖m‖) (h4 : 4 * t * δ ^ 2 ≤ 1)
    (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k ≤ 1) (hSs : ∀ i k, S i k = S k i)
    (ht : 0 ≤ t) (hC : LDECol H (green H z) S t) (hSB : ∀ i j, S i j ≤ Cs * B i j)
    (hD : ∀ a b, ∑ i, ∑ j, S a i * ‖green H z i j‖ ^ 2 * S j b ≤ A * B a b) (a b : ι) :
    ∑ i, S a i * ‖green H z i b‖ ^ 2 ≤ (4 * Cs + 16 * t * A) * B a b := by
  set G := green H z with hGdef
  have hpt : ∀ i, S a i * ‖G i b‖ ^ 2 ≤ (if i = b then 4 * S a b else 0) +
      16 * t * ∑ α, S a i * ‖G i α‖ ^ 2 * S α b := by
    intro i
    have hnn : 0 ≤ 16 * t * ∑ α, S a i * ‖G i α‖ ^ 2 * S α b :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun α _ =>
        mul_nonneg (mul_nonneg (hS0 a i) (by positivity)) (hS0 α b))
    by_cases hib : i = b
    · subst hib
      rw [ite_eq_left rfl]
      have := Resample_diag_sq hG hδm hm1 i
      nlinarith [hS0 a i]
    · rw [ite_eq_right hib, zero_add]
      have h := offDiagColDet H z m S δ t hH hz hG hδm hS0 hS1 ht h4 hC b i (Ne.symm hib)
      unfold TvarCol at h
      have hm2 : ‖m‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg m]
      have hsum0 : 0 ≤ ∑ α, S b α * ‖G i α‖ ^ 2 :=
        Finset.sum_nonneg fun α _ => mul_nonneg (hS0 b α) (by positivity)
      have h' : ‖G i b‖ ^ 2 ≤ 16 * t * ∑ α, S b α * ‖G i α‖ ^ 2 := by
        refine h.trans ?_
        have := mul_le_mul_of_nonneg_right hm2 hsum0
        nlinarith
      have e : ∑ α, S a i * ‖G i α‖ ^ 2 * S α b = S a i * ∑ α, S b α * ‖G i α‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hSs α b]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left h' (hS0 a i)
      nlinarith
  calc ∑ i, S a i * ‖G i b‖ ^ 2
      ≤ ∑ i, ((if i = b then 4 * S a b else 0) + 16 * t * ∑ α, S a i * ‖G i α‖ ^ 2 * S α b) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = 4 * S a b + 16 * t * ∑ i, ∑ α, S a i * ‖G i α‖ ^ 2 * S α b := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _),
          ← Finset.mul_sum]
    _ ≤ 4 * (Cs * B a b) + 16 * t * (A * B a b) := by
        gcongr
        · exact hSB a b
        · exact hD a b
    _ = (4 * Cs + 16 * t * A) * B a b := by ring

/-- **The deterministic part of the improvement on the cutoff event.** On `‖G − m‖_max ≤ δ` with the side conditions
`δ ≤ |m|/2`, `δ ≤ 1`, `4tδ² ≤ 1`, `Kδ ≤ 1/2`, the large deviation bounds with factor `t ≥ 1`,
`s ≤ C_s B`, `B ≤ w = B_{ii}`, the stability of `1 − m² S` with constant `K`, and
`D^s_{ab} ≤ A B_{ab}`: `|G_{ij} − m δ_{ij}|² ≤ (16 + 10⁴ K²) t² (4 C_s + 16 t A) B_{ij}`. -/
private theorem Resample_core (H : Matrix ι ι ℂ) (z m : ℂ) (S : Matrix ι ι ℝ) (B : ι → ι → ℝ)
    (w Cs K t A δ : ℝ) (hH : H.IsHermitian) (hz : 0 < z.im) (hm : m * (m + z) = -1)
    (hm4 : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hG : GoodEvent (green H z) m δ) (hδm : δ ≤ ‖m‖ / 2)
    (hδ1 : δ ≤ 1) (h4 : 4 * t * δ ^ 2 ≤ 1) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ i, ∑ k, S i k = 1) (hS2 : ∀ k, ∑ i, S i k ≤ 1) (hSs : ∀ i k, S i k = S k i)
    (ht : 1 ≤ t) (hL : Resample_LDE H (green H z) S t) (hB0 : ∀ i j, 0 ≤ B i j)
    (hBw : ∀ i j, B i j ≤ w) (hBd : ∀ i, B i i = w) (hSB : ∀ i j, S i j ≤ Cs * B i j)
    (hCs : 0 ≤ Cs) (hstab : Stable S (m ^ 2) K) (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 2) (hA : 0 ≤ A)
    (hD : ∀ a b, ∑ i, ∑ j, S a i * ‖green H z i j‖ ^ 2 * S j b ≤ A * B a b) (i j : ι) :
    ‖entryErr (green H z) m i j‖ ^ 2 ≤
      (16 + 10 ^ 4 * K ^ 2) * t ^ 2 * (4 * Cs + 16 * t * A) * B i j := by
  obtain ⟨hR, hC, hQ, hdg⟩ := hL
  set G := green H z with hGdef
  set Λ₀ := 4 * Cs + 16 * t * A with hΛ₀
  have hΛ0 : 0 ≤ Λ₀ := by positivity
  have hδm' : δ ≤ ‖m‖ := by linarith [norm_nonneg m]
  have hS1' : ∀ i, ∑ k, S i k ≤ 1 := fun i => (hS1 i).le
  have ht0 : 0 ≤ t := by linarith
  have hP := Resample_P_le H z m S B Cs t A δ hH hz hm1 hG hδm' h4 hS0 hS1' hSs ht0 hC hSB hD
  have hw0 : 0 ≤ w := (hB0 i i).trans (hBw i i)
  have hK2 : 0 ≤ 10 ^ 4 * K ^ 2 := by positivity
  by_cases hij : i = j
  · subst hij
    have hdiag := diagDet H z m S δ t (Λ₀ * w) K hH hz hm hm4 hm1 hG hδm hδ1 hS0 hS1 hS2 ht hQ
      hdg (fun a b => (hP a b).trans (mul_le_mul_of_nonneg_left (hBw a b) hΛ0))
      (fun a b => (hSB a b).trans (by
        have := mul_le_mul_of_nonneg_left (hBw a b) hCs
        have : Cs * w ≤ Λ₀ * w := mul_le_mul_of_nonneg_right (by
          have : 0 ≤ 16 * t * A := by positivity
          linarith) hw0
        linarith)) hstab hK hKδ i
    have he : entryErr G m i i = G i i - m := by simp [entryErr]
    rw [he, hBd i]
    have h0 : 0 ≤ 100 * K * t * Real.sqrt (Λ₀ * w) := by positivity
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hdiag 2
    have hs : Real.sqrt (Λ₀ * w) ^ 2 = Λ₀ * w := Real.sq_sqrt (by positivity)
    calc ‖G i i - m‖ ^ 2 ≤ (100 * K * t * Real.sqrt (Λ₀ * w)) ^ 2 := hsq
      _ = 10 ^ 4 * K ^ 2 * t ^ 2 * (Λ₀ * w) := by rw [mul_pow, hs]; ring
      _ ≤ (16 + 10 ^ 4 * K ^ 2) * t ^ 2 * Λ₀ * w := by
          have : 0 ≤ 16 * t ^ 2 * Λ₀ * w := by positivity
          nlinarith
  · have he : entryErr G m i j = G i j := by simp [entryErr, hij]
    rw [he]
    have h := offDiagDet H z m S δ t hH hz hG hδm' hS0 hS1' ht0 h4 hR i j hij
    unfold Tvar at h
    have hm2 : ‖m‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg m]
    have hP' := hP i j
    have hsum0 : 0 ≤ ∑ α, S i α * ‖G α j‖ ^ 2 :=
      Finset.sum_nonneg fun α _ => mul_nonneg (hS0 i α) (by positivity)
    have hBij := hB0 i j
    calc ‖G i j‖ ^ 2 ≤ 16 * t * (‖m‖ ^ 2 * ∑ α, S i α * ‖G α j‖ ^ 2) := h
      _ ≤ 16 * t * (1 * (Λ₀ * B i j)) := by
          gcongr
      _ ≤ (16 + 10 ^ 4 * K ^ 2) * t ^ 2 * Λ₀ * B i j := by
          have h1 : t ≤ t ^ 2 := by nlinarith
          have h2 : 0 ≤ Λ₀ * B i j := by positivity
          have h3 : 16 * t * (Λ₀ * B i j) ≤ 16 * t ^ 2 * (Λ₀ * B i j) := by
            have := mul_le_mul_of_nonneg_right h1 h2
            nlinarith
          have h5 : 0 ≤ 10 ^ 4 * K ^ 2 * t ^ 2 * (Λ₀ * B i j) := by positivity
          nlinarith

end Core

/-! ## The deterministic part of the pair event -/

section Pair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `‖x‖² ≤ 2‖e‖² + 2a²` from `‖x − e‖ ≤ a`. -/
private theorem Resample_sq_le {x e : ℂ} {a : ℝ} (h : ‖x - e‖ ≤ a) :
    ‖x‖ ^ 2 ≤ 2 * ‖e‖ ^ 2 + 2 * a ^ 2 := by
  have h1 : ‖x‖ ≤ ‖e‖ + ‖x - e‖ := by
    calc ‖x‖ = ‖e + (x - e)‖ := by rw [add_sub_cancel]
      _ ≤ ‖e‖ + ‖x - e‖ := norm_add_le _ _
  have h0 := norm_nonneg (x - e)
  nlinarith [norm_nonneg x, norm_nonneg e, sq_nonneg (‖e‖ - ‖x - e‖)]

/-- `‖x‖ ≤ (C + 1) u` from `‖x‖² ≤ C u²`, `C, u ≥ 0`. -/
private theorem Resample_le_of_sq {x : ℂ} {C u : ℝ} (hC : 0 ≤ C) (hu : 0 ≤ u)
    (h : ‖x‖ ^ 2 ≤ C * u ^ 2) : ‖x‖ ≤ (C + 1) * u := by
  have h2 : ‖x‖ ^ 2 ≤ ((C + 1) * u) ^ 2 := by
    refine h.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg u)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

omit [Fintype ι] in
/-- `‖δ_{kl} m‖² ≤ δ_{kl}` for `|m| ≤ 1`. -/
private theorem Resample_norm_ite_sq {m : ℂ} (hm1 : ‖m‖ ≤ 1) (k l : ι) :
    ‖(if k = l then m else 0)‖ ^ 2 ≤ (if k = l then 1 else 0) := by
  split_ifs
  · nlinarith [norm_nonneg m]
  · simp

/-- A sum over `k ≠ y` of a termwise bounded quantity is at most the full sum of the bound. -/
private theorem Resample_sum_ne_le (y : ι) (f g : ι → ℝ) (hfg : ∀ k, k ≠ y → f k ≤ g k)
    (hg : ∀ k, 0 ≤ g k) : ∑ k : {a : ι // a ≠ y}, f k.1 ≤ ∑ k, g k := by
  calc ∑ k : {a : ι // a ≠ y}, f k.1 ≤ ∑ k : {a : ι // a ≠ y}, g k.1 :=
        Finset.sum_le_sum fun k _ => hfg k.1 k.2
    _ = (∑ k, g k) - g y := sum_subtype_ne y g
    _ ≤ ∑ k, g k := by linarith [hg y]

/-- The right-hand sides of the large deviation bounds at row `y` for a matrix `M` (the minor
`G^{(y)}`) with `|M_{kl} − m δ_{kl}| ≤ Y₁ B_{kl}^{1/2}` for `k, l ≠ y`: the row and column sums are
`≤ 2(C_s + C_c) Y₁² B_{yj}`, the quadratic form `≤ 2(C_s + C_c²) Y₁² r²`, and
`|Σ_{k≠y} s_{yk} M_{kk} − m| ≤ (1 + C_s) Y₁ r`, where `B ≤ r² = B_{ii}`. -/
private theorem Resample_rhs (S : Matrix ι ι ℝ) (B : ι → ι → ℝ) (M : ι → ι → ℂ) (m : ℂ) (y : ι)
    (Y₁ r Cs Cc : ℝ) (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k = 1)
    (hSs : ∀ i k, S i k = S k i) (hB0 : ∀ i j, 0 ≤ B i j) (hBs : ∀ i j, B i j = B j i)
    (hBw : ∀ i j, B i j ≤ r ^ 2) (hBd : ∀ i, B i i = r ^ 2) (hSB : ∀ i j, S i j ≤ Cs * B i j)
    (hconv : ∀ x z, ∑ α, S x α * B α z ≤ Cc * B x z) (hCs : 0 ≤ Cs) (hCc : 0 ≤ Cc)
    (hm1 : ‖m‖ ≤ 1) (hY₁ : 1 ≤ Y₁) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hM : ∀ k l, k ≠ y → l ≠ y → ‖M k l - (if k = l then m else 0)‖ ≤ Y₁ * Real.sqrt (B k l)) :
    (∀ j, j ≠ y → ∑ k : {a : ι // a ≠ y}, S y k.1 * ‖M k.1 j‖ ^ 2 ≤
        2 * (Cs + Cc) * Y₁ ^ 2 * B y j) ∧
    (∀ j, j ≠ y → ∑ k : {a : ι // a ≠ y}, S y k.1 * ‖M j k.1‖ ^ 2 ≤
        2 * (Cs + Cc) * Y₁ ^ 2 * B y j) ∧
    (∑ k : {a : ι // a ≠ y}, ∑ l : {a : ι // a ≠ y}, S y k.1 * ‖M k.1 l.1‖ ^ 2 * S l.1 y ≤
        2 * (Cs + Cc ^ 2) * Y₁ ^ 2 * r ^ 2) ∧
    ‖∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) * M k.1 k.1 - m‖ ≤ (1 + Cs) * Y₁ * r := by
  have hsq : ∀ k l, k ≠ y → l ≠ y →
      ‖M k l‖ ^ 2 ≤ 2 * (if k = l then 1 else 0) + 2 * Y₁ ^ 2 * B k l := by
    intro k l hk hl
    have h := Resample_sq_le (hM k l hk hl)
    have h2 := Resample_norm_ite_sq (ι := ι) hm1 k l
    have h3 : (Y₁ * Real.sqrt (B k l)) ^ 2 = Y₁ ^ 2 * B k l := by
      rw [mul_pow, Real.sq_sqrt (hB0 k l)]
    rw [h3] at h
    nlinarith
  have hY2 : 1 ≤ Y₁ ^ 2 := by nlinarith
  have hite0 : ∀ k l : ι, (0 : ℝ) ≤ (if k = l then 1 else 0) := fun k l => by
    split_ifs <;> norm_num
  -- the row and column sums
  have hrow : ∀ j, ∑ k, S y k * (2 * (if k = j then 1 else 0) + 2 * Y₁ ^ 2 * B k j) ≤
      2 * (Cs + Cc) * Y₁ ^ 2 * B y j := by
    intro j
    have e : ∑ k, S y k * (2 * (if k = j then 1 else 0) + 2 * Y₁ ^ 2 * B k j) =
        2 * S y j + 2 * Y₁ ^ 2 * ∑ k, S y k * B k j := by
      have e1 : ∀ k, S y k * (2 * (if k = j then 1 else 0) + 2 * Y₁ ^ 2 * B k j) =
          2 * (if k = j then S y k else 0) + 2 * Y₁ ^ 2 * (S y k * B k j) := by
        intro k; split_ifs <;> ring
      rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [e]
    have h1 := hSB y j
    have h2 := hconv y j
    have hb := hB0 y j
    have : Cs * B y j ≤ Cs * Y₁ ^ 2 * B y j := by
      have := mul_le_mul_of_nonneg_left hY2 (mul_nonneg hCs hb); nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * Y₁ ^ 2)]
  refine ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_⟩
  · refine (Resample_sum_ne_le y (fun k => S y k * ‖M k j‖ ^ 2)
      (fun k => S y k * (2 * (if k = j then 1 else 0) + 2 * Y₁ ^ 2 * B k j))
      (fun k hk => mul_le_mul_of_nonneg_left (hsq k j hk hj) (hS0 y k))
      (fun k => mul_nonneg (hS0 y k) (by have := hite0 k j; have := hB0 k j; positivity))).trans
      (hrow j)
  · refine (Resample_sum_ne_le y (fun k => S y k * ‖M j k‖ ^ 2)
      (fun k => S y k * (2 * (if k = j then 1 else 0) + 2 * Y₁ ^ 2 * B k j))
      (fun k hk => ?_)
      (fun k => mul_nonneg (hS0 y k) (by have := hite0 k j; have := hB0 k j; positivity))).trans
      (hrow j)
    refine mul_le_mul_of_nonneg_left ((hsq j k hj hk).trans (le_of_eq ?_)) (hS0 y k)
    rw [hBs j k]
    by_cases h : j = k
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  · -- the quadratic form
    have hterm : ∀ k l, k ≠ y → l ≠ y → S y k * ‖M k l‖ ^ 2 * S l y ≤
        S y k * (2 * (if k = l then 1 else 0) + 2 * Y₁ ^ 2 * B k l) * S l y := by
      intro k l hk hl
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsq k l hk hl) (hS0 y k))
        (hS0 l y)
    have hg0 : ∀ k l, 0 ≤ S y k * (2 * (if k = l then 1 else 0) + 2 * Y₁ ^ 2 * B k l) * S l y := by
      intro k l
      have := hite0 k l
      have := hB0 k l
      have := hS0 y k
      have := hS0 l y
      positivity
    have h1 : ∑ k : {a : ι // a ≠ y}, ∑ l : {a : ι // a ≠ y}, S y k.1 * ‖M k.1 l.1‖ ^ 2 * S l.1 y ≤
        ∑ k, ∑ l, S y k * (2 * (if k = l then 1 else 0) + 2 * Y₁ ^ 2 * B k l) * S l y := by
      refine Resample_sum_ne_le y (fun k => ∑ l : {a : ι // a ≠ y}, S y k * ‖M k l.1‖ ^ 2 * S l.1 y)
        (fun k => ∑ l, S y k * (2 * (if k = l then 1 else 0) + 2 * Y₁ ^ 2 * B k l) * S l y)
        (fun k hk => Resample_sum_ne_le y _ _ (fun l hl => hterm k l hk hl) (fun l => hg0 k l))
        (fun k => Finset.sum_nonneg fun l _ => hg0 k l)
    refine h1.trans ?_
    have e : ∑ k, ∑ l, S y k * (2 * (if k = l then 1 else 0) + 2 * Y₁ ^ 2 * B k l) * S l y =
        2 * ∑ k, S y k * S k y + 2 * Y₁ ^ 2 * ∑ l, (∑ k, S y k * B k l) * S l y := by
      have : ∀ k, ∑ l, S y k * (2 * (if k = l then 1 else 0) + 2 * Y₁ ^ 2 * B k l) * S l y =
          2 * (S y k * S k y) + 2 * Y₁ ^ 2 * ∑ l, S y k * B k l * S l y := by
        intro k
        have e1 : ∀ l, S y k * (2 * (if k = l then 1 else 0) + 2 * Y₁ ^ 2 * B k l) * S l y =
            2 * (if k = l then S y k * S l y else 0) + 2 * Y₁ ^ 2 * (S y k * B k l * S l y) := by
          intro l; split_ifs <;> ring
        rw [Finset.sum_congr rfl fun l _ => e1 l, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_comm (f := fun k l => S y k * B k l * S l y)]
      congr 2
      exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_mul]
    rw [e]
    have hA : ∑ k, S y k * S k y ≤ Cs * r ^ 2 := by
      calc ∑ k, S y k * S k y ≤ ∑ k, S y k * (Cs * r ^ 2) :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
              ((hSB k y).trans (mul_le_mul_of_nonneg_left (hBw k y) hCs)) (hS0 y k)
        _ = Cs * r ^ 2 := by rw [← Finset.sum_mul, hS1 y, one_mul]
    have hB : ∑ l, (∑ k, S y k * B k l) * S l y ≤ Cc ^ 2 * r ^ 2 := by
      calc ∑ l, (∑ k, S y k * B k l) * S l y ≤ ∑ l, Cc * B y l * S l y :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hconv y l) (hS0 l y)
        _ = Cc * ∑ l, S y l * B l y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by rw [hSs l y, hBs y l]; ring
        _ ≤ Cc * (Cc * B y y) := mul_le_mul_of_nonneg_left (hconv y y) hCc
        _ = Cc ^ 2 * r ^ 2 := by rw [hBd]; ring
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    have : Cs * r ^ 2 ≤ Cs * Y₁ ^ 2 * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left hY2 (mul_nonneg hCs hr2); nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 * Y₁ ^ 2)]
  · -- the sum `Σ_{k ≠ y} s_{yk} M_{kk} − m`
    have hsum1 : ∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) = 1 - S y y := by
      have := sum_subtype_ne y (fun k => (S y k : ℂ))
      rw [this]
      have h := congrArg (fun x : ℝ => (x : ℂ)) (hS1 y)
      simp only [ofReal_sum, ofReal_one] at h
      rw [h]
    have e : ∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) * M k.1 k.1 - m =
        ∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) * (M k.1 k.1 - m) - (S y y : ℂ) * m := by
      have : ∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) * (M k.1 k.1 - m) =
          ∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) * M k.1 k.1 - (1 - S y y) * m := by
        rw [← hsum1, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this]; ring
    rw [e]
    have hk : ∀ k : {a : ι // a ≠ y}, ‖(S y k.1 : ℂ) * (M k.1 k.1 - m)‖ ≤ S y k.1 * (Y₁ * r) := by
      intro k
      have h := hM k.1 k.1 k.2 k.2
      rw [ite_eq_left rfl, hBd, Real.sqrt_sq hr] at h
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS0 y k.1)]
      exact mul_le_mul_of_nonneg_left h (hS0 y k.1)
    have h1 : ‖∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) * (M k.1 k.1 - m)‖ ≤ Y₁ * r := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hk k).trans ?_)
      rw [← Finset.sum_mul]
      have : ∑ k : {a : ι // a ≠ y}, S y k.1 ≤ 1 := by
        have := Resample_sum_ne_le y (fun k => S y k) (fun k => S y k) (fun _ _ => le_rfl)
          (fun k => hS0 y k)
        rw [hS1 y] at this; exact this
      have : 0 ≤ Y₁ * r := by positivity
      nlinarith
    have h2 : ‖(S y y : ℂ) * m‖ ≤ Cs * r ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS0 y y)]
      calc S y y * ‖m‖ ≤ (Cs * B y y) * 1 :=
            mul_le_mul (hSB y y) hm1 (norm_nonneg _) (by have := hB0 y y; positivity)
        _ = Cs * r ^ 2 := by rw [hBd, mul_one]
    calc ‖∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) * (M k.1 k.1 - m) - (S y y : ℂ) * m‖
        ≤ Y₁ * r + Cs * r ^ 2 := (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ ≤ (1 + Cs) * Y₁ * r := by
          have : Cs * r ^ 2 ≤ Cs * Y₁ * r := by
            have : r ^ 2 ≤ Y₁ * r := by nlinarith
            exact mul_le_mul_of_nonneg_left this hCs |>.trans_eq (by ring)
          nlinarith

omit [Fintype ι] in
/-- The minor `G^{(y)}` from `|G_{ij} − m δ_{ij}| ≤ Y B_{ij}^{1/2}`:
`|G_{yy}| ≥ 1/8` and `|G^{(y)}_{kl} − m δ_{kl}| ≤ (1 + ĉ) Y B_{kl}^{1/2}` for `k, l ≠ y`, given
`Y r ≤ 1/8`, `B_{yy} = r²` and `B_{ky}^{1/2} B_{yl}^{1/2} ≤ ĉ r B_{kl}^{1/2}`. -/
private theorem Resample_minor (G : Matrix ι ι ℂ) (B : ι → ι → ℝ) (m : ℂ) (y : ι) (Y r ĉ : ℝ)
    (hm4 : 1 / 4 ≤ ‖m‖) (hBd : B y y = r ^ 2) (hr : 0 ≤ r)
    (hY : 1 ≤ Y) (hYr : Y * r ≤ 1 / 8) (hĉ : 0 ≤ ĉ)
    (hBp : ∀ k l, Real.sqrt (B k y) * Real.sqrt (B y l) ≤ ĉ * r * Real.sqrt (B k l))
    (hG : ∀ i j, ‖entryErr G m i j‖ ≤ Y * Real.sqrt (B i j)) :
    1 / 8 ≤ ‖G y y‖ ∧ ∀ k l, k ≠ y → l ≠ y →
      ‖greenMinor G y k l - (if k = l then m else 0)‖ ≤ (1 + ĉ) * Y * Real.sqrt (B k l) := by
  have hyy : ‖G y y - m‖ ≤ Y * r := by
    have h := hG y y
    rwa [entryErr, ite_eq_left rfl, hBd, Real.sqrt_sq hr] at h
  have hGy : 1 / 8 ≤ ‖G y y‖ := by
    have : ‖m‖ ≤ ‖G y y‖ + ‖G y y - m‖ := by
      calc ‖m‖ = ‖G y y - (G y y - m)‖ := by ring_nf
        _ ≤ ‖G y y‖ + ‖G y y - m‖ := norm_sub_le _ _
    linarith
  refine ⟨hGy, fun k l hk hl => ?_⟩
  have hGy0 : G y y ≠ 0 := by
    intro h; rw [h, norm_zero] at hGy; norm_num at hGy
  have hky : ‖G k y‖ ≤ Y * Real.sqrt (B k y) := by
    have h := hG k y; rwa [entryErr, ite_eq_right hk, sub_zero] at h
  have hyl : ‖G y l‖ ≤ Y * Real.sqrt (B y l) := by
    have h := hG y l; rwa [entryErr, ite_eq_right (Ne.symm hl), sub_zero] at h
  have e : greenMinor G y k l - (if k = l then m else 0) =
      entryErr G m k l - G k y * G y l / G y y := by
    unfold greenMinor entryErr; ring
  rw [e]
  have h1 : ‖G k y * G y l / G y y‖ ≤ 8 * (Y * Real.sqrt (B k y)) * (Y * Real.sqrt (B y l)) := by
    rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
    have := mul_le_mul hky hyl (norm_nonneg _) (by positivity)
    have h8 : 1 ≤ 8 * ‖G y y‖ := by linarith
    have h0 : 0 ≤ Y * Real.sqrt (B k y) * (Y * Real.sqrt (B y l)) := by positivity
    nlinarith
  have h2 : 8 * (Y * Real.sqrt (B k y)) * (Y * Real.sqrt (B y l)) ≤ ĉ * Y * Real.sqrt (B k l) := by
    have hb := hBp k l
    have hs : 0 ≤ Real.sqrt (B k l) := Real.sqrt_nonneg _
    calc 8 * (Y * Real.sqrt (B k y)) * (Y * Real.sqrt (B y l))
        = 8 * Y ^ 2 * (Real.sqrt (B k y) * Real.sqrt (B y l)) := by ring
      _ ≤ 8 * Y ^ 2 * (ĉ * r * Real.sqrt (B k l)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (8 * Y * r) * (ĉ * Y * Real.sqrt (B k l)) := by ring
      _ ≤ 1 * (ĉ * Y * Real.sqrt (B k l)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ĉ * Y * Real.sqrt (B k l) := one_mul _
  calc ‖entryErr G m k l - G k y * G y l / G y y‖
      ≤ ‖entryErr G m k l‖ + ‖G k y * G y l / G y y‖ := norm_sub_le _ _
    _ ≤ Y * Real.sqrt (B k l) + ĉ * Y * Real.sqrt (B k l) := add_le_add (hG k l) (h1.trans h2)
    _ = (1 + ĉ) * Y * Real.sqrt (B k l) := by ring

/-- `G_{ji} = −G_{ii} Σ_{k≠i} G^{(i)}_{jk} h_{ki}` for `j ≠ i`. -/
private theorem Resample_col_eq {H : Matrix ι ι ℂ} {z : ℂ} (hH : H.IsHermitian) (hz : 0 < z.im)
    {i j : ι} (hij : i ≠ j) :
    green H z j i = -(green H z i i) * ∑ k : {a : ι // a ≠ i},
      greenMinor (green H z) i j k.1 * H k.1 i := by
  have hGii : green H z i i ≠ 0 := green_diag_ne_zero hH hz i
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

/-- **The new row**: for `H'` whose minor at `y`
satisfies `|G'^{(y)}_{kl} − m δ_{kl}| ≤ Y₁ B_{kl}^{1/2}` (`k, l ≠ y`), on the large deviation
bounds at row `y` with factor `τ²`, and with `C_E τ Y₁ r ≤ 1/16`:
`|G'_{yy} − m| ≤ 2 C_E τ Y₁ r`, `1/8 ≤ |G'_{yy}| ≤ 2`, and
`|G'_{yj}|, |G'_{jy}| ≤ 2 (C_R + 1) τ Y₁ B_{yj}^{1/2}` for `j ≠ y`, where `C_R = 2(C_s + C_c)` and
`C_E = 2 C_s + 2(C_s + C_c²) + 3`. -/
private theorem Resample_newrow (H : Matrix ι ι ℂ) (z m : ℂ) (S : Matrix ι ι ℝ) (B : ι → ι → ℝ)
    (y : ι) (Y₁ r τ Cs Cc : ℝ) (hH : H.IsHermitian) (hz : 0 < z.im) (hm : m * (m + z) = -1)
    (hm4 : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k = 1)
    (hSs : ∀ i k, S i k = S k i) (hB0 : ∀ i j, 0 ≤ B i j) (hBs : ∀ i j, B i j = B j i)
    (hBw : ∀ i j, B i j ≤ r ^ 2) (hBd : ∀ i, B i i = r ^ 2) (hSB : ∀ i j, S i j ≤ Cs * B i j)
    (hconv : ∀ x z, ∑ α, S x α * B α z ≤ Cc * B x z) (hCs : 0 ≤ Cs) (hCc : 0 ≤ Cc)
    (hY₁ : 1 ≤ Y₁) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 1 ≤ τ)
    (hM : ∀ k l, k ≠ y → l ≠ y →
      ‖greenMinor (green H z) y k l - (if k = l then m else 0)‖ ≤ Y₁ * Real.sqrt (B k l))
    (hR : ∀ j, ldeRowLHS H (green H z) y j ≤ τ ^ 2 * ldeRowRHS S (green H z) y j)
    (hC : ∀ j, ldeColLHS H (green H z) y j ≤ τ ^ 2 * ldeColRHS S (green H z) y j)
    (hQ : ldeQuadLHS H (green H z) S y ≤ τ ^ 2 * ldeQuadRHS S (green H z) y)
    (hd : ‖H y y‖ ^ 2 ≤ τ ^ 2 * S y y)
    (hsm : (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) * τ * Y₁ * r ≤ 1 / 16) :
    ‖green H z y y - m‖ ≤ 2 * (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) * τ * Y₁ * r ∧
    1 / 8 ≤ ‖green H z y y‖ ∧ ‖green H z y y‖ ≤ 2 ∧
    ∀ j, j ≠ y → ‖green H z y j‖ ≤ 2 * (2 * (Cs + Cc) + 1) * τ * Y₁ * Real.sqrt (B y j) ∧
      ‖green H z j y‖ ≤ 2 * (2 * (Cs + Cc) + 1) * τ * Y₁ * Real.sqrt (B y j) := by
  set G := green H z with hGdef
  set M := greenMinor G y with hMdef
  obtain ⟨hrow, hcol, hquad, hsum⟩ :=
    Resample_rhs S B M m y Y₁ r Cs Cc hS0 hS1 hSs hB0 hBs hBw hBd hSB hconv hCs hCc hm1 hY₁ hr hr1
      hM
  set CR := 2 * (Cs + Cc) with hCR
  set CQ := 2 * (Cs + Cc ^ 2) with hCQ
  set CE := 2 * Cs + CQ + 3 with hCE
  have hCR0 : 0 ≤ CR := by positivity
  have hCQ0 : 0 ≤ CQ := by positivity
  have hτ0 : 0 ≤ τ := by linarith
  have hY0 : 0 ≤ Y₁ := by linarith
  -- the diagonal entry
  have hm0 : m ≠ 0 := by intro h; rw [h, norm_zero] at hm4; norm_num at hm4
  have hGy0 : G y y ≠ 0 := green_diag_ne_zero hH hz y
  set T := ∑ k : {a : ι // a ≠ y}, ∑ l : {a : ι // a ≠ y}, H y k.1 * M k.1 l.1 * H l.1 y with hT
  set Ts := ∑ k : {a : ι // a ≠ y}, (S y k.1 : ℂ) * M k.1 k.1 with hTs
  have hschur : G y y = (H y y - z - T)⁻¹ := green_diag_schur hH hz y
  have hinvm : m⁻¹ = -(m + z) := by
    rw [inv_eq_iff_eq_inv, eq_comm]
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination -hm
  have hdiff : (G y y)⁻¹ - m⁻¹ = H y y - (T - Ts) - (Ts - m) := by
    rw [hschur, inv_inv, hinvm]; ring
  have hQ' : ‖T - Ts‖ ≤ (CQ + 1) * (τ * Y₁ * r) := by
    refine Resample_le_of_sq hCQ0 (by positivity) ?_
    have h := hQ
    unfold ldeQuadLHS ldeQuadRHS at h
    calc ‖T - Ts‖ ^ 2 ≤ τ ^ 2 * (CQ * Y₁ ^ 2 * r ^ 2) :=
          h.trans (mul_le_mul_of_nonneg_left hquad (by positivity))
      _ = CQ * (τ * Y₁ * r) ^ 2 := by ring
  have hd' : ‖H y y‖ ≤ (Cs + 1) * (τ * r) := by
    refine Resample_le_of_sq hCs (by positivity) ?_
    calc ‖H y y‖ ^ 2 ≤ τ ^ 2 * (Cs * r ^ 2) :=
          hd.trans (mul_le_mul_of_nonneg_left ((hSB y y).trans_eq (by rw [hBd])) (by positivity))
      _ = Cs * (τ * r) ^ 2 := by ring
  set E := CE * τ * Y₁ * r with hE
  have hEb : ‖(G y y)⁻¹ - m⁻¹‖ ≤ E := by
    rw [hdiff]
    have h1 := norm_sub_le (H y y - (T - Ts)) (Ts - m)
    have h2 := norm_sub_le (H y y) (T - Ts)
    have hτY : τ * r ≤ τ * Y₁ * r := by
      have := mul_le_mul_of_nonneg_left hY₁ (mul_nonneg hτ0 hr); nlinarith
    have hYτ : Y₁ * r ≤ τ * Y₁ * r := by
      have := mul_le_mul_of_nonneg_left hτ (mul_nonneg hY0 hr); nlinarith
    have : ‖H y y‖ + ‖T - Ts‖ + ‖Ts - m‖ ≤ E := by
      have e1 : (Cs + 1) * (τ * r) ≤ (Cs + 1) * (τ * Y₁ * r) :=
        mul_le_mul_of_nonneg_left hτY (by linarith)
      have e2 : (1 + Cs) * Y₁ * r ≤ (1 + Cs) * (τ * Y₁ * r) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hYτ (by linarith)
      rw [hE, hCE]
      nlinarith
    linarith
  have hE0 : 0 ≤ E := by positivity
  have hE16 : E ≤ 1 / 16 := hsm
  have hm1' : 1 ≤ ‖m⁻¹‖ := by rw [norm_inv]; exact one_le_inv₀ (by linarith) |>.2 hm1
  have hu : 15 / 16 ≤ ‖(G y y)⁻¹‖ := by
    have : ‖m⁻¹‖ ≤ ‖(G y y)⁻¹‖ + ‖(G y y)⁻¹ - m⁻¹‖ := by
      calc ‖m⁻¹‖ = ‖(G y y)⁻¹ - ((G y y)⁻¹ - m⁻¹)‖ := by ring_nf
        _ ≤ ‖(G y y)⁻¹‖ + ‖(G y y)⁻¹ - m⁻¹‖ := norm_sub_le _ _
    linarith
  have hGyy2 : ‖G y y‖ ≤ 16 / 15 := by
    rw [norm_inv] at hu
    have hpos : 0 < ‖G y y‖ := norm_pos_iff.2 hGy0
    rw [le_inv_comm₀ (by norm_num) hpos] at hu
    linarith
  have hdy : ‖G y y - m‖ ≤ 2 * E := by
    have e : G y y - m = G y y * m * (m⁻¹ - (G y y)⁻¹) := by field_simp
    rw [e, norm_mul, norm_mul, norm_sub_rev]
    calc ‖G y y‖ * ‖m‖ * ‖(G y y)⁻¹ - m⁻¹‖ ≤ (16 / 15) * 1 * E := by
          gcongr
      _ ≤ 2 * E := by nlinarith
  have hGy8 : 1 / 8 ≤ ‖G y y‖ := by
    have : ‖m‖ ≤ ‖G y y‖ + ‖G y y - m‖ := by
      calc ‖m‖ = ‖G y y - (G y y - m)‖ := by ring_nf
        _ ≤ ‖G y y‖ + ‖G y y - m‖ := norm_sub_le _ _
    linarith
  refine ⟨hdy.trans_eq (by rw [hE]; ring), hGy8, by linarith, fun j hj => ⟨?_, ?_⟩⟩
  · -- the row
    have hrowj : ‖∑ k : {a : ι // a ≠ y}, H y k.1 * M k.1 j‖ ≤
        (CR + 1) * (τ * Y₁ * Real.sqrt (B y j)) := by
      refine Resample_le_of_sq hCR0 (by positivity) ?_
      have h := hR j
      unfold ldeRowLHS ldeRowRHS at h
      calc ‖∑ k : {a : ι // a ≠ y}, H y k.1 * M k.1 j‖ ^ 2 ≤ τ ^ 2 * (CR * Y₁ ^ 2 * B y j) :=
            h.trans (mul_le_mul_of_nonneg_left (hrow j hj) (by positivity))
        _ = CR * (τ * Y₁ * Real.sqrt (B y j)) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (hB0 y j)]; ring
    have e := green_offdiag_eq hH hz (i := y) (j := j) hj
    rw [← hGdef] at e
    have e' : G y j = -(G y y) * ∑ k : {a : ι // a ≠ y}, H y k.1 * M k.1 j := by
      rw [e]; rfl
    rw [e', norm_mul, norm_neg]
    calc ‖G y y‖ * ‖∑ k : {a : ι // a ≠ y}, H y k.1 * M k.1 j‖
        ≤ 2 * ((CR + 1) * (τ * Y₁ * Real.sqrt (B y j))) :=
          mul_le_mul (by linarith) hrowj (norm_nonneg _) (by norm_num)
      _ = 2 * (CR + 1) * τ * Y₁ * Real.sqrt (B y j) := by ring
  · -- the column
    have hcolj : ‖∑ k : {a : ι // a ≠ y}, M j k.1 * H k.1 y‖ ≤
        (CR + 1) * (τ * Y₁ * Real.sqrt (B y j)) := by
      refine Resample_le_of_sq hCR0 (by positivity) ?_
      have h := hC j
      unfold ldeColLHS ldeColRHS at h
      calc ‖∑ k : {a : ι // a ≠ y}, M j k.1 * H k.1 y‖ ^ 2 ≤ τ ^ 2 * (CR * Y₁ ^ 2 * B y j) :=
            h.trans (mul_le_mul_of_nonneg_left (hcol j hj) (by positivity))
        _ = CR * (τ * Y₁ * Real.sqrt (B y j)) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (hB0 y j)]; ring
    have e := Resample_col_eq hH hz (i := y) (j := j) (Ne.symm hj)
    rw [← hGdef] at e
    rw [e, norm_mul, norm_neg]
    calc ‖G y y‖ * ‖∑ k : {a : ι // a ≠ y}, M j k.1 * H k.1 y‖
        ≤ 2 * ((CR + 1) * (τ * Y₁ * Real.sqrt (B y j))) :=
          mul_le_mul (by linarith) hcolj (norm_nonneg _) (by norm_num)
      _ = 2 * (CR + 1) * τ * Y₁ * Real.sqrt (B y j) := by ring

/-- `| |a|² − |b|² | ≤ λ |a|² + (1 + 1/λ) |a − b|²` for `λ > 0`. -/
private theorem Resample_sq_diff (a b : ℂ) {lam : ℝ} (hl : 0 < lam) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ lam * ‖a‖ ^ 2 + (1 + 1 / lam) * ‖a - b‖ ^ 2 := by
  have h1 : ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
    calc ‖b‖ = ‖a - (a - b)‖ := by ring_nf
      _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _
  have h2 : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    calc ‖a‖ = ‖b + (a - b)‖ := by ring_nf
      _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le _ _
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a - b)
  have h3 : |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * ‖a‖ * ‖a - b‖ + ‖a - b‖ ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have h4 : 2 * ‖a‖ * ‖a - b‖ ≤ lam * ‖a‖ ^ 2 + 1 / lam * ‖a - b‖ ^ 2 := by
    have : 0 ≤ (lam * ‖a‖ - ‖a - b‖) ^ 2 / lam := div_nonneg (sq_nonneg _) hl.le
    have e : (lam * ‖a‖ - ‖a - b‖) ^ 2 / lam =
        lam * ‖a‖ ^ 2 + 1 / lam * ‖a - b‖ ^ 2 - 2 * ‖a‖ * ‖a - b‖ := by
      field_simp; ring
    linarith
  linarith

/-- The entries of the resampled resolvent: with `Y₁ = (1 + ĉ) Y` and
`Z = C_Y τ Y₁`, `|G'_{ij} − m δ_{ij}| ≤ Z B_{ij}^{1/2}` for all `i, j`, and
`|G_{yy}|, |G'_{yy}| ≥ 1/8`. -/
private theorem Resample_pairEntries (H H' : Matrix ι ι ℂ) (z m : ℂ) (S : Matrix ι ι ℝ)
    (B : ι → ι → ℝ) (y : ι) (Y r τ ĉ Cs Cc : ℝ) (hH' : H'.IsHermitian)
    (hz : 0 < z.im) (hm : m * (m + z) = -1) (hm4 : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1)
    (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k = 1) (hSs : ∀ i k, S i k = S k i)
    (hB0 : ∀ i j, 0 < B i j) (hBs : ∀ i j, B i j = B j i) (hBw : ∀ i j, B i j ≤ r ^ 2)
    (hBd : ∀ i, B i i = r ^ 2) (hSB : ∀ i j, S i j ≤ Cs * B i j)
    (hconv : ∀ x z, ∑ α, S x α * B α z ≤ Cc * B x z) (hCs : 0 ≤ Cs) (hCc : 0 ≤ Cc)
    (hĉ : 0 ≤ ĉ)
    (hBp' : ∀ k y l, Real.sqrt (B k y) * Real.sqrt (B y l) ≤ ĉ * r * Real.sqrt (B k l))
    (hY : 1 ≤ Y) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 1 ≤ τ) (hYr : Y * r ≤ 1 / 8)
    (hsm : (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) * τ * ((1 + ĉ) * Y) * r ≤ 1 / 16)
    (hminor : ∀ a b, greenMinor (green H' z) y a b = greenMinor (green H z) y a b)
    (hG : ∀ i j, ‖entryErr (green H z) m i j‖ ≤ Y * Real.sqrt (B i j))
    (hR : ∀ j, ldeRowLHS H' (green H' z) y j ≤ τ ^ 2 * ldeRowRHS S (green H' z) y j)
    (hC : ∀ j, ldeColLHS H' (green H' z) y j ≤ τ ^ 2 * ldeColRHS S (green H' z) y j)
    (hQ : ldeQuadLHS H' (green H' z) S y ≤ τ ^ 2 * ldeQuadRHS S (green H' z) y)
    (hd : ‖H' y y‖ ^ 2 ≤ τ ^ 2 * S y y) :
    1 / 8 ≤ ‖green H z y y‖ ∧ 1 / 8 ≤ ‖green H' z y y‖ ∧
    Y ≤ (2 * (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) + 2 * (2 * (Cs + Cc) + 1) + 1 +
        2 * (2 * (Cs + Cc) + 1) ^ 2 * ĉ) * τ * ((1 + ĉ) * Y) ∧
    ∀ i j, ‖entryErr (green H' z) m i j‖ ≤
      (2 * (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) + 2 * (2 * (Cs + Cc) + 1) + 1 +
        2 * (2 * (Cs + Cc) + 1) ^ 2 * ĉ) * τ * ((1 + ĉ) * Y) * Real.sqrt (B i j) := by
  set G := green H z with hGdef
  set G' := green H' z with hG'def
  set CR := 2 * (Cs + Cc) with hCR
  set CE := 2 * Cs + 2 * (Cs + Cc ^ 2) + 3 with hCE
  set Y₁ := (1 + ĉ) * Y with hY₁def
  set CY := 2 * CE + 2 * (CR + 1) + 1 + 2 * (CR + 1) ^ 2 * ĉ with hCY
  set Z := CY * τ * Y₁ with hZ
  have hB0' : ∀ i j, 0 ≤ B i j := fun i j => (hB0 i j).le
  have hCR0 : 0 ≤ CR := by positivity
  have hCE1 : 1 ≤ CE := by rw [hCE]; nlinarith [sq_nonneg Cc]
  have hY₁ : 1 ≤ Y₁ := by rw [hY₁def]; nlinarith
  have hYY₁ : Y ≤ Y₁ := by rw [hY₁def]; nlinarith
  have hτ0 : 0 ≤ τ := by linarith
  have hCY1 : 1 ≤ CY := by
    rw [hCY]; have : 0 ≤ 2 * (CR + 1) ^ 2 * ĉ := by positivity
    linarith
  have hY₁Z : τ * Y₁ ≤ Z := by
    have := mul_le_mul_of_nonneg_right hCY1 (mul_nonneg hτ0 (by linarith : 0 ≤ Y₁))
    rw [hZ, mul_assoc]; linarith
  have hτY₁ : 1 ≤ τ * Y₁ := one_le_mul_of_one_le_of_one_le hτ hY₁
  have hZ1 : 1 ≤ Z := hτY₁.trans hY₁Z
  have hYZ : Y ≤ Z := hYY₁.trans ((le_mul_of_one_le_left (by linarith) hτ).trans hY₁Z)
  have hτY₁r : τ * Y₁ * r ≤ 1 / 16 := by
    have h0 : 0 ≤ τ * Y₁ * r := by positivity
    have : τ * Y₁ * r ≤ CE * τ * Y₁ * r := by
      have := mul_le_mul_of_nonneg_right hCE1 h0
      calc τ * Y₁ * r = 1 * (τ * Y₁ * r) := (one_mul _).symm
        _ ≤ CE * (τ * Y₁ * r) := this
        _ = CE * τ * Y₁ * r := by ring
    linarith
  -- the minor of `G`, which is the minor of `G'`
  obtain ⟨hGyy, hM⟩ := Resample_minor G B m y Y r ĉ hm4 (hBd y) hr hY hYr hĉ
    (fun k l => hBp' k y l) hG
  have hM' : ∀ k l, k ≠ y → l ≠ y →
      ‖greenMinor G' y k l - (if k = l then m else 0)‖ ≤ Y₁ * Real.sqrt (B k l) := by
    intro k l hk hl; rw [hminor]; exact (hM k l hk hl).trans_eq (by ring)
  obtain ⟨hdy, hGy8, hGy2, hrowcol⟩ := Resample_newrow H' z m S B y Y₁ r τ Cs Cc hH' hz hm hm4 hm1
    hS0 hS1 hSs hB0' hBs hBw hBd hSB hconv hCs hCc hY₁ hr hr1 hτ hM' hR hC hQ hd hsm
  -- the entries of `G'`
  have hsq : ∀ i, Real.sqrt (B i i) = r := fun i => by rw [hBd, Real.sqrt_sq hr]
  have hfac : ∀ k u : ℝ, k ≤ CY → 0 ≤ u → k * τ * Y₁ * u ≤ Z * u := by
    intro k u hk hu
    have h0 : 0 ≤ τ * Y₁ * u := by positivity
    calc k * τ * Y₁ * u = k * (τ * Y₁ * u) := by ring
      _ ≤ CY * (τ * Y₁ * u) := mul_le_mul_of_nonneg_right hk h0
      _ = Z * u := by rw [hZ]; ring
  have hc0 : 0 ≤ 2 * (CR + 1) ^ 2 * ĉ := by positivity
  have hk1 : 2 * CE ≤ CY := by rw [hCY]; linarith
  have hk2 : 2 * (CR + 1) ≤ CY := by rw [hCY]; linarith
  have hk3 : 1 + 2 * (CR + 1) ^ 2 * ĉ ≤ CY := by rw [hCY]; linarith
  have hG' : ∀ i j, ‖entryErr G' m i j‖ ≤ Z * Real.sqrt (B i j) := by
    intro i j
    have hsij : 0 ≤ Real.sqrt (B i j) := Real.sqrt_nonneg _
    by_cases hi : i = y
    · subst hi
      by_cases hj : j = i
      · subst hj
        rw [entryErr, ite_eq_left rfl, hsq]
        refine hdy.trans ?_
        have := hfac (2 * CE) r hk1 hr
        calc 2 * CE * τ * Y₁ * r = 2 * CE * τ * Y₁ * r := rfl
          _ ≤ Z * r := this
      · rw [entryErr, ite_eq_right (Ne.symm hj), sub_zero]
        exact (hrowcol j hj).1.trans (hfac _ _ hk2 hsij)
    · by_cases hj : j = y
      · subst hj
        rw [entryErr, ite_eq_right hi, sub_zero]
        refine (hrowcol i hi).2.trans ?_
        rw [hBs j i]
        exact hfac _ _ hk2 hsij
      · have e : entryErr G' m i j = (greenMinor G' y i j - (if i = j then m else 0)) +
            G' i y * G' y j / G' y y := by
          unfold entryErr greenMinor; ring
        rw [e]
        have h1 := hM' i j hi hj
        have hiy := (hrowcol i hi).2
        have hyj := (hrowcol j hj).1
        rw [hBs y i] at hiy
        set K₂ := 2 * (CR + 1) * τ * Y₁ with hK₂
        have hK₂0 : 0 ≤ K₂ := by positivity
        have h2 : ‖G' i y * G' y j / G' y y‖ ≤
            8 * ((K₂ * Real.sqrt (B i y)) * (K₂ * Real.sqrt (B y j))) := by
          rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
          have hm' := mul_le_mul hiy hyj (norm_nonneg _) (by positivity)
          have h0 : 0 ≤ K₂ * Real.sqrt (B i y) * (K₂ * Real.sqrt (B y j)) := by positivity
          have h8 : 1 ≤ 8 * ‖G' y y‖ := by linarith
          calc ‖G' i y‖ * ‖G' y j‖ ≤ K₂ * Real.sqrt (B i y) * (K₂ * Real.sqrt (B y j)) := hm'
            _ = 1 * (K₂ * Real.sqrt (B i y) * (K₂ * Real.sqrt (B y j))) := (one_mul _).symm
            _ ≤ (8 * ‖G' y y‖) * (K₂ * Real.sqrt (B i y) * (K₂ * Real.sqrt (B y j))) :=
                mul_le_mul_of_nonneg_right h8 h0
            _ = _ := by ring
        have h3 : 8 * ((K₂ * Real.sqrt (B i y)) * (K₂ * Real.sqrt (B y j))) ≤
            2 * (CR + 1) ^ 2 * ĉ * τ * Y₁ * Real.sqrt (B i j) := by
          have hb := hBp' i y j
          calc 8 * ((K₂ * Real.sqrt (B i y)) * (K₂ * Real.sqrt (B y j)))
              = 8 * K₂ ^ 2 * (Real.sqrt (B i y) * Real.sqrt (B y j)) := by ring
            _ ≤ 8 * K₂ ^ 2 * (ĉ * r * Real.sqrt (B i j)) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = (2 * (CR + 1) ^ 2 * ĉ * τ * Y₁ * Real.sqrt (B i j)) * (16 * (τ * Y₁ * r)) := by
                rw [hK₂]; ring
            _ ≤ (2 * (CR + 1) ^ 2 * ĉ * τ * Y₁ * Real.sqrt (B i j)) * 1 :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = _ := mul_one _
        have h4 : Y₁ * Real.sqrt (B i j) ≤ 1 * τ * Y₁ * Real.sqrt (B i j) := by
          have := mul_le_mul_of_nonneg_right hτ (mul_nonneg (by linarith : 0 ≤ Y₁) hsij)
          calc Y₁ * Real.sqrt (B i j) = 1 * (Y₁ * Real.sqrt (B i j)) := (one_mul _).symm
            _ ≤ τ * (Y₁ * Real.sqrt (B i j)) := this
            _ = 1 * τ * Y₁ * Real.sqrt (B i j) := by ring
        calc ‖greenMinor G' y i j - (if i = j then m else 0) + G' i y * G' y j / G' y y‖
            ≤ Y₁ * Real.sqrt (B i j) + 2 * (CR + 1) ^ 2 * ĉ * τ * Y₁ * Real.sqrt (B i j) :=
              (norm_add_le _ _).trans (add_le_add h1 (h2.trans h3))
          _ ≤ 1 * τ * Y₁ * Real.sqrt (B i j) + 2 * (CR + 1) ^ 2 * ĉ * τ * Y₁ * Real.sqrt (B i j) :=
              by linarith
          _ = (1 + 2 * (CR + 1) ^ 2 * ĉ) * τ * Y₁ * Real.sqrt (B i j) := by ring
          _ ≤ Z * Real.sqrt (B i j) := hfac _ _ hk3 hsij
  exact ⟨hGyy, hGy8, hYZ, hG'⟩

omit [Fintype ι] in
/-- The difference `G − G'` for two resolvents with the same minor at `y`, both with entries
`|F_{ij} − m δ_{ij}| ≤ Z B_{ij}^{1/2}` and `|F_{yy}| ≥ 1/8`:
`|G_{ij} − G'_{ij}|² ≤ 256 Z⁴ B_{iy} B_{yj} + 4 Z² (δ_{iy} B_{yj} + δ_{jy} B_{iy})`. -/
private theorem Resample_pairDiff (G G' : Matrix ι ι ℂ) (m : ℂ) (B : ι → ι → ℝ) (y : ι) (Z : ℝ)
    (hB0' : ∀ i j, 0 ≤ B i j) (hZ1 : 1 ≤ Z)
    (hminor : ∀ a b, greenMinor G' y a b = greenMinor G y a b)
    (hGyy : 1 / 8 ≤ ‖G y y‖) (hGy8 : 1 / 8 ≤ ‖G' y y‖)
    (hGZ : ∀ i j, ‖entryErr G m i j‖ ≤ Z * Real.sqrt (B i j))
    (hG' : ∀ i j, ‖entryErr G' m i j‖ ≤ Z * Real.sqrt (B i j)) (i j : ι) :
    ‖G i j - G' i j‖ ^ 2 ≤ 256 * Z ^ 4 * (B i y * B y j) +
      4 * Z ^ 2 * ((if i = y then B y j else 0) + (if j = y then B i y else 0)) := by
  have hite : ∀ (p : Prop) [Decidable p] (x : ℝ), 0 ≤ x → 0 ≤ (if p then x else 0) := by
    intro p _ x hx; split_ifs <;> linarith
  have hP : 0 ≤ 256 * Z ^ 4 * (B i y * B y j) := by
    have := hB0' i y; have := hB0' y j; positivity
  by_cases hij : i = y ∨ j = y
  · have e : G i j - G' i j = entryErr G m i j - entryErr G' m i j := by
      unfold entryErr; ring
    have h1 : ‖G i j - G' i j‖ ≤ 2 * Z * Real.sqrt (B i j) := by
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have := hGZ i j
      have := hG' i j
      linarith
    have h2 : ‖G i j - G' i j‖ ^ 2 ≤ 4 * Z ^ 2 * B i j := by
      have := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rwa [mul_pow, mul_pow, Real.sq_sqrt (hB0' i j), show (2 : ℝ) ^ 2 = 4 by norm_num] at this
    refine h2.trans ?_
    have hZ2 : 0 ≤ 4 * Z ^ 2 := by positivity
    rcases hij with hi | hj
    · subst hi
      have : B i j ≤ (if i = i then B i j else 0) + (if j = i then B i i else 0) := by
        rw [ite_eq_left rfl]; have := hite (j = i) (B i i) (hB0' i i); linarith
      have := mul_le_mul_of_nonneg_left this hZ2
      linarith
    · subst hj
      have : B i j ≤ (if i = j then B j j else 0) + (if j = j then B i j else 0) := by
        rw [ite_eq_left rfl]; have := hite (i = j) (B j j) (hB0' j j); linarith
      have := mul_le_mul_of_nonneg_left this hZ2
      linarith
  · obtain ⟨hi, hj⟩ := not_or.1 hij
    rw [ite_eq_right hi, ite_eq_right hj, add_zero, mul_zero, add_zero]
    have e : G i j - G' i j = G i y * G y j / G y y - G' i y * G' y j / G' y y := by
      have h1 := green_eq_greenMinor_add G y i j
      have h2 := green_eq_greenMinor_add G' y i j
      rw [hminor] at h2
      rw [h1, h2]; ring
    have hb : ∀ (F : Matrix ι ι ℂ), 1 / 8 ≤ ‖F y y‖ →
        (∀ i j, ‖entryErr F m i j‖ ≤ Z * Real.sqrt (B i j)) →
        ‖F i y * F y j / F y y‖ ≤ 8 * Z ^ 2 * (Real.sqrt (B i y) * Real.sqrt (B y j)) := by
      intro F hF8 hFe
      have hiy : ‖F i y‖ ≤ Z * Real.sqrt (B i y) := by
        have h := hFe i y; rwa [entryErr, ite_eq_right hi, sub_zero] at h
      have hyj : ‖F y j‖ ≤ Z * Real.sqrt (B y j) := by
        have h := hFe y j; rwa [entryErr, ite_eq_right (Ne.symm hj), sub_zero] at h
      rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
      have hm' := mul_le_mul hiy hyj (norm_nonneg _) (by positivity)
      have h0 : 0 ≤ Z * Real.sqrt (B i y) * (Z * Real.sqrt (B y j)) := by positivity
      have h8 : 1 ≤ 8 * ‖F y y‖ := by linarith
      calc ‖F i y‖ * ‖F y j‖ ≤ Z * Real.sqrt (B i y) * (Z * Real.sqrt (B y j)) := hm'
        _ = 1 * (Z * Real.sqrt (B i y) * (Z * Real.sqrt (B y j))) := (one_mul _).symm
        _ ≤ (8 * ‖F y y‖) * (Z * Real.sqrt (B i y) * (Z * Real.sqrt (B y j))) :=
            mul_le_mul_of_nonneg_right h8 h0
        _ = _ := by ring
    have h1 : ‖G i j - G' i j‖ ≤ 16 * Z ^ 2 * (Real.sqrt (B i y) * Real.sqrt (B y j)) := by
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have := hb G hGyy hGZ
      have := hb G' hGy8 hG'
      linarith
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖G i j - G' i j‖ ^ 2 ≤ (16 * Z ^ 2 * (Real.sqrt (B i y) * Real.sqrt (B y j))) ^ 2 :=
          this
      _ = 256 * Z ^ 4 * (B i y * B y j) := by
          have e2 : (Real.sqrt (B i y) * Real.sqrt (B y j)) ^ 2 = B i y * B y j := by
            rw [mul_pow, Real.sq_sqrt (hB0' i y), Real.sq_sqrt (hB0' y j)]
          rw [mul_pow, e2]; ring

/-- The weighted sum of the differences: `Σ_{ij} s_{ai} |G_{ij} − G'_{ij}|² s_{jb} ≤
(256 C_c² + 8 C_s C_c) Z⁴ B_{ay} B_{yb}`. -/
private theorem Resample_pairN (S : Matrix ι ι ℝ) (B : ι → ι → ℝ) (G G' : Matrix ι ι ℂ) (y : ι)
    (Z Cs Cc : ℝ) (hS0 : ∀ i k, 0 ≤ S i k) (hSs : ∀ i k, S i k = S k i)
    (hB0' : ∀ i j, 0 ≤ B i j) (hBs : ∀ i j, B i j = B j i) (hSB : ∀ i j, S i j ≤ Cs * B i j)
    (hconv : ∀ x z, ∑ α, S x α * B α z ≤ Cc * B x z) (hCs : 0 ≤ Cs) (hCc : 0 ≤ Cc)
    (hZ1 : 1 ≤ Z)
    (hdiff : ∀ i j, ‖G i j - G' i j‖ ^ 2 ≤ 256 * Z ^ 4 * (B i y * B y j) +
      4 * Z ^ 2 * ((if i = y then B y j else 0) + (if j = y then B i y else 0))) (a b : ι) :
    ∑ i, ∑ j, S a i * ‖G i j - G' i j‖ ^ 2 * S j b ≤
      (256 * Cc ^ 2 + 8 * Cs * Cc) * Z ^ 4 * (B a y * B y b) := by
  have hconv' : ∀ x, ∑ j, B y j * S j x ≤ Cc * B y x := by
    intro x
    calc ∑ j, B y j * S j x = ∑ j, S x j * B j y :=
          Finset.sum_congr rfl fun j _ => by rw [hSs j x, hBs y j]; ring
      _ ≤ Cc * B x y := hconv x y
      _ = Cc * B y x := by rw [hBs]
  calc ∑ i, ∑ j, S a i * ‖G i j - G' i j‖ ^ 2 * S j b
      ≤ ∑ i, ∑ j, S a i * (256 * Z ^ 4 * (B i y * B y j) +
          4 * Z ^ 2 * ((if i = y then B y j else 0) + (if j = y then B i y else 0))) * S j b :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdiff i j) (hS0 a i)) (hS0 j b)
    _ = 256 * Z ^ 4 * ((∑ i, S a i * B i y) * (∑ j, B y j * S j b)) +
          4 * Z ^ 2 * (S a y * (∑ j, B y j * S j b) + (∑ i, S a i * B i y) * S y b) := by
        have e1 : ∀ i j, S a i * (256 * Z ^ 4 * (B i y * B y j) +
            4 * Z ^ 2 * ((if i = y then B y j else 0) + (if j = y then B i y else 0))) * S j b =
            256 * Z ^ 4 * ((S a i * B i y) * (B y j * S j b)) +
            4 * Z ^ 2 * (if i = y then S a i * (B y j * S j b) else 0) +
              4 * Z ^ 2 * (if j = y then (S a i * B i y) * S j b else 0) := by
          intro i j; split_ifs <;> ring
        have h1 : ∑ i, ∑ j, S a i * B i y * (B y j * S j b) =
            (∑ i, S a i * B i y) * ∑ j, B y j * S j b := by rw [Finset.sum_mul_sum]
        have h2 : ∑ i, ∑ j, (if i = y then S a i * (B y j * S j b) else 0) =
            S a y * ∑ j, B y j * S j b := by
          rw [Finset.sum_eq_single y (fun i _ hi => by simp [hi]) (by simp), Finset.mul_sum]
          simp
        have h3 : ∑ i, ∑ j, (if j = y then S a i * B i y * S j b else 0) =
            (∑ i, S a i * B i y) * S y b := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp
        have h1' : ∑ i, ∑ j, 256 * Z ^ 4 * (S a i * B i y * (B y j * S j b)) =
            256 * Z ^ 4 * ((∑ i, S a i * B i y) * ∑ j, B y j * S j b) := by
          rw [← h1]; simp_rw [Finset.mul_sum]
        have h2' : ∑ i, ∑ j, 4 * Z ^ 2 * (if i = y then S a i * (B y j * S j b) else 0) =
            4 * Z ^ 2 * (S a y * ∑ j, B y j * S j b) := by
          simp_rw [← Finset.mul_sum]; rw [h2]
        have h3' : ∑ i, ∑ j, 4 * Z ^ 2 * (if j = y then S a i * B i y * S j b else 0) =
            4 * Z ^ 2 * ((∑ i, S a i * B i y) * S y b) := by
          simp_rw [← Finset.mul_sum]; rw [h3]
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e1 i j]
        simp only [Finset.sum_add_distrib]
        rw [h1', h2', h3']
        ring
    _ ≤ 256 * Z ^ 4 * ((Cc * B a y) * (Cc * B y b)) +
          4 * Z ^ 2 * ((Cs * B a y) * (Cc * B y b) + (Cc * B a y) * (Cs * B y b)) := by
        have h1 := hconv a y
        have h2 := hconv' b
        have h3 := hSB a y
        have h4 := hSB y b
        have p1 : 0 ≤ ∑ i, S a i * B i y :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hS0 a i) (hB0' i y)
        have p2 : 0 ≤ ∑ j, B y j * S j b :=
          Finset.sum_nonneg fun j _ => mul_nonneg (hB0' y j) (hS0 j b)
        have := hS0 a y
        have := hS0 y b
        have := hB0' a y
        have := hB0' y b
        gcongr
    _ ≤ (256 * Cc ^ 2 + 8 * Cs * Cc) * Z ^ 4 * (B a y * B y b) := by
        have hZ24 : Z ^ 2 ≤ Z ^ 4 := pow_le_pow_right₀ hZ1 (by norm_num)
        have hp : 0 ≤ B a y * B y b := mul_nonneg (hB0' a y) (hB0' y b)
        have hq : 0 ≤ 2 * Cs * Cc * (B a y * B y b) := by positivity
        have e : (Cs * B a y) * (Cc * B y b) + (Cc * B a y) * (Cs * B y b) =
            2 * Cs * Cc * (B a y * B y b) := by ring
        rw [e]
        have h5 : 4 * Z ^ 2 * (2 * Cs * Cc * (B a y * B y b)) ≤
            4 * Z ^ 4 * (2 * Cs * Cc * (B a y * B y b)) :=
          mul_le_mul_of_nonneg_right (by linarith) hq
        have e2 : 256 * Z ^ 4 * ((Cc * B a y) * (Cc * B y b)) + 4 * Z ^ 4 *
            (2 * Cs * Cc * (B a y * B y b)) =
            (256 * Cc ^ 2 + 8 * Cs * Cc) * Z ^ 4 * (B a y * B y b) := by ring
        linarith

omit [DecidableEq ι] in
/-- `|D^s_{ab}(G) − D^s_{ab}(G')| ≤ (A + 3 c K_N Z⁴) (B_{ay}^{1/2} + B_{yb}^{1/2}) B_{ab}` from
`D^s_{ab}(G) ≤ A B_{ab}`, the bound `N_{ab} ≤ K_N Z⁴ B_{ay} B_{yb}` on the weighted sum of the
differences, and the product bound on `B`. -/
private theorem Resample_pairD (S : Matrix ι ι ℝ) (B : ι → ι → ℝ) (G G' : Matrix ι ι ℂ) (y a b : ι)
    (r c KN Z A : ℝ) (hS0 : ∀ i k, 0 ≤ S i k) (hB0 : ∀ i j, 0 < B i j)
    (hBw : ∀ i j, B i j ≤ r ^ 2) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hc : 0 ≤ c) (hKN : 0 ≤ KN)
    (hBp : B a y * B y b ≤ c * B a b * (B a y + B y b))
    (hD : ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b ≤ A * B a b)
    (hN : ∑ i, ∑ j, S a i * ‖G i j - G' i j‖ ^ 2 * S j b ≤ KN * Z ^ 4 * (B a y * B y b)) :
    |∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b - ∑ i, ∑ j, S a i * ‖G' i j‖ ^ 2 * S j b| ≤
      (A + 3 * c * KN * Z ^ 4) * (Real.sqrt (B a y) + Real.sqrt (B y b)) * B a b := by
  have hB0' : ∀ i j, 0 ≤ B i j := fun i j => (hB0 i j).le
  set ρ := Real.sqrt (B a y) + Real.sqrt (B y b) with hρ
  have hρ0 : 0 < ρ := by
    have := Real.sqrt_pos.2 (hB0 a y); have := Real.sqrt_nonneg (B y b); linarith
  have hρ2 : ρ ≤ 2 := by
    have h1 : Real.sqrt (B a y) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact (hBw a y).trans (by nlinarith)
    have h2 : Real.sqrt (B y b) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact (hBw y b).trans (by nlinarith)
    linarith
  have hsumB : B a y + B y b ≤ ρ ^ 2 := by
    rw [hρ, add_sq, Real.sq_sqrt (hB0' a y), Real.sq_sqrt (hB0' y b)]
    have := Real.sqrt_nonneg (B a y); have := Real.sqrt_nonneg (B y b)
    nlinarith
  have hpt : ∀ i j, |S a i * ‖G i j‖ ^ 2 * S j b - S a i * ‖G' i j‖ ^ 2 * S j b| ≤
      ρ * (S a i * ‖G i j‖ ^ 2 * S j b) + (1 + 1 / ρ) * (S a i * ‖G i j - G' i j‖ ^ 2 * S j b) := by
    intro i j
    have h := Resample_sq_diff (G i j) (G' i j) hρ0
    have hw : 0 ≤ S a i * S j b := mul_nonneg (hS0 a i) (hS0 j b)
    have e : S a i * ‖G i j‖ ^ 2 * S j b - S a i * ‖G' i j‖ ^ 2 * S j b =
        (S a i * S j b) * (‖G i j‖ ^ 2 - ‖G' i j‖ ^ 2) := by ring
    rw [e, abs_mul, abs_of_nonneg hw]
    calc S a i * S j b * |‖G i j‖ ^ 2 - ‖G' i j‖ ^ 2|
        ≤ S a i * S j b * (ρ * ‖G i j‖ ^ 2 + (1 + 1 / ρ) * ‖G i j - G' i j‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hw
      _ = _ := by ring
  have hsum : |∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b - ∑ i, ∑ j, S a i * ‖G' i j‖ ^ 2 * S j b| ≤
      ρ * ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b +
        (1 + 1 / ρ) * ∑ i, ∑ j, S a i * ‖G i j - G' i j‖ ^ 2 * S j b := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hpt i j
  refine hsum.trans ?_
  have hD' := hD
  have hBab := hB0' a b
  have hprod := hBp
  have hN' := hN
  have hZ4 : 0 ≤ Z ^ 4 := by positivity
  have hKN0 : 0 ≤ KN := by positivity
  -- `(1 + 1/ρ) N ≤ 3 c K_N Z⁴ ρ B_{ab}`
  have hNb : (1 + 1 / ρ) * ∑ i, ∑ j, S a i * ‖G i j - G' i j‖ ^ 2 * S j b ≤
      3 * c * KN * Z ^ 4 * ρ * B a b := by
    have h1 : ∑ i, ∑ j, S a i * ‖G i j - G' i j‖ ^ 2 * S j b ≤
        KN * Z ^ 4 * (c * B a b * ρ ^ 2) := by
      refine hN.trans (mul_le_mul_of_nonneg_left (hprod.trans ?_) (by positivity))
      exact mul_le_mul_of_nonneg_left hsumB (by positivity)
    have h2 : (1 + 1 / ρ) * ρ ^ 2 ≤ 3 * ρ := by
      have e : (1 + 1 / ρ) * ρ ^ 2 = ρ ^ 2 + ρ := by field_simp
      rw [e]; nlinarith
    have h1ρ : 0 ≤ 1 + 1 / ρ := by positivity
    calc (1 + 1 / ρ) * ∑ i, ∑ j, S a i * ‖G i j - G' i j‖ ^ 2 * S j b
        ≤ (1 + 1 / ρ) * (KN * Z ^ 4 * (c * B a b * ρ ^ 2)) := mul_le_mul_of_nonneg_left h1 h1ρ
      _ = (KN * Z ^ 4 * c * B a b) * ((1 + 1 / ρ) * ρ ^ 2) := by ring
      _ ≤ (KN * Z ^ 4 * c * B a b) * (3 * ρ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3 * c * KN * Z ^ 4 * ρ * B a b := by ring
  have hDb : ρ * ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b ≤ A * ρ * B a b := by
    calc ρ * ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b ≤ ρ * (A * B a b) :=
          mul_le_mul_of_nonneg_left hD' hρ0.le
      _ = A * ρ * B a b := by ring
  calc ρ * ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b +
        (1 + 1 / ρ) * ∑ i, ∑ j, S a i * ‖G i j - G' i j‖ ^ 2 * S j b
      ≤ A * ρ * B a b + 3 * c * KN * Z ^ 4 * ρ * B a b := add_le_add hDb hNb
    _ = (A + 3 * c * KN * Z ^ 4) * ρ * B a b := by ring


/-- **The deterministic part of the pair event**. For `H` with
`|G_{ij} − m δ_{ij}| ≤ Y B_{ij}^{1/2}` and `D^s_{ab} ≤ A B_{ab}`, and `H'` with the same minor at
`y` satisfying the large deviation bounds at row `y` with factor `τ²`: with `Y₁ = (1 + ĉ) Y` and
`Z = C_Y τ Y₁`, `|G'_{ij} − m δ_{ij}| ≤ Z B_{ij}^{1/2}` for all `i, j`, and
`|D^s_{ab}(G) − D^s_{ab}(G')| ≤ (A + 3 c (256 C_c² + 8 C_s C_c) Z⁴)
(B_{ay}^{1/2} + B_{yb}^{1/2}) B_{ab}` for all `a, b`. -/
private theorem Resample_pairDet (H H' : Matrix ι ι ℂ) (z m : ℂ) (S : Matrix ι ι ℝ)
    (B : ι → ι → ℝ) (y : ι) (Y r τ ĉ c Cs Cc A : ℝ) (hH' : H'.IsHermitian)
    (hz : 0 < z.im) (hm : m * (m + z) = -1) (hm4 : 1 / 4 ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1)
    (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k = 1) (hSs : ∀ i k, S i k = S k i)
    (hB0 : ∀ i j, 0 < B i j) (hBs : ∀ i j, B i j = B j i) (hBw : ∀ i j, B i j ≤ r ^ 2)
    (hBd : ∀ i, B i i = r ^ 2) (hSB : ∀ i j, S i j ≤ Cs * B i j)
    (hconv : ∀ x z, ∑ α, S x α * B α z ≤ Cc * B x z) (hCs : 0 ≤ Cs) (hCc : 0 ≤ Cc)
    (hĉ : 0 ≤ ĉ) (hc : 0 ≤ c)
    (hBp' : ∀ k y l, Real.sqrt (B k y) * Real.sqrt (B y l) ≤ ĉ * r * Real.sqrt (B k l))
    (hBp : ∀ k y l, B k y * B y l ≤ c * B k l * (B k y + B y l))
    (hY : 1 ≤ Y) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hτ : 1 ≤ τ) (hYr : Y * r ≤ 1 / 8)
    (hsm : (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) * τ * ((1 + ĉ) * Y) * r ≤ 1 / 16)
    (hminor : ∀ a b, greenMinor (green H' z) y a b = greenMinor (green H z) y a b)
    (hG : ∀ i j, ‖entryErr (green H z) m i j‖ ≤ Y * Real.sqrt (B i j))
    (hD : ∀ a b, ∑ i, ∑ j, S a i * ‖green H z i j‖ ^ 2 * S j b ≤ A * B a b)
    (hR : ∀ j, ldeRowLHS H' (green H' z) y j ≤ τ ^ 2 * ldeRowRHS S (green H' z) y j)
    (hC : ∀ j, ldeColLHS H' (green H' z) y j ≤ τ ^ 2 * ldeColRHS S (green H' z) y j)
    (hQ : ldeQuadLHS H' (green H' z) S y ≤ τ ^ 2 * ldeQuadRHS S (green H' z) y)
    (hd : ‖H' y y‖ ^ 2 ≤ τ ^ 2 * S y y) :
    (∀ i j, ‖entryErr (green H' z) m i j‖ ≤
      (2 * (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) + 2 * (2 * (Cs + Cc) + 1) + 1 +
        2 * (2 * (Cs + Cc) + 1) ^ 2 * ĉ) * τ * ((1 + ĉ) * Y) * Real.sqrt (B i j)) ∧
    ∀ a b, |∑ i, ∑ j, S a i * ‖green H z i j‖ ^ 2 * S j b -
        ∑ i, ∑ j, S a i * ‖green H' z i j‖ ^ 2 * S j b| ≤
      (A + 3 * c * (256 * Cc ^ 2 + 8 * Cs * Cc) *
        ((2 * (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) + 2 * (2 * (Cs + Cc) + 1) + 1 +
          2 * (2 * (Cs + Cc) + 1) ^ 2 * ĉ) * τ * ((1 + ĉ) * Y)) ^ 4) *
        (Real.sqrt (B a y) + Real.sqrt (B y b)) * B a b := by
  obtain ⟨hGyy, hGy8, hYZ, hG'⟩ := Resample_pairEntries H H' z m S B y Y r τ ĉ Cs Cc hH' hz hm
    hm4 hm1 hS0 hS1 hSs hB0 hBs hBw hBd hSB hconv hCs hCc hĉ hBp' hY hr hr1 hτ hYr hsm hminor hG
    hR hC hQ hd
  set Z := (2 * (2 * Cs + 2 * (Cs + Cc ^ 2) + 3) + 2 * (2 * (Cs + Cc) + 1) + 1 +
    2 * (2 * (Cs + Cc) + 1) ^ 2 * ĉ) * τ * ((1 + ĉ) * Y) with hZ
  have hB0' : ∀ i j, 0 ≤ B i j := fun i j => (hB0 i j).le
  have hZ1 : 1 ≤ Z := hY.trans hYZ
  have hGZ : ∀ i j, ‖entryErr (green H z) m i j‖ ≤ Z * Real.sqrt (B i j) := fun i j =>
    (hG i j).trans (mul_le_mul_of_nonneg_right hYZ (Real.sqrt_nonneg _))
  refine ⟨hG', fun a b => ?_⟩
  have hdiff := Resample_pairDiff (green H z) (green H' z) m B y Z hB0' hZ1 hminor hGyy hGy8 hGZ hG'
  have hN := Resample_pairN S B (green H z) (green H' z) y Z Cs Cc hS0 hSs hB0' hBs hSB hconv hCs
    hCc hZ1 hdiff a b
  have h := Resample_pairD S B (green H z) (green H' z) y a b r c (256 * Cc ^ 2 + 8 * Cs * Cc) Z A
    hS0 hB0 hBw hr hr1 hc (by positivity) (hBp a y b) (hD a b) hN
  exact h.trans_eq (by ring)
end Pair

/-! ## The large deviation event and its probability -/

section Prob

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `|G^{(x)}_{ab}| ≤ (Im z)^{−1}`. -/
private theorem Resample_norm_greenMinor_le {z : ℂ} (hz : 0 < z.im) (ω : Sample ι) (x a b : ι) :
    ‖greenMinor (green (hmat ω) z) x a b‖ ≤ (z.im)⁻¹ := by
  have hH := hmat_isHermitian ω
  by_cases hab : a = x ∨ b = x
  · have hne := green_diag_ne_zero hH hz x
    have : greenMinor (green (hmat ω) z) x a b = 0 := by
      rcases hab with rfl | rfl <;> (unfold greenMinor; field_simp; ring)
    rw [this, norm_zero]; positivity
  · obtain ⟨ha, hb⟩ := not_or.mp hab
    rw [← minorGreen_eq_greenMinor (green (hmat ω) z) x ⟨a, ha⟩ ⟨b, hb⟩,
      ← inv_minor_resolvent hH hz x]
    have h : ‖green ((hmat ω).submatrix (Subtype.val : {c // c ≠ x} → ι) Subtype.val) z
        ⟨a, ha⟩ ⟨b, hb⟩‖ ≤ |z.im|⁻¹ := norm_green_entry_le (hH.submatrix _) hz.ne' _ _
    rw [abs_of_pos hz] at h
    exact h

/-- **The large deviation event** ([I, Lemma 5.1] with factor `t`): for every `p` there is `C`
such that the row, column, quadratic and diagonal bounds with factor `t` fail with probability at
most `4 |ι|² C t^{−p}`, uniformly in `S` symmetric and `≥ 0` and in `z ∈ ℂ₊`. -/
private theorem Resample_lde_prob (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ), S.IsSymm → (∀ a b, 0 ≤ S a b) → ∀ (z : ℂ), 0 < z.im →
    ∀ t : ℝ, 0 < t →
      gaussLaw S {ω | ¬ Resample_LDE (hmat ω) (green (hmat ω) z) S t} ≤
        ENNReal.ofReal (4 * (Fintype.card ι : ℝ) ^ 2 * (C / t ^ p)) := by
  obtain ⟨C₁, hC₁0, h₁⟩ := QTerm_lde_prob p
  obtain ⟨C₂, h₂⟩ := ldeQuadTail p
  obtain ⟨C₃, h₃⟩ := ldeDiagTail p
  refine ⟨C₁ + |C₂| + |C₃|, by positivity, fun {ι} _ _ S hS hS0 z hz t ht => ?_⟩
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNN : N ≤ N ^ 2 := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · rw [hN, h]; simp
    · have : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast h
      nlinarith
  have htp : 0 < t ^ p := pow_pos ht p
  -- the quadratic form at one row
  have hq : ∀ x, gaussLaw S {ω | ¬ ldeQuadLHS (hmat ω) (green (hmat ω) z) S x ≤
      t * ldeQuadRHS S (green (hmat ω) z) x} ≤ ENNReal.ofReal (|C₂| / t ^ p) := by
    intro x
    have h := h₂ S hS hS0 x (fun ω k l => greenMinor (green (hmat ω) z) x k.1 l.1)
      (fun k l => (polyMeas_greenMinor z hz x k.1 l.1).1)
      (fun k l => Graphs.freeOf_greenMinor z hz x k.1 l.1)
      ⟨(z.im)⁻¹, fun ω k l => Resample_norm_greenMinor_le hz ω x k.1 l.1⟩ t ht
    refine le_trans (measure_mono fun ω hω => ?_) (h.trans (ENNReal.ofReal_le_ofReal ?_))
    · simp only [Set.mem_ofPred_eq, not_le, ldeQuadLHS, ldeQuadRHS] at hω ⊢
      exact hω
    · exact div_le_div_of_nonneg_right (le_abs_self _) htp.le
  have hd : ∀ x, gaussLaw S {ω | ¬ ‖hmat ω x x‖ ^ 2 ≤ t * S x x} ≤
      ENNReal.ofReal (|C₃| / t ^ p) := by
    intro x
    refine le_trans (measure_mono fun ω hω => ?_) ((h₃ S hS0 x t ht).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_abs_self _) htp.le)))
    simp only [Set.mem_ofPred_eq, not_le] at hω ⊢
    exact hω
  have hsub : {ω : Sample ι | ¬ Resample_LDE (hmat ω) (green (hmat ω) z) S t} ⊆
      {ω | ¬ (LDERow (hmat ω) (green (hmat ω) z) S t ∧ LDECol (hmat ω) (green (hmat ω) z) S t)} ∪
      ((⋃ x : ι, {ω | ¬ ldeQuadLHS (hmat ω) (green (hmat ω) z) S x ≤
          t * ldeQuadRHS S (green (hmat ω) z) x}) ∪
        ⋃ x : ι, {ω | ¬ ‖hmat ω x x‖ ^ 2 ≤ t * S x x}) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Resample_LDE, LDEQuad] at hω
    by_cases h1 : LDERow (hmat ω) (green (hmat ω) z) S t ∧ LDECol (hmat ω) (green (hmat ω) z) S t
    · right
      by_cases h2 : ∀ i, ldeQuadLHS (hmat ω) (green (hmat ω) z) S i ≤
          t * ldeQuadRHS S (green (hmat ω) z) i
      · right
        have h3 : ¬ ∀ i, ‖hmat ω i i‖ ^ 2 ≤ t * S i i := fun h3 => hω ⟨h1.1, h1.2, h2, h3⟩
        push Not at h3
        obtain ⟨x, hx⟩ := h3
        exact Set.mem_iUnion.2 ⟨x, by simp only [Set.mem_ofPred_eq, not_le]; exact hx⟩
      · left
        push Not at h2
        obtain ⟨x, hx⟩ := h2
        exact Set.mem_iUnion.2 ⟨x, by simp only [Set.mem_ofPred_eq, not_le]; exact hx⟩
    · left; exact h1
  have hrc := h₁ S hS hS0 z hz t ht
  calc gaussLaw S {ω | ¬ Resample_LDE (hmat ω) (green (hmat ω) z) S t}
      ≤ ENNReal.ofReal (2 * N ^ 2 * (C₁ / t ^ p)) +
          ((∑ _x : ι, ENNReal.ofReal (|C₂| / t ^ p)) +
            ∑ _x : ι, ENNReal.ofReal (|C₃| / t ^ p)) := by
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hrc
          ((measure_union_le _ _).trans (add_le_add ?_ ?_))))
        · exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun x _ => hq x)
        · exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun x _ => hd x)
    _ = ENNReal.ofReal (2 * N ^ 2 * (C₁ / t ^ p) + (N * (|C₂| / t ^ p) + N * (|C₃| / t ^ p))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul,
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul hN0, ENNReal.ofReal_mul hN0, hN, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (4 * N ^ 2 * ((C₁ + |C₂| + |C₃|) / t ^ p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have a1 : 0 ≤ C₁ / t ^ p := by positivity
        have a2 : 0 ≤ |C₂| / t ^ p := by positivity
        have a3 : 0 ≤ |C₃| / t ^ p := by positivity
        have e : (C₁ + |C₂| + |C₃|) / t ^ p = C₁ / t ^ p + |C₂| / t ^ p + |C₃| / t ^ p := by
          rw [add_div, add_div]
        rw [e]
        have b2 : N * (|C₂| / t ^ p) ≤ N ^ 2 * (|C₂| / t ^ p) := mul_le_mul_of_nonneg_right hNN a2
        have b3 : N * (|C₃| / t ^ p) ≤ N ^ 2 * (|C₃| / t ^ p) := mul_le_mul_of_nonneg_right hNN a3
        have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
        nlinarith [mul_nonneg hN2 a1, mul_nonneg hN2 a2, mul_nonneg hN2 a3]

/-- `(ω, η) ↦ A.piecewise η ω` is measurable. -/
private theorem Resample_measurable_piecewise (A : Finset (Coord ι)) :
    Measurable fun p : Sample ι × Sample ι => A.piecewise p.2 p.1 := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ A
  · simp only [Finset.piecewise_eq_of_mem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_snd
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_fst

/-- Overwriting a sample on `A` by an independent copy has again the law of the sample. -/
private theorem Resample_measurePreserving (S : Matrix ι ι ℝ) (A : Finset (Coord ι)) :
    MeasurePreserving (fun p : Sample ι × Sample ι => A.piecewise p.2 p.1)
      ((gaussLaw S).prod (gaussLaw S)) (gaussLaw S) := by
  refine ⟨Resample_measurable_piecewise A, ?_⟩
  unfold gaussLaw
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (Resample_measurable_piecewise A) (MeasurableSet.univ_pi hs)]
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

/-- Under the law of `(ω, η)`, the events `ω ∈ E` and `resampleRow y η ω ∈ E` each have probability
at most `P(E)`, for any set `E`. -/
private theorem Resample_pair_le (S : Matrix ι ι ℝ) (y : ι) (E : Set (Sample ι)) :
    ((gaussLaw S).prod (gaussLaw S)) {q | q.1 ∈ E} ≤ gaussLaw S E ∧
    ((gaussLaw S).prod (gaussLaw S)) {q | resampleRow y q.2 q.1 ∈ E} ≤ gaussLaw S E := by
  have := isProbabilityMeasure_gaussLaw S
  constructor
  · have h := Measure.le_map_apply (μ := (gaussLaw S).prod (gaussLaw S))
      measurable_fst.aemeasurable E
    rw [Measure.map_fst_prod, measure_univ, one_smul] at h
    exact h
  · have hmp := Resample_measurePreserving S (rowCoords y)
    have h := Measure.le_map_apply (μ := (gaussLaw S).prod (gaussLaw S))
      hmp.measurable.aemeasurable E
    rw [hmp.map_eq] at h
    exact h

end Prob

/-! ## The limit `W → ∞` inside `adm(c₀, c₁)` -/

section Asymp

/-- Eventually along `admFilterL c₀ c₁`, `(W, L) ∈ adm(c₀, c₁)`. -/
private theorem Resample_ev_adm (c₀ c₁ : ℝ) : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ := by
  have h : ∀ᶠ q in admFilter c₀ c₁, q ∈ adm c₀ c₁ :=
    inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _)
  exact tendsto_comap.eventually h

/-- Eventually along `admFilterL c₀ c₁`, `W ≥ M`. -/
private theorem Resample_ev_W (c₀ c₁ M : ℝ) : ∀ᶠ p in admFilterL c₀ c₁, M ≤ (p.1.1 : ℝ) :=
  (tendsto_sizeW_admFilterL c₀ c₁).eventually (eventually_ge_atTop M)

/-- Eventually along `admFilterL c₀ c₁`, `C W^a ≤ W^b` for `a < b`. -/
private theorem Resample_ev_pow (c₀ c₁ C a b : ℝ) (h : a < b) :
    ∀ᶠ p in admFilterL c₀ c₁, C * (p.1.1 : ℝ) ^ a ≤ (p.1.1 : ℝ) ^ b := by
  have ht : Tendsto (fun p : SizeL => sizeW p ^ (b - a)) (admFilterL c₀ c₁) atTop :=
    (tendsto_rpow_atTop (sub_pos.2 h)).comp (tendsto_sizeW_admFilterL c₀ c₁)
  filter_upwards [ht.eventually (eventually_ge_atTop C), Resample_ev_W c₀ c₁ 1] with p h1 h2
  have hW : (0 : ℝ) < p.1.1 := by linarith
  have e : (p.1.1 : ℝ) ^ b = (p.1.1 : ℝ) ^ (b - a) * (p.1.1 : ℝ) ^ a := by
    rw [← Real.rpow_add hW]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hW.le _)

/-- The probability bound: for `p g ≥ D_m + 2d/c₁ + 1` and `t = W^g`,
`k |Z_L^d|² C t^{−p} ≤ W^{−D_m}` eventually along `admFilterL c₀ c₁`. -/
private theorem Resample_prob_num (d : ℕ) (c₀ c₁ : ℝ) (hc₁ : 0 < c₁) (g Dm C k : ℝ) (p : ℕ)
    (hp : Dm + 2 * (d / c₁) + 1 ≤ p * g) (hC : 0 ≤ C) (hk : 0 ≤ k) :
    ∀ᶠ q in admFilterL c₀ c₁, k * (Fintype.card (Zd d q.1.2) : ℝ) ^ 2 *
      (C / ((q.1.1 : ℝ) ^ g) ^ p) ≤ (q.1.1 : ℝ) ^ (-Dm) := by
  filter_upwards [Resample_ev_adm c₀ c₁, Resample_ev_W c₀ c₁ (max 1 (k * C))] with q hq hW
  have hW1 : (1 : ℝ) ≤ q.1.1 := (le_max_left _ _).trans hW
  have hW0 : (0 : ℝ) < q.1.1 := by linarith
  set W : ℝ := (q.1.1 : ℝ)
  have hN := card_Zd_le_adm d c₀ c₁ hc₁ q hq
  have hN2 : (Fintype.card (Zd d q.1.2) : ℝ) ^ 2 ≤ W ^ (2 * (d / c₁)) := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
    refine this.trans (le_of_eq ?_)
    rw [sizeW, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    congr 1; push_cast; ring
  have htp : (W ^ g) ^ p = W ^ (p * g) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  rw [htp]
  have hpos : 0 < W ^ (p * g) := Real.rpow_pos_of_pos hW0 _
  have h1 : W ^ (2 * (d / c₁)) / W ^ (p * g) ≤ W ^ (-Dm - 1) := by
    rw [← Real.rpow_sub hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have h2 : W ^ (-Dm - 1) = W ^ (-Dm) / W := by
    rw [Real.rpow_sub hW0, Real.rpow_one]
  have hkC : k * C ≤ W := (le_max_right _ _).trans hW
  calc k * (Fintype.card (Zd d q.1.2) : ℝ) ^ 2 * (C / W ^ (p * g))
      ≤ k * W ^ (2 * (d / c₁)) * (C / W ^ (p * g)) := by gcongr
    _ = k * C * (W ^ (2 * (d / c₁)) / W ^ (p * g)) := by ring
    _ ≤ k * C * (W ^ (-Dm) / W) := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ W * (W ^ (-Dm) / W) := mul_le_mul_of_nonneg_right hkC (by positivity)
    _ = W ^ (-Dm) := by field_simp

/-- A natural number `p` with `p g ≥ x` for `g > 0`. -/
private theorem Resample_exists_p (g x : ℝ) (hg : 0 < g) : ∃ p : ℕ, x ≤ p * g := by
  refine ⟨⌈x / g⌉₊, ?_⟩
  have := Nat.le_ceil (x / g)
  rw [div_le_iff₀ hg] at this
  exact this

end Asymp

/-! ## The quantities `Y`, `X`, `M` and `C` -/

section Cut

variable {d L : ℕ} [NeZero L]

/-- `|G_{ij} − m δ_{ij}| ≤ Y B_{ij}^{1/2}`. -/
private theorem Resample_entry_le (W : ℕ) (hW : 1 ≤ W) (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ)
    (i j : Zd d L) : ‖entryErr G m i j‖ ≤ cutY W G m * Real.sqrt (bB d L W i j) := by
  have hB := Real.sqrt_pos.2 (Resample_bB_pos (d := d) (L := L) hW i j)
  have h1 : ‖entryErr G m i j‖ / Real.sqrt (bB d L W i j) ≤ cutY W G m := by
    unfold cutY
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i)
    exact le_ciSup (f := fun j => ‖entryErr G m i j‖ / Real.sqrt (bB d L W i j))
      (Set.finite_range _).bddAbove j
  rwa [div_le_iff₀ hB] at h1

omit [NeZero L] in
/-- `Y ≤ V` from `|G_{ij} − m δ_{ij}| ≤ V B_{ij}^{1/2}` for all `i, j`. -/
private theorem Resample_cutY_le (W : ℕ) (hW : 1 ≤ W) (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ)
    (V : ℝ) (hV : 0 ≤ V) (h : ∀ i j, ‖entryErr G m i j‖ ≤ V * Real.sqrt (bB d L W i j)) :
    cutY W G m ≤ V := by
  unfold cutY
  refine Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) hV) hV
  have hB := Real.sqrt_pos.2 (Resample_bB_pos (d := d) (L := L) hW i j)
  rw [div_le_iff₀ hB]
  exact h i j

/-- `D^s_{ab} = X_{ab} B_{ab}`. -/
private theorem Resample_cutD_eq (W : ℕ) (hW : 1 ≤ W) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) :
    cutD S G a b = cutX W S G a b * bB d L W a b := by
  unfold cutX
  rw [div_mul_cancel₀ _ (Resample_bB_pos hW a b).ne']

/-- `X_{ab} ≥ 0` for `S ≥ 0`. -/
private theorem Resample_cutX_nonneg (W : ℕ) (hW : 1 ≤ W) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS0 : ∀ i k, 0 ≤ S i k) (G : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) :
    0 ≤ cutX W S G a b := by
  unfold cutX cutD
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
    (Resample_bB_pos hW a b).le
  exact mul_nonneg (mul_nonneg (hS0 a i) (by positivity)) (hS0 j b)

/-- `C(H) > 0` implies `Y ≤ W^β` and `X_{ab} < 2 W^α` for all `a, b`, for
`l ≥ 1` and `S ≥ 0`. -/
private theorem Resample_cutC_pos (β α : ℝ) (l W : ℕ) (hl : 1 ≤ l) (hW : 1 ≤ W)
    (S : Matrix (Zd d L) (Zd d L) ℝ) (hS0 : ∀ i k, 0 ≤ S i k) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (m : ℂ) (h : 0 < cutC β α l W S G m) :
    cutY W G m ≤ (W : ℝ) ^ β ∧ ∀ a b, cutX W S G a b < 2 * (W : ℝ) ^ α := by
  unfold cutC at h
  split_ifs at h with hY
  · refine ⟨hY, fun a b => ?_⟩
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
    have hWa : 0 < (W : ℝ) ^ α := Real.rpow_pos_of_pos hW0 α
    have hM : cutM l W S G / (W : ℝ) ^ α < 2 := by
      unfold cutPhi at h
      by_contra hc
      push Not at hc
      have : min 1 (2 - cutM l W S G / (W : ℝ) ^ α) ≤ 0 := (min_le_right _ _).trans (by linarith)
      rw [max_eq_left this] at h
      exact lt_irrefl _ h
    rw [div_lt_iff₀ hWa] at hM
    have hX0 : ∀ a b, 0 ≤ 1 + cutX W S G a b := fun a b => by
      have := Resample_cutX_nonneg W hW S hS0 G a b; linarith
    have hle : (1 + cutX W S G a b) ^ l ≤ ∑ a, ∑ b, (1 + cutX W S G a b) ^ l := by
      have h1 : (1 + cutX W S G a b) ^ l ≤ ∑ b, (1 + cutX W S G a b) ^ l :=
        Finset.single_le_sum (f := fun b => (1 + cutX W S G a b) ^ l)
          (fun b _ => pow_nonneg (hX0 a b) l) (Finset.mem_univ b)
      exact h1.trans (Finset.single_le_sum (f := fun a => ∑ b, (1 + cutX W S G a b) ^ l)
        (fun a _ => Finset.sum_nonneg fun b _ => pow_nonneg (hX0 a b) l) (Finset.mem_univ a))
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
    have h2 : 1 + cutX W S G a b ≤ cutM l W S G := by
      unfold cutM
      rw [one_div]
      have := Real.rpow_le_rpow (pow_nonneg (hX0 a b) l) hle (by positivity : (0 : ℝ) ≤ (l : ℝ)⁻¹)
      rwa [Real.pow_rpow_inv_natCast (hX0 a b) (by omega)] at this
    linarith
  · exact absurd h (lt_irrefl 0)

end Cut

/-! ## The model at one size -/

section Size

/-- `(W^x)² = W^{2x}` for `W ≥ 0`. -/
private theorem Resample_rpow_sq {W : ℝ} (hW : 0 ≤ W) (x : ℝ) : (W ^ x) ^ 2 = W ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]; ring_nf

/-- The bound `B` at one size: with `r = W^{−d/2}`, `0 < B_{ij} = B_{ji} ≤ r² = B_{ii}`, the
product bound `B_{ky} B_{yl} ≤ 2^{d−2} B_{kl} (B_{ky} + B_{yl})`, and its square-root form
`B_{ky}^{1/2} B_{yl}^{1/2} ≤ (2^{d−1})^{1/2} r B_{kl}^{1/2}`. -/
private theorem Resample_Bfacts {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) :
    (∀ i j : Zd d L, 0 < bB d L W i j) ∧ (∀ i j : Zd d L, bB d L W i j = bB d L W j i) ∧
    (∀ i j : Zd d L, bB d L W i j ≤ ((W : ℝ) ^ (-(d : ℝ) / 2)) ^ 2) ∧
    (∀ i : Zd d L, bB d L W i i = ((W : ℝ) ^ (-(d : ℝ) / 2)) ^ 2) ∧
    (∀ k y l : Zd d L, bB d L W k y * bB d L W y l ≤
      2 ^ (d - 2) * bB d L W k l * (bB d L W k y + bB d L W y l)) ∧
    (∀ k y l : Zd d L, Real.sqrt (bB d L W k y) * Real.sqrt (bB d L W y l) ≤
      Real.sqrt (2 * 2 ^ (d - 2)) * (W : ℝ) ^ (-(d : ℝ) / 2) * Real.sqrt (bB d L W k l)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hr2 : ((W : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (W : ℝ) ^ (-(d : ℝ)) := by
    rw [Resample_rpow_sq hW0.le]; ring_nf
  have hle : ∀ i j : Zd d L, bB d L W i j ≤ ((W : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 := fun i j => by
    rw [hr2]; exact bB_le_rpow hd hW i j
  refine ⟨fun i j => Resample_bB_pos hW i j, fun i j => Resample_bB_symm i j, hle,
    fun i => by rw [hr2]; exact bB_self hW i, fun k y l => Resample_bB_prod hd hW k y l,
    fun k y l => ?_⟩
  set r := (W : ℝ) ^ (-(d : ℝ) / 2)
  have hr : 0 ≤ r := Real.rpow_nonneg hW0.le _
  have hB0 : ∀ i j : Zd d L, 0 ≤ bB d L W i j := fun i j => (Resample_bB_pos hW i j).le
  have h1 : bB d L W k y * bB d L W y l ≤ (2 * 2 ^ (d - 2)) * r ^ 2 * bB d L W k l := by
    refine (Resample_bB_prod hd hW k y l).trans ?_
    have := add_le_add (hle k y) (hle y l)
    have h2 : (0 : ℝ) ≤ 2 ^ (d - 2) * bB d L W k l := by have := hB0 k l; positivity
    calc 2 ^ (d - 2) * bB d L W k l * (bB d L W k y + bB d L W y l)
        ≤ 2 ^ (d - 2) * bB d L W k l * (r ^ 2 + r ^ 2) := mul_le_mul_of_nonneg_left this h2
      _ = (2 * 2 ^ (d - 2)) * r ^ 2 * bB d L W k l := by ring
  rw [← Real.sqrt_mul (hB0 k y)]
  calc Real.sqrt (bB d L W k y * bB d L W y l)
      ≤ Real.sqrt ((2 * 2 ^ (d - 2)) * r ^ 2 * bB d L W k l) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (2 * 2 ^ (d - 2)) * r * Real.sqrt (bB d L W k l) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hr]

/-- The spectral parameter: for `z ∈ 𝐃(κ, ε)` at `W ≥ 1`, `κ > 0`: `Im z > 0`, `|Re z| < 2 − κ`,
`Im z ≤ 1`, `1/4 ≤ |m(z)| ≤ 1` and `m(m + z) = −1`. -/
private theorem Resample_zfacts {κ ε : ℝ} (hκ : 0 < κ) {W L : ℕ} (hW : 1 ≤ W) (hL : L ≠ 0)
    {z : ℂ} (hz : z ∈ specDom κ ε W L) :
    0 < z.im ∧ |z.re| < 2 - κ ∧ z.im ≤ 1 ∧ 1 / 4 ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ 1 ∧
      msc z * (msc z + z) = -1 := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have him : 0 < z.im := lt_of_lt_of_le (by positivity) h2
  have hz3 : ‖z‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him] at this
    linarith
  exact ⟨him, h1, h3, norm_msc_ge_quarter z him hz3, (norm_msc_lt_one him).le, msc_mul z⟩

/-- The variance matrix at one size, eventually along `admFilterL c₀ c₁`: `S ≥ 0` symmetric with
row sums `1` and column sums `≤ 1`, `s ≤ C_s B`, `S B ≤ C_s B` ([I, (1.8)]), and the stability of
`1 − m(z)² S` with a constant `K` uniform in `z` on the strip ([I, (B.19)]). -/
private theorem Resample_setup {d : ℕ} (hd : 2 ≤ d) (P : Profile d) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) {κ : ℝ} (hκ : 0 < κ) :
    ∃ Cs K : ℝ, 0 ≤ Cs ∧ 0 ≤ K ∧ ∀ᶠ p in admFilterL c₀ c₁, 1 ≤ p.1.1 ∧
      (∀ i k, 0 ≤ Smat P.ψ p.1.1 p.1.2 i k) ∧ (∀ i, ∑ k, Smat P.ψ p.1.1 p.1.2 i k = 1) ∧
      (∀ k, ∑ i, Smat P.ψ p.1.1 p.1.2 i k ≤ 1) ∧
      (∀ i k, Smat P.ψ p.1.1 p.1.2 i k = Smat P.ψ p.1.1 p.1.2 k i) ∧
      (∀ i j, Smat P.ψ p.1.1 p.1.2 i j ≤ Cs * bB d p.1.2 p.1.1 i j) ∧
      (∀ x y, ∑ α, Smat P.ψ p.1.1 p.1.2 x α * bB d p.1.2 p.1.1 α y ≤ Cs * bB d p.1.2 p.1.1 x y) ∧
      ∀ z : ℂ, |z.re| < 2 - κ → 0 < z.im → z.im ≤ 1 →
        Stable (Smat P.ψ p.1.1 p.1.2) (msc z ^ 2) K := by
  obtain ⟨Cs, hCs, hprof⟩ := Resample_profile hd P c₀ c₁ hc₀
  obtain ⟨K, W₁, hK, hstab⟩ := stable_Smat_strip d P c₀ c₁ hc₀ hc₁ κ hκ
  obtain ⟨W₂, hsym⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₃, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  refine ⟨Cs, K, hCs, hK, ?_⟩
  filter_upwards [Resample_ev_adm c₀ c₁, Resample_ev_W c₀ c₁ (max 1 (max W₁ (max W₂ W₃)))]
    with p hp hW
  have hW1 : (1 : ℝ) ≤ p.1.1 := (le_max_left _ _).trans hW
  have hWa : W₁ ≤ p.1.1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWb : W₂ ≤ p.1.1 :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  have hWc : W₃ ≤ p.1.1 :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  have hW1' : 1 ≤ p.1.1 := by exact_mod_cast hW1
  obtain ⟨hS, hS0⟩ := hsym p.1.1 p.1.2 hp hWb
  have hD := hds p.1.1 p.1.2 hp hWc
  obtain ⟨hSB, hconv⟩ := hprof p.1.1 p.1.2 hp hW1'
  refine ⟨hW1', hS0, fun i => sum_row_of_mem_doublyStochastic hD i,
    fun k => (sum_col_of_mem_doublyStochastic hD k).le, fun i k => (hS.apply k i), hSB,
    fun x y => ?_, fun z h1 h2 h3 => hstab p.1.1 p.1.2 hp hWa z h1 h2 h3⟩
  refine le_trans (Finset.sum_le_sum fun α _ => ?_) (hconv x y)
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (Resample_bB_pos hW1' α y).le

/-- **The deterministic part of the improvement on the cutoff event at one size**: on the large deviation event with
factor `t ≥ 1`, `Y ≤ W^β` and `X_{ab} ≤ 2 W^α` give
`|G_{ij} − m δ_{ij}|² ≤ (16 + 10⁴ K²)(4 C_s + 32) t³ W^α B_{ij}`, given the side conditions on
`δ = W^β W^{−d/2}`. -/
private theorem Resample_improve_det {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W)
    (S : Matrix (Zd d L) (Zd d L) ℝ) (Cs K : ℝ) (hCs : 0 ≤ Cs) (hK : 0 ≤ K)
    (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k = 1) (hS2 : ∀ k, ∑ i, S i k ≤ 1)
    (hSs : ∀ i k, S i k = S k i) (hSB : ∀ i j, S i j ≤ Cs * bB d L W i j) (z : ℂ)
    (hz : 0 < z.im) (hm : msc z * (msc z + z) = -1) (hm4 : 1 / 4 ≤ ‖msc z‖) (hm1 : ‖msc z‖ ≤ 1)
    (hstab : Stable S (msc z ^ 2) K) (H : Matrix (Zd d L) (Zd d L) ℂ) (hH : H.IsHermitian)
    (t β α : ℝ) (hα : 0 ≤ α) (ht : 1 ≤ t) (hL : Resample_LDE H (green H z) S t)
    (hY : cutY W (green H z) (msc z) ≤ (W : ℝ) ^ β)
    (hX : ∀ a b, cutX W S (green H z) a b ≤ 2 * (W : ℝ) ^ α)
    (hδ8 : (W : ℝ) ^ β * (W : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 / 8)
    (h4 : 4 * t * ((W : ℝ) ^ β * (W : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 ≤ 1)
    (hKδ : K * ((W : ℝ) ^ β * (W : ℝ) ^ (-(d : ℝ) / 2)) ≤ 1 / 2) (i j : Zd d L) :
    ‖entryErr (green H z) (msc z) i j‖ ^ 2 ≤
      (16 + 10 ^ 4 * K ^ 2) * (4 * Cs + 32) * (t ^ 3 * (W : ℝ) ^ α) * bB d L W i j := by
  obtain ⟨hB0, hBs, hBw, hBd, -, -⟩ := Resample_Bfacts (L := L) hd hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set r := (W : ℝ) ^ (-(d : ℝ) / 2) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hW0.le _
  set δ := (W : ℝ) ^ β * r with hδ
  have hWβ : 0 ≤ (W : ℝ) ^ β := Real.rpow_nonneg hW0.le _
  have hWα : 1 ≤ (W : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast hW) hα
  have hG : GoodEvent (green H z) (msc z) δ := by
    intro x y
    refine (Resample_entry_le W hW _ _ x y).trans ?_
    have hs : Real.sqrt (bB d L W x y) ≤ r := by
      calc Real.sqrt (bB d L W x y) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt (hBw x y)
        _ = r := Real.sqrt_sq hr0
    exact mul_le_mul hY hs (Real.sqrt_nonneg _) hWβ
  have hD : ∀ a b, ∑ i, ∑ j, S a i * ‖green H z i j‖ ^ 2 * S j b ≤
      2 * (W : ℝ) ^ α * bB d L W a b := by
    intro a b
    have e := Resample_cutD_eq W hW S (green H z) a b
    unfold cutD at e
    rw [e]
    exact mul_le_mul_of_nonneg_right (hX a b) (hB0 a b).le
  have hcore := Resample_core H z (msc z) S (bB d L W) (r ^ 2) Cs K t (2 * (W : ℝ) ^ α) δ hH hz hm
    hm4 hm1 hG (by linarith) (by linarith) h4 hS0 hS1 hS2 hSs ht hL (fun i j => (hB0 i j).le) hBw
    hBd hSB hCs hstab hK hKδ (by positivity) hD i j
  refine hcore.trans ?_
  have hBij := (hB0 i j).le
  have hK0 : 0 ≤ 16 + 10 ^ 4 * K ^ 2 := by positivity
  have ht2 : t ^ 2 * (4 * Cs + 16 * t * (2 * (W : ℝ) ^ α)) ≤
      (4 * Cs + 32) * (t ^ 3 * (W : ℝ) ^ α) := by
    have h1 : t ^ 2 ≤ t ^ 3 * (W : ℝ) ^ α := by
      have : t ^ 2 ≤ t ^ 3 := pow_le_pow_right₀ ht (by norm_num)
      nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ t) 3]
    have e : t ^ 2 * (4 * Cs + 16 * t * (2 * (W : ℝ) ^ α)) =
        4 * Cs * t ^ 2 + 32 * (t ^ 3 * (W : ℝ) ^ α) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 hCs]
  calc (16 + 10 ^ 4 * K ^ 2) * t ^ 2 * (4 * Cs + 16 * t * (2 * (W : ℝ) ^ α)) * bB d L W i j
      = (16 + 10 ^ 4 * K ^ 2) * (t ^ 2 * (4 * Cs + 16 * t * (2 * (W : ℝ) ^ α))) * bB d L W i j := by
        ring
    _ ≤ (16 + 10 ^ 4 * K ^ 2) * ((4 * Cs + 32) * (t ^ 3 * (W : ℝ) ^ α)) * bB d L W i j := by
        gcongr
    _ = _ := by ring

end Size

/-! ## The improvement on the cutoff event -/

/-- `√(K t³ W^α) < W^{α/2+γ}` and `Y ≤ √(K t³ W^α)` from the entrywise bound
`|G_{ij} − m δ_{ij}|² ≤ V B_{ij}`. -/
private theorem Resample_cutY_sqrt {d L W : ℕ} [NeZero L] (hW : 1 ≤ W)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ) (V : ℝ) (hV : 0 ≤ V)
    (h : ∀ i j, ‖entryErr G m i j‖ ^ 2 ≤ V * bB d L W i j) : cutY W G m ≤ Real.sqrt V := by
  refine Resample_cutY_le W hW G m _ (Real.sqrt_nonneg _) fun i j => ?_
  rw [← Real.sqrt_mul hV, ← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (h i j)

/-- **The improvement on the cutoff event**: for `d ≥ 8`, `0 < β < d/100` and
`α, γ > 0`, uniformly in `z ∈ 𝐃(κ, ε)`, the event `Y ≤ W^β`, `max_{ab} X_{ab} ≤ 2 W^α`,
`Y > W^{α/2+γ}` has probability at most `W^{−D_m}`, eventually along `adm(c₀, c₁)`. -/
theorem cutImprove : cutImproveStmt := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε β α γ hβ hβd hα hγ Dm hDm
  have hd2 : 2 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨Cs, K, hCs, hK, hset⟩ := Resample_setup hd2 P hc₀ hc₁ hκ
  set g := min γ β / 2 with hg
  have hg0 : 0 < g := by have := lt_min hγ hβ; positivity
  have hgγ : g ≤ γ / 2 := by have := min_le_left γ β; rw [hg]; linarith
  have hgβ : g ≤ β / 2 := by have := min_le_right γ β; rw [hg]; linarith
  obtain ⟨p, hp⟩ := Resample_exists_p g (Dm + 2 * (d / c₁) + 1) hg0
  obtain ⟨Cp, hCp0, hlde⟩ := Resample_lde_prob p
  set Kq := (16 + 10 ^ 4 * K ^ 2) * (4 * Cs + 32) with hKq
  have hKq0 : 0 ≤ Kq := by positivity
  filter_upwards [hset, Resample_prob_num d c₀ c₁ hc₁ g Dm Cp 4 p hp hCp0 (by norm_num),
    Resample_ev_pow c₀ c₁ 8 (β + -(d : ℝ) / 2) 0 (by linarith),
    Resample_ev_pow c₀ c₁ 4 (g + 2 * (β + -(d : ℝ) / 2)) 0 (by linarith),
    Resample_ev_pow c₀ c₁ (2 * K) (β + -(d : ℝ) / 2) 0 (by linarith),
    Resample_ev_pow c₀ c₁ (Kq + 1) (3 * g + α) (2 * (α / 2 + γ)) (by linarith)]
    with q hS hprob h8 h4 hK2 hfin
  obtain ⟨hW1, hS0, hS1, hS2, hSs, hSB, -, hstab⟩ := hS
  intro z hz
  obtain ⟨hzim, hzre, hzim1, hm4, hm1, hm⟩ := Resample_zfacts hκ hW1 q.2 hz
  have hW0 : (0 : ℝ) < q.1.1 := by exact_mod_cast hW1
  have hW1' : (1 : ℝ) ≤ q.1.1 := by exact_mod_cast hW1
  set W : ℝ := (q.1.1 : ℝ) with hWdef
  set t := W ^ g with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hW1' hg0.le
  have hsymm : (Smat P.ψ q.1.1 q.1.2).IsSymm := by
    ext i k; exact hSs k i
  rw [Real.rpow_zero] at h8 h4 hK2
  have hsplit : W ^ (β + -(d : ℝ) / 2) = W ^ β * W ^ (-(d : ℝ) / 2) := Real.rpow_add hW0 _ _
  have hδ8 : W ^ β * W ^ (-(d : ℝ) / 2) ≤ 1 / 8 := by rw [← hsplit]; linarith
  have hKδ : K * (W ^ β * W ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by rw [← hsplit]; linarith
  have h4' : 4 * t * (W ^ β * W ^ (-(d : ℝ) / 2)) ^ 2 ≤ 1 := by
    rw [← hsplit, Resample_rpow_sq hW0.le, ht, mul_assoc, ← Real.rpow_add hW0]
    linarith
  have ht3 : t ^ 3 * W ^ α = W ^ (3 * g + α) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0]; ring_nf
  have hsub : {ω | cutY q.1.1 (green (hmat ω) z) (msc z) ≤ W ^ β ∧
      (∀ a b, cutX q.1.1 (Smat P.ψ q.1.1 q.1.2) (green (hmat ω) z) a b ≤ 2 * W ^ α) ∧
      W ^ (α / 2 + γ) < cutY q.1.1 (green (hmat ω) z) (msc z)} ⊆
      {ω | ¬ Resample_LDE (hmat ω) (green (hmat ω) z) (Smat P.ψ q.1.1 q.1.2) t} := by
    rintro ω ⟨hY, hX, hlt⟩ hL
    have hcore := Resample_improve_det hd2 hW1 (Smat P.ψ q.1.1 q.1.2) Cs K hCs hK hS0 hS1 hS2
      hSs hSB z hzim hm hm4 hm1 (hstab z hzre hzim hzim1) (hmat ω) (hmat_isHermitian ω) t β α
      hα.le ht1 hL hY hX hδ8 h4' hKδ
    have hV := Resample_cutY_sqrt hW1 (green (hmat ω) z) (msc z) (Kq * (t ^ 3 * W ^ α))
      (by positivity) (fun i j => (hcore i j).trans_eq (by ring))
    have hlt2 : Real.sqrt (Kq * (t ^ 3 * W ^ α)) < W ^ (α / 2 + γ) := by
      rw [ht3]
      have hpos : 0 < W ^ (3 * g + α) := Real.rpow_pos_of_pos hW0 _
      have h1 : Kq * W ^ (3 * g + α) < (W ^ (α / 2 + γ)) ^ 2 := by
        rw [Resample_rpow_sq hW0.le]
        linarith
      calc Real.sqrt (Kq * W ^ (3 * g + α)) < Real.sqrt ((W ^ (α / 2 + γ)) ^ 2) :=
            Real.sqrt_lt_sqrt (by positivity) h1
        _ = W ^ (α / 2 + γ) := Real.sqrt_sq (Real.rpow_nonneg hW0.le _)
    linarith
  refine (measure_mono hsub).trans ((hlde _ hsymm hS0 z hzim t (by linarith)).trans ?_)
  exact ENNReal.ofReal_le_ofReal hprob

/-! ## The pair event -/

/-- **The pair event at one size, deterministically.** On `C(H) > 0` and the large deviation
events with factor `t = W^g = τ²`, `τ = W^{β/400}`, for both `H = hmat ω` and the resampled
`H'_y = hmat (resampleRow y η ω)`: `Y(H'_y) ≤ W^β` and
`|X_{ab}(H) − X_{ab}(H'_y)| ≤ W^{4β} (B_{ay}^{1/2} + B_{by}^{1/2})`, given the listed numerical side
conditions. -/
private theorem Resample_pair_size {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W)
    (S : Matrix (Zd d L) (Zd d L) ℝ) (Cs K : ℝ) (hCs : 0 ≤ Cs) (hK : 0 ≤ K)
    (hS0 : ∀ i k, 0 ≤ S i k) (hS1 : ∀ i, ∑ k, S i k = 1) (hS2 : ∀ k, ∑ i, S i k ≤ 1)
    (hSs : ∀ i k, S i k = S k i) (hSB : ∀ i j, S i j ≤ Cs * bB d L W i j)
    (hconv : ∀ x y, ∑ α, S x α * bB d L W α y ≤ Cs * bB d L W x y) (z : ℂ)
    (hz : 0 < z.im) (hm : msc z * (msc z + z) = -1) (hm4 : 1 / 4 ≤ ‖msc z‖) (hm1 : ‖msc z‖ ≤ 1)
    (hstab : Stable S (msc z ^ 2) K) (β α g a₀ aZ Kq ĉ CZ : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hg : g = 2 * (β / 400)) (ha₀ : 2 * a₀ = 3 * g + α)
    (haZ : aZ = β / 400 + a₀) (hKq : Kq = (16 + 10 ^ 4 * K ^ 2) * (4 * Cs + 32))
    (hĉ : ĉ = Real.sqrt (2 * 2 ^ (d - 2)))
    (hCZ : CZ = (2 * (2 * Cs + 2 * (Cs + Cs ^ 2) + 3) + 2 * (2 * (Cs + Cs) + 1) + 1 +
        2 * (2 * (Cs + Cs) + 1) ^ 2 * ĉ) * ((1 + ĉ) * (Kq + 1)))
    (h8 : (W : ℝ) ^ β * (W : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 / 8)
    (h4 : 4 * (W : ℝ) ^ g * ((W : ℝ) ^ β * (W : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 ≤ 1)
    (hKδ : K * ((W : ℝ) ^ β * (W : ℝ) ^ (-(d : ℝ) / 2)) ≤ 1 / 2)
    (hYr : (Kq + 1) * (W : ℝ) ^ a₀ * (W : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 / 8)
    (hsm : (2 * Cs + 2 * (Cs + Cs ^ 2) + 3) * (W : ℝ) ^ (β / 400) *
      ((1 + ĉ) * ((Kq + 1) * (W : ℝ) ^ a₀)) * (W : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 / 16)
    (hZ : CZ * (W : ℝ) ^ aZ ≤ (W : ℝ) ^ β)
    (hA : 2 * (W : ℝ) ^ α + 3 * 2 ^ (d - 2) * (256 * Cs ^ 2 + 8 * Cs * Cs) *
      (CZ * (W : ℝ) ^ aZ) ^ 4 ≤ (W : ℝ) ^ (4 * β))
    (y : Zd d L) (ω η : Sample (Zd d L))
    (hC : 0 < cutC β α l W S (green (hmat ω) z) (msc z))
    (hLω : Resample_LDE (hmat ω) (green (hmat ω) z) S ((W : ℝ) ^ g))
    (hLφ : Resample_LDE (hmat (resampleRow y η ω)) (green (hmat (resampleRow y η ω)) z) S
      ((W : ℝ) ^ g)) :
    cutY W (green (hmat (resampleRow y η ω)) z) (msc z) ≤ (W : ℝ) ^ β ∧
      ∀ a b, |cutX W S (green (hmat ω) z) a b -
          cutX W S (green (hmat (resampleRow y η ω)) z) a b| ≤
        (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)) := by
  obtain ⟨hB0, hBs, hBw, hBd, hBp, hBp'⟩ := Resample_Bfacts (L := L) hd hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set r := (W : ℝ) ^ (-(d : ℝ) / 2) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hW0.le _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)
  set τ := (W : ℝ) ^ (β / 400) with hτ
  have hτ1 : 1 ≤ τ := Real.one_le_rpow hW1 (by positivity)
  have hτt : τ ^ 2 = (W : ℝ) ^ g := by rw [hτ, Resample_rpow_sq hW0.le, hg]
  set t := (W : ℝ) ^ g with ht
  have ht1 : 1 ≤ t := by rw [← hτt]; nlinarith
  set m := msc z
  set H := hmat ω
  set H' := hmat (resampleRow y η ω)
  obtain ⟨hY, hXlt⟩ := Resample_cutC_pos β α l W hl hW S hS0 (green H z) m hC
  -- the improvement (8) for `H`
  have hcore := Resample_improve_det hd hW S Cs K hCs hK hS0 hS1 hS2 hSs hSB z hz hm hm4 hm1
    hstab H (hmat_isHermitian ω) t β α hα ht1 hLω hY (fun a b => (hXlt a b).le) h8 h4 hKδ
  have hKq0 : 0 ≤ Kq := by rw [hKq]; positivity
  set Y₀ := (Kq + 1) * (W : ℝ) ^ a₀ with hY₀
  have hY₀1 : 1 ≤ Y₀ := by
    have h1 : 1 ≤ (W : ℝ) ^ a₀ := Real.one_le_rpow hW1 (by
      have : 0 ≤ g := by rw [hg]; positivity
      linarith)
    nlinarith
  have hG : ∀ i j, ‖entryErr (green H z) m i j‖ ≤ Y₀ * Real.sqrt (bB d L W i j) := by
    intro i j
    have h := hcore i j
    have e : t ^ 3 * (W : ℝ) ^ α * bB d L W i j =
        ((W : ℝ) ^ a₀ * Real.sqrt (bB d L W i j)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hB0 i j).le, Resample_rpow_sq hW0.le, ha₀, ht,
        Real.rpow_add hW0, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      ring_nf
    have h' : ‖entryErr (green H z) m i j‖ ^ 2 ≤
        Kq * ((W : ℝ) ^ a₀ * Real.sqrt (bB d L W i j)) ^ 2 := by
      rw [← e, hKq]; linarith
    have := Resample_le_of_sq hKq0 (by positivity) h'
    rw [hY₀]; linarith
  have hD : ∀ a b, ∑ i, ∑ j, S a i * ‖green H z i j‖ ^ 2 * S j b ≤
      2 * (W : ℝ) ^ α * bB d L W a b := by
    intro a b
    have e := Resample_cutD_eq W hW S (green H z) a b
    unfold cutD at e
    rw [e]
    exact mul_le_mul_of_nonneg_right (hXlt a b).le (hB0 a b).le
  have hminor : ∀ a b, greenMinor (green H' z) y a b = greenMinor (green H z) y a b :=
    fun a b => Graphs.freeOf_greenMinor z hz y a b ω η
  obtain ⟨hRφ, hCφ, hQφ, hdφ⟩ := hLφ
  rw [← hτt] at hRφ hCφ hQφ hdφ
  have hĉ0 : 0 ≤ ĉ := by rw [hĉ]; exact Real.sqrt_nonneg _
  have hYr' : Y₀ * r ≤ 1 / 8 := by rw [hY₀]; exact hYr
  have hsm' : (2 * Cs + 2 * (Cs + Cs ^ 2) + 3) * τ * ((1 + ĉ) * Y₀) * r ≤ 1 / 16 := hsm
  have hBp'' : ∀ k y l, Real.sqrt (bB d L W k y) * Real.sqrt (bB d L W y l) ≤
      ĉ * r * Real.sqrt (bB d L W k l) := by rw [hĉ]; exact hBp'
  obtain ⟨hG', hDD⟩ := Resample_pairDet H H' z m S (bB d L W) y Y₀ r τ ĉ (2 ^ (d - 2)) Cs Cs
    (2 * (W : ℝ) ^ α) (hmat_isHermitian _) hz hm hm4 hm1 hS0 hS1 hSs hB0 hBs hBw hBd hSB hconv
    hCs hCs hĉ0 (by positivity) hBp'' hBp hY₀1 hr0 hr1 hτ1 hYr' hsm' hminor hG hD
    (fun j => hRφ y j) (fun j => hCφ y j) (hQφ y) (hdφ y)
  -- `Z = C_Z W^{a_Z}`
  have hZeq : (2 * (2 * Cs + 2 * (Cs + Cs ^ 2) + 3) + 2 * (2 * (Cs + Cs) + 1) + 1 +
      2 * (2 * (Cs + Cs) + 1) ^ 2 * ĉ) * τ * ((1 + ĉ) * Y₀) = CZ * (W : ℝ) ^ aZ := by
    rw [hCZ, haZ, Real.rpow_add hW0, hY₀, hτ]; ring
  rw [hZeq] at hG' hDD
  have hZ0 : 0 ≤ CZ * (W : ℝ) ^ aZ := by
    rw [← hZeq]
    have hτ0 : 0 ≤ τ := by linarith
    have hY₀0 : 0 ≤ Y₀ := by linarith
    exact mul_nonneg (mul_nonneg (by positivity) hτ0) (mul_nonneg (by linarith) hY₀0)
  refine ⟨(Resample_cutY_le W hW _ _ _ hZ0 hG').trans hZ, fun a b => ?_⟩
  have hBab := hB0 a b
  have e : cutX W S (green H z) a b - cutX W S (green H' z) a b =
      (∑ i, ∑ j, S a i * ‖green H z i j‖ ^ 2 * S j b -
        ∑ i, ∑ j, S a i * ‖green H' z i j‖ ^ 2 * S j b) / bB d L W a b := by
    unfold cutX cutD; rw [sub_div]
  rw [e, abs_div, abs_of_pos hBab, div_le_iff₀ hBab]
  refine (hDD a b).trans ?_
  rw [hBs y b]
  have hρ : 0 ≤ Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y) := by positivity
  have := mul_le_mul_of_nonneg_right hA (mul_nonneg hρ hBab.le)
  calc (2 * (W : ℝ) ^ α + 3 * 2 ^ (d - 2) * (256 * Cs ^ 2 + 8 * Cs * Cs) *
        (CZ * (W : ℝ) ^ aZ) ^ 4) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)) *
        bB d L W a b
      = (2 * (W : ℝ) ^ α + 3 * 2 ^ (d - 2) * (256 * Cs ^ 2 + 8 * Cs * Cs) *
        (CZ * (W : ℝ) ^ aZ) ^ 4) * ((Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)) *
        bB d L W a b) := by ring
    _ ≤ (W : ℝ) ^ (4 * β) * ((Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)) *
        bB d L W a b) := this
    _ = _ := by ring

/-- **The pair event**: for `d ≥ 8`, `0 < β < d/100`, `α = β/10` and
`l ≥ 1`, uniformly in `z ∈ 𝐃(κ, ε)` and `y`, under the law of `(ω, η)`, the event that `C(H) > 0`
while `Y(H'_y) ≤ W^β` and `|X_{ab}(H) − X_{ab}(H'_y)| ≤ W^{4β}(B_{ay}^{1/2} + B_{by}^{1/2})` for
all `a, b` fail, has probability at most `W^{−D_m}`, eventually along `adm(c₀, c₁)`. Here
`H = hmat ω` and `H'_y = hmat (resampleRow y η ω)`. -/
theorem cutPair : cutPairStmt := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε β hβ hβd l hl Dm hDm
  have hd2 : 2 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨Cs, K, hCs, hK, hset⟩ := Resample_setup hd2 P hc₀ hc₁ hκ
  obtain ⟨α, hα⟩ : ∃ x : ℝ, x = β / 10 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ x : ℝ, x = 2 * (β / 400) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; positivity
  obtain ⟨a₀, ha₀⟩ : ∃ x : ℝ, x = (3 * g + α) / 2 := ⟨_, rfl⟩
  obtain ⟨aZ, haZ⟩ : ∃ x : ℝ, x = β / 400 + a₀ := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ := Resample_exists_p g (Dm + 2 * (d / c₁) + 1) hg0
  obtain ⟨Cp, hCp0, hlde⟩ := Resample_lde_prob p
  obtain ⟨Kq, hKq⟩ : ∃ x : ℝ, x = (16 + 10 ^ 4 * K ^ 2) * (4 * Cs + 32) := ⟨_, rfl⟩
  have hKq0 : 0 ≤ Kq := by rw [hKq]; positivity
  obtain ⟨ĉ, hĉ⟩ : ∃ x : ℝ, x = Real.sqrt (2 * 2 ^ (d - 2)) := ⟨_, rfl⟩
  have hĉ0 : 0 ≤ ĉ := by rw [hĉ]; exact Real.sqrt_nonneg _
  obtain ⟨CE, hCE⟩ : ∃ x : ℝ, x = 2 * Cs + 2 * (Cs + Cs ^ 2) + 3 := ⟨_, rfl⟩
  obtain ⟨CZ, hCZ⟩ : ∃ x : ℝ, x = (2 * (2 * Cs + 2 * (Cs + Cs ^ 2) + 3) + 2 * (2 * (Cs + Cs) + 1) +
      1 + 2 * (2 * (Cs + Cs) + 1) ^ 2 * ĉ) * ((1 + ĉ) * (Kq + 1)) := ⟨_, rfl⟩
  obtain ⟨KN, hKN⟩ : ∃ x : ℝ, x = 256 * Cs ^ 2 + 8 * Cs * Cs := ⟨_, rfl⟩
  have hgβ : g = β / 200 := by rw [hg]; ring
  have ha₀β : a₀ = 23 * β / 400 := by rw [ha₀, hg, hα]; ring
  have haZβ : aZ = 24 * β / 400 := by rw [haZ, ha₀β]; ring
  have hαβ : α = β / 10 := hα
  filter_upwards [hset, Resample_prob_num d c₀ c₁ hc₁ g Dm Cp 8 p hp hCp0 (by norm_num),
    Resample_ev_pow c₀ c₁ 8 (β + -(d : ℝ) / 2) 0 (by linarith),
    Resample_ev_pow c₀ c₁ 4 (g + 2 * (β + -(d : ℝ) / 2)) 0 (by rw [hgβ]; linarith),
    Resample_ev_pow c₀ c₁ (2 * K) (β + -(d : ℝ) / 2) 0 (by linarith),
    Resample_ev_pow c₀ c₁ (8 * (Kq + 1)) (a₀ + -(d : ℝ) / 2) 0 (by rw [ha₀β]; linarith),
    Resample_ev_pow c₀ c₁ (16 * (CE * ((1 + ĉ) * (Kq + 1)))) (β / 400 + a₀ + -(d : ℝ) / 2) 0
      (by rw [ha₀β]; linarith),
    Resample_ev_pow c₀ c₁ CZ aZ β (by rw [haZβ]; linarith),
    Resample_ev_pow c₀ c₁ 4 α (4 * β) (by rw [hαβ]; linarith),
    Resample_ev_pow c₀ c₁ (2 * (3 * 2 ^ (d - 2) * KN * CZ ^ 4)) (4 * aZ) (4 * β)
      (by rw [haZβ]; linarith)]
    with q hS hprob h8 h4 hK2 hYr hsm hZ hA1 hA2
  obtain ⟨hW1, hS0, hS1, hS2, hSs, hSB, hconv, hstab⟩ := hS
  intro z hz y
  obtain ⟨hzim, hzre, hzim1, hm4, hm1, hm⟩ := Resample_zfacts hκ hW1 q.2 hz
  have hW0 : (0 : ℝ) < q.1.1 := by exact_mod_cast hW1
  set W : ℝ := (q.1.1 : ℝ) with hWdef
  rw [Real.rpow_zero] at h8 h4 hK2 hYr hsm
  have hsplit : W ^ (β + -(d : ℝ) / 2) = W ^ β * W ^ (-(d : ℝ) / 2) := Real.rpow_add hW0 _ _
  have hδ8 : W ^ β * W ^ (-(d : ℝ) / 2) ≤ 1 / 8 := by rw [← hsplit]; linarith
  have hKδ : K * (W ^ β * W ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by rw [← hsplit]; linarith
  have h4' : 4 * W ^ g * (W ^ β * W ^ (-(d : ℝ) / 2)) ^ 2 ≤ 1 := by
    rw [← hsplit, Resample_rpow_sq hW0.le, mul_assoc, ← Real.rpow_add hW0]
    linarith
  have hYr' : (Kq + 1) * W ^ a₀ * W ^ (-(d : ℝ) / 2) ≤ 1 / 8 := by
    rw [mul_assoc, ← Real.rpow_add hW0]; linarith
  have hsm' : (2 * Cs + 2 * (Cs + Cs ^ 2) + 3) * W ^ (β / 400) * ((1 + ĉ) * ((Kq + 1) * W ^ a₀)) *
      W ^ (-(d : ℝ) / 2) ≤ 1 / 16 := by
    rw [← hCE]
    have e : CE * W ^ (β / 400) * ((1 + ĉ) * ((Kq + 1) * W ^ a₀)) * W ^ (-(d : ℝ) / 2) =
        CE * ((1 + ĉ) * (Kq + 1)) * W ^ (β / 400 + a₀ + -(d : ℝ) / 2) := by
      rw [Real.rpow_add hW0, Real.rpow_add hW0]; ring
    rw [e]; linarith
  have hA : 2 * W ^ α + 3 * 2 ^ (d - 2) * (256 * Cs ^ 2 + 8 * Cs * Cs) * (CZ * W ^ aZ) ^ 4 ≤
      W ^ (4 * β) := by
    rw [← hKN]
    have e : (CZ * W ^ aZ) ^ 4 = CZ ^ 4 * W ^ (4 * aZ) := by
      rw [mul_pow, ← Real.rpow_natCast (W ^ aZ), ← Real.rpow_mul hW0.le]; push_cast; ring_nf
    rw [e]
    have : 3 * 2 ^ (d - 2) * KN * (CZ ^ 4 * W ^ (4 * aZ)) =
        (3 * 2 ^ (d - 2) * KN * CZ ^ 4) * W ^ (4 * aZ) := by ring
    rw [this]
    linarith
  set S := Smat P.ψ q.1.1 q.1.2 with hSdef
  have hsymm : S.IsSymm := by ext i k; exact hSs k i
  set t := W ^ g with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hW0 _
  set E := {ω : Sample (Zd d q.1.2) | ¬ Resample_LDE (hmat ω) (green (hmat ω) z) S t} with hE
  have hsub : {qq : Sample (Zd d q.1.2) × Sample (Zd d q.1.2) |
      0 < cutC β (β / 10) l q.1.1 S (green (hmat qq.1) z) (msc z) ∧
      ¬ (cutY q.1.1 (green (hmat (resampleRow y qq.2 qq.1)) z) (msc z) ≤ W ^ β ∧
        ∀ a b, |cutX q.1.1 S (green (hmat qq.1) z) a b -
            cutX q.1.1 S (green (hmat (resampleRow y qq.2 qq.1)) z) a b| ≤
          W ^ (4 * β) * (Real.sqrt (bB d q.1.2 q.1.1 a y) + Real.sqrt (bB d q.1.2 q.1.1 b y)))} ⊆
      {qq | qq.1 ∈ E} ∪ {qq | resampleRow y qq.2 qq.1 ∈ E} := by
    rintro ⟨ω, η⟩ ⟨hC, hnot⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, hE, not_or, not_not] at hcon
    rw [← hαβ] at hC
    have hα0 : 0 ≤ α := by rw [hαβ]; positivity
    have h2a : 2 * a₀ = 3 * g + α := by rw [ha₀]; ring
    exact hnot (Resample_pair_size hd2 hW1 S Cs K hCs hK hS0 hS1 hS2 hSs hSB hconv z hzim hm hm4
      hm1 (hstab z hzre hzim hzim1) β α g a₀ aZ Kq ĉ CZ l hl hα0 hβ.le hg h2a haZ hKq hĉ hCZ
      hδ8 h4' hKδ hYr' hsm' hZ hA y ω η hC hcon.1 hcon.2)
  have hPE := hlde S hsymm hS0 z hzim t htpos
  obtain ⟨hP1, hP2⟩ := Resample_pair_le S y E
  have hrb : rbmLaw d P q = gaussLaw S := rfl
  rw [hrb]
  calc ((gaussLaw S).prod (gaussLaw S)) _ ≤ ((gaussLaw S).prod (gaussLaw S))
        ({qq | qq.1 ∈ E} ∪ {qq | resampleRow y qq.2 qq.1 ∈ E}) := measure_mono hsub
    _ ≤ gaussLaw S E + gaussLaw S E := (measure_union_le _ _).trans (add_le_add hP1 hP2)
    _ ≤ ENNReal.ofReal (4 * (Fintype.card (Zd d q.1.2) : ℝ) ^ 2 * (Cp / t ^ p)) +
          ENNReal.ofReal (4 * (Fintype.card (Zd d q.1.2) : ℝ) ^ 2 * (Cp / t ^ p)) :=
        add_le_add hPE hPE
    _ = ENNReal.ofReal (8 * (Fintype.card (Zd d q.1.2) : ℝ) ^ 2 * (Cp / t ^ p)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ ENNReal.ofReal (W ^ (-Dm)) := ENNReal.ofReal_le_ofReal hprob

section Instances

end Instances

end RBM8D
