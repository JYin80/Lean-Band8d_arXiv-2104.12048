module

public import RBM8D.Deloc.Defs

@[expose] public section

/-!
# Deterministic steps of [I, §8]

The eigenvector bound `|u(x)|² ≤ η Im G_xx(λ + iη)` of the proof of [I, Theorem 1.3], the
inclusions `𝓑 ⊂ 𝓑̃ ⊂ 𝒜` of the proofs of [I, Theorem 1.3] and [I, Lemma 8.1], and the shell sum of
`B` near the diagonal.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Complex Matrix
open scoped ENNReal

namespace RBM8D

/-- The eigenvector bound of the proof of (1.13): for `H` Hermitian, `η > 0` and a unit vector
`u` with `H u = λ u`, `|u(x)|² ≤ η Im G_xx(λ + iη)`. -/
theorem eigvecBound :
  ∀ {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ), H.IsHermitian →
  ∀ (lam η : ℝ), 0 < η → ∀ u : n → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 → H *ᵥ u = (lam : ℂ) • u →
  ∀ x, ‖u x‖ ^ 2 ≤ η * (green H ((lam : ℂ) + (η : ℂ) * I) x x).im := by
  intro n _ _ H hH lam η hη u hu hEig x
  set z : ℂ := (lam : ℂ) + (η : ℂ) * I with hzdef
  have hz : 0 < z.im := by simp [z, hη]
  have hsub : (H - z • (1 : Matrix n n ℂ)) *ᵥ u = (-((η : ℂ) * I)) • u := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hEig]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, z]
    ring
  have h1 : green H z *ᵥ ((H - z • (1 : Matrix n n ℂ)) *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, green_mul_sub hH hz.ne', Matrix.one_mulVec]
  rw [hsub, Matrix.mulVec_smul] at h1
  have hx : u x = -((η : ℂ) * I) * ∑ y, green H z x y * u y := by
    conv_lhs => rw [← h1]
    simp [Matrix.mulVec, dotProduct]
  have hCS : ‖∑ y, green H z x y * u y‖ ^ 2 ≤
      (∑ y, ‖green H z x y‖ ^ 2) * ∑ y, ‖u y‖ ^ 2 := by
    calc ‖∑ y, green H z x y * u y‖ ^ 2 ≤ (∑ y, ‖green H z x y‖ * ‖u y‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (by simp))
      _ ≤ (∑ y, ‖green H z x y‖ ^ 2) * ∑ y, ‖u y‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [hu, mul_one, sum_norm_sq_green_row hH hz x] at hCS
  have hzim : z.im = η := by simp [z]
  rw [hzim] at hCS
  have hn : ‖-((η : ℂ) * I)‖ = η := by simp [abs_of_pos hη]
  rw [hx, norm_mul, mul_pow, hn]
  calc η ^ 2 * ‖∑ y, green H z x y * u y‖ ^ 2 ≤ η ^ 2 * ((green H z x x).im / η) := by gcongr
    _ = η * (green H z x x).im := by field_simp

/-- `(t + 1)^M ≤ 2^M (1 + k!) e^{t^γ}` for `t ≥ 0`, `γ > 0`, `M ≥ 0`, `k = ⌈M/γ⌉`. -/
private theorem det_pow_le_exp (γ M t : ℝ) (hγ : 0 < γ) (hM : 0 ≤ M) (ht : 0 ≤ t) :
    (t + 1) ^ M ≤ (2 : ℝ) ^ M * (1 + (⌈M / γ⌉₊).factorial) * Real.exp (t ^ γ) := by
  set k : ℕ := ⌈M / γ⌉₊ with hk
  have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2M : (0 : ℝ) < (2 : ℝ) ^ M := Real.rpow_pos_of_pos (by norm_num) M
  have hexp1 : 1 ≤ Real.exp (t ^ γ) := Real.one_le_exp (Real.rpow_nonneg ht γ)
  rcases le_total t 1 with h | h
  · calc (t + 1) ^ M ≤ (2 : ℝ) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      _ = (2 : ℝ) ^ M * 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ M * (1 + k.factorial) * Real.exp (t ^ γ) := by
        gcongr
        linarith
  · have hMk : M ≤ γ * k := by
      have h1 : M / γ ≤ k := Nat.le_ceil _
      rwa [div_le_iff₀ hγ, mul_comm] at h1
    have ht0 : 0 < t := by linarith
    have hx : (0 : ℝ) ≤ t ^ γ := Real.rpow_nonneg ht γ
    have hpow : t ^ M ≤ (t ^ γ) ^ k := by
      calc t ^ M ≤ t ^ (γ * (k : ℝ)) := Real.rpow_le_rpow_of_exponent_le h hMk
        _ = (t ^ γ) ^ k := by rw [Real.rpow_mul ht, Real.rpow_natCast]
    have hfac : (t ^ γ) ^ k ≤ k.factorial * Real.exp (t ^ γ) := by
      have := Real.pow_div_factorial_le_exp (t ^ γ) hx k
      rwa [div_le_iff₀ hkf, mul_comm] at this
    calc (t + 1) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      _ = (2 : ℝ) ^ M * t ^ M := Real.mul_rpow (by norm_num) ht
      _ ≤ (2 : ℝ) ^ M * (k.factorial * Real.exp (t ^ γ)) := by gcongr; exact hpow.trans hfac
      _ ≤ (2 : ℝ) ^ M * (1 + k.factorial) * Real.exp (t ^ γ) := by
        have : (0 : ℝ) ≤ Real.exp (t ^ γ) := (Real.exp_pos _).le
        nlinarith [mul_nonneg h2M.le this]

/-- The inclusion `𝓑_{γ,K,ℓ} ⊂ 𝓑̃_{M, C K, ℓ}` of the proof of [I, Theorem 1.3], with
`C = 2^M (1 + k!)`, `k = ⌈M/γ⌉`, for `ℓ > 0`, from `(t + 1)^M ≤ C e^{t^γ}` for `t ≥ 0`. -/
theorem bsubBt :
  ∀ (d L : ℕ) [NeZero L] (u : Zd d L → Zd d L → ℂ) (lam : Zd d L → ℝ) (κ γ K ℓ M : ℝ),
    0 < γ → 0 < ℓ → 0 ≤ M →
    locSetB d L κ γ K ℓ u lam ⊆
      locSetBt d L κ M ((2 : ℝ) ^ M * (1 + (⌈M / γ⌉₊).factorial) * K) ℓ u lam := by
  intro d L _ u lam κ γ K ℓ M hγ hℓ hM α hα
  simp only [locSetB, locSetBt, Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
  obtain ⟨hlam, x₀, hx₀⟩ := hα
  refine ⟨hlam, x₀, ?_⟩
  set C : ℝ := (2 : ℝ) ^ M * (1 + (⌈M / γ⌉₊).factorial) with hC
  have hC0 : 0 ≤ C := by positivity
  calc ∑ x, ‖u α x‖ ^ 2 * (((zdistInf d L (x - x₀) : ℝ) / ℓ) + 1) ^ M
      ≤ ∑ x, C * (‖u α x‖ ^ 2 * Real.exp (((zdistInf d L (x - x₀) : ℝ) / ℓ) ^ γ)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have := det_pow_le_exp γ M ((zdistInf d L (x - x₀) : ℝ) / ℓ) hγ hM (by positivity)
        have h0 : (0 : ℝ) ≤ ‖u α x‖ ^ 2 := by positivity
        calc ‖u α x‖ ^ 2 * (((zdistInf d L (x - x₀) : ℝ) / ℓ) + 1) ^ M
            ≤ ‖u α x‖ ^ 2 * (C * Real.exp (((zdistInf d L (x - x₀) : ℝ) / ℓ) ^ γ)) :=
              mul_le_mul_of_nonneg_left this h0
          _ = _ := by ring
    _ = C * ∑ x, ‖u α x‖ ^ 2 * Real.exp (((zdistInf d L (x - x₀) : ℝ) / ℓ) ^ γ) := by
        rw [Finset.mul_sum]
    _ ≤ C * K := mul_le_mul_of_nonneg_left hx₀ hC0

/-- For a far pair `ℓ̃ ≤ ‖y − x‖_L`, `1 ≤ (ℓ/ℓ̃)^M (‖x − x₀‖_L/ℓ + 1)^M (‖y − x₀‖_L/ℓ + 1)^M`. -/
private theorem det_far_pair (d L : ℕ) [NeZero L] (ℓ ℓt M : ℝ) (hℓ : 0 < ℓ) (hℓt : 0 < ℓt)
    (hM : 0 ≤ M) (x₀ x y : Zd d L) (h : ℓt ≤ (zdistInf d L (y - x) : ℝ)) :
    1 ≤ (ℓ / ℓt) ^ M * (((zdistInf d L (x - x₀) : ℝ) / ℓ + 1) ^ M *
      ((zdistInf d L (y - x₀) : ℝ) / ℓ + 1) ^ M) := by
  have htri : zdistInf d L (y - x) ≤ zdistInf d L (y - x₀) + zdistInf d L (x - x₀) := by
    have : y - x = (y - x₀) + -(x - x₀) := by abel
    rw [this]
    exact (zdistInf_add_le d L _ _).trans (by rw [zdistInf_neg])
  have htri' : ℓt ≤ (zdistInf d L (y - x₀) : ℝ) + (zdistInf d L (x - x₀) : ℝ) := by
    exact_mod_cast h.trans (by exact_mod_cast htri)
  set a : ℝ := (zdistInf d L (x - x₀) : ℝ) / ℓ with ha
  set b : ℝ := (zdistInf d L (y - x₀) : ℝ) / ℓ with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hab : ℓt / ℓ ≤ a + b := by
    rw [div_le_iff₀ hℓ, ha, hb, ← add_div, div_mul_cancel₀ _ hℓ.ne']
    linarith
  have hρ : 0 < ℓ / ℓt := by positivity
  have hbase : 1 ≤ (ℓ / ℓt) * ((a + 1) * (b + 1)) := by
    have h1 : 1 ≤ (ℓ / ℓt) * (a + b) := by
      have : (ℓ / ℓt) * (ℓt / ℓ) = 1 := by field_simp
      calc (1 : ℝ) = (ℓ / ℓt) * (ℓt / ℓ) := this.symm
        _ ≤ (ℓ / ℓt) * (a + b) := mul_le_mul_of_nonneg_left hab hρ.le
    calc (1 : ℝ) ≤ (ℓ / ℓt) * (a + b) := h1
      _ ≤ (ℓ / ℓt) * ((a + 1) * (b + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hρ.le
        nlinarith
  calc (1 : ℝ) ≤ ((ℓ / ℓt) * ((a + 1) * (b + 1))) ^ M := Real.one_le_rpow hbase hM
    _ = (ℓ / ℓt) ^ M * ((a + 1) ^ M * (b + 1) ^ M) := by
      rw [Real.mul_rpow hρ.le (by positivity), Real.mul_rpow (by positivity) (by positivity)]

/-- The inclusion `𝓑̃_{M,K,ℓ} ⊂ 𝒜_{δ_L, ℓ̃}` of the proof of [I, Lemma 8.1], with
`δ_L = K (ℓ/ℓ̃)^{M/2} L^{d/2}` (Cauchy–Schwarz and the torus triangle inequality). -/
theorem btSubA :
  ∀ (d L : ℕ) [NeZero L] (u : Zd d L → Zd d L → ℂ) (lam : Zd d L → ℝ) (κ M K ℓ ℓt : ℝ),
    0 < ℓ → 0 < ℓt → 0 ≤ M →
    locSetBt d L κ M K ℓ u lam ⊆
      locSetA d L κ (K * (ℓ / ℓt) ^ (M / 2) * (L : ℝ) ^ ((d : ℝ) / 2)) ℓt u lam := by
  intro d L _ u lam κ M K ℓ ℓt hℓ hℓt hM α hα
  classical
  simp only [locSetBt, locSetA, Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
  obtain ⟨hlam, x₀, hx₀⟩ := hα
  refine ⟨hlam, ?_⟩
  set v : Zd d L → ℝ := fun x => ‖u α x‖ ^ 2 with hv
  set w : Zd d L → ℝ := fun x => ((zdistInf d L (x - x₀) : ℝ) / ℓ + 1) ^ M with hw
  set ρ : ℝ := ℓ / ℓt with hρdef
  have hρ : 0 < ρ := by positivity
  have hv0 : ∀ x, 0 ≤ v x := fun x => by positivity
  have hw0 : ∀ x, 0 ≤ w x := fun x => by positivity
  set S : ℝ := ∑ x, v x * w x with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun x _ => mul_nonneg (hv0 x) (hw0 x)
  have hSK : S ≤ K := hx₀
  have hK0 : 0 ≤ K := hS0.trans hSK
  set F : Zd d L → ℝ := fun x =>
    ∑ y ∈ Finset.univ.filter (fun y => ℓt ≤ (zdistInf d L (y - x) : ℝ)), ‖u α y‖ ^ 2 with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x => Finset.sum_nonneg fun y _ => by positivity
  -- the double sum over far pairs
  have hT : ∑ x, v x * F x ≤ ρ ^ M * S ^ 2 := by
    calc ∑ x, v x * F x
        = ∑ x, ∑ y, if ℓt ≤ (zdistInf d L (y - x) : ℝ) then v x * v y else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hF, Finset.mul_sum, Finset.sum_filter]
      _ ≤ ∑ x, ∑ y, ρ ^ M * ((v x * w x) * (v y * w y)) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          split_ifs with hfar
          · have hp := det_far_pair d L ℓ ℓt M hℓ hℓt hM x₀ x y hfar
            have hvv : 0 ≤ v x * v y := mul_nonneg (hv0 x) (hv0 y)
            calc v x * v y = (v x * v y) * 1 := by ring
              _ ≤ (v x * v y) * (ρ ^ M * (w x * w y)) := mul_le_mul_of_nonneg_left hp hvv
              _ = _ := by ring
          · exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (hv0 x) (hw0 x))
              (mul_nonneg (hv0 y) (hw0 y)))
      _ = ρ ^ M * S ^ 2 := by
          rw [hS, sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
  -- Cauchy-Schwarz over the sites
  have hCS : (∑ x, ‖u α x‖ * Real.sqrt (F x)) ^ 2 ≤ (L : ℝ) ^ d * (ρ ^ M * S ^ 2) := by
    calc (∑ x, ‖u α x‖ * Real.sqrt (F x)) ^ 2
        = (∑ x, 1 * (‖u α x‖ * Real.sqrt (F x))) ^ 2 := by simp
      _ ≤ (∑ x : Zd d L, (1 : ℝ) ^ 2) * ∑ x, (‖u α x‖ * Real.sqrt (F x)) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (L : ℝ) ^ d * ∑ x, v x * F x := by
          congr 1
          · simp
          · refine Finset.sum_congr rfl fun x _ => ?_
            rw [mul_pow, Real.sq_sqrt (hF0 x)]
      _ ≤ (L : ℝ) ^ d * (ρ ^ M * S ^ 2) := mul_le_mul_of_nonneg_left hT (by positivity)
  have hδ0 : 0 ≤ K * ρ ^ (M / 2) * (L : ℝ) ^ ((d : ℝ) / 2) := by positivity
  have hδ2 : (K * ρ ^ (M / 2) * (L : ℝ) ^ ((d : ℝ) / 2)) ^ 2 = K ^ 2 * ρ ^ M * (L : ℝ) ^ d := by
    have h1 : (ρ ^ (M / 2)) ^ 2 = ρ ^ M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; norm_num
    have h2 : ((L : ℝ) ^ ((d : ℝ) / 2)) ^ 2 = (L : ℝ) ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg L)]
      rw [show (d : ℝ) / 2 * ((2 : ℕ) : ℝ) = (d : ℕ) by push_cast; ring, Real.rpow_natCast]
    rw [mul_pow, mul_pow, h1, h2]
  have hSS : S ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hS0 hSK 2
  refine le_of_sq_le_sq ?_ hδ0
  rw [hδ2]
  calc (∑ x, ‖u α x‖ * Real.sqrt (F x)) ^ 2 ≤ (L : ℝ) ^ d * (ρ ^ M * S ^ 2) := hCS
    _ ≤ (L : ℝ) ^ d * (ρ ^ M * K ^ 2) := by gcongr
    _ = _ := by ring

/-- At most two points of the cycle `ZMod L` are at distance exactly `r` from `0`. -/
private theorem det_card_zdist_eq (L : ℕ) [NeZero L] (r : ℕ) :
    (Finset.univ.filter (fun a : ZMod L => zdist L a = r)).card ≤ 2 := by
  have hmaps : Set.MapsTo (fun a : ZMod L => a.valMinAbs)
      (↑(Finset.univ.filter (fun a : ZMod L => zdist L a = r)))
      (↑({(r : ℤ), -(r : ℤ)} : Finset ℤ)) := by
    intro a ha
    have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    rw [zdist_eq_natAbs_valMinAbs] at ha'
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    dsimp only
    omega
  calc _ ≤ ({(r : ℤ), -(r : ℤ)} : Finset ℤ).card :=
        Finset.card_le_card_of_injOn _ hmaps (fun a _ b _ h => ZMod.valMinAbs_inj.mp h)
    _ ≤ 2 := Finset.card_le_two

/-- At most `2r + 1` points of the cycle `ZMod L` are at distance at most `r` from `0`. -/
private theorem det_card_zdist_le (L : ℕ) [NeZero L] (r : ℕ) :
    (Finset.univ.filter (fun a : ZMod L => zdist L a ≤ r)).card ≤ 2 * r + 1 := by
  have hmaps : Set.MapsTo (fun a : ZMod L => a.valMinAbs)
      (↑(Finset.univ.filter (fun a : ZMod L => zdist L a ≤ r))) (↑(Finset.Icc (-(r : ℤ)) r)) := by
    intro a ha
    have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    rw [zdist_eq_natAbs_valMinAbs] at ha'
    rw [Finset.mem_coe, Finset.mem_Icc]
    dsimp only
    omega
  calc _ ≤ (Finset.Icc (-(r : ℤ)) r).card :=
        Finset.card_le_card_of_injOn _ hmaps (fun a _ b _ h => ZMod.valMinAbs_inj.mp h)
    _ = 2 * r + 1 := by rw [Int.card_Icc]; omega

/-- The sphere `‖z‖_L = r`, `r ≥ 1`, of `Z_L^d` has at most `2d (2r + 1)^{d-1}` points. -/
private theorem det_card_shell (d L : ℕ) [NeZero L] (r : ℕ) (hr : 1 ≤ r) :
    (Finset.univ.filter (fun z : Zd d L => zdistInf d L z = r)).card ≤
      d * (2 * (2 * r + 1) ^ (d - 1)) := by
  classical
  set A : Finset (ZMod L) := Finset.univ.filter (fun a => zdist L a = r) with hA
  set B : Finset (ZMod L) := Finset.univ.filter (fun a => zdist L a ≤ r) with hB
  have hsub : Finset.univ.filter (fun z : Zd d L => zdistInf d L z = r) ⊆
      Finset.univ.biUnion (fun i : Fin d =>
        Fintype.piFinset (fun j : Fin d => if j = i then A else B)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hex : ∃ i, zdist L (z i) = r := by
      by_contra hne
      simp only [not_exists] at hne
      have hlt : zdistInf d L z < r := by
        unfold zdistInf
        rw [Finset.sup_lt_iff (by change 0 < r; omega)]
        intro i _
        exact lt_of_le_of_ne (hz ▸ zdist_le_zdistInf d L z i) (hne i)
      omega
    obtain ⟨i, hi⟩ := hex
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro j
    by_cases hj : j = i
    · subst hj; simp [A, hi]
    · simp only [hj, ite_false, B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz ▸ zdist_le_zdistInf d L z j
  have hone : ∀ i : Fin d, (Fintype.piFinset fun j : Fin d => if j = i then A else B).card ≤
      2 * (2 * r + 1) ^ (d - 1) := by
    intro i
    rw [Fintype.card_piFinset]
    calc ∏ j : Fin d, (if j = i then A else B).card
        ≤ ∏ j : Fin d, (if j = i then 2 else 2 * r + 1) :=
          Finset.prod_le_prod (fun j _ => by
            split_ifs
            · exact det_card_zdist_eq L r
            · exact det_card_zdist_le L r)
      _ = 2 * (2 * r + 1) ^ (d - 1) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
          rw [Finset.prod_congr rfl (g := fun _ => 2 * r + 1)
            (fun j hj => by simp [Finset.ne_of_mem_erase hj])]
          simp
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin d, (Fintype.piFinset fun j : Fin d => if j = i then A else B).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i : Fin d, 2 * (2 * r + 1) ^ (d - 1) := Finset.sum_le_sum fun i _ => hone i
    _ = _ := by simp

/-- The shell sum: `Σ_{0 < ‖y − x‖_L < ℓ̃} B_xy ≤ 2d 3^{d−1} ℓ̃² W^{−2}` for `d ≥ 2`, `W ≥ 1`. -/
theorem shellSum :
  ∀ (d L W : ℕ) [NeZero L], 2 ≤ d → 1 ≤ W → ∀ (ℓt : ℝ) (x : Zd d L),
    ∑ y ∈ Finset.univ.filter (fun y : Zd d L =>
        0 < zdistInf d L (y - x) ∧ (zdistInf d L (y - x) : ℝ) < ℓt), bB d L W x y ≤
      2 * d * 3 ^ (d - 1) * ℓt ^ 2 * (W : ℝ) ^ (-2 : ℝ) := by
  intro d L W _ hd hW ℓt x
  classical
  set S : Finset (Zd d L) := Finset.univ.filter (fun y : Zd d L =>
    0 < zdistInf d L (y - x) ∧ (zdistInf d L (y - x) : ℝ) < ℓt) with hS
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWm : (0 : ℝ) ≤ (W : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg hW0.le _
  set c : ℝ := 2 * d * 3 ^ (d - 1) * (W : ℝ) ^ (-2 : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  rcases le_or_gt ℓt 0 with hl | hl
  · have hSe : S = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun y hy => ?_
      rw [hS, Finset.mem_filter] at hy
      have := hy.2.2
      have h0 : (0 : ℝ) ≤ (zdistInf d L (y - x) : ℝ) := Nat.cast_nonneg _
      linarith
    rw [hSe, Finset.sum_empty]
    positivity
  · obtain ⟨R, hR⟩ : ∃ R : ℕ, ⌈ℓt⌉₊ = R + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hl))
    have hRlt : (R : ℝ) < ℓt := by
      have := Nat.ceil_lt_add_one hl.le
      rw [hR] at this
      push_cast at this
      linarith
    have hmaps : ∀ y ∈ S, zdistInf d L (y - x) ∈ Finset.Icc 1 R := by
      intro y hy
      rw [hS, Finset.mem_filter] at hy
      obtain ⟨_, h0, h1⟩ := hy
      have : zdistInf d L (y - x) < ⌈ℓt⌉₊ := Nat.lt_ceil.mpr h1
      rw [Finset.mem_Icc]
      omega
    have hterm : ∀ y ∈ S, bB d L W x y ≤
        (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (y - x) : ℕ) : ℝ) ^ (2 - (d : ℝ)) := by
      intro y hy
      rw [hS, Finset.mem_filter] at hy
      have h0 := hy.2.1
      unfold bB
      rw [← neg_sub, zdistInf_neg]
      have hr0 : (0 : ℝ) < (zdistInf d L (y - x) : ℝ) := by exact_mod_cast h0
      have hd' : (2 : ℝ) - d ≤ 0 := by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr0 (by linarith) hd') hWm
    have hfib : ∀ r ∈ Finset.Icc 1 R,
        ∑ y ∈ S with zdistInf d L (y - x) = r,
          (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (y - x) : ℕ) : ℝ) ^ (2 - (d : ℝ)) ≤ c * r := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.1
      have hr0 : (0 : ℝ) < r := by linarith
      have hcard : (S.filter (fun y => zdistInf d L (y - x) = r)).card ≤
          d * (2 * (2 * r + 1) ^ (d - 1)) := by
        refine le_trans ?_ (det_card_shell d L r hr.1)
        refine Finset.card_le_card_of_injOn (fun y => y - x) ?_ ?_
        · intro y hy
          have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
          exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩)
        · intro y _ y' _ h
          exact sub_left_injective h
      have hcardR : ((S.filter (fun y => zdistInf d L (y - x) = r)).card : ℝ) ≤
          d * (2 * (2 * (r : ℝ) + 1) ^ (d - 1)) := by exact_mod_cast hcard
      have hconst : ∑ y ∈ S with zdistInf d L (y - x) = r,
          (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (y - x) : ℕ) : ℝ) ^ (2 - (d : ℝ)) =
          ((S.filter (fun y => zdistInf d L (y - x) = r)).card : ℝ) *
            ((W : ℝ) ^ (-2 : ℝ) * (r : ℝ) ^ (2 - (d : ℝ))) := by
        rw [Finset.sum_congr rfl (g := fun _ => (W : ℝ) ^ (-2 : ℝ) * (r : ℝ) ^ (2 - (d : ℝ)))
          (fun y hy => by rw [(Finset.mem_filter.mp hy).2])]
        rw [Finset.sum_const, nsmul_eq_mul]
      have h2 : (r : ℝ) ^ (d - 1) * (r : ℝ) ^ (2 - (d : ℝ)) = r := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
        have : (((d - 1 : ℕ) : ℝ)) + (2 - (d : ℝ)) = 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this, Real.rpow_one]
      have key : (2 * (r : ℝ) + 1) ^ (d - 1) * (r : ℝ) ^ (2 - (d : ℝ)) ≤ 3 ^ (d - 1) * r := by
        calc (2 * (r : ℝ) + 1) ^ (d - 1) * (r : ℝ) ^ (2 - (d : ℝ))
            ≤ (3 * (r : ℝ)) ^ (d - 1) * (r : ℝ) ^ (2 - (d : ℝ)) := by
              gcongr
              linarith
          _ = 3 ^ (d - 1) * ((r : ℝ) ^ (d - 1) * (r : ℝ) ^ (2 - (d : ℝ))) := by
              rw [mul_pow]; ring
          _ = 3 ^ (d - 1) * r := by rw [h2]
      have hrp : 0 ≤ (r : ℝ) ^ (2 - (d : ℝ)) := Real.rpow_nonneg hr0.le _
      rw [hconst]
      calc ((S.filter (fun y => zdistInf d L (y - x) = r)).card : ℝ) *
            ((W : ℝ) ^ (-2 : ℝ) * (r : ℝ) ^ (2 - (d : ℝ)))
          ≤ (d * (2 * (2 * (r : ℝ) + 1) ^ (d - 1))) *
            ((W : ℝ) ^ (-2 : ℝ) * (r : ℝ) ^ (2 - (d : ℝ))) :=
            mul_le_mul_of_nonneg_right hcardR (mul_nonneg hWm hrp)
        _ = (2 * d * (W : ℝ) ^ (-2 : ℝ)) *
              ((2 * (r : ℝ) + 1) ^ (d - 1) * (r : ℝ) ^ (2 - (d : ℝ))) := by ring
        _ ≤ (2 * d * (W : ℝ) ^ (-2 : ℝ)) * (3 ^ (d - 1) * r) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = c * r := by rw [hc]; ring
    calc ∑ y ∈ S, bB d L W x y
        ≤ ∑ y ∈ S, (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (y - x) : ℕ) : ℝ) ^ (2 - (d : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = ∑ r ∈ Finset.Icc 1 R, ∑ y ∈ S with zdistInf d L (y - x) = r,
            (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (y - x) : ℕ) : ℝ) ^ (2 - (d : ℝ)) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ r ∈ Finset.Icc 1 R, c * r := Finset.sum_le_sum hfib
      _ ≤ ∑ r ∈ Finset.Icc 1 R, c * R := by
          refine Finset.sum_le_sum fun r hr => ?_
          have : (r : ℝ) ≤ R := by exact_mod_cast (Finset.mem_Icc.mp hr).2
          exact mul_le_mul_of_nonneg_left this hc0
      _ = c * R * R := by simp; ring
      _ ≤ c * ℓt * ℓt := by gcongr
      _ = 2 * d * 3 ^ (d - 1) * ℓt ^ 2 * (W : ℝ) ^ (-2 : ℝ) := by rw [hc]; ring

end RBM8D
