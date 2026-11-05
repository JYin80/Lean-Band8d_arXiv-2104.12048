import RBM8D.SelfEnergy.MainCancel
import RBM8D.SelfEnergy.Entrywise
import RBM8D.SelfEnergy.FT1c
import Batteries.Tactic.OpenPrivate

/-!
# [I, §8, proof of Theorem 1.4]: the bound part of [II, Lemma 3.9] = [I, Lemma 5.8]

For `d ≥ 8`, a profile `P`, `H(n − 1)`, `n`-th order `T`-equations over `Sig` with one `Σ_n = E`
for every error order `D > n`, and the local law `localLawTExpStmt'`, with `Σ' = Sig` updated at
`n` by `E`, `A = (n−2)d/2` and `R(E, W) = Σ_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)` (`ValZ.rowSum`):

* `Assembly.sigma_eq_zero`: the coefficient `𝔖_n(E)` of [I, (8.8)] vanishes for `|E| < 2`.
  Along the sizes `L_n` of [I, (5.39)] (`G13.windowFilter` at `c₀ = 1`) and at
  `z_n = E + i W^{2+ε}/L_n²`, [I, (5.40)] (`G13.mainCancel`), [I, (8.13)] (`VR2.rowSum`) and
  [I, (8.8)] (`FT1c.rowSumExpand`) give `|𝔖_n(E)| ≤ W^{-c} + (1 + C) W^{-1}`, and `W → ∞` along
  the proper filter of [I, (5.39)].
* `Assembly.rowSum_decay`: [I, (8.12)], `|R(E, W)| ≤ C W^{-D}` for every `D`, uniformly in
  `|E| < 2 − κ`.
* `Assembly.rowSumBound`: [I, (8.11)], `|Σ_x Σ_n(0, x)(z)| ≤ L^τ η W^{-(n-2)d/2}` on the whole
  domain `𝐃(κ, ε)`, from [I, (8.13)] on `𝐃(κ, ε)` and [I, (8.12)] with
  `D = (n−2)d/2 + 2/c₁ − 1`; no restriction `η ≤ L^{-ε}` is used.
* `G13.selfEnergyStepEnd : G13.selfEnergyStepEndStmt`: [I, (1.26)–(1.27)] for `Σ_n`, `n ≥ 4`
  even (`G13.boundStepStmt`), with [I, (1.26)] from `G13.entrywise`.
-/

noncomputable section

open scoped BigOperators
open Filter Topology

namespace RBM8D.Graphs

open private MainCancel_selfEnergiesUpTo_congr from RBM8D.SelfEnergy.MainCancel

/-- **[II, Lemma 3.9] = [I, Lemma 5.8]** for `d ≥ 8` and every profile, from the local law of
[II, Theorem 3.6] = [I, Theorem 2.16] for a family of `T`-expansions (`localLawTExpStmt'`):
the bound part `G13.boundStepStmt d P`. -/
def G13.selfEnergyStepEndStmt : Prop :=
  localLawTExpStmt' → ∀ (d : ℕ), 8 ≤ d → ∀ P : Profile d, G13.boundStepStmt d P

/-! ## The hypotheses at `Σ' = Sig` updated at `n` -/

/-- Under `H(n − 1)` and `n`-th order `T`-equations with `Σ_n = E`, the family `Sig` updated at
`n` by `E` has self-energies at the even orders `4 ≤ k ≤ n − 1` and `Σ_n = E` has the shape of an
`n`-th order self-energy. -/
private theorem Assembly_hyps {d : ℕ} (P : Profile d) (Strat : ℕ → ℕ → TRec → TEqRec) (n : ℕ)
    (hn : 1 ≤ n) (Sig : ℕ → Expansion 2) (E : Expansion 2) (𝒬n : ℕ → TEqRec)
    (hH : HWith d (smatVar P) Strat Sig (n - 1))
    (hT : ∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d (smatVar P) Sig n D (𝒬n D)) :
    SelfEnergiesUpTo d (smatVar P) (Function.update Sig n E) (n - 1) ∧
      SelfEnergyShape n (Function.update Sig n E n) := by
  refine ⟨MainCancel_selfEnergiesUpTo_congr (smatVar P) Sig _ (n - 1)
    (fun j hj => (Function.update_of_ne (by omega) _ _).symm) hH.1, ?_⟩
  obtain ⟨hE, -, -, -, -, hsh, -⟩ := hT (n + 1) (Nat.lt_succ_self n)
  rw [Function.update_self, ← hE]
  exact hsh

/-! ## Real inequalities -/

/-- For `w ≥ 1`, `a ≥ 5`, `0 < ε ≤ 1` and `w^a ≤ ℓ²/w²`: `ℓ^{1/2} w^{2+ε}/ℓ² ≤ w^{-1}`. -/
private theorem Assembly_mid {w ℓ a ε : ℝ} (hw : 1 ≤ w) (hℓ : 0 < ℓ) (ha : 5 ≤ a)
    (hε1 : ε ≤ 1) (hwin : w ^ a ≤ ℓ ^ 2 / w ^ 2) :
    ℓ ^ (1 / 2 : ℝ) * (w ^ (2 + ε) / ℓ ^ 2) ≤ w ^ (-1 : ℝ) := by
  have hw0 : 0 < w := by linarith
  have hQ : w ^ (a + 2) ≤ ℓ ^ (2 : ℝ) := by
    rw [Real.rpow_add hw0, Real.rpow_two, Real.rpow_two]
    rwa [le_div_iff₀ (by positivity)] at hwin
  have h32 : w ^ (3 + ε) ≤ ℓ ^ (3 / 2 : ℝ) :=
    calc w ^ (3 + ε) ≤ w ^ ((a + 2) * (3 / 4)) :=
          Real.rpow_le_rpow_of_exponent_le hw (by nlinarith)
      _ = (w ^ (a + 2)) ^ (3 / 4 : ℝ) := Real.rpow_mul hw0.le _ _
      _ ≤ (ℓ ^ (2 : ℝ)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hw0.le _) hQ (by norm_num)
      _ = ℓ ^ (3 / 2 : ℝ) := by rw [← Real.rpow_mul hℓ.le]; norm_num
  have hsplit : ℓ ^ 2 = ℓ ^ (1 / 2 : ℝ) * ℓ ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hℓ, ← Real.rpow_two]; norm_num
  have hw3 : w ^ (3 + ε) = w ^ (2 + ε) * w := by
    rw [show 3 + ε = (2 + ε) + 1 by ring, Real.rpow_add hw0, Real.rpow_one]
  have h1 : 0 < ℓ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hℓ _
  have h3 : 0 < ℓ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hℓ _
  rw [hsplit, Real.rpow_neg_one]
  calc ℓ ^ (1 / 2 : ℝ) * (w ^ (2 + ε) / (ℓ ^ (1 / 2 : ℝ) * ℓ ^ (3 / 2 : ℝ))) =
        w ^ (2 + ε) / ℓ ^ (3 / 2 : ℝ) := by field_simp
    _ ≤ w⁻¹ := by
        rw [div_le_iff₀ h3, inv_mul_eq_div, le_div_iff₀ hw0, ← hw3]
        exact h32

/-- For `|e| < 2 − κ`, `w ≥ 1`, `ℓ^{c₁} ≤ w` and `w^{2+ε} ≤ ℓ²`: the point
`z = e + i w^{2+ε}/ℓ²` lies in `𝐃(κ, c₁ε)`. -/
private theorem Assembly_mem_specDom {κ ε c₁ : ℝ} {W L : ℕ} (e : ℝ) (he : |e| < 2 - κ)
    (hW1 : 1 ≤ (W : ℝ)) (hL : 0 < (L : ℝ)) (hε : 0 < ε)
    (hadm : (L : ℝ) ^ c₁ ≤ W) (hη1 : (W : ℝ) ^ (2 + ε) ≤ (L : ℝ) ^ 2) :
    (e : ℂ) + Complex.I * ((((W : ℝ) ^ (2 + ε) / (L : ℝ) ^ 2 : ℝ)) : ℂ) ∈
      specDom κ (c₁ * ε) W L := by
  have hW0 : 0 < (W : ℝ) := by linarith
  have hre : ((e : ℂ) + Complex.I * ((((W : ℝ) ^ (2 + ε) / (L : ℝ) ^ 2 : ℝ)) : ℂ)).re = e := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; ring
  have him : ((e : ℂ) + Complex.I * ((((W : ℝ) ^ (2 + ε) / (L : ℝ) ^ 2 : ℝ)) : ℂ)).im =
      (W : ℝ) ^ (2 + ε) / (L : ℝ) ^ 2 := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; ring
  refine ⟨by rw [hre]; exact he, ?_, ?_⟩
  · rw [him]
    have hLc : (L : ℝ) ^ (c₁ * ε) ≤ (W : ℝ) ^ ε := by
      rw [Real.rpow_mul hL.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hL.le _) hadm hε.le
    have hsub : (L : ℝ) ^ (2 - c₁ * ε) = (L : ℝ) ^ 2 / (L : ℝ) ^ (c₁ * ε) := by
      rw [Real.rpow_sub hL, Real.rpow_two]
    have hLp : 0 < (L : ℝ) ^ (c₁ * ε) := Real.rpow_pos_of_pos hL _
    rw [hsub, div_div_eq_mul_div, Real.rpow_add hW0, Real.rpow_two]
    gcongr
  · rw [him, div_le_one (by positivity)]
    exact hη1

/-- For `w > 0`, `ℓ ≥ 1`, `ℓ^{c₁} ≤ w`, `C ≤ w` and `η ≥ w²/ℓ^{2−ε}`:
`C w^{-(A + 2/c₁ − 1)} ≤ ℓ^{τ/2} η w^{-A}`. -/
private theorem Assembly_absorb {w ℓ c₁ C A τ ε η : ℝ} (hw : 0 < w) (hℓ : 1 ≤ ℓ) (hc₁ : 0 < c₁)
    (hadm : ℓ ^ c₁ ≤ w) (hCw : C ≤ w) (hη : w ^ 2 / ℓ ^ (2 - ε) ≤ η) (hε : 0 ≤ ε)
    (hτ : 0 < τ) :
    C * w ^ (-(A + 2 / c₁ - 1)) ≤ ℓ ^ (τ / 2) * η * w ^ (-A) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hℓw : ℓ ≤ w ^ (1 / c₁) := by
    calc ℓ = (ℓ ^ c₁) ^ (1 / c₁) := by
          rw [← Real.rpow_mul hℓ0.le, mul_one_div_cancel hc₁.ne', Real.rpow_one]
      _ ≤ w ^ (1 / c₁) := Real.rpow_le_rpow (Real.rpow_nonneg hℓ0.le _) hadm (by positivity)
  have hℓ2 : ℓ ^ 2 ≤ w ^ (2 / c₁) := by
    calc ℓ ^ 2 ≤ (w ^ (1 / c₁)) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓw 2
      _ = w ^ (2 / c₁) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]; congr 1; push_cast; ring
  have hX : w ^ 2 / w ^ (2 / c₁) ≤ η := by
    have hle : ℓ ^ (2 - ε) ≤ ℓ ^ 2 := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le hℓ (by linarith)
    calc w ^ 2 / w ^ (2 / c₁) ≤ w ^ 2 / ℓ ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hℓ2
      _ ≤ w ^ 2 / ℓ ^ (2 - ε) :=
          div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hℓ0 _) hle
      _ ≤ η := hη
  have hX0 : 0 ≤ w ^ 2 / w ^ (2 / c₁) := by positivity
  have hsplit : w ^ (-(A + 2 / c₁ - 1)) = w ^ 2 / w ^ (2 / c₁) * w ^ (-A) * w ^ (-1 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hw, ← Real.rpow_add hw, ← Real.rpow_add hw]
    congr 1; ring
  have hCw' : C * w ^ (-1 : ℝ) ≤ 1 := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_one hw]; exact hCw
  have hWA : 0 < w ^ (-A) := Real.rpow_pos_of_pos hw _
  have hℓτ : 1 ≤ ℓ ^ (τ / 2) := Real.one_le_rpow hℓ (by positivity)
  rw [hsplit]
  calc C * (w ^ 2 / w ^ (2 / c₁) * w ^ (-A) * w ^ (-1 : ℝ)) =
        (C * w ^ (-1 : ℝ)) * (w ^ 2 / w ^ (2 / c₁) * w ^ (-A)) := by ring
    _ ≤ 1 * (w ^ 2 / w ^ (2 / c₁) * w ^ (-A)) :=
        mul_le_mul_of_nonneg_right hCw' (by positivity)
    _ ≤ 1 * (η * w ^ (-A)) := by gcongr
    _ ≤ ℓ ^ (τ / 2) * (η * w ^ (-A)) :=
        mul_le_mul_of_nonneg_right hℓτ (mul_nonneg (hX0.trans hX) hWA.le)
    _ = ℓ ^ (τ / 2) * η * w ^ (-A) := by ring

/-- For `τ > 0` and a natural number `L ≥ ⌈2^{2/τ}⌉`, `L^{τ/2} ≥ 2`. -/
private theorem Assembly_two_le_rpow {τ : ℝ} (hτ : 0 < τ) {L : ℕ}
    (hL : ⌈(2 : ℝ) ^ (2 / τ)⌉₊ ≤ L) : 2 ≤ (L : ℝ) ^ (τ / 2) := by
  have h1 : (2 : ℝ) ^ (2 / τ) ≤ L := le_trans (Nat.le_ceil _) (by exact_mod_cast hL)
  have h2 : ((2 : ℝ) ^ (2 / τ)) ^ (τ / 2) ≤ (L : ℝ) ^ (τ / 2) :=
    Real.rpow_le_rpow (by positivity) h1 (by positivity)
  rw [← Real.rpow_mul (by norm_num), show 2 / τ * (τ / 2) = 1 by field_simp,
    Real.rpow_one] at h2
  exact h2

/-- A complex number bounded by `W^{-c} + K W^{-1}` eventually along a proper filter on which
`W → ∞` is zero (`c > 0`). -/
private theorem Assembly_zero_of_eventually {F : Filter SizeL} [F.NeBot]
    (hW : Tendsto sizeW F atTop) {s : ℂ} {c K : ℝ} (hc : 0 < c)
    (h : ∀ᶠ p in F, ‖s‖ ≤ (p.1.1 : ℝ) ^ (-c) + K * (p.1.1 : ℝ) ^ (-1 : ℝ)) : s = 0 := by
  have hg : Tendsto (fun w : ℝ => w ^ (-c) + K * w ^ (-1 : ℝ)) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_neg_atTop hc
    have h2 := (tendsto_rpow_neg_atTop one_pos).const_mul K
    simpa using h1.add h2
  have := ge_of_tendsto (hg.comp hW) h
  exact norm_le_zero_iff.1 this

/-! ## `𝔖_n = 0`, [I, (8.12)] and [I, (8.11)] -/

/-- **`𝔖_n(E) = 0` for `|E| < 2`** ([I, §8, proof of Theorem 1.4]): under `H(n − 1)`, `n`-th order
`T`-equations with one `Σ_n = E` for every `D > n` and the local law `localLawTExpStmt'`, every
`𝔖 : ℝ → ℂ` with [I, (8.8)] for the row sum `R = ValZ.rowSum` of the family with `Σ_n = E`
vanishes on `(−2, 2)`. Along the sizes `L_n` of [I, (5.39)] at `c₀ = 1` and at
`z_n = E' + i W^{2+ε}/L_n²`, [I, (5.40)], [I, (8.13)] at `τ = 1/2` and [I, (8.8)] at
`D = (n−2)d/2 + 1` bound `|𝔖_n(E')|` by `W^{-c} + (1 + C) W^{-1}`. -/
theorem Assembly.sigma_eq_zero (hLL : localLawTExpStmt') (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (Strat : ℕ → ℕ → TRec → TEqRec) (n : ℕ) (hn : 4 ≤ n) (Sig : ℕ → Expansion 2)
    (E : Expansion 2) (𝒬n : ℕ → TEqRec) (hH : HWith d (smatVar P) Strat Sig (n - 1))
    (hT : ∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d (smatVar P) Sig n D (𝒬n D))
    (𝔖 : ℝ → ℂ)
    (h𝔖 : ∀ κ : ℝ, 0 < κ → ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, |e| < 2 - κ →
      ‖ValZ.rowSum (Function.update Sig n E) P.ψ n e W -
          (((W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * 𝔖 e‖ ≤ C * (W : ℝ) ^ (-D))
    (E' : ℝ) (hE' : |E'| < 2) : 𝔖 E' = 0 := by
  obtain ⟨hSE, hsh⟩ := Assembly_hyps P Strat n (by omega) Sig E 𝒬n hH hT
  have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨c, hc, ε₀, hε₀, hMC⟩ :=
    G13.mainCancel hLL d hd P Strat n hn Sig E 𝒬n hH hT 1 one_pos (by linarith)
  set ε : ℝ := min ε₀ 1 with hεdef
  have hε : 0 < ε := lt_min hε₀ one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hM := hMC ε hε (min_le_left _ _) E' hE'
  set A : ℝ := ((n : ℝ) - 2) * d / 2 with hAdef
  set a : ℝ := ((n : ℝ) - 3) * d / 2 + 1 with hadef
  have ha5 : 5 ≤ a := by
    have : (8 : ℝ) ≤ ((n : ℝ) - 3) * d := by nlinarith
    rw [hadef]; linarith
  set c₀' := G13.c0w d n 1 with hc₀'def
  set c₁' := G13.c1w d n 1 with hc₁'def
  have hb : a < ((n : ℝ) - 2) * d / 2 - 1 := by rw [hadef]; nlinarith
  have hc₀' : 0 < c₀' := by
    rw [hc₀'def, G13.c0w]; apply div_pos <;> linarith
  have hc₁' : 0 < c₁' := by
    rw [hc₁'def, G13.c1w]; apply div_pos <;> linarith
  have hc' : c₀' + c₁' < 1 := by
    rw [hc₀'def, hc₁'def, G13.c0w, G13.c1w]
    rw [div_add_div _ _ (by linarith) (by linarith), div_lt_one (by nlinarith)]
    nlinarith
  set κ : ℝ := (2 - |E'|) / 2 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have hEκ : |E'| < 2 - κ := by rw [hκdef]; linarith
  obtain ⟨C, W₀, hC⟩ := h𝔖 κ hκ (A + 1)
  obtain ⟨L₀, hL₀⟩ := VR2.rowSum d hd P n (Function.update Sig n E) hn hSE hsh κ (c₁' * ε) c₀'
    c₁' hκ (mul_pos hc₁' hε) hc₀' hc₁' hc' (1 / 2) (by norm_num)
  have hWt : Tendsto sizeW (G13.windowFilter d n 1) atTop :=
    (tendsto_sizeW_admFilterL c₀' c₁').mono_left inf_le_left
  have hadm : ∀ᶠ p in G13.windowFilter d n 1, p.1 ∈ adm c₀' c₁' := by
    refine mem_inf_of_left (Filter.mem_comap.2 ⟨adm c₀' c₁', ?_, fun p hp => hp⟩)
    exact mem_inf_of_left (mem_principal_self _)
  have hwin : ∀ᶠ p in G13.windowFilter d n 1, p ∈ G13.window d n 1 :=
    mem_inf_of_right (mem_principal_self _)
  have hbig : ∀ᶠ p in G13.windowFilter d n 1, max (max W₀ (L₀ : ℝ)) 1 ≤ sizeW p :=
    hWt.eventually (eventually_ge_atTop _)
  have := G13.windowFilter_neBot_of d n (by omega) 1 one_pos (by linarith)
  refine Assembly_zero_of_eventually hWt hc (K := 1 + C) ?_
  filter_upwards [hM, hadm, hwin, hbig] with p hp1 hp2 hp3 hp4
  set w : ℝ := (p.1.1 : ℝ) with hw
  set ℓ : ℝ := (p.1.2 : ℝ) with hℓ
  simp only [sizeW] at hp4
  have hw1 : 1 ≤ w := le_trans (le_max_right _ _) hp4
  have hwW₀ : W₀ ≤ w := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hp4
  have hwL₀ : (L₀ : ℝ) ≤ w := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hp4
  have hw0 : 0 < w := by linarith
  have hℓ0 : 0 < ℓ := Nat.cast_pos.2 (Nat.pos_of_ne_zero p.2)
  have hwin1 : w ^ a ≤ ℓ ^ 2 / w ^ 2 := hp3.1
  have hQ : w ^ (a + 2) ≤ ℓ ^ 2 := by
    rw [Real.rpow_add hw0, Real.rpow_two]
    rwa [le_div_iff₀ (by positivity)] at hwin1
  have hη1 : w ^ (2 + ε) ≤ ℓ ^ 2 :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)) hQ
  have hwℓ : w ≤ ℓ := by
    have h2 : w ^ 2 ≤ ℓ ^ 2 := by
      rw [← Real.rpow_two]
      exact le_trans (Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)) hQ
    exact (pow_le_pow_iff_left₀ hw0.le hℓ0.le two_ne_zero).1 h2
  have hL : L₀ ≤ p.1.2 := by
    have h := hwL₀.trans hwℓ
    rw [hℓ] at h
    exact_mod_cast h
  have hz := Assembly_mem_specDom (κ := κ) E' hEκ hw1 hℓ0 hε hp2.1 hη1
  have hV := hL₀ p.1.1 p.1.2 hL hp2 _ hz
  have hR := hC p.1.1 hwW₀ E' hEκ
  have hre : ((E' : ℂ) + Complex.I * (((w ^ (2 + ε) / ℓ ^ 2 : ℝ)) : ℂ)).re = E' := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; ring
  have him : ((E' : ℂ) + Complex.I * (((w ^ (2 + ε) / ℓ ^ 2 : ℝ)) : ℂ)).im =
      w ^ (2 + ε) / ℓ ^ 2 := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]; ring
  rw [hre, him] at hV
  have hmid := Assembly_mid hw1 hℓ0 ha5 hε1 hwin1
  set S := ∑ x : Zd d p.1.2, sigMat (Function.update Sig n E) (smatVar P p.1.1 p.1.2)
    ((E' : ℂ) + Complex.I * (((w ^ (2 + ε) / ℓ ^ 2 : ℝ)) : ℂ)) n 0 x with hS
  set R := ValZ.rowSum (Function.update Sig n E) P.ψ n E' p.1.1 with hRdef
  have hWA : 0 < w ^ (-A) := Real.rpow_pos_of_pos hw0 _
  have hnorm : ‖(((w ^ (-A) : ℝ)) : ℂ) * 𝔖 E'‖ = w ^ (-A) * ‖𝔖 E'‖ := by
    rw [norm_mul, Complex.norm_of_nonneg hWA.le]
  have htri : ‖(((w ^ (-A) : ℝ)) : ℂ) * 𝔖 E'‖ ≤
      ‖S‖ + ‖S - R‖ + ‖R - (((w ^ (-A) : ℝ)) : ℂ) * 𝔖 E'‖ := by
    have e : (((w ^ (-A) : ℝ)) : ℂ) * 𝔖 E' =
        S - (S - R) - (R - (((w ^ (-A) : ℝ)) : ℂ) * 𝔖 E') := by ring
    exact (congrArg norm e).le.trans
      ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl))
  have e1 : w ^ (-A - c) = w ^ (-A) * w ^ (-c) := by
    rw [sub_eq_add_neg, Real.rpow_add hw0]
  have e2 : w ^ (-(A + 1)) = w ^ (-A) * w ^ (-1 : ℝ) := by
    rw [neg_add, Real.rpow_add hw0]
  have key : w ^ (-A) * ‖𝔖 E'‖ ≤ w ^ (-A) * (w ^ (-c) + (1 + C) * w ^ (-1 : ℝ)) := by
    rw [← hnorm]
    calc ‖(((w ^ (-A) : ℝ)) : ℂ) * 𝔖 E'‖
        ≤ ‖S‖ + ‖S - R‖ + ‖R - (((w ^ (-A) : ℝ)) : ℂ) * 𝔖 E'‖ := htri
      _ ≤ w ^ (-A - c) + ℓ ^ (1 / 2 : ℝ) * (w ^ (2 + ε) / ℓ ^ 2) * w ^ (-A) +
            C * w ^ (-(A + 1)) := add_le_add (add_le_add hp1 hV) hR
      _ = w ^ (-A) * (w ^ (-c) + ℓ ^ (1 / 2 : ℝ) * (w ^ (2 + ε) / ℓ ^ 2) +
            C * w ^ (-1 : ℝ)) := by rw [e1, e2]; ring
      _ ≤ w ^ (-A) * (w ^ (-c) + w ^ (-1 : ℝ) + C * w ^ (-1 : ℝ)) := by gcongr
      _ = w ^ (-A) * (w ^ (-c) + (1 + C) * w ^ (-1 : ℝ)) := by ring
  exact le_of_mul_le_mul_left key hWA

/-- **[I, (8.12)]**: under the hypotheses of `Assembly.sigma_eq_zero`, the row sum
`R(E, W) = Σ_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)` (`ValZ.rowSum`) of the family with `Σ_n = E` satisfies
`|R(E, W)| ≤ C W^{-D}` for every `κ > 0` and `D`, `W ≥ W₀(κ, D)` and `|E| < 2 − κ`: [I, (8.8)]
with `𝔖_n = 0`. -/
theorem Assembly.rowSum_decay (hLL : localLawTExpStmt') (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (Strat : ℕ → ℕ → TRec → TEqRec) (n : ℕ) (hn : 4 ≤ n) (Sig : ℕ → Expansion 2)
    (E : Expansion 2) (𝒬n : ℕ → TEqRec) (hH : HWith d (smatVar P) Strat Sig (n - 1))
    (hT : ∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d (smatVar P) Sig n D (𝒬n D)) :
    ∀ κ : ℝ, 0 < κ → ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, |e| < 2 - κ →
      ‖ValZ.rowSum (Function.update Sig n E) P.ψ n e W‖ ≤ C * (W : ℝ) ^ (-D) := by
  obtain ⟨hSE, hsh⟩ := Assembly_hyps P Strat n (by omega) Sig E 𝒬n hH hT
  have hSh : SelfEnergyShapesUpTo (Function.update Sig n E) (n - 1) :=
    fun k h4 hk he => (hSE k h4 hk he).1
  obtain ⟨𝔖, h𝔖⟩ := FT1c.rowSumExpand d hd P n _ hn hSh hsh
  intro κ hκ D
  obtain ⟨C, W₀, hC⟩ := h𝔖 κ hκ D
  refine ⟨C, W₀, fun W hW e he => ?_⟩
  have h0 := Assembly.sigma_eq_zero hLL d hd P Strat n hn Sig E 𝒬n hH hT 𝔖 h𝔖 e (by linarith)
  simpa [h0] using hC W hW e he

/-- **[I, (8.11)]** on the whole domain `𝐃(κ, ε)`: under the hypotheses of
`Assembly.sigma_eq_zero`, for all `κ, ε, c₀, c₁ > 0` with `c₀ + c₁ < 1` and every `τ > 0` there is
`L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)` and `z ∈ 𝐃(κ, ε)`,
`|Σ_x Σ_n(0, x)(z)| ≤ L^τ η W^{-(n-2)d/2}` for the family with `Σ_n = E`. [I, (8.13)] at `τ/2`
compares the row sum with `R(Re z, W)`, and [I, (8.12)] at `D = (n−2)d/2 + 2/c₁ − 1` bounds
`R(Re z, W)` by `L^{τ/2} η W^{-(n-2)d/2}`, since `η ≥ W²/L² ≥ W^{2−2/c₁}` on `adm(c₀, c₁)`. -/
theorem Assembly.rowSumBound (hLL : localLawTExpStmt') (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (Strat : ℕ → ℕ → TRec → TEqRec) (n : ℕ) (hn : 4 ≤ n) (Sig : ℕ → Expansion 2)
    (E : Expansion 2) (𝒬n : ℕ → TEqRec) (hH : HWith d (smatVar P) Strat Sig (n - 1))
    (hT : ∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d (smatVar P) Sig n D (𝒬n D)) :
    ∀ κ ε c₀ c₁ : ℝ, 0 < κ → 0 < ε → 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L,
          ‖∑ x : Zd d L, sigMat (Function.update Sig n E) (smatVar P W L) z n 0 x‖ ≤
            (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) := by
  intro κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  obtain ⟨hSE, hsh⟩ := Assembly_hyps P Strat n (by omega) Sig E 𝒬n hH hT
  set A : ℝ := ((n : ℝ) - 2) * d / 2 with hAdef
  obtain ⟨C, W₀, hC⟩ := Assembly.rowSum_decay hLL d hd P Strat n hn Sig E 𝒬n hH hT κ hκ
    (A + 2 / c₁ - 1)
  obtain ⟨L₂, h₂⟩ := VR2.rowSum d hd P n _ hn hSE hsh κ ε c₀ c₁ hκ hε hc₀ hc₁ hc (τ / 2)
    (half_pos hτ)
  set M : ℝ := max (max C W₀) 1 with hMdef
  refine ⟨max (max L₂ ⌈(2 : ℝ) ^ (2 / τ)⌉₊) ⌈M ^ (1 / c₁)⌉₊, fun W L _ hL hadm z hz => ?_⟩
  have hL₂ : L₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL₃ : ⌈(2 : ℝ) ^ (2 / τ)⌉₊ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL₄ : ⌈M ^ (1 / c₁)⌉₊ ≤ L := le_trans (le_max_right _ _) hL
  have hℓ1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMw : M ≤ (W : ℝ) :=
    calc M = (M ^ (1 / c₁)) ^ c₁ := by
          rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hc₁.ne', Real.rpow_one]
      _ ≤ (L : ℝ) ^ c₁ := Real.rpow_le_rpow (by positivity)
          (le_trans (Nat.le_ceil _) (by exact_mod_cast hL₄)) hc₁.le
      _ ≤ W := hadm.1
  have hw0 : 0 < (W : ℝ) := by linarith
  have hCw : C ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMw
  have hW₀ : W₀ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMw
  have hR := hC W hW₀ z.re hz.1
  have hV := h₂ W L hL₂ hadm z hz
  have habs := Assembly_absorb (A := A) hw0 hℓ1 hc₁ hadm.1 hCw hz.2.1 hε.le hτ
  have h2 := Assembly_two_le_rpow hτ hL₃
  set S := ∑ x : Zd d L, sigMat (Function.update Sig n E) (smatVar P W L) z n 0 x with hS
  set R := ValZ.rowSum (Function.update Sig n E) P.ψ n z.re W with hRdef
  set Y := (L : ℝ) ^ (τ / 2) * z.im * (W : ℝ) ^ (-A) with hYdef
  have hY : 0 ≤ Y := le_trans (norm_nonneg _) hV
  have hLpos : (0 : ℝ) < L := by linarith
  calc ‖S‖ = ‖(S - R) + R‖ := by rw [sub_add_cancel]
    _ ≤ ‖S - R‖ + ‖R‖ := norm_add_le _ _
    _ ≤ Y + Y := add_le_add hV (hR.trans habs)
    _ = 2 * Y := by ring
    _ ≤ (L : ℝ) ^ (τ / 2) * Y := mul_le_mul_of_nonneg_right h2 hY
    _ = (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-A) := by
        rw [hYdef, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hLpos, add_halves]

/-! ## [I, (1.26)–(1.27)] for `Σ_n` -/

/-- **[II, Lemma 3.9] = [I, Lemma 5.8], the bound part** (`G13.selfEnergyStepEndStmt`): under the
local law `localLawTExpStmt'`, for `d ≥ 8`, every profile `P`, even `n ≥ 4`, `H(n − 1)` and
`n`-th order `T`-equations with one `Σ_n = E` for every `D > n`, the family with `Σ_n = E`
satisfies [I, (1.26)] with the diagonal term (`G13.entrywise`) and [I, (1.27)]
(`Assembly.rowSumBound`) for `Σ_n`, with one `L₀` for both. -/
theorem G13.selfEnergyStepEnd : G13.selfEnergyStepEndStmt := by
  intro hLL d hd P Strat n hn _ Sig E 𝒬n hH hT κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  obtain ⟨hSE, hsh⟩ := Assembly_hyps P Strat n (by omega) Sig E 𝒬n hH hT
  obtain ⟨L₁, h₁⟩ := G13.entrywise d hd P n _ hn hSE hsh κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  obtain ⟨L₂, h₂⟩ := Assembly.rowSumBound hLL d hd P Strat n hn Sig E 𝒬n hH hT κ ε c₀ c₁ hκ hε
    hc₀ hc₁ hc τ hτ
  exact ⟨max L₁ L₂, fun W L _ hL hadm z hz =>
    ⟨h₁ W L (le_trans (le_max_left _ _) hL) hadm z hz,
      h₂ W L (le_trans (le_max_right _ _) hL) hadm z hz⟩⟩

end RBM8D.Graphs
