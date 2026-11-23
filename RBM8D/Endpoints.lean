module

public import Batteries.Tactic.OpenPrivate
public import RBM8D.LocalLaw.Cutoff.Assembly
public import RBM8D.GlobalExp.TEquation
public import RBM8D.Deloc.Thm13
public import RBM8D.Diffusion.Main
public import RBM8D.Diffusion.Fourier
import all RBM8D.Deloc.Thm13
import all RBM8D.Diffusion.Fourier

@[expose] public section

/-!
# The endpoints: [I, Theorems 1.3, 1.4, 1.5], [I, Corollaries 1.6, 1.7]

[II, Theorem 3.6] is `localLawTExp_cutoff` and [II, Lemma 3.9] is `Assembly.selfEnergyStep'`.

* `G14.localLaw_of_parts'`: the local law [I, Theorem 1.4], (1.19) (`LocalLawStmt`) from the three
  statements of [II, Theorem 3.7, Lemma 3.9, Corollary 3.8].
* `G14.inst_localLawComp'`: the same with [II, Corollary 3.8] given by `solve`.
* `G14.localLaw_of_tEq'`: the local law from the `T`-equation [II, Theorem 3.7]
  (`tEquationStmt`).
* `thm13_eq112_of'`, `thm13_eq113_of'`, `thm13_of'`: [I, Theorem 1.3], (1.12), (1.13) and both
  jointly, from `tEquationStmt`.
* `localLaw : LocalLawStmt`: [I, Theorem 1.4].
* `thm13 : Thm13Stmt`: [I, Theorem 1.3].
* `quantumDiffusion : quantumDiffusionStmt`: [I, Theorem 1.5], [I, Corollary 1.6] and
  [I, Corollary 1.7].

Instances at `d = 8` and the Gaussian profile: the local law at `W = n`, `L = n⁴`; [I, Theorem 1.3]
at `W = ℓ = n`, `L = n⁴`; quantum diffusion at `W ≥ 4096`, `L = W²`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Complex Matrix

namespace RBM8D

open Graphs

open private Thm13_of_parts from RBM8D.Deloc.Thm13
open private norm_zfreq_le from RBM8D.Diffusion.Fourier

/-! ## The local law and [I, Theorem 1.3] from the `T`-equation -/

/-- **[I, Theorem 1.4], (1.19)** from the three statements of [II, Theorem 3.7, Lemma 3.9,
Corollary 3.8] for the variance family `smatVar P`: the joint induction gives a `T`-expansion of
every order `n ≥ 2` and every error order `D ≥ n + 2` (`G14.jointH_of_parts`,
`G14.family_of_jointH`); [II, Theorem 3.6] in the form `localLawTExpStmt'` is
`localLawTExp_cutoff`; the local law is `G14.localLaw_of_tExp`. -/
theorem G14.localLaw_of_parts' (hT : tEquationStmt)
    (hS : ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, selfEnergyStepStmt d (smatVar P))
    (hV : ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, solveStmt d (smatVar P)) : LocalLawStmt :=
  G14.localLaw_of_tExp localLawTExp_cutoff
    fun d hd P n hn D hD => by
      obtain ⟨Strat, hJ⟩ := G14.jointH_of_parts hT (smatVar P) (hS d hd P) (hV d hd P)
      obtain ⟨Sig, hF⟩ := G14.family_of_jointH hJ
      obtain ⟨𝒯, h1, h2⟩ := hF n hn D hD
      exact ⟨Sig, 𝒯, h1, h2⟩

/-- **[I, Theorem 1.4]** from the `T`-equation ([II, Theorem 3.7], `tEquationStmt`) and the
self-energy step ([II, Lemma 3.9], `selfEnergyStepStmt` at `smatVar P`); [II, Corollary 3.8] is
`solve`. -/
theorem G14.inst_localLawComp' (hT : tEquationStmt)
    (hSE : ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, selfEnergyStepStmt d (smatVar P)) : LocalLawStmt :=
  G14.localLaw_of_parts' hT hSE (fun d _ P => solve d (smatVar P))

/-- **[I, Theorem 1.4], (1.19)** from [II, Theorem 3.7] in the form `tEquationStmt`: the
self-energy step [II, Lemma 3.9] is `Assembly.selfEnergyStep'`, and [II, Corollary 3.8] is
`solve`. -/
theorem G14.localLaw_of_tEq' (hT : tEquationStmt) : LocalLawStmt :=
  G14.localLaw_of_parts' hT (fun d hd P => Assembly.selfEnergyStep' d hd P)
    (fun d _ P => solve d (smatVar P))

/-- **[I, Theorem 1.3], (1.12)** from [II, Theorem 3.7] (`tEquationStmt`). -/
theorem thm13_eq112_of' (hT : tEquationStmt) : Thm13_eq112Stmt :=
  thm13_eq112_ofLocalLaw (G14.localLaw_of_tEq' hT)

/-- **[I, Theorem 1.3], (1.13)** from [II, Theorem 3.7] (`tEquationStmt`). -/
theorem thm13_eq113_of' (hT : tEquationStmt) : Thm13_eq113Stmt :=
  thm13_eq113_ofLocalLaw (G14.localLaw_of_tEq' hT)

/-- **[I, Theorem 1.3]**, (1.12) and (1.13) jointly with one threshold `L₀`, from
[II, Theorem 3.7] (`tEquationStmt`). -/
theorem thm13_of' (hT : tEquationStmt) : Thm13Stmt :=
  Thm13_of_parts (thm13_eq112_of' hT) (thm13_eq113_of' hT)

/-! ## The endpoints -/

/-- [I, Theorem 1.4]. -/
theorem localLaw : LocalLawStmt :=
  G14.localLaw_of_tEq' tEquation

/-- [I, Theorem 1.3]. -/
theorem thm13 : Thm13Stmt :=
  thm13_of' tEquation

/-- [I, Theorem 1.5], [I, Corollary 1.6], [I, Corollary 1.7]. -/
theorem quantumDiffusion : quantumDiffusionStmt :=
  quantumDiffusion_of localLaw fun d hd P =>
    G14.jointH_of_parts tEquation (smatVar P) (Assembly.selfEnergyStep' d hd P)
      (solve d (smatVar P))

/-! ## Compiled instances -/

example : LocalLawStmt := localLaw

example : Thm13Stmt := thm13

example : quantumDiffusionStmt := quantumDiffusion

/-- `(w⁴)^a = w^{4a}` for `w ≥ 0`. -/
private theorem Endpoints_pow4_rpow (w a : ℝ) (hw : 0 ≤ w) : (w ^ 4) ^ a = w ^ (4 * a) := by
  rw [← Real.rpow_natCast w 4, ← Real.rpow_mul hw]
  norm_num

/-- `localLaw` at `d = 8`, the Gaussian profile `ψ(p) = e^{−|p|²/2}` of `G11.inst_endpointHyp`,
`c₀ = c₁ = 1/4`, `κ = ε = 1/2`, `τ = D = 1`, at `W = n`, `L = n⁴` with `n = max(L₀, 2)` and
`x = y = 0`: `(W, L) ∈ adm(1/4, 1/4)` (`L^{1/4} = W ≤ L^{3/4}`), the window
`[W²/L^{3/2}, 1] = [n^{−4}, 1]` of `η` is not collapsed, the bound `L^{−1} = n^{−4}` is `< 1`, and
the probability bound of (1.19) holds there. -/
example : ∃ (P : Profile 8) (p : SizeL), 2 ≤ p.1.1 ∧ p.1.2 = p.1.1 ^ 4 ∧
    p.1 ∈ adm (1 / 4) (1 / 4) ∧ (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - 1 / 2 : ℝ) < 1 ∧
    (p.1.2 : ℝ) ^ (-1 : ℝ) < 1 ∧
    rbmLaw 8 P p {ω | ∃ E : ℝ, E ∈ Set.Ioo (-2 + 1 / 2) (2 - 1 / 2) ∧ ∃ η : ℝ,
        (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - 1 / 2 : ℝ) ≤ η ∧ η ≤ 1 ∧
        (p.1.1 : ℝ) ^ (1 : ℝ) * bB 8 p.1.2 p.1.1 0 0 <
          ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * I)) (msc ((E : ℂ) + (η : ℂ) * I))
            0 0‖ ^ 2}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-1 : ℝ)) := by
  obtain ⟨P, -⟩ := G11.inst_endpointHyp
  obtain ⟨L₀, hL₀⟩ := localLaw 8 le_rfl P (1 / 4) (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (1 / 2) 1 1 (by norm_num) one_pos one_pos
  set n : ℕ := max L₀ 2 with hn
  have hn2 : 2 ≤ n := le_max_right _ _
  have hnL : L₀ ≤ n ^ 4 :=
    (le_max_left L₀ 2).trans (Nat.le_self_pow (by norm_num) _)
  have hL0 : n ^ 4 ≠ 0 := pow_ne_zero 4 (by omega)
  set w : ℝ := (n : ℝ) with hw
  have hw2 : (2 : ℝ) ≤ w := by rw [hw]; exact_mod_cast hn2
  have hw0 : (0 : ℝ) < w := by linarith
  have hcast : ((n ^ 4 : ℕ) : ℝ) = w ^ 4 := by rw [hw]; push_cast; ring
  have h34 : (w ^ 4) ^ (1 - 1 / 4 : ℝ) = w ^ 3 := by
    rw [Endpoints_pow4_rpow w _ hw0.le]; norm_num
  have h14 : (w ^ 4) ^ (1 / 4 : ℝ) = w := by
    rw [Endpoints_pow4_rpow w _ hw0.le]; norm_num
  have h32 : (w ^ 4) ^ (2 - 1 / 2 : ℝ) = w ^ 6 := by
    rw [Endpoints_pow4_rpow w _ hw0.le]; norm_num
  have hm1 : (w ^ 4) ^ (-1 : ℝ) = (w ^ 4)⁻¹ := Real.rpow_neg_one _
  let p : SizeL := ⟨(n, n ^ 4), hL0⟩
  have hp1 : (p.1.1 : ℝ) = w := rfl
  have hp2 : (p.1.2 : ℝ) = w ^ 4 := hcast
  have hadm : p.1 ∈ adm (1 / 4) (1 / 4) := by
    refine ⟨?_, ?_⟩
    · rw [hp1, hp2, h14]
    · rw [hp1, hp2, h34]
      have h1 : (1 : ℝ) ≤ w ^ 2 := by nlinarith
      calc w = w * 1 := (mul_one w).symm
        _ ≤ w * w ^ 2 := mul_le_mul_of_nonneg_left h1 hw0.le
        _ = w ^ 3 := by ring
  refine ⟨P, p, hn2, rfl, hadm, ?_, ?_, hL₀ p hnL hadm 0 0⟩
  · rw [hp1, hp2, h32, div_lt_one (by positivity)]
    nlinarith [pow_pos hw0 2, pow_pos hw0 3, pow_pos hw0 4, pow_pos hw0 5]
  · rw [hp2, hm1, inv_lt_one₀ (by positivity)]
    exact one_lt_pow₀ (by linarith) (by norm_num)

/-- `thm13` at `d = 8`, the Gaussian profile of `G11.inst_endpointHyp`, `c₀ = c₁ = 1/4`,
`κ = 1/2`, `γ = 1`, `K = 2`, `τ = D = 1`, at `W = ℓ = n`, `L = n⁴` with `n = max(L₀, 2)`: the
window `[W, L^{3/4}] = [n, n³]` is not collapsed, `L^{1/4} = W < L`, the threshold
`W(ℓ²/L² + W^{−4}) = n^{−5} + n^{−3}` of (1.12) is `< 1`, the threshold `W²/L = n^{−2}` of (1.13)
lies in `(L^{−4}, 1) = (N^{−1/2}, 1)`, and the bound `L^{−1} = n^{−4}` is `< 1`; both probability
bounds hold there. -/
example :
    ∃ (P : Profile 8) (p : SizeL) (ℓ : ℝ), 2 ≤ p.1.1 ∧ p.1.2 = p.1.1 ^ 4 ∧ ℓ = p.1.1 ∧
      (p.1.1 : ℝ) < (p.1.2 : ℝ) ^ (1 - 1 / 4 : ℝ) ∧
      (p.1.2 : ℝ) ^ (1 / 4 : ℝ) ≤ p.1.1 ∧ p.1.1 < p.1.2 ∧
      (p.1.1 : ℝ) ^ (1 : ℝ) * (ℓ ^ 2 / (p.1.2 : ℝ) ^ 2 + (p.1.1 : ℝ) ^ (-((8 : ℕ) : ℝ) / 2)) < 1 ∧
      (p.1.2 : ℝ) ^ (-((8 : ℕ) : ℝ) / 2) < (p.1.1 : ℝ) ^ (1 + 1 : ℝ) / (p.1.2 : ℝ) ∧
      (p.1.1 : ℝ) ^ (1 + 1 : ℝ) / (p.1.2 : ℝ) < 1 ∧
      (p.1.2 : ℝ) ^ (-1 : ℝ) < 1 ∧
      rbmLaw 8 P p {ω | ∃ (u : Zd 8 p.1.2 → Zd 8 p.1.2 → ℂ) (lam : Zd 8 p.1.2 → ℝ),
          IsOrthoEigenbasis (hmat ω) u lam ∧
          (p.1.1 : ℝ) ^ (1 : ℝ) * (ℓ ^ 2 / (p.1.2 : ℝ) ^ 2 +
              (p.1.1 : ℝ) ^ (-((8 : ℕ) : ℝ) / 2)) <
            ((locSetB 8 p.1.2 (1 / 2) 1 2 ℓ u lam).card : ℝ) / (p.1.2 : ℝ) ^ 8}
        ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-1 : ℝ)) ∧
      rbmLaw 8 P p {ω | ∃ lam : ℝ, lam ∈ Set.Ioo (-2 + 1 / 2) (2 - 1 / 2) ∧
          ∃ u : Zd 8 p.1.2 → ℂ, ∑ x, ‖u x‖ ^ 2 = 1 ∧ hmat ω *ᵥ u = (lam : ℂ) • u ∧
          ∃ x, (p.1.1 : ℝ) ^ (1 + 1 : ℝ) / (p.1.2 : ℝ) < ‖u x‖}
        ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-1 : ℝ)) := by
  obtain ⟨P, -⟩ := G11.inst_endpointHyp
  obtain ⟨L₀, hL₀⟩ := thm13 8 le_rfl P (1 / 4) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) 1 2 one_pos le_rfl one_lt_two 1 1 one_pos one_pos
  set n : ℕ := max L₀ 2 with hn
  have hn2 : 2 ≤ n := le_max_right _ _
  have hnL : L₀ ≤ n ^ 4 :=
    (le_max_left L₀ 2).trans (Nat.le_self_pow (by norm_num) _)
  have hL0 : n ^ 4 ≠ 0 := pow_ne_zero 4 (by omega)
  set w : ℝ := (n : ℝ) with hw
  have hw2 : (2 : ℝ) ≤ w := by rw [hw]; exact_mod_cast hn2
  have hw0 : (0 : ℝ) < w := by linarith
  have hcast : ((n ^ 4 : ℕ) : ℝ) = w ^ 4 := by rw [hw]; push_cast; ring
  have h34 : (w ^ 4) ^ (1 - 1 / 4 : ℝ) = w ^ 3 := by
    rw [Endpoints_pow4_rpow w _ hw0.le]; norm_num
  have h14 : (w ^ 4) ^ (1 / 4 : ℝ) = w := by
    rw [Endpoints_pow4_rpow w _ hw0.le]; norm_num
  have hm4 : w ^ (-((8 : ℕ) : ℝ) / 2) = (w ^ 4)⁻¹ := by
    rw [show (-((8 : ℕ) : ℝ) / 2) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hw0.le,
      Real.rpow_natCast]
  have hm16 : (w ^ 4) ^ (-((8 : ℕ) : ℝ) / 2) = ((w ^ 4) ^ 4)⁻¹ := by
    rw [show (-((8 : ℕ) : ℝ) / 2) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
  have h2 : w ^ (1 + 1 : ℝ) = w ^ 2 := by
    rw [show (1 + 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hm1 : (w ^ 4) ^ (-1 : ℝ) = (w ^ 4)⁻¹ := Real.rpow_neg_one _
  let p : SizeL := ⟨(n, n ^ 4), hL0⟩
  have hp1 : (p.1.1 : ℝ) = w := rfl
  have hp2 : (p.1.2 : ℝ) = w ^ 4 := hcast
  have hw4 : w < w ^ 4 := by nlinarith [pow_pos hw0 2, pow_pos hw0 3]
  obtain ⟨h12, h13⟩ := hL₀ p (n : ℝ) hnL le_rfl
    (by rw [hp2, h34]; nlinarith) (by rw [hp2, h14]) (Nat.le_self_pow (by norm_num) _)
  refine ⟨P, p, (n : ℝ), hn2, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h12, h13⟩
  · rw [hp1, hp2, h34]; nlinarith
  · rw [hp1, hp2, h14]
  · exact_mod_cast (show (p.1.1 : ℝ) < p.1.2 by rw [hp1, hp2]; exact hw4)
  · rw [hp1, hp2, hm4, Real.rpow_one]
    rw [show w * (w ^ 2 / (w ^ 4) ^ 2 + (w ^ 4)⁻¹) = (1 + w ^ 2) / w ^ 5 by field_simp,
      div_lt_one (by positivity)]
    have h8 : 8 ≤ w ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hw2 3]
    nlinarith [pow_pos hw0 2, mul_le_mul_of_nonneg_right h8 (pow_pos hw0 2).le]
  · rw [hp1, hp2, hm16, h2, lt_div_iff₀ (by positivity)]
    rw [show ((w ^ 4) ^ 4)⁻¹ * w ^ 4 = ((w ^ 4) ^ 3)⁻¹ by field_simp]
    have h1 : 1 < (w ^ 4) ^ 3 := one_lt_pow₀ (by nlinarith [pow_pos hw0 2]) (by norm_num)
    have h2' : 1 < w ^ 2 := by nlinarith
    calc ((w ^ 4) ^ 3)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
      _ < w ^ 2 := h2'
  · rw [hp1, hp2, h2, div_lt_one (by positivity)]
    nlinarith [pow_pos hw0 2]
  · rw [hp2, hm1, inv_lt_one₀ (by positivity)]
    nlinarith [pow_pos hw0 2]

/-- `quantumDiffusion` at `d = 8`, the Gaussian profile of `G11.inst_endpointHyp`,
`(c₀, c₁, κ, ε) = (1/10, 2/5, 1/10, 1/10)`, `M = 10`, `τ = δ = 1/2`. For the thresholds of the
three conclusions, the point `W ≥ 4096`, `L = W²` lies in `adm(1/10, 2/5)` with `W^{10} ≥ L⁴`,
`z = i ∈ 𝐃(1/10, 1/10)`, and `η = W^{−1}`, `k = e₁ ≠ 0` lie in the window of
[I, Corollary 1.7]. There: `1 − |m|² S (1 + Σ̃^{(10)})` is invertible, (1.24) and (1.28) hold at
`x = y = 0`, (1.22) holds at `x = y = 0`, and (1.36) holds at `p = 2π e₁/L`. -/
example :
    ∃ (P : Profile 8) (Sg : SigmaFam 8) (Gc : LocCorr 8) (C : ℝ) (W L : ℕ) (_ : NeZero L)
      (k : Zd 8 L), 4096 ≤ W ∧ L = W ^ 2 ∧ k ≠ 0 ∧ (∃ Sig, SigmaOf 8 P Sig Sg) ∧
      (W, L) ∈ adm (1 / 10) (2 / 5) ∧ I ∈ specDom (1 / 10) (1 / 10) W L ∧
      (L : ℝ) ^ 4 ≤ (W : ℝ) ^ 10 ∧
      (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - 1 / 10 : ℝ) ≤ (W : ℝ)⁻¹ ∧
      (W : ℝ)⁻¹ ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) ∧ ‖zfreq k‖ ≤ (W : ℝ) ^ (-1 - 1 / 2 : ℝ) ∧
      IsUnit (1 - amat (Smat P.ψ W L) I * (1 + sigTildeM Sg 10 W L I)) ∧
      ‖thetaM (Smat P.ψ W L) (1 + sigTildeM Sg 10 W L I) I 0 0‖ ≤
        (L : ℝ) ^ (1 / 2 : ℝ) * bB 8 L W 0 0 ∧
      ‖Gc W L I 0 0‖ ≤ (L : ℝ) ^ (1 / 2 : ℝ) * bB 8 L W 0 0 ^ ((3 : ℝ) / 2) ∧
      ‖(expT 8 P W L I 0 0 : ℂ) - (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg 10 W L I) I *
          (mAbs2 I • 1 + Gc W L I)) 0 0‖ ≤ C * (W : ℝ) ^ (-(((10 : ℕ) : ℝ) * (8 : ℕ) / 2)) ∧
      ∃ e₁ e₂ e₃ : ℂ, ‖e₁‖ ≤ C * (W : ℝ) ^ (-(((8 : ℕ) : ℝ) / 2) + 1 / 2) ∧
        ‖e₂‖ ≤ C * (((W : ℝ)⁻¹) ^ 2 + (W : ℝ) ^ (-((8 : ℕ) : ℝ) + 1 / 2) * (W : ℝ)⁻¹ +
          (W : ℝ) ^ 3 * ‖zfreq k‖ ^ 3) ∧
        ‖e₃‖ ≤ C * (W : ℝ) ^ (-((10 : ℕ) : ℝ)) ∧
        ((((W : ℝ)⁻¹ : ℝ) : ℂ) + qform W k (diffEff P Sg 10 W L
          (((0 : ℝ) : ℂ) + (((W : ℝ)⁻¹ : ℝ) : ℂ) * I)) + e₂ ≠ 0) ∧
        ∑ x, zchar k x * (expG2 8 P W L (((0 : ℝ) : ℂ) + (((W : ℝ)⁻¹ : ℝ) : ℂ) * I) 0 x : ℂ) =
          (rE 0 : ℂ) * (mAbs2 (((0 : ℝ) : ℂ) + (((W : ℝ)⁻¹ : ℝ) : ℂ) * I) + e₁) /
            ((((W : ℝ)⁻¹ : ℝ) : ℂ) + qform W k (diffEff P Sg 10 W L
              (((0 : ℝ) : ℂ) + (((W : ℝ)⁻¹ : ℝ) : ℂ) * I)) + e₂) + e₃ := by
  obtain ⟨P, -⟩ := G11.inst_endpointHyp
  obtain ⟨Sg, hSig, hM⟩ := quantumDiffusion 8 le_rfl P (1 / 10) (2 / 5) (1 / 10)
    (1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Gc, ⟨h15a, h15b⟩, h17⟩ := hM 10
  obtain ⟨L₁, hL₁⟩ := h15a (1 / 2) (by norm_num)
  obtain ⟨C₁, L₂, hL₂⟩ := h15b
  obtain ⟨C₂, L₃, hL₃⟩ := h17 (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨W, hW4n, hWL₁, hWL₂, hWL₃⟩ : ∃ W : ℕ, 4096 ≤ W ∧ L₁ ≤ W ∧ L₂ ≤ W ∧ L₃ ≤ W :=
    ⟨L₁ + L₂ + L₃ + 4096, by omega, by omega, by omega, by omega⟩
  have hL : NeZero (W ^ 2) := ⟨by positivity⟩
  have hW4 : (4096 : ℝ) ≤ W := by exact_mod_cast hW4n
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hLc : ((W ^ 2 : ℕ) : ℝ) = (W : ℝ) ^ (2 : ℝ) := by push_cast; rw [Real.rpow_two]
  have hp : ∀ a : ℝ, ((W : ℝ) ^ (2 : ℝ)) ^ a = (W : ℝ) ^ (2 * a) := fun a =>
    (Real.rpow_mul hW0.le 2 a).symm
  have hadm : (W, W ^ 2) ∈ adm (1 / 10) (2 / 5) := by
    refine ⟨?_, ?_⟩
    · change ((W ^ 2 : ℕ) : ℝ) ^ (2 / 5 : ℝ) ≤ W
      rw [hLc, hp]
      calc (W : ℝ) ^ (2 * (2 / 5) : ℝ) ≤ (W : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
        _ = W := Real.rpow_one _
    · change (W : ℝ) ≤ ((W ^ 2 : ℕ) : ℝ) ^ (1 - 1 / 10 : ℝ)
      rw [hLc, hp]
      calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hz : I ∈ specDom (1 / 10) (1 / 10) W (W ^ 2) := by
    refine ⟨by simp; norm_num, ?_, by simp⟩
    rw [Complex.I_im, hLc, hp, div_le_iff₀ (by positivity), one_mul]
    calc (W : ℝ) ^ 2 = (W : ℝ) ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ ≤ (W : ℝ) ^ (2 * (2 - 1 / 10) : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hL4 : (((W ^ 2 : ℕ) : ℝ)) ^ 4 ≤ (W : ℝ) ^ 10 := by
    push_cast
    rw [← pow_mul]
    exact pow_le_pow_right₀ hW1 (by norm_num)
  have hinv : (W : ℝ)⁻¹ = (W : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]
  have hw1 : (W : ℝ) ^ 2 / ((W ^ 2 : ℕ) : ℝ) ^ (2 - 1 / 10 : ℝ) ≤ (W : ℝ)⁻¹ := by
    rw [hLc, hp, ← Real.rpow_two, ← Real.rpow_sub hW0, hinv]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hw2 : (W : ℝ)⁻¹ ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hinv]; exact Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  set k : Zd 8 (W ^ 2) := Pi.single 0 1 with hkdef
  have hWW : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) W
  have hL2 : 1 < W ^ 2 := by omega
  have hk0 : k ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp only [hkdef, Pi.single_eq_same, Pi.zero_apply] at h1
    have : ((1 : ℕ) : ZMod (W ^ 2)) = 0 := by rw [Nat.cast_one]; exact h1
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd one_pos this
    omega
  have hkd : zdistInf 8 (W ^ 2) k ≤ 1 := by
    refine Finset.sup_le fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      simp only [hkdef, Pi.single_eq_same, zdist, ZMod.val_one_eq_one_mod]
      exact (min_le_left _ _).trans (Nat.mod_le _ _)
    · simp only [hkdef, Pi.single_eq_of_ne hi, zdist, ZMod.val_zero]
      simp
  have hk : ‖zfreq k‖ ≤ (W : ℝ) ^ (-1 - 1 / 2 : ℝ) := by
    refine (norm_zfreq_le k).trans ?_
    have hkd' : (zdistInf 8 (W ^ 2) k : ℝ) ≤ 1 := by exact_mod_cast hkd
    have hsq : (64 : ℝ) ≤ (W : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, show (64 : ℝ) = Real.sqrt 4096 by
        rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hW4
    have e : (W : ℝ) ^ (-1 - 1 / 2 : ℝ) = (W : ℝ) ^ (1 / 2 : ℝ) / (W : ℝ) ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_sub hW0]; norm_num
    rw [e, hLc, ← Real.rpow_two, le_div_iff₀ (by positivity)]
    have hpi := Real.pi_le_four
    have hpi0 := Real.pi_pos
    have h2 : ((8 : ℕ) : ℝ) * (2 * Real.pi * (zdistInf 8 (W ^ 2) k : ℝ) / (W : ℝ) ^ (2 : ℝ)) *
        (W : ℝ) ^ (2 : ℝ) = 16 * Real.pi * (zdistInf 8 (W ^ 2) k : ℝ) := by
      field_simp; push_cast; ring
    rw [h2]
    have hz0 : (0 : ℝ) ≤ (zdistInf 8 (W ^ 2) k : ℝ) := Nat.cast_nonneg _
    have : 16 * Real.pi * (zdistInf 8 (W ^ 2) k : ℝ) ≤ 16 * 4 * 1 := by gcongr
    linarith
  have hLL₁ : L₁ ≤ W ^ 2 := hWL₁.trans hWW
  have hLL₂ : L₂ ≤ W ^ 2 := hWL₂.trans hWW
  have hLL₃ : L₃ ≤ W ^ 2 := hWL₃.trans hWW
  obtain ⟨hU, hΘ, -, -, hGc⟩ := hL₁ W (W ^ 2) hLL₁ hadm I hz
  have h22 := (hL₂ W (W ^ 2) hLL₂ hadm I hz 0 0).1
  obtain ⟨-, e₁, e₂, e₃, he₁, he₂, he₃, hne, heq⟩ :=
    hL₃ W (W ^ 2) hLL₃ hadm hL4 0 (W : ℝ)⁻¹ (by norm_num) hw1 hw2 k hk
  have hmax : ∀ {X : ℝ} {C : ℝ}, 0 ≤ X → C ≤ max C₁ C₂ → C * X ≤ max C₁ C₂ * X :=
    fun hX hC => mul_le_mul_of_nonneg_right hC hX
  refine ⟨P, Sg, Gc, max C₁ C₂, W, W ^ 2, hL, k, hW4n, rfl, hk0, hSig, hadm, hz, hL4, hw1, hw2,
    hk, hU, hΘ 0 0, hGc 0 0, h22.trans (hmax (by positivity) (le_max_left _ _)), e₁, e₂, e₃,
    he₁.trans (hmax (by positivity) (le_max_right _ _)),
    he₂.trans (hmax (by positivity) (le_max_right _ _)),
    he₃.trans (hmax (by positivity) (le_max_right _ _)), hne, heq⟩

#print axioms localLawTExp_cutoff
#print axioms Assembly.selfEnergyStep'
#print axioms G14.localLaw_of_parts'
#print axioms G14.inst_localLawComp'
#print axioms G14.localLaw_of_tEq'
#print axioms thm13_eq112_of'
#print axioms thm13_eq113_of'
#print axioms thm13_of'
#print axioms localLaw
#print axioms thm13
#print axioms quantumDiffusion

end RBM8D
