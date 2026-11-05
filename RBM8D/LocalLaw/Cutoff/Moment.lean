import RBM8D.LocalLaw.Cutoff.Defs
import RBM8D.LocalLaw.Moment
import RBM8D.LocalLaw.LabelPaths
import RBM8D.LocalLaw.QTermOf
import RBM8D.SelfEnergy.Lem512Zero
import Batteries.Tactic.OpenPrivate

/-!
# The cutoff moment bound

`cutMoment_of : hookGraphSumStmt → cutImproveStmt → cutPairStmt → cutMomentStmt`: the bound
`E Z_{𝔞𝔟}^q ≤ W^{qν}` for `Z = C X` with the cutoff `C = 1{Y ≤ W^β} φ(M/W^α)`.

* **The terms of [II, (3.1)] at ports `(𝔞, t, t)` on the cutoff event** (`Moment_cutTerms`), at a
  single matrix `G` with `|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}`: the leading terms by
  [I, Lemma 6.2]; the graphs of `R`, `A`, the label-free graphs `Γ'_S` of `Err`, and the graphs of
  `Q` without internal atom or `⊕`-recollision at `𝔟₁ = 𝔟₂` by the rows of [II, Claim 8.6]
  (`graphSumStmt''`, the first two rows read with `Φ̃ = 1`, the third with `Φ̃ = 0` at the fixed
  exponent `c₀ᵀ/4` and [II, (3.15)]); the other graphs of `Q` with the hook weight at the label
  atom (`hookGraphSumStmt`). The weak `(1, 2)` norm of `G − m` is at most `C W^β`.
* **The resampled row**: on a good pair `(ω, ω^{[y,η]})`,
  `|C Z^k − C' Z'^k| ≤ K W^{4β+α} (1 + Z^k) J*_y` with `J*_y = h_y(𝔞, 𝔟) + Σ_i w_i h_y(i)`; the
  exchange of the two samples on row `y` preserves the law, so `cutPairStmt` controls the pairs
  in both directions.
* **The graphs of `Q`**: `E U Q_y(R) = E (U − P_y U) R`, bounded on the
  good pairs by the hook sums and off them by an a priori bound.
* **The graphs of `Err`**: the label removal of `labelRemovalErr` with the single matrix
  `G̃_{xy} = W^β B_{xy}^{1/2}` (`x ≠ y`), `G̃_{xx} = m (1 + W^β B_{xx}^{1/2}/|m|)`, off the
  samples whose resampled rows are bad with probability at least `W^{−D_m/2}` (Markov's inequality
  on the event of `cutPairStmt`) or with `‖ω‖ > W`.
* **The recursion**: with `|m|² B_{𝔞𝔟} X_{𝔞𝔟} = Σ_t T_{𝔞t} s_{t𝔟}` and
  `Σ_t B_{𝔞t} s_{t𝔟} ≤ C (⟨𝔞 − 𝔟⟩/W)^δ B_{𝔞𝔟}`, `E Z^{k+1} ≤ K W^{ν/2} (1 + E Z^k) + 1`.

`cutImproveStmt` is not read by the proof.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

open Graphs

open private Moment_ev_adm Moment_ev_thr Moment_tendsto Moment_bB_le_one Moment_rpow_mul_le
  Moment_diagRecoll_of_recoll Moment_diagRecoll_of_pmBlock Moment_chainLabels_entries
  Moment_theta_ord Moment_small_n from RBM8D.LocalLaw.Moment
open private Lem512_weakNorm_le Lem512_val_rbm from RBM8D.SelfEnergy.Lem512
open private QTerm_polyMeas_prod from RBM8D.LocalLaw.QTerm
open private QTermOf_list_int from RBM8D.LocalLaw.QTermOf
open private Chain_conv Chain_bB_eq Chain_brk_comm from RBM8D.Bound.Chain
open private Lem512Zero_comp_le Lem512Zero_valR_le Lem512Zero_integral_le Lem512Zero_moment
  Lem512Zero_norm_le_three from RBM8D.SelfEnergy.Lem512Zero
open private Moment_coeff_le Moment_cvar_le Moment_im_inv Moment_prod_le Moment_compVal_le
  Moment_ev_Sp Moment_ev_chain Moment_ev_list Moment_ev_Smat Moment_chain_eq Moment_polyMeas_valR
  Moment_meas_T Moment_T_le Moment_T_eq Moment_norm_valR_le Moment_bB_lower Moment_W_le_L
  from RBM8D.LocalLaw.Moment
open private LabelRemoval_coordVar_le LabelRemoval_card_coord from RBM8D.LocalLaw.LabelRemoval
open private LabelRemoval_Mres LabelRemoval_Mb LabelRemoval_Mb_pow LabelRemoval_val_bad
  LabelRemoval_inv_diag_le LabelRemoval_errKind LabelRemoval_valR_le LabelRemoval_ResDom
  LabelRemoval_norm_tail LabelRemoval_markov
  from RBM8D.LocalLaw.LabelRemoval

/-! ## Entry bounds -/

/-- `B_{xy}^{1/2} ≤ W^{−d/2}` for `W ≥ 1`, `d ≥ 2`. -/
private lemma CutMoment_sqrtB_le (d L W : ℕ) [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ (W : ℝ))
    (x y : Zd d L) : Real.sqrt (bB d L W x y) ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hB : bB d L W x y ≤ (W : ℝ) ^ (-(d : ℝ)) := by
    unfold bB
    have h0 : (0 : ℝ) ≤ (zdistInf d L (x - y) : ℝ) := Nat.cast_nonneg _
    have h1 : ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) ≤ (W : ℝ) ^ (2 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hW0 (by linarith) (by linarith)
    calc (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ))
        ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hW0.le _)
      _ = (W : ℝ) ^ (-(d : ℝ)) := by rw [← Real.rpow_add hW0]; ring_nf
  calc Real.sqrt (bB d L W x y) ≤ Real.sqrt ((W : ℝ) ^ (-(d : ℝ))) := Real.sqrt_le_sqrt hB
    _ = (W : ℝ) ^ (-((d : ℝ) / 2)) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _),
        ← Real.rpow_add hW0]
      ring_nf

/-- Under `|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}` with `0 ≤ β ≤ d/2`, `|G_{xy} − δ_{xy} m| ≤ 1`. -/
private lemma CutMoment_entry_le_one {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ (W : ℝ))
    {β : ℝ} (hβd : β ≤ (d : ℝ) / 2) (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ)
    (hG : ∀ x y, ‖entryErr G m x y‖ ≤ (W : ℝ) ^ β * Real.sqrt (bB d L W x y)) (x y : Zd d L) :
    ‖entryErr G m x y‖ ≤ 1 := by
  have hW0 : (0 : ℝ) < W := by linarith
  refine (hG x y).trans ?_
  calc (W : ℝ) ^ β * Real.sqrt (bB d L W x y) ≤ (W : ℝ) ^ β * (W : ℝ) ^ (-((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (CutMoment_sqrtB_le d L W hd hW x y) (Real.rpow_nonneg hW0.le _)
    _ = (W : ℝ) ^ (β - (d : ℝ) / 2) := by rw [← Real.rpow_add hW0]; ring_nf
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)

/-- The weak `(1, 2)` norm of `|G − m|` under the entry bound `W^β B^{1/2}`: at most `C W^β`. -/
private lemma CutMoment_weakNorm (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (z : ℂ) (G : Matrix (Zd d L) (Zd d L) ℂ) (β : ℝ),
      (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ β * Real.sqrt (bB d L W x y)) →
      weakNorm d L W 1 2 (errAbs G z) ≤ C * (W : ℝ) ^ β := by
  obtain ⟨C, hC0, hC⟩ := Lem512_weakNorm_le d (by omega)
  refine ⟨C, hC0, fun L W _ hW z G β hG => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  refine hC L W hW (errAbs G z) ((W : ℝ) ^ β) (Real.rpow_nonneg hW0.le _) fun x y => ?_
  simp only [errAbs, abs_norm]
  exact hG x y

/-- Eventually along the filter, `C ≤ W^c` for `c > 0`. -/
private lemma CutMoment_ev_rpow (d n : ℕ) (c₀ c₁ c₀T C c : ℝ) (hc : 0 < c) :
    ∀ᶠ p in llFilter d n c₀ c₁ c₀T, C ≤ (p.1.1 : ℝ) ^ c :=
  ((tendsto_rpow_atTop hc).comp (Moment_tendsto d n c₀ c₁ c₀T)).eventually (eventually_ge_atTop C)

/-- Eventually along the filter, `C ≤ W`. -/
private lemma CutMoment_ev_W (d n : ℕ) (c₀ c₁ c₀T C : ℝ) :
    ∀ᶠ p in llFilter d n c₀ c₁ c₀T, C ≤ (p.1.1 : ℝ) :=
  (Moment_tendsto d n c₀ c₁ c₀T).eventually (eventually_ge_atTop C)

/-! ## One graph without the hook weight -/

/-- **The rows of [II, Claim 8.6] at a single matrix on the cutoff event**: for a graph `g` with
the hypotheses of `graphSumStmt''`, with `n_𝔟 ≥ 2` if it is a `⊕`-recollision graph at
`𝔟₁ = 𝔟₂`, and with `n_𝔟 ≥ n + 1` and the rooting at the external atoms if it has an internal
atom and is not such a graph, there is `β_g > 0` such that for every `ν > 0`, eventually along
the filter, uniformly in `z ∈ 𝐃(κ, ε)`, `0 ≤ β ≤ β_g` and every `G` with
`|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}`: `|𝒢^{abs}_{𝔞,𝔟𝔟}| ≤ W^ν B_{𝔞𝔟}`. -/
private lemma CutMoment_graph (h₂ : graphSumStmt'') (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (c₀ c₁ κ ε c₀T : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ)
    (hε : 0 < ε) (hc₀T : 0 < c₀T) (n : ℕ) (Sig : ℕ → Expansion 2)
    (hSE : SelfEnergiesUpTo d (smatVar P) Sig n) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀n : ((n : ℝ) + 1) * ε₀ ≤ c₀T / 4) (hε₀d : ε₀ ≤ (d : ℝ) / 8)
    (nI C : ℕ) (g : Graph 3 nI) (hN : g.Normal C) (hK : g.TKinds n) (hAE : g.AtExternals)
    (hDC : g.DoublyConnected) (hTD : g.TensorDiffusive) (hDA : g.DotsAcyclic)
    (h1 : g.DiagRecoll → 2 ≤ g.diagOrd)
    (h3 : nI ≠ 0 → ¬ g.DiagRecoll → (n : ℤ) + 1 ≤ g.diagOrd ∧ g.RootedAtExt) :
    ∃ βg : ℝ, 0 < βg ∧ ∀ ν : ℝ, 0 < ν → ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
      ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ β : ℝ, 0 ≤ β → β ≤ βg →
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ a b, g.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, b, b] ≤
          (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a b := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cw, hCw0, hCw⟩ := CutMoment_weakNorm d hd
  obtain ⟨τ₃, hτ₃, W₃, hW₃⟩ := h₂ d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n Sig hSE nI C g hN hK hAE
    hDC hTD hDA ε₀ hε₀.le (by linarith) (c₀T / 4) (by positivity)
  refine ⟨min τ₃ (ε₀ / 2), lt_min hτ₃ (by positivity), fun ν hν => ?_⟩
  obtain ⟨τ', hτ', W₀, hW₀⟩ := h₂ d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n Sig hSE nI C g hN hK hAE
    hDC hTD hDA ε₀ hε₀.le (by linarith) ν hν
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, Moment_ev_thr d n c₀ c₁ c₀T,
    CutMoment_ev_W d n c₀ c₁ c₀T (max (max W₀ W₃) 1),
    CutMoment_ev_rpow d n c₀ c₁ c₀T Cw (ε₀ / 2) (by positivity)] with p hp hthr hW hCwW
  intro z hz β hβ0 hβ G hG a b
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hW0 : 0 < W := by linarith
  have hWW₀ : W₀ ≤ W := ((le_max_left _ _).trans (le_max_left _ _)).trans hW
  have hWW₃ : W₃ ≤ W := ((le_max_right _ _).trans (le_max_left _ _)).trans hW
  have hβε : β ≤ ε₀ / 2 := hβ.trans (min_le_right _ _)
  have hβτ : β ≤ τ₃ := hβ.trans (min_le_left _ _)
  have hB0 := (Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 a b).1
  have hνW : 0 ≤ W ^ ν := Real.rpow_nonneg hW0.le _
  have hwn : weakNorm d p.1.2 p.1.1 1 2 (errAbs G z) ≤ W ^ (ε₀ / 2) * W ^ β :=
    (hCw p.1.2 p.1.1 (by have h : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW1; exact_mod_cast h) z G β hG).trans
      (mul_le_mul_of_nonneg_right hCwW (Real.rpow_nonneg hW0.le _))
  have hrate : -((d : ℝ) / 2) + ε₀ ≤ 0 := by linarith
  -- the first two rows, with `Φ̃ = 1`
  have hwn1 : weakNorm d p.1.2 p.1.1 1 2 (errAbs G z) ≤ W ^ (ε₀ + τ') := by
    refine hwn.trans ?_
    rw [← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hent1 : ∀ x y, ‖entryErr G (msc z) x y‖ ≤
      W ^ τ' * (Real.sqrt (bB d p.1.2 p.1.1 x y) + 1) := by
    intro x y
    have h1' := CutMoment_entry_le_one (by omega) hW1 (by linarith) G (msc z) hG x y
    have h2' : (1 : ℝ) ≤ W ^ τ' := Real.one_le_rpow hW1 hτ'.le
    have h3' : (1 : ℝ) ≤ Real.sqrt (bB d p.1.2 p.1.1 x y) + 1 := by
      have := Real.sqrt_nonneg (bB d p.1.2 p.1.1 x y); linarith
    nlinarith
  obtain ⟨r1, r2, -⟩ := hW₀ p.1.1 p.1.2 hp hWW₀ z hz G 1 zero_le_one hwn1 hent1
  by_cases hdr : g.DiagRecoll
  · refine (r1 hdr (h1 hdr) a b).trans ?_
    have hx : W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos hW1 ?_
      have : (2 : ℝ) ≤ (g.diagOrd : ℝ) := by exact_mod_cast h1 hdr
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hrate
    calc W ^ ν * W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) * bB d p.1.2 p.1.1 a b
        ≤ W ^ ν * 1 * bB d p.1.2 p.1.1 a b := by gcongr
      _ = _ := by ring
  by_cases hnI : nI = 0
  · exact r2 hnI a b
  -- the third row, with `Φ̃ = 0`
  obtain ⟨hord, hRt⟩ := h3 hnI hdr
  have hwn3 : weakNorm d p.1.2 p.1.1 1 2 (errAbs G z) ≤ W ^ (ε₀ + τ₃) := by
    refine hwn.trans ?_
    rw [← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hent3 : ∀ x y, ‖entryErr G (msc z) x y‖ ≤
      W ^ τ₃ * (Real.sqrt (bB d p.1.2 p.1.1 x y) + 0) := by
    intro x y
    rw [add_zero]
    exact (hG x y).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hW1 hβτ) (Real.sqrt_nonneg _))
  obtain ⟨-, -, r3⟩ := hW₃ p.1.1 p.1.2 hp hWW₃ z hz G 0 le_rfl hwn3 hent3
  refine (r3 hnI hdr hRt a b).trans ?_
  have hnS : (n : ℝ) - 1 ≤ (g.diagOrd : ℝ) - 2 := by
    have : (n : ℝ) + 1 ≤ (g.diagOrd : ℝ) := by exact_mod_cast hord
    linarith
  have hx1 := Moment_rpow_mul_le W hW1 _ _ _ hrate hnS
  have hLW : (0 : ℝ) ≤ (p.1.2 : ℝ) ^ 2 / W ^ 2 := by positivity
  have hthr' : (p.1.2 : ℝ) ^ 2 / W ^ 2 ≤ W ^ (((n : ℝ) - 1) * d / 2 - c₀T) := hthr
  have hx2 : W ^ (c₀T / 4) * W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) *
      ((p.1.2 : ℝ) ^ 2 / W ^ 2) ≤ 1 := by
    calc W ^ (c₀T / 4) * W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) *
          ((p.1.2 : ℝ) ^ 2 / W ^ 2)
        ≤ W ^ (c₀T / 4) * W ^ (((n : ℝ) - 1) * (-((d : ℝ) / 2) + ε₀)) *
          W ^ (((n : ℝ) - 1) * d / 2 - c₀T) := by gcongr
      _ = W ^ (c₀T / 4 + ((n : ℝ) - 1) * ε₀ - c₀T) := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring
      _ ≤ 1 := by
          refine Real.rpow_le_one_of_one_le_of_nonpos hW1 ?_
          have : ((n : ℝ) - 1) * ε₀ ≤ ((n : ℝ) + 1) * ε₀ := by nlinarith
          linarith
  have hν1 : 1 ≤ W ^ ν := Real.one_le_rpow hW1 hν.le
  calc W ^ (c₀T / 4) * W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) *
        ((p.1.2 : ℝ) ^ 2 / W ^ 2) * (bB d p.1.2 p.1.1 a b + 0 ^ 2)
      ≤ 1 * bB d p.1.2 p.1.1 a b := by
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
        exact mul_le_mul_of_nonneg_right hx2 hB0
    _ ≤ W ^ ν * bB d p.1.2 p.1.1 a b := mul_le_mul_of_nonneg_right hν1 hB0

/-! ## The label-free graphs of a graph of `Err` -/

/-- **The graphs of `Err` on the cutoff event**: for a graph `g` with the kinds of `Err` and the
hypotheses of `graphSumStmt''`, with `n_𝔟 ≥ 2` if it is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`,
and with `n_𝔟 ≥ n + 1` and the rooting at the external atoms if it has an internal atom and is not
such a graph, the label-free graphs `Γ'_S` of `g' = g.wDLights` satisfy
`Σ_S |(Γ'_S)^{abs}_{𝔞,𝔟𝔟}| ≤ W^ν B_{𝔞𝔟}` at every `G` with `|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}`,
`0 ≤ β ≤ β_g`, eventually along the filter for every `ν > 0`. -/
private lemma CutMoment_err (h₂ : graphSumStmt'') (hLP : labelPathsStmt) (d : ℕ) (hd : 8 ≤ d)
    (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1)
    (hκ : 0 < κ) (hε : 0 < ε) (hc₀T : 0 < c₀T) (n : ℕ) (Sig : ℕ → Expansion 2)
    (hSE : SelfEnergiesUpTo d (smatVar P) Sig n) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀n : ((n : ℝ) + 1) * ε₀ ≤ c₀T / 4) (hε₀d : ε₀ ≤ (d : ℝ) / 8)
    (nI C : ℕ) (g : Graph 3 nI) (hN : g.Normal C) (hK : g.TKindsErr n) (hAE : g.AtExternals)
    (hDC : g.DoublyConnected) (hTD : g.TensorDiffusive) (hDA : g.DotsAcyclic)
    (hR : nI ≠ 0 → ¬ g.DiagRecoll → g.RootedAtExt) (h1 : g.DiagRecoll → 2 ≤ g.diagOrd)
    (h3 : nI ≠ 0 → ¬ g.DiagRecoll → (n : ℤ) + 1 ≤ g.diagOrd) :
    ∃ βg : ℝ, 0 < βg ∧ ∀ ν : ℝ, 0 < ν → ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
      ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ β : ℝ, 0 ≤ β → β ≤ βg →
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ a b, ∑ S ∈ g.wDLights.pathElig.powerset, (g.wDLights.pathRepl S).absVal
          (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, b, b] ≤
          (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a b := by
  obtain ⟨hNw, hKw, hAEw, hDCw, hTDw, hDAw, hDRw, hRtw, -, hdow⟩ :=
    G11.wDLights_props g n C hK hN hAE hDC hTD hDA
  set g' := g.wDLights with hg'
  have hRw : nI ≠ 0 → ¬ g'.DiagRecoll → g'.RootedAtExt := fun h h' =>
    hRtw.2 (hR h fun h'' => h' (hDRw.2 h''))
  have hrow : ∀ S : Finset (Fin g'.comps.length), ∃ βS : ℝ, 0 < βS ∧ (S ⊆ g'.pathElig →
      ∀ ν : ℝ, 0 < ν → ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
        ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ β : ℝ, 0 ≤ β → β ≤ βS →
        ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
          (∀ x y, ‖entryErr G (msc z) x y‖ ≤
            (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
          ∀ a b, (g'.pathRepl S).absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, b, b] ≤
            (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a b) := by
    intro S
    by_cases hS : S ⊆ g'.pathElig
    · obtain ⟨⟨C', hN'⟩, hK', hAE', hDC', hTD', hDA', -, -, hdr, hR', -, hdord⟩ :=
        hLP nI _ n g' hNw hKw hAEw hDCw hTDw hDAw hRw S hS
      have hSd : g'.diagOrd ≤ (g'.pathRepl S).diagOrd := by linarith [hdord]
      obtain ⟨βS, hβS, h⟩ := CutMoment_graph h₂ d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T n
        Sig hSE ε₀ hε₀ hε₀n hε₀d nI C' (g'.pathRepl S) hN' hK' hAE' hDC' hTD' hDA'
        (fun h => by
          have := h1 (hDRw.1 (hdr.1 h))
          rw [hdow] at hSd; omega)
        (fun hnI h => by
          have hdg : ¬ g.DiagRecoll := fun h' => h (hdr.2 (hDRw.2 h'))
          have := h3 hnI hdg
          rw [hdow] at hSd
          exact ⟨by omega, hR' hnI h⟩)
      exact ⟨βS, hβS, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hS⟩
  choose βf hβf hf using hrow
  set βg := Finset.univ.inf' Finset.univ_nonempty βf with hβg
  have hβg0 : 0 < βg := (Finset.lt_inf'_iff _).2 fun S _ => hβf S
  refine ⟨βg, hβg0, fun ν hν => ?_⟩
  set k := g'.pathElig.card with hk
  have hall : ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ S : Finset (Fin g'.comps.length),
      S ⊆ g'.pathElig → ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ β : ℝ, 0 ≤ β → β ≤ βf S →
        ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
          (∀ x y, ‖entryErr G (msc z) x y‖ ≤
            (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
          ∀ a b, (g'.pathRepl S).absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, b, b] ≤
            (p.1.1 : ℝ) ^ (ν / 2) * bB d p.1.2 p.1.1 a b := by
    refine Filter.eventually_all.2 fun S => ?_
    by_cases hS : S ⊆ g'.pathElig
    · filter_upwards [hf S hS (ν / 2) (by positivity)] with p hp _ z hz β hβ0 hβ G hG a b
      exact hp z hz β hβ0 hβ G hG a b
    · exact Eventually.of_forall fun p h => absurd h hS
  filter_upwards [hall, CutMoment_ev_W d n c₀ c₁ c₀T 1,
    CutMoment_ev_rpow d n c₀ c₁ c₀T ((2 : ℝ) ^ k) (ν / 2) (by positivity)]
    with p hp hW1 hk2 z hz β hβ0 hβ G hG a b
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have hB0 := (Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 a b).1
  have hle : ∀ S ∈ g'.pathElig.powerset, (g'.pathRepl S).absVal
      (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, b, b] ≤
      (p.1.1 : ℝ) ^ (ν / 2) * bB d p.1.2 p.1.1 a b := fun S hS =>
    hp S (Finset.mem_powerset.1 hS) z hz β hβ0
      (hβ.trans (Finset.inf'_le _ (Finset.mem_univ S))) G hG a b
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  calc (2 : ℝ) ^ k * ((p.1.1 : ℝ) ^ (ν / 2) * bB d p.1.2 p.1.1 a b)
      ≤ (p.1.1 : ℝ) ^ (ν / 2) * ((p.1.1 : ℝ) ^ (ν / 2) * bB d p.1.2 p.1.1 a b) :=
        mul_le_mul_of_nonneg_right hk2 (mul_nonneg (Real.rpow_nonneg hW0.le _) hB0)
    _ = (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a b := by
        rw [← mul_assoc, ← Real.rpow_add hW0]; ring_nf

/-! ## The leading terms -/

/-- The absolute-value graph of `m Θ^{[o]}_{𝔞𝔟} Ḡ_{𝔟𝔟}` at a single matrix. -/
private lemma CutMoment_thetaLabel_absVal {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2) (G : Matrix ι ι ℂ) (o : List ℕ)
    (a b : ι) :
    (thetaLabelGraph o).absVal (gData S z Sig G) ![a, b, b] =
      ‖msc z‖ * (‖(detData S z (sigMat Sig S z)).chain o a b‖ * ‖G b b‖) := by
  simp only [Graph.absVal, thetaLabelGraph, mkC, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Finset.univ_unique, Finset.sum_singleton]
  simp only [Comp.val, Coeff.eval, Charge.apply, norm_star]
  simp [CVar.eval, gData, detData, Data.chain]

/-- **The leading terms on the cutoff event** ([I, Lemma 6.2]): for a label `o` with entries even
in `[4, n]`, for every `ν > 0`, eventually along the filter, uniformly in `z ∈ 𝐃(κ, ε)`,
`β ≤ d/2` and every `G` with `|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}`:
`|m Θ^{[o]}_{𝔞𝔟}| |G_{𝔟𝔟}| ≤ W^ν B_{𝔞𝔟}`. -/
private lemma CutMoment_lead (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (n : ℕ)
    (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig n) (o : List ℕ)
    (ho : ∀ l ∈ o, 4 ≤ l ∧ l ≤ n ∧ Even l) (ν : ℝ) (hν : 0 < ν) :
    ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ β : ℝ, β ≤ (d : ℝ) / 2 →
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ a b, (thetaLabelGraph o).absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, b, b] ≤
          (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a b := by
  obtain ⟨W₀, hW₀⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (sigKer (smatVar P) Sig) o
    (fun l hl => ⟨(hSE l (ho l hl).1 (ho l hl).2.1 (ho l hl).2.2).2.1,
      (hSE l (ho l hl).1 (ho l hl).2.1 (ho l hl).2.2).2.2⟩) (ν / 2) (by positivity)
  obtain ⟨W₁, hW₁⟩ := detData_smatVar_eq_on_adm d P Sig c₀ c₁ hc₀ hc₁
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, CutMoment_ev_W d n c₀ c₁ c₀T (max (max W₀ W₁) 1),
    CutMoment_ev_rpow d n c₀ c₁ c₀T 2 (ν / 2) (by positivity)] with p hp hW h2
    z hz β hβ G hG a b
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hW0 : 0 < W := by linarith
  have hzim : 0 < z.im := by
    have h := hz.2.1
    have hL : (0 : ℝ) < (p.1.2 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero p.2
    exact lt_of_lt_of_le (by positivity) h
  have hm : ‖msc z‖ ≤ 1 := (norm_msc_lt_one hzim).le
  rw [CutMoment_thetaLabel_absVal]
  have hch := hW₀ p.1.1 p.1.2 hp (((le_max_left _ _).trans (le_max_left _ _)).trans hW) z hz a b
  rw [hW₁ p.1.1 p.1.2 hp (((le_max_right _ _).trans (le_max_left _ _)).trans hW) z] at hch
  have hB0 := (Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 a b).1
  have hord : W ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hW1 ?_
    have h2' : (2 : ℝ) ≤ (((Kind.theta o).ord : ℤ) : ℝ) := by
      exact_mod_cast Moment_theta_ord o fun l hl => by have := (ho l hl).1; omega
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have : 0 ≤ ((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d := mul_nonneg (by linarith) hd0
    linarith
  have hch' : ‖(detData (Smat P.ψ p.1.1 p.1.2) z (sigMat Sig (Smat P.ψ p.1.1 p.1.2) z)).chain o a b‖
      ≤ W ^ (ν / 2) * bB d p.1.2 p.1.1 a b := by
    refine hch.trans ?_
    calc W ^ (ν / 2) * W ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) * bB d p.1.2 p.1.1 a b
        ≤ W ^ (ν / 2) * 1 * bB d p.1.2 p.1.1 a b := by gcongr
      _ = _ := by ring
  have hGbb : ‖G b b‖ ≤ 2 := by
    have e : G b b = entryErr G (msc z) b b + msc z := by simp [entryErr]
    rw [e]
    have := CutMoment_entry_le_one (by omega) hW1 hβ G (msc z) hG b b
    exact (norm_add_le _ _).trans (by linarith)
  calc ‖msc z‖ * (‖(detData (Smat P.ψ p.1.1 p.1.2) z
        (sigMat Sig (Smat P.ψ p.1.1 p.1.2) z)).chain o a b‖ * ‖G b b‖)
      ≤ 1 * ((W ^ (ν / 2) * bB d p.1.2 p.1.1 a b) * 2) := by gcongr
    _ = 2 * W ^ (ν / 2) * bB d p.1.2 p.1.1 a b := by ring
    _ ≤ W ^ (ν / 2) * W ^ (ν / 2) * bB d p.1.2 p.1.1 a b := by gcongr
    _ = W ^ ν * bB d p.1.2 p.1.1 a b := by rw [← Real.rpow_add hW0]; ring_nf

/-! ## The hook weight at the label atom -/

/-- **The graphs of `Q` with an internal atom that are not `⊕`-recollision graphs at
`𝔟₁ = 𝔟₂`**, with the hook weight `B_{c σ(v)}^{1/2}` at an internal atom `v`
(`hookGraphSumStmt` at `τ = d/8`): there is `β_h > 0` such that eventually along the filter,
uniformly in `z ∈ 𝐃(κ, ε)`, `0 ≤ β ≤ β_h`, every `G` with `|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}`,
every `v` and every centre `c`: `Σ_σ K_g(𝔞, 𝔟; σ) B_{c σ(v)}^{1/2} ≤ W^{−3d/8} B_{𝔞𝔟}`. -/
private lemma CutMoment_hook (hH : hookGraphSumStmt) (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (c₀ c₁ κ ε c₀T : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ)
    (hε : 0 < ε) (n : ℕ) (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig n)
    (nI C : ℕ) (g : Graph 3 nI) (hN : g.Normal C) (hK : g.TKinds n) (hAE : g.AtExternals)
    (hDC : g.DoublyConnected) (hTD : g.TensorDiffusive) (hDA : g.DotsAcyclic)
    (hDR : ¬ g.DiagRecoll) (hRt : g.RootedAtExt) (h2 : 2 ≤ g.diagOrd) (hnI : nI ≠ 0) :
    ∃ βh : ℝ, 0 < βh ∧ ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
      ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ β : ℝ, 0 ≤ β → β ≤ βh →
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ (v : Fin nI) (a b c : Zd d p.1.2),
          g.absValHook (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, b, b] v
              (fun y => Real.sqrt (bB d p.1.2 p.1.1 c y)) ≤
            (p.1.1 : ℝ) ^ (-(3 * (d : ℝ) / 8)) * bB d p.1.2 p.1.1 a b := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hv : ∀ v : Fin nI, ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
      (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
          (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) →
          ∀ a b c : Zd d L,
            g.absValHook (gData (Smat P.ψ W L) z Sig G) ![a, b, b] v
                (fun y => Real.sqrt (bB d L W c y)) ≤
              (W : ℝ) ^ ((d : ℝ) / 8) * (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
                (W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b := fun v =>
    hH d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n Sig hSE nI C g hN hK hAE hDC hTD hDA hDR hRt v
      ((d : ℝ) / 8) (by positivity)
  choose τf hτf W₀f hW₀f using hv
  have hne : (Finset.univ : Finset (Fin nI)).Nonempty :=
    Finset.univ_nonempty_iff.2 ⟨⟨0, Nat.pos_of_ne_zero hnI⟩⟩
  set βh := Finset.univ.inf' hne τf with hβh
  set W₀ := Finset.univ.sup' hne W₀f with hW₀
  refine ⟨βh, (Finset.lt_inf'_iff _).2 fun v _ => hτf v, ?_⟩
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, CutMoment_ev_W d n c₀ c₁ c₀T (max W₀ 1)]
    with p hp hW z hz β hβ0 hβ G hG v a b c
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hW0 : 0 < W := by linarith
  have hβv : β ≤ τf v := hβ.trans (Finset.inf'_le _ (Finset.mem_univ v))
  have hWv : W₀f v ≤ W := (Finset.le_sup' _ (Finset.mem_univ v)).trans ((le_max_left _ _).trans hW)
  refine (hW₀f v p.1.1 p.1.2 hp hWv z hz G (fun x y => (hG x y).trans
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hW1 hβv)
      (Real.sqrt_nonneg _))) a b c).trans ?_
  have hB0 := (Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 a b).1
  have hx : W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hW1 ?_
    have : (2 : ℝ) ≤ (g.diagOrd : ℝ) := by exact_mod_cast h2
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  calc W ^ ((d : ℝ) / 8) * W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
        W ^ (-((d : ℝ) / 2)) * bB d p.1.2 p.1.1 a b
      ≤ W ^ ((d : ℝ) / 8) * 1 * W ^ (-((d : ℝ) / 2)) * bB d p.1.2 p.1.1 a b := by gcongr
    _ = W ^ (-(3 * (d : ℝ) / 8)) * bB d p.1.2 p.1.1 a b := by
        rw [mul_one, ← Real.rpow_add hW0]; ring_nf

/-! ## All the graphs of a record -/

/-- Finitely many bounds, each holding for `0 ≤ β ≤ β_g` and every `ν > 0` eventually, hold
together for `0 ≤ β ≤ min_g β_g`. -/
private lemma CutMoment_combine {α : Type*} {F : Filter SizeL} (R : α → ℝ → SizeL → ℝ → Prop)
    (l : List α) (h : ∀ g ∈ l, ∃ βg : ℝ, 0 < βg ∧ ∀ ν : ℝ, 0 < ν →
      ∀ᶠ p in F, ∀ β : ℝ, 0 ≤ β → β ≤ βg → R g ν p β) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ ν : ℝ, 0 < ν →
      ∀ᶠ p in F, ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ g ∈ l, R g ν p β := by
  induction l with
  | nil => exact ⟨1, one_pos, fun ν _ => Eventually.of_forall fun p β _ _ g hg => by simp at hg⟩
  | cons g l ih =>
    obtain ⟨β₁, hβ₁, h₁⟩ := h g (List.mem_cons_self ..)
    obtain ⟨β₂, hβ₂, h₂⟩ := ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    refine ⟨min β₁ β₂, lt_min hβ₁ hβ₂, fun ν hν => ?_⟩
    filter_upwards [h₁ ν hν, h₂ ν hν] with p hp₁ hp₂ β hβ0 hβ g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact hp₁ β hβ0 (hβ.trans (min_le_left _ _))
    · exact hp₂ β hβ0 (hβ.trans (min_le_right _ _)) g' hg'

/-- **The terms of [II, (3.1)] on the cutoff event**: for an `n`-th order `T`-expansion with
`D`-th order error, `D ≥ n + 2`, with the clauses `TRec.Def63G11`, there is `β₀ > 0` such that
for every `ν > 0`, eventually along the filter, uniformly in `z ∈ 𝐃(κ, ε)`, `0 ≤ β ≤ β₀`, every
single matrix `G` with `|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}` and `𝔞, t`:
* the leading terms, `Σ_T^{(n)}`, `R` and `A`: `|𝒢^{abs}_{𝔞,tt}| ≤ W^ν B_{𝔞t}`;
* `Err`: `Σ_S |(Γ'_S)^{abs}_{𝔞,tt}| ≤ W^ν B_{𝔞t}` over the label-free graphs of `g.wDLights`;
* the graphs of `Q` without internal atom or `⊕`-recollision at `𝔟₁ = 𝔟₂`:
  `|𝒢^{abs}_{𝔞,tt}| ≤ W^ν B_{𝔞t}`;
* the other graphs of `Q`, with the hook weight `B_{c σ(v)}^{1/2}` at any internal atom `v` and
  any centre `c`: `≤ W^{−3d/8} B_{𝔞t}`. -/
theorem Moment_cutTerms (hH : hookGraphSumStmt) (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (c₀ c₁ κ ε c₀T : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ)
    (hε : 0 < ε) (hc₀T : 0 < c₀T) (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec)
    (hnD : n + 2 ≤ D) (hT : IsTExpansion d (smatVar P) Sig n D 𝒯) (hG : 𝒯.Def63G11) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ ν : ℝ, 0 < ν → ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
      ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ a t : Zd d p.1.2,
          (∀ g ∈ leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A,
            g.2.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
              (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t) ∧
          (∀ g ∈ 𝒯.Err, ∑ S ∈ g.2.wDLights.pathElig.powerset, (g.2.wDLights.pathRepl S).absVal
            (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
              (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t) ∧
          (∀ g ∈ 𝒯.Q, (g.1 = 0 ∨ g.2.DiagRecoll) →
            g.2.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
              (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t) ∧
          (∀ g ∈ 𝒯.Q, g.1 ≠ 0 → ¬ g.2.DiagRecoll → ∀ (v : Fin g.1) (c : Zd d p.1.2),
            g.2.absValHook (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] v
                (fun y => Real.sqrt (bB d p.1.2 p.1.1 c y)) ≤
              (p.1.1 : ℝ) ^ (-(3 * (d : ℝ) / 8)) * bB d p.1.2 p.1.1 a t) := by
  by_cases hn : n ≤ 1
  · refine ⟨1, one_pos, fun ν _ => ?_⟩
    filter_upwards [Moment_small_n d n c₀ c₁ c₀T hc₀ hc₀T hn] with p hp
    exact hp.elim
  have hn2 : 2 ≤ n := by omega
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hSE, -, -, -, hShape, hD63⟩ := hT
  obtain ⟨hall, hRs, hAs, hQs, hErrs⟩ := hShape
  obtain ⟨hG1, hG2, hG3⟩ := hG
  have hdo : ∀ {m : ℕ} (Γ : Graph 3 m), Γ.diagOrd = Γ.ord - if Γ.pmBlockB then 2 else 0 :=
    fun Γ => rfl
  set ε₀ : ℝ := min ((d : ℝ) / 8) (c₀T / (4 * ((n : ℝ) + 1))) with hε₀def
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hε₀d : ε₀ ≤ (d : ℝ) / 8 := min_le_left _ _
  have hε₀n : ((n : ℝ) + 1) * ε₀ ≤ c₀T / 4 := by
    have : ε₀ ≤ c₀T / (4 * ((n : ℝ) + 1)) := min_le_right _ _
    calc ((n : ℝ) + 1) * ε₀ ≤ ((n : ℝ) + 1) * (c₀T / (4 * ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left this hn1.le
      _ = c₀T / 4 := by field_simp
  -- the leading terms, `R`, `A`
  obtain ⟨β₁, hβ₁, h₁⟩ := CutMoment_combine (F := llFilter d n c₀ c₁ c₀T)
    (fun (g : Σ m, Graph 3 m) ν p β => ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ a t : Zd d p.1.2, g.2.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
          (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t)
    (leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A) (by
      intro g hg
      have hgraph : ∀ (nI C : ℕ) (Γ : Graph 3 nI), Γ.Normal C → Γ.TKinds n → Γ.AtExternals →
          Γ.DoublyConnected → Γ.TensorDiffusive → Γ.DotsAcyclic →
          (Γ.DiagRecoll → 2 ≤ Γ.diagOrd) →
          (nI ≠ 0 → ¬ Γ.DiagRecoll → (n : ℤ) + 1 ≤ Γ.diagOrd ∧ Γ.RootedAtExt) →
          ∃ βg : ℝ, 0 < βg ∧ ∀ ν : ℝ, 0 < ν → ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
            ∀ β : ℝ, 0 ≤ β → β ≤ βg → ∀ z ∈ specDom κ ε p.1.1 p.1.2,
            ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
              (∀ x y, ‖entryErr G (msc z) x y‖ ≤
                (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
              ∀ a t : Zd d p.1.2, Γ.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
                (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t := by
        intro nI C Γ hN hK hAE hDC hTD hDA h1 h3
        obtain ⟨βg, hβg, hh⟩ := CutMoment_graph graphSum'' d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε
          hc₀T n Sig hSE ε₀ hε₀ hε₀n hε₀d nI C Γ hN hK hAE hDC hTD hDA h1 h3
        refine ⟨βg, hβg, fun ν hν => ?_⟩
        filter_upwards [hh ν hν] with p hp β hβ0 hβ z hz G hGe a t
        exact hp z hz β hβ0 hβ G hGe a t
      rcases List.mem_append.1 hg with hg | hgA
      rotate_left
      · -- `A`
        have hmem : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err :=
          List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hgA))
        obtain ⟨⟨C, hN⟩, hK, hAE, hDC⟩ :=
          hall.1 g (List.mem_append_left _ (List.mem_append_right _ hgA))
        obtain ⟨hTD, hDA⟩ := hG1 g hmem
        obtain ⟨-, hord⟩ := hAs g hgA
        refine hgraph g.1 C g.2 hN hK hAE hDC hTD hDA (fun _ => ?_) ?_
        · rw [hdo]
          by_cases hpm : g.2.pmBlockB = true
          · have := hG2 g (List.mem_append_right _ hgA) hpm
            simp only [hpm, ite_true]; omega
          · simp only [hpm]; simp; omega
        · intro hnI hndr
          have hext : g.2.ExtClause := by
            rcases (hD63.1.2.1 g hgA).2 with h0 | h
            · exact absurd h0.1 hnI
            · exact h.1
          have hpm : g.2.pmBlockB = false := by
            by_contra hpm
            have hpm' : g.2.pmBlockB = true := by simpa using hpm
            exact hndr (Moment_diagRecoll_of_pmBlock g.2 hext hpm')
          refine ⟨?_, hG3 g (List.mem_append_left _ (List.mem_append_left _ hgA)) hnI hndr⟩
          rw [hdo]; simp only [hpm]; simp; omega
      rcases List.mem_append.1 hg with hg | hgR
      rotate_left
      · -- `R`
        have hmem : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err :=
          List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hgR))
        obtain ⟨⟨C, hN⟩, hK, hAE, hDC⟩ :=
          hall.1 g (List.mem_append_left _ (List.mem_append_left _ hgR))
        obtain ⟨hTD, hDA⟩ := hG1 g hmem
        obtain ⟨-, hrec, h3, -⟩ := hRs g hgR
        have hdr := Moment_diagRecoll_of_recoll g.2 hrec
        refine hgraph g.1 C g.2 hN hK hAE hDC hTD hDA (fun _ => ?_) (fun _ h => absurd hdr h)
        rw [hdo]
        by_cases hpm : g.2.pmBlockB = true
        · have := hG2 g (List.mem_append_left _ hgR) hpm
          simp only [hpm, ite_true]; omega
        · simp only [hpm]; simp; omega
      · -- the leading terms
        have hlead : ∀ o : List ℕ, (∀ l ∈ o, 4 ≤ l ∧ l ≤ n ∧ Even l) →
            ∃ βg : ℝ, 0 < βg ∧ ∀ ν : ℝ, 0 < ν → ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
              ∀ β : ℝ, 0 ≤ β → β ≤ βg → ∀ z ∈ specDom κ ε p.1.1 p.1.2,
              ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
                (∀ x y, ‖entryErr G (msc z) x y‖ ≤
                  (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
                ∀ a t : Zd d p.1.2, (thetaLabelGraph o).absVal
                  (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
                  (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t := by
          intro o ho
          refine ⟨(d : ℝ) / 2, by positivity, fun ν hν => ?_⟩
          filter_upwards [CutMoment_lead d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε n Sig hSE o ho ν
            hν] with p hp β _ hβ z hz G hGe a t
          exact hp z hz β hβ G hGe a t
        rcases List.mem_append.1 hg with hg | hg
        · simp only [leadExp, List.mem_singleton] at hg
          subst hg
          exact hlead [] (by simp)
        · simp only [sigmaTExp, List.mem_map] at hg
          obtain ⟨o, ho, rfl⟩ := hg
          exact hlead o (Moment_chainLabels_entries n o ho))
  -- `Err`
  obtain ⟨β₂, hβ₂, h₂⟩ := CutMoment_combine (F := llFilter d n c₀ c₁ c₀T)
    (fun (g : Σ m, Graph 3 m) ν p β => ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ a t : Zd d p.1.2, ∑ S ∈ g.2.wDLights.pathElig.powerset, (g.2.wDLights.pathRepl S).absVal
          (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
          (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t)
    𝒯.Err (by
      intro g hgE
      have hmem : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := List.mem_append_right _ hgE
      obtain ⟨⟨C, hN⟩, hK, hAE, hDC⟩ := hall.2 g hgE
      obtain ⟨hTD, hDA⟩ := hG1 g hmem
      have hord := hErrs g hgE
      have hdiag : (n : ℤ) + 1 ≤ g.2.diagOrd := by
        rw [hdo]
        split_ifs <;> omega
      obtain ⟨βg, hβg, hh⟩ := CutMoment_err graphSum'' labelPaths d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc
        hκ hε hc₀T n Sig hSE ε₀ hε₀ hε₀n hε₀d g.1 C g.2 hN hK hAE hDC hTD hDA
        (hG3 g (List.mem_append_right _ hgE)) (fun _ => by omega) (fun _ _ => hdiag)
      refine ⟨βg, hβg, fun ν hν => ?_⟩
      filter_upwards [hh ν hν] with p hp β hβ0 hβ z hz G hGe a t
      exact hp z hz β hβ0 hβ G hGe a t)
  -- `Q`
  have hQprops : ∀ g ∈ 𝒯.Q, (∃ C, g.2.Normal C) ∧ g.2.TKinds n ∧ g.2.AtExternals ∧
      g.2.DoublyConnected ∧ g.2.TensorDiffusive ∧ g.2.DotsAcyclic ∧ 2 ≤ g.2.diagOrd := by
    intro g hgQ
    have hmem : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err :=
      List.mem_append_left _ (List.mem_append_right _ hgQ)
    obtain ⟨hC, hK, hAE, hDC⟩ := hall.1 g (List.mem_append_right _ hgQ)
    obtain ⟨hTD, hDA⟩ := hG1 g hmem
    obtain ⟨-, hord⟩ := hQs g hgQ
    refine ⟨hC, hK, hAE, hDC, hTD, hDA, ?_⟩
    rw [hdo]
    by_cases hpm : g.2.pmBlockB = true
    · have := hD63.2.2.2.2.1 g hgQ hpm
      simp only [hpm, ite_true]; omega
    · simp only [hpm]; simp; omega
  obtain ⟨β₃, hβ₃, h₃⟩ := CutMoment_combine (F := llFilter d n c₀ c₁ c₀T)
    (fun (g : Σ m, Graph 3 m) ν p β => ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ a t : Zd d p.1.2,
          ((g.1 = 0 ∨ g.2.DiagRecoll) →
            g.2.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
              (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t) ∧
          (g.1 ≠ 0 → ¬ g.2.DiagRecoll → ∀ (v : Fin g.1) (c : Zd d p.1.2),
            g.2.absValHook (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] v
                (fun y => Real.sqrt (bB d p.1.2 p.1.1 c y)) ≤
              (p.1.1 : ℝ) ^ (-(3 * (d : ℝ) / 8)) * bB d p.1.2 p.1.1 a t))
    𝒯.Q (by
      intro g hgQ
      obtain ⟨⟨C, hN⟩, hK, hAE, hDC, hTD, hDA, h2⟩ := hQprops g hgQ
      by_cases hcl : g.1 = 0 ∨ g.2.DiagRecoll
      · obtain ⟨βg, hβg, hh⟩ := CutMoment_graph graphSum'' d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε
          hc₀T n Sig hSE ε₀ hε₀ hε₀n hε₀d g.1 C g.2 hN hK hAE hDC hTD hDA (fun _ => h2)
          (fun hnI hdr => by
            rcases hcl with h | h
            · exact absurd h hnI
            · exact absurd h hdr)
        refine ⟨βg, hβg, fun ν hν => ?_⟩
        filter_upwards [hh ν hν] with p hp β hβ0 hβ z hz G hGe a t
        refine ⟨fun _ => hp z hz β hβ0 hβ G hGe a t, fun hnI hdr => ?_⟩
        rcases hcl with h | h
        · exact absurd h hnI
        · exact absurd h hdr
      · obtain ⟨hnI, hdr⟩ := not_or.1 hcl
        have hRt := hG3 g (List.mem_append_left _ (List.mem_append_right _ hgQ)) hnI hdr
        obtain ⟨βh, hβh, hh⟩ := CutMoment_hook hH d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε n Sig hSE
          g.1 C g.2 hN hK hAE hDC hTD hDA hdr hRt h2 hnI
        refine ⟨βh, hβh, fun ν hν => ?_⟩
        filter_upwards [hh] with p hp β hβ0 hβ z hz G hGe a t
        refine ⟨fun h => ?_, fun _ _ v c => hp z hz β hβ0 hβ G hGe v a t c⟩
        rcases h with h | h
        · exact absurd h hnI
        · exact absurd h hdr)
  refine ⟨min (min β₁ β₂) β₃, lt_min (lt_min hβ₁ hβ₂) hβ₃, fun ν hν => ?_⟩
  filter_upwards [h₁ ν hν, h₂ ν hν, h₃ ν hν] with p hp₁ hp₂ hp₃ z hz β hβ0 hβ G hGe a t
  have hb₁ : β ≤ β₁ := hβ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hb₂ : β ≤ β₂ := hβ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hb₃ : β ≤ β₃ := hβ.trans (min_le_right _ _)
  exact ⟨fun g hg => hp₁ β hβ0 hb₁ g hg z hz G hGe a t,
    fun g hg => hp₂ β hβ0 hb₂ g hg z hz G hGe a t,
    fun g hg => (hp₃ β hβ0 hb₃ g hg z hz G hGe a t).1,
    fun g hg => (hp₃ β hβ0 hb₃ g hg z hz G hGe a t).2⟩

/-! ## The cutoff -/

section Cutoff

variable {d L : ℕ} [NeZero L]

/-- `0 ≤ φ ≤ 1`, `φ` is `1`-Lipschitz, and `φ(t) > 0` forces `t < 2`. -/
private lemma CutMoment_phi (s t : ℝ) :
    0 ≤ cutPhi t ∧ cutPhi t ≤ 1 ∧ |cutPhi s - cutPhi t| ≤ |s - t| ∧ (0 < cutPhi t → t < 2) := by
  unfold cutPhi
  refine ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _), ?_, fun h => ?_⟩
  · have h1 : |min 1 (2 - s) - min 1 (2 - t)| ≤ |(2 - s) - (2 - t)| :=
      abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
    calc |max 0 (min 1 (2 - s)) - max 0 (min 1 (2 - t))|
        ≤ |min 1 (2 - s) - min 1 (2 - t)| := by
          rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
      _ ≤ |(2 - s) - (2 - t)| := h1
      _ = |s - t| := by rw [abs_sub_comm]; ring_nf
  · by_contra h2
    push Not at h2
    have : min 1 (2 - t) ≤ 0 := (min_le_right _ _).trans (by linarith)
    have : max 0 (min 1 (2 - t)) = 0 := max_eq_left this
    linarith

/-- `X_{ab} ≥ 0` for `S ≥ 0`. -/
private lemma CutMoment_X_nonneg {W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ} (hS : ∀ x y, 0 ≤ S x y)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) : 0 ≤ cutX W S G a b := by
  unfold cutX cutD
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) ?_
  · exact mul_nonneg (mul_nonneg (hS a i) (sq_nonneg _)) (hS j b)
  · unfold bB; positivity

/-- `1 + X_{ab} ≤ M` for `l ≥ 1`. -/
private lemma CutMoment_X_le_M {W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ} (hS : ∀ x y, 0 ≤ S x y)
    (l : ℕ) (hl : 1 ≤ l) (G : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) :
    1 + cutX W S G a b ≤ cutM l W S G := by
  have hX : ∀ a b, 0 ≤ 1 + cutX W S G a b := fun a b => by
    have := CutMoment_X_nonneg (W := W) hS G a b; linarith
  have h1 : (1 + cutX W S G a b) ^ l ≤ ∑ a', ∑ b', (1 + cutX W S G a' b') ^ l := by
    have e1 : (1 + cutX W S G a b) ^ l ≤ ∑ b', (1 + cutX W S G a b') ^ l :=
      Finset.single_le_sum (f := fun b' => (1 + cutX W S G a b') ^ l)
        (fun b' _ => pow_nonneg (hX a b') l) (Finset.mem_univ b)
    exact e1.trans (Finset.single_le_sum (f := fun a' => ∑ b', (1 + cutX W S G a' b') ^ l)
      (fun a' _ => Finset.sum_nonneg fun b' _ => pow_nonneg (hX a' b') l) (Finset.mem_univ a))
  unfold cutM
  calc 1 + cutX W S G a b = ((1 + cutX W S G a b) ^ l) ^ ((1 : ℝ) / l) := by
        rw [one_div, Real.pow_rpow_inv_natCast (hX a b) (by omega)]
    _ ≤ _ := Real.rpow_le_rpow (pow_nonneg (hX a b) l) h1 (by positivity)

/-- `0 ≤ C ≤ 1`; `C > 0` forces `Y ≤ W^β` and `M < 2 W^α`. -/
private lemma CutMoment_C (β α : ℝ) (l W : ℕ) (hW : 1 ≤ (W : ℝ)) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ) :
    0 ≤ cutC β α l W S G m ∧ cutC β α l W S G m ≤ 1 ∧
      (0 < cutC β α l W S G m → cutY W G m ≤ (W : ℝ) ^ β ∧ cutM l W S G < 2 * (W : ℝ) ^ α) := by
  have hW0 : (0 : ℝ) < W := by linarith
  unfold cutC
  split_ifs with hY
  · obtain ⟨h0, h1, -, h2⟩ := CutMoment_phi 0 (cutM l W S G / (W : ℝ) ^ α)
    refine ⟨h0, h1, fun h => ⟨hY, ?_⟩⟩
    have := h2 h
    rwa [div_lt_iff₀ (Real.rpow_pos_of_pos hW0 _)] at this
  · exact ⟨le_rfl, zero_le_one, fun h => absurd h (lt_irrefl 0)⟩

/-- `0 ≤ Z_{ab} ≤ 2 W^α`, `Z_{ab} ≤ X_{ab}`; `Z = 0` when `C = 0`. -/
private lemma CutMoment_Z (β α : ℝ) (l W : ℕ) (hl : 1 ≤ l) (hW : 1 ≤ (W : ℝ))
    {S : Matrix (Zd d L) (Zd d L) ℝ} (hS : ∀ x y, 0 ≤ S x y) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (m : ℂ) (a b : Zd d L) :
    0 ≤ cutZ β α l W S G m a b ∧ cutZ β α l W S G m a b ≤ 2 * (W : ℝ) ^ α := by
  obtain ⟨h0, h1, h2⟩ := CutMoment_C β α l W hW S G m
  have hX := CutMoment_X_nonneg (W := W) hS G a b
  unfold cutZ
  refine ⟨mul_nonneg h0 hX, ?_⟩
  rcases h0.lt_or_eq with hC | hC
  · have hM := CutMoment_X_le_M (W := W) hS l hl G a b
    have := (h2 hC).2
    calc cutC β α l W S G m * cutX W S G a b ≤ 1 * cutX W S G a b :=
          mul_le_mul_of_nonneg_right h1 hX
      _ ≤ _ := by linarith
  · rw [← hC, zero_mul]; positivity

end Cutoff

/-! ## The soft maximum under a perturbation -/

/-- `|(1 + x')^l − (1 + x)^l| ≤ 2 l ε (1 + x)^l` when `|x − x'| ≤ ε ≤ δ` and `(1 + δ)^{l−1} ≤ 2`. -/
private lemma CutMoment_pow_pert (l : ℕ) (x x' ε δ : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (hε : |x - x'| ≤ ε) (hεδ : ε ≤ δ) (hδ : (1 + δ) ^ (l - 1) ≤ 2) :
    |(1 + x') ^ l - (1 + x) ^ l| ≤ 2 * l * ε * (1 + x) ^ l := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hε
  have hδ0 : 0 ≤ δ := hε0.trans hεδ
  have hmax : max |1 + x'| |1 + x| ≤ (1 + x) * (1 + δ) := by
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    refine max_le ?_ (le_mul_of_one_le_right (by linarith) (by linarith))
    have := (abs_le.1 hε).1
    nlinarith
  have h := abs_pow_sub_pow_le (1 + x') (1 + x) l
  have e1 : |(1 + x') - (1 + x)| ≤ ε := by rw [abs_sub_comm]; ring_nf; ring_nf at hε; linarith
  calc |(1 + x') ^ l - (1 + x) ^ l| ≤ |(1 + x') - (1 + x)| * l * max |1 + x'| |1 + x| ^ (l - 1) := h
    _ ≤ ε * l * ((1 + x) * (1 + δ)) ^ (l - 1) := by gcongr
    _ = ε * l * ((1 + x) ^ (l - 1) * (1 + δ) ^ (l - 1)) := by rw [mul_pow]
    _ ≤ ε * l * ((1 + x) ^ l * 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_right₀ (by linarith) (Nat.sub_le l 1))
          hδ (by positivity) (by positivity)) (by positivity)
    _ = 2 * l * ε * (1 + x) ^ l := by ring

/-- **The soft maximum `M = (Σ_i (1 + X_i)^l)^{1/l}` under a perturbation**: if
`|X_i − X'_i| ≤ ε_i ≤ δ`, `(1 + δ)^{l−1} ≤ 2` and `ρ = 2l Σ_i w_i ε_i ≤ 1/2` with
`w_i = (1 + X_i)^l / Σ_j (1 + X_j)^l`, then `|M' − M| ≤ ρ M`. -/
private lemma CutMoment_softmax {κ : Type*} [Fintype κ] [Nonempty κ] (l : ℕ) (hl : 1 ≤ l)
    (X X' ε : κ → ℝ) (δ : ℝ) (w : κ → ℝ) (hw : ∀ i, w i = (1 + X i) ^ l / ∑ j, (1 + X j) ^ l)
    (hX : ∀ i, 0 ≤ X i) (hX' : ∀ i, 0 ≤ X' i)
    (hε : ∀ i, |X i - X' i| ≤ ε i) (hεδ : ∀ i, ε i ≤ δ) (hδ : (1 + δ) ^ (l - 1) ≤ 2)
    (hρ : 2 * l * ∑ i, w i * ε i ≤ 1 / 2) :
    |(∑ i, (1 + X' i) ^ l) ^ ((1 : ℝ) / l) - (∑ i, (1 + X i) ^ l) ^ ((1 : ℝ) / l)| ≤
      (2 * l * ∑ i, w i * ε i) * (∑ i, (1 + X i) ^ l) ^ ((1 : ℝ) / l) := by
  simp only [hw] at hρ ⊢
  set A := ∑ i, (1 + X i) ^ l with hA
  set A' := ∑ i, (1 + X' i) ^ l with hA'
  set ρ := 2 * l * ∑ i, (1 + X i) ^ l / A * ε i with hρdef
  have hA0 : 0 < A := by
    obtain ⟨i⟩ := ‹Nonempty κ›
    have h1 : 1 ≤ (1 + X i) ^ l := one_le_pow₀ (by linarith [hX i])
    have : (1 + X i) ^ l ≤ A := Finset.single_le_sum (f := fun j => (1 + X j) ^ l)
      (fun j _ => pow_nonneg (by linarith [hX j]) l) (Finset.mem_univ i)
    linarith
  have hA'0 : 0 ≤ A' := Finset.sum_nonneg fun i _ => pow_nonneg (by linarith [hX' i]) l
  have hε0 : ∀ i, 0 ≤ ε i := fun i => (abs_nonneg _).trans (hε i)
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => mul_nonneg ?_ (hε0 i))
    exact div_nonneg (pow_nonneg (by linarith [hX i]) l) hA0.le
  clear_value ρ A A'
  have hdiff : |A' - A| ≤ ρ * A := by
    have h1 : |A' - A| ≤ ∑ i, 2 * l * ε i * (1 + X i) ^ l := by
      rw [hA, hA', ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact CutMoment_pow_pert l (X i) (X' i) (ε i) δ (hX i) (hX' i) (hε i) (hεδ i) hδ
    refine h1.trans (le_of_eq ?_)
    have e : ρ * A = ∑ i, 2 * l * ((1 + X i) ^ l / A * ε i) * A := by
      rw [hρdef, mul_assoc, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have he0 : 0 ≤ (1 : ℝ) / l := by positivity
  have he1 : (1 : ℝ) / l ≤ 1 := by rw [div_le_one hl0]; exact_mod_cast hl
  set M := A ^ ((1 : ℝ) / l) with hM
  have hup : A' ^ ((1 : ℝ) / l) ≤ (1 + ρ) * M := by
    have h1 : A' ≤ A * (1 + ρ) := by have := (abs_le.1 hdiff).2; nlinarith
    calc A' ^ ((1 : ℝ) / l) ≤ (A * (1 + ρ)) ^ ((1 : ℝ) / l) := Real.rpow_le_rpow hA'0 h1 he0
      _ = M * (1 + ρ) ^ ((1 : ℝ) / l) := by rw [Real.mul_rpow hA0.le (by linarith)]
      _ ≤ M * (1 + ρ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hA0.le _)
          calc (1 + ρ) ^ ((1 : ℝ) / l) ≤ (1 + ρ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) he1
            _ = 1 + ρ := Real.rpow_one _
      _ = (1 + ρ) * M := by ring
  have hlo : (1 - ρ) * M ≤ A' ^ ((1 : ℝ) / l) := by
    have h1 : A * (1 - ρ) ≤ A' := by have := (abs_le.1 hdiff).1; nlinarith
    have h1ρ : 0 < 1 - ρ := by linarith
    calc (1 - ρ) * M ≤ (1 - ρ) ^ ((1 : ℝ) / l) * M := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hA0.le _)
          calc 1 - ρ = (1 - ρ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (1 - ρ) ^ ((1 : ℝ) / l) :=
                Real.rpow_le_rpow_of_exponent_ge h1ρ (by linarith) he1
      _ = (A * (1 - ρ)) ^ ((1 : ℝ) / l) := by
          rw [Real.mul_rpow hA0.le h1ρ.le]; ring
      _ ≤ A' ^ ((1 : ℝ) / l) := Real.rpow_le_rpow (by positivity) h1 he0
  rw [abs_le]
  constructor <;> nlinarith

section Pair

variable {d L : ℕ} [NeZero L]

/-- The weights `w_i = (1 + X_i)^l / Σ_j (1 + X_j)^l` of the soft maximum, `i = (a, b)`. -/
private def CutMoment_w (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (i : Zd d L × Zd d L) : ℝ :=
  (1 + cutX W S G i.1 i.2) ^ l / ∑ j : Zd d L × Zd d L, (1 + cutX W S G j.1 j.2) ^ l

/-- `h_y(a, b) = B_{ay}^{1/2} + B_{by}^{1/2}`. -/
private def CutMoment_h (d L W : ℕ) [NeZero L] (y : Zd d L) (i : Zd d L × Zd d L) : ℝ :=
  Real.sqrt (bB d L W i.1 y) + Real.sqrt (bB d L W i.2 y)

/-- `J*_y = h_y(a, b) + Σ_i w_i h_y(i)`. -/
private def CutMoment_J (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (a b y : Zd d L) : ℝ :=
  CutMoment_h d L W y (a, b) + ∑ i, CutMoment_w l W S G i * CutMoment_h d L W y i

omit [NeZero L] in
private lemma CutMoment_h_nonneg (W : ℕ) [NeZero L] (y : Zd d L) (i : Zd d L × Zd d L) :
    0 ≤ CutMoment_h d L W y i := by
  unfold CutMoment_h; positivity

private lemma CutMoment_w_nonneg (l W : ℕ) {S : Matrix (Zd d L) (Zd d L) ℝ}
    (hS : ∀ x y, 0 ≤ S x y) (G : Matrix (Zd d L) (Zd d L) ℂ) (i : Zd d L × Zd d L) :
    0 ≤ CutMoment_w l W S G i := by
  unfold CutMoment_w
  refine div_nonneg (pow_nonneg ?_ _) (Finset.sum_nonneg fun j _ => pow_nonneg ?_ _)
  · linarith [CutMoment_X_nonneg (W := W) hS G i.1 i.2]
  · linarith [CutMoment_X_nonneg (W := W) hS G j.1 j.2]

private lemma CutMoment_w_sum (l W : ℕ) {S : Matrix (Zd d L) (Zd d L) ℝ}
    (hS : ∀ x y, 0 ≤ S x y) (G : Matrix (Zd d L) (Zd d L) ℂ) :
    ∑ i, CutMoment_w l W S G i = 1 := by
  unfold CutMoment_w
  rw [← Finset.sum_div]
  refine div_self (ne_of_gt ?_)
  have h1 : (1 : ℝ) ≤ (1 + cutX W S G (0 : Zd d L) 0) ^ l :=
    one_le_pow₀ (by linarith [CutMoment_X_nonneg (W := W) hS G 0 0])
  have := Finset.single_le_sum (f := fun j : Zd d L × Zd d L => (1 + cutX W S G j.1 j.2) ^ l)
    (fun j _ => pow_nonneg (by linarith [CutMoment_X_nonneg (W := W) hS G j.1 j.2]) l)
    (Finset.mem_univ ((0 : Zd d L), (0 : Zd d L)))
  simp only at this
  linarith

/-- `0 ≤ J*_y`, and `J*_y ≤ 4 W^{−d/2}`. -/
private lemma CutMoment_J_le (l W : ℕ) (hd : 2 ≤ d) (hW : 1 ≤ (W : ℝ))
    {S : Matrix (Zd d L) (Zd d L) ℝ} (hS : ∀ x y, 0 ≤ S x y) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (a b y : Zd d L) :
    0 ≤ CutMoment_J l W S G a b y ∧ CutMoment_J l W S G a b y ≤ 4 * (W : ℝ) ^ (-((d : ℝ) / 2)) := by
  have hh : ∀ i, CutMoment_h d L W y i ≤ 2 * (W : ℝ) ^ (-((d : ℝ) / 2)) := fun i => by
    unfold CutMoment_h
    linarith [CutMoment_sqrtB_le d L W hd hW i.1 y, CutMoment_sqrtB_le d L W hd hW i.2 y]
  have hs : ∑ i, CutMoment_w l W S G i * CutMoment_h d L W y i ≤
      2 * (W : ℝ) ^ (-((d : ℝ) / 2)) := by
    calc ∑ i, CutMoment_w l W S G i * CutMoment_h d L W y i
        ≤ ∑ i, CutMoment_w l W S G i * (2 * (W : ℝ) ^ (-((d : ℝ) / 2))) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hh i)
            (CutMoment_w_nonneg l W hS G i)
      _ = _ := by rw [← Finset.sum_mul, CutMoment_w_sum l W hS G, one_mul]
  unfold CutMoment_J
  refine ⟨add_nonneg (CutMoment_h_nonneg W y _) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (CutMoment_w_nonneg l W hS G i) (CutMoment_h_nonneg W y i)), ?_⟩
  linarith [hh (a, b)]

/-- `(1 + Z)^q ≤ 2^q (1 + Z^q)` for `Z ≥ 0`. -/
private lemma CutMoment_one_add_pow (Z : ℝ) (hZ : 0 ≤ Z) (q : ℕ) :
    (1 + Z) ^ q ≤ 2 ^ q * (1 + Z ^ q) := by
  rcases le_total Z 1 with h | h
  · calc (1 + Z) ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ ≤ 2 ^ q * (1 + Z ^ q) := le_mul_of_one_le_right (by positivity)
          (by linarith [pow_nonneg hZ q])
  · calc (1 + Z) ^ q ≤ (2 * Z) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * Z ^ q := mul_pow _ _ _
      _ ≤ 2 ^ q * (1 + Z ^ q) := by gcongr; linarith

/-- **The cutoff under the resampling of a row**: if `Y(G), Y(G') ≤ W^β`
and `|X_{ab}(G) − X_{ab}(G')| ≤ W^{4β} h_y(a, b)` for all `a, b`, with `W^{4β} h_y ≤ δ`,
`(1 + δ)^{l−1} ≤ 2`, `2lδ ≤ 1/2` and `32 l W^{4β+α} J*_y ≤ 1`, then
`|C Z_{ab}^q − C' Z'^q_{ab}| ≤ (8l + 32 l q 2^q) W^{4β+α} (1 + Z_{ab}^q) J*_y`. -/
private lemma CutMoment_pair (β α : ℝ) (hα : 0 ≤ α) (l W q : ℕ) (hl : 1 ≤ l)
    (hW : 1 ≤ (W : ℝ)) {S : Matrix (Zd d L) (Zd d L) ℝ} (hS : ∀ x y, 0 ≤ S x y)
    (G G' : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ) (a b y : Zd d L)
    (hY : cutY W G m ≤ (W : ℝ) ^ β) (hY' : cutY W G' m ≤ (W : ℝ) ^ β)
    (hX : ∀ a' b', |cutX W S G a' b' - cutX W S G' a' b'| ≤
      (W : ℝ) ^ (4 * β) * CutMoment_h d L W y (a', b'))
    (δ : ℝ) (hδ : ∀ i, (W : ℝ) ^ (4 * β) * CutMoment_h d L W y i ≤ δ)
    (hδl : (1 + δ) ^ (l - 1) ≤ 2) (hδρ : 2 * l * δ ≤ 1 / 2)
    (hsmall : 32 * l * (W : ℝ) ^ (4 * β + α) * CutMoment_J l W S G a b y ≤ 1) :
    |cutC β α l W S G m * cutZ β α l W S G m a b ^ q -
        cutC β α l W S G' m * cutZ β α l W S G' m a b ^ q| ≤
      (8 * l + 32 * l * q * 2 ^ q) * (W : ℝ) ^ (4 * β + α) *
        (1 + cutZ β α l W S G m a b ^ q) * CutMoment_J l W S G a b y := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hWα : 1 ≤ (W : ℝ) ^ α := Real.one_le_rpow hW hα
  have hWαp : 0 < (W : ℝ) ^ α := by linarith
  have hW4 : 0 ≤ (W : ℝ) ^ (4 * β) := Real.rpow_nonneg hW0.le _
  have hW4α : (W : ℝ) ^ (4 * β + α) = (W : ℝ) ^ (4 * β) * (W : ℝ) ^ α := Real.rpow_add hW0 _ _
  set C := cutC β α l W S G m with hCdef
  set C' := cutC β α l W S G' m with hC'def
  set X := cutX W S G a b with hXdef
  set X' := cutX W S G' a b with hX'def
  set Z := cutZ β α l W S G m a b with hZdef
  set Z' := cutZ β α l W S G' m a b with hZ'def
  set J := CutMoment_J l W S G a b y with hJdef
  set ε : Zd d L × Zd d L → ℝ := fun i => (W : ℝ) ^ (4 * β) * CutMoment_h d L W y i with hεdef
  set ρ := 2 * l * ∑ i, CutMoment_w l W S G i * ε i with hρdef
  obtain ⟨hC0, hC1, hCpos⟩ := CutMoment_C β α l W hW S G m
  obtain ⟨hC'0, hC'1, hC'pos⟩ := CutMoment_C β α l W hW S G' m
  have hX0 : 0 ≤ X := CutMoment_X_nonneg hS G a b
  have hZ0 : 0 ≤ Z := (CutMoment_Z β α l W hl hW hS G m a b).1
  have hZ'0 : 0 ≤ Z' := (CutMoment_Z β α l W hl hW hS G' m a b).1
  have hJ0 : 0 ≤ J := by
    rw [hJdef]; unfold CutMoment_J
    exact add_nonneg (CutMoment_h_nonneg W y _) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (CutMoment_w_nonneg l W hS G i) (CutMoment_h_nonneg W y i))
  have hK0 : (0 : ℝ) ≤ (8 * l + 32 * l * q * 2 ^ q) * (W : ℝ) ^ (4 * β + α) *
      (1 + Z ^ q) * J := by positivity
  by_cases hboth : C = 0 ∧ C' = 0
  · have hZz : Z = 0 := by rw [hZdef]; unfold cutZ; rw [← hCdef, hboth.1, zero_mul]
    have hZz' : Z' = 0 := by rw [hZ'def]; unfold cutZ; rw [← hC'def, hboth.2, zero_mul]
    rw [hboth.1, hboth.2]; simpa using hK0
  have hpos : 0 < C ∨ 0 < C' := by
    by_contra h
    push Not at h
    exact hboth ⟨le_antisymm h.1 hC0, le_antisymm h.2 hC'0⟩
  -- the soft maximum
  have hρ : ρ = (W : ℝ) ^ (4 * β) *
      (2 * l * ∑ i, CutMoment_w l W S G i * CutMoment_h d L W y i) := by
    rw [hρdef, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [hεdef]; ring
  have hρδ : ρ ≤ 2 * l * δ := by
    rw [hρdef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ i, CutMoment_w l W S G i * ε i ≤ ∑ i, CutMoment_w l W S G i * δ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hδ i)
            (CutMoment_w_nonneg l W hS G i)
      _ = δ := by rw [← Finset.sum_mul, CutMoment_w_sum l W hS G, one_mul]
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    refine mul_nonneg hW4 (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (CutMoment_w_nonneg l W hS G i) (CutMoment_h_nonneg W y i)))
  have hMeq : ∀ G₀ : Matrix (Zd d L) (Zd d L) ℂ, cutM l W S G₀ =
      (∑ i : Zd d L × Zd d L, (1 + cutX W S G₀ i.1 i.2) ^ l) ^ ((1 : ℝ) / l) := fun G₀ => by
    unfold cutM; congr 1; exact (Fintype.sum_prod_type' (fun a b => (1 + cutX W S G₀ a b) ^ l)).symm
  have : Nonempty (Zd d L × Zd d L) := ⟨((0 : Zd d L), (0 : Zd d L))⟩
  have hsm := CutMoment_softmax (κ := Zd d L × Zd d L) l hl (fun i => cutX W S G i.1 i.2)
    (fun i => cutX W S G' i.1 i.2)
    ε δ (CutMoment_w l W S G) (fun i => rfl) (fun i => CutMoment_X_nonneg (W := W) hS G i.1 i.2)
    (fun i => CutMoment_X_nonneg (W := W) hS G' i.1 i.2)
    (fun i => hX i.1 i.2) (fun i => hδ i) hδl (hρδ.trans hδρ)
  beta_reduce at hsm
  rw [← hMeq G, ← hMeq G', ← hρdef] at hsm
  obtain ⟨M, hMdef⟩ : ∃ M, M = cutM l W S G := ⟨_, rfl⟩
  obtain ⟨M', hM'def⟩ : ∃ M', M' = cutM l W S G' := ⟨_, rfl⟩
  rw [← hMdef, ← hM'def] at hsm
  have hXM : 1 + X ≤ M := hMdef ▸ CutMoment_X_le_M hS l hl G a b
  have hM4 : M ≤ 4 * (W : ℝ) ^ α := by
    rcases hpos with h | h
    · rw [hMdef]; linarith [(hCpos h).2]
    · have h2 := (hC'pos h).2
      rw [← hM'def] at h2
      have := (abs_le.1 hsm).1
      have hρ2 : ρ ≤ 1 / 2 := hρδ.trans hδρ
      nlinarith
  have hCC : |C - C'| ≤ 4 * ρ := by
    have e1 : C = cutPhi (M / (W : ℝ) ^ α) := by
      rw [hCdef, hMdef]; unfold cutC; simp only [hY, ↓reduceIte]
    have e2 : C' = cutPhi (M' / (W : ℝ) ^ α) := by
      rw [hC'def, hM'def]; unfold cutC; simp only [hY', ↓reduceIte]
    rw [e1, e2]
    refine (CutMoment_phi _ _).2.2.1.trans ?_
    rw [← sub_div, abs_div, abs_of_pos hWαp, div_le_iff₀ hWαp, abs_sub_comm]
    calc |M' - M| ≤ ρ * M := hsm
      _ ≤ ρ * (4 * (W : ℝ) ^ α) := mul_le_mul_of_nonneg_left hM4 hρ0
      _ = 4 * ρ * (W : ℝ) ^ α := by ring
  -- `|Z − Z'|` and `|C Z^q − C' Z'^q|`
  set sw := ∑ i, CutMoment_w l W S G i * CutMoment_h d L W y i with hsw
  set H := CutMoment_h d L W y (a, b) with hH
  have hs0 : 0 ≤ sw := Finset.sum_nonneg fun i _ => mul_nonneg (CutMoment_w_nonneg l W hS G i)
    (CutMoment_h_nonneg W y i)
  have hH0 : 0 ≤ H := CutMoment_h_nonneg W y (a, b)
  have hJe : J = H + sw := by rw [hJdef]; rfl
  set E := (W : ℝ) ^ (4 * β + α) with hE
  have hE4 : (W : ℝ) ^ (4 * β) ≤ E := by
    rw [hW4α]; exact le_mul_of_one_le_right hW4 hWα
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hE0 : 0 ≤ E := hW4.trans hE4
  have hρJ : 4 * ρ ≤ 8 * l * E * J := by
    have a1 : (W : ℝ) ^ (4 * β) * sw ≤ E * (H + sw) :=
      (mul_le_mul_of_nonneg_right hE4 hs0).trans (mul_le_mul_of_nonneg_left (by linarith) hE0)
    calc 4 * ρ = 8 * l * ((W : ℝ) ^ (4 * β) * sw) := by rw [hρ]; ring
      _ ≤ 8 * l * (E * (H + sw)) := mul_le_mul_of_nonneg_left a1 (by positivity)
      _ = 8 * l * E * J := by rw [hJe]; ring
  have hZZ : |Z - Z'| ≤ 32 * l * E * J := by
    have e : Z - Z' = (C - C') * X + C' * (X - X') := by
      rw [hZdef, hZ'def]; unfold cutZ; ring
    rw [e]
    have hXle : X ≤ 4 * (W : ℝ) ^ α := by linarith
    have h1 : |(C - C') * X| ≤ 4 * ρ * (4 * (W : ℝ) ^ α) := by
      rw [abs_mul, abs_of_nonneg hX0]
      exact mul_le_mul hCC hXle hX0 (by positivity)
    have h2 : |C' * (X - X')| ≤ (W : ℝ) ^ (4 * β) * H := by
      rw [abs_mul, abs_of_nonneg hC'0]
      exact (mul_le_of_le_one_left (abs_nonneg _) hC'1).trans (hX a b)
    have h3 : 4 * ρ * (4 * (W : ℝ) ^ α) = 32 * l * E * sw := by
      rw [hρ, hW4α]; ring
    have h4 : (W : ℝ) ^ (4 * β) * H ≤ E * H := mul_le_mul_of_nonneg_right hE4 hH0
    have h5 : E * H ≤ 32 * l * E * H := by
      have h6 : E * H ≤ (32 * l) * (E * H) :=
        le_mul_of_one_le_left (mul_nonneg hE0 hH0) (by linarith)
      calc E * H ≤ (32 * l) * (E * H) := h6
        _ = 32 * l * E * H := by ring
    have h7 : 32 * l * E * J = 32 * l * E * sw + 32 * l * E * H := by rw [hJe]; ring
    calc |(C - C') * X + C' * (X - X')| ≤ |(C - C') * X| + |C' * (X - X')| := abs_add_le _ _
      _ ≤ 32 * l * E * J := by linarith
  have hZZ1 : |Z - Z'| ≤ 1 := hZZ.trans hsmall
  have hZ'le : Z' ≤ 1 + Z := by linarith [(abs_le.1 hZZ1).1]
  have hpow : |Z ^ q - Z' ^ q| ≤ 32 * l * E * J * q * (2 ^ q * (1 + Z ^ q)) := by
    have h := abs_pow_sub_pow_le Z Z' q
    rw [abs_of_nonneg hZ0, abs_of_nonneg hZ'0] at h
    have hmax : max Z Z' ≤ 1 + Z := max_le (by linarith) hZ'le
    have h1 : max Z Z' ^ (q - 1) ≤ 2 ^ q * (1 + Z ^ q) :=
      (pow_le_pow_left₀ (le_max_of_le_left hZ0) hmax _).trans
        ((pow_le_pow_right₀ (by linarith) (Nat.sub_le q 1)).trans (CutMoment_one_add_pow Z hZ0 q))
    calc |Z ^ q - Z' ^ q| ≤ |Z - Z'| * q * max Z Z' ^ (q - 1) := h
      _ ≤ 32 * l * E * J * q * (2 ^ q * (1 + Z ^ q)) := by gcongr
  have e : C * Z ^ q - C' * Z' ^ q = (C - C') * Z ^ q + C' * (Z ^ q - Z' ^ q) := by ring
  rw [e]
  have hZq : 0 ≤ Z ^ q := pow_nonneg hZ0 q
  have hEJ : 0 ≤ 8 * l * E * J := by positivity
  have g1 : |(C - C') * Z ^ q| ≤ 8 * l * E * J * (1 + Z ^ q) := by
    rw [abs_mul, abs_of_nonneg hZq]
    exact (mul_le_mul_of_nonneg_right (hCC.trans hρJ) hZq).trans
      (mul_le_mul_of_nonneg_left (by linarith) hEJ)
  have g2 : |C' * (Z ^ q - Z' ^ q)| ≤ 32 * l * E * J * q * (2 ^ q * (1 + Z ^ q)) := by
    rw [abs_mul, abs_of_nonneg hC'0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hC'1).trans hpow
  calc |(C - C') * Z ^ q + C' * (Z ^ q - Z' ^ q)|
      ≤ |(C - C') * Z ^ q| + |C' * (Z ^ q - Z' ^ q)| := abs_add_le _ _
    _ ≤ 8 * l * E * J * (1 + Z ^ q) + 32 * l * E * J * q * (2 ^ q * (1 + Z ^ q)) :=
        add_le_add g1 g2
    _ = (8 * l + 32 * l * q * 2 ^ q) * E * (1 + Z ^ q) * J := by ring

end Pair

/-! ## Resampling a row: the exchange of the two samples, measurability -/

section Resample

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Resampling row `y` of `ω^{[y,η]}` from `η^{[y,ω]}` gives back `ω`. -/
private lemma CutMoment_res_res (y : ι) (ω η : Sample ι) :
    resampleRow y (resampleRow y ω η) (resampleRow y η ω) = ω := by
  funext c
  unfold resampleRow
  by_cases h : c ∈ rowCoords y
  · simp [Finset.piecewise_eq_of_mem _ _ _ h]
  · simp [Finset.piecewise_eq_of_notMem _ _ _ h]

/-- **The exchange of the two samples on row `y`**, `(ω, η) ↦ (ω^{[y,η]}, η^{[y,ω]})`, preserves
the product law of [I, Assumption 1.1]. -/
private lemma CutMoment_swap (S : Matrix ι ι ℝ) (y : ι) :
    MeasurePreserving
      (fun q : Sample ι × Sample ι => (resampleRow y q.2 q.1, resampleRow y q.1 q.2))
      ((gaussLaw S).prod (gaussLaw S)) ((gaussLaw S).prod (gaussLaw S)) := by
  set ν : Coord ι → Measure ℝ := fun c => gaussianReal 0 (coordVar S c) with hν
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Coord ι) ν ν
  have hsw : MeasurePreserving
      (fun (a : Coord ι → ℝ × ℝ) c => (if c ∈ rowCoords y then Prod.swap else id) (a c))
      (Measure.pi fun c => (ν c).prod (ν c)) (Measure.pi fun c => (ν c).prod (ν c)) := by
    refine measurePreserving_pi _ _ fun c => ?_
    split_ifs
    · exact Measure.measurePreserving_swap
    · exact MeasurePreserving.id _
  have h := he.comp (hsw.comp he.symm)
  have hg : gaussLaw S = Measure.pi ν := rfl
  rw [hg]
  convert h using 1
  funext q
  simp only [Function.comp, MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.coe_mk,
    MeasurableEquiv.symm_mk, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    resampleRow]
  ext c
  · by_cases h : c ∈ rowCoords y <;> simp [h]
  · by_cases h : c ∈ rowCoords y <;> simp [h]

end Resample

section Meas

variable {d L : ℕ} [NeZero L]

/-- The entries of `G(ω)` are measurable in the sample. -/
private lemma CutMoment_meas_G (z : ℂ) (hz : 0 < z.im) (x y : Zd d L) :
    Measurable fun ω : Sample (Zd d L) => green (hmat ω) z x y :=
  (polyMeas_of_testFn _ (testFn_green z hz.ne' x y)).1

/-- `X_{ab}(G(ω))` is measurable. -/
private lemma CutMoment_meas_X (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (z : ℂ) (hz : 0 < z.im)
    (a b : Zd d L) : Measurable fun ω : Sample (Zd d L) => cutX W S (green (hmat ω) z) a b := by
  unfold cutX cutD
  refine Measurable.div_const (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => ?_) _
  exact ((CutMoment_meas_G z hz i j).norm.pow_const 2).const_mul _ |>.mul_const _

/-- `Y(G(ω))` is measurable. -/
private lemma CutMoment_meas_Y (W : ℕ) (z : ℂ) (hz : 0 < z.im) (m : ℂ) :
    Measurable fun ω : Sample (Zd d L) => cutY W (green (hmat ω) z) m := by
  unfold cutY entryErr
  refine Measurable.iSup fun i => Measurable.iSup fun j => ?_
  exact ((CutMoment_meas_G z hz i j).sub_const _).norm.div_const _

/-- `M(G(ω))` is measurable. -/
private lemma CutMoment_meas_M (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (z : ℂ) (hz : 0 < z.im) :
    Measurable fun ω : Sample (Zd d L) => cutM l W S (green (hmat ω) z) := by
  unfold cutM
  refine Measurable.pow_const (Finset.measurable_sum _ fun a _ =>
    Finset.measurable_sum _ fun b _ => ?_) _
  exact ((CutMoment_meas_X W S z hz a b).const_add 1).pow_const l

/-- `C(G(ω))` and `Z_{ab}(G(ω))` are measurable. -/
private lemma CutMoment_meas_CZ (β α : ℝ) (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (z : ℂ)
    (hz : 0 < z.im) (a b : Zd d L) :
    Measurable (fun ω : Sample (Zd d L) => cutC β α l W S (green (hmat ω) z) (msc z)) ∧
      Measurable (fun ω : Sample (Zd d L) => cutZ β α l W S (green (hmat ω) z) (msc z) a b) := by
  have hC : Measurable (fun ω : Sample (Zd d L) => cutC β α l W S (green (hmat ω) z) (msc z)) := by
    unfold cutC
    refine Measurable.ite (measurableSet_le (CutMoment_meas_Y W z hz _) measurable_const) ?_
      measurable_const
    have hφ : Continuous cutPhi := by unfold cutPhi; fun_prop
    exact hφ.measurable.comp ((CutMoment_meas_M l W S z hz).div_const _)
  exact ⟨hC, hC.mul (CutMoment_meas_X W S z hz a b)⟩

end Meas

/-! ## The graphs of `Q`: the exchange of `Q_y` -/

section QGraph

variable {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) {W L : ℕ} [NeZero L]

/-- `(ω, η) ↦ ω^{[y,η]}` is measurable. -/
private lemma CutMoment_meas_res {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι) :
    Measurable fun q : Sample ι × Sample ι => resampleRow y q.2 q.1 := by
  refine Measurable.of_eval fun c => ?_
  unfold resampleRow
  by_cases h : c ∈ rowCoords y
  · simp only [Finset.piecewise_eq_of_mem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_snd
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ h]
    exact (measurable_pi_apply c).comp measurable_fst

/-- **One graph of `Q` against a bounded weight `U`**: for a `Q`-graph `g`
with the kinds of [II, Def 3.2] and its label `Q_u`, and a measurable `0 ≤ U ≤ U_max`, if outside
measurable sets `T_y` of pairs `(ω, η)` the difference `|U(ω) − U(ω^{[y,η]})|` is at most
`K (1 + Z(ω)) J(ω, y)` on `Γ(ω)` and `0` off it, the weighted sum
`Σ_σ |c_σ| |R_σ(ω)| J(ω, σ(u))` is at most `B_nd` on `Γ`, and `Σ_σ |c_σ| |R_σ(ω)| ≤ A_max`, then
`|E U g_{𝔞,tt}| ≤ K B_nd E(1 + Z) + 2 U_max A_max Σ_y P(T_y)`. -/
private lemma CutMoment_Q (z : ℂ) (hz : 0 < z.im) (hS : (Smat P.ψ W L).IsSymm)
    (hS0 : ∀ x y, 0 ≤ Smat P.ψ W L x y) {n N : ℕ} (g : Graph 3 n) (hK : g.TKinds N)
    (u : Atom 3 n) (hu : ∃ c ∈ g.comps, c.label = some (.Q, u))
    (hall : ∀ c ∈ g.comps, (c.kind.isRandom = true ∨ c.label.isSome = true) →
      c.label = some (.Q, u))
    (a t : Zd d L) (U Zf : Sample (Zd d L) → ℝ) (hUm : Measurable U)
    (Gd : Set (Sample (Zd d L))) (J : Sample (Zd d L) → Zd d L → ℝ) (K Bnd Amax Umax : ℝ)
    (hK0 : 0 ≤ K) (hBnd : 0 ≤ Bnd) (hU0 : ∀ ω, 0 ≤ U ω) (hU1 : ∀ ω, U ω ≤ Umax)
    (hZ0 : ∀ ω, 0 ≤ Zf ω) (hZi : Integrable Zf (gaussLaw (Smat P.ψ W L)))
    (T : Zd d L → Set (Sample (Zd d L) × Sample (Zd d L))) (hTm : ∀ y, MeasurableSet (T y))
    (hgood : ∀ y ω η, (ω, η) ∉ T y →
      |U ω - U (resampleRow y η ω)| ≤ Gd.indicator (fun ω' => K * (1 + Zf ω') * J ω' y) ω)
    (hJ0 : ∀ ω y, 0 ≤ J ω y)
    (hBndH : ∀ ω ∈ Gd, ∑ s : Fin n → Zd d L, ‖g.coeff.eval (msc z)‖ *
      (g.comps.map fun c => ‖Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω) z))
        (Sum.elim ![a, t, t] s) c‖).prod * J ω (Sum.elim ![a, t, t] s u) ≤ Bnd)
    (hA : ∀ ω, ∑ s : Fin n → Zd d L, ‖g.coeff.eval (msc z)‖ *
      (g.comps.map fun c => ‖Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω) z))
        (Sum.elim ![a, t, t] s) c‖).prod ≤ Amax) :
    ‖∫ ω, (U ω : ℂ) * g.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, t, t] ω
        ∂(gaussLaw (Smat P.ψ W L))‖ ≤
      K * Bnd * ∫ ω, (1 + Zf ω) ∂(gaussLaw (Smat P.ψ W L)) +
        2 * Umax * Amax *
          ∑ y, ((gaussLaw (Smat P.ψ W L)).prod (gaussLaw (Smat P.ψ W L))).real (T y) := by
  set S := Smat P.ψ W L with hSdef
  set μ := gaussLaw S with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw S
  have hL := pqLaws_Pexp_poly S hS hS0
  set D := rbmData d P Sig W L z with hD
  have hl : g.labels = [(.Q, u)] := QTerm_labels_eq g u hu hall
  have hR : ∀ c ∈ g.comps, c.kind.isRandom = true → c.label.isSome = true := fun c hc h => by
    rw [hall c hc (Or.inl h)]; rfl
  have hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.Q, u) := by
    intro c hc
    rcases h : c.label with _ | ℓ
    · left; rfl
    · right; rw [← h]; exact hall c hc (Or.inr (by rw [h]; rfl))
  set σ : (Fin n → Zd d L) → Atom 3 n → Zd d L := fun s => Sum.elim ![a, t, t] s with hσ
  set lab : (Fin n → Zd d L) → Sample (Zd d L) → ℂ := fun s => QTerm_lab g u D (σ s) with hlabdef
  set dt : (Fin n → Zd d L) → ℂ := fun s => QTerm_det g (D 0) (σ s) with hdt
  have hlabP : ∀ s, PolyMeas (lab s) := fun s =>
    QTerm_polyMeas_prod d P Sig W L z hz hS hS0 g hK (σ s) _ fun c hc => List.mem_of_mem_filter hc
  have hUP : PolyMeas fun ω => (U ω : ℂ) := by
    refine ⟨Complex.measurable_ofReal.comp hUm, Umax, 0, fun ω => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU0 ω), pow_zero, mul_one]
    exact hU1 ω
  -- the value of `g` as a sum over the labellings
  have hval : ∀ ω, g.valR ⟨Pexp S⟩ D ![a, t, t] ω =
      ∑ s, dt s * (lab s ω - Pexp S (σ s u) (lab s) ω) := by
    intro ω
    unfold Graph.valR
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [QTerm_termR_eq g _ hl S D _ ω, QTerm_det_const P Sig W L z g hR _ ω 0]
  have hnorm : ∀ ω s, ‖dt s‖ * ‖lab s ω‖ = ‖g.coeff.eval (msc z)‖ *
      (g.comps.map fun c => ‖Comp.val (gData S z Sig (green (hmat ω) z)) (σ s) c‖).prod := by
    intro ω s
    change ‖QTerm_det g (rbmData d P Sig W L z 0) (σ s)‖ *
      ‖QTerm_lab g u (rbmData d P Sig W L z) (σ s) ω‖ = _
    rw [QTerm_det_const P Sig W L z g hR (σ s) 0 ω]
    exact (QTerm_abs_term P Sig W L z g hK u hlab (σ s) ω).symm
  -- the exchange of `Q_y` and the resampled pairs
  set F : (Fin n → Zd d L) → Sample (Zd d L) × Sample (Zd d L) → ℝ := fun s q =>
    ‖lab s q.1‖ * |U q.1 - U (resampleRow (σ s u) q.2 q.1)| with hF
  set Dom : Sample (Zd d L) × Sample (Zd d L) → ℝ := fun q =>
    2 * Umax * Amax * ∑ y, (T y).indicator (fun _ => 1) q + K * (1 + Zf q.1) * Bnd with hDom
  have hUmax0 : 0 ≤ Umax := (hU0 0).trans (hU1 0)
  have hAmax0 : 0 ≤ Amax := by
    refine le_trans ?_ (hA 0)
    exact Finset.sum_nonneg fun s _ => mul_nonneg (norm_nonneg _) (List.prod_nonneg fun x hx => by
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _)
  have hDomi : Integrable Dom (μ.prod μ) := by
    refine Integrable.add ((integrable_finsetSum _ fun y _ =>
      (integrable_const (1 : ℝ)).indicator (hTm y)).const_mul _) ?_
    have : Integrable (fun q : Sample (Zd d L) × Sample (Zd d L) => 1 + Zf q.1) (μ.prod μ) :=
      ((integrable_const 1).add hZi).comp_fst μ
    exact (this.const_mul K).mul_const Bnd
  have hFm : ∀ s, Measurable (F s) := fun s =>
    ((hlabP s).1.comp measurable_fst).norm.mul (continuous_abs.measurable.comp
      ((hUm.comp measurable_fst).sub (hUm.comp (CutMoment_meas_res (σ s u)))))
  have hF0 : ∀ s q, 0 ≤ F s q := fun s q => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  -- the pointwise bound of the sum
  have hsumF : ∀ q, ∑ s, ‖dt s‖ * F s q ≤ Dom q := by
    intro q
    have hpt : ∀ s, ‖dt s‖ * F s q ≤ ‖dt s‖ * ‖lab s q.1‖ *
        ((T (σ s u)).indicator (fun _ => 2 * Umax) q +
          Gd.indicator (fun ω' => K * (1 + Zf ω') * J ω' (σ s u)) q.1) := by
      intro s
      rw [hF, ← mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      by_cases hq : q ∈ T (σ s u)
      · rw [Set.indicator_of_mem hq]
        have h1 := hU0 q.1; have h2 := hU1 q.1
        have h3 := hU0 (resampleRow (σ s u) q.2 q.1); have h4 := hU1 (resampleRow (σ s u) q.2 q.1)
        have : 0 ≤ Gd.indicator (fun ω' => K * (1 + Zf ω') * J ω' (σ s u)) q.1 :=
          Set.indicator_nonneg (fun ω' _ => mul_nonneg (mul_nonneg hK0 (by linarith [hZ0 ω']))
            (hJ0 ω' _)) _
        rw [abs_le]; constructor <;> linarith
      · rw [Set.indicator_of_notMem hq, zero_add]
        exact hgood (σ s u) q.1 q.2 hq
    refine (Finset.sum_le_sum fun s _ => hpt s).trans ?_
    simp only [mul_add, Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · -- the bad pairs
      have h1 : ∀ s, ‖dt s‖ * ‖lab s q.1‖ * (T (σ s u)).indicator (fun _ => 2 * Umax) q ≤
          ‖dt s‖ * ‖lab s q.1‖ * (2 * Umax * ∑ y, (T y).indicator (fun _ => 1) q) := by
        intro s
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        have hy : (T (σ s u)).indicator (fun _ => (1 : ℝ)) q ≤
            ∑ y, (T y).indicator (fun _ => 1) q :=
          Finset.single_le_sum (f := fun y => (T y).indicator (fun _ => (1 : ℝ)) q)
            (fun y _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ _)
        by_cases hq : q ∈ T (σ s u)
        · rw [Set.indicator_of_mem hq] at hy ⊢
          nlinarith
        · rw [Set.indicator_of_notMem hq]
          exact mul_nonneg (by linarith) (Finset.sum_nonneg fun y _ =>
            Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      refine (Finset.sum_le_sum fun s _ => h1 s).trans ?_
      rw [← Finset.sum_mul]
      have hsum : ∑ s, ‖dt s‖ * ‖lab s q.1‖ ≤ Amax := by
        simp only [hnorm]; exact hA q.1
      have h0 : 0 ≤ 2 * Umax * ∑ y, (T y).indicator (fun _ => (1 : ℝ)) q :=
        mul_nonneg (by linarith) (Finset.sum_nonneg fun y _ =>
          Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      calc (∑ s, ‖dt s‖ * ‖lab s q.1‖) * (2 * Umax * ∑ y, (T y).indicator (fun _ => 1) q)
          ≤ Amax * (2 * Umax * ∑ y, (T y).indicator (fun _ => 1) q) :=
            mul_le_mul_of_nonneg_right hsum h0
        _ = 2 * Umax * Amax * ∑ y, (T y).indicator (fun _ => 1) q := by ring
    · -- the good pairs
      by_cases hq : q.1 ∈ Gd
      · simp only [Set.indicator_of_mem hq]
        have hB := hBndH q.1 hq
        have e : ∀ s, ‖dt s‖ * ‖lab s q.1‖ * ((K * 1 + K * Zf q.1) * J q.1 (σ s u)) =
            K * (1 + Zf q.1) * (‖g.coeff.eval (msc z)‖ * (g.comps.map fun c =>
              ‖Comp.val (gData S z Sig (green (hmat q.1) z)) (σ s) c‖).prod * J q.1 (σ s u)) := by
          intro s; rw [hnorm]; ring
        change ∑ s, ‖dt s‖ * ‖lab s q.1‖ * ((K * 1 + K * Zf q.1) * J q.1 (σ s u)) ≤
          K * (1 + Zf q.1) * Bnd
        rw [Finset.sum_congr rfl fun s _ => e s, ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hB (mul_nonneg hK0 (by linarith [hZ0 q.1]))
      · simp only [Set.indicator_of_notMem hq, mul_zero, Finset.sum_const_zero]
        exact mul_nonneg (mul_nonneg hK0 (by linarith [hZ0 q.1])) hBnd
  have hGi : ∀ s, Integrable (fun q => ‖dt s‖ * F s q) (μ.prod μ) := by
    intro s
    refine Integrable.mono' hDomi ((hFm s).const_mul _).aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hF0 s q))]
    refine le_trans ?_ (hsumF q)
    exact Finset.single_le_sum (f := fun s' => ‖dt s'‖ * F s' q)
      (fun s' _ => mul_nonneg (norm_nonneg _) (hF0 s' q)) (Finset.mem_univ s)
  -- one labelling
  have hone : ∀ s, ‖dt s‖ * ‖∫ ω, (U ω : ℂ) * (lab s ω - Pexp S (σ s u) (lab s) ω) ∂μ‖ ≤
      ∫ q, ‖dt s‖ * F s q ∂(μ.prod μ) := by
    intro s
    rw [QTerm_swap S hS hS0 (σ s u) _ _ hUP (hlabP s), integral_prod _ (hGi s)]
    have hpt : ∀ ω, ‖dt s‖ * ‖((U ω : ℂ) - Pexp S (σ s u) (fun ω => (U ω : ℂ)) ω) * lab s ω‖ ≤
        ∫ η, ‖dt s‖ * F s (ω, η) ∂μ := by
      intro ω
      have hint : Integrable (fun η => (U (resampleRow (σ s u) η ω) : ℂ)) μ := by
        refine Integrable.mono' (integrable_const Umax) ?_ (Eventually.of_forall fun η => ?_)
        · exact (Complex.measurable_ofReal.comp (hUm.comp ((CutMoment_meas_res (σ s u)).comp
            (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU0 _)]; exact hU1 _
      have e : (U ω : ℂ) - Pexp S (σ s u) (fun ω => (U ω : ℂ)) ω =
          ∫ η, ((U ω : ℂ) - U (resampleRow (σ s u) η ω)) ∂μ := by
        rw [integral_sub (integrable_const _) hint, integral_const, probReal_univ, one_smul]
        rfl
      rw [e, norm_mul]
      have h1 : ‖∫ η, ((U ω : ℂ) - U (resampleRow (σ s u) η ω)) ∂μ‖ ≤
          ∫ η, |U ω - U (resampleRow (σ s u) η ω)| ∂μ := by
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        refine integral_congr_ae (Eventually.of_forall fun η => ?_)
        simp only
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      calc ‖dt s‖ * (‖∫ η, ((U ω : ℂ) - U (resampleRow (σ s u) η ω)) ∂μ‖ * ‖lab s ω‖)
          ≤ ‖dt s‖ * ((∫ η, |U ω - U (resampleRow (σ s u) η ω)| ∂μ) * ‖lab s ω‖) := by gcongr
        _ = ∫ η, ‖dt s‖ * F s (ω, η) ∂μ := by
            rw [← integral_mul_const, ← integral_const_mul]
            refine integral_congr_ae (Eventually.of_forall fun η => ?_)
            simp only [hF]; ring
    calc ‖dt s‖ * ‖∫ ω, ((U ω : ℂ) - Pexp S (σ s u) (fun ω => (U ω : ℂ)) ω) * lab s ω ∂μ‖
        ≤ ‖dt s‖ * ∫ ω, ‖((U ω : ℂ) - Pexp S (σ s u) (fun ω => (U ω : ℂ)) ω) * lab s ω‖ ∂μ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
      _ = ∫ ω, ‖dt s‖ * ‖((U ω : ℂ) - Pexp S (σ s u) (fun ω => (U ω : ℂ)) ω) * lab s ω‖ ∂μ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ ω, ∫ η, ‖dt s‖ * F s (ω, η) ∂μ ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity)
            (hGi s).integral_prod_left (Eventually.of_forall hpt)
  -- the sum over the labellings
  have hsplit : ∫ ω, (U ω : ℂ) * g.valR ⟨Pexp S⟩ D ![a, t, t] ω ∂μ =
      ∑ s, dt s * ∫ ω, (U ω : ℂ) * (lab s ω - Pexp S (σ s u) (lab s) ω) ∂μ := by
    simp_rw [hval, Finset.mul_sum]
    have hint : ∀ s, Integrable (fun ω => (U ω : ℂ) * (dt s * (lab s ω -
        Pexp S (σ s u) (lab s) ω))) μ := by
      intro s
      refine integrable_of_polyMeas S _ (hL.adm_mul _ _ hUP (hL.adm_mul _ _ (hL.adm_const _) ?_))
      have := hL.adm_add _ _ (hlabP s) (hL.adm_mul _ _ (hL.adm_const (-1))
        (hL.adm_P (σ s u) _ (hlabP s)))
      refine (congrArg PolyMeas ?_).mp this
      funext ω; simp only [Pi.add_apply, Pi.mul_apply]; ring
    rw [integral_finsetSum _ fun s _ => hint s]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
  rw [hsplit]
  calc ‖∑ s, dt s * ∫ ω, (U ω : ℂ) * (lab s ω - Pexp S (σ s u) (lab s) ω) ∂μ‖
      ≤ ∑ s, ‖dt s‖ * ‖∫ ω, (U ω : ℂ) * (lab s ω - Pexp S (σ s u) (lab s) ω) ∂μ‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun s _ => norm_mul _ _
    _ ≤ ∑ s, ∫ q, ‖dt s‖ * F s q ∂(μ.prod μ) := Finset.sum_le_sum fun s _ => hone s
    _ = ∫ q, ∑ s, ‖dt s‖ * F s q ∂(μ.prod μ) := (integral_finsetSum _ fun s _ => hGi s).symm
    _ ≤ ∫ q, Dom q ∂(μ.prod μ) :=
        integral_mono (integrable_finsetSum _ fun s _ => hGi s) hDomi hsumF
    _ = _ := by
        have hi1 : Integrable (fun q : Sample (Zd d L) × Sample (Zd d L) =>
            K * (1 + Zf q.1) * Bnd) (μ.prod μ) :=
          ((((integrable_const 1).add hZi).comp_fst μ).const_mul K).mul_const Bnd
        have hi2 : ∀ y, Integrable (fun q : Sample (Zd d L) × Sample (Zd d L) =>
            (T y).indicator (fun _ => (1 : ℝ)) q) (μ.prod μ) := fun y =>
          (integrable_const (1 : ℝ)).indicator (hTm y)
        rw [hDom, integral_add ((integrable_finsetSum _ fun y _ => hi2 y).const_mul _) hi1,
          integral_const_mul, integral_finsetSum _ fun y _ => hi2 y, integral_mul_const,
          integral_const_mul]
        have e1 : ∫ q : Sample (Zd d L) × Sample (Zd d L), (1 + Zf q.1) ∂(μ.prod μ) =
            ∫ ω, (1 + Zf ω) ∂μ := by
          rw [integral_fun_fst (f := fun ω => 1 + Zf ω), probReal_univ, one_smul]
        have e2 : ∀ y, ∫ q, (T y).indicator (fun _ => (1 : ℝ)) q ∂(μ.prod μ) =
            (μ.prod μ).real (T y) := fun y => by
          rw [integral_indicator (hTm y), setIntegral_const, smul_eq_mul, mul_one]
        simp only [e1, e2]
        ring

end QGraph

/-! ## The graphs of `Err`: the label removal on the cutoff event -/

section ErrGraph

variable {d L : ℕ} [NeZero L]

/-- The single matrix of the label removal on the cutoff event:
`G̃_{xy} = W^β B_{xy}^{1/2}` for `x ≠ y` and `G̃_{xx} = m (1 + W^β B_{xx}^{1/2} / |m|)`. -/
private def CutMoment_Gt (W : ℕ) (m : ℂ) (β : ℝ) : Matrix (Zd d L) (Zd d L) ℂ := fun x y =>
  if x = y then m + (m / (‖m‖ : ℂ)) * (((W : ℝ) ^ β * Real.sqrt (bB d L W x x) : ℝ) : ℂ)
  else (((W : ℝ) ^ β * Real.sqrt (bB d L W x y) : ℝ) : ℂ)

omit [NeZero L] in
/-- The entries of `G̃`: `|G̃_{xx} − m| = W^β B_{xx}^{1/2}`, `|G̃_{xx}| = |m| + W^β B_{xx}^{1/2}`,
`|G̃_{xy}| = W^β B_{xy}^{1/2}` for `x ≠ y`, and `|G̃_{xy} − δ_{xy} m| = W^β B_{xy}^{1/2}`. -/
private lemma CutMoment_Gt_facts (W : ℕ) (m : ℂ) (hm : m ≠ 0) (β : ℝ) (x y : Zd d L) :
    ‖CutMoment_Gt W m β x x - m‖ = (W : ℝ) ^ β * Real.sqrt (bB d L W x x) ∧
      ‖CutMoment_Gt W m β x x‖ = ‖m‖ + (W : ℝ) ^ β * Real.sqrt (bB d L W x x) ∧
      (x ≠ y → ‖CutMoment_Gt W m β x y‖ = (W : ℝ) ^ β * Real.sqrt (bB d L W x y)) ∧
      ‖entryErr (CutMoment_Gt W m β) m x y‖ = (W : ℝ) ^ β * Real.sqrt (bB d L W x y) := by
  have hm0 : 0 < ‖m‖ := norm_pos_iff.2 hm
  have hr : ∀ x y : Zd d L, 0 ≤ (W : ℝ) ^ β * Real.sqrt (bB d L W x y) := fun x y => by
    have : (0 : ℝ) ≤ (W : ℝ) ^ β := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hu : ‖m / (‖m‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0, div_self hm0.ne']
  have hxx : CutMoment_Gt W m β x x =
      m + (m / (‖m‖ : ℂ)) * (((W : ℝ) ^ β * Real.sqrt (bB d L W x x) : ℝ) : ℂ) := by
    simp [CutMoment_Gt]
  have h1 : ‖CutMoment_Gt W m β x x - m‖ = (W : ℝ) ^ β * Real.sqrt (bB d L W x x) := by
    rw [hxx, add_sub_cancel_left, norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hr x x)]
  refine ⟨h1, ?_, fun h => ?_, ?_⟩
  · have e : CutMoment_Gt W m β x x =
        m * (((1 + (W : ℝ) ^ β * Real.sqrt (bB d L W x x) / ‖m‖ : ℝ)) : ℂ) := by
      rw [hxx]
      push_cast
      field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := hr x x; positivity)]
    field_simp
  · have e : CutMoment_Gt W m β x y = (((W : ℝ) ^ β * Real.sqrt (bB d L W x y) : ℝ) : ℂ) := by
      simp [CutMoment_Gt, h]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr x y)]
  · by_cases h : x = y
    · subst h
      have e : entryErr (CutMoment_Gt W m β) m x x = CutMoment_Gt W m β x x - m := by
        simp [entryErr]
      rw [e]; exact h1
    · have e : entryErr (CutMoment_Gt W m β) m x y =
          (((W : ℝ) ^ β * Real.sqrt (bB d L W x y) : ℝ) : ℂ) := by
        simp [entryErr, CutMoment_Gt, h]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr x y)]

omit [NeZero L] in
/-- A matrix with `|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}` is dominated by `G̃`. -/
private lemma CutMoment_dom (W : ℕ) (m : ℂ) (hm : m ≠ 0) (β : ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (hG : ∀ x y, ‖entryErr G m x y‖ ≤ (W : ℝ) ^ β * Real.sqrt (bB d L W x y)) :
    (∀ x y, ‖G x y‖ ≤ ‖CutMoment_Gt W m β x y‖) ∧
      (∀ x, ‖G x x - m‖ ≤ ‖CutMoment_Gt W m β x x - m‖) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · by_cases h : x = y
    · subst h
      rw [(CutMoment_Gt_facts W m hm β x x).2.1]
      have e : G x x = entryErr G m x x + m := by simp [entryErr]
      rw [e]
      refine (norm_add_le _ _).trans ?_
      linarith [hG x x]
    · rw [(CutMoment_Gt_facts W m hm β x y).2.2.1 h]
      have := hG x y
      simpa [entryErr, h] using this
  · rw [(CutMoment_Gt_facts W m hm β x x).1]
    have := hG x x
    simpa [entryErr] using this

/-- **The label removal at one sample on the cutoff event**: if `|G(ω) − m| ≤ W^β B^{1/2}`
entrywise, every resampled resolvent `G(ω^{[y,η]})`, `η` outside a measurable set `T`, has the
same bound, `W^β W^{−d/2} ≤ 1/8`, `Im z ≥ W^{−a}`, `lo ≤ W^β B^{1/2}` entrywise and
`M_{4R'}(ω, y)^{1/2} P(T)^{1/2} ≤ (lo/M_b)^{R'}`, then the value of a graph `Γ` of `Err` at the
sample `ω` is at most `3^{#labels} C_Γ Σ_S |(Γ'_S)^{abs}_{𝔞,𝔟𝔟}(G̃)|` (`LabelRemoval_valR_le`). -/
private lemma CutMoment_errPt (P : Profile d) (Sig : ℕ → Expansion 2) {nI : ℕ}
    (Γ : Graph 3 nI) (N : ℕ) (hΓ : Γ.TKindsErr N) (W : ℕ) (z : ℂ) (hzim : 0 < z.im)
    (hz3 : ‖z‖ ≤ 3) (a : ℝ) (hW1 : 1 ≤ (W : ℝ)) (hima : (W : ℝ) ^ (-a) ≤ z.im) (β : ℝ)
    (h8 : ∀ x : Zd d L, (W : ℝ) ^ β * Real.sqrt (bB d L W x x) ≤ 1 / 8) (lo : ℝ)
    (hlo0 : 0 ≤ lo) (hlo1 : lo ≤ 1)
    (hloB : ∀ x y : Zd d L, lo ≤ (W : ℝ) ^ β * Real.sqrt (bB d L W x y))
    (ω : Sample (Zd d L))
    (hY : ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤
      (W : ℝ) ^ β * Real.sqrt (bB d L W x y))
    (T : Set (Sample (Zd d L))) (hTm : MeasurableSet T)
    (hgood : ∀ y η, η ∉ T → ∀ x x', ‖entryErr (green (hmat (resampleRow y η ω)) z) (msc z) x x'‖ ≤
      (W : ℝ) ^ β * Real.sqrt (bB d L W x x'))
    (hS1 : ∀ c, coordVar (Smat P.ψ W L) c ≤ 1)
    (hP : ∀ y, Real.sqrt (LabelRemoval.momBound (2 * (2 * Γ.wDLights.comps.length)) ω y) *
      Real.sqrt (gaussLaw (Smat P.ψ W L) T).toReal ≤
        (lo / LabelRemoval_Mb Γ.wDLights.comps.length d L W a) ^ Γ.wDLights.comps.length)
    (a₀ b₀ : Zd d L) :
    ‖Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a₀, b₀, b₀] ω‖ ≤
      3 ^ Γ.labels.length * (G11.wDConst Γ * ∑ S ∈ Γ.wDLights.pathElig.powerset,
        (Γ.wDLights.pathRepl S).absVal
          (gData (Smat P.ψ W L) z Sig (CutMoment_Gt W (msc z) β)) ![a₀, b₀, b₀]) := by
  set Sm := Smat P.ψ W L with hSm
  have hW0 : (0 : ℝ) < W := by linarith
  have hm4 : 1 / 4 ≤ ‖msc z‖ := norm_msc_ge_quarter z hzim hz3
  have hm1 : ‖msc z‖ ≤ 1 := (norm_msc_lt_one hzim).le
  have hm0 : msc z ≠ 0 := msc_ne_zero z
  set Gt : Matrix (Zd d L) (Zd d L) ℂ := CutMoment_Gt W (msc z) β with hGt
  have hd8 : ∀ (G : Matrix (Zd d L) (Zd d L) ℂ), (∀ x y, ‖entryErr G (msc z) x y‖ ≤
      (W : ℝ) ^ β * Real.sqrt (bB d L W x y)) → ∀ x, ‖G x x - msc z‖ ≤ 1 / 8 := by
    intro G hG x
    have := hG x x
    simp only [entryErr, ↓reduceIte] at this
    linarith [h8 x]
  -- the bounds off the event
  set M := LabelRemoval_Mres d L W a with hM
  have hLd : (1 : ℝ) ≤ ((L : ℝ) ^ d) ^ 2 := one_le_pow₀ (one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)))
  have hWa : 0 ≤ (W : ℝ) ^ a := Real.rpow_nonneg hW0.le _
  have hM1 : 1 ≤ M := by rw [hM, LabelRemoval_Mres]; nlinarith
  have hima' : z.im⁻¹ ≤ (W : ℝ) ^ a := by
    rw [inv_le_comm₀ hzim (by positivity), ← Real.rpow_neg hW0.le]; exact hima
  have hall : ∀ (ω' : Sample (Zd d L)) (x y : Zd d L), ‖green (hmat ω') z x y‖ ≤ M - 1 := by
    intro ω' x y
    have h1 := norm_green_entry_le (hmat_isHermitian ω') hzim.ne' x y
    rw [abs_of_pos hzim] at h1
    rw [hM, LabelRemoval_Mres]
    nlinarith
  have hinv : ∀ (ω' : Sample (Zd d L)) (x : Zd d L),
      ‖(green (hmat ω') z x x)⁻¹‖ ≤ M * (1 + ‖ω'‖) ^ 2 := by
    intro ω' x
    refine (LabelRemoval_inv_diag_le hzim ω' x).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [card_Zd, hM, LabelRemoval_Mres]
    push_cast
    have : ((L : ℝ) ^ d) ^ 2 * (4 * z.im⁻¹) ≤ ((L : ℝ) ^ d) ^ 2 * (4 * (W : ℝ) ^ a) := by gcongr
    nlinarith
  set R' := Γ.wDLights.comps.length with hR'
  set Mb := LabelRemoval_Mb R' d L W a with hMb
  have hMbM : 8 * ((R' : ℝ) + 1) * 4 ^ R' * M = Mb := rfl
  have hMMb : M ≤ Mb := by
    rw [← hMbM]
    have : (1 : ℝ) ≤ 8 * ((R' : ℝ) + 1) * 4 ^ R' := by
      have := one_le_pow₀ (n := R') (by norm_num : (1 : ℝ) ≤ 4); nlinarith
    exact le_mul_of_one_le_left (by linarith) this
  have hbad : ∀ (σ : Atom 3 nI → Zd d L) (ω' : Sample (Zd d L)) (c : Comp (Atom 3 nI)),
      c ∈ Γ.comps → c.kind.isRandom = true →
      ‖Comp.val (gData Sm z Sig (green (hmat ω') z)) σ c‖ ≤
        Mb ^ (c.kind.wDDeg + 1) * (1 + ‖ω'‖) ^ 2 := by
    intro σ ω' c hc hr
    refine LabelRemoval_val_bad Sm z Sig _ M Mb _ hM1 (one_le_pow₀ (by
      linarith [norm_nonneg ω'])) (hall ω') (hinv ω') hm1 hm4 σ N c
      (LabelRemoval_errKind hΓ hc) hr hMMb fun _ => ?_
    rw [← hMbM]
    refine LabelRemoval_Mb_pow M hM1 R' _ ?_
    rw [hR', G11.wDLights_length]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun c => c.kind.wDDeg) hc)
    omega
  obtain ⟨hG1, hG2⟩ := CutMoment_dom W (msc z) hm0 β _ hY
  have hlo : ∀ x y, lo ≤ ‖Gt x y‖ := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [(CutMoment_Gt_facts W (msc z) hm0 β x x).2.1]
      linarith [hloB x x, norm_nonneg (msc z)]
    · rw [(CutMoment_Gt_facts W (msc z) hm0 β x y).2.2.1 hxy]; exact hloB x y
  have hlo2 : ∀ x, lo ≤ ‖Gt x x - msc z‖ := by
    intro x; rw [(CutMoment_Gt_facts W (msc z) hm0 β x x).1]; exact hloB x x
  have hMb0 : 0 < Mb := by linarith
  have hloM : lo ≤ Mb := by linarith
  refine LabelRemoval_valR_le Γ P Sig W L z N hΓ Gt ω T hTm Mb lo hlo0 hloM hMb0
    hbad hm1 hm4 hlo hlo2 hG1 hG2 (hd8 _ hY) a₀ b₀ (fun y η hη => ⟨?_, hd8 _ (hgood y η hη)⟩)
    hS1 hP
  obtain ⟨d1, d2⟩ := CutMoment_dom W (msc z) hm0 β _ (hgood y η hη)
  refine ⟨fun a' => d1 a' a', d2, fun b hb => d1 y b, fun a' ha => d1 a' y, fun a' b' _ _ _ => ?_,
    fun _ a' b' _ _ _ => d1 a' b'⟩
  exact (d1 a' b').trans (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

end ErrGraph

/-- **A priori bound of a graph of `Err`**: eventually along the filter,
`|𝒢_{𝔞,𝔟𝔟}(ω)| ≤ W^K (1 + ‖ω‖)^q` at every `z ∈ 𝐃(κ, ε)`, `𝔞`, `𝔟` and sample `ω`. -/
private lemma CutMoment_apriori (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ)
    (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig N) {n : ℕ} (g : Graph 3 n)
    (hK : g.TKindsErr N) :
    ∃ (K : ℝ) (q : ℕ), 0 ≤ K ∧ ∀ᶠ p in llFilter d N c₀ c₁ c₀T,
      ∀ (u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2}) (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
        ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 u.1) ![a, b, b] ω‖ ≤
          (p.1.1 : ℝ) ^ K * (1 + ‖ω‖) ^ q := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := Lem512Zero_comp_le d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE g hK
  set c := g.comps.length with hcdef
  set Cst : ℝ := 2 ^ (2 * c) * (1 + LabelRemoval.gaussMoment (2 * c)) with hCst
  have hg : 0 ≤ LabelRemoval.gaussMoment (2 * c) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hCst0 : 0 ≤ Cst := by positivity
  set K₁ : ℝ := max 4 (4 / Real.sqrt (2 * κ)) with hK₁
  set Cg : ℝ := ∑ s ∈ g.coeff.support, ‖g.coeff.coeff s‖ * ∏ i ∈ s.support, K₁ ^ s i with hCg
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  set E₁ : ℝ := K₀ * c + 2 + 2 * d / c₁ with hE₁
  refine ⟨n * ((d : ℝ) / c₁) + (1 + K₀ * c + E₁ * c), 2 * c * (c + 1), by positivity, ?_⟩
  filter_upwards [hK₀, Moment_ev_adm d N c₀ c₁ c₀T, (Moment_tendsto d N c₀ c₁ c₀T).eventually
    (eventually_ge_atTop (max 4 (max W₂ (max Cg (3 * Cst + 1)))))] with p hcomp hp hW u a b ω
  change max 4 (max W₂ (max Cg (3 * Cst + 1))) ≤ (p.1.1 : ℝ) at hW
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW4 : 4 ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hW₂ : W₂ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hCgW : Cg ≤ W :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
  have hCstW : 3 * Cst + 1 ≤ W :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
  have hS1 : ∀ c', coordVar (Smat P.ψ p.1.1 p.1.2) c' ≤ 1 :=
    LabelRemoval_coordVar_le _ (hds p.1.1 p.1.2 hp hW₂)
  obtain ⟨him, -⟩ := Moment_im_inv (c₀ := c₀) hc₁ hε p hp hW1 u.1 u.2
  have hA1 : 1 ≤ W ^ K₀ := Real.one_le_rpow hW1 hK₀0
  have h := Lem512Zero_valR_le g (Smat P.ψ p.1.1 p.1.2) hS1
    (rbmData d P Sig p.1.1 p.1.2 u.1) (W ^ K₀) hA1 (fun _ => rfl)
    (fun ω' σ c' hc' => hcomp u ω' σ c' hc') ![a, b, b] ω
  refine h.trans ?_
  have hcoef : ‖g.coeff.eval (rbmData d P Sig p.1.1 p.1.2 u.1 0).m‖ ≤ W :=
    (Moment_coeff_le g.coeff _ K₁ fun i => Moment_cvar_le hκ u.1 u.2 him i).trans hCgW
  have hcardC : (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ 3 * W ^ (2 * (d : ℝ) / c₁) := by
    refine LabelRemoval_card_coord.trans ?_
    have : (Fintype.card (Zd d p.1.2) : ℝ) ≤ W ^ ((d : ℝ) / c₁) := card_Zd_le_adm d c₀ c₁ hc₁ p hp
    have h2 : (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ W ^ (2 * (d : ℝ) / c₁) := by
      calc (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ (W ^ ((d : ℝ) / c₁)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
        _ = W ^ (2 * (d : ℝ) / c₁) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    linarith
  have hX1 : 1 ≤ W ^ (2 * (d : ℝ) / c₁) := Real.one_le_rpow hW1 (by positivity)
  have hB : 1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ W ^ (1 + 2 * (d : ℝ) / c₁) := by
    rw [Real.rpow_add hW0, Real.rpow_one]
    have e1 : Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ 3 * Cst * W ^ (2 * (d : ℝ) / c₁) := by
      nlinarith
    nlinarith
  have hAc : (W ^ K₀) ^ c = W ^ (K₀ * c) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have hY : 2 * (W ^ K₀) ^ c * (1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ)) ≤ W ^ E₁ := by
    rw [hAc, hE₁]
    have e2 : W ^ (K₀ * c + 2 + 2 * d / c₁) = W ^ (K₀ * c) * W * W ^ (1 + 2 * (d : ℝ) / c₁) := by
      rw [(show K₀ * c + 2 + 2 * d / c₁ = K₀ * c + 1 + (1 + 2 * d / c₁) by ring),
        Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
    rw [e2]
    have : 0 ≤ W ^ (K₀ * c) := Real.rpow_nonneg hW0.le _
    have h2W : 2 * W ^ (K₀ * c) ≤ W ^ (K₀ * c) * W := by nlinarith
    exact mul_le_mul h2W hB (by positivity) (by positivity)
  have hYc : (2 * (W ^ K₀) ^ c * (1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ))) ^ c ≤
      W ^ (E₁ * c) :=
    (pow_le_pow_left₀ (by positivity) hY c).trans
      (le_of_eq (by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]))
  have hcardn : (Fintype.card (Zd d p.1.2) : ℝ) ^ n ≤ W ^ (n * ((d : ℝ) / c₁)) := by
    have h0 : (Fintype.card (Zd d p.1.2) : ℝ) ≤ W ^ ((d : ℝ) / c₁) :=
      card_Zd_le_adm d c₀ c₁ hc₁ p hp
    calc (Fintype.card (Zd d p.1.2) : ℝ) ^ n ≤ (W ^ ((d : ℝ) / c₁)) ^ n :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h0 n
      _ = W ^ (n * ((d : ℝ) / c₁)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  have hR1 : (0 : ℝ) ≤ (1 + ‖ω‖) ^ (2 * c * (c + 1)) := by positivity
  rw [Real.rpow_add hW0]
  refine mul_le_mul_of_nonneg_right ?_ hR1
  refine mul_le_mul hcardn ?_ (by positivity) (by positivity)
  rw [← hCst]
  calc ‖g.coeff.eval (rbmData d P Sig p.1.1 p.1.2 u.1 0).m‖ * (W ^ K₀) ^ c *
        (2 * (W ^ K₀) ^ c * (1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ))) ^ c
      ≤ W * W ^ (K₀ * c) * W ^ (E₁ * c) := by
        rw [hAc] at hYc ⊢
        gcongr
  _ = W ^ (1 + K₀ * c + E₁ * c) := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]


/-! ## The averaging over `t` -/

/-- `s_{xy} ≤ C ⟨x − y⟩^{−d}` on `adm(c₀, c₁)` ([I, Assumption 1.1]). -/
private lemma CutMoment_S_le (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → 1 ≤ W → ∀ x y : Zd d L,
      Smat P.ψ W L x y ≤ C * brk d L W x y ^ (-(d : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨C₁, hC₁⟩ := subpoly_adm d P c₀ c₁ hc₀ d
  refine ⟨2 ^ d * (|C₀| + |C₁|), by positivity, fun W L _ hadm hW x y => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h0 := hC₀ W L hadm (x - y)
  have h1 := hC₁ W L hadm (x - y)
  rw [pow_zero, one_mul] at h0
  set r : ℝ := (zdistInf d L (x - y) : ℝ) with hr
  set f : ℝ := |fWL P.ψ W L (x - y)| with hf
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hb : brk d L W x y = r + W := rfl
  have hb0 : 0 < r + W := by linarith
  have hWd : (W : ℝ) ^ d * f ≤ |C₀| := by
    have := (le_div_iff₀ (by positivity)).1 h0
    calc (W : ℝ) ^ d * f = f * (W : ℝ) ^ d := by ring
      _ ≤ C₀ := this
      _ ≤ |C₀| := le_abs_self _
  have hrd : r ^ d * f ≤ |C₁| := by
    have e : (r / W) ^ d * f = r ^ d * f / (W : ℝ) ^ d := by rw [div_pow]; ring
    rw [e] at h1
    have := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (W : ℝ) ^ d)).1 h1
    exact this.trans (le_abs_self _)
  have hsum : (r + W) ^ d * f ≤ 2 ^ d * (|C₀| + |C₁|) := by
    have hpow : (r + W) ^ d ≤ 2 ^ d * (r ^ d + (W : ℝ) ^ d) := by
      rcases le_total r W with h | h
      · calc (r + W) ^ d ≤ (2 * W) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
          _ = 2 ^ d * (W : ℝ) ^ d := mul_pow _ _ _
          _ ≤ 2 ^ d * (r ^ d + (W : ℝ) ^ d) := by gcongr; linarith [pow_nonneg hr0 d]
      · calc (r + W) ^ d ≤ (2 * r) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
          _ = 2 ^ d * r ^ d := mul_pow _ _ _
          _ ≤ 2 ^ d * (r ^ d + (W : ℝ) ^ d) := by gcongr; linarith [pow_nonneg hW0.le d]
    calc (r + W) ^ d * f ≤ 2 ^ d * (r ^ d + (W : ℝ) ^ d) * f :=
          mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ = 2 ^ d * (r ^ d * f + (W : ℝ) ^ d * f) := by ring
      _ ≤ 2 ^ d * (|C₀| + |C₁|) :=
          mul_le_mul_of_nonneg_left (by linarith [hrd, hWd]) (by positivity)
  have hS : Smat P.ψ W L x y ≤ f := le_abs_self _
  rw [hb, Real.rpow_neg hb0.le, Real.rpow_natCast]
  calc Smat P.ψ W L x y ≤ f := hS
    _ = (r + W) ^ d * f / (r + W) ^ d := by field_simp
    _ ≤ 2 ^ d * (|C₀| + |C₁|) / (r + W) ^ d := by gcongr
    _ = 2 ^ d * (|C₀| + |C₁|) * ((r + W) ^ d)⁻¹ := by ring

/-- **The average of `B_{𝔞t}` against `s_{t𝔟}`**: `Σ_t B_{𝔞t} s_{t𝔟} ≤ C (⟨𝔞 − 𝔟⟩/W)^δ B_{𝔞𝔟}`. -/
private lemma CutMoment_SB (d : ℕ) (hd : 3 ≤ d) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → 1 ≤ W → ∀ a b : Zd d L,
      ∑ t, bB d L W a t * Smat P.ψ W L t b ≤
        C * (brk d L W a b / W) ^ δ * bB d L W a b := by
  obtain ⟨Cs, hCs0, hCs⟩ := CutMoment_S_le d P c₀ c₁ hc₀
  obtain ⟨Cc, hCc0, hCc⟩ := Chain_conv d hd δ hδ
  refine ⟨Cs * Cc, by positivity, fun W L _ hadm hW a b => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWm : (0 : ℝ) ≤ (W : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg hW0.le _
  calc ∑ t, bB d L W a t * Smat P.ψ W L t b
      ≤ ∑ t, (W : ℝ) ^ (-2 : ℝ) * (Cs * (brk d L W b t ^ (-(d : ℝ)) *
          brk d L W t a ^ (-((d : ℝ) - 2)))) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [Chain_bB_eq, Chain_brk_comm d L W a t]
        have hb : (0 : ℝ) ≤ brk d L W t a ^ (2 - (d : ℝ)) := by unfold brk; positivity
        have e : brk d L W t a ^ (2 - (d : ℝ)) = brk d L W t a ^ (-((d : ℝ) - 2)) := by ring_nf
        calc (W : ℝ) ^ (-2 : ℝ) * brk d L W t a ^ (2 - (d : ℝ)) * Smat P.ψ W L t b
            ≤ (W : ℝ) ^ (-2 : ℝ) * brk d L W t a ^ (2 - (d : ℝ)) *
                (Cs * brk d L W b t ^ (-(d : ℝ))) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hWm hb)
              rw [Chain_brk_comm d L W b t]; exact hCs W L hadm hW t b
          _ = _ := by rw [e]; ring
    _ = (W : ℝ) ^ (-2 : ℝ) * Cs * ∑ t, brk d L W b t ^ (-(d : ℝ)) *
          brk d L W t a ^ (-((d : ℝ) - 2)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
    _ ≤ (W : ℝ) ^ (-2 : ℝ) * Cs * (Cc * (brk d L W b a / W) ^ δ *
          brk d L W b a ^ (-((d : ℝ) - 2))) := by
        gcongr; exact hCc L W hW b a
    _ = Cs * Cc * (brk d L W a b / W) ^ δ * bB d L W a b := by
        rw [Chain_bB_eq, Chain_brk_comm d L W b a]
        have e : brk d L W a b ^ (2 - (d : ℝ)) = brk d L W a b ^ (-((d : ℝ) - 2)) := by ring_nf
        rw [e]; ring

/-- A priori bound, polynomial in `W` and in `‖ω‖`, of the value of a formal sum of graphs with
the kinds of `Err`. -/
private lemma CutMoment_apriori_list (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ)
    (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig N) (E : Expansion 3)
    (hE : ∀ g ∈ E, g.2.TKindsErr N) :
    ∃ (K : ℝ) (r : ℕ), 0 ≤ K ∧ ∀ᶠ p in llFilter d N c₀ c₁ c₀T,
      ∀ (u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2}) (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
        ‖E.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 u.1) ![a, b, b] ω‖ ≤
          (p.1.1 : ℝ) ^ K * (1 + ‖ω‖) ^ r := by
  induction E with
  | nil => exact ⟨0, 0, le_rfl, Eventually.of_forall fun p u a b ω => by simp [Expansion.valR]⟩
  | cons g E ih =>
    obtain ⟨K₁, r₁, hK₁0, h₁⟩ := ih fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')
    obtain ⟨K₂, r₂, hK₂0, h₂⟩ := CutMoment_apriori d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE
      g.2 (hE g (List.mem_cons_self ..))
    refine ⟨max K₁ K₂ + 1, max r₁ r₂, by positivity, ?_⟩
    filter_upwards [h₁, h₂, (Moment_tendsto d N c₀ c₁ c₀T).eventually
      (eventually_ge_atTop 2)] with p hp₁ hp₂ hW u a b ω
    change (2 : ℝ) ≤ p.1.1 at hW
    have hW1 : (1 : ℝ) ≤ p.1.1 := by linarith
    have hW0 : (0 : ℝ) < p.1.1 := by linarith
    have hω : 1 ≤ 1 + ‖ω‖ := by linarith [norm_nonneg ω]
    have hval : Expansion.valR (g :: E) ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩
        (rbmData d P Sig p.1.1 p.1.2 u.1) ![a, b, b] ω =
        g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 u.1) ![a, b, b] ω +
          Expansion.valR E ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 u.1)
            ![a, b, b] ω := by
      simp [Expansion.valR]
    rw [hval]
    refine (norm_add_le _ _).trans ?_
    have e1 : (p.1.1 : ℝ) ^ K₂ * (1 + ‖ω‖) ^ r₂ ≤
        (p.1.1 : ℝ) ^ (max K₁ K₂) * (1 + ‖ω‖) ^ (max r₁ r₂) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hW1 (le_max_right _ _))
        (pow_le_pow_right₀ hω (le_max_right _ _)) (by positivity) (by positivity)
    have e2 : (p.1.1 : ℝ) ^ K₁ * (1 + ‖ω‖) ^ r₁ ≤
        (p.1.1 : ℝ) ^ (max K₁ K₂) * (1 + ‖ω‖) ^ (max r₁ r₂) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hW1 (le_max_left _ _))
        (pow_le_pow_right₀ hω (le_max_left _ _)) (by positivity) (by positivity)
    have e3 : (p.1.1 : ℝ) ^ (max K₁ K₂ + 1) = (p.1.1 : ℝ) ^ (max K₁ K₂) * p.1.1 := by
      rw [Real.rpow_add hW0, Real.rpow_one]
    rw [e3]
    have hX : 0 ≤ (p.1.1 : ℝ) ^ (max K₁ K₂) * (1 + ‖ω‖) ^ (max r₁ r₂) := by positivity
    have h2W := mul_le_mul_of_nonneg_left hW hX
    have q1 := hp₁ u a b ω
    have q2 := hp₂ u a b ω
    calc _ ≤ (p.1.1 : ℝ) ^ K₂ * (1 + ‖ω‖) ^ r₂ + (p.1.1 : ℝ) ^ K₁ * (1 + ‖ω‖) ^ r₁ :=
          add_le_add q2 q1
      _ ≤ _ := by nlinarith

/-! ## A priori bound of the absolute-value graphs at `G(ω)` -/

/-- `|𝒢^{abs}| ≤ |ι|^n |coeff| (2M)^c` when the entries read are bounded by `M ≥ 1`. -/
private lemma CutMoment_absVal_le {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} (N : ℕ)
    (Γ : Graph k n) (hΓ : Γ.TKinds N) (D : Data ι) (M : ℝ) (hM1 : 1 ≤ M) (hm : ‖D.m‖ ≤ 1)
    (hG : ∀ x y, ‖D.Gm ∅ x y‖ ≤ M) (hS : ∀ x y, ‖D.S x y‖ ≤ M) (hSp : ∀ x y, ‖D.Sp x y‖ ≤ M)
    (hSm : ∀ x y, ‖D.Sm x y‖ ≤ M)
    (hch : ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ x y, ‖D.chain o x y‖ ≤ M) (e : Fin k → ι) :
    Γ.absVal D e ≤ (Fintype.card ι : ℝ) ^ n * (‖Γ.coeff.eval D.m‖ * (2 * M) ^ Γ.comps.length) := by
  have hTK : ∀ c' ∈ Γ.comps, c'.isTKind N = true := List.all_eq_true.1 hΓ
  unfold Graph.absVal
  have hterm : ∀ s : Fin n → ι, ‖Γ.coeff.eval D.m‖ *
      (Γ.comps.map fun c => ‖Comp.val D (Sum.elim e s) c‖).prod ≤
        ‖Γ.coeff.eval D.m‖ * (2 * M) ^ Γ.comps.length := by
    intro s
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have e1 : (Γ.comps.map fun c => ‖Comp.val D (Sum.elim e s) c‖).prod =
        ‖(Γ.comps.map (Comp.val D (Sum.elim e s))).prod‖ := by
      rw [List.norm_prod, List.map_map]; rfl
    rw [e1]
    exact Moment_prod_le _ _ (2 * M) (by linarith) fun c hc =>
      Moment_compVal_le N D _ c (hTK c hc) M hM1 hm hG hS hSp hSm (hch c hc)
  refine (Finset.sum_le_sum fun s _ => hterm s).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- **A priori bound, polynomial in `W`, of the absolute-value graph at `G(ω)`** for a graph with
the kinds of [II, Def 3.2], eventually along the filter, uniformly in `z ∈ 𝐃(κ, ε)`, `𝔞, 𝔟` and
the sample. -/
private lemma CutMoment_absVal_apriori (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (c₀ c₁ κ ε c₀T : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ)
    (hε : 0 < ε) (n : ℕ) (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig n)
    {nI : ℕ} (g : Graph 3 nI) (hK : g.TKinds n) :
    ∃ K : ℝ, ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
        g.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig (green (hmat ω) z)) ![a, b, b] ≤
          (p.1.1 : ℝ) ^ K := by
  set U : SizeL → Type := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} with hU
  set e : ℝ := 2 / c₁ + 1 with he
  have he0 : 1 ≤ e := by
    have : 0 ≤ 2 / c₁ := by positivity
    linarith
  set c := g.comps.length with hcdef
  set K₀ : ℝ := max 4 (4 / Real.sqrt (2 * κ)) with hK₀
  set Cg : ℝ := ∑ s ∈ g.coeff.support, ‖g.coeff.coeff s‖ * ∏ i ∈ s.support, K₀ ^ s i with hCg
  obtain ⟨KS, hKS⟩ := Moment_ev_Sp d n P c₀ c₁ κ ε c₀T hc₀ hc₁ hκ hε U (fun _ u => u.1)
    (fun _ u => u.2)
  have hch : ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ c' ∈ g.comps, ∀ o, c'.kind = .theta o →
      ∀ (u : U p) (ω : Sample (Zd d p.1.2)) (x y : Zd d p.1.2),
        ‖(rbmData d P Sig p.1.1 p.1.2 u.1 ω).chain o x y‖ ≤ (p.1.1 : ℝ) := by
    refine Moment_ev_list g.comps fun c' hc' => ?_
    by_cases h : ∃ o, c'.kind = .theta o
    · obtain ⟨o, ho⟩ := h
      have hok : labelOK n o = true := by
        have := List.all_eq_true.1 hK c' hc'
        simp only [Comp.isTKind, ho, Bool.and_eq_true] at this
        exact this.2
      filter_upwards [Moment_ev_chain d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε n Sig hSE U
        (fun _ u => u.1) (fun _ u => u.2) o hok] with p hp o' ho'
      rw [ho] at ho'
      cases ho'
      exact hp
    · exact Eventually.of_forall fun p o ho => absurd ⟨o, ho⟩ h
  refine ⟨(d : ℝ) * nI / c₁ + 1 + (e + 1) * c, ?_⟩
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, Moment_ev_Smat d n P c₀ c₁ c₀T hc₀ hc₁, hKS, hch,
    (Moment_tendsto d n c₀ c₁ c₀T).eventually (eventually_ge_atTop (max 2 (max KS Cg)))]
    with p hp hSm hKSp hchp hW z hz a b ω
  change max 2 (max KS Cg) ≤ (p.1.1 : ℝ) at hW
  set u : U p := ⟨z, hz⟩ with hu
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW2 : 2 ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hKSW : KS ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hCgW : Cg ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  obtain ⟨him, himW⟩ := Moment_im_inv (c₀ := c₀) hc₁ hε p hp hW1 z hz
  have hWe : W ≤ W ^ e := by
    calc W = W ^ (1 : ℝ) := (Real.rpow_one W).symm
      _ ≤ W ^ e := Real.rpow_le_rpow_of_exponent_le hW1 he0
  have hM1 : 1 ≤ W ^ e := hW1.trans hWe
  have hbound := CutMoment_absVal_le n g hK (gData (Smat P.ψ p.1.1 p.1.2) z Sig (green (hmat ω) z))
    (W ^ e) hM1 (norm_msc_lt_one him).le
    (fun x y => by
      change ‖green (hmat ω) z x y‖ ≤ W ^ e
      refine (norm_green_entry_le (hmat_isHermitian ω) him.ne' x y).trans ?_
      rw [abs_of_pos him]
      exact himW.trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)))
    (fun x y => by
      change ‖((Smat P.ψ p.1.1 p.1.2 x y : ℝ) : ℂ)‖ ≤ W ^ e
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hSm.2.1 x y)]
      have : Smat P.ψ p.1.1 p.1.2 x y ≤ ∑ y', Smat P.ψ p.1.1 p.1.2 x y' :=
        Finset.single_le_sum (fun y' _ => hSm.2.1 x y') (Finset.mem_univ y)
      rw [hSm.2.2 x] at this
      exact this.trans hM1)
    (fun x y => (hKSp u x y).1.trans (hKSW.trans hWe))
    (fun x y => (hKSp u x y).2.trans (hKSW.trans hWe))
    (fun c' hc' o ho x y => by
      have h := hchp c' hc' o ho u ω x y
      rw [Moment_chain_eq] at h
      exact h.trans hWe) ![a, b, b]
  refine hbound.trans ?_
  have hcard : (Fintype.card (Zd d p.1.2) : ℝ) ^ nI ≤ W ^ ((d : ℝ) * nI / c₁) := by
    have h0 : (Fintype.card (Zd d p.1.2) : ℝ) ≤ W ^ ((d : ℝ) / c₁) :=
      card_Zd_le_adm d c₀ c₁ hc₁ p hp
    calc (Fintype.card (Zd d p.1.2) : ℝ) ^ nI ≤ (W ^ ((d : ℝ) / c₁)) ^ nI :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h0 nI
      _ = W ^ ((d : ℝ) * nI / c₁) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  have hcoef : ‖g.coeff.eval (msc z)‖ ≤ W :=
    (Moment_coeff_le g.coeff _ K₀ fun i => Moment_cvar_le hκ z hz him i).trans hCgW
  have h2M : 2 * W ^ e ≤ W ^ (e + 1) := by
    have h := Real.rpow_add hW0 e 1
    rw [Real.rpow_one] at h
    rw [h]
    have : 0 ≤ W ^ e := Real.rpow_nonneg hW0.le _
    nlinarith
  have hA : (2 * W ^ e) ^ c ≤ W ^ ((e + 1) * c) := by
    calc (2 * W ^ e) ^ c ≤ (W ^ (e + 1)) ^ c := pow_le_pow_left₀ (by positivity) h2M c
      _ = W ^ ((e + 1) * c) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  calc (Fintype.card (Zd d p.1.2) : ℝ) ^ nI *
        (‖g.coeff.eval (gData (Smat P.ψ p.1.1 p.1.2) z Sig (green (hmat ω) z)).m‖ *
          (2 * W ^ e) ^ c)
      ≤ W ^ ((d : ℝ) * nI / c₁) * (W * W ^ ((e + 1) * c)) := by
        gcongr
        exact hcoef
    _ = W ^ ((d : ℝ) * nI / c₁ + 1 + (e + 1) * c) := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]; ring

/-! ## The cutoff event, the identity of `X_{𝔞𝔟}` and the resampled pairs -/

section Assembly

variable {d L : ℕ} [NeZero L]

/-- `Y ≤ W^β` gives `|G_{xy} − δ_{xy} m| ≤ W^β B_{xy}^{1/2}`. -/
private lemma CutMoment_Y_entry (W : ℕ) (hW : 1 ≤ (W : ℝ)) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (m : ℂ) (β : ℝ) (hY : cutY W G m ≤ (W : ℝ) ^ β) (x y : Zd d L) :
    ‖entryErr G m x y‖ ≤ (W : ℝ) ^ β * Real.sqrt (bB d L W x y) := by
  have hB : 0 < Real.sqrt (bB d L W x y) := by
    apply Real.sqrt_pos.2; unfold bB; have : (0 : ℝ) < W := by linarith
    positivity
  have h1 : ‖entryErr G m x y‖ / Real.sqrt (bB d L W x y) ≤ cutY W G m := by
    unfold cutY
    refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) x)
    exact le_ciSup (f := fun j => ‖entryErr G m x j‖ / Real.sqrt (bB d L W x j))
      (Finite.bddAbove_range _) y
  rw [div_le_iff₀ hB] at h1
  linarith [mul_le_mul_of_nonneg_right hY hB.le]

/-- `|m|² B_{𝔞𝔟} X_{𝔞𝔟} = Σ_t T_{𝔞t} s_{t𝔟}` with `T_{𝔞t} = |m|² Σ_x s_{𝔞x} |G_{xt}|²`. -/
private lemma CutMoment_X_eq (W : ℕ) (hW : 1 ≤ (W : ℝ)) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ) (a b : Zd d L) :
    ‖m‖ ^ 2 * bB d L W a b * cutX W S G a b = ∑ t, S t b * Tvar S G m a t := by
  have hB : 0 < bB d L W a b := by unfold bB; have : (0 : ℝ) < W := by linarith
                                   positivity
  unfold cutX cutD Tvar
  rw [mul_assoc, mul_div_cancel₀ _ hB.ne']
  calc ‖m‖ ^ 2 * ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b
      = ∑ i, ∑ j, ‖m‖ ^ 2 * (S a i * ‖G i j‖ ^ 2 * S j b) := by simp_rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, ‖m‖ ^ 2 * (S a i * ‖G i j‖ ^ 2 * S j b) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun t _ => by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **The cutoff weight on a good pair**: off the event of `cutPairStmt` at `(ω, η)` and at the
exchanged pair, `|C Z^k − C' Z'^k| ≤ K W^{4β+α} (1 + Z^k) J*_y` on `{Y(ω) ≤ W^β}` and `0` off it,
with `K = 8l + 32 l k 2^k`. -/
private lemma CutMoment_goodPair (hd : 2 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (l W k : ℕ) (hl : 1 ≤ l)
    (hW : 1 ≤ (W : ℝ)) {S : Matrix (Zd d L) (Zd d L) ℝ} (hS : ∀ x y, 0 ≤ S x y)
    (G G' : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ) (a b y : Zd d L)
    (h1 : 0 < cutC β (β / 10) l W S G m → cutY W G' m ≤ (W : ℝ) ^ β ∧
      ∀ a' b', |cutX W S G a' b' - cutX W S G' a' b'| ≤
        (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a' y) + Real.sqrt (bB d L W b' y)))
    (h2 : 0 < cutC β (β / 10) l W S G' m → cutY W G m ≤ (W : ℝ) ^ β ∧
      ∀ a' b', |cutX W S G' a' b' - cutX W S G a' b'| ≤
        (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a' y) + Real.sqrt (bB d L W b' y)))
    (δ : ℝ) (hδ : ∀ i, (W : ℝ) ^ (4 * β) * CutMoment_h d L W y i ≤ δ)
    (hδl : (1 + δ) ^ (l - 1) ≤ 2) (hδρ : 2 * l * δ ≤ 1 / 2)
    (hsmall : 32 * l * (W : ℝ) ^ (4 * β + β / 10) * CutMoment_J l W S G a b y ≤ 1) :
    |cutC β (β / 10) l W S G m * cutZ β (β / 10) l W S G m a b ^ k -
        cutC β (β / 10) l W S G' m * cutZ β (β / 10) l W S G' m a b ^ k| ≤
      {G₀ : Matrix (Zd d L) (Zd d L) ℂ | cutY W G₀ m ≤ (W : ℝ) ^ β}.indicator
        (fun G₀ => (8 * l + 32 * l * k * 2 ^ k) * (W : ℝ) ^ (4 * β + β / 10) *
          (1 + cutZ β (β / 10) l W S G₀ m a b ^ k) * CutMoment_J l W S G₀ a b y) G := by
  obtain ⟨hC0, -, hCpos⟩ := CutMoment_C β (β / 10) l W hW S G m
  obtain ⟨hC'0, -, hC'pos⟩ := CutMoment_C β (β / 10) l W hW S G' m
  have hZ0 := (CutMoment_Z β (β / 10) l W hl hW hS G m a b).1
  have hJ0 := (CutMoment_J_le l W hd hW hS G a b y).1
  have hind0 : 0 ≤ {G₀ : Matrix (Zd d L) (Zd d L) ℂ | cutY W G₀ m ≤ (W : ℝ) ^ β}.indicator
      (fun G₀ => (8 * l + 32 * l * k * 2 ^ k) * (W : ℝ) ^ (4 * β + β / 10) *
        (1 + cutZ β (β / 10) l W S G₀ m a b ^ k) * CutMoment_J l W S G₀ a b y) G := by
    refine Set.indicator_nonneg (fun G₀ _ => ?_) _
    have := (CutMoment_Z β (β / 10) l W hl hW hS G₀ m a b).1
    have := (CutMoment_J_le l W hd hW hS G₀ a b y).1
    positivity
  by_cases hboth : cutC β (β / 10) l W S G m = 0 ∧ cutC β (β / 10) l W S G' m = 0
  · rw [hboth.1, hboth.2]; simpa using hind0
  have hgood : cutY W G m ≤ (W : ℝ) ^ β ∧ cutY W G' m ≤ (W : ℝ) ^ β ∧
      ∀ a' b', |cutX W S G a' b' - cutX W S G' a' b'| ≤
        (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a' y) + Real.sqrt (bB d L W b' y)) := by
    by_cases hpos : 0 < cutC β (β / 10) l W S G m
    · obtain ⟨e1, e2⟩ := h1 hpos
      exact ⟨(hCpos hpos).1, e1, e2⟩
    · have hpos' : 0 < cutC β (β / 10) l W S G' m := by
        rcases hC'0.lt_or_eq with h | h
        · exact h
        · exact absurd ⟨le_antisymm (not_lt.1 hpos) hC0, h.symm⟩ hboth
      obtain ⟨e1, e2⟩ := h2 hpos'
      exact ⟨e1, (hC'pos hpos').1, fun a' b' => by rw [abs_sub_comm]; exact e2 a' b'⟩
  obtain ⟨hY, hY', hX⟩ := hgood
  rw [Set.indicator_of_mem (show G ∈ {G₀ : Matrix (Zd d L) (Zd d L) ℂ |
    cutY W G₀ m ≤ (W : ℝ) ^ β} from hY)]
  exact CutMoment_pair β (β / 10) (by positivity) l W k hl hW hS G G' m a b y hY hY' hX δ hδ hδl
    hδρ hsmall

end Assembly

/-! ## One step of the recursion -/

section Step

variable {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) {W L : ℕ} [NeZero L]

/-- The value of a formal sum of graphs with the kinds of [II, Def 3.2] has polynomial growth. -/
private lemma CutMoment_polyMeas_exp (z : ℂ) (hz : 0 < z.im) (hS : (Smat P.ψ W L).IsSymm)
    (hS0 : ∀ x y, 0 ≤ Smat P.ψ W L x y) (N : ℕ) (E : Expansion 3) (hE : ∀ g ∈ E, g.2.TKinds N)
    (e : Fin 3 → Zd d L) :
    PolyMeas (E.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e) := by
  have hL := pqLaws_Pexp_poly (Smat P.ψ W L) hS hS0
  induction E with
  | nil =>
    have : Expansion.valR ([] : Expansion 3) ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e =
        fun _ => 0 := by funext ω; simp [Expansion.valR]
    rw [this]; exact hL.adm_const 0
  | cons g E ih =>
    have : Expansion.valR (g :: E) ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e =
        g.2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e +
          Expansion.valR E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e := by
      funext ω; simp [Expansion.valR]
    rw [this]
    exact hL.adm_add _ _ (Moment_polyMeas_valR d P Sig W L z hz hS hS0 g.2
      (hE g (List.mem_cons_self ..)) e) (ih fun g' hg' => hE g' (List.mem_cons_of_mem _ hg'))

/-- **One step of the recursion at one size**: with `U = C Z_{𝔞𝔟}^k`, if the
terms of [II, (3.1)] at `(𝔞, t, t)` other than `Q` are at most `A₁ B_{𝔞t}` on the cutoff event
off an event `Bad` of probability at most `β_E` and at most `K_r (1 + ‖ω‖)^r` everywhere, if
`|E U Q_{𝔞,tt}| ≤ A₂ B_{𝔞t} (1 + E Z^k) + ε_Q`, `Σ_t B_{𝔞t} s_{t𝔟} ≤ C_{SB} B_{𝔞𝔟}`,
`|m| ≥ 1/4` and `B_{𝔞𝔟} ≥ W^{−K_B}`, then
`E Z^{k+1} ≤ 16 C_{SB} (A₁ + A₂)(1 + E Z^k) + 16 W^{K_B} (ε_E + ε_Q)`, with `ε_E` the bound of
`Lem512Zero_integral_le` at the threshold `‖ω‖ ≤ W`. -/
private lemma CutMoment_stepPt (z : ℂ) (hz : 0 < z.im) (hS : (Smat P.ψ W L).IsSymm)
    (hS0 : ∀ x y, 0 ≤ Smat P.ψ W L x y) (hS1 : ∀ x, ∑ y, Smat P.ψ W L x y = 1)
    (hcv : ∀ c, coordVar (Smat P.ψ W L) c ≤ 1)
    (n : ℕ) (𝒯 : TRec) (hId : 𝒯.Identity Sig n) (hsh : SelfEnergyShapesUpTo Sig n)
    (hQK : ∀ g ∈ 𝒯.Q, g.2.TKinds n)
    (β : ℝ) (l k : ℕ) (hl : 1 ≤ l) (hW : 1 ≤ (W : ℝ)) (a b : Zd d L)
    (Bad : Set (Sample (Zd d L))) (βE A₁ A₂ Kr εQ CSB KB : ℝ) (r j : ℕ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hKr : 0 ≤ Kr) (hβE : 0 ≤ βE)
    (hBad : gaussLaw (Smat P.ψ W L) Bad ≤ ENNReal.ofReal βE)
    (hrest : ∀ ω, 0 < cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z) (msc z) → ω ∉ Bad →
      ∀ t, ‖(leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Err).valR ⟨Pexp (Smat P.ψ W L)⟩
        (rbmData d P Sig W L z) ![a, t, t] ω‖ ≤ A₁ * bB d L W a t)
    (hrestAll : ∀ ω t, ‖(leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Err).valR
      ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, t, t] ω‖ ≤ Kr * (1 + ‖ω‖) ^ r)
    (hQ : ∀ t, ‖∫ ω, ((cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z) (msc z) *
        cutZ β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z) (msc z) a b ^ k : ℝ) : ℂ) *
        𝒯.Q.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, t, t] ω
          ∂(gaussLaw (Smat P.ψ W L))‖ ≤
      A₂ * bB d L W a t * (1 + ∫ ω, cutZ β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z)
        (msc z) a b ^ k ∂(gaussLaw (Smat P.ψ W L))) + εQ)
    (hεQ : 0 ≤ εQ) (hSB : ∑ t, bB d L W a t * Smat P.ψ W L t b ≤ CSB * bB d L W a b)
    (hm : 1 / 4 ≤ ‖msc z‖) (hBl : (W : ℝ) ^ (-KB) ≤ bB d L W a b) :
    ∫ ω, cutZ β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z) (msc z) a b ^ (k + 1)
        ∂(gaussLaw (Smat P.ψ W L)) ≤
      16 * CSB * (A₁ + A₂) * (1 + ∫ ω, cutZ β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z)
        (msc z) a b ^ k ∂(gaussLaw (Smat P.ψ W L))) +
      16 * (W : ℝ) ^ KB * ((2 * (W : ℝ) ^ (β / 10)) ^ k * Kr * ((1 + (W : ℝ)) ^ r * βE +
        ((1 + (W : ℝ)) ^ j)⁻¹ * (1 + 2 ^ (r + j) * (1 + LabelRemoval.gaussMoment (r + j)) *
          Fintype.card (Coord (Zd d L)))) + εQ) := by
  set S := Smat P.ψ W L with hSdef
  set μ := gaussLaw S with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw S
  set m := msc z with hmdef
  set C : Sample (Zd d L) → ℝ := fun ω => cutC β (β / 10) l W S (green (hmat ω) z) m with hC
  set Zf : Sample (Zd d L) → ℝ := fun ω => cutZ β (β / 10) l W S (green (hmat ω) z) m a b with hZf
  set U : Sample (Zd d L) → ℝ := fun ω => C ω * Zf ω ^ k with hU
  set Um : ℝ := (2 * (W : ℝ) ^ (β / 10)) ^ k with hUm
  set Tv : Zd d L → Sample (Zd d L) → ℝ := fun t ω => Tvar S (green (hmat ω) z) m a t with hTv
  set rest : Zd d L → Sample (Zd d L) → ℂ := fun t =>
    (leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Err).valR ⟨Pexp S⟩ (rbmData d P Sig W L z)
      ![a, t, t] with hrestdef
  set Qv : Zd d L → Sample (Zd d L) → ℂ := fun t =>
    𝒯.Q.valR ⟨Pexp S⟩ (rbmData d P Sig W L z) ![a, t, t] with hQv
  set EZ := ∫ ω, Zf ω ^ k ∂μ with hEZ
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hCm, hZm⟩ := CutMoment_meas_CZ β (β / 10) l W S z hz a b
  have hUmeas : Measurable U := hCm.mul (hZm.pow_const k)
  have hC01 : ∀ ω, 0 ≤ C ω ∧ C ω ≤ 1 := fun ω =>
    ⟨(CutMoment_C β (β / 10) l W hW S _ m).1, (CutMoment_C β (β / 10) l W hW S _ m).2.1⟩
  have hZ02 : ∀ ω, 0 ≤ Zf ω ∧ Zf ω ≤ 2 * (W : ℝ) ^ (β / 10) := fun ω =>
    CutMoment_Z β (β / 10) l W hl hW hS0 _ m a b
  have hU0 : ∀ ω, 0 ≤ U ω := fun ω => mul_nonneg (hC01 ω).1 (pow_nonneg (hZ02 ω).1 k)
  have hUZ : ∀ ω, U ω ≤ Zf ω ^ k := fun ω =>
    mul_le_of_le_one_left (pow_nonneg (hZ02 ω).1 k) (hC01 ω).2
  have hUm1 : ∀ ω, U ω ≤ Um := fun ω =>
    (hUZ ω).trans (pow_le_pow_left₀ (hZ02 ω).1 (hZ02 ω).2 k)
  have hUm0 : 0 ≤ Um := (hU0 0).trans (hUm1 0)
  have hZki : Integrable (fun ω => Zf ω ^ k) μ :=
    Integrable.mono' (integrable_const Um) (hZm.pow_const k).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hZ02 ω).1 k)]
        exact pow_le_pow_left₀ (hZ02 ω).1 (hZ02 ω).2 k)
  have hUi : Integrable U μ :=
    Integrable.mono' (integrable_const Um) hUmeas.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hU0 ω)]; exact hUm1 ω)
  have hEU : ∫ ω, U ω ∂μ ≤ EZ := integral_mono hUi hZki hUZ
  have hEZ0 : 0 ≤ EZ := integral_nonneg fun ω => pow_nonneg (hZ02 ω).1 k
  -- `T_{𝔞t}` is bounded and measurable
  have hm1 : ‖m‖ ≤ 1 := (norm_msc_lt_one hz).le
  have hT : ∀ t ω, 0 ≤ Tv t ω ∧ Tv t ω ≤ (z.im⁻¹) ^ 2 := fun t ω =>
    Moment_T_le S hS0 hS1 _ m hm1 z.im⁻¹ (fun x y => by
      have := norm_green_entry_le (hmat_isHermitian ω) hz.ne' x y
      rwa [abs_of_pos hz] at this) a t
  have hUTi : ∀ t, Integrable (fun ω => U ω * Tv t ω) μ := fun t =>
    Integrable.mono' (integrable_const (Um * (z.im⁻¹) ^ 2))
      (hUmeas.mul (Moment_meas_T d L S z hz a t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hU0 ω) (hT t ω).1)]
        exact mul_le_mul (hUm1 ω) (hT t ω).2 (hT t ω).1 hUm0)
  have hUP : PolyMeas fun ω => (U ω : ℂ) := by
    refine ⟨Complex.measurable_ofReal.comp hUmeas, Um, 0, fun ω => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU0 ω), pow_zero, mul_one]
    exact hUm1 ω
  have hL := pqLaws_Pexp_poly S hS hS0
  have hUQi : ∀ t, Integrable (fun ω => (U ω : ℂ) * Qv t ω) μ := fun t =>
    integrable_of_polyMeas S _ (hL.adm_mul _ _ hUP
      (CutMoment_polyMeas_exp P Sig z hz hS hS0 n 𝒯.Q hQK ![a, t, t]))
  -- one `t`
  have hone : ∀ t, ∫ ω, U ω * Tv t ω ∂μ ≤ (A₁ + A₂) * bB d L W a t * (1 + EZ) +
      (Um * Kr * ((1 + (W : ℝ)) ^ r * βE + ((1 + (W : ℝ)) ^ j)⁻¹ *
        (1 + 2 ^ (r + j) * (1 + LabelRemoval.gaussMoment (r + j)) *
          Fintype.card (Coord (Zd d L)))) + εQ) := by
    intro t
    have hTeq : ∀ ω, (Tv t ω : ℂ) = rest t ω + Qv t ω := fun ω =>
      Moment_T_eq d P Sig n 𝒯 hId hsh W L z hS hS0 hS1 hz a t ω
    set g : Sample (Zd d L) → ℝ := fun ω => U ω * (rest t ω).re with hg
    have hsplit : ∀ ω, U ω * Tv t ω = g ω + ((U ω : ℂ) * Qv t ω).re := by
      intro ω
      have h := congrArg Complex.re (hTeq ω)
      simp only [Complex.ofReal_re, Complex.add_re] at h
      rw [hg]; simp only [Complex.re_ofReal_mul]; rw [h]; ring
    have hre : Integrable (fun ω => ((U ω : ℂ) * Qv t ω).re) μ := (hUQi t).re
    have hgi : Integrable g μ := by
      have : g = fun ω => U ω * Tv t ω - ((U ω : ℂ) * Qv t ω).re := by
        funext ω; rw [hsplit ω]; ring
      rw [this]; exact (hUTi t).sub hre
    have hB0 : 0 ≤ bB d L W a t := by unfold bB; positivity
    set f2 : Sample (Zd d L) → ℝ := fun ω => max (g ω - A₁ * bB d L W a t * U ω) 0 with hf2
    have hf2i : Integrable f2 μ := (hgi.sub (hUi.const_mul _)).pos_part
    have hgle : ∀ ω, g ω ≤ A₁ * bB d L W a t * U ω + f2 ω := fun ω => by
      have := le_max_left (g ω - A₁ * bB d L W a t * U ω) 0
      simp only [hf2]; linarith
    have hf2bad : ∫ ω, f2 ω ∂μ ≤ 0 + Um * Kr * (1 + (W : ℝ)) ^ r * βE + Um * Kr *
        ((1 + (W : ℝ)) ^ j)⁻¹ * (1 + 2 ^ (r + j) * (1 + LabelRemoval.gaussMoment (r + j)) *
          Fintype.card (Coord (Zd d L))) := by
      refine Lem512Zero_integral_le S hcv f2 Bad 0 (Um * Kr) W βE r j le_rfl
        (mul_nonneg hUm0 hKr) hW0.le hβE hBad (fun ω => le_max_right _ _) (fun ω hω => ?_)
        (fun ω => ?_)
      · simp only [hf2]
        refine max_le ?_ le_rfl
        rcases (hC01 ω).1.lt_or_eq with hpos | hzero
        · have h1 := hrest ω hpos hω t
          have h2 : (rest t ω).re ≤ A₁ * bB d L W a t :=
            (Complex.re_le_norm _).trans h1
          have : g ω ≤ U ω * (A₁ * bB d L W a t) := mul_le_mul_of_nonneg_left h2 (hU0 ω)
          linarith
        · have hU00 : U ω = 0 := by simp only [hU]; rw [← hzero, zero_mul]
          simp only [hg, hU00, zero_mul, mul_zero, sub_zero, le_refl]
      · simp only [hf2]
        refine max_le ?_ (by positivity)
        have h1 : g ω ≤ U ω * ‖rest t ω‖ :=
          mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hU0 ω)
        have h2 : U ω * ‖rest t ω‖ ≤ Um * (Kr * (1 + ‖ω‖) ^ r) :=
          mul_le_mul (hUm1 ω) (hrestAll ω t) (norm_nonneg _) hUm0
        have h3 : 0 ≤ A₁ * bB d L W a t * U ω := by have := hU0 ω; positivity
        nlinarith
    have hgI : ∫ ω, g ω ∂μ ≤ A₁ * bB d L W a t * ∫ ω, U ω ∂μ + ∫ ω, f2 ω ∂μ := by
      rw [← integral_const_mul, ← integral_add (hUi.const_mul _) hf2i]
      exact integral_mono hgi ((hUi.const_mul _).add hf2i) hgle
    have hQre : ∫ ω, ((U ω : ℂ) * Qv t ω).re ∂μ ≤
        A₂ * bB d L W a t * (1 + EZ) + εQ := by
      have e := integral_re (hUQi t)
      simp only [RCLike.re_to_complex] at e
      rw [e]
      exact (Complex.re_le_norm _).trans (hQ t)
    calc ∫ ω, U ω * Tv t ω ∂μ = ∫ ω, g ω ∂μ + ∫ ω, ((U ω : ℂ) * Qv t ω).re ∂μ := by
          rw [← integral_add hgi hre]
          exact integral_congr_ae (Eventually.of_forall hsplit)
      _ ≤ A₁ * bB d L W a t * EZ + (0 + Um * Kr * (1 + (W : ℝ)) ^ r * βE + Um * Kr *
            ((1 + (W : ℝ)) ^ j)⁻¹ * (1 + 2 ^ (r + j) * (1 + LabelRemoval.gaussMoment (r + j)) *
              Fintype.card (Coord (Zd d L)))) + (A₂ * bB d L W a t * (1 + EZ) + εQ) := by
          have := mul_le_mul_of_nonneg_left hEU (by positivity : 0 ≤ A₁ * bB d L W a t)
          linarith
      _ ≤ _ := by
          have : A₁ * bB d L W a t * EZ ≤ A₁ * bB d L W a t * (1 + EZ) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          nlinarith
  -- the sum over `t`
  set E : ℝ := Um * Kr * ((1 + (W : ℝ)) ^ r * βE + ((1 + (W : ℝ)) ^ j)⁻¹ *
    (1 + 2 ^ (r + j) * (1 + LabelRemoval.gaussMoment (r + j)) *
      Fintype.card (Coord (Zd d L)))) + εQ with hE
  have hE0 : 0 ≤ E := by
    have : 0 ≤ LabelRemoval.gaussMoment (r + j) :=
      integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
    rw [hE]; positivity
  have hB : 0 < bB d L W a b := by unfold bB; positivity
  have hm0 : 0 < ‖m‖ := by linarith
  have hmB : 0 < ‖m‖ ^ 2 * bB d L W a b := by positivity
  have hpt : ∀ ω, Zf ω ^ (k + 1) =
      (‖m‖ ^ 2 * bB d L W a b)⁻¹ * ∑ t, S t b * (U ω * Tv t ω) := by
    intro ω
    have hX := CutMoment_X_eq W hW S (green (hmat ω) z) m a b
    have hZ : Zf ω = C ω * cutX W S (green (hmat ω) z) a b := rfl
    have hXe : cutX W S (green (hmat ω) z) a b =
        (‖m‖ ^ 2 * bB d L W a b)⁻¹ * ∑ t, S t b * Tv t ω := by
      rw [← hX]; field_simp
    have h2 : Zf ω ^ (k + 1) = (C ω * Zf ω ^ k) * cutX W S (green (hmat ω) z) a b := by
      rw [pow_succ]; nth_rewrite 2 [hZ]; ring
    rw [h2, hXe]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by simp only [hU]; ring
  have hint : ∫ ω, Zf ω ^ (k + 1) ∂μ =
      (‖m‖ ^ 2 * bB d L W a b)⁻¹ * ∑ t, S t b * ∫ ω, U ω * Tv t ω ∂μ := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
      integral_finsetSum _ fun t _ => (hUTi t).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun t _ => integral_const_mul _ _
  have hcol : ∑ t, S t b = 1 := by
    rw [← hS1 b]; exact Finset.sum_congr rfl fun t _ => hS.apply b t
  have hCSB : 0 ≤ CSB := by
    have h0 : 0 ≤ ∑ t, bB d L W a t * S t b := Finset.sum_nonneg fun t _ =>
      mul_nonneg (by unfold bB; positivity) (hS0 t b)
    by_contra h
    push Not at h
    nlinarith
  have hsum : ∑ t, S t b * ∫ ω, U ω * Tv t ω ∂μ ≤
      (A₁ + A₂) * (1 + EZ) * (CSB * bB d L W a b) + E := by
    calc ∑ t, S t b * ∫ ω, U ω * Tv t ω ∂μ
        ≤ ∑ t, S t b * ((A₁ + A₂) * bB d L W a t * (1 + EZ) + E) :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hone t) (hS0 t b)
      _ = (A₁ + A₂) * (1 + EZ) * ∑ t, bB d L W a t * S t b + E * ∑ t, S t b := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ ≤ (A₁ + A₂) * (1 + EZ) * (CSB * bB d L W a b) + E := by
          rw [hcol, mul_one]
          have : 0 ≤ (A₁ + A₂) * (1 + EZ) := by positivity
          have := mul_le_mul_of_nonneg_left hSB this
          linarith
  rw [hint]
  have hinvm : (‖m‖ ^ 2)⁻¹ ≤ 16 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have hinvB : (bB d L W a b)⁻¹ ≤ (W : ℝ) ^ KB := by
    rw [inv_le_comm₀ hB (by positivity), ← Real.rpow_neg hW0.le]; exact hBl
  have hinv1 : (bB d L W a b)⁻¹ * (‖m‖ ^ 2)⁻¹ ≤ 16 * (W : ℝ) ^ KB := by
    rw [mul_comm]; exact mul_le_mul hinvm hinvB (by positivity) (by norm_num)
  calc (‖m‖ ^ 2 * bB d L W a b)⁻¹ * ∑ t, S t b * ∫ ω, U ω * Tv t ω ∂μ
      ≤ (‖m‖ ^ 2 * bB d L W a b)⁻¹ * ((A₁ + A₂) * (1 + EZ) * (CSB * bB d L W a b) + E) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (‖m‖ ^ 2)⁻¹ * (CSB * (A₁ + A₂) * (1 + EZ)) +
          (bB d L W a b)⁻¹ * (‖m‖ ^ 2)⁻¹ * E := by
        field_simp
    _ ≤ 16 * (CSB * (A₁ + A₂) * (1 + EZ)) + 16 * (W : ℝ) ^ KB * E := by
        gcongr
    _ = _ := by rw [hE]; ring

end Step

/-! ## Exponents along the filter -/

/-- Eventually along the filter, `C W^a ≤ W^b` for `a < b`. -/
private lemma CutMoment_ev_absorb (d n : ℕ) (c₀ c₁ c₀T C a b : ℝ) (hab : a < b) :
    ∀ᶠ p in llFilter d n c₀ c₁ c₀T, C * (p.1.1 : ℝ) ^ a ≤ (p.1.1 : ℝ) ^ b := by
  filter_upwards [CutMoment_ev_rpow d n c₀ c₁ c₀T C (b - a) (by linarith),
    CutMoment_ev_W d n c₀ c₁ c₀T 1] with p hp hW
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  calc C * (p.1.1 : ℝ) ^ a ≤ (p.1.1 : ℝ) ^ (b - a) * (p.1.1 : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hW0.le _)
    _ = (p.1.1 : ℝ) ^ b := by rw [← Real.rpow_add hW0]; ring_nf

/-- On `adm(c₀, c₁)`: `|Z_L^d| ≤ W^{d/c₁}` and `|Coord| ≤ 3 W^{2d/c₁}`. -/
private lemma CutMoment_cards {c₀ c₁ : ℝ} (hc₁ : 0 < c₁) (d : ℕ) (p : SizeL)
    (hp : p.1 ∈ adm c₀ c₁) (hW : 1 ≤ (p.1.1 : ℝ)) :
    (Fintype.card (Zd d p.1.2) : ℝ) ≤ (p.1.1 : ℝ) ^ ((d : ℝ) / c₁) ∧
      (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ 3 * (p.1.1 : ℝ) ^ (2 * (d : ℝ) / c₁) := by
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have h0 : (Fintype.card (Zd d p.1.2) : ℝ) ≤ (p.1.1 : ℝ) ^ ((d : ℝ) / c₁) :=
    card_Zd_le_adm d c₀ c₁ hc₁ p hp
  refine ⟨h0, LabelRemoval_card_coord.trans ?_⟩
  have h2 : (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ (p.1.1 : ℝ) ^ (2 * (d : ℝ) / c₁) := by
    calc (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ ((p.1.1 : ℝ) ^ ((d : ℝ) / c₁)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h0 2
      _ = (p.1.1 : ℝ) ^ (2 * (d : ℝ) / c₁) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  linarith

/-- **The numerical condition of the label removal on the cutoff event**: for `R` components,
there is `E` such that for `D_m ≥ E`, eventually along the filter, for every sample with
`‖ω‖ ≤ W` and every set `T` with `P(T) ≤ |Z_L^d| W^{−D_m/2}`:
`M_{4R}(ω, y)^{1/2} P(T)^{1/2} ≤ (W^{−K_B/2} / M_b)^R`. -/
private lemma CutMoment_hP (d n : ℕ) (P : Profile d) (c₀ c₁ c₀T : ℝ) (hc₁ : 0 < c₁) (R : ℕ)
    (KB : ℝ) :
    ∃ E : ℝ, ∀ Dm : ℝ, E ≤ Dm → ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
      ∀ (ω : Sample (Zd d p.1.2)) (y : Zd d p.1.2) (T : Set (Sample (Zd d p.1.2))),
        ‖ω‖ ≤ p.1.1 → (gaussLaw (Smat P.ψ p.1.1 p.1.2) T).toReal ≤
          (Fintype.card (Zd d p.1.2) : ℝ) * (p.1.1 : ℝ) ^ (-(Dm / 2)) →
        Real.sqrt (LabelRemoval.momBound (2 * (2 * R)) ω y) *
            Real.sqrt (gaussLaw (Smat P.ψ p.1.1 p.1.2) T).toReal ≤
          ((p.1.1 : ℝ) ^ (-(KB / 2)) / LabelRemoval_Mb R d p.1.2 p.1.1 (2 / c₁)) ^ R := by
  set gm := LabelRemoval.gaussMoment (2 * (2 * R)) with hgm
  have hgm0 : 0 ≤ gm := integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  -- `M_{4R} ≤ W^{E₁}`, `M_b ≤ W^{E₂}`
  set E₁ : ℝ := 4 * R + 2 * d / c₁ + 1 with hE₁
  set E₂ : ℝ := 2 * d / c₁ + 2 / c₁ + 2 with hE₂
  refine ⟨2 * (E₁ + d / c₁ + 2 * R * E₂ + R * KB) + 2, fun Dm hDm => ?_⟩
  have hd0 : (0 : ℝ) ≤ d / c₁ := by positivity
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, CutMoment_ev_W d n c₀ c₁ c₀T 2,
    CutMoment_ev_rpow d n c₀ c₁ c₀T (2 ^ (2 * (2 * R)) + 3 * 2 ^ (2 * (2 * R)) * (1 + gm)) 1
      one_pos,
    CutMoment_ev_rpow d n c₀ c₁ c₀T (96 * ((R : ℝ) + 1) * 4 ^ R) 1 one_pos]
    with p hp hW2 hC1 hC2 ω y T hω hT
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  obtain ⟨hN, hNc⟩ := CutMoment_cards hc₁ d p hp hW1
  rw [Real.rpow_one] at hC1 hC2
  -- the moment bound
  have hM : LabelRemoval.momBound (2 * (2 * R)) ω y ≤ W ^ E₁ := by
    unfold LabelRemoval.momBound
    have hrc : ((rowCoords y).card : ℝ) ≤ Fintype.card (Coord (Zd d p.1.2)) := by
      exact_mod_cast Finset.card_le_univ _
    have h1 : (1 + ‖ω‖) ^ (2 * (2 * R)) ≤ (2 * W) ^ (2 * (2 * R)) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hX : 1 ≤ W ^ (2 * (d : ℝ) / c₁) := Real.one_le_rpow hW1 (by positivity)
    have h4 : W ^ (2 * (2 * R)) ≤ W ^ (4 * (R : ℝ) + 2 * d / c₁) := by
      rw [← Real.rpow_natCast]
      have : (0 : ℝ) ≤ 2 * (d : ℝ) / c₁ := by positivity
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by push_cast; linarith)
    have hsplit : W ^ E₁ = W ^ (4 * (R : ℝ) + 2 * d / c₁) * W := by
      rw [hE₁, Real.rpow_add hW0, Real.rpow_one]
    have hWE : 1 ≤ W ^ (4 * (R : ℝ) + 2 * d / c₁) := Real.one_le_rpow hW1 (by positivity)
    have hX2 : W ^ (2 * (d : ℝ) / c₁) ≤ W ^ (4 * (R : ℝ) + 2 * d / c₁) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by have : (0 : ℝ) ≤ 4 * R := by positivity
                                               linarith)
    calc (1 + ‖ω‖) ^ (2 * (2 * R)) + 2 ^ (2 * (2 * R)) * (1 + gm) * ((rowCoords y).card : ℝ)
        ≤ 2 ^ (2 * (2 * R)) * W ^ (2 * (2 * R)) + 2 ^ (2 * (2 * R)) * (1 + gm) *
            (3 * W ^ (2 * (d : ℝ) / c₁)) := by
          rw [← mul_pow]; gcongr; exact hrc.trans hNc
      _ ≤ 2 ^ (2 * (2 * R)) * W ^ (4 * (R : ℝ) + 2 * d / c₁) +
            3 * 2 ^ (2 * (2 * R)) * (1 + gm) * W ^ (4 * (R : ℝ) + 2 * d / c₁) := by
          have a1 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 ^ (2 * (2 * R)))
          have a2 := mul_le_mul_of_nonneg_left hX2
            (by positivity : (0 : ℝ) ≤ 3 * 2 ^ (2 * (2 * R)) * (1 + gm))
          nlinarith
      _ = (2 ^ (2 * (2 * R)) + 3 * 2 ^ (2 * (2 * R)) * (1 + gm)) *
            W ^ (4 * (R : ℝ) + 2 * d / c₁) := by ring
      _ ≤ W * W ^ (4 * (R : ℝ) + 2 * d / c₁) := by gcongr
      _ = W ^ E₁ := by rw [hsplit]; ring
  -- the bound `M_b`
  set Mb := LabelRemoval_Mb R d p.1.2 p.1.1 (2 / c₁) with hMbdef
  have hLd : ((p.1.2 : ℝ) ^ d) ≤ W ^ ((d : ℝ) / c₁) := by
    have := hN; rw [card_Zd] at this; push_cast at this; exact this
  have hLd1 : (1 : ℝ) ≤ (p.1.2 : ℝ) ^ d := one_le_pow₀ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne p.1.2))
  have hW2c : 1 ≤ W ^ (2 / c₁) := Real.one_le_rpow hW1 (by positivity)
  have hMb1 : 1 ≤ Mb := by
    rw [hMbdef, LabelRemoval_Mb, LabelRemoval_Mres]
    have : (1 : ℝ) ≤ 8 * ((R : ℝ) + 1) * 4 ^ R := by
      have := one_le_pow₀ (n := R) (by norm_num : (1 : ℝ) ≤ 4); nlinarith
    have : (1 : ℝ) ≤ 6 * ((p.1.2 : ℝ) ^ d) ^ 2 * (W ^ (2 / c₁) + 1) := by nlinarith
    nlinarith
  have hMbE : Mb ≤ W ^ E₂ := by
    rw [hMbdef, LabelRemoval_Mb, LabelRemoval_Mres]
    have h1 : ((p.1.2 : ℝ) ^ d) ^ 2 ≤ W ^ (2 * (d : ℝ) / c₁) := by
      calc ((p.1.2 : ℝ) ^ d) ^ 2 ≤ (W ^ ((d : ℝ) / c₁)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hLd 2
        _ = W ^ (2 * (d : ℝ) / c₁) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have h2 : W ^ (2 / c₁) + 1 ≤ 2 * W ^ (2 / c₁) := by linarith
    have hsplit : W ^ E₂ = W * (W ^ (2 * (d : ℝ) / c₁) * W ^ (2 / c₁)) * W := by
      rw [hE₂, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_two]; ring
    calc 8 * ((R : ℝ) + 1) * 4 ^ R * (6 * ((p.1.2 : ℝ) ^ d) ^ 2 * (W ^ (2 / c₁) + 1))
        ≤ 8 * ((R : ℝ) + 1) * 4 ^ R * (6 * W ^ (2 * (d : ℝ) / c₁) * (2 * W ^ (2 / c₁))) := by
          gcongr
      _ = 96 * ((R : ℝ) + 1) * 4 ^ R * (W ^ (2 * (d : ℝ) / c₁) * W ^ (2 / c₁)) := by ring
      _ ≤ W * (W ^ (2 * (d : ℝ) / c₁) * W ^ (2 / c₁)) := by gcongr
      _ ≤ W * (W ^ (2 * (d : ℝ) / c₁) * W ^ (2 / c₁)) * W :=
          le_mul_of_one_le_right (by positivity) hW1
      _ = W ^ E₂ := hsplit.symm
  -- the right side
  have hR : W ^ (-((R : ℝ) * (KB / 2 + E₂))) ≤ (W ^ (-(KB / 2)) / Mb) ^ R := by
    have h1 : W ^ (-(KB / 2) - E₂) ≤ W ^ (-(KB / 2)) / Mb := by
      rw [Real.rpow_sub hW0]
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) hMbE
    calc W ^ (-((R : ℝ) * (KB / 2 + E₂))) = (W ^ (-(KB / 2) - E₂)) ^ R := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 R
  -- the left side
  have hT' : (gaussLaw (Smat P.ψ p.1.1 p.1.2) T).toReal ≤ W ^ ((d : ℝ) / c₁ - Dm / 2) := by
    refine hT.trans ?_
    rw [show W ^ ((d : ℝ) / c₁ - Dm / 2) = W ^ ((d : ℝ) / c₁) * W ^ (-(Dm / 2)) by
      rw [← Real.rpow_add hW0]; ring_nf]
    exact mul_le_mul_of_nonneg_right hN (by positivity)
  have hL : Real.sqrt (LabelRemoval.momBound (2 * (2 * R)) ω y) *
      Real.sqrt (gaussLaw (Smat P.ψ p.1.1 p.1.2) T).toReal ≤
        W ^ ((E₁ + (d : ℝ) / c₁ - Dm / 2) / 2) := by
    have e : W ^ ((E₁ + (d : ℝ) / c₁ - Dm / 2) / 2) =
        Real.sqrt (W ^ E₁) * Real.sqrt (W ^ ((d : ℝ) / c₁ - Dm / 2)) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.rpow_add hW0,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]; ring_nf
    rw [e]
    exact mul_le_mul (Real.sqrt_le_sqrt hM) (Real.sqrt_le_sqrt hT') (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  refine hL.trans (le_trans ?_ hR)
  exact Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)

/-- `CutMoment_hP` for all the graphs of a list at once. -/
private lemma CutMoment_hP_list (d n : ℕ) (P : Profile d) (c₀ c₁ c₀T : ℝ) (hc₁ : 0 < c₁)
    (KB : ℝ) (E : Expansion 3) :
    ∃ E₀ : ℝ, ∀ Dm : ℝ, E₀ ≤ Dm → ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ g ∈ E,
      ∀ (ω : Sample (Zd d p.1.2)) (y : Zd d p.1.2) (T : Set (Sample (Zd d p.1.2))),
        ‖ω‖ ≤ p.1.1 → (gaussLaw (Smat P.ψ p.1.1 p.1.2) T).toReal ≤
          (Fintype.card (Zd d p.1.2) : ℝ) * (p.1.1 : ℝ) ^ (-(Dm / 2)) →
        Real.sqrt (LabelRemoval.momBound (2 * (2 * g.2.wDLights.comps.length)) ω y) *
            Real.sqrt (gaussLaw (Smat P.ψ p.1.1 p.1.2) T).toReal ≤
          ((p.1.1 : ℝ) ^ (-(KB / 2)) /
            LabelRemoval_Mb g.2.wDLights.comps.length d p.1.2 p.1.1 (2 / c₁)) ^
              g.2.wDLights.comps.length := by
  induction E with
  | nil => exact ⟨0, fun Dm _ => Eventually.of_forall fun p g hg => by simp at hg⟩
  | cons g E ih =>
    obtain ⟨E₁, h₁⟩ := ih
    obtain ⟨E₂, h₂⟩ := CutMoment_hP d n P c₀ c₁ c₀T hc₁ g.2.wDLights.comps.length KB
    refine ⟨max E₁ E₂, fun Dm hDm => ?_⟩
    filter_upwards [h₁ Dm ((le_max_left _ _).trans hDm), h₂ Dm ((le_max_right _ _).trans hDm)]
      with p hp₁ hp₂ g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact hp₂
    · exact hp₁ g' hg'

/-- `CutMoment_absVal_apriori` for all the graphs of a list at once. -/
private lemma CutMoment_absVal_apriori_list (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (c₀ c₁ κ ε c₀T : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ)
    (hε : 0 < ε) (n : ℕ) (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig n)
    (E : Expansion 3) (hE : ∀ g ∈ E, g.2.TKinds n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ g ∈ E, ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
        g.2.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig (green (hmat ω) z)) ![a, b, b] ≤
          (p.1.1 : ℝ) ^ K := by
  induction E with
  | nil => exact ⟨0, le_rfl, Eventually.of_forall fun p g hg => by simp at hg⟩
  | cons g E ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := ih fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')
    obtain ⟨K₂, h₂⟩ := CutMoment_absVal_apriori d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε n Sig hSE
      g.2 (hE g (List.mem_cons_self ..))
    refine ⟨max K₁ |K₂|, le_max_of_le_left hK₁, ?_⟩
    filter_upwards [h₁, h₂, CutMoment_ev_W d n c₀ c₁ c₀T 1] with p hp₁ hp₂ hW g' hg' z hz a b ω
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact (hp₂ z hz a b ω).trans (Real.rpow_le_rpow_of_exponent_le hW
        ((le_abs_self _).trans (le_max_right _ _)))
    · exact (hp₁ g' hg' z hz a b ω).trans (Real.rpow_le_rpow_of_exponent_le hW (le_max_left _ _))

/-! ## The graphs of `Q` at one size -/

section QAll

variable {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) {W L : ℕ} [NeZero L]

/-- The pairs `(ω, η)` off which `cutPairStmt` holds at `(ω, η)` and at the exchanged pair. -/
private def CutMoment_T (β : ℝ) (l : ℕ) (z : ℂ) (y : Zd d L) :
    Set (Sample (Zd d L) × Sample (Zd d L)) :=
  let B : Set (Sample (Zd d L) × Sample (Zd d L)) :=
    {q | 0 < cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat q.1) z) (msc z) ∧
      ¬ (cutY W (green (hmat (resampleRow y q.2 q.1)) z) (msc z) ≤ (W : ℝ) ^ β ∧
        ∀ a b, |cutX W (Smat P.ψ W L) (green (hmat q.1) z) a b -
            cutX W (Smat P.ψ W L) (green (hmat (resampleRow y q.2 q.1)) z) a b| ≤
          (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)))}
  toMeasurable ((gaussLaw (Smat P.ψ W L)).prod (gaussLaw (Smat P.ψ W L))) B ∪
    (fun q : Sample (Zd d L) × Sample (Zd d L) => (resampleRow y q.2 q.1, resampleRow y q.1 q.2))
      ⁻¹' toMeasurable ((gaussLaw (Smat P.ψ W L)).prod (gaussLaw (Smat P.ψ W L))) B

/-- `CutMoment_T` is measurable, has measure at most twice that of the event of `cutPairStmt`,
and off it the pair `(ω, ω^{[y,η]})` is good in both directions. -/
private lemma CutMoment_T_props (β : ℝ) (l : ℕ) (z : ℂ) (y : Zd d L) (εp : ℝ) (hεp : 0 ≤ εp)
    (hpair : ((gaussLaw (Smat P.ψ W L)).prod (gaussLaw (Smat P.ψ W L)))
      {q | 0 < cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat q.1) z) (msc z) ∧
        ¬ (cutY W (green (hmat (resampleRow y q.2 q.1)) z) (msc z) ≤ (W : ℝ) ^ β ∧
          ∀ a b, |cutX W (Smat P.ψ W L) (green (hmat q.1) z) a b -
              cutX W (Smat P.ψ W L) (green (hmat (resampleRow y q.2 q.1)) z) a b| ≤
            (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)))} ≤
        ENNReal.ofReal εp) :
    MeasurableSet (CutMoment_T P (W := W) β l z y) ∧
      ((gaussLaw (Smat P.ψ W L)).prod (gaussLaw (Smat P.ψ W L))).real
        (CutMoment_T P (W := W) β l z y) ≤ 2 * εp ∧
      ∀ ω η, (ω, η) ∉ CutMoment_T P (W := W) β l z y →
        (0 < cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z) (msc z) →
          cutY W (green (hmat (resampleRow y η ω)) z) (msc z) ≤ (W : ℝ) ^ β ∧
          ∀ a b, |cutX W (Smat P.ψ W L) (green (hmat ω) z) a b -
              cutX W (Smat P.ψ W L) (green (hmat (resampleRow y η ω)) z) a b| ≤
            (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y))) ∧
        (0 < cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat (resampleRow y η ω)) z) (msc z) →
          cutY W (green (hmat ω) z) (msc z) ≤ (W : ℝ) ^ β ∧
          ∀ a b, |cutX W (Smat P.ψ W L) (green (hmat (resampleRow y η ω)) z) a b -
              cutX W (Smat P.ψ W L) (green (hmat ω) z) a b| ≤
            (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y))) := by
  set μ := gaussLaw (Smat P.ψ W L) with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw _
  set B : Set (Sample (Zd d L) × Sample (Zd d L)) :=
    {q | 0 < cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat q.1) z) (msc z) ∧
      ¬ (cutY W (green (hmat (resampleRow y q.2 q.1)) z) (msc z) ≤ (W : ℝ) ^ β ∧
        ∀ a b, |cutX W (Smat P.ψ W L) (green (hmat q.1) z) a b -
            cutX W (Smat P.ψ W L) (green (hmat (resampleRow y q.2 q.1)) z) a b| ≤
          (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)))} with hB
  have hsw := CutMoment_swap (Smat P.ψ W L) y
  have hTB : CutMoment_T P (W := W) β l z y = toMeasurable (μ.prod μ) B ∪
      (fun q : Sample (Zd d L) × Sample (Zd d L) => (resampleRow y q.2 q.1, resampleRow y q.1 q.2))
        ⁻¹' toMeasurable (μ.prod μ) B := rfl
  have hm1 := measurableSet_toMeasurable (μ.prod μ) B
  refine ⟨?_, ?_, fun ω η hωη => ⟨fun hC => ?_, fun hC => ?_⟩⟩
  · rw [hTB]; exact hm1.union (hsw.measurable hm1)
  · rw [hTB]
    have h1 : (μ.prod μ) (toMeasurable (μ.prod μ) B) ≤ ENNReal.ofReal εp := by
      rw [measure_toMeasurable]; exact hpair
    have h2 : (μ.prod μ) ((fun q : Sample (Zd d L) × Sample (Zd d L) =>
        (resampleRow y q.2 q.1, resampleRow y q.1 q.2)) ⁻¹' toMeasurable (μ.prod μ) B) ≤
          ENNReal.ofReal εp := by
      rw [hsw.measure_preimage hm1.nullMeasurableSet]; exact h1
    have h3 := (measure_union_le (μ := μ.prod μ) (toMeasurable (μ.prod μ) B)
      ((fun q : Sample (Zd d L) × Sample (Zd d L) =>
        (resampleRow y q.2 q.1, resampleRow y q.1 q.2)) ⁻¹' toMeasurable (μ.prod μ) B)).trans
      (add_le_add h1 h2)
    rw [← ENNReal.ofReal_add hεp hεp] at h3
    rw [Measure.real]
    refine (ENNReal.toReal_le_of_le_ofReal (by linarith) h3).trans (by linarith)
  · have hn : (ω, η) ∉ B := fun h => hωη (Or.inl (subset_toMeasurable _ _ h))
    by_contra hcon
    exact hn ⟨hC, hcon⟩
  · have hn : (resampleRow y η ω, resampleRow y ω η) ∉ B := fun h =>
      hωη (Or.inr (subset_toMeasurable _ _ h))
    by_contra hcon
    refine hn ⟨hC, ?_⟩
    simp only [CutMoment_res_res]
    exact hcon

end QAll

section QAll2

variable {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) {W L : ℕ} [NeZero L]

/-- **The graphs of `Q` at one size**: `|E C Z_{𝔞𝔟}^k Q_{𝔞,tt}|` is at most
`#Q B_{𝔞t} (1 + E Z^k) + #Q 2 U_max W^{K_Q} |Z_L^d| 2ε_p`. -/
private lemma CutMoment_QBound (hd : 8 ≤ d) (z : ℂ) (hz : 0 < z.im)
    (hS : (Smat P.ψ W L).IsSymm) (hS0 : ∀ x y, 0 ≤ Smat P.ψ W L x y) (n : ℕ) (Qs : Expansion 3)
    (hQK : ∀ g ∈ Qs, g.2.TKinds n) (hQq : ∀ g ∈ Qs, g.2.IsQGraph)
    (hQint : ∀ g ∈ Qs, g.1 ≠ 0 → ¬ g.2.DiagRecoll → ∀ u : Atom 3 g.1,
      (∃ c ∈ g.2.comps, c.label = some (.Q, u)) → ∃ v : Fin g.1, u = .inr v)
    (β : ℝ) (hβ : 0 ≤ β) (l k : ℕ) (hl : 1 ≤ l) (hW : 1 ≤ (W : ℝ)) (a b t : Zd d L)
    (ν' KQ εp δ : ℝ) (hν'0 : 0 ≤ ν') (hεp : 0 ≤ εp)
    (hrows : ∀ ω, cutY W (green (hmat ω) z) (msc z) ≤ (W : ℝ) ^ β → ∀ g ∈ Qs,
      ((g.1 = 0 ∨ g.2.DiagRecoll) →
        g.2.absVal (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) ![a, t, t] ≤
          (W : ℝ) ^ ν' * bB d L W a t) ∧
      (g.1 ≠ 0 → ¬ g.2.DiagRecoll → ∀ (v : Fin g.1) (c : Zd d L),
        g.2.absValHook (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) ![a, t, t] v
            (fun y => Real.sqrt (bB d L W c y)) ≤
          (W : ℝ) ^ (-(3 * (d : ℝ) / 8)) * bB d L W a t))
    (hAp : ∀ g ∈ Qs, ∀ ω,
      g.2.absVal (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) ![a, t, t] ≤ (W : ℝ) ^ KQ)
    (hpair : ∀ y : Zd d L, ((gaussLaw (Smat P.ψ W L)).prod (gaussLaw (Smat P.ψ W L)))
      {q | 0 < cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat q.1) z) (msc z) ∧
        ¬ (cutY W (green (hmat (resampleRow y q.2 q.1)) z) (msc z) ≤ (W : ℝ) ^ β ∧
          ∀ a b, |cutX W (Smat P.ψ W L) (green (hmat q.1) z) a b -
              cutX W (Smat P.ψ W L) (green (hmat (resampleRow y q.2 q.1)) z) a b| ≤
            (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)))} ≤
        ENNReal.ofReal εp)
    (hδ : ∀ y i, (W : ℝ) ^ (4 * β) * CutMoment_h d L W y i ≤ δ)
    (hδl : (1 + δ) ^ (l - 1) ≤ 2) (hδρ : 2 * l * δ ≤ 1 / 2)
    (hsmall : ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) y,
      32 * l * (W : ℝ) ^ (4 * β + β / 10) * CutMoment_J l W (Smat P.ψ W L) G a b y ≤ 1)
    (hKB : (8 * l + 32 * l * k * 2 ^ k) * (W : ℝ) ^ (4 * β + β / 10) *
      (4 * (W : ℝ) ^ (-(3 * (d : ℝ) / 8) + ν')) ≤ 1)
    (hνd : (W : ℝ) ^ (-((d : ℝ) / 2)) * (W : ℝ) ^ ν' ≤ (W : ℝ) ^ (-(3 * (d : ℝ) / 8) + ν')) :
    ‖∫ ω, ((cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z) (msc z) *
        cutZ β (β / 10) l W (Smat P.ψ W L) (green (hmat ω) z) (msc z) a b ^ k : ℝ) : ℂ) *
        Qs.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, t, t] ω
          ∂(gaussLaw (Smat P.ψ W L))‖ ≤
      Qs.length * (bB d L W a t * (1 + ∫ ω, cutZ β (β / 10) l W (Smat P.ψ W L)
        (green (hmat ω) z) (msc z) a b ^ k ∂(gaussLaw (Smat P.ψ W L)))) +
      Qs.length * (2 * (2 * (W : ℝ) ^ (β / 10)) ^ k * (W : ℝ) ^ KQ *
        (Fintype.card (Zd d L) * (2 * εp))) := by
  set S := Smat P.ψ W L with hSdef
  set μ := gaussLaw S with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw S
  have hL := pqLaws_Pexp_poly S hS hS0
  set m := msc z with hm
  set U : Sample (Zd d L) → ℝ := fun ω => cutC β (β / 10) l W S (green (hmat ω) z) m *
    cutZ β (β / 10) l W S (green (hmat ω) z) m a b ^ k with hU
  set Zf : Sample (Zd d L) → ℝ := fun ω => cutZ β (β / 10) l W S (green (hmat ω) z) m a b ^ k
    with hZf
  set Um : ℝ := (2 * (W : ℝ) ^ (β / 10)) ^ k with hUm
  set EZ := ∫ ω, Zf ω ∂μ with hEZ
  set ε₂ : ℝ := 2 * Um * (W : ℝ) ^ KQ * (Fintype.card (Zd d L) * (2 * εp)) with hε₂
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hCm, hZm⟩ := CutMoment_meas_CZ β (β / 10) l W S z hz a b
  have hUmeas : Measurable U := hCm.mul (hZm.pow_const k)
  have hZf0 : ∀ ω, 0 ≤ Zf ω := fun ω =>
    pow_nonneg (CutMoment_Z β (β / 10) l W hl hW hS0 _ m a b).1 k
  have hU0 : ∀ ω, 0 ≤ U ω := fun ω =>
    mul_nonneg (CutMoment_C β (β / 10) l W hW S _ m).1 (hZf0 ω)
  have hU1 : ∀ ω, U ω ≤ Um := fun ω => by
    have h1 := (CutMoment_C β (β / 10) l W hW S (green (hmat ω) z) m).2.1
    have h2 := CutMoment_Z β (β / 10) l W hl hW hS0 (green (hmat ω) z) m a b
    calc U ω ≤ 1 * Zf ω := mul_le_mul_of_nonneg_right h1 (hZf0 ω)
      _ ≤ Um := by rw [one_mul]; exact pow_le_pow_left₀ h2.1 h2.2 k
  have hZi : Integrable Zf μ :=
    Integrable.mono' (integrable_const Um) (hZm.pow_const k).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hZf0 ω)]
        have h2 := CutMoment_Z β (β / 10) l W hl hW hS0 (green (hmat ω) z) m a b
        exact pow_le_pow_left₀ h2.1 h2.2 k)
  have hUP : PolyMeas fun ω => (U ω : ℂ) := by
    refine ⟨Complex.measurable_ofReal.comp hUmeas, Um, 0, fun ω => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hU0 ω), pow_zero, mul_one]
    exact hU1 ω
  have hI1 : ∫ ω, (1 + Zf ω) ∂μ = 1 + EZ := by
    rw [integral_add (integrable_const 1) hZi, integral_const, probReal_univ, one_smul]
  -- one graph
  have hone : ∀ g ∈ Qs, ‖∫ ω, (U ω : ℂ) * g.2.valR ⟨Pexp S⟩ (rbmData d P Sig W L z)
      ![a, t, t] ω ∂μ‖ ≤ bB d L W a t * (1 + EZ) + ε₂ := by
    intro g hg
    obtain ⟨u, hu, hallu⟩ := hQq g hg
    set K : ℝ := (8 * l + 32 * l * k * 2 ^ k) * (W : ℝ) ^ (4 * β + β / 10) with hK
    set Bnd : ℝ := 4 * (W : ℝ) ^ (-(3 * (d : ℝ) / 8) + ν') * bB d L W a t with hBnd
    have hB0 : 0 ≤ bB d L W a t := by unfold bB; positivity
    have hK0 : 0 ≤ K := by positivity
    have hBnd0 : 0 ≤ Bnd := by positivity
    have hTp := fun y => CutMoment_T_props P β l z y εp hεp (hpair y)
    set J : Sample (Zd d L) → Zd d L → ℝ := fun ω y => CutMoment_J l W S (green (hmat ω) z) a b y
      with hJ
    have hJ0 : ∀ ω y, 0 ≤ J ω y := fun ω y => (CutMoment_J_le l W (by omega) hW hS0 _ a b y).1
    have hgood : ∀ y ω η, (ω, η) ∉ CutMoment_T P (W := W) β l z y →
        |U ω - U (resampleRow y η ω)| ≤ {ω' | cutY W (green (hmat ω') z) m ≤ (W : ℝ) ^ β}.indicator
          (fun ω' => K * (1 + Zf ω') * J ω' y) ω := by
      intro y ω η hn
      obtain ⟨h1, h2⟩ := (hTp y).2.2 ω η hn
      have h := CutMoment_goodPair (by omega) β hβ l W k hl hW hS0 (green (hmat ω) z)
        (green (hmat (resampleRow y η ω)) z) m a b y h1 h2 δ (hδ y) hδl hδρ (hsmall _ y)
      by_cases hY : cutY W (green (hmat ω) z) m ≤ (W : ℝ) ^ β
      · rw [Set.indicator_of_mem (show ω ∈ {ω' | cutY W (green (hmat ω') z) m ≤ (W : ℝ) ^ β}
          from hY)]
        rw [Set.indicator_of_mem (show green (hmat ω) z ∈ {G₀ : Matrix (Zd d L) (Zd d L) ℂ |
          cutY W G₀ m ≤ (W : ℝ) ^ β} from hY)] at h
        exact h
      · rw [Set.indicator_of_notMem (show ω ∉ {ω' | cutY W (green (hmat ω') z) m ≤ (W : ℝ) ^ β}
          from hY)]
        rw [Set.indicator_of_notMem (show green (hmat ω) z ∉ {G₀ : Matrix (Zd d L) (Zd d L) ℂ |
          cutY W G₀ m ≤ (W : ℝ) ^ β} from hY)] at h
        exact h
    have hBndH : ∀ ω ∈ {ω' | cutY W (green (hmat ω') z) m ≤ (W : ℝ) ^ β},
        ∑ s : Fin g.1 → Zd d L, ‖g.2.coeff.eval (msc z)‖ *
          (g.2.comps.map fun c => ‖Comp.val (gData S z Sig (green (hmat ω) z))
            (Sum.elim ![a, t, t] s) c‖).prod * J ω (Sum.elim ![a, t, t] s u) ≤ Bnd := by
      intro ω hω
      obtain ⟨hr1, hr2⟩ := hrows ω hω g hg
      set A : (Fin g.1 → Zd d L) → ℝ := fun s => ‖g.2.coeff.eval (msc z)‖ *
        (g.2.comps.map fun c => ‖Comp.val (gData S z Sig (green (hmat ω) z))
          (Sum.elim ![a, t, t] s) c‖).prod with hA
      have hA0 : ∀ s, 0 ≤ A s := fun s => mul_nonneg (norm_nonneg _)
        (List.prod_nonneg fun x hx => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hx; positivity)
      have habs : g.2.absVal (gData S z Sig (green (hmat ω) z)) ![a, t, t] = ∑ s, A s := rfl
      by_cases hcl : g.1 = 0 ∨ g.2.DiagRecoll
      · have hJle : ∀ s, J ω (Sum.elim ![a, t, t] s u) ≤ 4 * (W : ℝ) ^ (-((d : ℝ) / 2)) :=
          fun s => (CutMoment_J_le l W (by omega) hW hS0 _ a b _).2
        calc ∑ s, A s * J ω (Sum.elim ![a, t, t] s u)
            ≤ ∑ s, A s * (4 * (W : ℝ) ^ (-((d : ℝ) / 2))) :=
              Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hJle s) (hA0 s)
          _ = 4 * (W : ℝ) ^ (-((d : ℝ) / 2)) * ∑ s, A s := by rw [← Finset.sum_mul]; ring
          _ ≤ 4 * (W : ℝ) ^ (-((d : ℝ) / 2)) * ((W : ℝ) ^ ν' * bB d L W a t) := by
              rw [← habs]; exact mul_le_mul_of_nonneg_left (hr1 hcl) (by positivity)
          _ = 4 * ((W : ℝ) ^ (-((d : ℝ) / 2)) * (W : ℝ) ^ ν') * bB d L W a t := by ring
          _ ≤ Bnd := by rw [hBnd]; gcongr
      · obtain ⟨hnI, hdr⟩ := not_or.1 hcl
        obtain ⟨v, rfl⟩ := hQint g hg hnI hdr u hu
        have hhook : ∀ c, ∑ s, A s * Real.sqrt (bB d L W c (s v)) ≤
            (W : ℝ) ^ (-(3 * (d : ℝ) / 8)) * bB d L W a t := by
          intro c
          refine le_trans (le_of_eq ?_) (hr2 hnI hdr v c)
          unfold Graph.absValHook
          refine Finset.sum_congr rfl fun s _ => ?_
          simp only [hA]
          rw [show (gData S z Sig (green (hmat ω) z)).m = msc z from rfl]
          ring
        set H := (W : ℝ) ^ (-(3 * (d : ℝ) / 8)) * bB d L W a t with hHdef
        have hpair2 : ∀ i : Zd d L × Zd d L,
            ∑ s, A s * CutMoment_h d L W (s v) i ≤ 2 * H := by
          intro i
          unfold CutMoment_h
          have e : ∑ s, A s * (Real.sqrt (bB d L W i.1 (s v)) + Real.sqrt (bB d L W i.2 (s v))) =
              ∑ s, A s * Real.sqrt (bB d L W i.1 (s v)) +
                ∑ s, A s * Real.sqrt (bB d L W i.2 (s v)) := by
            rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
          rw [e]; linarith [hhook i.1, hhook i.2]
        have hw0 := CutMoment_w_nonneg l W hS0 (green (hmat ω) z)
        have hwsum := CutMoment_w_sum l W hS0 (green (hmat ω) z)
        have e : ∑ s, A s * J ω (Sum.elim ![a, t, t] s (Sum.inr v)) =
            ∑ s, A s * CutMoment_h d L W (s v) (a, b) +
              ∑ i, CutMoment_w l W S (green (hmat ω) z) i *
                ∑ s, A s * CutMoment_h d L W (s v) i := by
          simp only [hJ, CutMoment_J, Sum.elim_inr, mul_add, Finset.sum_add_distrib,
            Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
        rw [e]
        have h2 : ∑ i, CutMoment_w l W S (green (hmat ω) z) i *
            ∑ s, A s * CutMoment_h d L W (s v) i ≤ 2 * H := by
          calc ∑ i, CutMoment_w l W S (green (hmat ω) z) i * ∑ s, A s * CutMoment_h d L W (s v) i
              ≤ ∑ i, CutMoment_w l W S (green (hmat ω) z) i * (2 * H) :=
                Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpair2 i) (hw0 i)
            _ = 2 * H := by rw [← Finset.sum_mul, hwsum, one_mul]
        have hH : 4 * H ≤ Bnd := by
          rw [hHdef, hBnd, ← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ hB0
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW ?_) (by norm_num)
          linarith [hν'0]
        linarith [hpair2 (a, b)]
    have hQg := CutMoment_Q P Sig z hz hS hS0 g.2 (hQK g hg) u hu hallu a t U Zf hUmeas
      {ω' | cutY W (green (hmat ω') z) m ≤ (W : ℝ) ^ β} J K Bnd ((W : ℝ) ^ KQ)
      Um hK0 hBnd0 hU0 hU1 hZf0 hZi (fun y => CutMoment_T P (W := W) β l z y)
      (fun y => (hTp y).1) hgood hJ0 hBndH (fun ω => hAp g hg ω)
    refine hQg.trans ?_
    rw [hI1]
    have hKB' : K * Bnd ≤ bB d L W a t := by
      rw [hBnd, hK, ← mul_assoc]
      exact mul_le_of_le_one_left hB0 hKB
    have hsumT : ∑ y, ((gaussLaw S).prod (gaussLaw S)).real (CutMoment_T P (W := W) β l z y) ≤
        Fintype.card (Zd d L) * (2 * εp) := by
      calc ∑ y, ((gaussLaw S).prod (gaussLaw S)).real (CutMoment_T P (W := W) β l z y)
          ≤ ∑ _y : Zd d L, 2 * εp := Finset.sum_le_sum fun y _ => (hTp y).2.1
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hEZ0 : 0 ≤ EZ := integral_nonneg hZf0
    have hUm0 : 0 ≤ Um := (hU0 0).trans (hU1 0)
    have e1 : K * Bnd * (1 + EZ) ≤ bB d L W a t * (1 + EZ) :=
      mul_le_mul_of_nonneg_right hKB' (by linarith)
    have e2 : 2 * Um * (W : ℝ) ^ KQ * ∑ y, ((gaussLaw S).prod (gaussLaw S)).real
        (CutMoment_T P (W := W) β l z y) ≤ ε₂ := by
      rw [hε₂]; gcongr
    linarith
  have hF : ∀ g ∈ Qs, Integrable (fun ω => (U ω : ℂ) * g.2.valR ⟨Pexp S⟩
      (rbmData d P Sig W L z) ![a, t, t] ω) μ := fun g hg =>
    integrable_of_polyMeas S _ (hL.adm_mul _ _ hUP
      (Moment_polyMeas_valR d P Sig W L z hz hS hS0 g.2 (hQK g hg) ![a, t, t]))
  have hlist := QTermOf_list_int μ Qs (fun g ω => (U ω : ℂ) * g.2.valR ⟨Pexp S⟩
    (rbmData d P Sig W L z) ![a, t, t] ω) hF _ hone
  have heq : (fun ω => (U ω : ℂ) * Qs.valR ⟨Pexp S⟩ (rbmData d P Sig W L z) ![a, t, t] ω) =
      fun ω => (Qs.map fun g => (U ω : ℂ) * g.2.valR ⟨Pexp S⟩
        (rbmData d P Sig W L z) ![a, t, t] ω).sum := by
    funext ω
    simp only [Expansion.valR]
    rw [← List.sum_map_mul_left]
  change ‖∫ ω, (U ω : ℂ) * Qs.valR ⟨Pexp S⟩ (rbmData d P Sig W L z) ![a, t, t] ω ∂μ‖ ≤ _
  rw [heq]
  refine hlist.2.trans (le_of_eq ?_)
  rw [hε₂]; ring

end QAll2

/-! ## The terms other than `Q` at one sample -/

/-- The value of a label-free graph is its value without labels. -/
private lemma CutMoment_valR_labelFree {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (h : Γ.LabelFree) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι)
    (ω : Ω) : Γ.valR PF D e ω = Γ.val (D ω) e := by
  have hl : Γ.labels = [] := by
    unfold Graph.labels
    rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
    intro c hc; rw [h c hc]
  have hf : (Γ.comps.filter fun c => c.label.isNone) = Γ.comps :=
    List.filter_eq_self.2 fun c hc => by rw [h c hc]; rfl
  unfold Graph.valR Graph.val Graph.termR Graph.term
  simp only [hl, List.map_nil, List.prod_nil, mul_one, hf]

/-- The graphs of the leading terms and of `Σ_T^{(n)}` are label-free, with the kinds of
[II, Def 3.2]. -/
private lemma CutMoment_lead_props (n : ℕ) :
    ∀ g ∈ leadExp ++ sigmaTExp n, g.2.LabelFree ∧ g.2.TKinds n := by
  have hθ : ∀ o : List ℕ, (∀ l ∈ o, 4 ≤ l ∧ l ≤ n ∧ Even l) →
      (thetaLabelGraph o).LabelFree ∧ (thetaLabelGraph o).TKinds n := by
    intro o ho
    refine ⟨fun c hc => ?_, ?_⟩
    · simp only [thetaLabelGraph, mkC, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> rfl
    · rw [Graph.TKinds, List.all_eq_true]
      intro c hc
      simp only [thetaLabelGraph, mkC, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · simp only [Comp.isTKind, List.isEmpty_nil, Bool.true_and]
        unfold labelOK
        rw [List.all_eq_true]
        intro j hj
        obtain ⟨h1, h2, h3⟩ := ho j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨h1, h2⟩, Nat.even_iff.1 h3⟩
      · rfl
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · simp only [leadExp, List.mem_singleton] at hg
    subst hg
    exact hθ [] (by simp)
  · simp only [sigmaTExp, List.mem_map] at hg
    obtain ⟨o, ho, rfl⟩ := hg
    exact hθ o (Moment_chainLabels_entries n o ho)

/-- **The terms other than `Q` at one sample on the cutoff event**: if every label-free graph of
the leading terms, `Σ_T^{(n)}`, `R`, `A` has `|𝒢^{abs}(G(ω))| ≤ W^ν B_{𝔞t}`, and every graph of
`Err` has `|g(ω)| ≤ 3^{#labels} C_g Σ_S |(Γ'_S)^{abs}(G̃)|` with
`Σ_S |(Γ'_S)^{abs}(G̃)| ≤ W^ν B_{𝔞t}`,
then `|(lead + Σ_T + R + A + Err)(ω)| ≤ c_r W^ν B_{𝔞t}`. -/
private lemma CutMoment_restPt {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (n : ℕ) (𝒯 : TRec)
    (hRA : ∀ g ∈ 𝒯.R ++ 𝒯.A, g.2.LabelFree ∧ g.2.TKinds n) (ω : Sample (Zd d L)) (a t : Zd d L)
    (Gt : Matrix (Zd d L) (Zd d L) ℂ) (X : ℝ)
    (h1 : ∀ g ∈ leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A,
      g.2.absVal (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) ![a, t, t] ≤ X)
    (h2 : ∀ g ∈ 𝒯.Err, ∑ S ∈ g.2.wDLights.pathElig.powerset, (g.2.wDLights.pathRepl S).absVal
      (gData (Smat P.ψ W L) z Sig Gt) ![a, t, t] ≤ X)
    (h3 : ∀ g ∈ 𝒯.Err, ‖g.2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, t, t] ω‖ ≤
      3 ^ g.2.labels.length * (G11.wDConst g.2 * ∑ S ∈ g.2.wDLights.pathElig.powerset,
        (g.2.wDLights.pathRepl S).absVal (gData (Smat P.ψ W L) z Sig Gt) ![a, t, t])) :
    ‖(leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Err).valR ⟨Pexp (Smat P.ψ W L)⟩
        (rbmData d P Sig W L z) ![a, t, t] ω‖ ≤
      (((leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A).length : ℝ) +
        (𝒯.Err.map fun g => (3 : ℝ) ^ g.2.labels.length * G11.wDConst g.2).sum) * X := by
  have hsplit : (leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Err).valR ⟨Pexp (Smat P.ψ W L)⟩
      (rbmData d P Sig W L z) ![a, t, t] ω =
      (leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A).valR ⟨Pexp (Smat P.ψ W L)⟩
        (rbmData d P Sig W L z) ![a, t, t] ω + 𝒯.Err.valR ⟨Pexp (Smat P.ψ W L)⟩
        (rbmData d P Sig W L z) ![a, t, t] ω := by
    simp only [Expansion.valR, List.map_append, List.sum_append]
  rw [hsplit, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Moment_norm_valR_le _ _ _ _ ω).trans ?_
    have hone : ∀ g ∈ leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A,
        ‖g.2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, t, t] ω‖ ≤ X := by
      intro g hg
      have hLT : g.2.LabelFree ∧ g.2.TKinds n := by
        rcases List.mem_append.1 hg with hg | hgA
        · rcases List.mem_append.1 hg with hg | hgR
          · exact CutMoment_lead_props n g hg
          · exact hRA g (List.mem_append_left _ hgR)
        · exact hRA g (List.mem_append_right _ hgA)
      rw [CutMoment_valR_labelFree g.2 hLT.1, Lem512_val_rbm P Sig W L z ω g.2 hLT.2]
      exact (norm_val_le_absVal 3 g.1 _ g.2 _ _).trans (h1 g hg)
    calc ((leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A).map fun g =>
          ‖g.2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, t, t] ω‖).sum
        ≤ ((leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A).map fun _ => X).sum :=
          List.sum_le_sum fun g hg => hone g hg
      _ = _ := by rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
  · refine (Moment_norm_valR_le _ _ _ _ ω).trans ?_
    rw [← List.sum_map_mul_right]
    refine List.sum_le_sum fun g hg => (h3 g hg).trans ?_
    have hC : 0 ≤ (3 : ℝ) ^ g.2.labels.length * G11.wDConst g.2 :=
      mul_nonneg (by positivity) (zero_le_one.trans (G11.one_le_wDConst _))
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 g hg) hC

/-! ## The exceptional samples -/

/-- **The samples whose resampled rows are bad with large probability** (Markov's inequality in
`η`): if `P(B_y) ≤ ε` for every `y`, the samples `ω` with `P_η(B_y(ω)) ≥ t` for some `y` have
probability at most `|ι| ε / t`; adding `{‖ω‖ > W}` costs `|Coord| E|Z|^j / W^j`. -/
private lemma CutMoment_badMeas {ι : Type} [Fintype ι] (S : Matrix ι ι ℝ)
    (hcv : ∀ c, coordVar S c ≤ 1) (B : ι → Set (Sample ι × Sample ι)) (ε t W : ℝ) (hε : 0 ≤ ε)
    (ht : 0 < t) (hW : 0 < W) (j : ℕ)
    (hB : ∀ y, ((gaussLaw S).prod (gaussLaw S)) (B y) ≤ ENNReal.ofReal ε) (A : Set (Sample ι)) :
    gaussLaw S (A ∩ {ω | W < ‖ω‖ ∨ ∃ y, ENNReal.ofReal t ≤
        gaussLaw S (Prod.mk ω ⁻¹' toMeasurable ((gaussLaw S).prod (gaussLaw S)) (B y))}) ≤
      ENNReal.ofReal (Fintype.card (Coord ι) * LabelRemoval.gaussMoment j / W ^ j +
        Fintype.card ι * (ε / t)) := by
  classical
  set μ := gaussLaw S with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw S
  have hsub : A ∩ {ω | W < ‖ω‖ ∨ ∃ y, ENNReal.ofReal t ≤
      μ (Prod.mk ω ⁻¹' toMeasurable (μ.prod μ) (B y))} ⊆
      {ω | W < ‖ω‖} ∪
        ⋃ y, {ω | ENNReal.ofReal t ≤ μ (Prod.mk ω ⁻¹' toMeasurable (μ.prod μ) (B y))} := by
    rintro ω ⟨-, h | ⟨y, hy⟩⟩
    · exact Or.inl h
    · exact Or.inr (Set.mem_iUnion.2 ⟨y, hy⟩)
  have h1 : μ {ω | W < ‖ω‖} ≤ ENNReal.ofReal (Fintype.card (Coord ι) *
      LabelRemoval.gaussMoment j / W ^ j) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (LabelRemoval_norm_tail S hcv W hW j)
  have h2 : ∀ y, μ {ω | ENNReal.ofReal t ≤ μ (Prod.mk ω ⁻¹' toMeasurable (μ.prod μ) (B y))} ≤
      ENNReal.ofReal (ε / t) := by
    intro y
    refine (LabelRemoval_markov μ μ (B y) (ENNReal.ofReal t) (by simpa using ht)
      ENNReal.ofReal_ne_top).trans ?_
    rw [ENNReal.ofReal_div_of_pos ht]
    exact ENNReal.div_le_div_right (hB y) _
  calc μ (A ∩ {ω | W < ‖ω‖ ∨ ∃ y, ENNReal.ofReal t ≤
        μ (Prod.mk ω ⁻¹' toMeasurable (μ.prod μ) (B y))})
      ≤ μ ({ω | W < ‖ω‖} ∪ ⋃ y, {ω | ENNReal.ofReal t ≤
          μ (Prod.mk ω ⁻¹' toMeasurable (μ.prod μ) (B y))}) := measure_mono hsub
    _ ≤ μ {ω | W < ‖ω‖} + ∑ y, μ {ω | ENNReal.ofReal t ≤
          μ (Prod.mk ω ⁻¹' toMeasurable (μ.prod μ) (B y))} :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
    _ ≤ ENNReal.ofReal (Fintype.card (Coord ι) * LabelRemoval.gaussMoment j / W ^ j) +
          ∑ _y : ι, ENNReal.ofReal (ε / t) :=
        add_le_add h1 (Finset.sum_le_sum fun y _ => h2 y)
    _ = _ := by
        have hg : 0 ≤ LabelRemoval.gaussMoment j :=
          integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]

/-! ## One step of the recursion along the filter -/

/-- The exceptional events of one step of the recursion: the four contributions of
`CutMoment_stepPt` beyond the main term are at most `1/4` each. -/
private lemma CutMoment_small (W : ℝ) (hW1 : 1 ≤ W) (KB Kr0 KQ α β : ℝ) (hα : α = β / 10)
    (Dm d c₁ : ℝ) (hc₁ : 0 < c₁) (k r j : ℕ) (gmj gmrj : ℝ) (hgmj0 : 0 ≤ gmj) (hgmrj0 : 0 ≤ gmrj)
    (N NC nQ : ℝ) (hnQ0 : 0 ≤ nQ) (hN0 : 0 ≤ N) (hNC0 : 0 ≤ NC) (hd0 : 0 ≤ d)
    (hN : N ≤ W ^ (d / c₁))
    (hNc : NC ≤ 3 * W ^ (2 * d / c₁))
    (n5 : 64 * 2 ^ k * 2 ^ r * 3 * gmj * W ^ (KB + k * α + Kr0 + r + 2 * d / c₁ - j) ≤ 1)
    (n6 : 64 * 2 ^ k * 2 ^ r * W ^ (KB + k * α + Kr0 + r + d / c₁ - Dm / 2) ≤ 1)
    (n7 : 64 * 2 ^ k * (1 + 3 * (2 ^ (r + j) * (1 + gmrj))) *
      W ^ (KB + k * α + Kr0 + 2 * d / c₁ - j) ≤ 1)
    (n8 : 256 * (nQ + 1) * 2 ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm) ≤ 1) :
    16 * W ^ KB * ((2 * W ^ (β / 10)) ^ k * W ^ Kr0 * ((1 + W) ^ r *
      (NC * gmj / W ^ j + N * W ^ (-(Dm / 2))) + ((1 + W) ^ j)⁻¹ *
        (1 + 2 ^ (r + j) * (1 + gmrj) * NC)) +
      nQ * (2 * (2 * W ^ (β / 10)) ^ k * W ^ KQ * (N * (2 * W ^ (-Dm))))) ≤ 1 := by
  have hW0 : 0 < W := by linarith
  set Um : ℝ := (2 * W ^ (β / 10)) ^ k with hUm
  have hc6 : ∀ x₁ x₂ x₃ x₄ x₅ x₆ : ℝ, W ^ x₁ * W ^ x₂ * W ^ x₃ * W ^ x₄ * W ^ x₅ * W ^ x₆ =
      W ^ (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) := by
    intros; simp only [Real.rpow_add hW0]
  have hc5 : ∀ x₁ x₂ x₃ x₄ x₅ : ℝ, W ^ x₁ * W ^ x₂ * W ^ x₃ * W ^ x₄ * W ^ x₅ =
      W ^ (x₁ + x₂ + x₃ + x₄ + x₅) := by
    intros; simp only [Real.rpow_add hW0]
  have hUmle : Um ≤ 2 ^ k * W ^ (k * α) := by
    rw [hUm, mul_pow, ← Real.rpow_natCast (W ^ (β / 10)), ← Real.rpow_mul hW0.le, hα,
      mul_comm (β / 10)]
  have h1W : (1 + W) ^ r ≤ 2 ^ r * W ^ (r : ℝ) := by
    rw [Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) r
  have hWj : ((1 + W) ^ j)⁻¹ ≤ W ^ (-(j : ℝ)) := by
    rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hW0.le (by linarith) j)
  have hWj' : 1 / W ^ j = W ^ (-(j : ℝ)) := by
    rw [Real.rpow_neg hW0.le, Real.rpow_natCast, one_div]
  have hX : 1 ≤ W ^ (2 * d / c₁) := Real.one_le_rpow hW1 (by positivity)
  have hUm0 : 0 ≤ Um := by positivity
  have hKr : 0 ≤ W ^ Kr0 := by positivity
  set C3 : ℝ := 2 ^ (r + j) * (1 + gmrj) with hC3
  have hC30 : 0 ≤ C3 := by positivity
  have b1 : 16 * W ^ KB * (Um * W ^ Kr0 * ((1 + W) ^ r * (NC * gmj / W ^ j))) ≤ 1 / 4 := by
    calc 16 * W ^ KB * (Um * W ^ Kr0 * ((1 + W) ^ r * (NC * gmj / W ^ j)))
        ≤ 16 * W ^ KB * (2 ^ k * W ^ (k * α) * W ^ Kr0 * (2 ^ r * W ^ (r : ℝ) *
            (3 * W ^ (2 * d / c₁) * gmj * W ^ (-(j : ℝ))))) := by
          rw [div_eq_mul_one_div _ (W ^ j), hWj']
          gcongr
      _ = 16 * 2 ^ k * 2 ^ r * 3 * gmj * (W ^ KB * W ^ (k * α) * W ^ Kr0 * W ^ (r : ℝ) *
            W ^ (2 * d / c₁) * W ^ (-(j : ℝ))) := by ring
      _ = 16 * 2 ^ k * 2 ^ r * 3 * gmj * W ^ (KB + k * α + Kr0 + r + 2 * d / c₁ - j) := by
          rw [hc6]; ring_nf
      _ ≤ 1 / 4 := by linarith
  have b2 : 16 * W ^ KB * (Um * W ^ Kr0 * ((1 + W) ^ r * (N * W ^ (-(Dm / 2))))) ≤ 1 / 4 := by
    calc 16 * W ^ KB * (Um * W ^ Kr0 * ((1 + W) ^ r * (N * W ^ (-(Dm / 2)))))
        ≤ 16 * W ^ KB * (2 ^ k * W ^ (k * α) * W ^ Kr0 * (2 ^ r * W ^ (r : ℝ) *
            (W ^ (d / c₁) * W ^ (-(Dm / 2))))) := by gcongr
      _ = 16 * 2 ^ k * 2 ^ r * (W ^ KB * W ^ (k * α) * W ^ Kr0 * W ^ (r : ℝ) *
            W ^ (d / c₁) * W ^ (-(Dm / 2))) := by ring
      _ = 16 * 2 ^ k * 2 ^ r * W ^ (KB + k * α + Kr0 + r + d / c₁ - Dm / 2) := by
          rw [hc6]; ring_nf
      _ ≤ 1 / 4 := by linarith
  have b3 : 16 * W ^ KB * (Um * W ^ Kr0 * (((1 + W) ^ j)⁻¹ * (1 + C3 * NC))) ≤ 1 / 4 := by
    have hM : 1 + C3 * NC ≤ (1 + 3 * C3) * W ^ (2 * d / c₁) := by
      have := mul_le_mul_of_nonneg_left hNc hC30
      linarith
    calc 16 * W ^ KB * (Um * W ^ Kr0 * (((1 + W) ^ j)⁻¹ * (1 + C3 * NC)))
        ≤ 16 * W ^ KB * (2 ^ k * W ^ (k * α) * W ^ Kr0 * (W ^ (-(j : ℝ)) *
            ((1 + 3 * C3) * W ^ (2 * d / c₁)))) := by gcongr
      _ = 16 * 2 ^ k * (1 + 3 * C3) * (W ^ KB * W ^ (k * α) * W ^ Kr0 *
            W ^ (2 * d / c₁) * W ^ (-(j : ℝ))) := by ring
      _ = 16 * 2 ^ k * (1 + 3 * C3) * W ^ (KB + k * α + Kr0 + 2 * d / c₁ - j) := by
          rw [hc5]; ring_nf
      _ ≤ 1 / 4 := by linarith
  have b4 : 16 * W ^ KB * (nQ * (2 * Um * W ^ KQ * (N * (2 * W ^ (-Dm))))) ≤ 1 / 4 := by
    calc 16 * W ^ KB * (nQ * (2 * Um * W ^ KQ * (N * (2 * W ^ (-Dm)))))
        ≤ 16 * W ^ KB * (nQ * (2 * (2 ^ k * W ^ (k * α)) * W ^ KQ *
            (W ^ (d / c₁) * (2 * W ^ (-Dm))))) := by gcongr
      _ = 64 * nQ * 2 ^ k * (W ^ KB * W ^ (k * α) * W ^ KQ * W ^ (d / c₁) *
            W ^ (-Dm)) := by ring
      _ = 64 * nQ * 2 ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm) := by
          rw [hc5]; ring_nf
      _ ≤ 1 / 4 := by
          have : 64 * nQ * 2 ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm) ≤
              256 * (nQ + 1) * 2 ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm) / 4 := by
            have h0 : 0 ≤ (2 : ℝ) ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm) := by positivity
            have e1 : 64 * nQ * 2 ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm) =
                64 * nQ * ((2 : ℝ) ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm)) := by ring
            have e2 : 256 * (nQ + 1) * 2 ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm) / 4 =
                64 * nQ * ((2 : ℝ) ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm)) +
                  64 * ((2 : ℝ) ^ k * W ^ (KB + k * α + KQ + d / c₁ - Dm)) := by ring
            rw [e1, e2]; linarith
          linarith
  calc 16 * W ^ KB * (Um * W ^ Kr0 * ((1 + W) ^ r *
        (NC * gmj / W ^ j + N * W ^ (-(Dm / 2))) + ((1 + W) ^ j)⁻¹ * (1 + C3 * NC)) +
        nQ * (2 * Um * W ^ KQ * (N * (2 * W ^ (-Dm)))))
      = 16 * W ^ KB * (Um * W ^ Kr0 * ((1 + W) ^ r * (NC * gmj / W ^ j))) +
        16 * W ^ KB * (Um * W ^ Kr0 * ((1 + W) ^ r * (N * W ^ (-(Dm / 2))))) +
        16 * W ^ KB * (Um * W ^ Kr0 * (((1 + W) ^ j)⁻¹ * (1 + C3 * NC))) +
        16 * W ^ KB * (nQ * (2 * Um * W ^ KQ * (N * (2 * W ^ (-Dm))))) := by
        ring
    _ ≤ 1 := by linarith

/-- The event of `cutPairStmt` at row `y`. -/
private def CutMoment_BP {d : ℕ} (P : Profile d) {W L : ℕ} [NeZero L] (β : ℝ) (l : ℕ) (z : ℂ)
    (y : Zd d L) : Set (Sample (Zd d L) × Sample (Zd d L)) :=
  {q | 0 < cutC β (β / 10) l W (Smat P.ψ W L) (green (hmat q.1) z) (msc z) ∧
    ¬ (cutY W (green (hmat (resampleRow y q.2 q.1)) z) (msc z) ≤ (W : ℝ) ^ β ∧
      ∀ a b, |cutX W (Smat P.ψ W L) (green (hmat q.1) z) a b -
          cutX W (Smat P.ψ W L) (green (hmat (resampleRow y q.2 q.1)) z) a b| ≤
        (W : ℝ) ^ (4 * β) * (Real.sqrt (bB d L W a y) + Real.sqrt (bB d L W b y)))}

set_option maxHeartbeats 4000000 in
-- the step collects about twenty eventual statements along the filter
/-- **One step of the recursion**: for `0 < β ≤ min(β₀, d/400)`,
`0 < ν ≤ 1`, `l ≥ 1` and `k`, there is `K` with, eventually along the filter, uniformly in
`z ∈ 𝐃(κ, ε)` and `𝔞, 𝔟`: `E Z_{𝔞𝔟}^{k+1} ≤ K W^{ν/2} (1 + E Z_{𝔞𝔟}^k) + 1`. -/
private lemma CutMoment_stepEv (hPair : cutPairStmt) (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (c₀ c₁ κ ε c₀T : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ)
    (hε : 0 < ε) (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec)
    (hT : IsTExpansion d (smatVar P) Sig n D 𝒯)
    (β₁ : ℝ) (hterms : ∀ ν : ℝ, 0 < ν → ∀ᶠ p in llFilter d n c₀ c₁ c₀T,
      ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ β : ℝ, 0 ≤ β → β ≤ β₁ →
      ∀ G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (p.1.1 : ℝ) ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y)) →
        ∀ a t : Zd d p.1.2,
          (∀ g ∈ leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A,
            g.2.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
              (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t) ∧
          (∀ g ∈ 𝒯.Err, ∑ S ∈ g.2.wDLights.pathElig.powerset, (g.2.wDLights.pathRepl S).absVal
            (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
              (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t) ∧
          (∀ g ∈ 𝒯.Q, (g.1 = 0 ∨ g.2.DiagRecoll) →
            g.2.absVal (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] ≤
              (p.1.1 : ℝ) ^ ν * bB d p.1.2 p.1.1 a t) ∧
          (∀ g ∈ 𝒯.Q, g.1 ≠ 0 → ¬ g.2.DiagRecoll → ∀ (v : Fin g.1) (c : Zd d p.1.2),
            g.2.absValHook (gData (Smat P.ψ p.1.1 p.1.2) z Sig G) ![a, t, t] v
                (fun y => Real.sqrt (bB d p.1.2 p.1.1 c y)) ≤
              (p.1.1 : ℝ) ^ (-(3 * (d : ℝ) / 8)) * bB d p.1.2 p.1.1 a t))
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ β₁) (hβd : β ≤ (d : ℝ) / 400) (ν : ℝ) (hν : 0 < ν)
    (hν1 : ν ≤ 1) (l : ℕ) (hl : 1 ≤ l) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ a b : Zd d p.1.2,
        ∫ ω, cutZ β (β / 10) l p.1.1 (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) z) (msc z) a b ^ (k + 1)
            ∂(rbmLaw d P p) ≤
          K * (p.1.1 : ℝ) ^ (ν / 2) * (1 + ∫ ω, cutZ β (β / 10) l p.1.1 (Smat P.ψ p.1.1 p.1.2)
            (green (hmat ω) z) (msc z) a b ^ k ∂(rbmLaw d P p)) + 1 := by
  obtain ⟨hSE, -, hId, hsh, hShape, hD63⟩ := hT
  obtain ⟨hall, hRs, hAs, hQs, -⟩ := hShape
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set α : ℝ := β / 10 with hα
  set ν' : ℝ := ν / 8 with hν'
  set KB : ℝ := 3 + ((d : ℝ) - 2) / c₁ with hKB
  have hKB0 : 0 ≤ KB := by
    have : (0 : ℝ) ≤ ((d : ℝ) - 2) / c₁ := div_nonneg (by linarith) hc₁.le
    linarith
  -- the graphs
  have hQK : ∀ g ∈ 𝒯.Q, g.2.TKinds n := fun g hg =>
    (hall.1 g (List.mem_append_right _ hg)).2.1
  have hQq : ∀ g ∈ 𝒯.Q, g.2.IsQGraph := fun g hg => (hQs g hg).1
  have hQint : ∀ g ∈ 𝒯.Q, g.1 ≠ 0 → ¬ g.2.DiagRecoll → ∀ u : Atom 3 g.1,
      (∃ c ∈ g.2.comps, c.label = some (.Q, u)) → ∃ v : Fin g.1, u = .inr v := by
    intro g hg hnI hdr u hu
    have h63 := hD63.1.2.2 g hg
    have hext : g.2.ExtClause := (h63.2.2.resolve_left fun h => hnI h.1).1
    have hRt := hD63.2.2.2.2.2.2.1 g (List.mem_append_left _ (List.mem_append_right _ hg)) hnI hdr
    exact QTerm_label_internal g.2 hnI hdr h63.2.1 hext hRt u hu
  have hRA : ∀ g ∈ 𝒯.R ++ 𝒯.A, g.2.LabelFree ∧ g.2.TKinds n := by
    intro g hg
    refine ⟨?_, (hall.1 g (List.mem_append_left _ hg)).2.1⟩
    rcases List.mem_append.1 hg with h | h
    · exact (hRs g h).1
    · exact (hAs g h).1
  have hrestK : ∀ g ∈ leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Err, g.2.TKindsErr n := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hgE
    · rcases List.mem_append.1 hg with hg | hgA
      · rcases List.mem_append.1 hg with hg | hgR
        · exact Graph.tKindsErr_of_tKinds n _ (CutMoment_lead_props n g hg).2
        · exact Graph.tKindsErr_of_tKinds n _ (hRA g (List.mem_append_left _ hgR)).2
      · exact Graph.tKindsErr_of_tKinds n _ (hRA g (List.mem_append_right _ hgA)).2
    · exact (hall.2 g hgE).2.1
  -- a priori bounds, the averaging over `t`, the label removal
  obtain ⟨Kr0, r, hKr0, hrestAp⟩ := CutMoment_apriori_list d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε
    n Sig hSE _ hrestK
  obtain ⟨KQ, hKQ0, hQAp⟩ := CutMoment_absVal_apriori_list d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε
    n Sig hSE 𝒯.Q hQK
  set δS : ℝ := ν * c₁ / 4 with hδS
  obtain ⟨CSB0, hCSB0, hSB⟩ := CutMoment_SB d (by omega) P c₀ c₁ hc₀ δS (by positivity)
  obtain ⟨EhP, hhP⟩ := CutMoment_hP_list d n P c₀ c₁ c₀T hc₁ KB 𝒯.Err
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  -- the exponents
  set E1 : ℝ := KB + k * α + Kr0 + r + KQ + 2 * d / c₁ + 2 with hE1
  have hE1p : 2 ≤ E1 := by
    have : 0 ≤ k * α := by positivity
    have : (0 : ℝ) ≤ 2 * d / c₁ := by positivity
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    linarith
  set j : ℕ := ⌈E1⌉₊ with hj
  have hjE : E1 ≤ j := Nat.le_ceil _
  set Dm : ℝ := max |EhP| (2 * E1) with hDm
  have hDm0 : 0 < Dm := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hpairEv : ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ y : Zd d p.1.2, ((rbmLaw d P p).prod (rbmLaw d P p))
        (CutMoment_BP P (W := p.1.1) β l z y) ≤ ENNReal.ofReal ((p.1.1 : ℝ) ^ (-Dm)) :=
    (hPair d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε β hβ0 (by linarith) l hl Dm hDm0).filter_mono
      inf_le_left
  -- the constants
  set cr : ℝ := (((leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A).length : ℝ) +
    (𝒯.Err.map fun g => (3 : ℝ) ^ g.2.labels.length * G11.wDConst g.2).sum) with hcr
  have hcr0 : 0 ≤ cr := by
    refine add_nonneg (Nat.cast_nonneg _) (List.sum_nonneg fun x hx => ?_)
    obtain ⟨g, _, rfl⟩ := List.mem_map.1 hx
    exact mul_nonneg (by positivity) (zero_le_one.trans (G11.one_le_wDConst _))
  set nQ : ℝ := (𝒯.Q.length : ℝ) with hnQ
  set Klk : ℝ := 8 * l + 32 * l * k * 2 ^ k with hKlk
  set gmj := LabelRemoval.gaussMoment j with hgmj
  set gmrj := LabelRemoval.gaussMoment (r + j) with hgmrj
  have hgmj0 : 0 ≤ gmj := integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hgmrj0 : 0 ≤ gmrj := integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  refine ⟨16 * (CSB0 * 2 ^ δS) * (cr + nQ), by positivity, ?_⟩
  -- the numerical conditions
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  set cl : ℝ := (2 : ℝ) ^ ((1 : ℝ) / l) - 1 with hcl
  have hcl0 : 0 < cl := by
    rw [hcl, sub_pos]; exact Real.one_lt_rpow (by norm_num) (by positivity)
  have N1 := CutMoment_ev_absorb d n c₀ c₁ c₀T (max (8 * l) (2 / cl)) (4 * β - (d : ℝ) / 2) 0
    (by linarith)
  have N2 := CutMoment_ev_absorb d n c₀ c₁ c₀T (128 * l) (4 * β + α - (d : ℝ) / 2) 0
    (by linarith)
  have N3 := CutMoment_ev_absorb d n c₀ c₁ c₀T (4 * Klk) (4 * β + α + (-(3 * (d : ℝ) / 8) + ν')) 0
    (by linarith)
  have N4 := CutMoment_ev_absorb d n c₀ c₁ c₀T 8 (β - (d : ℝ) / 2) 0 (by linarith)
  have N5 := CutMoment_ev_absorb d n c₀ c₁ c₀T (64 * 2 ^ k * 2 ^ r * 3 * gmj)
    (KB + k * α + Kr0 + r + 2 * d / c₁ - j) 0 (by
      have : (0 : ℝ) ≤ KQ := hKQ0; linarith)
  have N6 := CutMoment_ev_absorb d n c₀ c₁ c₀T (64 * 2 ^ k * 2 ^ r)
    (KB + k * α + Kr0 + r + d / c₁ - Dm / 2) 0 (by
      have h1 : 2 * E1 ≤ Dm := le_max_right _ _
      have : (0 : ℝ) ≤ KQ := hKQ0
      have : (0 : ℝ) ≤ d / c₁ := by positivity
      have : (d : ℝ) / c₁ ≤ 2 * d / c₁ := by
        rw [mul_div_assoc]; linarith
      linarith)
  have N7 := CutMoment_ev_absorb d n c₀ c₁ c₀T (64 * 2 ^ k * (1 + 3 * (2 ^ (r + j) * (1 + gmrj))))
    (KB + k * α + Kr0 + 2 * d / c₁ - j) 0 (by
      have : (0 : ℝ) ≤ KQ := hKQ0
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      linarith)
  have N8 := CutMoment_ev_absorb d n c₀ c₁ c₀T (256 * (nQ + 1) * 2 ^ k)
    (KB + k * α + KQ + d / c₁ - Dm) 0 (by
      have h1 : 2 * E1 ≤ Dm := le_max_right _ _
      have : (0 : ℝ) ≤ d / c₁ := by positivity
      have : (d : ℝ) / c₁ ≤ 2 * d / c₁ := by
        rw [mul_div_assoc]; linarith
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      have : 0 ≤ k * α := by positivity
      linarith)
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, Moment_ev_Smat d n P c₀ c₁ c₀T hc₀ hc₁,
    hterms ν' (by positivity), hrestAp, hQAp, hhP Dm (le_trans (le_abs_self _) (le_max_left _ _)),
    hpairEv, CutMoment_ev_W d n c₀ c₁ c₀T (max ((2 : ℝ) ^ d) (max 2 W₂)),
    N1, N2, N3, N4, N5, N6, N7, N8]
    with p hp hSm hterm hrA hqA hhPp hpairp hW n1 n2 n3 n4 n5 n6 n7 n8 z hz a b
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set S := Smat P.ψ p.1.1 p.1.2 with hSdef
  set μ := rbmLaw d P p with hμ
  have hμS : μ = gaussLaw S := rfl
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw S
  set m := msc z with hmdef
  have hW2d : (2 : ℝ) ^ d ≤ W := (le_max_left _ _).trans hW
  have hW2 : (2 : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hWW₂ : W₂ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  rw [Real.rpow_zero] at n1 n2 n3 n4 n5 n6 n7 n8
  have hcv : ∀ c, coordVar S c ≤ 1 := LabelRemoval_coordVar_le _ (hds p.1.1 p.1.2 hp hWW₂)
  obtain ⟨him, himW⟩ := Moment_im_inv (c₀ := c₀) hc₁ hε p hp hW1 z hz
  have hz3 := Lem512Zero_norm_le_three z hz him hκ
  have hm4 : 1 / 4 ≤ ‖m‖ := norm_msc_ge_quarter z him hz3
  have hima : W ^ (-(2 / c₁)) ≤ z.im := by
    rw [Real.rpow_neg hW0.le]
    exact (inv_le_comm₀ him (Real.rpow_pos_of_pos hW0 _)).1 himW
  obtain ⟨hN, hNc⟩ := CutMoment_cards hc₁ d p hp hW1
  -- the bad set
  set Bad : Set (Sample (Zd d p.1.2)) :=
    {ω | 0 < cutC β (β / 10) l p.1.1 S (green (hmat ω) z) m} ∩
      {ω | W < ‖ω‖ ∨ ∃ y, ENNReal.ofReal (W ^ (-(Dm / 2))) ≤
        gaussLaw S (Prod.mk ω ⁻¹' toMeasurable ((gaussLaw S).prod (gaussLaw S))
          (CutMoment_BP P (W := p.1.1) β l z y))} with hBad
  have hBadμ := CutMoment_badMeas S hcv (fun y => CutMoment_BP P (W := p.1.1) β l z y)
    (W ^ (-Dm)) (W ^ (-(Dm / 2))) W (by positivity) (by positivity) hW0 j (hpairp z hz)
    {ω | 0 < cutC β (β / 10) l p.1.1 S (green (hmat ω) z) m}
  have hDmh : W ^ (-Dm) / W ^ (-(Dm / 2)) = W ^ (-(Dm / 2)) := by
    rw [← Real.rpow_sub hW0]; ring_nf
  rw [hDmh] at hBadμ
  -- the entry bounds
  have hsq : ∀ x y : Zd d p.1.2, Real.sqrt (bB d p.1.2 p.1.1 x y) ≤ W ^ (-((d : ℝ) / 2)) :=
    fun x y => CutMoment_sqrtB_le d p.1.2 p.1.1 (by omega) hW1 x y
  have hBlow : ∀ x y : Zd d p.1.2, W ^ (-KB) ≤ bB d p.1.2 p.1.1 x y := fun x y =>
    Moment_bB_lower d (by omega) c₀ c₁ hc₀ hc₁ p hp hW2d x y
  have hWβ : 1 ≤ W ^ β := Real.one_le_rpow hW1 hβ0.le
  have hloB : ∀ x y : Zd d p.1.2, W ^ (-(KB / 2)) ≤ W ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y) := by
    intro x y
    have h1 : W ^ (-(KB / 2)) = Real.sqrt (W ^ (-KB)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]; ring_nf
    rw [h1]
    exact (Real.sqrt_le_sqrt (hBlow x y)).trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) hWβ)
  have h8 : ∀ x : Zd d p.1.2, W ^ β * Real.sqrt (bB d p.1.2 p.1.1 x x) ≤ 1 / 8 := by
    intro x
    have e : W ^ β * W ^ (-((d : ℝ) / 2)) = W ^ (β - (d : ℝ) / 2) := by
      rw [← Real.rpow_add hW0]; ring_nf
    calc W ^ β * Real.sqrt (bB d p.1.2 p.1.1 x x) ≤ W ^ β * W ^ (-((d : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hsq x x) (by positivity)
      _ ≤ 1 / 8 := by rw [e]; linarith
  have hGt : ∀ x y, ‖entryErr (CutMoment_Gt p.1.1 m β) m x y‖ ≤
      W ^ β * Real.sqrt (bB d p.1.2 p.1.1 x y) := fun x y =>
    le_of_eq (CutMoment_Gt_facts p.1.1 m (msc_ne_zero z) β x y).2.2.2
  -- the terms other than `Q`
  have hrest : ∀ ω, 0 < cutC β (β / 10) l p.1.1 S (green (hmat ω) z) m → ω ∉ Bad →
      ∀ t, ‖(leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Err).valR ⟨Pexp S⟩
        (rbmData d P Sig p.1.1 p.1.2 z) ![a, t, t] ω‖ ≤ (cr * W ^ ν') * bB d p.1.2 p.1.1 a t := by
    intro ω hC hnB t
    have hY := ((CutMoment_C β (β / 10) l p.1.1 hW1 S _ m).2.2 hC).1
    have hent := CutMoment_Y_entry p.1.1 hW1 _ m β hY
    have hω : ‖ω‖ ≤ W ∧ ∀ y, gaussLaw S (Prod.mk ω ⁻¹' toMeasurable
        ((gaussLaw S).prod (gaussLaw S)) (CutMoment_BP P (W := p.1.1) β l z y)) <
          ENNReal.ofReal (W ^ (-(Dm / 2))) := by
      by_contra hcon
      apply hnB
      refine ⟨hC, ?_⟩
      by_cases h1 : ‖ω‖ ≤ W
      · right
        push Not at hcon
        obtain ⟨y, hy⟩ := hcon h1
        exact ⟨y, hy⟩
      · left; exact lt_of_not_ge h1
    set T : Set (Sample (Zd d p.1.2)) := ⋃ y, Prod.mk ω ⁻¹' toMeasurable
      ((gaussLaw S).prod (gaussLaw S)) (CutMoment_BP P (W := p.1.1) β l z y) with hT
    have hTm : MeasurableSet T := MeasurableSet.iUnion fun y =>
      measurable_prodMk_left (measurableSet_toMeasurable _ _)
    have hTμ : (gaussLaw S T).toReal ≤ (Fintype.card (Zd d p.1.2) : ℝ) * W ^ (-(Dm / 2)) := by
      have h1 : gaussLaw S T ≤ ∑ _y : Zd d p.1.2, ENNReal.ofReal (W ^ (-(Dm / 2))) :=
        (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun y _ => (hω.2 y).le)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h1
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1
    have hgoodT : ∀ y η, η ∉ T → ∀ x x', ‖entryErr (green (hmat (resampleRow y η ω)) z) m x x'‖ ≤
        W ^ β * Real.sqrt (bB d p.1.2 p.1.1 x x') := by
      intro y η hη
      have hη' : (ω, η) ∉ CutMoment_BP P (W := p.1.1) β l z y := fun h =>
        hη (Set.mem_iUnion.2 ⟨y, subset_toMeasurable _ _ h⟩)
      have hY' : cutY p.1.1 (green (hmat (resampleRow y η ω)) z) m ≤ W ^ β := by
        by_contra hcon
        exact hη' ⟨hC, fun h => hcon h.1⟩
      exact CutMoment_Y_entry p.1.1 hW1 _ m β hY'
    have h3 : ∀ g ∈ 𝒯.Err, ‖g.2.valR ⟨Pexp S⟩ (rbmData d P Sig p.1.1 p.1.2 z) ![a, t, t] ω‖ ≤
        3 ^ g.2.labels.length * (G11.wDConst g.2 * ∑ S' ∈ g.2.wDLights.pathElig.powerset,
          (g.2.wDLights.pathRepl S').absVal (gData S z Sig (CutMoment_Gt p.1.1 m β)) ![a, t, t]) :=
      fun g hg => CutMoment_errPt P Sig g.2 n (hall.2 g hg).2.1 p.1.1 z him hz3 (2 / c₁) hW1 hima β
        h8 (W ^ (-(KB / 2))) (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)) hloB ω hent T hTm hgoodT hcv
        (fun y => hhPp g hg ω y T hω.1 hTμ) a t
    obtain ⟨h1, h2, -, -⟩ := hterm z hz β hβ0.le hβ1 (green (hmat ω) z) hent a t
    obtain ⟨-, h2', -, -⟩ := hterm z hz β hβ0.le hβ1 (CutMoment_Gt p.1.1 m β) hGt a t
    have := CutMoment_restPt P Sig p.1.1 p.1.2 z n 𝒯 hRA ω a t (CutMoment_Gt p.1.1 m β)
      (W ^ ν' * bB d p.1.2 p.1.1 a t) h1 h2' h3
    refine this.trans (le_of_eq ?_)
    rw [hcr]; ring
  -- the graphs of `Q`
  set δ : ℝ := 2 * W ^ (4 * β - (d : ℝ) / 2) with hδdef
  have hWd : W ^ (4 * β) * W ^ (-((d : ℝ) / 2)) = W ^ (4 * β - (d : ℝ) / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hδ : ∀ (y : Zd d p.1.2) i, W ^ (4 * β) * CutMoment_h d p.1.2 p.1.1 y i ≤ δ := by
    intro y i
    have : CutMoment_h d p.1.2 p.1.1 y i ≤ 2 * W ^ (-((d : ℝ) / 2)) := by
      unfold CutMoment_h; linarith [hsq i.1 y, hsq i.2 y]
    calc W ^ (4 * β) * CutMoment_h d p.1.2 p.1.1 y i ≤ W ^ (4 * β) * (2 * W ^ (-((d : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = δ := by rw [hδdef, ← hWd]; ring
  have hmax1 : 8 * l * W ^ (4 * β - (d : ℝ) / 2) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) n1
  have hmax2 : 2 / cl * W ^ (4 * β - (d : ℝ) / 2) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) n1
  have hδρ : 2 * l * δ ≤ 1 / 2 := by rw [hδdef]; nlinarith
  have hδl : (1 + δ) ^ (l - 1) ≤ 2 := by
    have hδc : δ ≤ cl := by
      rw [hδdef]
      have := (div_mul_eq_mul_div 2 cl (W ^ (4 * β - (d : ℝ) / 2)))
      rw [this, div_le_one hcl0] at hmax2
      linarith
    have h1 : 1 + δ ≤ (2 : ℝ) ^ ((1 : ℝ) / l) := by rw [hcl] at hδc; linarith
    have hδ0 : 0 ≤ δ := by positivity
    calc (1 + δ) ^ (l - 1) ≤ (1 + δ) ^ l := pow_le_pow_right₀ (by linarith) (Nat.sub_le l 1)
      _ ≤ ((2 : ℝ) ^ ((1 : ℝ) / l)) ^ l := pow_le_pow_left₀ (by linarith) h1 l
      _ = 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hl0.ne',
            Real.rpow_one]
  have hsmall : ∀ (G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ) y,
      32 * l * W ^ (4 * β + β / 10) * CutMoment_J l p.1.1 S G a b y ≤ 1 := by
    intro G y
    have hJ := CutMoment_J_le l p.1.1 (by omega) hW1 hSm.2.1 G a b y
    have e : W ^ (4 * β + β / 10) * W ^ (-((d : ℝ) / 2)) = W ^ (4 * β + α - (d : ℝ) / 2) := by
      rw [← Real.rpow_add hW0]; congr 1
    calc 32 * l * W ^ (4 * β + β / 10) * CutMoment_J l p.1.1 S G a b y
        ≤ 32 * l * W ^ (4 * β + β / 10) * (4 * W ^ (-((d : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hJ.2 (by positivity)
      _ = 128 * l * (W ^ (4 * β + β / 10) * W ^ (-((d : ℝ) / 2))) := by ring
      _ ≤ 1 := by rw [e]; exact n2
  have hKBq : (8 * l + 32 * l * k * 2 ^ k) * W ^ (4 * β + β / 10) *
      (4 * W ^ (-(3 * (d : ℝ) / 8) + ν')) ≤ 1 := by
    have e : W ^ (4 * β + β / 10) * W ^ (-(3 * (d : ℝ) / 8) + ν') =
        W ^ (4 * β + α + (-(3 * (d : ℝ) / 8) + ν')) := by rw [← Real.rpow_add hW0, hα]
    calc (8 * l + 32 * l * k * 2 ^ k) * W ^ (4 * β + β / 10) * (4 * W ^ (-(3 * (d : ℝ) / 8) + ν'))
        = 4 * Klk * (W ^ (4 * β + β / 10) * W ^ (-(3 * (d : ℝ) / 8) + ν')) := by rw [hKlk]; ring
      _ ≤ 1 := by rw [e]; exact n3
  have hνd : W ^ (-((d : ℝ) / 2)) * W ^ ν' ≤ W ^ (-(3 * (d : ℝ) / 8) + ν') := by
    rw [← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hQb := fun t => CutMoment_QBound P Sig hd z him hSm.1 hSm.2.1 n 𝒯.Q hQK hQq hQint β hβ0.le
    l k hl hW1 a b t ν' KQ (W ^ (-Dm)) δ (by positivity) (by positivity)
    (fun ω hY g hg => by
      obtain ⟨-, -, r3, r4⟩ := hterm z hz β hβ0.le hβ1 (green (hmat ω) z)
        (CutMoment_Y_entry p.1.1 hW1 _ m β hY) a t
      exact ⟨r3 g hg, r4 g hg⟩)
    (fun g hg ω => hqA g hg z hz a t ω) (hpairp z hz) hδ hδl hδρ hsmall hKBq hνd
  -- one step at this size
  set N : ℝ := (Fintype.card (Zd d p.1.2) : ℝ) with hNdef
  set NC : ℝ := (Fintype.card (Coord (Zd d p.1.2)) : ℝ) with hNCdef
  set Um : ℝ := (2 * W ^ (β / 10)) ^ k with hUm
  have hstep := CutMoment_stepPt P Sig z him hSm.1 hSm.2.1 hSm.2.2 hcv n 𝒯 hId hsh hQK β l k hl
    hW1 a b Bad (NC * gmj / W ^ j + N * W ^ (-(Dm / 2))) (cr * W ^ ν') nQ (W ^ Kr0)
    (nQ * (2 * Um * W ^ KQ * (N * (2 * W ^ (-Dm)))))
    (CSB0 * (brk d p.1.2 p.1.1 a b / W) ^ δS) KB r j (by positivity) (by positivity)
    (by positivity) (by positivity) hBadμ hrest (fun ω t => hrA ⟨z, hz⟩ a t ω)
    (fun t => (hQb t).trans (le_of_eq (by rw [hUm]; ring))) (by positivity)
    (hSB p.1.1 p.1.2 hp (by have h : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW1; exact_mod_cast h) a b) hm4
    (hBlow a b)
  refine hstep.trans (add_le_add ?_ ?_)
  · -- the main term
    have hL1 : (1 : ℝ) ≤ p.1.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne p.1.2)
    have hLW : (p.1.2 : ℝ) ≤ W ^ (1 / c₁) := by
      have hL0 : (0 : ℝ) < p.1.2 := by linarith
      calc (p.1.2 : ℝ) = ((p.1.2 : ℝ) ^ c₁) ^ (1 / c₁) := by
            rw [← Real.rpow_mul hL0.le, mul_one_div_cancel hc₁.ne', Real.rpow_one]
        _ ≤ W ^ (1 / c₁) := Real.rpow_le_rpow (by positivity) hp.1 (by positivity)
    have hWL := Moment_W_le_L hc₀ p hp
    have hbrk : brk d p.1.2 p.1.1 a b / W ≤ 2 * W ^ (1 / c₁) := by
      rw [div_le_iff₀ hW0]
      have h1 : (zdistInf d p.1.2 (a - b) : ℝ) ≤ p.1.2 := by
        have := zdistInf_le_half d p.1.2 (a - b)
        have : zdistInf d p.1.2 (a - b) ≤ p.1.2 := this.trans (Nat.div_le_self _ _)
        exact_mod_cast this
      have h2 : brk d p.1.2 p.1.1 a b ≤ 2 * (p.1.2 : ℝ) := by unfold brk; linarith
      have h3 : 2 * (p.1.2 : ℝ) ≤ 2 * W ^ (1 / c₁) * W := by nlinarith
      linarith
    have hbrk0 : 0 ≤ brk d p.1.2 p.1.1 a b / W := by unfold brk; positivity
    have hCSB : (brk d p.1.2 p.1.1 a b / W) ^ δS ≤ 2 ^ δS * W ^ (ν / 4) := by
      calc (brk d p.1.2 p.1.1 a b / W) ^ δS ≤ (2 * W ^ (1 / c₁)) ^ δS :=
            Real.rpow_le_rpow hbrk0 hbrk (by positivity)
        _ = 2 ^ δS * W ^ (ν / 4) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hW0.le, hδS]
            congr 2; field_simp
    have hν'1 : 1 ≤ W ^ ν' := Real.one_le_rpow hW1 (by positivity)
    have hA : cr * W ^ ν' + nQ ≤ (cr + nQ) * W ^ ν' := by
      have : nQ ≤ nQ * W ^ ν' := le_mul_of_one_le_right (by positivity) hν'1
      linarith
    have hWν : W ^ (ν / 4) * W ^ ν' ≤ W ^ (ν / 2) := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by rw [hν']; linarith)
    set EZ := ∫ ω, cutZ β (β / 10) l p.1.1 S (green (hmat ω) z) m a b ^ k ∂(gaussLaw S) with hEZ
    have hEZ0 : 0 ≤ EZ := integral_nonneg fun ω =>
      pow_nonneg (CutMoment_Z β (β / 10) l p.1.1 hl hW1 hSm.2.1 _ m a b).1 k
    calc 16 * (CSB0 * (brk d p.1.2 p.1.1 a b / W) ^ δS) * (cr * W ^ ν' + nQ) * (1 + EZ)
        ≤ 16 * (CSB0 * (2 ^ δS * W ^ (ν / 4))) * ((cr + nQ) * W ^ ν') * (1 + EZ) := by
          gcongr
      _ = 16 * (CSB0 * 2 ^ δS) * (cr + nQ) * (W ^ (ν / 4) * W ^ ν') * (1 + EZ) := by ring
      _ ≤ 16 * (CSB0 * 2 ^ δS) * (cr + nQ) * W ^ (ν / 2) * (1 + EZ) := by gcongr
  · -- the exceptional events
    exact CutMoment_small W hW1 KB Kr0 KQ α β rfl Dm (d : ℝ) c₁ hc₁ k r j gmj gmrj hgmj0 hgmrj0 N
      NC
      nQ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity) hN hNc n5 n6 n7
      n8

/-! ## The cutoff moment bound -/

/-- **The cutoff moment bound**: from the hook graph sum (`hookGraphSumStmt`),
the improvement on the cutoff event (`cutImproveStmt`, not read by the proof) and the pair event
(`cutPairStmt`), for an `n`-th order `T`-expansion with `D`-th order error, `D ≥ n + 4`, with the
clauses `TRec.Def63G11`: there is `β₀ > 0` such that for `0 < β ≤ β₀`, `α = β/10`, every `ν > 0`
and `l, q ≥ 1`, eventually along `llFilter`, `E Z_{𝔞𝔟}(z)^q ≤ W^{qν}` uniformly in
`z ∈ 𝐃(κ, ε)` and `𝔞, 𝔟`. The proof is the recursion `E Z^{k+1} ≤ K W^{ν/2} (1 + E Z^k) + 1`
in `k`, with `β₀ = min(β_g, d/400)` and `β_g` from `Moment_cutTerms`. -/
theorem cutMoment_of : hookGraphSumStmt → cutImproveStmt → cutPairStmt → cutMomentStmt := by
  intro hH _ hPair d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T n D Sig 𝒯 hnD hT hG
  by_cases hn : n ≤ 1
  · refine ⟨1, one_pos, fun β _ _ ν _ l q _ _ => ?_⟩
    filter_upwards [Moment_small_n d n c₀ c₁ c₀T hc₀ hc₀T hn] with p hp
    exact hp.elim
  obtain ⟨β₁, hβ₁, hterms⟩ := Moment_cutTerms hH d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T n D
    Sig 𝒯 (by omega) hT hG
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨min β₁ ((d : ℝ) / 400), lt_min hβ₁ (by positivity),
    fun β hβ hββ ν hν l q hl hq => ?_⟩
  have hβ1 : β ≤ β₁ := hββ.trans (min_le_left _ _)
  have hβd : β ≤ (d : ℝ) / 400 := hββ.trans (min_le_right _ _)
  set ν₁ : ℝ := min ν 1 with hν₁
  have hν₁0 : 0 < ν₁ := lt_min hν one_pos
  have hrec : ∀ k : ℕ, ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ a b : Zd d p.1.2,
        ∫ ω, cutZ β (β / 10) l p.1.1 (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) z) (msc z) a b ^ k
            ∂(rbmLaw d P p) ≤ (p.1.1 : ℝ) ^ ((k : ℝ) * ν₁) := by
    intro k
    induction k with
    | zero =>
      refine Eventually.of_forall fun p z _ a b => ?_
      have : IsProbabilityMeasure (rbmLaw d P p) := isProbabilityMeasure_gaussLaw _
      simp
    | succ k ih =>
      obtain ⟨K, hK0, hstep⟩ := CutMoment_stepEv hPair d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε n D
        Sig 𝒯 hT β₁ hterms β hβ hβ1 hβd ν₁ hν₁0 (min_le_right _ _) l hl k
      filter_upwards [ih, hstep, CutMoment_ev_rpow d n c₀ c₁ c₀T (2 * K + 1) (ν₁ / 2)
        (by positivity), CutMoment_ev_W d n c₀ c₁ c₀T 1] with p hih hst hWK hW z hz a b
      set W : ℝ := (p.1.1 : ℝ) with hWdef
      have hW0 : 0 < W := by linarith
      have h1 := hst z hz a b
      have h2 := hih z hz a b
      have hk1 : 1 ≤ W ^ ((k : ℝ) * ν₁) := Real.one_le_rpow hW (by positivity)
      have hν2 : 1 ≤ W ^ (ν₁ / 2) := Real.one_le_rpow hW (by positivity)
      have e : W ^ (((k + 1 : ℕ) : ℝ) * ν₁) = W ^ (ν₁ / 2) * W ^ (ν₁ / 2) * W ^ ((k : ℝ) * ν₁) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; push_cast; ring_nf
      rw [e]
      calc _ ≤ K * W ^ (ν₁ / 2) * (1 + W ^ ((k : ℝ) * ν₁)) + 1 := by
            refine h1.trans ?_
            gcongr
        _ ≤ K * W ^ (ν₁ / 2) * (2 * W ^ ((k : ℝ) * ν₁)) +
              W ^ (ν₁ / 2) * W ^ ((k : ℝ) * ν₁) := by
            gcongr
            · linarith
            · nlinarith
        _ = (2 * K + 1) * W ^ (ν₁ / 2) * W ^ ((k : ℝ) * ν₁) := by ring
        _ ≤ W ^ (ν₁ / 2) * W ^ (ν₁ / 2) * W ^ ((k : ℝ) * ν₁) := by gcongr
  filter_upwards [hrec q, CutMoment_ev_W d n c₀ c₁ c₀T 1] with p hp hW z hz a b
  refine (hp z hz a b).trans (Real.rpow_le_rpow_of_exponent_le hW ?_)
  exact mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _)

end RBM8D
