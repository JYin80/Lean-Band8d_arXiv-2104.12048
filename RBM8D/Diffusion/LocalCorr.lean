module

public import Batteries.Tactic.OpenPrivate
public import RBM8D.Diffusion.ErrMain
public import RBM8D.Diffusion.DiagMean
public import RBM8D.Diffusion.Singular
public import RBM8D.Diffusion.ModelSymm
public import RBM8D.SelfEnergy.Entrywise
public import RBM8D.SelfEnergy.MainCancel
public import RBM8D.Diffusion.ErrBound
public import RBM8D.Bound.Doubly
public import RBM8D.LocalLaw.Moment
import all RBM8D.Diffusion.ErrBound
import all RBM8D.Diffusion.Singular
import all RBM8D.Bound.Doubly
import all RBM8D.SelfEnergy.MainCancel
import all RBM8D.LocalLaw.Moment
import all RBM8D.Diffusion.ErrMain
import all RBM8D.Diffusion.DiagMean

@[expose] public section

/-!
# The local correction: [I, (1.28)]

`localCorr : localCorrStmt`: under the local law [I, Theorem 1.4], for an `n`-th order
`T`-equation `𝒬` with error order `D ≥ n + 2`, `n ≥ 4`, and self-energies `Σ_4, …, Σ_n`, the local
correction `𝒢_{x𝔟}` of [I, (8.16)] (`corrMat`) satisfies `|𝒢_{x𝔟}| ≤ L^τ B_{x𝔟}^{3/2}` for
`L ≥ L₀` along `adm(c₀, c₁)` and `z ∈ 𝐃(κ, ε)`.

* **Off the diagonal** (`x ≠ 𝔟`) only the graphs of `R` and the graphs of `A` in which `⊕`, `⊖` lie
  in one dotted block contribute. Each of them is doubly connected, of diagonal scaling order
  `n_𝔟 ≥ 3`, and either has no internal atom or is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` (for `R`
  by the recollision dot, for `A` by the clause on the external atoms, [II, Lemma 6.5 (4)]). With
  the root atom internal and undotted, `𝔟` then lies in an internal molecule and [I, (6.20)] gives
  `𝒢^{abs}_{x, 𝔟𝔟} ≤ W^τ W^{−(n_𝔟 − 3)d/2} B_{x𝔟}^{3/2}`; with the root atom external or dotted the
  graph carries the factor `1_{x = 𝔟}` ([I, (8.20)]). The expectation step of [II, Claims 8.6,
  8.7] turns these deterministic bounds into bounds of `E|𝒢_{x, 𝔟𝔟}|`.
* **On the diagonal** the whole entry is bounded at once. The identity `|G_{𝔟𝔟}|² − T_{𝔟,𝔟𝔟} =
  Y'_{𝔟𝔟} + (Σ̃^{(n)} T)_{𝔟,𝔟𝔟}` (`singularIdStmt`, valid at a singular `S`) and `E Q = 0` give
  `𝒢_{𝔟𝔟} = (E|G_{𝔟𝔟}|² − |m|² − E T_{𝔟,𝔟𝔟}) − Σ_y Σ̃^{(n)}_{𝔟y} E T_{y,𝔟𝔟} −
  E(Γ_A + Γ_Err)_{𝔟,𝔟𝔟}`.
  Write `Δ_x = G_{xx} − m`. The Gaussian integration by parts with the test function `Δ̄_𝔟` gives
  `E|G_{𝔟𝔟}|² − |m|² − E T_{𝔟,𝔟𝔟} = m̄ E Δ_𝔟 + m E Δ̄_𝔟 + Σ_k s_{𝔟k} (m² C̃_{k𝔟} + m E Z_{k𝔟})` with
  `C̃_{k𝔟} = E[Δ_k Δ̄_𝔟]`, `Z_{k𝔟} = Δ_k |Δ_𝔟|² + |G_{k𝔟}|² Δ̄_𝔟`, and
  `(1 − m² S) C̃_{·𝔟} = m F̃_{·𝔟}` with
  `F̃_{k𝔟} = Σ_j s_{kj} E[Δ_j Δ_k Δ̄_𝔟 + G_{jk} Ḡ_{𝔟k} Ḡ_{j𝔟}]`.
  With `(1 − m² S)⁻¹ = 1 + S^+` ([I, Lemma 2.2]), `|E Δ_𝔟| ≤ W^τ W^{−3d/2}` (`diagMeanStmt`),
  the local law, [I, (1.26)] for `Σ_l` (`G13.entrywise`) and [I, (8.17)] (`errBoundStmt`), every
  term is at most `W^τ W^{−3d/2} = W^τ B_{𝔟𝔟}^{3/2}`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

open private rootRest_eq isTKind_map from RBM8D.Diffusion.ErrBound
open private gm_empty tGraph_val graphVal_det chain_congr from RBM8D.Diffusion.Singular
open private bB_pos₁ im_pos_of_specDom from RBM8D.Bound.Doubly
open private MainCancel_valR_integrable_err MainCancel_sigMat_congr
  MainCancel_selfEnergiesUpTo_congr from RBM8D.SelfEnergy.MainCancel
open private Moment_diagRecoll_of_recoll Moment_diagRecoll_of_pmBlock Moment_bB_lower
  from RBM8D.LocalLaw.Moment
open private ErrMain_AbsBd ErrMain_absVal_gB2 ErrMain_absVal_pin_eq_zero ErrMain_formB1Abs
  ErrMain_transfer ErrMain_caseB_of_block ErrMain_rootRest_tKindsErr ErrMain_L₀ ErrMain_normInt
  ErrMain_sumBound from RBM8D.Diffusion.ErrMain
open private tf_G tf_mul tf_const tf_add tf_sub tf_D integ ibp norm_integral_le_good norm_mul3_le
  norm_wsum_le solve isUnit_one_sub one_add_mul_one_sub splusBound_le_two splusBound_rowSum
  final_ineq from RBM8D.Diffusion.DiagMean

open ErrForms

/-! ## Off the diagonal: one graph of `R` or of the `⊕⊖`-block graphs of `A` -/

section OffDiag

variable {n : ℕ}

/-- **The strong form of the second form of [I, (8.20)]** ([I, (6.20)], root atom internal and
undotted, `𝔟` in an internal molecule): `𝒢^{abs}_{x, 𝔟𝔟} ≤ W^τ W^{−(effOrd g − 3)d/2} B_{x𝔟}^{3/2}`
under the entry hypothesis `|G_{pq} − δ_{pq} m| ≤ W^{τ'} B^{1/2}_{pq}`. -/
private theorem LocalCorr_formB2 :
    ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
      ∀ {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v : Fin n) (C : ℕ),
        Rooted g j (.inr v) → g.Normal C → g.DoublyConnected → g.TKinds N →
        dotB g v = false → CaseB g →
        ∀ τ : ℝ, 0 < τ → ErrMain_AbsBd d P c₀ c₁ κ ε Sig g fun W L _ x b =>
              (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 3) * d / 2)) *
                bB d L W x b ^ ((3 : ℝ) / 2) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n g j v C hR hN hDC hT hv hB τ hτ
  have hdot := hN.1.noIntDot
  by_cases hZ : ∀ c ∈ g.comps, (nd c && !atT c) = true → c.kind = .xdot →
      pinAtom 1 (pB g (.inr v) (1 : Fin 2) 0) c.x ≠ pinAtom 1 (pB g (.inr v) (1 : Fin 2) 0) c.y
  swap
  · push Not at hZ
    obtain ⟨c, hc, hq, hk, he⟩ := hZ
    refine ⟨1, one_pos, 1, fun W L _ hadm hW z hz G hG x b => ?_⟩
    beta_reduce
    rw [ErrMain_absVal_gB2 hR hdot hv, gB2, ErrMain_absVal_pin_eq_zero g nd 1 _ ⟨c, hc, hq, hk, he⟩]
    have hW1 : 1 ≤ W := by exact_mod_cast (show (1 : ℝ) ≤ W from hW)
    have := bB_pos₁ (d := d) (L := L) hW1 x b
    positivity
  obtain ⟨C', hNo⟩ := normal_gB2 hR hN hDC hv hB hZ
  have hDC2 := dc_gB2 hR hN hDC hv hB
  have hT2 := tKinds_pin hT nd 1 (pB g (.inr v) (1 : Fin 2) 0)
  have ho := ord_gB2 hR hv
  obtain ⟨W₁, hW₁⟩ := dcStrong d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig _ C'
    (gB2 g (.inr v)) hNo hDC2 hT2 (τ / 2) (by positivity)
  set o : ℝ := ((gB2 g (.inr v)).ord : ℝ) - 2 with hodef
  set τ' := min 1 (τ / (2 * (|o| + 1))) with hτ'
  have hτ'0 : 0 < τ' := lt_min one_pos (by positivity)
  refine ⟨τ', hτ'0, max W₁ 1, fun W L _ hadm hW z hz G hG x b => ?_⟩
  beta_reduce
  have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ1 : 1 ≤ (W : ℝ) ^ τ' := Real.one_le_rpow hW1 hτ'0.le
  have hΛW : (W : ℝ) ^ τ' ≤ (W : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hW1 ((min_le_left _ _).trans (by linarith))
  have hs := strong_of_entry hW1n G z (by linarith) hG
  have hdc := hW₁ W L hadm ((le_max_left _ _).trans hW) z hz G _ hΛ1 hΛW hs x b
  rw [ErrMain_absVal_gB2 hR hdot hv]
  refine hdc.trans ?_
  have hΛo : ((W : ℝ) ^ τ') ^ o ≤ (W : ℝ) ^ (τ / 2) := rpow_rpow_le hW1 (tau_mul_le hτ)
  rw [ho]
  have e1 : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hB0 : 0 ≤ bB d L W x b ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (bB_pos₁ hW1n x b).le _
  calc (W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ τ') ^ o * (W : ℝ) ^ (-(((effOrd g : ℝ) - 3) * d / 2)) *
        bB d L W x b ^ ((3 : ℝ) / 2)
      ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((effOrd g : ℝ) - 3) * d / 2)) *
          bB d L W x b ^ ((3 : ℝ) / 2) := by gcongr
    _ = _ := by rw [e1]

/-- **The forms of [I, (8.20)] for a graph whose `𝔟` lies in an internal molecule** (or without
internal atom): `𝒢^{abs}_{x, 𝔟𝔟} ≤ W^τ W^{−(e − 3)d/2} B_{x𝔟}^{3/2} + 1_{x = 𝔟} W^τ W^{−(e − 2)d/2}`
with `e = effOrd g`, under the entry hypothesis `|G_{pq} − δ_{pq} m| ≤ W^{τ'} B^{1/2}_{pq}`. -/
private theorem LocalCorr_formKey :
    ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
      ∀ {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v : Atom 3 n) (C : ℕ),
        Rooted g j v → g.Normal C → g.DoublyConnected → g.TKinds N → (CaseB g ∨ n = 0) →
        ∀ τ : ℝ, 0 < τ → ErrMain_AbsBd d P c₀ c₁ κ ε Sig g fun W L _ x b =>
              (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 3) * d / 2)) *
                bB d L W x b ^ ((3 : ℝ) / 2) + (if x = b then 1 else 0) *
                ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 2) * d / 2))) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n g j v C hR hN hDC hT hB τ hτ
  have hpos : ∀ (W L : ℕ) [NeZero L], (1 : ℝ) ≤ W → ∀ x b : Zd d L,
      0 ≤ (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 3) * d / 2)) *
        bB d L W x b ^ ((3 : ℝ) / 2) := by
    intro W L _ hW x b
    have hW1n : 1 ≤ W := by exact_mod_cast hW
    have := Real.rpow_nonneg (bB_pos₁ (d := d) (L := L) hW1n x b).le ((3 : ℝ) / 2)
    positivity
  rcases v with a | i
  · obtain ⟨τ', hτ', W₀, h⟩ := ErrMain_formB1Abs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g j _
      C hR hN hDC hT (fun i h => by cases h) hB τ hτ
    refine ⟨τ', hτ', max W₀ 1, fun W L _ hadm hW z hz G hG x b => ?_⟩
    exact (h W L hadm ((le_max_left _ _).trans hW) z hz G hG x b).trans
      (le_add_of_nonneg_left (hpos W L ((le_max_right _ _).trans hW) x b))
  · have hB' : CaseB g := hB.resolve_right fun h0 => by subst h0; exact i.elim0
    by_cases hdi : dotB g i = true
    · obtain ⟨τ', hτ', W₀, h⟩ := ErrMain_formB1Abs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig
        g j _ C hR hN hDC hT (fun i' h => by cases h; exact hdi) (Or.inl hB') τ hτ
      refine ⟨τ', hτ', max W₀ 1, fun W L _ hadm hW z hz G hG x b => ?_⟩
      exact (h W L hadm ((le_max_left _ _).trans hW) z hz G hG x b).trans
        (le_add_of_nonneg_left (hpos W L ((le_max_right _ _).trans hW) x b))
    · obtain ⟨τ', hτ', W₀, h⟩ := LocalCorr_formB2 d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig
        g j i C hR hN hDC hT (by simpa using hdi) hB' τ hτ
      exact ⟨τ', hτ', W₀, fun W L _ hadm hW z hz G hG x b =>
        (h W L hadm hW z hz G hG x b).trans (le_add_of_nonneg_right (by positivity))⟩

/-- A `⊕`-recollision graph at `𝔟₁ = 𝔟₂` with a root edge has `𝔟` in an internal molecule: some
dotted edge joins `⊕` or `⊖` to an internal atom (`ErrForms.CaseB`). -/
private theorem LocalCorr_caseB {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v) (hD : g.DiagRecoll) : CaseB g := by
  have hT : ∀ c ∈ g.comps, c.kind = .dot → c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
    intro c hc hk
    have := atT_eq_false hR hc (by rw [hk]; simp)
    simp only [atT, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at this
    exact this
  simp only [Graph.DiagRecoll, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    List.contains_iff_mem] at hD
  obtain ⟨B, hB, he, u, hu, hr⟩ := hD
  rcases u with a | b
  · simp at hr
  rcases he with he | he
  · exact ErrMain_caseB_of_block hT (Or.inl rfl)
      ((g.sameBlock_iff_mem_dotBlocks _ _).2 ⟨B, hB, he, hu⟩)
  · exact ErrMain_caseB_of_block hT (Or.inr rfl)
      ((g.sameBlock_iff_mem_dotBlocks _ _).2 ⟨B, hB, he, hu⟩)

/-- **One graph of the local correction** ([I, (1.28)] for one graph, via [I, (8.20)], (6.20) and
[II, Claims 8.6, 8.7]): for a graph `g` of the form [II, Def 3.3 (4)], normal regular, with the
kinds of `Err` with labels in `[4, N]`, [II, Def 3.2 (9)], doubly connected, with only diffusive
components at `⊗`, dotted edges forming a forest, which is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`
when it has an internal atom, and of diagonal scaling order `n_𝔟 ≥ 3`: under the local law there is
`K ≥ 0` such that for all `τ, D' > 0`, for `L ≥ L₀` along `adm(c₀, c₁)`,
`E|𝒢_{x, 𝔟𝔟}| ≤ K W^τ (B_{x𝔟}^{3/2} + 1_{x = 𝔟} W^{−d/2}) + W^{−D'}`. -/
private theorem LocalCorr_graph (hLL : LocalLawStmt) {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    {N : ℕ} {Sig : ℕ → Expansion 2} (hSE : SelfEnergiesUpTo d (smatVar P) Sig N)
    (g : Graph 3 n) (hTR : g.ThetaRooted) {C : ℕ} (hN : g.Normal C) (hK : g.TKindsErr N)
    (hAE : g.AtExternals) (hDC : g.DoublyConnected) (hTD : g.TensorDiffusive)
    (hDA : g.DotsAcyclic) (hDR : n ≠ 0 → g.DiagRecoll) (he : (3 : ℤ) ≤ g.diagOrd) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ x b : Zd d L,
          ∫ ω, ‖(rootRest g).2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![x, b, b] ω‖
              ∂(rbmLaw d P (sizeOf W L)) ≤
            K * ((W : ℝ) ^ τ * (bB d L W x b ^ ((3 : ℝ) / 2) +
              (if x = b then 1 else 0) * (W : ℝ) ^ (-((d : ℝ) / 2)))) + (W : ℝ) ^ (-D') := by
  obtain ⟨j, v, hv, hk, -, hlab, hxy, hrest, -⟩ := hTR
  set Γ := (rootRest g).2 with hΓ
  have hΓK : Γ.TKindsErr N :=
    ErrMain_rootRest_tKindsErr g j v hk hxy (fun c hc => (hrest c hc).1) hK
  obtain ⟨hGN, hGT, hGAE, hGDC, hGTD, hGDA, hGDR, -, -, hGdiag⟩ :=
    G11.wDLights_props g N C hK hN hAE hDC hTD hDA
  have hGRE' : n ≠ 0 → ¬ g.wDLights.DiagRecoll → g.wDLights.RootedAtExt :=
    fun h0 h1 => absurd (hGDR.2 (hDR h0)) h1
  set F : ∀ W L : ℕ, Zd d L → Zd d L → ℝ := fun W L x b =>
    bB d L W x b ^ ((3 : ℝ) / 2) + (if x = b then 1 else 0) * (W : ℝ) ^ (-((d : ℝ) / 2)) with hF
  refine ⟨(Γ.wDLights.pathElig.powerset.card : ℝ), by positivity, fun τ hτ D' hD' => ?_⟩
  -- the label-free graphs `Γ_S`, one at a time
  have hS : ∀ S ∈ Γ.wDLights.pathElig.powerset, ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, 1 ≤ W₀ ∧
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
          (∀ p q, ‖entryErr G (msc z) p q‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W p q)) →
          ∀ x b : Zd d L, (Γ.wDLights.pathRepl S).absVal (gData (Smat P.ψ W L) z Sig G)
            ![x, b, b] ≤ (W : ℝ) ^ (τ / 2) * F W L x b := by
    intro S hSm
    obtain ⟨S', hS', j', hR', habs⟩ := ErrMain_transfer g j v hv hk hlab hxy
      (fun c hc => ⟨(hrest c hc).1, (hrest c hc).2.1, (hrest c hc).2.2.1, (hrest c hc).2.2.2⟩) S
      (Finset.mem_powerset.1 hSm)
    obtain ⟨⟨C', hN'⟩, hT', -, hDC', -, hDA', -, -, hDR', -, -, hdiag'⟩ :=
      labelPaths n _ N g.wDLights hGN hGT hGAE hGDC hGTD hGDA hGRE' S' hS'
    have hB : CaseB (g.wDLights.pathRepl S') ∨ n = 0 := by
      rcases Nat.eq_zero_or_pos n with h0 | hn
      · exact Or.inr h0
      · exact Or.inl (LocalCorr_caseB hR' (hDR'.2 (hGDR.2 (hDR hn.ne'))))
    obtain ⟨τ', hτ', W₁, hW₁⟩ := LocalCorr_formKey d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE
      _ j' v C' hR' hN' hDC' hT' hB (τ / 2) (by positivity)
    have heff : (3 : ℤ) ≤ effOrd (g.wDLights.pathRepl S') := by
      have h1 := diagOrd_le_effOrd hR' ((Graph.dotsAcyclic_iff_dotExcess_eq_zero _).1 hDA')
      have h2 : (0 : ℤ) ≤ (S'.card : ℤ) := by positivity
      linarith
    have heff' : (3 : ℝ) ≤ (effOrd (g.wDLights.pathRepl S') : ℝ) := by exact_mod_cast heff
    refine ⟨τ', hτ', max W₁ 1, le_max_right _ _, fun W L _ hadm hW z hz G hG x b => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [habs]
    refine (hW₁ W L hadm ((le_max_left _ _).trans hW) z hz G hG x b).trans ?_
    simp only [hF]
    have e1 : (W : ℝ) ^ (-(((effOrd (g.wDLights.pathRepl S') : ℝ) - 3) * d / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hW1 (by nlinarith)
    have e2 : (W : ℝ) ^ (-(((effOrd (g.wDLights.pathRepl S') : ℝ) - 2) * d / 2)) ≤
        (W : ℝ) ^ (-((d : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
    have hi0 : (0 : ℝ) ≤ if x = b then 1 else 0 := by split_ifs <;> norm_num
    have hτ0 : (0 : ℝ) ≤ (W : ℝ) ^ (τ / 2) := by positivity
    have hW1n : 1 ≤ W := by exact_mod_cast hW1
    have hB0 : 0 ≤ bB d L W x b ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (bB_pos₁ hW1n x b).le _
    calc (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((effOrd (g.wDLights.pathRepl S') : ℝ) - 3) * d / 2)) *
          bB d L W x b ^ ((3 : ℝ) / 2) + (if x = b then 1 else 0) * ((W : ℝ) ^ (τ / 2) *
          (W : ℝ) ^ (-(((effOrd (g.wDLights.pathRepl S') : ℝ) - 2) * d / 2)))
        ≤ (W : ℝ) ^ (τ / 2) * 1 * bB d L W x b ^ ((3 : ℝ) / 2) +
          (if x = b then 1 else 0) * ((W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-((d : ℝ) / 2))) := by
          gcongr
      _ = _ := by ring
  choose! τf hτf W₀f hW₀f hbd using hS
  have hne : (Γ.wDLights.pathElig.powerset).Nonempty := ⟨∅, Finset.empty_mem_powerset _⟩
  set τ' := (Γ.wDLights.pathElig.powerset).inf' hne τf with hτ'def
  have hτ' : 0 < τ' := (Finset.lt_inf'_iff hne).2 fun S hS => hτf S hS
  set W₀ := (Γ.wDLights.pathElig.powerset).sup' hne W₀f with hW₀def
  have hβ : ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ (a b : Zd d L) (G : Matrix (Zd d L) (Zd d L) ℂ),
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) →
        ∑ S ∈ Γ.wDLights.pathElig.powerset, (Γ.wDLights.pathRepl S).absVal
          (gData (Smat P.ψ W L) z Sig G) ![a, b, b] ≤
          (Γ.wDLights.pathElig.powerset.card : ℝ) * ((W : ℝ) ^ (τ / 2) * F W L a b) := by
    refine ⟨W₀, fun W L _ hadm hW z hz x b G hG => ?_⟩
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun S hSm => ?_
    have hW1 : (1 : ℝ) ≤ W := (hW₀f S hSm).trans ((Finset.le_sup' W₀f hSm).trans hW)
    refine hbd S hSm W L hadm ((Finset.le_sup' W₀f hSm).trans hW) z hz G (fun p q => ?_) x b
    refine (hG p q).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    exact Real.rpow_le_rpow_of_exponent_le hW1 (Finset.inf'_le τf hSm)
  obtain ⟨L₀, hL₀⟩ := ErrExp.expBound hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE _ Γ hΓK τ' hτ'
    (fun W L _ x b => (Γ.wDLights.pathElig.powerset.card : ℝ) * ((W : ℝ) ^ (τ / 2) * F W L x b))
    hβ (τ / 2) (by positivity) D' hD'
  refine ⟨L₀, fun W L _ hL hadm z hz x b => (hL₀ W L hL hadm z hz x b).trans (le_of_eq ?_)⟩
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add' hW0 (by positivity)]; ring_nf
  rw [← this]
  ring

end OffDiag

/-! ## Off the diagonal: the sum over the graphs -/

section OffDiagSum

/-- The graph facts of the graphs of `R` and of the graphs of `A` in which `⊕`, `⊖` lie in one
dotted block ([II, Def 3.2], [II, Def 3.3 (4)], [II, Def 6.3]): normal regular, with the kinds of
[II, Def 3.2], doubly connected, only diffusive components at `⊗`, dotted edges forming a forest; a
`⊕`-recollision graph at `𝔟₁ = 𝔟₂` when there is an internal atom; diagonal scaling order
`n_𝔟 ≥ 3`. -/
private theorem LocalCorr_facts {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec}
    (hS : 𝒬.IsTEqStruct Sig n D) :
    ∀ g ∈ 𝒬.R ++ 𝒬.A.filter (fun g => g.2.pmBlockB), g.2.ThetaRooted ∧ (∃ C, g.2.Normal C) ∧
      g.2.TKindsErr (n - 1) ∧ g.2.AtExternals ∧ g.2.DoublyConnected ∧ g.2.TensorDiffusive ∧
      g.2.DotsAcyclic ∧ (g.1 ≠ 0 → g.2.DiagRecoll) ∧ (3 : ℤ) ≤ g.2.diagOrd := by
  obtain ⟨-, -, -, -, hShape, hTR, hDef⟩ := hS
  obtain ⟨⟨hS1, -⟩, hSR, -, -, -⟩ := hShape
  obtain ⟨⟨-, hDA, -⟩, hDall, -, hPM5, -⟩ := hDef
  intro g hg
  have hRA : g ∈ 𝒬.R ∨ (g ∈ 𝒬.A ∧ g.2.pmBlockB = true) := by
    rcases List.mem_append.1 hg with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.1 h)
  have hRA' : g ∈ 𝒬.toTRec.R ++ 𝒬.toTRec.A := by
    rcases hRA with h | ⟨h, -⟩
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ h
  have hRAQ : g ∈ 𝒬.toTRec.R ++ 𝒬.toTRec.A ++ 𝒬.toTRec.Q := List.mem_append_left _ hRA'
  have hall : g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err := List.mem_append_left _ hRAQ
  obtain ⟨hN, hK, hAE, hDC⟩ := hS1 g hRAQ
  obtain ⟨hTD, hdx, -, -⟩ := hDall g hall
  refine ⟨hTR g hall, hN, Graph.tKindsErr_of_tKinds _ _ hK, hAE, hDC, hTD,
    (Graph.dotsAcyclic_iff_dotExcess_eq_zero _).2 hdx, ?_, ?_⟩
  · intro h0
    rcases hRA with h | ⟨h, hpm⟩
    · exact Moment_diagRecoll_of_recoll g.2 (hSR g h).2.1
    · rcases (hDA g h).2 with ⟨h1, -⟩ | ⟨hE, -⟩
      · exact absurd h1 h0
      · exact Moment_diagRecoll_of_pmBlock g.2 hE hpm
  · unfold Graph.diagOrd
    by_cases hpm : g.2.pmBlockB = true
    · have := hPM5 g hRA' hpm
      simp only [hpm, ite_true]
      omega
    · rcases hRA with h | ⟨-, h⟩
      · have := (hSR g h).2.2.1
        simp only [hpm, Bool.false_eq_true, ite_false, sub_zero]
        exact this
      · exact absurd h hpm

/-- **[I, (1.28)] off the diagonal, before the choice of the constants**: for an `n`-th order
`T`-equation there are `K, len ≥ 0` such that for all `τ, D' > 0`, for `L ≥ L₀` along
`adm(c₀, c₁)`, `|𝒢_{x𝔟}| ≤ K W^τ B_{x𝔟}^{3/2} + len W^{−D'}` for `x ≠ 𝔟`. -/
private theorem LocalCorr_offDiag (hLL : LocalLawStmt) {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec} (hS : 𝒬.IsTEqStruct Sig n D)
    (hSE : SelfEnergiesUpTo d (smatVar P) Sig (n - 1)) :
    ∃ K len : ℝ, 0 ≤ K ∧ 0 ≤ len ∧ ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ x b : Zd d L, x ≠ b →
          ‖corrMat d P Sig 𝒬 W L z x b‖ ≤ K * ((W : ℝ) ^ τ * bB d L W x b ^ ((3 : ℝ) / 2)) +
            len * (W : ℝ) ^ (-D') := by
  have hfacts := LocalCorr_facts hS
  set l := 𝒬.R ++ 𝒬.A.filter (fun g => g.2.pmBlockB) with hl
  obtain ⟨K, hK0, hsum⟩ := ErrMain_sumBound P Sig (c₀ := c₀) (c₁ := c₁) (κ := κ) (ε := ε)
    (fun W L x b => bB d L W x b ^ ((3 : ℝ) / 2) +
      (if x = b then 1 else 0) * (W : ℝ) ^ (-((d : ℝ) / 2))) l
    fun g hgl => by
      obtain ⟨hTR', ⟨C, hN⟩, hK, hAE, hDC, hTD, hDA, hDR, hdiag⟩ := hfacts g hgl
      exact LocalCorr_graph hLL hd P hc₀ hc₁ hc hκ hε hSE g.2 hTR' hN hK hAE hDC hTD hDA hDR
        hdiag
  refine ⟨K, l.length, hK0, by positivity, fun τ hτ D' hD' => ?_⟩
  obtain ⟨W_VK, hVK⟩ := Smat_isVarKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨L₁, hL₁⟩ := hsum τ hτ D' hD'
  obtain ⟨L₂, hL₂⟩ := ErrMain_L₀ (c₀ := c₀) hc₁ (max 1 W_VK)
  refine ⟨max L₁ L₂, fun W L _ hL hadm z hz x b hxb => ?_⟩
  have hW := hL₂ W L ((le_max_right _ _).trans hL) hadm
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hW
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hVKW := hVK W L hadm ((le_max_right _ _).trans hW)
  have hzim : 0 < z.im := im_pos_of_specDom hW1n hz
  set f : (Σ n, Graph 3 n) → Sample (Zd d L) → ℂ := fun g => (rootRest g.2).2.valR
    ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![x, b, b] with hf
  have hint : ∀ g ∈ l, Integrable (f g) (gaussLaw (Smat P.ψ W L)) := by
    intro g hgl
    obtain ⟨⟨j, v, -, hk, -, -, hxy, hrest, -⟩, -, hK, -⟩ := hfacts g hgl
    exact MainCancel_valR_integrable_err P Sig W L z hVKW hzim _
      (ErrMain_rootRest_tKindsErr g.2 j v hk hxy (fun c hc => (hrest c hc).1) hK) _
  have hm : corrMat d P Sig 𝒬 W L z x b = ∫ ω, (l.map fun g => f g ω).sum
      ∂(gaussLaw (Smat P.ψ W L)) := by
    simp only [corrMat, Matrix.of_apply, hxb, ↓reduceIte, mul_zero, zero_add]
    rfl
  rw [hm]
  refine ((ErrMain_normInt (gaussLaw (Smat P.ψ W L)) f _ hint).2).trans ?_
  refine (hL₁ W L ((le_max_left _ _).trans hL) hadm z hz x b).trans (le_of_eq ?_)
  simp [hxb]

end OffDiagSum

/-! ## On the diagonal: the integration by parts at a fixed variance matrix -/

section DiagFixed

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Integrability of `a f + b g + c h`. -/
private lemma LocalCorr_int3_int {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g h : Ω → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (a b c : ℂ) : Integrable (fun ω => a * f ω + b * g ω + c * h ω) μ :=
  (show Integrable (fun ω => a * f ω + b * g ω) μ from
    (hf.const_mul a).add (hg.const_mul b)).add (hh.const_mul c)

/-- `E[a f + b g + c h] = a E f + b E g + c E h`. -/
private lemma LocalCorr_int3 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g h : Ω → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (a b c : ℂ) :
    ∫ ω, (a * f ω + b * g ω + c * h ω) ∂μ =
      a * ∫ ω, f ω ∂μ + b * ∫ ω, g ω ∂μ + c * ∫ ω, h ω ∂μ := by
  rw [integral_add (show Integrable (fun ω => a * f ω + b * g ω) μ from
    (hf.const_mul a).add (hg.const_mul b)) (hh.const_mul c),
    integral_add (hf.const_mul a) (hg.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- `Z_{k𝔟} = Δ_k Δ_𝔟 Δ̄_𝔟 + G_{k𝔟} Ḡ_{k𝔟} Δ̄_𝔟` at the sample `ω`, with `Δ_x = G_{xx} − m`. -/
private def LocalCorr_zk (z : ℂ) (ω : Sample ι) (k b : ι) : ℂ :=
  (green (hmat ω) z k k - msc z) * (green (hmat ω) z b b - msc z) *
      star (green (hmat ω) z b b - msc z) +
    green (hmat ω) z k b * star (green (hmat ω) z k b) * star (green (hmat ω) z b b - msc z)

/-- `X̃_{j,k𝔟} = Δ_j Δ_k Δ̄_𝔟 + G_{jk} Ḡ_{𝔟k} Ḡ_{j𝔟}` at the sample `ω`. -/
private def LocalCorr_xk (z : ℂ) (ω : Sample ι) (j k b : ι) : ℂ :=
  (green (hmat ω) z j j - msc z) * (green (hmat ω) z k k - msc z) *
      star (green (hmat ω) z b b - msc z) +
    green (hmat ω) z j k * star (green (hmat ω) z b k) * star (green (hmat ω) z j b)

/-- `C̃_{k𝔟} = E[Δ_k Δ̄_𝔟]`. -/
private def LocalCorr_ct (S : Matrix ι ι ℝ) (z : ℂ) (k b : ι) : ℂ :=
  ∫ ω, (green (hmat ω) z k k - msc z) * star (green (hmat ω) z b b - msc z) ∂(gaussLaw S)

/-- `F̃_{k𝔟} = E Σ_j s_{kj} X̃_{j,k𝔟}`. -/
private def LocalCorr_fv (S : Matrix ι ι ℝ) (z : ℂ) (k b : ι) : ℂ :=
  ∫ ω, ∑ j, (S k j : ℂ) * LocalCorr_xk z ω j k b ∂(gaussLaw S)

private lemma LocalCorr_tf_Gc {z : ℂ} (hz : z.im ≠ 0) (x y : ι) :
    TestFn fun ω : Sample ι => star (green (hmat ω) z x y) :=
  testFn_closed.2.2.2.1 _ (tf_G hz x y)

private lemma LocalCorr_tf_Dc {z : ℂ} (hz : z.im ≠ 0) (x : ι) :
    TestFn fun ω : Sample ι => star (green (hmat ω) z x x - msc z) :=
  testFn_closed.2.2.2.1 _ (tf_D hz x)

/-- `∂_{h_{ka}} Δ̄_𝔟 = −Ḡ_{𝔟a} Ḡ_{k𝔟}`. -/
private lemma LocalCorr_dh_Dc {z : ℂ} (hz : z.im ≠ 0) (k a b : ι) (ω : Sample ι) :
    dh k a (fun ω => star (green (hmat ω) z b b - msc z)) ω =
      -(star (green (hmat ω) z b a) * star (green (hmat ω) z k b)) := by
  have e : (fun ω : Sample ι => star (green (hmat ω) z b b - msc z)) =
      (fun ω => star (green (hmat ω) z b b)) + fun _ => -star (msc z) := by
    funext ω; simp [sub_eq_add_neg]
  rw [e, dh_add k a _ _ (LocalCorr_tf_Gc hz b b) (tf_const _), dh_const, add_zero,
    dh_conj_green z hz k a b b ω]

/-- **The integration by parts with the test function `Δ̄_𝔟`**: `E[G_{𝔟𝔟} Ḡ_{𝔟𝔟}] − m m̄ −
Σ_k m m̄ s_{𝔟k} E[G_{k𝔟} Ḡ_{k𝔟}] = m̄ E Δ_𝔟 + m E Δ̄_𝔟 + Σ_k s_{𝔟k} (m² C̃_{k𝔟} + m E Z_{k𝔟})`. -/
private theorem LocalCorr_stepA (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {z : ℂ} (hz : z.im ≠ 0) (b : ι) :
    ∫ ω, green (hmat ω) z b b * star (green (hmat ω) z b b) ∂(gaussLaw S) -
        msc z * star (msc z) -
      ∑ k, msc z * star (msc z) * (S b k : ℂ) *
        ∫ ω, green (hmat ω) z k b * star (green (hmat ω) z k b) ∂(gaussLaw S) =
    star (msc z) * ∫ ω, (green (hmat ω) z b b - msc z) ∂(gaussLaw S) +
      msc z * star (∫ ω, (green (hmat ω) z b b - msc z) ∂(gaussLaw S)) +
      ∑ k, (S b k : ℂ) * (msc z ^ 2 * LocalCorr_ct S z k b +
        msc z * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S)) := by
  have := isProbabilityMeasure_gaussLaw S
  have tD := fun x => tf_D (ι := ι) hz x
  have tZ : ∀ k, TestFn fun ω => LocalCorr_zk z ω k b := fun k =>
    tf_add (tf_mul (tf_mul (tD k) (tD b)) (LocalCorr_tf_Dc hz b))
      (tf_mul (tf_mul (tf_G hz k b) (LocalCorr_tf_Gc hz k b)) (LocalCorr_tf_Dc hz b))
  have tP : ∀ k, TestFn fun ω => green (hmat ω) z k b * star (green (hmat ω) z k b) :=
    fun k => tf_mul (tf_G hz k b) (LocalCorr_tf_Gc hz k b)
  have tC : ∀ k, TestFn fun ω =>
      (green (hmat ω) z k k - msc z) * star (green (hmat ω) z b b - msc z) :=
    fun k => tf_mul (tD k) (LocalCorr_tf_Dc hz b)
  have h := ibp S hS hS0 hS1 hz b _ (LocalCorr_tf_Dc hz b)
  simp only [LocalCorr_dh_Dc hz] at h
  have hpt : ∀ k ω, msc z ^ 2 * ((green (hmat ω) z k k - msc z) *
        star (green (hmat ω) z b b - msc z)) +
      msc z * ((green (hmat ω) z k k - msc z) * (green (hmat ω) z b b - msc z) *
        star (green (hmat ω) z b b - msc z) - green (hmat ω) z k b *
          -(star (green (hmat ω) z b b) * star (green (hmat ω) z k b))) =
      msc z ^ 2 * ((green (hmat ω) z k k - msc z) * star (green (hmat ω) z b b - msc z)) +
        msc z * LocalCorr_zk z ω k b +
        msc z * star (msc z) * (green (hmat ω) z k b * star (green (hmat ω) z k b)) := by
    intro k ω; simp only [LocalCorr_zk, star_sub]; ring
  simp only [hpt] at h
  have e1 : ∀ k, ∫ ω, (msc z ^ 2 * ((green (hmat ω) z k k - msc z) *
        star (green (hmat ω) z b b - msc z)) + msc z * LocalCorr_zk z ω k b +
        msc z * star (msc z) * (green (hmat ω) z k b * star (green (hmat ω) z k b))) ∂(gaussLaw S) =
      msc z ^ 2 * LocalCorr_ct S z k b + msc z * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S) +
        msc z * star (msc z) *
          ∫ ω, green (hmat ω) z k b * star (green (hmat ω) z k b) ∂(gaussLaw S) := by
    intro k
    rw [LocalCorr_int3 (integ S (tC k)) (integ S (tZ k)) (integ S (tP k))]
    rfl
  simp only [e1] at h
  -- the left side
  have hL : ∫ ω, green (hmat ω) z b b * star (green (hmat ω) z b b) ∂(gaussLaw S) =
      ∫ ω, (green (hmat ω) z b b - msc z) * star (green (hmat ω) z b b - msc z) ∂(gaussLaw S) +
        star (msc z) * ∫ ω, (green (hmat ω) z b b - msc z) ∂(gaussLaw S) +
        msc z * ∫ ω, star (green (hmat ω) z b b - msc z) ∂(gaussLaw S) +
        msc z * star (msc z) := by
    have hpt' : ∀ ω, green (hmat ω) z b b * star (green (hmat ω) z b b) =
        1 * ((green (hmat ω) z b b - msc z) * star (green (hmat ω) z b b - msc z)) +
          star (msc z) * (green (hmat ω) z b b - msc z) +
          msc z * star (green (hmat ω) z b b - msc z) + msc z * star (msc z) := by
      intro ω; simp only [star_sub]; ring
    simp only [hpt']
    rw [integral_add (LocalCorr_int3_int (integ S (tC b)) (integ S (tD b))
      (integ S (LocalCorr_tf_Dc hz b)) 1 (star (msc z)) (msc z)) (integrable_const _),
      LocalCorr_int3 (integ S (tC b)) (integ S (tD b)) (integ S (LocalCorr_tf_Dc hz b)),
      integral_const]
    simp
  have hc : ∫ ω, star (green (hmat ω) z b b - msc z) ∂(gaussLaw S) =
      star (∫ ω, (green (hmat ω) z b b - msc z) ∂(gaussLaw S)) := integral_conj
  rw [hL, hc, h]
  simp only [mul_add, Finset.sum_add_distrib]
  have e2 : ∀ k, (S b k : ℂ) * (msc z * star (msc z) *
      ∫ ω, green (hmat ω) z k b * star (green (hmat ω) z k b) ∂(gaussLaw S)) =
      msc z * star (msc z) * (S b k : ℂ) *
        ∫ ω, green (hmat ω) z k b * star (green (hmat ω) z k b) ∂(gaussLaw S) := fun k => by ring
  simp only [e2]
  ring

/-- **The equation of `C̃`**: `C̃_{k𝔟} = Σ_j m² s_{kj} C̃_{j𝔟} + m F̃_{k𝔟}`, that is
`(1 − m² S) C̃_{·𝔟} = m F̃_{·𝔟}`. -/
private theorem LocalCorr_stepB (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {z : ℂ} (hz : z.im ≠ 0) (k b : ι) :
    LocalCorr_ct S z k b =
      ∑ j, msc z ^ 2 * (S k j : ℂ) * LocalCorr_ct S z j b + msc z * LocalCorr_fv S z k b := by
  have tD := fun x => tf_D (ι := ι) hz x
  have tX : ∀ j, TestFn fun ω => LocalCorr_xk z ω j k b := fun j =>
    tf_add (tf_mul (tf_mul (tD j) (tD k)) (LocalCorr_tf_Dc hz b))
      (tf_mul (tf_mul (tf_G hz j k) (LocalCorr_tf_Gc hz b k)) (LocalCorr_tf_Gc hz j b))
  have tC : ∀ j, TestFn fun ω =>
      (green (hmat ω) z j j - msc z) * star (green (hmat ω) z b b - msc z) :=
    fun j => tf_mul (tD j) (LocalCorr_tf_Dc hz b)
  have h := ibp S hS hS0 hS1 hz k _ (LocalCorr_tf_Dc hz b)
  simp only [LocalCorr_dh_Dc hz] at h
  have hpt : ∀ j ω, msc z ^ 2 * ((green (hmat ω) z j j - msc z) *
        star (green (hmat ω) z b b - msc z)) +
      msc z * ((green (hmat ω) z j j - msc z) * (green (hmat ω) z k k - msc z) *
        star (green (hmat ω) z b b - msc z) - green (hmat ω) z j k *
          -(star (green (hmat ω) z b k) * star (green (hmat ω) z j b))) =
      msc z ^ 2 * ((green (hmat ω) z j j - msc z) * star (green (hmat ω) z b b - msc z)) +
        msc z * LocalCorr_xk z ω j k b := by
    intro j ω; simp only [LocalCorr_xk]; ring
  simp only [hpt] at h
  simp only [LocalCorr_ct]
  rw [h, LocalCorr_fv, integral_finsetSum _ fun j _ => (integ S (tX j)).const_mul _,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_add ((integ S (tC j)).const_mul _) ((integ S (tX j)).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- On a sample with `|G_{xy} − m δ_{xy}| ≤ ρ ≤ 1` for all `x, y` and `|m| ≤ 1`:
`|X̃_{j,k𝔟}| ≤ 2ρ³ + 2ρ² (δ_{jk} + δ_{j𝔟}) + δ_{k𝔟} (2ρ² + 8 δ_{j𝔟})`. -/
private lemma LocalCorr_norm_xk_good {z : ℂ} (hm : ‖msc z‖ ≤ 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (ω : Sample ι) (hω : ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ)
    (j k b : ι) :
    ‖LocalCorr_xk z ω j k b‖ ≤ 2 * ρ ^ 3 + 2 * ρ ^ 2 * ((if j = k then 1 else 0) +
      (if j = b then 1 else 0)) + (if k = b then 2 * ρ ^ 2 + (if j = b then 8 else 0) else 0) := by
  have hoff : ∀ x y, x ≠ y → ‖green (hmat ω) z x y‖ ≤ ρ := fun x y h => by
    have := hω x y; simpa [entryErr, h] using this
  have hd : ∀ x, ‖green (hmat ω) z x x - msc z‖ ≤ ρ := fun x => by
    have := hω x x; simpa [entryErr] using this
  have hdiag : ∀ x, ‖green (hmat ω) z x x‖ ≤ 2 := fun x => by
    have e : green (hmat ω) z x x = (green (hmat ω) z x x - msc z) + msc z := by ring
    rw [e]
    linarith [norm_add_le (green (hmat ω) z x x - msc z) (msc z), hd x]
  have hD3 := norm_mul3_le (hd j) (hd k) (show ‖star (green (hmat ω) z b b - msc z)‖ ≤ ρ by
    rw [norm_star]; exact hd b)
  have hsplit : ‖LocalCorr_xk z ω j k b‖ ≤ ρ * ρ * ρ +
      ‖green (hmat ω) z j k‖ * ‖green (hmat ω) z b k‖ * ‖green (hmat ω) z j b‖ := by
    refine (norm_add_le _ _).trans (add_le_add hD3 (le_of_eq ?_))
    rw [norm_mul, norm_mul, norm_star, norm_star]
  have hρ2 : 0 ≤ ρ ^ 2 := by positivity
  have hρ3 : ρ ^ 3 ≤ ρ ^ 2 := by nlinarith
  have hn := fun x y => norm_nonneg (green (hmat ω) z x y)
  refine hsplit.trans ?_
  by_cases hkb : k = b
  · subst hkb
    by_cases hjk : j = k
    · subst hjk
      have h3 := mul_le_mul (mul_le_mul (hdiag j) (hdiag j) (hn _ _) (by norm_num)) (hdiag j)
        (hn _ _) (by norm_num)
      simp only [ite_true]
      nlinarith
    · have h3 := mul_le_mul (mul_le_mul (hoff j k hjk) (hdiag k) (hn _ _) hρ0) (hoff j k hjk)
        (hn _ _) (by positivity)
      simp only [hjk, ite_true, ite_false]
      nlinarith
  · by_cases hjk : j = k
    · subst hjk
      have h3 := mul_le_mul (mul_le_mul (hdiag j) (hoff b j (Ne.symm hkb)) (hn _ _)
        (by norm_num)) (hoff j b hkb) (hn _ _) (by positivity)
      simp only [hkb, ite_true, ite_false]
      nlinarith
    · by_cases hjb : j = b
      · subst hjb
        have h3 := mul_le_mul (mul_le_mul (hoff j k hjk) (hoff j k hjk) (hn _ _) hρ0)
          (hdiag j) (hn _ _) (by positivity)
        simp only [hkb, hjk, ite_true, ite_false]
        nlinarith
      · have h3 := mul_le_mul (mul_le_mul (hoff j k hjk) (hoff b k (Ne.symm hkb)) (hn _ _) hρ0)
          (hoff j b hjb) (hn _ _) (by positivity)
        simp only [hkb, hjk, hjb, ite_false]
        nlinarith

/-- On a sample of the local-law event, `|Σ_j s_{kj} X̃_{j,k𝔟}| ≤ 2ρ³ + 4ρ² s₀ +
δ_{k𝔟}(2ρ² + 8s₀)` for `s_{xy} ≤ s₀`. -/
private lemma LocalCorr_norm_sum_xk_good (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {s₀ : ℝ} (hs : ∀ x y, S x y ≤ s₀) {z : ℂ} (hm : ‖msc z‖ ≤ 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (ω : Sample ι)
    (hω : ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ) (k b : ι) :
    ‖∑ j, (S k j : ℂ) * LocalCorr_xk z ω j k b‖ ≤
      2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + (if k = b then 2 * ρ ^ 2 + 8 * s₀ else 0) := by
  refine (norm_wsum_le S hS0 k _).trans ?_
  have hρ2 : 0 ≤ ρ ^ 2 := by positivity
  calc ∑ j, S k j * ‖LocalCorr_xk z ω j k b‖
      ≤ ∑ j, S k j * (2 * ρ ^ 3 + 2 * ρ ^ 2 * ((if j = k then 1 else 0) +
          (if j = b then 1 else 0)) + (if k = b then 2 * ρ ^ 2 + (if j = b then 8 else 0)
            else 0)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (LocalCorr_norm_xk_good hm hρ0 hρ1 ω hω j k b) (hS0 k j)
    _ = 2 * ρ ^ 3 * ∑ j, S k j + 2 * ρ ^ 2 * (S k k + S k b) +
        (if k = b then 2 * ρ ^ 2 * ∑ j, S k j + 8 * S k b else 0) := by
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        split_ifs with h
        · subst h
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
            ← Finset.sum_mul]
          ring
        · simp only [Finset.sum_const_zero, ← Finset.sum_mul]
          ring
    _ ≤ 2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + (if k = b then 2 * ρ ^ 2 + 8 * s₀ else 0) := by
        rw [hS1 k]
        have h1 := hs k k
        have h2 := hs k b
        split_ifs <;> nlinarith

/-- Everywhere, `|Σ_j s_{kj} X̃_{j,k𝔟}| ≤ 9 Λ³` for `|G_{xy}| ≤ Λ` and `1 ≤ Λ`. -/
private lemma LocalCorr_norm_sum_xk_le (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {z : ℂ} (hm : ‖msc z‖ ≤ 1) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : Sample ι) (hG : ∀ x y, ‖green (hmat ω) z x y‖ ≤ Λ) (k b : ι) :
    ‖∑ j, (S k j : ℂ) * LocalCorr_xk z ω j k b‖ ≤ 9 * Λ ^ 3 := by
  have hd : ∀ x, ‖green (hmat ω) z x x - msc z‖ ≤ 2 * Λ := fun x =>
    (norm_sub_le _ _).trans (by linarith [hG x x])
  have hx : ∀ j, ‖LocalCorr_xk z ω j k b‖ ≤ 9 * Λ ^ 3 := fun j => by
    have h1 := norm_mul3_le (hd j) (hd k)
      (show ‖star (green (hmat ω) z b b - msc z)‖ ≤ 2 * Λ by rw [norm_star]; exact hd b)
    have h2 := norm_mul3_le (hG j k)
      (show ‖star (green (hmat ω) z b k)‖ ≤ Λ by rw [norm_star]; exact hG b k)
      (show ‖star (green (hmat ω) z j b)‖ ≤ Λ by rw [norm_star]; exact hG j b)
    have := norm_add_le ((green (hmat ω) z j j - msc z) * (green (hmat ω) z k k - msc z) *
      star (green (hmat ω) z b b - msc z))
      (green (hmat ω) z j k * star (green (hmat ω) z b k) * star (green (hmat ω) z j b))
    simp only [LocalCorr_xk]
    nlinarith
  refine (norm_wsum_le S hS0 k _).trans ?_
  calc ∑ j, S k j * ‖LocalCorr_xk z ω j k b‖ ≤ ∑ j, S k j * (9 * Λ ^ 3) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) (hS0 k j)
    _ = 9 * Λ ^ 3 := by rw [← Finset.sum_mul, hS1 k, one_mul]

/-- **The bound of `Σ_k s_{𝔟k} C̃_{k𝔟}`** at a fixed variance matrix `S ≥ 0` (symmetric, row
sums `1`, `s_{xy} ≤ s₀`) and `0 < Im z ≤ 1`, for `|S^+_{xy}| ≤ r₀`, `Σ_y |S^+_{xy}| ≤ r₁` and a set
`Bad` off which `|G_{xy} − m δ_{xy}| ≤ ρ ≤ 1`: it is at most `(1 + r₁) β₁ + (s₀ + r₀) β₂` with
`β₁ = 2ρ³ + 4ρ² s₀ + 9 η⁻³ P(Bad)` and `β₂ = 2ρ² + 8 s₀`. -/
private theorem LocalCorr_ct_bound (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {s₀ : ℝ} (hs : ∀ x y, S x y ≤ s₀) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) {r₀ r₁ : ℝ}
    (hR0 : ∀ x y, ‖Splus (msc z) S x y‖ ≤ r₀) (hR1 : ∀ x, ∑ y, ‖Splus (msc z) S x y‖ ≤ r₁)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (Bad : Set (Sample ι))
    (hgood : ∀ ω, ω ∉ Bad → ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ) (b : ι) :
    ‖∑ k, (S b k : ℂ) * LocalCorr_ct S z k b‖ ≤
      (1 + r₁) * (2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + 9 * z.im⁻¹ ^ 3 * (gaussLaw S Bad).toReal) +
        (s₀ + r₀) * (2 * ρ ^ 2 + 8 * s₀) := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have := isProbabilityMeasure_gaussLaw S
  have hR := one_add_mul_one_sub S (msc z) (isUnit_one_sub S hS0 hS1 hm1)
  set Λ := z.im⁻¹ with hΛdef
  have hΛ : 1 ≤ Λ := one_le_inv_iff₀.mpr ⟨hz, hz1⟩
  have hG : ∀ (ω : Sample ι) x y, ‖green (hmat ω) z x y‖ ≤ Λ := fun ω x y => by
    have := norm_green_entry_le (hmat_isHermitian ω) hz0 x y
    rwa [abs_of_pos hz] at this
  have hs0 : 0 ≤ s₀ := (hS0 b b).trans (hs b b)
  set β₁ := 2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + 9 * Λ ^ 3 * (gaussLaw S Bad).toReal with hβ₁
  set β₂ := 2 * ρ ^ 2 + 8 * s₀ with hβ₂
  have hβ₁0 : 0 ≤ β₁ := by positivity
  have hβ₂0 : 0 ≤ β₂ := by positivity
  have hF : ∀ k c, ‖LocalCorr_fv S z k c‖ ≤ β₁ + if k = c then β₂ else 0 := by
    intro k c
    have h := norm_integral_le_good (gaussLaw S)
      (fun ω => ∑ j, (S k j : ℂ) * LocalCorr_xk z ω j k c) Bad
      (2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + (if k = c then 2 * ρ ^ 2 + 8 * s₀ else 0)) (9 * Λ ^ 3)
      (by split_ifs <;> positivity)
      (fun ω => LocalCorr_norm_sum_xk_le S hS0 hS1 hm1.le hΛ ω (hG ω) k c)
      (fun ω hω => LocalCorr_norm_sum_xk_good S hS0 hS1 hs hm1.le hρ0 hρ1 ω (hgood ω hω) k c)
    refine h.trans (le_of_eq ?_)
    rw [hβ₁, hβ₂]
    split_ifs <;> ring
  -- the columns of `C̃`
  have hA : ∀ x k, (msc z ^ 2 • cmat S) x k = msc z ^ 2 * (S x k : ℂ) := fun x k => by
    simp [cmat]
  have hC : ∀ k, ‖LocalCorr_ct S z k b‖ ≤ (1 + r₁) * β₁ + (if k = b then β₂ else 0) + r₀ * β₂ := by
    intro k
    have hsol := solve (msc z ^ 2 • cmat S) (Splus (msc z) S) hR (fun a => LocalCorr_ct S z a b)
      (fun a => msc z * LocalCorr_fv S z a b)
      (fun a => by simp only [hA]; exact LocalCorr_stepB S hS hS0 hS1 hz0 a b) k
    rw [hsol]
    have hw : ∀ y, ‖msc z * LocalCorr_fv S z y b‖ ≤ β₁ + if y = b then β₂ else 0 := fun y => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hm1.le).trans (hF y b)
    have hsum : ‖∑ y, Splus (msc z) S k y * (msc z * LocalCorr_fv S z y b)‖ ≤
        r₁ * β₁ + r₀ * β₂ := by
      calc ‖∑ y, Splus (msc z) S k y * (msc z * LocalCorr_fv S z y b)‖
          ≤ ∑ y, ‖Splus (msc z) S k y‖ * (β₁ + if y = b then β₂ else 0) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hw y) (norm_nonneg _)
        _ = (∑ y, ‖Splus (msc z) S k y‖) * β₁ + ‖Splus (msc z) S k b‖ * β₂ := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mul_ite, mul_zero,
              Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        _ ≤ r₁ * β₁ + r₀ * β₂ := by
            gcongr
            · exact hR1 k
            · exact hR0 k b
    calc ‖msc z * LocalCorr_fv S z k b + ∑ y, Splus (msc z) S k y * (msc z * LocalCorr_fv S z y b)‖
        ≤ ‖msc z * LocalCorr_fv S z k b‖ +
          ‖∑ y, Splus (msc z) S k y * (msc z * LocalCorr_fv S z y b)‖ := norm_add_le _ _
      _ ≤ (β₁ + if k = b then β₂ else 0) + (r₁ * β₁ + r₀ * β₂) := add_le_add (hw k) hsum
      _ = _ := by ring
  calc ‖∑ k, (S b k : ℂ) * LocalCorr_ct S z k b‖ ≤ ∑ k, S b k * ‖LocalCorr_ct S z k b‖ :=
        norm_wsum_le S hS0 b _
    _ ≤ ∑ k, S b k * ((1 + r₁) * β₁ + (if k = b then β₂ else 0) + r₀ * β₂) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hC k) (hS0 b k)
    _ = ∑ k, (S b k * ((1 + r₁) * β₁ + r₀ * β₂) + if k = b then S b k * β₂ else 0) :=
        Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
    _ = ((1 + r₁) * β₁ + r₀ * β₂) * ∑ k, S b k + S b b * β₂ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_mul]
        simp only [Finset.mem_univ, ite_true]
        ring
    _ ≤ (1 + r₁) * β₁ + (s₀ + r₀) * β₂ := by
        rw [hS1 b, mul_one]
        nlinarith [hs b b]

/-- **The bound of `Σ_k s_{𝔟k} E Z_{k𝔟}`**: under the hypotheses of `LocalCorr_ct_bound`, it is at
most `2ρ³ + 4ρ s₀ + 10 η⁻³ P(Bad)`. -/
private theorem LocalCorr_z_bound (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {s₀ : ℝ} (hs : ∀ x y, S x y ≤ s₀) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (Bad : Set (Sample ι))
    (hgood : ∀ ω, ω ∉ Bad → ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ) (b : ι) :
    ‖∑ k, (S b k : ℂ) * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S)‖ ≤
      2 * ρ ^ 3 + 4 * ρ * s₀ + 10 * z.im⁻¹ ^ 3 * (gaussLaw S Bad).toReal := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have := isProbabilityMeasure_gaussLaw S
  set Λ := z.im⁻¹ with hΛdef
  have hΛ : 1 ≤ Λ := one_le_inv_iff₀.mpr ⟨hz, hz1⟩
  have hG : ∀ (ω : Sample ι) x y, ‖green (hmat ω) z x y‖ ≤ Λ := fun ω x y => by
    have := norm_green_entry_le (hmat_isHermitian ω) hz0 x y
    rwa [abs_of_pos hz] at this
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hs0 : 0 ≤ s₀ := (hS0 b b).trans (hs b b)
  have tD := fun x => tf_D (ι := ι) hz0 x
  have tZ : ∀ k, TestFn fun ω => LocalCorr_zk z ω k b := fun k =>
    tf_add (tf_mul (tf_mul (tD k) (tD b)) (LocalCorr_tf_Dc hz0 b))
      (tf_mul (tf_mul (tf_G hz0 k b) (LocalCorr_tf_Gc hz0 k b)) (LocalCorr_tf_Dc hz0 b))
  have e : ∑ k, (S b k : ℂ) * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S) =
      ∫ ω, ∑ k, (S b k : ℂ) * LocalCorr_zk z ω k b ∂(gaussLaw S) := by
    rw [integral_finsetSum _ fun k _ => (integ S (tZ k)).const_mul _]
    exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
  rw [e]
  have hZ : ∀ ω, ‖∑ k, (S b k : ℂ) * LocalCorr_zk z ω k b‖ ≤ 10 * Λ ^ 3 := by
    intro ω
    have hd : ∀ x, ‖green (hmat ω) z x x - msc z‖ ≤ 2 * Λ := fun x =>
      (norm_sub_le _ _).trans (by linarith [hG ω x x])
    have hx : ∀ k, ‖LocalCorr_zk z ω k b‖ ≤ 10 * Λ ^ 3 := fun k => by
      have hdc : ‖star (green (hmat ω) z b b - msc z)‖ ≤ 2 * Λ := by rw [norm_star]; exact hd b
      have h1 := norm_mul3_le (hd k) (hd b) hdc
      have h2 := norm_mul3_le (hG ω k b)
        (show ‖star (green (hmat ω) z k b)‖ ≤ Λ by rw [norm_star]; exact hG ω k b) hdc
      have := norm_add_le ((green (hmat ω) z k k - msc z) * (green (hmat ω) z b b - msc z) *
        star (green (hmat ω) z b b - msc z))
        (green (hmat ω) z k b * star (green (hmat ω) z k b) * star (green (hmat ω) z b b - msc z))
      simp only [LocalCorr_zk]
      nlinarith
    refine (norm_wsum_le S hS0 b _).trans ?_
    calc ∑ k, S b k * ‖LocalCorr_zk z ω k b‖ ≤ ∑ k, S b k * (10 * Λ ^ 3) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hx k) (hS0 b k)
      _ = 10 * Λ ^ 3 := by rw [← Finset.sum_mul, hS1 b, one_mul]
  have hZg : ∀ ω, ω ∉ Bad → ‖∑ k, (S b k : ℂ) * LocalCorr_zk z ω k b‖ ≤ 2 * ρ ^ 3 + 4 * ρ * s₀ := by
    intro ω hω
    have hω' := hgood ω hω
    have hoff : ∀ x y, x ≠ y → ‖green (hmat ω) z x y‖ ≤ ρ := fun x y h => by
      have := hω' x y; simpa [entryErr, h] using this
    have hd : ∀ x, ‖green (hmat ω) z x x - msc z‖ ≤ ρ := fun x => by
      have := hω' x x; simpa [entryErr] using this
    have hdiag : ∀ x, ‖green (hmat ω) z x x‖ ≤ 2 := fun x => by
      have e : green (hmat ω) z x x = (green (hmat ω) z x x - msc z) + msc z := by ring
      rw [e]
      linarith [norm_add_le (green (hmat ω) z x x - msc z) (msc z), hd x]
    have hdc : ‖star (green (hmat ω) z b b - msc z)‖ ≤ ρ := by rw [norm_star]; exact hd b
    have hx : ∀ k, ‖LocalCorr_zk z ω k b‖ ≤ 2 * ρ ^ 3 + (if k = b then 4 * ρ else 0) := by
      intro k
      have h1 := norm_mul3_le (hd k) (hd b) hdc
      have hsplit : ‖LocalCorr_zk z ω k b‖ ≤ ρ * ρ * ρ +
          ‖green (hmat ω) z k b‖ * ‖green (hmat ω) z k b‖ *
            ‖star (green (hmat ω) z b b - msc z)‖ := by
        refine (norm_add_le _ _).trans (add_le_add h1 (le_of_eq ?_))
        rw [norm_mul, norm_mul, norm_star]
      refine hsplit.trans ?_
      have hn := norm_nonneg (green (hmat ω) z k b)
      have hn' := norm_nonneg (star (green (hmat ω) z b b - msc z))
      by_cases hkb : k = b
      · subst hkb
        have h3 := mul_le_mul (mul_le_mul (hdiag k) (hdiag k) hn (by norm_num)) hdc hn'
          (by norm_num)
        simp only [ite_true]
        nlinarith
      · have h3 := mul_le_mul (mul_le_mul (hoff k b hkb) (hoff k b hkb) hn hρ0) hdc hn'
          (by positivity)
        simp only [hkb, ite_false]
        nlinarith
    refine (norm_wsum_le S hS0 b _).trans ?_
    calc ∑ k, S b k * ‖LocalCorr_zk z ω k b‖
        ≤ ∑ k, S b k * (2 * ρ ^ 3 + (if k = b then 4 * ρ else 0)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hx k) (hS0 b k)
      _ = 2 * ρ ^ 3 * ∑ k, S b k + S b b * (4 * ρ) := by
          simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true, ← Finset.sum_mul]
          ring
      _ ≤ 2 * ρ ^ 3 + 4 * ρ * s₀ := by
          rw [hS1 b]
          nlinarith [hs b b]
  have h := norm_integral_le_good (gaussLaw S) (fun ω => ∑ k, (S b k : ℂ) * LocalCorr_zk z ω k b)
    Bad (2 * ρ ^ 3 + 4 * ρ * s₀) (10 * Λ ^ 3) (by positivity) hZ hZg
  refine h.trans (le_of_eq ?_)
  ring

/-- **The bound of `E T_{y,𝔟𝔟}`**: under the hypotheses of `LocalCorr_ct_bound`,
`|E Σ_x |m|² s_{yx} |G_{x𝔟}|²| ≤ ρ² + 4 s₀ + η⁻² P(Bad)`. -/
private theorem LocalCorr_t_bound (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {s₀ : ℝ} (hs : ∀ x y, S x y ≤ s₀) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) {ρ : ℝ} (hρ1 : ρ ≤ 1) (Bad : Set (Sample ι))
    (hgood : ∀ ω, ω ∉ Bad → ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ) (y b : ι) :
    ‖∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S y x : ℂ) * ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ)
      ∂(gaussLaw S)‖ ≤ ρ ^ 2 + 4 * s₀ + z.im⁻¹ ^ 2 * (gaussLaw S Bad).toReal := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have := isProbabilityMeasure_gaussLaw S
  set Λ := z.im⁻¹ with hΛdef
  have hΛ : 1 ≤ Λ := one_le_inv_iff₀.mpr ⟨hz, hz1⟩
  have hG : ∀ (ω : Sample ι) x y, ‖green (hmat ω) z x y‖ ≤ Λ := fun ω x y => by
    have := norm_green_entry_le (hmat_isHermitian ω) hz0 x y
    rwa [abs_of_pos hz] at this
  have hm1 : ‖msc z‖ ^ 2 ≤ 1 := by
    have := (norm_msc_lt_one hz).le
    nlinarith [norm_nonneg (msc z)]
  have hs0 : 0 ≤ s₀ := (hS0 b b).trans (hs b b)
  have hpt : ∀ ω, ‖∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S y x : ℂ) *
      ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ)‖ ≤ ∑ x, S y x * ‖green (hmat ω) z x b‖ ^ 2 := by
    intro ω
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (hS0 y x),
      Real.norm_of_nonneg (by positivity)]
    have := mul_nonneg (hS0 y x) (sq_nonneg ‖green (hmat ω) z x b‖)
    nlinarith
  have hall : ∀ ω, ‖∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S y x : ℂ) *
      ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ)‖ ≤ Λ ^ 2 := by
    intro ω
    refine (hpt ω).trans ?_
    calc ∑ x, S y x * ‖green (hmat ω) z x b‖ ^ 2 ≤ ∑ x, S y x * Λ ^ 2 :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hG ω x b) 2) (hS0 y x)
      _ = Λ ^ 2 := by rw [← Finset.sum_mul, hS1 y, one_mul]
  have hgd : ∀ ω, ω ∉ Bad → ‖∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S y x : ℂ) *
      ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ)‖ ≤ ρ ^ 2 + 4 * s₀ := by
    intro ω hω
    have hω' := hgood ω hω
    have hoff : ∀ x, x ≠ b → ‖green (hmat ω) z x b‖ ≤ ρ := fun x h => by
      have := hω' x b; simpa [entryErr, h] using this
    have hdiag : ‖green (hmat ω) z b b‖ ≤ 2 := by
      have hd : ‖green (hmat ω) z b b - msc z‖ ≤ ρ := by
        have := hω' b b; simpa [entryErr] using this
      have e : green (hmat ω) z b b = (green (hmat ω) z b b - msc z) + msc z := by ring
      rw [e]
      linarith [norm_add_le (green (hmat ω) z b b - msc z) (msc z), (norm_msc_lt_one hz).le, hρ1]
    refine (hpt ω).trans ?_
    have hx : ∀ x, ‖green (hmat ω) z x b‖ ^ 2 ≤ ρ ^ 2 + if x = b then 4 else 0 := by
      intro x
      by_cases h : x = b
      · subst h
        simp only [ite_true]
        nlinarith [norm_nonneg (green (hmat ω) z x x), sq_nonneg ρ]
      · simp only [h, ite_false, add_zero]
        exact pow_le_pow_left₀ (norm_nonneg _) (hoff x h) 2
    calc ∑ x, S y x * ‖green (hmat ω) z x b‖ ^ 2
        ≤ ∑ x, S y x * (ρ ^ 2 + if x = b then 4 else 0) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hx x) (hS0 y x)
      _ = ρ ^ 2 * ∑ x, S y x + S y b * 4 := by
          simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true, ← Finset.sum_mul]
          ring
      _ ≤ ρ ^ 2 + 4 * s₀ := by
          rw [hS1 y]
          nlinarith [hs y b]
  have h := norm_integral_le_good (gaussLaw S) (fun ω => ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) *
    (S y x : ℂ) * ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ)) Bad (ρ ^ 2 + 4 * s₀) (Λ ^ 2)
    (by positivity) hall hgd
  exact h

/-- **The fixed bound on the diagonal**: under the hypotheses of `LocalCorr_ct_bound`,
`|E|G_{𝔟𝔟}|² − |m|² − E T_{𝔟,𝔟𝔟}| ≤ 2|E G_{𝔟𝔟} − m| + (1 + r₁) β₁ + (s₀ + r₀) β₂ + 2ρ³ + 4ρ s₀ +
10 η⁻³ P(Bad)`. -/
private theorem LocalCorr_diagFixed (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {s₀ : ℝ} (hs : ∀ x y, S x y ≤ s₀) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) {r₀ r₁ : ℝ}
    (hR0 : ∀ x y, ‖Splus (msc z) S x y‖ ≤ r₀) (hR1 : ∀ x, ∑ y, ‖Splus (msc z) S x y‖ ≤ r₁)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (Bad : Set (Sample ι))
    (hgood : ∀ ω, ω ∉ Bad → ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ) (b : ι) :
    ‖∫ ω, ((‖green (hmat ω) z b b‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw S) - ((‖msc z‖ ^ 2 : ℝ) : ℂ) -
      ∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S b x : ℂ) * ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ)
        ∂(gaussLaw S)‖ ≤
      2 * ‖∫ ω, green (hmat ω) z b b ∂(gaussLaw S) - msc z‖ +
        ((1 + r₁) * (2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + 9 * z.im⁻¹ ^ 3 * (gaussLaw S Bad).toReal) +
          (s₀ + r₀) * (2 * ρ ^ 2 + 8 * s₀)) +
        (2 * ρ ^ 3 + 4 * ρ * s₀ + 10 * z.im⁻¹ ^ 3 * (gaussLaw S Bad).toReal) := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have := isProbabilityMeasure_gaussLaw S
  have hm1 : ‖msc z‖ ≤ 1 := (norm_msc_lt_one hz).le
  have hsq : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := fun w => by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; rfl
  have tP : ∀ x y : ι, TestFn fun ω : Sample ι => green (hmat ω) z x y *
      star (green (hmat ω) z x y) :=
    fun x y => tf_mul (tf_G hz0 x y) (LocalCorr_tf_Gc hz0 x y)
  have hT : ∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S b x : ℂ) *
      ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw S) =
      ∑ k, msc z * star (msc z) * (S b k : ℂ) *
        ∫ ω, green (hmat ω) z k b * star (green (hmat ω) z k b) ∂(gaussLaw S) := by
    simp only [hsq]
    rw [integral_finsetSum _ fun k _ => (integ S (tP k b)).const_mul _]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hA : ∫ ω, ((‖green (hmat ω) z b b‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw S) =
      ∫ ω, green (hmat ω) z b b * star (green (hmat ω) z b b) ∂(gaussLaw S) := by
    simp only [hsq]
  have hg : ∫ ω, (green (hmat ω) z b b - msc z) ∂(gaussLaw S) =
      ∫ ω, green (hmat ω) z b b ∂(gaussLaw S) - msc z := by
    rw [integral_sub (integ S (tf_G hz0 b b)) (integrable_const _), integral_const]
    simp
  rw [hT, hA, hsq (msc z), LocalCorr_stepA S hS hS0 hS1 hz0 b, hg]
  set g := ∫ ω, green (hmat ω) z b b ∂(gaussLaw S) - msc z with hgdef
  have e : ∑ k, (S b k : ℂ) * (msc z ^ 2 * LocalCorr_ct S z k b +
      msc z * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S)) =
      msc z ^ 2 * ∑ k, (S b k : ℂ) * LocalCorr_ct S z k b +
        msc z * ∑ k, (S b k : ℂ) * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have h1 := LocalCorr_ct_bound S hS hS0 hS1 hs hz hz1 hR0 hR1 hρ0 hρ1 Bad hgood b
  have h2 := LocalCorr_z_bound S hS0 hS1 hs hz hz1 hρ0 hρ1 Bad hgood b
  have hm2 : ‖msc z ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm1
  calc ‖star (msc z) * g + msc z * star g + (msc z ^ 2 * ∑ k, (S b k : ℂ) * LocalCorr_ct S z k b +
        msc z * ∑ k, (S b k : ℂ) * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S))‖
      ≤ ‖star (msc z) * g‖ + ‖msc z * star g‖ +
          (‖msc z ^ 2 * ∑ k, (S b k : ℂ) * LocalCorr_ct S z k b‖ +
          ‖msc z * ∑ k, (S b k : ℂ) * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S)‖) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _)) (norm_add_le _ _))
    _ ≤ ‖g‖ + ‖g‖ + (‖∑ k, (S b k : ℂ) * LocalCorr_ct S z k b‖ +
          ‖∑ k, (S b k : ℂ) * ∫ ω, LocalCorr_zk z ω k b ∂(gaussLaw S)‖) := by
        simp only [norm_mul, norm_star]
        gcongr
        · exact mul_le_of_le_one_left (norm_nonneg _) hm1
        · exact mul_le_of_le_one_left (norm_nonneg _) hm1
        · exact mul_le_of_le_one_left (norm_nonneg _) hm2
        · exact mul_le_of_le_one_left (norm_nonneg _) hm1
    _ ≤ _ := by linarith

end DiagFixed

/-! ## On the diagonal: the identity through the rooted `T`-equation -/

section DiagIdentity

/-- The rooted graph has the kinds of [II, Def 3.2] if the graph has them. -/
private theorem LocalCorr_rootRest_tKinds {n N : ℕ} (g : Graph 3 n) (j : Fin g.comps.length)
    (v : Atom 3 n) (hk : g.comps[j].kind = .theta [])
    (hxy : g.comps[j].x = .inl 0 ∧ g.comps[j].y = v)
    (hrest : ∀ c ∈ (g.dropComp j).comps, c.x ≠ .inl 0) (hK : g.TKinds N) :
    (rootRest g).2.TKinds N := by
  rw [rootRest_eq g j v hk hxy hrest]
  have hK' : ∀ c ∈ (g.dropComp j).comps, c.isTKind N = true :=
    fun c hc => List.all_eq_true.1 hK c (List.mem_of_mem_eraseIdx hc)
  unfold Graph.TKinds
  rw [List.all_eq_true]
  rcases v with a | i
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hK' c hc
    · cases hc with
      | head => rfl
      | tail _ h => cases h
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact (isTKind_map N _ c₀).trans (hK' c₀ hc₀)

/-- The rooted graph of a `Q`-graph ([I, Def 2.14 (ii)]) of the form [II, Def 3.3 (4)] is a
`Q`-graph: the root edge carries no label, and the label atom is moved with the other atoms. -/
private theorem LocalCorr_rootRest_qGraph {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length)
    (v : Atom 3 n) (hk : g.comps[j].kind = .theta []) (hlab : g.comps[j].label = none)
    (hxy : g.comps[j].x = .inl 0 ∧ g.comps[j].y = v)
    (hrest : ∀ c ∈ (g.dropComp j).comps, c.x ≠ .inl 0) (hQ : g.IsQGraph) :
    (rootRest g).2.IsQGraph := by
  rw [rootRest_eq g j v hk hxy hrest]
  obtain ⟨u, ⟨c₀, hc₀, hl₀⟩, hall⟩ := hQ
  have hc₀' : c₀ ∈ (g.dropComp j).comps := by
    have hd : g.comps = g.comps.take j ++ g.comps[j] :: g.comps.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop j g.comps, List.drop_eq_getElem_cons j.2]
      rfl
    have hc := hc₀
    rw [hd, List.mem_append, List.mem_cons] at hc
    simp only [Graph.dropComp, List.eraseIdx_eq_take_drop_succ, List.mem_append]
    rcases hc with hc | rfl | hc
    · exact Or.inl hc
    · rw [hlab] at hl₀
      cases hl₀
    · exact Or.inr hc
  have hall' : ∀ c ∈ (g.dropComp j).comps, (c.kind.isRandom = true ∨ c.label.isSome = true) →
      c.label = some (.Q, u) := fun c hc => hall c (List.mem_of_mem_eraseIdx hc)
  rcases v with a | i
  · refine ⟨u, ⟨c₀, List.mem_append_left _ hc₀', hl₀⟩, fun c hc h => ?_⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact hall' c hc h
    · cases hc with
      | head => exfalso; rcases h with h | h <;> cases h
      | tail _ h' => cases h'
  · obtain ⟨F, hF⟩ : ∃ F : Atom 3 n → Atom 3 (n - 1),
        ((g.dropComp j).rootGraph (.inr i)).2.comps = (g.dropComp j).comps.map (Comp.map F) :=
      ⟨_, rfl⟩
    refine ⟨F u, ⟨c₀.map F, ?_, by simp only [Comp.map, hl₀, Option.map_some]; rfl⟩,
      fun c hc h => ?_⟩
    · rw [hF]; exact List.mem_map_of_mem hc₀'
    · rw [hF] at hc
      obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
      have := hall' c₁ hc₁ (by
        rcases h with h | h
        · exact Or.inl h
        · right
          revert h
          simp only [Comp.map]
          rcases c₁.label with _ | p
          · intro h; cases h
          · intro _; rfl)
      simp only [Comp.map, this, Option.map_some]
      rfl

/-- The rooted graphs of a list of graphs of the form [II, Def 3.3 (4)] with the kinds of `Err`
are integrable, and the expectation of `gammaVal` is the sum of their expectations. -/
private theorem LocalCorr_gammaInt {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2)
    (W L : ℕ) [NeZero L] (z : ℂ) (hVK : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) {N : ℕ}
    (l : Expansion 3) (hl : ∀ g ∈ l, g.2.ThetaRooted ∧ g.2.TKindsErr N) (x b : Zd d L) :
    Integrable (gammaVal l ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b)
        (gaussLaw (Smat P.ψ W L)) ∧
      ∫ ω, gammaVal l ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b ω
          ∂(gaussLaw (Smat P.ψ W L)) =
        (l.map fun g => ∫ ω, (rootRest g.2).2.valR ⟨Pexp (Smat P.ψ W L)⟩
          (rbmData d P Sig W L z) ![x, b, b] ω ∂(gaussLaw (Smat P.ψ W L))).sum := by
  induction l with
  | nil =>
    have : gammaVal ([] : Expansion 3) ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b =
        fun _ => 0 := by funext ω; simp [gammaVal]
    rw [this]
    exact ⟨integrable_zero _ _ _, by simp⟩
  | cons g l ih =>
    obtain ⟨⟨j, v, -, hk, -, -, hxy, hrest, -⟩, hK⟩ := hl g List.mem_cons_self
    have h1 := MainCancel_valR_integrable_err P Sig W L z hVK hz _
      (ErrMain_rootRest_tKindsErr g.2 j v hk hxy (fun c hc => (hrest c hc).1) hK) ![x, b, b]
    obtain ⟨h2, h3⟩ := ih fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')
    have : gammaVal (g :: l) ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b =
        fun ω => (rootRest g.2).2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z)
          ![x, b, b] ω + gammaVal l ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b ω := by
      funext ω; simp [gammaVal]
    rw [this]
    refine ⟨h1.add h2, ?_⟩
    rw [integral_add h1 h2, h3, List.map_cons, List.sum_cons]

/-- **`Σ̃^{(n)}` on the data record of the model is deterministic**: for an `n`-th order
`T`-equation, `Σ̃^{(n)} = Σ_n + Σ_{l ∈ [4, n) even} Σ_l` with `Σ_n` the value of `Σ_n = 𝒬.SigN` on
the deterministic record (the matrix `sigMat` of `Sig` updated at `n` by `𝒬.SigN`). -/
private theorem LocalCorr_sigTilde {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (n : ℕ)
    (hn : 4 ≤ n) (SigN : Expansion 2) (hsh : SelfEnergyShapesUpTo Sig (n - 1))
    (hN : SelfEnergyShape n SigN) (W L : ℕ) [NeZero L] (z : ℂ) (ω : Sample (Zd d L)) :
    sigTilde n SigN (rbmData d P Sig W L z ω) =
      sigMat (Function.update Sig n SigN) (Smat P.ψ W L) z n +
        ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig (Smat P.ψ W L) z l := by
  set Sig' := Function.update Sig n SigN with hSig'
  have hSn : Sig' n = SigN := Function.update_self ..
  have hSl : ∀ l, l < n → Sig' l = Sig l := fun l hl => Function.update_of_ne (Nat.ne_of_lt hl) ..
  unfold sigTilde
  refine congrArg₂ (· + ·) ?_ rfl
  rcases Nat.even_or_odd n with hev | hodd
  · have hsh' : SelfEnergyShapesUpTo Sig' n := by
      intro k hk4 hkn hk
      rcases Nat.lt_or_ge k n with hlt | hge
      · rw [hSl k hlt]
        exact hsh k hk4 (by omega) hk
      · obtain rfl : k = n := le_antisymm hkn hge
        rw [hSn]; exact hN
    have hc := Moment_sigConsistent d P Sig' n hsh' W L z ω n hn (Nat.lt_succ_self n) hev
    change sigMat Sig' (Smat P.ψ W L) z n = _ at hc
    rw [hc, hSn]
    ext x y
    simp only [Matrix.of_apply, Expansion.val]
    refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
    have hall := (hN g hg).2.1
    refine graphVal_det (n - 1) g.2 hall (rbmData d P Sig W L z ω) (rbmData d P Sig' W L z ω) rfl
      rfl rfl rfl (fun o ho => ?_) ![x, y]
    refine chain_congr (rbmData d P Sig W L z ω) (rbmData d P Sig' W L z ω) rfl o fun l hl => ?_
    have hl' : l ≤ n - 1 := by
      have := List.all_eq_true.1 ho l hl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.2
    change sigMat Sig (Smat P.ψ W L) z l = sigMat Sig' (Smat P.ψ W L) z l
    exact MainCancel_sigMat_congr Sig Sig' _ z l fun j hj => (hSl j (by omega)).symm
  · have h0 : SigN = [] := G13.shape_odd_nil hodd hN
    ext x y
    simp [sigMat, hSn, h0, Expansion.val]

/-- **The diagonal entry through the rooted `T`-equation** (with `singularIdStmt` and
`E Q = 0`): for an `n`-th order `T`-equation with `n ≥ 4`, at a variance kernel `S_{W,L}` and
`Im z > 0`, `𝒢_{𝔟𝔟} = (E|G_{𝔟𝔟}|² − |m|² − E T_{𝔟,𝔟𝔟}) − Σ_y Σ̃^{(n)}_{𝔟y} E T_{y,𝔟𝔟} −
E(Γ_A + Γ_Err)_{𝔟,𝔟𝔟}`. -/
private theorem LocalCorr_diagId {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) {n D : ℕ}
    {𝒬 : TEqRec} (hn : 4 ≤ n) (hS : 𝒬.IsTEqStruct Sig n D)
    (hNR : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2) (W L : ℕ) [NeZero L] (z : ℂ)
    (hVK : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) (b : Zd d L) :
    corrMat d P Sig 𝒬 W L z b b =
      (∫ ω, ((‖green (hmat ω) z b b‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw (Smat P.ψ W L)) -
        ((‖msc z‖ ^ 2 : ℝ) : ℂ) -
        ∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (Smat P.ψ W L b x : ℂ) *
          ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw (Smat P.ψ W L))) -
      ∑ y, (sigMat (Function.update Sig n 𝒬.SigN) (Smat P.ψ W L) z n +
          ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig (Smat P.ψ W L) z l) b y *
        ∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (Smat P.ψ W L y x : ℂ) *
          ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw (Smat P.ψ W L)) -
      errMat d P Sig 𝒬 W L z b b := by
  set S := Smat P.ψ W L with hSdef
  set μ := gaussLaw S with hμ
  have hprob : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw S
  have hsym : S.IsSymm := Matrix.IsSymm.ext fun i j => hVK.symm j i
  have hz0 : z.im ≠ 0 := hz.ne'
  set PF : PFamily (Sample (Zd d L)) (Zd d L) := ⟨Pexp S⟩ with hPF
  set Dt := rbmData d P Sig W L z with hDt
  set M := sigMat (Function.update Sig n 𝒬.SigN) S z n +
    ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l with hM
  have hS₀ := hS
  obtain ⟨-, -, hsh, hshN, hShape, hTR, -⟩ := hS
  -- the facts of the graphs
  have hKE : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, g.2.ThetaRooted ∧ g.2.TKindsErr (n - 1) := by
    obtain ⟨⟨h1, h2⟩, -⟩ := hShape
    intro g hg
    refine ⟨hTR g hg, ?_⟩
    rcases List.mem_append.1 hg with hg | hg
    · exact Graph.tKindsErr_of_tKinds _ _ (h1 g hg).2.1
    · exact (h2 g hg).2.1
  have hsub : ∀ l : Expansion 3, (∀ g ∈ l, g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) →
      ∀ g ∈ l, g.2.ThetaRooted ∧ g.2.TKindsErr (n - 1) := fun l hl g hg => hKE g (hl g hg)
  -- the value `v g` of one rooted graph
  set v : (Σ n, Graph 3 n) → ℂ := fun g => ∫ ω, (rootRest g.2).2.valR PF Dt ![b, b, b] ω ∂μ
    with hv
  -- the `Q`-graphs have expectation `0`
  have hQ0 : ∀ g ∈ 𝒬.Q, v g = 0 := by
    intro g hg
    have hall : g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err := by simp [hg]
    obtain ⟨j, w, -, hk, -, hlab, hxy, hrest, -⟩ := hTR g hall
    obtain ⟨⟨h1, -⟩, -, -, hQ, -⟩ := hShape
    have hK := (h1 g (List.mem_append_right _ hg)).2.1
    exact MainCancelId.expQ_zero P Sig W L z hVK hz _
      (LocalCorr_rootRest_tKinds g.2 j w hk hxy (fun c hc => (hrest c hc).1) hK)
      (LocalCorr_rootRest_qGraph g.2 j w hk hlab hxy (fun c hc => (hrest c hc).1) (hQ g hg).1)
      ![b, b, b]
  -- the sum over the graphs
  have hall := LocalCorr_gammaInt P Sig W L z hVK hz (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) hKE b b
  have hRA := LocalCorr_gammaInt P Sig W L z hVK hz (𝒬.R ++ 𝒬.A.filter fun g => g.2.pmBlockB)
    (hsub _ fun g hg => by
      rcases List.mem_append.1 hg with h | h
      · simp [h]
      · simp [(List.mem_filter.1 h).1]) b b
  have hAE := LocalCorr_gammaInt P Sig W L z hVK hz
    (𝒬.A.filter (fun g => !g.2.pmBlockB) ++ 𝒬.Err)
    (hsub _ fun g hg => by
      rcases List.mem_append.1 hg with h | h
      · simp [(List.mem_filter.1 h).1]
      · simp [h]) b b
  have hsplit : ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map v).sum =
      ((𝒬.R ++ 𝒬.A.filter fun g => g.2.pmBlockB).map v).sum +
        ((𝒬.A.filter (fun g => !g.2.pmBlockB) ++ 𝒬.Err).map v).sum := by
    have hA : (𝒬.A.map v).sum = ((𝒬.A.filter fun g => g.2.pmBlockB).map v).sum +
        ((𝒬.A.filter fun g => !g.2.pmBlockB).map v).sum := by
      rw [← List.sum_append, ← List.map_append]
      exact (((List.filter_append_perm _ 𝒬.A).map v).sum_eq).symm
    have hQ : (𝒬.Q.map v).sum = 0 := by
      rw [List.sum_eq_zero]
      intro a ha
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
      exact hQ0 g hg
    simp only [List.map_append, List.sum_append, hA, hQ]
    ring
  -- the identity at every sample
  have hsq : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := fun w => by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; rfl
  set fT : Zd d L → Sample (Zd d L) → ℂ := fun y ω => ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) *
    (S y x : ℂ) * ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ) with hfT
  have hsT : ∀ ω, sigTilde n 𝒬.SigN (modelDataSig Sig S z ω) = M := fun ω =>
    LocalCorr_sigTilde P Sig n hn 𝒬.SigN hsh hshN W L z ω
  have hid : ∀ ω, ((‖green (hmat ω) z b b‖ ^ 2 : ℝ) : ℂ) - fT b ω =
      msc z * star (green (hmat ω) z b b) + gammaVal (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) PF Dt b b ω +
        ∑ y, M b y * fT y ω := by
    intro ω
    have h := singularId Sig n D 𝒬 hS₀ hNR (Zd d L) S z hsym hVK.nonneg hVK.rowSum hz b b ω
    simp only [tGraph_val, yRoot, hsT, gm_empty, ite_true] at h
    exact h
  -- integrability
  have tP : ∀ x y : Zd d L, TestFn fun ω : Sample (Zd d L) => green (hmat ω) z x y *
      star (green (hmat ω) z x y) :=
    fun x y => tf_mul (tf_G hz0 x y) (LocalCorr_tf_Gc hz0 x y)
  have hiA : Integrable (fun ω => ((‖green (hmat ω) z b b‖ ^ 2 : ℝ) : ℂ)) μ :=
    (integ S (tP b b)).congr (Eventually.of_forall fun ω => (hsq _).symm)
  have hiT : ∀ y, Integrable (fT y) μ := fun y => by
    refine integrable_finsetSum _ fun x _ => ?_
    exact ((integ S (tP x b)).const_mul (((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S y x : ℂ))).congr
      (Eventually.of_forall fun ω => by simp only [hsq])
  have hiY : Integrable (fun ω => msc z * star (green (hmat ω) z b b)) μ :=
    (integ S (LocalCorr_tf_Gc hz0 b b)).const_mul _
  have hiS : Integrable (fun ω => ∑ y, M b y * fT y ω) μ :=
    integrable_finsetSum _ fun y _ => (hiT y).const_mul _
  have hE := congrArg (fun F : Sample (Zd d L) → ℂ => ∫ ω, F ω ∂μ) (funext hid)
  have hiYγ : Integrable (fun ω => msc z * star (green (hmat ω) z b b) +
      gammaVal (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) PF Dt b b ω) μ := hiY.add hall.1
  rw [integral_sub hiA (hiT b), integral_add hiYγ hiS, integral_add hiY hall.1,
    integral_const_mul, hall.2, hsplit, ← hRA.2, ← hAE.2,
    integral_finsetSum _ fun y _ => (hiT y).const_mul _] at hE
  simp only [integral_const_mul] at hE
  -- the two sides
  have hC : corrMat d P Sig 𝒬 W L z b b = msc z * (∫ ω, star (green (hmat ω) z b b) ∂μ -
      star (msc z)) + ∫ ω, gammaVal (𝒬.R ++ 𝒬.A.filter fun g => g.2.pmBlockB) PF Dt b b ω ∂μ := by
    simp only [corrMat, Matrix.of_apply, ite_true]
    congr 1
    congr 1
    change ∫ ω, (star (green (hmat ω) z b b) - star (msc z)) ∂μ = _
    rw [integral_sub (integ S (LocalCorr_tf_Gc hz0 b b)) (integrable_const _), integral_const]
    simp
    rfl
  have hEr : errMat d P Sig 𝒬 W L z b b =
      ∫ ω, gammaVal (𝒬.A.filter (fun g => !g.2.pmBlockB) ++ 𝒬.Err) PF Dt b b ω ∂μ := rfl
  rw [hC, hEr]
  simp only [hfT] at hE
  linear_combination -hE + hsq (msc z)

end DiagIdentity

/-! ## The exponents -/

section Exponents

/-- `B_{xx} = W^{−d}`, so that `B_{xx}^{3/2} = W^{−3d/2}`. -/
private theorem LocalCorr_bB_diag {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (x : Zd d L) :
    bB d L W x x ^ ((3 : ℝ) / 2) = (W : ℝ) ^ (-(3 * (d : ℝ) / 2)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hxx : brk d L W x x = W := by
    unfold brk
    rw [sub_self, (zdistInf_eq_zero_iff d L).2 rfl, Nat.cast_zero, zero_add]
  have hb : bB d L W x x = (W : ℝ) ^ (-(d : ℝ)) := by
    change (W : ℝ) ^ (-2 : ℝ) * brk d L W x x ^ (2 - (d : ℝ)) = _
    rw [hxx, ← Real.rpow_add hW0]
    ring_nf
  rw [hb, ← Real.rpow_mul hW0.le]
  ring_nf

/-- **The row sum of a kernel with the entry bound [I, (1.26)]** of an order `l ≥ 4`:
`Σ_x |K_{0x}| ≤ A C W^{−d}` from
`|K_{0x}| ≤ A W^{−(l−4)d/2} B_{0x}² + 1_{x=0} A W^{−(l−2)d/2}`, with
`Σ_x B_{0x}² ≤ C_B W^{−d}` ([II, (8.33)]). -/
private theorem LocalCorr_rowSum {d : ℕ} (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (K : Matrix (Zd d L) (Zd d L) ℂ) (A : ℝ) (l : ℕ),
      4 ≤ l → 0 ≤ A →
      (∀ x, ‖K 0 x‖ ≤ A * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
        (if x = 0 then A * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)) →
      ∑ x, ‖K 0 x‖ ≤ A * C * (W : ℝ) ^ (-(d : ℝ)) := by
  obtain ⟨CB, hCB⟩ := bSum.2 d (by omega)
  refine ⟨|CB| + 1, by positivity, fun L W _ hW K A l hl hA hK => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hl' : (4 : ℝ) ≤ l := by exact_mod_cast hl
  have hxx : brk d L W 0 0 = W := by
    unfold brk
    rw [sub_self, (zdistInf_eq_zero_iff d L).2 rfl, Nat.cast_zero, zero_add]
  have hB2 : ∑ x, bB d L W 0 x ^ 2 ≤ |CB| * (W : ℝ) ^ (-(d : ℝ)) := by
    have h := hCB L W hW 0 0
    rw [hxx] at h
    have e : ∀ x, bB d L W 0 x ^ 2 = bB d L W 0 x * bB d L W x 0 := fun x => by
      rw [bB_comm' x 0]; ring
    simp only [e]
    refine h.trans ?_
    calc CB * (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4))
        = CB * (W : ℝ) ^ (-(d : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hW0]; ring_nf
      _ ≤ |CB| * (W : ℝ) ^ (-(d : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have e1 : (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by nlinarith)
  have e2 : (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) ≤ (W : ℝ) ^ (-(d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
  calc ∑ x, ‖K 0 x‖
      ≤ ∑ x, (A * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
          (if x = 0 then A * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)) :=
        Finset.sum_le_sum fun x _ => hK x
    _ = A * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * ∑ x, bB d L W 0 x ^ 2 +
          A * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mul_sum]
        simp
    _ ≤ A * 1 * (|CB| * (W : ℝ) ^ (-(d : ℝ))) + A * (W : ℝ) ^ (-(d : ℝ)) := by
        gcongr
    _ = A * (|CB| + 1) * (W : ℝ) ^ (-(d : ℝ)) := by ring

end Exponents

/-! ## The two bounds along `adm(c₀, c₁)` -/

section Bounds

/-- **[I, (1.28)] off the diagonal**: for an `n`-th order `T`-equation and `τ > 0` there is `L₀`
with `|𝒢_{x𝔟}| ≤ W^τ B_{x𝔟}^{3/2}` for `x ≠ 𝔟`, `L ≥ L₀` along `adm(c₀, c₁)` and `z ∈ 𝐃(κ, ε)`. -/
private theorem LocalCorr_offDiagFin (hLL : LocalLawStmt) {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec} (hS : 𝒬.IsTEqStruct Sig n D)
    (hSE : SelfEnergiesUpTo d (smatVar P) Sig (n - 1)) {τ : ℝ} (hτ : 0 < τ) :
    ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L, ∀ x b : Zd d L, x ≠ b →
        ‖corrMat d P Sig 𝒬 W L z x b‖ ≤ (W : ℝ) ^ τ * bB d L W x b ^ ((3 : ℝ) / 2) := by
  obtain ⟨K, len, hK0, hlen0, hoff⟩ := LocalCorr_offDiag hLL hd P hc₀ hc₁ hc hκ hε hS hSE
  set a : ℝ := 3 + ((d : ℝ) - 2) / c₁ with ha
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have ha0 : 0 ≤ a := by rw [ha]; have : 0 ≤ ((d : ℝ) - 2) / c₁ := by
                           apply div_nonneg <;> linarith
                         linarith
  obtain ⟨L₁, hL₁⟩ := hoff (τ / 2) (by positivity) (3 / 2 * a + 1) (by positivity)
  obtain ⟨L₂, hL₂⟩ := ErrMain_L₀ (c₀ := c₀) hc₁
    (max (2 ^ d) ((max 1 (K + len)) ^ (1 / (τ / 2))))
  refine ⟨max L₁ L₂, fun W L _ hL hadm z hz x b hxb => ?_⟩
  have hW := hL₂ W L ((le_max_right _ _).trans hL) hadm
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hW1 : (1 : ℝ) ≤ W := h2d.trans ((le_max_left _ _).trans hW)
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hKW : K + len ≤ (W : ℝ) ^ (τ / 2) :=
    const_le_rpow' (by positivity) ((le_max_right _ _).trans hW)
  have hlow := Moment_bB_lower d (by omega) c₀ c₁ hc₀ hc₁ (sizeOf W L) hadm
    ((le_max_left _ _).trans hW) x b
  have hB0 : 0 ≤ bB d L W x b := (bB_pos₁ hW1n x b).le
  have hB32 : (W : ℝ) ^ (-(3 / 2 * a + 1)) ≤ bB d L W x b ^ ((3 : ℝ) / 2) := by
    calc (W : ℝ) ^ (-(3 / 2 * a + 1)) ≤ (W : ℝ) ^ (-a * (3 / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = ((W : ℝ) ^ (-a)) ^ ((3 : ℝ) / 2) := Real.rpow_mul hW0.le _ _
      _ ≤ bB d L W x b ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) hlow (by norm_num)
  have hτ2 : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hA1 : (1 : ℝ) ≤ (W : ℝ) ^ (τ / 2) := Real.one_le_rpow hW1 (by positivity)
  have hb3 : 0 ≤ bB d L W x b ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hB0 _
  refine (hL₁ W L ((le_max_left _ _).trans hL) hadm z hz x b hxb).trans ?_
  calc K * ((W : ℝ) ^ (τ / 2) * bB d L W x b ^ ((3 : ℝ) / 2)) + len * (W : ℝ) ^ (-(3 / 2 * a + 1))
      ≤ K * ((W : ℝ) ^ (τ / 2) * bB d L W x b ^ ((3 : ℝ) / 2)) +
          len * ((W : ℝ) ^ (τ / 2) * bB d L W x b ^ ((3 : ℝ) / 2)) := by
        gcongr
        exact hB32.trans (le_mul_of_one_le_left hb3 hA1)
    _ = (K + len) * ((W : ℝ) ^ (τ / 2) * bB d L W x b ^ ((3 : ℝ) / 2)) := by ring
    _ ≤ (W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ (τ / 2) * bB d L W x b ^ ((3 : ℝ) / 2)) := by gcongr
    _ = (W : ℝ) ^ τ * bB d L W x b ^ ((3 : ℝ) / 2) := by rw [← hτ2]; ring

/-- The exponent count on the diagonal at a fixed `(W, L)`, in the variables `w = W^{τ/16} ≥ 1`
and `q = W^{−d/2} ≤ 1`, with `ρ = wq`, `s₀ = C_s q²`, `r₀ = 2K q²`, `r₁ = K_r w` and
`μ' = η⁻³ P(Bad)`: the bound of `LocalCorr_diagFixed` is at most `4 w⁸ q³`. -/
private lemma LocalCorr_ineqX {w q Kr Cs K μ' G : ℝ} (hw : 1 ≤ w) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hKr : 0 ≤ Kr) (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hμ : 0 ≤ μ')
    (h1 : 2 * ((1 + Kr) * ((1 + Kr) * (2 + 4 * Cs) + (Cs + 2 * K) * (2 + 8 * Cs))) ≤ w ^ 3)
    (h2 : 2 * (9 * (1 + Kr) ^ 2) * μ' ≤ q ^ 3) (h20 : 20 * μ' ≤ q ^ 3)
    (hw5 : 2 * (2 + 4 * Cs) ≤ w ^ 5) (hG : G ≤ w ^ 8 * q ^ 3) :
    2 * G + ((1 + Kr * w) * (2 * (w * q) ^ 3 + 4 * (w * q) ^ 2 * (Cs * q ^ 2) + 9 * μ') +
      (Cs * q ^ 2 + 2 * K * q ^ 2) * (2 * (w * q) ^ 2 + 8 * (Cs * q ^ 2))) +
      (2 * (w * q) ^ 3 + 4 * (w * q) * (Cs * q ^ 2) + 10 * μ') ≤ 4 * (w ^ 8 * q ^ 3) := by
  have hfin := final_ineq w q Kr Cs K μ' hw hq0 hq1 hKr hCs hK hμ h1 h2
  set V := (1 + Kr * w) * (2 * (w * q) ^ 3 + 4 * (w * q) ^ 2 * (Cs * q ^ 2) + 9 * μ') +
    (Cs * q ^ 2 + 2 * K * q ^ 2) * (2 * (w * q) ^ 2 + 8 * (Cs * q ^ 2)) with hV
  have hV0 : 0 ≤ V := by positivity
  have hw0 : 0 ≤ w := by linarith
  have hVle : V ≤ w ^ 8 * q ^ 3 := by
    refine le_trans ?_ hfin
    have h1w : 1 ≤ 1 + Kr * w := by nlinarith
    calc V = 1 * V := (one_mul V).symm
      _ ≤ (1 + Kr * w) * V := mul_le_mul_of_nonneg_right h1w hV0
  have hq3n : 0 ≤ q ^ 3 := by positivity
  have hw3 : 0 ≤ w ^ 3 := by positivity
  have hw13 : w ≤ w ^ 3 := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ 3 := pow_le_pow_right₀ hw (by norm_num)
  have e1 : 2 * (w * q) ^ 3 + 4 * (w * q) * (Cs * q ^ 2) ≤ (2 + 4 * Cs) * w ^ 3 * q ^ 3 := by
    have : 4 * (w * q) * (Cs * q ^ 2) ≤ 4 * Cs * w ^ 3 * q ^ 3 := by
      calc 4 * (w * q) * (Cs * q ^ 2) = 4 * Cs * w * q ^ 3 := by ring
        _ ≤ 4 * Cs * w ^ 3 * q ^ 3 := by gcongr
    have e : 2 * (w * q) ^ 3 = 2 * w ^ 3 * q ^ 3 := by ring
    rw [e]
    linarith
  have e2 : (2 + 4 * Cs) * w ^ 3 * q ^ 3 ≤ w ^ 8 * q ^ 3 / 2 := by
    have e : w ^ 8 * q ^ 3 / 2 = (w ^ 5 / 2) * (w ^ 3 * q ^ 3) := by ring
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e3 : 10 * μ' ≤ w ^ 8 * q ^ 3 / 2 := by
    have : q ^ 3 ≤ w ^ 8 * q ^ 3 := le_mul_of_one_le_left hq3n (one_le_pow₀ hw)
    linarith
  linarith

/-- **[I, (1.28)] on the diagonal**: for an `n`-th order `T`-equation with `n ≥ 4`, `D ≥ n + 2`
and self-energies `Σ_4, …, Σ_n`, and `0 < τ ≤ 1`, there is `L₀` with
`|𝒢_{𝔟𝔟}| ≤ W^τ W^{−3d/2}` for `L ≥ L₀` along `adm(c₀, c₁)` and `z ∈ 𝐃(κ, ε)`. -/
private theorem LocalCorr_diag (hLL : LocalLawStmt) {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec} (hn : 4 ≤ n) (hnD : n + 2 ≤ D)
    (hS : 𝒬.IsTEqStruct Sig n D) (hNR : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2)
    (hSE : SelfEnergiesUpTo d (smatVar P) Sig n) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L, ∀ b : Zd d L,
        ‖corrMat d P Sig 𝒬 W L z b b‖ ≤ (W : ℝ) ^ τ * (W : ℝ) ^ (-(3 * (d : ℝ) / 2)) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  set D₀ : ℝ := 2 * (d : ℝ) - 4 with hD₀
  have hD₀0 : 0 < D₀ := by rw [hD₀]; linarith
  set τs : ℝ := τ / (16 * D₀) with hτsdef
  have hτs : 0 < τs := by positivity
  have hτsD : τs * D₀ = τ / 16 := by rw [hτsdef]; field_simp
  set Dll : ℝ := 4 * (d : ℝ) + 7 with hDll
  -- the inputs
  obtain ⟨Cs, hCs⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨Csym, hCsym⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨W₃, hker⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨K, W₄, hK⟩ := Splus_decay_msc d c₀ c₁ hc₀ hc₁ P.ψ c' hc' Csym κ τs D₀ hκ hτs hD₀0
  obtain ⟨CR, hCR0, hCR⟩ := splusBound_rowSum d hd
  obtain ⟨W₅, hVK⟩ := Smat_isVarKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨CM, hCM0, hrow⟩ := LocalCorr_rowSum hd
  obtain ⟨L₁, hL₁⟩ := hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ ε (τ / 8) Dll hε (by positivity)
    (by rw [hDll]; positivity)
  obtain ⟨L₂, hL₂⟩ := diagMean hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε (τ / 2) (by positivity)
  obtain ⟨L₃, hL₃⟩ := errBound hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig n D 𝒬 hn hnD hS hNR hSE
    (τ / 2) (by positivity)
  -- [I, (1.26)] for `Σ_n = 𝒬.SigN` and for `Σ_l`, `l < n` even
  set Sig' := Function.update Sig n 𝒬.SigN with hSig'
  have hSl : ∀ l, l < n → Sig' l = Sig l := fun l hl => Function.update_of_ne (Nat.ne_of_lt hl) ..
  obtain ⟨L₄, hL₄⟩ := G13.entrywise d hd P n Sig' hn
    (MainCancel_selfEnergiesUpTo_congr (smatVar P) Sig Sig' (n - 1)
      (fun j hj => (hSl j (by omega)).symm) (fun k h4 hk he => hSE k h4 (by omega) he))
    (by rw [hSig', Function.update_self]; exact hS.2.2.2.1)
    κ ε c₀ c₁ hκ hε hc₀ hc₁ hc c₁ hc₁
  have hEl : ∀ l, ∃ L₀ : ℕ, 4 ≤ l → l < n → Even l → ∀ (W L : ℕ) [NeZero L], L₀ ≤ L →
      (W, L) ∈ adm c₀ c₁ → ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        ‖sigMat Sig (smatVar P W L) z l 0 x‖ ≤
          (L : ℝ) ^ c₁ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
            (if x = 0 then (L : ℝ) ^ c₁ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0) := by
    intro l
    by_cases h : 4 ≤ l ∧ l < n ∧ Even l
    · obtain ⟨L₀, hL₀⟩ := G13.entrywise d hd P l Sig h.1
        (fun k h4 hk he => hSE k h4 (by omega) he) (hSE l h.1 (by omega) h.2.2).1
        κ ε c₀ c₁ hκ hε hc₀ hc₁ hc c₁ hc₁
      exact ⟨L₀, fun _ _ _ => hL₀⟩
    · exact ⟨0, fun h4 hl he => absurd ⟨h4, hl, he⟩ h⟩
  choose L₅f hL₅f using hEl
  set L₅ := ∑ l ∈ Finset.range n, L₅f l with hL₅
  -- the constants
  set Cs' := |Cs| with hCs'
  set K' := |K| with hK'
  set Kr := K' * CR with hKr
  set K₁ := (1 + Kr) * ((1 + Kr) * (2 + 4 * Cs') + (Cs' + 2 * K') * (2 + 8 * Cs')) with hK₁
  set K₂ := 9 * (1 + Kr) ^ 2 + 10 with hK₂
  set KT := ((n : ℝ) + 1) * CM * (2 + 4 * Cs') with hKT
  have hKr0 : 0 ≤ Kr := by positivity
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hKT0 : 0 ≤ KT := by positivity
  set e₁ : ℝ := (2 * K₁) ^ (16 / (3 * τ)) with he₁
  set e₂ : ℝ := (max 1 (2 * (2 + 4 * Cs'))) ^ (1 / (5 * τ / 16)) with he₂
  set e₃ : ℝ := (max 1 6) ^ (1 / (τ / 2)) with he₃
  have he₁0 : 0 ≤ e₁ := by positivity
  have he₂0 : 0 ≤ e₂ := by positivity
  have he₃0 : 0 ≤ e₃ := by positivity
  set Wt : ℝ := max (max (max W₃ W₄) (max W₅ 1)) (max (max e₁ e₂) (max e₃ KT)) with hWt
  obtain ⟨Lw, hLw⟩ := ErrMain_L₀ (c₀ := c₀) hc₁ Wt
  refine ⟨max (max (max L₁ L₂) (max L₃ L₄)) (max L₅ (max Lw ⌈2 * K₂ + 1⌉₊)),
    fun W L _ hL hadm z hz b => ?_⟩
  have hLL₁ : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    |>.trans hL
  have hLL₂ : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    |>.trans hL
  have hLL₃ : L₃ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
    |>.trans hL
  have hLL₄ : L₄ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
    |>.trans hL
  have hLL₅ : L₅ ≤ L := le_trans (le_max_left _ _) (le_max_right _ _) |>.trans hL
  have hLLw : Lw ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _) |>.trans hL
  have hLK : ⌈2 * K₂ + 1⌉₊ ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _) |>.trans hL
  have hW : Wt ≤ W := hLw W L hLLw hadm
  have hWa : max (max W₃ W₄) (max W₅ 1) ≤ (W : ℝ) := (le_max_left _ _).trans hW
  have hWb : max (max e₁ e₂) (max e₃ KT) ≤ (W : ℝ) := (le_max_right _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hWa
  have hW0 : (0 : ℝ) < W := by linarith only [hW1]
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW₃ : W₃ ≤ (W : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hWa
  have hW₄ : W₄ ≤ (W : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hWa
  have hW₅ : W₅ ≤ (W : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hWa
  have hWe₁ : e₁ ≤ (W : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hWb
  have hWe₂ : e₂ ≤ (W : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hWb
  have hWe₃ : e₃ ≤ (W : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hWb
  have hWKT : KT ≤ (W : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hWb
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hWL : (W : ℝ) ≤ L := hadm.2.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hc₀] : 1 - c₀ ≤ 1))
  have hLc : (L : ℝ) ^ c₁ ≤ W := hadm.1
  -- the spectral parameter
  have hzim : 0 < z.im := lt_of_lt_of_le (by positivity) hz.2.1
  have hz1 : z.im ≤ 1 := hz.2.2
  have hzre : |z.re| < 2 - κ := hz.1
  -- the variance matrix
  set S := Smat P.ψ W L with hSdef
  have hVKW : IsVarKernel S := hVK W L hadm hW₅
  have hSs : S.IsSymm := Matrix.IsSymm.ext fun i j => hVKW.symm j i
  have hS0 : ∀ x y, 0 ≤ S x y := hVKW.nonneg
  have hS1 : ∀ x, ∑ y, S x y = 1 := hVKW.rowSum
  have hSv : smatVar P W L = S := smatVar_eq_of_isSymm P hSs
  -- the scales `w = W^{τ/16}` and `q = W^{−d/2}`
  set w : ℝ := (W : ℝ) ^ (τ / 16) with hw
  set q : ℝ := (W : ℝ) ^ (-((d : ℝ) / 2)) with hq
  have hw1 : 1 ≤ w := Real.one_le_rpow hW1 (by positivity)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hq2 : q ^ 2 = (W : ℝ) ^ (-(d : ℝ)) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  have hq3 : q ^ 3 = (W : ℝ) ^ (-(3 * (d : ℝ) / 2)) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  have hw2 : w ^ 2 = (W : ℝ) ^ (τ / 8) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  have hw8 : w ^ 8 = (W : ℝ) ^ (τ / 2) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  have hρ1 : w * q ≤ 1 := by
    rw [hw, hq, ← Real.rpow_add hW0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  -- `s_{xy} ≤ |C_s| W^{−d}`
  have hs : ∀ x y, S x y ≤ Cs' * q ^ 2 := by
    intro x y
    have h := hCs W L hadm (x - y)
    rw [pow_zero, one_mul] at h
    have e : S x y = fWL P.ψ W L (x - y) := rfl
    rw [e, hq2, Real.rpow_neg hW0.le, Real.rpow_natCast, ← div_eq_mul_inv]
    exact (le_abs_self _).trans (h.trans (div_le_div_of_nonneg_right (le_abs_self _)
      (by positivity)))
  -- `S^+`
  have hSp : ∀ x y, ‖Splus (msc z) S x y‖ ≤ K' * splusBound W τs D₀ x y := fun x y =>
    ((hK W L hadm hW₄ S (hker W L hadm hW₃) (hCsym W L hadm) z hzim hzre x y).1).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by unfold splusBound; positivity))
  have hR0 : ∀ x y, ‖Splus (msc z) S x y‖ ≤ 2 * K' * q ^ 2 := fun x y => by
    refine (hSp x y).trans ?_
    have h := mul_le_mul_of_nonneg_left (splusBound_le_two (L := L) hWn τs D₀
      (by rw [hD₀]; linarith) x y) (abs_nonneg K)
    rw [hq2]
    linarith
  have hR1 : ∀ x, ∑ y, ‖Splus (msc z) S x y‖ ≤ Kr * w := fun x => by
    calc ∑ y, ‖Splus (msc z) S x y‖ ≤ ∑ y, K' * splusBound W τs D₀ x y :=
          Finset.sum_le_sum fun y _ => hSp x y
      _ = K' * ∑ y, splusBound W τs D₀ x y := by rw [Finset.mul_sum]
      _ ≤ K' * (CR * (W : ℝ) ^ (τs * D₀)) :=
          mul_le_mul_of_nonneg_left (hCR L W hWn τs hτs.le x) (abs_nonneg _)
      _ = Kr * w := by rw [hτsD, hKr, hw]; ring
  -- the event of the local law
  set bad : Zd d L → Zd d L → Set (Sample (Zd d L)) := fun x y => {ω | ∃ E : ℝ,
    E ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ η : ℝ, (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ η ∧ η ≤ 1 ∧
      (W : ℝ) ^ (τ / 8) * bB d L W x y <
        ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * Complex.I))
          (msc ((E : ℂ) + (η : ℂ) * Complex.I)) x y‖ ^ 2}
    with hbad
  have hbadμ : ∀ x y, gaussLaw S (bad x y) ≤ ENNReal.ofReal ((L : ℝ) ^ (-Dll)) :=
    fun x y => hL₁ ⟨(W, L), NeZero.ne L⟩ hLL₁ hadm x y
  set Bad := ⋃ x, ⋃ y, bad x y with hBad
  have hgood : ∀ ω, ω ∉ Bad → ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ w * q := by
    intro ω hω x y
    have hxy : ω ∉ bad x y := fun h => hω (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, h⟩⟩)
    have hle : ‖entryErr (green (hmat ω) z) (msc z) x y‖ ^ 2 ≤
        (W : ℝ) ^ (τ / 8) * bB d L W x y := by
      by_contra hlt
      push Not at hlt
      refine hxy ⟨z.re, ⟨by linarith [neg_abs_le z.re], by linarith [le_abs_self z.re]⟩, z.im,
        hz.2.1, hz1, ?_⟩
      rwa [Complex.re_add_im]
    have hB : (W : ℝ) ^ (τ / 8) * bB d L W x y ≤ (w * q) ^ 2 := by
      rw [mul_pow, hw2, hq2]
      exact mul_le_mul_of_nonneg_left (bB_le_rpow (by omega) hWn x y) (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (hle.trans hB)
  -- `P(Bad) ≤ L^{2d} L^{−D}`
  have hμ : (gaussLaw S Bad).toReal ≤
      (L : ℝ) ^ (d : ℝ) * ((L : ℝ) ^ (d : ℝ) * (L : ℝ) ^ (-Dll)) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc gaussLaw S Bad ≤ ∑ x, gaussLaw S (⋃ y, bad x y) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ x : Zd d L, ∑ y : Zd d L, ENNReal.ofReal ((L : ℝ) ^ (-Dll)) :=
          Finset.sum_le_sum fun x _ => (measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun y _ => hbadμ x y)
      _ = ENNReal.ofReal ((L : ℝ) ^ (d : ℝ) * ((L : ℝ) ^ (d : ℝ) * (L : ℝ) ^ (-Dll))) := by
          simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            Real.rpow_natCast, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  -- `η⁻¹ ≤ L²`
  have hΛ : z.im⁻¹ ≤ (L : ℝ) ^ (2 : ℝ) := by
    have h1 : (L : ℝ) ^ (-(2 - ε)) ≤ z.im := by
      calc (L : ℝ) ^ (-(2 - ε)) = 1 / (L : ℝ) ^ (2 - ε) := by
            rw [Real.rpow_neg hLpos.le, one_div]
        _ ≤ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) :=
            div_le_div_of_nonneg_right (one_le_pow₀ hW1) (by positivity)
        _ ≤ z.im := hz.2.1
    calc z.im⁻¹ ≤ ((L : ℝ) ^ (-(2 - ε)))⁻¹ := inv_anti₀ (by positivity) h1
      _ = (L : ℝ) ^ (2 - ε) := by rw [Real.rpow_neg hLpos.le, inv_inv]
      _ ≤ (L : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hε])
  have hΛ1 : 1 ≤ z.im⁻¹ := one_le_inv_iff₀.mpr ⟨hzim, hz1⟩
  set μ' := z.im⁻¹ ^ 3 * (gaussLaw S Bad).toReal with hμ'
  have hP0 : 0 ≤ (gaussLaw S Bad).toReal := ENNReal.toReal_nonneg
  have hμ'0 : 0 ≤ μ' := by positivity
  have hμ'le : μ' ≤ (L : ℝ) ^ (-1 : ℝ) * (L : ℝ) ^ (-(2 * (d : ℝ))) := by
    calc μ' ≤ ((L : ℝ) ^ (2 : ℝ)) ^ 3 *
          ((L : ℝ) ^ (d : ℝ) * ((L : ℝ) ^ (d : ℝ) * (L : ℝ) ^ (-Dll))) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hΛ 3) hμ ENNReal.toReal_nonneg
            (by positivity)
      _ = (L : ℝ) ^ (-1 : ℝ) * (L : ℝ) ^ (-(2 * (d : ℝ))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le, ← Real.rpow_add hLpos,
            ← Real.rpow_add hLpos, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos, hDll]
          ring_nf
  have h2' : 2 * K₂ * μ' ≤ q ^ 3 := by
    have hLK' : 2 * K₂ + 1 ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hLK)
    have hinv : 2 * K₂ * (L : ℝ) ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_one hLpos]
      linarith
    have hq3' : (L : ℝ) ^ (-(2 * (d : ℝ))) ≤ q ^ 3 := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      calc (L : ℝ) ^ (-(2 * (d : ℝ))) ≤ (L : ℝ) ^ (-((d : ℝ) / 2) * ((3 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith)
        _ ≤ (W : ℝ) ^ (-((d : ℝ) / 2) * ((3 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hW0 hWL (by push_cast; linarith)
    have hK₂0 : 0 ≤ K₂ := by positivity
    calc 2 * K₂ * μ' ≤ 2 * K₂ * ((L : ℝ) ^ (-1 : ℝ) * (L : ℝ) ^ (-(2 * (d : ℝ)))) :=
          mul_le_mul_of_nonneg_left hμ'le (by positivity)
      _ = (2 * K₂ * (L : ℝ) ^ (-1 : ℝ)) * (L : ℝ) ^ (-(2 * (d : ℝ))) := by ring
      _ ≤ 1 * (L : ℝ) ^ (-(2 * (d : ℝ))) := mul_le_mul_of_nonneg_right hinv (by positivity)
      _ ≤ q ^ 3 := by rw [one_mul]; exact hq3'
  have hsq0 := sq_nonneg (1 + Kr)
  have h2 : 2 * (9 * (1 + Kr) ^ 2) * μ' ≤ q ^ 3 :=
    le_trans (mul_le_mul_of_nonneg_right (by rw [hK₂]; linarith only [hsq0]) hμ'0) h2'
  have h20 : 20 * μ' ≤ q ^ 3 :=
    le_trans (mul_le_mul_of_nonneg_right (by rw [hK₂]; linarith only [hsq0]) hμ'0) h2'
  have h1 : 2 * K₁ ≤ w ^ 3 := by
    have e : w ^ 3 = (W : ℝ) ^ (3 * τ / 16) := by
      rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
    rw [e]
    calc 2 * K₁ = ((2 * K₁) ^ (16 / (3 * τ))) ^ (3 * τ / 16) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show 16 / (3 * τ) * (3 * τ / 16) = (1 : ℝ) by field_simp, Real.rpow_one]
      _ ≤ (W : ℝ) ^ (3 * τ / 16) := Real.rpow_le_rpow (by positivity) hWe₁ (by positivity)
  have hw5 : 2 * (2 + 4 * Cs') ≤ w ^ 5 := by
    have e : w ^ 5 = (W : ℝ) ^ (5 * τ / 16) := by
      rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
    rw [e]
    exact const_le_rpow' (by positivity) hWe₂
  have h6 : (6 : ℝ) ≤ (W : ℝ) ^ (τ / 2) := const_le_rpow' (by positivity) hWe₃
  -- the identity on the diagonal at `𝔟 = 0`
  have htr := (modelTransInv d P Sig 𝒬 W L z hSs hzim).2.2.1 0 0 b
  simp only [zero_add] at htr
  rw [htr, LocalCorr_diagId P Sig hn hS hNR W L z hVKW hzim 0]
  -- the three terms
  have hX := LocalCorr_diagFixed S hSs hS0 hS1 hs hzim hz1 hR0 hR1 (by positivity) hρ1 Bad
    hgood 0
  have hg : ‖∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw S) - msc z‖ ≤ w ^ 8 * q ^ 3 := by
    rw [hw8, hq3]
    exact hL₂ W L hLL₂ hadm z hz 0
  have hfin := final_ineq w q Kr Cs' K' μ' hw1 hq0 hq1 hKr0 (abs_nonneg _) (abs_nonneg _) hμ'0
    h1 h2
  have hXb : ‖∫ ω, ((‖green (hmat ω) z 0 0‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw S) - ((‖msc z‖ ^ 2 : ℝ) : ℂ) -
      ∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S 0 x : ℂ) * ((‖green (hmat ω) z x 0‖ ^ 2 : ℝ) : ℂ)
        ∂(gaussLaw S)‖ ≤ 4 * (w ^ 8 * q ^ 3) := by
    refine hX.trans (le_of_eq_of_le ?_ (LocalCorr_ineqX hw1 hq0 hq1 hKr0 (abs_nonneg _)
      (abs_nonneg _) hμ'0 h1 h2 h20 hw5 hg))
    rw [hμ']
    ring
  -- the row of `Σ̃^{(n)}`
  have hA0 : (0 : ℝ) ≤ (L : ℝ) ^ c₁ := by positivity
  have hrowN : ∑ y, ‖sigMat (Function.update Sig n 𝒬.SigN) S z n 0 y‖ ≤
      (L : ℝ) ^ c₁ * CM * (W : ℝ) ^ (-(d : ℝ)) :=
    hrow L W hWn _ _ n hn hA0 fun x => by
      have h := hL₄ W L hLL₄ hadm z hz x
      rw [hSv] at h
      exact h
  have hrowl : ∀ l ∈ (Finset.Ico 4 n).filter Even, ∑ y, ‖sigMat Sig S z l 0 y‖ ≤
      (L : ℝ) ^ c₁ * CM * (W : ℝ) ^ (-(d : ℝ)) := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
    obtain ⟨h4, hln⟩ := Finset.mem_Ico.1 hl1
    have hLl : L₅f l ≤ L := le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le (L₅f i))
      (Finset.mem_range.2 hln)) hLL₅
    exact hrow L W hWn _ _ l h4 hA0 fun x => by
      have h := hL₅f l h4 hln hl2 W L hLl hadm z hz x
      rw [hSv] at h
      exact h
  have hcard : (((Finset.Ico 4 n).filter Even).card : ℝ) ≤ n := by
    have : ((Finset.Ico 4 n).filter Even).card ≤ n :=
      (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hMrow : ∑ y, ‖(sigMat (Function.update Sig n 𝒬.SigN) S z n +
      ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l) 0 y‖ ≤
      ((n : ℝ) + 1) * CM * (W : ℝ) * q ^ 2 := by
    have hA : (L : ℝ) ^ c₁ * CM * (W : ℝ) ^ (-(d : ℝ)) ≤ CM * (W : ℝ) * q ^ 2 := by
      rw [hq2]
      have := mul_le_mul_of_nonneg_right hLc (show 0 ≤ CM * (W : ℝ) ^ (-(d : ℝ)) by positivity)
      linarith only [this]
    have hA' : 0 ≤ CM * (W : ℝ) * q ^ 2 := by positivity
    calc ∑ y, ‖(sigMat (Function.update Sig n 𝒬.SigN) S z n +
          ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l) 0 y‖
        ≤ ∑ y, (‖sigMat (Function.update Sig n 𝒬.SigN) S z n 0 y‖ +
            ∑ l ∈ (Finset.Ico 4 n).filter Even, ‖sigMat Sig S z l 0 y‖) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [Matrix.add_apply, Matrix.sum_apply]
          exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ = ∑ y, ‖sigMat (Function.update Sig n 𝒬.SigN) S z n 0 y‖ +
            ∑ l ∈ (Finset.Ico 4 n).filter Even, ∑ y, ‖sigMat Sig S z l 0 y‖ := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ ≤ CM * (W : ℝ) * q ^ 2 + ∑ _l ∈ (Finset.Ico 4 n).filter Even, CM * (W : ℝ) * q ^ 2 :=
          add_le_add (hrowN.trans hA) (Finset.sum_le_sum fun l hl => (hrowl l hl).trans hA)
      _ = (1 + (((Finset.Ico 4 n).filter Even).card : ℝ)) * (CM * (W : ℝ) * q ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (1 + (n : ℝ)) * (CM * (W : ℝ) * q ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith only [hcard]) hA'
      _ = ((n : ℝ) + 1) * CM * (W : ℝ) * q ^ 2 := by ring
  -- `E T_{y,00}`
  have hTy : ∀ y, ‖∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S y x : ℂ) *
      ((‖green (hmat ω) z x 0‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw S)‖ ≤ (2 + 4 * Cs') * w ^ 2 * q ^ 2 := by
    intro y
    refine (LocalCorr_t_bound S hS0 hS1 hs hzim hz1 hρ1 Bad hgood y 0).trans ?_
    have hΛP : z.im⁻¹ ^ 2 * (gaussLaw S Bad).toReal ≤ q ^ 2 := by
      have e1 : z.im⁻¹ ^ 2 * (gaussLaw S Bad).toReal ≤ μ' := by
        rw [hμ']
        refine mul_le_mul_of_nonneg_right ?_ hP0
        calc z.im⁻¹ ^ 2 = z.im⁻¹ ^ 2 * 1 := (mul_one _).symm
          _ ≤ z.im⁻¹ ^ 2 * z.im⁻¹ := mul_le_mul_of_nonneg_left hΛ1 (by positivity)
          _ = z.im⁻¹ ^ 3 := by ring
      have e2 : q ^ 3 ≤ q ^ 2 := pow_le_pow_of_le_one hq0 hq1 (by norm_num)
      linarith only [e1, e2, h20, hμ'0]
    have hw2' : 1 ≤ w ^ 2 := one_le_pow₀ hw1
    have hq2n : 0 ≤ q ^ 2 := by positivity
    have hc0 : 0 ≤ Cs' := abs_nonneg _
    have e3 : q ^ 2 ≤ w ^ 2 * q ^ 2 := le_mul_of_one_le_left hq2n hw2'
    have e4 : Cs' * q ^ 2 ≤ Cs' * (w ^ 2 * q ^ 2) := mul_le_mul_of_nonneg_left e3 hc0
    calc (w * q) ^ 2 + 4 * (Cs' * q ^ 2) + z.im⁻¹ ^ 2 * (gaussLaw S Bad).toReal
        ≤ w ^ 2 * q ^ 2 + 4 * (Cs' * (w ^ 2 * q ^ 2)) + w ^ 2 * q ^ 2 := by
          rw [mul_pow]; linarith only [e3, e4, hΛP]
      _ = (2 + 4 * Cs') * w ^ 2 * q ^ 2 := by ring
  have hSumT : ‖∑ y, (sigMat (Function.update Sig n 𝒬.SigN) S z n +
      ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l) 0 y *
        ∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S y x : ℂ) *
          ((‖green (hmat ω) z x 0‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw S)‖ ≤ w ^ 8 * q ^ 3 := by
    have hT0 : 0 ≤ (2 + 4 * Cs') * w ^ 2 * q ^ 2 := by positivity
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y, ‖(sigMat (Function.update Sig n 𝒬.SigN) S z n +
          ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l) 0 y *
            ∫ ω, ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S y x : ℂ) *
              ((‖green (hmat ω) z x 0‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw S)‖
        ≤ ∑ y, ‖(sigMat (Function.update Sig n 𝒬.SigN) S z n +
          ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l) 0 y‖ *
            ((2 + 4 * Cs') * w ^ 2 * q ^ 2) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hTy y) (norm_nonneg _)
      _ = (∑ y, ‖(sigMat (Function.update Sig n 𝒬.SigN) S z n +
          ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l) 0 y‖) *
            ((2 + 4 * Cs') * w ^ 2 * q ^ 2) := by rw [Finset.sum_mul]
      _ ≤ (((n : ℝ) + 1) * CM * (W : ℝ) * q ^ 2) * ((2 + 4 * Cs') * w ^ 2 * q ^ 2) :=
          mul_le_mul_of_nonneg_right hMrow hT0
      _ = (KT * ((W : ℝ) * q)) * (w ^ 2 * q ^ 3) := by rw [hKT]; ring
      _ ≤ 1 * (w ^ 8 * q ^ 3) := by
          have hWq : (W : ℝ) * ((W : ℝ) * q) ≤ 1 := by
            rw [hq, ← mul_assoc, ← pow_two, ← Real.rpow_natCast, ← Real.rpow_add hW0]
            exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by push_cast; linarith only [hd'])
          have hWq0 : 0 ≤ (W : ℝ) * q := by positivity
          have h1' : KT * ((W : ℝ) * q) ≤ 1 :=
            (mul_le_mul_of_nonneg_right hWKT hWq0).trans hWq
          have h2'' : w ^ 2 * q ^ 3 ≤ w ^ 8 * q ^ 3 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hw1 (by norm_num)) (by positivity)
          exact mul_le_mul h1' h2'' (by positivity) zero_le_one
      _ = w ^ 8 * q ^ 3 := one_mul _
  -- `E(Γ_A + Γ_Err)_{0,00}`
  have hErr : ‖errMat d P Sig 𝒬 W L z 0 0‖ ≤ w ^ 8 * q ^ 3 := by
    refine (hL₃ W L hLL₃ hadm z hz 0 0).1.trans ?_
    rw [hw8, hq3]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1
      (by nlinarith only [hn', hd'])) (by positivity)
  -- the sum
  have hw80 : 0 ≤ w ^ 8 * q ^ 3 := by positivity
  rw [← hq3, show (W : ℝ) ^ τ = w ^ 8 * w ^ 8 by
    rw [hw8, ← Real.rpow_add hW0]; ring_nf]
  calc _ ≤ ‖_‖ + ‖_‖ + ‖errMat d P Sig 𝒬 W L z 0 0‖ := norm_sub_le_of_le
          (norm_sub_le _ _) le_rfl
    _ ≤ 4 * (w ^ 8 * q ^ 3) + w ^ 8 * q ^ 3 + w ^ 8 * q ^ 3 :=
        add_le_add (add_le_add hXb hSumT) hErr
    _ = 6 * (w ^ 8 * q ^ 3) := by ring
    _ ≤ w ^ 8 * (w ^ 8 * q ^ 3) := mul_le_mul_of_nonneg_right (hw8 ▸ h6) hw80
    _ = w ^ 8 * w ^ 8 * q ^ 3 := by ring

end Bounds

/-- **[I, (1.28)]**: under the local law [I, Theorem 1.4], for `d ≥ 8`, a profile, constants
`c₀, c₁, κ, ε > 0`, an `n`-th order `T`-equation `𝒬` with error order `D ≥ n + 2`, `n ≥ 4`, of the
form [II, Def 3.3 (4)] without `P`/`Q` labels at `⊗`, and self-energies `Σ_4, …, Σ_n`: for every
`τ > 0` there is `L₀` such that the local correction of [I, (8.16)] satisfies
`|𝒢_{x𝔟}| ≤ L^τ B_{x𝔟}^{3/2}` for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)`, `z ∈ 𝐃(κ, ε)` and all `x, 𝔟`. -/
theorem localCorr : localCorrStmt := by
  intro hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig n D 𝒬 hn hnD hS hNR hSE τ hτ
  -- the window `adm(c₀', c₁')` with `c₀' + c₁' < 1` contains `adm(c₀, c₁)`
  set c₀' := min c₀ (1 / 2) with hc₀'def
  set c₁' := min c₁ (1 / 4) with hc₁'def
  have hc₀' : 0 < c₀' := lt_min hc₀ (by norm_num)
  have hc₁' : 0 < c₁' := lt_min hc₁ (by norm_num)
  have hc' : c₀' + c₁' < 1 := by
    have := min_le_right c₀ (1 / 2); have := min_le_right c₁ (1 / 4); linarith
  have hadm' : ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → (W, L) ∈ adm c₀' c₁' := by
    intro W L _ h
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    exact ⟨(Real.rpow_le_rpow_of_exponent_le hL1 (min_le_left _ _)).trans h.1,
      h.2.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [min_le_left c₀ (1 / 2)]))⟩
  set τ₁ := min τ 1 with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min hτ one_pos
  have hSE' : SelfEnergiesUpTo d (smatVar P) Sig (n - 1) :=
    fun k h4 hk he => hSE k h4 (by omega) he
  obtain ⟨L₁, hL₁⟩ := LocalCorr_offDiagFin hLL hd P hc₀' hc₁' hc' hκ hε hS hSE' hτ₁
  obtain ⟨L₂, hL₂⟩ := LocalCorr_diag hLL hd P hc₀' hc₁' hc' hκ hε hn hnD hS hNR hSE hτ₁
    (min_le_right _ _)
  refine ⟨max L₁ L₂, fun W L _ hL hadm z hz x b => ?_⟩
  have hadm₁ := hadm' W L hadm
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hW1 : (1 : ℝ) ≤ W := (Real.one_le_rpow hL1 hc₁.le).trans hadm.1
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hWL : (W : ℝ) ≤ L := hadm.2.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : 1 - c₀ ≤ 1))
  have hB0 : 0 ≤ bB d L W x b ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (bB_pos₁ hWn x b).le _
  have key : ‖corrMat d P Sig 𝒬 W L z x b‖ ≤ (W : ℝ) ^ τ₁ * bB d L W x b ^ ((3 : ℝ) / 2) := by
    by_cases hxb : x = b
    · subst hxb
      rw [LocalCorr_bB_diag hWn x]
      exact hL₂ W L ((le_max_right _ _).trans hL) hadm₁ z hz x
    · exact hL₁ W L ((le_max_left _ _).trans hL) hadm₁ z hz x b hxb
  refine key.trans (mul_le_mul_of_nonneg_right ?_ hB0)
  calc (W : ℝ) ^ τ₁ ≤ (W : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _)
    _ ≤ (L : ℝ) ^ τ := Real.rpow_le_rpow (by positivity) hWL hτ.le

end RBM8D
