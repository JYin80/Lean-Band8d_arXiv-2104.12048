import RBM8D.SelfEnergy.Lem512
import RBM8D.Bound.GraphSum
import RBM8D.LocalLaw.Defs
import RBM8D.LocalLaw.Eta1
import RBM8D.LocalLaw.Continuity
import RBM8D.LocalLaw.Entrywise
import RBM8D.LocalLaw.Moment
import RBM8D.LocalLaw.QTermOf
import RBM8D.LocalLaw.LabelPaths
import RBM8D.LocalLaw.LabelRemoval
import RBM8D.Prob.Net
import Batteries.Tactic.OpenPrivate

/-!
# The bounds of [I, Lemma 5.12] on the graphs of `A` and `Err` without internal atoms

[I, (5.42)–(5.43)] in the strong norm, at `𝔟₁ = 𝔟₂ = 𝔟` and summed over `𝔞, 𝔟`, for the graphs
without internal atoms. Such a graph is a product of entries at the three fixed atoms: its only
component at `⊗` is a `Θ` edge from `⊗` to `⊕` or `⊖`, of value `Θ^{(o)}_{𝔞𝔟}`, and every other
component is an entry at `(𝔟, 𝔟)`, of size `W^{−q d/2}` for its scaling order `q`, except a dotted
edge between `⊕` and `⊖`, which is `1` at `⊕ = ⊖`.

* `Lem512Zero.detStmt`: for a single matrix `G` with `‖G − m‖_{w;(1,2)} ≤ W^{ε₀+τ'}`,
  `|𝒢^{abs}_{𝔞,𝔟𝔟}| ≤ W^τ W^{(n_𝔟−2)(−d/2+ε₀)} B_{𝔞𝔟}`, with `n_𝔟` the diagonal scaling order;
* `Lem512Zero.graphRowStmt`: for one graph of `A` without internal atoms, under the local law
  `|G_{xy} − m δ_{xy}|² ≺ B_{xy}` ([I, Theorem 2.16] in the form of `localLawTExpStmt'`),
  `Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}| ≤ W^δ L^d (L²/W²) W^{−(n_𝔟−2)d/2}`;
* `Lem512Zero.errRowStmt`: the same bound for one graph of `Err` without internal atoms, which may
  carry weights `W_d` of [II, (4.21)] and `P`/`Q` labels;
* `Lem512Zero.recordRowsStmt`: for a record with the graph properties of [II, Def 3.2], the sums
  over the graphs of `A` and of `Err` without internal atoms are at most
  `W^δ L^d (L²/W²) W^{−(n−3)d/2}` and `W^δ L^d (L²/W²) W^{−(D−3)d/2}`.

The expectations are split on the event of the local law. Off it, the graphs of `A` have an a
priori bound polynomial in `W`; the graphs of `Err` have a bound polynomial in `W` and in the
norm of the sample, whose moments are Gaussian.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

open private Moment_apriori_graph Moment_ev_adm Moment_tendsto Moment_W_le_L Moment_bB_le_one
  Moment_ev_list from RBM8D.LocalLaw.Moment
open private Moment_prod_le Moment_compVal_le Moment_im_inv Moment_ev_Smat Moment_ev_Sp
  Moment_ev_chain Moment_Gm_empty Moment_Sp_eq Moment_cvar_le Moment_coeff_le
  from RBM8D.LocalLaw.Moment
open private LabelRemoval_integrable_piecewise LabelRemoval_moment_res LabelRemoval_pow_piecewise_le
  LabelRemoval_coord_moment LabelRemoval_card_coord LabelRemoval_coordVar_le LabelRemoval_val_rbm
  LabelRemoval_val_bad LabelRemoval_Mb_pow LabelRemoval_inv_diag_le LabelRemoval_errKind
  from RBM8D.LocalLaw.LabelRemoval
open private Continuity_boxB Continuity_box Continuity_bB_le from RBM8D.LocalLaw.Continuity
open private Entrywise_base Entrywise_Phi Entrywise_Phi_zero Entrywise_Phi_nonneg
  from RBM8D.LocalLaw.Entrywise
open private Lem512_weakNorm_le Lem512_val_rbm Lem512_sum_le Lem512_arith Lem512_list_le
  Lem512_rpow_neg_le from RBM8D.SelfEnergy.Lem512

/-! ## The statements -/

/-- **The bound of a graph without internal atoms at `𝔟₁ = 𝔟₂`** at a single matrix: for `d ≥ 8`,
a profile `P`, `c₀, c₁ > 0` with `c₀ + c₁ < 1`, `κ, ε > 0`, the self-energies `Σ_l` of the even
orders `4 ≤ l ≤ N`, and a graph `𝒢` without internal atoms, normal regular, of the kinds of
[II, Def 3.2] with labels in `[4, N]`, with only diffusive components at `⊗` and dotted edges
forming a forest: for every `0 ≤ ε₀ < d/2` and `τ > 0` there are `τ' > 0` and `W₀` such that for
`W ≥ W₀` along `adm(c₀, c₁)`, `z ∈ 𝐃(κ, ε)` and every matrix `G` with
`‖G − m‖_{w;(1,2)} ≤ W^{ε₀+τ'}`,
`|𝒢^{abs}_{𝔞,𝔟𝔟}| ≤ W^τ W^{(n_𝔟−2)(−d/2+ε₀)} B_{𝔞𝔟}` for all `𝔞, 𝔟`. -/
def Lem512Zero.detStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (C : ℕ) (g : Graph 3 0), g.Normal C → g.TKinds N → g.TensorDiffusive → g.DotsAcyclic →
      ∀ ε₀ : ℝ, 0 ≤ ε₀ → ε₀ < (d : ℝ) / 2 →
      ∀ τ : ℝ, 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
        (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
          ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
            weakNorm d L W 1 2 (errAbs G z) ≤ (W : ℝ) ^ (ε₀ + τ') → ∀ a b : Zd d L,
              g.absVal (gData (Smat P.ψ W L) z Sig G) ![a, b, b] ≤
                (W : ℝ) ^ τ * (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) *
                  bB d L W a b

/-- **[I, Lemma 5.12], (5.42) for a graph of `A` without internal atoms**, in the strong norm: for
`d ≥ 8`, a profile `P`, `c₀, c₁ > 0` with `c₀ + c₁ < 1`, `κ, ε > 0`, `c₀ᵀ`, the self-energies `Σ_l`
of the even orders `4 ≤ l ≤ N`, the local law `|G_{xy}(z) − m(z) δ_{xy}|² ≺ B_{xy}` uniformly in
`z ∈ 𝐃(κ, ε)` and `x, y` along `llFilter d N c₀ c₁ c₀ᵀ`, a filter `F` below it, spectral
parameters `z_p ∈ 𝐃(κ, ε)` eventually along `F`, and a graph `𝒢` without internal atoms, normal
regular, of the kinds of [II, Def 3.2] with labels in `[4, N]`, with only diffusive components at
`⊗`, dotted edges forming a forest and without `P`/`Q` labels: for every `δ > 0`, eventually along
`F`, `Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤ W^δ L^d (L²/W²) W^{−(n_𝔟−2)d/2}`. -/
def Lem512Zero.graphRowStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) →
    ∀ (F : Filter SizeL), F ≤ llFilter d N c₀ c₁ c₀T → ∀ z : SizeL → ℂ,
      (∀ᶠ p in F, z p ∈ specDom κ ε p.1.1 p.1.2) →
    ∀ (C : ℕ) (g : Graph 3 0), g.Normal C → g.TKinds N → g.TensorDiffusive → g.DotsAcyclic →
      g.LabelFree →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ p in F,
      ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
        ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
          ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
        (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-(((g.diagOrd : ℝ) - 2) * d / 2))

/-- **[I, Lemma 5.12], (5.43) for a graph of `Err` without internal atoms**, in the strong norm:
with the hypotheses of `Lem512Zero.graphRowStmt` on `d`, `P`, the constants, `Σ`, the local law,
`F` and `z`, and `c₀ᵀ > 0`, for a graph `𝒢` without internal atoms, normal regular, with the
kinds of `Err` (the kinds of [II, Def 3.2] with labels in `[4, N]` and the weights `W_d` of
[II, (4.21)], with or without `P`/`Q` labels), with [II, Def 3.2 (9)], doubly connected, with only
diffusive components at `⊗` and dotted edges forming a forest: for every `δ > 0`, eventually along
`F`, `Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤ W^δ L^d (L²/W²) W^{−(n_𝔟−2)d/2}`. -/
def Lem512Zero.errRowStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → 0 < c₀T → ∀ (N : ℕ) (Sig : ℕ → Expansion 2),
    SelfEnergiesUpTo d (smatVar P) Sig N →
    StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) →
    ∀ (F : Filter SizeL), F ≤ llFilter d N c₀ c₁ c₀T → ∀ z : SizeL → ℂ,
      (∀ᶠ p in F, z p ∈ specDom κ ε p.1.1 p.1.2) →
    ∀ (C : ℕ) (g : Graph 3 0), g.Normal C → g.TKindsErr N → g.AtExternals →
      g.DoublyConnected → g.TensorDiffusive → g.DotsAcyclic →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ p in F,
      ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
        ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
          ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
        (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-(((g.diagOrd : ℝ) - 2) * d / 2))

/-- **[I, Lemma 5.12], (5.42)–(5.43) for the graphs without internal atoms** of a record with the
graph properties of [II, Def 3.2] (`TRec.Shape N n D`, labels in `[4, N]`) and the clauses
`TRec.Def63G11` read at `𝔟₁ = 𝔟₂`, in the strong norm: with the hypotheses of
`Lem512Zero.errRowStmt` on `d`, `P`, the constants, `Σ`, the local law, `F` and `z`, for every
`δ > 0`, eventually along `F`,
* `Σ_{𝒢 ∈ A, n_𝒢 = 0} Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤ W^δ L^d (L²/W²) W^{−(n−3)d/2}`;
* `Σ_{𝒢 ∈ Err, n_𝒢 = 0} Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤ W^δ L^d (L²/W²) W^{−(D−3)d/2}`.

For an `n`-th order `T`-equation `𝒬` the record is `𝒬.toTRec` with `N = n − 1`. -/
def Lem512Zero.recordRowsStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → 0 < c₀T → ∀ (N n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec),
    SelfEnergiesUpTo d (smatVar P) Sig N → 𝒯.Shape N n D → 𝒯.Def63G11 →
    StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) →
    ∀ (F : Filter SizeL), F ≤ llFilter d N c₀ c₁ c₀T → ∀ z : SizeL → ℂ,
      (∀ᶠ p in F, z p ∈ specDom κ ε p.1.1 p.1.2) →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ p in F,
      ((𝒯.A.filter fun g => g.1 = 0).map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
            ![a, b, b] ω‖ ∂(rbmLaw d P p)).sum ≤
        (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-(((n : ℝ) - 3) * d / 2)) ∧
      ((𝒯.Err.filter fun g => g.1 = 0).map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
            ![a, b, b] ω‖ ∂(rbmLaw d P p)).sum ≤
        (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-(((D : ℝ) - 3) * d / 2))

/-! ## The deterministic bound -/

set_option maxHeartbeats 2000000 in
-- the products over the components take long to elaborate
/-- **The bound of a graph without internal atoms at `𝔟₁ = 𝔟₂`** (`Lem512Zero.detStmt`): the
component at `⊗` is a `Θ` edge from `⊗` to `⊕` or `⊖`, bounded by `W^{τ₁} W^{−q d/2} W^d B_{𝔞𝔟}`
([I, Lemma 6.2]); every other component is bounded by its maximum `W^{τ₁} W^{−q d/2}`, times
`Λ = W^{ε₀+τ'}` for a solid edge or a light weight, and a dotted edge by `1`; there is at most one
dotted edge, between `⊕` and `⊖`, so that the orders add up to `n_𝔟`. -/
theorem Lem512Zero.det : Lem512Zero.detStmt := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig C g hNo hT hTD hDA ε₀ hε₀ hε₀d τ hτ
  classical
  set nb : ℝ := (g.diagOrd : ℝ) with hnb
  set τ' : ℝ := min (τ / (8 * (|nb - 2| + 2))) (((d : ℝ) / 2 - ε₀) / 2) with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) (by linarith)
  have hτ'1 : τ' ≤ τ / (8 * (|nb - 2| + 2)) := min_le_left _ _
  have hτ'2 : τ' ≤ ((d : ℝ) / 2 - ε₀) / 2 := min_le_right _ _
  have hτ'd : ε₀ + τ' ≤ (d : ℝ) / 2 := by linarith
  have hτ'abs : |nb - 2| * τ' ≤ τ / 8 := by
    have hpos : 0 < 8 * (|nb - 2| + 2) := by positivity
    calc |nb - 2| * τ' ≤ (|nb - 2| + 2) * τ' :=
          mul_le_mul_of_nonneg_right (by linarith) hτ'0.le
      _ ≤ (|nb - 2| + 2) * (τ / (8 * (|nb - 2| + 2))) :=
          mul_le_mul_of_nonneg_left hτ'1 (by positivity)
      _ = τ / 8 := by field_simp
  refine ⟨τ', hτ'0, ?_⟩
  obtain ⟨ia, xa, hxa0, hiaD, hia⟩ := exists_aEdge g hNo hTD
  have hxab : xa = .inl 1 ∨ xa = .inl 2 := by
    rcases xa with j | j
    · fin_cases j
      · exact absurd rfl hxa0
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact j.elim0
  have hTi := tkind_at g hT
  have hxd := xdot_of_normal' g hNo
  have hbk : ∀ i ∈ [ia], (∃ o, g.comps[i].kind = .theta o) ∨ ∃ w, g.comps[i].kind = .waved w := by
    intro i hi
    rw [List.mem_singleton] at hi
    subst hi
    exact Or.inl (tkind_diff _ (hTi _) hiaD)
  obtain ⟨C₀, hC₀, -⟩ := sqrtB_norms d hd
  set τ₁ : ℝ := τ / (4 * ((g.comps.length : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁ℓ : τ₁ * g.comps.length ≤ τ / 4 := by
    rw [hτ₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨M, W₁, hM, hW₁, hmain⟩ := dc_main d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g hT
    hxd [ia] [] (List.nodup_singleton _) List.nodup_nil hbk (fun i hi => by simp at hi)
    (fun i _ hi => by simp at hi) C₀ hC₀ τ₁ hτ₁0
  have hcount := count_le g hT [ia] (List.nodup_singleton _) hbk
  have hY : dotY g = ∅ := Finset.eq_empty_of_isEmpty _
  have hdo := diagOrd_le' g hNo hTD hDA hY
  refine ⟨max W₁ ((max 1 M) ^ (4 / τ)), fun W L _ hadm hW z hz G hEw a b => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := hW₁.trans ((le_max_left _ _).trans hW)
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set Λ : ℝ := (W : ℝ) ^ (ε₀ + τ') with hΛdef
  have hΛ : 1 ≤ Λ := Real.one_le_rpow hW1 (by linarith)
  have hΛW : Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hW1 hτ'd
  obtain ⟨e3, he3⟩ : ∃ e3 : Fin 3 → Zd d L, e3 = ![a, b, b] := ⟨_, rfl⟩
  have he0 : e3 0 = a := by rw [he3]; rfl
  have he1 : e3 1 = b := by rw [he3]; rfl
  have he2 : e3 2 = b := by rw [he3]; rfl
  rw [← he3]
  have hE := errAbs_le_weak hW1n G z Λ hEw
  have hmain' := hmain W L hadm ((le_max_left _ _).trans hW) z hz G Λ hΛ hΛW hE e3
  have hS : (∑ s : Fin 0 → Zd d L,
      ([ia].map fun i : Fin g.comps.length => bB d L W (Sum.elim e3 s g.comps[i].x)
          (Sum.elim e3 s g.comps[i].y)).prod *
        (([] : List (Fin g.comps.length)).map fun i : Fin g.comps.length =>
          |blueMat d L W C₀ Λ (errAbs G z) (blueIdx g.comps[i])
            (Sum.elim e3 s g.comps[i].x) (Sum.elim e3 s g.comps[i].y)|).prod *
          wDot g (Sum.elim e3 s)) ≤ bB d L W a b := by
    have hone : ∀ s : Fin 0 → Zd d L,
        ([ia].map fun i : Fin g.comps.length => bB d L W (Sum.elim e3 s g.comps[i].x)
          (Sum.elim e3 s g.comps[i].y)).prod *
        (([] : List (Fin g.comps.length)).map fun i : Fin g.comps.length =>
          |blueMat d L W C₀ Λ (errAbs G z) (blueIdx g.comps[i])
            (Sum.elim e3 s g.comps[i].x) (Sum.elim e3 s g.comps[i].y)|).prod *
          wDot g (Sum.elim e3 s) ≤ bB d L W a b := by
      intro s
      have hb : Sum.elim e3 s xa = b := by
        rcases hxab with h | h <;> rw [h] <;> simp [he1, he2]
      have h1 : bB d L W (Sum.elim e3 s g.comps[ia].x) (Sum.elim e3 s g.comps[ia].y) =
          bB d L W a b := by
        rcases hia with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [hx, hy, hb]; simp only [Sum.elim_inl, he0]
        · rw [hx, hy, hb, bB_comm']; simp only [Sum.elim_inl, he0]
      obtain ⟨hw0, hw1⟩ := wDot_mem g (Sum.elim e3 s)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [h1]
      have := (bB_pos₁ (d := d) (L := L) hW1n a b).le
      nlinarith
    calc _ ≤ ∑ _s : Fin 0 → Zd d L, bB d L W a b := Finset.sum_le_sum fun s _ => hone s
      _ = bB d L W a b := by simp
  set E : ℝ := ∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ) - 2 with hEdef
  have hqE : ((∑ i : Fin g.comps.length, lamW g.comps[i] : ℕ) : ℝ) ≤ E := by
    rw [hEdef]; push_cast at hcount ⊢
    simp only [List.length_singleton, Nat.cast_one] at hcount; linarith
  have hnbE : nb - 2 ≤ E := by
    rw [hnb, hEdef]
    simpa using hdo
  have hΛE : Λ ^ (∑ i : Fin g.comps.length, lamW g.comps[i]) * (W : ℝ) ^ (-(E * d / 2)) ≤
      (W : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) * (W : ℝ) ^ (|nb - 2| * τ') := by
    rw [← Real.rpow_natCast]
    calc Λ ^ ((∑ i : Fin g.comps.length, lamW g.comps[i] : ℕ) : ℝ) * (W : ℝ) ^ (-(E * d / 2))
        ≤ Λ ^ E * (W : ℝ) ^ (-(E * d / 2)) := by
          gcongr
      _ ≤ _ := final_pow (W : ℝ) (d : ℝ) ε₀ τ' E nb hW1 hτ'0.le hnbE hτ'd
  have hexp : (W : ℝ) ^ (∑ i : Fin g.comps.length, (-(ordE g.comps[i] : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ [ia].length *
        ((W : ℝ) ^ ((d : ℝ) / 2)) ^ ([] : List (Fin g.comps.length)).length) =
      (W : ℝ) ^ (-(E * d / 2)) := by
    rw [sum_expo]
    have := pow_combine (W : ℝ) hW0 (∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ)) (d : ℝ) 0
      [ia].length ([] : List (Fin g.comps.length)).length
    rw [show -((0 : ℝ) * d / 2) = 0 by ring, Real.rpow_zero, mul_one] at this
    rw [this, hEdef]
    congr 1
    simp only [List.length_singleton, List.length_nil]
    push_cast
    ring
  have hM' := const_le_rpow M τ W hτ ((le_max_right _ _).trans hW)
  have hWτ₁ : (W : ℝ) ^ (τ₁ * g.comps.length) ≤ (W : ℝ) ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hW1 hτ₁ℓ
  have hB0 := (bB_pos₁ (d := d) (L := L) hW1n a b).le
  have hτ8 : (W : ℝ) ^ (|nb - 2| * τ') ≤ (W : ℝ) ^ (τ / 8) :=
    Real.rpow_le_rpow_of_exponent_le hW1 hτ'abs
  have h2 : (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 8) ≤ (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hX0 : 0 ≤ (W : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) := Real.rpow_nonneg hW0.le _
  calc g.absVal (gData (Smat P.ψ W L) z Sig G) e3
      ≤ _ := hmain'
    _ ≤ M * (W : ℝ) ^ (τ₁ * g.comps.length) * Λ ^ (∑ i : Fin g.comps.length, lamW g.comps[i]) *
          (W : ℝ) ^ (∑ i : Fin g.comps.length, (-(ordE g.comps[i] : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ [ia].length *
            ((W : ℝ) ^ ((d : ℝ) / 2)) ^ ([] : List (Fin g.comps.length)).length) *
          bB d L W a b := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = M * (W : ℝ) ^ (τ₁ * g.comps.length) *
          (Λ ^ (∑ i : Fin g.comps.length, lamW g.comps[i]) * (W : ℝ) ^ (-(E * d / 2))) *
          bB d L W a b := by rw [← hexp]; ring
    _ ≤ (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 4) *
          ((W : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) * (W : ℝ) ^ (τ / 8)) * bB d L W a b := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul hM' hWτ₁ (by positivity)
            (by positivity)) (hΛE.trans (mul_le_mul_of_nonneg_left hτ8 hX0)) (by positivity)
            (by positivity)) hB0
    _ = (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 8) *
          (W : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) * bB d L W a b := by ring
    _ ≤ (W : ℝ) ^ τ * (W : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) * bB d L W a b := by
          gcongr

/-! ## Polynomial moments of the sample -/

/-- `E(1 + ‖ω‖)^q ≤ 1 + 2^q (1 + E|Z|^q) |Coord ι|` for coordinate variances at most `1`, and
`(1 + ‖ω‖)^q` is integrable. -/
private theorem Lem512Zero_moment {ι : Type} [Fintype ι] (S : Matrix ι ι ℝ)
    (hS : ∀ c, coordVar S c ≤ 1) (q : ℕ) :
    Integrable (fun ω : Sample ι => (1 + ‖ω‖) ^ q) (gaussLaw S) ∧
      ∫ ω, (1 + ‖ω‖) ^ q ∂(gaussLaw S) ≤
        1 + 2 ^ q * (1 + LabelRemoval.gaussMoment q) * Fintype.card (Coord ι) := by
  classical
  have := isProbabilityMeasure_gaussLaw S
  have hpw : ∀ η : Sample ι, (Finset.univ : Finset (Coord ι)).piecewise η 0 = η := fun η =>
    Finset.piecewise_univ _ _
  have hi0 := LabelRemoval_integrable_piecewise S Finset.univ (0 : Sample ι) q
  simp only [hpw] at hi0
  have hint : ∀ c, Integrable (fun η : Sample ι => (1 + |η c|) ^ q) (gaussLaw S) := by
    intro c
    have hpoly : PolyMeas fun η : Sample ι => (((1 + |η c|) ^ q : ℝ) : ℂ) := by
      refine ⟨by fun_prop, 1, q, fun η => ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
      exact pow_le_pow_left₀ (by positivity) (by
        have := norm_le_pi_norm η c; rw [Real.norm_eq_abs] at this; linarith) q
    refine (integrable_of_polyMeas S _ hpoly).norm.congr (Eventually.of_forall fun η => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  refine ⟨hi0, ?_⟩
  calc ∫ ω, (1 + ‖ω‖) ^ q ∂(gaussLaw S)
      ≤ ∫ η, (1 + ∑ c : Coord ι, (1 + |η c|) ^ q) ∂(gaussLaw S) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun η => by positivity)
          ((integrable_const _).add (integrable_finsetSum _ fun c _ => hint c))
          (Eventually.of_forall fun η => ?_)
        have h := LabelRemoval_pow_piecewise_le (Finset.univ : Finset (Coord ι)) η 0 q
        rw [hpw, norm_zero, add_zero, one_pow] at h
        exact h
    _ = 1 + ∑ c : Coord ι, ∫ η, (1 + |η c|) ^ q ∂(gaussLaw S) := by
        rw [integral_add (integrable_const _) (integrable_finsetSum _ fun c _ => hint c),
          integral_finsetSum _ fun c _ => hint c, integral_const]
        simp
    _ ≤ 1 + ∑ _c : Coord ι, 2 ^ q * (1 + LabelRemoval.gaussMoment q) := by
        gcongr with c
        exact LabelRemoval_coord_moment S c (hS c) q
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- `M_q(ω, y) ≤ (1 + 2^q (1 + E|Z|^q) |Coord ι|) (1 + ‖ω‖)^q` (`LabelRemoval.momBound`). -/
private theorem Lem512Zero_momBound_le {ι : Type} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (ω : Sample ι) (y : ι) :
    LabelRemoval.momBound q ω y ≤
      (1 + 2 ^ q * (1 + LabelRemoval.gaussMoment q) * Fintype.card (Coord ι)) * (1 + ‖ω‖) ^ q := by
  unfold LabelRemoval.momBound
  have hg : 0 ≤ LabelRemoval.gaussMoment q :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) q
  have hc : ((rowCoords y).card : ℝ) ≤ Fintype.card (Coord ι) := by
    exact_mod_cast Finset.card_le_univ _
  have h1 : (1 : ℝ) ≤ (1 + ‖ω‖) ^ q := one_le_pow₀ (by linarith [norm_nonneg ω])
  have h0 : 0 ≤ 2 ^ q * (1 + LabelRemoval.gaussMoment q) := by positivity
  have hC0 : (0 : ℝ) ≤ Fintype.card (Coord ι) := Nat.cast_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hc h0
  have e2 : 2 ^ q * (1 + LabelRemoval.gaussMoment q) * (Fintype.card (Coord ι) : ℝ) ≤
      2 ^ q * (1 + LabelRemoval.gaussMoment q) * Fintype.card (Coord ι) * (1 + ‖ω‖) ^ q :=
    le_mul_of_one_le_right (by positivity) h1
  nlinarith

/-- `|P_y F(ω)| ≤ A M_q(ω, y)` when `|F(ω')| ≤ A (1 + ‖ω'‖)^q` everywhere. -/
private theorem Lem512Zero_Pexp_le {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (hS : ∀ c, coordVar S c ≤ 1) (y : ι) (F : Sample ι → ℂ) (A : ℝ) (q : ℕ) (hA : 0 ≤ A)
    (hF : ∀ ω, ‖F ω‖ ≤ A * (1 + ‖ω‖) ^ q) (ω : Sample ι) :
    ‖Pexp S y F ω‖ ≤ A * LabelRemoval.momBound q ω y := by
  have := isProbabilityMeasure_gaussLaw S
  unfold Pexp partialExp
  have hi := LabelRemoval_integrable_piecewise S (rowCoords y) ω q
  calc ‖∫ η, F ((rowCoords y).piecewise η ω) ∂(gaussLaw S)‖
      ≤ ∫ η, A * (1 + ‖(rowCoords y).piecewise η ω‖) ^ q ∂(gaussLaw S) :=
        norm_integral_le_of_norm_le (hi.const_mul A) (Eventually.of_forall fun η => hF _)
    _ = A * ∫ η, (1 + ‖(rowCoords y).piecewise η ω‖) ^ q ∂(gaussLaw S) := integral_const_mul _ _
    _ ≤ A * LabelRemoval.momBound q ω y :=
        mul_le_mul_of_nonneg_left (LabelRemoval_moment_res S hS y ω q) hA

/-- A priori bound of the value of a graph with `P`/`Q` labels read by the partial expectations
`P_x`, when every factor is at most `A (1 + ‖ω‖)²`: with `c` the number of components and
`B = 1 + 2^{2c} (1 + E|Z|^{2c}) |Coord ι|`,
`|Γ| ≤ |ι|^n |coeff| A^c (2 A^c B)^c (1 + ‖ω‖)^{2c(c+1)}`. -/
private theorem Lem512Zero_valR_le {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ}
    (Γ : Graph k n) (S : Matrix ι ι ℝ) (hS : ∀ c, coordVar S c ≤ 1) (D : Sample ι → Data ι)
    (A : ℝ) (hA1 : 1 ≤ A) (hm : ∀ ω, (D ω).m = (D 0).m)
    (hcomp : ∀ (ω' : Sample ι) (σ : Atom k n → ι), ∀ c ∈ Γ.comps,
      ‖Comp.val (D ω') σ c‖ ≤ A * (1 + ‖ω'‖) ^ 2)
    (e : Fin k → ι) (ω : Sample ι) :
    ‖Γ.valR ⟨Pexp S⟩ D e ω‖ ≤ (Fintype.card ι : ℝ) ^ n * (‖Γ.coeff.eval (D 0).m‖ *
      A ^ Γ.comps.length * (2 * A ^ Γ.comps.length *
        (1 + 2 ^ (2 * Γ.comps.length) * (1 + LabelRemoval.gaussMoment (2 * Γ.comps.length)) *
          Fintype.card (Coord ι))) ^ Γ.comps.length) *
      (1 + ‖ω‖) ^ (2 * Γ.comps.length * (Γ.comps.length + 1)) := by
  set c := Γ.comps.length with hc
  set B₁ : ℝ := 1 + 2 ^ (2 * c) * (1 + LabelRemoval.gaussMoment (2 * c)) *
    Fintype.card (Coord ι) with hB₁
  have hg : 0 ≤ LabelRemoval.gaussMoment (2 * c) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hB₁1 : 1 ≤ B₁ := by
    have : (0 : ℝ) ≤ 2 ^ (2 * c) * (1 + LabelRemoval.gaussMoment (2 * c)) *
      Fintype.card (Coord ι) := by positivity
    linarith
  have hA0 : 0 ≤ A := by linarith
  have hR : ∀ ω' : Sample ι, 1 ≤ 1 + ‖ω'‖ := fun ω' => by linarith [norm_nonneg ω']
  have hsub : ∀ (p : Comp (Atom k n) → Bool) ω' (σ : Atom k n → ι),
      ‖((Γ.comps.filter p).map (Comp.val (D ω') σ)).prod‖ ≤ A ^ c * (1 + ‖ω'‖) ^ (2 * c) := by
    intro p ω' σ
    have h1 : 1 ≤ A * (1 + ‖ω'‖) ^ 2 := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ (hR ω'))
    refine (Moment_prod_le _ _ (A * (1 + ‖ω'‖) ^ 2) (by linarith) fun c' hc' =>
      hcomp ω' σ c' (List.mem_of_mem_filter hc')).trans ?_
    refine (pow_le_pow_right₀ h1 (List.length_filter_le _ _)).trans (le_of_eq ?_)
    rw [mul_pow, ← pow_mul, mul_comm 2 c]
  have hterm : ∀ σ : Atom k n → ι, ‖Γ.termR ⟨Pexp S⟩ D σ ω‖ ≤
      ‖Γ.coeff.eval (D 0).m‖ * A ^ c * (2 * A ^ c * B₁) ^ c *
        (1 + ‖ω‖) ^ (2 * c * (c + 1)) := by
    intro σ
    unfold Graph.termR
    rw [norm_mul, norm_mul, hm ω]
    set Y : ℝ := 2 * A ^ c * B₁ * (1 + ‖ω‖) ^ (2 * c) with hY
    have hY1 : 1 ≤ Y := by
      have : 1 ≤ A ^ c := one_le_pow₀ hA1
      have : 1 ≤ (1 + ‖ω‖) ^ (2 * c) := one_le_pow₀ (hR ω)
      have : 1 ≤ A ^ c * B₁ := one_le_mul_of_one_le_of_one_le (by assumption) hB₁1
      nlinarith
    have hlab : Γ.labels.length ≤ c := by
      unfold Graph.labels
      exact (List.dedup_sublist _).length_le.trans (List.length_filterMap_le _ _)
    have hlabs : ‖(Γ.labels.map fun ℓ =>
        PFamily.op ⟨Pexp S⟩ ℓ.1 (σ ℓ.2) (fun ω' =>
          ((Γ.comps.filter fun c' => decide (c'.label = some ℓ)).map
            (Comp.val (D ω') σ)).prod) ω).prod‖ ≤ Y ^ c := by
      refine (Moment_prod_le _ _ Y (by linarith) fun ℓ _ => ?_).trans
        (pow_le_pow_right₀ hY1 hlab)
      have hP : ‖PFamily.P ⟨Pexp S⟩ (σ ℓ.2) (fun ω' =>
          ((Γ.comps.filter fun c' => decide (c'.label = some ℓ)).map
            (Comp.val (D ω') σ)).prod) ω‖ ≤ A ^ c * B₁ * (1 + ‖ω‖) ^ (2 * c) := by
        refine (Lem512Zero_Pexp_le S hS (σ ℓ.2) _ (A ^ c) (2 * c) (pow_nonneg hA0 _)
          (fun ω' => hsub _ ω' σ) ω).trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (Lem512Zero_momBound_le (2 * c) ω (σ ℓ.2))
          (pow_nonneg hA0 _)
      have hF := hsub (fun c' => decide (c'.label = some ℓ)) ω σ
      have hAc : 0 ≤ A ^ c * (1 + ‖ω‖) ^ (2 * c) := by positivity
      rcases ℓ with ⟨pq, u⟩
      cases pq
      · refine hP.trans ?_
        rw [hY]
        nlinarith
      · simp only [PFamily.op, Pi.sub_apply]
        refine (norm_sub_le _ _).trans ?_
        have : A ^ c * (1 + ‖ω‖) ^ (2 * c) ≤ A ^ c * B₁ * (1 + ‖ω‖) ^ (2 * c) := by
          rw [mul_comm (A ^ c) B₁, mul_assoc]
          exact le_mul_of_one_le_left hAc hB₁1
        rw [hY]
        linarith
    have hYc : Y ^ c = (2 * A ^ c * B₁) ^ c * (1 + ‖ω‖) ^ (2 * c * c) := by
      rw [hY, mul_pow, ← pow_mul]
    calc ‖Γ.coeff.eval (D 0).m‖ *
          ‖((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod‖ *
          ‖(Γ.labels.map fun ℓ => PFamily.op ⟨Pexp S⟩ ℓ.1 (σ ℓ.2) (fun ω' =>
            ((Γ.comps.filter fun c' => decide (c'.label = some ℓ)).map
              (Comp.val (D ω') σ)).prod) ω).prod‖
        ≤ ‖Γ.coeff.eval (D 0).m‖ * (A ^ c * (1 + ‖ω‖) ^ (2 * c)) * Y ^ c := by
          gcongr
          exact hsub _ ω σ
      _ = _ := by
          rw [hYc]
          have : (1 + ‖ω‖) ^ (2 * c * (c + 1)) = (1 + ‖ω‖) ^ (2 * c) * (1 + ‖ω‖) ^ (2 * c * c) := by
            rw [← pow_add]; congr 1; ring
          rw [this]; ring
  unfold Graph.valR
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun s _ => hterm _).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [hB₁]
  ring_nf
  exact le_rfl

/-! ## A priori bounds of the graphs of `Err` -/

/-- `‖z‖ ≤ 3` on `𝐃(κ, ε)`. -/
private theorem Lem512Zero_norm_le_three {κ ε : ℝ} {W L : ℕ} [NeZero L] (z : ℂ)
    (hz : z ∈ specDom κ ε W L) (him : 0 < z.im) (hκ : 0 < κ) : ‖z‖ ≤ 3 := by
  have hre : |z.re| < 2 - κ := hz.1
  have him1 : z.im ≤ 1 := hz.2.2
  have := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos him] at this
  linarith

/-- Eventually along the filter, every factor of a graph with the kinds of `Err` on the data
record of the model is at most `W^K (1 + ‖ω‖)²`, at every `z ∈ 𝐃(κ, ε)`: the entries of `G` are at
most `(Im z)⁻¹`, `|(G_{xx})⁻¹| ≤ C (1 + ‖ω‖)²` (Schur complement formula), `|m| ≥ 1/4`, and the
deterministic factors are at most `W`. -/
private theorem Lem512Zero_comp_le (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ)
    (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig N) {n : ℕ}
    (g : Graph 3 n) (hK : g.TKindsErr N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ p in llFilter d N c₀ c₁ c₀T,
      ∀ (u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2}) (ω' : Sample (Zd d p.1.2))
        (σ : Atom 3 n → Zd d p.1.2), ∀ c ∈ g.comps,
        ‖Comp.val (rbmData d P Sig p.1.1 p.1.2 u.1 ω') σ c‖ ≤ (p.1.1 : ℝ) ^ K * (1 + ‖ω'‖) ^ 2 := by
  set U : SizeL → Type := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} with hU
  set e : ℝ := 2 / c₁ + 1 with he
  have he0 : 1 ≤ e := by have : 0 ≤ 2 / c₁ := by positivity
                         linarith
  set R : ℕ := (g.comps.map fun c => c.kind.wDDeg).sum with hR
  set e₂ : ℝ := (2 * d + 2) / c₁ + 4 with he₂
  have hd0 : (0 : ℝ) ≤ (2 * d + 2) / c₁ := by positivity
  set Kb : ℝ := 8 * ((R : ℝ) + 1) * 4 ^ R with hKb
  have hKb1 : 1 ≤ Kb := by
    have hR1 : (1 : ℝ) ≤ (R : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) R]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hR1) (one_le_pow₀ (by norm_num))
  obtain ⟨KS, hKS⟩ := Moment_ev_Sp d N P c₀ c₁ κ ε c₀T hc₀ hc₁ hκ hε U (fun _ u => u.1)
    (fun _ u => u.2)
  have hch : ∀ᶠ p in llFilter d N c₀ c₁ c₀T, ∀ c' ∈ g.comps, ∀ o, c'.kind = .theta o →
      ∀ (u : U p) (ω : Sample (Zd d p.1.2)) (x y : Zd d p.1.2),
        ‖(rbmData d P Sig p.1.1 p.1.2 u.1 ω).chain o x y‖ ≤ (p.1.1 : ℝ) := by
    refine Moment_ev_list g.comps fun c' hc' => ?_
    by_cases h : ∃ o, c'.kind = .theta o
    · obtain ⟨o, ho⟩ := h
      have hok : labelOK N o = true := by
        rcases LabelRemoval_errKind hK hc' with hT | ⟨-, hw⟩
        · simp only [Comp.isTKind, ho, Bool.and_eq_true] at hT
          exact hT.2
        · rw [ho] at hw; cases hw
      filter_upwards [Moment_ev_chain d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE U
        (fun _ u => u.1) (fun _ u => u.2) o hok] with p hp o' ho'
      rw [ho] at ho'
      cases ho'
      exact hp
    · exact Eventually.of_forall fun p o ho => absurd ⟨o, ho⟩ h
  refine ⟨max (e + 1) ((e₂ + 1) * (R + 1)), le_max_of_le_left (by linarith), ?_⟩
  filter_upwards [Moment_ev_adm d N c₀ c₁ c₀T, Moment_ev_Smat d N P c₀ c₁ c₀T hc₀ hc₁, hKS, hch,
    (Moment_tendsto d N c₀ c₁ c₀T).eventually (eventually_ge_atTop (max 3 (max KS Kb)))]
    with p hp hSm hKSp hchp hW u ω' σ c hc
  change max 3 (max KS Kb) ≤ (p.1.1 : ℝ) at hW
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW3 : 3 ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hKSW : KS ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hKbW : Kb ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  obtain ⟨him, himW⟩ := Moment_im_inv (c₀ := c₀) hc₁ hε p hp hW1 u.1 u.2
  have hz3 := Lem512Zero_norm_le_three u.1 u.2 him hκ
  have hr1 : (1 : ℝ) ≤ (1 + ‖ω'‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg ω'])
  have hWe : W ≤ W ^ e := by
    calc W = W ^ (1 : ℝ) := (Real.rpow_one W).symm
      _ ≤ W ^ e := Real.rpow_le_rpow_of_exponent_le hW1 he0
  have hM1 : 1 ≤ W ^ e := hW1.trans hWe
  have hKmax : 0 ≤ W ^ max (e + 1) ((e₂ + 1) * (R + 1)) := Real.rpow_nonneg hW0.le _
  have hGim : ∀ x y, ‖green (hmat ω') u.1 x y‖ ≤ W ^ (2 / c₁) := by
    intro x y
    refine (norm_green_entry_le (hmat_isHermitian ω') him.ne' x y).trans ?_
    rw [abs_of_pos him]
    exact himW
  rcases LabelRemoval_errKind hK hc with hT | ⟨hmin, hwd⟩
  · -- a component with the kinds of [II, Def 3.2]
    have h := Moment_compVal_le N (rbmData d P Sig p.1.1 p.1.2 u.1 ω') σ c hT (W ^ e) hM1
      (norm_msc_lt_one him).le
      (fun x y => by
        rw [Moment_Gm_empty]
        exact (hGim x y).trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)))
      (fun x y => by
        change ‖((Smat P.ψ p.1.1 p.1.2 x y : ℝ) : ℂ)‖ ≤ W ^ e
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hSm.2.1 x y)]
        have : Smat P.ψ p.1.1 p.1.2 x y ≤ ∑ y', Smat P.ψ p.1.1 p.1.2 x y' :=
          Finset.single_le_sum (fun y' _ => hSm.2.1 x y') (Finset.mem_univ y)
        rw [hSm.2.2 x] at this
        exact this.trans hM1)
      (fun x y => by
        rw [(Moment_Sp_eq d P Sig p.1.1 p.1.2 u.1 ω').1]
        exact (hKSp u x y).1.trans (hKSW.trans hWe))
      (fun x y => by
        rw [(Moment_Sp_eq d P Sig p.1.1 p.1.2 u.1 ω').2]
        exact (hKSp u x y).2.trans (hKSW.trans hWe))
      (fun o ho x y => (hchp c hc o ho u ω' x y).trans hWe)
    have h2 : 2 * W ^ e ≤ W ^ (e + 1) := by
      rw [Real.rpow_add_one hW0.ne' e]
      have h0 : 0 ≤ W ^ e := Real.rpow_nonneg hW0.le e
      have := mul_le_mul_of_nonneg_left hW3 h0
      linarith
    have h3 : W ^ (e + 1) ≤ W ^ max (e + 1) ((e₂ + 1) * (R + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (le_max_left _ _)
    calc ‖Comp.val (rbmData d P Sig p.1.1 p.1.2 u.1 ω') σ c‖ ≤ 2 * W ^ e := h
      _ ≤ W ^ max (e + 1) ((e₂ + 1) * (R + 1)) := h2.trans h3
      _ ≤ _ := le_mul_of_one_le_right hKmax hr1
  · -- a weight `W_d`
    rw [LabelRemoval_val_rbm P Sig _ _ _ ω' σ N c (Or.inr ⟨hmin, hwd⟩)]
    have hdd : c.kind.wDDeg ≤ R :=
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun c => c.kind.wDDeg) hc)
    have hrand : c.kind.isRandom = true := by
      obtain ⟨κ', x, y, mi, l⟩ := c
      cases κ' <;> simp_all [Kind.isWD, Kind.isRandom]
    have hm4 : 1 / 4 ≤ ‖msc u.1‖ := norm_msc_ge_quarter u.1 him hz3
    have hWa : 1 ≤ W ^ ((2 * d + 2) / c₁) := Real.one_le_rpow hW1 hd0
    have hW4 : W ^ e₂ = W ^ ((2 * d + 2) / c₁) * W ^ 4 := by
      rw [he₂, Real.rpow_add hW0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hW16 : (81 : ℝ) ≤ W ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hW3 4
      norm_num at this; linarith
    have hMe : 1 ≤ W ^ e₂ := Real.one_le_rpow hW1 (by linarith)
    have hcard : (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ W ^ (2 * (d : ℝ) / c₁) := by
      have : (Fintype.card (Zd d p.1.2) : ℝ) ≤ W ^ ((d : ℝ) / c₁) := card_Zd_le_adm d c₀ c₁ hc₁ p hp
      calc (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ (W ^ ((d : ℝ) / c₁)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
        _ = W ^ (2 * (d : ℝ) / c₁) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have hsplit : W ^ (2 * (d : ℝ) / c₁) * W ^ (2 / c₁) = W ^ ((2 * d + 2) / c₁) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    have hG' : ∀ a b, ‖green (hmat ω') u.1 a b‖ ≤ W ^ e₂ - 1 := by
      intro a b
      have h1 : W ^ (2 / c₁) ≤ W ^ ((2 * d + 2) / c₁) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (by
          have : 0 ≤ 2 * (d : ℝ) / c₁ := by positivity
          rw [add_div]; linarith)
      have := hGim a b
      have h81 : W ^ ((2 * d + 2) / c₁) * 81 ≤ W ^ ((2 * d + 2) / c₁) * W ^ 4 :=
        mul_le_mul_of_nonneg_left hW16 (by positivity)
      rw [hW4]; linarith
    have hinv : ∀ a, ‖(green (hmat ω') u.1 a a)⁻¹‖ ≤ W ^ e₂ * (1 + ‖ω'‖) ^ 2 := by
      intro a
      refine (LabelRemoval_inv_diag_le him ω' a).trans
        (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have hi4 : 4 * u.1.im⁻¹ ≤ 4 * W ^ (2 / c₁) := by linarith [himW]
      have : (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 * (4 * u.1.im⁻¹) ≤
          4 * W ^ ((2 * d + 2) / c₁) := by
        rw [← hsplit]
        calc (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 * (4 * u.1.im⁻¹)
            ≤ W ^ (2 * (d : ℝ) / c₁) * (4 * W ^ (2 / c₁)) :=
              mul_le_mul hcard hi4 (by positivity) (by positivity)
          _ = _ := by ring
      have h81 : W ^ ((2 * d + 2) / c₁) * 81 ≤ W ^ ((2 * d + 2) / c₁) * W ^ 4 :=
        mul_le_mul_of_nonneg_left hW16 (by positivity)
      rw [hW4]; linarith
    have hMMb : W ^ e₂ ≤ Kb * W ^ e₂ := le_mul_of_one_le_left (zero_le_one.trans hMe) hKb1
    have hMb1 : 1 ≤ Kb * W ^ e₂ := one_le_mul_of_one_le_of_one_le hKb1 hMe
    have hval := LabelRemoval_val_bad (Smat P.ψ p.1.1 p.1.2) u.1 Sig (green (hmat ω') u.1)
      (W ^ e₂) (Kb * W ^ e₂) ((1 + ‖ω'‖) ^ 2) hMe hr1 hG' hinv (norm_msc_lt_one him).le hm4 σ N
      c (Or.inr ⟨hmin, hwd⟩) hrand hMMb (fun _ => LabelRemoval_Mb_pow (W ^ e₂) hMe R _ hdd)
    refine hval.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hMbW : Kb * W ^ e₂ ≤ W ^ (e₂ + 1) := by
      rw [Real.rpow_add_one hW0.ne' e₂, mul_comm (W ^ e₂)]
      exact mul_le_mul_of_nonneg_right hKbW (by positivity)
    calc (Kb * W ^ e₂) ^ (c.kind.wDDeg + 1) ≤ (Kb * W ^ e₂) ^ (R + 1) :=
          pow_le_pow_right₀ hMb1 (by omega)
      _ ≤ (W ^ (e₂ + 1)) ^ (R + 1) := pow_le_pow_left₀ (by linarith) hMbW _
      _ = W ^ ((e₂ + 1) * (R + 1)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; push_cast; ring_nf
      _ ≤ W ^ max (e + 1) ((e₂ + 1) * (R + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (le_max_right _ _)

/-- **A priori bound of a graph of `Err` without internal atoms**: eventually along the filter,
`|𝒢_{𝔞,𝔟𝔟}(ω)| ≤ W^K (1 + ‖ω‖)^q` at every `z ∈ 𝐃(κ, ε)`, `𝔞`, `𝔟` and sample `ω`. -/
private theorem Lem512Zero_apriori (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ)
    (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig N) (g : Graph 3 0)
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
  refine ⟨1 + K₀ * c + E₁ * c, 2 * c * (c + 1), by positivity, ?_⟩
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
  have hcard0 : (Fintype.card (Zd d p.1.2) : ℝ) ^ (0 : ℕ) = 1 := pow_zero _
  rw [hcard0, one_mul]
  have hR1 : (0 : ℝ) ≤ (1 + ‖ω‖) ^ (2 * c * (c + 1)) := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hR1
  rw [← hCst]
  calc ‖g.coeff.eval (rbmData d P Sig p.1.1 p.1.2 u.1 0).m‖ * (W ^ K₀) ^ c *
        (2 * (W ^ K₀) ^ c * (1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ))) ^ c
      ≤ W * W ^ (K₀ * c) * W ^ (E₁ * c) := by
        rw [hAc] at hYc ⊢
        gcongr
  _ = W ^ (1 + K₀ * c + E₁ * c) := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]

/-! ## The hypotheses of the label removal from the local law -/

/-- [II, (7.7)] from the local law: `|G_{xy} − m δ_{xy}|² ≺ B_{xy} ≤ W^{−d}` gives
`|G_{xy} − m δ_{xy}| ≺ W^{−d/2+ε₀}` for every `ε₀ ≥ 0`. -/
private theorem Lem512Zero_h77 {d : ℕ} (hd : 2 ≤ d) (P : Profile d) {c₀ c₁ κ ε c₀T : ℝ} {N : ℕ}
    (hLL : StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2)) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) :
    StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖)
      (fun p _ _ => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) := by
  intro τ hτ D hD
  filter_upwards [hLL τ hτ D hD, (Moment_tendsto d N c₀ c₁ c₀T).eventually
    (eventually_ge_atTop 1)] with p hp hW
  refine le_trans (measure_mono ?_) hp
  rintro ω ⟨v, hv⟩
  refine ⟨v, ?_⟩
  change (1 : ℝ) ≤ p.1.1 at hW
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have hW1n : 1 ≤ p.1.1 := by exact_mod_cast hW
  change (p.1.1 : ℝ) ^ τ * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀) <
    ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ at hv
  change (p.1.1 : ℝ) ^ τ * bB d p.1.2 p.1.1 v.2.1 v.2.2 <
    ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2
  have hB := Continuity_bB_le hd hW1n v.2.1 v.2.2
  have hx0 : 0 ≤ (p.1.1 : ℝ) ^ τ * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀) := by positivity
  have hsq : (p.1.1 : ℝ) ^ τ * ((p.1.1 : ℝ) ^ (d : ℝ))⁻¹ ≤
      ((p.1.1 : ℝ) ^ τ * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ^ 2 := by
    rw [← Real.rpow_neg hW0.le, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hW0.le, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW (by push_cast; nlinarith)
  calc (p.1.1 : ℝ) ^ τ * bB d p.1.2 p.1.1 v.2.1 v.2.2
      ≤ (p.1.1 : ℝ) ^ τ * ((p.1.1 : ℝ) ^ (d : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ ((p.1.1 : ℝ) ^ τ * (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀)) ^ 2 := hsq
    _ < _ := by gcongr

/-- `|G_{xy}|² ≤ 2 |G_{xy} − m δ_{xy}|² + 2 δ_{xy}` for `|m| ≤ 1`. -/
private theorem Lem512Zero_sq_le {ι : Type} [DecidableEq ι] (G : Matrix ι ι ℂ) (m : ℂ)
    (hm : ‖m‖ ≤ 1) (x y : ι) :
    ‖G x y‖ ^ 2 ≤ 2 * ‖entryErr G m x y‖ ^ 2 + 2 * (if x = y then 1 else 0) := by
  have h1 : G x y = entryErr G m x y + (if x = y then m else 0) := by
    unfold entryErr; ring
  have h2 : ‖G x y‖ ≤ ‖entryErr G m x y‖ + ‖(if x = y then m else 0)‖ := by
    rw [h1]; exact norm_add_le _ _
  have h3 : ‖(if x = y then m else 0)‖ ^ 2 ≤ (if x = y then (1 : ℝ) else 0) := by
    split_ifs
    · nlinarith [norm_nonneg m]
    · simp
  have h6 : 0 ≤ ‖G x y‖ := norm_nonneg _
  have h7 : ‖G x y‖ ^ 2 ≤ (‖entryErr G m x y‖ + ‖(if x = y then m else 0)‖) ^ 2 :=
    pow_le_pow_left₀ h6 h2 2
  nlinarith [sq_nonneg (‖entryErr G m x y‖ - ‖(if x = y then m else 0)‖)]

/-- [II, (7.8)] from the local law: off the exceptional event,
`|G_{xy}|² ≤ 2 W^{τ} B_{xy} + 2 δ_{xy}`
and `Σ_{|y − x₀| ≤ K} (B_{xy} + B_{yx}) ≤ C K²/W²` give
`K^{−d} Σ_{|y − x₀| ≤ K} (|G_{xy}|² + |G_{yx}|²) ≤ (2 C W^{τ} + 4) W^{−4} K^{4−d}` for
`W ≤ K ≤ L/2`. -/
private theorem Lem512Zero_h78 {d : ℕ} (hd : 2 ≤ d) (P : Profile d) {c₀ c₁ κ ε c₀T : ℝ} {N : ℕ}
    (hLL : StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2)) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) :
    StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {v : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2 × ℕ //
        p.1.1 ≤ v.2.2.2 ∧ 2 * v.2.2.2 ≤ p.1.2})
      (fun p v ω => boxAvg d p.1.2 (green (hmat ω) v.1.1.1) v.1.2.1 v.1.2.2.1 v.1.2.2.2)
      (fun p v _ => (p.1.1 : ℝ) ^ (2 * ε₀) * (p.1.1 : ℝ) ^ (-4 : ℝ) *
        (v.1.2.2.2 : ℝ) ^ (4 - (d : ℝ))) := by
  intro τ hτ D hD
  obtain ⟨CB, hCB0, hCB⟩ := Continuity_boxB d hd
  have hsz := Moment_tendsto d N c₀ c₁ c₀T
  filter_upwards [hLL (τ / 2) (by positivity) D hD, hsz.eventually (eventually_ge_atTop 1),
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τ / 2)).comp hsz).eventually
      (eventually_ge_atTop (2 * CB + 4))] with p hp hW hWτ
  refine le_trans (measure_mono ?_) hp
  intro ω hω
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hcon
  obtain ⟨v, hv⟩ := hω
  refine absurd hv (not_lt.2 ?_)
  change (1 : ℝ) ≤ p.1.1 at hW
  change 2 * CB + 4 ≤ (p.1.1 : ℝ) ^ (τ / 2) at hWτ
  have hW1n : 1 ≤ p.1.1 := by exact_mod_cast hW
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  obtain ⟨⟨u, x, x₀, K⟩, hK1, hK2⟩ := v
  simp only
  set G := green (hmat ω) u.1 with hG
  have him : 0 < u.1.im := by
    refine lt_of_lt_of_le ?_ u.2.2.1
    exact div_pos (by positivity)
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero p.2) _)
  have hm : ‖msc u.1‖ ≤ 1 := (norm_msc_lt_one him).le
  have hE : ∀ a b : Zd d p.1.2, ‖entryErr G (msc u.1) a b‖ ^ 2 ≤
      W ^ (τ / 2) * bB d p.1.2 p.1.1 a b := fun a b => hcon (u, a, b)
  have hK1' : W ≤ (K : ℝ) := Nat.cast_le.mpr hK1
  have hK0 : 0 < (K : ℝ) := by linarith
  set box := Finset.univ.filter (fun y : Zd d p.1.2 => zdistInf d p.1.2 (y - x₀) ≤ K) with hbox
  have hsum : ∑ y ∈ box, (‖G x y‖ ^ 2 + ‖G y x‖ ^ 2) ≤
      2 * W ^ (τ / 2) * (CB * (K : ℝ) ^ 2 / W ^ 2) + 4 := by
    have hB := hCB p.1.2 p.1.1 hW1n K hK1 hK2 x x₀
    change ∑ y ∈ box, (bB d p.1.2 p.1.1 x y + bB d p.1.2 p.1.1 y x) ≤ _ at hB
    have hpt : ∀ y ∈ box, ‖G x y‖ ^ 2 + ‖G y x‖ ^ 2 ≤
        2 * W ^ (τ / 2) * (bB d p.1.2 p.1.1 x y + bB d p.1.2 p.1.1 y x) +
          (2 * (if x = y then 1 else 0) + 2 * (if y = x then 1 else 0)) := by
      intro y _
      have e1 := Lem512Zero_sq_le G (msc u.1) hm x y
      have e2 := Lem512Zero_sq_le G (msc u.1) hm y x
      have e3 := hE x y
      have e4 := hE y x
      nlinarith
    have hδ : ∑ y ∈ box, (2 * (if x = y then (1 : ℝ) else 0) + 2 * (if y = x then 1 else 0)) ≤
        4 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have h1 : ∑ y ∈ box, (if x = y then (1 : ℝ) else 0) ≤ 1 := by
        rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
      have h2 : ∑ y ∈ box, (if y = x then (1 : ℝ) else 0) ≤ 1 := by
        rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
      linarith
    calc ∑ y ∈ box, (‖G x y‖ ^ 2 + ‖G y x‖ ^ 2)
        ≤ ∑ y ∈ box, (2 * W ^ (τ / 2) * (bB d p.1.2 p.1.1 x y + bB d p.1.2 p.1.1 y x) +
          (2 * (if x = y then 1 else 0) + 2 * (if y = x then 1 else 0))) := Finset.sum_le_sum hpt
      _ = 2 * W ^ (τ / 2) * ∑ y ∈ box, (bB d p.1.2 p.1.1 x y + bB d p.1.2 p.1.1 y x) +
          ∑ y ∈ box, (2 * (if x = y then (1 : ℝ) else 0) + 2 * (if y = x then 1 else 0)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * W ^ (τ / 2) * (CB * (K : ℝ) ^ 2 / W ^ 2) + 4 := by
          gcongr
  have hKd : (0 : ℝ) < (K : ℝ) ^ d := by positivity
  have e1 : (W : ℝ) ^ (-4 : ℝ) = (W ^ 4)⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e2 : (K : ℝ) ^ (4 - (d : ℝ)) = (K : ℝ) ^ 4 / (K : ℝ) ^ d := by
    rw [Real.rpow_sub hK0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.rpow_natCast]
  unfold boxAvg
  rw [← hbox, div_le_iff₀ hKd, e1, e2]
  have hKW : 1 ≤ (K : ℝ) ^ 2 / W ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_pow_left₀ hW0.le hK1' 2
  have hKW4 : (K : ℝ) ^ 2 / W ^ 2 ≤ (K : ℝ) ^ 4 / W ^ 4 := by
    have : (K : ℝ) ^ 4 / W ^ 4 = ((K : ℝ) ^ 2 / W ^ 2) ^ 2 := by ring
    rw [this]; nlinarith
  have hτ2 : W ^ (τ / 2) * W ^ (τ / 2) = W ^ τ := by rw [← Real.rpow_add hW0]; ring_nf
  have hε1 : 1 ≤ W ^ (2 * ε₀) := Real.one_le_rpow hW (by linarith)
  have hτ0 : 1 ≤ W ^ (τ / 2) := Real.one_le_rpow hW (by positivity)
  have hX : 2 * W ^ (τ / 2) * (CB * (K : ℝ) ^ 2 / W ^ 2) + 4 ≤ W ^ τ * ((K : ℝ) ^ 4 / W ^ 4) := by
    have hK4 : 1 ≤ (K : ℝ) ^ 4 / W ^ 4 := hKW.trans hKW4
    have h1 : 2 * W ^ (τ / 2) * (CB * (K : ℝ) ^ 2 / W ^ 2) ≤
        2 * CB * W ^ (τ / 2) * ((K : ℝ) ^ 4 / W ^ 4) := by
      have : CB * (K : ℝ) ^ 2 / W ^ 2 = CB * ((K : ℝ) ^ 2 / W ^ 2) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hKW4 hCB0
      nlinarith
    have h2 : (4 : ℝ) ≤ 4 * W ^ (τ / 2) * ((K : ℝ) ^ 4 / W ^ 4) := by nlinarith
    rw [← hτ2]
    nlinarith
  calc ∑ y ∈ box, (‖G x y‖ ^ 2 + ‖G y x‖ ^ 2)
      ≤ W ^ τ * ((K : ℝ) ^ 4 / W ^ 4) := hsum.trans hX
    _ ≤ sizeW p ^ τ * (W ^ (2 * ε₀) * (W ^ 4)⁻¹ * ((K : ℝ) ^ 4 / (K : ℝ) ^ d)) * (K : ℝ) ^ d := by
        rw [show sizeW p = W from rfl]
        field_simp
        nlinarith [Real.rpow_nonneg hW0.le τ, pow_pos hK0 4]

/-! ## The expectation split for the graphs of `Err` -/

set_option linter.unusedDecidableInType false in
-- the bound is stated with the sample space of a decidable index type
/-- `E f ≤ A + K (1 + t)^q β + K (1 + t)^{−j} E(1 + ‖ω‖)^{q+j}` when `0 ≤ f ≤ A` off an event of
probability at most `β` and `f ≤ K (1 + ‖ω‖)^q` everywhere: on the event, `‖ω‖ ≤ t` or
`(1 + ‖ω‖)^q ≤ (1 + ‖ω‖)^{q+j}/(1 + t)^j`. -/
private theorem Lem512Zero_integral_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : ∀ c, coordVar S c ≤ 1) (f : Sample ι → ℝ) (bad : Set (Sample ι))
    (A K t β : ℝ) (q j : ℕ) (hA : 0 ≤ A) (hK : 0 ≤ K) (ht : 0 ≤ t) (hβ : 0 ≤ β)
    (hbad : gaussLaw S bad ≤ ENNReal.ofReal β) (hf0 : ∀ ω, 0 ≤ f ω)
    (hgood : ∀ ω, ω ∉ bad → f ω ≤ A) (hall : ∀ ω, f ω ≤ K * (1 + ‖ω‖) ^ q) :
    ∫ ω, f ω ∂(gaussLaw S) ≤ A + K * (1 + t) ^ q * β + K * ((1 + t) ^ j)⁻¹ *
      (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) * Fintype.card (Coord ι)) := by
  have := isProbabilityMeasure_gaussLaw S
  obtain ⟨hmi, hmb⟩ := Lem512Zero_moment S hS (q + j)
  set s := toMeasurable (gaussLaw S) bad with hs
  have hsm : MeasurableSet s := measurableSet_toMeasurable _ bad
  have htj : 0 < (1 + t) ^ j := by positivity
  set h : Sample ι → ℝ := fun ω => A + s.indicator (fun _ => K * (1 + t) ^ q) ω +
    K * ((1 + t) ^ j)⁻¹ * (1 + ‖ω‖) ^ (q + j) with hh
  have hint : Integrable h (gaussLaw S) :=
    ((integrable_const A).add ((integrable_const _).indicator hsm)).add (hmi.const_mul _)
  have hle : ∀ ω, f ω ≤ h ω := by
    intro ω
    have hr : 1 ≤ 1 + ‖ω‖ := by linarith [norm_nonneg ω]
    have hind : 0 ≤ s.indicator (fun _ => K * (1 + t) ^ q) ω :=
      Set.indicator_nonneg (fun _ _ => by positivity) _
    have htail : 0 ≤ K * ((1 + t) ^ j)⁻¹ * (1 + ‖ω‖) ^ (q + j) := by positivity
    by_cases hω : ω ∈ bad
    · have hωs : ω ∈ s := subset_toMeasurable _ bad hω
      by_cases hn : ‖ω‖ ≤ t
      · have : f ω ≤ K * (1 + t) ^ q :=
          (hall ω).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith) q) hK)
        rw [hh]; simp only [Set.indicator_of_mem hωs]; linarith
      · have h1 : (1 + t) ^ j ≤ (1 + ‖ω‖) ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
        have h2 : (1 + ‖ω‖) ^ q ≤ ((1 + t) ^ j)⁻¹ * (1 + ‖ω‖) ^ (q + j) := by
          rw [pow_add, inv_mul_eq_div, le_div_iff₀ htj]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have : f ω ≤ K * ((1 + t) ^ j)⁻¹ * (1 + ‖ω‖) ^ (q + j) := by
          rw [mul_assoc]; exact (hall ω).trans (mul_le_mul_of_nonneg_left h2 hK)
        rw [hh]; simp only; linarith
    · rw [hh]; simp only; linarith [hgood ω hω]
  have hμs : (gaussLaw S).real s ≤ β := by
    rw [Measure.real, hs, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hβ hbad
  have hI : ∫ ω, h ω ∂(gaussLaw S) = A + (gaussLaw S).real s * (K * (1 + t) ^ q) +
      K * ((1 + t) ^ j)⁻¹ * ∫ ω, (1 + ‖ω‖) ^ (q + j) ∂(gaussLaw S) := by
    have hi1 : Integrable (fun ω => A + s.indicator (fun _ => K * (1 + t) ^ q) ω) (gaussLaw S) :=
      (integrable_const A).add ((integrable_const _).indicator hsm)
    have hi2 : Integrable (fun ω : Sample ι => K * ((1 + t) ^ j)⁻¹ * (1 + ‖ω‖) ^ (q + j))
        (gaussLaw S) := hmi.const_mul _
    have hi3 : Integrable (fun ω => s.indicator (fun _ => K * (1 + t) ^ q) ω) (gaussLaw S) :=
      (integrable_const _).indicator hsm
    simp only [hh]
    rw [integral_add hi1 hi2, integral_add (integrable_const A) hi3, integral_const,
      integral_indicator_const _ hsm, integral_const_mul]
    simp [smul_eq_mul]
  have hfin : ∫ ω, h ω ∂(gaussLaw S) ≤ A + K * (1 + t) ^ q * β + K * ((1 + t) ^ j)⁻¹ *
      (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) * Fintype.card (Coord ι)) := by
    rw [hI]
    have hKq : 0 ≤ K * (1 + t) ^ q := by positivity
    have e1 : (gaussLaw S).real s * (K * (1 + t) ^ q) ≤ K * (1 + t) ^ q * β := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hμs hKq
    have e2 : K * ((1 + t) ^ j)⁻¹ * ∫ ω, (1 + ‖ω‖) ^ (q + j) ∂(gaussLaw S) ≤
        K * ((1 + t) ^ j)⁻¹ * (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
          Fintype.card (Coord ι)) :=
      mul_le_mul_of_nonneg_left hmb (by positivity)
    linarith
  by_cases hf : Integrable f (gaussLaw S)
  · exact (integral_mono hf hint hle).trans hfin
  · rw [integral_undef hf]
    have : 0 ≤ ∫ ω, h ω ∂(gaussLaw S) :=
      integral_nonneg fun ω => (hf0 ω).trans (hle ω)
    linarith

/-! ## The graphs of `A` -/

/-- **[I, Lemma 5.12], (5.42) for a graph of `A` without internal atoms**
(`Lem512Zero.graphRowStmt`): off the exceptional event of the local law, `Lem512Zero.det` at
`ε₀ = 0` (its weak norm hypothesis follows from the entrywise bound) and
`Σ_y B_{ay} ≤ C L²/W²` ([II, (8.33)]); on it the a priori bound polynomial in `W`. -/
theorem Lem512Zero.graphRow : Lem512Zero.graphRowStmt := by
  intro d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE hLL F hF z hz C g hN hK hTD hDA hLF δ hδ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨τ', hτ', W₀, hW₀⟩ := Lem512Zero.det d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE C g hN
    hK hTD hDA 0 le_rfl (by positivity) (δ / 2) (by positivity)
  obtain ⟨C₁, hC₁0, hC₁⟩ := sumB1 d hd
  obtain ⟨Cw, hCw0, hCw⟩ := Lem512_weakNorm_le d (by omega)
  obtain ⟨K, hKev⟩ := Moment_apriori_graph d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE
    (fun p => {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2}) (fun _ u => u.1) (fun _ u => u.2) g hK
  set e : ℝ := ((g.diagOrd : ℝ) - 2) * d / 2 with he
  set D' : ℝ := |K| + 2 * d / c₁ + |e| + 1 with hD'
  have hD'0 : 0 < D' := by
    have : 0 ≤ 2 * (d : ℝ) / c₁ := by positivity
    have := abs_nonneg K; have := abs_nonneg e; linarith
  have hsz : Tendsto sizeW F atTop := (Moment_tendsto d N c₀ c₁ c₀T).mono_left hF
  have hpow : ∀ r : ℝ, 0 < r → ∀ M : ℝ, ∀ᶠ p in F, M ≤ (p.1.1 : ℝ) ^ r := fun r hr M =>
    ((tendsto_rpow_atTop hr).comp hsz).eventually (eventually_ge_atTop M)
  filter_upwards [hz, (hLL τ' hτ' D' hD'0).filter_mono hF,
    (Moment_ev_adm d N c₀ c₁ c₀T).filter_mono hF, hKev.filter_mono hF,
    hsz.eventually (eventually_ge_atTop (max W₀ 2)), hpow (δ / 2) (by positivity) (2 * C₁),
    hpow (τ' / 2) (by positivity) (max Cw 1)] with p hzp hbad hadm hKp hW hWC hWw
  change max W₀ 2 ≤ (p.1.1 : ℝ) at hW
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  have hW2 : 2 ≤ W := (le_max_right _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hW1n : 1 ≤ p.1.1 := by
    have h : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW1
    exact_mod_cast h
  have : IsProbabilityMeasure (rbmLaw d P p) := isProbabilityMeasure_gaussLaw _
  set bad := {ω | ∃ u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2,
    sizeW p ^ τ' * bB d p.1.2 p.1.1 u.2.1 u.2.2 <
      ‖entryErr (green (hmat ω) u.1.1) (msc u.1.1) u.2.1 u.2.2‖ ^ 2} with hbad_def
  -- off the exceptional event the hypothesis of `Lem512Zero.det` holds at `G = G(ω)`
  have hgood : ∀ ω, ω ∉ bad → ∀ a b : Zd d p.1.2,
      g.absVal (gData (Smat P.ψ p.1.1 p.1.2) (z p) Sig (green (hmat ω) (z p))) ![a, b, b] ≤
        (p.1.1 : ℝ) ^ (δ / 2) * (p.1.1 : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + 0)) *
          bB d p.1.2 p.1.1 a b := by
    intro ω hω
    have hsq : ∀ x y, ‖entryErr (green (hmat ω) (z p)) (msc (z p)) x y‖ ^ 2 ≤
        W ^ τ' * bB d p.1.2 p.1.1 x y := by
      intro x y
      by_contra h
      exact hω ⟨(⟨z p, hzp⟩, x, y), lt_of_not_ge h⟩
    have hent : ∀ x y, ‖entryErr (green (hmat ω) (z p)) (msc (z p)) x y‖ ≤
        W ^ (τ' / 2) * Real.sqrt (bB d p.1.2 p.1.1 x y) := by
      intro x y
      have h := Real.sqrt_le_sqrt (hsq x y)
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (Real.rpow_nonneg hW0.le _),
        Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le] at h
      convert h using 3; ring
    have hwn : weakNorm d p.1.2 p.1.1 1 2 (errAbs (green (hmat ω) (z p)) (z p)) ≤
        W ^ (0 + τ') := by
      refine (hCw p.1.2 p.1.1 hW1n _ (W ^ (τ' / 2)) (Real.rpow_nonneg hW0.le _)
        fun x y => ?_).trans ?_
      · simp only [errAbs, abs_norm]; exact hent x y
      · rw [zero_add]
        have hsplit : W ^ τ' = W ^ (τ' / 2) * W ^ (τ' / 2) := by
          rw [← Real.rpow_add hW0]; ring_nf
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hWw)
          (Real.rpow_nonneg hW0.le _)
    exact hW₀ p.1.1 p.1.2 hadm ((le_max_left _ _).trans hW) (z p) hzp
      (green (hmat ω) (z p)) hwn
  -- the value on the data record of the model is bounded by the absolute-value graph
  have hval : ∀ (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
      ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p)) ![a, b, b] ω‖ ≤
        g.absVal (gData (Smat P.ψ p.1.1 p.1.2) (z p) Sig (green (hmat ω) (z p))) ![a, b, b] := by
    intro a b ω
    rw [Graph.valR_of_labelFree 3 0 g _ _ _ _ _ hLF]
    dsimp only
    rw [Lem512_val_rbm P Sig _ _ _ ω g hK]
    exact norm_val_le_absVal 3 0 _ g _ _
  have hall : ∀ (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
      ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p)) ![a, b, b] ω‖ ≤
        W ^ K := fun a b ω => hKp ⟨z p, hzp⟩ a b ω
  have hβ : (0 : ℝ) ≤ W ^ (-D') := Real.rpow_nonneg hW0.le _
  have hB0 : ∀ a b : Zd d p.1.2, 0 ≤ bB d p.1.2 p.1.1 a b :=
    fun a b => (Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 a b).1
  have hS : ∀ a : Zd d p.1.2, ∑ b, bB d p.1.2 p.1.1 a b ≤ C₁ * (L ^ 2 / W ^ 2) :=
    hC₁ p.1.2 p.1.1 hW1n
  have hexp : W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + 0)) = W ^ (-e) := by
    rw [he]; congr 1; ring
  have hbadμ : rbmLaw d P p bad ≤ ENNReal.ofReal (W ^ (-D')) := hbad
  have hsum := Lem512_sum_le (rbmLaw d P p)
    (fun a b ω => ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
      ![a, b, b] ω‖) (bB d p.1.2 p.1.1) bad (W ^ (δ / 2) * W ^ (-e) * 1) (W ^ K) (W ^ (-D'))
    (C₁ * (L ^ 2 / W ^ 2)) (by positivity) hB0 (Real.rpow_nonneg hW0.le _) hβ hbadμ hS
    (fun a b ω hω => by
      refine (hval a b ω).trans ?_
      have := hgood ω hω a b
      rw [hexp] at this
      linarith)
    hall
  refine hsum.trans ?_
  have := Lem512_arith (d := d) hc₀ hc₁ p hadm δ e K C₁ 1 le_rfl hC₁0 hW2 hWC hδ
  rw [mul_one] at this ⊢
  rw [mul_one] at this
  exact this

/-! ## The graphs of `Err` -/

set_option maxHeartbeats 4000000 in
-- the final count instantiates several eventual statements at once
/-- **[I, Lemma 5.12], (5.43) for a graph of `Err` without internal atoms**
(`Lem512Zero.errRowStmt`): the weights `W_d` are replaced by `d + 1` light weights and the labels
are removed by the resampled row (`labelRemovalErr`, with [II, (7.7)], [II, (7.8)] and
[II, (8.1)] from the local law); the label-free graphs have no internal atoms and diagonal scaling
order at least `n_𝔟`, and are bounded by `Lem512Zero.det` with a loss `W^{(n_𝔟−2)ε₀}` absorbed in
`W^δ`. Off the exceptional event this gives `B_{𝔞𝔟}`; on it the value is at most
`W^K (1 + ‖ω‖)^q`, whose expectation on the event is at most `W^{−D}`. -/
theorem Lem512Zero.errRow : Lem512Zero.errRowStmt := by
  intro d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T N Sig hSE hLL F hF z hz C g hN hK hAE hDC
    hTD hDA δ hδ
  classical
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set nb : ℝ := (g.diagOrd : ℝ) with hnb
  set e : ℝ := (nb - 2) * d / 2 with he
  -- the loss `ε₀` of the label removal, absorbed in `W^{δ/8}`
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ,
      ε₀ = min (δ / (8 * (|nb - 2| + 1))) (min (c₀T / ((N : ℝ) + 1)) ((d : ℝ) / 40)) := ⟨_, rfl⟩
  have hε₀ : 0 < ε₀ := by
    rw [hε₀def]; exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hε₀1 : ε₀ ≤ δ / (8 * (|nb - 2| + 1)) := by rw [hε₀def]; exact min_le_left _ _
  have hε₀2 : ε₀ ≤ c₀T / ((N : ℝ) + 1) := by
    rw [hε₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hε₀3 : ε₀ ≤ (d : ℝ) / 40 := by
    rw [hε₀def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hε₀n : ((N : ℝ) - 1) * ε₀ < c₀T := by
    have : ε₀ * ((N : ℝ) + 1) ≤ c₀T := (le_div_iff₀ hN1).1 hε₀2
    nlinarith
  have hε₀d : ε₀ < (d : ℝ) / 20 := by linarith
  have hε₀δ : (nb - 2) * ε₀ ≤ δ / 8 := by
    have h1 : (nb - 2) * ε₀ ≤ (|nb - 2| + 1) * ε₀ :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self (nb - 2)]) hε₀.le
    have h2 : ε₀ * (8 * (|nb - 2| + 1)) ≤ δ := (le_div_iff₀ (by positivity)).1 hε₀1
    nlinarith
  have hτ₀0 : 0 < δ / 8 := by positivity
  -- the light weights and their label-free graphs
  obtain ⟨hNw, hKw, hAEw, hDCw, hTDw, hDAw, -, -, -, hdow⟩ :=
    G11.wDLights_props g N C hK hN hAE hDC hTD hDA
  set g' := g.wDLights with hg'
  set k := g'.pathElig.card with hk
  have hrow : ∀ S : Finset (Fin g'.comps.length), ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ,
      S ⊆ g'.pathElig → ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ z' ∈ specDom κ ε W L, ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
          weakNorm d L W 1 2 (errAbs G z') ≤ (W : ℝ) ^ (ε₀ + τ') → ∀ a b : Zd d L,
            (g'.pathRepl S).absVal (gData (Smat P.ψ W L) z' Sig G) ![a, b, b] ≤
              (W : ℝ) ^ (δ / 8) * (W : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) *
                bB d L W a b := by
    intro S
    by_cases hS : S ⊆ g'.pathElig
    · obtain ⟨⟨C', hN'⟩, hK', -, -, hTD', hDA', -, -, -, -, -, hdord⟩ :=
        labelPaths 0 _ N g' hNw hKw hAEw hDCw hTDw hDAw (fun h => absurd rfl h) S hS
      obtain ⟨τ', hτ', W₀, hW₀⟩ := Lem512Zero.det d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE C'
        (g'.pathRepl S) hN' hK' hTD' hDA' ε₀ hε₀.le (by linarith) (δ / 8) hτ₀0
      refine ⟨τ', hτ', max W₀ 1, fun _ W L _ hadm hW z' hz' G hwn a b => ?_⟩
      have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
      refine (hW₀ W L hadm (le_trans (le_max_left _ _) hW) z' hz' G hwn a b).trans ?_
      have hSd : nb ≤ ((g'.pathRepl S).diagOrd : ℝ) := by
        have h1 : g'.diagOrd + (S.card : ℤ) ≤ (g'.pathRepl S).diagOrd := hdord
        have h2 : g.diagOrd ≤ (g'.pathRepl S).diagOrd := by rw [← hdow]; omega
        rw [hnb]; exact_mod_cast h2
      have hrate : -((d : ℝ) / 2) + ε₀ ≤ 0 := by linarith
      have hx : (W : ℝ) ^ ((((g'.pathRepl S).diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) ≤
          (W : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (mul_le_mul_of_nonpos_right (by linarith) hrate)
      have hB0 : 0 ≤ bB d L W a b := by unfold bB; positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity)) hB0
    · exact ⟨1, one_pos, 0, fun h => absurd h hS⟩
  choose τ'f hτ'f W₀f hW₀f using hrow
  set τ' := Finset.univ.inf' Finset.univ_nonempty τ'f with hτ'def
  set W₀ := Finset.univ.sup' Finset.univ_nonempty W₀f with hW₀def
  have hτ' : 0 < τ' := (Finset.lt_inf'_iff _).2 fun S _ => hτ'f S
  set U : SizeL → Type := fun p => {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2} with hU
  set β : ∀ p : SizeL, U p → Zd d p.1.2 → Zd d p.1.2 → ℝ := fun p _ a b =>
    (2 : ℝ) ^ k * ((p.1.1 : ℝ) ^ (δ / 8) * (p.1.1 : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) *
      bB d p.1.2 p.1.1 a b) with hβdef
  have hsz := Moment_tendsto d N c₀ c₁ c₀T
  have hβ : ∀ᶠ p in llFilter d N c₀ c₁ c₀T, ∀ (u : U p) (a b : Zd d p.1.2)
      (G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ),
      weakNorm d p.1.2 p.1.1 1 2 (errAbs G u.1) ≤ (p.1.1 : ℝ) ^ (ε₀ + τ') →
      (∀ x y, ‖entryErr G (msc u.1) x y‖ ≤
        (p.1.1 : ℝ) ^ τ' * (Real.sqrt (bB d p.1.2 p.1.1 x y) + Entrywise_Phi d N c₀T ε₀ 0 p)) →
      ∑ S ∈ g'.pathElig.powerset, (g'.pathRepl S).absVal
          (gData (Smat P.ψ p.1.1 p.1.2) u.1 Sig G) ![a, b, b] ≤ β p u a b := by
    filter_upwards [Moment_ev_adm d N c₀ c₁ c₀T, hsz.eventually (eventually_ge_atTop W₀),
      hsz.eventually (eventually_ge_atTop 1)] with p hp hW hW1p u a b G hwn _
    change (1 : ℝ) ≤ p.1.1 at hW1p
    have hle : ∀ S ∈ g'.pathElig.powerset, (g'.pathRepl S).absVal
        (gData (Smat P.ψ p.1.1 p.1.2) u.1 Sig G) ![a, b, b] ≤
        (p.1.1 : ℝ) ^ (δ / 8) * (p.1.1 : ℝ) ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) *
          bB d p.1.2 p.1.1 a b := by
      intro S hS
      have hτS : τ' ≤ τ'f S := Finset.inf'_le _ (Finset.mem_univ S)
      have hWS : W₀f S ≤ W₀ := Finset.le_sup' _ (Finset.mem_univ S)
      refine hW₀f S (Finset.mem_powerset.1 hS) p.1.1 p.1.2 hp (hWS.trans hW) u.1 u.2 G ?_ a b
      exact hwn.trans (Real.rpow_le_rpow_of_exponent_le hW1p (by linarith))
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    push_cast
    exact le_rfl
  -- the hypotheses of the label removal
  have h77 := Lem512Zero_h77 (by omega) P hLL ε₀ hε₀.le
  have h78 := Lem512Zero_h78 (by omega) P hLL ε₀ hε₀.le
  have h81 := Entrywise_base hd P (κ := κ) (ε := ε) (c₀T := c₀T) (ε₀ := ε₀) (n := N) hc₀ hc₁
    (U' := U) (fun _ u => u.1) (fun _ u => u.2) h77
  have hδΦ : 0 < (d : ℝ) / 2 - ε₀ := by linarith
  have hΦ : ∀ᶠ p in llFilter d N c₀ c₁ c₀T, ∀ _u : U p,
      0 ≤ Entrywise_Phi d N c₀T ε₀ 0 p ∧
        Entrywise_Phi d N c₀T ε₀ 0 p ≤ (p.1.1 : ℝ) ^ (-((d : ℝ) / 2 - ε₀)) :=
    Eventually.of_forall fun p _ => ⟨Entrywise_Phi_nonneg _ _ _ _ _ _, by
      rw [Entrywise_Phi_zero]; exact le_of_eq (by congr 1; ring)⟩
  have hD' : 0 < δ / 8 + 2 * d / c₁ + |e| + 2 := by
    have : 0 ≤ 2 * (d : ℝ) / c₁ := by positivity
    have := abs_nonneg e
    linarith
  have hLR := labelRemovalErr d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T N Sig ε₀ hε₀ hε₀n hε₀d
    U (fun _ u => u.1) (fun _ u => u.2) h77 h78 (fun p _ => Entrywise_Phi d N c₀T ε₀ 0 p)
    ((d : ℝ) / 2 - ε₀) hδΦ hΦ h81 N 0 g hK τ' hτ' β hβ _ hD'
  -- the a priori bound and the exponents of the exceptional event
  obtain ⟨Ka, q, hKa0, hap⟩ :=
    Lem512Zero_apriori d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE g hK
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌈Ka + 4 * d / c₁ + |e| + 3⌉₊ := ⟨_, rfl⟩
  have hjge : Ka + 4 * d / c₁ + |e| + 3 ≤ (j : ℝ) := by rw [hj]; exact Nat.le_ceil _
  obtain ⟨Cq, hCq⟩ : ∃ Cq : ℝ, Cq = 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) :=
    ⟨_, rfl⟩
  have hgm : 0 ≤ LabelRemoval.gaussMoment (q + j) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hCq0 : 0 ≤ Cq := by rw [hCq]; positivity
  have hDd : 0 < Ka + 2 * q + 2 * d / c₁ + |e| + 2 := by
    have : 0 ≤ 2 * (d : ℝ) / c₁ := by positivity
    have := abs_nonneg e
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := sumB1 d hd
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  have hszF : Tendsto sizeW F atTop := hsz.mono_left hF
  have hpow : ∀ r : ℝ, 0 < r → ∀ M : ℝ, ∀ᶠ p in F, M ≤ (p.1.1 : ℝ) ^ r := fun r hr M =>
    ((tendsto_rpow_atTop hr).comp hszF).eventually (eventually_ge_atTop M)
  filter_upwards [hz, (hLR (δ / 8) hτ₀0 _ hDd).filter_mono hF, hap.filter_mono hF,
    (Moment_ev_adm d N c₀ c₁ c₀T).filter_mono hF,
    hszF.eventually (eventually_ge_atTop (max 3 (max W₂ (3 * Cq + 1)))),
    hpow (δ / 8) hτ₀0 ((2 : ℝ) ^ k), hpow (δ / 2) (by positivity) (2 * C₁)] with
    p hzp hbad happ hadm hW hWk hWC
  change max 3 (max W₂ (3 * Cq + 1)) ≤ (p.1.1 : ℝ) at hW
  have hW3 : (3 : ℝ) ≤ p.1.1 := (le_max_left _ _).trans hW
  have hW1n : 1 ≤ p.1.1 := by
    have h : (1 : ℝ) ≤ (p.1.1 : ℝ) := by linarith
    exact_mod_cast h
  have hS1 : ∀ c', coordVar (Smat P.ψ p.1.1 p.1.2) c' ≤ 1 :=
    LabelRemoval_coordVar_le _ (hds p.1.1 p.1.2 hadm ((le_max_left _ _).trans
      ((le_max_right _ _).trans hW)))
  have hCqW : 3 * Cq + 1 ≤ (p.1.1 : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have : IsProbabilityMeasure (rbmLaw d P p) := isProbabilityMeasure_gaussLaw _
  set u₀ : U p := ⟨z p, hzp⟩ with hu₀
  have hB0 : ∀ a b : Zd d p.1.2, 0 ≤ bB d p.1.2 p.1.1 a b :=
    fun a b => (Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 a b).1
  have hβ0 : ∀ a b, 0 ≤ β p u₀ a b := fun a b => by
    simp only [hβdef]
    have := hB0 a b
    positivity
  -- the expectation of one entry
  set R₂ : ℝ := W ^ (δ / 8) * W ^ (-(δ / 8 + 2 * d / c₁ + |e| + 2)) +
    W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + 2 * d / c₁ + |e| + 2)) +
    W ^ Ka * ((1 + W) ^ j)⁻¹ *
      (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
        Fintype.card (Coord (Zd d p.1.2))) with hR₂
  set cB : ℝ := W ^ (δ / 8) * ((2 : ℝ) ^ k * (W ^ (δ / 8) *
    W ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)))) with hcB
  have hent : ∀ a b : Zd d p.1.2,
      ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤ cB * bB d p.1.2 p.1.1 a b + R₂ := by
    intro a b
    have h := Lem512Zero_integral_le (Smat P.ψ p.1.1 p.1.2) hS1
      (fun ω => ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖)
      {ω | ∃ v : U p × Zd d p.1.2 × Zd d p.1.2,
        sizeW p ^ (δ / 8) * (β p v.1 v.2.1 v.2.2 +
          sizeW p ^ (-(δ / 8 + 2 * d / c₁ + |e| + 2))) <
        ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 v.1.1)
          ![v.2.1, v.2.2, v.2.2] ω‖}
      (W ^ (δ / 8) * (β p u₀ a b + W ^ (-(δ / 8 + 2 * d / c₁ + |e| + 2)))) (W ^ Ka) W
      (W ^ (-(Ka + 2 * q + 2 * d / c₁ + |e| + 2))) q j
      (mul_nonneg (by positivity) (add_nonneg (hβ0 a b) (by positivity))) (by positivity)
      hW0.le (by positivity) hbad (fun ω => norm_nonneg _)
      (fun ω hω => by
        by_contra hcon
        exact hω ⟨(u₀, a, b), lt_of_not_ge hcon⟩)
      (fun ω => happ u₀ a b ω)
    refine h.trans (le_of_eq ?_)
    rw [hR₂, hcB, hβdef]
    ring
  have hsum : ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
      ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
      (Fintype.card (Zd d p.1.2) : ℝ) * (cB * (C₁ * (L ^ 2 / W ^ 2))) +
        (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 * R₂ := by
    have hcB0 : 0 ≤ cB := by rw [hcB]; positivity
    calc _ ≤ ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2, (cB * bB d p.1.2 p.1.1 a b + R₂) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hent a b
      _ = ∑ a : Zd d p.1.2, (cB * ∑ b, bB d p.1.2 p.1.1 a b +
            (Fintype.card (Zd d p.1.2) : ℝ) * R₂) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
      _ ≤ ∑ a : Zd d p.1.2, (cB * (C₁ * (L ^ 2 / W ^ 2)) +
            (Fintype.card (Zd d p.1.2) : ℝ) * R₂) :=
          Finset.sum_le_sum fun a _ => by gcongr; exact hC₁ p.1.2 p.1.1 hW1n a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  refine hsum.trans ?_
  -- the exponents
  have hcB : cB ≤ W ^ (δ / 2) * W ^ (-e) * 1 := by
    have hX : W ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀)) ≤ W ^ (δ / 8) * W ^ (-e) := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by rw [he]; nlinarith)
    have h2k : (2 : ℝ) ^ k ≤ W ^ (δ / 8) := hWk
    have hsplit : W ^ (δ / 2) = W ^ (δ / 8) * W ^ (δ / 8) * W ^ (δ / 8) * W ^ (δ / 8) := by
      rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
    rw [hcB, hsplit, mul_one]
    have h8 : 0 ≤ W ^ (δ / 8) := by positivity
    calc W ^ (δ / 8) * ((2 : ℝ) ^ k * (W ^ (δ / 8) * W ^ ((nb - 2) * (-((d : ℝ) / 2) + ε₀))))
        ≤ W ^ (δ / 8) * (W ^ (δ / 8) * (W ^ (δ / 8) * (W ^ (δ / 8) * W ^ (-e)))) := by
          gcongr
      _ = _ := by ring
  have hR₂ : R₂ ≤ W ^ (0 : ℝ) * W ^ (-(|(0 : ℝ)| + 2 * d / c₁ + |e| + 1)) := by
    rw [Real.rpow_zero, one_mul, abs_zero, zero_add]
    set Y : ℝ := 2 * d / c₁ + |e| with hY
    have hY0 : 0 ≤ Y := by
      have : 0 ≤ 2 * (d : ℝ) / c₁ := by positivity
      have := abs_nonneg e
      linarith
    have t1 : W ^ (δ / 8) * W ^ (-(δ / 8 + 2 * d / c₁ + |e| + 2)) = W ^ (-(Y + 2)) := by
      rw [← Real.rpow_add hW0, hY]; congr 1; ring
    have h1W : 1 + W ≤ W ^ 2 := by nlinarith
    have t2 : W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + 2 * d / c₁ + |e| + 2)) ≤
        W ^ (-(Y + 2)) := by
      have : (1 + W) ^ q ≤ W ^ ((2 * q : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, pow_mul]
        exact pow_le_pow_left₀ (by linarith) h1W q
      calc W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + 2 * d / c₁ + |e| + 2))
          ≤ W ^ Ka * W ^ ((2 * q : ℕ) : ℝ) * W ^ (-(Ka + 2 * q + 2 * d / c₁ + |e| + 2)) := by
            gcongr
        _ = W ^ (-(Y + 2)) := by
            rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, hY]; congr 1; push_cast; ring
    have hcard : (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ 3 * W ^ (2 * (d : ℝ) / c₁) := by
      refine LabelRemoval_card_coord.trans ?_
      have h0 : (Fintype.card (Zd d p.1.2) : ℝ) ≤ W ^ ((d : ℝ) / c₁) :=
        card_Zd_le_adm d c₀ c₁ hc₁ p hadm
      have h2 : (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ W ^ (2 * (d : ℝ) / c₁) := by
        calc (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ (W ^ ((d : ℝ) / c₁)) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) h0 2
          _ = W ^ (2 * (d : ℝ) / c₁) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
      linarith
    have hX1 : 1 ≤ W ^ (2 * (d : ℝ) / c₁) := Real.one_le_rpow hW1 (by positivity)
    have hMq : 1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
        (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ W ^ (2 * (d : ℝ) / c₁ + 1) := by
      rw [Real.rpow_add hW0, Real.rpow_one, ← hCq]
      have e1 : Cq * (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤
          3 * Cq * W ^ (2 * (d : ℝ) / c₁) := by nlinarith
      nlinarith
    have t3 : W ^ Ka * ((1 + W) ^ j)⁻¹ *
        (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
          Fintype.card (Coord (Zd d p.1.2))) ≤ W ^ (-(Y + 2)) := by
      have hinv : ((1 + W) ^ j)⁻¹ ≤ W ^ (-(j : ℝ)) := by
        rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hW0.le (by linarith) j)
      calc W ^ Ka * ((1 + W) ^ j)⁻¹ *
            (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
              Fintype.card (Coord (Zd d p.1.2)))
          ≤ W ^ Ka * W ^ (-(j : ℝ)) * W ^ (2 * (d : ℝ) / c₁ + 1) := by
            gcongr
        _ = W ^ (Ka - j + (2 * (d : ℝ) / c₁ + 1)) := by
            rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
        _ ≤ W ^ (-(Y + 2)) := Real.rpow_le_rpow_of_exponent_le hW1 (by
            rw [hY]
            have : 4 * (d : ℝ) / c₁ = 2 * (2 * d / c₁) := by ring
            linarith)
    have hsum3 : 3 * W ^ (-(Y + 2)) ≤ W ^ (-(Y + 1)) := by
      have e : W ^ (-(Y + 1)) = W ^ (-(Y + 2)) * W := by
        rw [← Real.rpow_add_one hW0.ne']; congr 1; ring
      rw [e]
      have : 0 ≤ W ^ (-(Y + 2)) := Real.rpow_nonneg hW0.le _
      nlinarith
    have hfin : W ^ (-(Y + 1)) = W ^ (-(2 * d / c₁ + |e| + 1)) := by rw [hY]
    rw [hR₂, ← hfin]
    linarith
  have harith := Lem512_arith (d := d) hc₀ hc₁ p hadm δ e 0 C₁ 1 le_rfl hC₁0 (by linarith) hWC hδ
  have hcard0 : 0 ≤ (Fintype.card (Zd d p.1.2) : ℝ) := Nat.cast_nonneg _
  calc (Fintype.card (Zd d p.1.2) : ℝ) * (cB * (C₁ * (L ^ 2 / W ^ 2))) +
        (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 * R₂
      ≤ (Fintype.card (Zd d p.1.2) : ℝ) * (W ^ (δ / 2) * W ^ (-e) * 1 * (C₁ * (L ^ 2 / W ^ 2))) +
          (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 *
            (W ^ (0 : ℝ) * W ^ (-(|(0 : ℝ)| + 2 * d / c₁ + |e| + 1))) := by
        gcongr
    _ ≤ W ^ δ * L ^ d * (L ^ 2 / W ^ 2) * 1 * W ^ (-e) := harith
    _ = _ := by rw [he, mul_one]

/-! ## The bound per record -/

/-- The diagonal scaling order is at least the scaling order minus `2`. -/
private theorem Lem512Zero_diagOrd_ge {n : ℕ} (g : Graph 3 n) : g.ord - 2 ≤ g.diagOrd := by
  unfold Graph.diagOrd; split_ifs <;> omega

/-- **[I, Lemma 5.12], (5.42)–(5.43) for the graphs without internal atoms** of a record
(`Lem512Zero.recordRowsStmt`): `Lem512Zero.graphRow` on the graphs of `A` and `Lem512Zero.errRow`
on the graphs of `Err` without internal atoms, with `n_𝔟 ≥ ord − 2 ≥ n − 1` on `A` and
`n_𝔟 ≥ D − 1` on `Err`; the number of graphs is absorbed in `W^{δ/2}`. -/
theorem Lem512Zero.recordRows : Lem512Zero.recordRowsStmt := by
  intro d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T N n D Sig 𝒯 hSE hSh h63 hLL F hF z hz δ hδ
  obtain ⟨⟨hS1, hS2⟩, -, hSA, -, hSErr⟩ := hSh
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hsz : Tendsto sizeW F atTop := (Moment_tendsto d N c₀ c₁ c₀T).mono_left hF
  set T : SizeL → ℝ → ℝ := fun p r => (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
    (p.1.1 : ℝ) ^ (-((r - 3) * d / 2)) with hT
  have hrowA : ∀ g ∈ 𝒯.A.filter (fun g => g.1 = 0), ∀ᶠ p in F,
      ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
        ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
          ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤ (p.1.1 : ℝ) ^ (δ / 2) * T p n := by
    intro g hg
    obtain ⟨hgA, hg0⟩ := List.mem_filter.1 hg
    have hg0' : g.1 = 0 := by simpa using hg0
    obtain ⟨m, g2⟩ := g
    simp only at hg0'
    subst hg0'
    obtain ⟨⟨C, hNo⟩, hK, -, -⟩ := hS1 _ (by simp only [List.mem_append]; tauto)
    obtain ⟨hTD, hDA⟩ := h63.1 _ (by simp only [List.mem_append]; tauto)
    obtain ⟨hLF, hord⟩ := hSA _ hgA
    have hrow := Lem512Zero.graphRow d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE hLL F hF z
      hz C g2 hNo hK hTD hDA hLF (δ / 2) (by positivity)
    filter_upwards [hrow, hsz.eventually (eventually_ge_atTop 1)] with p hp hW
    change (1 : ℝ) ≤ p.1.1 at hW
    refine hp.trans ?_
    have hdo : ((n : ℝ) - 3) ≤ ((g2.diagOrd : ℝ) - 2) := by
      have h1 := Lem512Zero_diagOrd_ge g2
      have hord' : (n : ℤ) < g2.ord := hord
      have : (n : ℤ) - 1 ≤ g2.diagOrd := by omega
      have : ((n : ℤ) : ℝ) - 1 ≤ (g2.diagOrd : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hle := Lem512_rpow_neg_le (p.1.1 : ℝ) (((g2.diagOrd : ℝ) - 2) * d / 2)
      (((n : ℝ) - 3) * d / 2) hW (by nlinarith)
    simp only [hT]
    have : 0 ≤ (p.1.1 : ℝ) ^ (δ / 2) * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) := by
      positivity
    calc (p.1.1 : ℝ) ^ (δ / 2) * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-(((g2.diagOrd : ℝ) - 2) * d / 2))
        ≤ (p.1.1 : ℝ) ^ (δ / 2) * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-(((n : ℝ) - 3) * d / 2)) := mul_le_mul_of_nonneg_left hle this
      _ = _ := by ring
  have hrowE : ∀ g ∈ 𝒯.Err.filter (fun g => g.1 = 0), ∀ᶠ p in F,
      ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
        ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
          ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤ (p.1.1 : ℝ) ^ (δ / 2) * T p D := by
    intro g hg
    obtain ⟨hgE, hg0⟩ := List.mem_filter.1 hg
    have hg0' : g.1 = 0 := by simpa using hg0
    obtain ⟨m, g2⟩ := g
    simp only at hg0'
    subst hg0'
    obtain ⟨⟨C, hNo⟩, hK, hAE, hDC⟩ := hS2 _ hgE
    obtain ⟨hTD, hDA⟩ := h63.1 _ (by simp only [List.mem_append]; tauto)
    have hord := hSErr _ hgE
    have hrow := Lem512Zero.errRow d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T N Sig hSE hLL F hF
      z hz C g2 hNo hK hAE hDC hTD hDA (δ / 2) (by positivity)
    filter_upwards [hrow, hsz.eventually (eventually_ge_atTop 1)] with p hp hW
    change (1 : ℝ) ≤ p.1.1 at hW
    refine hp.trans ?_
    have hdo : ((D : ℝ) - 3) ≤ ((g2.diagOrd : ℝ) - 2) := by
      have h1 := Lem512Zero_diagOrd_ge g2
      have hord' : (D : ℤ) < g2.ord := hord
      have : (D : ℤ) - 1 ≤ g2.diagOrd := by omega
      have : ((D : ℤ) : ℝ) - 1 ≤ (g2.diagOrd : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hle := Lem512_rpow_neg_le (p.1.1 : ℝ) (((g2.diagOrd : ℝ) - 2) * d / 2)
      (((D : ℝ) - 3) * d / 2) hW (by nlinarith)
    simp only [hT]
    have : 0 ≤ (p.1.1 : ℝ) ^ (δ / 2) * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) := by
      positivity
    calc (p.1.1 : ℝ) ^ (δ / 2) * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-(((g2.diagOrd : ℝ) - 2) * d / 2))
        ≤ (p.1.1 : ℝ) ^ (δ / 2) * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-(((D : ℝ) - 3) * d / 2)) := mul_le_mul_of_nonneg_left hle this
      _ = _ := by ring
  filter_upwards [Moment_ev_list _ hrowA, Moment_ev_list _ hrowE,
    hsz.eventually (eventually_ge_atTop 1),
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).comp hsz).eventually
      (eventually_ge_atTop ((𝒯.A.length + 𝒯.Err.length : ℕ) : ℝ))] with p hA hE hW hWl
  change (1 : ℝ) ≤ p.1.1 at hW
  change ((𝒯.A.length + 𝒯.Err.length : ℕ) : ℝ) ≤ (p.1.1 : ℝ) ^ (δ / 2) at hWl
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have hT0 : ∀ r, 0 ≤ T p r := fun r => by simp only [hT]; positivity
  have hlenA : (((𝒯.A.filter fun g => g.1 = 0)).length : ℝ) ≤ (p.1.1 : ℝ) ^ (δ / 2) := by
    refine le_trans ?_ hWl
    have : ((𝒯.A.filter fun g => g.1 = 0).length : ℝ) ≤ 𝒯.A.length := by
      exact_mod_cast List.length_filter_le _ _
    push_cast
    have := Nat.cast_nonneg (α := ℝ) 𝒯.Err.length
    linarith
  have hlenE : (((𝒯.Err.filter fun g => g.1 = 0)).length : ℝ) ≤ (p.1.1 : ℝ) ^ (δ / 2) := by
    refine le_trans ?_ hWl
    have : ((𝒯.Err.filter fun g => g.1 = 0).length : ℝ) ≤ 𝒯.Err.length := by
      exact_mod_cast List.length_filter_le _ _
    push_cast
    have := Nat.cast_nonneg (α := ℝ) 𝒯.A.length
    linarith
  constructor
  · have := Lem512_list_le _ _ (p.1.1 : ℝ) δ (T p n) hW0 (hT0 n) hlenA hA
    refine this.trans (le_of_eq ?_)
    simp only [hT]; ring
  · have := Lem512_list_le _ _ (p.1.1 : ℝ) δ (T p D) hW0 (hT0 D) hlenE hE
    refine this.trans (le_of_eq ?_)
    simp only [hT]; ring

end RBM8D
