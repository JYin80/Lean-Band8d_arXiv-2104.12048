import RBM8D.LocalLaw.Primed

/-!
# The cutoff-moment argument for the local law: definitions and statements

The definitions and statements of the cutoff-moment bootstrap for [II, Theorem 3.6] in the form
`localLawTExpStmt'`:

* `Graph.absValHook`: the absolute-value graph with an extra weight at an internal atom;
* `cutD`, `cutX`, `cutY`, `cutM`, `cutPhi`, `cutC`, `cutZ`: the quantities `D^s_{ab}`,
  `X_{ab} = D^s_{ab}/B_{ab}`, `Y`, the soft maximum `M`, the profile `φ`, the cutoff `C` and
  `Z_{ab} = C X_{ab}`;
* `resampleRow`: the sample with row and column `y` resampled, giving `H'_y`;
* `hookGraphSumStmt`: the hook graph sum; `cutImproveStmt`: the improvement on the cutoff event;
  `cutPairStmt`: the pair event; `cutMomentStmt`: the cutoff moment bound. Together,
  `cutImproveStmt` and `cutMomentStmt` give `localLawTExpStmt'`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Complex

namespace RBM8D

open Graphs

/-- The absolute-value graph `𝒢^{abs}` (`Graph.absVal`) with the extra factor `w(σ(v))` at the
internal atom `v`: the hook graph sum `H^c_g` when `w = B_{c·}^{1/2}`. -/
def Graphs.Graph.absValHook {k n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (D : Data ι) (e : Fin k → ι) (v : Fin n) (w : ι → ℝ) : ℝ :=
  ∑ s : Fin n → ι, w (s v) *
    (‖Γ.coeff.eval D.m‖ * (Γ.comps.map fun c => ‖Comp.val D (Sum.elim e s) c‖).prod)

section Defs

variable {d L : ℕ} [NeZero L]

/-- `D^s_{ab} = Σ_{i,j} s_{ai} |G_{ij}|² s_{jb}`. -/
def cutD (S : Matrix (Zd d L) (Zd d L) ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) : ℝ :=
  ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b

/-- `X_{ab} = D^s_{ab} / B_{ab}`. -/
def cutX (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (a b : Zd d L) : ℝ :=
  cutD S G a b / bB d L W a b

/-- `Y = max_{i,j} |G_{ij} − m δ_{ij}| / B_{ij}^{1/2}`. -/
def cutY (W : ℕ) (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ) : ℝ :=
  ⨆ i, ⨆ j, ‖entryErr G m i j‖ / Real.sqrt (bB d L W i j)

/-- The soft maximum `M = (Σ_{a,b} (1 + X_{ab})^l)^{1/l}`. -/
def cutM (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ) : ℝ :=
  (∑ a, ∑ b, (1 + cutX W S G a b) ^ l) ^ ((1 : ℝ) / l)

/-- `φ`: `1` on `(−∞, 1]`, `0` on `[2, ∞)`, linear in between. -/
def cutPhi (t : ℝ) : ℝ := max 0 (min 1 (2 - t))

/-- The cutoff `C(H) = 1{Y ≤ W^β} φ(M / W^α)`. -/
def cutC (β α : ℝ) (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (m : ℂ) : ℝ :=
  if cutY W G m ≤ (W : ℝ) ^ β then cutPhi (cutM l W S G / (W : ℝ) ^ α) else 0

/-- `Z_{ab} = C(H) X_{ab}`. -/
def cutZ (β α : ℝ) (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (m : ℂ) (a b : Zd d L) : ℝ :=
  cutC β α l W S G m * cutX W S G a b

end Defs

/-- The sample with the coordinates of row and column `y` taken from `η` and the others from `ω`:
the resampled matrix `H'_y = hmat (resampleRow y η ω)`. -/
def resampleRow {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι) (η ω : Sample ι) : Sample ι :=
  (rowCoords y).piecewise η ω

/-- **The hook graph sum**: for a graph with the
hypotheses of the third clause of `graphSumStmt''` and an internal atom `v`, for every centre
`c`, `Σ_σ K_g(a, b; σ) B_{c σ(v)}^{1/2} ≤ W^τ W^{−(n_𝔟 − 2)d/2} W^{−d/2} B_{ab}` at `𝔟₁ = 𝔟₂ = b`,
for every single matrix `G` with `|G_{xy} − δ_{xy} m| ≤ W^{τ'} B_{xy}^{1/2}`. -/
def hookGraphSumStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (nI C : ℕ) (g : Graph 3 nI), g.Normal C → g.TKinds N → g.AtExternals →
      g.DoublyConnected → g.TensorDiffusive → g.DotsAcyclic → ¬ g.DiagRecoll → g.RootedAtExt →
      ∀ (v : Fin nI) (τ : ℝ), 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
        (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
          ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
            (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) →
            ∀ a b c : Zd d L,
              g.absValHook (gData (Smat P.ψ W L) z Sig G) ![a, b, b] v
                  (fun y => Real.sqrt (bB d L W c y)) ≤
                (W : ℝ) ^ τ * (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
                  (W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b

/-- **The improvement on the cutoff event**: for `0 < β < d/100`,
`α, γ > 0`, uniformly in `z ∈ 𝐃(κ, ε)`, the event `Y ≤ W^β`, `max_{ab} X_{ab} ≤ 2W^α`,
`Y > W^{α/2 + γ}` has probability at most `W^{−D_m}`, eventually along `adm(c₀, c₁)`. -/
def cutImproveStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ β α γ : ℝ, 0 < β → β < (d : ℝ) / 100 → 0 < α → 0 < γ →
    ∀ Dm : ℝ, 0 < Dm → ∀ᶠ p in admFilterL c₀ c₁, ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      rbmLaw d P p {ω | cutY p.1.1 (green (hmat ω) z) (msc z) ≤ (p.1.1 : ℝ) ^ β ∧
          (∀ a b, cutX p.1.1 (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) z) a b ≤
            2 * (p.1.1 : ℝ) ^ α) ∧
          (p.1.1 : ℝ) ^ (α / 2 + γ) < cutY p.1.1 (green (hmat ω) z) (msc z)} ≤
        ENNReal.ofReal ((p.1.1 : ℝ) ^ (-Dm))

/-- **The pair event**: for `0 < β < d/100`,
`α = β/10` and `l ≥ 1`, uniformly in `z ∈ 𝐃(κ, ε)` and `y`, under the law of `(ω, η)`, the
event `C(H) > 0` and not [`Y(H'_y) ≤ W^β` and `|X_{ab}(H) − X_{ab}(H'_y)| ≤
W^{4β}(B_{ay}^{1/2} + B_{by}^{1/2})` for all `a, b`] has probability at most `W^{−D_m}`. -/
def cutPairStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ β : ℝ, 0 < β → β < (d : ℝ) / 100 → ∀ l : ℕ, 1 ≤ l →
    ∀ Dm : ℝ, 0 < Dm → ∀ᶠ p in admFilterL c₀ c₁, ∀ z ∈ specDom κ ε p.1.1 p.1.2,
      ∀ y : Zd d p.1.2,
        ((rbmLaw d P p).prod (rbmLaw d P p))
          {q | 0 < cutC β (β / 10) l p.1.1 (Smat P.ψ p.1.1 p.1.2) (green (hmat q.1) z) (msc z) ∧
            ¬ (cutY p.1.1 (green (hmat (resampleRow y q.2 q.1)) z) (msc z) ≤
                (p.1.1 : ℝ) ^ β ∧
              ∀ a b, |cutX p.1.1 (Smat P.ψ p.1.1 p.1.2) (green (hmat q.1) z) a b -
                  cutX p.1.1 (Smat P.ψ p.1.1 p.1.2) (green (hmat (resampleRow y q.2 q.1)) z) a b| ≤
                (p.1.1 : ℝ) ^ (4 * β) *
                  (Real.sqrt (bB d p.1.2 p.1.1 a y) + Real.sqrt (bB d p.1.2 p.1.1 b y)))} ≤
          ENNReal.ofReal ((p.1.1 : ℝ) ^ (-Dm))

/-- **The cutoff moment bound**: for an `n`-th order `T`-expansion with
`D`-th order error, `D ≥ n + 4`, with `TRec.Def63G11`, there is `β₀ > 0` such that for
`0 < β ≤ β₀`, `α = β/10`, every `ν > 0`, `l, q ≥ 1`, eventually along `llFilter`,
`E Z_{ab}(z)^q ≤ W^{qν}` uniformly in `z ∈ 𝐃(κ, ε)` and `a, b`. -/
def cutMomentStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → 0 < c₀T →
    ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), n + 4 ≤ D →
      IsTExpansion d (smatVar P) Sig n D 𝒯 → 𝒯.Def63G11 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β ≤ β₀ → ∀ ν : ℝ, 0 < ν → ∀ l q : ℕ, 1 ≤ l → 1 ≤ q →
        ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ z ∈ specDom κ ε p.1.1 p.1.2, ∀ a b : Zd d p.1.2,
          ∫ ω, cutZ β (β / 10) l p.1.1 (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) z) (msc z) a b ^ q
              ∂(rbmLaw d P p) ≤ (p.1.1 : ℝ) ^ ((q : ℝ) * ν)

end RBM8D
