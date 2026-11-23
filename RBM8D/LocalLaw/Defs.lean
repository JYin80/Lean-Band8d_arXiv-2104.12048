module

public import RBM8D.TExp.Second
public import RBM8D.Bound.GraphAbs
public import RBM8D.Bound.Norm
public import RBM8D.Bound.Chain
public import RBM8D.Input.GT
public import RBM8D.Input.GTDiag
public import RBM8D.Graph.Local.ModelGauss
public import RBM8D.Graph.Rooting

@[expose] public section

/-!
# The local law from a T-expansion: definitions and statements

Statements, as propositions, of [I, Theorem 2.16] = [II, Theorem 3.6] and of the steps of its
proof in [I, §5.2] and [II, §7–§8], with the interface [II, Lemma 9.1] = [I, Lemma 5.6]:

* the clauses of [II, Def 6.3] read by [II, (8.18)–(8.24)] at `𝔟₁ = 𝔟₂`: every component at `⊗` is
  diffusive, the dotted edges form a forest, the graphs of `R` and `A` with `⊕`, `⊖` in one
  dotted block have scaling order at least `5`, and the graphs of `A`, `Q` and `Err` with an
  internal atom that are not `⊕`-recollision graphs at `𝔟₁ = 𝔟₂` are rooted at `⊗`, `⊕`, `⊖`
  (`Graph.RootedAtExt`); the diagonal scaling order `n_𝔟 = ord − 2·[⊕, ⊖ in one dotted block]`;
* the doubly connected bound [I, (6.40)] and the graph-summation estimate [II, Claim 8.6] in
  the form with external atoms `⊗, ⊕, ⊖`; the estimate [II, Claim 8.6] with the diagonal scaling
  order, with the bound [II, (8.21)] for the graphs with a dotted edge at `𝔟` after
  `𝔟₁ = 𝔟₂`, and with the bound of the labelled `Θ` edge for the graphs without internal atom,
  on a formal sum and per graph;
* the removal of the `P`/`Q` labels of a graph by the resampled row of the label atom: the
  label-free graphs with a path through the label atom (the Schur complement identity), their
  structure, and the bound of the labelled value by their values at single matrices with the
  bounds of [II, Notation 8.8]; the monotonicity of the absolute-value graph in the moduli of the
  resolvent entries;
* the condition [II, (3.15)] on `L`, the filter of the local law, the matrix `A` of [II, (9.1)]
  and the moment bound [II, Lemma 9.1];
* [II, Theorem 3.6] along this filter, and [II, Lemmas 7.2, 7.3, 7.4, 8.1] and [II, Claim 8.7];
* the second order `T`-expansion as a `T`-expansion with every error order `D > 2` and the
  clauses above;
* the inclusion of `adm(c₀, c₁)` in the condition [II, (3.15)] at the order
  `n* = ⌈(4/d)(1/c₁ − 1 + c₀/2)⌉ + 1`.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators
open MeasureTheory Filter Complex

namespace RBM8D.Graphs

/-! ## The clauses read at `𝔟₁ = 𝔟₂` -/

/-- The diagonal scaling order `n_𝔟 = ord − 2·[⊕, ⊖ in one dotted block]`: the scaling order of the
graph with `⊕ = ⊖ = 𝔟`, when the dotted edges form a forest and no dotted edge is at `⊗`. -/
def Graph.diagOrd {n : ℕ} (Γ : Graph 3 n) : ℤ := Γ.ord - if Γ.pmBlockB then 2 else 0

/-- The clauses of [II, Def 6.3] that [II, (8.18)–(8.24)] read at `𝔟₁ = 𝔟₂`: every graph of `R`,
`A`, `Q`, `Err` has only diffusive components at `⊗` and dotted edges forming a forest, every
graph of `R` and `A` with `⊕`, `⊖` in one dotted block has scaling order at least `5`, and every
graph of `A`, `Q` and `Err` with an internal atom that is not a `⊕`-recollision graph at
`𝔟₁ = 𝔟₂` is rooted at the external atoms (`Graph.RootedAtExt`). -/
def TRec.Def63G11 (𝒯 : TRec) : Prop :=
  (∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, g.2.TensorDiffusive ∧ g.2.DotsAcyclic) ∧
    (∀ g ∈ 𝒯.R ++ 𝒯.A, g.2.PMBlock → 5 ≤ g.2.ord) ∧
    ∀ g ∈ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt

/-! ## Removing the `P`/`Q` labels: paths through the label atom -/

/-- The dotted block of the atom `v` contains an external atom (in particular, `v` may be
external): a label at `v` then reads a row of `H` at an external index. -/
def Graph.labelFixedB {n : ℕ} (Γ : Graph 3 n) (v : Atom 3 n) : Bool :=
  (dotBlocks (allAtoms 3 n) Γ.comps).any fun B => B.contains v && B.any fun w => w.isLeft

/-- The component `c` can be replaced by a path through its label atom: it is a labelled solid
edge or weight whose label atom `v` is internal, with a dotted block free of external atoms, and
whose ends differ from `v`. -/
def Graph.pathEligB {n : ℕ} (Γ : Graph 3 n) (c : Comp (Atom 3 n)) : Bool :=
  match c.label with
  | some (_, v) => c.kind.isRandom && !Γ.labelFixedB v && c.x != v && c.y != v
  | none => false

/-- The components replaced by a path through their label atom (`Graph.pathEligB`). -/
def Graph.pathElig {n : ℕ} (Γ : Graph 3 n) : Finset (Fin Γ.comps.length) :=
  Finset.univ.filter fun i => Γ.pathEligB Γ.comps[i] = true

/-- The path `x–v–y` replacing a component `c` from `x` to `y` (for a weight, `x = y`): the solid
edges `x–v`, `v–y` with the charge of `c`, and the `×`-dotted edges `x ≠ v`, `v ≠ y`. These are
the factors `G_{xv} G_{vy}` of the Schur complement identity
`G^{[v]}_{xy} = G_{xy} − G_{xv} G_{vy} / G_{vv} + G^{[v]}_{xv} G^{[v]}_{vy} / G^{[v]}_{vv}` for the
matrix `G^{[v]}` with row and column `v` resampled. -/
def Comp.pathVia {V : Type*} (c : Comp V) (v : V) : List (Comp V) :=
  let ch : Charge :=
    match c.kind with
    | .G ch | .weight ch | .light ch | .inv ch | .wD ch _ => ch
    | _ => .plus
  [⟨.G ch, c.x, v, [], none⟩, ⟨.G ch, v, c.y, [], none⟩, ⟨.xdot, c.x, v, [], none⟩,
    ⟨.xdot, v, c.y, [], none⟩]

/-- The label-free graph `Γ_S` of the label removal: every component with index in `S` is replaced
by the path through its label atom (`Comp.pathVia`), the `P`/`Q` labels of the other components
are erased, and a `×`-dotted edge between two distinct atoms that carry no solid edge after
the replacement is removed. -/
def Graph.pathRepl {n : ℕ} (Γ : Graph 3 n) (S : Finset (Fin Γ.comps.length)) : Graph 3 n :=
  let cs : List (Comp (Atom 3 n)) := (List.finRange Γ.comps.length).flatMap fun i =>
    match Γ.comps[i].label with
    | some (_, v) => if i ∈ S then Γ.comps[i].pathVia v else [{ Γ.comps[i] with label := none }]
    | none => [Γ.comps[i]]
  ⟨cs.filter fun c => !(c.kind == .xdot && c.x != c.y &&
      !cs.any fun c' => c'.kind.isSolid &&
        ((c'.x == c.x && c'.y == c.y) || (c'.x == c.y && c'.y == c.x))), Γ.coeff⟩

instance G11_decAtExternals {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.AtExternals := by
  unfold Graph.AtExternals; infer_instance

instance G11_decTKinds {k n : ℕ} (N : ℕ) (Γ : Graph k n) : Decidable (Γ.TKinds N) :=
  inferInstanceAs (Decidable (_ = true))

instance G11_decLabelFree {k n : ℕ} (Γ : Graph k n) : Decidable Γ.LabelFree :=
  inferInstanceAs (Decidable (∀ c ∈ Γ.comps, c.label = none))

end RBM8D.Graphs

namespace RBM8D

open Graphs

/-! ## Graph bounds ([I, (6.40)], [II, Claim 8.6]) -/

/-- [I, (6.40)], the form of [I, Lemma 6.10] used in [II, (8.21), (8.33)], as stochastic
domination along `W → ∞` inside `adm(c₀, c₁)` at scale `W`: for random matrices `G(u)` and
spectral parameters `z(u) ∈ 𝐃(κ, ε)` indexed by `u`, and `0 ≤ ε₀ < d/2`,
`‖G - m‖_{w;(1,2)} ≺ W^{ε₀}` uniformly in `u` implies
`‖W^{(n_{xy}-3)d/2} |𝒢^{abs}_{xy}| / B_{xy}‖_{w;(1,2)} ≺ W^{(n_{xy}-2)ε₀}` uniformly in `u`. -/
def dcWeakDomStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (n C : ℕ) (Γ : Graph 2 n), Γ.internalize.Normal C → Γ.internalize.DoublyConnected →
      Γ.TKinds N → ∀ ε₀ : ℝ, 0 ≤ ε₀ → ε₀ < (d : ℝ) / 2 →
      ∀ (Ω : SizeL → Type) [∀ p, MeasurableSpace (Ω p)] (Pr : ∀ p, Measure (Ω p))
        (U : SizeL → Type) (z : ∀ p, U p → ℂ)
        (G : ∀ p, U p → Ω p → Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ),
        (∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) →
        StochDom (admFilterL c₀ c₁) sizeW Pr
            (fun p u ω => weakNorm d p.1.2 p.1.1 1 2 (errAbs (G p u ω) (z p u)))
            (fun p _ _ => sizeW p ^ ε₀) →
          StochDom (admFilterL c₀ c₁) sizeW Pr
            (fun p u ω => weakNorm d p.1.2 p.1.1 1 2
              (normGraph2 d p.1.2 p.1.1 Γ (gData (Smat P.ψ p.1.1 p.1.2) (z p u) Sig (G p u ω))))
            (fun p _ _ => sizeW p ^ (((Γ.ord : ℝ) - 2) * ε₀))

/-- [II, Claim 8.6] with the diagonal scaling order, per graph: the rows of [II, Claim 8.6] for one
graph `g` with external atoms `⊗, ⊕, ⊖`, under hypotheses on `g` alone. For `d ≥ 8`,
`0 ≤ ε₀ < d/2`, self-energies `Sig` of orders `4, …, N`, and a normal regular graph `g` with the
kinds of [II, Def 3.2] (labels of entries in `[4, N]`), condition [II, Def 3.2 (9)], doubly
connected, with only diffusive components at `⊗` and dotted edges forming a forest: for every
`τ > 0` there are `τ' > 0` and `W₀` such that for `W ≥ W₀` along `adm(c₀, c₁)`, `z ∈ 𝐃(κ, ε)`,
`Φ̃ ≥ 0` and every single matrix `G` with `‖G − m‖_{w;(1,2)} ≤ W^{ε₀+τ'}` and
`|G_{xy} − δ_{xy} m| ≤ W^{τ'} (B_{xy}^{1/2} + Φ̃)`:
* if `g` is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` with `n_𝔟 ≥ 2`, the bound [II, (8.21)]
  `|𝒢^{abs}_{𝔞,𝔟𝔟}| ≤ W^τ W^{(n_𝔟−2)(−d/2+ε₀)} B_{𝔞𝔟}`;
* if `g` has no internal atom, `|𝒢^{abs}_{𝔞,𝔟𝔟}| ≤ W^τ B_{𝔞𝔟}`;
* otherwise, if `g` is rooted at the external atoms (`Graph.RootedAtExt`),
  `|𝒢^{abs}_{𝔞,𝔟𝔟}| ≤ W^τ W^{(n_𝔟−2)(−d/2+ε₀)} (L²/W²) (B_{𝔞𝔟} + Φ̃²)`
  ([II, (8.23)–(8.24)]). -/
def graphSumStmt'' : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (nI C : ℕ) (g : Graph 3 nI), g.Normal C → g.TKinds N → g.AtExternals →
      g.DoublyConnected → g.TensorDiffusive → g.DotsAcyclic →
      ∀ ε₀ : ℝ, 0 ≤ ε₀ → ε₀ < (d : ℝ) / 2 →
      ∀ τ : ℝ, 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
        (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
          ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) (Φ : ℝ), 0 ≤ Φ →
            weakNorm d L W 1 2 (errAbs G z) ≤ (W : ℝ) ^ (ε₀ + τ') →
            (∀ x y, ‖entryErr G (msc z) x y‖ ≤
              (W : ℝ) ^ τ' * (Real.sqrt (bB d L W x y) + Φ)) →
            (g.DiagRecoll → 2 ≤ g.diagOrd → ∀ a b : Zd d L,
              g.absVal (gData (Smat P.ψ W L) z Sig G) ![a, b, b] ≤
                (W : ℝ) ^ τ * (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) *
                  bB d L W a b) ∧
            (nI = 0 → ∀ a b : Zd d L,
              g.absVal (gData (Smat P.ψ W L) z Sig G) ![a, b, b] ≤ (W : ℝ) ^ τ * bB d L W a b) ∧
            (nI ≠ 0 → ¬ g.DiagRecoll → g.RootedAtExt → ∀ a b : Zd d L,
              g.absVal (gData (Smat P.ψ W L) z Sig G) ![a, b, b] ≤
                (W : ℝ) ^ τ * (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) *
                  ((L : ℝ) ^ 2 / (W : ℝ) ^ 2) * (bB d L W a b + Φ ^ 2))

/-! ## The filter, the averaged matrix and the random data record -/

/-- The sizes with [II, (3.15)]: `L²/W² ≤ W^{(n−1)d/2 − c₀}`. -/
def thrSet (d n : ℕ) (c₀T : ℝ) : Set SizeL :=
  {p | (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ≤ (p.1.1 : ℝ) ^ (((n : ℝ) - 1) * d / 2 - c₀T)}

/-- `W → ∞` inside `adm(c₀, c₁)` with [II, (3.15)] at order `n`: the filter of
[II, Theorem 3.6]. -/
def llFilter (d n : ℕ) (c₀ c₁ c₀T : ℝ) : Filter SizeL :=
  admFilterL c₀ c₁ ⊓ 𝓟 (thrSet d n c₀T)

/-- The box average `K^{−d} Σ_{|y − x₀| ≤ K} (|G_{xy}|² + |G_{yx}|²)` of [II, (7.6), (7.8)]. -/
def boxAvg (d L : ℕ) [NeZero L] (G : Matrix (Zd d L) (Zd d L) ℂ) (x x₀ : Zd d L) (K : ℕ) : ℝ :=
  (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (‖G x y‖ ^ 2 + ‖G y x‖ ^ 2)) /
    (K : ℝ) ^ d

/-- The data record of the model at the sample `ω` and the spectral parameter `z`, with the
self-energy matrices `Σ_l` of `Sig` read by the labelled `Θ` edges. -/
def rbmData (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (z : ℂ)
    (ω : Sample (Zd d L)) : Data (Zd d L) :=
  { modelData (Smat P.ψ W L) z hmat ω with Sig := sigMat Sig (Smat P.ψ W L) z }

/-! ## The steps [II, Lemmas 7.2, 7.3, 7.4, 8.1] and [II, Claim 8.7] -/

/-- **[II, Lemma 7.2]**: for `d ≥ 8`, a profile `P`, `c₀, c₁ > 0` with `c₀ + c₁ < 1` and
`κ > 0`, `|G_{xy}(E + i) − m(E + i) δ_{xy}|² ≺ B_{xy}` uniformly in `|E| < 2 − κ` and `x, y`,
along `W → ∞` inside `adm(c₀, c₁)` (its proof reads the second order `T`-expansion only, so no
condition on `L` enters). -/
def eta1StepStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 → 0 < κ →
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
      (U := fun p => {E : ℝ // |E| < 2 - κ} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) ((v.1.1 : ℂ) + I)) (msc ((v.1.1 : ℂ) + I))
        v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2)

/-- **[II, Lemma 7.3] = [I, Lemma 5.3]**: under the hypotheses of [II, Theorem 3.6] and
[II, (7.5)] at spectral parameters `z̃(u) = E(u) + iη̃(u) ∈ 𝐃(κ, ε)`:
* [II, (7.6)]: `K^{−d} Σ_{|y−x₀| ≤ K} (|G_{xy}(z)|² + |G_{yx}(z)|²) ≺ (η̃/η)² W^{−4} K^{4−d}`
  uniformly in `u`, `x, x₀`, integers `K ∈ [W, L/2]` and `z = E(u) + iη` with
  `W²/L^{2−ε} ≤ η ≤ η̃(u)`;
* [II, (7.7)]: for every `ε₀ ∈ (0, d/20)`, `‖G(z) − m(z)‖_max ≺ W^{−d/2+ε₀}` uniformly in `u`,
  `x, y` and `z = E(u) + iη` with `max(W^{−ε₀} η̃(u), W²/L^{2−ε}) ≤ η ≤ η̃(u)`. -/
def continuityStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → 0 < c₀T →
    ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), n + 2 ≤ D →
      IsTExpansion d (smatVar P) Sig n D 𝒯 → 𝒯.Def63G11 →
      ∀ (U : SizeL → Type) (zt : ∀ p, U p → ℂ), (∀ p u, zt p u ∈ specDom κ ε p.1.1 p.1.2) →
      StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
        (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
        (fun p v ω => ‖entryErr (green (hmat ω) (zt p v.1)) (msc (zt p v.1)) v.2.1 v.2.2‖ ^ 2)
        (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) →
      StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
          (U := fun p => {v : U p × ℝ × Zd d p.1.2 × Zd d p.1.2 × ℕ //
            (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) ≤ v.2.1 ∧ v.2.1 ≤ (zt p v.1).im ∧
              p.1.1 ≤ v.2.2.2.2 ∧ 2 * v.2.2.2.2 ≤ p.1.2})
          (fun p v ω => boxAvg d p.1.2
            (green (hmat ω) (((zt p v.1.1).re : ℂ) + (v.1.2.1 : ℂ) * I))
            v.1.2.2.1 v.1.2.2.2.1 v.1.2.2.2.2)
          (fun p v _ => ((zt p v.1.1).im / v.1.2.1) ^ 2 * (p.1.1 : ℝ) ^ (-4 : ℝ) *
            (v.1.2.2.2.2 : ℝ) ^ (4 - (d : ℝ))) ∧
        ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < (d : ℝ) / 20 →
          StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
            (U := fun p => {v : U p × ℝ × Zd d p.1.2 × Zd d p.1.2 //
              max ((p.1.1 : ℝ) ^ (-ε₀) * (zt p v.1).im) ((p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε)) ≤
                v.2.1 ∧ v.2.1 ≤ (zt p v.1).im})
            (fun p v ω => ‖entryErr (green (hmat ω) (((zt p v.1.1).re : ℂ) + (v.1.2.1 : ℂ) * I))
              (msc (((zt p v.1.1).re : ℂ) + (v.1.2.1 : ℂ) * I)) v.1.2.2.1 v.1.2.2.2‖)
            (fun p _ _ => (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + ε₀))

/-! ## Graphs with `P`/`Q` labels ([II, Claims 8.6, 8.7]) -/

/-- The structure of the label-free graphs `Γ_S` (`Graph.pathRepl`): for a normal regular graph
`Γ` with the kinds of [II, Def 3.2], condition [II, Def 3.2 (9)], doubly connected, with only
diffusive components at `⊗` and dotted edges forming a forest, rooted at the external atoms
(`Graph.RootedAtExt`) when it has an internal atom and is not a `⊕`-recollision graph at
`𝔟₁ = 𝔟₂`, and every set `S` of components replaceable by a path through their (internal) label
atom, the graph `Γ_S` has the same properties, has no `P`/`Q` label, has the same dotted blocks (so
`⊕`, `⊖` lie in one dotted block, and `Γ_S` is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`, exactly when
this holds for `Γ`), and its scaling order and diagonal scaling order exceed those of `Γ` by at
least `|S|`. -/
def labelPathsStmt : Prop :=
  ∀ (nI C N : ℕ) (Γ : Graph 3 nI), Γ.Normal C → Γ.TKinds N → Γ.AtExternals →
    Γ.DoublyConnected → Γ.TensorDiffusive → Γ.DotsAcyclic →
    (nI ≠ 0 → ¬ Γ.DiagRecoll → Γ.RootedAtExt) →
    ∀ S ⊆ Γ.pathElig,
      (∃ C', (Γ.pathRepl S).Normal C') ∧ (Γ.pathRepl S).TKinds N ∧
      (Γ.pathRepl S).AtExternals ∧ (Γ.pathRepl S).DoublyConnected ∧
      (Γ.pathRepl S).TensorDiffusive ∧ (Γ.pathRepl S).DotsAcyclic ∧
      (Γ.pathRepl S).LabelFree ∧ (Γ.pathRepl S).pmBlockB = Γ.pmBlockB ∧
      ((Γ.pathRepl S).DiagRecoll ↔ Γ.DiagRecoll) ∧
      (nI ≠ 0 → ¬ (Γ.pathRepl S).DiagRecoll → (Γ.pathRepl S).RootedAtExt) ∧
      Γ.ord + (S.card : ℤ) ≤ (Γ.pathRepl S).ord ∧
      Γ.diagOrd + (S.card : ℤ) ≤ (Γ.pathRepl S).diagOrd

/-! ## The call relation of the proof -/

/-- [II, Lemma 7.2] from [I, (6.40)] (the bound [II, (8.21)] on the graphs of the second order
`T`-expansion with a dotted edge at `𝔟`). -/
def eta1Step_ofStmt : Prop := dcWeakDomStmt → eta1StepStmt

end RBM8D

namespace RBM8D.Graphs

/-! ## The second order `T`-expansion -/

/-- A graph whose internal atoms lie in one molecule is doubly connected, with empty nets. -/
private theorem G11_dc_of_spans {k n : ℕ} (Γ : Graph k n) (h : Γ.Spans ∅) :
    Γ.DoublyConnected :=
  ⟨∅, ∅, Finset.disjoint_empty_left _, by simp, by simp, h, h⟩

/-- The graph properties of [II, Def 3.2] for the second order `T`-expansion at order `2`, with
labels in `[4, 2]`, for every error order `D`. -/
private theorem G11_h2Rec_shape (D : ℕ) : h2Rec.Shape 2 2 D := by
  have h1 : ∀ g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q ++ h2Rec.Err,
      g.2.Normal 12 ∧ g.2.TKinds 2 ∧ g.2.AtExternals ∧ g.2.Spans ∅ := by
    decide
  have hA : ∀ g ∈ h2Rec.A, g.2.LabelFree ∧ ((2 : ℕ) : ℤ) < g.2.ord := by decide
  have hQ : ∀ g ∈ h2Rec.Q, g.2.IsQGraph ∧ 2 ≤ g.2.ord := by decide
  refine ⟨⟨fun g hg => ?_, fun g hg => by simp [h2Rec] at hg⟩, fun g hg => by simp [h2Rec] at hg,
    hA, hQ, fun g hg => by simp [h2Rec] at hg⟩
  obtain ⟨hn, hk, he, hs⟩ := h1 g (List.mem_append_left _ hg)
  exact ⟨⟨12, hn⟩, hk, he, G11_dc_of_spans _ hs⟩

private theorem G11_valR_append {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (E F : Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω) :
    (E ++ F).valR PF D e ω = E.valR PF D e ω + F.valR PF D e ω := by
  simp [Expansion.valR, List.map_append, List.sum_append]

private theorem G11_valR_nil {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω) :
    Expansion.valR ([] : Expansion k) PF D e ω = 0 := rfl

private theorem G11_valR_flatMap_oDot {Ω ι : Type} [Fintype ι]
    [DecidableEq ι] (E : Expansion 3) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin 3 → ι)
    (ω : Ω) :
    Expansion.valR (E.flatMap fun g => oDot g.2) PF D e ω = E.valR PF D e ω := by
  induction E with
  | nil => rfl
  | cons g E ih =>
    rw [List.flatMap_cons, G11_valR_append, ih]
    have h1 := congrFun (oDot_value 3 g.1 Ω ι PF D trivial g.2 e) ω
    rw [h1]
    simp [Expansion.valR]

/-- The identity [II, (3.1)] at order `2` for the second order `T`-expansion, from
[I, Lemma 2.5] and the value identity of `O_dot`. -/
private theorem G11_h2Rec_identity (Sig : ℕ → Expansion 2) : h2Rec.Identity Sig 2 := by
  intro Ω ι _ _ PF D hA _ e ω
  have hsplit : secondOrderExp =
      leadExp ++ (secondOrderExp.drop 1).take 2 ++ secondOrderExp.drop 3 := rfl
  have hS : sigmaTExp 2 = [] := by decide
  rw [← congrFun (secondOrderT Ω ι PF D hA e) ω, hsplit]
  simp only [TRec.rhs, hS, h2Rec, G11_valR_append, G11_valR_nil, G11_valR_flatMap_oDot]
  ring

/-- The second order `T`-expansion is an `n = 2`-th order `T`-expansion with every error order
`D > 2` ([II, Def 3.2], [II, Def 6.3]), for every variance family and every family `Sig`. -/
theorem G11.h2Rec_isTExpansion (d : ℕ) (Svar : VarFamily d) (Sig : ℕ → Expansion 2) (D : ℕ)
    (hD : 2 < D) : IsTExpansion d Svar Sig 2 D h2Rec :=
  ⟨fun _ hk hk' => absurd (hk.trans hk') (by norm_num),
    hD, G11_h2Rec_identity Sig, fun j hj hj' => absurd (hj.trans hj') (by norm_num),
    G11_h2Rec_shape D, h2Rec_def63⟩

set_option maxRecDepth 100000 in
/-- The second order `T`-expansion satisfies the clauses `TRec.Def63G11`: `⊗` carries only the
`Θ` edge, the dotted edges of every graph form a forest, the two graphs of `A` with `⊕`, `⊖` in
one dotted block have scaling order `5`, and the graphs of `A` and `Q` with an internal atom that
are not `⊕`-recollision graphs at `𝔟₁ = 𝔟₂` are rooted at the external atoms. -/
theorem G11.h2Rec_def63G11 : h2Rec.Def63G11 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end RBM8D.Graphs

namespace RBM8D

open Graphs

/-! ## The filter of [II, Theorem 3.6] at the instance -/

/-- `(W, W²) ∈ adm(1/4, 1/2)` for `W ≥ 1`: `(W²)^{1/2} = W` and `W ≤ (W²)^{3/4}`. -/
private theorem G11_adm_sq (W : ℕ) (hW : 1 ≤ W) : (W, W ^ 2) ∈ adm (1 / 4) (1 / 2) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hsq : ((W ^ 2 : ℕ) : ℝ) = (W : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; push_cast; ring
  refine ⟨?_, ?_⟩
  · change ((W ^ 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ (W : ℝ)
    rw [hsq, ← Real.rpow_mul hW0]
    norm_num
  · change (W : ℝ) ≤ ((W ^ 2 : ℕ) : ℝ) ^ (1 - 1 / 4 : ℝ)
    rw [hsq, ← Real.rpow_mul hW0]
    calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (W : ℝ) ^ (2 * (1 - 1 / 4) : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)

/-- `(W, W²)` satisfies [II, (3.15)] at `d = 8`, `n = 2`, `c₀ᵀ = 2`, with equality:
`L²/W² = W² = W^{(2−1)·8/2 − 2}`. -/
private theorem G11_thr_sq (W : ℕ) (hW : 1 ≤ W) :
    ((W ^ 2 : ℕ) : ℝ) ^ 2 / (W : ℝ) ^ 2 ≤ (W : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) * ((8 : ℕ) : ℝ) / 2 - 2) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h : (((2 : ℕ) : ℝ) - 1) * ((8 : ℕ) : ℝ) / 2 - 2 = (2 : ℕ) := by norm_num
  rw [h, Real.rpow_natCast]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  ring_nf
  exact le_rfl

/-- The sizes `(W, W²)`, `W ≥ 1`. -/
private def G11_sqSize (W : ℕ) : SizeL := ⟨(W + 1, (W + 1) ^ 2), by positivity⟩

/-- The filter of [II, Theorem 3.6] at `d = 8`, `n = 2`, `c₀ = 1/4`, `c₁ = 1/2`, `c₀ᵀ = 2` is
proper: the sizes `(W, W²)` tend to it. -/
theorem G11.llFilter_neBot : (llFilter 8 2 (1 / 4) (1 / 2) 2).NeBot := by
  have ht : Tendsto G11_sqSize atTop (llFilter 8 2 (1 / 4) (1 / 2) 2) := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (Eventually.of_forall fun W => ?_)⟩
    · refine tendsto_comap_iff.2 (tendsto_inf.2 ⟨tendsto_principal.2
        (Eventually.of_forall fun W => G11_adm_sq (W + 1) (by omega)), ?_⟩)
      refine tendsto_comap_iff.2 ?_
      exact tendsto_add_atTop_nat 1
    · exact G11_thr_sq (W + 1) (by omega)
  exact ht.neBot

/-- The size `(16, 256)` lies in `adm(1/4, 1/2)` (`256^{1/2} = 16 ≤ 16 ≤ 64 = 256^{3/4}`) and
satisfies [II, (3.15)] at `d = 8`, `n = 2`, `c₀ᵀ = 2` with equality (`256 = 16²`). -/
theorem G11.point_16_256 : ((16, 256) : ℕ × ℕ) ∈ adm (1 / 4) (1 / 2) ∧
    ((256 : ℕ) : ℝ) ^ 2 / ((16 : ℕ) : ℝ) ^ 2 ≤
      ((16 : ℕ) : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) * ((8 : ℕ) : ℝ) / 2 - 2) :=
  ⟨G11_adm_sq 16 (by norm_num), G11_thr_sq 16 (by norm_num)⟩

/-- `z = i/2 ∈ 𝐃(1/2, 1/2)` at `(W, L) = (16, 256)`: `16²/256^{3/2} = 1/16 ≤ 1/2 ≤ 1`. -/
theorem G11.specDom_16_256 : (I / 2 : ℂ) ∈ specDom (1 / 2) (1 / 2) 16 256 := by
  refine ⟨by simp; norm_num, ?_, by simp; norm_num⟩
  have h : ((256 : ℕ) : ℝ) ^ (2 - 1 / 2 : ℝ) = 4096 := by
    rw [show ((256 : ℕ) : ℝ) = (16 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  simp only [Nat.cast_ofNat] at h ⊢
  rw [h]
  simp
  norm_num

end RBM8D

namespace RBM8D

section Witness

open scoped FourierTransform SchwartzMap Nat ContDiff

private theorem gauss_poly_bound (m : ℕ) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ m * Real.exp (-(r ^ 2) / 2) ≤ C := by
  refine ⟨2 ^ m * (1 + 2 ^ m * m !), fun r hr => ?_⟩
  have h1 : (1 + r) ^ m ≤ 2 ^ m * (1 + r ^ (2 * m)) := by
    rcases le_total r 1 with h | h
    · calc (1 + r) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
        _ ≤ 2 ^ m * (1 + r ^ (2 * m)) := by
          have : 0 ≤ r ^ (2 * m) := by positivity
          nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m]
    · calc (1 + r) ^ m ≤ (2 * r ^ 2) ^ m := pow_le_pow_left₀ (by linarith) (by nlinarith) m
        _ = 2 ^ m * r ^ (2 * m) := by rw [mul_pow, pow_mul]
        _ ≤ 2 ^ m * (1 + r ^ (2 * m)) := by
          have : (0 : ℝ) ≤ 2 ^ m := by positivity
          nlinarith
  have h2 : r ^ (2 * m) ≤ 2 ^ m * m ! * Real.exp (r ^ 2 / 2) := by
    have h := Real.pow_div_factorial_le_exp (x := r ^ 2 / 2) (by positivity) m
    have hf : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hf] at h
    calc r ^ (2 * m) = 2 ^ m * (r ^ 2 / 2) ^ m := by
          rw [div_pow, pow_mul]; field_simp
      _ ≤ 2 ^ m * (Real.exp (r ^ 2 / 2) * m !) := by gcongr
      _ = _ := by ring
  have he : Real.exp (-(r ^ 2) / 2) * Real.exp (r ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have he0 : 0 < Real.exp (-(r ^ 2) / 2) := Real.exp_pos _
  have he1 : Real.exp (-(r ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc (1 + r) ^ m * Real.exp (-(r ^ 2) / 2)
      ≤ 2 ^ m * (1 + 2 ^ m * m ! * Real.exp (r ^ 2 / 2)) * Real.exp (-(r ^ 2) / 2) := by
        refine mul_le_mul_of_nonneg_right (h1.trans ?_) he0.le
        have : (0 : ℝ) ≤ 2 ^ m := by positivity
        nlinarith
    _ = 2 ^ m * (Real.exp (-(r ^ 2) / 2) + 2 ^ m * m ! *
          (Real.exp (-(r ^ 2) / 2) * Real.exp (r ^ 2 / 2))) := by ring
    _ ≤ 2 ^ m * (1 + 2 ^ m * m !) := by
        rw [he, mul_one]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The Gaussian `x ↦ e^{−‖x‖²/2}` as a Schwartz function. -/
private def gaussS (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : 𝓢(H, ℝ) where
  toFun x := Real.exp (-(‖x‖ ^ 2) / 2)
  smooth' := by
    have : ContDiff ℝ ∞ (fun x : H => -(‖x‖ ^ 2) / 2) := ((contDiff_norm_sq ℝ).neg).div_const _
    exact Real.contDiff_exp.comp this
  decay' k n := by
    obtain ⟨K, M, hM, hb⟩ :=
      (Function.hasTemperateGrowth_norm_sq H).norm_iteratedFDeriv_le_uniform n
    obtain ⟨C, hC⟩ := gauss_poly_bound (k + K * n)
    refine ⟨n ! * (max M 1) ^ n * C, fun x => ?_⟩
    have hcomp : (fun x : H => Real.exp (-(‖x‖ ^ 2) / 2)) =
        (fun s : ℝ => Real.exp ((-1 / 2) * s)) ∘ (fun x : H => ‖x‖ ^ 2) := by
      ext x; simp only [Function.comp_apply]; ring_nf
    set A : ℝ := max M 1 * (1 + ‖x‖) ^ K with hA
    have hA1 : 1 ≤ A := one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (one_le_pow₀ (by linarith [norm_nonneg x]))
    have h := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (N := ∞) (n := n)
      (g := fun s : ℝ => Real.exp ((-1 / 2) * s)) (f := fun x : H => ‖x‖ ^ 2)
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)) (contDiff_norm_sq ℝ)
      (WithTop.coe_le_coe.mpr le_top) x (C := Real.exp (-(‖x‖ ^ 2) / 2)) (D := A) ?_ ?_
    · rw [← hcomp] at h
      have hx : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
      have hC' := hC ‖x‖ (norm_nonneg x)
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : H => Real.exp (-(‖x‖ ^ 2) / 2)) x‖
          ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(‖x‖ ^ 2) / 2) * A ^ n) := by gcongr
        _ = n ! * (max M 1) ^ n * ((1 + ‖x‖) ^ (k + K * n) * Real.exp (-(‖x‖ ^ 2) / 2)) := by
          rw [hA, mul_pow, ← pow_mul, pow_add]; ring
        _ ≤ n ! * (max M 1) ^ n * C := by gcongr
    · intro i _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul, norm_mul,
        norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le]
      have : ‖(-1 / 2 : ℝ)‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) (by norm_num)
      calc ‖(-1 / 2 : ℝ)‖ ^ i * Real.exp (-1 / 2 * ‖x‖ ^ 2)
          ≤ 1 * Real.exp (-1 / 2 * ‖x‖ ^ 2) := by gcongr
        _ = Real.exp (-(‖x‖ ^ 2) / 2) := by ring_nf
    · intro i hi1 hin
      calc ‖iteratedFDeriv ℝ i (fun x : H => ‖x‖ ^ 2) x‖ ≤ M * (1 + ‖x‖) ^ K := hb i hin x
        _ ≤ A := by rw [hA]; gcongr; exact le_max_left _ _
        _ ≤ A ^ i := le_self_pow₀ hA1 (by omega)

/-- `ψ(p) = e^{−|p|²/2}` on `ℝ^8`. -/
private def psiG : 𝓢(EuclideanSpace ℝ (Fin 8), ℝ) := gaussS _

private theorem psiG_apply (p : EuclideanSpace ℝ (Fin 8)) :
    psiG p = Real.exp (-(‖p‖ ^ 2) / 2) := rfl

/-- `(2π)^{−8} ∫ e^{−W²|p|²/2} e^{i p·y} dp = (2π)^{−8} (2π/W²)^4 e^{−|y|²/(2W²)}`. -/
private theorem profInt_psiG (W : ℝ) (hW : 0 < W) (y : EuclideanSpace ℝ (Fin 8)) :
    profInt psiG W y = ((((2 * Real.pi) ^ 8)⁻¹ * (2 * Real.pi / W ^ 2) ^ 4 *
      Real.exp (-(‖y‖ ^ 2) / (2 * W ^ 2)) : ℝ) : ℂ) := by
  have hint : ∀ p : EuclideanSpace ℝ (Fin 8),
      (psiG (W • p) : ℂ) * cexp (I * (inner ℝ p y : ℝ)) =
        cexp (-((W ^ 2 / 2 : ℝ) : ℂ) * (‖p‖ : ℂ) ^ 2 + I * (inner ℝ y p : ℝ)) := by
    intro p
    rw [psiG_apply, Complex.ofReal_exp, ← Complex.exp_add, norm_smul, real_inner_comm,
      Real.norm_of_nonneg hW.le]
    congr 1
    push_cast
    ring
  have hb : 0 < (((W ^ 2 / 2 : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  simp_rw [profInt, hint]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb I y, finrank_euclideanSpace_fin]
  have h4 : ((8 : ℕ) : ℂ) / 2 = ((4 : ℕ) : ℂ) := by norm_num
  rw [h4, Complex.cpow_natCast, I_sq]
  have hW2 : (W : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hW 2).ne'
  push_cast
  rw [mul_assoc]
  congr 2
  · congr 1
    field_simp
  · congr 1
    field_simp
    ring

private theorem profInt_psiG_re_nonneg (W : ℝ) (hW : 0 < W) (y : EuclideanSpace ℝ (Fin 8)) :
    0 ≤ (profInt psiG W y).re := by
  rw [profInt_psiG W hW y, Complex.ofReal_re]
  positivity

private theorem norm_zrep_neg {L : ℕ} [NeZero L] (x : Zd 8 L) : ‖zrep (-x)‖ = ‖zrep x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := ZMod.natAbs_valMinAbs_neg (x i)
  have h' : |((-x i).valMinAbs : ℝ)| = |((x i).valMinAbs : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
  have h2 : ((-x i).valMinAbs : ℝ) ^ 2 = ((x i).valMinAbs : ℝ) ^ 2 := by
    rw [← sq_abs, h', sq_abs]
  simpa [zrep] using h2

private theorem fRaw_psiG_nonneg (W L : ℕ) (hW : 1 ≤ W) (x : Zd 8 L) : 0 ≤ fRaw psiG W L x :=
  profInt_psiG_re_nonneg W (by exact_mod_cast hW) _

private theorem fRaw_psiG_neg (W L : ℕ) [NeZero L] (hW : 1 ≤ W) (x : Zd 8 L) :
    fRaw psiG W L (-x) = fRaw psiG W L x := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  simp only [fRaw, profInt_psiG (W : ℝ) hW', norm_zrep_neg]

private theorem fWL_psiG_neg (W L : ℕ) [NeZero L] (hW : 1 ≤ W) (x : Zd 8 L) :
    fWL psiG W L (-x) = fWL psiG W L x := by
  simp only [fWL, fRaw_psiG_neg W L hW]

private theorem fRaw_psiG_zero_pos (W L : ℕ) [NeZero L] (hW : 1 ≤ W) :
    0 < fRaw psiG W L 0 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [fRaw, profInt_psiG (W : ℝ) hW', Complex.ofReal_re]
  positivity

private theorem ZWL_psiG_pos (W L : ℕ) [NeZero L] (hW : 1 ≤ W) : 0 < ZWL psiG W L :=
  lt_of_lt_of_le (fRaw_psiG_zero_pos W L hW)
    (Finset.single_le_sum (fun x _ => fRaw_psiG_nonneg W L hW x) (Finset.mem_univ _))

/-- `e^{−t/2} ≤ max(1 − 3t/8, 5/8)` for `t ≥ 0`. -/
private theorem exp_neg_half_le (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t / 2) ≤ max (1 - 3 / 8 * t) (1 - 3 / 8) := by
  have hq := Real.quadratic_le_exp_of_nonneg (x := t / 2) (by positivity)
  have hprod : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hpos : 0 < Real.exp (t / 2) := Real.exp_pos _
  have hpos' : 0 < Real.exp (-t / 2) := Real.exp_pos _
  rcases le_total t 1 with h | h
  · refine le_max_of_le_left ?_
    -- `(1 + s + s²/2)(1 − 3s/4) ≥ 1` for `0 ≤ s ≤ 1/2`, `s = t/2`
    have key : 1 ≤ Real.exp (t / 2) * (1 - 3 / 8 * t) := by
      have h38 : 0 ≤ 1 - 3 / 8 * t := by linarith
      calc (1 : ℝ) ≤ (1 + t / 2 + (t / 2) ^ 2 / 2) * (1 - 3 / 8 * t) := by nlinarith
        _ ≤ Real.exp (t / 2) * (1 - 3 / 8 * t) := by gcongr
    nlinarith
  · refine le_max_of_le_right ?_
    have hq1 := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
    have hmono : Real.exp (-t / 2) ≤ Real.exp (-1 / 2) := Real.exp_le_exp.mpr (by linarith)
    have hprod1 : Real.exp (-1 / 2) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    have : Real.exp (-1 / 2) ≤ 5 / 8 := by
      have hp : 0 < Real.exp (-1 / 2) := Real.exp_pos _
      nlinarith
    linarith

/-- The Gaussian `ψ(p) = e^{−|p|²/2}` satisfies [I, Assumption 1.2] with `c_ψ = 3/8`, and
`f_{W,L}(x) = Z_{W,L}^{−1}(2π)^{−8}(2π/W²)^4 e^{−|[x]_L|²/(2W²)}` is positive, and symmetric
for every `W ≥ 1`, `L ≥ 1`. -/
private def gaussProfile : Profile 8 where
  ψ := psiG
  cψ := 3 / 8
  cψ_pos := by norm_num
  symm p := by rw [psiG_apply, psiG_apply, norm_neg]
  at_zero := by rw [psiG_apply]; simp
  abs_le_one p := by
    rw [psiG_apply, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := sq_nonneg ‖p‖
    linarith
  le_max p := by
    rw [psiG_apply]
    have h := exp_neg_half_le (‖p‖ ^ 2) (sq_nonneg _)
    rw [neg_div] at h ⊢
    convert h using 2
  f_nonneg W L _ hW x :=
    mul_nonneg (inv_nonneg.mpr (ZWL_psiG_pos W L hW).le) (fRaw_psiG_nonneg W L hW x)
  f_symm _ _ _ _ := ⟨1, fun W L _ _ hW x => fWL_psiG_neg W L hW x⟩


end Witness


end RBM8D

namespace RBM8D

open Graphs

/-! ## The hypotheses of the local law at one point -/

/-- The hypotheses of [II, Theorem 3.6] at one point: `d = 8`, the Gaussian profile,
`c₀ = 1/4`, `c₁ = 1/2`, `κ = ε = 1/2`, `c₀ᵀ = 2`, `n = 2`, `D = 4`, `Σ = 0`, the second order
`T`-expansion, which is a `T`-expansion and satisfies `TRec.Def63G11`; the filter is proper;
the size `(16, 256)` lies in `adm(1/4, 1/2)` and in [II, (3.15)] (with equality); `z = i/2` lies in
`𝐃(1/2, 1/2)` there, and `B_{00} > 0`. -/
theorem G11.inst_endpointHyp : ∃ P : Profile 8,
    (0 : ℝ) < 1 / 4 ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 4 : ℝ) + 1 / 2 < 1 ∧ (0 : ℝ) < 2 ∧ 2 + 2 ≤ 4 ∧
    IsTExpansion 8 (smatVar P) (fun _ => []) 2 4 h2Rec ∧ h2Rec.Def63G11 ∧
    (llFilter 8 2 (1 / 4) (1 / 2) 2).NeBot ∧
    (∃ p : SizeL, p.1 = (16, 256) ∧ p.1 ∈ adm (1 / 4) (1 / 2) ∧ p ∈ thrSet 8 2 2) ∧
    (I / 2 : ℂ) ∈ specDom (1 / 2) (1 / 2) 16 256 ∧ 0 < bB 8 256 16 0 0 := by
  refine ⟨gaussProfile, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    G11.h2Rec_isTExpansion 8 _ _ 4 (by norm_num), G11.h2Rec_def63G11, G11.llFilter_neBot,
    ⟨⟨(16, 256), by norm_num⟩, rfl, G11.point_16_256.1, G11.point_16_256.2⟩,
    G11.specDom_16_256, by unfold bB; positivity⟩

/-! ## Monotonicity of the absolute-value graph -/

private theorem G11_prod_le {α : Type*} (f g : α → ℝ) :
    ∀ l : List α, (∀ a ∈ l, 0 ≤ f a) → (∀ a ∈ l, f a ≤ g a) → (l.map f).prod ≤ (l.map g).prod
  | [], _, _ => le_rfl
  | a :: l, h0, h => by
    simp only [List.map_cons, List.prod_cons]
    have h0' : ∀ b ∈ l, 0 ≤ f b := fun b hb => h0 b (List.mem_cons_of_mem _ hb)
    exact mul_le_mul (h a List.mem_cons_self)
      (G11_prod_le f g l h0' fun b hb => h b (List.mem_cons_of_mem _ hb))
      (List.prod_nonneg fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
        exact h0' b hb)
      ((h0 a List.mem_cons_self).trans (h a List.mem_cons_self))

end RBM8D

namespace RBM8D.Graphs

/-! ## The weights `W_d` of [II, (4.21)] and the light weights -/

/-- The weights `W_d` of [II, (4.21)], of any charge and any degree. -/
def Kind.isWD : Kind → Bool
  | .wD _ _ => true
  | _ => false

/-- The degree `d` of a weight `W_d`, and `0` for the other kinds. -/
def Kind.wDDeg : Kind → ℕ
  | .wD _ d => d
  | _ => 0

/-- The light weight of the charge of a weight `W_d`; the other kinds unchanged. -/
def Kind.wDL : Kind → Kind
  | .wD ch _ => .light ch
  | κ => κ

/-- The component `c` with a weight `W_d` replaced by the light weight `G_{xx} − m` of the same
charge, with the same ends, minor and label; the other components unchanged. -/
def Comp.wDLight {V : Type*} (c : Comp V) : Comp V := { c with kind := c.kind.wDL }

/-- The graph `Γ` with every weight `W_d` of [II, (4.21)] replaced by `d + 1` light weights
`G_{xx} − m` of the same charge, ends, minor and label (`W_d` has the scaling order `d + 1` of
`d + 1` light weights): the first one in place of `W_d`, the other `d` appended after the
components of `Γ`. A graph without `W_d` is unchanged up to the empty list of appended
components. -/
def Graph.wDLights {k n : ℕ} (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map Comp.wDLight ++ Γ.comps.flatMap fun c => List.replicate c.kind.wDDeg c.wDLight,
    Γ.coeff⟩

end RBM8D.Graphs

namespace RBM8D

open Graphs

/-- The bound of the weight `W_d` of [II, (4.21)]: with `e = g − m`, for `m ≠ 0` and
`|e| ≤ |m|/2`, `|g⁻¹ − m⁻¹ Σ_{j ≤ d} (−e/m)^j| ≤ 2 |m|^{−(d+2)} |e|^{d+1}` (the bound of `d + 1`
light weights `G_{xx} − m` at one atom, the scaling order `d + 1` of `W_d`). -/
def wDMajorantStmt : Prop :=
  ∀ (m g : ℂ) (d : ℕ), m ≠ 0 → ‖g - m‖ ≤ ‖m‖ / 2 →
    ‖g⁻¹ - m⁻¹ * ∑ j ∈ Finset.range (d + 1), (-(g - m) / m) ^ j‖ ≤
      2 * ‖m‖⁻¹ ^ (d + 2) * ‖g - m‖ ^ (d + 1)

/-- The closed form of `W_d`: `g⁻¹ − m⁻¹ Σ_{j ≤ d} (−(g − m)/m)^j = (−(g − m)/m)^{d+1} g⁻¹`. -/
private theorem G11_wD_closed (m g : ℂ) (d : ℕ) (hm : m ≠ 0) (hg : g ≠ 0) :
    g⁻¹ - m⁻¹ * ∑ j ∈ Finset.range (d + 1), (-(g - m) / m) ^ j =
      (-(g - m) / m) ^ (d + 1) * g⁻¹ := by
  set r : ℂ := -(g - m) / m with hr
  have hgr : g = m * (1 - r) := by
    rw [hr]
    field_simp
    ring
  have hS := geom_sum_mul_neg r (d + 1)
  have key : (g⁻¹ - m⁻¹ * ∑ j ∈ Finset.range (d + 1), r ^ j) * g = r ^ (d + 1) := by
    rw [sub_mul, inv_mul_cancel₀ hg]
    conv_lhs => rw [hgr]
    rw [show m⁻¹ * (∑ j ∈ Finset.range (d + 1), r ^ j) * (m * (1 - r)) =
      (m⁻¹ * m) * ((∑ j ∈ Finset.range (d + 1), r ^ j) * (1 - r)) by ring, inv_mul_cancel₀ hm,
      one_mul, hS]
    ring
  calc g⁻¹ - m⁻¹ * ∑ j ∈ Finset.range (d + 1), r ^ j
      = (g⁻¹ - m⁻¹ * ∑ j ∈ Finset.range (d + 1), r ^ j) * g * g⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]
    _ = r ^ (d + 1) * g⁻¹ := by rw [key]

/-- The bound of `W_d` ([II, (4.21)]): `|W_d| ≤ 2 |m|^{−(d+2)} |G_{xx} − m|^{d+1}` for
`|G_{xx} − m| ≤ |m|/2`, from the closed form and `|g| ≥ |m|/2`. -/
theorem wDMajorant : wDMajorantStmt := by
  intro m g d hm he
  have hm0 : 0 < ‖m‖ := norm_pos_iff.2 hm
  have hgm : ‖m‖ / 2 ≤ ‖g‖ := by
    have := norm_sub_norm_le m (m - g)
    rw [show m - (m - g) = g by ring, norm_sub_rev] at this
    linarith
  have hg : g ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgm
    linarith
  have hg0 : 0 < ‖g‖ := norm_pos_iff.2 hg
  rw [G11_wD_closed m g d hm hg, norm_mul, norm_pow, norm_div, norm_neg, norm_inv]
  have h1 : ‖g‖⁻¹ ≤ 2 * ‖m‖⁻¹ := by
    rw [inv_le_comm₀ hg0 (by positivity)]
    rw [mul_inv, inv_inv]
    linarith
  calc (‖g - m‖ / ‖m‖) ^ (d + 1) * ‖g‖⁻¹ ≤ (‖g - m‖ / ‖m‖) ^ (d + 1) * (2 * ‖m‖⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * ‖m‖⁻¹ ^ (d + 2) * ‖g - m‖ ^ (d + 1) := by
        rw [div_eq_mul_inv, mul_pow]
        ring

/-! ## The light weights of the weights `W_d`: the graph properties -/

section WDLights

variable {k n : ℕ}

private theorem G11_wDL_of_not {κ : Kind} (h : κ.isWD = false) : κ.wDL = κ := by
  cases κ <;> simp_all [Kind.wDL, Kind.isWD]

private theorem G11_wDDeg_of_not {κ : Kind} (h : κ.isWD = false) : κ.wDDeg = 0 := by
  cases κ <;> simp_all [Kind.wDDeg, Kind.isWD]

private theorem G11_wDLight_of_not {V : Type*} {c : Comp V} (h : c.kind.isWD = false) :
    c.wDLight = c := by
  unfold Comp.wDLight; rw [G11_wDL_of_not h]

private theorem G11_wDL_isDiffusive (κ : Kind) : κ.wDL.isDiffusive = κ.isDiffusive := by
  cases κ <;> rfl

private theorem G11_wDL_joinsMol (κ : Kind) : κ.wDL.joinsMol = κ.joinsMol := by
  cases κ <;> rfl

private theorem G11_wDL_isSolid (κ : Kind) : κ.wDL.isSolid = κ.isSolid := by
  cases κ <;> rfl

private theorem G11_wDL_isBlue (κ : Kind) : κ.wDL.isBlue = κ.isBlue := by
  cases κ <;> rfl

private theorem G11_wDL_eq_dot (κ : Kind) : κ.wDL = .dot ↔ κ = .dot := by
  cases κ <;> simp [Kind.wDL]

private theorem G11_wDL_eq_xdot (κ : Kind) : κ.wDL = .xdot ↔ κ = .xdot := by
  cases κ <;> simp [Kind.wDL]

private theorem G11_wDL_eq_G (κ : Kind) (ch : Charge) : κ.wDL = .G ch ↔ κ = .G ch := by
  cases κ <;> simp [Kind.wDL]

private theorem G11_wDL_beq_G (κ : Kind) (ch : Charge) :
    (κ.wDL == .G ch) = (κ == .G ch) := by
  cases κ <;> simp [Kind.wDL]

private theorem G11_wDL_beq_dot (κ : Kind) : (κ.wDL == .dot) = (κ == .dot) := by
  cases κ <;> simp [Kind.wDL]

/-- The components of `Γ.wDLights` are the components `c.wDLight`, `c` a component of `Γ`. -/
theorem G11.mem_wDLights (Γ : Graph k n) (c' : Comp (Atom k n)) :
    c' ∈ Γ.wDLights.comps ↔ ∃ c ∈ Γ.comps, c.wDLight = c' := by
  simp only [Graph.wDLights, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_replicate]
  constructor
  · rintro (h | ⟨c, hc, -, rfl⟩)
    · exact h
    · exact ⟨c, hc, rfl⟩
  · exact Or.inl

private theorem G11_exists_wDLights (Γ : Graph k n) (Q : Comp (Atom k n) → Prop) :
    (∃ c ∈ Γ.wDLights.comps, Q c) ↔ ∃ c ∈ Γ.comps, Q c.wDLight := by
  constructor
  · rintro ⟨c', hc', hQ⟩
    obtain ⟨c, hc, rfl⟩ := (G11.mem_wDLights Γ c').1 hc'
    exact ⟨c, hc, hQ⟩
  · rintro ⟨c, hc, hQ⟩
    exact ⟨c.wDLight, (G11.mem_wDLights Γ _).2 ⟨c, hc, rfl⟩, hQ⟩

private theorem G11_forall_wDLights (Γ : Graph k n) (Q : Comp (Atom k n) → Prop) :
    (∀ c ∈ Γ.wDLights.comps, Q c) ↔ ∀ c ∈ Γ.comps, Q c.wDLight := by
  constructor
  · intro h c hc
    exact h _ ((G11.mem_wDLights Γ _).2 ⟨c, hc, rfl⟩)
  · intro h c' hc'
    obtain ⟨c, hc, rfl⟩ := (G11.mem_wDLights Γ c').1 hc'
    exact h c hc

/-- A filter that discards the weights `W_d` and the light weights made from them sees the same
components in `Γ.wDLights` and in `Γ`. -/
private theorem G11_filter_wDLights (Γ : Graph k n) (p : Comp (Atom k n) → Bool)
    (hp : ∀ c, c.kind.isWD = true → p c = false ∧ p c.wDLight = false) :
    Γ.wDLights.comps.filter p = Γ.comps.filter p := by
  have h1 : ∀ l : List (Comp (Atom k n)), (l.map Comp.wDLight).filter p = l.filter p := by
    intro l
    induction l with
    | nil => rfl
    | cons c l ih =>
      by_cases hc : c.kind.isWD = true
      · obtain ⟨h1, h2⟩ := hp c hc
        simp [List.filter_cons, h1, h2, ih]
      · rw [Bool.not_eq_true] at hc
        simp [List.filter_cons, G11_wDLight_of_not hc, ih]
  have h2 : (Γ.comps.flatMap fun c => List.replicate c.kind.wDDeg c.wDLight).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp only [List.mem_flatMap, List.mem_replicate] at ha
    obtain ⟨c, -, hd, rfl⟩ := ha
    by_cases hc : c.kind.isWD = true
    · simp [(hp c hc).2]
    · exact absurd (G11_wDDeg_of_not (by simpa using hc)) hd
  simp only [Graph.wDLights, List.filter_append, h1, h2, List.append_nil]

private theorem G11_dotBlocks_filter {V : Type*} [DecidableEq V] (as : List V)
    (cs : List (Comp V)) :
    dotBlocks as cs = dotBlocks as (cs.filter fun c => decide (c.kind = .dot)) := by
  unfold dotBlocks
  generalize (as.map fun a => [a]) = P
  induction cs generalizing P with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c.kind = .dot
    · simp [List.filter_cons, hc, ih]
    · simp [List.filter_cons, hc, ih]

/-- `Γ.wDLights` has the dotted blocks of `Γ`. -/
theorem G11.wDLights_dotBlocks (Γ : Graph k n) (as : List (Atom k n)) :
    dotBlocks as Γ.wDLights.comps = dotBlocks as Γ.comps := by
  rw [G11_dotBlocks_filter, G11_dotBlocks_filter as Γ.comps, G11_filter_wDLights]
  intro c hc
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> simp_all [Kind.isWD, Comp.wDLight, Kind.wDL]

/-- `Γ.wDLights` has the same label atoms fixed to external atoms as `Γ`. -/
theorem G11.wDLights_labelFixedB (Γ : Graph 3 n) : Γ.wDLights.labelFixedB = Γ.labelFixedB := by
  funext v
  unfold Graph.labelFixedB
  rw [G11.wDLights_dotBlocks]

/-- `Γ.wDLights` has the components replaceable by a path of `Γ` at the same positions. -/
theorem G11.wDLights_pathEligB (Γ : Graph 3 n) (c : Comp (Atom 3 n)) :
    Γ.wDLights.pathEligB c = Γ.pathEligB c := by
  unfold Graph.pathEligB
  rw [G11.wDLights_labelFixedB]

theorem G11.wDLights_pmBlockB (Γ : Graph 3 n) : Γ.wDLights.pmBlockB = Γ.pmBlockB := by
  unfold Graph.pmBlockB
  rw [G11.wDLights_dotBlocks]

theorem G11.wDLights_diagRecoll (Γ : Graph 3 n) : Γ.wDLights.DiagRecoll ↔ Γ.DiagRecoll := by
  unfold Graph.DiagRecoll
  rw [G11.wDLights_dotBlocks]

theorem G11.wDLights_dotsAcyclic (Γ : Graph k n) : Γ.wDLights.DotsAcyclic ↔ Γ.DotsAcyclic := by
  unfold Graph.DotsAcyclic
  rw [G11.wDLights_dotBlocks, G11_filter_wDLights]
  intro c hc
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> simp_all [Kind.isWD, Comp.wDLight, Kind.wDL]

/-- A product over the components of `Γ.wDLights` is the product over the components `c` of `Γ`
of the factor at `c.wDLight` to the power `d + 1` for `W_d`, and `1` otherwise. -/
theorem G11.wDLights_prod {M : Type*} [CommMonoid M] (Γ : Graph k n) (g : Comp (Atom k n) → M) :
    (Γ.wDLights.comps.map g).prod =
      (Γ.comps.map fun c => g c.wDLight ^ (c.kind.wDDeg + 1)).prod := by
  have h : ∀ l : List (Comp (Atom k n)), (l.map (g ∘ Comp.wDLight)).prod *
      ((l.flatMap fun c => List.replicate c.kind.wDDeg c.wDLight).map g).prod =
      (l.map fun c => g c.wDLight ^ (c.kind.wDDeg + 1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.flatMap_cons,
        List.map_append, List.prod_append, ← ih, List.map_replicate, List.prod_replicate,
        pow_succ, Function.comp_apply]
      ac_rfl
  rw [← h]
  simp [Graph.wDLights, List.map_append, List.prod_append, List.map_map]

/-- The scaling order of `Γ.wDLights` is that of `Γ` (`W_d` has the order `d + 1` of `d + 1`
light weights). -/
theorem G11.wDLights_ord (Γ : Graph k n) : Γ.wDLights.ord = Γ.ord := by
  have hs : ∀ l : List (Comp (Atom k n)), ((l.map Comp.wDLight ++
      l.flatMap fun c => List.replicate c.kind.wDDeg c.wDLight).map fun c => c.kind.ord).sum =
      (l.map fun c => c.kind.ord).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons c l ih =>
      simp only [List.map_append, List.sum_append] at ih
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
        List.sum_append, List.map_replicate, List.sum_replicate]
      have hc : c.wDLight.kind.ord + c.kind.wDDeg • c.wDLight.kind.ord = c.kind.ord := by
        obtain ⟨κ, x, y, mi, lb⟩ := c
        cases κ <;> simp [Kind.wDDeg, Comp.wDLight, Kind.wDL, Kind.ord] <;> ring
      linarith
  unfold Graph.ord
  exact congrArg (fun x => x - 2 * (n : ℤ)) (hs Γ.comps)

theorem G11.wDLights_diagOrd (Γ : Graph 3 n) : Γ.wDLights.diagOrd = Γ.diagOrd := by
  unfold Graph.diagOrd
  rw [G11.wDLights_ord, G11.wDLights_pmBlockB]

theorem G11.wDLights_length (Γ : Graph k n) : Γ.wDLights.comps.length =
    Γ.comps.length + (Γ.comps.map fun c => c.kind.wDDeg).sum := by
  simp [Graph.wDLights, List.length_flatMap]

/-- The components of the kinds of [II, Def 3.2] and of the weights `W_d` without minor become
components of the kinds of [II, Def 3.2]. -/
theorem G11.wDLights_tKinds (Γ : Graph k n) (N : ℕ) (h : Γ.TKindsErr N) :
    Γ.wDLights.TKinds N := by
  unfold Graph.TKinds
  rw [List.all_eq_true, G11_forall_wDLights]
  intro c hc
  have := List.all_eq_true.1 h c hc
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ <;> simp_all [Comp.isTKind, Comp.wDLight, Kind.wDL]

theorem G11.wDLights_edgeGraph (Γ : Graph k n) : Γ.wDLights.edgeGraph = Γ.edgeGraph := by
  ext u v
  simp only [Graph.edgeGraph, SimpleGraph.fromRel_adj, G11_exists_wDLights]
  rfl

theorem G11.wDLights_wavedThetaGraph (Γ : Graph k n) :
    Γ.wDLights.wavedThetaGraph = Γ.wavedThetaGraph := by
  ext u v
  simp only [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj, G11_exists_wDLights]
  simp only [Comp.wDLight, G11_wDL_joinsMol, G11_wDL_isDiffusive, ne_eq, G11_wDL_eq_dot]

theorem G11.wDLights_molGraph (Γ : Graph k n) : Γ.wDLights.molGraph = Γ.molGraph := by
  ext u v
  simp only [Graph.molGraph, SimpleGraph.fromRel_adj, G11_exists_wDLights]
  simp only [Comp.wDLight, G11_wDL_joinsMol]

theorem G11.wDLights_dotGraph (Γ : Graph k n) : Γ.wDLights.dotGraph = Γ.dotGraph := by
  ext u v
  simp only [Graph.dotGraph, SimpleGraph.fromRel_adj, G11_exists_wDLights]
  simp only [Comp.wDLight, G11_wDL_eq_dot]

theorem G11.wDLights_sameMol (Γ : Graph k n) : Γ.wDLights.SameMol = Γ.SameMol := by
  funext u v
  unfold Graph.SameMol
  rw [G11.wDLights_molGraph]

theorem G11.wDLights_unpinned (Γ : Graph k n) : Γ.wDLights.Unpinned = Γ.Unpinned := by
  funext u
  unfold Graph.Unpinned Graph.SameBlock
  rw [G11.wDLights_dotGraph]

theorem G11.wDLights_normal (Γ : Graph k n) (C : ℕ) (h : Γ.Normal C) :
    Γ.wDLights.Normal (C + (Γ.comps.map fun c => c.kind.wDDeg).sum) := by
  obtain ⟨⟨hs, hc, hi, hd⟩, h2, h3⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [G11.wDLights_length]; omega
  · rw [G11.wDLights_edgeGraph]; exact hc
  · rw [G11.wDLights_wavedThetaGraph]; exact hi
  · rw [G11_forall_wDLights]
    intro c hc' hk
    exact hd c hc' ((G11_wDL_eq_dot c.kind).1 hk)
  · rw [G11_forall_wDLights]
    intro c hc' hk
    exact h2 c hc' (by rw [← G11_wDL_isSolid]; exact hk)
  · intro u v huv
    rw [G11_exists_wDLights, G11_exists_wDLights]
    simp only [Comp.wDLight, G11_wDL_eq_xdot, G11_wDL_isSolid]
    exact h3 u v huv

theorem G11.wDLights_atExternals (Γ : Graph 3 n) : Γ.wDLights.AtExternals ↔ Γ.AtExternals := by
  unfold Graph.AtExternals
  rw [G11_filter_wDLights]
  · simp only [List.any_eq_true, G11_exists_wDLights]
    simp only [Comp.wDLight, G11_wDL_beq_G, G11_wDL_isDiffusive, G11_wDL_beq_dot]
  · intro c hc
    obtain ⟨κ, x, y, mi, l⟩ := c
    cases κ <;> simp_all [Kind.isWD, Comp.wDLight, Kind.wDL, Kind.isDiffusive]

theorem G11.wDLights_tensorDiffusive (Γ : Graph 3 n) :
    Γ.wDLights.TensorDiffusive ↔ Γ.TensorDiffusive := by
  unfold Graph.TensorDiffusive
  rw [List.all_eq_true, List.all_eq_true, G11_forall_wDLights]
  simp only [Comp.wDLight, G11_wDL_isDiffusive]

theorem G11.wDLights_rootedAtExt (Γ : Graph 3 n) :
    Γ.wDLights.RootedAtExt ↔ Γ.RootedAtExt := by
  unfold Graph.RootedAtExt Graph.HasDiffToPinned Graph.DiffToPinned
  rw [G11.wDLights_unpinned]
  simp only [G11_exists_wDLights, G11_forall_wDLights]
  simp only [Comp.wDLight, G11_wDL_isDiffusive, G11_wDL_eq_G]

/-- The light weights of the weights `W_d` keep a doubly connected graph doubly connected: the
components of `Γ` keep their positions, ends and diffusive and blue kinds, and the molecules are
unchanged. -/
theorem G11.wDLights_doublyConnected (Γ : Graph k n) (h : Γ.DoublyConnected) :
    Γ.wDLights.DoublyConnected := by
  obtain ⟨bl, bu, hdis, hbl, hbu, hsb, hsu⟩ := h
  have hlen : Γ.comps.length ≤ Γ.wDLights.comps.length := by
    rw [G11.wDLights_length]; omega
  set φ : Fin Γ.comps.length ↪ Fin Γ.wDLights.comps.length := Fin.castLEEmb hlen with hφ
  have hget' : ∀ (j : ℕ) (hj : j < Γ.comps.length) (hj' : j < Γ.wDLights.comps.length),
      Γ.wDLights.comps[j] = Γ.comps[j].wDLight := by
    intro j hj hj'
    simp [Graph.wDLights, List.getElem_append, hj]
  have hget : ∀ i : Fin Γ.comps.length, Γ.wDLights.comps[φ i] = Γ.comps[i].wDLight :=
    fun i => hget' i.1 i.2 (φ i).2
  have hspan : ∀ B : Finset (Fin Γ.comps.length), Γ.Spans B → Γ.wDLights.Spans (B.map φ) := by
    intro B hB
    refine hB.mono fun a b hab => ?_
    simp only [Graph.net, SimpleGraph.fromRel_adj] at hab ⊢
    refine ⟨hab.1, ?_⟩
    rw [G11.wDLights_sameMol]
    rcases hab.2 with h | h
    · refine Or.inl ?_
      rcases h with h | ⟨i, hi, hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨φ i, Finset.mem_map_of_mem φ hi, by rw [hget]; exact hx,
          by rw [hget]; exact hy⟩
    · refine Or.inr ?_
      rcases h with h | ⟨i, hi, hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨φ i, Finset.mem_map_of_mem φ hi, by rw [hget]; exact hx,
          by rw [hget]; exact hy⟩
  refine ⟨bl.map φ, bu.map φ, Finset.disjoint_map φ |>.2 hdis, ?_, ?_, hspan bl hsb, hspan bu hsu⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    rw [hget]
    simpa [Comp.wDLight, G11_wDL_isDiffusive] using hbl j hj
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    rw [hget]
    simpa [Comp.wDLight, G11_wDL_isDiffusive, G11_wDL_isBlue] using hbu j hj

/-- **The graph properties of the light weights of the weights `W_d`**: for a graph `Γ` with the
kinds of `Err` (`Graph.TKindsErr`), normal regular, with [II, Def 3.2 (9)], doubly connected, with
only diffusive components at `⊗` and dotted edges forming a forest, the graph `Γ.wDLights` has the
kinds of [II, Def 3.2] and the same properties, the same `⊕`-recollision property at `𝔟₁ = 𝔟₂`,
the same rooting at the external atoms, the same scaling order and the same diagonal scaling
order. -/
theorem G11.wDLights_props (Γ : Graph 3 n) (N C : ℕ) (hK : Γ.TKindsErr N) (hN : Γ.Normal C)
    (hAE : Γ.AtExternals) (hDC : Γ.DoublyConnected) (hTD : Γ.TensorDiffusive)
    (hDA : Γ.DotsAcyclic) :
    Γ.wDLights.Normal (C + (Γ.comps.map fun c => c.kind.wDDeg).sum) ∧ Γ.wDLights.TKinds N ∧
      Γ.wDLights.AtExternals ∧ Γ.wDLights.DoublyConnected ∧ Γ.wDLights.TensorDiffusive ∧
      Γ.wDLights.DotsAcyclic ∧ (Γ.wDLights.DiagRecoll ↔ Γ.DiagRecoll) ∧
      (Γ.wDLights.RootedAtExt ↔ Γ.RootedAtExt) ∧ Γ.wDLights.ord = Γ.ord ∧
      Γ.wDLights.diagOrd = Γ.diagOrd :=
  ⟨G11.wDLights_normal Γ C hN, G11.wDLights_tKinds Γ N hK, (G11.wDLights_atExternals Γ).2 hAE,
    G11.wDLights_doublyConnected Γ hDC, (G11.wDLights_tensorDiffusive Γ).2 hTD,
    (G11.wDLights_dotsAcyclic Γ).2 hDA, G11.wDLights_diagRecoll Γ, G11.wDLights_rootedAtExt Γ,
    G11.wDLights_ord Γ, G11.wDLights_diagOrd Γ⟩

end WDLights

/-- **One weight `W_d` against its light weights**: on any data record with `m ≠ 0`, a component
`c` satisfies `|c| ≤ 2 |m|^{−(d+2)} |c.wDLight|^{d+1}` if it is a weight `W_d` with
`|G_{xx} − m| ≤ |m|/2` (`wDMajorant`), and `|c| ≤ |c.wDLight|` otherwise (then `c.wDLight = c`). -/
theorem G11.wD_val_le {ι V : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι) (σ : V → ι)
    (c : Comp V) (hm : D.m ≠ 0)
    (hs : c.kind.isWD = true → ‖Comp.val D σ c.wDLight‖ ≤ ‖D.m‖ / 2) :
    ‖Comp.val D σ c‖ ≤ (if c.kind.isWD then 2 * ‖D.m‖⁻¹ ^ (c.kind.wDDeg + 2) else 1) *
      ‖Comp.val D σ c.wDLight‖ ^ (c.kind.wDDeg + 1) := by
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ with
  | wD ch dd =>
    have hn : ∀ w : ℂ, ‖ch.apply w‖ = ‖w‖ := fun w => by cases ch <;> first | rfl | exact norm_star w
    simp only [Comp.wDLight, Kind.wDL, Kind.isWD, Kind.wDDeg, ite_true, Comp.val, hn] at hs ⊢
    exact wDMajorant _ _ dd hm (hs trivial)
  | _ => simp [Comp.wDLight, Kind.wDL, Kind.isWD, Kind.wDDeg]

/-- The constant `Π_{W_d} 2 · 4^{d+2}` of a graph, over its weights `W_d`. -/
def G11.wDConst {k n : ℕ} (Γ : Graph k n) : ℝ :=
  (Γ.comps.map fun c => if c.kind.isWD then 2 * 4 ^ (c.kind.wDDeg + 2) else 1).prod

theorem G11.one_le_wDConst {k n : ℕ} (Γ : Graph k n) : 1 ≤ G11.wDConst Γ := by
  unfold G11.wDConst
  have := G11_prod_le (fun _ => (1 : ℝ))
    (fun c => if c.kind.isWD then 2 * 4 ^ (c.kind.wDDeg + 2) else 1) Γ.comps
    (fun _ _ => zero_le_one) fun c _ => by
      split_ifs
      · have : (1 : ℝ) ≤ 4 ^ (c.kind.wDDeg + 2) := one_le_pow₀ (by norm_num)
        linarith
      · exact le_rfl
  simpa using this

end RBM8D

namespace RBM8D

open Graphs

end RBM8D
