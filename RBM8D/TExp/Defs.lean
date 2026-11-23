module

public import RBM8D.MainDefs
public import RBM8D.Graph.Deterministic
public import RBM8D.Graph.Standard
public import RBM8D.Graph.Local.Basic
public import RBM8D.Graph.MolRead
public import RBM8D.Basic.Domain
public import RBM8D.Graph.Local.Dot
public import RBM8D.Graph.Rooting
public import RBM8D.Graph.Local.IBP
public import RBM8D.Kernel.Circulant
public import RBM8D.Kernel.Propagator
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section

/-!
# Self-energies, labelled `Θ` edges, `T`-expansions and `T`-equations

The objects of [I, §2.3–2.5, §6.1, §6.3] = [II, §2.2, §3.1–3.2, §6.2–6.4]: deterministic data
records and the self-energy matrices, self-energies ([II, Def 2.7]), labelled `Θ` edges
([I, Def 6.3]), `T`-expansions and `T`-equations with [II, Def 6.3] in the block reading, the
induction hypothesis `H(n)` with the construction `Strat`, the second order `T`-expansion, and
the statements of [II, Theorem 3.7, Corollary 3.8, Lemma 3.9] as propositions.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- A family of variance matrices `S_{W,L}` on `Z_L^d`, indexed by the band width `W` and the
side length `L ≥ 1`. -/
abbrev VarFamily (d : ℕ) : Type := ℕ → ∀ (L : ℕ) [NeZero L], Matrix (Zd d L) (Zd d L) ℝ

/-- A data record whose self-energy matrices of even order `k ∈ [4, N)` are the values of
`Sig k` on the record itself (the matrices read by the labelled `Θ` edges, [I, Def 6.3]). -/
def SigConsistent {ι : Type} [Fintype ι] [DecidableEq ι] (Sig : ℕ → Expansion 2) (N : ℕ)
    (D : Data ι) : Prop :=
  ∀ k, 4 ≤ k → k < N → Even k → D.Sig k = Matrix.of fun x y => (Sig k).val D ![x, y]

/-- The components of the graphs of [II, Def 3.2]: solid edges, regular and light weights, waved
edges, `Θ` edges with labels of entries even in `[4, N]` ([II, Def 3.2 (2)]), dotted and
`×`-dotted edges; no minor. -/
def Comp.isTKind {V : Type*} (N : ℕ) (c : Comp V) : Bool :=
  c.minor.isEmpty &&
    match c.kind with
    | .G _ | .weight _ | .light _ | .waved _ | .dot | .xdot => true
    | .theta o => labelOK N o
    | _ => false

/-- Every component of `Γ` has a kind of [II, Def 3.2] with labels of entries in `[4, N]`. -/
def Graph.TKinds {k n : ℕ} (N : ℕ) (Γ : Graph k n) : Prop :=
  Γ.comps.all (Comp.isTKind N) = true

/-- The kinds of the graphs of `Err`: every component of `Γ` has a kind of [II, Def 3.2] with
labels of entries in `[4, N]` (`Comp.isTKind`), or is a weight `W_d` of [II, (4.21)] without
minor, of any charge and any degree `d`, with or without a `P`/`Q` label (the graphs of scaling
order `> D` of [II, Lemma 4.15], which may carry `P`/`Q` labels by [II, Def 3.2 (8)]). -/
def Graph.TKindsErr {k n : ℕ} (N : ℕ) (Γ : Graph k n) : Prop :=
  Γ.comps.all (fun c => c.isTKind N ||
    (c.minor.isEmpty && match c.kind with | .wD _ _ => true | _ => false)) = true

/-- The kinds of [II, Def 3.2] are kinds of `Err`. -/
theorem Graph.tKindsErr_of_tKinds {k n : ℕ} (N : ℕ) (Γ : Graph k n) (h : Γ.TKinds N) :
    Γ.TKindsErr N :=
  List.all_eq_true.2 fun c hc => by
    simp [List.all_eq_true.1 h c hc]

/-- A component of a graph of the form `Graph.Plain`, as a boolean: no minor, no `(G_{xx})⁻¹` or
`W_D` weight, not a dotted loop, a weight sitting on its atom, a label only on a random
component. -/
def Comp.plainCheck {V : Type*} [DecidableEq V] (c : Comp V) : Bool :=
  c.minor.isEmpty && (match c.kind with | .inv _ => false | .wD _ _ => false | _ => true) &&
    (c.kind != .dot || c.x != c.y) && (!c.kind.isWeight || c.y == c.x) &&
    (c.label.isNone || c.kind.isRandom)

/-- `Graph.Plain` is the boolean `Comp.plainCheck` on every component. -/
theorem Graph.plain_iff_check {k n : ℕ} (Γ : Graph k n) :
    Γ.Plain ↔ Γ.comps.all Comp.plainCheck = true := by
  rw [List.all_eq_true]
  refine forall₂_congr fun c _ => ?_
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ <;> cases lab <;>
    simp [Comp.plainCheck, Comp.WF, Kind.isWeight, Kind.isRandom, List.isEmpty_iff]

/-- `Graph.Plain` is decidable, by `Comp.plainCheck`. -/
instance Graph.instDecidablePlain {k n : ℕ} (Γ : Graph k n) : Decidable Γ.Plain :=
  decidable_of_iff _ (Graph.plain_iff_check Γ).symm

/-- [I, (1.25)] = [II, (1.20)] for `Σ_l`, as exact identities for every `(W, L)` and every `z` with
`Im z > 0`: `Σ_l(x, x + a) = Σ_l(0, a)` and `Σ_l(0, a) = Σ_l(0, -a)`. -/
def SelfEnergySymm (d : ℕ) (Svar : VarFamily d)
    (Sig : ℕ → Expansion 2) (l : ℕ) : Prop :=
  ∀ (W L : ℕ) [NeZero L] (z : ℂ), 0 < z.im → ∀ x a : Zd d L,
    sigMat Sig (Svar W L) z l x (x + a) = sigMat Sig (Svar W L) z l 0 a ∧
      sigMat Sig (Svar W L) z l 0 a = sigMat Sig (Svar W L) z l 0 (-a)

/-- [I, (1.26)–(1.27)] for `Σ_l`, uniformly in the parameters: for all `κ, ε, c₀, c₁ > 0` with
`c₀ + c₁ < 1` and every `τ > 0` there is `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)` and
`z ∈ 𝐃(κ, ε)`: `|Σ_l(0, x)| ≤ L^τ W^{-(l-4)d/2} B_{0x}² + L^τ W^{-(l-2)d/2} 1_{x=0}` for every
`x`, and `|Σ_x Σ_l(0, x)| ≤ L^τ η W^{-(l-2)d/2}`. The diagonal term `L^τ W^{-(l-2)d/2} 1_{x=0}`
is added to [I, (1.26)]: a graph of [I, Def 2.13 (i)] with a dotted edge between `x` and `y`,
such as `m² δ_{xy} s_{xx} S⁺_{xx}` of order `6`, has size `W^{-2d}` at `x = 0`. -/
def SelfEnergyBound (d : ℕ) (Svar : VarFamily d)
    (Sig : ℕ → Expansion 2) (l : ℕ) : Prop :=
  ∀ κ ε c₀ c₁ : ℝ, 0 < κ → 0 < ε → 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L,
        (∀ x : Zd d L, ‖sigMat Sig (Svar W L) z l 0 x‖ ≤
          (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
            (if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)) ∧
        ‖∑ x : Zd d L, sigMat Sig (Svar W L) z l 0 x‖ ≤
          (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))

/-- `Sig l` is an `l`-th order self-energy ([II, Def 2.7] = [I, Def 2.13 (i)–(ii)]) for the
dimension `d` and the variance matrices `Svar W L` on `Z_L^d`, the labelled `Θ` edges of `Sig l`
reading the lower orders of `Sig`. -/
def IsSelfEnergy (d : ℕ) (Svar : VarFamily d)
    (Sig : ℕ → Expansion 2) (l : ℕ) : Prop :=
  SelfEnergyShape l (Sig l) ∧ SelfEnergySymm d Svar Sig l ∧ SelfEnergyBound d Svar Sig l

/-- The even orders `4 ≤ k ≤ n` of `Sig` are self-energies. -/
def SelfEnergiesUpTo (d : ℕ) (Svar : VarFamily d)
    (Sig : ℕ → Expansion 2) (n : ℕ) : Prop :=
  ∀ k, 4 ≤ k → k ≤ n → Even k → IsSelfEnergy d Svar Sig k

/-- The even orders `4 ≤ k ≤ n` of `Sig` have the shape of a self-energy ([II, Def 3.2 (3)]). -/
def SelfEnergyShapesUpTo (Sig : ℕ → Expansion 2) (n : ℕ) : Prop :=
  ∀ k, 4 ≤ k → k ≤ n → Even k → SelfEnergyShape k (Sig k)

/-- The labels `(j₁ + 2, …, j_r + 2)` with `jᵢ ≥ 2` even and `Σ jᵢ ≤ b`, in at most `f`
levels. -/
def chainLabelsAux : ℕ → ℕ → List (List ℕ)
  | 0, _ => []
  | f + 1, b => ((List.range (b + 1)).filter fun j => decide (2 ≤ j) && j % 2 == 0).flatMap
      fun j => [j + 2] :: (chainLabelsAux f (b - j)).map ((j + 2) :: ·)

/-- The labels `(2k₁, …, 2k_l)`, `l ≥ 1`, `2kᵢ ≥ 4`, of the labelled `Θ` edges of scaling order
`k = Σ 2kᵢ - 2(l - 1) ≤ n` ([II, (3.3)–(3.4)]; for `l ≥ 2` the bound `2kᵢ ≤ k - 1` of (3.4)
holds automatically). -/
def chainLabels (n : ℕ) : List (List ℕ) := chainLabelsAux (n - 2) (n - 2)

/-- The graph `m Θ^{[o]}_{a b₁} Ḡ_{b₁ b₂}` with the labelled `Θ` edge of label `o` (the plain
`Θ` edge for `o = []`); external atoms `a = 0`, `b₁ = 1`, `b₂ = 2`. -/
def thetaLabelGraph (o : List ℕ) : Graph 3 0 :=
  ⟨[mkC (.theta o) (.inl 0) (.inl 1), mkC (.G .minus) (.inl 1) (.inl 2)], cm⟩

/-- The graph `m Θ^{[o]}_{a b₁} Ḡ_{b₁ b₂}` is plain, for every label `o`. -/
theorem thetaLabelGraph_plain (o : List ℕ) : (thetaLabelGraph o).Plain := by
  rw [Graph.plain_iff_check]
  rfl

/-- The leading term `m Θ_{a b₁} Ḡ_{b₁ b₂}` of [II, (3.1)]. -/
def leadExp : Expansion 3 := [⟨0, thetaLabelGraph []⟩]

/-- The term `m (Θ Σ_T^{(n)} Θ)_{a b₁} Ḡ_{b₁ b₂}` of [II, (3.1)]: by [II, (3.3)–(3.4)] it is the
sum of `m Θ^{[o]}_{a b₁} Ḡ_{b₁ b₂}` over the labels `o` of order `≤ n`, the labelled edge having
the value `(Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ)_{a b₁}`. -/
def sigmaTExp (n : ℕ) : Expansion 3 := (chainLabels n).map fun o => ⟨0, thetaLabelGraph o⟩

/-- The formal sums `R_T^{(n)}`, `A_T^{(>n)}`, `Q_T^{(n)}`, `Err_{n,D}` of [II, (3.1)], with
external atoms `⊗ = a = 0`, `⊕ = b₁ = 1`, `⊖ = b₂ = 2`. -/
structure TRec where
  R : Expansion 3
  A : Expansion 3
  Q : Expansion 3
  Err : Expansion 3

/-- The right side of [II, (3.1)] at order `n`. -/
def TRec.rhs (n : ℕ) (𝒯 : TRec) : Expansion 3 :=
  leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err

/-- The identity [II, (3.1)]: `T_{a,b₁b₂}` equals the right side, at every sample, for every data
record with the model relations whose self-energy matrices of orders `≤ n` are the values of
`Sig`. -/
def TRec.Identity (Sig : ℕ → Expansion 2) (n : ℕ) (𝒯 : TRec) : Prop :=
  ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
    modelAdm Ω ι PF D → (∀ ω, SigConsistent Sig (n + 1) (D ω)) → ∀ (e : Fin 3 → ι) (ω : Ω),
      (𝒯.rhs n).valR PF D e ω = tGraph.valR PF D e ω

/-- [II, Def 3.2 (9)]: exactly one diffusive edge is attached to `⊗`; a blue solid, diffusive or
dotted edge is attached to `⊕`; a red solid, diffusive or dotted edge is attached to `⊖`. -/
def Graph.AtExternals {n : ℕ} (Γ : Graph 3 n) : Prop :=
  (Γ.comps.filter fun c => c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0)).length = 1 ∧
    Γ.comps.any (fun c => (c.kind == .G .plus || c.kind.isDiffusive || c.kind == .dot) &&
      (c.x == .inl 1 || c.y == .inl 1)) = true ∧
    Γ.comps.any (fun c => (c.kind == .G .minus || c.kind.isDiffusive || c.kind == .dot) &&
      (c.x == .inl 2 || c.y == .inl 2)) = true

/-- Every diffusive edge with an end at `⊗` has `⊕` as its other end: the edge at `⊗` is
`Θ_{⊗⊕}`, plain or labelled (the component test is that of the first clause of
`Graph.AtExternals`). -/
def Graph.RootAtPlus {n : ℕ} (Γ : Graph 3 n) : Prop :=
  Γ.comps.all (fun c => !(c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0)) ||
    (c.x == .inl 0 && c.y == .inl 1) || (c.x == .inl 1 && c.y == .inl 0)) = true

instance {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.RootAtPlus :=
  inferInstanceAs (Decidable (_ = true))

/-- The atom of every `Q` label is `⊕`: in a graph without internal atoms the label of the
`Q`-graph of [I, Lemma 2.5, (2.9)] sits at `𝔟₁`. -/
def Graph.QLabelAtPlus {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∀ c ∈ Γ.comps, ∀ u, c.label = some (.Q, u) → u = .inl 1

instance {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.QLabelAtPlus := by
  unfold Graph.QLabelAtPlus
  infer_instance

/-- The profile at `⊖` of a graph: every component with an end at `⊖` is a dotted edge, a
`×`-dotted edge, or a red solid edge `Ḡ_{u⊖}` with second atom `⊖` and first atom `u ≠ ⊖`, and at
most one component is of the last kind. In the charge pattern of [II, Lemma 5.13] the atom `⊖`
is only a column index of `Ḡ`; with [II, Def 3.2 (9)] and the clause on an unpinned `⊖` this is
the form of the graphs without internal atoms that the substitution at `y₂ = ⊖` reads. -/
def Graph.MinusProfile {n : ℕ} (Γ : Graph 3 n) : Prop :=
  (∀ c ∈ Γ.comps, (c.x = .inl 2 ∨ c.y = .inl 2) →
      c.kind = .dot ∨ c.kind = .xdot ∨ (c.kind = .G .minus ∧ c.y = .inl 2 ∧ c.x ≠ .inl 2)) ∧
    (Γ.comps.filter fun c =>
      decide (c.kind = .G .minus ∧ c.y = .inl 2 ∧ c.x ≠ .inl 2)).length ≤ 1

instance {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.MinusProfile := by
  unfold Graph.MinusProfile
  infer_instance

/-- The graph properties of [II, Def 3.2] with labels of entries in `[4, N]`, at order `n` and
error order `D`: every graph is normal regular, satisfies (9) and is doubly connected (10); the
graphs of `R`, `A`, `Q` have the kinds of (2), and the graphs of `Err` the kinds of (2) or the
weights `W_d` of [II, (4.21)] (`Graph.TKindsErr`); `R` consists of label-free
`⊕/⊖`-recollision graphs of orders `3, …, n` (4); `A` of label-free graphs of order `> n` (5);
`Q` of `Q`-graphs of order `≥ 2` (6); `Err` of graphs of order `> D` (8). -/
def TRec.Shape (N n D : ℕ) (𝒯 : TRec) : Prop :=
  ((∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q,
      (∃ C, g.2.Normal C) ∧ g.2.TKinds N ∧ g.2.AtExternals ∧ g.2.DoublyConnected) ∧
    (∀ g ∈ 𝒯.Err,
      (∃ C, g.2.Normal C) ∧ g.2.TKindsErr N ∧ g.2.AtExternals ∧ g.2.DoublyConnected)) ∧
  (∀ g ∈ 𝒯.R, g.2.LabelFree ∧ g.2.IsRecollision {1, 2} ∧ 3 ≤ g.2.ord ∧ g.2.ord ≤ n) ∧
  (∀ g ∈ 𝒯.A, g.2.LabelFree ∧ (n : ℤ) < g.2.ord) ∧
  (∀ g ∈ 𝒯.Q, g.2.IsQGraph ∧ 2 ≤ g.2.ord) ∧
  (∀ g ∈ 𝒯.Err, (D : ℤ) < g.2.ord)

/-- [II, Def 6.3] in the block reading of the dotted edges at `⊗`, `⊕`, `⊖` (`Graph.toMG'`): the
graphs of `R` are globally standard (`gsPM'`) and those of `A` sequentially pre-deterministic
(`spdPM'`); those of `R`, and those of `A` and `Q` with an internal atom, satisfy the clause on
the external atoms and the charge pattern of the block normal form, and those of `A` and `Q`
without an internal atom have their diffusive edge at `⊗` joining `⊗` to `⊕`
(`Graph.RootAtPlus`); those of `Q` are sequentially pre-deterministic and satisfy the `Q`-label
condition `Graph.QLabelInMISB`, and those of `Q` without an internal atom have their `Q` label at
`⊕` (`Graph.QLabelAtPlus`). With these, the clauses that the substitution of
[II, Lemma 6.5] reads on the dotted edges, the labels and the orders, and the rooting that
[II, (8.18)–(8.24)] read at `𝔟₁ = 𝔟₂`: every graph of `R`, `A`, `Q`, `Err` has only diffusive
edges at `⊗` (`Graph.TensorDiffusive`), dot excess `0`, no labelled dotted or `×`-dotted edge
(`Graph.NoLabDot`) and at most one label (one label group per graph, [II, §4.4]); every
`⊕/⊖`-recollision graph of `A` is globally standard; the graphs of `R` and `A` in which `⊕`, `⊖`
lie in one dotted block (`Graph.PMBlock`) have scaling order `≥ 5`, those of `Q` scaling order
`≥ 4`; the graphs of `Q` and `Err` satisfy `Graph.RgCheck`; every graph of `A`,
`Q` and `Err` with an internal atom that is not a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`
(`Graph.DiagRecoll`) is rooted at the external atoms (`Graph.RootedAtExt`); the graphs of `R`,
`A`, `Q` are plain (`Graph.Plain`), that is atomic graphs in the sense of [I, Def 2.6]: no
minor, no `(G_{xx})⁻¹` or `W_D` weight, no dotted loop, every weight on its atom and a `P`/`Q`
label only on a solid edge or a weight; the graphs of `A` and `Q` without an internal atom have
the profile at `⊖` (`Graph.MinusProfile`). -/
def TRec.Def63 (𝒯 : TRec) : Prop :=
  ((∀ g ∈ 𝒯.R, gsPM' g.2 ∧ g.2.ExtClause ∧ g.2.ColourInvB) ∧
  (∀ g ∈ 𝒯.A, spdPM' g.2 ∧ ((g.1 = 0 ∧ g.2.RootAtPlus) ∨ g.2.ExtClause ∧ g.2.ColourInvB)) ∧
  (∀ g ∈ 𝒯.Q, spdPM' g.2 ∧ g.2.QLabelInMISB ∧
    ((g.1 = 0 ∧ g.2.RootAtPlus) ∨ g.2.ExtClause ∧ g.2.ColourInvB))) ∧
    (∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, g.2.TensorDiffusive ∧ g.2.dotExcess = 0 ∧ g.2.NoLabDot ∧
      g.2.labels.length ≤ 1) ∧
    (∀ g ∈ 𝒯.A, g.2.IsRecollision {1, 2} → gsPM' g.2) ∧
    (∀ g ∈ 𝒯.R ++ 𝒯.A, g.2.PMBlock → 5 ≤ g.2.ord) ∧
    (∀ g ∈ 𝒯.Q, g.2.PMBlock → 4 ≤ g.2.ord) ∧
    (∀ g ∈ 𝒯.Q ++ 𝒯.Err, g.2.RgCheck) ∧
    (∀ g ∈ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt) ∧
    (∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q, g.2.Plain) ∧
    (∀ g ∈ 𝒯.Q, g.1 = 0 → g.2.QLabelAtPlus) ∧
    (∀ g ∈ 𝒯.A ++ 𝒯.Q, g.1 = 0 → g.2.MinusProfile)

/-- The graphs of `R`, `A`, `Q` of a record with the clauses `TRec.Def63` are plain. -/
theorem TRec.plain_of_def63 {𝒯 : TRec} (h : 𝒯.Def63) : ∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q, g.2.Plain :=
  h.2.2.2.2.2.2.2.1

/-- The graphs of `Q` without an internal atom of a record with the clauses `TRec.Def63` have
their `Q` label at `⊕`. -/
theorem TRec.qLabelAtPlus_of_def63 {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.Q, g.1 = 0 → g.2.QLabelAtPlus :=
  h.2.2.2.2.2.2.2.2.1

/-- The graphs of `A` and `Q` without an internal atom of a record with the clauses `TRec.Def63`
have the profile at `⊖` (`Graph.MinusProfile`). -/
theorem TRec.minusProfile_of_def63 {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.A ++ 𝒯.Q, g.1 = 0 → g.2.MinusProfile :=
  h.2.2.2.2.2.2.2.2.2

/-- The structural part of an `n`-th order `T`-expansion with `D`-th order error ([II, Def 3.2]
items (1)–(6), (8)–(10), and [II, Def 6.3]): `n < D`, the identity [II, (3.1)], the even orders
`4, …, n` of `Sig` have the shape of self-energies, and the graph properties. -/
def TRec.IsTExpStruct (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒯 : TRec) : Prop :=
  n < D ∧ 𝒯.Identity Sig n ∧ SelfEnergyShapesUpTo Sig n ∧ 𝒯.Shape n n D ∧ 𝒯.Def63

/-- An `n`-th order `T`-expansion with `D`-th order error ([II, Def 3.2], [II, Def 6.3]): the
structural part, and `Sig k` is a self-energy for every even `4 ≤ k ≤ n` ([II, Def 3.2 (3)]). -/
def IsTExpansion (d : ℕ) (Svar : VarFamily d) (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒯 : TRec) :
    Prop :=
  SelfEnergiesUpTo d Svar Sig n ∧ 𝒯.IsTExpStruct Sig n D

/-- [II, Def 3.2 (7)] between the `T`-expansions `𝒯` of order `n` and `𝒯'` of a higher order:
for every `k ≤ n` the graphs of order `k` of `R` and of `Q` are the same, up to order. -/
def TRec.Coherent (n : ℕ) (𝒯 𝒯' : TRec) : Prop :=
  ∀ k : ℕ, k ≤ n →
    (𝒯.R.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
        (𝒯'.R.filter fun g => decide (g.2.ord = (k : ℤ))) ∧
      (𝒯.Q.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
        (𝒯'.Q.filter fun g => decide (g.2.ord = (k : ℤ)))

/-- The graphs of `R`, `A`, `Q` of `𝒯` and of `𝒯'` in which `⊕`, `⊖` lie in one dotted block
(`Graph.PMBlock`), of every scaling order `k ≤ m`, are the same up to order; the three formal sums
are joined (a graph of order `n + 1` lies in `A` of the `n`-th order and in `R` of the
`(n + 1)`-th order expansion). -/
def TRec.CoherentPM (m : ℕ) (𝒯 𝒯' : TRec) : Prop :=
  ∀ k : ℕ, k ≤ m →
    ((𝒯.R ++ 𝒯.A ++ 𝒯.Q).filter fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ))).Perm
      ((𝒯'.R ++ 𝒯'.A ++ 𝒯'.Q).filter fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ)))

/-- The index of the internal atom `j ≠ i` after the internal atom `i` is removed. -/
def finDrop {n : ℕ} (i j : Fin n) (h : j ≠ i) : Fin (n - 1) :=
  if hlt : j.val < i.val then ⟨j.val, by omega⟩
  else ⟨j.val - 1, by have := Fin.val_ne_of_ne h; omega⟩

/-- The graph `𝒢_{x, b₁ b₂}` with external atoms `x = 0`, `b₁ = 1`, `b₂ = 2` obtained from a graph
with external atoms `a, b₁, b₂` in which `a` does not occur, the internal atom `i` becoming the
external atom `x`. -/
def Graph.rootAt {n : ℕ} (Γ : Graph 3 n) (i : Fin n) : Graph 3 (n - 1) :=
  Γ.mapAtoms fun u => match u with
    | .inl j => .inl j
    | .inr j => if h : j = i then .inl 0 else .inr (finDrop i j h)

/-- The graph without the component of index `j`. -/
def Graph.dropComp {k n : ℕ} (Γ : Graph k n) (j : ℕ) : Graph k n :=
  ⟨Γ.comps.eraseIdx j, Γ.coeff⟩

/-- The graph `𝒢_{x, b₁ b₂}` of [II, Def 3.3 (4)] for the end `v` of the `Θ` edge at `⊗`: for an
internal `v` the graph `rootAt v`; for an external `v` (`x = v` fixed by a dotted edge) the graph
with the dotted edge `x = v` added, the atom `0` standing for `x`. -/
def Graph.rootGraph {n : ℕ} (Γ : Graph 3 n) : Atom 3 n → Σ n' : ℕ, Graph 3 n'
  | .inr i => ⟨n - 1, Γ.rootAt i⟩
  | .inl b => ⟨n, ⟨Γ.comps ++ [mkC .dot (.inl 0) (.inl b)], Γ.coeff⟩⟩

/-- [II, Def 3.3 (4)]: the graph is `∑_x Θ_{a x} 𝒢_{x, b₁ b₂}` with `a = ⊗`: its only component
at `⊗` is a plain `Θ` edge with first index `⊗` and second index an atom `v ≠ ⊗`, and the rest
does not mention `⊗` (neither in the ends, the minor atoms, nor the atom of a label) and, with
`x = v` external, is normal regular. -/
def Graph.ThetaRooted {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∃ (j : Fin Γ.comps.length) (v : Atom 3 n), v ≠ .inl 0 ∧
    Γ.comps[j].kind = .theta [] ∧ Γ.comps[j].minor = [] ∧ Γ.comps[j].label = none ∧
    (Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v) ∧
    (∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor ∧
      c.label.map Prod.snd ≠ some (.inl 0)) ∧
    ∃ C, ((Γ.dropComp j).rootGraph v).2.Normal C

/-- The data of an `n`-th order `T`-equation: `Σ_n` (external atoms `x = 0`, `y = 1`) and the
formal sums `R_IT^{(n)}`, `A_IT^{(>n)}`, `Q_IT^{(n)}`, `Err'_{n,D}` of [II, (3.5)]. -/
structure TEqRec where
  SigN : Expansion 2
  R : Expansion 3
  A : Expansion 3
  Q : Expansion 3
  Err : Expansion 3

/-- The formal sums `R`, `A`, `Q`, `Err` of a `T`-equation as a record of the same type as a
`T`-expansion. -/
def TEqRec.toTRec (𝒬 : TEqRec) : TRec := ⟨𝒬.R, 𝒬.A, 𝒬.Q, 𝒬.Err⟩

/-- `Σ̃^{(n)} = Σ_n + Σ_{l=4}^{n-1} Σ_l` of [II, (3.14)] on the record `D`: the value of `SigN`
and the self-energy matrices of `D` of even order `l ∈ [4, n)`; the odd orders vanish
([II, (2.6)]). -/
def sigTilde {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (SigN : Expansion 2) (D : Data ι) :
    Matrix ι ι ℂ :=
  Matrix.of (fun x y => SigN.val D ![x, y]) + ∑ l ∈ (Finset.Ico 4 n).filter Even, D.Sig l

/-- The identity [II, (3.5)]: `T_{a,b₁b₂} = m Θ_{a b₁} Ḡ_{b₁ b₂} + Σ_x (Θ Σ̃^{(n)})_{a x}
T_{x,b₁b₂} + R + A + Q + Err'`, at every sample, for every data record with the model relations
whose self-energy matrices of orders `< n` are the values of `Sig`. -/
def TEqRec.Identity (Sig : ℕ → Expansion 2) (n : ℕ) (𝒬 : TEqRec) : Prop :=
  ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
    modelAdm Ω ι PF D → (∀ ω, SigConsistent Sig n (D ω)) → ∀ (e : Fin 3 → ι) (ω : Ω),
      tGraph.valR PF D e ω =
        (leadExp ++ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).valR PF D e ω +
          ∑ x, ((D ω).Theta * sigTilde n 𝒬.SigN (D ω)) (e 0) x * tGraph.valR PF D ![x, e 1, e 2] ω

/-- The structural part of an `n`-th order `T`-equation with `D`-th order error ([II, Def 3.3],
[II, Def 6.3]): `n < D`; the identity [II, (3.5)]; the even orders `4, …, n - 1` of `Sig` have
the shape of self-energies; `Σ_n` has the shape of an `n`-th order self-energy (2), (3), (5);
`R`, `A`, `Q`, `Err` have the properties of [II, Def 3.2] with labels in `[4, n - 1]` (1), (3),
every graph has the form (4), and [II, Def 6.3] holds. -/
def TEqRec.IsTEqStruct (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒬 : TEqRec) : Prop :=
  n < D ∧ 𝒬.Identity Sig n ∧ SelfEnergyShapesUpTo Sig (n - 1) ∧ SelfEnergyShape n 𝒬.SigN ∧
    𝒬.toTRec.Shape (n - 1) n D ∧
    (∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, g.2.ThetaRooted) ∧ 𝒬.toTRec.Def63

/-- A graph of the form [II, Def 3.3 (4)] carries no `P`/`Q` label at `⊗`: the component at `⊗` has
no label and the rest does not mention `⊗`. -/
theorem Graph.ThetaRooted.label_ne_root {n : ℕ} {Γ : Graph 3 n} (h : Γ.ThetaRooted) :
    ∀ c ∈ Γ.comps, c.label.map Prod.snd ≠ some (.inl 0) := by
  obtain ⟨j, v, -, -, -, hl, -, hrest, -⟩ := h
  have hd : Γ.comps = Γ.comps.take j ++ Γ.comps[j] :: Γ.comps.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j Γ.comps, List.drop_eq_getElem_cons j.2]
    rfl
  intro c hc
  rw [hd, List.mem_append, List.mem_cons] at hc
  rcases hc with hc | rfl | hc
  · exact (hrest c (by simp [Graph.dropComp, List.eraseIdx_eq_take_drop_succ, hc])).2.2.2
  · have h0 : Γ.comps[(j : ℕ)].label = none := hl
    simp [h0]
  · exact (hrest c (by simp [Graph.dropComp, List.eraseIdx_eq_take_drop_succ, hc])).2.2.2

/-- An `n`-th order `T`-equation with `D`-th order error ([II, Def 3.3] read with `Q_IT^{(n)}`):
the structural part, and `Sig k` is a self-energy for every even `4 ≤ k ≤ n - 1`. -/
def IsTEquation (d : ℕ) (Svar : VarFamily d) (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒬 : TEqRec) :
    Prop :=
  SelfEnergiesUpTo d Svar Sig (n - 1) ∧ 𝒬.IsTEqStruct Sig n D

/-- The graphs of scaling order `≤ m` of `R`, `A`, `Q` and `Err` of `𝒯` and of `𝒯'` are the same,
up to order. -/
def TRec.AgreeTo (m : ℕ) (𝒯 𝒯' : TRec) : Prop :=
  ∀ k : ℕ, k ≤ m →
    (𝒯.R.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
        (𝒯'.R.filter fun g => decide (g.2.ord = (k : ℤ))) ∧
      (𝒯.A.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
        (𝒯'.A.filter fun g => decide (g.2.ord = (k : ℤ))) ∧
      (𝒯.Q.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
        (𝒯'.Q.filter fun g => decide (g.2.ord = (k : ℤ))) ∧
      (𝒯.Err.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
        (𝒯'.Err.filter fun g => decide (g.2.ord = (k : ℤ)))

/-- The graph with every plain `Θ` edge at `⊗` replaced by the labelled `Θ` edge of label `o`. -/
def Graph.relabelRoot {n : ℕ} (o : List ℕ) (Γ : Graph 3 n) : Graph 3 n :=
  ⟨Γ.comps.map fun c =>
      if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0) then { c with kind := .theta o }
      else c,
    Γ.coeff⟩

/-- The formal sums `R`, `Q` from which the `n`-th order `T`-expansion obtained by solving the
`T`-equation `𝒬` takes its graphs of scaling order `≤ n` ([II, (6.1)–(6.3)]): in
`Σ_x Θ^{(n)}_{a x} 𝒢_{x, b₁ b₂}` with `Θ^{(n)} = Σ_k (Θ Σ̃^{(n)})^k Θ`, the `Θ` edge at `⊗` of every
graph of `R_IT^{(n)}` and `Q_IT^{(n)}` stays plain or becomes the labelled edge of a label of
order `≤ n`. `A` and `Err` are empty. -/
def TEqRec.solveLow (n : ℕ) (𝒬 : TEqRec) : TRec where
  R := 𝒬.R.flatMap fun g => ([] :: chainLabels n).map fun o => ⟨g.1, g.2.relabelRoot o⟩
  A := []
  Q := 𝒬.Q.flatMap fun g => ([] :: chainLabels n).map fun o => ⟨g.1, g.2.relabelRoot o⟩
  Err := []

/-- The record of the `n`-th order `T`-expansion obtained by solving the `T`-equation `𝒬`
([II, (6.1)–(6.3)]), with `R`, `Q` as in `TEqRec.solveLow` (the `Θ` edge at `⊗` plain or labelled
by a label of order `≤ n`) and `A` of `𝒬` kept. -/
def TEqRec.solvePM (n : ℕ) (𝒬 : TEqRec) : TRec := { 𝒬.solveLow n with A := 𝒬.A }

/-- The second order `T`-expansion: `R = 0`, `A` the `O_dot` normal forms of the two graphs of
[I, (2.8)], `Q` the `O_dot` normal forms of the four graphs of [I, (2.9)], `Err = 0`. -/
def h2Rec : TRec where
  R := []
  A := ((secondOrderExp.drop 1).take 2).flatMap fun g => oDot g.2
  Q := (secondOrderExp.drop 3).flatMap fun g => oDot g.2
  Err := []

/-- The second order `T`-expansion as a second order `T`-equation: `Σ_2 = 0`, so that
`Σ̃^{(2)} = 0`, and the formal sums of `h2Rec`. -/
def h2TEq : TEqRec := ⟨[], h2Rec.R, h2Rec.A, h2Rec.Q, h2Rec.Err⟩

/-- The families of `H(n)` for `Sig` and the construction `Strat` ([II, Theorem 3.7,
Corollary 3.8] up to order `n`, [II, §6.4]): the `k`-th order `T`-equations `𝒬 k D` and
`T`-expansions `𝒯 k D` with `D`-th order error, `2 ≤ k ≤ n`, `k < D`, such that
* `𝒬 k D` is a `T`-equation and `𝒯 k D` a `T`-expansion over `Sig`, the graphs of order `≤ k`
  of `R` and `Q` of `𝒯 k D` are those of the solved `T`-equation `𝒬 k D`, and the graphs of
  order `≤ k + 1` of `R`, `A`, `Q` of `𝒯 k D` in which `⊕`, `⊖` lie in one dotted block are
  those of the solved record `(𝒬 k D).solvePM k`;
* `Σ_k` of `𝒬 k D` is `Sig k` for `k ≥ 3`, for every `D`;
* the graphs of order `≤ k` of `R` and `Q` of the `T`-equations and of the `T`-expansions do not
  depend on the order ([II, Def 3.3 (1)], [II, (6.9)]; [II, Def 3.2 (7)]), and the graphs of
  order `≤ k + 1` of `R`, `A`, `Q` of the `T`-expansions in which `⊕`, `⊖` lie in one dotted
  block do not depend on the order `k' ≥ k`;
* the graphs of order `≤ D` do not depend on the error order `D' ≥ D`;
* the second order `T`-equation is that of [I, Lemma 2.5], and for `3 ≤ k ≤ n` the `k`-th order
  `T`-equation with error order `D` is `Strat k D` applied to the `(k - 1)`-th order
  `T`-expansion with error order `D` ([II, (6.8)–(6.9)]). -/
def HFam (Strat : ℕ → ℕ → TRec → TEqRec) (Sig : ℕ → Expansion 2) (n : ℕ)
    (𝒬 : ℕ → ℕ → TEqRec) (𝒯 : ℕ → ℕ → TRec) : Prop :=
  (∀ k D, 2 ≤ k → k ≤ n → k < D →
    (𝒬 k D).IsTEqStruct Sig k D ∧ (𝒯 k D).IsTExpStruct Sig k D ∧
      TRec.Coherent k ((𝒬 k D).solveLow k) (𝒯 k D) ∧
      TRec.CoherentPM (k + 1) (𝒯 k D) ((𝒬 k D).solvePM k)) ∧
  (∀ k D, 3 ≤ k → k ≤ n → k < D → (𝒬 k D).SigN = Sig k) ∧
  (∀ k k' D, 2 ≤ k → k ≤ k' → k' ≤ n → k' < D →
    TRec.Coherent k (𝒬 k D).toTRec (𝒬 k' D).toTRec ∧ TRec.Coherent k (𝒯 k D) (𝒯 k' D) ∧
      TRec.CoherentPM (k + 1) (𝒯 k D) (𝒯 k' D)) ∧
  (∀ k D D', 2 ≤ k → k ≤ n → k < D → D ≤ D' →
    (𝒬 k D).toTRec.AgreeTo D (𝒬 k D').toTRec ∧ (𝒯 k D).AgreeTo D (𝒯 k D')) ∧
  (∀ D, 2 ≤ n → 2 < D → 𝒬 2 D = h2TEq) ∧
  (∀ k D, 3 ≤ k → k ≤ n → k < D → 𝒬 k D = Strat k D (𝒯 (k - 1) D))

/-- The structural part of `H(n)` for the family `Sig` and the construction `Strat`: families of
`T`-equations and `T`-expansions of the orders `2 ≤ k ≤ n` for every error order `D`, as in
`HFam`. -/
def HStructWith (Strat : ℕ → ℕ → TRec → TEqRec) (Sig : ℕ → Expansion 2) (n : ℕ) : Prop :=
  ∃ (𝒬 : ℕ → ℕ → TEqRec) (𝒯 : ℕ → ℕ → TRec), HFam Strat Sig n 𝒬 𝒯

/-- `H(n)` for the family `Sig` and the construction `Strat`: `Sig k` is a self-energy for every
even `4 ≤ k ≤ n`, and the structural part holds. It reads only `Sig 4, …, Sig n`. -/
def HWith (d : ℕ) (Svar : VarFamily d) (Strat : ℕ → ℕ → TRec → TEqRec)
    (Sig : ℕ → Expansion 2) (n : ℕ) : Prop :=
  SelfEnergiesUpTo d Svar Sig n ∧ HStructWith Strat Sig n

/-- **[II, Theorem 3.7] = [I, Lemma 5.7]** in the parallel form ([II, (6.8)–(6.9)]): there is a
construction `Strat` (the `T`-equation of order `n` with error order `D` built by
[II, Strategy 6.6] from the `(n - 1)`-th order `T`-expansion) such that, for `n ≥ 3` and families
of `H(n - 1)` that record `Strat`, one `Σ_n = E` serves every `D > n`, the `T`-equation
`Strat n D (𝒯 (n - 1) D)` has the structure of [II, Def 3.3], [II, Def 6.3], its graphs of order
`≤ n - 1` of `R` and `Q` are those of the `(n - 1)`-th order `T`-equation ([II, (6.9)]), its
graphs of order `≤ n` of `R`, `A`, `Q` in which `⊕`, `⊖` lie in one dotted block are those of the
`(n - 1)`-th order `T`-equation, and its graphs of order `≤ D` do not depend on `D`. -/
def tEquationStmt : Prop :=
  ∃ Strat : ℕ → ℕ → TRec → TEqRec, ∀ n : ℕ, 3 ≤ n →
    ∀ (Sig : ℕ → Expansion 2) (𝒬 : ℕ → ℕ → TEqRec) (𝒯 : ℕ → ℕ → TRec),
      HFam Strat Sig (n - 1) 𝒬 𝒯 →
      ∃ E : Expansion 2, ∀ D, n < D →
        (Strat n D (𝒯 (n - 1) D)).SigN = E ∧
        (Strat n D (𝒯 (n - 1) D)).IsTEqStruct Sig n D ∧
        TRec.Coherent (n - 1) (𝒬 (n - 1) D).toTRec (Strat n D (𝒯 (n - 1) D)).toTRec ∧
        TRec.CoherentPM n (𝒬 (n - 1) D).toTRec (Strat n D (𝒯 (n - 1) D)).toTRec ∧
        ∀ D', D ≤ D' →
          (Strat n D (𝒯 (n - 1) D)).toTRec.AgreeTo D (Strat n D' (𝒯 (n - 1) D')).toTRec

/-- `Σ_n` of the `n`-th order `T`-equations is an `n`-th order self-energy ([II, Lemma 3.9] =
[I, Lemma 5.8]): from `H(n - 1)` for `Sig` and any construction `Strat`, and `n`-th order
`T`-equations over `Sig` with one `Σ_n = E` for every `D > n`. -/
def selfEnergyStepStmt (d : ℕ) (Svar : VarFamily d) : Prop :=
  ∀ (Strat : ℕ → ℕ → TRec → TEqRec) (n : ℕ), 3 ≤ n →
    ∀ (Sig : ℕ → Expansion 2) (E : Expansion 2) (𝒬n : ℕ → TEqRec),
      HWith d Svar Strat Sig (n - 1) →
      (∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d Svar Sig n D (𝒬n D)) →
      IsSelfEnergy d Svar (Function.update Sig n E) n

/-- Solving the `T`-equation ([II, Corollary 3.8] = [I, Lemma 5.13], [II, (6.1)–(6.3)]): from
`n`-th order `T`-equations over `Sig` for every `D > n`, with one `Σ_n = E` that is an `n`-th order
self-energy and with graphs of order `≤ D` independent of `D`, `n`-th order `T`-expansions over
`Sig` with `Σ_n = E` in place, whose graphs of order `≤ n` of `R` and `Q` are those of the solved
`T`-equation, whose graphs of order `≤ n + 1` of `R`, `A`, `Q` in which `⊕`, `⊖` lie in one dotted
block are those of the solved record `(𝒬n D).solvePM n`, and whose graphs of order `≤ D` do not
depend on `D`. -/
def solveStmt (d : ℕ) (Svar : VarFamily d) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (E : Expansion 2) (𝒬n : ℕ → TEqRec),
    (∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d Svar Sig n D (𝒬n D)) →
    (∀ D D', n < D → D ≤ D' → (𝒬n D).toTRec.AgreeTo D (𝒬n D').toTRec) →
    IsSelfEnergy d Svar (Function.update Sig n E) n →
    ∃ 𝒯n : ℕ → TRec, ∀ D, n < D →
      IsTExpansion d Svar (Function.update Sig n E) n D (𝒯n D) ∧
      TRec.Coherent n ((𝒬n D).solveLow n) (𝒯n D) ∧
      TRec.CoherentPM (n + 1) (𝒯n D) ((𝒬n D).solvePM n) ∧
      ∀ D', D ≤ D' → (𝒯n D).AgreeTo D (𝒯n D')

/-- The induction step `H(n - 1) ⇒ H(n)` for the construction `Strat` ([II, Theorem 3.7,
Corollary 3.8, Lemma 3.9]), with the new self-energy added to the same family. -/
def inductionStepStmt (d : ℕ) (Svar : VarFamily d) (Strat : ℕ → ℕ → TRec → TEqRec) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ Sig : ℕ → Expansion 2, HWith d Svar Strat Sig (n - 1) →
    ∃ E : Expansion 2, HWith d Svar Strat (Function.update Sig n E) n

/-- One family of self-energies for all orders and the construction `Strat`: `H(n)` for every
`n ≥ 2`. -/
def jointHStmt (d : ℕ) (Svar : VarFamily d) (Strat : ℕ → ℕ → TRec → TEqRec) : Prop :=
  ∃ Sig : ℕ → Expansion 2, ∀ n : ℕ, 2 ≤ n → HWith d Svar Strat Sig n

/-- The matrix of order `l` in the self-energy matrices of order `N > l` is `Σ_l`: entry `l` of
`sigUpTo` is fixed at step `l` and never overwritten. -/
theorem sigUpTo_eq_sigMat :
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Sig : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ)
    (l N : ℕ), l < N → sigUpTo Sig S z N l = sigMat Sig S z l := by
  intro ι _ _ Sig S z l N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with hl | rfl
    · simp only [sigUpTo]
      rw [Function.update_of_ne (by omega)]
      exact ih hl
    · simp only [sigUpTo, sigMat, Function.update_self]

/-- The zero formal sum is a self-energy of every order `l` ([II, (2.6)]). -/
theorem isSelfEnergy_nil :
  ∀ (d : ℕ) (Svar : VarFamily d)
    (Sig : ℕ → Expansion 2) (l : ℕ), Sig l = [] → IsSelfEnergy d Svar Sig l := by
  intro d Svar Sig l hl
  have h0 : ∀ (W L : ℕ) [NeZero L] (z : ℂ), sigMat Sig (Svar W L) z l = 0 := by
    intro W L _ z
    ext x y
    simp [sigMat, hl, Expansion.val]
  refine ⟨fun g hg => by simp [hl] at hg, ?_, ?_⟩
  · intro W L _ z _ x a
    simp [h0]
  · intro κ ε c₀ c₁ _ _ _ _ _ τ _
    refine ⟨0, fun W L _ _ _ z hz => ?_⟩
    have him : 0 ≤ z.im := le_trans (by
      have : (0:ℝ) ≤ (L : ℝ) ^ (2 - ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity) hz.2.1
    refine ⟨fun x => ?_, ?_⟩
    · simp only [h0, Matrix.zero_apply, norm_zero]
      have : (0:ℝ) ≤ (L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have : (0:ℝ) ≤ (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have : (0:ℝ) ≤ (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have : (0:ℝ) ≤ if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0 := by
        split_ifs <;> positivity
      positivity
    · simp only [h0, Matrix.zero_apply, Finset.sum_const_zero, norm_zero]
      have : (0:ℝ) ≤ (L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have : (0:ℝ) ≤ (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity

section Instances

/-- Adjacency in the graph of all components is decidable. -/
instance instDecAdjEdgeGraph {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.edgeGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.x = u ∧ c.y = v) ∨ (∃ c ∈ Γ.comps, c.x = v ∧ c.y = u))))

/-- Adjacency in the graph of waved and diffusive components is decidable. -/
instance instDecAdjWavedTheta {k n : ℕ} (Γ : Graph k n) :
    DecidableRel Γ.wavedThetaGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = v ∧ c.y = u))))

/-- Adjacency in the graph of waved and dotted components is decidable. -/
instance instDecAdjMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.molGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = v ∧ c.y = u))))

/-- Being in one molecule is decidable. -/
instance instDecSameMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameMol :=
  fun u v =>
    haveI : Decidable (Γ.molGraph.Reachable u v) :=
      @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjMol Γ) u v
    inferInstanceAs (Decidable (u = v ∨
      (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)))

/-- Adjacency in a net is decidable. -/
instance instDecAdjNet {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) :
    DecidableRel (Γ.net B).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧
    ((Γ.SameMol (.inr a) (.inr b) ∨ ∃ i ∈ B, Γ.comps[i].x = .inr a ∧ Γ.comps[i].y = .inr b) ∨
      (Γ.SameMol (.inr b) (.inr a) ∨ ∃ i ∈ B, Γ.comps[i].x = .inr b ∧ Γ.comps[i].y = .inr a))))

/-- Regularity with a given bound is decidable. -/
instance instDecRegular {k n : ℕ} (C : ℕ) (Γ : Graph k n) : Decidable (Γ.Regular C) :=
  haveI : DecidableRel Γ.edgeGraph.Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjEdgeGraph Γ)
  haveI : DecidableRel Γ.wavedThetaGraph.Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjWavedTheta Γ)
  haveI : Decidable Γ.edgeGraph.Preconnected :=
    inferInstanceAs (Decidable (∀ u v, Γ.edgeGraph.Reachable u v))
  decidable_of_iff (k + n + Γ.comps.length ≤ C ∧ Γ.edgeGraph.Preconnected ∧
      (∀ a b : Fin n, Γ.wavedThetaGraph.Reachable (.inr a) (.inr b)) ∧
      ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

set_option synthInstance.maxSize 1024 in
/-- Normal regularity with a given bound is decidable. -/
instance instDecNormal {k n : ℕ} (C : ℕ) (Γ : Graph k n) : Decidable (Γ.Normal C) :=
  inferInstanceAs (Decidable (Γ.Regular C ∧ (∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) ∧
    ∀ u v : Atom k n, u ≠ v →
      ((∃ c ∈ Γ.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)))))

/-- Spanning the internal molecules is decidable. -/
instance instDecSpans {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) :
    Decidable (Γ.Spans B) :=
  haveI : DecidableRel (Γ.net B).Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjNet Γ B)
  inferInstanceAs (Decidable (∀ a b, (Γ.net B).Reachable a b))

end Instances

end RBM8D.Graphs
