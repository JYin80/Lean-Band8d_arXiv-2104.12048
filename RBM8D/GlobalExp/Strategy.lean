import RBM8D.GlobalExp.Local
import RBM8D.Graph.QExp.Main
import RBM8D.Graph.QExp.Clauses
import RBM8D.Graph.QExp.FlatSchur
import RBM8D.Graph.QExp.FlatSplit
import RBM8D.Graph.Local.Strategy
import RBM8D.TExp.Second
import RBM8D.Graph.Local.DotNorm
import RBM8D.Graph.Local.SolidMono

/-!
# The global expansion strategy in the block reading: definitions and statements

[II, Strategy 6.6] and [II, Lemmas 6.5, 6.7, 6.8] in the block reading of the dotted edges at
`⊗`, `⊕`, `⊖` (`Graph.toMG'`, `Graph.InvB'`, `Graph.ExtClause`), with the scaling orders of the
order tests, of the invariant and of the measure of a run read in the count of [II, (2.5)]
(`Graph.paperOrd`, equal to `Graph.ord` on graphs of dot excess `0`):

* the statements of [II, Lemmas 5.10, 5.13, 6.4] and of the clause on `⊗` of the `Q`-expansions
  of [II, Lemma 4.15] in this reading, which enter as hypotheses;
* the clause of Step 3 on a `Q`-expansion (`qexpClauseB`), the clause on the external atoms kept
  by the local expansions and by the substitution;
* the minimal isolated subset, the `t`-variable of Step 2, the stopping rules (S1)–(S4) and the
  outputs read on `Graph.toMG'`; the clauses on dotted edges (`Graph.DotFree`,
  `Graph.NoLabDot`, `Graph.RgCheck`); the invariant of a run (`Graph.InvRun`), with the clause
  that every component at `⊗` is a diffusive edge (`Graph.TensorDiffusive`);
* the steps and runs (`StrategyStepB`, `GlobalRunB`), the value identity of a run;
* the scaling order of the `O_dot` forms of a substituted graph (`glue_oDotT_normalStmt`): it
  drops by `2` exactly when `y₁ = y₂` and `⊕`, `⊖` lie in one block of the substituted graph
  (`Graph.PMBlock`); the light weights and the solid edges of the local expansions at equal order;
  the measure of a run (`runMu`) and its descent along Step 1 and along Steps 2–3;
* the rooting of a graph at the external atoms (`Graph.RootedAtExt`) from the clause on the
  external atoms, the charge pattern of the block normal form and [II, Def 3.2 (9)];
* [II, Def 6.3] with the clauses on dotted edges, labels, orders and rooting read by the
  substitution and by [II, (8.18)–(8.24)] (`TRec.Def63`);
* the invariant kept by every step, [II, Lemma 6.7], [II, Lemma 6.5] (on the `O_dot` forms of the
  substituted graphs) and [II, Lemma 6.8] with the output classes of [II, Def 6.3];
* the step `xdotLoop` on a host of Steps 2–3 with a `×`-dotted loop at its new internal atom.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The clauses of Step 3 and of the external atoms along a run -/

/-- The clause of Step 3 of [II, Strategy 6.6] on a `Q`-expansion `E` of `Γ` at `x`: the clauses
`qExpansionOut'` for some bound, and the invariant `Graph.InvB'` passed to every output graph. -/
def qexpClauseB {n₀ : ℕ} (D : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀) (E : TExpansion 3 n₀) : Prop :=
  (∃ C', ∀ t ∈ E, qExpansionOut' D C' (.inr x) Γ t) ∧ (Γ.InvB' → ∀ t ∈ E, t.g.InvB')

/-- The substitution of Steps 2–3 of [II, Strategy 6.6] at internal atoms `x`, `y₁`, `y₂` keeps
the clause on the external atoms, for every substituted formal sum. -/
def globalSubst_extClauseStmt : Prop :=
  ∀ (m : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (F : Expansion 3),
    x.isRight = true → y₁.isRight = true → y₂.isRight = true →
    (H.glue x y₁ y₂ (tVar true)).ExtClause → ∀ g ∈ H.globalSubst x y₁ y₂ F, g.2.ExtClause

/-! ## The objects of [II, Strategy 6.6] read on `Graph.toMG'` -/

/-- No dotted edge. -/
def Graph.DotFree {k n : ℕ} (Γ : Graph k n) : Prop := ∀ c ∈ Γ.comps, c.kind ≠ .dot

/-- No dotted edge at `⊗` (the part of `Graph.TensorDiffusive` on dotted edges). -/
def Graph.OtimesNoDot {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind ≠ .dot

/-- The minimal isolated subset of `Graph.toMG'` is locally standard ([II, Strategy 6.6, Step 1]):
no labels; no weight on the atoms of its molecules; each of these atoms has degree `0` or is
standard neutral. -/
def Graph.MISLocStdB {k n : ℕ} (Γ : Graph k n) : Prop :=
  Γ.LabelFree ∧ ∀ i : Fin n, Γ.molRep (.inr i) ∈ Γ.toMG'.MIS →
    Γ.wt (.inr i) = 0 ∧
      (Γ.deg (.inr i) = 0 ∨ (Γ.deg (.inr i) = 2 ∧ Γ.stdNeutralAt (.inr i) = true))

/-- The component `i` is a blue solid edge of the minimal isolated subset of `Graph.toMG'` that
Step 2 of [II, Strategy 6.6] may expand: both atoms in molecules of the minimal isolated subset,
and either inside one molecule, or the first edge of a pre-deterministic order of the subgraph of
`Graph.toMG'` induced on the minimal isolated subset. -/
def Graph.Step2EdgeB {k n : ℕ} (Γ : Graph k n) (i : Fin Γ.comps.length) : Prop :=
  Γ.comps[i].kind = .G .plus ∧ Γ.molRep Γ.comps[i].x ∈ Γ.toMG'.MIS ∧
    Γ.molRep Γ.comps[i].y ∈ Γ.toMG'.MIS ∧
    (Γ.SameMol Γ.comps[i].x Γ.comps[i].y ∨
      ∃ l, (Γ.toMG'.induce Γ.toMG'.MIS).IsPDOrder l ∧ l.head? = some (.inl i))

/-- The `t`-variable chosen in Step 2 of [II, Strategy 6.6]: the component `i` is a blue solid edge
`G_{y₁α}` that Step 2 may expand (`Graph.Step2EdgeB`), and the red solid edges `Ḡ_{y₂α}` ending
at its second atom `α` and the waved edges `s` at `α` join internal atoms. The `t`-variable is
then `t_{y₁y₂,x} = |m|² ∑_α G_{y₁α} Ḡ_{y₂α} s_{αx}` of [II, (4.14)] with `x`, `y₁`, `y₂`
internal. -/
def Graph.Step2EdgeB' {k n : ℕ} (Γ : Graph k n) (i : Fin Γ.comps.length) : Prop :=
  Γ.Step2EdgeB i ∧
    ∀ c ∈ Γ.comps, (c.kind = .G .minus ∧ c.y = Γ.comps[i].y ∨
        c.kind = .waved .s ∧ (c.x = Γ.comps[i].y ∨ c.y = Γ.comps[i].y)) →
      c.x.isRight = true ∧ c.y.isRight = true

/-- In a graph with the charge pattern `Graph.ColourInv'`, every blue solid edge that Step 2 may
expand gives the `t`-variable `t_{y₁y₂,x}` at its second atom. -/
def step2EdgeB'_of_colourInvStmt : Prop :=
  ∀ (n : ℕ) (Γ : Graph 3 n) (i : Fin Γ.comps.length), Γ.ColourInv' → Γ.Step2EdgeB i →
    Γ.Step2EdgeB' i

/-- For the `t`-variable `t_{y₁y₂,x}` chosen in Step 2 at the last atom of a graph
`H.glue x y₁ y₂ (tVar true)`, the atoms `x`, `y₁`, `y₂` are internal. -/
def step2EdgeB'_internalStmt : Prop :=
  ∀ (m : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m),
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    x.isRight = true ∧ y₁.isRight = true ∧ y₂.isRight = true

open Classical in
/-- Non-expandable graphs ((S4) of [II, §6.3]) read on `Graph.toMG'`: locally standard, with no
redundant blue solid edge between two internal molecules. -/
def Graph.NonExpandableB {k n : ℕ} (Γ : Graph k n) : Prop :=
  Γ.LocallyStandard ∧ ∀ e, Γ.toMG'.IsIntPlus e → ¬ Γ.toMG'.IsRedundant e

/-- The stopping rules (S1)–(S4) of [II, §6.3] at the cutoff order `n`, read on `Graph.toMG'`: a
normal regular graph that is a `⊕/⊖`-recollision graph, has scaling order `≥ n + 1`, is a
`Q`-graph, or is non-expandable. -/
def Graph.StopsB {n₀ : ℕ} (n : ℕ) (Γ : Graph 3 n₀) : Prop :=
  (∃ C, Γ.Normal C) ∧
    (Γ.IsRecollision {1, 2} ∨ (n : ℤ) + 1 ≤ Γ.ord ∨ Γ.IsQGraph ∨ Γ.NonExpandableB)

/-- The output graphs of [II, Strategy 6.6], read on `Graph.toMG'`: graphs of dot excess `0` (the
dotted edges form a forest without loops) that are stopped by (S1)–(S4), normal regular of
scaling order `> D`, or with a locally standard minimal isolated subset and no blue solid edge for
Step 2. -/
def Graph.StratLeafB {n₀ : ℕ} (n D : ℕ) (Γ : Graph 3 n₀) : Prop :=
  Γ.dotExcess = 0 ∧
    (Γ.StopsB n ∨ ((∃ C, Γ.Normal C) ∧ (D : ℤ) < Γ.ord) ∨ (Γ.MISLocStdB ∧ ∀ i, ¬ Γ.Step2EdgeB i))

/-- The maximal subgraph is deterministic: every solid edge and every weight has an external
atom. -/
def Graph.MaxDeterministic {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, c.kind.isRandom = true → c.x.isLeft = true ∨ c.y.isLeft = true

/-- `Γ'` is `Γ` with its internal atoms renumbered by a permutation, its components listed in
another order, and the two atoms of some waved edges `s`, dotted and `×`-dotted edges exchanged;
the coefficient is the same. -/
def Graph.Reorder {k n : ℕ} (Γ Γ' : Graph k n) : Prop :=
  Γ'.coeff = Γ.coeff ∧ ∃ (π : Equiv.Perm (Fin n)) (cs : List (Comp (Atom k n))),
    List.Forall₂ (fun c c' => c' = c ∨
        ((c.kind = .waved .s ∨ c.kind = .dot ∨ c.kind = .xdot) ∧
          c' = { c with x := c.y, y := c.x }))
      (Γ.relabel π).comps cs ∧ cs.Perm Γ'.comps

/-- A reordered graph has the same value under the model relations (`s` is symmetric). -/
def reorder_valueStmt : Prop :=
  ∀ (k n : ℕ) (Γ Γ' : Graph k n), Γ.Reorder Γ' →
    ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
      modelAdm Ω ι PF D → ∀ e : Fin k → ι, Γ'.valR PF D e = Γ.valR PF D e

/-- The invariant of a run of [II, Strategy 6.6] at error order `D`: the invariant `Graph.InvB'`
of [II, Lemma 5.13] in the block reading together with `Graph.TensorDiffusive` (only diffusive
edges at `⊗`); or a `Q`-graph without internal atom (the `O_dot` forms of
`m Θ_{⊗⊕} Q_⊕(Ḡ_{⊕⊖})` of [I, (2.9)]); or scaling order `> D` in the count of [II, (2.5)], with
the clause on the external atoms, the charge pattern of the block normal form, only diffusive
edges at `⊗`, and every `O_dot` form normal regular of scaling order `> D` in that count (the
graphs of [II, Lemma 6.5 (5)]). -/
def Graph.InvRun {n : ℕ} (D : ℕ) (Γ : Graph 3 n) : Prop :=
  (Γ.InvB' ∧ Γ.TensorDiffusive) ∨ (n = 0 ∧ Γ.IsQGraph) ∨
    ((D : ℤ) < Γ.paperOrd ∧ Γ.ExtClause ∧ Γ.ColourInvB ∧ Γ.TensorDiffusive ∧
      ∀ t ∈ oDotT Γ, (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C)

/-! ## Steps and runs of [II, Strategy 6.6] in the block reading -/

/-- One step of [II, Strategy 6.6] at the cutoff order `n` and error order `D`, with the
`T`-expansion `𝒯` of order `n - 1`; the minimal isolated subset is that of `Graph.toMG'`:
* Step 1 (`loc`): a local expansion `localOp'` in the form of `Graph.LocSide`, at an internal
  atom of the minimal isolated subset of a normal regular, globally standard graph without labels
  of scaling order `≤ D` that is not stopped;
* `O_dot` (normal regular form), on every graph;
* the removal of a redundant dotted edge (`DotNormStep`, the step `dropDot` of
  [I, Strategy 3.21]) from a normal regular plain graph (its dotted edges carry no label);
* a reordering of the atoms and components (`Graph.Reorder`);
* the duplication of a `×`-dotted edge between two internal atoms (`xdotDup`), a step that keeps
  the value because `1_{u ≠ v}² = 1_{u ≠ v}`: the `t`-variable of [II, (4.14)] has the factors
  `1_{α ≠ y₁}` and `1_{α ≠ y₂}`, which are one factor at `y₁ = y₂`;
* the removal of one of two parallel `×`-dotted edges between two internal atoms (`xdotDrop`), the
  converse of `xdotDup`, which keeps the value for the same reason: one copy stays;
* the empty formal sum for a graph with a `×`-dotted loop (`xdotLoop`): the factor `1_{u ≠ v}` of
  a `×`-dotted edge is `0` at `u = v`, so the graph has value `0`; the `t`-variable of [II, (4.14)]
  has the indicators `1_{α ≠ y₁}` and `1_{α ≠ y₂}`, and `1_{α ≠ α}` does not occur there;
* the identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1` in the coefficient (`coeffNorm`): the ring `Coeff`
  has the generators `m`, `m⁻¹`, `r`, `m̄`, `m̄⁻¹`, `r̄` freely, and the factors are `1` at the
  value `m = m_sc(z) ≠ 0` of the model;
* Steps 2–3 (`subst`): for a normal regular, globally standard graph `H.glue x y₁ y₂ (tVar true)`
  without dotted edges, of scaling order between `4` and `n` (and `≤ D`), not a
  `⊕/⊖`-recollision graph, with only diffusive edges at `⊗`, a locally standard minimal isolated
  subset and the blue solid edge `G_{y₁α}` chosen by Step 2 (`Graph.Step2EdgeB'`), the
  substitution of the right side of [II, (4.15)] with all `G` entries transposed;
* Step 3 (`qexp`): a `Q`-expansion of a graph `Γ₀ Q_x(Γ̃₀)` of scaling order `≤ D` that is not a
  `Q`-graph, with the clause `qexpClauseB`. -/
inductive StrategyStepB (n D : ℕ) (𝒯 : TRec) : (Σ n₀ : ℕ, Graph 3 n₀) → Expansion 3 → Prop
  | loc {n₀ : ℕ} (Γ : Graph 3 n₀) (o : Fin 5) (x : Fin n₀) (C : ℕ) :
      ¬ Γ.StopsB n → ¬ (D : ℤ) < Γ.ord → Γ.Normal C → Γ.LabelFree → Γ.Plain → gsPM' Γ →
      Γ.molRep (.inr x) ∈ Γ.toMG'.MIS → Γ.LocSide o (.inr x) →
      StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ (localOp' o (.inr x) Γ).forget
  | dot {n₀ : ℕ} (Γ : Graph 3 n₀) : StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ (oDot Γ)
  | dropDot {n₀ : ℕ} (Γ Γ' : Graph 3 n₀) (C : ℕ) :
      DotNormStep Γ Γ' → Γ.Normal C → Γ.Plain → StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ [⟨n₀, Γ'⟩]
  | reorder {n₀ : ℕ} (Γ Γ' : Graph 3 n₀) : Γ.Reorder Γ' → StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ [⟨n₀, Γ'⟩]
  | xdotDup {n₀ : ℕ} (Γ : Graph 3 n₀) (i : Fin Γ.comps.length) :
      Γ.comps[i].kind = .xdot → Γ.comps[i].x.isRight = true → Γ.comps[i].y.isRight = true →
      StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ [⟨n₀, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩]
  | xdotDrop {n₀ : ℕ} (Γ : Graph 3 n₀) (i j : Fin Γ.comps.length) :
      i ≠ j → (Γ.comps[j] = Γ.comps[i] ∨
        Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x }) →
      Γ.comps[i].kind = .xdot → Γ.comps[i].x.isRight = true → Γ.comps[i].y.isRight = true →
      StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ [⟨n₀, ⟨Γ.comps.eraseIdx j, Γ.coeff⟩⟩]
  | xdotLoop {n₀ : ℕ} (Γ : Graph 3 n₀) (i : Fin Γ.comps.length) :
      Γ.comps[i].kind = .xdot → Γ.comps[i].x = Γ.comps[i].y →
      StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ []
  | coeffNorm {n₀ : ℕ} (Γ : Graph 3 n₀) :
      StrategyStepB n D 𝒯 ⟨n₀, Γ⟩
        [⟨n₀, ⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩⟩]
  | subst {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (C : ℕ) :
      ¬ (D : ℤ) < (H.glue x y₁ y₂ (tVar true)).ord → 4 ≤ (H.glue x y₁ y₂ (tVar true)).ord →
      (H.glue x y₁ y₂ (tVar true)).ord ≤ n → (H.glue x y₁ y₂ (tVar true)).Normal C →
      (H.glue x y₁ y₂ (tVar true)).DotFree →
      H.LabelFree → gsPM' (H.glue x y₁ y₂ (tVar true)) →
      ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
      (H.glue x y₁ y₂ (tVar true)).TensorDiffusive → (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
      (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
        (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
      StrategyStepB n D 𝒯 ⟨m + 1, H.glue x y₁ y₂ (tVar true)⟩
        (H.globalSubst x y₁ y₂ (𝒯.tSubst (n - 1)).swapSolid)
  | qexp {n₀ : ℕ} (Γ : Graph 3 n₀) (x : Fin n₀) (E : TExpansion 3 n₀) :
      ¬ (D : ℤ) < Γ.ord → Γ.IsQFormAt (.inr x) → ¬ Γ.IsQGraph → E.ValueEq Γ modelAdm →
      qexpClauseB D x Γ E → StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ E.forget

/-- A run of [II, Strategy 6.6] with the steps `StrategyStepB`: each graph is an output
(`Graph.StratLeafB`) or is replaced by the formal sum of one step, until only outputs are left.
`GlobalRunB n D 𝒯 E F` says that the run from `E` ends with the outputs `F`. -/
inductive GlobalRunB (n D : ℕ) (𝒯 : TRec) : Expansion 3 → Expansion 3 → Prop
  | nil : GlobalRunB n D 𝒯 [] []
  | out {g : Σ n₀ : ℕ, Graph 3 n₀} {E F : Expansion 3} :
      g.2.StratLeafB n D → GlobalRunB n D 𝒯 E F → GlobalRunB n D 𝒯 (g :: E) (g :: F)
  | step {g : Σ n₀ : ℕ, Graph 3 n₀} {E E₁ F : Expansion 3} :
      StrategyStepB n D 𝒯 g E₁ → GlobalRunB n D 𝒯 (E₁ ++ E) F → GlobalRunB n D 𝒯 (g :: E) F

/-- A run keeps values: with a `T`-expansion `𝒯` of order `n - 1` over `Sig` whose self-energies
have the shape of [II, Def 2.7 (i)] and whose graphs have at most one label, the inputs and the
outputs of a run have the same value, given the value identity of `Graph.Reorder`. -/
def globalRun_valueStmtB : Prop :=
  reorder_valueStmt →
  ∀ (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒯 : TRec), 1 ≤ n → 𝒯.Identity Sig (n - 1) →
    SelfEnergyShapesUpTo Sig (n - 1) →
    (∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, g.2.labels.length ≤ 1) →
    ∀ E F, GlobalRunB n D 𝒯 E F →
      ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (Dt : Ω → Data ι),
        modelAdm Ω ι PF Dt → (∀ ω, SigConsistent Sig n (Dt ω)) → ∀ e : Fin 3 → ι,
          E.valR PF Dt e = F.valR PF Dt e

/-! ## The order of the substituted graphs, the solid edges and the measure of a run -/

/-- **The scaling order of the `O_dot` forms of a substituted graph** ([II, Lemma 6.5],
[II, (2.5)], [II, Def 4.2]): let `H.glue x y₁ y₂ (tVar true)` be normal regular without dotted
edges, with `x`, `y₁`, `y₂` internal and `H` without labels, and let `g` be normal regular with
no dotted edge at `⊗`, dot excess `0`, the clause `Graph.RgCheck`, at most one label and no
labelled dotted or `×`-dotted edge. Every `O_dot` form `t` of `H.glue x y₁ y₂ g` is normal regular
without dotted edges; its scaling order is that of `H.glue x y₁ y₂ g` minus `2` if `y₁ = y₂` and
`⊕`, `⊖` lie in one block of `g` (two dotted edges from one internal atom of `g` to the same atom
`y₁`), and equal to it otherwise; and `t` is doubly connected if `H.glue x y₁ y₂ g` is. -/
def glue_oDotT_normalStmt : Prop :=
  ∀ (m n' C C' : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n'),
    x.isRight = true → y₁.isRight = true → y₂.isRight = true → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    g.Normal C' → g.OtimesNoDot → g.dotExcess = 0 → g.RgCheck → g.labels.length ≤ 1 →
    g.NoLabDot →
    ∀ t ∈ oDotT (H.glue x y₁ y₂ g), (∃ C'', t.g.Normal C'') ∧ t.g.DotFree ∧
      ((y₁ = y₂ ∧ g.PMBlock) → t.g.ord + 2 = (H.glue x y₁ y₂ g).ord) ∧
      (¬ (y₁ = y₂ ∧ g.PMBlock) → t.g.ord = (H.glue x y₁ y₂ g).ord) ∧
      ((H.glue x y₁ y₂ g).DoublyConnected → t.g.DoublyConnected)

/-- The measure of a run of [II, Strategy 6.6] at the cutoff order `n` ([II, Lemma 6.8]),
compared lexicographically: the missing order `n + 1 - Graph.paperOrd`, the number of light
weights, the number of solid edges, then `(mfl, eextN, phi)` of the descent of
[I, Strategy 3.21], and last the dot excess. It is read on macro steps, from the input to every
output without labels: a local expansion of Step 1 (`locMuStmt`), the removal of one redundant
dotted edge (`dotNormStep_muStmt`), and a substitution of Steps 2–3 followed by `O_dot` and, on
the `O_dot` forms of a substituted `Q`-graph, by a `Q`-expansion (`substMuStmt`). A reordering,
and `O_dot` on a normal regular graph, keep it. -/
def runMu (n : ℕ) {k n₀ : ℕ} (Γ : Graph k n₀) :
    ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))))) :=
  toLex (((n : ℤ) + 1 - Γ.paperOrd).toNat,
    toLex (Γ.lwN, toLex (Γ.solidN, toLex (Γ.mfl, toLex (Γ.eextN, toLex (Γ.phi,
      Γ.dotExcess.toNat))))))

/-- The local expansion `localOp' o` applies at `x` (the inputs of [I, Lemmas 3.9, 3.13, 3.16,
3.19] in [II, Strategy 6.6, Step 1]): `O_weight` at an atom with a weight; `O_multi-e` at an
atom without weight of degree `≥ 1` that has degree `≥ 3` or is neither standard neutral nor of
the `GG` shape; `O_GG` and the transposed `O_GG` at an atom without weight of the `GG` shape;
`O_GḠ` at an atom without weight of the `GḠ` shape that has degree `≥ 3` or is neither standard
neutral nor of the `GG` shape. -/
def Graph.LocAdm {k n : ℕ} (o : Fin 5) (x : Atom k n) (Γ : Graph k n) : Prop :=
  (o = 0 ∧ 0 < Γ.wt x) ∨
    (o = 1 ∧ Γ.wt x = 0 ∧ 1 ≤ Γ.deg x ∧
      (3 ≤ Γ.deg x ∨ (Γ.stdNeutralAt x = false ∧ ∀ y y', ¬ Γ.GGInputAt x y y'))) ∨
    ((o = 2 ∨ o = 4) ∧ Γ.wt x = 0 ∧ ∃ y y', Γ.GGInputAt x y y') ∨
    (o = 3 ∧ Γ.wt x = 0 ∧
      (3 ≤ Γ.deg x ∨ (Γ.stdNeutralAt x = false ∧ ∀ y y', ¬ Γ.GGInputAt x y y')) ∧
      ∃ y y', Γ.GGbarInputAt x y y')

/-- **The descent of Step 1** ([II, Lemma 6.8], [I, Strategy 3.21]): a local expansion that
applies at an internal atom of a normal regular plain graph without labels, with the invariant of
a run and no `×`-dotted edge inside a block, of scaling order `≤ D` and not stopped, lowers
`runMu n` on every output without labels (outputs of higher order lower the first coordinate;
outputs of equal order have dot excess `0` and fewer light weights, or as many light weights and
at most as many solid edges, and then a smaller `(mfl, eextN, phi)` if the solid edges are as
many). -/
def locMuStmt : Prop :=
  ∀ (n D n₀ C : ℕ) (Γ : Graph 3 n₀) (o : Fin 5) (x : Fin n₀), Γ.InvRun D → ¬ Γ.StopsB n →
    ¬ (D : ℤ) < Γ.ord → Γ.Normal C → Γ.LabelFree → Γ.Plain → Γ.XdotApart →
    Γ.LocAdm o (.inr x) → ∀ t ∈ localOp' o (.inr x) Γ, t.g.LabelFree → runMu n t.g < runMu n Γ

/-- The removal of a redundant dotted edge from a normal regular plain graph lowers `runMu n`:
it keeps the order in the count of [II, (2.5)], the light weights, the solid edges, the blocks
and the components other than dotted edges, does not raise the number of internal atoms of
degree `2` that are not standard neutral, and lowers the dot excess by `1`. -/
def dotNormStep_muStmt : Prop :=
  ∀ (n k n₀ C : ℕ) (g g' : Graph k n₀), DotNormStep g g' → g.Normal C → g.Plain →
    runMu n g' < runMu n g

/-- **The inputs of Step 1 have no dotted edge** ([II, Strategy 6.6]): a normal regular plain
graph without labels, with the invariant of a run, of scaling order `≤ D` and not stopped, has no
dotted edge (such an edge would join two internal atoms, touch `⊗`, make a `⊕/⊖`-recollision
graph, or be a loop). -/
def locInput_dotFreeStmt : Prop :=
  ∀ (n D n₀ C : ℕ) (Γ : Graph 3 n₀), Γ.InvRun D → ¬ (D : ℤ) < Γ.ord → Γ.LabelFree →
    Γ.Normal C → Γ.Plain → ¬ Γ.StopsB n → ∀ c ∈ Γ.comps, c.kind ≠ .dot

/-- Every elementary step of the `Q`-expansions maps a graph with at most one label to a graph
with at most one label ([II, §4.4]: one label group per graph, (4.16), Lemmas 4.11, 4.13,
4.14). -/
def qElemStep_labelsStmt : Prop :=
  ∀ g g' : Σ n, Graph 3 n, QElemStep g g' → g.2.labels.length ≤ 1 → g'.2.labels.length ≤ 1

/-- A reordered graph (`Graph.Reorder`) has the same order in the count of [II, (2.5)], and its
`O_dot` forms are normal regular of scaling order `> D` in that count when those of the graph
are. -/
def reorder_oDotTStmt : Prop :=
  ∀ (D n : ℕ) (Γ Γ' : Graph 3 n), Γ.Reorder Γ' → Γ'.paperOrd = Γ.paperOrd ∧
    ((∀ t ∈ oDotT Γ, (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C) →
      ∀ t ∈ oDotT Γ', (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C)

/-! ## The invariant of a run -/

/-- The local expansions of Step 1, at an internal atom of a normal regular graph without labels
with the invariant `Graph.InvB'`, only diffusive edges at `⊗` and no dotted edge from `⊕` or `⊖` to
an internal atom, give graphs with the charge pattern of the block normal form, no ghost edge,
internal label atoms and only diffusive edges at `⊗`. -/
def localOp_clausesStmtB : Prop :=
  ∀ (n₀ C : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), Γ.Normal C → Γ.LabelFree → Γ.Plain →
    Γ.InvB' → Γ.TensorDiffusive → ¬ Γ.IsRecollision {1, 2} →
    ∀ o : Fin 5, Γ.LocSide o (.inr x) → ∀ t ∈ localOp' o (.inr x) Γ,
      t.g.ColourInvB ∧ t.g.NoGhost ∧ t.g.LabelsInt ∧ t.g.TensorDiffusive

/-- `O_dot` keeps `Graph.TensorDiffusive`, and keeps the `Q`-graphs without internal atom. -/
def oDot_otimesStmt : Prop :=
  (∀ (n : ℕ) (Γ : Graph 3 n), Γ.TensorDiffusive → ∀ t ∈ oDotT Γ, t.g.TensorDiffusive) ∧
    ∀ Γ : Graph 3 0, Γ.IsQGraph → ∀ t ∈ oDotT Γ, t.nOut = 0 ∧ t.g.IsQGraph

/-- `O_dot` keeps the clause on the external atoms and the charge pattern of the block normal form
on graphs with only diffusive edges at `⊗`: it adds dotted or `×`-dotted edges only at the two
atoms of a solid edge, whose first atom is internal or pinned, and identifies internal atoms
only. -/
def oDot_extClauseStmt : Prop :=
  ∀ (n : ℕ) (Γ : Graph 3 n), Γ.ExtClause → Γ.ColourInvB → Γ.TensorDiffusive →
    ∀ t ∈ oDotT Γ, t.g.ExtClause ∧ t.g.ColourInvB

/-- The substitution of Steps 2–3 at internal atoms `x`, `y₁`, `y₂` of a graph that is not a
`⊕/⊖`-recollision graph and has only diffusive edges at `⊗`, with the clause on the external
atoms, the charge pattern of the block normal form, no ghost edge and internal label atoms, gives,
for every substituted formal sum without ghost edges, graphs with the charge pattern of the block
normal form, no ghost edge, internal label atoms and only diffusive edges at `⊗`. -/
def globalSubst_clausesStmt : Prop :=
  ∀ (m : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (F : Expansion 3),
    x.isRight = true → y₁.isRight = true → y₂.isRight = true →
    (H.glue x y₁ y₂ (tVar true)).ExtClause → (H.glue x y₁ y₂ (tVar true)).ColourInvB →
    (H.glue x y₁ y₂ (tVar true)).NoGhost → (H.glue x y₁ y₂ (tVar true)).LabelsInt →
    (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} → (∀ g ∈ F, g.2.NoGhost) →
    ∀ g ∈ H.globalSubst x y₁ y₂ F,
      g.2.ColourInvB ∧ g.2.NoGhost ∧ g.2.LabelsInt ∧ g.2.TensorDiffusive

/-- A reordered graph (`Graph.Reorder`) has the invariant of a run if the graph has it. -/
def reorder_invRunStmt : Prop :=
  ∀ (n D : ℕ) (Γ Γ' : Graph 3 n), Γ.Reorder Γ' → Γ.InvRun D → Γ'.InvRun D

/-- Every step of [II, Strategy 6.6] keeps the invariant of a run, for `n ≥ 3` and an
`(n - 1)`-th order `T`-expansion `𝒯` with error order `D` (with the clauses `TRec.Def63`). -/
def invRun_stepStmt : Prop :=
  ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
    ∀ (g : Σ n₀ : ℕ, Graph 3 n₀) (E₁ : Expansion 3), StrategyStepB n D 𝒯 g E₁ →
      g.2.InvRun D → ∀ h ∈ E₁, h.2.InvRun D

/-! ## [II, Lemmas 6.5, 6.7, 6.8] in the block reading -/

/-- **The descent of Steps 2–3** ([II, Lemma 6.8], by (1)–(5) of [II, Lemma 6.5]): under the
hypotheses of [II, Lemma 6.5], every `O_dot` form without labels of a substituted graph, and
every output without labels of a `Q`-expansion with the clause `qexpClauseB` of an `O_dot` form of
a substituted `Q`-graph, has a smaller `runMu n` than `G = H.glue x y₁ y₂ (tVar true)`. At
`y₁ = y₂` the leading term and the third recollision term of [II, (4.15)] keep the order and the
light weights and lower the number of solid edges. -/
def substMuStmt : Prop :=
  ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m)
    (x y₁ y₂ : Atom 3 m),
    3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    4 ≤ (H.glue x y₁ y₂ (tVar true)).ord → (H.glue x y₁ y₂ (tVar true)).ord ≤ n →
    (H.glue x y₁ y₂ (tVar true)).InvB' → (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    gsPM' (H.glue x y₁ y₂ (tVar true)) → ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
    (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    (∀ g ∈ 𝒯.tSubst (n - 1), ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), t.g.LabelFree →
      runMu n t.g < runMu n (H.glue x y₁ y₂ (tVar true))) ∧
    (∀ g ∈ 𝒯.Q, ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid),
      ∀ (x' : Fin t.nOut) (E : TExpansion 3 t.nOut), t.g.IsQFormAt (.inr x') →
        ¬ t.g.IsQGraph → qexpClauseB D x' t.g E → ∀ s ∈ E, s.g.LabelFree →
          runMu n s.g < runMu n (H.glue x y₁ y₂ (tVar true)))

/-- The clauses on every output graph of a run: only diffusive edges at `⊗`, dot excess `0`, no
labelled dotted or `×`-dotted edge, at most one label. -/
def Graph.LeafC {n₀ : ℕ} (Γ : Graph 3 n₀) : Prop :=
  Γ.TensorDiffusive ∧ Γ.dotExcess = 0 ∧ Γ.NoLabDot ∧ Γ.labels.length ≤ 1

/-- The output class `R` of [II, Def 6.3 (1)] in the block reading: a `⊕/⊖`-recollision graph
without labels, globally standard, with the clause on the external atoms and the charge pattern
of the block normal form, of scaling order `≥ 5` if `⊕`, `⊖` lie in one block. -/
def Graph.LeafR {n₀ : ℕ} (Γ : Graph 3 n₀) : Prop :=
  Γ.IsRecollision {1, 2} ∧ Γ.LabelFree ∧ gsPM' Γ ∧ Γ.ExtClause ∧ Γ.ColourInvB ∧
    (Γ.PMBlock → 5 ≤ Γ.ord)

/-- The output class `A` of [II, Def 6.3 (2)] in the block reading at the cutoff order `n`: a graph
without labels of scaling order `≥ n + 1`, sequentially pre-deterministic, with the clause on the
external atoms and the charge pattern of the block normal form; globally standard if it is a
`⊕/⊖`-recollision graph; of scaling order `≥ 5` if `⊕`, `⊖` lie in one block. -/
def Graph.LeafA {n₀ : ℕ} (n : ℕ) (Γ : Graph 3 n₀) : Prop :=
  (n : ℤ) + 1 ≤ Γ.ord ∧ Γ.LabelFree ∧ spdPM' Γ ∧ Γ.ExtClause ∧ Γ.ColourInvB ∧
    (Γ.IsRecollision {1, 2} → gsPM' Γ) ∧ (Γ.PMBlock → 5 ≤ Γ.ord)

/-- The output class `Q` of [II, Def 6.3 (3)] in the block reading: a sequentially
pre-deterministic `Q`-graph with `Graph.QLabelInMISB`, of scaling order `≥ 4` if `⊕`, `⊖` lie in
one block, with the clause `Graph.RgCheck`. -/
def Graph.LeafQ {n₀ : ℕ} (Γ : Graph 3 n₀) : Prop :=
  Γ.IsQGraph ∧ spdPM' Γ ∧ Γ.QLabelInMISB ∧ (Γ.PMBlock → 4 ≤ Γ.ord) ∧ Γ.RgCheck

/-- The outputs of [II, Lemma 6.7] in the block reading: a globally standard graph without labels
with a deterministic maximal subgraph, the clause on the external atoms and the charge pattern of
the block normal form. -/
def Graph.LeafDet {n₀ : ℕ} (Γ : Graph 3 n₀) : Prop :=
  Γ.LabelFree ∧ gsPM' Γ ∧ Γ.MaxDeterministic ∧ Γ.ExtClause ∧ Γ.ColourInvB

/-- The clause `Graph.ExtClause` needs an internal atom: its clause on `⊗` is a diffusive edge from
`⊗` to an internal or identified atom, and without internal atoms no atom is identified. -/
theorem Strategy_extClause_ne_zero {n : ℕ} {Γ : Graph 3 n} (h : Γ.ExtClause) : n ≠ 0 := by
  rintro rfl
  obtain ⟨c, -, -, hc⟩ := (h.2.2.1 ⟨rfl, fun b => b.elim0⟩).1
  rcases hc with ⟨-, hy⟩ | ⟨-, hx⟩
  · refine hy ⟨?_, fun b => b.elim0⟩
    rcases c.y with y | y
    · rfl
    · exact y.elim0
  · refine hx ⟨?_, fun b => b.elim0⟩
    rcases c.x with x | x
    · rfl
    · exact x.elim0

/-- The output classes give [II, Def 6.3] in the block reading with the clauses read by the
substitution (`TRec.Def63`): a record whose graphs of `R`, `A`, `Q` are of the classes
`Graph.LeafR`, `Graph.LeafA n`, `Graph.LeafQ`, whose graphs of `Err` satisfy `Graph.RgCheck`,
all of whose graphs satisfy `Graph.LeafC`, whose graphs of `R`, `A`, `Q` are plain
(`Graph.Plain`), whose graphs of `Q` with an internal atom satisfy the
clause on the external atoms and the charge pattern of the block normal form, whose graphs of `Q`
without an internal atom satisfy `Graph.RootAtPlus`, `Graph.QLabelAtPlus` and
`Graph.MinusProfile`, and whose graphs of `A`, `Q` and `Err` with an internal atom that are not
`⊕`-recollision graphs at `𝔟₁ = 𝔟₂` are rooted at the external atoms, satisfies `TRec.Def63`. The graphs of `A` have an internal atom, since the
clause on the external atoms needs a diffusive edge from `⊗` to an internal or identified atom, so
the hypothesis on their profile at `⊖` is vacuous for the graphs of the class `Graph.LeafA n`. -/
theorem TRec.def63_of_leaves (n : ℕ) (𝒯 : TRec)
    (hR : ∀ g ∈ 𝒯.R, g.2.LeafR ∧ g.2.LeafC ∧ g.2.Plain)
    (hA : ∀ g ∈ 𝒯.A, g.2.LeafA n ∧ g.2.LeafC ∧ (g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt) ∧
      g.2.Plain ∧ (g.1 = 0 → g.2.MinusProfile))
    (hQ : ∀ g ∈ 𝒯.Q, g.2.LeafQ ∧ g.2.LeafC ∧ (g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt) ∧
      (g.1 ≠ 0 → g.2.ExtClause ∧ g.2.ColourInvB) ∧
      (g.1 = 0 → g.2.RootAtPlus ∧ g.2.QLabelAtPlus ∧ g.2.MinusProfile) ∧ g.2.Plain)
    (hE : ∀ g ∈ 𝒯.Err, g.2.LeafC ∧ g.2.RgCheck ∧
      (g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt)) : 𝒯.Def63 := by
  refine ⟨⟨fun g hg => ?_, fun g hg => ?_, fun g hg => ?_⟩, fun g hg => ?_,
    fun g hg => (hA g hg).1.2.2.2.2.2.1, fun g hg => ?_, fun g hg => (hQ g hg).1.2.2.2.1,
    fun g hg => ?_, fun g hg => ?_, fun g hg => ?_, fun g hg h0 => ((hQ g hg).2.2.2.2.1 h0).2.1,
    fun g hg h0 => ?_⟩
  · obtain ⟨⟨-, -, h1, h2, h3, -⟩, -⟩ := hR g hg
    exact ⟨h1, h2, h3⟩
  · obtain ⟨⟨-, -, h1, h2, h3, -, -⟩, -⟩ := hA g hg
    exact ⟨h1, Or.inr ⟨h2, h3⟩⟩
  · obtain ⟨⟨-, h1, h2, -, -⟩, -, -, hx, hr, -⟩ := hQ g hg
    exact ⟨h1, h2, (em (g.1 = 0)).elim (fun h => Or.inl ⟨h, (hr h).1⟩) fun h => Or.inr (hx h)⟩
  · simp only [List.mem_append, or_assoc] at hg
    rcases hg with hg | hg | hg | hg
    · exact (hR g hg).2.1
    · exact (hA g hg).2.1
    · exact (hQ g hg).2.1
    · exact (hE g hg).1
  · rcases List.mem_append.1 hg with hg | hg
    · exact (hR g hg).1.2.2.2.2.2
    · exact (hA g hg).1.2.2.2.2.2.2
  · rcases List.mem_append.1 hg with hg | hg
    · exact (hQ g hg).1.2.2.2.2
    · exact (hE g hg).2.1
  · simp only [List.mem_append, or_assoc] at hg
    rcases hg with hg | hg | hg
    · exact (hA g hg).2.2.1
    · exact (hQ g hg).2.2.1
    · exact (hE g hg).2.2
  · simp only [List.mem_append, or_assoc] at hg
    rcases hg with hg | hg | hg
    · exact (hR g hg).2.2
    · exact (hA g hg).2.2.2.1
    · exact (hQ g hg).2.2.2.2.2
  · rcases List.mem_append.1 hg with hg | hg
    · exact (hA g hg).2.2.2.2 h0
    · exact ((hQ g hg).2.2.2.2.1 h0).2.2

/-- The graphs of the leading term, of the self-energy terms at order `m` and of the recollision
terms of [II, (4.15)] are plain. -/
theorem leadSigmaCorr_plain (m : ℕ) : ∀ g ∈ leadExp ++ sigmaTExp m ++ tVarCorr, g.2.Plain := by
  have hc : ∀ g ∈ tVarCorr, g.2.Plain := by
    set_option maxRecDepth 100000 in decide +kernel
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · obtain rfl : g = ⟨0, thetaLabelGraph []⟩ := by simpa [leadExp] using hg
      exact thetaLabelGraph_plain _
    · obtain ⟨o, -, rfl⟩ := List.mem_map.1 hg
      exact thetaLabelGraph_plain o
  · exact hc g hg

/-! ## Decidability instances for concrete graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance G8r_decAdjDot {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

private instance G8r_decSameBlock {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameBlock :=
  fun u v => @SimpleGraph.instDecidableRelReachable _ _ _ _ (G8r_decAdjDot Γ) u v

private instance G8r_decAdjMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.molGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = v ∧ c.y = u))))

private instance G8r_decSameMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameMol :=
  fun u v =>
    haveI : Decidable (Γ.molGraph.Reachable u v) :=
      @SimpleGraph.instDecidableRelReachable _ _ _ _ (G8r_decAdjMol Γ) u v
    inferInstanceAs (Decidable (u = v ∨
      (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)))

private instance G8r_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

private instance G8r_decXdotApart {k n : ℕ} (Γ : Graph k n) : Decidable Γ.XdotApart := by
  unfold Graph.XdotApart; infer_instance

/-! ### The `t`-variable of Step 2 -/

/-- An atom whose molecule is an internal vertex of `Graph.toMG'` is internal. -/
private theorem G8r_isRight_of_mem_int {k n : ℕ} (Γ : Graph k n) (u : Atom k n)
    (h : Γ.molRep u ∈ Γ.toMG'.int) : u.isRight = true := by
  rcases u with a | a
  · obtain ⟨b, -, hb⟩ := Finset.mem_image.1 h
    simp [Graph.molRep] at hb
  · rfl

/-- An atom whose molecule lies in the minimal isolated subset of `Graph.toMG'` is internal. -/
private theorem G8r_isRight_of_mem_MIS {k n : ℕ} (Γ : Graph k n) (u : Atom k n)
    (h : Γ.molRep u ∈ Γ.toMG'.MIS) : u.isRight = true := by
  refine G8r_isRight_of_mem_int Γ u ?_
  classical
  simp only [MGraph.MIS, Finset.mem_filter] at h
  exact h.1

private theorem G8r_step2EdgeB'_of_colourInv : step2EdgeB'_of_colourInvStmt := by
  intro n Γ i h hS
  refine ⟨hS, fun c hc hc' => ?_⟩
  have hq : Γ.comps[i].y.isRight = true := G8r_isRight_of_mem_MIS Γ _ hS.2.2.1
  rcases hc' with ⟨hk, hy⟩ | ⟨hk, -⟩
  · have hr : c.kind.isRandom = true := by rw [hk]; rfl
    exact ⟨((h c hc).1 hr).1, hy ▸ hq⟩
  · exact (h c hc).2 hk

/-- The components of `H.glue x y₁ y₂ (tVar true)` after those of `H`: `s_{αx}`, `G_{y₁α}`,
`Ḡ_{y₂α}` and the two `×`-dotted edges. -/
private theorem G8r_glue_tVar_comps {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) :
    (H.glue x y₁ y₂ (tVar true)).comps = liftCs 1 H.comps ++
      [⟨.waved .s, newA 0, liftA 1 x, [], none⟩, ⟨.G .plus, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩, ⟨.xdot, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.xdot, liftA 1 y₂, newA 0, [], none⟩] := by
  rfl

private theorem G8r_isRight_liftA {m : ℕ} (u : Atom 3 m) : (liftA 1 u).isRight = u.isRight := by
  rcases u with a | a <;> rfl

private theorem G8r_step2EdgeB'_internal : step2EdgeB'_internalStmt := by
  intro m H x y₁ y₂ h
  have hlen : (liftCs 1 H.comps).length = H.comps.length := by simp [liftCs]
  have hi : H.comps.length + 1 < (H.glue x y₁ y₂ (tVar true)).comps.length := by
    rw [G8r_glue_tVar_comps]
    simp [hlen]
  obtain ⟨hS, hc⟩ := h ⟨_, hi⟩ rfl
  have hci : (H.glue x y₁ y₂ (tVar true)).comps[(⟨_, hi⟩ : Fin _)] =
      ⟨.G .plus, liftA 1 y₁, newA 0, [], none⟩ := by
    simp only [Fin.getElem_fin, G8r_glue_tVar_comps]
    rw [List.getElem_append_right (by omega)]
    simp [hlen]
  have hy₁ := G8r_isRight_of_mem_MIS _ _ hS.2.1
  rw [hci] at hy₁ hc
  have hmem : ∀ c ∈ [(⟨.waved .s, newA 0, liftA 1 x, [], none⟩ : Comp (Atom 3 (m + 1))),
      ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩], c ∈ (H.glue x y₁ y₂ (tVar true)).comps := by
    intro c hc'
    rw [G8r_glue_tVar_comps]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl <;> simp
  have h1 := hc ⟨.waved .s, newA 0, liftA 1 x, [], none⟩ (hmem _ (by simp))
    (Or.inr ⟨rfl, Or.inl rfl⟩)
  have h2 := hc ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩ (hmem _ (by simp)) (Or.inl ⟨rfl, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · rw [← G8r_isRight_liftA]; exact h1.2
  · rw [← G8r_isRight_liftA]; exact hy₁
  · rw [← G8r_isRight_liftA]; exact h2.1

end Instances

/-! ## The Step 2 statements, the value identity of a reordering and of a run -/

/-- The statement `step2EdgeB'_of_colourInvStmt`. -/
theorem step2EdgeB'_of_colourInv : step2EdgeB'_of_colourInvStmt :=
  G8r_step2EdgeB'_of_colourInv

/-- The statement `step2EdgeB'_internalStmt`. -/
theorem step2EdgeB'_internal : step2EdgeB'_internalStmt :=
  G8r_step2EdgeB'_internal

/-- The factor of a component read at `σ` after a map `f` of the atoms is the factor of the
original component read at `σ ∘ f`. -/
private theorem Strategy_comp_val_map {ι V W : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

/-- A map of the second component of a pair, injective on that component, is injective. -/
private theorem Strategy_prodMap_id_injective {α β γ : Type*} {f : α → β}
    (hf : Function.Injective f) : Function.Injective (Prod.map (id : γ → γ) f) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.map, Prod.mk.injEq, id] at h
  rw [h.1, hf h.2]

/-- The labels of the image of a graph under an injective map of the atoms are the image of the
labels. -/
private theorem Strategy_labels_mapAtoms {k n k' n' : ℕ} (Γ : Graph k n)
    (f : Atom k n → Atom k' n') (hf : Function.Injective f) :
    (Γ.mapAtoms f).labels = Γ.labels.map (Prod.map id f) := by
  have hg := Strategy_prodMap_id_injective (γ := PQ) hf
  unfold Graph.labels Graph.mapAtoms
  rw [← List.dedup_map_of_injective hg, List.map_filterMap, List.filterMap_map]
  rfl

/-- The labelled term of the image of a graph under an injective map of the atoms, at `σ`, is
the labelled term of the graph at `σ ∘ f`. -/
private theorem Strategy_termR_mapAtoms {k n k' n' : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (f : Atom k n → Atom k' n') (hf : Function.Injective f)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k' n' → ι) (ω : Ω) :
    (Γ.mapAtoms f).termR PF D σ ω = Γ.termR PF D (σ ∘ f) ω := by
  have hg := Strategy_prodMap_id_injective (γ := PQ) hf
  have hunl : ∀ c : Comp (Atom k n), (Comp.map f c).label.isNone = c.label.isNone := by
    intro c
    simp [Comp.map]
  have hgrp : ∀ (ℓ : PQ × Atom k n) (c : Comp (Atom k n)),
      decide ((Comp.map f c).label = some (Prod.map id f ℓ)) = decide (c.label = some ℓ) := by
    intro ℓ c
    have : (Comp.map f c).label = some (Prod.map id f ℓ) ↔ c.label = some ℓ := by
      change Option.map (Prod.map id f) c.label = Option.map (Prod.map id f) (some ℓ) ↔ _
      exact (Option.map_injective hg).eq_iff
    simp [this]
  unfold Graph.termR
  rw [Strategy_labels_mapAtoms Γ f hf]
  simp only [Graph.mapAtoms, List.filter_map, List.map_map]
  simp only [Function.comp_def, Strategy_comp_val_map, hunl, hgrp, Prod.map_fst, Prod.map_snd,
    id]

/-- The value of a graph with labels does not depend on the names of the internal atoms
([I, Def 2.9]). -/
private theorem Strategy_valR_relabel {k n : ℕ} (Γ : Graph k n) (π : Equiv.Perm (Fin n))
    {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) : (Γ.relabel π).valR PF D e = Γ.valR PF D e := by
  funext ω
  have hf : Function.Injective (Sum.map (id : Fin k → Fin k) π) :=
    Sum.map_injective.2 ⟨Function.injective_id, π.injective⟩
  simp only [Graph.valR]
  rw [← (Equiv.arrowCongr π.symm (Equiv.refl ι)).sum_comp
    (fun s => Γ.termR PF D (Sum.elim e s) ω)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Graph.relabel, Strategy_termR_mapAtoms Γ _ hf, Sum.elim_comp_map]
  rfl

/-- Permuting a list of components keeps the product of the factors of a filtered sublist. -/
private theorem Strategy_prod_perm {V ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : V → ι) (p : Comp V → Bool) {l l' : List (Comp V)} (h : l.Perm l') :
    ((l'.filter p).map (Comp.val D σ)).prod = ((l.filter p).map (Comp.val D σ)).prod :=
  ((h.filter p).map _).prod_eq.symm

/-- Listing the components in another order keeps the labelled term. -/
private theorem Strategy_termR_perm {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ Γ' : Graph k n) (hc : Γ'.coeff = Γ.coeff) (hp : Γ.comps.Perm Γ'.comps)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω) :
    Γ'.termR PF D σ ω = Γ.termR PF D σ ω := by
  have hl : Γ.labels.Perm Γ'.labels := (hp.filterMap _).dedup
  unfold Graph.termR
  rw [hc, Strategy_prod_perm _ _ _ hp]
  congr 1
  have hf : (fun ℓ : PQ × Atom k n => PF.op ℓ.1 (σ ℓ.2) (fun ω' =>
      ((Γ'.comps.filter fun c => decide (c.label = some ℓ)).map (Comp.val (D ω') σ)).prod) ω) =
      (fun ℓ => PF.op ℓ.1 (σ ℓ.2) (fun ω' =>
      ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map (Comp.val (D ω') σ)).prod) ω) := by
    funext ℓ
    congr 1
    funext ω'
    exact Strategy_prod_perm _ _ _ hp
  rw [hf]
  exact (hl.map _).prod_eq.symm

/-- The relation of `Graph.Reorder` between the components of the relabelled graph and the
reordered list: equal, or the two atoms of `s`, of a dotted or of a `×`-dotted edge exchanged. -/
private def Strategy_SwapRel {k n : ℕ} (c c' : Comp (Atom k n)) : Prop :=
  c' = c ∨ ((c.kind = .waved .s ∨ c.kind = .dot ∨ c.kind = .xdot) ∧
    c' = { c with x := c.y, y := c.x })

/-- The exchange of the two atoms of `s`, of a dotted or of a `×`-dotted edge keeps the label
and, for a symmetric `s`, the factor. -/
private theorem Strategy_swapRel_val {k n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (hS : D.S.IsSymm) (σ : Atom k n → ι) {c c' : Comp (Atom k n)}
    (h : Strategy_SwapRel c c') : c'.label = c.label ∧ Comp.val D σ c' = Comp.val D σ c := by
  rcases h with rfl | ⟨hk, rfl⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨rfl, ?_⟩
    rcases hk with hk | hk | hk <;> simp only [Comp.val, hk]
    · exact hS.apply _ _
    · simp only [eq_comm]
    · simp only [eq_comm]

/-- The exchanges of `Strategy_SwapRel` keep the list of labels. -/
private theorem Strategy_filterMap_swap {k n : ℕ} {l l' : List (Comp (Atom k n))}
    (h : List.Forall₂ Strategy_SwapRel l l') :
    l'.filterMap Comp.label = l.filterMap Comp.label := by
  induction h with
  | nil => rfl
  | @cons c c' l l' hr _ ih =>
    have hlab : c'.label = c.label := by
      rcases hr with rfl | ⟨-, rfl⟩ <;> rfl
    simp only [List.filterMap_cons, hlab, ih]

/-- The exchanges of `Strategy_SwapRel` keep the product of the factors of every sublist filtered
by the labels, for a symmetric `s`. -/
private theorem Strategy_prod_swap {k n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (hS : D.S.IsSymm) (σ : Atom k n → ι)
    (p : Option (PQ × Atom k n) → Bool) {l l' : List (Comp (Atom k n))}
    (h : List.Forall₂ Strategy_SwapRel l l') :
    ((l'.filter fun c => p c.label).map (Comp.val D σ)).prod =
      ((l.filter fun c => p c.label).map (Comp.val D σ)).prod := by
  induction h with
  | nil => rfl
  | @cons c c' l l' hr _ ih =>
    obtain ⟨hlab, hv⟩ := Strategy_swapRel_val D hS σ hr
    simp only [List.filter_cons, hlab]
    split <;> simp only [List.map_cons, List.prod_cons, hv, ih]

/-- The exchanges of `Strategy_SwapRel` keep the labelled term, for a symmetric `s`. -/
private theorem Strategy_termR_swap {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ Γ' : Graph k n) (hc : Γ'.coeff = Γ.coeff)
    (h : List.Forall₂ Strategy_SwapRel Γ.comps Γ'.comps)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (hS : ∀ ω, (D ω).S.IsSymm) (σ : Atom k n → ι) (ω : Ω) :
    Γ'.termR PF D σ ω = Γ.termR PF D σ ω := by
  have hl : Γ'.labels = Γ.labels := by
    simp only [Graph.labels, Strategy_filterMap_swap h]
  unfold Graph.termR
  rw [hc, hl, Strategy_prod_swap (D ω) (hS ω) σ (fun o => o.isNone) h]
  congr 1
  congr 1
  refine List.map_congr_left fun ℓ _ => ?_
  congr 1
  funext ω'
  exact Strategy_prod_swap (D ω') (hS ω') σ (fun o => decide (o = some ℓ)) h

/-- The statement `reorder_valueStmt`. -/
theorem reorder_value : reorder_valueStmt := by
  intro k n Γ Γ' ⟨hc, π, cs, h₂, hp⟩ Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  have hS : ∀ ω, (D ω).S.IsSymm := fun ω => by
    rw [A.data_S ω]
    exact A.isSymm.map _
  let Γ₂ : Graph k n := ⟨cs, Γ.coeff⟩
  rw [← Strategy_valR_relabel Γ π PF D e]
  funext ω
  simp only [Graph.valR]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Strategy_termR_perm Γ₂ Γ' hc hp PF D _ ω]
  exact Strategy_termR_swap (Γ.relabel π) Γ₂ rfl h₂ PF D hS _ ω

/-- The value of a concatenation of formal sums is the sum of the values. -/
private theorem Strategy_valR_append {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (E F : Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) :
    (E ++ F).valR PF D e = E.valR PF D e + F.valR PF D e := by
  funext ω
  simp [Expansion.valR, List.map_append, List.sum_append]

/-- The value of `g :: E` is the value of `g` plus the value of `E`. -/
private theorem Strategy_valR_cons {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Σ n, Graph k n) (E : Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) :
    Expansion.valR (g :: E) PF D e = g.2.valR PF D e + E.valR PF D e := by
  funext ω
  simp [Expansion.valR]

/-- The empty formal sum has value `0`. -/
private theorem Strategy_valR_nil {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) :
    Expansion.valR ([] : Expansion k) PF D e = 0 := by
  funext ω
  simp [Expansion.valR]

/-- Exchanging the atoms of the solid edges keeps the labels. -/
private theorem Strategy_labels_swapSolid {k n : ℕ} (Γ : Graph k n) :
    Γ.swapSolid.labels = Γ.labels := by
  have h : Comp.label ∘ (Comp.swapSolid (V := Atom k n)) = Comp.label := by
    funext c
    simp only [Function.comp_apply, Comp.swapSolid]
    split <;> rfl
  simp only [Graph.labels, Graph.swapSolid, List.filterMap_map, h]

/-- Every graph of the right side of [II, (4.15)] with all `G` entries transposed has at most one
label when the graphs of `R`, `A`, `Q`, `Err` have at most one label. -/
private theorem Strategy_tSubst_labels (n : ℕ) (𝒯 : TRec)
    (hlab : ∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, g.2.labels.length ≤ 1) :
    ∀ g ∈ (𝒯.tSubst n).swapSolid, g.2.labels.length ≤ 1 := by
  have hc : ∀ g ∈ tVarCorr, g.2.labels.length ≤ 1 := by decide
  intro g hg
  simp only [Expansion.swapSolid, List.mem_map] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  simp only [Strategy_labels_swapSolid]
  simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg₀
  rcases hg₀ with (((((hl | hs) | hR) | hA) | hQ) | hE) | hT
  · simp only [leadExp, List.mem_singleton] at hl
    subst hl
    exact Nat.zero_le _
  · simp only [sigmaTExp, List.mem_map] at hs
    obtain ⟨o, -, rfl⟩ := hs
    exact Nat.zero_le _
  · exact hlab g₀ (by simp [hR])
  · exact hlab g₀ (by simp [hA])
  · exact hlab g₀ (by simp [hQ])
  · exact hlab g₀ (by simp [hE])
  · exact hc g₀ hT

/-- A factor `v` of a product with `v * v = v`, listed a second time, does not change the
product. -/
private theorem Strategy_prod_dup {v : ℂ} {L : List ℂ} (hv : v ∈ L) (hvv : v * v = v) :
    (L ++ [v]).prod = L.prod := by
  rw [List.prod_append, List.prod_singleton, ← List.prod_erase hv]
  calc v * (L.erase v).prod * v = (v * v) * (L.erase v).prod := by ring
    _ = v * (L.erase v).prod := by rw [hvv]

/-- A `×`-dotted edge `c` of `Γ` listed a second time does not change the term at a labelling `σ`
and an outcome `ω`: its factor is `0` or `1`, and `1_{u ≠ v}² = 1_{u ≠ v}`; if `c` carries a
label, the list of labels is a permutation of that of `Γ`. -/
private theorem Strategy_termR_xdotDup {n₀ : ℕ} (Γ : Graph 3 n₀) (c : Comp (Atom 3 n₀))
    (hc : c ∈ Γ.comps) (hk : c.kind = .xdot) {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom 3 n₀ → ι) (ω : Ω) :
    (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph 3 n₀).termR PF D σ ω = Γ.termR PF D σ ω := by
  have hvv : ∀ D' : Data ι, Comp.val D' σ c * Comp.val D' σ c = Comp.val D' σ c := by
    intro D'
    simp only [Comp.val, hk]
    split_ifs <;> simp
  have hunl : (((Γ.comps ++ [c]).filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod
      = ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod := by
    cases hl : c.label with
    | none =>
      simp only [List.filter_append, List.map_append, hl, List.filter_cons_of_pos, List.filter_nil,
        Option.isNone_none]
      exact Strategy_prod_dup (List.mem_map_of_mem (List.mem_filter.2 ⟨hc, by simp [hl]⟩))
        (hvv _)
    | some ℓ => simp [List.filter_append, hl]
  have hfun : ∀ (ℓ : PQ × Atom 3 n₀) (ω' : Ω),
      (((Γ.comps ++ [c]).filter fun d => decide (d.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod =
      ((Γ.comps.filter fun d => decide (d.label = some ℓ)).map (Comp.val (D ω') σ)).prod := by
    intro ℓ ω'
    by_cases hl : c.label = some ℓ
    · simp only [List.filter_append, List.map_append, hl, List.filter_cons_of_pos, List.filter_nil,
        decide_true]
      exact Strategy_prod_dup (List.mem_map_of_mem (List.mem_filter.2 ⟨hc, by simp [hl]⟩))
        (hvv _)
    · simp [List.filter_append, hl]
  have hlab : (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph 3 n₀).labels.Perm Γ.labels := by
    unfold Graph.labels
    cases hl : c.label with
    | none => simp [List.filterMap_append, hl]
    | some ℓ =>
      have hm : ℓ ∈ Γ.comps.filterMap Comp.label := List.mem_filterMap.2 ⟨c, hc, hl⟩
      refine (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).2 fun a => ?_
      simp only [List.mem_dedup, List.filterMap_append, List.mem_append]
      constructor
      · rintro (h | h)
        · exact h
        · obtain ⟨d, hd, hda⟩ := List.mem_filterMap.1 h
          obtain rfl := List.mem_singleton.1 hd
          obtain rfl : ℓ = a := Option.some.inj (hl.symm.trans hda)
          exact hm
      · exact Or.inl
  unfold Graph.termR
  simp only [hunl, hfun]
  rw [(hlab.map _).prod_eq]

/-- A `×`-dotted edge listed a second time does not change the value of a graph. -/
private theorem Strategy_valR_xdotDup {n₀ : ℕ} (Γ : Graph 3 n₀) (c : Comp (Atom 3 n₀))
    (hc : c ∈ Γ.comps) (hk : c.kind = .xdot) {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin 3 → ι) :
    (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph 3 n₀).valR PF D e = Γ.valR PF D e := by
  funext ω
  exact Finset.sum_congr rfl fun s _ => Strategy_termR_xdotDup Γ c hc hk PF D _ ω

/-- A component with its internal atoms renumbered by the identity permutation is the
component. -/
private theorem Strategy_map_refl {n : ℕ} (c : Comp (Atom 3 n)) :
    c.map (Sum.map id (Equiv.refl (Fin n))) = c := by
  have hf : (Sum.map id (Equiv.refl (Fin n)) : Atom 3 n → Atom 3 n) = id := by
    funext u; cases u <;> rfl
  rw [hf]
  cases c with
  | mk κ x y mi l => simp [Comp.map]

/-- The graph with the component `j` erased and a copy of the `×`-dotted edge `i` appended is a
reordering (`Graph.Reorder`) of the graph, when `j` is a copy of `i` up to the order of its two
atoms. -/
theorem Strategy_reorder_xdotDrop {n₀ : ℕ} (Γ : Graph 3 n₀) (i j : Fin Γ.comps.length)
    (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) :
    Γ.Reorder ⟨Γ.comps.eraseIdx j ++ [Γ.comps[i]], Γ.coeff⟩ := by
  refine ⟨rfl, Equiv.refl _, Γ.comps.set j Γ.comps[i], ?_, ?_⟩
  · have hrel : (Γ.relabel (Equiv.refl _)).comps = Γ.comps :=
      List.map_id'' Strategy_map_refl Γ.comps
    rw [hrel]
    refine List.forall₂_iff_get.2 ⟨by simp, fun a h₁ h₂ => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_set]
    split_ifs with h
    · subst h
      simp only [Fin.getElem_fin] at hc ⊢
      rcases hc with h1 | h2
      · exact Or.inl h1.symm
      · refine Or.inr ⟨Or.inr (Or.inr (by rw [h2]; exact hk)), ?_⟩
        rw [h2]
    · exact Or.inl rfl
  · rw [List.set_eq_take_append_cons_drop, ite_eq_left j.2, List.eraseIdx_eq_take_drop_succ]
    exact List.perm_middle.trans (List.perm_append_singleton _ _).symm

/-- Removing one of two parallel `×`-dotted edges does not change the value of a graph, whichever
way round the removed edge lists its atoms. -/
private theorem Strategy_valR_xdotDrop {n₀ : ℕ} (Γ : Graph 3 n₀) (i j : Fin Γ.comps.length)
    (hij : i ≠ j)
    (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) (hR : reorder_valueStmt) {Ω ι : Type} [Fintype ι]
    [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι) (hA : modelAdm Ω ι PF D)
    (e : Fin 3 → ι) :
    (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 n₀).valR PF D e = Γ.valR PF D e := by
  have hmem : Γ.comps[i] ∈ Γ.comps.eraseIdx j :=
    List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, fun h => hij (Fin.ext h), rfl⟩
  rw [← hR 3 n₀ Γ _ (Strategy_reorder_xdotDrop Γ i j hc hk) Ω ι PF D hA e]
  exact (Strategy_valR_xdotDup ⟨Γ.comps.eraseIdx j, Γ.coeff⟩ Γ.comps[i] hmem hk PF D e).symm

/-- The factor `m · m⁻¹ · m̄ · m̄⁻¹` has value `1` at a value `m ≠ 0`. -/
private theorem Strategy_coeffNorm_eval (m : ℂ) (hm : m ≠ 0) (p : Coeff) :
    Coeff.eval m (p * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv) =
      Coeff.eval m p := by
  have hm' : star m ≠ 0 := star_ne_zero.2 hm
  unfold Coeff.eval
  simp only [map_mul, MvPolynomial.eval_X, cm, cmb, CVar.eval]
  field_simp

/-- Multiplying the coefficient by `m · m⁻¹ · m̄ · m̄⁻¹` does not change the value of a graph in
the model, where `m = m_sc(z) ≠ 0`. -/
private theorem Strategy_valR_coeffNorm {n₀ : ℕ} (Γ : Graph 3 n₀) {Ω ι : Type} [Fintype ι]
    [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι) (hA : modelAdm Ω ι PF D)
    (e : Fin 3 → ι) :
    (⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩ :
      Graph 3 n₀).valR PF D e = Γ.valR PF D e := by
  obtain ⟨A⟩ := hA
  funext ω
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold Graph.termR
  dsimp only
  rw [Strategy_coeffNorm_eval _ (by rw [A.data_m ω]; exact msc_ne_zero _)]
  rfl

/-- A graph with a `×`-dotted loop has value `0` in the model: the factor `1_{u ≠ v}` of the loop
is `0` at every labelling, and so is the unlabelled product or, for a labelled loop, the operator
`P_x` or `Q_x` of the zero function. -/
private theorem Strategy_valR_xdotLoop {n₀ : ℕ} (Γ : Graph 3 n₀) (c : Comp (Atom 3 n₀))
    (hc : c ∈ Γ.comps) (hk : c.kind = .xdot) (hxy : c.x = c.y) {Ω ι : Type} [Fintype ι]
    [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι) (hA : modelAdm Ω ι PF D)
    (e : Fin 3 → ι) : Γ.valR PF D e = 0 := by
  obtain ⟨A⟩ := hA
  funext ω
  refine Finset.sum_eq_zero fun s _ => ?_
  have h0 : ∀ D' : Data ι, Comp.val D' (Sum.elim e s) c = 0 := by
    intro D'
    simp [Comp.val, hk, hxy]
  cases hl : c.label with
  | none => exact termR_eq_zero_of_val PF D _ ω hc hl (h0 _)
  | some ℓ =>
    have hmem : ℓ ∈ Γ.labels := List.mem_dedup.2 (List.mem_filterMap.2 ⟨c, hc, hl⟩)
    have hf : (fun ω' => ((Γ.comps.filter fun d => decide (d.label = some ℓ)).map
        (Comp.val (D ω') (Sum.elim e s))).prod) = fun _ => 0 := by
      funext ω'
      exact List.prod_eq_zero (List.mem_map.2
        ⟨c, List.mem_filter.2 ⟨hc, by simp [hl]⟩, h0 _⟩)
    have hP : ∀ x, PF.P x (fun _ => (0 : ℂ)) = fun _ => 0 := fun x =>
      A.laws.of_meas x _ (A.laws.good_const 0) (A.laws.meas_const x 0)
    have hop : PF.op ℓ.1 (Sum.elim e s ℓ.2) (fun ω' => ((Γ.comps.filter fun d =>
        decide (d.label = some ℓ)).map (Comp.val (D ω') (Sum.elim e s))).prod) ω = 0 := by
      rw [hf]
      cases ℓ.1 with
      | P => simp [PFamily.op, hP]
      | Q => simp [PFamily.op, hP]
    unfold Graph.termR
    rw [List.prod_eq_zero (List.mem_map.2 ⟨ℓ, hmem, hop⟩)]
    simp

/-- One step of [II, Strategy 6.6] keeps values. -/
private theorem Strategy_step_value (hR : reorder_valueStmt) (Sig : ℕ → Expansion 2)
    (n D : ℕ) (𝒯 : TRec) (h1 : 1 ≤ n) (hid : 𝒯.Identity Sig (n - 1))
    (hsh : SelfEnergyShapesUpTo Sig (n - 1))
    (hlab : ∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, g.2.labels.length ≤ 1)
    {g : Σ n₀ : ℕ, Graph 3 n₀} {E₁ : Expansion 3} (h : StrategyStepB n D 𝒯 g E₁)
    {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (Dt : Ω → Data ι)
    (hA : modelAdm Ω ι PF Dt) (hS : ∀ ω, SigConsistent Sig n (Dt ω)) (e : Fin 3 → ι) :
    E₁.valR PF Dt e = g.2.valR PF Dt e := by
  cases h with
  | loc Γ o x C _ _ _ _ _ _ _ _ =>
    match o with
    | 0 => exact oWeight_value 3 _ (.inr x) Ω ι PF Dt hA Γ e
    | 1 => exact oMultiE_value 3 _ (.inr x) Ω ι PF Dt hA Γ e
    | 2 => exact oGG_value 3 _ (.inr x) Ω ι PF Dt hA Γ e
    | 3 => exact oGGbar_value 3 _ (.inr x) Ω ι PF Dt hA Γ e
    | 4 => exact oGGT_value' 3 _ (.inr x) Ω ι PF Dt hA Γ e
  | dot Γ => exact oDot_value 3 _ Ω ι PF Dt trivial Γ e
  | dropDot Γ Γ' C hstep _ hP =>
    obtain ⟨i, c, hc, hk, hb, rfl⟩ := hstep
    have hlab' : ∀ d ∈ Γ.comps, d.kind = .dot → d.label = none := by
      intro d hd hdk
      have hw := ((hP d hd).2.2.2.2).2
      rw [hdk] at hw
      cases hl : d.label with
      | none => rfl
      | some l => simp [hl, Kind.isRandom] at hw
    rw [Strategy_valR_cons, Strategy_valR_nil, add_zero]
    exact dropDot_value Γ hc hk hb hlab' Ω ι PF Dt e
  | reorder Γ Γ' h' =>
    rw [Strategy_valR_cons, Strategy_valR_nil, add_zero]
    exact hR 3 _ Γ Γ' h' Ω ι PF Dt hA e
  | xdotDup Γ i hk _ _ =>
    rw [Strategy_valR_cons, Strategy_valR_nil, add_zero]
    exact Strategy_valR_xdotDup Γ _ (List.getElem_mem _) hk PF Dt e
  | xdotDrop Γ i j hij hc hk _ _ =>
    rw [Strategy_valR_cons, Strategy_valR_nil, add_zero]
    exact Strategy_valR_xdotDrop Γ i j hij hc hk hR PF Dt hA e
  | xdotLoop Γ i hk hxy =>
    rw [Strategy_valR_nil]
    exact (Strategy_valR_xdotLoop Γ _ (List.getElem_mem _) hk hxy PF Dt hA e).symm
  | coeffNorm Γ =>
    rw [Strategy_valR_cons, Strategy_valR_nil, add_zero]
    exact Strategy_valR_coeffNorm Γ PF Dt hA e
  | subst H x y₁ y₂ C _ _ _ _ _ hH _ _ _ _ _ =>
    have hS' : ∀ ω, SigConsistent Sig (n - 1 + 1) (Dt ω) := by
      rw [Nat.sub_add_cancel h1]
      exact hS
    exact globalSubst_value 3 _ 1 H x y₁ y₂ (tVar true) _ Ω ι PF Dt hH (by decide)
      (Strategy_tSubst_labels (n - 1) 𝒯 hlab)
      (tSubstT_value' Sig (n - 1) 𝒯 hid hsh Ω ι PF Dt hA hS') e
  | qexp Γ x E _ _ _ hV _ => exact hV Ω ι PF Dt hA e

/-- The statement `globalRun_valueStmtB`. -/
theorem globalRun_valueB : globalRun_valueStmtB := by
  intro hR Sig n D 𝒯 h1 hid hsh hlab E F hrun Ω ι _ _ PF Dt hA hS e
  induction hrun with
  | nil => rfl
  | out _ _ ih => rw [Strategy_valR_cons, Strategy_valR_cons, ih]
  | step hs _ ih =>
    rw [Strategy_valR_cons, ← Strategy_step_value hR Sig n D 𝒯 h1 hid hsh hlab hs PF Dt hA hS e,
      ← Strategy_valR_append, ih]

section StrategyInstances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end StrategyInstances

end RBM8D.Graphs
