module

public import RBM8D.GlobalExp.TerminationB
public import RBM8D.Graph.QExp.SelRunIso
public import RBM8D.GlobalExp.Termination
public import RBM8D.GlobalExp.GlobalGood
public import RBM8D.Graph.MolCarry
public import RBM8D.GlobalExp.RunClauses
public import RBM8D.GlobalExp.Local
public import RBM8D.TExp.Second
import all RBM8D.GlobalExp.Termination
import all RBM8D.GlobalExp.GlobalGood
import all RBM8D.Graph.MolCarry
import all RBM8D.GlobalExp.RunClauses
import all RBM8D.GlobalExp.Local
import all RBM8D.GlobalExp.TerminationB
import all RBM8D.TExp.Second

@[expose] public section

/-!
# [II, Lemma 6.8] in the block reading: the selector of a run

A run of [II, Strategy 6.6] whose choices are functions of the graph alone ([II, Lemma 6.8]):

* the locations of a step (`TerminationC_Loc`) and the formal sum each one gives
  (`TerminationC_stepOut`), with the `Q`-expansion of Step 3 taken from a family `𝔈` of
  [II, Lemma 4.15];
* the conditions under which a location is a step (`TerminationC_Adm`): the premises of the step
  of `StrategyStepB`, and on the steps that keep the value without changing the order (the
  duplication and the removal of a `×`-dotted edge, the identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1`
  and a reordering) conditions that make each of them lower the measure `TerminationC_nu`;
* the graphs that are outputs of a run (`TerminationC_Out`: the outputs of [II, Strategy 6.6] with
  the clauses of [II, Lemma 6.8]), the invariant along a run (`TerminationC_RI`), the admissible
  selectors (`AdmSelector`) and the runs they drive (`SelRunB`);
* the choice of the `t`-variable of Step 2 by its atom `α` (`TerminationC_alpha`) and the measure
  `TerminationC_nu` of the normal form of Step 2: the coefficient divisible by `m m̄`, as many
  `×`-dotted edges as solid edges between `α` and each of its neighbours, and the form
  `H.glue x y₁ y₂ (tVar true)` of [II, (4.14)];
* **one selector, a function of the graph alone, is admissible** for every cutoff order, error
  order and `T`-expansion (`TerminationC_admSelector`): every graph with the invariant of a run
  that is not an output has a step of [II, Strategy 6.6]. At the blue solid edge `G_{y₁α}` of
  Step 2 the graph is brought to the form `H.glue x y₁ y₂ (tVar true)` by a reordering
  (`TerminationC_closure`), after the coefficient and the `×`-dotted edges at `α` are normalised
  and a `×`-dotted loop is removed (its graph has value `0`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Locations, steps and runs -/

/-- A location of a step of [II, Strategy 6.6] at a graph with `n₀` internal atoms: a local
expansion `o` at an internal atom (Step 1), `O_dot`, the removal of a redundant dotted edge (to the
graph given), a reordering (to the graph given), the duplication of the `×`-dotted edge with the
given index, the removal of the second of two parallel `×`-dotted edges, the empty sum at a
`×`-dotted loop, the identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1` in the coefficient, the substitution
of Steps 2–3 at `H.glue x y₁ y₂ (tVar true)`, and the `Q`-expansion of Step 3 at an internal label
atom. -/
inductive TerminationC_Loc (n₀ : ℕ) : Type
  | loc (o : Fin 5) (x : Fin n₀)
  | dot
  | dropDot (Γ' : Graph 3 n₀)
  | reorder (Γ' : Graph 3 n₀)
  | xdotDup (i : ℕ)
  | xdotDrop (i j : ℕ)
  | xdotLoop (i : ℕ)
  | coeffNorm
  | subst (m : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
  | qexp (x : Fin n₀)

/-- The formal sum given by a location at the graph `g`, at the cutoff order `n` and error order
`D`, with the `T`-expansion `𝒯` of order `n - 1` substituted in Steps 2–3 and the family `𝔈` of
`Q`-expansions of [II, Lemma 4.15] used in Step 3. -/
def TerminationC_stepOut (n D : ℕ) (𝒯 : TRec)
    (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀) (g : Σ n₀ : ℕ, Graph 3 n₀) :
    TerminationC_Loc g.1 → Expansion 3
  | .loc o x => (localOp' o (.inr x) g.2).forget
  | .dot => oDot g.2
  | .dropDot Γ' => [⟨g.1, Γ'⟩]
  | .reorder Γ' => [⟨g.1, Γ'⟩]
  | .xdotDup i => [⟨g.1, ⟨g.2.comps ++ (g.2.comps[i]?).toList, g.2.coeff⟩⟩]
  | .xdotDrop _ j => [⟨g.1, ⟨g.2.comps.eraseIdx j, g.2.coeff⟩⟩]
  | .xdotLoop _ => []
  | .coeffNorm =>
    [⟨g.1, ⟨g.2.comps,
      g.2.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩⟩]
  | .subst _ H x y₁ y₂ => H.globalSubst x y₁ y₂ (𝒯.tSubst (n - 1)).swapSolid
  | .qexp x => (𝔈 D g.1 x g.2).forget

/-- The graph-only premises of the substitution of Steps 2–3 ([II, Strategy 6.6]) at
`G = H.glue x y₁ y₂ (tVar true)`: scaling order `≥ 4`, normal regular without dotted edges, `H`
without labels, globally standard, not a `⊕/⊖`-recollision graph, only diffusive edges at `⊗`, a
locally standard minimal isolated subset, and the blue solid edge `G_{y₁α}` of the `t`-variable
chosen by Step 2. -/
def TerminationC_HostPrem {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) : Prop :=
  4 ≤ (H.glue x y₁ y₂ (tVar true)).ord ∧ (∃ C, (H.glue x y₁ y₂ (tVar true)).Normal C) ∧
    (H.glue x y₁ y₂ (tVar true)).DotFree ∧ H.LabelFree ∧ gsPM' (H.glue x y₁ y₂ (tVar true)) ∧
    ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} ∧
    (H.glue x y₁ y₂ (tVar true)).TensorDiffusive ∧ (H.glue x y₁ y₂ (tVar true)).MISLocStdB ∧
    ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i

/-- The graph is a host of the substitution of Steps 2–3: of the form
`H.glue x y₁ y₂ (tVar true)` of [II, (4.14)] with the graph-only premises
`TerminationC_HostPrem`. -/
def TerminationC_GlueHost (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  ∃ (m : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m),
    g = ⟨m + 1, H.glue x y₁ y₂ (tVar true)⟩ ∧ TerminationC_HostPrem H x y₁ y₂

/-- The internal atom `a` is the second atom `α` of a blue solid edge `G_{y₁α}` that Step 2 of
[II, Strategy 6.6] may expand, with the `t`-variable `t_{y₁y₂,x}` at `α`
(`Graph.Step2EdgeB'`). -/
def TerminationC_Qual {n₀ : ℕ} (Γ : Graph 3 n₀) (a : Fin n₀) : Prop :=
  ∃ i : Fin Γ.comps.length, Γ.comps[i].y = .inr a ∧ Γ.Step2EdgeB' i

open Classical in
/-- The atom `α` of the `t`-variable chosen in Step 2: the largest internal atom with
`TerminationC_Qual` (`none` if there is none). It reads the atoms of the components only. -/
def TerminationC_alpha (g : Σ n₀ : ℕ, Graph 3 n₀) : Option (Fin g.1) :=
  if h : ∃ a, TerminationC_Qual g.2 a then
    some ((Finset.univ.filter (TerminationC_Qual g.2)).max'
      (by obtain ⟨a, ha⟩ := h; exact ⟨a, by simpa using ha⟩))
  else none

/-- The number of `×`-dotted edges between `u` and `v`, in either orientation. -/
def TerminationC_xmult {n₀ : ℕ} (Γ : Graph 3 n₀) (u v : Atom 3 n₀) : ℕ :=
  (Γ.comps.filter fun c => c.kind == .xdot && (c.x == u && c.y == v || c.x == v && c.y == u)).length

/-- The number of solid edges between `u` and `v`, in either orientation. -/
def TerminationC_smult {n₀ : ℕ} (Γ : Graph 3 n₀) (u v : Atom 3 n₀) : ℕ :=
  (Γ.comps.filter fun c => c.kind.isSolid && (c.x == u && c.y == v || c.x == v && c.y == u)).length

open Classical in
/-- The distance of the `×`-dotted edges at `a` from their form in `H.glue x y₁ y₂ (tVar true)`:
over the atoms `v ≠ a`, the difference between the numbers of `×`-dotted and of solid edges
between `a` and `v` (in [II, (4.14)] the factors `1_{α ≠ y₁}`, `1_{α ≠ y₂}`: one `×`-dotted edge
to each of `y₁`, `y₂`, two when `y₁ = y₂`, and none to another atom). -/
def TerminationC_pairTerm {n₀ : ℕ} (Γ : Graph 3 n₀) (a : Atom 3 n₀) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => v ≠ a),
    ((TerminationC_xmult Γ a v - TerminationC_smult Γ a v) +
      (TerminationC_smult Γ a v - TerminationC_xmult Γ a v))

open Classical in
/-- **The measure of the normal form of Step 2**: `1` if the coefficient is not divisible by `m m̄`
(the factor of the `t`-variable of [II, (4.14)]), plus the distance `TerminationC_pairTerm` at the
atom `α` chosen by `TerminationC_alpha`, plus `1` if the graph is not a host of Steps 2–3. -/
def TerminationC_nu (g : Σ n₀ : ℕ, Graph 3 n₀) : ℕ :=
  (if cm * cmb ∣ g.2.coeff then 0 else 1) +
    (match TerminationC_alpha g with
      | some a => TerminationC_pairTerm g.2 (.inr a)
      | none => 0) +
    (if TerminationC_GlueHost g then 0 else 1)

/-- The graph lies in the cell of Step 2: without labels, with a locally standard minimal isolated
subset, and with an atom `α` chosen by `TerminationC_alpha`. -/
def TerminationC_Cell (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  g.2.LabelFree ∧ g.2.MISLocStdB ∧ (TerminationC_alpha g).isSome = true

/-- The component `c` joins the atoms `u` and `v`, in either orientation. -/
def TerminationC_Joins {n₀ : ℕ} (c : Comp (Atom 3 n₀)) (u v : Atom 3 n₀) : Prop :=
  c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u

/-- The `×`-dotted edges `i ≠ j` are parallel, between internal atoms, one of them at the chosen
atom `α` and an atom `v ≠ α` with more `×`-dotted than solid edges between `α` and `v`. -/
def TerminationC_DropAt (g : Σ n₀ : ℕ, Graph 3 n₀) (i j : Fin g.2.comps.length) : Prop :=
  i ≠ j ∧ (g.2.comps[j] = g.2.comps[i] ∨
      g.2.comps[j] = { g.2.comps[i] with x := g.2.comps[i].y, y := g.2.comps[i].x }) ∧
    g.2.comps[i].kind = .xdot ∧ g.2.comps[i].x.isRight = true ∧ g.2.comps[i].y.isRight = true ∧
    ∃ a v, TerminationC_alpha g = some a ∧ v ≠ .inr a ∧ TerminationC_Joins g.2.comps[i] (.inr a) v ∧
      TerminationC_smult g.2 (.inr a) v < TerminationC_xmult g.2 (.inr a) v

/-- The `×`-dotted edge `i` is between internal atoms, at the chosen atom `α` and an atom `v ≠ α`
with fewer `×`-dotted than solid edges between `α` and `v`. -/
def TerminationC_DupAt (g : Σ n₀ : ℕ, Graph 3 n₀) (i : Fin g.2.comps.length) : Prop :=
  g.2.comps[i].kind = .xdot ∧ g.2.comps[i].x.isRight = true ∧ g.2.comps[i].y.isRight = true ∧
    ∃ a v, TerminationC_alpha g = some a ∧ v ≠ .inr a ∧ TerminationC_Joins g.2.comps[i] (.inr a) v ∧
      TerminationC_xmult g.2 (.inr a) v < TerminationC_smult g.2 (.inr a) v

/-- **Admissible locations** at the graph `g`, for the cutoff order `n`, the error order `D` and the
family `𝔈`: the premises of the step of `StrategyStepB` with the output
`TerminationC_stepOut`, and
* Step 1 (`loc`) only where the local expansion applies (`Graph.LocAdm`) and no `×`-dotted edge
  lies inside a block;
* `O_dot` only on a graph that is not normal regular;
* the duplication or the removal of a `×`-dotted edge only at the atom `α` chosen in Step 2,
  towards as many `×`-dotted as solid edges, in the cell of Step 2 and not at a host of Steps 2–3;
* the identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1` only in that cell, on a coefficient not divisible by
  `m m̄`, and not at a host;
* a reordering only from a graph that is not a host to a host of Steps 2–3;
* a Q-expansion only at a normal regular plain graph in Q-form ([II, Strategy 6.6], Step 3, after
  `O_dot`);
* the empty sum at a `×`-dotted loop anywhere in the graph. -/
def TerminationC_Adm (n D : ℕ)
    (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀) (g : Σ n₀ : ℕ, Graph 3 n₀) :
    TerminationC_Loc g.1 → Prop
  | .loc o x => ¬ g.2.StopsB n ∧ ¬ (D : ℤ) < g.2.ord ∧ (∃ C, g.2.Normal C) ∧ g.2.LabelFree ∧
      g.2.Plain ∧ gsPM' g.2 ∧ g.2.molRep (.inr x) ∈ g.2.toMG'.MIS ∧ g.2.LocSide o (.inr x) ∧
      g.2.LocAdm o (.inr x) ∧ g.2.XdotApart
  | .dot => ¬ ∃ C, g.2.Normal C
  | .dropDot Γ' => DotNormStep g.2 Γ' ∧ (∃ C, g.2.Normal C) ∧ g.2.Plain
  | .reorder Γ' => g.2.Reorder Γ' ∧ ¬ TerminationC_GlueHost g ∧ TerminationC_GlueHost ⟨g.1, Γ'⟩
  | .xdotDup i => ∃ h : i < g.2.comps.length, TerminationC_DupAt g ⟨i, h⟩ ∧
      TerminationC_Cell g ∧ ¬ TerminationC_GlueHost g
  | .xdotDrop i j => ∃ (hi : i < g.2.comps.length) (hj : j < g.2.comps.length),
      TerminationC_DropAt g ⟨i, hi⟩ ⟨j, hj⟩ ∧ TerminationC_Cell g ∧ ¬ TerminationC_GlueHost g
  | .xdotLoop i => ∃ h : i < g.2.comps.length,
      g.2.comps[i].kind = .xdot ∧ g.2.comps[i].x = g.2.comps[i].y
  | .coeffNorm => TerminationC_Cell g ∧ ¬ TerminationC_GlueHost g ∧ ¬ cm * cmb ∣ g.2.coeff
  | .subst m H x y₁ y₂ => g = ⟨m + 1, H.glue x y₁ y₂ (tVar true)⟩ ∧
      ¬ (D : ℤ) < (H.glue x y₁ y₂ (tVar true)).ord ∧
      (H.glue x y₁ y₂ (tVar true)).ord ≤ n ∧ TerminationC_HostPrem H x y₁ y₂
  | .qexp x => (∃ C, g.2.Normal C) ∧ g.2.Plain ∧ ¬ (D : ℤ) < g.2.ord ∧ g.2.IsQFormAt (.inr x) ∧
      ¬ g.2.IsQGraph ∧ (𝔈 D g.1 x g.2).ValueEq g.2 modelAdm ∧
      qexpClauseB D x g.2 (𝔈 D g.1 x g.2)

/-- An admissible location is a step of [II, Strategy 6.6] (`StrategyStepB`) with the output
`TerminationC_stepOut`. -/
theorem TerminationC_Adm.step {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} {g : Σ n₀ : ℕ, Graph 3 n₀}
    {l : TerminationC_Loc g.1} (h : TerminationC_Adm n D 𝔈 g l) :
    StrategyStepB n D 𝒯 g (TerminationC_stepOut n D 𝒯 𝔈 g l) := by
  obtain ⟨n₀, Γ⟩ := g
  cases l with
  | loc o x =>
    obtain ⟨h1, h2, ⟨C, h3⟩, h4, h5, h6, h7, h8, -, -⟩ := h
    exact StrategyStepB.loc Γ o x C h1 h2 h3 h4 h5 h6 h7 h8
  | dot => exact StrategyStepB.dot Γ
  | dropDot Γ' =>
    obtain ⟨h1, ⟨C, h2⟩, h3⟩ := h
    exact StrategyStepB.dropDot Γ Γ' C h1 h2 h3
  | reorder Γ' => exact StrategyStepB.reorder Γ Γ' h.1
  | xdotDup i =>
    obtain ⟨hi, ⟨hk, hx, hy, -⟩, -⟩ := h
    have e : (Γ.comps[i]?).toList = [Γ.comps[i]] := by
      rw [List.getElem?_eq_getElem hi]; rfl
    show StrategyStepB n D 𝒯 ⟨n₀, Γ⟩ [⟨n₀, ⟨Γ.comps ++ (Γ.comps[i]?).toList, Γ.coeff⟩⟩]
    rw [e]
    exact StrategyStepB.xdotDup Γ ⟨i, hi⟩ hk hx hy
  | xdotDrop i j =>
    obtain ⟨hi, hj, ⟨hne, hc, hk, hx, hy, -⟩, -⟩ := h
    exact StrategyStepB.xdotDrop Γ ⟨i, hi⟩ ⟨j, hj⟩ hne hc hk hx hy
  | xdotLoop i =>
    obtain ⟨hi, hk, hxy⟩ := h
    exact StrategyStepB.xdotLoop Γ ⟨i, hi⟩ hk hxy
  | coeffNorm => exact StrategyStepB.coeffNorm Γ
  | subst m H x y₁ y₂ =>
    obtain ⟨he, hD, hn, ho, ⟨C, hN⟩, hdf, hL, hgs, hr, hT, hM, hst⟩ := h
    obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.1 he
    cases eq_of_heq he
    exact StrategyStepB.subst H x y₁ y₂ C hD ho hn hN hdf hL hgs hr hT hM hst
  | qexp x =>
    obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := h
    exact StrategyStepB.qexp Γ x _ h1 h2 h3 h4 h5

/-- **The outputs of a run** of [II, Strategy 6.6] with the clauses of [II, Lemma 6.8]: an output
graph (`Graph.StratLeafB`) with the conjunct of [II, Lemma 6.8] on every output graph. -/
def TerminationC_Out (n D : ℕ) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  g.2.StratLeafB n D ∧ g.2.DoublyConnected ∧ (∃ C, g.2.Normal C) ∧ g.2.LeafC ∧
    (¬ (D : ℤ) < g.2.ord → g.2.Plain) ∧
    (((D : ℤ) < g.2.ord ∧ g.2.RgCheck ∧ (g.1 ≠ 0 → g.2.ExtClause ∧ g.2.ColourInvB)) ∨
      g.2.LeafR ∨ g.2.LeafA n ∨
      (g.2.LeafQ ∧ (g.1 ≠ 0 → g.2.ExtClause ∧ g.2.ColourInvB) ∧
        (g.1 = 0 → g.2.RootAtPlus ∧ g.2.QLabelAtPlus ∧ g.2.MinusProfile)) ∨ g.2.LeafDet)

/-- **The invariant of a run** read by the selector ([II, Lemma 6.8]): the invariant of a run
`Graph.InvRun D` and the leaf invariants `TerminationB_Inv n D`, doubly connected, only diffusive
edges at `⊗`, no labelled dotted or `×`-dotted edge, at most one label and no `P`-label, the
clauses of the class `Q` of [II, Def 6.3] on `Q`-graphs (sequentially pre-deterministic, the label
in the minimal isolated subset), plain when the dot excess is not `0`, and the kinds of
[II, Def 3.2] below the error order. -/
def TerminationC_RI (n D : ℕ) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  g.2.InvRun D ∧ TerminationB_Inv n D g.2 ∧ g.2.DoublyConnected ∧ g.2.TensorDiffusive ∧
    g.2.NoLabDot ∧ g.2.labels.length ≤ 1 ∧ (∀ c ∈ g.2.comps, ∀ u, c.label ≠ some (.P, u)) ∧
    (g.2.IsQGraph → spdPM' g.2 ∧ g.2.QLabelInMISB) ∧ (g.2.dotExcess ≠ 0 → g.2.Plain) ∧
    ((D : ℤ) < g.2.paperOrd ∨ ∃ N, g.2.TKinds N)

/-- The graphs at which a selector has to give a step: the graphs that are not normal regular
(the substituted graphs of Steps 2–3 before `O_dot`), and the graphs with the invariant
`TerminationC_RI`. -/
def TerminationC_Dom (n D : ℕ) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  (¬ ∃ C, g.2.Normal C) ∨ TerminationC_RI n D g

/-- **Admissible selectors** ([II, Lemma 6.8], [II, Strategy 6.6]): a location for every graph, a
function of the graph alone, that is admissible (`TerminationC_Adm`) at every graph of
`TerminationC_Dom` that is not an output (`TerminationC_Out`); there it is a step of
`StrategyStepB n D 𝒯` with the output `TerminationC_stepOut`. -/
def AdmSelector (n D : ℕ) (𝒯 : TRec)
    (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1) : Prop :=
  ∀ g, TerminationC_Dom n D g → ¬ TerminationC_Out n D g →
    TerminationC_Adm n D 𝔈 g (ℓ g) ∧ StrategyStepB n D 𝒯 g (TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g))

/-- **The run driven by a selector** `ℓ`: every graph is an output iff it is in
`TerminationC_Out`, and otherwise it is replaced by the output of the step at its location
`ℓ g`. `SelRunB n D 𝒯 𝔈 ℓ E F` says that this run from `E` ends with the outputs `F`. -/
inductive SelRunB (n D : ℕ) (𝒯 : TRec)
    (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1) : Expansion 3 → Expansion 3 → Prop
  | nil : SelRunB n D 𝒯 𝔈 ℓ [] []
  | out {g : Σ n₀ : ℕ, Graph 3 n₀} {E F : Expansion 3} :
      TerminationC_Out n D g → SelRunB n D 𝒯 𝔈 ℓ E F → SelRunB n D 𝒯 𝔈 ℓ (g :: E) (g :: F)
  | step {g : Σ n₀ : ℕ, Graph 3 n₀} {E F : Expansion 3} :
      ¬ TerminationC_Out n D g → StrategyStepB n D 𝒯 g (TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g)) →
      SelRunB n D 𝒯 𝔈 ℓ (TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g) ++ E) F →
      SelRunB n D 𝒯 𝔈 ℓ (g :: E) F

/-- A run driven by a selector is a run of [II, Strategy 6.6] (`GlobalRunB`). -/
theorem SelRunB.globalRunB {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    {ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1} {E F : Expansion 3}
    (h : SelRunB n D 𝒯 𝔈 ℓ E F) : GlobalRunB n D 𝒯 E F := by
  induction h with
  | nil => exact GlobalRunB.nil
  | out hO _ ih => exact GlobalRunB.out hO.1 ih
  | step _ hs _ ih => exact GlobalRunB.step hs ih

/-- A run driven by a selector is determined by its inputs. -/
theorem SelRunB.functional {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    {ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1} {E F F' : Expansion 3}
    (h : SelRunB n D 𝒯 𝔈 ℓ E F) (h' : SelRunB n D 𝒯 𝔈 ℓ E F') : F = F' := by
  induction h generalizing F' with
  | nil => cases h'; rfl
  | out hO _ ih =>
    cases h' with
    | out _ h'' => rw [ih h'']
    | step hO' _ _ => exact absurd hO hO'
  | step hO _ _ ih =>
    cases h' with
    | out hO' _ => exact absurd hO' hO
    | step _ _ h'' => exact ih h''

/-! ## The cells of a graph with the invariant of a run -/

section Cells

open private Termination_inv1 Termination_not_qGraph Termination_td_at Termination_walk_ext_int
  Termination_sameBlock_of_dotFree Termination_randomFirstInt from RBM8D.GlobalExp.Termination
open private GlobalGood_isRight_of_mem_MIS from RBM8D.GlobalExp.GlobalGood

variable {n₀ : ℕ}

/-- In a graph without dotted edges the block normal form is the graph. -/
private theorem TerminationC_blockNorm {Γ : Graph 3 n₀} (hD : Γ.DotFree) : Γ.blockNorm = Γ := by
  have hfa : ∀ u, Γ.flatAtom u = u := by
    intro u
    cases u with
    | inr b => rfl
    | inl a =>
      have : Γ.anchor (.inl a) = none := by
        unfold Graph.anchor
        rw [List.find?_eq_none]
        intro b _ hb
        have hb' : Γ.SameBlock (.inl a) (.inr b) := by simpa using hb
        exact absurd (Termination_sameBlock_of_dotFree hD hb') (by simp)
      simp [Graph.flatAtom, this]
  have hfc : ∀ c ∈ Γ.comps, Γ.flatComp c = c := by
    intro c hc
    simp [Graph.flatComp, hD c hc, hfa]
  show (⟨Γ.comps.map Γ.flatComp, Γ.coeff⟩ : Graph 3 n₀) = Γ
  rw [List.map_congr_left hfc, List.map_id']

/-- **The inputs of Steps 1–2 have no dotted edge** (`locInput_dotFree`, read at a graph that is
not a `⊕/⊖`-recollision graph): a dotted edge at `⊗` is excluded by the diffusive edges at `⊗`,
one from `⊕` or `⊖` to an internal atom makes a `⊕/⊖`-recollision graph, one between internal
atoms is excluded by regularity, a loop by `Graph.Plain`, and one between `⊕` and `⊖` puts an
internal atom into their block, so that a dotted edge of that block joins an external to an
internal atom. -/
private theorem TerminationC_dotFree {D C : ℕ} {Γ : Graph 3 n₀} (hI : Γ.InvRun D)
    (hD : ¬ (D : ℤ) < Γ.ord) (hL : Γ.LabelFree) (hN : Γ.Normal C) (hP : Γ.Plain)
    (hR : ¬ Γ.IsRecollision {1, 2}) : Γ.DotFree := by
  intro c hc hk
  obtain ⟨hB, hT⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
  have key : ∀ d ∈ Γ.comps, d.kind = .dot → ¬ (d.x.isLeft = true ∧ d.y.isRight = true ∨
      d.y.isLeft = true ∧ d.x.isRight = true) := by
    intro d hd hdk h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 h1
      fin_cases a
      · have := Termination_td_at hT hd (Or.inl ha)
        rw [hdk] at this
        cases this
      · exact hR ⟨d, hd, hdk, Or.inl ⟨⟨1, by simp, ha⟩, h2⟩⟩
      · exact hR ⟨d, hd, hdk, Or.inl ⟨⟨2, by simp, ha⟩, h2⟩⟩
    · obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 h1
      fin_cases a
      · have := Termination_td_at hT hd (Or.inr ha)
        rw [hdk] at this
        cases this
      · exact hR ⟨d, hd, hdk, Or.inr ⟨⟨1, by simp, ha⟩, h2⟩⟩
      · exact hR ⟨d, hd, hdk, Or.inr ⟨⟨2, by simp, ha⟩, h2⟩⟩
  have hleft : ∀ u : Atom 3 n₀, u.isRight = false → u.isLeft = true := by
    intro u hu; cases u <;> simp_all
  by_cases hx : c.x.isRight = true <;> by_cases hy : c.y.isRight = true
  · rcases hN.1.noIntDot c hc hk with h | h
    · cases hcx : c.x <;> simp_all
    · cases hcy : c.y <;> simp_all
  · exact key c hc hk (Or.inr ⟨hleft _ (by simpa using hy), hx⟩)
  · exact key c hc hk (Or.inl ⟨hleft _ (by simpa using hx), hy⟩)
  · have hne : c.x ≠ c.y := (hP c hc).2.2.2.1 hk
    have hsb : Γ.SameBlock c.x c.y :=
      ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩).reachable
    obtain ⟨b, ⟨w⟩⟩ := hB.2.2.1.1 c.x c.y hne hsb
    obtain ⟨d, hd, hdk, hdd⟩ := Termination_walk_ext_int w (hleft _ (by simpa using hx)) rfl
    exact key d hd hdk hdd

/-- A removal of a redundant dotted edge needs a positive dot excess. -/
private theorem TerminationC_dotExcess_of_step {Γ Γ' : Graph 3 n₀} (h : DotNormStep Γ Γ') :
    Γ.dotExcess ≠ 0 := by
  obtain ⟨i, c, hc, hk, hr, rfl⟩ := h
  obtain ⟨-, he, -⟩ := drop_one Γ hc hk hr
  have he' : eL (Γ.comps.eraseIdx i) + 1 = eL Γ.comps := he
  have h0 := eL_nonneg (Γ.comps.eraseIdx i)
  have : Γ.dotExcess = eL Γ.comps := rfl
  omega

/-- A normal regular graph with the invariant of a run and no removal of a redundant dotted edge
has dot excess `0`. -/
private theorem TerminationC_dotExcess_zero {n D C : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h : ¬ ∃ Γ', DotNormStep g.2 Γ') :
    g.2.dotExcess = 0 := by
  by_contra hne
  obtain ⟨-, -, -, -, -, -, -, -, hP, -⟩ := hR
  obtain ⟨g', h1, -, h3, -⟩ := g.2.exists_dotNorm hN (hP hne)
  rcases h1.cases_head with rfl | ⟨g₁, hs, -⟩
  · exact hne h3
  · exact h ⟨g₁, hs⟩

/-- Plain below the error order, at dot excess `0`. -/
private theorem TerminationC_plain {n D : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (h0 : g.2.dotExcess = 0) (hD : ¬ (D : ℤ) < g.2.ord) :
    g.2.Plain :=
  hR.2.1.1.resolve_right (by rw [Graph.paperOrd_of_dotExcess h0]; exact hD)

/-- The clause on the external atoms and the charge pattern, with an internal atom. -/
private theorem TerminationC_ext {D : ℕ} {Γ : Graph 3 n₀} (hI : Γ.InvRun D) (h : n₀ ≠ 0) :
    Γ.ExtClause ∧ Γ.ColourInvB := by
  rcases hI with ⟨⟨-, hC, hE, -⟩, -⟩ | ⟨h0, -⟩ | ⟨-, hE, hC, -⟩
  · exact ⟨hE, hC⟩
  · exact absurd h0 h
  · exact ⟨hE, hC⟩

/-- An output from the invariant of a run, dot excess `0`, a disjunct of `Graph.StratLeafB` and a
class of [II, Def 6.3] (or the order `> D`). -/
private theorem TerminationC_out_of {n D C : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h0 : g.2.dotExcess = 0)
    (hS : g.2.StopsB n ∨ ((∃ C, g.2.Normal C) ∧ (D : ℤ) < g.2.ord) ∨
      (g.2.MISLocStdB ∧ ∀ i, ¬ g.2.Step2EdgeB i))
    (hcl : ((D : ℤ) < g.2.ord ∧ g.2.RgCheck ∧ (g.1 ≠ 0 → g.2.ExtClause ∧ g.2.ColourInvB)) ∨
      g.2.LeafR ∨ g.2.LeafA n ∨
      (g.2.LeafQ ∧ (g.1 ≠ 0 → g.2.ExtClause ∧ g.2.ColourInvB) ∧
        (g.1 = 0 → g.2.RootAtPlus ∧ g.2.QLabelAtPlus ∧ g.2.MinusProfile)) ∨ g.2.LeafDet) :
    TerminationC_Out n D g := by
  obtain ⟨-, -, hDC, hT, hND, hlab, -⟩ := id hR
  exact ⟨⟨h0, hS⟩, hDC, ⟨C, hN⟩, ⟨hT, h0, hND, hlab⟩,
    fun hD => TerminationC_plain hR h0 hD, hcl⟩

/-- **Err**: a graph of order `> D` with the invariant of a run is an output. -/
private theorem TerminationC_out_err {n D C : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h0 : g.2.dotExcess = 0)
    (hD : (D : ℤ) < g.2.ord) : TerminationC_Out n D g := by
  refine TerminationC_out_of hR hN h0 (Or.inr (Or.inl ⟨⟨C, hN⟩, hD⟩))
    (Or.inl ⟨hD, TerminationB_rgCheck g.2 fun h => ⟨(TerminationC_ext hR.1 h).1, hR.2.2.2.1⟩,
      fun h => TerminationC_ext hR.1 h⟩)

/-- **Q**: a `Q`-graph of order `≤ D` with the invariant of a run is an output. -/
private theorem TerminationC_out_q {n D C : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h0 : g.2.dotExcess = 0)
    (hQ : g.2.IsQGraph) : TerminationC_Out n D g := by
  obtain ⟨hI, hv, -, hT, -, -, -, hq, -, -⟩ := id hR
  have hpo := Graph.paperOrd_of_dotExcess h0
  refine TerminationC_out_of hR hN h0 (Or.inl ⟨⟨C, hN⟩, Or.inr (Or.inr (Or.inl hQ))⟩)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hQ, (hq hQ).1, (hq hQ).2, fun hpm => ?_,
      TerminationB_rgCheck g.2 fun h => ⟨(TerminationC_ext hI h).1, hT⟩⟩,
      fun h => TerminationC_ext hI h, hv.2.2.2.2.2⟩))))
  have := (hv.2.2.2.2.1 hpm).1
  rw [hpo] at this
  exact this

/-- The invariant `Graph.InvB'` and only diffusive edges at `⊗`, without labels and of order
`≤ D`. -/
private theorem TerminationC_invB {n D : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hL : g.2.LabelFree) (hD : ¬ (D : ℤ) < g.2.ord) :
    g.2.InvB' ∧ g.2.TensorDiffusive :=
  Termination_inv1 hR.1 (fun h => Termination_not_qGraph hL h.2) hD

/-- **A**: a graph without labels of order `≥ n + 1` and `≤ D` is an output. -/
private theorem TerminationC_out_a {n D C : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h0 : g.2.dotExcess = 0)
    (hL : g.2.LabelFree) (hD : ¬ (D : ℤ) < g.2.ord) (hn : (n : ℤ) + 1 ≤ g.2.ord) :
    TerminationC_Out n D g := by
  obtain ⟨hB, -⟩ := TerminationC_invB hR hL hD
  have hpo := Graph.paperOrd_of_dotExcess h0
  have hv := hR.2.1
  refine TerminationC_out_of hR hN h0 (Or.inl ⟨⟨C, hN⟩, Or.inr (Or.inl hn)⟩)
    (Or.inr (Or.inr (Or.inl ⟨hn, hL, hB.1, hB.2.2.1, hB.2.1,
      fun hr => hv.2.2.2.1 hL hr (by rw [hpo]; exact not_lt.1 hD), fun hpm => ?_⟩)))
  have := (hv.2.2.2.2.1 hpm).2 hL
  rw [hpo] at this
  exact this

/-- **R**: a `⊕/⊖`-recollision graph without labels of order `≤ D` is an output. -/
private theorem TerminationC_out_r {n D C : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h0 : g.2.dotExcess = 0)
    (hL : g.2.LabelFree) (hD : ¬ (D : ℤ) < g.2.ord) (hr : g.2.IsRecollision {1, 2}) :
    TerminationC_Out n D g := by
  obtain ⟨hB, -⟩ := TerminationC_invB hR hL hD
  have hpo := Graph.paperOrd_of_dotExcess h0
  have hv := hR.2.1
  refine TerminationC_out_of hR hN h0 (Or.inl ⟨⟨C, hN⟩, Or.inl hr⟩)
    (Or.inr (Or.inl ⟨hr, hL, hv.2.2.2.1 hL hr (by rw [hpo]; exact not_lt.1 hD), hB.2.2.1,
      hB.2.1, fun hpm => ?_⟩))
  have := (hv.2.2.2.2.1 hpm).2 hL
  rw [hpo] at this
  exact this

/-- **Det** ([II, Lemma 6.7], `nonstopB'`): a graph without labels of order `≤ n` and `≤ D` with a
locally standard minimal isolated subset, not a `⊕/⊖`-recollision graph, without blue solid edge
for Step 2, is an output. -/
private theorem TerminationC_out_det {n D C : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h0 : g.2.dotExcess = 0)
    (hL : g.2.LabelFree) (hD : ¬ (D : ℤ) < g.2.ord) (hn : g.2.ord ≤ n)
    (hM : g.2.MISLocStdB) (hr : ¬ g.2.IsRecollision {1, 2}) (hs : ∀ i, ¬ g.2.Step2EdgeB i) :
    TerminationC_Out n D g := by
  obtain ⟨hB, hT⟩ := TerminationC_invB hR hL hD
  have hpo := Graph.paperOrd_of_dotExcess h0
  have hgs : gsPM' g.2 := hR.2.1.2.2.1 hL (by rw [hpo]; exact hn)
  have hP := TerminationC_plain hR h0 hD
  obtain ⟨-, hdet⟩ := nonstopB' g.1 C g.2 hN hgs hB.2.1 hB.2.2.1 hT hM hr hs hP
  exact TerminationC_out_of hR hN h0 (Or.inr (Or.inr ⟨hM, hs⟩))
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, hgs, hdet, hB.2.2.1, hB.2.1⟩))))

/-- Two labels of a graph with at most one label are equal. -/
private theorem TerminationC_label_eq {Γ : Graph 3 n₀} (h1 : Γ.labels.length ≤ 1)
    {c d : Comp (Atom 3 n₀)} (hc : c ∈ Γ.comps) (hd : d ∈ Γ.comps) {l l' : PQ × Atom 3 n₀}
    (hl : c.label = some l) (hl' : d.label = some l') : l = l' := by
  have m1 : l ∈ Γ.labels := List.mem_dedup.2 (List.mem_filterMap.2 ⟨c, hc, hl⟩)
  have m2 : l' ∈ Γ.labels := List.mem_dedup.2 (List.mem_filterMap.2 ⟨d, hd, hl'⟩)
  generalize Γ.labels = L at m1 m2 h1
  match L, m1, m2, h1 with
  | [_], m1, m2, _ => rw [List.mem_singleton.1 m1, List.mem_singleton.1 m2]

/-- A graph with labels, the invariant of a run and dot excess `0` is a `Q`-graph, or of order
`> D`, or of the form `Γ₀ Q_x(Γ̃₀)` at an internal atom `x` without being a `Q`-graph. -/
private theorem TerminationC_labelled {n D : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (h0 : g.2.dotExcess = 0) (hL : ¬ g.2.LabelFree) :
    g.2.IsQGraph ∨ (D : ℤ) < g.2.ord ∨ ∃ x : Fin g.1, g.2.IsQFormAt (.inr x) ∧ ¬ g.2.IsQGraph := by
  obtain ⟨hI, -, -, -, -, hlab, hP, -⟩ := hR
  by_cases hQ : g.2.IsQGraph
  · exact Or.inl hQ
  by_cases hD : (D : ℤ) < g.2.ord
  · exact Or.inr (Or.inl hD)
  right; right
  simp only [Graph.LabelFree, not_forall] at hL
  obtain ⟨c, hc, hcl⟩ := hL
  obtain ⟨⟨pq, u⟩, hl⟩ := Option.ne_none_iff_exists'.1 hcl
  have hpq : pq = .Q := by
    cases pq
    · exact absurd hl (hP c hc u)
    · rfl
  subst hpq
  have hform : g.2.IsQFormAt u := by
    refine ⟨⟨c, hc, hl⟩, fun d hd => ?_⟩
    rcases hdl : d.label with - | l'
    · exact Or.inl rfl
    · exact Or.inr (by rw [TerminationC_label_eq hlab hd hc hdl hl])
  have hu : u.isRight = true := by
    rcases hI with ⟨⟨-, -, -, -, hLI⟩, -⟩ | ⟨-, hq⟩ | ⟨hpo, -⟩
    · have := hLI c hc
      rw [hl] at this
      simpa using this
    · exact absurd hq hQ
    · rw [Graph.paperOrd_of_dotExcess h0] at hpo
      exact absurd hpo hD
  obtain ⟨x, rfl⟩ : ∃ x, u = .inr x := by
    cases u with
    | inl a => simp at hu
    | inr x => exact ⟨x, rfl⟩
  exact ⟨x, hform, hQ⟩

/-- A standard neutral atom has degree `2`. -/
private theorem TerminationC_deg_of_std {k : ℕ} {Γ : Graph k n₀} {u : Atom k n₀}
    (h : Γ.stdNeutralAt u = true) : Γ.deg u = 2 := by
  unfold Graph.stdNeutralAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, h2⟩, -⟩, -⟩ := h
  rw [List.filter_filter] at h2
  unfold Graph.deg
  rw [← h2]
  congr 1
  refine List.filter_congr fun c _ => ?_
  rcases hk : c.kind <;> simp [Kind.isSolid]

/-- The local expansion chosen at an atom of the minimal isolated subset that is not locally
standard: `O_weight` at a weight, the transposed `O_GG` at the input shape of `O_GG`, otherwise
`O_multi-e`. -/
def TerminationC_locOp {k : ℕ} (Γ : Graph k n₀) (x : Atom k n₀) : Fin 5 :=
  open Classical in if 0 < Γ.wt x then 0 else if ∃ y y', Γ.GGInputAt x y y' then 4 else 1

/-- The chosen local expansion applies (`Graph.LocAdm`) at an atom without weight of degree
`≠ 0` that is not standard neutral of degree `2`, or at an atom with a weight. -/
private theorem TerminationC_locAdm {k : ℕ} {Γ : Graph k n₀} {x : Atom k n₀}
    (h : ¬ (Γ.wt x = 0 ∧ (Γ.deg x = 0 ∨ (Γ.deg x = 2 ∧ Γ.stdNeutralAt x = true)))) :
    Γ.LocAdm (TerminationC_locOp Γ x) x := by
  classical
  unfold TerminationC_locOp
  by_cases hw : 0 < Γ.wt x
  · simp only [hw, ite_true]
    exact Or.inl ⟨rfl, hw⟩
  have hw0 : Γ.wt x = 0 := by omega
  simp only [hw, ite_false]
  by_cases hg : ∃ y y', Γ.GGInputAt x y y'
  · simp only [hg, ite_true]
    exact Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hw0, hg⟩))
  · simp only [hg, ite_false]
    have hd : Γ.deg x ≠ 0 := fun h' => h ⟨hw0, Or.inl h'⟩
    refine Or.inr (Or.inl ⟨rfl, hw0, by omega, ?_⟩)
    by_cases h3 : 3 ≤ Γ.deg x
    · exact Or.inl h3
    · refine Or.inr ⟨?_, fun y y' hy => hg ⟨y, y', hy⟩⟩
      by_contra hs
      have hs' : Γ.stdNeutralAt x = true := by simpa using hs
      exact h ⟨hw0, Or.inr ⟨TerminationC_deg_of_std hs', hs'⟩⟩

/-- A non-expandable graph is locally standard at every internal atom. -/
private theorem TerminationC_not_nonExp {k : ℕ} {Γ : Graph k n₀} {x : Fin n₀}
    (h : ¬ (Γ.wt (.inr x) = 0 ∧
      (Γ.deg (.inr x) = 0 ∨ (Γ.deg (.inr x) = 2 ∧ Γ.stdNeutralAt (.inr x) = true)))) :
    ¬ Γ.NonExpandableB := by
  rintro ⟨⟨-, hw, hd⟩, -⟩
  refine h ⟨?_, ?_⟩
  · unfold Graph.wt
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have := hw c hc
    rcases hk : c.kind <;> simp_all [Kind.isWeight]
  · rcases (hd x).1 with h0 | h2
    · exact Or.inl h0
    · exact Or.inr ⟨h2, (hd x).2 h2⟩

/-- No `×`-dotted loop and no dotted edge: no `×`-dotted edge inside a block. -/
private theorem TerminationC_xdotApart {Γ : Graph 3 n₀} (hD : Γ.DotFree)
    (hl : ¬ ∃ i : Fin Γ.comps.length, Γ.comps[i].kind = .xdot ∧ Γ.comps[i].x = Γ.comps[i].y) :
    Γ.XdotApart := by
  intro c hc hk hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  exact hl ⟨⟨i, hi⟩, hk, Termination_sameBlock_of_dotFree hD hb⟩

/-- **Step 1 at a cell graph**: the local expansion chosen at an atom of the minimal isolated
subset that is not locally standard is admissible. -/
private theorem TerminationC_loc_adm {n D C : ℕ} {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ →
    TExpansion 3 n₀} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h0 : g.2.dotExcess = 0)
    (hL : g.2.LabelFree) (hD : ¬ (D : ℤ) < g.2.ord) (hn : g.2.ord ≤ n)
    (hr : ¬ g.2.IsRecollision {1, 2})
    (hl : ¬ ∃ i : Fin g.2.comps.length, g.2.comps[i].kind = .xdot ∧
      g.2.comps[i].x = g.2.comps[i].y)
    {x : Fin g.1} (hx : g.2.molRep (.inr x) ∈ g.2.toMG'.MIS)
    (hb : ¬ (g.2.wt (.inr x) = 0 ∧ (g.2.deg (.inr x) = 0 ∨
      (g.2.deg (.inr x) = 2 ∧ g.2.stdNeutralAt (.inr x) = true)))) :
    TerminationC_Adm n D 𝔈 g (.loc (TerminationC_locOp g.2 (.inr x)) x) := by
  have hpo := Graph.paperOrd_of_dotExcess h0
  have hP := TerminationC_plain hR h0 hD
  obtain ⟨hB, -⟩ := TerminationC_invB hR hL hD
  have hdf := TerminationC_dotFree hR.1 hD hL hN hP hr
  have hK := Termination_randomFirstInt hB.2.1 hdf
  refine ⟨?_, hD, ⟨C, hN⟩, hL, hP, hR.2.1.2.2.1 hL (by rw [hpo]; exact hn), hx, ?_,
    TerminationC_locAdm hb, TerminationC_xdotApart hdf hl⟩
  · rintro ⟨-, hs⟩
    rcases hs with hs | hs | hs | hs
    · exact hr hs
    · exact absurd hs (by omega)
    · exact Termination_not_qGraph hL hs
    · exact TerminationC_not_nonExp hb hs
  · refine ⟨fun h2 _ => ?_, fun _ _ c hc hs _ => hK c hc ?_⟩
    · exfalso
      unfold TerminationC_locOp at h2
      split_ifs at h2 <;> simp at h2
    · rcases hk : c.kind <;> simp_all [Kind.isSolid, Kind.isRandom]

/-- An atom whose molecule lies in the minimal isolated subset of `Graph.toMG'` is internal. -/
private theorem TerminationC_isRight_of_MIS {Γ : Graph 3 n₀} {u : Atom 3 n₀}
    (h : Γ.molRep u ∈ Γ.toMG'.MIS) : ∃ a, u = .inr a := by
  have := GlobalGood_isRight_of_mem_MIS Γ h
  cases u with
  | inl b => simp at this
  | inr a => exact ⟨a, rfl⟩

/-- Without an atom chosen by `TerminationC_alpha`, a graph without dotted edges with the charge
pattern of the block normal form has no blue solid edge for Step 2. -/
private theorem TerminationC_noStep2 {g : Σ n₀ : ℕ, Graph 3 n₀} (hD : g.2.DotFree)
    (hC : g.2.ColourInvB) (ha : (TerminationC_alpha g).isSome = false) :
    ∀ i, ¬ g.2.Step2EdgeB i := by
  intro i hi
  have hC' : g.2.ColourInv' := by
    have := hC
    unfold Graph.ColourInvB at this
    rwa [TerminationC_blockNorm hD] at this
  have h' := step2EdgeB'_of_colourInv g.1 g.2 i hC' hi
  obtain ⟨a, ha'⟩ := TerminationC_isRight_of_MIS hi.2.2.1
  have hq : ∃ a, TerminationC_Qual g.2 a := ⟨a, i, ha', h'⟩
  unfold TerminationC_alpha at ha
  simp [hq] at ha

end Cells


/-! ## Changes of names of the molecular graph -/

section Transport

open private TrH TrH.mk TrH.inj TrH.int_sub TrH.ext_sub TrH.ends_mem TrH.int_eq TrH.ext_eq
  TrH.ginj TrH.cls_eq TrH.ends_eq TrH.surj TrH.iso_iff TrH.pull TrH.induce TrH.mem_image
  TrH.image_ssubset_iff TrH.intPlus_fwd TrH.intPlus_bwd TrH.convert TrH.erase TrH.dc
  from RBM8D.Graph.MolCarry
open private GlobalGood_mis_sub from RBM8D.GlobalExp.GlobalGood

variable {V E V' E' : Type} [DecidableEq V'] {G : MGraph V E} {G' : MGraph V' E'} {f : V → V'}
  {g : E → E'} {T : Set V}

/-- Under a change of names, an internal vertex lies in the minimal isolated subset iff its image
does. -/
private theorem TerminationC_mis_iff (h : TrH G G' f g T) {v : V} (hv : v ∈ G.int) :
    f v ∈ G'.MIS ↔ v ∈ G.MIS := by
  classical
  have hT : ∀ S, S ⊆ G.int → ∀ w ∈ S, w ∈ T := fun S hS w hw => TrH.int_sub h w (hS hw)
  have hprop : ∀ P, P ⊆ G.int →
      (G'.IsProperIso G'.int (P.image f) ↔ G.IsProperIso G.int P) := by
    intro P hP
    unfold MGraph.IsProperIso
    rw [TrH.int_eq h, TrH.iso_iff h (hT P hP),
      TrH.image_ssubset_iff h (hT P hP) (hT _ le_rfl)]
  simp only [MGraph.MIS, Finset.mem_filter]
  constructor
  · rintro ⟨-, h2⟩
    refine ⟨hv, fun P hP => ?_⟩
    have hPi : P ⊆ G.int := hP.2.subset
    exact (TrH.mem_image h (hT P hPi) (TrH.int_sub h v hv)).1 (h2 _ ((hprop P hPi).2 hP))
  · rintro ⟨-, h2⟩
    refine ⟨by rw [TrH.int_eq h]; exact Finset.mem_image_of_mem f hv, fun P' hP' => ?_⟩
    obtain ⟨P, hPi, rfl⟩ := TrH.pull h hP'.2.subset
    exact Finset.mem_image_of_mem f (h2 P ((hprop P hPi).1 hP'))

/-- Under a change of names, the minimal isolated subset is the image of the minimal isolated
subset. -/
private theorem TerminationC_mis_image (h : TrH G G' f g T) : G'.MIS = G.MIS.image f := by
  ext w
  constructor
  · intro hw
    have hwi : w ∈ G'.int := GlobalGood_mis_sub _ hw
    rw [TrH.int_eq h] at hwi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hwi
    exact Finset.mem_image_of_mem f ((TerminationC_mis_iff h hv).1 hw)
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact (TerminationC_mis_iff h (GlobalGood_mis_sub _ hv)).2 hv

/-- A pre-deterministic order is carried by a change of names. -/
private theorem TerminationC_pdOrder [DecidableEq E] [DecidableEq E'] (h : TrH G G' f g T)
    {l : List E} (hl : G.IsPDOrder l) : G'.IsPDOrder (l.map g) := by
  obtain ⟨hnd, hmem, hr⟩ := hl
  have pl : ∀ x ∈ l, G.cls x ≠ none := fun x hx => by rw [((hmem x).1 hx).1]; simp
  refine ⟨hnd.map_on fun x hx y hy hxy => TrH.ginj h x y (pl x hx) (pl y hy) hxy,
    fun e' => ⟨fun he' => ?_, fun he' => ?_⟩, fun j hj => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
    exact TrH.intPlus_fwd h ((hmem x).1 hx)
  · obtain ⟨x, hx, rfl⟩ := TrH.intPlus_bwd h he'
    exact List.mem_map_of_mem ((hmem x).2 hx)
  · have hj' : j < l.length := by simpa using hj
    have hc := TrH.convert h (l := l.take j) (fun x hx => pl x (List.mem_of_mem_take hx))
    obtain ⟨c, d1, d2⟩ := hr j hj'
    have cx : (G.convert (l.take j)).cls l[j] ≠ none := by rw [c]; simp
    rw [List.getElem_map, ← List.map_take]
    exact ⟨by rw [TrH.cls_eq hc _ cx]; exact c, TrH.dc hc d1, TrH.dc (TrH.erase hc cx) d2⟩

/-- A pre-deterministic order of the subgraph induced on the minimal isolated subset is carried by
a change of names, with the image of its first edge first. -/
private theorem TerminationC_pdOrder_mis [DecidableEq V] [DecidableEq E] [DecidableEq E']
    (h : TrH G G' f g T) {l : List E} (hl : (G.induce G.MIS).IsPDOrder l) :
    (G'.induce G'.MIS).IsPDOrder (l.map g) := by
  rw [TerminationC_mis_image h]
  exact TerminationC_pdOrder
    (TrH.induce h fun v hv => TrH.int_sub h v (GlobalGood_mis_sub _ hv)) hl

end Transport

section IsoGraph

open private TrH TrH.mk TrH.int_eq TrH.inj TrH.int_sub from RBM8D.Graph.MolCarry
open private RunClauses_Iso RunClauses_SwapR RunClauses_eA RunClauses_eA_inl RunClauses_eA_inr
  RunClauses_iso_molRep RunClauses_iso_rho RunClauses_iso_sameMol RunClauses_iso_sameBlock
  RunClauses_iso_unpinned RunClauses_molRep_of_block RunClauses_swapR_eq
  from RBM8D.GlobalExp.RunClauses
open private Local_rho Local_rho_vtx Local_molRep_vtx Local_molRep_idem Local_molRep_eq_iff
  Local_anchor_none Local_anchor_some from RBM8D.GlobalExp.Local

variable {n : ℕ} {π : Equiv.Perm (Fin n)} {Γ Γ' : Graph 3 n}

/-- The class of the edge of `Graph.toMG'` given by a component. -/
private theorem TerminationC_cls_inl (Γ : Graph 3 n) (i : Fin Γ.comps.length) :
    Γ.toMG'.cls (.inl i) = if Γ.comps[i].kind = .dot then none else
      if Local_rho Γ Γ.comps[i].x = Local_rho Γ Γ.comps[i].y then none
      else Γ.comps[i].kind.mclass := by
  simp only [Graph.toMG', Graph.flatComp, Local_rho, Fin.getElem_fin]
  by_cases hd : Γ.comps[(i : ℕ)].kind = .dot
  · simp [hd]
  · simp only [hd, ite_false, false_or]
    by_cases hc : Γ.molRep (Γ.flatAtom Γ.comps[(i : ℕ)].x) =
      Γ.molRep (Γ.flatAtom Γ.comps[(i : ℕ)].y) <;> simp [hc]

/-- The ends of the edge of `Graph.toMG'` given by a component other than a dotted edge. -/
private theorem TerminationC_ends_inl (Γ : Graph 3 n) (i : Fin Γ.comps.length)
    (hd : Γ.comps[i].kind ≠ .dot) :
    Γ.toMG'.ends (.inl i) = (Local_rho Γ Γ.comps[i].x, Local_rho Γ Γ.comps[i].y) := by
  simp only [Fin.getElem_fin] at hd
  simp [Graph.toMG', Graph.flatComp, hd, Local_rho]

/-- **The molecular graph of a reordered graph** is a change of names of the molecular graph
(`Graph.toMG'`): the molecules are carried by the renumbering of the internal atoms, and the
components by a bijection of their positions that matches each component with its image. -/
private theorem TerminationC_trH (h : RunClauses_Iso π Γ Γ')
    (σ : Fin Γ.comps.length → Fin Γ'.comps.length)
    (hσ : ∀ i, RunClauses_SwapR (Γ.comps[i].map (RunClauses_eA π)) Γ'.comps[σ i])
    (hbij : Function.Bijective σ) :
    TrH Γ.toMG' Γ'.toMG' (fun v => Γ'.molRep (RunClauses_eA π v)) (Sum.map σ id)
      (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext) := by
  set F : Atom 3 n → Atom 3 n := fun v => Γ'.molRep (RunClauses_eA π v) with hFdef
  have hFmol : ∀ v, F (Γ.molRep v) = F v := RunClauses_iso_molRep h
  have hfix : ∀ v ∈ (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext : Set (Atom 3 n)), Γ.molRep v = v := by
    intro v hv
    rcases hv with hv | hv
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hv
      exact Local_molRep_idem Γ _
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hv
      rfl
  have hinj : Set.InjOn F (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext) := by
    intro v hv w hw hvw
    rw [← hfix v hv, ← hfix w hw, Local_molRep_eq_iff, ← RunClauses_iso_sameMol h,
      ← Local_molRep_eq_iff]
    exact hvw
  have hvtx : ∀ u, Local_rho Γ u ∈ (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext : Set (Atom 3 n)) := by
    intro u
    rcases Local_rho_vtx Γ u with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  have hrho : ∀ u, Local_rho Γ' (RunClauses_eA π u) = F (Local_rho Γ u) :=
    fun u => RunClauses_iso_rho h u
  -- the classes and ends of the edges of the components
  have hcl : ∀ i, Γ'.toMG'.cls (.inl (σ i)) = Γ.toMG'.cls (.inl i) := by
    intro i
    rw [TerminationC_cls_inl, TerminationC_cls_inl]
    rcases hσ i with he | ⟨hk, he⟩
    · rw [he]
      simp only [Comp.map, hrho, hinj.eq_iff (hvtx _) (hvtx _)]
    · rw [he]
      simp only [Comp.map, Fin.getElem_fin] at hk ⊢
      rcases hk with hk | hk | hk <;> simp [hk, Kind.mclass]
  have hen : ∀ i, Γ.toMG'.cls (.inl i) ≠ none →
      Γ'.toMG'.ends (.inl (σ i)) = (F (Γ.toMG'.ends (.inl i)).1, F (Γ.toMG'.ends (.inl i)).2) := by
    intro i hi
    have hd : Γ.comps[i].kind ≠ .dot := by
      intro hd
      rw [TerminationC_cls_inl, ite_eq_left hd] at hi
      exact hi rfl
    have hns : ¬ (Γ.comps[i].kind = .waved .s ∨ Γ.comps[i].kind = .dot ∨
        Γ.comps[i].kind = .xdot) := by
      rintro (hk | hk | hk) <;> rw [TerminationC_cls_inl] at hi <;>
        simp only [Fin.getElem_fin] at hk hi <;> simp [hk, Kind.mclass] at hi
    have he : Γ'.comps[σ i] = Γ.comps[i].map (RunClauses_eA π) := by
      rcases hσ i with he | ⟨hk, -⟩
      · exact he
      · exact absurd hk hns
    have hd' : Γ'.comps[σ i].kind ≠ .dot := by rw [he]; exact hd
    rw [TerminationC_ends_inl _ _ hd', TerminationC_ends_inl _ _ hd, he]
    simp only [Comp.map, hrho]
  have hanc : ∀ a : Fin 3, (Γ'.anchor (.inl a) = none ↔ Γ.anchor (.inl a) = none) := by
    intro a
    have hU := RunClauses_iso_unpinned h (.inl a)
    rw [Local_anchor_none, Local_anchor_none]
    unfold Graph.Unpinned at hU
    simpa [RunClauses_eA_inl] using hU
  have hclr : ∀ a : Fin 3, Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a) := by
    intro a
    simp only [Graph.toMG']
    rcases h1 : Γ.anchor (.inl a) with - | b <;> rcases h2 : Γ'.anchor (.inl a) with - | b'
    · rfl
    · exact absurd ((hanc a).2 h1) (by rw [h2]; simp)
    · exact absurd ((hanc a).1 h2) (by rw [h1]; simp)
    · rfl
  have henr : ∀ a : Fin 3, Γ.toMG'.cls (.inr a) ≠ none →
      Γ'.toMG'.ends (.inr a) = (F (Γ.toMG'.ends (.inr a)).1, F (Γ.toMG'.ends (.inr a)).2) := by
    intro a ha
    rcases h1 : Γ.anchor (.inl a) with - | b
    · simp [Graph.toMG', h1] at ha
    · rcases h2 : Γ'.anchor (.inl a) with - | b'
      · exact absurd ((hanc a).1 h2) (by rw [h1]; simp)
      · simp only [Graph.toMG', h1, h2]
        refine Prod.ext ?_ rfl
        show Γ'.molRep (.inr b') = F (Γ.molRep (.inr b))
        rw [hFmol]
        have hbl : Γ'.SameBlock (.inr b') (RunClauses_eA π (.inr b)) :=
          (Local_anchor_some h2).symm.trans
            ((RunClauses_iso_sameBlock h (.inl a) (.inr b)).2 (Local_anchor_some h1))
        exact RunClauses_molRep_of_block Γ' hbl (Or.inr ⟨rfl, rfl⟩)
  refine TrH.mk hinj (fun v hv => Or.inl hv) (fun v hv => Or.inr hv) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro (i | a) he
    · have hd : Γ.comps[i].kind ≠ .dot := by
        intro hd
        rw [TerminationC_cls_inl, ite_eq_left hd] at he
        exact he rfl
      rw [TerminationC_ends_inl _ _ hd]
      exact ⟨hvtx _, hvtx _⟩
    · rcases h1 : Γ.anchor (.inl a) with - | b
      · simp [Graph.toMG', h1] at he
      · simp only [Graph.toMG', h1]
        refine ⟨?_, Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)⟩
        rcases Local_molRep_vtx Γ (.inr b) with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
  · ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a', rfl⟩
      refine ⟨Γ.molRep (.inr (π.symm a')), ⟨_, rfl⟩, ?_⟩
      show F (Γ.molRep _) = _
      rw [hFmol]
      simp [hFdef, RunClauses_eA_inr]
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨π a, by show _ = F (Γ.molRep _); rw [hFmol]; rfl⟩
  · ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨.inl a, ⟨a, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  · rintro (i | a) (j | b) - - he
    · simp only [Sum.map_inl, Sum.inl.injEq] at he
      rw [hbij.1 he]
    · simp at he
    · simp at he
    · simpa using he
  · rintro (i | a) -
    · exact hcl i
    · exact hclr a
  · rintro (i | a) he
    · exact Or.inl (hen i he)
    · exact Or.inl (henr a he)
  · rintro (j | a) he
    · obtain ⟨i, rfl⟩ := hbij.2 j
      exact ⟨.inl i, by rw [← hcl i]; exact he, rfl⟩
    · exact ⟨.inr a, by rw [← hclr a]; exact he, rfl⟩

open private TrH from RBM8D.Graph.MolCarry in
open private TerminationB_eA_beq TerminationB_iso_deg TerminationB_iso_std
  from RBM8D.GlobalExp.TerminationB in
open private RunClauses_iso_count RunClauses_iso_mem' from RBM8D.GlobalExp.RunClauses in
open private GlobalGood_mis_sub from RBM8D.GlobalExp.GlobalGood in
open private Local_mem_int from RBM8D.GlobalExp.Local in
/-- **A locally standard minimal isolated subset is carried by a reordering**: the molecules of
the minimal isolated subset are the images, and the weights, degrees and standard neutral atoms
are read at the images of the atoms. -/
private theorem TerminationC_iso_misLocStd (h : RunClauses_Iso π Γ Γ')
    (σ : Fin Γ.comps.length → Fin Γ'.comps.length)
    (hσ : ∀ i, RunClauses_SwapR (Γ.comps[i].map (RunClauses_eA π)) Γ'.comps[σ i])
    (hbij : Function.Bijective σ) (hM : Γ.MISLocStdB) : Γ'.MISLocStdB := by
  have hT := TerminationC_trH h σ hσ hbij
  refine ⟨fun c' hc' => ?_, fun i' hi' => ?_⟩
  · obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
    rw [(RunClauses_swapR_eq hr).2.1]
    simp [Comp.map, hM.1 c hc]
  · set u : Atom 3 n := .inr (π.symm i') with hu
    have he : RunClauses_eA π u = .inr i' := by
      rw [hu, RunClauses_eA_inr]; simp
    have hmr : Γ'.molRep (.inr i') = Γ'.molRep (RunClauses_eA π (Γ.molRep u)) := by
      rw [RunClauses_iso_molRep h, he]
    have hint : Γ.molRep u ∈ Γ.toMG'.int := Local_mem_int.2 ⟨_, rfl⟩
    have hmis : Γ.molRep u ∈ Γ.toMG'.MIS := by
      rw [← TerminationC_mis_iff hT hint]
      rw [← hmr]
      exact hi'
    obtain ⟨hw, hd⟩ := hM.2 (π.symm i') hmis
    have hwt : Γ'.wt (RunClauses_eA π u) = Γ.wt u := by
      unfold Graph.wt
      rw [RunClauses_iso_count h]
      · congr 1
        refine List.filter_congr fun c _ => ?_
        simp only [Function.comp_apply, Comp.map, TerminationB_eA_beq]
      · intro c c' hr
        rcases hr with rfl | ⟨hk, rfl⟩
        · rfl
        · rcases hk with hk | hk | hk <;> simp [hk]
    rw [he] at hwt
    rw [hwt, ← he, TerminationB_iso_deg h, TerminationB_iso_std h]
    exact ⟨hw, hd⟩

open private TrH from RBM8D.Graph.MolCarry in
open private RunClauses_iso_mem' RunClauses_eA_isRight from RBM8D.GlobalExp.RunClauses in
open private GlobalGood_mis_sub from RBM8D.GlobalExp.GlobalGood in
/-- **The blue solid edge of Step 2 is carried by a reordering** (`Graph.Step2EdgeB'`): its atoms
lie in the image of the minimal isolated subset, and a pre-deterministic order of the subgraph
induced on it is carried with the image of the edge first. -/
private theorem TerminationC_iso_step2 (h : RunClauses_Iso π Γ Γ')
    (σ : Fin Γ.comps.length → Fin Γ'.comps.length)
    (hσ : ∀ i, RunClauses_SwapR (Γ.comps[i].map (RunClauses_eA π)) Γ'.comps[σ i])
    (hbij : Function.Bijective σ) {i : Fin Γ.comps.length} (hS : Γ.Step2EdgeB' i) :
    Γ'.Step2EdgeB' (σ i) := by
  classical
  have hT := TerminationC_trH h σ hσ hbij
  obtain ⟨⟨hk, hx, hy, hm⟩, hc⟩ := hS
  have he : Γ'.comps[σ i] = Γ.comps[i].map (RunClauses_eA π) := by
    rcases hσ i with he | ⟨hk', -⟩
    · exact he
    · simp only [Comp.map] at hk'
      rw [hk] at hk'
      rcases hk' with h' | h' | h' <;> cases h'
  have hmis : ∀ u, Γ.molRep u ∈ Γ.toMG'.MIS →
      Γ'.molRep (RunClauses_eA π u) ∈ Γ'.toMG'.MIS := by
    intro u hu
    rw [← RunClauses_iso_molRep h]
    exact (TerminationC_mis_iff hT (GlobalGood_mis_sub _ hu)).2 hu
  refine ⟨⟨by rw [he]; exact hk, by rw [he]; exact hmis _ hx, by rw [he]; exact hmis _ hy, ?_⟩,
    fun c' hc' hcond => ?_⟩
  · rcases hm with hm | ⟨l, hl, hhd⟩
    · left
      rw [he]
      exact (RunClauses_iso_sameMol h _ _).2 hm
    · right
      refine ⟨l.map (Sum.map σ id), TerminationC_pdOrder_mis hT hl, ?_⟩
      rw [List.head?_map, hhd]
      rfl
  · obtain ⟨c, hcm, hr⟩ := RunClauses_iso_mem' h hc'
    obtain ⟨hk', -, -, hxy, -⟩ := RunClauses_swapR_eq hr
    rw [he] at hcond
    simp only [Comp.map] at hk' hxy hcond
    have hcond' : c.kind = .G .minus ∧ c.y = Γ.comps[i].y ∨
        c.kind = .waved .s ∧ (c.x = Γ.comps[i].y ∨ c.y = Γ.comps[i].y) := by
      have hinj := (RunClauses_eA π).injective
      rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have hcc : c' = c.map (RunClauses_eA π) := by
          rcases hr with he' | ⟨hk'', -⟩
          · exact he'
          · exfalso
            simp only [Comp.map] at hk''
            rw [← hk', h1] at hk''
            rcases hk'' with h' | h' | h' <;> cases h'
        refine ⟨hk' ▸ h1, ?_⟩
        rw [hcc] at h2
        exact hinj h2
      · right
        refine ⟨hk' ▸ h1, ?_⟩
        rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3, h4] at h2 <;>
          rcases h2 with h2 | h2
        · exact Or.inl (hinj h2)
        · exact Or.inr (hinj h2)
        · exact Or.inr (hinj h2)
        · exact Or.inl (hinj h2)
    obtain ⟨h1, h2⟩ := hc c hcm hcond'
    rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3, h4, RunClauses_eA_isRight,
      RunClauses_eA_isRight]
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h1⟩

end IsoGraph


/-! ## The atom `α` of the `t`-variable: the generated grid -/

section Grid

variable {n₀ : ℕ}

/-- The charge of a solid edge. -/
private def TerminationC_ch : Kind → Charge
  | .G ch => ch
  | _ => .plus

/-- The component `c` has an end at `u`. -/
private def TerminationC_at {k : ℕ} (u : Atom k n₀) (c : Comp (Atom k n₀)) : Bool :=
  c.x == u || c.y == u

/-- Without solid loops, the ends at `u` of the solid edges attached to `u` (`Graph.ends`) are read
from the list of these edges. -/
private theorem TerminationC_ends_eq {k : ℕ} (Γ : Graph k n₀) (u : Atom k n₀)
    (hns : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) :
    Γ.ends u = (Γ.comps.filter fun c => c.kind.isSolid && TerminationC_at u c).map
      fun c => (decide (c.x = u), TerminationC_ch c.kind) := by
  unfold Graph.ends
  generalize Γ.comps = L at hns
  induction L with
  | nil => rfl
  | cons c L ih =>
    have hns' : ∀ d ∈ L, d.kind.isSolid = true → d.x ≠ d.y :=
      fun d hd => hns d (List.mem_cons_of_mem _ hd)
    have hc := hns c List.mem_cons_self
    rw [List.filterMap_cons, List.filter_cons, ih hns']
    rcases hk : c.kind with ch | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
      simp only [Kind.isSolid, Bool.false_and, Bool.true_and] <;> try rfl
    have hc' := hc (by rw [hk]; rfl)
    by_cases h1 : c.x = u
    · have h2 : c.y ≠ u := fun h2 => hc' (h1.trans h2.symm)
      simp [TerminationC_at, h1, h2, TerminationC_ch, hk]
    · by_cases h2 : c.y = u
      · simp [TerminationC_at, h1, h2, TerminationC_ch, hk]
      · simp [TerminationC_at, h1, h2]

/-- **The solid edges at a standard neutral atom** entered by a blue solid edge `c₀`: the solid
edges attached to `u` are `c₀` and one red solid edge `c₂` that also enters `u` (two matched solid
edges of opposite charges, [I, Def 3.17]). -/
private theorem TerminationC_std_solid {Γ : Graph 3 n₀} {u : Atom 3 n₀}
    (hns : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) (hstd : Γ.stdNeutralAt u = true)
    {c₀ : Comp (Atom 3 n₀)} (hc₀ : c₀ ∈ Γ.comps) (hk₀ : c₀.kind = .G .plus) (hy₀ : c₀.y = u) :
    ∃ c₂ ∈ Γ.comps, c₂.kind = .G .minus ∧ c₂.y = u ∧ c₂.x ≠ u ∧
      (Γ.comps.filter fun c => c.kind.isSolid && TerminationC_at u c).Perm [c₀, c₂] := by
  set S := Γ.comps.filter fun c => c.kind.isSolid && TerminationC_at u c with hS
  have hlen : S.length = 2 := by
    have := TerminationC_deg_of_std hstd
    unfold Graph.deg at this
    exact this
  have hends := TerminationC_ends_eq Γ u hns
  have hmem : ∀ c ∈ S, c ∈ Γ.comps ∧ c.kind.isSolid = true ∧ (c.x = u ∨ c.y = u) := by
    intro c hc
    rw [hS, List.mem_filter] at hc
    simp only [Bool.and_eq_true, TerminationC_at, Bool.or_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2⟩
  have hc₀S : c₀ ∈ S := by
    rw [hS, List.mem_filter]
    simp [hc₀, hk₀, Kind.isSolid, TerminationC_at, hy₀]
  have hx₀ : c₀.x ≠ u := fun h => hns c₀ hc₀ (by rw [hk₀]; rfl) (h.trans hy₀.symm)
  obtain ⟨d₁, d₂, hd⟩ := List.length_eq_two.1 hlen
  have hm₁ := hmem d₁ (by rw [hd]; simp)
  have hm₂ := hmem d₂ (by rw [hd]; simp)
  have hst := hstd
  unfold Graph.stdNeutralAt at hst
  rw [hends, ← hS, hd] at hst
  simp only [List.map_cons, List.map_nil, Bool.and_eq_true] at hst
  obtain ⟨-, hme⟩ := hst
  have hsolid : ∀ c : Comp (Atom 3 n₀), c.kind.isSolid = true → ∃ ch, c.kind = .G ch := by
    intro c hc
    rcases hk : c.kind <;> simp_all [Kind.isSolid]
  rw [hd] at hc₀S
  rcases List.mem_pair.1 hc₀S with rfl | rfl
  · obtain ⟨ch, hch⟩ := hsolid d₂ hm₂.2.1
    simp only [hx₀, hk₀, hch, TerminationC_ch, decide_false, matchedEnds] at hme
    by_cases hx₂ : d₂.x = u
    · simp [hx₂] at hme
    · cases ch
      · simp [hx₂] at hme
      · have hy₂ : d₂.y = u := hm₂.2.2.resolve_left hx₂
        exact ⟨d₂, hm₂.1, hch, hy₂, hx₂, by rw [hd]⟩
  · obtain ⟨ch, hch⟩ := hsolid d₁ hm₁.2.1
    simp only [hx₀, hk₀, hch, TerminationC_ch, decide_false, matchedEnds] at hme
    by_cases hx₁ : d₁.x = u
    · simp [hx₁] at hme
    · cases ch
      · simp [hx₁] at hme
      · have hy₁ : d₁.y = u := hm₁.2.2.resolve_left hx₁
        exact ⟨d₁, hm₁.1, hch, hy₁, hx₁, by rw [hd]; exact List.Perm.swap _ _ _⟩


/-- **The waved edge at a standard neutral atom**: exactly one waved edge `s` is attached to `u`,
and every other component attached to `u` other than a `×`-dotted edge is a solid edge. -/
private theorem TerminationC_std_s {Γ : Graph 3 n₀} {u : Atom 3 n₀}
    (hstd : Γ.stdNeutralAt u = true) :
    ∃ cS ∈ Γ.comps, cS.kind = .waved .s ∧ (cS.x = u ∨ cS.y = u) ∧
      (∀ c ∈ Γ.comps, (c.x = u ∨ c.y = u) → c.kind ≠ .xdot → c.kind.isSolid = true ∨ c = cS) ∧
      (Γ.comps.filter fun c => c.kind == .waved .s && TerminationC_at u c) = [cS] := by
  set L := Γ.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u) with hL
  have hst := hstd
  unfold Graph.stdNeutralAt at hst
  simp only [Bool.and_eq_true, beq_iff_eq] at hst
  obtain ⟨⟨⟨h3, h2⟩, h1⟩, -⟩ := hst
  rw [← hL] at h3 h2 h1
  have hns : (L.filter fun c => !c.kind.isSolid).length = 1 := by
    have := List.length_eq_length_filter_add (l := L) (fun c => c.kind.isSolid)
    omega
  obtain ⟨cS, hcS⟩ := List.length_eq_one_iff.1 hns
  have hsS : (L.filter fun c => c.kind == .waved .s) = [cS] := by
    obtain ⟨d, hd⟩ := List.length_eq_one_iff.1 h1
    have hdm : d ∈ L.filter fun c => !c.kind.isSolid := by
      have : d ∈ L.filter fun c => c.kind == .waved .s := by rw [hd]; simp
      rw [List.mem_filter] at this ⊢
      refine ⟨this.1, ?_⟩
      have hk : d.kind = .waved .s := by simpa using this.2
      simp [hk, Kind.isSolid]
    rw [hcS, List.mem_singleton] at hdm
    rw [hd, hdm]
  have hmem : cS ∈ L.filter fun c => c.kind == .waved .s := by rw [hsS]; simp
  rw [List.mem_filter, hL, List.mem_filter] at hmem
  obtain ⟨⟨hc, hc2⟩, hc3⟩ := hmem
  have hk : cS.kind = .waved .s := by simpa using hc3
  have hc2' := hc2
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc2'
  refine ⟨cS, hc, hk, hc2'.2, ?_, ?_⟩
  · intro c hcm hu hx
    by_cases hs : c.kind.isSolid = true
    · exact Or.inl hs
    · right
      have : c ∈ L.filter fun c => !c.kind.isSolid := by
        rw [List.mem_filter, hL, List.mem_filter]
        refine ⟨⟨hcm, ?_⟩, by simpa using hs⟩
        simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact ⟨hx, hu⟩
      rw [hcS, List.mem_singleton] at this
      exact this
  · rw [← hsS, hL, List.filter_filter]
    refine List.filter_congr fun c _ => ?_
    by_cases hk : c.kind = .waved .s
    · simp [hk, TerminationC_at]
    · have hk' : (c.kind == Kind.waved Wave.s) = false := by simpa using hk
      simp [hk']

/-- The orders of the kinds of [II, Def 3.2]: nonnegative, at least `2` for waved and diffusive
edges, and `0` only for weights and `×`-dotted edges. -/
private theorem TerminationC_ord_tkind {V : Type*} {N : ℕ} {c : Comp V} (h : c.isTKind N = true) :
    0 ≤ c.kind.ord ∧
      ((c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) → 2 ≤ c.kind.ord) ∧
      (c.kind.ord < 1 → c.kind.isWeight = true ∨ c.kind = .xdot) := by
  unfold Comp.isTKind at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  generalize c.kind = κ at h ⊢
  cases κ with
  | theta o => ?_
  | _ => simp_all [Kind.ord, Kind.joinsMol, Kind.isDiffusive, Kind.isWeight]
  simp only at h
  simp only [Kind.ord, Kind.isDiffusive, Kind.isWeight, Bool.false_eq_true,
    reduceCtorEq, or_self, imp_false, not_lt]
  have h4 : ∀ j ∈ o, 4 ≤ j := by
    intro j hj
    simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact (h j hj).1.1
  have : 4 * (o.length : ℤ) ≤ (o.sum : ℤ) := by
    clear h
    induction o with
    | nil => simp
    | cons a o ih =>
      have ha := h4 a List.mem_cons_self
      have := ih (fun j hj => h4 j (List.mem_cons_of_mem _ hj))
      simp only [List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
      omega
  omega

/-- The connected graph `SimpleGraph.fromRel R` on a finite type has at least `|V| - 1` edges, each
given by a pair of `L`. -/
private theorem TerminationC_card_le {V : Type} [Fintype V] [DecidableEq V] {R : V → V → Prop}
    (L : List (V × V)) (hR : ∀ u v, R u v → (u, v) ∈ L) (hc : (SimpleGraph.fromRel R).Connected) :
    Fintype.card V ≤ L.length + 1 := by
  have hcard := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at hcard
  have hsub : (SimpleGraph.fromRel R).edgeSet ⊆ ↑((L.map fun p => s(p.1, p.2)).toFinset) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
      rcases he.2 with h' | h'
      · exact ⟨(u, v), hR u v h', rfl⟩
      · exact ⟨(v, u), hR v u h', Sym2.eq_swap⟩
  have hedge : Nat.card (SimpleGraph.fromRel R).edgeSet ≤ L.length := by
    rw [Nat.card_coe_set_eq]
    calc Set.ncard (SimpleGraph.fromRel R).edgeSet
        ≤ Set.ncard (↑((L.map fun p => s(p.1, p.2)).toFinset) : Set (Sym2 V)) :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (L.map fun p => s(p.1, p.2)).toFinset.card := Set.ncard_coe_finset _
      _ ≤ (L.map fun p => s(p.1, p.2)).length := List.toFinset_card_le _
      _ = L.length := List.length_map _
  omega

/-- Reachability is carried by a map of adjacencies to reachability. -/
private theorem TerminationC_reach_of {V : Type*} {G G' : SimpleGraph V}
    (h : ∀ u v, G'.Adj u v → G.Reachable u v) {u v : V} (hr : G'.Reachable u v) :
    G.Reachable u v := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons ha _ ih => exact (h _ _ ha).trans ih

/-- The waved and diffusive components. -/
private def TerminationC_wt {V : Type*} (c : Comp V) : Bool :=
  decide (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true)


/-- The sum of the orders of components of the kinds of [II, Def 3.2] is at least the number of
waved and diffusive ones plus the number of those of order `≥ 1`. -/
private theorem TerminationC_sum_ge {V : Type*} {N : ℕ} (L : List (Comp V))
    (hK : ∀ c ∈ L, c.isTKind N = true) :
    (((L.filter TerminationC_wt).length : ℤ) +
      (L.filter fun c => decide (1 ≤ c.kind.ord)).length) ≤ (L.map fun c => c.kind.ord).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have hc := TerminationC_ord_tkind (hK c List.mem_cons_self)
    have ih := ih (fun d hd => hK d (List.mem_cons_of_mem _ hd))
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases h1 : TerminationC_wt c = true
    · have h2 := hc.2.1 (by simpa [TerminationC_wt] using h1)
      have h3 : decide (1 ≤ c.kind.ord) = true := by simp; omega
      simp only [h1, h3, ite_true, List.length_cons]
      push_cast
      omega
    · have h1' : TerminationC_wt c = false := by simpa using h1
      by_cases h2 : 1 ≤ c.kind.ord
      · have h3 : decide (1 ≤ c.kind.ord) = true := by simp; omega
        simp only [h1', h3, ite_true, Bool.false_eq_true, ite_false, List.length_cons]
        push_cast
        omega
      · have h3 : decide (1 ≤ c.kind.ord) = false := by simp; omega
        simp only [h1', h3, Bool.false_eq_true, ite_false]
        omega

/-- **The order bound of Steps 2–3** ([II, Lemma 6.8]; [II, (2.5)]): a normal regular plain graph
without dotted edges, with the kinds of [II, Def 3.2] and the clause on the external atoms, with two
distinct solid edges between internal atoms, has scaling order `≥ 4`. The internal atoms and `⊗`
are joined by at least `n₀` waved and diffusive edges (regularity and the diffusive edge at `⊗`),
and all atoms by at least `n₀ + 2` components of order `≥ 1` other than the two solid edges
(connectedness). -/
private theorem TerminationC_four_le_ord {C N : ℕ} {Γ : Graph 3 n₀} (hN : Γ.Normal C)
    (hD : Γ.DotFree) (hP : Γ.Plain) (hK : Γ.TKinds N) (hE : Γ.ExtClause)
    {c₀ c₂ : Comp (Atom 3 n₀)} (h0 : c₀ ∈ Γ.comps) (h2 : c₂ ∈ Γ.comps) (hne : c₀ ≠ c₂)
    (hs0 : c₀.kind.ord = 1) (hs2 : c₂.kind.ord = 1)
    (hi0 : c₀.x.isRight = true ∧ c₀.y.isRight = true)
    (hi2 : c₂.x.isRight = true ∧ c₂.y.isRight = true) : 4 ≤ Γ.ord := by
  classical
  have hK' : ∀ c ∈ Γ.comps, c.isTKind N = true := fun c hc => List.all_eq_true.1 hK c hc
  set W := Γ.comps.filter TerminationC_wt with hW
  set U := Γ.comps.filter fun c => decide (1 ≤ c.kind.ord) with hU
  set U' := (U.erase c₀).erase c₂ with hU'
  -- the sum of the orders
  have hsum : ((W.length : ℤ) + U.length) ≤ (Γ.comps.map fun c => c.kind.ord).sum :=
    TerminationC_sum_ge Γ.comps hK'
  -- the internal atoms are joined by waved and diffusive edges
  have hint : ∀ a b : Fin n₀, ∀ {R : Atom 3 n₀ → Atom 3 n₀ → Prop},
      (∀ c ∈ W, R c.x c.y) → (SimpleGraph.fromRel R).Reachable (.inr a) (.inr b) := by
    intro a b R hR
    refine TerminationC_reach_of (fun u v huv => ?_) (hN.1.internal a b)
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at huv
    obtain ⟨hne', ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := huv
    · refine SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne', Or.inl ?_⟩)
      exact hR c (List.mem_filter.2 ⟨hc, by simpa [TerminationC_wt] using hk⟩)
    · refine SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne', Or.inr ?_⟩)
      exact hR c (List.mem_filter.2 ⟨hc, by simpa [TerminationC_wt] using hk⟩)
  obtain ⟨a₀, ha₀⟩ : ∃ a : Fin n₀, c₀.x = .inr a := by
    rcases h : c₀.x with b | a
    · rw [h] at hi0; simp at hi0
    · exact ⟨a, rfl⟩
  -- the diffusive edge at `⊗`
  have hsb : ∀ u v, Γ.SameBlock u v → u = v := by
    intro u v huv
    obtain ⟨w⟩ := huv
    cases w with
    | nil => rfl
    | cons hadj _ =>
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨-, ⟨d, hd, hk, -⟩ | ⟨d, hd, hk, -⟩⟩ := hadj <;> exact absurd hk (hD d hd)
  have hunp : ∀ i : Fin 3, Γ.Unpinned (.inl i) :=
    fun i => ⟨rfl, fun b hb => by simpa using hsb _ _ hb⟩
  obtain ⟨cT, hcT, hdT, hcTe⟩ := (hE.2.2.1 (hunp 0)).1
  obtain ⟨z, hz⟩ : ∃ z : Fin n₀, (cT.x = .inl 0 ∧ cT.y = .inr z) ∨ (cT.y = .inl 0 ∧ cT.x = .inr z) := by
    rcases hcTe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hy : cT.y with i | z
      · exact absurd (hunp i) (by rw [← hy]; exact h2)
      · exact ⟨z, Or.inl ⟨h1, rfl⟩⟩
    · rcases hx : cT.x with i | z
      · exact absurd (hunp i) (by rw [← hx]; exact h2)
      · exact ⟨z, Or.inr ⟨h1, rfl⟩⟩
  have hcTW : cT ∈ W := List.mem_filter.2 ⟨hcT, by simp [TerminationC_wt, hdT]⟩
  -- the bound on the waved and diffusive edges
  have hW1 : n₀ ≤ W.length := by
    let R : Atom 3 n₀ → Atom 3 n₀ → Prop := fun u v =>
      (∃ c ∈ W, c.x = u ∧ c.y = v) ∨ (u = .inl 0 ∧ (v = .inl 1 ∨ v = .inl 2))
    have hc : (SimpleGraph.fromRel R).Connected := by
      have hr : ∀ u, (SimpleGraph.fromRel R).Reachable (.inr a₀) u := by
        have hW' : ∀ c ∈ W, R c.x c.y := fun c hc => Or.inl ⟨c, hc, rfl, rfl⟩
        have hT0 : (SimpleGraph.fromRel R).Reachable (.inr z) (.inl 0) := by
          refine SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, ?_⟩)
          rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr (Or.inl ⟨cT, hcTW, h1, h2⟩)
          · exact Or.inl (Or.inl ⟨cT, hcTW, h2, h1⟩)
        intro u
        rcases u with i | b
        · refine (hint a₀ z hW').trans (hT0.trans ?_)
          fin_cases i
          · rfl
          · exact SimpleGraph.Adj.reachable
              ((SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl (Or.inr ⟨rfl, Or.inl rfl⟩)⟩)
          · exact SimpleGraph.Adj.reachable
              ((SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl (Or.inr ⟨rfl, Or.inr rfl⟩)⟩)
        · exact hint a₀ b hW'
      have : Nonempty (Atom 3 n₀) := ⟨.inr a₀⟩
      exact ⟨fun u v => (hr u).symm.trans (hr v)⟩
    have := TerminationC_card_le (R := R) (W.map (fun c => (c.x, c.y)) ++
      [(.inl 0, .inl 1), (.inl 0, .inl 2)]) (fun u v h => by
        rcases h with ⟨c, hc, rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
        · exact List.mem_append_left _ (List.mem_map.2 ⟨c, hc, rfl⟩)
        · simp
        · simp) hc
    simp only [Fintype.card_sum, Fintype.card_fin, List.length_append, List.length_map,
      List.length_cons, List.length_nil] at this
    omega
  -- the bound on the components of order `≥ 1`
  have hc0U : c₀ ∈ U := List.mem_filter.2 ⟨h0, by simp [hs0]⟩
  have hc2U : c₂ ∈ U.erase c₀ := (List.mem_erase_of_ne hne.symm).2
    (List.mem_filter.2 ⟨h2, by simp [hs2]⟩)
  have hlen : U.length = U'.length + 2 := by
    rw [hU', List.length_erase_of_mem hc2U, List.length_erase_of_mem hc0U]
    have : 2 ≤ U.length := by
      have h1 := List.length_erase_of_mem hc0U
      have h2 : 0 < (U.erase c₀).length := List.length_pos_of_mem hc2U
      omega
    omega
  have hWU : ∀ c ∈ W, c ∈ U' := by
    intro c hc
    rw [hW, List.mem_filter] at hc
    have ho := (TerminationC_ord_tkind (hK' c hc.1)).2.1 (by simpa [TerminationC_wt] using hc.2)
    have hn0 : c ≠ c₀ := by
      rintro rfl
      have := hs0
      omega
    have hn2 : c ≠ c₂ := by
      rintro rfl
      have := hs2
      omega
    rw [hU', List.mem_erase_of_ne hn2, List.mem_erase_of_ne hn0]
    exact List.mem_filter.2 ⟨hc.1, by simp; omega⟩
  have hU1 : n₀ + 2 ≤ U'.length := by
    let R : Atom 3 n₀ → Atom 3 n₀ → Prop := fun u v => ∃ c ∈ U', c.x = u ∧ c.y = v
    have hW' : ∀ c ∈ W, R c.x c.y := fun c hc => ⟨c, hWU c hc, rfl, rfl⟩
    have hintR : ∀ u v : Atom 3 n₀, u.isRight = true → v.isRight = true →
        (SimpleGraph.fromRel R).Reachable u v := by
      intro u v hu hv
      rcases u with i | a
      · simp at hu
      rcases v with i | b
      · simp at hv
      exact hint a b hW'
    have hsolid : ∀ d ∈ Γ.comps, 1 ≤ d.kind.ord → d.x ≠ d.y →
        (SimpleGraph.fromRel R).Reachable d.x d.y := by
      intro d hd ho hxy
      by_cases hdU : d ∈ U'
      · exact SimpleGraph.Adj.reachable
          ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hxy, Or.inl ⟨d, hdU, rfl, rfl⟩⟩)
      · have hdU0 : d ∈ U := List.mem_filter.2 ⟨hd, by simp; omega⟩
        have : d = c₀ ∨ d = c₂ := by
          by_contra hc
          push Not at hc
          rw [hU', List.mem_erase_of_ne hc.2, List.mem_erase_of_ne hc.1] at hdU
          exact hdU hdU0
        rcases this with rfl | rfl
        · exact hintR _ _ hi0.1 hi0.2
        · exact hintR _ _ hi2.1 hi2.2
    have hso : ∀ e : Comp (Atom 3 n₀), e.kind.isSolid = true → e.kind.ord = 1 := by
      intro e he
      rcases hk : e.kind <;> rw [hk] at he <;> simp [Kind.isSolid, Kind.ord] at he ⊢
    have hc : (SimpleGraph.fromRel R).Connected := by
      have : Nonempty (Atom 3 n₀) := ⟨.inr a₀⟩
      refine ⟨fun u v => TerminationC_reach_of (fun u v huv => ?_) (hN.1.connected u v)⟩
      rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at huv
      obtain ⟨hne', ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, rfl, rfl⟩⟩ := huv
      all_goals
        have hd' := TerminationC_ord_tkind (hK' d hd)
        by_cases ho : 1 ≤ d.kind.ord
      · exact hsolid d hd ho hne'
      · rcases hd'.2.2 (by omega) with hw | hx
        · exact absurd ((hP d hd).2.2.2.2.1 hw).symm hne'
        · obtain ⟨e, he, hes, hee⟩ := (hN.2.2 d.x d.y hne').1 ⟨d, hd, hx, Or.inl ⟨rfl, rfl⟩⟩
          have heo : e.kind.ord = 1 := hso e hes
          rcases hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]; exact hsolid e he (by omega) (by rw [h1, h2]; exact hne')
          · rw [← h1, ← h2]; exact (hsolid e he (by omega) (by rw [h1, h2]; exact hne'.symm)).symm
      · exact (hsolid d hd ho hne'.symm).symm
      · rcases hd'.2.2 (by omega) with hw | hx
        · exact absurd ((hP d hd).2.2.2.2.1 hw) hne'
        · obtain ⟨e, he, hes, hee⟩ := (hN.2.2 d.y d.x hne').1 ⟨d, hd, hx, Or.inr ⟨rfl, rfl⟩⟩
          have heo : e.kind.ord = 1 := hso e hes
          rcases hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]; exact hsolid e he (by omega) (by rw [h1, h2]; exact hne')
          · rw [← h1, ← h2]; exact (hsolid e he (by omega) (by rw [h1, h2]; exact hne'.symm)).symm
    have := TerminationC_card_le (R := R) (U'.map (fun c => (c.x, c.y)))
      (fun u v ⟨c, hc, h1, h2⟩ => List.mem_map.2 ⟨c, hc, by rw [h1, h2]⟩) hc
    simp only [Fintype.card_sum, Fintype.card_fin, List.length_map] at this
    omega
  unfold Graph.ord
  omega

end Grid


/-! ## The closure of Step 2 at `α`: a reordering to the form `H.glue x y₁ y₂ (tVar true)` -/

section Closure

open private RunClauses_Iso RunClauses_SwapR RunClauses_eA RunClauses_eA_inl RunClauses_eA_inr
  from RBM8D.GlobalExp.RunClauses
open private Termination_sameBlock_of_dotFree from RBM8D.GlobalExp.Termination

/-- The components of `H.glue x y₁ y₂ (tVar true)`: those of `H`, then `s_{αx}`, `G_{y₁α}`,
`Ḡ_{y₂α}` and the two `×`-dotted edges. -/
private theorem TerminationC_glue_comps {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) :
    (H.glue x y₁ y₂ (tVar true)).comps = liftCs 1 H.comps ++
      [⟨.waved .s, newA 0, liftA 1 x, [], none⟩, ⟨.G .plus, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩, ⟨.xdot, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.xdot, liftA 1 y₂, newA 0, [], none⟩] := by
  rfl

private theorem TerminationC_newA {m : ℕ} : (newA 0 : Atom 3 (m + 1)) = .inr (Fin.last m) := by
  simp [newA, Fin.ext_iff]

private theorem TerminationC_liftA_ne {m : ℕ} (u : Atom 3 m) :
    liftA 1 u ≠ (.inr (Fin.last m) : Atom 3 (m + 1)) := by
  rcases u with i | j
  · simp [liftA]
  · simp [liftA, Fin.ext_iff]
    omega

/-- In `H.glue x y₁ y₂ (tVar true)` the only blue solid edge entering the new atom is the one at
position `|H| + 1`. -/
private theorem TerminationC_glue_G {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (j : Fin (H.glue x y₁ y₂ (tVar true)).comps.length)
    (hk : (H.glue x y₁ y₂ (tVar true)).comps[j].kind = .G .plus)
    (hy : (H.glue x y₁ y₂ (tVar true)).comps[j].y = .inr (Fin.last m)) :
    j.val = H.comps.length + 1 := by
  have hj := j.2
  have e := TerminationC_glue_comps H x y₁ y₂
  simp only [Fin.getElem_fin] at hk hy
  have hlen : (H.glue x y₁ y₂ (tVar true)).comps.length = H.comps.length + 5 := by
    rw [e]; simp [liftCs]
  by_cases hlt : (j : ℕ) < H.comps.length
  · exfalso
    have : (H.glue x y₁ y₂ (tVar true)).comps[(j : ℕ)] = (H.comps[(j : ℕ)]).map (liftA 1) := by
      simp only [e]
      rw [List.getElem_append_left (by simp [liftCs]; exact hlt)]
      simp [liftCs]
    rw [this] at hy
    exact TerminationC_liftA_ne _ hy
  · obtain ⟨k, hk'⟩ : ∃ k, (j : ℕ) = H.comps.length + k := ⟨j - H.comps.length, by omega⟩
    have hk5 : k < 5 := by omega
    have : (H.glue x y₁ y₂ (tVar true)).comps[(j : ℕ)] =
        [(⟨.waved .s, newA 0, liftA 1 x, [], none⟩ : Comp (Atom 3 (m + 1))),
          ⟨.G .plus, liftA 1 y₁, newA 0, [], none⟩, ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩,
          ⟨.xdot, liftA 1 y₁, newA 0, [], none⟩, ⟨.xdot, liftA 1 y₂, newA 0, [], none⟩][k] := by
      simp only [e]
      rw [List.getElem_append_right (by simp [liftCs]; omega)]
      congr 1
      simp [liftCs, hk']
    rw [this] at hk hy
    interval_cases k <;> simp_all

/-- The atom map that forgets the last internal atom (sending it to `⊗`). -/
private def TerminationC_pull {m : ℕ} : Atom 3 (m + 1) → Atom 3 m
  | .inl i => .inl i
  | .inr j => if h : (j : ℕ) < m then .inr ⟨j, h⟩ else .inl 0

private theorem TerminationC_lift_pull {m : ℕ} {u : Atom 3 (m + 1)}
    (h : u ≠ .inr (Fin.last m)) : liftA 1 (TerminationC_pull u) = u := by
  rcases u with i | j
  · rfl
  · have hj : (j : ℕ) < m := by
      have := j.2
      have hne : (j : ℕ) ≠ m := fun he => h (by congr 1; exact Fin.ext he)
      omega
    simp [TerminationC_pull, hj, liftA]

/-- A list split by a predicate. -/
private theorem TerminationC_perm_split {β : Type*} (L : List β) (p : β → Bool) {L₁ L₂ : List β}
    (h₁ : (L.filter p).Perm L₁) (h₂ : (L.filter fun b => !p b).Perm L₂) : L.Perm (L₁ ++ L₂) :=
  (List.filter_append_perm p L).symm.trans (h₁.append h₂)

/-- The atoms `u`, `v` are the two ends of `c`, in either orientation. -/
private def TerminationC_joinsB {k n : ℕ} (u v : Atom k n) (c : Comp (Atom k n)) : Bool :=
  c.x == u && c.y == v || c.x == v && c.y == u

private theorem TerminationC_xmult_eq {n₀ : ℕ} (Γ : Graph 3 n₀) (u v : Atom 3 n₀) :
    TerminationC_xmult Γ u v =
      (Γ.comps.filter fun c => c.kind == .xdot && TerminationC_joinsB u v c).length := rfl

private theorem TerminationC_smult_eq {n₀ : ℕ} (Γ : Graph 3 n₀) (u v : Atom 3 n₀) :
    TerminationC_smult Γ u v =
      (Γ.comps.filter fun c => c.kind.isSolid && TerminationC_joinsB u v c).length := rfl


/-- A waved or diffusive kind is neither solid nor `×`-dotted. -/
private theorem TerminationC_wt_kind {κ : Kind}
    (h : κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true) :
    κ.isSolid = false ∧ κ ≠ .xdot := by
  cases κ <;> simp_all [Kind.joinsMol, Kind.isDiffusive, Kind.isSolid]

private theorem TerminationC_joinsB_at {k n : ℕ} {u v : Atom k n} {c : Comp (Atom k n)}
    (h : TerminationC_joinsB u v c = true) : TerminationC_at u c = true := by
  simp only [TerminationC_joinsB, TerminationC_at, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h ⊢
  rcases h with ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h


/-- A list with at least one element with `p` has a position with `p`. -/
private theorem TerminationC_one_idx {β : Type*} (L : List β) (p : β → Bool)
    (h : 1 ≤ (L.filter p).length) : ∃ i : Fin L.length, p L[i] = true := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos h
  obtain ⟨hcL, hp⟩ := List.mem_filter.1 hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcL
  exact ⟨⟨i, hi⟩, hp⟩

/-- A list with at least two elements with `p` has two distinct positions with `p`. -/
private theorem TerminationC_two_idx {β : Type*} (L : List β) (p : β → Bool)
    (h : 2 ≤ (L.filter p).length) :
    ∃ i j : Fin L.length, i ≠ j ∧ p L[i] = true ∧ p L[j] = true := by
  set I := (List.finRange L.length).filter fun i => p L[i] with hI
  have hlen : I.length = (L.filter p).length := by
    conv_rhs => rw [← List.map_getElem_finRange L]
    rw [List.filter_map, List.length_map]
    rfl
  have hnd : I.Nodup := (List.nodup_finRange _).filter _
  match hI' : I, hlen, hnd with
  | i :: j :: rest, _, hnd =>
    have hi : i ∈ I := by rw [hI']; simp
    have hj : j ∈ I := by rw [hI']; simp
    refine ⟨i, j, fun he => ?_, (List.mem_filter.1 hi).2, (List.mem_filter.1 hj).2⟩
    subst he
    simp at hnd
  | [], hlen, _ =>
    simp only [List.length_nil] at hlen
    omega
  | [_], hlen, _ =>
    simp only [List.length_singleton] at hlen
    omega

/-- A component without minor and label. -/
private theorem TerminationC_eta {V : Type*} {c : Comp V} (hm : c.minor = []) (hl : c.label = none) :
    c = ⟨c.kind, c.x, c.y, [], none⟩ := by
  obtain ⟨k, x, y, mi, l⟩ := c
  simp only at hm hl
  subst hm hl
  rfl

/-- **The closure of Step 2 at `α`** ([II, (4.14)], [II, Strategy 6.6, Step 2]): at a normal regular
plain graph without labels and dotted edges, at a standard neutral atom `α` entered by the blue
solid edge `G_{y₁α}` (position `i₀`), without `×`-dotted loop, with as many `×`-dotted as solid
edges between `α` and each other atom, and with a coefficient divisible by `m m̄`, a reordering
(`α` renumbered last, the waved edge and the `×`-dotted edges at `α` turned towards their form)
gives `H.glue x y₁ y₂ (tVar true)`, with `G_{y₁α}` at position `|H| + 1`. -/
private theorem TerminationC_closure {m C : ℕ} {Γ : Graph 3 (m + 1)} {a : Fin (m + 1)}
    (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree)
    (hstd : Γ.stdNeutralAt (.inr a) = true)
    {i₀ : Fin Γ.comps.length} (hk₀ : Γ.comps[i₀].kind = .G .plus) (hy₀ : Γ.comps[i₀].y = .inr a)
    (hint₀ : Γ.comps[i₀].x.isRight = true)
    (hl : ∀ c ∈ Γ.comps, c.kind = .xdot → c.x ≠ c.y)
    (hpair : ∀ v, v ≠ .inr a → TerminationC_xmult Γ (.inr a) v = TerminationC_smult Γ (.inr a) v)
    (hdiv : cm * cmb ∣ Γ.coeff) :
    ∃ (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (π : Equiv.Perm (Fin (m + 1)))
      (σ : Fin Γ.comps.length → Fin (H.glue x y₁ y₂ (tVar true)).comps.length),
      RunClauses_Iso π Γ (H.glue x y₁ y₂ (tVar true)) ∧
      (∀ i, RunClauses_SwapR (Γ.comps[i].map (RunClauses_eA π))
        (H.glue x y₁ y₂ (tVar true)).comps[σ i]) ∧
      Function.Bijective σ ∧ (σ i₀).val = H.comps.length + 1 ∧ H.LabelFree := by
  classical
  obtain ⟨q, hq⟩ := hdiv
  set α : Atom 3 (m + 1) := .inr a with hα
  set αL : Atom 3 (m + 1) := .inr (Fin.last m) with hαL
  set c₀ := Γ.comps[i₀] with hc₀def
  have hc₀ : c₀ ∈ Γ.comps := List.getElem_mem _
  have hns : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y := hN.2.1
  have hx₀ : c₀.x ≠ α := fun h => hns c₀ hc₀ (by rw [hk₀]; rfl) (h.trans hy₀.symm)
  obtain ⟨c₂, hc₂, hk₂, hy₂, hx₂, hS⟩ := TerminationC_std_solid hns hstd hc₀ hk₀ hy₀
  obtain ⟨cS, hcS, hkS, -, honly, hsfilt⟩ := TerminationC_std_s hstd
  have heta : ∀ c ∈ Γ.comps, c = ⟨c.kind, c.x, c.y, [], none⟩ :=
    fun c hc => TerminationC_eta (hP c hc).1 (hL c hc)
  -- the waved edge at `α` is not a loop (regularity)
  obtain ⟨b₁, hb₁⟩ : ∃ b, c₀.x = .inr b := by
    rcases h : c₀.x with i | b
    · rw [h] at hint₀; simp at hint₀
    · exact ⟨b, rfl⟩
  obtain ⟨w, hw, hcSj⟩ : ∃ w, w ≠ α ∧ (cS.x = α ∧ cS.y = w ∨ cS.x = w ∧ cS.y = α) := by
    have hab : α ≠ .inr b₁ := fun h => hx₀ (hb₁.trans h.symm)
    obtain ⟨p⟩ := hN.1.internal a b₁
    cases p with
    | nil => exact absurd rfl hab
    | cons hadj _ =>
      rename_i w _
      rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩ := hadj
      · obtain ⟨hns', hnx⟩ := TerminationC_wt_kind hk
        have := (honly c hc (Or.inl h1) hnx).resolve_left (by simp [hns'])
        subst this
        exact ⟨w, fun h => hne h.symm, Or.inl ⟨h1, h2⟩⟩
      · obtain ⟨hns', hnx⟩ := TerminationC_wt_kind hk
        have := (honly c hc (Or.inr h2) hnx).resolve_left (by simp [hns'])
        subst this
        exact ⟨w, fun h => hne h.symm, Or.inr ⟨h1, h2⟩⟩
  -- the renumbering
  set π : Equiv.Perm (Fin (m + 1)) := Equiv.swap a (Fin.last m) with hπ
  set eA := RunClauses_eA π with heAdef
  have heAα : eA α = αL := by
    rw [hα, heAdef, RunClauses_eA_inr]; simp [hπ, hαL]
  have heAne : ∀ u, u ≠ α → eA u ≠ αL := by
    intro u hu
    rw [← heAα]
    exact fun h => hu (eA.injective h)
  have hlp : ∀ u, u ≠ α → liftA 1 (TerminationC_pull (eA u)) = eA u :=
    fun u hu => TerminationC_lift_pull (heAne u hu)
  -- the turn of the waved edge and the `×`-dotted edges at `α`
  let Φ : Comp (Atom 3 (m + 1)) → Comp (Atom 3 (m + 1)) := fun c =>
    if (c.map eA).kind = .waved .s ∧ (c.map eA).y = αL ∨
        (c.map eA).kind = .xdot ∧ (c.map eA).x = αL then
      { c.map eA with x := (c.map eA).y, y := (c.map eA).x }
    else c.map eA
  have hΦat : ∀ c, TerminationC_at αL (Φ c) = TerminationC_at α c := by
    intro c
    have h1 : (eA c.x == αL) = (c.x == α) := by
      rw [← heAα]; by_cases h : c.x = α <;> simp [h, eA.injective.eq_iff]
    have h2 : (eA c.y == αL) = (c.y == α) := by
      rw [← heAα]; by_cases h : c.y = α <;> simp [h, eA.injective.eq_iff]
    simp only [Φ, TerminationC_at]
    split_ifs <;> simp only [Comp.map, h1, h2, Bool.or_comm]
  have hΦoff : ∀ c, TerminationC_at α c = false → Φ c = c.map eA := by
    intro c hc
    simp only [TerminationC_at, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
    simp only [Φ, Comp.map]
    refine ite_eq_right ?_
    rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact heAne _ hc.2 h
    · exact heAne _ hc.1 h
  -- the graph `H` and the atoms
  let H : Graph 3 m := ⟨(Γ.comps.filter fun c => !TerminationC_at α c).map
    (fun c => (c.map eA).map TerminationC_pull), q⟩
  let x := TerminationC_pull (eA w)
  let y₁ := TerminationC_pull (eA c₀.x)
  let y₂ := TerminationC_pull (eA c₂.x)
  set G' := H.glue x y₁ y₂ (tVar true) with hG'
  set cs := Γ.comps.map Φ with hcs
  -- the five components at `α`
  have hΦ₀ : Φ c₀ = ⟨.G .plus, liftA 1 y₁, newA 0, [], none⟩ := by
    rw [heta c₀ hc₀, TerminationC_newA]
    simp only [Φ, Comp.map, hk₀, hy₀, heAα, List.map_nil, Option.map_none]
    rw [ite_eq_right (by simp)]
    simp [y₁, hlp _ hx₀, hαL]
  have hΦ₂ : Φ c₂ = ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩ := by
    rw [heta c₂ hc₂, TerminationC_newA]
    simp only [Φ, Comp.map, hk₂, hy₂, heAα, List.map_nil, Option.map_none]
    rw [ite_eq_right (by simp)]
    simp [y₂, hlp _ hx₂, hαL]
  have hΦS : Φ cS = ⟨.waved .s, newA 0, liftA 1 x, [], none⟩ := by
    rw [heta cS hcS, TerminationC_newA]
    rcases hcSj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Φ, Comp.map, hkS, h1, h2, heAα, List.map_nil, Option.map_none]
      rw [ite_eq_right ?_]
      · simp [x, hlp _ hw, hαL]
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact heAne _ hw h
        · cases h
    · simp only [Φ, Comp.map, hkS, h1, h2, heAα, List.map_nil, Option.map_none]
      rw [ite_eq_left (by simp)]
      simp [x, hlp _ hw, hαL]
  -- the `×`-dotted edges at `α`
  have hXf : ∀ c ∈ Γ.comps, c.kind = .xdot → TerminationC_at α c = true →
      ∃ v, v ≠ α ∧ (c.x = α ∧ c.y = v ∨ c.x = v ∧ c.y = α) ∧
        Φ c = ⟨.xdot, eA v, αL, [], none⟩ := by
    intro c hc hk hat
    have hne := hl c hc hk
    simp only [TerminationC_at, Bool.or_eq_true, beq_iff_eq] at hat
    by_cases h1 : c.x = α
    · refine ⟨c.y, fun h => hne (h1.trans h.symm), Or.inl ⟨h1, rfl⟩, ?_⟩
      rw [heta c hc]
      simp only [Φ, Comp.map, hk, h1, heAα, List.map_nil, Option.map_none]
      rw [ite_eq_left (by simp)]
    · have h2 : c.y = α := hat.resolve_left h1
      refine ⟨c.x, h1, Or.inr ⟨rfl, h2⟩, ?_⟩
      rw [heta c hc]
      simp only [Φ, Comp.map, hk, h2, heAα, List.map_nil, Option.map_none]
      rw [ite_eq_right ?_]
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · cases h
      · exact heAne _ h1 h
  have hSmem : ∀ d ∈ Γ.comps, d.kind.isSolid = true → TerminationC_at α d = true →
      d = c₀ ∨ d = c₂ := by
    intro d hd hs ha
    have : d ∈ [c₀, c₂] := hS.subset (List.mem_filter.2 ⟨hd, by simp [hs, ha]⟩)
    simpa using this
  have hXv : ∀ c ∈ Γ.comps, c.kind = .xdot → ∀ v, v ≠ α →
      (c.x = α ∧ c.y = v ∨ c.x = v ∧ c.y = α) → v = c₀.x ∨ v = c₂.x := by
    intro c hc hk v hv hj
    obtain ⟨d, hd, hds, hdj⟩ := (hN.2.2 α v (Ne.symm hv)).1 ⟨c, hc, hk, hj⟩
    have hda : TerminationC_at α d = true := by
      simp only [TerminationC_at, Bool.or_eq_true, beq_iff_eq]
      rcases hdj with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    rcases hSmem d hd hds hda with rfl | rfl
    · rcases hdj with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hx₀
      · exact Or.inl h.symm
    · rcases hdj with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hx₂
      · exact Or.inr h.symm
  have hsm : ∀ v, TerminationC_smult Γ α v =
      ([c₀, c₂].filter (TerminationC_joinsB α v)).length := by
    intro v
    rw [TerminationC_smult_eq]
    have : (Γ.comps.filter fun c => c.kind.isSolid && TerminationC_joinsB α v c) =
        (Γ.comps.filter fun c => c.kind.isSolid && TerminationC_at α c).filter
          (TerminationC_joinsB α v) := by
      rw [List.filter_filter]
      refine List.filter_congr fun c _ => ?_
      rcases hJ : TerminationC_joinsB α v c
      · simp
      · simp [TerminationC_joinsB_at hJ]
    rw [this, (hS.filter _).length_eq]
  -- the components at `α`
  set A := Γ.comps.filter (TerminationC_at α) with hA
  set X := A.filter fun c => c.kind == .xdot with hX
  have hXm : ∀ c ∈ X, c ∈ Γ.comps ∧ TerminationC_at α c = true ∧ c.kind = .xdot := by
    intro c hc
    rw [hX, hA, List.mem_filter, List.mem_filter] at hc
    exact ⟨hc.1.1, hc.1.2, by simpa using hc.2⟩
  have hxm : ∀ v, TerminationC_xmult Γ α v = (X.filter (TerminationC_joinsB α v)).length := by
    intro v
    rw [TerminationC_xmult_eq, hX, hA, List.filter_filter, List.filter_filter]
    congr 1
    refine List.filter_congr fun c _ => ?_
    rcases hJ : TerminationC_joinsB α v c
    · simp
    · simp [TerminationC_joinsB_at hJ, Bool.and_comm]
  have hA1 : (A.filter fun c => c.kind.isSolid).Perm [c₀, c₂] := by
    rw [hA, List.filter_filter]; exact hS
  have hA2 : ((A.filter fun c => !c.kind.isSolid).filter fun c => c.kind == .waved .s) = [cS] := by
    rw [hA, List.filter_filter, List.filter_filter, ← hsfilt]
    refine List.filter_congr fun c _ => ?_
    by_cases hk : c.kind = .waved .s
    · simp [hk, Kind.isSolid]
    · have : (c.kind == .waved .s) = false := by simpa using hk
      simp [this]
  have hA3 : ((A.filter fun c => !c.kind.isSolid).filter fun c => !(c.kind == .waved .s)) = X := by
    rw [List.filter_filter, hX]
    refine List.filter_congr fun c hc => ?_
    have hc' := List.mem_filter.1 hc
    by_cases hk : c.kind = .xdot
    · simp [hk, Kind.isSolid]
    · have hat : c.x = α ∨ c.y = α := by simpa [TerminationC_at] using hc'.2
      have hk' : (c.kind == .xdot) = false := by simpa using hk
      rcases honly c hc'.1 hat hk with hs | rfl
      · simp [hs, hk']
      · simp [hkS]
  have hAperm : A.Perm ([c₀, c₂] ++ ([cS] ++ X)) :=
    TerminationC_perm_split A (fun c => c.kind.isSolid) hA1
      (TerminationC_perm_split _ (fun c => c.kind == .waved .s) (List.Perm.of_eq hA2)
        (List.Perm.of_eq hA3))
  -- the `×`-dotted edges at `α` in their form
  have hy1 : liftA 1 y₁ = eA c₀.x := hlp _ hx₀
  have hy2 : liftA 1 y₂ = eA c₂.x := hlp _ hx₂
  have hXperm : (X.map Φ).Perm [⟨.xdot, liftA 1 y₁, newA 0, [], none⟩,
      ⟨.xdot, liftA 1 y₂, newA 0, [], none⟩] := by
    rw [hy1, hy2, TerminationC_newA]
    have hmap : ∀ c ∈ X, ∀ v, v ≠ α → TerminationC_joinsB α v c = true →
        Φ c = ⟨.xdot, eA v, αL, [], none⟩ := by
      intro c hc v hv hJ
      obtain ⟨hcm, hat, hk⟩ := hXm c hc
      obtain ⟨v', hv', hj', hΦ'⟩ := hXf c hcm hk hat
      have : v' = v := by
        simp only [TerminationC_joinsB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hJ
        rcases hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hJ with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · rw [← h2, h4]
        · exact absurd (h1.symm.trans h3) (Ne.symm hv)
        · exact absurd (h3.symm.trans h1) (Ne.symm hv')
        · rw [← h1, h3]
      rw [hΦ', this]
    have hvX : ∀ c ∈ X, TerminationC_joinsB α c₀.x c = true ∨ TerminationC_joinsB α c₂.x c = true := by
      intro c hc
      obtain ⟨hcm, hat, hk⟩ := hXm c hc
      obtain ⟨v, hv, hj, -⟩ := hXf c hcm hk hat
      have hJ : TerminationC_joinsB α v c = true := by
        simp only [TerminationC_joinsB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
        exact hj
      rcases hXv c hcm hk v hv hj with rfl | rfl
      · exact Or.inl hJ
      · exact Or.inr hJ
    have hJ0 : TerminationC_joinsB α c₀.x c₀ = true := by
      simp [TerminationC_joinsB, hy₀]
    have hJ2 : TerminationC_joinsB α c₂.x c₂ = true := by
      simp [TerminationC_joinsB, hy₂]
    by_cases hyy : c₀.x = c₂.x
    · have hall : ∀ c ∈ X, TerminationC_joinsB α c₀.x c = true := by
        intro c hc
        rcases hvX c hc with h | h
        · exact h
        · rw [hyy]; exact h
      have hlen : X.length = 2 := by
        have h1 := hxm c₀.x
        rw [hpair _ hx₀, hsm, List.filter_eq_self.2 hall] at h1
        rw [← h1]
        simp [hJ0, hyy ▸ hJ2]
      have : X.map Φ = List.replicate 2 (⟨.xdot, eA c₀.x, αL, [], none⟩ : Comp _) := by
        rw [List.eq_replicate_iff]
        refine ⟨by rw [List.length_map, hlen], fun b hb => ?_⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact hmap c hc _ hx₀ (hall c hc)
      rw [this, ← hyy]
      rfl
    · have hJ02 : TerminationC_joinsB α c₀.x c₂ = false := by
        simp [TerminationC_joinsB, hy₂, Ne.symm hyy, hx₂]
      have hJ20 : TerminationC_joinsB α c₂.x c₀ = false := by
        simp [TerminationC_joinsB, hy₀, hyy, hx₀]
      have hsplit := TerminationC_perm_split X (TerminationC_joinsB α c₀.x)
        (L₁ := X.filter (TerminationC_joinsB α c₀.x))
        (L₂ := X.filter (TerminationC_joinsB α c₂.x)) (List.Perm.refl _) (by
          refine List.Perm.of_eq (List.filter_congr fun c hc => ?_)
          rcases hvX c hc with h | h
          · have : TerminationC_joinsB α c₂.x c = false := by
              by_contra h'
              simp only [Bool.not_eq_false] at h'
              simp only [TerminationC_joinsB, Bool.or_eq_true, Bool.and_eq_true,
                beq_iff_eq] at h h'
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
              · exact hyy (h2.symm.trans h4)
              · exact hx₂ (h3.symm.trans h1)
              · exact hx₀ (h1.symm.trans h3)
              · exact hyy (h1.symm.trans h3)
            simp [h, this]
          · have : TerminationC_joinsB α c₀.x c = false := by
              by_contra h'
              simp only [Bool.not_eq_false] at h'
              simp only [TerminationC_joinsB, Bool.or_eq_true, Bool.and_eq_true,
                beq_iff_eq] at h h'
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
              · exact hyy (h4.symm.trans h2)
              · exact hx₀ (h3.symm.trans h1)
              · exact hx₂ (h1.symm.trans h3)
              · exact hyy (h3.symm.trans h1)
            simp [h, this])
      have hl1 : (X.filter (TerminationC_joinsB α c₀.x)).length = 1 := by
        rw [← hxm, hpair _ hx₀, hsm]
        simp [hJ0, hJ02]
      have hl2 : (X.filter (TerminationC_joinsB α c₂.x)).length = 1 := by
        rw [← hxm, hpair _ hx₂, hsm]
        simp [hJ2, hJ20]
      have e1 : (X.filter (TerminationC_joinsB α c₀.x)).map Φ =
          [(⟨.xdot, eA c₀.x, αL, [], none⟩ : Comp _)] := by
        rw [← List.replicate_one, List.eq_replicate_iff]
        refine ⟨by rw [List.length_map, hl1], fun b hb => ?_⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact hmap c (List.mem_filter.1 hc).1 _ hx₀ (List.mem_filter.1 hc).2
      have e2 : (X.filter (TerminationC_joinsB α c₂.x)).map Φ =
          [(⟨.xdot, eA c₂.x, αL, [], none⟩ : Comp _)] := by
        rw [← List.replicate_one, List.eq_replicate_iff]
        refine ⟨by rw [List.length_map, hl2], fun b hb => ?_⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact hmap c (List.mem_filter.1 hc).1 _ hx₂ (List.mem_filter.1 hc).2
      have := hsplit.map Φ
      rw [List.map_append, e1, e2] at this
      exact this
  -- the components of the form
  have hB : (cs.filter (TerminationC_at αL)).Perm
      [⟨.waved .s, newA 0, liftA 1 x, [], none⟩, ⟨.G .plus, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩, ⟨.xdot, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.xdot, liftA 1 y₂, newA 0, [], none⟩] := by
    have e : cs.filter (TerminationC_at αL) = A.map Φ := by
      rw [hcs, List.filter_map, hA]
      congr 1
      exact List.filter_congr fun c _ => hΦat c
    rw [e]
    refine (hAperm.map Φ).trans ?_
    simp only [List.map_cons, hΦ₀, hΦ₂, hΦS, List.cons_append, List.nil_append]
    refine ((List.Perm.swap _ _ _).cons _).trans ((List.Perm.swap _ _ _).trans ?_)
    exact ((hXperm.cons _).cons _).cons _
  have hH : (cs.filter fun c => !TerminationC_at αL c) = liftCs 1 H.comps := by
    rw [hcs, List.filter_map]
    simp only [liftCs, H, List.map_map]
    rw [List.filter_congr (q := fun c => !TerminationC_at α c) fun c _ => by
      simp only [Function.comp_apply, hΦat]]
    refine List.map_congr_left fun c hc => ?_
    have hc' := List.mem_filter.1 hc
    have hno : TerminationC_at α c = false := by simpa using hc'.2
    rw [Function.comp_apply, hΦoff c hno]
    have hxy : c.x ≠ α ∧ c.y ≠ α := by
      simpa [TerminationC_at] using hno
    rw [heta c hc'.1]
    simp [Comp.map, hlp _ hxy.1, hlp _ hxy.2]
  have hperm : cs.Perm G'.comps := by
    rw [hG', TerminationC_glue_comps]
    refine TerminationC_perm_split cs (fun c => !TerminationC_at αL c) (List.Perm.of_eq hH) ?_
    simpa only [Bool.not_not] using hB
  -- the bijection of the positions
  have hlen : (Γ.comps.length : ℕ) = cs.length := by rw [hcs, List.length_map]
  let σ : Fin Γ.comps.length → Fin G'.comps.length := fun i => hperm.idxBij (Fin.cast hlen i)
  have hσ : ∀ i, G'.comps[σ i] = Φ Γ.comps[i] := by
    intro i
    show G'.comps[(hperm.idxBij (Fin.cast hlen i) : ℕ)] = Φ Γ.comps[(i : ℕ)]
    rw [hperm.getElem_idxBij_eq_getElem]
    simp [hcs]
  have hbij : Function.Bijective σ := by
    have hl := hperm.idxBij_leftInverse_idxBij_symm
    have hr := hperm.idxBij_rightInverse_idxBij_symm
    constructor
    · intro i j hij
      have := congrArg hperm.symm.idxBij hij
      simp only [σ, hr.eq] at this
      exact (Fin.cast_injective hlen) this
    · intro j
      refine ⟨Fin.cast hlen.symm (hperm.symm.idxBij j), ?_⟩
      simp only [σ, Fin.cast_cast, Fin.cast_eq_self]
      exact hl j
  refine ⟨H, x, y₁, y₂, π, σ, ⟨?_, cs, ?_, hperm⟩, fun i => ?_, hbij, ?_, ?_⟩
  · show q * (cm * cmb) = Γ.coeff
    rw [hq]
    ring
  · rw [hcs, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro c _
    simp only [Φ]
    split_ifs with h
    · right
      rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨Or.inl h, rfl⟩
      · exact ⟨Or.inr (Or.inr h), rfl⟩
    · left; rfl
  · rw [hσ i]
    simp only [Φ]
    split_ifs with h
    · right
      rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨Or.inl h, rfl⟩
      · exact ⟨Or.inr (Or.inr h), rfl⟩
    · left; rfl
  · refine TerminationC_glue_G H x y₁ y₂ (σ i₀) ?_ ?_
    · rw [hσ i₀, ← hc₀def, hΦ₀]
    · rw [hσ i₀, ← hc₀def, hΦ₀, TerminationC_newA]
  · intro c hc
    simp only [H, List.mem_map, List.mem_filter] at hc
    obtain ⟨d, ⟨hd, -⟩, rfl⟩ := hc
    simp [Comp.map, hL d hd]


end Closure


/-! ## The choice of `α` is stable under the normalisation of Step 2 -/

section Stable

open private TrH TrH.mk TrH.symm TrH.cls_eq TrH.ginj from RBM8D.Graph.MolCarry
open private RunClauses_Iso RunClauses_SwapR RunClauses_eA RunClauses_eA_isRight
  RunClauses_iso_molRep RunClauses_iso_sameMol RunClauses_iso_mem RunClauses_swapR_eq
  from RBM8D.GlobalExp.RunClauses
open private GlobalGood_mis_sub GlobalGood_isRight_of_mem_MIS from RBM8D.GlobalExp.GlobalGood
open private TrH.surj from RBM8D.Graph.MolCarry
open private Termination_molRep_mem Termination_sameBlock_mem Termination_flatComp_congr
  Termination_anchor_congr Termination_sameMol_mem from RBM8D.GlobalExp.Termination

variable {n : ℕ}

/-- A reordering gives a bijection of the positions that matches each component with its image. -/
private theorem TerminationC_iso_sigma {π : Equiv.Perm (Fin n)} {Γ Γ' : Graph 3 n}
    (h : RunClauses_Iso π Γ Γ') :
    ∃ σ : Fin Γ.comps.length → Fin Γ'.comps.length, Function.Bijective σ ∧
      ∀ i, RunClauses_SwapR (Γ.comps[i].map (RunClauses_eA π)) Γ'.comps[σ i] := by
  classical
  obtain ⟨-, cs, h1, h2⟩ := h
  have hlen : Γ.comps.length = cs.length := by rw [← h1.length_eq, List.length_map]
  refine ⟨fun i => h2.idxBij (Fin.cast hlen i), ⟨fun i j hij => ?_, fun j => ?_⟩, fun i => ?_⟩
  · have := congrArg h2.symm.idxBij hij
    simp only [h2.idxBij_rightInverse_idxBij_symm.eq] at this
    exact Fin.cast_injective hlen this
  · refine ⟨Fin.cast hlen.symm (h2.symm.idxBij j), ?_⟩
    simp only [Fin.cast_cast, Fin.cast_eq_self]
    exact h2.idxBij_leftInverse_idxBij_symm j
  · show RunClauses_SwapR _ Γ'.comps[(h2.idxBij (Fin.cast hlen i) : ℕ)]
    rw [h2.getElem_idxBij_eq_getElem]
    have := h1.get (i := i) (by simp) (by rw [← hlen]; exact i.2)
    simpa using this

/-- **The blue solid edge of Step 2 read back along a reordering**: the converse of
`TerminationC_iso_step2`, by the inverse change of names. -/
private theorem TerminationC_iso_step2_bwd {π : Equiv.Perm (Fin n)} {Γ Γ' : Graph 3 n}
    (h : RunClauses_Iso π Γ Γ') (σ : Fin Γ.comps.length → Fin Γ'.comps.length)
    (hσ : ∀ i, RunClauses_SwapR (Γ.comps[i].map (RunClauses_eA π)) Γ'.comps[σ i])
    (hbij : Function.Bijective σ) {i : Fin Γ.comps.length} (hS : Γ'.Step2EdgeB' (σ i)) :
    Γ.Step2EdgeB' i := by
  classical
  have hT := TerminationC_trH h σ hσ hbij
  have : Nonempty (Atom 3 n) := ⟨.inl 0⟩
  have : Nonempty (Fin Γ.comps.length ⊕ Fin 3) := ⟨.inr 0⟩
  have hT' := TrH.symm hT
  obtain ⟨⟨hk, hx, hy, hm⟩, hc⟩ := hS
  have he : Γ'.comps[σ i] = Γ.comps[i].map (RunClauses_eA π) := by
    rcases hσ i with he | ⟨hk', he'⟩
    · exact he
    · rw [he'] at hk
      simp only [Comp.map] at hk hk'
      rw [hk] at hk'
      rcases hk' with h' | h' | h' <;> cases h'
  have hk' : Γ.comps[i].kind = .G .plus := by rw [he] at hk; exact hk
  have hmis : ∀ u, Γ'.molRep (RunClauses_eA π u) ∈ Γ'.toMG'.MIS → Γ.molRep u ∈ Γ.toMG'.MIS := by
    intro u hu
    have hint : Γ.molRep u ∈ Γ.toMG'.int := by
      rcases u with b | b
      · exfalso
        have := GlobalGood_isRight_of_mem_MIS Γ' hu
        simp [RunClauses_eA] at this
      · simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨b, rfl⟩
    rw [← RunClauses_iso_molRep h] at hu
    exact (TerminationC_mis_iff hT hint).1 hu
  rw [he] at hx hy hc hm
  simp only [Comp.map] at hx hy hc hm
  refine ⟨⟨hk', hmis _ hx, hmis _ hy, ?_⟩, fun c hcm hcond => ?_⟩
  · rcases hm with hm | ⟨l', hl', hhd⟩
    · exact Or.inl ((RunClauses_iso_sameMol h _ _).1 hm)
    · right
      refine ⟨l'.map (Function.invFunOn (Sum.map σ id) {e | Γ.toMG'.cls e ≠ none}),
        TerminationC_pdOrder_mis hT' hl', ?_⟩
      rw [List.head?_map, hhd]
      simp only [Option.map_some]
      congr 1
      have hpres : Γ.toMG'.cls (.inl i) ≠ none := by
        obtain ⟨-, hmem, -⟩ := hl'
        have hin : (Sum.inl (σ i) : Fin Γ'.comps.length ⊕ Fin 3) ∈ l' := by
          rcases l' with _ | ⟨e, l'⟩
          · simp at hhd
          · simp only [List.head?_cons, Option.some.injEq] at hhd
            rw [hhd]; exact List.mem_cons_self
        have hip := ((hmem _).1 hin).1
        have hp' : Γ'.toMG'.cls (.inl (σ i)) ≠ none := by
          intro hn
          simp only [MGraph.induce, hn] at hip
          split_ifs at hip
        obtain ⟨e, he1, he2⟩ := TrH.surj hT _ hp'
        rcases e with j | b
        · simp only [Sum.map_inl, Sum.inl.injEq] at he2
          rw [← hbij.1 he2]
          exact he1
        · simp at he2
      have hinj : Set.InjOn (Sum.map σ id) {e | Γ.toMG'.cls e ≠ none} :=
        fun a ha b hb hab => TrH.ginj hT a b ha hb hab
      exact hinj.leftInvOn_invFunOn hpres
  · obtain ⟨c', hc', hr⟩ := RunClauses_iso_mem h hcm
    obtain ⟨hk'', -, -, hxy, -⟩ := RunClauses_swapR_eq hr
    simp only [Comp.map] at hk'' hxy
    have hinj := (RunClauses_eA π).injective
    have hcond' : c'.kind = .G .minus ∧ c'.y = RunClauses_eA π Γ.comps[i].y ∨
        c'.kind = .waved .s ∧ (c'.x = RunClauses_eA π Γ.comps[i].y ∨
          c'.y = RunClauses_eA π Γ.comps[i].y) := by
      rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have hcc : c' = c.map (RunClauses_eA π) := by
          rcases hr with he' | ⟨hk3, -⟩
          · exact he'
          · exfalso
            simp only [Comp.map] at hk3
            rw [h1] at hk3
            rcases hk3 with h' | h' | h' <;> cases h'
        rw [hcc]
        exact ⟨h1, by simp [Comp.map, h2]⟩
      · right
        refine ⟨hk''.trans h1, ?_⟩
        rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3, h4] <;> rcases h2 with h2 | h2 <;>
          rw [h2] <;> simp
    obtain ⟨h1, h2⟩ := hc c' hc' hcond'
    rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h3, RunClauses_eA_isRight] at h1
      rw [h4, RunClauses_eA_isRight] at h2
      exact ⟨h1, h2⟩
    · rw [h3, RunClauses_eA_isRight] at h1
      rw [h4, RunClauses_eA_isRight] at h2
      exact ⟨h2, h1⟩

/-- The molecular graph of a graph with one more copy of a `×`-dotted edge is a change of names of
the molecular graph: the identity on the molecules and the inclusion of the positions. -/
private theorem TerminationC_app_trH {Γ : Graph 3 n} {d : Comp (Atom 3 n)} (hd : d ∈ Γ.comps)
    (hk : d.kind = .xdot) (co : Coeff) :
    ∃ ι : Fin Γ.comps.length → Fin (⟨Γ.comps ++ [d], co⟩ : Graph 3 n).comps.length,
      (∀ j, (ι j : ℕ) = j) ∧
      TrH Γ.toMG' (⟨Γ.comps ++ [d], co⟩ : Graph 3 n).toMG' id (Sum.map ι id)
        (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext) := by
  set Γ' : Graph 3 n := ⟨Γ.comps ++ [d], co⟩ with hΓ'
  have hmem : ∀ e, e ∈ Γ'.comps ↔ e ∈ Γ.comps := by
    intro e
    simp only [hΓ', List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl)
      · exact h
      · exact hd
    · exact Or.inl
  have hrep := Termination_molRep_mem hmem
  have hsb := Termination_sameBlock_mem hmem
  have hfc := Termination_flatComp_congr hsb
  have han := Termination_anchor_congr hsb
  have hlt : ∀ j : Fin Γ.comps.length, (j : ℕ) < Γ'.comps.length := fun j => by
    simp only [hΓ', List.length_append, List.length_singleton]
    omega
  have hget : ∀ j : Fin Γ.comps.length, Γ'.comps[(j : ℕ)]'(hlt j) = Γ.comps[j] := fun j =>
    List.getElem_append_left _
  let ι : Fin Γ.comps.length → Fin Γ'.comps.length := fun j => ⟨j, hlt j⟩
  have hcls : ∀ j, Γ'.toMG'.cls (.inl (ι j)) = Γ.toMG'.cls (.inl j) := by
    intro j
    simp only [Graph.toMG', Fin.getElem_fin, ι, hget, hfc, hrep]
  have hends : ∀ j, Γ'.toMG'.ends (.inl (ι j)) = Γ.toMG'.ends (.inl j) := by
    intro j
    simp only [Graph.toMG', Fin.getElem_fin, ι, hget, hfc, hrep]
  have hclsr : ∀ a, Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a) := by
    intro a
    simp only [Graph.toMG', han]
  have hendsr : ∀ a, Γ'.toMG'.ends (.inr a) = Γ.toMG'.ends (.inr a) := by
    intro a
    simp only [Graph.toMG', han, hrep]
  refine ⟨ι, fun _ => rfl, TrH.mk (Set.injOn_id _) (fun v hv => Or.inl hv) (fun v hv => Or.inr hv)
    (fun e _ => ?_) ?_ ?_ ?_ ?_ ?_ ?_⟩
  · obtain ⟨h1, h2⟩ := MolInsert_toMG'_ends_vtx 3 n Γ e
    exact ⟨h1, h2⟩
  · simp only [Graph.toMG', Finset.image_id, hrep]
  · simp only [Graph.toMG', Finset.image_id]
  · rintro (a | a) (b | b) - - h
    · simp only [Sum.map_inl, Sum.inl.injEq] at h
      exact congrArg Sum.inl (Fin.ext (by simpa [ι] using congrArg Fin.val h))
    · simp at h
    · simp at h
    · simpa using h
  · rintro (j | a) _
    · exact hcls j
    · exact hclsr a
  · rintro (j | a) _
    · left
      rw [Sum.map_inl, hends j]
      rfl
    · left
      simp only [Sum.map_inr, id, hendsr a]
  · rintro (j | a) hj
    · by_cases hjl : (j : ℕ) < Γ.comps.length
      · refine ⟨.inl ⟨j, hjl⟩, ?_, rfl⟩
        rw [← hcls]
        exact hj
      · exfalso
        have hj' : (j : ℕ) = Γ.comps.length := by
          have := j.2
          simp [hΓ'] at this
          omega
        have hdj : Γ'.comps[j] = d := by
          simp only [Fin.getElem_fin, hΓ', hj']
          exact List.getElem_concat_length rfl _
        apply hj
        simp only [Graph.toMG', hdj]
        split_ifs
        · rfl
        · simp [Graph.flatComp, hk, Kind.mclass]
    · exact ⟨.inr a, by rw [← hclsr]; exact hj, rfl⟩

/-- **The choice of `α` is kept by one more copy of a `×`-dotted edge** (the step `xdotDup`): the
blue solid edges of Step 2 and their atoms are the same. -/
private theorem TerminationC_qual_app {Γ : Graph 3 n} {d : Comp (Atom 3 n)} (hd : d ∈ Γ.comps)
    (hk : d.kind = .xdot) (co : Coeff) (a : Fin n) :
    TerminationC_Qual (⟨Γ.comps ++ [d], co⟩ : Graph 3 n) a ↔ TerminationC_Qual Γ a := by
  classical
  set Γ' : Graph 3 n := ⟨Γ.comps ++ [d], co⟩ with hΓ'
  obtain ⟨ι, hι, hT⟩ := TerminationC_app_trH hd hk co
  have hmem : ∀ e, e ∈ Γ'.comps ↔ e ∈ Γ.comps := by
    intro e
    simp only [hΓ', List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl)
      · exact h
      · exact hd
    · exact Or.inl
  have hrep := Termination_molRep_mem hmem
  have hsm := Termination_sameMol_mem hmem
  have hmis : Γ'.toMG'.MIS = Γ.toMG'.MIS := by
    rw [TerminationC_mis_image hT, Finset.image_id]
  have hget : ∀ j : Fin Γ.comps.length, Γ'.comps[ι j] = Γ.comps[j] := by
    intro j
    simp only [Fin.getElem_fin, hι]
    exact List.getElem_append_left _
  have hlast : ∀ j' : Fin Γ'.comps.length, Γ'.comps[j'].kind ≠ .xdot → ∃ j, ι j = j' := by
    intro j' hj'
    by_cases hjl : (j' : ℕ) < Γ.comps.length
    · exact ⟨⟨j', hjl⟩, Fin.ext (hι _)⟩
    · exfalso
      have hj : (j' : ℕ) = Γ.comps.length := by
        have := j'.2
        simp [hΓ'] at this
        omega
      apply hj'
      simp only [Fin.getElem_fin, hΓ', hj, List.getElem_concat_length rfl _]
      exact hk
  constructor
  · rintro ⟨j', hy, ⟨⟨hk', hx, hyM, hm⟩, hc⟩⟩
    obtain ⟨j, rfl⟩ := hlast j' (by rw [hk']; simp)
    rw [hget] at hy hk' hx hyM hm hc
    rw [hrep, hmis] at hx hyM
    refine ⟨j, hy, ⟨hk', hx, hyM, ?_⟩, fun c hcm hcond => hc c ((hmem c).2 hcm) hcond⟩
    rcases hm with hm | ⟨l', hl', hhd⟩
    · exact Or.inl ((hsm _ _).1 hm)
    · right
      have : Nonempty (Atom 3 n) := ⟨.inl 0⟩
      have : Nonempty (Fin Γ.comps.length ⊕ Fin 3) := ⟨.inr 0⟩
      have hT' := TrH.symm hT
      refine ⟨l'.map (Function.invFunOn (Sum.map ι id) {e | Γ.toMG'.cls e ≠ none}),
        TerminationC_pdOrder_mis hT' hl', ?_⟩
      rw [List.head?_map, hhd]
      simp only [Option.map_some]
      congr 1
      have hpres : Γ.toMG'.cls (.inl j) ≠ none := by
        obtain ⟨-, hmem', -⟩ := hl'
        have hin : (Sum.inl (ι j) : Fin Γ'.comps.length ⊕ Fin 3) ∈ l' := by
          rcases l' with _ | ⟨e, l'⟩
          · simp at hhd
          · simp only [List.head?_cons, Option.some.injEq] at hhd
            rw [hhd]; exact List.mem_cons_self
        have hip := ((hmem' _).1 hin).1
        have hp' : Γ'.toMG'.cls (.inl (ι j)) ≠ none := by
          intro hn
          simp only [MGraph.induce, hn] at hip
          split_ifs at hip
        obtain ⟨e, he1, he2⟩ := TrH.surj hT _ hp'
        rcases e with j₂ | b
        · simp only [Sum.map_inl, Sum.inl.injEq] at he2
          have : j₂ = j := Fin.ext (by rw [← hι, ← hι j, he2])
          rw [← this]
          exact he1
        · simp at he2
      have hinj : Set.InjOn (Sum.map ι id) {e | Γ.toMG'.cls e ≠ none} :=
        fun a ha b hb hab => TrH.ginj hT a b ha hb hab
      exact hinj.leftInvOn_invFunOn hpres
  · rintro ⟨j, hy, ⟨⟨hk', hx, hyM, hm⟩, hc⟩⟩
    refine ⟨ι j, by rw [hget]; exact hy, ⟨by rw [hget]; exact hk', ?_, ?_, ?_⟩, ?_⟩
    · rw [hget, hrep, hmis]; exact hx
    · rw [hget, hrep, hmis]; exact hyM
    · rw [hget]
      rcases hm with hm | ⟨l, hl, hhd⟩
      · exact Or.inl ((hsm _ _).2 hm)
      · right
        refine ⟨l.map (Sum.map ι id), TerminationC_pdOrder_mis hT hl, ?_⟩
        rw [List.head?_map, hhd]
        rfl
    · intro c hcm hcond
      rw [hget] at hcond
      exact hc c ((hmem c).1 hcm) hcond

/-- **The choice of `α` is kept by a reordering that does not renumber the atoms**. -/
private theorem TerminationC_qual_iso {Γ Γ' : Graph 3 n} (h : RunClauses_Iso (Equiv.refl _) Γ Γ')
    (a : Fin n) : TerminationC_Qual Γ' a ↔ TerminationC_Qual Γ a := by
  obtain ⟨σ, hbij, hσ⟩ := TerminationC_iso_sigma h
  have hid : ∀ u, RunClauses_eA (Equiv.refl (Fin n)) u = u := by
    intro u; cases u <;> rfl
  have hG : ∀ i, Γ.comps[i].kind = .G .plus → Γ'.comps[σ i] = Γ.comps[i] := by
    intro i hk
    rcases hσ i with he | ⟨hk', -⟩
    · rw [he]
      have hf : ⇑(RunClauses_eA (Equiv.refl (Fin n))) = id := funext hid
      rw [hf]
      cases Γ.comps[i]
      simp [Comp.map]
    · simp only [Comp.map] at hk'
      rw [hk] at hk'
      rcases hk' with h' | h' | h' <;> cases h'
  constructor
  · rintro ⟨j, hy, hS⟩
    obtain ⟨i, rfl⟩ := hbij.2 j
    have hS' := TerminationC_iso_step2_bwd h σ hσ hbij hS
    rw [hG i hS'.1.1] at hy
    exact ⟨i, hy, hS'⟩
  · rintro ⟨i, hy, hS⟩
    refine ⟨σ i, by rw [hG i hS.1.1]; exact hy, TerminationC_iso_step2 h σ hσ hbij hS⟩

/-- `TerminationC_alpha` depends on the graph only through `TerminationC_Qual`. -/
private theorem TerminationC_alpha_congr {Γ Γ' : Graph 3 n}
    (h : ∀ a, TerminationC_Qual Γ' a ↔ TerminationC_Qual Γ a) :
    TerminationC_alpha ⟨n, Γ'⟩ = TerminationC_alpha ⟨n, Γ⟩ := by
  classical
  unfold TerminationC_alpha
  by_cases hex : ∃ a, TerminationC_Qual Γ a
  · have hex' : ∃ a, TerminationC_Qual Γ' a := by
      obtain ⟨a, ha⟩ := hex; exact ⟨a, (h a).2 ha⟩
    rw [dite_eq_left hex, dite_eq_left hex']
    congr 1
    have hmem : ∀ y, y ∈ Finset.univ.filter (TerminationC_Qual Γ') ↔
        y ∈ Finset.univ.filter (TerminationC_Qual Γ) := by
      intro y; simp [h y]
    refine le_antisymm (Finset.max'_le _ _ _ fun y hy => Finset.le_max' _ _ ((hmem y).1 hy))
      (Finset.max'_le _ _ _ fun y hy => Finset.le_max' _ _ ((hmem y).2 hy))
  · have hex' : ¬ ∃ a, TerminationC_Qual Γ' a := by
      rintro ⟨a, ha⟩; exact hex ⟨a, (h a).1 ha⟩
    rw [dite_eq_right hex, dite_eq_right hex']

/-- The molecular graph does not read the coefficient. -/
private theorem TerminationC_toMG'_coeff (cs : List (Comp (Atom 3 n))) (c c' : Coeff) :
    Graph.toMG' (⟨cs, c⟩ : Graph 3 n) = Graph.toMG' ⟨cs, c'⟩ := by
  unfold Graph.toMG'
  congr 1
  · funext e
    rcases e with i | a <;> rfl
  · funext e
    rcases e with i | a <;> rfl

/-- **The choice of `α` does not read the coefficient.** -/
private theorem TerminationC_qual_coeff (Γ : Graph 3 n) (co : Coeff) (a : Fin n) :
    TerminationC_Qual (⟨Γ.comps, co⟩ : Graph 3 n) a ↔ TerminationC_Qual Γ a := by
  obtain ⟨cs, c⟩ := Γ
  unfold TerminationC_Qual Graph.Step2EdgeB' Graph.Step2EdgeB
  rw [TerminationC_toMG'_coeff cs co c]
  exact Iff.rfl

/-- The graph with the `×`-dotted edge `j` erased and a copy of the parallel `×`-dotted edge `i`
appended is a reordering that does not renumber the atoms. -/
private theorem TerminationC_iso_drop (Γ : Graph 3 n) (i j : Fin Γ.comps.length)
    (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) :
    RunClauses_Iso (Equiv.refl _) Γ ⟨Γ.comps.eraseIdx j ++ [Γ.comps[i]], Γ.coeff⟩ := by
  have hid : ∀ c : Comp (Atom 3 n), c.map (RunClauses_eA (Equiv.refl (Fin n))) = c := by
    intro c
    have hf : ⇑(RunClauses_eA (Equiv.refl (Fin n))) = id := by
      funext u; cases u <;> rfl
    rw [hf]
    cases c
    simp [Comp.map]
  refine ⟨rfl, Γ.comps.set j Γ.comps[i], ?_, ?_⟩
  · rw [List.map_id'' hid]
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

/-- **The choice of `α` is kept by the removal of one of two parallel `×`-dotted edges** (the step
`xdotDrop`). -/
private theorem TerminationC_qual_drop (Γ : Graph 3 n) (i j : Fin Γ.comps.length) (hij : i ≠ j)
    (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) (co : Coeff) (a : Fin n) :
    TerminationC_Qual (⟨Γ.comps.eraseIdx j, co⟩ : Graph 3 n) a ↔ TerminationC_Qual Γ a := by
  have hmem : Γ.comps[i] ∈ (⟨Γ.comps.eraseIdx j, co⟩ : Graph 3 n).comps := by
    show Γ.comps[i] ∈ Γ.comps.eraseIdx j
    rw [List.mem_eraseIdx_iff_getElem]
    exact ⟨i, i.2, fun h => hij (Fin.ext h), rfl⟩
  rw [← TerminationC_qual_app hmem hk Γ.coeff a]
  exact (TerminationC_qual_iso (TerminationC_iso_drop Γ i j hc hk) a)

end Stable


/-! ## The measure `TerminationC_nu` of the normal form of Step 2 -/

section Measure

open private RunClauses_Iso from RBM8D.GlobalExp.RunClauses

variable {n₀ : ℕ}

private theorem TerminationC_count_app {β : Type*} (L : List β) (c : β) (p : β → Bool) :
    ((L ++ [c]).filter p).length = (L.filter p).length + (if p c then 1 else 0) := by
  rw [List.filter_append, List.length_append]
  cases h : p c <;> simp [h]

private theorem TerminationC_count_erase {β : Type*} (L : List β) (j : ℕ) (hj : j < L.length)
    (p : β → Bool) :
    (L.filter p).length = ((L.eraseIdx j).filter p).length + (if p L[j] then 1 else 0) := by
  rw [((List.getElem_cons_eraseIdx_perm hj).symm.filter p).length_eq, List.filter_cons]
  cases h : p L[j] <;> simp [h]

/-- A sum over a finite set changes by one at one point. -/
private theorem TerminationC_sum_dec {β : Type*} (S : Finset β) (F F' : β → ℕ)
    {v : β} (hv : v ∈ S) (hF : ∀ w ∈ S, w ≠ v → F' w = F w) (hFv : F' v + 1 = F v) :
    (∑ w ∈ S, F' w) + 1 = ∑ w ∈ S, F w := by
  classical
  have h := Finset.sum_congr rfl fun w hw =>
    hF w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)
  rw [← Finset.add_sum_erase S F' hv, ← Finset.add_sum_erase S F hv, h, ← hFv]
  ring

private theorem TerminationC_joinsB_ne {c : Comp (Atom 3 n₀)} {u v w : Atom 3 n₀}
    (hc : TerminationC_Joins c u v) (hvu : v ≠ u) (hw : w ≠ v) :
    TerminationC_joinsB u w c = false := by
  simp only [TerminationC_joinsB, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact ⟨Or.inr (Ne.symm hw), Or.inr hvu⟩
  · exact ⟨Or.inl hvu, Or.inl (Ne.symm hw)⟩

private theorem TerminationC_joinsB_eq {c : Comp (Atom 3 n₀)} {u v : Atom 3 n₀}
    (hc : TerminationC_Joins c u v) : TerminationC_joinsB u v c = true := by
  simp only [TerminationC_joinsB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact hc

/-- The distance `TerminationC_pairTerm` drops by one when the number of `×`-dotted edges between
`a` and one atom `v ≠ a` moves by one towards the number of solid edges, the rest unchanged. -/
private theorem TerminationC_pairTerm_dec {Γ Γ' : Graph 3 n₀} {a v : Atom 3 n₀} (hva : v ≠ a)
    (hs : ∀ w, TerminationC_smult Γ' a w = TerminationC_smult Γ a w)
    (hx : ∀ w, w ≠ v → TerminationC_xmult Γ' a w = TerminationC_xmult Γ a w)
    (hxv : TerminationC_xmult Γ' a v + 1 = TerminationC_xmult Γ a v ∧
        TerminationC_smult Γ a v < TerminationC_xmult Γ a v ∨
      TerminationC_xmult Γ' a v = TerminationC_xmult Γ a v + 1 ∧
        TerminationC_xmult Γ a v < TerminationC_smult Γ a v) :
    TerminationC_pairTerm Γ' a + 1 = TerminationC_pairTerm Γ a := by
  classical
  unfold TerminationC_pairTerm
  simp only [hs]
  refine TerminationC_sum_dec _ _ _ (v := v) ?_ (fun w _ hw => by rw [hx w hw]) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hva
  · rcases hxv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **At a host of Steps 2–3 the measure is `0`**: the coefficient of `H.glue x y₁ y₂ (tVar true)`
is divisible by `m m̄`, the chosen atom `α` is the new atom (the largest), and at `α` the
`×`-dotted edges of the `t`-variable match its solid edges. -/
theorem TerminationC_nu_host {g : Σ n₀ : ℕ, Graph 3 n₀} (h : TerminationC_GlueHost g) :
    TerminationC_nu g = 0 := by
  classical
  obtain ⟨m, H, x, y₁, y₂, rfl, hp⟩ := h
  set G := H.glue x y₁ y₂ (tVar true) with hG
  have hlen : H.comps.length + 1 < G.comps.length := by
    rw [hG, TerminationC_glue_comps]; simp [liftCs]
  have hq : TerminationC_Qual G (Fin.last m) := by
    refine ⟨⟨H.comps.length + 1, hlen⟩, ?_, hp.2.2.2.2.2.2.2.2 _ rfl⟩
    simp only [Fin.getElem_fin, hG, TerminationC_glue_comps]
    rw [List.getElem_append_right (by simp [liftCs])]
    simp [liftCs, TerminationC_newA]
  have hα : TerminationC_alpha ⟨m + 1, G⟩ = some (Fin.last m) := by
    unfold TerminationC_alpha
    rw [dite_eq_left ⟨_, hq⟩]
    congr 1
    exact le_antisymm (Fin.le_last _) (Finset.le_max' _ _ (by simpa using hq))
  have hlift : ∀ c ∈ liftCs 1 H.comps, c.x ≠ .inr (Fin.last m) ∧ c.y ≠ .inr (Fin.last m) := by
    intro c hc
    simp only [liftCs, List.mem_map] at hc
    obtain ⟨d, -, rfl⟩ := hc
    exact ⟨TerminationC_liftA_ne _, TerminationC_liftA_ne _⟩
  have hpair : ∀ w, TerminationC_xmult G (.inr (Fin.last m)) w =
      TerminationC_smult G (.inr (Fin.last m)) w := by
    intro w
    rw [TerminationC_xmult_eq, TerminationC_smult_eq, hG, TerminationC_glue_comps,
      List.filter_append, List.filter_append, List.length_append, List.length_append]
    have h1 : (liftCs 1 H.comps).filter (fun c => c.kind == .xdot &&
        TerminationC_joinsB (.inr (Fin.last m)) w c) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      simp [TerminationC_joinsB, (hlift c hc).1, (hlift c hc).2]
    have h2 : (liftCs 1 H.comps).filter (fun c => c.kind.isSolid &&
        TerminationC_joinsB (.inr (Fin.last m)) w c) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      simp [TerminationC_joinsB, (hlift c hc).1, (hlift c hc).2]
    rw [h1, h2]
    have hn1 : (liftA 1 y₁ == (Sum.inr (Fin.last m) : Atom 3 (m + 1))) = false := by
      simpa using TerminationC_liftA_ne y₁
    have hn2 : (liftA 1 y₂ == (Sum.inr (Fin.last m) : Atom 3 (m + 1))) = false := by
      simpa using TerminationC_liftA_ne y₂
    simp only [TerminationC_newA, List.filter_cons, List.filter_nil, TerminationC_joinsB, hn1, hn2]
    by_cases e1 : liftA 1 y₁ = w <;> by_cases e2 : liftA 1 y₂ = w <;>
      simp [e1, e2, Kind.isSolid]
  have hdiv : cm * cmb ∣ G.coeff := ⟨H.coeff, by rw [hG]; show H.coeff * (cm * cmb) = _; ring⟩
  unfold TerminationC_nu
  rw [hα]
  simp only [hdiv, ite_true, TerminationC_pairTerm, hpair, Nat.sub_self, add_zero,
    Finset.sum_const_zero, zero_add]
  rw [ite_eq_left ⟨m, H, x, y₁, y₂, rfl, hp⟩]

/-- **The identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1` lowers the measure** (the step `coeffNorm`):
the coefficient becomes divisible by `m m̄`, the components and the chosen atom are kept. -/
theorem TerminationC_nu_coeffNorm {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (h : TerminationC_Adm n D 𝔈 g .coeffNorm) :
    ∀ g' ∈ TerminationC_stepOut n D 𝒯 𝔈 g .coeffNorm, TerminationC_nu g' < TerminationC_nu g := by
  classical
  obtain ⟨-, hGH, hdiv⟩ := h
  intro g' hg'
  obtain ⟨n₀, Γ⟩ := g
  simp only [TerminationC_stepOut, List.mem_singleton] at hg'
  subst hg'
  have hα : TerminationC_alpha ⟨n₀, ⟨Γ.comps,
      Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩⟩ =
      TerminationC_alpha ⟨n₀, Γ⟩ := TerminationC_alpha_congr fun b => TerminationC_qual_coeff Γ _ b
  have hd : cm * cmb ∣ Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv :=
    ⟨Γ.coeff * MvPolynomial.X .mInv * MvPolynomial.X .mBarInv, by ring⟩
  unfold TerminationC_nu
  rw [hα]
  simp only [hd, ite_true, hdiv, ite_false, hGH]
  rcases TerminationC_alpha ⟨n₀, Γ⟩ with - | a
  · dsimp only
    split_ifs <;> omega
  · simp only
    have : TerminationC_pairTerm (⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb *
      MvPolynomial.X .mBarInv⟩ : Graph 3 n₀) (.inr a) = TerminationC_pairTerm Γ (.inr a) := rfl
    rw [this]
    split_ifs <;> omega

/-- **The duplication of a `×`-dotted edge at `α` lowers the measure** (the step `xdotDup`): the
chosen atom is kept (`TerminationC_qual_app`) and the distance at `α` drops by one. -/
theorem TerminationC_nu_xdotDup {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} {g : Σ n₀ : ℕ, Graph 3 n₀}
    {i : ℕ} (h : TerminationC_Adm n D 𝔈 g (.xdotDup i)) :
    ∀ g' ∈ TerminationC_stepOut n D 𝒯 𝔈 g (.xdotDup i), TerminationC_nu g' < TerminationC_nu g := by
  classical
  obtain ⟨hi, ⟨hk, -, -, a, v, ha, hva, hj, hlt⟩, -, hGH⟩ := h
  intro g' hg'
  obtain ⟨n₀, Γ⟩ := g
  simp only [TerminationC_stepOut, List.mem_singleton] at hg'
  subst hg'
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.toList_some]
  have hk : Γ.comps[i].kind = .xdot := hk
  have hj : TerminationC_Joins Γ.comps[i] (.inr a) v := hj
  have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
  have hα : TerminationC_alpha ⟨n₀, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩ = some a := by
    rw [TerminationC_alpha_congr fun b => TerminationC_qual_app hmem hk Γ.coeff b]
    exact ha
  have hdec := TerminationC_pairTerm_dec (Γ := Γ) (Γ' := ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩)
    (a := .inr a) hva
    (fun w => by
      rw [TerminationC_smult_eq, TerminationC_smult_eq, TerminationC_count_app]
      simp [hk, Kind.isSolid])
    (fun w hw => by
      rw [TerminationC_xmult_eq, TerminationC_xmult_eq, TerminationC_count_app]
      simp [TerminationC_joinsB_ne hj (Ne.symm (Ne.symm hva)) hw])
    (Or.inr ⟨by
      rw [TerminationC_xmult_eq, TerminationC_xmult_eq, TerminationC_count_app]
      simp [hk, TerminationC_joinsB_eq hj], hlt⟩)
  unfold TerminationC_nu
  rw [hα]
  simp only [ha, hGH, ite_false]
  split_ifs <;> omega

/-- **The removal of one of two parallel `×`-dotted edges at `α` lowers the measure** (the step
`xdotDrop`): the chosen atom is kept (`TerminationC_qual_drop`) and the distance at `α` drops by
one. -/
theorem TerminationC_nu_xdotDrop {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} {g : Σ n₀ : ℕ, Graph 3 n₀}
    {i j : ℕ} (h : TerminationC_Adm n D 𝔈 g (.xdotDrop i j)) :
    ∀ g' ∈ TerminationC_stepOut n D 𝒯 𝔈 g (.xdotDrop i j),
      TerminationC_nu g' < TerminationC_nu g := by
  classical
  obtain ⟨hi, hj', ⟨hij, hc, hk, -, -, a, v, ha, hva, hj, hlt⟩, -, hGH⟩ := h
  intro g' hg'
  obtain ⟨n₀, Γ⟩ := g
  simp only [TerminationC_stepOut, List.mem_singleton] at hg'
  subst hg'
  have hα : TerminationC_alpha ⟨n₀, ⟨Γ.comps.eraseIdx j, Γ.coeff⟩⟩ = some a := by
    rw [TerminationC_alpha_congr fun b => TerminationC_qual_drop Γ ⟨i, hi⟩ ⟨j, hj'⟩
      hij hc hk Γ.coeff b]
    exact ha
  have hkj : Γ.comps[j].kind = .xdot := by
    simp only [Fin.getElem_fin] at hc hk
    rcases hc with h' | h' <;> rw [h'] <;> exact hk
  have hjj : TerminationC_Joins Γ.comps[j] (.inr a) v := by
    simp only [Fin.getElem_fin] at hc hj
    rcases hc with h' | h' <;> rw [h']
    · exact hj
    · rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
  have hdec := TerminationC_pairTerm_dec (Γ := Γ) (Γ' := ⟨Γ.comps.eraseIdx j, Γ.coeff⟩)
    (a := .inr a) hva
    (fun w => by
      rw [TerminationC_smult_eq, TerminationC_smult_eq,
        TerminationC_count_erase Γ.comps j hj']
      simp [hkj, Kind.isSolid])
    (fun w hw => by
      rw [TerminationC_xmult_eq, TerminationC_xmult_eq,
        TerminationC_count_erase Γ.comps j hj']
      simp [TerminationC_joinsB_ne hjj (Ne.symm (Ne.symm hva)) hw])
    (Or.inl ⟨by
      rw [TerminationC_xmult_eq, TerminationC_xmult_eq,
        TerminationC_count_erase Γ.comps j hj']
      simp [hkj, TerminationC_joinsB_eq hjj], hlt⟩)
  unfold TerminationC_nu
  rw [hα]
  simp only [ha, hGH, ite_false]
  split_ifs <;> omega

/-- **A reordering to a host lowers the measure** (the step `reorder`): the measure is `0` at the
host and at least `1` at a graph that is not a host. -/
theorem TerminationC_nu_reorder {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} {g : Σ n₀ : ℕ, Graph 3 n₀}
    {Γ' : Graph 3 g.1} (h : TerminationC_Adm n D 𝔈 g (.reorder Γ')) :
    ∀ g' ∈ TerminationC_stepOut n D 𝒯 𝔈 g (.reorder Γ'), TerminationC_nu g' < TerminationC_nu g := by
  classical
  obtain ⟨-, hGH, hGH'⟩ := h
  intro g' hg'
  simp only [TerminationC_stepOut, List.mem_singleton] at hg'
  subst hg'
  rw [TerminationC_nu_host hGH']
  unfold TerminationC_nu
  simp only [hGH, ite_false]
  omega

end Measure

/-! ## The selector -/

/-- The data of a host of Steps 2–3 chosen at a host. -/
def TerminationC_hostLoc {g : Σ n₀ : ℕ, Graph 3 n₀} (h : TerminationC_GlueHost g) :
    TerminationC_Loc g.1 :=
  .subst h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose

private theorem TerminationC_hostLoc_spec {g : Σ n₀ : ℕ, Graph 3 n₀} (h : TerminationC_GlueHost g) :
    ∃ (m : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m), TerminationC_hostLoc h = .subst m H x y₁ y₂ ∧
      g = ⟨m + 1, H.glue x y₁ y₂ (tVar true)⟩ ∧ TerminationC_HostPrem H x y₁ y₂ :=
  ⟨_, _, _, _, _, rfl, h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec⟩

open Classical in
/-- **The selector** of [II, Strategy 6.6], a function of the graph alone: in this order, the empty
sum at a `×`-dotted loop; `O_dot` on a graph that is not normal regular; the removal of a
redundant dotted edge; the `Q`-expansion of Step 3 at the internal label atom of a graph
`Γ₀ Q_x(Γ̃₀)` that is not a `Q`-graph; Step 1 at an atom of the minimal isolated subset that is
not locally standard; the substitution of Steps 2–3 at a host; and at the atom `α` chosen in
Step 2: the identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1`, the removal and the duplication of a
`×`-dotted edge at `α`, and a reordering to a host. -/
def TerminationC_sel (g : Σ n₀ : ℕ, Graph 3 n₀) : TerminationC_Loc g.1 :=
  if h₁ : ∃ i : Fin g.2.comps.length, g.2.comps[i].kind = .xdot ∧
      g.2.comps[i].x = g.2.comps[i].y then .xdotLoop h₁.choose
  else if ¬ ∃ C, g.2.Normal C then .dot
  else if h₃ : ∃ Γ', DotNormStep g.2 Γ' then .dropDot h₃.choose
  else if h₄ : ∃ x : Fin g.1, g.2.IsQFormAt (.inr x) ∧ ¬ g.2.IsQGraph then .qexp h₄.choose
  else if h₅ : ∃ x : Fin g.1, g.2.molRep (.inr x) ∈ g.2.toMG'.MIS ∧
      ¬ (g.2.wt (.inr x) = 0 ∧ (g.2.deg (.inr x) = 0 ∨
        (g.2.deg (.inr x) = 2 ∧ g.2.stdNeutralAt (.inr x) = true))) then
    .loc (TerminationC_locOp g.2 (.inr h₅.choose)) h₅.choose
  else if h₆ : TerminationC_GlueHost g then TerminationC_hostLoc h₆
  else if (TerminationC_alpha g).isSome = false then .dot
  else if ¬ cm * cmb ∣ g.2.coeff then .coeffNorm
  else if h₇ : ∃ i j, TerminationC_DropAt g i j then .xdotDrop h₇.choose h₇.choose_spec.choose
  else if h₈ : ∃ i, TerminationC_DupAt g i then .xdotDup h₈.choose
  else if h₉ : ∃ Γ', g.2.Reorder Γ' ∧ TerminationC_GlueHost ⟨g.1, Γ'⟩ then .reorder h₉.choose
  else .dot

/-- The atom chosen by `TerminationC_alpha` has the property `TerminationC_Qual`. -/
private theorem TerminationC_alpha_spec {g : Σ n₀ : ℕ, Graph 3 n₀} {a : Fin g.1}
    (h : TerminationC_alpha g = some a) : TerminationC_Qual g.2 a := by
  classical
  unfold TerminationC_alpha at h
  split_ifs at h with hq
  obtain rfl := Option.some.inj h
  have := Finset.max'_mem (Finset.univ.filter (TerminationC_Qual g.2))
    (by obtain ⟨a, ha⟩ := hq; exact ⟨a, by simpa using ha⟩)
  simpa using this

open private TerminationB_iso_gs TerminationB_iso_recoll from RBM8D.GlobalExp.TerminationB in
open private RunClauses_Iso RunClauses_SwapR RunClauses_eA RunClauses_iso_ord RunClauses_iso_normal
  RunClauses_iso_td RunClauses_iso_mem' RunClauses_swapR_eq from RBM8D.GlobalExp.RunClauses in
open private GlobalGood_isRight_of_mem_MIS from RBM8D.GlobalExp.GlobalGood in
/-- **The closure of Step 2 at `α`** at a cell graph: the coefficient divisible by `m m̄`, no
`×`-dotted loop, and no removal or duplication of a `×`-dotted edge at `α` admissible (so the
`×`-dotted edges at `α` match the solid ones), a reordering gives a host of Steps 2–3. -/
private theorem TerminationC_host_exists {n D C : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hR : TerminationC_RI n D g) (hN : g.2.Normal C) (h0 : g.2.dotExcess = 0)
    (hL : g.2.LabelFree) (hM : g.2.MISLocStdB) (hr : ¬ g.2.IsRecollision {1, 2})
    (hD : ¬ (D : ℤ) < g.2.ord) (hn : g.2.ord ≤ n)
    (hl : ¬ ∃ i : Fin g.2.comps.length, g.2.comps[i].kind = .xdot ∧
      g.2.comps[i].x = g.2.comps[i].y)
    (ha : (TerminationC_alpha g).isSome = true) (hdiv : cm * cmb ∣ g.2.coeff)
    (hdrop : ¬ ∃ i j, TerminationC_DropAt g i j) (hdup : ¬ ∃ i, TerminationC_DupAt g i) :
    ∃ Γ', g.2.Reorder Γ' ∧ TerminationC_GlueHost ⟨g.1, Γ'⟩ := by
  classical
  have hpo := Graph.paperOrd_of_dotExcess h0
  have hP := TerminationC_plain hR h0 hD
  obtain ⟨hB, hT⟩ := TerminationC_invB hR hL hD
  have hdf := TerminationC_dotFree hR.1 hD hL hN hP hr
  have hgs : gsPM' g.2 := hR.2.1.2.2.1 hL (by rw [hpo]; exact hn)
  obtain ⟨Nk, hTK⟩ : ∃ N, g.2.TKinds N :=
    hR.2.2.2.2.2.2.2.2.2.resolve_left (by rw [hpo]; exact hD)
  obtain ⟨a, haeq⟩ := Option.isSome_iff_exists.1 ha
  obtain ⟨i₀, hy₀, hS₀⟩ := TerminationC_alpha_spec haeq
  obtain ⟨⟨hk₀, hx₀M, hy₀M, hm₀⟩, hS₀c⟩ := hS₀
  have hl' : ∀ c ∈ g.2.comps, c.kind = .xdot → c.x ≠ c.y := by
    intro c hc hk hxy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact hl ⟨⟨i, hi⟩, hk, hxy⟩
  -- the atom `α` is standard neutral
  have hc₀ : g.2.comps[i₀] ∈ g.2.comps := List.getElem_mem _
  have hstd : g.2.stdNeutralAt (.inr a) = true := by
    have hmis : g.2.molRep (.inr a) ∈ g.2.toMG'.MIS := by rw [← hy₀]; exact hy₀M
    obtain ⟨-, hd⟩ := hM.2 a hmis
    rcases hd with hd | ⟨-, hs⟩
    · exfalso
      unfold Graph.deg at hd
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hd
      have := hd _ hc₀
      have hk₀' := hk₀
      have hy₀' := hy₀
      simp only [Fin.getElem_fin] at this hk₀' hy₀'
      simp [hk₀', Kind.isSolid, hy₀'] at this
    · exact hs
  have hns : ∀ c ∈ g.2.comps, c.kind.isSolid = true → c.x ≠ c.y := hN.2.1
  obtain ⟨c₂, hc₂, hk₂, hy₂, hx₂, hS⟩ := TerminationC_std_solid hns hstd hc₀ hk₀ hy₀
  have hint₀ : g.2.comps[i₀].x.isRight = true := GlobalGood_isRight_of_mem_MIS g.2 hx₀M
  have hint₂ : c₂.x.isRight = true :=
    (hS₀c c₂ hc₂ (Or.inl ⟨hk₂, hy₂.trans hy₀.symm⟩)).1
  -- the `×`-dotted edges at `α` match the solid ones
  have hsolnb : ∀ v, v ≠ .inr a → 0 < TerminationC_smult g.2 (.inr a) v ∨
      0 < TerminationC_xmult g.2 (.inr a) v → v.isRight = true := by
    intro v hv h
    have : ∃ d ∈ g.2.comps, d.kind.isSolid = true ∧
        (d.x = .inr a ∧ d.y = v ∨ d.x = v ∧ d.y = .inr a) := by
      rcases h with h | h
      · obtain ⟨i, hi⟩ := TerminationC_one_idx g.2.comps (fun c => c.kind.isSolid && TerminationC_joinsB (.inr a) v c) (by rw [← TerminationC_smult_eq]; exact h)
        simp only [TerminationC_joinsB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hi
        exact ⟨_, List.getElem_mem _, hi.1, hi.2⟩
      · obtain ⟨i, hi⟩ := TerminationC_one_idx g.2.comps (fun c => c.kind == .xdot && TerminationC_joinsB (.inr a) v c) (by rw [← TerminationC_xmult_eq]; exact h)
        simp only [TerminationC_joinsB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hi
        exact (hN.2.2 _ _ (Ne.symm hv)).1 ⟨_, List.getElem_mem _, hi.1, hi.2⟩
    obtain ⟨d, hd, hds, hdj⟩ := this
    have hda : TerminationC_at (.inr a) d = true := by
      simp only [TerminationC_at, Bool.or_eq_true, beq_iff_eq]
      rcases hdj with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    have : d ∈ [g.2.comps[i₀], c₂] := hS.subset (List.mem_filter.2 ⟨hd, by simp [hds, hda]⟩)
    rcases List.mem_pair.1 this with rfl | rfl
    · rcases hdj with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd (h.trans hy₀.symm) (hns _ hc₀ hds)
      · rw [← h]; exact hint₀
    · rcases hdj with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hx₂
      · rw [← h]; exact hint₂
  have hpair : ∀ v, v ≠ .inr a →
      TerminationC_xmult g.2 (.inr a) v = TerminationC_smult g.2 (.inr a) v := by
    intro v hv
    by_contra hne
    have hvi : v.isRight = true := hsolnb v hv (by omega)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- fewer `×`-dotted than solid edges: a duplication is admissible
      have hx1 : 1 ≤ TerminationC_xmult g.2 (.inr a) v := by
        by_contra h0'
        have h0'' : TerminationC_xmult g.2 (.inr a) v = 0 := by omega
        obtain ⟨i, hi⟩ := TerminationC_one_idx g.2.comps (fun c => c.kind.isSolid && TerminationC_joinsB (.inr a) v c)
          (by rw [← TerminationC_smult_eq]; omega)
        simp only [TerminationC_joinsB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hi
        obtain ⟨e, he, hek, hej⟩ := (hN.2.2 _ _ (Ne.symm hv)).2 ⟨_, List.getElem_mem _, hi.1, hi.2⟩
        rw [TerminationC_xmult_eq, List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0''
        have := h0'' e he
        simp [TerminationC_joinsB, hek] at this
        rcases hej with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact this.1 h1 h2
        · exact this.2 h1 h2
      obtain ⟨i, hi⟩ := TerminationC_one_idx g.2.comps (fun c => c.kind == .xdot && TerminationC_joinsB (.inr a) v c)
        (by rw [← TerminationC_xmult_eq]; exact hx1)
      simp only [TerminationC_joinsB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hi
      refine hdup ⟨i, hi.1, ?_, ?_, a, v, haeq, hv, hi.2, hlt⟩
      · rcases hi.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> [rfl; exact hvi]
      · rcases hi.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> [exact hvi; rfl]
    · -- more `×`-dotted than solid edges: a removal is admissible
      have hs1 : 1 ≤ TerminationC_smult g.2 (.inr a) v := by
        by_contra h0'
        have h0'' : TerminationC_smult g.2 (.inr a) v = 0 := by omega
        obtain ⟨i, hi⟩ := TerminationC_one_idx g.2.comps (fun c => c.kind == .xdot && TerminationC_joinsB (.inr a) v c)
          (by rw [← TerminationC_xmult_eq]; omega)
        simp only [TerminationC_joinsB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hi
        obtain ⟨e, he, hek, hej⟩ := (hN.2.2 _ _ (Ne.symm hv)).1 ⟨_, List.getElem_mem _, hi.1, hi.2⟩
        rw [TerminationC_smult_eq, List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0''
        have := h0'' e he
        simp [TerminationC_joinsB, hek] at this
        rcases hej with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact this.1 h1 h2
        · exact this.2 h1 h2
      obtain ⟨i, j, hij, hi, hj⟩ := TerminationC_two_idx g.2.comps (fun c => c.kind == .xdot && TerminationC_joinsB (.inr a) v c)
        (by rw [← TerminationC_xmult_eq]; omega)
      simp only [TerminationC_joinsB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hi hj
      have hcmp : ∀ c ∈ g.2.comps, c.kind = .xdot →
          (c.x = .inr a ∧ c.y = v ∨ c.x = v ∧ c.y = .inr a) →
          c = ⟨.xdot, .inr a, v, [], none⟩ ∨ c = ⟨.xdot, v, .inr a, [], none⟩ := by
        intro c hc hk hj'
        rw [TerminationC_eta (hP c hc).1 (hL c hc), hk]
        rcases hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact Or.inl rfl
        · exact Or.inr rfl
      refine hdrop ⟨i, j, hij, ?_, hi.1, ?_, ?_, a, v, haeq, hv, hi.2, hgt⟩
      · rcases hcmp _ (List.getElem_mem _) hi.1 hi.2 with h1 | h1 <;>
          rcases hcmp _ (List.getElem_mem _) hj.1 hj.2 with h2 | h2 <;>
          simp only [Fin.getElem_fin] at h1 h2 ⊢ <;> rw [h1, h2] <;> simp
      · rcases hi.2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> [rfl; exact hvi]
      · rcases hi.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> [exact hvi; rfl]
  -- the reordering
  obtain ⟨n₀, Γ⟩ := g
  cases n₀ with
  | zero => exact a.elim0
  | succ m =>
  obtain ⟨H, x, y₁, y₂, π, σ, hiso, hσ, hbij, hσ₀, hHL⟩ :=
    TerminationC_closure hN hP hL hstd hk₀ hy₀ hint₀ hl' hpair hdiv
  have hre : Γ.Reorder (H.glue x y₁ y₂ (tVar true)) := by
    obtain ⟨hc, cs, h1, h2⟩ := hiso
    exact ⟨hc, π, cs, h1, h2⟩
  refine ⟨H.glue x y₁ y₂ (tVar true), hre, m, H, x, y₁, y₂, rfl, ?_⟩
  have h4 : 4 ≤ Γ.ord := TerminationC_four_le_ord hN hdf hP hTK hB.2.2.1 hc₀ hc₂
    (fun h => by rw [h] at hk₀; rw [hk₀] at hk₂; cases hk₂)
    (by rw [hk₀]; rfl) (by rw [hk₂]; rfl)
    ⟨hint₀, by rw [hy₀]; rfl⟩ ⟨hint₂, by rw [hy₂]; rfl⟩
  refine ⟨by rw [RunClauses_iso_ord hiso]; exact h4, ⟨C, RunClauses_iso_normal hiso hN⟩,
    fun c' hc' => ?_, hHL, TerminationB_iso_gs hiso hB.2.2.2.1 hgs,
    fun hr' => hr (TerminationB_iso_recoll hiso hr'), RunClauses_iso_td hiso hT,
    TerminationC_iso_misLocStd hiso σ hσ hbij hM, fun i hi => ?_⟩
  · obtain ⟨c, hc, hrel⟩ := RunClauses_iso_mem' hiso hc'
    rw [(RunClauses_swapR_eq hrel).1]
    exact hdf c hc
  · have : i = σ i₀ := Fin.ext (by rw [hi, hσ₀])
    rw [this]
    exact TerminationC_iso_step2 hiso σ hσ hbij ⟨⟨hk₀, hx₀M, hy₀M, hm₀⟩, hS₀c⟩

open private Termination_not_qGraph from RBM8D.GlobalExp.Termination in
/-- **Item (ii) of [II, Lemma 6.8]** in the selector form: for a family `𝔈` of `Q`-expansions with
the clauses `QExpFamilyStmt`, the selector `TerminationC_sel` is admissible at every cutoff order
`n`, error order `D` and `T`-expansion `𝒯`. -/
theorem TerminationC_sel_adm (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (hF : QExpFamilyStmt 𝔈) (n D : ℕ) (𝒯 : TRec) : AdmSelector n D 𝒯 𝔈 TerminationC_sel := by
  intro g hdom hout
  suffices h : TerminationC_Adm n D 𝔈 g (TerminationC_sel g) from ⟨h, h.step⟩
  delta TerminationC_sel
  by_cases h₁ : ∃ i : Fin g.2.comps.length, g.2.comps[i].kind = .xdot ∧
      g.2.comps[i].x = g.2.comps[i].y
  · rw [dite_eq_left h₁]
    exact ⟨h₁.choose.2, h₁.choose_spec⟩
  rw [dite_eq_right h₁]
  by_cases h₂ : ¬ ∃ C, g.2.Normal C
  · rw [ite_eq_left h₂]
    exact h₂
  rw [ite_eq_right h₂]
  obtain ⟨C, hN⟩ := not_not.1 h₂
  have hR : TerminationC_RI n D g := hdom.resolve_left (not_not.2 ⟨C, hN⟩)
  by_cases h₃ : ∃ Γ', DotNormStep g.2 Γ'
  · rw [dite_eq_left h₃]
    exact ⟨h₃.choose_spec, ⟨C, hN⟩, hR.2.2.2.2.2.2.2.2.1
      (TerminationC_dotExcess_of_step h₃.choose_spec)⟩
  rw [dite_eq_right h₃]
  have h0 := TerminationC_dotExcess_zero hR hN h₃
  have hD : ¬ (D : ℤ) < g.2.ord := fun hD => hout (TerminationC_out_err hR hN h0 hD)
  by_cases h₄ : ∃ x : Fin g.1, g.2.IsQFormAt (.inr x) ∧ ¬ g.2.IsQGraph
  · rw [dite_eq_left h₄]
    obtain ⟨hform, hQ⟩ := h₄.choose_spec
    have hP := TerminationC_plain hR h0 hD
    obtain ⟨hv, hq⟩ := hF.1 D g.1 h₄.choose g.2 ⟨C, hN⟩ hform hP
    exact ⟨⟨C, hN⟩, hP, hD, hform, hQ, hv, hq⟩
  rw [dite_eq_right h₄]
  have hL : g.2.LabelFree := by
    by_contra hL
    rcases TerminationC_labelled hR h0 hL with hQ | hD' | hx
    · exact hout (TerminationC_out_q hR hN h0 hQ)
    · exact hD hD'
    · exact h₄ hx
  have hr : ¬ g.2.IsRecollision {1, 2} :=
    fun hr => hout (TerminationC_out_r hR hN h0 hL hD hr)
  have hn : g.2.ord ≤ n := by
    by_contra hn
    exact hout (TerminationC_out_a hR hN h0 hL hD (by omega))
  by_cases h₅ : ∃ x : Fin g.1, g.2.molRep (.inr x) ∈ g.2.toMG'.MIS ∧
      ¬ (g.2.wt (.inr x) = 0 ∧ (g.2.deg (.inr x) = 0 ∨
        (g.2.deg (.inr x) = 2 ∧ g.2.stdNeutralAt (.inr x) = true)))
  · rw [dite_eq_left h₅]
    exact TerminationC_loc_adm hR hN h0 hL hD hn hr h₁ h₅.choose_spec.1 h₅.choose_spec.2
  rw [dite_eq_right h₅]
  have hM : g.2.MISLocStdB := ⟨hL, fun i hi => by
    by_contra hb
    exact h₅ ⟨i, hi, hb⟩⟩
  by_cases h₆ : TerminationC_GlueHost g
  · rw [dite_eq_left h₆]
    obtain ⟨m, H, x, y₁, y₂, he, rfl, hp⟩ := TerminationC_hostLoc_spec h₆
    rw [he]
    exact ⟨rfl, hD, hn, hp⟩
  rw [dite_eq_right h₆]
  by_cases h₇ : (TerminationC_alpha g).isSome = false
  · rw [ite_eq_left h₇]
    exfalso
    have hP := TerminationC_plain hR h0 hD
    obtain ⟨hB, -⟩ := TerminationC_invB hR hL hD
    have hdf := TerminationC_dotFree hR.1 hD hL hN hP hr
    exact hout (TerminationC_out_det hR hN h0 hL hD hn hM hr
      (TerminationC_noStep2 hdf hB.2.1 h₇))
  rw [ite_eq_right h₇]
  have ha : (TerminationC_alpha g).isSome = true := by
    cases hα : TerminationC_alpha g <;> simp_all
  have hcell : TerminationC_Cell g := ⟨hL, hM, ha⟩
  by_cases h₈ : ¬ cm * cmb ∣ g.2.coeff
  · rw [ite_eq_left h₈]
    exact ⟨hcell, h₆, h₈⟩
  rw [ite_eq_right h₈]
  by_cases h₉ : ∃ i j, TerminationC_DropAt g i j
  · rw [dite_eq_left h₉]
    exact ⟨h₉.choose.2, h₉.choose_spec.choose.2, h₉.choose_spec.choose_spec, hcell, h₆⟩
  rw [dite_eq_right h₉]
  by_cases h₁₀ : ∃ i, TerminationC_DupAt g i
  · rw [dite_eq_left h₁₀]
    exact ⟨h₁₀.choose.2, h₁₀.choose_spec, hcell, h₆⟩
  rw [dite_eq_right h₁₀]
  by_cases h₁₁ : ∃ Γ', g.2.Reorder Γ' ∧ TerminationC_GlueHost ⟨g.1, Γ'⟩
  · rw [dite_eq_left h₁₁]
    exact ⟨h₁₁.choose_spec.1, h₆, h₁₁.choose_spec.2⟩
  rw [dite_eq_right h₁₁]
  exact absurd (TerminationC_host_exists hR hN h0 hL hM hr hD hn h₁ ha (not_not.1 h₈) h₉ h₁₀)
    h₁₁

/-- **Item (ii) of [II, Lemma 6.8]** in the selector reading: for every family `𝔈` of
`Q`-expansions of [II, Lemma 4.15] with the clauses `QExpFamilyStmt`, one selector `ℓ₀`, a function
of the graph alone chosen before the cutoff order `n`, the error order `D` and the `T`-expansion
`𝒯`, is admissible for every `n ≥ 3` and every `(n - 1)`-th order `T`-expansion `𝒯` with error
order `D`. -/
theorem TerminationC_admSelector (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (hF : QExpFamilyStmt 𝔈) :
    ∃ ℓ₀ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1,
      ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
        AdmSelector n D 𝒯 𝔈 ℓ₀ :=
  ⟨TerminationC_sel, fun n D _ 𝒯 _ _ => TerminationC_sel_adm 𝔈 hF n D 𝒯⟩

section Instances

open private h2Rec_struct from RBM8D.TExp.Second

end Instances

end RBM8D.Graphs
