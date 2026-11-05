import RBM8D.Graph.Syntax
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Regular graphs, recollision graphs and Q-graphs

Regular and normal regular graphs ([I, Def 2.11] = [II, Def 2.5], with the explicit bound `C` in place of "O(1)"), recollision graphs and Q-graphs ([I, Def 2.14] = [II, Def 3.1]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-! ## Regular graphs, recollision graphs, `Q`-graphs -/

/-- The graph on the atoms whose edges are all components. -/
def Graph.edgeGraph {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, c.x = u ∧ c.y = v

/-- The graph on the atoms whose edges are the waved and diffusive edges. -/
def Graph.wavedThetaGraph {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps,
    (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v

/-- Regular graphs ([I, Def 2.11 (i)–(iii)] = [II, Def 2.5]), with the explicit bound `C` on
the numbers of atoms and components in place of "`O(1)`": connected; any two internal atoms
joined by a path of waved and `Θ` edges; no dotted edge between two internal atoms. -/
structure Graph.Regular {k n : ℕ} (C : ℕ) (Γ : Graph k n) : Prop where
  size : k + n + Γ.comps.length ≤ C
  connected : Γ.edgeGraph.Preconnected
  internal : ∀ a b : Fin n, Γ.wavedThetaGraph.Reachable (Sum.inr a) (Sum.inr b)
  noIntDot : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true

/-- Normal regular graphs ([I, Def 2.11 (iv)] = [II, Def 2.5 (iv)]): every solid edge joins two
distinct atoms (the diagonal entries `G_{xx}` are weights), and two distinct atoms are joined by
a `×`-dotted edge if and only if they are joined by a solid edge. -/
def Graph.Normal {k n : ℕ} (C : ℕ) (Γ : Graph k n) : Prop :=
  Γ.Regular C ∧ (∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) ∧ ∀ u v : Atom k n, u ≠ v →
    ((∃ c ∈ Γ.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
      (∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)))

/-- Recollision graphs ([I, Def 2.14 (i)] = [II, Def 3.1 (i)]): a dotted edge joins one of the
external atoms in `B` (the atoms `⊕`, `⊖`) to an internal atom. -/
def Graph.IsRecollision {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin k)) : Prop :=
  ∃ c ∈ Γ.comps, c.kind = .dot ∧
    ((∃ b ∈ B, c.x = Sum.inl b) ∧ c.y.isRight = true ∨
      (∃ b ∈ B, c.y = Sum.inl b) ∧ c.x.isRight = true)

/-- `Q`-graphs ([I, Def 2.14 (ii)] = [II, Def 3.1 (ii)]): for one atom `u`, some component
carries the label `Q_u`, and every solid edge, every weight and every labelled component
carries the label `Q_u`. -/
def Graph.IsQGraph {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∃ u : Atom k n, (∃ c ∈ Γ.comps, c.label = some (.Q, u)) ∧
    ∀ c ∈ Γ.comps, (c.kind.isRandom = true ∨ c.label.isSome = true) → c.label = some (.Q, u)

section Instances

end Instances

end RBM8D.Graphs
