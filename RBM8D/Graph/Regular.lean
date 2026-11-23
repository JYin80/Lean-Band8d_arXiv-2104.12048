module

public import RBM8D.MainDefs
public import RBM8D.Graph.Syntax
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
# Regular graphs, recollision graphs and Q-graphs

Regular and normal regular graphs ([I, Def 2.11] = [II, Def 2.5], with the explicit bound `C` in place of "O(1)"), recollision graphs and Q-graphs ([I, Def 2.14] = [II, Def 3.1]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-! ## Regular graphs, recollision graphs, `Q`-graphs -/

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
