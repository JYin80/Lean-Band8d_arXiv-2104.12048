import RBM8D.Graph.Deterministic

/-!
# Weakly and strongly isolated subsets, globally standard graphs

Strongly and weakly isolated subsets ([II, Def 6.1]) and globally standard graphs
([II, Def 6.2]) on the molecular multigraph and on atomic graphs. An isolated subset is strongly
isolated iff it is not weakly isolated.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

variable {V E : Type}

/-! ## Weakly and strongly isolated subsets, globally standard graphs -/

/-- The edge `e` is a red solid edge between `S` and its complement ([II, Def 6.1]). -/
abbrev MGraph.RedCrosses (G : MGraph V E) (S : Finset V) (e : E) : Prop :=
  G.cls e = some .minus ∧ G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2 ∧ G.Cut S e

/-- Weakly isolated subsets ([II, Def 6.1]): isolated, with at least two red solid edges to the
complement. -/
def MGraph.IsWeaklyIso (G : MGraph V E) (P : Finset V) : Prop :=
  G.IsIsolated P ∧ ∃ e e', e ≠ e' ∧ G.RedCrosses P e ∧ G.RedCrosses P e'

/-- Globally standard graphs ([II, Def 6.2]): sequentially pre-deterministic, and every proper
isolated subset is weakly isolated. -/
def MGraph.GloballyStandard [DecidableEq V] [DecidableEq E] (G : MGraph V E) : Prop :=
  G.SPD ∧ ∀ P, G.IsProperIso G.int P → G.IsWeaklyIso P

section Instances

end Instances

end RBM8D.Graphs
