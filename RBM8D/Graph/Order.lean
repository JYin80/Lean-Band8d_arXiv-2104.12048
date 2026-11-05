import RBM8D.Graph.Syntax

/-!
# Scaling order

The scaling order of [I, Def 2.12, (6.10)] = [II, Def 2.6, (2.11)].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-! ## Scaling order -/

/-- The scaling order of one component ([I, (2.12), (6.10)] = [II, (2.5), (2.11)];
[II, (4.21), (6.3), Def 9.4]): `1` for a solid edge and a light weight, `0` for regular and
`(-1)` weights, `D + 1` for `W_D`, `2` for a waved edge, `Σ oᵢ + 2 - 2l` for a `Θ` edge with
label `[o₁, …, o_l]` (`2` for the plain `Θ` edge), `2(D + 2)` for `Θ^{(n)}_err`, `0` for a
ghost edge, `2` for a dotted edge and `0` for a `×`-dotted edge. -/
def Kind.ord : Kind → ℤ
  | .G _ => 1
  | .weight _ => 0
  | .light _ => 1
  | .inv _ => 0
  | .wD _ d => (d : ℤ) + 1
  | .waved _ => 2
  | .theta o => (o.sum : ℤ) + 2 - 2 * o.length
  | .thetaErr _ d => 2 * ((d : ℤ) + 2)
  | .ghost => 0
  | .aux _ r _ => r
  | .dot => 2
  | .xdot => 0

/-- The scaling order of a graph ([I, Def 2.12, (6.10)] = [II, Def 2.6, (2.11)]): the sum of
the orders of its components minus twice the number of internal atoms. -/
def Graph.ord {k n : ℕ} (Γ : Graph k n) : ℤ :=
  (Γ.comps.map fun c => c.kind.ord).sum - 2 * n

end RBM8D.Graphs
