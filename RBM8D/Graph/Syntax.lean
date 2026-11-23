module

public import RBM8D.MainDefs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# Atomic graphs: syntax

The syntax of atomic graphs of [I, Def 2.6] = [II, Def 2.2] (with the later kinds of [II, §4.4, (4.21), (6.3), Def 9.4]): atoms, component kinds, components, coefficients, graphs and formal sums. No type here depends on the dimension, the band width or the side length.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-! ## Syntax -/

/-- The relabelling of the internal atoms by a permutation `π`. -/
def Graph.relabel {k n : ℕ} (Γ : Graph k n) (π : Equiv.Perm (Fin n)) : Graph k n :=
  Γ.mapAtoms (Sum.map id π)

/-- The graph `Γ` with its coefficient multiplied by `c`. -/
def Graph.smul {k n : ℕ} (c : Coeff) (Γ : Graph k n) : Graph k n := ⟨Γ.comps, c * Γ.coeff⟩

/-- A formal sum with every coefficient multiplied by `c`. -/
def Expansion.smul {k : ℕ} (c : Coeff) (E : Expansion k) : Expansion k :=
  E.map fun g => ⟨g.1, g.2.smul c⟩

/-- Weight kinds: the component sits on the atom `x`. -/
def Kind.isWeight : Kind → Bool
  | .weight _ | .light _ | .inv _ | .wD _ _ => true
  | _ => false

/-- Random kinds: the solid edges and all weights. -/
def Kind.isRandom : Kind → Bool
  | .G _ | .weight _ | .light _ | .inv _ | .wD _ _ => true
  | _ => false

/-- Well-formed components: a weight has `y = x`, and only solid edges and weights carry a
`P`/`Q` label ([I, Def 2.6]). -/
def Comp.WF {V : Type*} (c : Comp V) : Prop :=
  (c.kind.isWeight = true → c.y = c.x) ∧ (c.label.isSome = true → c.kind.isRandom = true)

/-- A graph without `P`/`Q` labels. -/
def Graph.LabelFree {k n : ℕ} (Γ : Graph k n) : Prop := ∀ c ∈ Γ.comps, c.label = none

end RBM8D.Graphs
