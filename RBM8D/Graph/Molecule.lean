module

public import RBM8D.MainDefs
public import RBM8D.Graph.Syntax
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
# Molecules and the doubly connected property

Molecules ([I, Def 3.4] = [II, Def 2.10]), the molecular graph ([I, Def 6.4] = [II, Def 2.11]) and the doubly connected property ([I, Def 6.5, Def 7.5] = [II, Def 2.12]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

theorem Graph.sameMol_equivalence {k n : ℕ} (Γ : Graph k n) : Equivalence Γ.SameMol where
  refl _ := Or.inl rfl
  symm := by
    rintro u v (h | ⟨hu, hv, h⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨hv, hu, h.symm⟩
  trans := by
    rintro u v w (rfl | ⟨hu, hv, h⟩) h'
    · exact h'
    · rcases h' with rfl | ⟨_, hw, h'⟩
      · exact Or.inr ⟨hu, hv, h⟩
      · exact Or.inr ⟨hu, hw, h.trans h'⟩

/-- The component with index `i` is an edge of the molecular graph ([I, Def 6.4] =
[II, Def 2.11]): its ends lie in different molecules, and it is a solid edge, a diffusive edge,
a ghost edge, or a dotted edge between an external and an internal atom. Weights, `×`-dotted
edges and all edges inside a molecule are discarded. The molecular graph is a multigraph whose
edges are these indices, joining the molecules of their two ends. -/
def Graph.IsMolEdge {k n : ℕ} (Γ : Graph k n) (i : Fin Γ.comps.length) : Prop :=
  ¬ Γ.SameMol Γ.comps[i].x Γ.comps[i].y ∧
    (Γ.comps[i].kind.isSolid = true ∨ Γ.comps[i].kind.isDiffusive = true ∨
      Γ.comps[i].kind = .ghost ∨
      (Γ.comps[i].kind = .dot ∧ Γ.comps[i].x.isRight ≠ Γ.comps[i].y.isRight))

section Instances

end Instances

end RBM8D.Graphs
