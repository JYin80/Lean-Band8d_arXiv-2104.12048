import RBM8D.Graph.Syntax
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Molecules and the doubly connected property

Molecules ([I, Def 3.4] = [II, Def 2.10]), the molecular graph ([I, Def 6.4] = [II, Def 2.11]) and the doubly connected property ([I, Def 6.5, Def 7.5] = [II, Def 2.12]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-- The graph on the atoms whose edges are the waved and dotted edges. -/
def Graph.molGraph {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v

/-- Two atoms are in the same molecule ([I, Def 3.4] = [II, Def 2.10]): they are equal, or both
are internal and joined by a path of waved and dotted edges. Every external atom is a molecule
of its own. -/
def Graph.SameMol {k n : ℕ} (Γ : Graph k n) (u v : Atom k n) : Prop :=
  u = v ∨ (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)

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

/-- The graph on the internal atoms whose edges join two atoms of one molecule, or the two ends
of a component with index in `B`. Its connected components are the classes of internal molecules
joined by the edges of `B` in the molecular graph with the external molecules removed. -/
def Graph.net {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => Γ.SameMol (Sum.inr a) (Sum.inr b) ∨
    ∃ i ∈ B, Γ.comps[i].x = Sum.inr a ∧ Γ.comps[i].y = Sum.inr b

/-- The edges `B` contain a spanning tree of the internal molecules ([I, Def 6.5]): any two
internal atoms are joined in `net B`. -/
def Graph.Spans {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) : Prop :=
  (Γ.net B).Preconnected

/-- The doubly connected property ([I, Def 6.5] = [II, Def 2.12], with [I, Def 7.5] and
[II, Def 9.4]): there are disjoint sets of components, a black net of diffusive edges and a blue
net of diffusive, blue solid or ghost edges, each containing a spanning tree of the molecular
graph with the external molecules removed. -/
def Graph.DoublyConnected {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∃ black blue : Finset (Fin Γ.comps.length), Disjoint black blue ∧
    (∀ i ∈ black, Γ.comps[i].kind.isDiffusive = true) ∧
    (∀ i ∈ blue, Γ.comps[i].kind.isDiffusive = true ∨ Γ.comps[i].kind.isBlue = true) ∧
    Γ.Spans black ∧ Γ.Spans blue

section Instances

end Instances

end RBM8D.Graphs
