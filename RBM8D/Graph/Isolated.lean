import RBM8D.Graph.Molecule

/-!
# The molecular multigraph and isolated subsets

The molecular graph of [II, Def 2.11] as an abstract multigraph, the doubly connected property on it ([II, Def 2.12]), isolated subsets and subgraphs, minimal and maximal isolated subsets ([II, Defs 5.2, 5.4]), and [II, Claim 5.1].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The molecular multigraph and isolated subsets -/

/-- The classes of the edges of the molecular graph ([II, Def 2.11]): diffusive edges (`Θ`
edges, `Θ_err` edges, diffusive auxiliary edges), blue solid edges `G`, ghost edges
([II, Def 9.4]), red solid edges `Ḡ`, and dotted edges between an external and an internal
molecule. -/
inductive MClass
  | diff
  | plus
  | ghost
  | minus
  | dot
  deriving DecidableEq, Repr

/-- The class of a component kind as an edge of the molecular graph; `none` for the kinds that
are never edges of the molecular graph (weights, waved edges, `×`-dotted edges, non-diffusive
auxiliary edges). -/
def Kind.mclass : Kind → Option MClass
  | .G .plus => some .plus
  | .G .minus => some .minus
  | .theta _ => some .diff
  | .thetaErr _ _ => some .diff
  | .aux _ _ b => if b then some .diff else none
  | .ghost => some .ghost
  | .dot => some .dot
  | _ => none

/-- A molecular multigraph on the vertex type `V` (molecules) with edge type `E`: the internal
and the external vertices, the two ends of each edge, and the class of each edge; an edge of
class `none` is absent. -/
structure MGraph (V E : Type) where
  int : Finset V
  ext : Finset V
  ends : E → V × V
  cls : E → Option MClass

variable {V E : Type}

/-- The vertices: internal or external. -/
abbrev MGraph.IsVtx (G : MGraph V E) (v : V) : Prop := v ∈ G.int ∨ v ∈ G.ext

/-- The edge `e` has exactly one end in `S`. -/
abbrev MGraph.Cut (G : MGraph V E) (S : Finset V) (e : E) : Prop :=
  ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∉ S) ∨ ((G.ends e).1 ∉ S ∧ (G.ends e).2 ∈ S)

/-- The edges `B` contain a spanning tree of the internal vertices, in cut form: every set `S`
of internal vertices other than `∅` and all of them is left by an edge of `B` between two
internal vertices. -/
abbrev MGraph.Spans (G : MGraph V E) (B : Finset E) : Prop :=
  ∀ S : Finset V, S ⊆ G.int → S.Nonempty → ¬ G.int ⊆ S →
    ∃ e ∈ B, G.cls e ≠ none ∧ (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧ G.Cut S e

/-- The doubly connected property ([II, Def 2.12], with [II, Def 9.4]) on the molecular
multigraph: disjoint black and blue nets, the black net of diffusive edges and the blue net of
diffusive, blue solid or ghost edges, each containing a spanning tree of the internal
vertices. -/
def MGraph.DC (G : MGraph V E) : Prop :=
  ∃ black blue : Finset E, Disjoint black blue ∧
    (∀ e ∈ black, G.cls e = some .diff) ∧
    (∀ e ∈ blue, G.cls e = some .diff ∨ G.cls e = some .plus ∨ G.cls e = some .ghost) ∧
    G.Spans black ∧ G.Spans blue

/-- The edge `e` joins `S` to its complement in the molecular graph without red solid edges
([II, §5]): it is present, not a red solid edge, both ends are vertices and exactly one end
lies in `S`. -/
abbrev MGraph.Crosses (G : MGraph V E) (S : Finset V) (e : E) : Prop :=
  G.cls e ≠ none ∧ G.cls e ≠ some .minus ∧ G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2 ∧
    G.Cut S e

/-- Isolated subsets of molecules ([II, Def 5.2]): a set of internal vertices joined to its
complement (the other internal and all external vertices) by exactly two edges of the molecular
graph without red solid edges. -/
def MGraph.IsIsolated (G : MGraph V E) (P : Finset V) : Prop :=
  P ⊆ G.int ∧ ∃ e₁ e₂ : E, e₁ ≠ e₂ ∧ ∀ e, G.Crosses P e ↔ e = e₁ ∨ e = e₂

/-- A proper isolated subset `P` of `S` ([II, Def 5.2]): `P` is isolated and `P ⊂ S`. A proper
isolated subset without a named superset is one of `S = G.int`. -/
def MGraph.IsProperIso (G : MGraph V E) (S P : Finset V) : Prop :=
  G.IsIsolated P ∧ P ⊂ S

/-- Maximal isolated subsets of `S` ([II, Def 5.4 (ii)]): a proper isolated subset of `S` that
is not a proper subset of another proper isolated subset of `S`. -/
def MGraph.IsMaximalIso (G : MGraph V E) (S P : Finset V) : Prop :=
  G.IsProperIso S P ∧ ∀ Q, G.IsProperIso S Q → ¬ P ⊂ Q

/-- Any two proper isolated subsets are comparable ([II, Def 5.9 (ii)]). -/
def MGraph.IsoChain (G : MGraph V E) : Prop :=
  ∀ P Q, G.IsProperIso G.int P → G.IsProperIso G.int Q → P ⊆ Q ∨ Q ⊆ P

/-- The set `S` is the set of all internal vertices or an isolated subset. -/
def MGraph.IsoOrTop (G : MGraph V E) (S : Finset V) : Prop :=
  S = G.int ∨ G.IsIsolated S

open Classical in
/-- The minimal isolated subset (MIS, [II, Def 5.4 (i)]): the intersection of all proper
isolated subsets with the internal vertices; the set of all internal vertices if there is no
proper isolated subset. -/
def MGraph.MIS (G : MGraph V E) : Finset V :=
  G.int.filter fun v => ∀ P, G.IsProperIso G.int P → v ∈ P

/-! ### Theorems -/

/-- [II, Claim 5.1] on the molecular multigraph: in a doubly connected multigraph, every set of
internal vertices other than `∅` and all of them is crossed by a diffusive edge and by a second
edge that is diffusive, blue solid or a ghost edge, none of them a red solid edge. -/
theorem MGraph.claim51 :
  ∀ (V E : Type) (G : MGraph V E), G.DC → ∀ S : Finset V, S ⊆ G.int → S.Nonempty →
    ¬ G.int ⊆ S → ∃ i j, i ≠ j ∧ G.Crosses S i ∧ G.Crosses S j ∧ G.cls i = some .diff ∧
      (G.cls j = some .diff ∨ G.cls j = some .plus ∨ G.cls j = some .ghost) := by
  intro V E G ⟨black, blue, hd, hbk, hbu, hsk, hsu⟩ S hS hne hn
  obtain ⟨e, he, h1, h2, h3, h4⟩ := hsk S hS hne hn
  obtain ⟨f, hf, g1, g2, g3, g4⟩ := hsu S hS hne hn
  have hef : e ≠ f := fun h => Finset.disjoint_left.1 hd he (h ▸ hf)
  refine ⟨e, f, hef, ⟨h1, ?_, Or.inl h2, Or.inl h3, h4⟩, ⟨g1, ?_, Or.inl g2, Or.inl g3, g4⟩,
    hbk e he, hbu f hf⟩
  · rw [hbk e he]
    simp
  · rcases hbu f hf with h | h | h <;> rw [h] <;> simp

section Instances

end Instances

end RBM8D.Graphs
