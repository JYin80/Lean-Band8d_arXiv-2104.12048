module

public import RBM8D.Graph.Isolated

@[expose] public section

/-!
# Pre-deterministic and sequentially pre-deterministic graphs

Pivotal and redundant edges ([II, Def 5.5]), pre-deterministic graphs ([II, Def 5.8]) and sequentially pre-deterministic graphs ([II, Def 5.9]), on the molecular multigraph and on atomic graphs.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

variable {V E : Type}

/-! ## Pre-deterministic and sequentially pre-deterministic graphs -/

/-- The edge `e` with its class changed to `none`: the graph with `e` removed. -/
def MGraph.erase [DecidableEq E] (G : MGraph V E) (e : E) : MGraph V E :=
  { G with cls := Function.update G.cls e none }

/-- The blue solid edges in `l` changed into diffusive (`Θ`) edges; the other edges are kept. -/
def MGraph.convert [DecidableEq E] (G : MGraph V E) (l : List E) : MGraph V E :=
  { G with cls := fun e => if e ∈ l ∧ G.cls e = some .plus then some .diff else G.cls e }

/-- The subgraph induced on the set `S` of vertices ([II, Def 5.2]): the vertices of `S`, all
internal, and the edges with both ends in `S`. -/
def MGraph.induce [DecidableEq V] (G : MGraph V E) (S : Finset V) : MGraph V E where
  int := S
  ext := ∅
  ends := G.ends
  cls e := if (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S then G.cls e else none

/-- The end of the edge `e` outside `P` (the second end if the first one lies in `P`). -/
def MGraph.outer [DecidableEq V] (G : MGraph V E) (P : Finset V) (e : E) : V :=
  if (G.ends e).1 ∈ P then (G.ends e).2 else (G.ends e).1

/-- The replacement of [II, Def 5.9 (iii)]: in the subgraph induced on `S`, the subset `P` and
its two external edges `e₁`, `e₂` are removed and one `Θ` edge is added between the outer ends
`M`, `M'` of `e₁` and `e₂`; the new edge carries the index `e₁`. If `M = M'` it is a loop, which
crosses no cut. -/
def MGraph.replace [DecidableEq V] [DecidableEq E] (G : MGraph V E) (S P : Finset V)
    (e₁ e₂ : E) : MGraph V E where
  int := S \ P
  ext := ∅
  ends e := if e = e₁ then (G.outer P e₁, G.outer P e₂) else G.ends e
  cls e := if e = e₁ then some .diff else if e = e₂ then none else (G.induce (S \ P)).cls e

/-- Internal blue solid edges: blue solid edges between two internal vertices. -/
abbrev MGraph.IsIntPlus (G : MGraph V E) (e : E) : Prop :=
  G.cls e = some .plus ∧ (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int

/-- Redundant edges ([II, Def 5.5]): a blue solid edge of a doubly connected graph whose removal
leaves the graph doubly connected. -/
def MGraph.IsRedundant [DecidableEq E] (G : MGraph V E) (e : E) : Prop :=
  G.cls e = some .plus ∧ G.DC ∧ (G.erase e).DC

/-- Pre-deterministic orders ([II, Def 5.8]): a list without repetition of all internal blue
solid edges such that for each `j`, after the first `j` edges are changed into `Θ` edges, the
`j`-th edge is redundant. -/
def MGraph.IsPDOrder [DecidableEq E] (G : MGraph V E) (l : List E) : Prop :=
  l.Nodup ∧ (∀ e, e ∈ l ↔ G.IsIntPlus e) ∧
    ∀ (j : ℕ) (hj : j < l.length), (G.convert (l.take j)).IsRedundant l[j]

/-- Pre-deterministic graphs ([II, Def 5.8]): doubly connected, with a pre-deterministic
order. -/
def MGraph.PreDet [DecidableEq E] (G : MGraph V E) : Prop :=
  G.DC ∧ ∃ l, G.IsPDOrder l

/-- Sequentially pre-deterministic graphs ([II, Def 5.9]): (i) doubly connected; (ii) the
proper isolated subsets form a chain; (iii) the subgraph induced on the minimal isolated subset
is pre-deterministic, and for the set of all internal vertices and every isolated subset `S`,
replacing a maximal isolated subset of `S` and its two external edges by one `Θ` edge in the
subgraph induced on `S` gives a pre-deterministic graph. -/
def MGraph.SPD [DecidableEq V] [DecidableEq E] (G : MGraph V E) : Prop :=
  G.DC ∧ G.IsoChain ∧
    (∀ S, G.IsoOrTop S → (∀ Q, ¬ G.IsProperIso S Q) → (G.induce S).PreDet) ∧
    ∀ S P e₁ e₂, G.IsoOrTop S → G.IsMaximalIso S P → e₁ ≠ e₂ → G.Crosses P e₁ →
      G.Crosses P e₂ → (G.replace S P e₁ e₂).PreDet

/-! ### Changing classes and inducing -/

/-- An edge with both ends in `S` keeps its class in the subgraph induced on `S`. -/
private theorem induce_cls [DecidableEq V] (G : MGraph V E) (S : Finset V) {e : E}
    (h1 : (G.ends e).1 ∈ S) (h2 : (G.ends e).2 ∈ S) : (G.induce S).cls e = G.cls e := by
  simp [MGraph.induce, h1, h2]

/-- Inducing on a set of vertices commutes with changing blue solid edges into `Θ` edges. -/
private theorem induce_convert [DecidableEq V] [DecidableEq E] (G : MGraph V E) (S : Finset V)
    (l : List E) : (G.induce S).convert l = (G.convert l).induce S := by
  unfold MGraph.induce MGraph.convert
  congr 1
  funext e
  by_cases h : (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S <;> simp [h]

/-- Inducing on a set of vertices commutes with removing an edge. -/
private theorem induce_erase [DecidableEq V] [DecidableEq E] (G : MGraph V E) (S : Finset V)
    (e : E) : (G.induce S).erase e = (G.erase e).induce S := by
  unfold MGraph.induce MGraph.erase
  congr 1
  funext x
  by_cases hx : x = e
  · subst hx
    simp
  · by_cases h : (G.ends x).1 ∈ S ∧ (G.ends x).2 ∈ S <;> simp [h, hx]

/-- Inducing a doubly connected graph on all its internal vertices keeps it doubly connected: the
edges of the nets with an external end are dropped, and the edges that cut an internal set have
internal ends. -/
private theorem dc_induce_int [DecidableEq V] {G : MGraph V E} (hG : G.DC) :
    (G.induce G.int).DC := by
  classical
  obtain ⟨black, blue, hd, hbk, hbu, hsk, hsu⟩ := hG
  have hcls : ∀ e, (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int →
      (G.induce G.int).cls e = G.cls e := fun e h1 h2 => induce_cls G G.int h1 h2
  refine ⟨black.filter fun e => (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int,
    blue.filter fun e => (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int,
    hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _), ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨heb, h1, h2⟩ := Finset.mem_filter.1 he
    rw [hcls e h1 h2]
    exact hbk e heb
  · intro e he
    obtain ⟨heb, h1, h2⟩ := Finset.mem_filter.1 he
    rw [hcls e h1 h2]
    exact hbu e heb
  · intro S hS hne hn
    obtain ⟨e, he, h1, h2, h3, h4⟩ := hsk S hS hne hn
    exact ⟨e, Finset.mem_filter.2 ⟨he, h2, h3⟩, by rw [hcls e h2 h3]; exact h1, h2, h3, h4⟩
  · intro S hS hne hn
    obtain ⟨e, he, h1, h2, h3, h4⟩ := hsu S hS hne hn
    exact ⟨e, Finset.mem_filter.2 ⟨he, h2, h3⟩, by rw [hcls e h2 h3]; exact h1, h2, h3, h4⟩

/-- A redundant edge with internal ends stays redundant in the subgraph induced on all internal
vertices. -/
private theorem isRedundant_induce_int [DecidableEq V] [DecidableEq E] {H : MGraph V E} {e : E}
    (h1 : (H.ends e).1 ∈ H.int) (h2 : (H.ends e).2 ∈ H.int) (h : H.IsRedundant e) :
    (H.induce H.int).IsRedundant e := by
  refine ⟨?_, dc_induce_int h.2.1, ?_⟩
  · rw [induce_cls H H.int h1 h2]
    exact h.1
  · rw [induce_erase]
    exact dc_induce_int h.2.2

/-- The subgraph induced on all internal vertices of a pre-deterministic graph is
pre-deterministic, with the same order. -/
private theorem preDet_induce_int [DecidableEq V] [DecidableEq E] {G : MGraph V E}
    (h : G.PreDet) : (G.induce G.int).PreDet := by
  obtain ⟨hdc, l, hnd, hmem, hred⟩ := h
  refine ⟨dc_induce_int hdc, l, hnd, fun e => ?_, fun j hj => ?_⟩
  · rw [hmem e]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by rw [induce_cls G G.int h2 h3]; exact h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by rw [← induce_cls G G.int h2 h3]; exact h1, h2, h3⟩
  · have hmj : G.IsIntPlus l[j] := (hmem _).1 (List.getElem_mem hj)
    rw [induce_convert]
    exact isRedundant_induce_int hmj.2.1 hmj.2.2 (hred j hj)

/-! ### The ends of the replaced edges -/

/-- In a doubly connected graph, the two nets give, for every set `X` of internal vertices other
than `∅` and all of them, a black edge and a blue edge crossing `X`, with internal ends; no edge
is both black and blue, here recorded by a colouring `c`. -/
private theorem dc_color {G : MGraph V E} (hG : G.DC) :
    ∃ c : E → Prop, ∀ X : Finset V, X ⊆ G.int → X.Nonempty → ¬ G.int ⊆ X →
      ∃ b f, c b ∧ ¬ c f ∧ G.Crosses X b ∧ G.Crosses X f ∧
        ((G.ends b).1 ∈ G.int ∧ (G.ends b).2 ∈ G.int) ∧
        ((G.ends f).1 ∈ G.int ∧ (G.ends f).2 ∈ G.int) := by
  obtain ⟨black, blue, hd, hbk, hbu, hsk, hsu⟩ := hG
  refine ⟨(· ∈ black), fun X h1 h2 h3 => ?_⟩
  obtain ⟨b, hb, b1, b2, b3, b4⟩ := hsk X h1 h2 h3
  obtain ⟨f, hf, f1, f2, f3, f4⟩ := hsu X h1 h2 h3
  refine ⟨b, f, hb, Finset.disjoint_right.1 hd hf, ⟨b1, ?_, Or.inl b2, Or.inl b3, b4⟩,
    ⟨f1, ?_, Or.inl f2, Or.inl f3, f4⟩, ⟨b2, b3⟩, ⟨f2, f3⟩⟩
  · rw [hbk b hb]
    simp
  · rcases hbu f hf with h | h | h <;> rw [h] <;> simp

/-- If two edges of a colouring lie among `x`, `y`, one in the colour and one not, then `x` and `y`
have different colours. -/
private theorem color_aux {c : E → Prop} {b f x y : E} (hb : b = x ∨ b = y) (hf : f = x ∨ f = y)
    (cb : c b) (cf : ¬ c f) : (c x ∨ c y) ∧ (¬ c x ∨ ¬ c y) := by
  rcases hb with rfl | rfl <;> rcases hf with rfl | rfl
  · exact absurd cb cf
  · exact ⟨Or.inl cb, Or.inr cf⟩
  · exact ⟨Or.inr cb, Or.inl cf⟩
  · exact absurd cb cf

/-- Three propositions cannot be pairwise different. -/
private theorem triangle_aux {A B C : Prop} (h1 : (A ∨ B) ∧ (¬ A ∨ ¬ B))
    (h2 : (A ∨ C) ∧ (¬ A ∨ ¬ C)) (h3 : (B ∨ C) ∧ (¬ B ∨ ¬ C)) : False := by
  tauto

/-- The end of an edge cutting `P` that lies outside `P` is not in `P`. -/
private theorem outer_not_mem [DecidableEq V] {G : MGraph V E} {P : Finset V} {e : E}
    (h : G.Cut P e) : G.outer P e ∉ P := by
  unfold MGraph.outer
  split_ifs with h1
  · rcases h with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact h2
    · exact absurd h1 h2
  · exact h1

/-- The outer end of an edge is one of its ends. -/
private theorem outer_eq [DecidableEq V] (G : MGraph V E) (P : Finset V) (e : E) :
    G.outer P e = (G.ends e).1 ∨ G.outer P e = (G.ends e).2 := by
  unfold MGraph.outer
  split_ifs <;> simp

/-- An edge that cuts `P ⊆ S` and whose outer end lies outside `S` cuts `S`. -/
private theorem cut_of_outer [DecidableEq V] {G : MGraph V E} {S P : Finset V} {e : E}
    (hPS : P ⊆ S) (h : G.Cut P e) (ho : G.outer P e ∉ S) : G.Cut S e := by
  unfold MGraph.outer at ho
  have h1 : (G.ends e).1 ∈ P → (G.ends e).1 ∈ S := fun a => hPS a
  have h2 : (G.ends e).2 ∈ P → (G.ends e).2 ∈ S := fun a => hPS a
  split_ifs at ho with h3 <;> simp only [MGraph.Cut] at h ⊢ <;> tauto

/-- An edge that cuts `P ⊆ S` and whose outer end lies outside `S` does not cut `S \ P`. -/
private theorem not_cut_sdiff [DecidableEq V] {G : MGraph V E} {S P : Finset V} {e : E}
    (hPS : P ⊆ S) (h : G.Cut P e) (ho : G.outer P e ∉ S) : ¬ G.Cut (S \ P) e := by
  unfold MGraph.outer at ho
  have h1 : (G.ends e).1 ∈ P → (G.ends e).1 ∈ S := fun a => hPS a
  have h2 : (G.ends e).2 ∈ P → (G.ends e).2 ∈ S := fun a => hPS a
  split_ifs at ho with h3 <;> simp only [MGraph.Cut, Finset.mem_sdiff] at h ⊢ <;> tauto

/-- An edge that cuts `S \ P` cuts `P` or `S`. -/
private theorem crosses_sdiff [DecidableEq V] {G : MGraph V E} {S P : Finset V} {x : E}
    (h : G.Crosses (S \ P) x) : G.Crosses P x ∨ G.Crosses S x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have : G.Cut P x ∨ G.Cut S x := by
    simp only [MGraph.Cut, Finset.mem_sdiff] at h5 ⊢
    tauto
  rcases this with h | h
  · exact Or.inl ⟨h1, h2, h3, h4, h⟩
  · exact Or.inr ⟨h1, h2, h3, h4, h⟩

/-- A set that has an edge cutting it is nonempty. -/
private theorem nonempty_of_cut {G : MGraph V E} {P : Finset V} {e : E} (h : G.Cut P e) :
    P.Nonempty := by
  rcases h with ⟨h, -⟩ | ⟨-, h⟩
  exacts [⟨_, h⟩, ⟨_, h⟩]

/-- An edge crossing a proper isolated subset `P` of the set of all internal vertices has
internal ends, so its outer end is internal. -/
private theorem outer_mem_int [DecidableEq V] {G : MGraph V E} (hG : G.DC) {P : Finset V}
    (hP : G.IsIsolated P) (hnot : ¬ G.int ⊆ P) {e : E} (he : G.Crosses P e) :
    G.outer P e ∈ G.int := by
  obtain ⟨c, hc⟩ := dc_color hG
  obtain ⟨hPint, e₁, e₂, hne, hPx⟩ := hP
  obtain ⟨b, f, cb, cf, xb, xf, ib, if_⟩ := hc P hPint (nonempty_of_cut he.2.2.2.2) hnot
  have hb := (hPx b).1 xb
  have hf := (hPx f).1 xf
  have hbf : b ≠ f := fun h => cf (h ▸ cb)
  have hef : e = b ∨ e = f := by
    rcases (hPx e).1 he with h | h <;> rcases hb with h' | h' <;> rcases hf with h'' | h'' <;>
      first | exact Or.inl (h.trans h'.symm) | exact Or.inr (h.trans h''.symm) |
        exact absurd (h'.trans h''.symm) hbf
  have hint : (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int := by
    rcases hef with rfl | rfl
    · exact ib
    · exact if_
  rcases outer_eq G P e with h | h <;> rw [h]
  exacts [hint.1, hint.2]

/-- A proper isolated subset `P` of an isolated subset `S ≠ G.int`: the outer end of an edge
crossing `P` lies in `S`. The three sets `P`, `S` and `S \ P` are each crossed by one black and one
blue edge; an edge crossing `S \ P` crosses `P` or `S` and does not leave `S` through the outer end
of the edge, so the three pairs of crossing edges would be a proper two-colouring of a triangle. -/
private theorem outer_mem_of_iso [DecidableEq V] {G : MGraph V E} (hG : G.DC) {S P : Finset V}
    (hS : G.IsIsolated S) (hSint : S ≠ G.int) (hPS : P ⊂ S) (hP : G.IsIsolated P) {e : E}
    (he : G.Crosses P e) : G.outer P e ∈ S := by
  by_contra hout
  obtain ⟨c, hc⟩ := dc_color hG
  obtain ⟨hPint, e₁, e₂, hne, hPx⟩ := hP
  obtain ⟨hSsub, s₁, s₂, hne', hSx⟩ := hS
  obtain ⟨e', hee', hPx⟩ : ∃ e', e ≠ e' ∧ ∀ x, G.Crosses P x ↔ x = e ∨ x = e' := by
    rcases (hPx e).1 he with rfl | rfl
    · exact ⟨e₂, hne, hPx⟩
    · exact ⟨e₁, hne.symm, fun x => (hPx x).trans or_comm⟩
  have heS : G.Crosses S e :=
    ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, cut_of_outer hPS.1 he.2.2.2.2 hout⟩
  obtain ⟨g, heg, hSx⟩ : ∃ g, e ≠ g ∧ ∀ x, G.Crosses S x ↔ x = e ∨ x = g := by
    rcases (hSx e).1 heS with rfl | rfl
    · exact ⟨s₂, hne', hSx⟩
    · exact ⟨s₁, hne'.symm, fun x => (hSx x).trans or_comm⟩
  obtain ⟨s, hsS, hsP⟩ := Finset.exists_of_ssubset hPS
  have hPne : P.Nonempty := nonempty_of_cut he.2.2.2.2
  have hPnot : ¬ G.int ⊆ P := fun h => hsP (h (hSsub hsS))
  have hSnot : ¬ G.int ⊆ S := fun h => hSint (Finset.Subset.antisymm hSsub h)
  have hTsub : S \ P ⊆ G.int := Finset.sdiff_subset.trans hSsub
  have hTne : (S \ P).Nonempty := ⟨s, Finset.mem_sdiff.2 ⟨hsS, hsP⟩⟩
  have hTnot : ¬ G.int ⊆ S \ P := fun h => by
    obtain ⟨p, hp⟩ := hPne
    exact (Finset.mem_sdiff.1 (h (hPint hp))).2 hp
  obtain ⟨bP, fP, cbP, cfP, xbP, xfP, -, -⟩ := hc P hPint hPne hPnot
  obtain ⟨bS, fS, cbS, cfS, xbS, xfS, -, -⟩ := hc S hSsub ⟨s, hsS⟩ hSnot
  obtain ⟨bT, fT, cbT, cfT, xbT, xfT, -, -⟩ := hc (S \ P) hTsub hTne hTnot
  have hnT := not_cut_sdiff hPS.1 he.2.2.2.2 hout
  have hTP : ∀ x, G.Crosses (S \ P) x → x = e' ∨ x = g := by
    intro x hx
    have hxe : x ≠ e := fun h => hnT (h ▸ hx.2.2.2.2)
    rcases crosses_sdiff hx with h | h
    · rcases (hPx x).1 h with h | h
      · exact absurd h hxe
      · exact Or.inl h
    · rcases (hSx x).1 h with h | h
      · exact absurd h hxe
      · exact Or.inr h
  have h1 := color_aux ((hPx _).1 xbP) ((hPx _).1 xfP) cbP cfP
  have h2 := color_aux ((hSx _).1 xbS) ((hSx _).1 xfS) cbS cfS
  have h3 := color_aux (hTP _ xbT) (hTP _ xfT) cbT cfT
  exact triangle_aux h1 h2 h3

/-! ### Theorems -/

/-- Changing blue solid edges into `Θ` edges keeps the doubly connected property ([II, §5.3]):
the nets are unchanged, because no edge is removed and the class `plus` becomes `diff`. -/
theorem MGraph.DC_convert :
  ∀ (V E : Type) [DecidableEq E] (G : MGraph V E) (l : List E), G.DC → (G.convert l).DC := by
  intro V E _ G l ⟨black, blue, hd, hbk, hbu, hsk, hsu⟩
  have hne : ∀ e, G.cls e ≠ none → (G.convert l).cls e ≠ none := by
    intro e h
    change (if e ∈ l ∧ G.cls e = some .plus then some MClass.diff else G.cls e) ≠ none
    split_ifs <;> simp [h]
  refine ⟨black, blue, hd, fun e he => ?_, fun e he => ?_, fun S h1 h2 h3 => ?_,
    fun S h1 h2 h3 => ?_⟩
  · change (if e ∈ l ∧ G.cls e = some .plus then some MClass.diff else G.cls e) = some .diff
    rw [hbk e he]
    simp
  · change (if e ∈ l ∧ G.cls e = some .plus then some MClass.diff else G.cls e) = some .diff ∨
      (if e ∈ l ∧ G.cls e = some .plus then some MClass.diff else G.cls e) = some .plus ∨
      (if e ∈ l ∧ G.cls e = some .plus then some MClass.diff else G.cls e) = some .ghost
    by_cases hh : e ∈ l ∧ G.cls e = some .plus
    · simp [hh]
    · simpa [hh] using hbu e he
  · obtain ⟨e, he, h1', h2', h3', h4'⟩ := hsk S h1 h2 h3
    exact ⟨e, he, hne e h1', h2', h3', h4'⟩
  · obtain ⟨e, he, h1', h2', h3', h4'⟩ := hsu S h1 h2 h3
    exact ⟨e, he, hne e h1', h2', h3', h4'⟩

/-- The replacement of [II, Def 5.9 (iii)] is well defined: in a doubly connected graph, the
two external edges of a proper isolated subset `P` of `S` (the set of all internal vertices or
an isolated subset) end in `S \ P`. -/
theorem MGraph.replace_ends :
  ∀ (V E : Type) [DecidableEq V] (G : MGraph V E), G.DC → ∀ S P e, G.IsoOrTop S →
    G.IsProperIso S P → G.Crosses P e → G.outer P e ∈ S \ P := by
  intro V E _ G hG S P e hS hPS he
  obtain ⟨hP, hPsub⟩ := hPS
  refine Finset.mem_sdiff.2 ⟨?_, outer_not_mem he.2.2.2.2⟩
  by_cases hSint : S = G.int
  · subst hSint
    exact outer_mem_int hG hP (Finset.not_subset.2 (Finset.exists_of_ssubset hPsub)) he
  · rcases hS with h | h
    · exact absurd h hSint
    · exact outer_mem_of_iso hG h hSint hPsub hP he

/-- A pre-deterministic graph without proper isolated subset is sequentially pre-deterministic
([II, Def 5.9], [II, §5.4]): the chain and replacement conditions are vacuous, and the induced
subgraph on all internal vertices is pre-deterministic. -/
theorem MGraph.SPD_of_preDet :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E), G.PreDet →
    (∀ Q, ¬ G.IsProperIso G.int Q) → G.SPD := by
  intro V E _ _ G hpd hno
  have htop : ∀ S, G.IsoOrTop S → S = G.int := by
    intro S hS
    rcases hS with h | h
    · exact h
    · by_contra hne
      exact hno S ⟨h, Finset.ssubset_iff_subset_ne.2 ⟨h.1, hne⟩⟩
  refine ⟨hpd.1, fun P Q hP _ => absurd hP (hno P), fun S hS _ => ?_, fun S P _ _ hS hmax => ?_⟩
  · rw [htop S hS]
    exact preDet_induce_int hpd
  · rw [htop S hS] at hmax
    exact absurd hmax.1 (hno P)

section Instances

end Instances

end RBM8D.Graphs
