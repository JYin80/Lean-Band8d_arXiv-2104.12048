module

public import RBM8D.Graph.MolOps

@[expose] public section

/-!
# Merging molecules

[II, Claim A.4], [II, Lemma 5.10 (A)], [II, Lemma 5.11].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

variable {V E : Type}

/-! ## Connectivity of a set of edges -/

/-- The vertices `u`, `v` are internal and joined by a present edge of `B`. -/
private def MGraph.Adj (X : MGraph V E) (B : Finset E) (u v : V) : Prop :=
  ∃ e ∈ B, X.cls e ≠ none ∧ u ∈ X.int ∧ v ∈ X.int ∧ (X.ends e = (u, v) ∨ X.ends e = (v, u))

/-- Adjacency by a present edge of `B`, or the link between `p` and `q`. -/
private def MGraph.Lk (X : MGraph V E) (B : Finset E) (p q u v : V) : Prop :=
  X.Adj B u v ∨ (u = p ∧ v = q) ∨ (u = q ∧ v = p)

/-- Connectivity by present edges of `B` and the link between `p` and `q`. -/
private abbrev MGraph.Rch (X : MGraph V E) (B : Finset E) (p q : V) : V → V → Prop :=
  Relation.ReflTransGen (X.Lk B p q)

/-- Adjacency is symmetric. -/
private theorem MGraph.Adj.symm {X : MGraph V E} {B : Finset E} {u v : V} (h : X.Adj B u v) :
    X.Adj B v u := by
  obtain ⟨e, he, hc, hu, hv, h⟩ := h
  exact ⟨e, he, hc, hv, hu, h.symm⟩

/-- Adjacency with the link is symmetric. -/
private theorem MGraph.Lk.symm {X : MGraph V E} {B : Finset E} {p q u v : V}
    (h : X.Lk B p q u v) : X.Lk B p q v u := by
  rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- Connectivity is symmetric. -/
private theorem rch_symm {X : MGraph V E} {B : Finset E} {p q u v : V} (h : X.Rch B p q u v) :
    X.Rch B p q v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.head hs.symm ih

/-- Connectivity is transitive. -/
private theorem rch_trans {X : MGraph V E} {B : Finset E} {p q u v w : V} (h : X.Rch B p q u v)
    (h' : X.Rch B p q v w) : X.Rch B p q u w :=
  Relation.ReflTransGen.trans h h'

/-- A present edge of `B` with internal ends joins its ends. -/
private theorem rch_edge {X : MGraph V E} {B : Finset E} {p q : V} {e : E} (he : e ∈ B)
    (hc : X.cls e ≠ none) (h1 : (X.ends e).1 ∈ X.int) (h2 : (X.ends e).2 ∈ X.int) :
    X.Rch B p q (X.ends e).1 (X.ends e).2 :=
  Relation.ReflTransGen.single (Or.inl ⟨e, he, hc, h1, h2, Or.inl rfl⟩)

/-- The link joins `p` and `q`. -/
private theorem rch_link {X : MGraph V E} {B : Finset E} {p q : V} : X.Rch B p q p q :=
  Relation.ReflTransGen.single (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- Lifting connectivity along a map of vertices. -/
private theorem rch_lift {X Y : MGraph V E} {B B' : Finset E} {p q p' q' : V} (g : V → V)
    (hs : ∀ a b, X.Lk B p q a b → Y.Rch B' p' q' (g a) (g b)) {u v : V}
    (h : X.Rch B p q u v) : Y.Rch B' p' q' (g u) (g v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs' ih => exact rch_trans ih (hs _ _ hs')

/-- A spanning set of edges connects any two internal vertices. -/
private theorem rch_of_spans {X : MGraph V E} {B : Finset E} (p q : V)
    (h : X.Spans B) {u v : V} (hu : u ∈ X.int) (hv : v ∈ X.int) : X.Rch B p q u v := by
  classical
  by_contra hn
  obtain ⟨e, he, hc, h1, h2, hcut⟩ := h (X.int.filter fun w => X.Rch B p q u w)
    (Finset.filter_subset _ _) ⟨u, Finset.mem_filter.2 ⟨hu, Relation.ReflTransGen.refl⟩⟩
    (fun hs => hn (Finset.mem_filter.1 (hs hv)).2)
  have hr := rch_edge (p := p) (q := q) he hc h1 h2
  simp only [MGraph.Cut, Finset.mem_filter, h1, h2, true_and] at hcut
  rcases hcut with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hb (rch_trans ha hr)
  · exact ha (rch_trans hb (rch_symm hr))

/-- A set of edges that connects any two internal vertices, without the link, spans. -/
private theorem spans_of_rch {X : MGraph V E} {B : Finset E} (p : V)
    (h : ∀ u ∈ X.int, ∀ v ∈ X.int, X.Rch B p p u v) : X.Spans B := by
  intro S hS ⟨s, hs⟩ hn
  obtain ⟨t, ht, hts⟩ := Finset.not_subset.1 hn
  have key : ∀ w, X.Rch B p p s w → w ∈ S ∨ ∃ e ∈ B, X.cls e ≠ none ∧ (X.ends e).1 ∈ X.int ∧
      (X.ends e).2 ∈ X.int ∧ X.Cut S e := by
    intro w hw
    induction hw with
    | refl => exact Or.inl hs
    | tail _ hst ih =>
      rcases ih with ha | h
      · rename_i a b _
        rcases hst with ⟨e, he, hc, hai, hbi, hends⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · by_cases hb : b ∈ S
          · exact Or.inl hb
          · refine Or.inr ⟨e, he, hc, ?_, ?_, ?_⟩ <;>
              rcases hends with hends | hends <;> simp only [MGraph.Cut, hends] <;> tauto
        · exact Or.inl ha
        · exact Or.inl ha
      · exact Or.inr h
  rcases key t (h s (hS hs) t ht) with h' | h'
  · exact absurd h' hts
  · exact h'

/-- Spanning in a graph with mapped vertices: if every internal vertex is connected to `p` with
the link between `p` and `q`, and `f p = f q`, the set spans the graph with the vertices mapped
by `f`. -/
private theorem spans_mapV [DecidableEq V] {X : MGraph V E} {B : Finset E} {p q : V} (f : V → V)
    (hpq : f p = f q) (h : ∀ u ∈ X.int, X.Rch B p q u p) : (X.mapV f).Spans B := by
  refine spans_of_rch (f p) fun a ha b hb => ?_
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
  have step : ∀ x y, X.Lk B p q x y → (X.mapV f).Rch B (f p) (f p) (f x) (f y) := by
    intro x y hxy
    rcases hxy with ⟨e, he, hc, hx, hy, hends⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine Relation.ReflTransGen.single (Or.inl ⟨e, he, hc, Finset.mem_image_of_mem _ hx,
        Finset.mem_image_of_mem _ hy, ?_⟩)
      rcases hends with hends | hends
      · exact Or.inl (by simp [MGraph.mapV, hends])
      · exact Or.inr (by simp [MGraph.mapV, hends])
    · rw [hpq]
    · rw [hpq]
  exact rch_trans (rch_lift f step (h u hu)) (rch_symm (rch_lift f step (h v hv)))

/-- A present edge of `B` joins its ends, given in either order. -/
private theorem rch_edge' {X : MGraph V E} {B : Finset E} {p q a b : V} {e : E} (he : e ∈ B)
    (hc : X.cls e ≠ none) (hends : X.ends e = (a, b) ∨ X.ends e = (b, a)) (ha : a ∈ X.int)
    (hb : b ∈ X.int) : X.Rch B p q a b :=
  Relation.ReflTransGen.single (Or.inl ⟨e, he, hc, ha, hb, hends⟩)

/-- Simulation: if every adjacency of `X` by an edge of `B` is a connection in `Y`, every
connection of `X` without the link is a connection in `Y`. -/
private theorem rch_sim {X Y : MGraph V E} {B B' : Finset E} {p q : V} (r : V)
    (hs : ∀ e ∈ B, X.cls e ≠ none → (X.ends e).1 ∈ X.int → (X.ends e).2 ∈ X.int →
      Y.Rch B' p q (X.ends e).1 (X.ends e).2) {u v : V} (h : X.Rch B r r u v) :
    Y.Rch B' p q u v := by
  have := rch_lift (Y := Y) (B' := B') (p' := p) (q' := q) id (fun a b hab => by
    rcases hab with ⟨e, he, hc, ha, hb, hends⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hends with hends | hends
      · have := hs e he hc (by rw [hends]; exact ha) (by rw [hends]; exact hb)
        rw [hends] at this
        exact this
      · have := hs e he hc (by rw [hends]; exact hb) (by rw [hends]; exact ha)
        rw [hends] at this
        exact rch_symm this
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.refl) h
  exact this

/-- Spanning from nets: a set of edges that connects every internal vertex to `r` spans. -/
private theorem spans_of_rch' {X : MGraph V E} {B : Finset E} (r : V)
    (h : ∀ u ∈ X.int, X.Rch B r r u r) : X.Spans B :=
  spans_of_rch r fun u hu v hv => rch_trans (h u hu) (rch_symm (h v hv))

/-! ## The doubly connected property under operations -/

/-- Mapping the vertices keeps a spanning set spanning. -/
private theorem spans_mapV' [DecidableEq V] {X : MGraph V E} {B : Finset E} (f : V → V)
    (h : X.Spans B) : (X.mapV f).Spans B := by
  intro S hS hne hn
  obtain ⟨r, hr⟩ := hne
  refine spans_of_rch r (fun a ha b hb => ?_) S hS ⟨r, hr⟩ hn
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
  have step : ∀ x y, X.Lk B u u x y → (X.mapV f).Rch B r r (f x) (f y) := by
    intro x y hxy
    rcases hxy with ⟨e, he, hc, hx, hy, hends⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine rch_edge' he hc ?_ (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy)
      rcases hends with hends | hends
      · exact Or.inl (by simp [MGraph.mapV, hends])
      · exact Or.inr (by simp [MGraph.mapV, hends])
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.refl
  exact rch_lift f step (rch_of_spans u u h hu hv)

/-- Mapping the vertices keeps the doubly connected property. -/
private theorem dc_mapV [DecidableEq V] {X : MGraph V E} (f : V → V) (h : X.DC) :
    (X.mapV f).DC := by
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := h
  exact ⟨K, L, hd, hK, hL, spans_mapV' f hsK, spans_mapV' f hsL⟩

/-- The doubly connected property of a graph with mapped vertices from two nets whose edges
connect every internal vertex to `p`, with the link between `p` and `q`, `f p = f q`. -/
private theorem dc_mapV_of [DecidableEq V] {X : MGraph V E} {p q : V} (f : V → V)
    (hpq : f p = f q) (K L : Finset E) (hd : Disjoint K L) (hK : ∀ e ∈ K, X.cls e = some .diff)
    (hL : ∀ e ∈ L, X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost)
    (hsK : ∀ u ∈ X.int, X.Rch K p q u p) (hsL : ∀ u ∈ X.int, X.Rch L p q u p) :
    (X.mapV f).DC :=
  ⟨K, L, hd, hK, hL, spans_mapV f hpq hsK, spans_mapV f hpq hsL⟩

/-- Removing an edge from a graph: a doubly connected graph with the edge removed gives a doubly
connected graph. -/
private theorem dc_of_erase [DecidableEq E] {X : MGraph V E} {x : E} (h : (X.erase x).DC) :
    X.DC := by
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := h
  have hcls : ∀ e, (X.erase x).cls e ≠ none → X.cls e = (X.erase x).cls e := by
    intro e he
    by_cases hx : e = x
    · subst hx; simp [MGraph.erase] at he
    · simp [MGraph.erase, hx]
  refine ⟨K, L, hd, fun e he => ?_, fun e he => ?_, fun S h1 h2 h3 => ?_, fun S h1 h2 h3 => ?_⟩
  · rw [hcls e (by rw [hK e he]; simp)]; exact hK e he
  · rw [hcls e (by rcases hL e he with h | h | h <;> rw [h] <;> simp)]; exact hL e he
  · obtain ⟨e, he, hc, h4⟩ := hsK S h1 h2 h3
    exact ⟨e, he, by rw [hcls e hc]; exact hc, h4⟩
  · obtain ⟨e, he, hc, h4⟩ := hsL S h1 h2 h3
    exact ⟨e, he, by rw [hcls e hc]; exact hc, h4⟩

/-- Changing classes commutes with mapping the vertices. -/
private theorem mapV_convert [DecidableEq V] [DecidableEq E] (X : MGraph V E) (f : V → V)
    (l : List E) : (X.mapV f).convert l = (X.convert l).mapV f := rfl

/-- Removing an edge commutes with mapping the vertices. -/
private theorem mapV_erase [DecidableEq V] [DecidableEq E] (X : MGraph V E) (f : V → V) (x : E) :
    (X.mapV f).erase x = (X.erase x).mapV f := rfl

/-- Redundancy in a graph with mapped vertices from the doubly connected property after the
edge is removed. -/
private theorem red_mapV [DecidableEq V] [DecidableEq E] {X : MGraph V E} (f : V → V) {x : E}
    (hx : X.cls x = some .plus) (h : ((X.erase x).mapV f).DC) : (X.mapV f).IsRedundant x := by
  refine ⟨hx, dc_of_erase (x := x) ?_, ?_⟩ <;> rw [mapV_erase] <;> exact h

/-- Changing two lists of edges in turn is changing their concatenation. -/
private theorem convert_convert [DecidableEq E] (X : MGraph V E) (l₁ l₂ : List E) :
    (X.convert l₁).convert l₂ = X.convert (l₁ ++ l₂) := by
  unfold MGraph.convert
  congr 1
  funext e
  by_cases h1 : e ∈ l₁ <;> by_cases h2 : e ∈ l₂ <;> by_cases hp : X.cls e = some .plus <;>
    simp [h1, h2, hp]

/-- Changing no edge. -/
private theorem convert_nil [DecidableEq E] (X : MGraph V E) : X.convert [] = X := by
  unfold MGraph.convert
  simp

/-- The redundancy steps of a list of edges: after the edges before it are changed into `Θ`
edges, each edge is redundant. -/
private def Steps [DecidableEq E] (X : MGraph V E) (l : List E) : Prop :=
  ∀ (t : ℕ) (ht : t < l.length), (X.convert (l.take t)).IsRedundant l[t]

/-- The redundancy steps of a concatenation. -/
private theorem steps_append [DecidableEq E] {X : MGraph V E} {l₁ l₂ : List E}
    (h₁ : Steps X l₁) (h₂ : Steps (X.convert l₁) l₂) : Steps X (l₁ ++ l₂) := by
  intro t ht
  by_cases hlt : t < l₁.length
  · rw [List.take_append_of_le_length hlt.le, List.getElem_append_left hlt]
    exact h₁ t hlt
  · rw [not_lt] at hlt
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hlt
    have hs : s < l₂.length := by simp at ht; omega
    have := h₂ s hs
    rw [convert_convert] at this
    rw [List.take_length_add_append, List.getElem_append_right (by omega)]
    simpa using this

/-- A set of edges containing a spanning set spans. -/
private theorem spans_mono' {X : MGraph V E} {B B' : Finset E} (h : X.Spans B) (hs : B ⊆ B') :
    X.Spans B' := by
  intro S h1 h2 h3
  obtain ⟨e, he, h4⟩ := h S h1 h2 h3
  exact ⟨e, hs he, h4⟩

/-- A connection by a set of edges either avoids the edge `x`, or reaches an end of `x` without
it. -/
private theorem rch_split [DecidableEq E] {H : MGraph V E} {B : Finset E} {r u v : V} (x : E)
    (h : H.Rch B r r u v) : H.Rch (B.erase x) r r u v ∨ H.Rch (B.erase x) r r u (H.ends x).1 ∨
      H.Rch (B.erase x) r r u (H.ends x).2 := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail _ hst ih =>
    rename_i a c _
    rcases ih with ih | ih | ih
    · rcases hst with ⟨e, he, hc, ha, hc', hends⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · by_cases hex : e = x
        · subst hex
          rcases hends with hends | hends
          · exact Or.inr (Or.inl (by rw [hends]; exact ih))
          · exact Or.inr (Or.inr (by rw [hends]; exact ih))
        · exact Or.inl (rch_trans ih (rch_edge' (Finset.mem_erase.2 ⟨hex, he⟩) hc hends ha hc'))
      · exact Or.inl ih
      · exact Or.inl ih
    · exact Or.inr (Or.inl ih)
    · exact Or.inr (Or.inr ih)

/-! ## [II, Claim A.4] -/

/-- The four entries of a list without repetition are pairwise different. -/
private theorem mm_nodup4 {α : Type} {a b c d : α} (h : [a, b, c, d].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2, h.2.2⟩

/-- The ends and classes of the edges of `G.twoSplit N b₀ b₂ b b₄`. -/
private theorem ts_facts [DecidableEq V] [DecidableEq E] (G : MGraph V E) (N : V)
    {b₀ b₂ b b₄ : E} (hnd : [b₀, b₂, b, b₄].Nodup) :
    (G.twoSplit N b₀ b₂ b b₄).int = insert N G.int ∧
    (G.twoSplit N b₀ b₂ b b₄).ends b₀ = ((G.ends b₀).1, N) ∧
    (G.twoSplit N b₀ b₂ b b₄).ends b₂ = (N, (G.ends b₀).2) ∧
    (G.twoSplit N b₀ b₂ b b₄).ends b = ((G.ends b).1, N) ∧
    (G.twoSplit N b₀ b₂ b b₄).ends b₄ = (N, (G.ends b).2) ∧
    (∀ e, e ≠ b₀ → e ≠ b₂ → e ≠ b → e ≠ b₄ → (G.twoSplit N b₀ b₂ b b₄).ends e = G.ends e) ∧
    (G.twoSplit N b₀ b₂ b b₄).cls b₂ = G.cls b₀ ∧
    (G.twoSplit N b₀ b₂ b b₄).cls b₄ = G.cls b ∧
    (∀ e, e ≠ b₂ → e ≠ b₄ → (G.twoSplit N b₀ b₂ b b₄).cls e = G.cls e) := by
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := mm_nodup4 hnd
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h0b, h04, h0b.symm, h2b.symm]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h02.symm, h2b, h24, h0b.symm, h2b.symm]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h0b.symm, h2b.symm]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h0b.symm, h2b.symm, hb4.symm]
  · intro e e0 e2 eb e4
    simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, e0, e2, eb, e4]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h24]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h2b.symm]
  · intro e e2 e4
    simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, e2, e4]

/-- Simulation in a graph with edges replaced by paths through `N`: a connection of `H` by edges
of `B` is a connection of `Y` by edges of `B'`, if every edge of `B` other than `b₀`, `b` is an
edge of `B'` with the same ends, and the ends of `b₀` and of `b` are connected in `Y`. -/
private theorem ts_rch {H Y : MGraph V E} {N : V} {b₀ b : E} {B B' : Finset E}
    (hint : H.int ⊆ Y.int)
    (hsame : ∀ e ∈ B, H.cls e ≠ none → e ≠ b₀ → e ≠ b →
      Y.ends e = H.ends e ∧ Y.cls e ≠ none ∧ e ∈ B')
    (hb₀ : b₀ ∈ B → H.cls b₀ ≠ none → Y.Rch B' N N (H.ends b₀).1 (H.ends b₀).2)
    (hb : b ∈ B → H.cls b ≠ none → Y.Rch B' N N (H.ends b).1 (H.ends b).2)
    {u v : V} (h : H.Rch B N N u v) : Y.Rch B' N N u v := by
  refine rch_sim N (fun e he hc h1 h2 => ?_) h
  by_cases e0 : e = b₀
  · subst e0; exact hb₀ he hc
  by_cases eb : e = b
  · subst eb; exact hb he hc
  obtain ⟨hends, hc', hB'⟩ := hsame e he hc e0 eb
  rw [← hends]
  exact rch_edge hB' hc' (by rw [hends]; exact hint h1) (by rw [hends]; exact hint h2)

/-- Spanning in a graph with edges replaced by paths through a new vertex `N`. -/
private theorem ts_spans [DecidableEq V] {H Y : MGraph V E} {N : V} {b₀ b : E} {B B' : Finset E}
    (hB : H.Spans B) (hint : Y.int = insert N H.int)
    (hsame : ∀ e ∈ B, H.cls e ≠ none → e ≠ b₀ → e ≠ b →
      Y.ends e = H.ends e ∧ Y.cls e ≠ none ∧ e ∈ B')
    (hb₀ : b₀ ∈ B → H.cls b₀ ≠ none → Y.Rch B' N N (H.ends b₀).1 (H.ends b₀).2)
    (hb : b ∈ B → H.cls b ≠ none → Y.Rch B' N N (H.ends b).1 (H.ends b).2)
    (hN : ∃ a ∈ H.int, Y.Rch B' N N N a) : Y.Spans B' := by
  have hsub : H.int ⊆ Y.int := by rw [hint]; exact Finset.subset_insert _ _
  obtain ⟨a, ha, hNa⟩ := hN
  refine spans_of_rch' N fun u hu => ?_
  rw [hint, Finset.mem_insert] at hu
  rcases hu with rfl | hu
  · exact Relation.ReflTransGen.refl
  · exact rch_trans (ts_rch hsub hsame hb₀ hb (rch_of_spans N N hB hu ha)) (rch_symm hNa)

/-- A path `x`–`N`–`y` of two present edges of `B'` in `Y`. -/
private theorem rch_two {Y : MGraph V E} {B' : Finset E} {N x y : V} {e₁ e₂ : E} (h₁ : e₁ ∈ B')
    (h₂ : e₂ ∈ B') (c₁ : Y.cls e₁ ≠ none) (c₂ : Y.cls e₂ ≠ none) (n₁ : Y.ends e₁ = (x, N))
    (n₂ : Y.ends e₂ = (N, y)) (hx : x ∈ Y.int) (hN : N ∈ Y.int) (hy : y ∈ Y.int) :
    Y.Rch B' N N x y :=
  rch_trans (rch_edge' h₁ c₁ (Or.inl n₁) hx hN) (rch_edge' h₂ c₂ (Or.inl n₂) hN hy)

/-- Key fact of [II, Claim A.4]: in a doubly connected graph `H`, the `Θ` edge `b₀` and the blue
solid edge `b` between internal vertices, each replaced by a path through a new vertex `N`, give
a doubly connected graph `Y`. The graph `Y` is described by its ends and classes. -/
private theorem dc_ts [DecidableEq V] {H Y : MGraph V E} {N : V} {b₀ b₂ b b₄ : E}
    (hH : H.DC) (hnd : [b₀, b₂, b, b₄].Nodup) (h0 : H.cls b₀ = some .diff)
    (hb : H.cls b = some .plus) (hx₀ : (H.ends b₀).1 ∈ H.int) (hy₀ : (H.ends b₀).2 ∈ H.int)
    (hx : (H.ends b).1 ∈ H.int) (hy : (H.ends b).2 ∈ H.int) (h2 : H.cls b₂ = none)
    (h4 : H.cls b₄ = none) (hint : Y.int = insert N H.int)
    (hY0 : Y.ends b₀ = ((H.ends b₀).1, N)) (hY2 : Y.ends b₂ = (N, (H.ends b₀).2))
    (hYb : Y.ends b = ((H.ends b).1, N)) (hY4 : Y.ends b₄ = (N, (H.ends b).2))
    (hYo : ∀ e, e ≠ b₀ → e ≠ b₂ → e ≠ b → e ≠ b₄ → Y.ends e = H.ends e ∧ Y.cls e = H.cls e)
    (c0 : Y.cls b₀ = some .diff) (c2 : Y.cls b₂ = some .diff) (cb : Y.cls b = some .plus)
    (c4 : Y.cls b₄ = some .plus) : Y.DC := by
  classical
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := mm_nodup4 hnd
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := hH
  have hNY : N ∈ Y.int := by rw [hint]; exact Finset.mem_insert_self _ _
  have hsub : H.int ⊆ Y.int := by rw [hint]; exact Finset.subset_insert _ _
  have nK : ∀ e ∈ K, H.cls e ≠ none := fun e he => by rw [hK e he]; simp
  have nL : ∀ e ∈ L, H.cls e ≠ none := fun e he => by
    rcases hL e he with h | h | h <;> rw [h] <;> simp
  have bK : b ∉ K := fun h => by have := hK b h; rw [hb] at this; simp at this
  have b2K : b₂ ∉ K := fun h => nK b₂ h h2
  have b4K : b₄ ∉ K := fun h => nK b₄ h h4
  have b2L : b₂ ∉ L := fun h => nL b₂ h h2
  have b4L : b₄ ∉ L := fun h => nL b₄ h h4
  have ne0 : Y.cls b₀ ≠ none := by rw [c0]; simp
  have ne2 : Y.cls b₂ ≠ none := by rw [c2]; simp
  have neb : Y.cls b ≠ none := by rw [cb]; simp
  have ne4 : Y.cls b₄ ≠ none := by rw [c4]; simp
  have hx₀' := hsub hx₀
  have hy₀' := hsub hy₀
  have hx' := hsub hx
  have hy' := hsub hy
  -- the classes of the other edges
  have oK : ∀ e ∈ K, e ≠ b₀ → Y.cls e = some .diff := fun e he e0 => by
    rw [(hYo e e0 (fun h => b2K (h ▸ he)) (fun h => bK (h ▸ he)) (fun h => b4K (h ▸ he))).2]
    exact hK e he
  have oL : ∀ e ∈ L, e ≠ b₀ → e ≠ b →
      (Y.cls e = some .diff ∨ Y.cls e = some .plus ∨ Y.cls e = some .ghost) := fun e he e0 eb => by
    rw [(hYo e e0 (fun h => b2L (h ▸ he)) eb (fun h => b4L (h ▸ he))).2]
    exact hL e he
  have same : ∀ (B B' : Finset E), (∀ e ∈ B, e ≠ b₀ → e ≠ b → e ∈ B') → ∀ e ∈ B,
      H.cls e ≠ none → e ≠ b₀ → e ≠ b → Y.ends e = H.ends e ∧ Y.cls e ≠ none ∧ e ∈ B' := by
    intro B B' hBB e he hc e0 eb
    have e2 : e ≠ b₂ := fun h => hc (h ▸ h2)
    have e4 : e ≠ b₄ := fun h => hc (h ▸ h4)
    obtain ⟨h1, h1'⟩ := hYo e e0 e2 eb e4
    exact ⟨h1, by rw [h1']; exact hc, hBB e he e0 eb⟩
  -- the blue net with `b`
  have hsL₀ : H.Spans (insert b L) := spans_mono' hsL (Finset.subset_insert _ _)
  have pb : ∀ B' : Finset E, b ∈ B' → b₄ ∈ B' →
      Y.Rch B' N N (H.ends b).1 (H.ends b).2 := fun B' h h' =>
    rch_two h h' neb ne4 hYb hY4 hx' hNY hy'
  have p0 : ∀ B' : Finset E, b₀ ∈ B' → b₂ ∈ B' →
      Y.Rch B' N N (H.ends b₀).1 (H.ends b₀).2 := fun B' h h' =>
    rch_two h h' ne0 ne2 hY0 hY2 hx₀' hNY hy₀'
  by_cases h0L : b₀ ∈ L
  · -- `b₀` in the blue net: one end of `b₀` is joined to `(H.ends b).1` without `b₀`
    have h0K : b₀ ∉ K := fun h => Finset.disjoint_left.1 hd h h0L
    have hr := rch_split (r := N) b₀ (rch_of_spans N N hsL₀ hx hx₀)
    have side : H.Rch ((insert b L).erase b₀) N N (H.ends b).1 (H.ends b₀).1 ∨
        H.Rch ((insert b L).erase b₀) N N (H.ends b).1 (H.ends b₀).2 := by
      rcases hr with hr | hr | hr
      · exact Or.inl hr
      · exact Or.inl hr
      · exact Or.inr hr
    rcases side with side | side
    · refine ⟨insert b₀ K, insert b₂ (insert b₄ ((insert b L).erase b₀)), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_insert_left]
        refine ⟨by simp [h02, h04], ?_⟩
        rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
        exact ⟨b2K, b4K, Finset.disjoint_left.2 fun e he he' => by
          obtain ⟨-, he'⟩ := Finset.mem_erase.1 he'
          rcases Finset.mem_insert.1 he' with rfl | he'
          · exact bK he
          · exact Finset.disjoint_left.1 hd he he'⟩
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact c0
        · exact oK e he (fun h => h0K (h ▸ he))
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inl c2
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inl c4)
        obtain ⟨e0, he⟩ := Finset.mem_erase.1 he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inl cb)
        by_cases eb : e = b
        · subst eb; exact Or.inr (Or.inl cb)
        · exact oL e he e0 eb
      · refine ts_spans hsK hint (same K _ fun e he _ _ => Finset.mem_insert_of_mem he)
          (fun h => absurd h h0K) (fun h => absurd h bK) ⟨_, hx₀, ?_⟩
        exact rch_edge' (Finset.mem_insert_self _ _) ne0 (Or.inr hY0) hNY hx₀'
      · have hB' : b ∈ insert b₂ (insert b₄ ((insert b L).erase b₀)) := by simp [h0b.symm]
        have hB4 : b₄ ∈ insert b₂ (insert b₄ ((insert b L).erase b₀)) := by simp
        have hB2 : b₂ ∈ insert b₂ (insert b₄ ((insert b L).erase b₀)) := by simp
        have lift := fun {u v : V} (h : H.Rch ((insert b L).erase b₀) N N u v) =>
          ts_rch (b₀ := b₀) (b := b) hsub (same _ _ fun e he _ _ => by simp [he]) (fun h => by simp
              at h)
            (fun _ _ => pb _ hB' hB4) h
        refine ts_spans hsL₀ hint (same _ _ fun e he e0 _ => by simp [Finset.mem_erase, e0, he])
          (fun _ _ => ?_) (fun _ _ => pb _ hB' hB4) ⟨_, hx, ?_⟩
        · exact rch_trans (rch_symm (lift side))
            (rch_two hB' hB2 neb ne2 hYb hY2 hx' hNY hy₀')
        · exact rch_edge' hB' neb (Or.inr hYb) hNY hx'
    · refine ⟨insert b₂ K, insert b₄ (insert b L), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_insert_left]
        refine ⟨by simp [h24, h2b, b2L], ?_⟩
        rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
        exact ⟨b4K, bK, hd⟩
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact c2
        · exact oK e he (fun h => h0K (h ▸ he))
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inl c4)
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inl cb)
        by_cases e0 : e = b₀
        · subst e0; exact Or.inl c0
        by_cases eb : e = b
        · subst eb; exact Or.inr (Or.inl cb)
        · exact oL e he e0 eb
      · refine ts_spans hsK hint (same K _ fun e he _ _ => Finset.mem_insert_of_mem he)
          (fun h => absurd h h0K) (fun h => absurd h bK) ⟨_, hy₀, ?_⟩
        exact rch_edge' (Finset.mem_insert_self _ _) ne2 (Or.inl hY2) hNY hy₀'
      · have hB' : b ∈ insert b₄ (insert b L) := by simp
        have hB4 : b₄ ∈ insert b₄ (insert b L) := by simp
        have hB0 : b₀ ∈ insert b₄ (insert b L) := by simp [h0L]
        have lift := fun {u v : V} (h : H.Rch ((insert b L).erase b₀) N N u v) =>
          ts_rch (b₀ := b₀) (b := b) hsub
            (same _ (insert b₄ (insert b L)) fun e he _ _ => by
              simp only [Finset.mem_erase] at he; simp [he.2])
            (fun h => by simp at h) (fun _ _ => pb _ hB' hB4) h
        refine ts_spans hsL₀ hint (same _ _ fun e he _ _ => Finset.mem_insert_of_mem he)
          (fun _ _ => ?_) (fun _ _ => pb _ hB' hB4) ⟨_, hx, ?_⟩
        · exact rch_trans (rch_edge' hB0 ne0 (Or.inl hY0) hx₀' hNY)
            (rch_trans (rch_edge' hB' neb (Or.inr hYb) hNY hx') (lift side))
        · exact rch_edge' hB' neb (Or.inr hYb) hNY hx'
  · have hL₀ : b₀ ∉ insert b L := by simp [h0b, h0L]
    by_cases h0K : b₀ ∈ K
    · refine ⟨insert b₂ K, insert b₄ (insert b L), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_insert_left]
        refine ⟨by simp [h24, h2b, b2L], ?_⟩
        rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
        exact ⟨b4K, bK, hd⟩
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact c2
        by_cases e0 : e = b₀
        · subst e0; exact c0
        · exact oK e he e0
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inl c4)
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inl cb)
        by_cases eb : e = b
        · subst eb; exact Or.inr (Or.inl cb)
        · exact oL e he (fun h => h0L (h ▸ he)) eb
      · refine ts_spans hsK hint (same K _ fun e he _ _ => Finset.mem_insert_of_mem he)
          (fun _ _ => p0 _ (Finset.mem_insert_of_mem h0K) (Finset.mem_insert_self _ _))
          (fun h => absurd h bK) ⟨_, hx₀, ?_⟩
        exact rch_edge' (Finset.mem_insert_of_mem h0K) ne0 (Or.inr hY0) hNY hx₀'
      · refine ts_spans hsL₀ hint (same _ _ fun e he _ _ => Finset.mem_insert_of_mem he)
          (fun h => absurd h hL₀) (fun _ _ => pb _ (by simp) (by simp)) ⟨_, hx, ?_⟩
        exact rch_edge' (by simp) neb (Or.inr hYb) hNY hx'
    · refine ⟨insert b₀ K, insert b₄ (insert b L), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_insert_left]
        refine ⟨by simp [h04, h0b, h0L], ?_⟩
        rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
        exact ⟨b4K, bK, hd⟩
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact c0
        · exact oK e he (fun h => h0K (h ▸ he))
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inl c4)
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inr (Or.inl cb)
        by_cases eb : e = b
        · subst eb; exact Or.inr (Or.inl cb)
        · exact oL e he (fun h => h0L (h ▸ he)) eb
      · refine ts_spans hsK hint (same K _ fun e he _ _ => Finset.mem_insert_of_mem he)
          (fun h => absurd h h0K) (fun h => absurd h bK) ⟨_, hx₀, ?_⟩
        exact rch_edge' (Finset.mem_insert_self _ _) ne0 (Or.inr hY0) hNY hx₀'
      · refine ts_spans hsL₀ hint (same _ _ fun e he _ _ => Finset.mem_insert_of_mem he)
          (fun h => absurd h hL₀) (fun _ _ => pb _ (by simp) (by simp)) ⟨_, hx, ?_⟩
        exact rch_edge' (by simp) neb (Or.inr hYb) hNY hx'

/-- Nets of `H` with the edge `b` absent: classes and membership of the special edges. -/
private theorem ts_nets_facts {H : MGraph V E} {K L : Finset E} {b₂ b b₄ : E}
    (hK : ∀ e ∈ K, H.cls e = some .diff)
    (hL : ∀ e ∈ L, H.cls e = some .diff ∨ H.cls e = some .plus ∨ H.cls e = some .ghost)
    (hbn : H.cls b = none) (h2 : H.cls b₂ = none) (h4 : H.cls b₄ = none) :
    (∀ e ∈ K, H.cls e ≠ none) ∧ (∀ e ∈ L, H.cls e ≠ none) ∧ b ∉ K ∧ b ∉ L ∧ b₂ ∉ K ∧
      b₂ ∉ L ∧ b₄ ∉ K ∧ b₄ ∉ L := by
  have nK : ∀ e ∈ K, H.cls e ≠ none := fun e he => by rw [hK e he]; simp
  have nL : ∀ e ∈ L, H.cls e ≠ none := fun e he => by
    rcases hL e he with h | h | h <;> rw [h] <;> simp
  exact ⟨nK, nL, fun h => nK b h hbn, fun h => nL b h hbn, fun h => nK b₂ h h2,
    fun h => nL b₂ h h2, fun h => nK b₄ h h4, fun h => nL b₄ h h4⟩

/-- [II, Claim A.4 (ii)], first case: nets `K`, `L` of `H` (the graph with `b` removed) with `b₀`
not in the blue net. Black: `K` with `b₀` replaced by the path `b₀`, `b₂` (or `b₀` added); blue:
`L` and an edge `g` from `N` to an internal vertex. -/
private theorem dc_ts_A [DecidableEq V] {H Y : MGraph V E} {N : V}
    {b₀ b₂ b b₄ g : E} {K L : Finset E} (hnd : [b₀, b₂, b, b₄].Nodup) (hd : Disjoint K L)
    (hK : ∀ e ∈ K, H.cls e = some .diff)
    (hL : ∀ e ∈ L, H.cls e = some .diff ∨ H.cls e = some .plus ∨ H.cls e = some .ghost)
    (hsK : H.Spans K) (hsL : H.Spans L) (h0L : b₀ ∉ L)
    (hx₀ : (H.ends b₀).1 ∈ H.int) (hy₀ : (H.ends b₀).2 ∈ H.int) (hbn : H.cls b = none)
    (h2 : H.cls b₂ = none) (h4 : H.cls b₄ = none) (hint : Y.int = insert N H.int)
    (hY0 : Y.ends b₀ = ((H.ends b₀).1, N)) (hY2 : Y.ends b₂ = (N, (H.ends b₀).2))
    (hYo : ∀ e, e ≠ b₀ → e ≠ b₂ → e ≠ b → e ≠ b₄ → Y.ends e = H.ends e ∧ Y.cls e = H.cls e)
    (c0 : Y.cls b₀ = some .diff) (c2 : Y.cls b₂ = some .diff) (hg : g = b ∨ g = b₄)
    (cg : Y.cls g = some .diff ∨ Y.cls g = some .plus) {w : V} (hw : w ∈ H.int)
    (hge : Y.ends g = (w, N) ∨ Y.ends g = (N, w)) : Y.DC := by
  classical
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := mm_nodup4 hnd
  obtain ⟨nK, nL, bK, bL, b2K, b2L, b4K, b4L⟩ := ts_nets_facts hK hL hbn h2 h4
  have hNY : N ∈ Y.int := by rw [hint]; exact Finset.mem_insert_self _ _
  have hsub : H.int ⊆ Y.int := by rw [hint]; exact Finset.subset_insert _ _
  have ne0 : Y.cls b₀ ≠ none := by rw [c0]; simp
  have ne2 : Y.cls b₂ ≠ none := by rw [c2]; simp
  have neg : Y.cls g ≠ none := by rcases cg with h | h <;> rw [h] <;> simp
  have gK : g ∉ K := by rcases hg with rfl | rfl <;> assumption
  have gL : g ∉ L := by rcases hg with rfl | rfl <;> assumption
  have g0 : g ≠ b₀ := by rcases hg with rfl | rfl <;> [exact h0b.symm; exact h04.symm]
  have g2 : g ≠ b₂ := by rcases hg with rfl | rfl <;> [exact h2b.symm; exact h24.symm]
  have same : ∀ (B B' : Finset E), (∀ e ∈ B, e ≠ b₀ → e ∈ B') → ∀ e ∈ B,
      H.cls e ≠ none → e ≠ b₀ → e ≠ b → Y.ends e = H.ends e ∧ Y.cls e ≠ none ∧ e ∈ B' := by
    intro B B' hBB e he hc e0 eb
    obtain ⟨h1, h1'⟩ := hYo e e0 (fun h => hc (h ▸ h2)) eb (fun h => hc (h ▸ h4))
    exact ⟨h1, by rw [h1']; exact hc, hBB e he e0⟩
  have ocls : ∀ e, H.cls e ≠ none → e ≠ b₀ → Y.cls e = H.cls e := fun e hc e0 =>
    (hYo e e0 (fun h => hc (h ▸ h2)) (fun h => hc (h ▸ hbn)) (fun h => hc (h ▸ h4))).2
  have hL' : Y.Spans (insert g L) := by
    refine ts_spans hsL hint (same L _ fun e he _ => Finset.mem_insert_of_mem he)
      (fun h => absurd h h0L) (fun _ h => absurd hbn h) ⟨w, hw, ?_⟩
    rcases hge with hge | hge
    · exact rch_edge' (Finset.mem_insert_self _ _) neg (Or.inr hge) hNY (hsub hw)
    · exact rch_edge' (Finset.mem_insert_self _ _) neg (Or.inl hge) hNY (hsub hw)
  have cL : ∀ e ∈ insert g L, Y.cls e = some .diff ∨ Y.cls e = some .plus ∨
      Y.cls e = some .ghost := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · rcases cg with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [ocls e (nL e he) (fun h => h0L (h ▸ he))]; exact hL e he
  by_cases h0K : b₀ ∈ K
  · refine ⟨insert b₂ K, insert g L, ?_, ?_, cL, ?_, hL'⟩
    · rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
      exact ⟨by simp [g2.symm, b2L], gK, hd⟩
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact c2
      by_cases e0 : e = b₀
      · subst e0; exact c0
      · rw [ocls e (nK e he) e0]; exact hK e he
    · refine ts_spans hsK hint (same K _ fun e he _ => Finset.mem_insert_of_mem he)
        (fun _ _ => rch_two (Finset.mem_insert_of_mem h0K) (Finset.mem_insert_self _ _) ne0 ne2
          hY0 hY2 (hsub hx₀) hNY (hsub hy₀)) (fun h => absurd h bK) ⟨_, hx₀, ?_⟩
      exact rch_edge' (Finset.mem_insert_of_mem h0K) ne0 (Or.inr hY0) hNY (hsub hx₀)
  · refine ⟨insert b₀ K, insert g L, ?_, ?_, cL, ?_, hL'⟩
    · rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
      exact ⟨by simp [g0.symm, h0L], gK, hd⟩
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact c0
      · rw [ocls e (nK e he) (fun h => h0K (h ▸ he))]; exact hK e he
    · refine ts_spans hsK hint (same K _ fun e he _ => Finset.mem_insert_of_mem he)
        (fun h => absurd h h0K) (fun h => absurd h bK) ⟨_, hx₀, ?_⟩
      exact rch_edge' (Finset.mem_insert_self _ _) ne0 (Or.inr hY0) hNY (hsub hx₀)

/-- [II, Claim A.4 (ii)], second case, with `b₀` in the blue net `L` of `H` (the graph with `b`
removed) and `b₄` absent: black `K` and one half of `b₀`; blue `L` with `b₀` replaced by a path
through `b`. -/
private theorem dc_ts_B [DecidableEq V] {H Y : MGraph V E} {N : V}
    {b₀ b₂ b b₄ : E} {K L : Finset E} (hnd : [b₀, b₂, b, b₄].Nodup) (hd : Disjoint K L)
    (hK : ∀ e ∈ K, H.cls e = some .diff)
    (hL : ∀ e ∈ L, H.cls e = some .diff ∨ H.cls e = some .plus ∨ H.cls e = some .ghost)
    (hsK : H.Spans K) (hsL : H.Spans L) (h0L : b₀ ∈ L)
    (hx₀ : (H.ends b₀).1 ∈ H.int) (hy₀ : (H.ends b₀).2 ∈ H.int) (hx : (H.ends b).1 ∈ H.int)
    (hbn : H.cls b = none)
    (h2 : H.cls b₂ = none) (h4 : H.cls b₄ = none) (hint : Y.int = insert N H.int)
    (hY0 : Y.ends b₀ = ((H.ends b₀).1, N)) (hY2 : Y.ends b₂ = (N, (H.ends b₀).2))
    (hYb : Y.ends b = ((H.ends b).1, N))
    (hYo : ∀ e, e ≠ b₀ → e ≠ b₂ → e ≠ b → e ≠ b₄ → Y.ends e = H.ends e ∧ Y.cls e = H.cls e)
    (c0 : Y.cls b₀ = some .diff) (c2 : Y.cls b₂ = some .diff) (cb : Y.cls b = some .plus) :
    Y.DC := by
  classical
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := mm_nodup4 hnd
  obtain ⟨nK, nL, bK, bL, b2K, b2L, b4K, b4L⟩ := ts_nets_facts hK hL hbn h2 h4
  have hNY : N ∈ Y.int := by rw [hint]; exact Finset.mem_insert_self _ _
  have hsub : H.int ⊆ Y.int := by rw [hint]; exact Finset.subset_insert _ _
  have ne0 : Y.cls b₀ ≠ none := by rw [c0]; simp
  have ne2 : Y.cls b₂ ≠ none := by rw [c2]; simp
  have neb : Y.cls b ≠ none := by rw [cb]; simp
  have h0K : b₀ ∉ K := fun h => Finset.disjoint_left.1 hd h h0L
  have same : ∀ (B B' : Finset E), (∀ e ∈ B, e ≠ b₀ → e ∈ B') → ∀ e ∈ B,
      H.cls e ≠ none → e ≠ b₀ → e ≠ b → Y.ends e = H.ends e ∧ Y.cls e ≠ none ∧ e ∈ B' := by
    intro B B' hBB e he hc e0 eb
    obtain ⟨h1, h1'⟩ := hYo e e0 (fun h => hc (h ▸ h2)) eb (fun h => hc (h ▸ h4))
    exact ⟨h1, by rw [h1']; exact hc, hBB e he e0⟩
  have ocls : ∀ e, H.cls e ≠ none → e ≠ b₀ → Y.cls e = H.cls e := fun e hc e0 =>
    (hYo e e0 (fun h => hc (h ▸ h2)) (fun h => hc (h ▸ hbn)) (fun h => hc (h ▸ h4))).2
  have hr := rch_split (r := N) b₀ (rch_of_spans N N hsL hx hx₀)
  have side : H.Rch (L.erase b₀) N N (H.ends b).1 (H.ends b₀).1 ∨
      H.Rch (L.erase b₀) N N (H.ends b).1 (H.ends b₀).2 := by
    rcases hr with hr | hr | hr
    · exact Or.inl hr
    · exact Or.inl hr
    · exact Or.inr hr
  rcases side with side | side
  · refine ⟨insert b₀ K, insert b₂ (insert b (L.erase b₀)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_insert_left]
      refine ⟨by simp [h02, h0b], ?_⟩
      rw [Finset.disjoint_insert_right, Finset.disjoint_insert_right]
      exact ⟨b2K, bK, hd.mono_right (Finset.erase_subset _ _)⟩
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact c0
      · rw [ocls e (nK e he) (fun h => h0K (h ▸ he))]; exact hK e he
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact Or.inl c2
      rcases Finset.mem_insert.1 he with rfl | he
      · exact Or.inr (Or.inl cb)
      obtain ⟨e0, he⟩ := Finset.mem_erase.1 he
      rw [ocls e (nL e he) e0]; exact hL e he
    · refine ts_spans hsK hint (same K _ fun e he _ => Finset.mem_insert_of_mem he)
        (fun h => absurd h h0K) (fun h => absurd h bK) ⟨_, hx₀, ?_⟩
      exact rch_edge' (Finset.mem_insert_self _ _) ne0 (Or.inr hY0) hNY (hsub hx₀)
    · have hB' : b ∈ insert b₂ (insert b (L.erase b₀)) := by simp
      have hB2 : b₂ ∈ insert b₂ (insert b (L.erase b₀)) := by simp
      have lift := fun {u v : V} (h : H.Rch (L.erase b₀) N N u v) =>
        ts_rch (b₀ := b₀) (b := b) (B' := insert b₂ (insert b (L.erase b₀))) hsub
          (same _ _ fun e he _ => by simp [he]) (fun h => by simp at h)
          (fun _ h => absurd hbn h) h
      refine ts_spans hsL hint (same _ _ fun e he e0 => by simp [Finset.mem_erase, e0, he])
        (fun _ _ => ?_) (fun _ h => absurd hbn h) ⟨_, hx, ?_⟩
      · exact rch_trans (rch_symm (lift side))
          (rch_two hB' hB2 neb ne2 hYb hY2 (hsub hx) hNY (hsub hy₀))
      · exact rch_edge' hB' neb (Or.inr hYb) hNY (hsub hx)
  · refine ⟨insert b₂ K, insert b L, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
      exact ⟨by simp [h2b, b2L], bK, hd⟩
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact c2
      · rw [ocls e (nK e he) (fun h => h0K (h ▸ he))]; exact hK e he
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact Or.inr (Or.inl cb)
      by_cases e0 : e = b₀
      · subst e0; exact Or.inl c0
      · rw [ocls e (nL e he) e0]; exact hL e he
    · refine ts_spans hsK hint (same K _ fun e he _ => Finset.mem_insert_of_mem he)
        (fun h => absurd h h0K) (fun h => absurd h bK) ⟨_, hy₀, ?_⟩
      exact rch_edge' (Finset.mem_insert_self _ _) ne2 (Or.inl hY2) hNY (hsub hy₀)
    · have hB' : b ∈ insert b L := by simp
      have hB0 : b₀ ∈ insert b L := by simp [h0L]
      have lift := fun {u v : V} (h : H.Rch (L.erase b₀) N N u v) =>
        ts_rch (b₀ := b₀) (b := b) hsub
          (same _ (insert b L) fun e he _ => by
            simp only [Finset.mem_erase] at he; simp [he.2])
          (fun h => by simp at h) (fun _ h => absurd hbn h) h
      refine ts_spans hsL hint (same _ _ fun e he _ => Finset.mem_insert_of_mem he)
        (fun _ _ => ?_) (fun _ h => absurd hbn h) ⟨_, hx, ?_⟩
      · exact rch_trans (rch_edge' hB0 ne0 (Or.inl hY0) (hsub hx₀) hNY)
          (rch_trans (rch_edge' hB' neb (Or.inr hYb) hNY (hsub hx)) (lift side))
      · exact rch_edge' hB' neb (Or.inr hYb) hNY (hsub hx)

/-- [II, Claim A.4 (ii)], second case, after `b₄` is changed into a `Θ` edge and `b` removed:
black `K` and `b₄`; blue `L` with `b₀` replaced by the path `b₀`, `b₂`. -/
private theorem dc_ts_C [DecidableEq V] {H Y : MGraph V E} {N : V}
    {b₀ b₂ b b₄ : E} {K L : Finset E} (hnd : [b₀, b₂, b, b₄].Nodup) (hd : Disjoint K L)
    (hK : ∀ e ∈ K, H.cls e = some .diff)
    (hL : ∀ e ∈ L, H.cls e = some .diff ∨ H.cls e = some .plus ∨ H.cls e = some .ghost)
    (hsK : H.Spans K) (hsL : H.Spans L) (h0L : b₀ ∈ L)
    (hx₀ : (H.ends b₀).1 ∈ H.int) (hy₀ : (H.ends b₀).2 ∈ H.int) (hy : (H.ends b).2 ∈ H.int)
    (hbn : H.cls b = none)
    (h2 : H.cls b₂ = none) (h4 : H.cls b₄ = none) (hint : Y.int = insert N H.int)
    (hY0 : Y.ends b₀ = ((H.ends b₀).1, N)) (hY2 : Y.ends b₂ = (N, (H.ends b₀).2))
    (hY4 : Y.ends b₄ = (N, (H.ends b).2))
    (hYo : ∀ e, e ≠ b₀ → e ≠ b₂ → e ≠ b → e ≠ b₄ → Y.ends e = H.ends e ∧ Y.cls e = H.cls e)
    (c0 : Y.cls b₀ = some .diff) (c2 : Y.cls b₂ = some .diff) (c4 : Y.cls b₄ = some .diff) :
    Y.DC := by
  classical
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := mm_nodup4 hnd
  obtain ⟨nK, nL, bK, bL, b2K, b2L, b4K, b4L⟩ := ts_nets_facts hK hL hbn h2 h4
  have hNY : N ∈ Y.int := by rw [hint]; exact Finset.mem_insert_self _ _
  have hsub : H.int ⊆ Y.int := by rw [hint]; exact Finset.subset_insert _ _
  have ne0 : Y.cls b₀ ≠ none := by rw [c0]; simp
  have ne2 : Y.cls b₂ ≠ none := by rw [c2]; simp
  have ne4 : Y.cls b₄ ≠ none := by rw [c4]; simp
  have h0K : b₀ ∉ K := fun h => Finset.disjoint_left.1 hd h h0L
  have same : ∀ (B B' : Finset E), (∀ e ∈ B, e ≠ b₀ → e ∈ B') → ∀ e ∈ B,
      H.cls e ≠ none → e ≠ b₀ → e ≠ b → Y.ends e = H.ends e ∧ Y.cls e ≠ none ∧ e ∈ B' := by
    intro B B' hBB e he hc e0 eb
    obtain ⟨h1, h1'⟩ := hYo e e0 (fun h => hc (h ▸ h2)) eb (fun h => hc (h ▸ h4))
    exact ⟨h1, by rw [h1']; exact hc, hBB e he e0⟩
  have ocls : ∀ e, H.cls e ≠ none → e ≠ b₀ → Y.cls e = H.cls e := fun e hc e0 =>
    (hYo e e0 (fun h => hc (h ▸ h2)) (fun h => hc (h ▸ hbn)) (fun h => hc (h ▸ h4))).2
  refine ⟨insert b₄ K, insert b₂ L, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
    exact ⟨by simp [h24.symm, b4L], b2K, hd⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact c4
    · rw [ocls e (nK e he) (fun h => h0K (h ▸ he))]; exact hK e he
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact Or.inl c2
    by_cases e0 : e = b₀
    · subst e0; exact Or.inl c0
    · rw [ocls e (nL e he) e0]; exact hL e he
  · refine ts_spans hsK hint (same K _ fun e he _ => Finset.mem_insert_of_mem he)
      (fun h => absurd h h0K) (fun h => absurd h bK) ⟨_, hy, ?_⟩
    exact rch_edge' (Finset.mem_insert_self _ _) ne4 (Or.inl hY4) hNY (hsub hy)
  · refine ts_spans hsL hint (same L _ fun e he _ => Finset.mem_insert_of_mem he)
      (fun _ _ => rch_two (by simp [h0L]) (by simp) ne0 ne2 hY0 hY2 (hsub hx₀) hNY (hsub hy₀))
      (fun _ h => absurd hbn h) ⟨_, hy₀, ?_⟩
    exact rch_edge' (Finset.mem_insert_self _ _) ne2 (Or.inl hY2) hNY (hsub hy₀)

/-- **[II, Claim A.4]**: in a doubly connected graph, with a `Θ` edge `b₀` and a blue solid edge
`b` between internal molecules each replaced by a path through a new molecule `N` (`b₀`, `b₂` and
`b`, `b₄`): (i) every redundant blue solid edge other than `b` stays redundant; (ii) if `b` is
redundant, then `b` is redundant and, after it is changed into a `Θ` edge, so is `b₄`, or `b₄` is
redundant and, after it is changed into a `Θ` edge, so is `b`. -/
theorem MGraph.claimA4 :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (N : V) (b₀ b₂ b b₄ : E),
    G.DC → N ∉ G.int → N ∉ G.ext → G.cls b₀ = some .diff → G.cls b = some .plus →
    (G.ends b₀).1 ∈ G.int → (G.ends b₀).2 ∈ G.int → (G.ends b).1 ∈ G.int →
    (G.ends b).2 ∈ G.int → [b₀, b₂, b, b₄].Nodup → G.cls b₂ = none → G.cls b₄ = none →
    (∀ e, e ≠ b → G.IsRedundant e → (G.twoSplit N b₀ b₂ b b₄).IsRedundant e) ∧
    (G.IsRedundant b →
      ((G.twoSplit N b₀ b₂ b b₄).IsRedundant b ∧
          ((G.twoSplit N b₀ b₂ b b₄).convert [b]).IsRedundant b₄) ∨
        ((G.twoSplit N b₀ b₂ b b₄).IsRedundant b₄ ∧
          ((G.twoSplit N b₀ b₂ b b₄).convert [b₄]).IsRedundant b)) := by
  intro V E _ _ G N b₀ b₂ b b₄ hdc _ _ h0 hb hx₀ hy₀ hx hy hnd h2 h4
  obtain ⟨hint, he0, he2, heb, he4, heo, hc2, hc4, hco⟩ := ts_facts G N hnd
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := mm_nodup4 hnd
  set T := G.twoSplit N b₀ b₂ b b₄ with hT
  have c0 : T.cls b₀ = some .diff := by rw [hco b₀ h02 h04, h0]
  have cb : T.cls b = some .plus := by rw [hco b h2b.symm hb4, hb]
  have c2 : T.cls b₂ = some .diff := by rw [hc2, h0]
  have c4 : T.cls b₄ = some .plus := by rw [hc4, hb]
  have hTo : ∀ e, e ≠ b₀ → e ≠ b₂ → e ≠ b → e ≠ b₄ → T.ends e = G.ends e ∧ T.cls e = G.cls e :=
    fun e e0 e2 eb e4 => ⟨heo e e0 e2 eb e4, hco e e2 e4⟩
  have dcT : T.DC := dc_ts hdc hnd h0 hb hx₀ hy₀ hx hy h2 h4 hint he0 he2 heb he4 hTo c0 c2 cb c4
  -- the graphs with an edge removed
  have upd : ∀ (c : E → Option MClass) (x e : E), e ≠ x → Function.update c x none e = c e :=
    fun c x e h => Function.update_of_ne h _ _
  refine ⟨fun e heb' ⟨he, _, hdce⟩ => ?_, fun ⟨_, _, hdcb⟩ => ?_⟩
  · have e0 : e ≠ b₀ := fun h => by rw [h, h0] at he; simp at he
    have e2 : e ≠ b₂ := fun h => by rw [h, h2] at he; simp at he
    have e4 : e ≠ b₄ := fun h => by rw [h, h4] at he; simp at he
    refine ⟨by rw [hco e e2 e4]; exact he, dcT, ?_⟩
    refine dc_ts (H := G.erase e) (Y := T.erase e) hdce hnd
      (by simp [MGraph.erase, upd _ _ _ e0.symm, h0]) (by simp [MGraph.erase, upd _ _ _ heb'.symm,
          hb])
      hx₀ hy₀ hx hy (by simp [MGraph.erase, upd _ _ _ e2.symm, h2])
      (by simp [MGraph.erase, upd _ _ _ e4.symm, h4]) hint he0 he2 heb he4 (fun f f0 f2 fb f4 => ?_)
      (by simp [MGraph.erase, upd _ _ _ e0.symm, c0])
      (by simp [MGraph.erase, upd _ _ _ e2.symm, c2])
      (by simp [MGraph.erase, upd _ _ _ heb'.symm, cb])
      (by simp [MGraph.erase, upd _ _ _ e4.symm, c4])
    refine ⟨heo f f0 f2 fb f4, ?_⟩
    by_cases hfe : f = e
    · subst hfe; simp [MGraph.erase]
    · simp [MGraph.erase, upd _ _ _ hfe, hco f f2 f4]
  · obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := hdcb
    have hbn : (G.erase b).cls b = none := by simp [MGraph.erase]
    have e2' : (G.erase b).cls b₂ = none := by simp [MGraph.erase, upd _ _ _ h2b, h2]
    have e4' : (G.erase b).cls b₄ = none := by simp [MGraph.erase, upd _ _ _ hb4.symm, h4]
    have oth : ∀ (Y : MGraph V E), Y.ends = T.ends → (∀ e, e ≠ b → e ≠ b₄ → Y.cls e = T.cls e) →
        ∀ e, e ≠ b₀ → e ≠ b₂ → e ≠ b → e ≠ b₄ →
          Y.ends e = (G.erase b).ends e ∧ Y.cls e = (G.erase b).cls e := by
      intro Y hYe hYc e e0 e2 eb e4
      refine ⟨by rw [hYe]; exact heo e e0 e2 eb e4, ?_⟩
      rw [hYc e eb e4, hco e e2 e4]
      simp [MGraph.erase, upd _ _ _ eb]
    have hcv : ∀ (x e : E), e ≠ x → (T.convert [x]).cls e = T.cls e := by
      intro x e h; simp [MGraph.convert, h]
    by_cases h0L : b₀ ∈ L
    · right
      refine ⟨⟨c4, dc_of_erase (x := b₄) ?_, ?_⟩, ⟨?_, dc_of_erase (x := b) ?_, ?_⟩⟩
      rotate_right 3
      · simp [MGraph.convert, hb4, cb]
      all_goals first
        | exact dc_ts_B hnd hd hK hL hsK hsL h0L hx₀ hy₀ hx hbn e2' e4' hint he0 he2 heb
            (oth _ rfl fun e _ h => upd _ _ _ h)
            (by simp [MGraph.erase, upd _ _ _ h04, c0]) (by simp [MGraph.erase, upd _ _ _ h24, c2])
            (by simp [MGraph.erase, upd _ _ _ hb4, cb])
        | exact dc_ts_C hnd hd hK hL hsK hsL h0L hx₀ hy₀ hy hbn e2' e4' hint he0 he2 he4
            (oth _ rfl fun e h _ => by simp [MGraph.erase, upd _ _ _ h, hcv b₄ e (by assumption)])
            (by simp [MGraph.erase, upd _ _ _ h0b, hcv b₄ b₀ h04, c0])
            (by simp [MGraph.erase, upd _ _ _ h2b, hcv b₄ b₂ h24, c2])
            (by simp [MGraph.erase, upd _ _ _ hb4.symm, MGraph.convert, c4])
    · left
      refine ⟨⟨cb, dc_of_erase (x := b) ?_, ?_⟩, ⟨?_, dc_of_erase (x := b₄) ?_, ?_⟩⟩
      rotate_right 3
      · simp [MGraph.convert, hb4.symm, c4]
      all_goals first
        | exact dc_ts_A (g := b₄) hnd hd hK hL hsK hsL h0L hx₀ hy₀ hbn e2' e4' hint he0 he2
            (oth _ rfl fun e h _ => upd _ _ _ h)
            (by simp [MGraph.erase, upd _ _ _ h0b, c0]) (by simp [MGraph.erase, upd _ _ _ h2b, c2])
            (Or.inr rfl) (Or.inr (by simp [MGraph.erase, upd _ _ _ hb4.symm, c4])) hy
            (Or.inr he4)
        | exact dc_ts_A (g := b) hnd hd hK hL hsK hsL h0L hx₀ hy₀ hbn e2' e4' hint he0 he2
            (oth _ rfl fun e _ h => by simp [MGraph.erase, upd _ _ _ h, hcv b e (by assumption)])
            (by simp [MGraph.erase, upd _ _ _ h04, hcv b b₀ h0b, c0])
            (by simp [MGraph.erase, upd _ _ _ h24, hcv b b₂ h2b, c2]) (Or.inl rfl)
            (Or.inl (by simp [MGraph.erase, upd _ _ _ hb4, MGraph.convert, cb])) hx (Or.inl heb)

/-! ## The chain of isolated subsets -/

/-- The data of a chain of proper isolated subsets of a sequentially pre-deterministic graph
without ghost edges: the chain `P` with `k` members, the component `lev v` of each vertex, and the
two crossing edges `cc l` (diffusive) and `cc' l` (diffusive or blue solid) of `P (l + 1)`. -/
private structure Ctx [DecidableEq V] [DecidableEq E] (G : MGraph V E) where
  k : ℕ
  P : ℕ → Finset V
  lev : V → ℕ
  cc : ℕ → E
  cc' : ℕ → E
  spd : G.SPD
  chain : G.IsChain k P
  lev_le : ∀ v, lev v ≤ k
  memP : ∀ v ∈ G.int, ∀ m ≤ k, (v ∈ P m ↔ m ≤ lev v)
  Psub : ∀ m ≤ k, P m ⊆ G.int
  cc_ne : ∀ l < k, cc l ≠ cc' l
  cc_diff : ∀ l < k, G.cls (cc l) = some .diff
  cc'_cls : ∀ l < k, G.cls (cc' l) = some .diff ∨ G.cls (cc' l) = some .plus
  cross : ∀ l < k, ∀ e, G.Crosses (P (l + 1)) e ↔ e = cc l ∨ e = cc' l
  cc_ends : ∀ l < k, ∀ x, (x = cc l ∨ x = cc' l) → ∃ w, w ∈ G.int ∧ lev w = l + 1 ∧
    G.outer (P (l + 1)) x ∈ G.int ∧ lev (G.outer (P (l + 1)) x) = l ∧
    (G.ends x = (G.outer (P (l + 1)) x, w) ∨ G.ends x = (w, G.outer (P (l + 1)) x))
  jump : ∀ e, G.cls e ≠ none → G.cls e ≠ some .minus → (G.ends e).1 ∈ G.int →
    (G.ends e).2 ∈ G.int → lev (G.ends e).1 ≠ lev (G.ends e).2 →
    ∃ l < k, e = cc l ∨ e = cc' l

/-- The members of a chain decrease. -/
private theorem chain_anti {G : MGraph V E} {k : ℕ} {P : ℕ → Finset V} (hc : G.IsChain k P)
    {a b : ℕ} (hab : a ≤ b) (hbk : b ≤ k) : P b ⊆ P a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (hc.2.1 (a + n) (by omega)).1.2.1.trans (ih (by omega) (by omega))

/-- A member of a chain is the set of all internal vertices or an isolated subset. -/
private theorem chain_isoOrTop {G : MGraph V E} {k : ℕ} {P : ℕ → Finset V} (hc : G.IsChain k P)
    {l : ℕ} (hl : l ≤ k) : G.IsoOrTop (P l) := by
  rcases l with _ | l
  · exact Or.inl hc.1
  · exact Or.inr (hc.2.1 l (by omega)).1.1

/-- The ends of an edge cutting `P`: the outer end and an end in `P`. -/
private theorem ends_of_cut [DecidableEq V] {G : MGraph V E} {P : Finset V} {e : E}
    (h : G.Cut P e) : G.outer P e ∉ P ∧ ∃ w ∈ P,
      (G.ends e = (G.outer P e, w) ∨ G.ends e = (w, G.outer P e)) := by
  unfold MGraph.outer
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ite_eq_left h1]
    exact ⟨h2, _, h1, Or.inr rfl⟩
  · rw [ite_eq_right h1]
    exact ⟨h1, _, h2, Or.inl rfl⟩

/-- The chain data of a sequentially pre-deterministic graph without ghost edges. -/
private theorem ctx_exists [DecidableEq V] [DecidableEq E] [Nonempty E] {G : MGraph V E} {k : ℕ}
    {P : ℕ → Finset V} (hs : G.SPD) (hc : G.IsChain k P) (hng : ∀ e, G.cls e ≠ some .ghost) :
    ∃ C : Ctx G, C.k = k ∧ C.P = P := by
  classical
  have hdc := hs.1
  have Pint : ∀ m ≤ k, P m ⊆ G.int := fun m hm => hc.1 ▸ chain_anti hc (Nat.zero_le m) hm
  have hex : ∀ v, ∃ l, k ≤ l ∨ v ∉ P (l + 1) := fun _ => ⟨k, Or.inl le_rfl⟩
  let lev : V → ℕ := fun v => Nat.find (hex v)
  have lev_le : ∀ v, lev v ≤ k := fun v => Nat.find_min' _ (Or.inl le_rfl)
  have lev_spec : ∀ v, k ≤ lev v ∨ v ∉ P (lev v + 1) := fun v => Nat.find_spec (hex v)
  have lev_min : ∀ v l, l < lev v → v ∈ P (l + 1) := fun v l hl => by
    have := Nat.find_min (hex v) hl
    simp only [not_or, not_not] at this
    exact this.2
  have memP : ∀ v ∈ G.int, ∀ m ≤ k, (v ∈ P m ↔ m ≤ lev v) := by
    intro v hv m hm
    constructor
    · intro hvm
      by_contra hlt
      rw [not_le] at hlt
      rcases lev_spec v with h | h
      · exact absurd (lev_le v) (by omega)
      · exact h (chain_anti hc (by omega) hm hvm)
    · intro hml
      rcases m with _ | m
      · rw [hc.1]; exact hv
      · exact lev_min v m (by omega)
  have hcr : ∀ l, l < k → ∃ c c', c ≠ c' ∧ G.cls c = some .diff ∧
      (G.cls c' = some .diff ∨ G.cls c' = some .plus) ∧
      ∀ e, G.Crosses (P (l + 1)) e ↔ e = c ∨ e = c' := by
    intro l hl
    obtain ⟨⟨⟨-, e₁, e₂, hne, hx⟩, hss⟩, -⟩ := hc.2.1 l hl
    have hsub := Pint (l + 1) (by omega)
    obtain ⟨a, b, hab, ha, hb, hca, hcb⟩ := MGraph.claim51 V E G hdc (P (l + 1)) hsub
      (by
        obtain ⟨-, -, -, -, h⟩ := (hx e₁).2 (Or.inl rfl)
        rcases h with ⟨h, -⟩ | ⟨-, h⟩
        exacts [⟨_, h⟩, ⟨_, h⟩])
      (fun h => hss.2 (h.trans' (Pint l (by omega))))
    refine ⟨a, b, hab, hca, ?_, fun e => ?_⟩
    · rcases hcb with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hng b)
    · rw [hx e]
      rcases (hx a).1 ha with rfl | rfl <;> rcases (hx b).1 hb with rfl | rfl
      · exact absurd rfl hab
      · rfl
      · exact or_comm
      · exact absurd rfl hab
  choose! cc cc' hcc using hcr
  have cross : ∀ l < k, ∀ e, G.Crosses (P (l + 1)) e ↔ e = cc l ∨ e = cc' l :=
    fun l hl => (hcc l hl).2.2.2
  have levP : ∀ v ∈ G.int, ∀ m ≤ k, v ∈ P m → v ∉ P (m + 1) → lev v = m := by
    intro v hv m hm h1 h2
    have := (memP v hv m hm).1 h1
    by_cases hmk : m + 1 ≤ k
    · have := mt (memP v hv (m + 1) hmk).2 h2; omega
    · have := lev_le v; omega
  refine ⟨⟨k, P, lev, cc, cc', hs, hc, lev_le, memP, Pint, fun l hl => (hcc l hl).1,
    fun l hl => (hcc l hl).2.1, fun l hl => (hcc l hl).2.2.1, cross, ?_, ?_⟩, rfl, rfl⟩
  · intro l hl x hx
    have hxc : G.Crosses (P (l + 1)) x := (cross l hl x).2 hx
    have hpp : G.IsProperIso (P l) (P (l + 1)) := (hc.2.1 l hl).1
    have ho := MGraph.replace_ends V E G hdc (P l) (P (l + 1)) x (chain_isoOrTop hc hl.le) hpp hxc
    obtain ⟨ho1, ho2⟩ := Finset.mem_sdiff.1 ho
    have hoi := Pint l hl.le ho1
    obtain ⟨-, w, hw, hends⟩ := ends_of_cut hxc.2.2.2.2
    have hwi := Pint (l + 1) (by omega) hw
    refine ⟨w, hwi, ?_, hoi, levP _ hoi l hl.le ho1 ho2, hends⟩
    have h1 := (memP w hwi (l + 1) (by omega)).1 hw
    by_contra hne
    have h2 : l + 2 ≤ lev w := by omega
    have hk2 : l + 2 ≤ k := (lev_le w).trans' h2
    have hw2 : w ∈ P (l + 2) := (memP w hwi (l + 2) hk2).2 h2
    have ho2' : G.outer (P (l + 1)) x ∉ P (l + 2) := fun h => ho2 (chain_anti hc (by omega) hk2 h)
    have hcut2 : G.Cut (P (l + 2)) x := by
      rcases hends with h | h <;> simp only [MGraph.Cut, h] <;> tauto
    have hxc2 : G.Crosses (P (l + 2)) x := ⟨hxc.1, hxc.2.1, hxc.2.2.1, hxc.2.2.2.1, hcut2⟩
    have ho' := MGraph.replace_ends V E G hdc (P (l + 1)) (P (l + 2)) x
      (chain_isoOrTop hc (by omega)) (hc.2.1 (l + 1) (by omega)).1 hxc2
    have heq : G.outer (P (l + 2)) x = G.outer (P (l + 1)) x := by
      unfold MGraph.outer at ho2' ⊢
      rcases hends with h | h
      · rw [h] at ho2' ⊢
        simp only at ho2' ⊢
        split_ifs at ho2' ⊢ <;> simp_all
      · rw [h] at ho2' ⊢
        simp only at ho2' ⊢
        split_ifs at ho2' ⊢
        simp_all
    rw [heq] at ho'
    exact ho2 (Finset.mem_sdiff.1 ho').1
  · intro e hc1 hc2 h1 h2 hne
    have key : ∀ a b, (a = (G.ends e).1 ∧ b = (G.ends e).2 ∨ a = (G.ends e).2 ∧ b = (G.ends e).1) →
        lev a < lev b → ∃ l < k, e = cc l ∨ e = cc' l := by
      intro a b hab hlt
      have ha : a ∈ G.int := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
      have hb : b ∈ G.int := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
      have hlk : lev a < k := lt_of_lt_of_le hlt (lev_le b)
      refine ⟨lev a, hlk, (cross (lev a) hlk e).1 ⟨hc1, hc2, Or.inl h1, Or.inl h2, ?_⟩⟩
      have haP : a ∉ P (lev a + 1) := fun h => by
        have := (memP a ha _ (by omega)).1 h; omega
      have hbP : b ∈ P (lev a + 1) := (memP b hb _ (by omega)).2 (by omega)
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨haP, hbP⟩
      · exact Or.inl ⟨hbP, haP⟩
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key _ _ (Or.inl ⟨rfl, rfl⟩) h
    · exact key _ _ (Or.inr ⟨rfl, rfl⟩) h

/-! ## Induced subgraphs on parts of the chain -/

/-- A net `N` of a doubly connected graph, restricted to the edges inside `Q`, spans the subgraph
induced on `Q` if at most two edges with internal ends leave `Q`: otherwise `N` has two edges
leaving `Q` and the other net `N'` a third one. -/
private theorem spans_induce_of_cut2 [DecidableEq V] {X : MGraph V E} {N N' : Finset E}
    (hd : Disjoint N N') (hN : X.Spans N) (hN' : X.Spans N')
    (hNc : ∀ e ∈ N, X.cls e ≠ some .minus) (hN'c : ∀ e ∈ N', X.cls e ≠ some .minus)
    {Q : Finset V} (hQ : Q ⊆ X.int) (s : Finset E) (hs : s.card ≤ 2)
    (hcut : ∀ e, X.cls e ≠ none → X.cls e ≠ some .minus → (X.ends e).1 ∈ X.int →
      (X.ends e).2 ∈ X.int → X.Cut Q e → e ∈ s) :
    (X.induce Q).Spans (N.filter fun e => (X.ends e).1 ∈ Q ∧ (X.ends e).2 ∈ Q) := by
  classical
  intro S hS hne hnot
  by_contra hno
  have hin : ∀ e ∈ N, X.cls e ≠ none → (X.ends e).1 ∈ Q → (X.ends e).2 ∈ Q → ¬ X.Cut S e := by
    intro e he hc h1 h2 hcut'
    refine hno ⟨e, Finset.mem_filter.2 ⟨he, h1, h2⟩, ?_, h1, h2, hcut'⟩
    simp [MGraph.induce, h1, h2, hc]
  obtain ⟨v, hvQ, hvS⟩ := Finset.not_subset.1 hnot
  obtain ⟨w, hwS⟩ := hne
  have out : ∀ T : Finset V, T ⊆ Q → T.Nonempty → ¬ X.int ⊆ T → (∀ e ∈ N, X.cls e ≠ none →
      (X.ends e).1 ∈ Q → (X.ends e).2 ∈ Q → ¬ X.Cut T e) →
      ∃ e ∈ N, e ∈ s ∧ (X.ends e).1 ∈ X.int ∧ (X.ends e).2 ∈ X.int ∧
        (((X.ends e).1 ∈ T ∧ (X.ends e).2 ∉ Q) ∨ ((X.ends e).2 ∈ T ∧ (X.ends e).1 ∉ Q)) := by
    intro T hT hTne hTnot hTin
    obtain ⟨e, he, hc, h1, h2, hcut'⟩ := hN T (hT.trans hQ) hTne hTnot
    have := hTin e he hc
    simp only [MGraph.Cut] at this hcut'
    have hpos : ((X.ends e).1 ∈ T ∧ (X.ends e).2 ∉ Q) ∨ ((X.ends e).2 ∈ T ∧ (X.ends e).1 ∉ Q) := by
      rcases hcut' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨ha, fun hq => this (hT ha) hq (Or.inl ⟨ha, hb⟩)⟩
      · exact Or.inr ⟨hb, fun hq => this hq (hT hb) (Or.inr ⟨ha, hb⟩)⟩
    refine ⟨e, he, hcut e hc (hNc e he) h1 h2 ?_, h1, h2, hpos⟩
    simp only [MGraph.Cut]
    rcases hpos with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨hT ha, hb⟩
    · exact Or.inr ⟨hb, hT ha⟩
  have hin' : ∀ e ∈ N, X.cls e ≠ none → (X.ends e).1 ∈ Q → (X.ends e).2 ∈ Q →
      ¬ X.Cut (Q \ S) e := by
    intro e he hc h1 h2 hcut'
    refine hin e he hc h1 h2 ?_
    simp only [MGraph.Cut, Finset.mem_sdiff] at hcut' ⊢
    tauto
  obtain ⟨e₁, he₁, hs₁, -, -, hp₁⟩ := out S hS ⟨w, hwS⟩ (fun h => hvS (h (hQ hvQ))) hin
  obtain ⟨e₂, he₂, hs₂, -, -, hp₂⟩ := out (Q \ S) Finset.sdiff_subset
    ⟨v, Finset.mem_sdiff.2 ⟨hvQ, hvS⟩⟩
    (fun h => (Finset.mem_sdiff.1 (h (hQ (hS hwS)))).2 hwS) hin'
  have h12 : e₁ ≠ e₂ := by
    rintro rfl
    simp only [Finset.mem_sdiff] at hp₂
    rcases hp₁ with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hp₂ with ⟨c, d⟩ | ⟨c, d⟩
    · exact c.2 a
    · exact b c.1
    · exact d (hS a)
    · exact c.2 a
  -- the other net leaves `Q` too
  have hQnot : ¬ X.int ⊆ Q := by
    intro h
    obtain ⟨e, he, hc, h1, h2, hcut'⟩ := hN S (hS.trans hQ) ⟨w, hwS⟩ (fun h' => hvS (h' (hQ hvQ)))
    exact hin e he hc (h h1) (h h2) hcut'
  obtain ⟨f, hf, hfc, hf1, hf2, hfcut⟩ := hN' Q hQ ⟨v, hvQ⟩ hQnot
  have hfs := hcut f hfc (hN'c f hf) hf1 hf2 hfcut
  have h1f : e₁ ≠ f := fun h => Finset.disjoint_left.1 hd he₁ (h ▸ hf)
  have h2f : e₂ ≠ f := fun h => Finset.disjoint_left.1 hd he₂ (h ▸ hf)
  have hsub : ({e₁, e₂, f} : Finset E) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_eq_three.2 ⟨e₁, e₂, f, h12, h1f, h2f, rfl⟩] at this
  omega

/-- The subgraph induced on a set `Q` of internal vertices of a doubly connected graph, left by
at most two edges with internal ends, is doubly connected. -/
private theorem dc_induce_of_cut2 [DecidableEq V] {X : MGraph V E} (hX : X.DC) {Q : Finset V}
    (hQ : Q ⊆ X.int) (s : Finset E) (hs : s.card ≤ 2)
    (hcut : ∀ e, X.cls e ≠ none → X.cls e ≠ some .minus → (X.ends e).1 ∈ X.int →
      (X.ends e).2 ∈ X.int → X.Cut Q e → e ∈ s) : (X.induce Q).DC := by
  classical
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := hX
  have hKm : ∀ e ∈ K, X.cls e ≠ some .minus := fun e he => by rw [hK e he]; simp
  have hLm : ∀ e ∈ L, X.cls e ≠ some .minus := fun e he => by
    rcases hL e he with h | h | h <;> rw [h] <;> simp
  refine ⟨K.filter fun e => (X.ends e).1 ∈ Q ∧ (X.ends e).2 ∈ Q,
    L.filter fun e => (X.ends e).1 ∈ Q ∧ (X.ends e).2 ∈ Q,
    hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _), ?_, ?_,
    spans_induce_of_cut2 hd hsK hsL hKm hLm hQ s hs hcut,
    spans_induce_of_cut2 hd.symm hsL hsK hLm hKm hQ s hs hcut⟩
  · intro e he
    obtain ⟨he, h1, h2⟩ := Finset.mem_filter.1 he
    simp only [MGraph.induce, h1, h2, and_self, ↓reduceIte]
    exact hK e he
  · intro e he
    obtain ⟨he, h1, h2⟩ := Finset.mem_filter.1 he
    simp only [MGraph.induce, h1, h2, and_self, ↓reduceIte]
    exact hL e he

/-- Inducing twice. -/
private theorem induce_induce [DecidableEq V] (X : MGraph V E) {A B : Finset V} (h : B ⊆ A) :
    (X.induce A).induce B = X.induce B := by
  unfold MGraph.induce
  congr 1
  funext e
  by_cases hb : (X.ends e).1 ∈ B ∧ (X.ends e).2 ∈ B
  · simp [hb, h hb.1, h hb.2]
  · simp [hb]

/-- The vertices of the components `a, …, b - 1` of the chain. -/
private def Ctx.Lvl [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G) (a b : ℕ) :
    Finset V :=
  G.int.filter fun v => a ≤ C.lev v ∧ C.lev v < b

/-- Membership in the components `a, …, b - 1`. -/
private theorem Ctx.mem_Lvl [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {a b : ℕ} {v : V} : v ∈ C.Lvl a b ↔ v ∈ G.int ∧ a ≤ C.lev v ∧ C.lev v < b := by
  unfold Ctx.Lvl
  rw [Finset.mem_filter]

/-- The subgraph induced on the components `a, …, b - 1` of the chain is doubly connected. -/
private theorem Ctx.dc_Lvl [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {a : ℕ} (b : ℕ) (ha : a ≤ C.k) : (G.induce (C.Lvl a b)).DC := by
  classical
  have hdc := C.spd.1
  -- the subgraph induced on `P a`
  have h1 : (G.induce (C.P a)).DC := by
    rcases a with _ | a
    · refine dc_induce_of_cut2 hdc (C.Psub 0 ha) ∅ (by simp) fun e _ _ h1 h2 hc => ?_
      rw [C.chain.1] at hc
      simp only [MGraph.Cut] at hc
      tauto
    · obtain ⟨-, e₁, e₂, -, hx⟩ := (C.chain.2.1 a (by omega)).1.1
      refine dc_induce_of_cut2 hdc (C.Psub _ ha) {e₁, e₂} (Finset.card_le_two)
        fun e hc hm h1 h2 hcut => ?_
      rcases (hx e).1 ⟨hc, hm, Or.inl h1, Or.inl h2, hcut⟩ with rfl | rfl <;> simp
  have hsub : C.Lvl a b ⊆ C.P a := by
    intro v hv
    obtain ⟨hv, hav, -⟩ := C.mem_Lvl.1 hv
    exact (C.memP v hv a ha).2 hav
  rw [← induce_induce G hsub]
  by_cases hb : b ≤ C.k ∧ a < b
  · obtain ⟨hbk, hab⟩ := hb
    obtain ⟨-, e₁, e₂, -, hx⟩ := (C.chain.2.1 (b - 1) (by omega)).1.1
    refine dc_induce_of_cut2 h1 hsub {e₁, e₂} (Finset.card_le_two)
      fun e hc hm h1' h2' hcut => ?_
    have hcG : G.cls e ≠ none ∧ (G.ends e).1 ∈ C.P a ∧ (G.ends e).2 ∈ C.P a := by
      by_cases hin : (G.ends e).1 ∈ C.P a ∧ (G.ends e).2 ∈ C.P a
      · simp only [MGraph.induce, hin, and_self, ↓reduceIte] at hc
        exact ⟨hc, hin⟩
      · simp [MGraph.induce, hin] at hc
    obtain ⟨hcG, ha1, ha2⟩ := hcG
    have hmG : G.cls e ≠ some .minus := by
      simpa [MGraph.induce, ha1, ha2] using hm
    have hi1 := C.Psub a ha ha1
    have hi2 := C.Psub a ha ha2
    have hcut' : G.Cut (C.P (b - 1 + 1)) e := by
      have e1 := (C.memP _ hi1 a ha).1 ha1
      have e2 := (C.memP _ hi2 a ha).1 ha2
      have f1 := C.memP _ hi1 (b - 1 + 1) (by omega)
      have f2 := C.memP _ hi2 (b - 1 + 1) (by omega)
      simp only [MGraph.Cut, MGraph.induce, C.mem_Lvl] at hcut
      simp only [MGraph.Cut, f1, f2]
      rcases hcut with ⟨⟨-, -, h⟩, h'⟩ | ⟨h', ⟨-, -, h⟩⟩
      · refine Or.inr ⟨by omega, ?_⟩
        by_contra h''; exact h' ⟨hi2, e2, by omega⟩
      · refine Or.inl ⟨?_, by omega⟩
        by_contra h''; exact h' ⟨hi1, e1, by omega⟩
    rcases (hx e).1 ⟨hcG, hmG, Or.inl hi1, Or.inl hi2, hcut'⟩ with rfl | rfl <;> simp
  · refine dc_induce_of_cut2 h1 hsub ∅ (by simp) fun e hc _ h1' h2' hcut => ?_
    exfalso
    simp only [MGraph.induce] at h1' h2'
    simp only [MGraph.Cut, MGraph.induce, C.mem_Lvl] at hcut
    have e1 := (C.memP _ (C.Psub a ha h1') a ha).1 h1'
    have e2 := (C.memP _ (C.Psub a ha h2') a ha).1 h2'
    have l1 := C.lev_le (G.ends e).1
    have l2 := C.lev_le (G.ends e).2
    rcases hcut with ⟨⟨-, -, h⟩, h'⟩ | ⟨h', ⟨-, -, h⟩⟩
    · exact h' ⟨C.Psub a ha h2', e2, by omega⟩
    · exact h' ⟨C.Psub a ha h1', e1, by omega⟩

/-! ## Saturated sets under a merging map -/

/-- The map `f` identifies at most the two vertices `p`, `q`. -/
private def MergeMap (f : V → V) (p q : V) : Prop :=
  ∀ a b, f a = f b → a = b ∨ ((a = p ∨ a = q) ∧ (b = p ∨ b = q))

/-- The map of operation (A) identifies at most `M` and `M'`. -/
private theorem mergeMap_merge [DecidableEq V] (M M' : V) :
    MergeMap (fun v => if v = M' then M else v) M M' := by
  intro a b h
  by_cases ha : a = M' <;> by_cases hb : b = M' <;> simp only [ha, hb, ↓reduceIte] at h
  · exact Or.inl (ha.trans hb.symm)
  · exact Or.inr ⟨Or.inr ha, Or.inl h.symm⟩
  · exact Or.inr ⟨Or.inl h, Or.inr hb⟩
  · exact Or.inl h

/-- A set is saturated for `f`: a vertex whose image is the image of a member is a member. -/
private def Sat [DecidableEq V] (f : V → V) (S : Finset V) : Prop := ∀ a, f a ∈ S.image f → a ∈ S

/-- A set containing both or neither of the identified vertices is saturated. -/
private theorem sat_of [DecidableEq V] {f : V → V} {p q : V} (hf : MergeMap f p q) {S : Finset V}
    (hS : p ∈ S ↔ q ∈ S) : Sat f S := by
  intro a ha
  obtain ⟨s, hs, hfs⟩ := Finset.mem_image.1 ha
  rcases hf s a hfs with rfl | ⟨h1, h2⟩
  · exact hs
  · have hp : p ∈ S := by
      rcases h1 with rfl | rfl
      · exact hs
      · exact hS.2 hs
    rcases h2 with rfl | rfl
    · exact hp
    · exact hS.1 hp

/-- The image of a vertex lies in the image of a saturated set exactly when the vertex lies in
the set. -/
private theorem mem_image_sat [DecidableEq V] {f : V → V} {S : Finset V} (h : Sat f S) (a : V) :
    f a ∈ S.image f ↔ a ∈ S :=
  ⟨h a, Finset.mem_image_of_mem f⟩

/-- Inducing commutes with mapping the vertices, on a saturated set. -/
private theorem induce_mapV [DecidableEq V] (G : MGraph V E) {f : V → V} {S : Finset V}
    (h : Sat f S) : (G.mapV f).induce (S.image f) = (G.induce S).mapV f := by
  unfold MGraph.induce MGraph.mapV
  simp only [Finset.image_empty, mem_image_sat h]

/-- The image of a difference of saturated sets. -/
private theorem image_sdiff_sat [DecidableEq V] {f : V → V} {S P : Finset V} (hP : Sat f P) :
    S.image f \ P.image f = (S \ P).image f := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hn⟩
    exact ⟨s, ⟨hs, fun hp => hn ⟨s, hp, rfl⟩⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hsP⟩, rfl⟩
    exact ⟨⟨s, hs, rfl⟩, fun ⟨t, ht, hts⟩ => hsP (hP s (hts ▸ Finset.mem_image_of_mem f ht))⟩

/-- The difference of saturated sets is saturated. -/
private theorem sat_sdiff [DecidableEq V] {f : V → V} {S P : Finset V} (hS : Sat f S)
    (hP : Sat f P) : Sat f (S \ P) := by
  intro a ha
  rw [← image_sdiff_sat hP, Finset.mem_sdiff] at ha
  exact Finset.mem_sdiff.2 ⟨hS a ha.1, fun h => ha.2 (Finset.mem_image_of_mem f h)⟩

/-- The outer end commutes with mapping the vertices, on a saturated set. -/
private theorem outer_mapV [DecidableEq V] (G : MGraph V E) {f : V → V} {P : Finset V}
    (h : Sat f P) (e : E) : (G.mapV f).outer (P.image f) e = f (G.outer P e) := by
  unfold MGraph.outer MGraph.mapV
  simp only [mem_image_sat h]
  split_ifs <;> rfl

/-- The replacement of [II, Def 5.9 (iii)] commutes with mapping the vertices, on saturated
sets. -/
private theorem replace_mapV [DecidableEq V] [DecidableEq E] (G : MGraph V E) {f : V → V}
    {S P : Finset V} (hS : Sat f S) (hP : Sat f P) (e₁ e₂ : E) :
    (G.mapV f).replace (S.image f) (P.image f) e₁ e₂ = (G.replace S P e₁ e₂).mapV f := by
  have hSP := sat_sdiff hS hP
  unfold MGraph.replace
  rw [image_sdiff_sat hP, induce_mapV G hSP, outer_mapV G hP, outer_mapV G hP]
  simp only [MGraph.mapV, Finset.image_empty]
  congr 1
  funext e
  split_ifs <;> rfl

/-- A vertex has the image of a vertex exactly when it is a vertex. -/
private theorem isVtx_mapV [DecidableEq V] {G : MGraph V E} {f : V → V} {p q : V}
    (hf : MergeMap f p q) (hp : p ∈ G.int) (hq : q ∈ G.int) (a : V) :
    (G.mapV f).IsVtx (f a) ↔ G.IsVtx a := by
  constructor
  · rintro (h | h) <;> obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 h <;>
      rcases hf b a hab with rfl | ⟨-, rfl | rfl⟩
    · exact Or.inl hb
    · exact Or.inl hp
    · exact Or.inl hq
    · exact Or.inr hb
    · exact Or.inl hp
    · exact Or.inl hq
  · rintro (h | h)
    · exact Or.inl (Finset.mem_image_of_mem f h)
    · exact Or.inr (Finset.mem_image_of_mem f h)

/-- Crossing edges of a saturated set and of its image. -/
private theorem crosses_mapV [DecidableEq V] {G : MGraph V E} {f : V → V} {p q : V}
    (hf : MergeMap f p q) (hp : p ∈ G.int) (hq : q ∈ G.int) {S : Finset V} (hS : Sat f S)
    (e : E) : (G.mapV f).Crosses (S.image f) e ↔ G.Crosses S e := by
  unfold MGraph.Crosses MGraph.Cut
  have h1 := isVtx_mapV (G := G) hf hp hq (G.ends e).1
  have h2 := isVtx_mapV (G := G) hf hp hq (G.ends e).2
  simp only [MGraph.mapV] at h1 h2 ⊢
  simp only [mem_image_sat hS]
  rw [h1, h2]

/-- Isolated subsets: a saturated set is isolated exactly when its image is. -/
private theorem iso_mapV [DecidableEq V] {G : MGraph V E} {f : V → V} {p q : V}
    (hf : MergeMap f p q) (hp : p ∈ G.int) (hq : q ∈ G.int) {S : Finset V} (hS : Sat f S)
    (hSi : S ⊆ G.int) : (G.mapV f).IsIsolated (S.image f) ↔ G.IsIsolated S := by
  unfold MGraph.IsIsolated
  simp only [crosses_mapV hf hp hq hS]
  exact ⟨fun ⟨_, h⟩ => ⟨hSi, h⟩, fun ⟨_, h⟩ => ⟨Finset.image_subset_image hSi, h⟩⟩

/-- The saturated preimage of a set of internal vertices of the graph with mapped vertices. -/
private def preim [DecidableEq V] (G : MGraph V E) (f : V → V) (Q : Finset V) : Finset V :=
  G.int.filter fun v => f v ∈ Q

/-- The saturated preimage of a set `Q` of internal vertices of the graph with mapped vertices:
its image is `Q`, and it is a saturated set of internal vertices. -/
private theorem preim_spec [DecidableEq V] {G : MGraph V E} {f : V → V} {p q : V}
    (hf : MergeMap f p q) (hp : p ∈ G.int) (hq : q ∈ G.int) {Q : Finset V}
    (hQ : Q ⊆ (G.mapV f).int) :
    (preim G f Q).image f = Q ∧ Sat f (preim G f Q) ∧ preim G f Q ⊆ G.int := by
  refine ⟨?_, ?_, Finset.filter_subset _ _⟩
  · ext v
    simp only [preim, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨-, ha⟩, rfl⟩; exact ha
    · intro hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hQ hv)
      exact ⟨a, ⟨ha, hv⟩, rfl⟩
  · intro a ha
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 ha
    obtain ⟨hbi, hbQ⟩ := Finset.mem_filter.1 hb
    refine Finset.mem_filter.2 ⟨?_, hab ▸ hbQ⟩
    rcases hf b a hab with rfl | ⟨-, rfl | rfl⟩
    · exact hbi
    · exact hp
    · exact hq

/-- The image of the saturated preimage of the image of a saturated set. -/
private theorem preim_image [DecidableEq V] {G : MGraph V E} {f : V → V} {S : Finset V}
    (hS : Sat f S) (hSi : S ⊆ G.int) : preim G f (S.image f) = S := by
  ext v
  simp only [preim, Finset.mem_filter, mem_image_sat hS]
  exact ⟨fun h => h.2, fun h => ⟨hSi h, h⟩⟩

/-- Inclusion of images of saturated sets. -/
private theorem image_subset_sat [DecidableEq V] {f : V → V} {S T : Finset V}
    (hT : Sat f T) : S.image f ⊆ T.image f ↔ S ⊆ T := by
  constructor
  · intro h a ha
    exact hT a (h (Finset.mem_image_of_mem f ha))
  · exact Finset.image_subset_image

/-- Strict inclusion of images of saturated sets. -/
private theorem image_ssubset_sat [DecidableEq V] {f : V → V} {S T : Finset V} (hS : Sat f S)
    (hT : Sat f T) : S.image f ⊂ T.image f ↔ S ⊂ T := by
  rw [Finset.ssubset_def, Finset.ssubset_def, image_subset_sat hT, image_subset_sat hS]

/-- The pre-deterministic property is kept under a map of vertices that does not identify an
internal vertex with any other vertex outside the internal vertices. -/
private theorem preDet_mapV [DecidableEq V] [DecidableEq E] {X : MGraph V E} (f : V → V)
    (hX : X.PreDet) (hf : ∀ a, f a ∈ X.int.image f → a ∈ X.int) : (X.mapV f).PreDet := by
  obtain ⟨hdc, l, hnd, hmem, hred⟩ := hX
  have hip : ∀ e, (X.mapV f).IsIntPlus e ↔ X.IsIntPlus e := by
    intro e
    simp only [MGraph.IsIntPlus, MGraph.mapV]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, hf _ h2, hf _ h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨h1, Finset.mem_image_of_mem f h2, Finset.mem_image_of_mem f h3⟩⟩
  refine ⟨dc_mapV f hdc, l, hnd, fun e => (hmem e).trans (hip e).symm, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hred j hj
  rw [mapV_convert]
  refine ⟨h1, dc_mapV f h2, ?_⟩
  rw [mapV_erase]
  exact dc_mapV f h3

/-! ## The components of the chain -/

/-- The ends of the crossing edges of `P (l + 1)`: internal, in the components `l` and `l + 1`. -/
private theorem Ctx.cc_lev [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G) {l : ℕ}
    (hl : l < C.k) {x : E} (hx : x = C.cc l ∨ x = C.cc' l) :
    (G.ends x).1 ∈ G.int ∧ (G.ends x).2 ∈ G.int ∧
      ((C.lev (G.ends x).1 = l ∧ C.lev (G.ends x).2 = l + 1) ∨
        (C.lev (G.ends x).1 = l + 1 ∧ C.lev (G.ends x).2 = l)) := by
  obtain ⟨w, hw, hlw, ho, hlo, hends⟩ := C.cc_ends l hl x hx
  rcases hends with h | h <;> rw [h]
  · exact ⟨ho, hw, Or.inl ⟨hlo, hlw⟩⟩
  · exact ⟨hw, ho, Or.inr ⟨hlw, hlo⟩⟩

/-- The graph of the component `l` of the chain, with `P (l + 1)` and its two external edges
replaced by one `Θ` edge carrying the index `cc l`. -/
private def Ctx.R [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G) (l : ℕ) :
    MGraph V E :=
  G.replace (C.P l) (C.P (l + 1)) (C.cc l) (C.cc' l)

/-- The internal vertices of the graph of the component `l`: the vertices of the component. -/
private theorem Ctx.R_int [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G) {l : ℕ}
    (hl : l < C.k) (v : V) : v ∈ (C.R l).int ↔ v ∈ G.int ∧ C.lev v = l := by
  change v ∈ C.P l \ C.P (l + 1) ↔ _
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    have hv := C.Psub l hl.le h1
    have a := (C.memP v hv l hl.le).1 h1
    have b := mt (C.memP v hv (l + 1) hl).2 h2
    exact ⟨hv, by omega⟩
  · rintro ⟨hv, rfl⟩
    exact ⟨(C.memP v hv _ hl.le).2 le_rfl, fun h => by
      have := (C.memP v hv _ hl).1 h; omega⟩

/-- The graph of the component `l < k` is pre-deterministic ([II, Def 5.9 (iii)]). -/
private theorem Ctx.R_preDet [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {l : ℕ} (hl : l < C.k) : (C.R l).PreDet :=
  C.spd.2.2.2 _ _ _ _ (chain_isoOrTop C.chain hl.le) (C.chain.2.1 l hl) (C.cc_ne l hl)
    ((C.cross l hl _).2 (Or.inl rfl)) ((C.cross l hl _).2 (Or.inr rfl))

/-- The edges of the graph of the component `l`. -/
private theorem Ctx.R_cls [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G) {l : ℕ}
    (hl : l < C.k) :
    (C.R l).ends (C.cc l) = (G.outer (C.P (l + 1)) (C.cc l), G.outer (C.P (l + 1)) (C.cc' l)) ∧
    (C.R l).cls (C.cc l) = some .diff ∧ (C.R l).cls (C.cc' l) = none ∧
    (∀ e, (C.R l).cls e ≠ none → e = C.cc l ∨ ((G.ends e).1 ∈ G.int ∧
      C.lev (G.ends e).1 = l ∧ (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).2 = l ∧
      (C.R l).cls e = G.cls e ∧ (C.R l).ends e = G.ends e)) ∧
    (∀ e, (G.ends e).1 ∈ G.int → C.lev (G.ends e).1 = l → (G.ends e).2 ∈ G.int →
      C.lev (G.ends e).2 = l → (C.R l).cls e = G.cls e ∧ (C.R l).ends e = G.ends e) := by
  have hne := C.cc_ne l hl
  have inside : ∀ e, ((G.ends e).1 ∈ C.P l \ C.P (l + 1) ∧ (G.ends e).2 ∈ C.P l \ C.P (l + 1) ↔
      (G.ends e).1 ∈ G.int ∧ C.lev (G.ends e).1 = l ∧ (G.ends e).2 ∈ G.int ∧
        C.lev (G.ends e).2 = l) := by
    intro e
    have h1 := C.R_int hl (G.ends e).1
    have h2 := C.R_int hl (G.ends e).2
    change _ ∈ C.P l \ C.P (l + 1) ↔ _ at h1 h2
    rw [h1, h2, and_assoc]
  have notcc : ∀ e, (G.ends e).1 ∈ G.int → C.lev (G.ends e).1 = l → (G.ends e).2 ∈ G.int →
      C.lev (G.ends e).2 = l → e ≠ C.cc l ∧ e ≠ C.cc' l := by
    intro e _ h1 _ h2
    constructor <;> rintro rfl
    · obtain ⟨-, -, h⟩ := C.cc_lev hl (Or.inl rfl); omega
    · obtain ⟨-, -, h⟩ := C.cc_lev hl (Or.inr rfl); omega
  have hcls : ∀ e, (C.R l).cls e = if e = C.cc l then some .diff else if e = C.cc' l then none
      else if (G.ends e).1 ∈ C.P l \ C.P (l + 1) ∧ (G.ends e).2 ∈ C.P l \ C.P (l + 1) then
        G.cls e else none := fun e => rfl
  have hends : ∀ e, e ≠ C.cc l → (C.R l).ends e = G.ends e := fun e h => by
    simp [Ctx.R, MGraph.replace, h]
  refine ⟨by simp [Ctx.R, MGraph.replace], by simp [Ctx.R, MGraph.replace],
    by simp [Ctx.R, MGraph.replace, hne.symm], fun e he => ?_, fun e h1 h2 h3 h4 => ?_⟩
  · by_cases he1 : e = C.cc l
    · exact Or.inl he1
    · right
      by_cases he2 : e = C.cc' l
      · subst he2; simp [Ctx.R, MGraph.replace, hne.symm] at he
      have hin : (G.ends e).1 ∈ C.P l \ C.P (l + 1) ∧ (G.ends e).2 ∈ C.P l \ C.P (l + 1) := by
        by_contra hn
        rw [hcls, ite_eq_right he1, ite_eq_right he2, ite_eq_right hn] at he
        exact he rfl
      obtain ⟨a, b, c, d⟩ := (inside e).1 hin
      refine ⟨a, b, c, d, ?_, hends e he1⟩
      rw [hcls, ite_eq_right he1, ite_eq_right he2, ite_eq_left hin]
  · obtain ⟨n1, n2⟩ := notcc e h1 h2 h3 h4
    have hin := (inside e).2 ⟨h1, h2, h3, h4⟩
    refine ⟨?_, hends e n1⟩
    rw [hcls, ite_eq_right n1, ite_eq_right n2, ite_eq_left hin]

/-- Connectivity in the graph `X` on the components `i, …, j`, from a component `c`: nets of the
graph `Y` of the component, of the subgraph induced on the components `i, …, c - 1` and of the
subgraph induced on the components `c + 1, …, j`, and extra crossing edges `Ex`, connect every
vertex of `X` to `Mi`, with the link between `Mi` and `Mj`. -/
private theorem center_conn [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {i j c : ℕ} {Mi Mj : V} (hjk : j ≤ C.k) (hic : i ≤ c) (hcj : c ≤ j)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    {X Y : MGraph V E}
    (hXint : ∀ v, v ∈ X.int ↔ v ∈ G.int ∧ i ≤ C.lev v ∧ C.lev v ≤ j)
    (hYint : ∀ v, v ∈ Y.int ↔ v ∈ G.int ∧ C.lev v = c)
    (hrest : ∀ e, G.cls e ≠ none → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int →
      i ≤ C.lev (G.ends e).1 → C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 →
      C.lev (G.ends e).2 ≤ j → C.lev (G.ends e).1 ≠ c → C.lev (G.ends e).2 ≠ c →
      X.ends e = G.ends e ∧ X.cls e ≠ none)
    (hcen : ∀ e, Y.cls e ≠ none → (c < j → e ≠ C.cc c) → X.ends e = Y.ends e ∧ X.cls e ≠ none)
    (hθ : c < j →
      Y.ends (C.cc c) = (G.outer (C.P (c + 1)) (C.cc c), G.outer (C.P (c + 1)) (C.cc' c)))
    (hXp : i < c → X.cls (C.cc (c - 1)) ≠ none ∧ X.ends (C.cc (c - 1)) = G.ends (C.cc (c - 1)))
    (hXc : c < j → X.cls (C.cc c) ≠ none ∧ X.ends (C.cc c) = G.ends (C.cc c) ∧
      X.cls (C.cc' c) ≠ none ∧ X.ends (C.cc' c) = G.ends (C.cc' c))
    {Nc NU ND Ex : Finset E} (hNc : Y.Spans Nc) (hNU : (G.induce (C.Lvl i c)).Spans NU)
    (hND : (G.induce (C.Lvl (c + 1) (j + 1))).Spans ND)
    (hθN : c < j → C.cc c ∈ Nc → C.cc' c ∈ Ex)
    (hatt : c = i ∨ c = j ∨ (c < j ∧ (C.cc c ∈ Nc ∨ C.cc c ∈ Ex ∨ C.cc' c ∈ Ex)) ∨
      (i < c ∧ C.cc (c - 1) ∈ Ex)) :
    ∀ u ∈ X.int, X.Rch (Nc ∪ NU ∪ ND ∪ Ex) Mi Mj u Mi := by
  set N := Nc ∪ NU ∪ ND ∪ Ex with hN
  have sNc : Nc ⊆ N := fun e h => by simp [hN, h]
  have sNU : NU ⊆ N := fun e h => by simp [hN, h]
  have sND : ND ⊆ N := fun e h => by simp [hN, h]
  have sEx : Ex ⊆ N := fun e h => by simp [hN, h]
  have hYX : ∀ v, v ∈ Y.int → v ∈ X.int := fun v hv => by
    obtain ⟨h1, h2⟩ := (hYint v).1 hv
    exact (hXint v).2 ⟨h1, by omega, by omega⟩
  -- a piece induced on the components `a, …, b - 1`
  have piece : ∀ a b (NP : Finset E), NP ⊆ N → i ≤ a → b ≤ j + 1 → (c < a ∨ b ≤ c) →
      (G.induce (C.Lvl a b)).Spans NP → ∀ u ∈ C.Lvl a b, ∀ v ∈ C.Lvl a b, X.Rch N Mi Mj u v := by
    intro a b NP hsub ha hb hab hsp u hu v hv
    refine rch_sim (X := G.induce (C.Lvl a b)) u (fun e he hc h1 h2 => ?_)
      (rch_of_spans u u hsp hu hv)
    have hin : (G.ends e).1 ∈ C.Lvl a b ∧ (G.ends e).2 ∈ C.Lvl a b := by
      by_contra hn; simp [MGraph.induce, hn] at hc
    have hcG : G.cls e ≠ none := by simpa [MGraph.induce, hin] using hc
    obtain ⟨a1, a2, a3⟩ := C.mem_Lvl.1 hin.1
    obtain ⟨b1, b2, b3⟩ := C.mem_Lvl.1 hin.2
    obtain ⟨he1, he2⟩ := hrest e hcG a1 b1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    change X.Rch N Mi Mj (G.ends e).1 (G.ends e).2
    rw [← he1]
    exact rch_edge (hsub he) he2 (by rw [he1]; exact (hXint _).2 ⟨a1, by omega, by omega⟩)
      (by rw [he1]; exact (hXint _).2 ⟨b1, by omega, by omega⟩)
  have hU : ∀ u ∈ C.Lvl i c, X.Rch N Mi Mj u Mi := by
    intro u hu
    obtain ⟨-, h1, h2⟩ := C.mem_Lvl.1 hu
    exact piece i c NU sNU le_rfl (by omega) (Or.inr le_rfl) hNU u hu Mi
      (C.mem_Lvl.2 ⟨hMi, by omega, by omega⟩)
  have hD : ∀ u ∈ C.Lvl (c + 1) (j + 1), X.Rch N Mi Mj u Mi := by
    intro u hu
    obtain ⟨-, h1, h2⟩ := C.mem_Lvl.1 hu
    exact rch_trans (piece (c + 1) (j + 1) ND sND (by omega) le_rfl (Or.inl (by omega)) hND u hu
      Mj (C.mem_Lvl.2 ⟨hMj, by omega, by omega⟩)) (rch_symm rch_link)
  -- a crossing edge of `P (l + 1)` joins its outer end to its end in the component `l + 1`
  have cross : ∀ l x, l < C.k → (x = C.cc l ∨ x = C.cc' l) → x ∈ N → X.cls x ≠ none →
      X.ends x = G.ends x → i ≤ l → l + 1 ≤ j → ∃ w, w ∈ G.int ∧ C.lev w = l + 1 ∧
        X.Rch N Mi Mj (G.outer (C.P (l + 1)) x) w ∧ G.outer (C.P (l + 1)) x ∈ G.int ∧
        C.lev (G.outer (C.P (l + 1)) x) = l := by
    intro l x hl hx hxN hxc hxe hil hlj
    obtain ⟨w, hw, hlw, ho, hlo, hends⟩ := C.cc_ends l hl x hx
    refine ⟨w, hw, hlw, rch_edge' hxN hxc (by rw [hxe]; exact hends)
      ((hXint _).2 ⟨ho, by omega, by omega⟩) ((hXint _).2 ⟨hw, by omega, by omega⟩), ho, hlo⟩
  -- the component `c`
  have hC : ∀ u ∈ Y.int, ∀ v ∈ Y.int, X.Rch N Mi Mj u v := by
    intro u hu v hv
    refine rch_sim (X := Y) u (fun e he hc h1 h2 => ?_) (rch_of_spans u u hNc hu hv)
    by_cases hθe : c < j ∧ e = C.cc c
    · obtain ⟨hcj', rfl⟩ := hθe
      rw [hθ hcj']
      obtain ⟨xc, xe, xc', xe'⟩ := hXc hcj'
      have hk : c < C.k := by omega
      obtain ⟨w, hw, hlw, hr, -⟩ := cross c (C.cc c) hk (Or.inl rfl) (sNc he) xc xe hic (by omega)
      obtain ⟨w', hw', hlw', hr', -⟩ := cross c (C.cc' c) hk (Or.inr rfl) (sEx (hθN hcj' he)) xc'
        xe' hic (by omega)
      have hwD := hD w (C.mem_Lvl.2 ⟨hw, by omega, by omega⟩)
      have hwD' := hD w' (C.mem_Lvl.2 ⟨hw', by omega, by omega⟩)
      exact rch_trans hr (rch_trans hwD (rch_symm (rch_trans hr' hwD')))
    · obtain ⟨he1, he2⟩ := hcen e hc (fun hcj' h => hθe ⟨hcj', h⟩)
      rw [← he1]
      exact rch_edge (sNc he) he2 (by rw [he1]; exact hYX _ h1) (by rw [he1]; exact hYX _ h2)
  -- the component `c` is attached to the others
  have hA : ∃ w ∈ Y.int, X.Rch N Mi Mj w Mi := by
    rcases hatt with rfl | rfl | ⟨hcj', h⟩ | ⟨hic', h⟩
    · exact ⟨Mi, (hYint Mi).2 ⟨hMi, hMi'⟩, Relation.ReflTransGen.refl⟩
    · exact ⟨Mj, (hYint Mj).2 ⟨hMj, hMj'⟩, rch_symm rch_link⟩
    · obtain ⟨xc, xe, xc', xe'⟩ := hXc hcj'
      have hk : c < C.k := by omega
      have key : ∀ x, (x = C.cc c ∨ x = C.cc' c) → x ∈ N → X.cls x ≠ none →
          X.ends x = G.ends x → ∃ w ∈ Y.int, X.Rch N Mi Mj w Mi := by
        intro x hx hxN hxc hxe
        obtain ⟨w, hw, hlw, hr, ho, hlo⟩ := cross c x hk hx hxN hxc hxe hic (by omega)
        exact ⟨_, (hYint _).2 ⟨ho, hlo⟩, rch_trans hr (hD w (C.mem_Lvl.2 ⟨hw, by omega, by omega⟩))⟩
      rcases h with h | h | h
      · exact key _ (Or.inl rfl) (sNc h) xc xe
      · exact key _ (Or.inl rfl) (sEx h) xc xe
      · exact key _ (Or.inr rfl) (sEx h) xc' xe'
    · obtain ⟨xc, xe⟩ := hXp hic'
      have hk : c - 1 < C.k := by omega
      obtain ⟨w, hw, hlw, hr, ho, hlo⟩ := cross (c - 1) _ hk (Or.inl rfl) (sEx h) xc xe (by omega)
        (by omega)
      exact ⟨w, (hYint w).2 ⟨hw, by omega⟩,
        rch_trans (rch_symm hr) (hU _ (C.mem_Lvl.2 ⟨ho, by omega, by omega⟩))⟩
  obtain ⟨w, hw, hwM⟩ := hA
  intro u hu
  obtain ⟨hu1, hu2, hu3⟩ := (hXint u).1 hu
  rcases lt_trichotomy (C.lev u) c with h | h | h
  · exact hU u (C.mem_Lvl.2 ⟨hu1, hu2, h⟩)
  · exact rch_trans (hC u ((hYint u).2 ⟨hu1, h⟩) w hw) hwM
  · exact hD u (C.mem_Lvl.2 ⟨hu1, by omega, by omega⟩)

/-- The subgraph induced on the components `a, …, b - 1` of the chain is doubly connected, also
when it is empty. -/
private theorem Ctx.dc_Lvl' [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    (a b : ℕ) : (G.induce (C.Lvl a b)).DC := by
  by_cases ha : a ≤ C.k
  · exact C.dc_Lvl b ha
  · have he : C.Lvl a b = ∅ := by
      ext v
      simp only [C.mem_Lvl, Finset.notMem_empty, iff_false, not_and]
      intro _ h; have := C.lev_le v; omega
    refine ⟨∅, ∅, disjoint_bot_left, by simp, by simp, ?_, ?_⟩ <;>
    · intro S hS ⟨v, hv⟩
      have := hS hv
      simp [MGraph.induce, he] at this

/-- A present edge of an induced subgraph has both ends in the set and its class in the graph. -/
private theorem induce_pres [DecidableEq V] {G : MGraph V E} {S : Finset V} {e : E}
    (h : (G.induce S).cls e ≠ none) :
    (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S ∧ (G.induce S).cls e = G.cls e := by
  by_cases hin : (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S
  · exact ⟨hin.1, hin.2, by simp [MGraph.induce, hin]⟩
  · exact absurd (by simp [MGraph.induce, hin]) h

/-- Disjointness of nets assembled from three regions of edges. -/
private theorem disj_regions [DecidableEq E] {R₀ R₁ R₂ : E → Prop} {A₂ B₂ A₀ B₀ A₁ B₁ Ea Eb :
    Finset E}
    (h₂ : ∀ e, e ∈ A₂ ∨ e ∈ B₂ ∨ e ∈ Ea ∨ e ∈ Eb → R₂ e) (h₀ : ∀ e, e ∈ A₀ ∨ e ∈ B₀ → R₀ e)
    (h₁ : ∀ e, e ∈ A₁ ∨ e ∈ B₁ → R₁ e) (x₀₁ : ∀ e, R₀ e → R₁ e → False)
    (x₀₂ : ∀ e, R₀ e → R₂ e → False) (x₁₂ : ∀ e, R₁ e → R₂ e → False)
    (d₂ : ∀ e, e ∈ A₂ ∨ e ∈ Ea → e ∈ B₂ ∨ e ∈ Eb → False) (d₀ : Disjoint A₀ B₀)
    (d₁ : Disjoint A₁ B₁) : Disjoint (A₂ ∪ A₀ ∪ A₁ ∪ Ea) (B₂ ∪ B₀ ∪ B₁ ∪ Eb) := by
  rw [Finset.disjoint_left]
  intro e ha hb
  simp only [Finset.mem_union] at ha hb
  rcases ha with ((ha | ha) | ha) | ha <;> rcases hb with ((hb | hb) | hb) | hb
  all_goals first
    | exact d₂ e (by tauto) (by tauto)
    | exact Finset.disjoint_left.1 d₀ ha hb
    | exact Finset.disjoint_left.1 d₁ ha hb
    | exact x₀₂ e (h₀ e (by tauto)) (h₂ e (by tauto))
    | exact x₁₂ e (h₁ e (by tauto)) (h₂ e (by tauto))
    | exact x₀₁ e (h₀ e (by tauto)) (h₁ e (by tauto))

/-- The step of [II, Lemma 5.11] at the component `c` of the chain: from the graph `Y` of
the component and the subgraphs induced on the other components, the graph `X` with the vertices
`Mi` and `Mj` identified is doubly connected. -/
private theorem center_step [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {f : V → V} {i j c : ℕ} {Mi Mj : V} (hjk : j ≤ C.k) (hic : i ≤ c) (hcj : c ≤ j)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hf : f Mi = f Mj) {X Y : MGraph V E}
    (hXint : ∀ v, v ∈ X.int ↔ v ∈ G.int ∧ i ≤ C.lev v ∧ C.lev v ≤ j)
    (hYint : ∀ v, v ∈ Y.int ↔ v ∈ G.int ∧ C.lev v = c) (hY : Y.DC)
    (hrest : ∀ e, G.cls e ≠ none → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int →
      i ≤ C.lev (G.ends e).1 → C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 →
      C.lev (G.ends e).2 ≤ j → C.lev (G.ends e).1 ≠ c → C.lev (G.ends e).2 ≠ c →
      X.ends e = G.ends e ∧ (X.cls e = G.cls e ∨ (G.cls e = some .plus ∧ X.cls e = some .diff)))
    (hcen : ∀ e, Y.cls e ≠ none → (c < j → e ≠ C.cc c) → X.ends e = Y.ends e ∧ X.cls e = Y.cls e)
    (hYpres : ∀ e, Y.cls e ≠ none → C.lev (G.ends e).1 = c ∨ C.lev (G.ends e).2 = c)
    (hθ : c < j →
      Y.ends (C.cc c) = (G.outer (C.P (c + 1)) (C.cc c), G.outer (C.P (c + 1)) (C.cc' c)))
    (hYc' : c < j → Y.cls (C.cc' c) = none) (hYp : i < c → Y.cls (C.cc (c - 1)) = none)
    (hXp : i < c → X.cls (C.cc (c - 1)) = some .diff ∧
      X.ends (C.cc (c - 1)) = G.ends (C.cc (c - 1)))
    (hXc : c < j → X.cls (C.cc c) = some .diff ∧ X.ends (C.cc c) = G.ends (C.cc c) ∧
      X.cls (C.cc' c) = some .diff ∧ X.ends (C.cc' c) = G.ends (C.cc' c)) :
    (X.mapV f).DC := by
  classical
  obtain ⟨Kc, Lc, hdc, hKc, hLc, hsKc, hsLc⟩ := hY
  obtain ⟨KU, LU, hdU, hKU, hLU, hsKU, hsLU⟩ := C.dc_Lvl' i c
  obtain ⟨KD, LD, hdD, hKD, hLD, hsKD, hsLD⟩ := C.dc_Lvl' (c + 1) (j + 1)
  have dne : (some MClass.diff) ≠ none := by simp
  -- presence and classes
  have hrest' : ∀ e, G.cls e ≠ none → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int →
      i ≤ C.lev (G.ends e).1 → C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 →
      C.lev (G.ends e).2 ≤ j → C.lev (G.ends e).1 ≠ c → C.lev (G.ends e).2 ≠ c →
      X.ends e = G.ends e ∧ X.cls e ≠ none := by
    intro e hc a b c' d e' f' g' h'
    obtain ⟨h1, h2⟩ := hrest e hc a b c' d e' f' g' h'
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | ⟨-, h2⟩ <;> rw [h2]
    · exact hc
    · exact dne
  have hcen' : ∀ e, Y.cls e ≠ none → (c < j → e ≠ C.cc c) → X.ends e = Y.ends e ∧ X.cls e ≠ none :=
    fun e hc h => ⟨(hcen e hc h).1, by rw [(hcen e hc h).2]; exact hc⟩
  have hXp' : i < c → X.cls (C.cc (c - 1)) ≠ none ∧ X.ends (C.cc (c - 1)) = G.ends (C.cc (c - 1)) :=
    fun h => ⟨by rw [(hXp h).1]; exact dne, (hXp h).2⟩
  have hXc' : c < j → X.cls (C.cc c) ≠ none ∧ X.ends (C.cc c) = G.ends (C.cc c) ∧
      X.cls (C.cc' c) ≠ none ∧ X.ends (C.cc' c) = G.ends (C.cc' c) := fun h =>
    ⟨by rw [(hXc h).1]; exact dne, (hXc h).2.1, by rw [(hXc h).2.2.1]; exact dne, (hXc h).2.2.2⟩
  have conn := fun (Nc NU ND Ex : Finset E) => center_conn (Ex := Ex) C hjk hic hcj hMi hMi' hMj
    hMj' hXint hYint hrest' hcen' hθ hXp' hXc' (Nc := Nc) (NU := NU) (ND := ND)
  -- the regions of the edges
  have rU : ∀ e, e ∈ KU ∨ e ∈ LU → (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧
      i ≤ C.lev (G.ends e).1 ∧ C.lev (G.ends e).1 < c ∧ i ≤ C.lev (G.ends e).2 ∧
      C.lev (G.ends e).2 < c ∧ G.cls e ≠ none ∧ (G.induce (C.Lvl i c)).cls e = G.cls e := by
    intro e he
    have hc : (G.induce (C.Lvl i c)).cls e ≠ none := by
      rcases he with he | he
      · rw [hKU e he]; exact dne
      · rcases hLU e he with h | h | h <;> rw [h] <;> simp
    obtain ⟨h1, h2, h3⟩ := induce_pres hc
    obtain ⟨a1, a2, a3⟩ := C.mem_Lvl.1 h1
    obtain ⟨b1, b2, b3⟩ := C.mem_Lvl.1 h2
    exact ⟨a1, b1, a2, a3, b2, b3, by rw [← h3]; exact hc, h3⟩
  have rD : ∀ e, e ∈ KD ∨ e ∈ LD → (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧
      c + 1 ≤ C.lev (G.ends e).1 ∧ C.lev (G.ends e).1 < j + 1 ∧ c + 1 ≤ C.lev (G.ends e).2 ∧
      C.lev (G.ends e).2 < j + 1 ∧ G.cls e ≠ none ∧
      (G.induce (C.Lvl (c + 1) (j + 1))).cls e = G.cls e := by
    intro e he
    have hc : (G.induce (C.Lvl (c + 1) (j + 1))).cls e ≠ none := by
      rcases he with he | he
      · rw [hKD e he]; exact dne
      · rcases hLD e he with h | h | h <;> rw [h] <;> simp
    obtain ⟨h1, h2, h3⟩ := induce_pres hc
    obtain ⟨a1, a2, a3⟩ := C.mem_Lvl.1 h1
    obtain ⟨b1, b2, b3⟩ := C.mem_Lvl.1 h2
    exact ⟨a1, b1, a2, a3, b2, b3, by rw [← h3]; exact hc, h3⟩
  -- classes of the pieces in `X`
  have cKU : ∀ e ∈ KU, X.cls e = some .diff := by
    intro e he
    obtain ⟨a1, b1, a2, a3, b2, b3, hc, h3⟩ := rU e (Or.inl he)
    have hG : G.cls e = some .diff := by rw [← h3]; exact hKU e he
    rcases (hrest e hc a1 b1 a2 (by omega) b2 (by omega) (by omega) (by omega)).2 with h | ⟨h, _⟩
    · rw [h, hG]
    · rw [hG] at h; exact absurd h (by simp)
  have cKD : ∀ e ∈ KD, X.cls e = some .diff := by
    intro e he
    obtain ⟨a1, b1, a2, a3, b2, b3, hc, h3⟩ := rD e (Or.inl he)
    have hG : G.cls e = some .diff := by rw [← h3]; exact hKD e he
    rcases (hrest e hc a1 b1 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).2 with h | ⟨h, _⟩
    · rw [h, hG]
    · rw [hG] at h; exact absurd h (by simp)
  have blue : ∀ e, (G.cls e = some .diff ∨ G.cls e = some .plus ∨ G.cls e = some .ghost) →
      (X.cls e = G.cls e ∨ (G.cls e = some .plus ∧ X.cls e = some .diff)) →
      (X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost) := by
    intro e hG h
    rcases h with h | ⟨-, h⟩
    · rw [h]; exact hG
    · exact Or.inl h
  have cLU : ∀ e ∈ LU, X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost := by
    intro e he
    obtain ⟨a1, b1, a2, a3, b2, b3, hc, h3⟩ := rU e (Or.inr he)
    exact blue e (by rw [← h3]; exact hLU e he)
      (hrest e hc a1 b1 a2 (by omega) b2 (by omega) (by omega) (by omega)).2
  have cLD : ∀ e ∈ LD, X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost := by
    intro e he
    obtain ⟨a1, b1, a2, a3, b2, b3, hc, h3⟩ := rD e (Or.inr he)
    exact blue e (by rw [← h3]; exact hLD e he)
      (hrest e hc a1 b1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).2
  have cKc : ∀ e ∈ Kc, X.cls e = some .diff := by
    intro e he
    by_cases h : c < j ∧ e = C.cc c
    · obtain ⟨h1, rfl⟩ := h; exact (hXc h1).1
    · rw [(hcen e (by rw [hKc e he]; exact dne) fun a b => h ⟨a, b⟩).2]; exact hKc e he
  have cLc : ∀ e ∈ Lc, X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost := by
    intro e he
    by_cases h : c < j ∧ e = C.cc c
    · obtain ⟨h1, rfl⟩ := h; exact Or.inl (hXc h1).1
    · rw [(hcen e (by rcases hLc e he with h' | h' | h' <;> rw [h'] <;> simp)
        fun a b => h ⟨a, b⟩).2]
      exact hLc e he
  have pKc : ∀ e ∈ Kc, Y.cls e ≠ none := fun e he => by rw [hKc e he]; exact dne
  have pLc : ∀ e ∈ Lc, Y.cls e ≠ none := fun e he => by
    rcases hLc e he with h | h | h <;> rw [h] <;> simp
  -- the regions
  let R₂ : E → Prop := fun e => C.lev (G.ends e).1 = c ∨ C.lev (G.ends e).2 = c
  let R₀ : E → Prop := fun e => C.lev (G.ends e).1 < c ∧ C.lev (G.ends e).2 < c
  let R₁ : E → Prop := fun e => c < C.lev (G.ends e).1 ∧ c < C.lev (G.ends e).2
  have h₀ : ∀ e, e ∈ KU ∨ e ∈ LU → R₀ e := fun e he => by
    obtain ⟨-, -, -, a, -, b, -⟩ := rU e he; exact ⟨a, b⟩
  have h₁ : ∀ e, e ∈ KD ∨ e ∈ LD → R₁ e := fun e he => by
    obtain ⟨-, -, a, -, b, -⟩ := rD e he; exact ⟨by omega, by omega⟩
  have x₀₁ : ∀ e, R₀ e → R₁ e → False := fun e a b => by simp only [R₀, R₁] at a b; omega
  have x₀₂ : ∀ e, R₀ e → R₂ e → False := fun e a b => by simp only [R₀, R₂] at a b; omega
  have x₁₂ : ∀ e, R₁ e → R₂ e → False := fun e a b => by simp only [R₁, R₂] at a b; omega
  have r₂ : ∀ l x, l < C.k → (x = C.cc l ∨ x = C.cc' l) → (l = c ∨ l + 1 = c) → R₂ x := by
    intro l x hl hx hlc
    obtain ⟨-, -, h⟩ := C.cc_lev hl hx
    simp only [R₂]; omega
  have rc : ∀ e, e ∈ Kc ∨ e ∈ Lc → R₂ e := fun e he => by
    rcases he with he | he
    · exact hYpres e (pKc e he)
    · exact hYpres e (pLc e he)
  have fin := fun (ExK ExL : Finset E) (hd : Disjoint (Kc ∪ KU ∪ KD ∪ ExK) (Lc ∪ LU ∪ LD ∪ ExL))
      (cK : ∀ e ∈ ExK, X.cls e = some .diff) (cL : ∀ e ∈ ExL, X.cls e = some .diff)
      (sK : ∀ u ∈ X.int, X.Rch (Kc ∪ KU ∪ KD ∪ ExK) Mi Mj u Mi)
      (sL : ∀ u ∈ X.int, X.Rch (Lc ∪ LU ∪ LD ∪ ExL) Mi Mj u Mi) =>
    dc_mapV_of (X := X) f hf _ _ hd
      (fun e he => by
        simp only [Finset.mem_union] at he
        rcases he with ((he | he) | he) | he
        · exact cKc e he
        · exact cKU e he
        · exact cKD e he
        · exact cK e he)
      (fun e he => by
        simp only [Finset.mem_union] at he
        rcases he with ((he | he) | he) | he
        · exact cLc e he
        · exact cLU e he
        · exact cLD e he
        · exact Or.inl (cL e he)) sK sL
  rcases Nat.lt_or_ge c j with hcj' | hcj'
  · obtain ⟨xc, -, xc', -⟩ := hXc hcj'
    have hk : c < C.k := by omega
    have ne' := C.cc_ne c hk
    -- the crossing edge of `P c` on the side of `Mi`
    let Ep : Finset E := if i < c then {C.cc (c - 1)} else ∅
    have mEp : ∀ e ∈ Ep, i < c ∧ e = C.cc (c - 1) := by
      intro e he
      by_cases h : i < c
      · simp only [Ep, h, ↓reduceIte, Finset.mem_singleton] at he; exact ⟨h, he⟩
      · simp [Ep, h] at he
    have cEp : ∀ e ∈ Ep, X.cls e = some .diff := fun e he => by
      obtain ⟨h, rfl⟩ := mEp e he; exact (hXp h).1
    have attEp : c = i ∨ (i < c ∧ C.cc (c - 1) ∈ Ep) := by
      by_cases h : i < c
      · exact Or.inr ⟨h, by simp [Ep, h]⟩
      · exact Or.inl (by omega)
    have rEp : ∀ e ∈ Ep, R₂ e := fun e he => by
      obtain ⟨h, rfl⟩ := mEp e he; exact r₂ (c - 1) _ (by omega) (Or.inl rfl) (Or.inr (by omega))
    have Epc : ∀ e ∈ Ep, e ∉ Kc ∧ e ∉ Lc := fun e he => by
      obtain ⟨h, rfl⟩ := mEp e he
      exact ⟨fun h' => pKc _ h' (hYp h), fun h' => pLc _ h' (hYp h)⟩
    have Epc' : C.cc' c ∉ Ep := fun h => by
      obtain ⟨h1, h2⟩ := mEp _ h
      obtain ⟨-, -, a⟩ := C.cc_lev hk (Or.inr rfl)
      obtain ⟨-, -, b⟩ := C.cc_lev (l := c - 1) (by omega) (Or.inl rfl)
      rw [h2] at a; omega
    have c'K : C.cc' c ∉ Kc := fun h => pKc _ h (hYc' hcj')
    have c'L : C.cc' c ∉ Lc := fun h => pLc _ h (hYc' hcj')
    by_cases hθK : C.cc c ∈ Kc
    · have hθL : C.cc c ∉ Lc := fun h => Finset.disjoint_left.1 hdc hθK h
      refine fin {C.cc' c} Ep ?_ (fun e he => by rw [Finset.mem_singleton.1 he]; exact xc') cEp
        (conn Kc KU KD {C.cc' c} hsKc hsKU hsKD (fun _ _ => Finset.mem_singleton_self _)
          (Or.inr (Or.inr (Or.inl ⟨hcj', Or.inl hθK⟩))))
        (conn Lc LU LD Ep hsLc hsLU hsLD (fun _ h => absurd h hθL) (attEp.elim Or.inl fun h =>
            Or.inr (Or.inr (Or.inr h))))
      refine disj_regions (R₀ := R₀) (R₁ := R₁) (R₂ := R₂) (fun e he => ?_) h₀ h₁ x₀₁ x₀₂ x₁₂
        (fun e ha hb => ?_) hdU hdD
      · rcases he with he | he | he | he
        · exact rc e (Or.inl he)
        · exact rc e (Or.inr he)
        · rw [Finset.mem_singleton.1 he]; exact r₂ c _ hk (Or.inr rfl) (Or.inl rfl)
        · exact rEp e he
      · rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Finset.disjoint_left.1 hdc ha hb
        · exact (Epc e hb).1 ha
        · rw [Finset.mem_singleton.1 ha] at hb; exact c'L hb
        · rw [Finset.mem_singleton.1 ha] at hb; exact Epc' hb
    by_cases hθL : C.cc c ∈ Lc
    · refine fin Ep {C.cc' c} ?_ cEp (fun e he => by rw [Finset.mem_singleton.1 he]; exact xc')
        (conn Kc KU KD Ep hsKc hsKU hsKD (fun _ h => absurd h hθK) (attEp.elim Or.inl fun h =>
            Or.inr (Or.inr (Or.inr h))))
        (conn Lc LU LD {C.cc' c} hsLc hsLU hsLD (fun _ _ => Finset.mem_singleton_self _)
          (Or.inr (Or.inr (Or.inl ⟨hcj', Or.inl hθL⟩))))
      refine disj_regions (R₀ := R₀) (R₁ := R₁) (R₂ := R₂) (fun e he => ?_) h₀ h₁ x₀₁ x₀₂ x₁₂
        (fun e ha hb => ?_) hdU hdD
      · rcases he with he | he | he | he
        · exact rc e (Or.inl he)
        · exact rc e (Or.inr he)
        · exact rEp e he
        · rw [Finset.mem_singleton.1 he]; exact r₂ c _ hk (Or.inr rfl) (Or.inl rfl)
      · rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Finset.disjoint_left.1 hdc ha hb
        · rw [Finset.mem_singleton.1 hb] at ha; exact c'K ha
        · exact (Epc e ha).2 hb
        · rw [Finset.mem_singleton.1 hb] at ha; exact Epc' ha
    · refine fin {C.cc c} {C.cc' c} ?_ (fun e he => by rw [Finset.mem_singleton.1 he]; exact xc)
        (fun e he => by rw [Finset.mem_singleton.1 he]; exact xc')
        (conn Kc KU KD {C.cc c} hsKc hsKU hsKD (fun _ h => absurd h hθK)
          (Or.inr (Or.inr (Or.inl ⟨hcj', Or.inr (Or.inl (Finset.mem_singleton_self _))⟩))))
        (conn Lc LU LD {C.cc' c} hsLc hsLU hsLD (fun _ h => absurd h hθL)
          (Or.inr (Or.inr (Or.inl ⟨hcj', Or.inr (Or.inr (Finset.mem_singleton_self _))⟩))))
      refine disj_regions (R₀ := R₀) (R₁ := R₁) (R₂ := R₂) (fun e he => ?_) h₀ h₁ x₀₁ x₀₂ x₁₂
        (fun e ha hb => ?_) hdU hdD
      · rcases he with he | he | he | he
        · exact rc e (Or.inl he)
        · exact rc e (Or.inr he)
        · rw [Finset.mem_singleton.1 he]; exact r₂ c _ hk (Or.inl rfl) (Or.inl rfl)
        · rw [Finset.mem_singleton.1 he]; exact r₂ c _ hk (Or.inr rfl) (Or.inl rfl)
      · rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Finset.disjoint_left.1 hdc ha hb
        · rw [Finset.mem_singleton.1 hb] at ha; exact c'K ha
        · rw [Finset.mem_singleton.1 ha] at hb; exact hθL hb
        · rw [Finset.mem_singleton.1 ha, Finset.mem_singleton] at hb; exact ne' hb
  · have hcj2 : c = j := le_antisymm hcj hcj'
    refine fin ∅ ∅ ?_ (by simp) (by simp)
      (conn Kc KU KD ∅ hsKc hsKU hsKD (fun h => absurd h (by omega))
        (Or.inr (Or.inl hcj2)))
      (conn Lc LU LD ∅ hsLc hsLU hsLD (fun h => absurd h (by omega))
        (Or.inr (Or.inl hcj2)))
    refine disj_regions (R₀ := R₀) (R₁ := R₁) (R₂ := R₂) (fun e he => ?_) h₀ h₁ x₀₁ x₀₂ x₁₂
      (fun e ha hb => ?_) hdU hdD
    · rcases he with he | he | he | he
      · exact rc e (Or.inl he)
      · exact rc e (Or.inr he)
      · simp at he
      · simp at he
    · rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Finset.disjoint_left.1 hdc ha hb
      all_goals simp at *

/-! ## The pre-deterministic order of [II, Lemma 5.11] -/

/-- The graph `X` is `W` with some blue solid edges changed into `Θ` edges and some edges
removed. -/
private def Wk (W X : MGraph V E) : Prop :=
  X.int = W.int ∧ X.ends = W.ends ∧
    ∀ e, X.cls e = none ∨ X.cls e = W.cls e ∨ (W.cls e = some .plus ∧ X.cls e = some .diff)

/-- A graph is obtained from itself. -/
private theorem wk_refl (W : MGraph V E) : Wk W W := ⟨rfl, rfl, fun _ => Or.inr (Or.inl rfl)⟩

/-- Changing blue solid edges into `Θ` edges. -/
private theorem wk_convert [DecidableEq E] (W : MGraph V E) (l : List E) : Wk W (W.convert l) := by
  refine ⟨rfl, rfl, fun e => ?_⟩
  by_cases h : e ∈ l ∧ W.cls e = some .plus
  · exact Or.inr (Or.inr ⟨h.2, by simp [MGraph.convert, h]⟩)
  · exact Or.inr (Or.inl (by simp [MGraph.convert, h]))

/-- Changing blue solid edges into `Θ` edges and removing an edge. -/
private theorem wk_convert_erase [DecidableEq E] (W : MGraph V E) (l : List E) (x : E) :
    Wk W ((W.convert l).erase x) := by
  obtain ⟨-, -, h⟩ := wk_convert W l
  refine ⟨rfl, rfl, fun e => ?_⟩
  by_cases hx : e = x
  · subst hx; exact Or.inl (by simp [MGraph.erase])
  · have : ((W.convert l).erase x).cls e = (W.convert l).cls e := by simp [MGraph.erase, hx]
    rw [this]; exact h e

/-- The step of [II, Lemma 5.11] at the component `c`, for graphs `X` and `Y` obtained from the
graph `Z` on the components `i, …, j` and from the graph `R` of the component by changing blue
solid edges into `Θ` edges and removing edges. -/
private theorem center_wrap [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {f : V → V} {i j c : ℕ} {Mi Mj : V} (hjk : j ≤ C.k) (hic : i ≤ c) (hcj : c ≤ j)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hf : f Mi = f Mj) {Z R X Y : MGraph V E}
    (hZint : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ i ≤ C.lev v ∧ C.lev v ≤ j)
    (hZG : ∀ e, (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int → i ≤ C.lev (G.ends e).1 →
      C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 → C.lev (G.ends e).2 ≤ j →
      Z.ends e = G.ends e ∧ Z.cls e = G.cls e)
    (hRint : ∀ v, v ∈ R.int ↔ v ∈ G.int ∧ C.lev v = c)
    (hRpres : ∀ e, R.cls e ≠ none → ((G.ends e).1 ∈ G.int ∧ C.lev (G.ends e).1 = c ∧
      (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).2 = c ∧ R.cls e = G.cls e ∧ R.ends e = G.ends e) ∨
      (c < j ∧ e = C.cc c) ∨ (Z.ends e = R.ends e ∧ Z.cls e = some .diff ∧
        R.cls e = some .diff ∧ (C.lev (G.ends e).1 = c ∨ C.lev (G.ends e).2 = c) ∧
        (j < C.lev (G.ends e).1 ∨ j < C.lev (G.ends e).2)))
    (hRθ : c < j →
      R.ends (C.cc c) = (G.outer (C.P (c + 1)) (C.cc c), G.outer (C.P (c + 1)) (C.cc' c)))
    (hRc' : c < j → R.cls (C.cc' c) = none) (hRp : i < c → R.cls (C.cc (c - 1)) = none)
    (hX : Wk Z X) (hY : Wk R Y) (hYdc : Y.DC)
    (hXer : ∀ e, X.cls e = none → Z.cls e ≠ none →
      (C.lev (G.ends e).1 = c ∧ C.lev (G.ends e).2 = c) ∨ (i < c ∧ e = C.cc' (c - 1)))
    (hmatch : ∀ e, (G.ends e).1 ∈ G.int → C.lev (G.ends e).1 = c → (G.ends e).2 ∈ G.int →
      C.lev (G.ends e).2 = c → G.cls e ≠ none → X.cls e = Y.cls e)
    (hXc' : c < j → X.cls (C.cc' c) = some .diff) : (X.mapV f).DC := by
  obtain ⟨hXi, hXe, hXc⟩ := hX
  obtain ⟨hYi, hYe, hYc⟩ := hY
  have dne : (some MClass.diff) ≠ none := by simp
  have Ypres : ∀ e, Y.cls e ≠ none → R.cls e ≠ none := by
    intro e h hR
    rcases hYc e with h' | h' | ⟨h', -⟩
    · exact h h'
    · exact h (h'.trans hR)
    · rw [hR] at h'; exact absurd h' (by simp)
  have Ynone : ∀ e, R.cls e = none → Y.cls e = none := fun e h => by
    by_contra h'; exact Ypres e h' h
  -- the class in `X` of a present edge of `Z` that is not removed
  have Xkeep : ∀ e, Z.cls e ≠ none → ¬ (C.lev (G.ends e).1 = c ∧ C.lev (G.ends e).2 = c) →
      ¬ (i < c ∧ e = C.cc' (c - 1)) →
      X.cls e = Z.cls e ∨ (Z.cls e = some .plus ∧ X.cls e = some .diff) := by
    intro e hz h1 h2
    rcases hXc e with h | h | h
    · rcases hXer e h hz with h' | h'
      · exact absurd h' h1
      · exact absurd h' h2
    · exact Or.inl h
    · exact Or.inr h
  have ccl := fun l (hl : l < C.k) x (hx : x = C.cc l ∨ x = C.cc' l) => C.cc_lev hl hx
  refine center_step C (f := f) hjk hic hcj hMi hMi' hMj hMj' hf
    (fun v => by rw [hXi]; exact hZint v)
    (fun v => by rw [hYi]; exact hRint v) hYdc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro e hc h1 h2 a1 a2 b1 b2 n1 n2
    obtain ⟨hze, hzc⟩ := hZG e h1 h2 a1 a2 b1 b2
    refine ⟨by rw [hXe]; exact hze, ?_⟩
    rw [← hzc]
    refine Xkeep e (by rw [hzc]; exact hc) (fun h => n1 h.1) ?_
    rintro ⟨hic', rfl⟩
    obtain ⟨-, -, h⟩ := ccl (c - 1) (by omega) _ (Or.inr rfl)
    omega
  · intro e hc hne
    have hR := Ypres e hc
    rcases hRpres e hR with ⟨a1, a2, b1, b2, hrc, hre⟩ | ⟨hcj', rfl⟩ | ⟨hze, hzc, hrc, -, hj⟩
    · have hG : G.cls e ≠ none := by rw [← hrc]; exact hR
      obtain ⟨hze, -⟩ := hZG e a1 b1 (by omega) (by omega) (by omega) (by omega)
      exact ⟨by rw [hXe, hYe, hze, hre], hmatch e a1 a2 b1 b2 hG⟩
    · exact absurd rfl (hne hcj')
    · refine ⟨by rw [hXe, hYe, hze], ?_⟩
      have hx : X.cls e = some .diff := by
        rcases Xkeep e (by rw [hzc]; exact dne) (by omega) (fun ⟨_, h⟩ => by
          subst h; obtain ⟨-, -, h⟩ := ccl (c - 1) (by omega) _ (Or.inr rfl); omega) with h | h
        · rw [h, hzc]
        · exact h.2
      have hy : Y.cls e = some .diff := by
        rcases hYc e with h | h | h
        · exact absurd h hc
        · rw [h, hrc]
        · exact h.2
      rw [hx, hy]
  · intro e hc
    rcases hRpres e (Ypres e hc) with ⟨-, a, -⟩ | ⟨hcj', rfl⟩ | ⟨-, -, -, h, -⟩
    · exact Or.inl a
    · obtain ⟨-, -, h⟩ := ccl c (by omega) _ (Or.inl rfl); omega
    · exact h
  · intro h; rw [hYe]; exact hRθ h
  · intro h; exact Ynone _ (hRc' h)
  · intro h; exact Ynone _ (hRp h)
  · intro hic'
    obtain ⟨g1, g2, g3⟩ := ccl (c - 1) (by omega) _ (Or.inl rfl)
    obtain ⟨hze, hzc⟩ := hZG _ g1 g2 (by omega) (by omega) (by omega) (by omega)
    have hzd : Z.cls (C.cc (c - 1)) = some .diff := by rw [hzc]; exact C.cc_diff _ (by omega)
    refine ⟨?_, by rw [hXe]; exact hze⟩
    rcases Xkeep _ (by rw [hzd]; exact dne) (by omega)
      (fun ⟨_, h⟩ => C.cc_ne (c - 1) (by omega) h) with h | h
    · rw [h, hzd]
    · exact h.2
  · intro hcj'
    obtain ⟨g1, g2, g3⟩ := ccl c (by omega) _ (Or.inl rfl)
    obtain ⟨hze, hzc⟩ := hZG _ g1 g2 (by omega) (by omega) (by omega) (by omega)
    obtain ⟨g1', g2', g3'⟩ := ccl c (by omega) _ (Or.inr rfl)
    obtain ⟨hze', -⟩ := hZG _ g1' g2' (by omega) (by omega) (by omega) (by omega)
    have hzd : Z.cls (C.cc c) = some .diff := by rw [hzc]; exact C.cc_diff _ (by omega)
    refine ⟨?_, by rw [hXe]; exact hze, hXc' hcj', by rw [hXe]; exact hze'⟩
    have hn : ¬ (i < c ∧ C.cc c = C.cc' (c - 1)) := by
      rintro ⟨hic', h⟩
      obtain ⟨-, -, h'⟩ := ccl (c - 1) (by omega) _ (Or.inr rfl)
      rw [← h] at h'; omega
    rcases Xkeep (C.cc c) (by rw [hzd]; exact dne) (by omega) hn with h | h
    · rw [h, hzd]
    · exact h.2

/-- An entry of a list without repetition is not among the entries before it. -/
private theorem getElem_notMem_take {α : Type} {l : List α} (h : l.Nodup) {t : ℕ}
    (ht : t < l.length) : l[t] ∉ l.take t := by
  intro hm
  have h' := List.take_append_drop t l
  rw [← h', List.nodup_append] at h
  exact h.2.2 _ hm _ (by rw [List.drop_eq_getElem_cons ht]; exact List.mem_cons_self) rfl

/-- The classes after changing blue solid edges into `Θ` edges and removing an edge. -/
private theorem ce_cls [DecidableEq E] (W : MGraph V E) (l : List E) (x e : E) :
    ((W.convert l).erase x).cls e = if e = x then none else
      if e ∈ l ∧ W.cls e = some .plus then some .diff else W.cls e := by
  by_cases h : e = x
  · subst h; simp [MGraph.erase]
  · simp [MGraph.erase, MGraph.convert, h]

/-- The classes after changing blue solid edges into `Θ` edges. -/
private theorem c_cls [DecidableEq E] (W : MGraph V E) (l : List E) (e : E) :
    (W.convert l).cls e = if e ∈ l ∧ W.cls e = some .plus then some .diff else W.cls e := rfl

/-- Only the removed edge of a present edge becomes absent. -/
private theorem ce_none [DecidableEq E] (W : MGraph V E) (l : List E) (x e : E)
    (h : ((W.convert l).erase x).cls e = none) (hW : W.cls e ≠ none) : e = x := by
  rw [ce_cls] at h
  by_contra hx
  rw [ite_eq_right hx] at h
  split_ifs at h with h'
  exact hW h

/-- The order of [II, Lemma 5.11]: the order of the component `j`, then, for
`m = j - 1, …, j - d`, the crossing edge `cc' m` if it is a blue solid edge, and the order of the
component `m`. -/
private def ordList (ℓ J : ℕ → List E) (j : ℕ) : ℕ → List E
  | 0 => ℓ j
  | d + 1 => ordList ℓ J j d ++ (J (j - (d + 1)) ++ ℓ (j - (d + 1)))

/-- The graph of the component `c` and its blue solid edges: the internal blue solid edges of
`C.R c` are the blue solid edges with both ends in the component `c`. -/
private theorem Ctx.R_intPlus [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {c : ℕ} (hc : c < C.k) (e : E) : (C.R c).IsIntPlus e ↔ G.cls e = some .plus ∧
      (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).1 = c ∧
      C.lev (G.ends e).2 = c := by
  obtain ⟨-, hd, -, hpres, hin⟩ := C.R_cls hc
  constructor
  · rintro ⟨h1, -, -⟩
    rcases hpres e (by rw [h1]; simp) with rfl | ⟨a1, a2, b1, b2, hrc, -⟩
    · rw [hd] at h1; exact absurd h1 (by simp)
    · exact ⟨by rw [← hrc]; exact h1, a1, b1, a2, b2⟩
  · rintro ⟨h1, a1, b1, a2, b2⟩
    obtain ⟨hrc, hre⟩ := hin e a1 a2 b1 b2
    refine ⟨by rw [hrc]; exact h1, ?_, ?_⟩ <;> rw [hre, C.R_int hc]
    · exact ⟨a1, a2⟩
    · exact ⟨b1, b2⟩

/-- The crossing edge `cc (c - 1)` is absent from the graph of the component `c`. -/
private theorem Ctx.R_prev [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {c : ℕ} (hc : c < C.k) (h0 : 0 < c) : (C.R c).cls (C.cc (c - 1)) = none := by
  obtain ⟨-, -, -, hpres, -⟩ := C.R_cls hc
  by_contra h
  obtain ⟨-, -, hl⟩ := C.cc_lev (l := c - 1) (by omega) (Or.inl rfl)
  rcases hpres _ h with h' | ⟨-, a, -, b, -⟩
  · obtain ⟨-, -, hl'⟩ := C.cc_lev hc (Or.inl rfl)
    rw [h'] at hl; omega
  · omega

/-- **The pre-deterministic order of [II, Lemma 5.11]**: in the setting of a chain with the
components `i < j`, a graph `Z` on the components `i, …, j` that agrees with `G` inside them,
with the bottom graph `Rb` of the component `j`, gives a pre-deterministic graph once `Mi` and
`Mj` are identified. -/
private theorem merge_core [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {f : V → V} {i j : ℕ} {Mi Mj : V} (hij : i < j) (hjk : j ≤ C.k)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hf : MergeMap f Mi Mj) (hfe : f Mi = f Mj) {Z Rb : MGraph V E}
    (hZint : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ i ≤ C.lev v ∧ C.lev v ≤ j)
    (hZG : ∀ e, (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int → i ≤ C.lev (G.ends e).1 →
      C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 → C.lev (G.ends e).2 ≤ j →
      Z.ends e = G.ends e ∧ Z.cls e = G.cls e)
    (hZp : ∀ e, Z.cls e = some .plus → (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧
      i ≤ C.lev (G.ends e).1 ∧ C.lev (G.ends e).1 ≤ j ∧ i ≤ C.lev (G.ends e).2 ∧
      C.lev (G.ends e).2 ≤ j)
    (hRint : ∀ v, v ∈ Rb.int ↔ v ∈ G.int ∧ C.lev v = j) (hRpd : Rb.PreDet)
    (hRpres : ∀ e, Rb.cls e ≠ none → ((G.ends e).1 ∈ G.int ∧ C.lev (G.ends e).1 = j ∧
      (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).2 = j ∧ Rb.cls e = G.cls e ∧
      Rb.ends e = G.ends e) ∨ (Z.ends e = Rb.ends e ∧ Z.cls e = some .diff ∧
        Rb.cls e = some .diff ∧ (C.lev (G.ends e).1 = j ∨ C.lev (G.ends e).2 = j) ∧
        (j < C.lev (G.ends e).1 ∨ j < C.lev (G.ends e).2)))
    (hRG : ∀ e, (G.ends e).1 ∈ G.int → C.lev (G.ends e).1 = j → (G.ends e).2 ∈ G.int →
      C.lev (G.ends e).2 = j → Rb.cls e = G.cls e ∧ Rb.ends e = G.ends e) :
    (Z.mapV f).PreDet := by
  classical
  have dne : (some MClass.diff) ≠ none := by simp
  have pne : (some MClass.plus) ≠ none := by simp
  -- the orders of the components
  have hpd : ∀ l, ∃ o : List E, (l < j → (C.R l).IsPDOrder o) ∧ (l = j → Rb.IsPDOrder o) := by
    intro l
    by_cases hl : l < j
    · obtain ⟨-, o, ho⟩ := C.R_preDet (l := l) (by omega)
      exact ⟨o, fun _ => ho, fun h => by omega⟩
    · by_cases hlj : l = j
      · obtain ⟨-, o, ho⟩ := hRpd
        exact ⟨o, fun h => by omega, fun _ => ho⟩
      · exact ⟨[], fun h => absurd h hl, fun h => absurd h hlj⟩
  choose ℓ hℓ using hpd
  let J : ℕ → List E := fun l => if G.cls (C.cc' l) = some .plus then [C.cc' l] else []
  have hJ : ∀ l e, e ∈ J l ↔ e = C.cc' l ∧ G.cls (C.cc' l) = some .plus := by
    intro l e
    by_cases h : G.cls (C.cc' l) = some .plus <;> simp [J, h]
  -- the facts of the bottom graph in the form of the step
  have hRpres' : ∀ e, Rb.cls e ≠ none → ((G.ends e).1 ∈ G.int ∧ C.lev (G.ends e).1 = j ∧
      (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).2 = j ∧ Rb.cls e = G.cls e ∧
      Rb.ends e = G.ends e) ∨ (j < j ∧ e = C.cc j) ∨ (Z.ends e = Rb.ends e ∧
        Z.cls e = some .diff ∧ Rb.cls e = some .diff ∧
        (C.lev (G.ends e).1 = j ∨ C.lev (G.ends e).2 = j) ∧
        (j < C.lev (G.ends e).1 ∨ j < C.lev (G.ends e).2)) := fun e h =>
    (hRpres e h).elim Or.inl fun h => Or.inr (Or.inr h)
  have hRp : i < j → Rb.cls (C.cc (j - 1)) = none := by
    intro hij'
    by_contra h
    obtain ⟨-, -, hl⟩ := C.cc_lev (l := j - 1) (by omega) (Or.inl rfl)
    rcases hRpres _ h with ⟨-, a, -, b, -⟩ | ⟨-, -, -, -, h'⟩ <;> omega
  -- the components `c < j`
  have Rmid : ∀ c, i ≤ c → c < j → (∀ v, v ∈ (C.R c).int ↔ v ∈ G.int ∧ C.lev v = c) ∧
      (∀ e, (C.R c).cls e ≠ none → ((G.ends e).1 ∈ G.int ∧ C.lev (G.ends e).1 = c ∧
        (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).2 = c ∧ (C.R c).cls e = G.cls e ∧
        (C.R c).ends e = G.ends e) ∨ (c < j ∧ e = C.cc c) ∨ (Z.ends e = (C.R c).ends e ∧
          Z.cls e = some .diff ∧ (C.R c).cls e = some .diff ∧
          (C.lev (G.ends e).1 = c ∨ C.lev (G.ends e).2 = c) ∧
          (j < C.lev (G.ends e).1 ∨ j < C.lev (G.ends e).2))) ∧
      (c < j → (C.R c).ends (C.cc c) =
        (G.outer (C.P (c + 1)) (C.cc c), G.outer (C.P (c + 1)) (C.cc' c))) ∧
      (c < j → (C.R c).cls (C.cc' c) = none) ∧ (i < c → (C.R c).cls (C.cc (c - 1)) = none) := by
    intro c hic hcj
    have hc : c < C.k := by omega
    obtain ⟨hθ, -, hc', hpres, -⟩ := C.R_cls hc
    refine ⟨C.R_int hc, fun e he => ?_, fun _ => hθ, fun _ => hc', fun h => C.R_prev hc (by omega)⟩
    rcases hpres e he with h | h
    · exact Or.inr (Or.inl ⟨hcj, h⟩)
    · exact Or.inl h
  -- membership in the components
  have hZcls : ∀ e, (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int → i ≤ C.lev (G.ends e).1 →
      C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 → C.lev (G.ends e).2 ≤ j →
      Z.cls e = G.cls e := fun e a b c d e' f' => (hZG e a b c d e' f').2
  have hℓj := (hℓ j).2 rfl
  have memj : ∀ e, e ∈ ℓ j ↔ G.cls e = some .plus ∧ (G.ends e).1 ∈ G.int ∧
      (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).1 = j ∧ C.lev (G.ends e).2 = j := by
    intro e
    rw [hℓj.2.1 e]
    constructor
    · rintro ⟨h1, -, -⟩
      rcases hRpres e (by rw [h1]; exact pne) with ⟨a1, a2, b1, b2, hrc, -⟩ | ⟨-, -, h', -⟩
      · exact ⟨by rw [← hrc]; exact h1, a1, b1, a2, b2⟩
      · rw [h1] at h'; exact absurd h' (by simp)
    · rintro ⟨h1, a1, b1, a2, b2⟩
      obtain ⟨hrc, hre⟩ := hRG e a1 a2 b1 b2
      refine ⟨by rw [hrc]; exact h1, ?_, ?_⟩ <;> rw [hre, hRint]
      · exact ⟨a1, a2⟩
      · exact ⟨b1, b2⟩
  have memm : ∀ m, m < j → ∀ e, e ∈ ℓ m ↔ G.cls e = some .plus ∧ (G.ends e).1 ∈ G.int ∧
      (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).1 = m ∧ C.lev (G.ends e).2 = m := by
    intro m hm e
    rw [((hℓ m).1 hm).2.1 e, C.R_intPlus (by omega)]
  -- the invariant of the induction
  have main : ∀ d, d ≤ j - i → (ordList ℓ J j d).Nodup ∧
      (∀ e, e ∈ ordList ℓ J j d ↔ G.cls e = some .plus ∧ (G.ends e).1 ∈ G.int ∧
        (G.ends e).2 ∈ G.int ∧ j - d ≤ C.lev (G.ends e).1 ∧ C.lev (G.ends e).1 ≤ j ∧
        j - d ≤ C.lev (G.ends e).2 ∧ C.lev (G.ends e).2 ≤ j) ∧
      Steps (Z.mapV f) (ordList ℓ J j d) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨hℓj.1, fun e => ?_, fun t ht => ?_⟩
      · simp only [ordList, Nat.sub_zero, memj]
        constructor
        · rintro ⟨h1, a1, b1, a2, b2⟩; exact ⟨h1, a1, b1, by omega, by omega, by omega, by omega⟩
        · rintro ⟨h1, a1, b1, a2, a3, b2, b3⟩; exact ⟨h1, a1, b1, by omega, by omega⟩
      · simp only [ordList] at ht ⊢
        have hx := (memj _).1 (List.getElem_mem ht)
        obtain ⟨hxp, x1, x2, x3, x4⟩ := hx
        have hxZ := hZcls _ x1 x2 (by omega) (by omega) (by omega) (by omega)
        rw [mapV_convert]
        refine red_mapV f ?_ ?_
        · rw [c_cls, ite_eq_right (fun h => getElem_notMem_take hℓj.1 ht h.1), hxZ, hxp]
        · refine center_wrap C (f := f) (c := j) hjk hij.le le_rfl hMi hMi' hMj hMj' hfe hZint hZG
            hRint hRpres' (fun h => absurd h (by omega))
            (fun h => absurd h (by omega)) hRp (wk_convert_erase _ _ _) (wk_convert_erase _ _ _)
            (hℓj.2.2 t ht).2.2 (fun e h1 h2 => Or.inl ?_) (fun e a1 a2 b1 b2 hG => ?_)
            (fun h => absurd h (by omega))
          · have := ce_none _ _ _ _ h1 h2; subst this; exact ⟨x3, x4⟩
          · rw [ce_cls, ce_cls, hZcls e a1 b1 (by omega) (by omega) (by omega) (by omega),
              (hRG e a1 a2 b1 b2).1]
    | succ d ih =>
      intro hd
      obtain ⟨ihn, ihm, ihs⟩ := ih (by omega)
      set m := j - (d + 1) with hm
      have hmj : m < j := by omega
      have him : i ≤ m := by omega
      have hm1 : j - d = m + 1 := by omega
      have hmk : m < C.k := by omega
      rw [hm1] at ihm
      obtain ⟨c1, c2, c3⟩ := C.cc_lev hmk (Or.inr rfl)
      have hc'Z := hZcls (C.cc' m) c1 c2 (by omega) (by omega) (by omega) (by omega)
      have hℓm := (hℓ m).1 hmj
      have nO : ∀ e, (C.lev (G.ends e).1 = m ∨ C.lev (G.ends e).2 = m) → e ∉ ordList ℓ J j d :=
        fun e h he => by have := (ihm e).1 he; omega
      refine ⟨?_, fun e => ?_, ?_⟩
      · rw [ordList, ← hm, List.nodup_append, List.nodup_append]
        refine ⟨ihn, ⟨by by_cases h : G.cls (C.cc' m) = some .plus <;> simp [J, h], hℓm.1, ?_⟩, ?_⟩
        · intro a ha b hb hab
          subst hab
          obtain ⟨rfl, -⟩ := (hJ m a).1 ha
          obtain ⟨-, -, -, h1, h2⟩ := (memm m hmj _).1 hb
          omega
        · intro a ha b hb hab
          subst hab
          rcases List.mem_append.1 hb with hb | hb
          · obtain ⟨rfl, -⟩ := (hJ m a).1 hb
            exact nO _ (by omega) ha
          · obtain ⟨-, -, -, h1, -⟩ := (memm m hmj _).1 hb
            exact nO _ (Or.inl h1) ha
      · rw [ordList, ← hm, List.mem_append, List.mem_append, ihm, hJ, memm m hmj]
        constructor
        · rintro (⟨h1, a1, b1, a2, a3, b2, b3⟩ | ⟨rfl, hp⟩ | ⟨h1, a1, b1, a2, b2⟩)
          · exact ⟨h1, a1, b1, by omega, a3, by omega, b3⟩
          · exact ⟨hp, c1, c2, by omega, by omega, by omega, by omega⟩
          · exact ⟨h1, a1, b1, by omega, by omega, by omega, by omega⟩
        · rintro ⟨h1, a1, b1, a2, a3, b2, b3⟩
          by_cases hge : m + 1 ≤ C.lev (G.ends e).1 ∧ m + 1 ≤ C.lev (G.ends e).2
          · exact Or.inl ⟨h1, a1, b1, hge.1, a3, hge.2, b3⟩
          · by_cases heq : C.lev (G.ends e).1 = m ∧ C.lev (G.ends e).2 = m
            · exact Or.inr (Or.inr ⟨h1, a1, b1, heq.1, heq.2⟩)
            · right; left
              obtain ⟨l, hl, hle⟩ := C.jump e (by rw [h1]; exact pne) (by rw [h1]; simp) a1 b1
                (by omega)
              obtain ⟨-, -, hll⟩ := C.cc_lev hl hle
              have hlm : l = m := by omega
              subst hlm
              rcases hle with rfl | rfl
              · rw [C.cc_diff _ hl] at h1; exact absurd h1 (by simp)
              · exact ⟨rfl, h1⟩
      · rw [ordList, ← hm]
        refine steps_append ihs (steps_append ?_ ?_)
        · -- the crossing edge `cc' m`
          by_cases hp : G.cls (C.cc' m) = some .plus
          · have hJm : J m = [C.cc' m] := by simp [J, hp]
            rw [hJm]
            intro t ht
            obtain rfl : t = 0 := by simp at ht; omega
            simp only [List.take_zero, List.getElem_cons_zero]
            rw [convert_nil, mapV_convert]
            refine red_mapV f ?_ ?_
            · rw [c_cls, ite_eq_right (fun h => nO _ (by omega) h.1), hc'Z, hp]
            · have hXer : ∀ e, ((Z.convert (ordList ℓ J j d)).erase (C.cc' m)).cls e = none →
                  Z.cls e ≠ none → (C.lev (G.ends e).1 = m + 1 ∧ C.lev (G.ends e).2 = m + 1) ∨
                    (i < m + 1 ∧ e = C.cc' (m + 1 - 1)) := fun e h1 h2 => by
                have := ce_none _ _ _ _ h1 h2
                exact Or.inr ⟨by omega, by simpa using this⟩
              have match1 : ∀ e, (G.ends e).1 ∈ G.int → C.lev (G.ends e).1 = m + 1 →
                  (G.ends e).2 ∈ G.int → C.lev (G.ends e).2 = m + 1 →
                  ((Z.convert (ordList ℓ J j d)).erase (C.cc' m)).cls e =
                    if G.cls e = some .plus then some .diff else G.cls e := by
                intro e a1 a2 b1 b2
                have hne : e ≠ C.cc' m := by rintro rfl; omega
                rw [ce_cls, ite_eq_right hne, hZcls e a1 b1 (by omega) (by omega) (by omega) (by
                    omega)]
                by_cases hgp : G.cls e = some .plus
                · rw [ite_eq_left ⟨(ihm e).2 ⟨hgp, a1, b1, by omega, by omega, by omega, by omega⟩,
                    hgp⟩,
                    ite_eq_left hgp]
                · rw [ite_eq_right (fun h => hgp h.2), ite_eq_right hgp]
              by_cases hm2 : m + 1 < j
              · obtain ⟨r1, r2, r3, r4, r5⟩ := Rmid (m + 1) (by omega) hm2
                have hℓm1 := (hℓ (m + 1)).1 hm2
                refine center_wrap C (f := f) (c := (m + 1)) hjk (by omega) hm2.le hMi hMi' hMj
                    hMj' hfe hZint hZG r1 r2 r3 r4 r5 (wk_convert_erase _ _ _)
                  (wk_convert (C.R (m + 1)) (ℓ (m + 1)))
                  (MGraph.DC_convert _ _ _ (ℓ (m + 1)) (C.R_preDet (by omega)).1) hXer
                  (fun e a1 a2 b1 b2 hG => ?_) (fun _ => ?_)
                · rw [match1 e a1 a2 b1 b2, c_cls,
                    (C.R_cls (l := m + 1) (by omega)).2.2.2.2 e a1 a2 b1 b2 |>.1]
                  by_cases hgp : G.cls e = some .plus
                  · rw [ite_eq_left hgp, ite_eq_left ⟨((memm (m + 1) hm2 e).2 ⟨hgp, a1, b1, a2,
                      b2⟩), hgp⟩]
                  · rw [ite_eq_right hgp, ite_eq_right (fun h => hgp h.2)]
                · obtain ⟨d1, d2, d3⟩ := C.cc_lev (l := m + 1) (by omega) (Or.inr rfl)
                  have hne : C.cc' (m + 1) ≠ C.cc' m := by
                    intro h; rw [h] at d3; omega
                  rw [ce_cls, ite_eq_right hne, hZcls _ d1 d2 (by omega) (by omega) (by omega) (by
                      omega)]
                  rcases C.cc'_cls (m + 1) (by omega) with h | h
                  · rw [h]; simp
                  · rw [ite_eq_left ⟨(ihm _).2 ⟨h, d1, d2, by omega, by omega, by omega, by omega⟩,
                      h⟩]
              · have hmj' : m + 1 = j := by omega
                refine center_wrap C (f := f) (c := (m + 1)) hjk (by omega) (by omega) hMi hMi' hMj
                    hMj' hfe hZint hZG (fun v => by rw [hRint, hmj'])
                  (fun e he => by rw [hmj']; exact hRpres' e he)
                  (fun h => absurd h (by omega)) (fun h => absurd h (by omega))
                  (fun h => by rw [hmj']; exact hRp (by omega)) (wk_convert_erase _ _ _)
                  (wk_convert Rb (ℓ j)) (MGraph.DC_convert _ _ _ (ℓ j) hRpd.1) hXer
                  (fun e a1 a2 b1 b2 hG => ?_) (fun h => absurd h (by omega))
                rw [hmj'] at a2 b2
                rw [match1 e a1 (by omega) b1 (by omega), c_cls, (hRG e a1 a2 b1 b2).1]
                by_cases hgp : G.cls e = some .plus
                · rw [ite_eq_left hgp, ite_eq_left ⟨(memj e).2 ⟨hgp, a1, b1, a2, b2⟩, hgp⟩]
                · rw [ite_eq_right hgp, ite_eq_right (fun h => hgp h.2)]
          · have hJm : J m = [] := by simp [J, hp]
            rw [hJm]
            intro t ht
            simp at ht
        · -- the order of the component `m`
          intro t ht
          rw [convert_convert, convert_convert, mapV_convert]
          have hx := (memm m hmj _).1 (List.getElem_mem ht)
          obtain ⟨hxp, x1, x2, x3, x4⟩ := hx
          have hxZ := hZcls _ x1 x2 (by omega) (by omega) (by omega) (by omega)
          have hxO : (ℓ m)[t] ∉ ordList ℓ J j d := nO _ (Or.inl x3)
          have hxJ : (ℓ m)[t] ∉ J m := fun h => by
            obtain ⟨h', -⟩ := (hJ m _).1 h
            rw [h'] at x3 x4; omega
          refine red_mapV f ?_ ?_
          · rw [c_cls, ite_eq_right (fun h => by
              simp only [List.mem_append] at h
              rcases h.1 with h | h | h
              · exact hxO h
              · exact hxJ h
              · exact getElem_notMem_take hℓm.1 ht h), hxZ, hxp]
          · obtain ⟨r1, r2, r3, r4, r5⟩ := Rmid m him hmj
            refine center_wrap C (f := f) (c := m) hjk him hmj.le hMi hMi' hMj hMj' hfe hZint hZG
                r1 r2 r3 r4 r5 (wk_convert_erase _ _ _)
              (wk_convert_erase _ _ _) (hℓm.2.2 t ht).2.2 (fun e h1 h2 => Or.inl ?_)
              (fun e a1 a2 b1 b2 hG => ?_) (fun _ => ?_)
            · have := ce_none _ _ _ _ h1 h2; subst this; exact ⟨x3, x4⟩
            · have heO : e ∉ ordList ℓ J j d := nO _ (Or.inl a2)
              have heJ : e ∉ J m := fun h => by
                obtain ⟨h', -⟩ := (hJ m _).1 h
                rw [h'] at a2 b2; omega
              rw [ce_cls, ce_cls, hZcls e a1 b1 (by omega) (by omega) (by omega) (by omega),
                ((C.R_cls (l := m) (by omega)).2.2.2.2 e a1 a2 b1 b2).1]
              simp only [List.mem_append, heO, heJ, false_or]
            · obtain ⟨d1, d2, d3⟩ := C.cc_lev hmk (Or.inr rfl)
              have hne : C.cc' m ≠ (ℓ m)[t] := by
                intro h; rw [← h] at x3 x4; omega
              rw [ce_cls, ite_eq_right hne, hc'Z]
              rcases C.cc'_cls m hmk with h | h
              · rw [h]; simp
              · rw [ite_eq_left ⟨by simp [(hJ m _).2 ⟨rfl, h⟩], h⟩]
  obtain ⟨hn, hmem, hst⟩ := main (j - i) le_rfl
  have hji : j - (j - i) = i := by omega
  rw [hji] at hmem
  -- the doubly connected property
  have hdc : (Z.mapV f).DC := by
    refine center_wrap C (f := f) (c := j) hjk hij.le le_rfl hMi hMi' hMj hMj' hfe hZint hZG hRint
        hRpres' (fun h => absurd h (by omega))
      (fun h => absurd h (by omega)) hRp (wk_refl Z) (wk_refl Rb) hRpd.1
      (fun e h1 h2 => absurd h1 h2) (fun e a1 a2 b1 b2 _ => ?_) (fun h => absurd h (by omega))
    rw [hZcls e a1 b1 (by omega) (by omega) (by omega) (by omega), (hRG e a1 a2 b1 b2).1]
  have hsat : Sat f Z.int := sat_of hf (by
    rw [hZint, hZint]; exact ⟨fun _ => ⟨hMj, by omega, by omega⟩, fun _ => ⟨hMi, by omega, by
        omega⟩⟩)
  refine ⟨hdc, ordList ℓ J j (j - i), hn, fun e => ?_, hst⟩
  rw [hmem]
  simp only [MGraph.IsIntPlus, MGraph.mapV, mem_image_sat hsat]
  constructor
  · rintro ⟨h1, a1, b1, a2, a3, b2, b3⟩
    obtain ⟨hze, hzc⟩ := hZG e a1 b1 a2 a3 b2 b3
    refine ⟨by rw [hzc]; exact h1, ?_, ?_⟩ <;> rw [hze, hZint]
    · exact ⟨a1, a2, a3⟩
    · exact ⟨b1, b2, b3⟩
  · rintro ⟨h1, -, -⟩
    obtain ⟨a1, b1, a2, a3, b2, b3⟩ := hZp e h1
    obtain ⟨-, hzc⟩ := hZG e a1 b1 a2 a3 b2 b3
    exact ⟨by rw [← hzc]; exact h1, a1, b1, a2, a3, b2, b3⟩

/-! ## [II, Lemmas 5.10 (A), 5.11] -/

/-- A proper isolated subset of the set of all internal vertices is a member of the chain. -/
private theorem chain_iso_eq {G : MGraph V E} {k : ℕ} {P : ℕ → Finset V}
    (hc : G.IsChain k P) (hio : G.IsoChain) {Q : Finset V} (hQ : G.IsProperIso G.int Q) :
    ∃ l, 1 ≤ l ∧ l ≤ k ∧ Q = P l := by
  classical
  set l := Nat.findGreatest (fun l => Q ⊆ P l) k with hl
  have hlk : l ≤ k := Nat.findGreatest_le k
  have hQl : Q ⊆ P l := Nat.findGreatest_spec (P := fun l => Q ⊆ P l) (Nat.zero_le k)
    (by rw [hc.1]; exact hQ.2.1)
  by_cases heq : Q = P l
  · refine ⟨l, ?_, hlk, heq⟩
    by_contra h0
    have : l = 0 := by omega
    rw [this, hc.1] at heq
    exact hQ.2.ne heq
  · have hss : Q ⊂ P l := Finset.ssubset_iff_subset_ne.2 ⟨hQl, heq⟩
    rcases Nat.lt_or_ge l k with hlt | hge
    · have hmax := hc.2.1 l hlt
      have hPint : P (l + 1) ⊂ G.int := by
        refine Finset.ssubset_of_ssubset_of_subset hmax.1.2 ?_
        rw [← hc.1]; exact chain_anti hc (Nat.zero_le l) hlt.le
      have hng : ¬ Q ⊆ P (l + 1) :=
        Nat.findGreatest_is_greatest (P := fun l => Q ⊆ P l) (n := k) (by omega) (by omega)
      exfalso
      rcases hio _ _ hQ ⟨hmax.1.1, hPint⟩ with h | h
      · exact hng h
      · by_cases h' : P (l + 1) = Q
        · exact hng (h' ▸ Finset.Subset.refl _)
        · exact hmax.2 Q ⟨hQ.1, hss⟩ (Finset.ssubset_iff_subset_ne.2 ⟨h, h'⟩)
    · have : l = k := le_antisymm hlk hge
      rw [this] at hss
      exact absurd ⟨hQ.1, hss⟩ (hc.2.2 Q)

/-- A sequentially pre-deterministic graph has a chain of proper isolated subsets: each member
after the first is a maximal isolated subset of the previous one, and the last one has no proper
isolated subset. -/
private theorem exists_chain {G : MGraph V E} :
    ∃ k P, G.IsChain k P := by
  classical
  have hmax : ∀ S, (∃ Q, G.IsProperIso S Q) → ∃ Q, G.IsMaximalIso S Q := by
    intro S ⟨Q₀, hQ₀⟩
    obtain ⟨Q, hQ, hmx⟩ := Finset.exists_max_image (S.powerset.filter fun Q => G.IsProperIso S Q)
      Finset.card ⟨Q₀, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hQ₀.2.1, hQ₀⟩⟩
    obtain ⟨-, hQ⟩ := Finset.mem_filter.1 hQ
    refine ⟨Q, hQ, fun Q' hQ' hlt => ?_⟩
    have := hmx Q' (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hQ'.2.1, hQ'⟩)
    have := Finset.card_lt_card hlt
    omega
  let nxt : Finset V → Finset V := fun S =>
    if h : ∃ Q, G.IsProperIso S Q then Classical.choose (hmax S h) else S
  have hnxt : ∀ S (h : ∃ Q, G.IsProperIso S Q), G.IsMaximalIso S (nxt S) := fun S h => by
    simp only [nxt, h, ↓reduceDIte]; exact Classical.choose_spec (hmax S h)
  let P : ℕ → Finset V := fun l => nxt^[l] G.int
  have hP : ∀ l, P (l + 1) = nxt (P l) := fun l => Function.iterate_succ_apply' _ _ _
  have hex : ∃ l, ¬ ∃ Q, G.IsProperIso (P l) Q := by
    by_contra hn
    push Not at hn
    have key : ∀ l, (P l).card + l ≤ (P 0).card := by
      intro l
      induction l with
      | zero => simp
      | succ n ih =>
        have := Finset.card_lt_card (hnxt (P n) (hn n)).1.2
        rw [hP]; omega
    have := key ((P 0).card + 1)
    omega
  refine ⟨Nat.find hex, P, rfl, fun l hl => ?_, not_exists.1 (Nat.find_spec hex)⟩
  have := Nat.find_min hex hl
  rw [not_not] at this
  rw [hP]
  exact hnxt _ this

/-- An edge with both ends in `S` keeps its class in the subgraph induced on `S`. -/
private theorem ind_cls [DecidableEq V] (G : MGraph V E) {S : Finset V} {e : E}
    (h1 : (G.ends e).1 ∈ S) (h2 : (G.ends e).2 ∈ S) : (G.induce S).cls e = G.cls e := by
  simp [MGraph.induce, h1, h2]

/-- An edge other than the two replaced ones keeps its class of the induced subgraph. -/
private theorem rep_cls [DecidableEq V] [DecidableEq E] (G : MGraph V E) {S P : Finset V}
    {e₁ e₂ e : E} (h1 : e ≠ e₁) (h2 : e ≠ e₂) :
    (G.replace S P e₁ e₂).cls e = (G.induce (S \ P)).cls e := by
  simp [MGraph.replace, h1, h2]

/-- Membership in the members of the chain. -/
private theorem Ctx.mem_P [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G) {m : ℕ}
    (hm : m ≤ C.k) (v : V) : v ∈ C.P m ↔ v ∈ G.int ∧ m ≤ C.lev v :=
  ⟨fun h => ⟨C.Psub m hm h, (C.memP v (C.Psub m hm h) m hm).1 h⟩,
    fun ⟨h1, h2⟩ => (C.memP v h1 m hm).2 h2⟩

/-- [II, Lemma 5.11] for a map `f` identifying a vertex `Mi` of the component `i` with a vertex
`Mj` of the component `j > i`. -/
private theorem merge_clause [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {f : V → V} {i j : ℕ} {Mi Mj : V} (hij : i < j) (hjk : j ≤ C.k)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hf : MergeMap f Mi Mj) (hfe : f Mi = f Mj) :
    (G.mapV f).ClauseIII ((C.P i).image f) ((chainNext C.k C.P j).map (Finset.image f)) := by
  classical
  have hik : i ≤ C.k := by omega
  have hPi : Sat f (C.P i) := sat_of hf (by
    rw [C.mem_P hik, C.mem_P hik]; exact ⟨fun _ => ⟨hMj, by omega⟩, fun _ => ⟨hMi, by omega⟩⟩)
  have Pint : ∀ m, m ≤ C.k → C.P m ⊆ G.int := C.Psub
  by_cases hjk' : j < C.k
  · have hPj : Sat f (C.P (j + 1)) := sat_of hf (by
      rw [C.mem_P hjk', C.mem_P hjk']; constructor <;> rintro ⟨-, h⟩ <;> omega)
    have hch : chainNext C.k C.P j = some (C.P (j + 1)) := by simp [chainNext, hjk']
    rw [hch, Option.map_some]
    -- the crossing edges of `P (j + 1)`
    have crl : ∀ e, G.Crosses (C.P (j + 1)) e → (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧
        ((C.lev (G.ends e).1 = j ∧ C.lev (G.ends e).2 = j + 1) ∨
          (C.lev (G.ends e).1 = j + 1 ∧ C.lev (G.ends e).2 = j)) := fun e he =>
      C.cc_lev hjk' ((C.cross j hjk' e).1 he)
    refine ⟨⟨⟨(iso_mapV hf hMi hMj hPj (Pint _ hjk')).2 (C.chain.2.1 j hjk').1.1, ?_⟩, ?_⟩, ?_⟩
    · rw [image_ssubset_sat hPj hPi, Finset.ssubset_iff_subset_ne]
      refine ⟨chain_anti C.chain (by omega) hjk', fun h => ?_⟩
      have : Mi ∈ C.P (j + 1) := by rw [h]; exact (C.mem_P hik _).2 ⟨hMi, by omega⟩
      rw [C.mem_P hjk'] at this; omega
    · intro Q ⟨hQi, hQs⟩ hlt
      obtain ⟨hQim, hQsat, hQsub⟩ := preim_spec hf hMi hMj (hQi.1)
      rw [← hQim] at hQi hQs hlt
      rw [iso_mapV hf hMi hMj hQsat hQsub] at hQi
      rw [image_ssubset_sat hQsat hPi] at hQs
      rw [image_ssubset_sat hPj hQsat] at hlt
      have hio : G.IsProperIso G.int (preim G f Q) := by
        refine ⟨hQi, Finset.ssubset_of_ssubset_of_subset hQs ?_⟩
        rw [← C.chain.1]; exact chain_anti C.chain (Nat.zero_le i) hik
      obtain ⟨l, hl1, hlk, hl⟩ := chain_iso_eq C.chain C.spd.2.1 hio
      rw [hl] at hQs hlt hQsat
      have hil : i < l := by
        by_contra h
        exact hQs.2 (chain_anti C.chain (by omega) hik)
      have hlj : l ≤ j := by
        by_contra h
        exact hlt.2 (chain_anti C.chain (by omega) hlk)
      have hMjl : Mj ∈ C.P l := (C.mem_P hlk _).2 ⟨hMj, by omega⟩
      have := hQsat Mi (by rw [hfe]; exact Finset.mem_image_of_mem f hMjl)
      rw [C.mem_P hlk] at this; omega
    · intro e₁ e₂ hne h1 h2
      rw [crosses_mapV hf hMi hMj hPj] at h1 h2
      rw [replace_mapV G hPi hPj]
      obtain ⟨g1, g2, g3⟩ := crl e₁ h1
      obtain ⟨g1', g2', g3'⟩ := crl e₂ h2
      have nE : ∀ e, C.lev (G.ends e).1 ≤ j → C.lev (G.ends e).2 ≤ j → e ≠ e₁ ∧ e ≠ e₂ := by
        intro e a b
        constructor <;> rintro rfl <;> omega
      have sdi : ∀ a, a ≤ j → ∀ v, v ∈ C.P a \ C.P (j + 1) ↔ v ∈ G.int ∧ a ≤ C.lev v ∧
          C.lev v ≤ j := by
        intro a ha v
        rw [Finset.mem_sdiff, C.mem_P (by omega), C.mem_P hjk']
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by by_contra h; exact h3 ⟨h1, by omega⟩⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, fun ⟨_, h⟩ => by omega⟩
      have hRe1 : (G.replace (C.P j) (C.P (j + 1)) e₁ e₂).cls e₁ = some .diff := by
        simp [MGraph.replace]
      refine merge_core C hij hjk hMi hMi' hMj hMj' hf hfe (fun v => sdi i hij.le v)
        (fun e a1 b1 a2 a3 b2 b3 => ?_) (fun e he => ?_) (fun v => ?_)
        (C.spd.2.2.2 _ _ _ _ (chain_isoOrTop C.chain hjk) (C.chain.2.1 j hjk') hne h1 h2)
        (fun e he => ?_) (fun e a1 a2 b1 b2 => ?_)
      · obtain ⟨n1, n2⟩ := nE e a3 b3
        have hin : (G.ends e).1 ∈ C.P i \ C.P (j + 1) ∧ (G.ends e).2 ∈ C.P i \ C.P (j + 1) :=
          ⟨(sdi i hij.le _).2 ⟨a1, a2, a3⟩, (sdi i hij.le _).2 ⟨b1, b2, b3⟩⟩
        exact ⟨by simp [MGraph.replace, n1], by rw [rep_cls G n1 n2, ind_cls G hin.1 hin.2]⟩
      · have n1 : e ≠ e₁ := by rintro rfl; simp [MGraph.replace] at he
        have n2 : e ≠ e₂ := by rintro rfl; simp [MGraph.replace, hne.symm] at he
        have hin : (G.ends e).1 ∈ C.P i \ C.P (j + 1) ∧ (G.ends e).2 ∈ C.P i \ C.P (j + 1) := by
          rw [rep_cls G n1 n2] at he
          exact ⟨(induce_pres (by rw [he]; simp)).1, (induce_pres (by rw [he]; simp)).2.1⟩
        obtain ⟨a1, a2, a3⟩ := (sdi i hij.le _).1 hin.1
        obtain ⟨b1, b2, b3⟩ := (sdi i hij.le _).1 hin.2
        exact ⟨a1, b1, a2, a3, b2, b3⟩
      · change v ∈ C.P j \ C.P (j + 1) ↔ _
        rw [sdi j le_rfl]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega, by omega⟩
      · by_cases n1 : e = e₁
        · subst n1
          refine Or.inr ⟨by simp [MGraph.replace], by simp [MGraph.replace], hRe1, ?_, ?_⟩ <;> omega
        · have n2 : e ≠ e₂ := by rintro rfl; simp [MGraph.replace, hne.symm] at he
          have hin : (G.ends e).1 ∈ C.P j \ C.P (j + 1) ∧ (G.ends e).2 ∈ C.P j \ C.P (j + 1) := by
            rw [rep_cls G n1 n2] at he
            exact ⟨(induce_pres he).1, (induce_pres he).2.1⟩
          obtain ⟨a1, a2, a3⟩ := (sdi j le_rfl _).1 hin.1
          obtain ⟨b1, b2, b3⟩ := (sdi j le_rfl _).1 hin.2
          refine Or.inl ⟨a1, by omega, b1, by omega, ?_, by simp [MGraph.replace, n1]⟩
          rw [rep_cls G n1 n2, ind_cls G hin.1 hin.2]
      · obtain ⟨n1, n2⟩ := nE e (by omega) (by omega)
        have hin : (G.ends e).1 ∈ C.P j \ C.P (j + 1) ∧ (G.ends e).2 ∈ C.P j \ C.P (j + 1) :=
          ⟨(sdi j le_rfl _).2 ⟨a1, by omega, by omega⟩, (sdi j le_rfl _).2 ⟨b1, by omega, by omega⟩⟩
        exact ⟨by rw [rep_cls G n1 n2, ind_cls G hin.1 hin.2], by simp [MGraph.replace, n1]⟩
  · have hjk2 : j = C.k := by omega
    have hch : chainNext C.k C.P j = none := by simp [chainNext, hjk']
    rw [hch, Option.map_none]
    change ((G.mapV f).induce ((C.P i).image f)).PreDet
    rw [induce_mapV G hPi]
    have mi : ∀ a, a ≤ C.k → ∀ v, v ∈ C.P a ↔ v ∈ G.int ∧ a ≤ C.lev v ∧ C.lev v ≤ j := by
      intro a ha v
      rw [C.mem_P ha]
      have := C.lev_le v
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩
      · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    refine merge_core C hij hjk hMi hMi' hMj hMj' hf hfe (mi i hik) (fun e a1 b1 a2 a3 b2 b3 => ?_)
      (fun e he => ?_) (fun v => ?_)
      (C.spd.2.2.1 _ (chain_isoOrTop C.chain le_rfl) C.chain.2.2) (fun e he => ?_)
      (fun e a1 a2 b1 b2 => ?_)
    · have hin : (G.ends e).1 ∈ C.P i ∧ (G.ends e).2 ∈ C.P i :=
        ⟨(mi i hik _).2 ⟨a1, a2, a3⟩, (mi i hik _).2 ⟨b1, b2, b3⟩⟩
      exact ⟨rfl, ind_cls G hin.1 hin.2⟩
    · obtain ⟨h1, h2, -⟩ := induce_pres (by rw [he]; simp)
      obtain ⟨a1, a2, a3⟩ := (mi i hik _).1 h1
      obtain ⟨b1, b2, b3⟩ := (mi i hik _).1 h2
      exact ⟨a1, b1, a2, a3, b2, b3⟩
    · change v ∈ C.P C.k ↔ _
      rw [C.mem_P le_rfl]
      have := C.lev_le v
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := induce_pres he
      rw [C.mem_P le_rfl] at h1 h2
      have l1 := C.lev_le (G.ends e).1
      have l2 := C.lev_le (G.ends e).2
      exact Or.inl ⟨h1.1, by omega, h2.1, by omega, h3, rfl⟩
    · have hin : (G.ends e).1 ∈ C.P C.k ∧ (G.ends e).2 ∈ C.P C.k :=
        ⟨(C.mem_P le_rfl _).2 ⟨a1, by omega⟩, (C.mem_P le_rfl _).2 ⟨b1, by omega⟩⟩
      exact ⟨ind_cls G hin.1 hin.2, rfl⟩

/-- **[II, Lemma 5.11]**, without ghost edges: in a sequentially pre-deterministic graph with
the chain `P` of `k` proper isolated subsets, merging a molecule `M` of the component `Γ_i` with
a molecule `M'` of the component `Γ_j`, `i < j`: for `j < k`, the image of `P (j + 1)` is the
maximal isolated subset of the image of `P i`, and replacing it and its two external edges by one
`Θ` edge gives a pre-deterministic graph; for `j = k`, the subgraph induced on the image of `P i`
is pre-deterministic. -/
theorem MGraph.merge_chain :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (k : ℕ) (P : ℕ → Finset V)
    (i j : ℕ) (M M' : V), (∀ e₀ : E, G.cls e₀ ≠ some .ghost) → G.SPD → G.IsChain k P →
    i < j → j ≤ k → MGraph.InComp k P i M → MGraph.InComp k P j M' →
    (G.merge M M').ClauseIII ((P i).image fun v => if v = M' then M else v)
      ((chainNext k P j).map (Finset.image fun v => if v = M' then M else v)) := by
  intro V E _ _ G k P i j M M' hng hs hc hij hjk hM hM'
  have : Nonempty E := by
    obtain ⟨-, e₁, -, -, -⟩ := (hc.2.1 0 (by omega)).1.1
    exact ⟨e₁⟩
  obtain ⟨C, rfl, rfl⟩ := ctx_exists hs hc hng
  have hMi : M ∈ G.int := C.Psub i (by omega) hM.1
  have hMj : M' ∈ G.int := C.Psub j hjk hM'.1
  have li : C.lev M = i := by
    have h1 := (C.memP M hMi i (by omega)).1 hM.1
    have h3 : ¬ i + 1 ≤ C.lev M := fun h => hM.2 (by omega) ((C.memP M hMi (i + 1) (by omega)).2 h)
    omega
  have lj : C.lev M' = j := by
    have h1 := (C.memP M' hMj j hjk).1 hM'.1
    by_cases hjk' : j < C.k
    · have h3 : ¬ j + 1 ≤ C.lev M' := fun h => hM'.2 hjk' ((C.memP M' hMj (j + 1) hjk').2 h)
      omega
    · have := C.lev_le M'; omega
  have hne : M ≠ M' := by intro h; rw [h] at li; omega
  exact merge_clause C hij hjk hMi li hMj lj (mergeMap_merge M M') (by simp [hne])

/-- A member of a chain: the set of all internal vertices, or an isolated subset. -/
private theorem iso_top_eq {G : MGraph V E} {k : ℕ} {P : ℕ → Finset V}
    (hc : G.IsChain k P) (hio : G.IsoChain) {T : Finset V} (hT : G.IsoOrTop T) :
    ∃ s ≤ k, T = P s := by
  rcases hT with rfl | hiso
  · exact ⟨0, Nat.zero_le k, hc.1.symm⟩
  · by_cases htop : T = G.int
    · exact ⟨0, Nat.zero_le k, htop.trans hc.1.symm⟩
    · obtain ⟨l, -, hlk, hl⟩ := chain_iso_eq hc hio
        ⟨hiso, Finset.ssubset_iff_subset_ne.2 ⟨hiso.1, htop⟩⟩
      exact ⟨l, hlk, hl⟩

/-- **[II, Lemma 5.10], operation (A)**, without ghost edges: merging two internal molecules of a
sequentially pre-deterministic graph gives a sequentially pre-deterministic graph. -/
theorem MGraph.spd_merge :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (M M' : V),
    (∀ e₀ : E, G.cls e₀ ≠ some .ghost) → G.SPD → M ∈ G.int → M' ∈ G.int →
    (G.merge M M').SPD := by
  intro V E _ _ G M M' hng hs hM hM'
  by_cases hMM : M = M'
  · subst hMM
    have : G.merge M M = G := by
      have hid : (fun v => if v = M then M else v) = id := by
        funext v; split_ifs with h <;> simp [h]
      unfold MGraph.merge MGraph.mapV
      rw [hid]
      simp
    rw [this]; exact hs
  have : Nonempty E := by
    obtain ⟨_, _, _, _, _, hsK, _⟩ := hs.1
    obtain ⟨e, -⟩ := hsK {M} (by simpa using hM) (by simp)
      (fun h => hMM (Finset.mem_singleton.1 (h hM')).symm)
    exact ⟨e⟩
  obtain ⟨k, P, hc⟩ := exists_chain (G := G)
  obtain ⟨C, rfl, rfl⟩ := ctx_exists hs hc hng
  set f : V → V := fun v => if v = M' then M else v with hfdef
  have hf : MergeMap f M M' := mergeMap_merge M M'
  have hfe : f M = f M' := by simp [hfdef]
  have hf' : MergeMap f M' M := fun a b h => (hf a b h).imp id fun ⟨h1, h2⟩ =>
    ⟨h1.symm, h2.symm⟩
  change (G.mapV f).SPD
  have hint : Sat f G.int := sat_of hf (iff_of_true hM hM')
  set a := C.lev M with ha
  set b := C.lev M' with hb
  have satP : ∀ l, l ≤ C.k → (Sat f (C.P l) ↔ (l ≤ a ↔ l ≤ b)) := by
    intro l hl
    constructor
    · intro h
      rw [← C.mem_P hl M |>.trans (and_iff_right hM), ← C.mem_P hl M' |>.trans (and_iff_right hM')]
      constructor
      · intro h'; exact h M' (by rw [← hfe]; exact Finset.mem_image_of_mem f h')
      · intro h'; exact h M (by rw [hfe]; exact Finset.mem_image_of_mem f h')
    · intro h
      refine sat_of hf ?_
      rw [C.mem_P hl, C.mem_P hl]
      exact ⟨fun ⟨_, h'⟩ => ⟨hM', h.1 h'⟩, fun ⟨_, h'⟩ => ⟨hM, h.2 h'⟩⟩
  have isoP : ∀ l, 1 ≤ l → l ≤ C.k → G.IsIsolated (C.P l) := by
    intro l h1 h2
    have := (C.chain.2.1 (l - 1) (by omega)).1.1
    rwa [Nat.sub_add_cancel h1] at this
  have santi : ∀ s l, s < l → l ≤ C.k → C.P l ⊂ C.P s := fun s l h1 h2 =>
    Finset.ssubset_of_subset_of_ssubset (chain_anti C.chain h1 h2) (C.chain.2.1 s (by omega)).1.2
  have proper : ∀ s l, s < l → l ≤ C.k → Sat f (C.P s) → Sat f (C.P l) →
      (G.mapV f).IsProperIso ((C.P s).image f) ((C.P l).image f) := by
    intro s l h1 h2 hs' hl'
    exact ⟨(iso_mapV hf hM hM' hl' (C.Psub l h2)).2 (isoP l (by omega) h2),
      (image_ssubset_sat hl' hs').2 (santi s l h1 h2)⟩
  -- an isolated subset or the top set of the graph with `M` and `M'` identified
  have pull : ∀ S, (G.mapV f).IsoOrTop S → ∃ s ≤ C.k, S = (C.P s).image f ∧ Sat f (C.P s) := by
    intro S hS
    have hSi : S ⊆ (G.mapV f).int := by
      rcases hS with rfl | h
      · exact Finset.Subset.refl _
      · exact h.1
    obtain ⟨hSim, hSsat, hSsub⟩ := preim_spec hf hM hM' hSi
    have hT : G.IsoOrTop (preim G f S) := by
      rcases hS with rfl | h
      · exact Or.inl (preim_image hint (Finset.Subset.refl _))
      · rw [← hSim] at h; exact Or.inr ((iso_mapV hf hM hM' hSsat hSsub).1 h)
    obtain ⟨s, hsk, hs'⟩ := iso_top_eq C.chain C.spd.2.1 hT
    rw [hs'] at hSim hSsat
    exact ⟨s, hsk, hSim.symm, hSsat⟩
  have hla := C.lev_le M
  have hlb := C.lev_le M'
  -- one of `M`, `M'` in the component `s`, the other deeper: the levels between are
  -- not saturated
  have unsat : ∀ s l, s < l → l ≤ C.k → (∀ l', s < l' → l' ≤ l → ¬ Sat f (C.P l')) →
      Sat f (C.P s) → (a = s ∧ l ≤ b) ∨ (b = s ∧ l ≤ a) := by
    intro s l h1 h2 hn hs'
    have e1 := (satP s (by omega)).1 hs'
    have e2 := mt (satP (s + 1) (by omega)).2 (hn (s + 1) (by omega) (by omega))
    have e3 := mt (satP l h2).2 (hn l h1 le_rfl)
    by_cases h : s + 1 ≤ a
    · have hb' : ¬ s + 1 ≤ b := fun h' => e2 (iff_of_true h h')
      have hbs : b = s := by have := e1.1 (by omega); omega
      refine Or.inr ⟨hbs, ?_⟩
      by_contra h''; exact e3 (iff_of_false h'' (by omega))
    · have hb' : s + 1 ≤ b := by by_contra h'; exact e2 (iff_of_false h h')
      have has : a = s := by have := e1.2 (by omega); omega
      refine Or.inl ⟨has, ?_⟩
      by_contra h''; exact e3 (iff_of_false (by omega) h'')
  refine ⟨dc_mapV f hs.1, ?_, ?_, ?_⟩
  · intro P₁ Q₁ hP hQ
    obtain ⟨s₁, hs₁, rfl, hsat₁⟩ := pull P₁ (Or.inr hP.1)
    obtain ⟨s₂, hs₂, rfl, hsat₂⟩ := pull Q₁ (Or.inr hQ.1)
    rw [image_subset_sat hsat₂, image_subset_sat hsat₁]
    rcases le_total s₁ s₂ with h | h
    · exact Or.inr (chain_anti C.chain h hs₂)
    · exact Or.inl (chain_anti C.chain h hs₁)
  · intro S hS hmin
    obtain ⟨s, hsk, rfl, hsat⟩ := pull S hS
    by_cases hsk' : s = C.k
    · subst hsk'
      rw [induce_mapV G hsat]
      exact preDet_mapV f (C.spd.2.2.1 _ (chain_isoOrTop C.chain le_rfl) C.chain.2.2) hsat
    · -- the deeper members are not saturated
      have hn : ∀ l', s < l' → l' ≤ C.k → ¬ Sat f (C.P l') := fun l' h1 h2 h3 =>
        hmin _ (proper s l' h1 h2 hsat h3)
      rcases unsat s C.k (by omega) le_rfl (fun l' h1 h2 => hn l' h1 h2) hsat with
        ⟨has, hbk⟩ | ⟨hbs, hak⟩
      · have := merge_clause C (f := f) (i := s) (j := C.k) (by omega) le_rfl hM has hM'
          (by omega) hf hfe
        simpa [chainNext, MGraph.ClauseIII] using this
      · have := merge_clause C (f := f) (i := s) (j := C.k) (by omega) le_rfl hM' hbs hM
          (by omega) hf' hfe.symm
        simpa [chainNext, MGraph.ClauseIII] using this
  · intro S P₁ e₁ e₂ hS hmax hne h1 h2
    obtain ⟨s, hsk, rfl, hsat⟩ := pull S hS
    obtain ⟨hP₁im, hP₁sat, hP₁sub⟩ := preim_spec hf hM hM' hmax.1.1.1
    have hiso := hmax.1.1
    rw [← hP₁im] at hiso
    rw [iso_mapV hf hM hM' hP₁sat hP₁sub] at hiso
    have hss := hmax.1.2
    rw [← hP₁im, image_ssubset_sat hP₁sat hsat] at hss
    obtain ⟨p, hp1, hpk, hp⟩ := chain_iso_eq C.chain C.spd.2.1
      ⟨hiso, Finset.ssubset_of_ssubset_of_subset hss (C.Psub s hsk)⟩
    rw [hp] at hP₁sat hss hP₁im
    rw [← hP₁im] at h1 h2 hmax ⊢
    have hsp : s < p := by
      by_contra h
      exact hss.2 (chain_anti C.chain (by omega) hsk)
    by_cases hp' : p = s + 1
    · subst hp'
      rw [crosses_mapV hf hM hM' hP₁sat] at h1 h2
      rw [replace_mapV G hsat hP₁sat]
      exact preDet_mapV f (C.spd.2.2.2 _ _ _ _ (chain_isoOrTop C.chain hsk) (C.chain.2.1 s
        (by omega)) hne h1 h2) (sat_sdiff hsat hP₁sat)
    · have hn : ∀ l', s < l' → l' ≤ p - 1 → ¬ Sat f (C.P l') := fun l' h1' h2' h3 =>
        hmax.2 _ (proper s l' h1' (by omega) hsat h3)
          ((image_ssubset_sat hP₁sat h3).2 (santi l' p (by omega) hpk))
      have e4 := (satP p hpk).1 hP₁sat
      rcases unsat s (p - 1) (by omega) (by omega) hn hsat with ⟨has, hbk⟩ | ⟨hbs, hak⟩
      · have hbp : b = p - 1 := by
          by_contra h; exact absurd (e4.2 (by omega)) (by omega)
        have := merge_clause C (f := f) (i := s) (j := p - 1) (by omega) (by omega) hM has
          hM' hbp hf hfe
        have hch : chainNext C.k C.P (p - 1) = some (C.P p) := by
          simp [chainNext, show p - 1 < C.k by omega, Nat.sub_add_cancel hp1]
        rw [hch] at this
        exact this.2 e₁ e₂ hne h1 h2
      · have hap : a = p - 1 := by
          by_contra h; exact absurd (e4.1 (by omega)) (by omega)
        have := merge_clause C (f := f) (i := s) (j := p - 1) (by omega) (by omega) hM' hbs
          hM hap hf' hfe.symm
        have hch : chainNext C.k C.P (p - 1) = some (C.P p) := by
          simp [chainNext, show p - 1 < C.k by omega, Nat.sub_add_cancel hp1]
        rw [hch] at this
        exact this.2 e₁ e₂ hne h1 h2

section Instances

end Instances

end RBM8D.Graphs
