module

public import RBM8D.Graph.Deterministic

@[expose] public section

/-!
# Operations on the molecular multigraph

The operations of [II, §5.4] on `MGraph` (merging molecules, splitting an edge through a molecule, recolouring, adding an internal vertex, collapsing a set), chains of isolated subsets, and the claims of [II, App A] used by [II, Lemmas 5.10–5.13].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

variable {V E : Type}

/-- The molecular multigraph with its vertices mapped by `f`: the ends of every edge are mapped,
and so are the internal and external vertices. An edge whose two ends get the same image is a
loop, which crosses no cut. -/
def MGraph.mapV [DecidableEq V] (G : MGraph V E) (f : V → V) : MGraph V E where
  int := G.int.image f
  ext := G.ext.image f
  ends e := (f (G.ends e).1, f (G.ends e).2)
  cls := G.cls

/-- Operation (A) of [II, §5.4]: the molecule `M'` identified with the molecule `M`. -/
def MGraph.merge [DecidableEq V] (G : MGraph V E) (M M' : V) : MGraph V E :=
  G.mapV fun v => if v = M' then M else v

/-- Operation (B) of [II, §5.4]: the edge `e` between `M` and `M'` replaced by the edge `e` from
`M` to `w` and the edge `e'` (absent before) from `w` to `M'`, of the class of `e`. -/
def MGraph.split [DecidableEq E] (G : MGraph V E) (e e' : E) (w : V) : MGraph V E where
  int := G.int
  ext := G.ext
  ends f := if f = e then ((G.ends e).1, w) else if f = e' then (w, (G.ends e).2) else G.ends f
  cls f := if f = e' then G.cls e else G.cls f

/-- The class of the edge `e` changed to `c`, its ends kept. -/
def MGraph.recolor [DecidableEq E] (G : MGraph V E) (e : E) (c : Option MClass) : MGraph V E :=
  { G with cls := Function.update G.cls e c }

/-- The edge `e` set to join `u` to `v` with the class `c`. -/
def MGraph.setEdge [DecidableEq E] (G : MGraph V E) (e : E) (u v : V) (c : Option MClass) :
    MGraph V E where
  int := G.int
  ext := G.ext
  ends f := if f = e then (u, v) else G.ends f
  cls := Function.update G.cls e c

/-- The vertex `v` added to the internal vertices (a new molecule). -/
def MGraph.addInt [DecidableEq V] (G : MGraph V E) (v : V) : MGraph V E :=
  { G with int := insert v G.int }

/-- The set `S` of internal vertices collapsed to its vertex `s₀` (the quotient graph `𝒢/𝒮` of
[II, Claim A.1]). -/
def MGraph.collapse [DecidableEq V] (G : MGraph V E) (S : Finset V) (s₀ : V) : MGraph V E :=
  G.mapV fun v => if v ∈ S then s₀ else v

/-- The chain of proper isolated subsets of [II, (5.2)–(5.4)] with `k` members: `P 0` is the set
of all internal vertices, `P (l + 1)` is the maximal isolated subset of `P l` for `l < k`, and
`P k` (the minimal isolated subset) has no proper isolated subset. -/
def MGraph.IsChain (G : MGraph V E) (k : ℕ) (P : ℕ → Finset V) : Prop :=
  P 0 = G.int ∧ (∀ l < k, G.IsMaximalIso (P l) (P (l + 1))) ∧ ∀ Q, ¬ G.IsProperIso (P k) Q

/-- The vertex `M` lies in the component `Γ_l` of the chain ([II, (5.4)]): in `P l`, and not in
`P (l + 1)` when `l < k`. -/
def MGraph.InComp (k : ℕ) (P : ℕ → Finset V) (l : ℕ) (M : V) : Prop :=
  M ∈ P l ∧ (l < k → M ∉ P (l + 1))

/-- Every replacement of [II, Def 5.9 (iii)] of the subset `P` of `S` and two of its external
edges by one `Θ` edge gives a pre-deterministic graph. -/
def MGraph.ReplPreDet [DecidableEq V] [DecidableEq E] (G : MGraph V E) (S P : Finset V) : Prop :=
  ∀ e₁ e₂, e₁ ≠ e₂ → G.Crosses P e₁ → G.Crosses P e₂ → (G.replace S P e₁ e₂).PreDet

/-- The pre-deterministic clause of [II, Def 5.9 (iii)] for `S` and its next member `T` of the
chain: for `T = none`, the subgraph induced on `S` is pre-deterministic; for `T = some P`, the set
`P` is the maximal isolated subset of `S` and every replacement of `P` gives a pre-deterministic
graph. -/
def MGraph.ClauseIII [DecidableEq V] [DecidableEq E] (G : MGraph V E) (S : Finset V) :
    Option (Finset V) → Prop
  | none => (G.induce S).PreDet
  | some P => G.IsMaximalIso S P ∧ G.ReplPreDet S P

/-- The member of the chain after `P j`: `P (j + 1)` for `j < k`, none for `j = k`. -/
def chainNext (k : ℕ) (P : ℕ → Finset V) (j : ℕ) : Option (Finset V) :=
  if j < k then some (P (j + 1)) else none

/-- The graph of [II, Claims A.4, A.5]: a new molecule `N`, the `Θ` edge `b₀` replaced by a path
`b₀`, `b₂` through `N`, and the edge `b` replaced by a path `b`, `b₄` through `N`. -/
def MGraph.twoSplit [DecidableEq V] [DecidableEq E] (G : MGraph V E) (N : V) (b₀ b₂ b b₄ : E) :
    MGraph V E :=
  ((G.addInt N).split b₀ b₂ N).split b b₄ N

/-! ## Nets of doubly connected graphs -/

/-- A set of edges containing a spanning set of edges spans. -/
private theorem spans_mono {G : MGraph V E} {B B' : Finset E} (h : G.Spans B) (hs : B ⊆ B') :
    G.Spans B' := by
  intro S h1 h2 h3
  obtain ⟨e, he, h4⟩ := h S h1 h2 h3
  exact ⟨e, hs he, h4⟩

/-- An edge `e` of a spanning net of `G` that cuts `X` is replaced in `H` either by an edge with
the same ends, or by the two edges `e`, `e'` of a path through `w`; one of them cuts `X`. -/
private theorem step_edit {G H : MGraph V E} {P' : Finset E} {w : V}
    {X : Finset V} {e : E} (hint : G.int ⊆ H.int) (hw : w ∈ H.int)
    (hx : (G.ends e).1 ∈ G.int) (hy : (G.ends e).2 ∈ G.int) (hcut : G.Cut X e)
    (hP : e ∈ P' ∧ H.cls e ≠ none ∧
      (H.ends e = G.ends e ∨ ∃ e' ∈ P', H.cls e' ≠ none ∧ H.ends e = ((G.ends e).1, w) ∧
        H.ends e' = (w, (G.ends e).2))) :
    ∃ e'' ∈ P', H.cls e'' ≠ none ∧ (H.ends e'').1 ∈ H.int ∧ (H.ends e'').2 ∈ H.int ∧
      H.Cut X e'' := by
  obtain ⟨hmem, hcl, hends | ⟨e', he', hcl', h1, h2⟩⟩ := hP
  · refine ⟨e, hmem, hcl, ?_, ?_, ?_⟩
    · rw [hends]; exact hint hx
    · rw [hends]; exact hint hy
    · simp only [MGraph.Cut, hends] at hcut ⊢; exact hcut
  · by_cases hcase : ((G.ends e).1 ∈ X ↔ w ∉ X)
    · refine ⟨e, hmem, hcl, ?_, ?_, ?_⟩
      · rw [h1]; exact hint hx
      · rw [h1]; exact hw
      · simp only [MGraph.Cut, h1]; tauto
    · refine ⟨e', he', hcl', ?_, ?_, ?_⟩
      · rw [h2]; exact hw
      · rw [h2]; exact hint hy
      · simp only [MGraph.Cut, h2]
        simp only [MGraph.Cut] at hcut
        tauto

/-- Spanning after an edit. Let `H` be a graph whose internal vertices are those of `G` and
possibly one more vertex `N`, and let `P` be a spanning net of `G`. If every present edge of `P` is
kept in `P'` with the same ends, or is replaced by a path of two edges of `P'` through a vertex `w`
of `H`, and `N`, if new, is joined to an old vertex by an edge of `P'`, then `P'` spans `H`. -/
private theorem spans_edit [DecidableEq V] {G H : MGraph V E} {P P' : Finset E} {N w : V}
    (hG : G.Spans P) (hint : H.int = insert N G.int) (hw : w ∈ H.int)
    (hconn : N ∉ G.int → ∃ y ∈ G.int, ∃ e ∈ P', H.cls e ≠ none ∧
      (H.ends e = (N, y) ∨ H.ends e = (y, N)))
    (hP : ∀ e ∈ P, G.cls e ≠ none → e ∈ P' ∧ H.cls e ≠ none ∧
      (H.ends e = G.ends e ∨ ∃ e' ∈ P', H.cls e' ≠ none ∧ H.ends e = ((G.ends e).1, w) ∧
        H.ends e' = (w, (G.ends e).2))) : H.Spans P' := by
  have hsub : G.int ⊆ H.int := by rw [hint]; exact Finset.subset_insert _ _
  intro X hX hne hnot
  by_cases hN : N ∈ G.int
  · have hHG : H.int = G.int := by rw [hint]; exact Finset.insert_eq_of_mem hN
    rw [hHG] at hX hnot
    obtain ⟨e, he, hc, hx, hy, hcut⟩ := hG X hX hne hnot
    exact step_edit hsub hw hx hy hcut (hP e he hc)
  · by_cases hcase : (X.erase N).Nonempty ∧ ¬ G.int ⊆ X.erase N
    · obtain ⟨hne0, hnot0⟩ := hcase
      have hX0 : X.erase N ⊆ G.int := by
        intro v hv
        obtain ⟨hvN, hvX⟩ := Finset.mem_erase.1 hv
        have := hX hvX
        rw [hint, Finset.mem_insert] at this
        exact this.resolve_left hvN
      obtain ⟨e, he, hc, hx, hy, hcut⟩ := hG _ hX0 hne0 hnot0
      have hxN : (G.ends e).1 ≠ N := fun h => hN (h ▸ hx)
      have hyN : (G.ends e).2 ≠ N := fun h => hN (h ▸ hy)
      have hcutX : G.Cut X e := by
        simp only [MGraph.Cut, Finset.mem_erase] at hcut ⊢
        tauto
      exact step_edit hsub hw hx hy hcutX (hP e he hc)
    · obtain ⟨y, hy, e, he, hcl, hends⟩ := hconn hN
      have hNH : N ∈ H.int := by rw [hint]; exact Finset.mem_insert_self _ _
      have hyH : y ∈ H.int := hsub hy
      have hyN : y ≠ N := fun h => hN (h ▸ hy)
      have hcutXy : (N ∈ X ∧ y ∉ X) ∨ (N ∉ X ∧ y ∈ X) := by
        by_cases hNX : N ∈ X
        · refine Or.inl ⟨hNX, fun hyX => hcase ⟨⟨y, Finset.mem_erase.2 ⟨hyN, hyX⟩⟩, fun hs => ?_⟩⟩
          apply hnot
          intro v hv
          rw [hint, Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · exact hNX
          · exact (Finset.mem_erase.1 (hs hv)).2
        · refine Or.inr ⟨hNX, ?_⟩
          by_contra hyX
          refine hcase ⟨?_, ?_⟩
          · rw [Finset.erase_eq_of_notMem hNX]; exact hne
          · rw [Finset.erase_eq_of_notMem hNX]
            exact fun hs => hyX (hs hy)
      rcases hends with hends | hends
      · refine ⟨e, he, hcl, ?_, ?_, ?_⟩
        · rw [hends]; exact hNH
        · rw [hends]; exact hyH
        · simp only [MGraph.Cut, hends]; exact hcutXy
      · refine ⟨e, he, hcl, ?_, ?_, ?_⟩
        · rw [hends]; exact hyH
        · rw [hends]; exact hNH
        · simp only [MGraph.Cut, hends]; tauto

/-- Nets of a doubly connected graph, the black net of diffusive edges and the blue net of
diffusive, blue solid or ghost edges, that together contain two given edges of class diffusive or
blue solid. -/
private theorem dc_norm {G : MGraph V E} (hG : G.DC) (e₁ e₂ : E)
    (h₁ : G.cls e₁ = some .diff ∨ G.cls e₁ = some .plus)
    (h₂ : G.cls e₂ = some .diff ∨ G.cls e₂ = some .plus) :
    ∃ B L : Finset E, Disjoint B L ∧ (∀ e ∈ B, G.cls e = some .diff) ∧
      (∀ e ∈ L, G.cls e = some .diff ∨ G.cls e = some .plus ∨ G.cls e = some .ghost) ∧
      G.Spans B ∧ G.Spans L ∧ (e₁ ∈ B ∨ e₁ ∈ L) ∧ (e₂ ∈ B ∨ e₂ ∈ L) := by
  classical
  obtain ⟨B, L, hd, hB, hL, hsB, hsL⟩ := hG
  refine ⟨B, (L ∪ {e₁, e₂}) \ B, Finset.disjoint_sdiff, hB, ?_, hsB, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨he, -⟩ := Finset.mem_sdiff.1 he
    rcases Finset.mem_union.1 he with he | he
    · exact hL e he
    · rcases Finset.mem_insert.1 he with rfl | he
      · rcases h₁ with h | h <;> simp [h]
      · rw [Finset.mem_singleton] at he
        subst he
        rcases h₂ with h | h <;> simp [h]
  · refine spans_mono hsL fun e he => Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ he, ?_⟩
    exact fun hb => Finset.disjoint_left.1 hd hb he
  · by_cases h : e₁ ∈ B
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.2 ⟨by simp, h⟩)
  · by_cases h : e₂ ∈ B
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.2 ⟨by simp, h⟩)

/-- The three entries of a list without repetition are pairwise different. -/
private theorem nodup3 {α : Type} {a b c : α} (h : [a, b, c].Nodup) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The four entries of a list without repetition are pairwise different. -/
private theorem nodup4 {α : Type} {a b c d : α} (h : [a, b, c, d].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2, h.2.2⟩

/-- Removing an edge commutes with replacing a different edge by a path. -/
private theorem erase_split [DecidableEq E] (G : MGraph V E) {e b b' : E} (w : V) (h1 : e ≠ b)
    (h2 : e ≠ b') : (G.split b b' w).erase e = (G.erase e).split b b' w := by
  unfold MGraph.erase MGraph.split
  congr 1
  funext f
  by_cases hf : f = e
  · subst hf
    simp [h2]
  · by_cases hf' : f = b'
    · subst hf'
      simp [h2.symm, h1.symm]
    · simp [hf, hf']

/-- Removing an edge commutes with setting a different edge. -/
private theorem erase_setEdge [DecidableEq E] (G : MGraph V E) {e b : E} (u v : V)
    (c : Option MClass) (h : e ≠ b) :
    (G.setEdge b u v c).erase e = (G.erase e).setEdge b u v c := by
  unfold MGraph.erase MGraph.setEdge
  congr 1
  exact Function.update_comm h.symm _ _ _

/-- Removing an edge commutes with adding an internal vertex. -/
private theorem erase_addInt [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e : E) (v : V) :
    (G.addInt v).erase e = (G.erase e).addInt v := rfl

/-! ## [II, Claim A.1] -/

/-- A vertex whose image under the collapse of `S ⊆ G.int` to `s₀ ∈ S` is internal in the
quotient graph is internal. -/
private theorem collapse_mem_int [DecidableEq V] {G : MGraph V E} {S : Finset V} {s₀ : V}
    (hS : S ⊆ G.int) (hs₀ : s₀ ∈ S) {a : V}
    (h : (if a ∈ S then s₀ else a) ∈ (G.collapse S s₀).int) : a ∈ G.int := by
  obtain ⟨a', ha', hfa⟩ := Finset.mem_image.1 h
  by_cases ha : a ∈ S
  · exact hS ha
  · by_cases ha'S : a' ∈ S
    · have : s₀ = a := by simpa only [ha, ha'S, ↓reduceIte] using hfa
      exact absurd (this ▸ hs₀) ha
    · have : a' = a := by simpa only [ha, ha'S, ↓reduceIte] using hfa
      exact this ▸ ha'

/-- A spanning net of `G` spans the quotient graph. -/
private theorem spans_collapse [DecidableEq V] {G : MGraph V E} {S : Finset V} {s₀ : V}
    {B : Finset E} (hB : G.Spans B) : (G.collapse S s₀).Spans B := by
  intro X hX hne hnot
  obtain ⟨x, hx⟩ := hne
  obtain ⟨u, hu, hux⟩ := Finset.mem_image.1 (hX hx)
  obtain ⟨e, he, hc, h1, h2, hcut⟩ := hB
    (G.int.filter fun v => (if v ∈ S then s₀ else v) ∈ X) (Finset.filter_subset _ _)
    ⟨u, Finset.mem_filter.2 ⟨hu, by rw [hux]; exact hx⟩⟩ (by
      intro h
      apply hnot
      intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
      exact (Finset.mem_filter.1 (h hu)).2)
  refine ⟨e, he, hc, Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2, ?_⟩
  have hends : (G.collapse S s₀).ends e = ((if (G.ends e).1 ∈ S then s₀ else (G.ends e).1),
      (if (G.ends e).2 ∈ S then s₀ else (G.ends e).2)) := rfl
  simp only [MGraph.Cut, hends, Finset.mem_filter, h1, h2, true_and] at hcut ⊢
  exact hcut

/-- A present edge of the subgraph induced on `S` has both ends in `S` and its class in `G`. -/
private theorem induce_cls_ne [DecidableEq V] {G : MGraph V E} {S : Finset V} {e : E}
    (h : (G.induce S).cls e ≠ none) :
    ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S) ∧ (G.induce S).cls e = G.cls e := by
  unfold MGraph.induce at h ⊢
  by_cases hin : (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S
  · exact ⟨hin, by simp [hin]⟩
  · exact absurd (by simp [hin]) h

/-- Spanning nets of the quotient graph and of the subgraph induced on `S` give a spanning net of
`G`: the edges of the quotient net that are not inside `S`, together with the edges of the net of
the induced subgraph. -/
private theorem spans_collapse_back [DecidableEq V] [DecidableEq E] {G : MGraph V E}
    {S : Finset V} {s₀ : V} (hS : S ⊆ G.int) (hs₀ : s₀ ∈ S) {B' BS : Finset E}
    (h' : (G.collapse S s₀).Spans B') (hS' : (G.induce S).Spans BS) :
    G.Spans (B'.filter (fun e => ¬ ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S)) ∪ BS) := by
  have fS : ∀ u ∈ S, (if u ∈ S then s₀ else u) = s₀ := fun u hu => by simp [hu]
  have fN : ∀ u ∉ S, (if u ∈ S then s₀ else u) = u := fun u hu => by simp [hu]
  intro X hX hne hnot
  by_cases hsat : S ⊆ X ∨ Disjoint S X
  · have key : ∀ u, (if u ∈ S then s₀ else u) ∈ X ↔ u ∈ X := by
      intro u
      by_cases hu : u ∈ S
      · rw [fS u hu]
        rcases hsat with h | h
        · exact ⟨fun _ => h hu, fun _ => h hs₀⟩
        · exact ⟨fun h' => absurd h' (Finset.disjoint_left.1 h hs₀),
            fun h' => absurd h' (Finset.disjoint_left.1 h hu)⟩
      · rw [fN u hu]
    obtain ⟨x, hx⟩ := hne
    obtain ⟨v, hv, hvX⟩ := Finset.not_subset.1 hnot
    obtain ⟨e, he, hc, h1, h2, hcut⟩ := h' ((G.collapse S s₀).int.filter (· ∈ X))
      (Finset.filter_subset _ _)
      ⟨_, Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (hX hx), (key x).2 hx⟩⟩ (by
        intro h
        exact hvX ((key v).1 (Finset.mem_filter.1 (h (Finset.mem_image_of_mem _ hv))).2))
    have ha : (G.ends e).1 ∈ G.int := collapse_mem_int hS hs₀ h1
    have hc' : (G.ends e).2 ∈ G.int := collapse_mem_int hS hs₀ h2
    have hends : (G.collapse S s₀).ends e = ((if (G.ends e).1 ∈ S then s₀ else (G.ends e).1),
        (if (G.ends e).2 ∈ S then s₀ else (G.ends e).2)) := rfl
    have h1' : (if (G.ends e).1 ∈ S then s₀ else (G.ends e).1) ∈ (G.collapse S s₀).int := h1
    have h2' : (if (G.ends e).2 ∈ S then s₀ else (G.ends e).2) ∈ (G.collapse S s₀).int := h2
    simp only [MGraph.Cut, hends, Finset.mem_filter, h1', h2', true_and] at hcut
    refine ⟨e, Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, fun hin => ?_⟩), hc, ha, hc', ?_⟩
    · rw [fS _ hin.1, fS _ hin.2] at hcut
      tauto
    · simpa only [MGraph.Cut, key] using hcut
  · have hnot1 : ¬ S ⊆ X := fun h => hsat (Or.inl h)
    have hnot2 : ¬ Disjoint S X := fun h => hsat (Or.inr h)
    obtain ⟨v, hvS, hvX⟩ := Finset.not_subset.1 hnot1
    obtain ⟨w, hwS, hwX⟩ := Finset.not_disjoint_iff.1 hnot2
    obtain ⟨e, he, hc, h1, h2, hcut⟩ := hS' (S ∩ X) Finset.inter_subset_left
      ⟨w, Finset.mem_inter.2 ⟨hwS, hwX⟩⟩
      (fun h => hvX (Finset.mem_inter.1 (h hvS)).2)
    obtain ⟨hin, hcls⟩ := induce_cls_ne hc
    refine ⟨e, Finset.mem_union_right _ he, hcls ▸ hc, hS hin.1, hS hin.2, ?_⟩
    have hends : (G.induce S).ends = G.ends := rfl
    simp only [MGraph.Cut, hends, Finset.mem_inter, hin.1, hin.2, true_and] at hcut ⊢
    exact hcut

/-- **[II, Claim A.1]**: if the subgraph induced on the set `S` of internal molecules is doubly
connected, the graph is doubly connected iff the quotient graph `𝒢/𝒮` is. -/
theorem MGraph.claimA1 :
  ∀ (V E : Type) [DecidableEq V] (G : MGraph V E) (S : Finset V) (s₀ : V), S ⊆ G.int →
    s₀ ∈ S → (G.induce S).DC → (G.DC ↔ (G.collapse S s₀).DC) := by
  classical
  intro V E _ G S s₀ hS hs₀ ⟨BS, LS, hdS, hBS, hLS, hsBS, hsLS⟩
  constructor
  · rintro ⟨B, L, hd, hB, hL, hsB, hsL⟩
    exact ⟨B, L, hd, hB, hL, spans_collapse hsB, spans_collapse hsL⟩
  · rintro ⟨B', L', hd, hB, hL, hsB, hsL⟩
    refine ⟨B'.filter (fun e => ¬ ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S)) ∪ BS,
      L'.filter (fun e => ¬ ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S)) ∪ LS, ?_, ?_, ?_,
      spans_collapse_back hS hs₀ hsB hsBS, spans_collapse_back hS hs₀ hsL hsLS⟩
    · rw [Finset.disjoint_left]
      intro e he he'
      rcases Finset.mem_union.1 he with he | he <;> rcases Finset.mem_union.1 he' with he' | he'
      · exact Finset.disjoint_left.1 hd (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he').1
      · refine (Finset.mem_filter.1 he).2 (induce_cls_ne (e := e) ?_).1
        rcases hLS e he' with h | h | h <;> rw [h] <;> simp
      · refine (Finset.mem_filter.1 he').2 (induce_cls_ne (e := e) ?_).1
        rw [hBS e he]; simp
      · exact Finset.disjoint_left.1 hdS he he'
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · exact hB e (Finset.mem_filter.1 he).1
      · have h := hBS e he
        rw [(induce_cls_ne (e := e) (by rw [h]; simp)).2] at h
        exact h
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · exact hL e (Finset.mem_filter.1 he).1
      · have h := hLS e he
        rw [(induce_cls_ne (e := e) (by rcases h with h | h | h <;> rw [h] <;> simp)).2] at h
        exact h

/-! ## [II, Claim A.3] -/

/-- A diffusive or blue solid edge `b` of a doubly connected graph replaced by a path `b`, `b'`
through a new vertex `N`, and `N` joined to an old internal vertex `M` by a diffusive edge `f`:
the graph is doubly connected. The graph `H` is described by its ends and classes. -/
private theorem dc_pathleaf [DecidableEq V] {G H : MGraph V E} (hG : G.DC)
    {N M : V} {b b' f : E} (hM : M ∈ G.int) (hy : (G.ends b).2 ∈ G.int)
    (hint : H.int = insert N G.int)
    (hb : G.cls b = some .diff ∨ G.cls b = some .plus) (hb' : G.cls b' = none)
    (hf : G.cls f = none) (hbb' : b ≠ b') (hb'f : b' ≠ f)
    (hframe : ∀ e, G.cls e ≠ none → e ≠ b → H.ends e = G.ends e ∧ H.cls e = G.cls e)
    (hHb : H.ends b = ((G.ends b).1, N) ∧ H.cls b = G.cls b)
    (hHb' : H.ends b' = (N, (G.ends b).2) ∧ H.cls b' = G.cls b)
    (hHf : H.ends f = (N, M) ∧ H.cls f = some .diff) : H.DC := by
  classical
  obtain ⟨B, L, hd, hB, hL, hsB, hsL, hbm, -⟩ := dc_norm hG b b hb hb
  have hcb : G.cls b ≠ none := by rcases hb with h | h <;> rw [h] <;> simp
  have hNH : N ∈ H.int := by rw [hint]; exact Finset.mem_insert_self _ _
  have hcl : ∀ e, G.cls e ≠ none → H.cls e = G.cls e := by
    intro e he
    by_cases heb : e = b
    · subst heb; exact hHb.2
    · exact (hframe e he heb).2
  have hnB : ∀ e ∈ B, G.cls e ≠ none := fun e he => by rw [hB e he]; simp
  have hnL : ∀ e ∈ L, G.cls e ≠ none := fun e he => by
    rcases hL e he with h | h | h <;> rw [h] <;> simp
  have hb'B : b' ∉ B := fun h => hb' ▸ hnB b' h <| rfl
  have hb'L : b' ∉ L := fun h => hb' ▸ hnL b' h <| rfl
  have hfB : f ∉ B := fun h => hf ▸ hnB f h <| rfl
  have hfL : f ∉ L := fun h => hf ▸ hnL f h <| rfl
  have key : ∀ P P' : Finset E, G.Spans P → (∀ e ∈ P, e ∈ P') → (b ∈ P → b' ∈ P') →
      (f ∈ P' ∨ b' ∈ P') → H.Spans P' := by
    intro P P' hP hsub hbP hc
    refine spans_edit (N := N) (w := N) hP hint hNH ?_ fun e he hce => ?_
    · intro _
      rcases hc with hc | hc
      · exact ⟨M, hM, f, hc, by rw [hHf.2]; simp, Or.inl hHf.1⟩
      · exact ⟨(G.ends b).2, hy, b', hc, by rw [hHb'.2]; exact hcb, Or.inl hHb'.1⟩
    · refine ⟨hsub e he, by rw [hcl e hce]; exact hce, ?_⟩
      by_cases heb : e = b
      · subst heb
        exact Or.inr ⟨b', hbP he, by rw [hHb'.2]; exact hcb, hHb.1, hHb'.1⟩
      · exact Or.inl (hframe e hce heb).1
  by_cases hbL : b ∈ L
  · have hbB : b ∉ B := fun h => Finset.disjoint_left.1 hd h hbL
    refine ⟨insert f B, insert b' L, ?_, ?_, ?_,
      key B (insert f B) hsB (fun e he => Finset.mem_insert_of_mem he)
        (fun h => absurd h hbB) (Or.inl (Finset.mem_insert_self _ _)),
      key L (insert b' L) hsL (fun e he => Finset.mem_insert_of_mem he)
        (fun _ => Finset.mem_insert_self _ _) (Or.inr (Finset.mem_insert_self _ _))⟩
    · rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
      refine ⟨?_, hb'B, hd⟩
      rw [Finset.mem_insert]
      exact fun h => h.elim (fun h => hb'f h.symm) hfL
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact hHf.2
      · rw [hcl e (hnB e he)]; exact hB e he
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · rw [hHb'.2]
        rcases hb with h | h <;> rw [h] <;> simp
      · rw [hcl e (hnL e he)]; exact hL e he
  · have hbB : b ∈ B := hbm.resolve_right hbL
    refine ⟨insert b' B, insert f L, ?_, ?_, ?_,
      key B (insert b' B) hsB (fun e he => Finset.mem_insert_of_mem he)
        (fun _ => Finset.mem_insert_self _ _) (Or.inr (Finset.mem_insert_self _ _)),
      key L (insert f L) hsL (fun e he => Finset.mem_insert_of_mem he)
        (fun h => absurd h hbL) (Or.inl (Finset.mem_insert_self _ _))⟩
    · rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
      refine ⟨?_, hfB, hd⟩
      rw [Finset.mem_insert]
      exact fun h => h.elim (fun h => hb'f h) hb'L
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · rw [hHb'.2]; exact hB b hbB
      · rw [hcl e (hnB e he)]; exact hB e he
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · rw [hHf.2]; simp
      · rw [hcl e (hnL e he)]; exact hL e he

/-- The graph of [II, Claim A.3], with the edge `b₂` of any class, is doubly connected: the edge
`b₂` is in neither net. -/
private theorem dc_A3 [DecidableEq V] [DecidableEq E] {G : MGraph V E} (hG : G.DC)
    {N M₁ M₂ : V} {b b₁ b₂ b₄ : E} (c : Option MClass) (hM₁ : M₁ ∈ G.int)
    (hbp : G.cls b = some .plus) (hy : (G.ends b).2 ∈ G.int) (hnd : [b, b₁, b₂, b₄].Nodup)
    (hb₁ : G.cls b₁ = none) (hb₂ : G.cls b₂ = none) (hb₄ : G.cls b₄ = none) :
    ((((G.addInt N).split b b₄ N).setEdge b₁ N M₁ (some .diff)).setEdge b₂ N M₂ c).DC := by
  obtain ⟨h1, h2, h4, h12, h14, h24⟩ := nodup4 hnd
  refine dc_pathleaf (N := N) (M := M₁) (b := b) (b' := b₄) (f := b₁) hG hM₁ hy ?_
    (Or.inr hbp) hb₄ hb₁ h4 h14.symm ?_ ?_ ?_ ?_
  · rfl
  · intro e he heb
    have he1 : e ≠ b₁ := fun h => he (h ▸ hb₁)
    have he2 : e ≠ b₂ := fun h => he (h ▸ hb₂)
    have he4 : e ≠ b₄ := fun h => he (h ▸ hb₄)
    simp [MGraph.setEdge, MGraph.split, MGraph.addInt, heb, he1, he2, he4]
  · simp [MGraph.setEdge, MGraph.split, MGraph.addInt, h1, h2, h4]
  · simp [MGraph.setEdge, MGraph.split, MGraph.addInt, h4.symm, h14.symm, h24.symm]
  · simp [MGraph.setEdge, MGraph.split, MGraph.addInt, h12]

/-- **[II, Claim A.3]**: in a doubly connected graph, a new molecule `N` with a `Θ` edge `b₁` to
`M₁` and a blue solid edge `b₂` to `M₂`, and the blue solid edge `b` between internal molecules
replaced by a path `b`, `b₄` through `N`: the edge `b₂` is redundant. -/
theorem MGraph.claimA3 :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (N M₁ M₂ : V)
    (b b₁ b₂ b₄ : E), G.DC → N ∉ G.int → N ∉ G.ext → M₁ ∈ G.int → M₂ ∈ G.int →
    G.cls b = some .plus → (G.ends b).1 ∈ G.int → (G.ends b).2 ∈ G.int → [b, b₁, b₂, b₄].Nodup →
    G.cls b₁ = none → G.cls b₂ = none → G.cls b₄ = none →
    ((((G.addInt N).split b b₄ N).setEdge b₁ N M₁ (some .diff)).setEdge b₂ N M₂
      (some .plus)).IsRedundant b₂ := by
  intro V E _ _ G N M₁ M₂ b b₁ b₂ b₄ hdc _ _ hM₁ _ hbp _ hby hnd hb₁ hb₂ hb₄
  refine ⟨by simp [MGraph.setEdge], dc_A3 hdc _ hM₁ hbp hby hnd hb₁ hb₂ hb₄, ?_⟩
  have : (((((G.addInt N).split b b₄ N).setEdge b₁ N M₁ (some .diff)).setEdge b₂ N M₂
      (some .plus)).erase b₂) =
      ((((G.addInt N).split b b₄ N).setEdge b₁ N M₁ (some .diff)).setEdge b₂ N M₂ none) := by
    unfold MGraph.erase MGraph.setEdge
    simp
  rw [this]
  exact dc_A3 hdc _ hM₁ hbp hby hnd hb₁ hb₂ hb₄

/-! ## [II, Claim A.5] -/

/-- The ends and classes of the edges of the graph `G.twoSplit N b₀ b₂ b b₄`. -/
private theorem twoSplit_facts [DecidableEq V] [DecidableEq E] (G : MGraph V E) (N : V)
    {b₀ b₂ b b₄ : E} (hnd : [b₀, b₂, b, b₄].Nodup) (h0 : G.cls b₀ = some .diff)
    (hb : G.cls b = some .diff) :
    (G.twoSplit N b₀ b₂ b b₄).int = insert N G.int ∧
    (G.twoSplit N b₀ b₂ b b₄).ends b₀ = ((G.ends b₀).1, N) ∧
    (G.twoSplit N b₀ b₂ b b₄).ends b₂ = (N, (G.ends b₀).2) ∧
    (G.twoSplit N b₀ b₂ b b₄).ends b = ((G.ends b).1, N) ∧
    (G.twoSplit N b₀ b₂ b b₄).ends b₄ = (N, (G.ends b).2) ∧
    (∀ e, e ≠ b₀ → e ≠ b₂ → e ≠ b → e ≠ b₄ → (G.twoSplit N b₀ b₂ b b₄).ends e = G.ends e) ∧
    (G.twoSplit N b₀ b₂ b b₄).cls b₂ = some .diff ∧
    (G.twoSplit N b₀ b₂ b b₄).cls b₄ = some .diff ∧
    (∀ e, e ≠ b₂ → e ≠ b₄ → (G.twoSplit N b₀ b₂ b b₄).cls e = G.cls e) := by
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := nodup4 hnd
  have h20 := h02.symm
  have hb0 := h0b.symm
  have h40 := h04.symm
  have hb2 := h2b.symm
  have h42 := h24.symm
  have h4b := hb4.symm
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h0b, h04, hb0, hb2]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h20, h2b, h24, hb0, hb2]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, hb0, hb2]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, hb0, hb2, h4b]
  · intro e e0 e2 eb e4
    simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, e0, e2, eb, e4]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, h0, h24]
  · simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, hb, hb2]
  · intro e e2 e4
    simp [MGraph.twoSplit, MGraph.split, MGraph.addInt, e2, e4]

/-- Spanning in the graph `G.twoSplit N b₀ b₂ b b₄`: a set `P'` of edges spans if it contains a
spanning net `P` of `G`, the new halves `b₂`, `b₄` of the edges `b₀`, `b` of `P`, and an edge at
`N`. -/
private theorem twoSplit_spans [DecidableEq V] [DecidableEq E] {G : MGraph V E} {N : V}
    {b₀ b₂ b b₄ : E} (hnd : [b₀, b₂, b, b₄].Nodup) (h0 : G.cls b₀ = some .diff)
    (hb : G.cls b = some .diff) (hx₀ : (G.ends b₀).1 ∈ G.int) (hy₀ : (G.ends b₀).2 ∈ G.int)
    (hx : (G.ends b).1 ∈ G.int) (hy : (G.ends b).2 ∈ G.int) (h2 : G.cls b₂ = none)
    {P P' : Finset E} (hP : G.Spans P) (hsub : ∀ e ∈ P, e ∈ P') (h₀ : b₀ ∈ P → b₂ ∈ P')
    (h₁ : b ∈ P → b₄ ∈ P') (hc : b₀ ∈ P' ∨ b₂ ∈ P' ∨ b ∈ P' ∨ b₄ ∈ P') (h4 : G.cls b₄ = none) :
    (G.twoSplit N b₀ b₂ b b₄).Spans P' := by
  obtain ⟨hint, he0, he2, heb, he4, heo, hc2, hc4, hco⟩ := twoSplit_facts G N hnd h0 hb
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := nodup4 hnd
  have hNH : N ∈ (G.twoSplit N b₀ b₂ b b₄).int := by
    rw [hint]; exact Finset.mem_insert_self _ _
  have hc0 : (G.twoSplit N b₀ b₂ b b₄).cls b₀ ≠ none := by
    rw [hco b₀ h02 h04, h0]; simp
  have hcb : (G.twoSplit N b₀ b₂ b b₄).cls b ≠ none := by
    rw [hco b h2b.symm hb4, hb]; simp
  refine spans_edit (N := N) (w := N) hP hint hNH ?_ fun e he hce => ?_
  · intro _
    rcases hc with h | h | h | h
    · exact ⟨_, hx₀, b₀, h, hc0, Or.inr he0⟩
    · exact ⟨_, hy₀, b₂, h, by rw [hc2]; simp, Or.inl he2⟩
    · exact ⟨_, hx, b, h, hcb, Or.inr heb⟩
    · exact ⟨_, hy, b₄, h, by rw [hc4]; simp, Or.inl he4⟩
  · have e2 : e ≠ b₂ := fun h => hce (h ▸ h2)
    have e4 : e ≠ b₄ := fun h => hce (h ▸ h4)
    refine ⟨hsub e he, by rw [hco e e2 e4]; exact hce, ?_⟩
    by_cases e0 : e = b₀
    · subst e0
      exact Or.inr ⟨b₂, h₀ he, by rw [hc2]; simp, he0, he2⟩
    · by_cases eb : e = b
      · subst eb
        exact Or.inr ⟨b₄, h₁ he, by rw [hc4]; simp, heb, he4⟩
      · exact Or.inl (heo e e0 e2 eb e4)

/-- If a set `P` of edges does not span a graph whose internal vertices are those of `I` and a
vertex `N`, then some nonempty subset `T` of `I` is cut by no present edge of `P` between internal
vertices. -/
private theorem not_spans_out [DecidableEq V] {H : MGraph V E} {P : Finset E} {N : V}
    {I : Finset V} (hint : H.int = insert N I) (h : ¬ H.Spans P) :
    ∃ T : Finset V, T ⊆ I ∧ T.Nonempty ∧ ∀ e ∈ P, H.cls e ≠ none → (H.ends e).1 ∈ H.int →
      (H.ends e).2 ∈ H.int → ¬ H.Cut T e := by
  have h' : ∃ S : Finset V, S ⊆ H.int ∧ S.Nonempty ∧ ¬ H.int ⊆ S ∧ ∀ e ∈ P, H.cls e ≠ none →
      (H.ends e).1 ∈ H.int → (H.ends e).2 ∈ H.int → ¬ H.Cut S e := by
    by_contra hc
    apply h
    intro S hS hne hnot
    by_contra hex
    exact hc ⟨S, hS, hne, hnot, fun e he hc hx hy hcut => hex ⟨e, he, hc, hx, hy, hcut⟩⟩
  obtain ⟨S, hS, hne, hnot, hS'⟩ := h'
  by_cases hNS : N ∈ S
  · refine ⟨H.int \ S, ?_, ?_, fun e he hc hx hy hcut => hS' e he hc hx hy ?_⟩
    · intro v hv
      obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.1 hv
      rw [hint, Finset.mem_insert] at hv1
      exact hv1.resolve_left fun h => hv2 (h ▸ hNS)
    · obtain ⟨v, hv, hv'⟩ := Finset.not_subset.1 hnot
      exact ⟨v, Finset.mem_sdiff.2 ⟨hv, hv'⟩⟩
    · simp only [MGraph.Cut, Finset.mem_sdiff] at hcut ⊢
      tauto
  · refine ⟨S, ?_, hne, hS'⟩
    intro v hv
    have := hS hv
    rw [hint, Finset.mem_insert] at this
    exact this.resolve_left fun h => hNS (h ▸ hv)

/-- If neither of two sets cuts an edge, then neither does their union. -/
private theorem cut_union_aux {a₁ a₂ c₁ c₂ : Prop}
    (h₁ : ¬ ((a₁ ∧ ¬ c₁) ∨ (¬ a₁ ∧ c₁))) (h₂ : ¬ ((a₂ ∧ ¬ c₂) ∨ (¬ a₂ ∧ c₂))) :
    ¬ (((a₁ ∨ a₂) ∧ ¬ (c₁ ∨ c₂)) ∨ (¬ (a₁ ∨ a₂) ∧ (c₁ ∨ c₂))) := by
  tauto

/-- The combinatorial step of [II, Claim A.5], for two edges `b₀`, `b` in one spanning net `X` of
`G`: in `G.twoSplit N b₀ b₂ b b₄`, the four edges `b₀`, `b₂`, `b`, `b₄` together with the other
edges of `X` form a set of which one of `b₀`, `b₂` can be removed so that the rest spans. -/
private theorem twoSplit_same_net [DecidableEq V] [DecidableEq E] {G : MGraph V E} {N : V}
    {b₀ b₂ b b₄ : E} {X : Finset E} (hnd : [b₀, b₂, b, b₄].Nodup) (hN : N ∉ G.int)
    (h0 : G.cls b₀ = some .diff) (hb : G.cls b = some .diff) (hx₀ : (G.ends b₀).1 ∈ G.int)
    (hy₀ : (G.ends b₀).2 ∈ G.int) (hx : (G.ends b).1 ∈ G.int) (hy : (G.ends b).2 ∈ G.int)
    (h2 : G.cls b₂ = none) (h4 : G.cls b₄ = none) (hX : G.Spans X)
    (hXc : ∀ e ∈ X, G.cls e ≠ none) (hb₀X : b₀ ∈ X) (hbX : b ∈ X) :
    (G.twoSplit N b₀ b₂ b b₄).Spans ((insert b₂ (insert b₄ X)).erase b₀) ∨
      (G.twoSplit N b₀ b₂ b b₄).Spans ((insert b₂ (insert b₄ X)).erase b₂) := by
  obtain ⟨hint, he0, he2, heb, he4, heo, hc2, hc4, hco⟩ := twoSplit_facts G N hnd h0 hb
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := nodup4 hnd
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  obtain ⟨T₁, hT₁, hne₁, hc₁⟩ := not_spans_out hint hn1
  obtain ⟨T₂, hT₂, hne₂, hc₂⟩ := not_spans_out hint hn2
  have hNT₁ : N ∉ T₁ := fun h => hN (hT₁ h)
  have hNT₂ : N ∉ T₂ := fun h => hN (hT₂ h)
  have hsub : G.int ⊆ (G.twoSplit N b₀ b₂ b b₄).int := by
    rw [hint]; exact Finset.subset_insert _ _
  have hNH : N ∈ (G.twoSplit N b₀ b₂ b b₄).int := by
    rw [hint]; exact Finset.mem_insert_self _ _
  have hn2c : (G.twoSplit N b₀ b₂ b b₄).cls b₂ ≠ none := by rw [hc2]; simp
  have hn4c : (G.twoSplit N b₀ b₂ b b₄).cls b₄ ≠ none := by rw [hc4]; simp
  have hn0c : (G.twoSplit N b₀ b₂ b b₄).cls b₀ ≠ none := by rw [hco b₀ h02 h04, h0]; simp
  have hnbc : (G.twoSplit N b₀ b₂ b b₄).cls b ≠ none := by rw [hco b h2b.symm hb4, hb]; simp
  -- the other edges of `X` are unchanged
  have hnot2 : ∀ e ∈ X, e ≠ b₂ := fun e he h => hXc e he (h ▸ h2)
  have hnot4 : ∀ e ∈ X, e ≠ b₄ := fun e he h => hXc e he (h ▸ h4)
  have hcutG : ∀ e ∈ X, e ≠ b₀ → e ≠ b → ∀ T,
      ((G.twoSplit N b₀ b₂ b b₄).Cut T e ↔ G.Cut T e) := by
    intro e he e0 eb T
    simp only [MGraph.Cut, heo e e0 (hnot2 e he) eb (hnot4 e he)]
  -- a set that no other edge of `X` cuts is cut by `b₀` or `b`
  have special : ∀ T : Finset V, T ⊆ G.int → T.Nonempty → ¬ G.int ⊆ T →
      (∀ e ∈ X, e ≠ b₀ → e ≠ b → G.cls e ≠ none → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int →
        ¬ G.Cut T e) → G.Cut T b₀ ∨ G.Cut T b := by
    intro T hT hne hnot hno
    obtain ⟨e, he, hc, hx', hy', hcut⟩ := hX T hT hne hnot
    by_cases e0 : e = b₀
    · subst e0; exact Or.inl hcut
    · by_cases eb : e = b
      · subst eb; exact Or.inr hcut
      · exact absurd hcut (hno e he e0 eb hc hx' hy')
  have hmem : ∀ e ∈ X, e ≠ b₀ → e ∈ (insert b₂ (insert b₄ X)).erase b₀ := fun e he e0 =>
    Finset.mem_erase.2 ⟨e0, by simp [he]⟩
  have hmem' : ∀ e ∈ X, e ≠ b₂ → e ∈ (insert b₂ (insert b₄ X)).erase b₂ := fun e he e2 =>
    Finset.mem_erase.2 ⟨e2, by simp [he]⟩
  have hother1 : ∀ e ∈ X, e ≠ b₀ → e ≠ b → G.cls e ≠ none → (G.ends e).1 ∈ G.int →
      (G.ends e).2 ∈ G.int → ¬ G.Cut T₁ e := by
    intro e he e0 eb hc hx' hy' hcut
    have e2 := hnot2 e he
    have e4 := hnot4 e he
    refine hc₁ e (hmem e he e0) (by rw [hco e e2 e4]; exact hc) ?_ ?_
      ((hcutG e he e0 eb T₁).2 hcut)
    · rw [heo e e0 e2 eb e4]; exact hsub hx'
    · rw [heo e e0 e2 eb e4]; exact hsub hy'
  have hother2 : ∀ e ∈ X, e ≠ b₀ → e ≠ b → G.cls e ≠ none → (G.ends e).1 ∈ G.int →
      (G.ends e).2 ∈ G.int → ¬ G.Cut T₂ e := by
    intro e he e0 eb hc hx' hy' hcut
    have e2 := hnot2 e he
    have e4 := hnot4 e he
    refine hc₂ e (hmem' e he e2) (by rw [hco e e2 e4]; exact hc) ?_ ?_
      ((hcutG e he e0 eb T₂).2 hcut)
    · rw [heo e e0 e2 eb e4]; exact hsub hx'
    · rw [heo e e0 e2 eb e4]; exact hsub hy'
  -- the first set: `b₂`, `b`, `b₄` are not cut
  have hy₀T₁ : (G.ends b₀).2 ∉ T₁ := by
    have := hc₁ b₂ (Finset.mem_erase.2 ⟨h02.symm, by simp⟩) hn2c (by rw [he2]; exact hNH)
      (by rw [he2]; exact hsub hy₀)
    simp only [MGraph.Cut, he2] at this
    exact fun h => this (Or.inr ⟨hNT₁, h⟩)
  have hxT₁ : (G.ends b).1 ∉ T₁ := by
    have := hc₁ b (Finset.mem_erase.2 ⟨h0b.symm, by simp [hbX]⟩) hnbc (by rw [heb]; exact hsub hx)
      (by rw [heb]; exact hNH)
    simp only [MGraph.Cut, heb] at this
    exact fun h => this (Or.inl ⟨h, hNT₁⟩)
  have hyT₁ : (G.ends b).2 ∉ T₁ := by
    have := hc₁ b₄ (Finset.mem_erase.2 ⟨h04.symm, by simp⟩) hn4c (by rw [he4]; exact hNH)
      (by rw [he4]; exact hsub hy)
    simp only [MGraph.Cut, he4] at this
    exact fun h => this (Or.inr ⟨hNT₁, h⟩)
  have hx₀T₁ : (G.ends b₀).1 ∈ T₁ := by
    rcases special T₁ hT₁ hne₁ (fun h => hy₀T₁ (h hy₀)) hother1 with h | h
    · simp only [MGraph.Cut] at h
      tauto
    · simp only [MGraph.Cut] at h
      tauto
  -- the second set: `b₀`, `b`, `b₄` are not cut
  have hx₀T₂ : (G.ends b₀).1 ∉ T₂ := by
    have := hc₂ b₀ (Finset.mem_erase.2 ⟨h02, by simp [hb₀X]⟩) hn0c (by rw [he0]; exact hsub hx₀)
      (by rw [he0]; exact hNH)
    simp only [MGraph.Cut, he0] at this
    exact fun h => this (Or.inl ⟨h, hNT₂⟩)
  have hxT₂ : (G.ends b).1 ∉ T₂ := by
    have := hc₂ b (Finset.mem_erase.2 ⟨h2b.symm, by simp [hbX]⟩) hnbc (by rw [heb]; exact hsub hx)
      (by rw [heb]; exact hNH)
    simp only [MGraph.Cut, heb] at this
    exact fun h => this (Or.inl ⟨h, hNT₂⟩)
  have hyT₂ : (G.ends b).2 ∉ T₂ := by
    have := hc₂ b₄ (Finset.mem_erase.2 ⟨h24.symm, by simp⟩) hn4c (by rw [he4]; exact hNH)
      (by rw [he4]; exact hsub hy)
    simp only [MGraph.Cut, he4] at this
    exact fun h => this (Or.inr ⟨hNT₂, h⟩)
  have hy₀T₂ : (G.ends b₀).2 ∈ T₂ := by
    rcases special T₂ hT₂ hne₂ (fun h => hx₀T₂ (h hx₀)) hother2 with h | h
    · simp only [MGraph.Cut] at h
      tauto
    · simp only [MGraph.Cut] at h
      tauto
  -- the union of the two sets is cut by no edge of `X`
  have hU : G.Cut (T₁ ∪ T₂) b₀ ∨ G.Cut (T₁ ∪ T₂) b := by
    refine special (T₁ ∪ T₂) (Finset.union_subset hT₁ hT₂) (hne₁.mono Finset.subset_union_left)
      (fun h => ?_) fun e he e0 eb hc hx' hy' hcut => ?_
    · exact (Finset.mem_union.1 (h hx)).elim hxT₁ hxT₂
    · have c1 := hother1 e he e0 eb hc hx' hy'
      have c2 := hother2 e he e0 eb hc hx' hy'
      simp only [MGraph.Cut, Finset.mem_union] at hcut c1 c2
      exact cut_union_aux c1 c2 hcut
  rcases hU with h | h
  · simp only [MGraph.Cut, Finset.mem_union] at h
    exact h.elim (fun h => h.2 (Or.inr hy₀T₂)) fun h => h.1 (Or.inl hx₀T₁)
  · simp only [MGraph.Cut, Finset.mem_union] at h
    exact h.elim (fun h => h.1.elim hxT₁ hxT₂) fun h => h.2.elim hyT₁ hyT₂

/-- The case of [II, Claim A.5] with both edges in one net `X`: the nets of the new graph, from
the spanning nets `X`, `Y` of `G` with `b₀`, `b` in `X`. -/
private theorem twoSplit_hard [DecidableEq V] [DecidableEq E] {G : MGraph V E} {N : V}
    {b₀ b₂ b b₄ : E} {X Y : Finset E} (hnd : [b₀, b₂, b, b₄].Nodup) (hN : N ∉ G.int)
    (h0 : G.cls b₀ = some .diff) (hb : G.cls b = some .diff) (hx₀ : (G.ends b₀).1 ∈ G.int)
    (hy₀ : (G.ends b₀).2 ∈ G.int) (hx : (G.ends b).1 ∈ G.int) (hy : (G.ends b).2 ∈ G.int)
    (h2 : G.cls b₂ = none) (h4 : G.cls b₄ = none) (hX : G.Spans X) (hY : G.Spans Y)
    (hXY : Disjoint X Y) (hXc : ∀ e ∈ X, G.cls e ≠ none) (hYc : ∀ e ∈ Y, G.cls e ≠ none)
    (hb₀X : b₀ ∈ X) (hbX : b ∈ X) :
    ∃ X' Y' : Finset E, (G.twoSplit N b₀ b₂ b b₄).Spans X' ∧ (G.twoSplit N b₀ b₂ b b₄).Spans Y' ∧
      Disjoint X' Y' ∧ (∀ e ∈ X', e ∈ X ∨ e = b₂ ∨ e = b₄) ∧
        (∀ e ∈ Y', e ∈ Y ∨ e = b₀ ∨ e = b₂) := by
  have b₀Y : b₀ ∉ Y := fun h => Finset.disjoint_left.1 hXY hb₀X h
  have bY : b ∉ Y := fun h => Finset.disjoint_left.1 hXY hbX h
  have b₂Y : b₂ ∉ Y := fun h => hYc b₂ h h2
  have b₄Y : b₄ ∉ Y := fun h => hYc b₄ h h4
  have fin : ∀ f, (f = b₀ ∨ f = b₂) →
      (G.twoSplit N b₀ b₂ b b₄).Spans ((insert b₂ (insert b₄ X)).erase f) →
      ∃ X' Y' : Finset E, (G.twoSplit N b₀ b₂ b b₄).Spans X' ∧
        (G.twoSplit N b₀ b₂ b b₄).Spans Y' ∧ Disjoint X' Y' ∧ (∀ e ∈ X', e ∈ X ∨ e = b₂ ∨ e = b₄) ∧
        (∀ e ∈ Y', e ∈ Y ∨ e = b₀ ∨ e = b₂) := by
    intro f hf hs
    refine ⟨_, insert f Y, hs, ?_, ?_, ?_, ?_⟩
    · refine twoSplit_spans hnd h0 hb hx₀ hy₀ hx hy h2 hY (fun e he => Finset.mem_insert_of_mem he)
        (fun h => absurd h b₀Y) (fun h => absurd h bY) ?_ h4
      rcases hf with rfl | rfl
      · exact Or.inl (Finset.mem_insert_self _ _)
      · exact Or.inr (Or.inl (Finset.mem_insert_self _ _))
    · rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨hef, he⟩ := Finset.mem_erase.1 he
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact hef rfl
      · rcases Finset.mem_insert.1 he with rfl | he
        · exact b₂Y he'
        · rcases Finset.mem_insert.1 he with rfl | he
          · exact b₄Y he'
          · exact Finset.disjoint_left.1 hXY he he'
    · intro e he
      obtain ⟨-, he⟩ := Finset.mem_erase.1 he
      rcases Finset.mem_insert.1 he with h | he
      · exact Or.inr (Or.inl h)
      · rcases Finset.mem_insert.1 he with h | he
        · exact Or.inr (Or.inr h)
        · exact Or.inl he
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · rcases hf with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exact Or.inl he
  rcases twoSplit_same_net hnd hN h0 hb hx₀ hy₀ hx hy h2 h4 hX hXc hb₀X hbX with hs | hs
  · exact fin b₀ (Or.inl rfl) hs
  · exact fin b₂ (Or.inr rfl) hs

/-- The graph `G.twoSplit N b₀ b₂ b b₄` of a doubly connected graph, with `b₀`, `b` diffusive edges
between internal vertices, is doubly connected. -/
private theorem dc_twoSplit [DecidableEq V] [DecidableEq E] {G : MGraph V E} {N : V}
    {b₀ b₂ b b₄ : E} (hG : G.DC) (hnd : [b₀, b₂, b, b₄].Nodup) (hN : N ∉ G.int)
    (h0 : G.cls b₀ = some .diff) (hb : G.cls b = some .diff) (hx₀ : (G.ends b₀).1 ∈ G.int)
    (hy₀ : (G.ends b₀).2 ∈ G.int) (hx : (G.ends b).1 ∈ G.int) (hy : (G.ends b).2 ∈ G.int)
    (h2 : G.cls b₂ = none) (h4 : G.cls b₄ = none) : (G.twoSplit N b₀ b₂ b b₄).DC := by
  obtain ⟨B, L, hd, hB, hL, hsB, hsL, hm0, hmb⟩ := dc_norm hG b₀ b (Or.inl h0) (Or.inl hb)
  obtain ⟨hint, he0, he2, heb, he4, heo, hc2, hc4, hco⟩ := twoSplit_facts G N hnd h0 hb
  obtain ⟨h02, h0b, h04, h2b, h24, hb4⟩ := nodup4 hnd
  have hnB : ∀ e ∈ B, G.cls e ≠ none := fun e he => by rw [hB e he]; simp
  have hnL : ∀ e ∈ L, G.cls e ≠ none := fun e he => by
    rcases hL e he with h | h | h <;> rw [h] <;> simp
  have b₂B : b₂ ∉ B := fun h => hnB b₂ h h2
  have b₄B : b₄ ∉ B := fun h => hnB b₄ h h4
  have b₂L : b₂ ∉ L := fun h => hnL b₂ h h2
  have b₄L : b₄ ∉ L := fun h => hnL b₄ h h4
  have hcold : ∀ e, G.cls e ≠ none → (G.twoSplit N b₀ b₂ b b₄).cls e = G.cls e := fun e he =>
    hco e (fun h => he (h ▸ h2)) (fun h => he (h ▸ h4))
  have hdiff : ∀ e, (e = b₀ ∨ e = b₂ ∨ e = b ∨ e = b₄) →
      (G.twoSplit N b₀ b₂ b b₄).cls e = some .diff := by
    rintro e (rfl | rfl | rfl | rfl)
    · rw [hcold _ (by rw [h0]; simp), h0]
    · exact hc2
    · rw [hcold _ (by rw [hb]; simp), hb]
    · exact hc4
  have mk : ∀ B' L' : Finset E, Disjoint B' L' →
      (∀ e ∈ B', e ∈ B ∨ e = b₀ ∨ e = b₂ ∨ e = b ∨ e = b₄) →
      (∀ e ∈ L', e ∈ L ∨ e = b₀ ∨ e = b₂ ∨ e = b ∨ e = b₄) →
      (G.twoSplit N b₀ b₂ b b₄).Spans B' → (G.twoSplit N b₀ b₂ b b₄).Spans L' →
      (G.twoSplit N b₀ b₂ b b₄).DC := by
    intro B' L' hdis hB' hL' sB sL
    refine ⟨B', L', hdis, fun e he => ?_, fun e he => ?_, sB, sL⟩
    · rcases hB' e he with h | h | h | h | h
      · rw [hcold e (hnB e h)]; exact hB e h
      · exact hdiff e (Or.inl h)
      · exact hdiff e (Or.inr (Or.inl h))
      · exact hdiff e (Or.inr (Or.inr (Or.inl h)))
      · exact hdiff e (Or.inr (Or.inr (Or.inr h)))
    · rcases hL' e he with h | h | h | h | h
      · rw [hcold e (hnL e h)]; exact hL e h
      · rw [hdiff e (Or.inl h)]; simp
      · rw [hdiff e (Or.inr (Or.inl h))]; simp
      · rw [hdiff e (Or.inr (Or.inr (Or.inl h)))]; simp
      · rw [hdiff e (Or.inr (Or.inr (Or.inr h)))]; simp
  have sp : ∀ {P P' : Finset E}, G.Spans P → (∀ e ∈ P, e ∈ P') → (b₀ ∈ P → b₂ ∈ P') →
      (b ∈ P → b₄ ∈ P') → (b₀ ∈ P' ∨ b₂ ∈ P' ∨ b ∈ P' ∨ b₄ ∈ P') →
      (G.twoSplit N b₀ b₂ b b₄).Spans P' := fun hP hsub h₀ h₁ hc =>
    twoSplit_spans (N := N) hnd h0 hb hx₀ hy₀ hx hy h2 hP hsub h₀ h₁ hc h4
  rcases hm0 with h0B | h0L <;> rcases hmb with hbB | hbL
  · obtain ⟨X', Y', sX, sY, hdis, hX', hY'⟩ := twoSplit_hard (X := B) (Y := L) hnd hN h0 hb hx₀
      hy₀ hx hy h2 h4 hsB hsL hd hnB hnL h0B hbB
    refine mk X' Y' hdis (fun e he => ?_) (fun e he => ?_) sX sY
    · rcases hX' e he with h | h | h <;> simp [h]
    · rcases hY' e he with h | h | h <;> simp [h]
  · have h0L' : b₀ ∉ L := fun h => Finset.disjoint_left.1 hd h0B h
    have hbB' : b ∉ B := fun h => Finset.disjoint_left.1 hd h hbL
    refine mk (insert b₂ B) (insert b₄ L)
      (Finset.disjoint_insert_left.2
        ⟨by simp [h24, b₂L], Finset.disjoint_insert_right.2 ⟨b₄B, hd⟩⟩)
      (fun e he => ?_) (fun e he => ?_)
      (sp hsB (fun e he => Finset.mem_insert_of_mem he) (fun _ => Finset.mem_insert_self _ _)
        (fun h => absurd h hbB') (Or.inr (Or.inl (Finset.mem_insert_self _ _))))
      (sp hsL (fun e he => Finset.mem_insert_of_mem he) (fun h => absurd h h0L')
        (fun _ => Finset.mem_insert_self _ _)
        (Or.inr (Or.inr (Or.inr (Finset.mem_insert_self _ _)))))
    · rcases Finset.mem_insert.1 he with h | h <;> simp [h]
    · rcases Finset.mem_insert.1 he with h | h <;> simp [h]
  · have hbB' : b ∉ L := fun h => Finset.disjoint_left.1 hd hbB h
    have h0B' : b₀ ∉ B := fun h => Finset.disjoint_left.1 hd h h0L
    refine mk (insert b₄ B) (insert b₂ L)
      (Finset.disjoint_insert_left.2
        ⟨by simp [h24.symm, b₄L], Finset.disjoint_insert_right.2 ⟨b₂B, hd⟩⟩)
      (fun e he => ?_) (fun e he => ?_)
      (sp hsB (fun e he => Finset.mem_insert_of_mem he) (fun h => absurd h h0B')
        (fun _ => Finset.mem_insert_self _ _)
        (Or.inr (Or.inr (Or.inr (Finset.mem_insert_self _ _)))))
      (sp hsL (fun e he => Finset.mem_insert_of_mem he) (fun _ => Finset.mem_insert_self _ _)
        (fun h => absurd h hbB') (Or.inr (Or.inl (Finset.mem_insert_self _ _))))
    · rcases Finset.mem_insert.1 he with h | h <;> simp [h]
    · rcases Finset.mem_insert.1 he with h | h <;> simp [h]
  · obtain ⟨X', Y', sX, sY, hdis, hX', hY'⟩ := twoSplit_hard (X := L) (Y := B) hnd hN h0 hb hx₀
      hy₀ hx hy h2 h4 hsL hsB hd.symm hnL hnB h0L hbL
    refine mk Y' X' hdis.symm (fun e he => ?_) (fun e he => ?_) sY sX
    · rcases hY' e he with h | h | h <;> simp [h]
    · rcases hX' e he with h | h | h <;> simp [h]

/-- **[II, Claim A.5]**: in a doubly connected graph, with two `Θ` edges `b₀`, `b` between
internal molecules replaced by paths `b₀`, `b₂` and `b`, `b₄` through a new molecule `N`, every
redundant blue solid edge stays redundant. -/
theorem MGraph.claimA5 :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (N : V) (b₀ b₂ b b₄ : E),
    G.DC → N ∉ G.int → N ∉ G.ext → G.cls b₀ = some .diff → G.cls b = some .diff →
    (G.ends b₀).1 ∈ G.int → (G.ends b₀).2 ∈ G.int → (G.ends b).1 ∈ G.int →
    (G.ends b).2 ∈ G.int → [b₀, b₂, b, b₄].Nodup → G.cls b₂ = none → G.cls b₄ = none →
    ∀ e, G.IsRedundant e → (G.twoSplit N b₀ b₂ b b₄).IsRedundant e := by
  intro V E _ _ G N b₀ b₂ b b₄ hdc hN _ h0 hb hx₀ hy₀ hx hy hnd h2 h4 e ⟨he, hdce, hdce'⟩
  have e0 : e ≠ b₀ := fun h => by
    rw [h, h0] at he
    cases he
  have eb : e ≠ b := fun h => by
    rw [h, hb] at he
    cases he
  have e2 : e ≠ b₂ := fun h => by
    rw [h, h2] at he
    cases he
  have e4 : e ≠ b₄ := fun h => by
    rw [h, h4] at he
    cases he
  obtain ⟨-, -, -, -, -, -, -, -, hco⟩ := twoSplit_facts G N hnd h0 hb
  refine ⟨?_, dc_twoSplit hdc hnd hN h0 hb hx₀ hy₀ hx hy h2 h4, ?_⟩
  · rw [hco e e2 e4]; exact he
  · have : (G.twoSplit N b₀ b₂ b b₄).erase e = (G.erase e).twoSplit N b₀ b₂ b b₄ := by
      unfold MGraph.twoSplit
      rw [erase_split _ N eb e4, erase_split _ N e0 e2, erase_addInt]
    rw [this]
    exact dc_twoSplit hdce' hnd hN (by simpa [MGraph.erase, e0.symm] using h0)
      (by simpa [MGraph.erase, eb.symm] using hb) hx₀ hy₀ hx hy
      (by simpa [MGraph.erase, e2.symm] using h2) (by simpa [MGraph.erase, e4.symm] using h4)

/-! ## [II, Claim A.6] -/

/-- A graph obtained from a doubly connected graph `G` by adding a new vertex `N` and two new
edges `f₁`, `f₂` from `N` to internal vertices, `f₁` diffusive and `f₂` diffusive or blue solid, is
doubly connected. The graph `H` is described by its ends and classes. -/
private theorem dc_leaf [DecidableEq V] {G H : MGraph V E} (hG : G.DC)
    {N M₁ M₂ : V} {f₁ f₂ : E} (hM₁ : M₁ ∈ G.int) (hM₂ : M₂ ∈ G.int)
    (hint : H.int = insert N G.int) (hf₁ : G.cls f₁ = none) (hf₂ : G.cls f₂ = none)
    (hne : f₁ ≠ f₂) (hframe : ∀ e, G.cls e ≠ none → H.ends e = G.ends e ∧ H.cls e = G.cls e)
    (hH₁ : H.ends f₁ = (N, M₁) ∧ H.cls f₁ = some .diff)
    (hH₂ : H.ends f₂ = (N, M₂) ∧ (H.cls f₂ = some .diff ∨ H.cls f₂ = some .plus)) : H.DC := by
  classical
  obtain ⟨B, L, hd, hB, hL, hsB, hsL⟩ := hG
  have hNH : N ∈ H.int := by rw [hint]; exact Finset.mem_insert_self _ _
  have hnB : ∀ e ∈ B, G.cls e ≠ none := fun e he => by rw [hB e he]; simp
  have hnL : ∀ e ∈ L, G.cls e ≠ none := fun e he => by
    rcases hL e he with h | h | h <;> rw [h] <;> simp
  have key : ∀ (P : Finset E) (f : E) (M : V), M ∈ G.int → H.ends f = (N, M) →
      H.cls f ≠ none → G.Spans P → H.Spans (insert f P) := by
    intro P f M hM hends hcl hP
    refine spans_edit (N := N) (w := N) hP hint hNH ?_ fun e he hce => ?_
    · exact fun _ => ⟨M, hM, f, Finset.mem_insert_self _ _, hcl, Or.inl hends⟩
    · exact ⟨Finset.mem_insert_of_mem he, by rw [(hframe e hce).2]; exact hce,
        Or.inl (hframe e hce).1⟩
  have hf₁B : f₁ ∉ B := fun h => hf₁ ▸ hnB f₁ h <| rfl
  have hf₂B : f₂ ∉ B := fun h => hf₂ ▸ hnB f₂ h <| rfl
  have hf₁L : f₁ ∉ L := fun h => hf₁ ▸ hnL f₁ h <| rfl
  have hf₂L : f₂ ∉ L := fun h => hf₂ ▸ hnL f₂ h <| rfl
  refine ⟨insert f₁ B, insert f₂ L, ?_, ?_, ?_,
    key B f₁ M₁ hM₁ hH₁.1 (by rw [hH₁.2]; simp) hsB,
    key L f₂ M₂ hM₂ hH₂.1 (by rcases hH₂.2 with h | h <;> rw [h] <;> simp) hsL⟩
  · rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
    refine ⟨?_, hf₂B, hd⟩
    rw [Finset.mem_insert]
    exact fun h => h.elim hne hf₁L
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hH₁.2
    · rw [(hframe e (hnB e he)).2]; exact hB e he
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · rcases hH₂.2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [(hframe e (hnL e he)).2]; exact hL e he

/-- **[II, Claim A.6]**: in a doubly connected graph, a new molecule `N` with a `Θ` edge `b₁` to
`M₁` and blue solid edges `b₂`, `b₃` to `M₂`, `M₃`: each of `b₂`, `b₃` is redundant, and stays
redundant after the other one is changed into a `Θ` edge. -/
theorem MGraph.claimA6 :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (N M₁ M₂ M₃ : V)
    (b₁ b₂ b₃ : E), G.DC → N ∉ G.int → N ∉ G.ext → M₁ ∈ G.int → M₂ ∈ G.int → M₃ ∈ G.int →
    [b₁, b₂, b₃].Nodup → G.cls b₁ = none → G.cls b₂ = none → G.cls b₃ = none →
    let G' := (((G.addInt N).setEdge b₁ N M₁ (some .diff)).setEdge b₂ N M₂ (some .plus)).setEdge
      b₃ N M₃ (some .plus)
    G'.IsRedundant b₂ ∧ G'.IsRedundant b₃ ∧ (G'.convert [b₂]).IsRedundant b₃ ∧
      (G'.convert [b₃]).IsRedundant b₂ := by
  intro V E _ _ G N M₁ M₂ M₃ b₁ b₂ b₃ hdc _ _ hM₁ hM₂ hM₃ hnd hb₁ hb₂ hb₃ G'
  obtain ⟨h12, h13, h23⟩ := nodup3 hnd
  have hint : G'.int = insert N G.int := rfl
  have hE : ∀ e, G.cls e ≠ none → G'.ends e = G.ends e := by
    intro e he
    have e1 : e ≠ b₁ := fun h => he (h ▸ hb₁)
    have e2 : e ≠ b₂ := fun h => he (h ▸ hb₂)
    have e3 : e ≠ b₃ := fun h => he (h ▸ hb₃)
    simp [G', MGraph.setEdge, MGraph.addInt, e1, e2, e3]
  have hC : ∀ e, G.cls e ≠ none → G'.cls e = G.cls e := by
    intro e he
    have e1 : e ≠ b₁ := fun h => he (h ▸ hb₁)
    have e2 : e ≠ b₂ := fun h => he (h ▸ hb₂)
    have e3 : e ≠ b₃ := fun h => he (h ▸ hb₃)
    simp [G', MGraph.setEdge, MGraph.addInt, e1, e2, e3]
  have hE1 : G'.ends b₁ = (N, M₁) := by simp [G', MGraph.setEdge, h12, h13]
  have hE2 : G'.ends b₂ = (N, M₂) := by simp [G', MGraph.setEdge, h23]
  have hE3 : G'.ends b₃ = (N, M₃) := by simp [G', MGraph.setEdge]
  have hC1 : G'.cls b₁ = some .diff := by simp [G', MGraph.setEdge, h12, h13]
  have hC2 : G'.cls b₂ = some .plus := by simp [G', MGraph.setEdge, h23]
  have hC3 : G'.cls b₃ = some .plus := by simp [G', MGraph.setEdge]
  have hv : ∀ e, G.cls e ≠ none → e ≠ b₂ ∧ e ≠ b₃ := fun e he =>
    ⟨fun h => he (h ▸ hb₂), fun h => he (h ▸ hb₃)⟩
  have V1 : G'.DC :=
    dc_leaf hdc hM₁ hM₂ (f₁ := b₁) (f₂ := b₂) hint hb₁ hb₂ h12
      (fun e he => ⟨hE e he, hC e he⟩) ⟨hE1, hC1⟩ ⟨hE2, Or.inr hC2⟩
  have V2 : (G'.erase b₂).DC :=
    dc_leaf hdc hM₁ hM₃ (f₁ := b₁) (f₂ := b₃) hint hb₁ hb₃ h13
      (fun e he => ⟨hE e he, by simp [MGraph.erase, (hv e he).1, hC e he]⟩)
      ⟨hE1, by simp [MGraph.erase, h12, hC1]⟩
      ⟨hE3, Or.inr (by simp [MGraph.erase, h23.symm, hC3])⟩
  have V3 : (G'.erase b₃).DC :=
    dc_leaf hdc hM₁ hM₂ (f₁ := b₁) (f₂ := b₂) hint hb₁ hb₂ h12
      (fun e he => ⟨hE e he, by simp [MGraph.erase, (hv e he).2, hC e he]⟩)
      ⟨hE1, by simp [MGraph.erase, h13, hC1]⟩
      ⟨hE2, Or.inr (by simp [MGraph.erase, h23, hC2])⟩
  have V4 : (G'.convert [b₂]).DC :=
    dc_leaf hdc hM₁ hM₃ (f₁ := b₁) (f₂ := b₃) hint hb₁ hb₃ h13
      (fun e he => ⟨hE e he, by simp [MGraph.convert, (hv e he).1, hC e he]⟩)
      ⟨hE1, by simp [MGraph.convert, h12, hC1]⟩
      ⟨hE3, Or.inr (by simp [MGraph.convert, h23.symm, hC3])⟩
  have V5 : ((G'.convert [b₂]).erase b₃).DC :=
    dc_leaf hdc hM₁ hM₂ (f₁ := b₁) (f₂ := b₂) hint hb₁ hb₂ h12
      (fun e he => ⟨hE e he, by
        simp [MGraph.erase, MGraph.convert, (hv e he).1, (hv e he).2,
          hC e he]⟩)
      ⟨hE1, by simp [MGraph.erase, MGraph.convert, h12, h13, hC1]⟩
      ⟨hE2, Or.inl (by simp [MGraph.erase, MGraph.convert, h23, hC2])⟩
  have V6 : (G'.convert [b₃]).DC :=
    dc_leaf hdc hM₁ hM₂ (f₁ := b₁) (f₂ := b₂) hint hb₁ hb₂ h12
      (fun e he => ⟨hE e he, by simp [MGraph.convert, (hv e he).2, hC e he]⟩)
      ⟨hE1, by simp [MGraph.convert, h13, hC1]⟩
      ⟨hE2, Or.inr (by simp [MGraph.convert, h23, hC2])⟩
  have V7 : ((G'.convert [b₃]).erase b₂).DC :=
    dc_leaf hdc hM₁ hM₃ (f₁ := b₁) (f₂ := b₃) hint hb₁ hb₃ h13
      (fun e he => ⟨hE e he, by
        simp [MGraph.erase, MGraph.convert, (hv e he).1, (hv e he).2,
          hC e he]⟩)
      ⟨hE1, by simp [MGraph.erase, MGraph.convert, h12, h13, hC1]⟩
      ⟨hE3, Or.inl (by simp [MGraph.erase, MGraph.convert, h23.symm, hC3])⟩
  refine ⟨⟨hC2, V1, V2⟩, ⟨hC3, V1, V3⟩, ⟨?_, V4, V5⟩, ⟨?_, V6, V7⟩⟩
  · simp [MGraph.convert, h23.symm, hC3]
  · simp [MGraph.convert, h23, hC2]

/-! ## [II, Claim A.7] -/

/-- The graph of [II, Claim A.7] is doubly connected. -/
private theorem dc_A7 [DecidableEq V] [DecidableEq E] {G : MGraph V E} (hG : G.DC) {N M₃ : V}
    {b₀ b₂ b₃ : E} (h0 : G.cls b₀ = some .diff) (hy0 : (G.ends b₀).2 ∈ G.int)
    (hM₃ : M₃ ∈ G.int) (hnd : [b₀, b₂, b₃].Nodup) (hb₂ : G.cls b₂ = none)
    (hb₃ : G.cls b₃ = none) :
    (((G.addInt N).split b₀ b₂ N).setEdge b₃ N M₃ (some .diff)).DC := by
  obtain ⟨h02, h03, h23⟩ := nodup3 hnd
  refine dc_pathleaf (N := N) hG hM₃ hy0 (b := b₀) (b' := b₂) (f := b₃) ?_ (Or.inl h0) hb₂ hb₃
    h02 h23
    ?_ ?_ ?_ ?_
  · rfl
  · intro e he heb
    have he2 : e ≠ b₂ := fun h => he (h ▸ hb₂)
    have he3 : e ≠ b₃ := fun h => he (h ▸ hb₃)
    simp [MGraph.setEdge, MGraph.split, MGraph.addInt, heb, he2, he3]
  · simp [MGraph.setEdge, MGraph.split, MGraph.addInt, h02, h03]
  · simp [MGraph.setEdge, MGraph.split, MGraph.addInt, h23, h02.symm]
  · simp [MGraph.setEdge, MGraph.split, MGraph.addInt]

/-- **[II, Claim A.7]**: in a doubly connected graph, the `Θ` edge `b₀` between internal
molecules replaced by a path `b₀`, `b₂` through a new molecule `N`, and a `Θ` edge `b₃` from `N` to
`M₃` added: every redundant blue solid edge stays redundant. -/
theorem MGraph.claimA7 :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (N M₃ : V) (b₀ b₂ b₃ : E),
    G.DC → N ∉ G.int → N ∉ G.ext → G.cls b₀ = some .diff → (G.ends b₀).1 ∈ G.int →
    (G.ends b₀).2 ∈ G.int → M₃ ∈ G.int → [b₀, b₂, b₃].Nodup → G.cls b₂ = none →
    G.cls b₃ = none →
    ∀ e, G.IsRedundant e → (((G.addInt N).split b₀ b₂ N).setEdge b₃ N M₃ (some .diff)).IsRedundant e := by
  intro V E _ _ G N M₃ b₀ b₂ b₃ hdc _ _ h0 _ hy0 hM₃ hnd hb₂ hb₃ e ⟨he, hdce, hdce'⟩
  obtain ⟨h02, h03, h23⟩ := nodup3 hnd
  have he0 : e ≠ b₀ := fun h => by
    rw [h, h0] at he
    cases he
  have he2 : e ≠ b₂ := fun h => by
    rw [h, hb₂] at he
    cases he
  have he3 : e ≠ b₃ := fun h => by
    rw [h, hb₃] at he
    cases he
  refine ⟨?_, dc_A7 hdc h0 hy0 hM₃ hnd hb₂ hb₃, ?_⟩
  · simpa [MGraph.setEdge, MGraph.split, MGraph.addInt, he2, he3, Function.update_apply] using he
  · rw [erase_setEdge _ _ _ _ he3, erase_split _ _ he0 he2, erase_addInt]
    refine dc_A7 hdce' ?_ hy0 hM₃ hnd ?_ ?_
    · simpa [MGraph.erase, he0.symm] using h0
    · simpa [MGraph.erase, he2.symm] using hb₂
    · simpa [MGraph.erase, he3.symm] using hb₃

section Instances

end Instances

end RBM8D.Graphs
