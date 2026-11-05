import RBM8D.Graph.MolCarry

/-!
# Adding an edge between two internal molecules

A sequentially pre-deterministic molecular multigraph without ghost edges ([II, Def 5.9]) stays
sequentially pre-deterministic when an absent edge is set to join two internal molecules as a blue
solid, diffusive or red solid edge. This is the step of [II, Lemma 6.5 (3), (4)] for `n' = 0` in
which an edge between two external vertices of the inserted graph becomes an edge between two
internal molecules of the host graph.

If the new edge joins the component `Γ_i` of the chain of proper isolated subsets
([II, (5.2)–(5.4)]) to the component `Γ_j`, `i < j`, the members `P (i + 1), …, P j` of the chain
stop being isolated and the other members stay isolated. The new clause of [II, Def 5.9 (iii)] is
the replacement of `P (j + 1)` in `P i`, or the subgraph induced on `P i` when `j` is the last
level; its pre-deterministic order is the new edge, then the order of the component `j`, then, for
`m = j - 1, …, i`, the second crossing edge of `P (m + 1)` when it is blue solid and the order of
the component `m`.
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

/-! ## Changing classes and removing edges -/

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

/-- The order of the components `j - d, …, j`: the order `ℓ j` of the component `j`, then, for
`m = j - 1, …, j - d`, the list `J m` (the crossing edge `cc' m` if it is a blue solid edge) and the
order `ℓ m` of the component `m`. -/
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

/-! ## The chain of a sequentially pre-deterministic graph -/

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


/-! ## Adding present edges -/

/-- The graph `H'` has the internal vertices of `H` and every present edge of `H`, with its class
and its ends. -/
private def Sup (H H' : MGraph V E) : Prop :=
  H'.int = H.int ∧ ∀ f, H.cls f ≠ none → H'.cls f = H.cls f ∧ H'.ends f = H.ends f

/-- A graph with more present edges keeps the doubly connected property: the nets are kept. -/
private theorem dc_sup {H H' : MGraph V E} (h : Sup H H') (hH : H.DC) : H'.DC := by
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := hH
  have pK : ∀ f ∈ K, H.cls f ≠ none := fun f hf => by rw [hK f hf]; simp
  have pL : ∀ f ∈ L, H.cls f ≠ none := fun f hf => by
    rcases hL f hf with h | h | h <;> rw [h] <;> simp
  have sp : ∀ B : Finset E, H.Spans B → H'.Spans B := by
    intro B hB S hS hne hn
    rw [h.1] at hS hn
    obtain ⟨f, hf, hc, h1, h2, hcut⟩ := hB S hS hne hn
    obtain ⟨hc', he'⟩ := h.2 f hc
    refine ⟨f, hf, by rw [hc']; exact hc, ?_, ?_, ?_⟩
    · rw [he', h.1]; exact h1
    · rw [he', h.1]; exact h2
    · simp only [MGraph.Cut, he']; exact hcut
  exact ⟨K, L, hd, fun f hf => by rw [(h.2 f (pK f hf)).1]; exact hK f hf,
    fun f hf => by rw [(h.2 f (pL f hf)).1]; exact hL f hf, sp K hsK, sp L hsL⟩

/-- Removing the same edge from both graphs keeps the relation `Sup`. -/
private theorem sup_erase [DecidableEq E] {H H' : MGraph V E} (h : Sup H H') (x : E) :
    Sup (H.erase x) (H'.erase x) := by
  refine ⟨h.1, fun f hf => ?_⟩
  by_cases hx : f = x
  · subst hx; simp [MGraph.erase] at hf
  · have hf' : H.cls f ≠ none := by simpa [MGraph.erase, hx] using hf
    simp only [MGraph.erase, Function.update_of_ne hx]
    exact h.2 f hf'

/-- A present edge after changing blue solid edges into `Θ` edges is present before. -/
private theorem convert_pres [DecidableEq E] {H : MGraph V E} {l : List E} {f : E}
    (h : (H.convert l).cls f ≠ none) : H.cls f ≠ none := by
  intro hn; apply h; simp [MGraph.convert, hn]

/-- Pre-deterministic graphs: only the internal vertices, the classes and the ends of the present
edges matter. -/
private theorem preDet_of_agree [DecidableEq E] {H H' : MGraph V E} (hi : H'.int = H.int)
    (hc : H'.cls = H.cls) (he : ∀ f, H.cls f ≠ none → H'.ends f = H.ends f) (hH : H.PreDet) :
    H'.PreDet := by
  obtain ⟨hdc, l, hnd, hmem, hred⟩ := hH
  have conv : ∀ l', (H'.convert l').cls = (H.convert l').cls := fun l' => by
    funext f; simp only [MGraph.convert, hc]
  have sc : ∀ l', Sup (H.convert l') (H'.convert l') := fun l' =>
    ⟨hi, fun f hf => ⟨by rw [conv], he f (convert_pres hf)⟩⟩
  refine ⟨dc_sup ⟨hi, fun f hf => ⟨by rw [hc], he f hf⟩⟩ hdc, l, hnd, fun f => ?_, fun t ht => ?_⟩
  · rw [hmem f]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hp : H.cls f ≠ none := by rw [h1]; simp
      refine ⟨by rw [hc]; exact h1, ?_, ?_⟩ <;> rw [he f hp, hi]
      · exact h2
      · exact h3
    · rintro ⟨h1, h2, h3⟩
      have hp : H.cls f ≠ none := by rw [← hc, h1]; simp
      refine ⟨by rw [← hc]; exact h1, ?_, ?_⟩ <;> rw [← he f hp, ← hi]
      · exact h2
      · exact h3
  · obtain ⟨h1, h2, h3⟩ := hred t ht
    exact ⟨by rw [conv]; exact h1, dc_sup (sc _) h2, dc_sup (sup_erase (sc _) _) h3⟩

/-- An absent edge set to an absent edge between any two vertices, or to a blue solid edge between
two internal vertices, keeps the pre-deterministic property; the new blue solid edge heads the
order. -/
private theorem preDet_setEdge [DecidableEq E] {H : MGraph V E} {e : E} (u v : V)
    (c : Option MClass) (hH : H.PreDet) (he : H.cls e = none)
    (hc : c = none ∨ (c = some .plus ∧ u ∈ H.int ∧ v ∈ H.int)) : (H.setEdge e u v c).PreDet := by
  have hends : ∀ f, H.cls f ≠ none → (H.setEdge e u v c).ends f = H.ends f := by
    intro f hf
    have hfe : f ≠ e := by rintro rfl; exact hf he
    simp [MGraph.setEdge, hfe]
  have hcls : ∀ f, f ≠ e → (H.setEdge e u v c).cls f = H.cls f := by
    intro f hfe
    simp [MGraph.setEdge, Function.update_of_ne hfe]
  rcases hc with rfl | ⟨rfl, hu, hv⟩
  · refine preDet_of_agree (H := H) rfl ?_ hends hH
    funext f
    by_cases hfe : f = e
    · subst hfe; simp [MGraph.setEdge, he]
    · exact hcls f hfe
  · set H' := H.setEdge e u v (some .plus) with hH'
    obtain ⟨hdc, l, hnd, hmem, hred⟩ := hH
    have hsup : Sup H H' := ⟨rfl, fun f hf => ⟨hcls f (by rintro rfl; exact hf he), hends f hf⟩⟩
    have hel : e ∉ l := fun h => by
      have := ((hmem e).1 h).1
      rw [he] at this
      exact absurd this (by simp)
    -- the classes after the new edge and the edges of `l'` are changed into `Θ` edges
    have sc : ∀ l', Sup (H.convert l') (H'.convert (e :: l')) := by
      intro l'
      refine ⟨rfl, fun f hf => ⟨?_, hends f (convert_pres hf)⟩⟩
      have hfe : f ≠ e := by rintro rfl; exact convert_pres hf he
      simp only [MGraph.convert, hcls f hfe, List.mem_cons, hfe, false_or]
    refine ⟨dc_sup hsup hdc, e :: l, List.nodup_cons.2 ⟨hel, hnd⟩, fun f => ?_, fun t ht => ?_⟩
    · rw [List.mem_cons]
      by_cases hfe : f = e
      · subst hfe
        simp only [true_or, true_iff]
        exact ⟨by simp [hH', MGraph.setEdge], by simpa [hH', MGraph.setEdge] using hu,
          by simpa [hH', MGraph.setEdge] using hv⟩
      · rw [hmem f]
        simp only [hfe, false_or, MGraph.IsIntPlus, hcls f hfe]
        constructor
        · rintro ⟨h1, h2, h3⟩
          have hp : H.cls f ≠ none := by rw [h1]; simp
          rw [hends f hp]
          exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩
          have hp : H.cls f ≠ none := by rw [h1]; simp
          rw [hends f hp] at h2 h3
          exact ⟨h1, h2, h3⟩
    · rcases t with _ | t
      · simp only [List.take_zero, List.getElem_cons_zero, convert_nil]
        refine ⟨by simp [hH', MGraph.setEdge], dc_sup hsup hdc,
          dc_sup (H := H) (H' := H'.erase e) ⟨rfl, fun f hf => ?_⟩ hdc⟩
        have hfe : f ≠ e := by rintro rfl; exact hf he
        simp only [MGraph.erase, Function.update_of_ne hfe]
        exact hsup.2 f hf
      · have ht' : t < l.length := by simp at ht; omega
        simp only [List.take_succ_cons, List.getElem_cons_succ]
        obtain ⟨h1, h2, h3⟩ := hred t ht'
        refine ⟨?_, dc_sup (sc _) h2, dc_sup (sup_erase (sc _) _) h3⟩
        have hp : H.cls l[t] ≠ none := by
          have := ((hmem _).1 (List.getElem_mem ht')).1
          rw [this]; simp
        exact ((sc (l.take t)).2 _ (by rw [h1]; simp)).1.trans h1

/-! ## The doubly connected property at one component -/

/-- A spanning net of the subgraph induced on the components `a, …, b - 1`, whose edges are kept
in `X` with their ends, connects any two of its vertices in `X`. -/
private theorem piece_conn [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {a b : ℕ} {X : MGraph V E} {N NP : Finset E} (r : V) (hsub : NP ⊆ N)
    (hsp : (G.induce (C.Lvl a b)).Spans NP)
    (hin : ∀ e, G.cls e ≠ none → (G.ends e).1 ∈ C.Lvl a b → (G.ends e).2 ∈ C.Lvl a b →
      X.ends e = G.ends e ∧ X.cls e ≠ none ∧ (G.ends e).1 ∈ X.int ∧ (G.ends e).2 ∈ X.int) :
    ∀ u ∈ C.Lvl a b, ∀ v ∈ C.Lvl a b, X.Rch N r r u v := by
  intro u hu v hv
  refine rch_sim (X := G.induce (C.Lvl a b)) u (fun e he hc h1 h2 => ?_)
    (rch_of_spans u u hsp hu hv)
  obtain ⟨i1, i2, i3⟩ := induce_pres hc
  obtain ⟨x1, x2, x3, x4⟩ := hin e (by rw [← i3]; exact hc) i1 i2
  change X.Rch N r r (G.ends e).1 (G.ends e).2
  rw [← x1]
  exact rch_edge (hsub he) x2 (by rw [x1]; exact x3) (by rw [x1]; exact x4)

/-- Connectivity in the graph `X` on the components `i, …, j` from the component `c`: nets of
the graph `Y` of the component, of the subgraph induced on the components `i, …, c - 1` and of
the subgraph induced on the components `c + 1, …, j`, together with crossing edges and the new
edge `ε` between `Mi` and `Mj`, connect every vertex of `X` to `Mi`. A `Θ` edge of `Y` carrying
the index `cc c` is followed through `cc c`, the components after `c` and `cc' c`. -/
private theorem add_conn [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {i j c : ℕ} {Mi Mj : V} {ε : E} (hjk : j ≤ C.k) (hic : i ≤ c) (hcj : c ≤ j)
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
    (hXp : i < c → X.cls (C.cc (c - 1)) ≠ none ∧ X.ends (C.cc (c - 1)) = G.ends (C.cc (c - 1)) ∧
      X.cls (C.cc' (c - 1)) ≠ none ∧ X.ends (C.cc' (c - 1)) = G.ends (C.cc' (c - 1)))
    (hXc : c < j → X.cls (C.cc c) ≠ none ∧ X.ends (C.cc c) = G.ends (C.cc c) ∧
      X.cls (C.cc' c) ≠ none ∧ X.ends (C.cc' c) = G.ends (C.cc' c))
    (hXε : c < j → X.cls ε ≠ none ∧ (X.ends ε = (Mi, Mj) ∨ X.ends ε = (Mj, Mi)))
    {N Nc NU ND : Finset E} (sNc : Nc ⊆ N) (sNU : NU ⊆ N) (sND : ND ⊆ N)
    (hNc : Y.Spans Nc) (hNU : (G.induce (C.Lvl i c)).Spans NU)
    (hND : (G.induce (C.Lvl (c + 1) (j + 1))).Spans ND)
    (hθN : c < j → C.cc c ∈ Nc → C.cc' c ∈ N)
    (attU : i < c → C.cc (c - 1) ∈ N ∨ C.cc' (c - 1) ∈ N)
    (attD : c < j → C.cc c ∈ N ∨ C.cc' c ∈ N ∨ ε ∈ N) :
    ∀ u ∈ X.int, X.Rch N Mi Mi u Mi := by
  have hYX : ∀ v, v ∈ Y.int → v ∈ X.int := fun v hv => by
    obtain ⟨h1, h2⟩ := (hYint v).1 hv
    exact (hXint v).2 ⟨h1, by omega, by omega⟩
  have inX : ∀ v, v ∈ G.int → i ≤ C.lev v → C.lev v ≤ j → v ∈ X.int :=
    fun v a b c => (hXint v).2 ⟨a, b, c⟩
  -- a piece induced on the components `a, …, b - 1`, away from `c`
  have piece : ∀ a b (NP : Finset E), NP ⊆ N → i ≤ a → b ≤ j + 1 → (c < a ∨ b ≤ c) →
      (G.induce (C.Lvl a b)).Spans NP → ∀ u ∈ C.Lvl a b, ∀ v ∈ C.Lvl a b,
        X.Rch N Mi Mi u v := by
    intro a b NP hsub ha hb hab hsp
    refine piece_conn C Mi hsub hsp fun e hc h1 h2 => ?_
    obtain ⟨a1, a2, a3⟩ := C.mem_Lvl.1 h1
    obtain ⟨b1, b2, b3⟩ := C.mem_Lvl.1 h2
    obtain ⟨x1, x2⟩ := hrest e hc a1 b1 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    exact ⟨x1, x2, inX _ a1 (by omega) (by omega), inX _ b1 (by omega) (by omega)⟩
  have hU : ∀ u ∈ C.Lvl i c, X.Rch N Mi Mi u Mi := by
    intro u hu
    obtain ⟨-, h1, h2⟩ := C.mem_Lvl.1 hu
    exact piece i c NU sNU le_rfl (by omega) (Or.inr le_rfl) hNU u hu Mi
      (C.mem_Lvl.2 ⟨hMi, by omega, by omega⟩)
  have hD : ∀ u ∈ C.Lvl (c + 1) (j + 1), X.Rch N Mi Mi u Mj := by
    intro u hu
    obtain ⟨-, h1, h2⟩ := C.mem_Lvl.1 hu
    exact piece (c + 1) (j + 1) ND sND (by omega) le_rfl (Or.inl (by omega)) hND u hu
      Mj (C.mem_Lvl.2 ⟨hMj, by omega, by omega⟩)
  -- a crossing edge of `P (l + 1)` joins its outer end to its end in the component `l + 1`
  have cross : ∀ l x, l < C.k → (x = C.cc l ∨ x = C.cc' l) → x ∈ N → X.cls x ≠ none →
      X.ends x = G.ends x → i ≤ l → l + 1 ≤ j → ∃ w, w ∈ G.int ∧ C.lev w = l + 1 ∧
        X.Rch N Mi Mi (G.outer (C.P (l + 1)) x) w ∧ G.outer (C.P (l + 1)) x ∈ G.int ∧
        C.lev (G.outer (C.P (l + 1)) x) = l := by
    intro l x hl hx hxN hxc hxe hil hlj
    obtain ⟨w, hw, hlw, ho, hlo, hends⟩ := C.cc_ends l hl x hx
    exact ⟨w, hw, hlw, rch_edge' hxN hxc (by rw [hxe]; exact hends)
      (inX _ ho (by omega) (by omega)) (inX _ hw (by omega) (by omega)), ho, hlo⟩
  -- the component `c`
  have hC : ∀ u ∈ Y.int, ∀ v ∈ Y.int, X.Rch N Mi Mi u v := by
    intro u hu v hv
    refine rch_sim (X := Y) u (fun e he hc h1 h2 => ?_) (rch_of_spans u u hNc hu hv)
    by_cases hθe : c < j ∧ e = C.cc c
    · obtain ⟨hcj', rfl⟩ := hθe
      rw [hθ hcj']
      obtain ⟨xc, xe, xc', xe'⟩ := hXc hcj'
      have hk : c < C.k := by omega
      obtain ⟨w, hw, hlw, hr, -⟩ := cross c (C.cc c) hk (Or.inl rfl) (sNc he) xc xe hic (by omega)
      obtain ⟨w', hw', hlw', hr', -⟩ := cross c (C.cc' c) hk (Or.inr rfl) (hθN hcj' he) xc'
        xe' hic (by omega)
      have hwD := hD w (C.mem_Lvl.2 ⟨hw, by omega, by omega⟩)
      have hwD' := hD w' (C.mem_Lvl.2 ⟨hw', by omega, by omega⟩)
      exact rch_trans hr (rch_trans hwD (rch_symm (rch_trans hr' hwD')))
    · obtain ⟨he1, he2⟩ := hcen e hc (fun hcj' h => hθe ⟨hcj', h⟩)
      rw [← he1]
      exact rch_edge (sNc he) he2 (by rw [he1]; exact hYX _ h1) (by rw [he1]; exact hYX _ h2)
  -- the component `c` is attached to `Mi`
  have hA : ∃ w ∈ Y.int, X.Rch N Mi Mi w Mi := by
    by_cases hic' : i < c
    · obtain ⟨xc, xe, xc', xe'⟩ := hXp hic'
      have hk : c - 1 < C.k := by omega
      have key : ∀ x, (x = C.cc (c - 1) ∨ x = C.cc' (c - 1)) → x ∈ N → X.cls x ≠ none →
          X.ends x = G.ends x → ∃ w ∈ Y.int, X.Rch N Mi Mi w Mi := by
        intro x hx hxN hxc hxe
        obtain ⟨w, hw, hlw, hr, ho, hlo⟩ := cross (c - 1) x hk hx hxN hxc hxe (by omega)
          (by omega)
        exact ⟨w, (hYint w).2 ⟨hw, by omega⟩,
          rch_trans (rch_symm hr) (hU _ (C.mem_Lvl.2 ⟨ho, by omega, by omega⟩))⟩
      rcases attU hic' with h | h
      · exact key _ (Or.inl rfl) h xc xe
      · exact key _ (Or.inr rfl) h xc' xe'
    · exact ⟨Mi, (hYint Mi).2 ⟨hMi, by omega⟩, Relation.ReflTransGen.refl⟩
  obtain ⟨w₀, hw₀, hw₀M⟩ := hA
  have hCM : ∀ u ∈ Y.int, X.Rch N Mi Mi u Mi := fun u hu => rch_trans (hC u hu w₀ hw₀) hw₀M
  -- the components after `c` are attached to `Mi`
  have hDM : c < j → X.Rch N Mi Mi Mj Mi := by
    intro hcj'
    obtain ⟨xc, xe, xc', xe'⟩ := hXc hcj'
    have hk : c < C.k := by omega
    have key : ∀ x, (x = C.cc c ∨ x = C.cc' c) → x ∈ N → X.cls x ≠ none →
        X.ends x = G.ends x → X.Rch N Mi Mi Mj Mi := by
      intro x hx hxN hxc hxe
      obtain ⟨w, hw, hlw, hr, ho, hlo⟩ := cross c x hk hx hxN hxc hxe hic (by omega)
      exact rch_trans (rch_symm (hD w (C.mem_Lvl.2 ⟨hw, by omega, by omega⟩)))
        (rch_trans (rch_symm hr) (hCM _ ((hYint _).2 ⟨ho, hlo⟩)))
    rcases attD hcj' with h | h | h
    · exact key _ (Or.inl rfl) h xc xe
    · exact key _ (Or.inr rfl) h xc' xe'
    · obtain ⟨hεc, hεe⟩ := hXε hcj'
      exact rch_symm (rch_edge' h hεc hεe (inX _ hMi (by omega) (by omega))
        (inX _ hMj (by omega) (by omega)))
  intro u hu
  obtain ⟨hu1, hu2, hu3⟩ := (hXint u).1 hu
  rcases lt_trichotomy (C.lev u) c with h | h | h
  · exact hU u (C.mem_Lvl.2 ⟨hu1, hu2, h⟩)
  · exact hCM u ((hYint u).2 ⟨hu1, h⟩)
  · exact rch_trans (hD u (C.mem_Lvl.2 ⟨hu1, by omega, by omega⟩)) (hDM (by omega))

/-- The step at the component `c` of the chain: from the graph `Y` of the component and the
subgraphs induced on the other components, the graph `X` on the components `i, …, j`, with the
new edge `ε` diffusive when `c < j`, is doubly connected. The nets are assembled from the nets of
the pieces and the crossing edges of `P c` and `P (c + 1)`; when a net of `Y` uses the `Θ` edge
of `P (c + 1)`, the other net enters the components after `c` through `ε`. -/
private theorem add_step [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {i j c : ℕ} {Mi Mj : V} {ε : E} (hjk : j ≤ C.k) (hic : i ≤ c) (hcj : c ≤ j)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hεG : G.cls ε = none) {X Y : MGraph V E}
    (hXint : ∀ v, v ∈ X.int ↔ v ∈ G.int ∧ i ≤ C.lev v ∧ C.lev v ≤ j)
    (hYint : ∀ v, v ∈ Y.int ↔ v ∈ G.int ∧ C.lev v = c) (hY : Y.DC)
    (hrest : ∀ e, G.cls e ≠ none → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int →
      i ≤ C.lev (G.ends e).1 → C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 →
      C.lev (G.ends e).2 ≤ j → C.lev (G.ends e).1 ≠ c → C.lev (G.ends e).2 ≠ c →
      X.ends e = G.ends e ∧ (X.cls e = G.cls e ∨ (G.cls e = some .plus ∧ X.cls e = some .diff)))
    (hcen : ∀ e, Y.cls e ≠ none → (c < j → e ≠ C.cc c) → X.ends e = Y.ends e ∧ X.cls e = Y.cls e)
    (hYpres : ∀ e, Y.cls e ≠ none → C.lev (G.ends e).1 = c ∨ C.lev (G.ends e).2 = c)
    (hYε : Y.cls ε = none)
    (hθ : c < j →
      Y.ends (C.cc c) = (G.outer (C.P (c + 1)) (C.cc c), G.outer (C.P (c + 1)) (C.cc' c)))
    (hYc' : c < j → Y.cls (C.cc' c) = none)
    (hYp : i < c → Y.cls (C.cc (c - 1)) = none ∧ Y.cls (C.cc' (c - 1)) = none)
    (hXp : i < c → X.cls (C.cc (c - 1)) = some .diff ∧
      X.ends (C.cc (c - 1)) = G.ends (C.cc (c - 1)) ∧
      (X.cls (C.cc' (c - 1)) = some .diff ∨ X.cls (C.cc' (c - 1)) = some .plus) ∧
      X.ends (C.cc' (c - 1)) = G.ends (C.cc' (c - 1)))
    (hXc : c < j → X.cls (C.cc c) = some .diff ∧ X.ends (C.cc c) = G.ends (C.cc c) ∧
      X.cls (C.cc' c) = some .diff ∧ X.ends (C.cc' c) = G.ends (C.cc' c))
    (hXε : c < j → X.cls ε = some .diff ∧ (X.ends ε = (Mi, Mj) ∨ X.ends ε = (Mj, Mi))) :
    X.DC := by
  classical
  obtain ⟨Kc, Lc, hdc, hKc, hLc, hsKc, hsLc⟩ := hY
  obtain ⟨KU, LU, hdU, hKU, hLU, hsKU, hsLU⟩ := C.dc_Lvl' i c
  obtain ⟨KD, LD, hdD, hKD, hLD, hsKD, hsLD⟩ := C.dc_Lvl' (c + 1) (j + 1)
  have dne : (some MClass.diff) ≠ none := by simp
  -- presence
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
  have hcen' : ∀ e, Y.cls e ≠ none → (c < j → e ≠ C.cc c) → X.ends e = Y.ends e ∧
      X.cls e ≠ none := fun e hc h => ⟨(hcen e hc h).1, by rw [(hcen e hc h).2]; exact hc⟩
  have hXp' : i < c → X.cls (C.cc (c - 1)) ≠ none ∧
      X.ends (C.cc (c - 1)) = G.ends (C.cc (c - 1)) ∧ X.cls (C.cc' (c - 1)) ≠ none ∧
      X.ends (C.cc' (c - 1)) = G.ends (C.cc' (c - 1)) := fun h => by
    obtain ⟨h1, h2, h3, h4⟩ := hXp h
    refine ⟨by rw [h1]; exact dne, h2, ?_, h4⟩
    rcases h3 with h3 | h3 <;> rw [h3] <;> simp
  have hXc' : c < j → X.cls (C.cc c) ≠ none ∧ X.ends (C.cc c) = G.ends (C.cc c) ∧
      X.cls (C.cc' c) ≠ none ∧ X.ends (C.cc' c) = G.ends (C.cc' c) := fun h =>
    ⟨by rw [(hXc h).1]; exact dne, (hXc h).2.1, by rw [(hXc h).2.2.1]; exact dne, (hXc h).2.2.2⟩
  have hXε' : c < j → X.cls ε ≠ none ∧ (X.ends ε = (Mi, Mj) ∨ X.ends ε = (Mj, Mi)) := fun h =>
    ⟨by rw [(hXε h).1]; exact dne, (hXε h).2⟩
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
  -- the edges of the nets of `Y` are not the extra edges
  have nY : ∀ e, Y.cls e ≠ none → e ≠ ε ∧ (c < j → e ≠ C.cc' c) ∧
      (i < c → e ≠ C.cc (c - 1) ∧ e ≠ C.cc' (c - 1)) := by
    intro e he
    refine ⟨fun h => he (h ▸ hYε), fun h h' => he (h' ▸ hYc' h), fun h => ⟨fun h' => he ?_,
      fun h' => he ?_⟩⟩
    · rw [h']; exact (hYp h).1
    · rw [h']; exact (hYp h).2
  -- the extra edges are distinct
  have gpres : ∀ l x, l < C.k → (x = C.cc l ∨ x = C.cc' l) → G.cls x ≠ none := by
    intro l x hl hx
    rcases hx with rfl | rfl
    · rw [C.cc_diff l hl]; exact dne
    · rcases C.cc'_cls l hl with h | h <;> rw [h] <;> simp
  have εne : ∀ l x, l < C.k → (x = C.cc l ∨ x = C.cc' l) → ε ≠ x := fun l x hl hx h =>
    gpres l x hl hx (h ▸ hεG)
  have lne : ∀ l l' x x', l < C.k → l' < C.k → (x = C.cc l ∨ x = C.cc' l) →
      (x' = C.cc l' ∨ x' = C.cc' l') → l ≠ l' → x ≠ x' := by
    intro l l' x x' hl hl' hx hx' hll h
    obtain ⟨-, -, a⟩ := C.cc_lev hl hx
    obtain ⟨-, -, b⟩ := C.cc_lev hl' hx'
    rw [h] at a
    omega
  -- the regions
  let R₂ : E → Prop := fun e => e = ε ∨ C.lev (G.ends e).1 = c ∨ C.lev (G.ends e).2 = c
  let R₀ : E → Prop := fun e => G.cls e ≠ none ∧ C.lev (G.ends e).1 < c ∧ C.lev (G.ends e).2 < c
  let R₁ : E → Prop := fun e => G.cls e ≠ none ∧ c < C.lev (G.ends e).1 ∧ c < C.lev (G.ends e).2
  have h₀ : ∀ e, e ∈ KU ∨ e ∈ LU → R₀ e := fun e he => by
    obtain ⟨-, -, -, a, -, b, hc, -⟩ := rU e he; exact ⟨hc, a, b⟩
  have h₁ : ∀ e, e ∈ KD ∨ e ∈ LD → R₁ e := fun e he => by
    obtain ⟨-, -, a, -, b, -, hc, -⟩ := rD e he; exact ⟨hc, by omega, by omega⟩
  have x₀₁ : ∀ e, R₀ e → R₁ e → False := fun e a b => by simp only [R₀, R₁] at a b; omega
  have x₀₂ : ∀ e, R₀ e → R₂ e → False := fun e a b => by
    simp only [R₀, R₂] at a b
    rcases b with rfl | b
    · exact a.1 hεG
    · omega
  have x₁₂ : ∀ e, R₁ e → R₂ e → False := fun e a b => by
    simp only [R₁, R₂] at a b
    rcases b with rfl | b
    · exact a.1 hεG
    · omega
  have r₂ : ∀ l x, l < C.k → (x = C.cc l ∨ x = C.cc' l) → (l = c ∨ l + 1 = c) → R₂ x := by
    intro l x hl hx hlc
    obtain ⟨-, -, h⟩ := C.cc_lev hl hx
    simp only [R₂]; omega
  have rc : ∀ e, e ∈ Kc ∨ e ∈ Lc → R₂ e := fun e he => by
    rcases he with he | he
    · exact Or.inr (hYpres e (pKc e he))
    · exact Or.inr (hYpres e (pLc e he))
  -- the crossing edges of `P c`
  let EpK : Finset E := if i < c then {C.cc (c - 1)} else ∅
  let EpL : Finset E := if i < c then {C.cc' (c - 1)} else ∅
  have mEpK : ∀ e ∈ EpK, i < c ∧ e = C.cc (c - 1) := by
    intro e he
    by_cases h : i < c
    · simp only [EpK, h, ↓reduceIte, Finset.mem_singleton] at he; exact ⟨h, he⟩
    · simp [EpK, h] at he
  have mEpL : ∀ e ∈ EpL, i < c ∧ e = C.cc' (c - 1) := by
    intro e he
    by_cases h : i < c
    · simp only [EpL, h, ↓reduceIte, Finset.mem_singleton] at he; exact ⟨h, he⟩
    · simp [EpL, h] at he
  have aK : i < c → C.cc (c - 1) ∈ EpK := fun h => by simp [EpK, h]
  have aL : i < c → C.cc' (c - 1) ∈ EpL := fun h => by simp [EpL, h]
  have rEpK : ∀ e ∈ EpK, R₂ e := fun e he => by
    obtain ⟨h, rfl⟩ := mEpK e he
    exact r₂ (c - 1) _ (by omega) (Or.inl rfl) (Or.inr (by omega))
  have rEpL : ∀ e ∈ EpL, R₂ e := fun e he => by
    obtain ⟨h, rfl⟩ := mEpL e he
    exact r₂ (c - 1) _ (by omega) (Or.inr rfl) (Or.inr (by omega))
  have cEpK : ∀ e ∈ EpK, X.cls e = some .diff := fun e he => by
    obtain ⟨h, rfl⟩ := mEpK e he; exact (hXp h).1
  have cEpL : ∀ e ∈ EpL, X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost :=
    fun e he => by
      obtain ⟨h, rfl⟩ := mEpL e he
      rcases (hXp h).2.2.1 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  have dEp : ∀ e, e ∈ EpK → e ∈ EpL → False := fun e ha hb => by
    obtain ⟨h, rfl⟩ := mEpK e ha
    obtain ⟨-, h'⟩ := mEpL _ hb
    exact C.cc_ne (c - 1) (by omega) h'
  have EpKc : ∀ e ∈ EpK, e ∉ Kc ∧ e ∉ Lc := fun e he => by
    obtain ⟨h, rfl⟩ := mEpK e he
    exact ⟨fun h' => ((nY _ (pKc _ h')).2.2 h).1 rfl, fun h' => ((nY _ (pLc _ h')).2.2 h).1 rfl⟩
  have EpLc : ∀ e ∈ EpL, e ∉ Kc ∧ e ∉ Lc := fun e he => by
    obtain ⟨h, rfl⟩ := mEpL e he
    exact ⟨fun h' => ((nY _ (pKc _ h')).2.2 h).2 rfl, fun h' => ((nY _ (pLc _ h')).2.2 h).2 rfl⟩
  -- the nets from the extra edges `Ea` (black) and `Eb` (blue)
  have fin : ∀ (Ea Eb : Finset E), (∀ e ∈ Ea, X.cls e = some .diff) →
      (∀ e ∈ Eb, X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost) →
      (∀ e ∈ Ea, R₂ e) → (∀ e ∈ Eb, R₂ e) →
      (∀ e, e ∈ Kc ∨ e ∈ Ea → e ∈ Lc ∨ e ∈ Eb → False) →
      (∀ u ∈ X.int, X.Rch (Kc ∪ KU ∪ KD ∪ Ea) Mi Mi u Mi) →
      (∀ u ∈ X.int, X.Rch (Lc ∪ LU ∪ LD ∪ Eb) Mi Mi u Mi) → X.DC := by
    intro Ea Eb cA cB rA rB d₂ sK sL
    refine ⟨Kc ∪ KU ∪ KD ∪ Ea, Lc ∪ LU ∪ LD ∪ Eb, ?_, fun e he => ?_, fun e he => ?_,
      spans_of_rch' Mi sK, spans_of_rch' Mi sL⟩
    · refine disj_regions (R₀ := R₀) (R₁ := R₁) (R₂ := R₂) (fun e he => ?_) h₀ h₁ x₀₁ x₀₂ x₁₂
        d₂ hdU hdD
      rcases he with he | he | he | he
      · exact rc e (Or.inl he)
      · exact rc e (Or.inr he)
      · exact rA e he
      · exact rB e he
    · simp only [Finset.mem_union] at he
      rcases he with ((he | he) | he) | he
      · exact cKc e he
      · exact cKU e he
      · exact cKD e he
      · exact cA e he
    · simp only [Finset.mem_union] at he
      rcases he with ((he | he) | he) | he
      · exact cLc e he
      · exact cLU e he
      · exact cLD e he
      · exact cB e he
  have conn := fun (N Nc NU ND : Finset E) (sNc : Nc ⊆ N) (sNU : NU ⊆ N) (sND : ND ⊆ N)
      (hNc : Y.Spans Nc) (hNU : (G.induce (C.Lvl i c)).Spans NU)
      (hND : (G.induce (C.Lvl (c + 1) (j + 1))).Spans ND) =>
    add_conn C (ε := ε) hjk hic hcj hMi hMi' hMj hMj' hXint hYint hrest' hcen' hθ hXp' hXc' hXε'
      sNc sNU sND hNc hNU hND
  have s1 : ∀ A B D F : Finset E, A ⊆ A ∪ B ∪ D ∪ F := fun A B D F e h => by simp [h]
  have s2 : ∀ A B D F : Finset E, B ⊆ A ∪ B ∪ D ∪ F := fun A B D F e h => by simp [h]
  have s3 : ∀ A B D F : Finset E, D ⊆ A ∪ B ∪ D ∪ F := fun A B D F e h => by simp [h]
  have s4 : ∀ A B D F : Finset E, ∀ e ∈ F, e ∈ A ∪ B ∪ D ∪ F := fun A B D F e h => by simp [h]
  rcases Nat.lt_or_ge c j with hcj' | hcj'
  · have hk : c < C.k := by omega
    have ne' := C.cc_ne c hk
    have rc0 : R₂ (C.cc c) := r₂ c _ hk (Or.inl rfl) (Or.inl rfl)
    have rc1 : R₂ (C.cc' c) := r₂ c _ hk (Or.inr rfl) (Or.inl rfl)
    have rε : R₂ ε := Or.inl rfl
    have c'K : C.cc' c ∉ Kc := fun h => (nY _ (pKc _ h)).2.1 hcj' rfl
    have c'L : C.cc' c ∉ Lc := fun h => (nY _ (pLc _ h)).2.1 hcj' rfl
    have εK : ε ∉ Kc := fun h => (nY _ (pKc _ h)).1 rfl
    have εL : ε ∉ Lc := fun h => (nY _ (pLc _ h)).1 rfl
    have Epc' : ∀ e, e ∈ EpK ∨ e ∈ EpL → e ≠ C.cc c ∧ e ≠ C.cc' c ∧ e ≠ ε := by
      intro e he
      have key : ∀ x, (x = C.cc (c - 1) ∨ x = C.cc' (c - 1)) → i < c →
          x ≠ C.cc c ∧ x ≠ C.cc' c ∧ x ≠ ε := fun x hx h =>
        ⟨lne _ _ _ _ (by omega) hk hx (Or.inl rfl) (by omega),
          lne _ _ _ _ (by omega) hk hx (Or.inr rfl) (by omega),
          fun h' => εne (c - 1) x (by omega) hx h'.symm⟩
      rcases he with he | he
      · obtain ⟨h, rfl⟩ := mEpK e he; exact key _ (Or.inl rfl) h
      · obtain ⟨h, rfl⟩ := mEpL e he; exact key _ (Or.inr rfl) h
    have εc' : ε ≠ C.cc' c := εne c _ hk (Or.inr rfl)
    have εc : ε ≠ C.cc c := εne c _ hk (Or.inl rfl)
    have hxc := hXc hcj'
    have cε := (hXε hcj').1
    by_cases hθK : C.cc c ∈ Kc
    · -- the `Θ` edge in the black net: the blue net enters through `ε`
      have hθL : C.cc c ∉ Lc := fun h => Finset.disjoint_left.1 hdc hθK h
      refine fin (insert (C.cc' c) EpK) (insert ε EpL) ?_ ?_ ?_ ?_ ?_
        (conn _ Kc KU KD (s1 _ _ _ _) (s2 _ _ _ _) (s3 _ _ _ _) hsKc hsKU hsKD
          (fun _ _ => s4 _ _ _ _ _ (Finset.mem_insert_self _ _))
          (fun h => Or.inl (s4 _ _ _ _ _ (Finset.mem_insert_of_mem (aK h))))
          (fun _ => Or.inl (s1 _ _ _ _ hθK)))
        (conn _ Lc LU LD (s1 _ _ _ _) (s2 _ _ _ _) (s3 _ _ _ _) hsLc hsLU hsLD
          (fun _ h => absurd h hθL)
          (fun h => Or.inr (s4 _ _ _ _ _ (Finset.mem_insert_of_mem (aL h))))
          (fun _ => Or.inr (Or.inr (s4 _ _ _ _ _ (Finset.mem_insert_self _ _)))))
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact hxc.2.2.1
        · exact cEpK e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inl cε
        · exact cEpL e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact rc1
        · exact rEpK e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact rε
        · exact rEpL e he
      · intro e ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Finset.disjoint_left.1 hdc ha hb
        · rcases Finset.mem_insert.1 hb with rfl | hb
          · exact εK ha
          · exact (EpLc e hb).1 ha
        · rcases Finset.mem_insert.1 ha with rfl | ha
          · exact c'L hb
          · exact (EpKc e ha).2 hb
        · rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with h | hb
          · exact εc' h.symm
          · exact (Epc' _ (Or.inr hb)).2.1 rfl
          · exact (Epc' _ (Or.inl ha)).2.2 h
          · exact dEp e ha hb
    by_cases hθL : C.cc c ∈ Lc
    · -- the `Θ` edge in the blue net: the black net enters through `ε`
      refine fin (insert ε EpK) (insert (C.cc' c) EpL) ?_ ?_ ?_ ?_ ?_
        (conn _ Kc KU KD (s1 _ _ _ _) (s2 _ _ _ _) (s3 _ _ _ _) hsKc hsKU hsKD
          (fun _ h => absurd h hθK)
          (fun h => Or.inl (s4 _ _ _ _ _ (Finset.mem_insert_of_mem (aK h))))
          (fun _ => Or.inr (Or.inr (s4 _ _ _ _ _ (Finset.mem_insert_self _ _)))))
        (conn _ Lc LU LD (s1 _ _ _ _) (s2 _ _ _ _) (s3 _ _ _ _) hsLc hsLU hsLD
          (fun _ _ => s4 _ _ _ _ _ (Finset.mem_insert_self _ _))
          (fun h => Or.inr (s4 _ _ _ _ _ (Finset.mem_insert_of_mem (aL h))))
          (fun _ => Or.inl (s1 _ _ _ _ hθL)))
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact cε
        · exact cEpK e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inl hxc.2.2.1
        · exact cEpL e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact rε
        · exact rEpK e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact rc1
        · exact rEpL e he
      · intro e ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Finset.disjoint_left.1 hdc ha hb
        · rcases Finset.mem_insert.1 hb with rfl | hb
          · exact c'K ha
          · exact (EpLc e hb).1 ha
        · rcases Finset.mem_insert.1 ha with rfl | ha
          · exact εL hb
          · exact (EpKc e ha).2 hb
        · rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with h | hb
          · exact εc' h
          · exact (Epc' _ (Or.inr hb)).2.2 rfl
          · exact (Epc' _ (Or.inl ha)).2.1 h
          · exact dEp e ha hb
    · -- the `Θ` edge in no net
      refine fin (insert (C.cc c) EpK) (insert (C.cc' c) EpL) ?_ ?_ ?_ ?_ ?_
        (conn _ Kc KU KD (s1 _ _ _ _) (s2 _ _ _ _) (s3 _ _ _ _) hsKc hsKU hsKD
          (fun _ h => absurd h hθK)
          (fun h => Or.inl (s4 _ _ _ _ _ (Finset.mem_insert_of_mem (aK h))))
          (fun _ => Or.inl (s4 _ _ _ _ _ (Finset.mem_insert_self _ _))))
        (conn _ Lc LU LD (s1 _ _ _ _) (s2 _ _ _ _) (s3 _ _ _ _) hsLc hsLU hsLD
          (fun _ h => absurd h hθL)
          (fun h => Or.inr (s4 _ _ _ _ _ (Finset.mem_insert_of_mem (aL h))))
          (fun _ => Or.inr (Or.inl (s4 _ _ _ _ _ (Finset.mem_insert_self _ _)))))
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact hxc.1
        · exact cEpK e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact Or.inl hxc.2.2.1
        · exact cEpL e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact rc0
        · exact rEpK e he
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact rc1
        · exact rEpL e he
      · intro e ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Finset.disjoint_left.1 hdc ha hb
        · rcases Finset.mem_insert.1 hb with rfl | hb
          · exact c'K ha
          · exact (EpLc e hb).1 ha
        · rcases Finset.mem_insert.1 ha with rfl | ha
          · exact hθL hb
          · exact (EpKc e ha).2 hb
        · rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with h | hb
          · exact ne' h
          · exact (Epc' _ (Or.inr hb)).1 rfl
          · exact (Epc' _ (Or.inl ha)).2.1 h
          · exact dEp e ha hb
  · have hcj2 : c = j := le_antisymm hcj hcj'
    refine fin EpK EpL cEpK cEpL rEpK rEpL ?_
      (conn _ Kc KU KD (s1 _ _ _ _) (s2 _ _ _ _) (s3 _ _ _ _) hsKc hsKU hsKD
        (fun h => absurd h (by omega)) (fun h => Or.inl (s4 _ _ _ _ _ (aK h)))
        (fun h => absurd h (by omega)))
      (conn _ Lc LU LD (s1 _ _ _ _) (s2 _ _ _ _) (s3 _ _ _ _) hsLc hsLU hsLD
        (fun h => absurd h (by omega)) (fun h => Or.inr (s4 _ _ _ _ _ (aL h)))
        (fun h => absurd h (by omega)))
    intro e ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Finset.disjoint_left.1 hdc ha hb
    · exact (EpLc e hb).1 ha
    · exact (EpKc e ha).2 hb
    · exact dEp e ha hb

/-- A present edge of the subgraph induced on the components `a, …, b - 1`: its ends lie in these
components and it keeps its class. -/
private theorem lvl_pres [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G) {a b : ℕ}
    {e : E} (hc : (G.induce (C.Lvl a b)).cls e ≠ none) :
    (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧ a ≤ C.lev (G.ends e).1 ∧
      C.lev (G.ends e).1 < b ∧ a ≤ C.lev (G.ends e).2 ∧ C.lev (G.ends e).2 < b ∧
      G.cls e ≠ none ∧ (G.induce (C.Lvl a b)).cls e = G.cls e := by
  obtain ⟨h1, h2, h3⟩ := induce_pres hc
  obtain ⟨a1, a2, a3⟩ := C.mem_Lvl.1 h1
  obtain ⟨b1, b2, b3⟩ := C.mem_Lvl.1 h2
  exact ⟨a1, b1, a2, a3, b2, b3, by rw [← h3]; exact hc, h3⟩

/-- The edges of a black net and of a blue net are present. -/
private theorem net_pres {X : MGraph V E} {K L : Finset E} (hK : ∀ e ∈ K, X.cls e = some .diff)
    (hL : ∀ e ∈ L, X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost) :
    ∀ e, e ∈ K ∨ e ∈ L → X.cls e ≠ none := by
  intro e he
  rcases he with he | he
  · rw [hK e he]; simp
  · rcases hL e he with h | h | h <;> rw [h] <;> simp

/-- The step at the crossing edge `cc' (c - 1)` of `P c`, `i < c`: the graph `X` on the components
`i, …, j` without this edge is doubly connected. The black net is made of the black nets of the
subgraphs induced on the components `i, …, c - 1` and `c, …, j` and of `cc (c - 1)`, the blue net
of their blue nets and of the new edge `ε`. -/
private theorem add_jstep [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {i j c : ℕ} {Mi Mj : V} {ε : E} (hjk : j ≤ C.k) (hic : i < c) (hcj : c ≤ j)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hεG : G.cls ε = none) {X : MGraph V E}
    (hXint : ∀ v, v ∈ X.int ↔ v ∈ G.int ∧ i ≤ C.lev v ∧ C.lev v ≤ j)
    (hrest : ∀ e, G.cls e ≠ none → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int →
      i ≤ C.lev (G.ends e).1 → C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 →
      C.lev (G.ends e).2 ≤ j → (C.lev (G.ends e).1 < c ↔ C.lev (G.ends e).2 < c) →
      X.ends e = G.ends e ∧ (X.cls e = G.cls e ∨ (G.cls e = some .plus ∧ X.cls e = some .diff)))
    (hXp : X.cls (C.cc (c - 1)) = some .diff ∧ X.ends (C.cc (c - 1)) = G.ends (C.cc (c - 1)))
    (hXε : X.cls ε = some .diff ∧ (X.ends ε = (Mi, Mj) ∨ X.ends ε = (Mj, Mi))) : X.DC := by
  classical
  obtain ⟨KU, LU, hdU, hKU, hLU, hsKU, hsLU⟩ := C.dc_Lvl' i c
  obtain ⟨KD, LD, hdD, hKD, hLD, hsKD, hsLD⟩ := C.dc_Lvl' c (j + 1)
  have dne : (some MClass.diff) ≠ none := by simp
  have inX : ∀ v, v ∈ G.int → i ≤ C.lev v → C.lev v ≤ j → v ∈ X.int :=
    fun v a b c => (hXint v).2 ⟨a, b, c⟩
  have pU := net_pres hKU hLU
  have pD := net_pres hKD hLD
  have rU : ∀ e, e ∈ KU ∨ e ∈ LU → _ := fun e he => lvl_pres C (pU e he)
  have rD : ∀ e, e ∈ KD ∨ e ∈ LD → _ := fun e he => lvl_pres C (pD e he)
  have xU : ∀ e, e ∈ KU ∨ e ∈ LU → X.ends e = G.ends e ∧
      (X.cls e = G.cls e ∨ (G.cls e = some .plus ∧ X.cls e = some .diff)) := by
    intro e he
    obtain ⟨a1, b1, a2, a3, b2, b3, hc, -⟩ := rU e he
    exact hrest e hc a1 b1 a2 (by omega) b2 (by omega) (iff_of_true a3 b3)
  have xD : ∀ e, e ∈ KD ∨ e ∈ LD → X.ends e = G.ends e ∧
      (X.cls e = G.cls e ∨ (G.cls e = some .plus ∧ X.cls e = some .diff)) := by
    intro e he
    obtain ⟨a1, b1, a2, a3, b2, b3, hc, -⟩ := rD e he
    exact hrest e hc a1 b1 (by omega) (by omega) (by omega) (by omega)
      (iff_of_false (by omega) (by omega))
  have black : ∀ e, (G.induce (C.Lvl i c)).cls e = some .diff ∨
      (G.induce (C.Lvl c (j + 1))).cls e = some .diff → G.cls e ≠ none →
      (X.cls e = G.cls e ∨ (G.cls e = some .plus ∧ X.cls e = some .diff)) →
      X.cls e = some .diff := by
    intro e h hc h'
    have hG : G.cls e = some .diff := by
      rcases h with h | h
      · rw [← (lvl_pres C (by rw [h]; exact dne)).2.2.2.2.2.2.2]; exact h
      · rw [← (lvl_pres C (by rw [h]; exact dne)).2.2.2.2.2.2.2]; exact h
    rcases h' with h' | ⟨h', -⟩
    · rw [h', hG]
    · rw [hG] at h'; exact absurd h' (by simp)
  have blue : ∀ e, (G.cls e = some .diff ∨ G.cls e = some .plus ∨ G.cls e = some .ghost) →
      (X.cls e = G.cls e ∨ (G.cls e = some .plus ∧ X.cls e = some .diff)) →
      (X.cls e = some .diff ∨ X.cls e = some .plus ∨ X.cls e = some .ghost) := by
    intro e hG h
    rcases h with h | ⟨-, h⟩
    · rw [h]; exact hG
    · exact Or.inl h
  -- the crossing edge `cc (c - 1)`
  have hk : c - 1 < C.k := by omega
  obtain ⟨w, hw, hlw, ho, hlo, hends⟩ := C.cc_ends (c - 1) hk _ (Or.inl rfl)
  obtain ⟨-, -, hcl⟩ := C.cc_lev hk (Or.inl rfl)
  have hgc : G.cls (C.cc (c - 1)) ≠ none := by rw [C.cc_diff _ hk]; exact dne
  -- connectivity of the pieces
  have piece : ∀ a b (N NP : Finset E), NP ⊆ N → i ≤ a → b ≤ j + 1 → (b ≤ c ∨ c ≤ a) →
      (G.induce (C.Lvl a b)).Spans NP → ∀ u ∈ C.Lvl a b, ∀ v ∈ C.Lvl a b,
        X.Rch N Mi Mi u v := by
    intro a b N NP hsub ha hb hab hsp
    refine piece_conn C Mi hsub hsp fun e hc h1 h2 => ?_
    obtain ⟨a1, a2, a3⟩ := C.mem_Lvl.1 h1
    obtain ⟨b1, b2, b3⟩ := C.mem_Lvl.1 h2
    obtain ⟨x1, x2⟩ := hrest e hc a1 b1 (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨x1, ?_, inX _ a1 (by omega) (by omega), inX _ b1 (by omega) (by omega)⟩
    rcases x2 with h | ⟨-, h⟩ <;> rw [h]
    · exact hc
    · exact dne
  have sp : ∀ (A B : Finset E) (x : E), (G.induce (C.Lvl i c)).Spans A →
      (G.induce (C.Lvl c (j + 1))).Spans B → X.cls x ≠ none →
      (∀ u ∈ C.Lvl c (j + 1), X.Rch (A ∪ B ∪ {x}) Mi Mi u Mi) → X.Spans (A ∪ B ∪ {x}) := by
    intro A B x hA hB hx hD
    refine spans_of_rch' Mi fun u hu => ?_
    obtain ⟨hu1, hu2, hu3⟩ := (hXint u).1 hu
    by_cases hlu : C.lev u < c
    · exact piece i c _ A (fun e h => by simp [h]) le_rfl (by omega) (Or.inl le_rfl) hA u
        (C.mem_Lvl.2 ⟨hu1, hu2, hlu⟩) Mi (C.mem_Lvl.2 ⟨hMi, by omega, by omega⟩)
    · exact hD u (C.mem_Lvl.2 ⟨hu1, by omega, by omega⟩)
  refine ⟨KU ∪ KD ∪ {C.cc (c - 1)}, LU ∪ LD ∪ {ε}, ?_, fun e he => ?_, fun e he => ?_,
    sp KU KD _ hsKU hsKD (by rw [hXp.1]; exact dne) fun u hu => ?_,
    sp LU LD _ hsLU hsLD (by rw [hXε.1]; exact dne) fun u hu => ?_⟩
  · rw [Finset.disjoint_left]
    intro e ha hb
    simp only [Finset.mem_union, Finset.mem_singleton] at ha hb
    rcases ha with (ha | ha) | rfl <;> rcases hb with (hb | hb) | hb
    · exact Finset.disjoint_left.1 hdU ha hb
    · obtain ⟨-, -, -, a, -, b, -⟩ := rU e (Or.inl ha)
      obtain ⟨-, -, c', -, d, -, -⟩ := rD e (Or.inr hb)
      omega
    · subst hb; exact (rU _ (Or.inl ha)).2.2.2.2.2.2.1 hεG
    · obtain ⟨-, -, a, -, b, -, -⟩ := rD e (Or.inl ha)
      obtain ⟨-, -, -, c', -, d, -⟩ := rU e (Or.inr hb)
      omega
    · exact Finset.disjoint_left.1 hdD ha hb
    · subst hb; exact (rD _ (Or.inl ha)).2.2.2.2.2.2.1 hεG
    · obtain ⟨-, -, -, a, -, b, -⟩ := rU _ (Or.inr hb)
      omega
    · obtain ⟨-, -, a, -, b, -, -⟩ := rD _ (Or.inr hb)
      omega
    · exact hgc (hb ▸ hεG)
  · simp only [Finset.mem_union, Finset.mem_singleton] at he
    rcases he with (he | he) | rfl
    · exact black e (Or.inl (hKU e he)) (pU e (Or.inl he) |> fun h =>
        (lvl_pres C h).2.2.2.2.2.2.1) (xU e (Or.inl he)).2
    · exact black e (Or.inr (hKD e he)) (pD e (Or.inl he) |> fun h =>
        (lvl_pres C h).2.2.2.2.2.2.1) (xD e (Or.inl he)).2
    · exact hXp.1
  · simp only [Finset.mem_union, Finset.mem_singleton] at he
    rcases he with (he | he) | rfl
    · have h := lvl_pres C (pU e (Or.inr he))
      exact blue e (by rw [← h.2.2.2.2.2.2.2]; exact hLU e he) (xU e (Or.inr he)).2
    · have h := lvl_pres C (pD e (Or.inr he))
      exact blue e (by rw [← h.2.2.2.2.2.2.2]; exact hLD e he) (xD e (Or.inr he)).2
    · exact Or.inl hXε.1
  · -- the black net: through `cc (c - 1)`
    have h1 := piece c (j + 1) (KU ∪ KD ∪ {C.cc (c - 1)}) KD (fun e h => by simp [h]) (by omega)
      le_rfl (Or.inr le_rfl)
      hsKD u hu w (C.mem_Lvl.2 ⟨hw, by omega, by omega⟩)
    have h2 : X.Rch (KU ∪ KD ∪ {C.cc (c - 1)}) Mi Mi (G.outer (C.P (c - 1 + 1)) (C.cc (c - 1)))
        w := rch_edge' (e := C.cc (c - 1)) (by simp) (by rw [hXp.1]; exact dne)
          (by rw [hXp.2]; exact hends)
          (inX _ ho (by omega) (by omega)) (inX _ hw (by omega) (by omega))
    have h3 := piece i c (KU ∪ KD ∪ {C.cc (c - 1)}) KU (fun e h => by simp [h]) le_rfl (by omega)
      (Or.inl le_rfl) hsKU _
      (C.mem_Lvl.2 ⟨ho, by omega, by omega⟩) Mi (C.mem_Lvl.2 ⟨hMi, by omega, by omega⟩)
    exact rch_trans h1 (rch_trans (rch_symm h2) h3)
  · -- the blue net: through `ε`
    have h1 := piece c (j + 1) (LU ∪ LD ∪ {ε}) LD (fun e h => by simp [h]) (by omega) le_rfl
      (Or.inr le_rfl)
      hsLD u hu Mj (C.mem_Lvl.2 ⟨hMj, by omega, by omega⟩)
    have h2 : X.Rch (LU ∪ LD ∪ {ε}) Mi Mi Mi Mj := rch_edge' (e := ε) (by simp)
      (by rw [hXε.1]; exact dne)
      hXε.2 (inX _ hMi (by omega) (by omega)) (inX _ hMj (by omega) (by omega))
    exact rch_trans h1 (rch_symm h2)

/-! ## The pre-deterministic order of the new clause -/

/-- A blue solid edge whose removal leaves a doubly connected graph is redundant. -/
private theorem red_of [DecidableEq E] {X : MGraph V E} {x : E} (hx : X.cls x = some .plus)
    (h : (X.erase x).DC) : X.IsRedundant x :=
  ⟨hx, dc_of_erase h, h⟩

/-- The step at the component `c`, for graphs `X` and `Y` obtained from the graph `Z` on the
components `i, …, j` and from the graph `R` of the component by changing blue solid edges into
`Θ` edges and removing edges. -/
private theorem add_wrap [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {i j c : ℕ} {Mi Mj : V} {ε : E} (hjk : j ≤ C.k) (hic : i ≤ c) (hcj : c ≤ j)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hεG : G.cls ε = none) {Z R X Y : MGraph V E}
    (hZint : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ i ≤ C.lev v ∧ C.lev v ≤ j)
    (hZG : ∀ e, e ≠ ε → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int → i ≤ C.lev (G.ends e).1 →
      C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 → C.lev (G.ends e).2 ≤ j →
      Z.ends e = G.ends e ∧ Z.cls e = G.cls e)
    (hZεe : Z.ends ε = (Mi, Mj) ∨ Z.ends ε = (Mj, Mi))
    (hRint : ∀ v, v ∈ R.int ↔ v ∈ G.int ∧ C.lev v = c)
    (hRpres : ∀ e, R.cls e ≠ none → ((G.ends e).1 ∈ G.int ∧ C.lev (G.ends e).1 = c ∧
      (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).2 = c ∧ R.cls e = G.cls e ∧ R.ends e = G.ends e) ∨
      (c < j ∧ e = C.cc c) ∨ (Z.ends e = R.ends e ∧ Z.cls e = some .diff ∧
        R.cls e = some .diff ∧ (C.lev (G.ends e).1 = c ∨ C.lev (G.ends e).2 = c) ∧
        (j < C.lev (G.ends e).1 ∨ j < C.lev (G.ends e).2)))
    (hRθ : c < j →
      R.ends (C.cc c) = (G.outer (C.P (c + 1)) (C.cc c), G.outer (C.P (c + 1)) (C.cc' c)))
    (hRc' : c < j → R.cls (C.cc' c) = none)
    (hRp : i < c → R.cls (C.cc (c - 1)) = none ∧ R.cls (C.cc' (c - 1)) = none)
    (hRε : R.cls ε = none) (hX : Wk Z X) (hY : Wk R Y) (hYdc : Y.DC)
    (hXer : ∀ e, X.cls e = none → Z.cls e ≠ none →
      (C.lev (G.ends e).1 = c ∧ C.lev (G.ends e).2 = c ∧ e ≠ ε) ∨ (e = ε ∧ c = j))
    (hmatch : ∀ e, (G.ends e).1 ∈ G.int → C.lev (G.ends e).1 = c → (G.ends e).2 ∈ G.int →
      C.lev (G.ends e).2 = c → G.cls e ≠ none → X.cls e = Y.cls e)
    (hXc' : c < j → X.cls (C.cc' c) = some .diff)
    (hXε : c < j → X.cls ε = some .diff) : X.DC := by
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
  have Xkeep : ∀ e, Z.cls e ≠ none → e ≠ ε → ¬ (C.lev (G.ends e).1 = c ∧ C.lev (G.ends e).2 = c) →
      X.cls e = Z.cls e ∨ (Z.cls e = some .plus ∧ X.cls e = some .diff) := by
    intro e hz hε h1
    rcases hXc e with h | h | h
    · rcases hXer e h hz with h' | h'
      · exact absurd ⟨h'.1, h'.2.1⟩ h1
      · exact absurd h'.1 hε
    · exact Or.inl h
    · exact Or.inr h
  have ccl := fun l (hl : l < C.k) x (hx : x = C.cc l ∨ x = C.cc' l) => C.cc_lev hl hx
  have gne : ∀ e, G.cls e ≠ none → e ≠ ε := fun e h h' => h (h' ▸ hεG)
  -- a crossing edge of `P l` or `P (l + 1)` inside the components `i, …, j`
  have crZ : ∀ l x, l < C.k → (x = C.cc l ∨ x = C.cc' l) → i ≤ l → l + 1 ≤ j →
      Z.ends x = G.ends x ∧ Z.cls x = G.cls x ∧ G.cls x ≠ none := by
    intro l x hl hx h1 h2
    obtain ⟨g1, g2, g3⟩ := ccl l hl x hx
    have hg : G.cls x ≠ none := by
      rcases hx with rfl | rfl
      · rw [C.cc_diff l hl]; exact dne
      · rcases C.cc'_cls l hl with h | h <;> rw [h] <;> simp
    exact ⟨(hZG x (gne x hg) g1 g2 (by omega) (by omega) (by omega) (by omega)).1,
      (hZG x (gne x hg) g1 g2 (by omega) (by omega) (by omega) (by omega)).2, hg⟩
  refine add_step C (ε := ε) hjk hic hcj hMi hMi' hMj hMj' hεG
    (fun v => by rw [hXi]; exact hZint v)
    (fun v => by rw [hYi]; exact hRint v) hYdc ?_ ?_ ?_ (Ynone _ hRε) ?_ ?_ ?_ ?_ ?_ ?_
  · intro e hc h1 h2 a1 a2 b1 b2 n1 n2
    obtain ⟨hze, hzc⟩ := hZG e (gne e hc) h1 h2 a1 a2 b1 b2
    refine ⟨by rw [hXe]; exact hze, ?_⟩
    rw [← hzc]
    exact Xkeep e (by rw [hzc]; exact hc) (gne e hc) (fun h => n1 h.1)
  · intro e hc hne
    have hR := Ypres e hc
    have heε : e ≠ ε := fun h => hR (h ▸ hRε)
    rcases hRpres e hR with ⟨a1, a2, b1, b2, hrc, hre⟩ | ⟨hcj', rfl⟩ | ⟨hze, hzc, hrc, hl, hj⟩
    · have hG : G.cls e ≠ none := by rw [← hrc]; exact hR
      obtain ⟨hze, -⟩ := hZG e heε a1 b1 (by omega) (by omega) (by omega) (by omega)
      exact ⟨by rw [hXe, hYe, hze, hre], hmatch e a1 a2 b1 b2 hG⟩
    · exact absurd rfl (hne hcj')
    · refine ⟨by rw [hXe, hYe, hze], ?_⟩
      have hx : X.cls e = some .diff := by
        rcases Xkeep e (by rw [hzc]; exact dne) heε (by omega) with h | h
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
  · intro h; exact ⟨Ynone _ (hRp h).1, Ynone _ (hRp h).2⟩
  · intro hic'
    obtain ⟨hze, hzc, hg⟩ := crZ (c - 1) _ (by omega) (Or.inl rfl) (by omega) (by omega)
    obtain ⟨hze', hzc', hg'⟩ := crZ (c - 1) _ (by omega) (Or.inr rfl) (by omega) (by omega)
    obtain ⟨-, -, l1⟩ := ccl (c - 1) (by omega) _ (Or.inl rfl)
    obtain ⟨-, -, l2⟩ := ccl (c - 1) (by omega) _ (Or.inr rfl)
    have hzd : Z.cls (C.cc (c - 1)) = some .diff := by rw [hzc]; exact C.cc_diff _ (by omega)
    refine ⟨?_, by rw [hXe]; exact hze, ?_, by rw [hXe]; exact hze'⟩
    · rcases Xkeep _ (by rw [hzd]; exact dne) (gne _ hg) (by omega) with h | h
      · rw [h, hzd]
      · exact h.2
    · rcases Xkeep _ (by rw [hzc']; exact hg') (gne _ hg') (by omega) with h | h
      · rw [h, hzc']; exact C.cc'_cls _ (by omega)
      · exact Or.inl h.2
  · intro hcj'
    obtain ⟨hze, hzc, hg⟩ := crZ c _ (by omega) (Or.inl rfl) hic (by omega)
    obtain ⟨hze', -, -⟩ := crZ c _ (by omega) (Or.inr rfl) hic (by omega)
    obtain ⟨-, -, l1⟩ := ccl c (by omega) _ (Or.inl rfl)
    have hzd : Z.cls (C.cc c) = some .diff := by rw [hzc]; exact C.cc_diff _ (by omega)
    refine ⟨?_, by rw [hXe]; exact hze, hXc' hcj', by rw [hXe]; exact hze'⟩
    rcases Xkeep (C.cc c) (by rw [hzd]; exact dne) (gne _ hg) (by omega) with h | h
    · rw [h, hzd]
    · exact h.2
  · intro hcj'
    exact ⟨hXε hcj', by rw [hXe]; exact hZεe⟩

/-- Removing an edge. -/
private theorem wk_erase [DecidableEq E] (W : MGraph V E) (x : E) : Wk W (W.erase x) := by
  have := wk_convert_erase W [] x
  rwa [convert_nil] at this

/-- **The pre-deterministic order of the new clause**: in the setting of a chain with the
components `i < j`, a graph `Z` on the components `i, …, j` that agrees with `G` inside them, has
the new blue solid edge `ε` between `Mi` and `Mj`, and has the bottom graph `Rb` on the
component `j`, is pre-deterministic. The order is `ε`, the order of `Rb`, then, for
`m = j - 1, …, i`, the crossing edge `cc' m` if it is a blue solid edge and the order of the
component `m`. -/
private theorem add_core [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {i j : ℕ} {Mi Mj : V} {ε : E} (hij : i < j) (hjk : j ≤ C.k)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hεG : G.cls ε = none) {Z Rb : MGraph V E}
    (hZint : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ i ≤ C.lev v ∧ C.lev v ≤ j)
    (hZG : ∀ e, e ≠ ε → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int → i ≤ C.lev (G.ends e).1 →
      C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 → C.lev (G.ends e).2 ≤ j →
      Z.ends e = G.ends e ∧ Z.cls e = G.cls e)
    (hZε : Z.cls ε = some .plus) (hZεe : Z.ends ε = (Mi, Mj) ∨ Z.ends ε = (Mj, Mi))
    (hZp : ∀ e, e ≠ ε → Z.cls e = some .plus → (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧
      i ≤ C.lev (G.ends e).1 ∧ C.lev (G.ends e).1 ≤ j ∧ i ≤ C.lev (G.ends e).2 ∧
      C.lev (G.ends e).2 ≤ j)
    (hRint : ∀ v, v ∈ Rb.int ↔ v ∈ G.int ∧ C.lev v = j) (hRpd : Rb.PreDet)
    (hRpres : ∀ e, Rb.cls e ≠ none → ((G.ends e).1 ∈ G.int ∧ C.lev (G.ends e).1 = j ∧
      (G.ends e).2 ∈ G.int ∧ C.lev (G.ends e).2 = j ∧ Rb.cls e = G.cls e ∧
      Rb.ends e = G.ends e) ∨ (Z.ends e = Rb.ends e ∧ Z.cls e = some .diff ∧
        Rb.cls e = some .diff ∧ (C.lev (G.ends e).1 = j ∨ C.lev (G.ends e).2 = j) ∧
        (j < C.lev (G.ends e).1 ∨ j < C.lev (G.ends e).2)))
    (hRG : ∀ e, (G.ends e).1 ∈ G.int → C.lev (G.ends e).1 = j → (G.ends e).2 ∈ G.int →
      C.lev (G.ends e).2 = j → Rb.cls e = G.cls e ∧ Rb.ends e = G.ends e)
    (hRε : Rb.cls ε = none) :
    Z.PreDet := by
  classical
  have dne : (some MClass.diff) ≠ none := by simp
  have pne : (some MClass.plus) ≠ none := by simp
  have gne : ∀ e, G.cls e ≠ none → e ≠ ε := fun e h h' => h (h' ▸ hεG)
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
  have hRp : i < j → Rb.cls (C.cc (j - 1)) = none ∧ Rb.cls (C.cc' (j - 1)) = none := by
    intro _
    have key : ∀ x, (x = C.cc (j - 1) ∨ x = C.cc' (j - 1)) → Rb.cls x = none := by
      intro x hx
      by_contra h
      obtain ⟨-, -, hl⟩ := C.cc_lev (l := j - 1) (by omega) hx
      rcases hRpres _ h with ⟨-, a, -, b, -⟩ | ⟨-, -, -, -, h'⟩ <;> omega
    exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩
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
      (c < j → (C.R c).cls (C.cc' c) = none) ∧
      (i < c → (C.R c).cls (C.cc (c - 1)) = none ∧ (C.R c).cls (C.cc' (c - 1)) = none) ∧
      (C.R c).cls ε = none := by
    intro c hic hcj
    have hc : c < C.k := by omega
    obtain ⟨hθ, -, hc', hpres, -⟩ := C.R_cls hc
    have prev : ∀ x, (x = C.cc (c - 1) ∨ x = C.cc' (c - 1)) → 0 < c → (C.R c).cls x = none := by
      intro x hx h0
      by_contra h
      obtain ⟨-, -, hl⟩ := C.cc_lev (l := c - 1) (by omega) hx
      rcases hpres _ h with h' | ⟨-, a, -, b, -⟩
      · obtain ⟨-, -, hl'⟩ := C.cc_lev hc (Or.inl rfl)
        rw [h'] at hl; omega
      · omega
    refine ⟨C.R_int hc, fun e he => ?_, fun _ => hθ, fun _ => hc', fun h =>
      ⟨prev _ (Or.inl rfl) (by omega), prev _ (Or.inr rfl) (by omega)⟩, ?_⟩
    · rcases hpres e he with h | h
      · exact Or.inr (Or.inl ⟨hcj, h⟩)
      · exact Or.inl h
    · by_contra h
      rcases hpres ε h with h' | ⟨-, -, -, -, h', -⟩
      · have := C.cc_diff c hc
        rw [← h', hεG] at this; exact absurd this (by simp)
      · rw [h', hεG] at h; exact h rfl
  -- membership in the components
  have hZcls : ∀ e, G.cls e ≠ none → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.int →
      i ≤ C.lev (G.ends e).1 → C.lev (G.ends e).1 ≤ j → i ≤ C.lev (G.ends e).2 →
      C.lev (G.ends e).2 ≤ j → Z.cls e = G.cls e := fun e hg a b c d e' f' =>
    (hZG e (gne e hg) a b c d e' f').2
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
  -- a list starting with `ε`, then edges of `G`
  have memε : ∀ (l : List E) e, e ≠ ε → (e ∈ [ε] ++ l ↔ e ∈ l) := by
    intro l e he
    simp [he]
  -- the head of the order: the new edge `ε`
  have hdc0 : (Z.erase ε).DC := by
    refine add_wrap C (c := j) hjk hij.le le_rfl hMi hMi' hMj hMj' hεG hZint hZG hZεe hRint
      hRpres' (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) hRp hRε
      (wk_erase Z ε) (wk_refl Rb) hRpd.1 (fun e h1 h2 => Or.inr ⟨?_, rfl⟩)
      (fun e a1 a2 b1 b2 hG => ?_) (fun h => absurd h (by omega)) (fun h => absurd h (by omega))
    · by_contra hne
      exact h2 (by simpa [MGraph.erase, hne] using h1)
    · rw [show (Z.erase ε).cls e = Z.cls e by simp [MGraph.erase, gne e hG],
        hZcls e hG a1 b1 (by omega) (by omega) (by omega) (by omega), (hRG e a1 a2 b1 b2).1]
  have head : Steps Z [ε] := by
    intro t ht
    obtain rfl : t = 0 := by simp at ht; omega
    simp only [List.take_zero, List.getElem_cons_zero, convert_nil]
    exact red_of hZε hdc0
  -- the invariant of the induction
  have main : ∀ d, d ≤ j - i → (ordList ℓ J j d).Nodup ∧
      (∀ e, e ∈ ordList ℓ J j d ↔ G.cls e = some .plus ∧ (G.ends e).1 ∈ G.int ∧
        (G.ends e).2 ∈ G.int ∧ j - d ≤ C.lev (G.ends e).1 ∧ C.lev (G.ends e).1 ≤ j ∧
        j - d ≤ C.lev (G.ends e).2 ∧ C.lev (G.ends e).2 ≤ j) ∧
      Steps (Z.convert [ε]) (ordList ℓ J j d) := by
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
        have hxg : G.cls (ℓ j)[t] ≠ none := by rw [hxp]; exact pne
        have hxZ := hZcls _ hxg x1 x2 (by omega) (by omega) (by omega) (by omega)
        rw [convert_convert]
        refine red_of ?_ ?_
        · rw [c_cls, ite_eq_right (fun h => by
            rw [memε _ _ (gne _ hxg)] at h
            exact getElem_notMem_take hℓj.1 ht h.1), hxZ, hxp]
        · refine add_wrap C (c := j) hjk hij.le le_rfl hMi hMi' hMj hMj' hεG hZint hZG hZεe
            hRint hRpres' (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) hRp hRε
            (wk_convert_erase _ _ _) (wk_convert_erase _ _ _) (hℓj.2.2 t ht).2.2
            (fun e h1 h2 => Or.inl ?_) (fun e a1 a2 b1 b2 hG => ?_)
            (fun h => absurd h (by omega)) (fun h => absurd h (by omega))
          · have := ce_none _ _ _ _ h1 h2; subst this; exact ⟨x3, x4, gne _ hxg⟩
          · rw [ce_cls, ce_cls, hZcls e hG a1 b1 (by omega) (by omega) (by omega) (by omega),
              (hRG e a1 a2 b1 b2).1]
            simp only [memε _ _ (gne e hG)]
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
      have hc'g : G.cls (C.cc' m) ≠ none := by
        rcases C.cc'_cls m hmk with h | h <;> rw [h] <;> simp
      have hc'Z := hZcls (C.cc' m) hc'g c1 c2 (by omega) (by omega) (by omega) (by omega)
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
            rw [convert_nil, convert_convert]
            have hcO : C.cc' m ∉ ordList ℓ J j d := nO _ (by omega)
            refine red_of ?_ ?_
            · rw [c_cls, ite_eq_right (fun h => by
                rw [memε _ _ (gne _ hc'g)] at h
                exact hcO h.1), hc'Z, hp]
            · obtain ⟨d1, d2, d3⟩ := C.cc_lev hmk (Or.inl rfl)
              have hcne : C.cc m ≠ C.cc' m := C.cc_ne m hmk
              have hcg : G.cls (C.cc m) ≠ none := by rw [C.cc_diff m hmk]; exact dne
              refine add_jstep C (c := m + 1) (ε := ε) hjk (by omega) (by omega) hMi hMi' hMj
                hMj' hεG (fun v => hZint v) (fun e hc a1 b1 a2 a3 b2 b3 hs => ?_) ⟨?_, ?_⟩ ⟨?_, ?_⟩
              · have hne : e ≠ C.cc' m := by rintro rfl; omega
                obtain ⟨hze, hzc⟩ := hZG e (gne e hc) a1 b1 a2 a3 b2 b3
                refine ⟨hze, ?_⟩
                rw [ce_cls, ite_eq_right hne, ← hzc]
                by_cases h : e ∈ [ε] ++ ordList ℓ J j d ∧ Z.cls e = some .plus
                · rw [ite_eq_left h]; exact Or.inr ⟨h.2, rfl⟩
                · rw [ite_eq_right h]; exact Or.inl rfl
              · simp only [Nat.add_sub_cancel]
                rw [ce_cls, ite_eq_right hcne, hZcls _ hcg d1 d2 (by omega) (by omega) (by omega)
                  (by omega), C.cc_diff m hmk]
                simp
              · simp only [Nat.add_sub_cancel]
                exact (hZG _ (gne _ hcg) d1 d2 (by omega) (by omega) (by omega) (by omega)).1
              · have hne : ε ≠ C.cc' m := fun h => gne _ hc'g h.symm
                rw [ce_cls, ite_eq_right hne, ite_eq_left ⟨by simp, hZε⟩]
              · exact hZεe
          · have hJm : J m = [] := by simp [J, hp]
            rw [hJm]
            intro t ht
            simp at ht
        · -- the order of the component `m`
          intro t ht
          rw [convert_convert, convert_convert, convert_convert]
          have hx := (memm m hmj _).1 (List.getElem_mem ht)
          obtain ⟨hxp, x1, x2, x3, x4⟩ := hx
          have hxg : G.cls (ℓ m)[t] ≠ none := by rw [hxp]; exact pne
          have hxZ := hZcls _ hxg x1 x2 (by omega) (by omega) (by omega) (by omega)
          have hxO : (ℓ m)[t] ∉ ordList ℓ J j d := nO _ (Or.inl x3)
          have hxJ : (ℓ m)[t] ∉ J m := fun h => by
            obtain ⟨h', -⟩ := (hJ m _).1 h
            rw [h'] at x3 x4; omega
          refine red_of ?_ ?_
          · rw [c_cls, ite_eq_right (fun h => by
              simp only [List.mem_append, List.mem_singleton] at h
              rcases h.1 with h | h | h | h
              · exact gne _ hxg h
              · exact hxO h
              · exact hxJ h
              · exact getElem_notMem_take hℓm.1 ht h), hxZ, hxp]
          · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := Rmid m him hmj
            refine add_wrap C (c := m) hjk him hmj.le hMi hMi' hMj hMj' hεG hZint hZG hZεe
                r1 r2 r3 r4 r5 r6 (wk_convert_erase _ _ _)
              (wk_convert_erase _ _ _) (hℓm.2.2 t ht).2.2 (fun e h1 h2 => Or.inl ?_)
              (fun e a1 a2 b1 b2 hG => ?_) (fun _ => ?_) (fun _ => ?_)
            · have := ce_none _ _ _ _ h1 h2; subst this; exact ⟨x3, x4, gne _ hxg⟩
            · have heO : e ∉ ordList ℓ J j d := nO _ (Or.inl a2)
              have heJ : e ∉ J m := fun h => by
                obtain ⟨h', -⟩ := (hJ m _).1 h
                rw [h'] at a2 b2; omega
              rw [ce_cls, ce_cls, hZcls e hG a1 b1 (by omega) (by omega) (by omega) (by omega),
                ((C.R_cls (l := m) (by omega)).2.2.2.2 e a1 a2 b1 b2).1]
              simp only [List.mem_append, List.mem_singleton, heO, heJ, gne e hG, false_or]
            · obtain ⟨d1, d2, d3⟩ := C.cc_lev hmk (Or.inr rfl)
              have hne : C.cc' m ≠ (ℓ m)[t] := by
                intro h; rw [← h] at x3 x4; omega
              rw [ce_cls, ite_eq_right hne, hc'Z]
              rcases C.cc'_cls m hmk with h | h
              · rw [h]; simp
              · rw [ite_eq_left ⟨by simp [(hJ m _).2 ⟨rfl, h⟩], h⟩]
            · have hne : ε ≠ (ℓ m)[t] := fun h => gne _ hxg h.symm
              rw [ce_cls, ite_eq_right hne, ite_eq_left ⟨by simp, hZε⟩]
  obtain ⟨hn, hmem, hst⟩ := main (j - i) le_rfl
  have hji : j - (j - i) = i := by omega
  rw [hji] at hmem
  have hεO : ε ∉ ordList ℓ J j (j - i) := fun h => by
    have := ((hmem ε).1 h).1
    rw [hεG] at this; exact absurd this (by simp)
  refine ⟨dc_of_erase hdc0, ε :: ordList ℓ J j (j - i), List.nodup_cons.2 ⟨hεO, hn⟩,
    fun e => ?_, ?_⟩
  · rw [List.mem_cons]
    by_cases he : e = ε
    · subst he
      simp only [true_or, true_iff]
      have hi : Mi ∈ Z.int := (hZint _).2 ⟨hMi, by omega, by omega⟩
      have hj : Mj ∈ Z.int := (hZint _).2 ⟨hMj, by omega, by omega⟩
      refine ⟨hZε, ?_, ?_⟩ <;> rcases hZεe with h | h <;> rw [h] <;> assumption
    · rw [hmem]
      simp only [he, false_or, MGraph.IsIntPlus]
      constructor
      · rintro ⟨h1, a1, b1, a2, a3, b2, b3⟩
        obtain ⟨hze, hzc⟩ := hZG e he a1 b1 a2 a3 b2 b3
        refine ⟨by rw [hzc]; exact h1, ?_, ?_⟩ <;> rw [hze, hZint]
        · exact ⟨a1, a2, a3⟩
        · exact ⟨b1, b2, b3⟩
      · rintro ⟨h1, -, -⟩
        obtain ⟨a1, b1, a2, a3, b2, b3⟩ := hZp e he h1
        obtain ⟨-, hzc⟩ := hZG e he a1 b1 a2 a3 b2 b3
        exact ⟨by rw [← hzc]; exact h1, a1, b1, a2, a3, b2, b3⟩
  · exact steps_append head hst

/-! ## The new clause of [II, Def 5.9 (iii)] -/

/-- The ends of the edges other than `ε` are kept by setting `ε`. -/
private theorem setEdge_ends_ne [DecidableEq E] (G : MGraph V E) {ε f : E} (u v : V)
    (c : Option MClass) (h : f ≠ ε) : (G.setEdge ε u v c).ends f = G.ends f := by
  simp [MGraph.setEdge, h]

/-- The classes of the edges other than `ε` are kept by setting `ε`. -/
private theorem setEdge_cls_ne [DecidableEq E] (G : MGraph V E) {ε f : E} (u v : V)
    (c : Option MClass) (h : f ≠ ε) : (G.setEdge ε u v c).cls f = G.cls f := by
  simp [MGraph.setEdge, Function.update_of_ne h]

/-- The outer end of an edge other than `ε` is kept by setting `ε`. -/
private theorem setEdge_outer_ne [DecidableEq V] [DecidableEq E] (G : MGraph V E) {ε f : E}
    (u v : V) (c : Option MClass) (P : Finset V) (h : f ≠ ε) :
    (G.setEdge ε u v c).outer P f = G.outer P f := by
  simp [MGraph.outer, MGraph.setEdge, h]

/-- **The new clause of [II, Def 5.9 (iii)]**: the new blue solid edge `ε` joins a vertex `Mi` of
the component `i` to a vertex `Mj` of the component `j > i`. For `j < k`, every replacement of
`P (j + 1)` in `P i` and its two external edges by one `Θ` edge gives a pre-deterministic graph;
for `j = k`, the subgraph induced on `P i` is pre-deterministic. -/
private theorem add_clause [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : Ctx G)
    {i j : ℕ} {Mi Mj p q : V} {ε : E} (hij : i < j) (hjk : j ≤ C.k)
    (hMi : Mi ∈ G.int) (hMi' : C.lev Mi = i) (hMj : Mj ∈ G.int) (hMj' : C.lev Mj = j)
    (hεG : G.cls ε = none) (hpq : (p, q) = (Mi, Mj) ∨ (p, q) = (Mj, Mi)) :
    (j < C.k → ∀ e₁ e₂, e₁ ≠ e₂ → G.Crosses (C.P (j + 1)) e₁ → G.Crosses (C.P (j + 1)) e₂ →
      ((G.setEdge ε p q (some .plus)).replace (C.P i) (C.P (j + 1)) e₁ e₂).PreDet) ∧
    (j = C.k → ((G.setEdge ε p q (some .plus)).induce (C.P i)).PreDet) := by
  classical
  set G' := G.setEdge ε p q (some .plus) with hG'
  have hik : i ≤ C.k := by omega
  have gne : ∀ e, G.cls e ≠ none → e ≠ ε := fun e h h' => h (h' ▸ hεG)
  have e1 : ∀ f, f ≠ ε → G'.ends f = G.ends f := fun f h => setEdge_ends_ne G p q _ h
  have c1 : ∀ f, f ≠ ε → G'.cls f = G.cls f := fun f h => setEdge_cls_ne G p q _ h
  have eε : G'.ends ε = (Mi, Mj) ∨ G'.ends ε = (Mj, Mi) := by
    have : G'.ends ε = (p, q) := by simp [hG', MGraph.setEdge]
    rw [this]; exact hpq
  have cε : G'.cls ε = some .plus := by simp [hG', MGraph.setEdge]
  have hpq' : (p = Mi ∧ q = Mj) ∨ (p = Mj ∧ q = Mi) := by
    rcases hpq with h | h <;> simp only [Prod.mk.injEq] at h
    · exact Or.inl h
    · exact Or.inr h
  constructor
  · intro hjk' e₁ e₂ hne h1 h2
    have crl : ∀ e, G.Crosses (C.P (j + 1)) e → (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int ∧
        ((C.lev (G.ends e).1 = j ∧ C.lev (G.ends e).2 = j + 1) ∨
          (C.lev (G.ends e).1 = j + 1 ∧ C.lev (G.ends e).2 = j)) := fun e he =>
      C.cc_lev hjk' ((C.cross j hjk' e).1 he)
    obtain ⟨g1, g2, g3⟩ := crl e₁ h1
    obtain ⟨g1', g2', g3'⟩ := crl e₂ h2
    have n1ε : e₁ ≠ ε := gne _ h1.1
    have n2ε : e₂ ≠ ε := gne _ h2.1
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
    have hεS : (G'.ends ε).1 ∈ C.P i \ C.P (j + 1) ∧ (G'.ends ε).2 ∈ C.P i \ C.P (j + 1) := by
      have hi : Mi ∈ C.P i \ C.P (j + 1) := (sdi i hij.le _).2 ⟨hMi, by omega, by omega⟩
      have hj : Mj ∈ C.P i \ C.P (j + 1) := (sdi i hij.le _).2 ⟨hMj, by omega, by omega⟩
      rcases eε with h | h <;> rw [h]
      · exact ⟨hi, hj⟩
      · exact ⟨hj, hi⟩
    refine add_core C (ε := ε) hij hjk hMi hMi' hMj hMj' hεG (fun v => sdi i hij.le v)
      (fun e he a1 b1 a2 a3 b2 b3 => ?_) ?_ ?_ (fun e he hp => ?_) (fun v => ?_)
      (C.spd.2.2.2 _ _ _ _ (chain_isoOrTop C.chain hjk) (C.chain.2.1 j hjk') hne h1 h2)
      (fun e he => ?_) (fun e a1 a2 b1 b2 => ?_) ?_
    · obtain ⟨n1, n2⟩ := nE e a3 b3
      have hin : (G.ends e).1 ∈ C.P i \ C.P (j + 1) ∧ (G.ends e).2 ∈ C.P i \ C.P (j + 1) :=
        ⟨(sdi i hij.le _).2 ⟨a1, a2, a3⟩, (sdi i hij.le _).2 ⟨b1, b2, b3⟩⟩
      refine ⟨by simp [MGraph.replace, n1, e1 e he], ?_⟩
      rw [rep_cls G' n1 n2, ind_cls G' (by rw [e1 e he]; exact hin.1)
        (by rw [e1 e he]; exact hin.2), c1 e he]
    · rw [rep_cls G' (Ne.symm n1ε) (Ne.symm n2ε), ind_cls G' hεS.1 hεS.2, cε]
    · simpa [MGraph.replace, Ne.symm n1ε] using eε
    · have n1 : e ≠ e₁ := by rintro rfl; simp [MGraph.replace] at hp
      have n2 : e ≠ e₂ := by rintro rfl; simp [MGraph.replace, hne.symm] at hp
      rw [rep_cls G' n1 n2] at hp
      have hin := induce_pres (by rw [hp]; simp)
      rw [e1 e he] at hin
      obtain ⟨a1, a2, a3⟩ := (sdi i hij.le _).1 hin.1
      obtain ⟨b1, b2, b3⟩ := (sdi i hij.le _).1 hin.2.1
      exact ⟨a1, b1, a2, a3, b2, b3⟩
    · change v ∈ C.P j \ C.P (j + 1) ↔ _
      rw [sdi j le_rfl]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega, by omega⟩
    · by_cases n1 : e = e₁
      · subst n1
        refine Or.inr ⟨?_, by simp [MGraph.replace], hRe1, ?_, ?_⟩
        · have o1 : G'.outer (C.P (j + 1)) e = G.outer (C.P (j + 1)) e :=
            setEdge_outer_ne G p q _ _ n1ε
          have o2 : G'.outer (C.P (j + 1)) e₂ = G.outer (C.P (j + 1)) e₂ :=
            setEdge_outer_ne G p q _ _ n2ε
          simp [MGraph.replace, o1, o2]
        all_goals omega
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
    · rw [rep_cls G (Ne.symm n1ε) (Ne.symm n2ε)]
      simp [MGraph.induce, hεG]
  · intro hjk2
    have mi : ∀ a, a ≤ C.k → ∀ v, v ∈ C.P a ↔ v ∈ G.int ∧ a ≤ C.lev v ∧ C.lev v ≤ j := by
      intro a ha v
      rw [C.mem_P ha]
      have := C.lev_le v
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩
      · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    have hεS : (G'.ends ε).1 ∈ C.P i ∧ (G'.ends ε).2 ∈ C.P i := by
      have hi : Mi ∈ C.P i := (mi i hik _).2 ⟨hMi, by omega, by omega⟩
      have hj : Mj ∈ C.P i := (mi i hik _).2 ⟨hMj, by omega, by omega⟩
      rcases eε with h | h <;> rw [h]
      · exact ⟨hi, hj⟩
      · exact ⟨hj, hi⟩
    refine add_core C (ε := ε) hij hjk hMi hMi' hMj hMj' hεG (mi i hik)
      (fun e he a1 b1 a2 a3 b2 b3 => ?_) ?_ eε (fun e he hp => ?_) (fun v => ?_)
      (C.spd.2.2.1 _ (chain_isoOrTop C.chain le_rfl) C.chain.2.2) (fun e he => ?_)
      (fun e a1 a2 b1 b2 => ?_) ?_
    · have hin : (G.ends e).1 ∈ C.P i ∧ (G.ends e).2 ∈ C.P i :=
        ⟨(mi i hik _).2 ⟨a1, a2, a3⟩, (mi i hik _).2 ⟨b1, b2, b3⟩⟩
      refine ⟨e1 e he, ?_⟩
      rw [ind_cls G' (by rw [e1 e he]; exact hin.1) (by rw [e1 e he]; exact hin.2), c1 e he]
    · rw [ind_cls G' hεS.1 hεS.2, cε]
    · obtain ⟨h1, h2, -⟩ := induce_pres (by rw [hp]; simp)
      rw [e1 e he] at h1 h2
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
    · simp [MGraph.induce, hεG]

/-! ## Adding a blue solid edge -/

/-- Equality of molecular multigraphs from their four components. -/
private theorem mg_ext' {G H : MGraph V E} (h1 : G.int = H.int) (h2 : G.ext = H.ext)
    (h3 : G.ends = H.ends) (h4 : G.cls = H.cls) : G = H := by
  cases G; cases H; simp_all

/-- Setting `ε` to a blue solid edge commutes with inducing on `S`: the new edge is present in
the induced subgraph when both its ends lie in `S`. -/
private theorem induce_setEdge [DecidableEq V] [DecidableEq E] (G : MGraph V E) (S : Finset V)
    (ε : E) (u v : V) :
    (G.setEdge ε u v (some .plus)).induce S =
      (G.induce S).setEdge ε u v (if u ∈ S ∧ v ∈ S then some .plus else none) := by
  refine mg_ext' rfl rfl rfl (funext fun f => ?_)
  by_cases hf : f = ε
  · subst hf; simp [MGraph.induce, MGraph.setEdge]
  · simp [MGraph.induce, MGraph.setEdge, hf]

/-- Setting `ε` to a blue solid edge commutes with the replacement of [II, Def 5.9 (iii)] of two
other edges. -/
private theorem replace_setEdge [DecidableEq V] [DecidableEq E] (G : MGraph V E)
    (S P : Finset V) {ε e₁ e₂ : E} (u v : V) (h1 : e₁ ≠ ε) (h2 : e₂ ≠ ε) :
    (G.setEdge ε u v (some .plus)).replace S P e₁ e₂ =
      (G.replace S P e₁ e₂).setEdge ε u v
        (if u ∈ S \ P ∧ v ∈ S \ P then some .plus else none) := by
  refine mg_ext' rfl rfl (funext fun f => ?_) (funext fun f => ?_)
  · by_cases hf : f = ε
    · subst hf; simp [MGraph.replace, MGraph.setEdge, Ne.symm h1]
    · by_cases hf1 : f = e₁
      · subst hf1; simp [MGraph.replace, MGraph.setEdge, MGraph.outer, hf, h2]
      · simp [MGraph.replace, MGraph.setEdge, hf, hf1]
  · by_cases hf : f = ε
    · subst hf; simp [MGraph.replace, MGraph.setEdge, MGraph.induce, Ne.symm h1, Ne.symm h2]
    · simp [MGraph.replace, MGraph.setEdge, MGraph.induce, hf]

/-- [II, Def 5.9] for a new blue solid edge between two distinct internal vertices of a
sequentially pre-deterministic graph without ghost edges. -/
private theorem spd_addPlus [DecidableEq V] [DecidableEq E] {G : MGraph V E} {ε : E} {u v : V}
    (hng : ∀ e₀, G.cls e₀ ≠ some .ghost) (hs : G.SPD) (hε : G.cls ε = none) (hu : u ∈ G.int)
    (hv : v ∈ G.int) : (G.setEdge ε u v (some .plus)).SPD := by
  classical
  have : Nonempty E := ⟨ε⟩
  obtain ⟨k, P, hc⟩ := exists_chain (G := G)
  obtain ⟨C, rfl, rfl⟩ := ctx_exists hs hc hng
  have gne : ∀ e, G.cls e ≠ none → e ≠ ε := fun e h h' => h (h' ▸ hε)
  have e1 : ∀ f, f ≠ ε → (G.setEdge ε u v (some .plus)).ends f = G.ends f :=
    fun f h => setEdge_ends_ne G u v _ h
  have c1 : ∀ f, f ≠ ε → (G.setEdge ε u v (some .plus)).cls f = G.cls f :=
    fun f h => setEdge_cls_ne G u v _ h
  -- the sets cut by the new edge
  let Cu : Finset V → Prop := fun S => ¬ (u ∈ S ↔ v ∈ S)
  have hcr' : ∀ S f, f ≠ ε → ((G.setEdge ε u v (some .plus)).Crosses S f ↔ G.Crosses S f) := by
    intro S f hf
    simp only [MGraph.Crosses, MGraph.IsVtx, MGraph.Cut, e1 f hf, c1 f hf]
    rfl
  have hcrε : ∀ S, (G.setEdge ε u v (some .plus)).Crosses S ε ↔ Cu S := by
    intro S
    have he : (G.setEdge ε u v (some .plus)).ends ε = (u, v) := by simp [MGraph.setEdge]
    have hc : (G.setEdge ε u v (some .plus)).cls ε = some .plus := by simp [MGraph.setEdge]
    simp only [MGraph.Crosses, MGraph.IsVtx, MGraph.Cut, he, hc, Cu]
    constructor
    · rintro ⟨-, -, -, -, h⟩; tauto
    · intro h
      exact ⟨by simp, by simp, Or.inl hu, Or.inl hv, by tauto⟩
  have hcr : ∀ S f, ¬ Cu S → ((G.setEdge ε u v (some .plus)).Crosses S f ↔ G.Crosses S f) := by
    intro S f hS
    by_cases hf : f = ε
    · subst hf
      rw [hcrε]
      exact iff_of_false hS fun h => h.1 hε
    · exact hcr' S f hf
  have isoIff : ∀ S, (G.setEdge ε u v (some .plus)).IsIsolated S ↔
      G.IsIsolated S ∧ ¬ Cu S := by
    intro S
    constructor
    · rintro ⟨hS, e₁, e₂, hne, hx⟩
      have nc : ¬ Cu S := by
        intro hcu
        have hε' := (hx ε).1 ((hcrε S).2 hcu)
        have hne' : S.Nonempty := by
          by_cases h : u ∈ S
          · exact ⟨u, h⟩
          · exact ⟨v, by simp only [Cu] at hcu; tauto⟩
        have hns : ¬ G.int ⊆ S := by
          intro h
          exact hcu (iff_of_true (h hu) (h hv))
        obtain ⟨a, b, hab, ha, hb, -, -⟩ := MGraph.claim51 _ _ G hs.1 S hS hne' hns
        have aε : a ≠ ε := gne a ha.1
        have bε : b ≠ ε := gne b hb.1
        have ha' := (hx a).1 ((hcr' S a aε).2 ha)
        have hb' := (hx b).1 ((hcr' S b bε).2 hb)
        rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rcases hε' with h3 | h3 <;>
          first
            | exact hab (h1.trans h2.symm)
            | exact aε (h1.trans h3.symm)
            | exact bε (h2.trans h3.symm)
      exact ⟨⟨hS, e₁, e₂, hne, fun f => by rw [← hcr S f nc]; exact hx f⟩, nc⟩
    · rintro ⟨⟨hS, e₁, e₂, hne, hx⟩, nc⟩
      exact ⟨hS, e₁, e₂, hne, fun f => by rw [hcr S f nc]; exact hx f⟩
  have cutP : ∀ l, l ≤ C.k → (Cu (C.P l) ↔ ¬ (l ≤ C.lev u ↔ l ≤ C.lev v)) := by
    intro l hl
    simp only [Cu, C.mem_P hl, hu, hv, true_and]
  have isoP : ∀ l, 1 ≤ l → l ≤ C.k → G.IsIsolated (C.P l) := by
    intro l h1 h2
    have := (C.chain.2.1 (l - 1) (by omega)).1.1
    rwa [Nat.sub_add_cancel h1] at this
  have santi : ∀ s l, s < l → l ≤ C.k → C.P l ⊂ C.P s := fun s l h1 h2 =>
    Finset.ssubset_of_subset_of_ssubset (chain_anti C.chain h1 h2) (C.chain.2.1 s (by omega)).1.2
  have pull : ∀ S, (G.setEdge ε u v (some .plus)).IsoOrTop S →
      ∃ s ≤ C.k, S = C.P s ∧ ¬ Cu (C.P s) := by
    intro S hS
    have hT : G.IsoOrTop S := by
      rcases hS with h | h
      · exact Or.inl h
      · exact Or.inr ((isoIff S).1 h).1
    obtain ⟨s, hsk, rfl⟩ := iso_top_eq C.chain C.spd.2.1 hT
    refine ⟨s, hsk, rfl, ?_⟩
    rcases hS with h | h
    · change C.P s = G.int at h
      rw [h]; simp [Cu, hu, hv]
    · exact ((isoIff _).1 h).2
  have proper : ∀ s l, s < l → l ≤ C.k → ¬ Cu (C.P l) →
      (G.setEdge ε u v (some .plus)).IsProperIso (C.P s) (C.P l) := fun s l h1 h2 h3 =>
    ⟨(isoIff _).2 ⟨isoP l (by omega) h2, h3⟩, santi s l h1 h2⟩
  have hla := C.lev_le u
  have hlb := C.lev_le v
  -- the members of the chain cut by the new edge
  have unsat : ∀ s l, s < l → l ≤ C.k → (∀ l', s < l' → l' ≤ l → Cu (C.P l')) →
      ¬ Cu (C.P s) → (C.lev u = s ∧ l ≤ C.lev v) ∨ (C.lev v = s ∧ l ≤ C.lev u) := by
    intro s l h1 h2 hn hs'
    have e1 := (cutP s (by omega)).not.1 hs'
    have e2 := (cutP (s + 1) (by omega)).1 (hn (s + 1) (by omega) (by omega))
    have e3 := (cutP l h2).1 (hn l h1 le_rfl)
    rw [not_not] at e1
    by_cases h : s + 1 ≤ C.lev u
    · have hb' : ¬ s + 1 ≤ C.lev v := fun h' => e2 (iff_of_true h h')
      have hbs : C.lev v = s := by have := e1.1 (by omega); omega
      refine Or.inr ⟨hbs, ?_⟩
      by_contra h''; exact e3 (iff_of_false h'' (by omega))
    · have hb' : s + 1 ≤ C.lev v := by by_contra h'; exact e2 (iff_of_false h h')
      have has : C.lev u = s := by have := e1.2 (by omega); omega
      refine Or.inl ⟨has, ?_⟩
      by_contra h''; exact e3 (iff_of_false (by omega) h'')
  refine ⟨dc_sup (H := G) ⟨rfl, fun f hf => ⟨c1 f (gne f hf), e1 f (gne f hf)⟩⟩ hs.1, ?_, ?_, ?_⟩
  · intro P₁ Q₁ hP hQ
    exact C.spd.2.1 P₁ Q₁ ⟨((isoIff _).1 hP.1).1, hP.2⟩ ⟨((isoIff _).1 hQ.1).1, hQ.2⟩
  · intro S hS hmin
    obtain ⟨s, hsk, rfl, hns⟩ := pull S hS
    by_cases hsk' : s = C.k
    · subst hsk'
      rw [induce_setEdge]
      refine preDet_setEdge u v _ (C.spd.2.2.1 _ (chain_isoOrTop C.chain le_rfl) C.chain.2.2)
        (by simp [MGraph.induce, hε]) ?_
      split_ifs with h
      · exact Or.inr ⟨rfl, h⟩
      · exact Or.inl rfl
    · have hn' : ∀ l', s < l' → l' ≤ C.k → Cu (C.P l') := fun l' h1 h2 => by
        intro h3; exact hmin _ (proper s l' h1 h2 fun h => h h3)
      rcases unsat s C.k (by omega) le_rfl (fun l' h1 h2 => hn' l' h1 h2) hns with
        ⟨has, hbk⟩ | ⟨hbs, hak⟩
      · exact (add_clause C (Mi := u) (Mj := v) (ε := ε) (by omega) le_rfl hu has hv (by omega)
          hε (Or.inl rfl)).2 rfl
      · exact (add_clause C (Mi := v) (Mj := u) (ε := ε) (by omega) le_rfl hv hbs hu (by omega)
          hε (Or.inr rfl)).2 rfl
  · intro S P₁ e₁ e₂ hS hmax hne h1 h2
    obtain ⟨s, hsk, rfl, hns⟩ := pull S hS
    have hP₁ := (isoIff _).1 hmax.1.1
    obtain ⟨p, hp1, hpk, rfl⟩ := chain_iso_eq C.chain C.spd.2.1
      ⟨hP₁.1, Finset.ssubset_of_ssubset_of_subset hmax.1.2 (C.Psub s hsk)⟩
    have hsp : s < p := by
      by_contra h
      exact hmax.1.2.2 (chain_anti C.chain (by omega) hsk)
    rw [hcr _ _ hP₁.2] at h1 h2
    by_cases hp' : p = s + 1
    · subst hp'
      rw [replace_setEdge G _ _ u v (gne _ h1.1) (gne _ h2.1)]
      refine preDet_setEdge u v _ (C.spd.2.2.2 _ _ _ _ (chain_isoOrTop C.chain hsk)
        (C.chain.2.1 s (by omega)) hne h1 h2) ?_ ?_
      · simp [MGraph.replace, MGraph.induce, hε, Ne.symm (gne _ h1.1), Ne.symm (gne _ h2.1)]
      · split_ifs with h
        · exact Or.inr ⟨rfl, h⟩
        · exact Or.inl rfl
    · have hn : ∀ l', s < l' → l' ≤ p - 1 → Cu (C.P l') := fun l' h1' h2' => by
        intro h3
        exact hmax.2 _ (proper s l' h1' (by omega) fun h => h h3) (santi l' p (by omega) hpk)
      have e4 := (cutP p hpk).not.1 hP₁.2
      rw [not_not] at e4
      have hpp : p - 1 + 1 = p := by omega
      rcases unsat s (p - 1) (by omega) (by omega) hn hns with ⟨has, hbk⟩ | ⟨hbs, hak⟩
      · have hbp : C.lev v = p - 1 := by
          by_contra h; have := e4.2 (by omega); omega
        have := (add_clause C (Mi := u) (Mj := v) (ε := ε) (i := s) (j := p - 1) (by omega)
          (by omega) hu has hv hbp hε (Or.inl rfl)).1 (by omega)
        rw [hpp] at this
        exact this e₁ e₂ hne h1 h2
      · have hap : C.lev u = p - 1 := by
          by_contra h; have := e4.1 (by omega); omega
        have := (add_clause C (Mi := v) (Mj := u) (ε := ε) (i := s) (j := p - 1) (by omega)
          (by omega) hv hbs hu hap hε (Or.inr rfl)).1 (by omega)
        rw [hpp] at this
        exact this e₁ e₂ hne h1 h2

/-! ## [II, Lemma 6.5 (3), (4)]: adding edges between internal molecules -/

/-- **Adding an edge between two internal molecules** ([II, Lemma 6.5 (3), (4)], the case
`n' = 0`): on a sequentially pre-deterministic graph without ghost edges ([II, Def 5.9]), an
absent edge set to join two internal molecules as a blue solid, diffusive or red solid edge gives
a sequentially pre-deterministic graph. -/
theorem MGraph.spd_addEdge :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e : E) (u v : V) (c : MClass),
    (∀ e₀ : E, G.cls e₀ ≠ some .ghost) → G.SPD → G.cls e = none → u ∈ G.int → v ∈ G.int →
    (c = .plus ∨ c = .diff ∨ c = .minus) → (G.setEdge e u v (some c)).SPD := by
  intro V E _ _ G e u v c hng hs he hu hv hc
  have hplus : (G.setEdge e u v (some .plus)).SPD := spd_addPlus hng hs he hu hv
  rcases hc with rfl | rfl | rfl
  · exact hplus
  · have heq : (G.setEdge e u v (some .plus)).recolor e (some .diff) =
        G.setEdge e u v (some .diff) :=
      mg_ext' rfl rfl rfl (by simp [MGraph.recolor, MGraph.setEdge])
    rw [← heq]
    exact MGraph.spd_conv _ _ _ e ⟨by simp [MGraph.setEdge], by simpa [MGraph.setEdge] using hu,
      by simpa [MGraph.setEdge] using hv⟩ hplus
  · exact (MGraph.spd_red _ _ G e u v (some .minus) (Or.inl he) (Or.inr rfl)).2 hs

section Instances

end Instances

end RBM8D.Graphs
