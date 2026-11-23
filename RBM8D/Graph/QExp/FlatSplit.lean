module

public import RBM8D.Graph.MolDot

@[expose] public section

/-!
# The splitting, `×`-dotted, rebasing and merging steps of the `Q`-expansions in the block reading

The molecular graph in the block reading of every term of `1 = 1_{u = v} + 1_{u ≠ v}`, of
`1_{u ≠ v} = 1 - 1_{u = v}`, of the move of an end within a block, and of `O_merge`, on a graph
with the invariant `Graph.InvB'`, is carried from that of the graph.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Blocks, molecules and the block normal form -/

section Generic

variable {k n : ℕ}

/-- The least internal atom of the block of `u` lies in that block. -/
private theorem FlatSplit_anchor_some {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.anchor u = some b) : Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor at h
  have hb := List.find?_some h
  exact of_decide_eq_true hb

/-- The block of `u` has no internal atom exactly when `Graph.anchor` is `none` at `u`. -/
private theorem FlatSplit_anchor_none {Γ : Graph k n} {u : Atom k n} :
    Γ.anchor u = none ↔ ∀ b, ¬ Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor
  rw [List.find?_eq_none]
  simp

/-- An atom lies in the block of its atom in the block normal form. -/
private theorem FlatSplit_flat_block (Γ : Graph k n) (u : Atom k n) :
    Γ.SameBlock u (Γ.flatAtom u) := by
  cases u with
  | inr b => exact SimpleGraph.Reachable.refl _
  | inl a =>
    rcases hA : Γ.anchor (.inl a) with _ | b
    · simp only [Graph.flatAtom, hA]
      exact SimpleGraph.Reachable.refl _
    · simp only [Graph.flatAtom, hA]
      exact FlatSplit_anchor_some hA

/-- In a block with an internal atom, the atom of the block normal form is internal. -/
private theorem FlatSplit_flat_isRight {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.SameBlock u (.inr b)) : (Γ.flatAtom u).isRight = true := by
  cases u with
  | inr _ => rfl
  | inl a =>
    rcases hA : Γ.anchor (.inl a) with _ | b'
    · exact absurd h (FlatSplit_anchor_none.1 hA b)
    · simp only [Graph.flatAtom, hA]
      rfl

/-- The block of an atom that is not unpinned has an internal atom. -/
private theorem FlatSplit_block_of_not_unpinned {Γ : Graph k n} {u : Atom k n}
    (h : ¬ Γ.Unpinned u) : ∃ b, Γ.SameBlock u (.inr b) := by
  cases u with
  | inr b => exact ⟨b, SimpleGraph.Reachable.refl _⟩
  | inl a =>
    by_contra hn
    push Not at hn
    exact h ⟨rfl, hn⟩

/-- The default value of `List.find?` does not matter when some element satisfies the
predicate. -/
private theorem FlatSplit_find_congr {α : Type} (l : List α) (P P' : α → Bool) (d d' : α)
    (hPP : ∀ x, P x = P' x) (h : ∃ x ∈ l, P x = true) :
    (l.find? P).getD d = (l.find? P').getD d' := by
  have e : P = P' := funext hPP
  subst e
  obtain ⟨x, hx, hp⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨x, hx, hp⟩)
  simp [hr]

/-- A property of all elements satisfying `P` and of the default value holds for the value of
`List.find?`. -/
private theorem FlatSplit_find_getD {α : Type} (l : List α) (P : α → Bool) (d : α)
    (Q : α → Prop) (hP : ∀ b, P b = true → Q b) (hd : Q d) : Q ((l.find? P).getD d) := by
  cases h : l.find? P with
  | none => simpa using hd
  | some r => simpa using hP r (List.find?_some h)

/-- An atom lies in the molecule of its representative. -/
private theorem FlatSplit_molRep_spec (Γ : Graph k n) (u : Atom k n) :
    Γ.SameMol u (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inl rfl
  | inr a =>
    unfold Graph.molRep
    exact FlatSplit_find_getD _ _ a (fun r => Γ.SameMol (.inr a) (.inr r))
      (fun b hb => of_decide_eq_true hb) (Or.inl rfl)

/-- Two atoms have the same representative exactly when they lie in one molecule. -/
private theorem FlatSplit_molRep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.molRep u = Γ.molRep v ↔ Γ.SameMol u v := by
  have E := Γ.sameMol_equivalence
  constructor
  · intro h
    exact E.trans (FlatSplit_molRep_spec Γ u) (h ▸ E.symm (FlatSplit_molRep_spec Γ v))
  · intro h
    cases u with
    | inl a =>
      rcases h with rfl | ⟨h1, -⟩
      · rfl
      · exact absurd h1 (by simp)
    | inr a =>
      cases v with
      | inl b =>
        rcases h with h | ⟨-, h2, -⟩
        · exact absurd h (by simp)
        · exact absurd h2 (by simp)
      | inr b =>
        unfold Graph.molRep
        refine congrArg Sum.inr (FlatSplit_find_congr _ _ _ _ _ (fun c => ?_)
          ⟨b, List.mem_finRange _, decide_eq_true h⟩)
        exact decide_eq_decide.2 ⟨fun h' => E.trans (E.symm h) h', fun h' => E.trans h h'⟩

/-- The dotted edges are edges of the molecular graph. -/
private theorem FlatSplit_dot_le_mol (Γ : Graph k n) : Γ.dotGraph ≤ Γ.molGraph := by
  intro u v huv
  simp only [Graph.dotGraph, Graph.molGraph, SimpleGraph.fromRel_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
  · exact Or.inl ⟨c, hc, by simp [hk, Kind.joinsMol], h1, h2⟩
  · exact Or.inr ⟨c, hc, by simp [hk, Kind.joinsMol], h1, h2⟩

/-- The ends of a dotted edge lie in one block. -/
private theorem FlatSplit_sameBlock_dot {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : Γ.SameBlock c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
    exact SimpleGraph.Reachable.refl _
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩).reachable

/-- The ends of a waved or dotted edge are joined in the molecular graph. -/
private theorem FlatSplit_molReach_comp {Γ : Graph k n} {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind.joinsMol = true) : Γ.molGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩).reachable

/-- Two atoms of one block whose block has an internal atom have the same molecule in the block
normal form. -/
private theorem FlatSplit_molRep_flat {Γ : Graph k n} {u v : Atom k n} {b : Fin n}
    (huv : Γ.SameBlock u v) (hb : Γ.SameBlock u (.inr b)) :
    Γ.molRep (Γ.flatAtom u) = Γ.molRep (Γ.flatAtom v) := by
  have hu := FlatSplit_flat_isRight hb
  have hv := FlatSplit_flat_isRight (huv.symm.trans hb)
  have hb' : Γ.SameBlock (Γ.flatAtom u) (Γ.flatAtom v) :=
    (FlatSplit_flat_block Γ u).symm.trans (huv.trans (FlatSplit_flat_block Γ v))
  exact (FlatSplit_molRep_eq_iff Γ _ _).2
    (Or.inr ⟨hu, hv, SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol Γ) hb'⟩)

/-- Under the first clause of `Graph.ExtClause`, two atoms of one block have the same molecule in
the block normal form. -/
private theorem FlatSplit_molRep_flat_E {Γ : Graph k n}
    (hE1 : ∀ u v : Atom k n, u ≠ v → Γ.SameBlock u v → ∃ b : Fin n, Γ.SameBlock u (.inr b))
    {u v : Atom k n} (h : Γ.SameBlock u v) :
    Γ.molRep (Γ.flatAtom u) = Γ.molRep (Γ.flatAtom v) := by
  by_cases huv : u = v
  · rw [huv]
  · obtain ⟨b, hb⟩ := hE1 u v huv h
    exact FlatSplit_molRep_flat h hb

/-- The representative of every atom is a vertex of `Graph.toMG'`. -/
private theorem FlatSplit_molRep_vtx (Γ : Graph k n) (u : Atom k n) :
    Γ.toMG'.IsVtx (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  | inr a => exact Or.inl (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)

/-- The vertices of `Graph.toMG'` are their own representatives. -/
private theorem FlatSplit_vtx_fix {Γ : Graph k n} {v : Atom k n} (h : Γ.toMG'.IsVtx v) :
    Γ.molRep v = v := by
  rcases h with h | h
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h
    exact (FlatSplit_molRep_eq_iff Γ _ _).2
      (Γ.sameMol_equivalence.symm (FlatSplit_molRep_spec Γ _))
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h
    rfl

/-- The pin edge `.inr a` of `Graph.toMG'` at an external atom whose block has an internal
atom. -/
private theorem FlatSplit_pin_some {Γ : Graph k n} {a : Fin k} {b : Fin n}
    (h : Γ.anchor (.inl a) = some b) :
    Γ.toMG'.cls (.inr a) = some (pinClass a) ∧
      Γ.toMG'.ends (.inr a) = (Γ.molRep (.inr b), .inl a) := by
  simp only [Graph.toMG', h, true_and]

/-- The pin edge `.inr a` of `Graph.toMG'` at an unpinned external atom is absent. -/
private theorem FlatSplit_pin_none {Γ : Graph k n} {a : Fin k} (h : Γ.anchor (.inl a) = none) :
    Γ.toMG'.cls (.inr a) = none := by
  simp only [Graph.toMG', h]

/-- The present edges of `Graph.toMG'` join vertices. -/
private theorem FlatSplit_vtx (Γ : Graph k n) (e : Fin Γ.comps.length ⊕ Fin k)
    (he : Γ.toMG'.cls e ≠ none) :
    Γ.toMG'.IsVtx (Γ.toMG'.ends e).1 ∧ Γ.toMG'.IsVtx (Γ.toMG'.ends e).2 := by
  rcases e with i | a
  · exact ⟨FlatSplit_molRep_vtx Γ _, FlatSplit_molRep_vtx Γ _⟩
  · rcases hA : Γ.anchor (.inl a) with _ | b
    · exact absurd (FlatSplit_pin_none hA) he
    · rw [(FlatSplit_pin_some hA).2]
      exact ⟨FlatSplit_molRep_vtx Γ (.inr b), FlatSplit_molRep_vtx Γ (.inl a)⟩

/-! ### The edge of `Graph.toMG'` given by a component -/

/-- The class of the edge of `Graph.toMG'` given by the component `c`. -/
private def FlatSplit_cls (Γ : Graph k n) (c : Comp (Atom k n)) : Option MClass :=
  if (Γ.flatComp c).kind = .dot ∨
      Γ.molRep (Γ.flatComp c).x = Γ.molRep (Γ.flatComp c).y then none
  else (Γ.flatComp c).kind.mclass

/-- The ends of the edge of `Graph.toMG'` given by the component `c`. -/
private def FlatSplit_ends (Γ : Graph k n) (c : Comp (Atom k n)) : Atom k n × Atom k n :=
  (Γ.molRep (Γ.flatComp c).x, Γ.molRep (Γ.flatComp c).y)

private theorem FlatSplit_cls_of_ne (Γ : Graph k n) {c : Comp (Atom k n)} (hk : c.kind ≠ .dot) :
    FlatSplit_cls Γ c = if Γ.molRep (Γ.flatAtom c.x) = Γ.molRep (Γ.flatAtom c.y) then none
      else c.kind.mclass := by
  simp [FlatSplit_cls, Graph.flatComp, hk]

private theorem FlatSplit_ends_of_ne (Γ : Graph k n) {c : Comp (Atom k n)} (hk : c.kind ≠ .dot) :
    FlatSplit_ends Γ c = (Γ.molRep (Γ.flatAtom c.x), Γ.molRep (Γ.flatAtom c.y)) := by
  simp [FlatSplit_ends, Graph.flatComp, hk]

private theorem FlatSplit_cls_dot (Γ : Graph k n) {c : Comp (Atom k n)} (hk : c.kind = .dot) :
    FlatSplit_cls Γ c = none := by
  simp [FlatSplit_cls, Graph.flatComp, hk]

private theorem FlatSplit_cls_none (Γ : Graph k n) {c : Comp (Atom k n)}
    (hk : c.kind.mclass = none) : FlatSplit_cls Γ c = none := by
  unfold FlatSplit_cls
  split_ifs
  · rfl
  · rw [Graph.flatComp_kind]
    exact hk

private theorem FlatSplit_ne_dot (Γ : Graph k n) {c : Comp (Atom k n)}
    (h : FlatSplit_cls Γ c ≠ none) : c.kind ≠ .dot :=
  fun hk => h (FlatSplit_cls_dot Γ hk)

/-! ### Graphs with the same blocks and molecules -/

/-- Graphs with the same blocks and the same molecules have the same block normal form and the
same representatives. -/
private theorem FlatSplit_reading {Γ Γ' : Graph k n}
    (hB : ∀ u v, Γ'.SameBlock u v ↔ Γ.SameBlock u v)
    (hM : ∀ u v, Γ'.SameMol u v ↔ Γ.SameMol u v) :
    Γ'.anchor = Γ.anchor ∧ Γ'.flatAtom = Γ.flatAtom ∧ Γ'.molRep = Γ.molRep := by
  have ha : Γ'.anchor = Γ.anchor := by
    funext u
    unfold Graph.anchor
    congr 1
    funext b
    exact decide_eq_decide.2 (hB _ _)
  refine ⟨ha, ?_, ?_⟩
  · funext u
    cases u with
    | inl a => simp only [Graph.flatAtom, ha]
    | inr a => rfl
  · funext u
    cases u with
    | inl a => rfl
    | inr a =>
      change Sum.inr ((List.find? (fun b => decide (Γ'.SameMol (.inr a) (.inr b)))
          (List.finRange n)).getD a) =
        Sum.inr ((List.find? (fun b => decide (Γ.SameMol (.inr a) (.inr b)))
          (List.finRange n)).getD a)
      congr 3
      funext b
      exact decide_eq_decide.2 (hM _ _)

/-- Two simple graphs given by relations with the same symmetric closure are equal. -/
private theorem FlatSplit_fromRel_eq {V : Type} {R R' : V → V → Prop}
    (h₁ : ∀ u v, R' u v → R u v ∨ R v u) (h₂ : ∀ u v, R u v → R' u v ∨ R' v u) :
    SimpleGraph.fromRel R' = SimpleGraph.fromRel R := by
  ext u v
  simp only [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h₁ u v h⟩
    · exact ⟨hne, (h₁ v u h).symm⟩
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h₂ u v h⟩
    · exact ⟨hne, (h₂ v u h).symm⟩

/-- The graph of the components satisfying `P` depends only on those components. -/
private theorem FlatSplit_rel_eq_of_mem (P : Comp (Atom k n) → Prop)
    {l l' : List (Comp (Atom k n))} (h : ∀ c, P c → (c ∈ l' ↔ c ∈ l)) :
    SimpleGraph.fromRel (fun u v => ∃ c ∈ l', P c ∧ c.x = u ∧ c.y = v) =
      SimpleGraph.fromRel (fun u v => ∃ c ∈ l, P c ∧ c.x = u ∧ c.y = v) :=
  FlatSplit_fromRel_eq
    (fun _ _ ⟨c, hc, hP, h1, h2⟩ => Or.inl ⟨c, (h c hP).1 hc, hP, h1, h2⟩)
    (fun _ _ ⟨c, hc, hP, h1, h2⟩ => Or.inl ⟨c, (h c hP).2 hc, hP, h1, h2⟩)

/-- The graph of the components satisfying `P` does not depend on the orientation of a last
component. -/
private theorem FlatSplit_rel_eq_swap (P : Comp (Atom k n) → Prop)
    {l l' : List (Comp (Atom k n))} {d d' : Comp (Atom k n)} (h : ∀ c, P c → (c ∈ l' ↔ c ∈ l))
    (hd : P d) (hd' : P d') (hxy : d'.x = d.x ∧ d'.y = d.y ∨ d'.x = d.y ∧ d'.y = d.x) :
    SimpleGraph.fromRel (fun u v => ∃ c ∈ l' ++ [d'], P c ∧ c.x = u ∧ c.y = v) =
      SimpleGraph.fromRel (fun u v => ∃ c ∈ l ++ [d], P c ∧ c.x = u ∧ c.y = v) := by
  have hdm : d ∈ l ++ [d] := List.mem_append_right _ (List.mem_singleton_self _)
  have hdm' : d' ∈ l' ++ [d'] := List.mem_append_right _ (List.mem_singleton_self _)
  apply FlatSplit_fromRel_eq
  · rintro u v ⟨c, hc, hP, hx, hy⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl ⟨c, List.mem_append_left _ ((h c hP).1 hc), hP, hx, hy⟩
    · rw [List.mem_singleton] at hc
      rw [hc] at hx hy
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨d, hdm, hd, h1.symm.trans hx, h2.symm.trans hy⟩
      · exact Or.inr ⟨d, hdm, hd, h2.symm.trans hy, h1.symm.trans hx⟩
  · rintro u v ⟨c, hc, hP, hx, hy⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl ⟨c, List.mem_append_left _ ((h c hP).2 hc), hP, hx, hy⟩
    · rw [List.mem_singleton] at hc
      rw [hc] at hx hy
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨d', hdm', hd', h1.trans hx, h2.trans hy⟩
      · exact Or.inr ⟨d', hdm', hd', h1.trans hy, h2.trans hx⟩

/-- Graphs with the same waved and dotted edges have the same blocks and molecules. -/
private theorem FlatSplit_same_of_mem {Γ Γ' : Graph k n}
    (h : ∀ c, c.kind.joinsMol = true → (c ∈ Γ'.comps ↔ c ∈ Γ.comps)) :
    (∀ u v, Γ'.SameBlock u v ↔ Γ.SameBlock u v) ∧ (∀ u v, Γ'.SameMol u v ↔ Γ.SameMol u v) := by
  have hd : Γ'.dotGraph = Γ.dotGraph :=
    FlatSplit_rel_eq_of_mem (fun c => c.kind = .dot) (fun c hc => h c (by rw [hc]; rfl))
  have hm : Γ'.molGraph = Γ.molGraph :=
    FlatSplit_rel_eq_of_mem (fun c => c.kind.joinsMol = true) h
  refine ⟨fun u v => ?_, fun u v => ?_⟩
  · change Γ'.dotGraph.Reachable u v ↔ Γ.dotGraph.Reachable u v
    rw [hd]
  · change u = v ∨ (u.isRight = true ∧ v.isRight = true ∧ Γ'.molGraph.Reachable u v) ↔
      u = v ∨ (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)
    rw [hm]

/-- Reachability is the same in two graphs whose edges are joined by paths in the other. -/
private theorem FlatSplit_reach_iff {V : Type} {G H : SimpleGraph V}
    (h₁ : ∀ u v, G.Adj u v → H.Reachable u v) (h₂ : ∀ u v, H.Adj u v → G.Reachable u v)
    (u v : V) : G.Reachable u v ↔ H.Reachable u v := by
  have key : ∀ {G H : SimpleGraph V}, (∀ u v, G.Adj u v → H.Reachable u v) →
      ∀ u v, G.Reachable u v → H.Reachable u v := by
    intro G H h u v ⟨w⟩
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons ha _ ih => exact (h _ _ ha).trans ih
  exact ⟨key h₁ u v, key h₂ u v⟩

/-- An element of `l ++ [d]`. -/
private theorem FlatSplit_getElem_append {α : Type} (l : List α) (d : α) (j : ℕ)
    (h : j < (l ++ [d]).length) :
    (l ++ [d])[j] = if h' : j < l.length then l[j] else d := by
  rw [List.getElem_append]
  split_ifs <;> simp

end Generic

/-! ## Changes of names between graphs with the same blocks and molecules -/

section Transport

variable {n : ℕ}

/-- The map of the edges of `Graph.toMG'` sending the component `i` to the component `σ i` (to the
pin edge at `⊗` if `σ i` is out of range) and every pin edge to itself. -/
private def FlatSplit_g {L L' : ℕ} (σ : ℕ → ℕ) : Fin L ⊕ Fin 3 → Fin L' ⊕ Fin 3
  | .inl i => if h : σ i < L' then .inl ⟨σ i, h⟩ else .inr 0
  | .inr a => .inr a

private theorem FlatSplit_g_inl {L L' : ℕ} (σ : ℕ → ℕ) (i : Fin L) (h : σ i < L') :
    (FlatSplit_g σ (.inl i) : Fin L' ⊕ Fin 3) = .inl ⟨σ i, h⟩ := by
  simp [FlatSplit_g, h]

/-- A change of names between `Graph.toMG'` of two graphs with the same blocks and molecules: the
identity on the vertices, the component `i` sent to the component `σ i`. -/
private theorem FlatSplit_tr_main {Γ Γ' : Graph 3 n}
    (hR : Γ'.anchor = Γ.anchor ∧ Γ'.flatAtom = Γ.flatAtom ∧ Γ'.molRep = Γ.molRep)
    (σ : ℕ → ℕ)
    (hfwd : ∀ i : Fin Γ.comps.length, FlatSplit_cls Γ Γ.comps[i] ≠ none →
      ∃ c', Γ'.comps[σ i]? = some c' ∧ FlatSplit_cls Γ c' = FlatSplit_cls Γ Γ.comps[i] ∧
        FlatSplit_ends Γ c' = FlatSplit_ends Γ Γ.comps[i])
    (hinj : ∀ i j : Fin Γ.comps.length, FlatSplit_cls Γ Γ.comps[i] ≠ none →
      FlatSplit_cls Γ Γ.comps[j] ≠ none → σ i = σ j → i = j)
    (hsurj : ∀ j : Fin Γ'.comps.length, FlatSplit_cls Γ Γ'.comps[j] ≠ none →
      ∃ i : Fin Γ.comps.length, FlatSplit_cls Γ Γ.comps[i] ≠ none ∧ σ i = j) :
    Γ.toMG'.Transported Γ'.toMG' := by
  obtain ⟨ha, hf, hm⟩ := hR
  have hfc : Γ'.flatComp = Γ.flatComp := by
    funext c
    unfold Graph.flatComp
    rw [hf]
  have hcls : FlatSplit_cls Γ' = FlatSplit_cls Γ := by
    funext c
    unfold FlatSplit_cls
    rw [hfc, hm]
  have hends : FlatSplit_ends Γ' = FlatSplit_ends Γ := by
    funext c
    unfold FlatSplit_ends
    rw [hfc, hm]
  have hci : ∀ j : Fin Γ'.comps.length,
      Γ'.toMG'.cls (.inl j) = FlatSplit_cls Γ Γ'.comps[j] := fun j => by
    rw [← hcls]
    rfl
  have hei : ∀ j : Fin Γ'.comps.length,
      Γ'.toMG'.ends (.inl j) = FlatSplit_ends Γ Γ'.comps[j] := fun j => by
    rw [← hends]
    rfl
  have hfwd' : ∀ i : Fin Γ.comps.length, FlatSplit_cls Γ Γ.comps[i] ≠ none →
      ∃ h : σ i < Γ'.comps.length,
        FlatSplit_cls Γ Γ'.comps[(⟨σ i, h⟩ : Fin Γ'.comps.length)] = FlatSplit_cls Γ Γ.comps[i] ∧
        FlatSplit_ends Γ Γ'.comps[(⟨σ i, h⟩ : Fin Γ'.comps.length)] =
          FlatSplit_ends Γ Γ.comps[i] := by
    intro i hi
    obtain ⟨c', hc', h1, h2⟩ := hfwd i hi
    obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.1 hc'
    refine ⟨h, ?_, ?_⟩
    · have e' : Γ'.comps[(⟨σ i, h⟩ : Fin Γ'.comps.length)] = c' := e
      rw [e']
      exact h1
    · have e' : Γ'.comps[(⟨σ i, h⟩ : Fin Γ'.comps.length)] = c' := e
      rw [e']
      exact h2
  have hpc : ∀ a, Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a) := by
    intro a
    rcases hA : Γ.anchor (.inl a) with _ | b
    · rw [FlatSplit_pin_none hA, FlatSplit_pin_none (by rw [ha]; exact hA)]
    · rw [(FlatSplit_pin_some hA).1, (FlatSplit_pin_some (by rw [ha]; exact hA)).1]
  have hpe : ∀ a, Γ.toMG'.cls (.inr a) ≠ none →
      Γ'.toMG'.ends (.inr a) = Γ.toMG'.ends (.inr a) := by
    intro a h
    rcases hA : Γ.anchor (.inl a) with _ | b
    · exact absurd (FlatSplit_pin_none hA) h
    · rw [(FlatSplit_pin_some hA).2, (FlatSplit_pin_some (by rw [ha]; exact hA)).2, hm]
  refine ⟨id, FlatSplit_g σ, ?_, Set.injOn_id _, ?_, Finset.image_id.symm, FlatSplit_vtx Γ, ?_, ?_,
    ?_⟩
  · rintro (i | a) (j | b) hi hj h
    · obtain ⟨hσi, -⟩ := hfwd' i hi
      obtain ⟨hσj, -⟩ := hfwd' j hj
      rw [FlatSplit_g_inl σ i hσi, FlatSplit_g_inl σ j hσj] at h
      simp only [Sum.inl.injEq, Fin.mk.injEq] at h
      exact congrArg Sum.inl (hinj i j hi hj h)
    · obtain ⟨hσi, -⟩ := hfwd' i hi
      rw [FlatSplit_g_inl σ i hσi] at h
      exact absurd h (by simp [FlatSplit_g])
    · obtain ⟨hσj, -⟩ := hfwd' j hj
      rw [FlatSplit_g_inl σ j hσj] at h
      exact absurd h (by simp [FlatSplit_g])
    · simp only [FlatSplit_g, Sum.inr.injEq] at h
      rw [h]
  · change Finset.univ.image (fun a : Fin n => Γ'.molRep (.inr a)) =
      (Finset.univ.image fun a : Fin n => Γ.molRep (.inr a)).image id
    rw [hm, Finset.image_id]
  · rintro (i | a) hi
    · obtain ⟨h, h1, -⟩ := hfwd' i hi
      rw [FlatSplit_g_inl σ i h, hci]
      exact h1
    · exact hpc a
  · rintro (i | a) hi
    · obtain ⟨h, -, h2⟩ := hfwd' i hi
      left
      rw [FlatSplit_g_inl σ i h, hei]
      exact h2
    · left
      exact hpe a hi
  · rintro (j | a) hj
    · by_contra hc
      rw [hci] at hc
      obtain ⟨i, hi, hσ⟩ := hsurj j hc
      obtain ⟨h, -⟩ := hfwd' i hi
      apply hj (.inl i) hi
      rw [FlatSplit_g_inl σ i h]
      exact congrArg Sum.inl (Fin.ext hσ)
    · by_contra hc
      rw [hpc] at hc
      exact hj (.inr a) hc rfl

/-- Adding a `×`-dotted edge is a change of names in the block reading. -/
private theorem FlatSplit_tr_xdot (Γ : Graph 3 n) (u v : Atom 3 n) (c' : Coeff) :
    Γ.toMG'.Transported (⟨Γ.comps ++ [mkC .xdot u v], c'⟩ : Graph 3 n).toMG' := by
  obtain ⟨hB, hM⟩ := FlatSplit_same_of_mem (Γ := Γ)
    (Γ' := ⟨Γ.comps ++ [mkC .xdot u v], c'⟩) (fun c hc => by
      change c ∈ Γ.comps ++ [mkC .xdot u v] ↔ c ∈ Γ.comps
      rw [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · exact h
        · simp [mkC, Kind.joinsMol] at hc
      · exact Or.inl)
  have hlast : FlatSplit_cls Γ (mkC .xdot u v) = none := FlatSplit_cls_none Γ rfl
  refine FlatSplit_tr_main (FlatSplit_reading hB hM) (fun i => i) ?_ ?_ ?_
  · intro i _
    refine ⟨Γ.comps[i], ?_, rfl, rfl⟩
    change (Γ.comps ++ [mkC .xdot u v])[(i : ℕ)]? = _
    rw [List.getElem?_append_left i.2, List.getElem?_eq_getElem i.2]
    rfl
  · intro i j _ _ h
    exact Fin.ext h
  · intro j hj
    have e := FlatSplit_getElem_append Γ.comps (mkC .xdot u v) j j.2
    have hj' : FlatSplit_cls Γ (Γ.comps ++ [mkC .xdot u v])[(j : ℕ)] ≠ none := hj
    rw [e] at hj'
    split_ifs at hj' with hjl
    · exact ⟨⟨j, hjl⟩, hj', rfl⟩
    · exact absurd hlast hj'

/-- Removing a `×`-dotted edge is a change of names in the block reading. -/
private theorem FlatSplit_tr_erase (Γ : Graph 3 n) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .xdot) (c' : Coeff) :
    Γ.toMG'.Transported (⟨Γ.comps.eraseIdx i, c'⟩ : Graph 3 n).toMG' := by
  obtain ⟨hB, hM⟩ := FlatSplit_same_of_mem (Γ := Γ)
    (Γ' := ⟨Γ.comps.eraseIdx i, c'⟩) (fun c hc => by
      change c ∈ Γ.comps.eraseIdx i ↔ c ∈ Γ.comps
      rw [List.mem_eraseIdx_iff_getElem]
      constructor
      · rintro ⟨j, hj, -, rfl⟩
        exact List.getElem_mem hj
      · intro h
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
        refine ⟨j, hj, ?_, rfl⟩
        rintro rfl
        rw [hk] at hc
        exact absurd hc (by simp [Kind.joinsMol]))
  have hlen : (Γ.comps.eraseIdx i).length = Γ.comps.length - 1 :=
    List.length_eraseIdx_of_lt hi
  have hni : ∀ j : ℕ, ∀ hj : j < Γ.comps.length, FlatSplit_cls Γ Γ.comps[j] ≠ none → j ≠ i := by
    rintro j hj h rfl
    exact h (FlatSplit_cls_none Γ (by rw [hk]; rfl))
  refine FlatSplit_tr_main (FlatSplit_reading hB hM) (fun j => if j < i then j else j - 1)
    ?_ ?_ ?_
  · intro j hj
    have hji := hni j j.2 hj
    refine ⟨Γ.comps[j], ?_, rfl, rfl⟩
    change (Γ.comps.eraseIdx i)[(if (j : ℕ) < i then (j : ℕ) else j - 1)]? = _
    by_cases hlt : (j : ℕ) < i
    · rw [show (if (j : ℕ) < i then (j : ℕ) else j - 1) = j by simp [hlt],
        List.getElem?_eraseIdx_of_lt hlt, List.getElem?_eq_getElem j.2]
      rfl
    · rw [show (if (j : ℕ) < i then (j : ℕ) else j - 1) = j - 1 by simp [hlt],
        List.getElem?_eraseIdx_of_ge (by omega)]
      have e : (j : ℕ) - 1 + 1 = j := by omega
      rw [e, List.getElem?_eq_getElem j.2]
      rfl
  · intro a b ha hb h
    have h1 := hni a a.2 ha
    have h2 := hni b b.2 hb
    apply Fin.ext
    split_ifs at h <;> omega
  · intro j hj
    have hjl : (j : ℕ) < Γ.comps.length - 1 := hlen ▸ j.2
    have hj' : FlatSplit_cls Γ (Γ.comps.eraseIdx i)[(j : ℕ)] ≠ none := hj
    by_cases hlt : (j : ℕ) < i
    · rw [List.getElem_eraseIdx_of_lt _ hlt] at hj'
      exact ⟨⟨j, by omega⟩, hj', by simp [hlt]⟩
    · rw [List.getElem_eraseIdx_of_ge _ (by omega)] at hj'
      refine ⟨⟨j + 1, by omega⟩, hj', ?_⟩
      have : ¬ (j : ℕ) + 1 < i := by omega
      simp [this]

/-- Changing the orientation of a last dotted edge, and the coefficient, is a change of names in
the block reading. -/
private theorem FlatSplit_tr_swap {l : List (Comp (Atom 3 n))} {p q p' q' : Atom 3 n}
    {c₁ c₂ : Coeff} (hxy : p' = p ∧ q' = q ∨ p' = q ∧ q' = p) :
    (⟨l ++ [mkC .dot p q], c₁⟩ : Graph 3 n).toMG'.Transported
      (⟨l ++ [mkC .dot p' q'], c₂⟩ : Graph 3 n).toMG' := by
  have hd : (⟨l ++ [mkC .dot p' q'], c₂⟩ : Graph 3 n).dotGraph =
      (⟨l ++ [mkC .dot p q], c₁⟩ : Graph 3 n).dotGraph :=
    FlatSplit_rel_eq_swap (fun c => c.kind = .dot) (fun _ _ => Iff.rfl) rfl rfl hxy
  have hm : (⟨l ++ [mkC .dot p' q'], c₂⟩ : Graph 3 n).molGraph =
      (⟨l ++ [mkC .dot p q], c₁⟩ : Graph 3 n).molGraph :=
    FlatSplit_rel_eq_swap (fun c => c.kind.joinsMol = true) (fun _ _ => Iff.rfl) rfl rfl hxy
  have hB : ∀ u v, (⟨l ++ [mkC .dot p' q'], c₂⟩ : Graph 3 n).SameBlock u v ↔
      (⟨l ++ [mkC .dot p q], c₁⟩ : Graph 3 n).SameBlock u v := fun u v => by
    unfold Graph.SameBlock
    rw [hd]
  have hM : ∀ u v, (⟨l ++ [mkC .dot p' q'], c₂⟩ : Graph 3 n).SameMol u v ↔
      (⟨l ++ [mkC .dot p q], c₁⟩ : Graph 3 n).SameMol u v := fun u v => by
    unfold Graph.SameMol
    rw [hm]
  have hlt : ∀ (d : Comp (Atom 3 n)) (hd : d.kind = .dot) (j : ℕ) (hj : j < (l ++ [d]).length),
      FlatSplit_cls (⟨l ++ [mkC .dot p q], c₁⟩ : Graph 3 n) (l ++ [d])[j] ≠ none →
        j < l.length := by
    intro d hd j hj h
    rw [FlatSplit_getElem_append] at h
    split_ifs at h with hjl
    · exact hjl
    · exact absurd (FlatSplit_cls_dot _ hd) h
  refine FlatSplit_tr_main (FlatSplit_reading hB hM) (fun i => i) ?_ ?_ ?_
  · intro i hi
    have hil := hlt _ rfl i i.2 hi
    refine ⟨l[(i : ℕ)], ?_, ?_, ?_⟩
    · change (l ++ [mkC .dot p' q'])[(i : ℕ)]? = _
      rw [List.getElem?_append_left hil, List.getElem?_eq_getElem hil]
    · have e : (l ++ [mkC .dot p q])[(i : ℕ)] = l[(i : ℕ)] := List.getElem_append_left hil
      change _ = FlatSplit_cls _ (l ++ [mkC .dot p q])[(i : ℕ)]
      rw [e]
    · have e : (l ++ [mkC .dot p q])[(i : ℕ)] = l[(i : ℕ)] := List.getElem_append_left hil
      change _ = FlatSplit_ends _ (l ++ [mkC .dot p q])[(i : ℕ)]
      rw [e]
  · intro i j _ _ h
    exact Fin.ext h
  · intro j hj
    have hjl := hlt _ rfl j j.2 hj
    have hjl' : (j : ℕ) < (l ++ [mkC .dot p q]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    refine ⟨⟨j, hjl'⟩, ?_, rfl⟩
    have e1 : (l ++ [mkC .dot p' q'])[(j : ℕ)] = l[(j : ℕ)] := List.getElem_append_left hjl
    have e2 : (l ++ [mkC .dot p q])[(j : ℕ)] = l[(j : ℕ)] := List.getElem_append_left hjl
    have hj' : FlatSplit_cls (⟨l ++ [mkC .dot p q], c₁⟩ : Graph 3 n)
        (l ++ [mkC .dot p' q'])[(j : ℕ)] ≠ none := hj
    change FlatSplit_cls _ (l ++ [mkC .dot p q])[(j : ℕ)] ≠ none
    rw [e2]
    rwa [e1] at hj'

end Transport

/-- The block normal form at `1 = 1_{u = v} + 1_{u ≠ v}` with `v` internal, at any atom `u`
(in particular `⊗`, `⊕`, `⊖`). -/
theorem qElemStep_split_flat :
  ∀ (n : ℕ) (u v : Atom 3 n) (Γ : Graph 3 n), v.isRight = true → Γ.InvB' →
    ∀ t ∈ oSplitT u v Γ, Γ.FlatCarried t.g := by
  rintro n u v Γ hv ⟨-, hC, hE, hG, -⟩ t ht
  unfold oSplitT at ht
  split_ifs at ht with huv
  · rw [List.mem_singleton] at ht
    subst ht
    exact Relation.ReflTransGen.refl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · obtain ⟨b, rfl⟩ : ∃ b, v = .inr b := by
        cases v with
        | inl a => simp at hv
        | inr b => exact ⟨b, rfl⟩
      exact flatCarried_trans 3 n n n Γ _ _
        (addDot_flat n Γ (.inr b) u hC hE hG ⟨b, SimpleGraph.Reachable.refl _⟩)
        (MolDot_flatCarried_of_transported (FlatSplit_tr_swap (Or.inr ⟨rfl, rfl⟩)))
    · exact MolDot_flatCarried_of_transported (FlatSplit_tr_xdot Γ u v Γ.coeff)

/-- The block normal form at `1_{u ≠ v} = 1 - 1_{u = v}` at a `×`-dotted edge without solid
edge. -/
theorem qElemStep_xdot_flat :
  ∀ (n : ℕ) (i : ℕ) (Γ : Graph 3 n), Γ.InvB' → ∀ t ∈ oXdotT i Γ, Γ.FlatCarried t.g := by
  rintro n i Γ ⟨-, hC, hE, hG, -⟩ t ht
  unfold oXdotT at ht
  split at ht
  · rename_i c hc
    split_ifs at ht with hcond
    · obtain ⟨hk, -, -⟩ := hcond
      obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
      have hki : Γ.comps[i].kind = .xdot := by rw [hci]; exact hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact MolDot_flatCarried_of_transported (FlatSplit_tr_erase Γ i hi hki Γ.coeff)
      · have hmem : c ∈ Γ.comps := hci ▸ List.getElem_mem hi
        have hnp := hE.2.1 c hmem hk
        obtain ⟨p, q, hpq, b, hp⟩ : ∃ p q : Atom 3 n, (p = c.x ∧ q = c.y ∨ p = c.y ∧ q = c.x) ∧
            ∃ b, Γ.SameBlock p (.inr b) := by
          by_cases hx : Γ.Unpinned c.x
          · exact ⟨c.y, c.x, Or.inr ⟨rfl, rfl⟩,
              FlatSplit_block_of_not_unpinned (fun hy => hnp ⟨hx, hy⟩)⟩
          · exact ⟨c.x, c.y, Or.inl ⟨rfl, rfl⟩, FlatSplit_block_of_not_unpinned hx⟩
        have h1 := addDot_flat n Γ p q hC hE hG ⟨b, hp⟩
        have hi' : i < (Γ.comps ++ [mkC .dot p q]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        have hk' : (Γ.comps ++ [mkC .dot p q])[i].kind = .xdot := by
          rw [List.getElem_append_left hi]; exact hki
        have h2 := FlatSplit_tr_erase (⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩ : Graph 3 n) i hi' hk'
          Γ.coeff
        have e : (⟨(Γ.comps ++ [mkC .dot p q]).eraseIdx i, Γ.coeff⟩ : Graph 3 n) =
            ⟨Γ.comps.eraseIdx i ++ [mkC .dot p q], Γ.coeff⟩ := by
          rw [List.eraseIdx_append_of_lt_length hi]
        rw [e] at h2
        have h3 := FlatSplit_tr_swap (l := Γ.comps.eraseIdx i) (p := p) (q := q) (p' := c.x)
          (q' := c.y) (c₁ := Γ.coeff) (c₂ := -Γ.coeff) (by
            rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩)
        exact flatCarried_trans 3 n n n Γ _ _ h1
          (flatCarried_trans 3 n n n _ _ _ (MolDot_flatCarried_of_transported h2)
            (MolDot_flatCarried_of_transported h3))
    · rw [List.mem_singleton] at ht
      subst ht
      exact Relation.ReflTransGen.refl
  · rw [List.mem_singleton] at ht
    subst ht
    exact Relation.ReflTransGen.refl

/-- An element of a list satisfying `P` lies in the list after the element `i` is replaced, when
neither the original nor the new element satisfies `P`. -/
private theorem FlatSplit_mem_set {α : Type} {P : α → Prop} {l : List α} {i : ℕ} {a : α}
    (hi : i < l.length) (hPi : ¬ P l[i]) (hPa : ¬ P a) (x : α) (hx : P x) :
    x ∈ l.set i a ↔ x ∈ l := by
  constructor
  · intro h
    rcases List.mem_or_eq_of_mem_set h with h | rfl
    · exact h
    · exact absurd hx hPa
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    have hji : i ≠ j := by
      rintro rfl
      exact hPi hx
    have e : (l.set i a)[j]'(by simpa using hj) = l[j] := List.getElem_set_ne hji _
    rw [← e]
    exact List.getElem_mem _

/-- The block normal form at the move of an end of a component other than a dotted edge to an
atom of its block. -/
theorem qElemStep_rebase_flat :
  ∀ (n : ℕ) (i : ℕ) (Γ : Graph 3 n) (c : Comp (Atom 3 n)) (u v : Atom 3 n),
    Γ.comps[i]? = some c → c.kind ≠ .dot → Γ.SameBlock u v → Γ.InvB' →
    Γ.FlatCarried (⟨Γ.comps.set i
      { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y }, Γ.coeff⟩ :
        Graph 3 n) := by
  rintro n i Γ c u v hc hk hb ⟨-, -, hE, -, -⟩
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  have hcm : c ∈ Γ.comps := hci ▸ List.getElem_mem hi
  have hfx : ∀ w, Γ.SameBlock w (if w = u then v else w) := by
    intro w
    split_ifs with h
    · rw [h]
      exact hb
    · exact SimpleGraph.Reachable.refl _
  have hcx := hfx c.x
  have hcy := hfx c.y
  generalize hc' : ({ c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y } :
    Comp (Atom 3 n)) = c' at hcx hcy ⊢
  have hck : c'.kind = c.kind := by rw [← hc']
  have hcx' : c'.x = if c.x = u then v else c.x := by rw [← hc']
  have hcy' : c'.y = if c.y = u then v else c.y := by rw [← hc']
  rw [← hcx'] at hcx
  rw [← hcy'] at hcy
  have hk' : c'.kind ≠ .dot := by rw [hck]; exact hk
  have hil : i < (Γ.comps.set i c').length := by simpa using hi
  have hc'm : c' ∈ Γ.comps.set i c' := List.mem_set hi c'
  -- blocks
  have hd : (⟨Γ.comps.set i c', Γ.coeff⟩ : Graph 3 n).dotGraph = Γ.dotGraph :=
    FlatSplit_rel_eq_of_mem (fun d => d.kind = .dot)
      (FlatSplit_mem_set (P := fun d => d.kind = .dot) hi (by rw [hci]; exact hk) hk')
  have hB : ∀ a b, (⟨Γ.comps.set i c', Γ.coeff⟩ : Graph 3 n).SameBlock a b ↔ Γ.SameBlock a b :=
    fun a b => by
      unfold Graph.SameBlock
      rw [hd]
  -- molecules
  have hreach : ∀ a b, (⟨Γ.comps.set i c', Γ.coeff⟩ : Graph 3 n).molGraph.Reachable a b ↔
      Γ.molGraph.Reachable a b := by
    apply FlatSplit_reach_iff
    · intro a b hab
      have key : ∀ d ∈ Γ.comps.set i c', d.kind.joinsMol = true → Γ.molGraph.Reachable d.x d.y := by
        intro d hdm hj
        rcases List.mem_or_eq_of_mem_set hdm with hdm | rfl
        · exact FlatSplit_molReach_comp hdm hj
        · exact (SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol Γ) hcx.symm).trans
            ((FlatSplit_molReach_comp hcm (hck ▸ hj)).trans
              (SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol Γ) hcy))
      simp only [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨-, ⟨d, hdm, hj, rfl, rfl⟩ | ⟨d, hdm, hj, rfl, rfl⟩⟩ := hab
      · exact key d hdm hj
      · exact (key d hdm hj).symm
    · intro a b hab
      have hcx2 : (⟨Γ.comps.set i c', Γ.coeff⟩ : Graph 3 n).SameBlock c.x c'.x := (hB _ _).2 hcx
      have hcy2 : (⟨Γ.comps.set i c', Γ.coeff⟩ : Graph 3 n).SameBlock c.y c'.y := (hB _ _).2 hcy
      have key : ∀ d ∈ Γ.comps, d.kind.joinsMol = true →
          (⟨Γ.comps.set i c', Γ.coeff⟩ : Graph 3 n).molGraph.Reachable d.x d.y := by
        intro d hdm hj
        obtain ⟨j, hj', rfl⟩ := List.getElem_of_mem hdm
        by_cases hji : i = j
        · subst hji
          rw [hci] at hj ⊢
          exact (SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol _) hcx2).trans
            ((FlatSplit_molReach_comp (Γ := ⟨Γ.comps.set i c', Γ.coeff⟩) hc'm
              (hck.symm ▸ hj)).trans
              (SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol _) hcy2.symm))
        · have e : (Γ.comps.set i c')[j]'(by simpa using hj') = Γ.comps[j] :=
            List.getElem_set_ne hji _
          have hm : Γ.comps[j] ∈ Γ.comps.set i c' := e ▸ List.getElem_mem _
          exact FlatSplit_molReach_comp (Γ := ⟨Γ.comps.set i c', Γ.coeff⟩) hm hj
      simp only [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨-, ⟨d, hdm, hj, rfl, rfl⟩ | ⟨d, hdm, hj, rfl, rfl⟩⟩ := hab
      · exact key d hdm hj
      · exact (key d hdm hj).symm
  have hM : ∀ a b, (⟨Γ.comps.set i c', Γ.coeff⟩ : Graph 3 n).SameMol a b ↔ Γ.SameMol a b :=
    fun a b => by
      unfold Graph.SameMol
      rw [hreach]
  -- the moved component keeps its edge of `Graph.toMG'`
  have ex : Γ.molRep (Γ.flatAtom c'.x) = Γ.molRep (Γ.flatAtom c.x) :=
    (FlatSplit_molRep_flat_E hE.1 hcx).symm
  have ey : Γ.molRep (Γ.flatAtom c'.y) = Γ.molRep (Γ.flatAtom c.y) :=
    (FlatSplit_molRep_flat_E hE.1 hcy).symm
  have hread :
      FlatSplit_cls Γ c' = FlatSplit_cls Γ c ∧ FlatSplit_ends Γ c' = FlatSplit_ends Γ c := by
    rw [FlatSplit_cls_of_ne Γ hk', FlatSplit_cls_of_ne Γ hk, FlatSplit_ends_of_ne Γ hk',
      FlatSplit_ends_of_ne Γ hk, ex, ey, hck]
    exact ⟨rfl, rfl⟩
  have hget : ∀ (j : ℕ) (hj : j < Γ.comps.length),
      ∃ d, (Γ.comps.set i c')[j]? = some d ∧ FlatSplit_cls Γ d = FlatSplit_cls Γ Γ.comps[j] ∧
        FlatSplit_ends Γ d = FlatSplit_ends Γ Γ.comps[j] := by
    intro j hj
    by_cases hji : i = j
    · subst hji
      refine ⟨c', List.getElem?_set_self hi, ?_⟩
      rw [hci]
      exact hread
    · refine ⟨Γ.comps[j], ?_, rfl, rfl⟩
      rw [List.getElem?_set_ne hji, List.getElem?_eq_getElem hj]
  apply MolDot_flatCarried_of_transported
  refine FlatSplit_tr_main (FlatSplit_reading hB hM) (fun j => j) (fun j _ => hget j j.2) ?_ ?_
  · intro a b _ _ h
    exact Fin.ext h
  · intro j hj
    have hjl : (j : ℕ) < Γ.comps.length := by simpa using j.2
    refine ⟨⟨j, hjl⟩, ?_, rfl⟩
    obtain ⟨d, hd1, hd2, -⟩ := hget j hjl
    have e : (Γ.comps.set i c')[(j : ℕ)] = d := by
      have := List.getElem?_eq_getElem (l := Γ.comps.set i c') (by simpa using hjl)
      rw [hd1] at this
      exact (Option.some.inj this).symm
    have hj' : FlatSplit_cls Γ (Γ.comps.set i c')[(j : ℕ)] ≠ none := hj
    rw [e, hd2] at hj'
    exact hj'

/-! ## `O_merge` in the block reading -/

section Merge

variable {k n : ℕ}

/-- The image of a component under `O_merge` with the representatives `rep` of the blocks and the
map `f` of the atoms, or `none` if it is removed. -/
private def FlatSplit_mc {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

/-- The representative of an atom in the dot blocks. -/
private def FlatSplit_rep (Γ : Graph k n) : Atom k n → Atom k n :=
  blockRep (dotBlocks (allAtoms k n) Γ.comps)

/-- The representatives of the internal atoms, without repetition. -/
private def FlatSplit_roots (Γ : Graph k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => FlatSplit_rep Γ (Sum.inr i)).dedup

/-- The atom map of `O_merge`. -/
private def FlatSplit_f (Γ : Graph k n) : Atom k n → Atom k (FlatSplit_roots Γ).length :=
  fun u => match u with
    | .inl a => .inl a
    | .inr i => .inr ⟨(FlatSplit_roots Γ).idxOf (FlatSplit_rep Γ (.inr i)),
        List.idxOf_lt_length_of_mem
          (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩

private theorem FlatSplit_mergeT_eq (Γ : Graph k n) : Γ.mergeT =
    if Γ.comps.any (fun c => c.kind == .xdot && FlatSplit_rep Γ c.x == FlatSplit_rep Γ c.y) then
      none
    else some ⟨(FlatSplit_roots Γ).length,
      ⟨Γ.comps.filterMap (FlatSplit_mc (FlatSplit_rep Γ) (FlatSplit_f Γ)), Γ.coeff⟩,
      FlatSplit_f Γ⟩ := rfl

/-- Two atoms of one class of `dotBlocks` lie in one block. -/
private theorem FlatSplit_dotBlocks_conn {V : Type} [DecidableEq V] (R : V → V → Prop)
    (hrefl : ∀ u, R u u) (hsymm : ∀ u v, R u v → R v u)
    (htrans : ∀ u v w, R u v → R v w → R u w) (as : List V) :
    ∀ cs : List (Comp V), (∀ c ∈ cs, c.kind = .dot → R c.x c.y) →
      ∀ B ∈ dotBlocks as cs, ∀ u ∈ B, ∀ v ∈ B, R u v := by
  intro cs
  induction cs using List.reverseRecOn with
  | nil =>
    intro _ B hB u hu v hv
    simp only [dotBlocks, List.foldl_nil, List.mem_map] at hB
    obtain ⟨a, -, rfl⟩ := hB
    simp only [List.mem_singleton] at hu hv
    subst hu
    subst hv
    exact hrefl _
  | append_singleton cs c ih =>
    intro hcs B hB u hu v hv
    have ih' := ih (fun c' hc' => hcs c' (List.mem_append_left _ hc'))
    have hsnoc : dotBlocks as (cs ++ [c]) =
        if c.kind = .dot then joinBlocks (dotBlocks as cs) c.x c.y else dotBlocks as cs := by
      simp [dotBlocks, List.foldl_append]
    rw [hsnoc] at hB
    split_ifs at hB with hk
    · unfold joinBlocks at hB
      rw [List.mem_append] at hB
      rcases hB with hB | hB
      · exact ih' B (List.mem_of_mem_filter hB) u hu v hv
      · rw [List.mem_singleton] at hB
        subst hB
        have hxy : R c.x c.y :=
          hcs c (List.mem_append_right _ (List.mem_singleton_self _)) hk
        have key : ∀ w ∈ (dotBlocks as cs).filter (fun B => B.contains c.x || B.contains c.y),
            ∀ z ∈ w, R z c.x := by
          intro w hw z hz
          have hw' := List.mem_filter.1 hw
          have hcont := hw'.2
          simp only [Bool.or_eq_true, List.contains_iff_mem] at hcont
          rcases hcont with hx | hy
          · exact ih' w hw'.1 z hz _ hx
          · exact htrans _ _ _ (ih' w hw'.1 z hz _ hy) (hsymm _ _ hxy)
        rw [List.mem_flatten] at hu hv
        obtain ⟨w₁, hw₁, hu⟩ := hu
        obtain ⟨w₂, hw₂, hv⟩ := hv
        exact htrans _ _ _ (key w₁ hw₁ u hu) (hsymm _ _ (key w₂ hw₂ v hv))
    · exact ih' B hB u hu v hv

/-- The representative of the block of `u` is `u` or an atom of a class containing `u`. -/
private theorem FlatSplit_blockRep_spec {V : Type} [DecidableEq V] (P : List (List V)) (u : V) :
    blockRep P u = u ∨ ∃ B ∈ P, u ∈ B ∧ blockRep P u ∈ B := by
  unfold blockRep
  generalize hf : P.find? (fun B => B.contains u) = o
  rcases o with _ | ⟨_ | ⟨r, rest⟩⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · right
    refine ⟨r :: rest, List.mem_of_find?_eq_some hf, ?_, List.mem_cons_self ..⟩
    simpa [List.contains_iff_mem] using List.find?_some hf

/-- Atoms with the same representative lie in one block. -/
private theorem FlatSplit_rep_block (Γ : Graph k n) (u v : Atom k n)
    (h : FlatSplit_rep Γ u = FlatSplit_rep Γ v) : Γ.SameBlock u v := by
  have hs : ∀ w, Γ.SameBlock w (FlatSplit_rep Γ w) := by
    intro w
    rcases FlatSplit_blockRep_spec (dotBlocks (allAtoms k n) Γ.comps) w with h' | ⟨B, hB, hw, hr⟩
    · change Γ.SameBlock w (blockRep (dotBlocks (allAtoms k n) Γ.comps) w)
      rw [h']
      exact SimpleGraph.Reachable.refl _
    · exact FlatSplit_dotBlocks_conn Γ.SameBlock (fun _ => SimpleGraph.Reachable.refl _)
        (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h') (allAtoms k n) Γ.comps
        (fun _ h hk => FlatSplit_sameBlock_dot h hk) B hB w hw _ hr
  exact (hs u).trans (h ▸ (hs v).symm)

/-- The atom map of `O_merge` identifies only internal atoms with the same representative. -/
private theorem FlatSplit_f_eq (Γ : Graph k n) (i j : Fin n)
    (h : FlatSplit_f Γ (.inr i) = FlatSplit_f Γ (.inr j)) :
    FlatSplit_rep Γ (.inr i) = FlatSplit_rep Γ (.inr j) := by
  simp only [FlatSplit_f, Sum.inr.injEq, Fin.mk.injEq] at h
  have hm : FlatSplit_rep Γ (.inr i) ∈ FlatSplit_roots Γ :=
    List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
  exact (List.idxOf_inj (l := FlatSplit_roots Γ) hm).1 h

/-- Every internal atom of the output of `O_merge` is the image of an internal atom. -/
private theorem FlatSplit_f_surj (Γ : Graph k n) (j : Fin (FlatSplit_roots Γ).length) :
    ∃ i, FlatSplit_f Γ (.inr i) = .inr j := by
  have hj : (FlatSplit_roots Γ)[j.1] ∈ FlatSplit_roots Γ := List.getElem_mem j.2
  obtain ⟨i, -, hi⟩ := List.mem_map.1 (List.mem_dedup.1 hj)
  refine ⟨i, ?_⟩
  simp only [FlatSplit_f, Sum.inr.injEq]
  apply Fin.ext
  simp only
  rw [hi]
  exact (List.nodup_dedup _).idxOf_getElem j.1 j.2

/-- The two shapes of a component kept by `O_merge`. -/
private theorem FlatSplit_mc_cases {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : FlatSplit_mc rep f c = some c') :
    (c' = c.map f ∧ ¬ (c.kind.isSolid = true ∧ rep c.x = rep c.y)) ∨
      (c.kind.isSolid = true ∧ rep c.x = rep c.y ∧
        c' = { c.map f with kind := c.kind.toWeight, y := f c.x }) := by
  unfold FlatSplit_mc at h
  split_ifs at h with h1 h2
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact Or.inr ⟨h2.1, h2.2, (Option.some.inj h).symm⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact Or.inl ⟨(Option.some.inj h).symm, h2⟩

/-- A component other than a dotted edge with distinct images of its ends is kept by `O_merge`
as its image, unless it is a solid edge inside a block. -/
private theorem FlatSplit_mc_map {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (h : c.kind ≠ .dot ∨ f c.x ≠ f c.y)
    (hs : ¬ (c.kind.isSolid = true ∧ rep c.x = rep c.y)) :
    FlatSplit_mc rep f c = some (c.map f) := by
  unfold FlatSplit_mc
  have h1 : ¬ (c.kind == .dot && f c.x == f c.y) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    tauto
  have h2 : ¬ (c.kind.isSolid && rep c.x == rep c.y) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact hs
  split_ifs
  rfl

/-- A solid edge inside a block becomes a weight under `O_merge`. -/
private theorem FlatSplit_mc_weight {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (hs : c.kind.isSolid = true)
    (hr : rep c.x = rep c.y) :
    FlatSplit_mc rep f c = some { c.map f with kind := c.kind.toWeight, y := f c.x } := by
  unfold FlatSplit_mc
  have hk : c.kind ≠ .dot := by
    intro h
    rw [h] at hs
    exact absurd hs (by simp [Kind.isSolid])
  have h1 : ¬ (c.kind == .dot && f c.x == f c.y) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    tauto
  have h2 : (c.kind.isSolid && rep c.x == rep c.y) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hs, hr⟩
  split_ifs
  rfl

/-- The weight of a solid edge is neither a dotted edge, nor waved, nor an edge of the molecular
graph. -/
private theorem FlatSplit_toWeight {κ : Kind} (h : κ.isSolid = true) :
    κ.toWeight ≠ .dot ∧ κ.toWeight.joinsMol = false ∧ κ.toWeight.mclass = none := by
  cases κ <;> simp_all [Kind.isSolid, Kind.toWeight, Kind.joinsMol, Kind.mclass]

/-- Waved and dotted edges are not solid. -/
private theorem FlatSplit_joinsMol_solid {κ : Kind} (h : κ.joinsMol = true) :
    κ.isSolid = false := by
  cases κ <;> simp_all [Kind.joinsMol, Kind.isSolid]

/-! ### Positions in `List.filterMap` -/

private theorem FlatSplit_fm_get {α β : Type} (F : α → Option β) (l : List α) (l' : List β)
    (hl' : l' = l.filterMap F) (i : ℕ) (hi : i < l.length) {b : β} (hb : F l[i] = some b) :
    l'[((l.take i).filterMap F).length]? = some b := by
  subst hl'
  have key : ∀ (A B : List α) (x : α), F x = some b →
      ((A ++ x :: B).filterMap F)[(A.filterMap F).length]? = some b := by
    intro A B x hx
    simp [List.filterMap_append, hx]
  have e : l.take i ++ l[i] :: l.drop (i + 1) = l := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have := key (l.take i) (l.drop (i + 1)) l[i] hb
  rwa [e] at this

private theorem FlatSplit_fm_lt {α β : Type} (F : α → Option β) (l : List α) {i j : ℕ}
    (hij : i < j) (hi : i < l.length) (hb : (F l[i]).isSome = true) :
    ((l.take i).filterMap F).length < ((l.take j).filterMap F).length := by
  have h1 : ((l.take (i + 1)).filterMap F).length = ((l.take i).filterMap F).length + 1 := by
    rw [← List.take_append_getElem hi, List.filterMap_append]
    obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.1 hb
    simp [hb']
  have h2 : ((l.take (i + 1)).filterMap F).length ≤ ((l.take j).filterMap F).length :=
    ((List.take_sublist_take_left hij).filterMap F).length_le
  omega

private theorem FlatSplit_fm_surj {α β : Type} (F : α → Option β) (l : List α) :
    ∀ (j : ℕ) (hj : j < (l.filterMap F).length), ∃ i, ∃ hi : i < l.length,
      F l[i] = some (l.filterMap F)[j] ∧ ((l.take i).filterMap F).length = j := by
  induction l with
  | nil => intro j hj; simp at hj
  | cons a l ih =>
    intro j hj
    rcases ha : F a with _ | b
    · have hj' : j < (l.filterMap F).length := by simpa [List.filterMap_cons, ha] using hj
      obtain ⟨i, hi, h1, h2⟩ := ih j hj'
      refine ⟨i + 1, by simpa using hi, ?_, ?_⟩
      · simp [ha, h1]
      · simp [ha, h2]
    · cases j with
      | zero => exact ⟨0, by simp, by simp [ha], by simp⟩
      | succ j =>
        have hj' : j < (l.filterMap F).length := by
          simp [ha] at hj
          omega
        obtain ⟨i, hi, h1, h2⟩ := ih j hj'
        refine ⟨i + 1, by simpa using hi, ?_, ?_⟩
        · simp [ha, h1]
        · simp [ha, h2]

end Merge

/-- `O_merge` is a change of names in the block reading: the map of the vertices is the map of
the atoms followed by the representative of the molecule, the component `i` is sent to its
position in the output, and under the first clause of `Graph.ExtClause` the solid edges that
become weights were already inside one molecule. -/
private theorem FlatSplit_tr_merge {n m : ℕ} {Γ : Graph 3 n} (Γ' : Graph 3 m)
    (rep : Atom 3 n → Atom 3 n) (f : Atom 3 n → Atom 3 m)
    (hΓ' : Γ'.comps = Γ.comps.filterMap (FlatSplit_mc rep f))
    (hE1 : ∀ u v : Atom 3 n, u ≠ v → Γ.SameBlock u v → ∃ b : Fin n, Γ.SameBlock u (.inr b))
    (hrep : ∀ u v, rep u = rep v → Γ.SameBlock u v)
    (hfl : ∀ a, f (.inl a) = .inl a) (hfr : ∀ i, ∃ j, f (.inr i) = .inr j)
    (hfs : ∀ j, ∃ i, f (.inr i) = .inr j)
    (hfe : ∀ i j, f (.inr i) = f (.inr j) → rep (.inr i) = rep (.inr j)) :
    Γ.toMG'.Transported Γ'.toMG' := by
  have hmem : ∀ c', c' ∈ Γ'.comps ↔ ∃ c ∈ Γ.comps, FlatSplit_mc rep f c = some c' := by
    intro c'
    rw [hΓ']
    exact List.mem_filterMap
  -- the map of the atoms identifies only atoms of one block
  have D1 : ∀ u v, f u = f v → Γ.SameBlock u v := by
    rintro (a | i) (b | j) h
    · rw [hfl, hfl] at h
      cases h
      exact SimpleGraph.Reachable.refl _
    · obtain ⟨j', hj'⟩ := hfr j
      rw [hfl, hj'] at h
      cases h
    · obtain ⟨i', hi'⟩ := hfr i
      rw [hfl, hi'] at h
      cases h
    · exact hrep _ _ (hfe i j h)
  have hR : ∀ u, u.isRight = true → (f u).isRight = true := by
    rintro (a | i) h
    · simp at h
    · obtain ⟨j, hj⟩ := hfr i
      rw [hj]
      rfl
  have hR' : ∀ u, (f u).isRight = true → u.isRight = true := by
    rintro (a | i) h
    · rw [hfl] at h
      simp at h
    · rfl
  have hfsurj : ∀ w : Atom 3 m, ∃ u, f u = w := by
    rintro (a | j)
    · exact ⟨.inl a, hfl a⟩
    · obtain ⟨i, hi⟩ := hfs j
      exact ⟨.inr i, hi⟩
  -- dotted and waved edges of the output
  have H1 : ∀ d' ∈ Γ'.comps, d'.kind = .dot →
      ∃ d ∈ Γ.comps, d.kind = .dot ∧ f d.x = d'.x ∧ f d.y = d'.y := by
    intro d' hd' hk
    obtain ⟨d, hd, hmc⟩ := (hmem d').1 hd'
    rcases FlatSplit_mc_cases hmc with ⟨rfl, -⟩ | ⟨hs, -, rfl⟩
    · exact ⟨d, hd, hk, rfl, rfl⟩
    · exact absurd hk (FlatSplit_toWeight hs).1
  have H2 : ∀ d' ∈ Γ'.comps, d'.kind.joinsMol = true →
      ∃ d ∈ Γ.comps, d.kind.joinsMol = true ∧ f d.x = d'.x ∧ f d.y = d'.y := by
    intro d' hd' hk
    obtain ⟨d, hd, hmc⟩ := (hmem d').1 hd'
    rcases FlatSplit_mc_cases hmc with ⟨rfl, -⟩ | ⟨hs, -, rfl⟩
    · exact ⟨d, hd, hk, rfl, rfl⟩
    · have := (FlatSplit_toWeight hs).2.1
      exact absurd hk (by simp [this])
  have H3 : ∀ d ∈ Γ.comps, d.kind = .dot → Γ'.SameBlock (f d.x) (f d.y) := by
    intro d hd hk
    by_cases he : f d.x = f d.y
    · rw [he]
      exact SimpleGraph.Reachable.refl _
    · have hmc : FlatSplit_mc rep f d = some (d.map f) :=
        FlatSplit_mc_map (Or.inr he) (by rw [hk]; simp [Kind.isSolid])
      exact FlatSplit_sameBlock_dot ((hmem _).2 ⟨d, hd, hmc⟩) hk
  have H4 : ∀ d ∈ Γ.comps, d.kind.joinsMol = true →
      Γ'.molGraph.Reachable (f d.x) (f d.y) := by
    intro d hd hk
    by_cases hdot : d.kind = .dot
    · exact SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol _) (H3 d hd hdot)
    · have hmc : FlatSplit_mc rep f d = some (d.map f) :=
        FlatSplit_mc_map (Or.inl hdot) (by rw [FlatSplit_joinsMol_solid hk]; simp)
      exact FlatSplit_molReach_comp ((hmem _).2 ⟨d, hd, hmc⟩) hk
  -- blocks and molecules are mapped onto blocks and molecules
  have D2 : ∀ x y, Γ.SameBlock x y → Γ'.SameBlock (f x) (f y) := by
    intro x y ⟨w⟩
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab _ ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨-, ⟨d, hd, hk, rfl, rfl⟩ | ⟨d, hd, hk, rfl, rfl⟩⟩ := hab
      · exact H3 d hd hk
      · exact (H3 d hd hk).symm
  have D3 : ∀ x' y', Γ'.SameBlock x' y' → ∀ x y, f x = x' → f y = y' → Γ.SameBlock x y := by
    intro x' y' ⟨w⟩
    induction w with
    | nil =>
      intro x y hx hy
      exact D1 x y (hx.trans hy.symm)
    | @cons a b c hab _ ih =>
      intro x y hx hy
      simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨-, ⟨d', hd', hk, h1, h2⟩ | ⟨d', hd', hk, h1, h2⟩⟩ := hab
      · obtain ⟨d, hd, hk', e1, e2⟩ := H1 d' hd' hk
        exact (D1 x d.x (hx.trans (e1.trans h1).symm)).trans
          ((FlatSplit_sameBlock_dot hd hk').trans (ih d.y y (e2.trans h2) hy))
      · obtain ⟨d, hd, hk', e1, e2⟩ := H1 d' hd' hk
        exact (D1 x d.y (hx.trans (e2.trans h2).symm)).trans
          ((FlatSplit_sameBlock_dot hd hk').symm.trans (ih d.x y (e1.trans h1) hy))
  have D4 : ∀ x y, Γ.molGraph.Reachable x y → Γ'.molGraph.Reachable (f x) (f y) := by
    intro x y ⟨w⟩
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab _ ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      simp only [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨-, ⟨d, hd, hk, rfl, rfl⟩ | ⟨d, hd, hk, rfl, rfl⟩⟩ := hab
      · exact H4 d hd hk
      · exact (H4 d hd hk).symm
  have D5 : ∀ x' y', Γ'.molGraph.Reachable x' y' → ∀ x y, f x = x' → f y = y' →
      Γ.molGraph.Reachable x y := by
    intro x' y' ⟨w⟩
    induction w with
    | nil =>
      intro x y hx hy
      exact SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol Γ) (D1 x y (hx.trans hy.symm))
    | @cons a b c hab _ ih =>
      intro x y hx hy
      simp only [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨-, ⟨d', hd', hk, h1, h2⟩ | ⟨d', hd', hk, h1, h2⟩⟩ := hab
      · obtain ⟨d, hd, hk', e1, e2⟩ := H2 d' hd' hk
        exact (SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol Γ)
          (D1 x d.x (hx.trans (e1.trans h1).symm))).trans
          ((FlatSplit_molReach_comp hd hk').trans (ih d.y y (e2.trans h2) hy))
      · obtain ⟨d, hd, hk', e1, e2⟩ := H2 d' hd' hk
        exact (SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol Γ)
          (D1 x d.y (hx.trans (e2.trans h2).symm))).trans
          ((FlatSplit_molReach_comp hd hk').symm.trans (ih d.x y (e1.trans h1) hy))
  have D4' : ∀ x y, Γ.SameMol x y → Γ'.SameMol (f x) (f y) := by
    rintro x y (rfl | ⟨hx, hy, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hR x hx, hR y hy, D4 x y h⟩
  have D5' : ∀ x y, Γ'.SameMol (f x) (f y) → Γ.SameMol x y := by
    rintro x y (h | ⟨hx, hy, h⟩)
    · rcases x with a | i <;> rcases y with b | j
      · rw [hfl, hfl] at h
        cases h
        exact Or.inl rfl
      · obtain ⟨j', hj'⟩ := hfr j
        rw [hfl, hj'] at h
        cases h
      · obtain ⟨i', hi'⟩ := hfr i
        rw [hfl, hi'] at h
        cases h
      · exact Or.inr ⟨rfl, rfl,
          SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol Γ) (D1 _ _ h)⟩
    · exact Or.inr ⟨hR' x hx, hR' y hy, D5 _ _ h x y rfl rfl⟩
  have D6 : ∀ w, Γ'.molRep (f (Γ.molRep w)) = Γ'.molRep (f w) := fun w =>
    (FlatSplit_molRep_eq_iff Γ' _ _).2
      (D4' _ _ (Γ.sameMol_equivalence.symm (FlatSplit_molRep_spec Γ w)))
  -- identified external atoms
  have D7a : ∀ (a : Fin 3) (b : Fin n), Γ.SameBlock (.inl a) (.inr b) →
      ∃ b', Γ'.anchor (.inl a) = some b' ∧ Γ'.molRep (.inr b') = Γ'.molRep (f (.inr b)) := by
    intro a b hab
    have h := D2 _ _ hab
    rw [hfl] at h
    obtain ⟨j, hj⟩ := hfr b
    rw [hj] at h ⊢
    rcases hA : Γ'.anchor (.inl a) with _ | b'
    · exact absurd h (FlatSplit_anchor_none.1 hA j)
    · refine ⟨b', rfl, (FlatSplit_molRep_eq_iff Γ' _ _).2 (Or.inr ⟨rfl, rfl, ?_⟩)⟩
      exact SimpleGraph.Reachable.mono (FlatSplit_dot_le_mol Γ')
        ((FlatSplit_anchor_some hA).symm.trans h)
  have D7b : ∀ a : Fin 3, Γ.anchor (.inl a) = none → Γ'.anchor (.inl a) = none := by
    intro a hA
    refine FlatSplit_anchor_none.2 fun j hj => ?_
    obtain ⟨i, hi⟩ := hfs j
    exact FlatSplit_anchor_none.1 hA i (D3 _ _ hj (.inl a) (.inr i) (hfl a) hi)
  have D8 : ∀ w, Γ'.molRep (Γ'.flatAtom (f w)) = Γ'.molRep (f (Γ.flatAtom w)) := by
    rintro (a | i)
    · rw [hfl]
      rcases hA : Γ.anchor (.inl a) with _ | b
      · have hA' := D7b a hA
        simp only [Graph.flatAtom, hA, hA', hfl]
      · obtain ⟨b', hb', hm⟩ := D7a a b (FlatSplit_anchor_some hA)
        simp only [Graph.flatAtom, hA, hb']
        exact hm
    · obtain ⟨j, hj⟩ := hfr i
      simp only [Graph.flatAtom, hj]
  -- the map of the vertices
  let φ : Atom 3 n → Atom 3 m := fun w => Γ'.molRep (f w)
  have D9 : ∀ w, Γ'.molRep (Γ'.flatAtom (f w)) = φ (Γ.molRep (Γ.flatAtom w)) := fun w =>
    (D8 w).trans (D6 _).symm
  have D10 : ∀ p q, Γ.toMG'.IsVtx p → Γ.toMG'.IsVtx q → φ p = φ q → p = q := by
    intro p q hp hq h
    have h' : Γ.SameMol p q := D5' p q ((FlatSplit_molRep_eq_iff Γ' _ _).1 h)
    rw [← FlatSplit_vtx_fix hp, ← FlatSplit_vtx_fix hq]
    exact (FlatSplit_molRep_eq_iff Γ _ _).2 h'
  -- the components
  have C1 : ∀ c : Comp (Atom 3 n), c.kind ≠ .dot →
      FlatSplit_cls Γ' (c.map f) = FlatSplit_cls Γ c ∧
        FlatSplit_ends Γ' (c.map f) = (φ (FlatSplit_ends Γ c).1, φ (FlatSplit_ends Γ c).2) := by
    intro c hk
    have hk' : (c.map f).kind ≠ .dot := hk
    rw [FlatSplit_cls_of_ne Γ' hk', FlatSplit_cls_of_ne Γ hk, FlatSplit_ends_of_ne Γ' hk',
      FlatSplit_ends_of_ne Γ hk]
    have ex : Γ'.molRep (Γ'.flatAtom (c.map f).x) = φ (Γ.molRep (Γ.flatAtom c.x)) := D9 c.x
    have ey : Γ'.molRep (Γ'.flatAtom (c.map f).y) = φ (Γ.molRep (Γ.flatAtom c.y)) := D9 c.y
    rw [ex, ey]
    refine ⟨?_, rfl⟩
    have hiff : φ (Γ.molRep (Γ.flatAtom c.x)) = φ (Γ.molRep (Γ.flatAtom c.y)) ↔
        Γ.molRep (Γ.flatAtom c.x) = Γ.molRep (Γ.flatAtom c.y) :=
      ⟨D10 _ _ (FlatSplit_molRep_vtx _ _) (FlatSplit_molRep_vtx _ _), fun h => by rw [h]⟩
    by_cases h : Γ.molRep (Γ.flatAtom c.x) = Γ.molRep (Γ.flatAtom c.y)
    · simp only [h, ite_true]
    · simp only [mt hiff.1 h, h, ite_false]
      rfl
  have C2 : ∀ c, ∀ c', FlatSplit_mc rep f c = some c' → FlatSplit_cls Γ c ≠ none →
      c' = c.map f := by
    intro c c' hmc hp
    rcases FlatSplit_mc_cases hmc with ⟨h, -⟩ | ⟨hs, hr, -⟩
    · exact h
    · exfalso
      apply hp
      rw [FlatSplit_cls_of_ne Γ (FlatSplit_ne_dot Γ hp)]
      simp [FlatSplit_molRep_flat_E hE1 (hrep _ _ hr)]
  have C3 : ∀ c, ∀ c', FlatSplit_mc rep f c = some c' → FlatSplit_cls Γ' c' ≠ none →
      c' = c.map f ∧ c.kind ≠ .dot := by
    intro c c' hmc hp
    rcases FlatSplit_mc_cases hmc with ⟨rfl, -⟩ | ⟨hs, -, rfl⟩
    · exact ⟨rfl, fun hk => hp (FlatSplit_cls_dot Γ' (c := c.map f) hk)⟩
    · exact absurd (FlatSplit_cls_none Γ' (FlatSplit_toWeight hs).2.2) hp
  have C4 : ∀ c, c.kind ≠ .dot → ∃ c', FlatSplit_mc rep f c = some c' := by
    intro c hk
    by_cases hs : c.kind.isSolid = true ∧ rep c.x = rep c.y
    · exact ⟨_, FlatSplit_mc_weight hs.1 hs.2⟩
    · exact ⟨_, FlatSplit_mc_map (Or.inl hk) hs⟩
  -- the map of the edges
  let σ : ℕ → ℕ := fun i => ((Γ.comps.take i).filterMap (FlatSplit_mc rep f)).length
  have hpres : ∀ i : Fin Γ.comps.length, FlatSplit_cls Γ Γ.comps[i] ≠ none →
      ∃ h : σ i < Γ'.comps.length,
        Γ'.comps[(⟨σ i, h⟩ : Fin Γ'.comps.length)] = Γ.comps[i].map f := by
    intro i hi
    obtain ⟨c', hc'⟩ := C4 _ (FlatSplit_ne_dot Γ hi)
    have e := C2 _ _ hc' hi
    rw [e] at hc'
    have h := FlatSplit_fm_get _ _ Γ'.comps hΓ' i i.2 hc'
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 h
    exact ⟨h1, h2⟩
  have hsome : ∀ i : Fin Γ.comps.length, FlatSplit_cls Γ Γ.comps[i] ≠ none →
      (FlatSplit_mc rep f Γ.comps[i]).isSome = true := by
    intro i hi
    obtain ⟨c', hc'⟩ := C4 _ (FlatSplit_ne_dot Γ hi)
    rw [hc']
    rfl
  refine ⟨φ, FlatSplit_g σ, ?_, ?_, ?_, ?_, FlatSplit_vtx Γ, ?_, ?_, ?_⟩
  · rintro (i | a) (j | b) hi hj h
    · obtain ⟨hσi, -⟩ := hpres i hi
      obtain ⟨hσj, -⟩ := hpres j hj
      rw [FlatSplit_g_inl σ i hσi, FlatSplit_g_inl σ j hσj] at h
      simp only [Sum.inl.injEq, Fin.mk.injEq] at h
      congr 1
      rcases lt_trichotomy (i : ℕ) j with hlt | heq | hgt
      · exact absurd h (ne_of_lt (FlatSplit_fm_lt _ _ hlt i.2 (hsome i hi)))
      · exact Fin.ext heq
      · exact absurd h.symm (ne_of_lt (FlatSplit_fm_lt _ _ hgt j.2 (hsome j hj)))
    · obtain ⟨hσi, -⟩ := hpres i hi
      rw [FlatSplit_g_inl σ i hσi] at h
      exact absurd h (by simp [FlatSplit_g])
    · obtain ⟨hσj, -⟩ := hpres j hj
      rw [FlatSplit_g_inl σ j hσj] at h
      exact absurd h (by simp [FlatSplit_g])
    · simp only [FlatSplit_g, Sum.inr.injEq] at h
      rw [h]
  · intro p hp q hq h
    exact D10 p q (by simpa using hp) (by simpa using hq) h
  · change Finset.univ.image (fun j : Fin m => Γ'.molRep (.inr j)) =
      (Finset.univ.image fun i : Fin n => Γ.molRep (.inr i)).image φ
    rw [Finset.image_image]
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := hfs j
      exact ⟨i, by simp only [φ, D6, hi]⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hfr i
      exact ⟨j, by simp only [φ, D6, hj]⟩
  · change Finset.univ.image (fun a : Fin 3 => (.inl a : Atom 3 m)) =
      (Finset.univ.image fun a : Fin 3 => (.inl a : Atom 3 n)).image φ
    rw [Finset.image_image]
    congr 1
    funext a
    change (.inl a : Atom 3 m) = Γ'.molRep (f (.inl a))
    rw [hfl]
    rfl
  · rintro (i | a) hi
    · obtain ⟨h, hc⟩ := hpres i hi
      rw [FlatSplit_g_inl σ i h]
      change FlatSplit_cls Γ' Γ'.comps[(⟨σ i, h⟩ : Fin Γ'.comps.length)] =
        FlatSplit_cls Γ Γ.comps[i]
      rw [hc]
      exact (C1 _ (FlatSplit_ne_dot Γ hi)).1
    · rcases hA : Γ.anchor (.inl a) with _ | b
      · exact absurd (FlatSplit_pin_none hA) hi
      · obtain ⟨b', hb', -⟩ := D7a a b (FlatSplit_anchor_some hA)
        change Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a)
        rw [(FlatSplit_pin_some hA).1, (FlatSplit_pin_some hb').1]
  · rintro (i | a) hi
    · obtain ⟨h, hc⟩ := hpres i hi
      left
      rw [FlatSplit_g_inl σ i h]
      change FlatSplit_ends Γ' Γ'.comps[(⟨σ i, h⟩ : Fin Γ'.comps.length)] = _
      rw [hc]
      exact (C1 _ (FlatSplit_ne_dot Γ hi)).2
    · rcases hA : Γ.anchor (.inl a) with _ | b
      · exact absurd (FlatSplit_pin_none hA) hi
      · obtain ⟨b', hb', hm⟩ := D7a a b (FlatSplit_anchor_some hA)
        left
        change Γ'.toMG'.ends (.inr a) = (φ (Γ.toMG'.ends (.inr a)).1, φ (Γ.toMG'.ends (.inr a)).2)
        rw [(FlatSplit_pin_some hA).2, (FlatSplit_pin_some hb').2]
        simp only [φ, D6, hm, hfl]
        rfl
  · rintro (j | a) hj
    · by_contra hc
      have hjl : (j : ℕ) < (Γ.comps.filterMap (FlatSplit_mc rep f)).length := hΓ' ▸ j.2
      obtain ⟨i, hi, h1, h2⟩ := FlatSplit_fm_surj (FlatSplit_mc rep f) Γ.comps j hjl
      have e : Γ'.comps[j] = (Γ.comps.filterMap (FlatSplit_mc rep f))[(j : ℕ)] :=
        List.getElem_of_eq hΓ' j.2
      have hc' : FlatSplit_cls Γ' Γ'.comps[j] ≠ none := hc
      rw [e] at hc'
      obtain ⟨e', hk⟩ := C3 _ _ h1 hc'
      have hp : FlatSplit_cls Γ Γ.comps[i] ≠ none := by
        rw [← (C1 _ hk).1, ← e']
        exact hc'
      obtain ⟨h, -⟩ := hpres ⟨i, hi⟩ hp
      apply hj (.inl ⟨i, hi⟩) hp
      rw [FlatSplit_g_inl σ _ h]
      exact congrArg Sum.inl (Fin.ext h2)
    · by_contra hc
      rcases hA : Γ.anchor (.inl a) with _ | b
      · exact hc (FlatSplit_pin_none (D7b a hA))
      · exact hj (.inr a) (by rw [(FlatSplit_pin_some hA).1]; simp) rfl

/-- The block normal form at `O_merge` ([II, Def 4.1]). -/
theorem qElemStep_merge_flat :
  ∀ (n : ℕ) (Γ : Graph 3 n) (t : Tracked 3 n), Γ.mergeT = some t → Γ.InvB' → Γ.FlatCarried t.g := by
  rintro n Γ t ht ⟨-, -, hE, -, -⟩
  rw [FlatSplit_mergeT_eq] at ht
  split_ifs at ht
  obtain rfl := Option.some.inj ht
  exact MolDot_flatCarried_of_transported
    (FlatSplit_tr_merge _ (FlatSplit_rep Γ) (FlatSplit_f Γ) rfl hE.1 (FlatSplit_rep_block Γ)
      (fun a => rfl) (fun i => ⟨_, rfl⟩) (FlatSplit_f_surj Γ) (FlatSplit_f_eq Γ))

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

section Helpers

variable {V E : Type}

end Helpers

end Instances

end RBM8D.Graphs
