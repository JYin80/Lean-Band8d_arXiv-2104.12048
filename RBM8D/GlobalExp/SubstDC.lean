module

public import RBM8D.GlobalExp.Strategy
public import RBM8D.Graph.DotBlocks

@[expose] public section

/-!
# [II, Lemma 5.7] and [II, Lemma 6.5 (5)] in the block reading

The doubly connected property of a substituted graph ([II, Lemma 5.7]): let
`G = H.glue x y₁ y₂ (tVar true)` have no dotted edges, be sequentially pre-deterministic in the
block reading, and have the blue solid edge `G_{y₁α}` chosen by Step 2 of [II, Strategy 6.6]. Then
`G_{y₁α}` is redundant ([II, Def 5.9 (iii)]), and substituting into `H` a doubly connected graph
`g` that has no internal atom, is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` (`Graph.DiagRecoll`) or
is rooted at the external atoms (`Graph.RootedAtExt`) gives a doubly connected graph
(`substDCB`).

With the scaling order of the `O_dot` forms of a substituted graph (`glue_oDotT_normalStmt`) as a
hypothesis, [II, Lemma 6.5 (5)] in the block reading: every `O_dot` form of a substituted graph of
`Err` is normal regular without dotted edges, doubly connected, of scaling order
`≥ ord G + D - 3` (`globalGood_row5`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Reachability -/

section Reach

/-- A map that sends each edge to an edge or to a single vertex sends paths to paths. -/
private theorem SubstDC_reach_map {V W : Type*} {A : SimpleGraph V} {B : SimpleGraph W}
    (f : V → W) (h : ∀ u v, A.Adj u v → f u = f v ∨ B.Adj (f u) (f v)) {u v : V}
    (huv : A.Reachable u v) : B.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    rcases h _ _ hadj with he | ha
    · rw [he]
      exact ih
    · exact ha.reachable.trans ih

/-- A graph on a finite type is preconnected if every set of vertices other than `∅` and all of
them is left by an edge. -/
private theorem SubstDC_preconnected_of_cut {V : Type*} [Fintype V] {A : SimpleGraph V}
    (h : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → ∃ a ∈ S, ∃ b ∉ S, A.Adj a b) :
    A.Preconnected := by
  classical
  intro u v
  by_contra hv
  set S := Finset.univ.filter fun w => A.Reachable u w with hS
  have hu : u ∈ S := by simp [S]
  have hvS : v ∉ S := by simp [S, hv]
  obtain ⟨a, ha, b, hb, hab⟩ := h S ⟨u, hu⟩ (fun e => hvS (e ▸ Finset.mem_univ v))
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hb (ha.trans hab.reachable)

end Reach

/-! ## Molecules and nets under maps of the atoms -/

section MapAtoms

variable {k n k' n' : ℕ}

/-- If every waved or dotted component of `Γ` goes under `f` to one atom or to a waved or dotted
component of `Γ'` between the images of its atoms, every edge of the molecular graph of `Γ` goes
to an edge of that of `Γ'` or to one atom. -/
private theorem SubstDC_molGraph_map {Γ : Graph k n} {Γ' : Graph k' n'}
    (f : Atom k n → Atom k' n')
    (hf : ∀ c ∈ Γ.comps, c.kind.joinsMol = true → f c.x = f c.y ∨
      ∃ c' ∈ Γ'.comps, c'.kind.joinsMol = true ∧ c'.x = f c.x ∧ c'.y = f c.y) (u v : Atom k n)
    (h : Γ.molGraph.Adj u v) : f u = f v ∨ Γ'.molGraph.Adj (f u) (f v) := by
  by_cases he : f u = f v
  · exact Or.inl he
  · right
    rw [Graph.molGraph, SimpleGraph.fromRel_adj] at h ⊢
    obtain ⟨-, ⟨c, hc, hj, rfl, rfl⟩ | ⟨c, hc, hj, rfl, rfl⟩⟩ := h
    · rcases hf c hc hj with h' | ⟨c', hc', hj', hx, hy⟩
      · exact absurd h' he
      · exact ⟨he, Or.inl ⟨c', hc', hj', hx, hy⟩⟩
    · rcases hf c hc hj with h' | ⟨c', hc', hj', hx, hy⟩
      · exact absurd h'.symm he
      · exact ⟨he, Or.inr ⟨c', hc', hj', hx, hy⟩⟩

/-- Under the hypothesis of `SubstDC_molGraph_map`, a map that keeps internal atoms internal keeps
two atoms in one molecule. -/
private theorem SubstDC_sameMol_map {Γ : Graph k n} {Γ' : Graph k' n'}
    (f : Atom k n → Atom k' n')
    (hf : ∀ c ∈ Γ.comps, c.kind.joinsMol = true → f c.x = f c.y ∨
      ∃ c' ∈ Γ'.comps, c'.kind.joinsMol = true ∧ c'.x = f c.x ∧ c'.y = f c.y)
    (hR : ∀ u, u.isRight = true → (f u).isRight = true) {u v : Atom k n}
    (h : Γ.SameMol u v) : Γ'.SameMol (f u) (f v) := by
  rcases h with rfl | ⟨hu, hv, hr⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hR u hu, hR v hv, SubstDC_reach_map f (SubstDC_molGraph_map f hf) hr⟩

/-- An edge of the set `B` between two distinct internal atoms is an edge of the net. -/
private theorem SubstDC_net_adj_of_edge {Γ : Graph k n} {B : Finset (Fin Γ.comps.length)}
    {a b : Fin n} (hab : a ≠ b) (i : Fin Γ.comps.length) (hi : i ∈ B)
    (h : (Γ.comps[i].x = .inr a ∧ Γ.comps[i].y = .inr b) ∨
      (Γ.comps[i].x = .inr b ∧ Γ.comps[i].y = .inr a)) : (Γ.net B).Adj a b := by
  rw [Graph.net, SimpleGraph.fromRel_adj]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨hab, Or.inl (Or.inr ⟨i, hi, h1, h2⟩)⟩
  · exact ⟨hab, Or.inr (Or.inr ⟨i, hi, h1, h2⟩)⟩

/-- Two internal atoms of one molecule are joined in every net. -/
private theorem SubstDC_net_reach_of_sameMol {Γ : Graph k n} (B : Finset (Fin Γ.comps.length))
    {a b : Fin n} (h : Γ.SameMol (.inr a) (.inr b)) : (Γ.net B).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · refine SimpleGraph.Adj.reachable ?_
    rw [Graph.net, SimpleGraph.fromRel_adj]
    exact ⟨hab, Or.inl (Or.inl h)⟩

/-- A map of the internal atoms that keeps molecules and sends each edge of `B` between internal
atoms to one atom or to an edge of `B'` sends net paths to net paths. -/
private theorem SubstDC_net_reach_map {Γ : Graph k n} {Γ' : Graph k' n'}
    {B : Finset (Fin Γ.comps.length)} {B' : Finset (Fin Γ'.comps.length)} (fN : Fin n → Fin n')
    (hS : ∀ a b, Γ.SameMol (.inr a) (.inr b) → Γ'.SameMol (.inr (fN a)) (.inr (fN b)))
    (hB : ∀ i ∈ B, ∀ a b, Γ.comps[i].x = .inr a → Γ.comps[i].y = .inr b →
      ∃ i' ∈ B', (Γ'.comps[i'].x = .inr (fN a) ∧ Γ'.comps[i'].y = .inr (fN b)) ∨
        (Γ'.comps[i'].x = .inr (fN b) ∧ Γ'.comps[i'].y = .inr (fN a)))
    {a b : Fin n} (h : (Γ.net B).Reachable a b) : (Γ'.net B').Reachable (fN a) (fN b) := by
  refine SubstDC_reach_map fN (fun u v huv => ?_) h
  by_cases he : fN u = fN v
  · exact Or.inl he
  · right
    rw [Graph.net, SimpleGraph.fromRel_adj] at huv
    obtain ⟨-, (hm | ⟨i, hi, h1, h2⟩) | (hm | ⟨i, hi, h1, h2⟩)⟩ := huv
    · rw [Graph.net, SimpleGraph.fromRel_adj]
      exact ⟨he, Or.inl (Or.inl (hS u v hm))⟩
    · obtain ⟨i', hi', h'⟩ := hB i hi u v h1 h2
      exact SubstDC_net_adj_of_edge he i' hi' h'
    · rw [Graph.net, SimpleGraph.fromRel_adj]
      exact ⟨he, Or.inr (Or.inl (hS v u hm))⟩
    · obtain ⟨i', hi', h'⟩ := hB i hi v u h1 h2
      exact SubstDC_net_adj_of_edge he i' hi' (h'.symm)

end MapAtoms

/-! ## Kind classes -/

/-- The kinds of class `diff` are the diffusive kinds. -/
private theorem SubstDC_mclass_diff (K : Kind) :
    K.mclass = some .diff ↔ K.isDiffusive = true := by
  cases K <;> first
    | (simp [Kind.mclass, Kind.isDiffusive]; done)
    | (rename_i c; cases c <;> simp [Kind.mclass, Kind.isDiffusive])

/-- The kinds of class `diff`, `plus` or `ghost` are the diffusive and the blue kinds. -/
private theorem SubstDC_mclass_blue (K : Kind) :
    (K.mclass = some .diff ∨ K.mclass = some .plus ∨ K.mclass = some .ghost) ↔
      (K.isDiffusive = true ∨ K.isBlue = true) := by
  cases K <;> first
    | (simp [Kind.mclass, Kind.isDiffusive, Kind.isBlue]; done)
    | (rename_i c; cases c <;> simp [Kind.mclass, Kind.isDiffusive, Kind.isBlue])

/-! ## The molecular graph `Graph.toMG'` of a graph without dotted edges -/

section DotFree

variable {k n : ℕ}

/-- The default value of `List.find?` does not matter when some element satisfies the
predicate. -/
private theorem SubstDC_find_congr {α : Type} (l : List α) (P P' : α → Bool) (d d' : α)
    (hPP : ∀ x, P x = P' x) (h : ∃ x ∈ l, P x = true) :
    (l.find? P).getD d = (l.find? P').getD d' := by
  have e : P = P' := funext hPP
  subst e
  obtain ⟨x, hx, hp⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨x, hx, hp⟩)
  simp [hr]

/-- A property of all elements satisfying `P` and of the default value holds for the value of
`List.find?`. -/
private theorem SubstDC_find_getD {α : Type} (l : List α) (P : α → Bool) (d : α) (Q : α → Prop)
    (hP : ∀ b, P b = true → Q b) (hd : Q d) : Q ((l.find? P).getD d) := by
  cases h : l.find? P with
  | none => simpa using hd
  | some r => simpa using hP r (List.find?_some h)

/-- An atom lies in the molecule of its representative. -/
private theorem SubstDC_molRep_spec (Γ : Graph k n) (u : Atom k n) :
    Γ.SameMol u (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inl rfl
  | inr a =>
    unfold Graph.molRep
    exact SubstDC_find_getD _ _ a (fun r => Γ.SameMol (.inr a) (.inr r))
      (fun b hb => of_decide_eq_true hb) (Or.inl rfl)

/-- Two atoms have the same representative exactly when they lie in one molecule. -/
private theorem SubstDC_molRep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.molRep u = Γ.molRep v ↔ Γ.SameMol u v := by
  have E := Γ.sameMol_equivalence
  constructor
  · intro h
    exact E.trans (SubstDC_molRep_spec Γ u) (h ▸ E.symm (SubstDC_molRep_spec Γ v))
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
        refine congrArg Sum.inr (SubstDC_find_congr _ _ _ _ _ (fun c => ?_)
          ⟨b, List.mem_finRange _, decide_eq_true h⟩)
        exact decide_eq_decide.2 ⟨fun h' => E.trans (E.symm h) h', fun h' => E.trans h h'⟩

/-- The representative of an internal atom is an internal vertex of `Graph.toMG'`. -/
private theorem SubstDC_molRep_mem_int (Γ : Graph k n) (a : Fin n) :
    Γ.molRep (.inr a) ∈ Γ.toMG'.int :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

/-- An atom whose representative is an internal vertex of `Graph.toMG'` is internal. -/
private theorem SubstDC_isRight_of_mem_int (Γ : Graph k n) (u : Atom k n)
    (h : Γ.molRep u ∈ Γ.toMG'.int) : ∃ a, u = .inr a := by
  rcases u with a | a
  · obtain ⟨b, -, hb⟩ := Finset.mem_image.1 h
    simp [Graph.molRep] at hb
  · exact ⟨a, rfl⟩

/-- Without dotted edges two atoms lie in one block only if they are equal. -/
private theorem SubstDC_sameBlock_eq {Γ : Graph k n} (hd : Γ.DotFree) {u v : Atom k n}
    (h : Γ.SameBlock u v) : u = v := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ =>
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨c, hc, hk, -⟩ | ⟨c, hc, hk, -⟩⟩ := hadj <;> exact absurd hk (hd c hc)

/-- Without dotted edges no external atom has an anchor. -/
private theorem SubstDC_anchor {Γ : Graph k n} (hd : Γ.DotFree) (a : Fin k) :
    Γ.anchor (.inl a) = none := by
  unfold Graph.anchor
  rw [List.find?_eq_none]
  intro b _ hb
  exact absurd (SubstDC_sameBlock_eq hd (of_decide_eq_true hb)) (by simp)

/-- Without dotted edges the block normal form keeps every component. -/
private theorem SubstDC_flatComp {Γ : Graph k n} (hd : Γ.DotFree) (c : Comp (Atom k n)) :
    Γ.flatComp c = c := by
  have hf : ∀ u, Γ.flatAtom u = u := by
    intro u
    cases u with
    | inr b => rfl
    | inl a => simp only [Graph.flatAtom, SubstDC_anchor hd a]
  unfold Graph.flatComp
  split_ifs
  · rfl
  · rw [hf, hf]

/-- Without dotted edges the pin edges of `Graph.toMG'` are absent. -/
private theorem SubstDC_cls_inr {Γ : Graph k n} (hd : Γ.DotFree) (a : Fin k) :
    Γ.toMG'.cls (.inr a) = none := by
  simp only [Graph.toMG', SubstDC_anchor hd a]

/-- Without dotted edges the edge `.inl i` of `Graph.toMG'` joins the molecules of the two atoms
of the component `i`. -/
private theorem SubstDC_ends_inl {Γ : Graph k n} (hd : Γ.DotFree) (i : Fin Γ.comps.length) :
    Γ.toMG'.ends (.inl i) = (Γ.molRep Γ.comps[i].x, Γ.molRep Γ.comps[i].y) := by
  simp only [Graph.toMG', SubstDC_flatComp hd]

/-- Without dotted edges the edge `.inl i` of `Graph.toMG'` is absent or has the class of the
kind of the component `i`. -/
private theorem SubstDC_cls_inl {Γ : Graph k n} (hd : Γ.DotFree) (i : Fin Γ.comps.length) :
    Γ.toMG'.cls (.inl i) = if Γ.molRep Γ.comps[i].x = Γ.molRep Γ.comps[i].y then none
      else Γ.comps[i].kind.mclass := by
  have hk : Γ.comps[i].kind ≠ .dot := hd _ (List.getElem_mem _)
  simp only [Graph.toMG', SubstDC_flatComp hd, hk, false_or]

end DotFree

/-! ## Nets without one edge -/

section Nets

variable {V E : Type}

/-- The molecular multigraph `G` has disjoint black and blue nets, as in `MGraph.DC`, neither of
which contains the edge `b`. -/
private def SubstDC_NetsWithout (G : MGraph V E) (b : E) : Prop :=
  ∃ black blue : Finset E, Disjoint black blue ∧ b ∉ black ∧ b ∉ blue ∧
    (∀ e ∈ black, G.cls e = some .diff) ∧
    (∀ e ∈ blue, G.cls e = some .diff ∨ G.cls e = some .plus ∨ G.cls e = some .ghost) ∧
    G.Spans black ∧ G.Spans blue

/-- An edge present in the subgraph induced on `P` with the edge `b` removed differs from `b`,
has both ends in `P`, and has its class in `G`. -/
private theorem SubstDC_induce_erase_cls [DecidableEq V] [DecidableEq E] {G : MGraph V E}
    {P : Finset V} {b e : E} (he : ((G.induce P).erase b).cls e ≠ none) :
    e ≠ b ∧ (G.ends e).1 ∈ P ∧ (G.ends e).2 ∈ P ∧ ((G.induce P).erase b).cls e = G.cls e := by
  by_cases heb : e = b
  · subst heb
    simp [MGraph.erase] at he
  · simp only [MGraph.erase, MGraph.induce, Function.update_of_ne heb] at he ⊢
    by_cases hp : (G.ends e).1 ∈ P ∧ (G.ends e).2 ∈ P
    · exact ⟨heb, hp.1, hp.2, by rw [ite_eq_left_iff.2 (fun h => absurd hp h)]⟩
    · rw [ite_eq_right_iff.2 (fun h => absurd h hp)] at he
      exact absurd rfl he

/-- A net of `G`, with its edges inside `P` replaced by a net of the subgraph induced on
`P ⊆ G.int` without the edge `b`, is a net of `G`: a cut that splits `P` is crossed inside `P`,
any other cut by an edge not inside `P`. -/
private theorem SubstDC_spans_replace [DecidableEq V] [DecidableEq E] {G : MGraph V E}
    {P : Finset V} {b : E} {B B' : Finset E} (hP : P ⊆ G.int) (hs : G.Spans B)
    (hs' : ((G.induce P).erase b).Spans B') :
    G.Spans (B.filter (fun e => ¬ ((G.ends e).1 ∈ P ∧ (G.ends e).2 ∈ P)) ∪ B') := by
  intro S hS hne hnot
  by_cases hsplit : (S ∩ P).Nonempty ∧ ¬ P ⊆ S ∩ P
  · obtain ⟨e, he, hc, h1, h2, hcut⟩ := hs' (S ∩ P) Finset.inter_subset_right hsplit.1 hsplit.2
    obtain ⟨-, hp1, hp2, hcl⟩ := SubstDC_induce_erase_cls hc
    refine ⟨e, Finset.mem_union_right _ he, hcl ▸ hc, hP hp1, hP hp2, ?_⟩
    simp only [MGraph.Cut, MGraph.induce, MGraph.erase, Finset.mem_inter] at hcut ⊢
    tauto
  · obtain ⟨e, he, hc, h1, h2, hcut⟩ := hs S hS hne hnot
    refine ⟨e, Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, ?_⟩), hc, h1, h2, hcut⟩
    rintro ⟨hp1, hp2⟩
    simp only [Finset.not_nonempty_iff_eq_empty, not_not, not_and_or] at hsplit
    rcases hsplit with h0 | hsub
    · have : ∀ v ∈ P, v ∉ S := fun v hv hvS =>
        Finset.notMem_empty v (h0 ▸ Finset.mem_inter.2 ⟨hvS, hv⟩)
      rcases hcut with ⟨ha, -⟩ | ⟨-, ha⟩
      · exact this _ hp1 ha
      · exact this _ hp2 ha
    · have : ∀ v ∈ P, v ∈ S := fun v hv => (Finset.mem_inter.1 (hsub hv)).1
      rcases hcut with ⟨-, ha⟩ | ⟨ha, -⟩
      · exact ha (this _ hp2)
      · exact ha (this _ hp1)

/-- If `G` is doubly connected and the subgraph induced on `P ⊆ G.int` without the edge `b`
inside `P` is doubly connected, then `G` has nets without `b`. -/
private theorem SubstDC_nets_of_induce [DecidableEq V] [DecidableEq E] {G : MGraph V E}
    {P : Finset V} {b : E} (hG : G.DC) (hP : P ⊆ G.int)
    (hb : (G.ends b).1 ∈ P ∧ (G.ends b).2 ∈ P) (hI : ((G.induce P).erase b).DC) :
    SubstDC_NetsWithout G b := by
  obtain ⟨bk, bu, hd, hbk, hbu, hsk, hsu⟩ := hG
  obtain ⟨bk', bu', hd', hbk', hbu', hsk', hsu'⟩ := hI
  have hne : ∀ e, ((G.induce P).erase b).cls e = some .diff ∨
      ((G.induce P).erase b).cls e = some .plus ∨ ((G.induce P).erase b).cls e = some .ghost →
      ((G.induce P).erase b).cls e ≠ none := by
    intro e h
    rcases h with h | h | h <;> rw [h] <;> simp
  have hk' : ∀ e ∈ bk', e ≠ b ∧ (G.ends e).1 ∈ P ∧ (G.ends e).2 ∈ P ∧ G.cls e = some .diff := by
    intro e he
    have hc := hbk' e he
    obtain ⟨h1, h2, h3, h4⟩ := SubstDC_induce_erase_cls (hne e (Or.inl hc))
    exact ⟨h1, h2, h3, h4 ▸ hc⟩
  have hu' : ∀ e ∈ bu', e ≠ b ∧ (G.ends e).1 ∈ P ∧ (G.ends e).2 ∈ P ∧
      (G.cls e = some .diff ∨ G.cls e = some .plus ∨ G.cls e = some .ghost) := by
    intro e he
    have hc := hbu' e he
    obtain ⟨h1, h2, h3, h4⟩ := SubstDC_induce_erase_cls (hne e hc)
    exact ⟨h1, h2, h3, h4 ▸ hc⟩
  refine ⟨bk.filter (fun e => ¬ ((G.ends e).1 ∈ P ∧ (G.ends e).2 ∈ P)) ∪ bk',
    bu.filter (fun e => ¬ ((G.ends e).1 ∈ P ∧ (G.ends e).2 ∈ P)) ∪ bu', ?_, ?_, ?_, ?_, ?_,
    SubstDC_spans_replace hP hsk hsk', SubstDC_spans_replace hP hsu hsu'⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with ⟨h1, n1⟩ | h1 <;> rcases h2 with ⟨h2, n2⟩ | h2
    · exact Finset.disjoint_left.1 hd h1 h2
    · exact n1 ⟨(hu' e h2).2.1, (hu' e h2).2.2.1⟩
    · exact n2 ⟨(hk' e h1).2.1, (hk' e h1).2.2.1⟩
    · exact Finset.disjoint_left.1 hd' h1 h2
  · simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and]
    exact ⟨fun _ h => h hb.1 hb.2, fun h => (hk' b h).1 rfl⟩
  · simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and]
    exact ⟨fun _ h => h hb.1 hb.2, fun h => (hu' b h).1 rfl⟩
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact hbk e (Finset.mem_filter.1 h).1
    · exact (hk' e h).2.2.2
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact hbu e (Finset.mem_filter.1 h).1
    · exact (hu' e h).2.2.2

/-- Changing no edge into a `Θ` edge keeps the graph. -/
private theorem SubstDC_convert_nil [DecidableEq E] (G : MGraph V E) : G.convert [] = G := by
  cases G
  simp [MGraph.convert]

end Nets

/-! ## The edge chosen by Step 2 is redundant -/

section Step2

variable {k n : ℕ}

/-- In a graph without dotted edges whose molecular graph `Graph.toMG'` is sequentially
pre-deterministic, the molecular graph has nets without a blue solid edge that Step 2 of
[II, Strategy 6.6] may expand ([II, Def 5.9 (iii)], the first edge of a pre-deterministic order
is redundant). -/
private theorem SubstDC_nets_step2 {Γ : Graph k n} (hd : Γ.DotFree) (hs : spdPM' Γ)
    {i : Fin Γ.comps.length} (h : Γ.Step2EdgeB i) : SubstDC_NetsWithout Γ.toMG' (.inl i) := by
  have hdc : Γ.toMG'.DC := hs.1
  obtain ⟨-, hx, hy, hsm | ⟨l, hl, hh⟩⟩ := h
  · obtain ⟨bk, bu, hdj, hbk, hbu, hsk, hsu⟩ := hdc
    have hcl : Γ.toMG'.cls (.inl i) = none := by
      rw [SubstDC_cls_inl hd]
      exact ite_eq_left_iff.2 fun h => absurd ((SubstDC_molRep_eq_iff Γ _ _).2 hsm) h
    refine ⟨bk, bu, hdj, fun h => ?_, fun h => ?_, hbk, hbu, hsk, hsu⟩
    · have := hbk _ h
      rw [hcl] at this
      exact absurd this (by simp)
    · rcases hbu _ h with h' | h' | h' <;> rw [hcl] at h' <;> exact absurd h' (by simp)
  · cases l with
    | nil => simp at hh
    | cons a l' =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have h0 := hl.2.2 0 (by simp)
    simp only [List.take_zero, SubstDC_convert_nil, List.getElem_cons_zero] at h0
    refine SubstDC_nets_of_induce hdc
      (by unfold MGraph.MIS; exact @Finset.filter_subset _ _ (fun _ => Classical.propDecidable _) _)
      ?_ h0.2.2
    rw [SubstDC_ends_inl hd]
    exact ⟨hx, hy⟩

/-- Nets of `Graph.toMG'` of a graph without dotted edges give nets of the graph with the same
components. -/
private theorem SubstDC_spans_of_toMG' {Γ : Graph k n} (hd : Γ.DotFree)
    {B : Finset (Fin Γ.comps.length ⊕ Fin k)} (hs : Γ.toMG'.Spans B) :
    Γ.Spans (Finset.univ.filter fun j => (Sum.inl j : Fin Γ.comps.length ⊕ Fin k) ∈ B) := by
  classical
  refine SubstDC_preconnected_of_cut fun S hS hSu => ?_
  by_cases hcl : ∃ a ∈ S, ∃ c ∉ S, Γ.SameMol (.inr a) (.inr c)
  · obtain ⟨a, ha, c, hc, hm⟩ := hcl
    refine ⟨a, ha, c, hc, ?_⟩
    rw [Graph.net, SimpleGraph.fromRel_adj]
    exact ⟨fun e => hc (e ▸ ha), Or.inl (Or.inl hm)⟩
  push Not at hcl
  have hmem : ∀ u : Fin n, Γ.molRep (.inr u) ∈ S.image (fun a => Γ.molRep (.inr a)) ↔ u ∈ S := by
    intro u
    constructor
    · intro h
      obtain ⟨a, ha, he⟩ := Finset.mem_image.1 h
      by_contra hu
      exact hcl a ha u hu ((SubstDC_molRep_eq_iff Γ _ _).1 he)
    · intro h
      exact Finset.mem_image_of_mem _ h
  obtain ⟨c, hc⟩ : ∃ c, c ∉ S := by
    by_contra h
    push Not at h
    exact hSu (Finset.eq_univ_iff_forall.2 h)
  obtain ⟨a₀, ha₀⟩ := hS
  obtain ⟨e, he, hce, h1, h2, hcut⟩ := hs (S.image fun a => Γ.molRep (.inr a))
    (fun v hv => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hv
      exact SubstDC_molRep_mem_int Γ a)
    ⟨_, Finset.mem_image_of_mem _ ha₀⟩
    (fun h => hc ((hmem c).1 (h (SubstDC_molRep_mem_int Γ c))))
  rcases e with j | a
  · simp only [MGraph.Cut] at hcut
    rw [SubstDC_ends_inl hd] at h1 h2 hcut
    obtain ⟨u, hu⟩ := SubstDC_isRight_of_mem_int Γ _ h1
    obtain ⟨v, hv⟩ := SubstDC_isRight_of_mem_int Γ _ h2
    have hjB : j ∈ Finset.univ.filter fun j => (Sum.inl j : Fin Γ.comps.length ⊕ Fin k) ∈ B :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
    simp only [hu, hv, hmem] at hcut
    rcases hcut with ⟨huS, hvS⟩ | ⟨huS, hvS⟩
    · exact ⟨u, huS, v, hvS, SubstDC_net_adj_of_edge (fun e => hvS (e ▸ huS)) j hjB
        (Or.inl ⟨hu, hv⟩)⟩
    · exact ⟨v, hvS, u, huS, SubstDC_net_adj_of_edge (fun e => huS (e ▸ hvS)) j hjB
        (Or.inr ⟨hu, hv⟩)⟩
  · exact absurd (SubstDC_cls_inr hd a) hce

/-- In a graph without dotted edges whose molecular graph `Graph.toMG'` is sequentially
pre-deterministic, a blue solid edge that Step 2 may expand is redundant: there are disjoint
black and blue nets of the graph, without that edge. -/
private theorem SubstDC_atom_nets {Γ : Graph k n} (hd : Γ.DotFree) (hs : spdPM' Γ)
    {i : Fin Γ.comps.length} (h : Γ.Step2EdgeB i) :
    ∃ black blue : Finset (Fin Γ.comps.length), Disjoint black blue ∧ i ∉ black ∧ i ∉ blue ∧
      (∀ j ∈ black, Γ.comps[j].kind.isDiffusive = true) ∧
      (∀ j ∈ blue, Γ.comps[j].kind.isDiffusive = true ∨ Γ.comps[j].kind.isBlue = true) ∧
      Γ.Spans black ∧ Γ.Spans blue := by
  classical
  obtain ⟨bk, bu, hdj, hik, hiu, hbk, hbu, hsk, hsu⟩ := SubstDC_nets_step2 hd hs h
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, SubstDC_spans_of_toMG' hd hsk, SubstDC_spans_of_toMG' hd hsu⟩
  · rw [Finset.disjoint_left]
    intro j h1 h2
    exact Finset.disjoint_left.1 hdj (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
  · intro h'
    exact hik (Finset.mem_filter.1 h').2
  · intro h'
    exact hiu (Finset.mem_filter.1 h').2
  · intro j hj
    have hc := hbk _ (Finset.mem_filter.1 hj).2
    rw [SubstDC_cls_inl hd] at hc
    split_ifs at hc
    exact (SubstDC_mclass_diff _).1 hc
  · intro j hj
    have hc := hbu _ (Finset.mem_filter.1 hj).2
    rw [SubstDC_cls_inl hd] at hc
    split_ifs at hc with h'
    · rcases hc with hc | hc | hc <;> exact absurd hc (by simp)
    · exact (SubstDC_mclass_blue _).1 hc

end Step2

/-! ## The substituted graph -/

section Glue

variable {m n' : ℕ}

/-- The components of `H.glue x y₁ y₂ (tVar true)` after those of `H`: `s_{αx}`, `G_{y₁α}`,
`Ḡ_{y₂α}` and the two `×`-dotted edges. -/
private theorem SubstDC_host_comps (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) :
    (H.glue x y₁ y₂ (tVar true)).comps = liftCs 1 H.comps ++
      [⟨.waved .s, newA 0, liftA 1 x, [], none⟩, ⟨.G .plus, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩, ⟨.xdot, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.xdot, liftA 1 y₂, newA 0, [], none⟩] := by
  rfl

private theorem SubstDC_liftCs_length {j : ℕ} (cs : List (Comp (Atom 3 m))) :
    (liftCs j cs).length = cs.length := by
  simp [liftCs]

/-- The components of `H.glue x y₁ y₂ g'` of index below the number of components of `H` are
those of `H`. -/
private theorem SubstDC_glue_getElem_left (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g' : Graph 3 n')
    (i : ℕ) (hi : i < H.comps.length) (h : i < (H.glue x y₁ y₂ g').comps.length) :
    (H.glue x y₁ y₂ g').comps[i] = Comp.map (liftA n') H.comps[i] := by
  simp only [Graph.glue]
  rw [List.getElem_append_left (by rw [SubstDC_liftCs_length]; exact hi)]
  simp [liftCs]

/-- The components of `H.glue x y₁ y₂ g.swapSolid` after those of `H` are the images of the
components of `g` with the atoms of their solid edges exchanged. -/
private theorem SubstDC_glue_getElem_right (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (i : Fin g.comps.length)
    (h : H.comps.length + i.val < (H.glue x y₁ y₂ g.swapSolid).comps.length) :
    (H.glue x y₁ y₂ g.swapSolid).comps[H.comps.length + i.val] =
      Comp.map (glueAtom x y₁ y₂) g.comps[i].swapSolid := by
  simp only [Graph.glue]
  rw [List.getElem_append_right (by rw [SubstDC_liftCs_length]; omega)]
  simp [SubstDC_liftCs_length, Graph.swapSolid]

private theorem SubstDC_glue_length (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n') :
    (H.glue x y₁ y₂ g.swapSolid).comps.length = H.comps.length + g.comps.length := by
  simp [Graph.glue, SubstDC_liftCs_length, Graph.swapSolid]

private theorem SubstDC_host_length (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) :
    (H.glue x y₁ y₂ (tVar true)).comps.length = H.comps.length + 5 := by
  rw [SubstDC_host_comps]
  simp [SubstDC_liftCs_length]

/-- A diffusive or blue component of `H.glue x y₁ y₂ (tVar true)` is a component of `H` or the
blue solid edge `G_{y₁α}`. -/
private theorem SubstDC_host_idx (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (j : Fin (H.glue x y₁ y₂ (tVar true)).comps.length)
    (hk : (H.glue x y₁ y₂ (tVar true)).comps[j].kind.isDiffusive = true ∨
      (H.glue x y₁ y₂ (tVar true)).comps[j].kind.isBlue = true) :
    j.val < H.comps.length ∨ j.val = H.comps.length + 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨d, hd⟩ : ∃ d, j.val = H.comps.length + d := ⟨j.val - H.comps.length, by omega⟩
  have hj : j.val < H.comps.length + 5 := SubstDC_host_length H x y₁ y₂ ▸ j.2
  have hcj : (H.glue x y₁ y₂ (tVar true)).comps[j] =
      [(⟨.waved .s, newA 0, liftA 1 x, [], none⟩ : Comp (Atom 3 (m + 1))),
        ⟨.G .plus, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.G .minus, liftA 1 y₂, newA 0, [], none⟩, ⟨.xdot, liftA 1 y₁, newA 0, [], none⟩,
        ⟨.xdot, liftA 1 y₂, newA 0, [], none⟩][d]'(by
          simp only [List.length_cons, List.length_nil]; omega) := by
    simp only [Fin.getElem_fin, SubstDC_host_comps]
    rw [List.getElem_append_right (by rw [SubstDC_liftCs_length]; omega)]
    simp only [SubstDC_liftCs_length, hd, Nat.add_sub_cancel_left]
  rw [hcj] at hk
  have hd5 : d < 5 := by omega
  have hd1 : d ≠ 1 := by omega
  interval_cases d <;> simp [Kind.isDiffusive, Kind.isBlue] at hk hd1

/-- The internal atoms of `H.glue x y₁ y₂ (tVar true)` sent to those of `H.glue x y₁ y₂ g'`: the
atoms of `H` to themselves, the atom `α` to `x = .inr x₀`. -/
private def SubstDC_fN (x₀ : Fin m) (j : Fin (m + 1)) : Fin (m + n') :=
  if h : j.val < m then ⟨j.val, by omega⟩ else Fin.castAdd n' x₀

/-- The atom map of `SubstDC_fN`. -/
private def SubstDC_fA (x₀ : Fin m) : Atom 3 (m + 1) → Atom 3 (m + n') :=
  Sum.map id (SubstDC_fN (n' := n') x₀)

private theorem SubstDC_fA_liftA (x₀ : Fin m) (u : Atom 3 m) :
    SubstDC_fA (n' := n') x₀ (liftA 1 u) = liftA n' u := by
  rcases u with a | a
  · rfl
  · simp only [SubstDC_fA, liftA, Sum.map_inr, SubstDC_fN, Fin.val_castAdd, a.2, dite_true]
    rfl

private theorem SubstDC_fA_newA (x₀ : Fin m) :
    SubstDC_fA (n' := n') x₀ (newA (n := m) (j := 1) 0) = liftA n' (.inr x₀) := by
  simp only [SubstDC_fA, newA, Sum.map_inr, SubstDC_fN, Fin.natAdd, Fin.val_zero, add_zero,
    lt_irrefl, dite_false]
  rfl

/-- The components of `B` and of `Bg` as a set of components of `H.glue x y₁ y₂ g.swapSolid`:
the components of `H` whose index lies in `B`, and the images of the components of `g` whose
index lies in `Bg`. -/
private def SubstDC_lift (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (B : Finset (Fin (H.glue x y₁ y₂ (tVar true)).comps.length))
    (Bg : Finset (Fin g.comps.length)) :
    Finset (Fin (H.glue x y₁ y₂ g.swapSolid).comps.length) :=
  Finset.univ.filter fun j => (j.val < H.comps.length ∧ ∃ i ∈ B, i.val = j.val) ∨
    ∃ i ∈ Bg, H.comps.length + i.val = j.val

/-- The index of the component `i` of `g` in `H.glue x y₁ y₂ g.swapSolid`. -/
private def SubstDC_rIdx (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (i : Fin g.comps.length) : Fin (H.glue x y₁ y₂ g.swapSolid).comps.length :=
  ⟨H.comps.length + i.val, by rw [SubstDC_glue_length]; omega⟩

private theorem SubstDC_rIdx_mem (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    {B : Finset (Fin (H.glue x y₁ y₂ (tVar true)).comps.length)}
    {Bg : Finset (Fin g.comps.length)} {i : Fin g.comps.length} (hi : i ∈ Bg) :
    SubstDC_rIdx H x y₁ y₂ g i ∈ SubstDC_lift H x y₁ y₂ g B Bg :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨i, hi, rfl⟩⟩

private theorem SubstDC_rIdx_getElem (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (i : Fin g.comps.length) :
    (H.glue x y₁ y₂ g.swapSolid).comps[SubstDC_rIdx H x y₁ y₂ g i] =
      Comp.map (glueAtom x y₁ y₂) g.comps[i].swapSolid :=
  SubstDC_glue_getElem_right H x y₁ y₂ g i _

/-- A component of `H.glue x y₁ y₂ g.swapSolid` with index in `SubstDC_lift` is a component of
`H` with index in `B` or a component of `g` with index in `Bg`. -/
private theorem SubstDC_lift_cases (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    {B : Finset (Fin (H.glue x y₁ y₂ (tVar true)).comps.length)}
    {Bg : Finset (Fin g.comps.length)} {j : Fin (H.glue x y₁ y₂ g.swapSolid).comps.length}
    (hj : j ∈ SubstDC_lift H x y₁ y₂ g B Bg) :
    (∃ i ∈ B, ∃ hi : i.val < H.comps.length,
      (H.glue x y₁ y₂ (tVar true)).comps[i] = Comp.map (liftA 1) H.comps[i.val] ∧
      (H.glue x y₁ y₂ g.swapSolid).comps[j] = Comp.map (liftA n') H.comps[i.val]) ∨
    ∃ i ∈ Bg, j = SubstDC_rIdx H x y₁ y₂ g i := by
  rcases (Finset.mem_filter.1 hj).2 with ⟨hjl, i, hi, hij⟩ | ⟨i, hi, hij⟩
  · refine Or.inl ⟨i, hi, hij ▸ hjl, ?_, ?_⟩
    · exact SubstDC_glue_getElem_left H x y₁ y₂ _ i.val (hij ▸ hjl) _
    · simp only [Fin.getElem_fin, ← hij]
      exact SubstDC_glue_getElem_left H x y₁ y₂ _ i.val (hij ▸ hjl) _
  · exact Or.inr ⟨i, hi, Fin.ext hij.symm⟩

/-- The kinds of the components of `SubstDC_lift`. -/
private theorem SubstDC_lift_kind (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    {B : Finset (Fin (H.glue x y₁ y₂ (tVar true)).comps.length)}
    {Bg : Finset (Fin g.comps.length)} (P : Kind → Prop)
    (hB : ∀ i ∈ B, P (H.glue x y₁ y₂ (tVar true)).comps[i].kind)
    (hBg : ∀ i ∈ Bg, P g.comps[i].kind) :
    ∀ j ∈ SubstDC_lift H x y₁ y₂ g B Bg, P (H.glue x y₁ y₂ g.swapSolid).comps[j].kind := by
  intro j hj
  rcases SubstDC_lift_cases H x y₁ y₂ g hj with ⟨i, hi, hil, h1, h2⟩ | ⟨i, hi, rfl⟩
  · have := hB i hi
    rw [h1] at this
    rw [h2]
    exact this
  · rw [SubstDC_rIdx_getElem]
    have := hBg i hi
    unfold Comp.swapSolid
    split_ifs <;> exact this

/-- Disjoint sets give disjoint sets `SubstDC_lift`. -/
private theorem SubstDC_lift_disjoint (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    {B B' : Finset (Fin (H.glue x y₁ y₂ (tVar true)).comps.length)}
    {Bg Bg' : Finset (Fin g.comps.length)} (h : Disjoint B B') (hg : Disjoint Bg Bg') :
    Disjoint (SubstDC_lift H x y₁ y₂ g B Bg) (SubstDC_lift H x y₁ y₂ g B' Bg') := by
  rw [Finset.disjoint_left]
  intro j h1 h2
  rcases (Finset.mem_filter.1 h1).2 with ⟨hjl, i, hi, hij⟩ | ⟨i, hi, hij⟩ <;>
    rcases (Finset.mem_filter.1 h2).2 with ⟨hjl', i', hi', hij'⟩ | ⟨i', hi', hij'⟩
  · have e : i = i' := Fin.ext (hij.trans hij'.symm)
    subst e
    exact Finset.disjoint_left.1 h hi hi'
  · omega
  · omega
  · have e : i = i' := Fin.ext (by omega)
    subst e
    exact Finset.disjoint_left.1 hg hi hi'

/-- The molecules of `H.glue x y₁ y₂ (tVar true)` go to molecules of `H.glue x y₁ y₂ g.swapSolid`
under `SubstDC_fA` (the waved edge `s_{αx}` goes to one atom). -/
private theorem SubstDC_sameMol_host (H : Graph 3 m) (x₀ : Fin m) (y₁ y₂ : Atom 3 m)
    (g : Graph 3 n') {u v : Atom 3 (m + 1)} (h : (H.glue (.inr x₀) y₁ y₂ (tVar true)).SameMol u v) :
    (H.glue (.inr x₀) y₁ y₂ g.swapSolid).SameMol (SubstDC_fA x₀ u) (SubstDC_fA x₀ v) := by
  refine SubstDC_sameMol_map _ (fun c hc hj => ?_) (fun u hu => ?_) h
  · rw [SubstDC_host_comps] at hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      refine Or.inr ⟨Comp.map (liftA n') c₀, List.mem_append_left _ (List.mem_map_of_mem hc₀),
        hj, ?_, ?_⟩
      · simp [Comp.map, SubstDC_fA_liftA]
      · simp [Comp.map, SubstDC_fA_liftA]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [Kind.joinsMol] at hj
      left
      simp only [SubstDC_fA_newA, SubstDC_fA_liftA]
  · rcases u with a | a
    · exact absurd hu (by simp)
    · rfl

/-- The molecules of `g` go to molecules of `H.glue x y₁ y₂ g.swapSolid`. -/
private theorem SubstDC_sameMol_g (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    {u v : Atom 3 n'} (h : g.SameMol u v) :
    (H.glue x y₁ y₂ g.swapSolid).SameMol (glueAtom x y₁ y₂ u) (glueAtom x y₁ y₂ v) := by
  refine SubstDC_sameMol_map _ (fun c hc hj => ?_) (fun u hu => ?_) h
  · have hs : c.swapSolid = c := by
      unfold Comp.swapSolid
      have : c.kind.isSolid = false := by
        rcases c with ⟨K, _, _, _, _⟩
        cases K <;> simp_all [Kind.joinsMol, Kind.isSolid]
      simp [this]
    refine Or.inr ⟨Comp.map (glueAtom x y₁ y₂) c, ?_, hj, rfl, rfl⟩
    refine List.mem_append_right _ ?_
    simp only [Graph.swapSolid, List.map_map]
    exact List.mem_map.2 ⟨c, hc, by simp [hs]⟩
  · rcases u with a | a
    · exact absurd hu (by simp)
    · rfl

/-- Net paths of `H.glue x y₁ y₂ (tVar true)` through components of `H` go to net paths of
`H.glue x y₁ y₂ g.swapSolid`. -/
private theorem SubstDC_reach_host (H : Graph 3 m) (x₀ : Fin m) (y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    {B : Finset (Fin (H.glue (.inr x₀) y₁ y₂ (tVar true)).comps.length)}
    (Bg : Finset (Fin g.comps.length)) (hB : ∀ i ∈ B, i.val < H.comps.length) {a b : Fin (m + 1)}
    (h : ((H.glue (.inr x₀) y₁ y₂ (tVar true)).net B).Reachable a b) :
    ((H.glue (.inr x₀) y₁ y₂ g.swapSolid).net (SubstDC_lift H (.inr x₀) y₁ y₂ g B Bg)).Reachable
      (SubstDC_fN x₀ a) (SubstDC_fN x₀ b) := by
  refine SubstDC_net_reach_map _ (fun a b hm => SubstDC_sameMol_host H x₀ y₁ y₂ g hm)
    (fun i hi a b h1 h2 => ?_) h
  have hil := hB i hi
  have hj : i.val < (H.glue (.inr x₀) y₁ y₂ g.swapSolid).comps.length := by
    rw [SubstDC_glue_length]; omega
  refine ⟨⟨i.val, hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl ⟨hil, i, hi, rfl⟩⟩,
    Or.inl ?_⟩
  have e1 := SubstDC_glue_getElem_left H (.inr x₀) y₁ y₂ (tVar true) i.val hil i.2
  have e2 := SubstDC_glue_getElem_left H (.inr x₀) y₁ y₂ g.swapSolid i.val hil hj
  simp only [Fin.getElem_fin] at h1 h2 e1 ⊢
  rw [e1] at h1 h2
  rw [e2]
  simp only [Comp.map] at h1 h2 ⊢
  rw [← SubstDC_fA_liftA x₀, h1, ← SubstDC_fA_liftA x₀, h2]
  exact ⟨rfl, rfl⟩

/-- Net paths of `g` go to net paths of `H.glue x y₁ y₂ g.swapSolid`. -/
private theorem SubstDC_reach_g (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (B : Finset (Fin (H.glue x y₁ y₂ (tVar true)).comps.length))
    {Bg : Finset (Fin g.comps.length)} {a b : Fin n'} (h : (g.net Bg).Reachable a b) :
    ((H.glue x y₁ y₂ g.swapSolid).net (SubstDC_lift H x y₁ y₂ g B Bg)).Reachable
      (Fin.natAdd m a) (Fin.natAdd m b) := by
  refine SubstDC_net_reach_map (Fin.natAdd m) (fun a b hm => SubstDC_sameMol_g H x y₁ y₂ g hm)
    (fun i hi a b h1 h2 => ⟨_, SubstDC_rIdx_mem H x y₁ y₂ g hi, ?_⟩) h
  rw [SubstDC_rIdx_getElem]
  simp only [Fin.getElem_fin] at h1 h2 ⊢
  unfold Comp.swapSolid
  split_ifs
  · exact Or.inr ⟨by simp [Comp.map, h2, glueAtom, newA], by simp [Comp.map, h1, glueAtom, newA]⟩
  · exact Or.inl ⟨by simp [Comp.map, h1, glueAtom, newA], by simp [Comp.map, h2, glueAtom, newA]⟩

/-- Every internal atom of `H.glue x y₁ y₂ g.swapSolid` is joined to `x` in the net of
`SubstDC_lift B Bg` if `B` spans the host through components of `H` and every internal atom of
`g` is joined to an atom of `H`. -/
private theorem SubstDC_spans_final (H : Graph 3 m) (x₀ : Fin m) (y₁ y₂ : Atom 3 m)
    (g : Graph 3 n') {B : Finset (Fin (H.glue (.inr x₀) y₁ y₂ (tVar true)).comps.length)}
    {Bg : Finset (Fin g.comps.length)} (hB : ∀ i ∈ B, i.val < H.comps.length)
    (hs : (H.glue (.inr x₀) y₁ y₂ (tVar true)).Spans B)
    (hlink : ∀ j : Fin n', ∃ h : Fin m, ((H.glue (.inr x₀) y₁ y₂ g.swapSolid).net
      (SubstDC_lift H (.inr x₀) y₁ y₂ g B Bg)).Reachable (Fin.natAdd m j) (Fin.castAdd n' h)) :
    (H.glue (.inr x₀) y₁ y₂ g.swapSolid).Spans (SubstDC_lift H (.inr x₀) y₁ y₂ g B Bg) := by
  have e : ∀ b : Fin m, SubstDC_fN (n' := n') x₀ (Fin.castAdd 1 b) = Fin.castAdd n' b := by
    intro b
    simp only [SubstDC_fN, Fin.val_castAdd, b.2, dite_true]
    rfl
  have hH : ∀ a : Fin m, ((H.glue (.inr x₀) y₁ y₂ g.swapSolid).net
      (SubstDC_lift H (.inr x₀) y₁ y₂ g B Bg)).Reachable (Fin.castAdd n' x₀)
        (Fin.castAdd n' a) := by
    intro a
    have := SubstDC_reach_host H x₀ y₁ y₂ g Bg hB (hs (Fin.castAdd 1 x₀) (Fin.castAdd 1 a))
    rwa [e, e] at this
  have hall : ∀ p, ((H.glue (.inr x₀) y₁ y₂ g.swapSolid).net
      (SubstDC_lift H (.inr x₀) y₁ y₂ g B Bg)).Reachable (Fin.castAdd n' x₀) p := by
    intro p
    induction p using Fin.addCases with
    | left a => exact hH a
    | right j =>
      obtain ⟨h, hr⟩ := hlink j
      exact (hH h).trans hr.symm
  intro p q
  exact (hall p).symm.trans (hall q)

/-- The doubly connected property of `H.glue x y₁ y₂ g.swapSolid` from nets of the host without
the blue solid edge `G_{y₁α}` and nets of `g` each of whose internal atoms is joined to an atom of
`H` (no internal atom in `g`, or one internal atom of `g` joined to an atom of `H`). -/
private theorem SubstDC_core (H : Graph 3 m) (x₀ : Fin m) (y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (hd : (H.glue (.inr x₀) y₁ y₂ (tVar true)).DotFree)
    (hs : spdPM' (H.glue (.inr x₀) y₁ y₂ (tVar true)))
    (hst : ∀ i : Fin (H.glue (.inr x₀) y₁ y₂ (tVar true)).comps.length,
      i.val = H.comps.length + 1 → (H.glue (.inr x₀) y₁ y₂ (tVar true)).Step2EdgeB i)
    (gk gu : Finset (Fin g.comps.length)) (hgd : Disjoint gk gu)
    (hgk : ∀ i ∈ gk, g.comps[i].kind.isDiffusive = true)
    (hgu : ∀ i ∈ gu, g.comps[i].kind.isDiffusive = true ∨ g.comps[i].kind.isBlue = true)
    (hsk : g.Spans gk) (hsu : g.Spans gu)
    (hlk : n' = 0 ∨ ∀ B, ∃ j : Fin n', ∃ h : Fin m, ((H.glue (.inr x₀) y₁ y₂ g.swapSolid).net
      (SubstDC_lift H (.inr x₀) y₁ y₂ g B gk)).Reachable (Fin.natAdd m j) (Fin.castAdd n' h))
    (hlu : n' = 0 ∨ ∀ B, ∃ j : Fin n', ∃ h : Fin m, ((H.glue (.inr x₀) y₁ y₂ g.swapSolid).net
      (SubstDC_lift H (.inr x₀) y₁ y₂ g B gu)).Reachable (Fin.natAdd m j) (Fin.castAdd n' h)) :
    (H.glue (.inr x₀) y₁ y₂ g.swapSolid).DoublyConnected := by
  have hb : H.comps.length + 1 < (H.glue (.inr x₀) y₁ y₂ (tVar true)).comps.length := by
    rw [SubstDC_host_length]; omega
  obtain ⟨Bk, Bu, hdj, hbk, hbu, hkk, hku, hsk', hsu'⟩ :=
    SubstDC_atom_nets hd hs (hst ⟨_, hb⟩ rfl)
  have hlt : ∀ B : Finset (Fin (H.glue (.inr x₀) y₁ y₂ (tVar true)).comps.length),
      (⟨_, hb⟩ : Fin _) ∉ B →
      (∀ i ∈ B, (H.glue (.inr x₀) y₁ y₂ (tVar true)).comps[i].kind.isDiffusive = true ∨
        (H.glue (.inr x₀) y₁ y₂ (tVar true)).comps[i].kind.isBlue = true) →
      ∀ i ∈ B, i.val < H.comps.length := by
    intro B hnb hk i hi
    rcases SubstDC_host_idx H _ y₁ y₂ i (hk i hi) with h | h
    · exact h
    · have e : i = ⟨_, hb⟩ := Fin.ext h
      exact absurd (e ▸ hi) hnb
  have hBk := hlt Bk hbk (fun i hi => Or.inl (hkk i hi))
  have hBu := hlt Bu hbu hku
  have hfull : ∀ (B : Finset (Fin (H.glue (.inr x₀) y₁ y₂ (tVar true)).comps.length))
      (Bg : Finset (Fin g.comps.length)), g.Spans Bg →
      (n' = 0 ∨ ∀ B, ∃ j : Fin n', ∃ h : Fin m, ((H.glue (.inr x₀) y₁ y₂ g.swapSolid).net
        (SubstDC_lift H (.inr x₀) y₁ y₂ g B Bg)).Reachable (Fin.natAdd m j) (Fin.castAdd n' h)) →
      ∀ j : Fin n', ∃ h : Fin m, ((H.glue (.inr x₀) y₁ y₂ g.swapSolid).net
        (SubstDC_lift H (.inr x₀) y₁ y₂ g B Bg)).Reachable (Fin.natAdd m j) (Fin.castAdd n' h) := by
    intro B Bg hsg hl j
    rcases hl with h0 | hl
    · subst h0
      exact j.elim0
    · obtain ⟨j₀, h, hr⟩ := hl B
      exact ⟨h, (SubstDC_reach_g H _ y₁ y₂ g B (hsg j j₀)).trans hr⟩
  refine ⟨SubstDC_lift H _ y₁ y₂ g Bk gk, SubstDC_lift H _ y₁ y₂ g Bu gu,
    SubstDC_lift_disjoint H _ y₁ y₂ g hdj hgd,
    SubstDC_lift_kind H _ y₁ y₂ g (fun K => K.isDiffusive = true) hkk hgk,
    SubstDC_lift_kind H _ y₁ y₂ g (fun K => K.isDiffusive = true ∨ K.isBlue = true) hku hgu,
    SubstDC_spans_final H x₀ y₁ y₂ g hBk hsk' (hfull Bk gk hsk hlk),
    SubstDC_spans_final H x₀ y₁ y₂ g hBu hsu' (hfull Bu gu hsu hlu)⟩

/-- An external atom of `g` in the block of an internal atom of `g` joins that internal atom to
an atom of `H` in every net of `H.glue x y₁ y₂ g.swapSolid` (the dotted path becomes a path of
dotted edges between internal atoms). -/
private theorem SubstDC_link_pinned (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (hint : ∀ e : Fin 3, ∃ h : Fin m, ![x, y₁, y₂] e = .inr h) {e : Fin 3} {j : Fin n'}
    (hb : g.SameBlock (.inl e) (.inr j))
    (B : Finset (Fin (H.glue x y₁ y₂ g.swapSolid).comps.length)) :
    ∃ h : Fin m, ((H.glue x y₁ y₂ g.swapSolid).net B).Reachable (Fin.natAdd m j)
      (Fin.castAdd n' h) := by
  obtain ⟨h, hh⟩ := hint e
  refine ⟨h, SubstDC_net_reach_of_sameMol B (Or.inr ⟨rfl, rfl, ?_⟩)⟩
  have hr := SubstDC_reach_map (glueAtom x y₁ y₂) (B := (H.glue x y₁ y₂ g.swapSolid).molGraph)
    (fun u v huv => ?_) hb
  · have e1 : glueAtom x y₁ y₂ (.inl e : Atom 3 n') = .inr (Fin.castAdd n' h) := by
      simp [glueAtom, hh, liftA]
    have e2 : glueAtom x y₁ y₂ (.inr j : Atom 3 n') = .inr (Fin.natAdd m j) := rfl
    rw [e1, e2] at hr
    exact hr.symm
  · by_cases he : glueAtom x y₁ y₂ u = glueAtom x y₁ y₂ v
    · exact Or.inl he
    · right
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at huv
      rw [Graph.molGraph, SimpleGraph.fromRel_adj]
      have hm : ∀ c ∈ g.comps, c.kind = .dot →
          Comp.map (glueAtom x y₁ y₂) c ∈ (H.glue x y₁ y₂ g.swapSolid).comps := by
        intro c hc hk
        refine List.mem_append_right _ ?_
        simp only [Graph.swapSolid, List.map_map]
        refine List.mem_map.2 ⟨c, hc, ?_⟩
        simp [Comp.swapSolid, hk, Kind.isSolid]
      obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := huv
      · exact ⟨he, Or.inl ⟨_, hm c hc hk, by simp [hk, Comp.map, Kind.joinsMol], rfl, rfl⟩⟩
      · exact ⟨he, Or.inr ⟨_, hm c hc hk, by simp [hk, Comp.map, Kind.joinsMol], rfl, rfl⟩⟩

/-- A component of `g` with index in `Bg` between an external atom and an internal atom of `g`
joins that internal atom to an atom of `H` in the net of `SubstDC_lift B Bg`. -/
private theorem SubstDC_link_edge (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (hint : ∀ e : Fin 3, ∃ h : Fin m, ![x, y₁, y₂] e = .inr h)
    (B : Finset (Fin (H.glue x y₁ y₂ (tVar true)).comps.length))
    {Bg : Finset (Fin g.comps.length)} {i : Fin g.comps.length} (hi : i ∈ Bg) {e : Fin 3}
    {j : Fin n'} (hc : (g.comps[i].x = .inl e ∧ g.comps[i].y = .inr j) ∨
      (g.comps[i].x = .inr j ∧ g.comps[i].y = .inl e)) :
    ∃ h : Fin m, ((H.glue x y₁ y₂ g.swapSolid).net (SubstDC_lift H x y₁ y₂ g B Bg)).Reachable
      (Fin.natAdd m j) (Fin.castAdd n' h) := by
  obtain ⟨h, hh⟩ := hint e
  refine ⟨h, SimpleGraph.Adj.reachable (SubstDC_net_adj_of_edge ?_ _
    (SubstDC_rIdx_mem H x y₁ y₂ g hi) ?_)⟩
  · intro he
    have := congrArg Fin.val he
    simp at this
    omega
  · rw [SubstDC_rIdx_getElem]
    have e1 : glueAtom x y₁ y₂ (.inl e : Atom 3 n') = .inr (Fin.castAdd n' h) := by
      simp [glueAtom, hh, liftA]
    have e2 : glueAtom x y₁ y₂ (.inr j : Atom 3 n') = .inr (Fin.natAdd m j) := rfl
    unfold Comp.swapSolid
    split_ifs <;> rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Comp.map, h1, h2, e1, e2, and_self, true_or, or_true]

end Glue

/-! ## [II, Lemma 5.7] in the block reading -/

section Main

/-- An index of a component of a list. -/
private theorem SubstDC_idx_of_mem {α : Type} {l : List α} {c : α} (h : c ∈ l) :
    ∃ i : Fin l.length, l[i] = c := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨⟨i, hi⟩, rfl⟩

/-- A net restricted to its components between two internal atoms spans the same atoms. -/
private theorem SubstDC_spans_restrict {k n : ℕ} {Γ : Graph k n} {B : Finset (Fin Γ.comps.length)}
    (hs : Γ.Spans B) :
    Γ.Spans (B.filter fun i => Γ.comps[i].x.isRight = true ∧ Γ.comps[i].y.isRight = true) := by
  intro a b
  refine (hs a b).mono fun u v h => ?_
  rw [Graph.net, SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨hne, (hm | ⟨i, hi, h1, h2⟩) | (hm | ⟨i, hi, h1, h2⟩)⟩ := h
  · exact ⟨hne, Or.inl (Or.inl hm)⟩
  · exact ⟨hne, Or.inl (Or.inr ⟨i, Finset.mem_filter.2 ⟨hi, by rw [h1]; rfl, by rw [h2]; rfl⟩,
      h1, h2⟩)⟩
  · exact ⟨hne, Or.inr (Or.inl hm)⟩
  · exact ⟨hne, Or.inr (Or.inr ⟨i, Finset.mem_filter.2 ⟨hi, by rw [h1]; rfl, by rw [h2]; rfl⟩,
      h1, h2⟩)⟩

/-- A larger set of components spans. -/
private theorem SubstDC_spans_mono {k n : ℕ} {Γ : Graph k n} {B B' : Finset (Fin Γ.comps.length)}
    (hBB : B ⊆ B') (hs : Γ.Spans B) : Γ.Spans B' := by
  intro a b
  refine (hs a b).mono fun u v h => ?_
  rw [Graph.net, SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨hne, (hm | ⟨i, hi, h1, h2⟩) | (hm | ⟨i, hi, h1, h2⟩)⟩ := h
  · exact ⟨hne, Or.inl (Or.inl hm)⟩
  · exact ⟨hne, Or.inl (Or.inr ⟨i, hBB hi, h1, h2⟩)⟩
  · exact ⟨hne, Or.inr (Or.inl hm)⟩
  · exact ⟨hne, Or.inr (Or.inr ⟨i, hBB hi, h1, h2⟩)⟩

/-- An atom that is not unpinned, in a graph whose external atoms are in blocks without internal
atoms, is internal. -/
private theorem SubstDC_int_of_not_unpinned {n' : ℕ} {g : Graph 3 n'}
    (hP : ¬ ∃ (e : Fin 3) (j : Fin n'), g.SameBlock (.inl e) (.inr j)) {u : Atom 3 n'}
    (h : ¬ g.Unpinned u) : ∃ j, u = .inr j := by
  rcases u with e | j
  · exact absurd ⟨rfl, fun b hb => hP ⟨e, b, hb⟩⟩ h
  · exact ⟨j, rfl⟩

/-- A `⊕`-recollision graph at `𝔟₁ = 𝔟₂` has an external atom in the block of an internal
atom. -/
private theorem SubstDC_pinned_of_diagRecoll {n' : ℕ} {g : Graph 3 n'} (h : g.DiagRecoll) :
    ∃ (e : Fin 3) (j : Fin n'), g.SameBlock (.inl e) (.inr j) := by
  unfold Graph.DiagRecoll at h
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h
  obtain ⟨B, hB, h12, u, hu, hr⟩ := h
  rcases u with a | j
  · exact absurd hr (by simp)
  · rcases h12 with h1 | h2
    · exact ⟨1, j, (Graph.sameBlock_iff_mem_dotBlocks g _ _).2 ⟨B, hB, h1, hu⟩⟩
    · exact ⟨2, j, (Graph.sameBlock_iff_mem_dotBlocks g _ _).2 ⟨B, hB, h2, hu⟩⟩

/-- **[II, Lemma 5.7] in the block reading** (the doubly connected property of a substituted
graph): let `G = H.glue x y₁ y₂ (tVar true)` be a graph without dotted edges, sequentially
pre-deterministic in the block reading (`spdPM'`), with the blue solid edge `G_{y₁α}` chosen by
Step 2 of [II, Strategy 6.6] (`Graph.Step2EdgeB'`). Then `H` with a doubly connected graph `g`
substituted at `x, y₁, y₂` (the atoms of the solid edges of `g` exchanged) is doubly connected,
if `g` has no internal atom, is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` (`Graph.DiagRecoll`), or is
rooted at the external atoms (`Graph.RootedAtExt`). -/
theorem substDCB :
  ∀ (m n' : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n'),
    (H.glue x y₁ y₂ (tVar true)).DotFree → spdPM' (H.glue x y₁ y₂ (tVar true)) →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    g.DoublyConnected → (n' = 0 ∨ g.DiagRecoll ∨ g.RootedAtExt) →
    (H.glue x y₁ y₂ g.swapSolid).DoublyConnected := by
  intro m n' H x y₁ y₂ g h1 h2 h3 h4 h5
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ h3
  rcases x with x | x₀
  · exact absurd hx (by simp)
  obtain ⟨y₁₀, rfl⟩ : ∃ a, y₁ = .inr a := by
    rcases y₁ with a | a
    · exact absurd hy₁ (by simp)
    · exact ⟨a, rfl⟩
  obtain ⟨y₂₀, rfl⟩ : ∃ a, y₂ = .inr a := by
    rcases y₂ with a | a
    · exact absurd hy₂ (by simp)
    · exact ⟨a, rfl⟩
  have hint : ∀ e : Fin 3, ∃ h : Fin m, ![(.inr x₀ : Atom 3 m), .inr y₁₀, .inr y₂₀] e = .inr h := by
    intro e
    fin_cases e
    exacts [⟨x₀, rfl⟩, ⟨y₁₀, rfl⟩, ⟨y₂₀, rfl⟩]
  have hst := fun i hi => (h3 i hi).1
  obtain ⟨gk, gu, hgd, hgk, hgu, hsk, hsu⟩ := h4
  by_cases hP : ∃ (e : Fin 3) (j : Fin n'), g.SameBlock (.inl e) (.inr j)
  · obtain ⟨e, j, hb⟩ := hP
    refine SubstDC_core H x₀ _ _ g h1 h2 hst gk gu hgd hgk hgu hsk hsu
      (Or.inr fun B => ⟨j, SubstDC_link_pinned H _ _ _ g hint hb _⟩)
      (Or.inr fun B => ⟨j, SubstDC_link_pinned H _ _ _ g hint hb _⟩)
  rcases h5 with h0 | hD | hR
  · exact SubstDC_core H x₀ _ _ g h1 h2 hst gk gu hgd hgk hgu hsk hsu (Or.inl h0) (Or.inl h0)
  · exact absurd (SubstDC_pinned_of_diagRecoll hD) hP
  -- the diffusive edge at `⊗` and the blue solid or diffusive edge at `⊕`
  obtain ⟨⟨⟨c₀, hc₀, hk₀, hc₀'⟩, -⟩, hplus, -⟩ := hR
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n', (c₀.x = .inl 0 ∧ c₀.y = .inr j₀) ∨
      (c₀.x = .inr j₀ ∧ c₀.y = .inl 0) := by
    rcases hc₀' with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · obtain ⟨j, hj⟩ := SubstDC_int_of_not_unpinned hP hy
      exact ⟨j, Or.inl ⟨hx, hj⟩⟩
    · obtain ⟨j, hj⟩ := SubstDC_int_of_not_unpinned hP hx
      exact ⟨j, Or.inr ⟨hj, hy⟩⟩
  obtain ⟨c₁, hc₁, hk₁, j₁, hj₁⟩ : ∃ c₁ ∈ g.comps,
      (c₁.kind.isDiffusive = true ∨ c₁.kind.isBlue = true) ∧ ∃ j₁ : Fin n',
        (c₁.x = .inl 1 ∧ c₁.y = .inr j₁) ∨ (c₁.x = .inr j₁ ∧ c₁.y = .inl 1) := by
    rcases hplus with ⟨c, hc, hk, hxy⟩ | ⟨c, hc, hk, hxy⟩
    · refine ⟨c, hc, Or.inr (by rw [hk]; rfl), ?_⟩
      rcases hxy with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · rcases hcy : c.y with a | j
        · rw [hcy] at hy; exact absurd hy (by simp)
        · exact ⟨j, Or.inl ⟨hx, rfl⟩⟩
      · rcases hcx : c.x with a | j
        · rw [hcx] at hx; exact absurd hx (by simp)
        · exact ⟨j, Or.inr ⟨rfl, hy⟩⟩
    · refine ⟨c, hc, Or.inl hk, ?_⟩
      rcases hxy with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · obtain ⟨j, hj⟩ := SubstDC_int_of_not_unpinned hP hy
        exact ⟨j, Or.inl ⟨hx, hj⟩⟩
      · obtain ⟨j, hj⟩ := SubstDC_int_of_not_unpinned hP hx
        exact ⟨j, Or.inr ⟨hj, hy⟩⟩
  obtain ⟨i₀, rfl⟩ := SubstDC_idx_of_mem hc₀
  obtain ⟨i₁, rfl⟩ := SubstDC_idx_of_mem hc₁
  have hne : i₀ ≠ i₁ := by
    rintro rfl
    rcases hj₀ with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hj₁ with ⟨c, d⟩ | ⟨c, d⟩ <;>
      simp_all
  set gk' := gk.filter fun i => g.comps[i].x.isRight = true ∧ g.comps[i].y.isRight = true
  set gu' := gu.filter fun i => g.comps[i].x.isRight = true ∧ g.comps[i].y.isRight = true
  have hext : ∀ (i : Fin g.comps.length) (e : Fin 3) (j : Fin n'),
      ((g.comps[i].x = .inl e ∧ g.comps[i].y = .inr j) ∨
        (g.comps[i].x = .inr j ∧ g.comps[i].y = .inl e)) →
      ¬ (g.comps[i].x.isRight = true ∧ g.comps[i].y.isRight = true) := by
    intro i e j h hr
    rcases h with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a] at hr; exact absurd hr.1 (by simp)
    · rw [b] at hr; exact absurd hr.2 (by simp)
  refine SubstDC_core H x₀ _ _ g h1 h2 hst (insert i₀ gk') (insert i₁ gu') ?_ ?_ ?_
    (SubstDC_spans_mono (Finset.subset_insert _ _) (SubstDC_spans_restrict hsk))
    (SubstDC_spans_mono (Finset.subset_insert _ _) (SubstDC_spans_restrict hsu))
    (Or.inr fun B => ⟨j₀, SubstDC_link_edge H _ _ _ g hint B (Finset.mem_insert_self _ _) hj₀⟩)
    (Or.inr fun B => ⟨j₁, SubstDC_link_edge H _ _ _ g hint B (Finset.mem_insert_self _ _) hj₁⟩)
  · rw [Finset.disjoint_left]
    intro i ha hb
    rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with e | hb
    · exact hne e
    · exact hext _ _ _ hj₀ (Finset.mem_filter.1 hb).2
    · subst e
      exact hext _ _ _ hj₁ (Finset.mem_filter.1 ha).2
    · exact Finset.disjoint_left.1 hgd (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1
  · intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hk₀
    · exact hgk i (Finset.mem_filter.1 hi).1
  · intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hk₁
    · exact hgu i (Finset.mem_filter.1 hi).1

end Main

/-! ## [II, Lemma 6.5 (5)] in the block reading -/

section Row5

variable {k n : ℕ}

/-- A component that is not a solid edge is kept by `Comp.swapSolid`. -/
private theorem SubstDC_swap_of_not_solid {V : Type*} {c : Comp V} (h : c.kind.isSolid = false) :
    c.swapSolid = c := by
  simp [Comp.swapSolid, h]

private theorem SubstDC_swap_kind {V : Type*} (c : Comp V) : c.swapSolid.kind = c.kind := by
  unfold Comp.swapSolid; split <;> rfl

private theorem SubstDC_swap_label {V : Type*} (c : Comp V) : c.swapSolid.label = c.label := by
  unfold Comp.swapSolid; split <;> rfl

private theorem SubstDC_not_solid {K : Kind} (h : K = .dot ∨ K.joinsMol = true ∨
    K.isDiffusive = true) : K.isSolid = false := by
  rcases h with rfl | h | h
  · rfl
  · cases K <;> simp_all [Kind.joinsMol, Kind.isSolid]
  · cases K <;> simp_all [Kind.isDiffusive, Kind.isSolid]

/-- The dotted edges of `Γ.swapSolid` are those of `Γ`. -/
private theorem SubstDC_swap_dotGraph (Γ : Graph k n) : Γ.swapSolid.dotGraph = Γ.dotGraph := by
  ext u v
  simp only [Graph.dotGraph, SimpleGraph.fromRel_adj, Graph.swapSolid, List.mem_map]
  have key : ∀ u v, (∃ c, (∃ a ∈ Γ.comps, a.swapSolid = c) ∧ c.kind = .dot ∧ c.x = u ∧ c.y = v) ↔
      ∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v := by
    intro u v
    constructor
    · rintro ⟨c, ⟨a, ha, rfl⟩, hk, hx, hy⟩
      rw [SubstDC_swap_kind] at hk
      rw [SubstDC_swap_of_not_solid (SubstDC_not_solid (Or.inl hk))] at hx hy
      exact ⟨a, ha, hk, hx, hy⟩
    · rintro ⟨c, hc, hk, hx, hy⟩
      refine ⟨c, ⟨c, hc, SubstDC_swap_of_not_solid (SubstDC_not_solid (Or.inl hk))⟩, hk, hx, hy⟩
  rw [key u v, key v u]

private theorem SubstDC_swap_dotExcess (Γ : Graph k n) :
    Γ.swapSolid.dotExcess = Γ.dotExcess := by
  have hn : Γ.swapSolid.nDots = Γ.nDots := by
    simp only [Graph.nDots, Graph.swapSolid, List.filter_map, List.length_map]
    congr 2
    funext c
    simp [SubstDC_swap_kind]
  unfold Graph.dotExcess
  rw [hn, SubstDC_swap_dotGraph]

private theorem SubstDC_swap_otimesNoDot {Γ : Graph 3 n} (h : Γ.TensorDiffusive) :
    Γ.swapSolid.OtimesNoDot := by
  intro c hc hx hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  rw [SubstDC_swap_kind] at hk
  rw [SubstDC_swap_of_not_solid (SubstDC_not_solid (Or.inl hk))] at hx
  have := List.all_eq_true.1 h a ha
  rcases hx with hx | hx <;> simp [hx, hk, Kind.isDiffusive] at this

private theorem SubstDC_swap_rgCheck {Γ : Graph 3 n} (h : Γ.RgCheck) : Γ.swapSolid.RgCheck := by
  rcases h with h | ⟨c, hc, hk, he⟩
  · exact Or.inl h
  · refine Or.inr ⟨c, List.mem_map.2 ⟨c, hc, ?_⟩, hk, he⟩
    exact SubstDC_swap_of_not_solid (SubstDC_not_solid (Or.inr hk))

private theorem SubstDC_swap_labels (Γ : Graph k n) : Γ.swapSolid.labels = Γ.labels := by
  simp only [Graph.labels, Graph.swapSolid, List.filterMap_map]
  congr 2
  funext c
  simp [SubstDC_swap_label]

private theorem SubstDC_swap_noLabDot {Γ : Graph k n} (h : Γ.NoLabDot) : Γ.swapSolid.NoLabDot := by
  intro c hc hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  rw [SubstDC_swap_kind] at hk
  rw [SubstDC_swap_label]
  exact h a ha hk

private theorem SubstDC_tVar_ord : (tVar true).ord = 2 := by
  decide +kernel

/-- **[II, Lemma 6.5 (5)] in the block reading** (the conjunct on `Err` of [II, Lemma 6.5]),
with the hypotheses on `𝒯` of [II, Def 3.2] at order `n - 1` and of [II, Def 6.3]: under the
hypotheses of [II, Lemma 6.5], every `O_dot` form `t` of the substitution of a graph of `Err` is
normal regular without dotted edges, doubly connected, of scaling order `≥ ord G + D - 3`, where
`G = H.glue x y₁ y₂ (tVar true)`. The scaling order of the `O_dot` forms of a substituted graph
(`glue_oDotT_normalStmt`) is a hypothesis. -/
theorem globalGood_row5 : glue_oDotT_normalStmt →
  ∀ (n D : ℕ) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m),
    3 ≤ n → (n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    4 ≤ (H.glue x y₁ y₂ (tVar true)).ord → (H.glue x y₁ y₂ (tVar true)).ord ≤ n →
    (H.glue x y₁ y₂ (tVar true)).InvB' → (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    gsPM' (H.glue x y₁ y₂ (tVar true)) → ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
    (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    (∀ g ∈ 𝒯.Err, ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ t.g.DoublyConnected ∧
        (H.glue x y₁ y₂ (tVar true)).ord + D - 3 ≤ t.g.ord) := by
  intro hC2 n D 𝒯 m C H x y₁ y₂ _ ⟨_, hSh, hDef⟩ hL hN hd _ _ _ _ hgs _ _ hst g hg t ht
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hall : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
  obtain ⟨⟨C', hgN⟩, -, -, hgDC⟩ := hSh.1.2 g hg
  have hord : (D : ℤ) < g.2.ord := hSh.2.2.2.2 g hg
  obtain ⟨hT, hX, hNL, hlab⟩ := hDef.2.1 g hall
  have hRg := hDef.2.2.2.2.2.1 g (by simp [hg])
  have hroot := hDef.2.2.2.2.2.2.1 g (by simp [hg])
  have h5 : g.1 = 0 ∨ g.2.DiagRecoll ∨ g.2.RootedAtExt := by
    by_cases h0 : g.1 = 0
    · exact Or.inl h0
    by_cases hD : g.2.DiagRecoll
    · exact Or.inr (Or.inl hD)
    exact Or.inr (Or.inr (hroot h0 hD))
  have hdc := substDCB m g.1 H x y₁ y₂ g.2 hd hgs.1 hst hgDC h5
  obtain ⟨hN', hd', hε, hε', hdc'⟩ := hC2 m g.1 C C' H x y₁ y₂ g.2.swapSolid hx hy₁ hy₂ hL hN hd
    (Graph.swapSolid_Normal hgN) (SubstDC_swap_otimesNoDot hT)
    (by rw [SubstDC_swap_dotExcess]; exact hX) (SubstDC_swap_rgCheck hRg)
    (by rw [SubstDC_swap_labels]; exact hlab) (SubstDC_swap_noLabDot hNL) t ht
  refine ⟨hN', hd', hdc' hdc, ?_⟩
  have e1 := glue_ord 3 m g.1 H x y₁ y₂ g.2.swapSolid
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  have e3 : g.2.swapSolid.ord = g.2.ord := (swapSolid_basic 3 g.1 g.2).2.1
  rw [SubstDC_tVar_ord] at e2
  by_cases hε0 : y₁ = y₂ ∧ g.2.swapSolid.PMBlock
  · have := hε hε0
    omega
  · have := hε' hε0
    omega

end Row5

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end Instances

end RBM8D.Graphs
