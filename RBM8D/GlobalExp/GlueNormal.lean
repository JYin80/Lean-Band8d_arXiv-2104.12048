import RBM8D.GlobalExp.Strategy
import RBM8D.Graph.DotBlocks

/-!
# The `O_dot` forms of a substituted graph

The scaling order of the `O_dot` forms ([II, Defs 4.1–4.2]) of a graph `H.glue x y₁ y₂ g`
obtained by substituting `g` for the `t`-variable of `H.glue x y₁ y₂ (tVar true)`
([II, §4.3, (4.14)], in the proof of [II, Lemma 6.5]), in the count of [II, (2.5)]:

* every solid edge of the substituted graph carries a `×`-dotted edge with the same ends and every
  `×`-dotted edge between distinct atoms carries a solid edge, so `O_dot` has no pair to split, and
  `O_merge` merges every block into one internal atom and removes every dotted edge;
* the dot excess of the substituted graph is `1` if `y₁ = y₂` and `⊕`, `⊖` lie in one block of `g`,
  and `0` otherwise (the cycle rank of the image of the dotted forest of `g`);
* the `O_dot` forms are normal regular without dotted edges and keep the doubly connected property
  ([II, Def 2.12]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Connected components of simple graphs -/

section GraphCard

variable {V W : Type*}

/-- Reachability along a map that carries every edge of a relation to a reachable pair. -/
private theorem gn_reach_map {r : V → V → Prop} {H : SimpleGraph W} (ψ : V → W)
    (h : ∀ a b, r a b → H.Reachable (ψ a) (ψ b)) {u v : V}
    (hr : (SimpleGraph.fromRel r).Reachable u v) : H.Reachable (ψ u) (ψ v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hadj ih =>
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h1 | h1
    · exact ih.trans (h _ _ h1)
    · exact ih.trans (h _ _ h1).symm

/-- Two atoms in relation are reachable in the graph of the relation. -/
private theorem gn_fromRel_reach {r : V → V → Prop} {a b : V} (h : r a b) :
    (SimpleGraph.fromRel r).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl h⟩).reachable

/-- A walk in `E` from the image of `u` under `ι` stays in the image of the atoms reachable from
`u` in `F`, until it meets an atom of `S`. -/
private theorem gn_escape {F : SimpleGraph V} {E : SimpleGraph W} (ι : V → W) (S : V → Prop)
    (hstep : ∀ z w', E.Adj (ι z) w' → (∃ z', w' = ι z' ∧ F.Reachable z z') ∨ S z)
    {u : V} {w : W} (hr : E.Reachable (ι u) w) :
    (∃ z, w = ι z ∧ F.Reachable u z) ∨ ∃ s, S s ∧ F.Reachable u s := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact Or.inl ⟨u, rfl, SimpleGraph.Reachable.refl _⟩
  | tail _ hadj ih =>
    rcases ih with ⟨z, rfl, hz⟩ | h
    · rcases hstep z _ hadj with ⟨z', rfl, hz'⟩ | hS
      · exact Or.inl ⟨z', rfl, hz.trans hz'⟩
      · exact Or.inr ⟨z, hS, hz⟩
    · exact Or.inr h

/-- Reachability in a graph with one more edge `u v`. -/
private theorem gn_reach_add_edge_iff {G H : SimpleGraph V} {u v : V}
    (hadj : ∀ a b, H.Adj a b ↔ G.Adj a b ∨ (a ≠ b ∧ (a = u ∧ b = v ∨ a = v ∧ b = u)))
    (a b : V) :
    H.Reachable a b ↔ G.Reachable a b ∨ (G.Reachable a u ∧ G.Reachable v b) ∨
      (G.Reachable a v ∧ G.Reachable u b) := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
    | @cons a a' b h _ ih =>
      rcases (hadj a a').1 h with h1 | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rcases ih with h2 | ⟨h2, h3⟩ | ⟨h2, h3⟩
        · exact Or.inl (h1.reachable.trans h2)
        · exact Or.inr (Or.inl ⟨h1.reachable.trans h2, h3⟩)
        · exact Or.inr (Or.inr ⟨h1.reachable.trans h2, h3⟩)
      · rcases ih with h2 | ⟨h2, h3⟩ | ⟨h2, h3⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h2⟩)
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h3⟩)
        · exact Or.inl h3
      · rcases ih with h2 | ⟨h2, h3⟩ | ⟨h2, h3⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h2⟩)
        · exact Or.inl h3
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h3⟩)
  · have hle : ∀ a b, G.Reachable a b → H.Reachable a b := by
      intro a b h
      obtain ⟨w⟩ := h
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons h _ ih => exact ((hadj _ _).2 (Or.inl h)).reachable.trans ih
    have huv : H.Reachable u v := by
      by_cases h : u = v
      · rw [h]
      · exact ((hadj u v).2 (Or.inr ⟨h, Or.inl ⟨rfl, rfl⟩⟩)).reachable
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hle _ _ h
    · exact ((hle _ _ h1).trans huv).trans (hle _ _ h2)
    · exact ((hle _ _ h1).trans huv.symm).trans (hle _ _ h2)

/-- Adding an edge between two connected components lowers their number by one. -/
private theorem gn_card_cc_add_edge [Finite V] {G H : SimpleGraph V} {u v : V}
    (hadj : ∀ a b, H.Adj a b ↔ G.Adj a b ∨ (a ≠ b ∧ (a = u ∧ b = v ∨ a = v ∧ b = u)))
    (huv : ¬ G.Reachable u v) :
    Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent + 1 := by
  classical
  have hR := gn_reach_add_edge_iff hadj
  have hGH : ∀ a b, G.Reachable a b → H.Reachable a b := fun a b h => (hR a b).2 (Or.inl h)
  let φ : G.ConnectedComponent → H.ConnectedComponent :=
    Quot.lift (fun a => H.connectedComponentMk a) fun a b h =>
      SimpleGraph.ConnectedComponent.sound (hGH a b h)
  have hφ : ∀ a, φ (G.connectedComponentMk a) = H.connectedComponentMk a := fun a => rfl
  let ψ : G.ConnectedComponent → Option H.ConnectedComponent := fun c =>
    if c = G.connectedComponentMk v then none else some (φ c)
  have hψ : Function.Bijective ψ := by
    constructor
    · intro c₁ c₂ h
      induction c₁ using SimpleGraph.ConnectedComponent.ind with | h a =>
      induction c₂ using SimpleGraph.ConnectedComponent.ind with | h b =>
      by_cases h1 : G.connectedComponentMk a = G.connectedComponentMk v
      · by_cases h2 : G.connectedComponentMk b = G.connectedComponentMk v
        · rw [h1, h2]
        · simp only [ψ, h1, h2, ite_true, ite_false] at h
          cases h
      · by_cases h2 : G.connectedComponentMk b = G.connectedComponentMk v
        · simp only [ψ, h1, h2, ite_true, ite_false] at h
          cases h
        · simp only [ψ, h1, h2, ite_false, Option.some.injEq, hφ,
            SimpleGraph.ConnectedComponent.eq] at h
          rw [SimpleGraph.ConnectedComponent.eq] at h1 h2 ⊢
          rcases (hR a b).1 h with h3 | ⟨-, h3⟩ | ⟨h3, -⟩
          · exact h3
          · exact absurd h3.symm h2
          · exact absurd h3 h1
    · intro o
      rcases o with _ | d
      · exact ⟨G.connectedComponentMk v, by simp [ψ]⟩
      · induction d using SimpleGraph.ConnectedComponent.ind with | h b =>
        by_cases hb : G.Reachable b v
        · refine ⟨G.connectedComponentMk u, ?_⟩
          have hne : G.connectedComponentMk u ≠ G.connectedComponentMk v := by
            rw [Ne, SimpleGraph.ConnectedComponent.eq]
            exact huv
          simp only [ψ, hne, ite_false, hφ, Option.some.injEq, SimpleGraph.ConnectedComponent.eq]
          exact ((hR u v).2 (Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _,
            SimpleGraph.Reachable.refl _⟩))).trans (hGH _ _ hb.symm)
        · refine ⟨G.connectedComponentMk b, ?_⟩
          have hne : G.connectedComponentMk b ≠ G.connectedComponentMk v := by
            rw [Ne, SimpleGraph.ConnectedComponent.eq]
            exact hb
          simp [ψ, hne, hφ]
  rw [Nat.card_congr (Equiv.ofBijective ψ hψ), Finite.card_option]

/-- Two graphs with the same reachability have the same number of connected components. -/
private theorem gn_card_cc_of_reach_iff {G H : SimpleGraph V}
    (hr : ∀ a b, H.Reachable a b ↔ G.Reachable a b) :
    Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent := by
  let φ : G.ConnectedComponent → H.ConnectedComponent :=
    Quot.lift (fun a => H.connectedComponentMk a) fun a b h =>
      SimpleGraph.ConnectedComponent.sound ((hr a b).2 h)
  have hφ : Function.Bijective φ := by
    constructor
    · intro c₁ c₂ h
      induction c₁ using SimpleGraph.ConnectedComponent.ind with | h a =>
      induction c₂ using SimpleGraph.ConnectedComponent.ind with | h b =>
      have h' : H.connectedComponentMk a = H.connectedComponentMk b := h
      rw [SimpleGraph.ConnectedComponent.eq] at h' ⊢
      exact (hr a b).1 h'
    · intro d
      induction d using SimpleGraph.ConnectedComponent.ind with | h w =>
      exact ⟨G.connectedComponentMk w, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective φ hφ)

/-- The graph without edges has one connected component per vertex. -/
private theorem gn_card_cc_bot :
    Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Nat.card V := by
  have hb : Function.Bijective (⊥ : SimpleGraph V).connectedComponentMk := by
    constructor
    · intro a b h
      rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_bot] at h
      exact h
    · intro c
      induction c using SimpleGraph.ConnectedComponent.ind with | h a =>
      exact ⟨a, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm

end GraphCard

/-! ## The dot excess of a list of components -/

section DotExcess

variable {k n : ℕ}

private theorem gn_dg_reach_mono {L L' : List (Comp (Atom k n))}
    (h : ∀ c ∈ L, c.kind = .dot → c ∈ L') {a b : Atom k n} (hr : (dg L).Reachable a b) :
    (dg L').Reachable a b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨hne, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    refine SimpleGraph.Reachable.trans ?_ ih
    exact (dg_adj.2 ⟨hne, c, h c hc hk, hk, hxy⟩).reachable

private theorem gn_dg_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ c, c.kind = .dot → (c ∈ L ↔ c ∈ L')) : dg L = dg L' := by
  ext a b
  rw [dg_adj, dg_adj]
  constructor
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).1 hc, hk, hxy⟩
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).2 hc, hk, hxy⟩

private theorem gn_eL_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : eL L = eL L' := by
  simp only [eL, nD_perm h, gn_dg_congr fun _ _ => h.mem_iff]

/-- A list without dotted components has the graph without edges. -/
private theorem gn_dg_eq_bot {L : List (Comp (Atom k n))} (h : ∀ c ∈ L, c.kind ≠ .dot) :
    dg L = ⊥ := by
  ext a b
  simp only [dg_adj, SimpleGraph.bot_adj, iff_false, not_and]
  rintro - ⟨c, hc, hk, -⟩
  exact h c hc hk

private theorem gn_card_atom : Nat.card (Atom k n) = k + n := by
  simp

/-- A list without dotted components has dot excess `0`. -/
private theorem gn_eL_of_nodot {L : List (Comp (Atom k n))} (h : ∀ c ∈ L, c.kind ≠ .dot) :
    eL L = 0 := by
  have hn : nD L = 0 := by
    unfold nD
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simpa using h c hc
  simp only [eL, hn, gn_dg_eq_bot h, gn_card_cc_bot, gn_card_atom]
  push_cast
  ring

private theorem gn_dg_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : dg (c :: L) = dg L := by
  apply gn_dg_congr
  intro d hd
  simp only [List.mem_cons]
  constructor
  · rintro (rfl | h)
    · exact absurd hd hk
    · exact h
  · exact Or.inr

private theorem gn_dg_cons_dot_adj {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (a b : Atom k n) :
    (dg (c :: L)).Adj a b ↔ (dg L).Adj a b ∨ (a ≠ b ∧ (a = c.x ∧ b = c.y ∨ a = c.y ∧ b = c.x)) := by
  rw [dg_adj, dg_adj]
  constructor
  · rintro ⟨hne, d, hd, hdk, hxy⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · right
      refine ⟨hne, ?_⟩
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    · exact Or.inl ⟨hne, d, hd, hdk, hxy⟩
  · rintro (⟨hne, d, hd, hdk, hxy⟩ | ⟨hne, hxy⟩)
    · exact ⟨hne, d, List.mem_cons_of_mem _ hd, hdk, hxy⟩
    · refine ⟨hne, c, List.mem_cons_self .., hk, ?_⟩
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩

private theorem gn_eL_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : eL (c :: L) = eL L := by
  simp [eL, nD_cons, hk, gn_dg_cons_nondot L hk]

/-- A dotted component between two blocks keeps the dot excess. -/
private theorem gn_eL_cons_dot_new {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : ¬ (dg L).Reachable c.x c.y) : eL (c :: L) = eL L := by
  have h := gn_card_cc_add_edge (G := dg L) (H := dg (c :: L)) (gn_dg_cons_dot_adj L hk) hr
  simp only [eL, nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- A dotted component whose ends are already in one block raises the dot excess by `1`. -/
private theorem gn_eL_cons_dot_red {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : (dg L).Reachable c.x c.y) : eL (c :: L) = eL L + 1 := by
  have hr' : ∀ a b, (dg (c :: L)).Reachable a b ↔ (dg L).Reachable a b := by
    intro a b
    rw [gn_reach_add_edge_iff (gn_dg_cons_dot_adj L hk)]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h
      · exact (h1.trans hr).trans h2
      · exact (h1.trans hr.symm).trans h2
    · exact Or.inl
  have h := gn_card_cc_of_reach_iff (G := dg L) (H := dg (c :: L)) hr'
  simp only [eL, nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- Components without dotted edges in front of a list keep its dot excess. -/
private theorem gn_eL_append_nodot {A : List (Comp (Atom k n))} (hA : ∀ c ∈ A, c.kind ≠ .dot)
    (B : List (Comp (Atom k n))) : eL (A ++ B) = eL B := by
  induction A with
  | nil => rfl
  | cons c A ih =>
    rw [List.cons_append, gn_eL_cons_nondot _ (hA c (List.mem_cons_self ..)),
      ih fun d hd => hA d (List.mem_cons_of_mem _ hd)]

end DotExcess

/-! ## The dot excess under a map of the atoms -/

section DotMap

variable {k n k' n' : ℕ}

/-- Reachability in the graph of dotted components of the image of `L` under `ψ`: two images are
joined exactly when the atoms are joined by the dotted components of `L` and of a list `I` of
dotted components whose ends `ψ` identifies, provided every pair of atoms with the same image is
joined by `L ++ I`. -/
private theorem gn_dg_map_reach (ψ : Atom k n → Atom k' n') (L I : List (Comp (Atom k n)))
    (hI : ∀ c ∈ I, ψ c.x = ψ c.y) (hψ : ∀ p q, ψ p = ψ q → (dg (L ++ I)).Reachable p q)
    (u v : Atom k n) :
    (dg (L.map (Comp.map ψ))).Reachable (ψ u) (ψ v) ↔ (dg (L ++ I)).Reachable u v := by
  constructor
  · intro h
    have key : ∀ w, (dg (L.map (Comp.map ψ))).Reachable (ψ u) w →
        ∃ z, ψ z = w ∧ (dg (L ++ I)).Reachable u z := by
      intro w hw
      rw [SimpleGraph.reachable_iff_reflTransGen] at hw
      induction hw with
      | refl => exact ⟨u, rfl, SimpleGraph.Reachable.refl _⟩
      | tail _ hadj ih =>
        obtain ⟨z, rfl, hz⟩ := ih
        obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hadj
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
        have he' : e ∈ L ++ I := List.mem_append_left _ he
        have hek : e.kind = .dot := hk
        have hr := dg_reach_of_mem he' hek
        rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨e.y, h2, hz.trans ?_⟩
          exact (hψ _ _ h1).symm.trans hr
        · refine ⟨e.x, h1, hz.trans ?_⟩
          exact (hψ _ _ h2).symm.trans hr.symm
    obtain ⟨z, hz, hr⟩ := key _ h
    exact hr.trans (hψ _ _ hz)
  · intro h
    have hdg : dg (L ++ I) = SimpleGraph.fromRel fun u v =>
        ∃ c ∈ L ++ I, c.kind = .dot ∧ c.x = u ∧ c.y = v := rfl
    rw [hdg] at h
    refine gn_reach_map ψ ?_ h
    rintro a b ⟨c, hc, hk, rfl, rfl⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact dg_reach_of_mem (List.mem_map_of_mem hc) hk
    · rw [hI c hc]

/-- **The dot excess under a map of the atoms**: if every pair of atoms with the same image under
`ψ` is joined by the dotted list `I` whose ends `ψ` identifies, the dot excess of the image of `L`
plus that of `I` is the dot excess of `L ++ I`. -/
private theorem gn_eL_map (ψ : Atom k n → Atom k' n') (I : List (Comp (Atom k n)))
    (hI : ∀ c ∈ I, ψ c.x = ψ c.y) (hψ : ∀ p q, ψ p = ψ q → (dg I).Reachable p q) :
    ∀ L : List (Comp (Atom k n)), eL (L.map (Comp.map ψ)) + eL I = eL (L ++ I)
  | [] => by
    rw [List.map_nil, List.nil_append, gn_eL_of_nodot (by simp), zero_add]
  | c :: L => by
    have ih := gn_eL_map ψ I hI hψ L
    have hψ' : ∀ p q, ψ p = ψ q → (dg (L ++ I)).Reachable p q := fun p q h =>
      gn_dg_reach_mono (fun d hd _ => List.mem_append_right _ hd) (hψ p q h)
    rw [List.map_cons, List.cons_append]
    by_cases hk : c.kind = .dot
    · have hk' : (c.map ψ).kind = .dot := hk
      have hiff := gn_dg_map_reach ψ L I hI hψ' c.x c.y
      by_cases hr : (dg (L ++ I)).Reachable c.x c.y
      · rw [gn_eL_cons_dot_red _ hk hr, gn_eL_cons_dot_red _ hk' (hiff.2 hr)]
        omega
      · rw [gn_eL_cons_dot_new _ hk hr, gn_eL_cons_dot_new _ hk' (fun h => hr (hiff.1 h))]
        exact ih
    · have hk' : (c.map ψ).kind ≠ .dot := hk
      rw [gn_eL_cons_nondot _ hk, gn_eL_cons_nondot _ hk']
      exact ih

end DotMap

/-! ## Blocks and their representatives -/

section Blocks

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem gn_flatten_map_singleton (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private theorem gn_joinBlocks_flatten_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

private theorem gn_foldl_flatten_perm (cs : List (Comp V)) (P : List (List V)) :
    (cs.foldl (fun P c => if c.kind = .dot then joinBlocks P c.x c.y else P) P).flatten.Perm
      P.flatten := by
  induction cs generalizing P with
  | nil => exact List.Perm.refl _
  | cons c cs ih =>
    rw [List.foldl_cons]
    refine (ih _).trans ?_
    split_ifs
    · exact gn_joinBlocks_flatten_perm _ _ _
    · exact List.Perm.refl _

/-- The blocks of `dotBlocks` partition the atoms. -/
private theorem gn_dotBlocks_flatten_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  have h := gn_foldl_flatten_perm cs (as.map fun a => [a])
  rw [gn_flatten_map_singleton] at h
  exact h

/-- Two atoms of one block of a partition have the same representative. -/
private theorem gn_blockRep_eq_of_mem {P : List (List V)} (hnd : P.flatten.Nodup) {B : List V}
    (hB : B ∈ P) {u v : V} (hu : u ∈ B) (hv : v ∈ B) : blockRep P u = blockRep P v := by
  have hfind : ∀ w ∈ B, P.find? (fun B' => B'.contains w) = some B := by
    intro w hw
    have hex : (P.find? (fun B' => B'.contains w)).isSome = true :=
      List.find?_isSome.2 ⟨B, hB, by simpa [List.contains_iff_mem] using hw⟩
    obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 hex
    rw [hB']
    have hB'mem := List.mem_of_find?_eq_some hB'
    have hw' : w ∈ B' := by simpa [List.contains_iff_mem] using List.find?_some hB'
    congr 1
    by_contra hne
    rw [List.nodup_flatten] at hnd
    have := hnd.2.forall (R := List.Disjoint) hB'mem hB hne
    exact this hw' hw
  unfold blockRep
  rw [hfind u hu, hfind v hv]
  cases B with
  | nil => simp at hu
  | cons r rest => rfl

end Blocks

section Rep

variable {k n : ℕ}

private theorem gn_allAtoms_nodup : (allAtoms k n).Nodup := by
  unfold allAtoms
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange k).map Sum.inl_injective,
    (List.nodup_finRange n).map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  simp at hab

/-- The ends of a dotted edge have the same representative in the blocks of `O_merge`. -/
private theorem gn_mrep_dot (Γ : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : Γ.mrep c.x = Γ.mrep c.y := by
  have hs : Γ.SameBlock c.x c.y := by
    unfold Graph.SameBlock Graph.dotGraph
    exact gn_fromRel_reach ⟨c, hc, hk, rfl, rfl⟩
  obtain ⟨B, hB, hx, hy⟩ := (Γ.sameBlock_iff_mem_dotBlocks _ _).1 hs
  have hnd : (dotBlocks (allAtoms k n) Γ.comps).flatten.Nodup :=
    (gn_dotBlocks_flatten_perm _ _).nodup_iff.2 gn_allAtoms_nodup
  exact gn_blockRep_eq_of_mem hnd hB hx hy

end Rep

/-! ## Doubly connected structures -/

section Tagged

variable {k n m : ℕ}

/-- The kinds usable in a blue net whose solid edges have charge `bc`: the solid edges of charge
`bc` and the ghost edges. -/
private def Kind.gnBlueC (bc : Charge) : Kind → Bool
  | .G c => decide (c = bc)
  | .ghost => true
  | _ => false

private theorem Kind.gnBlueC_plus (κ : Kind) : κ.gnBlueC .plus = κ.isBlue := by
  cases κ with
  | G c => cases c <;> rfl
  | _ => rfl

/-- A component with a tag. -/
private abbrev GnTC (k n : ℕ) : Type := Comp (Atom k n) × Option Bool

/-- The graph on the internal atoms whose edges join two atoms of one molecule, or the two ends of
a component of `L` with the tag `some t`. -/
private def Graph.gnNetT (Γ : Graph k n) (L : List (GnTC k n)) (t : Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => Γ.SameMol (Sum.inr a) (Sum.inr b) ∨
    ∃ p ∈ L, p.2 = some t ∧ p.1.x = Sum.inr a ∧ p.1.y = Sum.inr b

/-- The tagged list `L` is a doubly connected structure on `Γ` with blue charge `bc`: it lists the
components of `Γ`, black ones are diffusive, blue ones are diffusive or blue, and each net spans the
internal atoms. -/
private structure Graph.GnDCT (bc : Charge) (Γ : Graph k n) (L : List (GnTC k n)) : Prop where
  map_fst : L.map Prod.fst = Γ.comps
  black : ∀ p ∈ L, p.2 = some false → p.1.kind.isDiffusive = true
  blue : ∀ p ∈ L, p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.gnBlueC bc = true
  spanBlack : (Γ.gnNetT L false).Preconnected
  spanBlue : (Γ.gnNetT L true).Preconnected

/-- The graph has a doubly connected structure with blue charge `bc`. -/
private def Graph.GnDCS (bc : Charge) (Γ : Graph k n) : Prop := ∃ L, Γ.GnDCT bc L

private theorem Graph.gn_molReach_of_comp {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind.joinsMol = true) : Γ.molGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

private theorem Graph.gn_netT_reach_of_sameMol (Γ : Graph k n) (L : List (GnTC k n)) (t : Bool)
    {a b : Fin n} (h : Γ.SameMol (Sum.inr a) (Sum.inr b)) : (Γ.gnNetT L t).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl (Or.inl h)⟩ |>.reachable

private theorem Graph.gn_netT_reach_of_mem (Γ : Graph k n) (L : List (GnTC k n)) (t : Bool)
    {p : GnTC k n} (hp : p ∈ L) (ht : p.2 = some t) {a b : Fin n} (hx : p.1.x = Sum.inr a)
    (hy : p.1.y = Sum.inr b) : (Γ.gnNetT L t).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl (Or.inr ⟨p, hp, ht, hx, hy⟩)⟩ |>.reachable

/-- Reachability in the molecular graph is carried by a map of the atoms that carries every waved
and dotted component to a reachable pair. -/
private theorem gn_molReach_map {Γ : Graph k n} {Γ' : Graph k m} (f : Atom k n → Atom k m)
    (hmol : ∀ c ∈ Γ.comps, c.kind.joinsMol = true → Γ'.molGraph.Reachable (f c.x) (f c.y))
    {u v : Atom k n} (h : Γ.molGraph.Reachable u v) : Γ'.molGraph.Reachable (f u) (f v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := hadj
    · exact (hmol c hc hk).trans ih
    · exact (hmol c hc hk).symm.trans ih

private theorem gn_sameMol_map {Γ : Graph k n} {Γ' : Graph k m} (φ : Fin n → Fin m)
    (hmol : ∀ c ∈ Γ.comps, c.kind.joinsMol = true →
      Γ'.molGraph.Reachable (Sum.map id φ c.x) (Sum.map id φ c.y))
    {u v : Atom k n} (h : Γ.SameMol u v) : Γ'.SameMol (Sum.map id φ u) (Sum.map id φ v) := by
  rcases h with rfl | ⟨hu, hv, hr⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, ?_, gn_molReach_map _ hmol hr⟩
    · rcases u with a | a
      · simp at hu
      · rfl
    · rcases v with a | a
      · simp at hv
      · rfl

/-- Transport of a doubly connected structure along a map `φ` of the internal atoms: it suffices
that waved and dotted components stay joined, every tagged component of `Γ` joins the images of its
ends in the corresponding net of `Γ'`, and every internal atom of `Γ'` lies in the molecule of the
image of an atom of `Γ`. -/
private theorem Graph.GnDCT.transport {bc : Charge} {Γ : Graph k n} {L : List (GnTC k n)}
    (h : Γ.GnDCT bc L) (φ : Fin n → Fin m) {Γ' : Graph k m} (L' : List (GnTC k m))
    (hmap : L'.map Prod.fst = Γ'.comps)
    (hbl : ∀ p ∈ L', p.2 = some false → p.1.kind.isDiffusive = true)
    (hbu : ∀ p ∈ L', p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.gnBlueC bc = true)
    (hmol : ∀ c ∈ Γ.comps, c.kind.joinsMol = true →
      Γ'.molGraph.Reachable (Sum.map id φ c.x) (Sum.map id φ c.y))
    (hedge : ∀ t : Bool, ∀ p ∈ L, p.2 = some t → ∀ a b, p.1.x = Sum.inr a → p.1.y = Sum.inr b →
      (Γ'.gnNetT L' t).Reachable (φ a) (φ b))
    (hcov : ∀ w : Fin m, ∃ a : Fin n, Γ'.SameMol (Sum.inr w) (Sum.inr (φ a))) : Γ'.GnDCT bc L' := by
  have key : ∀ t : Bool, (Γ.gnNetT L t).Preconnected → (Γ'.gnNetT L' t).Preconnected := by
    intro t hspan
    have hwalk : ∀ a b, (Γ.gnNetT L t).Reachable a b → (Γ'.gnNetT L' t).Reachable (φ a) (φ b) := by
      intro a b hr
      obtain ⟨w⟩ := hr
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a' b' c' hadj _ ih =>
        rw [Graph.gnNetT, SimpleGraph.fromRel_adj] at hadj
        have hstep : (Γ'.gnNetT L' t).Reachable (φ a') (φ b') := by
          rcases hadj.2 with (hs | ⟨p, hp, ht, hx, hy⟩) | (hs | ⟨p, hp, ht, hx, hy⟩)
          · exact Graph.gn_netT_reach_of_sameMol _ _ _ (gn_sameMol_map φ hmol hs)
          · exact hedge t p hp ht a' b' hx hy
          · exact (Graph.gn_netT_reach_of_sameMol _ _ _ (gn_sameMol_map φ hmol hs)).symm
          · exact (hedge t p hp ht b' a' hx hy).symm
        exact hstep.trans ih
    intro w₁ w₂
    obtain ⟨a₁, h₁⟩ := hcov w₁
    obtain ⟨a₂, h₂⟩ := hcov w₂
    exact ((Graph.gn_netT_reach_of_sameMol _ _ _ h₁).trans (hwalk a₁ a₂ (hspan a₁ a₂))).trans
      (Graph.gn_netT_reach_of_sameMol _ _ _ h₂).symm
  exact ⟨hmap, hbl, hbu, key false h.spanBlack, key true h.spanBlue⟩

/-- A tagged list of the components of `Γ` with tags `some false` on `black` and `some true` on
`blue`. -/
private def Graph.gnTagList (Γ : Graph k n) (black blue : Finset (Fin Γ.comps.length)) :
    List (GnTC k n) :=
  (List.finRange Γ.comps.length).map fun i =>
    (Γ.comps[i.1], if i ∈ black then some false else if i ∈ blue then some true else none)

private theorem Graph.gn_tagList_map_fst (Γ : Graph k n)
    (black blue : Finset (Fin Γ.comps.length)) :
    (Γ.gnTagList black blue).map Prod.fst = Γ.comps := by
  unfold Graph.gnTagList
  rw [List.map_map]
  exact List.map_getElem_finRange Γ.comps

private theorem Graph.gn_tagList_mem {Γ : Graph k n} {black blue : Finset (Fin Γ.comps.length)}
    {p : GnTC k n} (hp : p ∈ Γ.gnTagList black blue) : ∃ i : Fin Γ.comps.length,
    p = (Γ.comps[i.1], if i ∈ black then some false else if i ∈ blue then some true else none) := by
  unfold Graph.gnTagList at hp
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
  exact ⟨i, rfl⟩

/-- The net of a set of components is the net of the tagged list that marks them. -/
private theorem Graph.gn_net_eq_netT {Γ : Graph k n} {black blue : Finset (Fin Γ.comps.length)}
    (B : Finset (Fin Γ.comps.length)) (t : Bool)
    (hB : ∀ i : Fin Γ.comps.length,
      (if i ∈ black then some false else if i ∈ blue then some true else none) = some t ↔ i ∈ B) :
    Γ.net B = Γ.gnNetT (Γ.gnTagList black blue) t := by
  unfold Graph.net Graph.gnNetT
  congr 1
  funext a b
  refine propext (or_congr Iff.rfl ?_)
  constructor
  · rintro ⟨i, hi, hx, hy⟩
    exact ⟨_, List.mem_map_of_mem (List.mem_finRange i), (hB i).2 hi, hx, hy⟩
  · rintro ⟨p, hp, ht, hx, hy⟩
    obtain ⟨i, rfl⟩ := Graph.gn_tagList_mem hp
    exact ⟨i, (hB i).1 ht, hx, hy⟩

/-- The tagged list of a doubly connected graph. -/
private theorem Graph.gn_doublyConnected_dcs {Γ : Graph k n} (h : Γ.DoublyConnected) :
    Γ.GnDCS .plus := by
  obtain ⟨black, blue, hd, hbl, hbu, hsl, hsu⟩ := h
  refine ⟨Γ.gnTagList black blue, Γ.gn_tagList_map_fst black blue, ?_, ?_, ?_, ?_⟩
  · intro p hp ht
    obtain ⟨i, rfl⟩ := Graph.gn_tagList_mem hp
    by_cases hi : i ∈ black
    · exact hbl i hi
    · by_cases hj : i ∈ blue <;> simp [hi, hj] at ht
  · intro p hp ht
    obtain ⟨i, rfl⟩ := Graph.gn_tagList_mem hp
    by_cases hi : i ∈ black
    · simp [hi] at ht
    · by_cases hj : i ∈ blue
      · rw [Kind.gnBlueC_plus]
        exact hbu i hj
      · simp [hi, hj] at ht
  · rw [← Graph.gn_net_eq_netT black false]
    · exact hsl
    · intro i
      by_cases hi : i ∈ black <;> by_cases hj : i ∈ blue <;> simp [hi, hj]
  · rw [← Graph.gn_net_eq_netT blue true]
    · exact hsu
    · intro i
      by_cases hi : i ∈ black
      · have hj : i ∉ blue := fun hj => Finset.disjoint_left.1 hd hi hj
        simp [hi, hj]
      · by_cases hj : i ∈ blue <;> simp [hi, hj]

/-- A doubly connected structure with blue charge `plus` gives the doubly connected property. -/
private theorem Graph.GnDCT.doublyConnected {Γ : Graph k n} {L : List (GnTC k n)}
    (h : Γ.GnDCT .plus L) : Γ.DoublyConnected := by
  obtain ⟨cs, co⟩ := Γ
  obtain rfl : cs = L.map Prod.fst := h.map_fst.symm
  have hL : ∀ i : Fin (L.map Prod.fst).length, i.1 < L.length := fun i => by
    simpa using i.2
  let black : Finset (Fin (L.map Prod.fst).length) :=
    Finset.univ.filter fun i => (L[i.1]'(hL i)).2 = some false
  let blue : Finset (Fin (L.map Prod.fst).length) :=
    Finset.univ.filter fun i => (L[i.1]'(hL i)).2 = some true
  have hnet : ∀ (B : Finset (Fin (L.map Prod.fst).length)) (t : Bool),
      (∀ i : Fin (L.map Prod.fst).length, i ∈ B ↔ (L[i.1]'(hL i)).2 = some t) →
      (Graph.mk (L.map Prod.fst) co).net B = (Graph.mk (L.map Prod.fst) co).gnNetT L t := by
    intro B t hB
    unfold Graph.net Graph.gnNetT
    congr 1
    funext a b
    refine propext (or_congr Iff.rfl ?_)
    constructor
    · rintro ⟨i, hi, hx, hy⟩
      exact ⟨_, List.getElem_mem _, (hB i).1 hi, by simpa using hx, by simpa using hy⟩
    · rintro ⟨p, hp, ht, hx, hy⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
      exact ⟨⟨i, by simpa using hi⟩, (hB _).2 ht, by simpa using hx, by simpa using hy⟩
  refine ⟨black, blue, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hj
    simp only [black, blue, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rw [hi] at hj
    exact absurd hj (by simp)
  · intro i hi
    simp only [black, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa using h.black _ (List.getElem_mem _) hi
  · intro i hi
    simp only [blue, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have := h.blue _ (List.getElem_mem _) hi
    rw [Kind.gnBlueC_plus] at this
    simpa using this
  · rw [Graph.Spans, hnet black false]
    · exact h.spanBlack
    · intro i
      simp [black]
  · rw [Graph.Spans, hnet blue true]
    · exact h.spanBlue
    · intro i
      simp [blue]


/-- A graph with a doubly connected structure with blue charge `plus` is doubly connected. -/
private theorem Graph.GnDCS.doublyConnected {Γ : Graph k n} (h : Γ.GnDCS .plus) :
    Γ.DoublyConnected := by
  obtain ⟨L, hL⟩ := h
  exact hL.doublyConnected


/-- A tagged component of `L` is diffusive or blue. -/
private theorem Graph.GnDCT.kind_of_tag {bc : Charge} {Γ : Graph k n} {L : List (GnTC k n)}
    (h : Γ.GnDCT bc L) {p : GnTC k n} (hp : p ∈ L) (ht : p.2 ≠ none) :
    p.1.kind.isDiffusive = true ∨ p.1.kind.gnBlueC bc = true := by
  rcases hp2 : p.2 with _ | _ | _
  · exact absurd hp2 ht
  · exact Or.inl (h.black p hp hp2)
  · exact h.blue p hp hp2

end Tagged

/-! ## Outputs of `O_merge` that remove every dotted edge -/

section Out

variable {k n : ℕ}

/-- The graph on the atoms whose edges are the waved, dotted and diffusive edges. -/
private def Graph.gnWtd (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps,
    (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v

/-- The tracked graph `t` is obtained from `Γ` by an atom map that fixes the external atoms, maps
internal atoms onto internal atoms, identifies the ends of every dotted edge and separates the ends
of every solid edge: the components of `t` are the images of the components of `Γ` other than
dotted edges. -/
private structure GnOut (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps =
    Γ.comps.filterMap fun c => if c.kind = .dot then none else some (c.map t.f)
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_inr : ∃ h : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (h i)) ∧ Function.Surjective h
  f_dot : ∀ c ∈ Γ.comps, c.kind = .dot → t.f c.x = t.f c.y
  f_solid : ∀ c ∈ Γ.comps, c.kind.isSolid = true → t.f c.x ≠ t.f c.y

variable {Γ : Graph k n} {t : Tracked k n}

private theorem GnOut.mem (hs : GnOut Γ t) {c' : Comp (Atom k t.nOut)} :
    c' ∈ t.g.comps ↔ ∃ c ∈ Γ.comps, c.kind ≠ .dot ∧ c.map t.f = c' := by
  rw [hs.comps_eq, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, h⟩
    split_ifs at h with hk
    exact ⟨c, hc, hk, Option.some.inj h⟩
  · rintro ⟨c, hc, hk, rfl⟩
    exact ⟨c, hc, by simp [hk]⟩

private theorem GnOut.f_surj (hs : GnOut Γ t) : Function.Surjective t.f := by
  obtain ⟨h, hh, hsurj⟩ := hs.f_inr
  intro u
  rcases u with a | j
  · exact ⟨.inl a, hs.f_inl a⟩
  · obtain ⟨i, rfl⟩ := hsurj j
    exact ⟨.inr i, hh i⟩

private theorem GnOut.dotFree (hs : GnOut Γ t) : t.g.DotFree := by
  intro c' hc'
  obtain ⟨c, -, hk, rfl⟩ := hs.mem.1 hc'
  exact hk

private theorem GnOut.solid_ne (hs : GnOut Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind.isSolid = true → c'.x ≠ c'.y := by
  intro c' hc' hk
  obtain ⟨c, hc, -, rfl⟩ := hs.mem.1 hc'
  exact hs.f_solid c hc hk

/-- Every solid edge carries a `×`-dotted edge with the same ends, and every `×`-dotted edge
between distinct atoms carries a solid edge. -/
private def GnBal (Γ : Graph k n) : Prop :=
  (∀ c ∈ Γ.comps, c.kind.isSolid = true → ∃ d ∈ Γ.comps, d.kind = .xdot ∧
    (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x)) ∧
  (∀ c ∈ Γ.comps, c.kind = .xdot → c.x ≠ c.y → ∃ d ∈ Γ.comps, d.kind.isSolid = true ∧
    (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x))

private theorem GnOut.balance (hs : GnOut Γ t) (hb : GnBal Γ) :
    ∀ u v : Atom k t.nOut, u ≠ v →
      ((∃ c ∈ t.g.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ t.g.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u))) := by
  have hxd : (Kind.xdot).isSolid = false := rfl
  intro u v huv
  constructor
  · rintro ⟨c', hc', hk, hends⟩
    obtain ⟨c, hc, -, rfl⟩ := hs.mem.1 hc'
    have hne : c.x ≠ c.y := by
      intro h
      apply huv
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; simp [Comp.map, h]
      · rw [← h1, ← h2]; simp [Comp.map, h]
    obtain ⟨d, hd, hdk, hde⟩ := hb.2 c hc hk hne
    have hdnd : d.kind ≠ .dot := by intro h; rw [h] at hdk; cases hdk
    refine ⟨d.map t.f, hs.mem.2 ⟨d, hd, hdnd, rfl⟩, hdk, ?_⟩
    simp only [Comp.map] at hends ⊢
    rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  · rintro ⟨c', hc', hk, hends⟩
    obtain ⟨c, hc, -, rfl⟩ := hs.mem.1 hc'
    obtain ⟨d, hd, hdk, hde⟩ := hb.1 c hc hk
    have hdnd : d.kind ≠ .dot := by
      intro h
      rw [h] at hdk
      cases hdk
    refine ⟨d.map t.f, hs.mem.2 ⟨d, hd, hdnd, rfl⟩, hdk, ?_⟩
    simp only [Comp.map] at hends ⊢
    rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

private theorem GnOut.connected (hs : GnOut Γ t) (hc : Γ.edgeGraph.Preconnected) :
    t.g.edgeGraph.Preconnected := by
  have hedge : ∀ a b, (∃ c ∈ Γ.comps, c.x = a ∧ c.y = b) →
      t.g.edgeGraph.Reachable (t.f a) (t.f b) := by
    rintro a b ⟨c, hc, rfl, rfl⟩
    by_cases hk : c.kind = .dot
    · rw [hs.f_dot c hc hk]
    · exact gn_fromRel_reach ⟨c.map t.f, hs.mem.2 ⟨c, hc, hk, rfl⟩, rfl, rfl⟩
  intro u' v'
  obtain ⟨u, rfl⟩ := hs.f_surj u'
  obtain ⟨v, rfl⟩ := hs.f_surj v'
  exact gn_reach_map t.f hedge (hc u v)

private theorem GnOut.internal (hs : GnOut Γ t)
    (hw : ∀ a b : Fin n, Γ.gnWtd.Reachable (.inr a) (.inr b)) :
    ∀ a b : Fin t.nOut, t.g.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
  have hedge : ∀ a b, (∃ c ∈ Γ.comps,
      (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧ c.x = a ∧ c.y = b) →
      t.g.wavedThetaGraph.Reachable (t.f a) (t.f b) := by
    rintro a b ⟨c, hc, hk, rfl, rfl⟩
    by_cases hd : c.kind = .dot
    · rw [hs.f_dot c hc hd]
    · refine gn_fromRel_reach ⟨c.map t.f, hs.mem.2 ⟨c, hc, hd, rfl⟩, ?_, rfl, rfl⟩
      change (c.kind.joinsMol = true ∧ c.kind ≠ .dot) ∨ c.kind.isDiffusive = true
      tauto
  obtain ⟨h, hh, hsurj⟩ := hs.f_inr
  intro a b
  obtain ⟨i, rfl⟩ := hsurj a
  obtain ⟨j, rfl⟩ := hsurj b
  rw [← hh, ← hh]
  exact gn_reach_map t.f hedge (hw i j)

/-- The output is normal regular, with the bound `k + n + #components of Γ`. -/
private theorem GnOut.normal (hs : GnOut Γ t) (hb : GnBal Γ) (hc : Γ.edgeGraph.Preconnected)
    (hw : ∀ a b : Fin n, Γ.gnWtd.Reachable (.inr a) (.inr b)) :
    t.g.Normal (k + n + Γ.comps.length) := by
  refine ⟨⟨?_, hs.connected hc, hs.internal hw, ?_⟩, hs.solid_ne, hs.balance hb⟩
  · have h1 := hs.nOut_le
    have h2 : t.g.comps.length ≤ Γ.comps.length := by
      rw [hs.comps_eq]
      exact List.length_filterMap_le _ _
    omega
  · intro c hc hk
    exact absurd hk (hs.dotFree c hc)

/-- The output has dot excess `0`. -/
private theorem GnOut.dotExcess (hs : GnOut Γ t) : t.g.dotExcess = 0 :=
  gn_eL_of_nodot hs.dotFree

/-- The output of a doubly connected graph is doubly connected. -/
private theorem GnOut.doublyConnected (hs : GnOut Γ t) (hdc : Γ.DoublyConnected) :
    t.g.DoublyConnected := by
  obtain ⟨L, hL⟩ := Graph.gn_doublyConnected_dcs hdc
  obtain ⟨h, hh, hsurj⟩ := hs.f_inr
  have hf : t.f = Sum.map id h := by
    funext u
    rcases u with a | i
    · exact hs.f_inl a
    · exact hh i
  let L' : List (GnTC k t.nOut) :=
    L.filterMap fun p => if p.1.kind = .dot then none else some (p.1.map t.f, p.2)
  have hmem : ∀ p ∈ L, p.1.kind ≠ .dot → (p.1.map t.f, p.2) ∈ L' := by
    intro p hp hk
    exact List.mem_filterMap.2 ⟨p, hp, by simp [hk]⟩
  have hmem' : ∀ q ∈ L', ∃ p ∈ L, p.1.kind ≠ .dot ∧ q = (p.1.map t.f, p.2) := by
    intro q hq
    obtain ⟨p, hp, hq'⟩ := List.mem_filterMap.1 hq
    split_ifs at hq' with hk
    exact ⟨p, hp, hk, (Option.some.inj hq').symm⟩
  have hfst : ∀ M : List (GnTC k n), (M.filterMap fun p =>
      if p.1.kind = .dot then none else some (p.1.map t.f, p.2)).map Prod.fst =
      (M.map Prod.fst).filterMap fun c => if c.kind = .dot then none else some (c.map t.f) := by
    intro M
    induction M with
    | nil => rfl
    | cons p M ih =>
      by_cases hk : p.1.kind = .dot
      · simp [hk, ih]
      · simp [hk, ih]
  refine Graph.GnDCS.doublyConnected ⟨L', hL.transport h L' ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rw [hfst, hL.map_fst, hs.comps_eq]
  · intro q hq hqt
    obtain ⟨p, hp, -, rfl⟩ := hmem' q hq
    exact hL.black p hp hqt
  · intro q hq hqt
    obtain ⟨p, hp, -, rfl⟩ := hmem' q hq
    exact hL.blue p hp hqt
  · intro c hc hk
    rw [← hf]
    by_cases hd : c.kind = .dot
    · rw [hs.f_dot c hc hd]
    · exact Graph.gn_molReach_of_comp (hs.mem.2 ⟨c, hc, hd, rfl⟩) hk
  · intro b p hp hpt a a' hx hy
    have hkind := hL.kind_of_tag hp (by rw [hpt]; simp)
    have hnd : p.1.kind ≠ .dot := by
      intro hd
      rw [hd] at hkind
      simp [Kind.isDiffusive, Kind.gnBlueC] at hkind
    refine Graph.gn_netT_reach_of_mem _ _ _ (hmem p hp hnd) hpt ?_ ?_
    · change t.f p.1.x = _
      rw [hx, hh]
    · change t.f p.1.y = _
      rw [hy, hh]
  · intro w
    obtain ⟨a, rfl⟩ := hsurj w
    exact ⟨a, Or.inl rfl⟩

end Out

/-! ## The atoms of a substituted graph -/

section Atoms

variable {m j : ℕ}

private theorem gn_liftA_inj : Function.Injective (liftA (k := 3) (n := m) j) :=
  Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective m j⟩

private theorem gn_newA_inj : Function.Injective (newA (k := 3) (n := m) (j := j)) :=
  fun _ _ h => Fin.natAdd_injective j m (Sum.inr_injective h)

private theorem gn_liftA_ne_newA (u : Atom 3 m) (i : Fin j) : liftA j u ≠ newA i := by
  rcases u with a | a
  · simp [liftA, newA]
  · simp only [liftA, newA, Sum.map_inr, ne_eq, Sum.inr.injEq, Fin.ext_iff, Fin.val_castAdd,
      Fin.val_natAdd]
    omega

private theorem gn_isRight_liftA (u : Atom 3 m) : (liftA j u).isRight = u.isRight := by
  rcases u with a | a <;> rfl

/-- An atom of a graph with `j` more internal atoms is an old atom or a new one. -/
private theorem gn_atom_cases (w : Atom 3 (m + j)) : (∃ u, w = liftA j u) ∨ ∃ i, w = newA i := by
  rcases w with a | i
  · exact Or.inl ⟨.inl a, rfl⟩
  · induction i using Fin.addCases with
    | left i => exact Or.inl ⟨.inr i, rfl⟩
    | right i => exact Or.inr ⟨i, rfl⟩

end Atoms

/-! ## Graphs on the components of a given kind -/

section KindGraph

variable {k n : ℕ}

/-- The graph on the atoms whose edges are the components with kind satisfying `P`. -/
private def gn_kg (Γ : Graph k n) (P : Kind → Prop) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, P c.kind ∧ c.x = u ∧ c.y = v

private theorem gn_kg_edge (Γ : Graph k n) : Γ.edgeGraph = gn_kg Γ fun _ => True := by
  ext u v
  simp [Graph.edgeGraph, gn_kg]

private theorem gn_kg_of_mem {Γ : Graph k n} {P : Kind → Prop} {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hP : P c.kind) : (gn_kg Γ P).Reachable c.x c.y :=
  gn_fromRel_reach ⟨c, hc, hP, rfl, rfl⟩

/-- Reachability is carried by a map of the atoms that carries every component of kind `P` of
`Γ` to a component of kind `P'` of `Γ'`. -/
private theorem gn_kg_map {k' n' : ℕ} {Γ : Graph k n} {Γ' : Graph k' n'} {P P' : Kind → Prop}
    (ψ : Atom k n → Atom k' n') (h : ∀ c ∈ Γ.comps, P c.kind → c.map ψ ∈ Γ'.comps ∧ P' c.kind)
    {u v : Atom k n} (hr : (gn_kg Γ P).Reachable u v) : (gn_kg Γ' P').Reachable (ψ u) (ψ v) := by
  refine gn_reach_map (r := fun u v => ∃ c ∈ Γ.comps, P c.kind ∧ c.x = u ∧ c.y = v) ψ ?_ hr
  rintro a b ⟨c, hc, hP, rfl, rfl⟩
  obtain ⟨h1, h2⟩ := h c hc hP
  exact gn_kg_of_mem (c := c.map ψ) h1 h2

end KindGraph

/-! ## The substituted graph -/

section Glue

variable {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m} {g : Graph 3 n'}

/-- The components of the `t`-variable `t_{y₁y₂,x}` at the new atom `α`. -/
private theorem gn_tvar_comps (x y₁ y₂ : Atom 3 m) :
    (tVar true).comps.map (Comp.map (glueAtom (n' := 1) x y₁ y₂)) =
      [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
       mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
       mkC .xdot (liftA 1 y₂) (newA 0)] := rfl

private theorem gn_mem_glue {n'' : ℕ} {𝒢 : Graph 3 n''} {c : Comp (Atom 3 (m + n''))} :
    c ∈ (H.glue x y₁ y₂ 𝒢).comps ↔
      (∃ d ∈ H.comps, d.map (liftA n'') = c) ∨ ∃ d ∈ 𝒢.comps, d.map (glueAtom x y₁ y₂) = c := by
  simp [Graph.glue, liftCs]

private theorem gn_mem_host {c : Comp (Atom 3 (m + 1))} :
    c ∈ (H.glue x y₁ y₂ (tVar true)).comps ↔
      (∃ d ∈ H.comps, d.map (liftA 1) = c) ∨
        c ∈ [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
          mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
          mkC .xdot (liftA 1 y₂) (newA 0)] := by
  rw [← gn_tvar_comps]
  simp only [Graph.glue, liftCs, List.mem_append, List.mem_map]

/-- Every component of the `t`-variable has the end `α`. -/
private theorem gn_tvar_alpha {c : Comp (Atom 3 (m + 1))}
    (hc : c ∈ [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
      mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
      mkC .xdot (liftA 1 y₂) (newA 0)]) :
    (c.x = newA 0 ∨ c.y = newA 0) ∧ (c.x = liftA 1 x ∨ c.x = liftA 1 y₁ ∨ c.x = liftA 1 y₂ ∨
      c.x = newA 0) ∧ (c.y = liftA 1 x ∨ c.y = newA 0) ∧
      (c.kind.isSolid = false → c.kind ≠ .xdot → c = mkC (.waved .s) (newA 0) (liftA 1 x)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [mkC, Kind.isSolid]

/-- A component of `H` with its image in the host. -/
private theorem gn_host_of_H {d : Comp (Atom 3 m)} (hd : d ∈ H.comps) :
    d.map (liftA 1) ∈ (H.glue x y₁ y₂ (tVar true)).comps :=
  gn_mem_host.2 (Or.inl ⟨d, hd, rfl⟩)

/-- A component of the host whose ends are old atoms comes from `H`. -/
private theorem gn_H_of_host {c : Comp (Atom 3 (m + 1))}
    (hc : c ∈ (H.glue x y₁ y₂ (tVar true)).comps) (hx : ∃ u, c.x = liftA 1 u)
    (hy : ∃ v, c.y = liftA 1 v) : ∃ d ∈ H.comps, d.map (liftA 1) = c := by
  rcases gn_mem_host.1 hc with h | h
  · exact h
  · exfalso
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    rcases (gn_tvar_alpha h).1 with h1 | h1
    · exact gn_liftA_ne_newA u 0 (hu.symm.trans h1)
    · exact gn_liftA_ne_newA v 0 (hv.symm.trans h1)

private theorem gn_glueAtom_inl (e : Fin 3) :
    glueAtom (n' := n') x y₁ y₂ (.inl e) = liftA n' (![x, y₁, y₂] e) := rfl

private theorem gn_isRight_glueAtom (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) (p : Atom 3 n') : (glueAtom x y₁ y₂ p).isRight = true := by
  rcases p with e | i
  · rw [gn_glueAtom_inl, gn_isRight_liftA]
    fin_cases e
    · exact hx
    · exact hy₁
    · exact hy₂
  · rfl

/-- The ends of a companion are carried by a map of the atoms. -/
private theorem gn_ends_map {V W : Type*} (f : V → W) {d e : Comp V}
    (h : e.x = d.x ∧ e.y = d.y ∨ e.x = d.y ∧ e.y = d.x) :
    (e.map f).x = (d.map f).x ∧ (e.map f).y = (d.map f).y ∨
      (e.map f).x = (d.map f).y ∧ (e.map f).y = (d.map f).x := by
  simp only [Comp.map]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

/-- The ends of a companion are pulled back along an injective map of the atoms. -/
private theorem gn_ends_inj {V W : Type*} {f : V → W} (hf : Function.Injective f) {d e : Comp V}
    (h : (e.map f).x = (d.map f).x ∧ (e.map f).y = (d.map f).y ∨
      (e.map f).x = (d.map f).y ∧ (e.map f).y = (d.map f).x) :
    e.x = d.x ∧ e.y = d.y ∨ e.x = d.y ∧ e.y = d.x := by
  simp only [Comp.map] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hf h1, hf h2⟩
  · exact Or.inr ⟨hf h1, hf h2⟩

/-- Every dotted edge of the substituted graph joins two internal atoms. -/
private theorem gn_glue_dot (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) (hGd : (H.glue x y₁ y₂ (tVar true)).DotFree) :
    ∀ c ∈ (H.glue x y₁ y₂ g).comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true := by
  intro c hc hk
  rcases gn_mem_glue.1 hc with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
  · exact absurd hk (hGd _ (gn_host_of_H hd))
  · exact ⟨gn_isRight_glueAtom hx hy₁ hy₂ _, gn_isRight_glueAtom hx hy₁ hy₂ _⟩

/-- The components of `H` in the substituted graph are not dotted edges. -/
private theorem gn_H_nodot (hGd : (H.glue x y₁ y₂ (tVar true)).DotFree) :
    ∀ c ∈ liftCs n' H.comps, c.kind ≠ .dot := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact hGd _ (gn_host_of_H hd)

/-- The substituted graph is balanced: every solid edge has a `×`-dotted companion and every
`×`-dotted edge between distinct atoms has a solid companion. -/
private theorem gn_glue_bal {C C' : ℕ} (hG : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hg : g.Normal C') : GnBal (H.glue x y₁ y₂ g) := by
  constructor
  · intro c hc hs
    rcases gn_mem_glue.1 hc with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · have hd' := gn_host_of_H (x := x) (y₁ := y₁) (y₂ := y₂) hd
      have hne := hG.2.1 _ hd' hs
      obtain ⟨e, he, hek, hee⟩ := (hG.2.2 _ _ hne).2 ⟨_, hd', hs, Or.inl ⟨rfl, rfl⟩⟩
      obtain ⟨e', he', rfl⟩ := gn_H_of_host he
        (by rcases hee with ⟨h, -⟩ | ⟨h, -⟩ <;> exact ⟨_, h⟩)
        (by rcases hee with ⟨-, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩)
      refine ⟨e'.map (liftA n'), gn_mem_glue.2 (Or.inl ⟨e', he', rfl⟩), hek, ?_⟩
      exact gn_ends_map _ (gn_ends_inj gn_liftA_inj hee)
    · have hne := hg.2.1 d hd hs
      obtain ⟨e, he, hek, hee⟩ := (hg.2.2 _ _ hne).2 ⟨d, hd, hs, Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨e.map _, gn_mem_glue.2 (Or.inr ⟨e, he, rfl⟩), hek, gn_ends_map _ hee⟩
  · intro c hc hk hne
    rcases gn_mem_glue.1 hc with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · have hd' := gn_host_of_H (x := x) (y₁ := y₁) (y₂ := y₂) hd
      have hne' : (d.map (liftA 1)).x ≠ (d.map (liftA 1)).y := by
        intro h
        exact hne (congrArg (liftA n') (gn_liftA_inj h))
      obtain ⟨e, he, hek, hee⟩ := (hG.2.2 _ _ hne').1 ⟨_, hd', hk, Or.inl ⟨rfl, rfl⟩⟩
      obtain ⟨e', he', rfl⟩ := gn_H_of_host he
        (by rcases hee with ⟨h, -⟩ | ⟨h, -⟩ <;> exact ⟨_, h⟩)
        (by rcases hee with ⟨-, h⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩)
      refine ⟨e'.map (liftA n'), gn_mem_glue.2 (Or.inl ⟨e', he', rfl⟩), hek, ?_⟩
      exact gn_ends_map _ (gn_ends_inj gn_liftA_inj hee)
    · have hne' : d.x ≠ d.y := fun h => hne (by simp [Comp.map, h])
      obtain ⟨e, he, hek, hee⟩ := (hg.2.2 _ _ hne').1 ⟨d, hd, hk, Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨e.map _, gn_mem_glue.2 (Or.inr ⟨e, he, rfl⟩), hek, gn_ends_map _ hee⟩

/-- A path in the host from an original atom stays among the original atoms, joined in `H`, until it reaches
an atom of `S`; the components of the `t`-variable of kind `P` only leave `S`. -/
private theorem gn_host_escape (P : Kind → Prop) (S : Atom 3 m → Prop)
    (hS : ∀ c ∈ [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
      mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
      mkC .xdot (liftA 1 y₂) (newA 0)], P c.kind → ∀ z, (c.x = liftA 1 z ∨ c.y = liftA 1 z) → S z)
    {u : Atom 3 m} {w : Atom 3 (m + 1)}
    (hr : (gn_kg (H.glue x y₁ y₂ (tVar true)) P).Reachable (liftA 1 u) w) :
    (∃ z, w = liftA 1 z ∧ (gn_kg H P).Reachable u z) ∨ ∃ s, S s ∧ (gn_kg H P).Reachable u s := by
  refine gn_escape (F := gn_kg H P) (liftA 1) S (fun z w' hadj => ?_) hr
  unfold gn_kg at hadj
  rw [SimpleGraph.fromRel_adj] at hadj
  obtain ⟨-, ⟨c, hc, hP, hcx, hcy⟩ | ⟨c, hc, hP, hcx, hcy⟩⟩ := hadj
  · rcases gn_mem_host.1 hc with ⟨d, hd, rfl⟩ | ht
    · have h1 : d.x = z := gn_liftA_inj hcx
      refine Or.inl ⟨d.y, hcy.symm, ?_⟩
      rw [← h1]
      exact gn_kg_of_mem hd hP
    · exact Or.inr (hS c ht hP z (Or.inl hcx))
  · rcases gn_mem_host.1 hc with ⟨d, hd, rfl⟩ | ht
    · have h1 : d.y = z := gn_liftA_inj hcy
      refine Or.inl ⟨d.x, hcx.symm, ?_⟩
      rw [← h1]
      exact (gn_kg_of_mem hd hP).symm
    · exact Or.inr (hS c ht hP z (Or.inr hcy))

/-- Every atom of `H` is joined in `H` to `x`, `y₁` or `y₂`. -/
private theorem gn_H_reach_ext {C : ℕ} (hG : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (u : Atom 3 m) : ∃ s, (s = x ∨ s = y₁ ∨ s = y₂) ∧ (gn_kg H fun _ => True).Reachable u s := by
  have hr := hG.1.connected (liftA 1 u) (newA 0)
  rw [gn_kg_edge] at hr
  have hS : ∀ c ∈ [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
      mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
      mkC .xdot (liftA 1 y₂) (newA 0)], (fun _ => True) c.kind →
      ∀ z, (c.x = liftA 1 z ∨ c.y = liftA 1 z) → z = x ∨ z = y₁ ∨ z = y₂ := by
    intro c hc _ z hz
    obtain ⟨-, h2, h3, -⟩ := gn_tvar_alpha hc
    rcases hz with hz | hz
    · rw [hz] at h2
      rcases h2 with h | h | h | h
      · exact Or.inl (gn_liftA_inj h)
      · exact Or.inr (Or.inl (gn_liftA_inj h))
      · exact Or.inr (Or.inr (gn_liftA_inj h))
      · exact absurd h (gn_liftA_ne_newA z 0)
    · rw [hz] at h3
      rcases h3 with h | h
      · exact Or.inl (gn_liftA_inj h)
      · exact absurd h (gn_liftA_ne_newA z 0)
  rcases gn_host_escape (fun _ => True) (fun s => s = x ∨ s = y₁ ∨ s = y₂) hS hr with
    ⟨z, hz, -⟩ | h
  · exact absurd hz.symm (gn_liftA_ne_newA z 0)
  · exact h

/-- The kinds of the edges of `Graph.wavedThetaGraph` are neither solid edges nor `×`-dotted
edges. -/
private theorem gn_wt_kind {κ : Kind} (h : κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true) :
    κ.isSolid = false ∧ κ ≠ .xdot := by
  cases κ <;> simp_all [Kind.joinsMol, Kind.isDiffusive, Kind.isSolid]

/-- Every internal atom of `H` is joined to `x` in `H` by waved and diffusive edges. -/
private theorem gn_H_reach_x {C : ℕ} (hx : x.isRight = true)
    (hG : (H.glue x y₁ y₂ (tVar true)).Normal C) (i : Fin m) :
    (gn_kg H fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true).Reachable
      (.inr i) x := by
  obtain ⟨ix, rfl⟩ : ∃ ix, x = .inr ix := by
    rcases x with a | a
    · simp at hx
    · exact ⟨a, rfl⟩
  have hr := hG.1.internal (Fin.castAdd 1 i) (Fin.castAdd 1 ix)
  change (gn_kg (H.glue (.inr ix) y₁ y₂ (tVar true))
    fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true).Reachable
    (liftA 1 (.inr i)) (liftA 1 (.inr ix)) at hr
  have hS : ∀ c ∈ [mkC (.waved .s) (newA 0) (liftA 1 (.inr ix)),
      mkC (.G .plus) (liftA 1 y₁) (newA 0), mkC (.G .minus) (liftA 1 y₂) (newA 0),
      mkC .xdot (liftA 1 y₁) (newA 0), mkC .xdot (liftA 1 y₂) (newA 0)],
      (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) →
      ∀ z, (c.x = liftA 1 z ∨ c.y = liftA 1 z) → z = .inr ix := by
    intro c hc hP z hz
    obtain ⟨hs, hxd⟩ := gn_wt_kind hP
    have hc' := (gn_tvar_alpha hc).2.2.2 hs hxd
    rw [hc'] at hz
    rcases hz with hz | hz
    · exact absurd hz.symm (gn_liftA_ne_newA z 0)
    · exact (gn_liftA_inj (j := 1) (show liftA 1 (.inr ix) = liftA 1 z from hz)).symm
  rcases gn_host_escape _ (fun s => s = .inr ix) hS hr with ⟨z, hz, h⟩ | ⟨s, rfl, h⟩
  · rw [gn_liftA_inj hz]
    exact h
  · exact h

/-- The images of `⊗`, `⊕`, `⊖`. -/
private theorem gn_ext_image (s : Atom 3 m) (hs : s = x ∨ s = y₁ ∨ s = y₂) :
    ∃ e : Fin 3, liftA n' s = glueAtom x y₁ y₂ (.inl e) := by
  rcases hs with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- The substituted graph is connected. -/
private theorem gn_glue_conn {C C' : ℕ} (hG : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hg : g.Normal C') : (H.glue x y₁ y₂ g).edgeGraph.Preconnected := by
  rw [gn_kg_edge]
  have hgg : ∀ p q : Atom 3 n',
      (gn_kg (H.glue x y₁ y₂ g) fun _ => True).Reachable (glueAtom x y₁ y₂ p)
        (glueAtom x y₁ y₂ q) := by
    intro p q
    have h := hg.1.connected p q
    rw [gn_kg_edge] at h
    exact gn_kg_map _ (fun c hc _ => ⟨gn_mem_glue.2 (Or.inr ⟨c, hc, rfl⟩), trivial⟩) h
  have hcov : ∀ w, ∃ p : Atom 3 n',
      (gn_kg (H.glue x y₁ y₂ g) fun _ => True).Reachable w (glueAtom x y₁ y₂ p) := by
    intro w
    rcases gn_atom_cases w with ⟨u, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨s, hs, hr⟩ := gn_H_reach_ext hG u
      obtain ⟨e, he⟩ := gn_ext_image (n' := n') s hs
      refine ⟨.inl e, ?_⟩
      rw [← he]
      exact gn_kg_map _ (fun c hc _ => ⟨gn_mem_glue.2 (Or.inl ⟨c, hc, rfl⟩), trivial⟩) hr
    · exact ⟨.inr i, SimpleGraph.Reachable.refl _⟩
  intro w₁ w₂
  obtain ⟨p, hp⟩ := hcov w₁
  obtain ⟨q, hq⟩ := hcov w₂
  exact (hp.trans (hgg p q)).trans hq.symm

/-- Any two internal atoms of the substituted graph are joined by waved, dotted and diffusive
edges. -/
private theorem gn_glue_wtd {C C' : ℕ} (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) (hG : (H.glue x y₁ y₂ (tVar true)).Normal C) (hg : g.Normal C')
    (hgr : g.RgCheck) (a b : Fin (m + n')) :
    (H.glue x y₁ y₂ g).gnWtd.Reachable (.inr a) (.inr b) := by
  change (gn_kg _ fun κ => κ.joinsMol = true ∨ κ.isDiffusive = true).Reachable _ _
  have hHmap : ∀ {u v : Atom 3 m},
      (gn_kg H fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true).Reachable u v →
      (gn_kg (H.glue x y₁ y₂ g) fun κ => κ.joinsMol = true ∨ κ.isDiffusive = true).Reachable
        (liftA n' u) (liftA n' v) := fun h =>
    gn_kg_map _ (fun c hc hP => ⟨gn_mem_glue.2 (Or.inl ⟨c, hc, rfl⟩), by tauto⟩) h
  have hgmap : ∀ {p q : Atom 3 n'},
      (gn_kg g fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true).Reachable p q →
      (gn_kg (H.glue x y₁ y₂ g) fun κ => κ.joinsMol = true ∨ κ.isDiffusive = true).Reachable
        (glueAtom x y₁ y₂ p) (glueAtom x y₁ y₂ q) := fun h =>
    gn_kg_map _ (fun c hc hP => ⟨gn_mem_glue.2 (Or.inr ⟨c, hc, rfl⟩), by tauto⟩) h
  -- every internal atom of `H` reaches `x`
  have hHx : ∀ u : Atom 3 m, u.isRight = true →
      (gn_kg (H.glue x y₁ y₂ g) fun κ => κ.joinsMol = true ∨ κ.isDiffusive = true).Reachable
        (liftA n' u) (liftA n' x) := by
    intro u hu
    rcases u with a | i
    · simp at hu
    · exact hHmap (gn_H_reach_x hx hG i)
  have hall : ∀ a : Fin (m + n'),
      (gn_kg (H.glue x y₁ y₂ g) fun κ => κ.joinsMol = true ∨ κ.isDiffusive = true).Reachable
        (.inr a) (liftA n' x) := by
    intro a
    rcases gn_atom_cases (.inr a) with ⟨u, hu⟩ | ⟨i, hi⟩
    · rw [hu]
      refine hHx u ?_
      rw [← gn_isRight_liftA (j := n'), ← hu]
      rfl
    · rw [hi]
      rcases hgr with h0 | ⟨c, hc, hP, hends⟩
      · exact (Fin.elim0 (h0 ▸ i))
      have hce : (gn_kg (H.glue x y₁ y₂ g) fun κ => κ.joinsMol = true ∨
          κ.isDiffusive = true).Reachable (glueAtom x y₁ y₂ c.x) (glueAtom x y₁ y₂ c.y) :=
        gn_kg_of_mem (c := c.map (glueAtom x y₁ y₂)) (gn_mem_glue.2 (Or.inr ⟨c, hc, rfl⟩)) hP
      -- the internal end `j₀` and the external end `e` of `c`
      have key : ∀ (j₀ : Fin n') (e : Fin 3),
          (gn_kg (H.glue x y₁ y₂ g) fun κ => κ.joinsMol = true ∨
            κ.isDiffusive = true).Reachable (newA j₀) (liftA n' (![x, y₁, y₂] e)) →
          (gn_kg (H.glue x y₁ y₂ g) fun κ => κ.joinsMol = true ∨
            κ.isDiffusive = true).Reachable (newA i) (liftA n' x) := by
        intro j₀ e h
        have h1 : (gn_kg (H.glue x y₁ y₂ g) fun κ => κ.joinsMol = true ∨
            κ.isDiffusive = true).Reachable (newA i) (newA j₀) :=
          hgmap (hg.1.internal i j₀)
        refine (h1.trans h).trans (hHx _ ?_)
        fin_cases e
        · exact hx
        · exact hy₁
        · exact hy₂
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hcx : c.x with e | j₀
        · rw [hcx] at h1; simp at h1
        rcases hcy : c.y with e | j₁
        · rw [hcx, hcy] at hce
          exact key j₀ e hce
        · rw [hcy] at h2; simp at h2
      · rcases hcx : c.x with e | j₀
        · rcases hcy : c.y with e' | j₁
          · rw [hcy] at h2; simp at h2
          · rw [hcx, hcy] at hce
            exact key j₁ e hce.symm
        · rw [hcx] at h1; simp at h1
  exact (hall a).trans (hall b).symm

end Glue

/-! ## The dot excess of the substituted graph -/

section GlueDotExcess

variable {k n n' : ℕ}

/-- An atom met by no dotted component is alone in its block. -/
private theorem gn_dg_isolated {L : List (Comp (Atom k n))} {a : Atom k n}
    (h : ∀ c ∈ L, c.kind = .dot → c.x ≠ a ∧ c.y ≠ a) {u : Atom k n} (hr : (dg L).Reachable a u) :
    u = a := by
  obtain ⟨w⟩ := hr
  cases w with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    rcases hxy with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact (h c hc hk).1 h1
    · exact (h c hc hk).2 h2

/-- The dotted edges `⊗ = ⊕`, `⊗ = ⊖`, `⊕ = ⊖` for the identifications `a`, `b`, `c`. -/
private def gn_I (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    List (Comp (Atom 3 n')) :=
  (if a then [mkC .dot (.inl 0) (.inl 1)] else []) ++
    (if b then [mkC .dot (.inl 0) (.inl 2)] else []) ++
    (if c then [mkC .dot (.inl 1) (.inl 2)] else [])

open Classical in
/-- The dot excess after the identifications `a` (`⊗ = ⊕`), `b` (`⊗ = ⊖`), `c` (`⊕ = ⊖`) of a list
of components without dotted edge at `⊗`. -/
private theorem gn_eL_ext (a b c : Prop) [Decidable a] [Decidable b] [Decidable c]
    (hab : a → b → c) (hac : a → c → b) (hbc : b → c → a) (B : List (Comp (Atom 3 n')))
    (hB : ∀ d ∈ B, d.kind = .dot → d.x ≠ .inl 0 ∧ d.y ≠ .inl 0) :
    eL (gn_I a b c ++ B) = eL B + (if c ∧ (dg B).Reachable (.inl 1) (.inl 2) then 1 else 0) +
      (if a ∧ b then 1 else 0) := by
  have hiso : ∀ u, (dg B).Reachable (.inl 0) u → u = .inl 0 := fun u h => gn_dg_isolated hB h
  have h01 : ¬ (dg B).Reachable (.inl 0) (.inl 1) := fun h => by simpa using hiso _ h
  have h02 : ¬ (dg B).Reachable (.inl 0) (.inl 2) := fun h => by simpa using hiso _ h
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c
  · -- `⊗ = ⊕ = ⊖`
    simp only [gn_I, ha, hb, hc, ite_true, List.cons_append,
      List.nil_append, true_and, and_self]
    have e1 : (dg (mkC .dot (.inl 0) (.inl 2) :: mkC .dot (.inl 1) (.inl 2) :: B)).Reachable
        (.inl 0) (.inl 1) :=
      (dg_reach_of_mem (c := mkC .dot (.inl 0) (.inl 2)) (by simp) rfl).trans
        (dg_reach_of_mem (c := mkC .dot (.inl 1) (.inl 2)) (by simp) rfl).symm
    have e2 : ¬ (dg (mkC .dot (.inl 1) (.inl 2) :: B)).Reachable (.inl 0) (.inl 2) := by
      rw [gn_reach_add_edge_iff (gn_dg_cons_dot_adj B rfl)]
      rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact h02 h
      · exact h01 h
      · exact h02 h
    rw [gn_eL_cons_dot_red _ rfl e1, gn_eL_cons_dot_new _ rfl e2]
    by_cases hP : (dg B).Reachable (.inl 1) (.inl 2)
    · rw [gn_eL_cons_dot_red _ rfl hP, ite_eq_left hP]
    · rw [gn_eL_cons_dot_new _ rfl hP, ite_eq_right hP]
      ring
  · exact absurd (hab ha hb) hc
  · exact absurd (hac ha hc) hb
  · simp only [gn_I, ha, hb, hc, ite_true, ite_false, List.cons_append,
      List.nil_append, List.append_nil, false_and, and_false]
    rw [gn_eL_cons_dot_new _ rfl h01]
    ring
  · exact absurd (hbc hb hc) ha
  · simp only [gn_I, ha, hb, hc, ite_true, ite_false, List.cons_append,
      List.nil_append, List.append_nil, false_and]
    rw [gn_eL_cons_dot_new _ rfl h02]
    ring
  · simp only [gn_I, ha, hb, hc, ite_true, ite_false, List.cons_append,
      List.nil_append, List.append_nil, true_and, and_false]
    by_cases hP : (dg B).Reachable (.inl 1) (.inl 2)
    · rw [gn_eL_cons_dot_red _ rfl hP, ite_eq_left hP]
      ring
    · rw [gn_eL_cons_dot_new _ rfl hP, ite_eq_right hP]
      ring
  · simp only [gn_I, ha, hb, hc, ite_false, List.nil_append, false_and, and_false]
    ring

variable {m : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m} {g : Graph 3 n'}

/-- The identified pairs of external atoms of `g` are joined by the dotted edges `gn_I`. -/
private theorem gn_I_reach (e e' : Fin 3) (he : ![x, y₁, y₂] e = ![x, y₁, y₂] e') :
    (dg (gn_I (n' := n') (x = y₁) (x = y₂) (y₁ = y₂))).Reachable (.inl e) (.inl e') := by
  fin_cases e <;> fin_cases e' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at he ⊢
  all_goals first
    | exact SimpleGraph.Reachable.refl _
    | exact dg_reach_of_mem (c := mkC .dot (.inl 0) (.inl 1)) (by simp [gn_I, he]) rfl
    | exact (dg_reach_of_mem (c := mkC .dot (.inl 0) (.inl 1)) (by simp [gn_I, he]) rfl).symm
    | exact dg_reach_of_mem (c := mkC .dot (.inl 0) (.inl 2)) (by simp [gn_I, he]) rfl
    | exact (dg_reach_of_mem (c := mkC .dot (.inl 0) (.inl 2)) (by simp [gn_I, he]) rfl).symm
    | exact dg_reach_of_mem (c := mkC .dot (.inl 1) (.inl 2)) (by simp [gn_I, he]) rfl
    | exact (dg_reach_of_mem (c := mkC .dot (.inl 1) (.inl 2)) (by simp [gn_I, he]) rfl).symm

/-- **The dot excess of the substituted graph**: `1` if `y₁ = y₂` and `⊕`, `⊖` lie in one block of
`g`, and `0` otherwise, for `g` with dot excess `0` and no dotted edge at `⊗`. -/
private theorem gn_glue_dotExcess (hGd : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hgo : g.OtimesNoDot) (hge : g.dotExcess = 0) :
    (H.glue x y₁ y₂ g).dotExcess = if y₁ = y₂ ∧ g.PMBlock then 1 else 0 := by
  have h0 : (H.glue x y₁ y₂ g).dotExcess = eL (g.comps.map (Comp.map (glueAtom x y₁ y₂))) :=
    gn_eL_append_nodot (gn_H_nodot hGd) _
  have hI : ∀ c ∈ gn_I (n' := n') (x = y₁) (x = y₂) (y₁ = y₂),
      glueAtom (n' := n') x y₁ y₂ c.x = glueAtom x y₁ y₂ c.y := by
    intro c hc
    simp only [gn_I, List.mem_append] at hc
    rcases hc with (hc | hc) | hc <;> split_ifs at hc with h <;>
      simp only [List.mem_singleton, List.not_mem_nil] at hc <;> subst hc
    all_goals
      change liftA n' (![x, y₁, y₂] _) = liftA n' (![x, y₁, y₂] _)
      simp [h]
  have hψ : ∀ p q : Atom 3 n', glueAtom x y₁ y₂ p = glueAtom x y₁ y₂ q →
      (dg (gn_I (n' := n') (x = y₁) (x = y₂) (y₁ = y₂))).Reachable p q := by
    intro p q h
    rcases p with e | i <;> rcases q with e' | i'
    · exact gn_I_reach e e' (gn_liftA_inj h)
    · exact absurd h (gn_liftA_ne_newA _ i')
    · exact absurd h.symm (gn_liftA_ne_newA _ i)
    · rw [gn_newA_inj h]
  have hmap := gn_eL_map (glueAtom x y₁ y₂) _ hI hψ g.comps
  rw [gn_eL_perm List.perm_append_comm] at hmap
  have hB : ∀ d ∈ g.comps, d.kind = .dot → d.x ≠ .inl 0 ∧ d.y ≠ .inl 0 := fun d hd hk =>
    ⟨fun h => hgo d hd (Or.inl h) hk, fun h => hgo d hd (Or.inr h) hk⟩
  have htr : ∀ {u v w : Atom 3 m}, u = v → u = w → v = w := fun h1 h2 => h1.symm.trans h2
  have e1 := gn_eL_ext (n' := n') (x = y₁) (x = y₂) (y₁ = y₂) (fun h1 h2 => htr h1 h2)
    (fun h1 h2 => h1.trans h2) (fun h1 h2 => h1.trans h2.symm) g.comps hB
  have e2 := gn_eL_ext (n' := n') (x = y₁) (x = y₂) (y₁ = y₂) (fun h1 h2 => htr h1 h2)
    (fun h1 h2 => h1.trans h2) (fun h1 h2 => h1.trans h2.symm) [] (by simp)
  rw [List.append_nil, gn_eL_of_nodot (L := []) (by simp)] at e2
  have hnil : ¬ (dg ([] : List (Comp (Atom 3 n')))).Reachable (.inl 1) (.inl 2) := by
    rw [gn_dg_eq_bot (by simp), SimpleGraph.reachable_bot]
    simp
  have hge' : eL g.comps = 0 := hge
  have hpm : g.PMBlock ↔ (dg g.comps).Reachable (.inl 1) (.inl 2) :=
    (Graph.pmBlock_iff_sameBlock g).trans Iff.rfl
  rw [h0]
  rw [ite_eq_right (fun h => hnil h.2)] at e2
  rw [hge'] at e1
  by_cases h : y₁ = y₂ ∧ g.PMBlock
  · rw [ite_eq_left ⟨h.1, hpm.1 h.2⟩] at e1
    rw [ite_eq_left h]
    linarith
  · rw [ite_eq_right (fun h' => h ⟨h'.1, hpm.2 h'.2⟩)] at e1
    rw [ite_eq_right h]
    linarith

end GlueDotExcess

/-! ## The branches of `O_dot` on the substituted graph -/

section Branches

variable {k n : ℕ}

private theorem gn_foldl_mem {α : Type*} (F : List α → α → List α)
    (hF : ∀ acc p, F acc p = acc ∨ F acc p = acc ++ [p]) :
    ∀ (l acc : List α) (q : α), q ∈ l.foldl F acc → q ∈ acc ∨ q ∈ l
  | [], _, _, h => Or.inl h
  | p :: l, acc, q, h => by
    rcases gn_foldl_mem F hF l (F acc p) q h with h1 | h1
    · rcases hF acc p with h2 | h2
      · rw [h2] at h1
        exact Or.inl h1
      · rw [h2, List.mem_append, List.mem_singleton] at h1
        rcases h1 with h1 | rfl
        · exact Or.inl h1
        · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- A balanced graph has no pair to split in `O_dot`. -/
private theorem gn_splitPairs_nil {Γ : Graph k n} (hb : GnBal Γ) : Γ.splitPairs = [] := by
  unfold Graph.splitPairs
  dsimp only
  rw [List.filterMap_eq_nil_iff]
  intro p hp
  rcases gn_foldl_mem _ (fun acc q => by split_ifs <;> simp) _ [] p hp with h | h
  · simp at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, hcp⟩ := h
  split_ifs at hcp with hk
  obtain rfl := Option.some.inj hcp
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
  obtain ⟨hk, hne⟩ := hk
  have h1 : spJoined Γ Kind.isSolid c.x c.y = true := by
    rw [spJoined_iff]
    rcases hk with hk | hk
    · exact ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨d, hd, hdk, hde⟩ := hb.2 c hc hk hne
      exact ⟨d, hd, hdk, hde⟩
  have h2 : spJoined Γ (· == .xdot) c.x c.y = true := by
    rw [spJoined_iff]
    rcases hk with hk | hk
    · obtain ⟨d, hd, hdk, hde⟩ := hb.1 c hc hk
      exact ⟨d, hd, by simp [hdk], hde⟩
    · exact ⟨c, hc, by simp [hk], Or.inl ⟨rfl, rfl⟩⟩
  change (if (spJoined Γ Kind.isSolid c.x c.y != spJoined Γ (· == .xdot) c.x c.y) = true then
    some (c.x, c.y, spJoined Γ Kind.isSolid c.x c.y) else none) = none
  rw [h1, h2]
  rfl

private theorem gn_comp_map_id {V : Type*} (c : Comp V) : c.map id = c := by
  obtain ⟨κ, u, v, T, ℓ⟩ := c
  simp [Comp.map]

/-- The identity is an output of `O_merge` that removes every dotted edge on a graph without
dotted edges and without solid loops. -/
private theorem gn_out_self {Γ : Graph k n} (hdf : Γ.DotFree)
    (hsl : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) : GnOut Γ (Tracked.self Γ) := by
  refine ⟨?_, le_refl _, fun _ => rfl, ⟨id, fun _ => rfl, Function.surjective_id⟩,
    fun c hc hk => absurd hk (hdf c hc), hsl⟩
  change Γ.comps = _
  conv_lhs => rw [← List.filterMap_some (l := Γ.comps)]
  apply List.filterMap_congr
  intro c hc
  change some c = if c.kind = .dot then none else some (c.map id)
  rw [ite_eq_right (hdf c hc), gn_comp_map_id]

/-- On a balanced graph whose dotted edges join internal atoms, `O_merge` of the term of
`dotChoice` without pairs removes every dotted edge and keeps every solid edge, and the scaling
order drops by twice the dot excess. -/
private theorem gn_out_merge {Γ : Graph k n} (hb : GnBal Γ)
    (hdots : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    {t : Tracked k n} (hm : (Γ.dotChoice [] []).mergeT = some t) :
    GnOut Γ t ∧ t.g.ord = Γ.ord - 2 * Γ.dotExcess := by
  have hc : (Γ.dotChoice [] []).comps = Γ.comps := by simp [Graph.dotChoice]
  have hs := mergeT_spec hm
  have hrep : (Γ.dotChoice [] []).mrep = Γ.mrep := by
    unfold Graph.mrep
    rw [hc]
  have hsol : ∀ c ∈ Γ.comps, c.kind.isSolid = true → Γ.mrep c.x ≠ Γ.mrep c.y := by
    intro c hc' hk heq
    obtain ⟨d, hd, hdk, hde⟩ := hb.1 c hc' hk
    apply hs.xdot_ne d (by rw [hc]; exact hd) hdk
    rw [hrep]
    rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact heq
    · exact heq.symm
  have hdot : ∀ c ∈ Γ.comps, c.kind = .dot → t.f c.x = t.f c.y := by
    intro c hc' hk
    obtain ⟨h1, h2⟩ := hdots c hc' hk
    exact hs.f_eq _ _ (by rw [hrep]; exact gn_mrep_dot Γ hc' hk) h1 h2
  have hout : GnOut Γ t := by
    refine ⟨?_, hs.nOut_le, hs.f_inl, hs.f_inr, hdot,
      fun c hc' hk => hs.f_ne _ _ (by rw [hrep]; exact hsol c hc' hk)⟩
    rw [hs.comps_eq, hc, hrep]
    apply List.filterMap_congr
    intro c hc'
    by_cases hd : c.kind = .dot
    · rw [mergeComp_dot hd, ite_eq_left (hdot c hc' hd), ite_eq_left hd]
    · by_cases hk : c.kind.isSolid = true
      · rw [mergeComp_solid hk, ite_eq_right (hsol c hc' hk), ite_eq_right hd]
      · have hk' : c.kind.isSolid = false := by simpa using hk
        unfold mergeComp
        simp [hd, hk']
  refine ⟨hout, ?_⟩
  have hobl := hs.obl_eq
  have hconv : convN (Γ.dotChoice [] []) = 0 := by
    unfold convN
    rw [hc, hrep, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc' h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact hsol c hc' h.1 h.2
  have hobl' : (Γ.dotChoice [] []).obl = Γ.obl := by
    unfold Graph.obl Graph.ord Graph.dotExcess Graph.nDots Graph.dotGraph
    rw [hc]
  rw [hconv, hobl'] at hobl
  have ht0 := hout.dotExcess
  unfold Graph.obl at hobl
  rw [ht0] at hobl
  push_cast at hobl
  linarith

end Branches

section Main

variable {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m} {g : Graph 3 n'}

/-- The substituted graph is not in the first case of `O_dot`. -/
private theorem gn_glue_branch1 (hH : H.LabelFree) (hgl : g.labels.length ≤ 1)
    (hgn : g.NoLabDot) :
    ¬ (2 ≤ (H.glue x y₁ y₂ g).labels.length ∨
      ((H.glue x y₁ y₂ g).comps.any fun c =>
        (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true) := by
  rintro (h | h)
  · have hsub : ((H.glue x y₁ y₂ g).comps.filterMap Comp.label).toFinset ⊆
        (g.comps.filterMap Comp.label).toFinset.image (Prod.map id (glueAtom x y₁ y₂)) := by
      intro ℓ hℓ
      rw [List.mem_toFinset, List.mem_filterMap] at hℓ
      obtain ⟨c, hc, hcl⟩ := hℓ
      rcases gn_mem_glue.1 hc with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
      · change d.label.map _ = _ at hcl
        rw [hH d hd] at hcl
        cases hcl
      · change d.label.map _ = _ at hcl
        obtain ⟨ℓ', hℓ', rfl⟩ := Option.map_eq_some_iff.1 hcl
        exact Finset.mem_image.2 ⟨ℓ', List.mem_toFinset.2 (List.mem_filterMap.2 ⟨d, hd, hℓ'⟩),
          rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (g.comps.filterMap Comp.label).toFinset)
      (f := Prod.map id (glueAtom x y₁ y₂))
    rw [List.card_toFinset] at h1 h2
    have : (H.glue x y₁ y₂ g).labels.length ≤ g.labels.length := h1.trans h2
    unfold Graph.labels at this hgl h
    omega
  · rw [List.any_eq_true] at h
    obtain ⟨c, hc, hb⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hb
    rcases gn_mem_glue.1 hc with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · obtain ⟨-, hb⟩ := hb
      change (d.label.map _).isSome = true at hb
      rw [hH d hd] at hb
      simp at hb
    · obtain ⟨hk, hb⟩ := hb
      change (d.label.map _).isSome = true at hb
      rw [hgn d hd hk] at hb
      simp at hb

/-- **The `O_dot` forms of a substituted graph** ([II, Lemma 6.5], [II, (2.5)],
[II, Defs 4.1–4.2]): with `H.glue x y₁ y₂ (tVar true)` normal regular without dotted edges, `x`,
`y₁`, `y₂` internal and `H` without labels, and `g` normal regular with no dotted edge at `⊗`, dot
excess `0`, the clause `Graph.RgCheck`, at most one label and no labelled dotted or `×`-dotted
edge, every `O_dot` form of `H.glue x y₁ y₂ g` is normal regular without dotted edges, of the
scaling order of `H.glue x y₁ y₂ g` minus `2` if `y₁ = y₂` and `⊕`, `⊖` lie in one block of `g`
and of the same scaling order otherwise, and doubly connected if `H.glue x y₁ y₂ g` is. -/
theorem glue_oDotT_normal : glue_oDotT_normalStmt := by
  intro m n' C C' H x y₁ y₂ g hx hy₁ hy₂ hH hG hGd hg hgo hge hgr hgl hgn t ht
  have hb := gn_glue_bal hG hg
  have hdots := gn_glue_dot (g := g) hx hy₁ hy₂ hGd
  have hconn := gn_glue_conn hG hg
  have hw := gn_glue_wtd hx hy₁ hy₂ hG hg hgr
  have hex := gn_glue_dotExcess hGd hgo hge
  have hsp := gn_splitPairs_nil hb
  have hb1 := gn_glue_branch1 (x := x) (y₁ := y₁) (y₂ := y₂) hH hgl hgn
  obtain ⟨hout, hord⟩ : GnOut (H.glue x y₁ y₂ g) t ∧
      t.g.ord = (H.glue x y₁ y₂ g).ord - 2 * (H.glue x y₁ y₂ g).dotExcess := by
    unfold oDotT at ht
    dsimp only at ht
    rw [ite_eq_right hb1] at ht
    split_ifs at ht with h2
    · obtain rfl := List.mem_singleton.1 ht
      have h2' := (Bool.and_eq_true_iff.1 h2).2
      rw [Bool.not_eq_true', List.any_eq_false] at h2'
      have hdf : (H.glue x y₁ y₂ g).DotFree := fun c hc hk =>
        h2' c hc (by simp [hk, (hdots c hc hk).1, (hdots c hc hk).2])
      have hsl : ∀ c ∈ (H.glue x y₁ y₂ g).comps, c.kind.isSolid = true → c.x ≠ c.y :=
        fun c hc hk heq => h2' c hc (by simp [hk, heq])
      refine ⟨gn_out_self hdf hsl, ?_⟩
      change _ = _ - 2 * eL _
      rw [gn_eL_of_nodot hdf, mul_zero, sub_zero]
      rfl
    · rw [hsp, List.sublists_nil] at ht
      simp only [List.filterMap_cons, List.filterMap_nil] at ht
      split at ht
      · simp at ht
      · rename_i t' ht'
        obtain rfl := List.mem_singleton.1 ht
        exact gn_out_merge hb hdots ht'
  refine ⟨⟨_, hout.normal hb hconn hw⟩, hout.dotFree, fun h => ?_, fun h => ?_,
    hout.doublyConnected⟩
  · rw [hex, ite_eq_left h] at hord
    linarith
  · rw [hex, ite_eq_right h] at hord
    linarith

end Main

/-! ## Two substituted graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance gn_decAdjMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.molGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = v ∧ c.y = u))))

private instance gn_decSameMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameMol :=
  fun u v =>
    haveI : Decidable (Γ.molGraph.Reachable u v) :=
      @SimpleGraph.instDecidableRelReachable _ _ _ _ (gn_decAdjMol Γ) u v
    inferInstanceAs (Decidable (u = v ∨
      (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)))

private instance gn_decAdjNet {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) :
    DecidableRel (Γ.net B).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧
    ((Γ.SameMol (.inr a) (.inr b) ∨ ∃ i ∈ B, Γ.comps[i].x = .inr a ∧ Γ.comps[i].y = .inr b) ∨
      (Γ.SameMol (.inr b) (.inr a) ∨ ∃ i ∈ B, Γ.comps[i].x = .inr b ∧ Γ.comps[i].y = .inr a))))

private instance gn_decSpans {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) :
    Decidable (Γ.Spans B) :=
  haveI : DecidableRel (Γ.net B).Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (gn_decAdjNet Γ B)
  inferInstanceAs (Decidable (∀ a b, (Γ.net B).Reachable a b))

private instance gn_decLabelFree {k n : ℕ} (Γ : Graph k n) : Decidable Γ.LabelFree :=
  inferInstanceAs (Decidable (∀ c ∈ Γ.comps, c.label = none))

private instance gn_decOtimesNoDot {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.OtimesNoDot := by
  unfold Graph.OtimesNoDot; infer_instance

private instance gn_decNoLabDot {k n : ℕ} (Γ : Graph k n) : Decidable Γ.NoLabDot := by
  unfold Graph.NoLabDot; infer_instance

private instance gn_decRgCheck {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.RgCheck := by
  unfold Graph.RgCheck; infer_instance

end Instances

end RBM8D.Graphs
