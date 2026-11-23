module

public import RBM8D.Graph.Local.Weight
public import RBM8D.Graph.Local.Transposed

@[expose] public section

/-!
# The local expansion strategy, first part

The first half of the file `RBM8D/Graph/Local/Strategy.lean`, which continues it: the operations
`O_merge` and `O_dot`, the quantities of the descent, and the terms of the local operations.

The elementary steps of [I, Strategy 3.21] and [I, Lemma 3.22] = [II, Lemma 4.9], with the `GG`
expansion in the form whose waved edge in the main term joins `x` to an internal atom.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- One elementary step of [I, Strategy 3.21]: the second graph is a term of one of the following
operations applied to the first.
* `dot`: `O_dot` ([I, Def 3.2]).
* `dropDot`: removal of a dotted edge whose ends are joined by the other dotted edges (a dotted
  loop included).
* `weight`, `multiE`, `ggbar`: `O_weight`, `O_multi-e`, `O_GḠ` at an internal atom.
* `gg`: `O_GG` in the form of [II, (4.10)] at an internal atom whose outgoing solid edges end at
  internal atoms.
* `ggT`: the transposed `O_GG` at an internal atom whose incoming solid edges start at internal
  atoms. -/
inductive LocElemStep {k : ℕ} : (Σ n, Graph k n) → (Σ n, Graph k n) → Prop
  | dot {n : ℕ} (Γ : Graph k n) (t : Tracked k n) (ht : t ∈ oDotT Γ) :
      LocElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | dropDot {n : ℕ} (i : ℕ) (Γ : Graph k n) (c : Comp (Atom k n)) (hc : Γ.comps[i]? = some c)
      (hk : c.kind = .dot)
      (hb : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).SameBlock c.x c.y) :
      LocElemStep ⟨n, Γ⟩ ⟨n, ⟨Γ.comps.eraseIdx i, Γ.coeff⟩⟩
  | weight {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hx : x.isRight = true)
      (ht : t ∈ oWeightT x Γ) : LocElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | multiE {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hx : x.isRight = true)
      (ht : t ∈ oMultiET x Γ) : LocElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | gg {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hx : x.isRight = true)
      (hout : Γ.GGOutInt x) (ht : t ∈ oGGT x Γ) : LocElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | ggT {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hx : x.isRight = true)
      (hin : Γ.GGInInt x) (ht : t ∈ oGGTT x Γ) : LocElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | ggbar {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hx : x.isRight = true)
      (ht : t ∈ oGGbarT x Γ) : LocElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩

/-! ## Connected components of simple graphs -/

section GraphCard

variable {V W : Type*}

/-- Reachability in a graph with one more edge `u v`. -/
private theorem reach_add_edge_iff {G H : SimpleGraph V} {u v : V}
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
private theorem card_cc_add_edge [Finite V] {G H : SimpleGraph V} {u v : V}
    (hadj : ∀ a b, H.Adj a b ↔ G.Adj a b ∨ (a ≠ b ∧ (a = u ∧ b = v ∨ a = v ∧ b = u)))
    (huv : ¬ G.Reachable u v) :
    Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent + 1 := by
  classical
  have hR := reach_add_edge_iff hadj
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

/-- A surjective map of the vertices that reflects and preserves reachability gives a bijection
of the connected components. -/
private theorem card_cc_of_map [Finite V] {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W)
    (hf : Function.Surjective f) (hr : ∀ a b, H.Reachable (f a) (f b) ↔ G.Reachable a b) :
    Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent := by
  let φ : G.ConnectedComponent → H.ConnectedComponent :=
    Quot.lift (fun a => H.connectedComponentMk (f a)) fun a b h =>
      SimpleGraph.ConnectedComponent.sound ((hr a b).2 h)
  have hφ : Function.Bijective φ := by
    constructor
    · intro c₁ c₂ h
      induction c₁ using SimpleGraph.ConnectedComponent.ind with | h a =>
      induction c₂ using SimpleGraph.ConnectedComponent.ind with | h b =>
      have h' : H.connectedComponentMk (f a) = H.connectedComponentMk (f b) := h
      rw [SimpleGraph.ConnectedComponent.eq] at h' ⊢
      exact (hr a b).1 h'
    · intro d
      induction d using SimpleGraph.ConnectedComponent.ind with | h w =>
      obtain ⟨a, rfl⟩ := hf w
      exact ⟨G.connectedComponentMk a, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective φ hφ)

/-- Two graphs with the same reachability have the same number of connected components. -/
private theorem card_cc_of_reach_iff [Finite V] {G H : SimpleGraph V}
    (hr : ∀ a b, H.Reachable a b ↔ G.Reachable a b) :
    Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent :=
  card_cc_of_map id Function.surjective_id hr

/-- A map onto `W` constant on the connected components bounds `Nat.card W`. -/
private theorem card_le_card_cc [Finite V] {G : SimpleGraph V} (f : V → W)
    (hf : Function.Surjective f) (hc : ∀ a b, G.Reachable a b → f a = f b) :
    Nat.card W ≤ Nat.card G.ConnectedComponent := by
  let φ : G.ConnectedComponent → W := Quot.lift f fun a b h => hc a b h
  refine Nat.card_le_card_of_surjective φ ?_
  intro w
  obtain ⟨a, rfl⟩ := hf w
  exact ⟨G.connectedComponentMk a, rfl⟩

/-- The graph without edges has one connected component per vertex. -/
private theorem card_cc_bot [Finite V] :
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

/-! ## Dotted components of a list -/

section Dots

variable {k n : ℕ}

/-- The graph on the atoms whose edges are the dotted components of a list. -/
def dg (L : List (Comp (Atom k n))) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ L, c.kind = .dot ∧ c.x = u ∧ c.y = v

/-- The number of dotted components of a list. -/
def nD (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => decide (c.kind = .dot)).length

/-- The dot excess of a list of components. -/
def eL (L : List (Comp (Atom k n))) : ℤ :=
  (nD L : ℤ) - ((k + n : ℕ) : ℤ) + (Nat.card (dg L).ConnectedComponent : ℤ)

theorem dg_adj {L : List (Comp (Atom k n))} {a b : Atom k n} :
    (dg L).Adj a b ↔ a ≠ b ∧ ∃ c ∈ L, c.kind = .dot ∧ (c.x = a ∧ c.y = b ∨ c.x = b ∧ c.y = a) := by
  simp only [dg, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact ⟨h, c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨h, c, hc, hk, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨h, c, hc, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact ⟨h, Or.inr ⟨c, hc, hk, rfl, rfl⟩⟩

/-- The ends of a dotted component are reachable. -/
theorem dg_reach_of_mem {L : List (Comp (Atom k n))} {c : Comp (Atom k n)} (hc : c ∈ L)
    (hk : c.kind = .dot) : (dg L).Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (dg_adj.2 ⟨h, c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩).reachable

/-- Reachability in the graph of dotted components is monotone in the dotted components. -/
private theorem dg_reach_mono {L L' : List (Comp (Atom k n))}
    (h : ∀ c ∈ L, c.kind = .dot → c ∈ L') {a b : Atom k n} (hr : (dg L).Reachable a b) :
    (dg L').Reachable a b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨hne, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    refine SimpleGraph.Reachable.trans ?_ ih
    exact (dg_adj.2 ⟨hne, c, h c hc hk, hk, hxy⟩).reachable

/-- The graph of dotted components depends only on the dotted components. -/
private theorem dg_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ c, c.kind = .dot → (c ∈ L ↔ c ∈ L')) : dg L = dg L' := by
  ext a b
  rw [dg_adj, dg_adj]
  constructor
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).1 hc, hk, hxy⟩
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).2 hc, hk, hxy⟩

private theorem dg_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : dg L = dg L' :=
  dg_congr fun _ _ => h.mem_iff

theorem nD_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : nD L = nD L' :=
  (h.filter _).length_eq

private theorem eL_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : eL L = eL L' := by
  simp only [eL, nD_perm h, dg_perm h]

/-- Two lists with the same dotted components, with multiplicity, have the same graph of dotted
components and the same dot excess. -/
private theorem dg_eL_of_filter_perm {L L' : List (Comp (Atom k n))}
    (h : (L.filter fun c => decide (c.kind = .dot)).Perm
      (L'.filter fun c => decide (c.kind = .dot))) :
    dg L = dg L' ∧ eL L = eL L' := by
  have hg : dg L = dg L' := by
    apply dg_congr
    intro c hk
    have := h.mem_iff (a := c)
    simp only [List.mem_filter, hk, decide_true, and_true] at this
    exact this
  refine ⟨hg, ?_⟩
  simp only [eL, nD, h.length_eq, hg]

private theorem dg_nil : dg ([] : List (Comp (Atom k n))) = ⊥ := by
  ext a b
  simp [dg_adj]

private theorem dg_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : dg (c :: L) = dg L := by
  apply dg_congr
  intro d hd
  simp only [List.mem_cons]
  constructor
  · rintro (rfl | h)
    · exact absurd hd hk
    · exact h
  · exact Or.inr

private theorem dg_cons_dot_adj {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
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

theorem nD_cons (c : Comp (Atom k n)) (L : List (Comp (Atom k n))) :
    nD (c :: L) = nD L + if c.kind = .dot then 1 else 0 := by
  unfold nD
  by_cases h : c.kind = .dot
  · rw [List.filter_cons_of_pos (by simp [h])]
    simp [h]
  · rw [List.filter_cons_of_neg (by simp [h])]
    simp [h]

private theorem eL_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : eL (c :: L) = eL L := by
  simp [eL, nD_cons, hk, dg_cons_nondot L hk]

/-- A dotted component between two blocks keeps the dot excess. -/
private theorem eL_cons_dot_new {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : ¬ (dg L).Reachable c.x c.y) : eL (c :: L) = eL L := by
  have h := card_cc_add_edge (G := dg L) (H := dg (c :: L)) (dg_cons_dot_adj L hk) hr
  simp only [eL, nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- Reachability is unchanged by a dotted component whose ends are reachable. -/
private theorem dg_reach_cons_red {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : (dg L).Reachable c.x c.y) (a b : Atom k n) :
    (dg (c :: L)).Reachable a b ↔ (dg L).Reachable a b := by
  rw [reach_add_edge_iff (dg_cons_dot_adj L hk)]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h
    · exact (h1.trans hr).trans h2
    · exact (h1.trans hr.symm).trans h2
  · exact Or.inl

/-- A dotted component whose ends are already in one block raises the dot excess by `1`. -/
private theorem eL_cons_dot_red {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : (dg L).Reachable c.x c.y) : eL (c :: L) = eL L + 1 := by
  have h := card_cc_of_reach_iff (G := dg L) (H := dg (c :: L)) (dg_reach_cons_red L hk hr)
  simp only [eL, nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- Every dotted component is needed: its ends are not joined by the other dotted components. -/
def NonRed (L : List (Comp (Atom k n))) : Prop :=
  ∀ (c : Comp (Atom k n)) (L' : List (Comp (Atom k n))), L.Perm (c :: L') → c.kind = .dot →
    ¬ (dg L').Reachable c.x c.y

private theorem nonRed_tail {c : Comp (Atom k n)} {L : List (Comp (Atom k n))}
    (h : NonRed (c :: L)) : NonRed L := by
  intro d L' hp hk hr
  apply h d (c :: L') ((hp.cons c).trans (List.Perm.swap d c L')) hk
  exact dg_reach_mono (fun e he _ => List.mem_cons_of_mem _ he) hr

private theorem card_atom : Nat.card (Atom k n) = k + n := by
  simp

/-- When every dotted component is needed, the dot excess is `0`. -/
theorem eL_eq_zero_of_nonRed : ∀ {L : List (Comp (Atom k n))}, NonRed L → eL L = 0
  | [], _ => by
    simp only [eL, nD, List.filter_nil, List.length_nil, dg_nil, card_cc_bot, card_atom]
    push_cast
    ring
  | c :: L, h => by
    have ih := eL_eq_zero_of_nonRed (nonRed_tail h)
    by_cases hk : c.kind = .dot
    · rw [eL_cons_dot_new L hk (h c L (List.Perm.refl _) hk), ih]
    · rw [eL_cons_nondot L hk, ih]

/-- A list with positive dot excess has a dotted component whose ends are joined by the others. -/
theorem exists_red_of_pos {L : List (Comp (Atom k n))} (h : 0 < eL L) :
    ∃ (i : ℕ) (c : Comp (Atom k n)), L[i]? = some c ∧ c.kind = .dot ∧
      (dg (L.eraseIdx i)).Reachable c.x c.y := by
  by_contra hc
  push Not at hc
  have hn : NonRed L := by
    intro c L' hp hk hr
    have hcL : c ∈ L := hp.symm.subset (List.mem_cons_self ..)
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.1 hcL
    have hp' : (L.eraseIdx i).Perm L' := by
      have h1 := List.getElem_cons_eraseIdx_perm hi
      rw [hci] at h1
      exact (h1.trans hp).cons_inv
    exact hc i c (by rw [List.getElem?_eq_getElem hi, hci]) hk (by rw [dg_perm hp']; exact hr)
  have := eL_eq_zero_of_nonRed hn
  omega

/-- Removing a dotted component whose ends are joined by the others lowers the dot excess by
`1` and keeps the blocks. -/
private theorem eL_eraseIdx_red {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) (hk : c.kind = .dot) (hr : (dg (L.eraseIdx i)).Reachable c.x c.y) :
    eL (L.eraseIdx i) + 1 = eL L ∧
      ∀ a b, (dg (L.eraseIdx i)).Reachable a b ↔ (dg L).Reachable a b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  have hp := List.getElem_cons_eraseIdx_perm hi
  refine ⟨?_, fun a b => ?_⟩
  · rw [← eL_perm hp, eL_cons_dot_red _ hk hr]
  · rw [← dg_perm hp, dg_reach_cons_red _ hk hr]

/-- The dot excess is never negative. -/
theorem eL_nonneg : ∀ (L : List (Comp (Atom k n))), 0 ≤ eL L := by
  intro L
  induction h : L.length generalizing L with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 h
    simp only [eL, nD, List.filter_nil, List.length_nil, dg_nil, card_cc_bot, card_atom]
    push_cast
    ring_nf
    rfl
  | succ m ih =>
    by_cases hn : NonRed L
    · rw [eL_eq_zero_of_nonRed hn]
    · simp only [NonRed, not_forall, not_not] at hn
      obtain ⟨c, L', hp, hk, hr⟩ := hn
      have h1 : eL L = eL L' + 1 := by rw [eL_perm hp, eL_cons_dot_red _ hk hr]
      have h2 := ih L' (by have := hp.length_eq; simp at this; omega)
      omega

/-- A labelling that agrees on the ends of every dotted component agrees along paths of dotted
components. -/
private theorem sigma_eq_of_reach {ι : Type*} {L : List (Comp (Atom k n))} (σ : Atom k n → ι)
    (hz : ∀ c ∈ L, c.kind = .dot → σ c.x = σ c.y) {a b : Atom k n}
    (hr : (dg L).Reachable a b) : σ a = σ b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := dg_adj.1 hadj
    · exact (hz c hc hk).trans ih
    · exact (hz c hc hk).symm.trans ih

end Dots

/-! ## The merging operation -/

section Blocks

variable {V : Type*} [DecidableEq V]

/-- The relation "joined by a dotted component". -/
private def dotRel (cs : List (Comp V)) : V → V → Prop :=
  fun u v => ∃ c ∈ cs, c.kind = .dot ∧ c.x = u ∧ c.y = v

omit [DecidableEq V] in
private theorem dotRel_mono {cs cs' : List (Comp V)} (h : ∀ c ∈ cs, c ∈ cs') :
    dotRel cs ≤ dotRel cs' := by
  rintro u v ⟨c, hc, hk, hx, hy⟩
  exact ⟨c, h c hc, hk, hx, hy⟩

omit [DecidableEq V] in
private theorem flatten_map_singleton' (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private theorem joinBlocks_flatten_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

/-- One step of `dotBlocks`. -/
private def blockStep (c : Comp V) (P : List (List V)) : List (List V) :=
  if c.kind = .dot then joinBlocks P c.x c.y else P

private theorem dotBlocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) = blockStep c (dotBlocks as cs) := by
  simp [dotBlocks, List.foldl_append, blockStep]

private theorem dotBlocks_nil (as : List V) : dotBlocks as ([] : List (Comp V)) =
    as.map fun a => [a] := rfl

private theorem dotBlocks_flatten_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  induction cs using List.reverseRecOn with
  | nil => rw [dotBlocks_nil, flatten_map_singleton']
  | append_singleton cs c ih =>
    rw [dotBlocks_snoc, blockStep]
    split_ifs
    · exact (joinBlocks_flatten_perm _ _ _).trans ih
    · exact ih

private theorem dotBlocks_conn (as : List V) (cs : List (Comp V)) :
    ∀ B ∈ dotBlocks as cs, ∀ u ∈ B, ∀ v ∈ B, Relation.EqvGen (dotRel cs) u v := by
  induction cs using List.reverseRecOn with
  | nil =>
    intro B hB u hu v hv
    rw [dotBlocks_nil, List.mem_map] at hB
    obtain ⟨a, -, rfl⟩ := hB
    simp only [List.mem_singleton] at hu hv
    subst hu; subst hv
    exact Relation.EqvGen.refl _
  | append_singleton cs c ih =>
    have hmono : ∀ u v, Relation.EqvGen (dotRel cs) u v →
        Relation.EqvGen (dotRel (cs ++ [c])) u v := fun u v h =>
      Relation.EqvGen.mono (dotRel_mono fun c' hc' => List.mem_append_left _ hc') u v h
    intro B hB u hu v hv
    rw [dotBlocks_snoc, blockStep] at hB
    split_ifs at hB with hk
    · unfold joinBlocks at hB
      rw [List.mem_append] at hB
      rcases hB with hB | hB
      · exact hmono _ _ (ih B (List.mem_of_mem_filter hB) u hu v hv)
      · rw [List.mem_singleton] at hB
        subst hB
        have hxy : Relation.EqvGen (dotRel (cs ++ [c])) c.x c.y :=
          Relation.EqvGen.rel _ _ ⟨c, List.mem_append_right _ (List.mem_singleton_self _), hk, rfl,
            rfl⟩
        -- every element of the joined block is connected to `c.x` by dotted edges
        have key : ∀ w ∈ (dotBlocks as cs).filter (fun B => B.contains c.x || B.contains c.y),
            ∀ z ∈ w, Relation.EqvGen (dotRel (cs ++ [c])) z c.x := by
          intro w hw z hz
          have hw' := List.mem_filter.1 hw
          have hcont := hw'.2
          simp only [Bool.or_eq_true, List.contains_iff_mem] at hcont
          rcases hcont with hx | hy
          · exact hmono _ _ (ih w hw'.1 z hz _ hx)
          · exact (hmono _ _ (ih w hw'.1 z hz _ hy)).trans _ _ _ hxy.symm
        rw [List.mem_flatten] at hu hv
        obtain ⟨w₁, hw₁, hu⟩ := hu
        obtain ⟨w₂, hw₂, hv⟩ := hv
        exact (key w₁ hw₁ u hu).trans _ _ _ (key w₂ hw₂ v hv).symm
    · exact hmono _ _ (ih B hB u hu v hv)

private theorem dotBlocks_joined (as : List V) (cs : List (Comp V))
    (hcs : ∀ c ∈ cs, c.x ∈ as ∧ c.y ∈ as) :
    ∀ c ∈ cs, c.kind = .dot → ∃ B ∈ dotBlocks as cs, c.x ∈ B ∧ c.y ∈ B := by
  induction cs using List.reverseRecOn with
  | nil => intro c hc; simp at hc
  | append_singleton cs c ih =>
    have ih' := ih fun c' hc' => hcs c' (List.mem_append_left _ hc')
    intro c' hc' hk'
    rw [dotBlocks_snoc, blockStep]
    -- membership of an atom of `as` in some block
    have hmem : ∀ a ∈ as, ∃ B ∈ dotBlocks as cs, a ∈ B := by
      intro a ha
      have := (dotBlocks_flatten_perm as cs).mem_iff.2 ha
      rwa [List.mem_flatten] at this
    split_ifs with hk
    · rcases List.mem_append.1 hc' with hc' | hc'
      · obtain ⟨B, hB, hx, hy⟩ := ih' c' hc' hk'
        by_cases hcB : (B.contains c.x || B.contains c.y) = true
        · refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c.x || B.contains c.y).flatten,
            ?_, ?_, ?_⟩
          · unfold joinBlocks
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hx⟩
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hy⟩
        · refine ⟨B, ?_, hx, hy⟩
          unfold joinBlocks
          refine List.mem_append_left _ (List.mem_filter.2 ⟨hB, ?_⟩)
          simpa using hcB
      · rw [List.mem_singleton] at hc'
        subst hc'
        obtain ⟨hxa, hya⟩ := hcs _ (List.mem_append_right _ (List.mem_singleton_self _))
        obtain ⟨B₁, hB₁, hx⟩ := hmem _ hxa
        obtain ⟨B₂, hB₂, hy⟩ := hmem _ hya
        refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c'.x || B.contains c'.y).flatten,
          ?_, ?_, ?_⟩
        · unfold joinBlocks
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [List.mem_flatten]
          exact ⟨B₁, List.mem_filter.2 ⟨hB₁, by simp [hx]⟩, hx⟩
        · rw [List.mem_flatten]
          exact ⟨B₂, List.mem_filter.2 ⟨hB₂, by simp [hy]⟩, hy⟩
    · rcases List.mem_append.1 hc' with hc' | hc'
      · exact ih' c' hc' hk'
      · rw [List.mem_singleton] at hc'
        subst hc'
        exact absurd hk' hk

/-- Two atoms of one block of a partition have the same representative. -/
private theorem blockRep_eq_of_mem {P : List (List V)} (hnd : P.flatten.Nodup) {B : List V}
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

private theorem blockRep_spec (P : List (List V)) (u : V) :
    blockRep P u = u ∨ ∃ B ∈ P, u ∈ B ∧ blockRep P u ∈ B := by
  unfold blockRep
  generalize hf : P.find? (fun B => B.contains u) = o
  rcases o with _ | ⟨_ | ⟨r, rest⟩⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · right
    refine ⟨r :: rest, List.mem_of_find?_eq_some hf, ?_, List.mem_cons_self ..⟩
    simpa [List.contains_iff_mem] using List.find?_some hf

end Blocks

/-! ## The data of `O_merge` -/

section MergeData

variable {k n : ℕ}

private theorem mem_allAtoms (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | i <;> simp [allAtoms]

private theorem allAtoms_nodup : (allAtoms k n).Nodup := by
  unfold allAtoms
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange k).map Sum.inl_injective,
    (List.nodup_finRange n).map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  simp at hab

/-- The representative of an atom in the dot blocks of a graph. -/
def Graph.mrep (Γ : Graph k n) : Atom k n → Atom k n :=
  blockRep (dotBlocks (allAtoms k n) Γ.comps)

private theorem Graph.mrep_dot (Γ : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : Γ.mrep c.x = Γ.mrep c.y := by
  obtain ⟨B, hB, hx, hy⟩ := dotBlocks_joined (allAtoms k n) Γ.comps
    (fun c _ => ⟨mem_allAtoms _, mem_allAtoms _⟩) c hc hk
  have hnd : (dotBlocks (allAtoms k n) Γ.comps).flatten.Nodup :=
    (dotBlocks_flatten_perm _ _).nodup_iff.2 allAtoms_nodup
  exact blockRep_eq_of_mem hnd hB hx hy

private theorem Graph.mrep_conn (Γ : Graph k n) (u : Atom k n) :
    Relation.EqvGen (dotRel Γ.comps) u (Γ.mrep u) := by
  rcases blockRep_spec (dotBlocks (allAtoms k n) Γ.comps) u with h | ⟨B, hB, hu, hr⟩
  · have : Γ.mrep u = u := h
    rw [this]
    exact Relation.EqvGen.refl _
  · exact dotBlocks_conn _ _ B hB u hu _ hr

/-- The roots: the representatives of the internal atoms, without repetition. -/
private def Graph.mroots (Γ : Graph k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => Γ.mrep (Sum.inr i)).dedup

private theorem Graph.mem_mroots (Γ : Graph k n) (i : Fin n) : Γ.mrep (.inr i) ∈ Γ.mroots :=
  List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

/-- The new internal atom of an internal atom: the position of its root. -/
private def Graph.midx (Γ : Graph k n) (i : Fin n) : Fin Γ.mroots.length :=
  ⟨Γ.mroots.idxOf (Γ.mrep (.inr i)), List.idxOf_lt_length_of_mem (Γ.mem_mroots i)⟩

/-- The atom map of `O_merge`. -/
private def Graph.mmap (Γ : Graph k n) : Atom k n → Atom k Γ.mroots.length :=
  fun u => match u with
    | .inl a => .inl a
    | .inr i => .inr (Γ.midx i)

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
def mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

private theorem mergeT_eq (Γ : Graph k n) : Γ.mergeT =
    if Γ.comps.any (fun c => c.kind == .xdot && Γ.mrep c.x == Γ.mrep c.y) then none else
    some ⟨Γ.mroots.length, ⟨Γ.comps.filterMap (mergeComp Γ.mrep Γ.mmap), Γ.coeff⟩, Γ.mmap⟩ := rfl

/-- The structure of a tracked graph `t` with `Γ.mergeT = some t`: its components, its atom map
and its blocks. -/
structure MergeSpec (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps = Γ.comps.filterMap (mergeComp Γ.mrep t.f)
  coeff_eq : t.g.coeff = Γ.coeff
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_surj : Function.Surjective t.f
  f_inr : ∃ g : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (g i)) ∧ Function.Surjective g
  f_eq : ∀ u v, Γ.mrep u = Γ.mrep v → u.isRight = true → v.isRight = true → t.f u = t.f v
  f_ne : ∀ u v, Γ.mrep u ≠ Γ.mrep v → t.f u ≠ t.f v
  xdot_ne : ∀ c ∈ Γ.comps, c.kind = .xdot → Γ.mrep c.x ≠ Γ.mrep c.y

theorem mergeT_spec {Γ : Graph k n} {t : Tracked k n} (h : Γ.mergeT = some t) :
    MergeSpec Γ t := by
  rw [mergeT_eq] at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have hsurj : Function.Surjective Γ.midx := by
    intro j
    have hj : Γ.mroots[j.1] ∈ Γ.mroots := List.getElem_mem j.2
    obtain ⟨i, -, hi⟩ := List.mem_map.1 (List.mem_dedup.1 hj)
    refine ⟨i, Fin.ext ?_⟩
    simp only [Graph.midx]
    rw [hi]
    exact (List.nodup_dedup _).idxOf_getElem j.1 j.2
  refine ⟨rfl, rfl, ?_, fun a => rfl, ?_, ⟨Γ.midx, fun i => rfl, hsurj⟩, ?_, ?_, ?_⟩
  · exact (List.dedup_sublist _).length_le.trans (by simp)
  · intro u'
    rcases u' with a | j
    · exact ⟨.inl a, rfl⟩
    · obtain ⟨i, hi⟩ := hsurj j
      exact ⟨.inr i, by simp [Graph.mmap, hi]⟩
  · intro u v huv hu hv
    rcases u with a | i
    · simp at hu
    rcases v with b | j
    · simp at hv
    have : Γ.midx i = Γ.midx j := Fin.ext (by
      change Γ.mroots.idxOf (Γ.mrep (.inr i)) = Γ.mroots.idxOf (Γ.mrep (.inr j))
      rw [huv])
    simp [Graph.mmap, this]
  · intro u v huv hf
    rcases u with a | i <;> rcases v with b | j
    · simp only [Graph.mmap, Sum.inl.injEq] at hf
      exact huv (by rw [hf])
    · simp [Graph.mmap] at hf
    · simp [Graph.mmap] at hf
    · simp only [Graph.mmap, Sum.inr.injEq] at hf
      have h2 := congrArg Fin.val hf
      simp only [Graph.midx] at h2
      exact huv ((List.idxOf_inj (Γ.mem_mroots i)).1 h2)
  · intro c hcm hk hcc
    apply hc
    rw [List.any_eq_true]
    exact ⟨c, hcm, by simp [hk, hcc]⟩

end MergeData

section MergeComp

variable {k n : ℕ}

private theorem mergeComp_label {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : mergeComp rep f c = some c') :
    c'.label = c.label.map (Prod.map id f) := by
  unfold mergeComp at h
  split_ifs at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain rfl := Option.some.inj h
    rfl

private theorem mergeComp_none {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (h : mergeComp rep f c = none) : c.kind = .dot ∧ f c.x = f c.y := by
  unfold mergeComp at h
  split_ifs at h with h1
  simpa using h1

private theorem mergeComp_of_solid {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (hs : c.kind.isSolid = true)
    (h : rep c.x ≠ rep c.y) : mergeComp rep f c = some (c.map f) := by
  unfold mergeComp
  split_ifs with h1 h2
  · simp at h1
    cases hk : c.kind <;> simp_all [Kind.isSolid]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact absurd h2.2 h
  · rfl

theorem mergeComp_kind {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : mergeComp rep f c = some c') :
    c'.kind = c.kind ∨ ∃ ch, c.kind = .G ch ∧ c'.kind = .weight ch := by
  unfold mergeComp at h
  split_ifs at h with h1 h2
  · obtain rfl := Option.some.inj h
    right
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    have hsolid : c.kind.isSolid = true := h2.1
    obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    exact ⟨ch, hch, by simp [hch, Kind.toWeight]⟩
  · obtain rfl := Option.some.inj h
    left
    rfl


end MergeComp

section MergeFacts

variable {k n : ℕ}

theorem mergeComp_dot {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hk : c.kind = .dot) :
    mergeComp rep f c = if f c.x = f c.y then none else some (c.map f) := by
  unfold mergeComp
  by_cases h : f c.x = f c.y
  · simp [hk, h]
  · simp [hk, h, Kind.isSolid]

theorem mergeComp_solid {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hs : c.kind.isSolid = true) :
    mergeComp rep f c = if rep c.x = rep c.y then
      some { c.map f with kind := c.kind.toWeight, y := f c.x } else some (c.map f) := by
  have hnd : c.kind ≠ .dot := by
    intro h
    rw [h] at hs
    simp [Kind.isSolid] at hs
  unfold mergeComp
  by_cases h : rep c.x = rep c.y
  · simp [hs, h, hnd]
  · simp [hs, h, hnd]

private theorem mergeComp_other {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hd : c.kind ≠ .dot) (hs : c.kind.isSolid = false) :
    mergeComp rep f c = some (c.map f) := by
  unfold mergeComp
  simp [hd, hs]

variable {Γ : Graph k n} {t : Tracked k n}

theorem MergeSpec.mem_comps (hs : MergeSpec Γ t) {c' : Comp (Atom k t.nOut)} :
    c' ∈ t.g.comps ↔ ∃ c ∈ Γ.comps, mergeComp Γ.mrep t.f c = some c' := by
  rw [hs.comps_eq, List.mem_filterMap]

/-- A component that is neither a dotted edge nor a solid edge keeps its kind and is mapped. -/
private theorem MergeSpec.mem_of_other (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hd : c.kind ≠ .dot) (hsol : c.kind.isSolid = false) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, mergeComp_other hd hsol⟩

private theorem MergeSpec.mem_of_dot (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) (hf : t.f c.x ≠ t.f c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [mergeComp_dot hk, ite_eq_right hf]⟩

end MergeFacts

/-! ## Blocks, scaling order and dot excess under `O_merge` -/

section MergeBlocks

variable {k n : ℕ}

private theorem eqvGen_dotRel_reach {L : List (Comp (Atom k n))} {u v : Atom k n}
    (h : Relation.EqvGen (dotRel L) u v) : (dg L).Reachable u v := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact dg_reach_of_mem hc hk
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two atoms have the same representative exactly when they lie in one block. -/
private theorem Graph.mrep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.mrep u = Γ.mrep v ↔ Γ.SameBlock u v := by
  constructor
  · intro h
    have h1 := eqvGen_dotRel_reach (Γ.mrep_conn u)
    have h2 := eqvGen_dotRel_reach (Γ.mrep_conn v)
    rw [h] at h1
    exact h1.trans h2.symm
  · intro h
    exact sigma_eq_of_reach Γ.mrep (fun c hc hk => Γ.mrep_dot hc hk) h

variable {Γ : Graph k n} {t : Tracked k n}

private theorem MergeSpec.sameBlock_of_f_eq (hs : MergeSpec Γ t) {u v : Atom k n}
    (h : t.f u = t.f v) : Γ.SameBlock u v := by
  by_contra hb
  exact hs.f_ne u v (fun hr => hb ((Γ.mrep_eq_iff u v).1 hr)) h

/-- Two distinct atoms with the same image are internal. -/
private theorem MergeSpec.isRight_of_f_eq (hs : MergeSpec Γ t) {u v : Atom k n}
    (h : t.f u = t.f v) (hne : u ≠ v) : u.isRight = true ∧ v.isRight = true := by
  obtain ⟨g, hg, -⟩ := hs.f_inr
  rcases u with a | i <;> rcases v with b | j
  · rw [hs.f_inl, hs.f_inl] at h
    exact absurd (by rw [Sum.inl.inj h]) hne
  · rw [hs.f_inl, hg] at h
    cases h
  · rw [hs.f_inl, hg] at h
    cases h
  · exact ⟨rfl, rfl⟩

private theorem MergeSpec.dot_of_mem (hs : MergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind = .dot) :
    ∃ c ∈ Γ.comps, c.kind = .dot ∧ t.f c.x ≠ t.f c.y ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .dot := h ▸ hk
    rw [mergeComp_dot hck] at hm
    split_ifs at hm with hf
    exact ⟨c, hc, hck, hf, (Option.some.inj hm).symm⟩
  · rw [hch'] at hk
    cases hk

/-- Blocks are mapped into blocks. -/
private theorem MergeSpec.sameBlock_map (hs : MergeSpec Γ t) {u v : Atom k n}
    (h : Γ.SameBlock u v) : t.g.SameBlock (t.f u) (t.f v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    refine SimpleGraph.Reachable.trans ?_ ih
    have : t.g.SameBlock (t.f c.x) (t.f c.y) := by
      by_cases hf : t.f c.x = t.f c.y
      · exact hf ▸ SimpleGraph.Reachable.refl _
      · exact dg_reach_of_mem (hs.mem_of_dot hc hk hf) (by simp [Comp.map, hk])
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · exact this.symm

/-- Atoms whose images lie in one block lie in one block. -/
private theorem MergeSpec.sameBlock_of_map (hs : MergeSpec Γ t) {u v : Atom k n}
    (h : t.g.SameBlock (t.f u) (t.f v)) : Γ.SameBlock u v := by
  have key : ∀ a b, (dg t.g.comps).Reachable a b → ∀ u v, t.f u = a → t.f v = b →
      Γ.SameBlock u v := by
    intro a b hr
    obtain ⟨w⟩ := hr
    induction w with
    | nil => intro u v hu hv; exact hs.sameBlock_of_f_eq (hu.trans hv.symm)
    | @cons a a' b hadj _ ih =>
      intro u v hu hv
      obtain ⟨-, c', hc', hk', hxy⟩ := dg_adj.1 hadj
      obtain ⟨c, hc, hk, -, rfl⟩ := hs.dot_of_mem hc' hk'
      have hcc : Γ.SameBlock c.x c.y := dg_reach_of_mem hc hk
      simp only [Comp.map] at hxy
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (hs.sameBlock_of_f_eq (hu.trans h1.symm)).trans (hcc.trans (ih c.y v h2 hv))
      · exact (hs.sameBlock_of_f_eq (hu.trans h2.symm)).trans
          (hcc.symm.trans (ih c.x v h1 hv))
  exact key _ _ h u v rfl rfl

private theorem MergeSpec.sameBlock_iff (hs : MergeSpec Γ t) (u v : Atom k n) :
    t.g.SameBlock (t.f u) (t.f v) ↔ Γ.SameBlock u v :=
  ⟨hs.sameBlock_of_map, hs.sameBlock_map⟩

/-- `O_merge` keeps the number of blocks. -/
private theorem MergeSpec.card_cc (hs : MergeSpec Γ t) :
    Nat.card (dg Γ.comps).ConnectedComponent = Nat.card (dg t.g.comps).ConnectedComponent :=
  card_cc_of_map t.f hs.f_surj hs.sameBlock_iff

/-- The dotted components removed by `O_merge`. -/
private def removedDots (Γ : Graph k n) (f : Atom k n → Atom k m) : List (Comp (Atom k n)) :=
  Γ.comps.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)

theorem nD_filterMap_mergeComp {m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) :
    ∀ L : List (Comp (Atom k n)), nD (L.filterMap (mergeComp rep f)) +
      (L.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)).length = nD L
  | [] => rfl
  | c :: L => by
    have ih := nD_filterMap_mergeComp rep f L
    rcases hm : mergeComp rep f c with _ | c'
    · obtain ⟨hk, hf⟩ := mergeComp_none hm
      rw [List.filterMap_cons_none hm, List.filter_cons_of_pos (by simp [hk, hf]), nD_cons]
      simp only [hk, ite_true, List.length_cons]
      omega
    · have hnd : ¬ (c.kind = .dot ∧ f c.x = f c.y) := by
        rintro ⟨hk, hf⟩
        rw [mergeComp_dot hk] at hm
        simp [hf] at hm
      have hkk : (c'.kind = .dot) ↔ (c.kind = .dot) := by
        rcases mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
        · rw [h]
        · rw [hch, hch']
          simp
      rw [List.filterMap_cons_some hm, List.filter_cons_of_neg (by simpa using hnd), nD_cons,
        nD_cons]
      by_cases hk : c.kind = .dot
      · simp only [hkk.2 hk, hk, ite_true]
        omega
      · simp only [show ¬ c'.kind = .dot from fun h => hk (hkk.1 h), hk, ite_false]
        omega

end MergeBlocks

/-! ## Doubly connected structures -/

section Tagged

variable {k n m : ℕ}

/-- The kinds usable in a blue net whose solid edges have charge `bc`: the solid edges of charge
`bc` and the ghost edges. -/
def Kind.SP1blueC (bc : Charge) : Kind → Bool
  | .G c => decide (c = bc)
  | .ghost => true
  | _ => false

/-- A component with a tag. -/
abbrev SP1TC (k n : ℕ) : Type := Comp (Atom k n) × Option Bool

/-- The graph on the internal atoms whose edges join two atoms of one molecule, or the two ends of
a component of `L` with the tag `some t`. -/
def Graph.SP1netT (Γ : Graph k n) (L : List (SP1TC k n)) (t : Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => Γ.SameMol (Sum.inr a) (Sum.inr b) ∨
    ∃ p ∈ L, p.2 = some t ∧ p.1.x = Sum.inr a ∧ p.1.y = Sum.inr b

/-- The tagged list `L` is a doubly connected structure on `Γ` with blue charge `bc`: it lists the
components of `Γ`, black ones are diffusive, blue ones are diffusive or blue, and each net spans the
internal atoms. -/
structure Graph.SP1DCT (bc : Charge) (Γ : Graph k n) (L : List (SP1TC k n)) : Prop where
  map_fst : L.map Prod.fst = Γ.comps
  black : ∀ p ∈ L, p.2 = some false → p.1.kind.isDiffusive = true
  blue : ∀ p ∈ L, p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.SP1blueC bc = true
  spanBlack : (Γ.SP1netT L false).Preconnected
  spanBlue : (Γ.SP1netT L true).Preconnected

/-- The graph has a doubly connected structure with blue charge `bc`. -/
def Graph.DCS (bc : Charge) (Γ : Graph k n) : Prop := ∃ L, Γ.SP1DCT bc L

private theorem Graph.molReach_of_comp {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind.joinsMol = true) : Γ.molGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

private theorem Graph.netT_reach_of_sameMol (Γ : Graph k n) (L : List (SP1TC k n)) (t : Bool)
    {a b : Fin n} (h : Γ.SameMol (Sum.inr a) (Sum.inr b)) : (Γ.SP1netT L t).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl (Or.inl h)⟩ |>.reachable

private theorem Graph.netT_reach_of_mem (Γ : Graph k n) (L : List (SP1TC k n)) (t : Bool)
    {p : SP1TC k n} (hp : p ∈ L) (ht : p.2 = some t) {a b : Fin n} (hx : p.1.x = Sum.inr a)
    (hy : p.1.y = Sum.inr b) : (Γ.SP1netT L t).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl (Or.inr ⟨p, hp, ht, hx, hy⟩)⟩ |>.reachable

/-- Reachability in the molecular graph is carried by a map of the atoms that carries every waved
and dotted component to a reachable pair. -/
private theorem molReach_map {Γ : Graph k n} {Γ' : Graph k m} (f : Atom k n → Atom k m)
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

private theorem sameMol_map {Γ : Graph k n} {Γ' : Graph k m} (φ : Fin n → Fin m)
    (hmol : ∀ c ∈ Γ.comps, c.kind.joinsMol = true →
      Γ'.molGraph.Reachable (Sum.map id φ c.x) (Sum.map id φ c.y))
    {u v : Atom k n} (h : Γ.SameMol u v) : Γ'.SameMol (Sum.map id φ u) (Sum.map id φ v) := by
  rcases h with rfl | ⟨hu, hv, hr⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, ?_, molReach_map _ hmol hr⟩
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
private theorem Graph.SP1DCT.transport {bc : Charge} {Γ : Graph k n} {L : List (SP1TC k n)}
    (h : Γ.SP1DCT bc L) (φ : Fin n → Fin m) {Γ' : Graph k m} (L' : List (SP1TC k m))
    (hmap : L'.map Prod.fst = Γ'.comps)
    (hbl : ∀ p ∈ L', p.2 = some false → p.1.kind.isDiffusive = true)
    (hbu : ∀ p ∈ L', p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.SP1blueC bc = true)
    (hmol : ∀ c ∈ Γ.comps, c.kind.joinsMol = true →
      Γ'.molGraph.Reachable (Sum.map id φ c.x) (Sum.map id φ c.y))
    (hedge : ∀ t : Bool, ∀ p ∈ L, p.2 = some t → ∀ a b, p.1.x = Sum.inr a → p.1.y = Sum.inr b →
      (Γ'.SP1netT L' t).Reachable (φ a) (φ b))
    (hcov : ∀ w : Fin m, ∃ a : Fin n, Γ'.SameMol (Sum.inr w) (Sum.inr (φ a))) : Γ'.SP1DCT bc L' := by
  have key : ∀ t : Bool, (Γ.SP1netT L t).Preconnected → (Γ'.SP1netT L' t).Preconnected := by
    intro t hspan
    have hwalk : ∀ a b, (Γ.SP1netT L t).Reachable a b → (Γ'.SP1netT L' t).Reachable (φ a) (φ b) := by
      intro a b hr
      obtain ⟨w⟩ := hr
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a' b' c' hadj _ ih =>
        rw [Graph.SP1netT, SimpleGraph.fromRel_adj] at hadj
        have hstep : (Γ'.SP1netT L' t).Reachable (φ a') (φ b') := by
          rcases hadj.2 with (hs | ⟨p, hp, ht, hx, hy⟩) | (hs | ⟨p, hp, ht, hx, hy⟩)
          · exact Graph.netT_reach_of_sameMol _ _ _ (sameMol_map φ hmol hs)
          · exact hedge t p hp ht a' b' hx hy
          · exact (Graph.netT_reach_of_sameMol _ _ _ (sameMol_map φ hmol hs)).symm
          · exact (hedge t p hp ht b' a' hx hy).symm
        exact hstep.trans ih
    intro w₁ w₂
    obtain ⟨a₁, h₁⟩ := hcov w₁
    obtain ⟨a₂, h₂⟩ := hcov w₂
    exact ((Graph.netT_reach_of_sameMol _ _ _ h₁).trans (hwalk a₁ a₂ (hspan a₁ a₂))).trans
      (Graph.netT_reach_of_sameMol _ _ _ h₂).symm
  exact ⟨hmap, hbl, hbu, key false h.spanBlack, key true h.spanBlue⟩

/-- A tagged component of `L` has neither the kind `xdot` nor a weight kind if it is tagged
or joins molecules: its kind is diffusive, blue or joins molecules. -/
private theorem Graph.SP1DCT.kind_of_tag {bc : Charge} {Γ : Graph k n} {L : List (SP1TC k n)}
    (h : Γ.SP1DCT bc L) {p : SP1TC k n} (hp : p ∈ L) (ht : p.2 ≠ none) :
    p.1.kind.isDiffusive = true ∨ p.1.kind.SP1blueC bc = true := by
  rcases hp2 : p.2 with _ | _ | _
  · exact absurd hp2 ht
  · exact Or.inl (h.black p hp hp2)
  · exact h.blue p hp hp2



end Tagged

/-! ## Replacing one component by a list -/

section Replace

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

private theorem termR_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') (co : Coeff)
    (σ : Atom k n → ι) (ω : Ω) :
    Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω = Graph.termR (⟨L', co⟩ : Graph k n) PF D σ ω := by
  have h1 : ((L.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod =
      ((L'.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod :=
    ((h.filter _).map _).prod_eq
  have h2 : (L.filterMap Comp.label).dedup.Perm (L'.filterMap Comp.label).dedup :=
    (h.filterMap _).dedup
  have h3 : ∀ ℓ : PQ × Atom k n,
      (fun ω' => ((L.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) =
      (fun ω' => ((L'.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) :=
    fun ℓ => funext fun ω' => ((h.filter _).map _).prod_eq
  simp only [Graph.termR, Graph.labels, h3, h1]
  congr 1
  exact (h2.map _).prod_eq


end Replace

/-! ## Values of the dotted edge steps -/

section DotVals

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]

private theorem termR_cons_unl (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω)
    (c : Comp (Atom k n)) (L : List (Comp (Atom k n))) (co : Coeff) (hc : c.label = none) :
    Graph.termR (⟨c :: L, co⟩ : Graph k n) PF D σ ω =
      Comp.val (D ω) σ c * Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω := by
  have h1 : (c :: L).filter (fun c => c.label.isNone) = c :: L.filter (fun c => c.label.isNone) :=
    List.filter_cons_of_pos (by simp [hc])
  have h2 : (c :: L).filterMap Comp.label = L.filterMap Comp.label :=
    List.filterMap_cons_none hc
  have h3 : ∀ ℓ : PQ × Atom k n, (c :: L).filter (fun c => decide (c.label = some ℓ)) =
      L.filter (fun c => decide (c.label = some ℓ)) :=
    fun ℓ => List.filter_cons_of_neg (by simp [hc])
  simp only [Graph.termR, Graph.labels, h1, h2, h3, List.map_cons, List.prod_cons]
  ring

/-- The component at index `i`, if it has no label, factors out of every term. -/
private theorem termR_eraseIdx_unl (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι)
    (ω : Ω) (Γ : Graph k n) {i : ℕ} {c : Comp (Atom k n)} (hc : Γ.comps[i]? = some c)
    (hl : c.label = none) :
    Γ.termR PF D σ ω = Comp.val (D ω) σ c *
      Graph.termR (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n) PF D σ ω := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  have hp := List.getElem_cons_eraseIdx_perm hi
  rw [← termR_cons_unl PF D σ ω _ _ _ hl]
  exact (termR_perm (PF := PF) (D := D) hp Γ.coeff σ ω).symm

private theorem termR_eq_zero_of_val' {Γ : Graph k n} (PF : PFamily Ω ι) (D : Ω → Data ι)
    (σ : Atom k n → ι) (ω : Ω) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hl : c.label = none)
    (h0 : Comp.val (D ω) σ c = 0) : Γ.termR PF D σ ω = 0 := by
  unfold Graph.termR
  have : ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl]⟩, h0⟩)
  rw [this]
  simp

end DotVals

/-- Removing a dotted edge whose ends are joined by the other dotted edges preserves the value,
for every data record and every family of conditional expectations, when no dotted edge carries
a label. -/
theorem dropDot_value {k n : ℕ} (Γ : Graph k n) {i : ℕ} {c : Comp (Atom k n)}
    (hc : Γ.comps[i]? = some c) (hk : c.kind = .dot)
    (hb : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).SameBlock c.x c.y)
    (hlab : ∀ d ∈ Γ.comps, d.kind = .dot → d.label = none) :
    ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
      (e : Fin k → ι),
      (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).valR PF D e = Γ.valR PF D e := by
  intro Ω ι _ _ PF D e
  funext ω
  simp only [Graph.valR]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hcm : c ∈ Γ.comps := List.mem_of_getElem? hc
  rw [termR_eraseIdx_unl PF D _ ω Γ hc (hlab c hcm hk)]
  by_cases hz : ∀ d ∈ Γ.comps.eraseIdx i, d.kind = .dot →
      Sum.elim e s d.x = Sum.elim e s d.y
  · have := sigma_eq_of_reach (Sum.elim e s) hz hb
    simp [Comp.val, hk, this]
  · push Not at hz
    obtain ⟨d, hd, hdk, hne⟩ := hz
    have hdm : d ∈ Γ.comps := List.mem_of_mem_eraseIdx hd
    rw [termR_eq_zero_of_val' (Γ := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩) PF D _ ω hd
      (hlab d hdm hdk) (by simp [Comp.val, hdk, hne])]
    ring

/-! ## Lists with one component replaced -/

section Replace2

variable {α : Type*}

private theorem mem_eraseIdx_of_ne {L : List α} {i : ℕ} {c d : α} (hc : L[i]? = some c)
    (hd : d ∈ L) (hne : d ≠ c) : d ∈ L.eraseIdx i := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hd
  rw [List.mem_eraseIdx_iff_getElem?]
  refine ⟨j, ?_, List.getElem?_eq_getElem hj⟩
  rintro rfl
  rw [List.getElem?_eq_getElem hj] at hc
  exact hne (Option.some.inj hc)

private theorem mem_or_of_mem {L : List α} {i : ℕ} {c d : α} (hc : L[i]? = some c)
    (hd : d ∈ L) : d ∈ L.eraseIdx i ∨ d = c := by
  by_cases h : d = c
  · exact Or.inr h
  · exact Or.inl (mem_eraseIdx_of_ne hc hd h)

private theorem perm_eraseIdx {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c) :
    L.Perm (c :: L.eraseIdx i) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  exact (List.getElem_cons_eraseIdx_perm hi).symm

private theorem sum_map_eraseIdx {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c)
    (g : α → ℤ) : (L.map g).sum = ((L.eraseIdx i).map g).sum + g c := by
  rw [((perm_eraseIdx hc).map g).sum_eq]
  simp [add_comm]

end Replace2

/-! ## Connectivity transfers -/

section ConnTransfer

variable {k n : ℕ}

private theorem edgeNoX_reach_of_comp {T : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ T.comps)
    (hk : c.kind ≠ .xdot) : T.edgeGraphNoX.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

private theorem edgeNoX_reach_of_dg {T : Graph k n} {a b : Atom k n}
    (h : (dg T.comps).Reachable a b) : T.edgeGraphNoX.Reachable a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    have := edgeNoX_reach_of_comp hc (by rw [hk]; simp)
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this.trans ih
    · exact this.symm.trans ih

/-- Connectivity without `×`-dotted edges passes to a graph on the same atoms in which the ends of
every component other than a `×`-dotted edge are joined. -/
private theorem connNoX_transfer {T T' : Graph k n} (h : T.ConnNoX)
    (hr : ∀ c ∈ T.comps, c.kind ≠ .xdot → T'.edgeGraphNoX.Reachable c.x c.y) : T'.ConnNoX := by
  intro u v
  obtain ⟨w⟩ := h u v
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := hadj
    · exact (hr c hc hk).trans ih
    · exact (hr c hc hk).symm.trans ih

private theorem molReach_of_dg {T : Graph k n} {a b : Atom k n}
    (h : (dg T.comps).Reachable a b) : T.molGraph.Reachable a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    have := Graph.molReach_of_comp hc (by rw [hk]; rfl)
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this.trans ih
    · exact this.symm.trans ih

/-- A doubly connected structure passes to a graph on the same atoms. -/
private theorem Graph.SP1DCT.same {bc : Charge} {T T' : Graph k n} {L : List (SP1TC k n)}
    (h : T.SP1DCT bc L) (L' : List (SP1TC k n)) (hmap : L'.map Prod.fst = T'.comps)
    (hbl : ∀ p ∈ L', p.2 = some false → p.1.kind.isDiffusive = true)
    (hbu : ∀ p ∈ L', p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.SP1blueC bc = true)
    (hmol : ∀ c ∈ T.comps, c.kind.joinsMol = true → T'.molGraph.Reachable c.x c.y)
    (hedge : ∀ t : Bool, ∀ p ∈ L, p.2 = some t → ∀ a b, p.1.x = Sum.inr a →
      p.1.y = Sum.inr b → (T'.SP1netT L' t).Reachable a b) : T'.SP1DCT bc L' := by
  have hid : (Sum.map (id : Fin k → Fin k) (id : Fin n → Fin n)) = id := by
    funext u
    rcases u <;> rfl
  refine h.transport id L' hmap hbl hbu ?_ hedge (fun w => ⟨w, Or.inl rfl⟩)
  intro c hc hk
  rw [hid]
  exact hmol c hc hk

end ConnTransfer

/-! ## Removing redundant dotted edges -/

section Drop

variable {k m : ℕ}

/-- Removing a dotted edge whose ends are joined by the other dotted edges. -/
theorem drop_one (g : Graph k m) {i : ℕ} {c : Comp (Atom k m)} (hc : g.comps[i]? = some c)
    (hk : c.kind = .dot) (hr : (dg (g.comps.eraseIdx i)).Reachable c.x c.y) :
    let g₁ : Graph k m := ⟨g.comps.eraseIdx i, g.coeff⟩
    LocElemStep ⟨m, g⟩ ⟨m, g₁⟩ ∧ eL g₁.comps + 1 = eL g.comps ∧ g₁.ord + 2 = g.ord ∧
      (∀ d ∈ g.comps, d.kind ≠ .dot → d ∈ g₁.comps) ∧
      (∀ u v, g₁.SameBlock u v ↔ g.SameBlock u v) ∧
      (g.DCS .plus → g₁.DCS .plus) ∧ (g.ConnNoX → g₁.ConnNoX) ∧
      g₁.wavedThetaGraph = g.wavedThetaGraph := by
  intro g₁
  have hmem : ∀ d ∈ g.comps, d.kind ≠ .dot → d ∈ g₁.comps := by
    intro d hd hdk
    exact mem_eraseIdx_of_ne hc hd (fun h => hdk (h ▸ hk))
  have hr₁ : (dg g₁.comps).Reachable c.x c.y := hr
  obtain ⟨he, hb⟩ := eL_eraseIdx_red hc hk hr
  refine ⟨LocElemStep.dropDot i g c hc hk hr, he, ?_, hmem, hb, ?_, ?_, ?_⟩
  · simp only [Graph.ord, g₁]
    rw [sum_map_eraseIdx hc (fun c => c.kind.ord), hk]
    simp only [Kind.ord]
    ring
  · rintro ⟨L, hL⟩
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
    have hLi : i < L.length := by rw [← List.length_map (f := Prod.fst), hL.map_fst]; exact hi
    have hLc : L[i]? = some L[i] := List.getElem?_eq_getElem hLi
    have hfst : L[i].1 = g.comps[i] := by
      have := congrArg (fun l => l[i]?) hL.map_fst
      simp only [List.getElem?_map, List.getElem?_eq_getElem hLi, List.getElem?_eq_getElem hi,
        Option.map_some, Option.some.injEq] at this
      exact this
    refine ⟨L.eraseIdx i, hL.same (L.eraseIdx i) ?_ ?_ ?_ ?_ ?_⟩
    · rw [← List.eraseIdx_map, hL.map_fst]
    · intro p hp hpt
      exact hL.black p (List.mem_of_mem_eraseIdx hp) hpt
    · intro p hp hpt
      exact hL.blue p (List.mem_of_mem_eraseIdx hp) hpt
    · intro d hd hdk
      by_cases hdd : d.kind = .dot
      · rcases mem_or_of_mem (List.getElem?_eq_getElem hi) hd with hd' | rfl
        · exact Graph.molReach_of_comp (Γ := g₁) hd' hdk
        · exact molReach_of_dg hr₁
      · exact Graph.molReach_of_comp (hmem d hd hdd) hdk
    · intro t p hp hpt a b hx hy
      rcases mem_or_of_mem hLc hp with hp' | hpe
      · exact Graph.netT_reach_of_mem _ _ _ hp' hpt hx hy
      · exfalso
        have := hL.kind_of_tag hp (by rw [hpt]; simp)
        rw [hpe, hfst, hk] at this
        simp [Kind.isDiffusive, Kind.SP1blueC] at this
  · intro hconn
    refine connNoX_transfer hconn fun d hd hdk => ?_
    by_cases hdd : d.kind = .dot
    · rcases mem_or_of_mem hc hd with hd' | rfl
      · exact edgeNoX_reach_of_comp (T := g₁) hd' hdk
      · exact edgeNoX_reach_of_dg hr₁
    · exact edgeNoX_reach_of_comp (hmem d hd hdd) hdk
  · ext u v
    simp only [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj]
    have key : ∀ d, (d.kind.joinsMol = true ∧ d.kind ≠ .dot ∨ d.kind.isDiffusive = true) →
        (d ∈ g₁.comps ↔ d ∈ g.comps) := by
      intro d hd
      have hdd : d.kind ≠ .dot := by
        rcases hd with ⟨-, h⟩ | h
        · exact h
        · intro h'
          rw [h'] at h
          simp [Kind.isDiffusive] at h
      exact ⟨List.mem_of_mem_eraseIdx, fun h => hmem d h hdd⟩
    constructor
    · rintro ⟨hne, ⟨d, hd, hdk, rfl, rfl⟩ | ⟨d, hd, hdk, rfl, rfl⟩⟩
      · exact ⟨hne, Or.inl ⟨d, (key d hdk).1 hd, hdk, rfl, rfl⟩⟩
      · exact ⟨hne, Or.inr ⟨d, (key d hdk).1 hd, hdk, rfl, rfl⟩⟩
    · rintro ⟨hne, ⟨d, hd, hdk, rfl, rfl⟩ | ⟨d, hd, hdk, rfl, rfl⟩⟩
      · exact ⟨hne, Or.inl ⟨d, (key d hdk).2 hd, hdk, rfl, rfl⟩⟩
      · exact ⟨hne, Or.inr ⟨d, (key d hdk).2 hd, hdk, rfl, rfl⟩⟩

end Drop


section SplitPairs

variable {k n : ℕ}

/-- The test "joined by a component whose kind satisfies `p`". -/
def spJoined (Γ : Graph k n) (p : Kind → Bool) (u v : Atom k n) : Bool :=
  Γ.comps.any fun c => p c.kind && ((c.x == u && c.y == v) || (c.x == v && c.y == u))

/-- The ordered candidate pairs. -/
def spCand (Γ : Graph k n) : List (Atom k n × Atom k n) :=
  Γ.comps.filterMap fun c =>
    if (c.kind.isSolid || c.kind == .xdot) && c.x != c.y then some (c.x, c.y) else none

/-- One step of the removal of repeated unordered pairs. -/
def spStep (acc : List (Atom k n × Atom k n)) (p : Atom k n × Atom k n) :
    List (Atom k n × Atom k n) :=
  if acc.any (fun q => q == p || q == p.swap) then acc else acc ++ [p]

/-- The candidate pairs, each unordered pair once. -/
def spUniq (Γ : Graph k n) : List (Atom k n × Atom k n) := (spCand Γ).foldl spStep []

private theorem splitPairs_eq (Γ : Graph k n) : Γ.splitPairs =
    (spUniq Γ).filterMap fun p =>
      if (spJoined Γ Kind.isSolid p.1 p.2 != spJoined Γ (· == .xdot) p.1 p.2) = true then
        some (p.1, p.2, spJoined Γ Kind.isSolid p.1 p.2) else none := rfl

theorem spJoined_iff (Γ : Graph k n) (pr : Kind → Bool) (u v : Atom k n) :
    spJoined Γ pr u v = true ↔
      ∃ c ∈ Γ.comps, pr c.kind = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u) := by
  unfold spJoined
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

private theorem foldl_spStep_pairwise (l acc : List (Atom k n × Atom k n))
    (h : acc.Pairwise fun a b => ¬(b = a ∨ b = a.swap)) :
    (l.foldl spStep acc).Pairwise fun a b => ¬(b = a ∨ b = a.swap) := by
  induction l generalizing acc with
  | nil => exact h
  | cons p l ih =>
    apply ih
    unfold spStep
    split_ifs with hany
    · exact h
    · rw [List.pairwise_append]
      refine ⟨h, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hab
      apply hany
      rw [List.any_eq_true]
      refine ⟨a, ha, ?_⟩
      simp only [Bool.or_eq_true, beq_iff_eq]
      rcases hab with h1 | h1
      · exact Or.inl h1.symm
      · right
        rw [h1]
        simp

private theorem spUniq_pairwise (Γ : Graph k n) :
    (spUniq Γ).Pairwise fun a b => ¬(b = a ∨ b = a.swap) :=
  foldl_spStep_pairwise _ _ List.Pairwise.nil

/-- Two members of `spUniq` that are equal as unordered pairs are equal. -/
theorem spUniq_eq {Γ : Graph k n} {q q' : Atom k n × Atom k n} (hq : q ∈ spUniq Γ)
    (hq' : q' ∈ spUniq Γ) (h : q' = q ∨ q' = q.swap) : q' = q := by
  by_contra hne
  have : Std.Symm fun a b : Atom k n × Atom k n => ¬(b = a ∨ b = a.swap) := by
    refine ⟨fun a b hab hba => hab ?_⟩
    rcases hba with h | h
    · exact Or.inl h.symm
    · right
      rw [h]
      simp
  exact (spUniq_pairwise Γ).forall hq hq' (Ne.symm hne) h

/-- Membership in `splitPairs`. -/
theorem mem_splitPairs {Γ : Graph k n} {p : Atom k n × Atom k n × Bool} :
    p ∈ Γ.splitPairs ↔ (p.1, p.2.1) ∈ spUniq Γ ∧
      spJoined Γ Kind.isSolid p.1 p.2.1 != spJoined Γ (· == .xdot) p.1 p.2.1 ∧
      p.2.2 = spJoined Γ Kind.isSolid p.1 p.2.1 := by
  rw [splitPairs_eq, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, hp⟩
    split_ifs at hp with hne
    · obtain rfl := Option.some.inj hp
      exact ⟨hq, by simpa using hne, rfl⟩
  · rintro ⟨hq, hne, hs⟩
    refine ⟨(p.1, p.2.1), hq, ?_⟩
    have hne' : (spJoined Γ Kind.isSolid p.1 p.2.1 != spJoined Γ (· == .xdot) p.1 p.2.1) =
        true := by simpa using hne
    simp only [hne', ↓reduceIte]
    rw [← hs]

theorem splitPairs_nodup (Γ : Graph k n) : Γ.splitPairs.Nodup := by
  rw [splitPairs_eq]
  apply List.Nodup.filterMap
  · have key : ∀ (x : Atom k n × Atom k n) (b : Atom k n × Atom k n × Bool),
        b ∈ (if (spJoined Γ Kind.isSolid x.1 x.2 != spJoined Γ (· == .xdot) x.1 x.2) = true then
          some (x.1, x.2, spJoined Γ Kind.isSolid x.1 x.2) else none) →
        b.1 = x.1 ∧ b.2.1 = x.2 := by
      intro x b hx
      split_ifs at hx
      · rw [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact ⟨rfl, rfl⟩
      · simp at hx
    intro a a' b hb hb'
    obtain ⟨h1, h2⟩ := key a b hb
    obtain ⟨h3, h4⟩ := key a' b hb'
    exact Prod.ext (h1.symm.trans h3) (h2.symm.trans h4)
  · exact (spUniq_pairwise Γ).imp fun {a b} h hab => h (Or.inl hab.symm)

end SplitPairs
/-! ## The terms of `O_dot` -/

section DotChoice

variable {k n : ℕ}

/-- The test "the pair `{u, v}` is a pair without solid edge". -/
def xonlyB (SP : List (Atom k n × Atom k n × Bool)) (u v : Atom k n) : Bool :=
  SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))

/-- The components of `Γ` that stay in `dotChoice Γ SP A`. -/
def keptComps (Γ : Graph k n) (SP : List (Atom k n × Atom k n × Bool)) :
    List (Comp (Atom k n)) :=
  Γ.comps.filter fun c => !(c.kind == .xdot && xonlyB SP c.x c.y)

/-- The components added in `dotChoice Γ SP A`. -/
def addedComps (SP A : List (Atom k n × Atom k n × Bool)) : List (Comp (Atom k n)) :=
  SP.filterMap fun p =>
    if p ∈ A then some (mkC .dot p.1 p.2.1) else if p.2.2 then some (mkC .xdot p.1 p.2.1)
    else none

private theorem dotChoice_eq (Γ : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    Γ.dotChoice SP A = ⟨keptComps Γ SP ++ addedComps SP A,
      (-1 : Coeff) ^ (A.filter fun p => !p.2.2).length * Γ.coeff⟩ := rfl

private theorem xonlyB_iff (SP : List (Atom k n × Atom k n × Bool)) (u v : Atom k n) :
    xonlyB SP u v = true ↔
      ∃ p ∈ SP, p.2.2 = false ∧ (p.1 = u ∧ p.2.1 = v ∨ p.1 = v ∧ p.2.1 = u) := by
  unfold xonlyB
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']

private theorem mem_keptComps (Γ : Graph k n) (SP : List (Atom k n × Atom k n × Bool))
    (c : Comp (Atom k n)) :
    c ∈ keptComps Γ SP ↔ c ∈ Γ.comps ∧ ¬ (c.kind = .xdot ∧ xonlyB SP c.x c.y = true) := by
  unfold keptComps
  simp [List.mem_filter, imp_iff_not_or]

theorem mem_addedComps {SP A : List (Atom k n × Atom k n × Bool)} {c : Comp (Atom k n)} :
    c ∈ addedComps SP A ↔ ∃ p ∈ SP, (p ∈ A ∧ c = mkC .dot p.1 p.2.1) ∨
      (p ∉ A ∧ p.2.2 = true ∧ c = mkC .xdot p.1 p.2.1) := by
  unfold addedComps
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, h⟩
    refine ⟨p, hp, ?_⟩
    split_ifs at h with h1 h2
    · exact Or.inl ⟨h1, (Option.some.inj h).symm⟩
    · exact Or.inr ⟨h1, h2, (Option.some.inj h).symm⟩
  · rintro ⟨p, hp, h | h⟩
    · exact ⟨p, hp, by rw [ite_eq_left h.1, h.2]⟩
    · exact ⟨p, hp, by rw [ite_eq_right h.1, ite_eq_left h.2.1, h.2.2]⟩

private theorem addedComps_label {SP A : List (Atom k n × Atom k n × Bool)}
    {c : Comp (Atom k n)} (h : c ∈ addedComps SP A) : c.label = none ∧
      (c.kind = .dot ∨ c.kind = .xdot) := by
  obtain ⟨p, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 h
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩



end DotChoice
section ODotBranches

variable {k n : ℕ}

theorem oDotT_branch2 {Γ : Graph k n}
    (h1 : ¬ (2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true))
    (h2 : (Γ.splitPairs.isEmpty && !(Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) = true) :
    oDotT Γ = [Tracked.self Γ] := by
  unfold oDotT
  dsimp only
  rw [ite_eq_right h1, ite_eq_left h2]

end ODotBranches


/-! ## Scaling order and dot excess under `O_dot` -/

section DotCount

variable {k n : ℕ}

/-- The scaling order minus twice the dot excess. -/
def Graph.obl (g : Graph k n) : ℤ := g.ord - 2 * g.dotExcess

private theorem Graph.dotExcess_eq_eL (g : Graph k n) : g.dotExcess = eL g.comps := rfl

private theorem eL_nil : eL ([] : List (Comp (Atom k n))) = 0 := by
  simp only [eL, nD, List.filter_nil, List.length_nil, dg_nil, card_cc_bot, card_atom]
  push_cast
  ring

/-- The dot excess is superadditive. -/
private theorem eL_append_ge (L : List (Comp (Atom k n))) :
    ∀ L' : List (Comp (Atom k n)), eL L + eL L' ≤ eL (L' ++ L)
  | [] => by simp [eL_nil]
  | c :: L' => by
    have ih := eL_append_ge L L'
    by_cases hk : c.kind = .dot
    · rw [List.cons_append]
      by_cases hr : (dg L').Reachable c.x c.y
      · have hr' : (dg (L' ++ L)).Reachable c.x c.y :=
          dg_reach_mono (fun d hd _ => List.mem_append_left _ hd) hr
        rw [eL_cons_dot_red _ hk hr, eL_cons_dot_red _ hk hr']
        linarith
      · rw [eL_cons_dot_new _ hk hr]
        by_cases hr' : (dg (L' ++ L)).Reachable c.x c.y
        · rw [eL_cons_dot_red _ hk hr']
          linarith
        · rw [eL_cons_dot_new _ hk hr']
          exact ih
    · rw [List.cons_append, eL_cons_nondot _ hk, eL_cons_nondot _ hk]
      exact ih

/-- The dot excess depends only on the dotted components. -/
private theorem eL_eq_eL_filter (L : List (Comp (Atom k n))) :
    eL L = eL (L.filter fun c => decide (c.kind = .dot)) :=
  (dg_eL_of_filter_perm (by rw [List.filter_filter]; simp)).2

private theorem ordSum_filterMap_mergeComp' {m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) :
    ∀ L : List (Comp (Atom k n)),
      ((L.filterMap (mergeComp rep f)).map fun c => c.kind.ord).sum +
        2 * ((L.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)).length : ℤ) +
        ((L.filter fun c => c.kind.isSolid && rep c.x == rep c.y).length : ℤ) =
      (L.map fun c => c.kind.ord).sum
  | [] => by simp
  | c :: L => by
    have ih := ordSum_filterMap_mergeComp' rep f L
    rcases hm : mergeComp rep f c with _ | c'
    · obtain ⟨hk, hf⟩ := mergeComp_none hm
      have hs : c.kind.isSolid = false := by rw [hk]; rfl
      rw [List.filterMap_cons_none hm, List.filter_cons_of_pos (by simp [hk, hf]),
        List.filter_cons_of_neg (by simp [hs])]
      simp only [List.length_cons, List.map_cons, List.sum_cons, hk]
      have h2 : Kind.dot.ord = 2 := rfl
      push_cast
      linarith
    · have hnd : ¬ (c.kind = .dot ∧ f c.x = f c.y) := by
        rintro ⟨hk, hf⟩
        rw [mergeComp_dot hk] at hm
        simp [hf] at hm
      rw [List.filterMap_cons_some hm, List.filter_cons_of_neg (by simpa using hnd)]
      by_cases hc : (c.kind.isSolid && rep c.x == rep c.y) = true
      · rw [List.filter_cons, ite_eq_left hc]
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        rw [mergeComp_solid hc.1, ite_eq_left hc.2] at hm
        obtain rfl := Option.some.inj hm
        obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
          have := hc.1
          cases hk : c.kind <;> simp_all [Kind.isSolid]
        have h0 : c.kind.toWeight.ord = 0 := by rw [hch]; rfl
        have h1 : c.kind.ord = 1 := by rw [hch]; rfl
        simp only [List.map_cons, List.sum_cons, List.length_cons, h0, h1]
        push_cast
        linarith
      · rw [List.filter_cons, ite_eq_right hc]
        have hkk : c'.kind = c.kind := by
          rcases mergeComp_kind hm with h | ⟨ch, hch, -⟩
          · exact h
          · have hs : c.kind.isSolid = true := by rw [hch]; rfl
            have hr : rep c.x ≠ rep c.y := by
              intro h'
              apply hc
              simp [hs, h']
            rw [mergeComp_of_solid hs hr] at hm
            rw [← Option.some.inj hm]
            rfl
        simp only [List.map_cons, List.sum_cons, hkk]
        linarith

variable {Γ : Graph k n} {t : Tracked k n}

/-- The scaling order and the dot excess after `O_merge`: removed dotted components lower both,
identified internal atoms raise both, and a solid component inside a block lowers the order by
one. -/
private theorem MergeSpec.ord_eL' (hs : MergeSpec Γ t) :
    t.g.ord = Γ.ord - 2 * ((removedDots Γ t.f).length : ℤ) -
        ((Γ.comps.filter fun c => c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y).length : ℤ) +
        2 * ((n : ℤ) - t.nOut) ∧
      eL t.g.comps = eL Γ.comps - ((removedDots Γ t.f).length : ℤ) + ((n : ℤ) - t.nOut) := by
  have h1 := ordSum_filterMap_mergeComp' Γ.mrep t.f Γ.comps
  have h2 := nD_filterMap_mergeComp Γ.mrep t.f Γ.comps
  rw [← hs.comps_eq] at h1 h2
  refine ⟨?_, ?_⟩
  · simp only [Graph.ord, removedDots]
    linarith
  · simp only [eL, removedDots, hs.card_cc]
    push_cast
    omega

/-- The removed dotted components are at most the identified internal atoms plus their own dot
excess. -/
private theorem MergeSpec.removedDots_le' (hs : MergeSpec Γ t) :
    ((removedDots Γ t.f).length : ℤ) ≤ (n : ℤ) - t.nOut + eL (removedDots Γ t.f) := by
  set H := removedDots Γ t.f with hH
  have hmemH : ∀ c ∈ H, c ∈ Γ.comps ∧ c.kind = .dot ∧ t.f c.x = t.f c.y := by
    intro c hc
    rw [hH, removedDots, List.mem_filter] at hc
    simpa using hc
  have hnD : nD H = H.length := by
    unfold nD
    rw [List.filter_eq_self.2]
    intro c hc
    simp [(hmemH c hc).2.1]
  have hle := card_le_card_cc (G := dg H) t.f hs.f_surj (by
    intro a b hr
    exact sigma_eq_of_reach t.f (fun c hc _ => (hmemH c hc).2.2) hr)
  rw [card_atom] at hle
  simp only [eL, hnD]
  push_cast at hle ⊢
  omega

end DotCount


/-! ## Connected components of a graph with more edges -/

section CCMore

variable {V : Type*}

/-- More reachability gives fewer connected components. -/
private theorem card_cc_le_of_reach [Finite V] {G H : SimpleGraph V}
    (hGH : ∀ a b, G.Reachable a b → H.Reachable a b) :
    Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent :=
  card_le_card_cc H.connectedComponentMk (fun c => by
    induction c using SimpleGraph.ConnectedComponent.ind with | h a => exact ⟨a, rfl⟩)
    (fun a b h => SimpleGraph.ConnectedComponent.sound (hGH a b h))

/-- The map of connected components of a graph with more reachability. -/
private def ccMap {G H : SimpleGraph V} (hGH : ∀ a b, G.Reachable a b → H.Reachable a b) :
    G.ConnectedComponent → H.ConnectedComponent :=
  Quot.lift (fun a => H.connectedComponentMk a) fun a b h =>
    SimpleGraph.ConnectedComponent.sound (hGH a b h)

private theorem ccMap_surj {G H : SimpleGraph V} (hGH : ∀ a b, G.Reachable a b → H.Reachable a b) :
    Function.Surjective (ccMap hGH) := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with | h a =>
  exact ⟨G.connectedComponentMk a, rfl⟩

/-- With as many connected components, the reachability is the same. -/
theorem reach_of_card_cc_eq [Finite V] {G H : SimpleGraph V}
    (hGH : ∀ a b, G.Reachable a b → H.Reachable a b)
    (hc : Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent) :
    ∀ a b, H.Reachable a b → G.Reachable a b := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hinj : Function.Injective (ccMap hGH) := by
    have hb := (Fintype.bijective_iff_surjective_and_card (ccMap hGH)).2
      ⟨ccMap_surj hGH, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc]⟩
    exact hb.1
  intro a b h
  have : ccMap hGH (G.connectedComponentMk a) = ccMap hGH (G.connectedComponentMk b) :=
    SimpleGraph.ConnectedComponent.sound h
  have := hinj this
  exact SimpleGraph.ConnectedComponent.exact this

/-- With one connected component fewer, exactly two connected components are joined. -/
theorem reach_of_card_cc_succ [Finite V] {G H : SimpleGraph V}
    (hGH : ∀ a b, G.Reachable a b → H.Reachable a b)
    (hc : Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent + 1) :
    ∃ a b, ¬ G.Reachable a b ∧ H.Reachable a b ∧ ∀ u v, H.Reachable u v →
      G.Reachable u v ∨ (G.Reachable u a ∧ G.Reachable v b) ∨
        (G.Reachable u b ∧ G.Reachable v a) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  set φ := ccMap hGH with hφ
  have hlt : Fintype.card H.ConnectedComponent < Fintype.card G.ConnectedComponent := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc]
    omega
  obtain ⟨c₁, c₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hlt
  -- `φ` is injective away from `c₂`
  let S := {c : G.ConnectedComponent // c ≠ c₂}
  let ψ : S → H.ConnectedComponent := fun c => φ c.1
  have hψs : Function.Surjective ψ := by
    intro d
    obtain ⟨c, rfl⟩ := ccMap_surj hGH d
    by_cases h : c = c₂
    · exact ⟨⟨c₁, hne⟩, by rw [h]; exact heq⟩
    · exact ⟨⟨c, h⟩, rfl⟩
  have hcardS : Fintype.card S = Fintype.card H.ConnectedComponent := by
    have h1 : Fintype.card S = Fintype.card G.ConnectedComponent - 1 := by
      simp only [S]
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have h2 : Fintype.card G.ConnectedComponent = Fintype.card H.ConnectedComponent + 1 := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc]
    omega
  have hψi : Function.Injective ψ :=
    ((Fintype.bijective_iff_surjective_and_card ψ).2 ⟨hψs, hcardS⟩).1
  induction c₁ using SimpleGraph.ConnectedComponent.ind with | h a =>
  induction c₂ using SimpleGraph.ConnectedComponent.ind with | h b =>
  refine ⟨a, b, fun h => hne (SimpleGraph.ConnectedComponent.sound h),
    SimpleGraph.ConnectedComponent.exact heq, ?_⟩
  intro u v huv
  have hφuv : φ (G.connectedComponentMk u) = φ (G.connectedComponentMk v) :=
    SimpleGraph.ConnectedComponent.sound huv
  by_cases hu : G.connectedComponentMk u = G.connectedComponentMk b
  · by_cases hv : G.connectedComponentMk v = G.connectedComponentMk b
    · left
      exact SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)
    · -- `v` is in the class of `a`
      have : (⟨G.connectedComponentMk v, hv⟩ : S) = ⟨G.connectedComponentMk a, hne⟩ := by
        apply hψi
        change φ _ = φ _
        rw [← hφuv, hu, heq]
      have hva : G.connectedComponentMk v = G.connectedComponentMk a := congrArg Subtype.val this
      right; right
      exact ⟨SimpleGraph.ConnectedComponent.exact hu,
        SimpleGraph.ConnectedComponent.exact hva⟩
  · by_cases hv : G.connectedComponentMk v = G.connectedComponentMk b
    · have : (⟨G.connectedComponentMk u, hu⟩ : S) = ⟨G.connectedComponentMk a, hne⟩ := by
        apply hψi
        change φ _ = φ _
        rw [hφuv, hv, heq]
      have hua : G.connectedComponentMk u = G.connectedComponentMk a := congrArg Subtype.val this
      right; left
      exact ⟨SimpleGraph.ConnectedComponent.exact hua,
        SimpleGraph.ConnectedComponent.exact hv⟩
    · left
      have : (⟨G.connectedComponentMk u, hu⟩ : S) = ⟨G.connectedComponentMk v, hv⟩ :=
        hψi hφuv
      exact SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val this)

end CCMore


/-! ## The terms of `O_dot`: scaling order and dot excess -/

section DotTerms

variable {k n : ℕ}

private theorem length_filter_le_add {α : Type*} (L : List α) (P Q R : α → Bool)
    (h : ∀ c ∈ L, P c = true → Q c = true ∨ R c = true) :
    (L.filter P).length ≤ (L.filter Q).length + (L.filter R).length := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have ih' := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc := h c (List.mem_cons_self ..)
    rw [List.filter_cons, List.filter_cons, List.filter_cons]
    by_cases hP : P c = true <;> by_cases hQ : Q c = true <;> by_cases hR : R c = true <;>
      simp only [hP, hQ, hR, ite_true, ite_false, Bool.false_eq_true, List.length_cons] <;>
      first | omega | (exfalso; rcases hc hP with h1 | h1 <;> simp_all)

theorem length_filter_mono {α : Type*} (L : List α) (P Q : α → Bool)
    (h : ∀ c ∈ L, P c = true → Q c = true) : (L.filter P).length ≤ (L.filter Q).length := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have ih' := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    rw [List.filter_cons, List.filter_cons]
    by_cases hP : P c = true
    · simp only [hP, h c (List.mem_cons_self ..) hP, ite_true, List.length_cons]
      omega
    · by_cases hQ : Q c = true <;>
        simp only [hP, hQ, ite_true, ite_false, Bool.false_eq_true, List.length_cons] <;> omega

private theorem kept_filter_dot (h : Graph k n) (SP : List (Atom k n × Atom k n × Bool)) :
    (keptComps h SP).filter (fun c => decide (c.kind = .dot)) =
      h.comps.filter (fun c => decide (c.kind = .dot)) := by
  unfold keptComps
  rw [List.filter_filter]
  apply List.filter_congr
  intro c _
  by_cases hk : c.kind = .dot <;> simp [hk]

private theorem ordSum_kept (h : Graph k n) (SP : List (Atom k n × Atom k n × Bool)) :
    ((keptComps h SP).map fun c => c.kind.ord).sum = (h.comps.map fun c => c.kind.ord).sum := by
  unfold keptComps
  generalize h.comps = L
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.filter_cons]
    split_ifs with hc
    · rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    · have hc' : (c.kind == Kind.xdot && xonlyB SP c.x c.y) = true := by simpa using hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc'
      have h0 : c.kind.ord = 0 := by rw [hc'.1]; rfl
      rw [ih, List.map_cons, List.sum_cons, h0, zero_add]

private theorem ordSum_added (SP A : List (Atom k n × Atom k n × Bool)) :
    ((addedComps SP A).map fun c => c.kind.ord).sum = 2 * (nD (addedComps SP A) : ℤ) := by
  unfold addedComps nD
  induction SP with
  | nil => simp
  | cons p SP ih =>
    rw [List.filterMap_cons]
    split_ifs with h1 h2
    · rw [List.map_cons, List.sum_cons, List.filter_cons_of_pos (by simp [mkC]), List.length_cons,
        ih]
      have : (mkC Kind.dot p.1 p.2.1 : Comp (Atom k n)).kind.ord = 2 := rfl
      rw [this]
      push_cast
      ring
    · rw [List.map_cons, List.sum_cons, List.filter_cons_of_neg (by simp [mkC]), ih]
      have : (mkC Kind.xdot p.1 p.2.1 : Comp (Atom k n)).kind.ord = 0 := rfl
      rw [this, zero_add]
    · exact ih

theorem nD_append (L L' : List (Comp (Atom k n))) : nD (L ++ L') = nD L + nD L' := by
  simp [nD, List.filter_append]

theorem nD_kept (h : Graph k n) (SP : List (Atom k n × Atom k n × Bool)) :
    nD (keptComps h SP) = nD h.comps := by
  unfold nD
  rw [kept_filter_dot]

theorem dc_comps (h : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    (h.dotChoice SP A).comps = keptComps h SP ++ addedComps SP A := by
  rw [dotChoice_eq]

private theorem dc_ord (h : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    (h.dotChoice SP A).ord = h.ord + 2 * (nD (addedComps SP A) : ℤ) := by
  simp only [Graph.ord, dc_comps, List.map_append, List.sum_append, ordSum_kept, ordSum_added]
  ring

theorem dc_reach (h : Graph k n) (SP A : List (Atom k n × Atom k n × Bool))
    {a b : Atom k n} (hr : (dg h.comps).Reachable a b) :
    (dg (h.dotChoice SP A).comps).Reachable a b := by
  refine dg_reach_mono (fun c hc hk => ?_) hr
  rw [dc_comps]
  refine List.mem_append_left _ ?_
  rw [mem_keptComps]
  exact ⟨hc, fun h' => by rw [hk] at h'; exact absurd h'.1 (by simp)⟩

/-- The number of connected components of the graph of dotted edges. -/
def ccN (L : List (Comp (Atom k n))) : ℕ := Nat.card (dg L).ConnectedComponent

theorem ccN_dc_le (h : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    ccN (h.dotChoice SP A).comps ≤ ccN h.comps :=
  card_cc_le_of_reach fun _ _ hr => dc_reach h SP A hr

theorem dc_obl (h : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    (h.dotChoice SP A).obl =
      h.obl + 2 * ((ccN h.comps : ℤ) - ccN (h.dotChoice SP A).comps) := by
  simp only [Graph.obl, Graph.dotExcess_eq_eL, dc_ord, eL, ccN]
  rw [dc_comps, nD_append, nD_kept]
  push_cast
  ring

/-- The number of solid components with both ends in one block. -/
def convN (g : Graph k n) : ℕ :=
  (g.comps.filter fun c => c.kind.isSolid && g.mrep c.x == g.mrep c.y).length

theorem MergeSpec.obl_eq {Γ : Graph k n} {t : Tracked k n} (hs : MergeSpec Γ t) :
    t.g.obl = Γ.obl - convN Γ := by
  obtain ⟨h1, h2⟩ := hs.ord_eL'
  simp only [Graph.obl, Graph.dotExcess_eq_eL, convN]
  rw [h1, h2]
  ring

/-- Dotted edges with an external end are never removed by `O_merge`. -/
private theorem MergeSpec.dot_ne {Γ : Graph k n} {t : Tracked k n} (hs : MergeSpec Γ t)
    {c : Comp (Atom k n)} (hxy : c.x ≠ c.y) (hext : c.x.isRight = false ∨ c.y.isRight = false) :
    t.f c.x ≠ t.f c.y := by
  intro hf
  obtain ⟨h1, h2⟩ := hs.isRight_of_f_eq hf hxy
  rcases hext with h | h
  · rw [h1] at h; cases h
  · rw [h2] at h; cases h

/-- Hypotheses on the input of `O_dot`: plain, dotted edges with an external end, no solid loop,
no `×`-dotted edge inside a block, at most one distinct label. -/
structure DotIn (h : Graph k n) : Prop where
  plain : h.Plain
  dotExt : ∀ c ∈ h.comps, c.kind = .dot → c.x.isRight = false ∨ c.y.isRight = false
  noLoop : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y
  xa : h.XdotApart
  lab : h.labels.length ≤ 1

/-- An output of `O_dot` other than the input: the merge of a term of `dotChoice`. -/
theorem mem_oDotT_cases {h : Graph k n} {t : Tracked k n} (ht : t ∈ oDotT h) :
    t = Tracked.self h ∨ ∃ A, List.Sublist A h.splitPairs ∧
      (h.dotChoice h.splitPairs A).mergeT = some t := by
  unfold oDotT at ht
  dsimp only at ht
  split_ifs at ht with h1 h2
  · exact Or.inl (List.mem_singleton.1 ht)
  · exact Or.inl (List.mem_singleton.1 ht)
  · obtain ⟨A, hA, hm⟩ := List.mem_filterMap.1 ht
    exact Or.inr ⟨A, List.mem_sublists.1 hA, hm⟩

/-- `u` and `v` are joined by a `×`-dotted edge of `h`. -/
private theorem hasXdot_iff (h : Graph k n) (u v : Atom k n) :
    h.hasXdot u v = true ↔
      ∃ d ∈ h.comps, d.kind = .xdot ∧ (d.x = u ∧ d.y = v ∨ d.x = v ∧ d.y = u) := by
  simp only [Graph.hasXdot, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]

/-- A solid edge without a `×`-dotted edge between its ends. -/
def unpB (h : Graph k n) (c : Comp (Atom k n)) : Bool :=
  c.kind.isSolid && !h.hasXdot c.x c.y

/-- A solid component of a term of `dotChoice` with both ends in one block has no `×`-dotted edge
between its ends, when the merge succeeds. -/
private theorem conv_unp {h : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n} (hm : (h.dotChoice h.splitPairs A).mergeT = some t) {c : Comp (Atom k n)}
    (hc : c ∈ h.comps) (hs : c.kind.isSolid = true)
    (hr : (h.dotChoice h.splitPairs A).mrep c.x = (h.dotChoice h.splitPairs A).mrep c.y) :
    h.hasXdot c.x c.y = false := by
  have hspec := mergeT_spec hm
  by_contra hx
  rw [Bool.not_eq_false, hasXdot_iff] at hx
  obtain ⟨d, hd, hdk, hxy⟩ := hx
  have hdk' : d ∈ (h.dotChoice h.splitPairs A).comps := by
    rw [dc_comps]
    refine List.mem_append_left _ ((mem_keptComps _ _ _).2 ⟨hd, ?_⟩)
    rintro ⟨-, hxo⟩
    rw [xonlyB_iff] at hxo
    obtain ⟨p, hp, hpf, hpe⟩ := hxo
    obtain ⟨-, -, hpb⟩ := mem_splitPairs.1 hp
    have hsj : spJoined h Kind.isSolid p.1 p.2.1 = true := by
      rw [spJoined_iff]
      refine ⟨c, hc, hs, ?_⟩
      rcases hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3, h4] <;> simp
    rw [hsj] at hpb
    rw [hpb] at hpf
    cases hpf
  apply hspec.xdot_ne d hdk' hdk
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hr]
  · rw [h1, h2, hr]

open Classical in
/-- The converted solid components lie in `h` and have no `×`-dotted partner. -/
theorem convN_le {h : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n} (hm : (h.dotChoice h.splitPairs A).mergeT = some t) :
    convN (h.dotChoice h.splitPairs A) ≤ (h.comps.filter fun c => unpB h c &&
      decide ((dg (h.dotChoice h.splitPairs A).comps).Reachable c.x c.y)).length := by
  set dc := h.dotChoice h.splitPairs A with hdc
  unfold convN
  have hc1 : (dc.comps.filter fun c => c.kind.isSolid && dc.mrep c.x == dc.mrep c.y) =
      (keptComps h h.splitPairs).filter fun c => c.kind.isSolid && dc.mrep c.x == dc.mrep c.y := by
    rw [hdc, dc_comps, List.filter_append]
    have : (addedComps h.splitPairs A).filter
        (fun c => c.kind.isSolid && (h.dotChoice h.splitPairs A).mrep c.x ==
          (h.dotChoice h.splitPairs A).mrep c.y) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      rcases (addedComps_label hc).2 with hk | hk <;> simp [hk, Kind.isSolid]
    rw [this, List.append_nil]
  rw [hc1]
  unfold keptComps
  rw [List.filter_filter]
  refine length_filter_mono _ _ _ fun c hc hP => ?_
  have hs : c.kind.isSolid = true := by
    revert hP; cases c.kind.isSolid <;> simp
  have hr : dc.mrep c.x = dc.mrep c.y := by
    revert hP; by_cases hh : dc.mrep c.x = dc.mrep c.y <;> simp [hh]
  simp only [unpB, Bool.and_eq_true, hs, true_and, decide_eq_true_eq]
  refine ⟨by simpa using conv_unp hm hc hs hr, ?_⟩
  exact (dc.mrep_eq_iff c.x c.y).1 hr

private theorem reach_new {h : Graph k n} {nw : Atom k n → Bool}
    (hnd : ∀ c ∈ h.comps, c.kind = .dot → nw c.x = false ∧ nw c.y = false) {α β : Atom k n}
    (hα : nw α = true) (hr : (dg h.comps).Reachable α β) : α = β := by
  obtain ⟨w⟩ := hr
  cases w with
  | nil => rfl
  | cons hadj _ =>
    obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    obtain ⟨h1, h2⟩ := hnd c hc hk
    rcases hxy with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · rw [h1] at hα; cases hα
    · rw [h2] at hα; cases hα

/-- The data of the new atoms of a term of a local operation, for `O_dot`: no dotted or
`×`-dotted edge at a new atom; at most two solid edges without `×`-dotted partner at a new atom; at
most `s` of them between old atoms; at most four in all, at most two if `s = 0`. -/
structure DotNew (h : Graph k n) (s : ℕ) (nw : Atom k n → Bool) : Prop where
  noDot : ∀ c ∈ h.comps, (c.kind = .dot ∨ c.kind = .xdot) → nw c.x = false ∧ nw c.y = false
  two : ∀ α, nw α = true →
    (h.comps.filter fun c => unpB h c && (c.x == α || c.y == α)).length ≤ 2
  old : (h.comps.filter fun c => unpB h c && !nw c.x && !nw c.y).length ≤ s
  four : (h.comps.filter (unpB h)).length ≤ 4
  zero : s = 0 → (h.comps.filter (unpB h)).length ≤ 2

open Classical in
/-- The bound `e ≤ s + 2J` on the converted solid edges, with its cases. -/
private theorem conv_bound {h : Graph k n} (hd : DotIn h) {s : ℕ} {nw : Atom k n → Bool}
    (hn : DotNew h s nw) {A : List (Atom k n × Atom k n × Bool)} {t : Tracked k n}
    (hm : (h.dotChoice h.splitPairs A).mergeT = some t) :
    (convN (h.dotChoice h.splitPairs A) : ℤ) ≤
      s + 2 * ((ccN h.comps : ℤ) - ccN (h.dotChoice h.splitPairs A).comps) := by
  set dc := h.dotChoice h.splitPairs A with hdc
  have hle := convN_le hm
  rw [← hdc] at hle
  have hJ := ccN_dc_le h h.splitPairs A
  rw [← hdc] at hJ
  have hnd : ∀ c ∈ h.comps, c.kind = .dot → nw c.x = false ∧ nw c.y = false :=
    fun c hc hk => hn.noDot c hc (Or.inl hk)
  have hGH : ∀ a b, (dg h.comps).Reachable a b → (dg dc.comps).Reachable a b :=
    fun _ _ hr => dc_reach h _ A hr
  rcases Nat.lt_or_ge (ccN dc.comps + 1) (ccN h.comps) with hJ2 | hJ1
  · -- two or more merges
    have h4 : (h.comps.filter fun c => unpB h c &&
        decide ((dg dc.comps).Reachable c.x c.y)).length ≤ 4 :=
      (length_filter_mono _ _ _ fun c _ hc => by
        simp only [Bool.and_eq_true] at hc; exact hc.1).trans hn.four
    omega
  rcases Nat.lt_or_ge (ccN dc.comps) (ccN h.comps) with hJ1' | hJ0
  · -- one merge
    have hc1 : ccN h.comps = ccN dc.comps + 1 := by omega
    obtain ⟨a, b, -, -, hab⟩ := reach_of_card_cc_succ hGH hc1
    by_cases hnab : nw a = true ∨ nw b = true
    · set α₀ := if nw a = true then a else b with hα₀
      have hα₀n : nw α₀ = true := by
        rw [hα₀]
        split_ifs with h1
        · exact h1
        · exact hnab.resolve_left h1
      have hsplit := length_filter_le_add h.comps
        (fun c => unpB h c && decide ((dg dc.comps).Reachable c.x c.y))
        (fun c => unpB h c && !nw c.x && !nw c.y)
        (fun c => unpB h c && (c.x == α₀ || c.y == α₀)) (by
          intro c hc hP
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
          obtain ⟨hu, hr⟩ := hP
          by_cases hold : nw c.x = false ∧ nw c.y = false
          · left
            simp [hu, hold.1, hold.2]
          right
          simp only [Bool.and_eq_true, hu, true_and, Bool.or_eq_true, beq_iff_eq]
          have hloop := hd.noLoop c hc (by simp only [unpB, Bool.and_eq_true] at hu; exact hu.1)
          -- some end of `c` is new
          have hnew : nw c.x = true ∨ nw c.y = true := by
            by_contra hh
            push Not at hh
            exact hold ⟨by simpa using hh.1, by simpa using hh.2⟩
          rcases hab c.x c.y hr with hr' | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
          · exfalso
            rcases hnew with hx | hy
            · exact hloop (reach_new hnd hx hr')
            · exact hloop (reach_new hnd hy hr'.symm).symm
          · -- `c.x` with `a`, `c.y` with `b`
            rcases hnew with hx | hy
            · have := reach_new hnd hx hxa
              rw [hα₀]
              split_ifs with h1
              · exact Or.inl this
              · exact absurd (this ▸ hx) h1
            · have hyb' := reach_new hnd hy hyb
              rw [hα₀]
              split_ifs with h1
              · exact Or.inl (reach_new hnd h1 hxa.symm).symm
              · exact Or.inr hyb'
          · rcases hnew with hx | hy
            · have hxb' := reach_new hnd hx hxb
              rw [hα₀]
              split_ifs with h1
              · exact Or.inr (reach_new hnd h1 hya.symm).symm
              · exact Or.inl hxb'
            · have := reach_new hnd hy hya
              rw [hα₀]
              split_ifs with h1
              · exact Or.inr this
              · exact absurd (this ▸ hy) h1)
      have h2 := hn.two α₀ hα₀n
      have h3 := hn.old
      omega
    · push Not at hnab
      have hsub := length_filter_mono h.comps
        (fun c => unpB h c && decide ((dg dc.comps).Reachable c.x c.y))
        (fun c => unpB h c && !nw c.x && !nw c.y) (by
          intro c hc hP
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
          obtain ⟨hu, hr⟩ := hP
          have hloop := hd.noLoop c hc (by simp only [unpB, Bool.and_eq_true] at hu; exact hu.1)
          have hna : nw a = false := by simpa using hnab.1
          have hnb : nw b = false := by simpa using hnab.2
          have key : ∀ w, nw w = true → (dg h.comps).Reachable w a ∨
              (dg h.comps).Reachable w b → False := by
            intro w hw hr'
            rcases hr' with hr' | hr'
            · rw [reach_new hnd hw hr'] at hw; rw [hna] at hw; cases hw
            · rw [reach_new hnd hw hr'] at hw; rw [hnb] at hw; cases hw
          have hx : nw c.x = false := by
            by_contra hx
            simp only [Bool.not_eq_false] at hx
            rcases hab c.x c.y hr with hr' | ⟨hxa, -⟩ | ⟨hxb, -⟩
            · exact hloop (reach_new hnd hx hr')
            · exact key _ hx (Or.inl hxa)
            · exact key _ hx (Or.inr hxb)
          have hy : nw c.y = false := by
            by_contra hy
            simp only [Bool.not_eq_false] at hy
            rcases hab c.x c.y hr with hr' | ⟨-, hyb⟩ | ⟨-, hya⟩
            · exact hloop (reach_new hnd hy hr'.symm).symm
            · exact key _ hy (Or.inr hyb)
            · exact key _ hy (Or.inl hya)
          simp [hu, hx, hy])
      have h3 := hn.old
      omega
  · -- no merge
    have hc0 : ccN h.comps = ccN dc.comps := le_antisymm hJ0 hJ
    have hr0 := reach_of_card_cc_eq hGH hc0
    have hsub := length_filter_mono h.comps
      (fun c => unpB h c && decide ((dg dc.comps).Reachable c.x c.y))
      (fun c => unpB h c && !nw c.x && !nw c.y) (by
        intro c hc hP
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
        obtain ⟨hu, hr⟩ := hP
        have hr' := hr0 _ _ hr
        have hloop := hd.noLoop c hc (by simp only [unpB, Bool.and_eq_true] at hu; exact hu.1)
        have hx : nw c.x = false := by
          by_contra hx
          exact hloop (reach_new hnd (by simpa using hx) hr')
        have hy : nw c.y = false := by
          by_contra hy
          exact hloop (reach_new hnd (by simpa using hy) hr'.symm).symm
        simp [hu, hx, hy])
    have h3 := hn.old
    omega

end DotTerms


/-! ## The dot excess does not decrease under `O_dot` -/

section DotExcess

variable {k n : ℕ}

private theorem filter_split_perm {α : Type*} (L : List α) (p q : α → Bool) :
    (L.filter p).Perm ((L.filter fun c => p c && q c) ++ (L.filter fun c => p c && !q c)) := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.filter_cons]
    by_cases hp : p c = true
    · by_cases hq : q c = true
      · simp only [hp, hq, Bool.and_self, ite_true, Bool.not_true, Bool.and_false,
          Bool.false_eq_true, ite_false, List.cons_append]
        exact ih.cons c
      · simp only [hp, hq, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
          Bool.not_false, Bool.and_self]
        exact (ih.cons c).trans List.perm_middle.symm
    · simp only [hp, Bool.false_and, Bool.false_eq_true, ite_false]
      exact ih

/-- `O_merge` of a term of `dotChoice` does not lower the dot excess below that of the input. -/
private theorem merge_eL_ge {h : Graph k n} (hd : DotIn h) {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n} (hm : (h.dotChoice h.splitPairs A).mergeT = some t) :
    eL h.comps ≤ eL t.g.comps := by
  set dc := h.dotChoice h.splitPairs A with hdc
  have hs := mergeT_spec hm
  obtain ⟨-, h2⟩ := hs.ord_eL'
  have h3 := hs.removedDots_le'
  set rem := removedDots dc t.f with hrem
  -- the dotted components of `dc`
  have hHd : ∀ c ∈ h.comps, c.kind = .dot → t.f c.x ≠ t.f c.y := fun c hc hk =>
    hs.dot_ne ((hd.plain c hc).2.2.2.1 hk) (hd.dotExt c hc hk)
  have hremeq : rem = (addedComps h.splitPairs A).filter
      fun c => decide (c.kind = .dot ∧ t.f c.x = t.f c.y) := by
    rw [hrem, removedDots, hdc, dc_comps, List.filter_append]
    have : (keptComps h h.splitPairs).filter
        (fun c => decide (c.kind = .dot ∧ t.f c.x = t.f c.y)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcon
      simp only [decide_eq_true_eq] at hcon
      exact hHd c ((mem_keptComps _ _ _).1 hc).1 hcon.1 hcon.2
    rw [this, List.nil_append]
  set Y := (addedComps h.splitPairs A).filter
    fun c => decide (c.kind = .dot) && !decide (t.f c.x = t.f c.y) with hY
  have hperm : (dc.comps.filter fun c => decide (c.kind = .dot)).Perm
      ((h.comps.filter fun c => decide (c.kind = .dot)) ++ (rem ++ Y)) := by
    rw [hdc, dc_comps, List.filter_append, kept_filter_dot]
    refine List.Perm.append_left _ ?_
    have := filter_split_perm (addedComps h.splitPairs A) (fun c => decide (c.kind = .dot))
      (fun c => decide (t.f c.x = t.f c.y))
    refine this.trans (List.Perm.append_right _ ?_)
    rw [hremeq]
    apply List.Perm.of_eq
    apply List.filter_congr
    intro c _
    simp [Bool.decide_and]
  have hdc_eL : eL dc.comps = eL ((h.comps.filter fun c => decide (c.kind = .dot)) ++ (rem ++ Y)) :=
    (eL_eq_eL_filter _).trans (eL_perm hperm)
  have h4 := eL_append_ge (rem ++ Y) (h.comps.filter fun c => decide (c.kind = .dot))
  have h5 := eL_append_ge Y rem
  have h6 := eL_nonneg Y
  have h7 : eL (h.comps.filter fun c => decide (c.kind = .dot)) = eL h.comps :=
    (eL_eq_eL_filter _).symm
  have hle := hs.nOut_le
  rw [h2]
  linarith

/-- `O_dot` keeps the scaling order minus twice the dot excess up to the order surplus `s` of the
input, and does not lower the dot excess. -/
theorem dot_obl {h : Graph k n} (hd : DotIn h) {s : ℕ} {nw : Atom k n → Bool}
    (hn : DotNew h s nw) {t : Tracked k n} (ht : t ∈ oDotT h) :
    h.dotExcess ≤ t.g.dotExcess ∧ h.obl - s ≤ t.g.obl := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact ⟨le_rfl, by simp [Tracked.self]⟩
  · refine ⟨merge_eL_ge hd hm, ?_⟩
    have hs := mergeT_spec hm
    rw [hs.obl_eq, dc_obl]
    have := conv_bound hd hn hm
    linarith

end DotExcess


/-! ## The quantities of the descent -/

section Quantities

variable {k n : ℕ}

/-- Light weights. -/
def Kind.isLt : Kind → Bool
  | .light _ => true
  | _ => false

/-- Regular weights. -/
def Kind.isRg : Kind → Bool
  | .weight _ => true
  | _ => false

/-- The number of light weights. -/
def Graph.lwN (g : Graph k n) : ℕ := (g.comps.filter fun c => c.kind.isLt).length

/-- The number of regular weights. -/
def Graph.rwN (g : Graph k n) : ℕ := (g.comps.filter fun c => c.kind.isRg).length

/-- The number of solid edges at an external atom. -/
def Graph.eextN (g : Graph k n) : ℕ :=
  (g.comps.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length

/-- The excess degree `∑ (deg − 2)₊` over the internal atoms. -/
def Graph.degX (g : Graph k n) : ℕ := ∑ i : Fin n, (g.deg (.inr i) - 2)

/-- The number of internal atoms of degree `2` that are not standard neutral. -/
def Graph.badN (g : Graph k n) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    g.deg (.inr i) = 2 ∧ g.stdNeutralAt (.inr i) = false).card

/-- The potential `1000 · (light weights) + 100 · ∑ (deg − 2)₊ + 10 · (internal atoms of degree
`2` that are not standard neutral) + (regular weights)`. -/
def Graph.phi (g : Graph k n) : ℕ := 1000 * g.lwN + 100 * g.degX + 10 * g.badN + g.rwN

/-- No two distinct internal atoms lie in one block. -/
def Graph.SepInt (g : Graph k n) : Prop :=
  ∀ i j : Fin n, g.SameBlock (.inr i) (.inr j) → i = j

open Classical in
/-- `0` if no two distinct internal atoms lie in one block, `1` otherwise. -/
def Graph.mfl (g : Graph k n) : ℕ := if g.SepInt then 0 else 1

/-- The components other than `×`-dotted edges. -/
private def Graph.noX (g : Graph k n) : List (Comp (Atom k n)) :=
  g.comps.filter fun c => c.kind != .xdot

private theorem deg_eq_of_noX {g g' : Graph k n} (h : g.noX = g'.noX) (u : Atom k n) :
    g.deg u = g'.deg u := by
  have key : ∀ g : Graph k n, g.deg u =
      (g.noX.filter fun c => c.kind.isSolid && (c.x == u || c.y == u)).length := by
    intro g
    unfold Graph.deg Graph.noX
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro c _
    cases hk : c.kind <;> simp [Kind.isSolid]
  rw [key g, key g', h]

private theorem ends_eq_of_noX {g g' : Graph k n} (h : g.noX = g'.noX) (u : Atom k n) :
    g.ends u = g'.ends u := by
  have key : ∀ g : Graph k n, g.ends u = g.noX.filterMap fun c =>
      match c.kind with
      | .G ch => if c.x = u ∧ c.y ≠ u then some (true, ch)
          else if c.y = u ∧ c.x ≠ u then some (false, ch) else none
      | _ => none := by
    intro g
    unfold Graph.ends Graph.noX
    rw [List.filterMap_filter]
    congr 1
    funext c
    cases hk : c.kind <;> simp
  rw [key g, key g', h]

private theorem stdNeutralAt_eq_of_noX {g g' : Graph k n} (h : g.noX = g'.noX) (u : Atom k n) :
    g.stdNeutralAt u = g'.stdNeutralAt u := by
  have key : ∀ g : Graph k n, (g.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u)) =
      g.noX.filter fun c => c.x == u || c.y == u := by
    intro g
    unfold Graph.noX
    rw [List.filter_filter]
    apply List.filter_congr
    intro c _
    simp [Bool.and_comm]
  unfold Graph.stdNeutralAt
  rw [key g, key g', h, ends_eq_of_noX h]

private theorem count_eq_of_noX {g g' : Graph k n} (h : g.noX = g'.noX) (P : Kind → Bool)
    (hP : P .xdot = false) (Q : Comp (Atom k n) → Bool) :
    (g.comps.filter fun c => P c.kind && Q c).length =
      (g'.comps.filter fun c => P c.kind && Q c).length := by
  have key : ∀ g : Graph k n, (g.comps.filter fun c => P c.kind && Q c) =
      g.noX.filter fun c => P c.kind && Q c := by
    intro g
    unfold Graph.noX
    rw [List.filter_filter]
    apply List.filter_congr
    intro c _
    by_cases hk : c.kind = .xdot
    · simp [hk, hP]
    · simp [hk]
  rw [key g, key g', h]

private theorem phi_eq_of_noX {g g' : Graph k n} (h : g.noX = g'.noX) : g.phi = g'.phi := by
  have h1 : g.lwN = g'.lwN := by
    have := count_eq_of_noX h Kind.isLt rfl (fun _ => true)
    simpa [Graph.lwN] using this
  have h2 : g.rwN = g'.rwN := by
    have := count_eq_of_noX h Kind.isRg rfl (fun _ => true)
    simpa [Graph.rwN] using this
  have h3 : g.degX = g'.degX := by
    unfold Graph.degX
    exact Finset.sum_congr rfl fun i _ => by rw [deg_eq_of_noX h]
  have h4 : g.badN = g'.badN := by
    unfold Graph.badN
    congr 1
    apply Finset.filter_congr
    intro i _
    rw [deg_eq_of_noX h, stdNeutralAt_eq_of_noX h]
  simp only [Graph.phi, h1, h2, h3, h4]

private theorem eextN_eq_of_noX {g g' : Graph k n} (h : g.noX = g'.noX) : g.eextN = g'.eextN :=
  count_eq_of_noX h Kind.isSolid rfl fun c => c.x.isLeft || c.y.isLeft

/-! ### Injective maps of the atoms -/

variable {m : ℕ}

private theorem beq_map_inj {f : Atom k n → Atom k m} (hf : Function.Injective f)
    (a b : Atom k n) : (f a == f b) = (a == b) := by
  by_cases h : a = b
  · simp [h]
  · simp [h, hf.ne h]

private theorem deg_map_inj {f : Atom k n → Atom k m} (hf : Function.Injective f)
    (L : List (Comp (Atom k n))) (co co' : Coeff) (u : Atom k n) :
    (⟨L.map (Comp.map f), co'⟩ : Graph k m).deg (f u) = (⟨L, co⟩ : Graph k n).deg u := by
  have hb := beq_map_inj hf
  unfold Graph.deg
  simp only [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro c _
  simp only [Function.comp, Comp.map, hb]

private theorem ends_map_inj {f : Atom k n → Atom k m} (hf : Function.Injective f)
    (L : List (Comp (Atom k n))) (co co' : Coeff) (u : Atom k n) :
    (⟨L.map (Comp.map f), co'⟩ : Graph k m).ends (f u) = (⟨L, co⟩ : Graph k n).ends u := by
  unfold Graph.ends
  simp only [List.filterMap_map]
  congr 1
  funext c
  simp only [Function.comp, Comp.map, hf.eq_iff, ne_eq]

private theorem stdNeutralAt_map_inj {f : Atom k n → Atom k m} (hf : Function.Injective f)
    (L : List (Comp (Atom k n))) (co co' : Coeff) (u : Atom k n) :
    (⟨L.map (Comp.map f), co'⟩ : Graph k m).stdNeutralAt (f u) =
      (⟨L, co⟩ : Graph k n).stdNeutralAt u := by
  have hcs : (L.map (Comp.map f)).filter (fun c => c.kind != .xdot && (c.x == f u || c.y == f u)) =
      (L.filter fun c => c.kind != .xdot && (c.x == u || c.y == u)).map (Comp.map f) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro c _
    simp only [Function.comp, Comp.map, beq_map_inj hf]
  unfold Graph.stdNeutralAt
  simp only
  rw [ends_map_inj hf L co co' u, hcs]
  simp only [List.filter_map, List.length_map, Function.comp_def, Comp.map]

end Quantities


/-! ## The quantities under `O_merge` -/

section MergeQuant

variable {k n : ℕ}

private theorem count_filterMap {α β : Type*} (F : α → Option β) (P : β → Bool) (Q : α → Bool)
    (h : ∀ a, match F a with | some b => P b = Q a | none => Q a = false) :
    ∀ L : List α, ((L.filterMap F).filter P).length = (L.filter Q).length
  | [] => rfl
  | a :: L => by
    have ih := count_filterMap F P Q h L
    have ha := h a
    rcases hF : F a with _ | b
    · rw [hF] at ha
      simp only at ha
      rw [List.filterMap_cons_none hF, List.filter_cons_of_neg (by simp [ha])]
      exact ih
    · rw [hF] at ha
      simp only at ha
      rw [List.filterMap_cons_some hF, List.filter_cons, List.filter_cons, ha]
      split_ifs <;> simp [ih]

private theorem length_filter_or_add {α : Type*} (L : List α) (p q : α → Bool) :
    (L.filter fun a => p a || q a).length + (L.filter fun a => p a && q a).length =
      (L.filter p).length + (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.filter_cons]
    by_cases hp : p a = true <;> by_cases hq : q a = true <;>
      simp only [hp, hq, Bool.or_true, Bool.and_true, Bool.or_false, Bool.and_false, ite_true,
        ite_false, Bool.false_eq_true, List.length_cons] <;> omega

variable {Γ : Graph k n} {t : Tracked k n}

private theorem MergeSpec.isLeft (hs : MergeSpec Γ t) (u : Atom k n) :
    (t.f u).isLeft = u.isLeft := by
  obtain ⟨g, hg, -⟩ := hs.f_inr
  rcases u with a | i
  · simp [hs.f_inl]
  · rw [hg]
    rfl

private theorem MergeSpec.isRight (hs : MergeSpec Γ t) (u : Atom k n) :
    (t.f u).isRight = u.isRight := by
  have := hs.isLeft u
  rcases hu : u with a | i <;> rcases hfu : t.f u with b | j <;> simp_all

/-- `O_merge` keeps the light weights. -/
theorem MergeSpec.lwN_eq (hs : MergeSpec Γ t) : t.g.lwN = Γ.lwN := by
  unfold Graph.lwN
  rw [hs.comps_eq]
  apply count_filterMap
  intro c
  rcases hm : mergeComp Γ.mrep t.f c with _ | c'
  · obtain ⟨hk, -⟩ := mergeComp_none hm
    simp [hk, Kind.isLt]
  · simp only
    rcases mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
    · rw [h]
    · rw [hch, hch']
      rfl

private theorem MergeSpec.rwN_eq (hs : MergeSpec Γ t) : t.g.rwN = Γ.rwN + convN Γ := by
  unfold Graph.rwN convN
  rw [hs.comps_eq]
  have h1 : ((Γ.comps.filterMap (mergeComp Γ.mrep t.f)).filter fun c => c.kind.isRg).length =
      (Γ.comps.filter fun c => c.kind.isRg || (c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y)).length := by
    apply count_filterMap
    intro c
    rcases hm : mergeComp Γ.mrep t.f c with _ | c'
    · obtain ⟨hk, -⟩ := mergeComp_none hm
      simp [hk, Kind.isRg, Kind.isSolid]
    · simp only
      by_cases hsol : c.kind.isSolid = true
      · rw [mergeComp_solid hsol] at hm
        obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
          cases hk : c.kind <;> simp_all [Kind.isSolid]
        split_ifs at hm with hr
        · obtain rfl := Option.some.inj hm
          show (c.kind.toWeight).isRg = (c.kind.isRg || (c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y))
          rw [hch]
          simp [Kind.toWeight, Kind.isRg, Kind.isSolid, hr]
        · obtain rfl := Option.some.inj hm
          simp [Comp.map, hch, hr, Kind.isRg]
      · have hsol' : c.kind.isSolid = false := by simpa using hsol
        rcases mergeComp_kind hm with h | ⟨ch, hch, -⟩
        · rw [h, hsol']
          simp
        · rw [hch] at hsol'
          cases hsol'
  have h2 := length_filter_or_add Γ.comps (fun c => c.kind.isRg)
    (fun c => c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y)
  have h3 : (Γ.comps.filter fun c => c.kind.isRg && (c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y))
      = [] := by
    rw [List.filter_eq_nil_iff]
    intro c _
    cases hk : c.kind <;> simp [Kind.isRg, Kind.isSolid]
  rw [h1]
  rw [h3, List.length_nil] at h2
  omega

/-- The number of converted solid components with an external end. -/
private def convExt (g : Graph k n) : ℕ :=
  (g.comps.filter fun c => (c.kind.isSolid && g.mrep c.x == g.mrep c.y) &&
    (c.x.isLeft || c.y.isLeft)).length

private theorem MergeSpec.eextN_eq (hs : MergeSpec Γ t) : t.g.eextN + convExt Γ = Γ.eextN := by
  unfold Graph.eextN convExt
  rw [hs.comps_eq]
  have h1 : ((Γ.comps.filterMap (mergeComp Γ.mrep t.f)).filter
      fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length =
      (Γ.comps.filter fun c => (c.kind.isSolid && (c.x.isLeft || c.y.isLeft)) &&
        !(c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y)).length := by
    apply count_filterMap
    intro c
    rcases hm : mergeComp Γ.mrep t.f c with _ | c'
    · obtain ⟨hk, -⟩ := mergeComp_none hm
      simp [hk, Kind.isSolid]
    · simp only
      by_cases hsol : c.kind.isSolid = true
      · rw [mergeComp_solid hsol] at hm
        obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
          cases hk : c.kind <;> simp_all [Kind.isSolid]
        split_ifs at hm with hr
        · obtain rfl := Option.some.inj hm
          show ((c.kind.toWeight).isSolid && ((t.f c.x).isLeft || (t.f c.x).isLeft)) =
            ((c.kind.isSolid && (c.x.isLeft || c.y.isLeft)) &&
              !(c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y))
          rw [hch]
          simp [Kind.toWeight, Kind.isSolid, hr]
        · obtain rfl := Option.some.inj hm
          simp [Comp.map, hch, hr, Kind.isSolid, hs.isLeft]
      · have hsol' : c.kind.isSolid = false := by simpa using hsol
        rcases mergeComp_kind hm with h | ⟨ch, hch, -⟩
        · rw [h, hsol']
          simp
        · rw [hch] at hsol'
          cases hsol'
  have h2 := (filter_split_perm Γ.comps (fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft))
    (fun c => c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y)).length_eq
  rw [List.length_append] at h2
  have e1 : (Γ.comps.filter fun c => (c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y) &&
      (c.x.isLeft || c.y.isLeft)) = Γ.comps.filter fun c =>
        (c.kind.isSolid && (c.x.isLeft || c.y.isLeft)) &&
          (c.kind.isSolid && Γ.mrep c.x == Γ.mrep c.y) := by
    apply List.filter_congr
    intro c _
    cases c.kind.isSolid <;> simp [Bool.and_comm]
  rw [h1, e1]
  omega

end MergeQuant


/-! ## Local views at an atom -/

section LocalView

variable {k n m : ℕ}

/-- The component is attached to `u`. -/
def atB {k n : ℕ} (u : Atom k n) (c : Comp (Atom k n)) : Bool := c.x == u || c.y == u

/-- The end of a solid component at `u`, as in `Graph.ends`. -/
private def endF {k n : ℕ} (u : Atom k n) (c : Comp (Atom k n)) : Option (Bool × Charge) :=
  match c.kind with
  | .G ch => if c.x = u ∧ c.y ≠ u then some (true, ch)
      else if c.y = u ∧ c.x ≠ u then some (false, ch) else none
  | _ => none

private theorem deg_local (g : Graph k n) (u : Atom k n) :
    g.deg u = ((g.comps.filter (atB u)).filter fun c => c.kind.isSolid).length := by
  unfold Graph.deg
  rw [List.filter_filter]
  congr 1

private theorem ends_local (g : Graph k n) (u : Atom k n) :
    g.ends u = (g.comps.filter (atB u)).filterMap (endF u) := by
  unfold Graph.ends
  rw [List.filterMap_filter]
  congr 1
  funext c
  by_cases h : atB u c = true
  · rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]
    have hx : c.x ≠ u := fun hx => h (by simp [atB, hx])
    have hy : c.y ≠ u := fun hy => h (by simp [atB, hy])
    cases c.kind <;> simp [hx, hy]

private theorem cs_local (g : Graph k n) (u : Atom k n) :
    (g.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u)) =
      (g.comps.filter (atB u)).filter fun c => c.kind != .xdot := by
  rw [List.filter_filter]
  rfl

/-- Two graphs with corresponding local lists at `u` and `u'` have the same degree, ends and
standard neutral status there. -/
private theorem local_transfer {g : Graph k n} {g' : Graph k m} {u : Atom k n} {u' : Atom k m}
    (f : Atom k n → Atom k m) (hf : ∀ a, f a = u' ↔ a = u)
    (h : g'.comps.filter (atB u') = (g.comps.filter (atB u)).map (Comp.map f)) :
    g'.deg u' = g.deg u ∧ g'.ends u' = g.ends u ∧ g'.stdNeutralAt u' = g.stdNeutralAt u := by
  have hends : g'.ends u' = g.ends u := by
    rw [ends_local, ends_local, h, List.filterMap_map]
    congr 1
    funext c
    simp only [Function.comp, endF, Comp.map, ne_eq]
    have h1 : (f c.x = u') ↔ (c.x = u) := hf c.x
    have h2 : (f c.y = u') ↔ (c.y = u) := hf c.y
    simp only [h1, h2]
  have hcs : (g'.comps.filter fun c => c.kind != .xdot && (c.x == u' || c.y == u')) =
      (g.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u)).map (Comp.map f) := by
    rw [cs_local, cs_local, h, List.filter_map]
    rfl
  refine ⟨?_, hends, ?_⟩
  · rw [deg_local, deg_local, h, List.filter_map, List.length_map]
    rfl
  · unfold Graph.stdNeutralAt
    simp only
    rw [hcs, hends]
    simp only [List.filter_map, List.length_map, Function.comp_def, Comp.map]

variable {Γ : Graph k n} {t : Tracked k n}

/-- At an atom whose image is the image of no other atom, with no solid edge in a block and no
dotted loop attached, the components of the merge are the images of the components of `Γ`. -/
private theorem MergeSpec.local_eq (hs : MergeSpec Γ t) {w : Atom k n}
    (hfib : ∀ u, t.f u = t.f w → u = w)
    (hloop : ∀ c ∈ Γ.comps, c.kind = .dot → c.x ≠ c.y)
    (hconv : ∀ c ∈ Γ.comps, (c.x = w ∨ c.y = w) → c.kind.isSolid = true →
      Γ.mrep c.x ≠ Γ.mrep c.y) :
    t.g.comps.filter (atB (t.f w)) = (Γ.comps.filter (atB w)).map (Comp.map t.f) := by
  rw [hs.comps_eq]
  have hfw : ∀ a, (t.f a == t.f w) = (a == w) := by
    intro a
    by_cases ha : a = w
    · simp [ha]
    · have : t.f a ≠ t.f w := fun h' => ha (hfib a h')
      simp [ha, this]
  have key : ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, c ∈ Γ.comps) →
      (L.filterMap (mergeComp Γ.mrep t.f)).filter (atB (t.f w)) =
        (L.filter (atB w)).map (Comp.map t.f) := by
    intro L hL
    induction L with
    | nil => rfl
    | cons c L ih =>
      have ih' := ih fun d hd => hL d (List.mem_cons_of_mem _ hd)
      have hc := hL c (List.mem_cons_self ..)
      by_cases hat : atB w c = true
      · have hat' : c.x = w ∨ c.y = w := by simpa [atB] using hat
        have hm : mergeComp Γ.mrep t.f c = some (c.map t.f) := by
          by_cases hk : c.kind = .dot
          · rw [mergeComp_dot hk]
            have : t.f c.x ≠ t.f c.y := by
              intro h'
              rcases hat' with hx | hy
              · exact hloop c hc hk (hx.trans (hfib c.y (h'.symm.trans (by rw [hx]))).symm)
              · exact hloop c hc hk ((hfib c.x (h'.trans (by rw [hy]))).trans hy.symm)
            rw [ite_eq_right this]
          · by_cases hsol : c.kind.isSolid = true
            · rw [mergeComp_solid hsol, ite_eq_right (hconv c hc hat' hsol)]
            · exact mergeComp_other hk (by simpa using hsol)
        rw [List.filterMap_cons_some hm, List.filter_cons, List.filter_cons, hat]
        have : atB (t.f w) (c.map t.f) = true := by
          simp only [atB, Comp.map, hfw]
          simpa [atB] using hat
        rw [this]
        simp [ih']
      · have hat' : c.x ≠ w ∧ c.y ≠ w := by simpa [atB, not_or] using hat
        rw [List.filter_cons, ite_eq_right hat]
        rcases hm : mergeComp Γ.mrep t.f c with _ | c'
        · rw [List.filterMap_cons_none hm]
          exact ih'
        · rw [List.filterMap_cons_some hm, List.filter_cons]
          have hno : atB (t.f w) c' = false := by
            unfold mergeComp at hm
            split_ifs at hm
            · obtain rfl := Option.some.inj hm
              simp [atB, Comp.map, hfw, hat'.1]
            · obtain rfl := Option.some.inj hm
              simp [atB, Comp.map, hfw, hat'.1, hat'.2]
          rw [hno]
          simpa using ih'
  exact key Γ.comps fun c hc => hc

/-- No two distinct internal atoms of a merge lie in one block. -/
private theorem MergeSpec.sepInt (hs : MergeSpec Γ t) : t.g.SepInt := by
  intro a b hab
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  obtain ⟨i, rfl⟩ := hgs a
  obtain ⟨j, rfl⟩ := hgs b
  rw [← hg, ← hg] at hab
  have h1 := hs.sameBlock_of_map hab
  have h2 := hs.f_eq _ _ ((Γ.mrep_eq_iff _ _).2 h1) rfl rfl
  rw [hg, hg] at h2
  exact Sum.inr.inj h2

/-- The merge keeps the `×`-dotted edges outside blocks. -/
private theorem MergeSpec.xdotApart (hs : MergeSpec Γ t) : t.g.XdotApart := by
  intro c' hc' hk' hb
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .xdot := h ▸ hk'
    have hsol : c.kind.isSolid = false := by rw [hck]; rfl
    have hd : c.kind ≠ .dot := by rw [hck]; simp
    rw [mergeComp_other hd hsol] at hm
    obtain rfl := Option.some.inj hm
    exact hs.xdot_ne c hc hck ((Γ.mrep_eq_iff _ _).2 (hs.sameBlock_of_map hb))
  · rw [hch'] at hk'
    cases hk'

end LocalView


/-! ## `O_dot` outputs of the same reduced order: the merge-free case -/

section DotCaseC

variable {k n m : ℕ}

private theorem filter_imp_of_length_eq {α : Type*} (L : List α) (P Q : α → Bool)
    (h : ∀ c ∈ L, P c = true → Q c = true) (hl : (L.filter P).length = (L.filter Q).length) :
    ∀ c ∈ L, Q c = true → P c = true := by
  induction L with
  | nil => intro c hc; simp at hc
  | cons a L ih =>
    have hle := length_filter_mono L P Q fun c hc => h c (List.mem_cons_of_mem _ hc)
    have ha := h a (List.mem_cons_self ..)
    rw [List.filter_cons, List.filter_cons] at hl
    intro c hc hQ
    by_cases hPa : P a = true
    · simp only [hPa, ha hPa, ite_true, List.length_cons, Nat.add_right_cancel_iff] at hl
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hPa
      · exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd)) hl c hc hQ
    · by_cases hQa : Q a = true
      · simp only [hPa, hQa, ite_true, Bool.false_eq_true, ite_false, List.length_cons] at hl
        omega
      · simp only [hPa, hQa, Bool.false_eq_true, ite_false] at hl
        rcases List.mem_cons.1 hc with rfl | hc
        · exact absurd hQ hQa
        · exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd)) hl c hc hQ

/-- The scaling quantities are kept by a bijective map of the atoms that fixes the external
atoms. -/
private theorem phi_map_bij {f : Atom k n → Atom k m} (g : Fin n ≃ Fin m)
    (hfl : ∀ a, f (.inl a) = .inl a) (hfr : ∀ i, f (.inr i) = .inr (g i))
    (L : List (Comp (Atom k n))) (co co' : Coeff) :
    (⟨L.map (Comp.map f), co'⟩ : Graph k m).phi = (⟨L, co⟩ : Graph k n).phi := by
  have hf : Function.Injective f := by
    intro u v huv
    rcases u with a | i <;> rcases v with b | j
    · rw [hfl, hfl] at huv; rw [Sum.inl.inj huv]
    · rw [hfl, hfr] at huv; cases huv
    · rw [hfr, hfl] at huv; cases huv
    · rw [hfr, hfr] at huv; rw [g.injective (Sum.inr.inj huv)]
  have h1 : (⟨L.map (Comp.map f), co'⟩ : Graph k m).lwN = (⟨L, co⟩ : Graph k n).lwN := by
    simp only [Graph.lwN, List.filter_map, List.length_map]
    rfl
  have h2 : (⟨L.map (Comp.map f), co'⟩ : Graph k m).rwN = (⟨L, co⟩ : Graph k n).rwN := by
    simp only [Graph.rwN, List.filter_map, List.length_map]
    rfl
  have hdeg : ∀ i, (⟨L.map (Comp.map f), co'⟩ : Graph k m).deg (.inr (g i)) =
      (⟨L, co⟩ : Graph k n).deg (.inr i) := by
    intro i
    rw [← hfr]
    exact deg_map_inj hf L co co' _
  have hstd : ∀ i, (⟨L.map (Comp.map f), co'⟩ : Graph k m).stdNeutralAt (.inr (g i)) =
      (⟨L, co⟩ : Graph k n).stdNeutralAt (.inr i) := by
    intro i
    rw [← hfr]
    exact stdNeutralAt_map_inj hf L co co' _
  have h3 : (⟨L.map (Comp.map f), co'⟩ : Graph k m).degX = (⟨L, co⟩ : Graph k n).degX := by
    unfold Graph.degX
    rw [← g.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [hdeg]
  have h4 : (⟨L.map (Comp.map f), co'⟩ : Graph k m).badN = (⟨L, co⟩ : Graph k n).badN := by
    unfold Graph.badN
    rw [Finset.card_filter, Finset.card_filter, ← g.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [hdeg, hstd]
  simp only [Graph.phi, h1, h2, h3, h4]

variable {h : Graph k n}

open Classical in
/-- The converted components are exactly the solid components without `×`-dotted partner whose
ends lie in one block. -/
private theorem convN_eq {A : List (Atom k n × Atom k n × Bool)} {t : Tracked k n}
    (hm : (h.dotChoice h.splitPairs A).mergeT = some t) :
    convN (h.dotChoice h.splitPairs A) = (h.comps.filter fun c => unpB h c &&
      decide ((dg (h.dotChoice h.splitPairs A).comps).Reachable c.x c.y)).length := by
  set dc := h.dotChoice h.splitPairs A with hdc
  unfold convN
  have hc1 : (dc.comps.filter fun c => c.kind.isSolid && dc.mrep c.x == dc.mrep c.y) =
      (keptComps h h.splitPairs).filter fun c => c.kind.isSolid && dc.mrep c.x == dc.mrep c.y := by
    rw [hdc, dc_comps, List.filter_append]
    have : (addedComps h.splitPairs A).filter
        (fun c => c.kind.isSolid && (h.dotChoice h.splitPairs A).mrep c.x ==
          (h.dotChoice h.splitPairs A).mrep c.y) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      rcases (addedComps_label hc).2 with hk | hk <;> simp [hk, Kind.isSolid]
    rw [this, List.append_nil]
  rw [hc1]
  unfold keptComps
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro c hc
  by_cases hs : c.kind.isSolid = true
  · have hx : (c.kind == Kind.xdot) = false := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    by_cases hr : dc.mrep c.x = dc.mrep c.y
    · have hun := conv_unp hm hc hs hr
      have hre : (dg dc.comps).Reachable c.x c.y := (dc.mrep_eq_iff c.x c.y).1 hr
      simp only [unpB, hs, hr, hx, hun, hre, beq_self_eq_true, Bool.and_self, Bool.not_false,
        decide_true, Bool.true_and, Bool.false_and]
    · have hre : ¬ dc.SameBlock c.x c.y := fun h' => hr ((dc.mrep_eq_iff c.x c.y).2 h')
      have : ¬ (dg dc.comps).Reachable c.x c.y := hre
      simp [unpB, hs, hr, this]
  · have hs' : c.kind.isSolid = false := by simpa using hs
    simp [unpB, hs']

open Classical in
/-- `O_dot` outputs with no merge of blocks and no converted solid edge: the same quantities as
the input. -/
private theorem dot_caseC (hd : DotIn h) (hsep : h.SepInt) {A : List (Atom k n × Atom k n × Bool)}
    (hA : List.Sublist A h.splitPairs) {t : Tracked k n}
    (hm : (h.dotChoice h.splitPairs A).mergeT = some t)
    (hJ : ∀ a b, (dg (h.dotChoice h.splitPairs A).comps).Reachable a b → (dg h.comps).Reachable a b)
    (he : convN (h.dotChoice h.splitPairs A) = 0) :
    t.g.phi = h.phi ∧ t.g.eextN = h.eextN := by
  set dc := h.dotChoice h.splitPairs A with hdc
  have hs := mergeT_spec hm
  -- no dotted edge is added
  have hA0 : A = [] := by
    by_contra hne
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
    have hpSP := hA.subset hp
    have hdot : mkC .dot p.1 p.2.1 ∈ dc.comps := by
      rw [hdc, dc_comps]
      exact List.mem_append_right _ (mem_addedComps.2 ⟨p, hpSP, Or.inl ⟨hp, rfl⟩⟩)
    have hr : (dg h.comps).Reachable p.1 p.2.1 := hJ _ _ (dg_reach_of_mem hdot rfl)
    obtain ⟨-, hne', hpb⟩ := mem_splitPairs.1 hpSP
    cases hflag : p.2.2
    · -- a pair without solid edge: its `×`-dotted edge would be inside a block
      have hx : spJoined h (· == .xdot) p.1 p.2.1 = true := by
        rw [hflag] at hpb
        rw [← hpb] at hne'
        simpa using hne'
      rw [spJoined_iff] at hx
      obtain ⟨d, hd', hdk, hdxy⟩ := hx
      apply hd.xa d hd' (by simpa using hdk)
      rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hr
      · rw [h1, h2]; exact hr.symm
    · -- a pair with a solid edge: that edge would be converted
      have hsj : spJoined h Kind.isSolid p.1 p.2.1 = true := by rw [← hpb, hflag]
      have hxj : spJoined h (· == .xdot) p.1 p.2.1 = false := by
        rw [hsj] at hne'
        simpa using hne'
      rw [spJoined_iff] at hsj
      obtain ⟨c, hc, hcs, hcxy⟩ := hsj
      have hun : unpB h c = true := by
        simp only [unpB, hcs, Bool.true_and, Bool.not_eq_true']
        by_contra hx
        simp only [Bool.not_eq_false] at hx
        rw [hasXdot_iff] at hx
        obtain ⟨d, hd', hdk, hdxy⟩ := hx
        have : spJoined h (· == .xdot) p.1 p.2.1 = true := by
          rw [spJoined_iff]
          refine ⟨d, hd', by simp [hdk], ?_⟩
          rcases hcxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
            simp_all
        rw [hxj] at this
        cases this
      have hcr : (dg dc.comps).Reachable c.x c.y := by
        have := dg_reach_of_mem hdot rfl
        rcases hcxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact this
        · rw [h1, h2]; exact this.symm
      have hpos := convN_eq hm
      rw [← hdc, he] at hpos
      have : 0 < (h.comps.filter fun c => unpB h c &&
          decide ((dg dc.comps).Reachable c.x c.y)).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨hc, by simp [hun, hcr]⟩)
      omega
  subst hA0
  -- the merge is injective
  have hinj : Function.Injective t.f := by
    intro u v huv
    by_contra hne
    obtain ⟨hu, hv⟩ := hs.isRight_of_f_eq huv hne
    have hb := hJ _ _ (hs.sameBlock_of_f_eq huv)
    rcases u with a | i
    · simp at hu
    rcases v with b | j
    · simp at hv
    exact hne (by rw [hsep i j hb])
  -- every component is mapped
  have hdl : ∀ c ∈ dc.comps, c.kind = .dot → c.x ≠ c.y := by
    intro c hc hk
    rw [hdc, dc_comps] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact (hd.plain c ((mem_keptComps _ _ _).1 hc).1).2.2.2.1 hk
    · obtain ⟨p, -, ⟨hpA, -⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 hc
      · simp at hpA
      · simp [mkC] at hk
  have hcomps : t.g.comps = dc.comps.map (Comp.map t.f) := by
    rw [hs.comps_eq]
    apply List.filterMap_eq_map_iff_forall_eq_some.2
    intro c hc
    by_cases hk : c.kind = .dot
    · rw [mergeComp_dot hk, ite_eq_right fun h' => hdl c hc hk (hinj h')]
    · by_cases hsol : c.kind.isSolid = true
      · have hr : dc.mrep c.x ≠ dc.mrep c.y := by
          intro hr
          have hpos : 0 < convN dc := List.length_pos_of_mem (List.mem_filter.2 ⟨hc, by
            simp [hsol, hr]⟩)
          omega
        rw [mergeComp_solid hsol, ite_eq_right hr]
      · exact mergeComp_other hk (by simpa using hsol)
  -- the quantities
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have hgi : Function.Injective g := by
    intro i j hij
    have := hinj (show t.f (.inr i) = t.f (.inr j) by rw [hg, hg, hij])
    exact Sum.inr.inj this
  have hphi : t.g.phi = dc.phi := by
    have key := phi_map_bij (f := t.f) (Equiv.ofBijective g ⟨hgi, hgs⟩) hs.f_inl hg dc.comps
      dc.coeff t.g.coeff
    rw [← key]
    rcases ht : t.g with ⟨cs, co⟩
    rw [ht] at hcomps
    simp only at hcomps
    rw [hcomps]
  have hnoX : dc.noX = h.noX := by
    unfold Graph.noX
    rw [hdc, dc_comps, List.filter_append]
    have : (addedComps h.splitPairs []).filter (fun c => c.kind != .xdot) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨p, -, ⟨hpA, -⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 hc
      · simp at hpA
      · simp [mkC]
    rw [this, List.append_nil]
    unfold keptComps
    rw [List.filter_filter]
    apply List.filter_congr
    intro c _
    by_cases hk : c.kind = .xdot <;> simp [hk]
  refine ⟨hphi.trans (phi_eq_of_noX hnoX), ?_⟩
  have h1 := hs.eextN_eq
  have h2 : convExt dc = 0 := by
    have hle : convExt dc ≤ convN dc := length_filter_mono _ _ _ fun c _ hc => by
      simp only [Bool.and_eq_true] at hc ⊢
      exact hc.1
    omega
  rw [h2, add_zero] at h1
  rw [h1]
  exact eextN_eq_of_noX hnoX

end DotCaseC


/-! ## `O_dot` outputs of the same reduced order: one merge -/

section DotCaseD

variable {k n m : ℕ}

private theorem local_noX {g g' : Graph k n} {u : Atom k n}
    (h : (g.comps.filter (atB u)).filter (fun c => c.kind != .xdot) =
      (g'.comps.filter (atB u)).filter (fun c => c.kind != .xdot)) :
    g.deg u = g'.deg u ∧ g.stdNeutralAt u = g'.stdNeutralAt u := by
  have hd : ∀ g : Graph k n, g.deg u =
      (((g.comps.filter (atB u)).filter fun c => c.kind != .xdot).filter
        fun c => c.kind.isSolid).length := by
    intro g
    rw [deg_local]
    congr 1
    conv_rhs => rw [List.filter_filter]
    apply List.filter_congr
    intro c _
    cases hk : c.kind <;> simp [Kind.isSolid]
  have he : ∀ g : Graph k n, g.ends u =
      ((g.comps.filter (atB u)).filter fun c => c.kind != .xdot).filterMap (endF u) := by
    intro g
    rw [ends_local]
    conv_rhs => rw [List.filterMap_filter]
    congr 1
    funext c
    by_cases hk : c.kind = .xdot
    · simp [hk, endF]
    · simp [hk]
  refine ⟨by rw [hd g, hd g', h], ?_⟩
  unfold Graph.stdNeutralAt
  rw [cs_local, cs_local, he g, he g', h]

private theorem sum_erase_image {β : Type*} [AddCommMonoid β] (g : Fin n → Fin m)
    (hgs : Function.Surjective g) (iα iv : Fin n) (hne : iα ≠ iv) (hg : g iα = g iv)
    (hinj : ∀ i j, g i = g j → i = j ∨ (i = iα ∧ j = iv) ∨ (i = iv ∧ j = iα)) (F : Fin m → β) :
    ∑ j, F j = ∑ i ∈ Finset.univ.erase iα, F (g i) := by
  have himg : (Finset.univ.erase iα).image g = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨i, rfl⟩ := hgs j
    rw [Finset.mem_image]
    by_cases hi : i = iα
    · exact ⟨iv, Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩, by rw [hi, hg]⟩
    · exact ⟨i, Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩, rfl⟩
  rw [← himg, Finset.sum_image]
  intro i hi j hj hij
  rcases hinj i j hij with h | ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h
  · exact absurd h1 (Finset.mem_erase.1 hi).1
  · exact absurd h2 (Finset.mem_erase.1 hj).1

variable {h : Graph k n}

private theorem deg_dc (h : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) (u : Atom k n) :
    (h.dotChoice SP A).deg u = h.deg u := by
  unfold Graph.deg
  rw [dc_comps, List.filter_append]
  have : (addedComps SP A).filter (fun c => c.kind.isSolid && (c.x == u || c.y == u)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    rcases (addedComps_label hc).2 with hk | hk <;> simp [hk, Kind.isSolid]
  rw [this, List.append_nil]
  unfold keptComps
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro c _
  by_cases hs : c.kind.isSolid = true
  · have : (c.kind == Kind.xdot) = false := by cases hk : c.kind <;> simp_all [Kind.isSolid]
    simp [hs, this]
  · simp [hs]

end DotCaseD


/-! ## `O_dot` outputs of the same reduced order: one merge, the quantities -/

section DotCaseD2

variable {k n : ℕ} {h : Graph k n}

private theorem pair_eq {α : Type*} {x y a v w : α} (h1 : x = a ∧ y = v ∨ x = v ∧ y = a)
    (h2 : x = a ∧ y = w ∨ x = w ∧ y = a) (hav : a ≠ v) : w = v := by
  rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases h2 with ⟨e3, e4⟩ | ⟨e3, e4⟩
  · exact e4.symm.trans e2
  · exact absurd (e4.symm.trans e2) hav
  · exact absurd (e3.symm.trans e1) hav
  · exact e3.symm.trans e1

private theorem count_merge {α : Type*} (L : List α) (P Q R : α → Bool)
    (hR : ∀ c ∈ L, R c = true → P c = true ∧ Q c = true) :
    (L.filter fun c => (P c || Q c) && !R c).length + 2 * (L.filter R).length ≤
      (L.filter P).length + (L.filter Q).length := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have ih' := ih fun d hd => hR d (List.mem_cons_of_mem _ hd)
    have hc := hR c (List.mem_cons_self ..)
    simp only [List.filter_cons]
    by_cases hr : R c = true
    · obtain ⟨hp, hq⟩ := hc hr
      simp only [hp, hq, hr, Bool.or_self, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ite_false, ite_true, List.length_cons]
      omega
    · have hr' : R c = false := by simpa using hr
      by_cases hp : P c = true <;> by_cases hq : Q c = true <;>
        simp only [hp, hq, hr', Bool.or_self, Bool.or_true, Bool.true_or, Bool.not_false,
          Bool.and_true, Bool.false_eq_true, ite_false, ite_true, List.length_cons, Bool.or_false,
          Bool.false_or] <;> omega

/-- `dotChoice` keeps the components other than dotted and `×`-dotted edges. -/
theorem dc_count (h : Graph k n) (SP A : List (Atom k n × Atom k n × Bool))
    (P : Kind → Bool) (hd : P .dot = false) (hx : P .xdot = false) (Q : Comp (Atom k n) → Bool) :
    ((h.dotChoice SP A).comps.filter fun c => P c.kind && Q c).length =
      (h.comps.filter fun c => P c.kind && Q c).length := by
  rw [dc_comps, List.filter_append]
  have : (addedComps SP A).filter (fun c => P c.kind && Q c) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    rcases (addedComps_label hc).2 with hk | hk <;> simp [hk, hd, hx]
  rw [this, List.append_nil]
  unfold keptComps
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro c _
  by_cases hk : c.kind = .xdot
  · simp [hk, hx]
  · simp [hk]

set_option maxHeartbeats 1000000 in
open Classical in
private theorem dot_caseD_aux {nw : Atom k n → Bool} (hd : DotIn h) (hn : DotNew h 0 nw)
    (hsep : h.SepInt) {A : List (Atom k n × Atom k n × Bool)} {t : Tracked k n} (hm : (h.dotChoice h.splitPairs A).mergeT = some t) {a b : Atom k n}
    (hna : nw a = true) (hab : ¬ (dg h.comps).Reachable a b)
    (hstr : ∀ u v, (dg (h.dotChoice h.splitPairs A).comps).Reachable u v →
      (dg h.comps).Reachable u v ∨ ((dg h.comps).Reachable u a ∧ (dg h.comps).Reachable v b) ∨
        ((dg h.comps).Reachable u b ∧ (dg h.comps).Reachable v a))
    (he : convN (h.dotChoice h.splitPairs A) = 2)
    (hext : convExt (h.dotChoice h.splitPairs A) = 0) :
    ∃ α v : Atom k n, nw α = true ∧ v.isRight = true ∧ α ≠ v ∧ h.deg α = 2 ∧
      (∀ c ∈ h.comps, unpB h c = true → atB α c = true →
        (c.x = α ∧ c.y = v ∨ c.x = v ∧ c.y = α)) ∧
      t.g.eextN = h.eextN ∧ t.g.lwN = h.lwN ∧
      t.g.phi ≤ h.phi + 2 := by
  set dc := h.dotChoice h.splitPairs A with hdc
  have hs := mergeT_spec hm
  have hnd : ∀ c ∈ h.comps, c.kind = .dot → nw c.x = false ∧ nw c.y = false :=
    fun c hc hk => hn.noDot c hc (Or.inl hk)
  set X := h.comps.filter fun c => unpB h c && decide ((dg dc.comps).Reachable c.x c.y) with hX
  have hXlen : X.length = 2 := by
    have := convN_eq hm
    rw [← hdc] at this
    rw [hX, ← this, he]
  have hXmem : ∀ c ∈ X, c ∈ h.comps ∧ unpB h c = true ∧ (dg dc.comps).Reachable c.x c.y := by
    intro c hc
    rw [hX, List.mem_filter] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2⟩
  have hsolU : ∀ c, unpB h c = true → c.kind.isSolid = true := by
    intro c hc
    simp only [unpB, Bool.and_eq_true] at hc
    exact hc.1
  have hkept : ∀ c ∈ h.comps, c.kind.isSolid = true → c ∈ dc.comps := by
    intro c hc hsol
    rw [hdc, dc_comps]
    refine List.mem_append_left _ ((mem_keptComps _ _ _).2 ⟨hc, ?_⟩)
    rintro ⟨hk, -⟩
    rw [hk] at hsol
    cases hsol
  -- the converted edges join internal atoms
  have hXint : ∀ c ∈ X, c.x.isRight = true ∧ c.y.isRight = true := by
    intro c hc
    obtain ⟨hch, hu, hr⟩ := hXmem c hc
    have hsol := hsolU c hu
    have hrep : dc.mrep c.x = dc.mrep c.y := (dc.mrep_eq_iff _ _).2 hr
    by_contra hcon
    have hlt : 0 < convExt dc := by
      refine List.length_pos_of_mem (List.mem_filter.2 ⟨hkept c hch hsol, ?_⟩)
      have : (c.x.isLeft || c.y.isLeft) = true := by
        rcases hx : c.x with x | x <;> rcases hy : c.y with y | y <;> simp_all
      simp [hsol, hrep, this]
    omega
  -- each converted edge joins `a` to an internal atom of the block of `b`
  have hXa : ∀ c ∈ X, (c.x = a ∧ (dg h.comps).Reachable c.y b) ∨
      (c.y = a ∧ (dg h.comps).Reachable c.x b) := by
    intro c hc
    obtain ⟨hch, hu, hr⟩ := hXmem c hc
    have hloop := hd.noLoop c hch (hsolU c hu)
    rcases hstr c.x c.y hr with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      obtain ⟨hx, hy⟩ := hXint c hc
      rcases hcx : c.x with x | x
      · rw [hcx] at hx; cases hx
      rcases hcy : c.y with y | y
      · rw [hcy] at hy; cases hy
      rw [hcx, hcy] at h0
      exact hloop (by rw [hcx, hcy, hsep x y h0])
    · exact Or.inl ⟨(reach_new hnd hna h1.symm).symm, h2⟩
    · exact Or.inr ⟨(reach_new hnd hna h2.symm).symm, h1⟩
  -- the atom `v`
  obtain ⟨c₁, hc₁⟩ : ∃ c, c ∈ X := List.exists_mem_of_length_pos (by omega)
  obtain ⟨v, hvR, hvb, hc₁v⟩ : ∃ v : Atom k n, v.isRight = true ∧ (dg h.comps).Reachable v b ∧
      (c₁.x = a ∧ c₁.y = v ∨ c₁.x = v ∧ c₁.y = a) := by
    rcases hXa c₁ hc₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨c₁.y, (hXint c₁ hc₁).2, h2, Or.inl ⟨h1, rfl⟩⟩
    · exact ⟨c₁.x, (hXint c₁ hc₁).1, h2, Or.inr ⟨rfl, h1⟩⟩
  have hav : a ≠ v := by
    intro hav
    apply hab
    rw [hav]
    exact hvb
  have hvuniq : ∀ w : Atom k n, w.isRight = true → (dg h.comps).Reachable w b → w = v := by
    intro w hw hwb
    rcases hwc : w with x | x
    · rw [hwc] at hw; cases hw
    rcases hvc : v with y | y
    · rw [hvc] at hvR; cases hvR
    have : (dg h.comps).Reachable (.inr x) (.inr y) := by
      rw [← hwc, ← hvc]
      exact hwb.trans hvb.symm
    rw [hsep x y this]
  have hXav : ∀ c ∈ X, c.x = a ∧ c.y = v ∨ c.x = v ∧ c.y = a := by
    intro c hc
    rcases hXa c hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, hvuniq _ (hXint c hc).2 h2⟩
    · exact Or.inr ⟨hvuniq _ (hXint c hc).1 h2, h1⟩
  -- the edges without partner at `a` are the two converted edges
  have hUa : ∀ c ∈ h.comps, unpB h c = true → atB a c = true →
      c ∈ X := by
    have hsub : ∀ c ∈ h.comps, (unpB h c && decide ((dg dc.comps).Reachable c.x c.y)) = true →
        (unpB h c && (c.x == a || c.y == a)) = true := by
      intro c hc hP
      have hcX : c ∈ X := by rw [hX]; exact List.mem_filter.2 ⟨hc, hP⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
      rcases hXav c hcX with ⟨h1, -⟩ | ⟨-, h2⟩
      · simp [hP.1, h1]
      · simp [hP.1, h2]
    have hlen : X.length = (h.comps.filter fun c => unpB h c && (c.x == a || c.y == a)).length := by
      have h1 := length_filter_mono h.comps _ _ hsub
      have h2 := hn.two a hna
      rw [← hX] at h1
      omega
    intro c hc hu hat
    have := filter_imp_of_length_eq h.comps _ _ hsub hlen c hc (by
      simp only [atB] at hat
      simp [hu, hat])
    rw [hX]
    exact List.mem_filter.2 ⟨hc, this⟩
  -- every solid edge at `a` has no partner
  have hnoXa : ∀ c ∈ h.comps, atB a c = true → h.hasXdot c.x c.y = false := by
    intro c hc hat
    by_contra hx
    simp only [Bool.not_eq_false, hasXdot_iff] at hx
    obtain ⟨d, hd', hdk, hdxy⟩ := hx
    obtain ⟨h1, h2⟩ := hn.noDot d hd' (Or.inr hdk)
    simp only [atB, Bool.or_eq_true, beq_iff_eq] at hat
    rcases hat with hat | hat <;> rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h3, hat, hna] at h1; cases h1
    · rw [h4, hat, hna] at h2; cases h2
    · rw [h4, hat, hna] at h2; cases h2
    · rw [h3, hat, hna] at h1; cases h1
  have hdega : h.deg a = 2 := by
    rw [deg_local]
    have : ((h.comps.filter (atB a)).filter fun c => c.kind.isSolid) =
        h.comps.filter fun c => unpB h c && (c.x == a || c.y == a) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro c hc
      by_cases hat : atB a c = true
      · have := hnoXa c hc hat
        rw [hat]
        simp only [atB] at hat
        simp [unpB, this, hat]
      · have hat' : (c.x == a || c.y == a) = false := by simpa [atB] using hat
        simp [hat', atB]
    rw [this]
    have hle := hn.two a hna
    have hge : X.length ≤ (h.comps.filter fun c => unpB h c && (c.x == a || c.y == a)).length := by
      rw [hX]
      refine length_filter_mono _ _ _ fun c hc hP => ?_
      have hcX : c ∈ X := by rw [hX]; exact List.mem_filter.2 ⟨hc, hP⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
      rcases hXav c hcX with ⟨h1, -⟩ | ⟨-, h2⟩
      · simp [hP.1, h1]
      · simp [hP.1, h2]
    omega
  have haR : a.isRight = true := by
    rcases hc₁v with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [← h1]; exact (hXint c₁ hc₁).1
    · rw [← h2]; exact (hXint c₁ hc₁).2
  -- the fibres of the atom map
  have hfav : t.f a = t.f v := by
    have hr : (dg dc.comps).Reachable a v := by
      have := (hXmem c₁ hc₁).2.2
      rcases hc₁v with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at this; exact this
      · rw [h1, h2] at this; exact this.symm
    exact hs.f_eq _ _ ((dc.mrep_eq_iff _ _).2 hr) haR hvR
  have hfib : ∀ u w, t.f u = t.f w → u = w ∨ (u = a ∧ w = v) ∨ (u = v ∧ w = a) := by
    intro u w huw
    by_cases hne : u = w
    · exact Or.inl hne
    obtain ⟨hu, hw⟩ := hs.isRight_of_f_eq huw hne
    have hr := hs.sameBlock_of_f_eq huw
    rcases hstr u w hr with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      rcases hcu : u with x | x
      · rw [hcu] at hu; cases hu
      rcases hcw : w with y | y
      · rw [hcw] at hw; cases hw
      rw [hcu, hcw] at h0
      exact hne (by rw [hcu, hcw, hsep x y h0])
    · exact Or.inr (Or.inl ⟨(reach_new hnd hna h1.symm).symm, hvuniq w hw h2⟩)
    · exact Or.inr (Or.inr ⟨hvuniq u hu h1, (reach_new hnd hna h2.symm).symm⟩)
  -- the converted edges are the two edges between `a` and `v`
  have hconvX : ∀ c ∈ dc.comps, c.kind.isSolid = true → dc.mrep c.x = dc.mrep c.y →
      (c.x = a ∧ c.y = v ∨ c.x = v ∧ c.y = a) := by
    intro c hc hsol hr
    have hch : c ∈ h.comps := by
      rw [hdc, dc_comps] at hc
      rcases List.mem_append.1 hc with hc | hc
      · exact ((mem_keptComps _ _ _).1 hc).1
      · rcases (addedComps_label hc).2 with hk | hk <;> rw [hk] at hsol <;> cases hsol
    have hun := conv_unp hm hch hsol hr
    have hcX : c ∈ X := by
      rw [hX]
      refine List.mem_filter.2 ⟨hch, ?_⟩
      have hre : (dg dc.comps).Reachable c.x c.y := (dc.mrep_eq_iff _ _).1 hr
      simp [unpB, hsol, hun, hre]
    exact hXav c hcX
  -- the dotted edges of `dc` join distinct atoms
  have hdl : ∀ c ∈ dc.comps, c.kind = .dot → c.x ≠ c.y := by
    intro c hc hk
    rw [hdc, dc_comps] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact (hd.plain c ((mem_keptComps _ _ _).1 hc).1).2.2.2.1 hk
    · obtain ⟨p, hp, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 hc
      · simp only [mkC]
        intro hpp
        obtain ⟨-, hne', hpb⟩ := mem_splitPairs.1 hp
        cases hflag : p.2.2
        · have hx : spJoined h (· == .xdot) p.1 p.2.1 = true := by
            rw [hflag] at hpb
            rw [← hpb] at hne'
            simpa using hne'
          rw [spJoined_iff] at hx
          obtain ⟨d, hd', hdk, hdxy⟩ := hx
          apply hd.xa d hd' (by simpa using hdk)
          have : d.x = d.y := by
            rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hpp]
          rw [this]
          exact SimpleGraph.Reachable.refl _
        · have hsj : spJoined h Kind.isSolid p.1 p.2.1 = true := by rw [← hpb, hflag]
          rw [spJoined_iff] at hsj
          obtain ⟨c, hc', hcs, hcxy⟩ := hsj
          apply hd.noLoop c hc' hcs
          rcases hcxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hpp]
      · simp [mkC] at hk
  -- the added dotted edges join `a` and `v`
  have hadded : ∀ c ∈ addedComps h.splitPairs A, c.kind = .dot →
      (c.x = a ∧ c.y = v ∨ c.x = v ∧ c.y = a) := by
    intro c hc hk
    obtain ⟨p, hp, ⟨hpA, rfl⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 hc
    · simp only [mkC]
      have hcdc : mkC .dot p.1 p.2.1 ∈ dc.comps := by
        rw [hdc, dc_comps]
        exact List.mem_append_right _ hc
      have hr : (dg dc.comps).Reachable p.1 p.2.1 := dg_reach_of_mem hcdc rfl
      obtain ⟨-, hne', hpb⟩ := mem_splitPairs.1 hp
      -- the pair is joined in `h` by an edge without partner or by a `×`-dotted edge
      have hjoin : (∃ c ∈ h.comps, unpB h c = true ∧
          (c.x = p.1 ∧ c.y = p.2.1 ∨ c.x = p.2.1 ∧ c.y = p.1)) ∨
          (∃ d ∈ h.comps, d.kind = .xdot ∧
            (d.x = p.1 ∧ d.y = p.2.1 ∨ d.x = p.2.1 ∧ d.y = p.1)) := by
        cases hflag : p.2.2
        · right
          have hx : spJoined h (· == .xdot) p.1 p.2.1 = true := by
            rw [hflag] at hpb
            rw [← hpb] at hne'
            simpa using hne'
          rw [spJoined_iff] at hx
          obtain ⟨d, hd', hdk, hdxy⟩ := hx
          exact ⟨d, hd', by simpa using hdk, hdxy⟩
        · left
          have hsj : spJoined h Kind.isSolid p.1 p.2.1 = true := by rw [← hpb, hflag]
          have hxj : spJoined h (· == .xdot) p.1 p.2.1 = false := by
            rw [hsj] at hne'
            simpa using hne'
          rw [spJoined_iff] at hsj
          obtain ⟨c, hc', hcs, hcxy⟩ := hsj
          refine ⟨c, hc', ?_, hcxy⟩
          simp only [unpB, hcs, Bool.true_and, Bool.not_eq_true']
          by_contra hx
          simp only [Bool.not_eq_false] at hx
          rw [hasXdot_iff] at hx
          obtain ⟨d, hd', hdk, hdxy⟩ := hx
          have : spJoined h (· == .xdot) p.1 p.2.1 = true := by
            rw [spJoined_iff]
            refine ⟨d, hd', by simp [hdk], ?_⟩
            rcases hcxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
              simp_all
          rw [hxj] at this
          cases this
      rcases hstr p.1 p.2.1 hr with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso
        rcases hjoin with ⟨c, hc', hu, hcxy⟩ | ⟨d, hd', hdk, hdxy⟩
        · have hcX : c ∈ X := by
            rw [hX]
            refine List.mem_filter.2 ⟨hc', ?_⟩
            have : (dg dc.comps).Reachable c.x c.y := by
              rcases hcxy with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · rw [e1, e2]; exact hr
              · rw [e1, e2]; exact hr.symm
            simp [hu, this]
          have hcr : (dg h.comps).Reachable c.x c.y := by
            rcases hcxy with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [e1, e2]; exact h0
            · rw [e1, e2]; exact h0.symm
          apply hab
          rcases hXav c hcX with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2] at hcr; exact hcr.trans hvb
          · rw [e1, e2] at hcr; exact hcr.symm.trans hvb
        · apply hd.xa d hd' hdk
          rcases hdxy with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2]; exact h0
          · rw [e1, e2]; exact h0.symm
      · have hp1 : p.1 = a := (reach_new hnd hna h1.symm).symm
        rcases hjoin with ⟨c, hc', hu, hcxy⟩ | ⟨d, hd', hdk, hdxy⟩
        · have hat : atB a c = true := by
            rcases hcxy with ⟨e1, -⟩ | ⟨-, e2⟩
            · simp [atB, e1, hp1]
            · simp [atB, e2, hp1]
          rw [hp1] at hcxy
          exact Or.inl ⟨hp1, pair_eq (hXav c (hUa c hc' hu hat)) hcxy hav⟩
        · exfalso
          obtain ⟨n1, n2⟩ := hn.noDot d hd' (Or.inr hdk)
          rcases hdxy with ⟨e1, -⟩ | ⟨-, e2⟩
          · rw [e1, hp1, hna] at n1; cases n1
          · rw [e2, hp1, hna] at n2; cases n2
      · have hp2 : p.2.1 = a := (reach_new hnd hna h2.symm).symm
        rcases hjoin with ⟨c, hc', hu, hcxy⟩ | ⟨d, hd', hdk, hdxy⟩
        · have hat : atB a c = true := by
            rcases hcxy with ⟨-, e2⟩ | ⟨e1, -⟩
            · simp [atB, e2, hp2]
            · simp [atB, e1, hp2]
          rw [hp2] at hcxy
          have hcxy' : c.x = a ∧ c.y = p.1 ∨ c.x = p.1 ∧ c.y = a := hcxy.symm
          exact Or.inr ⟨pair_eq (hXav c (hUa c hc' hu hat)) hcxy' hav, hp2⟩
        · exfalso
          obtain ⟨n1, n2⟩ := hn.noDot d hd' (Or.inr hdk)
          rcases hdxy with ⟨-, e2⟩ | ⟨e1, -⟩
          · rw [e2, hp2, hna] at n2; cases n2
          · rw [e1, hp2, hna] at n1; cases n1
    · simp [mkC] at hk
  -- local views away from `a` and `v`
  have hloc : ∀ w : Atom k n, w ≠ a → w ≠ v →
      t.g.deg (t.f w) = h.deg w ∧ t.g.stdNeutralAt (t.f w) = h.stdNeutralAt w := by
    intro w hwa hwv
    have hfw : ∀ u, t.f u = t.f w → u = w := by
      intro u hu
      rcases hfib u w hu with e | ⟨-, e⟩ | ⟨-, e⟩
      · exact e
      · exact absurd e hwv
      · exact absurd e hwa
    have hle := hs.local_eq hfw hdl (fun c hc hat hsol hr => by
      rcases hconvX c hc hsol hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hat with e | e
      · exact hwa (e.symm.trans e1)
      · exact hwv (e.symm.trans e2)
      · exact hwv (e.symm.trans e1)
      · exact hwa (e.symm.trans e2))
    obtain ⟨h1, -, h2⟩ := local_transfer t.f (fun u => ⟨hfw u, fun e => by rw [e]⟩) hle
    have hnx : (dc.comps.filter (atB w)).filter (fun c => c.kind != .xdot) =
        (h.comps.filter (atB w)).filter (fun c => c.kind != .xdot) := by
      rw [hdc, dc_comps, List.filter_append, List.filter_append]
      have hadd : ((addedComps h.splitPairs A).filter (atB w)).filter
          (fun c => c.kind != .xdot) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc hnx
        obtain ⟨hc, hat⟩ := List.mem_filter.1 hc
        have hk : c.kind = .dot := by
          rcases (addedComps_label hc).2 with hk | hk
          · exact hk
          · simp [hk] at hnx
        simp only [atB, Bool.or_eq_true, beq_iff_eq] at hat
        rcases hadded c hc hk with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hat with e | e
        · exact hwa (e.symm.trans e1)
        · exact hwv (e.symm.trans e2)
        · exact hwv (e.symm.trans e1)
        · exact hwa (e.symm.trans e2)
      rw [hadd, List.append_nil]
      unfold keptComps
      rw [List.filter_filter, List.filter_filter, List.filter_filter]
      apply List.filter_congr
      intro c _
      by_cases hk : c.kind = .xdot <;> simp [hk]
    obtain ⟨h3, h4⟩ := local_noX hnx
    exact ⟨h1.trans h3, h2.trans h4⟩
  -- the atom of the block
  have hbeqv : ∀ u, (t.f u == t.f v) = (u == a || u == v) := by
    intro u
    by_cases huv : u = v
    · simp [huv]
    by_cases hua : u = a
    · simp [hua, hfav]
    have : t.f u ≠ t.f v := by
      intro e
      rcases hfib u v e with e' | ⟨e', -⟩ | ⟨e', -⟩
      · exact huv e'
      · exact hua e'
      · exact huv e'
    have h1 : (t.f u == t.f v) = false := by simpa using this
    have h2 : (u == a) = false := by simpa using hua
    have h3 : (u == v) = false := by simpa using huv
    rw [h1, h2, h3]
    rfl
  have hdegz : t.g.deg (t.f v) + 2 ≤ h.deg v := by
    have hz : t.g.deg (t.f v) = (dc.comps.filter fun c =>
        ((c.kind.isSolid && atB a c) || (c.kind.isSolid && atB v c)) &&
          !(c.kind.isSolid && dc.mrep c.x == dc.mrep c.y)).length := by
      unfold Graph.deg
      rw [hs.comps_eq]
      apply count_filterMap
      intro c
      rcases hm' : mergeComp dc.mrep t.f c with _ | c'
      · obtain ⟨hk, -⟩ := mergeComp_none hm'
        simp [hk, Kind.isSolid]
      · simp only
        by_cases hsol : c.kind.isSolid = true
        · rw [mergeComp_solid hsol] at hm'
          obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
            cases hk : c.kind <;> simp_all [Kind.isSolid]
          split_ifs at hm' with hr
          · obtain rfl := Option.some.inj hm'
            show ((c.kind.toWeight).isSolid && _) = _
            rw [hch]
            simp [Kind.toWeight, Kind.isSolid, hr]
          · obtain rfl := Option.some.inj hm'
            have hr' : (dc.mrep c.x == dc.mrep c.y) = false := by simpa using hr
            simp only [Comp.map, hsol, hbeqv, hr', atB]
            generalize (c.x == a) = b1
            generalize (c.y == a) = b2
            generalize (c.x == v) = b3
            generalize (c.y == v) = b4
            revert b1 b2 b3 b4
            decide
        · have hsol' : c.kind.isSolid = false := by simpa using hsol
          rcases mergeComp_kind hm' with e | ⟨ch, hch, -⟩
          · rw [e, hsol']
            simp
          · rw [hch] at hsol'
            cases hsol'
    have hcm := count_merge dc.comps (fun c => c.kind.isSolid && atB a c)
      (fun c => c.kind.isSolid && atB v c)
      (fun c => c.kind.isSolid && dc.mrep c.x == dc.mrep c.y) (by
        intro c hc hR
        simp only [Bool.and_eq_true, beq_iff_eq] at hR
        rcases hconvX c hc hR.1 hR.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [hR.1, atB, e1, e2])
    have hda : (dc.comps.filter fun c => c.kind.isSolid && atB a c).length = h.deg a := by
      rw [← deg_dc h h.splitPairs A a]
      rfl
    have hdv : (dc.comps.filter fun c => c.kind.isSolid && atB v c).length = h.deg v := by
      rw [← deg_dc h h.splitPairs A v]
      rfl
    have hcv : (dc.comps.filter fun c => c.kind.isSolid && dc.mrep c.x == dc.mrep c.y).length = 2 :=
      he
    rw [hda, hdv, hcv, ← hz] at hcm
    omega
  -- the sums over the internal atoms
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  obtain ⟨ia, rfl⟩ : ∃ ia, a = .inr ia := by
    rcases a with x | x
    · simp at haR
    · exact ⟨x, rfl⟩
  obtain ⟨iv, rfl⟩ : ∃ iv, v = .inr iv := by
    rcases v with x | x
    · simp at hvR
    · exact ⟨x, rfl⟩
  have hne : ia ≠ iv := fun e => hav (by rw [e])
  have hgg : g ia = g iv := by
    have := hfav
    rw [hg, hg] at this
    exact Sum.inr.inj this
  have hginj : ∀ i j, g i = g j → i = j ∨ (i = ia ∧ j = iv) ∨ (i = iv ∧ j = ia) := by
    intro i j hij
    have : t.f (.inr i) = t.f (.inr j) := by rw [hg, hg, hij]
    rcases hfib _ _ this with e | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl (Sum.inr.inj e)
    · exact Or.inr (Or.inl ⟨Sum.inr.inj e1, Sum.inr.inj e2⟩)
    · exact Or.inr (Or.inr ⟨Sum.inr.inj e1, Sum.inr.inj e2⟩)
  have hivm : iv ∈ Finset.univ.erase ia := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  have hrest : ∀ i ∈ (Finset.univ.erase ia).erase iv,
      t.g.deg (.inr (g i)) = h.deg (.inr i) ∧
        t.g.stdNeutralAt (.inr (g i)) = h.stdNeutralAt (.inr i) := by
    intro i hi
    have hiv : i ≠ iv := (Finset.mem_erase.1 hi).1
    have hia : i ≠ ia := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    rw [← hg]
    exact hloc _ (fun e => hia (Sum.inr.inj e)) (fun e => hiv (Sum.inr.inj e))
  have hz' : t.g.deg (.inr (g iv)) + 2 ≤ h.deg (.inr iv) := by
    rw [← hg]
    exact hdegz
  have hdegX : t.g.degX + (if 4 ≤ h.deg (.inr iv) then 2 else 0) ≤ h.degX := by
    unfold Graph.degX
    rw [sum_erase_image g hgs ia iv hne hgg hginj, ← Finset.add_sum_erase _ _ hivm,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ ia), ← Finset.add_sum_erase _ _ hivm]
    rw [Finset.sum_congr rfl fun i hi => by rw [(hrest i hi).1]]
    have : t.g.deg (.inr (g iv)) - 2 + (if 4 ≤ h.deg (.inr iv) then 2 else 0) ≤
        h.deg (.inr iv) - 2 := by
      split_ifs <;> omega
    omega
  have hbadN : t.g.badN ≤ h.badN + (if 4 ≤ h.deg (.inr iv) then 1 else 0) := by
    unfold Graph.badN
    rw [Finset.card_filter, Finset.card_filter]
    rw [sum_erase_image g hgs ia iv hne hgg hginj, ← Finset.add_sum_erase _ _ hivm,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ ia), ← Finset.add_sum_erase _ _ hivm]
    rw [Finset.sum_congr rfl fun i hi => by rw [(hrest i hi).1, (hrest i hi).2]]
    have : (if t.g.deg (.inr (g iv)) = 2 ∧ t.g.stdNeutralAt (.inr (g iv)) = false then 1 else 0) ≤
        (if 4 ≤ h.deg (.inr iv) then 1 else 0) := by
      split_ifs with h1 h2
      · exact le_rfl
      · omega
      · exact Nat.zero_le _
      · exact le_rfl
    have h0 : ∀ p : Prop, [Decidable p] → (0 : ℕ) ≤ (if p then 1 else 0) := fun _ _ =>
      Nat.zero_le _
    have := h0 (h.deg (.inr ia) = 2 ∧ h.stdNeutralAt (.inr ia) = false)
    have := h0 (h.deg (.inr iv) = 2 ∧ h.stdNeutralAt (.inr iv) = false)
    omega
  have hlw : dc.lwN = h.lwN := by
    have := dc_count h h.splitPairs A Kind.isLt rfl rfl (fun _ => true)
    simpa [Graph.lwN] using this
  have hrw : dc.rwN = h.rwN := by
    have := dc_count h h.splitPairs A Kind.isRg rfl rfl (fun _ => true)
    simpa [Graph.rwN] using this
  have hee : dc.eextN = h.eextN :=
    dc_count h h.splitPairs A Kind.isSolid rfl rfl fun c => c.x.isLeft || c.y.isLeft
  refine ⟨.inr ia, .inr iv, hna, hvR, hav, hdega, ?_, ?_, hs.lwN_eq.trans hlw, ?_⟩
  · intro c hc hu hat
    exact hXav c (hUa c hc hu hat)
  · have := hs.eextN_eq
    rw [hext, add_zero] at this
    rw [this, hee]
  · have h1 := hs.lwN_eq
    have h2 := hs.rwN_eq
    rw [he] at h2
    unfold Graph.phi
    rw [h1, h2, hlw, hrw]
    split_ifs at hbadN hdegX ⊢ <;> omega


end DotCaseD2


/-! ## `O_dot` outputs of the same reduced order -/

section DotEqual

variable {k n : ℕ} {h : Graph k n}

set_option maxHeartbeats 1000000 in
open Classical in
/-- An output of `O_dot` (merge case) whose reduced order equals that of the input minus the
surplus `s` has fewer solid edges at external atoms, or `s = 0` and it has the quantities of the
input (no merge), or `s = 0` and two edges between a new atom `α` and an atom `v` became weights
(one merge). -/
private theorem dot_equal3 {nw : Atom k n → Bool} (hd : DotIn h) {s : ℕ} (hn : DotNew h s nw)
    (hsep : h.SepInt) {A : List (Atom k n × Atom k n × Bool)} (hA : List.Sublist A h.splitPairs)
    {t : Tracked k n} (hm : (h.dotChoice h.splitPairs A).mergeT = some t)
    (heq : t.g.obl = h.obl - s) :
    t.g.eextN < h.eextN ∨
    (s = 0 ∧ t.g.phi = h.phi ∧ t.g.eextN = h.eextN) ∨
    (s = 0 ∧ ∃ α v : Atom k n, nw α = true ∧ v.isRight = true ∧ α ≠ v ∧ h.deg α = 2 ∧
      (∀ c ∈ h.comps, unpB h c = true → atB α c = true →
        (c.x = α ∧ c.y = v ∨ c.x = v ∧ c.y = α)) ∧
      t.g.eextN = h.eextN ∧ t.g.lwN = h.lwN ∧
      t.g.phi ≤ h.phi + 2) := by
  set dc := h.dotChoice h.splitPairs A with hdc
  have hs := mergeT_spec hm
  have hnd : ∀ c ∈ h.comps, c.kind = .dot → nw c.x = false ∧ nw c.y = false :=
    fun c hc hk => hn.noDot c hc (Or.inl hk)
  have hobl := hs.obl_eq
  try rw [← hdc] at hobl
  have hdco := dc_obl h h.splitPairs A
  try rw [← hdc] at hdco
  have hJ := ccN_dc_le h h.splitPairs A
  try rw [← hdc] at hJ
  have he : (convN dc : ℤ) = s + 2 * ((ccN h.comps : ℤ) - ccN dc.comps) := by linarith
  have hee := hs.eextN_eq
  have hdcE : dc.eextN = h.eextN :=
    dc_count h h.splitPairs A Kind.isSolid rfl rfl fun c => c.x.isLeft || c.y.isLeft
  by_cases hext : 0 < convExt dc
  · left
    omega
  have hext0 : convExt dc = 0 := by omega
  right
  set X := h.comps.filter fun c => unpB h c && decide ((dg dc.comps).Reachable c.x c.y) with hX
  have hXlen : X.length = convN dc := by
    have := convN_eq hm
    try rw [← hdc] at this
    rw [hX, this]
  have hXmem : ∀ c ∈ X, c ∈ h.comps ∧ unpB h c = true ∧ (dg dc.comps).Reachable c.x c.y := by
    intro c hc
    rw [hX, List.mem_filter] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2⟩
  have hsolU : ∀ c, unpB h c = true → c.kind.isSolid = true := by
    intro c hc
    simp only [unpB, Bool.and_eq_true] at hc
    exact hc.1
  -- converted edges join internal atoms
  have hXint : ∀ c ∈ X, c.x.isRight = true ∧ c.y.isRight = true := by
    intro c hc
    obtain ⟨hch, hu, hr⟩ := hXmem c hc
    have hsol := hsolU c hu
    have hrep : dc.mrep c.x = dc.mrep c.y := (dc.mrep_eq_iff _ _).2 hr
    have hcdc : c ∈ dc.comps := by
      rw [hdc, dc_comps]
      refine List.mem_append_left _ ((mem_keptComps _ _ _).2 ⟨hch, ?_⟩)
      rintro ⟨hk, -⟩
      rw [hk] at hsol
      cases hsol
    by_contra hcon
    have hlt : 0 < convExt dc := by
      refine List.length_pos_of_mem (List.mem_filter.2 ⟨hcdc, ?_⟩)
      have : (c.x.isLeft || c.y.isLeft) = true := by
        rcases hx : c.x with x | x <;> rcases hy : c.y with y | y <;> simp_all
      simp [hsol, hrep, this]
    omega
  have hXne : ∀ c ∈ X, c.x ≠ c.y := fun c hc =>
    hd.noLoop c (hXmem c hc).1 (hsolU c (hXmem c hc).2.1)
  -- `h`-reachable ends of a converted edge are impossible
  have hXnr : ∀ c ∈ X, ¬ (dg h.comps).Reachable c.x c.y := by
    intro c hc hr
    obtain ⟨hx, hy⟩ := hXint c hc
    rcases hcx : c.x with x | x
    · rw [hcx] at hx; cases hx
    rcases hcy : c.y with y | y
    · rw [hcy] at hy; cases hy
    rw [hcx, hcy] at hr
    exact hXne c hc (by rw [hcx, hcy, hsep x y hr])
  have hGH : ∀ a b, (dg h.comps).Reachable a b → (dg dc.comps).Reachable a b :=
    fun _ _ hr => dc_reach h _ A hr
  rcases Nat.lt_or_ge (ccN dc.comps + 1) (ccN h.comps) with hJ2 | hJ1
  · -- two or more merges: impossible
    exfalso
    have h4 : X.length ≤ (h.comps.filter (unpB h)).length :=
      length_filter_mono _ _ _ fun c _ hc => by simp only [Bool.and_eq_true] at hc; exact hc.1
    have hf := hn.four
    have hz := hn.zero
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · have := hz hs0
      omega
    · omega
  rcases Nat.lt_or_ge (ccN dc.comps) (ccN h.comps) with hJ1' | hJ0
  · -- one merge
    have hc1 : ccN h.comps = ccN dc.comps + 1 := by omega
    obtain ⟨a, b, hab, -, hstr⟩ := reach_of_card_cc_succ hGH hc1
    have hcross : ∀ c ∈ X, ((dg h.comps).Reachable c.x a ∧ (dg h.comps).Reachable c.y b) ∨
        ((dg h.comps).Reachable c.x b ∧ (dg h.comps).Reachable c.y a) := by
      intro c hc
      rcases hstr c.x c.y (hXmem c hc).2.2 with h0 | h1 | h1
      · exact absurd h0 (hXnr c hc)
      · exact Or.inl h1
      · exact Or.inr h1
    have hen : (convN dc : ℤ) = s + 2 := by rw [he, hc1]; push_cast; ring
    -- `s = 0`
    have hs0 : s = 0 := by
      by_contra hs0
      obtain ⟨c₀, hc₀⟩ : ∃ c, c ∈ X := List.exists_mem_of_length_pos (by omega)
      by_cases hold : nw c₀.x = false ∧ nw c₀.y = false
      · -- all converted edges are between old atoms
        have hall : ∀ c ∈ X, nw c.x = false ∧ nw c.y = false := by
          intro c hc
          have key : ∀ w, nw w = true → (dg h.comps).Reachable w a ∨
              (dg h.comps).Reachable w b → False := by
            intro w hw hr
            rcases hr with hr | hr
            · have e := reach_new hnd hw hr
              rcases hcross c₀ hc₀ with ⟨h1, -⟩ | ⟨-, h2⟩
              · rw [← e] at h1
                have := reach_new hnd hw h1.symm
                rw [← this] at hold
                rw [hold.1] at hw; cases hw
              · rw [← e] at h2
                have := reach_new hnd hw h2.symm
                rw [← this] at hold
                rw [hold.2] at hw; cases hw
            · have e := reach_new hnd hw hr
              rcases hcross c₀ hc₀ with ⟨-, h2⟩ | ⟨h1, -⟩
              · rw [← e] at h2
                have := reach_new hnd hw h2.symm
                rw [← this] at hold
                rw [hold.2] at hw; cases hw
              · rw [← e] at h1
                have := reach_new hnd hw h1.symm
                rw [← this] at hold
                rw [hold.1] at hw; cases hw
          constructor
          · by_contra hx
            simp only [Bool.not_eq_false] at hx
            rcases hcross c hc with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact key _ hx (Or.inl h1)
            · exact key _ hx (Or.inr h1)
          · by_contra hy
            simp only [Bool.not_eq_false] at hy
            rcases hcross c hc with ⟨-, h2⟩ | ⟨-, h2⟩
            · exact key _ hy (Or.inr h2)
            · exact key _ hy (Or.inl h2)
        have hle : X.length ≤ (h.comps.filter fun c => unpB h c && !nw c.x && !nw c.y).length := by
          rw [hX]
          refine length_filter_mono _ _ _ fun c hc hP => ?_
          have hcX : c ∈ X := by rw [hX]; exact List.mem_filter.2 ⟨hc, hP⟩
          obtain ⟨e1, e2⟩ := hall c hcX
          simp only [Bool.and_eq_true] at hP
          simp [hP.1, e1, e2]
        have := hn.old
        omega
      · -- a converted edge at a new atom: all converted edges are at that atom
        have hnew : ∃ ε, nw ε = true ∧ (ε = c₀.x ∨ ε = c₀.y) := by
          by_contra hh
          push Not at hh
          apply hold
          constructor
          · by_contra hx; exact (hh c₀.x (by simpa using hx)).1 rfl
          · by_contra hy; exact (hh c₀.y (by simpa using hy)).2 rfl
        obtain ⟨ε, hε, hεc⟩ := hnew
        have hεab : (dg h.comps).Reachable ε a ∨ (dg h.comps).Reachable ε b := by
          rcases hεc with rfl | rfl <;> rcases hcross c₀ hc₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl h1
          · exact Or.inr h1
          · exact Or.inr h2
          · exact Or.inl h2
        have hat : ∀ c ∈ X, c.x = ε ∨ c.y = ε := by
          intro c hc
          rcases hεab with hr | hr
          · have e := reach_new hnd hε hr
            rcases hcross c hc with ⟨h1, -⟩ | ⟨-, h2⟩
            · rw [← e] at h1; exact Or.inl (reach_new hnd hε h1.symm).symm
            · rw [← e] at h2; exact Or.inr (reach_new hnd hε h2.symm).symm
          · have e := reach_new hnd hε hr
            rcases hcross c hc with ⟨-, h2⟩ | ⟨h1, -⟩
            · rw [← e] at h2; exact Or.inr (reach_new hnd hε h2.symm).symm
            · rw [← e] at h1; exact Or.inl (reach_new hnd hε h1.symm).symm
        have hle : X.length ≤ (h.comps.filter fun c => unpB h c && (c.x == ε || c.y == ε)).length := by
          rw [hX]
          refine length_filter_mono _ _ _ fun c hc hP => ?_
          have hcX : c ∈ X := by rw [hX]; exact List.mem_filter.2 ⟨hc, hP⟩
          simp only [Bool.and_eq_true] at hP
          rcases hat c hcX with e | e <;> simp [hP.1, e]
        have := hn.two ε hε
        omega
    subst hs0
    have hn0 : DotNew h 0 nw := hn
    have he2 : convN dc = 2 := by omega
    -- one of `a`, `b` is new
    obtain ⟨c₀, hc₀⟩ : ∃ c, c ∈ X := List.exists_mem_of_length_pos (by omega)
    have hnew : nw a = true ∨ nw b = true := by
      have hold0 : ¬ (nw c₀.x = false ∧ nw c₀.y = false) := by
        rintro ⟨e1, e2⟩
        have : 0 < (h.comps.filter fun c => unpB h c && !nw c.x && !nw c.y).length :=
          List.length_pos_of_mem (List.mem_filter.2 ⟨(hXmem c₀ hc₀).1, by
            simp [(hXmem c₀ hc₀).2.1, e1, e2]⟩)
        have := hn.old
        omega
      have hεc : nw c₀.x = true ∨ nw c₀.y = true := by
        by_contra hh
        push Not at hh
        exact hold0 ⟨by simpa using hh.1, by simpa using hh.2⟩
      rcases hεc with hx | hy <;> rcases hcross c₀ hc₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ((reach_new hnd hx h1) ▸ hx)
      · exact Or.inr ((reach_new hnd hx h1) ▸ hx)
      · exact Or.inr ((reach_new hnd hy h2) ▸ hy)
      · exact Or.inl ((reach_new hnd hy h2) ▸ hy)
    refine Or.inr ⟨rfl, ?_⟩
    rcases hnew with hna | hnb
    · exact dot_caseD_aux hd hn0 hsep hm hna hab hstr he2 hext0
    · refine dot_caseD_aux hd hn0 hsep hm hnb (fun hr => hab hr.symm) ?_ he2 hext0
      intro u v huv
      rcases hstr u v huv with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h0
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · -- no merge
    have hc0 : ccN h.comps = ccN dc.comps := le_antisymm hJ0 hJ
    have hr0 := reach_of_card_cc_eq hGH hc0
    have hes : (convN dc : ℤ) = s := by rw [he, hc0]; ring
    have hs0 : s = 0 := by
      by_contra hs0
      obtain ⟨c₀, hc₀⟩ : ∃ c, c ∈ X := List.exists_mem_of_length_pos (by omega)
      exact hXnr c₀ hc₀ (hr0 _ _ (hXmem c₀ hc₀).2.2)
    subst hs0
    left
    obtain ⟨h1, h2⟩ := dot_caseC hd hsep hA hm hr0 (by show convN dc = 0; omega)
    exact ⟨rfl, h1, h2⟩

end DotEqual


/-! ## Orders and weight counts of lists of components -/

section Lists

variable {V : Type*}

/-- The sum of the scaling orders of a list of components. -/
def ordL (cs : List (Comp V)) : ℤ := (cs.map fun c => c.kind.ord).sum

@[simp] private theorem ordL_nil : ordL ([] : List (Comp V)) = 0 := rfl

@[simp] private theorem ordL_cons (c : Comp V) (cs : List (Comp V)) :
    ordL (c :: cs) = c.kind.ord + ordL cs := by simp [ordL]

@[simp] private theorem ordL_append (cs cs' : List (Comp V)) :
    ordL (cs ++ cs') = ordL cs + ordL cs' := by simp [ordL]

private theorem Graph.ord_eq {k n : ℕ} (Γ : Graph k n) : Γ.ord = ordL Γ.comps - 2 * n := rfl

end Lists

/-! ## Complex conjugation of graphs: invariant properties -/

section ConjInv

variable {k n : ℕ}

/-- The complex conjugate of one component. -/
def Comp.conj {V : Type*} (c : Comp V) : Comp V := { c with kind := c.kind.conj }

theorem Graph.conj_comps (Γ : Graph k n) : Γ.conj.comps = Γ.comps.map Comp.conj := rfl

theorem Kind.conj_isSolid (κ : Kind) : κ.conj.isSolid = κ.isSolid := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.isSolid]

private theorem Kind.conj_isRandom (κ : Kind) : κ.conj.isRandom = κ.isRandom := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.isRandom]

private theorem Kind.conj_isWeight (κ : Kind) : κ.conj.isWeight = κ.isWeight := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.isWeight]

private theorem Kind.conj_joinsMol (κ : Kind) : κ.conj.joinsMol = κ.joinsMol := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.joinsMol]

private theorem Kind.conj_isDiffusive (κ : Kind) : κ.conj.isDiffusive = κ.isDiffusive := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.isDiffusive]

theorem Kind.conj_ord (κ : Kind) : κ.conj.ord = κ.ord := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.ord]

theorem Kind.conj_eq_dot (κ : Kind) : κ.conj = .dot ↔ κ = .dot := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

theorem Kind.conj_eq_xdot (κ : Kind) : κ.conj = .xdot ↔ κ = .xdot := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

private theorem Kind.conj_inv (κ : Kind) : (∃ ch, κ.conj = .inv ch) ↔ ∃ ch, κ = .inv ch := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

private theorem Kind.conj_wD (κ : Kind) : (∃ ch d, κ.conj = .wD ch d) ↔ ∃ ch d, κ = .wD ch d := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

@[simp] theorem Comp.conj_x {V : Type*} (c : Comp V) : c.conj.x = c.x := rfl

@[simp] theorem Comp.conj_y {V : Type*} (c : Comp V) : c.conj.y = c.y := rfl

@[simp] theorem Comp.conj_label {V : Type*} (c : Comp V) : c.conj.label = c.label := rfl

@[simp] theorem Comp.conj_kind {V : Type*} (c : Comp V) : c.conj.kind = c.kind.conj := rfl

private theorem Graph.mem_conj_comps {Γ : Graph k n} {c' : Comp (Atom k n)} :
    c' ∈ Γ.conj.comps ↔ ∃ c ∈ Γ.comps, c' = c.conj := by
  rw [Graph.conj_comps, List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩

theorem Graph.conj_ord (Γ : Graph k n) : Γ.conj.ord = Γ.ord := by
  unfold Graph.ord
  simp only [Graph.conj_comps, List.map_map, Function.comp_def, Comp.conj_kind, Kind.conj_ord]

private theorem Graph.conj_length (Γ : Graph k n) : Γ.conj.comps.length = Γ.comps.length := by
  simp [Graph.conj_comps]

theorem Graph.conj_wt (Γ : Graph k n) (u : Atom k n) : Γ.conj.wt u = Γ.wt u := by
  unfold Graph.wt
  simp only [Graph.conj_comps, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro c _
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> (try cases ‹Wave›) <;> simp [Comp.conj, Kind.conj]

private theorem Graph.conj_edgeGraph (Γ : Graph k n) : Γ.conj.edgeGraph = Γ.edgeGraph := by
  unfold Graph.edgeGraph
  congr 1
  funext u v
  apply propext
  simp only [Graph.mem_conj_comps]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, h1, h2⟩; exact ⟨c, hc, h1, h2⟩
  · rintro ⟨c, hc, h1, h2⟩; exact ⟨c.conj, ⟨c, hc, rfl⟩, h1, h2⟩

private theorem Graph.conj_wavedThetaGraph (Γ : Graph k n) :
    Γ.conj.wavedThetaGraph = Γ.wavedThetaGraph := by
  unfold Graph.wavedThetaGraph
  congr 1
  funext u v
  apply propext
  simp only [Graph.mem_conj_comps]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, h0, h1, h2⟩
    refine ⟨c, hc, ?_, h1, h2⟩
    simpa [Kind.conj_joinsMol, Kind.conj_eq_dot, Kind.conj_isDiffusive] using h0
  · rintro ⟨c, hc, h0, h1, h2⟩
    refine ⟨c.conj, ⟨c, hc, rfl⟩, ?_, h1, h2⟩
    simpa [Kind.conj_joinsMol, Kind.conj_eq_dot, Kind.conj_isDiffusive] using h0

private theorem Graph.conj_Regular {C : ℕ} {Γ : Graph k n} (h : Γ.Regular C)
    : Γ.conj.Regular C := by
  refine ⟨by rw [Graph.conj_length]; exact h.size, ?_, ?_, ?_⟩
  · rw [Graph.conj_edgeGraph]; exact h.connected
  · intro a b; rw [Graph.conj_wavedThetaGraph]; exact h.internal a b
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact h.noIntDot c hc ((Kind.conj_eq_dot _).1 hk)

theorem Graph.conj_Normal {C : ℕ} {Γ : Graph k n} (h : Γ.Normal C) : Γ.conj.Normal C := by
  obtain ⟨hr, hs, hx⟩ := h
  refine ⟨Graph.conj_Regular hr, ?_, ?_⟩
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact hs c hc (by simpa [Kind.conj_isSolid] using hk)
  · intro u v huv
    have h := hx u v huv
    simp only [Graph.mem_conj_comps]
    constructor
    · rintro ⟨c', ⟨c, hc, rfl⟩, hk, hm⟩
      obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := h.1 ⟨c, hc, by simpa [Kind.conj_eq_xdot] using hk, hm⟩
      exact ⟨c₂.conj, ⟨c₂, hc₂, rfl⟩, by simpa [Kind.conj_isSolid] using hk₂, hm₂⟩
    · rintro ⟨c', ⟨c, hc, rfl⟩, hk, hm⟩
      obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := h.2 ⟨c, hc, by simpa [Kind.conj_isSolid] using hk, hm⟩
      exact ⟨c₂.conj, ⟨c₂, hc₂, rfl⟩, by simpa [Kind.conj_eq_xdot] using hk₂, hm₂⟩

theorem Graph.conj_Plain {Γ : Graph k n} (h : Γ.Plain) : Γ.conj.Plain := by
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h c hc
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch hk
    have : ∃ ch', c.conj.kind = .inv ch' := ⟨ch, hk⟩
    obtain ⟨ch', hch'⟩ := (Kind.conj_inv c.kind).1 this
    exact h2 ch' hch'
  · intro ch d hk
    have : ∃ ch' d', c.conj.kind = .wD ch' d' := ⟨ch, d, hk⟩
    obtain ⟨ch', d', hch'⟩ := (Kind.conj_wD c.kind).1 this
    exact h3 ch' d' hch'
  · intro hk
    exact h4 ((Kind.conj_eq_dot _).1 hk)
  · intro hw
    rw [Comp.conj_kind, Kind.conj_isWeight] at hw
    exact h5 hw
  · intro hl
    rw [Comp.conj_kind, Kind.conj_isRandom]
    exact h6 hl

end ConjInv

/-! ## Lists of components: erasing, lifting, labelling, derivatives -/

section Lists2

variable {V : Type*}

private theorem eraseIdx_map {W : Type*} (f : Comp V → Comp W) (l : List (Comp V)) (j : ℕ) :
    (l.map f).eraseIdx j = (l.eraseIdx j).map f := by
  induction l generalizing j with
  | nil => simp
  | cons c l ih =>
    cases j with
    | zero => simp
    | succ j => simp [ih]

end Lists2

section LiftLabel

variable {k n : ℕ}

private theorem ordL_liftCs (j : ℕ) (cs : List (Comp (Atom k n))) : ordL
    (liftCs j cs) = ordL cs := by
  simp [liftCs, ordL, Comp.map, List.map_map, Function.comp_def]

private theorem liftA_injective (j : ℕ) : Function.Injective (liftA (k := k) (n := n) j) := by
  intro u v h
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [liftA, Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq, Sum.inr.injEq,
      Fin.castAdd_inj, reduceCtorEq] at h ⊢ <;> exact h

private theorem liftA_isRight (j : ℕ) (u : Atom k n) : (liftA j u).isRight = u.isRight := by
  rcases u with a | a <;> simp [liftA]

private theorem liftA_isLeft (j : ℕ) (u : Atom k n) : (liftA j u).isLeft = u.isLeft := by
  rcases u with a | a <;> simp [liftA]

private theorem liftA_ne_newA (j : ℕ) (u : Atom k n) (i : Fin j) : liftA j u ≠ newA i := by
  rcases u with a | a
  · simp [liftA, newA]
  · intro h
    have := congrArg Fin.val (Sum.inr.inj h)
    simp at this
    have := a.isLt
    omega

private theorem mem_liftCs {j : ℕ} {cs : List (Comp (Atom k n))} {c' : Comp (Atom k (n + j))} :
    c' ∈ liftCs j cs ↔ ∃ c ∈ cs, c' = c.map (liftA j) := by
  unfold liftCs
  rw [List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩

end LiftLabel

section DTermsFacts

variable {V : Type*} [DecidableEq V]

theorem mem_dTerms {p q : V} {cs : List (Comp V)} {d : List (Comp V)} :
    d ∈ dTerms p q cs ↔ ∃ j, ∃ (hj : j < cs.length), ∃ ps, (cs[j]).dPieces p q = some ps ∧
      d = cs.eraseIdx j ++ ps := by
  unfold dTerms
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, -, hi⟩
    obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hi
    exact ⟨i.1, i.2, ps, hps, rfl⟩
  · rintro ⟨j, hj, ps, hps, rfl⟩
    refine ⟨⟨j, hj⟩, List.mem_finRange _, ?_⟩
    simp [hps]

private theorem dPieces_random {p q : V} {c : Comp V} {ps : List (Comp V)}
    (h : c.dPieces p q = some ps) :
    (∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch) := by
  unfold Comp.dPieces at h
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp_all

end DTermsFacts

section NewOKDef

variable {k n : ℕ}

/-- A component that may be added to a graph: a solid edge, a weight, a light weight or a
waved edge, without minor; a weight sits on its atom, a solid edge joins two distinct atoms, only
random components are labelled. -/
def NewOK {V : Type*} (c : Comp V) : Prop :=
  c.minor = [] ∧
  ((∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch) ∨
    ∃ w, c.kind = .waved w) ∧
  (c.kind.isWeight = true → c.y = c.x) ∧ (c.kind.isSolid = true → c.x ≠ c.y) ∧
  (c.label.isSome = true → c.kind.isRandom = true)

end NewOKDef

/-! ## New components, and the graphs extending a graph -/

section NewComps

variable {k n : ℕ}

/-- The optional `Q`-labelling of all random components of a list. -/
private def labW {V : Type*} : Option V → List (Comp V) → List (Comp V)
  | none, L => L
  | some u, L => labelQs u L

private theorem NewOK_solidC {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    NewOK (solidC ch u v) := by
  unfold solidC
  split_ifs with h
  · exact ⟨rfl, Or.inr (Or.inl ⟨ch, rfl⟩), fun _ => rfl,
      fun hs => by simp [mkC, Kind.isSolid] at hs, fun hl => by simp [mkC] at hl⟩
  · exact ⟨rfl, Or.inl ⟨ch, rfl⟩, fun hw => by simp [mkC, Kind.isWeight] at hw, fun _ => h,
      fun hl => by simp [mkC] at hl⟩

private theorem NewOK_waved {V : Type*} (w : Wave) (u v : V) : NewOK (mkC (.waved w) u v) :=
  ⟨rfl, Or.inr (Or.inr (Or.inr ⟨w, rfl⟩)), fun hw => by simp [mkC, Kind.isWeight] at hw,
    fun hs => by simp [mkC, Kind.isSolid] at hs, fun hl => by simp [mkC] at hl⟩

private theorem NewOK_light {V : Type*} (ch : Charge) (u : V) : NewOK (mkC (.light ch) u u) :=
  ⟨rfl, Or.inr (Or.inr (Or.inl ⟨ch, rfl⟩)), fun _ => rfl,
    fun hs => by simp [mkC, Kind.isSolid] at hs, fun hl => by simp [mkC] at hl⟩

private theorem NewOK_weight {V : Type*} (ch : Charge) (u : V) : NewOK (mkC (.weight ch) u u) :=
  ⟨rfl, Or.inr (Or.inl ⟨ch, rfl⟩), fun _ => rfl,
    fun hs => by simp [mkC, Kind.isSolid] at hs, fun hl => by simp [mkC] at hl⟩

private theorem NewOK_G {V : Type*} (ch : Charge) {u v : V} (h : u ≠ v) : NewOK (mkC (.G ch) u v) :=
  ⟨rfl, Or.inl ⟨ch, rfl⟩, fun hw => by simp [mkC, Kind.isWeight] at hw, fun _ => h,
    fun hl => by simp [mkC] at hl⟩

private theorem dPieces_newOK {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)}
    (h : c.dPieces p q = some ps) : ∀ c' ∈ ps, NewOK c' := by
  unfold Comp.dPieces at h
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> (try cases ‹Charge›) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    (intro c' hc'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
     rcases hc' with rfl | rfl <;> exact NewOK_solidC _ _ _)

end NewComps

section Paths

variable {V : Type*} [DecidableEq V]

end Paths

/-! ## The factors of the derivative: orders and pairs -/

section DPieces

variable {V : Type*} [DecidableEq V]

private theorem ord_solidC (ch : Charge) (u v : V) :
    (solidC ch u v).kind.ord = if u = v then 0 else 1 := by
  unfold solidC; split_ifs <;> simp [mkC, Kind.ord]

/-- The endpoint of a random component other than the one it sits on (itself, for a weight). -/
private def Comp.endB (c : Comp V) : V := if c.kind.isWeight then c.x else c.y

private theorem dPieces_eq_plus {p q : V} {c : Comp V} {ps : List (Comp V)}
    (h : c.dPieces p q = some ps)
    (hk : (∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch)) :
    (c.kind = .G .plus ∨ c.kind = .weight .plus ∨ c.kind = .light .plus) ∧
      ps = [solidC .plus c.x p, solidC .plus q c.endB] ∨
    (c.kind = .G .minus ∨ c.kind = .weight .minus ∨ c.kind = .light .minus) ∧
      ps = [solidC .minus c.x q, solidC .minus p c.endB] := by
  unfold Comp.dPieces at h
  unfold Comp.endB
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> (try cases ‹Charge›) <;> simp_all [Kind.isWeight]

end DPieces

/-! ## Reachability -/

section Reach

variable {k n : ℕ}

private theorem reach_map {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} (φ : α → β)
    (h : ∀ a b, G.Adj a b → H.Reachable (φ a) (φ b)) {u v : α} (huv : G.Reachable u v) :
    H.Reachable (φ u) (φ v) := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

private theorem atom_cases {j : ℕ} (u : Atom k (n + j)) :
    (∃ v : Atom k n, u = liftA j v) ∨ ∃ i : Fin j, u = newA i := by
  rcases u with a | i
  · exact Or.inl ⟨.inl a, rfl⟩
  · by_cases h : i.val < n
    · left
      exact ⟨.inr ⟨i.val, h⟩, by simp [liftA]⟩
    · right
      refine ⟨⟨i.val - n, by omega⟩, ?_⟩
      simp only [newA, Fin.natAdd_mk, Sum.inr.injEq]
      ext
      simp only []
      omega

end Reach


section Normalize

variable {k m : ℕ}

end Normalize



/-! ## Terms of the local operations before `O_dot` -/

section Sch

variable {k n : ℕ}

/-- The optional `Q`-labelling of one component. -/
def labF {V : Type*} : Option V → Comp V → Comp V
  | none => id
  | some u => Comp.labelQ u

private theorem labW_eq_map {V : Type*} (o : Option V) (L : List (Comp V)) :
    labW o L = L.map (labF o) := by
  cases o <;> simp [labW, labF, labelQs]

theorem labF_kind {V : Type*} (o : Option V) (c : Comp V) : (labF o c).kind = c.kind := by
  cases o with
  | none => rfl
  | some u => show (Comp.labelQ u c).kind = c.kind; unfold Comp.labelQ; split_ifs <;> rfl

private theorem labF_x {V : Type*} (o : Option V) (c : Comp V) : (labF o c).x = c.x := by
  cases o with
  | none => rfl
  | some u => show (Comp.labelQ u c).x = c.x; unfold Comp.labelQ; split_ifs <;> rfl

private theorem labF_y {V : Type*} (o : Option V) (c : Comp V) : (labF o c).y = c.y := by
  cases o with
  | none => rfl
  | some u => show (Comp.labelQ u c).y = c.y; unfold Comp.labelQ; split_ifs <;> rfl

private theorem labF_minor {V : Type*} (o : Option V) (c : Comp V) : (labF o c).minor = c.minor := by
  cases o with
  | none => rfl
  | some u => show (Comp.labelQ u c).minor = c.minor; unfold Comp.labelQ; split_ifs <;> rfl

private theorem labF_nonrandom {V : Type*} (o : Option V) {c : Comp V} (h : c.kind.isRandom = false) :
    labF o c = c := by
  cases o with
  | none => rfl
  | some u => show Comp.labelQ u c = c; unfold Comp.labelQ; simp [h]

private theorem labF_label_some {V : Type*} (u : V) (c : Comp V) :
    (labF (some u) c).label = if c.kind.isRandom then some (.Q, u) else c.label := by
  show (Comp.labelQ u c).label = _
  unfold Comp.labelQ
  split_ifs <;> rfl

/-- A term of a local operation before `O_dot`, with `j` new atoms: the components of `Γ` with the
random components `R` removed, moved to the graph with `j` more atoms, together with the new
components `N`, all random components labelled `Q_u` if `lab = some u`. -/
def Sch (Γ : Graph k n) (j : ℕ) (R : List (Comp (Atom k n))) (N : List (Comp (Atom k (n + j))))
    (lab : Option (Atom k (n + j))) (g : Graph k (n + j)) : Prop :=
  (∀ c ∈ R, c.kind.isRandom = true) ∧ ∃ K : List (Comp (Atom k n)),
    Γ.comps.Perm (K ++ R) ∧ g.comps.Perm ((liftCs j K ++ N).map (labF lab))

variable {Γ : Graph k n} {j : ℕ} {R : List (Comp (Atom k n))} {N : List (Comp (Atom k (n + j)))}
  {lab : Option (Atom k (n + j))} {g : Graph k (n + j)}

/-- Counting the components with a property in a term. -/
theorem Sch.count (hS : Sch Γ j R N lab g) (P : Comp (Atom k (n + j)) → Bool)
    (hP : ∀ c, P (labF lab c) = P c) :
    (g.comps.filter P).length + (R.filter fun c => P (c.map (liftA j))).length =
      (Γ.comps.filter fun c => P (c.map (liftA j))).length + (N.filter P).length := by
  obtain ⟨-, K, h1, h2⟩ := hS
  rw [(h2.filter P).length_eq, (h1.filter _).length_eq]
  have hc : ∀ L : List (Comp (Atom k (n + j))), ((L.map (labF lab)).filter P).length =
      (L.filter P).length := by
    intro L
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro c _
    simp [Function.comp, hP c]
  rw [hc, List.filter_append, List.filter_append, List.length_append, List.length_append]
  unfold liftCs
  rw [List.filter_map, List.length_map]
  simp only [Function.comp_def]
  omega

/-- The order of a term. -/
private theorem Sch.ordSum (hS : Sch Γ j R N lab g) :
    ordL g.comps + ordL R = ordL Γ.comps + ordL N := by
  obtain ⟨-, K, h1, h2⟩ := hS
  have hp : ∀ {L L' : List (Comp (Atom k (n + j)))}, L.Perm L' → ordL L = ordL L' :=
    fun h => (h.map _).sum_eq
  have hp' : ∀ {L L' : List (Comp (Atom k n))}, L.Perm L' → ordL L = ordL L' :=
    fun h => (h.map _).sum_eq
  rw [hp h2, hp' h1]
  have : ordL ((liftCs j K ++ N).map (labF lab)) = ordL (liftCs j K ++ N) := by
    unfold ordL
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp [labF_kind]
  rw [this, ordL_append, ordL_append, ordL_liftCs]
  ring

theorem Sch.ord (hS : Sch Γ j R N lab g) :
    g.ord + ordL R + 2 * j = Γ.ord + ordL N := by
  have := hS.ordSum
  simp only [Graph.ord_eq]
  push_cast
  linarith

/-- Reachability by dotted edges along an injective map of the atoms. -/
private theorem dg_map_reach {m : ℕ} {φ : Atom k n → Atom k m} (hφ : Function.Injective φ)
    {L : List (Comp (Atom k n))} {u v : Atom k n} :
    (dg (L.map (Comp.map φ))).Reachable (φ u) (φ v) ↔ (dg L).Reachable u v := by
  constructor
  · intro h
    suffices key : ∀ a b, (dg (L.map (Comp.map φ))).Reachable a b → ∀ u, a = φ u →
        ∃ v, b = φ v ∧ (dg L).Reachable u v by
      obtain ⟨v', hv', hr⟩ := key _ _ h u rfl
      rwa [hφ hv']
    intro a b hab
    obtain ⟨w⟩ := hab
    induction w with
    | nil => intro u hu; exact ⟨u, hu, .refl _⟩
    | cons hadj _ ih =>
      intro u hu
      obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hadj
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      have hk₀ : c₀.kind = .dot := hk
      have hr₀ := dg_reach_of_mem hc₀ hk₀
      simp only [Comp.map] at hxy
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 : c₀.x = u := hφ (h1.trans hu)
        obtain ⟨v, hv, hr⟩ := ih c₀.y h2.symm
        exact ⟨v, hv, (e1 ▸ hr₀).trans hr⟩
      · have e1 : c₀.y = u := hφ (h2.trans hu)
        obtain ⟨v, hv, hr⟩ := ih c₀.x h1.symm
        exact ⟨v, hv, (e1 ▸ hr₀.symm).trans hr⟩
  · intro h
    refine reach_map φ (fun a b hab => ?_) h
    obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hab
    have := dg_reach_of_mem (List.mem_map_of_mem (f := Comp.map φ) hc) hk
    simp only [Comp.map] at this
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · exact this.symm

/-- The dot excess of a list along an injective map of the atoms. -/
private theorem eL_map_inj {m : ℕ} {φ : Atom k n → Atom k m} (hφ : Function.Injective φ) :
    ∀ L : List (Comp (Atom k n)), eL (L.map (Comp.map φ)) = eL L
  | [] => by rw [List.map_nil, eL_nil, eL_nil]
  | c :: L => by
    rw [List.map_cons]
    by_cases hk : c.kind = .dot
    · have hk' : (c.map φ).kind = .dot := hk
      by_cases hr : (dg L).Reachable c.x c.y
      · rw [eL_cons_dot_red _ hk' ((dg_map_reach hφ).2 hr), eL_cons_dot_red _ hk hr,
          eL_map_inj hφ L]
      · rw [eL_cons_dot_new _ hk' (fun h => hr ((dg_map_reach hφ).1 h)), eL_cons_dot_new _ hk hr,
          eL_map_inj hφ L]
    · rw [eL_cons_nondot _ hk, eL_cons_nondot (c := c.map φ) _ hk, eL_map_inj hφ L]

/-- The dotted components of a term are those of `Γ`. -/
private theorem Sch.dots (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .dot) :
    (g.comps.filter fun c => decide (c.kind = .dot)).Perm
      ((Γ.comps.filter fun c => decide (c.kind = .dot)).map (Comp.map (liftA j))) := by
  obtain ⟨hR, K, h1, h2⟩ := hS
  refine (h2.filter _).trans ?_
  have e2 : (K ++ R).filter (fun c => decide (c.kind = .dot)) =
      K.filter (fun c => decide (c.kind = .dot)) := by
    rw [List.filter_append]
    have : R.filter (fun c => decide (c.kind = .dot)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      have := hR c hc
      intro h
      simp only [decide_eq_true_eq] at h
      rw [h] at this
      simp [Kind.isRandom] at this
    rw [this, List.append_nil]
  refine List.Perm.trans ?_ ((h1.filter _).map _).symm
  rw [e2, List.filter_map, List.filter_append]
  have hN' : N.filter ((fun c => decide (c.kind = .dot)) ∘ labF lab) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    simp [Function.comp, labF_kind, hN c hc]
  rw [hN', List.append_nil]
  unfold liftCs
  rw [List.filter_map, List.map_map]
  apply List.Perm.of_eq
  have hf : ((fun c => decide (c.kind = .dot)) ∘ labF lab) ∘ Comp.map (liftA j) =
      fun c : Comp (Atom k n) => decide (c.kind = .dot) := by
    funext c
    simp [Function.comp, labF_kind, Comp.map]
  rw [hf]
  apply List.map_congr_left
  intro c hc
  have hk : c.kind = .dot := by simpa using (List.mem_filter.1 hc).2
  simp only [Function.comp]
  exact labF_nonrandom lab (by simp [Comp.map, hk, Kind.isRandom])

private theorem Sch.eL_eq (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .dot) :
    eL g.comps = eL Γ.comps := by
  rw [eL_eq_eL_filter g.comps, eL_perm (hS.dots hN), eL_map_inj (liftA_injective j),
    ← eL_eq_eL_filter]

theorem Sch.dotExcess (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .dot) :
    g.dotExcess = Γ.dotExcess := hS.eL_eq hN

private theorem Sch.dg_eq (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .dot) :
    dg g.comps = dg (Γ.comps.map (Comp.map (liftA j))) := by
  rw [dg_congr (L := g.comps) (L' := g.comps.filter fun c => decide (c.kind = .dot))
      (fun c hk => by simp [hk]),
    dg_perm (hS.dots hN)]
  apply dg_congr
  intro c hk
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c₀, ⟨h, -⟩, rfl⟩; exact ⟨c₀, h, rfl⟩
  · rintro ⟨c₀, h, rfl⟩; exact ⟨c₀, ⟨h, hk⟩, rfl⟩

/-- The atoms of a graph with new atoms that are not images of the original atoms. -/
def isNewA (n : ℕ) {k m : ℕ} : Atom k m → Bool
  | .inl _ => false
  | .inr i => decide (n ≤ i.val)

private theorem isNewA_liftA (u : Atom k n) : isNewA n (liftA j u) = false := by
  rcases u with a | a <;> simp [isNewA, liftA]

private theorem isNewA_newA (i : Fin j) : isNewA n (newA i : Atom k (n + j)) = true := by
  simp [isNewA, newA]

private theorem isNewA_cases (u : Atom k (n + j)) :
    (isNewA n u = false ∧ ∃ v, u = liftA j v) ∨ (isNewA n u = true ∧ ∃ i : Fin j, u = newA i) := by
  rcases atom_cases (j := j) u with ⟨v, rfl⟩ | ⟨i, rfl⟩
  · exact Or.inl ⟨isNewA_liftA v, v, rfl⟩
  · exact Or.inr ⟨isNewA_newA i, i, rfl⟩

theorem Sch.mem_cases (hS : Sch Γ j R N lab g) {c : Comp (Atom k (n + j))} (hc : c ∈ g.comps) :
    (∃ c₀ ∈ Γ.comps, c = labF lab (c₀.map (liftA j))) ∨ ∃ c₁ ∈ N, c = labF lab c₁ := by
  obtain ⟨-, K, h1, h2⟩ := hS
  obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 (h2.mem_iff.1 hc)
  rcases List.mem_append.1 hc₁ with hK | hN
  · obtain ⟨c₀, hc₀, rfl⟩ := mem_liftCs.1 hK
    exact Or.inl ⟨c₀, h1.mem_iff.2 (List.mem_append_left _ hc₀), rfl⟩
  · exact Or.inr ⟨c₁, hN, rfl⟩

private theorem Sch.mem_of_nonrandom (hS : Sch Γ j R N lab g) {c₀ : Comp (Atom k n)} (hc₀ : c₀ ∈ Γ.comps)
    (hr : c₀.kind.isRandom = false) : c₀.map (liftA j) ∈ g.comps := by
  obtain ⟨hR, K, h1, h2⟩ := hS
  have hK : c₀ ∈ K := by
    rcases List.mem_append.1 (h1.mem_iff.1 hc₀) with h | h
    · exact h
    · rw [hR c₀ h] at hr; cases hr
  refine h2.mem_iff.2 (List.mem_map.2 ⟨c₀.map (liftA j), List.mem_append_left _
    (mem_liftCs.2 ⟨c₀, hK, rfl⟩), labF_nonrandom lab (by simpa [Comp.map] using hr)⟩)

theorem Sch.mem_N (hS : Sch Γ j R N lab g) {c : Comp (Atom k (n + j))} (hc : c ∈ N) :
    labF lab c ∈ g.comps := by
  obtain ⟨-, K, -, h2⟩ := hS
  exact h2.mem_iff.2 (List.mem_map.2 ⟨c, List.mem_append_right _ hc, rfl⟩)

private theorem Sch.sameBlock_lift (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .dot)
    (u v : Atom k n) : g.SameBlock (liftA j u) (liftA j v) ↔ Γ.SameBlock u v := by
  change (dg g.comps).Reachable _ _ ↔ (dg Γ.comps).Reachable _ _
  rw [hS.dg_eq hN]
  exact dg_map_reach (liftA_injective j)

private theorem Sch.sameBlock_new (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .dot)
    {u w : Atom k (n + j)} (hu : isNewA n u = true) (h : g.SameBlock u w) : w = u := by
  change (dg g.comps).Reachable _ _ at h
  rw [hS.dg_eq hN] at h
  obtain ⟨wk⟩ := h
  cases wk with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    obtain ⟨-, c, hc, -, hxy⟩ := dg_adj.1 hadj
    obtain ⟨c₀, -, rfl⟩ := List.mem_map.1 hc
    simp only [Comp.map] at hxy
    rcases hxy with ⟨h1, -⟩ | ⟨-, h1⟩
    · rw [← h1, isNewA_liftA] at hu; cases hu
    · rw [← h1, isNewA_liftA] at hu; cases hu

private theorem Sch.sepInt_iff (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .dot) :
    g.SepInt ↔ Γ.SepInt := by
  constructor
  · intro h a b hab
    have := h ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ ((hS.sameBlock_lift hN (.inr a) (.inr b)).2 hab)
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · intro h a b hab
    rcases isNewA_cases (j := j) (n := n) (Sum.inr a : Atom k (n + j)) with ⟨-, va, hva⟩ |
      ⟨ha, -⟩
    · rcases isNewA_cases (j := j) (n := n) (Sum.inr b : Atom k (n + j)) with ⟨-, vb, hvb⟩ |
        ⟨hb, -⟩
      · rw [hva, hvb] at hab
        have hb' := (hS.sameBlock_lift hN va vb).1 hab
        rcases va with va | va
        · simp [liftA] at hva
        rcases vb with vb | vb
        · simp [liftA] at hvb
        have e := h va vb hb'
        have : (Sum.inr a : Atom k (n + j)) = Sum.inr b := by rw [hva, hvb, e]
        exact Sum.inr.inj this
      · exact (Sum.inr.inj (hS.sameBlock_new hN hb hab.symm))
    · exact (Sum.inr.inj (hS.sameBlock_new hN ha hab)).symm

private theorem Graph.mfl_eq_of_iff {m : ℕ} {g₁ : Graph k m} {g₂ : Graph k n} (h : g₁.SepInt ↔ g₂.SepInt) :
    g₁.mfl = g₂.mfl := by
  unfold Graph.mfl
  by_cases h2 : g₂.SepInt
  · rw [if_pos (h.2 h2), if_pos h2]
  · rw [if_neg (fun h' => h2 (h.1 h')), if_neg h2]

private theorem Sch.xdotApart (hS : Sch Γ j R N lab g)
    (hN : ∀ c ∈ N, c.kind ≠ .dot ∧ c.kind ≠ .xdot) (hX : Γ.XdotApart) : g.XdotApart := by
  intro c hc hk hb
  rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
  · rw [labF_kind] at hk
    rw [labF_x, labF_y] at hb
    exact hX c₀ hc₀ hk ((hS.sameBlock_lift (fun c hc => (hN c hc).1) _ _).1 hb)
  · rw [labF_kind] at hk
    exact (hN c₁ hc₁).2 hk

private theorem Sch.plain (hS : Sch Γ j R N lab g) (hP : Γ.Plain) (hN : ∀ c ∈ N, NewOK c) : g.Plain := by
  intro c hc
  rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP c₀ hc₀
    refine ⟨by rw [labF_minor]; simp [Comp.map, p1], ?_, ?_, ?_, ?_, ?_⟩
    · rw [labF_kind]; exact p2
    · rw [labF_kind]; exact p3
    · rw [labF_kind, labF_x, labF_y]
      intro hk h
      exact p4 hk (liftA_injective j h)
    · rw [labF_kind, labF_x, labF_y]
      intro hw
      simp only [Comp.map] at hw ⊢
      rw [p5 hw]
    · intro hl
      cases lab with
      | none =>
        have : c₀.label.isSome = true := by simpa [labF, Comp.map] using hl
        simpa [labF_kind, Comp.map] using p6 this
      | some u =>
        rw [labF_label_some] at hl
        rw [labF_kind]
        split_ifs at hl with hr
        · exact hr
        · have : c₀.label.isSome = true := by simpa [Comp.map] using hl
          simpa [Comp.map] using p6 this
  · obtain ⟨p1, p2, p3, p4, p5⟩ := hN c₁ hc₁
    refine ⟨by rw [labF_minor]; exact p1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [labF_kind]; intro ch hk
      rcases p2 with ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ <;> rw [h] at hk <;> cases hk
    · rw [labF_kind]; intro ch d hk
      rcases p2 with ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ <;> rw [h] at hk <;> cases hk
    · rw [labF_kind]; intro hk
      rcases p2 with ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ <;> rw [h] at hk <;> cases hk
    · rw [labF_kind, labF_x, labF_y]; exact p3
    · intro hl
      cases lab with
      | none => exact p5 hl
      | some u =>
        rw [labF_label_some] at hl
        rw [labF_kind]
        split_ifs at hl with hr
        · exact hr
        · exact p5 hl

private theorem Sch.labelFree (hS : Sch Γ j R N none g) (hL : Γ.LabelFree)
    (hN : ∀ c ∈ N, c.label = none) : g.LabelFree := by
  intro c hc
  rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
  · simp [labF, Comp.map, hL c₀ hc₀]
  · exact hN _ hc₁

private theorem Sch.label_some (hS : Sch Γ j R N (some u) g) (hL : Γ.LabelFree)
    (hN : ∀ c ∈ N, c.label = none) :
    ∀ c ∈ g.comps, c.label = if c.kind.isRandom then some (.Q, u) else none := by
  intro c hc
  rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
  · rw [labF_label_some, labF_kind]
    simp [Comp.map, hL c₀ hc₀]
  · rw [labF_label_some, labF_kind, hN c₁ hc₁]

private theorem Sch.randomFirstInt (hS : Sch Γ j R N lab g) (hK : Γ.RandomFirstInt)
    (hN : ∀ c ∈ N, c.kind.isRandom = true → c.x.isRight = true) : g.RandomFirstInt := by
  intro c hc hr
  rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
  · rw [labF_kind] at hr
    rw [labF_x]
    simp only [Comp.map] at hr ⊢
    rw [liftA_isRight]
    exact hK c₀ hc₀ hr
  · rw [labF_kind] at hr
    rw [labF_x]
    exact hN c₁ hc₁ hr

private theorem Sch.molReach (hS : Sch Γ j R N lab g) {u v : Atom k n} (h : Γ.molGraph.Reachable u v) :
    g.molGraph.Reachable (liftA j u) (liftA j v) := by
  refine molReach_map (liftA j) (fun c hc hk => ?_) h
  have hr : c.kind.isRandom = false := by
    revert hk; cases c.kind <;> simp [Kind.joinsMol, Kind.isRandom]
  exact Graph.molReach_of_comp (hS.mem_of_nonrandom hc hr) hk

private theorem Sch.sameMol (hS : Sch Γ j R N lab g) {u v : Atom k n} (h : Γ.SameMol u v) :
    g.SameMol (liftA j u) (liftA j v) := by
  rcases h with rfl | ⟨hu, hv, hr⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by rw [liftA_isRight]; exact hu, by rw [liftA_isRight]; exact hv,
      hS.molReach hr⟩

private theorem Sch.hasXdot (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .xdot) (a b : Atom k (n + j)) :
    g.hasXdot a b = true ↔ ∃ c₀ ∈ Γ.comps, c₀.kind = .xdot ∧
      (liftA j c₀.x = a ∧ liftA j c₀.y = b ∨ liftA j c₀.x = b ∧ liftA j c₀.y = a) := by
  simp only [Graph.hasXdot, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨c, hc, hk, hxy⟩
    rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
    · rw [labF_kind] at hk
      rw [labF_x, labF_y] at hxy
      exact ⟨c₀, hc₀, hk, hxy⟩
    · rw [labF_kind] at hk
      exact absurd hk (hN c₁ hc₁)
  · rintro ⟨c₀, hc₀, hk, hxy⟩
    exact ⟨c₀.map (liftA j), hS.mem_of_nonrandom hc₀ (by simp [hk, Kind.isRandom]), hk, hxy⟩

private theorem Sch.hasXdot_lift (hS : Sch Γ j R N lab g) (hN : ∀ c ∈ N, c.kind ≠ .xdot) (a b : Atom k n) :
    g.hasXdot (liftA j a) (liftA j b) = Γ.hasXdot a b := by
  have h1 := hS.hasXdot hN (liftA j a) (liftA j b)
  have h2 : Γ.hasXdot a b = true ↔ ∃ c₀ ∈ Γ.comps, c₀.kind = .xdot ∧
      (c₀.x = a ∧ c₀.y = b ∨ c₀.x = b ∧ c₀.y = a) := by
    simp only [Graph.hasXdot, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
  have hi := liftA_injective (k := k) (n := n) j
  apply Bool.eq_iff_iff.2
  rw [h1, h2]
  constructor
  · rintro ⟨c₀, hc₀, hk, h | h⟩
    · exact ⟨c₀, hc₀, hk, Or.inl ⟨hi h.1, hi h.2⟩⟩
    · exact ⟨c₀, hc₀, hk, Or.inr ⟨hi h.1, hi h.2⟩⟩
  · rintro ⟨c₀, hc₀, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨c₀, hc₀, hk, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨c₀, hc₀, hk, Or.inr ⟨rfl, rfl⟩⟩

/-- The data of `O_dot` for a term, from its new components. -/
theorem Sch.dotNew {C : ℕ} (hS : Sch Γ j R N lab g) (hNorm : Γ.Normal C)
    (hN : ∀ c ∈ N, c.kind ≠ .dot ∧ c.kind ≠ .xdot) {s : ℕ}
    (two : ∀ i : Fin j, (N.filter fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2)
    (old : (N.filter fun c => c.kind.isSolid && !g.hasXdot c.x c.y && !isNewA n c.x &&
      !isNewA n c.y).length ≤ s)
    (four : (N.filter fun c => c.kind.isSolid).length ≤ 4)
    (zero : s = 0 → (N.filter fun c => c.kind.isSolid).length ≤ 2) :
    DotNew g s (isNewA n) := by
  have hNx : ∀ c ∈ N, c.kind ≠ .xdot := fun c hc => (hN c hc).2
  -- solid components of `Γ` moved to `g` have a `×`-dotted partner
  have hold : ∀ c₀ ∈ Γ.comps, c₀.kind.isSolid = true →
      g.hasXdot (c₀.map (liftA j)).x (c₀.map (liftA j)).y = true := by
    intro c₀ hc₀ hs
    simp only [Comp.map]
    rw [hS.hasXdot_lift hNx]
    obtain ⟨-, hl, hx⟩ := hNorm
    have hne := hl c₀ hc₀ hs
    obtain ⟨d, hd, hdk, hdxy⟩ := (hx c₀.x c₀.y hne).2 ⟨c₀, hc₀, hs, Or.inl ⟨rfl, rfl⟩⟩
    simp only [Graph.hasXdot, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    exact ⟨d, hd, hdk, hdxy⟩
  have hcount : ∀ P : Comp (Atom k (n + j)) → Bool, (∀ c, P (labF lab c) = P c) →
      (∀ c, P c = true → unpB g c = true) → (g.comps.filter P).length ≤ (N.filter P).length := by
    intro P hP hPu
    have := hS.count P hP
    have h0 : (Γ.comps.filter fun c => P (c.map (liftA j))).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc hPc
      have hu := hPu _ hPc
      simp only [unpB, Bool.and_eq_true, Bool.not_eq_true'] at hu
      have := hold c hc hu.1
      rw [hu.2] at this
      cases this
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc hk
    rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
    · rw [labF_x, labF_y]
      exact ⟨isNewA_liftA _, isNewA_liftA _⟩
    · rw [labF_kind] at hk
      rcases hk with hk | hk
      · exact absurd hk (hN c₁ hc₁).1
      · exact absurd hk (hN c₁ hc₁).2
  · intro α hα
    obtain ⟨i, rfl⟩ : ∃ i : Fin j, α = newA i := by
      rcases isNewA_cases (n := n) (j := j) α with ⟨h, -⟩ | ⟨-, h⟩
      · rw [h] at hα; cases hα
      · exact h
    refine (hcount _ (fun c => by simp [unpB, labF_kind, labF_x, labF_y])
      (fun c h => by simp only [Bool.and_eq_true] at h; exact h.1)).trans
      (le_trans (length_filter_mono _ _ _ fun c _ h => ?_) (two i))
    simp only [unpB, Bool.and_eq_true] at h ⊢
    exact ⟨h.1.1, by simpa [atB] using h.2⟩
  · refine (hcount _ (fun c => by simp [unpB, labF_kind, labF_x, labF_y])
      (fun c h => by simp only [Bool.and_eq_true] at h; exact h.1.1)).trans
      (le_trans (length_filter_mono _ _ _ fun c _ h => ?_) old)
    simp only [unpB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2⟩, h.2⟩
  · refine (hcount _ (fun c => by simp [unpB, labF_kind, labF_x, labF_y]) (fun c h => h)).trans
      (le_trans (length_filter_mono _ _ _ fun c _ h => ?_) four)
    simp only [unpB, Bool.and_eq_true] at h
    exact h.1
  · intro h0
    refine (hcount _ (fun c => by simp [unpB, labF_kind, labF_x, labF_y]) (fun c h => h)).trans
      (le_trans (length_filter_mono _ _ _ fun c _ h => ?_) (zero h0))
    simp only [unpB, Bool.and_eq_true] at h
    exact h.1

/-- The last condition of `Graph.stdNeutralAt` on the list of ends. -/
private def stdM : List (Bool × Charge) → Bool
  | [e₁, e₂] => matchedEnds e₁ e₂ && e₁.2 != e₂.2
  | _ => false

private theorem stdM_perm {l l' : List (Bool × Charge)} (h : l.Perm l') : stdM l = stdM l' := by
  match l, h.length_eq with
  | [a, b], _ =>
    rcases List.perm_pair.1 h.symm with rfl | rfl
    · rfl
    · simp only [stdM, matchedEnds]
      cases a.1 <;> cases b.1 <;> cases a.2 <;> cases b.2 <;> rfl
  | [], hl => match l', hl with | [], _ => rfl
  | [_], hl => match l', hl with | [_], _ => rfl
  | _ :: _ :: _ :: _, hl => match l', hl with | _ :: _ :: _ :: _, _ => rfl

private theorem std_eq (g : Graph k n) (u : Atom k n) : g.stdNeutralAt u =
    (((g.comps.filter (atB u)).filter fun c => c.kind != .xdot).length == 3 &&
      (((g.comps.filter (atB u)).filter fun c => c.kind != .xdot).filter
        fun c => c.kind.isSolid).length == 2 &&
      (((g.comps.filter (atB u)).filter fun c => c.kind != .xdot).filter
        fun c => c.kind == .waved .s).length == 1 && stdM (g.ends u)) := by
  rw [← cs_local]
  rfl

/-- Two graphs whose components at `u` and `u'` correspond up to order have the same degree,
ends up to order and standard neutral status there. -/
private theorem local_transfer_perm {m : ℕ} {g : Graph k n} {g' : Graph k m} {u : Atom k n}
    {u' : Atom k m} (f : Atom k n → Atom k m) (hf : ∀ a, f a = u' ↔ a = u)
    (h : (g'.comps.filter (atB u')).Perm ((g.comps.filter (atB u)).map (Comp.map f))) :
    g'.deg u' = g.deg u ∧ (g'.ends u').Perm (g.ends u) ∧ g'.stdNeutralAt u' = g.stdNeutralAt u := by
  have hends : (g'.ends u').Perm (g.ends u) := by
    rw [ends_local, ends_local]
    refine (h.filterMap _).trans (List.Perm.of_eq ?_)
    rw [List.filterMap_map]
    congr 1
    funext c
    simp only [Function.comp, endF, Comp.map, ne_eq]
    have h1 : (f c.x = u') ↔ (c.x = u) := hf c.x
    have h2 : (f c.y = u') ↔ (c.y = u) := hf c.y
    simp only [h1, h2]
  have hcs := h.filter (fun c => c.kind != .xdot)
  rw [List.filter_map] at hcs
  have hsame : ∀ (P : Comp (Atom k m) → Bool) (Q : Comp (Atom k n) → Bool),
      (∀ c, P (c.map f) = Q c) →
      (((g'.comps.filter (atB u')).filter fun c => c.kind != .xdot).filter P).length =
        (((g.comps.filter (atB u)).filter fun c => c.kind != .xdot).filter Q).length := by
    intro P Q hPQ
    rw [(hcs.filter P).length_eq, List.filter_map, List.length_map]
    have e : ((fun c : Comp (Atom k m) => c.kind != .xdot) ∘ Comp.map f) =
        fun c => c.kind != .xdot := by
      funext c; rfl
    rw [e]
    congr 1
    apply List.filter_congr
    intro c _
    simp [Function.comp, hPQ]
  refine ⟨?_, hends, ?_⟩
  · rw [deg_local, deg_local, (h.filter _).length_eq, List.filter_map, List.length_map]
    rfl
  · rw [std_eq, std_eq, stdM_perm hends]
    have e1 := hsame (fun _ => true) (fun _ => true) (fun _ => rfl)
    have e2 := hsame (fun c => c.kind.isSolid) (fun c => c.kind.isSolid) (fun _ => rfl)
    have e3 := hsame (fun c => c.kind == .waved .s) (fun c => c.kind == .waved .s) (fun _ => rfl)
    simp only [List.filter_true] at e1
    rw [e1, e2, e3]

private theorem beq_liftA (a b : Atom k n) : (liftA j a == liftA j b) = (a == b) := by
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq]
  exact (liftA_injective j).eq_iff

/-- Degree and standard neutral status at an atom of `Γ` untouched by the removed and the new
components of a term without labels. -/
private theorem Sch.local_untouched (hS : Sch Γ j R N none g) {u : Atom k n}
    (hR : ∀ c ∈ R, atB u c = false) (hN : ∀ c ∈ N, atB (liftA j u) c = false) :
    g.deg (liftA j u) = Γ.deg u ∧ g.stdNeutralAt (liftA j u) = Γ.stdNeutralAt u := by
  obtain ⟨-, K, h1, h2⟩ := hS
  have hl : (g.comps.filter (atB (liftA j u))).Perm ((Γ.comps.filter (atB u)).map
      (Comp.map (liftA j))) := by
    refine (h2.filter _).trans ?_
    refine List.Perm.trans ?_ ((h1.filter _).map _).symm
    have eN : N.filter (atB (liftA j u)) = [] :=
      List.filter_eq_nil_iff.2 (fun c hc => by simp [hN c hc])
    have eR : R.filter (atB u) = [] := List.filter_eq_nil_iff.2 (fun c hc => by simp [hR c hc])
    rw [show (liftCs j K ++ N).map (labF none) = liftCs j K ++ N from List.map_id _,
      List.filter_append, List.filter_append, eN, eR, List.append_nil, List.append_nil]
    unfold liftCs
    rw [List.filter_map]
    apply List.Perm.of_eq
    congr 1
    apply List.filter_congr
    intro c _
    simp only [Function.comp, atB, Comp.map, beq_liftA]
  have := local_transfer_perm (liftA j) (fun a => (liftA_injective j).eq_iff) hl
  exact ⟨this.1, this.2.2⟩

/-- The light weights, regular weights and solid edges at external atoms of a term. -/
theorem Sch.lwN (hS : Sch Γ j R N lab g) :
    g.lwN + (R.filter fun c => c.kind.isLt).length = Γ.lwN + (N.filter fun c => c.kind.isLt).length := by
  have := hS.count (fun c => c.kind.isLt) (fun c => by rw [labF_kind])
  simpa [Graph.lwN, Comp.map] using this

private theorem Sch.rwN (hS : Sch Γ j R N lab g) :
    g.rwN + (R.filter fun c => c.kind.isRg).length = Γ.rwN + (N.filter fun c => c.kind.isRg).length := by
  have := hS.count (fun c => c.kind.isRg) (fun c => by rw [labF_kind])
  simpa [Graph.rwN, Comp.map] using this

private theorem Sch.eextN (hS : Sch Γ j R N lab g) :
    g.eextN + (R.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length =
      Γ.eextN + (N.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length := by
  have := hS.count (fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft))
    (fun c => by rw [labF_kind, labF_x, labF_y])
  have hl : ∀ u : Atom k n, (liftA j u).isLeft = u.isLeft := fun u => liftA_isLeft j u
  simpa [Graph.eextN, Comp.map, hl] using this

private theorem Sch.deg (hS : Sch Γ j R N lab g) (u : Atom k n) :
    g.deg (liftA j u) + (R.filter fun c => c.kind.isSolid && atB u c).length =
      Γ.deg u + (N.filter fun c => c.kind.isSolid && atB (liftA j u) c).length := by
  have := hS.count (fun c => c.kind.isSolid && atB (liftA j u) c)
    (fun c => by simp [labF_kind, labF_x, labF_y, atB])
  have hi := liftA_injective (k := k) (n := n) j
  have e : ∀ c : Comp (Atom k n), ((c.map (liftA j)).kind.isSolid &&
      atB (liftA j u) (c.map (liftA j))) = (c.kind.isSolid && atB u c) := by
    intro c
    simp only [Comp.map, atB, beq_liftA]
  simp only [e] at this
  simpa [Graph.deg, atB] using this

private theorem Sch.deg_new (hS : Sch Γ j R N lab g) (i : Fin j) :
    g.deg (newA i) = (N.filter fun c => c.kind.isSolid && atB (newA i) c).length := by
  have := hS.count (fun c => c.kind.isSolid && atB (newA i) c)
    (fun c => by simp [labF_kind, labF_x, labF_y, atB])
  have e1 : (R.filter fun c => (c.map (liftA j)).kind.isSolid && atB (newA i) (c.map (liftA j))) =
      [] := by
    rw [List.filter_eq_nil_iff]
    intro c _
    simp [atB, Comp.map, liftA_ne_newA]
  have e2 : (Γ.comps.filter fun c => (c.map (liftA j)).kind.isSolid &&
      atB (newA i) (c.map (liftA j))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c _
    simp [atB, Comp.map, liftA_ne_newA]
  rw [e1, e2] at this
  simpa [Graph.deg, atB] using this

end Sch

/-! ## `O_dot` after a term of a local operation -/

section DotStep

variable {k n : ℕ}

private theorem foldl_spStep_subset (l acc : List (Atom k n × Atom k n)) :
    ∀ q ∈ l.foldl spStep acc, q ∈ acc ∨ q ∈ l := by
  induction l generalizing acc with
  | nil => intro q hq; exact Or.inl hq
  | cons p l ih =>
    intro q hq
    rcases ih _ q hq with h | h
    · unfold spStep at h
      split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons.2 (Or.inl (List.mem_singleton.1 h)))
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem sp_ne {g : Graph k n} {p : Atom k n × Atom k n × Bool} (hp : p ∈ g.splitPairs) :
    p.1 ≠ p.2.1 := by
  obtain ⟨hq, -, -⟩ := mem_splitPairs.1 hp
  unfold spUniq at hq
  rcases foldl_spStep_subset _ [] _ hq with h | h
  · simp at h
  · unfold spCand at h
    obtain ⟨c, -, hc⟩ := List.mem_filterMap.1 h
    split_ifs at hc with hcc
    · have h1 := Option.some.inj hc
      have h2 : c.x = p.1 := congrArg Prod.fst h1
      have h3 : c.y = p.2.1 := congrArg Prod.snd h1
      have : c.x ≠ c.y := by simpa using (by simpa using hcc : _ ∧ c.x ≠ c.y).2
      rw [h2, h3] at this
      exact this

private theorem mem_dotChoice_of_ne_xdot (Γ : Graph k n) (SP A : List (Atom k n × Atom k n × Bool))
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hk : c.kind ≠ .xdot) :
    c ∈ (Γ.dotChoice SP A).comps := by
  rw [dotChoice_eq]
  exact List.mem_append_left _ ((mem_keptComps Γ SP c).2 ⟨hc, fun h => hk h.1⟩)

private theorem Comp.map_minor_nil {V W : Type*} (f : V → W) {c : Comp V} (h : c.minor = []) :
    (c.map f).minor = [] := by simp [Comp.map, h]

private theorem plain_dotChoice {g : Graph k n} (hP : g.Plain)
    (A : List (Atom k n × Atom k n × Bool)) : (g.dotChoice g.splitPairs A).Plain := by
  intro c hc
  have hc' : c ∈ keptComps g g.splitPairs ++ addedComps g.splitPairs A := hc
  rcases List.mem_append.1 hc' with h | h
  · exact hP c ((mem_keptComps g _ c).1 h).1
  · obtain ⟨p, hp, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 h
    · refine ⟨rfl, fun ch => by simp [mkC], fun ch d => by simp [mkC], fun _ => sp_ne hp, ?_, ?_⟩
      · intro hw; simp [mkC, Kind.isWeight] at hw
      · intro hl; simp [mkC] at hl
    · refine ⟨rfl, fun ch => by simp [mkC], fun ch d => by simp [mkC],
        fun hk => by simp [mkC] at hk, ?_, ?_⟩
      · intro hw; simp [mkC, Kind.isWeight] at hw
      · intro hl; simp [mkC] at hl

private theorem MergeSpec.plain {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t)
    (hP : h.Plain) :
    t.g.Plain := by
  intro c' hc'
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP c hc
  unfold mergeComp at hm
  split_ifs at hm with hd hsol
  · obtain rfl := Option.some.inj hm
    obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hsol
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Comp.map, h1]
    · intro ch' h; simp [hch, Kind.toWeight] at h
    · intro ch' d' h; simp [hch, Kind.toWeight] at h
    · intro h; simp [hch, Kind.toWeight] at h
    · intro _; rfl
    · intro hl
      simp [hch, Kind.toWeight, Kind.isRandom]
  · obtain rfl := Option.some.inj hm
    refine ⟨Comp.map_minor_nil _ h1, ?_, ?_, ?_, ?_, ?_⟩
    · intro ch' h; exact h2 ch' (by simpa [Comp.map] using h)
    · intro ch' d' h; exact h3 ch' d' (by simpa [Comp.map] using h)
    · intro hk
      have hkc : c.kind = .dot := by simpa [Comp.map] using hk
      simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hd
      have := hd hkc
      simpa [Comp.map] using this
    · intro hw
      have := h5 (by simpa [Comp.map] using hw)
      simp [Comp.map, this]
    · intro hl
      have : c.label.isSome = true := by simpa [Comp.map] using hl
      simpa [Comp.map] using h6 this

private theorem labels_le_one_of {g : Graph k n} (p : PQ × Atom k n)
    (h : ∀ c ∈ g.comps, c.label = none ∨ c.label = some p) : g.labels.length ≤ 1 := by
  unfold Graph.labels
  have hsub : (g.comps.filterMap Comp.label).dedup ⊆ [p] := by
    intro q hq
    rw [List.mem_dedup, List.mem_filterMap] at hq
    obtain ⟨c, hc, hl⟩ := hq
    rcases h c hc with h1 | h1 <;> rw [h1] at hl
    · cases hl
    · rw [Option.some.injEq] at hl; rw [← hl]; exact List.mem_singleton_self _
  exact ((List.nodup_dedup _).subperm hsub).length_le

private theorem mergeComp_x {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : mergeComp rep f c = some c') :
    c'.x = f c.x := by
  unfold mergeComp at h
  split_ifs at h
  · obtain rfl := Option.some.inj h; rfl
  · obtain rfl := Option.some.inj h; rfl

private theorem mergeComp_random {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : mergeComp rep f c = some c') :
    c'.kind.isRandom = c.kind.isRandom := by
  rcases mergeComp_kind h with h1 | ⟨ch, h1, h2⟩
  · rw [h1]
  · rw [h1, h2]; rfl

variable {Γ : Graph k n} {t : Tracked k n}

private theorem MergeSpec.randomFirstInt (hs : MergeSpec Γ t) (hK : Γ.RandomFirstInt) :
    t.g.RandomFirstInt := by
  intro c' hc' hr
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rw [mergeComp_random hm] at hr
  rw [mergeComp_x hm, hs.isRight]
  exact hK c hc hr

private theorem MergeSpec.labelFree (hs : MergeSpec Γ t) (hL : Γ.LabelFree) : t.g.LabelFree := by
  intro c' hc'
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rw [mergeComp_label hm, hL c hc]
  rfl

private theorem MergeSpec.qGraph (hs : MergeSpec Γ t) {u : Atom k n}
    (hall : ∀ c ∈ Γ.comps, c.label = if c.kind.isRandom then some (.Q, u) else none)
    (hex : ∃ c ∈ Γ.comps, c.kind.isRandom = true) : t.g.IsQGraph := by
  refine ⟨t.f u, ?_, ?_⟩
  · obtain ⟨c, hc, hr⟩ := hex
    have hd : c.kind ≠ .dot := by intro h; rw [h] at hr; cases hr
    obtain ⟨c', hm⟩ : ∃ c', mergeComp Γ.mrep t.f c = some c' := by
      cases hmc : mergeComp Γ.mrep t.f c with
      | none => exact absurd (mergeComp_none hmc).1 hd
      | some c' => exact ⟨c', rfl⟩
    refine ⟨c', hs.mem_comps.2 ⟨c, hc, hm⟩, ?_⟩
    rw [mergeComp_label hm, hall c hc, if_pos hr]
    rfl
  · intro c' hc' hrl
    obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
    rw [mergeComp_label hm, hall c hc]
    rw [mergeComp_random hm, mergeComp_label hm, hall c hc] at hrl
    by_cases hr : c.kind.isRandom = true
    · rw [if_pos hr]; rfl
    · rw [if_neg hr] at hrl ⊢
      simp at hrl
      exact absurd hrl hr

private theorem MergeSpec.molReach (hs : MergeSpec Γ t) {u v : Atom k n} (h : Γ.molGraph.Reachable u v) :
    t.g.molGraph.Reachable (t.f u) (t.f v) := by
  refine molReach_map t.f (fun c hc hk => ?_) h
  by_cases hd : c.kind = .dot
  · by_cases he : t.f c.x = t.f c.y
    · rw [he]
    · have hm : mergeComp Γ.mrep t.f c = some (c.map t.f) := by
        rw [mergeComp_dot hd, if_neg he]
      exact Graph.molReach_of_comp (hs.mem_comps.2 ⟨c, hc, hm⟩) (by simpa [Comp.map] using hk)
  · have hsol : c.kind.isSolid = false := by
      revert hk; cases c.kind <;> simp [Kind.joinsMol, Kind.isSolid]
    exact Graph.molReach_of_comp (hs.mem_of_other hc hd hsol) (by simpa [Comp.map] using hk)

private theorem MergeSpec.sameMol (hs : MergeSpec Γ t) {u v : Atom k n} (h : Γ.SameMol u v) :
    t.g.SameMol (t.f u) (t.f v) := by
  rcases h with rfl | ⟨hu, hv, hr⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by rw [hs.isRight]; exact hu, by rw [hs.isRight]; exact hv, hs.molReach hr⟩

/-- `O_dot` output facts on a graph `h`: the input facts of `O_dot`, the clauses kept by its
outputs. -/
private theorem oDotT_keep {h : Graph k n} (hd : DotIn h) {t : Tracked k n} (ht : t ∈ oDotT h) :
    t.g.XdotApart ∧ (h.RandomFirstInt → t.g.RandomFirstInt) ∧ t.g.Plain ∧
    (h.LabelFree → t.g.LabelFree) ∧
    (∀ u, (∀ c ∈ h.comps, c.label = if c.kind.isRandom then some (.Q, u) else none) →
      (∃ c ∈ h.comps, c.kind.isRandom = true) → t.g.IsQGraph) ∧
    (∀ u v, h.SameMol u v → t.g.SameMol (t.f u) (t.f v)) ∧ (∀ u', ∃ u, t.g.SameMol u' (t.f u)) := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · refine ⟨hd.xa, id, hd.plain, id, fun u hall ⟨c, hc, hr⟩ => ⟨u, ⟨c, hc, ?_⟩, ?_⟩,
      fun u v h => h, fun u' => ⟨u', Or.inl rfl⟩⟩
    · rw [hall c hc, if_pos hr]
      rfl
    · intro c hc hrl
      rw [hall c hc] at hrl ⊢
      split_ifs at hrl ⊢ with hr
      · rfl
      · rcases hrl with hrl | hrl
        · exact absurd hrl hr
        · cases hrl
  · have hs := mergeT_spec hm
    set dc := h.dotChoice h.splitPairs A with hdc
    have hmem : ∀ c ∈ dc.comps, c ∈ h.comps ∨ (c.label = none ∧ (c.kind = .dot ∨ c.kind = .xdot)) := by
      intro c hc
      rw [hdc, dc_comps] at hc
      rcases List.mem_append.1 hc with h1 | h1
      · exact Or.inl ((mem_keptComps _ _ _).1 h1).1
      · exact Or.inr (addedComps_label h1)
    refine ⟨hs.xdotApart, fun hK => hs.randomFirstInt ?_, hs.plain (plain_dotChoice hd.plain A),
      fun hL => hs.labelFree ?_, fun u hall hex => hs.qGraph (u := u) ?_ ?_, ?_, ?_⟩
    · intro c hc hr
      rcases hmem c hc with h1 | ⟨-, h1 | h1⟩
      · exact hK c h1 hr
      · rw [h1] at hr; cases hr
      · rw [h1] at hr; cases hr
    · intro c hc
      rcases hmem c hc with h1 | ⟨h1, -⟩
      · exact hL c h1
      · exact h1
    · intro c hc
      rcases hmem c hc with h1 | ⟨h1, h2 | h2⟩
      · exact hall c h1
      · rw [h1, h2]; rfl
      · rw [h1, h2]; rfl
    · obtain ⟨c, hc, hr⟩ := hex
      have hk : c.kind ≠ .xdot := by intro h; rw [h] at hr; cases hr
      exact ⟨c, mem_dotChoice_of_ne_xdot h _ A hc hk, hr⟩
    · intro u v huv
      refine hs.sameMol ?_
      rcases huv with rfl | ⟨hu, hv, hr⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨hu, hv, molReach_map id (fun c hc hk => ?_) hr⟩
        have hx : c.kind ≠ .xdot := by intro h; rw [h] at hk; cases hk
        exact Graph.molReach_of_comp (mem_dotChoice_of_ne_xdot h _ A hc hx) hk
    · intro u'
      obtain ⟨u, rfl⟩ := hs.f_surj u'
      exact ⟨u, Or.inl rfl⟩

end DotStep

/-! ## The step: a term of a local operation followed by `O_dot` -/

section SchStep

variable {k n : ℕ}

/-- `(mfl, eextN, phi)` decreases lexicographically. -/
def LexLt {m m' : ℕ} (g' : Graph k m') (g : Graph k m) : Prop :=
  g'.mfl < g.mfl ∨ (g'.mfl ≤ g.mfl ∧ (g'.eextN < g.eextN ∨ (g'.eextN ≤ g.eextN ∧ g'.phi < g.phi)))

private theorem Graph.mfl_of_sepInt {g : Graph k n} (h : g.SepInt) : g.mfl = 0 := by
  unfold Graph.mfl; rw [if_pos h]

private theorem Graph.mfl_of_not_sepInt {g : Graph k n} (h : ¬ g.SepInt) : g.mfl = 1 := by
  unfold Graph.mfl; rw [if_neg h]

theorem NewOK.ne_dot {V : Type*} {c : Comp V} (h : NewOK c) : c.kind ≠ .dot := by
  obtain ⟨-, h2, -⟩ := h
  rcases h2 with ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ <;> rw [h] <;> simp

theorem NewOK.ne_xdot' {V : Type*} {c : Comp V} (h : NewOK c) : c.kind ≠ .xdot := by
  obtain ⟨-, h2, -⟩ := h
  rcases h2 with ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ | ⟨c', h⟩ <;> rw [h] <;> simp

variable {Γ : Graph k n} {j : ℕ} {R : List (Comp (Atom k n))} {N : List (Comp (Atom k (n + j)))}
  {lab : Option (Atom k (n + j))} {g : Graph k (n + j)}

theorem Sch.dotIn {C : ℕ} (hS : Sch Γ j R N lab g) (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hX : Γ.XdotApart) (hNo : ∀ c ∈ N, NewOK c ∧ c.label = none) :
    DotIn g := by
  have hNd : ∀ c ∈ N, c.kind ≠ .dot ∧ c.kind ≠ .xdot :=
    fun c hc => ⟨(hNo c hc).1.ne_dot, (hNo c hc).1.ne_xdot'⟩
  refine ⟨hS.plain hP (fun c hc => (hNo c hc).1), ?_, ?_, hS.xdotApart hNd hX, ?_⟩
  · intro c hc hk
    rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
    · rw [labF_kind] at hk
      rw [labF_x, labF_y]
      simp only [Comp.map, liftA_isRight]
      rcases hN.1.noIntDot c₀ hc₀ hk with h | h
      · left; cases hx : c₀.x <;> simp_all
      · right; cases hy : c₀.y <;> simp_all
    · rw [labF_kind] at hk
      exact absurd hk (hNd c₁ hc₁).1
  · intro c hc hk
    rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
    · rw [labF_kind] at hk
      rw [labF_x, labF_y]
      intro h
      exact hN.2.1 c₀ hc₀ hk (liftA_injective j h)
    · rw [labF_kind] at hk
      rw [labF_x, labF_y]
      exact (hNo c₁ hc₁).1.2.2.2.1 hk
  · cases lab with
    | none =>
      have := hS.labelFree hL (fun c hc => (hNo c hc).2)
      have h0 : g.labels = [] := by
        unfold Graph.labels
        rw [List.filterMap_eq_nil_iff.2 (fun c hc => this c hc)]
        rfl
      rw [h0]
      exact Nat.zero_le _
    | some u =>
      have := hS.label_some hL (fun c hc => (hNo c hc).2)
      refine labels_le_one_of (.Q, u) (fun c hc => ?_)
      rw [this c hc]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl

private theorem isNewA_pos {α : Atom k (n + j)} (h : isNewA n α = true) : j ≠ 0 := by
  rcases α with a | a
  · simp [isNewA] at h
  · simp only [isNewA, decide_eq_true_eq] at h
    have := a.2
    omega

/-- The step of a local operation: a term with the schema `Sch`, then `O_dot`. The dot excess and
the reduced order do not decrease; at equal reduced order, `(mfl, eextN, phi)` decreases; the
`×`-dotted edges stay outside blocks; the first atoms of random components stay internal;
molecules are kept. -/
private theorem Sch.step {C : ℕ} (hS : Sch Γ j R N lab g) (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart)
    (hNo : ∀ c ∈ N, NewOK c ∧ c.label = none)
    (hNK : ∀ c ∈ N, c.kind.isRandom = true → c.x.isRight = true)
    {s : ℕ} (hs : ordL N = ordL R + 2 * j + s)
    (two : ∀ i : Fin j, (N.filter fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2)
    (old : (N.filter fun c => c.kind.isSolid && !g.hasXdot c.x c.y && !isNewA n c.x &&
      !isNewA n c.y).length ≤ s)
    (four : (N.filter fun c => c.kind.isSolid).length ≤ 4)
    (zero : s = 0 → (N.filter fun c => c.kind.isSolid).length ≤ 2)
    (hext : (N.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length ≤
      (R.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length)
    (hphi : lab = none → s = 0 → g.phi + (if j = 0 then 1 else 3) ≤ Γ.phi)
    {t : Tracked k (n + j)} (ht : t ∈ oDotT g) :
    Γ.dotExcess ≤ t.g.dotExcess ∧ Γ.obl ≤ t.g.obl ∧
    (lab = none → t.g.obl = Γ.obl → LexLt t.g Γ) ∧
    t.g.XdotApart ∧ t.g.RandomFirstInt ∧ t.g.Plain ∧ (lab = none → t.g.LabelFree) ∧
    (∀ u, lab = some u → (∃ c ∈ g.comps, c.kind.isRandom = true) → t.g.IsQGraph) ∧
    (∀ u v, Γ.SameMol u v → t.g.SameMol (t.f (liftA j u)) (t.f (liftA j v))) ∧
    (∀ u', ∃ u, t.g.SameMol u' (t.f u)) := by
  have hNd : ∀ c ∈ N, c.kind ≠ .dot ∧ c.kind ≠ .xdot :=
    fun c hc => ⟨(hNo c hc).1.ne_dot, (hNo c hc).1.ne_xdot'⟩
  have hd := hS.dotIn hN hP hL hX hNo
  have hn := hS.dotNew hN hNd two old four zero
  have hexc : g.dotExcess = Γ.dotExcess := hS.dotExcess (fun c hc => (hNd c hc).1)
  have hord : g.ord = Γ.ord + s := by
    have := hS.ord
    linarith
  have hobl : g.obl = Γ.obl + s := by
    simp only [Graph.obl, hord, hexc]
    ring
  have hmfl : g.mfl = Γ.mfl := Graph.mfl_eq_of_iff (hS.sepInt_iff (fun c hc => (hNd c hc).1))
  have hee : g.eextN ≤ Γ.eextN := by
    have := hS.eextN
    omega
  obtain ⟨h1, h2⟩ := dot_obl hd hn ht
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := oDotT_keep hd ht
  refine ⟨hexc ▸ h1, by linarith, ?_, k1, k2 (hS.randomFirstInt hK hNK), k3,
    fun hl => k4 (by subst hl; exact hS.labelFree hL (fun c hc => (hNo c hc).2)), ?_,
    fun u v huv => k6 _ _ (hS.sameMol huv), k7⟩
  · intro hl heq
    rcases mem_oDotT_cases ht with rfl | ⟨A, hA, hm⟩
    · have hs0 : s = 0 := by
        change g.obl = Γ.obl at heq
        omega
      have := hphi hl hs0
      have h1 : 1 ≤ (if j = 0 then 1 else 3) := by split_ifs <;> omega
      exact Or.inr ⟨hmfl.le, Or.inr ⟨hee, by change g.phi < Γ.phi; omega⟩⟩
    · have hsT := mergeT_spec hm
      have hmt : t.g.mfl = 0 := Graph.mfl_of_sepInt hsT.sepInt
      by_cases hsep : g.SepInt
      · have hg0 : g.mfl = 0 := Graph.mfl_of_sepInt hsep
        have heq' : t.g.obl = g.obl - s := by rw [heq, hobl]; ring
        rcases dot_equal3 hd hn hsep hA hm heq' with h | ⟨hs0, hp, he⟩ |
            ⟨hs0, α, -, hα, -, -, -, -, he, -, hp⟩
        · exact Or.inr ⟨by omega, Or.inl (by omega)⟩
        · have := hphi hl hs0
          have h1 : 1 ≤ (if j = 0 then 1 else 3) := by split_ifs <;> omega
          exact Or.inr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
        · have := hphi hl hs0
          rw [if_neg (isNewA_pos hα)] at this
          exact Or.inr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
      · have hg1 : g.mfl = 1 := Graph.mfl_of_not_sepInt hsep
        exact Or.inl (by omega)
  · intro u hl hex
    subst hl
    exact k5 u (hS.label_some hL (fun c hc => (hNo c hc).2)) hex

end SchStep

/-! ## Terms of local operations with the data of the step -/

section TermOK

variable {k n : ℕ}

/-- The first atom of a component, or for `sw = true` the second atom of a solid edge. -/
def kAt {V : Type*} : Bool → Comp V → V
  | false, c => c.x
  | true, c => if c.kind.isSolid then c.y else c.x

/-- `TermOK` for the graph with its solid edges reversed when `sw = true`: the random new
components have their atom `kAt sw` internal. -/
def TermOKS (sw : Bool) (Γ : Graph k n) (x : Atom k n) (T : Tracked k n) : Prop :=
  ∃ (j : ℕ) (R : List (Comp (Atom k n))) (N : List (Comp (Atom k (n + j))))
    (lab : Option (Atom k (n + j))) (g : Graph k (n + j)) (s : ℕ),
    T = ⟨n + j, g, liftA j⟩ ∧ Sch Γ j R N lab g ∧ (∀ c ∈ N, NewOK c ∧ c.label = none) ∧
    (∀ c ∈ N, c.kind.isRandom = true → (kAt sw c).isRight = true) ∧
    ordL N = ordL R + 2 * j + s ∧
    (∀ i : Fin j, (N.filter fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2) ∧
    (N.filter fun c => c.kind.isSolid && !g.hasXdot c.x c.y && !isNewA n c.x &&
      !isNewA n c.y).length ≤ s ∧
    (N.filter fun c => c.kind.isSolid).length ≤ 4 ∧
    (s = 0 → (N.filter fun c => c.kind.isSolid).length ≤ 2) ∧
    (N.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length ≤
      (R.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length ∧
    (lab = none → s = 0 → g.phi + (if j = 0 then 1 else 3) ≤ Γ.phi) ∧
    (lab ≠ none → ∃ c ∈ g.comps, c.kind.isRandom = true) ∧
    (∀ i : Fin j, g.SameMol (liftA j x) (newA i))

/-- A term of a local operation at `x` before `O_dot`, with the data of the step: the
schema, the new components, the order surplus `s`, the solid edges without `×`-dotted partner,
the solid edges at external atoms, the potential at equal order, a random component if
labelled, and the new atoms in the molecule of `x`. -/
abbrev TermOK (Γ : Graph k n) (x : Atom k n) (T : Tracked k n) : Prop := TermOKS false Γ x T

/-- The clauses of an output `t` of one step at a graph `Γ`. -/
def StepOut (Γ : Graph k n) (t : Tracked k n) : Prop :=
  Γ.dotExcess ≤ t.g.dotExcess ∧ Γ.obl ≤ t.g.obl ∧
  (t.g.LabelFree → t.g.obl = Γ.obl → LexLt t.g Γ) ∧
  t.g.XdotApart ∧ t.g.RandomFirstInt ∧ t.g.Plain ∧ (t.g.LabelFree ∨ t.g.IsQGraph) ∧
  (∀ u v, Γ.SameMol u v → t.g.SameMol (t.f u) (t.f v)) ∧ (∀ u', ∃ u, t.g.SameMol u' (t.f u))

private theorem not_labelFree_of_qGraph {g : Graph k n} (h : g.IsQGraph) : ¬ g.LabelFree := by
  rintro hL
  obtain ⟨u, ⟨c, hc, hl⟩, -⟩ := h
  rw [hL c hc] at hl
  cases hl

/-- The step at a term: `O_dot` after a term with `TermOK`. -/
theorem TermOK.step {C : ℕ} {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (hT : TermOK Γ x T) (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree)
    (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart) {t : Tracked k T.nOut} (ht : t ∈ oDotT T.g) :
    StepOut Γ ⟨t.nOut, t.g, t.f ∘ T.f⟩ := by
  obtain ⟨j, R, N, lab, g, s, rfl, hS, hNo, hNK, hs, two, old, four, zero, hext, hphi, hlab,
    hatt⟩ := hT
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
    hS.step hN hP hL hK hX hNo hNK hs two old four zero hext hphi ht
  have hLQ : t.g.LabelFree ∨ t.g.IsQGraph := by
    cases lab with
    | none => exact Or.inl (a7 rfl)
    | some u => exact Or.inr (a8 u rfl (hlab (by simp)))
  refine ⟨a1, a2, fun hl he => ?_, a4, a5, a6, hLQ, a9, ?_⟩
  · cases lab with
    | none => exact a3 rfl he
    | some u => exact absurd hl (not_labelFree_of_qGraph (a8 u rfl (hlab (by simp))))
  · intro u'
    obtain ⟨w, hw⟩ := a10 u'
    rcases isNewA_cases (n := n) (j := j) w with ⟨-, v, rfl⟩ | ⟨-, i, rfl⟩
    · exact ⟨v, hw⟩
    · refine ⟨x, (Graph.sameMol_equivalence _).trans hw ?_⟩
      have := (oDotT_keep (hS.dotIn hN hP hL hX hNo) ht).2.2.2.2.2.1 _ _ (hatt i)
      exact (Graph.sameMol_equivalence _).symm this

end TermOK

/-! ## The terms of the edge expansions -/

section IdxLemmas

variable {α : Type*}

private theorem pickIdxs_eq (is : List ℕ) (l : List α) :
    pickIdxs is l = (l.zipIdx.filter fun p => is.contains p.2).map Prod.fst := rfl

private theorem eraseIdxs_eq (is : List ℕ) (l : List α) :
    eraseIdxs is l = (l.zipIdx.filter fun p => !is.contains p.2).map Prod.fst := rfl

private theorem eraseIdxs_pick_perm (is : List ℕ) (l : List α) :
    (eraseIdxs is l ++ pickIdxs is l).Perm l := by
  rw [eraseIdxs_eq, pickIdxs_eq]
  have h := List.filter_append_perm (fun p : α × ℕ => is.contains p.2) l.zipIdx
  have h2 := (h.map Prod.fst)
  rw [List.map_append, List.zipIdx_map_fst] at h2
  exact List.perm_append_comm.trans h2

private theorem mem_eraseIdxs_of_mem {is : List ℕ} {l : List α} {a : α} (h : a ∈ eraseIdxs is l) :
    a ∈ l := (eraseIdxs_pick_perm is l).subset (List.mem_append_left _ h)

private theorem zipIdx_nodup (l : List α) : l.zipIdx.Nodup := by
  have : (l.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' ..
  exact List.Nodup.of_map _ this

private theorem pickIdxs_perm (is : List ℕ) (hnd : is.Nodup) (l : List α) :
    (pickIdxs is l).Perm (is.filterMap fun i => l[i]?) := by
  classical
  rw [pickIdxs_eq]
  have key : (l.zipIdx.filter fun p => is.contains p.2).Perm
      (is.filterMap fun i => (l[i]?).map fun a => (a, i)) := by
    refine List.perm_of_nodup_nodup_toFinset_eq ?_ ?_ ?_
    · exact (zipIdx_nodup l).filter _
    · refine List.Nodup.filterMap ?_ hnd
      intro i i' p hp hp'
      simp only [Option.mem_def, Option.map_eq_some_iff] at hp hp'
      obtain ⟨a, -, rfl⟩ := hp
      obtain ⟨a', -, h⟩ := hp'
      exact (Prod.mk.inj h).2.symm
    · ext p
      simp only [List.mem_toFinset, List.mem_filter, List.mem_zipIdx_iff_getElem?,
        List.contains_iff_mem, List.mem_filterMap, Option.map_eq_some_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨p.2, h2, p.1, h1, rfl⟩
      · rintro ⟨i, hi, a, ha, rfl⟩
        exact ⟨ha, hi⟩
  have h2 := key.map Prod.fst
  rw [List.map_filterMap] at h2
  have h3 : (is.filterMap fun x => Option.map Prod.fst (Option.map (fun a => (a, x)) l[x]?)) =
      is.filterMap fun i => l[i]? := by
    apply List.filterMap_congr
    intro i _
    cases l[i]? <;> rfl
  rw [h3] at h2
  exact h2

end IdxLemmas

section EdgeIdx

variable {k n : ℕ}

private theorem mem_edgeIdx {Γ : Graph k n} {x : Atom k n} {ch : Charge} {out : Bool} {j : ℕ} :
    j ∈ Γ.edgeIdx x ch out ↔ ∃ c, Γ.comps[j]? = some c ∧ c.kind = .G ch ∧
      (if out = true then c.x = x ∧ c.y ≠ x else c.y = x ∧ c.x ≠ x) := by
  unfold Graph.edgeIdx
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?] at hp
    obtain ⟨hz, hf⟩ := hp
    refine ⟨p.1, hz, ?_⟩
    cases out <;> simp_all
  · rintro ⟨c, hc, hk, ho⟩
    refine ⟨(c, j), ?_, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?]
    refine ⟨hc, ?_⟩
    cases out <;> simp_all

private theorem edgeIdx_nodup (Γ : Graph k n) (x : Atom k n) (ch : Charge) (out : Bool) :
    (Γ.edgeIdx x ch out).Nodup := by
  unfold Graph.edgeIdx
  have : (Γ.comps.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' ..
  have h2 := (List.Nodup.sublist (List.filter_sublist (p := fun p : Comp (Atom k n) × ℕ =>
    p.1.kind == .G ch && (if out then p.1.x == x && p.1.y != x else p.1.y == x && p.1.x != x))
    (l := Γ.comps.zipIdx)) (zipIdx_nodup Γ.comps))
  refine List.Nodup.map_on ?_ h2
  intro p hp q hq h
  rw [List.mem_filter, List.mem_zipIdx_iff_getElem?] at hp hq
  have h1 := hp.1
  have h2' := hq.1
  rw [h] at h1
  rw [h1] at h2'
  exact Prod.ext (Option.some.inj h2') h

private theorem edgeIdx_disjoint {Γ : Graph k n} {x : Atom k n} {ch ch' : Charge} {out out' : Bool}
    (h : ch ≠ ch' ∨ out ≠ out') {j : ℕ} (h1 : j ∈ Γ.edgeIdx x ch out)
    (h2 : j ∈ Γ.edgeIdx x ch' out') : False := by
  rw [mem_edgeIdx] at h1 h2
  obtain ⟨c, hc, hk, ho⟩ := h1
  obtain ⟨c', hc', hk', ho'⟩ := h2
  rw [hc] at hc'
  obtain rfl := Option.some.inj hc'
  rw [hk] at hk'
  have hch : ch = ch' := by injection hk'
  subst hch
  rcases h with h | h
  · exact h rfl
  · cases out <;> cases out' <;> simp_all

end EdgeIdx


end RBM8D.Graphs
