import RBM8D.Graph.QExp.Step1
import RBM8D.Graph.Local.DotNorm

/-!
# The first step of the `Q`-expansions with deterministic choices

[II, Lemma 4.11], with [II, (4.17)–(4.21)], for a function of the graph: `selStep1 d x Γ` makes
every choice of [II, §4.4, Step 1] at the first index, in the printed order (the splits of the
atoms of `Γ₀` against `x`, [II, (4.17)] on every factor of `Γ₀` one by one, the factors with
minor `{x}` moved into the label group, [II, (4.20)], [II, (4.21)], the removal of the
`×`-dotted edges without solid edge, `O_merge`). Every step is a term of an operator of
`QElemStep`. The Taylor degree `d` of [II, (4.21)] is the only numeric parameter, and
`selDeg D Γ` is the degree used at error order `D`.

The main statements are `selStep1_clauses` (the clauses `qStep1Out D` of every output graph for
every error order `D ≤ ord Γ + d`, the components at the external atoms, and the strict rise of
the paper scaling order of the outputs that are not `Q`-forms), the
steps of the phases (`selStep1_split_step`, `selStep1_schur_step`, `selStep1_rev_step`,
`selStep1_taylor_step`, `selStep1_clean_step`), and the bounds on `selDeg`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Auxiliary facts on dotted components, `O_merge` and the invariants of the construction -/

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

section Dots

variable {k n : ℕ}

private theorem s1c_dg_adj {L : List (Comp (Atom k n))} {a b : Atom k n} :
    (step1_dg L).Adj a b ↔ a ≠ b ∧ ∃ c ∈ L, c.kind = .dot ∧ (c.x = a ∧ c.y = b ∨ c.x = b ∧ c.y = a) := by
  simp only [step1_dg, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact ⟨h, c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨h, c, hc, hk, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨h, c, hc, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact ⟨h, Or.inr ⟨c, hc, hk, rfl, rfl⟩⟩

/-- The ends of a dotted component are reachable. -/
private theorem s1c_dg_reach_of_mem {L : List (Comp (Atom k n))} {c : Comp (Atom k n)} (hc : c ∈ L)
    (hk : c.kind = .dot) : (step1_dg L).Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (s1c_dg_adj.2 ⟨h, c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩).reachable

/-- Reachability in the graph of dotted components is monotone in the dotted components. -/
private theorem dg_reach_mono {L L' : List (Comp (Atom k n))}
    (h : ∀ c ∈ L, c.kind = .dot → c ∈ L') {a b : Atom k n} (hr : (step1_dg L).Reachable a b) :
    (step1_dg L').Reachable a b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨hne, c, hc, hk, hxy⟩ := s1c_dg_adj.1 hadj
    refine SimpleGraph.Reachable.trans ?_ ih
    exact (s1c_dg_adj.2 ⟨hne, c, h c hc hk, hk, hxy⟩).reachable

/-- The graph of dotted components depends only on the dotted components. -/
private theorem dg_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ c, c.kind = .dot → (c ∈ L ↔ c ∈ L')) : step1_dg L = step1_dg L' := by
  ext a b
  rw [s1c_dg_adj, s1c_dg_adj]
  constructor
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).1 hc, hk, hxy⟩
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).2 hc, hk, hxy⟩

private theorem dg_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step1_dg L = step1_dg L' :=
  dg_congr fun _ _ => h.mem_iff

private theorem s1c_nD_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step1_nD L = step1_nD L' :=
  (h.filter _).length_eq

private theorem eL_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step1_eL L = step1_eL L' := by
  simp only [step1_eL, s1c_nD_perm h, dg_perm h]

/-- Two lists with the same dotted components, with multiplicity, have the same graph of dotted
components and the same dot excess. -/
private theorem dg_eL_of_filter_perm {L L' : List (Comp (Atom k n))}
    (h : (L.filter fun c => decide (c.kind = .dot)).Perm
      (L'.filter fun c => decide (c.kind = .dot))) :
    step1_dg L = step1_dg L' ∧ step1_eL L = step1_eL L' := by
  have hg : step1_dg L = step1_dg L' := by
    apply dg_congr
    intro c hk
    have := h.mem_iff (a := c)
    simp only [List.mem_filter, hk, decide_true, and_true] at this
    exact this
  refine ⟨hg, ?_⟩
  simp only [step1_eL, step1_nD, h.length_eq, hg]

private theorem dg_nil : step1_dg ([] : List (Comp (Atom k n))) = ⊥ := by
  ext a b
  simp [s1c_dg_adj]

private theorem dg_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : step1_dg (c :: L) = step1_dg L := by
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
    (step1_dg (c :: L)).Adj a b ↔ (step1_dg L).Adj a b ∨ (a ≠ b ∧ (a = c.x ∧ b = c.y ∨ a = c.y ∧ b = c.x)) := by
  rw [s1c_dg_adj, s1c_dg_adj]
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

private theorem s1c_nD_cons (c : Comp (Atom k n)) (L : List (Comp (Atom k n))) :
    step1_nD (c :: L) = step1_nD L + if c.kind = .dot then 1 else 0 := by
  unfold step1_nD
  by_cases h : c.kind = .dot
  · rw [List.filter_cons_of_pos (by simp [h])]
    simp [h]
  · rw [List.filter_cons_of_neg (by simp [h])]
    simp [h]

private theorem eL_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : step1_eL (c :: L) = step1_eL L := by
  simp [step1_eL, s1c_nD_cons, hk, dg_cons_nondot L hk]

/-- A dotted component between two blocks keeps the dot excess. -/
private theorem eL_cons_dot_new {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : ¬ (step1_dg L).Reachable c.x c.y) : step1_eL (c :: L) = step1_eL L := by
  have h := card_cc_add_edge (G := step1_dg L) (H := step1_dg (c :: L)) (dg_cons_dot_adj L hk) hr
  simp only [step1_eL, s1c_nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- Reachability is unchanged by a dotted component whose ends are reachable. -/
private theorem dg_reach_cons_red {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : (step1_dg L).Reachable c.x c.y) (a b : Atom k n) :
    (step1_dg (c :: L)).Reachable a b ↔ (step1_dg L).Reachable a b := by
  rw [reach_add_edge_iff (dg_cons_dot_adj L hk)]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h
    · exact (h1.trans hr).trans h2
    · exact (h1.trans hr.symm).trans h2
  · exact Or.inl

/-- A dotted component whose ends are already in one block raises the dot excess by `1`. -/
private theorem eL_cons_dot_red {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : (step1_dg L).Reachable c.x c.y) : step1_eL (c :: L) = step1_eL L + 1 := by
  have h := card_cc_of_reach_iff (G := step1_dg L) (H := step1_dg (c :: L)) (dg_reach_cons_red L hk hr)
  simp only [step1_eL, s1c_nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- Every dotted component is needed: its ends are not joined by the other dotted components. -/
private def s1c_NonRed (L : List (Comp (Atom k n))) : Prop :=
  ∀ (c : Comp (Atom k n)) (L' : List (Comp (Atom k n))), L.Perm (c :: L') → c.kind = .dot →
    ¬ (step1_dg L').Reachable c.x c.y

private theorem nonRed_tail {c : Comp (Atom k n)} {L : List (Comp (Atom k n))}
    (h : s1c_NonRed (c :: L)) : s1c_NonRed L := by
  intro d L' hp hk hr
  apply h d (c :: L') ((hp.cons c).trans (List.Perm.swap d c L')) hk
  exact dg_reach_mono (fun e he _ => List.mem_cons_of_mem _ he) hr

private theorem card_atom : Nat.card (Atom k n) = k + n := by
  simp

/-- When every dotted component is needed, the dot excess is `0`. -/
private theorem s1c_eL_eq_zero_of_nonRed : ∀ {L : List (Comp (Atom k n))}, s1c_NonRed L → step1_eL L = 0
  | [], _ => by
    simp only [step1_eL, step1_nD, List.filter_nil, List.length_nil, dg_nil, card_cc_bot, card_atom]
    push_cast
    ring
  | c :: L, h => by
    have ih := s1c_eL_eq_zero_of_nonRed (nonRed_tail h)
    by_cases hk : c.kind = .dot
    · rw [eL_cons_dot_new L hk (h c L (List.Perm.refl _) hk), ih]
    · rw [eL_cons_nondot L hk, ih]

/-- A list with positive dot excess has a dotted component whose ends are joined by the others. -/
private theorem s1c_exists_red_of_pos {L : List (Comp (Atom k n))} (h : 0 < step1_eL L) :
    ∃ (i : ℕ) (c : Comp (Atom k n)), L[i]? = some c ∧ c.kind = .dot ∧
      (step1_dg (L.eraseIdx i)).Reachable c.x c.y := by
  by_contra hc
  push Not at hc
  have hn : s1c_NonRed L := by
    intro c L' hp hk hr
    have hcL : c ∈ L := hp.symm.subset (List.mem_cons_self ..)
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.1 hcL
    have hp' : (L.eraseIdx i).Perm L' := by
      have h1 := List.getElem_cons_eraseIdx_perm hi
      rw [hci] at h1
      exact (h1.trans hp).cons_inv
    exact hc i c (by rw [List.getElem?_eq_getElem hi, hci]) hk (by rw [dg_perm hp']; exact hr)
  have := s1c_eL_eq_zero_of_nonRed hn
  omega

/-- The dot excess is never negative. -/
private theorem s1c_eL_nonneg : ∀ (L : List (Comp (Atom k n))), 0 ≤ step1_eL L := by
  intro L
  induction h : L.length generalizing L with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 h
    simp only [step1_eL, step1_nD, List.filter_nil, List.length_nil, dg_nil, card_cc_bot, card_atom]
    push_cast
    ring_nf
    rfl
  | succ m ih =>
    by_cases hn : s1c_NonRed L
    · rw [s1c_eL_eq_zero_of_nonRed hn]
    · simp only [s1c_NonRed, not_forall, not_not] at hn
      obtain ⟨c, L', hp, hk, hr⟩ := hn
      have h1 : step1_eL L = step1_eL L' + 1 := by rw [eL_perm hp, eL_cons_dot_red _ hk hr]
      have h2 := ih L' (by have := hp.length_eq; simp at this; omega)
      omega

/-- A labelling that agrees on the ends of every dotted component agrees along paths of dotted
components. -/
private theorem sigma_eq_of_reach {ι : Type*} {L : List (Comp (Atom k n))} (σ : Atom k n → ι)
    (hz : ∀ c ∈ L, c.kind = .dot → σ c.x = σ c.y) {a b : Atom k n}
    (hr : (step1_dg L).Reachable a b) : σ a = σ b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := s1c_dg_adj.1 hadj
    · exact (hz c hc hk).trans ih
    · exact (hz c hc hk).symm.trans ih

end Dots

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

private theorem Graph.mrep_dot (Γ : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : Γ.step1_mrep c.x = Γ.step1_mrep c.y := by
  obtain ⟨B, hB, hx, hy⟩ := dotBlocks_joined (allAtoms k n) Γ.comps
    (fun c _ => ⟨mem_allAtoms _, mem_allAtoms _⟩) c hc hk
  have hnd : (dotBlocks (allAtoms k n) Γ.comps).flatten.Nodup :=
    (dotBlocks_flatten_perm _ _).nodup_iff.2 allAtoms_nodup
  exact blockRep_eq_of_mem hnd hB hx hy

private theorem Graph.mrep_conn (Γ : Graph k n) (u : Atom k n) :
    Relation.EqvGen (dotRel Γ.comps) u (Γ.step1_mrep u) := by
  rcases blockRep_spec (dotBlocks (allAtoms k n) Γ.comps) u with h | ⟨B, hB, hu, hr⟩
  · have : Γ.step1_mrep u = u := h
    rw [this]
    exact Relation.EqvGen.refl _
  · exact dotBlocks_conn _ _ B hB u hu _ hr

/-- The roots: the representatives of the internal atoms, without repetition. -/
private def Graph.mroots (Γ : Graph k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => Γ.step1_mrep (Sum.inr i)).dedup

private theorem Graph.mem_mroots (Γ : Graph k n) (i : Fin n) : Γ.step1_mrep (.inr i) ∈ Γ.mroots :=
  List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

/-- The new internal atom of an internal atom: the position of its root. -/
private def Graph.midx (Γ : Graph k n) (i : Fin n) : Fin Γ.mroots.length :=
  ⟨Γ.mroots.idxOf (Γ.step1_mrep (.inr i)), List.idxOf_lt_length_of_mem (Γ.mem_mroots i)⟩

/-- The atom map of `O_merge`. -/
private def Graph.mmap (Γ : Graph k n) : Atom k n → Atom k Γ.mroots.length :=
  fun u => match u with
    | .inl a => .inl a
    | .inr i => .inr (Γ.midx i)

private theorem mergeT_eq (Γ : Graph k n) : Γ.mergeT =
    if Γ.comps.any (fun c => c.kind == .xdot && Γ.step1_mrep c.x == Γ.step1_mrep c.y) then none else
    some ⟨Γ.mroots.length, ⟨Γ.comps.filterMap (step1_mergeComp Γ.step1_mrep Γ.mmap), Γ.coeff⟩, Γ.mmap⟩ := rfl

private theorem mergeT_none {Γ : Graph k n} (h : Γ.mergeT = none) :
    ∃ c ∈ Γ.comps, c.kind = .xdot ∧ Γ.step1_mrep c.x = Γ.step1_mrep c.y := by
  rw [mergeT_eq] at h
  split_ifs at h with hc
  rw [List.any_eq_true] at hc
  obtain ⟨c, hc, hb⟩ := hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨c, hc, hb.1, hb.2⟩

private theorem s1c_mergeT_spec {Γ : Graph k n} {t : Tracked k n} (h : Γ.mergeT = some t) :
    Step1MergeSpec Γ t := by
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
      change Γ.mroots.idxOf (Γ.step1_mrep (.inr i)) = Γ.mroots.idxOf (Γ.step1_mrep (.inr j))
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
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : step1_mergeComp rep f c = some c') :
    c'.label = c.label.map (Prod.map id f) := by
  unfold step1_mergeComp at h
  split_ifs at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain rfl := Option.some.inj h
    rfl

private theorem mergeComp_none {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (h : step1_mergeComp rep f c = none) : c.kind = .dot ∧ f c.x = f c.y := by
  unfold step1_mergeComp at h
  split_ifs at h with h1
  simpa using h1

private theorem mergeComp_of_solid {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (hs : c.kind.isSolid = true)
    (h : rep c.x ≠ rep c.y) : step1_mergeComp rep f c = some (c.map f) := by
  unfold step1_mergeComp
  split_ifs with h1 h2
  · simp at h1
    cases hk : c.kind <;> simp_all [Kind.isSolid]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact absurd h2.2 h
  · rfl

private theorem s1c_mergeComp_kind {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : step1_mergeComp rep f c = some c') :
    c'.kind = c.kind ∨ ∃ ch, c.kind = .G ch ∧ c'.kind = .weight ch := by
  unfold step1_mergeComp at h
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

private theorem s1c_mergeComp_dot {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hk : c.kind = .dot) :
    step1_mergeComp rep f c = if f c.x = f c.y then none else some (c.map f) := by
  unfold step1_mergeComp
  by_cases h : f c.x = f c.y
  · simp [hk, h]
  · simp [hk, h, Kind.isSolid]

private theorem s1c_mergeComp_solid {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hs : c.kind.isSolid = true) :
    step1_mergeComp rep f c = if rep c.x = rep c.y then
      some { c.map f with kind := c.kind.toWeight, y := f c.x } else some (c.map f) := by
  have hnd : c.kind ≠ .dot := by
    intro h
    rw [h] at hs
    simp [Kind.isSolid] at hs
  unfold step1_mergeComp
  by_cases h : rep c.x = rep c.y
  · simp [hs, h, hnd]
  · simp [hs, h, hnd]

private theorem mergeComp_other {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hd : c.kind ≠ .dot) (hs : c.kind.isSolid = false) :
    step1_mergeComp rep f c = some (c.map f) := by
  unfold step1_mergeComp
  simp [hd, hs]

variable {Γ : Graph k n} {t : Tracked k n}

private theorem Step1MergeSpec.mem_comps (hs : Step1MergeSpec Γ t) {c' : Comp (Atom k t.nOut)} :
    c' ∈ t.g.comps ↔ ∃ c ∈ Γ.comps, step1_mergeComp Γ.step1_mrep t.f c = some c' := by
  rw [hs.comps_eq, List.mem_filterMap]

/-- A component that is neither a dotted edge nor a solid edge keeps its kind and is mapped. -/
private theorem Step1MergeSpec.mem_of_other (hs : Step1MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hd : c.kind ≠ .dot) (hsol : c.kind.isSolid = false) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, mergeComp_other hd hsol⟩

private theorem Step1MergeSpec.mem_of_solid (hs : Step1MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hsol : c.kind.isSolid = true) (hr : Γ.step1_mrep c.x ≠ Γ.step1_mrep c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [s1c_mergeComp_solid hsol, ite_eq_right hr]⟩

private theorem Step1MergeSpec.mem_of_dot (hs : Step1MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) (hf : t.f c.x ≠ t.f c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [s1c_mergeComp_dot hk, ite_eq_right hf]⟩

/-- A solid component of `t.g` is the image of a solid component of `Γ` whose ends are in
different blocks. -/
private theorem Step1MergeSpec.of_mem_solid (hs : Step1MergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind.isSolid = true) :
    ∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ Γ.step1_mrep c.x ≠ Γ.step1_mrep c.y ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases s1c_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind.isSolid = true := by rw [← h]; exact hk
    rw [s1c_mergeComp_solid hck] at hm
    split_ifs at hm with hr
    · exfalso
      obtain rfl := Option.some.inj hm
      obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
        cases hkk : c.kind <;> simp_all [Kind.isSolid]
      simp [Kind.toWeight, hch, Kind.isSolid] at hk
    · exact ⟨c, hc, hck, hr, (Option.some.inj hm).symm⟩
  · rw [hch'] at hk
    simp [Kind.isSolid] at hk

private theorem Step1MergeSpec.dot_reach (hs : Step1MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) :
    t.g.edgeGraphNoX.Reachable (t.f c.x) (t.f c.y) := by
  by_cases hf : t.f c.x = t.f c.y
  · rw [hf]
  · refine SimpleGraph.Adj.reachable ?_
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj]
    exact ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_dot hc hk hf, by simp [Comp.map, hk], rfl, rfl⟩⟩

private theorem Step1MergeSpec.eqv_reach (hs : Step1MergeSpec Γ t) {u v : Atom k n}
    (h : Relation.EqvGen (dotRel Γ.comps) u v) :
    t.g.edgeGraphNoX.Reachable (t.f u) (t.f v) := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact hs.dot_reach hc hk
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private theorem Step1MergeSpec.noX_reach (hs : Step1MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind ≠ .xdot) :
    t.g.edgeGraphNoX.Reachable (t.f c.x) (t.f c.y) := by
  by_cases hd : c.kind = .dot
  · exact hs.dot_reach hc hd
  by_cases hsol : c.kind.isSolid = true
  · by_cases hr : Γ.step1_mrep c.x = Γ.step1_mrep c.y
    · have hconn : Relation.EqvGen (dotRel Γ.comps) c.x c.y :=
        (Γ.mrep_conn c.x).trans _ _ _ (hr ▸ (Γ.mrep_conn c.y).symm)
      exact hs.eqv_reach hconn
    · by_cases hf : t.f c.x = t.f c.y
      · rw [hf]
      refine SimpleGraph.Adj.reachable ?_
      rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj]
      refine ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_solid hc hsol hr, ?_, rfl, rfl⟩⟩
      simpa [Comp.map] using hk
  · have hsol' : c.kind.isSolid = false := by simpa using hsol
    by_cases hf : t.f c.x = t.f c.y
    · rw [hf]
    refine SimpleGraph.Adj.reachable ?_
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj]
    refine ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_other hc hd hsol', ?_, rfl, rfl⟩⟩
    simpa [Comp.map] using hk

private theorem Step1MergeSpec.connNoX (hs : Step1MergeSpec Γ t) (hconn : Γ.ConnNoX) : t.g.ConnNoX := by
  have hadj : ∀ u v, Γ.edgeGraphNoX.Adj u v →
      t.g.edgeGraphNoX.Reachable (t.f u) (t.f v) := by
    intro u v h
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at h
    obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := h
    · exact hs.noX_reach hc hk
    · exact (hs.noX_reach hc hk).symm
  intro u' v'
  obtain ⟨u, rfl⟩ := hs.f_surj u'
  obtain ⟨v, rfl⟩ := hs.f_surj v'
  have h := hconn u v
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ h2 ih => exact ih.trans (hadj _ _ h2)

private theorem Step1MergeSpec.wt_reach (hs : Step1MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps)
    (hk : c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) :
    t.g.wavedThetaGraph.Reachable (t.f c.x) (t.f c.y) := by
  have hd : c.kind ≠ .dot := by
    rcases hk with ⟨-, h⟩ | h
    · exact h
    · intro hd
      rw [hd] at h
      simp [Kind.isDiffusive] at h
  have hsol : c.kind.isSolid = false := by
    rcases hk with ⟨h, -⟩ | h
    · cases hkk : c.kind <;> simp_all [Kind.joinsMol, Kind.isSolid]
    · cases hkk : c.kind <;> simp_all [Kind.isDiffusive, Kind.isSolid]
  by_cases hf : t.f c.x = t.f c.y
  · rw [hf]
  refine SimpleGraph.Adj.reachable ?_
  rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj]
  exact ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_other hc hd hsol, by simpa [Comp.map] using hk, rfl, rfl⟩⟩

private theorem Step1MergeSpec.internal (hs : Step1MergeSpec Γ t)
    (hint : ∀ a b : Fin n, Γ.wavedThetaGraph.Reachable (Sum.inr a) (Sum.inr b)) :
    ∀ a b : Fin t.nOut, t.g.wavedThetaGraph.Reachable (Sum.inr a) (Sum.inr b) := by
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have hadj : ∀ u v, Γ.wavedThetaGraph.Adj u v →
      t.g.wavedThetaGraph.Reachable (t.f u) (t.f v) := by
    intro u v h
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at h
    obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := h
    · exact hs.wt_reach hc hk
    · exact (hs.wt_reach hc hk).symm
  intro a b
  obtain ⟨i, rfl⟩ := hgs a
  obtain ⟨j, rfl⟩ := hgs b
  have key : ∀ y, Relation.ReflTransGen Γ.wavedThetaGraph.Adj (Sum.inr i) y →
      t.g.wavedThetaGraph.Reachable (t.f (.inr i)) (t.f y) := by
    intro y hy
    induction hy with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ h2 ih => exact ih.trans (hadj _ _ h2)
  have h := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (hint i j)
  have h2 := key _ h
  rwa [hg, hg] at h2

/-- Dotted edges of `t.g` have an external end. -/
private theorem Step1MergeSpec.noIntDot (hs : Step1MergeSpec Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind = .dot → c'.x.isLeft = true ∨ c'.y.isLeft = true := by
  intro c' hc' hk'
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases s1c_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .dot := h ▸ hk'
    rw [s1c_mergeComp_dot hck] at hm
    split_ifs at hm with hf
    obtain rfl := Option.some.inj hm
    by_contra hcon
    simp only [not_or, Bool.not_eq_true, Comp.map] at hcon
    obtain ⟨hx, hy⟩ := hcon
    apply hf
    have hx' : c.x.isRight = true := by
      rcases hcx : c.x with a | i
      · rw [hcx] at hx
        simp [hs.f_inl] at hx
      · rfl
    have hy' : c.y.isRight = true := by
      rcases hcy : c.y with a | i
      · rw [hcy] at hy
        simp [hs.f_inl] at hy
      · rfl
    exact hs.f_eq _ _ (Γ.mrep_dot hc hck) hx' hy'
  · rw [hch'] at hk'
    cases hk'

private theorem Step1MergeSpec.solid_ne (hs : Step1MergeSpec Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind.isSolid = true → c'.x ≠ c'.y := by
  intro c' hc' hk'
  obtain ⟨c, hc, -, hr, rfl⟩ := hs.of_mem_solid hc' hk'
  exact hs.f_ne _ _ hr

end MergeFacts

section MergeBlocks

variable {k n : ℕ}

private theorem eqvGen_dotRel_reach {L : List (Comp (Atom k n))} {u v : Atom k n}
    (h : Relation.EqvGen (dotRel L) u v) : (step1_dg L).Reachable u v := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact s1c_dg_reach_of_mem hc hk
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two atoms have the same representative exactly when they lie in one block. -/
private theorem Graph.mrep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.step1_mrep u = Γ.step1_mrep v ↔ Γ.SameBlock u v := by
  constructor
  · intro h
    have h1 := eqvGen_dotRel_reach (Γ.mrep_conn u)
    have h2 := eqvGen_dotRel_reach (Γ.mrep_conn v)
    rw [h] at h1
    exact h1.trans h2.symm
  · intro h
    exact sigma_eq_of_reach Γ.step1_mrep (fun c hc hk => Γ.mrep_dot hc hk) h

variable {Γ : Graph k n} {t : Tracked k n}

private theorem Step1MergeSpec.sameBlock_of_f_eq (hs : Step1MergeSpec Γ t) {u v : Atom k n}
    (h : t.f u = t.f v) : Γ.SameBlock u v := by
  by_contra hb
  exact hs.f_ne u v (fun hr => hb ((Γ.mrep_eq_iff u v).1 hr)) h

/-- Two distinct atoms with the same image are internal. -/
private theorem Step1MergeSpec.isRight_of_f_eq (hs : Step1MergeSpec Γ t) {u v : Atom k n}
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

private theorem Step1MergeSpec.dot_of_mem (hs : Step1MergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind = .dot) :
    ∃ c ∈ Γ.comps, c.kind = .dot ∧ t.f c.x ≠ t.f c.y ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases s1c_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .dot := h ▸ hk
    rw [s1c_mergeComp_dot hck] at hm
    split_ifs at hm with hf
    exact ⟨c, hc, hck, hf, (Option.some.inj hm).symm⟩
  · rw [hch'] at hk
    cases hk

/-- Blocks are mapped into blocks. -/
private theorem Step1MergeSpec.sameBlock_map (hs : Step1MergeSpec Γ t) {u v : Atom k n}
    (h : Γ.SameBlock u v) : t.g.SameBlock (t.f u) (t.f v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, hxy⟩ := s1c_dg_adj.1 hadj
    refine SimpleGraph.Reachable.trans ?_ ih
    have : t.g.SameBlock (t.f c.x) (t.f c.y) := by
      by_cases hf : t.f c.x = t.f c.y
      · exact hf ▸ SimpleGraph.Reachable.refl _
      · exact s1c_dg_reach_of_mem (hs.mem_of_dot hc hk hf) (by simp [Comp.map, hk])
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · exact this.symm

/-- Atoms whose images lie in one block lie in one block. -/
private theorem Step1MergeSpec.sameBlock_of_map (hs : Step1MergeSpec Γ t) {u v : Atom k n}
    (h : t.g.SameBlock (t.f u) (t.f v)) : Γ.SameBlock u v := by
  have key : ∀ a b, (step1_dg t.g.comps).Reachable a b → ∀ u v, t.f u = a → t.f v = b →
      Γ.SameBlock u v := by
    intro a b hr
    obtain ⟨w⟩ := hr
    induction w with
    | nil => intro u v hu hv; exact hs.sameBlock_of_f_eq (hu.trans hv.symm)
    | @cons a a' b hadj _ ih =>
      intro u v hu hv
      obtain ⟨-, c', hc', hk', hxy⟩ := s1c_dg_adj.1 hadj
      obtain ⟨c, hc, hk, -, rfl⟩ := hs.dot_of_mem hc' hk'
      have hcc : Γ.SameBlock c.x c.y := s1c_dg_reach_of_mem hc hk
      simp only [Comp.map] at hxy
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (hs.sameBlock_of_f_eq (hu.trans h1.symm)).trans (hcc.trans (ih c.y v h2 hv))
      · exact (hs.sameBlock_of_f_eq (hu.trans h2.symm)).trans
          (hcc.symm.trans (ih c.x v h1 hv))
  exact key _ _ h u v rfl rfl

private theorem Step1MergeSpec.sameBlock_iff (hs : Step1MergeSpec Γ t) (u v : Atom k n) :
    t.g.SameBlock (t.f u) (t.f v) ↔ Γ.SameBlock u v :=
  ⟨hs.sameBlock_of_map, hs.sameBlock_map⟩

/-- `O_merge` keeps the number of blocks. -/
private theorem Step1MergeSpec.card_cc (hs : Step1MergeSpec Γ t) :
    Nat.card (step1_dg Γ.comps).ConnectedComponent = Nat.card (step1_dg t.g.comps).ConnectedComponent :=
  card_cc_of_map t.f hs.f_surj hs.sameBlock_iff

/-- The dotted components removed by `O_merge`. -/
private def removedDots (Γ : Graph k n) (f : Atom k n → Atom k m) : List (Comp (Atom k n)) :=
  Γ.comps.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)

private theorem s1c_nD_filterMap_mergeComp {m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) :
    ∀ L : List (Comp (Atom k n)), step1_nD (L.filterMap (step1_mergeComp rep f)) +
      (L.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)).length = step1_nD L
  | [] => rfl
  | c :: L => by
    have ih := s1c_nD_filterMap_mergeComp rep f L
    rcases hm : step1_mergeComp rep f c with _ | c'
    · obtain ⟨hk, hf⟩ := mergeComp_none hm
      rw [List.filterMap_cons_none hm, List.filter_cons_of_pos (by simp [hk, hf]), s1c_nD_cons]
      simp only [hk, ite_true, List.length_cons]
      omega
    · have hnd : ¬ (c.kind = .dot ∧ f c.x = f c.y) := by
        rintro ⟨hk, hf⟩
        rw [s1c_mergeComp_dot hk] at hm
        simp [hf] at hm
      have hkk : (c'.kind = .dot) ↔ (c.kind = .dot) := by
        rcases s1c_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
        · rw [h]
        · rw [hch, hch']
          simp
      rw [List.filterMap_cons_some hm, List.filter_cons_of_neg (by simpa using hnd), s1c_nD_cons,
        s1c_nD_cons]
      by_cases hk : c.kind = .dot
      · simp only [hkk.2 hk, hk, ite_true]
        omega
      · simp only [show ¬ c'.kind = .dot from fun h => hk (hkk.1 h), hk, ite_false]
        omega

private theorem ordSum_filterMap_mergeComp {m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) :
    ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, c.kind.isSolid = true → rep c.x ≠ rep c.y) →
      ((L.filterMap (step1_mergeComp rep f)).map fun c => c.kind.ord).sum +
        2 * ((L.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)).length : ℤ) =
      (L.map fun c => c.kind.ord).sum
  | [], _ => by simp
  | c :: L, hsol => by
    have ih := ordSum_filterMap_mergeComp rep f L fun d hd => hsol d (List.mem_cons_of_mem _ hd)
    rcases hm : step1_mergeComp rep f c with _ | c'
    · obtain ⟨hk, hf⟩ := mergeComp_none hm
      rw [List.filterMap_cons_none hm, List.filter_cons_of_pos (by simp [hk, hf])]
      simp only [List.length_cons, List.map_cons, List.sum_cons, hk]
      have h2 : Kind.dot.ord = 2 := rfl
      push_cast
      linarith
    · have hnd : ¬ (c.kind = .dot ∧ f c.x = f c.y) := by
        rintro ⟨hk, hf⟩
        rw [s1c_mergeComp_dot hk] at hm
        simp [hf] at hm
      have hkk : c'.kind = c.kind := by
        rcases s1c_mergeComp_kind hm with h | ⟨ch, hch, -⟩
        · exact h
        · have hs : c.kind.isSolid = true := by rw [hch]; rfl
          rw [mergeComp_of_solid hs (hsol c (List.mem_cons_self ..) hs)] at hm
          rw [← Option.some.inj hm]
          rfl
      rw [List.filterMap_cons_some hm, List.filter_cons_of_neg (by simpa using hnd)]
      simp only [List.map_cons, List.sum_cons, hkk]
      linarith

/-- The scaling order and the dot excess after `O_merge`, when no solid edge lies in a block:
the removed dotted components lower both, the identified internal atoms raise both. -/
private theorem Step1MergeSpec.ord_eL (hs : Step1MergeSpec Γ t)
    (hsol : ∀ c ∈ Γ.comps, c.kind.isSolid = true → ¬ Γ.SameBlock c.x c.y) :
    t.g.ord = Γ.ord - 2 * ((removedDots Γ t.f).length : ℤ) + 2 * ((n : ℤ) - t.nOut) ∧
      step1_eL t.g.comps = step1_eL Γ.comps - ((removedDots Γ t.f).length : ℤ) + ((n : ℤ) - t.nOut) := by
  have hsol' : ∀ c ∈ Γ.comps, c.kind.isSolid = true → Γ.step1_mrep c.x ≠ Γ.step1_mrep c.y :=
    fun c hc hk hr => hsol c hc hk ((Γ.mrep_eq_iff _ _).1 hr)
  have h1 := ordSum_filterMap_mergeComp Γ.step1_mrep t.f Γ.comps hsol'
  have h2 := s1c_nD_filterMap_mergeComp Γ.step1_mrep t.f Γ.comps
  rw [← hs.comps_eq] at h1 h2
  refine ⟨?_, ?_⟩
  · simp only [Graph.ord, removedDots]
    linarith
  · simp only [step1_eL, removedDots, hs.card_cc]
    push_cast
    omega

/-- If the dotted components between internal atoms are needed and there is no dotted loop, the
removed dotted components are at most the identified internal atoms. -/
private theorem Step1MergeSpec.removedDots_le (hs : Step1MergeSpec Γ t) (hnr : NonRedInt Γ.comps)
    (hloop : ∀ c ∈ Γ.comps, c.kind = .dot → c.x ≠ c.y) :
    ((removedDots Γ t.f).length : ℤ) ≤ (n : ℤ) - t.nOut := by
  set H := removedDots Γ t.f with hH
  have hmemH : ∀ c ∈ H, c ∈ Γ.comps ∧ c.kind = .dot ∧ t.f c.x = t.f c.y := by
    intro c hc
    rw [hH, removedDots, List.mem_filter] at hc
    simpa using hc
  have hnr' : s1c_NonRed H := by
    intro c H' hp hk hr
    have hcH : c ∈ H := hp.symm.subset (List.mem_cons_self ..)
    obtain ⟨hcΓ, -, hf⟩ := hmemH c hcH
    obtain ⟨hx, hy⟩ := hs.isRight_of_f_eq hf (hloop c hcΓ hk)
    have hp' : Γ.comps.Perm (c :: (H' ++ Γ.comps.filter fun c =>
        !decide (c.kind = .dot ∧ t.f c.x = t.f c.y))) := by
      have h1 := (List.filter_append_perm (fun c => decide (c.kind = .dot ∧ t.f c.x = t.f c.y))
        Γ.comps).symm
      exact h1.trans ((hp.append_right _).trans (List.Perm.refl _))
    exact hnr c _ hp' hk hx hy (dg_reach_mono (fun e he _ => List.mem_append_left _ he) hr)
  have h0 := s1c_eL_eq_zero_of_nonRed hnr'
  have hnD : step1_nD H = H.length := by
    unfold step1_nD
    rw [List.filter_eq_self.2]
    intro c hc
    simp [(hmemH c hc).2.1]
  have hle := card_le_card_cc (G := step1_dg H) t.f hs.f_surj (by
    intro a b hr
    exact sigma_eq_of_reach t.f (fun c hc _ => (hmemH c hc).2.2) hr)
  rw [card_atom] at hle
  simp only [step1_eL, hnD] at h0
  push_cast at h0 hle
  omega

end MergeBlocks

section Tagged

variable {k n m : ℕ}

private theorem Kind.blueC_plus (κ : Kind) : κ.blueC .plus = κ.isBlue := by
  cases κ with
  | G c => cases c <;> rfl
  | _ => rfl

private theorem Graph.molReach_of_comp {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind.joinsMol = true) : Γ.molGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

private theorem Graph.netT_reach_of_sameMol (Γ : Graph k n) (L : List (TC k n)) (t : Bool)
    {a b : Fin n} (h : Γ.SameMol (Sum.inr a) (Sum.inr b)) : (Γ.netT L t).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl (Or.inl h)⟩ |>.reachable

private theorem Graph.netT_reach_of_mem (Γ : Graph k n) (L : List (TC k n)) (t : Bool)
    {p : TC k n} (hp : p ∈ L) (ht : p.2 = some t) {a b : Fin n} (hx : p.1.x = Sum.inr a)
    (hy : p.1.y = Sum.inr b) : (Γ.netT L t).Reachable a b := by
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
private theorem Graph.DCT.transport {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) (φ : Fin n → Fin m) {Γ' : Graph k m} (L' : List (TC k m))
    (hmap : L'.map Prod.fst = Γ'.comps)
    (hbl : ∀ p ∈ L', p.2 = some false → p.1.kind.isDiffusive = true)
    (hbu : ∀ p ∈ L', p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true)
    (hmol : ∀ c ∈ Γ.comps, c.kind.joinsMol = true →
      Γ'.molGraph.Reachable (Sum.map id φ c.x) (Sum.map id φ c.y))
    (hedge : ∀ t : Bool, ∀ p ∈ L, p.2 = some t → ∀ a b, p.1.x = Sum.inr a → p.1.y = Sum.inr b →
      (Γ'.netT L' t).Reachable (φ a) (φ b))
    (hcov : ∀ w : Fin m, ∃ a : Fin n, Γ'.SameMol (Sum.inr w) (Sum.inr (φ a))) : Γ'.DCT bc L' := by
  have key : ∀ t : Bool, (Γ.netT L t).Preconnected → (Γ'.netT L' t).Preconnected := by
    intro t hspan
    have hwalk : ∀ a b, (Γ.netT L t).Reachable a b → (Γ'.netT L' t).Reachable (φ a) (φ b) := by
      intro a b hr
      obtain ⟨w⟩ := hr
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a' b' c' hadj _ ih =>
        rw [Graph.netT, SimpleGraph.fromRel_adj] at hadj
        have hstep : (Γ'.netT L' t).Reachable (φ a') (φ b') := by
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

/-- A doubly connected structure with blue charge `plus` gives the doubly connected property. -/
private theorem Graph.DCT.doublyConnected {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT .plus L) : Γ.DoublyConnected := by
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
      (Graph.mk (L.map Prod.fst) co).net B = (Graph.mk (L.map Prod.fst) co).netT L t := by
    intro B t hB
    unfold Graph.net Graph.netT
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
    rw [Kind.blueC_plus] at this
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
private theorem Graph.Step1DCS.doublyConnected {Γ : Graph k n} (h : Γ.Step1DCS .plus) :
    Γ.DoublyConnected := by
  obtain ⟨L, hL⟩ := h
  exact hL.doublyConnected

/-- A tagged component of `L` has neither the kind `xdot` nor a weight kind if it is tagged
or joins molecules: its kind is diffusive, blue or joins molecules. -/
private theorem Graph.DCT.kind_of_tag {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {p : TC k n} (hp : p ∈ L) (ht : p.2 ≠ none) :
    p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true := by
  rcases hp2 : p.2 with _ | _ | _
  · exact absurd hp2 ht
  · exact Or.inl (h.black p hp hp2)
  · exact h.blue p hp hp2

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
private def mergeC (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

/-- The atom map of `O_merge` sends internal atoms onto internal atoms and fixes external ones,
atoms with the same representative have the same image, and the components are the images. -/
private theorem mergeT_struct {Γ : Graph k n} {t : Tracked k n} (ht : Γ.mergeT = some t) :
    ∃ (rep : Atom k n → Atom k n) (φ : Fin n → Fin t.nOut), t.f = Sum.map id φ ∧
      Function.Surjective φ ∧ (∀ i j, rep (Sum.inr i) = rep (Sum.inr j) → φ i = φ j) ∧
      t.g.comps = Γ.comps.filterMap (mergeC rep t.f) := by
  unfold Graph.mergeT at ht
  dsimp only at ht
  split_ifs at ht
  obtain rfl := Option.some.inj ht
  refine ⟨blockRep (dotBlocks (allAtoms k n) Γ.comps), fun i => ⟨_, List.idxOf_lt_length_of_mem
    (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩, ?_, ?_, ?_, rfl⟩
  · funext u
    rcases u with a | i <;> rfl
  · intro j
    have hj := List.getElem_mem j.2
    obtain ⟨i, -, hi⟩ := List.mem_map.1 (List.mem_dedup.1 hj)
    refine ⟨i, Fin.ext ?_⟩
    change List.idxOf _ _ = j.1
    rw [hi]
    exact (List.nodup_dedup _).idxOf_getElem j.1 j.2
  · intro i j hij
    refine Fin.ext ?_
    change List.idxOf _ _ = List.idxOf _ _
    rw [hij]

private theorem map_fst_filterMap {α β γ : Type*} (L : List (α × γ)) (F : α → Option β)
    (τ : α × γ → β → γ) :
    (L.filterMap fun p => (F p.1).map fun c' => (c', τ p c')).map Prod.fst =
      (L.map Prod.fst).filterMap F := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rcases hF : F p.1 with _ | c' <;> simp [hF, ih]

/-- `O_merge` keeps a doubly connected structure and sends internal atoms to internal atoms. -/
private theorem Graph.Step1DCS.mergeT {bc : Charge} {Γ : Graph k n} (h : Γ.Step1DCS bc)
    {t : Tracked k n} (ht : Γ.mergeT = some t) :
    t.g.Step1DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨rep, φ, hf, hsurj, hrep, hcomps⟩ := mergeT_struct ht
  have hint : ∀ u, (t.f u).isRight = u.isRight := by
    intro u
    rw [hf]
    rcases u with a | i <;> rfl
  refine ⟨?_, hint⟩
  let τ : TC k n → Comp (Atom k t.nOut) → Option Bool :=
    fun p c' => if c'.kind = p.1.kind then p.2 else none
  let L' : List (TC k t.nOut) :=
    L.filterMap fun p => (mergeC rep t.f p.1).map fun c' => (c', τ p c')
  have hmem : ∀ q ∈ L', ∃ p ∈ L, mergeC rep t.f p.1 = some q.1 ∧ q.2 = τ p q.1 := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := List.mem_filterMap.1 hq
    rcases hF : mergeC rep t.f p.1 with _ | c'
    · rw [hF] at hpq; simp at hpq
    · rw [hF] at hpq
      simp only [Option.map_some, Option.some.injEq] at hpq
      subst hpq
      exact ⟨p, hp, hF, rfl⟩
  refine ⟨L', ?_⟩
  refine hL.transport φ L' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcomps, ← hL.map_fst]
    exact map_fst_filterMap L (mergeC rep t.f) τ
  · intro q hq hqt
    obtain ⟨p, hp, -, hq2⟩ := hmem q hq
    have hk : q.1.kind = p.1.kind := by
      by_contra hne
      rw [hq2] at hqt
      simp [τ, hne] at hqt
    rw [hq2] at hqt
    simp only [τ, hk, ite_true] at hqt
    rw [hk]
    exact hL.black p hp hqt
  · intro q hq hqt
    obtain ⟨p, hp, -, hq2⟩ := hmem q hq
    have hk : q.1.kind = p.1.kind := by
      by_contra hne
      rw [hq2] at hqt
      simp [τ, hne] at hqt
    rw [hq2] at hqt
    simp only [τ, hk, ite_true] at hqt
    rw [hk]
    exact hL.blue p hp hqt
  · intro c hc hk
    rw [← hf]
    by_cases h1 : (c.kind == .dot && t.f c.x == t.f c.y) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1
      rw [h1.2]
    · have h2 : (c.kind.isSolid && rep c.x == rep c.y) = false := by
        have : c.kind.isSolid = false := by
          generalize c.kind = κ at hk
          cases κ <;> simp_all [Kind.joinsMol, Kind.isSolid]
        simp [this]
      have hc' : c.map t.f ∈ t.g.comps := by
        rw [hcomps]
        refine List.mem_filterMap.2 ⟨c, hc, ?_⟩
        simp [mergeC, h1, h2]
      exact Graph.molReach_of_comp hc' hk
  · intro t' p hp hpt a b hx hy
    have hkind : p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true :=
      hL.kind_of_tag hp (by rw [hpt]; simp)
    have hnd : p.1.kind ≠ .dot := by
      intro hd
      rw [hd] at hkind
      simp [Kind.isDiffusive, Kind.blueC] at hkind
    by_cases h2 : (p.1.kind.isSolid && rep p.1.x == rep p.1.y) = true
    · have hr : rep (Sum.inr a) = rep (Sum.inr b) := by
        simp only [Bool.and_eq_true, beq_iff_eq] at h2
        rw [hx, hy] at h2
        exact h2.2
      rw [hrep a b hr]
    · have hm : mergeC rep t.f p.1 = some (p.1.map t.f) := by
        simp [mergeC, hnd, h2]
      have hq : (p.1.map t.f, τ p (p.1.map t.f)) ∈ L' :=
        List.mem_filterMap.2 ⟨p, hp, by simp [hm]⟩
      have hτ : τ p (p.1.map t.f) = p.2 := by simp [τ, Comp.map]
      refine Graph.netT_reach_of_mem _ _ _ hq (hτ ▸ hpt) ?_ ?_
      · change t.f p.1.x = _
        rw [hx, hf]; rfl
      · change t.f p.1.y = _
        rw [hy, hf]; rfl
  · intro w
    obtain ⟨a, rfl⟩ := hsurj w
    exact ⟨a, Or.inl rfl⟩

end Tagged

section AbsorbVals

private theorem dedup_eq_singleton {α : Type*} [DecidableEq α] (l : List α) (a : α)
    (h1 : ∀ x ∈ l, x = a) (h2 : a ∈ l) : l.dedup = [a] := by
  have hnd := List.nodup_dedup l
  have hmem : ∀ x, x ∈ l.dedup ↔ x ∈ l := fun x => List.mem_dedup
  cases hd : l.dedup with
  | nil => exact absurd ((hmem a).2 h2) (by rw [hd]; simp)
  | cons x rest =>
    rw [hd] at hnd
    have hx : x = a := h1 x ((hmem x).1 (by rw [hd]; simp))
    have hrest : rest = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro y hy
      have hya : y = a := h1 y ((hmem y).1 (by rw [hd]; simp [hy]))
      exact (List.nodup_cons.1 hnd).1 (by rw [hx, ← hya]; exact hy)
    rw [hrest, hx]

/-- A graph whose labels are all `ℓ`, with at least one, has the single label `ℓ`. -/
private theorem labels_eq_single {k n : ℕ} (L : List (Comp (Atom k n))) (co : Coeff)
    (ℓ : PQ × Atom k n) (hl : ∀ c ∈ L, c.label = none ∨ c.label = some ℓ)
    (hex : ∃ c ∈ L, c.label = some ℓ) : (⟨L, co⟩ : Graph k n).labels = [ℓ] := by
  unfold Graph.labels
  apply dedup_eq_singleton
  · intro a ha
    obtain ⟨c, hc, hca⟩ := List.mem_filterMap.1 ha
    rcases hl c hc with h | h
    · rw [h] at hca; cases hca
    · rw [h] at hca; exact (Option.some.inj hca).symm
  · obtain ⟨c, hc, hcl⟩ := hex
    exact List.mem_filterMap.2 ⟨c, hc, hcl⟩

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

end AbsorbVals

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

private theorem length_filter_eraseIdx {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c)
    (p : α → Bool) :
    (L.filter p).length = ((L.eraseIdx i).filter p).length + if p c then 1 else 0 := by
  rw [((perm_eraseIdx hc).filter p).length_eq, List.filter_cons]
  split_ifs <;> simp

private theorem sum_map_eraseIdx {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c)
    (g : α → ℤ) : (L.map g).sum = ((L.eraseIdx i).map g).sum + g c := by
  rw [((perm_eraseIdx hc).map g).sum_eq]
  simp [add_comm]

end Replace2

section Inv

variable {k n : ℕ}

private theorem dotlab_of_wf {T : Graph k n} (hwf : ∀ c ∈ T.comps, c.WF) :
    ∀ c ∈ T.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
  intro c hc hk
  by_contra hl
  have := (hwf c hc).2 (by simpa [Option.isSome_iff_ne_none] using hl)
  rcases hk with hk | hk <;> rw [hk] at this <;> simp [Kind.isRandom] at this

end Inv

section ConnTransfer

variable {k n : ℕ}

private theorem edgeNoX_reach_of_comp {T : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ T.comps)
    (hk : c.kind ≠ .xdot) : T.edgeGraphNoX.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

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

private theorem wt_reach_of_comp {T : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ T.comps)
    (hk : c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) :
    T.wavedThetaGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

/-- The waved and `Θ` connectivity of the internal atoms passes to a graph on the same atoms
containing the waved and diffusive components. -/
private theorem internal_transfer {T T' : Graph k n}
    (h : ∀ a b : Fin n, T.wavedThetaGraph.Reachable (.inr a) (.inr b))
    (hr : ∀ c ∈ T.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) →
      c ∈ T'.comps) :
    ∀ a b : Fin n, T'.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
  have key : ∀ u v, T.wavedThetaGraph.Reachable u v → T'.wavedThetaGraph.Reachable u v := by
    intro u v huv
    obtain ⟨w⟩ := huv
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj _ ih =>
      rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := hadj
      · exact (wt_reach_of_comp (hr c hc hk) hk).trans ih
      · exact (wt_reach_of_comp (hr c hc hk) hk).symm.trans ih
  exact fun a b => key _ _ (h a b)

/-- A doubly connected structure passes to a graph on the same atoms. -/
private theorem Graph.DCT.same {bc : Charge} {T T' : Graph k n} {L : List (TC k n)}
    (h : T.DCT bc L) (L' : List (TC k n)) (hmap : L'.map Prod.fst = T'.comps)
    (hbl : ∀ p ∈ L', p.2 = some false → p.1.kind.isDiffusive = true)
    (hbu : ∀ p ∈ L', p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true)
    (hmol : ∀ c ∈ T.comps, c.kind.joinsMol = true → T'.molGraph.Reachable c.x c.y)
    (hedge : ∀ t : Bool, ∀ p ∈ L, p.2 = some t → ∀ a b, p.1.x = Sum.inr a →
      p.1.y = Sum.inr b → (T'.netT L' t).Reachable a b) : T'.DCT bc L' := by
  have hid : (Sum.map (id : Fin k → Fin k) (id : Fin n → Fin n)) = id := by
    funext u
    rcases u <;> rfl
  refine h.transport id L' hmap hbl hbu ?_ hedge (fun w => ⟨w, Or.inl rfl⟩)
  intro c hc hk
  rw [hid]
  exact hmol c hc hk

end ConnTransfer

section Final

variable {k n : ℕ}

private theorem Step1MergeSpec.hlab {Γ : Graph k n} {t : Tracked k n} (hs : Step1MergeSpec Γ t)
    (hlab : ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none) :
    ∀ c' ∈ t.g.comps, (c'.kind = .dot ∨ c'.kind = .xdot) → c'.label = none := by
  intro c' hc' hk'
  rw [hs.comps_eq, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hmc⟩ := hc'
  rw [mergeComp_label hmc]
  rcases s1c_mergeComp_kind hmc with h | ⟨ch, hch, hch'⟩
  · rw [hlab c hc (by rwa [h] at hk')]
    rfl
  · rw [hch'] at hk'
    rcases hk' with h | h <;> cases h

private theorem labels_length_le {T : Graph k n} {ℓ : PQ × Atom k n}
    (hl : ∀ c ∈ T.comps, c.label = none ∨ c.label = some ℓ) : T.labels.length ≤ 1 := by
  by_cases hex : ∃ c ∈ T.comps, c.label = some ℓ
  · obtain ⟨cs, co⟩ := T
    rw [labels_eq_single cs co ℓ hl hex]
    simp
  · push Not at hex
    have : T.labels = [] := by
      unfold Graph.labels
      rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
      intro c hc
      rcases hl c hc with h | h
      · exact h
      · exact absurd h (hex c hc)
    rw [this]
    simp

private theorem Comp.map_WF {V W : Type*} (f : V → W) {c : Comp V} (h : c.WF) : (c.map f).WF :=
  ⟨fun hw => by simp only [Comp.map] at hw ⊢; rw [h.1 hw],
    fun hl => h.2 (by simpa [Comp.map] using hl)⟩

end Final

section Transfer

variable {k n : ℕ}

private theorem filter_dot_eraseIdx {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) (hk : c.kind ≠ .dot) :
    ((L.eraseIdx i).filter fun c => decide (c.kind = .dot)).Perm
      (L.filter fun c => decide (c.kind = .dot)) := by
  have h := (perm_eraseIdx hc).filter (fun c => decide (c.kind = .dot))
  rw [List.filter_cons_of_neg (by simpa using hk)] at h
  exact h.symm

private theorem filter_dot_append {L new : List (Comp (Atom k n))}
    (hnew : ∀ d ∈ new, d.kind ≠ .dot) :
    (L ++ new).filter (fun c => decide (c.kind = .dot)) =
      L.filter fun c => decide (c.kind = .dot) := by
  have : new.filter (fun c => decide (c.kind = .dot)) = [] :=
    List.filter_eq_nil_iff.2 (fun d hd => by simpa using hnew d hd)
  rw [List.filter_append, this, List.append_nil]

/-- The needed dotted edges between internal atoms depend only on the dotted components. -/
private theorem nonRedInt_of_perm {L L' : List (Comp (Atom k n))} (h : NonRedInt L)
    (hp : (L'.filter fun c => decide (c.kind = .dot)).Perm
      (L.filter fun c => decide (c.kind = .dot))) : NonRedInt L' := by
  intro e M hM hk hx hy hr
  have h1 : (L'.filter fun c => decide (c.kind = .dot)).Perm
      (e :: M.filter fun c => decide (c.kind = .dot)) := by
    have := hM.filter (fun c => decide (c.kind = .dot))
    rwa [List.filter_cons_of_pos (by simpa using hk)] at this
  have h2 : L.Perm (e :: (M.filter (fun c => decide (c.kind = .dot)) ++
      L.filter fun c => !decide (c.kind = .dot))) := by
    have h3 := (List.filter_append_perm (fun c => decide (c.kind = .dot)) L).symm
    exact h3.trans ((hp.symm.trans h1).append_right _)
  apply h e _ h2 hk hx hy
  have : step1_dg (M.filter (fun c => decide (c.kind = .dot)) ++
      L.filter fun c => !decide (c.kind = .dot)) = step1_dg M := by
    apply dg_congr
    intro d hd
    simp [List.mem_append, List.mem_filter, hd]
  rw [this]
  exact hr

/-- A dotted edge between two blocks keeps the needed dotted edges needed. -/
private theorem nonRedInt_cons_dot {c : Comp (Atom k n)} {L : List (Comp (Atom k n))}
    (h : NonRedInt L) (hk : c.kind = .dot) (hr : ¬ (step1_dg L).Reachable c.x c.y) :
    NonRedInt (c :: L) := by
  intro e M hM hek hx hy hre
  by_cases hec : e = c
  · subst hec
    exact hr (by rw [dg_perm hM.cons_inv]; exact hre)
  · have heL : e ∈ L := by
      have : e ∈ c :: L := hM.symm.subset (List.mem_cons_self ..)
      rcases List.mem_cons.1 this with h' | h'
      · exact absurd h' hec
      · exact h'
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 heL
    have hL := perm_eraseIdx (List.getElem?_eq_getElem hj)
    have hM' : M.Perm (c :: L.eraseIdx j) := by
      have : (L[j] :: M).Perm (L[j] :: c :: L.eraseIdx j) :=
        hM.symm.trans ((hL.cons c).trans (List.Perm.swap _ _ _))
      exact this.cons_inv
    rw [dg_perm hM'] at hre
    have hnr := h _ _ hL hek hx hy
    rcases (reach_add_edge_iff (dg_cons_dot_adj _ hk) _ _).1 hre with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hnr h1
    · apply hr
      have hee : (step1_dg L).Reachable L[j].x L[j].y := by
        rw [dg_perm hL]
        exact s1c_dg_reach_of_mem (List.mem_cons_self ..) hek
      have hm : ∀ a b, (step1_dg (L.eraseIdx j)).Reachable a b → (step1_dg L).Reachable a b :=
        fun a b => dg_reach_mono fun d hd _ => List.mem_of_mem_eraseIdx hd
      exact ((hm _ _ h1).symm.trans hee).trans (hm _ _ h2).symm
    · apply hr
      have hee : (step1_dg L).Reachable L[j].x L[j].y := by
        rw [dg_perm hL]
        exact s1c_dg_reach_of_mem (List.mem_cons_self ..) hek
      have hm : ∀ a b, (step1_dg (L.eraseIdx j)).Reachable a b → (step1_dg L).Reachable a b :=
        fun a b => dg_reach_mono fun d hd _ => List.mem_of_mem_eraseIdx hd
      exact ((hm _ _ h2).trans hee.symm).trans (hm _ _ h1)

private theorem sizeΦ_le_of_filter {D' : ℕ} {X : Atom k n} {L L' : List (Comp (Atom k n))}
    (hl : L'.length ≤ L.length)
    (hp : (L'.filter (pendB X)).length ≤ (L.filter (pendB X)).length)
    (hm : nMin L' ≤ nMin L) (hi : nInv L' ≤ nInv L) : step1_sizeΦ D' X L' ≤ step1_sizeΦ D' X L := by
  unfold step1_sizeΦ nPend
  have := Nat.mul_le_mul_left (D' + 3) (Nat.add_le_add hp hm)
  have := Nat.mul_le_mul_left (D' + 1) hi
  omega

private theorem length_filter_eraseIdx_le {L : List (Comp (Atom k n))} (i : ℕ)
    (p : Comp (Atom k n) → Bool) : ((L.eraseIdx i).filter p).length ≤ (L.filter p).length :=
  ((List.eraseIdx_sublist L i).filter p).length_le

end Transfer

section Clean

variable {k n : ℕ}

private theorem solidJoinB_iff (L : List (Comp (Atom k n))) (u v : Atom k n) :
    solidJoinB L u v = true ↔ Step1HasS L u v := by
  simp only [solidJoinB, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Step1HasS]

private theorem nonRedInt_perm {L L' : List (Comp (Atom k n))} (h : NonRedInt L) (hp : L.Perm L') :
    NonRedInt L' := fun e M hM => h e M (hp.trans hM)

private theorem hasS_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ d, d.kind.isSolid = true → (d ∈ L ↔ d ∈ L')) (u v : Atom k n) :
    Step1HasS L u v ↔ Step1HasS L' u v := by
  constructor
  · rintro ⟨d, hd, hk, hxy⟩
    exact ⟨d, (h d hk).1 hd, hk, hxy⟩
  · rintro ⟨d, hd, hk, hxy⟩
    exact ⟨d, (h d hk).2 hd, hk, hxy⟩

private theorem hasX_of_ne {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) {u v : Atom k n} (h : Step1HasX L u v)
    (hne : ¬ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) : Step1HasX (L.eraseIdx i) u v := by
  obtain ⟨d, hd, hk, hxy⟩ := h
  refine ⟨d, mem_eraseIdx_of_ne hc hd ?_, hk, hxy⟩
  rintro rfl
  exact hne hxy

private theorem hasX_mono {L L' : List (Comp (Atom k n))} (h : ∀ d ∈ L, d ∈ L')
    {u v : Atom k n} (hx : Step1HasX L u v) : Step1HasX L' u v := by
  obtain ⟨d, hd, hk, hxy⟩ := hx
  exact ⟨d, h d hd, hk, hxy⟩

/-- Removing a component other than a dotted, waved or diffusive one keeps a doubly connected
structure; the components in its place keep the blue nets joined. -/
private theorem dcs_replace {T T' : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n)))
    (hT' : T'.comps = T.comps.eraseIdx i ++ new)
    (hjm : c.kind.joinsMol = false) (hdf : c.kind.isDiffusive = false) (hng : c.kind ≠ .ghost)
    (hmolnew : ∀ d ∈ T.comps, d.kind.joinsMol = true → d ≠ c → T'.molGraph.Reachable d.x d.y)
    (hblue : c.kind = .G .plus → ∀ a b, c.x = Sum.inr a → c.y = Sum.inr b →
      ∀ L₀ : List (TC k n), L₀.map Prod.fst = T.comps.eraseIdx i →
        (T'.netT (L₀ ++ new.map fun d => (d, if d.kind = .G .plus then some true else none))
          true).Reachable a b)
    (h : T.Step1DCS .plus) : T'.Step1DCS .plus := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  have hLi : i < L.length := by rw [← List.length_map (f := Prod.fst), hL.map_fst]; exact hi
  have hLc : L[i]? = some L[i] := List.getElem?_eq_getElem hLi
  have hfst : L[i].1 = T.comps[i] := by
    have := congrArg (fun l => l[i]?) hL.map_fst
    simp only [List.getElem?_map, List.getElem?_eq_getElem hLi, List.getElem?_eq_getElem hi,
      Option.map_some, Option.some.injEq] at this
    exact this
  have hmap0 : (L.eraseIdx i).map Prod.fst = T.comps.eraseIdx i := by
    rw [← List.eraseIdx_map, hL.map_fst]
  refine ⟨_, hL.same (L.eraseIdx i ++ new.map fun d =>
    (d, if d.kind = .G .plus then some true else none)) ?_ ?_ ?_ ?_ ?_⟩
  · rw [List.map_append, hmap0, hT', List.map_map]
    congr 1
    rw [show (Prod.fst ∘ fun d : Comp (Atom k n) =>
      (d, if d.kind = .G .plus then some true else none)) = id from rfl, List.map_id]
  · intro p hp hpt
    rcases List.mem_append.1 hp with hp | hp
    · exact hL.black p (List.mem_of_mem_eraseIdx hp) hpt
    · obtain ⟨d, -, rfl⟩ := List.mem_map.1 hp
      by_cases hd : d.kind = .G .plus <;> simp [hd] at hpt
  · intro p hp hpt
    rcases List.mem_append.1 hp with hp | hp
    · exact hL.blue p (List.mem_of_mem_eraseIdx hp) hpt
    · obtain ⟨d, -, rfl⟩ := List.mem_map.1 hp
      by_cases hd : d.kind = .G .plus
      · right
        simp [hd, Kind.blueC]
      · simp [hd] at hpt
  · intro d hd hdk
    by_cases hdc : d = T.comps[i]
    · rw [hdc] at hdk
      rw [hdk] at hjm
      cases hjm
    · exact hmolnew d hd hdk hdc
  · intro t p hp hpt a b hx hy
    rcases mem_or_of_mem hLc hp with hp' | hpe
    · exact Graph.netT_reach_of_mem _ _ _ (List.mem_append_left _ hp') hpt hx hy
    · subst hpe
      have hkt := hL.kind_of_tag hp (by rw [hpt]; simp)
      rw [hfst, hdf] at hkt
      simp only [Bool.false_eq_true, false_or] at hkt
      have hG : T.comps[i].kind = .G .plus := by
        generalize T.comps[i].kind = κ at hkt hng
        cases κ with
        | G ch => cases ch <;> simp_all [Kind.blueC]
        | _ => simp_all [Kind.blueC]
      have ht : t = true := by
        rcases t with _ | _
        · have := hL.black _ hp hpt
          rw [hfst, hdf] at this
          cases this
        · rfl
      subst ht
      rw [hfst] at hx hy
      exact hblue hG a b hx hy (L.eraseIdx i) hmap0

end Clean

section CleanSteps

variable {k n : ℕ}

/-- The term of `1_{u ≠ v} = 1 - 1_{u = v}` without the `×`-dotted edge. -/
private theorem clean_drop {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    (hmin : ∀ c ∈ T.comps, c.minor = []) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hk : c.kind = .xdot) (hns : ¬ Step1HasS T.comps c.x c.y)
    (hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i, T.coeff⟩⟩) :
    Step1Base D' S X Γ ⟨T.comps.eraseIdx i, T.coeff⟩ ∧
      (∀ u v, (⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n).SameBlock u v ↔ T.SameBlock u v) ∧
      (⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n).ord = T.ord ∧
      step1_nWD (T.comps.eraseIdx i) = step1_nWD T.comps ∧
      (∀ d ∈ T.comps, d.kind ≠ .xdot → d ∈ T.comps.eraseIdx i) := by
  set g : Graph k n := ⟨T.comps.eraseIdx i, T.coeff⟩ with hg
  have hin : ∀ d ∈ T.comps, d.kind ≠ .xdot → d ∈ g.comps :=
    fun d hd hdk => mem_eraseIdx_of_ne hc hd (fun h => hdk (h ▸ hk))
  have hdots := filter_dot_eraseIdx hc (by rw [hk]; simp)
  obtain ⟨hdg, heL⟩ := dg_eL_of_filter_perm hdots
  have hsb : ∀ u v, g.SameBlock u v ↔ T.SameBlock u v := fun u v => by
    change (step1_dg g.comps).Reachable u v ↔ (step1_dg T.comps).Reachable u v
    rw [hdg]
  have hcl : c.label = none := dotlab_of_wf hB.wf c (List.mem_of_getElem? hc) (Or.inr hk)
  have hordg : g.ord = T.ord := by
    simp only [Graph.ord, hg]
    rw [sum_map_eraseIdx hc (fun c => c.kind.ord) (L := T.comps), hk]
    simp [Kind.ord]
  have hnw : step1_nWD (T.comps.eraseIdx i) = step1_nWD T.comps := by
    unfold step1_nWD
    rw [length_filter_eraseIdx hc (fun c => c.kind.isWDB) (L := T.comps), hk]
    simp [Kind.isWDB]
  refine ⟨⟨hB.chain.tail hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hB.xright, ?_⟩, hsb, hordg, hnw, hin⟩
  · exact connNoX_transfer hB.conn fun d hd hdk => edgeNoX_reach_of_comp (hin d hd hdk) hdk
  · refine internal_transfer hB.internal fun d hd hdk => hin d hd ?_
    intro h
    rw [h] at hdk
    simp [Kind.joinsMol, Kind.isDiffusive] at hdk
  · intro d hd hdk
    have hdT := List.mem_of_mem_eraseIdx hd
    obtain ⟨hne, hx⟩ := hB.solid d hdT hdk
    refine ⟨hne, hasX_of_ne hc hx ?_⟩
    intro hxy
    apply hns
    refine ⟨d, hdT, hdk, ?_⟩
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  · intro d hd hdk hb
    exact hB.xapart d (List.mem_of_mem_eraseIdx hd) hdk ((hsb _ _).1 hb)
  · rw [← hB.excess, heL]
  · exact nonRedInt_of_perm hB.nonred hdots
  · intro hdc
    refine dcs_replace hc [] (by simp [hg]) (by rw [hk]; rfl) (by rw [hk]; rfl) (by rw [hk]; simp)
      ?_ (by intro h; rw [hk] at h; cases h) (hB.dc hdc)
    intro d hd hdk hne
    have : d ∈ g.comps := mem_eraseIdx_of_ne hc hd hne
    have h := Graph.molReach_of_comp this hdk
    simpa [hg] using h
  · exact fun d hd => hB.wf d (List.mem_of_mem_eraseIdx hd)
  · exact fun d hd => hB.noloop d (List.mem_of_mem_eraseIdx hd)
  · exact fun d hd => hB.lab d (List.mem_of_mem_eraseIdx hd)
  · obtain ⟨w, hw, hwl, hwm, hwi⟩ := hB.labex
    refine ⟨w, mem_eraseIdx_of_ne hc hw ?_, hwl, hwm, hwi⟩
    rintro rfl
    rw [hcl] at hwl
    cases hwl
  · exact fun d hd => hB.good d (List.mem_of_mem_eraseIdx hd)
  · exact fun d hd => Or.inl (hmin d (List.mem_of_mem_eraseIdx hd))
  · exact fun d hd => hB.inv d (List.mem_of_mem_eraseIdx hd)
  · exact fun d hd => hB.wd d (List.mem_of_mem_eraseIdx hd)
  · rw [hordg, hnw]
    exact hB.ord
  · refine le_trans (sizeΦ_le_of_filter ?_ (length_filter_eraseIdx_le i _)
      (length_filter_eraseIdx_le i _) (length_filter_eraseIdx_le i _)) hB.size
    exact (List.eraseIdx_sublist _ _).length_le

/-- The term of `1_{u ≠ v} = 1 - 1_{u = v}` with a dotted edge in place of the `×`-dotted edge. -/
private theorem clean_dot {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    (hmin : ∀ c ∈ T.comps, c.minor = []) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hk : c.kind = .xdot) (hns : ¬ Step1HasS T.comps c.x c.y)
    (hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩⟩)
    (hxa : (⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ : Graph k n).XdotApart) :
    Step1Base D' S X Γ ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ ∧
      (∀ u v, T.SameBlock u v →
        (⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ : Graph k n).SameBlock u v) ∧
      (⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ : Graph k n).ord = T.ord + 2 ∧
      step1_nWD (T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) = step1_nWD T.comps ∧
      (∀ d ∈ T.comps, d.kind ≠ .xdot → d ∈ T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) := by
  set g : Graph k n := ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ with hg
  have hin : ∀ d ∈ T.comps, d.kind ≠ .xdot → d ∈ g.comps :=
    fun d hd hdk => List.mem_append_left _ (mem_eraseIdx_of_ne hc hd (fun h => hdk (h ▸ hk)))
  have hdots := filter_dot_eraseIdx hc (by rw [hk]; simp)
  obtain ⟨hdg, heL⟩ := dg_eL_of_filter_perm hdots
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  have hnr : ¬ (step1_dg (T.comps.eraseIdx i)).Reachable c.x c.y := by
    rw [hdg]
    exact hB.xapart c hcT hk
  have hperm : g.comps.Perm (mkC .dot c.x c.y :: T.comps.eraseIdx i) :=
    List.perm_append_singleton _ _
  have hmono : ∀ u v, T.SameBlock u v → g.SameBlock u v := by
    intro u v h
    exact dg_reach_mono (fun d hd hdk => hin d hd (by rw [hdk]; simp)) h
  have hcl : c.label = none := dotlab_of_wf hB.wf c hcT (Or.inr hk)
  have hordg : g.ord = T.ord + 2 := by
    simp only [Graph.ord, hg, List.map_append, List.sum_append]
    rw [sum_map_eraseIdx hc (fun c => c.kind.ord) (L := T.comps), hk]
    simp [Kind.ord, mkC]
    ring
  have hnw : step1_nWD (T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) = step1_nWD T.comps := by
    unfold step1_nWD
    rw [length_filter_eraseIdx hc (fun c => c.kind.isWDB) (L := T.comps), hk, List.filter_append]
    simp [Kind.isWDB, mkC]
  have hfx : ∀ d ∈ g.comps, d ∈ T.comps.eraseIdx i ∨ d = mkC .dot c.x c.y := by
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)
  refine ⟨⟨hB.chain.tail hstep, ?_, ?_, ?_, hxa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hB.xright, ?_⟩, hmono, hordg, hnw, hin⟩
  · exact connNoX_transfer hB.conn fun d hd hdk => edgeNoX_reach_of_comp (hin d hd hdk) hdk
  · refine internal_transfer hB.internal fun d hd hdk => hin d hd ?_
    intro h
    rw [h] at hdk
    simp [Kind.joinsMol, Kind.isDiffusive] at hdk
  · intro d hd hdk
    rcases hfx d hd with hd | rfl
    · have hdT := List.mem_of_mem_eraseIdx hd
      obtain ⟨hne, hx⟩ := hB.solid d hdT hdk
      refine ⟨hne, hasX_mono (fun e he => List.mem_append_left _ he) (hasX_of_ne hc hx ?_)⟩
      intro hxy
      apply hns
      refine ⟨d, hdT, hdk, ?_⟩
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    · simp [mkC, Kind.isSolid] at hdk
  · rw [← hB.excess, eL_perm hperm, eL_cons_dot_new (c := mkC .dot c.x c.y) _ rfl hnr, heL]
  · exact nonRedInt_perm (nonRedInt_cons_dot (c := mkC .dot c.x c.y)
      (nonRedInt_of_perm hB.nonred hdots) rfl hnr) hperm.symm
  · intro hdc
    refine dcs_replace hc [mkC .dot c.x c.y] rfl (by rw [hk]; rfl) (by rw [hk]; rfl)
      (by rw [hk]; simp) ?_ (by intro h; rw [hk] at h; cases h) (hB.dc hdc)
    intro d hd hdk hne
    exact Graph.molReach_of_comp (List.mem_append_left _ (mem_eraseIdx_of_ne hc hd hne)) hdk
  · intro d hd
    rcases hfx d hd with hd | rfl
    · exact hB.wf d (List.mem_of_mem_eraseIdx hd)
    · exact ⟨by simp [mkC, Kind.isWeight], by simp [mkC]⟩
  · intro d hd hdk
    rcases hfx d hd with hd | rfl
    · exact hB.noloop d (List.mem_of_mem_eraseIdx hd) hdk
    · intro h
      have h' : c.x = c.y := h
      exact hB.xapart c hcT hk (by rw [h']; exact SimpleGraph.Reachable.refl _)
  · intro d hd
    rcases hfx d hd with hd | rfl
    · exact hB.lab d (List.mem_of_mem_eraseIdx hd)
    · exact Or.inl rfl
  · obtain ⟨w, hw, hwl, hwm, hwi⟩ := hB.labex
    refine ⟨w, List.mem_append_left _ (mem_eraseIdx_of_ne hc hw ?_), hwl, hwm, hwi⟩
    rintro rfl
    rw [hcl] at hwl
    cases hwl
  · intro d hd hdl
    rcases hfx d hd with hd | rfl
    · exact hB.good d (List.mem_of_mem_eraseIdx hd) hdl
    · simp [mkC] at hdl
  · intro d hd
    rcases hfx d hd with hd | rfl
    · exact Or.inl (hmin d (List.mem_of_mem_eraseIdx hd))
    · exact Or.inl rfl
  · intro d hd hdi
    rcases hfx d hd with hd | rfl
    · exact hB.inv d (List.mem_of_mem_eraseIdx hd) hdi
    · simp [mkC, Kind.step1_isInvB] at hdi
  · intro d hd hdi
    rcases hfx d hd with hd | rfl
    · exact hB.wd d (List.mem_of_mem_eraseIdx hd) hdi
    · rfl
  · rw [hordg, hnw]
    linarith [hB.ord]
  · refine le_trans (sizeΦ_le_of_filter (L' := T.comps.eraseIdx i ++ [mkC .dot c.x c.y])
      ?_ ?_ ?_ ?_) hB.size
    · simp only [List.length_append, List.length_singleton]
      rw [List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
      have := List.length_pos_of_mem hcT
      omega
    · rw [List.filter_append, List.length_append, length_filter_eraseIdx hc (pendB X)]
      simp [pendB, mkC, Kind.isRandom]
    · unfold nMin
      rw [List.filter_append, List.length_append, length_filter_eraseIdx hc]
      simp [mkC]
    · unfold nInv
      rw [List.filter_append, List.length_append, length_filter_eraseIdx hc]
      simp [mkC, Kind.step1_isInvB]

end CleanSteps

section CleanPhase

variable {k n : ℕ}

private theorem oXdotT_eq {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hk : c.kind = .xdot) (hl : c.label = none)
    (hs : solidJoinB T.comps c.x c.y = false) :
    oXdotT i T = [Tracked.self ⟨T.comps.eraseIdx i, T.coeff⟩,
      Tracked.self ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩] := by
  unfold solidJoinB at hs
  simp only [oXdotT, hc]
  rw [ite_eq_left ⟨hk, hl, hs⟩]

private theorem badB_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ d, d.kind.isSolid = true → (d ∈ L ↔ d ∈ L')) (c : Comp (Atom k n)) :
    badB L c = badB L' c := by
  have : solidJoinB L c.x c.y = solidJoinB L' c.x c.y := by
    rw [Bool.eq_iff_iff, solidJoinB_iff, solidJoinB_iff]
    exact hasS_congr h _ _
  simp only [badB, this]

end CleanPhase

section ReplaceStep

variable {k n : ℕ}

private theorem Kind.random_facts {κ : Kind} (h : κ.isRandom = true) :
    κ.joinsMol = false ∧ κ.isDiffusive = false ∧ κ ≠ .ghost ∧ κ ≠ .dot ∧ κ ≠ .xdot ∧
      (κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true → False) := by
  cases κ <;> simp_all [Kind.isRandom, Kind.joinsMol, Kind.isDiffusive]

private theorem ord_replace {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n))) (co : Coeff) :
    (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord =
      T.ord - c.kind.ord + (new.map fun d => d.kind.ord).sum := by
  simp only [Graph.ord, List.map_append, List.sum_append]
  rw [sum_map_eraseIdx hc (fun c => c.kind.ord) (L := T.comps)]
  ring

private theorem count_replace {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) (new : List (Comp (Atom k n))) (p : Comp (Atom k n) → Bool) :
    ((L.eraseIdx i ++ new).filter p).length + (if p c then 1 else 0) =
      (L.filter p).length + (new.filter p).length := by
  rw [List.filter_append, List.length_append, length_filter_eraseIdx hc p]
  ring

end ReplaceStep

section TaylorPhase

variable {k n : ℕ}

private theorem oTaylorT_eq {T : Graph k n} (D' : ℕ) {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch)
    (hg : (c.label.all fun ℓ => T.GoodGroup ℓ &&
      (T.comps.eraseIdx i).any fun c' => decide (c'.label = some ℓ)) = true) :
    oTaylorT D' i T = (((List.range (D' + 1)).map fun j =>
        (⟨T.comps.eraseIdx i ++ List.replicate j { c with kind := .light ch, y := c.x },
          (-1 : Coeff) ^ j * mInvOf ch ^ (j + 1) * T.coeff⟩ : Graph k n)) ++
      [(⟨T.comps.eraseIdx i ++ [{ c with kind := .wD ch D', y := c.x }], T.coeff⟩ : Graph k n)]).map
        Tracked.self := by
  simp only [oTaylorT, hc, hk, hg, ite_true, List.map_append, List.map_map, List.map_cons,
    List.map_nil]
  rfl

end TaylorPhase

section RevPhase

variable {k n : ℕ}

private theorem solidC_ne {V : Type*} [DecidableEq V] (ch : Charge) {u v : V} (h : u ≠ v) :
    solidC ch u v = mkC (.G ch) u v := by
  simp [solidC, h]

/-- The components `G_{ax} G_{xb} (G_{xx})⁻¹` of [II, (4.17), (4.20)] for the component `c` of
charge `ch`, with the label of `c`. -/
private def revNew (X : Atom k n) (c : Comp (Atom k n)) (ch : Charge) : List (Comp (Atom k n)) :=
  [{ mkC (.G ch) c.x X with label := c.label }, { mkC (.G ch) X c.y with label := c.label },
    { mkC (.inv ch) X X with label := c.label }]

private theorem oSchurRevT_eq {T : Graph k n} (X : Atom k n) {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .G ch) (hm : c.minor = [X])
    (hg : c.label.all T.GoodGroup = true) (hx : c.x ≠ X) (hy : c.y ≠ X) :
    oSchurRevT X i T = [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩].map Tracked.self := by
  have h1 := solidC_ne ch hx
  have h2 := solidC_ne ch (Ne.symm hy)
  simp only [oSchurRevT, hc, hk, hm, hg, decide_true, Bool.and_self, ite_true, h1, h2,
    List.map_cons, List.map_nil, revNew]
  rfl

private theorem oSchurWRevT_eq {T : Graph k n} (X : Atom k n) {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .weight ch ∨ c.kind = .light ch)
    (hm : c.minor = [X]) (hg : c.label.all T.GoodGroup = true) (hx : c.x ≠ X) (hyx : c.y = c.x) :
    oSchurWRevT X i T = [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩].map Tracked.self := by
  have hx' : (c.x != X) = true := by simpa using hx
  obtain ⟨κ, a, b, mm, l⟩ := c
  simp only at hyx hx hx' hm hk hg
  subst hyx
  rcases hk with hk | hk <;>
    simp only [oSchurWRevT, hc, hk, hm, hg, hx', decide_true, Bool.and_self, ite_true,
      List.map_cons, List.map_nil, revNew] <;> rfl

private theorem goodGroup_of {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    (c : Comp (Atom k n)) (hc : c ∈ T.comps) : c.label.all T.GoodGroup = true := by
  rcases hB.lab c hc with hl | hl
  · rw [hl]; rfl
  · rw [hl]
    simp only [Option.all_some, Graph.GoodGroup, List.all_eq_true]
    intro d hd
    by_cases hdl : d.label = some (.Q, X)
    · simp [hB.good d hd (by rw [hdl]; rfl)]
    · simp [hdl]

/-- The facts shared by the two terms of [II, (4.20)] at a component with minor `{X}`. -/
private theorem rev_common {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    (hcls : ClsQ X T ∨ ClsW D' X Γ T) {i : ℕ} {c : Comp (Atom k n)} (hc : T.comps[i]? = some c)
    (hm : c.minor = [X]) {ch : Charge}
    (hk : c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch)
    (hstep : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩) :
    ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩],
      Step1Base D' S X Γ g ∧ (ClsQ X g ∨ ClsW D' X Γ g) ∧ nMin g.comps + 1 = nMin T.comps ∧
        step1_nWD g.comps = step1_nWD T.comps := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  obtain ⟨-, -, hx, hy, hxX, hyX⟩ := (hB.minor c hcT).resolve_left (by rw [hm]; simp)
  have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hcnd := (Kind.random_facts hcr).2.2.2.1
  have hci : c.kind.step1_isInvB = false := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hcw : c.kind.isWDB = false := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hord0 := ord_replace hc
  have hBo := hB.ord
  have hBs := hB.size
  -- shared transfer facts
  have hsbT : ∀ new : List (Comp (Atom k n)), (∀ d ∈ new, d.kind ≠ .dot) → ∀ co : Coeff,
      ∀ u v, T.SameBlock u v → (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).SameBlock u v := by
    intro new hnew co u v h
    have hdots : ((T.comps.eraseIdx i ++ new).filter fun c => decide (c.kind = .dot)).Perm
        (T.comps.filter fun c => decide (c.kind = .dot)) := by
      rw [filter_dot_append hnew]
      exact filter_dot_eraseIdx hc hcnd
    change (step1_dg (T.comps.eraseIdx i ++ new)).Reachable u v
    rw [(dg_eL_of_filter_perm hdots).1]
    exact h
  have hsolT : ∀ new : List (Comp (Atom k n)), ∀ co : Coeff, ∀ d ∈ T.comps,
      d.kind.isSolid = true → d.label = none → (d.x = X ∨ d.y = X) →
        d ∈ (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).comps := by
    intro new co d hd _ _ hdX
    refine List.mem_append_left _ (mem_eraseIdx_of_ne hc hd ?_)
    rintro rfl
    rcases hdX with h | h
    · exact hx h
    · exact hy h
  have hQT : ∀ new : List (Comp (Atom k n)), (∀ d ∈ new, d.label = c.label) → ∀ co : Coeff,
      ClsQ X T → ClsQ X ⟨T.comps.eraseIdx i ++ new, co⟩ := by
    intro new hnew co hQ d hd hdr
    rcases List.mem_append.1 hd with h | h
    · exact hQ d (List.mem_of_mem_eraseIdx h) hdr
    · rw [hnew d h]
      exact hQ c hcT hcr
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · -- the term with the minor removed
    have hnew : ∀ d ∈ [{ c with minor := [] }], d = { c with minor := [] } :=
      fun d hd => List.mem_singleton.1 hd
    have hnw : step1_nWD (T.comps.eraseIdx i ++ [{ c with minor := [] }]) = step1_nWD T.comps := by
      have := count_replace hc [{ c with minor := [] }] (fun c => c.kind.isWDB)
      unfold step1_nWD
      simp only [hcw, Bool.false_eq_true, ite_false, add_zero, List.filter_cons,
        List.filter_nil] at this
      simpa using this
    have hord : (⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n).ord =
        T.ord := by
      rw [hord0]
      simp
    have hmin : nMin (T.comps.eraseIdx i ++ [{ c with minor := [] }]) + 1 = nMin T.comps := by
      have := count_replace hc [{ c with minor := [] }] (fun c => !c.minor.isEmpty)
      unfold nMin
      simpa [hm] using this
    refine ⟨?_, cls_replace hcls (hQT _ (by simp) _) (hsolT _ _)
      (hsbT _ (by simpa using hcnd) _) (by rw [hord, hnw]), hmin, hnw⟩
    refine base_replace hB hc [{ c with minor := [] }] T.coeff (hstep _ (by simp)) hcr ?_ ?_ ?_ ?_
      ?_ ?_ (Or.inr (Or.inl (by rw [hm]; simp))) ?_ ?_ ?_ ?_ ?_ ?_
    · intro d hd; rw [hnew d hd]; exact hcr
    · by_cases hxy : c.x = c.y
      · rw [hxy]
      · exact edgeNoX_reach_of_comp (c := { c with minor := [] }) (by simp)
          (Kind.random_facts hcr).2.2.2.2.1
    · intro d hd hds
      rw [hnew d hd] at hds ⊢
      exact hB.solid c hcT hds
    · intro hG _ _
      exact Or.inl ⟨{ c with minor := [] }, by simp, hG, rfl, rfl⟩
    · intro d hd
      rw [hnew d hd]
      exact hB.wf c hcT
    · intro d hd
      rw [hnew d hd]
      exact hB.lab c hcT
    · intro d hd _
      rw [hnew d hd]
      rcases hk with hk | hk | hk <;> simp [Comp.isGoodKind, hk]
    · intro d hd
      rw [hnew d hd]
      exact Or.inl rfl
    · intro d hd hdi
      rw [hnew d hd] at hdi
      rw [hci] at hdi
      cases hdi
    · intro d hd hdi
      rw [hnew d hd] at hdi
      rw [hcw] at hdi
      cases hdi
    · rw [hord, hnw]
      exact hBo
    · refine le_trans ?_ hBs
      have hp := count_replace hc [{ c with minor := [] }] (pendB X)
      have hi' := count_replace hc [{ c with minor := [] }] (fun c => c.kind.step1_isInvB)
      have hl : (T.comps.eraseIdx i ++ [{ c with minor := [] }]).length = T.comps.length := by
        rw [List.length_append, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
        have := List.length_pos_of_mem hcT
        simp only [List.length_singleton]
        omega
      have hcp : pendB X c = false := by simp [pendB, hm]
      have hp1 : (([{ c with minor := [] }] : List (Comp (Atom k n))).filter
          (pendB X)).length ≤ 1 := by
        simp only [List.filter_cons, List.filter_nil]
        split_ifs <;> simp
      simp only [hcp, Bool.false_eq_true, ite_false, add_zero] at hp
      simp only [hci, Bool.false_eq_true, ite_false, add_zero, List.filter_cons,
        List.filter_nil] at hi'
      unfold step1_sizeΦ nPend nInv
      have hi'' : ((T.comps.eraseIdx i ++ [{ c with minor := [] }]).filter
          fun (d : Comp (Atom k n)) => d.kind.step1_isInvB).length =
          (T.comps.filter fun (d : Comp (Atom k n)) => d.kind.step1_isInvB).length := by
        rw [hi']
        simp
      rw [hl, hi'']
      have := hmin
      unfold nMin at this
      unfold nMin
      nlinarith
  · -- the term `- G_{ax} G_{xb} (G_{xx})⁻¹`
    have hmemN : ∀ d ∈ revNew X c ch, d = { mkC (.G ch) c.x X with label := c.label } ∨
        d = { mkC (.G ch) X c.y with label := c.label } ∨
        d = { mkC (.inv ch) X X with label := c.label } := by
      intro d hd
      simpa [revNew] using hd
    have hnw : step1_nWD (T.comps.eraseIdx i ++ revNew X c ch) = step1_nWD T.comps := by
      have := count_replace hc (revNew X c ch) (fun c => c.kind.isWDB)
      unfold step1_nWD
      simp only [hcw, Bool.false_eq_true, ite_false, add_zero] at this
      rw [this]
      simp [revNew, mkC, Kind.isWDB]
    have hordN : ((revNew X c ch).map fun d => d.kind.ord).sum = 2 := by
      simp [revNew, mkC, Kind.ord]
    have hcord : c.kind.ord ≤ 1 := by
      rcases hk with hk | hk | hk <;> rw [hk] <;> simp [Kind.ord]
    have hord : T.ord + 1 ≤ (⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩ : Graph k n).ord := by
      rw [hord0, hordN]
      linarith
    have hmin : nMin (T.comps.eraseIdx i ++ revNew X c ch) + 1 = nMin T.comps := by
      have := count_replace hc (revNew X c ch) (fun c => !c.minor.isEmpty)
      unfold nMin
      simpa [hm, revNew, mkC] using this
    refine ⟨?_, cls_replace hcls (hQT _ (by simp [revNew]) _) (hsolT _ _)
      (hsbT _ (by simp [revNew, mkC]) _) (by rw [hnw]; linarith), hmin, hnw⟩
    refine base_replace hB hc (revNew X c ch) (-T.coeff) (hstep _ (by simp)) hcr ?_ ?_ ?_ ?_
      ?_ ?_ (Or.inr (Or.inl (by rw [hm]; simp))) ?_ ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> rfl
    · have r1 : (⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩ : Graph k n).edgeGraphNoX.Reachable
          c.x X := edgeNoX_reach_of_comp (c := { mkC (.G ch) c.x X with label := c.label })
            (by simp [revNew]) (by simp [mkC])
      have r2 : (⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩ : Graph k n).edgeGraphNoX.Reachable
          X c.y := edgeNoX_reach_of_comp (c := { mkC (.G ch) X c.y with label := c.label })
            (by simp [revNew]) (by simp [mkC])
      exact r1.trans r2
    · intro d hd hds
      rcases hmemN d hd with rfl | rfl | rfl
      · exact ⟨hx, hxX⟩
      · refine ⟨Ne.symm hy, ?_⟩
        obtain ⟨e, he, hek, hexy⟩ := hyX
        exact ⟨e, he, hek, hexy.symm⟩
      · simp [mkC, Kind.isSolid] at hds
    · intro hG _ _
      have hch : ch = .plus := by
        rcases hk with hk | hk | hk <;> rw [hk] at hG <;> cases hG
        rfl
      subst hch
      exact Or.inr ⟨{ mkC (.G .plus) c.x X with label := c.label }, by simp [revNew],
        { mkC (.G .plus) X c.y with label := c.label }, by simp [revNew], rfl, rfl, rfl, rfl, rfl,
        rfl⟩
    · intro d hd
      have hwf := hB.wf c hcT
      rcases hmemN d hd with rfl | rfl | rfl <;>
        exact ⟨fun h => by simp_all [mkC, Kind.isWeight], fun _ => rfl⟩
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> exact hB.lab c hcT
    · intro d hd _
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [mkC, Comp.isGoodKind]
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> exact Or.inl rfl
    · intro d hd hdi
      rcases hmemN d hd with rfl | rfl | rfl
      · simp [mkC, Kind.step1_isInvB] at hdi
      · simp [mkC, Kind.step1_isInvB] at hdi
      · exact ⟨rfl, rfl, rfl⟩
    · intro d hd hdi
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [mkC, Kind.isWDB] at hdi
    · rw [hnw]
      linarith
    · refine le_trans ?_ hBs
      have hp := count_replace hc (revNew X c ch) (pendB X)
      have hi' := count_replace hc (revNew X c ch) (fun c => c.kind.step1_isInvB)
      have hl : (T.comps.eraseIdx i ++ revNew X c ch).length + 1 = T.comps.length + 3 := by
        rw [List.length_append, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
        have := List.length_pos_of_mem hcT
        simp only [revNew, List.length_cons, List.length_nil]
        omega
      have hcp : pendB X c = false := by simp [pendB, hm]
      simp only [hcp, Bool.false_eq_true, ite_false, add_zero] at hp
      simp only [hci, Bool.false_eq_true, ite_false, add_zero] at hi'
      have e1 : (revNew X c ch).filter (pendB X) = [] := by simp [revNew, pendB, mkC]
      have e2 : ((revNew X c ch).filter fun c => c.kind.step1_isInvB).length = 1 := by
        simp [revNew, mkC, Kind.step1_isInvB]
      rw [e1] at hp
      rw [e2] at hi'
      unfold step1_sizeΦ nPend nInv
      have := hmin
      unfold nMin at this
      unfold nMin
      simp only [List.length_nil, add_zero] at hp
      rw [hp, hi']
      nlinarith

end RevPhase

section SchurPhase

variable {k n : ℕ}

private theorem oSchurT_eq {T : Graph k n} (X : Atom k n) {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .G ch) (hm : c.minor = [])
    (hl : c.label = none) (hx : c.x ≠ X) (hy : c.y ≠ X) :
    oSchurT X i T = [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩].map Tracked.self := by
  have h1 := solidC_ne ch hx
  have h2 := solidC_ne ch (Ne.symm hy)
  simp only [oSchurT, hc, hk, hm, hl, List.isEmpty_nil, Option.all_none, Bool.and_self, ite_true,
    h1, h2, List.map_cons, List.map_nil, revNew]
  rfl

private theorem oSchurWT_eq {T : Graph k n} (X : Atom k n) {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .weight ch ∨ c.kind = .light ch)
    (hm : c.minor = []) (hl : c.label = none) (hx : c.x ≠ X) (hyx : c.y = c.x) :
    oSchurWT X i T = [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩].map Tracked.self := by
  have hx' : (c.x != X) = true := by simpa using hx
  obtain ⟨κ, a, b, mm, l⟩ := c
  simp only at hyx hx hx' hm hk hl
  subst hyx hm hl
  rcases hk with hk | hk <;>
    simp only [oSchurWT, hc, hk, hx', List.isEmpty_nil, Option.all_none, Bool.and_self,
      ite_true, List.map_cons, List.map_nil, revNew] <;> rfl

/-- The facts shared by the two terms of [II, (4.17)] at a pending component. -/
private theorem schur_common {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    (hP : PendInv X Γ T) (hcls : ClsW D' X Γ T ∨ AllPend X T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hp : pendB X c = true) {ch : Charge}
    (hk : c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch)
    (hstep : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩) :
    ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩],
      Step1Base D' S X Γ g ∧ PendInv X Γ g ∧ (ClsW D' X Γ g ∨ AllPend X g) ∧
        nPend X g.comps + 1 = nPend X T.comps := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  obtain ⟨hcΓ, hxX, hyX⟩ := hP c hcT hp
  have hpp := hp
  simp only [pendB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, bne_iff_ne,
    ne_eq] at hpp
  obtain ⟨⟨⟨⟨hl, hcr⟩, hm⟩, hx⟩, hy⟩ := hpp
  have hcnd := (Kind.random_facts hcr).2.2.2.1
  have hci : c.kind.step1_isInvB = false := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hcw : c.kind.isWDB = false := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hord0 := ord_replace hc
  have hBo := hB.ord
  have hBs := hB.size
  have hfx : ∀ new : List (Comp (Atom k n)), ∀ d ∈ T.comps.eraseIdx i ++ new,
      d ∈ T.comps ∨ d ∈ new := by
    intro new d hd
    rcases List.mem_append.1 hd with h | h
    · exact Or.inl (List.mem_of_mem_eraseIdx h)
    · exact Or.inr h
  have hXg : ∀ new : List (Comp (Atom k n)), ∀ u v, Step1HasX T.comps u v →
      Step1HasX (T.comps.eraseIdx i ++ new) u v := by
    intro new u v ⟨d, hd, hk', hxy⟩
    refine ⟨d, List.mem_append_left _ (mem_eraseIdx_of_ne hc hd ?_), hk', hxy⟩
    rintro rfl
    exact (Kind.random_facts hcr).2.2.2.2.1 hk'
  have hsbT : ∀ new : List (Comp (Atom k n)), (∀ d ∈ new, d.kind ≠ .dot) → ∀ co : Coeff,
      ∀ u v, T.SameBlock u v → (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).SameBlock u v := by
    intro new hnew co u v h
    have hdots : ((T.comps.eraseIdx i ++ new).filter fun c => decide (c.kind = .dot)).Perm
        (T.comps.filter fun c => decide (c.kind = .dot)) := by
      rw [filter_dot_append hnew]
      exact filter_dot_eraseIdx hc hcnd
    change (step1_dg (T.comps.eraseIdx i ++ new)).Reachable u v
    rw [(dg_eL_of_filter_perm hdots).1]
    exact h
  have hsolT : ∀ new : List (Comp (Atom k n)), ∀ co : Coeff, ∀ d ∈ T.comps,
      d.kind.isSolid = true → d.label = none → (d.x = X ∨ d.y = X) →
        d ∈ (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).comps := by
    intro new co d hd _ _ hdX
    refine List.mem_append_left _ (mem_eraseIdx_of_ne hc hd ?_)
    rintro rfl
    rcases hdX with h | h
    · exact hx h
    · exact hy h
  have hPg : ∀ new : List (Comp (Atom k n)), (∀ d ∈ new, pendB X d = false) →
      PendInv X Γ ⟨T.comps.eraseIdx i ++ new, T.coeff⟩ := by
    intro new hnew d hd hdp
    rcases hfx new d hd with h | h
    · obtain ⟨h1, h2, h3⟩ := hP d h hdp
      exact ⟨h1, hXg new _ _ h2, hXg new _ _ h3⟩
    · rw [hnew d h] at hdp
      cases hdp
  have hnP : ∀ new : List (Comp (Atom k n)), (∀ d ∈ new, pendB X d = false) →
      nPend X (T.comps.eraseIdx i ++ new) + 1 = nPend X T.comps := by
    intro new hnew
    have := count_replace hc new (pendB X)
    have e : new.filter (pendB X) = [] :=
      List.filter_eq_nil_iff.2 (fun d hd => by rw [hnew d hd]; simp)
    rw [hp, e] at this
    unfold nPend
    simpa using this
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · -- the term with the minor `{X}`
    have hnew : ∀ d ∈ [{ c with minor := [X] }], d = { c with minor := [X] } :=
      fun d hd => List.mem_singleton.1 hd
    have hnp : ∀ d ∈ [{ c with minor := [X] }], pendB X d = false := by
      intro d hd
      rw [hnew d hd]
      simp [pendB]
    have hnw : step1_nWD (T.comps.eraseIdx i ++ [{ c with minor := [X] }]) = step1_nWD T.comps := by
      have := count_replace hc [{ c with minor := [X] }] (fun c => c.kind.isWDB)
      unfold step1_nWD
      simp only [hcw, Bool.false_eq_true, ite_false, add_zero, List.filter_cons,
        List.filter_nil] at this
      simpa using this
    have hord : (⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n).ord =
        T.ord := by
      rw [hord0]
      simp
    have hmin : nMin (T.comps.eraseIdx i ++ [{ c with minor := [X] }]) = nMin T.comps + 1 := by
      have := count_replace hc [{ c with minor := [X] }] (fun c => !c.minor.isEmpty)
      unfold nMin
      simpa [hm] using this
    refine ⟨?_, hPg _ hnp, ?_, hnP _ hnp⟩
    · refine base_replace hB hc [{ c with minor := [X] }] T.coeff (hstep _ (by simp)) hcr ?_ ?_ ?_
        ?_ ?_ ?_ (Or.inl hl) ?_ ?_ ?_ ?_ ?_ ?_
      · intro d hd; rw [hnew d hd]; exact hcr
      · by_cases hxy : c.x = c.y
        · rw [hxy]
        · exact edgeNoX_reach_of_comp (c := { c with minor := [X] }) (by simp)
            (Kind.random_facts hcr).2.2.2.2.1
      · intro d hd hds
        rw [hnew d hd] at hds ⊢
        exact hB.solid c hcT hds
      · intro hG _ _
        exact Or.inl ⟨{ c with minor := [X] }, by simp, hG, rfl, rfl⟩
      · intro d hd
        rw [hnew d hd]
        exact hB.wf c hcT
      · intro d hd
        rw [hnew d hd]
        exact Or.inl hl
      · intro d hd hdl
        rw [hnew d hd] at hdl
        simp [hl] at hdl
      · intro d hd
        rw [hnew d hd]
        exact Or.inr ⟨rfl, ⟨ch, hk⟩, hx, hy, hxX, hyX⟩
      · intro d hd hdi
        rw [hnew d hd] at hdi
        rw [hci] at hdi
        cases hdi
      · intro d hd hdi
        rw [hnew d hd] at hdi
        rw [hcw] at hdi
        cases hdi
      · rw [hord, hnw]
        exact hBo
      · refine le_trans ?_ hBs
        have hi' := count_replace hc [{ c with minor := [X] }] (fun c => c.kind.step1_isInvB)
        have hl' : (T.comps.eraseIdx i ++ [{ c with minor := [X] }]).length = T.comps.length := by
          rw [List.length_append, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
          have := List.length_pos_of_mem hcT
          simp only [List.length_singleton]
          omega
        simp only [hci, Bool.false_eq_true, ite_false, add_zero, List.filter_cons,
          List.filter_nil] at hi'
        have hi'' : ((T.comps.eraseIdx i ++ [{ c with minor := [X] }]).filter
            fun (d : Comp (Atom k n)) => d.kind.step1_isInvB).length =
            (T.comps.filter fun (d : Comp (Atom k n)) => d.kind.step1_isInvB).length := by
          rw [hi']
          simp
        have hP' := hnP _ hnp
        unfold step1_sizeΦ nInv
        rw [hl', hi'', hmin]
        nlinarith
    · rcases hcls with hW | hA
      · left
        rcases cls_replace (T' := ⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩)
            (Or.inr hW) (fun hq => absurd (hq c hcT hcr) (by rw [hl]; simp))
            (hsolT _ _) (hsbT [{ c with minor := [X] }] (by simpa using hcnd) T.coeff)
            (by rw [hord, hnw]) with hq | hw
        · exact absurd (hq { c with minor := [X] } (by simp) hcr) (by simp [hl])
        · exact hw
      · right
        intro d hd hdl hdr
        rcases hfx _ d hd with h | h
        · exact hA d h hdl hdr
        · rw [hnew d h]
          exact Or.inr rfl
  · -- the term `G_{ax} G_{xb} (G_{xx})⁻¹`
    have hmemN : ∀ d ∈ revNew X c ch, d = { mkC (.G ch) c.x X with label := c.label } ∨
        d = { mkC (.G ch) X c.y with label := c.label } ∨
        d = { mkC (.inv ch) X X with label := c.label } := by
      intro d hd
      simpa [revNew] using hd
    have hnp : ∀ d ∈ revNew X c ch, pendB X d = false := by
      intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [pendB, mkC]
    have hnw : step1_nWD (T.comps.eraseIdx i ++ revNew X c ch) = step1_nWD T.comps := by
      have := count_replace hc (revNew X c ch) (fun c => c.kind.isWDB)
      unfold step1_nWD
      simp only [hcw, Bool.false_eq_true, ite_false, add_zero] at this
      rw [this]
      simp [revNew, mkC, Kind.isWDB]
    have hordN : ((revNew X c ch).map fun d => d.kind.ord).sum = 2 := by
      simp [revNew, mkC, Kind.ord]
    have hcord : c.kind.ord ≤ 1 := by
      rcases hk with hk | hk | hk <;> rw [hk] <;> simp [Kind.ord]
    have hord : T.ord + 1 ≤ (⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩ : Graph k n).ord := by
      rw [hord0, hordN]
      linarith
    have hmin : nMin (T.comps.eraseIdx i ++ revNew X c ch) = nMin T.comps := by
      have := count_replace hc (revNew X c ch) (fun c => !c.minor.isEmpty)
      unfold nMin
      simpa [hm, revNew, mkC] using this
    refine ⟨?_, hPg _ hnp, Or.inl ⟨⟨c, hcΓ, hl, hcr, c.x, by simp, Or.inr
      ⟨{ mkC (.G ch) c.x X with label := c.label },
        List.mem_append_right _ (by unfold revNew; exact List.mem_cons_self ..), rfl,
        (show c.label = none from hl), Or.inl ⟨rfl, rfl⟩⟩⟩, by rw [hnw]; linarith⟩, hnP _ hnp⟩
    refine base_replace hB hc (revNew X c ch) T.coeff (hstep _ (by simp)) hcr ?_ ?_ ?_ ?_
      ?_ ?_ (Or.inl hl) ?_ ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> rfl
    · have r1 : (⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩ : Graph k n).edgeGraphNoX.Reachable
          c.x X := edgeNoX_reach_of_comp (c := { mkC (.G ch) c.x X with label := c.label })
            (by simp [revNew]) (by simp [mkC])
      have r2 : (⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩ : Graph k n).edgeGraphNoX.Reachable
          X c.y := edgeNoX_reach_of_comp (c := { mkC (.G ch) X c.y with label := c.label })
            (by simp [revNew]) (by simp [mkC])
      exact r1.trans r2
    · intro d hd hds
      rcases hmemN d hd with rfl | rfl | rfl
      · exact ⟨hx, hxX⟩
      · refine ⟨Ne.symm hy, ?_⟩
        obtain ⟨e, he, hek, hexy⟩ := hyX
        exact ⟨e, he, hek, hexy.symm⟩
      · simp [mkC, Kind.isSolid] at hds
    · intro hG _ _
      have hch : ch = .plus := by
        rcases hk with hk | hk | hk <;> rw [hk] at hG <;> cases hG
        rfl
      subst hch
      exact Or.inr ⟨{ mkC (.G .plus) c.x X with label := c.label }, by simp [revNew],
        { mkC (.G .plus) X c.y with label := c.label }, by simp [revNew], rfl, rfl, rfl, rfl, rfl,
        rfl⟩
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;>
        exact ⟨fun h => by simp_all [mkC, Kind.isWeight], fun _ => by simp_all⟩
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> exact Or.inl hl
    · intro d hd hdl
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [hl] at hdl
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> exact Or.inl rfl
    · intro d hd hdi
      rcases hmemN d hd with rfl | rfl | rfl
      · simp [mkC, Kind.step1_isInvB] at hdi
      · simp [mkC, Kind.step1_isInvB] at hdi
      · exact ⟨rfl, rfl, rfl⟩
    · intro d hd hdi
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [mkC, Kind.isWDB] at hdi
    · rw [hnw]
      linarith
    · refine le_trans ?_ hBs
      have hi' := count_replace hc (revNew X c ch) (fun c => c.kind.step1_isInvB)
      have hl' : (T.comps.eraseIdx i ++ revNew X c ch).length + 1 = T.comps.length + 3 := by
        rw [List.length_append, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
        have := List.length_pos_of_mem hcT
        simp only [revNew, List.length_cons, List.length_nil]
        omega
      simp only [hci, Bool.false_eq_true, ite_false, add_zero] at hi'
      have e2 : ((revNew X c ch).filter fun c => c.kind.step1_isInvB).length = 1 := by
        simp [revNew, mkC, Kind.step1_isInvB]
      rw [e2] at hi'
      have hP' := hnP _ hnp
      unfold step1_sizeΦ nInv
      rw [hi', hmin]
      nlinarith

end SchurPhase

section SchurPhase2

variable {k n : ℕ}

private theorem kind_of_plain_random {c : Comp (Atom k n)} (hp : c.minor = [] ∧
    (∀ ch, c.kind ≠ .inv ch) ∧ (∀ ch d, c.kind ≠ .wD ch d) ∧ (c.kind = .dot → c.x ≠ c.y) ∧ c.WF)
    (hr : c.kind.isRandom = true) :
    ∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch := by
  obtain ⟨-, hi, hw, -, -⟩ := hp
  revert hi hw hr
  cases c.kind with
  | G ch => exact fun _ _ _ => ⟨ch, Or.inl rfl⟩
  | weight ch => exact fun _ _ _ => ⟨ch, Or.inr (Or.inl rfl)⟩
  | light ch => exact fun _ _ _ => ⟨ch, Or.inr (Or.inr rfl)⟩
  | inv ch => exact fun _ hi _ => absurd rfl (hi ch)
  | wD ch d => exact fun _ _ hw => absurd rfl (hw ch d)
  | _ => simp [Kind.isRandom]

end SchurPhase2

section SchurPhase3

variable {k n : ℕ}

private theorem nMin_le_S {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T) :
    nMin T.comps ≤ S :=
  le_trans (List.length_filter_le _ _) (le_trans (by unfold step1_sizeΦ; omega) hB.size)

end SchurPhase3

section SplitPhase

variable {k n : ℕ}

private theorem sizeΦ_append_xdot {D' : ℕ} {X : Atom k n} (L : List (Comp (Atom k n)))
    {κ : Kind} (hκ : κ = .dot ∨ κ = .xdot) (u v : Atom k n) :
    step1_sizeΦ D' X (L ++ [mkC κ u v]) = step1_sizeΦ D' X L + 1 := by
  unfold step1_sizeΦ nPend nMin nInv
  rw [List.filter_append, List.filter_append, List.filter_append]
  rcases hκ with rfl | rfl <;> simp [mkC, pendB, Kind.isRandom, Kind.step1_isInvB] <;> ring

end SplitPhase

section SplitPhase2

variable {k n : ℕ}

private theorem oSplitT_eq {T : Graph k n} {u X : Atom k n} (h : u ≠ X) :
    oSplitT u X T = [(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
      ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩].map Tracked.self := by
  simp [oSplitT, h]

private theorem nBad_le_S {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T) :
    nBad T.comps ≤ S :=
  le_trans (List.length_filter_le _ _) (le_trans (by unfold step1_sizeΦ; omega) hB.size)

private theorem nPend_le_S {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T) :
    nPend X T.comps ≤ S :=
  le_trans (List.length_filter_le _ _) (le_trans (by unfold step1_sizeΦ; omega) hB.size)

end SplitPhase2

section Instances

end Instances

section OAt

variable {k n : ℕ}

private theorem atO_iff {o : Fin k} {c : Comp (Atom k n)} :
    step1_atO o c = true ↔ (c.x = .inl o ∨ c.y = .inl o) := by
  simp [step1_atO]

/-- A component whose ends are ends of `c` or the internal atom `X` is at the external atom `o`
only if `c` is. -/
private theorem atO_of_ends {o : Fin k} {c d : Comp (Atom k n)} {X : Atom k n}
    (hX : X.isRight = true) (ho : step1_atO o d = true) (hx : d.x = c.x ∨ d.x = c.y ∨ d.x = X)
    (hy : d.y = c.x ∨ d.y = c.y ∨ d.y = X) : step1_atO o c = true := by
  have hXo : X ≠ .inl o := by
    rintro rfl
    cases hX
  rw [atO_iff] at ho ⊢
  rcases ho with h | h
  · rcases hx with e | e | e <;> rw [e] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hXo
  · rcases hy with e | e | e <;> rw [e] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hXo

end OAt

section OSteps

variable {k n : ℕ}

private theorem atO_of_xx {o : Fin k} {c d : Comp (Atom k n)} (ho : step1_atO o d = true)
    (hx : d.x = c.x) (hy : d.y = c.x) : step1_atO o c = true := by
  rw [atO_iff] at ho ⊢
  rw [hx, hy] at ho
  exact Or.inl (ho.elim id id)

/-- A component between an atom of a random component of `Γ` and the internal atom `X` is not at
an external atom at which all components of `Γ` are diffusive. -/
private theorem split_atO {o : Fin k} {Γ : Graph k n} {X u : Atom k n} {c₀ : Comp (Atom k n)}
    (hX : X.isRight = true) (hO : Step1ODiff o Γ) (hc₀ : c₀ ∈ Γ.comps)
    (hr : c₀.kind.isRandom = true) (hu : u ∈ [c₀.x, c₀.y]) (κ : Kind) :
    step1_atO o (mkC κ u X) = false := by
  have hXo : X ≠ .inl o := by
    rintro rfl
    cases hX
  have hnd : c₀.kind.isDiffusive = false := by
    cases hk : c₀.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]
  have hc : ¬ (c₀.x = .inl o ∨ c₀.y = .inl o) := fun h => by
    rw [hO c₀ hc₀ h] at hnd
    cases hnd
  have huo : u ≠ .inl o := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact fun h => hc (Or.inl h)
    · exact fun h => hc (Or.inr h)
  simp [step1_atO, mkC, huo, hXo]

end OSteps

/-! ## The run of [II, Lemma 4.11] with deterministic choices -/

section Run

variable {k : ℕ}

/-- The Taylor degree of [II, (4.21)] for the expansion of `Γ` at error order `D`:
`D + (D + 1 - p)⁺`, with `p` the scaling order of `Γ` counted as in the paper
(`Graph.paperOrd`). -/
def selDeg {n : ℕ} (D : ℕ) (Γ : Graph k n) : ℕ := D + ((D : ℤ) + 1 - Γ.paperOrd).toNat

open Classical in
/-- The index of the first dotted edge of `L` whose ends are joined by the other dotted edges of
`L`. -/
def selStep1_firstRed {n : ℕ} (L : List (Comp (Atom k n))) : Option ℕ :=
  (List.range L.length).find? fun i =>
    decide (∃ c, L[i]? = some c ∧ c.kind = .dot ∧ (step1_dg (L.eraseIdx i)).Reachable c.x c.y)

/-- `r` times: the first dotted edge whose ends are joined by the other dotted edges is removed. -/
def selStep1_drop {n : ℕ} : ℕ → Graph k n → Graph k n
  | 0, g => g
  | r + 1, g =>
    match selStep1_firstRed g.comps with
    | some i => selStep1_drop r ⟨g.comps.eraseIdx i, g.coeff⟩
    | none => g

/-- The last step of the run: `O_merge`, then the removal of redundant dotted edges until the dot
excess is that of `T`. -/
def selStep1_final {n : ℕ} (T : Graph k n) : TExpansion k n :=
  match T.mergeT with
  | some t => [⟨t.nOut, selStep1_drop (step1_eL t.g.comps - step1_eL T.comps).toNat t.g, t.f⟩]
  | none => []

open Classical in
/-- The phase of the `×`-dotted edges without solid edge: at the first one,
`1_{u ≠ v} = 1 - 1_{u = v}`; a term with a `×`-dotted edge inside a block is dropped; with
fuel `0` or no such edge, the last step. -/
def selStep1_clean : ℕ → {n : ℕ} → Graph k n → TExpansion k n
  | 0, _, T => selStep1_final T
  | m + 1, _, T =>
    match T.comps.findIdx? (badB T.comps) with
    | some i => (oXdotT i T).bind fun _ g => if g.XdotApart then selStep1_clean m g else []
    | none => selStep1_final T

/-- The phase of [II, (4.21)] with Taylor degree `d`: at the first weight `(G_{xx})⁻¹`; with
fuel `0` or no such weight, the phase of the `×`-dotted edges without solid edge. -/
def selStep1_taylor (d : ℕ) : ℕ → {n : ℕ} → Graph k n → TExpansion k n
  | 0, _, T => selStep1_clean (nBad T.comps) T
  | m + 1, _, T =>
    match T.comps.findIdx? fun c => c.kind.step1_isInvB with
    | some i => (oTaylorT d i T).bind fun _ g => selStep1_taylor d m g
    | none => selStep1_clean (nBad T.comps) T

/-- [II, (4.20)] at the component with index `i`: at a weight or light weight, `oSchurWRevT`;
otherwise `oSchurRevT`. -/
def selStep1_revAt {n : ℕ} (X : Atom k n) (i : ℕ) (T : Graph k n) : TExpansion k n :=
  match (T.comps[i]?).map Comp.kind with
  | some (.weight _) | some (.light _) => oSchurWRevT X i T
  | _ => oSchurRevT X i T

/-- [II, (4.17)] at the component with index `i`: at a weight or light weight, `oSchurWT`;
otherwise `oSchurT`. -/
def selStep1_schurAt {n : ℕ} (X : Atom k n) (i : ℕ) (T : Graph k n) : TExpansion k n :=
  match (T.comps[i]?).map Comp.kind with
  | some (.weight _) | some (.light _) => oSchurWT X i T
  | _ => oSchurT X i T

/-- The phase of [II, (4.20)]: at the first component with a minor; with fuel `0` or no such
component, the phase of [II, (4.21)]. -/
def selStep1_rev (d : ℕ) : ℕ → {n : ℕ} → Atom k n → Graph k n → TExpansion k n
  | 0, _, _, T => selStep1_taylor d (nInv T.comps) T
  | m + 1, _, X, T =>
    match T.comps.findIdx? fun c => !c.minor.isEmpty with
    | some i => (selStep1_revAt X i T).bind fun f g => selStep1_rev d m (f X) g
    | none => selStep1_taylor d (nInv T.comps) T

open Classical in
/-- If every random component without label is pending or has the minor `{X}`, these factors are
moved into the label group `Q_X` (`Graph.absorb`); then the phase of [II, (4.20)]. -/
def selStep1_absorb (d : ℕ) {n : ℕ} (X : Atom k n) (T : Graph k n) : TExpansion k n :=
  if AllPend X T then selStep1_rev d (nMin (T.absorb (.Q, X)).comps) X (T.absorb (.Q, X))
  else selStep1_rev d (nMin T.comps) X T

/-- The phase of [II, (4.17)]: at the first pending component; with fuel `0` or no pending
component, `selStep1_absorb`. -/
def selStep1_schur (d : ℕ) : ℕ → {n : ℕ} → Atom k n → Graph k n → TExpansion k n
  | 0, _, X, T => selStep1_absorb d X T
  | m + 1, _, X, T =>
    match T.comps.findIdx? (pendB X) with
    | some i => (selStep1_schurAt X i T).bind fun f g => selStep1_schur d m (f X) g
    | none => selStep1_absorb d X T

open Classical in
/-- The splits `1 = 1_{u = X} + 1_{u ≠ X}` at the atoms `us` in order: the term with the dotted
edge goes to the phase of the `×`-dotted edges without solid edge (and is dropped if it has a
`×`-dotted edge inside a block), the term with the `×`-dotted edge goes on; after the last atom,
the phase of [II, (4.17)]. -/
def selStep1_split (d : ℕ) {n : ℕ} (X : Atom k n) : List (Atom k n) → Graph k n → TExpansion k n
  | [], T => selStep1_schur d (nPend X T.comps) X T
  | u :: us, T =>
    (if (⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n).XdotApart then
      selStep1_clean (nBad (T.comps ++ [mkC .dot u X])) ⟨T.comps ++ [mkC .dot u X], T.coeff⟩
    else []) ++ selStep1_split d X us ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩

/-- The atoms of the random components without label of `Γ`, in the order of the components. -/
def selStep1_us {n : ℕ} (Γ : Graph k n) : List (Atom k n) :=
  (Γ.comps.filter fun c => c.label.isNone && c.kind.isRandom).flatMap fun c => [c.x, c.y]

open Classical in
/-- The expansion of [II, Lemma 4.11] of a graph `Γ = Γ₀ Q_X(Γ̃₀)` with Taylor degree `d`,
with every choice made by the first index: no term if `Γ` has a `×`-dotted edge inside a block;
`Γ` itself if `Γ₀` has a weight or edge attached to the block of `X`; otherwise the splits of
the atoms of `Γ₀` against `X`, [II, (4.17)] on every factor of `Γ₀` one by one, the factors
moved into the label group, [II, (4.20)], [II, (4.21)], the removal of the `×`-dotted edges
without solid edge, and `O_merge`. The choices do not depend on `d`, which enters only through
[II, (4.21)]. -/
def selStep1 (d : ℕ) {n : ℕ} (X : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if Γ.XdotApart then
    if Γ.UnlabelledFreeAtBlock X then selStep1_split d X (selStep1_us Γ) Γ else [Tracked.self Γ]
  else []

end Run

/-! ## The Taylor degree -/

section Deg

variable {k n : ℕ}

/-- The Taylor degree is nondecreasing in the error order. -/
theorem selDeg_mono (Γ : Graph k n) {D D' : ℕ} (h : D ≤ D') : selDeg D Γ ≤ selDeg D' Γ := by
  unfold selDeg
  have : ((D : ℤ) + 1 - Γ.paperOrd).toNat ≤ ((D' : ℤ) + 1 - Γ.paperOrd).toNat :=
    Int.toNat_le_toNat (by omega)
  omega

/-- `D + 1 ≤ p + selDeg D Γ`, with `p` the scaling order of `Γ` counted as in the paper. -/
theorem selDeg_add (D : ℕ) (Γ : Graph k n) : (D : ℤ) + 1 ≤ Γ.paperOrd + selDeg D Γ := by
  unfold selDeg
  have := Int.self_le_toNat ((D : ℤ) + 1 - Γ.paperOrd)
  push_cast
  omega

private theorem selStep1_card_cc_le (Γ : Graph k n) :
    (Nat.card Γ.dotGraph.ConnectedComponent : ℤ) ≤ ((k + n : ℕ) : ℤ) := by
  have h1 : Nat.card Γ.dotGraph.ConnectedComponent ≤ Nat.card (Atom k n) :=
    Nat.card_le_card_of_surjective _ fun c => by
      induction c using SimpleGraph.ConnectedComponent.ind with | h a => exact ⟨a, rfl⟩
  have h2 : Nat.card (Atom k n) = k + n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  exact_mod_cast h2 ▸ h1

/-- The dot excess is at most the number of components. -/
theorem selStep1_dotExcess_le (Γ : Graph k n) : Γ.dotExcess ≤ Γ.comps.length := by
  have h1 := selStep1_card_cc_le Γ
  have h2 : Γ.nDots ≤ Γ.comps.length := List.length_filter_le _ _
  unfold Graph.dotExcess
  push_cast at h1 ⊢
  omega

/-- The Taylor degree for an input `Γ` normal regular with bound `C` and with
`D + 1 ≤ ord Γ + j` is at most `D + j + 2 C`. -/
theorem selDeg_le {C j D : ℕ} {Γ : Graph k n} (hN : Γ.Normal C) (hD : (D : ℤ) + 1 ≤ Γ.ord + j) :
    selDeg D Γ ≤ D + j + 2 * C := by
  unfold selDeg
  have hs := hN.1.size
  have he := selStep1_dotExcess_le Γ
  have hlen : (Γ.comps.length : ℤ) ≤ C := by
    have : k + n + Γ.comps.length ≤ C := hs
    exact_mod_cast (show Γ.comps.length ≤ C by omega)
  have : ((D : ℤ) + 1 - Γ.paperOrd).toNat ≤ j + 2 * C := by
    rw [Int.toNat_le]
    unfold Graph.paperOrd
    push_cast
    omega
  omega

end Deg

/-! ## The steps of the phases -/

section SelSteps

variable {k n : ℕ}

/-- One step of [II, (4.20)] at a component with minor `{X}`: the operator gives two graphs,
both keeping the clauses `Step1Base`, the components at the external atoms and the class, with
one component with a minor fewer. -/
theorem selStep1_rev_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    (hK : Step1OK1 Γ T) (hcls : ClsQ X T ∨ ClsW D' X Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hm : c.minor = [X]) :
    ∃ Gs : List (Graph k n), selStep1_revAt X i T = Gs.map Tracked.self ∧ Gs.length = 2 ∧
      TExpansion.ValueEq (Gs.map Tracked.self) T modelAdm ∧
      ∀ g ∈ Gs, (Step1Base D' S X Γ g ∧ (ClsQ X g ∨ ClsW D' X Γ g) ∧
        nMin g.comps + 1 = nMin T.comps ∧
        step1_nWD g.comps = step1_nWD T.comps) ∧ Step1OK1 Γ g := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  obtain ⟨-, ⟨ch, hk⟩, hx, hy, -, -⟩ := (hB.minor c hcT).resolve_left (by rw [hm]; simp)
  have hgg := goodGroup_of hB c hcT
  have hcd : c.kind.isDiffusive = false := by
    rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hOK : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], Step1OK1 Γ g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hK.replace hc hcd _ (fun d hd o ho => by rw [List.mem_singleton.1 hd] at ho; exact ho) _
    · refine hK.replace hc hcd _ (fun d hd o ho => ?_) _
      simp only [revNew, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact atO_of_ends hB.xright ho (Or.inl rfl) (Or.inr (Or.inr rfl))
      · exact atO_of_ends hB.xright ho (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      · exact atO_of_ends hB.xright ho (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl))
  rcases hk with hk | hk
  · have hE := oSchurRevT_eq X hc hk hm hgg hx hy
    have hSel : selStep1_revAt X i T = oSchurRevT X i T := by simp [selStep1_revAt, hc, hk]
    have hst : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
      fun g hg => QElemStep.schurRev X i T (Tracked.self g) hB.xright
        (by rw [hE]; exact List.mem_map_of_mem hg)
    refine ⟨[(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], hSel.trans hE, rfl, ?_,
      fun g hg => ⟨rev_common hB hcls hc hm (Or.inl hk) hst g hg, hOK g hg⟩⟩
    intro Ω ι _ _ PF D₀ hA e
    have := oSchurRev_value k n X i Ω ι PF D₀ hA T e
    unfold oSchurRev at this
    rw [hE] at this
    exact this
  · have hyx : c.y = c.x := (hB.wf c hcT).1 (by rcases hk with hk | hk <;> rw [hk] <;> rfl)
    have hE := oSchurWRevT_eq X hc hk hm hgg hx hyx
    have hSel : selStep1_revAt X i T = oSchurWRevT X i T := by
      rcases hk with hk | hk <;> simp [selStep1_revAt, hc, hk]
    have hst : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
      fun g hg => QElemStep.schurWRev X i T (Tracked.self g) hB.xright
        (by rw [hE]; exact List.mem_map_of_mem hg)
    refine ⟨[(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], hSel.trans hE, rfl, ?_,
      fun g hg => ⟨rev_common hB hcls hc hm (Or.inr hk) hst g hg, hOK g hg⟩⟩
    intro Ω ι _ _ PF D₀ hA e
    have := step1_oSchurWRev_value k n X i Ω ι PF D₀ hA T e
    simp only at this
    rw [hE] at this
    exact this

/-- One step of [II, (4.17)] at a pending component: the operator gives two graphs, both keeping
the clauses `Step1Base`, the components at the external atoms and the class, with one pending
component fewer. -/
theorem selStep1_schur_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hΓ : Γ.Plain)
    (hB : Step1Base D' S X Γ T) (hK : Step1OK1 Γ T) (hP : PendInv X Γ T)
    (hcls : ClsW D' X Γ T ∨ AllPend X T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hp : pendB X c = true) :
    ∃ Gs : List (Graph k n), selStep1_schurAt X i T = Gs.map Tracked.self ∧ Gs.length = 2 ∧
      TExpansion.ValueEq (Gs.map Tracked.self) T modelAdm ∧
      ∀ g ∈ Gs, (Step1Base D' S X Γ g ∧ PendInv X Γ g ∧ (ClsW D' X Γ g ∨ AllPend X g) ∧
        nPend X g.comps + 1 = nPend X T.comps) ∧ Step1OK1 Γ g := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  obtain ⟨hcΓ, -, -⟩ := hP c hcT hp
  have hpp := hp
  simp only [pendB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, bne_iff_ne,
    ne_eq] at hpp
  obtain ⟨⟨⟨⟨hl, hcr⟩, hm⟩, hx⟩, hy⟩ := hpp
  obtain ⟨ch, hk⟩ := kind_of_plain_random (hΓ c hcΓ) hcr
  have hcd : c.kind.isDiffusive = false := by
    rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hOK : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], Step1OK1 Γ g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hK.replace hc hcd _ (fun d hd o ho => by rw [List.mem_singleton.1 hd] at ho; exact ho) _
    · refine hK.replace hc hcd _ (fun d hd o ho => ?_) _
      simp only [revNew, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact atO_of_ends hB.xright ho (Or.inl rfl) (Or.inr (Or.inr rfl))
      · exact atO_of_ends hB.xright ho (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      · exact atO_of_ends hB.xright ho (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl))
  rcases hk with hk | hk
  · have hE := oSchurT_eq X hc hk hm hl hx hy
    have hSel : selStep1_schurAt X i T = oSchurT X i T := by simp [selStep1_schurAt, hc, hk]
    have hst : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
      fun g hg => QElemStep.schur X i T (Tracked.self g) hB.xright
        (by rw [hE]; exact List.mem_map_of_mem hg)
    refine ⟨[(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], hSel.trans hE, rfl, ?_,
      fun g hg => ⟨schur_common hB hP hcls hc hp (Or.inl hk) hst g hg, hOK g hg⟩⟩
    intro Ω ι _ _ PF D₀ hA e
    have := oSchur_value k n X i Ω ι PF D₀ hA T e
    unfold oSchur at this
    rw [hE] at this
    exact this
  · have hyx : c.y = c.x := (hB.wf c hcT).1 (by rcases hk with hk | hk <;> rw [hk] <;> rfl)
    have hE := oSchurWT_eq X hc hk hm hl hx hyx
    have hSel : selStep1_schurAt X i T = oSchurWT X i T := by
      rcases hk with hk | hk <;> simp [selStep1_schurAt, hc, hk]
    have hst : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
      fun g hg => QElemStep.schurW X i T (Tracked.self g) hB.xright
        (by rw [hE]; exact List.mem_map_of_mem hg)
    refine ⟨[(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], hSel.trans hE, rfl, ?_,
      fun g hg => ⟨schur_common hB hP hcls hc hp (Or.inr hk) hst g hg, hOK g hg⟩⟩
    intro Ω ι _ _ PF D₀ hA e
    have := step1_oSchurW_value k n X i Ω ι PF D₀ hA T e
    simp only at this
    rw [hE] at this
    exact this

/-- One step of [II, (4.21)] at a weight `(G_{xx})⁻¹` with Taylor degree `D'`: the operator gives
`D' + 2` graphs, each keeping the clauses `Step1Base`, the components at the external atoms and
the class, with one weight `(G_{xx})⁻¹` fewer. -/
theorem selStep1_taylor_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Step1Base D' S X Γ T) (hK : Step1OK1 Γ T) (hmin : ∀ c ∈ T.comps, c.minor = [])
    (hcls : ClsQ X T ∨ ClsW D' X Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hci : c.kind.step1_isInvB = true) :
    ∃ Gs : List (Graph k n), oTaylorT D' i T = Gs.map Tracked.self ∧ Gs.length = D' + 2 ∧
      TExpansion.ValueEq (Gs.map Tracked.self) T modelAdm ∧
      ∀ g ∈ Gs, Step1Base D' S X Γ g ∧ Step1OK1 Γ g ∧ (∀ c ∈ g.comps, c.minor = []) ∧
        (ClsQ X g ∨ ClsW D' X Γ g) ∧ nInv g.comps + 1 = nInv T.comps := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  have hi : i < T.comps.length := (List.getElem?_eq_some_iff.1 hc).1
  obtain ⟨ch, hk⟩ : ∃ ch, c.kind = .inv ch := by
    revert hci
    cases c.kind <;> simp [Kind.step1_isInvB]
  obtain ⟨hcx, hcy, hcm⟩ := hB.inv c hcT hci
  -- the guard of `oTaylorT`
  have hguard : (c.label.all fun ℓ => T.GoodGroup ℓ &&
      (T.comps.eraseIdx i).any fun c' => decide (c'.label = some ℓ)) = true := by
    rcases hB.lab c hcT with hl | hl
    · rw [hl]; rfl
    · rw [hl]
      simp only [Option.all_some, Bool.and_eq_true, Graph.GoodGroup, List.all_eq_true,
        List.any_eq_true, decide_eq_true_eq]
      refine ⟨fun d hd => ?_, ?_⟩
      · by_cases hdl : d.label = some (.Q, X)
        · simp [hB.good d hd (by rw [hdl]; rfl)]
        · simp [hdl]
      · obtain ⟨w, hw, hwl, -, hwi⟩ := hB.labex
        refine ⟨w, mem_eraseIdx_of_ne hc hw ?_, hwl⟩
        rintro rfl
        rw [hci] at hwi
        cases hwi
  have hE := oTaylorT_eq D' hc hk hguard
  set Lw : Comp (Atom k n) := { c with kind := .light ch, y := c.x } with hLw
  set W : Comp (Atom k n) := { c with kind := .wD ch D', y := c.x } with hW
  set Gs : List (Graph k n) := ((List.range (D' + 1)).map fun j' =>
      (⟨T.comps.eraseIdx i ++ List.replicate j' Lw,
        (-1 : Coeff) ^ j' * mInvOf ch ^ (j' + 1) * T.coeff⟩ : Graph k n)) ++
      [(⟨T.comps.eraseIdx i ++ [W], T.coeff⟩ : Graph k n)] with hGs
  have hv : TExpansion.ValueEq (Gs.map Tracked.self) T modelAdm := by
    intro Ω ι _ _ PF D₀ hA e
    have := oTaylor_value k n D' i Ω ι PF D₀ hA T e
    unfold oTaylor at this
    rw [hE] at this
    exact this
  have hlen : Gs.length = D' + 2 := by simp [hGs]
  refine ⟨Gs, hE, hlen, hv, fun g hg => ?_⟩
  have hstep : QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
    QElemStep.taylor D' i T (Tracked.self g) (by rw [hE]; exact List.mem_map_of_mem hg)
  have hcr : c.kind.isRandom = true := by rw [hk]; rfl
  have hcxy : c.x = c.y := hcx.trans hcy.symm
  have hcp : pendB X c = false := by simp [pendB, hcx]
  have hcmin : (!c.minor.isEmpty) = false := by simp [hcm]
  have hlwp : pendB X Lw = false := by simp [pendB, hLw, hcx]
  have hwp : pendB X W = false := by simp [pendB, hW, hcx]
  -- common facts on the new components
  have hT₀ : ∀ (new : List (Comp (Atom k n))) (co : Coeff),
      (∀ d ∈ new, d = Lw ∨ d = W) →
      QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i ++ new, co⟩⟩ →
      Γ.ord + (D' + 1) * (step1_nWD (T.comps.eraseIdx i ++ new) : ℤ) ≤
        (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord →
      step1_sizeΦ D' X (T.comps.eraseIdx i ++ new) ≤ S →
      T.ord - (D' + 1) * (step1_nWD T.comps : ℤ) ≤
        (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord -
        (D' + 1) * (step1_nWD (T.comps.eraseIdx i ++ new) : ℤ) →
      Step1Base D' S X Γ ⟨T.comps.eraseIdx i ++ new, co⟩ ∧
        Step1OK1 Γ ⟨T.comps.eraseIdx i ++ new, co⟩ ∧
        (∀ c ∈ T.comps.eraseIdx i ++ new, c.minor = []) ∧
        (ClsQ X ⟨T.comps.eraseIdx i ++ new, co⟩ ∨ ClsW D' X Γ ⟨T.comps.eraseIdx i ++ new, co⟩) := by
    intro new co hnew hst hord hsz hord'
    have hfx : ∀ d ∈ T.comps.eraseIdx i ++ new, d ∈ T.comps ∨ d = Lw ∨ d = W := by
      intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact Or.inl (List.mem_of_mem_eraseIdx h)
      · exact Or.inr (hnew d h)
    have hB' : Step1Base D' S X Γ ⟨T.comps.eraseIdx i ++ new, co⟩ := by
      refine base_replace hB hc new co hst hcr ?_ ?_ ?_ ?_ ?_ ?_ (Or.inr (Or.inr hci)) ?_ ?_ ?_ ?_
        (by linarith) hsz
      · intro d hd
        rcases hnew d hd with rfl | rfl <;> simp [hLw, hW, Kind.isRandom]
      · rw [hcxy]
      · intro d hd hds
        rcases hnew d hd with rfl | rfl <;> simp [Kind.isSolid] at hds
      · intro hG
        rw [hk] at hG
        cases hG
      · intro d hd
        have hwc := hB.wf c hcT
        rcases hnew d hd with rfl | rfl <;>
          exact ⟨fun _ => rfl, fun _ => by simp [hLw, hW, Kind.isRandom]⟩
      · intro d hd
        rcases hnew d hd with rfl | rfl <;> exact hB.lab c hcT
      · intro d hd _
        rcases hnew d hd with rfl | rfl <;> simp [hLw, hW, Comp.isGoodKind, hcm]
      · intro d hd
        rcases hnew d hd with rfl | rfl <;> exact Or.inl hcm
      · intro d hd hdi
        rcases hnew d hd with rfl | rfl <;> simp [Kind.step1_isInvB] at hdi
      · intro d hd _
        rcases hnew d hd with rfl | rfl <;> exact hcm
    refine ⟨hB', hK.replace hc (by rw [hk]; rfl) new (fun d hd o ho => by
      rcases hnew d hd with rfl | rfl <;> exact atO_of_xx ho rfl rfl) co, ?_, ?_⟩
    · intro d hd
      rcases hfx d hd with h | rfl | rfl
      · exact hmin d h
      · exact hcm
      · exact hcm
    · refine cls_replace hcls ?_ ?_ ?_ (by push_cast at hord' ⊢; linarith)
      · intro hQ d hd hdr
        rcases hfx d hd with h | rfl | rfl
        · exact hQ d h hdr
        · exact hQ c hcT hcr
        · exact hQ c hcT hcr
      · intro d hd hds _ _
        refine List.mem_append_left _ (mem_eraseIdx_of_ne hc hd ?_)
        rintro rfl
        rw [hk] at hds
        cases hds
      · intro u v h
        have hdots : ((T.comps.eraseIdx i ++ new).filter fun c => decide (c.kind = .dot)).Perm
            (T.comps.filter fun c => decide (c.kind = .dot)) := by
          rw [filter_dot_append (fun d hd => by rcases hnew d hd with rfl | rfl <;> simp)]
          exact filter_dot_eraseIdx hc (by rw [hk]; simp)
        change (step1_dg (T.comps.eraseIdx i ++ new)).Reachable u v
        rw [(dg_eL_of_filter_perm hdots).1]
        exact h
  -- the counts
  have hcnt : ∀ (new : List (Comp (Atom k n))), (∀ d ∈ new, d = Lw ∨ d = W) →
      step1_sizeΦ D' X (T.comps.eraseIdx i ++ new) + (D' + 1) + 1 ≤
        step1_sizeΦ D' X T.comps + new.length ∧
      nInv (T.comps.eraseIdx i ++ new) + 1 = nInv T.comps := by
    intro new hnew
    have hp := count_replace hc new (pendB X)
    have hm' := count_replace hc new (fun c => !c.minor.isEmpty)
    have hi' := count_replace hc new (fun c => c.kind.step1_isInvB)
    have hlen' : (T.comps.eraseIdx i ++ new).length + 1 = T.comps.length + new.length := by
      rw [List.length_append, List.length_eraseIdx_of_lt hi]
      have := List.length_pos_of_mem hcT
      omega
    have e1 : new.filter (pendB X) = [] := List.filter_eq_nil_iff.2 fun d hd => by
      rcases hnew d hd with rfl | rfl <;> simp [hlwp, hwp]
    have e2 : new.filter (fun c => !c.minor.isEmpty) = [] :=
      List.filter_eq_nil_iff.2 fun d hd => by
      rcases hnew d hd with rfl | rfl <;> simp [hLw, hW, hcm]
    have e3 : new.filter (fun c => c.kind.step1_isInvB) = [] :=
      List.filter_eq_nil_iff.2 fun d hd => by
      rcases hnew d hd with rfl | rfl <;> simp [hLw, hW, Kind.step1_isInvB]
    rw [e1, hcp] at hp
    rw [e2, hcmin] at hm'
    rw [e3, hci] at hi'
    simp only [List.length_nil, add_zero, Bool.false_eq_true, ite_false, ite_true] at hp hm' hi'
    unfold step1_sizeΦ nPend nMin nInv
    refine ⟨?_, hi'⟩
    rw [hp, hm']
    nlinarith [hi']
  have hord0 := ord_replace hc
  have hcord : c.kind.ord = 0 := by rw [hk]; rfl
  rw [hGs, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with ⟨j', hj', rfl⟩ | rfl
  · have hj'' : j' ≤ D' := by simp at hj'; omega
    have hnew : ∀ d ∈ List.replicate j' Lw, d = Lw ∨ d = W :=
      fun d hd => Or.inl (List.eq_of_mem_replicate hd)
    obtain ⟨h1, h2⟩ := hcnt _ hnew
    have hnw : step1_nWD (T.comps.eraseIdx i ++ List.replicate j' Lw) = step1_nWD T.comps := by
      have := count_replace hc (List.replicate j' Lw) (fun c => c.kind.isWDB)
      have e : (List.replicate j' Lw).filter (fun c => c.kind.isWDB) = [] :=
        List.filter_eq_nil_iff.2 fun d hd => by
          rw [List.eq_of_mem_replicate hd]; simp [hLw, Kind.isWDB]
      rw [e, hk] at this
      unfold step1_nWD
      have h2 : (Kind.inv ch).isWDB = false := rfl
      simp only [h2, Bool.false_eq_true, ite_false, add_zero, List.length_nil] at this
      exact this
    have hordj : (⟨T.comps.eraseIdx i ++ List.replicate j' Lw,
        (-1 : Coeff) ^ j' * mInvOf ch ^ (j' + 1) * T.coeff⟩ : Graph k n).ord = T.ord + j' := by
      rw [hord0, hcord]
      simp [hLw, Kind.ord, List.map_replicate, List.sum_replicate]
    have hBo := hB.ord
    have hBs := hB.size
    refine (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, h2⟩) (hT₀ _ _ hnew hstep ?_ ?_ ?_)
    · rw [hordj, hnw]
      linarith
    · simp only [List.length_replicate] at h1
      omega
    · rw [hordj, hnw]
      linarith
  · have hnew : ∀ d ∈ [W], d = Lw ∨ d = W := fun d hd => Or.inr (List.mem_singleton.1 hd)
    obtain ⟨h1, h2⟩ := hcnt _ hnew
    have hnw : step1_nWD (T.comps.eraseIdx i ++ [W]) = step1_nWD T.comps + 1 := by
      have := count_replace hc [W] (fun c => c.kind.isWDB)
      rw [hk] at this
      unfold step1_nWD
      have h2 : (Kind.inv ch).isWDB = false := rfl
      have h3 : ([W] : List (Comp (Atom k n))).filter (fun c => c.kind.isWDB) = [W] := by
        simp [hW, Kind.isWDB]
      simp only [h2, h3, Bool.false_eq_true, ite_false, add_zero, List.length_singleton] at this
      exact this
    have hordW : (⟨T.comps.eraseIdx i ++ [W], T.coeff⟩ : Graph k n).ord =
        T.ord + (D' + 1) := by
      rw [hord0, hcord]
      simp [hW, Kind.ord]
    have hBo := hB.ord
    have hBs := hB.size
    refine (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, h2⟩) (hT₀ _ _ hnew hstep ?_ ?_ ?_)
    · rw [hordW, hnw]
      push_cast
      linarith
    · simp only [List.length_singleton] at h1
      omega
    · rw [hordW, hnw]
      push_cast
      linarith

/-- One step of `1_{u ≠ v} = 1 - 1_{u = v}` at a `×`-dotted edge without solid edge: the operator
gives the graph without that edge and the graph with a dotted edge in its place; each of them
without `×`-dotted edge inside a block keeps the clauses `Step1Base`, the components at the
external atoms and the class, with one such `×`-dotted edge fewer, and the first one has no
`×`-dotted edge inside a block. -/
theorem selStep1_clean_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Step1Base D' S X Γ T) (hK : Step1OK1 Γ T) (hmin : ∀ c ∈ T.comps, c.minor = [])
    (hinv : ∀ c ∈ T.comps, c.kind.step1_isInvB = false) (hcls : ClsQ X T ∨ ClsW D' X Γ T)
    {i : ℕ} {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (hb : badB T.comps c = true) :
    oXdotT i T = [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].map Tracked.self ∧
      TExpansion.ValueEq ([(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].map Tracked.self) T modelAdm ∧
      (⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n).XdotApart ∧
      ∀ g ∈ [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩],
        (∀ d ∈ g.comps, (d.kind = .dot ∨ d.kind = .xdot) → d.label = none) ∧
        (g.XdotApart → Step1Base D' S X Γ g ∧ Step1OK1 Γ g ∧ (∀ c ∈ g.comps, c.minor = []) ∧
          (∀ c ∈ g.comps, c.kind.step1_isInvB = false) ∧ (ClsQ X g ∨ ClsW D' X Γ g) ∧
          nBad g.comps + 1 ≤ nBad T.comps) := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  have hcb := hb
  simp only [badB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcb
  obtain ⟨hk, hsj⟩ := hcb
  have hns : ¬ Step1HasS T.comps c.x c.y := by
    rw [← solidJoinB_iff, hsj]
    simp
  have hdotlab := dotlab_of_wf hB.wf
  have hcl : c.label = none := hdotlab c hcT (Or.inr hk)
  have hE := oXdotT_eq hc hk hcl hsj
  have hsame1 : ∀ d, d.kind.isSolid = true → (d ∈ T.comps ↔ d ∈ T.comps.eraseIdx i) := by
    intro d hd
    refine ⟨fun h => mem_eraseIdx_of_ne hc h (fun h' => ?_), List.mem_of_mem_eraseIdx⟩
    rw [h', hk] at hd
    simp [Kind.isSolid] at hd
  have hcnt : nBad T.comps = ((T.comps.eraseIdx i).filter (badB T.comps)).length + 1 := by
    unfold nBad
    rw [length_filter_eraseIdx hc (badB T.comps)]
    simp [badB, hk, hsj]
  have hb1 : nBad (T.comps.eraseIdx i) + 1 ≤ nBad T.comps := by
    unfold nBad
    rw [List.filter_congr (fun d _ => (badB_congr hsame1 d).symm)]
    unfold nBad at hcnt
    omega
  have hsame2 : ∀ d, d.kind.isSolid = true →
      (d ∈ T.comps ↔ d ∈ T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) := by
    intro d hd
    rw [hsame1 d hd, List.mem_append, List.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · simp [mkC, Kind.isSolid] at hd
  have hb2 : nBad (T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) + 1 ≤ nBad T.comps := by
    unfold nBad
    rw [List.filter_congr (fun d _ => (badB_congr hsame2 d).symm), List.filter_append]
    simp only [List.length_append]
    have : ([mkC .dot c.x c.y] : List (Comp (Atom k n))).filter (badB T.comps) = [] := by
      simp [badB, mkC]
    rw [this]
    simp only [List.length_nil, add_zero]
    unfold nBad at hcnt
    omega
  have hv : TExpansion.ValueEq ([(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].map Tracked.self) T modelAdm := by
    intro Ω ι _ _ PF D₀ _ e
    have := step1_oXdot_value k n i Ω ι PF D₀ trivial T e
    simp only [hE] at this
    exact this
  have hstep1 : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i, T.coeff⟩⟩ :=
    QElemStep.xdot i T (Tracked.self ⟨T.comps.eraseIdx i, T.coeff⟩) (by rw [hE]; simp)
  have hD1 := clean_drop hB hmin hc hk hns hstep1
  refine ⟨by rw [hE]; rfl, hv, hD1.1.xapart, ?_⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · refine ⟨fun d hd hdk => hdotlab d (List.mem_of_mem_eraseIdx hd) hdk, fun _ => ?_⟩
    obtain ⟨hB', hsb, hord, hnw, hin⟩ := hD1
    refine ⟨hB', hK.erase hc (by rw [hk]; rfl) T.coeff,
      fun d hd => hmin d (List.mem_of_mem_eraseIdx hd),
      fun d hd => hinv d (List.mem_of_mem_eraseIdx hd), ?_, hb1⟩
    exact cls_transfer hcls (fun d hd _ => List.mem_of_mem_eraseIdx hd)
      (fun d hd hds => hin d hd (by intro h; rw [h] at hds; simp [Kind.isSolid] at hds))
      (fun u v h => (hsb u v).2 h) hord.ge hnw
  · have hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩⟩ :=
      QElemStep.xdot i T (Tracked.self ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩)
        (by rw [hE]; simp)
    refine ⟨?_, fun hxa => ?_⟩
    · intro d hd hdk
      rcases List.mem_append.1 hd with h | h
      · exact hdotlab d (List.mem_of_mem_eraseIdx h) hdk
      · rw [List.mem_singleton.1 h]
        rfl
    obtain ⟨hB', hsb, hord, hnw, hin⟩ := clean_dot hB hmin hc hk hns hstep hxa
    have hfx : ∀ d ∈ T.comps.eraseIdx i ++ [mkC .dot c.x c.y],
        d ∈ T.comps.eraseIdx i ∨ d = mkC .dot c.x c.y := by
      intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.1 h)
    refine ⟨hB', hK.replace hc (by rw [hk]; rfl) _
      (fun d hd o ho => by rw [List.mem_singleton.1 hd] at ho; exact ho) _, ?_, ?_, ?_, hb2⟩
    · intro d hd
      rcases hfx d hd with h | rfl
      · exact hmin d (List.mem_of_mem_eraseIdx h)
      · rfl
    · intro d hd
      rcases hfx d hd with h | rfl
      · exact hinv d (List.mem_of_mem_eraseIdx h)
      · rfl
    · refine cls_transfer hcls ?_
        (fun d hd hds => hin d hd (by intro h; rw [h] at hds; simp [Kind.isSolid] at hds))
        hsb (by rw [hord]; linarith) hnw
      intro d hd hdr
      rcases hfx d hd with h | rfl
      · exact List.mem_of_mem_eraseIdx h
      · simp [mkC, Kind.isRandom] at hdr

/-- One split `1 = 1_{u = X} + 1_{u ≠ X}` at an atom `u` of a random component without label of
`Γ`, when `Γ₀` has no weight or edge attached to the block of `X` and the blocks of `T` are those
of `Γ`: the operator gives the graph with the dotted edge `u = X` and the graph with the
`×`-dotted edge `u ≠ X`. The first one, if it has no `×`-dotted edge inside a block, keeps the
clauses `Step1Base` and the components at the external atoms and has the class `ClsW`; the
second one has no `×`-dotted edge inside a block, keeps the clauses `Step1Base`, the components
at the external atoms and the blocks. -/
theorem selStep1_split_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hfree : Γ.UnlabelledFreeAtBlock X) (hB : Step1Base D' S X Γ T) (hK : Step1OK1 Γ T)
    (hsz : step1_sizeΦ D' X T.comps + 1 ≤ S) (hdg : step1_dg T.comps = step1_dg Γ.comps)
    {u : Atom k n} {c₀ : Comp (Atom k n)} (hc₀ : c₀ ∈ Γ.comps) (hl₀ : c₀.label = none)
    (hr₀ : c₀.kind.isRandom = true) (hu₀ : u ∈ [c₀.x, c₀.y]) :
    oSplitT u X T = [(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
        ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩].map Tracked.self ∧
      TExpansion.ValueEq ([(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
        ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩].map Tracked.self) T modelAdm ∧
      (∀ d ∈ T.comps ++ [mkC .dot u X], (d.kind = .dot ∨ d.kind = .xdot) → d.label = none) ∧
      ((⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n).XdotApart →
        Step1Base D' S X Γ ⟨T.comps ++ [mkC .dot u X], T.coeff⟩ ∧
        Step1OK1 Γ ⟨T.comps ++ [mkC .dot u X], T.coeff⟩ ∧
        ClsW D' X Γ ⟨T.comps ++ [mkC .dot u X], T.coeff⟩) ∧
      Step1Base D' S X Γ ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩ ∧
      Step1OK1 Γ ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩ ∧
      step1_dg (T.comps ++ [mkC .xdot u X]) = step1_dg Γ.comps := by
  have hnb : ¬ T.SameBlock u X := by
    have h := hfree c₀ hc₀ hl₀ hr₀
    change ¬ (step1_dg T.comps).Reachable u X
    rw [hdg]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu₀
    rcases hu₀ with rfl | rfl
    · exact h.1
    · exact h.2
  have huX : u ≠ X := fun h => hnb (by rw [h]; exact SimpleGraph.Reachable.refl _)
  have hnO : ∀ κ, ∀ o, Step1ODiff o Γ → ∀ d ∈ [mkC κ u X], step1_atO o d = false := by
    intro κ o hO d hd
    rw [List.mem_singleton.1 hd]
    exact split_atO hB.xright hO hc₀ hr₀ hu₀ κ
  have hE := oSplitT_eq (T := T) huX
  have hv : TExpansion.ValueEq ([(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
      ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩].map Tracked.self) T modelAdm := by
    intro Ω ι _ _ PF D₀ _ e
    have := step1_oSplit_value k n u X Ω ι PF D₀ trivial T e
    simp only at this
    rw [hE] at this
    exact this
  have hstep : ∀ g ∈ [(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
      ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ := fun g hg =>
    QElemStep.split u X T (Tracked.self g) hB.xright (by rw [hE]; exact List.mem_map_of_mem hg)
  have hdg' : step1_dg (T.comps ++ [mkC .xdot u X]) = step1_dg T.comps := by
    apply dg_congr
    intro e he
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl)
      · exact h
      · simp [mkC] at he
    · exact Or.inl
  have hxa : (⟨T.comps ++ [mkC .xdot u X], T.coeff⟩ : Graph k n).XdotApart := by
    intro d hd hdk hb
    have hb' : T.SameBlock d.x d.y := by
      change (step1_dg T.comps).Reachable d.x d.y
      rw [← hdg']
      exact hb
    rcases List.mem_append.1 hd with h | h
    · exact hB.xapart d h hdk hb'
    · rw [List.mem_singleton.1 h] at hb'
      exact hnb hb'
  obtain ⟨hB₂, -, -⟩ := base_append hB (Or.inr rfl) hnb (hstep _ (by simp)) hxa
    (by rw [sizeΦ_append_xdot _ (Or.inr rfl)]; exact hsz)
  refine ⟨hE, hv, ?_, fun hxa₁ => ?_, hB₂, hK.append _ (hnO .xdot) _, hdg'.trans hdg⟩
  · intro d hd hdk
    rcases List.mem_append.1 hd with h | h
    · exact dotlab_of_wf hB.wf d h hdk
    · rw [List.mem_singleton.1 h]; rfl
  obtain ⟨hB₁, hord, hnw⟩ := base_append hB (Or.inl rfl) hnb (hstep _ (by simp)) hxa₁
    (by rw [sizeΦ_append_xdot _ (Or.inl rfl)]; exact hsz)
  refine ⟨hB₁, hK.append _ (hnO .dot) _, ⟨c₀, hc₀, hl₀, hr₀, u, hu₀, Or.inl ?_⟩, ?_⟩
  · exact s1c_dg_reach_of_mem (L := T.comps ++ [mkC .dot u X]) (c := mkC .dot u X)
      (List.mem_append_right _ (List.mem_singleton_self _)) rfl
  · rw [hord, hnw]
    have := hB.ord
    simp only [Kind.ord]
    linarith

end SelSteps

/-! ## Expansions with a given list of terms -/

section DExp

variable {k n : ℕ}

/-- `F` has the value of `Γ`, at most `B` terms, and every term has the property `P`. -/
private def DExp (P : Tracked k n → Prop) (B : ℕ) (Γ : Graph k n) (F : TExpansion k n) : Prop :=
  F.ValueEq Γ modelAdm ∧ F.length ≤ B ∧ ∀ t ∈ F, P t

private theorem DExp.mono {P : Tracked k n → Prop} {B B' : ℕ} {Γ : Graph k n}
    {F : TExpansion k n} (h : DExp P B Γ F) (hB : B ≤ B') : DExp P B' Γ F :=
  ⟨h.1, h.2.1.trans hB, h.2.2⟩

/-- A graph of value `0` is the value of the empty sum. -/
private theorem DExp.nil {P : Tracked k n → Prop} (B : ℕ) {Γ : Graph k n}
    (h : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
      (e : Fin k → ι), Γ.valR PF D e = 0) : DExp P B Γ [] := by
  refine ⟨?_, by simp, by simp⟩
  intro Ω ι _ _ PF D _ e
  rw [h]
  funext ω
  simp [TExpansion.forget, Expansion.valR]

private theorem selStep1_forget_append {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (E F : TExpansion k n) :
    (E ++ F).forget.valR PF D e = E.forget.valR PF D e + F.forget.valR PF D e := by
  funext ω
  simp [TExpansion.forget, Expansion.valR]

/-- If a formal sum of graphs with the identity maps has the value of `Γ`, and each of its graphs
`g` is the value of `R g`, then `Γ` is the value of the concatenation of the `R g`. -/
private theorem DExp.bind {P : Tracked k n → Prop} {B : ℕ} {Γ : Graph k n}
    (Gs : List (Graph k n)) (R : Graph k n → TExpansion k n)
    (hv : TExpansion.ValueEq (Gs.map Tracked.self) Γ modelAdm)
    (h : ∀ g ∈ Gs, DExp P B g (R g)) : DExp P (Gs.length * B) Γ (Gs.flatMap R) := by
  have key : ∀ Gs : List (Graph k n), (∀ g ∈ Gs, DExp P B g (R g)) →
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
        modelAdm Ω ι PF D → ∀ e : Fin k → ι,
          (TExpansion.forget (Gs.flatMap R)).valR PF D e =
            fun ω => (Gs.map fun g => g.valR PF D e ω).sum) ∧
        (Gs.flatMap R).length ≤ Gs.length * B ∧ ∀ t ∈ Gs.flatMap R, P t := by
    intro Gs
    induction Gs with
    | nil =>
      intro _
      refine ⟨fun _ _ _ _ _ _ _ _ => ?_, by simp, by simp⟩
      funext ω
      simp [TExpansion.forget, Expansion.valR]
    | cons g Gs ih =>
      intro h
      obtain ⟨h1, h2, h3⟩ := h g (List.mem_cons_self ..)
      obtain ⟨h4, h5, h6⟩ := ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
      refine ⟨?_, ?_, ?_⟩
      · intro Ω ι _ _ PF D hA e
        rw [List.flatMap_cons, selStep1_forget_append, h1 Ω ι PF D hA e, h4 Ω ι PF D hA e]
        funext ω
        simp
      · simp only [List.flatMap_cons, List.length_append, List.length_cons]
        nlinarith
      · intro t ht
        rw [List.flatMap_cons] at ht
        rcases List.mem_append.1 ht with ht | ht
        · exact h3 t ht
        · exact h6 t ht
  obtain ⟨h1, h2, h3⟩ := key Gs h
  refine ⟨?_, h2, h3⟩
  intro Ω ι _ _ PF D hA e
  rw [h1 Ω ι PF D hA e, ← hv Ω ι PF D hA e]
  funext ω
  simp [TExpansion.forget, Expansion.valR, Tracked.self, Function.comp_def]

/-- The value of `Γ` as the sum of the values of two graphs, each the value of a formal sum. -/
private theorem DExp.append {P : Tracked k n → Prop} {B₁ B₂ : ℕ} {Γ g₁ g₂ : Graph k n}
    {F₁ F₂ : TExpansion k n}
    (hv : TExpansion.ValueEq ([g₁, g₂].map Tracked.self) Γ modelAdm)
    (h₁ : DExp P B₁ g₁ F₁) (h₂ : DExp P B₂ g₂ F₂) : DExp P (B₁ + B₂) Γ (F₁ ++ F₂) := by
  refine ⟨?_, by simp only [List.length_append]; exact Nat.add_le_add h₁.2.1 h₂.2.1, ?_⟩
  · intro Ω ι _ _ PF D hA e
    rw [selStep1_forget_append, h₁.1 Ω ι PF D hA e, h₂.1 Ω ι PF D hA e, ← hv Ω ι PF D hA e]
    funext ω
    simp [TExpansion.forget, Expansion.valR, Tracked.self]
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact h₁.2.2 t ht
    · exact h₂.2.2 t ht

/-- The operator `O` applied to graphs with the identity maps. -/
private theorem selStep1_bind_self (Gs : List (Graph k n))
    (O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n') :
    TExpansion.bind (Gs.map Tracked.self) O = Gs.flatMap fun g => O id g := by
  unfold TExpansion.bind
  rw [List.flatMap_map]
  congr 1
  funext g
  simp only [Tracked.self, Function.comp_id]
  exact List.map_id' _

private theorem selStep1_findIdx_some {α : Type*} {L : List α} {p : α → Bool} {i : ℕ}
    (h : L.findIdx? p = some i) : ∃ c, L[i]? = some c ∧ p c = true := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  exact ⟨L[i], List.getElem?_eq_getElem hi, hp⟩

end DExp

/-! ## The removal of the redundant dotted edges -/

section SelDrop

variable {k m : ℕ}

private theorem selStep1_firstRed_some {L : List (Comp (Atom k m))} {i : ℕ}
    (h : selStep1_firstRed L = some i) :
    ∃ c, L[i]? = some c ∧ c.kind = .dot ∧ (step1_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep1_firstRed at h
  simpa using List.find?_some h

private theorem selStep1_firstRed_none {L : List (Comp (Atom k m))}
    (h : selStep1_firstRed L = none) {i : ℕ} {c : Comp (Atom k m)} (hc : L[i]? = some c)
    (hk : c.kind = .dot) : ¬ (step1_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep1_firstRed at h
  rw [List.find?_eq_none] at h
  intro hr
  have hi : i < L.length := (List.getElem?_eq_some_iff.1 hc).1
  exact h i (List.mem_range.2 hi) (by simpa using ⟨c, hc, hk, hr⟩)

/-- The facts on `selStep1_drop r g` when `r` dotted edges are redundant. -/
private def DropSpec (e₀ : ℤ) (r : ℕ) (g g' : Graph k m) : Prop :=
  Relation.ReflTransGen QElemStep ⟨m, g⟩ ⟨m, g'⟩ ∧ step1_eL g'.comps = e₀ ∧
    g'.ord = g.ord - 2 * r ∧ g'.coeff = g.coeff ∧ g'.comps.Sublist g.comps ∧
    (∀ d ∈ g.comps, d.kind ≠ .dot → d ∈ g'.comps) ∧
    (∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) ∧
    (g.Step1DCS .plus → g'.Step1DCS .plus) ∧ (g.ConnNoX → g'.ConnNoX) ∧
    g'.wavedThetaGraph = g.wavedThetaGraph ∧
    ((∀ d ∈ g.comps, d.kind = .dot → d.label = none) →
      ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e : Fin k → ι), g'.valR PF D e = g.valR PF D e) ∧
    (g'.comps.filter fun c => decide (c.kind ≠ .dot)).Perm
      (g.comps.filter fun c => decide (c.kind ≠ .dot))

/-- Removing `r` times the first redundant dotted edge brings the dot excess down to `e₀`; the
components other than dotted edges are kept with their multiplicities. -/
private theorem selStep1_drop_spec (e₀ : ℤ) (he₀ : 0 ≤ e₀) :
    ∀ (r : ℕ) (g : Graph k m), step1_eL g.comps = e₀ + r → DropSpec e₀ r g (selStep1_drop r g)
  | 0, g, h => show DropSpec e₀ 0 g g from
      ⟨Relation.ReflTransGen.refl, by simpa using h, by simp, rfl,
      List.Sublist.refl _, fun _ hd _ => hd, fun _ _ => Iff.rfl, id, id, rfl,
      fun _ _ _ _ _ _ _ _ => rfl, List.Perm.refl _⟩
  | r + 1, g, h => by
    obtain ⟨i₀, c₀, hc₀, hk₀, hr₀⟩ :=
      s1c_exists_red_of_pos (L := g.comps) (by push_cast at h; omega)
    obtain ⟨i, hi⟩ : ∃ i, selStep1_firstRed g.comps = some i := by
      rcases h' : selStep1_firstRed g.comps with _ | i
      · exact absurd hr₀ (selStep1_firstRed_none h' hc₀ hk₀)
      · exact ⟨i, rfl⟩
    obtain ⟨c, hc, hk, hr⟩ := selStep1_firstRed_some hi
    have hdrop : selStep1_drop (r + 1) g = selStep1_drop r ⟨g.comps.eraseIdx i, g.coeff⟩ := by
      simp only [selStep1_drop, hi]
    rw [hdrop]
    obtain ⟨hstep, he, hord, hmem, hb, hdc, hconn, hwt⟩ := step1_drop_one g hc hk hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
      selStep1_drop_spec e₀ he₀ r ⟨g.comps.eraseIdx i, g.coeff⟩ (by push_cast at h; omega)
    refine ⟨Relation.ReflTransGen.head hstep h1, h2, ?_, h4,
      h5.trans (List.eraseIdx_sublist _ _),
      fun d hd hdk => h6 d (hmem d hd hdk) hdk, fun u v => (h7 u v).trans (hb u v),
      fun hg => h8 (hdc hg), fun hg => h9 (hconn hg), h10.trans hwt, ?_, ?_⟩
    · push_cast
      linarith
    · intro hlab Ω ι _ _ PF D e
      rw [h11 (fun d hd hdk => hlab d (List.mem_of_mem_eraseIdx hd) hdk) Ω ι PF D e]
      exact step1_dropDot_value g hc hk hr hlab Ω ι PF D e
    · refine h12.trans ?_
      have hp := (perm_eraseIdx hc).filter (fun c => decide (c.kind ≠ .dot))
      rw [List.filter_cons_of_neg (by simp [hk])] at hp
      exact hp.symm

end SelDrop

/-! ## The clauses on the output graphs -/

section SelPhases

variable {k n : ℕ}

/-- The clauses `qStep1Out` without the error order: in the last alternative the scaling order
is at least that of `Γ` plus `d + 1`; with the components at the external atoms kept. -/
private def SelOut (C' d : ℕ) (X : Atom k n) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  t.QBase C' X Γ ∧ (∀ u, ¬ t.IsNew u) ∧
    ((t.g.Plain ∧ t.g.IsQFormAt (t.f X)) ∨ (Γ.ord + d + 1 ≤ t.g.ord ∧ t.g.Clean)) ∧
    (Γ.UnlabelledFreeAtBlock X → t.g.Plain → t.g.IsQFormAt (t.f X) →
      ¬ t.g.IsQGraphAt (t.f X) → Γ.ord + 1 ≤ t.g.ord ∧ t.QWitness X Γ) ∧ Step1OO1 Γ t

set_option maxHeartbeats 400000 in
-- The elaboration of this proof needs more than the default number of heartbeats.
/-- The last step: `O_merge`, then the removal of the redundant dotted edges, gives one output
graph with the clauses `SelOut`. -/
private theorem selStep1_final_out {d S C' : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Step1Base d S X Γ T) (hK : Step1OK1 Γ T)
    (hmin : ∀ c ∈ T.comps, c.minor = [])
    (hinv : ∀ c ∈ T.comps, c.kind.step1_isInvB = false)
    (hN2 : ∀ c ∈ T.comps, c.kind = .xdot → Step1HasS T.comps c.x c.y)
    (hcls : ClsQ X T ∨ ClsW d X Γ T) (hC : k + n + S ≤ C') :
    DExp (SelOut C' d X Γ) 1 T (selStep1_final T) := by
  -- `O_merge` applies
  have hsol : ∀ c ∈ T.comps, c.kind.isSolid = true → ¬ T.SameBlock c.x c.y := by
    intro c hc hk hb
    obtain ⟨-, d, hd, hdk, hdxy⟩ := hB.solid c hc hk
    apply hB.xapart d hd hdk
    rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hb
    · rw [h1, h2]; exact hb.symm
  obtain ⟨t, ht⟩ : ∃ t, T.mergeT = some t := by
    rcases hm : T.mergeT with _ | t
    · obtain ⟨c, hc, hk, hr⟩ := mergeT_none hm
      exact absurd ((T.mrep_eq_iff _ _).1 hr) (hB.xapart c hc hk)
    · exact ⟨t, rfl⟩
  have hs := s1c_mergeT_spec ht
  obtain ⟨hord, heL⟩ := hs.ord_eL hsol
  have hle := hs.removedDots_le hB.nonred hB.noloop
  have hlen : t.nOut ≤ n := hs.nOut_le
  set nr := (removedDots T t.f).length with hnr
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = (n : ℤ) - t.nOut - nr := ⟨(n - t.nOut - nr : ℕ), by omega⟩
  have he₀ : 0 ≤ step1_eL T.comps := s1c_eL_nonneg _
  have hEq : step1_eL t.g.comps = step1_eL T.comps + r := by rw [heL, hr]; ring
  have hdr : (step1_eL t.g.comps - step1_eL T.comps).toNat = r := by
    rw [hEq, add_sub_cancel_left]
    exact Int.toNat_natCast r
  obtain ⟨hch, hge, hgo, hgc, hsub, hmem', hblk, hdc, hconn, hwt, hval, hnd'⟩ :=
    selStep1_drop_spec (step1_eL T.comps) he₀ r t.g hEq
  set g' := selStep1_drop r t.g with hg'
  have hdotlab := dotlab_of_wf hB.wf
  -- the components of `g'`
  have hmc : ∀ c ∈ T.comps, c.kind ≠ .dot →
      step1_mergeComp T.step1_mrep t.f c = some (c.map t.f) := by
    intro c hc hk
    by_cases hks : c.kind.isSolid = true
    · exact mergeComp_of_solid hks fun h => hsol c hc hks ((T.mrep_eq_iff _ _).1 h)
    · exact mergeComp_other hk (by simpa using hks)
  have hin : ∀ c ∈ T.comps, c.kind ≠ .dot → c.map t.f ∈ g'.comps := by
    intro c hc hk
    exact hmem' _ (hs.mem_comps.2 ⟨c, hc, hmc c hc hk⟩) (by simpa [Comp.map] using hk)
  have hout : ∀ c' ∈ g'.comps, ∃ c ∈ T.comps, c' = c.map t.f ∧
      (c.kind = .dot → t.f c.x ≠ t.f c.y) := by
    intro c' hc'
    obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 (hsub.subset hc')
    by_cases hk : c.kind = .dot
    · rw [s1c_mergeComp_dot hk] at hm
      split_ifs at hm with hf
      exact ⟨c, hc, (Option.some.inj hm).symm, fun _ => hf⟩
    · rw [hmc c hc hk] at hm
      exact ⟨c, hc, (Option.some.inj hm).symm, fun h => absurd h hk⟩
  have hordg : g'.ord = T.ord := by
    rw [hgo, hord, hr]
    ring
  have hlab1 : T.labels.length ≤ 1 := labels_length_le hB.lab
  -- the output
  have hfin : selStep1_final T = [⟨t.nOut, g', t.f⟩] := by
    simp only [selStep1_final, ht, hdr, hg']
  rw [hfin]
  refine ⟨?_, by simp, ?_⟩
  · intro Ω ι _ _ PF D₀ _ e
    have hm := oMerge_value k n T hlab1 hdotlab Ω ι PF D₀ e
    rw [ht] at hm
    funext ω
    simp only [TExpansion.forget, Expansion.valR, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [hval (fun c hc hk => (hs.hlab hdotlab) c hc (Or.inl hk)) Ω ι PF D₀ e]
    exact congrFun hm ω
  intro t' ht'
  simp only [List.mem_singleton] at ht'
  subst ht'
  obtain ⟨φ, hφ, -⟩ := hs.f_inr
  have hXr : (t.f X).isRight = true := by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, X = .inr x₀ := by
      rcases hX : X with a | x₀
      · rw [hX] at hB; exact absurd hB.xright (by simp)
      · exact ⟨x₀, rfl⟩
    rw [hx₀, hφ]
    rfl
  -- shape facts of `g'`
  have hwf' : ∀ c' ∈ g'.comps, c'.WF := by
    intro c' hc'
    obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
    exact Comp.map_WF _ (hB.wf c hc)
  have hClean : g'.Clean := by
    intro c' hc'
    obtain ⟨c, hc, rfl, hdl⟩ := hout c' hc'
    refine ⟨by simp [Comp.map, hmin c hc], ?_, ?_, Comp.map_WF _ (hB.wf c hc)⟩
    · intro ch hch
      have := hinv c hc
      simp only [Comp.map] at hch
      rw [hch] at this
      simp [Kind.step1_isInvB] at this
    · intro hk
      exact hdl hk
  have hQF : g'.IsQFormAt (t.f X) := by
    obtain ⟨c, hc, hcl, -, hci⟩ := hB.labex
    have hk : c.kind ≠ .dot := by
      intro h
      rw [hdotlab c hc (Or.inl h)] at hcl
      cases hcl
    refine ⟨⟨c.map t.f, hin c hc hk, by simp [Comp.map, hcl]⟩, ?_⟩
    intro c' hc'
    obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
    rcases hB.lab c hc with h | h
    · left; simp [Comp.map, h]
    · right; simp [Comp.map, h]
  have hnew : ∀ u, ¬ Tracked.IsNew ⟨t.nOut, g', t.f⟩ u := by
    intro u hu
    obtain ⟨v, hv⟩ := hs.f_surj u
    exact hu v hv
  have hsb : ∀ u v, g'.SameBlock (t.f u) (t.f v) ↔ T.SameBlock u v :=
    fun u v => (hblk _ _).trans (hs.sameBlock_iff u v)
  have hcompX : ∀ (κ : Kind) (u v : Atom k n), Step1HasX T.comps u v →
      ∃ c' ∈ g'.comps, c'.kind = .xdot ∧
        (c'.x = t.f u ∧ c'.y = t.f v ∨ c'.x = t.f v ∧ c'.y = t.f u) := by
    intro _ u v ⟨c, hc, hk, hxy⟩
    refine ⟨c.map t.f, hin c hc (by rw [hk]; simp), hk, ?_⟩
    simp only [Comp.map]
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
    · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
  -- the clauses
  refine ⟨⟨?_, ?_, ?_, ?_, hXr, ?_, ?_⟩, hnew, ?_, ?_, final_oo1 hs hK hsub hnd'⟩
  · -- normal regular
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · have h1 : g'.comps.length ≤ t.g.comps.length := hsub.length_le
      have h2 : t.g.comps.length ≤ T.comps.length := by
        rw [hs.comps_eq]
        exact List.length_filterMap_le _ _
      have h3 : T.comps.length ≤ S := le_trans (by unfold step1_sizeΦ; omega) hB.size
      change k + t.nOut + g'.comps.length ≤ C'
      omega
    · intro u v
      have h := hconn (hs.connNoX hB.conn) u v
      obtain ⟨w⟩ := h
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons hadj _ ih =>
        refine SimpleGraph.Reachable.trans ?_ ih
        rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hadj
        refine SimpleGraph.Adj.reachable ?_
        rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
        obtain ⟨hne, ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩⟩ := hadj
        · exact ⟨hne, Or.inl ⟨c, hc, h1, h2⟩⟩
        · exact ⟨hne, Or.inr ⟨c, hc, h1, h2⟩⟩
    · intro a b
      rw [hwt]
      exact hs.internal hB.internal a b
    · intro c' hc' hk
      exact hs.noIntDot c' (hsub.subset hc') hk
    · intro c' hc' hk
      exact hs.solid_ne c' (hsub.subset hc') hk
    · intro u v _
      constructor
      · rintro ⟨c', hc', hk, hxy⟩
        obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
        obtain ⟨d, hd, hdk, hdxy⟩ := hN2 c hc hk
        refine ⟨d.map t.f, hin d hd (by intro h; rw [h] at hdk; simp [Kind.isSolid] at hdk),
          hdk, ?_⟩
        simp only [Comp.map] at hxy ⊢
        rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
      · rintro ⟨c', hc', hk, hxy⟩
        obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
        obtain ⟨-, d, hd, hdk, hdxy⟩ := hB.solid c hc hk
        refine ⟨d.map t.f, hin d hd (by rw [hdk]; simp), hdk, ?_⟩
        simp only [Comp.map] at hxy ⊢
        rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  · -- order
    rw [hordg]
    have := hB.ord
    have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * (step1_nWD T.comps : ℤ) := by positivity
    push_cast at *
    linarith
  · -- no `×`-dot inside a block
    intro c' hc' hk hb
    obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
    exact hB.xapart c hc hk ((hsb _ _).1 hb)
  · -- dot excess
    change step1_eL g'.comps ≤ step1_eL Γ.comps
    rw [hge, hB.excess]
  · -- doubly connected
    intro hdcΓ
    exact Graph.Step1DCS.doublyConnected (hdc (Graph.Step1DCS.mergeT (hB.dc hdcΓ) ht).1)
  · -- chain of elementary steps
    exact (hB.chain.tail (QElemStep.merge T t ht)).trans hch
  · -- output form
    by_cases hw : step1_nWD T.comps = 0
    · left
      refine ⟨?_, hQF⟩
      intro c' hc'
      obtain ⟨h1, h2, h3, h4⟩ := hClean c' hc'
      refine ⟨h1, h2, ?_, h3, h4⟩
      intro ch dd hk
      obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
      have : c ∈ T.comps.filter fun c => c.kind.isWDB := by
        simp only [List.mem_filter]
        exact ⟨hc, by simp only [Comp.map] at hk; rw [hk]; rfl⟩
      unfold step1_nWD at hw
      rw [List.length_eq_zero_iff] at hw
      rw [hw] at this
      simp at this
    · right
      refine ⟨?_, hClean⟩
      rw [hordg]
      have h1 := hB.ord
      have h2 : (1 : ℤ) ≤ step1_nWD T.comps := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hw
      nlinarith
  · -- the strict clause
    intro _ _ _ hnQ
    rcases hcls with hQ | ⟨⟨c, hc, hcl, hcr, u, hu, hj⟩, hord1⟩
    · exfalso
      apply hnQ
      refine ⟨hQF.1, ?_⟩
      intro c' hc' hrl
      obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
      simp only [Comp.map] at hrl ⊢
      rcases hrl with hr | hl
      · rw [hQ c hc hr]; rfl
      · rcases hB.lab c hc with h | h
        · rw [h] at hl; simp at hl
        · rw [h]; rfl
    · refine ⟨?_, c, hc, hcl, hcr, u, hu, ?_⟩
      · rw [hordg]
        have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * (step1_nWD T.comps : ℤ) := by positivity
        push_cast at *
        linarith
      · rcases hj with hb | ⟨e', he', hes, hel, hexy⟩
        · exact Or.inl ((hsb _ _).2 hb)
        · simp only [Tracked.self, id] at hexy
          refine Or.inr ⟨e'.map t.f,
            hin e' he' (by intro h; rw [h] at hes; simp [Kind.isSolid] at hes),
            hes, by simp only [Comp.map, hel]; rfl, ?_⟩
          simp only [Comp.map]
          rcases hexy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
          · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

open Classical in
/-- The phase of the `×`-dotted edges without solid edge, then the last step. -/
private theorem selStep1_clean_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n}
    (hC : k + n + S ≤ C') :
    ∀ (m : ℕ) (T : Graph k n), nBad T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      (ClsQ X T ∨ ClsW d X Γ T) → DExp (SelOut C' d X Γ) (2 ^ m) T (selStep1_clean m T) := by
  have hfin : ∀ T : Graph k n, Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      (ClsQ X T ∨ ClsW d X Γ T) → (∀ c ∈ T.comps, badB T.comps c = false) →
      DExp (SelOut C' d X Γ) 1 T (selStep1_final T) := by
    intro T hB hK hmin hinv hcls hnb
    refine selStep1_final_out hB hK hmin hinv ?_ hcls hC
    intro c hc hk
    by_contra hns
    have := hnb c hc
    simp only [badB, hk, decide_true, Bool.true_and, Bool.not_eq_false'] at this
    rw [← solidJoinB_iff] at hns
    exact hns this
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hmin hinv hcls
    simp only [selStep1_clean]
    refine (hfin T hB hK hmin hinv hcls fun c hc => ?_).mono (by simp)
    by_contra h
    have : c ∈ T.comps.filter (badB T.comps) := List.mem_filter.2 ⟨hc, by simpa using h⟩
    have := List.length_pos_of_mem this
    unfold nBad at hm
    omega
  | succ m ih =>
    intro T hm hB hK hmin hinv hcls
    rcases hf : T.comps.findIdx? (badB T.comps) with _ | i
    · simp only [selStep1_clean, hf]
      exact (hfin T hB hK hmin hinv hcls (List.findIdx?_eq_none_iff.1 hf)).mono
        Nat.one_le_two_pow
    · obtain ⟨c, hc, hcb⟩ := selStep1_findIdx_some hf
      obtain ⟨hE, hv, -, hG⟩ := selStep1_clean_step hB hK hmin hinv hcls hc hcb
      simp only [selStep1_clean, hf]
      rw [hE, selStep1_bind_self]
      have h2m : 2 ^ (m + 1) = [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
          ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].length * 2 ^ m := by
        simp [pow_succ, mul_comm]
      rw [h2m]
      refine DExp.bind _ (fun g => if g.XdotApart then selStep1_clean m g else []) hv
        fun g hg => ?_
      obtain ⟨hlab, hgood⟩ := hG g hg
      by_cases hxa : g.XdotApart
      · obtain ⟨hB', hK', hmin', hinv', hcls', hbad⟩ := hgood hxa
        simp only [ite_eq_left hxa]
        exact ih g (by omega) hB' hK' hmin' hinv' hcls'
      · simp only [ite_eq_right hxa]
        exact DExp.nil _ (step1_valR_eq_zero g hlab hxa)

/-- The phase of [II, (4.21)], then the phase of the `×`-dotted edges without solid edge. -/
private theorem selStep1_taylor_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n}
    (hC : k + n + S ≤ C') :
    ∀ (m : ℕ) (T : Graph k n), nInv T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (ClsQ X T ∨ ClsW d X Γ T) →
      DExp (SelOut C' d X Γ) ((d + 2) ^ m * 2 ^ S) T (selStep1_taylor d m T) := by
  have hcl : ∀ (m : ℕ) (T : Graph k n), Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      (ClsQ X T ∨ ClsW d X Γ T) →
      DExp (SelOut C' d X Γ) ((d + 2) ^ m * 2 ^ S) T (selStep1_clean (nBad T.comps) T) := by
    intro m T hB hK hmin hinv hcls
    have hbad : nBad T.comps ≤ S :=
      le_trans (List.length_filter_le _ _) (le_trans (by unfold step1_sizeΦ; omega) hB.size)
    refine (selStep1_clean_out hC _ T le_rfl hB hK hmin hinv hcls).mono ?_
    calc 2 ^ nBad T.comps ≤ 2 ^ S := Nat.pow_le_pow_right (by omega) hbad
      _ ≤ (d + 2) ^ m * 2 ^ S := Nat.le_mul_of_pos_left _ (by positivity)
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hmin hcls
    have hinv : ∀ c ∈ T.comps, c.kind.step1_isInvB = false := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => c.kind.step1_isInvB :=
        List.mem_filter.2 ⟨hc, by simpa using h⟩
      have := List.length_pos_of_mem this
      unfold nInv at hm
      omega
    simp only [selStep1_taylor]
    exact hcl 0 T hB hK hmin hinv hcls
  | succ m ih =>
    intro T hm hB hK hmin hcls
    rcases hf : T.comps.findIdx? (fun c => c.kind.step1_isInvB) with _ | i
    · simp only [selStep1_taylor, hf]
      exact hcl (m + 1) T hB hK hmin (List.findIdx?_eq_none_iff.1 hf) hcls
    · obtain ⟨c, hc, hci⟩ := selStep1_findIdx_some hf
      obtain ⟨Gs, hE, hlen, hv, hGs⟩ := selStep1_taylor_step hB hK hmin hcls hc hci
      simp only [selStep1_taylor, hf]
      rw [hE, selStep1_bind_self]
      have hpow : (d + 2) ^ (m + 1) * 2 ^ S = Gs.length * ((d + 2) ^ m * 2 ^ S) := by
        rw [hlen]; ring
      rw [hpow]
      refine DExp.bind Gs (fun g => selStep1_taylor d m g) hv fun g hg => ?_
      obtain ⟨hB', hK', hmin', hcls', hcnt⟩ := hGs g hg
      exact ih g (by omega) hB' hK' hmin' hcls'

/-- The phase of [II, (4.20)], then the phase of [II, (4.21)]. -/
private theorem selStep1_rev_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n}
    (hC : k + n + S ≤ C') :
    ∀ (m : ℕ) (T : Graph k n), nMin T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      (ClsQ X T ∨ ClsW d X Γ T) →
      DExp (SelOut C' d X Γ) (2 ^ m * ((d + 2) ^ S * 2 ^ S)) T (selStep1_rev d m X T) := by
  have hta : ∀ (m : ℕ) (T : Graph k n), Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (ClsQ X T ∨ ClsW d X Γ T) →
      DExp (SelOut C' d X Γ) (2 ^ m * ((d + 2) ^ S * 2 ^ S)) T
        (selStep1_taylor d (nInv T.comps) T) := by
    intro m T hB hK hmin hcls
    have hinv : nInv T.comps ≤ S :=
      le_trans (List.length_filter_le _ _) (le_trans (by unfold step1_sizeΦ; omega) hB.size)
    refine (selStep1_taylor_out hC _ T le_rfl hB hK hmin hcls).mono ?_
    calc (d + 2) ^ nInv T.comps * 2 ^ S ≤ (d + 2) ^ S * 2 ^ S :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hinv)
      _ ≤ 2 ^ m * ((d + 2) ^ S * 2 ^ S) := Nat.le_mul_of_pos_left _ (by positivity)
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hcls
    have hmin : ∀ c ∈ T.comps, c.minor = [] := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => !c.minor.isEmpty :=
        List.mem_filter.2 ⟨hc, by simpa [List.isEmpty_iff] using h⟩
      have := List.length_pos_of_mem this
      unfold nMin at hm
      omega
    simp only [selStep1_rev]
    exact hta 0 T hB hK hmin hcls
  | succ m ih =>
    intro T hm hB hK hcls
    rcases hf : T.comps.findIdx? (fun c => !c.minor.isEmpty) with _ | i
    · have hmin : ∀ c ∈ T.comps, c.minor = [] := by
        intro c hc
        have := List.findIdx?_eq_none_iff.1 hf c hc
        simpa [List.isEmpty_iff] using this
      simp only [selStep1_rev, hf]
      exact hta (m + 1) T hB hK hmin hcls
    · obtain ⟨c, hc, hcm⟩ := selStep1_findIdx_some hf
      have hcT : c ∈ T.comps := List.mem_of_getElem? hc
      have hmX : c.minor = [X] := by
        rcases hB.minor c hcT with h | ⟨h, -⟩
        · rw [h] at hcm; simp at hcm
        · exact h
      obtain ⟨Gs, hE, hlen, hv, hGs⟩ := selStep1_rev_step hB hK hcls hc hmX
      simp only [selStep1_rev, hf]
      rw [hE, selStep1_bind_self]
      have hpow : 2 ^ (m + 1) * ((d + 2) ^ S * 2 ^ S) =
          Gs.length * (2 ^ m * ((d + 2) ^ S * 2 ^ S)) := by
        rw [hlen]; ring
      rw [hpow]
      refine DExp.bind Gs (fun g => selStep1_rev d m X g) hv fun g hg => ?_
      obtain ⟨⟨hB', hcls', hmin', -⟩, hK'⟩ := hGs g hg
      exact ih g (by omega) hB' hK' hcls'

/-- The move of the factors with minor `{X}` into the label group, then the phase of
[II, (4.20)]. -/
private theorem selStep1_absorb_out {d S C' : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hC : k + n + S ≤ C') (hB : Step1Base d S X Γ T) (hK : Step1OK1 Γ T)
    (hnp : nPend X T.comps = 0) (hcls : ClsW d X Γ T ∨ AllPend X T) :
    DExp (SelOut C' d X Γ) (2 ^ S * ((d + 2) ^ S * 2 ^ S)) T (selStep1_absorb d X T) := by
  unfold selStep1_absorb
  by_cases hA : AllPend X T
  · rw [ite_eq_left hA]
    obtain ⟨hB', hQ, hv⟩ := absorb_step hB hnp hA
    have h := DExp.bind [T.absorb (.Q, X)]
      (fun g => selStep1_rev d (nMin g.comps) X g) hv fun g hg => by
        rw [List.mem_singleton.1 hg]
        exact (selStep1_rev_out hC _ _ le_rfl hB' (hK.absorb X) (Or.inl hQ)).mono
          (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (nMin_le_S hB')))
    simpa using h
  · rw [ite_eq_right hA]
    exact (selStep1_rev_out hC _ _ le_rfl hB hK (Or.inr (hcls.resolve_right hA))).mono
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (nMin_le_S hB)))

/-- The phase of [II, (4.17)], then the move into the label group and the phase of
[II, (4.20)]. -/
private theorem selStep1_schur_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n} (hΓ : Γ.Plain)
    (hC : k + n + S ≤ C') :
    ∀ (m : ℕ) (T : Graph k n), nPend X T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      PendInv X Γ T → (ClsW d X Γ T ∨ AllPend X T) →
      DExp (SelOut C' d X Γ) (2 ^ m * (2 ^ S * ((d + 2) ^ S * 2 ^ S))) T
        (selStep1_schur d m X T) := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hP hcls
    simp only [selStep1_schur]
    simpa using selStep1_absorb_out hC hB hK (by omega) hcls
  | succ m ih =>
    intro T hm hB hK hP hcls
    rcases hf : T.comps.findIdx? (pendB X) with _ | i
    · have hnp : nPend X T.comps = 0 := by
        unfold nPend
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c hc
        simp [List.findIdx?_eq_none_iff.1 hf c hc]
      simp only [selStep1_schur, hf]
      exact (selStep1_absorb_out hC hB hK hnp hcls).mono
        (Nat.le_mul_of_pos_left _ (by positivity))
    · obtain ⟨c, hc, hcp⟩ := selStep1_findIdx_some hf
      obtain ⟨Gs, hE, hlen, hv, hGs⟩ := selStep1_schur_step hΓ hB hK hP hcls hc hcp
      simp only [selStep1_schur, hf]
      rw [hE, selStep1_bind_self]
      have hpow : 2 ^ (m + 1) * (2 ^ S * ((d + 2) ^ S * 2 ^ S)) =
          Gs.length * (2 ^ m * (2 ^ S * ((d + 2) ^ S * 2 ^ S))) := by
        rw [hlen]; ring
      rw [hpow]
      refine DExp.bind Gs (fun g => selStep1_schur d m X g) hv fun g hg => ?_
      obtain ⟨⟨hB', hP', hcls', hp'⟩, hK'⟩ := hGs g hg
      exact ih g (by omega) hB' hK' hP' hcls'

open Classical in
/-- The splits of the atoms of `Γ₀` against `X`, then the phase of [II, (4.17)]. -/
private theorem selStep1_split_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n} (hΓ : Γ.Plain)
    (hfree : Γ.UnlabelledFreeAtBlock X) (hC : k + n + S ≤ C') :
    ∀ (us : List (Atom k n)) (T : Graph k n),
      Step1Base d S X Γ T → Step1OK1 Γ T → step1_sizeΦ d X T.comps + us.length ≤ S →
      step1_dg T.comps = step1_dg Γ.comps →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      AllPend X T →
      (∀ c ∈ T.comps, pendB X c = true →
        c ∈ Γ.comps ∧ ∀ u ∈ [c.x, c.y], Step1HasX T.comps u X ∨ u ∈ us) →
      (∀ u ∈ us, ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧ u ∈ [c.x, c.y]) →
      DExp (SelOut C' d X Γ) (2 ^ us.length * (2 ^ S * (2 ^ S * ((d + 2) ^ S * 2 ^ S)))) T
        (selStep1_split d X us T)
  | [], T, hB, hK, _, _, _, _, hA, hP, _ => by
    have hP' : PendInv X Γ T := by
      intro c hc hp
      obtain ⟨h1, h2⟩ := hP c hc hp
      refine ⟨h1, ?_, ?_⟩
      · rcases h2 c.x (by simp) with h | h
        · exact h
        · simp at h
      · rcases h2 c.y (by simp) with h | h
        · exact h
        · simp at h
    simp only [selStep1_split]
    refine (selStep1_schur_out hΓ hC _ T le_rfl hB hK hP' (Or.inr hA)).mono ?_
    simp only [List.length_nil, pow_zero, one_mul]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (nPend_le_S hB))
  | u :: us, T, hB, hK, hsz, hdg, hmin, hinv, hA, hP, hus => by
    obtain ⟨c₀, hc₀, hl₀, hr₀, hu₀⟩ := hus u (List.mem_cons_self ..)
    have hBsz : step1_sizeΦ d X T.comps + 1 ≤ S := by
      simp only [List.length_cons] at hsz
      omega
    obtain ⟨-, hv, hlab₁, hgood₁, hB₂, hK₂, hdg₂⟩ :=
      selStep1_split_step hfree hB hK hBsz hdg hc₀ hl₀ hr₀ hu₀
    set B' := 2 ^ S * (2 ^ S * ((d + 2) ^ S * 2 ^ S)) with hB'def
    have hX : ∀ v w, Step1HasX T.comps v w → Step1HasX (T.comps ++ [mkC .xdot u X]) v w :=
      fun v w h => hasX_mono (fun d hd => List.mem_append_left _ hd) h
    -- the term with `u ≠ X`
    have h₂ := selStep1_split_out hΓ hfree hC us _ hB₂ hK₂ ?_ hdg₂ ?_ ?_ ?_ ?_
      (fun v hv => hus v (List.mem_cons_of_mem _ hv))
    · simp only [selStep1_split]
      refine (DExp.append (B₁ := B') hv ?_ h₂).mono ?_
      · -- the term with `u` identified with `X`
        by_cases hxa : (⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n).XdotApart
        · rw [ite_eq_left hxa]
          obtain ⟨hB₁, hK₁, hcls⟩ := hgood₁ hxa
          refine (selStep1_clean_out hC _ _ le_rfl hB₁ hK₁ ?_ ?_ (Or.inr hcls)).mono ?_
          · intro d hd
            rcases List.mem_append.1 hd with h | h
            · exact hmin d h
            · rw [List.mem_singleton.1 h]; rfl
          · intro d hd
            rcases List.mem_append.1 hd with h | h
            · exact hinv d h
            · rw [List.mem_singleton.1 h]; rfl
          · calc 2 ^ nBad (T.comps ++ [mkC .dot u X]) ≤ 2 ^ S :=
                Nat.pow_le_pow_right (by omega) (nBad_le_S hB₁)
              _ ≤ B' := by
                rw [hB'def]
                exact Nat.le_mul_of_pos_right _ (by positivity)
        · rw [ite_eq_right hxa]
          exact DExp.nil _ (step1_valR_eq_zero _ hlab₁ hxa)
      · have := Nat.one_le_two_pow (n := us.length)
        rw [List.length_cons, pow_succ]
        nlinarith
    · rw [sizeΦ_append_xdot _ (Or.inr rfl)]
      simp only [List.length_cons] at hsz
      omega
    · intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact hmin d h
      · rw [List.mem_singleton.1 h]; rfl
    · intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact hinv d h
      · rw [List.mem_singleton.1 h]; rfl
    · intro d hd hdl hdr
      rcases List.mem_append.1 hd with h | h
      · exact hA d h hdl hdr
      · rw [List.mem_singleton.1 h] at hdr; simp [mkC, Kind.isRandom] at hdr
    · intro d hd hdp
      rcases List.mem_append.1 hd with h | h
      · obtain ⟨h1, h2⟩ := hP d h hdp
        refine ⟨h1, fun v hv => ?_⟩
        rcases h2 v hv with h3 | h3
        · exact Or.inl (hX _ _ h3)
        · rcases List.mem_cons.1 h3 with rfl | h4
          · exact Or.inl ⟨mkC .xdot v X, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
          · exact Or.inr h4
      · rw [List.mem_singleton.1 h] at hdp; simp [pendB, mkC, Kind.isRandom] at hdp

end SelPhases

/-! ## The clauses of [II, Lemma 4.11] for the run -/

section SelMain

/-- **[II, Lemma 4.11]** for the run `selStep1`: for all `k`, `C`, `e` there are `K`, `C'` such
that for every normal regular graph `Γ = Γ₀ Q_x(Γ̃₀)` with bound `C` (`x` internal) and every
Taylor degree `d ≤ e`, the run has at most `K` terms and the value of `Γ`, and every output graph
`t` has the clauses `qStep1Out D C'` for every error order `D ≤ ord Γ + d`, keeps the components
at the external atoms at which all components of `Γ` are diffusive, and, if it is not of the form
`Γ_ω Q_x(Γ̃_ω)` without labels other than `Q_x`, has no `G^{(T)}`, `(G_{xx})⁻¹` or dotted loop and
a paper scaling order at least that of `Γ` plus `d + 1`. -/
theorem selStep1_clauses (k C e : ℕ) :
    ∃ K C' : ℕ, ∀ (n₀ : ℕ) (x₀ : Fin n₀) (Γ : Graph k n₀) (d : ℕ), d ≤ e →
      Γ.Normal C → Γ.IsQFormAt (.inr x₀) → Γ.Plain →
      (selStep1 d (.inr x₀) Γ).length ≤ K ∧ (selStep1 d (.inr x₀) Γ).ValueEq Γ modelAdm ∧
      ∀ t ∈ selStep1 d (.inr x₀) Γ,
        (∀ D : ℕ, (D : ℤ) ≤ Γ.ord + d → qStep1Out D C' (.inr x₀) Γ t) ∧ Step1OO1 Γ t ∧
        (¬ (t.g.Plain ∧ t.g.IsQFormAt (t.f (.inr x₀))) →
          t.g.Clean ∧ Γ.paperOrd + d + 1 ≤ t.g.paperOrd) := by
  set S := (e + 6) * C + 1 with hSdef
  refine ⟨2 ^ (2 * C) * (2 ^ S * (2 ^ S * ((e + 2) ^ S * 2 ^ S))), C + S, ?_⟩
  intro n₀ x Γ d hde hN hQ hP
  set X : Atom k n₀ := .inr x with hXdef
  suffices h : DExp (SelOut (C + S) d X Γ)
      (2 ^ (2 * C) * (2 ^ S * (2 ^ S * ((e + 2) ^ S * 2 ^ S)))) Γ (selStep1 d X Γ) by
    obtain ⟨hv, hlen, hall⟩ := h
    refine ⟨hlen, hv, fun t ht => ?_⟩
    obtain ⟨hbase, hnew, hform, hstrict, hoo⟩ := hall t ht
    refine ⟨fun D hD => ⟨hbase, hnew, ?_, hstrict⟩, hoo, fun hn => ?_⟩
    · rcases hform with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by linarith, h2⟩
    · rcases hform with h | ⟨h1, h2⟩
      · exact absurd h hn
      · refine ⟨h2, ?_⟩
        have hex := hbase.2.2.2.1
        unfold Graph.paperOrd
        linarith
  have hdotlab : ∀ d ∈ Γ.comps, (d.kind = .dot ∨ d.kind = .xdot) → d.label = none :=
    dotlab_of_wf fun c hc => (hP c hc).2.2.2.2
  have hsize := hN.1.size
  have hC : k + n₀ + S ≤ C + S := by omega
  -- a graph with a `×`-dotted edge inside a block has value `0`
  by_cases hxa : Γ.XdotApart
  swap
  · rw [selStep1, ite_eq_right hxa]
    exact DExp.nil _ (step1_valR_eq_zero Γ hdotlab hxa)
  -- the size bound at the input
  have hlenΓ : Γ.comps.length ≤ C := by omega
  have hminΓ : nMin Γ.comps = 0 := by
    unfold nMin
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp [(hP c hc).1]
  have hinvΓ : nInv Γ.comps = 0 := by
    unfold nInv
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have := (hP c hc).2.1
    revert this
    cases c.kind <;> simp [Kind.step1_isInvB]
  have hΦ : step1_sizeΦ d X Γ.comps ≤ (e + 4) * C := by
    have hpendΓ : nPend X Γ.comps ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
    unfold step1_sizeΦ
    rw [hminΓ, hinvΓ]
    have h1 : (d + 3) * (nPend X Γ.comps + 0) ≤ (e + 3) * C :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  by_cases hfree : Γ.UnlabelledFreeAtBlock X
  swap
  · -- `Γ₀` is attached to the block of `x`: the graph itself
    rw [selStep1, ite_eq_left hxa, ite_eq_right hfree]
    refine ⟨?_, ?_, ?_⟩
    · intro Ω ι _ _ PF D₀ _ e
      funext ω
      simp [TExpansion.forget, Expansion.valR, Tracked.self]
    · simp only [List.length_singleton]
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      refine ⟨⟨?_, le_refl _, hxa, le_refl _, rfl, id, Relation.ReflTransGen.refl⟩,
        fun u hu => hu u rfl, Or.inl ⟨hP, hQ⟩, fun h => absurd h hfree, Step1OO1.self Γ⟩
      exact ⟨⟨by have := hN.1.size; change k + n₀ + Γ.comps.length ≤ C + S; omega,
        hN.1.connected, hN.1.internal, hN.1.noIntDot⟩, hN.2.1, hN.2.2⟩
  -- the main case
  rw [selStep1, ite_eq_left hxa, ite_eq_left hfree]
  set R := Γ.comps.filter fun c => c.label.isNone && c.kind.isRandom with hR
  have hus : selStep1_us Γ = R.flatMap fun c => [c.x, c.y] := rfl
  have hlenus : (selStep1_us Γ).length ≤ 2 * C := by
    have h1 : (selStep1_us Γ).length = 2 * R.length := by
      rw [hus, List.length_flatMap]
      simp only [List.length_cons, List.length_nil]
      induction R with
      | nil => simp
      | cons a l ih => simp; ring
    have h2 : R.length ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
    omega
  have hB := base_init (D' := d) (S := S) hN hQ hP hxa rfl
    (by have : (e + 4) * C ≤ S := by rw [hSdef]; nlinarith
        omega)
  have hE := selStep1_split_out hP hfree hC (selStep1_us Γ) Γ hB (Step1OK1.refl Γ)
    (by have : (e + 4) * C + 2 * C ≤ S := by rw [hSdef]; nlinarith
        omega) rfl
    (fun c hc => (hP c hc).1)
    (fun c hc => by have := (hP c hc).2.1; revert this; cases c.kind <;> simp [Kind.step1_isInvB])
    ?_ ?_ ?_
  · refine hE.mono (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hlenus) ?_)
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_))
    exact Nat.pow_le_pow_left (by omega) S
  · intro c hc hl hr
    left
    have hcx := (hfree c hc hl hr).1
    have hcy := (hfree c hc hl hr).2
    have hx : c.x ≠ X := fun h => hcx (by rw [h]; exact SimpleGraph.Reachable.refl _)
    have hy : c.y ≠ X := fun h => hcy (by rw [h]; exact SimpleGraph.Reachable.refl _)
    simp [pendB, hl, hr, (hP c hc).1, hx, hy]
  · intro c hc hp
    refine ⟨hc, fun u hu => Or.inr ?_⟩
    rw [hus, List.mem_flatMap]
    refine ⟨c, ?_, hu⟩
    rw [hR, List.mem_filter]
    simp only [pendB, Bool.and_eq_true] at hp
    exact ⟨hc, by simp only [Bool.and_eq_true]; exact ⟨hp.1.1.1.1, hp.1.1.1.2⟩⟩
  · intro u hu
    rw [hus, List.mem_flatMap] at hu
    obtain ⟨c, hcR, hu⟩ := hu
    rw [hR, List.mem_filter] at hcR
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hcR
    exact ⟨c, hcR.1, hcR.2.1, hcR.2.2, hu⟩

end SelMain

section SelInstances

end SelInstances

end RBM8D.Graphs
