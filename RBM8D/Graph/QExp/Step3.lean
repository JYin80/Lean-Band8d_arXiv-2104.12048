import RBM8D.Graph.QExp.Step1

/-!
# The third step of the `Q`-expansions

[II, Lemma 4.14].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Connected components of simple graphs -/

section GraphCard

variable {V W : Type*}

/-- Reachability in a graph with one more edge `u v`. -/
theorem reach_add_edge_iff {G H : SimpleGraph V} {u v : V}
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
theorem card_cc_add_edge [Finite V] {G H : SimpleGraph V} {u v : V}
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
theorem card_cc_of_map [Finite V] {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W)
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
theorem card_cc_of_reach_iff [Finite V] {G H : SimpleGraph V}
    (hr : ∀ a b, H.Reachable a b ↔ G.Reachable a b) :
    Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent :=
  card_cc_of_map id Function.surjective_id hr

/-- A map onto `W` constant on the connected components bounds `Nat.card W`. -/
theorem card_le_card_cc [Finite V] {G : SimpleGraph V} (f : V → W)
    (hf : Function.Surjective f) (hc : ∀ a b, G.Reachable a b → f a = f b) :
    Nat.card W ≤ Nat.card G.ConnectedComponent := by
  let φ : G.ConnectedComponent → W := Quot.lift f fun a b h => hc a b h
  refine Nat.card_le_card_of_surjective φ ?_
  intro w
  obtain ⟨a, rfl⟩ := hf w
  exact ⟨G.connectedComponentMk a, rfl⟩

/-- The graph without edges has one connected component per vertex. -/
theorem card_cc_bot [Finite V] :
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
def step3_dg (L : List (Comp (Atom k n))) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ L, c.kind = .dot ∧ c.x = u ∧ c.y = v

/-- The number of dotted components of a list. -/
def step3_nD (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => decide (c.kind = .dot)).length

/-- The dot excess of a list of components. -/
def step3_eL (L : List (Comp (Atom k n))) : ℤ :=
  (step3_nD L : ℤ) - ((k + n : ℕ) : ℤ) + (Nat.card (step3_dg L).ConnectedComponent : ℤ)

theorem step3_dg_adj {L : List (Comp (Atom k n))} {a b : Atom k n} :
    (step3_dg L).Adj a b ↔ a ≠ b ∧ ∃ c ∈ L, c.kind = .dot ∧ (c.x = a ∧ c.y = b ∨ c.x = b ∧ c.y = a) := by
  simp only [step3_dg, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact ⟨h, c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨h, c, hc, hk, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨h, c, hc, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact ⟨h, Or.inr ⟨c, hc, hk, rfl, rfl⟩⟩

/-- The ends of a dotted component are reachable. -/
theorem step3_dg_reach_of_mem {L : List (Comp (Atom k n))} {c : Comp (Atom k n)} (hc : c ∈ L)
    (hk : c.kind = .dot) : (step3_dg L).Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (step3_dg_adj.2 ⟨h, c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩).reachable

/-- Reachability in the graph of dotted components is monotone in the dotted components. -/
theorem dg_reach_mono {L L' : List (Comp (Atom k n))}
    (h : ∀ c ∈ L, c.kind = .dot → c ∈ L') {a b : Atom k n} (hr : (step3_dg L).Reachable a b) :
    (step3_dg L').Reachable a b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨hne, c, hc, hk, hxy⟩ := step3_dg_adj.1 hadj
    refine SimpleGraph.Reachable.trans ?_ ih
    exact (step3_dg_adj.2 ⟨hne, c, h c hc hk, hk, hxy⟩).reachable

/-- The graph of dotted components depends only on the dotted components. -/
theorem dg_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ c, c.kind = .dot → (c ∈ L ↔ c ∈ L')) : step3_dg L = step3_dg L' := by
  ext a b
  rw [step3_dg_adj, step3_dg_adj]
  constructor
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).1 hc, hk, hxy⟩
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).2 hc, hk, hxy⟩

theorem dg_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step3_dg L = step3_dg L' :=
  dg_congr fun _ _ => h.mem_iff

theorem step3_nD_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step3_nD L = step3_nD L' :=
  (h.filter _).length_eq

theorem eL_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step3_eL L = step3_eL L' := by
  simp only [step3_eL, step3_nD_perm h, dg_perm h]

/-- Two lists with the same dotted components, with multiplicity, have the same graph of dotted
components and the same dot excess. -/
theorem dg_eL_of_filter_perm {L L' : List (Comp (Atom k n))}
    (h : (L.filter fun c => decide (c.kind = .dot)).Perm
      (L'.filter fun c => decide (c.kind = .dot))) :
    step3_dg L = step3_dg L' ∧ step3_eL L = step3_eL L' := by
  have hg : step3_dg L = step3_dg L' := by
    apply dg_congr
    intro c hk
    have := h.mem_iff (a := c)
    simp only [List.mem_filter, hk, decide_true, and_true] at this
    exact this
  refine ⟨hg, ?_⟩
  simp only [step3_eL, step3_nD, h.length_eq, hg]

theorem dg_nil : step3_dg ([] : List (Comp (Atom k n))) = ⊥ := by
  ext a b
  simp [step3_dg_adj]

theorem dg_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : step3_dg (c :: L) = step3_dg L := by
  apply dg_congr
  intro d hd
  simp only [List.mem_cons]
  constructor
  · rintro (rfl | h)
    · exact absurd hd hk
    · exact h
  · exact Or.inr

theorem dg_cons_dot_adj {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (a b : Atom k n) :
    (step3_dg (c :: L)).Adj a b ↔ (step3_dg L).Adj a b ∨ (a ≠ b ∧ (a = c.x ∧ b = c.y ∨ a = c.y ∧ b = c.x)) := by
  rw [step3_dg_adj, step3_dg_adj]
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

theorem step3_nD_cons (c : Comp (Atom k n)) (L : List (Comp (Atom k n))) :
    step3_nD (c :: L) = step3_nD L + if c.kind = .dot then 1 else 0 := by
  unfold step3_nD
  by_cases h : c.kind = .dot
  · rw [List.filter_cons_of_pos (by simp [h])]
    simp [h]
  · rw [List.filter_cons_of_neg (by simp [h])]
    simp [h]

theorem eL_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : step3_eL (c :: L) = step3_eL L := by
  simp [step3_eL, step3_nD_cons, hk, dg_cons_nondot L hk]

/-- A dotted component between two blocks keeps the dot excess. -/
theorem eL_cons_dot_new {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : ¬ (step3_dg L).Reachable c.x c.y) : step3_eL (c :: L) = step3_eL L := by
  have h := card_cc_add_edge (G := step3_dg L) (H := step3_dg (c :: L)) (dg_cons_dot_adj L hk) hr
  simp only [step3_eL, step3_nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- Reachability is unchanged by a dotted component whose ends are reachable. -/
theorem dg_reach_cons_red {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : (step3_dg L).Reachable c.x c.y) (a b : Atom k n) :
    (step3_dg (c :: L)).Reachable a b ↔ (step3_dg L).Reachable a b := by
  rw [reach_add_edge_iff (dg_cons_dot_adj L hk)]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h
    · exact (h1.trans hr).trans h2
    · exact (h1.trans hr.symm).trans h2
  · exact Or.inl

/-- A dotted component whose ends are already in one block raises the dot excess by `1`. -/
theorem eL_cons_dot_red {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : (step3_dg L).Reachable c.x c.y) : step3_eL (c :: L) = step3_eL L + 1 := by
  have h := card_cc_of_reach_iff (G := step3_dg L) (H := step3_dg (c :: L)) (dg_reach_cons_red L hk hr)
  simp only [step3_eL, step3_nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- Every dotted component is needed: its ends are not joined by the other dotted components. -/
def Step3NonRed (L : List (Comp (Atom k n))) : Prop :=
  ∀ (c : Comp (Atom k n)) (L' : List (Comp (Atom k n))), L.Perm (c :: L') → c.kind = .dot →
    ¬ (step3_dg L').Reachable c.x c.y

theorem nonRed_tail {c : Comp (Atom k n)} {L : List (Comp (Atom k n))}
    (h : Step3NonRed (c :: L)) : Step3NonRed L := by
  intro d L' hp hk hr
  apply h d (c :: L') ((hp.cons c).trans (List.Perm.swap d c L')) hk
  exact dg_reach_mono (fun e he _ => List.mem_cons_of_mem _ he) hr

theorem card_atom : Nat.card (Atom k n) = k + n := by
  simp

/-- When every dotted component is needed, the dot excess is `0`. -/
theorem step3_eL_eq_zero_of_nonRed : ∀ {L : List (Comp (Atom k n))}, Step3NonRed L → step3_eL L = 0
  | [], _ => by
    simp only [step3_eL, step3_nD, List.filter_nil, List.length_nil, dg_nil, card_cc_bot, card_atom]
    push_cast
    ring
  | c :: L, h => by
    have ih := step3_eL_eq_zero_of_nonRed (nonRed_tail h)
    by_cases hk : c.kind = .dot
    · rw [eL_cons_dot_new L hk (h c L (List.Perm.refl _) hk), ih]
    · rw [eL_cons_nondot L hk, ih]

/-- A list with positive dot excess has a dotted component whose ends are joined by the others. -/
theorem step3_exists_red_of_pos {L : List (Comp (Atom k n))} (h : 0 < step3_eL L) :
    ∃ (i : ℕ) (c : Comp (Atom k n)), L[i]? = some c ∧ c.kind = .dot ∧
      (step3_dg (L.eraseIdx i)).Reachable c.x c.y := by
  by_contra hc
  push Not at hc
  have hn : Step3NonRed L := by
    intro c L' hp hk hr
    have hcL : c ∈ L := hp.symm.subset (List.mem_cons_self ..)
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.1 hcL
    have hp' : (L.eraseIdx i).Perm L' := by
      have h1 := List.getElem_cons_eraseIdx_perm hi
      rw [hci] at h1
      exact (h1.trans hp).cons_inv
    exact hc i c (by rw [List.getElem?_eq_getElem hi, hci]) hk (by rw [dg_perm hp']; exact hr)
  have := step3_eL_eq_zero_of_nonRed hn
  omega

/-- Removing a dotted component whose ends are joined by the others lowers the dot excess by
`1` and keeps the blocks. -/
theorem eL_eraseIdx_red {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) (hk : c.kind = .dot) (hr : (step3_dg (L.eraseIdx i)).Reachable c.x c.y) :
    step3_eL (L.eraseIdx i) + 1 = step3_eL L ∧
      ∀ a b, (step3_dg (L.eraseIdx i)).Reachable a b ↔ (step3_dg L).Reachable a b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  have hp := List.getElem_cons_eraseIdx_perm hi
  refine ⟨?_, fun a b => ?_⟩
  · rw [← eL_perm hp, eL_cons_dot_red _ hk hr]
  · rw [← dg_perm hp, dg_reach_cons_red _ hk hr]

/-- The dot excess is never negative. -/
theorem step3_eL_nonneg : ∀ (L : List (Comp (Atom k n))), 0 ≤ step3_eL L := by
  intro L
  induction h : L.length generalizing L with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 h
    simp only [step3_eL, step3_nD, List.filter_nil, List.length_nil, dg_nil, card_cc_bot, card_atom]
    push_cast
    ring_nf
    rfl
  | succ m ih =>
    by_cases hn : Step3NonRed L
    · rw [step3_eL_eq_zero_of_nonRed hn]
    · simp only [Step3NonRed, not_forall, not_not] at hn
      obtain ⟨c, L', hp, hk, hr⟩ := hn
      have h1 : step3_eL L = step3_eL L' + 1 := by rw [eL_perm hp, eL_cons_dot_red _ hk hr]
      have h2 := ih L' (by have := hp.length_eq; simp at this; omega)
      omega

/-- A labelling that agrees on the ends of every dotted component agrees along paths of dotted
components. -/
theorem sigma_eq_of_reach {ι : Type*} {L : List (Comp (Atom k n))} (σ : Atom k n → ι)
    (hz : ∀ c ∈ L, c.kind = .dot → σ c.x = σ c.y) {a b : Atom k n}
    (hr : (step3_dg L).Reachable a b) : σ a = σ b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := step3_dg_adj.1 hadj
    · exact (hz c hc hk).trans ih
    · exact (hz c hc hk).symm.trans ih

end Dots

/-! ## The merging operation -/

section Blocks

variable {V : Type*} [DecidableEq V]

/-- The relation "joined by a dotted component". -/
def step3_dotRel (cs : List (Comp V)) : V → V → Prop :=
  fun u v => ∃ c ∈ cs, c.kind = .dot ∧ c.x = u ∧ c.y = v

omit [DecidableEq V] in
theorem step3_dotRel_mono {cs cs' : List (Comp V)} (h : ∀ c ∈ cs, c ∈ cs') :
    step3_dotRel cs ≤ step3_dotRel cs' := by
  rintro u v ⟨c, hc, hk, hx, hy⟩
  exact ⟨c, h c hc, hk, hx, hy⟩

omit [DecidableEq V] in
theorem step3_flatten_map_singleton' (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem step3_joinBlocks_flatten_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

/-- One step of `dotBlocks`. -/
def step3_blockStep (c : Comp V) (P : List (List V)) : List (List V) :=
  if c.kind = .dot then joinBlocks P c.x c.y else P

theorem step3_dotBlocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) = step3_blockStep c (dotBlocks as cs) := by
  simp [dotBlocks, List.foldl_append, step3_blockStep]

theorem step3_dotBlocks_nil (as : List V) : dotBlocks as ([] : List (Comp V)) =
    as.map fun a => [a] := rfl

theorem step3_dotBlocks_flatten_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  induction cs using List.reverseRecOn with
  | nil => rw [step3_dotBlocks_nil, step3_flatten_map_singleton']
  | append_singleton cs c ih =>
    rw [step3_dotBlocks_snoc, step3_blockStep]
    split_ifs
    · exact (step3_joinBlocks_flatten_perm _ _ _).trans ih
    · exact ih

theorem step3_dotBlocks_conn (as : List V) (cs : List (Comp V)) :
    ∀ B ∈ dotBlocks as cs, ∀ u ∈ B, ∀ v ∈ B, Relation.EqvGen (step3_dotRel cs) u v := by
  induction cs using List.reverseRecOn with
  | nil =>
    intro B hB u hu v hv
    rw [step3_dotBlocks_nil, List.mem_map] at hB
    obtain ⟨a, -, rfl⟩ := hB
    simp only [List.mem_singleton] at hu hv
    subst hu; subst hv
    exact Relation.EqvGen.refl _
  | append_singleton cs c ih =>
    have hmono : ∀ u v, Relation.EqvGen (step3_dotRel cs) u v →
        Relation.EqvGen (step3_dotRel (cs ++ [c])) u v := fun u v h =>
      Relation.EqvGen.mono (step3_dotRel_mono fun c' hc' => List.mem_append_left _ hc') u v h
    intro B hB u hu v hv
    rw [step3_dotBlocks_snoc, step3_blockStep] at hB
    split_ifs at hB with hk
    · unfold joinBlocks at hB
      rw [List.mem_append] at hB
      rcases hB with hB | hB
      · exact hmono _ _ (ih B (List.mem_of_mem_filter hB) u hu v hv)
      · rw [List.mem_singleton] at hB
        subst hB
        have hxy : Relation.EqvGen (step3_dotRel (cs ++ [c])) c.x c.y :=
          Relation.EqvGen.rel _ _ ⟨c, List.mem_append_right _ (List.mem_singleton_self _), hk, rfl,
            rfl⟩
        -- every element of the joined block is connected to `c.x` by dotted edges
        have key : ∀ w ∈ (dotBlocks as cs).filter (fun B => B.contains c.x || B.contains c.y),
            ∀ z ∈ w, Relation.EqvGen (step3_dotRel (cs ++ [c])) z c.x := by
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

theorem step3_dotBlocks_joined (as : List V) (cs : List (Comp V))
    (hcs : ∀ c ∈ cs, c.x ∈ as ∧ c.y ∈ as) :
    ∀ c ∈ cs, c.kind = .dot → ∃ B ∈ dotBlocks as cs, c.x ∈ B ∧ c.y ∈ B := by
  induction cs using List.reverseRecOn with
  | nil => intro c hc; simp at hc
  | append_singleton cs c ih =>
    have ih' := ih fun c' hc' => hcs c' (List.mem_append_left _ hc')
    intro c' hc' hk'
    rw [step3_dotBlocks_snoc, step3_blockStep]
    -- membership of an atom of `as` in some block
    have hmem : ∀ a ∈ as, ∃ B ∈ dotBlocks as cs, a ∈ B := by
      intro a ha
      have := (step3_dotBlocks_flatten_perm as cs).mem_iff.2 ha
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
theorem step3_blockRep_eq_of_mem {P : List (List V)} (hnd : P.flatten.Nodup) {B : List V}
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

theorem step3_blockRep_spec (P : List (List V)) (u : V) :
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

theorem step3_mem_allAtoms (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | i <;> simp [allAtoms]

theorem step3_allAtoms_nodup : (allAtoms k n).Nodup := by
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
def Graph.step3_mrep (Γ : Graph k n) : Atom k n → Atom k n :=
  blockRep (dotBlocks (allAtoms k n) Γ.comps)

theorem Graph.step3_mrep_dot (Γ : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : Γ.step3_mrep c.x = Γ.step3_mrep c.y := by
  obtain ⟨B, hB, hx, hy⟩ := step3_dotBlocks_joined (allAtoms k n) Γ.comps
    (fun c _ => ⟨step3_mem_allAtoms _, step3_mem_allAtoms _⟩) c hc hk
  have hnd : (dotBlocks (allAtoms k n) Γ.comps).flatten.Nodup :=
    (step3_dotBlocks_flatten_perm _ _).nodup_iff.2 step3_allAtoms_nodup
  exact step3_blockRep_eq_of_mem hnd hB hx hy

theorem Graph.step3_mrep_conn (Γ : Graph k n) (u : Atom k n) :
    Relation.EqvGen (step3_dotRel Γ.comps) u (Γ.step3_mrep u) := by
  rcases step3_blockRep_spec (dotBlocks (allAtoms k n) Γ.comps) u with h | ⟨B, hB, hu, hr⟩
  · have : Γ.step3_mrep u = u := h
    rw [this]
    exact Relation.EqvGen.refl _
  · exact step3_dotBlocks_conn _ _ B hB u hu _ hr

/-- The roots: the representatives of the internal atoms, without repetition. -/
def Graph.step3_mroots (Γ : Graph k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => Γ.step3_mrep (Sum.inr i)).dedup

theorem Graph.step3_mem_mroots (Γ : Graph k n) (i : Fin n) : Γ.step3_mrep (.inr i) ∈ Γ.step3_mroots :=
  List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

/-- The new internal atom of an internal atom: the position of its root. -/
def Graph.step3_midx (Γ : Graph k n) (i : Fin n) : Fin Γ.step3_mroots.length :=
  ⟨Γ.step3_mroots.idxOf (Γ.step3_mrep (.inr i)), List.idxOf_lt_length_of_mem (Γ.step3_mem_mroots i)⟩

/-- The atom map of `O_merge`. -/
def Graph.step3_mmap (Γ : Graph k n) : Atom k n → Atom k Γ.step3_mroots.length :=
  fun u => match u with
    | .inl a => .inl a
    | .inr i => .inr (Γ.step3_midx i)

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
def step3_mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

theorem step3_mergeT_eq (Γ : Graph k n) : Γ.mergeT =
    if Γ.comps.any (fun c => c.kind == .xdot && Γ.step3_mrep c.x == Γ.step3_mrep c.y) then none else
    some ⟨Γ.step3_mroots.length, ⟨Γ.comps.filterMap (step3_mergeComp Γ.step3_mrep Γ.step3_mmap), Γ.coeff⟩, Γ.step3_mmap⟩ := rfl

/-- The structure of a tracked graph `t` with `Γ.mergeT = some t`: its components, its atom map
and its blocks. -/
structure Step3MergeSpec (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps = Γ.comps.filterMap (step3_mergeComp Γ.step3_mrep t.f)
  coeff_eq : t.g.coeff = Γ.coeff
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_surj : Function.Surjective t.f
  f_inr : ∃ g : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (g i)) ∧ Function.Surjective g
  f_eq : ∀ u v, Γ.step3_mrep u = Γ.step3_mrep v → u.isRight = true → v.isRight = true → t.f u = t.f v
  f_ne : ∀ u v, Γ.step3_mrep u ≠ Γ.step3_mrep v → t.f u ≠ t.f v
  xdot_ne : ∀ c ∈ Γ.comps, c.kind = .xdot → Γ.step3_mrep c.x ≠ Γ.step3_mrep c.y

theorem mergeT_none {Γ : Graph k n} (h : Γ.mergeT = none) :
    ∃ c ∈ Γ.comps, c.kind = .xdot ∧ Γ.step3_mrep c.x = Γ.step3_mrep c.y := by
  rw [step3_mergeT_eq] at h
  split_ifs at h with hc
  rw [List.any_eq_true] at hc
  obtain ⟨c, hc, hb⟩ := hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨c, hc, hb.1, hb.2⟩

theorem step3_mergeT_spec {Γ : Graph k n} {t : Tracked k n} (h : Γ.mergeT = some t) :
    Step3MergeSpec Γ t := by
  rw [step3_mergeT_eq] at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have hsurj : Function.Surjective Γ.step3_midx := by
    intro j
    have hj : Γ.step3_mroots[j.1] ∈ Γ.step3_mroots := List.getElem_mem j.2
    obtain ⟨i, -, hi⟩ := List.mem_map.1 (List.mem_dedup.1 hj)
    refine ⟨i, Fin.ext ?_⟩
    simp only [Graph.step3_midx]
    rw [hi]
    exact (List.nodup_dedup _).idxOf_getElem j.1 j.2
  refine ⟨rfl, rfl, ?_, fun a => rfl, ?_, ⟨Γ.step3_midx, fun i => rfl, hsurj⟩, ?_, ?_, ?_⟩
  · exact (List.dedup_sublist _).length_le.trans (by simp)
  · intro u'
    rcases u' with a | j
    · exact ⟨.inl a, rfl⟩
    · obtain ⟨i, hi⟩ := hsurj j
      exact ⟨.inr i, by simp [Graph.step3_mmap, hi]⟩
  · intro u v huv hu hv
    rcases u with a | i
    · simp at hu
    rcases v with b | j
    · simp at hv
    have : Γ.step3_midx i = Γ.step3_midx j := Fin.ext (by
      change Γ.step3_mroots.idxOf (Γ.step3_mrep (.inr i)) = Γ.step3_mroots.idxOf (Γ.step3_mrep (.inr j))
      rw [huv])
    simp [Graph.step3_mmap, this]
  · intro u v huv hf
    rcases u with a | i <;> rcases v with b | j
    · simp only [Graph.step3_mmap, Sum.inl.injEq] at hf
      exact huv (by rw [hf])
    · simp [Graph.step3_mmap] at hf
    · simp [Graph.step3_mmap] at hf
    · simp only [Graph.step3_mmap, Sum.inr.injEq] at hf
      have h2 := congrArg Fin.val hf
      simp only [Graph.step3_midx] at h2
      exact huv ((List.idxOf_inj (Γ.step3_mem_mroots i)).1 h2)
  · intro c hcm hk hcc
    apply hc
    rw [List.any_eq_true]
    exact ⟨c, hcm, by simp [hk, hcc]⟩

end MergeData

section MergeComp

variable {k n : ℕ}

theorem step3_mergeComp_label {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : step3_mergeComp rep f c = some c') :
    c'.label = c.label.map (Prod.map id f) := by
  unfold step3_mergeComp at h
  split_ifs at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain rfl := Option.some.inj h
    rfl

theorem step3_mergeComp_none {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (h : step3_mergeComp rep f c = none) : c.kind = .dot ∧ f c.x = f c.y := by
  unfold step3_mergeComp at h
  split_ifs at h with h1
  simpa using h1

theorem step3_mergeComp_of_solid {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (hs : c.kind.isSolid = true)
    (h : rep c.x ≠ rep c.y) : step3_mergeComp rep f c = some (c.map f) := by
  unfold step3_mergeComp
  split_ifs with h1 h2
  · simp at h1
    cases hk : c.kind <;> simp_all [Kind.isSolid]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact absurd h2.2 h
  · rfl

theorem step3_mergeComp_kind {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : step3_mergeComp rep f c = some c') :
    c'.kind = c.kind ∨ ∃ ch, c.kind = .G ch ∧ c'.kind = .weight ch := by
  unfold step3_mergeComp at h
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

theorem step3_mergeComp_dot {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hk : c.kind = .dot) :
    step3_mergeComp rep f c = if f c.x = f c.y then none else some (c.map f) := by
  unfold step3_mergeComp
  by_cases h : f c.x = f c.y
  · simp [hk, h]
  · simp [hk, h, Kind.isSolid]

theorem step3_mergeComp_solid {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hs : c.kind.isSolid = true) :
    step3_mergeComp rep f c = if rep c.x = rep c.y then
      some { c.map f with kind := c.kind.toWeight, y := f c.x } else some (c.map f) := by
  have hnd : c.kind ≠ .dot := by
    intro h
    rw [h] at hs
    simp [Kind.isSolid] at hs
  unfold step3_mergeComp
  by_cases h : rep c.x = rep c.y
  · simp [hs, h, hnd]
  · simp [hs, h, hnd]

theorem step3_mergeComp_other {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hd : c.kind ≠ .dot) (hs : c.kind.isSolid = false) :
    step3_mergeComp rep f c = some (c.map f) := by
  unfold step3_mergeComp
  simp [hd, hs]

variable {Γ : Graph k n} {t : Tracked k n}

theorem Step3MergeSpec.mem_comps (hs : Step3MergeSpec Γ t) {c' : Comp (Atom k t.nOut)} :
    c' ∈ t.g.comps ↔ ∃ c ∈ Γ.comps, step3_mergeComp Γ.step3_mrep t.f c = some c' := by
  rw [hs.comps_eq, List.mem_filterMap]

/-- A component that is neither a dotted edge nor a solid edge keeps its kind and is mapped. -/
theorem Step3MergeSpec.mem_of_other (hs : Step3MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hd : c.kind ≠ .dot) (hsol : c.kind.isSolid = false) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, step3_mergeComp_other hd hsol⟩

theorem Step3MergeSpec.mem_of_solid (hs : Step3MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hsol : c.kind.isSolid = true) (hr : Γ.step3_mrep c.x ≠ Γ.step3_mrep c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [step3_mergeComp_solid hsol, ite_eq_right hr]⟩

theorem Step3MergeSpec.mem_of_dot (hs : Step3MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) (hf : t.f c.x ≠ t.f c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [step3_mergeComp_dot hk, ite_eq_right hf]⟩

/-- A solid component of `t.g` is the image of a solid component of `Γ` whose ends are in
different blocks. -/
theorem Step3MergeSpec.of_mem_solid (hs : Step3MergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind.isSolid = true) :
    ∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ Γ.step3_mrep c.x ≠ Γ.step3_mrep c.y ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases step3_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind.isSolid = true := by rw [← h]; exact hk
    rw [step3_mergeComp_solid hck] at hm
    split_ifs at hm with hr
    · exfalso
      obtain rfl := Option.some.inj hm
      obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
        cases hkk : c.kind <;> simp_all [Kind.isSolid]
      simp [Kind.toWeight, hch, Kind.isSolid] at hk
    · exact ⟨c, hc, hck, hr, (Option.some.inj hm).symm⟩
  · rw [hch'] at hk
    simp [Kind.isSolid] at hk

theorem Step3MergeSpec.dot_reach (hs : Step3MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) :
    t.g.edgeGraphNoX.Reachable (t.f c.x) (t.f c.y) := by
  by_cases hf : t.f c.x = t.f c.y
  · rw [hf]
  · refine SimpleGraph.Adj.reachable ?_
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj]
    exact ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_dot hc hk hf, by simp [Comp.map, hk], rfl, rfl⟩⟩

theorem Step3MergeSpec.eqv_reach (hs : Step3MergeSpec Γ t) {u v : Atom k n}
    (h : Relation.EqvGen (step3_dotRel Γ.comps) u v) :
    t.g.edgeGraphNoX.Reachable (t.f u) (t.f v) := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact hs.dot_reach hc hk
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem Step3MergeSpec.noX_reach (hs : Step3MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind ≠ .xdot) :
    t.g.edgeGraphNoX.Reachable (t.f c.x) (t.f c.y) := by
  by_cases hd : c.kind = .dot
  · exact hs.dot_reach hc hd
  by_cases hsol : c.kind.isSolid = true
  · by_cases hr : Γ.step3_mrep c.x = Γ.step3_mrep c.y
    · have hconn : Relation.EqvGen (step3_dotRel Γ.comps) c.x c.y :=
        (Γ.step3_mrep_conn c.x).trans _ _ _ (hr ▸ (Γ.step3_mrep_conn c.y).symm)
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

theorem Step3MergeSpec.connNoX (hs : Step3MergeSpec Γ t) (hconn : Γ.ConnNoX) : t.g.ConnNoX := by
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

theorem Step3MergeSpec.wt_reach (hs : Step3MergeSpec Γ t) {c : Comp (Atom k n)}
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

theorem Step3MergeSpec.internal (hs : Step3MergeSpec Γ t)
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
theorem Step3MergeSpec.noIntDot (hs : Step3MergeSpec Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind = .dot → c'.x.isLeft = true ∨ c'.y.isLeft = true := by
  intro c' hc' hk'
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases step3_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .dot := h ▸ hk'
    rw [step3_mergeComp_dot hck] at hm
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
    exact hs.f_eq _ _ (Γ.step3_mrep_dot hc hck) hx' hy'
  · rw [hch'] at hk'
    cases hk'

theorem Step3MergeSpec.solid_ne (hs : Step3MergeSpec Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind.isSolid = true → c'.x ≠ c'.y := by
  intro c' hc' hk'
  obtain ⟨c, hc, -, hr, rfl⟩ := hs.of_mem_solid hc' hk'
  exact hs.f_ne _ _ hr

end MergeFacts

/-! ## Blocks, scaling order and dot excess under `O_merge` -/

section MergeBlocks

variable {k n : ℕ}

theorem eqvGen_dotRel_reach {L : List (Comp (Atom k n))} {u v : Atom k n}
    (h : Relation.EqvGen (step3_dotRel L) u v) : (step3_dg L).Reachable u v := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact step3_dg_reach_of_mem hc hk
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two atoms have the same representative exactly when they lie in one block. -/
theorem Graph.mrep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.step3_mrep u = Γ.step3_mrep v ↔ Γ.SameBlock u v := by
  constructor
  · intro h
    have h1 := eqvGen_dotRel_reach (Γ.step3_mrep_conn u)
    have h2 := eqvGen_dotRel_reach (Γ.step3_mrep_conn v)
    rw [h] at h1
    exact h1.trans h2.symm
  · intro h
    exact sigma_eq_of_reach Γ.step3_mrep (fun c hc hk => Γ.step3_mrep_dot hc hk) h

variable {Γ : Graph k n} {t : Tracked k n}

theorem Step3MergeSpec.sameBlock_of_f_eq (hs : Step3MergeSpec Γ t) {u v : Atom k n}
    (h : t.f u = t.f v) : Γ.SameBlock u v := by
  by_contra hb
  exact hs.f_ne u v (fun hr => hb ((Γ.mrep_eq_iff u v).1 hr)) h

/-- Two distinct atoms with the same image are internal. -/
theorem Step3MergeSpec.isRight_of_f_eq (hs : Step3MergeSpec Γ t) {u v : Atom k n}
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

theorem Step3MergeSpec.dot_of_mem (hs : Step3MergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind = .dot) :
    ∃ c ∈ Γ.comps, c.kind = .dot ∧ t.f c.x ≠ t.f c.y ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases step3_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .dot := h ▸ hk
    rw [step3_mergeComp_dot hck] at hm
    split_ifs at hm with hf
    exact ⟨c, hc, hck, hf, (Option.some.inj hm).symm⟩
  · rw [hch'] at hk
    cases hk

/-- Blocks are mapped into blocks. -/
theorem Step3MergeSpec.sameBlock_map (hs : Step3MergeSpec Γ t) {u v : Atom k n}
    (h : Γ.SameBlock u v) : t.g.SameBlock (t.f u) (t.f v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, hxy⟩ := step3_dg_adj.1 hadj
    refine SimpleGraph.Reachable.trans ?_ ih
    have : t.g.SameBlock (t.f c.x) (t.f c.y) := by
      by_cases hf : t.f c.x = t.f c.y
      · exact hf ▸ SimpleGraph.Reachable.refl _
      · exact step3_dg_reach_of_mem (hs.mem_of_dot hc hk hf) (by simp [Comp.map, hk])
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · exact this.symm

/-- Atoms whose images lie in one block lie in one block. -/
theorem Step3MergeSpec.sameBlock_of_map (hs : Step3MergeSpec Γ t) {u v : Atom k n}
    (h : t.g.SameBlock (t.f u) (t.f v)) : Γ.SameBlock u v := by
  have key : ∀ a b, (step3_dg t.g.comps).Reachable a b → ∀ u v, t.f u = a → t.f v = b →
      Γ.SameBlock u v := by
    intro a b hr
    obtain ⟨w⟩ := hr
    induction w with
    | nil => intro u v hu hv; exact hs.sameBlock_of_f_eq (hu.trans hv.symm)
    | @cons a a' b hadj _ ih =>
      intro u v hu hv
      obtain ⟨-, c', hc', hk', hxy⟩ := step3_dg_adj.1 hadj
      obtain ⟨c, hc, hk, -, rfl⟩ := hs.dot_of_mem hc' hk'
      have hcc : Γ.SameBlock c.x c.y := step3_dg_reach_of_mem hc hk
      simp only [Comp.map] at hxy
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (hs.sameBlock_of_f_eq (hu.trans h1.symm)).trans (hcc.trans (ih c.y v h2 hv))
      · exact (hs.sameBlock_of_f_eq (hu.trans h2.symm)).trans
          (hcc.symm.trans (ih c.x v h1 hv))
  exact key _ _ h u v rfl rfl

theorem Step3MergeSpec.sameBlock_iff (hs : Step3MergeSpec Γ t) (u v : Atom k n) :
    t.g.SameBlock (t.f u) (t.f v) ↔ Γ.SameBlock u v :=
  ⟨hs.sameBlock_of_map, hs.sameBlock_map⟩

/-- `O_merge` keeps the number of blocks. -/
theorem Step3MergeSpec.card_cc (hs : Step3MergeSpec Γ t) :
    Nat.card (step3_dg Γ.comps).ConnectedComponent = Nat.card (step3_dg t.g.comps).ConnectedComponent :=
  card_cc_of_map t.f hs.f_surj hs.sameBlock_iff

/-- The dotted components removed by `O_merge`. -/
def removedDots (Γ : Graph k n) (f : Atom k n → Atom k m) : List (Comp (Atom k n)) :=
  Γ.comps.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)

theorem step3_nD_filterMap_mergeComp {m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) :
    ∀ L : List (Comp (Atom k n)), step3_nD (L.filterMap (step3_mergeComp rep f)) +
      (L.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)).length = step3_nD L
  | [] => rfl
  | c :: L => by
    have ih := step3_nD_filterMap_mergeComp rep f L
    rcases hm : step3_mergeComp rep f c with _ | c'
    · obtain ⟨hk, hf⟩ := step3_mergeComp_none hm
      rw [List.filterMap_cons_none hm, List.filter_cons_of_pos (by simp [hk, hf]), step3_nD_cons]
      simp only [hk, ite_true, List.length_cons]
      omega
    · have hnd : ¬ (c.kind = .dot ∧ f c.x = f c.y) := by
        rintro ⟨hk, hf⟩
        rw [step3_mergeComp_dot hk] at hm
        simp [hf] at hm
      have hkk : (c'.kind = .dot) ↔ (c.kind = .dot) := by
        rcases step3_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
        · rw [h]
        · rw [hch, hch']
          simp
      rw [List.filterMap_cons_some hm, List.filter_cons_of_neg (by simpa using hnd), step3_nD_cons,
        step3_nD_cons]
      by_cases hk : c.kind = .dot
      · simp only [hkk.2 hk, hk, ite_true]
        omega
      · simp only [show ¬ c'.kind = .dot from fun h => hk (hkk.1 h), hk, ite_false]
        omega

theorem ordSum_filterMap_mergeComp {m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) :
    ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, c.kind.isSolid = true → rep c.x ≠ rep c.y) →
      ((L.filterMap (step3_mergeComp rep f)).map fun c => c.kind.ord).sum +
        2 * ((L.filter fun c => decide (c.kind = .dot ∧ f c.x = f c.y)).length : ℤ) =
      (L.map fun c => c.kind.ord).sum
  | [], _ => by simp
  | c :: L, hsol => by
    have ih := ordSum_filterMap_mergeComp rep f L fun d hd => hsol d (List.mem_cons_of_mem _ hd)
    rcases hm : step3_mergeComp rep f c with _ | c'
    · obtain ⟨hk, hf⟩ := step3_mergeComp_none hm
      rw [List.filterMap_cons_none hm, List.filter_cons_of_pos (by simp [hk, hf])]
      simp only [List.length_cons, List.map_cons, List.sum_cons, hk]
      have h2 : Kind.dot.ord = 2 := rfl
      push_cast
      linarith
    · have hnd : ¬ (c.kind = .dot ∧ f c.x = f c.y) := by
        rintro ⟨hk, hf⟩
        rw [step3_mergeComp_dot hk] at hm
        simp [hf] at hm
      have hkk : c'.kind = c.kind := by
        rcases step3_mergeComp_kind hm with h | ⟨ch, hch, -⟩
        · exact h
        · have hs : c.kind.isSolid = true := by rw [hch]; rfl
          rw [step3_mergeComp_of_solid hs (hsol c (List.mem_cons_self ..) hs)] at hm
          rw [← Option.some.inj hm]
          rfl
      rw [List.filterMap_cons_some hm, List.filter_cons_of_neg (by simpa using hnd)]
      simp only [List.map_cons, List.sum_cons, hkk]
      linarith

/-- The scaling order and the dot excess after `O_merge`, when no solid edge lies in a block:
the removed dotted components lower both, the identified internal atoms raise both. -/
theorem Step3MergeSpec.ord_eL (hs : Step3MergeSpec Γ t)
    (hsol : ∀ c ∈ Γ.comps, c.kind.isSolid = true → ¬ Γ.SameBlock c.x c.y) :
    t.g.ord = Γ.ord - 2 * ((removedDots Γ t.f).length : ℤ) + 2 * ((n : ℤ) - t.nOut) ∧
      step3_eL t.g.comps = step3_eL Γ.comps - ((removedDots Γ t.f).length : ℤ) + ((n : ℤ) - t.nOut) := by
  have hsol' : ∀ c ∈ Γ.comps, c.kind.isSolid = true → Γ.step3_mrep c.x ≠ Γ.step3_mrep c.y :=
    fun c hc hk hr => hsol c hc hk ((Γ.mrep_eq_iff _ _).1 hr)
  have h1 := ordSum_filterMap_mergeComp Γ.step3_mrep t.f Γ.comps hsol'
  have h2 := step3_nD_filterMap_mergeComp Γ.step3_mrep t.f Γ.comps
  rw [← hs.comps_eq] at h1 h2
  refine ⟨?_, ?_⟩
  · simp only [Graph.ord, removedDots]
    linarith
  · simp only [step3_eL, removedDots, hs.card_cc]
    push_cast
    omega

/-- Dotted components between internal atoms are needed. -/
def Step3NonRedInt (L : List (Comp (Atom k n))) : Prop :=
  ∀ (c : Comp (Atom k n)) (L' : List (Comp (Atom k n))), L.Perm (c :: L') → c.kind = .dot →
    c.x.isRight = true → c.y.isRight = true → ¬ (step3_dg L').Reachable c.x c.y

/-- If the dotted components between internal atoms are needed and there is no dotted loop, the
removed dotted components are at most the identified internal atoms. -/
theorem Step3MergeSpec.removedDots_le (hs : Step3MergeSpec Γ t) (hnr : Step3NonRedInt Γ.comps)
    (hloop : ∀ c ∈ Γ.comps, c.kind = .dot → c.x ≠ c.y) :
    ((removedDots Γ t.f).length : ℤ) ≤ (n : ℤ) - t.nOut := by
  set H := removedDots Γ t.f with hH
  have hmemH : ∀ c ∈ H, c ∈ Γ.comps ∧ c.kind = .dot ∧ t.f c.x = t.f c.y := by
    intro c hc
    rw [hH, removedDots, List.mem_filter] at hc
    simpa using hc
  have hnr' : Step3NonRed H := by
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
  have h0 := step3_eL_eq_zero_of_nonRed hnr'
  have hnD : step3_nD H = H.length := by
    unfold step3_nD
    rw [List.filter_eq_self.2]
    intro c hc
    simp [(hmemH c hc).2.1]
  have hle := card_le_card_cc (G := step3_dg H) t.f hs.f_surj (by
    intro a b hr
    exact sigma_eq_of_reach t.f (fun c hc _ => (hmemH c hc).2.2) hr)
  rw [card_atom] at hle
  simp only [step3_eL, hnD] at h0
  push_cast at h0 hle
  omega

end MergeBlocks

/-! ## Doubly connected structures -/

section Tagged

variable {k n m : ℕ}

/-- The kinds usable in a blue net whose solid edges have charge `bc`: the solid edges of charge
`bc` and the ghost edges. -/
def Kind.step3_blueC (bc : Charge) : Kind → Bool
  | .G c => decide (c = bc)
  | .ghost => true
  | _ => false

theorem Kind.blueC_plus (κ : Kind) : κ.step3_blueC .plus = κ.isBlue := by
  cases κ with
  | G c => cases c <;> rfl
  | _ => rfl

/-- A component with a tag. -/
abbrev Step3TC (k n : ℕ) : Type := Comp (Atom k n) × Option Bool

/-- The graph on the internal atoms whose edges join two atoms of one molecule, or the two ends of
a component of `L` with the tag `some t`. -/
def Graph.step3_netT (Γ : Graph k n) (L : List (Step3TC k n)) (t : Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => Γ.SameMol (Sum.inr a) (Sum.inr b) ∨
    ∃ p ∈ L, p.2 = some t ∧ p.1.x = Sum.inr a ∧ p.1.y = Sum.inr b

/-- The tagged list `L` is a doubly connected structure on `Γ` with blue charge `bc`: it lists the
components of `Γ`, black ones are diffusive, blue ones are diffusive or blue, and each net spans the
internal atoms. -/
structure Graph.Step3DCT (bc : Charge) (Γ : Graph k n) (L : List (Step3TC k n)) : Prop where
  map_fst : L.map Prod.fst = Γ.comps
  black : ∀ p ∈ L, p.2 = some false → p.1.kind.isDiffusive = true
  blue : ∀ p ∈ L, p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.step3_blueC bc = true
  spanBlack : (Γ.step3_netT L false).Preconnected
  spanBlue : (Γ.step3_netT L true).Preconnected

/-- The graph has a doubly connected structure with blue charge `bc`. -/
def Graph.Step3DCS (bc : Charge) (Γ : Graph k n) : Prop := ∃ L, Γ.Step3DCT bc L

theorem Graph.molReach_of_comp {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind.joinsMol = true) : Γ.molGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

theorem Graph.netT_reach_of_sameMol (Γ : Graph k n) (L : List (Step3TC k n)) (t : Bool)
    {a b : Fin n} (h : Γ.SameMol (Sum.inr a) (Sum.inr b)) : (Γ.step3_netT L t).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl (Or.inl h)⟩ |>.reachable

theorem Graph.netT_reach_of_mem (Γ : Graph k n) (L : List (Step3TC k n)) (t : Bool)
    {p : Step3TC k n} (hp : p ∈ L) (ht : p.2 = some t) {a b : Fin n} (hx : p.1.x = Sum.inr a)
    (hy : p.1.y = Sum.inr b) : (Γ.step3_netT L t).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl (Or.inr ⟨p, hp, ht, hx, hy⟩)⟩ |>.reachable

/-- Reachability in the molecular graph is carried by a map of the atoms that carries every waved
and dotted component to a reachable pair. -/
theorem molReach_map {Γ : Graph k n} {Γ' : Graph k m} (f : Atom k n → Atom k m)
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

theorem sameMol_map {Γ : Graph k n} {Γ' : Graph k m} (φ : Fin n → Fin m)
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
theorem Graph.Step3DCT.transport {bc : Charge} {Γ : Graph k n} {L : List (Step3TC k n)}
    (h : Γ.Step3DCT bc L) (φ : Fin n → Fin m) {Γ' : Graph k m} (L' : List (Step3TC k m))
    (hmap : L'.map Prod.fst = Γ'.comps)
    (hbl : ∀ p ∈ L', p.2 = some false → p.1.kind.isDiffusive = true)
    (hbu : ∀ p ∈ L', p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.step3_blueC bc = true)
    (hmol : ∀ c ∈ Γ.comps, c.kind.joinsMol = true →
      Γ'.molGraph.Reachable (Sum.map id φ c.x) (Sum.map id φ c.y))
    (hedge : ∀ t : Bool, ∀ p ∈ L, p.2 = some t → ∀ a b, p.1.x = Sum.inr a → p.1.y = Sum.inr b →
      (Γ'.step3_netT L' t).Reachable (φ a) (φ b))
    (hcov : ∀ w : Fin m, ∃ a : Fin n, Γ'.SameMol (Sum.inr w) (Sum.inr (φ a))) : Γ'.Step3DCT bc L' := by
  have key : ∀ t : Bool, (Γ.step3_netT L t).Preconnected → (Γ'.step3_netT L' t).Preconnected := by
    intro t hspan
    have hwalk : ∀ a b, (Γ.step3_netT L t).Reachable a b → (Γ'.step3_netT L' t).Reachable (φ a) (φ b) := by
      intro a b hr
      obtain ⟨w⟩ := hr
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a' b' c' hadj _ ih =>
        rw [Graph.step3_netT, SimpleGraph.fromRel_adj] at hadj
        have hstep : (Γ'.step3_netT L' t).Reachable (φ a') (φ b') := by
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

/-- A tagged list of the components of `Γ` with tags `some false` on `black` and `some true` on
`blue`. -/
def Graph.tagList (Γ : Graph k n) (black blue : Finset (Fin Γ.comps.length)) :
    List (Step3TC k n) :=
  (List.finRange Γ.comps.length).map fun i =>
    (Γ.comps[i.1], if i ∈ black then some false else if i ∈ blue then some true else none)

theorem Graph.tagList_map_fst (Γ : Graph k n) (black blue : Finset (Fin Γ.comps.length)) :
    (Γ.tagList black blue).map Prod.fst = Γ.comps := by
  unfold Graph.tagList
  rw [List.map_map]
  exact List.map_getElem_finRange Γ.comps

theorem Graph.tagList_mem {Γ : Graph k n} {black blue : Finset (Fin Γ.comps.length)}
    {p : Step3TC k n} (hp : p ∈ Γ.tagList black blue) : ∃ i : Fin Γ.comps.length,
    p = (Γ.comps[i.1], if i ∈ black then some false else if i ∈ blue then some true else none) := by
  unfold Graph.tagList at hp
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
  exact ⟨i, rfl⟩

/-- The net of a set of components is the net of the tagged list that marks them. -/
theorem Graph.net_eq_netT {Γ : Graph k n} {black blue : Finset (Fin Γ.comps.length)}
    (B : Finset (Fin Γ.comps.length)) (t : Bool)
    (hB : ∀ i : Fin Γ.comps.length,
      (if i ∈ black then some false else if i ∈ blue then some true else none) = some t ↔ i ∈ B) :
    Γ.net B = Γ.step3_netT (Γ.tagList black blue) t := by
  unfold Graph.net Graph.step3_netT
  congr 1
  funext a b
  refine propext (or_congr Iff.rfl ?_)
  constructor
  · rintro ⟨i, hi, hx, hy⟩
    exact ⟨_, List.mem_map_of_mem (List.mem_finRange i), (hB i).2 hi, hx, hy⟩
  · rintro ⟨p, hp, ht, hx, hy⟩
    obtain ⟨i, rfl⟩ := Graph.tagList_mem hp
    exact ⟨i, (hB i).1 ht, hx, hy⟩

/-- The tagged list of a doubly connected graph. -/
theorem Graph.doublyConnected_dcs {Γ : Graph k n} (h : Γ.DoublyConnected) :
    Γ.Step3DCS .plus := by
  obtain ⟨black, blue, hd, hbl, hbu, hsl, hsu⟩ := h
  refine ⟨Γ.tagList black blue, Γ.tagList_map_fst black blue, ?_, ?_, ?_, ?_⟩
  · intro p hp ht
    obtain ⟨i, rfl⟩ := Graph.tagList_mem hp
    by_cases hi : i ∈ black
    · exact hbl i hi
    · by_cases hj : i ∈ blue <;> simp [hi, hj] at ht
  · intro p hp ht
    obtain ⟨i, rfl⟩ := Graph.tagList_mem hp
    by_cases hi : i ∈ black
    · simp [hi] at ht
    · by_cases hj : i ∈ blue
      · rw [Kind.blueC_plus]
        exact hbu i hj
      · simp [hi, hj] at ht
  · rw [← Graph.net_eq_netT black false]
    · exact hsl
    · intro i
      by_cases hi : i ∈ black <;> by_cases hj : i ∈ blue <;> simp [hi, hj]
  · rw [← Graph.net_eq_netT blue true]
    · exact hsu
    · intro i
      by_cases hi : i ∈ black
      · have hj : i ∉ blue := fun hj => Finset.disjoint_left.1 hd hi hj
        simp [hi, hj]
      · by_cases hj : i ∈ blue <;> simp [hi, hj]

/-- A doubly connected structure with blue charge `plus` gives the doubly connected property. -/
theorem Graph.Step3DCT.doublyConnected {Γ : Graph k n} {L : List (Step3TC k n)}
    (h : Γ.Step3DCT .plus L) : Γ.DoublyConnected := by
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
      (Graph.mk (L.map Prod.fst) co).net B = (Graph.mk (L.map Prod.fst) co).step3_netT L t := by
    intro B t hB
    unfold Graph.net Graph.step3_netT
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
theorem Graph.Step3DCS.doublyConnected {Γ : Graph k n} (h : Γ.Step3DCS .plus) :
    Γ.DoublyConnected := by
  obtain ⟨L, hL⟩ := h
  exact hL.doublyConnected

/-- A tagged component of `L` has neither the kind `xdot` nor a weight kind if it is tagged
or joins molecules: its kind is diffusive, blue or joins molecules. -/
theorem Graph.Step3DCT.kind_of_tag {bc : Charge} {Γ : Graph k n} {L : List (Step3TC k n)}
    (h : Γ.Step3DCT bc L) {p : Step3TC k n} (hp : p ∈ L) (ht : p.2 ≠ none) :
    p.1.kind.isDiffusive = true ∨ p.1.kind.step3_blueC bc = true := by
  rcases hp2 : p.2 with _ | _ | _
  · exact absurd hp2 ht
  · exact Or.inl (h.black p hp hp2)
  · exact h.blue p hp hp2

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
def mergeC (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

/-- The atom map of `O_merge` sends internal atoms onto internal atoms and fixes external ones,
atoms with the same representative have the same image, and the components are the images. -/
theorem mergeT_struct {Γ : Graph k n} {t : Tracked k n} (ht : Γ.mergeT = some t) :
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

theorem map_fst_filterMap {α β γ : Type*} (L : List (α × γ)) (F : α → Option β)
    (τ : α × γ → β → γ) :
    (L.filterMap fun p => (F p.1).map fun c' => (c', τ p c')).map Prod.fst =
      (L.map Prod.fst).filterMap F := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rcases hF : F p.1 with _ | c' <;> simp [hF, ih]

/-- `O_merge` keeps a doubly connected structure and sends internal atoms to internal atoms. -/
theorem Graph.Step3DCS.mergeT {bc : Charge} {Γ : Graph k n} (h : Γ.Step3DCS bc)
    {t : Tracked k n} (ht : Γ.mergeT = some t) :
    t.g.Step3DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨rep, φ, hf, hsurj, hrep, hcomps⟩ := mergeT_struct ht
  have hint : ∀ u, (t.f u).isRight = u.isRight := by
    intro u
    rw [hf]
    rcases u with a | i <;> rfl
  refine ⟨?_, hint⟩
  let τ : Step3TC k n → Comp (Atom k t.nOut) → Option Bool :=
    fun p c' => if c'.kind = p.1.kind then p.2 else none
  let L' : List (Step3TC k t.nOut) :=
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
    have hkind : p.1.kind.isDiffusive = true ∨ p.1.kind.step3_blueC bc = true :=
      hL.kind_of_tag hp (by rw [hpt]; simp)
    have hnd : p.1.kind ≠ .dot := by
      intro hd
      rw [hd] at hkind
      simp [Kind.isDiffusive, Kind.step3_blueC] at hkind
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

/-! ## Good factors -/

section Good

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

theorem good_pow' (A : ModelAdm Ω ι PF D) {f : Ω → ℂ} (hf : A.Good f) (n : ℕ) :
    A.Good fun ω => f ω ^ n := by
  induction n with
  | zero => simpa using A.laws.good_const 1
  | succ n ih =>
    have h := A.laws.good_mul _ _ ih hf
    convert h using 1
    funext ω
    simp [pow_succ]

theorem good_sum_range (A : ModelAdm Ω ι PF D) (f : ℕ → Ω → ℂ)
    (hf : ∀ j, A.Good (f j)) (n : ℕ) : A.Good fun ω => ∑ j ∈ Finset.range n, f j ω := by
  induction n with
  | zero => simpa using A.laws.good_const 0
  | succ n ih =>
    have h := A.laws.good_add _ _ ih (hf n)
    convert h using 1
    funext ω
    simp [Finset.sum_range_succ]

theorem good_charge (A : ModelAdm Ω ι PF D) (ch : Charge) {f : Ω → ℂ} (hf : A.Good f) :
    A.Good fun ω => ch.apply (f ω) := by
  cases ch
  · exact hf
  · exact A.good_star f hf

theorem good_val (A : ModelAdm Ω ι PF D) {V : Type*} (σ : V → ι) (c : Comp V)
    (hc : c.isGoodKind = true) : A.Good fun ω => Comp.val (D ω) σ c := by
  obtain ⟨κ, x, y, T, l⟩ := c
  cases κ with
  | G ch => exact good_charge A ch (A.good_entry _ _ _)
  | weight ch => exact good_charge A ch (A.good_entry _ _ _)
  | light ch =>
    have h := A.laws.good_add _ _ (A.good_entry ((T.map σ).toFinset) (σ x) (σ x))
      (A.laws.good_const (-(msc A.z)))
    have key : (fun ω => Comp.val (D ω) σ ⟨.light ch, x, y, T, l⟩) =
        fun ω => ch.apply ((((fun ω => (D ω).Gm ((T.map σ).toFinset) (σ x) (σ x)) +
          fun _ => -(msc A.z)) : Ω → ℂ) ω) := by
      funext ω
      simp [Comp.val, A.data_m ω, sub_eq_add_neg]
    rw [key]
    exact good_charge A ch h
  | inv ch =>
    simp only [Comp.isGoodKind, List.isEmpty_iff] at hc
    subst hc
    have h := good_charge A ch (A.good_inv (σ x))
    convert h using 2 with ω
    simp [Comp.val]
  | wD ch d =>
    simp only [Comp.isGoodKind, List.isEmpty_iff] at hc
    subst hc
    have hu : A.Good fun ω => (D ω).Gm ∅ (σ x) (σ x) := A.good_entry _ _ _
    have hS : A.Good fun ω => ∑ j ∈ Finset.range (d + 1),
        ((-(msc A.z)⁻¹) * (D ω).Gm ∅ (σ x) (σ x) + (msc A.z * (msc A.z)⁻¹)) ^ j := by
      refine good_sum_range A (fun j ω => ((-(msc A.z)⁻¹) * (D ω).Gm ∅ (σ x) (σ x) +
        (msc A.z * (msc A.z)⁻¹)) ^ j) (fun j => good_pow' A ?_ j) _
      have := A.laws.good_add _ _ (A.laws.good_mul _ _ (A.laws.good_const (-(msc A.z)⁻¹)) hu)
        (A.laws.good_const (msc A.z * (msc A.z)⁻¹))
      exact this
    have h2 := A.laws.good_add _ _ (A.good_inv (σ x))
      (A.laws.good_mul _ _ (A.laws.good_const (-(msc A.z)⁻¹)) hS)
    have key : (fun ω => Comp.val (D ω) σ ⟨.wD ch d, x, y, [], l⟩) =
        fun ω => ch.apply ((((fun ω => ((D ω).Gm ∅ (σ x) (σ x))⁻¹) +
          ((fun _ => -(msc A.z)⁻¹) * fun ω => ∑ j ∈ Finset.range (d + 1),
            ((-(msc A.z)⁻¹) * (D ω).Gm ∅ (σ x) (σ x) +
              (msc A.z * (msc A.z)⁻¹)) ^ j)) : Ω → ℂ) ω) := by
      funext ω
      simp only [Comp.val, A.data_m ω, List.map_nil, List.toFinset_nil, Pi.add_apply, Pi.mul_apply]
      congr 1
      rw [neg_mul, ← sub_eq_add_neg]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [div_eq_mul_inv]
      ring
    rw [key]
    exact good_charge A ch h2
  | waved w => simp [Comp.isGoodKind] at hc
  | theta o => simp [Comp.isGoodKind] at hc
  | thetaErr n d => simp [Comp.isGoodKind] at hc
  | ghost => simp [Comp.isGoodKind] at hc
  | aux j r b => simp [Comp.isGoodKind] at hc
  | dot => simp [Comp.isGoodKind] at hc
  | xdot => simp [Comp.isGoodKind] at hc

end Good

/-! ## The value of the removal of the label `P_u` -/

section DropPVals

theorem step3_dedup_eq_singleton {α : Type*} [DecidableEq α] (l : List α) (a : α)
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
theorem labels_eq_single {k n : ℕ} (L : List (Comp (Atom k n))) (co : Coeff)
    (ℓ : PQ × Atom k n) (hl : ∀ c ∈ L, c.label = none ∨ c.label = some ℓ)
    (hex : ∃ c ∈ L, c.label = some ℓ) : (⟨L, co⟩ : Graph k n).labels = [ℓ] := by
  unfold Graph.labels
  apply step3_dedup_eq_singleton
  · intro a ha
    obtain ⟨c, hc, hca⟩ := List.mem_filterMap.1 ha
    rcases hl c hc with h | h
    · rw [h] at hca; cases hca
    · rw [h] at hca; exact (Option.some.inj hca).symm
  · obtain ⟨c, hc, hcl⟩ := hex
    exact List.mem_filterMap.2 ⟨c, hc, hcl⟩

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

/-- The product of the component values, as a function of the sample point. -/
def Fn (D : Ω → Data ι) (σ : Atom k n → ι) (cs : List (Comp (Atom k n))) : Ω → ℂ :=
  fun ω => (cs.map (Comp.val (D ω) σ)).prod

theorem good_Fn (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) :
    ∀ cs : List (Comp (Atom k n)), (∀ c ∈ cs, c.isGoodKind = true) → A.Good (Fn D σ cs) := by
  intro cs
  induction cs with
  | nil =>
    intro _
    have := A.laws.good_const 1
    convert this using 1
    funext ω
    simp [Fn]
  | cons c cs ih =>
    intro h
    have := A.laws.good_mul _ _ (good_val A σ c (h c (List.mem_cons_self ..)))
      (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    convert this using 1
    funext ω
    simp [Fn]

/-- The conjugate of a function independent of a row is independent of it. -/
theorem meas_star (A : ModelAdm Ω ι PF D) (u : ι) {F : Ω → ℂ} (hg : A.Good F)
    (hm : A.Meas u F) : A.Meas u fun ω => star (F ω) := by
  have h1 : PF.P u (fun ω => star (F ω)) = fun ω => star (F ω) := by
    rw [A.P_star u F hg, A.laws.of_meas u F hg hm]
  have h2 := A.laws.meas_P u (fun ω => star (F ω)) (A.good_star F hg)
  rwa [h1] at h2

theorem meas_charge (A : ModelAdm Ω ι PF D) (u : ι) (ch : Charge) {F : Ω → ℂ}
    (hg : A.Good F) (hm : A.Meas u F) : A.Meas u fun ω => ch.apply (F ω) := by
  cases ch
  · exact hm
  · exact meas_star A u hg hm

/-- A solid edge, a weight or a light weight with minor `{u}` does not depend on the row of `u`. -/
theorem meas_val (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) (u : Atom k n)
    (c : Comp (Atom k n)) (hmin : c.minor = [u])
    (hk : ∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) :
    A.Meas (σ u) fun ω => Comp.val (D ω) σ c := by
  obtain ⟨ch, hk⟩ := hk
  have hs : (c.minor.map σ).toFinset = {σ u} := by simp [hmin]
  rcases hk with hk | hk | hk
  · have := meas_charge A (σ u) ch (A.good_entry {σ u} (σ c.x) (σ c.y))
      (A.meas_minor (σ u) (σ c.x) (σ c.y))
    convert this using 2 with ω
    simp [Comp.val, hk, hs]
  · have := meas_charge A (σ u) ch (A.good_entry {σ u} (σ c.x) (σ c.x))
      (A.meas_minor (σ u) (σ c.x) (σ c.x))
    convert this using 2 with ω
    simp [Comp.val, hk, hs]
  · have hg := A.laws.good_add _ _ (A.good_entry {σ u} (σ c.x) (σ c.x))
      (A.laws.good_const (-(msc A.z)))
    have hm := A.meas_add (σ u) _ _ (A.meas_minor (σ u) (σ c.x) (σ c.x))
      (A.laws.meas_const (σ u) (-(msc A.z)))
    have := meas_charge A (σ u) ch hg hm
    convert this using 2 with ω
    simp [Comp.val, hk, hs, A.data_m ω, sub_eq_add_neg]

theorem meas_Fn (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) (u : Atom k n) :
    ∀ cs : List (Comp (Atom k n)), (∀ c ∈ cs, c.minor = [u] ∧
      ∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) →
      A.Meas (σ u) (Fn D σ cs)
  | [], _ => by
    have := A.laws.meas_const (σ u) 1
    convert this using 1
    funext ω
    simp [Fn]
  | c :: cs, h => by
    have h1 := meas_val A σ u c (h c (List.mem_cons_self ..)).1 (h c (List.mem_cons_self ..)).2
    have h2 := meas_Fn A σ u cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    have := A.meas_mul (σ u) _ _ h1 h2
    convert this using 1
    funext ω
    simp [Fn]

/-- Removing the label `P_u` from a group of solid edges, weights and light weights, all with the
minor `{u}`, keeps the value under the model relations: such a group does not depend on the row of
`u`, so `P_u` acts on it as the identity. -/
theorem dropP_value (Γ : Graph k n) (u : Atom k n)
    (hl : ∀ c ∈ Γ.comps, c.label = none ∨ c.label = some (.P, u))
    (hex : ∃ c ∈ Γ.comps, c.label = some (.P, u))
    (hm : ∀ c ∈ Γ.comps, c.label = some (.P, u) → c.minor = [u] ∧
      ∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch)
    (A : ModelAdm Ω ι PF D) (e : Fin k → ι) :
    Γ.dropLabels.valR PF D e = Γ.valR PF D e := by
  obtain ⟨cs, co⟩ := Γ
  have hlab1 : (⟨cs, co⟩ : Graph k n).labels = [(.P, u)] := labels_eq_single cs co _ hl hex
  have hlab2 : (Graph.dropLabels ⟨cs, co⟩).labels = [] := by
    unfold Graph.labels
    rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
    intro c hc
    simp only [Graph.dropLabels, List.mem_map] at hc
    obtain ⟨c₀, -, rfl⟩ := hc
    rfl
  funext ω
  simp only [Graph.valR]
  refine Finset.sum_congr rfl fun s _ => ?_
  set σ := Sum.elim e s
  set F := Fn D σ (cs.filter fun c => decide (c.label = some (.P, u))) with hFdef
  have hg : A.Good F := good_Fn A σ _ fun c hc => by
    have hc' := List.mem_filter.1 hc
    obtain ⟨-, ch, hk⟩ := hm c hc'.1 (by simpa using hc'.2)
    rcases hk with hk | hk | hk <;> simp [Comp.isGoodKind, hk]
  have hmeas : A.Meas (σ u) F := meas_Fn A σ u _ fun c hc => by
    have hc' := List.mem_filter.1 hc
    exact hm c hc'.1 (by simpa using hc'.2)
  have hP : PF.P (σ u) F = F := A.laws.of_meas _ _ hg hmeas
  have hF : (fun ω' => ((cs.filter fun c => decide (c.label = some (PQ.P, u))).map
      (Comp.val (D ω') σ)).prod) = F := rfl
  have hall : ((cs.map fun c => { c with label := none }).filter fun c => c.label.isNone) =
      cs.map fun c => { c with label := none } :=
    List.filter_eq_self.2 fun c hc => by
      obtain ⟨c₀, -, rfl⟩ := List.mem_map.1 hc
      rfl
  have hval : ((cs.map fun c => { c with label := none }).map (Comp.val (D ω) σ)) =
      cs.map (Comp.val (D ω) σ) := by
    rw [List.map_map]
    rfl
  have hsplit : (cs.map (Comp.val (D ω) σ)).prod =
      ((cs.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod * F ω := by
    have hp := List.filter_append_perm (fun c : Comp (Atom k n) => c.label.isNone) cs
    have hc : cs.filter (fun c => !c.label.isNone) =
        cs.filter fun c => decide (c.label = some (PQ.P, u)) := by
      refine List.filter_congr fun c hc => ?_
      rcases hl c hc with h | h <;> simp [h]
    rw [hc] at hp
    rw [← (hp.map (Comp.val (D ω) σ)).prod_eq, List.map_append, List.prod_append]
    rfl
  simp only [Graph.termR, hlab1, hlab2, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, PFamily.op, hF, hP]
  simp only [Graph.dropLabels, hall, hval, hsplit]
  ring

end DropPVals

/-! ## Sums of expansions -/

section Bind

variable {k n : ℕ}

theorem forget_append_valR {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) (e : Fin k → ι) (E F : TExpansion k n) :
    (E ++ F).forget.valR PF D e = E.forget.valR PF D e + F.forget.valR PF D e := by
  funext ω
  simp [TExpansion.forget, Expansion.valR]

end Bind

/-! ## Lists with one component replaced -/

section Replace2

variable {α : Type*}

theorem mem_eraseIdx_of_ne {L : List α} {i : ℕ} {c d : α} (hc : L[i]? = some c)
    (hd : d ∈ L) (hne : d ≠ c) : d ∈ L.eraseIdx i := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hd
  rw [List.mem_eraseIdx_iff_getElem?]
  refine ⟨j, ?_, List.getElem?_eq_getElem hj⟩
  rintro rfl
  rw [List.getElem?_eq_getElem hj] at hc
  exact hne (Option.some.inj hc)

theorem mem_or_of_mem {L : List α} {i : ℕ} {c d : α} (hc : L[i]? = some c)
    (hd : d ∈ L) : d ∈ L.eraseIdx i ∨ d = c := by
  by_cases h : d = c
  · exact Or.inr h
  · exact Or.inl (mem_eraseIdx_of_ne hc hd h)

theorem perm_eraseIdx {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c) :
    L.Perm (c :: L.eraseIdx i) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  exact (List.getElem_cons_eraseIdx_perm hi).symm

theorem length_filter_eraseIdx {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c)
    (p : α → Bool) :
    (L.filter p).length = ((L.eraseIdx i).filter p).length + if p c then 1 else 0 := by
  rw [((perm_eraseIdx hc).filter p).length_eq, List.filter_cons]
  split_ifs <;> simp

theorem sum_map_eraseIdx {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c)
    (g : α → ℤ) : (L.map g).sum = ((L.eraseIdx i).map g).sum + g c := by
  rw [((perm_eraseIdx hc).map g).sum_eq]
  simp [add_comm]

end Replace2

/-! ## The invariants of the construction -/

section Inv

variable {k n : ℕ}

/-- `u` and `v` are joined by a `×`-dotted component. -/
def HasX (L : List (Comp (Atom k n))) (u v : Atom k n) : Prop :=
  ∃ d ∈ L, d.kind = .xdot ∧ (d.x = u ∧ d.y = v ∨ d.x = v ∧ d.y = u)

/-- `u` and `v` are joined by a solid component. -/
def HasS (L : List (Comp (Atom k n))) (u v : Atom k n) : Prop :=
  ∃ d ∈ L, d.kind.isSolid = true ∧ (d.x = u ∧ d.y = v ∨ d.x = v ∧ d.y = u)

/-- The weights `W_D`. -/
def Kind.step3_isWDB : Kind → Bool
  | .wD _ _ => true
  | _ => false

/-- The weights `(G_{xx})⁻¹`. -/
def Kind.isInvB : Kind → Bool
  | .inv _ => true
  | _ => false

/-- The number of `W_D` components. -/
def nWD (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => c.kind.step3_isWDB).length

/-- The labelled random components without minor and away from `X`: the factors of `𝒢` not yet
written by [II, (4.17)]. -/
def step3_pendB (X : Atom k n) (c : Comp (Atom k n)) : Bool :=
  c.label.isSome && c.kind.isRandom && c.minor.isEmpty && c.x != X && c.y != X

/-- The number of components with a minor. -/
def step3_nMin (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => !c.minor.isEmpty).length

/-- The number of weights `(G_{xx})⁻¹`. -/
def step3_nInv (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => c.kind.isInvB).length

/-- The number of pending components. -/
def step3_nPend (X : Atom k n) (L : List (Comp (Atom k n))) : ℕ := (L.filter (step3_pendB X)).length

/-- The size potential: it never grows along the construction and bounds the number of
components of every output. -/
def sizeΦ (D' : ℕ) (X : Atom k n) (L : List (Comp (Atom k n))) : ℕ :=
  L.length + (D' + 3) * (step3_nPend X L + step3_nMin L) + (D' + 1) * step3_nInv L

/-- The components of `Γ` without label other than dotted and `×`-dotted edges: the factor `Γ_ω`
of `Γ_ω P_x(𝒢)`. -/
def carryL (Γ : Graph k n) : List (Comp (Atom k n)) :=
  Γ.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)

/-- The clauses kept by every intermediate graph `T` of the construction for the input `Γ` at the
internal atom `X`, with Taylor degree `D'` and size bound `S`. -/
structure Base (D' S : ℕ) (X : Atom k n) (Γ T : Graph k n) : Prop where
  chain : Relation.ReflTransGen QElemStep ⟨n, Γ⟩ ⟨n, T⟩
  conn : T.ConnNoX
  internal : ∀ a b : Fin n, T.wavedThetaGraph.Reachable (.inr a) (.inr b)
  solid : ∀ c ∈ T.comps, c.kind.isSolid = true → c.x ≠ c.y ∧ HasX T.comps c.x c.y
  xapart : T.XdotApart
  excess : step3_eL T.comps = step3_eL Γ.comps
  nonred : Step3NonRedInt T.comps
  dc : Γ.DoublyConnected → T.Step3DCS .plus
  wf : ∀ c ∈ T.comps, c.WF
  noloop : ∀ c ∈ T.comps, c.kind = .dot → c.x ≠ c.y
  lab : ∀ c ∈ T.comps, c.label = none ∨ c.label = some (.P, X)
  good : ∀ c ∈ T.comps, c.label.isSome = true → c.isGoodKind = true
  minor : ∀ c ∈ T.comps, c.minor = [] ∨ (c.minor = [X] ∧
    (∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) ∧ c.x ≠ X ∧ c.y ≠ X ∧
      HasX T.comps c.x X ∧ HasX T.comps c.y X)
  inv : ∀ c ∈ T.comps, c.kind.isInvB = true → c.x = X ∧ c.y = X ∧ c.minor = []
  wd : ∀ c ∈ T.comps, c.kind.step3_isWDB = true → c.minor = []
  ord : Γ.ord + (D' + 1) * (nWD T.comps : ℤ) ≤ T.ord
  xright : X.isRight = true
  size : sizeΦ D' X T.comps ≤ S
  carry : (carryL Γ).Subperm T.comps
  blocks : ∀ u v, Γ.SameBlock u v → T.SameBlock u v

/-- The facts on the input graph used along the construction. -/
structure GIn (Γ : Graph k n) : Prop where
  plain : Γ.Plain
  xs : ∀ g ∈ Γ.comps, g.kind = .xdot → HasS Γ.comps g.x g.y
  sx : ∀ g ∈ Γ.comps, g.kind.isSolid = true → HasX Γ.comps g.x g.y
  nid : ∀ g ∈ Γ.comps, g.kind = .dot → g.x.isLeft = true ∨ g.y.isLeft = true

/-- A random component with the label `l`, without minor and not a weight `(G_{xx})⁻¹`, has an atom
in the block of `X`. -/
def Att (l : Option (PQ × Atom k n)) (X : Atom k n) (T : Graph k n) : Prop :=
  ∃ e ∈ T.comps, e.label = l ∧ e.kind.isRandom = true ∧ e.minor = [] ∧ e.kind.isInvB = false ∧
    ∃ u ∈ [e.x, e.y], T.SameBlock u X

/-- A labelled weight or edge is attached to the block of `X`, and the scaling order is strictly
higher: the outputs `Γ_ω P_x(𝒢̃_γ)`. -/
def ClsP (D' : ℕ) (X : Atom k n) (Γ T : Graph k n) : Prop :=
  Att (some (.P, X)) X T ∧ Γ.ord + 1 + (D' + 1) * (nWD T.comps : ℤ) ≤ T.ord

/-- No label, a weight or edge is attached to the block of `X`, and the scaling order is strictly
higher: the outputs `𝒢_ξ`. -/
def ClsLF (D' : ℕ) (X : Atom k n) (Γ T : Graph k n) : Prop :=
  T.LabelFree ∧ Att none X T ∧ Γ.ord + 1 + (D' + 1) * (nWD T.comps : ℤ) ≤ T.ord

/-- A component without minor and without label. -/
def baseC {V : Type*} (c : Comp V) : Comp V := { c with minor := [], label := none }

/-- Up to minors and labels, the components are those of `Γ` together with `×`-dotted edges
`u X`, where `u` is an atom of a random component of `Γ` not joined to `X` by a solid edge. -/
def LeadPerm (X : Atom k n) (Γ T : Graph k n) : Prop :=
  ∃ us : List (Atom k n), (∀ u ∈ us, ¬ HasS Γ.comps u X ∧
      ∃ g ∈ Γ.comps, g.kind.isRandom = true ∧ u ∈ [g.x, g.y]) ∧
    (T.comps.map baseC).Perm (Γ.comps.map baseC ++ us.map fun u => mkC .xdot u X)

/-- No label, and up to `×`-dotted edges the components are those of `Γ` with the labels and minors
removed: the leading term `𝒢`. -/
def ClsLead (X : Atom k n) (Γ T : Graph k n) : Prop := T.LabelFree ∧ LeadPerm X Γ T

/-- The three classes of the graphs after the label `P_x` is resolved. -/
def Cls (D' : ℕ) (X : Atom k n) (Γ T : Graph k n) : Prop :=
  ClsP D' X Γ T ∨ ClsLF D' X Γ T ∨ ClsLead X Γ T

theorem dotlab_of_wf {T : Graph k n} (hwf : ∀ c ∈ T.comps, c.WF) :
    ∀ c ∈ T.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
  intro c hc hk
  by_contra hl
  have := (hwf c hc).2 (by simpa [Option.isSome_iff_ne_none] using hl)
  rcases hk with hk | hk <;> rw [hk] at this <;> simp [Kind.isRandom] at this

end Inv

/-! ## The leading term -/

section Lead

variable {k n : ℕ}

theorem baseC_eq_iff {V : Type*} {c d : Comp V} (h : baseC c = baseC d) :
    c.kind = d.kind ∧ c.x = d.x ∧ c.y = d.y := by
  have h1 := congrArg Comp.kind h
  have h2 := congrArg Comp.x h
  have h3 := congrArg Comp.y h
  exact ⟨h1, h2, h3⟩

theorem mkC_xdot_baseC {V : Type*} {u X : V} {d : Comp V} (h : mkC .xdot u X = baseC d) :
    d.kind = .xdot ∧ d.x = u ∧ d.y = X := by
  have h1 := congrArg Comp.kind h
  have h2 := congrArg Comp.x h
  have h3 := congrArg Comp.y h
  exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem baseC_self {V : Type*} {c : Comp V} (hm : c.minor = []) (hl : c.label = none) :
    baseC c = c := by
  obtain ⟨κ, x, y, m, l⟩ := c
  simp only at hm hl
  subst hm hl
  rfl

/-- A component of `T` comes from a component of `Γ` or from one of the added `×`-dotted edges. -/
theorem lead_mem {X : Atom k n} {Γ T : Graph k n} {us : List (Atom k n)}
    (hp : (T.comps.map baseC).Perm (Γ.comps.map baseC ++ us.map fun u => mkC .xdot u X))
    {d : Comp (Atom k n)} (hd : d ∈ T.comps) :
    (∃ g ∈ Γ.comps, d.kind = g.kind ∧ d.x = g.x ∧ d.y = g.y) ∨
      ∃ u ∈ us, d.kind = .xdot ∧ d.x = u ∧ d.y = X := by
  have : baseC d ∈ Γ.comps.map baseC ++ us.map fun u => mkC .xdot u X :=
    hp.subset (List.mem_map_of_mem hd)
  rcases List.mem_append.1 this with h | h
  · obtain ⟨g, hg, hgd⟩ := List.mem_map.1 h
    exact Or.inl ⟨g, hg, baseC_eq_iff hgd.symm⟩
  · obtain ⟨u, hu, hud⟩ := List.mem_map.1 h
    exact Or.inr ⟨u, hu, mkC_xdot_baseC hud⟩

/-- A component of `Γ` has a copy in `T` up to minors and labels. -/
theorem lead_of_mem {X : Atom k n} {Γ T : Graph k n} {us : List (Atom k n)}
    (hp : (T.comps.map baseC).Perm (Γ.comps.map baseC ++ us.map fun u => mkC .xdot u X))
    {g : Comp (Atom k n)} (hg : g ∈ Γ.comps) : ∃ d ∈ T.comps, baseC d = baseC g := by
  have : baseC g ∈ T.comps.map baseC :=
    hp.symm.subset (List.mem_append_left _ (List.mem_map_of_mem hg))
  obtain ⟨d, hd, hdg⟩ := List.mem_map.1 this
  exact ⟨d, hd, hdg⟩

theorem lead_solid {X : Atom k n} {Γ T : Graph k n} (hL : LeadPerm X Γ T) {a b : Atom k n}
    (h : HasS T.comps a b) : HasS Γ.comps a b := by
  obtain ⟨us, -, hp⟩ := hL
  obtain ⟨d, hd, hk, hxy⟩ := h
  rcases lead_mem hp hd with ⟨g, hg, hk', hx, hy⟩ | ⟨u, -, hk', -, -⟩
  · exact ⟨g, hg, hk' ▸ hk, by rw [← hx, ← hy]; exact hxy⟩
  · rw [hk'] at hk
    cases hk

theorem lead_inv {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ) (hL : LeadPerm X Γ T)
    {d : Comp (Atom k n)} (hd : d ∈ T.comps) : d.kind.isInvB = false := by
  obtain ⟨us, -, hp⟩ := hL
  rcases lead_mem hp hd with ⟨g, hg, hk', -, -⟩ | ⟨u, -, hk', -, -⟩
  · rw [hk']
    have := (hG.plain g hg).2.1
    revert this
    cases g.kind <;> simp [Kind.isInvB]
  · rw [hk']
    rfl

theorem lead_dot {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ) (hL : LeadPerm X Γ T)
    {d : Comp (Atom k n)} (hd : d ∈ T.comps) (hk : d.kind = .dot) :
    d.x.isLeft = true ∨ d.y.isLeft = true := by
  obtain ⟨us, -, hp⟩ := hL
  rcases lead_mem hp hd with ⟨g, hg, hk', hx, hy⟩ | ⟨u, -, hk', -, -⟩
  · rw [hx, hy]
    exact hG.nid g hg (hk' ▸ hk)
  · rw [hk'] at hk
    cases hk

/-- A `×`-dotted edge of `T` without solid edge is one of the added edges `u X`; without it the
graph keeps the form of the leading term, and `u` is an atom of a random component of `Γ`. -/
theorem lead_erase {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ) (hL : LeadPerm X Γ T)
    {i : ℕ} {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (hk : c.kind = .xdot)
    (hns : ¬ HasS T.comps c.x c.y) (co : Coeff) :
    LeadPerm X Γ ⟨T.comps.eraseIdx i, co⟩ ∧ c.y = X ∧
      ∃ g ∈ Γ.comps, g.kind.isRandom = true ∧ c.x ∈ [g.x, g.y] := by
  obtain ⟨us, hus, hp⟩ := hL
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  have hmem : baseC c ∈ Γ.comps.map baseC ++ us.map fun u => mkC .xdot u X :=
    hp.subset (List.mem_map_of_mem hcT)
  rcases List.mem_append.1 hmem with h | h
  · exfalso
    obtain ⟨g, hg, hgc⟩ := List.mem_map.1 h
    obtain ⟨hk', hx, hy⟩ := baseC_eq_iff hgc
    obtain ⟨s, hs, hsk, hsxy⟩ := hG.xs g hg (hk'.trans hk)
    obtain ⟨d, hd, hds⟩ := lead_of_mem hp hs
    obtain ⟨hk'', hx', hy'⟩ := baseC_eq_iff hds
    apply hns
    refine ⟨d, hd, hk''.symm ▸ hsk, ?_⟩
    rw [hx', hy', ← hx, ← hy]
    exact hsxy
  · obtain ⟨u, hu, huc⟩ := List.mem_map.1 h
    obtain ⟨-, hx, hy⟩ := mkC_xdot_baseC huc
    refine ⟨⟨us.erase u, fun v hv => hus v (List.mem_of_mem_erase hv), ?_⟩, hy,
      by rw [hx]; exact (hus u hu).2⟩
    have h1 : (T.comps.map baseC).Perm (baseC c :: (T.comps.eraseIdx i).map baseC) := by
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
      have := (List.getElem_cons_eraseIdx_perm hi).symm.map baseC
      simpa using this
    have h2 : (Γ.comps.map baseC ++ us.map fun u => mkC .xdot u X).Perm
        (mkC .xdot u X :: (Γ.comps.map baseC ++ (us.erase u).map fun u => mkC .xdot u X)) := by
      have h3 := ((List.perm_cons_erase hu).map fun u => mkC .xdot u X)
      rw [List.map_cons] at h3
      exact (h3.append_left _).trans List.perm_middle
    rw [huc] at h2
    exact (h1.symm.trans (hp.trans h2)).cons_inv

/-- At the end of the construction the leading term has the components of `Γ` without labels,
in some order. -/
theorem lead_final {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ) (hL : LeadPerm X Γ T)
    (hmin : ∀ d ∈ T.comps, d.minor = []) (hlf : T.LabelFree)
    (hN2 : ∀ c ∈ T.comps, c.kind = .xdot → HasS T.comps c.x c.y) :
    T.comps.Perm Γ.dropLabels.comps := by
  obtain ⟨us, hus, hp⟩ := hL
  have hnil : us = [] := by
    rcases us with _ | ⟨u, us⟩
    · rfl
    · exfalso
      have hx : mkC .xdot u X ∈ Γ.comps.map baseC ++ (u :: us).map fun u => mkC .xdot u X :=
        List.mem_append_right _ (List.mem_map_of_mem (List.mem_cons_self ..))
      obtain ⟨d, hd, hdx⟩ := List.mem_map.1 (hp.symm.subset hx)
      obtain ⟨hk, hdx', hdy⟩ := mkC_xdot_baseC hdx.symm
      have := lead_solid ⟨u :: us, hus, hp⟩ (hN2 d hd hk)
      rw [hdx', hdy] at this
      exact (hus u (List.mem_cons_self ..)).1 this
  subst hnil
  rw [List.map_nil, List.append_nil] at hp
  have e1 : T.comps.map baseC = T.comps := by
    conv_rhs => rw [← List.map_id T.comps]
    exact List.map_congr_left fun d hd => baseC_self (hmin d hd) (hlf d hd)
  have e2 : Γ.comps.map baseC = Γ.dropLabels.comps := by
    simp only [Graph.dropLabels]
    refine List.map_congr_left fun g hg => ?_
    have hm := (hG.plain g hg).1
    obtain ⟨κ, x, y, m, l⟩ := g
    simp only at hm
    subst hm
    rfl
  rw [e1, e2] at hp
  exact hp

/-- An atom of a random component of `Γ` is an atom of a random component of `T` without label and
minor that is not a weight `(G_{xx})⁻¹`, in the leading term. -/
theorem lead_witness {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ) (hL : LeadPerm X Γ T)
    (hmin : ∀ d ∈ T.comps, d.minor = []) (hlf : T.LabelFree) {u : Atom k n}
    (hu : ∃ g ∈ Γ.comps, g.kind.isRandom = true ∧ u ∈ [g.x, g.y]) :
    ∃ e ∈ T.comps, e.label = none ∧ e.kind.isRandom = true ∧ e.minor = [] ∧
      e.kind.isInvB = false ∧ u ∈ [e.x, e.y] := by
  obtain ⟨g, hg, hgr, hug⟩ := hu
  obtain ⟨us, hus, hp⟩ := hL
  obtain ⟨e, he, heg⟩ := lead_of_mem hp hg
  obtain ⟨hk, hx, hy⟩ := baseC_eq_iff heg
  refine ⟨e, he, hlf e he, hk ▸ hgr, hmin e he, lead_inv hG ⟨us, hus, hp⟩ he, ?_⟩
  rw [hx, hy]
  exact hug

end Lead

/-! ## Connectivity transfers -/

section ConnTransfer

variable {k n : ℕ}

theorem edgeNoX_reach_of_comp {T : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ T.comps)
    (hk : c.kind ≠ .xdot) : T.edgeGraphNoX.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

theorem edgeNoX_reach_of_dg {T : Graph k n} {a b : Atom k n}
    (h : (step3_dg T.comps).Reachable a b) : T.edgeGraphNoX.Reachable a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, hxy⟩ := step3_dg_adj.1 hadj
    have := edgeNoX_reach_of_comp hc (by rw [hk]; simp)
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this.trans ih
    · exact this.symm.trans ih

/-- Connectivity without `×`-dotted edges passes to a graph on the same atoms in which the ends of
every component other than a `×`-dotted edge are joined. -/
theorem connNoX_transfer {T T' : Graph k n} (h : T.ConnNoX)
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

theorem wt_reach_of_comp {T : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ T.comps)
    (hk : c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) :
    T.wavedThetaGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

/-- The waved and `Θ` connectivity of the internal atoms passes to a graph on the same atoms
containing the waved and diffusive components. -/
theorem internal_transfer {T T' : Graph k n}
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

theorem molReach_of_dg {T : Graph k n} {a b : Atom k n}
    (h : (step3_dg T.comps).Reachable a b) : T.molGraph.Reachable a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, hxy⟩ := step3_dg_adj.1 hadj
    have := Graph.molReach_of_comp hc (by rw [hk]; rfl)
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this.trans ih
    · exact this.symm.trans ih

/-- A doubly connected structure passes to a graph on the same atoms. -/
theorem Graph.Step3DCT.same {bc : Charge} {T T' : Graph k n} {L : List (Step3TC k n)}
    (h : T.Step3DCT bc L) (L' : List (Step3TC k n)) (hmap : L'.map Prod.fst = T'.comps)
    (hbl : ∀ p ∈ L', p.2 = some false → p.1.kind.isDiffusive = true)
    (hbu : ∀ p ∈ L', p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.step3_blueC bc = true)
    (hmol : ∀ c ∈ T.comps, c.kind.joinsMol = true → T'.molGraph.Reachable c.x c.y)
    (hedge : ∀ t : Bool, ∀ p ∈ L, p.2 = some t → ∀ a b, p.1.x = Sum.inr a →
      p.1.y = Sum.inr b → (T'.step3_netT L' t).Reachable a b) : T'.Step3DCT bc L' := by
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
theorem step3_drop_one (g : Graph k m) {i : ℕ} {c : Comp (Atom k m)} (hc : g.comps[i]? = some c)
    (hk : c.kind = .dot) (hr : (step3_dg (g.comps.eraseIdx i)).Reachable c.x c.y) :
    let g₁ : Graph k m := ⟨g.comps.eraseIdx i, g.coeff⟩
    QElemStep ⟨m, g⟩ ⟨m, g₁⟩ ∧ step3_eL g₁.comps + 1 = step3_eL g.comps ∧ g₁.ord + 2 = g.ord ∧
      (∀ d ∈ g.comps, d.kind ≠ .dot → d ∈ g₁.comps) ∧
      (g₁.comps.filter fun d => !decide (d.kind = .dot)).Perm
        (g.comps.filter fun d => !decide (d.kind = .dot)) ∧
      (∀ u v, g₁.SameBlock u v ↔ g.SameBlock u v) ∧
      (g.Step3DCS .plus → g₁.Step3DCS .plus) ∧ (g.ConnNoX → g₁.ConnNoX) ∧
      g₁.wavedThetaGraph = g.wavedThetaGraph := by
  intro g₁
  have hmem : ∀ d ∈ g.comps, d.kind ≠ .dot → d ∈ g₁.comps := by
    intro d hd hdk
    exact mem_eraseIdx_of_ne hc hd (fun h => hdk (h ▸ hk))
  have hr₁ : (step3_dg g₁.comps).Reachable c.x c.y := hr
  obtain ⟨he, hb⟩ := eL_eraseIdx_red hc hk hr
  refine ⟨QElemStep.dropDot i g c hc hk hr, he, ?_, hmem, ?_, hb, ?_, ?_, ?_⟩
  · simp only [Graph.ord, g₁]
    rw [sum_map_eraseIdx hc (fun c => c.kind.ord), hk]
    simp only [Kind.ord]
    ring
  · have h := (perm_eraseIdx hc).filter (fun d => !decide (d.kind = .dot))
    rw [List.filter_cons_of_neg (by simp [hk])] at h
    exact h.symm
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
        simp [Kind.isDiffusive, Kind.step3_blueC] at this
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

/-! ## The final normalization -/

section Final

variable {k n : ℕ}

theorem Step3MergeSpec.hlab {Γ : Graph k n} {t : Tracked k n} (hs : Step3MergeSpec Γ t)
    (hlab : ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none) :
    ∀ c' ∈ t.g.comps, (c'.kind = .dot ∨ c'.kind = .xdot) → c'.label = none := by
  intro c' hc' hk'
  rw [hs.comps_eq, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hmc⟩ := hc'
  rw [step3_mergeComp_label hmc]
  rcases step3_mergeComp_kind hmc with h | ⟨ch, hch, hch'⟩
  · rw [hlab c hc (by rwa [h] at hk')]
    rfl
  · rw [hch'] at hk'
    rcases hk' with h | h <;> cases h

theorem labels_length_le {T : Graph k n} {ℓ : PQ × Atom k n}
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

theorem Comp.map_WF {V W : Type*} (f : V → W) {c : Comp V} (h : c.WF) : (c.map f).WF :=
  ⟨fun hw => by simp only [Comp.map] at hw ⊢; rw [h.1 hw],
    fun hl => h.2 (by simpa [Comp.map] using hl)⟩

/-- `filterMap` of a function that is `some ∘ g` on the list is the map of `g`. -/
theorem filterMap_eq_map_of {α β : Type*} (F : α → Option β) (g : α → β) :
    ∀ L : List α, (∀ a ∈ L, F a = some (g a)) → L.filterMap F = L.map g
  | [], _ => rfl
  | a :: L, h => by
    rw [List.filterMap_cons_some (h a (List.mem_cons_self ..)), List.map_cons,
      filterMap_eq_map_of F g L fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem mem_carryL {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ carryL Γ) :
    c ∈ Γ.comps ∧ c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot := by
  unfold carryL at hc
  rw [List.mem_filter] at hc
  simpa using hc

end Final

/-! ## Transfer of the invariants -/

section Transfer

variable {k n : ℕ}

theorem filter_dot_eraseIdx {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) (hk : c.kind ≠ .dot) :
    ((L.eraseIdx i).filter fun c => decide (c.kind = .dot)).Perm
      (L.filter fun c => decide (c.kind = .dot)) := by
  have h := (perm_eraseIdx hc).filter (fun c => decide (c.kind = .dot))
  rw [List.filter_cons_of_neg (by simpa using hk)] at h
  exact h.symm

theorem filter_dot_append {L new : List (Comp (Atom k n))}
    (hnew : ∀ d ∈ new, d.kind ≠ .dot) :
    (L ++ new).filter (fun c => decide (c.kind = .dot)) =
      L.filter fun c => decide (c.kind = .dot) := by
  have : new.filter (fun c => decide (c.kind = .dot)) = [] :=
    List.filter_eq_nil_iff.2 (fun d hd => by simpa using hnew d hd)
  rw [List.filter_append, this, List.append_nil]

/-- The needed dotted edges between internal atoms depend only on the dotted components. -/
theorem nonRedInt_of_perm {L L' : List (Comp (Atom k n))} (h : Step3NonRedInt L)
    (hp : (L'.filter fun c => decide (c.kind = .dot)).Perm
      (L.filter fun c => decide (c.kind = .dot))) : Step3NonRedInt L' := by
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
  have : step3_dg (M.filter (fun c => decide (c.kind = .dot)) ++
      L.filter fun c => !decide (c.kind = .dot)) = step3_dg M := by
    apply dg_congr
    intro d hd
    simp [List.mem_append, List.mem_filter, hd]
  rw [this]
  exact hr

/-- A dotted edge between two blocks keeps the needed dotted edges needed. -/
theorem nonRedInt_cons_dot {c : Comp (Atom k n)} {L : List (Comp (Atom k n))}
    (h : Step3NonRedInt L) (hk : c.kind = .dot) (hr : ¬ (step3_dg L).Reachable c.x c.y) :
    Step3NonRedInt (c :: L) := by
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
      have hee : (step3_dg L).Reachable L[j].x L[j].y := by
        rw [dg_perm hL]
        exact step3_dg_reach_of_mem (List.mem_cons_self ..) hek
      have hm : ∀ a b, (step3_dg (L.eraseIdx j)).Reachable a b → (step3_dg L).Reachable a b :=
        fun a b => dg_reach_mono fun d hd _ => List.mem_of_mem_eraseIdx hd
      exact ((hm _ _ h1).symm.trans hee).trans (hm _ _ h2).symm
    · apply hr
      have hee : (step3_dg L).Reachable L[j].x L[j].y := by
        rw [dg_perm hL]
        exact step3_dg_reach_of_mem (List.mem_cons_self ..) hek
      have hm : ∀ a b, (step3_dg (L.eraseIdx j)).Reachable a b → (step3_dg L).Reachable a b :=
        fun a b => dg_reach_mono fun d hd _ => List.mem_of_mem_eraseIdx hd
      exact ((hm _ _ h2).trans hee.symm).trans (hm _ _ h1)

theorem sizeΦ_le_of_filter {D' : ℕ} {X : Atom k n} {L L' : List (Comp (Atom k n))}
    (hl : L'.length ≤ L.length)
    (hp : (L'.filter (step3_pendB X)).length ≤ (L.filter (step3_pendB X)).length)
    (hm : step3_nMin L' ≤ step3_nMin L) (hi : step3_nInv L' ≤ step3_nInv L) : sizeΦ D' X L' ≤ sizeΦ D' X L := by
  unfold sizeΦ step3_nPend
  have := Nat.mul_le_mul_left (D' + 3) (Nat.add_le_add hp hm)
  have := Nat.mul_le_mul_left (D' + 1) hi
  omega

theorem length_filter_eraseIdx_le {L : List (Comp (Atom k n))} (i : ℕ)
    (p : Comp (Atom k n) → Bool) : ((L.eraseIdx i).filter p).length ≤ (L.filter p).length :=
  ((List.eraseIdx_sublist L i).filter p).length_le

end Transfer

/-! ## Removing the `×`-dotted edges without solid edge -/

section Clean

variable {k n : ℕ}

/-- Some solid component joins `u` and `v`. -/
def step3_solidJoinB (L : List (Comp (Atom k n))) (u v : Atom k n) : Bool :=
  L.any fun d => d.kind.isSolid && ((d.x == u && d.y == v) || (d.x == v && d.y == u))

theorem solidJoinB_iff (L : List (Comp (Atom k n))) (u v : Atom k n) :
    step3_solidJoinB L u v = true ↔ HasS L u v := by
  simp only [step3_solidJoinB, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, HasS]

/-- A `×`-dotted component whose ends are joined by no solid component. -/
def step3_badB (L : List (Comp (Atom k n))) (c : Comp (Atom k n)) : Bool :=
  decide (c.kind = .xdot) && !step3_solidJoinB L c.x c.y

/-- The number of `×`-dotted components whose ends are joined by no solid component. -/
def step3_nBad (L : List (Comp (Atom k n))) : ℕ := (L.filter (step3_badB L)).length

theorem nonRedInt_perm {L L' : List (Comp (Atom k n))} (h : Step3NonRedInt L) (hp : L.Perm L') :
    Step3NonRedInt L' := fun e M hM => h e M (hp.trans hM)

theorem hasS_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ d, d.kind.isSolid = true → (d ∈ L ↔ d ∈ L')) (u v : Atom k n) :
    HasS L u v ↔ HasS L' u v := by
  constructor
  · rintro ⟨d, hd, hk, hxy⟩
    exact ⟨d, (h d hk).1 hd, hk, hxy⟩
  · rintro ⟨d, hd, hk, hxy⟩
    exact ⟨d, (h d hk).2 hd, hk, hxy⟩

theorem hasX_of_ne {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) {u v : Atom k n} (h : HasX L u v)
    (hne : ¬ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) : HasX (L.eraseIdx i) u v := by
  obtain ⟨d, hd, hk, hxy⟩ := h
  refine ⟨d, mem_eraseIdx_of_ne hc hd ?_, hk, hxy⟩
  rintro rfl
  exact hne hxy

theorem hasX_mono {L L' : List (Comp (Atom k n))} (h : ∀ d ∈ L, d ∈ L')
    {u v : Atom k n} (hx : HasX L u v) : HasX L' u v := by
  obtain ⟨d, hd, hk, hxy⟩ := hx
  exact ⟨d, h d hd, hk, hxy⟩

/-- Removing a component other than a dotted, waved or diffusive one keeps a doubly connected
structure; the components in its place keep the blue nets joined. -/
theorem dcs_replace {T T' : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n)))
    (hT' : T'.comps = T.comps.eraseIdx i ++ new)
    (hjm : c.kind.joinsMol = false) (hdf : c.kind.isDiffusive = false) (hng : c.kind ≠ .ghost)
    (hmolnew : ∀ d ∈ T.comps, d.kind.joinsMol = true → d ≠ c → T'.molGraph.Reachable d.x d.y)
    (hblue : c.kind = .G .plus → ∀ a b, c.x = Sum.inr a → c.y = Sum.inr b →
      ∀ L₀ : List (Step3TC k n), L₀.map Prod.fst = T.comps.eraseIdx i →
        (T'.step3_netT (L₀ ++ new.map fun d => (d, if d.kind = .G .plus then some true else none))
          true).Reachable a b)
    (h : T.Step3DCS .plus) : T'.Step3DCS .plus := by
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
        simp [hd, Kind.step3_blueC]
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
        | G ch => cases ch <;> simp_all [Kind.step3_blueC]
        | _ => simp_all [Kind.step3_blueC]
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

/-- A sub-multiset of a list that does not contain the entry with index `i` is a sub-multiset of the
list without that entry. -/
theorem subperm_eraseIdx {α : Type*} {l L : List α} {i : ℕ} {c : α} (h : l.Subperm L)
    (hc : L[i]? = some c) (hn : c ∉ l) : l.Subperm (L.eraseIdx i) := by
  obtain ⟨l', hp, hs⟩ := (perm_eraseIdx hc).subperm_left.1 h
  have hn' : c ∉ l' := fun h => hn (hp.subset h)
  rcases List.sublist_cons_iff.1 hs with hs | ⟨r, rfl, -⟩
  · exact ⟨l', hp, hs⟩
  · exact absurd (List.mem_cons_self ..) hn'

/-- The term of `1_{u ≠ v} = 1 - 1_{u = v}` without the `×`-dotted edge. -/
theorem clean_drop {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T)
    (hmin : ∀ c ∈ T.comps, c.minor = []) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hk : c.kind = .xdot) (hns : ¬ HasS T.comps c.x c.y)
    (hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i, T.coeff⟩⟩) :
    Base D' S X Γ ⟨T.comps.eraseIdx i, T.coeff⟩ ∧
      (∀ u v, (⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n).SameBlock u v ↔ T.SameBlock u v) ∧
      (⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n).ord = T.ord ∧
      nWD (T.comps.eraseIdx i) = nWD T.comps ∧
      (∀ d ∈ T.comps, d.kind ≠ .xdot → d ∈ T.comps.eraseIdx i) := by
  set g : Graph k n := ⟨T.comps.eraseIdx i, T.coeff⟩ with hg
  have hin : ∀ d ∈ T.comps, d.kind ≠ .xdot → d ∈ g.comps :=
    fun d hd hdk => mem_eraseIdx_of_ne hc hd (fun h => hdk (h ▸ hk))
  have hdots := filter_dot_eraseIdx hc (by rw [hk]; simp)
  obtain ⟨hdg, heL⟩ := dg_eL_of_filter_perm hdots
  have hsb : ∀ u v, g.SameBlock u v ↔ T.SameBlock u v := fun u v => by
    change (step3_dg g.comps).Reachable u v ↔ (step3_dg T.comps).Reachable u v
    rw [hdg]
  have hordg : g.ord = T.ord := by
    simp only [Graph.ord, hg]
    rw [sum_map_eraseIdx hc (fun c => c.kind.ord) (L := T.comps), hk]
    simp [Kind.ord]
  have hnw : nWD (T.comps.eraseIdx i) = nWD T.comps := by
    unfold nWD
    rw [length_filter_eraseIdx hc (fun c => c.kind.step3_isWDB) (L := T.comps), hk]
    simp [Kind.step3_isWDB]
  refine ⟨⟨hB.chain.tail hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hB.xright, ?_, ?_, ?_⟩, hsb, hordg, hnw, hin⟩
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
  · exact fun d hd => hB.good d (List.mem_of_mem_eraseIdx hd)
  · exact fun d hd => Or.inl (hmin d (List.mem_of_mem_eraseIdx hd))
  · exact fun d hd => hB.inv d (List.mem_of_mem_eraseIdx hd)
  · exact fun d hd => hB.wd d (List.mem_of_mem_eraseIdx hd)
  · rw [hordg, hnw]
    exact hB.ord
  · refine le_trans (sizeΦ_le_of_filter ?_ (length_filter_eraseIdx_le i _)
      (length_filter_eraseIdx_le i _) (length_filter_eraseIdx_le i _)) hB.size
    exact (List.eraseIdx_sublist _ _).length_le
  · exact subperm_eraseIdx hB.carry hc fun h => (mem_carryL h).2.2.2 hk
  · exact fun u v h => (hsb u v).2 (hB.blocks u v h)

/-- The term of `1_{u ≠ v} = 1 - 1_{u = v}` with a dotted edge in place of the `×`-dotted edge. -/
theorem clean_dot {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T)
    (hmin : ∀ c ∈ T.comps, c.minor = []) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hk : c.kind = .xdot) (hns : ¬ HasS T.comps c.x c.y)
    (hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩⟩)
    (hxa : (⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ : Graph k n).XdotApart) :
    Base D' S X Γ ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ ∧
      (∀ u v, T.SameBlock u v →
        (⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ : Graph k n).SameBlock u v) ∧
      (⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ : Graph k n).ord = T.ord + 2 ∧
      nWD (T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) = nWD T.comps ∧
      (∀ d ∈ T.comps, d.kind ≠ .xdot → d ∈ T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) := by
  set g : Graph k n := ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩ with hg
  have hin : ∀ d ∈ T.comps, d.kind ≠ .xdot → d ∈ g.comps :=
    fun d hd hdk => List.mem_append_left _ (mem_eraseIdx_of_ne hc hd (fun h => hdk (h ▸ hk)))
  have hdots := filter_dot_eraseIdx hc (by rw [hk]; simp)
  obtain ⟨hdg, heL⟩ := dg_eL_of_filter_perm hdots
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  have hnr : ¬ (step3_dg (T.comps.eraseIdx i)).Reachable c.x c.y := by
    rw [hdg]
    exact hB.xapart c hcT hk
  have hperm : g.comps.Perm (mkC .dot c.x c.y :: T.comps.eraseIdx i) :=
    List.perm_append_singleton _ _
  have hmono : ∀ u v, T.SameBlock u v → g.SameBlock u v := by
    intro u v h
    exact dg_reach_mono (fun d hd hdk => hin d hd (by rw [hdk]; simp)) h
  have hordg : g.ord = T.ord + 2 := by
    simp only [Graph.ord, hg, List.map_append, List.sum_append]
    rw [sum_map_eraseIdx hc (fun c => c.kind.ord) (L := T.comps), hk]
    simp [Kind.ord, mkC]
    ring
  have hnw : nWD (T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) = nWD T.comps := by
    unfold nWD
    rw [length_filter_eraseIdx hc (fun c => c.kind.step3_isWDB) (L := T.comps), hk, List.filter_append]
    simp [Kind.step3_isWDB, mkC]
  have hfx : ∀ d ∈ g.comps, d ∈ T.comps.eraseIdx i ∨ d = mkC .dot c.x c.y := by
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)
  refine ⟨⟨hB.chain.tail hstep, ?_, ?_, ?_, hxa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hB.xright, ?_, ?_, ?_⟩, hmono, hordg, hnw, hin⟩
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
    · simp [mkC, Kind.isInvB] at hdi
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
    · rw [List.filter_append, List.length_append, length_filter_eraseIdx hc (step3_pendB X)]
      simp [step3_pendB, mkC, Kind.isRandom]
    · unfold step3_nMin
      rw [List.filter_append, List.length_append, length_filter_eraseIdx hc]
      simp [mkC]
    · unfold step3_nInv
      rw [List.filter_append, List.length_append, length_filter_eraseIdx hc]
      simp [mkC, Kind.isInvB]
  · exact (subperm_eraseIdx hB.carry hc fun h => (mem_carryL h).2.2.2 hk).trans
      (List.sublist_append_left _ _).subperm
  · exact fun u v h => hmono u v (hB.blocks u v h)

end CleanSteps

/-! ## The phase of the `×`-dotted edges without solid edge -/

section CleanPhase

variable {k n : ℕ}

theorem step3_oXdotT_eq {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hk : c.kind = .xdot) (hl : c.label = none)
    (hs : step3_solidJoinB T.comps c.x c.y = false) :
    oXdotT i T = [Tracked.self ⟨T.comps.eraseIdx i, T.coeff⟩,
      Tracked.self ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩] := by
  unfold step3_solidJoinB at hs
  simp only [oXdotT, hc]
  rw [ite_eq_left ⟨hk, hl, hs⟩]

theorem badB_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ d, d.kind.isSolid = true → (d ∈ L ↔ d ∈ L')) (c : Comp (Atom k n)) :
    step3_badB L c = step3_badB L' c := by
  have : step3_solidJoinB L c.x c.y = step3_solidJoinB L' c.x c.y := by
    rw [Bool.eq_iff_iff, solidJoinB_iff, solidJoinB_iff]
    exact hasS_congr h _ _
  simp only [step3_badB, this]

/-- An attached component passes to a graph that keeps it and maps blocks into blocks. -/
theorem att_transfer {l : Option (PQ × Atom k n)} {X : Atom k n} {T T' : Graph k n}
    (h : Att l X T)
    (hkeep : ∀ e ∈ T.comps, e.kind.isRandom = true → e.minor = [] → e.kind.isInvB = false →
      (∃ u ∈ [e.x, e.y], T.SameBlock u X) → e ∈ T'.comps)
    (hsb : ∀ u v, T.SameBlock u v → T'.SameBlock u v) : Att l X T' := by
  obtain ⟨e, he, hel, her, hem, hei, u, hu, hub⟩ := h
  exact ⟨e, hkeep e he her hem hei ⟨u, hu, hub⟩, hel, her, hem, hei, u, hu, hsb _ _ hub⟩

/-- The classes `ClsP`, `ClsLF` pass to a graph that keeps the random components, has no new
label, maps blocks into blocks and does not lower the scaling order. -/
theorem cls_clean {D' : ℕ} {X : Atom k n} {Γ T T' : Graph k n}
    (hcls : ClsP D' X Γ T ∨ ClsLF D' X Γ T)
    (hkeep : ∀ d ∈ T.comps, d.kind.isRandom = true → d ∈ T'.comps)
    (hlab : ∀ d ∈ T'.comps, d ∈ T.comps ∨ d.label = none)
    (hsb : ∀ u v, T.SameBlock u v → T'.SameBlock u v)
    (hord : T.ord ≤ T'.ord) (hnw : nWD T'.comps = nWD T.comps) :
    ClsP D' X Γ T' ∨ ClsLF D' X Γ T' := by
  have hk : ∀ e ∈ T.comps, e.kind.isRandom = true → e.minor = [] → e.kind.isInvB = false →
      (∃ u ∈ [e.x, e.y], T.SameBlock u X) → e ∈ T'.comps := fun e he her _ _ _ => hkeep e he her
  rcases hcls with ⟨ha, ho⟩ | ⟨hlf, ha, ho⟩
  · exact Or.inl ⟨att_transfer ha hk hsb, by rw [hnw]; linarith⟩
  · refine Or.inr ⟨?_, att_transfer ha hk hsb, by rw [hnw]; linarith⟩
    intro d hd
    rcases hlab d hd with h | h
    · exact hlf d h
    · exact h

end CleanPhase

/-! ## Replacing a random component -/

section ReplaceStep

variable {k n : ℕ}

theorem Kind.random_facts {κ : Kind} (h : κ.isRandom = true) :
    κ.joinsMol = false ∧ κ.isDiffusive = false ∧ κ ≠ .ghost ∧ κ ≠ .dot ∧ κ ≠ .xdot ∧
      (κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true → False) := by
  cases κ <;> simp_all [Kind.isRandom, Kind.joinsMol, Kind.isDiffusive]

theorem ord_replace {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n))) (co : Coeff) :
    (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord =
      T.ord - c.kind.ord + (new.map fun d => d.kind.ord).sum := by
  simp only [Graph.ord, List.map_append, List.sum_append]
  rw [sum_map_eraseIdx hc (fun c => c.kind.ord) (L := T.comps)]
  ring

theorem count_replace {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) (new : List (Comp (Atom k n))) (p : Comp (Atom k n) → Bool) :
    ((L.eraseIdx i ++ new).filter p).length + (if p c then 1 else 0) =
      (L.filter p).length + (new.filter p).length := by
  rw [List.filter_append, List.length_append, length_filter_eraseIdx hc p]
  ring

/-- The clauses `Base` pass to the graph in which the random component with index `i` is replaced
by the random components `new`. -/
theorem step3_base_replace {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T)
    {i : ℕ} {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n)))
    (co : Coeff) (hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i ++ new, co⟩⟩)
    (hck : c.kind.isRandom = true)
    (hnr : ∀ d ∈ new, d.kind.isRandom = true)
    (hconn : (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).edgeGraphNoX.Reachable c.x c.y)
    (hsol : ∀ d ∈ new, d.kind.isSolid = true → d.x ≠ d.y ∧ HasX T.comps d.x d.y)
    (hblue : c.kind = .G .plus → c.x.isRight = true → c.y.isRight = true →
      (∃ d ∈ new, d.kind = .G .plus ∧ d.x = c.x ∧ d.y = c.y) ∨
      (∃ d₁ ∈ new, ∃ d₂ ∈ new, d₁.kind = .G .plus ∧ d₂.kind = .G .plus ∧ d₁.x = c.x ∧
        d₁.y = X ∧ d₂.x = X ∧ d₂.y = c.y))
    (hwf : ∀ d ∈ new, d.WF)
    (hlab : ∀ d ∈ new, d.label = none ∨ d.label = some (.P, X))
    (hcc : c ∉ carryL Γ)
    (hgood : ∀ d ∈ new, d.label.isSome = true → d.isGoodKind = true)
    (hminor : ∀ d ∈ new, d.minor = [] ∨ (d.minor = [X] ∧
      (∃ ch, d.kind = .G ch ∨ d.kind = .weight ch ∨ d.kind = .light ch) ∧ d.x ≠ X ∧ d.y ≠ X ∧
        HasX T.comps d.x X ∧ HasX T.comps d.y X))
    (hinv : ∀ d ∈ new, d.kind.isInvB = true → d.x = X ∧ d.y = X ∧ d.minor = [])
    (hwd : ∀ d ∈ new, d.kind.step3_isWDB = true → d.minor = [])
    (hord : Γ.ord + (D' + 1) * (nWD (T.comps.eraseIdx i ++ new) : ℤ) ≤
      (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord)
    (hsize : sizeΦ D' X (T.comps.eraseIdx i ++ new) ≤ S) :
    Base D' S X Γ ⟨T.comps.eraseIdx i ++ new, co⟩ := by
  set g : Graph k n := ⟨T.comps.eraseIdx i ++ new, co⟩ with hg
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  have hndot : ∀ d ∈ new, d.kind ≠ .dot ∧ d.kind ≠ .xdot := fun d hd =>
    ⟨(Kind.random_facts (hnr d hd)).2.2.2.1, (Kind.random_facts (hnr d hd)).2.2.2.2.1⟩
  have hcnd : c.kind ≠ .dot ∧ c.kind ≠ .xdot :=
    ⟨(Kind.random_facts hck).2.2.2.1, (Kind.random_facts hck).2.2.2.2.1⟩
  have hin : ∀ d ∈ T.comps, d ≠ c → d ∈ g.comps :=
    fun d hd hne => List.mem_append_left _ (mem_eraseIdx_of_ne hc hd hne)
  have hfx : ∀ d ∈ g.comps, d ∈ T.comps ∨ d ∈ new := by
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact Or.inl (List.mem_of_mem_eraseIdx h)
    · exact Or.inr h
  have hdots : (g.comps.filter fun c => decide (c.kind = .dot)).Perm
      (T.comps.filter fun c => decide (c.kind = .dot)) := by
    change ((T.comps.eraseIdx i ++ new).filter _).Perm _
    rw [filter_dot_append (fun d hd => (hndot d hd).1)]
    exact filter_dot_eraseIdx hc hcnd.1
  obtain ⟨hdg, heL⟩ := dg_eL_of_filter_perm hdots
  have hsb : ∀ u v, g.SameBlock u v ↔ T.SameBlock u v := fun u v => by
    change (step3_dg g.comps).Reachable u v ↔ (step3_dg T.comps).Reachable u v
    rw [hdg]
  have hX : ∀ u v, HasX T.comps u v → HasX g.comps u v := by
    intro u v ⟨d, hd, hk, hxy⟩
    exact ⟨d, hin d hd (fun h => hcnd.2 (h ▸ hk)), hk, hxy⟩
  have hX' : ∀ u v, HasX g.comps u v → HasX T.comps u v := by
    intro u v ⟨d, hd, hk, hxy⟩
    rcases hfx d hd with h | h
    · exact ⟨d, h, hk, hxy⟩
    · exact absurd hk (hndot d h).2
  refine ⟨hB.chain.tail hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hord,
    hB.xright, hsize, ?_, ?_⟩
  · refine connNoX_transfer hB.conn fun d hd hdk => ?_
    by_cases hdc : d = c
    · subst hdc
      exact hconn
    · exact edgeNoX_reach_of_comp (hin d hd hdc) hdk
  · refine internal_transfer hB.internal fun d hd hdk => hin d hd ?_
    rintro rfl
    exact (Kind.random_facts hck).2.2.2.2.2 hdk
  · intro d hd hdk
    rcases hfx d hd with h | h
    · obtain ⟨hne, hx⟩ := hB.solid d h hdk
      exact ⟨hne, hX _ _ hx⟩
    · obtain ⟨hne, hx⟩ := hsol d h hdk
      exact ⟨hne, hX _ _ hx⟩
  · intro d hd hdk hb
    rcases hfx d hd with h | h
    · exact hB.xapart d h hdk ((hsb _ _).1 hb)
    · exact (hndot d h).2 hdk
  · rw [← hB.excess]
    exact (dg_eL_of_filter_perm hdots).2
  · exact nonRedInt_of_perm hB.nonred hdots
  · intro hdc
    refine dcs_replace hc new rfl (Kind.random_facts hck).1 (Kind.random_facts hck).2.1
      (Kind.random_facts hck).2.2.1 ?_ ?_ (hB.dc hdc)
    · intro d hd hdk hne
      exact Graph.molReach_of_comp (hin d hd hne) hdk
    · intro hG a b hx hy L₀ _
      have hXr : ∃ x₀, X = .inr x₀ := by
        rcases hXd : X with a' | x₀
        · have := hB.xright
          rw [hXd] at this
          simp at this
        · exact ⟨x₀, rfl⟩
      obtain ⟨x₀, hx₀⟩ := hXr
      rcases hblue hG (by rw [hx]; rfl) (by rw [hy]; rfl) with ⟨d, hd, hdk, hdx, hdy⟩ |
        ⟨d₁, hd₁, d₂, hd₂, hk₁, hk₂, h1x, h1y, h2x, h2y⟩
      · refine Graph.netT_reach_of_mem _ _ _ (p := (d, some true)) ?_ rfl (by rw [hdx, hx])
          (by rw [hdy, hy])
        refine List.mem_append_right _ (List.mem_map.2 ⟨d, hd, ?_⟩)
        simp [hdk]
      · have r1 : (g.step3_netT (L₀ ++ new.map fun d =>
            (d, if d.kind = .G .plus then some true else none)) true).Reachable a x₀ := by
          refine Graph.netT_reach_of_mem _ _ _ (p := (d₁, some true)) ?_ rfl (by rw [h1x, hx])
            (by rw [h1y, hx₀])
          exact List.mem_append_right _ (List.mem_map.2 ⟨d₁, hd₁, by simp [hk₁]⟩)
        have r2 : (g.step3_netT (L₀ ++ new.map fun d =>
            (d, if d.kind = .G .plus then some true else none)) true).Reachable x₀ b := by
          refine Graph.netT_reach_of_mem _ _ _ (p := (d₂, some true)) ?_ rfl (by rw [h2x, hx₀])
            (by rw [h2y, hy])
          exact List.mem_append_right _ (List.mem_map.2 ⟨d₂, hd₂, by simp [hk₂]⟩)
        exact r1.trans r2
  · intro d hd
    rcases hfx d hd with h | h
    · exact hB.wf d h
    · exact hwf d h
  · intro d hd hdk
    rcases hfx d hd with h | h
    · exact hB.noloop d h hdk
    · exact absurd hdk (hndot d h).1
  · intro d hd
    rcases hfx d hd with h | h
    · exact hB.lab d h
    · exact hlab d h
  · intro d hd hdl
    rcases hfx d hd with h | h
    · exact hB.good d h hdl
    · exact hgood d h hdl
  · intro d hd
    rcases hfx d hd with h | h
    · rcases hB.minor d h with h' | ⟨h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl h'
      · exact Or.inr ⟨h1, h2, h3, h4, hX _ _ h5, hX _ _ h6⟩
    · rcases hminor d h with h' | ⟨h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl h'
      · exact Or.inr ⟨h1, h2, h3, h4, hX _ _ h5, hX _ _ h6⟩
  · intro d hd hdi
    rcases hfx d hd with h | h
    · exact hB.inv d h hdi
    · exact hinv d h hdi
  · intro d hd hdi
    rcases hfx d hd with h | h
    · exact hB.wd d h hdi
    · exact hwd d h hdi
  · exact (subperm_eraseIdx hB.carry hc hcc).trans (List.sublist_append_left _ _).subperm
  · exact fun u v h => (hsb u v).2 (hB.blocks u v h)

/-- The classes pass to the graph in which a component is replaced. -/
theorem step3_cls_replace {D' : ℕ} {X : Atom k n} {Γ T T' : Graph k n}
    (hcls : Cls D' X Γ T) (hlead : ClsLead X Γ T → Cls D' X Γ T')
    (hkeep : ∀ e ∈ T.comps, e.kind.isRandom = true → e.minor = [] → e.kind.isInvB = false →
      (∃ u ∈ [e.x, e.y], T.SameBlock u X) → e ∈ T'.comps)
    (hsb : ∀ u v, T.SameBlock u v → T'.SameBlock u v)
    (hlf : T.LabelFree → T'.LabelFree)
    (hord : T.ord - (D' + 1) * (nWD T.comps : ℤ) ≤ T'.ord - (D' + 1) * (nWD T'.comps : ℤ)) :
    Cls D' X Γ T' := by
  rcases hcls with ⟨ha, ho⟩ | ⟨hl, ha, ho⟩ | hL
  · exact Or.inl ⟨att_transfer ha hkeep hsb, by linarith⟩
  · exact Or.inr (Or.inl ⟨hlf hl, att_transfer ha hkeep hsb, by linarith⟩)
  · exact hlead hL

/-- Replacing a component by one with the same kind and ends keeps the form of the leading
term. -/
theorem lead_replace {X : Atom k n} {Γ T : Graph k n} (hL : LeadPerm X Γ T) {i : ℕ}
    {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (d : Comp (Atom k n))
    (hd : baseC d = baseC c) (co : Coeff) :
    LeadPerm X Γ ⟨T.comps.eraseIdx i ++ [d], co⟩ := by
  obtain ⟨us, hus, hp⟩ := hL
  refine ⟨us, hus, ?_⟩
  have h1 : ((T.comps.eraseIdx i ++ [d]).map baseC).Perm (T.comps.map baseC) := by
    have h2 := ((perm_eraseIdx hc).map baseC).symm
    rw [List.map_cons, ← hd] at h2
    rw [List.map_append, List.map_singleton]
    exact List.perm_append_singleton _ _ |>.trans h2
  exact h1.trans hp

end ReplaceStep

/-! ## The phase of [II, (4.21)] -/

section TaylorPhase

variable {k n : ℕ}

theorem oTaylorT_eq {T : Graph k n} (D' : ℕ) {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
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

/-! ## The phase of [II, (4.20)] -/

section RevPhase

variable {k n : ℕ}

theorem solidC_ne {V : Type*} [DecidableEq V] (ch : Charge) {u v : V} (h : u ≠ v) :
    solidC ch u v = mkC (.G ch) u v := by
  simp [solidC, h]

/-- The components `G_{ax} G_{xb} (G_{xx})⁻¹` of [II, (4.17), (4.20)] for the component `c` of
charge `ch`, with the label of `c`. -/
def revNew (X : Atom k n) (c : Comp (Atom k n)) (ch : Charge) : List (Comp (Atom k n)) :=
  [{ mkC (.G ch) c.x X with label := c.label }, { mkC (.G ch) X c.y with label := c.label },
    { mkC (.inv ch) X X with label := c.label }]

theorem oSchurRevT_eq {T : Graph k n} (X : Atom k n) {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .G ch) (hm : c.minor = [X])
    (hg : c.label.all T.GoodGroup = true) (hx : c.x ≠ X) (hy : c.y ≠ X) :
    oSchurRevT X i T = [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩].map Tracked.self := by
  have h1 := solidC_ne ch hx
  have h2 := solidC_ne ch (Ne.symm hy)
  simp only [oSchurRevT, hc, hk, hm, hg, decide_true, Bool.and_self, ite_true, h1, h2,
    List.map_cons, List.map_nil, revNew]
  rfl

theorem oSchurWRevT_eq {T : Graph k n} (X : Atom k n) {i : ℕ} {c : Comp (Atom k n)}
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

theorem goodGroup_of {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T)
    (c : Comp (Atom k n)) (hc : c ∈ T.comps) : c.label.all T.GoodGroup = true := by
  rcases hB.lab c hc with hl | hl
  · rw [hl]; rfl
  · rw [hl]
    simp only [Option.all_some, Graph.GoodGroup, List.all_eq_true]
    intro d hd
    by_cases hdl : d.label = some (.P, X)
    · simp [hB.good d hd (by rw [hdl]; rfl)]
    · simp [hdl]

/-- The facts shared by the two terms of [II, (4.20)] at a component with minor `{X}`. -/
theorem rev_common {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ)
    (hB : Base D' S X Γ T) (hcls : Cls D' X Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c)
    (hm : c.minor = [X]) {ch : Charge}
    (hk : c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch)
    (hstep : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩) :
    ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩],
      Base D' S X Γ g ∧ Cls D' X Γ g ∧ step3_nMin g.comps + 1 = step3_nMin T.comps ∧
        nWD g.comps = nWD T.comps := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  obtain ⟨-, -, hx, hy, hxX, hyX⟩ := (hB.minor c hcT).resolve_left (by rw [hm]; simp)
  have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hcnd := (Kind.random_facts hcr).2.2.2.1
  have hci : c.kind.isInvB = false := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hcw : c.kind.step3_isWDB = false := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
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
    change (step3_dg (T.comps.eraseIdx i ++ new)).Reachable u v
    rw [(dg_eL_of_filter_perm hdots).1]
    exact h
  have hkeepT : ∀ new : List (Comp (Atom k n)), ∀ co : Coeff, ∀ e ∈ T.comps,
      e.kind.isRandom = true → e.minor = [] → e.kind.isInvB = false →
        (∃ u ∈ [e.x, e.y], T.SameBlock u X) →
        e ∈ (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).comps := by
    intro new co e he _ hem _ _
    refine List.mem_append_left _ (mem_eraseIdx_of_ne hc he ?_)
    rintro rfl
    rw [hm] at hem
    cases hem
  have hlfT : ∀ new : List (Comp (Atom k n)), (∀ d ∈ new, d.label = c.label) → ∀ co : Coeff,
      T.LabelFree → (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).LabelFree := by
    intro new hnew co hlf d hd
    rcases List.mem_append.1 hd with h | h
    · exact hlf d (List.mem_of_mem_eraseIdx h)
    · rw [hnew d h]
      exact hlf c hcT
  have hcc : c ∉ carryL Γ := by
    intro h
    have := (hG.plain c (mem_carryL h).1).1
    rw [hm] at this
    cases this
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · -- the term with the minor removed
    have hnew : ∀ d ∈ [{ c with minor := [] }], d = { c with minor := [] } :=
      fun d hd => List.mem_singleton.1 hd
    have hnw : nWD (T.comps.eraseIdx i ++ [{ c with minor := [] }]) = nWD T.comps := by
      have := count_replace hc [{ c with minor := [] }] (fun c => c.kind.step3_isWDB)
      unfold nWD
      simp only [hcw, Bool.false_eq_true, ite_false, add_zero, List.filter_cons,
        List.filter_nil] at this
      simpa using this
    have hord : (⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n).ord =
        T.ord := by
      rw [hord0]
      simp
    have hmin : step3_nMin (T.comps.eraseIdx i ++ [{ c with minor := [] }]) + 1 = step3_nMin T.comps := by
      have := count_replace hc [{ c with minor := [] }] (fun c => !c.minor.isEmpty)
      unfold step3_nMin
      simpa [hm] using this
    refine ⟨?_, step3_cls_replace hcls (fun hL => Or.inr (Or.inr ⟨hlfT _ (by simp) _ hL.1,
      lead_replace hL.2 hc { c with minor := [] } rfl T.coeff⟩)) (hkeepT _ _)
      (hsbT _ (by simpa using hcnd) _) (hlfT _ (by simp) _) (by rw [hord, hnw]), hmin, hnw⟩
    refine step3_base_replace hB hc [{ c with minor := [] }] T.coeff (hstep _ (by simp)) hcr ?_ ?_ ?_ ?_
      ?_ ?_ hcc ?_ ?_ ?_ ?_ ?_ ?_
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
      have hp := count_replace hc [{ c with minor := [] }] (step3_pendB X)
      have hi' := count_replace hc [{ c with minor := [] }] (fun c => c.kind.isInvB)
      have hl : (T.comps.eraseIdx i ++ [{ c with minor := [] }]).length = T.comps.length := by
        rw [List.length_append, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
        have := List.length_pos_of_mem hcT
        simp only [List.length_singleton]
        omega
      have hcp : step3_pendB X c = false := by simp [step3_pendB, hm]
      have hp1 : (([{ c with minor := [] }] : List (Comp (Atom k n))).filter
          (step3_pendB X)).length ≤ 1 := by
        simp only [List.filter_cons, List.filter_nil]
        split_ifs <;> simp
      simp only [hcp, Bool.false_eq_true, ite_false, add_zero] at hp
      simp only [hci, Bool.false_eq_true, ite_false, add_zero, List.filter_cons,
        List.filter_nil] at hi'
      unfold sizeΦ step3_nPend step3_nInv
      have hi'' : ((T.comps.eraseIdx i ++ [{ c with minor := [] }]).filter
          fun (d : Comp (Atom k n)) => d.kind.isInvB).length =
          (T.comps.filter fun (d : Comp (Atom k n)) => d.kind.isInvB).length := by
        rw [hi']
        simp
      rw [hl, hi'']
      have := hmin
      unfold step3_nMin at this
      unfold step3_nMin
      nlinarith
  · -- the term `- G_{ax} G_{xb} (G_{xx})⁻¹`
    have hmemN : ∀ d ∈ revNew X c ch, d = { mkC (.G ch) c.x X with label := c.label } ∨
        d = { mkC (.G ch) X c.y with label := c.label } ∨
        d = { mkC (.inv ch) X X with label := c.label } := by
      intro d hd
      simpa [revNew] using hd
    have hnw : nWD (T.comps.eraseIdx i ++ revNew X c ch) = nWD T.comps := by
      have := count_replace hc (revNew X c ch) (fun c => c.kind.step3_isWDB)
      unfold nWD
      simp only [hcw, Bool.false_eq_true, ite_false, add_zero] at this
      rw [this]
      simp [revNew, mkC, Kind.step3_isWDB]
    have hordN : ((revNew X c ch).map fun d => d.kind.ord).sum = 2 := by
      simp [revNew, mkC, Kind.ord]
    have hcord : c.kind.ord ≤ 1 := by
      rcases hk with hk | hk | hk <;> rw [hk] <;> simp [Kind.ord]
    have hord : T.ord + 1 ≤ (⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩ : Graph k n).ord := by
      rw [hord0, hordN]
      linarith
    have hmin : step3_nMin (T.comps.eraseIdx i ++ revNew X c ch) + 1 = step3_nMin T.comps := by
      have := count_replace hc (revNew X c ch) (fun c => !c.minor.isEmpty)
      unfold step3_nMin
      simpa [hm, revNew, mkC] using this
    have hlfN := hlfT (revNew X c ch) (by simp [revNew]) (-T.coeff)
    refine ⟨?_, step3_cls_replace hcls (fun hL => Or.inr (Or.inl ⟨hlfN hL.1,
      ⟨{ mkC (.G ch) c.x X with label := c.label }, List.mem_append_right _ (by simp [revNew]),
        hL.1 c hcT, rfl, rfl, rfl, X, by simp [mkC], SimpleGraph.Reachable.refl _⟩,
      by rw [hnw]; linarith⟩)) (hkeepT _ _)
      (hsbT _ (by simp [revNew, mkC]) _) hlfN (by rw [hnw]; linarith), hmin, hnw⟩
    refine step3_base_replace hB hc (revNew X c ch) (-T.coeff) (hstep _ (by simp)) hcr ?_ ?_ ?_ ?_
      ?_ ?_ hcc ?_ ?_ ?_ ?_ ?_ ?_
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
      · simp [mkC, Kind.isInvB] at hdi
      · simp [mkC, Kind.isInvB] at hdi
      · exact ⟨rfl, rfl, rfl⟩
    · intro d hd hdi
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [mkC, Kind.step3_isWDB] at hdi
    · rw [hnw]
      linarith
    · refine le_trans ?_ hBs
      have hp := count_replace hc (revNew X c ch) (step3_pendB X)
      have hi' := count_replace hc (revNew X c ch) (fun c => c.kind.isInvB)
      have hl : (T.comps.eraseIdx i ++ revNew X c ch).length + 1 = T.comps.length + 3 := by
        rw [List.length_append, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
        have := List.length_pos_of_mem hcT
        simp only [revNew, List.length_cons, List.length_nil]
        omega
      have hcp : step3_pendB X c = false := by simp [step3_pendB, hm]
      simp only [hcp, Bool.false_eq_true, ite_false, add_zero] at hp
      simp only [hci, Bool.false_eq_true, ite_false, add_zero] at hi'
      have e1 : (revNew X c ch).filter (step3_pendB X) = [] := by simp [revNew, step3_pendB, mkC]
      have e2 : ((revNew X c ch).filter fun c => c.kind.isInvB).length = 1 := by
        simp [revNew, mkC, Kind.isInvB]
      rw [e1] at hp
      rw [e2] at hi'
      unfold sizeΦ step3_nPend step3_nInv
      have := hmin
      unfold step3_nMin at this
      unfold step3_nMin
      simp only [List.length_nil, add_zero] at hp
      rw [hp, hi']
      nlinarith

end RevPhase

section RevPhase2

variable {k n : ℕ}

end RevPhase2

/-! ## The phase of [II, (4.17)] -/

section SchurPhase

variable {k n : ℕ}

/-- The components of `𝒢` not yet written by [II, (4.17)] are factors of `𝒢` whose atoms are
`×`-dotted to `X`. -/
def Step3PendInv (X : Atom k n) (Γ T : Graph k n) : Prop :=
  ∀ c ∈ T.comps, step3_pendB X c = true → c ∈ Γ.comps ∧ HasX T.comps c.x X ∧ HasX T.comps c.y X

/-- Every labelled random component is pending or has the minor `{X}`, some component carries the
label `P_X`, and the graph has the form of the leading term. -/
def AllPendL (X : Atom k n) (Γ T : Graph k n) : Prop :=
  (∀ c ∈ T.comps, c.label.isSome = true → c.kind.isRandom = true →
    step3_pendB X c = true ∨ c.minor = [X]) ∧ (∃ c ∈ T.comps, c.label = some (.P, X)) ∧ LeadPerm X Γ T

theorem oSchurT_eq {T : Graph k n} (X : Atom k n) {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .G ch) (hm : c.minor = [])
    (hg : c.label.all T.GoodGroup = true) (hx : c.x ≠ X) (hy : c.y ≠ X) :
    oSchurT X i T = [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩].map Tracked.self := by
  have h1 := solidC_ne ch hx
  have h2 := solidC_ne ch (Ne.symm hy)
  simp only [oSchurT, hc, hk, hm, hg, List.isEmpty_nil, Bool.and_self, ite_true,
    h1, h2, List.map_cons, List.map_nil, revNew]
  rfl

theorem oSchurWT_eq {T : Graph k n} (X : Atom k n) {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .weight ch ∨ c.kind = .light ch)
    (hm : c.minor = []) (hg : c.label.all T.GoodGroup = true) (hx : c.x ≠ X) (hyx : c.y = c.x) :
    oSchurWT X i T = [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩].map Tracked.self := by
  have hx' : (c.x != X) = true := by simpa using hx
  obtain ⟨κ, a, b, mm, l⟩ := c
  simp only at hyx hx hx' hm hk hg
  subst hyx hm
  rcases hk with hk | hk <;>
    simp only [oSchurWT, hc, hk, hx', hg, List.isEmpty_nil, Bool.and_self,
      ite_true, List.map_cons, List.map_nil, revNew] <;> rfl

/-- The facts shared by the two terms of [II, (4.17)] at a pending component. -/
theorem schur_common {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T)
    (hP : Step3PendInv X Γ T) (hcls : ClsP D' X Γ T ∨ AllPendL X Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hp : step3_pendB X c = true) {ch : Charge}
    (hk : c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch)
    (hstep : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩) :
    ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩],
      Base D' S X Γ g ∧ Step3PendInv X Γ g ∧ (ClsP D' X Γ g ∨ AllPendL X Γ g) ∧
        step3_nPend X g.comps + 1 = step3_nPend X T.comps := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  obtain ⟨hcΓ, hxX, hyX⟩ := hP c hcT hp
  have hpp := hp
  simp only [step3_pendB, Bool.and_eq_true, List.isEmpty_iff, bne_iff_ne, ne_eq] at hpp
  obtain ⟨⟨⟨⟨hl, hcr⟩, hm⟩, hx⟩, hy⟩ := hpp
  have hl' : c.label = some (.P, X) := by
    rcases hB.lab c hcT with h | h
    · rw [h] at hl; cases hl
    · exact h
  have hcc : c ∉ carryL Γ := fun h => by
    rw [(mem_carryL h).2.1] at hl'
    cases hl'
  have hnb : ∀ u ∈ [c.x, c.y], ¬ T.SameBlock u X := by
    intro u hu hb
    have hX : HasX T.comps u X := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact hxX
      · exact hyX
    obtain ⟨d, hd, hdk, hdxy⟩ := hX
    apply hB.xapart d hd hdk
    rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hb
    · rw [h1, h2]; exact hb.symm
  have hcnd := (Kind.random_facts hcr).2.2.2.1
  have hci : c.kind.isInvB = false := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hcw : c.kind.step3_isWDB = false := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hord0 := ord_replace hc
  have hBo := hB.ord
  have hBs := hB.size
  have hfx : ∀ new : List (Comp (Atom k n)), ∀ d ∈ T.comps.eraseIdx i ++ new,
      d ∈ T.comps ∨ d ∈ new := by
    intro new d hd
    rcases List.mem_append.1 hd with h | h
    · exact Or.inl (List.mem_of_mem_eraseIdx h)
    · exact Or.inr h
  have hXg : ∀ new : List (Comp (Atom k n)), ∀ u v, HasX T.comps u v →
      HasX (T.comps.eraseIdx i ++ new) u v := by
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
    change (step3_dg (T.comps.eraseIdx i ++ new)).Reachable u v
    rw [(dg_eL_of_filter_perm hdots).1]
    exact h
  have hkeepS : ∀ new : List (Comp (Atom k n)), ∀ co : Coeff, ∀ e ∈ T.comps,
      e.kind.isRandom = true → e.minor = [] → e.kind.isInvB = false →
        (∃ u ∈ [e.x, e.y], T.SameBlock u X) →
        e ∈ (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).comps := by
    intro new co e he _ _ _ ⟨u, hu, hub⟩
    refine List.mem_append_left _ (mem_eraseIdx_of_ne hc he ?_)
    rintro rfl
    exact hnb u hu hub
  have hPg : ∀ new : List (Comp (Atom k n)), (∀ d ∈ new, step3_pendB X d = false) →
      Step3PendInv X Γ ⟨T.comps.eraseIdx i ++ new, T.coeff⟩ := by
    intro new hnew d hd hdp
    rcases hfx new d hd with h | h
    · obtain ⟨h1, h2, h3⟩ := hP d h hdp
      exact ⟨h1, hXg new _ _ h2, hXg new _ _ h3⟩
    · rw [hnew d h] at hdp
      cases hdp
  have hnP : ∀ new : List (Comp (Atom k n)), (∀ d ∈ new, step3_pendB X d = false) →
      step3_nPend X (T.comps.eraseIdx i ++ new) + 1 = step3_nPend X T.comps := by
    intro new hnew
    have := count_replace hc new (step3_pendB X)
    have e : new.filter (step3_pendB X) = [] :=
      List.filter_eq_nil_iff.2 (fun d hd => by rw [hnew d hd]; simp)
    rw [hp, e] at this
    unfold step3_nPend
    simpa using this
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · -- the term with the minor `{X}`
    have hnew : ∀ d ∈ [{ c with minor := [X] }], d = { c with minor := [X] } :=
      fun d hd => List.mem_singleton.1 hd
    have hnp : ∀ d ∈ [{ c with minor := [X] }], step3_pendB X d = false := by
      intro d hd
      rw [hnew d hd]
      simp [step3_pendB]
    have hnw : nWD (T.comps.eraseIdx i ++ [{ c with minor := [X] }]) = nWD T.comps := by
      have := count_replace hc [{ c with minor := [X] }] (fun c => c.kind.step3_isWDB)
      unfold nWD
      simp only [hcw, Bool.false_eq_true, ite_false, add_zero, List.filter_cons,
        List.filter_nil] at this
      simpa using this
    have hord : (⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n).ord =
        T.ord := by
      rw [hord0]
      simp
    have hmin : step3_nMin (T.comps.eraseIdx i ++ [{ c with minor := [X] }]) = step3_nMin T.comps + 1 := by
      have := count_replace hc [{ c with minor := [X] }] (fun c => !c.minor.isEmpty)
      unfold step3_nMin
      simpa [hm] using this
    refine ⟨?_, hPg _ hnp, ?_, hnP _ hnp⟩
    · refine step3_base_replace hB hc [{ c with minor := [X] }] T.coeff (hstep _ (by simp)) hcr ?_ ?_ ?_
        ?_ ?_ ?_ hcc ?_ ?_ ?_ ?_ ?_ ?_
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
        exact hB.lab c hcT
      · intro d hd _
        rw [hnew d hd]
        rcases hk with hk | hk | hk <;> simp [Comp.isGoodKind, hk]
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
        have hi' := count_replace hc [{ c with minor := [X] }] (fun c => c.kind.isInvB)
        have hl' : (T.comps.eraseIdx i ++ [{ c with minor := [X] }]).length = T.comps.length := by
          rw [List.length_append, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
          have := List.length_pos_of_mem hcT
          simp only [List.length_singleton]
          omega
        simp only [hci, Bool.false_eq_true, ite_false, add_zero, List.filter_cons,
          List.filter_nil] at hi'
        have hi'' : ((T.comps.eraseIdx i ++ [{ c with minor := [X] }]).filter
            fun (d : Comp (Atom k n)) => d.kind.isInvB).length =
            (T.comps.filter fun (d : Comp (Atom k n)) => d.kind.isInvB).length := by
          rw [hi']
          simp
        have hP' := hnP _ hnp
        unfold sizeΦ step3_nInv
        rw [hl', hi'', hmin]
        nlinarith
    · rcases hcls with ⟨ha, ho⟩ | ⟨hA1, -, hA3⟩
      · left
        exact ⟨att_transfer ha (hkeepS _ _)
          (hsbT [{ c with minor := [X] }] (by simpa using hcnd) T.coeff),
          by rw [hord, hnw]; exact ho⟩
      · right
        refine ⟨?_, ⟨{ c with minor := [X] }, List.mem_append_right _ (List.mem_singleton_self _),
          hl'⟩, lead_replace hA3 hc { c with minor := [X] } rfl T.coeff⟩
        intro d hd hdl hdr
        rcases hfx _ d hd with h | h
        · exact hA1 d h hdl hdr
        · rw [hnew d h]
          exact Or.inr rfl
  · -- the term `G_{ax} G_{xb} (G_{xx})⁻¹`
    have hmemN : ∀ d ∈ revNew X c ch, d = { mkC (.G ch) c.x X with label := c.label } ∨
        d = { mkC (.G ch) X c.y with label := c.label } ∨
        d = { mkC (.inv ch) X X with label := c.label } := by
      intro d hd
      simpa [revNew] using hd
    have hnp : ∀ d ∈ revNew X c ch, step3_pendB X d = false := by
      intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [step3_pendB, mkC]
    have hnw : nWD (T.comps.eraseIdx i ++ revNew X c ch) = nWD T.comps := by
      have := count_replace hc (revNew X c ch) (fun c => c.kind.step3_isWDB)
      unfold nWD
      simp only [hcw, Bool.false_eq_true, ite_false, add_zero] at this
      rw [this]
      simp [revNew, mkC, Kind.step3_isWDB]
    have hordN : ((revNew X c ch).map fun d => d.kind.ord).sum = 2 := by
      simp [revNew, mkC, Kind.ord]
    have hcord : c.kind.ord ≤ 1 := by
      rcases hk with hk | hk | hk <;> rw [hk] <;> simp [Kind.ord]
    have hord : T.ord + 1 ≤ (⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩ : Graph k n).ord := by
      rw [hord0, hordN]
      linarith
    have hmin : step3_nMin (T.comps.eraseIdx i ++ revNew X c ch) = step3_nMin T.comps := by
      have := count_replace hc (revNew X c ch) (fun c => !c.minor.isEmpty)
      unfold step3_nMin
      simpa [hm, revNew, mkC] using this
    refine ⟨?_, hPg _ hnp, Or.inl ⟨⟨{ mkC (.G ch) c.x X with label := c.label },
        List.mem_append_right _ (by unfold revNew; exact List.mem_cons_self ..), hl', rfl, rfl, rfl,
        X, by simp [mkC], SimpleGraph.Reachable.refl _⟩, by rw [hnw]; linarith⟩, hnP _ hnp⟩
    refine step3_base_replace hB hc (revNew X c ch) T.coeff (hstep _ (by simp)) hcr ?_ ?_ ?_ ?_
      ?_ ?_ hcc ?_ ?_ ?_ ?_ ?_ ?_
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
        exact ⟨fun h => by simp_all [mkC, Kind.isWeight], fun _ => by simp [mkC, Kind.isRandom]⟩
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> exact hB.lab c hcT
    · intro d hd _
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [mkC, Comp.isGoodKind]
    · intro d hd
      rcases hmemN d hd with rfl | rfl | rfl <;> exact Or.inl rfl
    · intro d hd hdi
      rcases hmemN d hd with rfl | rfl | rfl
      · simp [mkC, Kind.isInvB] at hdi
      · simp [mkC, Kind.isInvB] at hdi
      · exact ⟨rfl, rfl, rfl⟩
    · intro d hd hdi
      rcases hmemN d hd with rfl | rfl | rfl <;> simp [mkC, Kind.step3_isWDB] at hdi
    · rw [hnw]
      linarith
    · refine le_trans ?_ hBs
      have hi' := count_replace hc (revNew X c ch) (fun c => c.kind.isInvB)
      have hl' : (T.comps.eraseIdx i ++ revNew X c ch).length + 1 = T.comps.length + 3 := by
        rw [List.length_append, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.1 hc).1]
        have := List.length_pos_of_mem hcT
        simp only [revNew, List.length_cons, List.length_nil]
        omega
      simp only [hci, Bool.false_eq_true, ite_false, add_zero] at hi'
      have e2 : ((revNew X c ch).filter fun c => c.kind.isInvB).length = 1 := by
        simp [revNew, mkC, Kind.isInvB]
      rw [e2] at hi'
      have hP' := hnP _ hnp
      unfold sizeΦ step3_nInv
      rw [hi', hmin]
      nlinarith

end SchurPhase

section SchurPhase2

variable {k n : ℕ}

theorem kind_of_plain_random {c : Comp (Atom k n)} (hp : c.minor = [] ∧
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

/-- The label `P_X` removed when every labelled factor has the minor `{X}`: the clauses `Base` are
kept, the graph has the form of the leading term, and the value is kept. -/
theorem dropP_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T)
    (hnp : step3_nPend X T.comps = 0) (hA : AllPendL X Γ T) :
    Base D' S X Γ T.dropLabels ∧ ClsLead X Γ T.dropLabels ∧
      TExpansion.ValueEq [Tracked.self T.dropLabels] T modelAdm := by
  set φ : Comp (Atom k n) → Comp (Atom k n) := fun c => { c with label := none } with hφ
  have hcomps : T.dropLabels.comps = T.comps.map φ := rfl
  have hφk : ∀ c, (φ c).kind = c.kind ∧ (φ c).x = c.x ∧ (φ c).y = c.y ∧ (φ c).minor = c.minor :=
    fun c => ⟨rfl, rfl, rfl, rfl⟩
  have hmem : ∀ c ∈ T.comps, φ c ∈ T.dropLabels.comps := fun c hc => by
    rw [hcomps]; exact List.mem_map_of_mem hc
  have hmem' : ∀ d ∈ T.dropLabels.comps, ∃ c ∈ T.comps, d = φ c := by
    intro d hd
    rw [hcomps, List.mem_map] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    exact ⟨c, hc, rfl⟩
  have hφid : ∀ c ∈ T.comps, c.label = none → φ c = c := by
    intro c _ hl
    obtain ⟨κ, x, y, m, l⟩ := c
    simp only at hl
    subst hl
    rfl
  have hnr : ∀ c ∈ T.comps, c.kind.isRandom = false → φ c = c := by
    intro c hc hr
    refine hφid c hc ?_
    by_contra hl
    have := (hB.wf c hc).2 (by simpa [Option.isSome_iff_ne_none] using hl)
    rw [hr] at this
    cases this
  have hnotpend : ∀ c ∈ T.comps, step3_pendB X c = false := by
    intro c hc
    by_contra h
    have : c ∈ T.comps.filter (step3_pendB X) := List.mem_filter.2 ⟨hc, by simpa using h⟩
    have := List.length_pos_of_mem this
    unfold step3_nPend at hnp
    omega
  have hmx : ∀ c ∈ T.comps, c.label = some (.P, X) → c.minor = [X] ∧
      ∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch := by
    intro c hc hl
    have hr : c.kind.isRandom = true := (hB.wf c hc).2 (by rw [hl]; rfl)
    rcases hA.1 c hc (by rw [hl]; rfl) hr with h | h
    · rw [hnotpend c hc] at h
      cases h
    · rcases hB.minor c hc with h' | ⟨h1, h2, -⟩
      · rw [h'] at h; cases h
      · exact ⟨h1, h2⟩
  have hdots : (T.dropLabels.comps.filter fun c => decide (c.kind = .dot)) =
      T.comps.filter fun c => decide (c.kind = .dot) := by
    rw [hcomps, List.filter_map]
    have e1 : ((fun c : Comp (Atom k n) => decide (c.kind = .dot)) ∘ φ) =
        fun c => decide (c.kind = .dot) := rfl
    rw [e1]
    conv_rhs => rw [← List.map_id (T.comps.filter _)]
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc
    exact hφid c hc1 (dotlab_of_wf hB.wf c hc1 (Or.inl (by simpa using hc2)))
  obtain ⟨hdg, heL⟩ := dg_eL_of_filter_perm (List.Perm.of_eq hdots)
  have hX : ∀ u v, HasX T.comps u v → HasX T.dropLabels.comps u v := by
    intro u v ⟨d, hd, hk, hxy⟩
    exact ⟨φ d, hmem d hd, hk, hxy⟩
  have hPF : T.IsPFormAt X := ⟨hA.2.1, hB.lab⟩
  have hstep : QElemStep ⟨n, T⟩ ⟨n, T.dropLabels⟩ := QElemStep.dropP X T hPF fun c hc hl => by
    rcases hB.lab c hc with h | h
    · rw [h] at hl; cases hl
    · rw [(hmx c hc h).1]
      exact List.mem_singleton_self _
  refine ⟨⟨hB.chain.tail hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hB.xright, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · refine connNoX_transfer hB.conn fun c hc hck => ?_
    exact edgeNoX_reach_of_comp (c := φ c) (hmem c hc) hck
  · refine internal_transfer hB.internal fun c hc hck => ?_
    rw [← hnr c hc ?_]
    · exact hmem c hc
    · cases hr : c.kind.isRandom
      · rfl
      · exact absurd hck (Kind.random_facts hr).2.2.2.2.2
  · intro d hd hds
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    obtain ⟨hne, hx⟩ := hB.solid c hc hds
    exact ⟨hne, hX _ _ hx⟩
  · intro d hd hdk hb
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    apply hB.xapart c hc hdk
    change (step3_dg T.comps).Reachable c.x c.y
    rw [← hdg]
    exact hb
  · rw [← hB.excess, heL]
  · exact nonRedInt_of_perm hB.nonred (List.Perm.of_eq hdots)
  · intro hdc
    obtain ⟨L, hL⟩ := hB.dc hdc
    refine ⟨L.map fun p => (φ p.1, p.2), hL.same _ ?_ ?_ ?_ ?_ ?_⟩
    · rw [List.map_map, hcomps, ← hL.map_fst, List.map_map]
      rfl
    · intro p hp hpt
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hL.black q hq hpt
    · intro p hp hpt
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hL.blue q hq hpt
    · intro c hc hck
      exact Graph.molReach_of_comp (c := φ c) (hmem c hc) hck
    · intro t p hp hpt a b hx hy
      exact Graph.netT_reach_of_mem _ _ _ (p := (φ p.1, p.2))
        (List.mem_map_of_mem (f := fun p : Step3TC k n => (φ p.1, p.2)) hp) hpt hx hy
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    exact ⟨(hB.wf c hc).1, fun h => by simp [hφ] at h⟩
  · intro d hd hdk
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    exact hB.noloop c hc hdk
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    exact Or.inl rfl
  · intro d hd hdl
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    simp [hφ] at hdl
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    rcases hB.minor c hc with h | ⟨h5, h6, h7, h8, h9, h10⟩
    · exact Or.inl h
    · exact Or.inr ⟨h5, h6, h7, h8, hX _ _ h9, hX _ _ h10⟩
  · intro d hd hdi
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    exact hB.inv c hc hdi
  · intro d hd hdi
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    exact hB.wd c hc hdi
  · have hnw : nWD T.dropLabels.comps = nWD T.comps := by
      unfold nWD
      rw [hcomps, List.filter_map, List.length_map]
      rfl
    have hord : T.dropLabels.ord = T.ord := by
      simp only [Graph.ord, hcomps, List.map_map]
      rfl
    rw [hnw, hord]
    exact hB.ord
  · refine le_trans (le_of_eq ?_) hB.size
    unfold sizeΦ step3_nPend step3_nMin step3_nInv
    rw [hcomps, List.filter_map, List.filter_map, List.filter_map, List.length_map,
      List.length_map, List.length_map, List.length_map]
    have e1 : (T.comps.filter (step3_pendB X ∘ φ)) = T.comps.filter (step3_pendB X) := by
      refine List.filter_congr fun c hc => ?_
      rw [Function.comp_apply, hnotpend c hc]
      simp [step3_pendB, hφ]
    rw [e1]
    rfl
  · have e1 : (carryL Γ).map φ = carryL Γ := by
      conv_rhs => rw [← List.map_id (carryL Γ)]
      refine List.map_congr_left fun c hc => ?_
      obtain ⟨-, hl, -⟩ := mem_carryL hc
      obtain ⟨κ, x, y, m, l⟩ := c
      simp only at hl
      subst hl
      rfl
    rw [hcomps, ← e1]
    obtain ⟨l, hp, hs⟩ := hB.carry
    exact ⟨l.map φ, hp.map φ, hs.map φ⟩
  · intro u v h
    change (step3_dg T.dropLabels.comps).Reachable u v
    rw [hdg]
    exact hB.blocks u v h
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    rfl
  · obtain ⟨us, hus, hp⟩ := hA.2.2
    refine ⟨us, hus, ?_⟩
    rw [hcomps, List.map_map]
    exact hp
  · intro Ω ι _ _ PF D₀ hAd e
    obtain ⟨A⟩ := hAd
    have := dropP_value T X hB.lab hA.2.1 hmx A e
    rw [← this]
    funext ω
    simp [TExpansion.forget, Expansion.valR, Tracked.self]

end SchurPhase2

section SchurPhase3

variable {k n : ℕ}

theorem nMin_le_S {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T) :
    step3_nMin T.comps ≤ S :=
  le_trans (List.length_filter_le _ _) (le_trans (by unfold sizeΦ; omega) hB.size)

end SchurPhase3

/-! ## The phase of the splits `1 = 1_{u = x} + 1_{u ≠ x}` -/

section SplitPhase

variable {k n : ℕ}

/-- Appending a dotted or `×`-dotted edge `u v` keeps the clauses `Base`, when it is no dotted
loop, its ends are in different blocks, and the result has no `×`-dotted edge inside a block. -/
theorem step3_base_append {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T)
    {κ : Kind} (hκ : κ = .dot ∨ κ = .xdot) {u v : Atom k n} (huv : ¬ T.SameBlock u v)
    (hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps ++ [mkC κ u v], T.coeff⟩⟩)
    (hxa : (⟨T.comps ++ [mkC κ u v], T.coeff⟩ : Graph k n).XdotApart)
    (hsize : sizeΦ D' X (T.comps ++ [mkC κ u v]) ≤ S) :
    Base D' S X Γ ⟨T.comps ++ [mkC κ u v], T.coeff⟩ ∧
      (⟨T.comps ++ [mkC κ u v], T.coeff⟩ : Graph k n).ord = T.ord + κ.ord ∧
      nWD (T.comps ++ [mkC κ u v]) = nWD T.comps := by
  set g : Graph k n := ⟨T.comps ++ [mkC κ u v], T.coeff⟩ with hg
  have hin : ∀ d ∈ T.comps, d ∈ g.comps := fun d hd => List.mem_append_left _ hd
  have hfx : ∀ d ∈ g.comps, d ∈ T.comps ∨ d = mkC κ u v := by
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)
  have huv' : u ≠ v := fun h => huv (by rw [h]; exact SimpleGraph.Reachable.refl _)
  have hperm : g.comps.Perm (mkC κ u v :: T.comps) := List.perm_append_singleton _ _
  have hnw : nWD g.comps = nWD T.comps := by
    unfold nWD
    rw [List.filter_append]
    rcases hκ with rfl | rfl <;> simp [mkC, Kind.step3_isWDB]
  have hord : g.ord = T.ord + κ.ord := by
    simp only [Graph.ord, hg, List.map_append, List.sum_append]
    simp [mkC]
    ring
  have hrandom : κ.isRandom = false := by rcases hκ with rfl | rfl <;> rfl
  refine ⟨⟨hB.chain.tail hstep, ?_, ?_, ?_, hxa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hB.xright, hsize, ?_, ?_⟩, hord, hnw⟩
  · exact connNoX_transfer hB.conn fun d hd hdk => edgeNoX_reach_of_comp (hin d hd) hdk
  · exact internal_transfer hB.internal fun d hd _ => hin d hd
  · intro d hd hds
    rcases hfx d hd with h | rfl
    · obtain ⟨hne, hx⟩ := hB.solid d h hds
      exact ⟨hne, hasX_mono hin hx⟩
    · rcases hκ with rfl | rfl <;> simp [mkC, Kind.isSolid] at hds
  · rcases hκ with rfl | rfl
    · rw [← hB.excess, eL_perm hperm, eL_cons_dot_new (c := mkC .dot u v) _ rfl huv]
    · rw [← hB.excess, eL_perm hperm, eL_cons_nondot (c := mkC .xdot u v) _ (by simp [mkC])]
  · rcases hκ with rfl | rfl
    · exact nonRedInt_perm (nonRedInt_cons_dot (c := mkC .dot u v) hB.nonred rfl huv) hperm.symm
    · refine nonRedInt_of_perm hB.nonred ?_
      rw [List.filter_append]
      simp [mkC]
  · intro hdc
    obtain ⟨L, hL⟩ := hB.dc hdc
    refine ⟨L ++ [(mkC κ u v, none)], hL.same _ ?_ ?_ ?_ ?_ ?_⟩
    · rw [List.map_append, hL.map_fst]
      rfl
    · intro p hp hpt
      rcases List.mem_append.1 hp with h | h
      · exact hL.black p h hpt
      · rw [List.mem_singleton.1 h] at hpt; cases hpt
    · intro p hp hpt
      rcases List.mem_append.1 hp with h | h
      · exact hL.blue p h hpt
      · rw [List.mem_singleton.1 h] at hpt; cases hpt
    · intro d hd hdk
      exact Graph.molReach_of_comp (hin d hd) hdk
    · intro t p hp hpt a b hx hy
      exact Graph.netT_reach_of_mem _ _ _ (List.mem_append_left _ hp) hpt hx hy
  · intro d hd
    rcases hfx d hd with h | rfl
    · exact hB.wf d h
    · rcases hκ with rfl | rfl <;> exact ⟨by simp [mkC, Kind.isWeight], by simp [mkC]⟩
  · intro d hd hdk
    rcases hfx d hd with h | rfl
    · exact hB.noloop d h hdk
    · exact huv'
  · intro d hd
    rcases hfx d hd with h | rfl
    · exact hB.lab d h
    · exact Or.inl rfl
  · intro d hd hdl
    rcases hfx d hd with h | rfl
    · exact hB.good d h hdl
    · simp [mkC] at hdl
  · intro d hd
    rcases hfx d hd with h | rfl
    · rcases hB.minor d h with h' | ⟨h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl h'
      · exact Or.inr ⟨h1, h2, h3, h4, hasX_mono hin h5, hasX_mono hin h6⟩
    · exact Or.inl rfl
  · intro d hd hdi
    rcases hfx d hd with h | rfl
    · exact hB.inv d h hdi
    · rcases hκ with rfl | rfl <;> simp [mkC, Kind.isInvB] at hdi
  · intro d hd hdi
    rcases hfx d hd with h | rfl
    · exact hB.wd d h hdi
    · rfl
  · rw [hord, hnw]
    have : (0 : ℤ) ≤ κ.ord := by rcases hκ with rfl | rfl <;> simp [Kind.ord]
    linarith [hB.ord]
  · exact hB.carry.trans (List.sublist_append_left _ _).subperm
  · intro a b h
    exact dg_reach_mono (fun d hd _ => hin d hd) (hB.blocks a b h)

theorem sizeΦ_append_xdot {D' : ℕ} {X : Atom k n} (L : List (Comp (Atom k n)))
    {κ : Kind} (hκ : κ = .dot ∨ κ = .xdot) (u v : Atom k n) :
    sizeΦ D' X (L ++ [mkC κ u v]) = sizeΦ D' X L + 1 := by
  unfold sizeΦ step3_nPend step3_nMin step3_nInv
  rw [List.filter_append, List.filter_append, List.filter_append]
  rcases hκ with rfl | rfl <;> simp [mkC, step3_pendB, Kind.isRandom, Kind.isInvB] <;> ring

end SplitPhase

section SplitPhase2

variable {k n : ℕ}

theorem step3_oSplitT_eq {T : Graph k n} {u X : Atom k n} (h : u ≠ X) :
    oSplitT u X T = [(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
      ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩].map Tracked.self := by
  simp [oSplitT, h]

theorem nBad_le_S {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T) :
    step3_nBad T.comps ≤ S :=
  le_trans (List.length_filter_le _ _) (le_trans (by unfold sizeΦ; omega) hB.size)

theorem nPend_le_S {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T) :
    step3_nPend X T.comps ≤ S :=
  le_trans (List.length_filter_le _ _) (le_trans (by unfold sizeΦ; omega) hB.size)

end SplitPhase2

/-! ## The input graph -/

section Init

variable {k n : ℕ}

theorem connNoX_of_normal {C : ℕ} {Γ : Graph k n} (h : Γ.Normal C) : Γ.ConnNoX := by
  intro u v
  have key : ∀ a b, Γ.edgeGraph.Reachable a b → Γ.edgeGraphNoX.Reachable a b := by
    intro a b hr
    obtain ⟨w⟩ := hr
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj _ ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨hne, ⟨c, hc, h1, h2⟩ | ⟨c, hc, h1, h2⟩⟩ := hadj
      · by_cases hk : c.kind = .xdot
        · obtain ⟨d, hd, hds, hdxy⟩ := (h.2.2 _ _ hne).1 ⟨c, hc, hk, Or.inl ⟨h1, h2⟩⟩
          have hdx : d.kind ≠ .xdot := by intro h'; rw [h'] at hds; simp [Kind.isSolid] at hds
          rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [← h3, ← h4]; exact edgeNoX_reach_of_comp hd hdx
          · rw [← h3, ← h4]; exact (edgeNoX_reach_of_comp hd hdx).symm
        · rw [← h1, ← h2]; exact edgeNoX_reach_of_comp hc hk
      · by_cases hk : c.kind = .xdot
        · obtain ⟨d, hd, hds, hdxy⟩ := (h.2.2 _ _ hne).1 ⟨c, hc, hk, Or.inr ⟨h1, h2⟩⟩
          have hdx : d.kind ≠ .xdot := by intro h'; rw [h'] at hds; simp [Kind.isSolid] at hds
          rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [← h3, ← h4]; exact edgeNoX_reach_of_comp hd hdx
          · rw [← h3, ← h4]; exact (edgeNoX_reach_of_comp hd hdx).symm
        · rw [← h1, ← h2]; exact (edgeNoX_reach_of_comp hc hk).symm
  exact key u v (h.1.connected u v)

/-- The clauses `Base` hold at the input. -/
theorem step3_base_init {D' S C : ℕ} {X : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hPF : Γ.IsPFormAt X) (hP : Γ.Plain) (hxa : Γ.XdotApart) (hX : X.isRight = true)
    (hS : sizeΦ D' X Γ.comps ≤ S) : Base D' S X Γ Γ := by
  have hnoinv : ∀ c ∈ Γ.comps, c.kind.isInvB = false := by
    intro c hc
    have := (hP c hc).2.1
    revert this
    cases c.kind <;> simp [Kind.isInvB]
  have hnowd : ∀ c ∈ Γ.comps, c.kind.step3_isWDB = false := by
    intro c hc
    have := (hP c hc).2.2.1
    revert this
    cases c.kind <;> simp [Kind.step3_isWDB]
  refine ⟨Relation.ReflTransGen.refl, connNoX_of_normal hN, hN.1.internal, ?_, hxa, rfl, ?_, ?_,
    fun c hc => (hP c hc).2.2.2.2, fun c hc => (hP c hc).2.2.2.1, hPF.2, ?_,
    fun c hc => Or.inl (hP c hc).1, fun c hc h => absurd h (by rw [hnoinv c hc]; simp),
    fun c hc h => absurd h (by rw [hnowd c hc]; simp), ?_, hX, hS,
    (List.filter_sublist).subperm, fun _ _ h => h⟩
  · intro c hc hk
    have hne := hN.2.1 c hc hk
    exact ⟨hne, (hN.2.2 _ _ hne).2 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩⟩
  · intro c L hp hk hx hy _
    have hc : c ∈ Γ.comps := hp.symm.subset (List.mem_cons_self ..)
    rcases hN.1.noIntDot c hc hk with h | h
    · revert h hx; cases c.x <;> simp
    · revert h hy; cases c.y <;> simp
  · exact fun h => Graph.doublyConnected_dcs h
  · intro c hc hl
    have hr := (hP c hc).2.2.2.2.2 hl
    obtain ⟨hm, hi, hw, -, -⟩ := hP c hc
    revert hr hi hw
    simp only [Comp.isGoodKind]
    cases c.kind <;> simp [Kind.isRandom, hm]
  · have : nWD Γ.comps = 0 := by
      unfold nWD
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      simp [hnowd c hc]
    rw [this]
    simp

end Init

section Instances

end Instances

/-! ## The components at an external atom -/

section OAt

variable {k n : ℕ}

/-- The component has an end at the external atom `o`. -/
def step3_atO (o : Fin k) (c : Comp (Atom k n)) : Bool := decide (c.x = .inl o ∨ c.y = .inl o)

/-- Every component of `Γ` at the external atom `o` is a diffusive edge. -/
def Step3ODiff (o : Fin k) (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, (c.x = .inl o ∨ c.y = .inl o) → c.kind.isDiffusive = true

/-- The components of `T` at the external atom `o` are, up to order, those of `Γ`. -/
def Step3OKeep (o : Fin k) (Γ T : Graph k n) : Prop :=
  (T.comps.filter (step3_atO o)).Perm (Γ.comps.filter (step3_atO o))

/-- The components of the output graph `t` at the external atom `o` are, up to order, the images
of those of `Γ`. -/
def Step3OOut (o : Fin k) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  (t.g.comps.filter (step3_atO o)).Perm ((Γ.comps.filter (step3_atO o)).map (Comp.map t.f))

/-- At every external atom at which all components of `Γ` are diffusive, the components of `T`
are, up to order, those of `Γ`. -/
def OK1 (Γ T : Graph k n) : Prop := ∀ o, Step3ODiff o Γ → Step3OKeep o Γ T

/-- At every external atom at which all components of `Γ` are diffusive, the components of the
output graph `t` are, up to order, the images of those of `Γ`. -/
def Step3OO1 (Γ : Graph k n) (t : Tracked k n) : Prop := ∀ o, Step3ODiff o Γ → Step3OOut o Γ t

theorem step3_atO_iff {o : Fin k} {c : Comp (Atom k n)} :
    step3_atO o c = true ↔ (c.x = .inl o ∨ c.y = .inl o) := by
  simp [step3_atO]

theorem Step3ODiff.diff {o : Fin k} {Γ : Graph k n} (hO : Step3ODiff o Γ) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (ho : step3_atO o c = true) : c.kind.isDiffusive = true :=
  hO c hc (step3_atO_iff.1 ho)

theorem Step3OKeep.diff {o : Fin k} {Γ T : Graph k n} (h : Step3OKeep o Γ T) (hO : Step3ODiff o Γ)
    {c : Comp (Atom k n)} (hc : c ∈ T.comps) (ho : step3_atO o c = true) : c.kind.isDiffusive = true :=
  hO.diff (List.mem_filter.1 (h.subset (List.mem_filter.2 ⟨hc, ho⟩))).1 ho

theorem Step3OKeep.atO_false {o : Fin k} {Γ T : Graph k n} (h : Step3OKeep o Γ T) (hO : Step3ODiff o Γ)
    {c : Comp (Atom k n)} (hc : c ∈ T.comps) (hd : c.kind.isDiffusive = false) :
    step3_atO o c = false := by
  cases ho : step3_atO o c
  · rfl
  · rw [h.diff hO hc ho] at hd
    cases hd

theorem Step3OKeep.erase {o : Fin k} {Γ T : Graph k n} (h : Step3OKeep o Γ T) {i : ℕ}
    {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (hco : step3_atO o c = false) (co : Coeff) :
    Step3OKeep o Γ ⟨T.comps.eraseIdx i, co⟩ := by
  have hp := (perm_eraseIdx hc).filter (step3_atO o)
  rw [List.filter_cons_of_neg (by simp [hco])] at hp
  exact hp.symm.trans h

theorem Step3OKeep.append {o : Fin k} {Γ : Graph k n} {L : List (Comp (Atom k n))}
    (h : (L.filter (step3_atO o)).Perm (Γ.comps.filter (step3_atO o))) (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, step3_atO o d = false) (co : Coeff) : Step3OKeep o Γ ⟨L ++ new, co⟩ := by
  have : new.filter (step3_atO o) = [] := List.filter_eq_nil_iff.2 fun d hd => by simp [hnew d hd]
  change ((L ++ new).filter (step3_atO o)).Perm _
  rw [List.filter_append, this, List.append_nil]
  exact h

/-- A map of components that keeps the ends and fixes the components at `o` keeps the components
at `o`. -/
theorem Step3OKeep.map {o : Fin k} {Γ T : Graph k n} (h : Step3OKeep o Γ T)
    (φ : Comp (Atom k n) → Comp (Atom k n)) (hφ : ∀ c, step3_atO o (φ c) = step3_atO o c)
    (hfix : ∀ c ∈ T.comps, step3_atO o c = true → φ c = c) (co : Coeff) :
    Step3OKeep o Γ ⟨T.comps.map φ, co⟩ := by
  change ((T.comps.map φ).filter (step3_atO o)).Perm _
  rw [List.filter_map]
  have e1 : T.comps.filter (step3_atO o ∘ φ) = T.comps.filter (step3_atO o) :=
    List.filter_congr fun c _ => by rw [Function.comp_apply, hφ]
  have e2 : (T.comps.filter (step3_atO o)).map φ = T.comps.filter (step3_atO o) := by
    conv_rhs => rw [← List.map_id (T.comps.filter (step3_atO o))]
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨hc, ho⟩ := List.mem_filter.1 hc
    exact hfix c hc ho
  rw [e1, e2]
  exact h

theorem Comp.step3_map_id'' {V : Type*} (c : Comp V) : c.map id = c := by
  cases c; simp [Comp.map]

theorem OK1.refl (Γ : Graph k n) : OK1 Γ Γ := fun _ _ => List.Perm.refl _

/-- Removing a component that is not diffusive keeps the components at the external atoms. -/
theorem OK1.erase {Γ T : Graph k n} (h : OK1 Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind.isDiffusive = false) (co : Coeff) :
    OK1 Γ ⟨T.comps.eraseIdx i, co⟩ := fun o hO =>
  (h o hO).erase hc ((h o hO).atO_false hO (List.mem_of_getElem? hc) hcd) co

/-- Replacing a component that is not diffusive by components, each at an external atom only if
the replaced one is, keeps the components at the external atoms. -/
theorem OK1.replace {Γ T : Graph k n} (h : OK1 Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind.isDiffusive = false)
    (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, ∀ o : Fin k, step3_atO o d = true → step3_atO o c = true) (co : Coeff) :
    OK1 Γ ⟨T.comps.eraseIdx i ++ new, co⟩ := by
  intro o hO
  have hco : step3_atO o c = false := (h o hO).atO_false hO (List.mem_of_getElem? hc) hcd
  refine Step3OKeep.append ((h o hO).erase hc hco T.coeff) new (fun d hd => ?_) co
  cases hd' : step3_atO o d
  · rfl
  · rw [hnew d hd o hd'] at hco
    cases hco

/-- Adding components that are not at the external atoms at which all components of `Γ` are
diffusive keeps the components there. -/
theorem OK1.append {Γ T : Graph k n} (h : OK1 Γ T) (new : List (Comp (Atom k n)))
    (hnew : ∀ o, Step3ODiff o Γ → ∀ d ∈ new, step3_atO o d = false) (co : Coeff) :
    OK1 Γ ⟨T.comps ++ new, co⟩ := fun o hO => Step3OKeep.append (h o hO) new (hnew o hO) co

/-- Removing the labels keeps the components at the external atoms, if only random components
carry labels. -/
theorem OK1.dropLabels {Γ T : Graph k n} (h : OK1 Γ T)
    (hwf : ∀ c ∈ T.comps, c.label.isSome = true → c.kind.isRandom = true) :
    OK1 Γ T.dropLabels := by
  intro o hO
  change Step3OKeep o Γ ⟨T.comps.map fun c => { c with label := none }, T.coeff⟩
  refine Step3OKeep.map (h o hO) (fun c => { c with label := none }) (fun c => rfl)
    (fun c hc ho => ?_) T.coeff
  have hd := (h o hO).diff hO hc ho
  have hl : c.label = none := by
    by_contra hne
    have hr := hwf c hc (Option.isSome_iff_ne_none.2 hne)
    cases hk : c.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]
  obtain ⟨κ, x, y, m, l⟩ := c
  simp only at hl
  subst hl
  rfl

/-- The graph `T` itself as an output keeps the components at the external atoms. -/
theorem Step3OO1.of_keep {Γ T : Graph k n} (h : OK1 Γ T) : Step3OO1 Γ (Tracked.self T) := by
  intro o hO
  have hid : (Γ.comps.filter (step3_atO o)).map (Comp.map (Tracked.self T).f) =
      Γ.comps.filter (step3_atO o) := by
    conv_rhs => rw [← List.map_id (Γ.comps.filter (step3_atO o))]
    exact List.map_congr_left fun c _ => Comp.step3_map_id'' c
  change (T.comps.filter (step3_atO o)).Perm _
  rw [hid]
  exact h o hO

/-- A component whose ends are ends of `c` or the internal atom `X` is at the external atom `o`
only if `c` is. -/
theorem atO_of_ends {o : Fin k} {c d : Comp (Atom k n)} {X : Atom k n}
    (hX : X.isRight = true) (ho : step3_atO o d = true) (hx : d.x = c.x ∨ d.x = c.y ∨ d.x = X)
    (hy : d.y = c.x ∨ d.y = c.y ∨ d.y = X) : step3_atO o c = true := by
  have hXo : X ≠ .inl o := by
    rintro rfl
    cases hX
  rw [step3_atO_iff] at ho ⊢
  rcases ho with h | h
  · rcases hx with e | e | e <;> rw [e] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hXo
  · rcases hy with e | e | e <;> rw [e] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hXo

/-- The components at `o` under `O_merge`, when `o` is the only atom with image `o` and every
component at `o` is diffusive. -/
theorem step3_filter_atO_merge {m : ℕ} (o : Fin k) (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) (hf : ∀ u, f u = .inl o ↔ u = .inl o) :
    ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, step3_atO o c = true → c.kind.isDiffusive = true) →
      (L.filterMap (step3_mergeComp rep f)).filter (step3_atO o) = (L.filter (step3_atO o)).map (Comp.map f)
  | [], _ => rfl
  | c :: L, hL => by
    have ih := step3_filter_atO_merge o rep f hf L fun d hd => hL d (List.mem_cons_of_mem _ hd)
    rw [List.filterMap_cons]
    by_cases ho : step3_atO o c = true
    · have hdf := hL c (List.mem_cons_self ..) ho
      have hnd : c.kind ≠ .dot := fun h => by rw [h] at hdf; cases hdf
      have hns : c.kind.isSolid = false := by
        cases hk : c.kind <;> simp_all [Kind.isSolid, Kind.isDiffusive]
      rw [step3_mergeComp_other hnd hns, List.filter_cons_of_pos ho]
      have ho' : step3_atO o (c.map f) = true := by
        rw [step3_atO_iff] at ho ⊢
        simp only [Comp.map]
        rcases ho with h | h
        · exact Or.inl ((hf _).2 h)
        · exact Or.inr ((hf _).2 h)
      rw [List.filter_cons_of_pos ho', ih, List.map_cons]
    · have ho2 : ¬ (c.x = .inl o ∨ c.y = .inl o) := fun h => ho (step3_atO_iff.2 h)
      push Not at ho2
      obtain ⟨hx, hy⟩ := ho2
      have hx' : f c.x ≠ .inl o := fun h => hx ((hf _).1 h)
      have hy' : f c.y ≠ .inl o := fun h => hy ((hf _).1 h)
      rw [List.filter_cons_of_neg ho]
      rcases hm : step3_mergeComp rep f c with _ | c'
      · exact ih
      · have hc' : step3_atO o c' = false := by
          unfold step3_mergeComp at hm
          split_ifs at hm
          · obtain rfl := Option.some.inj hm
            simp [step3_atO, Comp.map, hx']
          · obtain rfl := Option.some.inj hm
            simp [step3_atO, Comp.map, hx', hy']
        simp only
        rw [List.filter_cons_of_neg (by simp [hc']), ih]

/-- The atom map of `O_merge` sends only `o` to `o`. -/
theorem Step3MergeSpec.f_iff {Γ : Graph k n} {t : Tracked k n} (hs : Step3MergeSpec Γ t)
    (o : Fin k) (u : Atom k n) : t.f u = .inl o ↔ u = .inl o := by
  obtain ⟨φ, hφ, -⟩ := hs.f_inr
  rcases u with a | i
  · simp [hs.f_inl]
  · rw [hφ]
    simp

theorem step3_filter_atO_nd {o : Fin k} {L : List (Comp (Atom k n))}
    (hL : ∀ c ∈ L, step3_atO o c = true → c.kind ≠ .dot) :
    L.filter (step3_atO o) = (L.filter fun c => !decide (c.kind = .dot)).filter (step3_atO o) := by
  rw [List.filter_filter]
  refine List.filter_congr fun c hc => ?_
  by_cases ho : step3_atO o c = true
  · simp [ho, hL c hc ho]
  · simp [ho]

/-- The output of `O_merge` followed by the removal of redundant dotted edges keeps the components
at the external atoms. -/
theorem step3_final_oo1 {Γ T : Graph k n} {t : Tracked k n} (hs : Step3MergeSpec T t)
    (hK : OK1 Γ T) {g' : Graph k t.nOut} (hsub : g'.comps.Sublist t.g.comps)
    (hnd : (g'.comps.filter fun d => !decide (d.kind = .dot)).Perm
      (t.g.comps.filter fun d => !decide (d.kind = .dot))) :
    Step3OO1 Γ ⟨t.nOut, g', t.f⟩ := by
  intro o hO
  have hK' := hK o hO
  have hT : ∀ c ∈ T.comps, step3_atO o c = true → c.kind.isDiffusive = true :=
    fun c hc ho => hK'.diff hO hc ho
  have hm := step3_filter_atO_merge o T.step3_mrep t.f (hs.f_iff o) T.comps hT
  rw [← hs.comps_eq] at hm
  have hnd1 : ∀ c ∈ t.g.comps, step3_atO o c = true → c.kind ≠ .dot := by
    intro c hc ho h
    have hc' : c ∈ (T.comps.filter (step3_atO o)).map (Comp.map t.f) := by
      rw [← hm]
      exact List.mem_filter.2 ⟨hc, ho⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨hdT, hdo⟩ := List.mem_filter.1 hd
    have := hT d hdT hdo
    simp only [Comp.map] at h
    rw [h] at this
    cases this
  have hnd2 : ∀ c ∈ g'.comps, step3_atO o c = true → c.kind ≠ .dot :=
    fun c hc ho => hnd1 c (hsub.subset hc) ho
  change (g'.comps.filter (step3_atO o)).Perm ((Γ.comps.filter (step3_atO o)).map (Comp.map t.f))
  rw [step3_filter_atO_nd hnd2]
  refine (hnd.filter (step3_atO o)).trans ?_
  rw [← step3_filter_atO_nd hnd1, hm]
  exact List.Perm.map _ hK'

end OAt


section OSteps

variable {k n : ℕ}

theorem atO_of_xx {o : Fin k} {c d : Comp (Atom k n)} (ho : step3_atO o d = true)
    (hx : d.x = c.x) (hy : d.y = c.x) : step3_atO o c = true := by
  rw [step3_atO_iff] at ho ⊢
  rw [hx, hy] at ho
  exact Or.inl (ho.elim id id)

/-- A component between an atom of a random component of `Γ` and the internal atom `X` is not at
an external atom at which all components of `Γ` are diffusive. -/
theorem split_atO {o : Fin k} {Γ : Graph k n} {X u : Atom k n} {c₀ : Comp (Atom k n)}
    (hX : X.isRight = true) (hO : Step3ODiff o Γ) (hc₀ : c₀ ∈ Γ.comps)
    (hr : c₀.kind.isRandom = true) (hu : u ∈ [c₀.x, c₀.y]) (κ : Kind) :
    step3_atO o (mkC κ u X) = false := by
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
  simp [step3_atO, mkC, huo, hXo]

end OSteps

section OPhases

variable {k n : ℕ}

end OPhases

end RBM8D.Graphs
