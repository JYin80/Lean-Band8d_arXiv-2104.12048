import RBM8D.Graph.QExp.Defs

/-!
# The first step of the `Q`-expansions

[II, Lemma 4.11], with [II, (4.17)–(4.21)].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

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

end GraphCard

/-! ## Dotted components of a list -/

section Dots

variable {k n : ℕ}

/-- The graph on the atoms whose edges are the dotted components of a list. -/
def step1_dg (L : List (Comp (Atom k n))) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ L, c.kind = .dot ∧ c.x = u ∧ c.y = v

/-- The number of dotted components of a list. -/
def step1_nD (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => decide (c.kind = .dot)).length

/-- The dot excess of a list of components. -/
def step1_eL (L : List (Comp (Atom k n))) : ℤ :=
  (step1_nD L : ℤ) - ((k + n : ℕ) : ℤ) + (Nat.card (step1_dg L).ConnectedComponent : ℤ)

private theorem dg_adj {L : List (Comp (Atom k n))} {a b : Atom k n} :
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
private theorem dg_reach_of_mem {L : List (Comp (Atom k n))} {c : Comp (Atom k n)} (hc : c ∈ L)
    (hk : c.kind = .dot) : (step1_dg L).Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (dg_adj.2 ⟨h, c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩).reachable

/-- Reachability in the graph of dotted components is monotone in the dotted components. -/
private theorem dg_reach_mono {L L' : List (Comp (Atom k n))}
    (h : ∀ c ∈ L, c.kind = .dot → c ∈ L') {a b : Atom k n} (hr : (step1_dg L).Reachable a b) :
    (step1_dg L').Reachable a b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    obtain ⟨hne, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    refine SimpleGraph.Reachable.trans ?_ ih
    exact (dg_adj.2 ⟨hne, c, h c hc hk, hk, hxy⟩).reachable

/-- The graph of dotted components depends only on the dotted components. -/
private theorem dg_congr {L L' : List (Comp (Atom k n))}
    (h : ∀ c, c.kind = .dot → (c ∈ L ↔ c ∈ L')) : step1_dg L = step1_dg L' := by
  ext a b
  rw [dg_adj, dg_adj]
  constructor
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).1 hc, hk, hxy⟩
  · rintro ⟨hne, c, hc, hk, hxy⟩
    exact ⟨hne, c, (h c hk).2 hc, hk, hxy⟩

private theorem dg_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step1_dg L = step1_dg L' :=
  dg_congr fun _ _ => h.mem_iff

private theorem nD_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step1_nD L = step1_nD L' :=
  (h.filter _).length_eq

private theorem eL_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') : step1_eL L = step1_eL L' := by
  simp only [step1_eL, nD_perm h, dg_perm h]

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

private theorem nD_cons (c : Comp (Atom k n)) (L : List (Comp (Atom k n))) :
    step1_nD (c :: L) = step1_nD L + if c.kind = .dot then 1 else 0 := by
  unfold step1_nD
  by_cases h : c.kind = .dot
  · rw [List.filter_cons_of_pos (by simp [h])]
    simp [h]
  · rw [List.filter_cons_of_neg (by simp [h])]
    simp [h]

private theorem eL_cons_nondot {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind ≠ .dot) : step1_eL (c :: L) = step1_eL L := by
  simp [step1_eL, nD_cons, hk, dg_cons_nondot L hk]

/-- A dotted component between two blocks keeps the dot excess. -/
private theorem eL_cons_dot_new {c : Comp (Atom k n)} (L : List (Comp (Atom k n)))
    (hk : c.kind = .dot) (hr : ¬ (step1_dg L).Reachable c.x c.y) : step1_eL (c :: L) = step1_eL L := by
  have h := card_cc_add_edge (G := step1_dg L) (H := step1_dg (c :: L)) (dg_cons_dot_adj L hk) hr
  simp only [step1_eL, nD_cons, hk, ite_true, h]
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
  simp only [step1_eL, nD_cons, hk, ite_true, h]
  push_cast
  ring

/-- Removing a dotted component whose ends are joined by the others lowers the dot excess by
`1` and keeps the blocks. -/
private theorem eL_eraseIdx_red {L : List (Comp (Atom k n))} {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) (hk : c.kind = .dot) (hr : (step1_dg (L.eraseIdx i)).Reachable c.x c.y) :
    step1_eL (L.eraseIdx i) + 1 = step1_eL L ∧
      ∀ a b, (step1_dg (L.eraseIdx i)).Reachable a b ↔ (step1_dg L).Reachable a b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  have hp := List.getElem_cons_eraseIdx_perm hi
  refine ⟨?_, fun a b => ?_⟩
  · rw [← eL_perm hp, eL_cons_dot_red _ hk hr]
  · rw [← dg_perm hp, dg_reach_cons_red _ hk hr]

/-- A labelling that agrees on the ends of every dotted component agrees along paths of dotted
components. -/
private theorem sigma_eq_of_reach {ι : Type*} {L : List (Comp (Atom k n))} (σ : Atom k n → ι)
    (hz : ∀ c ∈ L, c.kind = .dot → σ c.x = σ c.y) {a b : Atom k n}
    (hr : (step1_dg L).Reachable a b) : σ a = σ b := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    obtain ⟨-, c, hc, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := dg_adj.1 hadj
    · exact (hz c hc hk).trans ih
    · exact (hz c hc hk).symm.trans ih

end Dots

section Blocks

variable {V : Type*} [DecidableEq V]

end Blocks

/-! ## The data of `O_merge` -/

section MergeData

variable {k n : ℕ}

/-- The representative of an atom in the dot blocks of a graph. -/
def Graph.step1_mrep (Γ : Graph k n) : Atom k n → Atom k n :=
  blockRep (dotBlocks (allAtoms k n) Γ.comps)

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
def step1_mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

/-- The structure of a tracked graph `t` with `Γ.mergeT = some t`: its components, its atom map
and its blocks. -/
structure Step1MergeSpec (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps = Γ.comps.filterMap (step1_mergeComp Γ.step1_mrep t.f)
  coeff_eq : t.g.coeff = Γ.coeff
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_surj : Function.Surjective t.f
  f_inr : ∃ g : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (g i)) ∧ Function.Surjective g
  f_eq : ∀ u v, Γ.step1_mrep u = Γ.step1_mrep v → u.isRight = true → v.isRight = true → t.f u = t.f v
  f_ne : ∀ u v, Γ.step1_mrep u ≠ Γ.step1_mrep v → t.f u ≠ t.f v
  xdot_ne : ∀ c ∈ Γ.comps, c.kind = .xdot → Γ.step1_mrep c.x ≠ Γ.step1_mrep c.y

end MergeData

section MergeComp

variable {k n : ℕ}

end MergeComp

section MergeFacts

variable {k n : ℕ}

private theorem mergeComp_other {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hd : c.kind ≠ .dot) (hs : c.kind.isSolid = false) :
    step1_mergeComp rep f c = some (c.map f) := by
  unfold step1_mergeComp
  simp [hd, hs]

variable {Γ : Graph k n} {t : Tracked k n}

end MergeFacts

/-! ## Blocks, scaling order and dot excess under `O_merge` -/

section MergeBlocks

variable {k n : ℕ}

variable {Γ : Graph k n} {t : Tracked k n}

/-- Dotted components between internal atoms are needed. -/
def NonRedInt (L : List (Comp (Atom k n))) : Prop :=
  ∀ (c : Comp (Atom k n)) (L' : List (Comp (Atom k n))), L.Perm (c :: L') → c.kind = .dot →
    c.x.isRight = true → c.y.isRight = true → ¬ (step1_dg L').Reachable c.x c.y

end MergeBlocks

/-! ## Doubly connected structures -/

section Tagged

variable {k n m : ℕ}

/-- The kinds usable in a blue net whose solid edges have charge `bc`: the solid edges of charge
`bc` and the ghost edges. -/
def Kind.blueC (bc : Charge) : Kind → Bool
  | .G c => decide (c = bc)
  | .ghost => true
  | _ => false

private theorem Kind.blueC_plus (κ : Kind) : κ.blueC .plus = κ.isBlue := by
  cases κ with
  | G c => cases c <;> rfl
  | _ => rfl

/-- A component with a tag. -/
abbrev TC (k n : ℕ) : Type := Comp (Atom k n) × Option Bool

/-- The graph on the internal atoms whose edges join two atoms of one molecule, or the two ends of
a component of `L` with the tag `some t`. -/
def Graph.netT (Γ : Graph k n) (L : List (TC k n)) (t : Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => Γ.SameMol (Sum.inr a) (Sum.inr b) ∨
    ∃ p ∈ L, p.2 = some t ∧ p.1.x = Sum.inr a ∧ p.1.y = Sum.inr b

/-- The tagged list `L` is a doubly connected structure on `Γ` with blue charge `bc`: it lists the
components of `Γ`, black ones are diffusive, blue ones are diffusive or blue, and each net spans the
internal atoms. -/
structure Graph.DCT (bc : Charge) (Γ : Graph k n) (L : List (TC k n)) : Prop where
  map_fst : L.map Prod.fst = Γ.comps
  black : ∀ p ∈ L, p.2 = some false → p.1.kind.isDiffusive = true
  blue : ∀ p ∈ L, p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true
  spanBlack : (Γ.netT L false).Preconnected
  spanBlue : (Γ.netT L true).Preconnected

/-- The graph has a doubly connected structure with blue charge `bc`. -/
def Graph.Step1DCS (bc : Charge) (Γ : Graph k n) : Prop := ∃ L, Γ.DCT bc L

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

/-- A tagged list of the components of `Γ` with tags `some false` on `black` and `some true` on
`blue`. -/
private def Graph.tagList (Γ : Graph k n) (black blue : Finset (Fin Γ.comps.length)) :
    List (TC k n) :=
  (List.finRange Γ.comps.length).map fun i =>
    (Γ.comps[i.1], if i ∈ black then some false else if i ∈ blue then some true else none)

private theorem Graph.tagList_map_fst (Γ : Graph k n) (black blue : Finset (Fin Γ.comps.length)) :
    (Γ.tagList black blue).map Prod.fst = Γ.comps := by
  unfold Graph.tagList
  rw [List.map_map]
  exact List.map_getElem_finRange Γ.comps

private theorem Graph.tagList_mem {Γ : Graph k n} {black blue : Finset (Fin Γ.comps.length)}
    {p : TC k n} (hp : p ∈ Γ.tagList black blue) : ∃ i : Fin Γ.comps.length,
    p = (Γ.comps[i.1], if i ∈ black then some false else if i ∈ blue then some true else none) := by
  unfold Graph.tagList at hp
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
  exact ⟨i, rfl⟩

/-- The net of a set of components is the net of the tagged list that marks them. -/
private theorem Graph.net_eq_netT {Γ : Graph k n} {black blue : Finset (Fin Γ.comps.length)}
    (B : Finset (Fin Γ.comps.length)) (t : Bool)
    (hB : ∀ i : Fin Γ.comps.length,
      (if i ∈ black then some false else if i ∈ blue then some true else none) = some t ↔ i ∈ B) :
    Γ.net B = Γ.netT (Γ.tagList black blue) t := by
  unfold Graph.net Graph.netT
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
private theorem Graph.doublyConnected_dcs {Γ : Graph k n} (h : Γ.DoublyConnected) :
    Γ.Step1DCS .plus := by
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

/-- A tagged component of `L` has neither the kind `xdot` nor a weight kind if it is tagged
or joins molecules: its kind is diffusive, blue or joins molecules. -/
private theorem Graph.DCT.kind_of_tag {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {p : TC k n} (hp : p ∈ L) (ht : p.2 ≠ none) :
    p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true := by
  rcases hp2 : p.2 with _ | _ | _
  · exact absurd hp2 ht
  · exact Or.inl (h.black p hp hp2)
  · exact h.blue p hp hp2

end Tagged

/-! ## Values: replacing one component -/

section Values

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι]

/-- The charge as a ring homomorphism: the identity or complex conjugation. -/
private def Charge.hom : Charge → ℂ →+* ℂ
  | .plus => RingHom.id ℂ
  | .minus => starRingEnd ℂ

private theorem Charge.apply_eq (ch : Charge) (z : ℂ) : ch.apply z = ch.hom z := by
  cases ch <;> rfl

private theorem Comp.val_label {V : Type*} (d : Data ι) (σ : V → ι) (c : Comp V)
    (l : Option (PQ × V)) : Comp.val d σ { c with label := l } = Comp.val d σ c := rfl

end Values

/-! ## Good factors -/

section Good

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

private theorem good_pow' (A : ModelAdm Ω ι PF D) {f : Ω → ℂ} (hf : A.Good f) (n : ℕ) :
    A.Good fun ω => f ω ^ n := by
  induction n with
  | zero => simpa using A.laws.good_const 1
  | succ n ih =>
    have h := A.laws.good_mul _ _ ih hf
    convert h using 1
    funext ω
    simp [pow_succ]

private theorem good_sum_range (A : ModelAdm Ω ι PF D) (f : ℕ → Ω → ℂ)
    (hf : ∀ j, A.Good (f j)) (n : ℕ) : A.Good fun ω => ∑ j ∈ Finset.range n, f j ω := by
  induction n with
  | zero => simpa using A.laws.good_const 0
  | succ n ih =>
    have h := A.laws.good_add _ _ ih (hf n)
    convert h using 1
    funext ω
    simp [Finset.sum_range_succ]

private theorem good_charge (A : ModelAdm Ω ι PF D) (ch : Charge) {f : Ω → ℂ} (hf : A.Good f) :
    A.Good fun ω => ch.apply (f ω) := by
  cases ch
  · exact hf
  · exact A.good_star f hf

private theorem good_val (A : ModelAdm Ω ι PF D) {V : Type*} (σ : V → ι) (c : Comp V)
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

/-! ## Linearity of the label operators -/

section Linear

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

private theorem P_zero (A : ModelAdm Ω ι PF D) (u : ι) : PF.P u (fun _ => 0) = fun _ => 0 := by
  have h := A.laws.smul u 0 (fun _ => (0 : ℂ)) (A.laws.good_const 0)
  have e : ((0 : ℂ) • (fun _ : Ω => (0 : ℂ))) = fun _ => 0 := by funext ω; simp
  rw [e] at h
  rw [h]
  funext ω
  simp

private theorem op_add (A : ModelAdm Ω ι PF D) (pq : PQ) (u : ι) {f g : Ω → ℂ} (hf : A.Good f)
    (hg : A.Good g) : PF.op pq u (f + g) = PF.op pq u f + PF.op pq u g := by
  cases pq
  · exact A.laws.add u f g hf hg
  · simp only [PFamily.op]
    rw [A.laws.add u f g hf hg]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

private theorem op_smul (A : ModelAdm Ω ι PF D) (pq : PQ) (u : ι) (a : ℂ) {f : Ω → ℂ}
    (hf : A.Good f) : PF.op pq u (a • f) = a • PF.op pq u f := by
  cases pq
  · exact A.laws.smul u a f hf
  · simp only [PFamily.op]
    rw [A.laws.smul u a f hf]
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

private theorem op_zero (A : ModelAdm Ω ι PF D) (pq : PQ) (u : ι) :
    PF.op pq u (fun _ => 0) = fun _ => 0 := by
  cases pq
  · exact P_zero A u
  · simp only [PFamily.op]
    rw [P_zero A u]
    funext ω
    simp

private theorem good_lincomb (A : ModelAdm Ω ι PF D) :
    ∀ l : List (ℂ × (Ω → ℂ)), (∀ p ∈ l, A.Good p.2) →
      A.Good fun ω => (l.map fun p => p.1 * p.2 ω).sum := by
  intro l
  induction l with
  | nil => intro _; simpa using A.laws.good_const 0
  | cons p l ih =>
    intro h
    have h1 := A.laws.good_add _ _
      (A.laws.good_mul _ _ (A.laws.good_const p.1) (h p (List.mem_cons_self ..)))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
    convert h1 using 1
    funext ω
    simp

/-- The label operators are linear on good functions. -/
private theorem op_lincomb (A : ModelAdm Ω ι PF D) (pq : PQ) (u : ι) :
    ∀ l : List (ℂ × (Ω → ℂ)), (∀ p ∈ l, A.Good p.2) →
      PF.op pq u (fun ω => (l.map fun p => p.1 * p.2 ω).sum) =
        fun ω => (l.map fun p => p.1 * PF.op pq u p.2 ω).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    simpa using op_zero A pq u
  | cons p l ih =>
    intro h
    have hp := h p (List.mem_cons_self ..)
    have hl := fun q hq => h q (List.mem_cons_of_mem _ hq)
    have e : (fun ω => ((p :: l).map fun p => p.1 * p.2 ω).sum) =
        (p.1 • p.2) + fun ω => (l.map fun p => p.1 * p.2 ω).sum := by
      funext ω
      simp
    have hs : A.Good (p.1 • p.2) := by
      have := A.laws.good_mul _ _ (A.laws.good_const p.1) hp
      convert this using 1
    rw [e, op_add A pq u hs (good_lincomb A l hl), op_smul A pq u p.1 hp, ih hl]
    funext ω
    simp

end Linear

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

private theorem filter_unl_of {L : List (Comp (Atom k n))} (h : ∀ c ∈ L, c.label = none) :
    L.filter (fun c => c.label.isNone) = L :=
  List.filter_eq_self.2 fun c hc => by simp [h c hc]

private theorem filter_grp_of_none {L : List (Comp (Atom k n))} (h : ∀ c ∈ L, c.label = none)
    (ℓ : PQ × Atom k n) : L.filter (fun c => decide (c.label = some ℓ)) = [] :=
  List.filter_eq_nil_iff.2 fun c hc => by simp [h c hc]

private theorem filterMap_label_of_none {L : List (Comp (Atom k n))}
    (h : ∀ c ∈ L, c.label = none) : L.filterMap Comp.label = [] :=
  List.filterMap_eq_nil_iff.2 fun c hc => h c hc

private theorem termR_replace_none (σ : Atom k n → ι) (ω : Ω)
    (rest : List (Comp (Atom k n))) (c : Comp (Atom k n)) (hc : c.label = none) (coeff : Coeff)
    (outs : List (Coeff × List (Comp (Atom k n))))
    (hlab : ∀ o ∈ outs, ∀ c' ∈ o.2, c'.label = none)
    (hval : Comp.val (D ω) σ c = (outs.map fun o => Coeff.eval (D ω).m o.1 *
      (o.2.map (Comp.val (D ω) σ)).prod).sum) :
    (outs.map fun o => Graph.termR (⟨rest ++ o.2, o.1 * coeff⟩ : Graph k n) PF D σ ω).sum =
      Graph.termR (⟨c :: rest, coeff⟩ : Graph k n) PF D σ ω := by
  set Fr := ((rest.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod with hFr
  set Lab := (((rest.filterMap Comp.label).dedup).map fun ℓ => PF.op ℓ.1 (σ ℓ.2)
    (fun ω' => ((rest.filter fun c => decide (c.label = some ℓ)).map
      (Comp.val (D ω') σ)).prod) ω).prod with hLab
  have hterm : ∀ o ∈ outs, Graph.termR (⟨rest ++ o.2, o.1 * coeff⟩ : Graph k n) PF D σ ω =
      (Coeff.eval (D ω).m coeff * Fr * Lab) *
        (Coeff.eval (D ω).m o.1 * (o.2.map (Comp.val (D ω) σ)).prod) := by
    intro o ho
    have h0 := hlab o ho
    simp only [Graph.termR, Graph.labels, List.filter_append, filter_unl_of h0,
      List.filterMap_append, filterMap_label_of_none h0, List.append_nil, filter_grp_of_none h0,
      List.map_append, List.prod_append, map_mul, Coeff.eval]
    rw [hFr, hLab]
    ring
  rw [List.map_congr_left hterm, List.sum_map_mul_left, ← hval]
  have hc1 : (c :: rest).filter (fun c => c.label.isNone) =
      c :: rest.filter (fun c => c.label.isNone) := List.filter_cons_of_pos (by simp [hc])
  have hc2 : ∀ ℓ : PQ × Atom k n, (c :: rest).filter (fun c => decide (c.label = some ℓ)) =
      rest.filter (fun c => decide (c.label = some ℓ)) :=
    fun ℓ => List.filter_cons_of_neg (by simp [hc])
  have hc3 : (c :: rest).filterMap Comp.label = rest.filterMap Comp.label := by
    simp [hc]
  simp only [Graph.termR, Graph.labels, hc1, hc2, hc3, List.map_cons, List.prod_cons]
  rw [← hFr, ← hLab]
  ring

/-- The product of the component values, as a function of the sample point. -/
private def Fn (D : Ω → Data ι) (σ : Atom k n → ι) (cs : List (Comp (Atom k n))) : Ω → ℂ :=
  fun ω => (cs.map (Comp.val (D ω) σ)).prod

private theorem Fn_append (σ : Atom k n → ι) (cs ds : List (Comp (Atom k n))) :
    Fn D σ (cs ++ ds) = Fn D σ cs * Fn D σ ds := by
  funext ω
  simp [Fn]

private theorem good_Fn (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) :
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

private theorem mem_labs {L : List (Comp (Atom k n))} {a : PQ × Atom k n} :
    a ∈ (L.filterMap Comp.label).dedup ↔ ∃ c ∈ L, c.label = some a := by
  simp [List.mem_dedup, List.mem_filterMap]

private theorem labs_perm {L L' : List (Comp (Atom k n))}
    (h : ∀ a, (∃ c ∈ L, c.label = some a) ↔ ∃ c ∈ L', c.label = some a) :
    ((L.filterMap Comp.label).dedup).Perm ((L'.filterMap Comp.label).dedup) :=
  (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).2
    fun a => by rw [mem_labs, mem_labs]; exact h a

/-- The list without the label `ℓ`. -/
private def eraseL (l : List (PQ × Atom k n)) (ℓ : PQ × Atom k n) : List (PQ × Atom k n) :=
  l.filter fun ℓ' => decide (ℓ' ≠ ℓ)

private theorem prod_map_eraseL {l : List (PQ × Atom k n)} (hl : l.Nodup) {ℓ : PQ × Atom k n}
    (hℓ : ℓ ∈ l) (f : PQ × Atom k n → ℂ) :
    (l.map f).prod = f ℓ * ((eraseL l ℓ).map f).prod := by
  induction l with
  | nil => simp at hℓ
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    by_cases hal : a = ℓ
    · subst hal
      have : eraseL (a :: t) a = t := by
        simp only [eraseL, List.filter_cons]
        simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
        exact List.filter_eq_self.2 fun b hb => by
          simp only [decide_eq_true_eq]
          rintro rfl
          exact hl.1 hb
      rw [this]
      simp
    · have hℓt : ℓ ∈ t := by
        rcases List.mem_cons.1 hℓ with h | h
        · exact absurd h.symm hal
        · exact h
      have : eraseL (a :: t) ℓ = a :: eraseL t ℓ := by
        simp [eraseL, hal]
      rw [this, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih hl.2 hℓt]
      ring

private theorem termR_split (L : List (Comp (Atom k n))) (co : Coeff) (σ : Atom k n → ι)
    (ω : Ω) (ℓ : PQ × Atom k n) (hℓ : ∃ c ∈ L, c.label = some ℓ) :
    Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω =
      Coeff.eval (D ω).m co * ((L.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod *
        (PF.op ℓ.1 (σ ℓ.2) (Fn D σ (L.filter fun c => decide (c.label = some ℓ))) ω *
          ((eraseL ((L.filterMap Comp.label).dedup) ℓ).map fun ℓ' => PF.op ℓ'.1 (σ ℓ'.2)
            (Fn D σ (L.filter fun c => decide (c.label = some ℓ'))) ω).prod) := by
  have hmem := mem_labs.2 hℓ
  simp only [Graph.termR, Graph.labels]
  rw [prod_map_eraseL (List.nodup_dedup _) hmem]
  rfl

private theorem others_eq {L L' : List (Comp (Atom k n))} (σ : Atom k n → ι) (ω : Ω)
    (ℓ : PQ × Atom k n)
    (hperm : ((L.filterMap Comp.label).dedup).Perm ((L'.filterMap Comp.label).dedup))
    (hgrp : ∀ ℓ', ℓ' ≠ ℓ → L.filter (fun c => decide (c.label = some ℓ')) =
      L'.filter (fun c => decide (c.label = some ℓ'))) :
    ((eraseL ((L.filterMap Comp.label).dedup) ℓ).map fun ℓ' => PF.op ℓ'.1 (σ ℓ'.2)
        (Fn D σ (L.filter fun c => decide (c.label = some ℓ'))) ω).prod =
      ((eraseL ((L'.filterMap Comp.label).dedup) ℓ).map fun ℓ' => PF.op ℓ'.1 (σ ℓ'.2)
        (Fn D σ (L'.filter fun c => decide (c.label = some ℓ'))) ω).prod := by
  have hp : (eraseL ((L.filterMap Comp.label).dedup) ℓ).Perm
      (eraseL ((L'.filterMap Comp.label).dedup) ℓ) := hperm.filter _
  rw [(hp.map (fun ℓ' => PF.op ℓ'.1 (σ ℓ'.2)
    (Fn D σ (L.filter fun c => decide (c.label = some ℓ'))) ω)).prod_eq]
  congr 1
  refine List.map_congr_left fun ℓ' hℓ' => ?_
  have hℓ'' : ℓ' ≠ ℓ := by
    simpa [eraseL] using (List.mem_filter.1 hℓ').2
  rw [hgrp ℓ' hℓ'']

private theorem filter_unl_of_some {M : List (Comp (Atom k n))} {ℓ : PQ × Atom k n}
    (h : ∀ c ∈ M, c.label = some ℓ) : M.filter (fun c => c.label.isNone) = [] :=
  List.filter_eq_nil_iff.2 fun c hc => by simp [h c hc]

private theorem filter_grp_of_some {M : List (Comp (Atom k n))} {ℓ : PQ × Atom k n}
    (h : ∀ c ∈ M, c.label = some ℓ) : M.filter (fun c => decide (c.label = some ℓ)) = M :=
  List.filter_eq_self.2 fun c hc => by simp [h c hc]

private theorem filter_grp_ne_of_some {M : List (Comp (Atom k n))} {ℓ ℓ' : PQ × Atom k n}
    (h : ∀ c ∈ M, c.label = some ℓ) (hne : ℓ' ≠ ℓ) :
    M.filter (fun c => decide (c.label = some ℓ')) = [] :=
  List.filter_eq_nil_iff.2 fun c hc => by simp [h c hc, Ne.symm hne]

private theorem termR_replace_some (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) (ω : Ω)
    (rest : List (Comp (Atom k n))) (c : Comp (Atom k n)) (ℓ : PQ × Atom k n)
    (hc : c.label = some ℓ) (coeff : Coeff) (outs : List (Coeff × List (Comp (Atom k n))))
    (hlab : ∀ o ∈ outs, ∀ c' ∈ o.2, c'.label = some ℓ)
    (hgood : ∀ c' ∈ c :: rest, c'.label = some ℓ → c'.isGoodKind = true)
    (hgood' : ∀ o ∈ outs, ∀ c' ∈ o.2, c'.isGoodKind = true)
    (hkeep : ∀ o ∈ outs, o.2 ≠ [] ∨ ∃ c' ∈ rest, c'.label = some ℓ)
    (hval : ∀ ω, Comp.val (D ω) σ c = (outs.map fun o => Coeff.eval (D ω).m o.1 *
      (o.2.map (Comp.val (D ω) σ)).prod).sum) :
    (outs.map fun o => Graph.termR (⟨rest ++ o.2, o.1 * coeff⟩ : Graph k n) PF D σ ω).sum =
      Graph.termR (⟨c :: rest, coeff⟩ : Graph k n) PF D σ ω := by
  set R : Ω → ℂ := Fn D σ (rest.filter fun c => decide (c.label = some ℓ)) with hR
  set U := ((rest.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod with hU
  set Oth := ((eraseL (((c :: rest).filterMap Comp.label).dedup) ℓ).map fun ℓ' =>
    PF.op ℓ'.1 (σ ℓ'.2) (Fn D σ ((c :: rest).filter fun c => decide (c.label = some ℓ'))) ω).prod
    with hOth
  have hRgood : A.Good R := by
    refine good_Fn A σ _ fun c' hc' => ?_
    obtain ⟨hc'1, hc'2⟩ := List.mem_filter.1 hc'
    exact hgood c' (List.mem_cons_of_mem _ hc'1) (by simpa using hc'2)
  -- the constants
  have hm : ∀ ω', (D ω').m = msc A.z := A.data_m
  set a : Coeff × List (Comp (Atom k n)) → ℂ := fun o => Coeff.eval (msc A.z) o.1 with ha
  have hval' : ∀ ω', Comp.val (D ω') σ c =
      (outs.map fun o => a o * (o.2.map (Comp.val (D ω') σ)).prod).sum := by
    intro ω'
    rw [hval ω', hm ω']
  -- the left side, term by term
  have hterm : ∀ o ∈ outs, Graph.termR (⟨rest ++ o.2, o.1 * coeff⟩ : Graph k n) PF D σ ω =
      (a o * Coeff.eval (D ω).m coeff * U) *
        (PF.op ℓ.1 (σ ℓ.2) (fun ω' => R ω' * Fn D σ o.2 ω') ω * Oth) := by
    intro o ho
    have h0 := hlab o ho
    have hℓo : ∃ c' ∈ rest ++ o.2, c'.label = some ℓ := by
      rcases hkeep o ho with h | ⟨c', hc', hc'l⟩
      · obtain ⟨c', hc'⟩ := List.exists_mem_of_ne_nil _ h
        exact ⟨c', List.mem_append_right _ hc', h0 c' hc'⟩
      · exact ⟨c', List.mem_append_left _ hc', hc'l⟩
    rw [termR_split _ _ σ ω ℓ hℓo]
    have e1 : (rest ++ o.2).filter (fun c => c.label.isNone) =
        rest.filter (fun c => c.label.isNone) := by
      rw [List.filter_append, filter_unl_of_some h0, List.append_nil]
    have e2 : (rest ++ o.2).filter (fun c => decide (c.label = some ℓ)) =
        rest.filter (fun c => decide (c.label = some ℓ)) ++ o.2 := by
      rw [List.filter_append, filter_grp_of_some h0]
    have hperm : (((c :: rest).filterMap Comp.label).dedup).Perm
        (((rest ++ o.2).filterMap Comp.label).dedup) := by
      refine labs_perm fun b => ?_
      constructor
      · rintro ⟨c', hc', hc'l⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · rw [hc] at hc'l
          obtain rfl : ℓ = b := Option.some.inj hc'l
          exact hℓo
        · exact ⟨c', List.mem_append_left _ hc', hc'l⟩
      · rintro ⟨c', hc', hc'l⟩
        rcases List.mem_append.1 hc' with hc' | hc'
        · exact ⟨c', List.mem_cons_of_mem _ hc', hc'l⟩
        · rw [h0 c' hc'] at hc'l
          obtain rfl : ℓ = b := Option.some.inj hc'l
          exact ⟨c, List.mem_cons_self .., hc⟩
    have hoth := others_eq (PF := PF) (D := D) σ ω ℓ hperm (fun ℓ' hℓ' => by
      rw [List.filter_append, filter_grp_ne_of_some h0 hℓ', List.append_nil,
        List.filter_cons_of_neg (by simp [hc, Ne.symm hℓ'])])
    rw [← hoth, e1, e2, Fn_append]
    simp only [map_mul, Coeff.eval, ha, hm ω]
    rfl
  rw [List.map_congr_left hterm]
  rw [termR_split (c :: rest) coeff σ ω ℓ ⟨c, List.mem_cons_self .., hc⟩]
  have e1 : (c :: rest).filter (fun c => c.label.isNone) =
      rest.filter (fun c => c.label.isNone) := List.filter_cons_of_neg (by simp [hc])
  have e2 : (c :: rest).filter (fun c => decide (c.label = some ℓ)) =
      c :: rest.filter (fun c => decide (c.label = some ℓ)) :=
    List.filter_cons_of_pos (by simp [hc])
  rw [e1, e2]
  have hgl : ∀ p ∈ outs.map (fun o => (a o, fun ω' => R ω' * Fn D σ o.2 ω')), A.Good p.2 := by
    intro p hp
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hp
    have := A.laws.good_mul _ _ hRgood (good_Fn A σ o.2 (hgood' o ho))
    exact this
  have hf : Fn D σ (c :: rest.filter fun c => decide (c.label = some ℓ)) =
      fun ω' => ((outs.map fun o => (a o, fun ω'' => R ω'' * Fn D σ o.2 ω'')).map
        fun p => p.1 * p.2 ω').sum := by
    funext ω'
    simp only [Fn, List.map_cons, List.prod_cons, List.map_map, Function.comp_def]
    rw [hval' ω', ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
    simp only [hR, Fn]
    ring
  rw [hf, op_lincomb A ℓ.1 (σ ℓ.2) _ hgl]
  simp only [List.map_map, Function.comp_def]
  calc _ = (outs.map fun o => (Coeff.eval (D ω).m coeff * U * Oth) *
        (a o * PF.op ℓ.1 (σ ℓ.2) (fun ω' => R ω' * Fn D σ o.2 ω') ω)).sum :=
        congrArg List.sum (List.map_congr_left fun o _ => by ring)
    _ = _ := by
        rw [List.sum_map_mul_left]
        ring

private theorem list_sum_map_sum {α β : Type*} [Fintype β] (l : List α) (f : α → β → ℂ) :
    (l.map fun a => ∑ b, f a b).sum = ∑ b, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

/-- The formal sum obtained by replacing the component with index `i` by the component lists of
`outs`, with their coefficients. -/
private def replT (Γ : Graph k n) (i : ℕ) (outs : List (Coeff × List (Comp (Atom k n)))) :
    TExpansion k n :=
  outs.map fun o => ⟨n, ⟨Γ.comps.eraseIdx i ++ o.2, o.1 * Γ.coeff⟩, id⟩

/-- Replacing the component `c` at index `i` by the lists of `outs`, with the coefficients of
`outs`, preserves the value, when the value of `c` is the corresponding combination, the new
components carry the label of `c`, and the group of that label consists of components of good
kinds. -/
private theorem valR_replace (A : ModelAdm Ω ι PF D) (Γ : Graph k n) (e : Fin k → ι)
    {i : ℕ} {c : Comp (Atom k n)} (hc : Γ.comps[i]? = some c)
    (outs : List (Coeff × List (Comp (Atom k n))))
    (hlab : ∀ o ∈ outs, ∀ c' ∈ o.2, c'.label = c.label)
    (hgood : c.label.all Γ.GoodGroup = true)
    (hgood' : c.label.isSome = true → ∀ o ∈ outs, ∀ c' ∈ o.2, c'.isGoodKind = true)
    (hkeep : ∀ ℓ, c.label = some ℓ → ∀ o ∈ outs,
      o.2 ≠ [] ∨ ∃ c' ∈ Γ.comps.eraseIdx i, c'.label = some ℓ)
    (hval : ∀ (σ : Atom k n → ι) (ω : Ω), Comp.val (D ω) σ c = (outs.map fun o =>
      Coeff.eval (D ω).m o.1 * (o.2.map (Comp.val (D ω) σ)).prod).sum) :
    (replT Γ i outs).forget.valR PF D e = Γ.valR PF D e := by
  obtain ⟨comps, coeff⟩ := Γ
  funext ω
  simp only [replT, TExpansion.forget, Expansion.valR, List.map_map, Function.comp_def,
    Graph.valR]
  rw [list_sum_map_sum outs (fun (o : Coeff × List (Comp (Atom k n))) (s : Fin n → ι) =>
    Graph.termR (⟨comps.eraseIdx i ++ o.2, o.1 * coeff⟩ : Graph k n) PF D (Sum.elim e s) ω)]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  have hperm := List.getElem_cons_eraseIdx_perm hi
  rw [hci] at hperm
  have hmemΓ : ∀ c' ∈ c :: comps.eraseIdx i, c' ∈ comps := fun c' hc' => hperm.mem_iff.1 hc'
  rw [← termR_perm hperm coeff (Sum.elim e s) ω]
  cases hl : c.label with
  | none =>
    exact termR_replace_none _ ω _ c hl coeff outs (fun o ho c' hc' => by rw [hlab o ho c' hc', hl])
      (hval _ ω)
  | some ℓ =>
    rw [hl] at hlab hgood
    refine termR_replace_some A _ ω _ c ℓ hl coeff outs (fun o ho c' hc' => hlab o ho c' hc') ?_
      (fun o ho c' hc' => hgood' (by rw [hl]; rfl) o ho c' hc') (hkeep ℓ hl) (hval _)
    intro c' hc' hc'l
    have h1 := hgood
    simp only [Option.all_some, Graph.GoodGroup, List.all_eq_true] at h1
    have := h1 c' (hmemΓ c' hc')
    simpa [hc'l] using this

end Replace

/-! ## The value identities (4.17), (4.20) -/

section SchurVals

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

private theorem val_mkInv {V : Type*} (d : Data ι) (σ : V → ι) (ch : Charge) (u : V) :
    Comp.val d σ (mkC (.inv ch) u u) = ch.hom ((d.Gm ∅ (σ u) (σ u))⁻¹) := by
  simp [Comp.val, mkC, Charge.apply_eq]

/-- [II, (4.17)] on the entries of the data record. -/
private theorem schur_id (A : ModelAdm Ω ι PF D) (ω : Ω) (ch : Charge) (a b i : ι) :
    ch.hom ((D ω).Gm ∅ a b) = ch.hom ((D ω).Gm {i} a b) +
      ch.hom ((D ω).Gm ∅ a i) * (ch.hom ((D ω).Gm ∅ i b) * ch.hom (((D ω).Gm ∅ i i)⁻¹)) := by
  rw [A.data_G ω, A.data_minor ω i]
  have h := RBM8D.green_eq_greenMinor_add (green (A.H ω) A.z) i a b
  conv_lhs => rw [h]
  simp [Matrix.of_apply, map_add, map_mul, map_inv₀, div_eq_mul_inv, mul_assoc]

end SchurVals

/-- A formal sum with one term `Γ` is value-preserving. -/
private theorem forget_self_valR {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) {k n : ℕ} (Γ : Graph k n) (e : Fin k → ι) :
    (TExpansion.forget [Tracked.self Γ]).valR PF D e = Γ.valR PF D e := by
  funext ω
  simp [TExpansion.forget, Expansion.valR, Tracked.self]

/-! ## The value identities (4.17), (4.20) at weights -/

section SchurWVals

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

/-- The value of a weight or light weight with charge `ch` and atom `a`: `ch (g_{aa})` or
`ch (g_{aa} - m)` for the matrix `g` of its minor. -/
private theorem val_weightLike {V : Type*} (d : Data ι) (σ : V → ι) (c : Comp V) (ch : Charge)
    (hk : c.kind = .weight ch ∨ c.kind = .light ch) :
    Comp.val d σ c = ch.hom (d.Gm (c.minor.map σ).toFinset (σ c.x) (σ c.x) -
      if c.kind = .light ch then d.m else 0) := by
  rcases hk with hk | hk <;> simp [Comp.val, hk, Charge.apply_eq]

private theorem val_mkG {V : Type*} (d : Data ι) (σ : V → ι) (ch : Charge) (u v : V) :
    Comp.val d σ (mkC (.G ch) u v) = ch.hom (d.Gm ∅ (σ u) (σ v)) := by
  simp [Comp.val, mkC, Charge.apply_eq]

/-- [II, (4.17)] at a weight or a light weight on an atom `a`. -/
private theorem schurW_id (A : ModelAdm Ω ι PF D) (ω : Ω) (ch : Charge) (a i : ι) (s : ℂ) :
    ch.hom ((D ω).Gm ∅ a a - s) = ch.hom ((D ω).Gm {i} a a - s) +
      ch.hom ((D ω).Gm ∅ a i) * (ch.hom ((D ω).Gm ∅ i a) * ch.hom (((D ω).Gm ∅ i i)⁻¹)) := by
  have h := schur_id A ω ch a a i
  rw [map_sub, map_sub, h]
  ring

end SchurWVals

/-- [II, (4.17)] at a weight or a light weight on an atom `a ≠ x`: `oSchurWT` preserves the value
of every graph under the model relations. -/
theorem step1_oSchurW_value (k n : ℕ) (x : Atom k n) (i : ℕ) :
    PreservesValue (fun Γ => (oSchurWT x i Γ).forget) modelAdm := by
  intro Ω ι _ _ PF D hA Γ e
  obtain ⟨A⟩ := hA
  rcases hci : Γ.comps[i]? with _ | c
  · have : oSchurWT x i Γ = [Tracked.self Γ] := by simp [oSchurWT, hci]
    simp only [this]
    exact forget_self_valR PF D Γ e
  · by_cases hkW : ∃ ch, c.kind = .weight ch ∨ c.kind = .light ch
    · obtain ⟨ch, hk⟩ := hkW
      by_cases hg : (c.minor.isEmpty && c.x != x && c.label.all Γ.GoodGroup) = true
      · have hE : oSchurWT x i Γ = replT Γ i [(1, [{ c with minor := [x] }]),
            (1, [{ mkC (.G ch) c.x x with label := c.label },
              { mkC (.G ch) x c.x with label := c.label },
              { mkC (.inv ch) x x with label := c.label }])] := by
          rcases hk with hk | hk <;> simp [oSchurWT, hci, hk, hg, replT]
        simp only [hE]
        simp only [Bool.and_eq_true] at hg
        have hmin : c.minor = [] := by simpa using hg.1.1
        refine valR_replace A Γ e hci _ ?_ hg.2 ?_ ?_ ?_
        · intro o ho c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc' <;>
            rcases hc' with rfl | rfl | rfl <;> rfl
        · intro _ o ho c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          · rcases hc' with rfl
            rcases hk with hk | hk <;> simp [Comp.isGoodKind, hk]
          · rcases hc' with rfl | rfl | rfl <;> simp [mkC, Comp.isGoodKind]
        · intro ℓ _ o ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp
        · intro σ ω
          have h1 := val_weightLike (D ω) σ c ch hk
          have h2 := val_weightLike (D ω) σ { c with minor := [x] } ch hk
          rw [h1, hmin]
          simp only [List.map_nil, List.toFinset_nil] at h2 ⊢
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons,
            List.prod_nil, Comp.val_label, val_mkG, val_mkInv, h2, mul_one, add_zero]
          have := schurW_id A ω ch (σ c.x) (σ x)
            (if c.kind = .light ch then (D ω).m else 0)
          simpa [Coeff.eval] using this
      · have : oSchurWT x i Γ = [Tracked.self Γ] := by
          rcases hk with hk | hk <;> simp [oSchurWT, hci, hk] <;> simpa using hg
        simp only [this]
        exact forget_self_valR PF D Γ e
    · have : oSchurWT x i Γ = [Tracked.self Γ] := by
        simp only [oSchurWT, hci]
        cases hk : c.kind <;> simp_all
      simp only [this]
      exact forget_self_valR PF D Γ e

/-- [II, (4.20)] at a weight or a light weight with minor `{x}` on an atom `a ≠ x`:
`oSchurWRevT` preserves the value of every graph under the model relations. -/
theorem step1_oSchurWRev_value (k n : ℕ) (x : Atom k n) (i : ℕ) :
    PreservesValue (fun Γ => (oSchurWRevT x i Γ).forget) modelAdm := by
  intro Ω ι _ _ PF D hA Γ e
  obtain ⟨A⟩ := hA
  rcases hci : Γ.comps[i]? with _ | c
  · have : oSchurWRevT x i Γ = [Tracked.self Γ] := by simp [oSchurWRevT, hci]
    simp only [this]
    exact forget_self_valR PF D Γ e
  · by_cases hkW : ∃ ch, c.kind = .weight ch ∨ c.kind = .light ch
    · obtain ⟨ch, hk⟩ := hkW
      by_cases hg : (decide (c.minor = [x]) && c.x != x && c.label.all Γ.GoodGroup) = true
      · have hE : oSchurWRevT x i Γ = replT Γ i [(1, [{ c with minor := [] }]),
            (-1, [{ mkC (.G ch) c.x x with label := c.label },
              { mkC (.G ch) x c.x with label := c.label },
              { mkC (.inv ch) x x with label := c.label }])] := by
          rcases hk with hk | hk <;> simp [oSchurWRevT, hci, hk, hg, replT]
        simp only [hE]
        simp only [Bool.and_eq_true] at hg
        have hmin : c.minor = [x] := by simpa using hg.1.1
        refine valR_replace A Γ e hci _ ?_ hg.2 ?_ ?_ ?_
        · intro o ho c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc' <;>
            rcases hc' with rfl | rfl | rfl <;> rfl
        · intro _ o ho c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          · rcases hc' with rfl
            rcases hk with hk | hk <;> simp [Comp.isGoodKind, hk]
          · rcases hc' with rfl | rfl | rfl <;> simp [mkC, Comp.isGoodKind]
        · intro ℓ _ o ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp
        · intro σ ω
          have h1 := val_weightLike (D ω) σ c ch hk
          have h2 := val_weightLike (D ω) σ { c with minor := [] } ch hk
          rw [h1, hmin]
          simp only [List.map_nil, List.toFinset_nil] at h2 ⊢
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons,
            List.prod_nil, Comp.val_label, val_mkG, val_mkInv, h2, mul_one, add_zero]
          have hs : ([σ x] : List ι).toFinset = {σ x} := by simp
          rw [hs]
          have := schurW_id A ω ch (σ c.x) (σ x)
            (if c.kind = .light ch then (D ω).m else 0)
          simp only [Coeff.eval, map_neg, map_one]
          linear_combination (-1 : ℂ) * this
      · have : oSchurWRevT x i Γ = [Tracked.self Γ] := by
          rcases hk with hk | hk <;> simp [oSchurWRevT, hci, hk] <;> simpa using hg
        simp only [this]
        exact forget_self_valR PF D Γ e
    · have : oSchurWRevT x i Γ = [Tracked.self Γ] := by
        simp only [oSchurWRevT, hci]
        cases hk : c.kind <;> simp_all
      simp only [this]
      exact forget_self_valR PF D Γ e

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

private theorem termR_append_unl (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω)
    (c : Comp (Atom k n)) (L : List (Comp (Atom k n))) (co : Coeff) (hc : c.label = none) :
    Graph.termR (⟨L ++ [c], co⟩ : Graph k n) PF D σ ω =
      Comp.val (D ω) σ c * Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω := by
  rw [termR_perm (PF := PF) (D := D) (List.perm_append_singleton c L) co σ ω,
    termR_cons_unl PF D σ ω c L co hc]

private theorem termR_neg (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω)
    (L : List (Comp (Atom k n))) (co : Coeff) :
    Graph.termR (⟨L, -co⟩ : Graph k n) PF D σ ω = -Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω := by
  simp only [Graph.termR, Graph.labels, Coeff.eval, map_neg]
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

/-- The partition `1 = 1_{u = v} + 1_{u ≠ v}`: `oSplitT` preserves the value of every graph, for
every data record and every family of conditional expectations. -/
theorem step1_oSplit_value (k n : ℕ) (u v : Atom k n) :
    PreservesValue (fun Γ => (oSplitT u v Γ).forget) anyAdm := by
  intro Ω ι _ _ PF D _ Γ e
  by_cases h : u = v
  · simp only [oSplitT, h, ite_true]
    exact forget_self_valR PF D Γ e
  · funext ω
    simp only [oSplitT, h, ite_false, TExpansion.forget, Expansion.valR, List.map_cons,
      List.map_nil, Tracked.self, List.sum_cons, List.sum_nil, add_zero, Graph.valR]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [termR_append_unl PF D _ ω _ _ _ rfl, termR_append_unl PF D _ ω _ _ _ rfl]
    simp only [mkC, Comp.val]
    by_cases hh : Sum.elim e s u = Sum.elim e s v <;> simp [hh]

/-- The identity `1_{u ≠ v} = 1 - 1_{u = v}`: `oXdotT` preserves the value of every graph, for
every data record and every family of conditional expectations. -/
theorem step1_oXdot_value (k n : ℕ) (i : ℕ) :
    PreservesValue (fun Γ : Graph k n => (oXdotT i Γ).forget) anyAdm := by
  intro Ω ι _ _ PF D _ Γ e
  rcases hci : Γ.comps[i]? with _ | c
  · simp only [oXdotT, hci]
    exact forget_self_valR PF D Γ e
  · by_cases hg : c.kind = .xdot ∧ c.label = none ∧ (Γ.comps.any fun d => d.kind.isSolid &&
        ((d.x == c.x && d.y == c.y) || (d.x == c.y && d.y == c.x))) = false
    · simp only [oXdotT, hci, ite_eq_left hg]
      funext ω
      simp only [TExpansion.forget, Expansion.valR, List.map_cons, List.map_nil, Tracked.self,
        List.sum_cons, List.sum_nil, add_zero, Graph.valR]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [termR_append_unl PF D _ ω _ _ _ rfl, termR_neg,
        termR_eraseIdx_unl PF D _ ω Γ hci hg.2.1]
      simp only [mkC, Comp.val, hg.1]
      by_cases hh : Sum.elim e s c.x = Sum.elim e s c.y <;> simp [hh]
    · simp only [oXdotT, hci, ite_eq_right hg]
      exact forget_self_valR PF D Γ e

/-- Removing a dotted edge whose ends are joined by the other dotted edges preserves the value,
for every data record and every family of conditional expectations, when no dotted edge carries
a label. -/
theorem step1_dropDot_value {k n : ℕ} (Γ : Graph k n) {i : ℕ} {c : Comp (Atom k n)}
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

/-- A graph with a `×`-dotted edge inside a block has value `0`, for every data record and every
family of conditional expectations, when no dotted or `×`-dotted edge carries a label. -/
theorem step1_valR_eq_zero {k n : ℕ} (Γ : Graph k n)
    (hlab : ∀ d ∈ Γ.comps, (d.kind = .dot ∨ d.kind = .xdot) → d.label = none)
    (h : ¬ Γ.XdotApart) :
    ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
      (e : Fin k → ι), Γ.valR PF D e = 0 := by
  intro Ω ι _ _ PF D e
  simp only [Graph.XdotApart, not_forall, not_not] at h
  obtain ⟨c, hc, hk, hb⟩ := h
  funext ω
  simp only [Graph.valR, Pi.zero_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hz : ∀ d ∈ Γ.comps, d.kind = .dot → Sum.elim e s d.x = Sum.elim e s d.y
  · have := sigma_eq_of_reach (Sum.elim e s) hz hb
    exact termR_eq_zero_of_val' PF D _ ω hc (hlab c hc (Or.inr hk)) (by simp [Comp.val, hk, this])
  · push Not at hz
    obtain ⟨d, hd, hdk, hne⟩ := hz
    exact termR_eq_zero_of_val' PF D _ ω hd (hlab d hd (Or.inl hdk)) (by simp [Comp.val, hdk, hne])

/-! ## The value of `absorb` -/

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

/-- The components moved into the label group by `absorb`. -/
private abbrev absP (u : Atom k n) (c : Comp (Atom k n)) : Prop :=
  c.label = none ∧ c.kind.isRandom = true ∧ u ∈ c.minor

private theorem absorb_prod_unl (ℓ : PQ × Atom k n) (d : Data ι) (σ : Atom k n → ι) :
    ∀ L : List (Comp (Atom k n)),
      (((L.map fun c => if absP ℓ.2 c then { c with label := some ℓ } else c).filter
          fun c => c.label.isNone).map (Comp.val d σ)).prod *
        ((L.filter fun c => decide (absP ℓ.2 c)).map (Comp.val d σ)).prod =
      ((L.filter fun c => c.label.isNone).map (Comp.val d σ)).prod
  | [] => by simp
  | c :: L => by
    have ih := absorb_prod_unl ℓ d σ L
    by_cases ha : absP ℓ.2 c
    · have e1 : (if absP ℓ.2 c then { c with label := some ℓ } else c) =
          { c with label := some ℓ } := ite_eq_left ha
      have hn : c.label.isNone = true := by simp [ha.1]
      have d1 : decide (absP ℓ.2 c) = true := decide_eq_true ha
      have d2 : ({ c with label := some ℓ } : Comp (Atom k n)).label.isNone = false := rfl
      simp only [List.map_cons, e1, List.filter_cons, d1, d2, hn, ite_true, Bool.false_eq_true,
        ite_false, List.prod_cons]
      rw [← ih]
      ring
    · have e1 : (if absP ℓ.2 c then { c with label := some ℓ } else c) = c := ite_eq_right ha
      have d1 : decide (absP ℓ.2 c) = false := decide_eq_false ha
      by_cases hn : c.label.isNone = true
      · simp only [List.map_cons, e1, List.filter_cons, d1, hn, ite_true, Bool.false_eq_true,
          ite_false, List.prod_cons]
        rw [← ih]
        ring
      · simp only [List.map_cons, e1, List.filter_cons, d1, hn, Bool.false_eq_true, ite_false]
        exact ih

private theorem absorb_prod_grp (ℓ : PQ × Atom k n) (d : Data ι) (σ : Atom k n → ι) :
    ∀ L : List (Comp (Atom k n)),
      (((L.map fun c => if absP ℓ.2 c then { c with label := some ℓ } else c).filter
          fun c => decide (c.label = some ℓ)).map (Comp.val d σ)).prod =
      ((L.filter fun c => decide (c.label = some ℓ)).map (Comp.val d σ)).prod *
        ((L.filter fun c => decide (absP ℓ.2 c)).map (Comp.val d σ)).prod
  | [] => by simp
  | c :: L => by
    have ih := absorb_prod_grp ℓ d σ L
    by_cases ha : absP ℓ.2 c
    · have e1 : (if absP ℓ.2 c then { c with label := some ℓ } else c) =
          { c with label := some ℓ } := ite_eq_left ha
      have d1 : decide (absP ℓ.2 c) = true := decide_eq_true ha
      have d2 : decide (({ c with label := some ℓ } : Comp (Atom k n)).label = some ℓ) = true :=
        decide_eq_true rfl
      have d3 : decide (c.label = some ℓ) = false := decide_eq_false (by rw [ha.1]; simp)
      simp only [List.map_cons, e1, List.filter_cons, d1, d3, ite_true, Bool.false_eq_true,
        ite_false, List.prod_cons, Comp.val_label, decide_true]
      rw [ih]
      ring
    · have e1 : (if absP ℓ.2 c then { c with label := some ℓ } else c) = c := ite_eq_right ha
      have d1 : decide (absP ℓ.2 c) = false := decide_eq_false ha
      by_cases hl : c.label = some ℓ
      · have d3 : decide (c.label = some ℓ) = true := decide_eq_true hl
        simp only [List.map_cons, e1, List.filter_cons, d1, d3, ite_true, Bool.false_eq_true,
          ite_false, List.prod_cons]
        rw [ih]
        ring
      · have d3 : decide (c.label = some ℓ) = false := decide_eq_false hl
        simp only [List.map_cons, e1, List.filter_cons, d1, d3, Bool.false_eq_true, ite_false]
        exact ih

/-- The conjugate of a function independent of a row is independent of it. -/
private theorem meas_star (A : ModelAdm Ω ι PF D) (u : ι) {F : Ω → ℂ} (hg : A.Good F)
    (hm : A.Meas u F) : A.Meas u fun ω => star (F ω) := by
  have h1 : PF.P u (fun ω => star (F ω)) = fun ω => star (F ω) := by
    rw [A.P_star u F hg, A.laws.of_meas u F hg hm]
  have h2 := A.laws.meas_P u (fun ω => star (F ω)) (A.good_star F hg)
  rwa [h1] at h2

private theorem meas_charge (A : ModelAdm Ω ι PF D) (u : ι) (ch : Charge) {F : Ω → ℂ}
    (hg : A.Good F) (hm : A.Meas u F) : A.Meas u fun ω => ch.apply (F ω) := by
  cases ch
  · exact hm
  · exact meas_star A u hg hm

/-- A solid edge, a weight or a light weight with minor `{u}` does not depend on the row of `u`. -/
private theorem meas_val (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) (u : Atom k n)
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

private theorem meas_Fn (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) (u : Atom k n) :
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

end AbsorbVals

/-- Moving the factors without label whose minor contains `u` into the label group `ℓ = (P or Q,
u)` preserves the value under the model relations, when every label is `ℓ`, the group consists of
components of good kinds, and the moved factors are solid edges, weights or light weights with
minor `{u}` (a factor independent of the row of `u` commutes with `P_u` and `Q_u`). -/
theorem step1_absorb_value {k n : ℕ} (Γ : Graph k n) (ℓ : PQ × Atom k n)
    (hl : ∀ c ∈ Γ.comps, c.label = none ∨ c.label = some ℓ)
    (hex : ∃ c ∈ Γ.comps, c.label = some ℓ)
    (hgood : ∀ c ∈ Γ.comps, c.label = some ℓ → c.isGoodKind = true)
    (habs : ∀ c ∈ Γ.comps, c.label = none → c.kind.isRandom = true → ℓ.2 ∈ c.minor →
      c.minor = [ℓ.2] ∧ ∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) :
    ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
      modelAdm Ω ι PF D → ∀ e : Fin k → ι, (Γ.absorb ℓ).valR PF D e = Γ.valR PF D e := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  obtain ⟨cs, co⟩ := Γ
  have hφ : (Graph.absorb ℓ ⟨cs, co⟩).comps =
      cs.map fun c => if absP ℓ.2 c then { c with label := some ℓ } else c := rfl
  have hl' : ∀ c ∈ (Graph.absorb ℓ ⟨cs, co⟩).comps, c.label = none ∨ c.label = some ℓ := by
    intro c hc
    rw [hφ, List.mem_map] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    by_cases ha : absP ℓ.2 c₀
    · rw [ite_eq_left ha]
      exact Or.inr rfl
    · rw [ite_eq_right ha]
      exact hl c₀ hc₀
  have hex' : ∃ c ∈ (Graph.absorb ℓ ⟨cs, co⟩).comps, c.label = some ℓ := by
    obtain ⟨c₀, hc₀, hl₀⟩ := hex
    refine ⟨c₀, ?_, hl₀⟩
    rw [hφ, List.mem_map]
    refine ⟨c₀, hc₀, ?_⟩
    have : ¬ absP ℓ.2 c₀ := fun ha => by rw [ha.1] at hl₀; cases hl₀
    rw [ite_eq_right this]
  have hlab1 : (⟨cs, co⟩ : Graph k n).labels = [ℓ] := labels_eq_single cs co ℓ hl hex
  have hlab2 : (Graph.absorb ℓ ⟨cs, co⟩).labels = [ℓ] := labels_eq_single _ co ℓ hl' hex'
  funext ω
  simp only [Graph.valR]
  refine Finset.sum_congr rfl fun s _ => ?_
  set σ := Sum.elim e s
  have hga : A.Good (Fn D σ (cs.filter fun c => decide (absP ℓ.2 c))) := by
    apply good_Fn A σ
    intro c hc
    have hc' := List.mem_filter.1 hc
    have ha : absP ℓ.2 c := by simpa using hc'.2
    obtain ⟨-, ch, hk⟩ := habs c hc'.1 ha.1 ha.2.1 ha.2.2
    rcases hk with hk | hk | hk <;> simp [Comp.isGoodKind, hk]
  have hgg : A.Good (Fn D σ (cs.filter fun c => decide (c.label = some ℓ))) := by
    apply good_Fn A σ
    intro c hc
    have hc' := List.mem_filter.1 hc
    exact hgood c hc'.1 (by simpa using hc'.2)
  have hma : A.Meas (σ ℓ.2) (Fn D σ (cs.filter fun c => decide (absP ℓ.2 c))) := by
    apply meas_Fn A σ ℓ.2
    intro c hc
    have hc' := List.mem_filter.1 hc
    have ha : absP ℓ.2 c := by simpa using hc'.2
    exact habs c hc'.1 ha.1 ha.2.1 ha.2.2
  have hop : PF.op ℓ.1 (σ ℓ.2) (Fn D σ (cs.filter fun c => decide (c.label = some ℓ)) *
      Fn D σ (cs.filter fun c => decide (absP ℓ.2 c))) ω =
      Fn D σ (cs.filter fun c => decide (absP ℓ.2 c)) ω *
        PF.op ℓ.1 (σ ℓ.2) (Fn D σ (cs.filter fun c => decide (c.label = some ℓ))) ω := by
    rw [mul_comm (Fn D σ _) (Fn D σ _)]
    rcases ℓ with ⟨pq, u⟩
    cases pq
    · simp only [PFamily.op]
      rw [A.laws.mul_left _ _ _ hga hgg hma]
      rfl
    · simp only [PFamily.op]
      rw [A.laws.mul_left _ _ _ hga hgg hma]
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring
  have hgrp : (fun ω' => (((Graph.absorb ℓ ⟨cs, co⟩).comps.filter
      fun c => decide (c.label = some ℓ)).map (Comp.val (D ω') σ)).prod) =
      Fn D σ (cs.filter fun c => decide (c.label = some ℓ)) *
        Fn D σ (cs.filter fun c => decide (absP ℓ.2 c)) := by
    funext ω'
    rw [hφ, absorb_prod_grp ℓ (D ω') σ cs]
    rfl
  have hunl := absorb_prod_unl ℓ (D ω) σ cs
  rw [← hφ] at hunl
  simp only [Graph.termR, hlab1, hlab2, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [hgrp, hop, ← hunl]
  have hco : (Graph.absorb ℓ ⟨cs, co⟩).coeff = co := rfl
  rw [hco]
  have hF : ∀ cs' : List (Comp (Atom k n)), Fn D σ cs' ω = (cs'.map (Comp.val (D ω) σ)).prod :=
    fun _ => rfl
  have hF2 : Fn D σ (cs.filter fun c => decide (c.label = some ℓ)) = fun ω' =>
      ((cs.filter fun c => decide (c.label = some ℓ)).map (Comp.val (D ω') σ)).prod := rfl
  rw [hF, hF2]
  ring

section Bind

variable {k n : ℕ}

end Bind

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

/-! ## The invariants of the construction -/

section Inv

variable {k n : ℕ}

/-- `u` and `v` are joined by a `×`-dotted component. -/
def Step1HasX (L : List (Comp (Atom k n))) (u v : Atom k n) : Prop :=
  ∃ d ∈ L, d.kind = .xdot ∧ (d.x = u ∧ d.y = v ∨ d.x = v ∧ d.y = u)

/-- `u` and `v` are joined by a solid component. -/
def Step1HasS (L : List (Comp (Atom k n))) (u v : Atom k n) : Prop :=
  ∃ d ∈ L, d.kind.isSolid = true ∧ (d.x = u ∧ d.y = v ∨ d.x = v ∧ d.y = u)

/-- The weights `W_D`. -/
def Kind.isWDB : Kind → Bool
  | .wD _ _ => true
  | _ => false

/-- The weights `(G_{xx})⁻¹`. -/
def Kind.step1_isInvB : Kind → Bool
  | .inv _ => true
  | _ => false

/-- The number of `W_D` components. -/
def step1_nWD (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => c.kind.isWDB).length

/-- The random components without label and minor away from `X`: the factors of `Γ₀` not yet
written by [II, (4.17)]. -/
def pendB (X : Atom k n) (c : Comp (Atom k n)) : Bool :=
  c.label.isNone && c.kind.isRandom && c.minor.isEmpty && c.x != X && c.y != X

/-- The number of components with a minor. -/
def nMin (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => !c.minor.isEmpty).length

/-- The number of weights `(G_{xx})⁻¹`. -/
def nInv (L : List (Comp (Atom k n))) : ℕ := (L.filter fun c => c.kind.step1_isInvB).length

/-- The number of pending components. -/
def nPend (X : Atom k n) (L : List (Comp (Atom k n))) : ℕ := (L.filter (pendB X)).length

/-- The size potential: it never grows along the construction and bounds the number of
components of every output. -/
def step1_sizeΦ (D' : ℕ) (X : Atom k n) (L : List (Comp (Atom k n))) : ℕ :=
  L.length + (D' + 3) * (nPend X L + nMin L) + (D' + 1) * nInv L

/-- The clauses kept by every intermediate graph `T` of the construction for the input `Γ` at the
internal atom `X`, with Taylor degree `D'` and size bound `S`. -/
structure Step1Base (D' S : ℕ) (X : Atom k n) (Γ T : Graph k n) : Prop where
  chain : Relation.ReflTransGen QElemStep ⟨n, Γ⟩ ⟨n, T⟩
  conn : T.ConnNoX
  internal : ∀ a b : Fin n, T.wavedThetaGraph.Reachable (.inr a) (.inr b)
  solid : ∀ c ∈ T.comps, c.kind.isSolid = true → c.x ≠ c.y ∧ Step1HasX T.comps c.x c.y
  xapart : T.XdotApart
  excess : step1_eL T.comps = step1_eL Γ.comps
  nonred : NonRedInt T.comps
  dc : Γ.DoublyConnected → T.Step1DCS .plus
  wf : ∀ c ∈ T.comps, c.WF
  noloop : ∀ c ∈ T.comps, c.kind = .dot → c.x ≠ c.y
  lab : ∀ c ∈ T.comps, c.label = none ∨ c.label = some (.Q, X)
  labex : ∃ c ∈ T.comps, c.label = some (.Q, X) ∧ c.minor = [] ∧ c.kind.step1_isInvB = false
  good : ∀ c ∈ T.comps, c.label.isSome = true → c.isGoodKind = true
  minor : ∀ c ∈ T.comps, c.minor = [] ∨ (c.minor = [X] ∧
    (∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) ∧ c.x ≠ X ∧ c.y ≠ X ∧
      Step1HasX T.comps c.x X ∧ Step1HasX T.comps c.y X)
  inv : ∀ c ∈ T.comps, c.kind.step1_isInvB = true → c.x = X ∧ c.y = X ∧ c.minor = []
  wd : ∀ c ∈ T.comps, c.kind.isWDB = true → c.minor = []
  ord : Γ.ord + (D' + 1) * (step1_nWD T.comps : ℤ) ≤ T.ord
  xright : X.isRight = true
  size : step1_sizeΦ D' X T.comps ≤ S

/-- Every random component carries the label `Q_X`: the outputs are `Q`-graphs. -/
def ClsQ (X : Atom k n) (T : Graph k n) : Prop :=
  ∀ c ∈ T.comps, c.kind.isRandom = true → c.label = some (.Q, X)

/-- An atom of a weight or edge of `Γ₀` is identified with `X` or joined to `X` by a solid edge
without label, and the scaling order is strictly higher. -/
def ClsW (D' : ℕ) (X : Atom k n) (Γ T : Graph k n) : Prop :=
  (Tracked.self T).QWitness X Γ ∧ Γ.ord + 1 + (D' + 1) * (step1_nWD T.comps : ℤ) ≤ T.ord

end Inv

/-! ## Connectivity transfers -/

section ConnTransfer

variable {k n : ℕ}

private theorem edgeNoX_reach_of_comp {T : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ T.comps)
    (hk : c.kind ≠ .xdot) : T.edgeGraphNoX.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

private theorem edgeNoX_reach_of_dg {T : Graph k n} {a b : Atom k n}
    (h : (step1_dg T.comps).Reachable a b) : T.edgeGraphNoX.Reachable a b := by
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

private theorem molReach_of_dg {T : Graph k n} {a b : Atom k n}
    (h : (step1_dg T.comps).Reachable a b) : T.molGraph.Reachable a b := by
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

/-! ## Removing redundant dotted edges -/

section Drop

variable {k m : ℕ}

/-- Removing a dotted edge whose ends are joined by the other dotted edges. -/
theorem step1_drop_one (g : Graph k m) {i : ℕ} {c : Comp (Atom k m)} (hc : g.comps[i]? = some c)
    (hk : c.kind = .dot) (hr : (step1_dg (g.comps.eraseIdx i)).Reachable c.x c.y) :
    let g₁ : Graph k m := ⟨g.comps.eraseIdx i, g.coeff⟩
    QElemStep ⟨m, g⟩ ⟨m, g₁⟩ ∧ step1_eL g₁.comps + 1 = step1_eL g.comps ∧ g₁.ord + 2 = g.ord ∧
      (∀ d ∈ g.comps, d.kind ≠ .dot → d ∈ g₁.comps) ∧
      (∀ u v, g₁.SameBlock u v ↔ g.SameBlock u v) ∧
      (g.Step1DCS .plus → g₁.Step1DCS .plus) ∧ (g.ConnNoX → g₁.ConnNoX) ∧
      g₁.wavedThetaGraph = g.wavedThetaGraph := by
  intro g₁
  have hmem : ∀ d ∈ g.comps, d.kind ≠ .dot → d ∈ g₁.comps := by
    intro d hd hdk
    exact mem_eraseIdx_of_ne hc hd (fun h => hdk (h ▸ hk))
  have hr₁ : (step1_dg g₁.comps).Reachable c.x c.y := hr
  obtain ⟨he, hb⟩ := eL_eraseIdx_red hc hk hr
  refine ⟨QElemStep.dropDot i g c hc hk hr, he, ?_, hmem, hb, ?_, ?_, ?_⟩
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
        simp [Kind.isDiffusive, Kind.blueC] at this
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

section Final

variable {k n : ℕ}

end Final

/-! ## Transfer of the invariants -/

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
        exact dg_reach_of_mem (List.mem_cons_self ..) hek
      have hm : ∀ a b, (step1_dg (L.eraseIdx j)).Reachable a b → (step1_dg L).Reachable a b :=
        fun a b => dg_reach_mono fun d hd _ => List.mem_of_mem_eraseIdx hd
      exact ((hm _ _ h1).symm.trans hee).trans (hm _ _ h2).symm
    · apply hr
      have hee : (step1_dg L).Reachable L[j].x L[j].y := by
        rw [dg_perm hL]
        exact dg_reach_of_mem (List.mem_cons_self ..) hek
      have hm : ∀ a b, (step1_dg (L.eraseIdx j)).Reachable a b → (step1_dg L).Reachable a b :=
        fun a b => dg_reach_mono fun d hd _ => List.mem_of_mem_eraseIdx hd
      exact ((hm _ _ h2).trans hee.symm).trans (hm _ _ h1)

end Transfer

/-! ## Removing the `×`-dotted edges without solid edge -/

section Clean

variable {k n : ℕ}

/-- Some solid component joins `u` and `v`. -/
def solidJoinB (L : List (Comp (Atom k n))) (u v : Atom k n) : Bool :=
  L.any fun d => d.kind.isSolid && ((d.x == u && d.y == v) || (d.x == v && d.y == u))

/-- A `×`-dotted component whose ends are joined by no solid component. -/
def badB (L : List (Comp (Atom k n))) (c : Comp (Atom k n)) : Bool :=
  decide (c.kind = .xdot) && !solidJoinB L c.x c.y

/-- The number of `×`-dotted components whose ends are joined by no solid component. -/
def nBad (L : List (Comp (Atom k n))) : ℕ := (L.filter (badB L)).length

private theorem nonRedInt_perm {L L' : List (Comp (Atom k n))} (h : NonRedInt L) (hp : L.Perm L') :
    NonRedInt L' := fun e M hM => h e M (hp.trans hM)

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

end CleanSteps

/-! ## The phase of the `×`-dotted edges without solid edge -/

section CleanPhase

variable {k n : ℕ}

theorem cls_transfer {D' : ℕ} {X : Atom k n} {Γ T T' : Graph k n}
    (hcls : ClsQ X T ∨ ClsW D' X Γ T)
    (hrand : ∀ d ∈ T'.comps, d.kind.isRandom = true → d ∈ T.comps)
    (hsolid : ∀ d ∈ T.comps, d.kind.isSolid = true → d ∈ T'.comps)
    (hsb : ∀ u v, T.SameBlock u v → T'.SameBlock u v)
    (hord : T.ord ≤ T'.ord) (hnw : step1_nWD T'.comps = step1_nWD T.comps) :
    ClsQ X T' ∨ ClsW D' X Γ T' := by
  rcases hcls with hQ | ⟨⟨c, hc, hcl, hcr, u, hu, hj⟩, ho⟩
  · exact Or.inl fun d hd hr => hQ d (hrand d hd hr) hr
  · refine Or.inr ⟨⟨c, hc, hcl, hcr, u, hu, ?_⟩, ?_⟩
    · rcases hj with hb | ⟨e, he, hes, hel, hexy⟩
      · exact Or.inl (hsb _ _ hb)
      · exact Or.inr ⟨e, hsolid e he hes, hes, hel, hexy⟩
    · rw [hnw]
      linarith

end CleanPhase

/-! ## Replacing a random component -/

section ReplaceStep

variable {k n : ℕ}

private theorem Kind.random_facts {κ : Kind} (h : κ.isRandom = true) :
    κ.joinsMol = false ∧ κ.isDiffusive = false ∧ κ ≠ .ghost ∧ κ ≠ .dot ∧ κ ≠ .xdot ∧
      (κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true → False) := by
  cases κ <;> simp_all [Kind.isRandom, Kind.joinsMol, Kind.isDiffusive]

/-- The clauses `Base` pass to the graph in which the random component with index `i` is replaced
by the random components `new`. -/
theorem base_replace {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    {i : ℕ} {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n)))
    (co : Coeff) (hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i ++ new, co⟩⟩)
    (hck : c.kind.isRandom = true)
    (hnr : ∀ d ∈ new, d.kind.isRandom = true)
    (hconn : (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).edgeGraphNoX.Reachable c.x c.y)
    (hsol : ∀ d ∈ new, d.kind.isSolid = true → d.x ≠ d.y ∧ Step1HasX T.comps d.x d.y)
    (hblue : c.kind = .G .plus → c.x.isRight = true → c.y.isRight = true →
      (∃ d ∈ new, d.kind = .G .plus ∧ d.x = c.x ∧ d.y = c.y) ∨
      (∃ d₁ ∈ new, ∃ d₂ ∈ new, d₁.kind = .G .plus ∧ d₂.kind = .G .plus ∧ d₁.x = c.x ∧
        d₁.y = X ∧ d₂.x = X ∧ d₂.y = c.y))
    (hwf : ∀ d ∈ new, d.WF)
    (hlab : ∀ d ∈ new, d.label = none ∨ d.label = some (.Q, X))
    (hlabex : c.label = none ∨ c.minor ≠ [] ∨ c.kind.step1_isInvB = true)
    (hgood : ∀ d ∈ new, d.label.isSome = true → d.isGoodKind = true)
    (hminor : ∀ d ∈ new, d.minor = [] ∨ (d.minor = [X] ∧
      (∃ ch, d.kind = .G ch ∨ d.kind = .weight ch ∨ d.kind = .light ch) ∧ d.x ≠ X ∧ d.y ≠ X ∧
        Step1HasX T.comps d.x X ∧ Step1HasX T.comps d.y X))
    (hinv : ∀ d ∈ new, d.kind.step1_isInvB = true → d.x = X ∧ d.y = X ∧ d.minor = [])
    (hwd : ∀ d ∈ new, d.kind.isWDB = true → d.minor = [])
    (hord : Γ.ord + (D' + 1) * (step1_nWD (T.comps.eraseIdx i ++ new) : ℤ) ≤
      (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord)
    (hsize : step1_sizeΦ D' X (T.comps.eraseIdx i ++ new) ≤ S) :
    Step1Base D' S X Γ ⟨T.comps.eraseIdx i ++ new, co⟩ := by
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
    change (step1_dg g.comps).Reachable u v ↔ (step1_dg T.comps).Reachable u v
    rw [hdg]
  have hX : ∀ u v, Step1HasX T.comps u v → Step1HasX g.comps u v := by
    intro u v ⟨d, hd, hk, hxy⟩
    exact ⟨d, hin d hd (fun h => hcnd.2 (h ▸ hk)), hk, hxy⟩
  have hX' : ∀ u v, Step1HasX g.comps u v → Step1HasX T.comps u v := by
    intro u v ⟨d, hd, hk, hxy⟩
    rcases hfx d hd with h | h
    · exact ⟨d, h, hk, hxy⟩
    · exact absurd hk (hndot d h).2
  refine ⟨hB.chain.tail hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hord,
    hB.xright, hsize⟩
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
      · have r1 : (g.netT (L₀ ++ new.map fun d =>
            (d, if d.kind = .G .plus then some true else none)) true).Reachable a x₀ := by
          refine Graph.netT_reach_of_mem _ _ _ (p := (d₁, some true)) ?_ rfl (by rw [h1x, hx])
            (by rw [h1y, hx₀])
          exact List.mem_append_right _ (List.mem_map.2 ⟨d₁, hd₁, by simp [hk₁]⟩)
        have r2 : (g.netT (L₀ ++ new.map fun d =>
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
  · obtain ⟨w, hw, hwl, hwm, hwi⟩ := hB.labex
    refine ⟨w, hin w hw ?_, hwl, hwm, hwi⟩
    rintro rfl
    rcases hlabex with h | h | h
    · rw [h] at hwl; cases hwl
    · exact h hwm
    · rw [h] at hwi; cases hwi
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

/-- The class of an output passes to the graph in which a component is replaced. -/
theorem cls_replace {D' : ℕ} {X : Atom k n} {Γ T T' : Graph k n}
    (hcls : ClsQ X T ∨ ClsW D' X Γ T) (hQ : ClsQ X T → ClsQ X T')
    (hsolid : ∀ d ∈ T.comps, d.kind.isSolid = true → d.label = none → (d.x = X ∨ d.y = X) →
      d ∈ T'.comps)
    (hsb : ∀ u v, T.SameBlock u v → T'.SameBlock u v)
    (hord : T.ord - (D' + 1) * (step1_nWD T.comps : ℤ) ≤ T'.ord - (D' + 1) * (step1_nWD T'.comps : ℤ)) :
    ClsQ X T' ∨ ClsW D' X Γ T' := by
  rcases hcls with hq | ⟨⟨c, hc, hcl, hcr, u, hu, hj⟩, ho⟩
  · exact Or.inl (hQ hq)
  · refine Or.inr ⟨⟨c, hc, hcl, hcr, u, hu, ?_⟩, ?_⟩
    · rcases hj with hb | ⟨e, he, hes, hel, hexy⟩
      · exact Or.inl (hsb _ _ hb)
      · refine Or.inr ⟨e, hsolid e he hes hel ?_, hes, hel, hexy⟩
        rcases hexy with ⟨-, h⟩ | ⟨h, -⟩
        · exact Or.inr h
        · exact Or.inl h
    · linarith

end ReplaceStep

section TaylorPhase

variable {k n : ℕ}

end TaylorPhase

section RevPhase

variable {k n : ℕ}

end RevPhase

section RevPhase2

variable {k n : ℕ}

end RevPhase2

/-! ## The phase of [II, (4.17)] -/

section SchurPhase

variable {k n : ℕ}

/-- The components of `Γ₀` not yet written by [II, (4.17)] are factors of `Γ₀` whose atoms are
`×`-dotted to `X`. -/
def PendInv (X : Atom k n) (Γ T : Graph k n) : Prop :=
  ∀ c ∈ T.comps, pendB X c = true → c ∈ Γ.comps ∧ Step1HasX T.comps c.x X ∧ Step1HasX T.comps c.y X

/-- Every random component without label is pending or has the minor `{X}`. -/
def AllPend (X : Atom k n) (T : Graph k n) : Prop :=
  ∀ c ∈ T.comps, c.label = none → c.kind.isRandom = true → pendB X c = true ∨ c.minor = [X]

end SchurPhase

section SchurPhase2

variable {k n : ℕ}

/-- The map of `absorb` on components. -/
private theorem absorb_comps (X : Atom k n) (T : Graph k n) :
    (T.absorb (.Q, X)).comps = T.comps.map fun c =>
      if absP X c then { c with label := some (.Q, X) } else c := rfl

private theorem absorb_dots (X : Atom k n) :
    ∀ L : List (Comp (Atom k n)), (L.map fun c =>
      if absP X c then { c with label := some (.Q, X) } else c).filter
        (fun c => decide (c.kind = .dot)) = L.filter fun c => decide (c.kind = .dot)
  | [] => rfl
  | c :: L => by
    have ih := absorb_dots X L
    by_cases ha : absP X c
    · have hnd : c.kind ≠ .dot := fun h => by
        have := ha.2.1
        rw [h] at this
        simp [Kind.isRandom] at this
      rw [List.map_cons, ite_eq_left ha, List.filter_cons_of_neg (by simpa using hnd),
        List.filter_cons_of_neg (by simpa using hnd), ih]
    · rw [List.map_cons, ite_eq_right ha, List.filter_cons, List.filter_cons, ih]

/-- The factors with minor `{X}` moved into the label group: the clauses `Base` are kept, the
output graphs are `Q`-graphs, and the value is kept. -/
theorem absorb_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    (hnp : nPend X T.comps = 0) (hA : AllPend X T) :
    Step1Base D' S X Γ (T.absorb (.Q, X)) ∧ ClsQ X (T.absorb (.Q, X)) ∧
      TExpansion.ValueEq [Tracked.self (T.absorb (.Q, X))] T modelAdm := by
  set φ : Comp (Atom k n) → Comp (Atom k n) := fun c =>
    if absP X c then { c with label := some (.Q, X) } else c with hφ
  have hcomps : (T.absorb (.Q, X)).comps = T.comps.map φ := absorb_comps X T
  have hφa : ∀ c, absP X c → φ c = { c with label := some (.Q, X) } := fun c ha => ite_eq_left ha
  have hφfix : ∀ c, ¬ absP X c → φ c = c := fun c ha => ite_eq_right ha
  have hφk : ∀ c, (φ c).kind = c.kind ∧ (φ c).x = c.x ∧ (φ c).y = c.y ∧ (φ c).minor = c.minor := by
    intro c
    by_cases ha : absP X c
    · rw [hφa c ha]; exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [hφfix c ha]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hmem : ∀ c ∈ T.comps, φ c ∈ (T.absorb (.Q, X)).comps := fun c hc => by
    rw [hcomps]; exact List.mem_map_of_mem hc
  have hmem' : ∀ d ∈ (T.absorb (.Q, X)).comps, ∃ c ∈ T.comps, d = φ c := by
    intro d hd
    rw [hcomps, List.mem_map] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    exact ⟨c, hc, rfl⟩
  have hnotpend : ∀ c ∈ T.comps, pendB X c = false := by
    intro c hc
    by_contra h
    have : c ∈ T.comps.filter (pendB X) := List.mem_filter.2 ⟨hc, by simpa using h⟩
    have := List.length_pos_of_mem this
    unfold nPend at hnp
    omega
  have hnr : ∀ c, c.kind.isRandom = false → φ c = c := fun c h => hφfix c (fun ha => by
    rw [ha.2.1] at h; cases h)
  have hdots : ((T.absorb (.Q, X)).comps.filter fun c => decide (c.kind = .dot)) =
      T.comps.filter fun c => decide (c.kind = .dot) := by
    rw [hcomps]
    exact absorb_dots X T.comps
  obtain ⟨hdg, heL⟩ := dg_eL_of_filter_perm (List.Perm.of_eq hdots)
  have hX : ∀ u v, Step1HasX T.comps u v → Step1HasX (T.absorb (.Q, X)).comps u v := by
    intro u v ⟨d, hd, hk, hxy⟩
    refine ⟨d, ?_, hk, hxy⟩
    rw [← hnr d (by rw [hk]; rfl)]
    exact hmem d hd
  have hX' : ∀ u v, Step1HasX (T.absorb (.Q, X)).comps u v → Step1HasX T.comps u v := by
    intro u v ⟨d, hd, hk, hxy⟩
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    obtain ⟨h1, h2, h3, -⟩ := hφk c
    rw [h1] at hk
    rw [h2, h3] at hxy
    exact ⟨c, hc, hk, hxy⟩
  have habsK : ∀ c ∈ T.comps, absP X c → c.minor = [X] ∧
      ∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch := by
    intro c hc ha
    rcases hB.minor c hc with h | ⟨h1, h2, -⟩
    · have := ha.2.2
      rw [h] at this
      simp at this
    · exact ⟨h1, h2⟩
  have hℓ : ∃ c ∈ T.comps, c.label = some (.Q, X) := by
    obtain ⟨w, hw, hwl, -⟩ := hB.labex
    exact ⟨w, hw, hwl⟩
  have hstep : QElemStep ⟨n, T⟩ ⟨n, T.absorb (.Q, X)⟩ := QElemStep.absorb (.Q, X) T hℓ hB.lab
  refine ⟨⟨hB.chain.tail hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hB.xright, ?_⟩, ?_, ?_⟩
  · refine connNoX_transfer hB.conn fun c hc hck => ?_
    have := edgeNoX_reach_of_comp (hmem c hc) (by rw [(hφk c).1]; exact hck)
    rwa [(hφk c).2.1, (hφk c).2.2.1] at this
  · refine internal_transfer hB.internal fun c hc hck => ?_
    rw [← hnr c ?_]
    · exact hmem c hc
    · cases hr : c.kind.isRandom
      · rfl
      · exact absurd hck (Kind.random_facts hr).2.2.2.2.2
  · intro d hd hds
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    obtain ⟨h1, h2, h3, -⟩ := hφk c
    rw [h1] at hds
    rw [h2, h3]
    obtain ⟨hne, hx⟩ := hB.solid c hc hds
    exact ⟨hne, hX _ _ hx⟩
  · intro d hd hdk hb
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    obtain ⟨h1, h2, h3, -⟩ := hφk c
    rw [h1] at hdk
    rw [h2, h3] at hb
    apply hB.xapart c hc hdk
    change (step1_dg T.comps).Reachable c.x c.y
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
      rw [(hφk q.1).1]
      exact hL.black q hq hpt
    · intro p hp hpt
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      rw [(hφk q.1).1]
      exact hL.blue q hq hpt
    · intro c hc hck
      have := Graph.molReach_of_comp (hmem c hc) (by rw [(hφk c).1]; exact hck)
      rwa [(hφk c).2.1, (hφk c).2.2.1] at this
    · intro t p hp hpt a b hx hy
      refine Graph.netT_reach_of_mem _ _ _ (p := (φ p.1, p.2))
        (List.mem_map_of_mem (f := fun p : TC k n => (φ p.1, p.2)) hp) hpt ?_ ?_
      · rw [(hφk p.1).2.1, hx]
      · rw [(hφk p.1).2.2.1, hy]
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    by_cases ha : absP X c
    · rw [hφa c ha]
      exact ⟨(hB.wf c hc).1, fun _ => ha.2.1⟩
    · rw [hφfix c ha]
      exact hB.wf c hc
  · intro d hd hdk
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    rw [(hφk c).1] at hdk
    rw [(hφk c).2.1, (hφk c).2.2.1]
    exact hB.noloop c hc hdk
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    by_cases ha : absP X c
    · rw [hφa c ha]
      exact Or.inr rfl
    · rw [hφfix c ha]
      exact hB.lab c hc
  · obtain ⟨w, hw, hwl, hwm, hwi⟩ := hB.labex
    refine ⟨w, ?_, hwl, hwm, hwi⟩
    rw [← hφfix w (fun ha => by rw [ha.1] at hwl; cases hwl)]
    exact hmem w hw
  · intro d hd hdl
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    by_cases ha : absP X c
    · obtain ⟨-, ch, hk⟩ := habsK c hc ha
      rw [hφa c ha]
      rcases hk with hk | hk | hk <;> simp [Comp.isGoodKind, hk]
    · rw [hφfix c ha] at hdl ⊢
      exact hB.good c hc hdl
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    obtain ⟨h1, h2, h3, h4⟩ := hφk c
    rw [h1, h2, h3, h4]
    rcases hB.minor c hc with h | ⟨h5, h6, h7, h8, h9, h10⟩
    · exact Or.inl h
    · exact Or.inr ⟨h5, h6, h7, h8, hX _ _ h9, hX _ _ h10⟩
  · intro d hd hdi
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    obtain ⟨h1, h2, h3, h4⟩ := hφk c
    rw [h1] at hdi
    rw [h2, h3, h4]
    exact hB.inv c hc hdi
  · intro d hd hdi
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    obtain ⟨h1, -, -, h4⟩ := hφk c
    rw [h1] at hdi
    rw [h4]
    exact hB.wd c hc hdi
  · have hnw : step1_nWD (T.absorb (.Q, X)).comps = step1_nWD T.comps := by
      unfold step1_nWD
      rw [hcomps, List.filter_map, List.length_map]
      congr 1
      exact List.filter_congr fun c _ => by rw [Function.comp_apply, (hφk c).1]
    have hord : (T.absorb (.Q, X)).ord = T.ord := by
      simp only [Graph.ord, hcomps, List.map_map]
      congr 2
      exact List.map_congr_left fun c _ => by rw [Function.comp_apply, (hφk c).1]
    rw [hnw, hord]
    exact hB.ord
  · refine le_trans (le_of_eq ?_) hB.size
    unfold step1_sizeΦ nPend nMin nInv
    rw [hcomps, List.filter_map, List.filter_map, List.filter_map, List.length_map,
      List.length_map, List.length_map, List.length_map]
    have e1 : (T.comps.filter (pendB X ∘ φ)) = T.comps.filter (pendB X) := by
      refine List.filter_congr fun c hc => ?_
      rw [Function.comp_apply, hnotpend c hc]
      by_cases ha : absP X c
      · rw [hφa c ha]
        have : X ∈ c.minor := ha.2.2
        simp [pendB]
      · rw [hφfix c ha, hnotpend c hc]
    have e2 : (T.comps.filter ((fun c => !c.minor.isEmpty) ∘ φ)) =
        T.comps.filter fun c => !c.minor.isEmpty :=
      List.filter_congr fun c _ => by rw [Function.comp_apply, (hφk c).2.2.2]
    have e3 : (T.comps.filter ((fun c => c.kind.step1_isInvB) ∘ φ)) =
        T.comps.filter fun c => c.kind.step1_isInvB :=
      List.filter_congr fun c _ => by rw [Function.comp_apply, (hφk c).1]
    rw [e1, e2, e3]
  · intro d hd hdr
    obtain ⟨c, hc, rfl⟩ := hmem' d hd
    rw [(hφk c).1] at hdr
    by_cases ha : absP X c
    · rw [hφa c ha]
    · rw [hφfix c ha]
      rcases hB.lab c hc with hl | hl
      · rcases hA c hc hl hdr with hp | hmX
        · rw [hnotpend c hc] at hp
          cases hp
        · exact absurd ⟨hl, hdr, by rw [hmX]; simp⟩ ha
      · exact hl
  · intro Ω ι _ _ PF D₀ hAd e
    have := step1_absorb_value T (.Q, X) hB.lab hℓ
      (fun c hc hcl => hB.good c hc (by rw [hcl]; rfl))
      (fun c hc hl hr hx => habsK c hc ⟨hl, hr, hx⟩) Ω ι PF D₀ hAd e
    rw [← this]
    funext ω
    simp [TExpansion.forget, Expansion.valR, Tracked.self]

end SchurPhase2

section SchurPhase3

variable {k n : ℕ}

end SchurPhase3

/-! ## The phase of the splits `1 = 1_{u = x} + 1_{u ≠ x}` -/

section SplitPhase

variable {k n : ℕ}

/-- Appending a dotted or `×`-dotted edge `u v` keeps the clauses `Base`, when it is no dotted
loop, its ends are in different blocks, and the result has no `×`-dotted edge inside a block. -/
theorem base_append {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base D' S X Γ T)
    {κ : Kind} (hκ : κ = .dot ∨ κ = .xdot) {u v : Atom k n} (huv : ¬ T.SameBlock u v)
    (hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps ++ [mkC κ u v], T.coeff⟩⟩)
    (hxa : (⟨T.comps ++ [mkC κ u v], T.coeff⟩ : Graph k n).XdotApart)
    (hsize : step1_sizeΦ D' X (T.comps ++ [mkC κ u v]) ≤ S) :
    Step1Base D' S X Γ ⟨T.comps ++ [mkC κ u v], T.coeff⟩ ∧
      (⟨T.comps ++ [mkC κ u v], T.coeff⟩ : Graph k n).ord = T.ord + κ.ord ∧
      step1_nWD (T.comps ++ [mkC κ u v]) = step1_nWD T.comps := by
  set g : Graph k n := ⟨T.comps ++ [mkC κ u v], T.coeff⟩ with hg
  have hin : ∀ d ∈ T.comps, d ∈ g.comps := fun d hd => List.mem_append_left _ hd
  have hfx : ∀ d ∈ g.comps, d ∈ T.comps ∨ d = mkC κ u v := by
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)
  have huv' : u ≠ v := fun h => huv (by rw [h]; exact SimpleGraph.Reachable.refl _)
  have hperm : g.comps.Perm (mkC κ u v :: T.comps) := List.perm_append_singleton _ _
  have hnw : step1_nWD g.comps = step1_nWD T.comps := by
    unfold step1_nWD
    rw [List.filter_append]
    rcases hκ with rfl | rfl <;> simp [mkC, Kind.isWDB]
  have hord : g.ord = T.ord + κ.ord := by
    simp only [Graph.ord, hg, List.map_append, List.sum_append]
    simp [mkC]
    ring
  have hrandom : κ.isRandom = false := by rcases hκ with rfl | rfl <;> rfl
  refine ⟨⟨hB.chain.tail hstep, ?_, ?_, ?_, hxa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hB.xright, hsize⟩, hord, hnw⟩
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
  · obtain ⟨w, hw, hwl, hwm, hwi⟩ := hB.labex
    exact ⟨w, hin w hw, hwl, hwm, hwi⟩
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
    · rcases hκ with rfl | rfl <;> simp [mkC, Kind.step1_isInvB] at hdi
  · intro d hd hdi
    rcases hfx d hd with h | rfl
    · exact hB.wd d h hdi
    · rfl
  · rw [hord, hnw]
    have : (0 : ℤ) ≤ κ.ord := by rcases hκ with rfl | rfl <;> simp [Kind.ord]
    linarith [hB.ord]

end SplitPhase

section SplitPhase2

variable {k n : ℕ}

end SplitPhase2

/-! ## The input graph -/

section Init

variable {k n : ℕ}

private theorem connNoX_of_normal {C : ℕ} {Γ : Graph k n} (h : Γ.Normal C) : Γ.ConnNoX := by
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
theorem base_init {D' S C : ℕ} {X : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hQ : Γ.IsQFormAt X) (hP : Γ.Plain) (hxa : Γ.XdotApart) (hX : X.isRight = true)
    (hS : step1_sizeΦ D' X Γ.comps ≤ S) : Step1Base D' S X Γ Γ := by
  have hnoinv : ∀ c ∈ Γ.comps, c.kind.step1_isInvB = false := by
    intro c hc
    have := (hP c hc).2.1
    revert this
    cases c.kind <;> simp [Kind.step1_isInvB]
  have hnowd : ∀ c ∈ Γ.comps, c.kind.isWDB = false := by
    intro c hc
    have := (hP c hc).2.2.1
    revert this
    cases c.kind <;> simp [Kind.isWDB]
  refine ⟨Relation.ReflTransGen.refl, connNoX_of_normal hN, hN.1.internal, ?_, hxa, rfl, ?_, ?_,
    fun c hc => (hP c hc).2.2.2.2, fun c hc => (hP c hc).2.2.2.1, hQ.2, ?_, ?_,
    fun c hc => Or.inl (hP c hc).1, fun c hc h => absurd h (by rw [hnoinv c hc]; simp),
    fun c hc h => absurd h (by rw [hnowd c hc]; simp), ?_, hX, hS⟩
  · intro c hc hk
    have hne := hN.2.1 c hc hk
    exact ⟨hne, (hN.2.2 _ _ hne).2 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩⟩
  · intro c L hp hk hx hy _
    have hc : c ∈ Γ.comps := hp.symm.subset (List.mem_cons_self ..)
    rcases hN.1.noIntDot c hc hk with h | h
    · revert h hx; cases c.x <;> simp
    · revert h hy; cases c.y <;> simp
  · exact fun h => Graph.doublyConnected_dcs h
  · obtain ⟨c, hc, hcl⟩ := hQ.1
    exact ⟨c, hc, hcl, (hP c hc).1, hnoinv c hc⟩
  · intro c hc hl
    have hr := (hP c hc).2.2.2.2.2 hl
    obtain ⟨hm, hi, hw, -, -⟩ := hP c hc
    revert hr hi hw
    simp only [Comp.isGoodKind]
    cases c.kind <;> simp [Kind.isRandom, hm]
  · have : step1_nWD Γ.comps = 0 := by
      unfold step1_nWD
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
def step1_atO (o : Fin k) (c : Comp (Atom k n)) : Bool := decide (c.x = .inl o ∨ c.y = .inl o)

/-- Every component of `Γ` at the external atom `o` is a diffusive edge. -/
def Step1ODiff (o : Fin k) (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, (c.x = .inl o ∨ c.y = .inl o) → c.kind.isDiffusive = true

/-- The components of `T` at the external atom `o` are, up to order, those of `Γ`. -/
def Step1OKeep (o : Fin k) (Γ T : Graph k n) : Prop :=
  (T.comps.filter (step1_atO o)).Perm (Γ.comps.filter (step1_atO o))

/-- The components of the output graph `t` at the external atom `o` are, up to order, the images
of those of `Γ`. -/
def Step1OOut (o : Fin k) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  (t.g.comps.filter (step1_atO o)).Perm ((Γ.comps.filter (step1_atO o)).map (Comp.map t.f))

/-- At every external atom at which all components of `Γ` are diffusive, the components of `T`
are, up to order, those of `Γ`. -/
def Step1OK1 (Γ T : Graph k n) : Prop := ∀ o, Step1ODiff o Γ → Step1OKeep o Γ T

/-- At every external atom at which all components of `Γ` are diffusive, the components of the
output graph `t` are, up to order, the images of those of `Γ`. -/
def Step1OO1 (Γ : Graph k n) (t : Tracked k n) : Prop := ∀ o, Step1ODiff o Γ → Step1OOut o Γ t

private theorem atO_iff {o : Fin k} {c : Comp (Atom k n)} :
    step1_atO o c = true ↔ (c.x = .inl o ∨ c.y = .inl o) := by
  simp [step1_atO]

private theorem Step1ODiff.diff {o : Fin k} {Γ : Graph k n} (hO : Step1ODiff o Γ) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (ho : step1_atO o c = true) : c.kind.isDiffusive = true :=
  hO c hc (atO_iff.1 ho)

private theorem Step1OKeep.diff {o : Fin k} {Γ T : Graph k n} (h : Step1OKeep o Γ T) (hO : Step1ODiff o Γ)
    {c : Comp (Atom k n)} (hc : c ∈ T.comps) (ho : step1_atO o c = true) : c.kind.isDiffusive = true :=
  hO.diff (List.mem_filter.1 (h.subset (List.mem_filter.2 ⟨hc, ho⟩))).1 ho

private theorem Step1OKeep.atO_false {o : Fin k} {Γ T : Graph k n} (h : Step1OKeep o Γ T) (hO : Step1ODiff o Γ)
    {c : Comp (Atom k n)} (hc : c ∈ T.comps) (hd : c.kind.isDiffusive = false) :
    step1_atO o c = false := by
  cases ho : step1_atO o c
  · rfl
  · rw [h.diff hO hc ho] at hd
    cases hd

private theorem Step1OKeep.erase {o : Fin k} {Γ T : Graph k n} (h : Step1OKeep o Γ T) {i : ℕ}
    {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (hco : step1_atO o c = false) (co : Coeff) :
    Step1OKeep o Γ ⟨T.comps.eraseIdx i, co⟩ := by
  have hp := (perm_eraseIdx hc).filter (step1_atO o)
  rw [List.filter_cons_of_neg (by simp [hco])] at hp
  exact hp.symm.trans h

private theorem Step1OKeep.append {o : Fin k} {Γ : Graph k n} {L : List (Comp (Atom k n))}
    (h : (L.filter (step1_atO o)).Perm (Γ.comps.filter (step1_atO o))) (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, step1_atO o d = false) (co : Coeff) : Step1OKeep o Γ ⟨L ++ new, co⟩ := by
  have : new.filter (step1_atO o) = [] := List.filter_eq_nil_iff.2 fun d hd => by simp [hnew d hd]
  change ((L ++ new).filter (step1_atO o)).Perm _
  rw [List.filter_append, this, List.append_nil]
  exact h

/-- A map of components that keeps the ends and fixes the components at `o` keeps the components
at `o`. -/
private theorem Step1OKeep.map {o : Fin k} {Γ T : Graph k n} (h : Step1OKeep o Γ T)
    (φ : Comp (Atom k n) → Comp (Atom k n)) (hφ : ∀ c, step1_atO o (φ c) = step1_atO o c)
    (hfix : ∀ c ∈ T.comps, step1_atO o c = true → φ c = c) (co : Coeff) :
    Step1OKeep o Γ ⟨T.comps.map φ, co⟩ := by
  change ((T.comps.map φ).filter (step1_atO o)).Perm _
  rw [List.filter_map]
  have e1 : T.comps.filter (step1_atO o ∘ φ) = T.comps.filter (step1_atO o) :=
    List.filter_congr fun c _ => by rw [Function.comp_apply, hφ]
  have e2 : (T.comps.filter (step1_atO o)).map φ = T.comps.filter (step1_atO o) := by
    conv_rhs => rw [← List.map_id (T.comps.filter (step1_atO o))]
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨hc, ho⟩ := List.mem_filter.1 hc
    exact hfix c hc ho
  rw [e1, e2]
  exact h

private theorem Comp.map_id'' {V : Type*} (c : Comp V) : c.map id = c := by
  cases c; simp [Comp.map]

/-- The output `Tracked.self Γ` keeps the components at `o`. -/
private theorem Step1OOut.self (o : Fin k) (Γ : Graph k n) : Step1OOut o Γ (Tracked.self Γ) := by
  unfold Step1OOut
  have : (Γ.comps.filter (step1_atO o)).map (Comp.map (Tracked.self Γ).f) = Γ.comps.filter (step1_atO o) := by
    conv_rhs => rw [← List.map_id (Γ.comps.filter (step1_atO o))]
    exact List.map_congr_left fun c _ => Comp.map_id'' c
  rw [this]
  exact List.Perm.refl _

theorem Step1OK1.refl (Γ : Graph k n) : Step1OK1 Γ Γ := fun _ _ => List.Perm.refl _

theorem Step1OO1.self (Γ : Graph k n) : Step1OO1 Γ (Tracked.self Γ) := fun o _ => Step1OOut.self o Γ

/-- Removing a component that is not diffusive keeps the components at the external atoms. -/
theorem Step1OK1.erase {Γ T : Graph k n} (h : Step1OK1 Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind.isDiffusive = false) (co : Coeff) :
    Step1OK1 Γ ⟨T.comps.eraseIdx i, co⟩ := fun o hO =>
  (h o hO).erase hc ((h o hO).atO_false hO (List.mem_of_getElem? hc) hcd) co

/-- Replacing a component that is not diffusive by components, each at an external atom only if
the replaced one is, keeps the components at the external atoms. -/
theorem Step1OK1.replace {Γ T : Graph k n} (h : Step1OK1 Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind.isDiffusive = false)
    (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, ∀ o : Fin k, step1_atO o d = true → step1_atO o c = true) (co : Coeff) :
    Step1OK1 Γ ⟨T.comps.eraseIdx i ++ new, co⟩ := by
  intro o hO
  have hco : step1_atO o c = false := (h o hO).atO_false hO (List.mem_of_getElem? hc) hcd
  refine Step1OKeep.append ((h o hO).erase hc hco T.coeff) new (fun d hd => ?_) co
  cases hd' : step1_atO o d
  · rfl
  · rw [hnew d hd o hd'] at hco
    cases hco

/-- Adding components that are not at the external atoms at which all components of `Γ` are
diffusive keeps the components there. -/
theorem Step1OK1.append {Γ T : Graph k n} (h : Step1OK1 Γ T) (new : List (Comp (Atom k n)))
    (hnew : ∀ o, Step1ODiff o Γ → ∀ d ∈ new, step1_atO o d = false) (co : Coeff) :
    Step1OK1 Γ ⟨T.comps ++ new, co⟩ := fun o hO => Step1OKeep.append (h o hO) new (hnew o hO) co

/-- The factors with minor `{X}` moved into the label group: the components at the external atoms
are kept. -/
theorem Step1OK1.absorb {Γ T : Graph k n} (h : Step1OK1 Γ T) (X : Atom k n) :
    Step1OK1 Γ (T.absorb (.Q, X)) := by
  intro o hO
  change Step1OKeep o Γ ⟨T.comps.map fun c => if c.label = none ∧ c.kind.isRandom = true ∧
    X ∈ c.minor then { c with label := some (.Q, X) } else c, T.coeff⟩
  refine Step1OKeep.map (h o hO) _ (fun c => ?_) (fun c hc ho => ?_) T.coeff
  · split <;> rfl
  · have hd := (h o hO).diff hO hc ho
    refine ite_eq_right_iff.2 fun hc' => ?_
    obtain ⟨-, hr, -⟩ := hc'
    cases hk : c.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]

/-- The components at `o` under `O_merge`, when `o` is the only atom with image `o` and every
component at `o` is diffusive. -/
private theorem filter_atO_merge {m : ℕ} (o : Fin k) (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) (hf : ∀ u, f u = .inl o ↔ u = .inl o) :
    ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, step1_atO o c = true → c.kind.isDiffusive = true) →
      (L.filterMap (step1_mergeComp rep f)).filter (step1_atO o) = (L.filter (step1_atO o)).map (Comp.map f)
  | [], _ => rfl
  | c :: L, hL => by
    have ih := filter_atO_merge o rep f hf L fun d hd => hL d (List.mem_cons_of_mem _ hd)
    rw [List.filterMap_cons]
    by_cases ho : step1_atO o c = true
    · have hdf := hL c (List.mem_cons_self ..) ho
      have hnd : c.kind ≠ .dot := fun h => by rw [h] at hdf; cases hdf
      have hns : c.kind.isSolid = false := by
        cases hk : c.kind <;> simp_all [Kind.isSolid, Kind.isDiffusive]
      rw [mergeComp_other hnd hns, List.filter_cons_of_pos ho]
      have ho' : step1_atO o (c.map f) = true := by
        rw [atO_iff] at ho ⊢
        simp only [Comp.map]
        rcases ho with h | h
        · exact Or.inl ((hf _).2 h)
        · exact Or.inr ((hf _).2 h)
      rw [List.filter_cons_of_pos ho', ih, List.map_cons]
    · have ho2 : ¬ (c.x = .inl o ∨ c.y = .inl o) := fun h => ho (atO_iff.2 h)
      push Not at ho2
      obtain ⟨hx, hy⟩ := ho2
      have hx' : f c.x ≠ .inl o := fun h => hx ((hf _).1 h)
      have hy' : f c.y ≠ .inl o := fun h => hy ((hf _).1 h)
      rw [List.filter_cons_of_neg ho]
      rcases hm : step1_mergeComp rep f c with _ | c'
      · exact ih
      · have hc' : step1_atO o c' = false := by
          unfold step1_mergeComp at hm
          split_ifs at hm
          · obtain rfl := Option.some.inj hm
            simp [step1_atO, Comp.map, hx']
          · obtain rfl := Option.some.inj hm
            simp [step1_atO, Comp.map, hx', hy']
        simp only
        rw [List.filter_cons_of_neg (by simp [hc']), ih]

/-- The atom map of `O_merge` sends only `o` to `o`. -/
private theorem Step1MergeSpec.f_iff {Γ : Graph k n} {t : Tracked k n} (hs : Step1MergeSpec Γ t)
    (o : Fin k) (u : Atom k n) : t.f u = .inl o ↔ u = .inl o := by
  obtain ⟨φ, hφ, -⟩ := hs.f_inr
  rcases u with a | i
  · simp [hs.f_inl]
  · rw [hφ]
    simp

private theorem filter_atO_nd {o : Fin k} {L : List (Comp (Atom k n))}
    (hL : ∀ c ∈ L, step1_atO o c = true → c.kind ≠ .dot) :
    L.filter (step1_atO o) = (L.filter fun c => decide (c.kind ≠ .dot)).filter (step1_atO o) := by
  rw [List.filter_filter]
  refine List.filter_congr fun c hc => ?_
  by_cases ho : step1_atO o c = true
  · simp [ho, hL c hc ho]
  · simp [ho]

/-- The output of `O_merge` followed by the removal of redundant dotted edges keeps the components
at the external atoms. -/
theorem final_oo1 {Γ T : Graph k n} {t : Tracked k n} (hs : Step1MergeSpec T t)
    (hK : Step1OK1 Γ T) {g' : Graph k t.nOut} (hsub : g'.comps.Sublist t.g.comps)
    (hnd : (g'.comps.filter fun c => decide (c.kind ≠ .dot)).Perm
      (t.g.comps.filter fun c => decide (c.kind ≠ .dot))) :
    Step1OO1 Γ ⟨t.nOut, g', t.f⟩ := by
  intro o hO
  have hK' := hK o hO
  have hT : ∀ c ∈ T.comps, step1_atO o c = true → c.kind.isDiffusive = true :=
    fun c hc ho => hK'.diff hO hc ho
  have hm := filter_atO_merge o T.step1_mrep t.f (hs.f_iff o) T.comps hT
  rw [← hs.comps_eq] at hm
  have hnd1 : ∀ c ∈ t.g.comps, step1_atO o c = true → c.kind ≠ .dot := by
    intro c hc ho h
    have hc' : c ∈ (T.comps.filter (step1_atO o)).map (Comp.map t.f) := by
      rw [← hm]
      exact List.mem_filter.2 ⟨hc, ho⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨hdT, hdo⟩ := List.mem_filter.1 hd
    have := hT d hdT hdo
    simp only [Comp.map] at h
    rw [h] at this
    cases this
  have hnd2 : ∀ c ∈ g'.comps, step1_atO o c = true → c.kind ≠ .dot :=
    fun c hc ho => hnd1 c (hsub.subset hc) ho
  change (g'.comps.filter (step1_atO o)).Perm ((Γ.comps.filter (step1_atO o)).map (Comp.map t.f))
  rw [filter_atO_nd hnd2]
  refine (hnd.filter (step1_atO o)).trans ?_
  rw [← filter_atO_nd hnd1, hm]
  exact List.Perm.map _ hK'

end OAt

section ODrop

variable {k m : ℕ}

end ODrop



section OSteps

variable {k n : ℕ}

end OSteps

section OPhases

variable {k n : ℕ}

end OPhases

end RBM8D.Graphs
