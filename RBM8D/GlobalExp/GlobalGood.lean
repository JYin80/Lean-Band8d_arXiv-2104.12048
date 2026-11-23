module

public import RBM8D.GlobalExp.RunClauses
public import RBM8D.Graph.QExp.MainB

@[expose] public section

/-!
# [II, Lemmas 6.5, 6.7] in the block reading

The graphs obtained by substituting the `T`-expansion of order `n - 1` into a globally standard
graph at Step 3 of [II, Strategy 6.6] ([II, Lemma 6.5]), and the graphs on which no step of the
strategy applies ([II, Lemma 6.7]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## [II, Lemma 6.7] on graphs without `(G_{xx})⁻¹` and `W_D` weights -/

/-- **[II, Lemma 6.7]** in the block reading, on graphs of the form `Graph.Plain` (no `G^{(T)}`
entry, no `(G_{xx})⁻¹` or `W_D` weight, no dotted loop): a normal regular graph, globally standard
in the block reading, with the charge pattern of the block normal form, the clause on the external
atoms, only diffusive edges at `⊗`, a locally standard minimal isolated subset of `Graph.toMG'`,
not a `⊕/⊖`-recollision graph and with no blue solid edge for Step 2, has no proper isolated
subset in `Graph.toMG'` and a deterministic maximal subgraph. -/
def nonstopStmtB' : Prop :=
  ∀ (n₀ C : ℕ) (Γ : Graph 3 n₀), Γ.Normal C → gsPM' Γ → Γ.ColourInvB → Γ.ExtClause →
    Γ.TensorDiffusive → Γ.MISLocStdB → ¬ Γ.IsRecollision {1, 2} → (∀ i, ¬ Γ.Step2EdgeB i) →
    Γ.Plain → (∀ P, ¬ Γ.toMG'.IsProperIso Γ.toMG'.int P) ∧ Γ.MaxDeterministic

section Nonstop

variable {n : ℕ}

/-! ### Graphs without dotted edges -/

/-- A walk of a simple graph stays in a set closed under adjacency. -/
private theorem GlobalGood_walk_closed {V : Type*} {G : SimpleGraph V} (p : V → Prop)
    (hp : ∀ a b, G.Adj a b → p a → p b) {u v : V} (h : G.Reachable u v) (hu : p u) : p v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hp _ _ hadj hu)

/-- Under the hypotheses of [II, Lemma 6.7], the graph has no dotted edge: a dotted edge has an
external end (regularity), no end at `⊗` (only diffusive edges at `⊗`), no internal end (not a
`⊕/⊖`-recollision graph) and is not a loop, so it joins `⊕` and `⊖`; then the block of `⊕` has
two atoms and no internal atom, against the clause on the external atoms. -/
private theorem GlobalGood_dotFree {C : ℕ} {Γ : Graph 3 n} (hN : Γ.Normal C) (hE : Γ.ExtClause)
    (hT : Γ.TensorDiffusive) (hR : ¬ Γ.IsRecollision {1, 2}) (hP : Γ.Plain) : Γ.DotFree := by
  have hTD : ∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.isDiffusive = true := by
    intro c hc h0
    have := List.all_eq_true.1 hT c hc
    rcases h0 with h0 | h0 <;> simpa [h0] using this
  -- every dotted edge joins `⊕` and `⊖`
  have hpm : ∀ c ∈ Γ.comps, c.kind = .dot →
      (c.x = .inl 1 ∨ c.x = .inl 2) ∧ (c.y = .inl 1 ∨ c.y = .inl 2) := by
    intro c hc hk
    have hne : c.x ≠ c.y := (hP c hc).2.2.2.1 hk
    have hd0 : ¬ (c.x = .inl 0 ∨ c.y = .inl 0) := fun h => by
      have := hTD c hc h; rw [hk] at this; exact absurd this (by decide)
    have hleft := hN.1.noIntDot c hc hk
    have hrec : ∀ b : Fin 3, b ≠ 0 → c.x = .inl b → c.y.isRight = false := by
      intro b hb hx
      by_contra hy
      refine hR ⟨c, hc, hk, Or.inl ⟨⟨b, ?_, hx⟩, by simpa using hy⟩⟩
      fin_cases b <;> simp_all
    have hrec' : ∀ b : Fin 3, b ≠ 0 → c.y = .inl b → c.x.isRight = false := by
      intro b hb hy
      by_contra hx
      refine hR ⟨c, hc, hk, Or.inr ⟨⟨b, ?_, hy⟩, by simpa using hx⟩⟩
      fin_cases b <;> simp_all
    rcases hx : c.x with a | a <;> rcases hy : c.y with b | b <;> rw [hx, hy] at hne hd0 hleft
    · fin_cases a <;> fin_cases b <;> simp_all
    · fin_cases a
      · simp at hd0
      · exact absurd (hrec 1 (by decide) hx) (by rw [hy]; simp)
      · exact absurd (hrec 2 (by decide) hx) (by rw [hy]; simp)
    · fin_cases b
      · simp at hd0
      · exact absurd (hrec' 1 (by decide) hy) (by rw [hx]; simp)
      · exact absurd (hrec' 2 (by decide) hy) (by rw [hx]; simp)
    · simp at hleft
  intro c hc hk
  obtain ⟨hx, hy⟩ := hpm c hc hk
  have hne : c.x ≠ c.y := (hP c hc).2.2.2.1 hk
  have hadj : Γ.dotGraph.Adj c.x c.y :=
    (SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
  have hb12 : Γ.SameBlock (.inl 1) (.inl 2) := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hadj hne
    · exact absurd rfl hne
    · exact hadj.reachable
    · exact hadj.reachable.symm
    · exact absurd rfl hne
  obtain ⟨b, hb⟩ := hE.1 (.inl 1) (.inl 2) (by simp) hb12
  have hcl : ∀ u v : Atom 3 n, Γ.dotGraph.Adj u v →
      (u = .inl 1 ∨ u = .inl 2) → (v = .inl 1 ∨ v = .inl 2) := by
    intro u v huv _
    obtain ⟨-, h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 huv
    rcases h with ⟨d, hd, hdk, rfl, rfl⟩ | ⟨d, hd, hdk, rfl, rfl⟩
    · exact (hpm d hd hdk).2
    · exact (hpm d hd hdk).1
  rcases GlobalGood_walk_closed _ hcl hb (Or.inl rfl) with h | h <;> exact Sum.inr_ne_inl h

/-- Without dotted edges, two atoms lie in one block only if they are equal. -/
private theorem GlobalGood_sameBlock {Γ : Graph 3 n} (hd : Γ.DotFree) (u v : Atom 3 n) :
    Γ.SameBlock u v ↔ u = v :=
  Graph.sameBlock_iff_eq Γ (fun c hc hk => absurd hk (hd c hc)) u v

/-- Without dotted edges, no external atom has an anchor. -/
private theorem GlobalGood_anchor {Γ : Graph 3 n} (hd : Γ.DotFree) (a : Fin 3) :
    Γ.anchor (.inl a) = none := by
  unfold Graph.anchor
  rw [List.find?_eq_none]
  intro _ _
  simp only [decide_eq_true_eq, GlobalGood_sameBlock hd]
  exact Sum.inl_ne_inr

/-- Without dotted edges, every atom is its own atom in the block normal form. -/
private theorem GlobalGood_flatAtom {Γ : Graph 3 n} (hd : Γ.DotFree) (u : Atom 3 n) :
    Γ.flatAtom u = u := by
  rcases u with a | a
  · simp only [Graph.flatAtom, GlobalGood_anchor hd a]
  · rfl

/-- Without dotted edges, the block normal form keeps every component. -/
private theorem GlobalGood_flatComp {Γ : Graph 3 n} (hd : Γ.DotFree) (c : Comp (Atom 3 n)) :
    Γ.flatComp c = c := by
  unfold Graph.flatComp
  split_ifs
  · rfl
  · simp only [GlobalGood_flatAtom hd]

/-- Without dotted edges, every external atom is unpinned. -/
private theorem GlobalGood_unpinned {Γ : Graph 3 n} (hd : Γ.DotFree) (a : Fin 3) :
    Γ.Unpinned (.inl a) :=
  ⟨rfl, fun _ h => Sum.inl_ne_inr ((GlobalGood_sameBlock hd _ _).1 h)⟩

/-- Without dotted edges, the charge pattern of the block normal form is `Graph.ColourInv'`. -/
private theorem GlobalGood_colourInv' {Γ : Graph 3 n} (hd : Γ.DotFree) (h : Γ.ColourInvB) :
    Γ.ColourInv' := by
  intro c hc
  have : c ∈ Γ.blockNorm.comps := by
    simp only [Graph.blockNorm, List.mem_map]
    exact ⟨c, hc, GlobalGood_flatComp hd c⟩
  exact h c this

/-! ### Molecules -/

/-- The representative of the molecule of an internal atom is an internal atom of its molecule. -/
private theorem GlobalGood_molRep_inr (Γ : Graph 3 n) (a : Fin n) :
    ∃ b : Fin n, Γ.molRep (.inr a) = .inr b ∧ Γ.SameMol (.inr a) (.inr b) := by
  have hs : ((List.finRange n).find?
      fun b : Fin n => decide (Γ.SameMol (.inr a) (.inr b))).isSome :=
    List.find?_isSome.2 ⟨a, List.mem_finRange a, decide_eq_true (Or.inl rfl)⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨b, by simp only [Graph.molRep, hb, Option.getD_some], ?_⟩
  simpa using List.find?_some hb

/-- Two atoms with the same representative lie in one molecule. -/
private theorem GlobalGood_sameMol_of_molRep (Γ : Graph 3 n) {u v : Atom 3 n}
    (h : Γ.molRep u = Γ.molRep v) : Γ.SameMol u v := by
  have key : ∀ w : Atom 3 n, Γ.SameMol w (Γ.molRep w) := by
    rintro (a | a)
    · exact Or.inl rfl
    · obtain ⟨b, hb, hs⟩ := GlobalGood_molRep_inr Γ a
      rw [hb]; exact hs
  exact (Γ.sameMol_equivalence.trans (key u) (h ▸ (Γ.sameMol_equivalence.symm (key v))))

/-- An atom whose molecule is an internal vertex of `Graph.toMG'` is internal. -/
private theorem GlobalGood_isRight_of_mem_int (Γ : Graph 3 n) {u : Atom 3 n}
    (h : Γ.molRep u ∈ Γ.toMG'.int) : u.isRight = true := by
  rcases u with a | a
  · obtain ⟨b, -, hb⟩ := Finset.mem_image.1 h
    obtain ⟨c, hc, -⟩ := GlobalGood_molRep_inr Γ b
    rw [hc] at hb
    simp [Graph.molRep] at hb
  · rfl

/-- The molecule of every atom is a vertex of `Graph.toMG'`. -/
private theorem GlobalGood_isVtx (Γ : Graph 3 n) (u : Atom 3 n) :
    Γ.toMG'.IsVtx (Γ.molRep u) := by
  rcases u with a | a
  · exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  · exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ a))

/-- The minimal isolated subset consists of internal vertices. -/
private theorem GlobalGood_mis_sub {V E : Type} (G : MGraph V E) : G.MIS ⊆ G.int := by
  classical
  intro v hv
  simp only [MGraph.MIS, Finset.mem_filter] at hv
  exact hv.1

/-- An atom whose molecule lies in the minimal isolated subset of `Graph.toMG'` is internal. -/
private theorem GlobalGood_isRight_of_mem_MIS (Γ : Graph 3 n) {u : Atom 3 n}
    (h : Γ.molRep u ∈ Γ.toMG'.MIS) : u.isRight = true :=
  GlobalGood_isRight_of_mem_int Γ (GlobalGood_mis_sub _ h)

/-! ### The edges of `Graph.toMG'` without dotted edges -/

/-- Without dotted edges, the edge `.inl i` of `Graph.toMG'` joins the molecules of the two atoms
of the component `i`. -/
private theorem GlobalGood_ends_inl {Γ : Graph 3 n} (hd : Γ.DotFree) (i : Fin Γ.comps.length) :
    Γ.toMG'.ends (.inl i) = (Γ.molRep Γ.comps[i].x, Γ.molRep Γ.comps[i].y) := by
  simp only [Graph.toMG', GlobalGood_flatComp hd]

/-- Without dotted edges, the edge `.inl i` of `Graph.toMG'` is absent when the two atoms of the
component `i` lie in one molecule, and has the class of its kind otherwise. -/
private theorem GlobalGood_cls_inl {Γ : Graph 3 n} (hd : Γ.DotFree) (i : Fin Γ.comps.length) :
    Γ.toMG'.cls (.inl i) = if Γ.molRep Γ.comps[i].x = Γ.molRep Γ.comps[i].y then none
      else Γ.comps[i].kind.mclass := by
  have hk : Γ.comps[i].kind ≠ .dot := hd _ (List.getElem_mem _)
  simp only [Graph.toMG', GlobalGood_flatComp hd, hk, false_or]

/-- Without dotted edges, the pin edges of `Graph.toMG'` are absent. -/
private theorem GlobalGood_cls_inr {Γ : Graph 3 n} (hd : Γ.DotFree) (a : Fin 3) :
    Γ.toMG'.cls (.inr a) = none := by
  simp only [Graph.toMG', GlobalGood_anchor hd a]

private theorem GlobalGood_mclass_plus {κ : Kind} (h : κ.mclass = some .plus) :
    κ = .G .plus := by
  cases κ with
  | G c => cases c <;> simp_all [Kind.mclass]
  | aux j r b => cases b <;> simp_all [Kind.mclass]
  | _ => simp_all [Kind.mclass]

private theorem GlobalGood_mclass_minus {κ : Kind} (h : κ.mclass = some .minus) :
    κ = .G .minus := by
  cases κ with
  | G c => cases c <;> simp_all [Kind.mclass]
  | aux j r b => cases b <;> simp_all [Kind.mclass]
  | _ => simp_all [Kind.mclass]

/-! ### The minimal isolated subset -/

/-- If the proper isolated subsets form a chain and one exists, the minimal isolated subset is a
proper isolated subset with no proper isolated subset of its own. -/
private theorem GlobalGood_mis_iso {V E : Type} {G : MGraph V E}
    (hch : G.IsoChain) {P : Finset V} (hP : G.IsProperIso G.int P) :
    G.IsProperIso G.int G.MIS ∧ ∀ Q, ¬ G.IsProperIso G.MIS Q := by
  classical
  have hex : ∃ k, ∃ Q, G.IsProperIso G.int Q ∧ Q.card = k := ⟨_, P, hP, rfl⟩
  obtain ⟨P₀, hP₀, hk⟩ := Nat.find_spec hex
  have hmin : ∀ Q, G.IsProperIso G.int Q → P₀ ⊆ Q := by
    intro Q hQ
    rcases hch P₀ Q hP₀ hQ with h | h
    · exact h
    · have h1 : Nat.find hex ≤ Q.card := Nat.find_min' hex ⟨Q, hQ, rfl⟩
      have : Q = P₀ := Finset.eq_of_subset_of_card_le h (by omega)
      rw [this]
  have hmis : G.MIS = P₀ := by
    ext v
    simp only [MGraph.MIS, Finset.mem_filter]
    constructor
    · rintro ⟨-, hv⟩
      exact hv P₀ hP₀
    · intro hv
      exact ⟨hP₀.1.1 hv, fun Q hQ => hmin Q hQ hv⟩
  rw [hmis]
  refine ⟨hP₀, fun Q ⟨hQ, hlt⟩ => ?_⟩
  have h1 : Nat.find hex ≤ Q.card :=
    Nat.find_min' hex ⟨Q, ⟨hQ, Finset.ssubset_of_ssubset_of_subset hlt hP₀.2.1⟩, rfl⟩
  have := Finset.card_lt_card hlt
  omega

/-- Without proper isolated subsets, the minimal isolated subset is the set of all internal
vertices. -/
private theorem GlobalGood_mis_int {V E : Type} {G : MGraph V E}
    (h : ∀ Q, ¬ G.IsProperIso G.int Q) : G.MIS = G.int := by
  classical
  unfold MGraph.MIS
  exact Finset.filter_true_of_mem fun v _ P hP => absurd hP (h P)

/-! ### Standard neutral atoms -/

private theorem GlobalGood_two_le_countP {α : Type*} {p : α → Bool} :
    ∀ {l : List α} {i j : ℕ} (hi : i < l.length) (hj : j < l.length), i ≠ j →
      p l[i] = true → p l[j] = true → 2 ≤ l.countP p
  | [], _, _, hi, _, _, _, _ => absurd hi (by simp)
  | a :: l, 0, 0, _, _, hij, _, _ => absurd rfl hij
  | a :: l, 0, j + 1, _, hj, _, hpi, hpj => by
    have hj' : j < l.length := by simpa using hj
    have : 0 < l.countP p :=
      List.countP_pos_iff.2 ⟨l[j], List.getElem_mem hj', by simpa using hpj⟩
    simp only [List.getElem_cons_zero] at hpi
    rw [List.countP_cons_of_pos hpi]
    omega
  | a :: l, i + 1, 0, hi, _, _, hpi, hpj => by
    have hi' : i < l.length := by simpa using hi
    have : 0 < l.countP p :=
      List.countP_pos_iff.2 ⟨l[i], List.getElem_mem hi', by simpa using hpi⟩
    simp only [List.getElem_cons_zero] at hpj
    rw [List.countP_cons_of_pos hpj]
    omega
  | a :: l, i + 1, j + 1, hi, hj, hij, hpi, hpj => by
    have := GlobalGood_two_le_countP (l := l) (Nat.lt_of_succ_lt_succ hi)
      (Nat.lt_of_succ_lt_succ hj) (fun h => hij (by rw [h])) (by simpa using hpi)
      (by simpa using hpj)
    rw [List.countP_cons]
    omega

set_option linter.flexible false in
/-- The number of ends of charge `ch` at `u` is the number of solid edges of charge `ch` at `u`
that are not loops. -/
private theorem GlobalGood_ends_countP (Γ : Graph 3 n) (u : Atom 3 n) (ch : Charge) :
    (Γ.ends u).countP (fun e => e.2 == ch) =
      Γ.comps.countP (fun c => c.kind == .G ch && (c.x == u || c.y == u) && c.x != c.y) := by
  unfold Graph.ends
  generalize Γ.comps = l
  induction l with
  | nil => rfl
  | cons c l ih =>
    rcases c with ⟨κ, x, y, mi, lab⟩
    cases κ with
    | G c' =>
      simp only [List.filterMap_cons, List.countP_cons]
      by_cases hx : x = u <;> by_cases hy : y = u <;> by_cases hc : c' = ch <;>
        simp_all
      exact fun h => hy h.symm
    | _ => simp [ih]

/-- At an atom of degree `0`, or of degree `2` that is standard neutral, of a graph whose solid
edges are not loops, there are as many solid edges of charge `plus` as of charge `minus`, and at
most one of each. -/
private theorem GlobalGood_std_count {Γ : Graph 3 n}
    (hloop : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) (u : Atom 3 n)
    (h : Γ.deg u = 0 ∨ (Γ.deg u = 2 ∧ Γ.stdNeutralAt u = true)) :
    Γ.comps.countP (fun c => c.kind == .G .plus && (c.x == u || c.y == u)) =
        Γ.comps.countP (fun c => c.kind == .G .minus && (c.x == u || c.y == u)) ∧
      Γ.comps.countP (fun c => c.kind == .G .minus && (c.x == u || c.y == u)) ≤ 1 := by
  have hcongr : ∀ ch : Charge,
      Γ.comps.countP (fun c => c.kind == .G ch && (c.x == u || c.y == u)) =
        (Γ.ends u).countP (fun e => e.2 == ch) := by
    intro ch
    rw [GlobalGood_ends_countP]
    refine List.countP_congr fun c hc => ?_
    by_cases hk : c.kind = .G ch
    · have := hloop c hc (by rw [hk]; rfl)
      simp [hk, this]
    · simp [hk]
  rw [hcongr, hcongr]
  rcases h with h | ⟨-, h⟩
  · have h0 : ∀ ch : Charge, (Γ.ends u).countP (fun e => e.2 == ch) = 0 := by
      intro ch
      rw [← hcongr, List.countP_eq_zero]
      intro c hc hp
      have hl : 0 < Γ.deg u := by
        unfold Graph.deg
        refine List.length_pos_iff_exists_mem.2 ⟨c, List.mem_filter.2 ⟨hc, ?_⟩⟩
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        simp only [hp.1, Kind.isSolid, Bool.true_and]
        exact hp.2
      omega
    rw [h0, h0]
    simp
  · unfold Graph.stdNeutralAt at h
    revert h
    rcases Γ.ends u with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, l⟩⟩⟩
    · simp
    · simp
    · rcases e₁ with ⟨d₁, c₁⟩
      rcases e₂ with ⟨d₂, c₂⟩
      cases c₁ <;> cases c₂ <;> simp
    · simp

/-! ### Crossing edges -/

/-- Without dotted edges, a red solid edge of `Graph.toMG'` between `S` and its complement is a
component `Ḡ` with one atom in a molecule of `S` and the other outside. -/
private theorem GlobalGood_redCross {Γ : Graph 3 n} (hd : Γ.DotFree) {S : Finset (Atom 3 n)}
    {e : Fin Γ.comps.length ⊕ Fin 3} (h : Γ.toMG'.RedCrosses S e) :
    ∃ i : Fin Γ.comps.length, e = .inl i ∧ Γ.comps[i].kind = .G .minus ∧
      (Γ.molRep Γ.comps[i].x ∈ S ∧ Γ.molRep Γ.comps[i].y ∉ S ∨
        Γ.molRep Γ.comps[i].x ∉ S ∧ Γ.molRep Γ.comps[i].y ∈ S) := by
  obtain ⟨hc, -, -, hcut⟩ := h
  rcases e with i | a
  · rw [GlobalGood_cls_inl hd] at hc
    split_ifs at hc
    simp only [MGraph.Cut, GlobalGood_ends_inl hd] at hcut
    exact ⟨i, rfl, GlobalGood_mclass_minus hc, hcut⟩
  · rw [GlobalGood_cls_inr hd] at hc
    exact absurd hc (by simp)

/-- Without dotted edges, a blue solid edge with one atom in a molecule of `S` and the other
outside is a blue edge of `Graph.toMG'` between `S` and its complement. -/
private theorem GlobalGood_plusCross {Γ : Graph 3 n} (hd : Γ.DotFree) {S : Finset (Atom 3 n)}
    (i : Fin Γ.comps.length) (hk : Γ.comps[i].kind = .G .plus)
    (hc : Γ.molRep Γ.comps[i].x ∈ S ∧ Γ.molRep Γ.comps[i].y ∉ S ∨
      Γ.molRep Γ.comps[i].x ∉ S ∧ Γ.molRep Γ.comps[i].y ∈ S) :
    Γ.toMG'.Crosses S (.inl i) ∧ Γ.toMG'.cls (.inl i) = some .plus := by
  have hne : Γ.molRep Γ.comps[i].x ≠ Γ.molRep Γ.comps[i].y := by
    rintro h
    rw [h] at hc
    tauto
  have hcls : Γ.toMG'.cls (.inl i) = some .plus := by
    rw [GlobalGood_cls_inl hd]
    simp only [hne, ↓reduceIte, hk]
    rfl
  refine ⟨⟨by rw [hcls]; simp, by rw [hcls]; simp, ?_, ?_, ?_⟩, hcls⟩
  · rw [GlobalGood_ends_inl hd]; exact GlobalGood_isVtx Γ _
  · rw [GlobalGood_ends_inl hd]; exact GlobalGood_isVtx Γ _
  · simp only [MGraph.Cut, GlobalGood_ends_inl hd]; exact hc

private theorem GlobalGood_pair {α : Type*} {a b x y z : α} (hx : x = a ∨ x = b)
    (hy : y = a ∨ y = b) (hz : z = a ∨ z = b) (hxy : x ≠ y) (hzx : z ≠ x) : z = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp_all

/-- A proper isolated subset of a doubly connected molecular graph has at most one blue solid
edge to its complement: its two edges to the complement are one edge of the black net and one
edge of the blue net. -/
private theorem GlobalGood_isolated_blue {V E : Type} {G : MGraph V E} (hDC : G.DC)
    {P : Finset V} (hP : G.IsProperIso G.int P) {e e' : E} (he : G.Crosses P e)
    (hc : G.cls e = some .plus) (he' : G.Crosses P e') (hc' : G.cls e' = some .plus) : e = e' := by
  obtain ⟨⟨hsub, e₁, e₂, -, hcr⟩, hlt⟩ := hP
  obtain ⟨B, B', hdis, hB, hB', hsB, hsB'⟩ := hDC
  have hne : P.Nonempty := by
    obtain ⟨-, -, -, -, hcut⟩ := (hcr e₁).2 (Or.inl rfl)
    rcases hcut with ⟨h, -⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩
  have hnot : ¬ G.int ⊆ P := fun h => (Finset.ssubset_iff_subset_ne.1 hlt).2
    (Finset.Subset.antisymm hlt.1 h)
  obtain ⟨eb, heb, hcb, hb1, hb2, hbcut⟩ := hsB P hsub hne hnot
  obtain ⟨eu, heu, hcu, hu1, hu2, hucut⟩ := hsB' P hsub hne hnot
  have hdb : G.cls eb = some .diff := hB eb heb
  have hbc : G.Crosses P eb := ⟨hcb, by rw [hdb]; simp, Or.inl hb1, Or.inl hb2, hbcut⟩
  have huc : G.Crosses P eu :=
    ⟨hcu, by rcases hB' eu heu with h | h | h <;> rw [h] <;> simp, Or.inl hu1, Or.inl hu2,
      hucut⟩
  have hbu : eb ≠ eu := by
    rintro rfl
    exact Finset.disjoint_left.1 hdis heb heu
  have h1 := (hcr eb).1 hbc
  have h2 := (hcr eu).1 huc
  have hneb : ∀ f, G.cls f = some .plus → f ≠ eb := by
    rintro f hf rfl
    rw [hdb] at hf
    exact absurd hf (by simp)
  rw [GlobalGood_pair h1 h2 ((hcr e).1 he) hbu (hneb e hc),
    GlobalGood_pair h1 h2 ((hcr e').1 he') hbu (hneb e' hc')]

/-- No blue solid edge has both atoms in molecules of the minimal isolated subset, when no
blue solid edge is chosen by Step 2: one inside a molecule is chosen by Step 2, and otherwise the
pre-deterministic order of the subgraph induced on the minimal isolated subset (no pin edge is
present without dotted edges) begins with a blue solid edge chosen by Step 2. -/
private theorem GlobalGood_noBlueIn {Γ : Graph 3 n} (hd : Γ.DotFree)
    (hpre : (Γ.toMG'.induce Γ.toMG'.MIS).PreDet) (hS : ∀ i, ¬ Γ.Step2EdgeB i)
    (i : Fin Γ.comps.length) (hk : Γ.comps[i].kind = .G .plus) :
    ¬ (Γ.molRep Γ.comps[i].x ∈ Γ.toMG'.MIS ∧ Γ.molRep Γ.comps[i].y ∈ Γ.toMG'.MIS) := by
  rintro ⟨hx, hy⟩
  obtain ⟨-, l, hl⟩ := hpre
  by_cases hm : Γ.molRep Γ.comps[i].x = Γ.molRep Γ.comps[i].y
  · exact hS i ⟨hk, hx, hy, Or.inl (GlobalGood_sameMol_of_molRep Γ hm)⟩
  have hip : (Γ.toMG'.induce Γ.toMG'.MIS).IsIntPlus (.inl i) := by
    have hends := GlobalGood_ends_inl hd i
    refine ⟨?_, ?_, ?_⟩
    · simp only [MGraph.induce, hends, GlobalGood_cls_inl hd, hx, hy, and_self, hm, ↓reduceIte]
      rw [hk]
      rfl
    · simp only [MGraph.induce, hends]; exact hx
    · simp only [MGraph.induce, hends]; exact hy
  have hmem := (hl.2.1 _).2 hip
  obtain ⟨e₀, l', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  obtain ⟨hc0, h01, h02⟩ := (hl.2.1 e₀).1 List.mem_cons_self
  rcases e₀ with j | a
  · simp only [MGraph.induce, GlobalGood_ends_inl hd] at hc0 h01 h02
    simp only [h01, h02, and_self, ↓reduceIte, GlobalGood_cls_inl hd] at hc0
    split_ifs at hc0
    exact hS j ⟨GlobalGood_mclass_plus hc0, h01, h02, Or.inr ⟨_, hl, rfl⟩⟩
  · simp [MGraph.induce, GlobalGood_cls_inr hd] at hc0

private theorem GlobalGood_eq_of_length_le_one {α : Type*} {l : List α} (h : l.length ≤ 1)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l, h, ha, hb with
  | [_], _, ha, hb => rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]

private theorem GlobalGood_isRandom {κ : Kind} (h : κ.isRandom = true) :
    (∃ ch, κ = .G ch) ∨ (∃ ch, κ = .weight ch) ∨ (∃ ch, κ = .light ch) ∨ (∃ ch, κ = .inv ch) ∨
      ∃ ch D, κ = .wD ch D := by
  cases κ <;> simp_all [Kind.isRandom]

/-! ### The two parts of the statement -/

variable {C : ℕ} {Γ : Graph 3 n}

/-- At an atom of the minimal isolated subset: as many blue as red solid edges, at most one of
each. -/
private theorem GlobalGood_std_mis (hN : Γ.Normal C) (hM : Γ.MISLocStdB) (u : Atom 3 n)
    (hu : Γ.molRep u ∈ Γ.toMG'.MIS) :
    Γ.comps.countP (fun c => c.kind == .G .plus && (c.x == u || c.y == u)) =
        Γ.comps.countP (fun c => c.kind == .G .minus && (c.x == u || c.y == u)) ∧
      Γ.comps.countP (fun c => c.kind == .G .minus && (c.x == u || c.y == u)) ≤ 1 := by
  have hr := GlobalGood_isRight_of_mem_MIS Γ hu
  rcases u with a | a
  · simp at hr
  · exact GlobalGood_std_count hN.2.1 _ (hM.2 a hu).2

/-- A red solid edge at an atom of the minimal isolated subset comes with a blue solid edge at
that atom. -/
private theorem GlobalGood_plus_of_minus (hN : Γ.Normal C) (hM : Γ.MISLocStdB) (u : Atom 3 n)
    (hu : Γ.molRep u ∈ Γ.toMG'.MIS) (c : Comp (Atom 3 n)) (hc : c ∈ Γ.comps)
    (hk : c.kind = .G .minus) (hcu : c.x = u ∨ c.y = u) :
    ∃ b : Fin Γ.comps.length, Γ.comps[b].kind = .G .plus ∧
      (Γ.comps[b].x = u ∨ Γ.comps[b].y = u) := by
  have h1 : 0 < Γ.comps.countP (fun c => c.kind == .G .minus && (c.x == u || c.y == u)) :=
    List.countP_pos_iff.2 ⟨c, hc, by simpa [hk] using hcu⟩
  rw [← (GlobalGood_std_mis hN hM u hu).1] at h1
  obtain ⟨b, hb, hpb⟩ := List.countP_pos_iff.1 h1
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hpb
  exact ⟨⟨i, hi⟩, hpb.1, hpb.2⟩

/-- Two distinct red solid edges never share an atom of the minimal isolated subset. -/
private theorem GlobalGood_two_minus (hN : Γ.Normal C) (hM : Γ.MISLocStdB) (u : Atom 3 n)
    (hu : Γ.molRep u ∈ Γ.toMG'.MIS) (i j : Fin Γ.comps.length) (hij : i ≠ j)
    (hki : Γ.comps[i].kind = .G .minus) (hiu : Γ.comps[i].x = u ∨ Γ.comps[i].y = u)
    (hkj : Γ.comps[j].kind = .G .minus) (hju : Γ.comps[j].x = u ∨ Γ.comps[j].y = u) : False := by
  have h2 := GlobalGood_two_le_countP
    (p := fun c => c.kind == .G .minus && (c.x == u || c.y == u)) i.2 j.2
    (fun h => hij (Fin.ext h))
    (by simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]; exact ⟨hki, hiu⟩)
    (by simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]; exact ⟨hkj, hju⟩)
  have := (GlobalGood_std_mis hN hM u hu).2
  omega

/-- A blue solid edge at an atom of the minimal isolated subset has its other atom outside. -/
private theorem GlobalGood_plus_cut (hd : Γ.DotFree)
    (hnb : ∀ b : Fin Γ.comps.length, Γ.comps[b].kind = .G .plus →
      ¬ (Γ.molRep Γ.comps[b].x ∈ Γ.toMG'.MIS ∧ Γ.molRep Γ.comps[b].y ∈ Γ.toMG'.MIS))
    (b : Fin Γ.comps.length) (w : Atom 3 n) (hk : Γ.comps[b].kind = .G .plus)
    (hw : Γ.molRep w ∈ Γ.toMG'.MIS) (hbw : Γ.comps[b].x = w ∨ Γ.comps[b].y = w) :
    Γ.toMG'.Crosses Γ.toMG'.MIS (.inl b) ∧ Γ.toMG'.cls (.inl b) = some .plus := by
  refine GlobalGood_plusCross hd b hk ?_
  have := hnb b hk
  rcases hbw with h | h <;> rw [h] at this ⊢ <;> tauto

/-- Under the hypotheses of [II, Lemma 6.7], `Graph.toMG'` has no proper isolated subset: the
minimal isolated subset would be weakly isolated, with two red solid edges to its complement at
two distinct atoms; each atom carries a blue solid edge, which leaves the minimal isolated subset,
and two such edges are too many for an isolated subset. -/
private theorem GlobalGood_noIso (hN : Γ.Normal C) (hgs : gsPM' Γ) (hd : Γ.DotFree)
    (hM : Γ.MISLocStdB) (hS : ∀ i, ¬ Γ.Step2EdgeB i) :
    ∀ P, ¬ Γ.toMG'.IsProperIso Γ.toMG'.int P := by
  intro P hP
  obtain ⟨⟨hDC, hch, hpre, -⟩, hweak⟩ := hgs
  obtain ⟨hI, hQ⟩ := GlobalGood_mis_iso hch hP
  have hnb := GlobalGood_noBlueIn hd (hpre _ (Or.inr hI.1) hQ) hS
  obtain ⟨-, e, e', hne, hr, hr'⟩ := hweak _ hI
  obtain ⟨i, rfl, hki, hci⟩ := GlobalGood_redCross hd hr
  obtain ⟨j, rfl, hkj, hcj⟩ := GlobalGood_redCross hd hr'
  have hij : i ≠ j := fun h => hne (by rw [h])
  have hend : ∀ c : Comp (Atom 3 n), (Γ.molRep c.x ∈ Γ.toMG'.MIS ∧ Γ.molRep c.y ∉ Γ.toMG'.MIS ∨
      Γ.molRep c.x ∉ Γ.toMG'.MIS ∧ Γ.molRep c.y ∈ Γ.toMG'.MIS) →
      ∃ u, Γ.molRep u ∈ Γ.toMG'.MIS ∧ (c.x = u ∨ c.y = u) := by
    rintro c (⟨h, -⟩ | ⟨-, h⟩)
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  obtain ⟨u, hu, hiu⟩ := hend _ hci
  obtain ⟨v, hv, hjv⟩ := hend _ hcj
  have huv : u ≠ v := by
    rintro rfl
    exact GlobalGood_two_minus hN hM u hu i j hij hki hiu hkj hjv
  obtain ⟨b, hbk, hbu⟩ := GlobalGood_plus_of_minus hN hM u hu _ (List.getElem_mem _) hki hiu
  obtain ⟨b', hbk', hbv⟩ := GlobalGood_plus_of_minus hN hM v hv _ (List.getElem_mem _) hkj hjv
  have hbb : b ≠ b' := by
    rintro rfl
    apply hnb b hbk
    rcases hbu with h1 | h1 <;> rcases hbv with h2 | h2
    · exact absurd (h1.symm.trans h2) huv
    · rw [h1, h2]; exact ⟨hu, hv⟩
    · rw [h1, h2]; exact ⟨hv, hu⟩
    · exact absurd (h1.symm.trans h2) huv
  obtain ⟨hcr, hcl⟩ := GlobalGood_plus_cut hd hnb b u hbk hu hbu
  obtain ⟨hcr', hcl'⟩ := GlobalGood_plus_cut hd hnb b' v hbk' hv hbv
  exact hbb (Sum.inl_injective (GlobalGood_isolated_blue hDC hI hcr hcl hcr' hcl'))

/-- Under the hypotheses of [II, Lemma 6.7] and without proper isolated subsets, every blue solid
edge at an internal atom `w` is `G_{w⊕}`. -/
private theorem GlobalGood_blue_ext (hC : Γ.ColourInv')
    (hin : ∀ w : Atom 3 n, w.isRight = true → Γ.molRep w ∈ Γ.toMG'.MIS)
    (hnb : ∀ b : Fin Γ.comps.length, Γ.comps[b].kind = .G .plus →
      ¬ (Γ.molRep Γ.comps[b].x ∈ Γ.toMG'.MIS ∧ Γ.molRep Γ.comps[b].y ∈ Γ.toMG'.MIS))
    (b : Fin Γ.comps.length) (w : Atom 3 n) (hw : w.isRight = true)
    (hk : Γ.comps[b].kind = .G .plus) (hbw : Γ.comps[b].x = w ∨ Γ.comps[b].y = w) :
    Γ.comps[b].x = w ∧ Γ.comps[b].y = .inl 1 := by
  have hr : Γ.comps[b].kind.isRandom = true := by rw [hk]; rfl
  obtain ⟨hx, hy0, -, hy2⟩ := (hC _ (List.getElem_mem _)).1 hr
  have hyl : Γ.comps[b].y.isRight = false := by
    by_contra h
    exact hnb b hk ⟨hin _ hx, hin _ (by simpa using h)⟩
  have hxw : Γ.comps[b].x = w := by
    rcases hbw with h | h
    · exact h
    · rw [h, hw] at hyl; exact absurd hyl (by simp)
  refine ⟨hxw, ?_⟩
  revert hy0 hy2 hyl
  rcases Γ.comps[b].y with a | a
  · intro hy0 hy2 _
    fin_cases a
    · exact absurd rfl hy0
    · rfl
    · exact absurd (hk.symm.trans (hy2 rfl)) (by simp)
  · intro _ _ hyl; simp at hyl

/-- Under the hypotheses of [II, Lemma 6.7] and without proper isolated subsets, the maximal
subgraph is deterministic: no weight lies on an internal atom (`Graph.MISLocStdB`, `Graph.Plain`),
a blue solid edge between internal atoms would be chosen by Step 2, and a red solid edge between
internal atoms `u`, `v` gives the two blue solid edges `G_{u⊕}`, `G_{v⊕}` at the unpinned `⊕`. -/
private theorem GlobalGood_maxDet (hN : Γ.Normal C) (hgs : gsPM' Γ) (hd : Γ.DotFree)
    (hC : Γ.ColourInv') (hE : Γ.ExtClause) (hM : Γ.MISLocStdB) (hS : ∀ i, ¬ Γ.Step2EdgeB i)
    (hP : Γ.Plain) (hex : ∀ P, ¬ Γ.toMG'.IsProperIso Γ.toMG'.int P) : Γ.MaxDeterministic := by
  obtain ⟨⟨-, -, hpre, -⟩, -⟩ := hgs
  have hmis := GlobalGood_mis_int hex
  have hnb := GlobalGood_noBlueIn hd (hpre _ (Or.inl hmis) (by rw [hmis]; exact hex)) hS
  have hin : ∀ w : Atom 3 n, w.isRight = true → Γ.molRep w ∈ Γ.toMG'.MIS := by
    rintro (a | a) h
    · simp at h
    · rw [hmis]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  intro c hc hrand
  obtain ⟨hx, -, -, -⟩ := (hC c hc).1 hrand
  obtain ⟨a, ha⟩ : ∃ a, c.x = .inr a := by
    revert hx
    rcases c.x with a | a
    · simp
    · exact fun _ => ⟨a, rfl⟩
  have hwt : ∀ ch, (c.kind = .weight ch ∨ c.kind = .light ch) → False := by
    intro ch hk
    have h0 := (hM.2 a (hin _ rfl)).1
    have : 0 < Γ.wt (.inr a) := by
      unfold Graph.wt
      refine List.length_pos_iff_exists_mem.2 ⟨c, List.mem_filter.2 ⟨hc, ?_⟩⟩
      rcases hk with hk | hk <;> simp [hk, ha]
    omega
  rcases GlobalGood_isRandom hrand with ⟨ch, hk⟩ | ⟨ch, hk⟩ | ⟨ch, hk⟩ | ⟨ch, hk⟩ | ⟨ch, D', hk⟩
  · by_contra hcon
    simp only [not_or] at hcon
    have hy : c.y.isRight = true := by simpa using hcon.2
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    cases ch with
    | plus => exact hnb ⟨i, hi⟩ hk ⟨hin _ hx, hin _ hy⟩
    | minus =>
      have hxy := hN.2.1 _ hc (by rw [hk]; rfl)
      obtain ⟨b, hbk, hbu⟩ := GlobalGood_plus_of_minus hN hM _ (hin _ hx) _ hc hk (Or.inl rfl)
      obtain ⟨b', hbk', hbv⟩ := GlobalGood_plus_of_minus hN hM _ (hin _ hy) _ hc hk (Or.inr rfl)
      obtain ⟨hb1, hb2⟩ := GlobalGood_blue_ext hC hin hnb b _ hx hbk hbu
      obtain ⟨hb1', hb2'⟩ := GlobalGood_blue_ext hC hin hnb b' _ hy hbk' hbv
      have hmem : ∀ b : Fin Γ.comps.length, Γ.comps[b].y = .inl 1 →
          Γ.comps[b].kind = .G .plus → Γ.comps[b] ∈ Γ.comps.filter fun c =>
            decide ((c.x = .inl 1 ∨ c.y = .inl 1) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot) := by
        intro b hb hk'
        have hb' : Γ.comps[(b : ℕ)].y = .inl 1 := hb
        have hk'' : Γ.comps[(b : ℕ)].kind = .G .plus := hk'
        refine List.mem_filter.2 ⟨List.getElem_mem _, ?_⟩
        simp [hb', hk'']
      have hle : Γ.nonDotDeg (.inl 1) ≤ 1 := (hE.2.2.2.2 (GlobalGood_unpinned hd 1)).2.2
      have := GlobalGood_eq_of_length_le_one hle (hmem b hb2 hbk) (hmem b' hb2' hbk')
      exact hxy (hb1.symm.trans ((congrArg Comp.x this).trans hb1'))
  · exact (hwt ch (Or.inl hk)).elim
  · exact (hwt ch (Or.inr hk)).elim
  · exact absurd hk ((hP c hc).2.1 ch)
  · exact absurd hk ((hP c hc).2.2.1 ch D')

/-! ### The statement -/

/-- **[II, Lemma 6.7]** in the block reading, on graphs of the form `Graph.Plain`. -/
theorem nonstopB' : nonstopStmtB' := by
  intro n₀ C Γ hN hgs hCB hE hT hM hR hS hP
  have hd := GlobalGood_dotFree hN hE hT hR hP
  have hex := GlobalGood_noIso hN hgs hd hM hS
  exact ⟨hex, GlobalGood_maxDet hN hgs hd (GlobalGood_colourInv' hd hCB) hE hM hS hP hex⟩

end Nonstop

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end Instances

end RBM8D.Graphs
