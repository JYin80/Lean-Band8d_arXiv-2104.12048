import RBM8D.Graph.MolDot

/-!
# The Schur-complement steps of the `Q`-expansions in the block reading

The molecular graph in the block reading of every term of the Schur-complement expansions
[II, (4.17), (4.20)] of a solid edge or a weight, on a graph with the invariant `Graph.InvB'`, is
carried from that of the graph.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Graphs with the same waved and dotted edges -/

section Same

variable {k n : ℕ}

/-- The ends of the edge of the component `d` in `Graph.toMG'` of `Γ`. -/
private def FlatSchur_ends (Γ : Graph k n) (d : Comp (Atom k n)) : Atom k n × Atom k n :=
  (Γ.molRep (Γ.flatComp d).x, Γ.molRep (Γ.flatComp d).y)

/-- The class of the edge of the component `d` in `Graph.toMG'` of `Γ`. -/
private def FlatSchur_cls (Γ : Graph k n) (d : Comp (Atom k n)) : Option MClass :=
  if (Γ.flatComp d).kind = .dot ∨ Γ.molRep (Γ.flatComp d).x = Γ.molRep (Γ.flatComp d).y then none
  else (Γ.flatComp d).kind.mclass

/-- Two graphs with the same waved and dotted edges have the same dotted graph and the same
molecular graph on the atoms. -/
private theorem FlatSchur_graphs {Γ Γ' : Graph k n}
    (h : ∀ d, d.kind.joinsMol = true → (d ∈ Γ'.comps ↔ d ∈ Γ.comps)) :
    Γ'.dotGraph = Γ.dotGraph ∧ Γ'.molGraph = Γ.molGraph := by
  have hd : ∀ u v, (∃ c ∈ Γ'.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ↔
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) := by
    intro u v
    constructor
    · rintro ⟨c, hc, hk, hx, hy⟩
      exact ⟨c, (h c (by rw [hk]; rfl)).1 hc, hk, hx, hy⟩
    · rintro ⟨c, hc, hk, hx, hy⟩
      exact ⟨c, (h c (by rw [hk]; rfl)).2 hc, hk, hx, hy⟩
  have hm : ∀ u v, (∃ c ∈ Γ'.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ↔
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) := by
    intro u v
    constructor
    · rintro ⟨c, hc, hk, hx, hy⟩
      exact ⟨c, (h c hk).1 hc, hk, hx, hy⟩
    · rintro ⟨c, hc, hk, hx, hy⟩
      exact ⟨c, (h c hk).2 hc, hk, hx, hy⟩
  constructor
  · ext u v
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj, hd]
  · ext u v
    simp only [Graph.molGraph, SimpleGraph.fromRel_adj, hm]

/-- Two graphs with the same waved and dotted edges have the same least internal atoms of the
blocks, the same molecule representatives and the same block normal form of every component. -/
private theorem FlatSchur_fun {Γ Γ' : Graph k n}
    (h : ∀ d, d.kind.joinsMol = true → (d ∈ Γ'.comps ↔ d ∈ Γ.comps)) :
    Γ'.anchor = Γ.anchor ∧ Γ'.molRep = Γ.molRep ∧ Γ'.flatAtom = Γ.flatAtom ∧
      Γ'.flatComp = Γ.flatComp := by
  obtain ⟨hd, hm⟩ := FlatSchur_graphs h
  have hb : ∀ u v, Γ'.SameBlock u v ↔ Γ.SameBlock u v := by
    intro u v
    unfold Graph.SameBlock
    rw [hd]
  have hM : ∀ u v, Γ'.SameMol u v ↔ Γ.SameMol u v := by
    intro u v
    unfold Graph.SameMol
    rw [hm]
  have ha : Γ'.anchor = Γ.anchor := by
    funext u
    unfold Graph.anchor
    congr 1
    funext b
    exact decide_eq_decide.2 (hb _ _)
  have hr : Γ'.molRep = Γ.molRep := by
    funext u
    cases u with
    | inl a => rfl
    | inr a =>
      simp only [Graph.molRep]
      congr 3
      funext b
      exact decide_eq_decide.2 (hM _ _)
  have hf : Γ'.flatAtom = Γ.flatAtom := by
    funext u
    cases u with
    | inl a => simp only [Graph.flatAtom, ha]
    | inr a => rfl
  refine ⟨ha, hr, hf, ?_⟩
  funext d
  simp only [Graph.flatComp, hf]

/-- `Graph.toMG'` of a graph with the waved and dotted edges of `Γ`, read with the functions of
`Γ`: the same vertices and edges `.inr a`, and the edge of each component read in `Γ`. -/
private theorem FlatSchur_toMG' {Γ Γ' : Graph k n}
    (h : ∀ d, d.kind.joinsMol = true → (d ∈ Γ'.comps ↔ d ∈ Γ.comps)) :
    Γ'.toMG'.int = Γ.toMG'.int ∧ Γ'.toMG'.ext = Γ.toMG'.ext ∧
      (∀ a, Γ'.toMG'.ends (.inr a) = Γ.toMG'.ends (.inr a)) ∧
      (∀ a, Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a)) ∧
      (∀ j : Fin Γ'.comps.length, Γ'.toMG'.ends (.inl j) = FlatSchur_ends Γ Γ'.comps[j]) ∧
      (∀ j : Fin Γ'.comps.length, Γ'.toMG'.cls (.inl j) = FlatSchur_cls Γ Γ'.comps[j]) := by
  obtain ⟨ha, hr, -, hf⟩ := FlatSchur_fun h
  refine ⟨?_, rfl, fun a => ?_, fun a => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [Graph.toMG', hr]
  · simp only [Graph.toMG', ha, hr]
  · simp only [Graph.toMG', ha]
  · simp only [Graph.toMG', FlatSchur_ends, hr, hf]
  · simp only [Graph.toMG', FlatSchur_cls, hr, hf]

/-- The edge of a component in `Graph.toMG'`. -/
private theorem FlatSchur_self (Γ : Graph k n) (j : Fin Γ.comps.length) :
    Γ.toMG'.ends (.inl j) = FlatSchur_ends Γ Γ.comps[j] ∧
      Γ.toMG'.cls (.inl j) = FlatSchur_cls Γ Γ.comps[j] :=
  ⟨rfl, rfl⟩

/-- The representative of the molecule of an atom is a vertex of `Graph.toMG'`. -/
private theorem FlatSchur_vtx (Γ : Graph k n) (u : Atom k n) : Γ.toMG'.IsVtx (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  | inr b => exact Or.inl (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)

/-- The representative of the molecule of an internal atom is an internal vertex. -/
private theorem FlatSchur_int (Γ : Graph k n) {u : Atom k n} (hu : u.isRight = true) :
    Γ.molRep u ∈ Γ.toMG'.int := by
  cases u with
  | inl a => simp at hu
  | inr b => exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩

/-- The present edges of `Graph.toMG'` join vertices. -/
private theorem FlatSchur_pv (Γ : Graph k n) :
    ∀ e, Γ.toMG'.cls e ≠ none →
      Γ.toMG'.IsVtx (Γ.toMG'.ends e).1 ∧ Γ.toMG'.IsVtx (Γ.toMG'.ends e).2 := by
  rintro (j | a) h
  · exact ⟨FlatSchur_vtx _ _, FlatSchur_vtx _ _⟩
  · revert h
    simp only [Graph.toMG']
    split
    · rename_i b _
      intro _
      exact ⟨FlatSchur_vtx Γ (.inr b), Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)⟩
    · intro h
      exact absurd rfl h

end Same

/-! ## Changes of names and chains of operations -/

section Chain

variable {V E : Type}

/-- A molecular multigraph with the vertices and the classes of the edges of `H`, and the ends of
the present edges of `H`, is transported onto `H`. -/
private theorem FlatSchur_tr_id [DecidableEq V] (G H : MGraph V E) (hi : G.int = H.int)
    (he : G.ext = H.ext) (hc : ∀ e, G.cls e = H.cls e)
    (hn : ∀ e, H.cls e ≠ none → G.ends e = H.ends e)
    (hv : ∀ e, H.cls e ≠ none → H.IsVtx (H.ends e).1 ∧ H.IsVtx (H.ends e).2) :
    G.Transported H := by
  refine ⟨id, id, fun _ _ _ _ h => h, Set.injOn_id _, by rw [hi, Finset.image_id],
    by rw [he, Finset.image_id], fun e h => ?_, fun e _ => (hc e).symm,
    fun e h => Or.inl ?_, fun e' h' => ?_⟩
  · rw [hc] at h
    rw [hn e h]
    simp only [MGraph.IsVtx, hi, he]
    exact hv e h
  · rw [hc] at h
    rw [hn e h]
    rfl
  · by_contra hne
    exact h' e' (by rw [hc]; exact hne) rfl

/-- The operations (B) and (Loop) on the path `A – X – B`: an edge `s₁` from `A` to `B` of class
`m` (absent if `A = B`) and an absent edge `s₂` become the edges `s₁` from `A` to `X` and `s₂`
from `X` to `B` of class `m` (each absent if its ends are equal), for a blue or red class `m`,
with `A` and `X` internal. -/
private theorem FlatSchur_chain [DecidableEq V] [DecidableEq E] (H : MGraph V E) (s₁ s₂ : E)
    (hs : s₁ ≠ s₂) (A B X : V) (m : MClass) (hm : m = .plus ∨ m = .minus)
    (hA : A ∈ H.int) (hB : H.IsVtx B) (hX : X ∈ H.int)
    (h₁ : H.ends s₁ = (A, X)) (h₁c : H.cls s₁ = if A = X then none else some m)
    (h₂ : H.ends s₂ = (X, B)) (h₂c : H.cls s₂ = if X = B then none else some m) :
    ∃ G₁, Relation.ReflTransGen MGraph.CarStep
        ((H.erase s₂).setEdge s₁ A B (if A = B then none else some m)) G₁ ∧
      G₁.int = H.int ∧ G₁.ext = H.ext ∧ (∀ e, G₁.cls e = H.cls e) ∧
      ∀ e, H.cls e ≠ none → G₁.ends e = H.ends e := by
  have hs' : s₂ ≠ s₁ := fun h => hs h.symm
  rcases hm with rfl | rfl
  · by_cases hAB : A = B
    · subst hAB
      by_cases hAX : A = X
      · subst hAX
        refine ⟨_, .refl, rfl, rfl, fun e => ?_, fun e he => ?_⟩
        · by_cases e1 : e = s₁
          · subst e1; simp [MGraph.setEdge, h₁c]
          · by_cases e2 : e = s₂
            · subst e2; simp [MGraph.setEdge, MGraph.erase, h₂c, hs']
            · simp [MGraph.setEdge, MGraph.erase, e1, e2]
        · have e1 : e ≠ s₁ := by rintro rfl; simp [h₁c] at he
          simp [MGraph.setEdge, MGraph.erase, e1]
      · refine ⟨_, .tail (.single (.loop _ s₁ A (by simp [MGraph.setEdge]) hA))
          (.split _ s₁ s₂ X (by simp [MGraph.setEdge]) (by simp [MGraph.setEdge, MGraph.IsVtx, hA])
            (by simp [MGraph.setEdge, MGraph.IsVtx, hA]) (by simp [MGraph.setEdge, hA]) hs
            (by simp [MGraph.setEdge, MGraph.erase, hs']) hX), rfl, rfl, fun e => ?_,
          fun e _ => ?_⟩
        · by_cases e1 : e = s₂
          · subst e1; simp [MGraph.split, MGraph.setEdge, h₂c, Ne.symm hAX]
          · by_cases e2 : e = s₁
            · subst e2; simp [MGraph.split, MGraph.setEdge, h₁c, hAX, hs]
            · simp [MGraph.split, MGraph.setEdge, MGraph.erase, e1, e2]
        · by_cases e1 : e = s₁
          · subst e1; simp [MGraph.split, MGraph.setEdge, h₁]
          · by_cases e2 : e = s₂
            · subst e2; simp [MGraph.split, MGraph.setEdge, h₂, hs']
            · simp [MGraph.split, MGraph.setEdge, MGraph.erase, e1, e2]
    · have hsp : MGraph.CarStep ((H.erase s₂).setEdge s₁ A B (if A = B then none else some .plus))
          ((((H.erase s₂).setEdge s₁ A B
            (if A = B then none else some .plus))).split s₁ s₂ X) :=
        .split _ s₁ s₂ X (by simp [MGraph.setEdge, hAB])
          (by simp [MGraph.setEdge, MGraph.IsVtx, hA])
          (by simpa [MGraph.setEdge, MGraph.IsVtx] using hB) (by simp [MGraph.setEdge, hA]) hs
          (by simp [MGraph.setEdge, MGraph.erase, hs']) hX
      by_cases hXA : X = A
      · subst hXA
        refine ⟨_, .tail (.single hsp)
          (.unloop _ s₁ (by simp [MGraph.split, MGraph.setEdge, hAB, hs])
            (by simp [MGraph.split, MGraph.setEdge])), rfl, rfl, fun e => ?_, fun e he => ?_⟩
        · by_cases e1 : e = s₁
          · subst e1; simp [MGraph.erase, h₁c]
          · by_cases e2 : e = s₂
            · subst e2; simp [MGraph.erase, MGraph.split, MGraph.setEdge, h₂c, hAB, hs']
            · simp [MGraph.erase, MGraph.split, MGraph.setEdge, e1, e2]
        · have e1 : e ≠ s₁ := by rintro rfl; simp [h₁c] at he
          by_cases e2 : e = s₂
          · subst e2; simp [MGraph.erase, MGraph.split, MGraph.setEdge, h₂, hs']
          · simp [MGraph.erase, MGraph.split, MGraph.setEdge, e1, e2]
      · by_cases hXB : X = B
        · subst hXB
          refine ⟨_, .tail (.single hsp) (.unloop _ s₂
            (by simp [MGraph.split, MGraph.setEdge, hAB])
            (by simp [MGraph.split, MGraph.setEdge, hs'])), rfl, rfl, fun e => ?_, fun e he => ?_⟩
          · by_cases e1 : e = s₂
            · subst e1; simp [MGraph.erase, h₂c]
            · by_cases e2 : e = s₁
              · subst e2; simp [MGraph.erase, MGraph.split, MGraph.setEdge, h₁c, hAB, hs]
              · simp [MGraph.erase, MGraph.split, MGraph.setEdge, e1, e2]
          · have e1 : e ≠ s₂ := by rintro rfl; simp [h₂c] at he
            by_cases e2 : e = s₁
            · subst e2; simp [MGraph.erase, MGraph.split, MGraph.setEdge, h₁]
            · simp [MGraph.erase, MGraph.split, MGraph.setEdge, e1, e2]
        · refine ⟨_, .single hsp, rfl, rfl, fun e => ?_, fun e _ => ?_⟩
          · by_cases e1 : e = s₂
            · subst e1; simp [MGraph.split, MGraph.setEdge, h₂c, hAB, hXB]
            · by_cases e2 : e = s₁
              · subst e2; simp [MGraph.split, MGraph.setEdge, h₁c, hAB, Ne.symm hXA, hs]
              · simp [MGraph.split, MGraph.setEdge, MGraph.erase, e1, e2]
          · by_cases e1 : e = s₁
            · subst e1; simp [MGraph.split, MGraph.setEdge, h₁]
            · by_cases e2 : e = s₂
              · subst e2; simp [MGraph.split, MGraph.setEdge, h₂, hs']
              · simp [MGraph.split, MGraph.setEdge, MGraph.erase, e1, e2]
  · refine ⟨_, .tail (.single (.red _ s₁ A X (if A = X then none else some .minus)
      (by by_cases hAB : A = B <;> simp [MGraph.setEdge, hAB])
      (by by_cases hAX : A = X <;> simp [hAX])))
      (.red _ s₂ X B (if X = B then none else some .minus)
        (by simp [MGraph.setEdge, MGraph.erase, hs'])
        (by by_cases hXB : X = B <;> simp [hXB])), rfl, rfl, fun e => ?_, fun e _ => ?_⟩
    · by_cases e1 : e = s₂
      · subst e1; simp [MGraph.setEdge, h₂c]
      · by_cases e2 : e = s₁
        · subst e2; simp [MGraph.setEdge, h₁c, hs]
        · simp [MGraph.setEdge, MGraph.erase, e1, e2]
    · by_cases e1 : e = s₂
      · subst e1; simp [MGraph.setEdge, h₂]
      · by_cases e2 : e = s₁
        · subst e2; simp [MGraph.setEdge, h₁, hs]
        · simp [MGraph.setEdge, MGraph.erase, e1, e2]

end Chain

/-! ## The components of the terms -/

section Terms

variable {n : ℕ}

/-- The position of the component `j` of a graph in a term of the expansion at the component `i`:
the components other than `i` keep their order and the component `i` is last among them. -/
private def FlatSchur_pos (i L j : ℕ) : ℕ := if j < i then j else if j = i then L - 1 else j - 1

/-- The map of the edges of `Graph.toMG'` that sends the component `j` to the position
`FlatSchur_pos i L j` and every edge `.inr a` to itself. -/
private def FlatSchur_sig (i L N : ℕ) : Fin L ⊕ Fin 3 → Fin N ⊕ Fin 3
  | .inl j => if h : FlatSchur_pos i L j < N then .inl ⟨_, h⟩ else .inr 0
  | .inr a => .inr a

/-- A molecular multigraph `G` that has the vertices and the edges `.inr a` of `Graph.toMG'` of
`Γ`, the edge of the component `j` of `Γ` at the position `FlatSchur_pos i L j`, and only absent
edges at the other positions, is a change of names of `Graph.toMG'` of `Γ`. -/
private theorem FlatSchur_reix {Γ : Graph 3 n} {N : ℕ} (i : ℕ) (hi : i < Γ.comps.length)
    (hN : Γ.comps.length ≤ N) (G : MGraph (Atom 3 n) (Fin N ⊕ Fin 3))
    (hint : G.int = Γ.toMG'.int) (hext : G.ext = Γ.toMG'.ext)
    (hpc : ∀ a, G.cls (.inr a) = Γ.toMG'.cls (.inr a))
    (hpe : ∀ a, Γ.toMG'.cls (.inr a) ≠ none → G.ends (.inr a) = Γ.toMG'.ends (.inr a))
    (hc : ∀ (j : Fin Γ.comps.length) (h : FlatSchur_pos i Γ.comps.length j < N),
      G.cls (.inl ⟨_, h⟩) = Γ.toMG'.cls (.inl j))
    (he : ∀ (j : Fin Γ.comps.length) (h : FlatSchur_pos i Γ.comps.length j < N),
      Γ.toMG'.cls (.inl j) ≠ none → G.ends (.inl ⟨_, h⟩) = Γ.toMG'.ends (.inl j))
    (hout : ∀ k : Fin N, Γ.comps.length ≤ k → G.cls (.inl k) = none) :
    Γ.toMG'.Transported G := by
  set L := Γ.comps.length
  have hlt : ∀ j : Fin L, FlatSchur_pos i L j < N := by
    intro j
    have := j.2
    unfold FlatSchur_pos
    split_ifs <;> omega
  have hsig : ∀ j : Fin L, FlatSchur_sig i L N (.inl j) = .inl ⟨_, hlt j⟩ := by
    intro j
    simp [FlatSchur_sig, hlt j]
  refine ⟨id, FlatSchur_sig i L N, ?_, Set.injOn_id _, by rw [hint, Finset.image_id],
    by rw [hext, Finset.image_id], FlatSchur_pv Γ, ?_, ?_, ?_⟩
  · rintro (j₁ | a₁) (j₂ | a₂) - - h
    · rw [hsig, hsig] at h
      have h' : FlatSchur_pos i L j₁ = FlatSchur_pos i L j₂ := by
        simpa using h
      have h1 := j₁.2
      have h2 := j₂.2
      congr 1
      ext
      unfold FlatSchur_pos at h'
      split_ifs at h' <;> omega
    · rw [hsig] at h
      simp [FlatSchur_sig] at h
    · rw [hsig] at h
      simp [FlatSchur_sig] at h
    · simpa [FlatSchur_sig] using h
  · rintro (j | a) h
    · rw [hsig, hc]
    · exact hpc a
  · rintro (j | a) h
    · left
      rw [hsig, he j _ h]
      rfl
    · left
      rw [show FlatSchur_sig i L N (.inr a) = .inr a from rfl, hpe a h]
      rfl
  · rintro (k | a) h'
    · by_cases hk : (k : ℕ) < L
      · set j : ℕ := if (k : ℕ) < i then k else if (k : ℕ) = L - 1 then i else k + 1 with hj
        have hjL : j < L := by
          rw [hj]
          split_ifs <;> omega
        have hpj : FlatSchur_pos i L j = k := by
          rw [hj]
          unfold FlatSchur_pos
          split_ifs <;> omega
        have hn : Γ.toMG'.cls (.inl ⟨j, hjL⟩) = none := by
          by_contra hne
          exact h' (.inl ⟨j, hjL⟩) hne (by rw [hsig]; congr 1; ext; exact hpj)
        rw [← hn, ← hc ⟨j, hjL⟩ (hlt _)]
        congr 2
        ext
        exact hpj.symm
      · exact hout k (by omega)
    · rw [hpc]
      by_contra hne
      exact h' (.inr a) hne rfl

/-- The edge in `Graph.toMG'` of a component that is neither a waved nor a dotted edge: from the
molecule of the block normal form of its first atom to that of its second atom, absent if the two
molecules are equal. -/
private theorem FlatSchur_nd (Γ : Graph 3 n) {d : Comp (Atom 3 n)} (hd : d.kind.joinsMol = false) :
    FlatSchur_ends Γ d = (Γ.molRep (Γ.flatAtom d.x), Γ.molRep (Γ.flatAtom d.y)) ∧
      FlatSchur_cls Γ d = if Γ.molRep (Γ.flatAtom d.x) = Γ.molRep (Γ.flatAtom d.y) then none
        else d.kind.mclass := by
  have hk : d.kind ≠ .dot := by
    intro h
    rw [h] at hd
    exact absurd hd (by decide)
  simp [FlatSchur_ends, FlatSchur_cls, Graph.flatComp, hk]

/-- The components of `l` other than its waved and dotted edges may be replaced by components of
`t` that are neither waved nor dotted edges. -/
private theorem FlatSchur_mem {l t : List (Comp (Atom 3 n))} {i : ℕ} (hi : i < l.length)
    (hj : l[i].kind.joinsMol = false) (ht : ∀ d ∈ t, d.kind.joinsMol = false) :
    ∀ d, d.kind.joinsMol = true → (d ∈ l.eraseIdx i ++ t ↔ d ∈ l) := by
  intro d hd
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_of_mem_eraseIdx h
    · rw [ht d h] at hd
      exact absurd hd (by decide)
  · intro h
    obtain ⟨j, hj', rfl⟩ := List.mem_iff_getElem.1 h
    refine List.mem_append_left _ (List.mem_eraseIdx_iff_getElem.2 ⟨j, hj', fun hji => ?_, rfl⟩)
    subst hji
    rw [hj] at hd
    exact absurd hd (by decide)

/-- The component of a term at the position of the component `j ≠ i` is that component. -/
private theorem FlatSchur_get {l t l' : List (Comp (Atom 3 n))} {i j : ℕ}
    (hl : l' = l.eraseIdx i ++ t) (hi : i < l.length) (hj : j < l.length) (hji : j ≠ i)
    (h : FlatSchur_pos i l.length j < l'.length) : l'[FlatSchur_pos i l.length j] = l[j] := by
  have hlen := List.length_eraseIdx_of_lt hi
  have hp : FlatSchur_pos i l.length j < (l.eraseIdx i).length := by
    rw [hlen]
    unfold FlatSchur_pos
    split_ifs <;> omega
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
  subst hl
  rw [List.getElem?_append_left hp, List.getElem?_eraseIdx]
  unfold FlatSchur_pos
  by_cases h₁ : j < i
  · simp [h₁]
  · have h₂ : ¬ j - 1 < i := by omega
    have h₃ : j - 1 + 1 = j := by omega
    simp [h₁, hji, h₂, h₃]

/-- The new components of a term follow the components other than `i`. -/
private theorem FlatSchur_tail {l t l' : List (Comp (Atom 3 n))} {i : ℕ}
    (hl : l' = l.eraseIdx i ++ t) (hi : i < l.length) (m : ℕ) (h : l.length - 1 + m < l'.length)
    (hm : m < t.length) : l'[l.length - 1 + m] = t[m] := by
  have hlen := List.length_eraseIdx_of_lt hi
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
  subst hl
  rw [List.getElem?_append_right (by omega), hlen]
  congr 1
  omega

/-- The block normal form at the term `Γ` with the component `i` replaced at the end by a component
of the same kind and ends (the minor or the coefficient may change): a change of names. -/
private theorem FlatSchur_minor {Γ Γ' : Graph 3 n} {i : ℕ} {c c' : Comp (Atom 3 n)}
    (hc : Γ.comps[i]? = some c) (hj : c.kind.joinsMol = false)
    (hΓ' : Γ'.comps = Γ.comps.eraseIdx i ++ [c'])
    (hk : c'.kind = c.kind) (hx : c'.x = c.x) (hy : c'.y = c.y) : Γ.FlatCarried Γ' := by
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  have hlen : Γ'.comps.length = Γ.comps.length := by
    rw [hΓ', List.length_append, List.length_eraseIdx_of_lt hi]
    simp only [List.length_singleton]
    omega
  have hsame : ∀ d, d.kind.joinsMol = true → (d ∈ Γ'.comps ↔ d ∈ Γ.comps) := by
    rw [hΓ']
    exact FlatSchur_mem hi (hci ▸ hj) (by simp [hk, hj])
  obtain ⟨hI, hE, hpe, hpc, hends, hcls⟩ := FlatSchur_toMG' hsame
  have hj' : c'.kind.joinsMol = false := hk ▸ hj
  have hcomp : ∀ (j : Fin Γ.comps.length) (h : FlatSchur_pos i Γ.comps.length j < Γ'.comps.length),
      FlatSchur_ends Γ Γ'.comps[FlatSchur_pos i Γ.comps.length j] = FlatSchur_ends Γ Γ.comps[j] ∧
      FlatSchur_cls Γ Γ'.comps[FlatSchur_pos i Γ.comps.length j] = FlatSchur_cls Γ Γ.comps[j] := by
    intro j h
    by_cases hji : (j : ℕ) = i
    · have hp : FlatSchur_pos i Γ.comps.length j = Γ.comps.length - 1 + 0 := by
        simp [FlatSchur_pos, hji]
      have h' : Γ'.comps[FlatSchur_pos i Γ.comps.length j] = c' := by
        simp only [hp]
        exact FlatSchur_tail hΓ' hi 0 (by omega) (by simp)
      have hj'' : Γ.comps[j] = c := by
        obtain ⟨j, hjL⟩ := j
        simp only at hji
        subst hji
        exact hci
      rw [h', hj'', (FlatSchur_nd Γ hj').1, (FlatSchur_nd Γ hj').2, (FlatSchur_nd Γ hj).1,
        (FlatSchur_nd Γ hj).2, hk, hx, hy]
      exact ⟨rfl, rfl⟩
    · rw [FlatSchur_get hΓ' hi j.2 hji h]
      exact ⟨rfl, rfl⟩
  exact MolDot_flatCarried_of_transported (FlatSchur_reix i hi (by omega) Γ'.toMG' hI hE hpc
    (fun a _ => hpe a) (fun j h => by rw [hcls]; exact (hcomp j h).2)
    (fun j h _ => by rw [hends]; exact (hcomp j h).1) (fun k hk => absurd k.2 (by omega)))

/-- The block normal form at the term of [II, (4.17), (4.20)] in which the component `i` (a solid
edge from `a` to `q`, or a weight on `a` with `q = a`) is replaced by the components `c₁` from `a`
to the internal atom `x`, `c₂` from `x` to `q` (each a solid edge of charge `ch` unless its ends are
equal) and `c₃` (no edge of the molecular graph), when the block normal form of `a` is internal:
operation (B), preceded by a blue solid loop when the input edge is absent, or two moves of red
edges, then the removal of loops. -/
private theorem FlatSchur_main {Γ Γ' : Graph 3 n} {i : ℕ} {c : Comp (Atom 3 n)}
    (hc : Γ.comps[i]? = some c) {b : Fin n} (ch : Charge) (q : Atom 3 n)
    (hcase : (c.kind = .G ch ∧ q = c.y) ∨ (c.kind.mclass = none ∧ q = c.x))
    (hj : c.kind.joinsMol = false) (hcx : (Γ.flatAtom c.x).isRight = true)
    {c₁ c₂ c₃ : Comp (Atom 3 n)} (hΓ' : Γ'.comps = Γ.comps.eraseIdx i ++ [c₁, c₂, c₃])
    (h₁x : c₁.x = c.x) (h₁y : c₁.y = .inr b) (h₁k : c₁.x ≠ c₁.y → c₁.kind = .G ch)
    (h₁j : c₁.kind.joinsMol = false)
    (h₂x : c₂.x = .inr b) (h₂y : c₂.y = q) (h₂k : c₂.x ≠ c₂.y → c₂.kind = .G ch)
    (h₂j : c₂.kind.joinsMol = false)
    (h₃j : c₃.kind.joinsMol = false) (h₃m : c₃.kind.mclass = none) :
    Γ.FlatCarried Γ' := by
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  set L := Γ.comps.length with hL
  have hlen : Γ'.comps.length = L + 2 := by
    rw [hΓ', List.length_append, List.length_eraseIdx_of_lt hi]
    simp only [List.length_cons, List.length_nil]
    omega
  have hsame : ∀ d, d.kind.joinsMol = true → (d ∈ Γ'.comps ↔ d ∈ Γ.comps) := by
    rw [hΓ']
    exact FlatSchur_mem hi (hci ▸ hj) (by simp [h₁j, h₂j, h₃j])
  obtain ⟨hI, hE, hpe, hpc, hends, hcls⟩ := FlatSchur_toMG' hsame
  obtain ⟨m, hm, hmm⟩ : ∃ m, (Kind.G ch).mclass = some m ∧ (m = .plus ∨ m = .minus) := by
    cases ch <;> simp [Kind.mclass]
  set A := Γ.molRep (Γ.flatAtom c.x) with hA
  set X := Γ.molRep (.inr b) with hX
  set B := Γ.molRep (Γ.flatAtom q) with hB
  let p₁ : Fin Γ'.comps.length := ⟨L - 1 + 0, by omega⟩
  let p₂ : Fin Γ'.comps.length := ⟨L - 1 + 1, by omega⟩
  let p₃ : Fin Γ'.comps.length := ⟨L - 1 + 2, by omega⟩
  have g₁ : Γ'.comps[p₁] = c₁ := FlatSchur_tail hΓ' hi 0 _ (by simp)
  have g₂ : Γ'.comps[p₂] = c₂ := FlatSchur_tail hΓ' hi 1 _ (by simp)
  have g₃ : Γ'.comps[p₃] = c₃ := FlatSchur_tail hΓ' hi 2 _ (by simp)
  set H := Γ'.toMG' with hH
  have e₁ : H.ends (.inl p₁) = (A, X) := by
    rw [hends, g₁, (FlatSchur_nd Γ h₁j).1, h₁x, h₁y]
    rfl
  have c₁c : H.cls (.inl p₁) = if A = X then none else some m := by
    rw [hcls, g₁, (FlatSchur_nd Γ h₁j).2, h₁x, h₁y]
    change (if A = X then none else c₁.kind.mclass) = _
    by_cases hAX : A = X
    · simp [hAX]
    · have hne : c₁.x ≠ c₁.y := by
        intro h
        apply hAX
        rw [hA, ← h₁x, h, h₁y]
        rfl
      simp [hAX, h₁k hne, hm]
  have e₂ : H.ends (.inl p₂) = (X, B) := by
    rw [hends, g₂, (FlatSchur_nd Γ h₂j).1, h₂x, h₂y]
    rfl
  have c₂c : H.cls (.inl p₂) = if X = B then none else some m := by
    rw [hcls, g₂, (FlatSchur_nd Γ h₂j).2, h₂x, h₂y]
    change (if X = B then none else c₂.kind.mclass) = _
    by_cases hXB : X = B
    · simp [hXB]
    · have hne : c₂.x ≠ c₂.y := by
        intro h
        apply hXB
        rw [hB, ← h₂y, ← h, h₂x]
        rfl
      simp [hXB, h₂k hne, hm]
  have c₃c : H.cls (.inl p₃) = none := by
    rw [hcls, g₃, (FlatSchur_nd Γ h₃j).2, h₃m]
    simp
  have c₀c : Γ.toMG'.cls (.inl ⟨i, hi⟩) = if A = B then none else some m := by
    rw [(FlatSchur_self Γ _).2]
    change FlatSchur_cls Γ Γ.comps[i] = _
    rw [hci, (FlatSchur_nd Γ hj).2]
    rcases hcase with ⟨hk, hq⟩ | ⟨hk, hq⟩
    · rw [hk, hm, hB, hq]
    · rw [hk, hB, hq]
      simp [hA]
  have e₀ : Γ.toMG'.cls (.inl ⟨i, hi⟩) ≠ none → Γ.toMG'.ends (.inl ⟨i, hi⟩) = (A, B) := by
    intro h
    rw [(FlatSchur_self Γ _).1]
    change FlatSchur_ends Γ Γ.comps[i] = _
    rw [hci, (FlatSchur_nd Γ hj).1]
    rcases hcase with ⟨hk, hq⟩ | ⟨hk, hq⟩
    · rw [hB, hq]
    · exfalso
      apply h
      rw [c₀c, hB, hq]
      simp [hA]
  have hAi : A ∈ H.int := by
    rw [hI]
    exact FlatSchur_int Γ hcx
  have hXi : X ∈ H.int := by
    rw [hI]
    exact FlatSchur_int Γ rfl
  have hBv : H.IsVtx B := by
    simp only [MGraph.IsVtx, hI, hE]
    exact FlatSchur_vtx Γ _
  have h12 : (Sum.inl p₁ : Fin Γ'.comps.length ⊕ Fin 3) ≠ .inl p₂ := by
    simp [p₁, p₂]
  obtain ⟨G₁, hch, hG₁i, hG₁e, hG₁c, hG₁n⟩ :=
    FlatSchur_chain H (.inl p₁) (.inl p₂) h12 A B X m hmm hAi hBv hXi e₁ c₁c e₂ c₂c
  set G₀ := (H.erase (.inl p₂)).setEdge (.inl p₁) A B (if A = B then none else some m) with hG₀
  have hG₀c : ∀ e, e ≠ .inl p₁ → e ≠ .inl p₂ → G₀.cls e = H.cls e := by
    intro e h1 h2
    simp [hG₀, MGraph.setEdge, MGraph.erase, h1, h2]
  have hG₀e : ∀ e, e ≠ .inl p₁ → G₀.ends e = H.ends e := by
    intro e h1
    simp [hG₀, MGraph.setEdge, MGraph.erase, h1]
  have hpos : ∀ (j : Fin L) (h : FlatSchur_pos i L j < Γ'.comps.length), (j : ℕ) ≠ i →
      (Sum.inl ⟨_, h⟩ : Fin Γ'.comps.length ⊕ Fin 3) ≠ .inl p₁ ∧
        (Sum.inl ⟨_, h⟩ : Fin Γ'.comps.length ⊕ Fin 3) ≠ .inl p₂ := by
    intro j h hji
    have := j.2
    have hlt : FlatSchur_pos i L j < L - 1 := by
      unfold FlatSchur_pos
      split_ifs <;> omega
    constructor <;> intro h' <;> simp [p₁, p₂, Fin.ext_iff] at h' <;> omega
  have hposi : ∀ (j : Fin L) (h : FlatSchur_pos i L j < Γ'.comps.length), (j : ℕ) = i →
      (⟨_, h⟩ : Fin Γ'.comps.length) = p₁ ∧ j = ⟨i, hi⟩ := by
    intro j h hji
    exact ⟨Fin.ext (by simp [p₁, FlatSchur_pos, hji]), Fin.ext hji⟩
  have htr : Γ.toMG'.Transported G₀ := by
    refine FlatSchur_reix i hi (by omega) G₀ hI hE (fun a => ?_) (fun a h => ?_) (fun j h => ?_)
      (fun j h hn => ?_) (fun k hk => ?_)
    · rw [hG₀c _ (by simp) (by simp), hpc]
    · rw [hG₀e _ (by simp), hpe]
    · by_cases hji : (j : ℕ) = i
      · obtain ⟨j, hjL⟩ := j
        simp only at hji
        subst hji
        rw [(hposi _ h rfl).1, c₀c]
        simp [hG₀, MGraph.setEdge]
      · obtain ⟨h1, h2⟩ := hpos j h hji
        rw [hG₀c _ h1 h2, hcls]
        exact congrArg (FlatSchur_cls Γ) (FlatSchur_get hΓ' hi j.2 hji h)
    · by_cases hji : (j : ℕ) = i
      · obtain ⟨j, hjL⟩ := j
        simp only at hji
        subst hji
        rw [(hposi _ h rfl).1, e₀ hn]
        simp [hG₀, MGraph.setEdge]
      · obtain ⟨h1, -⟩ := hpos j h hji
        rw [hG₀e _ h1, hends]
        exact congrArg (FlatSchur_ends Γ) (FlatSchur_get hΓ' hi j.2 hji h)
    · have := k.2
      by_cases hk2 : (k : ℕ) = L - 1 + 1
      · have : k = p₂ := Fin.ext hk2
        subst this
        have h21 : (Sum.inl p₂ : Fin Γ'.comps.length ⊕ Fin 3) ≠ .inl p₁ := fun h => h12 h.symm
        simp only [hG₀, MGraph.setEdge, MGraph.erase]
        rw [Function.update_of_ne h21, Function.update_self]
      · have : k = p₃ := Fin.ext (by simp [p₃]; omega)
        subst this
        rw [hG₀c _ (by simp [p₁, p₃]) (by simp [p₂, p₃]), c₃c]
  exact MolDot_flatCarried_of_chain G₀ G₁ htr hch
    (FlatSchur_tr_id G₁ H hG₁i hG₁e hG₁c hG₁n (FlatSchur_pv Γ'))

/-- `Graph.FlatCarried` is reflexive. -/
private theorem FlatSchur_refl (Γ : Graph 3 n) : Γ.FlatCarried Γ :=
  Relation.ReflTransGen.refl

/-- On a graph with the charge pattern of the block normal form, the block normal form of the
first atom of a random component other than a dotted edge is internal. -/
private theorem FlatSchur_colour {Γ : Graph 3 n} (h : Γ.ColourInvB) {c : Comp (Atom 3 n)}
    {i : ℕ} (hc : Γ.comps[i]? = some c) (hr : c.kind.isRandom = true)
    (hd : c.kind.joinsMol = false) :
    (Γ.flatAtom c.x).isRight = true := by
  have hk : c.kind ≠ .dot := by
    intro h'
    rw [h'] at hd
    exact absurd hd (by decide)
  unfold Graph.ColourInvB Graph.ColourInv' at h
  have hm : Γ.flatComp c ∈ Γ.blockNorm.comps :=
    List.mem_map_of_mem (List.mem_of_getElem? hc)
  have := ((h _ hm).1 (by rw [Graph.flatComp_kind]; exact hr)).1
  simpa [Graph.flatComp, hk] using this

/-- The solid edge or weight `solidC ch u v` runs from `u` to `v`, is a solid edge of charge `ch`
when `u ≠ v`, and is neither a waved nor a dotted edge. -/
private theorem FlatSchur_solidC (ch : Charge) (u v : Atom 3 n) :
    (solidC ch u v).x = u ∧ (solidC ch u v).y = v ∧
      ((solidC ch u v).x ≠ (solidC ch u v).y → (solidC ch u v).kind = .G ch) ∧
      (solidC ch u v).kind.joinsMol = false := by
  unfold solidC
  split_ifs with h
  · subst h
    exact ⟨rfl, rfl, fun h' => absurd rfl h', rfl⟩
  · exact ⟨rfl, rfl, fun _ => rfl, rfl⟩

end Terms

/-! ## The Schur-complement steps -/

/-- The block normal form at [II, (4.17)]: for a solid edge at an internal atom `x` of a graph with
the invariant `Graph.InvB'`, the molecular graph of every term is carried from that of the
graph. -/
theorem qElemStep_schur_flat :
  ∀ (n : ℕ) (x : Atom 3 n) (i : ℕ) (Γ : Graph 3 n), x.isRight = true → Γ.InvB' →
    ∀ t ∈ oSchurT x i Γ, Γ.FlatCarried t.g := by
  intro n x i Γ hx hI t ht
  obtain ⟨b, rfl⟩ : ∃ b, x = .inr b := by
    cases x with
    | inl a => simp at hx
    | inr b => exact ⟨b, rfl⟩
  unfold oSchurT at ht
  split at ht
  · rename_i c hc
    split at ht
    · rename_i ch hk
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact FlatSchur_minor hc (by rw [hk]; rfl) rfl rfl rfl rfl
        · exact FlatSchur_main hc ch c.y (.inl ⟨hk, rfl⟩) (by rw [hk]; rfl)
            (FlatSchur_colour hI.2.1 hc (by rw [hk]; rfl) (by rw [hk]; rfl)) rfl
            (FlatSchur_solidC ch c.x _).1 (FlatSchur_solidC ch c.x _).2.1
            (FlatSchur_solidC ch c.x _).2.2.1 (FlatSchur_solidC ch c.x _).2.2.2
            (FlatSchur_solidC ch _ c.y).1 (FlatSchur_solidC ch _ c.y).2.1
            (FlatSchur_solidC ch _ c.y).2.2.1 (FlatSchur_solidC ch _ c.y).2.2.2 rfl rfl
      · rw [List.mem_singleton] at ht
        subst ht
        exact FlatSchur_refl Γ
    · rw [List.mem_singleton] at ht
      subst ht
      exact FlatSchur_refl Γ
  · rw [List.mem_singleton] at ht
    subst ht
    exact FlatSchur_refl Γ

/-- The block normal form at [II, (4.20)] for a solid edge (as `qElemStep_schur_flat`). -/
theorem qElemStep_schurRev_flat :
  ∀ (n : ℕ) (x : Atom 3 n) (i : ℕ) (Γ : Graph 3 n), x.isRight = true → Γ.InvB' →
    ∀ t ∈ oSchurRevT x i Γ, Γ.FlatCarried t.g := by
  intro n x i Γ hx hI t ht
  obtain ⟨b, rfl⟩ : ∃ b, x = .inr b := by
    cases x with
    | inl a => simp at hx
    | inr b => exact ⟨b, rfl⟩
  unfold oSchurRevT at ht
  split at ht
  · rename_i c hc
    split at ht
    · rename_i ch hk
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact FlatSchur_minor hc (by rw [hk]; rfl) rfl rfl rfl rfl
        · exact FlatSchur_main hc ch c.y (.inl ⟨hk, rfl⟩) (by rw [hk]; rfl)
            (FlatSchur_colour hI.2.1 hc (by rw [hk]; rfl) (by rw [hk]; rfl)) rfl
            (FlatSchur_solidC ch c.x _).1 (FlatSchur_solidC ch c.x _).2.1
            (FlatSchur_solidC ch c.x _).2.2.1 (FlatSchur_solidC ch c.x _).2.2.2
            (FlatSchur_solidC ch _ c.y).1 (FlatSchur_solidC ch _ c.y).2.1
            (FlatSchur_solidC ch _ c.y).2.2.1 (FlatSchur_solidC ch _ c.y).2.2.2 rfl rfl
      · rw [List.mem_singleton] at ht
        subst ht
        exact FlatSchur_refl Γ
    · rw [List.mem_singleton] at ht
      subst ht
      exact FlatSchur_refl Γ
  · rw [List.mem_singleton] at ht
    subst ht
    exact FlatSchur_refl Γ

/-- The block normal form at [II, (4.17)] for a weight or light weight on an atom `a ≠ x`
(operation (B) on a blue solid loop at the molecule of `a`). -/
theorem qElemStep_schurW_flat :
  ∀ (n : ℕ) (x : Atom 3 n) (i : ℕ) (Γ : Graph 3 n), x.isRight = true → Γ.InvB' →
    ∀ t ∈ oSchurWT x i Γ, Γ.FlatCarried t.g := by
  intro n x i Γ hx hI t ht
  obtain ⟨b, rfl⟩ : ∃ b, x = .inr b := by
    cases x with
    | inl a => simp at hx
    | inr b => exact ⟨b, rfl⟩
  unfold oSchurWT at ht
  split at ht
  · rename_i c hc
    split at ht
    · rename_i ch hk
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact FlatSchur_minor hc (by rw [hk]; rfl) rfl rfl rfl rfl
        · exact FlatSchur_main hc ch c.x (.inr ⟨by rw [hk]; rfl, rfl⟩) (by rw [hk]; rfl)
            (FlatSchur_colour hI.2.1 hc (by rw [hk]; rfl) (by rw [hk]; rfl)) rfl rfl rfl
            (fun _ => rfl) rfl rfl rfl (fun _ => rfl) rfl rfl rfl
      · rw [List.mem_singleton] at ht
        subst ht
        exact FlatSchur_refl Γ
    · rename_i ch hk
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact FlatSchur_minor hc (by rw [hk]; rfl) rfl rfl rfl rfl
        · exact FlatSchur_main hc ch c.x (.inr ⟨by rw [hk]; rfl, rfl⟩) (by rw [hk]; rfl)
            (FlatSchur_colour hI.2.1 hc (by rw [hk]; rfl) (by rw [hk]; rfl)) rfl rfl rfl
            (fun _ => rfl) rfl rfl rfl (fun _ => rfl) rfl rfl rfl
      · rw [List.mem_singleton] at ht
        subst ht
        exact FlatSchur_refl Γ
    · rw [List.mem_singleton] at ht
      subst ht
      exact FlatSchur_refl Γ
  · rw [List.mem_singleton] at ht
    subst ht
    exact FlatSchur_refl Γ

/-- The block normal form at [II, (4.20)] for a weight or light weight with minor `{x}`. -/
theorem qElemStep_schurWRev_flat :
  ∀ (n : ℕ) (x : Atom 3 n) (i : ℕ) (Γ : Graph 3 n), x.isRight = true → Γ.InvB' →
    ∀ t ∈ oSchurWRevT x i Γ, Γ.FlatCarried t.g := by
  intro n x i Γ hx hI t ht
  obtain ⟨b, rfl⟩ : ∃ b, x = .inr b := by
    cases x with
    | inl a => simp at hx
    | inr b => exact ⟨b, rfl⟩
  unfold oSchurWRevT at ht
  split at ht
  · rename_i c hc
    split at ht
    · rename_i ch hk
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact FlatSchur_minor hc (by rw [hk]; rfl) rfl rfl rfl rfl
        · exact FlatSchur_main hc ch c.x (.inr ⟨by rw [hk]; rfl, rfl⟩) (by rw [hk]; rfl)
            (FlatSchur_colour hI.2.1 hc (by rw [hk]; rfl) (by rw [hk]; rfl)) rfl rfl rfl
            (fun _ => rfl) rfl rfl rfl (fun _ => rfl) rfl rfl rfl
      · rw [List.mem_singleton] at ht
        subst ht
        exact FlatSchur_refl Γ
    · rename_i ch hk
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact FlatSchur_minor hc (by rw [hk]; rfl) rfl rfl rfl rfl
        · exact FlatSchur_main hc ch c.x (.inr ⟨by rw [hk]; rfl, rfl⟩) (by rw [hk]; rfl)
            (FlatSchur_colour hI.2.1 hc (by rw [hk]; rfl) (by rw [hk]; rfl)) rfl rfl rfl
            (fun _ => rfl) rfl rfl rfl (fun _ => rfl) rfl rfl rfl
      · rw [List.mem_singleton] at ht
        subst ht
        exact FlatSchur_refl Γ
    · rw [List.mem_singleton] at ht
      subst ht
      exact FlatSchur_refl Γ
  · rw [List.mem_singleton] at ht
    subst ht
    exact FlatSchur_refl Γ

/-! ## Decidability instances for concrete graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance FlatSchur_decAdjDot {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

private instance FlatSchur_decSameBlock {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameBlock :=
  fun u v => @SimpleGraph.instDecidableRelReachable _ _ _ _ (FlatSchur_decAdjDot Γ) u v

section Helpers

variable {V E : Type}

end Helpers

end Instances

end RBM8D.Graphs
