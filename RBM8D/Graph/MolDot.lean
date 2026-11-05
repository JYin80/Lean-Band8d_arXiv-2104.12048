import RBM8D.Graph.MolRead
import RBM8D.Graph.MolCarry

/-!
# Dotted edges and carried molecular graphs in the block reading

The block reading on graphs without dotted edges at external atoms, [II, Lemma 5.10] for one
added dotted edge in the block reading, and molecular graphs carried from one atomic graph to
another by the operations of `RBM8D.Graph.MolCarry` (`Graph.FlatCarried`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Carried molecular graphs -/

/-- A molecular multigraph together with its types of vertices and of edges. -/
private structure MolDot_Pk : Type 1 where
  V : Type
  E : Type
  dV : DecidableEq V
  dE : DecidableEq E
  G : MGraph V E

/-- One step between molecular multigraphs: a change of names (`MGraph.Transported`), or one of
the operations `MGraph.CarStep` on the same types of vertices and edges. -/
private inductive MolDot_Step : MolDot_Pk → MolDot_Pk → Prop
  | tr (A B : MolDot_Pk) (h : @MGraph.Transported A.V A.E B.V B.E B.dV A.G B.G) :
      MolDot_Step A B
  | car (V E : Type) (dV : DecidableEq V) (dE : DecidableEq E) (G G' : MGraph V E)
      (h : @MGraph.CarStep V E dV dE G G') : MolDot_Step ⟨V, E, dV, dE, G⟩ ⟨V, E, dV, dE, G'⟩

/-- The molecular graph `Graph.toMG'` of `Γ'` is obtained from that of `Γ` by a finite sequence
of changes of names (`MGraph.Transported`) and of the operations `MGraph.CarStep`. -/
def Graph.FlatCarried {k n n' : ℕ} (Γ : Graph k n) (Γ' : Graph k n') : Prop :=
  Relation.ReflTransGen MolDot_Step ⟨_, _, inferInstance, inferInstance, Γ.toMG'⟩
    ⟨_, _, inferInstance, inferInstance, Γ'.toMG'⟩

/-- A chain of the operations `MGraph.CarStep` gives a chain of steps. -/
private theorem MolDot_chain {V E : Type} [dV : DecidableEq V] [dE : DecidableEq E]
    {G G' : MGraph V E} (h : Relation.ReflTransGen MGraph.CarStep G G') :
    Relation.ReflTransGen MolDot_Step ⟨V, E, dV, dE, G⟩ ⟨V, E, dV, dE, G'⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.car V E dV dE _ _ hs)

/-- `Graph.FlatCarried` from a change of names onto a graph `G₀`, a chain of the operations
`MGraph.CarStep` from `G₀` to `G₁`, and a change of names from `G₁` onto `Graph.toMG'` of the
second graph. -/
theorem MolDot_flatCarried_of_chain {k n n' : ℕ} {Γ : Graph k n} {Γ' : Graph k n'}
    {V E : Type} [DecidableEq V] [DecidableEq E] (G₀ G₁ : MGraph V E)
    (h₀ : Γ.toMG'.Transported G₀) (hch : Relation.ReflTransGen MGraph.CarStep G₀ G₁)
    (h₁ : G₁.Transported Γ'.toMG') : Γ.FlatCarried Γ' :=
  (((Relation.ReflTransGen.single (.tr _ ⟨V, E, _, _, G₀⟩ h₀)).trans (MolDot_chain hch)).tail
    (.tr ⟨V, E, _, _, G₁⟩ _ h₁))

/-- `Graph.FlatCarried` from a change of names onto `Graph.toMG'` of the second graph. -/
theorem MolDot_flatCarried_of_transported {k n n' : ℕ} {Γ : Graph k n} {Γ' : Graph k n'}
    (h : Γ.toMG'.Transported Γ'.toMG') : Γ.FlatCarried Γ' :=
  .single (.tr _ _ h)

/-- `Graph.FlatCarried` is transitive. -/
theorem flatCarried_trans :
  ∀ (k n n' n'' : ℕ) (Γ : Graph k n) (Γ' : Graph k n') (Γ'' : Graph k n''),
    Γ.FlatCarried Γ' → Γ'.FlatCarried Γ'' → Γ.FlatCarried Γ'' := by
  intro k n n' n'' Γ Γ' Γ'' h₁ h₂
  exact h₁.trans h₂

/-- The internal and external vertices of the molecular graph in the block reading are
distinct. -/
theorem Graph.toMG'_disjoint {k n : ℕ} (Γ : Graph k n) : Disjoint Γ.toMG'.int Γ.toMG'.ext := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and] at hv hv'
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨b, hb⟩ := hv'
  simp [Graph.molRep] at hb

/-- A change of names creates no ghost edge. -/
private theorem MolDot_tr_noGhost {V E V' E' : Type} [DecidableEq V'] {G : MGraph V E}
    {G' : MGraph V' E'} (h : G.Transported G') (hg : ∀ e, G.cls e ≠ some .ghost) :
    ∀ e, G'.cls e ≠ some .ghost := by
  obtain ⟨f, g, -, -, -, -, -, hcls, -, hout⟩ := h
  intro e
  by_cases he : ∃ e₀, G.cls e₀ ≠ none ∧ g e₀ = e
  · obtain ⟨e₀, he₀, rfl⟩ := he
    rw [hcls e₀ he₀]
    exact hg e₀
  · rw [hout e (fun e₀ h₁ h₂ => he ⟨e₀, h₁, h₂⟩)]
    simp

/-- A change of names keeps the internal and external vertices distinct. -/
private theorem MolDot_tr_disjoint {V E V' E' : Type} [DecidableEq V'] {G : MGraph V E}
    {G' : MGraph V' E'} (h : G.Transported G') (hd : Disjoint G.int G.ext) :
    Disjoint G'.int G'.ext := by
  obtain ⟨f, g, -, hf, hint, hext, -⟩ := h
  rw [hint, hext, Finset.disjoint_left]
  intro y hy hy'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 hy'
  have hba : b = a := hf (by simp [hb]) (by simp [ha]) hab
  subst hba
  exact Finset.disjoint_left.1 hd ha hb

/-- If the molecular graph of `Γ'` is carried from that of `Γ`, and `Γ` has no ghost edge, then
`spdPM'` passes from `Γ` to `Γ'`. -/
theorem flatCarried_spd :
  ∀ (k n n' : ℕ) (Γ : Graph k n) (Γ' : Graph k n'), Γ.FlatCarried Γ' → Γ.NoGhost → spdPM' Γ →
    spdPM' Γ' := by
  intro k n n' Γ Γ' h hg hs
  let P : MolDot_Pk → Prop := fun A =>
    @MGraph.SPD A.V A.E A.dV A.dE A.G ∧ (∀ e, A.G.cls e ≠ some .ghost) ∧
      Disjoint A.G.int A.G.ext
  have key : ∀ A B, MolDot_Step A B → P A → P B := by
    intro A B hst hA
    cases hst with
    | tr A B ht =>
      exact ⟨(@MGraph.spd_transport A.V A.E B.V B.E A.dV A.dE B.dV B.dE A.G B.G ht).2 hA.1,
        @MolDot_tr_noGhost _ _ _ _ B.dV _ _ ht hA.2.1,
        @MolDot_tr_disjoint _ _ _ _ B.dV _ _ ht hA.2.2⟩
    | car V E dV dE G G' hc =>
      obtain ⟨h1, h2, h3⟩ := @MGraph.carStep_spd V E dV dE G G' hc hA.2.2 hA.2.1 hA.1
      exact ⟨h1, h2, h3⟩
  have hP : P ⟨_, _, inferInstance, inferInstance, Γ.toMG'⟩ :=
    ⟨hs, Γ.toMG'_noGhost hg, Γ.toMG'_disjoint⟩
  have : ∀ B, Relation.ReflTransGen MolDot_Step ⟨_, _, inferInstance, inferInstance, Γ.toMG'⟩ B →
      P B := by
    intro B hB
    induction hB with
    | refl => exact hP
    | tail _ hst ih => exact key _ _ hst ih
  exact (this _ h).1

/-! ## Blocks, molecules and their representatives -/

section Generic

variable {k n : ℕ}

/-- The graph `Γ` with the dotted edge `p = q` added. -/
private def MolDot_add (Γ : Graph k n) (p q : Atom k n) : Graph k n :=
  ⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩

/-- The adjacency of the graph `fromRel` of the components satisfying `P`, with one more
component `d` satisfying `P`. -/
private theorem MolDot_fromRel_adj (P : Comp (Atom k n) → Prop) (l : List (Comp (Atom k n)))
    (d : Comp (Atom k n)) (hd : P d) (u v : Atom k n) :
    (SimpleGraph.fromRel fun u v => ∃ c ∈ l ++ [d], P c ∧ c.x = u ∧ c.y = v).Adj u v ↔
      (SimpleGraph.fromRel fun u v => ∃ c ∈ l, P c ∧ c.x = u ∧ c.y = v).Adj u v ∨
        (u ≠ v ∧ (u = d.x ∧ v = d.y ∨ u = d.y ∧ v = d.x)) := by
  simp only [SimpleGraph.fromRel_adj, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hne, ⟨c, hc | rfl, hk, rfl, rfl⟩ | ⟨c, hc | rfl, hk, rfl, rfl⟩⟩
    · exact Or.inl ⟨hne, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact Or.inr ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨hne, Or.inr ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact Or.inr ⟨hne, Or.inr ⟨rfl, rfl⟩⟩
  · rintro (⟨hne, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact ⟨hne, Or.inl ⟨c, Or.inl hc, hk, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inr ⟨c, Or.inl hc, hk, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inl ⟨d, Or.inr rfl, hd, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inr ⟨d, Or.inr rfl, hd, rfl, rfl⟩⟩

/-- Reachability in a graph with one more edge `p q`. -/
private theorem MolDot_reach {V : Type} {G G' : SimpleGraph V} (p q : V) (hle : G ≤ G')
    (hpq : G'.Reachable p q)
    (hadj : ∀ u v, G'.Adj u v → G.Adj u v ∨ (u = p ∧ v = q ∨ u = q ∧ v = p))
    (u v : V) :
    G'.Reachable u v ↔ G.Reachable u v ∨ (G.Reachable u p ∧ G.Reachable q v) ∨
      (G.Reachable u q ∧ G.Reachable p v) := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
    | @cons a b c h w ih =>
      rcases hadj _ _ h with h' | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases ih with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inl (h'.reachable.trans h3)
        · exact Or.inr (Or.inl ⟨h'.reachable.trans h3, h4⟩)
        · exact Or.inr (Or.inr ⟨h'.reachable.trans h3, h4⟩)
      · subst h1 h2
        rcases ih with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h3⟩)
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h4⟩)
        · exact Or.inl h4
      · subst h1 h2
        rcases ih with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h3⟩)
        · exact Or.inl h4
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h4⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact SimpleGraph.Reachable.mono hle h
    · exact (SimpleGraph.Reachable.mono hle h1).trans
        (hpq.trans (SimpleGraph.Reachable.mono hle h2))
    · exact (SimpleGraph.Reachable.mono hle h1).trans
        (hpq.symm.trans (SimpleGraph.Reachable.mono hle h2))

/-- The dotted edges are edges of the molecular graph. -/
private theorem MolDot_dot_le_mol (Γ : Graph k n) : Γ.dotGraph ≤ Γ.molGraph := by
  intro u v huv
  simp only [Graph.dotGraph, Graph.molGraph, SimpleGraph.fromRel_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
  · exact Or.inl ⟨c, hc, by simp [hk, Kind.joinsMol], h1, h2⟩
  · exact Or.inr ⟨c, hc, by simp [hk, Kind.joinsMol], h1, h2⟩

/-- The blocks after the dotted edge `p = q` is added. -/
private theorem MolDot_sameBlock_add (Γ : Graph k n) (p q u v : Atom k n) :
    (MolDot_add Γ p q).SameBlock u v ↔ Γ.SameBlock u v ∨ (Γ.SameBlock u p ∧ Γ.SameBlock q v) ∨
      (Γ.SameBlock u q ∧ Γ.SameBlock p v) := by
  have hadj := MolDot_fromRel_adj (fun c => c.kind = .dot) Γ.comps (mkC .dot p q) rfl
  refine MolDot_reach (G := Γ.dotGraph) (G' := (MolDot_add Γ p q).dotGraph) p q ?_ ?_ ?_ u v
  · intro a b h
    exact (hadj a b).2 (Or.inl h)
  · by_cases hpq : p = q
    · subst hpq
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ((hadj p q).2 (Or.inr ⟨hpq, Or.inl ⟨rfl, rfl⟩⟩))
  · intro a b h
    rcases (hadj a b).1 h with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

/-- The reachability in the molecular graph after the dotted edge `p = q` is added. -/
private theorem MolDot_molReach_add (Γ : Graph k n) (p q u v : Atom k n) :
    (MolDot_add Γ p q).molGraph.Reachable u v ↔ Γ.molGraph.Reachable u v ∨
      (Γ.molGraph.Reachable u p ∧ Γ.molGraph.Reachable q v) ∨
      (Γ.molGraph.Reachable u q ∧ Γ.molGraph.Reachable p v) := by
  have hadj := MolDot_fromRel_adj (fun c => c.kind.joinsMol = true) Γ.comps (mkC .dot p q) rfl
  refine MolDot_reach (G := Γ.molGraph) (G' := (MolDot_add Γ p q).molGraph) p q ?_ ?_ ?_ u v
  · intro a b h
    exact (hadj a b).2 (Or.inl h)
  · by_cases hpq : p = q
    · subst hpq
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ((hadj p q).2 (Or.inr ⟨hpq, Or.inl ⟨rfl, rfl⟩⟩))
  · intro a b h
    rcases (hadj a b).1 h with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

private theorem MolDot_sameBlock_mono {Γ : Graph k n} {p q u v : Atom k n}
    (h : Γ.SameBlock u v) : (MolDot_add Γ p q).SameBlock u v :=
  (MolDot_sameBlock_add Γ p q u v).2 (Or.inl h)

private theorem MolDot_sameMol_mono {Γ : Graph k n} {p q u v : Atom k n}
    (h : Γ.SameMol u v) : (MolDot_add Γ p q).SameMol u v := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, (MolDot_molReach_add Γ p q u v).2 (Or.inl h3)⟩

/-- `p` and `q` lie in one block after the dotted edge `p = q` is added. -/
private theorem MolDot_sameBlock_pq (Γ : Graph k n) (p q : Atom k n) :
    (MolDot_add Γ p q).SameBlock p q :=
  (MolDot_sameBlock_add Γ p q p q).2
    (Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩))

/-! ### Anchors, the block normal form and representatives -/

private theorem MolDot_anchor_some {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.anchor u = some b) : Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor at h
  have hb := List.find?_some h
  exact of_decide_eq_true hb

private theorem MolDot_anchor_none {Γ : Graph k n} {u : Atom k n} :
    Γ.anchor u = none ↔ ∀ b, ¬ Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor
  rw [List.find?_eq_none]
  simp

/-- An atom lies in the block of its atom in the block normal form. -/
private theorem MolDot_flat_block (Γ : Graph k n) (u : Atom k n) :
    Γ.SameBlock u (Γ.flatAtom u) := by
  cases u with
  | inr b => exact SimpleGraph.Reachable.refl _
  | inl a =>
    rcases hA : Γ.anchor (.inl a) with _ | b
    · simp only [Graph.flatAtom, hA]
      exact SimpleGraph.Reachable.refl _
    · simp only [Graph.flatAtom, hA]
      exact MolDot_anchor_some hA

/-- At an atom that is not unpinned, the atom of the block normal form is internal. -/
private theorem MolDot_flat_isRight {Γ : Graph k n} {u : Atom k n} (h : ¬ Γ.Unpinned u) :
    (Γ.flatAtom u).isRight = true := by
  cases u with
  | inr b => rfl
  | inl a =>
    rcases hA : Γ.anchor (.inl a) with _ | b
    · exact absurd ⟨rfl, MolDot_anchor_none.1 hA⟩ h
    · simp only [Graph.flatAtom, hA]
      rfl

/-- At an unpinned atom, the atom of the block normal form is the atom. -/
private theorem MolDot_flat_unpinned {Γ : Graph k n} {u : Atom k n} (h : Γ.Unpinned u) :
    Γ.flatAtom u = u := by
  obtain ⟨-, h2⟩ := h
  cases u with
  | inr b => rfl
  | inl a =>
    have hA : Γ.anchor (.inl a) = none := MolDot_anchor_none.2 h2
    simp only [Graph.flatAtom, hA]

/-- An atom in a block with an internal atom is not unpinned. -/
private theorem MolDot_not_unpinned {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.SameBlock u (.inr b)) : ¬ Γ.Unpinned u :=
  fun h' => h'.2 b h

/-- The default value of `List.find?` does not matter when some element satisfies the
predicate. -/
private theorem MolDot_find_congr {α : Type} (l : List α) (P P' : α → Bool) (d d' : α)
    (hPP : ∀ x, P x = P' x) (h : ∃ x ∈ l, P x = true) :
    (l.find? P).getD d = (l.find? P').getD d' := by
  have e : P = P' := funext hPP
  subst e
  obtain ⟨x, hx, hp⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨x, hx, hp⟩)
  simp [hr]

/-- A property of all elements satisfying `P` and of the default value holds for the value of
`List.find?`. -/
private theorem MolDot_find_getD {α : Type} (l : List α) (P : α → Bool) (d : α) (Q : α → Prop)
    (hP : ∀ b, P b = true → Q b) (hd : Q d) : Q ((l.find? P).getD d) := by
  cases h : l.find? P with
  | none => simpa using hd
  | some r => simpa using hP r (List.find?_some h)

/-- An atom lies in the molecule of its representative. -/
private theorem MolDot_molRep_spec (Γ : Graph k n) (u : Atom k n) :
    Γ.SameMol u (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inl rfl
  | inr a =>
    unfold Graph.molRep
    exact MolDot_find_getD _ _ a (fun r => Γ.SameMol (.inr a) (.inr r))
      (fun b hb => of_decide_eq_true hb) (Or.inl rfl)

/-- Atoms of one molecule have the same representative. -/
private theorem MolDot_molRep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.molRep u = Γ.molRep v ↔ Γ.SameMol u v := by
  have E := Γ.sameMol_equivalence
  constructor
  · intro h
    exact E.trans (MolDot_molRep_spec Γ u) (h ▸ E.symm (MolDot_molRep_spec Γ v))
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
        refine congrArg Sum.inr (MolDot_find_congr _ _ _ _ _ (fun c => ?_)
          ⟨b, List.mem_finRange _, decide_eq_true h⟩)
        exact decide_eq_decide.2 ⟨fun h' => E.trans (E.symm h) h', fun h' => E.trans h h'⟩

/-- The representative of an internal atom is internal, that of an external atom is the atom. -/
private theorem MolDot_molRep_cases (Γ : Graph k n) (u : Atom k n) :
    (∃ a, u = .inl a ∧ Γ.molRep u = .inl a) ∨ (∃ a b, u = .inr a ∧ Γ.molRep u = .inr b) := by
  cases u with
  | inl a => exact Or.inl ⟨a, rfl, rfl⟩
  | inr a => exact Or.inr ⟨a, _, rfl, rfl⟩

/-- In a block with an internal atom `c`, the representative of the atom of the block normal form
is that of `c`. -/
private theorem MolDot_molRep_flat {Γ : Graph k n} {u : Atom k n} {c : Fin n}
    (h : Γ.SameBlock u (.inr c)) : Γ.molRep (Γ.flatAtom u) = Γ.molRep (.inr c) := by
  have hr := MolDot_flat_isRight (MolDot_not_unpinned h)
  have hb : Γ.SameBlock (Γ.flatAtom u) (.inr c) := (MolDot_flat_block Γ u).symm.trans h
  exact (MolDot_molRep_eq_iff Γ _ _).2
    (Or.inr ⟨hr, rfl, SimpleGraph.Reachable.mono (MolDot_dot_le_mol Γ) hb⟩)

/-- The representative of every atom is a vertex of `Graph.toMG'`. -/
private theorem MolDot_molRep_vtx (Γ : Graph k n) (u : Atom k n) :
    Γ.toMG'.IsVtx (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  | inr a => exact Or.inl (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)

/-- The representatives of the internal atoms are the internal vertices. -/
private theorem MolDot_mem_int {Γ : Graph k n} {v : Atom k n} :
    v ∈ Γ.toMG'.int ↔ ∃ a, Γ.molRep (.inr a) = v := by
  simp [Graph.toMG']

private theorem MolDot_mem_ext {Γ : Graph k n} {v : Atom k n} :
    v ∈ Γ.toMG'.ext ↔ v.isLeft = true := by
  cases v <;> simp [Graph.toMG']

end Generic

/-! ## The molecular graph after a dotted edge is added -/

section Add

variable {k n : ℕ}

/-- The index in `MolDot_add Γ p q` of the component `i` of `Γ`. -/
private def MolDot_idx (Γ : Graph k n) (p q : Atom k n) (i : Fin Γ.comps.length) :
    Fin (MolDot_add Γ p q).comps.length :=
  ⟨i, by simp only [MolDot_add, List.length_append, List.length_singleton]; omega⟩

/-- The index of the added dotted edge. -/
private def MolDot_last (Γ : Graph k n) (p q : Atom k n) : Fin (MolDot_add Γ p q).comps.length :=
  ⟨Γ.comps.length, by simp [MolDot_add]⟩

private theorem MolDot_get_idx (Γ : Graph k n) (p q : Atom k n) (i : Fin Γ.comps.length) :
    (MolDot_add Γ p q).comps[MolDot_idx Γ p q i] = Γ.comps[i] := by
  simp [MolDot_add, MolDot_idx, List.getElem_append_left]

private theorem MolDot_get_last (Γ : Graph k n) (p q : Atom k n) :
    (MolDot_add Γ p q).comps[MolDot_last Γ p q] = mkC .dot p q := by
  simp [MolDot_add, MolDot_last]

private theorem MolDot_idx_cases (Γ : Graph k n) (p q : Atom k n)
    (j : Fin (MolDot_add Γ p q).comps.length) :
    (∃ i, j = MolDot_idx Γ p q i) ∨ j = MolDot_last Γ p q := by
  by_cases h : j.val < Γ.comps.length
  · exact Or.inl ⟨⟨j, h⟩, Fin.ext rfl⟩
  · right
    have := j.isLt
    simp only [MolDot_add, List.length_append, List.length_singleton] at this
    exact Fin.ext (by simp only [MolDot_last]; omega)

/-- The class of the edge `.inl i` of `Graph.toMG'`. -/
private theorem MolDot_cls_inl (Δ : Graph k n) (i : Fin Δ.comps.length) :
    Δ.toMG'.cls (.inl i) = if Δ.comps[i].kind = .dot then none
      else if Δ.molRep (Δ.flatAtom Δ.comps[i].x) = Δ.molRep (Δ.flatAtom Δ.comps[i].y) then none
      else Δ.comps[i].kind.mclass := by
  by_cases hk : Δ.comps[i.val].kind = .dot
  · simp [Graph.toMG', Graph.flatComp, hk]
  · simp [Graph.toMG', Graph.flatComp, hk]

/-- The ends of the edge `.inl i` of `Graph.toMG'` for a component other than a dotted edge. -/
private theorem MolDot_ends_inl (Δ : Graph k n) (i : Fin Δ.comps.length)
    (hk : Δ.comps[i].kind ≠ .dot) :
    Δ.toMG'.ends (.inl i) =
      (Δ.molRep (Δ.flatAtom Δ.comps[i].x), Δ.molRep (Δ.flatAtom Δ.comps[i].y)) := by
  have hk' : Δ.comps[i.val].kind ≠ .dot := hk
  simp [Graph.toMG', Graph.flatComp, hk']

private theorem MolDot_molRep_block {Δ : Graph k n} {a b : Fin n}
    (h : Δ.SameBlock (.inr a) (.inr b)) : Δ.molRep (.inr a) = Δ.molRep (.inr b) :=
  (MolDot_molRep_eq_iff Δ _ _).2
    (Or.inr ⟨rfl, rfl, SimpleGraph.Reachable.mono (MolDot_dot_le_mol Δ) h⟩)

/-- The edge `.inr a` of `Graph.toMG'` at an external atom `a` identified with an internal atom. -/
private theorem MolDot_pin_some {Δ : Graph k n} {a : Fin k} {b : Fin n}
    (h : Δ.SameBlock (.inl a) (.inr b)) :
    Δ.toMG'.cls (.inr a) = some (pinClass a) ∧
      Δ.toMG'.ends (.inr a) = (Δ.molRep (.inr b), .inl a) := by
  rcases hA : Δ.anchor (.inl a) with _ | b'
  · exact absurd h (MolDot_anchor_none.1 hA b)
  · have hb' := MolDot_anchor_some hA
    simp only [Graph.toMG', hA, true_and]
    rw [MolDot_molRep_block (hb'.symm.trans h)]

/-- The edge `.inr a` of `Graph.toMG'` at an unpinned external atom `a` is absent. -/
private theorem MolDot_pin_none {Δ : Graph k n} {a : Fin k} (h : Δ.Unpinned (.inl a)) :
    Δ.toMG'.cls (.inr a) = none := by
  have hA : Δ.anchor (.inl a) = none := MolDot_anchor_none.2 h.2
  simp only [Graph.toMG', hA]

private theorem MolDot_unpinned_of_add {Γ : Graph k n} {p q u : Atom k n}
    (h : (MolDot_add Γ p q).Unpinned u) : Γ.Unpinned u :=
  ⟨h.1, fun b hb => h.2 b (MolDot_sameBlock_mono hb)⟩

private theorem MolDot_unpinned_add {Γ : Graph k n} {p q u : Atom k n} {b₀ : Fin n}
    (hp : Γ.SameBlock p (.inr b₀)) (h : Γ.Unpinned u) (hq : ¬ Γ.SameBlock u q) :
    (MolDot_add Γ p q).Unpinned u := by
  refine ⟨h.1, fun b hb => ?_⟩
  rcases (MolDot_sameBlock_add Γ p q _ _).1 hb with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h.2 b h1
  · exact h.2 b₀ (h1.trans hp)
  · exact hq h1

/-- An atom in the block of an atom that is not unpinned is in a block with an internal atom. -/
private theorem MolDot_block_of_not_unpinned {Γ : Graph k n} {u q : Atom k n}
    (hq : ¬ Γ.Unpinned q) (h : Γ.SameBlock u q) : ∃ b, Γ.SameBlock u (.inr b) := by
  cases q with
  | inr b => exact ⟨b, h⟩
  | inl a =>
    by_contra hn
    push Not at hn
    exact hq ⟨rfl, fun b hb => hn b (h.trans hb)⟩

/-- The representatives of the molecules of the new graph read through those of `Γ`. -/
private theorem MolDot_molRep_molRep (Γ : Graph k n) (p q v : Atom k n) :
    (MolDot_add Γ p q).molRep (Γ.molRep v) = (MolDot_add Γ p q).molRep v :=
  (MolDot_molRep_eq_iff _ _ _).2
    (MolDot_sameMol_mono (Γ.sameMol_equivalence.symm (MolDot_molRep_spec Γ v)))

/-- Away from an unpinned atom in the block of `q`, the atom of the block normal form of the new
graph has the molecule of that of `Γ`. -/
private theorem MolDot_rho_add {Γ : Graph k n} {p q u : Atom k n} {b₀ : Fin n}
    (hp : Γ.SameBlock p (.inr b₀)) (hu : ¬ (Γ.Unpinned u ∧ Γ.SameBlock u q)) :
    (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom u) =
      (MolDot_add Γ p q).molRep (Γ.flatAtom u) := by
  by_cases h : Γ.Unpinned u
  · have hq : ¬ Γ.SameBlock u q := fun h' => hu ⟨h, h'⟩
    rw [MolDot_flat_unpinned (MolDot_unpinned_add hp h hq), MolDot_flat_unpinned h]
  · have hr := MolDot_flat_isRight h
    obtain ⟨c, hc⟩ : ∃ c, Γ.flatAtom u = .inr c := by
      cases hf : Γ.flatAtom u with
      | inl a =>
        rw [hf] at hr
        simp at hr
      | inr c => exact ⟨c, rfl⟩
    have hb : Γ.SameBlock u (.inr c) := hc ▸ MolDot_flat_block Γ u
    rw [hc]
    exact MolDot_molRep_flat (MolDot_sameBlock_mono hb)

/-- The atom `q` is read at the molecule of `p` in the new graph. -/
private theorem MolDot_rho_q {Γ : Graph k n} {p q : Atom k n} {b₀ : Fin n}
    (hp : Γ.SameBlock p (.inr b₀)) :
    (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom q) =
      (MolDot_add Γ p q).molRep (.inr b₀) :=
  MolDot_molRep_flat ((MolDot_sameBlock_pq Γ p q).symm.trans (MolDot_sameBlock_mono hp))

/-- The molecules of the new graph: the molecules of `Γ`, with that of `p` and the one reachable
from `q` identified. -/
private theorem MolDot_inj {Γ : Graph k n} {p q : Atom k n} {b₀ : Fin n}
    (hp : Γ.SameBlock p (.inr b₀)) {Mq : Atom k n}
    (hMq : ∀ a, Γ.molGraph.Reachable q (.inr a) → Γ.molRep (.inr a) = Mq) (a a' : Fin n)
    (h : (MolDot_add Γ p q).molRep (.inr a) = (MolDot_add Γ p q).molRep (.inr a')) :
    (if Γ.molRep (.inr a) = Mq then Γ.molRep (.inr b₀) else Γ.molRep (.inr a)) =
      (if Γ.molRep (.inr a') = Mq then Γ.molRep (.inr b₀) else Γ.molRep (.inr a')) := by
  have hpR : Γ.molGraph.Reachable p (.inr b₀) :=
    SimpleGraph.Reachable.mono (MolDot_dot_le_mol Γ) hp
  have toMp : ∀ x, Γ.molGraph.Reachable (.inr x) p →
      Γ.molRep (.inr x) = Γ.molRep (.inr b₀) := fun x hx =>
    (MolDot_molRep_eq_iff Γ _ _).2 (Or.inr ⟨rfl, rfl, hx.trans hpR⟩)
  rcases (MolDot_molRep_eq_iff _ _ _).1 h with h | ⟨-, -, h⟩
  · rw [h]
  · rcases (MolDot_molReach_add Γ p q _ _).1 h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [(MolDot_molRep_eq_iff Γ _ _).2 (Or.inr ⟨rfl, rfl, h⟩)]
    · rw [toMp a h1, hMq a' h2]
      simp
    · rw [hMq a h1.symm, toMp a' h2.symm]
      simp

end Add

/-! ## Chains of operations on molecular multigraphs -/

section Chains

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- All present loops removed, one at a time (`MGraph.CarStep.unloop`). -/
private theorem MolDot_unloopAll [Finite E] (K : MGraph V E) :
    ∃ K', Relation.ReflTransGen MGraph.CarStep K K' ∧ K'.int = K.int ∧ K'.ext = K.ext ∧
      K'.ends = K.ends ∧ ∀ e, K'.cls e = if (K.ends e).1 = (K.ends e).2 then none else K.cls e := by
  have := Fintype.ofFinite E
  have key : ∀ l : List E, ∃ K', Relation.ReflTransGen MGraph.CarStep K K' ∧ K'.int = K.int ∧
      K'.ext = K.ext ∧ K'.ends = K.ends ∧
      ∀ e, K'.cls e = if e ∈ l ∧ (K.ends e).1 = (K.ends e).2 then none else K.cls e := by
    intro l
    induction l with
    | nil => exact ⟨K, .refl, rfl, rfl, rfl, fun e => by simp⟩
    | cons a t ih =>
      obtain ⟨K₁, h₁, i₁, x₁, e₁, c₁⟩ := ih
      by_cases ha : K₁.cls a ≠ none ∧ (K.ends a).1 = (K.ends a).2
      · refine ⟨K₁.erase a, h₁.tail (.unloop _ _ ha.1 (by rw [e₁]; exact ha.2)), i₁, x₁, e₁,
          fun e => ?_⟩
        by_cases hea : e = a
        · subst hea
          simp [MGraph.erase, ha.2]
        · simp only [MGraph.erase, Function.update_of_ne hea, c₁ e, List.mem_cons, hea, false_or]
      · refine ⟨K₁, h₁, i₁, x₁, e₁, fun e => ?_⟩
        rw [c₁ e]
        by_cases hea : e = a
        · subst hea
          by_cases hL : (K.ends e).1 = (K.ends e).2
          · have : K₁.cls e = none := by
              by_contra hc
              exact ha ⟨hc, hL⟩
            rw [c₁ e] at this
            simp only [hL, and_true] at this ⊢
            split_ifs at this ⊢ <;> simp_all
          · simp [hL]
        · simp [hea]
  obtain ⟨K', h, i, x, e, c⟩ := key Finset.univ.toList
  exact ⟨K', h, i, x, e, fun e' => by rw [c e']; simp⟩

/-- One edge `e` from an internal vertex to the external vertex `q`, blue solid, diffusive or red,
moved to the internal vertex `M`: operation (B) or [II, Lemma 5.12 (v)] through `M` with the
absent edge `s`, the new edge from `M` to `q` then removed against the edge `π` from `M` to `q`;
a red edge is moved directly. -/
private theorem MolDot_move (K : MGraph V E) (M q : V) (e s π : E)
    (hM : M ∈ K.int) (hq : q ∈ K.ext) (hs : K.cls s = none) (hes : e ≠ s) (hsπ : s ≠ π)
    (heπ : e ≠ π) (hπ : K.ends π = (M, q)) (h1 : (K.ends e).1 ∈ K.int) (h2 : (K.ends e).2 = q)
    (hc : K.cls e = some .minus ∨ ((K.cls e = some .plus ∨ K.cls e = some .diff) ∧
      K.cls π ≠ none ∧ K.cls π ≠ some .minus)) :
    ∃ K', Relation.ReflTransGen MGraph.CarStep K K' ∧ K'.int = K.int ∧ K'.ext = K.ext ∧
      (∀ x, K'.cls x = K.cls x) ∧ K'.ends e = ((K.ends e).1, M) ∧
      ∀ x, x ≠ e → x ≠ s → K'.ends x = K.ends x := by
  have hπe : π ≠ e := Ne.symm heπ
  have hπs : π ≠ s := Ne.symm hsπ
  rcases hc with hc | ⟨hc, hπ1, hπ2⟩
  · refine ⟨K.setEdge e (K.ends e).1 M (some .minus),
      .single (.red _ _ _ _ _ (Or.inr hc) (Or.inr rfl)), rfl, rfl, fun x => ?_, ?_,
      fun x hx _ => ?_⟩
    · by_cases hx : x = e
      · subst hx
        simp [MGraph.setEdge, hc]
      · simp [MGraph.setEdge, hx]
    · simp [MGraph.setEdge]
    · simp [MGraph.setEdge, hx]
  · have hse : s ≠ e := Ne.symm hes
    have hq2 : (K.ends e).2 ∈ K.ext := h2 ▸ hq
    -- the first step: operation (B) or [II, Lemma 5.12 (v)] through `M`
    obtain ⟨K₁, c₁, hK₁s, hK₁e, hK₁i, hK₁x, hK₁c, hK₁cl, hK₁o⟩ : ∃ K₁,
        MGraph.CarStep K K₁ ∧ K₁.ends s = (M, (K.ends e).2) ∧ K₁.ends e = ((K.ends e).1, M) ∧
        K₁.int = K.int ∧ K₁.ext = K.ext ∧
        (K₁.cls s ≠ none ∧ K₁.cls s ≠ some .minus) ∧ (∀ x, x ≠ s → K₁.cls x = K.cls x) ∧
        ∀ x, x ≠ e → x ≠ s → K₁.ends x = K.ends x := by
      rcases hc with hc | hc
      · refine ⟨K.split e s M, .split _ _ _ _ hc (Or.inl h1) (Or.inr hq2) (Or.inl h1) hes hs hM,
          by simp [MGraph.split, hse], by simp [MGraph.split], rfl, rfl,
          by simp [MGraph.split, hc], fun x hx => by simp [MGraph.split, hx],
          fun x hx hxs => by simp [MGraph.split, hx, hxs]⟩
      · refine ⟨(K.split e s M).recolor s (some .dot),
          .splitExt _ _ _ _ _ hc h1 hq2 hes hs hM (Or.inr rfl),
          by simp [MGraph.split, MGraph.recolor, hse], by simp [MGraph.split, MGraph.recolor],
          rfl, rfl, by simp [MGraph.recolor],
          fun x hx => by simp [MGraph.split, MGraph.recolor, hx],
          fun x hx hxs => by simp [MGraph.split, MGraph.recolor, hx, hxs]⟩
    have hK₁π : K₁.ends π = (M, q) := by rw [hK₁o π hπe hπs, hπ]
    refine ⟨K₁.erase s, (Relation.ReflTransGen.single c₁).tail
        (.dropExt _ s π hsπ hK₁c (by rw [hK₁s, hK₁i]; exact hM) (by rw [hK₁s, hK₁x]; exact hq2)
          (by rw [hK₁cl π hπs]; exact ⟨hπ1, hπ2⟩) (by rw [hK₁π, hK₁s])
          (by rw [hK₁π, hK₁x]; exact hq)),
      hK₁i, hK₁x, fun x => ?_, ?_, fun x hx hxs => ?_⟩
    · by_cases hx : x = s
      · subst hx
        simp [MGraph.erase, hs]
      · simp [MGraph.erase, hx, hK₁cl x hx]
    · simp only [MGraph.erase]
      exact hK₁e
    · simp only [MGraph.erase]
      exact hK₁o x hx hxs

/-- The edges of a list, each from an internal vertex to the external vertex `q`, moved one at a
time to the internal vertex `M` (`MolDot_move`). -/
private theorem MolDot_moveList (M q : V) (s π : E) :
    ∀ (l : List E) (K : MGraph V E), l.Nodup → M ∈ K.int → q ∈ K.ext → K.cls s = none →
      s ≠ π → K.ends π = (M, q) →
      (∀ e ∈ l, e ≠ s ∧ e ≠ π ∧ (K.ends e).1 ∈ K.int ∧ (K.ends e).2 = q ∧
        (K.cls e = some .minus ∨ ((K.cls e = some .plus ∨ K.cls e = some .diff) ∧
          K.cls π ≠ none ∧ K.cls π ≠ some .minus))) →
      ∃ K', Relation.ReflTransGen MGraph.CarStep K K' ∧ K'.int = K.int ∧ K'.ext = K.ext ∧
        (∀ x, K'.cls x = K.cls x) ∧ (∀ x ∈ l, K'.ends x = ((K.ends x).1, M)) ∧
        ∀ x, x ∉ l → x ≠ s → K'.ends x = K.ends x
  | [], K, _, _, _, _, _, _, _ => ⟨K, .refl, rfl, rfl, fun _ => rfl, by simp, fun _ _ _ => rfl⟩
  | e :: t, K, hnd, hM, hq, hs, hsπ, hπ, hl => by
    obtain ⟨he1, he2, he3, he4, he5⟩ := hl e List.mem_cons_self
    obtain ⟨K₁, c₁, i₁, x₁, cl₁, ee₁, eo₁⟩ :=
      MolDot_move K M q e s π hM hq hs he1 hsπ he2 hπ he3 he4 he5
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.1 hnd
    have hπ₁ : K₁.ends π = (M, q) := by rw [eo₁ π (Ne.symm he2) (Ne.symm hsπ)]; exact hπ
    obtain ⟨K₂, c₂, i₂, x₂, cl₂, ee₂, eo₂⟩ := MolDot_moveList M q s π t K₁ hnd'
      (by rw [i₁]; exact hM) (by rw [x₁]; exact hq) (by rw [cl₁ s]; exact hs) hsπ hπ₁
      (fun x hx => by
        have hxe : x ≠ e := fun h => hnot (h ▸ hx)
        obtain ⟨h1, h2, h3, h4, h5⟩ := hl x (List.mem_cons_of_mem _ hx)
        rw [eo₁ x hxe h1, i₁, cl₁ x, cl₁ π]
        exact ⟨h1, h2, h3, h4, h5⟩)
    refine ⟨K₂, c₁.trans c₂, i₂.trans i₁, x₂.trans x₁, fun x => (cl₂ x).trans (cl₁ x),
      fun x hx => ?_, fun x hx hxs => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · rw [eo₂ x hnot he1, ee₁]
      · have hxe : x ≠ e := fun h => hnot (h ▸ hx)
        rw [ee₂ x hx, eo₁ x hxe (hl x (List.mem_cons_of_mem _ hx)).1]
    · have hxe : x ≠ e := fun h => hx (h ▸ List.mem_cons_self)
      have hxt : x ∉ t := fun h => hx (List.mem_cons_of_mem _ h)
      rw [eo₂ x hxt hxs, eo₁ x hxe hxs]

end Chains

/-! ## The first change of names -/

section First

variable {k n : ℕ}

/-- The pair `xy` with its two entries exchanged when the first one lies in `X`. -/
private def MolDot_or {V : Type} [DecidableEq V] (X : Finset V) (xy : V × V) : V × V :=
  if xy.1 ∈ X then (xy.2, xy.1) else xy

/-- `Graph.toMG'` of `Γ` with one absent edge more (the index of the added dotted edge) and every
edge with an external first end stored in the other order. -/
private def MolDot_G0 (Γ : Graph k n) (p q : Atom k n) :
    MGraph (Atom k n) (Fin (MolDot_add Γ p q).comps.length ⊕ Fin k) where
  int := Γ.toMG'.int
  ext := Γ.toMG'.ext
  ends e := MolDot_or Γ.toMG'.ext (match e with
    | .inl j => if h : j.val < Γ.comps.length then Γ.toMG'.ends (.inl ⟨j, h⟩) else (p, p)
    | .inr a => Γ.toMG'.ends (.inr a))
  cls e := match e with
    | .inl j => if h : j.val < Γ.comps.length then Γ.toMG'.cls (.inl ⟨j, h⟩) else none
    | .inr a => Γ.toMG'.cls (.inr a)

private theorem MolDot_G0_cls_idx (Γ : Graph k n) (p q : Atom k n) (i : Fin Γ.comps.length) :
    (MolDot_G0 Γ p q).cls (.inl (MolDot_idx Γ p q i)) = Γ.toMG'.cls (.inl i) := by
  simp [MolDot_G0, MolDot_idx]

private theorem MolDot_G0_cls_last (Γ : Graph k n) (p q : Atom k n) :
    (MolDot_G0 Γ p q).cls (.inl (MolDot_last Γ p q)) = none := by
  simp [MolDot_G0, MolDot_last]

private theorem MolDot_G0_ends_idx (Γ : Graph k n) (p q : Atom k n) (i : Fin Γ.comps.length) :
    (MolDot_G0 Γ p q).ends (.inl (MolDot_idx Γ p q i)) =
      MolDot_or Γ.toMG'.ext (Γ.toMG'.ends (.inl i)) := by
  simp [MolDot_G0, MolDot_idx]

/-- The present edges of `Graph.toMG'` join vertices. -/
private theorem MolDot_toMG'_vtx (Δ : Graph k n) (e : Fin Δ.comps.length ⊕ Fin k)
    (he : Δ.toMG'.cls e ≠ none) :
    Δ.toMG'.IsVtx (Δ.toMG'.ends e).1 ∧ Δ.toMG'.IsVtx (Δ.toMG'.ends e).2 := by
  rcases e with i | a
  · exact ⟨MolDot_molRep_vtx Δ _, MolDot_molRep_vtx Δ _⟩
  · rcases hA : Δ.anchor (.inl a) with _ | b
    · simp [Graph.toMG', hA] at he
    · have h := MolDot_pin_some (MolDot_anchor_some hA)
      rw [h.2]
      exact ⟨MolDot_molRep_vtx Δ (.inr b), MolDot_molRep_vtx Δ (.inl a)⟩

/-- `Graph.toMG'` of `Γ` is carried to `MolDot_G0` by a change of names. -/
private theorem MolDot_tr0 (Γ : Graph k n) (p q : Atom k n) :
    Γ.toMG'.Transported (MolDot_G0 Γ p q) := by
  have hinj : Function.Injective (Sum.map (MolDot_idx Γ p q) (id : Fin k → Fin k)) :=
    Function.Injective.sumMap
      (fun i j h => Fin.ext (by simpa [MolDot_idx] using congrArg Fin.val h))
      Function.injective_id
  refine ⟨id, Sum.map (MolDot_idx Γ p q) id, fun e₁ e₂ _ _ h => hinj h, Set.injOn_id _,
    Finset.image_id.symm, Finset.image_id.symm, MolDot_toMG'_vtx Γ, ?_, ?_, ?_⟩
  · rintro (i | a) _
    · exact MolDot_G0_cls_idx Γ p q i
    · rfl
  · rintro (i | a) _
    · rw [Sum.map_inl, MolDot_G0_ends_idx]
      unfold MolDot_or
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · change MolDot_or _ _ = _ ∨ MolDot_or _ _ = _
      unfold MolDot_or
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · rintro (j | a) hj
    · rcases MolDot_idx_cases Γ p q j with ⟨i, rfl⟩ | rfl
      · rw [MolDot_G0_cls_idx]
        by_contra hc
        exact hj (.inl i) hc rfl
      · exact MolDot_G0_cls_last Γ p q
    · change Γ.toMG'.cls (.inr a) = none
      by_contra hc
      exact hj (.inr a) hc rfl

end First

/-! ## The last change of names -/

section Final

variable {k n : ℕ}

/-- The map of the vertices identifying the vertex `Mq` with `Mp` (operation (A)). -/
private def MolDot_mu {V : Type} [DecidableEq V] (Mp Mq v : V) : V := if v = Mq then Mp else v

private theorem MolDot_molRep_inr_ne (Δ : Graph k n) (a : Fin n) (b : Fin k) :
    Δ.molRep (.inr a) ≠ .inl b := by
  simp [Graph.molRep]

/-- A graph `H` obtained from `MolDot_G0` by operation (A) on `Mp` and `Mq`, the edges at an
unpinned `q` moved to `Mp` together with a new edge from `Mp` to `q`, and the removal of loops, is
carried to `Graph.toMG'` of the new graph by the change of names `Graph.molRep` of the new
graph. -/
private theorem MolDot_final {Γ : Graph k n} {p q : Atom k n} {b₀ : Fin n}
    (hp : Γ.SameBlock p (.inr b₀)) {Mq : Atom k n} (hMq1 : Mq ∈ Γ.toMG'.int)
    (hMq2 : ∀ a, Γ.molGraph.Reachable q (.inr a) → Γ.molRep (.inr a) = Mq)
    (hMq3 : (MolDot_add Γ p q).molRep Mq = (MolDot_add Γ p q).molRep (.inr b₀))
    (hB1 : Γ.Unpinned q → ∀ u, Γ.SameBlock u q → u = q)
    (hQ : Γ.Unpinned q → ∀ e, Γ.toMG'.cls e ≠ none → (Γ.toMG'.ends e).1 ∈ Γ.toMG'.ext →
      (Γ.toMG'.ends e).2 ∈ Γ.toMG'.ext → (Γ.toMG'.ends e).1 ≠ q ∧ (Γ.toMG'.ends e).2 ≠ q)
    (H₂ H : MGraph (Atom k n) (Fin (MolDot_add Γ p q).comps.length ⊕ Fin k))
    (hi2 : H₂.int = Γ.toMG'.int.image (MolDot_mu (Γ.molRep (.inr b₀)) Mq))
    (hx2 : H₂.ext = Γ.toMG'.ext)
    (hpin : ∀ a, Γ.Unpinned q → q = .inl a →
      H₂.cls (.inr a) = some (pinClass a) ∧ H₂.ends (.inr a) = (Γ.molRep (.inr b₀), q))
    (hcl2 : ∀ e, (∀ a, Γ.Unpinned q → q = .inl a → e ≠ .inr a) →
      H₂.cls e = (MolDot_G0 Γ p q).cls e)
    (hen2a : ∀ e, (∀ a, Γ.Unpinned q → q = .inl a → e ≠ .inr a) →
      (MolDot_G0 Γ p q).cls e ≠ none → Γ.Unpinned q →
      MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).2 = q →
      H₂.ends e = (MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).1,
        Γ.molRep (.inr b₀)))
    (hen2b : ∀ e, (∀ a, Γ.Unpinned q → q = .inl a → e ≠ .inr a) →
      (MolDot_G0 Γ p q).cls e ≠ none →
      ¬ (Γ.Unpinned q ∧ MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).2 = q) →
      H₂.ends e = (MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).1,
        MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).2))
    (hHi : H.int = H₂.int) (hHx : H.ext = H₂.ext) (hHe : H.ends = H₂.ends)
    (hHc : ∀ e, H.cls e = if (H₂.ends e).1 = (H₂.ends e).2 then none else H₂.cls e) :
    H.Transported (MolDot_add Γ p q).toMG' := by
  classical
  have E := Γ.toMG'_disjoint
  generalize hMp : Γ.molRep (.inr b₀) = Mp at hi2 hpin hen2a hen2b
  have hMpI : Mp ∈ Γ.toMG'.int := hMp ▸ MolDot_mem_int.2 ⟨b₀, rfl⟩
  have hμc : ∀ v, MolDot_mu Mp Mq v = v ∨ MolDot_mu Mp Mq v = Mp := by
    intro v
    unfold MolDot_mu
    split_ifs <;> simp
  have hμMp : MolDot_mu Mp Mq Mp = Mp := by
    unfold MolDot_mu
    split_ifs <;> rfl
  have hμext : ∀ v ∈ Γ.toMG'.ext, MolDot_mu Mp Mq v = v := by
    intro v hv
    unfold MolDot_mu
    rw [ite_eq_right]
    rintro rfl
    exact Finset.disjoint_left.1 E hMq1 hv
  have hfMp : (MolDot_add Γ p q).molRep Mp = (MolDot_add Γ p q).molRep (.inr b₀) := by
    rw [← hMp, MolDot_molRep_molRep]
  have hfμ : ∀ v, (MolDot_add Γ p q).molRep (MolDot_mu Mp Mq v) =
      (MolDot_add Γ p q).molRep v := by
    intro v
    unfold MolDot_mu
    split_ifs with h
    · rw [h, hMq3, hfMp]
    · rfl
  have hvtx : ∀ v, Γ.toMG'.IsVtx v → H.IsVtx (MolDot_mu Mp Mq v) := by
    rintro v (hv | hv)
    · exact Or.inl (by rw [hHi, hi2]; exact Finset.mem_image_of_mem _ hv)
    · exact Or.inr (by rw [hHx, hx2, hμext v hv]; exact hv)
  have hMpV : H.IsVtx Mp := hμMp ▸ hvtx Mp (Or.inl hMpI)
  have hinj : ∀ v w, Γ.toMG'.IsVtx v → Γ.toMG'.IsVtx w →
      (MolDot_add Γ p q).molRep v = (MolDot_add Γ p q).molRep w →
      MolDot_mu Mp Mq v = MolDot_mu Mp Mq w := by
    rintro v w (hv | hv) (hw | hw) h
    · obtain ⟨a, rfl⟩ := MolDot_mem_int.1 hv
      obtain ⟨a', rfl⟩ := MolDot_mem_int.1 hw
      rw [MolDot_molRep_molRep, MolDot_molRep_molRep] at h
      have := MolDot_inj hp hMq2 a a' h
      rw [hMp] at this
      exact this
    · obtain ⟨a, rfl⟩ := MolDot_mem_int.1 hv
      cases w with
      | inr _ => exact absurd (MolDot_mem_ext.1 hw) (by simp)
      | inl b =>
        rw [MolDot_molRep_molRep] at h
        exact absurd h (MolDot_molRep_inr_ne _ a b)
    · obtain ⟨a, rfl⟩ := MolDot_mem_int.1 hw
      cases v with
      | inr _ => exact absurd (MolDot_mem_ext.1 hv) (by simp)
      | inl b =>
        rw [MolDot_molRep_molRep] at h
        exact absurd h.symm (MolDot_molRep_inr_ne _ a b)
    · rw [hμext v hv, hμext w hw]
      cases v with
      | inr _ => exact absurd (MolDot_mem_ext.1 hv) (by simp)
      | inl b =>
        cases w with
        | inr _ => exact absurd (MolDot_mem_ext.1 hw) (by simp)
        | inl b' => exact h
  have hρ : ∀ u, ¬ (Γ.Unpinned q ∧ u = q) →
      (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom u) =
        (MolDot_add Γ p q).molRep (Γ.molRep (Γ.flatAtom u)) := by
    intro u hu
    rw [MolDot_molRep_molRep]
    refine MolDot_rho_add hp ?_
    rintro ⟨h1, h2⟩
    by_cases hU : Γ.Unpinned q
    · exact hu ⟨hU, hB1 hU u h2⟩
    · obtain ⟨b, hb⟩ := MolDot_block_of_not_unpinned hU h2
      exact MolDot_not_unpinned hb h1
  have hρq : (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom q) =
      (MolDot_add Γ p q).molRep Mp := by
    rw [hfMp]
    exact MolDot_rho_q hp
  have hqext : Γ.Unpinned q → q ∈ Γ.toMG'.ext := fun hU => MolDot_mem_ext.2 hU.1
  have hρself : Γ.Unpinned q → Γ.molRep (Γ.flatAtom q) = q := by
    intro hU
    rw [MolDot_flat_unpinned hU]
    obtain ⟨h1, -⟩ := hU
    cases q with
    | inl a => rfl
    | inr a => simp at h1
  have hρeq : Γ.Unpinned q → ∀ u, Γ.molRep (Γ.flatAtom u) = q → u = q := by
    intro hU u hu
    by_cases hu' : Γ.Unpinned u
    · rw [MolDot_flat_unpinned hu'] at hu
      obtain ⟨h1, -⟩ := hu'
      cases u with
      | inl a => exact hu
      | inr a => simp at h1
    · have hr := MolDot_flat_isRight hu'
      exfalso
      have h3 : (Γ.molRep (Γ.flatAtom u)).isRight = true := by
        rcases MolDot_molRep_cases Γ (Γ.flatAtom u) with ⟨a, ha, -⟩ | ⟨a, b, -, hb⟩
        · rw [ha] at hr
          simp at hr
        · rw [hb]
          rfl
      rw [hu] at h3
      have h4 := hU.1
      cases q <;> simp_all
  have hμq : Γ.Unpinned q → ∀ v, MolDot_mu Mp Mq v = q → v = q := by
    intro hU v hv
    rcases hμc v with h | h
    · rw [h] at hv
      exact hv
    · rw [h] at hv
      exact absurd (hv ▸ hMpI) (Finset.disjoint_right.1 E (hqext hU))
  have hρρ : ∀ x y, Γ.molRep (Γ.flatAtom x) = Γ.molRep (Γ.flatAtom y) →
      (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom x) =
        (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom y) := by
    intro x y h
    by_cases hx : Γ.Unpinned q ∧ x = q
    · have hy : y = q := hρeq hx.1 y (by rw [← h, hx.2, hρself hx.1])
      rw [hx.2, hy]
    · by_cases hy : Γ.Unpinned q ∧ y = q
      · have hx' : x = q := hρeq hy.1 x (by rw [h, hy.2, hρself hy.1])
        exact absurd ⟨hy.1, hx'⟩ hx
      · rw [hρ x hx, hρ y hy, h]
  -- the edges one by one
  have key : ∀ e, (MolDot_add Γ p q).toMG'.cls e = H.cls e ∧ (H.cls e ≠ none →
      H.IsVtx (H.ends e).1 ∧ H.IsVtx (H.ends e).2 ∧
      ((MolDot_add Γ p q).toMG'.ends e = ((MolDot_add Γ p q).molRep (H.ends e).1,
          (MolDot_add Γ p q).molRep (H.ends e).2) ∨
        (MolDot_add Γ p q).toMG'.ends e = ((MolDot_add Γ p q).molRep (H.ends e).2,
          (MolDot_add Γ p q).molRep (H.ends e).1))) := by
    have hnone : ∀ e, H₂.cls e = none → H.cls e = none := by
      intro e h
      rw [hHc]
      split_ifs <;> [rfl; exact h]
    rintro (j | a)
    · have hnp : ∀ a, Γ.Unpinned q → q = .inl a → (Sum.inl j : Fin _ ⊕ Fin k) ≠ .inr a :=
        fun _ _ _ => Sum.inl_ne_inr
      rcases MolDot_idx_cases Γ p q j with ⟨i, rfl⟩ | rfl
      · have hcl : H₂.cls (.inl (MolDot_idx Γ p q i)) = Γ.toMG'.cls (.inl i) := by
          rw [hcl2 _ hnp, MolDot_G0_cls_idx]
        have hGc := MolDot_cls_inl Γ i
        have hG'c := MolDot_cls_inl (MolDot_add Γ p q) (MolDot_idx Γ p q i)
        rw [MolDot_get_idx] at hG'c
        by_cases hk : Γ.comps[i].kind = .dot
        · have h0 : H.cls (.inl (MolDot_idx Γ p q i)) = none :=
            hnone _ (by rw [hcl, hGc, ite_eq_left hk])
          rw [h0, hG'c, ite_eq_left hk]
          exact ⟨rfl, fun h => absurd rfl h⟩
        · have hGe := MolDot_ends_inl Γ i hk
          have hk' : (MolDot_add Γ p q).comps[MolDot_idx Γ p q i].kind ≠ .dot := by
            rw [MolDot_get_idx]
            exact hk
          have hG'e := MolDot_ends_inl (MolDot_add Γ p q) (MolDot_idx Γ p q i) hk'
          rw [MolDot_get_idx] at hG'e
          have hG0e := MolDot_G0_ends_idx Γ p q i
          rw [hGe] at hG0e
          rw [ite_eq_right hk] at hGc hG'c
          have hxv := MolDot_molRep_vtx Γ (Γ.flatAtom Γ.comps[i].x)
          have hyv := MolDot_molRep_vtx Γ (Γ.flatAtom Γ.comps[i].y)
          have hQ' := fun hU => hQ hU (.inl i)
          rw [hGe] at hQ'
          rw [hG'c, hG'e]
          generalize Γ.comps[i].kind = κ at *
          generalize Γ.comps[i].x = x at *
          generalize Γ.comps[i].y = y at *
          by_cases hpres : Γ.toMG'.cls (.inl i) = none
          · have h0 := hnone _ (by rw [hcl, hpres])
            rw [h0]
            refine ⟨?_, fun h => absurd rfl h⟩
            rw [hGc] at hpres
            by_cases h1 : Γ.molRep (Γ.flatAtom x) = Γ.molRep (Γ.flatAtom y)
            · rw [ite_eq_left (hρρ x y h1)]
            · rw [ite_eq_right h1] at hpres
              rw [hpres]
              split_ifs <;> rfl
          · have hne : Γ.molRep (Γ.flatAtom x) ≠ Γ.molRep (Γ.flatAtom y) := by
              intro h
              rw [hGc, ite_eq_left h] at hpres
              exact hpres rfl
            have hcG : Γ.toMG'.cls (.inl i) = κ.mclass := by rw [hGc, ite_eq_right hne]
            have hG0c : (MolDot_G0 Γ p q).cls (.inl (MolDot_idx Γ p q i)) ≠ none := by
              rw [MolDot_G0_cls_idx]
              exact hpres
            by_cases hq : Γ.Unpinned q ∧ (x = q ∨ y = q)
            · obtain ⟨hU, hxy⟩ := hq
              have hρq' : Γ.molRep (Γ.flatAtom q) ∈ Γ.toMG'.ext := by
                rw [hρself hU]
                exact hqext hU
              -- the other end
              obtain ⟨o, ho, hoq, hends⟩ : ∃ o, o ≠ q ∧ Γ.molRep (Γ.flatAtom o) ∈ Γ.toMG'.int ∧
                  ((x = q ∧ y = o) ∨ (y = q ∧ x = o)) := by
                rcases hxy with hxq | hyq
                · have hyq : y ≠ q := fun h => hne (by rw [hxq, h])
                  refine ⟨y, hyq, ?_, Or.inl ⟨hxq, rfl⟩⟩
                  rcases hyv with h | h
                  · exact h
                  · have h1 : Γ.molRep (Γ.flatAtom x) ∈ Γ.toMG'.ext := by rw [hxq]; exact hρq'
                    have h2 := (hQ' hU hpres h1 h).1
                    rw [hxq, hρself hU] at h2
                    exact absurd rfl h2
                · have hxq : x ≠ q := fun h => hne (by rw [hyq, h])
                  refine ⟨x, hxq, ?_, Or.inr ⟨hyq, rfl⟩⟩
                  rcases hxv with h | h
                  · exact h
                  · have h1 : Γ.molRep (Γ.flatAtom y) ∈ Γ.toMG'.ext := by rw [hyq]; exact hρq'
                    have h2 := (hQ' hU hpres h h1).2
                    rw [hyq, hρself hU] at h2
                    exact absurd rfl h2
              have hoE : Γ.molRep (Γ.flatAtom o) ∉ Γ.toMG'.ext := Finset.disjoint_left.1 E hoq
              have hG0o : (MolDot_G0 Γ p q).ends (.inl (MolDot_idx Γ p q i)) =
                  (Γ.molRep (Γ.flatAtom o), q) := by
                rw [hG0e]
                unfold MolDot_or
                rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · rw [h1, h2, hρself hU, ite_eq_left (hqext hU)]
                · rw [h1, h2, hρself hU, ite_eq_right hoE]
              have hH2 := hen2a _ hnp hG0c hU (by rw [hG0o, hμext q (hqext hU)])
              rw [hG0o] at hH2
              have hHe' : H.ends (.inl (MolDot_idx Γ p q i)) =
                  (MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom o)), Mp) := by rw [hHe, hH2]
              have hHc' : H.cls (.inl (MolDot_idx Γ p q i)) =
                  if MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom o)) = Mp then none else κ.mclass := by
                rw [hHc, hH2, hcl, hcG]
              have hρo := hρ o (fun h => ho h.2)
              have h1 : (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom o) =
                  (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom q) ↔
                  MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom o)) = Mp := by
                rw [hρo, hρq]
                constructor
                · intro h
                  rw [hinj _ _ (Or.inl hoq) (Or.inl hMpI) h, hμMp]
                · intro h
                  rw [← hfμ, h]
              have hiff : (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom x) =
                  (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom y) ↔
                  MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom o)) = Mp := by
                rcases hends with ⟨h2, h3⟩ | ⟨h2, h3⟩
                · rw [h2, h3, eq_comm]
                  exact h1
                · rw [h2, h3]
                  exact h1
              rw [hHc']
              refine ⟨?_, fun hc => ?_⟩
              · by_cases h : MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom o)) = Mp
                · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
                · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]
              · rw [hHe']
                refine ⟨hvtx _ (Or.inl hoq), hMpV, ?_⟩
                rw [hfμ, ← hρo, ← hρq]
                rcases hends with ⟨h2, h3⟩ | ⟨h2, h3⟩
                · rw [h2, h3]
                  exact Or.inr rfl
                · rw [h2, h3]
                  exact Or.inl rfl
            · have hx' : ¬ (Γ.Unpinned q ∧ x = q) := fun h => hq ⟨h.1, Or.inl h.2⟩
              have hy' : ¬ (Γ.Unpinned q ∧ y = q) := fun h => hq ⟨h.1, Or.inr h.2⟩
              have hiff : (MolDot_add Γ p q).molRep (Γ.molRep (Γ.flatAtom x)) =
                  (MolDot_add Γ p q).molRep (Γ.molRep (Γ.flatAtom y)) ↔
                  MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom x)) =
                    MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom y)) := by
                constructor
                · exact hinj _ _ hxv hyv
                · intro h
                  rw [← hfμ, h, hfμ]
              have hcls' : (if (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom x) =
                    (MolDot_add Γ p q).molRep ((MolDot_add Γ p q).flatAtom y) then none
                    else κ.mclass) =
                  if MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom x)) =
                    MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom y)) then none else κ.mclass := by
                rw [hρ x hx', hρ y hy']
                by_cases h : MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom x)) =
                    MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom y))
                · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
                · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]
              rw [hcls']
              by_cases hxE : Γ.molRep (Γ.flatAtom x) ∈ Γ.toMG'.ext
              · have hG0x : (MolDot_G0 Γ p q).ends (.inl (MolDot_idx Γ p q i)) =
                    (Γ.molRep (Γ.flatAtom y), Γ.molRep (Γ.flatAtom x)) := by
                  rw [hG0e]
                  unfold MolDot_or
                  rw [ite_eq_left hxE]
                have hnq : ¬ (Γ.Unpinned q ∧ MolDot_mu Mp Mq
                    ((MolDot_G0 Γ p q).ends (.inl (MolDot_idx Γ p q i))).2 = q) := by
                  rintro ⟨hU, h⟩
                  rw [hG0x] at h
                  exact hq ⟨hU, Or.inl (hρeq hU x (hμq hU _ h))⟩
                have hH2 := hen2b _ hnp hG0c hnq
                rw [hG0x] at hH2
                have hHc' : H.cls (.inl (MolDot_idx Γ p q i)) =
                    if MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom x)) =
                      MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom y)) then none else κ.mclass := by
                  rw [hHc, hH2, hcl, hcG]
                  by_cases h : MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom x)) =
                      MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom y))
                  · rw [ite_eq_left h.symm, ite_eq_left h]
                  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
                rw [hHc']
                refine ⟨rfl, fun _ => ?_⟩
                rw [hHe, hH2, hρ x hx', hρ y hy', hfμ, hfμ]
                exact ⟨hvtx _ hyv, hvtx _ hxv, Or.inr rfl⟩
              · have hG0x : (MolDot_G0 Γ p q).ends (.inl (MolDot_idx Γ p q i)) =
                    (Γ.molRep (Γ.flatAtom x), Γ.molRep (Γ.flatAtom y)) := by
                  rw [hG0e]
                  unfold MolDot_or
                  rw [ite_eq_right hxE]
                have hnq : ¬ (Γ.Unpinned q ∧ MolDot_mu Mp Mq
                    ((MolDot_G0 Γ p q).ends (.inl (MolDot_idx Γ p q i))).2 = q) := by
                  rintro ⟨hU, h⟩
                  rw [hG0x] at h
                  exact hq ⟨hU, Or.inr (hρeq hU y (hμq hU _ h))⟩
                have hH2 := hen2b _ hnp hG0c hnq
                rw [hG0x] at hH2
                have hHc' : H.cls (.inl (MolDot_idx Γ p q i)) =
                    if MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom x)) =
                      MolDot_mu Mp Mq (Γ.molRep (Γ.flatAtom y)) then none else κ.mclass := by
                  rw [hHc, hH2, hcl, hcG]
                rw [hHc']
                refine ⟨rfl, fun _ => ?_⟩
                rw [hHe, hH2, hρ x hx', hρ y hy', hfμ, hfμ]
                exact ⟨hvtx _ hxv, hvtx _ hyv, Or.inl rfl⟩
      · have h0 : H.cls (.inl (MolDot_last Γ p q)) = none :=
          hnone _ (by rw [hcl2 _ hnp, MolDot_G0_cls_last])
        have hG' : (MolDot_add Γ p q).toMG'.cls (.inl (MolDot_last Γ p q)) = none := by
          rw [MolDot_cls_inl, MolDot_get_last]
          simp [mkC]
        rw [hG', h0]
        exact ⟨rfl, fun h => absurd rfl h⟩
    · by_cases hpa : Γ.Unpinned q ∧ q = .inl a
      · obtain ⟨h1, h2⟩ := hpin a hpa.1 hpa.2
        have hMpq : Mp ≠ q := fun h => Finset.disjoint_left.1 E hMpI (h ▸ hqext hpa.1)
        have hc : H.cls (.inr a) = some (pinClass a) := by rw [hHc, h2, ite_eq_right hMpq, h1]
        have hbq : (MolDot_add Γ p q).SameBlock (.inl a) (.inr b₀) :=
          hpa.2 ▸ (MolDot_sameBlock_pq Γ p q).symm.trans (MolDot_sameBlock_mono hp)
        obtain ⟨g1, g2⟩ := MolDot_pin_some hbq
        rw [hc, g1]
        refine ⟨rfl, fun _ => ?_⟩
        rw [hHe, h2, g2]
        have hfq : (MolDot_add Γ p q).molRep q = q := by
          rcases MolDot_molRep_cases (MolDot_add Γ p q) q with ⟨a', ha', hm⟩ | ⟨a', b', ha', -⟩
          · exact hm.trans ha'.symm
          · exact absurd (ha'.symm.trans hpa.2) (by simp)
        refine ⟨hMpV, Or.inr (by rw [hHx, hx2]; exact hqext hpa.1),
          Or.inl (Prod.ext hfMp.symm ?_)⟩
        change Sum.inl a = (MolDot_add Γ p q).molRep q
        rw [hfq]
        exact hpa.2.symm
      · have hnp : ∀ a', Γ.Unpinned q → q = .inl a' →
            (Sum.inr a : Fin (MolDot_add Γ p q).comps.length ⊕ Fin k) ≠ .inr a' := by
          intro a' hU hq' h
          cases h
          exact hpa ⟨hU, hq'⟩
        have hcl : H₂.cls (.inr a) = Γ.toMG'.cls (.inr a) := hcl2 _ hnp
        by_cases hun : Γ.Unpinned (.inl a)
        · have h0 := hnone _ (by rw [hcl, MolDot_pin_none hun])
          have hnb : ¬ Γ.SameBlock (.inl a) q := by
            intro h
            by_cases hU : Γ.Unpinned q
            · exact hpa ⟨hU, (hB1 hU _ h).symm⟩
            · obtain ⟨b, hb⟩ := MolDot_block_of_not_unpinned hU h
              exact MolDot_not_unpinned hb hun
          rw [h0, MolDot_pin_none (MolDot_unpinned_add hp hun hnb)]
          exact ⟨rfl, fun h => absurd rfl h⟩
        · obtain ⟨b, hb⟩ : ∃ b, Γ.SameBlock (.inl a) (.inr b) := by
            by_contra hn
            push Not at hn
            exact hun ⟨rfl, hn⟩
          obtain ⟨g1, g2⟩ := MolDot_pin_some hb
          obtain ⟨g1', g2'⟩ := MolDot_pin_some (MolDot_sameBlock_mono (p := p) (q := q) hb)
          have hbI : Γ.molRep (.inr b) ∈ Γ.toMG'.int := MolDot_mem_int.2 ⟨b, rfl⟩
          have hG0e : (MolDot_G0 Γ p q).ends (.inr a) = (Γ.molRep (.inr b), .inl a) := by
            change MolDot_or Γ.toMG'.ext (Γ.toMG'.ends (.inr a)) = _
            rw [g2]
            unfold MolDot_or
            rw [ite_eq_right (Finset.disjoint_left.1 E hbI)]
          have haE : (.inl a : Atom k n) ∈ Γ.toMG'.ext := MolDot_mem_ext.2 rfl
          have hH2 := hen2b (.inr a) hnp (by change Γ.toMG'.cls (.inr a) ≠ none; rw [g1]; simp)
            (by
              rintro ⟨hU, h⟩
              rw [hG0e] at h
              exact hpa ⟨hU, by rw [← h, hμext _ haE]⟩)
          rw [hG0e, hμext _ haE] at hH2
          have hμb : MolDot_mu Mp Mq (Γ.molRep (.inr b)) ≠ .inl a := by
            rcases hμc (Γ.molRep (.inr b)) with h | h <;> rw [h]
            · exact MolDot_molRep_inr_ne _ _ _
            · rw [← hMp]
              exact MolDot_molRep_inr_ne _ _ _
          have hc : H.cls (.inr a) = some (pinClass a) := by
            rw [hHc, hH2, ite_eq_right hμb, hcl, g1]
          rw [hc, g1']
          refine ⟨rfl, fun _ => ?_⟩
          rw [hHe, hH2, g2', hfμ, MolDot_molRep_molRep]
          exact ⟨hvtx _ (Or.inl hbI), Or.inr (by rw [hHx, hx2]; exact haE), Or.inl rfl⟩
  refine ⟨(MolDot_add Γ p q).molRep, id, fun _ _ _ _ h => h, ?_, ?_, ?_,
    fun e he => ⟨((key e).2 he).1, ((key e).2 he).2.1⟩, fun e _ => (key e).1,
    fun e he => ((key e).2 he).2.2, fun e he => ?_⟩
  · -- injectivity on the vertices
    have hpre : ∀ x ∈ (↑H.int ∪ ↑H.ext : Set (Atom k n)), ∃ v, Γ.toMG'.IsVtx v ∧
        x = MolDot_mu Mp Mq v := by
      intro x hx
      rcases hx with hx | hx
      · rw [Finset.mem_coe, hHi, hi2] at hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
        exact ⟨v, Or.inl hv, rfl⟩
      · rw [Finset.mem_coe, hHx, hx2] at hx
        exact ⟨x, Or.inr hx, (hμext x hx).symm⟩
    intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := hpre x hx
    obtain ⟨w, hw, rfl⟩ := hpre y hy
    rw [hfμ, hfμ] at hxy
    exact hinj v w hv hw hxy
  · ext y
    rw [MolDot_mem_int, hHi, hi2, Finset.image_image]
    constructor
    · rintro ⟨a, rfl⟩
      refine Finset.mem_image.2 ⟨Γ.molRep (.inr a), MolDot_mem_int.2 ⟨a, rfl⟩, ?_⟩
      simp only [Function.comp]
      rw [hfμ, MolDot_molRep_molRep]
    · intro hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨a, rfl⟩ := MolDot_mem_int.1 hv
      refine ⟨a, ?_⟩
      simp only [Function.comp]
      rw [hfμ, MolDot_molRep_molRep]
  · ext y
    rw [MolDot_mem_ext, hHx, hx2]
    constructor
    · intro hy
      cases y with
      | inr _ => simp at hy
      | inl b => exact Finset.mem_image.2 ⟨.inl b, MolDot_mem_ext.2 rfl, rfl⟩
    · intro hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
      cases v with
      | inr _ => simp [MolDot_mem_ext] at hv
      | inl b => rfl
  · by_contra hc
    rw [(key e).1] at hc
    exact he e hc rfl

end Final

/-! ## The edges at an unpinned external vertex moved to a molecule -/

section Ext

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- The edges at the external vertex `q` (each from an internal vertex, red at `⊖`, blue solid or
diffusive at `⊕`, diffusive at `⊗`) moved to the internal vertex `M`, together with a new edge
`π` from `M` to `q` of the class `pinClass a₀`: a red edge set by `MGraph.CarStep.red` at `⊖`;
operation (B) or [II, Lemma 5.12 (v)] on one edge at `⊕` and `⊗`, the others moved by
`MolDot_moveList`. -/
private theorem MolDot_extChain [Finite E] (K : MGraph V E) (M q : V) (s π : E) (a₀ : Fin 3)
    (hM : M ∈ K.int) (hq : q ∈ K.ext) (hπ : K.cls π = none) (hs : K.cls s = none) (hsπ : s ≠ π)
    (hQ : ∀ e, K.cls e ≠ none → (K.ends e).2 = q → (K.ends e).1 ∈ K.int ∧
      ((K.cls e = some .minus ∧ a₀ = 2) ∨ (K.cls e = some .plus ∧ a₀ = 1) ∨
        (K.cls e = some .diff ∧ a₀ ≠ 2)))
    (hex : a₀ ≠ 2 → ∃ e, K.cls e ≠ none ∧ (K.ends e).2 = q) :
    ∃ K', Relation.ReflTransGen MGraph.CarStep K K' ∧ K'.int = K.int ∧ K'.ext = K.ext ∧
      (∀ x, K'.cls x = if x = π then some (pinClass a₀) else K.cls x) ∧ K'.ends π = (M, q) ∧
      (∀ e, K.cls e ≠ none → (K.ends e).2 = q → K'.ends e = ((K.ends e).1, M)) ∧
      (∀ e, e ≠ π → e ≠ s → ¬ (K.cls e ≠ none ∧ (K.ends e).2 = q) → K'.ends e = K.ends e) := by
  classical
  have := Fintype.ofFinite E
  set Q := Finset.univ.filter (fun e => K.cls e ≠ none ∧ (K.ends e).2 = q) with hQdef
  have memQ : ∀ e, e ∈ Q ↔ K.cls e ≠ none ∧ (K.ends e).2 = q := by
    intro e
    simp [hQdef]
  have hQs : ∀ e ∈ Q, e ≠ s := by
    intro e he h
    rw [h] at he
    exact ((memQ s).1 he).1 hs
  have hQπ : ∀ e ∈ Q, e ≠ π := by
    intro e he h
    rw [h] at he
    exact ((memQ π).1 he).1 hπ
  have hπQ : π ∉ Q := fun h => hQπ π h rfl
  have hsQ : s ∉ Q := fun h => hQs s h rfl
  by_cases h2 : a₀ = 2
  · -- `⊖`: a red edge from `M` to `q`, and the red edges moved
    have hpc : pinClass a₀ = .minus := by subst h2; rfl
    set K₀ := K.setEdge π M q (some .minus) with hK₀
    have c₀ : MGraph.CarStep K K₀ := .red _ _ _ _ _ (Or.inl hπ) (Or.inr rfl)
    have hK₀e : ∀ x, x ≠ π → K₀.ends x = K.ends x := fun x hx => by simp [hK₀, MGraph.setEdge, hx]
    have hK₀c : ∀ x, K₀.cls x = if x = π then some .minus else K.cls x := by
      intro x
      by_cases hx : x = π
      · subst hx
        simp [hK₀, MGraph.setEdge]
      · simp [hK₀, MGraph.setEdge, hx]
    have hK₀π : K₀.ends π = (M, q) := by simp [hK₀, MGraph.setEdge]
    obtain ⟨K', c', i', x', cl', ee', eo'⟩ := MolDot_moveList M q s π Q.toList K₀
      (Finset.nodup_toList Q) hM hq (by rw [hK₀c, ite_eq_right hsπ]; exact hs) hsπ hK₀π
      (fun e he => by
        rw [Finset.mem_toList] at he
        obtain ⟨hc, he2⟩ := (memQ e).1 he
        have hne := hQπ e he
        obtain ⟨hi, hcl⟩ := hQ e hc he2
        refine ⟨hQs e he, hne, by rw [hK₀e e hne]; exact hi, by rw [hK₀e e hne]; exact he2,
          Or.inl ?_⟩
        rw [hK₀c, ite_eq_right hne]
        rcases hcl with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact h
        · rw [h2] at h; exact absurd h (by decide)
        · exact absurd h2 h)
    refine ⟨K', (Relation.ReflTransGen.single c₀).trans c', i', x', fun x => ?_, ?_,
      fun e hc he2 => ?_, fun e hπ' hs' hn => ?_⟩
    · rw [cl', hK₀c, hpc]
    · rw [eo' π (by rw [Finset.mem_toList]; exact hπQ) (Ne.symm hsπ), hK₀π]
    · have he : e ∈ Q := (memQ e).2 ⟨hc, he2⟩
      rw [ee' e (by rw [Finset.mem_toList]; exact he), hK₀e e (hQπ e he)]
    · rw [eo' e (by rw [Finset.mem_toList]; exact fun h => hn ((memQ e).1 h)) hs', hK₀e e hπ']
  · -- `⊕` and `⊗`: operation (B) or [II, Lemma 5.12 (v)] on one edge, the others moved
    have hpc1 : pinClass a₀ = .plus ∨ pinClass a₀ = .dot := by
      fin_cases a₀
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd rfl h2
    have hpc2 : pinClass a₀ ≠ .minus := by
      rcases hpc1 with h | h <;> rw [h] <;> simp
    obtain ⟨e₀, he₀1, he₀2⟩ := hex h2
    have he₀Q : e₀ ∈ Q := (memQ e₀).2 ⟨he₀1, he₀2⟩
    have he₀π : e₀ ≠ π := hQπ e₀ he₀Q
    have hπe₀ : π ≠ e₀ := Ne.symm he₀π
    obtain ⟨hi₀, hcl₀⟩ := hQ e₀ he₀1 he₀2
    have hq₀ : (K.ends e₀).2 ∈ K.ext := he₀2 ▸ hq
    obtain ⟨K₀, c₀, i₀, x₀, hK₀c, hK₀π, hK₀e₀, hK₀e⟩ : ∃ K₀, MGraph.CarStep K K₀ ∧
        K₀.int = K.int ∧ K₀.ext = K.ext ∧
        (∀ x, K₀.cls x = if x = π then some (pinClass a₀) else K.cls x) ∧
        K₀.ends π = (M, q) ∧ K₀.ends e₀ = ((K.ends e₀).1, M) ∧
        ∀ x, x ≠ e₀ → x ≠ π → K₀.ends x = K.ends x := by
      rcases hcl₀ with ⟨-, h⟩ | ⟨hc, h⟩ | ⟨hc, -⟩
      · exact absurd h h2
      · have hpc : pinClass a₀ = .plus := by subst h; rfl
        refine ⟨K.split e₀ π M, .split _ _ _ _ hc (Or.inl hi₀) (Or.inr hq₀) (Or.inl hi₀) he₀π hπ hM,
          rfl, rfl, fun x => ?_, by simp [MGraph.split, hπe₀, he₀2], by simp [MGraph.split],
          fun x hx hx' => by simp [MGraph.split, hx, hx']⟩
        by_cases hx : x = π
        · subst hx
          simp [MGraph.split, hc, hpc]
        · simp [MGraph.split, hx]
      · refine ⟨(K.split e₀ π M).recolor π (some (pinClass a₀)),
          .splitExt _ _ _ _ _ hc hi₀ hq₀ he₀π hπ hM hpc1, rfl, rfl, fun x => ?_,
          by simp [MGraph.split, MGraph.recolor, hπe₀, he₀2],
          by simp [MGraph.split, MGraph.recolor],
          fun x hx hx' => by simp [MGraph.split, MGraph.recolor, hx, hx']⟩
        by_cases hx : x = π
        · subst hx
          simp [MGraph.recolor]
        · simp [MGraph.split, MGraph.recolor, hx]
    obtain ⟨K', c', i', x', cl', ee', eo'⟩ := MolDot_moveList M q s π (Q.erase e₀).toList K₀
      (Finset.nodup_toList _) (by rw [i₀]; exact hM) (by rw [x₀]; exact hq)
      (by rw [hK₀c, ite_eq_right hsπ]; exact hs) hsπ hK₀π
      (fun e he => by
        rw [Finset.mem_toList, Finset.mem_erase] at he
        obtain ⟨hee₀, he⟩ := he
        obtain ⟨hc, he2⟩ := (memQ e).1 he
        have hne := hQπ e he
        obtain ⟨hi, hcl⟩ := hQ e hc he2
        refine ⟨hQs e he, hne, by rw [hK₀e e hee₀ hne, i₀]; exact hi,
          by rw [hK₀e e hee₀ hne]; exact he2, Or.inr ⟨?_, ?_⟩⟩
        · rw [hK₀c, ite_eq_right hne]
          rcases hcl with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h h2
          · exact Or.inl h
          · exact Or.inr h
        · rw [hK₀c, ite_eq_left rfl]
          exact ⟨by simp, by simpa using hpc2⟩)
    refine ⟨K', (Relation.ReflTransGen.single c₀).trans c', i'.trans i₀, x'.trans x₀,
      fun x => ?_, ?_, fun e hc he2 => ?_, fun e hπ' hs' hn => ?_⟩
    · rw [cl', hK₀c]
    · rw [eo' π (by simp [hπQ]) (Ne.symm hsπ), hK₀π]
    · have he : e ∈ Q := (memQ e).2 ⟨hc, he2⟩
      by_cases hee₀ : e = e₀
      · subst hee₀
        rw [eo' e (by simp) (hQs e he), hK₀e₀]
      · rw [ee' e (by simp [hee₀, he]), hK₀e e hee₀ (hQπ e he)]
    · have hnQ : e ∉ Q := fun h => hn ((memQ e).1 h)
      have hee₀ : e ≠ e₀ := fun h => hnQ (h ▸ he₀Q)
      rw [eo' e (by simp [hnQ]) hs', hK₀e e hee₀ hπ']

end Ext

/-! ## [II, Lemma 5.10] for one dotted edge: the carried molecular graph -/

section AddDot

/-- The kinds of the edges of the molecular graph other than dotted and ghost edges: blue and red
solid edges and diffusive edges. -/
private theorem MolDot_kind_cases (κ : Kind) (h : κ.mclass ≠ none) (hd : κ ≠ .dot)
    (hg : κ ≠ .ghost) :
    κ = .G .plus ∨ κ = .G .minus ∨ (κ.isDiffusive = true ∧ κ.mclass = some .diff) := by
  cases κ with
  | G c => cases c <;> simp
  | aux j r b => cases b <;> simp_all [Kind.mclass, Kind.isDiffusive]
  | ghost => exact absurd rfl hg
  | dot => exact absurd rfl hd
  | theta o => simp [Kind.mclass, Kind.isDiffusive]
  | thetaErr _ _ => simp [Kind.mclass, Kind.isDiffusive]
  | _ => simp [Kind.mclass] at h

private theorem MolDot_diff_kind (κ : Kind) (h : κ.isDiffusive = true) :
    κ.mclass = some .diff ∧ κ ≠ .dot := by
  cases κ <;> simp_all [Kind.isDiffusive, Kind.mclass]

variable {k n : ℕ}

/-- The representative of an internal atom of the block normal form is an internal vertex. -/
private theorem MolDot_rho_int {Δ : Graph k n} {u : Atom k n}
    (h : (Δ.flatAtom u).isRight = true) : Δ.molRep (Δ.flatAtom u) ∈ Δ.toMG'.int := by
  cases hf : Δ.flatAtom u with
  | inl a =>
    rw [hf] at h
    simp at h
  | inr b => exact MolDot_mem_int.2 ⟨b, rfl⟩

/-- Only the external atom `a₀` itself is read at the external vertex `a₀`. -/
private theorem MolDot_rho_eq {Δ : Graph k n} {a₀ : Fin k} {u : Atom k n}
    (h : Δ.molRep (Δ.flatAtom u) = .inl a₀) : u = .inl a₀ := by
  by_cases hu : Δ.Unpinned u
  · rw [MolDot_flat_unpinned hu] at h
    obtain ⟨h1, -⟩ := hu
    cases u with
    | inl a => exact h
    | inr a => simp at h1
  · have := MolDot_rho_int (MolDot_flat_isRight hu)
    rw [h] at this
    exact absurd ((MolDot_mem_ext (Γ := Δ) (v := .inl a₀)).2 rfl)
      (Finset.disjoint_left.1 Δ.toMG'_disjoint this)

/-- A component of the molecular graph between an unpinned external atom and an atom read at an
internal atom is a present edge of `Graph.toMG'`. -/
private theorem MolDot_present {Γ : Graph k n} {a₀ : Fin k} (hU : Γ.Unpinned (.inl a₀))
    (i : Fin Γ.comps.length) (hk : Γ.comps[i].kind ≠ .dot) (hm : Γ.comps[i].kind.mclass ≠ none)
    {o : Atom k n} (ho : (Γ.flatAtom o).isRight = true)
    (hends : (Γ.comps[i].x = .inl a₀ ∧ Γ.comps[i].y = o) ∨
      (Γ.comps[i].y = .inl a₀ ∧ Γ.comps[i].x = o)) :
    Γ.toMG'.cls (.inl i) ≠ none := by
  have hq : Γ.molRep (Γ.flatAtom (.inl a₀)) = .inl a₀ := by rw [MolDot_flat_unpinned hU]; rfl
  have hne : Γ.molRep (Γ.flatAtom o) ≠ .inl a₀ := fun h =>
    Finset.disjoint_left.1 Γ.toMG'_disjoint (MolDot_rho_int ho) (h ▸ MolDot_mem_ext.2 rfl)
  rw [MolDot_cls_inl, ite_eq_right hk]
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hq, ite_eq_right (Ne.symm hne)]
    exact hm
  · rw [h1, h2, hq, ite_eq_right hne]
    exact hm

/-- The present edges of `Graph.toMG'` at an unpinned external atom `a₀`, under the charge pattern
of the block normal form, the clause on the external atoms and without ghost edges: the other end
is read at an internal atom, and the edge is red at `⊖`, blue solid at `⊕`, or diffusive at `⊗` and
`⊕`. -/
private theorem MolDot_atq {Γ : Graph 3 n} (hC : Γ.ColourInvB) (hE : Γ.ExtClause)
    (hG : Γ.NoGhost) {a₀ : Fin 3} (hU : Γ.Unpinned (.inl a₀)) (i : Fin Γ.comps.length)
    (hc : Γ.toMG'.cls (.inl i) ≠ none)
    (hq : Γ.comps[i].x = .inl a₀ ∨ Γ.comps[i].y = .inl a₀) :
    (∃ o, ((Γ.comps[i].x = .inl a₀ ∧ Γ.comps[i].y = o) ∨
        (Γ.comps[i].y = .inl a₀ ∧ Γ.comps[i].x = o)) ∧ (Γ.flatAtom o).isRight = true) ∧
      ((Γ.toMG'.cls (.inl i) = some .minus ∧ a₀ = 2) ∨
        (Γ.toMG'.cls (.inl i) = some .plus ∧ a₀ = 1) ∨
        (Γ.toMG'.cls (.inl i) = some .diff ∧ a₀ ≠ 2)) := by
  have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
  have hcls := MolDot_cls_inl Γ i
  generalize Γ.comps[i] = c at *
  have hk : c.kind ≠ .dot := fun h => hc (by rw [hcls, ite_eq_left h])
  rw [ite_eq_right hk] at hcls
  have hne : Γ.molRep (Γ.flatAtom c.x) ≠ Γ.molRep (Γ.flatAtom c.y) := fun h =>
    hc (by rw [hcls, ite_eq_left h])
  rw [ite_eq_right hne] at hcls
  have hm : c.kind.mclass ≠ none := fun h => hc (by rw [hcls, h])
  have hfc : Γ.flatComp c = { c with x := Γ.flatAtom c.x, y := Γ.flatAtom c.y } := by
    simp [Graph.flatComp, hk]
  have hCI := hC (Γ.flatComp c) (List.mem_map_of_mem hmem)
  rw [hfc] at hCI
  have hfq : Γ.flatAtom (.inl a₀) = .inl a₀ := MolDot_flat_unpinned hU
  obtain ⟨-, -, E3, E4, E5⟩ := hE
  have ha : a₀ = 0 ∨ a₀ = 1 ∨ a₀ = 2 := by fin_cases a₀ <;> simp
  rcases MolDot_kind_cases _ hm hk (hG _ hmem) with hκ | hκ | ⟨hd, hκ⟩
  · have h1 := hCI.1 (by rw [hκ]; rfl)
    have hx : c.x ≠ .inl a₀ := fun h => by
      have := h1.1
      rw [h, hfq] at this
      simp at this
    have hy : c.y = .inl a₀ := hq.resolve_left hx
    refine ⟨⟨c.x, Or.inr ⟨hy, rfl⟩, h1.1⟩, ?_⟩
    rw [hcls, hκ]
    dsimp only at h1
    rw [hy, hfq] at h1
    rcases ha with rfl | rfl | rfl
    · exact absurd rfl h1.2.1
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd ((h1.2.2.2 rfl).symm.trans hκ) (by simp)
  · have h1 := hCI.1 (by rw [hκ]; rfl)
    have hx : c.x ≠ .inl a₀ := fun h => by
      have := h1.1
      rw [h, hfq] at this
      simp at this
    have hy : c.y = .inl a₀ := hq.resolve_left hx
    refine ⟨⟨c.x, Or.inr ⟨hy, rfl⟩, h1.1⟩, ?_⟩
    rw [hcls, hκ]
    dsimp only at h1
    rw [hy, hfq] at h1
    rcases ha with rfl | rfl | rfl
    · exact absurd rfl h1.2.1
    · exact absurd ((h1.2.2.1 rfl).symm.trans hκ) (by simp)
    · exact Or.inl ⟨rfl, rfl⟩
  · have hdp : Γ.DiffToPinned (.inl a₀) → ∃ o, ((c.x = .inl a₀ ∧ c.y = o) ∨
        (c.y = .inl a₀ ∧ c.x = o)) ∧ (Γ.flatAtom o).isRight = true := by
      intro hD
      obtain ⟨hD1, hD2⟩ := hD c hmem hd
      rcases hq with hx | hy
      · exact ⟨c.y, Or.inl ⟨hx, rfl⟩, MolDot_flat_isRight (hD1 hx)⟩
      · exact ⟨c.x, Or.inr ⟨hy, rfl⟩, MolDot_flat_isRight (hD2 hy)⟩
    rcases ha with rfl | rfl | rfl
    · exact ⟨hdp (E3 hU).2, Or.inr (Or.inr ⟨by rw [hcls, hκ], by decide⟩)⟩
    · exact ⟨hdp (E5 hU).2.1, Or.inr (Or.inr ⟨by rw [hcls, hκ], by decide⟩)⟩
    · obtain ⟨h1, h2⟩ := (E4 hU).1 c hmem hd
      rcases hq with h | h
      · exact absurd h h1
      · exact absurd h h2

/-- At an unpinned `⊗` or `⊕` there is a present edge of `Graph.toMG'`. -/
private theorem MolDot_atq_ex {Γ : Graph 3 n} (hC : Γ.ColourInvB) (hE : Γ.ExtClause)
    {a₀ : Fin 3} (hU : Γ.Unpinned (.inl a₀)) (h2 : a₀ ≠ 2) :
    ∃ i : Fin Γ.comps.length, Γ.toMG'.cls (.inl i) ≠ none ∧
      (Γ.comps[i].x = .inl a₀ ∨ Γ.comps[i].y = .inl a₀) := by
  obtain ⟨-, -, E3, -, E5⟩ := hE
  have hdiff : Γ.HasDiffToPinned (.inl a₀) → ∃ i : Fin Γ.comps.length,
      Γ.toMG'.cls (.inl i) ≠ none ∧ (Γ.comps[i].x = .inl a₀ ∨ Γ.comps[i].y = .inl a₀) := by
    rintro ⟨c, hc, hd, hxy⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
    obtain ⟨hm, hk⟩ := MolDot_diff_kind _ hd
    have hm' : Γ.comps[j].kind.mclass ≠ none := by rw [hm]; simp
    refine ⟨⟨j, hj⟩, ?_, ?_⟩
    · rcases hxy with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · exact MolDot_present hU ⟨j, hj⟩ hk hm' (MolDot_flat_isRight hy) (Or.inl ⟨hx, rfl⟩)
      · exact MolDot_present hU ⟨j, hj⟩ hk hm' (MolDot_flat_isRight hx) (Or.inr ⟨hy, rfl⟩)
    · rcases hxy with ⟨hx, -⟩ | ⟨hy, -⟩
      · exact Or.inl hx
      · exact Or.inr hy
  have ha : a₀ = 0 ∨ a₀ = 1 := by fin_cases a₀ <;> simp_all
  rcases ha with rfl | rfl
  · exact hdiff (E3 hU).1
  · rcases (E5 hU).1 with ⟨c, hc, hκ, hxy⟩ | h
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
      have hk : Γ.comps[j].kind ≠ .dot := by rw [hκ]; simp
      have hfc : Γ.flatComp Γ.comps[j] =
          { Γ.comps[j] with x := Γ.flatAtom Γ.comps[j].x, y := Γ.flatAtom Γ.comps[j].y } := by
        simp [Graph.flatComp, hk]
      have hCI := hC (Γ.flatComp Γ.comps[j]) (List.mem_map_of_mem hc)
      rw [hfc] at hCI
      have h1 := (hCI.1 (by dsimp only; rw [hκ]; rfl)).1
      dsimp only at h1
      have hx : Γ.comps[j].x ≠ .inl 1 := fun h => by
        rw [h, MolDot_flat_unpinned hU] at h1
        simp at h1
      have hy := hxy.resolve_left hx
      have hm' : Γ.comps[j].kind.mclass ≠ none := by rw [hκ]; simp [Kind.mclass]
      exact ⟨⟨j, hj⟩, MolDot_present hU ⟨j, hj⟩ hk hm' h1 (Or.inr ⟨hy, rfl⟩), Or.inr hy⟩
    · exact hdiff h

end AddDot

/-- [II, Lemma 5.10] for one dotted edge `p = q` with `p` in a block with an internal atom, in
the block reading: the molecular graph of the new graph is carried from that of `Γ`. -/
private theorem MolDot_addDot_flat {n : ℕ} {Γ : Graph 3 n} {p q : Atom 3 n} {b₀ : Fin n}
    (hC : Γ.ColourInvB) (hE : Γ.ExtClause) (hG : Γ.NoGhost) (hp : Γ.SameBlock p (.inr b₀)) :
    Γ.FlatCarried (MolDot_add Γ p q) := by
  classical
  have E := Γ.toMG'_disjoint
  have hMpI : Γ.molRep (.inr b₀) ∈ Γ.toMG'.int := MolDot_mem_int.2 ⟨b₀, rfl⟩
  -- the molecule reachable from `q`
  obtain ⟨Mq, hMq1, hMq2, hMq3⟩ : ∃ Mq ∈ Γ.toMG'.int,
      (∀ a, Γ.molGraph.Reachable q (.inr a) → Γ.molRep (.inr a) = Mq) ∧
      (MolDot_add Γ p q).molRep Mq = (MolDot_add Γ p q).molRep (.inr b₀) := by
    by_cases h : ∃ a, Γ.molGraph.Reachable q (.inr a)
    · obtain ⟨a₁, ha₁⟩ := h
      refine ⟨Γ.molRep (.inr a₁), MolDot_mem_int.2 ⟨a₁, rfl⟩, fun a ha =>
        (MolDot_molRep_eq_iff Γ _ _).2 (Or.inr ⟨rfl, rfl, ha.symm.trans ha₁⟩), ?_⟩
      rw [MolDot_molRep_molRep]
      refine (MolDot_molRep_eq_iff _ _ _).2 (Or.inr ⟨rfl, rfl, ?_⟩)
      have h1 : (MolDot_add Γ p q).molGraph.Reachable (.inr a₁) q :=
        (MolDot_molReach_add Γ p q _ _).2 (Or.inl ha₁.symm)
      have h2 : (MolDot_add Γ p q).molGraph.Reachable q p :=
        SimpleGraph.Reachable.mono (MolDot_dot_le_mol _) (MolDot_sameBlock_pq Γ p q).symm
      have h3 : (MolDot_add Γ p q).molGraph.Reachable p (.inr b₀) :=
        SimpleGraph.Reachable.mono (MolDot_dot_le_mol _) (MolDot_sameBlock_mono hp)
      exact h1.trans (h2.trans h3)
    · push Not at h
      exact ⟨Γ.molRep (.inr b₀), hMpI, fun a ha => absurd ha (h a), MolDot_molRep_molRep Γ p q _⟩
  have hμext : ∀ v ∈ Γ.toMG'.ext, MolDot_mu (Γ.molRep (.inr b₀)) Mq v = v := by
    intro v hv
    unfold MolDot_mu
    rw [ite_eq_right]
    rintro rfl
    exact Finset.disjoint_left.1 E hMq1 hv
  have hμq : ∀ v, MolDot_mu (Γ.molRep (.inr b₀)) Mq v = q → Γ.Unpinned q → v = q := by
    intro v hv hU
    unfold MolDot_mu at hv
    split_ifs at hv
    · exact absurd (hv ▸ hMpI) (Finset.disjoint_right.1 E (MolDot_mem_ext.2 hU.1))
    · exact hv
  have hB1 : Γ.Unpinned q → ∀ u, Γ.SameBlock u q → u = q := by
    intro hU u hu
    by_contra hne
    obtain ⟨b, hb⟩ := hE.1 u q hne hu
    exact hU.2 b (hu.symm.trans hb)
  have hQ : Γ.Unpinned q → ∀ e, Γ.toMG'.cls e ≠ none → (Γ.toMG'.ends e).1 ∈ Γ.toMG'.ext →
      (Γ.toMG'.ends e).2 ∈ Γ.toMG'.ext → (Γ.toMG'.ends e).1 ≠ q ∧ (Γ.toMG'.ends e).2 ≠ q := by
    intro hU e hc h1 h2
    obtain ⟨a₀, hq0⟩ : ∃ a₀, q = .inl a₀ := by
      cases q with
      | inl a => exact ⟨a, rfl⟩
      | inr a => exact absurd hU.1 (by simp)
    rw [hq0] at hU ⊢
    rcases e with i | a
    · have hk : Γ.comps[i].kind ≠ .dot := fun h => hc (by rw [MolDot_cls_inl, ite_eq_left h])
      rw [MolDot_ends_inl Γ i hk] at h1 h2 ⊢
      constructor
      · intro hx
        obtain ⟨⟨o, ho, hor⟩, -⟩ := MolDot_atq hC hE hG hU i hc (Or.inl (MolDot_rho_eq hx))
        rcases ho with ⟨-, h⟩ | ⟨-, h⟩
        · rw [h] at h2
          exact Finset.disjoint_left.1 E (MolDot_rho_int hor) h2
        · rw [h] at h1
          exact Finset.disjoint_left.1 E (MolDot_rho_int hor) h1
      · intro hy
        obtain ⟨⟨o, ho, hor⟩, -⟩ := MolDot_atq hC hE hG hU i hc (Or.inr (MolDot_rho_eq hy))
        rcases ho with ⟨-, h⟩ | ⟨-, h⟩
        · rw [h] at h2
          exact Finset.disjoint_left.1 E (MolDot_rho_int hor) h2
        · rw [h] at h1
          exact Finset.disjoint_left.1 E (MolDot_rho_int hor) h1
    · by_cases hun : Γ.Unpinned (.inl a)
      · exact absurd (MolDot_pin_none hun) hc
      · obtain ⟨b, hb⟩ : ∃ b, Γ.SameBlock (.inl a) (.inr b) := by
          by_contra hn
          push Not at hn
          exact hun ⟨rfl, hn⟩
        rw [(MolDot_pin_some hb).2] at h1
        exact absurd h1 (Finset.disjoint_left.1 E (MolDot_mem_int.2 ⟨b, rfl⟩))
  -- operation (A)
  set H₁ := (MolDot_G0 Γ p q).merge (Γ.molRep (.inr b₀)) Mq with hH₁
  have c₁ : MGraph.CarStep (MolDot_G0 Γ p q) H₁ := .merge _ _ _ hMpI hMq1
  have hH₁i : H₁.int = Γ.toMG'.int.image (MolDot_mu (Γ.molRep (.inr b₀)) Mq) := rfl
  have hH₁x : H₁.ext = Γ.toMG'.ext := by
    ext v
    change v ∈ Γ.toMG'.ext.image (MolDot_mu (Γ.molRep (.inr b₀)) Mq) ↔ _
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hμext w hw]
      exact hw
    · intro hv
      exact ⟨v, hv, hμext v hv⟩
  have hH₁c : ∀ e, H₁.cls e = (MolDot_G0 Γ p q).cls e := fun e => rfl
  have hH₁e : ∀ e, H₁.ends e = (MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).1,
      MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).2) := fun e => rfl
  -- the edges at an unpinned `q`
  obtain ⟨H₂, c₂, hi2, hx2, hpin, hcl2, hen2a, hen2b⟩ : ∃ H₂,
      Relation.ReflTransGen MGraph.CarStep H₁ H₂ ∧
      H₂.int = Γ.toMG'.int.image (MolDot_mu (Γ.molRep (.inr b₀)) Mq) ∧ H₂.ext = Γ.toMG'.ext ∧
      (∀ a, Γ.Unpinned q → q = .inl a →
        H₂.cls (.inr a) = some (pinClass a) ∧ H₂.ends (.inr a) = (Γ.molRep (.inr b₀), q)) ∧
      (∀ e, (∀ a, Γ.Unpinned q → q = .inl a → e ≠ .inr a) →
        H₂.cls e = (MolDot_G0 Γ p q).cls e) ∧
      (∀ e, (∀ a, Γ.Unpinned q → q = .inl a → e ≠ .inr a) →
        (MolDot_G0 Γ p q).cls e ≠ none → Γ.Unpinned q →
        MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).2 = q →
        H₂.ends e = (MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).1,
          Γ.molRep (.inr b₀))) ∧
      (∀ e, (∀ a, Γ.Unpinned q → q = .inl a → e ≠ .inr a) →
        (MolDot_G0 Γ p q).cls e ≠ none →
        ¬ (Γ.Unpinned q ∧ MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).2 = q) →
        H₂.ends e = (MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).1,
          MolDot_mu (Γ.molRep (.inr b₀)) Mq ((MolDot_G0 Γ p q).ends e).2)) := by
    by_cases hU : Γ.Unpinned q
    · obtain ⟨a₀, hq0⟩ : ∃ a₀, q = .inl a₀ := by
        cases q with
        | inl a => exact ⟨a, rfl⟩
        | inr a => exact absurd hU.1 (by simp)
      have hU' : Γ.Unpinned (.inl a₀) := hq0 ▸ hU
      have hqE : q ∈ Γ.toMG'.ext := MolDot_mem_ext.2 hU.1
      -- the present edges of `H₁` at `q`
      have hQs : ∀ e, H₁.cls e ≠ none → (H₁.ends e).2 = q → (H₁.ends e).1 ∈ H₁.int ∧
          ((H₁.cls e = some .minus ∧ a₀ = 2) ∨ (H₁.cls e = some .plus ∧ a₀ = 1) ∨
            (H₁.cls e = some .diff ∧ a₀ ≠ 2)) := by
        intro e hc he2
        rw [hH₁c] at hc ⊢
        rw [hH₁e] at he2 ⊢
        have he2' := hμq _ he2 hU
        rcases e with j | a
        · rcases MolDot_idx_cases Γ p q j with ⟨i, rfl⟩ | rfl
          · rw [MolDot_G0_cls_idx] at hc ⊢
            rw [MolDot_G0_ends_idx] at he2' ⊢
            have hk : Γ.comps[i].kind ≠ .dot := fun h => hc (by rw [MolDot_cls_inl, ite_eq_left h])
            rw [MolDot_ends_inl Γ i hk] at he2' ⊢
            have hxy : Γ.comps[i].x = .inl a₀ ∨ Γ.comps[i].y = .inl a₀ := by
              unfold MolDot_or at he2'
              split_ifs at he2'
              · exact Or.inl (MolDot_rho_eq (he2'.trans hq0))
              · exact Or.inr (MolDot_rho_eq (he2'.trans hq0))
            obtain ⟨⟨o, ho, hor⟩, hcl⟩ := MolDot_atq hC hE hG hU' i hc hxy
            have hoE : Γ.molRep (Γ.flatAtom o) ∉ Γ.toMG'.ext :=
              Finset.disjoint_left.1 E (MolDot_rho_int hor)
            have hρq : Γ.molRep (Γ.flatAtom (.inl a₀)) = .inl a₀ := by
              rw [MolDot_flat_unpinned hU']
              rfl
            have hor' : MolDot_or Γ.toMG'.ext
                (Γ.molRep (Γ.flatAtom Γ.comps[i].x), Γ.molRep (Γ.flatAtom Γ.comps[i].y)) =
                (Γ.molRep (Γ.flatAtom o), .inl a₀) := by
              unfold MolDot_or
              rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [h1, h2, hρq, ite_eq_left (hq0 ▸ hqE)]
              · rw [h1, h2, hρq, ite_eq_right hoE]
            rw [hor']
            exact ⟨Finset.mem_image_of_mem _ (MolDot_rho_int hor), hcl⟩
          · rw [MolDot_G0_cls_last] at hc
            exact absurd rfl hc
        · change Γ.toMG'.cls (.inr a) ≠ none at hc
          by_cases hun : Γ.Unpinned (.inl a)
          · exact absurd (MolDot_pin_none hun) hc
          · obtain ⟨b, hb⟩ : ∃ b, Γ.SameBlock (.inl a) (.inr b) := by
              by_contra hn
              push Not at hn
              exact hun ⟨rfl, hn⟩
            change (MolDot_or Γ.toMG'.ext (Γ.toMG'.ends (.inr a))).2 = q at he2'
            rw [(MolDot_pin_some hb).2] at he2'
            unfold MolDot_or at he2'
            rw [ite_eq_right (Finset.disjoint_left.1 E (MolDot_mem_int.2 ⟨b, rfl⟩))] at he2'
            have h' : (Sum.inl a : Atom 3 n) = q := he2'
            exact absurd (by rw [h']; exact hU) hun
      have hex : a₀ ≠ 2 → ∃ e, H₁.cls e ≠ none ∧ (H₁.ends e).2 = q := by
        intro h2
        obtain ⟨i, hc, hxy⟩ := MolDot_atq_ex hC hE hU' h2
        obtain ⟨⟨o, ho, hor⟩, -⟩ := MolDot_atq hC hE hG hU' i hc hxy
        refine ⟨.inl (MolDot_idx Γ p q i), by rw [hH₁c, MolDot_G0_cls_idx]; exact hc, ?_⟩
        have hk : Γ.comps[i].kind ≠ .dot := fun h => hc (by rw [MolDot_cls_inl, ite_eq_left h])
        rw [hH₁e, MolDot_G0_ends_idx, MolDot_ends_inl Γ i hk]
        have hoE : Γ.molRep (Γ.flatAtom o) ∉ Γ.toMG'.ext :=
          Finset.disjoint_left.1 E (MolDot_rho_int hor)
        have hρq : Γ.molRep (Γ.flatAtom (.inl a₀)) = .inl a₀ := by
          rw [MolDot_flat_unpinned hU']
          rfl
        unfold MolDot_or
        rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, hρq, ite_eq_left (hq0 ▸ hqE), ← hq0, hμext q hqE]
        · rw [h1, h2, hρq, ite_eq_right hoE, ← hq0, hμext q hqE]
      have hπ : H₁.cls (.inr a₀) = none := by
        rw [hH₁c]
        exact MolDot_pin_none hU'
      have hs : H₁.cls (.inl (MolDot_last Γ p q)) = none := by
        rw [hH₁c, MolDot_G0_cls_last]
      obtain ⟨H₂, c₂, i₂, x₂, cl₂, eπ₂, eQ₂, eo₂⟩ := MolDot_extChain H₁ (Γ.molRep (.inr b₀)) q
        (.inl (MolDot_last Γ p q)) (.inr a₀) a₀
        (by rw [hH₁i]; exact Finset.mem_image.2 ⟨_, hMpI, by unfold MolDot_mu; split_ifs <;> rfl⟩)
        (by rw [hH₁x]; exact hqE) hπ hs Sum.inl_ne_inr hQs hex
      refine ⟨H₂, c₂, by rw [i₂, hH₁i], by rw [x₂, hH₁x], fun a _ ha => ?_, fun e he => ?_,
        fun e he hc _ he2 => ?_, fun e he hc hn => ?_⟩
      · rw [hq0] at ha
        cases ha
        rw [cl₂, ite_eq_left rfl, eπ₂]
        exact ⟨rfl, rfl⟩
      · rw [cl₂, ite_eq_right (he a₀ hU hq0)]
        exact hH₁c e
      · rw [eQ₂ e (by rw [hH₁c]; exact hc) (by rw [hH₁e]; exact he2), hH₁e]
      · have hes : e ≠ .inl (MolDot_last Γ p q) := by
          rintro rfl
          exact hc (MolDot_G0_cls_last Γ p q)
        rw [eo₂ e (he a₀ hU hq0) hes
          (fun h => hn ⟨hU, by have := h.2; rw [hH₁e] at this; exact this⟩), hH₁e]
    · exact ⟨H₁, .refl, hH₁i, hH₁x, fun a h => absurd h hU, fun e _ => rfl,
        fun e _ _ h => absurd h hU, fun e _ _ _ => rfl⟩
  -- the loops removed
  obtain ⟨H, c₃, hHi, hHx, hHe, hHc⟩ := MolDot_unloopAll H₂
  exact MolDot_flatCarried_of_chain (MolDot_G0 Γ p q) H (MolDot_tr0 Γ p q)
    ((Relation.ReflTransGen.single c₁).trans (c₂.trans c₃))
    (MolDot_final hp hMq1 hMq2 hMq3 hB1 hQ H₂ H hi2 hx2 hpin hcl2 hen2a hen2b hHi hHx hHe hHc)

/-- A dotted edge added at an atom whose block has an internal atom, on a graph with the charge
pattern of the block normal form, the clause on the external atoms and no ghost edge: the
molecular graph of the result is carried from that of the graph (operation (A) followed by the
removal of the loops it creates, when the other atom is identified with an internal atom;
operation (B), [II, Lemma 5.12 (v)] or the move of red edges when it is not). -/
theorem addDot_flat :
  ∀ (n : ℕ) (Γ : Graph 3 n) (p q : Atom 3 n), Γ.ColourInvB → Γ.ExtClause → Γ.NoGhost →
    (∃ b : Fin n, Γ.SameBlock p (.inr b)) →
    Γ.FlatCarried (⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩ : Graph 3 n) := by
  intro n Γ p q hC hE hG ⟨b₀, hp⟩
  exact MolDot_addDot_flat hC hE hG hp

/-! ## [II, Lemma 5.10] for one dotted edge: the charge pattern and the external clause -/

section Clauses

variable {k n : ℕ}

private theorem MolDot_mem_add {Γ : Graph k n} {p q : Atom k n} {c : Comp (Atom k n)} :
    c ∈ (MolDot_add Γ p q).comps ↔ c ∈ Γ.comps ∨ c = mkC .dot p q := by
  simp [MolDot_add]

private theorem MolDot_hasDiff_add {Γ : Graph k n} {p q u : Atom k n}
    (h : Γ.HasDiffToPinned u) : (MolDot_add Γ p q).HasDiffToPinned u := by
  obtain ⟨c, hc, hd, hxy⟩ := h
  refine ⟨c, MolDot_mem_add.2 (Or.inl hc), hd, ?_⟩
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, fun h => h2 (MolDot_unpinned_of_add h)⟩
  · exact Or.inr ⟨h1, fun h => h2 (MolDot_unpinned_of_add h)⟩

private theorem MolDot_diffTo_add {Γ : Graph k n} {p q u : Atom k n}
    (h : Γ.DiffToPinned u) : (MolDot_add Γ p q).DiffToPinned u := by
  intro c hc hd
  rcases MolDot_mem_add.1 hc with hc | rfl
  · obtain ⟨h1, h2⟩ := h c hc hd
    exact ⟨fun hx h' => h1 hx (MolDot_unpinned_of_add h'),
      fun hy h' => h2 hy (MolDot_unpinned_of_add h')⟩
  · simp [mkC, Kind.isDiffusive] at hd

private theorem MolDot_nonDotDeg_add (Γ : Graph k n) (p q u : Atom k n) :
    (MolDot_add Γ p q).nonDotDeg u = Γ.nonDotDeg u := by
  simp [Graph.nonDotDeg, MolDot_add, List.filter_append, mkC]

/-- An internal atom of the block normal form stays internal after a dotted edge is added. -/
private theorem MolDot_flat_add_isRight {Γ : Graph k n} {p q u : Atom k n}
    (h : (Γ.flatAtom u).isRight = true) : ((MolDot_add Γ p q).flatAtom u).isRight = true := by
  refine MolDot_flat_isRight (fun hU => ?_)
  have hU' := MolDot_unpinned_of_add hU
  rw [MolDot_flat_unpinned hU'] at h
  have h1 := hU'.1
  cases u <;> simp_all

/-- An external atom of the block normal form after a dotted edge is added was one before. -/
private theorem MolDot_flat_add_inl {Γ : Graph k n} {p q u : Atom k n} {a : Fin k}
    (h : (MolDot_add Γ p q).flatAtom u = .inl a) : Γ.flatAtom u = .inl a := by
  have hU' : (MolDot_add Γ p q).Unpinned u := by
    by_contra hn
    have := MolDot_flat_isRight hn
    rw [h] at this
    simp at this
  rw [MolDot_flat_unpinned (MolDot_unpinned_of_add hU'), ← MolDot_flat_unpinned hU', h]

private theorem MolDot_colour_add {Γ : Graph 3 n} {p q : Atom 3 n} (hC : Γ.ColourInvB) :
    (MolDot_add Γ p q).ColourInvB := by
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
  by_cases hk : c.kind = .dot
  · rw [show (MolDot_add Γ p q).flatComp c = c by simp [Graph.flatComp, hk]]
    simp [hk, Kind.isRandom]
  · have hfc' : (MolDot_add Γ p q).flatComp c =
        { c with
          x := (MolDot_add Γ p q).flatAtom c.x
          y := (MolDot_add Γ p q).flatAtom c.y } := by
      simp [Graph.flatComp, hk]
    rcases MolDot_mem_add.1 hc with hc | rfl
    · have h := hC (Γ.flatComp c) (List.mem_map_of_mem hc)
      have hfc : Γ.flatComp c = { c with x := Γ.flatAtom c.x, y := Γ.flatAtom c.y } := by
        simp [Graph.flatComp, hk]
      rw [hfc] at h
      rw [hfc']
      dsimp only at h ⊢
      obtain ⟨h1, h2⟩ := h
      refine ⟨fun hr => ?_, fun hs => ?_⟩
      · obtain ⟨r1, r2, r3, r4⟩ := h1 hr
        exact ⟨MolDot_flat_add_isRight r1, fun h' => r2 (MolDot_flat_add_inl h'),
          fun h' => r3 (MolDot_flat_add_inl h'), fun h' => r4 (MolDot_flat_add_inl h')⟩
      · obtain ⟨s1, s2⟩ := h2 hs
        exact ⟨MolDot_flat_add_isRight s1, MolDot_flat_add_isRight s2⟩
    · simp [mkC] at hk

private theorem MolDot_ext_add {Γ : Graph 3 n} {p q : Atom 3 n} {b₀ : Fin n}
    (hE : Γ.ExtClause) (hp : Γ.SameBlock p (.inr b₀)) : (MolDot_add Γ p q).ExtClause := by
  obtain ⟨E1, E2, E3, E4, E5⟩ := hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv h
    rcases (MolDot_sameBlock_add Γ p q u v).1 h with h | ⟨h1, -⟩ | ⟨h1, -⟩
    · obtain ⟨b, hb⟩ := E1 u v huv h
      exact ⟨b, MolDot_sameBlock_mono hb⟩
    · exact ⟨b₀, MolDot_sameBlock_mono (h1.trans hp)⟩
    · exact ⟨b₀, (MolDot_sameBlock_mono h1).trans
        ((MolDot_sameBlock_pq Γ p q).symm.trans (MolDot_sameBlock_mono hp))⟩
  · intro c hc hk
    rcases MolDot_mem_add.1 hc with hc | rfl
    · exact fun ⟨h1, h2⟩ => E2 c hc hk ⟨MolDot_unpinned_of_add h1, MolDot_unpinned_of_add h2⟩
    · simp [mkC] at hk
  · intro hU
    obtain ⟨h1, h2⟩ := E3 (MolDot_unpinned_of_add hU)
    exact ⟨MolDot_hasDiff_add h1, MolDot_diffTo_add h2⟩
  · intro hU
    obtain ⟨h1, h2⟩ := E4 (MolDot_unpinned_of_add hU)
    refine ⟨fun c hc hd => ?_, by rw [MolDot_nonDotDeg_add]; exact h2⟩
    rcases MolDot_mem_add.1 hc with hc | rfl
    · exact h1 c hc hd
    · simp [mkC, Kind.isDiffusive] at hd
  · intro hU
    obtain ⟨h1, h2, h3⟩ := E5 (MolDot_unpinned_of_add hU)
    refine ⟨?_, MolDot_diffTo_add h2, by rw [MolDot_nonDotDeg_add]; exact h3⟩
    rcases h1 with ⟨c, hc, hk, hxy⟩ | h
    · exact Or.inl ⟨c, MolDot_mem_add.2 (Or.inl hc), hk, hxy⟩
    · exact Or.inr (MolDot_hasDiff_add h)

private theorem MolDot_noGhost_add {Γ : Graph k n} {p q : Atom k n} (hG : Γ.NoGhost) :
    (MolDot_add Γ p q).NoGhost := by
  intro c hc
  rcases MolDot_mem_add.1 hc with hc | rfl
  · exact hG c hc
  · simp [mkC]

end Clauses

/-- A dotted edge `p = q` added at an atom `p` whose block has an internal atom ([II, Lemma 5.10]
for `O_dot`, one dotted edge at a time): on a graph that is sequentially pre-deterministic in the
block reading, with the charge pattern of the block normal form, the clause on the external atoms
and no ghost edge, the result has the same four properties. -/
theorem spdPM'_addDot :
  ∀ (n : ℕ) (Γ : Graph 3 n) (p q : Atom 3 n), spdPM' Γ → Γ.ColourInvB → Γ.ExtClause →
    Γ.NoGhost → (∃ b : Fin n, Γ.SameBlock p (.inr b)) →
    spdPM' (⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩ : Graph 3 n) ∧
      (⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩ : Graph 3 n).ColourInvB ∧
      (⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩ : Graph 3 n).ExtClause ∧
      (⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩ : Graph 3 n).NoGhost := by
  intro n Γ p q hs hC hE hG ⟨b₀, hp⟩
  exact ⟨flatCarried_spd 3 n n Γ (MolDot_add Γ p q) (MolDot_addDot_flat hC hE hG hp) hG hs,
    MolDot_colour_add hC, MolDot_ext_add hE hp, MolDot_noGhost_add hG⟩

/-- A dotted edge added at an atom whose block has an internal atom keeps the invariant
`Graph.InvB'`. -/
theorem invB'_addDot :
  ∀ (n : ℕ) (Γ : Graph 3 n) (p q : Atom 3 n), Γ.InvB' → (∃ b : Fin n, Γ.SameBlock p (.inr b)) →
    (⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩ : Graph 3 n).InvB' := by
  intro n Γ p q ⟨hs, hc, he, hg, hl⟩ hp
  obtain ⟨h1, h2, h3, h4⟩ := spdPM'_addDot n Γ p q hs hc he hg hp
  refine ⟨h1, h2, h3, h4, fun c hc' => ?_⟩
  rcases List.mem_append.1 hc' with h' | h'
  · exact hl c h'
  · rw [List.mem_singleton] at h'
    subst h'
    rfl

section Bridge

variable {V E V' E' : Type}

section Lemmas

variable [DecidableEq V'] {G : MGraph V E} {G' : MGraph V' E'} {f : V → V'} {g : E → E'}

end Lemmas

end Bridge

section BridgeGraph

variable {k n : ℕ}

end BridgeGraph

/-! ## Decidability instances for concrete graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance MolDot_decAdjDot {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

private instance MolDot_decSameBlock {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameBlock :=
  fun u v => @SimpleGraph.instDecidableRelReachable _ _ _ _ (MolDot_decAdjDot Γ) u v

private instance MolDot_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

section Helpers

variable {V E : Type}

end Helpers

end Instances

end RBM8D.Graphs
