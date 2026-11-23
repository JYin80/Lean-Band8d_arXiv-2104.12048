module

public import RBM8D.Graph.MolInsert
public import RBM8D.Graph.Local.Strategy
public import RBM8D.Graph.DotBlocks
public import RBM8D.Graph.Glue
public import RBM8D.GlobalExp.Strategy
public import RBM8D.Graph.QExp.MolMono

@[expose] public section

/-!
# The molecular graph of the block reading under `O_merge` and under the substitution

The molecular graph `Graph.toMG'` of [II, Def 2.11] in the block reading, along two operations of
[II, Lemma 6.5]:

* `O_merge` ([II, Def 4.1]) on a graph whose dotted edges all join two internal atoms: the
  molecular graph of the result is the molecular graph of the input up to the names of the
  vertices and of the present edges (`MGraph.Transported`), so that the sequentially
  pre-deterministic ([II, Def 5.9]) and the globally standard ([II, Def 6.2]) properties are the
  same for both;
* the substitution of a graph `𝒢` for the `t`-variable `t_{y₁y₂,x}` of a graph `H`
  ([II, §4.3], picture (6.5) of [II, Lemma 6.5 (2)]): the molecular graph of the substituted
  graph is the molecular graph of `𝒢` inserted into that of the graph with the `t`-variable
  (`MGraph.insert`), with the molecules identified as in the substituted graph and the loops
  removed.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Reachability and molecules along maps of the atoms -/

section Generic

variable {k n : ℕ}

/-- Reachability is carried along a map that sends every step of the relation to an equality or
to a step of the other relation. -/
private theorem SubstMol_reach_map {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    (φ : α → β) (h : ∀ a b, r a b → φ a = φ b ∨ r' (φ a) (φ b)) {a b : α}
    (hab : (SimpleGraph.fromRel r).Reachable a b) :
    (SimpleGraph.fromRel r').Reachable (φ a) (φ b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hab ⊢
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b' c' _ hadj ih =>
    rw [SimpleGraph.fromRel_adj] at hadj
    have hstep : φ b' = φ c' ∨ (SimpleGraph.fromRel r').Adj (φ b') (φ c') := by
      by_cases hne : φ b' = φ c'
      · exact Or.inl hne
      · refine Or.inr ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, ?_⟩)
        rcases hadj.2 with h1 | h1
        · rcases h _ _ h1 with he | he
          · exact absurd he hne
          · exact Or.inl he
        · rcases h _ _ h1 with he | he
          · exact absurd he.symm hne
          · exact Or.inr he
    rcases hstep with he | he
    · rw [← he]
      exact ih
    · exact ih.tail he

/-- Molecules are carried along a map of the atoms that keeps internal atoms internal and sends
every waved or dotted component to an equality or to a waved or dotted component. -/
private theorem SubstMol_sameMol_map {n' : ℕ} {Γ : Graph k n} {Γ' : Graph k n'}
    (φ : Atom k n → Atom k n') (hφ : ∀ u : Atom k n, u.isRight = true → (φ u).isRight = true)
    (hc : ∀ c ∈ Γ.comps, c.kind.joinsMol = true → φ c.x = φ c.y ∨
      ∃ c' ∈ Γ'.comps, c'.kind.joinsMol = true ∧ c'.x = φ c.x ∧ c'.y = φ c.y)
    {u v : Atom k n} (h : Γ.SameMol u v) : Γ'.SameMol (φ u) (φ v) := by
  rcases h with rfl | ⟨hu, hv, h⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨hφ u hu, hφ v hv, ?_⟩
    unfold Graph.molGraph at h ⊢
    refine SubstMol_reach_map φ (fun a b hab => ?_) h
    obtain ⟨c, hcm, hk, rfl, rfl⟩ := hab
    rcases hc c hcm hk with h' | ⟨c', hc', hk', hx', hy'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨c', hc', hk', hx', hy'⟩

/-- Blocks are carried along a map of the atoms that sends every dotted component to an equality
or to a dotted component. -/
private theorem SubstMol_sameBlock_map {n' : ℕ} {Γ : Graph k n} {Γ' : Graph k n'}
    (φ : Atom k n → Atom k n')
    (hc : ∀ c ∈ Γ.comps, c.kind = .dot → φ c.x = φ c.y ∨
      ∃ c' ∈ Γ'.comps, c'.kind = .dot ∧ c'.x = φ c.x ∧ c'.y = φ c.y)
    {u v : Atom k n} (h : Γ.SameBlock u v) : Γ'.SameBlock (φ u) (φ v) := by
  unfold Graph.SameBlock Graph.dotGraph at h ⊢
  refine SubstMol_reach_map φ (fun a b hab => ?_) h
  obtain ⟨c, hcm, hk, rfl, rfl⟩ := hab
  rcases hc c hcm hk with h' | ⟨c', hc', hk', hx', hy'⟩
  · exact Or.inl h'
  · exact Or.inr ⟨c', hc', hk', hx', hy'⟩

/-- Atoms of one block are joined in the graph of waved and dotted edges. -/
private theorem SubstMol_block_le_mol {Γ : Graph k n} {u v : Atom k n} (h : Γ.SameBlock u v) :
    Γ.molGraph.Reachable u v := by
  unfold Graph.SameBlock Graph.dotGraph at h
  unfold Graph.molGraph
  have := SubstMol_reach_map (r' := fun u v => ∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧
    c.y = v) id (fun a b ⟨c, hc, hk, hx, hy⟩ => Or.inr ⟨c, hc, by rw [hk]; rfl, hx, hy⟩) h
  exact this

/-- The two ends of a waved or dotted component are joined in the graph of waved and dotted
edges. -/
private theorem SubstMol_mol_adj {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hj : c.kind.joinsMol = true) : Γ.molGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact SimpleGraph.Adj.reachable
      ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hj, rfl, rfl⟩⟩)

/-- An atom lies in the molecule of its representative. -/
private theorem SubstMol_molRep_spec (Γ : Graph k n) (u : Atom k n) :
    Γ.SameMol u (Γ.molRep u) := by
  rcases u with a | a
  · exact Or.inl rfl
  · obtain ⟨b, hb, h⟩ := MolMono_molRep_inr Γ a
    rw [hb]
    exact h

/-- Two atoms have the same representative exactly when they lie in one molecule. -/
private theorem SubstMol_molRep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.molRep u = Γ.molRep v ↔ Γ.SameMol u v := by
  rcases u with a | a <;> rcases v with b | b
  · change (Sum.inl a : Atom k n) = Sum.inl b ↔ _
    refine ⟨fun h => Or.inl h, fun h => ?_⟩
    rcases h with h | ⟨h, -⟩
    · exact h
    · simp at h
  · obtain ⟨c, hc, -⟩ := MolMono_molRep_inr Γ b
    change (Sum.inl a : Atom k n) = Γ.molRep (.inr b) ↔ _
    rw [hc]
    refine ⟨fun h => by simp at h, fun h => ?_⟩
    rcases h with h | ⟨h, -⟩
    · simp at h
    · simp at h
  · obtain ⟨c, hc, -⟩ := MolMono_molRep_inr Γ a
    change Γ.molRep (.inr a) = (Sum.inl b : Atom k n) ↔ _
    rw [hc]
    refine ⟨fun h => by simp at h, fun h => ?_⟩
    rcases h with h | ⟨-, h, -⟩
    · simp at h
    · simp at h
  · exact MolMono_molRep_eq_iff Γ a b

/-- A vertex of `Graph.toMG'` is its own representative. -/
private theorem SubstMol_molRep_vtx {Γ : Graph k n} {u : Atom k n} (h : Γ.toMG'.IsVtx u) :
    Γ.molRep u = u := by
  rcases h with h | h
  · obtain ⟨-, -, h'⟩ := MolMono_of_mem_int Γ h
    exact h'
  · obtain ⟨a, rfl⟩ := (MolMono_mem_ext Γ u).1 h
    rfl

/-- Without dotted edges at external atoms, the block of an external atom is that atom. -/
private theorem SubstMol_sameBlock_inl {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) (a : Fin k)
    {u : Atom k n} (h : Γ.SameBlock (.inl a) u) : u = .inl a := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons h _ =>
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at h
    rcases h.2 with ⟨c, hc, hk, hx, -⟩ | ⟨c, hc, hk, -, hy⟩
    · have := (hd c hc hk).1
      rw [hx] at this
      simp at this
    · have := (hd c hc hk).2
      rw [hy] at this
      simp at this

/-- Without dotted edges at external atoms, two atoms of one block are equal or both internal. -/
private theorem SubstMol_sameBlock_cases {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    {u v : Atom k n} (h : Γ.SameBlock u v) :
    u = v ∨ (u.isRight = true ∧ v.isRight = true) := by
  rcases u with a | a
  · exact Or.inl (SubstMol_sameBlock_inl hd a h).symm
  · rcases v with b | b
    · exact Or.inl (SubstMol_sameBlock_inl hd b (SimpleGraph.Reachable.symm h))
    · exact Or.inr ⟨rfl, rfl⟩

/-- Without dotted edges at external atoms, atoms of one block lie in one molecule. -/
private theorem SubstMol_sameMol_of_sameBlock {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    {u v : Atom k n} (h : Γ.SameBlock u v) : Γ.SameMol u v := by
  rcases SubstMol_sameBlock_cases hd h with e | ⟨hu, hv⟩
  · exact Or.inl e
  · exact Or.inr ⟨hu, hv, SubstMol_block_le_mol h⟩

/-- Without dotted edges at external atoms, no external atom has an anchor. -/
private theorem SubstMol_anchor_none {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) (a : Fin k) :
    Γ.anchor (.inl a) = none := by
  classical
  rw [MolMono_anchor_eq_find]
  refine List.find?_eq_none.2 fun b _ => ?_
  simp only [decide_eq_true_eq]
  intro h
  exact absurd (SubstMol_sameBlock_inl hd a h) (by simp)

/-- Without dotted edges at external atoms, the block normal form moves no atom. -/
private theorem SubstMol_flatAtom {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (u : Atom k n) : Γ.flatAtom u = u := by
  rcases u with a | a
  · simp only [Graph.flatAtom, SubstMol_anchor_none hd a]
  · rfl

/-- Without dotted edges at external atoms, the block normal form keeps every component. -/
private theorem SubstMol_flatComp {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (c : Comp (Atom k n)) : Γ.flatComp c = c := by
  unfold Graph.flatComp
  split_ifs
  · rfl
  · rw [SubstMol_flatAtom hd, SubstMol_flatAtom hd]

/-- The block normal form keeps the kind of a component. -/
private theorem SubstMol_flatComp_kind (Γ : Graph k n) (c : Comp (Atom k n)) :
    (Γ.flatComp c).kind = c.kind := by
  unfold Graph.flatComp
  split_ifs <;> rfl

/-- The class of the edge `.inl i` of `Graph.toMG'`. -/
private theorem SubstMol_cls_inl' (Γ : Graph k n) (i : Fin Γ.comps.length) :
    Γ.toMG'.cls (.inl i) = if (Γ.flatComp Γ.comps[i]).kind = .dot ∨
      Γ.molRep (Γ.flatComp Γ.comps[i]).x = Γ.molRep (Γ.flatComp Γ.comps[i]).y then none
      else (Γ.flatComp Γ.comps[i]).kind.mclass := rfl

/-- The ends of the edge `.inl i` of `Graph.toMG'`. -/
private theorem SubstMol_ends_inl' (Γ : Graph k n) (i : Fin Γ.comps.length) :
    Γ.toMG'.ends (.inl i) =
      (Γ.molRep (Γ.flatComp Γ.comps[i]).x, Γ.molRep (Γ.flatComp Γ.comps[i]).y) := rfl

/-- Without dotted edges at external atoms, the class of the edge `.inl i` of `Graph.toMG'`. -/
private theorem SubstMol_cls_inl {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (i : Fin Γ.comps.length) :
    Γ.toMG'.cls (.inl i) = if Γ.comps[i].kind = .dot ∨
      Γ.molRep Γ.comps[i].x = Γ.molRep Γ.comps[i].y then none else Γ.comps[i].kind.mclass := by
  rw [SubstMol_cls_inl', SubstMol_flatComp hd]

/-- Without dotted edges at external atoms, the ends of the edge `.inl i` of `Graph.toMG'`. -/
private theorem SubstMol_ends_inl {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (i : Fin Γ.comps.length) :
    Γ.toMG'.ends (.inl i) = (Γ.molRep Γ.comps[i].x, Γ.molRep Γ.comps[i].y) := by
  rw [SubstMol_ends_inl', SubstMol_flatComp hd]

/-- Without dotted edges at external atoms, the edges `.inr a` of `Graph.toMG'` are absent. -/
private theorem SubstMol_cls_inr {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) (a : Fin k) :
    Γ.toMG'.cls (.inr a) = none := by
  change (match Γ.anchor (.inl a) with
    | some _ => some (pinClass a)
    | none => none) = none
  rw [SubstMol_anchor_none hd a]

/-- The internal vertices of `Graph.toMG'` are internal atoms. -/
private theorem SubstMol_int_isRight {Γ : Graph k n} {u : Atom k n} (h : u ∈ Γ.toMG'.int) :
    u.isRight = true := by
  obtain ⟨b, rfl, -⟩ := MolMono_of_mem_int Γ h
  rfl

/-- The representative of an internal atom is internal. -/
private theorem SubstMol_molRep_isRight (Γ : Graph k n) {u : Atom k n} (h : u.isRight = true) :
    (Γ.molRep u).isRight = true := by
  rcases u with a | a
  · simp at h
  · exact SubstMol_int_isRight (MolMono_molRep_mem_int Γ a)

end Generic

/-! ## Positions in a list after `List.filterMap` -/

/-- The position in `l.filterMap φ` of each kept entry of `l`: it is injective on the kept
entries and every entry of `l.filterMap φ` is reached. -/
private theorem SubstMol_filterMap_idx {α β : Type*} (φ : α → Option β) :
    ∀ (l : List α) (l' : List β), l' = l.filterMap φ → ∃ ι : ℕ → ℕ,
      (∀ i (hi : i < l.length) b, φ l[i] = some b → ∃ h : ι i < l'.length, l'[ι i] = b) ∧
      (∀ i j (hi : i < l.length) (hj : j < l.length), (φ l[i]).isSome = true →
        (φ l[j]).isSome = true → ι i = ι j → i = j) ∧
      (∀ j (hj : j < l'.length), ∃ i, ∃ hi : i < l.length, ι i = j ∧ φ l[i] = some l'[j])
  | [], l', hl => by
    subst hl
    exact ⟨id, fun i hi => by simp at hi, fun i j hi => by simp at hi, fun j hj => by simp at hj⟩
  | a :: l, l', hl => by
    cases ha : φ a with
    | none =>
      rw [List.filterMap_cons_none ha] at hl
      obtain ⟨ι, h1, h2, h3⟩ := SubstMol_filterMap_idx φ l l' hl
      refine ⟨fun i => ι (i - 1), ?_, ?_, ?_⟩
      · intro i hi b hb
        cases i with
        | zero => simp [ha] at hb
        | succ i => exact h1 i (by simpa using hi) b hb
      · intro i j hi hj si sj he
        cases i with
        | zero => simp [ha] at si
        | succ i =>
          cases j with
          | zero => simp [ha] at sj
          | succ j =>
            have := h2 i j (by simpa using hi) (by simpa using hj) si sj he
            omega
      · intro j hj
        obtain ⟨i, hi, hij, hφ⟩ := h3 j hj
        exact ⟨i + 1, by simpa using hi, by simpa using hij, hφ⟩
    | some b₀ =>
      rw [List.filterMap_cons_some ha] at hl
      subst hl
      obtain ⟨ι, h1, h2, h3⟩ := SubstMol_filterMap_idx φ l _ rfl
      refine ⟨fun i => if i = 0 then 0 else ι (i - 1) + 1, ?_, ?_, ?_⟩
      · intro i hi b hb
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, ha, Option.some.injEq] at hb
          exact ⟨by simp, by simp [hb]⟩
        | succ i =>
          obtain ⟨h, hb'⟩ := h1 i (by simpa using hi) b hb
          exact ⟨by simpa using h, by simpa using hb'⟩
      · intro i j hi hj si sj he
        cases i with
        | zero =>
          cases j with
          | zero => rfl
          | succ j => simp at he
        | succ i =>
          cases j with
          | zero => simp at he
          | succ j =>
            simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
              Nat.add_right_cancel_iff] at he
            have := h2 i j (by simpa using hi) (by simpa using hj) si sj he
            omega
      · intro j hj
        cases j with
        | zero => exact ⟨0, by simp, rfl, by simpa using ha⟩
        | succ j =>
          obtain ⟨i, hi, hij, hφ⟩ := h3 j (by simpa using hj)
          exact ⟨i + 1, by simpa using hi, by simp [hij], by simpa using hφ⟩

/-! ## `O_merge` with dotted edges between internal atoms -/

section MergeT

variable {k n : ℕ}

/-- The representative `blockRep` of an atom is the atom or lies in its block. -/
private theorem SubstMol_blockRep_spec {V : Type*} [DecidableEq V] (P : List (List V)) (u : V) :
    blockRep P u = u ∨ ∃ B ∈ P, u ∈ B ∧ blockRep P u ∈ B := by
  unfold blockRep
  generalize hf : P.find? (fun B => B.contains u) = o
  rcases o with _ | ⟨_ | ⟨r, rest⟩⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · right
    refine ⟨r :: rest, List.mem_of_find?_eq_some hf, ?_, List.mem_cons_self ..⟩
    simpa [List.contains_iff_mem] using List.find?_some hf

/-- An atom lies in the block of its representative `Graph.mrep`. -/
private theorem SubstMol_sameBlock_mrep (Γ : Graph k n) (u : Atom k n) :
    Γ.SameBlock u (Γ.mrep u) := by
  rcases SubstMol_blockRep_spec (dotBlocks (allAtoms k n) Γ.comps) u with h | ⟨B, hB, hu, hr⟩
  · have : Γ.mrep u = u := h
    rw [this]
    exact SimpleGraph.Reachable.refl _
  · exact (Γ.sameBlock_iff_mem_dotBlocks _ _).2 ⟨B, hB, hu, hr⟩

/-- Atoms with the same representative `Graph.mrep` lie in one block. -/
private theorem SubstMol_sameBlock_of_mrep (Γ : Graph k n) {u v : Atom k n}
    (h : Γ.mrep u = Γ.mrep v) : Γ.SameBlock u v :=
  SimpleGraph.Reachable.trans (SubstMol_sameBlock_mrep Γ u)
    (h ▸ SimpleGraph.Reachable.symm (SubstMol_sameBlock_mrep Γ v))

/-- A component that is neither dotted nor solid is mapped by `mergeComp`. -/
private theorem SubstMol_mergeComp_other {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (hd : c.kind ≠ .dot)
    (hs : c.kind.isSolid = false) : mergeComp rep f c = some (c.map f) := by
  unfold mergeComp
  simp [hd, hs]

/-- A component removed by `mergeComp` is dotted. -/
private theorem SubstMol_mergeComp_none {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (h : mergeComp rep f c = none) :
    c.kind = .dot := by
  unfold mergeComp at h
  split_ifs at h with h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact h1.1

/-- A waved or dotted component kept by `mergeComp` is mapped. -/
private theorem SubstMol_mergeComp_joins {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} {c' : Comp (Atom k m)}
    (h : mergeComp rep f c = some c') (hj : c'.kind.joinsMol = true) :
    c.kind.joinsMol = true ∧ c' = c.map f := by
  rcases mergeComp_kind h with hk | ⟨ch, -, hk⟩
  · have hjc : c.kind.joinsMol = true := hk ▸ hj
    refine ⟨hjc, ?_⟩
    by_cases hdk : c.kind = .dot
    · rw [mergeComp_dot hdk] at h
      split_ifs at h
      exact (Option.some.inj h).symm
    · have hs : c.kind.isSolid = false := by
        cases hc : c.kind <;> simp_all [Kind.isSolid, Kind.joinsMol]
      rw [SubstMol_mergeComp_other hdk hs] at h
      exact (Option.some.inj h).symm
  · rw [hk] at hj
    simp [Kind.joinsMol] at hj

variable {Γ : Graph k n} {t : Tracked k n}

/-- Atoms with the same image under `O_merge` lie in one block. -/
private theorem SubstMol_sameBlock_of_f (hs : MergeSpec Γ t) {u v : Atom k n}
    (h : t.f u = t.f v) : Γ.SameBlock u v := by
  by_cases hr : Γ.mrep u = Γ.mrep v
  · exact SubstMol_sameBlock_of_mrep Γ hr
  · exact absurd h (hs.f_ne u v hr)

/-- The atom map of `O_merge` keeps internal and external atoms. -/
private theorem SubstMol_f_isRight (hs : MergeSpec Γ t) (u : Atom k n) :
    (t.f u).isRight = u.isRight := by
  rcases u with a | i
  · rw [hs.f_inl]
    rfl
  · obtain ⟨g, hg, -⟩ := hs.f_inr
    rw [hg]
    rfl

/-- Atoms of one molecule have images in one molecule. -/
private theorem SubstMol_sameMol_fwd (hs : MergeSpec Γ t) {u v : Atom k n}
    (h : Γ.SameMol u v) : t.g.SameMol (t.f u) (t.f v) := by
  refine SubstMol_sameMol_map t.f (fun u hu => by rw [SubstMol_f_isRight hs]; exact hu)
    (fun c hc hj => ?_) h
  by_cases hdk : c.kind = .dot
  · by_cases he : t.f c.x = t.f c.y
    · exact Or.inl he
    · refine Or.inr ⟨c.map t.f, hs.mem_comps.2 ⟨c, hc, ?_⟩, hj, rfl, rfl⟩
      rw [mergeComp_dot hdk, ite_eq_right he]
  · have hsol : c.kind.isSolid = false := by
      cases hc : c.kind <;> simp_all [Kind.isSolid, Kind.joinsMol]
    exact Or.inr ⟨c.map t.f, hs.mem_comps.2 ⟨c, hc, SubstMol_mergeComp_other hdk hsol⟩, hj, rfl,
      rfl⟩

/-- A path of waved and dotted edges between images is read back as a path between the atoms. -/
private theorem SubstMol_reach_bwd (hs : MergeSpec Γ t) {u : Atom k n} {p : Atom k t.nOut}
    (h : t.g.molGraph.Reachable (t.f u) p) : ∀ v, t.f v = p → Γ.molGraph.Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact fun v hv => SubstMol_block_le_mol (SubstMol_sameBlock_of_f hs hv.symm)
  | @tail q p _ hadj ih =>
    intro v hv
    unfold Graph.molGraph at hadj
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with ⟨c', hc', hj, hx, hy⟩ | ⟨c', hc', hj, hx, hy⟩
    · obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
      obtain ⟨hjc, rfl⟩ := SubstMol_mergeComp_joins hm hj
      exact ((ih c.x hx).trans (SubstMol_mol_adj hc hjc)).trans
        (SubstMol_block_le_mol (SubstMol_sameBlock_of_f hs (hy.trans hv.symm)))
    · obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
      obtain ⟨hjc, rfl⟩ := SubstMol_mergeComp_joins hm hj
      exact ((ih c.y hy).trans (SubstMol_mol_adj hc hjc).symm).trans
        (SubstMol_block_le_mol (SubstMol_sameBlock_of_f hs (hx.trans hv.symm)))

/-- Atoms whose images lie in one molecule lie in one molecule. -/
private theorem SubstMol_sameMol_bwd
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (hs : MergeSpec Γ t) {u v : Atom k n} (h : t.g.SameMol (t.f u) (t.f v)) :
    Γ.SameMol u v := by
  rcases h with h | ⟨hu, hv, h⟩
  · exact SubstMol_sameMol_of_sameBlock hd (SubstMol_sameBlock_of_f hs h)
  · rw [SubstMol_f_isRight hs] at hu hv
    exact Or.inr ⟨hu, hv, SubstMol_reach_bwd hs h v rfl⟩

/-- Two atoms have images with the same representative exactly when they have the same
representative. -/
private theorem SubstMol_molRep_f
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (hs : MergeSpec Γ t) (u v : Atom k n) :
    t.g.molRep (t.f u) = t.g.molRep (t.f v) ↔ Γ.molRep u = Γ.molRep v := by
  rw [SubstMol_molRep_eq_iff, SubstMol_molRep_eq_iff]
  exact ⟨SubstMol_sameMol_bwd hd hs, SubstMol_sameMol_fwd hs⟩

/-- The image of the representative of an atom has the representative of the image. -/
private theorem SubstMol_molRep_f_molRep
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (hs : MergeSpec Γ t) (u : Atom k n) :
    t.g.molRep (t.f (Γ.molRep u)) = t.g.molRep (t.f u) :=
  (SubstMol_molRep_f hd hs _ _).2 (MolMono_molRep_idem Γ u)

/-- The dotted edges of the result of `O_merge` join internal atoms. -/
private theorem SubstMol_hd_merge
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (hs : MergeSpec Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind = .dot → c'.x.isRight = true ∧ c'.y.isRight = true := by
  intro c' hc' hk
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  obtain ⟨-, rfl⟩ := SubstMol_mergeComp_joins hm (by rw [hk]; rfl)
  obtain ⟨h1, h2⟩ := hd c hc hk
  exact ⟨(SubstMol_f_isRight hs c.x).trans h1, (SubstMol_f_isRight hs c.y).trans h2⟩

/-- A component kept by `O_merge` has the class of its image in the molecular graphs. -/
private theorem SubstMol_cls_merge
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (hs : MergeSpec Γ t) {c : Comp (Atom k n)} {c' : Comp (Atom k t.nOut)}
    (hm : mergeComp Γ.mrep t.f c = some c') :
    (if c'.kind = .dot ∨ t.g.molRep c'.x = t.g.molRep c'.y then none else c'.kind.mclass) =
      (if c.kind = .dot ∨ Γ.molRep c.x = Γ.molRep c.y then none else c.kind.mclass) ∧
    ((if c.kind = .dot ∨ Γ.molRep c.x = Γ.molRep c.y then none else c.kind.mclass) ≠ none →
      c' = c.map t.f) := by
  unfold mergeComp at hm
  split_ifs at hm with h1 h2
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain rfl := Option.some.inj hm
    obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    have hmol : Γ.molRep c.x = Γ.molRep c.y := (SubstMol_molRep_eq_iff Γ _ _).2
      (SubstMol_sameMol_of_sameBlock hd (SubstMol_sameBlock_of_mrep Γ h2.2))
    refine ⟨?_, fun h => absurd (by simp [hmol]) h⟩
    simp [hch, Kind.toWeight, Kind.mclass, hmol]
  · obtain rfl := Option.some.inj hm
    refine ⟨?_, fun _ => rfl⟩
    change (if c.kind = .dot ∨ t.g.molRep (t.f c.x) = t.g.molRep (t.f c.y) then none
      else c.kind.mclass) = _
    simp only [SubstMol_molRep_f hd hs]

end MergeT

/-- **`O_merge` and the molecular graph** ([II, Def 4.1], [II, Def 2.11] in the block reading):
if every dotted edge of `Γ` joins two internal atoms and `O_merge` does not vanish on `Γ`, the
molecular graph of the result is that of `Γ` up to the names of the vertices and of the present
edges. The vertices are mapped by the atom map of `O_merge` followed by the representative of the
molecule; a dotted edge or a solid edge inside one block is absent on both sides. The premise
`0 < k` gives an edge index for the removed dotted edges. -/
theorem toMG'_mergeT :
  ∀ (k n : ℕ) (Γ : Graph k n) (t : Tracked k n), 0 < k →
    (∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) →
    Γ.mergeT = some t → Γ.toMG'.Transported t.g.toMG' := by
  intro k n Γ t hk hd h
  classical
  have hs := mergeT_spec h
  have hd' := SubstMol_hd_merge hd hs
  obtain ⟨ι, h1, h2, h3⟩ :=
    SubstMol_filterMap_idx (mergeComp Γ.mrep t.f) Γ.comps t.g.comps hs.comps_eq
  let Ge : Fin Γ.comps.length ⊕ Fin k → Fin t.g.comps.length ⊕ Fin k := fun e =>
    match e with
    | .inl i => if hi : ι i < t.g.comps.length then .inl ⟨ι i, hi⟩ else .inr ⟨0, hk⟩
    | .inr a => .inr a
  have hkept : ∀ i : Fin Γ.comps.length, Γ.toMG'.cls (.inl i) ≠ none →
      ∃ c', mergeComp Γ.mrep t.f Γ.comps[i] = some c' := by
    intro i hi
    cases hm : mergeComp Γ.mrep t.f Γ.comps[i] with
    | some c' => exact ⟨c', rfl⟩
    | none =>
      exfalso
      apply hi
      rw [SubstMol_cls_inl hd, ite_eq_left (Or.inl (SubstMol_mergeComp_none hm))]
  have hGe : ∀ (i : Fin Γ.comps.length) c', mergeComp Γ.mrep t.f Γ.comps[i] = some c' →
      ∃ hj : ι i < t.g.comps.length, Ge (.inl i) = .inl ⟨ι i, hj⟩ ∧ t.g.comps[ι i] = c' := by
    intro i c' hm
    obtain ⟨hj, hc⟩ := h1 i i.2 c' hm
    exact ⟨hj, by simp only [Ge, dite_eq_left hj], hc⟩
  have hclsEq : ∀ (i : Fin Γ.comps.length) c', mergeComp Γ.mrep t.f Γ.comps[i] = some c' →
      t.g.toMG'.cls (Ge (.inl i)) = Γ.toMG'.cls (.inl i) := by
    intro i c' hm
    obtain ⟨hj, hG, hc⟩ := hGe i c' hm
    rw [hG, SubstMol_cls_inl hd', SubstMol_cls_inl hd]
    simp only [Fin.getElem_fin, hc]
    exact (SubstMol_cls_merge hd hs hm).1
  have hpres : ∀ e, Γ.toMG'.cls e ≠ none → ∃ (i : Fin Γ.comps.length) (c' : Comp (Atom k t.nOut)),
      e = .inl i ∧ mergeComp Γ.mrep t.f Γ.comps[i] = some c' ∧ c' = Γ.comps[i].map t.f := by
    intro e he
    rcases e with i | a
    · obtain ⟨c', hm⟩ := hkept i he
      refine ⟨i, c', rfl, hm, (SubstMol_cls_merge hd hs hm).2 ?_⟩
      rw [SubstMol_cls_inl hd] at he
      exact he
    · exact absurd (SubstMol_cls_inr hd a) he
  refine ⟨fun v => t.g.molRep (t.f v), Ge, ?_, ?_, ?_, ?_,
    fun e _ => MolInsert_toMG'_ends_vtx _ _ _ e, ?_, ?_, ?_⟩
  · intro e₁ e₂ he₁ he₂ he
    obtain ⟨i₁, c₁, rfl, hm₁, -⟩ := hpres e₁ he₁
    obtain ⟨i₂, c₂, rfl, hm₂, -⟩ := hpres e₂ he₂
    obtain ⟨hj₁, hG₁, -⟩ := hGe i₁ c₁ hm₁
    obtain ⟨hj₂, hG₂, -⟩ := hGe i₂ c₂ hm₂
    rw [hG₁, hG₂] at he
    simp only [Sum.inl.injEq, Fin.mk.injEq] at he
    have := h2 i₁ i₂ i₁.2 i₂.2 (by simp only [Fin.getElem_fin] at hm₁; simp [hm₁])
      (by simp only [Fin.getElem_fin] at hm₂; simp [hm₂]) he
    exact congrArg Sum.inl (Fin.ext this)
  · intro u hu v hv huv
    have hu' : Γ.toMG'.IsVtx u := by
      rcases hu with hu | hu
      · exact Or.inl hu
      · exact Or.inr hu
    have hv' : Γ.toMG'.IsVtx v := by
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr hv
    have := (SubstMol_molRep_f hd hs u v).1 huv
    rwa [SubstMol_molRep_vtx hu', SubstMol_molRep_vtx hv'] at this
  · ext M
    rw [MolMono_mem_int, Finset.mem_image]
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨g, hg, hsj⟩ := hs.f_inr
      obtain ⟨i, rfl⟩ := hsj j
      refine ⟨Γ.molRep (.inr i), MolMono_molRep_mem_int Γ i, ?_⟩
      rw [SubstMol_molRep_f_molRep hd hs, hg]
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨b, rfl, -⟩ := MolMono_of_mem_int Γ hv
      obtain ⟨g, hg, -⟩ := hs.f_inr
      exact ⟨g b, by rw [hg]⟩
  · ext M
    rw [MolMono_mem_ext, Finset.mem_image]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨.inl a, (MolMono_mem_ext Γ _).2 ⟨a, rfl⟩, by rw [hs.f_inl]; rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := (MolMono_mem_ext Γ v).1 hv
      exact ⟨a, by rw [hs.f_inl]; rfl⟩
  · intro e he
    obtain ⟨i, c', rfl, hm, -⟩ := hpres e he
    exact hclsEq i c' hm
  · intro e he
    obtain ⟨i, c', rfl, hm, hc'⟩ := hpres e he
    obtain ⟨hj, hG, hc⟩ := hGe i c' hm
    left
    rw [hG, SubstMol_ends_inl hd', SubstMol_ends_inl hd]
    simp only [Fin.getElem_fin, hc, hc', SubstMol_molRep_f_molRep hd hs]
    rfl
  · intro e' he'
    rcases e' with j | a
    · obtain ⟨i, hi, hij, hφ⟩ := h3 j j.2
      by_cases hc : Γ.toMG'.cls (.inl ⟨i, hi⟩) = none
      · obtain ⟨hj, hG, -⟩ := hGe ⟨i, hi⟩ _ hφ
        have hj' : (⟨ι i, hj⟩ : Fin t.g.comps.length) = j := Fin.ext hij
        rw [← hj', ← hG, hclsEq ⟨i, hi⟩ _ hφ, hc]
      · exfalso
        obtain ⟨hj, hG, -⟩ := hGe ⟨i, hi⟩ _ hφ
        exact he' (.inl ⟨i, hi⟩) hc (by rw [hG]; exact congrArg Sum.inl (Fin.ext hij))
    · exact SubstMol_cls_inr hd' a

/-! ## Globally standard graphs under a change of names -/

section Transport

variable {V E V' E' : Type}

/-- The fields of `MGraph.Transported` with the map of the vertices `f` and of the edges `g`. -/
private structure SubstMol_Tr [DecidableEq V'] (G : MGraph V E) (G' : MGraph V' E') (f : V → V')
    (g : E → E') : Prop where
  inj : Set.InjOn f (↑G.int ∪ ↑G.ext)
  int_eq : G'.int = G.int.image f
  ext_eq : G'.ext = G.ext.image f
  vtx : ∀ e, G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2
  ginj : ∀ e₁ e₂, G.cls e₁ ≠ none → G.cls e₂ ≠ none → g e₁ = g e₂ → e₁ = e₂
  cls_eq : ∀ e, G.cls e ≠ none → G'.cls (g e) = G.cls e
  ends_eq : ∀ e, G.cls e ≠ none → G'.ends (g e) = (f (G.ends e).1, f (G.ends e).2) ∨
    G'.ends (g e) = (f (G.ends e).2, f (G.ends e).1)
  surj : ∀ e', G'.cls e' ≠ none → ∃ e, G.cls e ≠ none ∧ g e = e'

section Lemmas

variable [DecidableEq V'] {G : MGraph V E} {G' : MGraph V' E'} {f : V → V'} {g : E → E'}

private theorem SubstMol_Tr.of (h : G.Transported G') : ∃ f g, SubstMol_Tr G G' f g := by
  obtain ⟨f, g, hg, hf, hint, hext, hv, hc, he, hs⟩ := h
  refine ⟨f, g, hf, hint, hext, hv, hg, hc, he, fun e' he' => ?_⟩
  by_contra hn
  push Not at hn
  exact he' (hs e' fun e h1 h2 => hn e h1 h2)

private theorem SubstMol_T_of {a : V} (ha : G.IsVtx a) :
    a ∈ (↑G.int ∪ ↑G.ext : Set V) := by
  rcases ha with ha | ha
  · exact Or.inl ha
  · exact Or.inr ha

private theorem SubstMol_Tr.mem_image (h : SubstMol_Tr G G' f g) {S : Finset V}
    (hS : ∀ v ∈ S, G.IsVtx v) {a : V} (ha : G.IsVtx a) : f a ∈ S.image f ↔ a ∈ S := by
  constructor
  · intro hm
    obtain ⟨b, hb, hfb⟩ := Finset.mem_image.1 hm
    rw [← h.inj (SubstMol_T_of (hS b hb)) (SubstMol_T_of ha) hfb]
    exact hb
  · exact Finset.mem_image_of_mem f

private theorem SubstMol_Tr.image_subset_iff (h : SubstMol_Tr G G' f g) {S P : Finset V}
    (hS : ∀ v ∈ S, G.IsVtx v) (hP : ∀ v ∈ P, G.IsVtx v) : S.image f ⊆ P.image f ↔ S ⊆ P :=
  ⟨fun hsub a ha => (h.mem_image hP (hS a ha)).1 (hsub (Finset.mem_image_of_mem f ha)),
    fun hsub => Finset.image_subset_image hsub⟩

private theorem SubstMol_Tr.image_ssubset_iff (h : SubstMol_Tr G G' f g) {S P : Finset V}
    (hS : ∀ v ∈ S, G.IsVtx v) (hP : ∀ v ∈ P, G.IsVtx v) : S.image f ⊂ P.image f ↔ S ⊂ P := by
  rw [Finset.ssubset_def, Finset.ssubset_def, h.image_subset_iff hS hP, h.image_subset_iff hP hS]

private theorem SubstMol_Tr.isVtx (h : SubstMol_Tr G G' f g) {a : V} (ha : G.IsVtx a) :
    G'.IsVtx (f a) ↔ G.IsVtx a := by
  simp only [MGraph.IsVtx, h.int_eq, h.ext_eq, h.mem_image (fun v hv => Or.inl hv) ha,
    h.mem_image (fun v hv => Or.inr hv) ha]

private theorem SubstMol_Tr.cut_iff (h : SubstMol_Tr G G' f g) {P : Finset V}
    (hP : ∀ v ∈ P, G.IsVtx v) {e : E} (he : G.cls e ≠ none) :
    G'.Cut (P.image f) (g e) ↔ G.Cut P e := by
  obtain ⟨ha, hb⟩ := h.vtx e he
  unfold MGraph.Cut
  rcases h.ends_eq e he with hE | hE <;> rw [hE] <;> dsimp only <;>
    rw [h.mem_image hP ha, h.mem_image hP hb]
  tauto

private theorem SubstMol_Tr.vtx_iff (h : SubstMol_Tr G G' f g) {e : E} (he : G.cls e ≠ none) :
    G'.IsVtx (G'.ends (g e)).1 ∧ G'.IsVtx (G'.ends (g e)).2 := by
  obtain ⟨ha, hb⟩ := h.vtx e he
  rcases h.ends_eq e he with hE | hE <;> rw [hE] <;> dsimp only
  · exact ⟨(h.isVtx ha).2 ha, (h.isVtx hb).2 hb⟩
  · exact ⟨(h.isVtx hb).2 hb, (h.isVtx ha).2 ha⟩

private theorem SubstMol_Tr.crosses_fwd (h : SubstMol_Tr G G' f g) {P : Finset V}
    (hP : ∀ v ∈ P, G.IsVtx v) {e : E} (hc : G.Crosses P e) : G'.Crosses (P.image f) (g e) := by
  obtain ⟨c1, c2, -, -, cu⟩ := hc
  have hv := h.vtx_iff c1
  exact ⟨by rw [h.cls_eq e c1]; exact c1, by rw [h.cls_eq e c1]; exact c2, hv.1, hv.2,
    (h.cut_iff hP c1).2 cu⟩

private theorem SubstMol_Tr.crosses_bwd (h : SubstMol_Tr G G' f g) {P : Finset V}
    (hP : ∀ v ∈ P, G.IsVtx v) {e' : E'} (hc : G'.Crosses (P.image f) e') :
    ∃ e, g e = e' ∧ G.Crosses P e := by
  obtain ⟨e, he, rfl⟩ := h.surj e' hc.1
  obtain ⟨c1, c2, -, -, cu⟩ := hc
  rw [h.cls_eq e he] at c1 c2
  have hv := h.vtx e he
  exact ⟨e, rfl, c1, c2, hv.1, hv.2, (h.cut_iff hP he).1 cu⟩

private theorem SubstMol_Tr.red_fwd (h : SubstMol_Tr G G' f g) {P : Finset V}
    (hP : ∀ v ∈ P, G.IsVtx v) {e : E} (hc : G.RedCrosses P e) :
    G'.RedCrosses (P.image f) (g e) := by
  obtain ⟨c1, -, -, cu⟩ := hc
  have c0 : G.cls e ≠ none := by rw [c1]; simp
  have hv := h.vtx_iff c0
  exact ⟨by rw [h.cls_eq e c0]; exact c1, hv.1, hv.2, (h.cut_iff hP c0).2 cu⟩

private theorem SubstMol_Tr.red_bwd (h : SubstMol_Tr G G' f g) {P : Finset V}
    (hP : ∀ v ∈ P, G.IsVtx v) {e' : E'} (hc : G'.RedCrosses (P.image f) e') :
    ∃ e, g e = e' ∧ G.RedCrosses P e := by
  obtain ⟨e, he, rfl⟩ := h.surj e' (by rw [hc.1]; simp)
  obtain ⟨c1, -, -, cu⟩ := hc
  rw [h.cls_eq e he] at c1
  have hv := h.vtx e he
  exact ⟨e, rfl, c1, hv.1, hv.2, (h.cut_iff hP he).1 cu⟩

private theorem SubstMol_Tr.iso_iff (h : SubstMol_Tr G G' f g) {P : Finset V}
    (hPi : P ⊆ G.int) : G'.IsIsolated (P.image f) ↔ G.IsIsolated P := by
  have hP : ∀ v ∈ P, G.IsVtx v := fun v hv => Or.inl (hPi hv)
  have hI : ∀ v ∈ G.int, G.IsVtx v := fun v hv => Or.inl hv
  constructor
  · rintro ⟨-, e₁', e₂', hne, hc⟩
    obtain ⟨e₁, rfl, c₁⟩ := h.crosses_bwd hP ((hc e₁').2 (Or.inl rfl))
    obtain ⟨e₂, rfl, c₂⟩ := h.crosses_bwd hP ((hc e₂').2 (Or.inr rfl))
    refine ⟨hPi, e₁, e₂, fun h' => hne (h' ▸ rfl), fun e => ⟨fun hce => ?_, ?_⟩⟩
    · rcases (hc (g e)).1 (h.crosses_fwd hP hce) with he | he
      · exact Or.inl (h.ginj _ _ hce.1 c₁.1 he)
      · exact Or.inr (h.ginj _ _ hce.1 c₂.1 he)
    · rintro (rfl | rfl)
      · exact c₁
      · exact c₂
  · rintro ⟨-, e₁, e₂, hne, hc⟩
    have c₁ := (hc e₁).2 (Or.inl rfl)
    have c₂ := (hc e₂).2 (Or.inr rfl)
    refine ⟨?_, g e₁, g e₂, fun h' => hne (h.ginj _ _ c₁.1 c₂.1 h'), fun e' => ⟨fun hce => ?_, ?_⟩⟩
    · rw [h.int_eq]
      exact Finset.image_subset_image hPi
    · obtain ⟨e, rfl, hce2⟩ := h.crosses_bwd hP hce
      rcases (hc e).1 hce2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact h.crosses_fwd hP c₁
      · exact h.crosses_fwd hP c₂

private theorem SubstMol_Tr.weak_iff (h : SubstMol_Tr G G' f g) {P : Finset V}
    (hPi : P ⊆ G.int) : G'.IsWeaklyIso (P.image f) ↔ G.IsWeaklyIso P := by
  have hP : ∀ v ∈ P, G.IsVtx v := fun v hv => Or.inl (hPi hv)
  unfold MGraph.IsWeaklyIso
  rw [h.iso_iff hPi]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨e₁', e₂', hne, c₁, c₂⟩
    obtain ⟨e₁, rfl, d₁⟩ := h.red_bwd hP c₁
    obtain ⟨e₂, rfl, d₂⟩ := h.red_bwd hP c₂
    exact ⟨e₁, e₂, fun h' => hne (h' ▸ rfl), d₁, d₂⟩
  · rintro ⟨e₁, e₂, hne, c₁, c₂⟩
    have p₁ : G.cls e₁ ≠ none := by rw [c₁.1]; simp
    have p₂ : G.cls e₂ ≠ none := by rw [c₂.1]; simp
    exact ⟨g e₁, g e₂, fun h' => hne (h.ginj _ _ p₁ p₂ h'), h.red_fwd hP c₁, h.red_fwd hP c₂⟩

private theorem SubstMol_Tr.pull (h : SubstMol_Tr G G' f g) {S' : Finset V'} (hS' : S' ⊆ G'.int) :
    ∃ S, S ⊆ G.int ∧ S.image f = S' := by
  classical
  refine ⟨G.int.filter (fun v => f v ∈ S'), Finset.filter_subset _ _, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    exact (Finset.mem_filter.1 ha).2
  · intro hy
    have := hS' hy
    rw [h.int_eq] at this
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 this
    exact Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨ha, hy⟩)

end Lemmas

/-- **Globally standard graphs under a change of names** ([II, Def 6.2]): a change of the names of
the vertices and of the present edges (`MGraph.Transported`) keeps the globally standard
property. -/
theorem SubstMol_gs_transport [DecidableEq V] [DecidableEq E] [DecidableEq V']
    [DecidableEq E'] {G : MGraph V E} {G' : MGraph V' E'} (ht : G.Transported G') :
    G'.GloballyStandard ↔ G.GloballyStandard := by
  have hs := MGraph.spd_transport V E V' E' G G' ht
  obtain ⟨f, g, h⟩ := SubstMol_Tr.of ht
  have hI : ∀ v ∈ G.int, G.IsVtx v := fun v hv => Or.inl hv
  unfold MGraph.GloballyStandard
  rw [hs]
  refine and_congr Iff.rfl ⟨fun h' P hP => ?_, fun h' P' hP' => ?_⟩
  · have hPi : P ⊆ G.int := hP.2.subset
    refine (h.weak_iff hPi).1 (h' _ ⟨(h.iso_iff hPi).2 hP.1, ?_⟩)
    rw [h.int_eq]
    exact (h.image_ssubset_iff (fun v hv => Or.inl (hPi hv)) hI).2 hP.2
  · obtain ⟨P, hPi, rfl⟩ := h.pull hP'.2.subset
    refine (h.weak_iff hPi).2 (h' P ⟨(h.iso_iff hPi).1 hP'.1, ?_⟩)
    rw [h.int_eq] at hP'
    exact (h.image_ssubset_iff (fun v hv => Or.inl (hPi hv)) hI).1 hP'.2

end Transport

/-- **`O_merge` and the sequentially pre-deterministic property** ([II, Def 4.1], [II, Def 5.9] in
the block reading): under the hypotheses of `toMG'_mergeT`, the input of `O_merge` is sequentially
pre-deterministic exactly when its result is. -/
theorem SubstMol_spdPM'_mergeT :
  ∀ (k n : ℕ) (Γ : Graph k n) (t : Tracked k n), 0 < k →
    (∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) →
    Γ.mergeT = some t → (spdPM' Γ ↔ spdPM' t.g) := by
  intro k n Γ t hk hd h
  exact (MGraph.spd_transport _ _ _ _ _ _ (toMG'_mergeT k n Γ t hk hd h)).symm

/-- **`O_merge` and the globally standard property** ([II, Def 4.1], [II, Def 6.2] in the block
reading): under the hypotheses of `toMG'_mergeT`, the input of `O_merge` is globally standard
exactly when its result is. -/
theorem SubstMol_gsPM'_mergeT :
  ∀ (k n : ℕ) (Γ : Graph k n) (t : Tracked k n), 0 < k →
    (∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) →
    Γ.mergeT = some t → (gsPM' Γ ↔ gsPM' t.g) := by
  intro k n Γ t hk hd h
  exact (SubstMol_gs_transport (toMG'_mergeT k n Γ t hk hd h)).symm

/-! ## The substitution of a graph for a `t`-variable -/

section GlueHelpers

variable {m : ℕ}

/-- The atoms of `H` times the `t`-variable `t_{y₁y₂,x}` read in `H` times a substituted graph:
the atoms of `H` keep their names and the atom `α` of the `t`-variable goes to `x`. -/
private def SubstMol_lift (n' : ℕ) (x : Atom 3 m) : Atom 3 (m + 1) → Atom 3 (m + n') :=
  Sum.elim (fun a => .inl a)
    (fun i => if h : i.val < m then .inr ⟨i.val, by omega⟩ else liftA n' x)

private theorem SubstMol_lift_liftA (n' : ℕ) (x u : Atom 3 m) :
    SubstMol_lift n' x (liftA 1 u) = liftA n' u := by
  rcases u with a | i
  · rfl
  · simp only [SubstMol_lift, liftA, Sum.map_inr, Sum.elim_inr, Fin.val_castAdd, i.2,
      dite_true]
    rfl

private theorem SubstMol_lift_newA (n' : ℕ) (x : Atom 3 m) :
    SubstMol_lift n' x (newA (0 : Fin 1)) = liftA n' x := by
  simp [SubstMol_lift, newA]

private theorem SubstMol_liftA_isRight (n' : ℕ) {u : Atom 3 m} (hu : u.isRight = true) :
    (liftA n' u).isRight = true := by
  rcases u with a | a
  · simp at hu
  · rfl

private theorem SubstMol_lift_isRight (n' : ℕ) {x : Atom 3 m} (hx : x.isRight = true)
    {u : Atom 3 (m + 1)} (hu : u.isRight = true) : (SubstMol_lift n' x u).isRight = true := by
  rcases u with a | i
  · simp at hu
  · simp only [SubstMol_lift, Sum.elim_inr]
    split_ifs
    · rfl
    · exact SubstMol_liftA_isRight n' hx

private theorem SubstMol_glueAtom_isRight {n' : ℕ} {x y₁ y₂ : Atom 3 m} (hx : x.isRight = true)
    (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true) (w : Atom 3 n') :
    (glueAtom x y₁ y₂ w).isRight = true := by
  rcases w with i | j
  · change (liftA n' (![x, y₁, y₂] i)).isRight = true
    fin_cases i
    · exact SubstMol_liftA_isRight n' hx
    · exact SubstMol_liftA_isRight n' hy₁
    · exact SubstMol_liftA_isRight n' hy₂
  · rfl

private theorem SubstMol_glue_length {n'' : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (𝒢 : Graph 3 n'') :
    (H.glue x y₁ y₂ 𝒢).comps.length = H.comps.length + 𝒢.comps.length := by
  simp [Graph.glue, liftCs]

private theorem SubstMol_glue_getL {n'' : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (𝒢 : Graph 3 n'') (i : ℕ) (hi : i < H.comps.length)
    (h : i < (H.glue x y₁ y₂ 𝒢).comps.length) :
    (H.glue x y₁ y₂ 𝒢).comps[i] = H.comps[i].map (liftA n'') := by
  simp [Graph.glue, liftCs, List.getElem_append_left, hi]

private theorem SubstMol_glue_getR {n'' : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (𝒢 : Graph 3 n'') (j : ℕ) (hj : j < 𝒢.comps.length)
    (h : H.comps.length + j < (H.glue x y₁ y₂ 𝒢).comps.length) :
    (H.glue x y₁ y₂ 𝒢).comps[H.comps.length + j] = 𝒢.comps[j].map (glueAtom x y₁ y₂) := by
  simp [Graph.glue, liftCs, List.getElem_append_right]

private theorem SubstMol_glue_mem {n'' : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (𝒢 : Graph 3 n'') {c : Comp (Atom 3 (m + n''))} (hc : c ∈ (H.glue x y₁ y₂ 𝒢).comps) :
    (∃ c₀ ∈ H.comps, c = c₀.map (liftA n'')) ∨
      ∃ c₀ ∈ 𝒢.comps, c = c₀.map (glueAtom x y₁ y₂) := by
  simp only [Graph.glue, liftCs, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨c₀, h, rfl⟩ | ⟨c₀, h, rfl⟩
  · exact Or.inl ⟨c₀, h, rfl⟩
  · exact Or.inr ⟨c₀, h, rfl⟩

private theorem SubstMol_tVar_comps : (tVar true).comps =
    [mkC (.waved .s) (.inr 0) (.inl 0), mkC (.G .plus) (.inl 1) (.inr 0),
      mkC (.G .minus) (.inl 2) (.inr 0), mkC .xdot (.inl 1) (.inr 0),
      mkC .xdot (.inl 2) (.inr 0)] := rfl

end GlueHelpers

section GlueCore

variable {m n' : ℕ}

set_option hygiene false in
/-- The graph `H` times the `t`-variable `t_{y₁y₂,x}`. -/
local notation "𝔾" => Graph.glue H x y₁ y₂ (tVar true)

set_option hygiene false in
/-- The graph `H` times the substituted graph `g`. -/
local notation "𝔾t" => Graph.glue H x y₁ y₂ g

/-- The facts on the molecules of `H` times `t_{y₁y₂,x}` and of `H` times `g` behind
`toMG'_glue`. -/
private theorem SubstMol_glue_facts (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (hD : (𝔾).DotFree) (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) :
    (∀ c ∈ (𝔾).comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) ∧
    (∀ c ∈ (𝔾t).comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) ∧
    (∀ v, (𝔾t).molRep (SubstMol_lift n' x ((𝔾).molRep v)) =
      (𝔾t).molRep (SubstMol_lift n' x v)) ∧
    (∀ u v, (𝔾).SameMol u v → (𝔾t).SameMol (SubstMol_lift n' x u) (SubstMol_lift n' x v)) ∧
    (∀ p q, g.SameMol p q → (𝔾t).SameMol (glueAtom x y₁ y₂ p) (glueAtom x y₁ y₂ q)) ∧
    (∀ u, (𝔾t).molRep (glueAtom x y₁ y₂ (g.flatAtom u)) = (𝔾t).molRep (glueAtom x y₁ y₂ u)) := by
  have hgR := SubstMol_glueAtom_isRight (n' := n') hx hy₁ hy₂
  have hH : ∀ c ∈ H.comps, c.kind ≠ .dot := by
    intro c hc
    have := hD (c.map (liftA 1)) (by
      simp only [Graph.glue, liftCs, List.mem_append, List.mem_map]
      exact Or.inl ⟨c, hc, rfl⟩)
    exact this
  have hdG : ∀ c ∈ (𝔾).comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true :=
    fun c hc hk => absurd hk (hD c hc)
  have hdGt : ∀ c ∈ (𝔾t).comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true := by
    intro c hc hk
    rcases SubstMol_glue_mem H x y₁ y₂ g hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₀, -, rfl⟩
    · exact absurd hk (hH c₀ hc₀)
    · exact ⟨hgR _, hgR _⟩
  have M2 : ∀ u v, (𝔾).SameMol u v →
      (𝔾t).SameMol (SubstMol_lift n' x u) (SubstMol_lift n' x v) := by
    intro u v h
    refine SubstMol_sameMol_map _ (fun u hu => SubstMol_lift_isRight n' hx hu)
      (fun c hc hj => ?_) h
    rcases SubstMol_glue_mem H x y₁ y₂ (tVar true) hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₀, hc₀, rfl⟩
    · refine Or.inr ⟨c₀.map (liftA n'), ?_, hj, ?_, ?_⟩
      · simp only [Graph.glue, liftCs, List.mem_append, List.mem_map]
        exact Or.inl ⟨c₀, hc₀, rfl⟩
      · exact (SubstMol_lift_liftA n' x c₀.x).symm
      · exact (SubstMol_lift_liftA n' x c₀.y).symm
    · left
      rw [SubstMol_tVar_comps] at hc₀
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc₀
      rcases hc₀ with rfl | rfl | rfl | rfl | rfl
      · change SubstMol_lift n' x (newA 0) = SubstMol_lift n' x (liftA 1 x)
        rw [SubstMol_lift_newA, SubstMol_lift_liftA]
      all_goals simp [Comp.map, mkC, Kind.joinsMol] at hj
  have M1 : ∀ v, (𝔾t).molRep (SubstMol_lift n' x ((𝔾).molRep v)) =
      (𝔾t).molRep (SubstMol_lift n' x v) := by
    intro v
    rw [SubstMol_molRep_eq_iff]
    exact M2 _ _ ((𝔾).sameMol_equivalence.symm (SubstMol_molRep_spec _ v))
  have hcg : ∀ c ∈ g.comps, c.map (glueAtom x y₁ y₂) ∈ (𝔾t).comps := by
    intro c hc
    simp only [Graph.glue, liftCs, List.mem_append, List.mem_map]
    exact Or.inr ⟨c, hc, rfl⟩
  have M4 : ∀ p q, g.SameMol p q → (𝔾t).SameMol (glueAtom x y₁ y₂ p) (glueAtom x y₁ y₂ q) :=
    fun p q h => SubstMol_sameMol_map _ (fun u _ => hgR u)
      (fun c hc hj => Or.inr ⟨_, hcg c hc, hj, rfl, rfl⟩) h
  have M4b : ∀ p q, g.SameBlock p q →
      (𝔾t).SameMol (glueAtom x y₁ y₂ p) (glueAtom x y₁ y₂ q) := by
    intro p q h
    have hb : (𝔾t).SameBlock (glueAtom x y₁ y₂ p) (glueAtom x y₁ y₂ q) :=
      SubstMol_sameBlock_map _ (fun c hc hk => Or.inr ⟨_, hcg c hc, hk, rfl, rfl⟩) h
    exact Or.inr ⟨hgR _, hgR _, SubstMol_block_le_mol hb⟩
  refine ⟨hdG, hdGt, M1, M2, M4, fun u => ?_⟩
  rw [SubstMol_molRep_eq_iff]
  rcases u with a | a
  · classical
    unfold Graph.flatAtom
    cases hA : g.anchor (.inl a) with
    | none => exact Or.inl rfl
    | some b =>
      rw [MolMono_anchor_eq_find] at hA
      have hb : g.SameBlock (.inl a) (.inr b) := by
        simpa using List.find?_some hA
      exact (𝔾t).sameMol_equivalence.symm (M4b _ _ hb)
  · exact Or.inl rfl

end GlueCore

section GlueMain

variable {m n' : ℕ}

set_option hygiene false in
/-- The graph `H` times the `t`-variable `t_{y₁y₂,x}`. -/
local notation "𝔾" => Graph.glue H x y₁ y₂ (tVar true)

set_option hygiene false in
/-- The graph `H` times the substituted graph `g`. -/
local notation "𝔾t" => Graph.glue H x y₁ y₂ g

set_option hygiene false in
/-- The molecular graph of `g` inserted into that of `H` times `t_{y₁y₂,x}`. -/
local notation "𝕀" => MGraph.insert (Graph.glue H x y₁ y₂ (tVar true)).toMG' g.toMG' σ B

/-- `toMG'_glue` with the maps `σ`, `ρ` and the set `B` given by their values. -/
private theorem SubstMol_glue_core (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (hD : (𝔾).DotFree) (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) (σ : Atom 3 n' → Atom 3 (m + 1))
    (hσ : ∀ i, σ (.inl i) = (𝔾).molRep (liftA 1 (![x, y₁, y₂] i)))
    (B : Finset (Fin (𝔾).comps.length ⊕ Fin 3))
    (hB : ∀ i : Fin (𝔾).comps.length,
      Sum.inl i ∈ B ↔ (i.val = H.comps.length + 1 ∨ i.val = H.comps.length + 2))
    (ρ : Atom 3 (m + 1) ⊕ Atom 3 n' → Atom 3 (m + n'))
    (hρl : ∀ v, ρ (.inl v) = SubstMol_lift n' x v)
    (hρr : ∀ w, ρ (.inr w) = glueAtom x y₁ y₂ w) :
    ∃ π : Atom 3 (m + 1) ⊕ Atom 3 n' → Atom 3 (m + 1) ⊕ Atom 3 n',
      (∀ v, π (π v) = π v) ∧ (∀ v ∈ (𝕀).int, π v ∈ (𝕀).int) ∧ (∀ v ∈ (𝕀).ext, π v = v) ∧
      (∀ v ∈ (𝕀).int, π v ∉ (𝕀).ext) ∧ Disjoint (𝕀).int (𝕀).ext ∧
      (∀ e, (𝕀).cls e ≠ none → (𝕀).IsVtx ((𝕀).ends e).1 ∧ (𝕀).IsVtx ((𝕀).ends e).2) ∧
      (∀ z ∈ (𝕀).int, ∀ z' ∈ (𝕀).int, (π z = π z' ↔ (𝔾t).SameMol (ρ z) (ρ z'))) ∧
      (((𝕀).mapV π).unloop).Transported (𝔾t).toMG' := by
  classical
  obtain ⟨hdG, hdGt, M1, M2, M4, Mflat⟩ := SubstMol_glue_facts H x y₁ y₂ g hD hx hy₁ hy₂
  set μ : Atom 3 (m + 1) ⊕ Atom 3 n' → Atom 3 (m + n') := fun z => (𝔾t).molRep (ρ z) with hμ
  have hμl : ∀ v, μ (.inl v) = (𝔾t).molRep (SubstMol_lift n' x v) := fun v => by
    rw [hμ]; dsimp only; rw [hρl]
  have hμr : ∀ w, μ (.inr w) = (𝔾t).molRep (glueAtom x y₁ y₂ w) := fun w => by
    rw [hμ]; dsimp only; rw [hρr]
  -- the external atoms of `g` go to internal molecules of `H` times `t_{y₁y₂,x}`
  have hσint : ∀ i, σ (.inl i) ∈ (𝔾).toMG'.int := by
    intro i
    have he : (![x, y₁, y₂] i).isRight = true := by
      fin_cases i
      exacts [hx, hy₁, hy₂]
    obtain ⟨t, ht⟩ : ∃ t, liftA 1 (![x, y₁, y₂] i) = .inr t := by
      rcases h : liftA 1 (![x, y₁, y₂] i) with a | t
      · have := SubstMol_liftA_isRight 1 he
        rw [h] at this
        simp at this
      · exact ⟨t, rfl⟩
    rw [hσ, ht]
    exact MolMono_molRep_mem_int _ t
  have Mext : ∀ i, μ (.inl (σ (.inl i))) = (𝔾t).molRep (glueAtom x y₁ y₂ (.inl i)) := by
    intro i
    rw [hμl, hσ, M1, SubstMol_lift_liftA]
    rfl
  set τ : Atom 3 n' → Atom 3 (m + 1) ⊕ Atom 3 n' :=
    fun w => if w ∈ g.toMG'.int then .inr w else .inl (σ w) with hτdef
  have hflat_inl : ∀ u a, g.flatAtom u = .inl a → u = .inl a := by
    intro u a h
    rcases u with a' | b'
    · unfold Graph.flatAtom at h
      cases hA : g.anchor (.inl a') with
      | none => rw [hA] at h; exact h
      | some b => rw [hA] at h; cases h
    · cases h
  have hrepg : ∀ p, (𝔾t).molRep (glueAtom x y₁ y₂ (g.molRep p)) =
      (𝔾t).molRep (glueAtom x y₁ y₂ p) := fun p =>
    (SubstMol_molRep_eq_iff _ _ _).2 (M4 _ _ (g.sameMol_equivalence.symm
      (SubstMol_molRep_spec g p)))
  have M3 : ∀ u, μ (τ (g.molRep (g.flatAtom u))) = (𝔾t).molRep (glueAtom x y₁ y₂ u) := by
    intro u
    by_cases hw : g.molRep (g.flatAtom u) ∈ g.toMG'.int
    · rw [hτdef]
      dsimp only
      rw [ite_eq_left hw, hμr, hrepg, Mflat]
    · rcases hf : g.flatAtom u with a | b
      · rw [hf] at hw
        have hu := hflat_inl u a hf
        subst hu
        change μ (τ (.inl a)) = _
        rw [hτdef]
        dsimp only
        rw [ite_eq_right (MolMono_inl_not_mem_int g a)]
        exact Mext a
      · rw [hf] at hw
        exact absurd (MolMono_molRep_mem_int g b) hw
  have hτ : ∀ w, g.toMG'.IsVtx w → τ w ∈ (𝕀).int := by
    intro w hw
    by_cases hwi : w ∈ g.toMG'.int
    · rw [hτdef]
      dsimp only
      rw [ite_eq_left hwi]
      exact Finset.inr_mem_disjSum.2 hwi
    · rcases hw with hw | hw
      · exact absurd hw hwi
      · obtain ⟨i, rfl⟩ := (MolMono_mem_ext g w).1 hw
        rw [hτdef]
        dsimp only
        rw [ite_eq_right hwi]
        exact Finset.inl_mem_disjSum.2 (hσint i)
  -- the vertices of the inserted graph
  have hGint : ∀ z, z ∈ (𝕀).int ↔
      (∃ v ∈ (𝔾).toMG'.int, z = .inl v) ∨ (∃ w ∈ g.toMG'.int, z = .inr w) := by
    intro z
    change z ∈ (𝔾).toMG'.int.disjSum g.toMG'.int ↔ _
    rw [Finset.mem_disjSum]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact Or.inl ⟨v, hv, rfl⟩
      · exact Or.inr ⟨w, hw, rfl⟩
    · rintro (⟨v, hv, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact Or.inl ⟨v, hv, rfl⟩
      · exact Or.inr ⟨w, hw, rfl⟩
  have hGext : ∀ z, z ∈ (𝕀).ext ↔ ∃ a : Fin 3, z = .inl (.inl a) := by
    intro z
    change z ∈ (𝔾).toMG'.ext.map Function.Embedding.inl ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := (MolMono_mem_ext _ v).1 hv
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨.inl a, (MolMono_mem_ext _ _).2 ⟨a, rfl⟩, rfl⟩
  have hdisj : Disjoint (𝕀).int (𝕀).ext := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨a, rfl⟩ := (hGext z).1 hz'
    rcases (hGint _).1 hz with ⟨v, hv, hv'⟩ | ⟨w, -, hw'⟩
    · cases hv'
      exact MolMono_inl_not_mem_int _ a hv
    · cases hw'
  have hμR : ∀ z ∈ (𝕀).int, (μ z).isRight = true := by
    intro z hz
    rcases (hGint z).1 hz with ⟨v, hv, rfl⟩ | ⟨w, hw, rfl⟩
    · rw [hμl]
      exact SubstMol_molRep_isRight _ (SubstMol_lift_isRight n' hx (SubstMol_int_isRight hv))
    · rw [hμr]
      exact SubstMol_molRep_isRight _ (SubstMol_glueAtom_isRight hx hy₁ hy₂ w)
  have hμE : ∀ a : Fin 3, μ (.inl (.inl a)) = .inl a := fun a => by
    rw [hμl]
    rfl
  -- the map `π`: each internal vertex goes to a chosen vertex of its molecule in `H` times `g`
  have : Nonempty (Atom 3 (m + 1) ⊕ Atom 3 n') := ⟨.inl (.inl 0)⟩
  set π : Atom 3 (m + 1) ⊕ Atom 3 n' → Atom 3 (m + 1) ⊕ Atom 3 n' := fun z =>
    if z ∈ (𝕀).int then Function.invFunOn μ ↑(𝕀).int (μ z) else z with hπdef
  have hπint : ∀ z ∈ (𝕀).int, π z ∈ (𝕀).int ∧ μ (π z) = μ z := by
    intro z hz
    have h := Function.invFunOn_pos (f := μ) (s := ↑(𝕀).int) ⟨z, hz, rfl⟩
    rw [hπdef]
    dsimp only
    rw [ite_eq_left hz]
    exact ⟨Finset.mem_coe.1 h.1, h.2⟩
  have hπout : ∀ z, z ∉ (𝕀).int → π z = z := by
    intro z hz
    rw [hπdef]
    dsimp only
    rw [ite_eq_right hz]
  have hπeq : ∀ z ∈ (𝕀).int, ∀ z' ∈ (𝕀).int, (π z = π z' ↔ μ z = μ z') := by
    intro z hz z' hz'
    constructor
    · intro h
      rw [← (hπint z hz).2, ← (hπint z' hz').2, h]
    · intro h
      rw [hπdef]
      dsimp only
      rw [ite_eq_left hz, ite_eq_left hz', h]
  have hidem : ∀ z, π (π z) = π z := by
    intro z
    by_cases hz : z ∈ (𝕀).int
    · exact (hπeq _ (hπint z hz).1 z hz).2 (hπint z hz).2
    · rw [hπout z hz, hπout z hz]
  have hπvtx : ∀ z, (𝕀).IsVtx z → (𝕀).IsVtx (π z) ∧ μ (π z) = μ z := by
    intro z hz
    by_cases hzi : z ∈ (𝕀).int
    · exact ⟨Or.inl (hπint z hzi).1, (hπint z hzi).2⟩
    · rw [hπout z hzi]
      exact ⟨hz, rfl⟩
  have hPV : ∀ z z', (𝕀).IsVtx z → (𝕀).IsVtx z' → (π z = π z' ↔ μ z = μ z') := by
    have hie : ∀ z z', z ∈ (𝕀).int → z' ∈ (𝕀).ext → ¬ π z = π z' ∧ ¬ μ z = μ z' := by
      intro z z' hz hz'
      have hz'i : z' ∉ (𝕀).int := fun h => Finset.disjoint_left.1 hdisj h hz'
      obtain ⟨a, rfl⟩ := (hGext z').1 hz'
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [hπout _ hz'i] at h
        exact Finset.disjoint_left.1 hdisj (hπint z hz).1 (h ▸ hz')
      · have := hμR z hz
        rw [h, hμE] at this
        simp at this
    intro z z' hz hz'
    rcases hz with hz | hz <;> rcases hz' with hz' | hz'
    · exact hπeq z hz z' hz'
    · exact iff_of_false (hie z z' hz hz').1 (hie z z' hz hz').2
    · exact iff_of_false (fun h => (hie z' z hz' hz).1 h.symm)
        (fun h => (hie z' z hz' hz).2 h.symm)
    · obtain ⟨a, rfl⟩ := (hGext z).1 hz
      obtain ⟨a', rfl⟩ := (hGext z').1 hz'
      have h1 : (.inl (.inl a) : Atom 3 (m + 1) ⊕ Atom 3 n') ∉ (𝕀).int :=
        fun h => Finset.disjoint_left.1 hdisj h hz
      have h2 : (.inl (.inl a') : Atom 3 (m + 1) ⊕ Atom 3 n') ∉ (𝕀).int :=
        fun h => Finset.disjoint_left.1 hdisj h hz'
      rw [hπout _ h1, hπout _ h2, hμE, hμE]
      simp
  -- every edge of the inserted graph joins two vertices
  have hR2 : ∀ e, (𝕀).IsVtx ((𝕀).ends e).1 ∧ (𝕀).IsVtx ((𝕀).ends e).2 := by
    have hK : ∀ v, (𝔾).toMG'.IsVtx v → (𝕀).IsVtx (.inl v) := by
      intro v hv
      rcases hv with hv | hv
      · exact Or.inl (Finset.inl_mem_disjSum.2 hv)
      · obtain ⟨a, rfl⟩ := (MolMono_mem_ext _ v).1 hv
        exact Or.inr ((hGext _).2 ⟨a, rfl⟩)
    intro e
    rcases e with e | f
    · exact ⟨hK _ (MolInsert_toMG'_ends_vtx _ _ _ e).1, hK _ (MolInsert_toMG'_ends_vtx _ _ _ e).2⟩
    · exact ⟨Or.inl (hτ _ (MolInsert_toMG'_ends_vtx _ _ _ f).1),
        Or.inl (hτ _ (MolInsert_toMG'_ends_vtx _ _ _ f).2)⟩
  -- the edges
  have hlenG : (𝔾).comps.length = H.comps.length + 5 := by
    rw [SubstMol_glue_length, SubstMol_tVar_comps]
    rfl
  have hlenGt : (𝔾t).comps.length = H.comps.length + g.comps.length :=
    SubstMol_glue_length H x y₁ y₂ g
  set Ge : (Fin (𝔾).comps.length ⊕ Fin 3) ⊕ (Fin g.comps.length ⊕ Fin 3) →
      Fin (𝔾t).comps.length ⊕ Fin 3 :=
    Sum.elim (Sum.elim (fun i => if h : i.val < H.comps.length then
        .inl ⟨i.val, by rw [hlenGt]; omega⟩ else .inr 0) .inr)
      (Sum.elim (fun j => .inl ⟨H.comps.length + j.val, by rw [hlenGt]; have := j.2; omega⟩)
        .inr) with hGedef
  set S := ((𝕀).mapV π).unloop with hSdef
  have hScls : ∀ e, S.cls e = if π ((𝕀).ends e).1 = π ((𝕀).ends e).2 then none
      else (𝕀).cls e := fun e => rfl
  have hSends : ∀ e, S.ends e = (π ((𝕀).ends e).1, π ((𝕀).ends e).2) := fun e => rfl
  -- the components of `H`
  have CLS1 : ∀ (i : Fin (𝔾).comps.length) (hi : i.val < H.comps.length),
      Ge (.inl (.inl i)) = .inl ⟨i.val, by rw [hlenGt]; omega⟩ ∧
      (𝔾t).toMG'.cls (Ge (.inl (.inl i))) = S.cls (.inl (.inl i)) ∧
      (S.cls (.inl (.inl i)) ≠ none → (𝔾t).toMG'.ends (Ge (.inl (.inl i))) =
        (μ (S.ends (.inl (.inl i))).1, μ (S.ends (.inl (.inl i))).2)) := by
    intro i hi
    have hGe : Ge (.inl (.inl i)) = .inl ⟨i.val, by rw [hlenGt]; omega⟩ := by
      rw [hGedef]
      simp only [Sum.elim_inl]
      rw [dite_eq_left hi]
    refine ⟨hGe, ?_⟩
    have hGi : (𝔾).comps[i] = H.comps[i.val].map (liftA 1) :=
      SubstMol_glue_getL H x y₁ y₂ (tVar true) i.val hi i.2
    have hGti : (𝔾t).comps[i.val]'(by rw [hlenGt]; omega) = H.comps[i.val].map (liftA n') :=
      SubstMol_glue_getL H x y₁ y₂ g i.val hi _
    have hnB : Sum.inl i ∉ B := by
      rw [hB]
      omega
    set c₀ := H.comps[i.val] with hc₀
    have hKc : (𝔾).toMG'.cls (.inl i) = if c₀.kind = .dot ∨
        (𝔾).molRep (liftA 1 c₀.x) = (𝔾).molRep (liftA 1 c₀.y) then none
        else c₀.kind.mclass := by
      rw [SubstMol_cls_inl hdG, hGi]
      rfl
    have hKe : (𝔾).toMG'.ends (.inl i) =
        ((𝔾).molRep (liftA 1 c₀.x), (𝔾).molRep (liftA 1 c₀.y)) := by
      rw [SubstMol_ends_inl hdG, hGi]
      rfl
    have hTc : (𝔾t).toMG'.cls (.inl ⟨i.val, by rw [hlenGt]; omega⟩) = if c₀.kind = .dot ∨
        (𝔾t).molRep (liftA n' c₀.x) = (𝔾t).molRep (liftA n' c₀.y) then none
        else c₀.kind.mclass := by
      rw [SubstMol_cls_inl hdGt]
      simp only [Fin.getElem_fin, hGti]
      rfl
    have hTe : (𝔾t).toMG'.ends (.inl ⟨i.val, by rw [hlenGt]; omega⟩) =
        ((𝔾t).molRep (liftA n' c₀.x), (𝔾t).molRep (liftA n' c₀.y)) := by
      rw [SubstMol_ends_inl hdGt]
      simp only [Fin.getElem_fin, hGti]
      rfl
    have hIe : (𝕀).ends (.inl (.inl i)) =
        (.inl ((𝔾).molRep (liftA 1 c₀.x)), .inl ((𝔾).molRep (liftA 1 c₀.y))) := by
      change (Sum.inl ((𝔾).toMG'.ends (.inl i)).1, Sum.inl ((𝔾).toMG'.ends (.inl i)).2) = _
      rw [hKe]
    have hIc : (𝕀).cls (.inl (.inl i)) = (𝔾).toMG'.cls (.inl i) := by
      change (if Sum.inl i ∈ B then none else (𝔾).toMG'.cls (.inl i)) = _
      rw [ite_eq_right hnB]
    have hv : ∀ u, (𝕀).IsVtx (.inl ((𝔾).molRep u)) := by
      intro u
      rcases MolMono_molRep_isVtx (𝔾) u with h | h
      · exact Or.inl (Finset.inl_mem_disjSum.2 h)
      · obtain ⟨a, ha⟩ := (MolMono_mem_ext _ _).1 h
        rw [ha]
        exact Or.inr ((hGext _).2 ⟨a, rfl⟩)
    have hμv : ∀ u, μ (.inl ((𝔾).molRep (liftA 1 u))) = (𝔾t).molRep (liftA n' u) := by
      intro u
      rw [hμl, M1, SubstMol_lift_liftA]
    have himp : (𝔾).molRep (liftA 1 c₀.x) = (𝔾).molRep (liftA 1 c₀.y) →
        (𝔾t).molRep (liftA n' c₀.x) = (𝔾t).molRep (liftA n' c₀.y) := by
      intro h
      rw [SubstMol_molRep_eq_iff] at h ⊢
      have := M2 _ _ h
      rwa [SubstMol_lift_liftA, SubstMol_lift_liftA] at this
    have hpe : π (.inl ((𝔾).molRep (liftA 1 c₀.x))) = π (.inl ((𝔾).molRep (liftA 1 c₀.y))) ↔
        (𝔾t).molRep (liftA n' c₀.x) = (𝔾t).molRep (liftA n' c₀.y) := by
      rw [hPV _ _ (hv _) (hv _), hμv, hμv]
    rw [hGe, hScls, hIe, hIc, hKc, hTc]
    dsimp only
    refine ⟨?_, fun hne => ?_⟩
    · by_cases hq : (𝔾t).molRep (liftA n' c₀.x) = (𝔾t).molRep (liftA n' c₀.y)
      · rw [ite_eq_left (hpe.2 hq), ite_eq_left (Or.inr hq)]
      · rw [ite_eq_right (fun h => hq (hpe.1 h))]
        by_cases hk : c₀.kind = .dot
        · rw [ite_eq_left (Or.inl hk), ite_eq_left (Or.inl hk)]
        · rw [ite_eq_right (by tauto), ite_eq_right (by tauto)]
    · rw [hSends, hIe, hTe]
      dsimp only
      rw [(hπvtx _ (hv _)).2, (hπvtx _ (hv _)).2, hμv, hμv]
  -- the components of `g`
  have CLS2 : ∀ j : Fin g.comps.length,
      Ge (.inr (.inl j)) = .inl ⟨H.comps.length + j.val, by rw [hlenGt]; have := j.2; omega⟩ ∧
      (𝔾t).toMG'.cls (Ge (.inr (.inl j))) = S.cls (.inr (.inl j)) ∧
      (S.cls (.inr (.inl j)) ≠ none → (𝔾t).toMG'.ends (Ge (.inr (.inl j))) =
        (μ (S.ends (.inr (.inl j))).1, μ (S.ends (.inr (.inl j))).2)) := by
    intro j
    have hGe : Ge (.inr (.inl j)) =
        .inl ⟨H.comps.length + j.val, by rw [hlenGt]; have := j.2; omega⟩ := rfl
    refine ⟨hGe, ?_⟩
    have hGtj : (𝔾t).comps[H.comps.length + j.val]'(by rw [hlenGt]; have := j.2; omega) =
        g.comps[j.val].map (glueAtom x y₁ y₂) :=
      SubstMol_glue_getR H x y₁ y₂ g j.val j.2 _
    set c := g.comps[j.val] with hc
    have hTc : (𝔾t).toMG'.cls (.inl ⟨H.comps.length + j.val, by rw [hlenGt]; have := j.2; omega⟩)
        = if c.kind = .dot ∨ (𝔾t).molRep (glueAtom x y₁ y₂ c.x) =
          (𝔾t).molRep (glueAtom x y₁ y₂ c.y) then none else c.kind.mclass := by
      rw [SubstMol_cls_inl hdGt]
      simp only [Fin.getElem_fin, hGtj]
      rfl
    have hTe : (𝔾t).toMG'.ends (.inl ⟨H.comps.length + j.val, by rw [hlenGt]; have := j.2; omega⟩)
        = ((𝔾t).molRep (glueAtom x y₁ y₂ c.x), (𝔾t).molRep (glueAtom x y₁ y₂ c.y)) := by
      rw [SubstMol_ends_inl hdGt]
      simp only [Fin.getElem_fin, hGtj]
      rfl
    have hIc : (𝕀).cls (.inr (.inl j)) = g.toMG'.cls (.inl j) := rfl
    have hIe : (𝕀).ends (.inr (.inl j)) =
        (τ (g.toMG'.ends (.inl j)).1, τ (g.toMG'.ends (.inl j)).2) := rfl
    rw [hGe, hTc, hScls, hIc]
    by_cases hk : c.kind = .dot
    · have hLc : g.toMG'.cls (.inl j) = none := by
        rw [SubstMol_cls_inl', SubstMol_flatComp_kind]
        exact ite_eq_left (Or.inl hk)
      rw [hLc, ite_eq_left (Or.inl hk)]
      exact ⟨by split_ifs <;> rfl, fun h => absurd (by split_ifs <;> rfl) h⟩
    · have hfl : g.flatComp c = { c with x := g.flatAtom c.x, y := g.flatAtom c.y } := by
        unfold Graph.flatComp
        rw [ite_eq_right hk]
      have hLc : g.toMG'.cls (.inl j) = if c.kind = .dot ∨
          g.molRep (g.flatAtom c.x) = g.molRep (g.flatAtom c.y) then none
          else c.kind.mclass := by
        rw [SubstMol_cls_inl']
        simp only [Fin.getElem_fin, ← hc, hfl]
      have hLe : g.toMG'.ends (.inl j) =
          (g.molRep (g.flatAtom c.x), g.molRep (g.flatAtom c.y)) := by
        rw [SubstMol_ends_inl']
        simp only [Fin.getElem_fin, ← hc, hfl]
      have hv : ∀ u, (𝕀).IsVtx (τ (g.molRep (g.flatAtom u))) :=
        fun u => Or.inl (hτ _ (MolMono_molRep_isVtx g _))
      have hpe : π (τ (g.molRep (g.flatAtom c.x))) = π (τ (g.molRep (g.flatAtom c.y))) ↔
          (𝔾t).molRep (glueAtom x y₁ y₂ c.x) = (𝔾t).molRep (glueAtom x y₁ y₂ c.y) := by
        rw [hPV _ _ (hv _) (hv _), M3, M3]
      have himp : g.molRep (g.flatAtom c.x) = g.molRep (g.flatAtom c.y) →
          (𝔾t).molRep (glueAtom x y₁ y₂ c.x) = (𝔾t).molRep (glueAtom x y₁ y₂ c.y) := by
        intro h
        rw [← M3, ← M3, h]
      rw [hIe, hLe, hLc]
      dsimp only
      refine ⟨?_, fun hne => ?_⟩
      · by_cases hq : (𝔾t).molRep (glueAtom x y₁ y₂ c.x) = (𝔾t).molRep (glueAtom x y₁ y₂ c.y)
        · rw [ite_eq_left (hpe.2 hq), ite_eq_left (Or.inr hq)]
        · rw [ite_eq_right (fun h => hq (hpe.1 h)), ite_eq_right (by tauto),
            ite_eq_right (by tauto)]
      · rw [hSends, hIe, hLe, hTe]
        dsimp only
        rw [(hπvtx _ (hv _)).2, (hπvtx _ (hv _)).2, M3, M3]
  -- the other edges are absent
  have hpres : ∀ e, S.cls e ≠ none →
      (∃ i : Fin (𝔾).comps.length, i.val < H.comps.length ∧ e = .inl (.inl i)) ∨
        ∃ j : Fin g.comps.length, e = .inr (.inl j) := by
    intro e he
    have hnone : (𝕀).cls e = none → S.cls e = none := by
      intro h
      rw [hScls, h]
      split_ifs <;> rfl
    rcases e with (i | a) | (j | a)
    · by_cases hi : i.val < H.comps.length
      · exact Or.inl ⟨i, hi, rfl⟩
      · exfalso
        apply he
        apply hnone
        change (if Sum.inl i ∈ B then none else (𝔾).toMG'.cls (.inl i)) = none
        by_cases hiB : Sum.inl i ∈ B
        · rw [ite_eq_left hiB]
        · rw [ite_eq_right hiB, SubstMol_cls_inl hdG]
          rw [hB] at hiB
          obtain ⟨j', hj'⟩ : ∃ j', i.val = H.comps.length + j' := ⟨i.val - H.comps.length, by omega⟩
          have hj5 : j' < (tVar true).comps.length := by
            rw [SubstMol_tVar_comps]
            have := i.2
            simp only [List.length_cons, List.length_nil]
            omega
          have hGi : (𝔾).comps[i] = ((tVar true).comps[j']).map (glueAtom x y₁ y₂) := by
            have := SubstMol_glue_getR H x y₁ y₂ (tVar true) j' hj5 (by rw [← hj']; exact i.2)
            simp only [Fin.getElem_fin]
            rw [← this]
            congr 1
          have hmc : ((𝔾).comps[i]).kind.mclass = none := by
            rw [hGi]
            change ((tVar true).comps[j']).kind.mclass = none
            simp only [SubstMol_tVar_comps]
            have h1 : j' ≠ 1 := by omega
            have h2 : j' ≠ 2 := by omega
            rw [SubstMol_tVar_comps] at hj5
            simp only [List.length_cons, List.length_nil] at hj5
            interval_cases j' <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2
          rw [hmc]
          split_ifs <;> rfl
    · exfalso
      apply he
      apply hnone
      change (if Sum.inr a ∈ B then none else (𝔾).toMG'.cls (.inr a)) = none
      rw [SubstMol_cls_inr hdG]
      split_ifs <;> rfl
    · exact Or.inr ⟨j, rfl⟩
    · exfalso
      apply he
      rw [hScls]
      change (if π (τ (g.toMG'.ends (.inr a)).1) = π (τ (g.toMG'.ends (.inr a)).2) then none
        else g.toMG'.cls (.inr a)) = none
      cases hA : g.anchor (.inl a) with
      | none =>
        have hLc : g.toMG'.cls (.inr a) = none := by
          change (match g.anchor (.inl a) with
            | some _ => some (pinClass a)
            | none => none) = none
          rw [hA]
        rw [hLc]
        split_ifs <;> rfl
      | some b =>
        have hLe : g.toMG'.ends (.inr a) = (g.molRep (.inr b), .inl a) := by
          change (match g.anchor (.inl a) with
            | some b => (g.molRep (.inr b), (.inl a : Atom 3 n'))
            | none => ((.inl a : Atom 3 n'), (.inl a : Atom 3 n'))) = _
          rw [hA]
        have hfa : g.flatAtom (.inl a) = .inr b := by
          unfold Graph.flatAtom
          rw [hA]
        have hv1 : (𝕀).IsVtx (τ (g.molRep (g.flatAtom (.inl a)))) :=
          Or.inl (hτ _ (MolMono_molRep_isVtx g _))
        have hv2 : (𝕀).IsVtx (τ (.inl a)) := Or.inl (hτ _ (MolMono_molRep_isVtx g (.inl a)))
        have hμ2 : μ (τ (.inl a)) = (𝔾t).molRep (glueAtom x y₁ y₂ (.inl a)) := by
          rw [hτdef]
          dsimp only
          rw [ite_eq_right (MolMono_inl_not_mem_int g a)]
          exact Mext a
        have heq : π (τ (g.molRep (g.flatAtom (.inl a)))) = π (τ (.inl a)) :=
          (hPV _ _ hv1 hv2).2 (by rw [M3, hμ2])
        rw [hfa] at heq
        rw [hLe]
        exact ite_eq_left heq
  -- the vertices of the image
  have hSvtx : ∀ p, p ∈ (↑S.int ∪ ↑S.ext : Set _) → (𝕀).IsVtx p ∧ π p = p := by
    intro p hp
    rcases hp with hp | hp
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
      exact ⟨Or.inl (hπint z hz).1, hidem z⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
      have hzi : z ∉ (𝕀).int := fun h => Finset.disjoint_left.1 hdisj h hz
      rw [hπout z hzi]
      exact ⟨Or.inr hz, hπout z hzi⟩
  have hρR : ∀ z ∈ (𝕀).int, ∃ t, ρ z = .inr t := by
    intro z hz
    have hr : (ρ z).isRight = true := by
      rcases (hGint z).1 hz with ⟨v, hv, rfl⟩ | ⟨w, hw, rfl⟩
      · rw [hρl]
        exact SubstMol_lift_isRight n' hx (SubstMol_int_isRight hv)
      · rw [hρr]
        exact SubstMol_glueAtom_isRight hx hy₁ hy₂ w
    rcases h : ρ z with a | t
    · rw [h] at hr
      simp at hr
    · exact ⟨t, rfl⟩
  refine ⟨π, hidem, fun v hv => (hπint v hv).1,
    fun v hv => hπout v (fun h => Finset.disjoint_left.1 hdisj h hv),
    fun v hv h => Finset.disjoint_left.1 hdisj (hπint v hv).1 h, hdisj, fun e _ => hR2 e,
    fun z hz z' hz' => by rw [hπeq z hz z' hz', ← SubstMol_molRep_eq_iff], μ, Ge, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro e₁ e₂ h₁ h₂ he
    rcases hpres e₁ h₁ with ⟨i₁, hi₁, rfl⟩ | ⟨j₁, rfl⟩ <;>
      rcases hpres e₂ h₂ with ⟨i₂, hi₂, rfl⟩ | ⟨j₂, rfl⟩
    · rw [(CLS1 i₁ hi₁).1, (CLS1 i₂ hi₂).1] at he
      simp only [Sum.inl.injEq, Fin.mk.injEq] at he
      rw [Fin.ext he]
    · rw [(CLS1 i₁ hi₁).1, (CLS2 j₂).1] at he
      simp only [Sum.inl.injEq, Fin.mk.injEq] at he
      omega
    · rw [(CLS2 j₁).1, (CLS1 i₂ hi₂).1] at he
      simp only [Sum.inl.injEq, Fin.mk.injEq] at he
      omega
    · rw [(CLS2 j₁).1, (CLS2 j₂).1] at he
      simp only [Sum.inl.injEq, Fin.mk.injEq, Nat.add_left_cancel_iff] at he
      rw [Fin.ext he]
  · intro p hp q hq hpq
    obtain ⟨hpv, hpp⟩ := hSvtx p hp
    obtain ⟨hqv, hqq⟩ := hSvtx q hq
    rw [← hpp, ← hqq]
    exact (hPV p q hpv hqv).2 hpq
  · ext M
    rw [MolMono_mem_int, Finset.mem_image]
    constructor
    · rintro ⟨t, rfl⟩
      by_cases ht : t.val < m
      · refine ⟨π (.inl ((𝔾).molRep (.inr ⟨t.val, by omega⟩))),
          Finset.mem_image_of_mem _ (Finset.inl_mem_disjSum.2 (MolMono_molRep_mem_int _ _)), ?_⟩
        rw [(hπint _ (Finset.inl_mem_disjSum.2 (MolMono_molRep_mem_int _ _))).2, hμl, M1]
        simp only [SubstMol_lift, Sum.elim_inr, ht, dite_true]
      · obtain ⟨j, hj⟩ : ∃ j, t.val = m + j := ⟨t.val - m, by omega⟩
        have hjn : j < n' := by have := t.2; omega
        refine ⟨π (.inr (g.molRep (.inr ⟨j, hjn⟩))),
          Finset.mem_image_of_mem _ (Finset.inr_mem_disjSum.2 (MolMono_molRep_mem_int _ _)), ?_⟩
        rw [(hπint _ (Finset.inr_mem_disjSum.2 (MolMono_molRep_mem_int _ _))).2, hμr, hrepg]
        change (𝔾t).molRep (.inr (Fin.natAdd m ⟨j, hjn⟩)) = _
        rw [show (Fin.natAdd m ⟨j, hjn⟩ : Fin (m + n')) = t from Fin.ext hj.symm]
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨t, ht⟩ := hρR z hz
      exact ⟨t, by rw [(hπint z hz).2, hμ]; dsimp only; rw [ht]⟩
  · ext M
    rw [MolMono_mem_ext, Finset.mem_image]
    constructor
    · rintro ⟨a, rfl⟩
      have hz : (.inl (.inl a) : Atom 3 (m + 1) ⊕ Atom 3 n') ∈ (𝕀).ext := (hGext _).2 ⟨a, rfl⟩
      have hzi : (.inl (.inl a) : Atom 3 (m + 1) ⊕ Atom 3 n') ∉ (𝕀).int :=
        fun h => Finset.disjoint_left.1 hdisj h hz
      refine ⟨.inl (.inl a), Finset.mem_image.2 ⟨_, hz, hπout _ hzi⟩, hμE a⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨a, rfl⟩ := (hGext z).1 hz
      have hzi : (.inl (.inl a) : Atom 3 (m + 1) ⊕ Atom 3 n') ∉ (𝕀).int :=
        fun h => Finset.disjoint_left.1 hdisj h hz
      exact ⟨a, by rw [hπout _ hzi, hμE]⟩
  · intro e _
    have hS : ∀ z, (𝕀).IsVtx z → S.IsVtx (π z) := by
      intro z hz
      rcases hz with hz | hz
      · exact Or.inl (Finset.mem_image_of_mem _ hz)
      · exact Or.inr (Finset.mem_image_of_mem _ hz)
    rw [hSends]
    exact ⟨hS _ (hR2 e).1, hS _ (hR2 e).2⟩
  · intro e he
    rcases hpres e he with ⟨i, hi, rfl⟩ | ⟨j, rfl⟩
    · exact (CLS1 i hi).2.1
    · exact (CLS2 j).2.1
  · intro e he
    left
    rcases hpres e he with ⟨i, hi, rfl⟩ | ⟨j, rfl⟩
    · exact (CLS1 i hi).2.2 he
    · exact (CLS2 j).2.2 he
  · intro e' he'
    rcases e' with p | a
    · by_cases hp : p.val < H.comps.length
      · have h1 := CLS1 ⟨p.val, by omega⟩ hp
        have hGe : Ge (.inl (.inl ⟨p.val, by omega⟩)) = .inl p := h1.1.trans rfl
        by_contra hc
        refine he' _ ?_ hGe
        rw [← h1.2.1, hGe]
        exact hc
      · have hj : p.val - H.comps.length < g.comps.length := by have := p.2; omega
        have h1 := CLS2 ⟨p.val - H.comps.length, hj⟩
        have hGe : Ge (.inr (.inl ⟨p.val - H.comps.length, hj⟩)) = .inl p :=
          h1.1.trans (congrArg Sum.inl (Fin.ext (by simp only; omega)))
        by_contra hc
        refine he' _ ?_ hGe
        rw [← h1.2.1, hGe]
        exact hc
    · exact SubstMol_cls_inr hdGt a

end GlueMain

/-- **The molecular graph of a substituted graph** ([II, §4.3], picture (6.5) of
[II, Lemma 6.5 (2)], [II, Def 2.11] in the block reading). Let `G` be `H` times the `t`-variable
`t_{y₁y₂,x}` at internal atoms `x`, `y₁`, `y₂`, without dotted edges, and let `g` be any graph
with external atoms `⊗`, `⊕`, `⊖`. Insert the molecular graph of `g` into that of `G`
(`MGraph.insert`), sending `⊗`, `⊕`, `⊖` to the molecules `σ ⊗`, `σ ⊕`, `σ ⊖` of `x`, `y₁`, `y₂`
and removing the edges `G_{y₁α}` and `Ḡ_{y₂α}` of the `t`-variable (the set `B`); read the
vertices in `H` times `g` by `ρ` (the atom `α` goes to `x`, the atoms of `g` to their glued
atoms). Then some map `π` of the vertices
* is idempotent, sends internal vertices to internal vertices, fixes the external ones and sends
  no internal vertex to an external one;
* identifies two internal vertices exactly when their readings lie in one molecule of `H` times
  `g`;

the internal and the external vertices of the inserted graph are distinct, its present edges join
vertices, and the inserted graph with its vertices mapped by `π` and its loops removed is the
molecular graph of `H` times `g` up to the names of the vertices and of the present edges. -/
theorem toMG'_glue :
  ∀ (m n' : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n'),
    (H.glue x y₁ y₂ (tVar true)).DotFree → x.isRight = true → y₁.isRight = true →
    y₂.isRight = true →
    let G := H.glue x y₁ y₂ (tVar true)
    let σ : Atom 3 n' → Atom 3 (m + 1) :=
      Sum.elim (fun i => G.molRep (liftA 1 (![x, y₁, y₂] i))) (fun _ => G.molRep (liftA 1 x))
    let B : Finset (Fin G.comps.length ⊕ Fin 3) :=
      {.inl ⟨H.comps.length + 1, by simp [G, Graph.glue, liftCs, tVar, tVarGraph, Graph.swapEnds]⟩,
        .inl ⟨H.comps.length + 2, by simp [G, Graph.glue, liftCs, tVar, tVarGraph, Graph.swapEnds]⟩}
    let Glue := G.toMG'.insert g.toMG' σ B
    let ρ : Atom 3 (m + 1) ⊕ Atom 3 n' → Atom 3 (m + n') :=
      Sum.elim (Sum.elim (fun a => .inl a)
        (fun i => if h : i.val < m then .inr ⟨i.val, by omega⟩ else liftA n' x))
        (glueAtom x y₁ y₂)
    ∃ π : Atom 3 (m + 1) ⊕ Atom 3 n' → Atom 3 (m + 1) ⊕ Atom 3 n',
      (∀ v, π (π v) = π v) ∧ (∀ v ∈ Glue.int, π v ∈ Glue.int) ∧ (∀ v ∈ Glue.ext, π v = v) ∧
      (∀ v ∈ Glue.int, π v ∉ Glue.ext) ∧ Disjoint Glue.int Glue.ext ∧
      (∀ e, Glue.cls e ≠ none → Glue.IsVtx (Glue.ends e).1 ∧ Glue.IsVtx (Glue.ends e).2) ∧
      (∀ z ∈ Glue.int, ∀ z' ∈ Glue.int,
        (π z = π z' ↔ (H.glue x y₁ y₂ g).SameMol (ρ z) (ρ z'))) ∧
      ((Glue.mapV π).unloop).Transported (H.glue x y₁ y₂ g).toMG' := by
  intro m n' H x y₁ y₂ g hD hx hy₁ hy₂ G σ B Glue ρ
  refine SubstMol_glue_core H x y₁ y₂ g hD hx hy₁ hy₂ σ (fun _ => rfl) B (fun i => ?_) ρ
    (fun _ => rfl) (fun _ => rfl)
  simp only [B, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq, Fin.ext_iff]

end RBM8D.Graphs
