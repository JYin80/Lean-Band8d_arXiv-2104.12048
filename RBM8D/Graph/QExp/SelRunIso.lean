import RBM8D.Graph.QExp.SelRun
import RBM8D.Graph.MolDot

/-!
# Weak isolation of the output graphs of the family of `Q`-expansions

The second part of the clause (F6) of `QExpFamilyStmt` for the family `selRunFam` of
[II, Lemma 4.15], from [II, Lemma 6.5 (4)], [II, Def 6.1] and [II, Lemma 4.15 (iv)], and the
existence of a family with all the clauses of `QExpFamilyStmt`:
* `Graph.splitUnpinned_add_two`: the split term `1_{u = x}` at an end `u = ⊕` or `⊖` of an edge
  of `Γ₀` that is not identified with an internal atom raises `MGraph.cHat` (at `⊕`) or the red
  crossing count (at `⊖`) of every set of molecules containing that of `x` and not that of the
  other end by `2`;
* `selStep1_witnessRun`: an output of the run `selStep1` that is not a `Q`-graph is reached
  through a step of the witness `SelRunWit` of [II, Lemma 4.11] at a graph with the dotted blocks
  of the input;
* `selRunFam_weakIso`: the weak-isolation part of (F6);
* `selRunFam_qExpFamilyStmt`, `exists_qExpFamilyStmt`: the clauses (F1)–(F6) for `selRunFam`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Adding an edge at a vertex without neighbours -/

section AddEdge

variable {V : Type*}

/-- A vertex without neighbours reaches only itself. -/
private theorem SelRunIso_reach_isolated {G : SimpleGraph V} {p : V} (hp : ∀ v, ¬ G.Adj p v)
    {v : V} (h : G.Reachable p v) : v = p := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  rcases Relation.ReflTransGen.cases_head h with h | ⟨w, hw, -⟩
  · exact h.symm
  · exact absurd hw (hp w)

/-- Reachability after adding the edge `p q` at a vertex `p` without neighbours. -/
private theorem SelRunIso_reach_add {G G' : SimpleGraph V} {p q : V} (hpq : p ≠ q)
    (hp : ∀ v, ¬ G.Adj p v)
    (hadj : ∀ u v, G'.Adj u v ↔ G.Adj u v ∨ (u = p ∧ v = q) ∨ (u = q ∧ v = p)) (u v : V) :
    G'.Reachable u v ↔
      G.Reachable u v ∨ (u = p ∧ G.Reachable q v) ∨ (G.Reachable u q ∧ v = p) := by
  have hle : G ≤ G' := fun a b h => (hadj a b).2 (Or.inl h)
  have hpq' : G'.Adj p q := (hadj p q).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inl (SimpleGraph.Reachable.refl _)
    | @tail w v' _ hwv ih =>
      rcases (hadj w v').1 hwv with ha | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h.trans ha.reachable)
        · exact Or.inr (Or.inl ⟨h1, h2.trans ha.reachable⟩)
        · rw [h2] at ha; exact absurd ha (hp _)
      · subst h1 h2
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact Or.inr (Or.inl ⟨SelRunIso_reach_isolated hp h.symm, SimpleGraph.Reachable.refl _⟩)
        · exact Or.inr (Or.inl ⟨h1, SimpleGraph.Reachable.refl _⟩)
        · exact Or.inl h1
      · subst h1 h2
        rcases ih with h | ⟨h1, h2⟩ | ⟨-, h2⟩
        · exact Or.inr (Or.inr ⟨h, rfl⟩)
        · rw [h1]; exact Or.inl (SimpleGraph.Reachable.refl _)
        · exact absurd h2.symm hpq
  · rintro (h | ⟨rfl, h⟩ | ⟨h, rfl⟩)
    · exact h.mono hle
    · exact hpq'.reachable.trans (h.mono hle)
    · exact (h.mono hle).trans hpq'.symm.reachable

/-- Two distinct members of a list give length at least `2`. -/
private theorem SelRunIso_two_le_length {α : Type*} {l : List α} {a b : α} (ha : a ∈ l)
    (hb : b ∈ l) (hab : a ≠ b) : 2 ≤ l.length := by
  rcases l with _ | ⟨z, _ | ⟨w, l⟩⟩
  · cases ha
  · simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · simp

end AddEdge

/-! ## Blocks, molecules and the block normal form -/

section Congr

variable {k n : ℕ}

/-- Graphs with the same blocks have the same anchors. -/
theorem SelRunIso_anchor_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v) (u : Atom k n) :
    Γ₁.anchor u = Γ₂.anchor u := by
  classical
  rw [MolMono_anchor_eq_find, MolMono_anchor_eq_find]
  congr 1
  funext b
  exact decide_eq_decide.2 (hB _ _)

/-- Graphs with the same blocks have the same block normal form of the atoms. -/
theorem SelRunIso_flatAtom_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v) (u : Atom k n) :
    Γ₁.flatAtom u = Γ₂.flatAtom u := by
  rcases u with a | a
  · simp only [Graph.flatAtom, SelRunIso_anchor_congr hB]
  · rfl

/-- Graphs with the same molecules have the same representatives of the molecules. -/
theorem SelRunIso_molRep_congr {Γ₁ Γ₂ : Graph k n}
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) (u : Atom k n) :
    Γ₁.molRep u = Γ₂.molRep u := by
  classical
  rcases u with a | a
  · rfl
  · rw [MolMono_molRep_eq_find, MolMono_molRep_eq_find]
    congr 3
    funext b
    exact decide_eq_decide.2 (hM _ _)

/-- Atoms of one block are joined by a path of waved and dotted edges. -/
theorem SelRunIso_mol_of_block (Γ : Graph k n) {u v : Atom k n} (h : Γ.SameBlock u v) :
    Γ.molGraph.Reachable u v := by
  rw [Graph.SameBlock, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hab ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
    rw [Graph.molGraph, SimpleGraph.fromRel_adj]
    refine ⟨hab.1, ?_⟩
    rcases hab.2 with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
    · exact Or.inl ⟨c, hc, by rw [hk]; rfl, h1, h2⟩
    · exact Or.inr ⟨c, hc, by rw [hk]; rfl, h1, h2⟩

/-- Two internal atoms of one block have the same representative of their molecule. -/
theorem SelRunIso_molRep_of_block (Γ : Graph k n) {a b : Fin n}
    (h : Γ.SameBlock (.inr a) (.inr b)) : Γ.molRep (.inr a) = Γ.molRep (.inr b) :=
  (MolMono_molRep_eq_iff Γ a b).2 (Or.inr ⟨rfl, rfl, SelRunIso_mol_of_block Γ h⟩)

/-- The block normal form of an atom is the atom itself or an internal atom of its block. -/
theorem SelRunIso_flatAtom_spec (Γ : Graph k n) (u : Atom k n) :
    Γ.flatAtom u = u ∨ ∃ b : Fin n, Γ.flatAtom u = .inr b ∧ Γ.SameBlock u (.inr b) := by
  classical
  rcases u with a | a
  · simp only [Graph.flatAtom]
    rcases h : Γ.anchor (.inl a) with _ | b
    · exact Or.inl rfl
    · right
      refine ⟨b, rfl, ?_⟩
      rw [MolMono_anchor_eq_find] at h
      simpa using List.find?_some h
  · exact Or.inl rfl

/-- The representative of the molecule of the block normal form of an atom is internal exactly
when the atom is internal or in a block with an internal atom. -/
theorem SelRunIso_flatAtom_inl (Γ : Graph k n) {u : Atom k n} {a : Fin k}
    (h : Γ.flatAtom u = .inl a) : u = .inl a ∧ Γ.Unpinned u := by
  classical
  rcases u with a' | a'
  · simp only [Graph.flatAtom] at h
    rcases hb : Γ.anchor (.inl a') with _ | b
    · rw [hb] at h
      cases h
      refine ⟨rfl, rfl, fun b' hb' => ?_⟩
      rw [MolMono_anchor_eq_find, List.find?_eq_none] at hb
      exact hb b' (List.mem_finRange b') (by simpa using hb')
    · rw [hb] at h; cases h
  · cases h

/-- The representative of the molecule of an atom that is external is the atom. -/
theorem SelRunIso_molRep_eq_inl (Γ : Graph k n) {w : Atom k n} {a : Fin k}
    (h : Γ.molRep w = .inl a) : w = .inl a := by
  rcases w with b | b
  · exact h
  · obtain ⟨c, hc, -⟩ := MolMono_molRep_inr Γ b
    rw [hc] at h; cases h

end Congr

/-! ## Counts over lists of present edges -/

section ListCounts

variable {V : Type} [DecidableEq V] (I X S : Finset V)

private theorem SelRunIso_cHatL_perm {L L' : List (V × V × MClass)} (h : L.Perm L') :
    MolMono_cHatL I X S L = MolMono_cHatL I X S L' := by
  have ht : MolMono_tExtL I X S L = MolMono_tExtL I X S L' := by
    ext a
    simp only [MolMono_mem_tExtL, h.mem_iff]
  unfold MolMono_cHatL MolMono_cIntL
  rw [h.countP_eq, ht]

private theorem SelRunIso_redL_perm {L L' : List (V × V × MClass)} (h : L.Perm L') :
    MolMono_redL I X S L = MolMono_redL I X S L' := by
  unfold MolMono_redL
  rw [h.countP_eq]

/-- A present edge that does not cross `S` does not change `MolMono_cHatL`. -/
private theorem SelRunIso_cHatL_cons_no {t : V × V × MClass} (ht : ¬ MolMono_crossT I X S t)
    (L : List (V × V × MClass)) : MolMono_cHatL I X S (t :: L) = MolMono_cHatL I X S L := by
  have h1 : MolMono_tExtL I X S (t :: L) = MolMono_tExtL I X S L := by
    ext a
    simp only [MolMono_mem_tExtL, List.mem_cons]
    constructor
    · rintro ⟨ha, t', rfl | ht', hc, he⟩
      · exact absurd hc ht
      · exact ⟨ha, t', ht', hc, he⟩
    · rintro ⟨ha, t', ht', hc, he⟩
      exact ⟨ha, t', Or.inr ht', hc, he⟩
  unfold MolMono_cHatL MolMono_cIntL
  rw [h1, List.countP_cons]
  have : ¬ MolMono_intT I X S t := fun h => ht h.1
  simp [this]

/-- A crossing present edge between two internal vertices, followed by a crossing present edge
from an internal vertex to an external vertex `a` reached by no other edge, raise
`MolMono_cHatL` by `2`. -/
private theorem SelRunIso_cHatL_two {t₁ t₂ : V × V × MClass} (h₁ : MolMono_intT I X S t₁)
    (h₂ : MolMono_crossT I X S t₂) (h₂i : t₂.1 ∈ I) {a : V} (ha : t₂.2.1 = a) (haX : a ∈ X)
    (haI : a ∉ I) (L : List (V × V × MClass)) (hL : ∀ t ∈ L, t.1 ≠ a ∧ t.2.1 ≠ a) :
    MolMono_cHatL I X S (t₁ :: t₂ :: L) = MolMono_cHatL I X S L + 2 := by
  have hext : MolMono_tExtL I X S (t₁ :: t₂ :: L) = insert a (MolMono_tExtL I X S L) := by
    ext v
    simp only [MolMono_mem_tExtL, List.mem_cons, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hvX, hvI⟩, t, rfl | rfl | ht, hc, he⟩
      · exfalso
        rcases he with rfl | rfl
        · exact hvI h₁.2.1
        · exact hvI h₁.2.2
      · rcases he with rfl | rfl
        · exact absurd h₂i hvI
        · exact Or.inl ha
      · exact Or.inr ⟨⟨hvX, hvI⟩, t, ht, hc, he⟩
    · rintro (rfl | ⟨hv, t, ht, hc, he⟩)
      · exact ⟨⟨haX, haI⟩, t₂, Or.inr (Or.inl rfl), h₂, Or.inr ha⟩
      · exact ⟨hv, t, Or.inr (Or.inr ht), hc, he⟩
  have hnot : a ∉ MolMono_tExtL I X S L := by
    rw [MolMono_mem_tExtL]
    rintro ⟨-, t, ht, -, he⟩
    rcases he with he | he
    · exact (hL t ht).1 he
    · exact (hL t ht).2 he
  have hn2 : ¬ MolMono_intT I X S t₂ := fun h => haI (ha ▸ h.2.2)
  unfold MolMono_cHatL MolMono_cIntL
  rw [hext, Finset.card_insert_of_notMem hnot, List.countP_cons, List.countP_cons]
  simp [h₁, hn2]
  omega

/-- Two red crossing present edges raise `MolMono_redL` by `2`. -/
private theorem SelRunIso_redL_two {t₀ t₁ t₂ : V × V × MClass} (h₀ : ¬ MolMono_redT I X S t₀)
    (h₁ : MolMono_redT I X S t₁) (h₂ : MolMono_redT I X S t₂) (L : List (V × V × MClass)) :
    MolMono_redL I X S (t₁ :: t₂ :: L) = MolMono_redL I X S (t₀ :: L) + 2 := by
  unfold MolMono_redL
  rw [List.countP_cons, List.countP_cons, List.countP_cons]
  simp [h₀, h₁, h₂]

end ListCounts

/-- The filter map of a list without repetition, with one entry `a₀` changed from `none` to
`some z`. -/
private theorem SelRunIso_filterMap_one {α β : Type*} :
    ∀ (l : List α) (f g : α → Option β) (a₀ : α) (z : β), l.Nodup → a₀ ∈ l → f a₀ = none →
      g a₀ = some z → (∀ a ∈ l, a ≠ a₀ → g a = f a) → (l.filterMap g).Perm (z :: l.filterMap f)
  | [], _, _, _, _, _, h, _, _, _ => by cases h
  | a :: l, f, g, a₀, z, hnd, hmem, hf, hg, hfg => by
    classical
    rw [List.nodup_cons] at hnd
    by_cases ha : a = a₀
    · subst ha
      have hl : l.filterMap g = l.filterMap f := List.filterMap_congr fun b hb =>
        hfg b (List.mem_cons_of_mem _ hb) fun h => hnd.1 (h ▸ hb)
      rw [List.filterMap_cons_some hg, List.filterMap_cons_none hf, hl]
    · have hm : a₀ ∈ l := (List.mem_cons.1 hmem).resolve_left (Ne.symm ha)
      have ih := SelRunIso_filterMap_one l f g a₀ z hnd.2 hm hf hg
        fun b hb => hfg b (List.mem_cons_of_mem _ hb)
      have he : g a = f a := hfg a (List.mem_cons_self ..) ha
      rw [List.filterMap_cons, List.filterMap_cons, he]
      rcases f a with _ | w
      · exact ih
      · exact (ih.cons w).trans (List.Perm.swap _ _ _)

/-! ## The split term at an unpinned external atom -/

section SplitUnpinned

variable {n : ℕ}

/-- The graph `T` with the dotted edge `p = X`. -/
private abbrev SelRunIso_addDot (T : Graph 3 n) (p X : Atom 3 n) : Graph 3 n :=
  ⟨T.comps ++ [mkC .dot p X], T.coeff⟩

private theorem SelRunIso_dot_adj (T : Graph 3 n) {p X : Atom 3 n} (hpX : p ≠ X) (u v : Atom 3 n) :
    (SelRunIso_addDot T p X).dotGraph.Adj u v ↔
      T.dotGraph.Adj u v ∨ (u = p ∧ v = X) ∨ (u = X ∧ v = p) := by
  rw [Graph.dotGraph, Graph.dotGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  have hmem : ∀ c, c ∈ (SelRunIso_addDot T p X).comps ↔ c ∈ T.comps ∨ c = mkC .dot p X := by
    intro c
    simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hne, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩
    · rcases (hmem c).1 hc with hc | rfl
      · exact Or.inl ⟨hne, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases (hmem c).1 hc with hc | rfl
      · exact Or.inl ⟨hne, Or.inr ⟨c, hc, hk, rfl, rfl⟩⟩
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rintro (⟨hne, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hne, Or.inl ⟨c, (hmem c).2 (Or.inl hc), hk, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inr ⟨c, (hmem c).2 (Or.inl hc), hk, rfl, rfl⟩⟩
    · exact ⟨hpX, Or.inl ⟨_, (hmem _).2 (Or.inr rfl), rfl, rfl, rfl⟩⟩
    · exact ⟨hpX.symm, Or.inr ⟨_, (hmem _).2 (Or.inr rfl), rfl, rfl, rfl⟩⟩

private theorem SelRunIso_mol_adj (T : Graph 3 n) {p X : Atom 3 n} (hpX : p ≠ X) (u v : Atom 3 n) :
    (SelRunIso_addDot T p X).molGraph.Adj u v ↔
      T.molGraph.Adj u v ∨ (u = p ∧ v = X) ∨ (u = X ∧ v = p) := by
  rw [Graph.molGraph, Graph.molGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  have hmem : ∀ c, c ∈ (SelRunIso_addDot T p X).comps ↔ c ∈ T.comps ∨ c = mkC .dot p X := by
    intro c
    simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hne, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩
    · rcases (hmem c).1 hc with hc | rfl
      · exact Or.inl ⟨hne, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases (hmem c).1 hc with hc | rfl
      · exact Or.inl ⟨hne, Or.inr ⟨c, hc, hk, rfl, rfl⟩⟩
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rintro (⟨hne, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hne, Or.inl ⟨c, (hmem c).2 (Or.inl hc), hk, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inr ⟨c, (hmem c).2 (Or.inl hc), hk, rfl, rfl⟩⟩
    · exact ⟨hpX, Or.inl ⟨_, (hmem _).2 (Or.inr rfl), rfl, rfl, rfl⟩⟩
    · exact ⟨hpX.symm, Or.inr ⟨_, (hmem _).2 (Or.inr rfl), rfl, rfl, rfl⟩⟩

/-- The facts on an unpinned external atom `p` carrying a random component `c`, under the clause on
the external atoms: no dotted edge and no waved edge leaves `p`, and no component other than `c`,
dotted and `×`-dotted edges is at `p`. -/
private theorem SelRunIso_unpinned_facts {T : Graph 3 n} (hE : T.ExtClause) {c : Comp (Atom 3 n)}
    (hc : c ∈ T.comps) (hr : c.kind.isRandom = true) {b : Fin 3} (hb : b = 1 ∨ b = 2)
    (hy : c.y = .inl b) (hU : T.Unpinned c.y) :
    (∀ v, ¬ T.dotGraph.Adj c.y v) ∧ (∀ v, ¬ T.molGraph.Adj c.y v) ∧
      (∀ d ∈ T.comps, (d.x = c.y ∨ d.y = c.y) → d.kind ≠ .dot → d.kind ≠ .xdot → d = c) ∧
      (∀ v, T.SameBlock c.y v → v = c.y) := by
  have hdeg : T.nonDotDeg c.y ≤ 1 := by
    rcases hb with rfl | rfl
    · rw [hy] at hU ⊢; exact (hE.2.2.2.2 hU).2.2
    · rw [hy] at hU ⊢; exact (hE.2.2.2.1 hU).2
  have hcd : c.kind ≠ .dot := fun h => by rw [h] at hr; cases hr
  have hcx : c.kind ≠ .xdot := fun h => by rw [h] at hr; cases hr
  have hblk : ∀ v, T.SameBlock c.y v → v = c.y := by
    intro v hv
    by_contra hne
    obtain ⟨b', hb'⟩ := hE.1 c.y v (Ne.symm hne) hv
    exact hU.2 b' hb'
  have honly : ∀ d ∈ T.comps, (d.x = c.y ∨ d.y = c.y) → d.kind ≠ .dot → d.kind ≠ .xdot →
      d = c := by
    intro d hd hat hdd hdx
    by_contra hne
    have hmemF : ∀ e ∈ T.comps, (e.x = c.y ∨ e.y = c.y) → e.kind ≠ .dot → e.kind ≠ .xdot →
        e ∈ T.comps.filter (fun e => decide ((e.x = c.y ∨ e.y = c.y) ∧ e.kind ≠ .dot ∧
          e.kind ≠ .xdot)) :=
      fun e he h1 h2 h3 => List.mem_filter.2 ⟨he, decide_eq_true ⟨h1, h2, h3⟩⟩
    have h2 := SelRunIso_two_le_length (hmemF d hd hat hdd hdx) (hmemF c hc (Or.inr rfl) hcd hcx)
      hne
    unfold Graph.nonDotDeg at hdeg
    omega
  refine ⟨fun v hv => ?_, fun v hv => ?_, honly, hblk⟩
  · exact (hv.ne (hblk v hv.reachable).symm).elim
  · have hne := hv.ne
    rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hv
    rcases hv.2 with ⟨d, hd, hj, h1, h2⟩ | ⟨d, hd, hj, h1, h2⟩
    · by_cases hdd : d.kind = .dot
      · refine hne (hblk v ?_).symm
        rw [← h1, ← h2]
        by_cases hxy : d.x = d.y
        · rw [hxy]; exact SimpleGraph.Reachable.refl _
        · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hxy, Or.inl ⟨d, hd, hdd, rfl, rfl⟩⟩).reachable
      · have hdx : d.kind ≠ .xdot := fun h => by rw [h] at hj; cases hj
        have := honly d hd (Or.inl h1) hdd hdx
        rw [this] at hj
        revert hj hr
        cases c.kind <;> simp [Kind.joinsMol, Kind.isRandom]
    · by_cases hdd : d.kind = .dot
      · refine hne (hblk v ?_).symm
        rw [← h1, ← h2]
        by_cases hxy : d.x = d.y
        · rw [hxy]; exact SimpleGraph.Reachable.refl _
        · exact ((SimpleGraph.fromRel_adj _ _ _).2
            ⟨hxy, Or.inl ⟨d, hd, hdd, rfl, rfl⟩⟩).reachable.symm
      · have hdx : d.kind ≠ .xdot := fun h => by rw [h] at hj; cases hj
        have := honly d hd (Or.inr h2) hdd hdx
        rw [this] at hj
        revert hj hr
        cases c.kind <;> simp [Kind.joinsMol, Kind.isRandom]

/-- The edge of `Graph.toMG'` given by a component, when present: not a dotted edge, its class,
and the molecules of the ends in the block normal form. -/
private theorem SelRunIso_edgeD_some {k : ℕ} (Γ : Graph k n) {d : Comp (Atom k n)}
    {t : Atom k n × Atom k n × MClass} (h : MolMono_edgeD Γ d = some t) :
    d.kind ≠ .dot ∧ d.kind.mclass = some t.2.2 ∧ t.1 = Γ.molRep (Γ.flatAtom d.x) ∧
      t.2.1 = Γ.molRep (Γ.flatAtom d.y) := by
  unfold MolMono_edgeD at h
  split_ifs at h with h1
  · simp only [not_or] at h1
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨h1.1, hm, rfl, rfl⟩

/-- Blocks, molecules and the block normal form after the dotted edge `c.y = X` at an unpinned
external atom `c.y` carrying the random component `c`: the molecules are unchanged, the atoms
other than `c.y` keep their block normal form, and `c.y` is moved to an internal atom of the
block of `X`. -/
private theorem SelRunIso_split_struct {T : Graph 3 n} (hE : T.ExtClause) {X : Atom 3 n}
    (hX : X.isRight = true) {c : Comp (Atom 3 n)} (hc : c ∈ T.comps)
    (hr : c.kind.isRandom = true) {b : Fin 3} (hb : b = 1 ∨ b = 2) (hy : c.y = .inl b)
    (hU : T.Unpinned c.y) :
    (∀ u, (SelRunIso_addDot T c.y X).molRep u = T.molRep u) ∧
      (∀ u, u ≠ c.y → (SelRunIso_addDot T c.y X).anchor u = T.anchor u) ∧
      (∃ b₀ : Fin n, (SelRunIso_addDot T c.y X).anchor c.y = some b₀ ∧
        T.molRep (.inr b₀) = T.molRep X) := by
  classical
  obtain ⟨hdot, hmol, -, hblk⟩ := SelRunIso_unpinned_facts hE hc hr hb hy hU
  have hpX : c.y ≠ X := by
    rw [hy]; intro h; rw [← h] at hX; cases hX
  have hB := SelRunIso_reach_add hpX hdot (SelRunIso_dot_adj T hpX)
  have hM := SelRunIso_reach_add hpX hmol (SelRunIso_mol_adj T hpX)
  have hpR : ∀ u : Atom 3 n, u.isRight = true → u ≠ c.y := by
    intro u hu h; rw [h, hy] at hu; cases hu
  refine ⟨fun u => SelRunIso_molRep_congr (fun u v => ?_) u, fun u hu => ?_, ?_⟩
  · unfold Graph.SameMol
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · rcases (hM u v).1 h3 with h | ⟨h4, -⟩ | ⟨-, h4⟩
        · exact Or.inr ⟨h1, h2, h⟩
        · exact absurd h4 (hpR u h1)
        · exact absurd h4 (hpR v h2)
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, (hM u v).2 (Or.inl h3)⟩
  · rw [MolMono_anchor_eq_find, MolMono_anchor_eq_find]
    congr 1
    funext b'
    refine decide_eq_decide.2 ⟨fun h => ?_, fun h => (hB _ _).2 (Or.inl h)⟩
    rcases (hB _ _).1 h with h | ⟨h1, -⟩ | ⟨-, h1⟩
    · exact h
    · exact absurd h1 hu
    · exact absurd h1 (hpR _ rfl)
  · have hiff : ∀ b' : Fin n, (SelRunIso_addDot T c.y X).SameBlock c.y (.inr b') ↔
        T.SameBlock X (.inr b') := by
      intro b'
      constructor
      · intro h
        rcases (hB _ _).1 h with h | ⟨-, h⟩ | ⟨-, h⟩
        · exact absurd (hblk _ h) (hpR _ rfl)
        · exact h
        · exact absurd h (hpR _ rfl)
      · intro h
        exact (hB _ _).2 (Or.inr (Or.inl ⟨rfl, h⟩))
    obtain ⟨x, rfl⟩ : ∃ x, X = .inr x := by
      rcases X with a | a
      · cases hX
      · exact ⟨a, rfl⟩
    have hsome : ((List.finRange n).find? fun b' =>
        decide (T.SameBlock (.inr x) (.inr b'))).isSome := by
      rw [List.find?_isSome]
      exact ⟨x, List.mem_finRange x, decide_eq_true (SimpleGraph.Reachable.refl _)⟩
    obtain ⟨b₀, hb₀⟩ := Option.isSome_iff_exists.1 hsome
    have hb₀' : T.SameBlock (.inr x) (.inr b₀) := by simpa using List.find?_some hb₀
    refine ⟨b₀, ?_, (SelRunIso_molRep_of_block T hb₀').symm⟩
    rw [MolMono_anchor_eq_find, ← hb₀]
    congr 1
    funext b'
    exact decide_eq_decide.2 (hiff b')

/-- **The split term `1_{u = x}` at an unpinned `⊕` or `⊖`** (the step "an atom of `Γ₀`
identified with `x`" in the proof of [II, Lemma 6.5 (4)], with [II, Lemma 4.11], at an external
end of an edge of `Γ₀`). Let `c` be a random component without label of `T` whose second atom
`c.y = b` is `⊕` or `⊖` and is not identified with an internal atom, and let `T'` be `T` with the
dotted edge `c.y = X` at the internal atom `X`. For a set `S` of internal molecules of the block
normal form containing the molecule of `X` and not that of `c.x`: at `⊕` the count
`MGraph.cHat` of `S` rises by `2` (the edge `c` and the blue edge to `⊕`), and at `⊖` the red
crossing count of `S` rises by `2` (the edge `c` and the red edge to `⊖`). -/
theorem Graph.splitUnpinned_add_two (T : Graph 3 n) (hI : T.InvB') (X : Atom 3 n)
    (hX : X.isRight = true) (c : Comp (Atom 3 n)) (hc : c ∈ T.comps) (hl : c.label = none)
    (hr : c.kind.isRandom = true) (b : Fin 3) (hb : b = 1 ∨ b = 2) (hy : c.y = .inl b)
    (hU : T.Unpinned c.y) (S : Finset (Atom 3 n)) (hS : S ⊆ T.toMG'.int)
    (hXS : T.molRep X ∈ S) (hxS : T.molRep (T.flatAtom c.x) ∉ S) :
    (b = 1 → (⟨T.comps ++ [mkC .dot c.y X], T.coeff⟩ : Graph 3 n).toMG'.cHat S =
        T.toMG'.cHat S + 2) ∧
      (b = 2 → (⟨T.comps ++ [mkC .dot c.y X], T.coeff⟩ : Graph 3 n).toMG'.redCount S =
        T.toMG'.redCount S + 2) := by
  classical
  obtain ⟨hdot, hmol, honly, hblk⟩ := SelRunIso_unpinned_facts hI.2.2.1 hc hr hb hy hU
  obtain ⟨hmr, hanc, b₀, hb₀, hMX⟩ := SelRunIso_split_struct hI.2.2.1 hX hc hr hb hy hU
  have hcd : c.kind ≠ .dot := fun h => by rw [h] at hr; cases hr
  have hcx : c.kind ≠ .xdot := fun h => by rw [h] at hr; cases hr
  have hcol : (T.flatAtom c.x).isRight = true ∧ T.flatAtom c.y ≠ .inl 0 ∧
      (T.flatAtom c.y = .inl 1 → c.kind = .G .plus) ∧
      (T.flatAtom c.y = .inl 2 → c.kind = .G .minus) := by
    have h := (hI.2.1 (T.flatComp c) (List.mem_map_of_mem hc)).1
    simp only [Graph.flatComp, hcd, ite_false] at h
    exact h hr
  have hancy : T.anchor c.y = none := by
    rw [MolMono_anchor_eq_find, List.find?_eq_none]
    intro b' _ h
    exact hU.2 b' (by simpa using h)
  have hrest : c ∉ T.comps.erase c := by
    intro hmem
    have hdeg : T.nonDotDeg c.y ≤ 1 := by
      rcases hb with rfl | rfl
      · rw [hy] at hU ⊢; exact (hI.2.2.1.2.2.2.2 hU).2.2
      · rw [hy] at hU ⊢; exact (hI.2.2.1.2.2.2.1 hU).2
    have hp := (List.perm_cons_erase hc).filter
      (fun e => decide ((e.x = c.y ∨ e.y = c.y) ∧ e.kind ≠ .dot ∧ e.kind ≠ .xdot))
    have hcP : (c.x = c.y ∨ c.y = c.y) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot := ⟨Or.inr rfl, hcd, hcx⟩
    unfold Graph.nonDotDeg at hdeg
    rw [hp.length_eq, List.filter_cons, ite_eq_left (decide_eq_true hcP), List.length_cons] at hdeg
    have : 0 < ((T.comps.erase c).filter fun e => decide ((e.x = c.y ∨ e.y = c.y) ∧
        e.kind ≠ .dot ∧ e.kind ≠ .xdot)).length :=
      List.length_pos_of_mem (List.mem_filter.2 ⟨hmem, decide_eq_true hcP⟩)
    omega
  have hcmem : c ∈ T.comps := hc
  obtain ⟨κ, cx, cy, cm, cl⟩ := c
  simp only at hy hU hcol hancy hcd hcx honly hmr hanc hb₀ hxS hblk hdot hmol hrest hcmem ⊢
  subst hy
  set T' := SelRunIso_addDot T (.inl b) X with hT'
  have hfy : T.flatAtom (.inl b) = .inl b := by simp only [Graph.flatAtom, hancy]
  have hfy' : T'.flatAtom (.inl b) = .inr b₀ := by simp only [Graph.flatAtom, hb₀]
  rw [hfy] at hcol
  obtain ⟨hfx, -, hk1, hk2⟩ := hcol
  have hxy : cx ≠ .inl b := by
    intro h
    rw [h, hfy] at hfx
    cases hfx
  have hfx' : T'.flatAtom cx = T.flatAtom cx := by
    rcases cx with a | a
    · simp only [Graph.flatAtom, hanc (.inl a) hxy]
    · rfl
  -- the molecules
  set Mx := T.molRep (T.flatAtom cx) with hMxdef
  set MX := T.molRep X with hMXdef
  have hMxI : Mx ∈ T.toMG'.int := by
    rcases hw : T.flatAtom cx with a | a
    · rw [hw] at hfx; cases hfx
    · rw [hMxdef, hw]; exact MolMono_molRep_mem_int T a
  have hMXI : MX ∈ T.toMG'.int := hS hXS
  have hyI : (.inl b : Atom 3 n) ∉ T.toMG'.int := MolMono_inl_not_mem_int T b
  have hyX : (.inl b : Atom 3 n) ∈ T.toMG'.ext := (MolMono_mem_ext T _).2 ⟨b, rfl⟩
  have hyS : (.inl b : Atom 3 n) ∉ S := fun h => hyI (hS h)
  have hMxy : Mx ≠ .inl b := fun h => hyI (h ▸ hMxI)
  have hMxX : Mx ≠ MX := fun h => hxS (h ▸ hXS)
  have hint : T'.toMG'.int = T.toMG'.int := by
    simp only [Graph.toMG', hmr]
  have hext : T'.toMG'.ext = T.toMG'.ext := rfl
  -- the kind of `c`
  obtain ⟨m, hm, hm1, hm2⟩ : ∃ m, κ.mclass = some m ∧ (b = 1 → m = .plus) ∧
      (b = 2 → m = .minus) := by
    rcases hb with rfl | rfl
    · exact ⟨.plus, by rw [hk1 rfl]; rfl, fun _ => rfl, fun h => absurd h (by decide)⟩
    · exact ⟨.minus, by rw [hk2 rfl]; rfl, fun h => absurd h (by decide), fun _ => rfl⟩
  set c : Comp (Atom 3 n) := ⟨κ, cx, .inl b, cm, cl⟩ with hcdef
  -- the present edges of `c`
  have heT : MolMono_edgeD T c = some (Mx, .inl b, m) := by
    unfold MolMono_edgeD
    have hne : ¬ (c.kind = .dot ∨ T.molRep (T.flatAtom c.x) = T.molRep (T.flatAtom c.y)) := by
      rintro (h | h)
      · exact hcd h
      · exact hMxy (by rw [hMxdef]; simpa [hcdef, hfy, Graph.molRep] using h)
    rw [ite_eq_right hne]
    simp [hcdef, hm, hfy, Graph.molRep, hMxdef]
  have heT' : MolMono_edgeD T' c = some (Mx, MX, m) := by
    have h1 : T'.molRep (T'.flatAtom c.x) = Mx := by
      change T'.molRep (T'.flatAtom cx) = Mx
      rw [hfx', hmr]
    have h2 : T'.molRep (T'.flatAtom c.y) = MX := by
      change T'.molRep (T'.flatAtom (.inl b)) = MX
      rw [hfy', hmr, hMX]
    unfold MolMono_edgeD
    rw [h1, h2, ite_eq_right (by rintro (h | h); exacts [hcd h, hMxX h])]
    change Option.map _ κ.mclass = _
    rw [hm]
    rfl
  -- the other components
  have hfl : ∀ u, u ≠ .inl b → T'.flatAtom u = T.flatAtom u := by
    intro u hu
    rcases u with a | a
    · simp only [Graph.flatAtom, hanc (.inl a) hu]
    · rfl
  have hother : ∀ d ∈ T.comps, d ≠ c → MolMono_edgeD T' d = MolMono_edgeD T d := by
    intro d hd hdc
    by_cases hat : d.x = .inl b ∨ d.y = .inl b
    · by_cases hdd : d.kind = .dot
      · simp [MolMono_edgeD, hdd]
      · by_cases hdx : d.kind = .xdot
        · simp [MolMono_edgeD, hdx, Kind.mclass]
        · exact absurd (honly d hd hat hdd hdx) hdc
    · simp only [not_or] at hat
      simp only [MolMono_edgeD, hfl _ hat.1, hfl _ hat.2, hmr]
  have hnewD : MolMono_edgeD T' (mkC .dot (.inl b) X) = none := by
    simp [MolMono_edgeD, mkC]
  -- the pin edges
  have hpin : ((List.finRange 3).filterMap (MolMono_pinD T')).Perm
      ((MX, .inl b, pinClass b) :: (List.finRange 3).filterMap (MolMono_pinD T)) := by
    refine SelRunIso_filterMap_one _ _ _ b _ (List.nodup_finRange 3) (List.mem_finRange b) ?_ ?_ ?_
    · simp only [MolMono_pinD, hancy]
    · simp only [MolMono_pinD, hb₀, hmr, hMX]
    · intro a _ ha
      have hne : (.inl a : Atom 3 n) ≠ .inl b := fun h => ha (Sum.inl_injective h)
      simp only [MolMono_pinD, hanc _ hne, hmr]
  -- the present edges as lists
  set A := (T.comps.erase c).filterMap (MolMono_edgeD T) with hA
  set P := (List.finRange 3).filterMap (MolMono_pinD T) with hP
  have hpc : T.comps.Perm (c :: T.comps.erase c) := List.perm_cons_erase hcmem
  have hET : (MolMono_edges T).Perm ((Mx, .inl b, m) :: (A ++ P)) := by
    unfold MolMono_edges
    have := (hpc.filterMap (MolMono_edgeD T)).append_right P
    rw [List.filterMap_cons_some heT] at this
    exact this
  have hET' : (MolMono_edges T').Perm ((Mx, MX, m) :: (MX, .inl b, pinClass b) :: (A ++ P)) := by
    unfold MolMono_edges
    have hcomps : T'.comps = T.comps ++ [mkC .dot (.inl b) X] := rfl
    rw [hcomps, List.filterMap_append, List.filterMap_cons_none hnewD, List.filterMap_nil,
      List.append_nil]
    have h1 := hpc.filterMap (MolMono_edgeD T')
    rw [List.filterMap_cons_some heT'] at h1
    have h2 : (T.comps.erase c).filterMap (MolMono_edgeD T') = A :=
      List.filterMap_congr fun d hd =>
        hother d (List.mem_of_mem_erase hd) fun h => hrest (h ▸ hd)
    rw [h2] at h1
    refine (h1.append hpin).trans ?_
    simp only [List.cons_append]
    exact List.Perm.cons _ List.perm_middle
  have hL : ∀ t ∈ A ++ P, t.1 ≠ .inl b ∧ t.2.1 ≠ .inl b := by
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨d, hd, hdt⟩ := List.mem_filterMap.1 ht
      obtain ⟨hdk, hdm, h1, h2⟩ := SelRunIso_edgeD_some T hdt
      have hdx : d.kind ≠ .xdot := fun h => by rw [h] at hdm; cases hdm
      have hdc : d ≠ c := fun h => hrest (h ▸ hd)
      have hdT : d ∈ T.comps := List.mem_of_mem_erase hd
      refine ⟨fun h => hdc (honly d hdT (Or.inl ?_) hdk hdx),
        fun h => hdc (honly d hdT (Or.inr ?_) hdk hdx)⟩
      · rw [h1] at h
        exact (SelRunIso_flatAtom_inl T (SelRunIso_molRep_eq_inl T h)).1
      · rw [h2] at h
        exact (SelRunIso_flatAtom_inl T (SelRunIso_molRep_eq_inl T h)).1
    · obtain ⟨a, -, hat⟩ := List.mem_filterMap.1 ht
      unfold MolMono_pinD at hat
      rcases ha : T.anchor (.inl a) with _ | b'
      · rw [ha] at hat; cases hat
      · rw [ha] at hat
        cases hat
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨b'', hb'', -⟩ := MolMono_molRep_inr T b'
          simp only at h
          rw [hb''] at h
          cases h
        · simp only [Sum.inl.injEq] at h
          subst h
          rw [hancy] at ha
          cases ha
  have hcut₀ : ¬ ((Mx ∈ S ∧ (.inl b : Atom 3 n) ∉ S) ∨ (Mx ∉ S ∧ (.inl b : Atom 3 n) ∈ S)) := by
    rintro (h | h)
    · exact hxS h.1
    · exact hyS h.2
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · subst h1
    have hm' : m = .plus := hm1 rfl
    subst hm'
    rw [MolMono_cHat_eq, MolMono_cHat_eq, hint, hext,
      SelRunIso_cHatL_perm _ _ _ hET', SelRunIso_cHatL_perm _ _ _ hET,
      SelRunIso_cHatL_cons_no _ _ _ (t := (Mx, .inl 1, .plus)) (fun h => hcut₀ h.2.2.2) (A ++ P)]
    refine SelRunIso_cHatL_two _ _ _ ⟨⟨by simp, Or.inl hMxI, Or.inl hMXI, Or.inr ⟨hxS, hXS⟩⟩,
      hMxI, hMXI⟩ ⟨by simp [pinClass], Or.inl hMXI, Or.inr hyX, Or.inl ⟨hXS, hyS⟩⟩ hMXI rfl hyX
      hyI _ hL
  · subst h2
    have hm' : m = .minus := hm2 rfl
    subst hm'
    rw [MolMono_redCount_eq, MolMono_redCount_eq, hint, hext,
      SelRunIso_redL_perm _ _ _ hET', SelRunIso_redL_perm _ _ _ hET]
    exact SelRunIso_redL_two _ _ _ (fun h => hcut₀ h.2.2.2)
      ⟨rfl, Or.inl hMxI, Or.inl hMXI, Or.inr ⟨hxS, hXS⟩⟩
      ⟨by simp [pinClass], Or.inl hMXI, Or.inr hyX, Or.inl ⟨hXS, hyS⟩⟩ _

end SplitUnpinned

/-! ## The witness graph of the run `selStep1` -/

section RunWit

variable {k n : ℕ}

/-- The witness of [II, Lemma 4.11] at the step from `T` to `g` of the run `selStep1` at the
internal atom `X` from `Γ`, with the facts of the order of the phases of the run: for a weight or
edge `c` of `Γ₀` (a random component of `Γ` without label), `T` has the dotted blocks of `Γ`, and
`g` is the second term `G_{c.x X} G_{X c.y} (G_{XX})⁻¹` of [II, (4.17)] at the component `c` of
`T`, with the charge of `c`, or the split term `1_{u = X}` at an atom `u` of `c`, with `c` a
component of `T`. -/
def SelRunWit (X : Atom k n) (Γ T g : Graph k n) : Prop :=
  ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧
    (∀ a b, T.SameBlock a b ↔ Γ.SameBlock a b) ∧
    ((∃ (i : ℕ) (ch : Charge), T.comps[i]? = some c ∧
        (c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) ∧
        g = ⟨T.comps.eraseIdx i ++ [mkC (.G ch) c.x X, mkC (.G ch) X c.y, mkC (.inv ch) X X],
          T.coeff⟩) ∨
      (c ∈ T.comps ∧ ∃ u ∈ [c.x, c.y], g = ⟨T.comps ++ [mkC .dot u X], T.coeff⟩))

private theorem iso_self_inj {a b : Graph k n} (h : Tracked.self a = Tracked.self b) : a = b := by
  simp only [Tracked.self, Tracked.mk.injEq, heq_eq_eq, true_and, and_true] at h
  exact h

private theorem iso_mem_self {Gs : List (Graph k n)} {g : Graph k n}
    (h : Tracked.self g ∈ Gs.map Tracked.self) : g ∈ Gs := by
  obtain ⟨g', hg', he⟩ := List.mem_map.1 h
  exact iso_self_inj he ▸ hg'

private theorem iso_bind_self (Gs : List (Graph k n))
    (O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n') :
    TExpansion.bind (Gs.map Tracked.self) O = Gs.flatMap fun g => O id g := by
  unfold TExpansion.bind
  rw [List.flatMap_map]
  congr 1
  funext g
  simp only [Tracked.self, Function.comp_id]
  exact List.map_id' _

private theorem iso_findIdx_some {α : Type*} {L : List α} {p : α → Bool} {i : ℕ}
    (h : L.findIdx? p = some i) : ∃ c, L[i]? = some c ∧ p c = true := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  exact ⟨L[i], List.getElem?_eq_getElem hi, hp⟩

/-- The dotted edges are unchanged when a component other than a dotted edge is replaced by
components other than dotted edges. -/
private theorem iso_dg_replace {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind ≠ .dot) (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, d.kind ≠ .dot) :
    step1_dg (T.comps.eraseIdx i ++ new) = step1_dg T.comps := by
  have hp := List.getElem_cons_eraseIdx_perm (List.getElem?_eq_some_iff.1 hc).1
  rw [(List.getElem?_eq_some_iff.1 hc).2] at hp
  unfold step1_dg
  congr 1
  funext u v
  apply propext
  constructor
  · rintro ⟨d, hd, hk, rfl, rfl⟩
    rcases List.mem_append.1 hd with hd | hd
    · exact ⟨d, List.mem_of_mem_eraseIdx hd, hk, rfl, rfl⟩
    · exact absurd hk (hnew d hd)
  · rintro ⟨d, hd, hk, rfl, rfl⟩
    rcases List.mem_cons.1 (hp.symm.subset hd) with rfl | hd'
    · exact absurd hk hcd
    · exact ⟨d, List.mem_append_left _ hd', hk, rfl, rfl⟩

/-- A step of the run that keeps the class `ClsQ`. -/
private def IsoRs (X : Atom k n) (T g : Graph k n) : Prop :=
  SelStep1CohStep X T g ∧ (ClsQ X T → ClsQ X g)

private theorem iso_rs_self {X : Atom k n} {T : Graph k n} (h : SelStep1CohStep X T T) :
    IsoRs X T T :=
  ⟨h, id⟩

private theorem iso_rs_replace {X : Atom k n} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n))) (co : Coeff)
    (hst : SelStep1CohStep X T ⟨T.comps.eraseIdx i ++ new, co⟩)
    (hcl : ∀ d ∈ new, d.kind.isRandom = true → c.kind.isRandom = true ∧ d.label = c.label) :
    IsoRs X T ⟨T.comps.eraseIdx i ++ new, co⟩ := by
  refine ⟨hst, fun hQ d hd hdr => ?_⟩
  rcases List.mem_append.1 hd with h | h
  · exact hQ d (List.mem_of_mem_eraseIdx h) hdr
  · obtain ⟨hr, hl⟩ := hcl d h hdr
    rw [hl]
    exact hQ c (List.mem_of_getElem? hc) hr

private theorem iso_rs_append {X : Atom k n} {T : Graph k n} (κ : Kind) (hκ : κ = .dot ∨ κ = .xdot)
    (u v : Atom k n) (hst : SelStep1CohStep X T ⟨T.comps ++ [mkC κ u v], T.coeff⟩) :
    IsoRs X T ⟨T.comps ++ [mkC κ u v], T.coeff⟩ := by
  have hnr : (mkC κ u v).kind.isRandom = false := by rcases hκ with rfl | rfl <;> rfl
  refine ⟨hst, fun hQ d hd hdr => ?_⟩
  rcases List.mem_append.1 hd with h | h
  · exact hQ d h hdr
  · rw [List.mem_singleton.1 h, hnr] at hdr
    cases hdr

private theorem iso_rs_absorb {X : Atom k n} {T : Graph k n}
    (hℓ : ∃ c ∈ T.comps, c.label = some (.Q, X))
    (hl : ∀ c ∈ T.comps, c.label = none ∨ c.label = some (.Q, X)) :
    IsoRs X T (T.absorb (.Q, X)) := by
  set φ : Comp (Atom k n) → Comp (Atom k n) := fun c =>
    if c.label = none ∧ c.kind.isRandom = true ∧ X ∈ c.minor then { c with label := some (.Q, X) }
    else c with hφ
  have hcomps : (T.absorb (.Q, X)).comps = T.comps.map φ := rfl
  have hk : ∀ c, (φ c).kind = c.kind := by
    intro c
    simp only [hφ]
    split_ifs <;> rfl
  refine ⟨.absorb T hℓ hl, fun hQ d hd hdr => ?_⟩
  rw [hcomps] at hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
  rw [hk c] at hdr
  have hcl := hQ c hc hdr
  have : φ c = c := by
    simp only [hφ]
    refine ite_eq_right fun h => ?_
    rw [hcl] at h
    cases h.1
  rw [this]
  exact hcl

/-- A step of [II, (4.17)] at a pending component `c`: the graph itself, the first term, or the
second term `G_{c.x X} G_{X c.y} (G_{XX})⁻¹` with the charge of `c`. -/
private theorem iso_rs_schur {X : Atom k n} {T g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hp : pendB X c = true) (hwf : c.WF)
    (hg : Tracked.self g ∈ selStep1_schurAt X i T) :
    IsoRs X T g ∧ (g = T ∨ g = ⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ ∨
      ∃ ch, (c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) ∧
        g = ⟨T.comps.eraseIdx i ++ [mkC (.G ch) c.x X, mkC (.G ch) X c.y, mkC (.inv ch) X X],
          T.coeff⟩) := by
  simp only [pendB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, bne_iff_ne,
    ne_eq] at hp
  obtain ⟨⟨⟨⟨hl, hr⟩, hm⟩, hx⟩, hy⟩ := hp
  obtain ⟨κ, cx, cy, cm, cl⟩ := c
  simp only at hl hm hx hy hr hwf ⊢
  subst hl hm
  have h1 : SelStep1CohStep X T
      ⟨T.comps.eraseIdx i ++ [⟨κ, cx, cy, [X], none⟩], T.coeff⟩ →
      IsoRs X T ⟨T.comps.eraseIdx i ++ [⟨κ, cx, cy, [X], none⟩], T.coeff⟩ := fun hst =>
    iso_rs_replace hc _ _ hst (by simp [hr])
  have h2 : ∀ ch,
      ∀ (hst : SelStep1CohStep X T ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cx X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩),
      IsoRs X T ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cx X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩ := fun ch hst =>
    iso_rs_replace hc _ _ hst (by simp [mkC, hr])
  cases κ with
  | G ch =>
    have hS : selStep1_schurAt X i T = oSchurT X i T := by simp [selStep1_schurAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schur i T g hg
    have hE : oSchurT X i T = [(⟨T.comps.eraseIdx i ++ [⟨.G ch, cx, cy, [X], none⟩], T.coeff⟩ :
        Graph k n), ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cx X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩].map Tracked.self := by
      simp only [oSchurT, hc, List.isEmpty_nil, Option.all_none, Bool.and_self, ↓reduceIte,
        solidC, hx, Ne.symm hy]
      rfl
    rw [hE] at hg
    rcases List.mem_cons.1 (iso_mem_self hg) with rfl | hg
    · exact ⟨h1 hst, Or.inr (Or.inl rfl)⟩
    · rw [List.mem_singleton.1 hg] at hst ⊢
      exact ⟨h2 ch hst, Or.inr (Or.inr ⟨ch, Or.inl rfl, rfl⟩)⟩
  | weight ch =>
    have hS : selStep1_schurAt X i T = oSchurWT X i T := by simp [selStep1_schurAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurW i T g hg
    have hyx : cy = cx := hwf.1 rfl
    subst hyx
    have hE : oSchurWT X i T = [(⟨T.comps.eraseIdx i ++ [⟨.weight ch, cy, cy, [X], none⟩],
        T.coeff⟩ : Graph k n), ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cy X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩].map Tracked.self := by
      simp only [oSchurWT, hc]
      split_ifs with hcond
      · rfl
      · simp [hx] at hcond
    rw [hE] at hg
    rcases List.mem_cons.1 (iso_mem_self hg) with rfl | hg
    · exact ⟨h1 hst, Or.inr (Or.inl rfl)⟩
    · rw [List.mem_singleton.1 hg] at hst ⊢
      exact ⟨h2 ch hst, Or.inr (Or.inr ⟨ch, Or.inr (Or.inl rfl), rfl⟩)⟩
  | light ch =>
    have hS : selStep1_schurAt X i T = oSchurWT X i T := by simp [selStep1_schurAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurW i T g hg
    have hyx : cy = cx := hwf.1 rfl
    subst hyx
    have hE : oSchurWT X i T = [(⟨T.comps.eraseIdx i ++ [⟨.light ch, cy, cy, [X], none⟩],
        T.coeff⟩ : Graph k n), ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cy X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩].map Tracked.self := by
      simp only [oSchurWT, hc]
      split_ifs with hcond
      · rfl
      · simp [hx] at hcond
    rw [hE] at hg
    rcases List.mem_cons.1 (iso_mem_self hg) with rfl | hg
    · exact ⟨h1 hst, Or.inr (Or.inl rfl)⟩
    · rw [List.mem_singleton.1 hg] at hst ⊢
      exact ⟨h2 ch hst, Or.inr (Or.inr ⟨ch, Or.inr (Or.inr rfl), rfl⟩)⟩
  | _ =>
    all_goals
      have hS : selStep1_schurAt X i T = oSchurT X i T := by simp [selStep1_schurAt, hc]
      rw [hS] at hg
      have hst := SelStep1CohStep.schur i T g hg
      have hE : oSchurT X i T = [Tracked.self T] := by simp [oSchurT, hc]
      rw [hE] at hg
      have := iso_self_inj (List.mem_singleton.1 hg)
      subst this
      exact ⟨iso_rs_self hst, Or.inl rfl⟩

private theorem iso_rs_minor {X : Atom k n} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hr : c.kind.isRandom = true) (m : List (Atom k n)) (co : Coeff)
    (hst : SelStep1CohStep X T ⟨T.comps.eraseIdx i ++ [{ c with minor := m }], co⟩) :
    IsoRs X T ⟨T.comps.eraseIdx i ++ [{ c with minor := m }], co⟩ :=
  iso_rs_replace hc _ _ hst (by simp [hr])

private theorem iso_rs_three {X : Atom k n} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hr : c.kind.isRandom = true) (a b e : Comp (Atom k n))
    (co : Coeff) (hst : SelStep1CohStep X T ⟨T.comps.eraseIdx i ++ [a, b, e], co⟩)
    (hl : a.label = c.label ∧ b.label = c.label ∧ e.label = c.label) :
    IsoRs X T ⟨T.comps.eraseIdx i ++ [a, b, e], co⟩ := by
  refine iso_rs_replace hc _ _ hst ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl) _
  exacts [⟨hr, hl.1⟩, ⟨hr, hl.2.1⟩, ⟨hr, hl.2.2⟩]

/-- A step of [II, (4.20)] at a component `c`. -/
private theorem iso_rs_rev {X : Atom k n} {T g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hg : Tracked.self g ∈ selStep1_revAt X i T) : IsoRs X T g := by
  obtain ⟨κ, cx, cy, cm, cl⟩ := c
  cases κ with
  | G ch =>
    have hS : selStep1_revAt X i T = oSchurRevT X i T := by simp [selStep1_revAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurRev i T g hg
    simp only [oSchurRevT, hc] at hg
    split_ifs at hg
    · rcases List.mem_cons.1 hg with he | hg
      · rw [iso_self_inj he] at hst ⊢
        exact iso_rs_minor hc rfl _ _ hst
      · rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
        exact iso_rs_three hc rfl _ _ _ _ hst ⟨rfl, rfl, rfl⟩
    · rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      exact iso_rs_self hst
  | weight ch =>
    have hS : selStep1_revAt X i T = oSchurWRevT X i T := by simp [selStep1_revAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurWRev i T g hg
    simp only [oSchurWRevT, hc] at hg
    split_ifs at hg
    · rcases List.mem_cons.1 hg with he | hg
      · rw [iso_self_inj he] at hst ⊢
        exact iso_rs_minor hc rfl _ _ hst
      · rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
        exact iso_rs_three hc rfl _ _ _ _ hst ⟨rfl, rfl, rfl⟩
    · rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      exact iso_rs_self hst
  | light ch =>
    have hS : selStep1_revAt X i T = oSchurWRevT X i T := by simp [selStep1_revAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurWRev i T g hg
    simp only [oSchurWRevT, hc] at hg
    split_ifs at hg
    · rcases List.mem_cons.1 hg with he | hg
      · rw [iso_self_inj he] at hst ⊢
        exact iso_rs_minor hc rfl _ _ hst
      · rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
        exact iso_rs_three hc rfl _ _ _ _ hst ⟨rfl, rfl, rfl⟩
    · rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      exact iso_rs_self hst
  | _ =>
    all_goals
      have hS : selStep1_revAt X i T = oSchurRevT X i T := by simp [selStep1_revAt, hc]
      rw [hS] at hg
      have hst := SelStep1CohStep.schurRev i T g hg
      have hE : oSchurRevT X i T = [Tracked.self T] := by simp [oSchurRevT, hc]
      rw [hE] at hg
      rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      exact iso_rs_self hst

/-- A step of [II, (4.21)] at the weight `(G_{xx})⁻¹` with index `i`. -/
private theorem iso_rs_taylor {X : Atom k n} {T g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (D : ℕ)
    (hg : Tracked.self g ∈ oTaylorT D i T) : IsoRs X T g := by
  have hst := SelStep1CohStep.taylor (X := X) D i T g hg
  have hr : c.kind.isRandom = true := by rw [hk]; rfl
  simp only [oTaylorT, hc, hk] at hg
  split_ifs at hg
  · rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨j, -, hj⟩ := List.mem_map.1 hg
      rw [← iso_self_inj hj] at hst ⊢
      refine iso_rs_replace hc _ _ hst ?_
      intro d hd _
      rw [List.eq_of_mem_replicate hd]
      exact ⟨hr, rfl⟩
    · rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      refine iso_rs_replace hc _ _ hst ?_
      simp [hr]
  · rw [iso_self_inj (List.mem_singleton.1 hg)] at hst ⊢
    exact iso_rs_self hst

/-- A step of `1_{u ≠ v} = 1 - 1_{u = v}` at a `×`-dotted edge `c` with index `i`. -/
private theorem iso_rs_clean {X : Atom k n} {T g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c)
    (hE : oXdotT i T = [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].map Tracked.self)
    (hg : g ∈ [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩]) : IsoRs X T g := by
  have hst : SelStep1CohStep X T g := .xdot i T g (by rw [hE]; exact List.mem_map_of_mem hg)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · have h := iso_rs_replace (X := X) hc [] T.coeff (by simpa using hst) (by simp)
    simpa using h
  · exact iso_rs_replace hc _ _ hst (by simp [mkC, Kind.isRandom])

private theorem iso_firstRed_some {m : ℕ} {L : List (Comp (Atom k m))} {i : ℕ}
    (h : selStep1_firstRed L = some i) :
    ∃ c, L[i]? = some c ∧ c.kind = .dot ∧ (step1_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep1_firstRed at h
  simpa using List.find?_some h

/-- The removals of redundant dotted edges: a chain of `SelStep1CohDrop`, keeping the components
other than dotted edges. -/
private theorem iso_drop {m : ℕ} : ∀ (r : ℕ) (g : Graph k m),
    Relation.ReflTransGen SelStep1CohDrop g (selStep1_drop r g) ∧
      (∀ c ∈ (selStep1_drop r g).comps, c ∈ g.comps) ∧
      (∀ c ∈ g.comps, c.kind ≠ .dot → c ∈ (selStep1_drop r g).comps)
  | 0, g => ⟨Relation.ReflTransGen.refl, fun _ h => h, fun _ h _ => h⟩
  | r + 1, g => by
    rcases hf : selStep1_firstRed g.comps with _ | i
    · simp only [selStep1_drop, hf]
      exact ⟨Relation.ReflTransGen.refl, fun _ h => h, fun _ h _ => h⟩
    · obtain ⟨c, hc, hk, hr⟩ := iso_firstRed_some hf
      obtain ⟨-, -, -, hmem, -⟩ := step1_drop_one g hc hk hr
      obtain ⟨h1, h4, h5⟩ := iso_drop r ⟨g.comps.eraseIdx i, g.coeff⟩
      simp only [selStep1_drop, hf]
      exact ⟨Relation.ReflTransGen.head ⟨i, c, hc, hk, hr, rfl⟩ h1,
        fun d hd => List.mem_of_mem_eraseIdx (h4 d hd), fun d hd hdk => h5 d (hmem d hd hdk) hdk⟩

private theorem iso_mergeComp_label {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : step3_mergeComp rep f c = some c') :
    c'.label = c.label.map (Prod.map id f) ∧ c'.kind.isRandom = c.kind.isRandom := by
  refine ⟨?_, ?_⟩
  · unfold step3_mergeComp at h
    split_ifs at h
    · obtain rfl := Option.some.inj h
      rfl
    · obtain rfl := Option.some.inj h
      rfl
  · rcases step3_mergeComp_kind h with h' | ⟨ch, h1, h2⟩
    · rw [h']
    · rw [h1, h2]
      rfl

/-- The last step of the run at a graph `T` with the clauses `Step1Base`: `O_merge`, then
removals of redundant dotted edges; a graph `T` of class `ClsQ` gives a `Q`-graph. -/
private theorem iso_final {d S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base d S X Γ T)
    {t : Tracked k n} (ht : t ∈ selStep1_final T) :
    ∃ s : Tracked k n, T.mergeT = some s ∧ ∃ g' : Graph k s.nOut,
      Relation.ReflTransGen SelStep1CohDrop s.g g' ∧ t = ⟨s.nOut, g', s.f⟩ ∧
      (ClsQ X T → g'.IsQGraphAt (s.f X)) := by
  unfold selStep1_final at ht
  rcases hm : T.mergeT with _ | s
  · rw [hm] at ht
    cases ht
  rw [hm, List.mem_singleton] at ht
  have hs := step3_mergeT_spec hm
  obtain ⟨hch, hsub, hkeep⟩ := iso_drop (step1_eL s.g.comps - step1_eL T.comps).toNat s.g
  refine ⟨s, rfl, _, hch, ht, fun hQ => ?_⟩
  have hmc : ∀ c' ∈ s.g.comps, ∃ c ∈ T.comps, step3_mergeComp T.step3_mrep s.f c = some c' := by
    intro c' hc'
    rw [hs.comps_eq] at hc'
    exact List.mem_filterMap.1 hc'
  obtain ⟨c, hc, hcl, -, -⟩ := hB.labex
  have hcr : c.kind.isRandom = true := (hB.wf c hc).2 (by rw [hcl]; rfl)
  have hcd : c.kind ≠ .dot := by intro h; rw [h] at hcr; cases hcr
  obtain ⟨c', hc'⟩ : ∃ c', step3_mergeComp T.step3_mrep s.f c = some c' := by
    unfold step3_mergeComp
    split_ifs with h1
    · simp [hcd] at h1
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have hc'k : c'.kind ≠ .dot := by
    rcases step3_mergeComp_kind hc' with h | ⟨ch, -, h⟩ <;> rw [h]
    · exact hcd
    · simp
  have hc's : c' ∈ s.g.comps := by
    rw [hs.comps_eq]
    exact List.mem_filterMap.2 ⟨c, hc, hc'⟩
  refine ⟨⟨c', hkeep c' hc's hc'k, ?_⟩, fun e he hre => ?_⟩
  · rw [(iso_mergeComp_label hc').1, hcl]
    rfl
  · obtain ⟨c₀, hc₀, hm₀⟩ := hmc e (hsub e he)
    obtain ⟨hl₀, hr₀⟩ := iso_mergeComp_label hm₀
    rw [hl₀]
    rcases hre with hre | hre
    · rw [hr₀] at hre
      rw [hQ c₀ hc₀ hre]
      rfl
    · rw [hl₀] at hre
      rcases hB.lab c₀ hc₀ with h | h
      · rw [h] at hre; cases hre
      · rw [h]; rfl

/-- An output `t` of a phase started at `T`: a chain of steps from `T` to a graph `T_f` with the
clauses `Step1Base`, `t` an output of the last step at `T_f`, and `T_f` of class `ClsQ` under
`q`. -/
private def IsoOut (X : Atom k n) (Γ : Graph k n) (q : Prop) (T : Graph k n) (t : Tracked k n) :
    Prop :=
  ∃ T_f, Relation.ReflTransGen (IsoRs X) T T_f ∧ (∃ d S, Step1Base d S X Γ T_f) ∧
    t ∈ selStep1_final T_f ∧ (q → ClsQ X T_f)

private theorem iso_rtg_step {X : Atom k n} {a b : Graph k n}
    (h : Relation.ReflTransGen (IsoRs X) a b) : Relation.ReflTransGen (SelStep1CohStep X) a b := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail h.1

private theorem IsoOut.cons {X : Atom k n} {Γ : Graph k n} {q q' : Prop} {T g : Graph k n}
    {t : Tracked k n} (h : IsoOut X Γ q' g t) (hR : IsoRs X T g) (hq : q → q') :
    IsoOut X Γ q T t := by
  obtain ⟨T_f, h1, hB, ht, hQ⟩ := h
  exact ⟨T_f, Relation.ReflTransGen.head hR h1, hB, ht, fun h => hQ (hq h)⟩

private theorem IsoOut.final {d S : ℕ} {X : Atom k n} {Γ T : Graph k n} {q : Prop}
    (hB : Step1Base d S X Γ T) {t : Tracked k n} (ht : t ∈ selStep1_final T) (hq : q → ClsQ X T) :
    IsoOut X Γ q T t :=
  ⟨T, Relation.ReflTransGen.refl, ⟨d, S, hB⟩, ht, hq⟩

private theorem IsoOut.mono {X : Atom k n} {Γ T : Graph k n} {q q' : Prop} {t : Tracked k n}
    (h : IsoOut X Γ q T t) (hq : q' → q) : IsoOut X Γ q' T t := by
  obtain ⟨T_f, h1, hB, ht, hQ⟩ := h
  exact ⟨T_f, h1, hB, ht, fun h => hQ (hq h)⟩

/-- An output `t` of a phase started at `T` whose chain contains the witness `SelRunWit` at a
step from `T₁` to `g`. -/
private def WitOut (X : Atom k n) (Γ T : Graph k n) (t : Tracked k n) : Prop :=
  ∃ T₁ g, Relation.ReflTransGen (SelStep1CohStep X) T T₁ ∧ SelStep1CohStep X T₁ g ∧
    SelRunWit X Γ T₁ g ∧ IsoOut X Γ False g t

private theorem WitOut.cons {X : Atom k n} {Γ T₀ T : Graph k n} {t : Tracked k n}
    (h : WitOut X Γ T t) (hst : SelStep1CohStep X T₀ T) : WitOut X Γ T₀ t := by
  obtain ⟨T₁, g, h1, h2, h3, h4⟩ := h
  exact ⟨T₁, g, Relation.ReflTransGen.head hst h1, h2, h3, h4⟩

private theorem iso_clean_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} :
    ∀ (m : ℕ) (T : Graph k n), Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      (ClsQ X T ∨ ClsW d X Γ T) → ∀ t ∈ selStep1_clean m T, IsoOut X Γ (ClsQ X T) T t := by
  intro m
  induction m with
  | zero =>
    intro T hB _ _ _ _ t ht
    simp only [selStep1_clean] at ht
    exact IsoOut.final hB ht id
  | succ m ih =>
    intro T hB hK hmin hinv hcls t ht
    rcases hf : T.comps.findIdx? (badB T.comps) with _ | i
    · simp only [selStep1_clean, hf] at ht
      exact IsoOut.final hB ht id
    · obtain ⟨c, hc, hcb⟩ := iso_findIdx_some hf
      obtain ⟨hE, -, -, hG⟩ := selStep1_clean_step hB hK hmin hinv hcls hc hcb
      simp only [selStep1_clean, hf] at ht
      rw [hE, iso_bind_self, List.mem_flatMap] at ht
      obtain ⟨g, hg, ht⟩ := ht
      by_cases hxa : g.XdotApart
      · rw [ite_eq_left hxa] at ht
        obtain ⟨hB', hK', hmin', hinv', hcls', -⟩ := (hG g hg).2 hxa
        have hR := iso_rs_clean (X := X) hc hE hg
        exact (ih g hB' hK' hmin' hinv' hcls' t ht).cons hR hR.2
      · rw [ite_eq_right hxa] at ht
        cases ht

private theorem iso_taylor_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} :
    ∀ (m : ℕ) (T : Graph k n), nInv T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (ClsQ X T ∨ ClsW d X Γ T) →
      ∀ t ∈ selStep1_taylor d m T, IsoOut X Γ (ClsQ X T) T t := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hmin hcls t ht
    have hinv : ∀ c ∈ T.comps, c.kind.step1_isInvB = false := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => c.kind.step1_isInvB :=
        List.mem_filter.2 ⟨hc, by simpa using h⟩
      have := List.length_pos_of_mem this
      unfold nInv at hm
      omega
    simp only [selStep1_taylor] at ht
    exact iso_clean_out _ T hB hK hmin hinv hcls t ht
  | succ m ih =>
    intro T hm hB hK hmin hcls t ht
    rcases hf : T.comps.findIdx? (fun c => c.kind.step1_isInvB) with _ | i
    · simp only [selStep1_taylor, hf] at ht
      exact iso_clean_out _ T hB hK hmin (List.findIdx?_eq_none_iff.1 hf) hcls t ht
    · obtain ⟨c, hc, hci⟩ := iso_findIdx_some hf
      obtain ⟨ch, hk⟩ : ∃ ch, c.kind = .inv ch := by
        revert hci
        cases c.kind <;> simp [Kind.step1_isInvB]
      obtain ⟨Gs, hE, -, -, hGs⟩ := selStep1_taylor_step hB hK hmin hcls hc hci
      simp only [selStep1_taylor, hf] at ht
      have hE' := hE
      rw [hE, iso_bind_self, List.mem_flatMap] at ht
      obtain ⟨g, hg, ht⟩ := ht
      obtain ⟨hB', hK', hmin', hcls', hcnt⟩ := hGs g hg
      have hR := iso_rs_taylor (X := X) hc hk d (by rw [hE']; exact List.mem_map_of_mem hg)
      exact (ih g (by omega) hB' hK' hmin' hcls' t ht).cons hR hR.2

private theorem iso_rev_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} :
    ∀ (m : ℕ) (T : Graph k n), nMin T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      (ClsQ X T ∨ ClsW d X Γ T) → ∀ t ∈ selStep1_rev d m X T, IsoOut X Γ (ClsQ X T) T t := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hcls t ht
    have hmin : ∀ c ∈ T.comps, c.minor = [] := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => !c.minor.isEmpty :=
        List.mem_filter.2 ⟨hc, by simpa [List.isEmpty_iff] using h⟩
      have := List.length_pos_of_mem this
      unfold nMin at hm
      omega
    simp only [selStep1_rev] at ht
    exact iso_taylor_out _ T le_rfl hB hK hmin hcls t ht
  | succ m ih =>
    intro T hm hB hK hcls t ht
    rcases hf : T.comps.findIdx? (fun c => !c.minor.isEmpty) with _ | i
    · have hmin : ∀ c ∈ T.comps, c.minor = [] := by
        intro c hc
        have := List.findIdx?_eq_none_iff.1 hf c hc
        simpa [List.isEmpty_iff] using this
      simp only [selStep1_rev, hf] at ht
      exact iso_taylor_out _ T le_rfl hB hK hmin hcls t ht
    · obtain ⟨c, hc, hcm⟩ := iso_findIdx_some hf
      have hcT : c ∈ T.comps := List.mem_of_getElem? hc
      obtain ⟨hmX, -⟩ : c.minor = [X] ∧ _ := by
        rcases hB.minor c hcT with h | h
        · rw [h] at hcm; simp at hcm
        · exact h
      obtain ⟨Gs, hE, -, -, hGs⟩ := selStep1_rev_step hB hK hcls hc hmX
      simp only [selStep1_rev, hf] at ht
      have hE' := hE
      rw [hE, iso_bind_self, List.mem_flatMap] at ht
      obtain ⟨g, hg, ht⟩ := ht
      obtain ⟨⟨hB', hcls', hmin', -⟩, hK'⟩ := hGs g hg
      have hR := iso_rs_rev (X := X) hc (by rw [hE']; exact List.mem_map_of_mem hg)
      exact (ih g (by omega) hB' hK' hcls' t ht).cons hR hR.2

private theorem iso_absorb_out {d S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Step1Base d S X Γ T) (hK : Step1OK1 Γ T) (hnp : nPend X T.comps = 0)
    (hcls : ClsW d X Γ T ∨ AllPend X T) :
    ∀ t ∈ selStep1_absorb d X T, IsoOut X Γ (AllPend X T) T t := by
  intro t ht
  unfold selStep1_absorb at ht
  by_cases hA : AllPend X T
  · rw [ite_eq_left hA] at ht
    obtain ⟨hB', hQ, -⟩ := absorb_step hB hnp hA
    obtain ⟨c, hc, hcl, -⟩ := hB.labex
    exact (iso_rev_out _ _ le_rfl hB' (hK.absorb X) (Or.inl hQ) t ht).cons
      (iso_rs_absorb ⟨c, hc, hcl⟩ hB.lab) fun _ => hQ
  · rw [ite_eq_right hA] at ht
    exact (iso_rev_out _ T le_rfl hB hK (Or.inr (hcls.resolve_right hA)) t ht).mono
      fun h => absurd h hA

private theorem iso_allPend_first {X : Atom k n} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hA : AllPend X T) : AllPend X ⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ := by
  intro d hd hl hr
  rcases List.mem_append.1 hd with h | h
  · exact hA d (List.mem_of_mem_eraseIdx h) hl hr
  · rw [List.mem_singleton.1 h]
    exact Or.inr rfl

private theorem iso_schur_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} (hΓ : Γ.Plain) :
    ∀ (m : ℕ) (T : Graph k n), nPend X T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      PendInv X Γ T → (ClsW d X Γ T ∨ AllPend X T) →
      ∀ t ∈ selStep1_schur d m X T, IsoOut X Γ False T t ∧
        (AllPend X T → step1_dg T.comps = step1_dg Γ.comps →
          WitOut X Γ T t ∨ IsoOut X Γ True T t) := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK _ hcls t ht
    simp only [selStep1_schur] at ht
    have h := iso_absorb_out hB hK (by omega) hcls t ht
    exact ⟨h.mono fun h => h.elim, fun hA _ => Or.inr (h.mono fun _ => hA)⟩
  | succ m ih =>
    intro T hm hB hK hP hcls t ht
    rcases hf : T.comps.findIdx? (pendB X) with _ | i
    · have hnp : nPend X T.comps = 0 := by
        unfold nPend
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c hc
        simp [List.findIdx?_eq_none_iff.1 hf c hc]
      simp only [selStep1_schur, hf] at ht
      have h := iso_absorb_out hB hK hnp hcls t ht
      exact ⟨h.mono fun h => h.elim, fun hA _ => Or.inr (h.mono fun _ => hA)⟩
    · obtain ⟨c, hc, hcp⟩ := iso_findIdx_some hf
      have hcT : c ∈ T.comps := List.mem_of_getElem? hc
      obtain ⟨Gs, hE, -, -, hGs⟩ := selStep1_schur_step hΓ hB hK hP hcls hc hcp
      simp only [selStep1_schur, hf] at ht
      have hE' := hE
      rw [hE, iso_bind_self, List.mem_flatMap] at ht
      obtain ⟨g, hg, ht⟩ := ht
      obtain ⟨⟨hB', hP', hcls', hp'⟩, hK'⟩ := hGs g hg
      obtain ⟨hR, hform⟩ := iso_rs_schur hc hcp (hB.wf c hcT)
        (by rw [hE']; exact List.mem_map_of_mem hg)
      obtain ⟨h₁, h₂⟩ := ih g (by omega) hB' hK' hP' hcls' t ht
      have hpp := hcp
      simp only [pendB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hpp
      have hcr : c.kind.isRandom = true := hpp.1.1.1.2
      have hcd : c.kind ≠ .dot := fun h => by rw [h] at hcr; cases hcr
      refine ⟨h₁.cons hR fun h => h.elim, fun hA hdg => ?_⟩
      have hshift : (WitOut X Γ g t ∨ IsoOut X Γ True g t) →
          WitOut X Γ T t ∨ IsoOut X Γ True T t := by
        rintro (h | h)
        · exact Or.inl (h.cons hR.1)
        · exact Or.inr (h.cons hR fun _ => trivial)
      rcases hform with rfl | rfl | ⟨ch, hkc, rfl⟩
      · exact hshift (h₂ hA hdg)
      · refine hshift (h₂ (iso_allPend_first hA) ?_)
        rw [iso_dg_replace hc hcd _ (by simp [hcd]), hdg]
      · refine Or.inl ⟨T, _, Relation.ReflTransGen.refl, hR.1, ⟨c, (hP c hcT hcp).1,
          hpp.1.1.1.1, hcr, fun a b => ?_, Or.inl ⟨i, ch, hc, hkc, rfl⟩⟩, h₁⟩
        change (step1_dg T.comps).Reachable a b ↔ (step1_dg Γ.comps).Reachable a b
        rw [hdg]

private theorem iso_hasX_mono {L L' : List (Comp (Atom k n))} (h : ∀ d ∈ L, d ∈ L')
    {u v : Atom k n} (hx : Step1HasX L u v) : Step1HasX L' u v := by
  obtain ⟨d, hd, rest⟩ := hx
  exact ⟨d, h d hd, rest⟩

private theorem iso_sizeΦ_append {D' : ℕ} {X : Atom k n} (L : List (Comp (Atom k n)))
    {κ : Kind} (hκ : κ = .dot ∨ κ = .xdot) (u v : Atom k n) :
    step1_sizeΦ D' X (L ++ [mkC κ u v]) = step1_sizeΦ D' X L + 1 := by
  unfold step1_sizeΦ nPend nMin nInv
  rw [List.filter_append, List.filter_append, List.filter_append]
  rcases hκ with rfl | rfl <;> simp [mkC, pendB, Kind.isRandom, Kind.step1_isInvB] <;> ring

open Classical in
private theorem iso_split_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} (hΓ : Γ.Plain)
    (hfree : Γ.UnlabelledFreeAtBlock X) :
    ∀ (us : List (Atom k n)) (T : Graph k n),
      Step1Base d S X Γ T → Step1OK1 Γ T → step1_sizeΦ d X T.comps + us.length ≤ S →
      step1_dg T.comps = step1_dg Γ.comps → (∀ c ∈ Γ.comps, c ∈ T.comps) →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      AllPend X T →
      (∀ c ∈ T.comps, pendB X c = true →
        c ∈ Γ.comps ∧ ∀ u ∈ [c.x, c.y], Step1HasX T.comps u X ∨ u ∈ us) →
      (∀ u ∈ us, ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧ u ∈ [c.x, c.y]) →
      ∀ t ∈ selStep1_split d X us T, WitOut X Γ T t ∨ IsoOut X Γ True T t
  | [], T, hB, hK, _, hdg, _, _, _, hA, hP, _ => by
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
    intro t ht
    simp only [selStep1_split] at ht
    exact (iso_schur_out hΓ _ T le_rfl hB hK hP' (Or.inr hA) t ht).2 hA hdg
  | u :: us, T, hB, hK, hsz, hdg, hsub, hmin, hinv, hA, hP, hus => by
    intro t ht
    obtain ⟨c₀, hc₀, hl₀, hr₀, hu₀⟩ := hus u (List.mem_cons_self ..)
    have hBsz : step1_sizeΦ d X T.comps + 1 ≤ S := by
      simp only [List.length_cons] at hsz
      omega
    obtain ⟨hE, -, -, hgood₁, hB₂, hK₂, hdg₂⟩ :=
      selStep1_split_step hfree hB hK hBsz hdg hc₀ hl₀ hr₀ hu₀
    simp only [selStep1_split, List.mem_append] at ht
    rcases ht with ht | ht
    · -- the term with `u` identified with `X`
      by_cases hxa : (⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n).XdotApart
      · rw [ite_eq_left hxa] at ht
        obtain ⟨hB₁, hK₁, hcls⟩ := hgood₁ hxa
        have hout := iso_clean_out _ _ hB₁ hK₁ (fun d hd => by
            rcases List.mem_append.1 hd with h | h
            · exact hmin d h
            · rw [List.mem_singleton.1 h]; rfl) (fun d hd => by
            rcases List.mem_append.1 hd with h | h
            · exact hinv d h
            · rw [List.mem_singleton.1 h]; rfl) (Or.inr hcls) t ht
        refine Or.inl ⟨T, _, Relation.ReflTransGen.refl, .split u T _ (by rw [hE]; simp),
          ⟨c₀, hc₀, hl₀, hr₀, fun a b => ?_, Or.inr ⟨hsub c₀ hc₀, u, hu₀, rfl⟩⟩,
          hout.mono fun h => h.elim⟩
        change (step1_dg T.comps).Reachable a b ↔ (step1_dg Γ.comps).Reachable a b
        rw [hdg]
      · rw [ite_eq_right hxa] at ht
        cases ht
    · -- the term with `u ≠ X`
      have hst : SelStep1CohStep X T ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩ :=
        .split u T _ (by rw [hE]; simp)
      have h := iso_split_out hΓ hfree us _ hB₂ hK₂ (by
          rw [iso_sizeΦ_append _ (Or.inr rfl)]
          simp only [List.length_cons] at hsz
          omega) hdg₂ (fun c hc => List.mem_append_left _ (hsub c hc)) (by
          intro d hd
          rcases List.mem_append.1 hd with h | h
          · exact hmin d h
          · rw [List.mem_singleton.1 h]; rfl) (by
          intro d hd
          rcases List.mem_append.1 hd with h | h
          · exact hinv d h
          · rw [List.mem_singleton.1 h]; rfl) (by
          intro d hd hdl hdr
          rcases List.mem_append.1 hd with h | h
          · exact hA d h hdl hdr
          · rw [List.mem_singleton.1 h] at hdr; simp [mkC, Kind.isRandom] at hdr) (by
          intro d hd hdp
          rcases List.mem_append.1 hd with h | h
          · obtain ⟨h1, h2⟩ := hP d h hdp
            refine ⟨h1, fun v hv => ?_⟩
            rcases h2 v hv with h3 | h3
            · exact Or.inl (iso_hasX_mono (fun d hd => List.mem_append_left _ hd) h3)
            · rcases List.mem_cons.1 h3 with rfl | h4
              · exact Or.inl ⟨mkC .xdot v X, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
              · exact Or.inr h4
          · rw [List.mem_singleton.1 h] at hdp; simp [pendB, mkC, Kind.isRandom] at hdp)
        (fun v hv => hus v (List.mem_cons_of_mem _ hv)) t ht
      rcases h with h | h
      · exact Or.inl (h.cons hst)
      · exact Or.inr (h.cons (iso_rs_append .xdot (Or.inr rfl) u X hst) fun _ => trivial)

/-- The clauses of the phases at the input `Γ`, for the Taylor degree `d` and the size bound
`(d + 6) C + 1`. -/
private theorem iso_root {C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph k n₀} (d : ℕ) (hN : Γ.Normal C)
    (hQ : Γ.IsQFormAt (.inr x₀)) (hP : Γ.Plain) (hxa : Γ.XdotApart)
    (hfree : Γ.UnlabelledFreeAtBlock (.inr x₀)) :
    Step1Base d ((d + 6) * C + 1) (.inr x₀) Γ Γ ∧
      step1_sizeΦ d (.inr x₀) Γ.comps + (selStep1_us Γ).length ≤ (d + 6) * C + 1 ∧
      (∀ c ∈ Γ.comps, c.minor = []) ∧ (∀ c ∈ Γ.comps, c.kind.step1_isInvB = false) ∧
      AllPend (.inr x₀) Γ ∧
      (∀ c ∈ Γ.comps, pendB (.inr x₀) c = true →
        c ∈ Γ.comps ∧ ∀ u ∈ [c.x, c.y], Step1HasX Γ.comps u (.inr x₀) ∨ u ∈ selStep1_us Γ) ∧
      (∀ u ∈ selStep1_us Γ, ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧
        u ∈ [c.x, c.y]) := by
  set X : Atom k n₀ := .inr x₀ with hXdef
  have hsize := hN.1.size
  have hlenΓ : Γ.comps.length ≤ C := by omega
  have hminΓ : nMin Γ.comps = 0 := by
    unfold nMin
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp [(hP c hc).1]
  have hinv : ∀ c ∈ Γ.comps, c.kind.step1_isInvB = false := fun c hc => by
    have := (hP c hc).2.1
    revert this
    cases c.kind <;> simp [Kind.step1_isInvB]
  have hinvΓ : nInv Γ.comps = 0 := by
    unfold nInv
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp [hinv c hc]
  have hΦ : step1_sizeΦ d X Γ.comps ≤ (d + 4) * C := by
    have hpendΓ : nPend X Γ.comps ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
    unfold step1_sizeΦ
    rw [hminΓ, hinvΓ]
    have h1 : (d + 3) * (nPend X Γ.comps + 0) ≤ (d + 3) * C :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
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
  have hS : (d + 4) * C + 2 * C ≤ (d + 6) * C + 1 := by nlinarith
  refine ⟨base_init hN hQ hP hxa rfl (by omega), by omega, fun c hc => (hP c hc).1, hinv, ?_, ?_,
    ?_⟩
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

end RunWit

/-- **The witness graph of the run** (the proof of [II, Lemma 4.11], with the order of the phases
of the run `selStep1`): for a normal regular graph `Γ = Γ₀ Q_x(Γ̃₀)` with bound `C` (`x`
internal) such that `Γ₀` has no weight or edge attached to the block of `x`, every output `t` of
the run with Taylor degree `d` that is not a `Q`-graph at the image of `x` is reached from `Γ` by
a chain of steps of the run (`SelStep1CohStep`) to a graph `T`, the step from `T` to `g` of the
witness `SelRunWit` (`T` has the dotted blocks of `Γ`; `g` is the second term of [II, (4.17)] at
a weight or edge `c` of `Γ₀` in `T`, with the charge of `c`, or the split term `1_{u = x}` at an
atom `u` of such a `c` in `T`), a chain of steps of the run from `g` to a graph `T_f`, then
`O_merge` at `T_f` and removals of redundant dotted edges, with the atom map of `O_merge`. -/
theorem selStep1_witnessRun {k C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph k n₀} (d : ℕ)
    (hN : Γ.Normal C) (hQ : Γ.IsQFormAt (.inr x₀)) (hP : Γ.Plain)
    (hfree : Γ.UnlabelledFreeAtBlock (.inr x₀)) :
    ∀ t ∈ selStep1 d (.inr x₀) Γ, ¬ t.g.IsQGraphAt (t.f (.inr x₀)) →
      ∃ (T g T_f : Graph k n₀) (s : Tracked k n₀) (g' : Graph k s.nOut),
        Relation.ReflTransGen (SelStep1CohStep (.inr x₀)) Γ T ∧
        SelStep1CohStep (.inr x₀) T g ∧ SelRunWit (.inr x₀) Γ T g ∧
        Relation.ReflTransGen (SelStep1CohStep (.inr x₀)) g T_f ∧ T_f.mergeT = some s ∧
        Relation.ReflTransGen SelStep1CohDrop s.g g' ∧ t = ⟨s.nOut, g', s.f⟩ := by
  intro t ht hnQ
  by_cases hxa : Γ.XdotApart
  swap
  · rw [selStep1, ite_eq_right hxa] at ht
    cases ht
  rw [selStep1, ite_eq_left hxa, ite_eq_left hfree] at ht
  obtain ⟨hB, hsz, hmin, hinv, hA, hPd, hus⟩ := iso_root d hN hQ hP hxa hfree
  rcases iso_split_out hP hfree _ Γ hB (Step1OK1.refl Γ) hsz rfl (fun _ h => h) hmin hinv hA
    hPd hus t ht with ⟨T, g, h1, h2, h3, T_f, h4, ⟨d', S', hBf⟩, htf, -⟩ | ⟨T_f, -, ⟨d', S', hBf⟩,
      htf, hQf⟩
  · obtain ⟨s, hm, g', hdr, rfl, -⟩ := iso_final hBf htf
    exact ⟨T, g, T_f, s, g', h1, h2, h3, iso_rtg_step h4, hm, hdr,
      rfl⟩
  · obtain ⟨s, -, g', -, rfl, hQg⟩ := iso_final (X := .inr x₀) hBf htf
    exact absurd (hQg (hQf trivial)) hnQ


/-! ## Weak isolation of the output graphs without labels -/

section SelRunIsoMain

variable {n : ℕ}

/-- The image of the representative of the molecule of an internal atom lies in the molecule of
the image of the atom. -/
private theorem SelRunIso_rep_map {k m : ℕ} {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {φ : Atom k n → Atom k m} (h : Γ₁.MolMono Γ₂ φ) (a : Fin n) :
    Γ₂.molRep (φ (Γ₁.molRep (.inr a))) = Γ₂.molRep (φ (.inr a)) := by
  obtain ⟨b, hb, hab⟩ := MolMono_molRep_inr Γ₁ a
  rw [hb]
  exact h.molRep_eq b a ((MolMono_molRep_eq_iff Γ₁ b a).2 (Γ₁.sameMol_equivalence.symm hab))

/-- `SelRunIso_rep_map` for the identity map. -/
private theorem SelRunIso_rep_id {k : ℕ} {Γ₁ Γ₂ : Graph k n} (h : Γ₁.MolMono Γ₂ id) (a : Fin n) :
    Γ₂.molRep (Γ₁.molRep (.inr a)) = Γ₂.molRep (.inr a) :=
  SelRunIso_rep_map h a

/-- The pullback along the identity to a graph with the same representatives of the molecules is
the set itself. -/
private theorem SelRunIso_pull_same {k : ℕ} {T g : Graph k n} (h : ∀ u, g.molRep u = T.molRep u)
    {S : Finset (Atom k n)} (hS : S ⊆ g.toMG'.int) : T.molPull g id S = S := by
  have hint : g.toMG'.int = T.toMG'.int := by simp only [Graph.toMG', h]
  ext M
  simp only [Graph.molPull, Finset.mem_filter, id, h]
  constructor
  · rintro ⟨hM, hm⟩
    obtain ⟨-, -, he⟩ := MolMono_of_mem_int T hM
    rwa [he] at hm
  · intro hm
    have hM : M ∈ T.toMG'.int := hint ▸ hS hm
    obtain ⟨-, -, he⟩ := MolMono_of_mem_int T hM
    exact ⟨hM, by rw [he]; exact hm⟩

/-- A component other than a waved or dotted edge replaced by components other than waved and
dotted edges: the molecules are unchanged. -/
private theorem SelRunIso_molRep_replace {k : ℕ} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcj : c.kind.joinsMol = false) (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, d.kind.joinsMol = false) (co : Coeff) (u : Atom k n) :
    (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).molRep u = T.molRep u := by
  have hp := List.getElem_cons_eraseIdx_perm (List.getElem?_eq_some_iff.1 hc).1
  rw [(List.getElem?_eq_some_iff.1 hc).2] at hp
  have hm : (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).molGraph = T.molGraph := by
    unfold Graph.molGraph
    congr 1
    funext a b
    apply propext
    constructor
    · rintro ⟨d, hd, hk, rfl, rfl⟩
      rcases List.mem_append.1 hd with hd | hd
      · exact ⟨d, List.mem_of_mem_eraseIdx hd, hk, rfl, rfl⟩
      · rw [hnew d hd] at hk; cases hk
    · rintro ⟨d, hd, hk, rfl, rfl⟩
      rcases List.mem_cons.1 (hp.symm.subset hd) with rfl | hd'
      · rw [hcj] at hk; cases hk
      · exact ⟨d, List.mem_append_left _ hd', hk, rfl, rfl⟩
  refine SelRunIso_molRep_congr (fun a b => ?_) u
  unfold Graph.SameMol
  rw [hm]

/-- The split term `1_{u = x}` at an atom `u` in a block with an internal atom `a`: a set of
molecules pulled back to `T` that contains the molecule of `x` contains that of `a`. -/
private theorem SelRunIso_split_contra {T : Graph 3 n} {x : Fin n} {u : Atom 3 n} {a : Fin n}
    {Sg : Finset (Atom 3 n)}
    (hTg : T.MolMono (⟨T.comps ++ [mkC .dot u (.inr x)], T.coeff⟩ : Graph 3 n) id)
    (hxT : T.molRep (.inr x) ∈ T.molPull ⟨T.comps ++ [mkC .dot u (.inr x)], T.coeff⟩ id Sg)
    (hnu : T.molRep (T.flatAtom u) ∉
      T.molPull ⟨T.comps ++ [mkC .dot u (.inr x)], T.coeff⟩ id Sg)
    (hfa : T.flatAtom u = .inr a) (hua : T.SameBlock u (.inr a)) : False := by
  set g : Graph 3 n := ⟨T.comps ++ [mkC .dot u (.inr x)], T.coeff⟩ with hg
  have hmono : ∀ v w, T.SameBlock v w → g.SameBlock v w := by
    intro v w h
    refine SimpleGraph.Reachable.mono ?_ h
    intro p q hpq
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hpq ⊢
    refine ⟨hpq.1, ?_⟩
    rcases hpq.2 with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
    · exact Or.inl ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩
    · exact Or.inr ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩
  have hux : g.SameBlock u (.inr x) := by
    by_cases h : u = .inr x
    · rw [h]; exact SimpleGraph.Reachable.refl _
    · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨mkC .dot u (.inr x),
        List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl⟩⟩).reachable
  have hax : g.molRep (.inr a) = g.molRep (.inr x) :=
    SelRunIso_molRep_of_block g ((hmono _ _ hua).symm.trans hux)
  have h1 := (Finset.mem_filter.1 hxT).2
  change g.molRep (T.molRep (.inr x)) ∈ Sg at h1
  rw [SelRunIso_rep_id hTg x, ← hax] at h1
  refine hnu ?_
  rw [hfa]
  refine Finset.mem_filter.2 ⟨MolMono_molRep_mem_int T a, ?_⟩
  change g.molRep (T.molRep (.inr a)) ∈ Sg
  rw [SelRunIso_rep_id hTg a]
  exact h1

/-- Two red crossing edges at `P'` in an isolated set: weakly isolated. -/
private theorem SelRunIso_weak_of_two {k m : ℕ} {G : Graph k m} {P' : Finset (Atom k m)}
    (hiso : G.toMG'.IsIsolated P') (h2 : 2 ≤ G.toMG'.redCount P') : G.toMG'.IsWeaklyIso P' := by
  classical
  refine ⟨hiso, ?_⟩
  unfold MGraph.redCount at h2
  obtain ⟨e, he, e', he', hne⟩ :=
    Finset.one_lt_card.1 (by omega : 1 < (Finset.univ.filter (G.toMG'.RedCrosses P')).card)
  exact ⟨e, e', hne, (Finset.mem_filter.1 he).2, (Finset.mem_filter.1 he').2⟩

/-- **The weak-isolation half of (F6) at a witness step.** Let `Γ` (with `Graph.InvB'`, no
weight or edge of `Γ₀` attached to the block of the internal atom `X`) reach `T` by steps of the
run `selStep1`, let the step from `T` to `g` be the witness `SelRunWit`, and let `φ` be a map from
`g` to a graph `G` that is `Graph.MolMono`. Every proper isolated subset `P'` of the molecular
graph of `G` whose pullback to `Γ` contains the molecule of `X` and no molecule of an atom of a
weight or edge of `Γ₀` is weakly isolated. -/
private theorem SelRunIso_weak_at_wit {m : ℕ} {Γ T g : Graph 3 n} {X : Atom 3 n}
    (hX : X.isRight = true) (hP : Γ.Plain) (hI : Γ.InvB') (hfree : Γ.UnlabelledFreeAtBlock X)
    (h1 : Relation.ReflTransGen (SelStep1CohStep X) Γ T) (h2 : SelStep1CohStep X T g)
    (h3 : SelRunWit X Γ T g) {G : Graph 3 m} {φ : Atom 3 n → Atom 3 m} (hφ : g.MolMono G φ)
    (P' : Finset (Atom 3 m)) (hiso : G.toMG'.IsProperIso G.toMG'.int P')
    (hxP : Γ.molRep X ∈ Γ.molPull G φ P')
    (hcP : ∀ c ∈ Γ.comps, c.label = none → c.kind.isRandom = true → ∀ u ∈ [c.x, c.y],
      Γ.molRep (Γ.flatAtom u) ∉ Γ.molPull G φ P') :
    G.toMG'.IsWeaklyIso P' := by
  obtain ⟨x, rfl⟩ := exists_inr_of_isRight hX
  obtain ⟨hΓT, hIT⟩ := SelRun_chain_molMono hX h1 hI
  have hTg := SelRun_step_molMono hX h2 hIT
  have hIg := qElemStep_invB _ _ (h2.qElemStep hX) hIT
  obtain ⟨c, hcΓ, hl, hr, hblk, hform⟩ := h3
  -- the pullbacks
  set Sg := g.molPull G φ P' with hSg
  set ST := T.molPull g id Sg with hST
  have hpull : Γ.molPull G φ P' = Γ.molPull T id ST := by
    rw [hST, hSg, ← MolMono_molPull_comp hTg hφ, ← MolMono_molPull_comp hΓT (hTg.comp hφ)]
    rfl
  rw [hpull] at hxP hcP
  have hP'I : P' ⊆ G.toMG'.int := hiso.1.1
  have hcg : g.toMG'.cHat Sg ≤ 2 :=
    (hφ.cHat_le P' hP'I).trans (G.toMG'.cHat_le_two_of_isIsolated hiso.1)
  have hrg : g.toMG'.redCount Sg ≤ G.toMG'.redCount P' := hφ.redCount_le P' hP'I
  have hSgI : Sg ⊆ g.toMG'.int := Finset.filter_subset _ _
  have hSTI : ST ⊆ T.toMG'.int := Finset.filter_subset _ _
  -- the molecule of `X` and those of the ends of `c` in `T`
  have hxT : T.molRep (.inr x) ∈ ST := by
    have := (Finset.mem_filter.1 hxP).2
    rwa [id, SelRunIso_rep_id hΓT x] at this
  have hflat := SelRunIso_flatAtom_congr hblk
  have hnot : ∀ u ∈ [c.x, c.y], T.molRep (T.flatAtom u) ∉ ST := by
    intro u hu hmem
    rw [hflat u] at hmem
    rcases hw : Γ.flatAtom u with a | a
    · rw [hw] at hmem
      exact MolMono_inl_not_mem_int T a (hSTI hmem)
    · rw [hw] at hmem
      refine hcP c hcΓ hl hr u hu ?_
      rw [hw]
      refine Finset.mem_filter.2 ⟨MolMono_molRep_mem_int Γ a, ?_⟩
      change T.molRep (Γ.molRep (.inr a)) ∈ ST
      rw [SelRunIso_rep_id hΓT a]
      exact hmem
  have hcT : c ∈ T.comps := by
    rcases hform with ⟨i, ch, hc, -, -⟩ | ⟨hc, -⟩
    · exact List.mem_of_getElem? hc
    · exact hc
  have hcd : c.kind ≠ .dot := fun h => by rw [h] at hr; cases hr
  have hcol : (T.flatAtom c.x).isRight = true ∧ T.flatAtom c.y ≠ .inl 0 := by
    have h := (hIT.2.1 (T.flatComp c) (List.mem_map_of_mem hcT)).1
    simp only [Graph.flatComp, hcd, ite_false] at h
    exact ⟨(h hr).1, (h hr).2.1⟩
  have hxint : T.molRep (T.flatAtom c.x) ∈ T.toMG'.int := by
    rcases hw : T.flatAtom c.x with a | a
    · rw [hw] at hcol; cases hcol.1
    · exact MolMono_molRep_mem_int T a
  have hdc : 2 ≤ T.toMG'.cHat ST := T.toMG'.two_le_cHat_of_DC hIT.1.1 hSTI ⟨_, hxT⟩
    fun h => hnot c.x (by simp) (h hxint)
  have hcx : c.x ≠ .inr x := fun h =>
    (hfree c hcΓ hl hr).1 (by rw [h]; exact SimpleGraph.Reachable.refl _)
  have hcy : c.y ≠ .inr x := fun h =>
    (hfree c hcΓ hl hr).2 (by rw [h]; exact SimpleGraph.Reachable.refl _)
  refine SelRunIso_weak_of_two hiso.1 (le_trans ?_ hrg)
  rcases hform with ⟨i, ch, hc, hk, rfl⟩ | ⟨-, u, hu, rfl⟩
  · -- the second term of [II, (4.17)]
    have hsame : Sg = ST := (SelRunIso_pull_same (fun u => SelRunIso_molRep_replace hc
      (by rcases hk with h | h | h <;> rw [h] <;> rfl) _ (by simp [mkC, Kind.joinsMol]) _ u)
      hSgI).symm
    rw [hsame] at hcg ⊢
    rcases hk with hk | hk
    · have hE := schur_add_two T (.inr x) i c ch T.coeff hc hk hIT rfl ST hSTI hxT
        (hnot c.x (by simp)) (hnot c.y (by simp))
      have hg : (⟨T.comps.eraseIdx i ++ [{ solidC ch c.x (.inr x) with label := c.label },
          { solidC ch (.inr x) c.y with label := c.label },
          { mkC (.inv ch) (.inr x) (.inr x) with label := c.label }], T.coeff⟩ : Graph 3 n) =
          ⟨T.comps.eraseIdx i ++ [mkC (.G ch) c.x (.inr x), mkC (.G ch) (.inr x) c.y,
            mkC (.inv ch) (.inr x) (.inr x)], T.coeff⟩ := by
        simp [solidC, hcx, Ne.symm hcy, hl, mkC]
      rw [hg] at hE
      cases ch
      · have := (hE.1 rfl).2
        omega
      · have := hE.2 rfl
        omega
    · have hyx : c.y = c.x := ((hP c hcΓ).2.2.2.2.1 (by rcases hk with h | h <;> rw [h] <;> rfl))
      have hE := schurW_add_two T (.inr x) i c ch T.coeff hc hk hIT rfl ST hSTI hxT
        (hnot c.x (by simp))
      have hg : (⟨T.comps.eraseIdx i ++ [{ mkC (.G ch) c.x (.inr x) with label := c.label },
          { mkC (.G ch) (.inr x) c.x with label := c.label },
          { mkC (.inv ch) (.inr x) (.inr x) with label := c.label }], T.coeff⟩ : Graph 3 n) =
          ⟨T.comps.eraseIdx i ++ [mkC (.G ch) c.x (.inr x), mkC (.G ch) (.inr x) c.y,
            mkC (.inv ch) (.inr x) (.inr x)], T.coeff⟩ := by
        simp [hl, mkC, hyx]
      rw [hg] at hE
      cases ch
      · have := (hE.1 rfl).2
        omega
      · have := hE.2 rfl
        omega
  · -- the split term `1_{u = x}`
    rcases SelRunIso_flatAtom_spec T u with hfu | ⟨a, hfa, hua⟩
    · rcases u with a | a
      · -- `u` unpinned
        obtain ⟨-, hU⟩ := SelRunIso_flatAtom_inl T hfu
        have hux : (.inl a : Atom 3 n) ≠ c.x := by
          intro h
          rw [← h, hfu] at hcol
          cases hcol.1
        have huy : c.y = .inl a := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with h | h
          · exact absurd h hux
          · exact h.symm
        have hb : a = 1 ∨ a = 2 := by
          have h0 := hcol.2
          rw [huy, hfu] at h0
          fin_cases a
          · exact absurd rfl h0
          · exact Or.inl rfl
          · exact Or.inr rfl
        rw [← huy] at hU
        have hE := Graph.splitUnpinned_add_two T hIT (.inr x) rfl c hcT hl hr a hb huy hU ST
          hSTI hxT (hnot c.x (by simp))
        obtain ⟨hmr, -, -⟩ := SelRunIso_split_struct (X := .inr x) hIT.2.2.1 rfl hcT hr hb huy hU
        rw [huy] at hE hmr
        have hsame : Sg = ST := (SelRunIso_pull_same hmr hSgI).symm
        rw [hsame] at hcg ⊢
        rcases hb with rfl | rfl
        · have := hE.1 rfl
          omega
        · have := hE.2 rfl
          omega
      · -- `u` internal
        exfalso
        exact SelRunIso_split_contra hTg hxT (hnot (.inr a) hu) hfu (SimpleGraph.Reachable.refl _)
    · exfalso
      exact SelRunIso_split_contra hTg hxT (hnot u hu) hfa hua

/-- The weak-isolation half of (F6) along an output `t` of `selStep1` that is not a `Q`-graph,
followed by a map from `t` that is `Graph.MolMono`. -/
private theorem SelRunIso_weak_tail {C n₀ m : ℕ} {x : Fin n₀} {Γ : Graph 3 n₀} (d : ℕ)
    (hN : Γ.Normal C) (hQ : Γ.IsQFormAt (.inr x)) (hP : Γ.Plain) (hI : Γ.InvB')
    (hfree : Γ.UnlabelledFreeAtBlock (.inr x)) {t : Tracked 3 n₀}
    (ht : t ∈ selStep1 d (.inr x) Γ) (hnQ : ¬ t.g.IsQGraphAt (t.f (.inr x))) {G : Graph 3 m}
    {ψ : Atom 3 t.nOut → Atom 3 m} (hψ : t.g.MolMono G ψ) (P' : Finset (Atom 3 m))
    (hiso : G.toMG'.IsProperIso G.toMG'.int P')
    (hxP : Γ.molRep (.inr x) ∈ Γ.molPull G (ψ ∘ t.f) P')
    (hcP : ∀ c ∈ Γ.comps, c.label = none → c.kind.isRandom = true → ∀ u ∈ [c.x, c.y],
      Γ.molRep (Γ.flatAtom u) ∉ Γ.molPull G (ψ ∘ t.f) P') :
    G.toMG'.IsWeaklyIso P' := by
  obtain ⟨T, g, T_f, s₀, g', h1, h2, h3, h4, hm, hdr, rfl⟩ :=
    selStep1_witnessRun d hN hQ hP hfree t ht hnQ
  obtain ⟨-, hIT⟩ := SelRun_chain_molMono rfl h1 hI
  have hIg := qElemStep_invB _ _ (h2.qElemStep rfl) hIT
  have hgt := (SelRun_final_molMono rfl h4 hm hdr hIg).1
  exact SelRunIso_weak_at_wit rfl hP hI hfree h1 h2 h3 (hgt.comp hψ) P' hiso hxP hcP

/-- **The weak-isolation half of (F6) for the family** ([II, Lemma 6.5 (4)] with [II, Def 6.1]
and [II, Lemma 4.15 (iv)]): for `k = 3` and a normal regular graph `Γ = Γ₀ Q_x(Γ̃₀)` (`x`
internal, plain) with the invariant `Graph.InvB'`, such that `Γ₀` has no weight or edge attached
to the block of `x`, every output graph `s` of the family without labels and of scaling order
`≤ D` has the property: every proper isolated subset `P'` of its molecular graph whose pullback
along the atom map `s.f` contains the molecule of `x` and no molecule of an atom of a weight or
edge of `Γ₀` is weakly isolated. -/
theorem selRunFam_weakIso {C D n₀ : ℕ} {x : Fin n₀} {Γ : Graph 3 n₀} (hN : Γ.Normal C)
    (hQ : Γ.IsQFormAt (.inr x)) (hP : Γ.Plain) (hI : Γ.InvB')
    (hfree : Γ.UnlabelledFreeAtBlock (.inr x)) :
    ∀ s ∈ selRunFam D n₀ x Γ, s.g.LabelFree → s.g.ord ≤ D →
      ∀ P' : Finset (Atom 3 s.nOut), s.g.toMG'.IsProperIso s.g.toMG'.int P' →
        Γ.molRep (.inr x) ∈ Γ.molPull s.g s.f P' →
        (∀ c ∈ Γ.comps, c.label = none → c.kind.isRandom = true → ∀ u ∈ [c.x, c.y],
          Γ.molRep (Γ.flatAtom u) ∉ Γ.molPull s.g s.f P') →
        s.g.toMG'.IsWeaklyIso P' := by
  intro s hs hlf hord P' hiso hxP hcP
  obtain ⟨C₁, hB⟩ := SelRun_step1_base D hN hQ hP
  obtain ⟨K₁, C₂, h1⟩ := selStep1_clauses 3 C (selDeg D Γ)
  obtain ⟨t, ht, u, hu, rfl⟩ := SelRun_fam_mem hs
  have hIt : t.g.InvB' := SelRun_invB_of_chain (hB t ht).2.2.2.2.2.2 hI
  rcases SelRun_tail_mem hu with ⟨hnc, rfl⟩ | ⟨⟨hp, hq, hnQ⟩, rfl | hu⟩
  · exfalso
    by_cases hpq : t.g.Plain ∧ t.g.IsQFormAt (t.f (.inr x))
    · have hg : t.g.IsQGraphAt (t.f (.inr x)) := by
        by_contra h
        exact hnc ⟨hpq.1, hpq.2, h⟩
      obtain ⟨c, hc, hcl⟩ := hg.1
      rw [hlf c hc] at hcl
      cases hcl
    · obtain ⟨-, hge⟩ := ((h1 n₀ x Γ _ le_rfl hN hQ hP).2.2 t ht).2.2 hpq
      have := selDeg_add D Γ
      have := SelRun_paperOrd_le t.g
      change t.g.ord ≤ D at hord
      linarith
  · exact SelRunIso_weak_tail _ hN hQ hP hI hfree ht hnQ (molMono_dropLabels t.g) P' hiso hxP hcP
  · obtain ⟨y, hy, hNP, hPP, hpP, hXP, -, -⟩ := SelRun_qp_facts (hB t ht) hp hq
    have hmem : Tracked.self (t.g.qpGraph (t.f (.inr x))) ∈ oQPT (t.f (.inr x)) t.g := by
      rw [oQPT_eq]; simp
    have hIP := qElemStep_invB _ _ (QElemStep.qToP _ t.g _ hq hmem) hIt
    have hψ := (molMono_oQPT _ t.g _ hmem).comp
      (selRounds_molMono D (selDeg D Γ) hNP hPP hpP hXP hIP u (by rw [← hy]; exact hu))
    exact SelRunIso_weak_tail _ hN hQ hP hI hfree ht hnQ hψ P' hiso hxP hcP

end SelRunIsoMain

/-! ## The family of `Q`-expansions -/

/-- **The family `selRunFam` has the clauses `QExpFamilyStmt`** ([II, Lemma 4.15] with the clauses
used in [II, Theorem 3.7]): (F1), (F2), (F5) from `selRunFam_clauses`, (F3) from
`selRunFam_coherent`, (F4) from `selRunFam_pmBlock`, and (F6) from `selRunFam_molMono` and
`selRunFam_weakIso`. -/
theorem selRunFam_qExpFamilyStmt :
    QExpFamilyStmt fun D n₀ x Γ => selRunFam D n₀ x Γ := by
  have hj : ∀ (D n₀ : ℕ) (Γ : Graph 3 n₀),
      (D : ℤ) + 1 ≤ Γ.ord + (((D : ℤ) + 1 - Γ.ord).toNat : ℕ) := by
    intro D n₀ Γ
    have := Int.self_le_toNat ((D : ℤ) + 1 - Γ.ord)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro D n₀ x Γ ⟨C, hN⟩ hQ hP
    obtain ⟨K, C', h⟩ := selRunFam_clauses C _ D
    obtain ⟨-, hv, ho⟩ := h n₀ x Γ hN hQ hP (hj D n₀ Γ)
    exact ⟨hv, ⟨C', fun t ht => (ho t ht).1⟩,
      fun hI t ht => qExpansionOut_invB D C' n₀ x Γ t (ho t ht).1.1 hI⟩
  · intro C j D
    obtain ⟨K, C', h⟩ := selRunFam_clauses C j D
    exact ⟨K, C', fun n₀ x Γ hN hQ hP hD =>
      ⟨(h n₀ x Γ hN hQ hP hD).1, fun t ht => ((h n₀ x Γ hN hQ hP hD).2.2 t ht).1⟩⟩
  · rintro D D' n₀ x Γ hDD ⟨C, hN⟩ hQ hP P hPD
    exact selRunFam_coherent hDD hN hQ hP P hPD
  · rintro D n₀ x Γ ⟨C, hN⟩ hQ hP - hn
    exact selRunFam_pmBlock hN hQ hP hn
  · rintro D n₀ x Γ ⟨C, hN⟩ hQ hP t ht hnp
    obtain ⟨K, C', h⟩ := selRunFam_clauses C _ D
    obtain ⟨⟨⟨hB, -⟩, -⟩, h5⟩ := (h n₀ x Γ hN hQ hP (hj D n₀ Γ)).2.2 t ht
    exact ⟨⟨C', hB.1⟩, hB.2.2.1, (h5 hnp).1, (h5 hnp).2⟩
  · rintro D n₀ x Γ ⟨C, hN⟩ hQ hP - hI s hs
    exact ⟨selRunFam_molMono hN hQ hP hI s hs,
      fun hfree => selRunFam_weakIso hN hQ hP hI hfree s hs⟩

/-- **A family of `Q`-expansions with the clauses `QExpFamilyStmt` exists**: the family
`selRunFam` of [II, Lemma 4.15] with deterministic choices. -/
theorem exists_qExpFamilyStmt :
    ∃ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 :=
  ⟨_, selRunFam_qExpFamilyStmt⟩

/-! ## Decidability instances for concrete graphs -/

section SelRunIsoInstances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance SelRunIso_decAdjDot {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

private instance SelRunIso_decSameBlock {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameBlock :=
  fun u v => @SimpleGraph.instDecidableRelReachable _ _ _ _ (SelRunIso_decAdjDot Γ) u v

private instance SelRunIso_decAdjMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.molGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = v ∧ c.y = u))))

private instance SelRunIso_decSameMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameMol :=
  fun u v =>
    haveI : Decidable (Γ.molGraph.Reachable u v) :=
      @SimpleGraph.instDecidableRelReachable _ _ _ _ (SelRunIso_decAdjMol Γ) u v
    inferInstanceAs (Decidable (u = v ∨
      (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)))

private instance SelRunIso_decIsQGraph {k n : ℕ} (Γ : Graph k n) : Decidable Γ.IsQGraph :=
  inferInstanceAs (Decidable (∃ u : Atom k n, (∃ c ∈ Γ.comps, c.label = some (.Q, u)) ∧
    ∀ c ∈ Γ.comps, (c.kind.isRandom = true ∨ c.label.isSome = true) → c.label = some (.Q, u)))

private instance SelRunIso_decIsQFormAt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.IsQFormAt u) := by
  unfold Graph.IsQFormAt; infer_instance

private instance SelRunIso_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

private instance SelRunIso_decColourInv' {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.ColourInv' := by
  unfold Graph.ColourInv'; infer_instance

private instance SelRunIso_decColourInvB {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.ColourInvB := by
  unfold Graph.ColourInvB; infer_instance

private instance SelRunIso_decExtClause {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.ExtClause := by
  unfold Graph.ExtClause Graph.HasDiffToPinned Graph.DiffToPinned; infer_instance

private instance SelRunIso_decNoGhost {k n : ℕ} (Γ : Graph k n) : Decidable Γ.NoGhost := by
  unfold Graph.NoGhost; infer_instance

private instance SelRunIso_decLabelsInt {k n : ℕ} (Γ : Graph k n) : Decidable Γ.LabelsInt := by
  unfold Graph.LabelsInt; infer_instance

private instance SelRunIso_decUnlabelledFreeAtBlock {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.UnlabelledFreeAtBlock u) := by
  unfold Graph.UnlabelledFreeAtBlock; infer_instance

section Helpers

variable {V E : Type}

end Helpers

end SelRunIsoInstances

end RBM8D.Graphs
