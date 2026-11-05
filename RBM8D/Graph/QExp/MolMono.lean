import RBM8D.Graph.MolRead

/-!
# Crossing counts along the block-preserving steps of the `Q`-expansions

Crossing counts of subsets of molecules in the molecular graph of [II, Def 2.11] (block reading,
`Graph.toMG'`): the number `MGraph.crossCount` of crossing edges without red solid edges
([II, Def 5.2]), the number `MGraph.redCount` of red crossing edges ([II, Def 6.1]), and the
count `MGraph.cHat` in which each external vertex is counted at most once. A map of the atoms
between two graphs is `Graph.MolMono` when it sends molecules into molecules, onto the internal
molecules, and the pullback of every set of internal molecules has `MGraph.cHat` and
`MGraph.redCount` at most those of the set. This is the fact behind [II, Lemma 6.5 (4)] that the
steps of the `Q`-expansions of [II, §4.4] create no new molecule and keep or subdivide the edges
between molecules. It is proved here for the steps that keep the blocks: [II, (4.17), (4.20)] at
a solid edge or a weight, [II, (4.21)], `O^{(x),1}_weight`, the `×`-dotted terms of
`1 = 1_{u = v} + 1_{u ≠ v}`, `1_{u ≠ v} = 1 - 1_{u = v}` and `O_dot`, `Q_u = 1 - P_u`, the moves
of factors into or out of a label group, the removal of a redundant dotted edge and the move of
an end inside a block. With the path `G_{ux} G_{xv}` of
[II, Lemma 4.11] a set containing the molecule of `x` and not those of `u`, `v` gains two
crossing edges of the colour of `G_{uv}`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Crossing counts of a molecular multigraph -/

section Counts

variable {V E : Type} [DecidableEq V] [Fintype E]

/-- The number of edges joining `S` to its complement in the molecular graph without red solid
edges (`MGraph.Crosses`, [II, Def 5.2]). -/
def MGraph.crossCount (G : MGraph V E) (S : Finset V) : ℕ :=
  (Finset.univ.filter (G.Crosses S)).card

/-- The number of red solid edges between `S` and its complement (`MGraph.RedCrosses`,
[II, Def 6.1]). -/
def MGraph.redCount (G : MGraph V E) (S : Finset V) : ℕ :=
  (Finset.univ.filter (G.RedCrosses S)).card

/-- The edges of `MGraph.Crosses` at `S` with both ends internal. -/
def MolMono_cInt (G : MGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter fun e => G.Crosses S e ∧ (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int

/-- The vertices that are external and not internal and are an end of an edge of
`MGraph.Crosses` at `S`. -/
def MolMono_tExt (G : MGraph V E) (S : Finset V) : Finset V :=
  (G.ext \ G.int).filter fun a => ∃ e, G.Crosses S e ∧ ((G.ends e).1 = a ∨ (G.ends e).2 = a)

/-- The crossing count of `S` with each external vertex counted at most once: the crossing edges
between two internal vertices, plus the external vertices reached by a crossing edge. -/
def MGraph.cHat (G : MGraph V E) (S : Finset V) : ℕ :=
  (MolMono_cInt G S).card + (MolMono_tExt G S).card

/-- Membership in `MolMono_cInt`. -/
theorem MolMono_mem_cInt (G : MGraph V E) (S : Finset V) (e : E) :
    e ∈ MolMono_cInt G S ↔ G.Crosses S e ∧ (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int := by
  simp [MolMono_cInt]

/-- Membership in `MolMono_tExt`. -/
theorem MolMono_mem_tExt (G : MGraph V E) (S : Finset V) (a : V) :
    a ∈ MolMono_tExt G S ↔ (a ∈ G.ext ∧ a ∉ G.int) ∧
      ∃ e, G.Crosses S e ∧ ((G.ends e).1 = a ∨ (G.ends e).2 = a) := by
  simp [MolMono_tExt]

/-- For a set of internal vertices, `MGraph.cHat` is at most the crossing count. -/
theorem MGraph.cHat_le_crossCount (G : MGraph V E) {S : Finset V} (hS : S ⊆ G.int) :
    G.cHat S ≤ G.crossCount S := by
  unfold MGraph.cHat MGraph.crossCount
  set C := Finset.univ.filter (G.Crosses S)
  have h1 : MolMono_cInt G S =
      C.filter (fun e => (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int) := by
    ext e
    simp [MolMono_cInt, C]
  have h2 : (MolMono_tExt G S).card ≤
      (C.filter fun e => ¬ ((G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int)).card := by
    classical
    rcases (MolMono_tExt G S).eq_empty_or_nonempty with hT | ⟨a₀, ha₀⟩
    · rw [hT]; simp
    obtain ⟨-, e₀, -⟩ := (MolMono_mem_tExt G S a₀).1 ha₀
    let f : V → E := fun a =>
      if h : ∃ e, G.Crosses S e ∧ ((G.ends e).1 = a ∨ (G.ends e).2 = a) then h.choose else e₀
    have hf : ∀ a ∈ MolMono_tExt G S,
        G.Crosses S (f a) ∧ ((G.ends (f a)).1 = a ∨ (G.ends (f a)).2 = a) := by
      intro a ha
      have h := ((MolMono_mem_tExt G S a).1 ha).2
      simp only [f, h, ↓reduceDIte]
      exact h.choose_spec
    refine Finset.card_le_card_of_injOn f (fun a ha => ?_) (fun a ha b hb hab => ?_)
    · obtain ⟨⟨-, hai⟩, -⟩ := (MolMono_mem_tExt G S a).1 ha
      obtain ⟨he, hea⟩ := hf a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, C]
      refine ⟨he, fun hh => hai ?_⟩
      rcases hea with h | h
      · exact h ▸ hh.1
      · exact h ▸ hh.2
    · have ha' : a ∈ MolMono_tExt G S := ha
      have hb' : b ∈ MolMono_tExt G S := hb
      obtain ⟨⟨-, hai⟩, -⟩ := (MolMono_mem_tExt G S a).1 ha'
      obtain ⟨⟨-, hbi⟩, -⟩ := (MolMono_mem_tExt G S b).1 hb'
      obtain ⟨he, hea⟩ := hf a ha'
      obtain ⟨-, heb⟩ := hf b hb'
      rw [hab] at he hea
      have hcut := he.2.2.2.2
      have haS : a ∉ S := fun h => hai (hS h)
      have hbS : b ∉ S := fun h => hbi (hS h)
      rcases hea with h₁ | h₁ <;> rcases heb with h₂ | h₂
      · exact h₁.symm.trans h₂
      · rcases hcut with hc | hc
        · exact absurd (h₁ ▸ hc.1) haS
        · exact absurd (h₂ ▸ hc.2) hbS
      · rcases hcut with hc | hc
        · exact absurd (h₂ ▸ hc.1) hbS
        · exact absurd (h₁ ▸ hc.2) haS
      · exact h₁.symm.trans h₂
  rw [h1]
  calc _ ≤ _ := Nat.add_le_add_left h2 _
    _ = C.card := Finset.card_filter_add_card_filter_not _

/-- The black and the blue net of a doubly connected graph each give a crossing edge between
two internal vertices for every proper nonempty set of internal vertices. -/
private theorem MolMono_dc_pair (G : MGraph V E) (hG : G.DC) {S : Finset V} (hS : S ⊆ G.int)
    (hne : S.Nonempty) (hns : ¬ G.int ⊆ S) :
    ∃ e₁ e₂, e₁ ≠ e₂ ∧ e₁ ∈ MolMono_cInt G S ∧ e₂ ∈ MolMono_cInt G S := by
  obtain ⟨bl, bu, hd, hbl, hbu, hsb, hsu⟩ := hG
  obtain ⟨e₁, he₁, hc₁, hi₁, hj₁, hcut₁⟩ := hsb S hS hne hns
  obtain ⟨e₂, he₂, hc₂, hi₂, hj₂, hcut₂⟩ := hsu S hS hne hns
  refine ⟨e₁, e₂, fun h => Finset.disjoint_left.1 hd he₁ (h ▸ he₂), ?_, ?_⟩
  · rw [MolMono_mem_cInt]
    exact ⟨⟨hc₁, by rw [hbl e₁ he₁]; simp, Or.inl hi₁, Or.inl hj₁, hcut₁⟩, hi₁, hj₁⟩
  · rw [MolMono_mem_cInt]
    refine ⟨⟨hc₂, ?_, Or.inl hi₂, Or.inl hj₂, hcut₂⟩, hi₂, hj₂⟩
    rcases hbu e₂ he₂ with h | h | h <;> rw [h] <;> simp

/-- In a doubly connected graph every proper nonempty set of internal vertices has
`MGraph.cHat` at least `2`. -/
theorem MGraph.two_le_cHat_of_DC (G : MGraph V E) (hG : G.DC) {S : Finset V}
    (hS : S ⊆ G.int) (hne : S.Nonempty) (hns : ¬ G.int ⊆ S) : 2 ≤ G.cHat S := by
  classical
  obtain ⟨e₁, e₂, hne', h₁, h₂⟩ := MolMono_dc_pair G hG hS hne hns
  have : ({e₁, e₂} : Finset E) ⊆ MolMono_cInt G S := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact h₁
    · rw [Finset.mem_singleton.1 he]; exact h₂
  have := Finset.card_le_card this
  rw [Finset.card_pair hne'] at this
  unfold MGraph.cHat
  omega

/-- An isolated subset ([II, Def 5.2]) has exactly two crossing edges. -/
private theorem MolMono_crossCount_of_isIsolated (G : MGraph V E) {P : Finset V}
    (h : G.IsIsolated P) : G.crossCount P = 2 := by
  classical
  obtain ⟨-, e₁, e₂, hne, hc⟩ := h
  have : Finset.univ.filter (G.Crosses P) = {e₁, e₂} := by
    ext e
    simp [hc]
  unfold MGraph.crossCount
  rw [this, Finset.card_pair hne]

/-- An isolated subset has `MGraph.cHat` at most `2`. -/
theorem MGraph.cHat_le_two_of_isIsolated (G : MGraph V E) {P : Finset V}
    (h : G.IsIsolated P) : G.cHat P ≤ 2 :=
  (G.cHat_le_crossCount h.1).trans (MolMono_crossCount_of_isIsolated G h).le

end Counts

/-! ## Representatives of molecules -/

section MolRep

variable {k n : ℕ}

open Classical in
/-- `Graph.molRep` at an internal atom, with any decision procedure. -/
theorem MolMono_molRep_eq_find (Γ : Graph k n) (a : Fin n) :
    Γ.molRep (.inr a) = .inr (((List.finRange n).find? fun b =>
      decide (Γ.SameMol (.inr a) (.inr b))).getD a) := by
  simp only [Graph.molRep]

open Classical in
/-- `Graph.anchor`, with any decision procedure. -/
theorem MolMono_anchor_eq_find (Γ : Graph k n) (u : Atom k n) :
    Γ.anchor u = (List.finRange n).find? fun b => decide (Γ.SameBlock u (.inr b)) := by
  simp only [Graph.anchor]

/-- The representative of the molecule of an internal atom is an internal atom of that
molecule. -/
theorem MolMono_molRep_inr (Γ : Graph k n) (a : Fin n) :
    ∃ b, Γ.molRep (.inr a) = .inr b ∧ Γ.SameMol (.inr a) (.inr b) := by
  classical
  rw [MolMono_molRep_eq_find]
  refine ⟨_, rfl, ?_⟩
  cases h : (List.finRange n).find? fun b => decide (Γ.SameMol (.inr a) (.inr b)) with
  | none => exact Or.inl rfl
  | some b => simpa using List.find?_some h

/-- Two internal atoms have the same representative exactly when they lie in one molecule. -/
theorem MolMono_molRep_eq_iff (Γ : Graph k n) (a b : Fin n) :
    Γ.molRep (.inr a) = Γ.molRep (.inr b) ↔ Γ.SameMol (.inr a) (.inr b) := by
  have E := Γ.sameMol_equivalence
  constructor
  · intro h
    obtain ⟨c, hc, hac⟩ := MolMono_molRep_inr Γ a
    obtain ⟨d, hd, hbd⟩ := MolMono_molRep_inr Γ b
    rw [hc, hd] at h
    cases h
    exact E.trans hac (E.symm hbd)
  · intro h
    classical
    rw [MolMono_molRep_eq_find, MolMono_molRep_eq_find]
    have hp : (fun c => decide (Γ.SameMol (.inr a) (.inr c))) =
        (fun c => decide (Γ.SameMol (.inr b) (.inr c))) := by
      funext c
      exact decide_eq_decide.2 ⟨fun h' => E.trans (E.symm h) h', fun h' => E.trans h h'⟩
    rw [hp]
    cases hf : (List.finRange n).find? fun c => decide (Γ.SameMol (.inr b) (.inr c)) with
    | some c => rfl
    | none =>
      exfalso
      have := List.find?_eq_none.1 hf b (List.mem_finRange b)
      simp only [decide_eq_true_eq] at this
      exact this (Or.inl rfl)

/-- The representative of the molecule of an atom represents its own molecule. -/
theorem MolMono_molRep_idem (Γ : Graph k n) (u : Atom k n) :
    Γ.molRep (Γ.molRep u) = Γ.molRep u := by
  rcases u with a | a
  · rfl
  · obtain ⟨b, hb, hab⟩ := MolMono_molRep_inr Γ a
    calc Γ.molRep (Γ.molRep (.inr a)) = Γ.molRep (.inr b) := by rw [hb]
      _ = Γ.molRep (.inr a) :=
        (MolMono_molRep_eq_iff Γ b a).2 (Γ.sameMol_equivalence.symm hab)

/-- The internal vertices of `Graph.toMG'` are the representatives of the molecules of the
internal atoms. -/
theorem MolMono_mem_int (Γ : Graph k n) (M : Atom k n) :
    M ∈ Γ.toMG'.int ↔ ∃ a : Fin n, Γ.molRep (.inr a) = M := by
  simp [Graph.toMG']

/-- The external vertices of `Graph.toMG'` are the external atoms. -/
theorem MolMono_mem_ext (Γ : Graph k n) (M : Atom k n) :
    M ∈ Γ.toMG'.ext ↔ ∃ a : Fin k, M = .inl a := by
  simp [Graph.toMG', eq_comm]

/-- The representative of the molecule of an internal atom is an internal vertex. -/
theorem MolMono_molRep_mem_int (Γ : Graph k n) (a : Fin n) :
    Γ.molRep (.inr a) ∈ Γ.toMG'.int :=
  (MolMono_mem_int Γ _).2 ⟨a, rfl⟩

/-- A vertex of `Graph.toMG'` that is internal is an internal atom representing its molecule. -/
theorem MolMono_of_mem_int (Γ : Graph k n) {M : Atom k n} (h : M ∈ Γ.toMG'.int) :
    ∃ b : Fin n, M = .inr b ∧ Γ.molRep M = M := by
  obtain ⟨a, rfl⟩ := (MolMono_mem_int Γ M).1 h
  obtain ⟨b, hb, -⟩ := MolMono_molRep_inr Γ a
  exact ⟨b, hb, MolMono_molRep_idem Γ _⟩

/-- The representative of an atom is a vertex of `Graph.toMG'`. -/
theorem MolMono_molRep_isVtx (Γ : Graph k n) (u : Atom k n) :
    Γ.toMG'.IsVtx (Γ.molRep u) := by
  rcases u with a | a
  · exact Or.inr ((MolMono_mem_ext Γ _).2 ⟨a, rfl⟩)
  · exact Or.inl (MolMono_molRep_mem_int Γ a)

/-- An external atom is not an internal vertex of `Graph.toMG'`. -/
theorem MolMono_inl_not_mem_int (Γ : Graph k n) (a : Fin k) :
    (.inl a : Atom k n) ∉ Γ.toMG'.int := by
  intro h
  obtain ⟨b, hb, -⟩ := MolMono_of_mem_int Γ h
  cases hb

end MolRep

/-! ## Maps of molecules that do not lower the crossing counts -/

section MolMonoDef

variable {k n m l : ℕ}

/-- The pullback of a set `S₂` of vertices of `Graph.toMG'` of `Γ₂` along the atom map `φ`: the
internal molecules of `Γ₁` whose image under `φ` lies in a molecule of `S₂`. -/
def Graph.molPull (Γ₁ : Graph k n) (Γ₂ : Graph k m) (φ : Atom k n → Atom k m)
    (S₂ : Finset (Atom k m)) : Finset (Atom k n) :=
  Γ₁.toMG'.int.filter fun M => Γ₂.molRep (φ M) ∈ S₂

/-- The atom map `φ` from `Γ₁` to `Γ₂` keeps the molecular graphs of the block reading
(`Graph.toMG'`) from losing crossings: internal atoms go to internal atoms, atoms of one molecule
go into one molecule, every internal molecule of `Γ₂` is hit, and for every set `S₂` of internal
molecules of `Γ₂` the pullback `Graph.molPull` has `MGraph.cHat` and `MGraph.redCount` at most
those of `S₂`. -/
structure Graph.MolMono (Γ₁ : Graph k n) (Γ₂ : Graph k m) (φ : Atom k n → Atom k m) : Prop where
  isRight : ∀ a : Fin n, (φ (.inr a)).isRight = true
  molRep_eq : ∀ a b : Fin n, Γ₁.molRep (.inr a) = Γ₁.molRep (.inr b) →
    Γ₂.molRep (φ (.inr a)) = Γ₂.molRep (φ (.inr b))
  onto : ∀ v ∈ Γ₂.toMG'.int, ∃ a : Fin n, Γ₂.molRep (φ (.inr a)) = v
  cHat_le : ∀ S₂ ⊆ Γ₂.toMG'.int,
    Γ₁.toMG'.cHat (Γ₁.molPull Γ₂ φ S₂) ≤ Γ₂.toMG'.cHat S₂
  redCount_le : ∀ S₂ ⊆ Γ₂.toMG'.int,
    Γ₁.toMG'.redCount (Γ₁.molPull Γ₂ φ S₂) ≤ Γ₂.toMG'.redCount S₂

/-- The pullback along the identity of a set of internal molecules is the set itself. -/
private theorem MolMono_molPull_id (Γ : Graph k n) {S : Finset (Atom k n)} (hS : S ⊆ Γ.toMG'.int) :
    Γ.molPull Γ id S = S := by
  ext M
  simp only [Graph.molPull, Finset.mem_filter, id]
  constructor
  · rintro ⟨hM, h⟩
    obtain ⟨-, -, he⟩ := MolMono_of_mem_int Γ hM
    rwa [he] at h
  · intro h
    obtain ⟨-, -, he⟩ := MolMono_of_mem_int Γ (hS h)
    exact ⟨hS h, by rw [he]; exact h⟩

/-- The identity map. -/
theorem Graph.MolMono.refl (Γ : Graph k n) : Γ.MolMono Γ id where
  isRight _ := rfl
  molRep_eq _ _ h := h
  onto v hv := (MolMono_mem_int Γ v).1 hv
  cHat_le S hS := by rw [MolMono_molPull_id Γ hS]
  redCount_le S hS := by rw [MolMono_molPull_id Γ hS]

/-- The image of the representative of the molecule of an internal atom lies in the molecule of
the image of the atom. -/
private theorem MolMono_rep_map {Γ₁ : Graph k n} {Γ₂ : Graph k m} {φ : Atom k n → Atom k m}
    (h : Γ₁.MolMono Γ₂ φ) (a : Fin n) :
    Γ₂.molRep (φ (Γ₁.molRep (.inr a))) = Γ₂.molRep (φ (.inr a)) := by
  obtain ⟨b, hb, hab⟩ := MolMono_molRep_inr Γ₁ a
  rw [hb]
  exact h.molRep_eq b a ((MolMono_molRep_eq_iff Γ₁ b a).2 (Γ₁.sameMol_equivalence.symm hab))

/-- The image of the representative of the molecule of an internal atom, as an atom of the
second graph. -/
private theorem MolMono_rep_map' {Γ₁ : Graph k n} {Γ₂ : Graph k m} {φ : Atom k n → Atom k m}
    (h : Γ₁.MolMono Γ₂ φ) {u : Atom k n} (hu : u.isRight = true) :
    Γ₂.molRep (φ (Γ₁.molRep u)) = Γ₂.molRep (φ u) := by
  rcases u with a | a
  · cases hu
  · exact MolMono_rep_map h a

/-- The pullback along a composition is the composition of the pullbacks. -/
theorem MolMono_molPull_comp {Γ₁ : Graph k n} {Γ₂ : Graph k m} {Γ₃ : Graph k l}
    {φ : Atom k n → Atom k m} {ψ : Atom k m → Atom k l} (h₁ : Γ₁.MolMono Γ₂ φ)
    (h₂ : Γ₂.MolMono Γ₃ ψ) (S₃ : Finset (Atom k l)) :
    Γ₁.molPull Γ₃ (ψ ∘ φ) S₃ = Γ₁.molPull Γ₂ φ (Γ₂.molPull Γ₃ ψ S₃) := by
  ext M
  simp only [Graph.molPull, Finset.mem_filter, Function.comp]
  constructor
  · rintro ⟨hM, h⟩
    obtain ⟨b, rfl, -⟩ := MolMono_of_mem_int Γ₁ hM
    obtain ⟨c, hc⟩ : ∃ c, φ (.inr b) = .inr c := by
      have := h₁.isRight b
      revert this
      cases φ (.inr b) with
      | inl _ => intro h; cases h
      | inr c => intro _; exact ⟨c, rfl⟩
    refine ⟨hM, ?_, ?_⟩
    · rw [hc]; exact MolMono_molRep_mem_int Γ₂ c
    · rw [hc, MolMono_rep_map h₂ c, ← hc]; exact h
  · rintro ⟨hM, -, h⟩
    obtain ⟨b, rfl, -⟩ := MolMono_of_mem_int Γ₁ hM
    refine ⟨hM, ?_⟩
    rwa [MolMono_rep_map' h₂ (h₁.isRight b)] at h

/-- Composition, in the order of `TExpansion.bind`. -/
theorem Graph.MolMono.comp {Γ₁ : Graph k n} {Γ₂ : Graph k m} {Γ₃ : Graph k l}
    {φ : Atom k n → Atom k m} {ψ : Atom k m → Atom k l} (h₁ : Γ₁.MolMono Γ₂ φ)
    (h₂ : Γ₂.MolMono Γ₃ ψ) : Γ₁.MolMono Γ₃ (ψ ∘ φ) where
  isRight a := by
    have := h₁.isRight a
    simp only [Function.comp]
    revert this
    cases φ (.inr a) with
    | inl _ => intro h; cases h
    | inr c => intro _; exact h₂.isRight c
  molRep_eq a b h := by
    have h' := h₁.molRep_eq a b h
    simp only [Function.comp]
    rw [← MolMono_rep_map' h₂ (h₁.isRight a), ← MolMono_rep_map' h₂ (h₁.isRight b), h']
  onto v hv := by
    obtain ⟨c, hc⟩ := h₂.onto v hv
    obtain ⟨a, ha⟩ := h₁.onto _ (MolMono_molRep_mem_int Γ₂ c)
    refine ⟨a, ?_⟩
    simp only [Function.comp]
    rw [← MolMono_rep_map' h₂ (h₁.isRight a), ha, MolMono_rep_map h₂ c, hc]
  cHat_le S₃ hS₃ := by
    rw [MolMono_molPull_comp h₁ h₂]
    exact (h₁.cHat_le _ (Finset.filter_subset _ _)).trans (h₂.cHat_le S₃ hS₃)
  redCount_le S₃ hS₃ := by
    rw [MolMono_molPull_comp h₁ h₂]
    exact (h₁.redCount_le _ (Finset.filter_subset _ _)).trans (h₂.redCount_le S₃ hS₃)

/-- The pullback of a nonempty set of internal molecules is nonempty. -/
theorem Graph.MolMono.molPull_nonempty {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {φ : Atom k n → Atom k m} (h : Γ₁.MolMono Γ₂ φ) {S₂ : Finset (Atom k m)}
    (hS : S₂ ⊆ Γ₂.toMG'.int) (hne : S₂.Nonempty) : (Γ₁.molPull Γ₂ φ S₂).Nonempty := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨a, ha⟩ := h.onto v (hS hv)
  refine ⟨Γ₁.molRep (.inr a), Finset.mem_filter.2 ⟨MolMono_molRep_mem_int Γ₁ a, ?_⟩⟩
  rw [MolMono_rep_map h a, ha]
  exact hv

/-- The pullback of a set missing an internal molecule misses an internal molecule. -/
theorem Graph.MolMono.molPull_not_superset {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {φ : Atom k n → Atom k m} (h : Γ₁.MolMono Γ₂ φ) {S₂ : Finset (Atom k m)}
    (_hS : S₂ ⊆ Γ₂.toMG'.int) (hns : ¬ Γ₂.toMG'.int ⊆ S₂) :
    ¬ Γ₁.toMG'.int ⊆ Γ₁.molPull Γ₂ φ S₂ := by
  obtain ⟨v, hv, hvS⟩ := Finset.not_subset.1 hns
  obtain ⟨a, ha⟩ := h.onto v hv
  intro hsub
  have := (Finset.mem_filter.1 (hsub (MolMono_molRep_mem_int Γ₁ a))).2
  rw [MolMono_rep_map h a, ha] at this
  exact hvS this

/-- Proper isolated subsets pull back to proper isolated subsets, with at least as many red
crossing edges, when the first molecular graph is doubly connected. -/
private theorem MolMono_pull_properIso_of_DC {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {φ : Atom k n → Atom k m} (h : Γ₁.MolMono Γ₂ φ) (hdc : Γ₁.toMG'.DC)
    {P₂ : Finset (Atom k m)} (hP : Γ₂.toMG'.IsProperIso Γ₂.toMG'.int P₂) :
    Γ₁.toMG'.IsProperIso Γ₁.toMG'.int (Γ₁.molPull Γ₂ φ P₂) ∧
      Γ₁.toMG'.redCount (Γ₁.molPull Γ₂ φ P₂) ≤ Γ₂.toMG'.redCount P₂ := by
  obtain ⟨hiso, hlt⟩ := hP
  have hP₂ : P₂ ⊆ Γ₂.toMG'.int := hiso.1
  have hns₂ : ¬ Γ₂.toMG'.int ⊆ P₂ := fun h' =>
    (Finset.ssubset_iff_subset_ne.1 hlt).2 (Finset.Subset.antisymm hP₂ h')
  have hne₂ : P₂.Nonempty := by
    obtain ⟨-, e₁, e₂, -, hc⟩ := hiso
    obtain ⟨-, -, -, -, hcut⟩ := (hc e₁).2 (Or.inl rfl)
    rcases hcut with h' | h'
    · exact ⟨_, h'.1⟩
    · exact ⟨_, h'.2⟩
  set Q := Γ₁.molPull Γ₂ φ P₂
  have hQi : Q ⊆ Γ₁.toMG'.int := Finset.filter_subset _ _
  have hQne := h.molPull_nonempty hP₂ hne₂
  have hQns := h.molPull_not_superset hP₂ hns₂
  obtain ⟨b₁, b₂, hb, hb₁, hb₂⟩ := MolMono_dc_pair _ hdc hQi hQne hQns
  have hle : Γ₁.toMG'.cHat Q ≤ 2 :=
    (h.cHat_le P₂ hP₂).trans (Γ₂.toMG'.cHat_le_two_of_isIsolated hiso)
  have hpair : ({b₁, b₂} : Finset _) ⊆ MolMono_cInt Γ₁.toMG' Q := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hb₁
    · rw [Finset.mem_singleton.1 he]; exact hb₂
  have hcard := Finset.card_le_card hpair
  rw [Finset.card_pair hb] at hcard
  have hT : MolMono_tExt Γ₁.toMG' Q = ∅ := by
    apply Finset.card_eq_zero.1
    unfold MGraph.cHat at hle
    omega
  have hC : MolMono_cInt Γ₁.toMG' Q = {b₁, b₂} := by
    refine (Finset.eq_of_subset_of_card_le hpair ?_).symm
    rw [Finset.card_pair hb]
    unfold MGraph.cHat at hle
    omega
  refine ⟨⟨⟨hQi, b₁, b₂, hb, fun e => ⟨fun he => ?_, fun he => ?_⟩⟩,
    Finset.ssubset_iff_subset_ne.2 ⟨hQi, fun heq => hQns (heq ▸ subset_refl _)⟩⟩,
    h.redCount_le P₂ hP₂⟩
  · by_cases hint : (Γ₁.toMG'.ends e).1 ∈ Γ₁.toMG'.int ∧ (Γ₁.toMG'.ends e).2 ∈ Γ₁.toMG'.int
    · have : e ∈ MolMono_cInt Γ₁.toMG' Q := (MolMono_mem_cInt _ _ _).2 ⟨he, hint⟩
      rw [hC] at this
      simpa using this
    · exfalso
      have hv1 := he.2.2.1
      have hv2 := he.2.2.2.1
      have key : ∀ a, a ∈ Γ₁.toMG'.ext → a ∉ Γ₁.toMG'.int →
          ((Γ₁.toMG'.ends e).1 = a ∨ (Γ₁.toMG'.ends e).2 = a) → False := by
        intro a ha hai hea
        have : a ∈ MolMono_tExt Γ₁.toMG' Q := (MolMono_mem_tExt _ _ _).2 ⟨⟨ha, hai⟩, e, he, hea⟩
        rw [hT] at this
        exact Finset.notMem_empty _ this
      by_cases h1 : (Γ₁.toMG'.ends e).1 ∈ Γ₁.toMG'.int
      · have h2 : (Γ₁.toMG'.ends e).2 ∉ Γ₁.toMG'.int := fun h2 => hint ⟨h1, h2⟩
        exact key _ (hv2.resolve_left h2) h2 (Or.inr rfl)
      · exact key _ (hv1.resolve_left h1) h1 (Or.inl rfl)
  · have : e ∈ MolMono_cInt Γ₁.toMG' Q := by
      rw [hC]; rcases he with rfl | rfl <;> simp
    exact ((MolMono_mem_cInt _ _ _).1 this).1

end MolMonoDef

/-! ## The edges of a molecular multigraph as a list of triples -/

section Triples

variable {V : Type} [DecidableEq V]

/-- A present edge, given by its two ends and its class, joins `S` to its complement without
being a red solid edge (`MGraph.Crosses`), for the internal vertices `I` and the external
vertices `X`. -/
abbrev MolMono_crossT (I X S : Finset V) (t : V × V × MClass) : Prop :=
  t.2.2 ≠ .minus ∧ (t.1 ∈ I ∨ t.1 ∈ X) ∧ (t.2.1 ∈ I ∨ t.2.1 ∈ X) ∧
    ((t.1 ∈ S ∧ t.2.1 ∉ S) ∨ (t.1 ∉ S ∧ t.2.1 ∈ S))

/-- A present edge is a red solid edge between `S` and its complement (`MGraph.RedCrosses`). -/
abbrev MolMono_redT (I X S : Finset V) (t : V × V × MClass) : Prop :=
  t.2.2 = .minus ∧ (t.1 ∈ I ∨ t.1 ∈ X) ∧ (t.2.1 ∈ I ∨ t.2.1 ∈ X) ∧
    ((t.1 ∈ S ∧ t.2.1 ∉ S) ∨ (t.1 ∉ S ∧ t.2.1 ∈ S))

/-- A present edge of `MolMono_crossT` with both ends internal. -/
abbrev MolMono_intT (I X S : Finset V) (t : V × V × MClass) : Prop :=
  MolMono_crossT I X S t ∧ t.1 ∈ I ∧ t.2.1 ∈ I

/-- The number of crossing edges of a list of present edges. -/
def MolMono_crossL (I X S : Finset V) (L : List (V × V × MClass)) : ℕ :=
  L.countP fun t => decide (MolMono_crossT I X S t)

/-- The number of crossing edges between two internal vertices of a list of present edges. -/
def MolMono_cIntL (I X S : Finset V) (L : List (V × V × MClass)) : ℕ :=
  L.countP fun t => decide (MolMono_intT I X S t)

/-- The vertices external and not internal reached by a crossing edge of a list of present
edges. -/
def MolMono_tExtL (I X S : Finset V) (L : List (V × V × MClass)) : Finset V :=
  (X \ I).filter fun a => ∃ t ∈ L, MolMono_crossT I X S t ∧ (t.1 = a ∨ t.2.1 = a)

/-- `MGraph.cHat` of a list of present edges. -/
def MolMono_cHatL (I X S : Finset V) (L : List (V × V × MClass)) : ℕ :=
  MolMono_cIntL I X S L + (MolMono_tExtL I X S L).card

/-- The number of red crossing edges of a list of present edges. -/
def MolMono_redL (I X S : Finset V) (L : List (V × V × MClass)) : ℕ :=
  L.countP fun t => decide (MolMono_redT I X S t)

/-- The present edge of an edge of a molecular multigraph: its ends and its class. -/
private def MolMono_dat {E : Type} (G : MGraph V E) (e : E) : Option (V × V × MClass) :=
  (G.cls e).map fun m => ((G.ends e).1, (G.ends e).2, m)

variable {E : Type}

omit [DecidableEq V] in
private theorem MolMono_crosses_iff (G : MGraph V E) (S : Finset V) (e : E) :
    G.Crosses S e ↔ ∃ t, MolMono_dat G e = some t ∧ MolMono_crossT G.int G.ext S t := by
  unfold MolMono_dat
  cases h : G.cls e <;> simp [MGraph.Crosses, h]

omit [DecidableEq V] in
private theorem MolMono_redCrosses_iff (G : MGraph V E) (S : Finset V) (e : E) :
    G.RedCrosses S e ↔ ∃ t, MolMono_dat G e = some t ∧ MolMono_redT G.int G.ext S t := by
  unfold MolMono_dat
  cases h : G.cls e <;> simp [MGraph.RedCrosses, h]

omit [DecidableEq V] in
private theorem MolMono_cInt_iff (G : MGraph V E) (S : Finset V) (e : E) :
    (G.Crosses S e ∧ (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int) ↔
      ∃ t, MolMono_dat G e = some t ∧ MolMono_intT G.int G.ext S t := by
  unfold MolMono_dat
  cases h : G.cls e <;> simp [MGraph.Crosses, h]

omit [DecidableEq V] in
private theorem MolMono_touch_iff (G : MGraph V E) (S : Finset V) (e : E) (a : V) :
    (G.Crosses S e ∧ ((G.ends e).1 = a ∨ (G.ends e).2 = a)) ↔
      ∃ t, MolMono_dat G e = some t ∧ (MolMono_crossT G.int G.ext S t ∧ (t.1 = a ∨ t.2.1 = a)) := by
  unfold MolMono_dat
  cases h : G.cls e <;> simp [MGraph.Crosses, h]

/-- A sum of indicators over a list, as a count over the present edges. -/
private theorem MolMono_sum_ite {α β : Type} (L : List α) (D : α → Option β) (p : β → Prop)
    [DecidablePred p] :
    (L.map fun c => if ∃ t, D c = some t ∧ p t then 1 else 0).sum =
      (L.filterMap D).countP (fun t => decide (p t)) := by
  classical
  induction L with
  | nil => rfl
  | cons c L ih =>
    cases h : D c with
    | none => simp [h, ih]
    | some t =>
      by_cases hp : p t
      · simp [h, ih, hp]
        omega
      · simp [h, ih, hp]

/-- A count over the edges `Fin l.length ⊕ Fin k` as a count over a list of present edges. -/
private theorem MolMono_card_filter {α β : Type} {k : ℕ} (l : List α) (D : α → Option β)
    (P : Fin k → Option β) (d : Fin l.length ⊕ Fin k → Option β)
    (hD : ∀ i : Fin l.length, d (.inl i) = D l[i.1]) (hP : ∀ a, d (.inr a) = P a)
    (p : β → Prop) [DecidablePred p] [DecidablePred fun e => ∃ t, d e = some t ∧ p t] :
    (Finset.univ.filter fun e => ∃ t, d e = some t ∧ p t).card =
      (l.filterMap D ++ (List.finRange k).filterMap P).countP (fun t => decide (p t)) := by
  classical
  rw [Finset.card_filter, Fintype.sum_sum_type, List.countP_append]
  congr 1
  · rw [← MolMono_sum_ite l D p, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hD]
  · rw [← MolMono_sum_ite _ P p, Fin.sum_univ_def]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    by_cases h : ∃ t, P a = some t ∧ p t <;> simp [hP, h]

/-- An existence over the edges `Fin l.length ⊕ Fin k` as an existence over a list of present
edges. -/
private theorem MolMono_exists_iff {α β : Type} {k : ℕ} (l : List α) (D : α → Option β)
    (P : Fin k → Option β) (d : Fin l.length ⊕ Fin k → Option β)
    (hD : ∀ i : Fin l.length, d (.inl i) = D l[i.1]) (hP : ∀ a, d (.inr a) = P a)
    (p : β → Prop) :
    (∃ e, ∃ t, d e = some t ∧ p t) ↔ ∃ t ∈ l.filterMap D ++ (List.finRange k).filterMap P, p t := by
  constructor
  · rintro ⟨e | a, t, ht, hp⟩
    · rw [hD] at ht
      exact ⟨t, List.mem_append_left _ (List.mem_filterMap.2 ⟨_, List.getElem_mem _, ht⟩), hp⟩
    · rw [hP] at ht
      exact ⟨t, List.mem_append_right _
        (List.mem_filterMap.2 ⟨a, List.mem_finRange a, ht⟩), hp⟩
  · rintro ⟨t, ht, hp⟩
    rcases List.mem_append.1 ht with ht | ht
    · obtain ⟨c, hc, hct⟩ := List.mem_filterMap.1 ht
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
      exact ⟨.inl ⟨i, hi⟩, t, by rw [hD]; exact hct, hp⟩
    · obtain ⟨a, -, hat⟩ := List.mem_filterMap.1 ht
      exact ⟨.inr a, t, by rw [hP]; exact hat, hp⟩

end Triples

/-! ## Comparison of lists of present edges -/

section ListCompare

variable {V : Type} [DecidableEq V] (I X S : Finset V)

/-- Membership in `MolMono_tExtL`. -/
theorem MolMono_mem_tExtL (L : List (V × V × MClass)) (a : V) :
    a ∈ MolMono_tExtL I X S L ↔ (a ∈ X ∧ a ∉ I) ∧
      ∃ t ∈ L, MolMono_crossT I X S t ∧ (t.1 = a ∨ t.2.1 = a) := by
  simp [MolMono_tExtL]

private theorem MolMono_tExtL_perm {L L' : List (V × V × MClass)} (h : L.Perm L') :
    MolMono_tExtL I X S L = MolMono_tExtL I X S L' := by
  ext a
  simp only [MolMono_mem_tExtL, h.mem_iff]

private theorem MolMono_cHatL_perm {L L' : List (V × V × MClass)} (h : L.Perm L') :
    MolMono_cHatL I X S L = MolMono_cHatL I X S L' := by
  unfold MolMono_cHatL MolMono_cIntL
  rw [h.countP_eq, MolMono_tExtL_perm I X S h]

private theorem MolMono_redL_perm {L L' : List (V × V × MClass)} (h : L.Perm L') :
    MolMono_redL I X S L = MolMono_redL I X S L' := by
  unfold MolMono_redL
  rw [h.countP_eq]

private theorem MolMono_crossL_perm {L L' : List (V × V × MClass)} (h : L.Perm L') :
    MolMono_crossL I X S L = MolMono_crossL I X S L' := by
  unfold MolMono_crossL
  rw [h.countP_eq]

private theorem MolMono_tExtL_append (A B : List (V × V × MClass)) :
    MolMono_tExtL I X S (A ++ B) = MolMono_tExtL I X S A ∪ MolMono_tExtL I X S B := by
  ext a
  simp only [MolMono_mem_tExtL, Finset.mem_union, List.mem_append]
  constructor
  · rintro ⟨ha, t, ht | ht, hc⟩
    · exact Or.inl ⟨ha, t, ht, hc⟩
    · exact Or.inr ⟨ha, t, ht, hc⟩
  · rintro (⟨ha, t, ht, hc⟩ | ⟨ha, t, ht, hc⟩)
    · exact ⟨ha, t, Or.inl ht, hc⟩
    · exact ⟨ha, t, Or.inr ht, hc⟩

/-- The replacement of the present edges `B₁` by `B₂` does not lower `MGraph.cHat` and the red
crossing count at `S`: the internal crossings of `B₁`, together with the external vertices
reached by `B₁` and not by `B₂`, are at most the internal crossings of `B₂`; the red crossings
of `B₁` are at most those of `B₂`. -/
def MolMono_Local (B₁ B₂ : List (V × V × MClass)) : Prop :=
  MolMono_cIntL I X S B₁ + (MolMono_tExtL I X S B₁ \ MolMono_tExtL I X S B₂).card ≤
      MolMono_cIntL I X S B₂ ∧
    MolMono_redL I X S B₁ ≤ MolMono_redL I X S B₂

/-- A replacement satisfying `MolMono_Local` inside any list of present edges does not lower
`MGraph.cHat` and the red crossing count. -/
theorem MolMono_append_le (A B₁ B₂ : List (V × V × MClass)) (h : MolMono_Local I X S B₁ B₂) :
    MolMono_cHatL I X S (A ++ B₁) ≤ MolMono_cHatL I X S (A ++ B₂) ∧
      MolMono_redL I X S (A ++ B₁) ≤ MolMono_redL I X S (A ++ B₂) := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · unfold MolMono_cHatL MolMono_cIntL at *
    rw [List.countP_append, List.countP_append, MolMono_tExtL_append, MolMono_tExtL_append]
    have hsub : MolMono_tExtL I X S A ∪ MolMono_tExtL I X S B₁ ⊆
        (MolMono_tExtL I X S A ∪ MolMono_tExtL I X S B₂) ∪
          (MolMono_tExtL I X S B₁ \ MolMono_tExtL I X S B₂) := by
      intro a ha
      simp only [Finset.mem_union, Finset.mem_sdiff] at ha ⊢
      tauto
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  · unfold MolMono_redL at *
    rw [List.countP_append, List.countP_append]
    omega

/-- A list of present edges that is a permutation of `A ++ B₁` or `A ++ B₂`. -/
private theorem MolMono_perm_le {L₁ L₂ A B₁ B₂ : List (V × V × MClass)} (h₁ : L₁.Perm (A ++ B₁))
    (h₂ : L₂.Perm (A ++ B₂)) (h : MolMono_Local I X S B₁ B₂) :
    MolMono_cHatL I X S L₁ ≤ MolMono_cHatL I X S L₂ ∧
      MolMono_redL I X S L₁ ≤ MolMono_redL I X S L₂ := by
  rw [MolMono_cHatL_perm I X S h₁, MolMono_cHatL_perm I X S h₂, MolMono_redL_perm I X S h₁,
    MolMono_redL_perm I X S h₂]
  exact MolMono_append_le I X S A B₁ B₂ h

/-- Adding present edges is a replacement satisfying `MolMono_Local`. -/
private theorem MolMono_local_nil (B : List (V × V × MClass)) : MolMono_Local I X S [] B := by
  simp [MolMono_Local, MolMono_cIntL, MolMono_redL, MolMono_tExtL]

/-- Equal lists of present edges. -/
private theorem MolMono_local_refl (B : List (V × V × MClass)) : MolMono_Local I X S B B := by
  simp [MolMono_Local]

/-- The edge from `u` to `v` of class `m`, absent when `u = v` (an edge inside one molecule). -/
def MolMono_opt (u v : V) (m : MClass) : List (V × V × MClass) :=
  if u = v then [] else [(u, v, m)]

/-- One present edge has at most one internal crossing or external vertex reached. -/
private theorem MolMono_single_le (hS : S ⊆ I) (t : V × V × MClass) :
    MolMono_cIntL I X S [t] + (MolMono_tExtL I X S [t]).card ≤ 1 := by
  by_cases hi : MolMono_intT I X S t
  · have hT : MolMono_tExtL I X S [t] = ∅ := by
      ext a
      simp only [MolMono_mem_tExtL, List.mem_singleton, exists_eq_left, Finset.notMem_empty,
        iff_false]
      rintro ⟨⟨-, hai⟩, -, h | h⟩
      · exact hai (h ▸ hi.2.1)
      · exact hai (h ▸ hi.2.2)
    rw [hT]
    simp [MolMono_cIntL, hi]
  · have h0 : MolMono_cIntL I X S [t] = 0 := by simp [MolMono_cIntL, hi]
    rw [h0, zero_add]
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    obtain ⟨⟨-, hai⟩, t', ht', hc, ha'⟩ := (MolMono_mem_tExtL I X S _ a).1 ha
    obtain ⟨⟨-, hbi⟩, t'', ht'', -, hb'⟩ := (MolMono_mem_tExtL I X S _ b).1 hb
    rw [List.mem_singleton] at ht' ht''
    subst ht' ht''
    have haS : a ∉ S := fun h => hai (hS h)
    have hbS : b ∉ S := fun h => hbi (hS h)
    obtain ⟨-, -, -, hcut⟩ := hc
    rcases ha' with rfl | rfl <;> rcases hb' with h | h
    · exact h
    · rcases hcut with hc | hc
      · exact absurd hc.1 haS
      · exact absurd (h ▸ hc.2) hbS
    · rcases hcut with hc | hc
      · exact absurd (h ▸ hc.1) hbS
      · exact absurd hc.2 haS
    · exact h

private theorem MolMono_one_le_cIntL {L : List (V × V × MClass)} {t : V × V × MClass} (ht : t ∈ L)
    (hi : MolMono_intT I X S t) : 1 ≤ MolMono_cIntL I X S L :=
  List.countP_pos_iff.2 ⟨t, ht, by simpa using hi⟩

private theorem MolMono_one_le_redL {L : List (V × V × MClass)} {t : V × V × MClass} (ht : t ∈ L)
    (hi : MolMono_redT I X S t) : 1 ≤ MolMono_redL I X S L :=
  List.countP_pos_iff.2 ⟨t, ht, by simpa using hi⟩

/-- **An edge replaced by a path.** The edge from `u` to `v` replaced by the path from `u` to `v`
through an internal vertex `x`, with the same class: `MGraph.cHat` and the red crossing count do
not drop. -/
theorem MolMono_local_path (hS : S ⊆ I) {u v x : V} (hx : x ∈ I) (m : MClass) :
    MolMono_Local I X S (MolMono_opt u v m) (MolMono_opt u x m ++ MolMono_opt x v m) := by
  by_cases huv : u = v
  · rw [show MolMono_opt u v m = [] by simp [MolMono_opt, huv]]
    exact MolMono_local_nil I X S _
  rw [show MolMono_opt u v m = [(u, v, m)] by simp [MolMono_opt, huv]]
  set B₂ := MolMono_opt u x m ++ MolMono_opt x v m with hB₂
  have hux : u ≠ x → (u, x, m) ∈ B₂ := fun h =>
    List.mem_append_left _ (by simp [MolMono_opt, h])
  have hxv : x ≠ v → (x, v, m) ∈ B₂ := fun h =>
    List.mem_append_right _ (by simp [MolMono_opt, h])
  have hxv' : x ∈ I ∨ x ∈ X := Or.inl hx
  have hsingle := MolMono_single_le I X S hS (u, v, m)
  have hA : (∃ t' ∈ B₂, MolMono_intT I X S t') →
      MolMono_cIntL I X S [(u, v, m)] +
        (MolMono_tExtL I X S [(u, v, m)] \ MolMono_tExtL I X S B₂).card ≤
        MolMono_cIntL I X S B₂ := by
    rintro ⟨t', ht', hi⟩
    have := MolMono_one_le_cIntL I X S ht' hi
    have := Finset.card_le_card (Finset.sdiff_subset (s := MolMono_tExtL I X S [(u, v, m)])
      (t := MolMono_tExtL I X S B₂))
    omega
  have hB : ∀ w, w ∉ I → (w = u ∨ w = v) → (∀ a, ((a = u ∨ a = v) → a ∉ I → a = w)) →
      (∃ t' ∈ B₂, MolMono_crossT I X S t' ∧ (t'.1 = w ∨ t'.2.1 = w)) →
      MolMono_cIntL I X S [(u, v, m)] +
        (MolMono_tExtL I X S [(u, v, m)] \ MolMono_tExtL I X S B₂).card ≤
        MolMono_cIntL I X S B₂ := by
    intro w hw hwe hend ⟨t', ht', hc', htw⟩
    have hni : ¬ MolMono_intT I X S (u, v, m) := by
      rintro ⟨-, hu, hv⟩
      rcases hwe with rfl | rfl
      · exact hw hu
      · exact hw hv
    have h0 : MolMono_cIntL I X S [(u, v, m)] = 0 := by simp [MolMono_cIntL, hni]
    have hsub : MolMono_tExtL I X S [(u, v, m)] \ MolMono_tExtL I X S B₂ = ∅ := by
      rw [Finset.sdiff_eq_empty_iff_subset]
      intro a ha
      obtain ⟨⟨haX, hai⟩, t, ht, -, hta⟩ := (MolMono_mem_tExtL I X S _ a).1 ha
      rw [List.mem_singleton] at ht
      subst ht
      have haw : a = w := hend a (hta.elim (fun h => Or.inl h.symm) fun h => Or.inr h.symm) hai
      subst haw
      exact (MolMono_mem_tExtL I X S _ _).2 ⟨⟨haX, hai⟩, t', ht', hc', htw⟩
    rw [h0, hsub]
    simp
  refine ⟨?_, ?_⟩
  · by_cases hc : MolMono_crossT I X S (u, v, m)
    · obtain ⟨hm, hu, hv, hcut⟩ := hc
      rcases hcut with ⟨huS, hvS⟩ | ⟨huS, hvS⟩
      · have huI := hS huS
        by_cases hxS : x ∈ S
        · have hxv0 : x ≠ v := fun h => hvS (h ▸ hxS)
          have hc' : MolMono_crossT I X S (x, v, m) := ⟨hm, hxv', hv, Or.inl ⟨hxS, hvS⟩⟩
          by_cases hvI : v ∈ I
          · exact hA ⟨_, hxv hxv0, hc', hx, hvI⟩
          · refine hB v hvI (Or.inr rfl) (fun a ha hai => ?_) ⟨_, hxv hxv0, hc', Or.inr rfl⟩
            rcases ha with rfl | rfl
            · exact absurd huI hai
            · rfl
        · have hux0 : u ≠ x := fun h => hxS (h ▸ huS)
          exact hA ⟨_, hux hux0, ⟨hm, Or.inl huI, hxv', Or.inl ⟨huS, hxS⟩⟩, huI, hx⟩
      · have hvI := hS hvS
        by_cases hxS : x ∈ S
        · have hux0 : u ≠ x := fun h => huS (h ▸ hxS)
          have hc' : MolMono_crossT I X S (u, x, m) := ⟨hm, hu, hxv', Or.inr ⟨huS, hxS⟩⟩
          by_cases huI : u ∈ I
          · exact hA ⟨_, hux hux0, hc', huI, hx⟩
          · refine hB u huI (Or.inl rfl) (fun a ha hai => ?_) ⟨_, hux hux0, hc', Or.inl rfl⟩
            rcases ha with rfl | rfl
            · rfl
            · exact absurd hvI hai
        · have hxv0 : x ≠ v := fun h => hxS (h ▸ hvS)
          exact hA ⟨_, hxv hxv0, ⟨hm, hxv', Or.inl hvI, Or.inr ⟨hxS, hvS⟩⟩, hx, hvI⟩
    · have hni : ¬ MolMono_intT I X S (u, v, m) := fun h => hc h.1
      have h0 : MolMono_cIntL I X S [(u, v, m)] = 0 := by simp [MolMono_cIntL, hni]
      have hT : MolMono_tExtL I X S [(u, v, m)] = ∅ := by
        ext a
        simp only [MolMono_mem_tExtL, List.mem_singleton, exists_eq_left, Finset.notMem_empty,
          iff_false]
        exact fun h => hc h.2.1
      rw [h0, hT]
      simp
  · by_cases hr : MolMono_redT I X S (u, v, m)
    · have h1 : MolMono_redL I X S [(u, v, m)] ≤ 1 := by
        unfold MolMono_redL
        exact (List.countP_le_length).trans (by simp)
      refine h1.trans ?_
      obtain ⟨hm, hu, hv, hcut⟩ := hr
      rcases hcut with ⟨huS, hvS⟩ | ⟨huS, hvS⟩
      · by_cases hxS : x ∈ S
        · have hxv0 : x ≠ v := fun h => hvS (h ▸ hxS)
          exact MolMono_one_le_redL I X S (hxv hxv0) ⟨hm, hxv', hv, Or.inl ⟨hxS, hvS⟩⟩
        · have hux0 : u ≠ x := fun h => hxS (h ▸ huS)
          exact MolMono_one_le_redL I X S (hux hux0) ⟨hm, hu, hxv', Or.inl ⟨huS, hxS⟩⟩
      · by_cases hxS : x ∈ S
        · have hux0 : u ≠ x := fun h => huS (h ▸ hxS)
          exact MolMono_one_le_redL I X S (hux hux0) ⟨hm, hu, hxv', Or.inr ⟨huS, hxS⟩⟩
        · have hxv0 : x ≠ v := fun h => hxS (h ▸ hvS)
          exact MolMono_one_le_redL I X S (hxv hxv0) ⟨hm, hxv', hv, Or.inr ⟨hxS, hvS⟩⟩
    · have : MolMono_redL I X S [(u, v, m)] = 0 := by simp [MolMono_redL, hr]
      rw [this]
      exact Nat.zero_le _

end ListCompare

/-! ## The edges of `Graph.toMG'` as a list -/

section GraphEdges

variable {k n : ℕ}

/-- The present edge of `Graph.toMG'` given by a component: absent for a dotted edge, an edge
inside one molecule, or a kind that is not an edge of the molecular graph; otherwise the
molecules of the ends in the block normal form, and the class. -/
def MolMono_edgeD (Γ : Graph k n) (c : Comp (Atom k n)) : Option (Atom k n × Atom k n × MClass) :=
  if c.kind = .dot ∨ Γ.molRep (Γ.flatAtom c.x) = Γ.molRep (Γ.flatAtom c.y) then none
  else c.kind.mclass.map fun m => (Γ.molRep (Γ.flatAtom c.x), Γ.molRep (Γ.flatAtom c.y), m)

/-- The present pin edge of `Graph.toMG'` at the external atom `a`. -/
def MolMono_pinD (Γ : Graph k n) (a : Fin k) : Option (Atom k n × Atom k n × MClass) :=
  match Γ.anchor (.inl a) with
  | some b => some (Γ.molRep (.inr b), .inl a, pinClass a)
  | none => none

/-- The present edges of `Graph.toMG'`: those of the components, then the pin edges. -/
def MolMono_edges (Γ : Graph k n) : List (Atom k n × Atom k n × MClass) :=
  Γ.comps.filterMap (MolMono_edgeD Γ) ++ (List.finRange k).filterMap (MolMono_pinD Γ)

private theorem MolMono_dat_inl (Γ : Graph k n) (i : Fin Γ.comps.length) :
    MolMono_dat Γ.toMG' (.inl i) = MolMono_edgeD Γ Γ.comps[i.1] := by
  simp only [MolMono_dat, Graph.toMG', MolMono_edgeD, Fin.getElem_fin, Graph.flatComp]
  by_cases hk : Γ.comps[i.1].kind = .dot
  · simp [hk]
  · simp only [hk, ite_false, false_or]
    split_ifs <;> rfl

private theorem MolMono_dat_inr (Γ : Graph k n) (a : Fin k) :
    MolMono_dat Γ.toMG' (.inr a) = MolMono_pinD Γ a := by
  simp only [MolMono_dat, Graph.toMG', MolMono_pinD]
  cases Γ.anchor (.inl a) <;> rfl

/-- The crossing count as a count over the present edges. -/
theorem MolMono_crossCount_eq (Γ : Graph k n) (S : Finset (Atom k n)) :
    Γ.toMG'.crossCount S =
      MolMono_crossL Γ.toMG'.int Γ.toMG'.ext S (MolMono_edges Γ) := by
  classical
  unfold MGraph.crossCount MolMono_crossL MolMono_edges
  rw [← MolMono_card_filter Γ.comps (MolMono_edgeD Γ) (MolMono_pinD Γ) (MolMono_dat Γ.toMG')
    (MolMono_dat_inl Γ) (MolMono_dat_inr Γ)]
  exact congrArg Finset.card (Finset.filter_congr fun e _ => MolMono_crosses_iff _ S e)

/-- The red crossing count as a count over the present edges. -/
theorem MolMono_redCount_eq (Γ : Graph k n) (S : Finset (Atom k n)) :
    Γ.toMG'.redCount S =
      MolMono_redL Γ.toMG'.int Γ.toMG'.ext S (MolMono_edges Γ) := by
  classical
  unfold MGraph.redCount MolMono_redL MolMono_edges
  rw [← MolMono_card_filter Γ.comps (MolMono_edgeD Γ) (MolMono_pinD Γ) (MolMono_dat Γ.toMG')
    (MolMono_dat_inl Γ) (MolMono_dat_inr Γ)]
  exact congrArg Finset.card (Finset.filter_congr fun e _ => MolMono_redCrosses_iff _ S e)

/-- `MGraph.cHat` as a count over the present edges. -/
theorem MolMono_cHat_eq (Γ : Graph k n) (S : Finset (Atom k n)) :
    Γ.toMG'.cHat S = MolMono_cHatL Γ.toMG'.int Γ.toMG'.ext S (MolMono_edges Γ) := by
  unfold MGraph.cHat MolMono_cHatL MolMono_cIntL MolMono_edges
  congr 1
  · classical
    unfold MolMono_cInt
    rw [← MolMono_card_filter Γ.comps (MolMono_edgeD Γ) (MolMono_pinD Γ) (MolMono_dat Γ.toMG')
      (MolMono_dat_inl Γ) (MolMono_dat_inr Γ)]
    exact congrArg Finset.card (Finset.filter_congr fun e _ => MolMono_cInt_iff _ S e)
  · unfold MolMono_tExt MolMono_tExtL
    congr 1
    ext a
    simp only [Finset.mem_filter]
    rw [← MolMono_exists_iff Γ.comps (MolMono_edgeD Γ) (MolMono_pinD Γ) (MolMono_dat Γ.toMG')
      (MolMono_dat_inl Γ) (MolMono_dat_inr Γ)]
    exact and_congr_right fun _ => exists_congr fun e => MolMono_touch_iff _ S e a

end GraphEdges

/-! ## Graphs with the same blocks and molecules -/

section Struct

variable {k n : ℕ}

private theorem MolMono_anchor_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v) (u : Atom k n) :
    Γ₁.anchor u = Γ₂.anchor u := by
  classical
  rw [MolMono_anchor_eq_find, MolMono_anchor_eq_find]
  congr 1
  funext b
  exact decide_eq_decide.2 (hB _ _)

private theorem MolMono_flatAtom_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v) (u : Atom k n) :
    Γ₁.flatAtom u = Γ₂.flatAtom u := by
  rcases u with a | a
  · simp only [Graph.flatAtom, MolMono_anchor_congr hB]
  · rfl

private theorem MolMono_molRep_congr {Γ₁ Γ₂ : Graph k n}
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) (u : Atom k n) :
    Γ₁.molRep u = Γ₂.molRep u := by
  classical
  rcases u with a | a
  · rfl
  · rw [MolMono_molRep_eq_find, MolMono_molRep_eq_find]
    congr 3
    funext b
    exact decide_eq_decide.2 (hM _ _)

private theorem MolMono_edgeD_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v)
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) : MolMono_edgeD Γ₁ = MolMono_edgeD Γ₂ := by
  funext c
  simp only [MolMono_edgeD, MolMono_flatAtom_congr hB, MolMono_molRep_congr hM]

private theorem MolMono_pinD_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v)
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) : MolMono_pinD Γ₁ = MolMono_pinD Γ₂ := by
  funext a
  simp only [MolMono_pinD, MolMono_anchor_congr hB, MolMono_molRep_congr hM]

private theorem MolMono_int_congr {Γ₁ Γ₂ : Graph k n}
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) : Γ₁.toMG'.int = Γ₂.toMG'.int := by
  simp only [Graph.toMG', MolMono_molRep_congr hM]

/-- A permutation `L ~ A ++ B`, followed by `P`. -/
private theorem MolMono_perm_aux {α : Type} {L A B : List α} (h : L.Perm (A ++ B)) (P : List α) :
    (L ++ P).Perm ((A ++ P) ++ B) := by
  refine (h.append_right P).trans ?_
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left A List.perm_append_comm

/-- Two graphs with the same blocks and molecules, whose present edges of components are
`A ++ B₁` and `A ++ B₂` up to order, with `B₁` replaced by `B₂` as in `MolMono_Local`: the
identity map is `Graph.MolMono`. -/
private theorem MolMono_of_local {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v)
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v)
    (A B₁ B₂ : List (Atom k n × Atom k n × MClass))
    (h₁ : (Γ₁.comps.filterMap (MolMono_edgeD Γ₁)).Perm (A ++ B₁))
    (h₂ : (Γ₂.comps.filterMap (MolMono_edgeD Γ₁)).Perm (A ++ B₂))
    (hl : ∀ S ⊆ Γ₁.toMG'.int, MolMono_Local Γ₁.toMG'.int Γ₁.toMG'.ext S B₁ B₂) :
    Γ₁.MolMono Γ₂ id := by
  have hI := MolMono_int_congr hM
  have hpull : ∀ S ⊆ Γ₂.toMG'.int, Γ₁.molPull Γ₂ id S = S := by
    intro S hS
    have : Γ₁.molPull Γ₂ id S = Γ₁.molPull Γ₁ id S := by
      simp only [Graph.molPull, id, MolMono_molRep_congr hM]
    rw [this, MolMono_molPull_id Γ₁ (hI ▸ hS)]
  have hE₂ : MolMono_edges Γ₂ = Γ₂.comps.filterMap (MolMono_edgeD Γ₁) ++
      (List.finRange k).filterMap (MolMono_pinD Γ₁) := by
    rw [MolMono_edges, MolMono_edgeD_congr hB hM, MolMono_pinD_congr hB hM]
  have key : ∀ S ⊆ Γ₂.toMG'.int,
      MolMono_cHatL Γ₁.toMG'.int Γ₁.toMG'.ext S (MolMono_edges Γ₁) ≤
        MolMono_cHatL Γ₁.toMG'.int Γ₁.toMG'.ext S (MolMono_edges Γ₂) ∧
      MolMono_redL Γ₁.toMG'.int Γ₁.toMG'.ext S (MolMono_edges Γ₁) ≤
        MolMono_redL Γ₁.toMG'.int Γ₁.toMG'.ext S (MolMono_edges Γ₂) := by
    intro S hS
    rw [hE₂]
    exact MolMono_perm_le _ _ _ (MolMono_perm_aux h₁ _) (MolMono_perm_aux h₂ _)
      (hl S (hI ▸ hS))
  refine ⟨fun _ => rfl, fun a b h => ?_, fun v hv => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · simp only [id, ← MolMono_molRep_congr hM]
    exact h
  · rw [← hI] at hv
    obtain ⟨a, ha⟩ := (MolMono_mem_int Γ₁ v).1 hv
    exact ⟨a, by simp only [id, ← MolMono_molRep_congr hM]; exact ha⟩
  · rw [hpull S hS, MolMono_cHat_eq, MolMono_cHat_eq, ← hI]
    exact (key S hS).1
  · rw [hpull S hS, MolMono_redCount_eq, MolMono_redCount_eq, ← hI]
    exact (key S hS).2

/-- Two graphs with the same blocks and molecules and the same present edges of components, up
to order. -/
private theorem MolMono_of_perm {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v)
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v)
    (h : (Γ₂.comps.filterMap (MolMono_edgeD Γ₁)).Perm (Γ₁.comps.filterMap (MolMono_edgeD Γ₁))) :
    Γ₁.MolMono Γ₂ id :=
  MolMono_of_local hB hM _ [] [] (by rw [List.append_nil]) (by rw [List.append_nil]; exact h)
    fun S _ => MolMono_local_refl _ _ S []

/-- Every waved or dotted edge of `l₁` has a copy, with the same kind and ends, in `l₂`. -/
private def MolMono_JoinSub (l₁ l₂ : List (Comp (Atom k n))) : Prop :=
  ∀ c ∈ l₁, c.kind.joinsMol = true → ∃ d ∈ l₂, d.kind = c.kind ∧ d.x = c.x ∧ d.y = c.y

private theorem MolMono_joinSub_of_mem {l₁ l₂ : List (Comp (Atom k n))}
    (h : ∀ c ∈ l₁, c.kind.joinsMol = true → c ∈ l₂) : MolMono_JoinSub l₁ l₂ :=
  fun c hc hj => ⟨c, h c hc hj, rfl, rfl, rfl⟩

/-- Graphs whose waved and dotted edges agree have the same blocks and the same molecules. -/
private theorem MolMono_same_of_join {Γ₁ Γ₂ : Graph k n} (h₁ : MolMono_JoinSub Γ₁.comps Γ₂.comps)
    (h₂ : MolMono_JoinSub Γ₂.comps Γ₁.comps) :
    (∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v) ∧
      (∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) := by
  have hrel : ∀ (p : Kind → Prop), (∀ κ, p κ → κ.joinsMol = true) → ∀ u v,
      (∃ c ∈ Γ₁.comps, p c.kind ∧ c.x = u ∧ c.y = v) ↔
        (∃ c ∈ Γ₂.comps, p c.kind ∧ c.x = u ∧ c.y = v) := by
    intro p hp u v
    constructor
    · rintro ⟨c, hc, hk, rfl, rfl⟩
      obtain ⟨d, hd, h1, h2, h3⟩ := h₁ c hc (hp _ hk)
      exact ⟨d, hd, h1 ▸ hk, h2, h3⟩
    · rintro ⟨c, hc, hk, rfl, rfl⟩
      obtain ⟨d, hd, h1, h2, h3⟩ := h₂ c hc (hp _ hk)
      exact ⟨d, hd, h1 ▸ hk, h2, h3⟩
  have hd : Γ₁.dotGraph = Γ₂.dotGraph := by
    unfold Graph.dotGraph
    congr 1
    funext u v
    exact propext (hrel (· = .dot) (fun κ h => by rw [h]; rfl) u v)
  have hm : Γ₁.molGraph = Γ₂.molGraph := by
    unfold Graph.molGraph
    congr 1
    funext u v
    exact propext (hrel (fun κ => κ.joinsMol = true) (fun _ h => h) u v)
  refine ⟨fun u v => by unfold Graph.SameBlock; rw [hd], fun u v => ?_⟩
  unfold Graph.SameMol
  rw [hm]

/-- A reachability transported along adjacencies. -/
private theorem MolMono_reach_of_adj {α : Type} {G H : SimpleGraph α}
    (h : ∀ u v, G.Adj u v → H.Reachable u v) {u v : α} (hr : G.Reachable u v) :
    H.Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hab ih => exact ih.trans (h _ _ hab)

/-- Atoms of one block are joined by a path of waved and dotted edges. -/
private theorem MolMono_mol_of_block (Γ : Graph k n) {u v : Atom k n} (h : Γ.SameBlock u v) :
    Γ.molGraph.Reachable u v := by
  refine MolMono_reach_of_adj (fun a b hab => ?_) h
  rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
  refine SimpleGraph.Adj.reachable ?_
  rw [Graph.molGraph, SimpleGraph.fromRel_adj]
  refine ⟨hab.1, ?_⟩
  rcases hab.2 with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
  · exact Or.inl ⟨c, hc, by rw [hk]; rfl, h1, h2⟩
  · exact Or.inr ⟨c, hc, by rw [hk]; rfl, h1, h2⟩

private theorem MolMono_sameMol_of_reach {Γ₁ Γ₂ : Graph k n}
    (h : ∀ u v, Γ₁.molGraph.Reachable u v ↔ Γ₂.molGraph.Reachable u v) :
    ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v := by
  intro u v
  unfold Graph.SameMol
  rw [h]

private theorem MolMono_perm_eraseIdx {α : Type} {l : List α} {i : ℕ} {c : α} (h : l[i]? = some c) :
    l.Perm (c :: l.eraseIdx i) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  conv_lhs => rw [← List.insertIdx_eraseIdx_getElem hi]
  exact List.perm_insertIdx _ _ (by rw [List.length_eraseIdx_of_lt hi]; omega)

private theorem MolMono_filterMap_cons {α β : Type} (D : α → Option β) (c : α) (l : List α) :
    (c :: l).filterMap D = (D c).toList ++ l.filterMap D := by
  cases h : D c <;> simp [h]

/-- `MolMono_edgeD` reads only the kind and the ends of a component. -/
private theorem MolMono_edgeD_eq_of (Γ : Graph k n) {c d : Comp (Atom k n)}
    (h : d.kind = c.kind ∧ d.x = c.x ∧ d.y = c.y) : MolMono_edgeD Γ d = MolMono_edgeD Γ c := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [MolMono_edgeD, h1, h2, h3]

private theorem MolMono_edgeD_none (Γ : Graph k n) {c : Comp (Atom k n)}
    (h : c.kind.mclass = none) :
    MolMono_edgeD Γ c = none := by
  unfold MolMono_edgeD
  split_ifs <;> simp [h]

private theorem MolMono_edgeD_dot (Γ : Graph k n) {c : Comp (Atom k n)} (h : c.kind = .dot) :
    MolMono_edgeD Γ c = none := by
  simp [MolMono_edgeD, h]

/-- The class of a solid edge of charge `ch` in the molecular graph. -/
private def MolMono_chClass : Charge → MClass
  | .plus => .plus
  | .minus => .minus

/-- The present edge of the solid edge (or weight) `solidC ch a b`. -/
private theorem MolMono_edgeD_solidC (Γ : Graph k n) (ch : Charge) (a b : Atom k n)
    (l : Option (PQ × Atom k n)) :
    (MolMono_edgeD Γ { solidC ch a b with label := l }).toList =
      MolMono_opt (Γ.molRep (Γ.flatAtom a)) (Γ.molRep (Γ.flatAtom b)) (MolMono_chClass ch) := by
  by_cases hab : a = b
  · subst hab
    simp [MolMono_edgeD, MolMono_opt, solidC, mkC]
  · unfold MolMono_edgeD MolMono_opt
    simp only [solidC, hab, ite_false, mkC]
    by_cases he : Γ.molRep (Γ.flatAtom a) = Γ.molRep (Γ.flatAtom b)
    · simp [he]
    · cases ch <;> simp [he, Kind.mclass, MolMono_chClass]

/-- The present edge of the solid edge `G_{ab}` of charge `ch`. -/
private theorem MolMono_edgeD_G (Γ : Graph k n) {c : Comp (Atom k n)} {ch : Charge}
    (hk : c.kind = .G ch) :
    (MolMono_edgeD Γ c).toList =
      MolMono_opt (Γ.molRep (Γ.flatAtom c.x)) (Γ.molRep (Γ.flatAtom c.y)) (MolMono_chClass ch) := by
  unfold MolMono_edgeD MolMono_opt
  by_cases he : Γ.molRep (Γ.flatAtom c.x) = Γ.molRep (Γ.flatAtom c.y)
  · simp [he]
  · cases ch <;> simp [he, hk, Kind.mclass, MolMono_chClass]

/-- The internal vertex of the molecule of an internal atom. -/
private theorem MolMono_rep_flat_int (Γ : Graph k n) {x : Atom k n} (hx : x.isRight = true) :
    Γ.molRep (Γ.flatAtom x) ∈ Γ.toMG'.int := by
  rcases x with a | a
  · cases hx
  · exact MolMono_molRep_mem_int Γ a

/-- **A component replaced.** The component `i`, neither waved nor dotted, replaced by
a list of components neither waved nor dotted, whose present edges replace that of the component
as in `MolMono_Local`: the identity map is `Graph.MolMono`. -/
private theorem MolMono_eraseIdx_append {Γ : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : Γ.comps[i]? = some c) (hcj : c.kind.joinsMol = false)
    (new : List (Comp (Atom k n))) (hnew : ∀ d ∈ new, d.kind.joinsMol = false) (co : Coeff)
    (hl : ∀ S ⊆ Γ.toMG'.int, MolMono_Local Γ.toMG'.int Γ.toMG'.ext S
      (MolMono_edgeD Γ c).toList (new.filterMap (MolMono_edgeD Γ))) :
    Γ.MolMono ⟨Γ.comps.eraseIdx i ++ new, co⟩ id := by
  have hp := MolMono_perm_eraseIdx hc
  obtain ⟨hB, hM⟩ := MolMono_same_of_join (Γ₁ := Γ) (Γ₂ := ⟨Γ.comps.eraseIdx i ++ new, co⟩)
    (MolMono_joinSub_of_mem fun d hd hj => by
      rcases List.mem_cons.1 (hp.mem_iff.1 hd) with rfl | hd'
      · rw [hcj] at hj; cases hj
      · exact List.mem_append_left _ hd')
    (MolMono_joinSub_of_mem fun d hd hj => by
      rcases List.mem_append.1 hd with hd' | hd'
      · exact List.mem_of_mem_eraseIdx hd'
      · rw [hnew d hd'] at hj; cases hj)
  refine MolMono_of_local hB hM ((Γ.comps.eraseIdx i).filterMap (MolMono_edgeD Γ))
    (MolMono_edgeD Γ c).toList (new.filterMap (MolMono_edgeD Γ)) ?_ ?_ hl
  · refine (hp.filterMap _).trans ?_
    rw [MolMono_filterMap_cons]
    exact List.perm_append_comm
  · change ((Γ.comps.eraseIdx i ++ new).filterMap (MolMono_edgeD Γ)).Perm _
    rw [List.filterMap_append]

/-- Components neither waved nor dotted added to a graph. -/
private theorem MolMono_append_new (Γ : Graph k n) (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, d.kind.joinsMol = false) (co : Coeff) :
    Γ.MolMono ⟨Γ.comps ++ new, co⟩ id := by
  obtain ⟨hB, hM⟩ := MolMono_same_of_join (Γ₁ := Γ) (Γ₂ := ⟨Γ.comps ++ new, co⟩)
    (MolMono_joinSub_of_mem fun d hd _ => List.mem_append_left _ hd)
    (MolMono_joinSub_of_mem fun d hd hj => by
      rcases List.mem_append.1 hd with hd' | hd'
      · exact hd'
      · rw [hnew d hd'] at hj; cases hj)
  refine MolMono_of_local hB hM (Γ.comps.filterMap (MolMono_edgeD Γ)) []
    (new.filterMap (MolMono_edgeD Γ)) (by rw [List.append_nil]) ?_
    fun S _ => MolMono_local_nil _ _ S _
  change ((Γ.comps ++ new).filterMap (MolMono_edgeD Γ)).Perm _
  rw [List.filterMap_append]

/-- A map of the components keeping kinds and ends (a change of labels or minors). -/
private theorem MolMono_of_map (Γ : Graph k n) (g : Comp (Atom k n) → Comp (Atom k n))
    (hg : ∀ c, (g c).kind = c.kind ∧ (g c).x = c.x ∧ (g c).y = c.y) (co : Coeff) :
    Γ.MolMono ⟨Γ.comps.map g, co⟩ id := by
  obtain ⟨hB, hM⟩ := MolMono_same_of_join (Γ₁ := Γ) (Γ₂ := ⟨Γ.comps.map g, co⟩)
    (fun c hc _ => ⟨g c, List.mem_map_of_mem hc, hg c⟩)
    (fun d hd _ => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
      obtain ⟨h1, h2, h3⟩ := hg c
      exact ⟨c, hc, h1.symm, h2.symm, h3.symm⟩)
  refine MolMono_of_perm hB hM ?_
  change ((Γ.comps.map g).filterMap (MolMono_edgeD Γ)).Perm _
  rw [List.filterMap_map]
  have : (MolMono_edgeD Γ ∘ g) = MolMono_edgeD Γ := funext fun c => MolMono_edgeD_eq_of Γ (hg c)
  rw [this]

end Struct

/-! ## The steps that keep the blocks -/

section Steps

variable {k n : ℕ}

private theorem MolMono_self (Γ : Graph k n) : Γ.MolMono (Tracked.self Γ).g (Tracked.self Γ).f :=
  Graph.MolMono.refl Γ

private theorem MolMono_filterMap_single {α β : Type} (D : α → Option β) (c : α) :
    [c].filterMap D = (D c).toList := by
  rw [MolMono_filterMap_cons]
  simp

private theorem MolMono_solidC_join (ch : Charge) (a b : Atom k n) (l : Option (PQ × Atom k n)) :
    ({ solidC ch a b with label := l } : Comp (Atom k n)).kind.joinsMol = false := by
  unfold solidC
  split_ifs <;> rfl

/-- The component `i`, whose present edge is absent, replaced by components neither waved nor
dotted. -/
theorem MolMono_eraseIdx_none {Γ : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : Γ.comps[i]? = some c) (hD : MolMono_edgeD Γ c = none) (hcj : c.kind.joinsMol = false)
    (new : List (Comp (Atom k n))) (hnew : ∀ d ∈ new, d.kind.joinsMol = false) (co : Coeff) :
    Γ.MolMono ⟨Γ.comps.eraseIdx i ++ new, co⟩ id :=
  MolMono_eraseIdx_append hc hcj new hnew co fun S _ => by
    rw [hD]
    exact MolMono_local_nil _ _ S _

/-- The component `i`, neither waved nor dotted, with its minor changed. -/
private theorem MolMono_minor_row {Γ : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : Γ.comps[i]? = some c) (hcj : c.kind.joinsMol = false) (T : List (Atom k n))
    (co : Coeff) : Γ.MolMono ⟨Γ.comps.eraseIdx i ++ [{ c with minor := T }], co⟩ id :=
  MolMono_eraseIdx_append hc hcj _ (by simpa using hcj) co fun S _ => by
    rw [MolMono_filterMap_single, MolMono_edgeD_eq_of Γ ⟨rfl, rfl, rfl⟩]
    exact MolMono_local_refl _ _ S _

/-- **The path of [II, (4.17), (4.20)]**: the solid edge `G_{ab}` with index `i` replaced by
`G_{ax} G_{xb} (G_{xx})⁻¹` at an internal atom `x`. -/
theorem MolMono_path_row {Γ : Graph k n} {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : Γ.comps[i]? = some c) (hk : c.kind = .G ch) {x : Atom k n} (hx : x.isRight = true)
    (l : Option (PQ × Atom k n)) (co : Coeff) :
    Γ.MolMono ⟨Γ.comps.eraseIdx i ++ [{ solidC ch c.x x with label := l },
      { solidC ch x c.y with label := l }, { mkC (.inv ch) x x with label := l }], co⟩ id := by
  refine MolMono_eraseIdx_append hc (by rw [hk]; rfl) _ ?_ co fun S hS => ?_
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact MolMono_solidC_join _ _ _ _
    · exact MolMono_solidC_join _ _ _ _
    · rfl
  · rw [MolMono_filterMap_cons, MolMono_filterMap_cons, MolMono_filterMap_single,
      MolMono_edgeD_solidC, MolMono_edgeD_solidC,
      MolMono_edgeD_none Γ (c := { mkC (.inv ch) x x with label := l }) rfl, MolMono_edgeD_G Γ hk]
    simp only [Option.toList_none, List.append_nil]
    exact MolMono_local_path _ _ S hS (MolMono_rep_flat_int Γ hx) _

/-- **[II, (4.17)]** at the solid edge with index `i`, at an internal atom `x`: every term is
`Graph.MolMono` with its atom map. -/
theorem molMono_oSchurT (x : Atom k n) (hx : x.isRight = true) (i : ℕ) (Γ : Graph k n)
    (t : Tracked k n) (ht : t ∈ oSchurT x i Γ) : Γ.MolMono t.g t.f := by
  unfold oSchurT at ht
  split at ht
  · rename_i c hci
    split at ht
    · rename_i ch hk
      split_ifs at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact MolMono_minor_row hci (by rw [hk]; rfl) _ _
        · exact MolMono_path_row hci hk hx _ _
      · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
    · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
  · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ

/-- **[II, (4.20)]** at the component with index `i`, at an internal atom `x`. -/
theorem molMono_oSchurRevT (x : Atom k n) (hx : x.isRight = true) (i : ℕ) (Γ : Graph k n)
    (t : Tracked k n) (ht : t ∈ oSchurRevT x i Γ) : Γ.MolMono t.g t.f := by
  unfold oSchurRevT at ht
  split at ht
  · rename_i c hci
    split at ht
    · rename_i ch hk
      split_ifs at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact MolMono_minor_row hci (by rw [hk]; rfl) _ _
        · exact MolMono_path_row hci hk hx _ _
      · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
    · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
  · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ

/-- The second term of [II, (4.17), (4.20)] at a weight or light weight with index `i`. -/
private theorem MolMono_weight_row {Γ : Graph k n} {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : Γ.comps[i]? = some c) (hk : c.kind = .weight ch ∨ c.kind = .light ch)
    (x : Atom k n) (co : Coeff) :
    Γ.MolMono ⟨Γ.comps.eraseIdx i ++ [{ mkC (.G ch) c.x x with label := c.label },
      { mkC (.G ch) x c.x with label := c.label },
      { mkC (.inv ch) x x with label := c.label }], co⟩ id := by
  refine MolMono_eraseIdx_none hc ?_ ?_ _ ?_ co
  · exact MolMono_edgeD_none Γ (by rcases hk with h | h <;> rw [h] <;> rfl)
  · rcases hk with h | h <;> rw [h] <;> rfl
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> rfl

/-- **[II, (4.17)]** at the weight or light weight with index `i`, at the atom `x`. -/
theorem molMono_oSchurWT (x : Atom k n) (i : ℕ) (Γ : Graph k n) (t : Tracked k n)
    (ht : t ∈ oSchurWT x i Γ) : Γ.MolMono t.g t.f := by
  unfold oSchurWT at ht
  split at ht
  · rename_i c hci
    split at ht
    · rename_i ch hk
      split_ifs at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact MolMono_minor_row hci (by rw [hk]; rfl) _ _
        · exact MolMono_weight_row hci (Or.inl hk) _ _
      · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
    · rename_i ch hk
      split_ifs at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact MolMono_minor_row hci (by rw [hk]; rfl) _ _
        · exact MolMono_weight_row hci (Or.inr hk) _ _
      · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
    · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
  · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ

/-- **[II, (4.20)]** at the weight or light weight with index `i` and minor `{x}`. -/
theorem molMono_oSchurWRevT (x : Atom k n) (i : ℕ) (Γ : Graph k n) (t : Tracked k n)
    (ht : t ∈ oSchurWRevT x i Γ) : Γ.MolMono t.g t.f := by
  unfold oSchurWRevT at ht
  split at ht
  · rename_i c hci
    split at ht
    · rename_i ch hk
      split_ifs at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact MolMono_minor_row hci (by rw [hk]; rfl) _ _
        · exact MolMono_weight_row hci (Or.inl hk) _ _
      · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
    · rename_i ch hk
      split_ifs at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact MolMono_minor_row hci (by rw [hk]; rfl) _ _
        · exact MolMono_weight_row hci (Or.inr hk) _ _
      · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
    · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
  · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ

/-- **[II, (4.21)]** at the weight `(G_{xx})⁻¹` with index `i`: every term. -/
theorem molMono_oTaylorT (D i : ℕ) (Γ : Graph k n) (t : Tracked k n)
    (ht : t ∈ oTaylorT D i Γ) : Γ.MolMono t.g t.f := by
  unfold oTaylorT at ht
  split at ht
  · rename_i c hci
    split at ht
    · rename_i ch hk
      have hD : MolMono_edgeD Γ c = none := MolMono_edgeD_none Γ (by rw [hk]; rfl)
      have hcj : c.kind.joinsMol = false := by rw [hk]; rfl
      dsimp only at ht
      split_ifs at ht
      · rcases List.mem_append.1 ht with ht | ht
        · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
          refine MolMono_eraseIdx_none hci hD hcj _ (fun d hd => ?_) _
          rw [(List.mem_replicate.1 hd).2]
          rfl
        · rw [List.mem_singleton.1 ht]
          exact MolMono_eraseIdx_none hci hD hcj _ (fun d hd => by
            rw [List.mem_singleton.1 hd]; rfl) _
      · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
    · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ
  · rw [List.mem_singleton.1 ht]; exact MolMono_self Γ

/-- The term of `1 = 1_{u = v} + 1_{u ≠ v}` with the `×`-dotted edge between `u` and `v`. -/
theorem molMono_split_xdot (u v : Atom k n) (Γ : Graph k n) :
    Γ.MolMono ⟨Γ.comps ++ [mkC .xdot u v], Γ.coeff⟩ id :=
  MolMono_append_new Γ _ (fun d hd => by rw [List.mem_singleton.1 hd]; rfl) _

/-- The term of `1_{u ≠ v} = 1 - 1_{u = v}` without the `×`-dotted edge with index `i`. -/
theorem molMono_xdot_erase (i : ℕ) (Γ : Graph k n) (c : Comp (Atom k n))
    (hc : Γ.comps[i]? = some c) (hk : c.kind = .xdot) :
    Γ.MolMono ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ id := by
  have := MolMono_eraseIdx_none hc (MolMono_edgeD_none Γ (by rw [hk]; rfl)) (by rw [hk]; rfl)
    [] (by simp) Γ.coeff
  rwa [List.append_nil] at this

/-- **`Q_u = 1 - P_u`**: both terms. -/
theorem molMono_oQPT (u : Atom k n) (Γ : Graph k n) (t : Tracked k n) (ht : t ∈ oQPT u Γ) :
    Γ.MolMono t.g t.f := by
  unfold oQPT at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact MolMono_of_map Γ (fun c => { c with label := none }) (fun _ => ⟨rfl, rfl, rfl⟩) _
  · refine MolMono_of_map Γ _ (fun c => ?_) _
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- The graph without its labels. -/
theorem molMono_dropLabels (Γ : Graph k n) : Γ.MolMono Γ.dropLabels id :=
  MolMono_of_map Γ (fun c => { c with label := none }) (fun _ => ⟨rfl, rfl, rfl⟩) _

/-- Factors with minor `{u}` moved into the label group `ℓ`. -/
theorem molMono_absorb (ℓ : PQ × Atom k n) (Γ : Graph k n) : Γ.MolMono (Γ.absorb ℓ) id :=
  MolMono_of_map Γ _ (fun c => by split_ifs <;> exact ⟨rfl, rfl, rfl⟩) _

private theorem MolMono_reach_of_rel {α : Type} {r : α → α → Prop} {u v : α} (h : r u v) :
    (SimpleGraph.fromRel r).Reachable u v := by
  by_cases huv : u = v
  · rw [huv]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨huv, Or.inl h⟩)

private theorem MolMono_reach_fromRel {α : Type} {r : α → α → Prop} {H : SimpleGraph α}
    (h : ∀ u v, r u v → H.Reachable u v) {u v : α}
    (hr : (SimpleGraph.fromRel r).Reachable u v) : H.Reachable u v :=
  MolMono_reach_of_adj (fun a b hab => by
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with h' | h'
    · exact h a b h'
    · exact (h b a h').symm) hr

/-- **The removal of a dotted edge** whose ends are joined by the other dotted edges. -/
theorem molMono_dropDot (i : ℕ) (Γ : Graph k n) (c : Comp (Atom k n))
    (hc : Γ.comps[i]? = some c) (hk : c.kind = .dot)
    (hb : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).SameBlock c.x c.y) :
    Γ.MolMono ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ id := by
  set Γ' : Graph k n := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ with hΓ'
  have hp := MolMono_perm_eraseIdx hc
  have hsub : ∀ d ∈ Γ'.comps, d ∈ Γ.comps := fun d hd => List.mem_of_mem_eraseIdx hd
  have hsplit : ∀ d ∈ Γ.comps, d = c ∨ d ∈ Γ'.comps := fun d hd =>
    List.mem_cons.1 (hp.mem_iff.1 hd)
  have hB : ∀ u v, Γ.SameBlock u v ↔ Γ'.SameBlock u v := by
    intro u v
    unfold Graph.SameBlock Graph.dotGraph
    constructor
    · intro h
      refine MolMono_reach_fromRel (fun a b hr => ?_) h
      obtain ⟨d, hd, hdk, hx, hy⟩ := hr
      rcases hsplit d hd with rfl | hd'
      · rw [← hx, ← hy]; exact hb
      · exact MolMono_reach_of_rel ⟨d, hd', hdk, hx, hy⟩
    · intro h
      refine MolMono_reach_fromRel (fun a b hr => ?_) h
      obtain ⟨d, hd, hdk, hx, hy⟩ := hr
      exact MolMono_reach_of_rel ⟨d, hsub d hd, hdk, hx, hy⟩
  have hM : ∀ u v, Γ.SameMol u v ↔ Γ'.SameMol u v := by
    refine MolMono_sameMol_of_reach fun u v => ⟨fun h => ?_, fun h => ?_⟩
    · unfold Graph.molGraph at h
      refine MolMono_reach_fromRel (fun a b hr => ?_) h
      obtain ⟨d, hd, hdk, hx, hy⟩ := hr
      rcases hsplit d hd with rfl | hd'
      · rw [← hx, ← hy]; exact MolMono_mol_of_block Γ' hb
      · exact MolMono_reach_of_rel ⟨d, hd', hdk, hx, hy⟩
    · unfold Graph.molGraph at h
      refine MolMono_reach_fromRel (fun a b hr => ?_) h
      obtain ⟨d, hd, hdk, hx, hy⟩ := hr
      exact MolMono_reach_of_rel ⟨d, hsub d hd, hdk, hx, hy⟩
  refine MolMono_of_perm hB hM (List.Perm.symm ((hp.filterMap _).trans ?_))
  rw [MolMono_filterMap_cons, MolMono_edgeD_dot Γ hk]
  rfl

/-- An atom in the block of the internal atom `b` has, in the block normal form, an atom of the
molecule of `b`. -/
private theorem MolMono_rep_flat_of_block_inr (Γ : Graph k n) {w : Atom k n} {b : Fin n}
    (h : Γ.SameBlock w (.inr b)) : Γ.molRep (Γ.flatAtom w) = Γ.molRep (.inr b) := by
  rcases w with a | a
  · classical
    have hanc : ∃ b', Γ.anchor (.inl a) = some b' ∧ Γ.SameBlock (.inl a) (.inr b') := by
      rw [MolMono_anchor_eq_find]
      cases hf : (List.finRange n).find? fun b' => decide (Γ.SameBlock (.inl a) (.inr b')) with
      | none =>
        exact absurd (List.find?_eq_none.1 hf b (List.mem_finRange b)) (by simpa using h)
      | some b' => exact ⟨b', rfl, by simpa using List.find?_some hf⟩
    obtain ⟨b', hb', hab'⟩ := hanc
    simp only [Graph.flatAtom, hb']
    have hbb : Γ.SameBlock (.inr b') (.inr b) :=
      SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm hab') h
    exact (MolMono_molRep_eq_iff Γ b' b).2 (Or.inr ⟨rfl, rfl, MolMono_mol_of_block Γ hbb⟩)
  · exact (MolMono_molRep_eq_iff Γ a b).2 (Or.inr ⟨rfl, rfl, MolMono_mol_of_block Γ h⟩)

private theorem MolMono_filterMap_set {α β : Type} (D : α → Option β) :
    ∀ (l : List α) (i : ℕ) (c c' : α), l[i]? = some c → D c' = D c →
      (l.set i c').filterMap D = l.filterMap D
  | [], i, c, c', h, _ => by simp at h
  | a :: l, 0, c, c', h, hD => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.set_cons_zero, MolMono_filterMap_cons, MolMono_filterMap_cons, hD]
  | a :: l, i + 1, c, c', h, hD => by
    rw [List.set_cons_succ, MolMono_filterMap_cons, MolMono_filterMap_cons,
      MolMono_filterMap_set D l i c c' (by simpa using h) hD]

end Steps

/-- Under the clause on the external atoms, two atoms of one block have, in the block normal
form, atoms of one molecule. -/
private theorem MolMono_rep_flat_of_block {n : ℕ} (Γ : Graph 3 n) (hE : Γ.ExtClause)
    {u v : Atom 3 n} (hb : Γ.SameBlock u v) :
    Γ.molRep (Γ.flatAtom u) = Γ.molRep (Γ.flatAtom v) := by
  by_cases huv : u = v
  · rw [huv]
  · obtain ⟨b, hub⟩ := hE.1 u v huv hb
    rw [MolMono_rep_flat_of_block_inr Γ hub, MolMono_rep_flat_of_block_inr Γ
      (SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm hb) hub)]

/-- **The move of an end of a component** other than a dotted edge to an atom of its block, under
the clause on the external atoms. -/
theorem molMono_rebase {n : ℕ} (i : ℕ) (Γ : Graph 3 n) (c : Comp (Atom 3 n)) (u v : Atom 3 n)
    (hE : Γ.ExtClause) (hc : Γ.comps[i]? = some c) (hk : c.kind ≠ .dot)
    (hb : Γ.SameBlock u v) :
    Γ.MolMono ⟨Γ.comps.set i
      { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y }, Γ.coeff⟩ id := by
  set c' : Comp (Atom 3 n) :=
    { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y } with hc'
  set Γ' : Graph 3 n := ⟨Γ.comps.set i c', Γ.coeff⟩ with hΓ'
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  have hmem' : c' ∈ Γ'.comps :=
    List.mem_iff_getElem.2 ⟨i, by simp [Γ', hi], by simp [Γ']⟩
  have ha : ∀ d ∈ Γ'.comps, d = c' ∨ d ∈ Γ.comps := fun d hd =>
    (List.mem_or_eq_of_mem_set hd).symm
  have hb' : ∀ d ∈ Γ.comps, d = c ∨ d ∈ Γ'.comps := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hd
    by_cases hji : j = i
    · subst hji; exact Or.inl hci
    · exact Or.inr (List.mem_iff_getElem.2
        ⟨j, by simpa [Γ'] using hj, List.getElem_set_ne (Ne.symm hji) _⟩)
  have hdot : Γ.dotGraph = Γ'.dotGraph := by
    unfold Graph.dotGraph
    congr 1
    funext a b
    apply propext
    constructor
    · rintro ⟨d, hd, hdk, rfl, rfl⟩
      rcases hb' d hd with rfl | hd'
      · exact absurd hdk hk
      · exact ⟨d, hd', hdk, rfl, rfl⟩
    · rintro ⟨d, hd, hdk, rfl, rfl⟩
      rcases ha d hd with rfl | hd'
      · exact absurd hdk hk
      · exact ⟨d, hd', hdk, rfl, rfl⟩
  have hB : ∀ a b, Γ.SameBlock a b ↔ Γ'.SameBlock a b := fun a b => by
    unfold Graph.SameBlock; rw [hdot]
  have hxx : ∀ w, Γ.molGraph.Reachable w (if w = u then v else w) ∧
      Γ'.molGraph.Reachable w (if w = u then v else w) := by
    intro w
    split_ifs with hw
    · subst hw
      exact ⟨MolMono_mol_of_block Γ hb, MolMono_mol_of_block Γ' ((hB _ _).1 hb)⟩
    · exact ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩
  have hM : ∀ a b, Γ.SameMol a b ↔ Γ'.SameMol a b := by
    refine MolMono_sameMol_of_reach fun a b => ⟨fun h => ?_, fun h => ?_⟩
    · unfold Graph.molGraph at h
      refine MolMono_reach_fromRel (fun a b hr => ?_) h
      obtain ⟨d, hd, hdk, hx, hy⟩ := hr
      rcases hb' d hd with rfl | hd'
      · subst hx hy
        have h3 : Γ'.molGraph.Reachable c'.x c'.y := MolMono_reach_of_rel ⟨c', hmem', hdk, rfl, rfl⟩
        exact (hxx d.x).2.trans (h3.trans (hxx d.y).2.symm)
      · exact MolMono_reach_of_rel ⟨d, hd', hdk, hx, hy⟩
    · unfold Graph.molGraph at h
      refine MolMono_reach_fromRel (fun a b hr => ?_) h
      obtain ⟨d, hd, hdk, hx, hy⟩ := hr
      rcases ha d hd with rfl | hd'
      · subst hx hy
        have h3 : Γ.molGraph.Reachable c.x c.y :=
          MolMono_reach_of_rel ⟨c, List.mem_iff_getElem.2 ⟨i, hi, hci⟩, hdk, rfl, rfl⟩
        exact (hxx c.x).1.symm.trans (h3.trans (hxx c.y).1)
      · exact MolMono_reach_of_rel ⟨d, hd', hdk, hx, hy⟩
  have hflat : ∀ w, Γ.molRep (Γ.flatAtom (if w = u then v else w)) =
      Γ.molRep (Γ.flatAtom w) := by
    intro w
    split_ifs with hw
    · rw [hw]; exact (MolMono_rep_flat_of_block Γ hE hb).symm
    · rfl
  have hD : MolMono_edgeD Γ c' = MolMono_edgeD Γ c := by
    change (if c.kind = .dot ∨ Γ.molRep (Γ.flatAtom (if c.x = u then v else c.x)) =
        Γ.molRep (Γ.flatAtom (if c.y = u then v else c.y)) then none
      else c.kind.mclass.map fun m => (Γ.molRep (Γ.flatAtom (if c.x = u then v else c.x)),
        Γ.molRep (Γ.flatAtom (if c.y = u then v else c.y)), m)) = _
    rw [hflat, hflat]
    rfl
  refine MolMono_of_perm hB hM ?_
  change ((Γ.comps.set i c').filterMap (MolMono_edgeD Γ)).Perm _
  rw [MolMono_filterMap_set _ _ _ _ _ hc hD]


/-! ## The two new crossing edges of the path through `x` ([II, Lemma 4.11]) -/

section PathTwo

variable {V : Type} [DecidableEq V] (I X S : Finset V)

/-- An edge with both ends outside `S` crosses nothing. -/
private theorem MolMono_opt_out {u v : V} (hu : u ∉ S) (hv : v ∉ S) (m : MClass)
    (A : List (V × V × MClass)) :
    MolMono_crossL I X S (A ++ MolMono_opt u v m) = MolMono_crossL I X S A ∧
      MolMono_cHatL I X S (A ++ MolMono_opt u v m) = MolMono_cHatL I X S A ∧
      MolMono_redL I X S (A ++ MolMono_opt u v m) = MolMono_redL I X S A := by
  by_cases huv : u = v
  · simp [MolMono_opt, huv]
  · have hT : MolMono_tExtL I X S [(u, v, m)] = ∅ := by
      ext a
      simp [MolMono_mem_tExtL, hu, hv]
    simp only [MolMono_opt, huv, ite_false]
    unfold MolMono_cHatL MolMono_crossL MolMono_cIntL MolMono_redL
    rw [MolMono_tExtL_append, hT, Finset.union_empty]
    simp [List.countP_append, hu, hv]

/-- The path from `u` to `v` through `x ∈ S`, with `u`, `v` outside `S`: two new crossing edges of
the class `m`. -/
private theorem MolMono_path_two {u v x : V} (hu : u ∉ S) (hv : v ∉ S) (hx : x ∈ S) (hxI : x ∈ I)
    (hu' : u ∈ I ∨ u ∈ X) (hv' : v ∈ I ∨ v ∈ X) (m : MClass) (A : List (V × V × MClass)) :
    (m ≠ .minus → MolMono_crossL I X S (A ++ (MolMono_opt u x m ++ MolMono_opt x v m)) =
        MolMono_crossL I X S A + 2) ∧
      (m = .minus → MolMono_redL I X S (A ++ (MolMono_opt u x m ++ MolMono_opt x v m)) =
        MolMono_redL I X S A + 2) ∧
      (m ≠ .minus → u ∈ I → v ∈ I →
        MolMono_cHatL I X S (A ++ (MolMono_opt u x m ++ MolMono_opt x v m)) =
          MolMono_cHatL I X S A + 2) ∧
      (m ≠ .minus → u ∈ I → v ∉ I → v ∉ MolMono_tExtL I X S A →
        MolMono_cHatL I X S (A ++ (MolMono_opt u x m ++ MolMono_opt x v m)) =
          MolMono_cHatL I X S A + 2) := by
  have hux : u ≠ x := fun h => hu (h ▸ hx)
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  have hB : MolMono_opt u x m ++ MolMono_opt x v m = [(u, x, m), (x, v, m)] := by
    simp [MolMono_opt, hux, hxv]
  rw [hB]
  have hxv' : x ∈ I ∨ x ∈ X := Or.inl hxI
  refine ⟨fun hm => ?_, fun hm => ?_, fun hm huI hvI => ?_, fun hm huI hvI hvT => ?_⟩
  · unfold MolMono_crossL
    rw [List.countP_append]
    simp [hm, hu', hv', hxv', hu, hv, hx]
  · unfold MolMono_redL
    rw [List.countP_append]
    simp [hm, hu', hv', hxv', hu, hv, hx]
  · have hT : MolMono_tExtL I X S [(u, x, m), (x, v, m)] = ∅ := by
      ext a
      simp only [MolMono_mem_tExtL, List.mem_cons, List.not_mem_nil, or_false,
        Finset.notMem_empty, iff_false, not_and]
      rintro ⟨-, hai⟩ ⟨t, (rfl | rfl), -, (h | h)⟩ <;> simp_all
    unfold MolMono_cHatL MolMono_cIntL
    rw [MolMono_tExtL_append, hT, Finset.union_empty, List.countP_append]
    simp [hm, hu, hv, hx, huI, hvI, hxI]
    omega
  · have hT : MolMono_tExtL I X S [(u, x, m), (x, v, m)] = {v} := by
      ext a
      simp only [MolMono_mem_tExtL, List.mem_cons, List.not_mem_nil, or_false,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨-, hai⟩, t, rfl | rfl, -, h | h⟩
        · exact absurd (h ▸ huI) hai
        · exact absurd (h ▸ hxI) hai
        · exact absurd (h ▸ hxI) hai
        · exact h.symm
      · rintro rfl
        exact ⟨⟨hv'.resolve_left hvI, hvI⟩, (x, a, m), Or.inr rfl,
          ⟨hm, hxv', hv', Or.inl ⟨hx, hv⟩⟩, Or.inr rfl⟩
    unfold MolMono_cHatL MolMono_cIntL
    rw [MolMono_tExtL_append, hT, List.countP_append,
      Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hvT)]
    simp [hm, hu, hv, hx, huI, hvI, hxI]
    omega

end PathTwo

section SchurTwoGraph

variable {k n : ℕ}

private theorem MolMono_molRep_eq_inl (Γ : Graph k n) {w : Atom k n} {a : Fin k}
    (h : Γ.molRep w = .inl a) : w = .inl a := by
  rcases w with b | b
  · exact h
  · obtain ⟨c, hc, -⟩ := MolMono_molRep_inr Γ b
    rw [hc] at h; cases h

private theorem MolMono_flatAtom_eq_inl (Γ : Graph k n) {w : Atom k n} {a : Fin k}
    (h : Γ.flatAtom w = .inl a) : w = .inl a ∧ Γ.anchor (.inl a) = none := by
  rcases w with b | b
  · simp only [Graph.flatAtom] at h
    cases hb : Γ.anchor (.inl b) with
    | none => rw [hb] at h; cases h; exact ⟨rfl, hb⟩
    | some b' => rw [hb] at h; cases h
  · cases h

private theorem MolMono_edgeD_some (Γ : Graph k n) {d : Comp (Atom k n)}
    {t : Atom k n × Atom k n × MClass} (h : MolMono_edgeD Γ d = some t) :
    d.kind ≠ .dot ∧ d.kind.mclass = some t.2.2 ∧ t.1 = Γ.molRep (Γ.flatAtom d.x) ∧
      t.2.1 = Γ.molRep (Γ.flatAtom d.y) := by
  unfold MolMono_edgeD at h
  split_ifs at h with h1
  · simp only [not_or] at h1
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨h1.1, hm, rfl, rfl⟩

/-- The component `i`, neither waved nor dotted, replaced by components neither waved nor
dotted: the internal vertices are kept, and the present edges are those of the other components
and the pin edges, followed by those of the component or of the new components. -/
private theorem MolMono_edges_eraseIdx_append {Γ : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : Γ.comps[i]? = some c) (hcj : c.kind.joinsMol = false)
    (new : List (Comp (Atom k n))) (hnew : ∀ d ∈ new, d.kind.joinsMol = false) (co : Coeff) :
    (⟨Γ.comps.eraseIdx i ++ new, co⟩ : Graph k n).toMG'.int = Γ.toMG'.int ∧
      (MolMono_edges (⟨Γ.comps.eraseIdx i ++ new, co⟩ : Graph k n)).Perm
        (((Γ.comps.eraseIdx i).filterMap (MolMono_edgeD Γ) ++
          (List.finRange k).filterMap (MolMono_pinD Γ)) ++ new.filterMap (MolMono_edgeD Γ)) ∧
      (MolMono_edges Γ).Perm
        (((Γ.comps.eraseIdx i).filterMap (MolMono_edgeD Γ) ++
          (List.finRange k).filterMap (MolMono_pinD Γ)) ++ (MolMono_edgeD Γ c).toList) := by
  have hp := MolMono_perm_eraseIdx hc
  obtain ⟨hB, hM⟩ := MolMono_same_of_join (Γ₁ := Γ) (Γ₂ := ⟨Γ.comps.eraseIdx i ++ new, co⟩)
    (MolMono_joinSub_of_mem fun d hd hj => by
      rcases List.mem_cons.1 (hp.mem_iff.1 hd) with rfl | hd'
      · rw [hcj] at hj; cases hj
      · exact List.mem_append_left _ hd')
    (MolMono_joinSub_of_mem fun d hd hj => by
      rcases List.mem_append.1 hd with hd' | hd'
      · exact List.mem_of_mem_eraseIdx hd'
      · rw [hnew d hd'] at hj; cases hj)
  refine ⟨(MolMono_int_congr hM).symm, ?_, ?_⟩
  · rw [MolMono_edges, ← MolMono_edgeD_congr hB hM, ← MolMono_pinD_congr hB hM]
    change (((Γ.comps.eraseIdx i ++ new).filterMap (MolMono_edgeD Γ)) ++ _).Perm _
    rw [List.filterMap_append]
    exact MolMono_perm_aux (List.Perm.refl _) _
  · refine MolMono_perm_aux ?_ _
    refine (hp.filterMap _).trans ?_
    rw [MolMono_filterMap_cons]
    exact List.perm_append_comm

/-- The clause `Graph.ColourInvB` at a random component: in the block normal form its first atom
is internal, its second atom is not `⊗`, and it is `⊕` only for a blue and `⊖` only for a red
solid edge. -/
private theorem MolMono_colour {n : ℕ} {Γ : Graph 3 n} (hI : Γ.ColourInvB) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hr : c.kind.isRandom = true) (hk : c.kind ≠ .dot) :
    (Γ.flatAtom c.x).isRight = true ∧ Γ.flatAtom c.y ≠ .inl 0 ∧
      (Γ.flatAtom c.y = .inl 1 → c.kind = .G .plus) ∧
      (Γ.flatAtom c.y = .inl 2 → c.kind = .G .minus) := by
  have h := (hI (Γ.flatComp c) (List.mem_map_of_mem hc)).1
  simp only [Graph.flatComp, hk, ite_false] at h
  exact h hr

/-- No present edge other than that of the component `i` reaches an unpinned `⊕` at which the
component `i` sits, under the clause on the external atoms. -/
private theorem MolMono_plus_untouched {n : ℕ} {Γ : Graph 3 n} (hE : Γ.ExtClause) {i : ℕ}
    {c : Comp (Atom 3 n)} (hc : Γ.comps[i]? = some c) (hk : c.kind ≠ .dot ∧ c.kind ≠ .xdot)
    (hcy : c.x = .inl 1 ∨ c.y = .inl 1) (hun : Γ.anchor (.inl 1) = none) :
    ∀ t ∈ (Γ.comps.eraseIdx i).filterMap (MolMono_edgeD Γ) ++
        (List.finRange 3).filterMap (MolMono_pinD Γ), t.1 ≠ .inl 1 ∧ t.2.1 ≠ .inl 1 := by
  classical
  have hUn : Γ.Unpinned (.inl 1) := by
    refine ⟨rfl, fun b hb => ?_⟩
    rw [MolMono_anchor_eq_find, List.find?_eq_none] at hun
    exact hun b (List.mem_finRange b) (by simpa using hb)
  have hdeg := (hE.2.2.2.2 hUn).2.2
  have hp := MolMono_perm_eraseIdx hc
  have hzero : ∀ d ∈ Γ.comps.eraseIdx i,
      ¬ ((d.x = .inl 1 ∨ d.y = .inl 1) ∧ d.kind ≠ .dot ∧ d.kind ≠ .xdot) := by
    intro d hd hpd
    unfold Graph.nonDotDeg at hdeg
    rw [(hp.filter _).length_eq, List.filter_cons_of_pos (by simpa using ⟨hcy, hk⟩),
      List.length_cons] at hdeg
    have : 0 < ((Γ.comps.eraseIdx i).filter fun d => decide ((d.x = .inl 1 ∨ d.y = .inl 1) ∧
        d.kind ≠ .dot ∧ d.kind ≠ .xdot)).length :=
      List.length_pos_of_mem (List.mem_filter.2 ⟨hd, by simpa using hpd⟩)
    omega
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨d, hd, hdt⟩ := List.mem_filterMap.1 ht
    obtain ⟨hdk, hm, h1, h2⟩ := MolMono_edgeD_some Γ hdt
    have hxd : d.kind ≠ .xdot := fun h => by rw [h] at hm; cases hm
    refine ⟨fun h => hzero d hd ⟨Or.inl ?_, hdk, hxd⟩, fun h => hzero d hd ⟨Or.inr ?_, hdk, hxd⟩⟩
    · rw [h1] at h
      exact (MolMono_flatAtom_eq_inl Γ (MolMono_molRep_eq_inl Γ h)).1
    · rw [h2] at h
      exact (MolMono_flatAtom_eq_inl Γ (MolMono_molRep_eq_inl Γ h)).1
  · obtain ⟨a, -, hat⟩ := List.mem_filterMap.1 ht
    unfold MolMono_pinD at hat
    cases hb : Γ.anchor (.inl a) with
    | none => rw [hb] at hat; cases hat
    | some b =>
      rw [hb] at hat
      cases hat
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨b', hb', -⟩ := MolMono_molRep_inr Γ b
        simp only [hb'] at h
        cases h
      · simp only [Sum.inl.injEq] at h
        subst h
        rw [hun] at hb
        cases hb

end SchurTwoGraph

/-- **The path of [II, Lemma 4.11] adds two crossing edges.** Let the component `i` of `Γ` be the
solid edge `c = G_{ab}` of charge `ch`, and let `Γ'` be the second term of [II, (4.17)] (or
[II, (4.20)]) at an internal atom `x`, with `G_{ax} G_{xb} (G_{xx})⁻¹` in place of `c`. For a set
`S` of internal molecules containing the molecule of `x` and not those of `a`, `b` (in the block
normal form): for `ch = plus` the crossing count and `MGraph.cHat` of `S` rise by `2`; for
`ch = minus` the red crossing count of `S` rises by `2`. -/
theorem schur_add_two {n : ℕ} (Γ : Graph 3 n) (x : Atom 3 n) (i : ℕ) (c : Comp (Atom 3 n))
    (ch : Charge) (co : Coeff) (hc : Γ.comps[i]? = some c) (hk : c.kind = .G ch)
    (hI : Γ.InvB') (hx : x.isRight = true) (S : Finset (Atom 3 n)) (_hS : S ⊆ Γ.toMG'.int)
    (hxS : Γ.molRep x ∈ S) (hu : Γ.molRep (Γ.flatAtom c.x) ∉ S)
    (hv : Γ.molRep (Γ.flatAtom c.y) ∉ S) :
    (ch = .plus →
      (⟨Γ.comps.eraseIdx i ++ [{ solidC ch c.x x with label := c.label },
        { solidC ch x c.y with label := c.label }, { mkC (.inv ch) x x with label := c.label }],
        co⟩ : Graph 3 n).toMG'.crossCount S = Γ.toMG'.crossCount S + 2 ∧
      (⟨Γ.comps.eraseIdx i ++ [{ solidC ch c.x x with label := c.label },
        { solidC ch x c.y with label := c.label }, { mkC (.inv ch) x x with label := c.label }],
        co⟩ : Graph 3 n).toMG'.cHat S = Γ.toMG'.cHat S + 2) ∧
    (ch = .minus →
      (⟨Γ.comps.eraseIdx i ++ [{ solidC ch c.x x with label := c.label },
        { solidC ch x c.y with label := c.label }, { mkC (.inv ch) x x with label := c.label }],
        co⟩ : Graph 3 n).toMG'.redCount S = Γ.toMG'.redCount S + 2) := by
  set new : List (Comp (Atom 3 n)) := [{ solidC ch c.x x with label := c.label },
    { solidC ch x c.y with label := c.label }, { mkC (.inv ch) x x with label := c.label }]
  have hnew : ∀ d ∈ new, d.kind.joinsMol = false := by
    intro d hd
    simp only [new, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact MolMono_solidC_join _ _ _ _
    · exact MolMono_solidC_join _ _ _ _
    · rfl
  obtain ⟨hInt, hp₂, hp₁⟩ := MolMono_edges_eraseIdx_append hc (by rw [hk]; rfl) new hnew co
  have hF : Γ.flatAtom x = x := by
    cases x with
    | inl a => cases hx
    | inr a => rfl
  have hxI : Γ.molRep (Γ.flatAtom x) ∈ Γ.toMG'.int := MolMono_rep_flat_int Γ hx
  have hxS' : Γ.molRep (Γ.flatAtom x) ∈ S := by rw [hF]; exact hxS
  have hN : new.filterMap (MolMono_edgeD Γ) =
      MolMono_opt (Γ.molRep (Γ.flatAtom c.x)) (Γ.molRep (Γ.flatAtom x)) (MolMono_chClass ch) ++
        MolMono_opt (Γ.molRep (Γ.flatAtom x)) (Γ.molRep (Γ.flatAtom c.y))
          (MolMono_chClass ch) := by
    simp only [new]
    rw [MolMono_filterMap_cons, MolMono_filterMap_cons, MolMono_filterMap_single,
      MolMono_edgeD_solidC, MolMono_edgeD_solidC,
      MolMono_edgeD_none Γ (c := { mkC (.inv ch) x x with label := c.label }) rfl]
    simp
  set A := (Γ.comps.eraseIdx i).filterMap (MolMono_edgeD Γ) ++
    (List.finRange 3).filterMap (MolMono_pinD Γ)
  have hcD := MolMono_edgeD_G Γ hk
  have hout := MolMono_opt_out Γ.toMG'.int Γ.toMG'.ext S hu hv (MolMono_chClass ch) A
  have htwo := MolMono_path_two Γ.toMG'.int Γ.toMG'.ext S hu hv hxS' hxI
    (MolMono_molRep_isVtx Γ _) (MolMono_molRep_isVtx Γ _) (MolMono_chClass ch) A
  rw [hN] at hp₂
  rw [hcD] at hp₁
  refine ⟨fun hch => ?_, fun hch => ?_⟩
  · subst hch
    have hm : MolMono_chClass Charge.plus ≠ .minus := by simp [MolMono_chClass]
    have hmem : c ∈ Γ.comps := List.mem_of_getElem? hc
    obtain ⟨hcx, hc0, hc1, hc2⟩ := MolMono_colour hI.2.1 hmem (by rw [hk]; rfl)
      (by rw [hk]; simp)
    have huI : Γ.molRep (Γ.flatAtom c.x) ∈ Γ.toMG'.int := by
      rcases hw : Γ.flatAtom c.x with a | a
      · rw [hw] at hcx; cases hcx
      · exact MolMono_molRep_mem_int Γ a
    refine ⟨?_, ?_⟩
    · rw [MolMono_crossCount_eq, MolMono_crossCount_eq, hInt,
        MolMono_crossL_perm _ _ _ hp₂, MolMono_crossL_perm _ _ _ hp₁, hout.1]
      exact htwo.1 hm
    · rw [MolMono_cHat_eq, MolMono_cHat_eq, hInt,
        MolMono_cHatL_perm _ _ _ hp₂, MolMono_cHatL_perm _ _ _ hp₁, hout.2.1]
      have hExt : (⟨Γ.comps.eraseIdx i ++ new, co⟩ : Graph 3 n).toMG'.ext = Γ.toMG'.ext := rfl
      rw [hExt]
      have key : (Γ.flatAtom c.y).isRight = true ∨ Γ.flatAtom c.y = .inl 1 := by
        rcases hw : Γ.flatAtom c.y with a | a
        · right
          fin_cases a
          · exact absurd hw hc0
          · rfl
          · exact absurd (hc2 hw) (by rw [hk]; simp)
        · left; rfl
      rcases key with hw | hw
      · refine htwo.2.2.1 hm huI ?_
        rcases hw' : Γ.flatAtom c.y with a | a
        · rw [hw'] at hw; cases hw
        · exact MolMono_molRep_mem_int Γ a
      · obtain ⟨hcy, hun⟩ := MolMono_flatAtom_eq_inl Γ hw
        have hvI : Γ.molRep (Γ.flatAtom c.y) ∉ Γ.toMG'.int := by
          rw [hw]; exact MolMono_inl_not_mem_int Γ 1
        refine htwo.2.2.2 hm huI hvI ?_
        intro hT
        obtain ⟨-, t, ht, -, htv⟩ := (MolMono_mem_tExtL _ _ _ _ _).1 hT
        have := MolMono_plus_untouched hI.2.2.1 hc ⟨by rw [hk]; simp, by rw [hk]; simp⟩
          (Or.inr hcy) hun t ht
        rw [hw] at htv
        rcases htv with h | h
        · exact this.1 h
        · exact this.2 h
  · subst hch
    rw [MolMono_redCount_eq, MolMono_redCount_eq, hInt,
      MolMono_redL_perm _ _ _ hp₂, MolMono_redL_perm _ _ _ hp₁, hout.2.2]
    exact htwo.2.1 rfl

/-- **The path of [II, Lemma 4.11] at a weight adds two crossing edges.** Let the component `i`
of `Γ` be a weight or light weight `c` of charge `ch` on `a`, and let `Γ'` be the second term of
[II, (4.17)] (or [II, (4.20)]) at the atom `x`, with `G_{ax} G_{xa} (G_{xx})⁻¹` in place of `c`.
For a set `S` of internal molecules containing the molecule of `x` and not that of `a` (in the
block normal form): for `ch = plus` the crossing count and `MGraph.cHat` of `S` rise by `2`; for
`ch = minus` the red crossing count of `S` rises by `2`. -/
theorem schurW_add_two {n : ℕ} (Γ : Graph 3 n) (x : Atom 3 n) (i : ℕ) (c : Comp (Atom 3 n))
    (ch : Charge) (co : Coeff) (hc : Γ.comps[i]? = some c)
    (hk : c.kind = .weight ch ∨ c.kind = .light ch)
    (hI : Γ.InvB') (hx : x.isRight = true) (S : Finset (Atom 3 n)) (_hS : S ⊆ Γ.toMG'.int)
    (hxS : Γ.molRep x ∈ S) (hu : Γ.molRep (Γ.flatAtom c.x) ∉ S) :
    (ch = .plus →
      (⟨Γ.comps.eraseIdx i ++ [{ mkC (.G ch) c.x x with label := c.label },
        { mkC (.G ch) x c.x with label := c.label }, { mkC (.inv ch) x x with label := c.label }],
        co⟩ : Graph 3 n).toMG'.crossCount S = Γ.toMG'.crossCount S + 2 ∧
      (⟨Γ.comps.eraseIdx i ++ [{ mkC (.G ch) c.x x with label := c.label },
        { mkC (.G ch) x c.x with label := c.label }, { mkC (.inv ch) x x with label := c.label }],
        co⟩ : Graph 3 n).toMG'.cHat S = Γ.toMG'.cHat S + 2) ∧
    (ch = .minus →
      (⟨Γ.comps.eraseIdx i ++ [{ mkC (.G ch) c.x x with label := c.label },
        { mkC (.G ch) x c.x with label := c.label }, { mkC (.inv ch) x x with label := c.label }],
        co⟩ : Graph 3 n).toMG'.redCount S = Γ.toMG'.redCount S + 2) := by
  set new : List (Comp (Atom 3 n)) := [{ mkC (.G ch) c.x x with label := c.label },
    { mkC (.G ch) x c.x with label := c.label }, { mkC (.inv ch) x x with label := c.label }]
  have hnew : ∀ d ∈ new, d.kind.joinsMol = false := by
    intro d hd
    simp only [new, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> rfl
  have hcj : c.kind.joinsMol = false := by rcases hk with h | h <;> rw [h] <;> rfl
  obtain ⟨hInt, hp₂, hp₁⟩ := MolMono_edges_eraseIdx_append hc hcj new hnew co
  have hF : Γ.flatAtom x = x := by
    cases x with
    | inl a => cases hx
    | inr a => rfl
  have hxI : Γ.molRep (Γ.flatAtom x) ∈ Γ.toMG'.int := MolMono_rep_flat_int Γ hx
  have hxS' : Γ.molRep (Γ.flatAtom x) ∈ S := by rw [hF]; exact hxS
  have hGD : ∀ a b : Atom 3 n, (MolMono_edgeD Γ { mkC (.G ch) a b with label := c.label }).toList =
      MolMono_opt (Γ.molRep (Γ.flatAtom a)) (Γ.molRep (Γ.flatAtom b)) (MolMono_chClass ch) :=
    fun a b => MolMono_edgeD_G Γ (c := { mkC (.G ch) a b with label := c.label }) rfl
  have hN : new.filterMap (MolMono_edgeD Γ) =
      MolMono_opt (Γ.molRep (Γ.flatAtom c.x)) (Γ.molRep (Γ.flatAtom x)) (MolMono_chClass ch) ++
        MolMono_opt (Γ.molRep (Γ.flatAtom x)) (Γ.molRep (Γ.flatAtom c.x))
          (MolMono_chClass ch) := by
    simp only [new]
    rw [MolMono_filterMap_cons, MolMono_filterMap_cons, MolMono_filterMap_single, hGD, hGD,
      MolMono_edgeD_none Γ (c := { mkC (.inv ch) x x with label := c.label }) rfl]
    simp
  have hcD : MolMono_edgeD Γ c = none :=
    MolMono_edgeD_none Γ (by rcases hk with h | h <;> rw [h] <;> rfl)
  set A := (Γ.comps.eraseIdx i).filterMap (MolMono_edgeD Γ) ++
    (List.finRange 3).filterMap (MolMono_pinD Γ)
  have htwo := MolMono_path_two Γ.toMG'.int Γ.toMG'.ext S hu hu hxS' hxI
    (MolMono_molRep_isVtx Γ _) (MolMono_molRep_isVtx Γ _) (MolMono_chClass ch) A
  rw [hN] at hp₂
  rw [hcD, Option.toList_none, List.append_nil] at hp₁
  have hmem : c ∈ Γ.comps := List.mem_of_getElem? hc
  have hcx := (MolMono_colour hI.2.1 hmem (by rcases hk with h | h <;> rw [h] <;> rfl)
    (by rcases hk with h | h <;> rw [h] <;> simp)).1
  have huI : Γ.molRep (Γ.flatAtom c.x) ∈ Γ.toMG'.int := by
    rcases hw : Γ.flatAtom c.x with a | a
    · rw [hw] at hcx; cases hcx
    · exact MolMono_molRep_mem_int Γ a
  refine ⟨fun hch => ?_, fun hch => ?_⟩
  · subst hch
    have hm : MolMono_chClass Charge.plus ≠ .minus := by simp [MolMono_chClass]
    refine ⟨?_, ?_⟩
    · rw [MolMono_crossCount_eq, MolMono_crossCount_eq, hInt,
        MolMono_crossL_perm _ _ _ hp₂, MolMono_crossL_perm _ _ _ hp₁]
      exact htwo.1 hm
    · rw [MolMono_cHat_eq, MolMono_cHat_eq, hInt,
        MolMono_cHatL_perm _ _ _ hp₂, MolMono_cHatL_perm _ _ _ hp₁]
      exact htwo.2.2.1 hm huI huI
  · subst hch
    rw [MolMono_redCount_eq, MolMono_redCount_eq, hInt,
      MolMono_redL_perm _ _ _ hp₂, MolMono_redL_perm _ _ _ hp₁]
    exact htwo.2.1 rfl

/-- **The corollary of monotonicity**: under the invariant `Graph.InvB'` of the first graph
(whose molecular graph is then doubly connected), every proper isolated subset ([II, Def 5.2]) of
the molecular graph of the second graph pulls back to a proper isolated subset, with at least as
many red crossing edges. -/
theorem Graph.MolMono.pull_properIso {n m : ℕ} {Γ₁ : Graph 3 n} {Γ₂ : Graph 3 m}
    {φ : Atom 3 n → Atom 3 m} (h : Γ₁.MolMono Γ₂ φ) (hI : Γ₁.InvB')
    {P₂ : Finset (Atom 3 m)} (hP : Γ₂.toMG'.IsProperIso Γ₂.toMG'.int P₂) :
    Γ₁.toMG'.IsProperIso Γ₁.toMG'.int (Γ₁.molPull Γ₂ φ P₂) ∧
      Γ₁.toMG'.redCount (Γ₁.molPull Γ₂ φ P₂) ≤ Γ₂.toMG'.redCount P₂ :=
  MolMono_pull_properIso_of_DC h hI.1.1 hP

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

section SPDHelpers

variable {V E : Type}

end SPDHelpers

end Instances

end RBM8D.Graphs
