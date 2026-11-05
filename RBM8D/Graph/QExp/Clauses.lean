import RBM8D.Graph.MolRead

/-!
# The clauses of the invariant of [II, Lemma 5.13] along the `Q`-expansions

Every elementary step of the `Q`-expansions keeps the charge pattern of the block normal form,
the clause on the external atoms, the absence of ghost edges and the internal label atoms, on
graphs with the invariant `Graph.InvB'`.
-/

noncomputable section

set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The clauses read through the unidentified external atoms -/

section Abstract

/-- The kind and the two ends of a component. -/
private abbrev KT (n : ℕ) : Type := Kind × Atom 3 n × Atom 3 n

/-- The kind of a component and, for each end, the external atom it is if that atom is not
identified with an internal atom (`none` otherwise). -/
private abbrev AC : Type := Kind × Option (Fin 3) × Option (Fin 3)

open Classical in
/-- The external atom `a` if `u = a` and `us a` holds, `none` otherwise. -/
private def side {n : ℕ} (us : Fin 3 → Prop) : Atom 3 n → Option (Fin 3)
  | .inl a => if us a then some a else none
  | .inr _ => none

@[simp] private theorem side_inr {n : ℕ} (us : Fin 3 → Prop) (b : Fin n) :
    side us (.inr b : Atom 3 n) = none := rfl

private theorem side_inl_pos {n : ℕ} {us : Fin 3 → Prop} {a : Fin 3} (h : us a) :
    side us (.inl a : Atom 3 n) = some a := by
  simp [side, h]

private theorem side_inl_neg {n : ℕ} {us : Fin 3 → Prop} {a : Fin 3} (h : ¬ us a) :
    side us (.inl a : Atom 3 n) = none := by
  simp [side, h]

private theorem side_eq_some {n : ℕ} {us : Fin 3 → Prop} {u : Atom 3 n} {a : Fin 3} :
    side us u = some a ↔ u = .inl a ∧ us a := by
  rcases u with b | b
  · by_cases h : us b
    · rw [side_inl_pos h]
      constructor
      · rintro ⟨⟩; exact ⟨rfl, h⟩
      · rintro ⟨hu, -⟩; cases hu; rfl
    · rw [side_inl_neg h]
      constructor
      · rintro ⟨⟩
      · rintro ⟨hu, h'⟩; cases hu; exact absurd h' h
  · simp

/-- A component with the external atoms of its ends recorded. -/
private def strip {n : ℕ} (c : Comp (Atom 3 n)) : KT n := (c.kind, c.x, c.y)

/-- A component without its ends, read through `side us`. -/
private def absT {n : ℕ} (us : Fin 3 → Prop) (p : KT n) : AC :=
  (p.1, side us p.2.1, side us p.2.2)

/-- A component other than a dotted or `×`-dotted edge with an end at an unidentified external
atom. -/
private def touch (p : AC) : Bool :=
  p.1 != .dot && p.1 != .xdot && (p.2.1.isSome || p.2.2.isSome)

/-- The charge pattern and the clause on `×`-dotted edges for one component. -/
private def elemOK (p : AC) : Prop :=
  (p.1.isRandom = true → p.2.1 = none ∧ p.2.2 ≠ some 0 ∧ (p.2.2 = some 1 → p.1 = .G .plus) ∧
    (p.2.2 = some 2 → p.1 = .G .minus)) ∧
  (p.1 = .waved .s → p.2.1 = none ∧ p.2.2 = none) ∧
  (p.1 = .xdot → p.2.1 = none ∨ p.2.2 = none)

/-- The component has an end at the external atom `a`. -/
private abbrev atA (a : Fin 3) (p : AC) : Prop := p.2.1 = some a ∨ p.2.2 = some a

/-- Every diffusive component at `a` ends at an identified atom. -/
private def DiffP (a : Fin 3) (L : List AC) : Prop :=
  ∀ p ∈ L, p.1.isDiffusive = true →
    (p.2.1 = some a → p.2.2 = none) ∧ (p.2.2 = some a → p.2.1 = none)

/-- Some diffusive component joins `a` to an identified atom. -/
private def HasDiffP (a : Fin 3) (L : List AC) : Prop :=
  ∃ p ∈ L, p.1.isDiffusive = true ∧ (p.2.1 = some a ∧ p.2.2 = none ∨ p.2.2 = some a ∧ p.2.1 = none)

/-- The number of components at `a`. -/
private def degA (a : Fin 3) (L : List AC) : ℕ := (L.filter fun p => decide (atA a p)).length

/-- The counting clauses at `⊗`, `⊖`, `⊕` on the list of components with an end at an
unidentified external atom. -/
private def AbsT (us : Fin 3 → Prop) (L : List AC) : Prop :=
  (us 0 → HasDiffP 0 L ∧ DiffP 0 L) ∧
  (us 2 → (∀ p ∈ L, p.1.isDiffusive = true → ¬ atA 2 p) ∧ degA 2 L ≤ 1) ∧
  (us 1 → ((∃ p ∈ L, p.1 = .G .plus ∧ atA 1 p) ∨ HasDiffP 1 L) ∧ DiffP 1 L ∧ degA 1 L ≤ 1)

private theorem AbsT_perm {us : Fin 3 → Prop} {L L' : List AC} (hp : L.Perm L') (h : AbsT us L) :
    AbsT us L' := by
  obtain ⟨h0, h2, h1⟩ := h
  have hm : ∀ p, p ∈ L ↔ p ∈ L' := fun p => hp.mem_iff
  have hd : ∀ a, degA a L = degA a L' := fun a => (hp.filter _).length_eq
  refine ⟨fun hu => ?_, fun hu => ?_, fun hu => ?_⟩
  · obtain ⟨⟨p, hpL, hp'⟩, hD⟩ := h0 hu
    exact ⟨⟨p, (hm p).1 hpL, hp'⟩, fun p hpL => hD p ((hm p).2 hpL)⟩
  · obtain ⟨hD, hc⟩ := h2 hu
    exact ⟨fun p hpL => hD p ((hm p).2 hpL), hd 2 ▸ hc⟩
  · obtain ⟨hE, hD, hc⟩ := h1 hu
    refine ⟨?_, fun p hpL => hD p ((hm p).2 hpL), hd 1 ▸ hc⟩
    rcases hE with ⟨p, hpL, hp'⟩ | ⟨p, hpL, hp'⟩
    · exact Or.inl ⟨p, (hm p).1 hpL, hp'⟩
    · exact Or.inr ⟨p, (hm p).1 hpL, hp'⟩

/-- The unidentified external atoms of a graph. -/
private def usG {n : ℕ} (Γ : Graph 3 n) : Fin 3 → Prop := fun a => Γ.Unpinned (.inl a)

/-- A component of `Γ` read through the unidentified external atoms of `Γ`. -/
private def absG {n : ℕ} (Γ : Graph 3 n) (c : Comp (Atom 3 n)) : AC := absT (usG Γ) (strip c)

/-- The components of `Γ` with an end at an unidentified external atom. -/
private def tL {n : ℕ} (Γ : Graph 3 n) : List AC := (Γ.comps.map (strip)).map (absT (usG Γ))
  |>.filter touch

/-- Every block with two or more atoms contains an internal atom. -/
private def E1a {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∀ u v : Atom 3 n, u ≠ v → Γ.SameBlock u v → ∃ b : Fin n, Γ.SameBlock u (.inr b)

/-- The four clauses in the reading through the unidentified external atoms. -/
private def Rep {n : ℕ} (Γ : Graph 3 n) : Prop :=
  E1a Γ ∧ (∀ c ∈ Γ.comps, elemOK (absG Γ c)) ∧ AbsT (usG Γ) (tL Γ) ∧ Γ.NoGhost ∧ Γ.LabelsInt

private theorem side_usG_none {n : ℕ} (Γ : Graph 3 n) (u : Atom 3 n) :
    side (usG Γ) u = none ↔ ¬ Γ.Unpinned u := by
  rcases u with a | b
  · by_cases h : usG Γ a
    · rw [side_inl_pos h]; simp only [reduceCtorEq, false_iff, not_not]; exact h
    · rw [side_inl_neg h]; simp only [true_iff]; exact h
  · simp [Graph.Unpinned]

private theorem side_usG_some {n : ℕ} (Γ : Graph 3 n) (u : Atom 3 n) (a : Fin 3) :
    side (usG Γ) u = some a ↔ u = .inl a ∧ Γ.Unpinned u := by
  rw [side_eq_some]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩

private theorem anchor_eq_none {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Γ.anchor u = none ↔ ∀ b : Fin n, ¬ Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor
  rw [List.find?_eq_none]
  simp

private theorem anchor_some {k n : ℕ} {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.anchor u = some b) : Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor at h
  have hb := List.find?_some h
  exact of_decide_eq_true hb

private theorem flatAtom_isRight {n : ℕ} (Γ : Graph 3 n) (u : Atom 3 n) :
    (Γ.flatAtom u).isRight = true ↔ side (usG Γ) u = none := by
  rw [side_usG_none]
  rcases u with a | b
  · rcases h : Γ.anchor (.inl a) with _ | b
    · simp only [Graph.flatAtom, h, Sum.isRight_inl, Bool.false_eq_true, false_iff, not_not]
      exact ⟨rfl, (anchor_eq_none Γ _).1 h⟩
    · simp only [Graph.flatAtom, h, Sum.isRight_inr, true_iff]
      exact fun hu => hu.2 b (anchor_some h)
  · simp [Graph.flatAtom, Graph.Unpinned]

private theorem flatAtom_inl {n : ℕ} (Γ : Graph 3 n) (u : Atom 3 n) (a : Fin 3) :
    Γ.flatAtom u = .inl a ↔ side (usG Γ) u = some a := by
  rw [side_usG_some]
  rcases u with a' | b
  · rcases h : Γ.anchor (.inl a') with _ | b
    · simp only [Graph.flatAtom, h, Sum.inl.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, rfl, (anchor_eq_none Γ _).1 h⟩
      · intro h'; obtain ⟨h'', -⟩ := h'; simpa using h''
    · simp only [Graph.flatAtom, h, reduceCtorEq, false_iff, not_and]
      exact fun _ hu => hu.2 b (anchor_some h)
  · simp [Graph.flatAtom, Graph.Unpinned]

private theorem mem_tL {n : ℕ} {Γ : Graph 3 n} {p : AC} :
    p ∈ tL Γ ↔ ∃ c ∈ Γ.comps, absG Γ c = p ∧ touch p = true := by
  simp only [tL, List.mem_filter, List.map_map, List.mem_map, Function.comp_def]
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, ht⟩; exact ⟨c, hc, rfl, ht⟩
  · rintro ⟨c, hc, rfl, ht⟩; exact ⟨⟨c, hc, rfl⟩, ht⟩

private theorem degA_tL {n : ℕ} (Γ : Graph 3 n) (a : Fin 3) (ha : usG Γ a) :
    degA a (tL Γ) = Γ.nonDotDeg (.inl a) := by
  unfold degA tL Graph.nonDotDeg
  rw [List.filter_filter, List.map_map, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro c _
  have hx : side (usG Γ) c.x = some a ↔ c.x = .inl a := by
    rw [side_eq_some]; exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩
  have hy : side (usG Γ) c.y = some a ↔ c.y = .inl a := by
    rw [side_eq_some]; exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩
  simp only [Function.comp_def, absT, strip, atA, touch, hx, hy]
  by_cases h1 : c.x = .inl a
  · simp [h1, side_inl_pos (n := n) ha]
    tauto
  · by_cases h2 : c.y = .inl a
    · simp [h1, h2, side_inl_pos (n := n) ha]
      tauto
    · simp [h1, h2]

private theorem side_some_iff {n : ℕ} {Γ : Graph 3 n} {a : Fin 3} (ha : usG Γ a) (u : Atom 3 n) :
    side (usG Γ) u = some a ↔ u = .inl a := by
  rw [side_eq_some]; exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩

private theorem touch_of_some {p : AC} (h1 : p.1 ≠ .dot) (h2 : p.1 ≠ .xdot)
    (h : p.2.1.isSome = true ∨ p.2.2.isSome = true) : touch p = true := by
  unfold touch
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨⟨by simpa using h1, by simpa using h2⟩, h⟩

private theorem diff_ne_dot {κ : Kind} (h : κ.isDiffusive = true) : κ ≠ .dot ∧ κ ≠ .xdot := by
  constructor <;> (intro he; rw [he] at h; simp [Kind.isDiffusive] at h)

private theorem hasDiff_iff {n : ℕ} {Γ : Graph 3 n} {a : Fin 3} (ha : usG Γ a) :
    Γ.HasDiffToPinned (.inl a) ↔ HasDiffP a (tL Γ) := by
  simp only [Graph.HasDiffToPinned, HasDiffP, mem_tL]
  constructor
  · rintro ⟨c, hc, hd, h⟩
    refine ⟨absG Γ c, ⟨c, hc, rfl, ?_⟩, hd, ?_⟩
    · obtain ⟨h1, h2⟩ := diff_ne_dot hd
      refine touch_of_some h1 h2 ?_
      rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · left; simp [absG, absT, strip, (side_some_iff ha _).2 h]
      · right; simp [absG, absT, strip, (side_some_iff ha _).2 h]
    · simp only [absG, absT, strip, side_some_iff ha, side_usG_none]
      exact h
  · rintro ⟨p, ⟨c, hc, rfl, -⟩, hd, h⟩
    refine ⟨c, hc, hd, ?_⟩
    simp only [absG, absT, strip, side_some_iff ha, side_usG_none] at h
    exact h

private theorem diffTo_iff {n : ℕ} {Γ : Graph 3 n} {a : Fin 3} (ha : usG Γ a) :
    Γ.DiffToPinned (.inl a) ↔ DiffP a (tL Γ) := by
  simp only [Graph.DiffToPinned, DiffP, mem_tL]
  constructor
  · rintro h p ⟨c, hc, rfl, -⟩ hd
    simp only [absG, absT, strip, side_some_iff ha, side_usG_none]
    exact h c hc hd
  · intro h c hc hd
    by_cases ht : touch (absG Γ c) = true
    · have := h _ ⟨c, hc, rfl, ht⟩ hd
      simp only [absG, absT, strip, side_some_iff ha, side_usG_none] at this
      exact this
    · obtain ⟨h1, h2⟩ := diff_ne_dot hd
      have hn : ¬ ((side (usG Γ) c.x).isSome = true ∨ (side (usG Γ) c.y).isSome = true) :=
        fun h' => ht (touch_of_some h1 h2 h')
      simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
        at hn
      refine ⟨fun hx => ?_, fun hy => ?_⟩
      · rw [← side_some_iff ha] at hx; rw [hx] at hn; simp at hn
      · rw [← side_some_iff ha] at hy; rw [hy] at hn; simp at hn

private theorem e3_iff {n : ℕ} {Γ : Graph 3 n} {a : Fin 3} (ha : usG Γ a) :
    (∀ c ∈ Γ.comps, c.kind.isDiffusive = true → c.x ≠ .inl a ∧ c.y ≠ .inl a) ↔
      ∀ p ∈ tL Γ, p.1.isDiffusive = true → ¬ atA a p := by
  simp only [mem_tL]
  constructor
  · rintro h p ⟨c, hc, rfl, -⟩ hd
    simp only [atA, absG, absT, strip, side_some_iff ha, not_or]
    exact h c hc hd
  · intro h c hc hd
    obtain ⟨h1, h2⟩ := diff_ne_dot hd
    by_cases ht : touch (absG Γ c) = true
    · have := h _ ⟨c, hc, rfl, ht⟩ hd
      simp only [atA, absG, absT, strip, side_some_iff ha, not_or] at this
      exact this
    · constructor
      · intro hx; apply ht; refine touch_of_some h1 h2 (Or.inl ?_)
        simp [absG, absT, strip, (side_some_iff ha _).2 hx]
      · intro hy; apply ht; refine touch_of_some h1 h2 (Or.inr ?_)
        simp [absG, absT, strip, (side_some_iff ha _).2 hy]

private theorem gplus_iff {n : ℕ} {Γ : Graph 3 n} {a : Fin 3} (ha : usG Γ a) :
    (∃ c ∈ Γ.comps, c.kind = .G .plus ∧ (c.x = .inl a ∨ c.y = .inl a)) ↔
      ∃ p ∈ tL Γ, p.1 = .G .plus ∧ atA a p := by
  simp only [mem_tL]
  constructor
  · rintro ⟨c, hc, hk, h⟩
    refine ⟨absG Γ c, ⟨c, hc, rfl, ?_⟩, hk, ?_⟩
    · refine touch_of_some (by simp [absG, absT, strip, hk]) (by simp [absG, absT, strip, hk]) ?_
      rcases h with h | h
      · left; simp [absG, absT, strip, (side_some_iff ha _).2 h]
      · right; simp [absG, absT, strip, (side_some_iff ha _).2 h]
    · simp only [atA, absG, absT, strip, side_some_iff ha]
      exact h
  · rintro ⟨p, ⟨c, hc, rfl, -⟩, hk, h⟩
    simp only [atA, absG, absT, strip, side_some_iff ha] at h hk
    exact ⟨c, hc, hk, h⟩

/-- The charge pattern of one component of the block normal form, read through the unidentified
external atoms. -/
private theorem flat_iff {n : ℕ} (Γ : Graph 3 n) (c : Comp (Atom 3 n)) :
    (((Γ.flatComp c).kind.isRandom = true → (Γ.flatComp c).x.isRight = true ∧
        (Γ.flatComp c).y ≠ .inl 0 ∧ ((Γ.flatComp c).y = .inl 1 → (Γ.flatComp c).kind = .G .plus) ∧
        ((Γ.flatComp c).y = .inl 2 → (Γ.flatComp c).kind = .G .minus)) ∧
      ((Γ.flatComp c).kind = .waved .s → (Γ.flatComp c).x.isRight = true ∧
        (Γ.flatComp c).y.isRight = true)) ↔
    (((absG Γ c).1.isRandom = true → (absG Γ c).2.1 = none ∧ (absG Γ c).2.2 ≠ some 0 ∧
        ((absG Γ c).2.2 = some 1 → (absG Γ c).1 = .G .plus) ∧
        ((absG Γ c).2.2 = some 2 → (absG Γ c).1 = .G .minus)) ∧
      ((absG Γ c).1 = .waved .s → (absG Γ c).2.1 = none ∧ (absG Γ c).2.2 = none)) := by
  by_cases hk : c.kind = .dot
  · simp [Graph.flatComp, hk, absG, absT, strip, Kind.isRandom]
  · simp only [Graph.flatComp, hk, ↓reduceIte]
    simp only [absG, absT, strip, ne_eq, flatAtom_inl, flatAtom_isRight]

private theorem clauses_rep {n : ℕ} (Γ : Graph 3 n) :
    (Γ.ColourInvB ∧ Γ.ExtClause ∧ Γ.NoGhost ∧ Γ.LabelsInt) ↔ Rep Γ := by
  have hcol : Γ.ColourInvB ↔ ∀ c ∈ Γ.comps,
      (((absG Γ c).1.isRandom = true → (absG Γ c).2.1 = none ∧ (absG Γ c).2.2 ≠ some 0 ∧
        ((absG Γ c).2.2 = some 1 → (absG Γ c).1 = .G .plus) ∧
        ((absG Γ c).2.2 = some 2 → (absG Γ c).1 = .G .minus)) ∧
      ((absG Γ c).1 = .waved .s → (absG Γ c).2.1 = none ∧ (absG Γ c).2.2 = none)) := by
    unfold Graph.ColourInvB Graph.ColourInv' Graph.blockNorm
    simp only [List.forall_mem_map]
    exact forall₂_congr fun c _ => flat_iff Γ c
  have hx : (∀ c ∈ Γ.comps, c.kind = .xdot → ¬ (Γ.Unpinned c.x ∧ Γ.Unpinned c.y)) ↔
      ∀ c ∈ Γ.comps, (absG Γ c).1 = .xdot → (absG Γ c).2.1 = none ∨ (absG Γ c).2.2 = none := by
    simp only [absG, absT, strip, side_usG_none, not_and_or]
  have h0 := fun (ha : usG Γ 0) => And.intro (hasDiff_iff ha) (diffTo_iff ha)
  unfold Rep elemOK Graph.ExtClause AbsT
  constructor
  · rintro ⟨hC, ⟨hA, hX, hE0, hE2, hE1⟩, hG, hL⟩
    refine ⟨hA, fun c hc => ⟨(hcol.1 hC c hc).1, (hcol.1 hC c hc).2, hx.1 hX c hc⟩,
      ⟨fun ha => ?_, fun ha => ?_, fun ha => ?_⟩, hG, hL⟩
    · obtain ⟨h1, h2⟩ := hE0 ha
      exact ⟨(hasDiff_iff ha).1 h1, (diffTo_iff ha).1 h2⟩
    · obtain ⟨h1, h2⟩ := hE2 ha
      exact ⟨(e3_iff ha).1 h1, (degA_tL Γ 2 ha).symm ▸ h2⟩
    · obtain ⟨h1, h2, h3⟩ := hE1 ha
      refine ⟨?_, (diffTo_iff ha).1 h2, (degA_tL Γ 1 ha).symm ▸ h3⟩
      rcases h1 with h1 | h1
      · exact Or.inl ((gplus_iff ha).1 h1)
      · exact Or.inr ((hasDiff_iff ha).1 h1)
  · rintro ⟨hA, hE, ⟨hE0, hE2, hE1⟩, hG, hL⟩
    refine ⟨hcol.2 fun c hc => ⟨(hE c hc).1, (hE c hc).2.1⟩,
      ⟨hA, hx.2 fun c hc => (hE c hc).2.2, fun ha => ?_, fun ha => ?_, fun ha => ?_⟩, hG, hL⟩
    · obtain ⟨h1, h2⟩ := hE0 ha
      exact ⟨(hasDiff_iff ha).2 h1, (diffTo_iff ha).2 h2⟩
    · obtain ⟨h1, h2⟩ := hE2 ha
      exact ⟨(e3_iff ha).2 h1, (degA_tL Γ 2 ha) ▸ h2⟩
    · obtain ⟨h1, h2, h3⟩ := hE1 ha
      refine ⟨?_, (diffTo_iff ha).2 h2, (degA_tL Γ 1 ha) ▸ h3⟩
      rcases h1 with h1 | h1
      · exact Or.inl ((gplus_iff ha).2 h1)
      · exact Or.inr ((hasDiff_iff ha).2 h1)

end Abstract

/-! ## Transfer of the clauses -/

section Transfer

/-- A component with its ends moved along `f`. -/
private def mapT {n n' : ℕ} (f : Atom 3 n → Atom 3 n') (p : KT n) : KT n' := (p.1, f p.2.1, f p.2.2)

/-- The relation "joined by a dotted component" of a list of components. -/
private def dotR {n : ℕ} (L : List (KT n)) (u v : Atom 3 n) : Prop :=
  ∃ p ∈ L, p.1 = .dot ∧ p.2.1 = u ∧ p.2.2 = v

private theorem dotGraph_eq {n : ℕ} (Γ : Graph 3 n) :
    Γ.dotGraph = SimpleGraph.fromRel (dotR (Γ.comps.map strip)) := by
  ext u v
  simp only [Graph.dotGraph, SimpleGraph.fromRel_adj, dotR, List.mem_map, strip]
  constructor
  · rintro ⟨h, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact ⟨h, Or.inl ⟨_, ⟨c, hc, rfl⟩, hk, rfl, rfl⟩⟩
    · exact ⟨h, Or.inr ⟨_, ⟨c, hc, rfl⟩, hk, rfl, rfl⟩⟩
  · rintro ⟨h, ⟨_, ⟨c, hc, rfl⟩, hk, rfl, rfl⟩ | ⟨_, ⟨c, hc, rfl⟩, hk, rfl, rfl⟩⟩
    · exact ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact ⟨h, Or.inr ⟨c, hc, hk, rfl, rfl⟩⟩

private theorem sameBlock_iff_dotR {n : ℕ} (Γ : Graph 3 n) (u v : Atom 3 n) :
    Γ.SameBlock u v ↔ (SimpleGraph.fromRel (dotR (Γ.comps.map strip))).Reachable u v := by
  rw [Graph.SameBlock, dotGraph_eq]

/-- Reachability is carried along a map that carries adjacency to reachability. -/
private theorem reach_map {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} (f : α → β)
    (h : ∀ a b, G.Adj a b → H.Reachable (f a) (f b)) {u v : α} (huv : G.Reachable u v) :
    H.Reachable (f u) (f v) := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons ha _ ih => exact (h _ _ ha).trans ih

/-- Along an injective map whose image relation is `R'`, reachability comes from reachability. -/
private theorem reach_back {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (hf : Function.Injective f) (h : ∀ u' v', R' u' v' → ∃ u v, R u v ∧ f u = u' ∧ f v = v')
    {u' v' : β} (hr : (SimpleGraph.fromRel R').Reachable u' v') :
    u' = v' ∨ ∃ u v, f u = u' ∧ f v = v' ∧ (SimpleGraph.fromRel R).Reachable u v := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact Or.inl rfl
  | @cons a b c hadj _ ih =>
    right
    rw [SimpleGraph.fromRel_adj] at hadj
    obtain ⟨hne, hab⟩ := hadj
    obtain ⟨x, y, hxy, hx, hy⟩ : ∃ x y, (SimpleGraph.fromRel R).Adj x y ∧ f x = a ∧ f y = b := by
      rcases hab with hab | hab
      · obtain ⟨x, y, hr, rfl, rfl⟩ := h _ _ hab
        refine ⟨x, y, ?_, rfl, rfl⟩
        rw [SimpleGraph.fromRel_adj]
        exact ⟨fun he => hne (by rw [he]), Or.inl hr⟩
      · obtain ⟨y, x, hr, rfl, rfl⟩ := h _ _ hab
        refine ⟨x, y, ?_, rfl, rfl⟩
        rw [SimpleGraph.fromRel_adj]
        exact ⟨fun he => hne (by rw [he]), Or.inr hr⟩
    rcases ih with rfl | ⟨y', z, hy', hz, hr⟩
    · exact ⟨x, y, hx, hy, hxy.reachable⟩
    · have : y' = y := hf (hy'.trans hy.symm)
      subst this
      exact ⟨x, z, hx, hz, hxy.reachable.trans hr⟩

/-- An atom is identified when it is internal or its block contains an internal atom. -/
private theorem not_unpinned_iff {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    ¬ Γ.Unpinned u ↔ u.isRight = true ∨ ∃ b : Fin n, Γ.SameBlock u (.inr b) := by
  unfold Graph.Unpinned
  rcases u with a | b
  · simp
  · simp only [Sum.isLeft_inr, Bool.false_eq_true, false_and, not_false_eq_true, Sum.isRight_inr,
      true_or]

private theorem pinned_of_sameBlock {k n : ℕ} {Γ : Graph k n} {u v : Atom k n}
    (h : Γ.SameBlock u v) (hv : ¬ Γ.Unpinned v) : ¬ Γ.Unpinned u := by
  rw [not_unpinned_iff] at hv ⊢
  right
  rcases hv with hv | ⟨b, hb⟩
  · rcases v with a | b
    · simp at hv
    · exact ⟨b, h⟩
  · exact ⟨b, h.trans hb⟩

private theorem elemOK_none (κ : Kind) : elemOK (κ, none, none) := by
  refine ⟨fun _ => ⟨rfl, ?_, ?_, ?_⟩, fun _ => ⟨rfl, rfl⟩, fun _ => Or.inl rfl⟩ <;> simp

private theorem touch_false_none {p : AC} (h1 : p.1 ≠ .dot) (h2 : p.1 ≠ .xdot)
    (ht : touch p = false) : p.2.1 = none ∧ p.2.2 = none := by
  by_contra hc
  rw [not_and_or] at hc
  have : touch p = true := touch_of_some h1 h2 (by
    rcases hc with hc | hc
    · left; exact Option.isSome_iff_ne_none.2 hc
    · right; exact Option.isSome_iff_ne_none.2 hc)
  rw [this] at ht
  cases ht

/-- An injective atom map fixing the external atoms and keeping internal atoms internal. -/
private structure GoodMap {n n' : ℕ} (f : Atom 3 n → Atom 3 n') : Prop where
  inl : ∀ a, f (.inl a) = .inl a
  inr : ∀ b, (f (.inr b)).isRight = true
  inj : Function.Injective f

private theorem GoodMap.id {n : ℕ} : GoodMap (id : Atom 3 n → Atom 3 n) :=
  ⟨fun _ => rfl, fun _ => rfl, Function.injective_id⟩

private theorem GoodMap.lift {n : ℕ} (j : ℕ) : GoodMap (liftA j : Atom 3 n → Atom 3 (n + j)) :=
  ⟨fun _ => rfl, fun _ => rfl, Sum.map_injective.2 ⟨fun _ _ h => h, Fin.castAdd_injective _ _⟩⟩

private theorem side_map {n n' : ℕ} {f : Atom 3 n → Atom 3 n'} (hf : GoodMap f)
    (us : Fin 3 → Prop) (u : Atom 3 n) : side us (f u) = side us u := by
  rcases u with a | b
  · rw [hf.inl]; rfl
  · have := hf.inr b
    rcases h : f (.inr b) with a | b'
    · rw [h] at this; simp at this
    · rfl

private theorem absT_mapT {n n' : ℕ} {f : Atom 3 n → Atom 3 n'} (hf : GoodMap f)
    (us : Fin 3 → Prop) (p : KT n) : absT us (mapT f p) = absT us p := by
  simp [absT, mapT, side_map hf]

/-- The obligation of a step: the components of the input are `L₁ ++ R`, those of the output
`f(L₁) ++ N`, where `R` and `N` have no dotted edge, `N` no ghost edge, every `×`-dotted edge of
`N` is read as one of `R`, and the components of `N` and `R` with an end at an unidentified
external atom agree. -/
private def Obl {n n' : ℕ} (us : Fin 3 → Prop) (f : Atom 3 n → Atom 3 n') (L : List (KT n))
    (L' : List (KT n')) : Prop :=
  ∃ (L₁ R : List (KT n)) (N : List (KT n')), L.Perm (L₁ ++ R) ∧ L'.Perm (L₁.map (mapT f) ++ N) ∧
    (∀ p ∈ R, p.1 ≠ .dot) ∧
    (∀ p ∈ N, p.1 ≠ .dot ∧ p.1 ≠ .ghost ∧ (p.1 = .xdot → absT us p ∈ R.map (absT us))) ∧
    ((N.map (absT us)).filter touch).Perm ((R.map (absT us)).filter touch)

private theorem rep_of_obl {n n' : ℕ} {Γ : Graph 3 n} {Γ' : Graph 3 n'}
    {f : Atom 3 n → Atom 3 n'} (hf : GoodMap f) (h : Rep Γ)
    (ho : Obl (usG Γ) f (Γ.comps.map strip) (Γ'.comps.map strip)) (hl : Γ'.LabelsInt) :
    Rep Γ' := by
  obtain ⟨hA, hE, hT, hG, -⟩ := h
  obtain ⟨L₁, R, N, hp, hp', hR, hN, hNR⟩ := ho
  set us := usG Γ
  -- the dotted components of `Γ'` are the images of those of `Γ`
  have hdot : ∀ u' v', dotR (Γ'.comps.map strip) u' v' →
      ∃ u v, dotR (Γ.comps.map strip) u v ∧ f u = u' ∧ f v = v' := by
    rintro u' v' ⟨q, hq, hk, rfl, rfl⟩
    rcases List.mem_append.1 (hp'.mem_iff.1 hq) with hq | hq
    · obtain ⟨p, hpL, rfl⟩ := List.mem_map.1 hq
      exact ⟨p.2.1, p.2.2, ⟨p, hp.mem_iff.2 (List.mem_append_left _ hpL), hk, rfl, rfl⟩, rfl, rfl⟩
    · exact absurd hk (hN q hq).1
  have hdot' : ∀ u v, dotR (Γ.comps.map strip) u v → dotR (Γ'.comps.map strip) (f u) (f v) := by
    rintro u v ⟨p, hpm, hk, rfl, rfl⟩
    rcases List.mem_append.1 (hp.mem_iff.1 hpm) with hpm | hpm
    · exact ⟨mapT f p, hp'.mem_iff.2 (List.mem_append_left _ (List.mem_map_of_mem hpm)), hk, rfl,
        rfl⟩
    · exact absurd hk (hR p hpm)
  have hfwd : ∀ u v, Γ.SameBlock u v → Γ'.SameBlock (f u) (f v) := by
    intro u v huv
    rw [sameBlock_iff_dotR] at huv ⊢
    refine reach_map f (fun a b hab => ?_) huv
    rw [SimpleGraph.fromRel_adj] at hab
    obtain ⟨hne, hab | hab⟩ := hab
    · exact (SimpleGraph.fromRel_adj _ _ _).2
        ⟨fun he => hne (hf.inj he), Or.inl (hdot' _ _ hab)⟩ |>.reachable
    · exact (SimpleGraph.fromRel_adj _ _ _).2
        ⟨fun he => hne (hf.inj he), Or.inr (hdot' _ _ hab)⟩ |>.reachable
  have hback : ∀ u' v', Γ'.SameBlock u' v' →
      u' = v' ∨ ∃ u v, f u = u' ∧ f v = v' ∧ Γ.SameBlock u v := by
    intro u' v' h'
    rw [sameBlock_iff_dotR] at h'
    rcases reach_back f hf.inj hdot h' with h | ⟨u, v, hu, hv, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, v, hu, hv, (sameBlock_iff_dotR _ _ _).2 hr⟩
  -- the unidentified external atoms do not change
  have hus : usG Γ' = us := by
    funext a
    apply propext
    simp only [usG, us, Graph.Unpinned, Sum.isLeft_inl, true_and]
    constructor
    · intro h' b hb
      have := hfwd _ _ hb
      rw [hf.inl] at this
      have hr := hf.inr b
      rcases hfb : f (.inr b) with a' | b'
      · rw [hfb] at hr; simp at hr
      · rw [hfb] at this; exact h' b' this
    · intro h' b' hb'
      rcases hback _ _ hb' with he | ⟨u, v, hu, hv, hr⟩
      · cases he
      · have hu' : u = .inl a := by
          rcases u with a'' | b''
          · rw [hf.inl] at hu; cases hu; rfl
          · have := hf.inr b''; rw [hu] at this; simp at this
        rcases v with a'' | b''
        · rw [hf.inl] at hv; cases hv
        · rw [hu'] at hr; exact h' b'' hr
  have habs : ∀ c' ∈ Γ'.comps, absG Γ' c' = absT us (strip c') := fun c' _ => by
    rw [absG, hus]
  -- a component of the output with an end at an unidentified external atom
  have hmem : ∀ c' ∈ Γ'.comps, strip c' ∈ L₁.map (mapT f) ∨ strip c' ∈ N := fun c' hc' =>
    List.mem_append.1 (hp'.mem_iff.1 (List.mem_map_of_mem hc'))
  have hL₁ : ∀ p ∈ L₁, ∃ c ∈ Γ.comps, strip c = p := fun p hpL =>
    List.mem_map.1 (hp.mem_iff.2 (List.mem_append_left _ hpL))
  have hRm : ∀ p ∈ R, ∃ c ∈ Γ.comps, strip c = p := fun p hpL =>
    List.mem_map.1 (hp.mem_iff.2 (List.mem_append_right _ hpL))
  refine ⟨?_, ?_, ?_, ?_, hl⟩
  · intro u' v' hne h'
    rcases hback _ _ h' with he | ⟨u, v, rfl, rfl, hr⟩
    · exact absurd he hne
    · obtain ⟨b, hb⟩ := hA u v (fun he => hne (by rw [he])) hr
      have := hfwd _ _ hb
      have hr' := hf.inr b
      rcases hfb : f (.inr b) with a' | b'
      · rw [hfb] at hr'; simp at hr'
      · rw [hfb] at this; exact ⟨b', this⟩
  · intro c' hc'
    rw [habs c' hc']
    rcases hmem c' hc' with hq | hq
    · obtain ⟨p, hpL, hpe⟩ := List.mem_map.1 hq
      obtain ⟨c, hc, rfl⟩ := hL₁ p hpL
      rw [← hpe, absT_mapT hf]
      exact hE c hc
    · by_cases ht : touch (absT us (strip c')) = true
      · have hin : absT us (strip c') ∈ (R.map (absT us)).filter touch :=
          hNR.mem_iff.1 (List.mem_filter.2 ⟨List.mem_map_of_mem hq, ht⟩)
        obtain ⟨p, hpR, hpe⟩ := List.mem_map.1 (List.mem_filter.1 hin).1
        obtain ⟨c, hc, rfl⟩ := hRm p hpR
        rw [← hpe]
        exact hE c hc
      · obtain ⟨h1, -, hx⟩ := hN _ hq
        by_cases h2 : (strip c').1 = .xdot
        · obtain ⟨p, hpR, hpe⟩ := List.mem_map.1 (hx h2)
          obtain ⟨c, hc, rfl⟩ := hRm p hpR
          rw [← hpe]
          exact hE c hc
        obtain ⟨e1, e2⟩ := touch_false_none h1 h2 (by simpa using ht)
        have : absT us (strip c') = ((strip c').1, none, none) := by
          rw [Prod.ext_iff, Prod.ext_iff]
          exact ⟨rfl, e1, e2⟩
        rw [this]
        exact elemOK_none _
  · rw [hus]
    refine AbsT_perm ?_ hT
    unfold tL
    rw [hus]
    refine List.Perm.symm ?_
    refine ((hp'.map _).filter _).trans ?_
    refine List.Perm.trans ?_ ((hp.map _).filter _).symm
    simp only [List.map_append, List.filter_append, List.map_map]
    have e2 : L₁.map (absT us ∘ mapT f) = L₁.map (absT us) :=
      List.map_congr_left fun p _ => absT_mapT hf us p
    rw [e2]
    exact hNR.append_left _
  · intro c' hc' hk
    rcases hmem c' hc' with hq | hq
    · obtain ⟨p, hpL, hpe⟩ := List.mem_map.1 hq
      obtain ⟨c, hc, rfl⟩ := hL₁ p hpL
      apply hG c hc
      have := congrArg Prod.fst hpe
      simp only [mapT, strip] at this
      rw [this]; exact hk
    · exact (hN _ hq).2.1 hk

private theorem side_mono {n : ℕ} {us us' : Fin 3 → Prop} (h : ∀ a, us' a → us a)
    {u : Atom 3 n} {a : Fin 3} (hs : side us' u = some a) : side us u = some a := by
  rw [side_eq_some] at hs ⊢
  exact ⟨hs.1, h a hs.2⟩

private theorem side_mono_iff {n : ℕ} {us us' : Fin 3 → Prop} (h : ∀ a, us' a → us a)
    {u : Atom 3 n} {a : Fin 3} (ha : us' a) : side us' u = some a ↔ side us u = some a := by
  rw [side_eq_some, side_eq_some]
  exact ⟨fun h' => ⟨h'.1, h a h'.2⟩, fun h' => ⟨h'.1, ha⟩⟩

private theorem side_mono_none {n : ℕ} {us us' : Fin 3 → Prop} (h : ∀ a, us' a → us a)
    {u : Atom 3 n} (hs : side us u = none) : side us' u = none := by
  rcases h' : side us' u with _ | a
  · rfl
  · rw [side_mono h h'] at hs; cases hs

private theorem mem_ftouch {n : ℕ} {us : Fin 3 → Prop} {L : List (KT n)} {p : AC} :
    p ∈ (L.map (absT us)).filter touch ↔ ∃ q ∈ L, absT us q = p ∧ touch p = true := by
  simp only [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, ht⟩; exact ⟨q, hq, rfl, ht⟩
  · rintro ⟨q, hq, rfl, ht⟩; exact ⟨⟨q, hq, rfl⟩, ht⟩

private theorem touch_mono {n : ℕ} {us us' : Fin 3 → Prop} (h : ∀ a, us' a → us a) (q : KT n)
    (ht : touch (absT us' q) = true) : touch (absT us q) = true := by
  simp only [touch, absT, Bool.and_eq_true, Bool.or_eq_true] at ht ⊢
  refine ⟨ht.1, ?_⟩
  rcases ht.2 with h1 | h1
  · left
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h1
    rw [side_mono h ha]; rfl
  · right
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h1
    rw [side_mono h ha]; rfl

private theorem degA_ftouch {n : ℕ} (us : Fin 3 → Prop) (L : List (KT n)) (a : Fin 3) :
    degA a ((L.map (absT us)).filter touch) =
      (L.filter fun q => decide (atA a (absT us q)) && touch (absT us q)).length := by
  unfold degA
  rw [List.filter_filter, List.filter_map, List.length_map]
  rfl

/-- The counting clauses survive when fewer external atoms are unidentified. -/
private theorem AbsT_demote {n : ℕ} {us us' : Fin 3 → Prop} (h : ∀ a, us' a → us a)
    (L : List (KT n)) (hT : AbsT us ((L.map (absT us)).filter touch)) :
    AbsT us' ((L.map (absT us')).filter touch) := by
  obtain ⟨h0, h2, h1⟩ := hT
  -- the clauses at one unidentified atom `a`
  have hHas : ∀ a, us' a → HasDiffP a ((L.map (absT us)).filter touch) →
      HasDiffP a ((L.map (absT us')).filter touch) := by
    rintro a ha ⟨p, hp, hd, hx⟩
    obtain ⟨q, hq, rfl, -⟩ := mem_ftouch.1 hp
    have hd' : (absT us' q).1.isDiffusive = true := hd
    obtain ⟨n1, n2⟩ := diff_ne_dot hd
    refine ⟨absT us' q, mem_ftouch.2 ⟨q, hq, rfl, ?_⟩, hd', ?_⟩
    · refine touch_of_some n1 n2 ?_
      rcases hx with ⟨hx, -⟩ | ⟨hx, -⟩
      · left; show (side us' q.2.1).isSome = true
        rw [side_mono_iff h ha |>.2 hx]; rfl
      · right; show (side us' q.2.2).isSome = true
        rw [side_mono_iff h ha |>.2 hx]; rfl
    · simp only [absT] at hx ⊢
      rcases hx with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inl ⟨(side_mono_iff h ha).2 hx, side_mono_none h hy⟩
      · exact Or.inr ⟨(side_mono_iff h ha).2 hx, side_mono_none h hy⟩
  have hDiff : ∀ a, us' a → DiffP a ((L.map (absT us)).filter touch) →
      DiffP a ((L.map (absT us')).filter touch) := by
    intro a ha hD p hp hd
    obtain ⟨q, hq, rfl, ht⟩ := mem_ftouch.1 hp
    have hin : absT us q ∈ (L.map (absT us)).filter touch :=
      mem_ftouch.2 ⟨q, hq, rfl, touch_mono h q ht⟩
    have := hD _ hin hd
    simp only [absT] at this ⊢
    refine ⟨fun hx => side_mono_none h (this.1 ((side_mono_iff h ha).1 hx)),
      fun hy => side_mono_none h (this.2 ((side_mono_iff h ha).1 hy))⟩
  have hDeg : ∀ a, us' a → degA a ((L.map (absT us')).filter touch) ≤
      degA a ((L.map (absT us)).filter touch) := by
    intro a ha
    rw [degA_ftouch, degA_ftouch]
    refine (List.monotone_filter_right L fun q hq => ?_).length_le
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq ⊢
    refine ⟨?_, touch_mono h q hq.2⟩
    simp only [atA, absT] at hq ⊢
    rcases hq.1 with hx | hx
    · exact Or.inl ((side_mono_iff h ha).1 hx)
    · exact Or.inr ((side_mono_iff h ha).1 hx)
  refine ⟨fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨hh, hd⟩ := h0 (h 0 ha)
    exact ⟨hHas 0 ha hh, hDiff 0 ha hd⟩
  · obtain ⟨hn, hc⟩ := h2 (h 2 ha)
    refine ⟨fun p hp hd hat => ?_, (hDeg 2 ha).trans hc⟩
    obtain ⟨q, hq, rfl, ht⟩ := mem_ftouch.1 hp
    refine hn (absT us q) (mem_ftouch.2 ⟨q, hq, rfl, touch_mono h q ht⟩) hd ?_
    simp only [atA, absT] at hat ⊢
    rcases hat with hx | hx
    · exact Or.inl ((side_mono_iff h ha).1 hx)
    · exact Or.inr ((side_mono_iff h ha).1 hx)
  · obtain ⟨he, hd, hc⟩ := h1 (h 1 ha)
    refine ⟨?_, hDiff 1 ha hd, (hDeg 1 ha).trans hc⟩
    rcases he with ⟨p, hp, hk, hat⟩ | hh
    · obtain ⟨q, hq, rfl, -⟩ := mem_ftouch.1 hp
      have hat' : atA 1 (absT us' q) := by
        simp only [atA, absT] at hat ⊢
        rcases hat with hx | hx
        · exact Or.inl ((side_mono_iff h ha).2 hx)
        · exact Or.inr ((side_mono_iff h ha).2 hx)
      refine Or.inl ⟨absT us' q, mem_ftouch.2 ⟨q, hq, rfl, ?_⟩, hk, hat'⟩
      refine touch_of_some (by rw [show (absT us' q).1 = _ from hk]; simp)
        (by rw [show (absT us' q).1 = _ from hk]; simp) ?_
      rcases hat' with hx | hx
      · left; rw [hx]; rfl
      · right; rw [hx]; rfl
    · exact Or.inr (hHas 1 ha hh)

private theorem elemOK_demote {κ : Kind} {x y x' y' : Option (Fin 3)}
    (hx : ∀ a, x' = some a → x = some a) (hy : ∀ a, y' = some a → y = some a)
    (h : elemOK (κ, x, y)) : elemOK (κ, x', y') := by
  obtain ⟨h1, h2, h3⟩ := h
  have nx : x = none → x' = none := fun e => by
    rcases h' : x' with _ | a
    · rfl
    · rw [hx a h'] at e; cases e
  have ny : y = none → y' = none := fun e => by
    rcases h' : y' with _ | a
    · rfl
    · rw [hy a h'] at e; cases e
  refine ⟨fun hr => ?_, fun hw => ?_, fun hd => ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := h1 hr
    exact ⟨nx e1, fun e => e2 (hy 0 e), fun e => e3 (hy 1 e), fun e => e4 (hy 2 e)⟩
  · obtain ⟨e1, e2⟩ := h2 hw
    exact ⟨nx e1, ny e2⟩
  · rcases h3 hd with e | e
    · exact Or.inl (nx e)
    · exact Or.inr (ny e)

private theorem exists_int_of_pinned {k n : ℕ} {Γ : Graph k n} {u : Atom k n}
    (h : ¬ Γ.Unpinned u) : ∃ b : Fin n, Γ.SameBlock u (.inr b) := by
  rcases (not_unpinned_iff Γ u).1 h with h | h
  · rcases u with a | b
    · simp at h
    · exact ⟨b, SimpleGraph.Reachable.refl _⟩
  · exact h

/-- Dotted and `×`-dotted edges added, each with an end identified with an internal atom, and
`×`-dotted edges removed. -/
private def ObM {n : ℕ} (us : Fin 3 → Prop) (L L' : List (KT n)) : Prop :=
  ∃ (L₁ R N : List (KT n)), L.Perm (L₁ ++ R) ∧ L'.Perm (L₁ ++ N) ∧ (∀ p ∈ R, p.1 = .xdot) ∧
    ∀ p ∈ N, (p.1 = .dot ∨ p.1 = .xdot) ∧ (side us p.2.1 = none ∨ side us p.2.2 = none)

private theorem rep_of_mono {n : ℕ} {Γ Γ' : Graph 3 n} (h : Rep Γ)
    (ho : ObM (usG Γ) (Γ.comps.map strip) (Γ'.comps.map strip)) (hl : Γ'.LabelsInt) :
    Rep Γ' := by
  obtain ⟨hA, hE, hT, hG, -⟩ := h
  obtain ⟨L₁, R, N, hp, hp', hR, hN⟩ := ho
  have hsub : ∀ u v, dotR (Γ.comps.map strip) u v → dotR (Γ'.comps.map strip) u v := by
    rintro u v ⟨p, hpm, hk, rfl, rfl⟩
    rcases List.mem_append.1 (hp.mem_iff.1 hpm) with hpm | hpm
    · exact ⟨p, hp'.mem_iff.2 (List.mem_append_left _ hpm), hk, rfl, rfl⟩
    · rw [hR p hpm] at hk; cases hk
  have hfwd : ∀ u v, Γ.SameBlock u v → Γ'.SameBlock u v := by
    intro u v huv
    rw [sameBlock_iff_dotR] at huv ⊢
    refine reach_map id (fun a b hab => ?_) huv
    rw [SimpleGraph.fromRel_adj] at hab
    obtain ⟨hne, hab | hab⟩ := hab
    · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl (hsub _ _ hab)⟩).reachable
    · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inr (hsub _ _ hab)⟩).reachable
  have hpin : ∀ u, ¬ Γ.Unpinned u → ¬ Γ'.Unpinned u := by
    intro u hu
    rw [not_unpinned_iff] at hu ⊢
    rcases hu with hu | ⟨b, hb⟩
    · exact Or.inl hu
    · exact Or.inr ⟨b, hfwd _ _ hb⟩
  have hus : ∀ a, usG Γ' a → usG Γ a := fun a ha => by
    by_contra hc; exact hpin _ hc ha
  have hsd : ∀ (u : Atom 3 n) a, side (usG Γ') u = some a → side (usG Γ) u = some a :=
    fun u a hs => side_mono hus hs
  have hL₁ : ∀ p ∈ L₁, ∃ c ∈ Γ.comps, strip c = p := fun p hpL =>
    List.mem_map.1 (hp.mem_iff.2 (List.mem_append_left _ hpL))
  refine ⟨?_, ?_, ?_, ?_, hl⟩
  · intro u v hne huv
    rw [sameBlock_iff_dotR] at huv
    obtain ⟨w⟩ := huv
    cases w with
    | nil => exact absurd rfl hne
    | @cons _ w' _ hadj _ =>
      rw [SimpleGraph.fromRel_adj] at hadj
      obtain ⟨hne', hd⟩ := hadj
      have key : ∀ x y, dotR (Γ'.comps.map strip) x y → (x = u ∧ y = w' ∨ x = w' ∧ y = u) →
          ∃ b : Fin n, Γ'.SameBlock u (.inr b) := by
        rintro x y ⟨p, hpm, hk, rfl, rfl⟩ hxy
        have huw : Γ'.SameBlock u w' := by
          rw [sameBlock_iff_dotR]
          exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne', hd⟩).reachable
        rcases List.mem_append.1 (hp'.mem_iff.1 hpm) with hpm | hpm
        · obtain ⟨c, hc, hce⟩ := hL₁ p hpm
          have hdot : Γ.SameBlock p.2.1 p.2.2 := by
            rw [sameBlock_iff_dotR]
            by_cases he : p.2.1 = p.2.2
            · rw [he]
            · exact ((SimpleGraph.fromRel_adj _ _ _).2
                ⟨he, Or.inl ⟨p, hp.mem_iff.2 (List.mem_append_left _ hpm), hk, rfl, rfl⟩⟩).reachable
          have huw0 : Γ.SameBlock u w' := by
            rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [← h1, ← h2]; exact hdot
            · rw [← h1, ← h2]; exact hdot.symm
          obtain ⟨b, hb⟩ := hA u w' hne' huw0
          exact ⟨b, hfwd _ _ hb⟩
        · have hpu : ¬ Γ.Unpinned p.2.1 ∨ ¬ Γ.Unpinned p.2.2 := by
            rcases (hN p hpm).2 with h' | h'
            · exact Or.inl ((side_usG_none Γ _).1 h')
            · exact Or.inr ((side_usG_none Γ _).1 h')
          have hu' : ¬ Γ'.Unpinned u := by
            rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rcases hpu with h' | h'
              · rw [h1] at h'; exact hpin _ h'
              · rw [h2] at h'; exact pinned_of_sameBlock huw (hpin _ h')
            · rcases hpu with h' | h'
              · rw [h1] at h'; exact pinned_of_sameBlock huw (hpin _ h')
              · rw [h2] at h'; exact hpin _ h'
          exact exists_int_of_pinned hu'
      rcases hd with hd | hd
      · exact key _ _ hd (Or.inl ⟨rfl, rfl⟩)
      · exact key _ _ hd (Or.inr ⟨rfl, rfl⟩)
  · intro c' hc'
    rcases List.mem_append.1 (hp'.mem_iff.1 (List.mem_map_of_mem hc')) with hq | hq
    · obtain ⟨c, hc, hce⟩ := hL₁ _ hq
      have := hE c hc
      simp only [absG, absT] at this ⊢
      rw [hce] at this
      exact elemOK_demote (fun a => hsd _ a) (fun a => hsd _ a) this
    · obtain ⟨hk, hs⟩ := hN _ hq
      simp only [absG, absT]
      rcases hk with hk | hk
      · refine ⟨fun hr => ?_, fun hw => ?_, fun hx => ?_⟩
        · rw [hk] at hr; cases hr
        · rw [hk] at hw; cases hw
        · rw [hk] at hx; cases hx
      · refine ⟨fun hr => ?_, fun hw => ?_, fun _ => ?_⟩
        · rw [hk] at hr; cases hr
        · rw [hk] at hw; cases hw
        · rcases hs with hs | hs
          · exact Or.inl (side_mono_none hus hs)
          · exact Or.inr (side_mono_none hus hs)
  · have hNt : ∀ us' : Fin 3 → Prop, (N.map (absT us')).filter touch = [] := by
      intro us'
      rw [List.filter_eq_nil_iff]
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      rcases (hN q hq).1 with hk | hk <;> simp [touch, absT, hk]
    have hRt : (R.map (absT (usG Γ))).filter touch = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      simp [touch, absT, hR q hq]
    have e' : (tL Γ').Perm ((L₁.map (absT (usG Γ'))).filter touch) := by
      unfold tL
      refine ((hp'.map _).filter _).trans ?_
      rw [List.map_append, List.filter_append, hNt, List.append_nil]
    have e : (tL Γ).Perm ((L₁.map (absT (usG Γ))).filter touch) := by
      unfold tL
      refine ((hp.map _).filter _).trans ?_
      rw [List.map_append, List.filter_append, hRt, List.append_nil]
    exact AbsT_perm e'.symm (AbsT_demote hus L₁ (AbsT_perm e hT))
  · intro c' hc' hk
    rcases List.mem_append.1 (hp'.mem_iff.1 (List.mem_map_of_mem hc')) with hq | hq
    · obtain ⟨c, hc, hce⟩ := hL₁ _ hq
      apply hG c hc
      have := congrArg Prod.fst hce
      simp only [strip] at this
      rw [this]; exact hk
    · rcases (hN _ hq).1 with h' | h'
      · simp only [strip] at h'; rw [hk] at h'; cases h'
      · simp only [strip] at h'; rw [hk] at h'; cases h'

end Transfer

/-! ## The obligation of a step -/

section Obligation

variable {n n' : ℕ} {us : Fin 3 → Prop} {f : Atom 3 n → Atom 3 n'}

private theorem Obl_refl (us : Fin 3 → Prop) (f : Atom 3 n → Atom 3 n') (L : List (KT n)) :
    Obl us f L (L.map (mapT f)) :=
  ⟨L, [], [], by simp, by simp, by simp, by simp, by simp⟩

private theorem Obl_perm {L M : List (KT n)} {L' M' : List (KT n')} (h1 : L.Perm M)
    (h2 : L'.Perm M') (h : Obl us f M M') : Obl us f L L' := by
  obtain ⟨L₁, R, N, hp, hp', hR, hN, ht⟩ := h
  exact ⟨L₁, R, N, h1.trans hp, h2.trans hp', hR, hN, ht⟩

private theorem Obl_cons (q : KT n) {L : List (KT n)} {L' : List (KT n')} (h : Obl us f L L') :
    Obl us f (q :: L) (mapT f q :: L') := by
  obtain ⟨L₁, R, N, hp, hp', hR, hN, ht⟩ := h
  exact ⟨q :: L₁, R, N, hp.cons q, by simpa using hp'.cons (mapT f q), hR, hN, ht⟩

private theorem Obl_append {L : List (KT n)} {L' : List (KT n')} (h : Obl us f L L')
    (E : List (KT n)) : Obl us f (L ++ E) (L' ++ E.map (mapT f)) := by
  obtain ⟨L₁, R, N, hp, hp', hR, hN, ht⟩ := h
  refine ⟨L₁ ++ E, R, N, ?_, ?_, hR, hN, ht⟩
  · refine (hp.append_right E).trans ?_
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  · refine (hp'.append_right _).trans ?_
    rw [List.map_append, List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm

private theorem Obl_repl (R₀ : List (KT n)) (N₀ : List (KT n')) (hR : ∀ p ∈ R₀, p.1 ≠ .dot)
    (hN : ∀ p ∈ N₀, p.1 ≠ .dot ∧ p.1 ≠ .ghost ∧ (p.1 = .xdot → absT us p ∈ R₀.map (absT us)))
    (ht : ((N₀.map (absT us)).filter touch).Perm ((R₀.map (absT us)).filter touch))
    {L : List (KT n)} {L' : List (KT n')} (h : Obl us f L L') :
    Obl us f (R₀ ++ L) (N₀ ++ L') := by
  obtain ⟨L₁, R, N, hp, hp', hR', hN', ht'⟩ := h
  refine ⟨L₁, R₀ ++ R, N₀ ++ N, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hp.append_left R₀).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  · refine (hp'.append_left N₀).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hR p hp
    · exact hR' p hp
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨h1, h2, h3⟩ := hN p hp
      exact ⟨h1, h2, fun hx => by
        rw [List.map_append]; exact List.mem_append_left _ (h3 hx)⟩
    · obtain ⟨h1, h2, h3⟩ := hN' p hp
      exact ⟨h1, h2, fun hx => by
        rw [List.map_append]; exact List.mem_append_right _ (h3 hx)⟩
  · simp only [List.map_append, List.filter_append]
    exact ht.append ht'

/-- The complex conjugate kind on a component. -/
private def conjT {n : ℕ} (p : KT n) : KT n := (p.1.conj, p.2.1, p.2.2)

private theorem Kind.conj_conj' (κ : Kind) : κ.conj.conj = κ := by
  cases κ with
  | G c => cases c <;> rfl
  | weight c => cases c <;> rfl
  | light c => cases c <;> rfl
  | inv c => cases c <;> rfl
  | wD c d => cases c <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem Kind.conj_eq_iff {κ κ' : Kind} : κ.conj = κ' ↔ κ = κ'.conj := by
  constructor
  · rintro rfl; rw [Kind.conj_conj']
  · rintro rfl; rw [Kind.conj_conj']

private theorem Kind.isRandom_conj (κ : Kind) : κ.conj.isRandom = κ.isRandom := by
  cases κ with
  | G c => cases c <;> rfl
  | weight c => cases c <;> rfl
  | light c => cases c <;> rfl
  | inv c => cases c <;> rfl
  | wD c d => cases c <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem conjT_conjT (p : KT n) : conjT (conjT p) = p := by
  simp [conjT, Kind.conj_conj']

private theorem strip_conj (H : Graph 3 n) :
    H.conj.comps.map strip = (H.comps.map strip).map conjT := by
  simp [Graph.conj, strip, conjT, Function.comp_def]

/-- The complex conjugate kind, read through the unidentified external atoms. -/
private def conjA (p : AC) : AC := (p.1.conj, p.2.1, p.2.2)

private theorem absT_conjT {n : ℕ} (us : Fin 3 → Prop) (p : KT n) :
    absT us (conjT p) = conjA (absT us p) := rfl

private theorem touch_conjA (p : AC) : touch (conjA p) = touch p := by
  rcases p with ⟨κ, a, b⟩
  cases κ with
  | G c => cases c <;> rfl
  | weight c => cases c <;> rfl
  | light c => cases c <;> rfl
  | inv c => cases c <;> rfl
  | wD c d => cases c <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem ftouch_conj {n : ℕ} (us : Fin 3 → Prop) (L : List (KT n)) :
    ((L.map conjT).map (absT us)).filter touch = ((L.map (absT us)).filter touch).map conjA := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.filter_cons, absT_conjT, touch_conjA]
    split_ifs <;> simp only [List.map_cons, ih]

private theorem Obl_conj {L : List (KT n)} {L' : List (KT n')} (h : Obl us f L L') :
    Obl us f (L.map conjT) (L'.map conjT) := by
  obtain ⟨L₁, R, N, hp, hp', hR, hN, ht⟩ := h
  refine ⟨L₁.map conjT, R.map conjT, N.map conjT, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hp.map conjT
  · have := hp'.map conjT
    simp only [List.map_append, List.map_map] at this ⊢
    exact this
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    intro h'
    exact hR q hq (Kind.conj_eq_iff.1 h')
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2, h3⟩ := hN q hq
    refine ⟨fun h' => h1 (Kind.conj_eq_iff.1 h'), fun h' => h2 (Kind.conj_eq_iff.1 h'),
      fun h' => ?_⟩
    obtain ⟨r, hr, hre⟩ := List.mem_map.1 (h3 (Kind.conj_eq_iff.1 h'))
    refine List.mem_map.2 ⟨conjT r, List.mem_map_of_mem hr, ?_⟩
    rw [absT_conjT, absT_conjT, hre]
  · rw [ftouch_conj, ftouch_conj]
    exact ht.map conjA

/-- Random components have an identified first atom, and an identified second atom unless they
are solid edges. -/
private def Nice {n : ℕ} (us : Fin 3 → Prop) (L : List (KT n)) : Prop :=
  ∀ p ∈ L, p.1.isRandom = true → side us p.2.1 = none ∧ ((∀ ch, p.1 ≠ .G ch) → side us p.2.2 = none)

private theorem Nice_conj {L : List (KT n)} (h : Nice us L) : Nice us (L.map conjT) := by
  intro p hp hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  simp only [conjT, Kind.isRandom_conj] at hr ⊢
  obtain ⟨h1, h2⟩ := h q hq hr
  refine ⟨h1, fun hG => h2 fun ch hc => hG ch.flip ?_⟩
  rw [hc]; cases ch <;> rfl

private theorem Nice_sub {L M : List (KT n)} (h : Nice us M) (hs : ∀ p ∈ L, p ∈ M) : Nice us L :=
  fun p hp => h p (hs p hp)

private theorem rep_elem {Γ : Graph 3 n} (h : Rep Γ) {c : Comp (Atom 3 n)} (hc : c ∈ Γ.comps) :
    elemOK (absG Γ c) := h.2.1 c hc

private theorem nice_of_rep {Γ : Graph 3 n} (h : Rep Γ) : Nice (usG Γ) (Γ.comps.map strip) := by
  intro p hp hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
  obtain ⟨e1, e2, e3, e4⟩ := (rep_elem h hc).1 hr
  refine ⟨e1, fun hG => ?_⟩
  rcases hy : side (usG Γ) (strip c).2.2 with _ | a
  · rfl
  · exfalso
    have hy' : (absG Γ c).2.2 = some a := hy
    fin_cases a
    · exact e2 hy'
    · exact hG _ (e3 hy')
    · exact hG _ (e4 hy')

private theorem ftouch_nil {N : List (KT n)}
    (h : ∀ p ∈ N, side us p.2.1 = none ∧ side us p.2.2 = none) :
    (N.map (absT us)).filter touch = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨h1, h2⟩ := h q hq
  simp [touch, absT, h1, h2]

end Obligation

/-! ## Steps that replace components -/

section Replace

variable {n : ℕ}

private theorem map_mapT_id (L : List (KT n)) : L.map (mapT id) = L := by
  have : (mapT id : KT n → KT n) = id := funext fun _ => rfl
  rw [this, List.map_id]

private theorem perm_eraseIdx {α : Type*} {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c) :
    L.Perm (c :: L.eraseIdx i) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  exact (List.getElem_cons_eraseIdx_perm hi).symm

/-- A component of `Γ` replaced by the components `new`. -/
private theorem rep_replace {Γ : Graph 3 n} {i : ℕ} {c : Comp (Atom 3 n)}
    (hc : Γ.comps[i]? = some c)
    (new : List (Comp (Atom 3 n))) (co : Coeff) (h : Rep Γ) (hc0 : c.kind ≠ .dot)
    (hN : ∀ p ∈ new.map strip, p.1 ≠ .dot ∧ p.1 ≠ .ghost ∧
      (p.1 = .xdot → absT (usG Γ) p = absT (usG Γ) (strip c)))
    (ht : (((new.map strip).map (absT (usG Γ))).filter touch).Perm
      (([strip c].map (absT (usG Γ))).filter touch))
    (hl : ∀ d ∈ new, d.label.all (fun ℓ => ℓ.2.isRight) = true) :
    Rep ⟨Γ.comps.eraseIdx i ++ new, co⟩ := by
  refine rep_of_obl GoodMap.id h ?_ ?_
  · have hp : (Γ.comps.map strip).Perm ([strip c] ++ (Γ.comps.eraseIdx i).map strip) := by
      have := (perm_eraseIdx hc).map strip
      simpa using this
    refine Obl_perm (M' := new.map strip ++ (Γ.comps.eraseIdx i).map strip) hp
      (by rw [List.map_append]; exact List.perm_append_comm) ?_
    refine Obl_repl [strip c] (new.map strip) (fun p hp => ?_) (fun p hp => ?_) ht ?_
    · rw [List.mem_singleton] at hp; subst hp; exact hc0
    · obtain ⟨h1, h2, h3⟩ := hN p hp
      exact ⟨h1, h2, fun hx => by simp [h3 hx]⟩
    · have := Obl_refl (usG Γ) id ((Γ.comps.eraseIdx i).map strip)
      rwa [map_mapT_id] at this
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.2.2.2.2 d (List.mem_of_mem_eraseIdx hd)
    · exact hl d hd

private theorem side_right {n : ℕ} {us : Fin 3 → Prop} {x : Atom 3 n} (hx : x.isRight = true) :
    side us x = none := by
  rcases x with a | b
  · simp at hx
  · rfl

private theorem strip_mkC {n : ℕ} (κ : Kind) (u v : Atom 3 n) : strip (mkC κ u v) = (κ, u, v) :=
  rfl

private theorem strip_solidC {n : ℕ} (ch : Charge) (u v : Atom 3 n) :
    strip (solidC ch u v) = (if u = v then .weight ch else .G ch, u, v) := by
  unfold solidC
  split_ifs with h
  · subst h; rfl
  · rfl

@[simp] private theorem solidC_x {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    (solidC ch u v).x = u := by
  unfold solidC; split_ifs <;> rfl

@[simp] private theorem solidC_y {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    (solidC ch u v).y = v := by
  unfold solidC; split_ifs with h
  · exact h
  · rfl

@[simp] private theorem solidC_kind {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    (solidC ch u v).kind = if u = v then .weight ch else .G ch := by
  unfold solidC; split_ifs <;> rfl

private theorem labelsInt_of_mem {n : ℕ} {Γ : Graph 3 n} (h : Rep Γ) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) : c.label.all (fun ℓ => ℓ.2.isRight) = true := h.2.2.2.2 c hc

private theorem nice_mem {n : ℕ} {Γ : Graph 3 n} (h : Rep Γ) {i : ℕ} {c : Comp (Atom 3 n)}
    (hc : Γ.comps[i]? = some c) (hr : c.kind.isRandom = true) :
    side (usG Γ) c.x = none ∧ ((∀ ch, c.kind ≠ .G ch) → side (usG Γ) c.y = none) :=
  nice_of_rep h (strip c) (List.mem_map_of_mem (List.mem_of_getElem? hc)) hr

/-- [II, (4.17), (4.20)] at a solid edge: the two terms. -/
private theorem rep_schur_terms {Γ : Graph 3 n} {x : Atom 3 n} {i : ℕ} {c : Comp (Atom 3 n)}
    {ch : Charge} (hx : x.isRight = true) (h : Rep Γ) (hc : Γ.comps[i]? = some c)
    (hk : c.kind = .G ch) (mi : List (Atom 3 n)) (co : Coeff) :
    Rep ⟨Γ.comps.eraseIdx i ++ [{ c with minor := mi }], co⟩ ∧
    Rep ⟨Γ.comps.eraseIdx i ++ [{ solidC ch c.x x with label := c.label },
      { solidC ch x c.y with label := c.label },
      { mkC (.inv ch) x x with label := c.label }], co⟩ := by
  have hlc := labelsInt_of_mem h (List.mem_of_getElem? hc)
  obtain ⟨hcx, -⟩ := nice_mem h hc (by rw [hk]; rfl)
  have hsx : side (usG Γ) x = none := side_right hx
  constructor
  · refine rep_replace hc _ co h (by rw [hk]; simp) ?_ ?_ ?_
    · intro p hp
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hp
      subst hp
      simp [strip, hk]
    · simp [strip]
    · intro d hd
      rw [List.mem_singleton] at hd; subst hd; exact hlc
  · refine rep_replace hc _ co h (by rw [hk]; simp) ?_ ?_ ?_
    · intro p hp
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      have e : ∀ u v : Atom 3 n, strip { solidC ch u v with label := c.label } =
          strip (solidC ch u v) := fun _ _ => rfl
      rcases hp with rfl | rfl | rfl
      · rw [e, strip_solidC]; split_ifs <;> simp
      · rw [e, strip_solidC]; split_ifs <;> simp
      · simp [strip, mkC]
    · have e : ∀ u v : Atom 3 n, strip { solidC ch u v with label := c.label } =
          strip (solidC ch u v) := fun _ _ => rfl
      by_cases hxy : x = c.y
      · have hsy : side (usG Γ) c.y = none := hxy ▸ hsx
        rw [ftouch_nil (by simp [e, strip_solidC, strip, mkC, hcx, hsx, hsy]),
          ftouch_nil (by simp [strip, hcx, hsy])]
      · simp [hxy, hcx, hsx, hk, touch, absT, strip, mkC, List.filter_cons]
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> exact hlc

/-- [II, (4.17), (4.20)] at a weight or a light weight: the two terms. -/
private theorem rep_schurW_terms {Γ : Graph 3 n} {x : Atom 3 n} {i : ℕ} {c : Comp (Atom 3 n)}
    {ch : Charge} (hx : x.isRight = true) (h : Rep Γ) (hc : Γ.comps[i]? = some c)
    (hk : c.kind = .weight ch ∨ c.kind = .light ch) (mi : List (Atom 3 n)) (co : Coeff) :
    Rep ⟨Γ.comps.eraseIdx i ++ [{ c with minor := mi }], co⟩ ∧
    Rep ⟨Γ.comps.eraseIdx i ++ [{ mkC (.G ch) c.x x with label := c.label },
      { mkC (.G ch) x c.x with label := c.label }, { mkC (.inv ch) x x with label := c.label }],
      co⟩ := by
  have hlc := labelsInt_of_mem h (List.mem_of_getElem? hc)
  have hr : c.kind.isRandom = true := by rcases hk with hk | hk <;> rw [hk] <;> rfl
  have hnG : ∀ ch', c.kind ≠ .G ch' := by rcases hk with hk | hk <;> rw [hk] <;> simp
  obtain ⟨hcx, hcy⟩ := nice_mem h hc hr
  have hcy := hcy hnG
  have hsx : side (usG Γ) x = none := side_right hx
  have hnd : c.kind ≠ .dot := by rcases hk with hk | hk <;> rw [hk] <;> simp
  constructor
  · refine rep_replace hc _ co h hnd ?_ ?_ ?_
    · intro p hp
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hp
      subst hp
      rcases hk with hk | hk <;> simp [strip, hk]
    · simp [strip]
    · intro d hd
      rw [List.mem_singleton] at hd; subst hd; exact hlc
  · refine rep_replace hc _ co h hnd ?_ ?_ ?_
    · intro p hp
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [strip, mkC]
    · rw [ftouch_nil (by simp [strip, mkC, hcx, hsx]), ftouch_nil (by simp [strip, hcx, hcy])]
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> exact hlc

/-- [II, (4.17)] at a solid edge. -/
private theorem rep_schur {Γ : Graph 3 n} {x : Atom 3 n} {i : ℕ} {t : Tracked 3 n}
    (hx : x.isRight = true) (h : Rep Γ) (ht : t ∈ oSchurT x i Γ) : Rep t.g := by
  unfold oSchurT at ht
  split at ht
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  rename_i c hci
  split at ht
  · rename_i ch hk
    split_ifs at ht
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      obtain ⟨h1, h2⟩ := rep_schur_terms hx h hci hk [x] Γ.coeff
      rcases ht with rfl | rfl
      · exact h1
      · exact h2
    · rw [List.mem_singleton.1 ht]; exact h
  · rw [List.mem_singleton.1 ht]; exact h

/-- [II, (4.20)] at a solid edge. -/
private theorem rep_schurRev {Γ : Graph 3 n} {x : Atom 3 n} {i : ℕ} {t : Tracked 3 n}
    (hx : x.isRight = true) (h : Rep Γ) (ht : t ∈ oSchurRevT x i Γ) : Rep t.g := by
  unfold oSchurRevT at ht
  split at ht
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  rename_i c hci
  split at ht
  · rename_i ch hk
    split_ifs at ht
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact (rep_schur_terms hx h hci hk [] Γ.coeff).1
      · exact (rep_schur_terms hx h hci hk [] (-Γ.coeff)).2
    · rw [List.mem_singleton.1 ht]; exact h
  · rw [List.mem_singleton.1 ht]; exact h

/-- [II, (4.17)] at a weight. -/
private theorem rep_schurW {Γ : Graph 3 n} {x : Atom 3 n} {i : ℕ} {t : Tracked 3 n}
    (hx : x.isRight = true) (h : Rep Γ) (ht : t ∈ oSchurWT x i Γ) : Rep t.g := by
  unfold oSchurWT at ht
  split at ht
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  rename_i c hci
  split at ht
  · rename_i ch hk
    split_ifs at ht
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      obtain ⟨h1, h2⟩ := rep_schurW_terms hx h hci (Or.inl hk) [x] Γ.coeff
      rcases ht with rfl | rfl
      · exact h1
      · exact h2
    · rw [List.mem_singleton.1 ht]; exact h
  · rename_i ch hk
    split_ifs at ht
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      obtain ⟨h1, h2⟩ := rep_schurW_terms hx h hci (Or.inr hk) [x] Γ.coeff
      rcases ht with rfl | rfl
      · exact h1
      · exact h2
    · rw [List.mem_singleton.1 ht]; exact h
  · rw [List.mem_singleton.1 ht]; exact h

/-- [II, (4.20)] at a weight. -/
private theorem rep_schurWRev {Γ : Graph 3 n} {x : Atom 3 n} {i : ℕ} {t : Tracked 3 n}
    (hx : x.isRight = true) (h : Rep Γ) (ht : t ∈ oSchurWRevT x i Γ) : Rep t.g := by
  unfold oSchurWRevT at ht
  split at ht
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  rename_i c hci
  split at ht
  · rename_i ch hk
    split_ifs at ht
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact (rep_schurW_terms hx h hci (Or.inl hk) [] Γ.coeff).1
      · exact (rep_schurW_terms hx h hci (Or.inl hk) [] (-Γ.coeff)).2
    · rw [List.mem_singleton.1 ht]; exact h
  · rename_i ch hk
    split_ifs at ht
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact (rep_schurW_terms hx h hci (Or.inr hk) [] Γ.coeff).1
      · exact (rep_schurW_terms hx h hci (Or.inr hk) [] (-Γ.coeff)).2
    · rw [List.mem_singleton.1 ht]; exact h
  · rw [List.mem_singleton.1 ht]; exact h

/-- [II, (4.21)]. -/
private theorem rep_taylor {Γ : Graph 3 n} {D i : ℕ} {t : Tracked 3 n} (h : Rep Γ)
    (ht : t ∈ oTaylorT D i Γ) : Rep t.g := by
  unfold oTaylorT at ht
  split at ht
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  rename_i c hci
  split at ht
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  rename_i ch hk
  dsimp only at ht
  split_ifs at ht
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  have hlc := labelsInt_of_mem h (List.mem_of_getElem? hci)
  obtain ⟨hcx, hcy⟩ := nice_mem h hci (by rw [hk]; rfl)
  have hcy := hcy (by rw [hk]; simp)
  have key : ∀ (new : List (Comp (Atom 3 n))) (co : Coeff),
      (∀ d ∈ new, d.kind = .light ch ∨ d.kind = .wD ch D) → (∀ d ∈ new, d.x = c.x ∧ d.y = c.x) →
      (∀ d ∈ new, d.label = c.label) → Rep ⟨Γ.comps.eraseIdx i ++ new, co⟩ := by
    intro new co hkn hxn hln
    refine rep_replace hci new co h (by rw [hk]; simp) ?_ ?_ ?_
    · intro p hp
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
      rcases hkn d hd with e | e <;> simp [strip, e]
    · rw [ftouch_nil, ftouch_nil]
      · simp [strip, hcx, hcy]
      · intro p hp
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
        simp [strip, (hxn d hd).1, (hxn d hd).2, hcx]
    · intro d hd; rw [hln d hd]; exact hlc
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ht
  rcases ht with ⟨j, -, rfl⟩ | rfl
  · exact key _ _ (fun d hd => by rw [List.eq_of_mem_replicate hd]; simp)
      (fun d hd => by rw [List.eq_of_mem_replicate hd]; simp)
      (fun d hd => by rw [List.eq_of_mem_replicate hd])
  · exact key _ _ (fun d hd => by rw [List.mem_singleton.1 hd]; simp)
      (fun d hd => by rw [List.mem_singleton.1 hd]; simp)
      (fun d hd => by rw [List.mem_singleton.1 hd])

/-- `O^{(x),1}_weight` on a list of components. -/
private theorem obl_splitRegular (us : Fin 3 → Prop) (x : Atom 3 n) :
    ∀ cs : List (Comp (Atom 3 n)), Nice us (cs.map strip) → ∀ p ∈ splitRegular x cs,
      Obl us id (cs.map strip) (p.1.map strip) ∧ ∀ c' ∈ p.1, ∃ c ∈ cs, c'.label = c.label
  | [], _, p, hp => by
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    exact ⟨Obl_refl us id [], by simp⟩
  | c :: cs, hN, p, hp => by
    have hN' : Nice us (cs.map strip) := Nice_sub hN (fun q hq => List.mem_cons_of_mem _ hq)
    have ih := obl_splitRegular us x cs hN'
    have hcons : ∀ q ∈ splitRegular x cs, Obl us id ((c :: cs).map strip) ((c :: q.1).map strip) ∧
        ∀ c' ∈ c :: q.1, ∃ d ∈ c :: cs, c'.label = d.label := by
      intro q hq
      obtain ⟨h1, h2⟩ := ih q hq
      refine ⟨?_, fun c' hc' => ?_⟩
      · have := Obl_cons (strip c) h1
        simpa [mapT] using this
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact ⟨c', List.mem_cons_self .., rfl⟩
        · obtain ⟨d, hd, e⟩ := h2 c' hc'
          exact ⟨d, List.mem_cons_of_mem _ hd, e⟩
    simp only [splitRegular] at hp
    split at hp
    · rename_i ch hk
      split_ifs at hp with hc
      · have hcN := hN (strip c) (List.mem_cons_self ..) (by simp [strip, hk, Kind.isRandom])
        have hcx : side us c.x = none := hcN.1
        have hcy : side us c.y = none := hcN.2 (by simp [strip, hk])
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          obtain ⟨h1, h2⟩ := ih q hq
          refine ⟨?_, fun c' hc' => ?_⟩
          · have := Obl_repl (us := us) (f := id) [strip c] [] (by simp [strip, hk])
              (by simp) (by rw [ftouch_nil (N := [strip c]) (by simp [strip, hcx, hcy])]; simp) h1
            simpa using this
          · obtain ⟨d, hd, e⟩ := h2 c' hc'
            exact ⟨d, List.mem_cons_of_mem _ hd, e⟩
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          obtain ⟨h1, h2⟩ := ih q hq
          refine ⟨?_, fun c' hc' => ?_⟩
          · have := Obl_repl (us := us) (f := id) [strip c] [strip { c with kind := .light ch }]
              (by simp [strip, hk]) (by simp [strip])
              (by rw [ftouch_nil (by simp [strip, hcx, hcy]),
                ftouch_nil (by simp [strip, hcx, hcy])]) h1
            simpa using this
          · rcases List.mem_cons.1 hc' with rfl | hc'
            · exact ⟨c, List.mem_cons_self .., rfl⟩
            · obtain ⟨d, hd, e⟩ := h2 c' hc'
              exact ⟨d, List.mem_cons_of_mem _ hd, e⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact hcons q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hcons q hq

/-- `O^{(x),1}_weight`. -/
private theorem rep_weight1 {Γ : Graph 3 n} {x : Atom 3 n} {t : Tracked 3 n} (h : Rep Γ)
    (ht : t ∈ oWeight1T x Γ) : Rep t.g := by
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨h1, h2⟩ := obl_splitRegular (usG Γ) x Γ.comps (nice_of_rep h) p hp
  refine rep_of_obl GoodMap.id h h1 ?_
  intro c' hc'
  obtain ⟨d, hd, e⟩ := h2 c' hc'
  rw [e]; exact labelsInt_of_mem h hd

/-- A step that changes labels only. -/
private theorem rep_relabel {Γ : Graph 3 n} (h : Rep Γ) (g : Comp (Atom 3 n) → Comp (Atom 3 n))
    (hg : ∀ c, strip (g c) = strip c) (co : Coeff)
    (hl : (⟨Γ.comps.map g, co⟩ : Graph 3 n).LabelsInt) :
    Rep ⟨Γ.comps.map g, co⟩ := by
  refine rep_of_obl GoodMap.id h ?_ hl
  have : (Γ.comps.map g).map strip = Γ.comps.map strip := by
    rw [List.map_map]; exact List.map_congr_left fun c _ => hg c
  show Obl _ _ _ ((Γ.comps.map g).map strip)
  rw [this]
  have := Obl_refl (usG Γ) id (Γ.comps.map strip)
  rwa [map_mapT_id] at this

private theorem rep_dropLabels {Γ : Graph 3 n} (h : Rep Γ) : Rep Γ.dropLabels := by
  unfold Graph.dropLabels
  exact rep_relabel h (fun c => { c with label := none }) (fun _ => rfl) Γ.coeff (fun c hc => by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc; rfl)

private theorem label_int_of {Γ : Graph 3 n} (h : Rep Γ) {ℓ : PQ × Atom 3 n}
    (hℓ : ∃ c ∈ Γ.comps, c.label = some ℓ) : ℓ.2.isRight = true := by
  obtain ⟨c, hc, he⟩ := hℓ
  have := labelsInt_of_mem h hc
  rw [he] at this
  simpa using this

/-- `Q_u = 1 - P_u`. -/
private theorem rep_qToP {Γ : Graph 3 n} {u : Atom 3 n} {t : Tracked 3 n} (h : Rep Γ)
    (hQ : Γ.IsQFormAt u) (ht : t ∈ oQPT u Γ) : Rep t.g := by
  have hu : u.isRight = true := label_int_of h (ℓ := (.Q, u)) hQ.1
  unfold oQPT at ht
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact rep_dropLabels h
  · refine rep_relabel h _ (fun c => by split_ifs <;> rfl) _ (fun c hc => ?_)
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    split_ifs
    · simpa using hu
    · exact labelsInt_of_mem h hd

/-- Factors with the atom of the label in their minor moved into the label group. -/
private theorem rep_absorb {Γ : Graph 3 n} {ℓ : PQ × Atom 3 n} (h : Rep Γ)
    (hℓ : ∃ c ∈ Γ.comps, c.label = some ℓ) : Rep (Γ.absorb ℓ) := by
  have hu := label_int_of h hℓ
  refine rep_relabel h _ (fun c => by split_ifs <;> rfl) _ (fun c hc => ?_)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  split_ifs
  · simpa using hu
  · exact labelsInt_of_mem h hd

/-- `1 = 1_{u = v} + 1_{u ≠ v}` with `v` internal. -/
private theorem rep_split {Γ : Graph 3 n} {u v : Atom 3 n} {t : Tracked 3 n}
    (hv : v.isRight = true) (h : Rep Γ) (ht : t ∈ oSplitT u v Γ) : Rep t.g := by
  unfold oSplitT at ht
  split_ifs at ht
  · rw [List.mem_singleton.1 ht]; exact h
  have key : ∀ κ : Kind, (κ = .dot ∨ κ = .xdot) →
      Rep (⟨Γ.comps ++ [mkC κ u v], Γ.coeff⟩ : Graph 3 n) := by
    intro κ hκ
    refine rep_of_mono h ⟨Γ.comps.map strip, [], [(κ, u, v)], by simp, by simp [strip, mkC],
      by simp, ?_⟩ ?_
    · intro p hp
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨hκ, Or.inr (side_right hv)⟩
    · intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact labelsInt_of_mem h hd
      · rw [List.mem_singleton.1 hd]; rfl
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp only [Tracked.self]
  · exact key _ (Or.inl rfl)
  · exact key _ (Or.inr rfl)

/-- `1_{u ≠ v} = 1 - 1_{u = v}` at a `×`-dotted edge. -/
private theorem rep_xdot {Γ : Graph 3 n} {i : ℕ} {t : Tracked 3 n} (h : Rep Γ)
    (ht : t ∈ oXdotT i Γ) : Rep t.g := by
  unfold oXdotT at ht
  split at ht
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  rename_i c hci
  split_ifs at ht with hc
  rotate_left
  · rw [List.mem_singleton.1 ht]; exact h
  have hp : (Γ.comps.map strip).Perm ((Γ.comps.eraseIdx i).map strip ++ [strip c]) := by
    have := (perm_eraseIdx hci).map strip
    rw [List.map_cons] at this
    exact this.trans (List.perm_append_singleton _ _).symm
  have hl : ∀ d ∈ Γ.comps.eraseIdx i, d.label.all (fun ℓ => ℓ.2.isRight) = true :=
    fun d hd => labelsInt_of_mem h (List.mem_of_mem_eraseIdx hd)
  have hE := rep_elem h (List.mem_of_getElem? hci)
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp only [Tracked.self]
  · refine rep_of_mono h ⟨(Γ.comps.eraseIdx i).map strip, [strip c], [], hp, by simp,
      by simp [strip, hc.1], by simp⟩ hl
  · refine rep_of_mono h ⟨(Γ.comps.eraseIdx i).map strip, [strip c], [(.dot, c.x, c.y)], hp,
      by simp [strip, mkC], by simp [strip, hc.1], ?_⟩ ?_
    · intro p hp'
      rw [List.mem_singleton] at hp'; subst hp'
      exact ⟨Or.inl rfl, hE.2.2 hc.1⟩
    · intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hl d hd
      · rw [List.mem_singleton.1 hd]; rfl

/-- Removal of a dotted edge whose ends are joined by the other dotted edges. -/
private theorem rep_dropDot {Γ : Graph 3 n} {i : ℕ} {c : Comp (Atom 3 n)}
    (hci : Γ.comps[i]? = some c) (hk : c.kind = .dot)
    (hb : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n).SameBlock c.x c.y) (h : Rep Γ) :
    Rep (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n) := by
  set Γ' : Graph 3 n := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩
  have hp := perm_eraseIdx hci
  have hsub : ∀ d ∈ Γ'.comps, d ∈ Γ.comps := fun d hd => List.mem_of_mem_eraseIdx hd
  have hsb : ∀ u v, Γ'.SameBlock u v ↔ Γ.SameBlock u v := by
    intro u v
    rw [sameBlock_iff_dotR, sameBlock_iff_dotR]
    constructor
    · refine fun hr => reach_map id (fun a b hab => ?_) hr
      rw [SimpleGraph.fromRel_adj] at hab
      obtain ⟨hne, hab⟩ := hab
      refine ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, ?_⟩).reachable
      rcases hab with ⟨p, hpm, h1, h2, h3⟩ | ⟨p, hpm, h1, h2, h3⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hpm
        exact Or.inl ⟨strip d, List.mem_map_of_mem (hsub d hd), h1, h2, h3⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hpm
        exact Or.inr ⟨strip d, List.mem_map_of_mem (hsub d hd), h1, h2, h3⟩
    · refine fun hr => reach_map id (fun a b hab => ?_) hr
      rw [SimpleGraph.fromRel_adj] at hab
      obtain ⟨hne, hab⟩ := hab
      have key : ∀ a b, dotR (Γ.comps.map strip) a b →
          (SimpleGraph.fromRel (dotR (Γ'.comps.map strip))).Reachable a b := by
        rintro a b ⟨p, hpm, h1, rfl, rfl⟩
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hpm
        rcases List.mem_cons.1 (hp.mem_iff.1 hd) with rfl | hd'
        · rw [← sameBlock_iff_dotR]; exact hb
        · by_cases he : (strip d).2.1 = (strip d).2.2
          · rw [he]
          · exact ((SimpleGraph.fromRel_adj _ _ _).2
              ⟨he, Or.inl ⟨strip d, List.mem_map_of_mem hd', h1, rfl, rfl⟩⟩).reachable
      rcases hab with hab | hab
      · exact key _ _ hab
      · exact (key _ _ hab).symm
  have hus : usG Γ' = usG Γ := by
    funext a; apply propext
    simp only [usG, Graph.Unpinned, hsb]
  have habs : ∀ d, absG Γ' d = absG Γ d := fun d => by simp only [absG, hus]
  obtain ⟨hA, hE, hT, hG, hL⟩ := h
  refine ⟨fun u v hne huv => ?_, fun d hd => ?_, ?_, fun d hd => hG d (hsub d hd),
    fun d hd => hL d (hsub d hd)⟩
  · obtain ⟨b, hb'⟩ := hA u v hne ((hsb u v).1 huv)
    exact ⟨b, (hsb _ _).2 hb'⟩
  · rw [habs]; exact hE d (hsub d hd)
  · rw [hus]
    refine AbsT_perm ?_ hT
    unfold tL
    rw [hus]
    have := ((hp.map strip).map (absT (usG Γ))).filter touch
    refine this.trans ?_
    simp [strip, touch, absT, hk, Γ']

/-- An end of a component other than a dotted edge moved to an atom of its block. -/
private theorem rep_rebase {Γ : Graph 3 n} {i : ℕ} {c : Comp (Atom 3 n)} {u v : Atom 3 n}
    (hci : Γ.comps[i]? = some c) (hk : c.kind ≠ .dot) (hb : Γ.SameBlock u v) (h : Rep Γ) :
    Rep (⟨Γ.comps.set i
      { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y }, Γ.coeff⟩ :
        Graph 3 n) := by
  set c' : Comp (Atom 3 n) :=
    { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y }
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hci
  have hside : ∀ w, side (usG Γ) (if w = u then v else w) = side (usG Γ) w := by
    intro w
    split_ifs with hw
    · subst hw
      by_cases huv : w = v
      · rw [huv]
      · obtain ⟨b, hb1⟩ := h.1 w v huv hb
        obtain ⟨b', hb2⟩ := h.1 v w (Ne.symm huv) hb.symm
        rw [(side_usG_none Γ w).2 ((not_unpinned_iff Γ w).2 (Or.inr ⟨b, hb1⟩)),
          (side_usG_none Γ v).2 ((not_unpinned_iff Γ v).2 (Or.inr ⟨b', hb2⟩))]
    · rfl
  have habs : absT (usG Γ) (strip c') = absT (usG Γ) (strip Γ.comps[i]) := by
    simp only [absT, strip, c', hside]
  have hng : Γ.comps[i].kind ≠ .ghost := h.2.2.2.1 _ (List.getElem_mem hi)
  refine rep_of_obl GoodMap.id h ?_ ?_
  · have hp : (Γ.comps.map strip).Perm ([strip Γ.comps[i]] ++ (Γ.comps.eraseIdx i).map strip) := by
      have := (perm_eraseIdx hci).map strip
      simpa using this
    have hp' : ((Γ.comps.set i c').map strip).Perm
        ([strip c'] ++ (Γ.comps.eraseIdx i).map strip) := by
      have := (List.set_perm_cons_eraseIdx hi c').map strip
      simpa using this
    refine Obl_perm hp hp' (Obl_repl _ _ (by simpa [strip] using hk) ?_ ?_ ?_)
    · intro p hp
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨hk, hng, fun _ => by simp [habs]⟩
    · simp only [List.map_cons, List.map_nil, habs]; exact List.Perm.refl _
    · have := Obl_refl (usG Γ) id ((Γ.comps.eraseIdx i).map strip)
      rwa [map_mapT_id] at this
  · intro d hd
    rcases List.mem_or_eq_of_mem_set hd with hd | rfl
    · exact labelsInt_of_mem h hd
    · show Γ.comps[i].label.all _ = true
      exact labelsInt_of_mem h (List.getElem_mem hi)

end Replace

/-! ## The merging operation -/

section MergeDots

variable {k n : ℕ}

/-- The graph on the atoms whose edges are the dotted components of a list. -/
private def dg (L : List (Comp (Atom k n))) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ L, c.kind = .dot ∧ c.x = u ∧ c.y = v

private theorem dg_adj {L : List (Comp (Atom k n))} {a b : Atom k n} :
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
private theorem dg_reach_of_mem {L : List (Comp (Atom k n))} {c : Comp (Atom k n)} (hc : c ∈ L)
    (hk : c.kind = .dot) : (dg L).Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (dg_adj.2 ⟨h, c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩).reachable


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

end MergeDots

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

/-- The representative of an atom in the dot blocks of a graph. -/
private def Graph.mrep (Γ : Graph k n) : Atom k n → Atom k n :=
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
private def mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
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
private structure MergeSpec (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps = Γ.comps.filterMap (mergeComp Γ.mrep t.f)
  coeff_eq : t.g.coeff = Γ.coeff
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_surj : Function.Surjective t.f
  f_inr : ∃ g : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (g i)) ∧ Function.Surjective g
  f_eq : ∀ u v, Γ.mrep u = Γ.mrep v → u.isRight = true → v.isRight = true → t.f u = t.f v
  f_ne : ∀ u v, Γ.mrep u ≠ Γ.mrep v → t.f u ≠ t.f v
  xdot_ne : ∀ c ∈ Γ.comps, c.kind = .xdot → Γ.mrep c.x ≠ Γ.mrep c.y

private theorem mergeT_spec {Γ : Graph k n} {t : Tracked k n} (h : Γ.mergeT = some t) :
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

private theorem mergeComp_kind {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
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

private theorem mergeComp_dot {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hk : c.kind = .dot) :
    mergeComp rep f c = if f c.x = f c.y then none else some (c.map f) := by
  unfold mergeComp
  by_cases h : f c.x = f c.y
  · simp [hk, h]
  · simp [hk, h, Kind.isSolid]

variable {Γ : Graph k n} {t : Tracked k n}

private theorem MergeSpec.mem_comps (hs : MergeSpec Γ t) {c' : Comp (Atom k t.nOut)} :
    c' ∈ t.g.comps ↔ ∃ c ∈ Γ.comps, mergeComp Γ.mrep t.f c = some c' := by
  rw [hs.comps_eq, List.mem_filterMap]

private theorem MergeSpec.mem_of_dot (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) (hf : t.f c.x ≠ t.f c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [mergeComp_dot hk, ite_eq_right hf]⟩

end MergeFacts

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


end MergeBlocks

/-! ## `O_merge` and `O_dot` keep the clauses -/

section MergeRep

variable {n : ℕ}

private theorem mergeComp_cases {m : ℕ} {rep : Atom 3 n → Atom 3 n} {f : Atom 3 n → Atom 3 m}
    {c : Comp (Atom 3 n)} {c' : Comp (Atom 3 m)} (h : mergeComp rep f c = some c') :
    c' = c.map f ∨ (c.kind.isSolid = true ∧ rep c.x = rep c.y ∧
      c' = { c.map f with kind := c.kind.toWeight, y := f c.x }) := by
  unfold mergeComp at h
  split_ifs at h with h1 h2
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact Or.inr ⟨h2.1, h2.2, (Option.some.inj h).symm⟩
  · exact Or.inl (Option.some.inj h).symm

private theorem isRandom_of_solid {κ : Kind} (h : κ.isSolid = true) : κ.isRandom = true := by
  cases κ <;> simp_all [Kind.isSolid, Kind.isRandom]

/-- `O_merge`. -/
private theorem rep_of_merge {Δ : Graph 3 n} {t : Tracked 3 n} (h : Rep Δ)
    (ht : Δ.mergeT = some t) : Rep t.g := by
  have hs := mergeT_spec ht
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have hside : ∀ (us : Fin 3 → Prop) (u : Atom 3 n), side us (t.f u) = side us u := by
    intro us u
    rcases u with a | b
    · rw [hs.f_inl]; rfl
    · rw [hg]; rfl
  have hus : usG t.g = usG Δ := by
    funext a
    apply propext
    simp only [usG, Graph.Unpinned, Sum.isLeft_inl, true_and]
    constructor
    · intro h' b hb
      have := (hs.sameBlock_iff (.inl a) (.inr b)).2 hb
      rw [hs.f_inl, hg] at this
      exact h' _ this
    · intro h' b' hb'
      obtain ⟨b, rfl⟩ := hgs b'
      rw [← hg b] at hb'
      have e := hs.f_inl a
      rw [← e] at hb'
      exact h' b ((hs.sameBlock_iff _ _).1 hb')
  set us := usG Δ
  have habs : ∀ c, absT us (strip (c.map t.f)) = absT us (strip c) := by
    intro c; simp [absT, strip, Comp.map, hside]
  have hN := nice_of_rep h
  -- a component of `Δ` is kept or becomes a weight inside a block
  have hconv : ∀ c ∈ Δ.comps, c.kind.isSolid = true → Δ.mrep c.x = Δ.mrep c.y →
      side us c.x = none ∧ side us c.y = none := by
    intro c hc hsol hr
    have hcx := (hN (strip c) (List.mem_map_of_mem hc) (isRandom_of_solid hsol)).1
    refine ⟨hcx, ?_⟩
    have hb := (Δ.mrep_eq_iff _ _).1 hr
    exact (side_usG_none Δ _).2
      (pinned_of_sameBlock hb.symm ((side_usG_none Δ _).1 hcx))
  have hcomp : ∀ c' ∈ t.g.comps, ∃ c ∈ Δ.comps, (absT us (strip c') = absT us (strip c) ∨
      (absT us (strip c') = (c'.kind, none, none) ∧ ∃ ch, c.kind = .G ch ∧ c'.kind = .weight ch)) ∧
      c'.label = c.label.map (Prod.map id t.f) := by
    intro c' hc'
    obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
    refine ⟨c, hc, ?_, mergeComp_label hm⟩
    rcases mergeComp_cases hm with rfl | ⟨hsol, hr, rfl⟩
    · exact Or.inl (habs c)
    · right
      obtain ⟨hcx, -⟩ := hconv c hc hsol hr
      obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
        cases hk : c.kind <;> simp_all [Kind.isSolid]
      refine ⟨?_, ch, hch, by simp [hch, Kind.toWeight]⟩
      simp [absT, strip, Comp.map, hside, hcx]
  obtain ⟨hA, hE, hT, hG, hL⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u' v' hne h'
    obtain ⟨u, rfl⟩ := hs.f_surj u'
    obtain ⟨v, rfl⟩ := hs.f_surj v'
    obtain ⟨b, hb⟩ := hA u v (fun he => hne (by rw [he])) ((hs.sameBlock_iff u v).1 h')
    have := (hs.sameBlock_iff u (.inr b)).2 hb
    rw [hg] at this
    exact ⟨g b, this⟩
  · intro c' hc'
    obtain ⟨c, hc, hab, -⟩ := hcomp c' hc'
    rw [absG, hus]
    rcases hab with hab | ⟨hab, -⟩
    · rw [hab]; exact hE c hc
    · rw [hab]; exact elemOK_none _
  · rw [hus]
    refine AbsT_perm ?_ hT
    unfold tL
    rw [hs.comps_eq, List.map_map, List.map_map]
    have key : ∀ L : List (Comp (Atom 3 n)), (∀ c ∈ L, c ∈ Δ.comps) →
        ((L.filterMap (mergeComp Δ.mrep t.f)).map (absT us ∘ strip)).filter touch =
          (L.map (absT us ∘ strip)).filter touch := by
      intro L hLs
      induction L with
      | nil => rfl
      | cons c L ih =>
        have ih' := ih fun d hd => hLs d (List.mem_cons_of_mem _ hd)
        have hc := hLs c (List.mem_cons_self ..)
        rw [List.filterMap_cons]
        rcases hm : mergeComp Δ.mrep t.f c with _ | c'
        · obtain ⟨hk, -⟩ := mergeComp_none hm
          simp only [List.map_cons, List.filter_cons, Function.comp_apply, ih']
          simp [touch, absT, strip, hk]
        · simp only [List.map_cons, List.filter_cons, Function.comp_apply, ih']
          rcases mergeComp_cases hm with rfl | ⟨hsol, hr, rfl⟩
          · rw [habs c]
          · obtain ⟨hcx, hcy⟩ := hconv c hc hsol hr
            have h1 : touch (absT us (strip
                { c.map t.f with kind := c.kind.toWeight, y := t.f c.x })) = false := by
              simp [touch, absT, strip, Comp.map, hside, hcx]
            have h2 : touch (absT us (strip c)) = false := by
              simp [touch, absT, strip, hcx, hcy]
            simp [h1, h2]
    rw [hus, key Δ.comps fun _ h => h]
  · intro c' hc' hk
    obtain ⟨c, hc, hab, -⟩ := hcomp c' hc'
    obtain ⟨c0, hc0, hm⟩ := hs.mem_comps.1 hc'
    rcases mergeComp_kind hm with e | ⟨ch, -, e⟩
    · exact hG c0 hc0 (e ▸ hk)
    · rw [hk] at e; cases e
  · intro c' hc'
    obtain ⟨c, hc, -, hlab⟩ := hcomp c' hc'
    rw [hlab]
    have := hL c hc
    rcases hcl : c.label with _ | ⟨pq, w⟩
    · rfl
    · rw [hcl] at this
      simp only [Option.all_some, Option.map_some, Prod.map] at this ⊢
      rcases w with a | b
      · simp at this
      · rw [hg]; rfl

/-- The pairs of `Graph.splitPairs` are the ends of a solid or `×`-dotted edge. -/
private theorem mem_foldl_uniq {α : Type*} (F : List α → α → List α)
    (hF : ∀ acc p, F acc p = acc ∨ F acc p = acc ++ [p]) :
    ∀ (cand acc : List α) (q : α), q ∈ cand.foldl F acc → q ∈ acc ∨ q ∈ cand
  | [], acc, q, hq => Or.inl hq
  | p :: cand, acc, q, hq => by
    rw [List.foldl_cons] at hq
    rcases mem_foldl_uniq F hF cand (F acc p) q hq with h | h
    · rcases hF acc p with e | e
      · rw [e] at h; exact Or.inl h
      · rw [e, List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem splitPairs_mem {k : ℕ} {Γ : Graph k n} {p : Atom k n × Atom k n × Bool}
    (hp : p ∈ Γ.splitPairs) :
    ∃ c ∈ Γ.comps, (c.kind.isSolid = true ∨ c.kind = .xdot) ∧ c.x = p.1 ∧ c.y = p.2.1 := by
  unfold Graph.splitPairs at hp
  simp only [List.mem_filterMap] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  have hpq : p.1 = q.1 ∧ p.2.1 = q.2 := by
    split_ifs at hqp
    obtain rfl := Option.some.inj hqp
    exact ⟨rfl, rfl⟩
  rcases mem_foldl_uniq _ (fun acc p => by split_ifs <;> simp) _ [] q hq with hq | hq
  · cases hq
  obtain ⟨c, hc, hcq⟩ := List.mem_filterMap.1 hq
  split_ifs at hcq with hcond
  obtain rfl := Option.some.inj hcq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hcond
  exact ⟨c, hc, hcond.1, hpq.1.symm, hpq.2.symm⟩

/-- One term of `O_dot` before `O_merge`. -/
private theorem rep_dotChoice {Γ : Graph 3 n} (h : Rep Γ)
    (A : List (Atom 3 n × Atom 3 n × Bool)) : Rep (Γ.dotChoice Γ.splitPairs A) := by
  unfold Graph.dotChoice
  simp only
  set P : Comp (Atom 3 n) → Bool := fun c => !(c.kind == .xdot &&
    Γ.splitPairs.any fun p => !p.2.2 && ((p.1 == c.x && p.2.1 == c.y) ||
      (p.1 == c.y && p.2.1 == c.x)))
  have hperm : (Γ.comps.map strip).Perm
      ((Γ.comps.filter P).map strip ++ (Γ.comps.filter fun c => !P c).map strip) := by
    rw [← List.map_append]; exact ((List.filter_append_perm P Γ.comps).map strip).symm
  have hN := nice_of_rep h
  refine rep_of_mono h ⟨(Γ.comps.filter P).map strip, (Γ.comps.filter fun c => !P c).map strip,
    _, hperm, by rw [List.map_append], ?_, ?_⟩ ?_
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
    have := (List.mem_filter.1 hc).2
    simp only [P, Bool.not_not, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hq
    obtain ⟨p, hpS, hpd⟩ := List.mem_filterMap.1 hd
    obtain ⟨c, hc, hck, hcx, hcy⟩ := splitPairs_mem hpS
    have hend : side (usG Γ) p.1 = none ∨ side (usG Γ) p.2.1 = none := by
      rw [← hcx, ← hcy]
      rcases hck with hck | hck
      · exact Or.inl (hN (strip c) (List.mem_map_of_mem hc) (isRandom_of_solid hck)).1
      · exact (rep_elem h hc).2.2 hck
    split_ifs at hpd
    · obtain rfl := Option.some.inj hpd
      exact ⟨Or.inl rfl, hend⟩
    · obtain rfl := Option.some.inj hpd
      exact ⟨Or.inr rfl, hend⟩
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact labelsInt_of_mem h (List.mem_of_mem_filter hd)
    · obtain ⟨p, -, hpd⟩ := List.mem_filterMap.1 hd
      split_ifs at hpd
      · obtain rfl := Option.some.inj hpd; rfl
      · obtain rfl := Option.some.inj hpd; rfl

/-- `O_dot`. -/
private theorem rep_dot {Γ : Graph 3 n} {t : Tracked 3 n} (h : Rep Γ) (ht : t ∈ oDotT Γ) :
    Rep t.g := by
  unfold oDotT at ht
  simp only at ht
  split_ifs at ht
  · rw [List.mem_singleton.1 ht]; exact h
  · rw [List.mem_singleton.1 ht]; exact h
  · obtain ⟨A, -, hA⟩ := List.mem_filterMap.1 ht
    exact rep_of_merge (rep_dotChoice h A) hA

end MergeRep

/-! ## The operations inside `P_x` -/

section PSteps

variable {n : ℕ}

private theorem strip_map {n' : ℕ} (f : Atom 3 n → Atom 3 n') (c : Comp (Atom 3 n)) :
    strip (c.map f) = mapT f (strip c) := rfl

private theorem strip_liftCs (j : ℕ) (L : List (Comp (Atom 3 n))) :
    (liftCs j L).map strip = (L.map strip).map (mapT (liftA j)) := by
  simp [liftCs, Function.comp_def, strip_map]

private theorem strip_pCore (Γ : Graph 3 n) :
    Γ.pCore.comps.map strip =
      (Γ.comps.filter fun c => c.label.isSome || !c.kind.isRandom).map strip := by
  simp [Graph.pCore, Function.comp_def, strip]

private theorem perm_pCore (Γ : Graph 3 n) :
    (Γ.comps.map strip).Perm (Γ.pCore.comps.map strip ++ Γ.pEnv.map strip) := by
  rw [strip_pCore, Graph.pEnv, ← List.map_append]
  apply List.Perm.map
  have h1 := List.filter_append_perm
    (fun c : Comp (Atom 3 n) => c.label.isSome || !c.kind.isRandom) Γ.comps
  have h2 : (Γ.comps.filter fun c => !(c.label.isSome || !c.kind.isRandom)) =
      Γ.comps.filter fun c => c.label.isNone && c.kind.isRandom :=
    List.filter_congr fun c _ => by cases c.label <;> simp
  rw [h2] at h1
  exact h1.symm

private theorem nice_pCore {Γ : Graph 3 n} (h : Rep Γ) : Nice (usG Γ) (Γ.pCore.comps.map strip) :=
  Nice_sub (nice_of_rep h) fun p hp =>
    (perm_pCore Γ).mem_iff.2 (List.mem_append_left _ hp)

private theorem label_pCore (Γ : Graph 3 n) : ∀ c ∈ Γ.pCore.comps, c.label = none := by
  intro c hc
  simp only [Graph.pCore, List.mem_map] at hc
  obtain ⟨d, -, rfl⟩ := hc
  rfl

/-- A term of an operation on the components `L`: an injective atom map fixing the external
atoms, the obligation of a step, and internal label atoms. -/
private def GoodT (us : Fin 3 → Prop) (L : List (KT n)) (t₀ : Tracked 3 n) : Prop :=
  GoodMap t₀.f ∧ Obl us t₀.f L (t₀.g.comps.map strip) ∧ t₀.g.LabelsInt

/-- The output of `pLiftT`: the operation inside `P_x` on `Γ.pCore`, the factors of `Γ_ω` put
back. -/
private theorem rep_pLift {Γ : Graph 3 n} {x : Atom 3 n} {E : TExpansion 3 n} {t : Tracked 3 n}
    (h : Rep Γ) (hP : Γ.IsPFormAt x)
    (hE : ∀ t₀ ∈ E, GoodT (usG Γ) (Γ.pCore.comps.map strip) t₀)
    (ht : t ∈ pLiftT x Γ E) : Rep t.g := by
  unfold pLiftT at ht
  obtain ⟨t₀, ht₀, he⟩ := List.mem_filterMap.1 ht
  split_ifs at he
  obtain rfl := Option.some.inj he
  obtain ⟨hf, ho, hl⟩ := hE t₀ ht₀
  have hx : x.isRight = true := label_int_of h hP.1
  have hfx : (t₀.f x).isRight = true := by
    rcases x with a | b
    · simp at hx
    · exact hf.inr b
  refine rep_of_obl hf h ?_ ?_
  · have hst : (t₀.g.comps.map fun c => if c.kind.isRandom then
        { c with label := some (.P, t₀.f x) } else c).map strip = t₀.g.comps.map strip := by
      rw [List.map_map]
      exact List.map_congr_left fun c _ => by simp only [Function.comp_apply]; split_ifs <;> rfl
    have ha := Obl_append ho (Γ.pEnv.map strip)
    refine Obl_perm (perm_pCore Γ) ?_ ha
    simp only [List.map_append, hst, List.map_map]
    exact List.Perm.refl _
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      split_ifs
      · simpa using hfx
      · exact hl d hd
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      have := (List.mem_filter.1 hd).2
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
      simp [Comp.map, this.1]

/-- `O^{(x),1}_weight` inside `P_x`. -/
private theorem rep_pWeight1 {Γ : Graph 3 n} {x : Atom 3 n} {t : Tracked 3 n} (h : Rep Γ)
    (hP : Γ.IsPFormAt x) (ht : t ∈ pLiftT x Γ (oWeight1T x Γ.pCore)) : Rep t.g := by
  refine rep_pLift h hP (fun t₀ ht₀ => ?_) ht
  unfold oWeight1T at ht₀
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht₀
  obtain ⟨h1, h2⟩ := obl_splitRegular (usG Γ) x Γ.pCore.comps (nice_pCore h) p hp
  refine ⟨GoodMap.id, h1, fun c hc => ?_⟩
  obtain ⟨d, hd, e⟩ := h2 c hc
  show c.label.all _ = true
  rw [e, label_pCore Γ d hd]; rfl

private theorem mem_dTerms {V : Type*} [DecidableEq V] {p q : V} {cs : List (Comp V)}
    {d : List (Comp V)} (hd : d ∈ dTerms p q cs) :
    ∃ m : Fin cs.length, ∃ ps, cs[m].dPieces p q = some ps ∧ d = cs.eraseIdx m ++ ps := by
  unfold dTerms at hd
  obtain ⟨m, -, hm⟩ := List.mem_filterMap.1 hd
  obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hm
  exact ⟨m, ps, hps, rfl⟩

private theorem dPieces_eq {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) :
    ∃ ch : Charge, (c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) ∧
      ps = [solidC ch c.x (if ch = .plus then p else q),
        solidC ch (if ch = .plus then q else p) (if c.kind.isWeight then c.x else c.y)] := by
  unfold Comp.dPieces at h
  rcases hk : c.kind with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
    simp only [hk] at h
  all_goals first | cases h | (cases ch <;> simp only at h <;> cases h <;> simp [Kind.isWeight])

/-- The two factors of `-∂_{h_{pq}} c` at internal atoms `p`, `q`. -/
private theorem dPieces_touch {us : Fin 3 → Prop} {p q : Atom 3 n} (hp : side us p = none)
    (hq : side us q = none) {c : Comp (Atom 3 n)} {ps : List (Comp (Atom 3 n))}
    (h : c.dPieces p q = some ps) (hc : side us c.x = none)
    (hc2 : (∀ ch, c.kind ≠ .G ch) → side us c.y = none) :
    (((ps.map strip).map (absT us)).filter touch).Perm (([strip c].map (absT us)).filter touch) ∧
      ∀ d ∈ ps, d.kind ≠ .dot ∧ d.kind ≠ .ghost ∧ d.kind ≠ .xdot ∧ d.label = none := by
  obtain ⟨ch, hk, rfl⟩ := dPieces_eq h
  have hP : side us (if ch = .plus then p else q) = none := by split_ifs <;> assumption
  have hQ : side us (if ch = .plus then q else p) = none := by split_ifs <;> assumption
  generalize (if ch = .plus then p else q) = P at hP
  generalize (if ch = .plus then q else p) = Q at hQ
  refine ⟨?_, ?_⟩
  · rcases hk with hk | hk | hk
    · have hw : c.kind.isWeight = false := by rw [hk]; rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases hqy : Q = c.y
      · rw [ftouch_nil (by simp [strip_solidC, hc, hP, hQ, ← hqy]),
          ftouch_nil (by simp [strip, hc, ← hqy, hQ])]
      · simp [strip_solidC, hqy, absT, strip, touch, hk, hc, hQ, hP, List.filter_cons]
    · have hw : c.kind.isWeight = true := by rw [hk]; rfl
      have hcy := hc2 (by rw [hk]; simp)
      simp only [hw, ↓reduceIte]
      rw [ftouch_nil (by simp [strip_solidC, hc, hP, hQ]), ftouch_nil (by simp [strip, hc, hcy])]
    · have hw : c.kind.isWeight = true := by rw [hk]; rfl
      have hcy := hc2 (by rw [hk]; simp)
      simp only [hw, ↓reduceIte]
      rw [ftouch_nil (by simp [strip_solidC, hc, hP, hQ]), ftouch_nil (by simp [strip, hc, hcy])]
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> (unfold solidC; split_ifs <;> simp [mkC])

/-- The obligation from a split of the input into replaced and kept components. -/
private theorem obl_of_split {n' : ℕ} {us : Fin 3 → Prop} {f : Atom 3 n → Atom 3 n'}
    {L K R₀ : List (KT n)} {L' N₀ : List (KT n')} (hp : L.Perm (R₀ ++ K))
    (hp' : L'.Perm (N₀ ++ K.map (mapT f))) (hR : ∀ p ∈ R₀, p.1 ≠ .dot)
    (hN : ∀ p ∈ N₀, p.1 ≠ .dot ∧ p.1 ≠ .ghost ∧ (p.1 = .xdot → absT us p ∈ R₀.map (absT us)))
    (ht : ((N₀.map (absT us)).filter touch).Perm ((R₀.map (absT us)).filter touch)) :
    Obl us f L L' :=
  Obl_perm hp hp' (Obl_repl R₀ N₀ hR hN ht (Obl_refl us f K))

private theorem side_liftA {us : Fin 3 → Prop} (j : ℕ) (u : Atom 3 n) :
    side us (liftA j u) = side us u := side_map (GoodMap.lift j) us u

@[simp] private theorem side_newA {us : Fin 3 → Prop} {j : ℕ} (i : Fin j) :
    side us (newA i : Atom 3 (n + j)) = none := rfl

/-- `-∂_{h_{pq}}` of a lifted product of components at internal atoms `p`, `q`. -/
private theorem obl_dTerms {us : Fin 3 → Prop} (L : List (Comp (Atom 3 n)))
    (hN : Nice us (L.map strip)) {p q : Atom 3 (n + 1)} (hp : side us p = none)
    (hq : side us q = none) {d : List (Comp (Atom 3 (n + 1)))}
    (hd : d ∈ dTerms p q (liftCs 1 L)) :
    Obl us (liftA 1) (L.map strip) (d.map strip) ∧
      ∀ c ∈ d, (∃ c₀ ∈ L, c₀.map (liftA 1) = c) ∨ c.label = none := by
  obtain ⟨m, ps, hps, rfl⟩ := mem_dTerms hd
  have hm : m.1 < L.length := by simpa [liftCs] using m.2
  have hcm : (liftCs 1 L)[m] = (L[m.1]'hm).map (liftA 1) := by
    rw [Fin.getElem_fin]; unfold liftCs; rw [List.getElem_map]
  have he : (liftCs 1 L).eraseIdx m = liftCs 1 (L.eraseIdx m) := by
    simp [liftCs, List.eraseIdx_map]
  rw [hcm] at hps
  have hmem : strip (L[m.1]'hm) ∈ L.map strip := List.mem_map_of_mem (List.getElem_mem hm)
  obtain ⟨h1, h2⟩ := dPieces_touch hp hq hps
    (by rw [show ((L[m.1]'hm).map (liftA 1)).x = liftA 1 (L[m.1]'hm).x from rfl, side_liftA]
        exact (hN _ hmem (by
          rcases dPieces_eq hps with ⟨ch, hk | hk | hk, -⟩ <;>
            simp only [Comp.map] at hk <;> simp [strip, hk, Kind.isRandom])).1)
    (fun hG => by
      rw [show ((L[m.1]'hm).map (liftA 1)).y = liftA 1 (L[m.1]'hm).y from rfl, side_liftA]
      refine (hN _ hmem ?_).2 hG
      rcases dPieces_eq hps with ⟨ch, hk | hk | hk, -⟩ <;>
        simp only [Comp.map] at hk <;> simp [strip, hk, Kind.isRandom])
  refine ⟨?_, ?_⟩
  · refine obl_of_split (R₀ := [strip (L[m.1]'hm)]) (N₀ := ps.map strip)
      (K := (L.eraseIdx m).map strip) ?_ ?_ ?_ ?_ ?_
    · have := (List.getElem_cons_eraseIdx_perm hm).symm.map strip
      simpa using this
    · rw [he, List.map_append, strip_liftCs]; exact List.perm_append_comm
    · intro p hp'
      rw [List.mem_singleton] at hp'; subst hp'
      intro hk
      rcases dPieces_eq hps with ⟨ch, hk' | hk' | hk', -⟩ <;>
        simp only [Comp.map] at hk' <;> simp [strip, hk'] at hk
    · intro p hp'
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp'
      obtain ⟨a1, a2, a3, -⟩ := h2 c hc
      exact ⟨a1, a2, fun h' => absurd h' a3⟩
    · refine h1.trans ?_
      simp only [List.map_cons, List.map_nil]
      rw [show strip ((L[m.1]'hm).map (liftA 1)) = mapT (liftA 1) (strip (L[m.1]'hm)) from rfl,
        absT_mapT (GoodMap.lift 1)]
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · rw [he] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      exact Or.inl ⟨c₀, List.mem_of_mem_eraseIdx hc₀, rfl⟩
    · exact Or.inr (h2 c hc).2.2.2

private theorem labelsInt_of_lift {n' : ℕ} {f : Atom 3 n → Atom 3 n'}
    {L : List (Comp (Atom 3 n))} (hl : ∀ c ∈ L, c.label = none) {c : Comp (Atom 3 n')}
    (hc : (∃ c₀ ∈ L, c₀.map f = c) ∨ c.label = none) : c.label = none := by
  rcases hc with ⟨c₀, hc₀, rfl⟩ | hc
  · simp [Comp.map, hl c₀ hc₀]
  · exact hc

/-- [II, (4.23)] at the first light weight of positive charge on `x`. -/
private theorem obl_wP2Pos {us : Fin 3 → Prop} {x : Atom 3 n} (hx : x.isRight = true)
    {H : Graph 3 n} (hN : Nice us (H.comps.map strip)) (hl : ∀ c ∈ H.comps, c.label = none)
    {E : TExpansion 3 n} (hE : oWeightP2Pos x H = some E) :
    ∀ t₀ ∈ E, GoodT us (H.comps.map strip) t₀ := by
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  rename_i i hi
  dsimp only at hE
  obtain rfl := Option.some.inj hE
  obtain ⟨hil, hik, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at hik
  have hsx : side us (liftA 1 x : Atom 3 (n + 1)) = none := by rw [side_liftA]; exact side_right hx
  have hmem : strip H.comps[i] ∈ H.comps.map strip := List.mem_map_of_mem (List.getElem_mem hil)
  obtain ⟨hcx, hcy⟩ := hN _ hmem (by simp [strip, hik.1, Kind.isRandom])
  replace hcy : side us H.comps[i].y = none := hcy (by simp [strip, hik.1])
  replace hcx : side us H.comps[i].x = none := hcx
  have hp : (H.comps.map strip).Perm ([strip H.comps[i]] ++ (H.comps.eraseIdx i).map strip) := by
    have := (List.getElem_cons_eraseIdx_perm hil).symm.map strip
    simpa using this
  have hlr : ∀ c ∈ liftCs 1 (H.comps.eraseIdx i), c.label = none := fun c hc =>
    labelsInt_of_lift (L := H.comps.eraseIdx i)
      (fun c hc => hl c (List.mem_of_mem_eraseIdx hc)) (Or.inl (List.mem_map.1 hc))
  have hlH : ∀ c ∈ liftCs 1 H.comps, c.label = none := fun c hc =>
    labelsInt_of_lift hl (Or.inl (List.mem_map.1 hc))
  intro t₀ ht₀
  rw [List.mem_append, List.mem_cons, List.mem_singleton, List.mem_map] at ht₀
  rcases ht₀ with (rfl | rfl) | ⟨d, hd, rfl⟩
  · refine ⟨GoodMap.lift 1, ?_, ?_⟩
    · refine obl_of_split (R₀ := [strip H.comps[i]])
        (N₀ := [(.waved .s, liftA 1 x, newA 0), (.light .plus, newA 0, newA 0)]) hp ?_ ?_ ?_ ?_
      · simp only [List.map_append, strip_liftCs]
        exact List.perm_append_comm.trans (by simp [strip, mkC])
      · simp [strip, hik.1]
      · simp
      · rw [ftouch_nil (by simp [hsx]), ftouch_nil (by simp [strip, hcx, hcy])]
    · intro c hc
      show c.label.all _ = true
      rcases List.mem_append.1 hc with hc | hc
      · rw [hlr c hc]; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl
  · refine ⟨GoodMap.lift 1, ?_, ?_⟩
    · refine obl_of_split (R₀ := []) (K := H.comps.map strip)
        (N₀ := [(.waved .s, liftA 1 x, newA 0), (.light .plus, newA 0, newA 0)])
        (by simp) ?_ (by simp) (by simp) ?_
      · simp only [List.map_append, strip_liftCs]
        exact List.perm_append_comm.trans (by simp [strip, mkC])
      · rw [ftouch_nil (by simp [hsx])]; simp
    · intro c hc
      show c.label.all _ = true
      rcases List.mem_append.1 hc with hc | hc
      · rw [hlH c hc]; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl
  · obtain ⟨h1, h2⟩ := obl_dTerms (us := us) (H.comps.eraseIdx i)
      (Nice_sub hN fun p hp' => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp'
        exact List.mem_map_of_mem (List.mem_of_mem_eraseIdx hc))
      (p := newA 0) (q := liftA 1 x) rfl hsx hd
    refine ⟨GoodMap.lift 1, ?_, ?_⟩
    · obtain ⟨L₁, R, N, hq1, hq2, hR, hN', ht'⟩ := h1
      refine Obl_perm hp (by rw [List.map_append]; exact List.perm_append_comm)
        (Obl_repl [strip H.comps[i]] [(.waved .s, liftA 1 x, newA 0), (.G .plus, newA 0, liftA 1 x)]
          (by simp [strip, hik.1]) (by simp)
          (by rw [ftouch_nil (by simp [hsx]), ftouch_nil (by simp [strip, hcx, hcy])])
          ⟨L₁, R, N, hq1, by simpa [strip, mkC] using hq2, hR, hN', ht'⟩)
    · intro c hc
      show c.label.all _ = true
      rcases List.mem_append.1 hc with hc | hc
      · rw [labelsInt_of_lift (L := H.comps.eraseIdx i)
          (fun c hc => hl c (List.mem_of_mem_eraseIdx hc)) (h2 c hc)]; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl

private theorem map_conjT_conjT (L : List (KT n)) : (L.map conjT).map conjT = L := by
  rw [List.map_map]
  have : (conjT ∘ conjT : KT n → KT n) = id := funext conjT_conjT
  rw [this, List.map_id]

/-- A term of an operation on the complex conjugate graph, conjugated back. -/
private theorem goodT_conj {us : Fin 3 → Prop} {H : Graph 3 n} {t₁ : Tracked 3 n}
    (h : GoodT us (H.conj.comps.map strip) t₁) :
    GoodT us (H.comps.map strip) ⟨t₁.nOut, t₁.g.conj, t₁.f⟩ := by
  obtain ⟨hf, ho, hl⟩ := h
  refine ⟨hf, ?_, ?_⟩
  · have := Obl_conj ho
    rw [strip_conj, map_conjT_conjT] at this
    show Obl us t₁.f _ (t₁.g.conj.comps.map strip)
    rw [strip_conj]
    exact this
  · intro c hc
    simp only [Graph.conj, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact hl d hd

private theorem nice_conj_pCore {Γ : Graph 3 n} (h : Rep Γ) :
    Nice (usG Γ) (Γ.pCore.conj.comps.map strip) := by
  rw [strip_conj]; exact Nice_conj (nice_pCore h)

private theorem label_conj {H : Graph 3 n} (hl : ∀ c ∈ H.comps, c.label = none) :
    ∀ c ∈ H.conj.comps, c.label = none := by
  intro c hc
  simp only [Graph.conj, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  exact hl d hd

/-- [II, (4.23)] inside `P_x`. -/
private theorem rep_pWeight2 {Γ : Graph 3 n} {x : Atom 3 n} {t : Tracked 3 n} (h : Rep Γ)
    (hP : Γ.IsPFormAt x) (ht : t ∈ oWeightP2T x Γ) : Rep t.g := by
  have hx := label_int_of h hP.1
  unfold oWeightP2T at ht
  split at ht
  · rename_i E hE
    exact rep_pLift h hP (obl_wP2Pos hx (nice_pCore h) (label_pCore Γ) hE) ht
  · split at ht
    · rename_i E hE
      refine rep_pLift h hP (fun t₀ ht₀ => ?_) ht
      obtain ⟨t₁, ht₁, rfl⟩ := List.mem_map.1 ht₀
      exact goodT_conj
        (obl_wP2Pos hx (nice_conj_pCore h) (label_conj (label_pCore Γ)) hE t₁ ht₁)
    · rw [List.mem_singleton.1 ht]; exact h

end PSteps

/-- A rearrangement of appended lists, by counting. -/
local macro "perm_tac" : tactic => `(tactic| (
  rw [List.perm_iff_count]; intro a
  simp only [strip_mkC, List.count_append, List.count_cons, List.count_nil]; omega))

/-! ## Index lists -/

section Indices

variable {α : Type*}

private theorem perm_pick_erase (is : List ℕ) (L : List α) :
    L.Perm (pickIdxs is L ++ eraseIdxs is L) := by
  unfold pickIdxs eraseIdxs
  rw [← List.map_append]
  conv_lhs => rw [← List.zipIdx_map_fst 0 L]
  exact ((List.filter_append_perm _ _).map Prod.fst).symm

private theorem pick_split (is : List ℕ) (P : ℕ → Bool) (L : List α) :
    (pickIdxs is L).Perm (pickIdxs (is.filter P) L ++ pickIdxs (is.filter fun i => !P i) L) := by
  unfold pickIdxs
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  have h1 := List.filter_append_perm (fun p : α × ℕ => P p.2)
    (L.zipIdx.filter fun p => is.contains p.2)
  rw [List.filter_filter, List.filter_filter] at h1
  refine h1.symm.trans (List.Perm.of_eq ?_)
  congr 1 <;> apply List.filter_congr <;> intro p _ <;> simp [Bool.and_comm]

private theorem zipIdx_filter_single (L : List α) (k i : ℕ) (h1 : k ≤ i)
    (h2 : i < k + L.length) :
    ((L.zipIdx k).filter fun p => [i].contains p.2).map Prod.fst = [L[i - k]'(by omega)] := by
  induction L generalizing k with
  | nil => simp at h2; omega
  | cons a L ih =>
    rw [List.zipIdx_cons, List.filter_cons]
    by_cases hk : k = i
    · subst hk
      have : (L.zipIdx (k + 1)).filter (fun p => [k].contains p.2) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        have := List.le_snd_of_mem_zipIdx hp
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq]
        omega
      rw [show ([k].contains k) = true by simp]
      simp only [↓reduceIte, this, List.map_cons, List.map_nil, Nat.sub_self,
        List.getElem_cons_zero]
    · have hki : k + 1 ≤ i := by omega
      have hne : ([i].contains k) = false := by simp; omega
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih (k + 1) hki (by simp at h2; omega)]
      have e : i - k = (i - (k + 1)) + 1 := by omega
      simp only [List.cons.injEq, and_true]
      rw [List.getElem_cons]
      split_ifs with h0
      · omega
      · congr 1

private theorem pick_single {L : List α} {i : ℕ} (hi : i < L.length) :
    pickIdxs [i] L = [L[i]] := by
  unfold pickIdxs
  rw [zipIdx_filter_single L 0 i (Nat.zero_le _) (by omega)]
  simp only [Nat.sub_zero]

end Indices

/-! ## The multi-edge expansion inside `P_x` -/

section MultiE

variable {n : ℕ}

private theorem mem_edgeIdx {Γ : Graph 3 n} {x : Atom 3 n} {ch : Charge} {out : Bool} {j : ℕ}
    (h : j ∈ Γ.edgeIdx x ch out) :
    ∃ hj : j < Γ.comps.length, Γ.comps[j].kind = .G ch ∧
      (if out then Γ.comps[j].x = x ∧ Γ.comps[j].y ≠ x
        else Γ.comps[j].y = x ∧ Γ.comps[j].x ≠ x) := by
  unfold Graph.edgeIdx at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  obtain ⟨hpz, hpp⟩ := List.mem_filter.1 hp
  obtain ⟨hlt, hpe⟩ := List.mem_zipIdx' (x := p.1) (i := p.2) hpz
  refine ⟨hlt, ?_⟩
  rw [← hpe]
  simp only [Bool.and_eq_true, beq_iff_eq] at hpp
  refine ⟨hpp.1, ?_⟩
  cases out <;> simpa using hpp.2

/-- A list of components of a term with `n + 1` internal atoms, with the obligation of a step and
no label. -/
private def GoodCS (us : Fin 3 → Prop) (H : Graph 3 n) (cs : List (Comp (Atom 3 (n + 1)))) :
    Prop :=
  Obl us (liftA 1) (H.comps.map strip) (cs.map strip) ∧ ∀ c ∈ cs, c.label = none

/-- Components without dotted, ghost or `×`-dotted edge and without label. -/
private def Fresh {m : ℕ} (cs : List (Comp (Atom 3 m))) : Prop :=
  ∀ c ∈ cs, c.kind ≠ .dot ∧ c.kind ≠ .ghost ∧ c.kind ≠ .xdot ∧ c.label = none

private theorem goodCS_split {us : Fin 3 → Prop} {H : Graph 3 n}
    (hl : ∀ c ∈ H.comps, c.label = none)
    (K R₀ : List (Comp (Atom 3 n))) (N₀ : List (Comp (Atom 3 (n + 1))))
    (hp : (H.comps.map strip).Perm (R₀.map strip ++ K.map strip)) (hK : ∀ c ∈ K, c ∈ H.comps)
    (hR : ∀ c ∈ R₀, c.kind ≠ .dot) (hN : Fresh N₀)
    (ht : (((N₀.map strip).map (absT us)).filter touch).Perm
      (((R₀.map strip).map (absT us)).filter touch)) :
    GoodCS us H (liftCs 1 K ++ N₀) := by
  refine ⟨obl_of_split hp ?_ ?_ ?_ ht, ?_⟩
  · rw [List.map_append, strip_liftCs]; exact List.perm_append_comm
  · intro p hp'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp'
    exact hR c hc
  · intro p hp'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp'
    obtain ⟨a1, a2, a3, -⟩ := hN c hc
    exact ⟨a1, a2, fun h => absurd h a3⟩
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact labelsInt_of_lift (L := K) (fun c hc => hl c (hK c hc)) (Or.inl (List.mem_map.1 hc))
    · exact (hN c hc).2.2.2

private theorem goodCS_append {us : Fin 3 → Prop} {H : Graph 3 n}
    {cs : List (Comp (Atom 3 (n + 1)))} (h : GoodCS us H cs) (N₀ : List (Comp (Atom 3 (n + 1))))
    (hN : Fresh N₀) (hs : ∀ c ∈ N₀, side us c.x = none ∧ side us c.y = none) :
    GoodCS us H (cs ++ N₀) := by
  obtain ⟨ho, hl⟩ := h
  refine ⟨?_, ?_⟩
  · have := Obl_repl (us := us) [] (N₀.map strip) (by simp) (fun p hp => ?_) ?_ ho
    · rw [List.map_append]
      exact Obl_perm (List.Perm.refl _) List.perm_append_comm (by simpa using this)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
      obtain ⟨a1, a2, a3, -⟩ := hN c hc
      exact ⟨a1, a2, fun h => absurd h a3⟩
    · rw [ftouch_nil (fun p hp => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp; exact hs c hc)]
      simp
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hl c hc
    · exact (hN c hc).2.2.2

private theorem goodT_of_goodCS {us : Fin 3 → Prop} {H : Graph 3 n}
    {cs : List (Comp (Atom 3 (n + 1)))} (h : GoodCS us H cs) (co : Coeff) :
    GoodT us (H.comps.map strip) ⟨n + 1, ⟨cs, co⟩, liftA 1⟩ :=
  ⟨GoodMap.lift 1, h.1, fun c hc => by show c.label.all _ = true; rw [h.2 c hc]; rfl⟩

private theorem strip_labelQs {m : ℕ} (u : Atom 3 m) (cs : List (Comp (Atom 3 m))) :
    (labelQs u cs).map strip = cs.map strip := by
  unfold labelQs
  rw [List.map_map]
  exact List.map_congr_left fun c _ => by
    simp only [Function.comp_apply, Comp.labelQ]; split_ifs <;> rfl

private theorem labelQs_int {m : ℕ} {u : Atom 3 m} (hu : u.isRight = true)
    {cs : List (Comp (Atom 3 m))} (hl : ∀ c ∈ cs, c.label.all (fun ℓ => ℓ.2.isRight) = true) :
    ∀ c ∈ labelQs u cs, c.label.all (fun ℓ => ℓ.2.isRight) = true := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  unfold Comp.labelQ
  split_ifs
  · simpa using hu
  · exact hl d hd

private theorem goodT_of_goodCS_Q {us : Fin 3 → Prop} {H : Graph 3 n} {x : Atom 3 n}
    (hx : x.isRight = true) {cs : List (Comp (Atom 3 (n + 1)))} (h : GoodCS us H cs)
    (co : Coeff) :
    GoodT us (H.comps.map strip) ⟨n + 1, ⟨labelQs (liftA 1 x) cs, co⟩, liftA 1⟩ := by
  refine ⟨GoodMap.lift 1, ?_, ?_⟩
  · show Obl _ _ _ ((labelQs (liftA 1 x) cs).map strip)
    rw [strip_labelQs]; exact h.1
  · refine labelQs_int ?_ fun c hc => by rw [h.2 c hc]; rfl
    rcases x with a | b
    · simp at hx
    · rfl

private theorem goodT_labelQs_id {us : Fin 3 → Prop} {H : Graph 3 n} {x : Atom 3 n}
    (hx : x.isRight = true) (hl : ∀ c ∈ H.comps, c.label = none) (co : Coeff) :
    GoodT us (H.comps.map strip) ⟨n, ⟨labelQs x H.comps, co⟩, id⟩ := by
  refine ⟨GoodMap.id, ?_, ?_⟩
  · show Obl _ _ _ ((labelQs x H.comps).map strip)
    rw [strip_labelQs]
    have := Obl_refl us id (H.comps.map strip)
    rwa [map_mapT_id] at this
  · exact labelQs_int hx fun c hc => by rw [hl c hc]; rfl

private theorem getD_of_lt {α : Type*} {L : List α} {j : ℕ} (h : j < L.length) (d : α) :
    L.getD j d = L[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

private theorem mem_of_mem_eraseIdxs {α : Type*} {is : List ℕ} {L : List α} {c : α}
    (h : c ∈ eraseIdxs is L) : c ∈ L :=
  (perm_pick_erase is L).mem_iff.2 (List.mem_append_right _ h)

private theorem mem_of_mem_pickIdxs {α : Type*} {is : List ℕ} {L : List α} {c : α}
    (h : c ∈ pickIdxs is L) : c ∈ L :=
  (perm_pick_erase is L).mem_iff.2 (List.mem_append_left _ h)

private theorem pick_congr {α : Type*} {is js : List ℕ} (L : List α) (h : ∀ i, i ∈ is ↔ i ∈ js) :
    pickIdxs is L = pickIdxs js L := by
  unfold pickIdxs
  congr 1
  exact List.filter_congr fun p _ => by simp [h]

/-- Two components removed at distinct indices. -/
private theorem perm_two {α : Type*} {L : List α} {i j : ℕ} (hij : i ≠ j) (hi : i < L.length)
    (hj : j < L.length) : L.Perm ([L[i], L[j]] ++ eraseIdxs [i, j] L) := by
  refine (perm_pick_erase [i, j] L).trans (List.Perm.append_right _ ?_)
  refine (pick_split [i, j] (· == i) L).trans ?_
  have e1 : [i, j].filter (· == i) = [i] := by simp [List.filter_cons, Ne.symm hij]
  have e2 : [i, j].filter (fun k => !(k == i)) = [j] := by simp [List.filter_cons, Ne.symm hij]
  rw [e1, e2, pick_single hi, pick_single hj]
  rfl

/-- The multi-edge expansion [I, (3.13)] at an atom with an edge of charge `plus` leaving it. -/
private theorem goodT_multiEOut {us : Fin 3 → Prop} {x : Atom 3 n} (hx : x.isRight = true)
    {H : Graph 3 n} (hN : Nice us (H.comps.map strip)) (hl : ∀ c ∈ H.comps, c.label = none)
    {E : TExpansion 3 n} (hE : multiEOut x H = some E) :
    ∀ t₀ ∈ E, GoodT us (H.comps.map strip) t₀ := by
  unfold multiEOut at hE
  split at hE
  · cases hE
  rename_i i₁ is₂ hi
  split at hE
  · cases hE
  rename_i e₁ he₁
  dsimp only at hE
  split at hE
  · cases hE
  obtain rfl := Option.some.inj hE
  have hsx : side us x = none := side_right hx
  have hsx1 : side us (liftA 1 x : Atom 3 (n + 1)) = none := by rw [side_liftA]; exact hsx
  have hi₁ : i₁ ∈ H.edgeIdx x .plus true := by rw [hi]; exact List.mem_cons_self ..
  obtain ⟨hi₁l, he₁k, he₁x⟩ := mem_edgeIdx hi₁
  simp only [↓reduceIte] at he₁x
  have he₁e : H.comps[i₁] = e₁ := by
    obtain ⟨h', e⟩ := List.getElem?_eq_some_iff.1 he₁; exact e
  rw [he₁e] at he₁k he₁x
  have he₁m : e₁ ∈ H.comps := List.mem_of_getElem? he₁
  set y₁ : Atom 3 (n + 1) := liftA 1 e₁.y
  have hsy₁ : side us y₁ = side us e₁.y := side_liftA 1 _
  -- the solid edges at `x`
  have hM : ∀ j ∈ H.edgeIdx x .minus true, ∃ hj : j < H.comps.length,
      H.comps[j].kind = .G .minus ∧ H.comps[j].x = x ∧ j ≠ i₁ := by
    intro j hj
    obtain ⟨hjl, hjk, hjx⟩ := mem_edgeIdx hj
    simp only [↓reduceIte] at hjx
    refine ⟨hjl, hjk, hjx.1, fun e => ?_⟩
    subst e
    rw [he₁e, he₁k] at hjk
    cases hjk
  have hPl : ∀ j ∈ H.edgeIdx x .plus false, ∃ hj : j < H.comps.length,
      H.comps[j].kind = .G .plus ∧ H.comps[j].y = x ∧ side us H.comps[j].x = none ∧ j ≠ i₁ := by
    intro j hj
    obtain ⟨hjl, hjk, hjx⟩ := mem_edgeIdx hj
    simp only [Bool.false_eq_true, ↓reduceIte] at hjx
    refine ⟨hjl, hjk, hjx.1,
      (hN _ (List.mem_map_of_mem (List.getElem_mem hjl)) (by simp [strip, hjk, Kind.isRandom])).1,
      fun e => ?_⟩
    subst e
    rw [he₁e] at hjx
    exact hjx.2 he₁x.1
  have hfr : ∀ (κ : Kind) (u v : Atom 3 (n + 1)), κ ≠ .dot → κ ≠ .ghost → κ ≠ .xdot →
      Fresh [mkC κ u v] := by
    intro κ u v h1 h2 h3 c hc
    rw [List.mem_singleton] at hc; subst hc
    exact ⟨h1, h2, h3, rfl⟩
  have hfr3 : ∀ (κ₁ κ₂ κ₃ : Kind) (u₁ v₁ u₂ v₂ u₃ v₃ : Atom 3 (n + 1)),
      κ₁ ≠ .dot ∧ κ₁ ≠ .ghost ∧ κ₁ ≠ .xdot → κ₂ ≠ .dot ∧ κ₂ ≠ .ghost ∧ κ₂ ≠ .xdot →
      κ₃ ≠ .dot ∧ κ₃ ≠ .ghost ∧ κ₃ ≠ .xdot →
      Fresh [mkC κ₁ u₁ v₁, mkC κ₂ u₂ v₂, mkC κ₃ u₃ v₃] := by
    intro κ₁ κ₂ κ₃ u₁ v₁ u₂ v₂ u₃ v₃ h1 h2 h3 c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨h1.1, h1.2.1, h1.2.2, rfl⟩
    · exact ⟨h2.1, h2.2.1, h2.2.2, rfl⟩
    · exact ⟨h3.1, h3.2.1, h3.2.2, rfl⟩
  have hGK : ∀ ch : Charge, (Kind.G ch) ≠ .dot ∧ (Kind.G ch) ≠ .ghost ∧ (Kind.G ch) ≠ .xdot :=
    fun ch => ⟨by simp, by simp, by simp⟩
  have hWK : (Kind.waved .s) ≠ .dot ∧ (Kind.waved .s) ≠ .ghost ∧ (Kind.waved .s) ≠ .xdot :=
    ⟨by simp, by simp, by simp⟩
  -- the main terms
  have gM : ∀ j ∈ H.edgeIdx x .minus true, GoodCS us H
      (liftCs 1 (eraseIdxs [i₁, j] H.comps) ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) y₁,
        mkC (.G .minus) (newA 0) (liftA 1 ((H.comps.getD j e₁).y))]) := by
    intro j hj
    obtain ⟨hjl, hjk, hjx, hne⟩ := hM j hj
    rw [getD_of_lt hjl]
    refine goodCS_split hl _ [H.comps[i₁], H.comps[j]] _ ?_ (fun c hc => mem_of_mem_eraseIdxs hc)
      ?_ (hfr3 _ _ _ _ _ _ _ _ _ hWK (hGK _) (hGK _)) ?_
    · rw [← List.map_append]; exact (perm_two (Ne.symm hne) hi₁l hjl).map strip
    · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [he₁e, he₁k]; simp
      · rw [hjk]; simp
    · simp [strip, mkC, absT, touch, side_liftA, hsx, he₁e, he₁k, he₁x.1, hjk, hjx, y₁,
        List.filter_cons]
  have gP : ∀ j ∈ H.edgeIdx x .plus false, GoodCS us H
      (liftCs 1 (eraseIdxs [i₁, j] H.comps) ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) y₁,
        mkC (.G .plus) (liftA 1 ((H.comps.getD j e₁).x)) (newA 0)]) := by
    intro j hj
    obtain ⟨hjl, hjk, hjy, hjs, hne⟩ := hPl j hj
    rw [getD_of_lt hjl]
    refine goodCS_split hl _ [H.comps[i₁], H.comps[j]] _ ?_ (fun c hc => mem_of_mem_eraseIdxs hc)
      ?_ (hfr3 _ _ _ _ _ _ _ _ _ hWK (hGK _) (hGK _)) ?_
    · rw [← List.map_append]; exact (perm_two (Ne.symm hne) hi₁l hjl).map strip
    · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [he₁e, he₁k]; simp
      · rw [hjk]; simp
    · simp [strip, mkC, absT, touch, side_liftA, hsx, he₁e, he₁k, he₁x.1, hjk, hjy, hjs, y₁,
        List.filter_cons]
  have hperm1 : (H.comps.map strip).Perm ([H.comps[i₁]].map strip ++
      (H.comps.eraseIdx i₁).map strip) := by
    rw [← List.map_append]; exact (List.getElem_cons_eraseIdx_perm hi₁l).symm.map strip
  have g1 : ∀ κ : Kind, κ ≠ .dot ∧ κ ≠ .ghost ∧ κ ≠ .xdot → ∀ u v : Atom 3 (n + 1),
      side us u = none → side us v = none → GoodCS us H (liftCs 1 (H.comps.eraseIdx i₁) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), mkC κ u v, mkC (.G .plus) (newA 0) y₁]) := by
    intro κ hκ u v hu hv
    refine goodCS_split hl _ [H.comps[i₁]] _ hperm1 (fun c hc => List.mem_of_mem_eraseIdx hc)
      ?_ (hfr3 _ _ _ _ _ _ _ _ _ hWK hκ (hGK _)) ?_
    · intro c hc; rw [List.mem_singleton] at hc; subst hc; rw [he₁e, he₁k]; simp
    · simp [strip, mkC, absT, touch, side_liftA, hsx, he₁e, he₁k, he₁x.1, hu, hv, y₁,
        List.filter_cons]
  have gL : GoodCS us H (liftCs 1 H.comps ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) := by
    refine goodCS_split hl H.comps [] _ (by simp) (fun c hc => hc) (by simp) ?_ ?_
    · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact ⟨by simp [mkC], by simp [mkC], by simp [mkC], rfl⟩
    · rw [ftouch_nil (by simp [strip, mkC, hsx1])]; simp
  -- the derivative terms
  set xIdx := H.edgeIdx x .plus true ++ H.edgeIdx x .minus true ++ H.edgeIdx x .plus false ++
    H.edgeIdx x .minus false
  have hi₁x : i₁ ∈ xIdx := by simp [xIdx, hi₁]
  have gD : ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs xIdx H.comps)),
      GoodCS us H (liftCs 1 (pickIdxs (xIdx.filter (· != i₁)) H.comps) ++ d ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) y₁]) := by
    intro d hd
    have hNe : Nice us ((eraseIdxs xIdx H.comps).map strip) := Nice_sub hN fun p hp => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
      exact List.mem_map_of_mem (mem_of_mem_eraseIdxs hc)
    obtain ⟨h1, h2⟩ := obl_dTerms (eraseIdxs xIdx H.comps) hNe (p := newA 0) (q := liftA 1 x)
      rfl hsx1 hd
    set P := pickIdxs (xIdx.filter (· != i₁)) H.comps
    have hpc : ∀ k, k ∈ xIdx.filter (fun i => !(i != i₁)) ↔ k ∈ [i₁] := by
      intro k
      by_cases hk : k = i₁
      · subst hk; simp [hi₁x]
      · simp [hk]
    have hp : (H.comps.map strip).Perm ([strip H.comps[i₁]] ++
        ((eraseIdxs xIdx H.comps).map strip ++ P.map strip)) := by
      have e1 := perm_pick_erase xIdx H.comps
      have e2 := pick_split xIdx (· != i₁) H.comps
      rw [pick_congr H.comps hpc, pick_single hi₁l] at e2
      have := (e1.trans (e2.append_right _)).map strip
      refine this.trans ?_
      simp only [P, List.map_append, List.map_cons, List.map_nil]
      perm_tac
    refine ⟨?_, ?_⟩
    · have ha := Obl_append h1 (P.map strip)
      have hr := Obl_repl (us := us) (f := liftA 1) [strip H.comps[i₁]]
        [(.waved .s, liftA 1 x, newA 0), (.G .plus, newA 0, y₁)]
        (by simp [strip, he₁e, he₁k]) (by simp)
        (by simp [strip, absT, touch, side_liftA, hsx, he₁e, he₁k, he₁x.1, y₁,
          List.filter_cons]) ha
      refine Obl_perm hp ?_ hr
      simp only [List.map_append, List.map_cons, List.map_nil, strip_liftCs]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (hc | hc) | rfl | rfl
      · exact labelsInt_of_lift (L := P) (fun c hc => hl c (mem_of_mem_pickIdxs hc))
          (Or.inl (List.mem_map.1 hc))
      · exact labelsInt_of_lift (L := eraseIdxs xIdx H.comps)
          (fun c hc => hl c (mem_of_mem_eraseIdxs hc)) (h2 c hc)
      · rfl
      · rfl
  have hlx : ∀ (ch : Charge) (κ : Kind) {cs : List (Comp (Atom 3 (n + 1)))}, GoodCS us H cs →
      κ ≠ .dot ∧ κ ≠ .ghost ∧ κ ≠ .xdot →
      GoodCS us H (cs ++ [mkC κ (liftA 1 x) (liftA 1 x)]) := fun _ κ cs h hκ =>
    goodCS_append h _ (hfr _ _ _ hκ.1 hκ.2.1 hκ.2.2) (by simp [mkC, hsx1])
  have hLK : ∀ ch : Charge, (Kind.light ch) ≠ .dot ∧ (Kind.light ch) ≠ .ghost ∧
      (Kind.light ch) ≠ .xdot := fun ch => ⟨by simp, by simp, by simp⟩
  have hWt : ∀ ch : Charge, (Kind.weight ch) ≠ .dot ∧ (Kind.weight ch) ≠ .ghost ∧
      (Kind.weight ch) ≠ .xdot := fun ch => ⟨by simp, by simp, by simp⟩
  intro t₀ ht₀
  simp only [List.mem_append, List.mem_map, List.mem_singleton, List.mem_ite_nil_left,
    or_assoc] at ht₀
  rcases ht₀ with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨_, ⟨d, hd, rfl⟩, rfl⟩ | rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨_, ⟨d, hd, rfl⟩, rfl⟩
  · exact goodT_of_goodCS (gM j hj) _
  · exact goodT_of_goodCS (gP j hj) _
  · exact goodT_of_goodCS (hlx .minus _ (gM j hj) (hLK _)) _
  · exact goodT_of_goodCS (hlx .plus _ (gP j hj) (hLK _)) _
  · exact goodT_of_goodCS gL _
  · exact goodT_of_goodCS (g1 _ (hGK _) _ _ hsx1 rfl) _
  · exact goodT_of_goodCS (g1 _ (hGK _) _ _ rfl hsx1) _
  · exact goodT_of_goodCS (gD d hd) _
  · exact goodT_labelQs_id hx hl _
  · exact goodT_of_goodCS_Q hx (hlx .minus _ (gM j hj) (hWt _)) _
  · exact goodT_of_goodCS_Q hx (hlx .plus _ (gP j hj) (hWt _)) _
  · exact goodT_of_goodCS_Q hx gL _
  · exact goodT_of_goodCS_Q hx (g1 _ (hGK _) _ _ hsx1 rfl) _
  · exact goodT_of_goodCS_Q hx (g1 _ (hGK _) _ _ rfl hsx1) _
  · exact goodT_of_goodCS_Q hx (gD d hd) _

/-- The multi-edge expansion [I, (3.14)] at an atom with an edge of charge `plus` entering it. -/
private theorem goodT_multiEIn {us : Fin 3 → Prop} {x : Atom 3 n} (hx : x.isRight = true)
    {H : Graph 3 n} (hN : Nice us (H.comps.map strip)) (hl : ∀ c ∈ H.comps, c.label = none)
    {E : TExpansion 3 n} (hE : multiEIn x H = some E) :
    ∀ t₀ ∈ E, GoodT us (H.comps.map strip) t₀ := by
  unfold multiEIn at hE
  split at hE
  · cases hE
  rename_i i₁ is₂ hi
  split at hE
  · cases hE
  rename_i e₁ he₁
  dsimp only at hE
  split at hE
  · cases hE
  obtain rfl := Option.some.inj hE
  have hsx : side us x = none := side_right hx
  have hsx1 : side us (liftA 1 x : Atom 3 (n + 1)) = none := by rw [side_liftA]; exact hsx
  have hi₁ : i₁ ∈ H.edgeIdx x .plus false := by rw [hi]; exact List.mem_cons_self ..
  obtain ⟨hi₁l, he₁k, he₁x⟩ := mem_edgeIdx hi₁
  simp only [Bool.false_eq_true, ↓reduceIte] at he₁x
  have he₁e : H.comps[i₁] = e₁ := by
    obtain ⟨h', e⟩ := List.getElem?_eq_some_iff.1 he₁; exact e
  rw [he₁e] at he₁k he₁x
  have he₁m : e₁ ∈ H.comps := List.mem_of_getElem? he₁
  have hsw : side us e₁.x = none :=
    (hN _ (List.mem_map_of_mem he₁m) (by simp [strip, he₁k, Kind.isRandom])).1
  set w₁ : Atom 3 (n + 1) := liftA 1 e₁.x
  have hsw₁ : side us w₁ = none := by simp only [w₁]; rw [side_liftA]; exact hsw
  -- the solid edges entering `x`
  have hM : ∀ j ∈ H.edgeIdx x .minus false, ∃ hj : j < H.comps.length,
      H.comps[j].kind = .G .minus ∧ H.comps[j].y = x ∧ side us H.comps[j].x = none ∧ j ≠ i₁ := by
    intro j hj
    obtain ⟨hjl, hjk, hjx⟩ := mem_edgeIdx hj
    simp only [Bool.false_eq_true, ↓reduceIte] at hjx
    refine ⟨hjl, hjk, hjx.1,
      (hN _ (List.mem_map_of_mem (List.getElem_mem hjl)) (by simp [strip, hjk, Kind.isRandom])).1,
      fun e => ?_⟩
    subst e
    rw [he₁e, he₁k] at hjk
    cases hjk
  have hfr3 : ∀ (κ₁ κ₂ κ₃ : Kind) (u₁ v₁ u₂ v₂ u₃ v₃ : Atom 3 (n + 1)),
      κ₁ ≠ .dot ∧ κ₁ ≠ .ghost ∧ κ₁ ≠ .xdot → κ₂ ≠ .dot ∧ κ₂ ≠ .ghost ∧ κ₂ ≠ .xdot →
      κ₃ ≠ .dot ∧ κ₃ ≠ .ghost ∧ κ₃ ≠ .xdot →
      Fresh [mkC κ₁ u₁ v₁, mkC κ₂ u₂ v₂, mkC κ₃ u₃ v₃] := by
    intro κ₁ κ₂ κ₃ u₁ v₁ u₂ v₂ u₃ v₃ h1 h2 h3 c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨h1.1, h1.2.1, h1.2.2, rfl⟩
    · exact ⟨h2.1, h2.2.1, h2.2.2, rfl⟩
    · exact ⟨h3.1, h3.2.1, h3.2.2, rfl⟩
  have hGK : ∀ ch : Charge, (Kind.G ch) ≠ .dot ∧ (Kind.G ch) ≠ .ghost ∧ (Kind.G ch) ≠ .xdot :=
    fun ch => ⟨by simp, by simp, by simp⟩
  have hWK : (Kind.waved .s) ≠ .dot ∧ (Kind.waved .s) ≠ .ghost ∧ (Kind.waved .s) ≠ .xdot :=
    ⟨by simp, by simp, by simp⟩
  -- the main terms
  have gM : ∀ j ∈ H.edgeIdx x .minus false, GoodCS us H
      (liftCs 1 (eraseIdxs [i₁, j] H.comps) ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) w₁ (newA 0),
        mkC (.G .minus) (liftA 1 ((H.comps.getD j e₁).x)) (newA 0)]) := by
    intro j hj
    obtain ⟨hjl, hjk, hjy, hjs, hne⟩ := hM j hj
    rw [getD_of_lt hjl]
    refine goodCS_split hl _ [H.comps[i₁], H.comps[j]] _ ?_ (fun c hc => mem_of_mem_eraseIdxs hc)
      ?_ (hfr3 _ _ _ _ _ _ _ _ _ hWK (hGK _) (hGK _)) ?_
    · rw [← List.map_append]; exact (perm_two (Ne.symm hne) hi₁l hjl).map strip
    · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [he₁e, he₁k]; simp
      · rw [hjk]; simp
    · simp [strip, mkC, absT, touch, side_liftA, hsx, he₁e, he₁k, he₁x.1, hsw, hsw₁, hjk, hjy,
        hjs, List.filter_cons]
  have hperm1 : (H.comps.map strip).Perm ([H.comps[i₁]].map strip ++
      (H.comps.eraseIdx i₁).map strip) := by
    rw [← List.map_append]; exact (List.getElem_cons_eraseIdx_perm hi₁l).symm.map strip
  have g1 : GoodCS us H (liftCs 1 (H.comps.eraseIdx i₁) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) w₁ (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 x)]) := by
    refine goodCS_split hl _ [H.comps[i₁]] _ hperm1 (fun c hc => List.mem_of_mem_eraseIdx hc)
      ?_ (hfr3 _ _ _ _ _ _ _ _ _ hWK (hGK _) (hGK _)) ?_
    · intro c hc; rw [List.mem_singleton] at hc; subst hc; rw [he₁e, he₁k]; simp
    · simp [strip, mkC, absT, touch, side_liftA, hsx, he₁e, he₁k, he₁x.1, hsw, hsw₁,
        List.filter_cons]
  have gL : GoodCS us H (liftCs 1 H.comps ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) := by
    refine goodCS_split hl H.comps [] _ (by simp) (fun c hc => hc) (by simp) ?_ ?_
    · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact ⟨by simp [mkC], by simp [mkC], by simp [mkC], rfl⟩
    · rw [ftouch_nil (by simp [strip, mkC, hsx1])]; simp
  -- the derivative terms
  set xIdx := H.edgeIdx x .plus false ++ H.edgeIdx x .minus false
  have hi₁x : i₁ ∈ xIdx := by simp [xIdx, hi₁]
  have gD : ∀ d ∈ dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs xIdx H.comps)),
      GoodCS us H (liftCs 1 (pickIdxs (xIdx.filter (· != i₁)) H.comps) ++ d ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) w₁ (newA 0)]) := by
    intro d hd
    have hNe : Nice us ((eraseIdxs xIdx H.comps).map strip) := Nice_sub hN fun p hp => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
      exact List.mem_map_of_mem (mem_of_mem_eraseIdxs hc)
    obtain ⟨h1, h2⟩ := obl_dTerms (eraseIdxs xIdx H.comps) hNe (p := liftA 1 x) (q := newA 0)
      hsx1 rfl hd
    set P := pickIdxs (xIdx.filter (· != i₁)) H.comps
    have hpc : ∀ k, k ∈ xIdx.filter (fun i => !(i != i₁)) ↔ k ∈ [i₁] := by
      intro k
      by_cases hk : k = i₁
      · subst hk; simp [hi₁x]
      · simp [hk]
    have hp : (H.comps.map strip).Perm ([strip H.comps[i₁]] ++
        ((eraseIdxs xIdx H.comps).map strip ++ P.map strip)) := by
      have e1 := perm_pick_erase xIdx H.comps
      have e2 := pick_split xIdx (· != i₁) H.comps
      rw [pick_congr H.comps hpc, pick_single hi₁l] at e2
      have := (e1.trans (e2.append_right _)).map strip
      refine this.trans ?_
      simp only [P, List.map_append, List.map_cons, List.map_nil]
      perm_tac
    refine ⟨?_, ?_⟩
    · have ha := Obl_append h1 (P.map strip)
      have hr := Obl_repl (us := us) (f := liftA 1) [strip H.comps[i₁]]
        [(.waved .s, liftA 1 x, newA 0), (.G .plus, w₁, newA 0)]
        (by simp [strip, he₁e, he₁k]) (by simp)
        (by simp [strip, absT, touch, side_liftA, hsx, he₁e, he₁k, he₁x.1, hsw, hsw₁,
          List.filter_cons]) ha
      refine Obl_perm hp ?_ hr
      simp only [List.map_append, List.map_cons, List.map_nil, strip_liftCs]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (hc | hc) | rfl | rfl
      · exact labelsInt_of_lift (L := P) (fun c hc => hl c (mem_of_mem_pickIdxs hc))
          (Or.inl (List.mem_map.1 hc))
      · exact labelsInt_of_lift (L := eraseIdxs xIdx H.comps)
          (fun c hc => hl c (mem_of_mem_eraseIdxs hc)) (h2 c hc)
      · rfl
      · rfl
  have hlx : ∀ (ch : Charge) (κ : Kind) {cs : List (Comp (Atom 3 (n + 1)))}, GoodCS us H cs →
      κ ≠ .dot ∧ κ ≠ .ghost ∧ κ ≠ .xdot →
      GoodCS us H (cs ++ [mkC κ (liftA 1 x) (liftA 1 x)]) := fun _ κ cs h hκ =>
    goodCS_append h _ (fun c hc => by
      rw [List.mem_singleton] at hc; subst hc; exact ⟨hκ.1, hκ.2.1, hκ.2.2, rfl⟩)
      (by simp [mkC, hsx1])
  have hLK : ∀ ch : Charge, (Kind.light ch) ≠ .dot ∧ (Kind.light ch) ≠ .ghost ∧
      (Kind.light ch) ≠ .xdot := fun ch => ⟨by simp, by simp, by simp⟩
  have hWt : ∀ ch : Charge, (Kind.weight ch) ≠ .dot ∧ (Kind.weight ch) ≠ .ghost ∧
      (Kind.weight ch) ≠ .xdot := fun ch => ⟨by simp, by simp, by simp⟩
  intro t₀ ht₀
  simp only [List.mem_append, List.mem_map, List.mem_singleton, List.mem_ite_nil_left,
    or_assoc] at ht₀
  rcases ht₀ with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ | ⟨_, ⟨d, hd, rfl⟩, rfl⟩ | rfl |
    ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ | ⟨_, ⟨d, hd, rfl⟩, rfl⟩
  · exact goodT_of_goodCS (gM j hj) _
  · exact goodT_of_goodCS (hlx .minus _ (gM j hj) (hLK _)) _
  · exact goodT_of_goodCS gL _
  · exact goodT_of_goodCS g1 _
  · exact goodT_of_goodCS (gD d hd) _
  · exact goodT_labelQs_id hx hl _
  · exact goodT_of_goodCS_Q hx (hlx .minus _ (gM j hj) (hWt _)) _
  · exact goodT_of_goodCS_Q hx gL _
  · exact goodT_of_goodCS_Q hx g1 _
  · exact goodT_of_goodCS_Q hx (gD d hd) _

/-- [II, (4.24)] inside `P_x`: the multi-edge expansion of [I, Def 3.11] in its four cases. -/
private theorem rep_pMultiE {Γ : Graph 3 n} {x : Atom 3 n} {E : TExpansion 3 n} {t : Tracked 3 n}
    (h : Rep Γ) (hP : Γ.IsPFormAt x) (hE : multiEHat x Γ.pCore = some E)
    (ht : t ∈ pLiftT x Γ E) : Rep t.g := by
  have hx := label_int_of h hP.1
  refine rep_pLift h hP ?_ ht
  have hc : ∀ {E₁ : TExpansion 3 n},
      (∀ t₁ ∈ E₁, GoodT (usG Γ) (Γ.pCore.conj.comps.map strip) t₁) →
      ∀ t₀ ∈ E₁.conj, GoodT (usG Γ) (Γ.pCore.comps.map strip) t₀ := by
    intro E₁ h₁ t₀ ht₀
    obtain ⟨t₁, ht₁, rfl⟩ := List.mem_map.1 ht₀
    exact goodT_conj (h₁ t₁ ht₁)
  unfold multiEHat at hE
  split_ifs at hE
  · exact goodT_multiEOut hx (nice_pCore h) (label_pCore Γ) hE
  · obtain ⟨E₁, hE₁, rfl⟩ := Option.map_eq_some_iff.1 hE
    exact hc (goodT_multiEOut hx (nice_conj_pCore h) (label_conj (label_pCore Γ)) hE₁)
  · exact goodT_multiEIn hx (nice_pCore h) (label_pCore Γ) hE
  · obtain ⟨E₁, hE₁, rfl⟩ := Option.map_eq_some_iff.1 hE
    exact hc (goodT_multiEIn hx (nice_conj_pCore h) (label_conj (label_pCore Γ)) hE₁)

end MultiE

/-! ## The clauses along one elementary step -/

/-- Every elementary step of the `Q`-expansions keeps the charge pattern of the block normal form,
the clause on the external atoms, the absence of ghost edges and internal label atoms, on graphs
with the invariant `Graph.InvB'`. -/
theorem qElemStep_clauses :
  ∀ g g' : Σ n, Graph 3 n, QElemStep g g' → g.2.InvB' →
    g'.2.ColourInvB ∧ g'.2.ExtClause ∧ g'.2.NoGhost ∧ g'.2.LabelsInt := by
  intro g g' hs hI
  have h : Rep g.2 := (clauses_rep g.2).1 hI.2
  refine (clauses_rep g'.2).2 ?_
  induction hs with
  | schur x i Γ t hx ht => exact rep_schur hx h ht
  | schurRev x i Γ t hx ht => exact rep_schurRev hx h ht
  | schurW x i Γ t hx ht => exact rep_schurW hx h ht
  | schurWRev x i Γ t hx ht => exact rep_schurWRev hx h ht
  | taylor D i Γ t ht => exact rep_taylor h ht
  | weight1 x Γ t ht => exact rep_weight1 h ht
  | dot Γ t ht => exact rep_dot h ht
  | merge Γ t ht => exact rep_of_merge h ht
  | split u v Γ t hv ht => exact rep_split hv h ht
  | xdot i Γ t ht => exact rep_xdot h ht
  | dropDot i Γ c hc hk hb => exact rep_dropDot hc hk hb h
  | rebase i Γ c u v hc hk hb => exact rep_rebase hc hk hb h
  | qToP u Γ t hQ ht => exact rep_qToP h hQ ht
  | absorb ℓ Γ hℓ hl => exact rep_absorb h hℓ
  | dropP u Γ hP hm => exact rep_dropLabels h
  | pWeight1 x Γ t hP hp ht => exact rep_pWeight1 h hP ht
  | pWeight2 x Γ t hP hp ht => exact rep_pWeight2 h hP ht
  | pMultiE x Γ E t hP hp hE ht => exact rep_pMultiE h hP hE ht

/-! ## Decidability instances for concrete graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance Cls_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

section Helpers

variable {V E : Type}

end Helpers

end Instances
end RBM8D.Graphs
