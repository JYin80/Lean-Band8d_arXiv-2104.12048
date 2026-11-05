import RBM8D.Graph.QExp.Defs
import RBM8D.Graph.Standard
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# The block reading of the dotted edges at `⊗`, `⊕`, `⊖`

The block normal form of [II, §4.4] (after (4.17)) and the molecular graph of [II, Def 2.11] in the
block reading: sequentially pre-deterministic and globally standard graphs
([II, Defs 5.9, 6.2]) in this reading; the charge pattern of the expansions of `T_{a,b₁b₂}`, the
clause on the external atoms and the invariant of [II, Lemma 5.13]; [II, Def 6.3 (3)] in this
reading.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Decidability of blocks and molecules -/

private instance Graph.instDecAdjDotG {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

private instance Graph.instDecSameBlockG {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameBlock :=
  fun u v => @SimpleGraph.instDecidableRelReachable _ _ _ _ (Graph.instDecAdjDotG Γ) u v

private instance Graph.instDecAdjMolG {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.molGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = v ∧ c.y = u))))

private instance Graph.instDecSameMolG {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameMol :=
  fun u v =>
    haveI : Decidable (Γ.molGraph.Reachable u v) :=
      @SimpleGraph.instDecidableRelReachable _ _ _ _ (Graph.instDecAdjMolG Γ) u v
    inferInstanceAs (Decidable (u = v ∨
      (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)))

/-! ## The block normal form and the molecular graph `toMG'` -/

/-- The least internal atom in the block of `u` (`none` if the block of `u` has no internal
atom). -/
def Graph.anchor {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Option (Fin n) :=
  (List.finRange n).find? fun b => decide (Γ.SameBlock u (.inr b))

/-- The external atom `u` is not identified with an internal atom: it is external and its block
has no internal atom. -/
def Graph.Unpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop :=
  u.isLeft = true ∧ ∀ b : Fin n, ¬ Γ.SameBlock u (.inr b)

/-- The atom of the block normal form at the atom `u`: the least internal atom of the block of
`u` if `u` is external and its block has an internal atom, otherwise `u`. -/
def Graph.flatAtom {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Atom k n :=
  match u with
  | .inl _ =>
    match Γ.anchor u with
    | some b => .inr b
    | none => u
  | .inr _ => u

/-- A component in the block normal form: a dotted edge is kept; for every other component, each
end at an external atom whose block has an internal atom is moved to the least internal atom of
that block. -/
def Graph.flatComp {k n : ℕ} (Γ : Graph k n) (c : Comp (Atom k n)) : Comp (Atom k n) :=
  if c.kind = .dot then c else { c with x := Γ.flatAtom c.x, y := Γ.flatAtom c.y }

/-- The block normal form ([II, §4.4], the form of the graphs after (4.17)): every end at an
external atom identified with an internal atom by dotted edges, of a component other than a
dotted edge, moved to the least internal atom of its block. -/
def Graph.blockNorm {k n : ℕ} (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map Γ.flatComp, Γ.coeff⟩

/-- The representative of the molecule of `u` ([II, Def 2.10], with paths of waved and dotted
edges through external atoms): `u` if `u` is external, otherwise the least internal atom of its
molecule. -/
def Graph.molRep {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Atom k n :=
  match u with
  | .inl _ => u
  | .inr a => .inr (((List.finRange n).find? fun b => decide (Γ.SameMol (.inr a) (.inr b))).getD a)

/-- The class of the edge from the molecule of the block of an identified external atom to that
atom: blue at `⊕` (index `1`), red at `⊖` (index `2`), dotted at `⊗` and the other external
atoms. -/
def pinClass {k : ℕ} (a : Fin k) : MClass :=
  if a.val = 1 then .plus else if a.val = 2 then .minus else .dot

/-- The molecular graph in the block reading ([II, Def 2.11]): the vertices are the molecules of the
graph (with all its dotted edges), each represented by `Graph.molRep`; the edge with index
`.inl i` is the component `i` of the block normal form between the molecules of its ends, absent
if it is a dotted edge, lies inside one molecule, or is not an edge of the molecular graph
(`Kind.mclass`); the edge with index `.inr a` joins the molecule of the block of the external
atom `a` to `a`, of class `pinClass a`, and is absent if the block of `a` has no internal atom. -/
def Graph.toMG' {k n : ℕ} (Γ : Graph k n) : MGraph (Atom k n) (Fin Γ.comps.length ⊕ Fin k) where
  int := Finset.univ.image fun a : Fin n => Γ.molRep (.inr a)
  ext := Finset.univ.image fun a : Fin k => (.inl a : Atom k n)
  ends
    | .inl i => (Γ.molRep (Γ.flatComp Γ.comps[i]).x, Γ.molRep (Γ.flatComp Γ.comps[i]).y)
    | .inr a =>
      match Γ.anchor (.inl a) with
      | some b => (Γ.molRep (.inr b), .inl a)
      | none => (.inl a, .inl a)
  cls
    | .inl i =>
      if (Γ.flatComp Γ.comps[i]).kind = .dot ∨
          Γ.molRep (Γ.flatComp Γ.comps[i]).x = Γ.molRep (Γ.flatComp Γ.comps[i]).y then none
      else (Γ.flatComp Γ.comps[i]).kind.mclass
    | .inr a =>
      match Γ.anchor (.inl a) with
      | some _ => some (pinClass a)
      | none => none

/-- Sequentially pre-deterministic ([II, Def 5.9]) in the block reading: the molecular graph
`Graph.toMG'` is sequentially pre-deterministic. -/
def spdPM' {k n : ℕ} (Γ : Graph k n) : Prop := Γ.toMG'.SPD

/-- Globally standard ([II, Def 6.2]) in the block reading: the molecular graph `Graph.toMG'` is
sequentially pre-deterministic and each of its proper isolated subsets is weakly isolated, the red
edges from identified `⊖` atoms counted. -/
def gsPM' {k n : ℕ} (Γ : Graph k n) : Prop := Γ.toMG'.GloballyStandard

/-! ## The charge pattern, the external clause and the invariant of [II, Lemma 5.13] -/

/-- The charge pattern of the graphs of the expansions of `T_{a,b₁b₂}` (`b₁` is only a column index
of `G`, `b₂` only of `Ḡ`, `a` of neither): every random component (solid edge or weight, with any
minor or label) has an internal first atom and a second atom other than `⊗`; its second atom is
`⊕` only for a blue solid edge and `⊖` only for a red solid edge; every waved edge `s` joins two
internal atoms. -/
def Graph.ColourInv' {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∀ c ∈ Γ.comps,
    (c.kind.isRandom = true → c.x.isRight = true ∧ c.y ≠ .inl 0 ∧
      (c.y = .inl 1 → c.kind = .G .plus) ∧ (c.y = .inl 2 → c.kind = .G .minus)) ∧
    (c.kind = .waved .s → c.x.isRight = true ∧ c.y.isRight = true)

/-- The charge pattern `Graph.ColourInv'` of the block normal form. -/
def Graph.ColourInvB {n : ℕ} (Γ : Graph 3 n) : Prop := Γ.blockNorm.ColourInv'

/-- The number of components at `u` other than dotted and `×`-dotted edges. -/
def Graph.nonDotDeg {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : ℕ :=
  (Γ.comps.filter fun c => decide ((c.x = u ∨ c.y = u) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).length

/-- Every diffusive edge at the atom `u` ends at an internal or an identified atom (an atom whose
block has an internal atom) at its other end. -/
def Graph.DiffToPinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop :=
  ∀ c ∈ Γ.comps, c.kind.isDiffusive = true →
    (c.x = u → ¬ Γ.Unpinned c.y) ∧ (c.y = u → ¬ Γ.Unpinned c.x)

/-- Some diffusive edge joins the atom `u` to an internal or an identified atom. -/
def Graph.HasDiffToPinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop :=
  ∃ c ∈ Γ.comps, c.kind.isDiffusive = true ∧
    (c.x = u ∧ ¬ Γ.Unpinned c.y ∨ c.y = u ∧ ¬ Γ.Unpinned c.x)

/-- The clause on the external atoms that are not identified with an internal atom, under which
[II, Lemmas 5.10, 5.13] hold in the block reading (external atoms `⊗ = a = 0`, `⊕ = b₁ = 1`,
`⊖ = b₂ = 2`):
* every block with two or more atoms contains an internal atom, and no `×`-dotted edge joins two
  external atoms whose blocks have no internal atom;
* if the block of `⊗` has no internal atom: some diffusive edge joins `⊗` to an internal or
  identified atom, and every diffusive edge at `⊗` does;
* if the block of `⊖` has no internal atom: no diffusive edge is at `⊖`, and at most one
  component other than dotted and `×`-dotted edges is at `⊖`;
* if the block of `⊕` has no internal atom: a blue solid edge is at `⊕`, or a diffusive edge
  joins `⊕` to an internal or identified atom; every diffusive edge at `⊕` does; and at most one
  component other than dotted and `×`-dotted edges is at `⊕`. -/
def Graph.ExtClause {n : ℕ} (Γ : Graph 3 n) : Prop :=
  (∀ u v : Atom 3 n, u ≠ v → Γ.SameBlock u v → ∃ b : Fin n, Γ.SameBlock u (.inr b)) ∧
  (∀ c ∈ Γ.comps, c.kind = .xdot → ¬ (Γ.Unpinned c.x ∧ Γ.Unpinned c.y)) ∧
  (Γ.Unpinned (.inl 0) → Γ.HasDiffToPinned (.inl 0) ∧ Γ.DiffToPinned (.inl 0)) ∧
  (Γ.Unpinned (.inl 2) →
    (∀ c ∈ Γ.comps, c.kind.isDiffusive = true → c.x ≠ .inl 2 ∧ c.y ≠ .inl 2) ∧
    Γ.nonDotDeg (.inl 2) ≤ 1) ∧
  (Γ.Unpinned (.inl 1) →
    ((∃ c ∈ Γ.comps, c.kind = .G .plus ∧ (c.x = .inl 1 ∨ c.y = .inl 1)) ∨
      Γ.HasDiffToPinned (.inl 1)) ∧
    Γ.DiffToPinned (.inl 1) ∧ Γ.nonDotDeg (.inl 1) ≤ 1)

/-- No ghost edge ([II, Def 9.4]). -/
def Graph.NoGhost {k n : ℕ} (Γ : Graph k n) : Prop := ∀ c ∈ Γ.comps, c.kind ≠ .ghost

/-- The atom of every `P`/`Q` label is internal. -/
def Graph.LabelsInt {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, c.label.all (fun ℓ => ℓ.2.isRight) = true

/-- The invariant of [II, Lemma 5.13] in the block reading: sequentially pre-deterministic in the
block reading, the charge pattern of the block normal form, the clause on the external atoms, no
ghost edge, and internal label atoms. -/
def Graph.InvB' {n : ℕ} (Γ : Graph 3 n) : Prop :=
  spdPM' Γ ∧ Γ.ColourInvB ∧ Γ.ExtClause ∧ Γ.NoGhost ∧ Γ.LabelsInt

/-- [II, Def 6.3 (3)] in the block reading: the atom `u` of every `Q`-label lies in a molecule of
the minimal isolated subset of `Graph.toMG'`, or `u` is `⊕` or `⊖` and either the graph has no
internal atom or `u` is joined by a waved edge to an internal atom whose molecule lies in that
minimal isolated subset. -/
def Graph.QLabelInMISB {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∀ c ∈ Γ.comps, ∀ u, c.label = some (.Q, u) →
    Γ.molRep u ∈ Γ.toMG'.MIS ∨
      ((u = .inl 1 ∨ u = .inl 2) ∧
        (n = 0 ∨ ∃ c' ∈ Γ.comps, ∃ a : Fin n, (∃ w, c'.kind = .waved w) ∧
          (c'.x = u ∧ c'.y = .inr a ∨ c'.x = .inr a ∧ c'.y = u) ∧
          Γ.molRep (.inr a) ∈ Γ.toMG'.MIS))

/-- A component in the block normal form keeps its kind. -/
theorem Graph.flatComp_kind {k n : ℕ} (Γ : Graph k n) (c : Comp (Atom k n)) :
    (Γ.flatComp c).kind = c.kind := by
  unfold Graph.flatComp
  split_ifs <;> rfl

/-- Without ghost edges, `Graph.toMG'` has no edge of class ghost. -/
theorem Graph.toMG'_noGhost {k n : ℕ} (Γ : Graph k n) (h : Γ.NoGhost) :
    ∀ e, Γ.toMG'.cls e ≠ some .ghost := by
  have hm : ∀ κ : Kind, κ ≠ .ghost → κ.mclass ≠ some .ghost := by
    intro κ hκ
    cases κ with
    | G c => cases c <;> simp [Kind.mclass]
    | aux j r b => cases b <;> simp [Kind.mclass]
    | ghost => exact absurd rfl hκ
    | _ => simp [Kind.mclass]
  rintro (i | a)
  · simp only [Graph.toMG']
    split_ifs
    · simp
    · exact hm _ (by rw [Graph.flatComp_kind]; exact h _ (List.getElem_mem _))
  · simp only [Graph.toMG']
    split
    · unfold pinClass
      split_ifs <;> simp
    · simp

/-! ## Graphs whose internal atoms lie in one molecule -/

section OneMol

/-- The representative of an internal atom is internal. -/
private theorem MolRead_molRep_inr {k n : ℕ} (Γ : Graph k n) (a : Fin n) :
    ∃ b : Fin n, Γ.molRep (.inr a) = .inr b := ⟨_, rfl⟩

/-- If all internal atoms lie in one molecule, `Graph.molRep` is constant on them. -/
private theorem MolRead_molRep_eq {k n : ℕ} (Γ : Graph k n)
    (h : ∀ b c : Fin n, Γ.SameMol (.inr b) (.inr c)) (a a' : Fin n) :
    Γ.molRep (.inr a) = Γ.molRep (.inr a') := by
  have e : (fun b : Fin n => decide (Γ.SameMol (.inr a) (.inr b))) =
      fun b => decide (Γ.SameMol (.inr a') (.inr b)) :=
    funext fun b => (decide_eq_true (h a b)).trans (decide_eq_true (h a' b)).symm
  have hs : ((List.finRange n).find?
      fun b : Fin n => decide (Γ.SameMol (.inr a') (.inr b))).isSome :=
    List.find?_isSome.2 ⟨a', List.mem_finRange a', decide_eq_true (h a' a')⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
  simp only [Graph.molRep, e, hb, Option.getD_some]

/-- If all internal atoms lie in one molecule, `Graph.toMG'` has at most one internal vertex. -/
private theorem MolRead_int_card_le_one {k n : ℕ} (Γ : Graph k n)
    (h : ∀ b c : Fin n, Γ.SameMol (.inr b) (.inr c)) : Γ.toMG'.int.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact MolRead_molRep_eq Γ h a b

/-- If all internal atoms lie in one molecule, `Graph.toMG'` has no internal blue solid edge. -/
private theorem MolRead_not_isIntPlus {k n : ℕ} (Γ : Graph k n)
    (h : ∀ b c : Fin n, Γ.SameMol (.inr b) (.inr c)) : ∀ e, ¬ Γ.toMG'.IsIntPlus e := by
  rintro (i | a) ⟨hcls, h1, h2⟩
  · have heq := Finset.card_le_one.1 (MolRead_int_card_le_one Γ h) _ h1 _ h2
    simp only [Graph.toMG'] at hcls heq
    simp only [heq, or_true, ite_true] at hcls
    exact absurd hcls (by simp)
  · have hend : (Γ.toMG'.ends (.inr a)).2 = .inl a := by
      simp only [Graph.toMG']
      split <;> rfl
    rw [hend] at h2
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and] at h2
    obtain ⟨a', ha'⟩ := h2
    obtain ⟨b, hb⟩ := MolRead_molRep_inr Γ a'
    rw [hb] at ha'
    exact Sum.inr_ne_inl ha'

/-- A molecular multigraph with at most one internal vertex has no proper isolated subset of its
internal vertices. -/
private theorem MolRead_no_properIso {V E : Type} {G : MGraph V E} (hc : G.int.card ≤ 1) :
    ∀ Q, ¬ G.IsProperIso G.int Q := by
  rintro Q ⟨⟨hQ, e₁, e₂, -, hcross⟩, hlt⟩
  have hQe : Q = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨w, hw, hwQ⟩ := Finset.exists_of_ssubset hlt
    exact hwQ (Finset.card_le_one.1 hc w hw v (hQ hv) ▸ hv)
  subst hQe
  obtain ⟨-, -, -, -, hc'⟩ := (hcross e₁).2 (Or.inl rfl)
  simp [MGraph.Cut] at hc'

/-- A molecular multigraph with at most one internal vertex: every set of edges spans. -/
private theorem MolRead_spans_of_card_le_one {V E : Type} {G : MGraph V E} (hc : G.int.card ≤ 1)
    (B : Finset E) : G.Spans B := by
  intro S hS ⟨v, hv⟩ hn
  refine absurd (fun w hw => ?_) hn
  rw [Finset.card_le_one.1 hc w hw v (hS hv)]
  exact hv

/-- A molecular multigraph with at most one internal vertex and no internal blue solid edge is
sequentially pre-deterministic. -/
private theorem MolRead_spd_of_card_le_one {V E : Type} [DecidableEq V] [DecidableEq E]
    {G : MGraph V E} (hc : G.int.card ≤ 1) (hp : ∀ e, ¬ G.IsIntPlus e) : G.SPD := by
  refine MGraph.SPD_of_preDet _ _ _ ?_ (MolRead_no_properIso hc)
  exact ⟨⟨∅, ∅, disjoint_bot_left, by simp, by simp, MolRead_spans_of_card_le_one hc _,
    MolRead_spans_of_card_le_one hc _⟩, [], List.nodup_nil,
    fun e => ⟨by simp, fun h => absurd h (hp e)⟩, fun j hj => absurd hj (by simp)⟩

end OneMol

/-- A graph whose internal atoms lie in one molecule is sequentially pre-deterministic in the
block reading. -/
theorem spdPM'_of_oneMol :
  ∀ (k n : ℕ) (Γ : Graph k n), (∀ b c : Fin n, Γ.SameMol (.inr b) (.inr c)) → spdPM' Γ := by
  intro k n Γ h
  exact MolRead_spd_of_card_le_one (MolRead_int_card_le_one Γ h) (MolRead_not_isIntPlus Γ h)

/-- A graph whose internal atoms lie in one molecule is globally standard in the block reading. -/
theorem gsPM'_of_oneMol :
  ∀ (k n : ℕ) (Γ : Graph k n), (∀ b c : Fin n, Γ.SameMol (.inr b) (.inr c)) → gsPM' Γ := by
  intro k n Γ h
  have hc := MolRead_int_card_le_one Γ h
  exact ⟨MolRead_spd_of_card_le_one hc (MolRead_not_isIntPlus Γ h),
    fun P hP => absurd hP (MolRead_no_properIso hc P)⟩

section BlockNorm

end BlockNorm

/-! ## Decidability instances for concrete graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance MolRead_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

end Instances

end RBM8D.Graphs
