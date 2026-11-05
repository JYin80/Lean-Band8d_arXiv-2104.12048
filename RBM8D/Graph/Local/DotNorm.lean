import RBM8D.Graph.Local.Strategy

/-!
# Dot normalisation and the scaling order of [II, (2.5)]

`Graph.ord` counts every dotted edge `1_{u = v}` as `2` ([II, (2.5)]). Read as one lost summation
index per dotted edge, (2.5) counts only the dotted edges of a spanning forest of each dot block:
`Graph.paperOrd` is the scaling order minus twice the dot excess. Removing redundant dotted edges
(those whose ends are joined by the other dotted edges, the elementary step `dropDot` of
[I, Strategy 3.21]) brings the dot excess to `0` and the scaling order to `Graph.paperOrd`, and
keeps the value, the blocks, the other components and the hypotheses of the local expansion.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

section PaperOrd

variable {k n : ℕ}

/-- The scaling order of [II, (2.5)] with one lost index per dotted edge of a spanning forest of
the blocks: `Graph.ord` minus twice the dot excess. -/
def Graph.paperOrd (g : Graph k n) : ℤ := g.ord - 2 * g.dotExcess

/-- `Graph.paperOrd` is the order `Graph.obl` of the descent of [I, Strategy 3.21]. -/
theorem Graph.paperOrd_eq_obl (g : Graph k n) : g.paperOrd = g.obl := rfl

/-- With dot excess `0` (the dotted edges form a forest without loops) the two counts agree. -/
theorem Graph.paperOrd_of_dotExcess {g : Graph k n} (h : g.dotExcess = 0) :
    g.paperOrd = g.ord := by
  simp [Graph.paperOrd, h]

end PaperOrd

/-! ## Removal of redundant dotted edges -/

section Step

variable {k n : ℕ}

/-- One removal of a dotted edge whose ends are joined by the other dotted edges: the elementary
step `LocElemStep.dropDot` of [I, Strategy 3.21], with the number of internal atoms fixed. -/
def DotNormStep (g g' : Graph k n) : Prop :=
  ∃ (i : ℕ) (c : Comp (Atom k n)), g.comps[i]? = some c ∧ c.kind = .dot ∧
    (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).SameBlock c.x c.y ∧
    g' = ⟨g.comps.eraseIdx i, g.coeff⟩

/-- A step `DotNormStep` is an elementary step of [I, Strategy 3.21]. -/
theorem DotNormStep.locElemStep {g g' : Graph k n} (h : DotNormStep g g') :
    LocElemStep ⟨n, g⟩ ⟨n, g'⟩ := by
  obtain ⟨i, c, hc, hk, hb, rfl⟩ := h
  exact LocElemStep.dropDot i g c hc hk hb

/-- A chain of steps `DotNormStep` is a chain of elementary steps of [I, Strategy 3.21]. -/
theorem DotNormStep.reflTransGen {g g' : Graph k n}
    (h : Relation.ReflTransGen DotNormStep g g') :
    Relation.ReflTransGen LocElemStep ⟨n, g⟩ ⟨n, g'⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail hs.locElemStep

/-- Reachability passes to a graph in which every edge of the first graph has its ends joined. -/
private theorem DotNorm.reach_of_adj {V : Type*} {G H : SimpleGraph V}
    (h : ∀ a b, G.Adj a b → H.Reachable a b) {u v : V} (huv : G.Reachable u v) :
    H.Reachable u v := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- Reachability in `fromRel R` passes to `fromRel R₁` when every pair related by `R` is related
by `R₁` or joined in a graph `B` below `fromRel R₁`. -/
private theorem DotNorm.reach_fromRel {V : Type*} {R R₁ : V → V → Prop} {B : SimpleGraph V}
    (hR : ∀ a b, R a b → R₁ a b ∨ B.Reachable a b) (hB : B ≤ SimpleGraph.fromRel R₁) {u v : V}
    (h : (SimpleGraph.fromRel R).Reachable u v) : (SimpleGraph.fromRel R₁).Reachable u v := by
  refine DotNorm.reach_of_adj (fun a b hab => ?_) h
  obtain ⟨hne, hab⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
  rcases hab with hab | hab
  · rcases hR a b hab with h1 | h1
    · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl h1⟩).reachable
    · exact h1.mono hB
  · rcases hR b a hab with h1 | h1
    · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inr h1⟩).reachable
    · exact (h1.mono hB).symm

/-- A list with the entry `c` at index `i`, and the list with that entry removed. -/
private theorem DotNorm.split {α : Type*} {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c) :
    ∃ A B : List α, L = A ++ c :: B ∧ L.eraseIdx i = A ++ B := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  refine ⟨L.take i, L.drop (i + 1), ?_, List.eraseIdx_eq_take_drop_succ L i⟩
  conv_lhs => rw [← List.take_append_drop i L]
  rw [List.drop_eq_getElem_cons hi]

/-- The ends of a dotted edge lie in one block. -/
private theorem DotNorm.sameBlock_of_mem {g : Graph k n} {d : Comp (Atom k n)} (hd : d ∈ g.comps)
    (hk : d.kind = .dot) : g.SameBlock d.x d.y := by
  by_cases h : d.x = d.y
  · rw [h]; exact SimpleGraph.Reachable.refl _
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨d, hd, hk, rfl, rfl⟩⟩).reachable

/-- The dotted edges of a plain graph carry no label. -/
private theorem DotNorm.dot_label {g : Graph k n} (hP : g.Plain) {d : Comp (Atom k n)}
    (hd : d ∈ g.comps) (hk : d.kind = .dot) : d.label = none := by
  have hwf := (hP d hd).2.2.2.2
  by_contra hne
  have := hwf.2 (Option.isSome_iff_ne_none.2 hne)
  rw [hk] at this
  cases this

/-- The clauses kept by the removal of redundant dotted edges from `g` to `g'`. -/
private structure DotNorm.Keep (C : ℕ) (g g' : Graph k n) : Prop where
  coeff : g'.coeff = g.coeff
  sub : g'.comps.Sublist g.comps
  nondot : g'.comps.filter (fun d => decide (d.kind ≠ .dot)) =
    g.comps.filter (fun d => decide (d.kind ≠ .dot))
  block : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v
  val : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι), g'.valR PF D e = g.valR PF D e
  normal : g'.Normal C
  plain : g'.Plain
  lf : g.LabelFree → g'.LabelFree
  q : g.IsQGraph → g'.IsQGraph
  rfi : g.RandomFirstInt → g'.RandomFirstInt
  xa : g.XdotApart → g'.XdotApart
  mol : ∀ u v, g'.SameMol u v ↔ g.SameMol u v
  dc : g.DoublyConnected → g'.DoublyConnected
  labels : g'.labels = g.labels

private theorem DotNorm.Keep.rfl' {C : ℕ} {g : Graph k n} (hN : g.Normal C) (hP : g.Plain) :
    DotNorm.Keep C g g where
  coeff := rfl
  sub := List.Sublist.refl _
  nondot := rfl
  block _ _ := Iff.rfl
  val _ _ _ _ _ _ _ := rfl
  normal := hN
  plain := hP
  lf := id
  q := id
  rfi := id
  xa := id
  mol _ _ := Iff.rfl
  dc := id
  labels := rfl

private theorem DotNorm.Keep.trans {C : ℕ} {g g₁ g₂ : Graph k n} (h₁ : DotNorm.Keep C g g₁)
    (h₂ : DotNorm.Keep C g₁ g₂) : DotNorm.Keep C g g₂ where
  coeff := h₂.coeff.trans h₁.coeff
  sub := h₂.sub.trans h₁.sub
  nondot := h₂.nondot.trans h₁.nondot
  block u v := (h₂.block u v).trans (h₁.block u v)
  val Ω ι _ _ PF D e := (h₂.val Ω ι PF D e).trans (h₁.val Ω ι PF D e)
  normal := h₂.normal
  plain := h₂.plain
  lf h := h₂.lf (h₁.lf h)
  q h := h₂.q (h₁.q h)
  rfi h := h₂.rfi (h₁.rfi h)
  xa h := h₂.xa (h₁.xa h)
  mol u v := (h₂.mol u v).trans (h₁.mol u v)
  dc h := h₂.dc (h₁.dc h)
  labels := h₂.labels.trans h₁.labels

/-- The doubly connected property passes to the graph without the dotted edge of index `i`. -/
private theorem DotNorm.dc_erase {g : Graph k n} {i : ℕ} (hi : i < g.comps.length)
    (hk : g.comps[i].kind = .dot)
    (hmol : ∀ u v, (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).SameMol u v ↔ g.SameMol u v)
    (h : g.DoublyConnected) : (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).DoublyConnected := by
  set L := g.comps with hL
  have hlen : (L.eraseIdx i).length = L.length - 1 := List.length_eraseIdx_of_lt hi
  let ψ : Fin (L.eraseIdx i).length → Fin L.length := fun j =>
    ⟨if j.val < i then j.val else j.val + 1, by split <;> omega⟩
  have hψ : ∀ j : Fin (L.eraseIdx i).length, (L.eraseIdx i)[j] = L[ψ j] := by
    intro j
    simp only [Fin.getElem_fin, ψ]
    rw [List.getElem_eraseIdx]
    split_ifs <;> rfl
  have hsurj : ∀ b : Fin L.length, b.val ≠ i → ∃ j, ψ j = b := by
    intro b hb
    refine ⟨⟨if b.val < i then b.val else b.val - 1, by split <;> omega⟩, Fin.ext ?_⟩
    simp only [ψ]
    split_ifs <;> omega
  have hne : ∀ b : Fin L.length, (L[b].kind.isDiffusive = true ∨ L[b].kind.isBlue = true) →
      b.val ≠ i := by
    intro b hb hbi
    have : L[b] = L[i] := by simp only [Fin.getElem_fin, hbi]
    rw [this, hk] at hb
    simp [Kind.isDiffusive, Kind.isBlue] at hb
  obtain ⟨black, blue, hdis, hblack, hblue, hsb, hsu⟩ := h
  let tr : Finset (Fin L.length) → Finset (Fin (L.eraseIdx i).length) := fun B =>
    Finset.univ.filter fun j => ψ j ∈ B
  have hspan : ∀ B : Finset (Fin L.length),
      (∀ b ∈ B, L[b].kind.isDiffusive = true ∨ L[b].kind.isBlue = true) → g.Spans B →
      (⟨L.eraseIdx i, g.coeff⟩ : Graph k n).Spans (tr B) := by
    intro B hB hS
    refine hS.mono fun a b hab => ?_
    rw [Graph.net, SimpleGraph.fromRel_adj] at hab ⊢
    refine ⟨hab.1, ?_⟩
    have key : ∀ a b : Fin n, (g.SameMol (.inr a) (.inr b) ∨
        ∃ j ∈ B, g.comps[j].x = .inr a ∧ g.comps[j].y = .inr b) →
        ((⟨L.eraseIdx i, g.coeff⟩ : Graph k n).SameMol (.inr a) (.inr b) ∨
        ∃ j ∈ tr B, (L.eraseIdx i)[j].x = .inr a ∧ (L.eraseIdx i)[j].y = .inr b) := by
      rintro a b (hm | ⟨j, hj, hx, hy⟩)
      · exact Or.inl ((hmol _ _).2 hm)
      · obtain ⟨j', rfl⟩ := hsurj j (hne j (hB j hj))
        refine Or.inr ⟨j', by simp [tr, hj], ?_, ?_⟩
        · rw [hψ]; exact hx
        · rw [hψ]; exact hy
    exact hab.2.imp (key a b) (key b a)
  refine ⟨tr black, tr blue, ?_, ?_, ?_, hspan black (fun b hb => Or.inl (hblack b hb)) hsb,
    hspan blue hblue hsu⟩
  · rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    exact Finset.disjoint_left.1 hdis hj hj'
  · intro j hj
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    change (L.eraseIdx i)[j].kind.isDiffusive = true
    rw [hψ]
    exact hblack _ hj
  · intro j hj
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    change (L.eraseIdx i)[j].kind.isDiffusive = true ∨ (L.eraseIdx i)[j].kind.isBlue = true
    rw [hψ]
    exact hblue _ hj

/-- One removal of a redundant dotted edge from a normal regular plain graph: it lowers the dot
excess by `1` and the scaling order by `2`, and keeps the clauses `DotNorm.Keep`. -/
private theorem DotNorm.step {C : ℕ} {g : Graph k n} (hN : g.Normal C) (hP : g.Plain) {i : ℕ}
    {c : Comp (Atom k n)} (hc : g.comps[i]? = some c) (hk : c.kind = .dot)
    (hr : (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).SameBlock c.x c.y) :
    (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).dotExcess + 1 = g.dotExcess ∧
      (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).ord + 2 = g.ord ∧
      DotNorm.Keep C g ⟨g.comps.eraseIdx i, g.coeff⟩ := by
  set g₁ : Graph k n := ⟨g.comps.eraseIdx i, g.coeff⟩ with hg₁
  obtain ⟨-, he, hord, hmem, hb, -, -, hwt⟩ := drop_one g hc hk hr
  have hsub : ∀ d ∈ g₁.comps, d ∈ g.comps := fun d hd => List.mem_of_mem_eraseIdx hd
  have hdich : ∀ d ∈ g.comps, d ∈ g₁.comps ∨ g₁.SameBlock d.x d.y := by
    intro d hd
    by_cases hdk : d.kind = .dot
    · exact Or.inr ((hb d.x d.y).2 (DotNorm.sameBlock_of_mem hd hdk))
    · exact Or.inl (hmem d hd hdk)
  have hdlab : ∀ d ∈ g.comps, d.kind = .dot → d.label = none :=
    fun d hd hdk => DotNorm.dot_label hP hd hdk
  obtain ⟨A, B, hA, hAB⟩ := DotNorm.split hc
  have hc0 : c.label = none := hdlab c (by rw [hA]; simp) hk
  -- reachability in a graph of components that contains the dotted edges
  have hreach : ∀ p : Comp (Atom k n) → Prop, (∀ d, d.kind = .dot → p d) → ∀ u v,
      (SimpleGraph.fromRel fun a b => ∃ d ∈ g.comps, p d ∧ d.x = a ∧ d.y = b).Reachable u v →
      (SimpleGraph.fromRel fun a b => ∃ d ∈ g₁.comps, p d ∧ d.x = a ∧ d.y = b).Reachable u v := by
    intro p hp u v h
    refine DotNorm.reach_fromRel (B := g₁.dotGraph) ?_ ?_ h
    · rintro a b ⟨d, hd, hpd, rfl, rfl⟩
      rcases hdich d hd with h1 | h1
      · exact Or.inl ⟨d, h1, hpd, rfl, rfl⟩
      · exact Or.inr h1
    · intro a b hab
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
      rw [SimpleGraph.fromRel_adj]
      refine ⟨hab.1, hab.2.imp ?_ ?_⟩ <;>
      · rintro ⟨d, hd, hdk, rfl, rfl⟩
        exact ⟨d, hd, hp d hdk, rfl, rfl⟩
  have hedge : ∀ u v, g.edgeGraph.Reachable u v → g₁.edgeGraph.Reachable u v := by
    intro u v h
    have h' := hreach (fun _ => True) (fun _ _ => trivial) u v (by
      refine DotNorm.reach_of_adj (fun a b hab => ?_) h
      rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at hab
      refine ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab.1, hab.2.imp ?_ ?_⟩).reachable <;>
      · rintro ⟨d, hd, rfl, rfl⟩
        exact ⟨d, hd, trivial, rfl, rfl⟩)
    refine DotNorm.reach_of_adj (fun a b hab => ?_) h'
    rw [SimpleGraph.fromRel_adj] at hab
    refine ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab.1, hab.2.imp ?_ ?_⟩).reachable <;>
    · rintro ⟨d, hd, -, rfl, rfl⟩
      exact ⟨d, hd, rfl, rfl⟩
  have hmolR : ∀ u v, g₁.molGraph.Reachable u v ↔ g.molGraph.Reachable u v := by
    intro u v
    constructor
    · intro h
      refine h.mono fun a b hab => ?_
      rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hab ⊢
      refine ⟨hab.1, hab.2.imp ?_ ?_⟩ <;>
      · rintro ⟨d, hd, hj, rfl, rfl⟩
        exact ⟨d, hsub d hd, hj, rfl, rfl⟩
    · exact hreach (fun d => d.kind.joinsMol = true) (fun d hdk => by rw [hdk]; rfl) u v
  have hmol : ∀ u v, g₁.SameMol u v ↔ g.SameMol u v := by
    intro u v
    simp only [Graph.SameMol, hmolR]
  refine ⟨he, hord, ⟨rfl, List.eraseIdx_sublist _ _, ?_, hb, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hmol, ?_, ?_⟩⟩
  · change (g.comps.eraseIdx i).filter _ = g.comps.filter _
    rw [hAB, hA]
    simp [List.filter_append, hk]
  · exact dropDot_value g hc hk hr hdlab
  · -- normal regular
    obtain ⟨⟨hsz, hcon, hint, hnoint⟩, hsol, hxs⟩ := hN
    refine ⟨⟨?_, fun u v => hedge u v (hcon u v), ?_, fun d hd => hnoint d (hsub d hd)⟩,
      fun d hd => hsol d (hsub d hd), ?_⟩
    · have := (List.eraseIdx_sublist g.comps i).length_le
      change k + n + (g.comps.eraseIdx i).length ≤ C
      omega
    · rw [hwt]; exact hint
    · intro u v huv
      have key : ∀ P : Kind → Prop, (∀ κ, P κ → κ ≠ .dot) →
          ((∃ c ∈ g₁.comps, P c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
            (∃ c ∈ g.comps, P c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u))) := by
        intro P hPd
        constructor
        · rintro ⟨c, hc, h⟩; exact ⟨c, hsub c hc, h⟩
        · rintro ⟨c, hc, h⟩; exact ⟨c, hmem c hc (hPd _ h.1), h⟩
      rw [key (fun κ => κ = .xdot) (fun κ h => by rw [h]; simp),
        key (fun κ => κ.isSolid = true) (fun κ h hd => by rw [hd] at h; cases h)]
      exact hxs u v huv
  · exact fun d hd => hP d (hsub d hd)
  · exact fun hL d hd => hL d (hsub d hd)
  · rintro ⟨u, ⟨d, hd, hl⟩, hall⟩
    refine ⟨u, ⟨d, hmem d hd fun hdk => ?_, hl⟩, fun d' hd' => hall d' (hsub d' hd')⟩
    rw [hdlab d hd hdk] at hl
    cases hl
  · exact fun hK d hd => hK d (hsub d hd)
  · intro hX d hd hdk hbl
    exact hX d (hsub d hd) hdk ((hb d.x d.y).1 hbl)
  · obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
    exact DotNorm.dc_erase hi (by rw [hci]; exact hk) hmol
  · change (List.filterMap Comp.label (g.comps.eraseIdx i)).dedup =
      (List.filterMap Comp.label g.comps).dedup
    rw [hAB, hA]
    simp [List.filterMap_append, hc0]

/-- Removing `r` redundant dotted edges, one at a time, from a graph of dot excess `r`. -/
private theorem DotNorm.loop {C : ℕ} : ∀ (r : ℕ) (g : Graph k n), g.dotExcess = r →
    g.Normal C → g.Plain → ∃ g' : Graph k n, Relation.ReflTransGen DotNormStep g g' ∧
      g'.dotExcess = 0 ∧ g'.ord = g.ord - 2 * r ∧ DotNorm.Keep C g g'
  | 0, g, h, hN, hP => ⟨g, Relation.ReflTransGen.refl, by simpa using h, by simp,
      DotNorm.Keep.rfl' hN hP⟩
  | r + 1, g, h, hN, hP => by
    obtain ⟨i, c, hc, hk, hr⟩ := exists_red_of_pos (L := g.comps)
      (by have : g.dotExcess = eL g.comps := rfl; push_cast at h; omega)
    obtain ⟨he, hord, hK⟩ := DotNorm.step hN hP hc hk hr
    obtain ⟨g', h1, h2, h3, h4⟩ := DotNorm.loop r ⟨g.comps.eraseIdx i, g.coeff⟩
      (by push_cast at h; omega) hK.normal hK.plain
    exact ⟨g', Relation.ReflTransGen.head ⟨i, c, hc, hk, hr, rfl⟩ h1, h2,
      by push_cast; omega, hK.trans h4⟩

/-- Dot normalisation ([II, (2.5)] with one lost index per dotted edge of a spanning forest of the
blocks): a normal regular plain graph `g` reaches, by removals of redundant dotted edges only, a
graph `g'` of dot excess `0` and scaling order `g.paperOrd`, with the same coefficient, the same
components other than dotted edges (in order), the same blocks, the same labels and the same
value for every data record and family of conditional expectations; `g'` is normal regular and
plain, and the properties label-free, `Q`-graph, random first atoms internal, `×`-dotted edges
apart, the molecules and the doubly connected property ([I, Def 6.5]) pass from `g` to `g'`. -/
theorem Graph.exists_dotNorm {C : ℕ} (g : Graph k n) (hN : g.Normal C) (hP : g.Plain) :
    ∃ g' : Graph k n, Relation.ReflTransGen DotNormStep g g' ∧
      Relation.ReflTransGen LocElemStep ⟨n, g⟩ ⟨n, g'⟩ ∧
      g'.dotExcess = 0 ∧ g'.ord = g.paperOrd ∧ g'.coeff = g.coeff ∧ g'.comps.Sublist g.comps ∧
      g'.comps.filter (fun d => decide (d.kind ≠ .dot)) =
        g.comps.filter (fun d => decide (d.kind ≠ .dot)) ∧
      (∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) ∧
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e : Fin k → ι), g'.valR PF D e = g.valR PF D e) ∧
      g'.Normal C ∧ g'.Plain ∧ (g.LabelFree → g'.LabelFree) ∧ (g.IsQGraph → g'.IsQGraph) ∧
      (g.RandomFirstInt → g'.RandomFirstInt) ∧ (g.XdotApart → g'.XdotApart) ∧
      (∀ u v, g'.SameMol u v ↔ g.SameMol u v) ∧ (g.DoublyConnected → g'.DoublyConnected) ∧
      g'.labels = g.labels := by
  have h0 : 0 ≤ g.dotExcess := eL_nonneg g.comps
  obtain ⟨g', h1, h2, h3, hK⟩ := DotNorm.loop (C := C) g.dotExcess.toNat g
    (Int.toNat_of_nonneg h0).symm hN hP
  refine ⟨g', h1, DotNormStep.reflTransGen h1, h2, ?_, hK.coeff, hK.sub, hK.nondot, hK.block,
    hK.val, hK.normal, hK.plain, hK.lf, hK.q, hK.rfi, hK.xa, hK.mol, hK.dc, hK.labels⟩
  rw [h3, Int.toNat_of_nonneg h0]
  rfl

end Step

section DotOrd

variable {k n : ℕ}

end DotOrd

section Instances

variable {k n : ℕ}

end Instances

end RBM8D.Graphs
