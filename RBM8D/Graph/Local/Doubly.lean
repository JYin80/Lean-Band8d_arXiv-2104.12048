module

public import RBM8D.Graph.Local.Weight
public import RBM8D.Graph.Local.Edge

@[expose] public section

/-!
# Local expansions keep the doubly connected property

[II, Lemma 4.10]. A doubly connected structure ([II, Def 2.12]) is recorded as a list of the
components of a graph, each tagged as unused, black or blue. Every local expansion
(`O_dot`, `O^{(x)}_weight`, `O^{(x)}_multi-e`, `O^{(x)}_GG`, `O^{(x)}_GḠ`) is checked term by term:
atoms identified by dotted edges map to atoms of one molecule, new atoms are joined to the atom `x`
by waved edges, and every blue solid edge that is removed is replaced by a path of blue solid
edges and waved edges.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Tagged components

A doubly connected structure is recorded as a list of components, each carrying a tag: `none`
(unused), `some false` (black net) or `some true` (blue net). -/

section Tagged

variable {k n m : ℕ}

/-- The kinds usable in a blue net whose solid edges have charge `bc`: the solid edges of charge
`bc` and the ghost edges. -/
private def Kind.blueC (bc : Charge) : Kind → Bool
  | .G c => decide (c = bc)
  | .ghost => true
  | _ => false

private theorem Kind.blueC_plus (κ : Kind) : κ.blueC .plus = κ.isBlue := by
  cases κ with
  | G c => cases c <;> rfl
  | _ => rfl

/-- A component with a tag. -/
private abbrev TC (k n : ℕ) : Type := Comp (Atom k n) × Option Bool

/-- The graph on the internal atoms whose edges join two atoms of one molecule, or the two ends of
a component of `L` with the tag `some t`. -/
private def Graph.netT (Γ : Graph k n) (L : List (TC k n)) (t : Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => Γ.SameMol (Sum.inr a) (Sum.inr b) ∨
    ∃ p ∈ L, p.2 = some t ∧ p.1.x = Sum.inr a ∧ p.1.y = Sum.inr b

/-- The tagged list `L` is a doubly connected structure on `Γ` with blue charge `bc`: it lists the
components of `Γ`, black ones are diffusive, blue ones are diffusive or blue, and each net spans the
internal atoms. -/
private structure Graph.DCT (bc : Charge) (Γ : Graph k n) (L : List (TC k n)) : Prop where
  map_fst : L.map Prod.fst = Γ.comps
  black : ∀ p ∈ L, p.2 = some false → p.1.kind.isDiffusive = true
  blue : ∀ p ∈ L, p.2 = some true → p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true
  spanBlack : (Γ.netT L false).Preconnected
  spanBlue : (Γ.netT L true).Preconnected

/-- The graph has a doubly connected structure with blue charge `bc`. -/
private def Graph.DCS (bc : Charge) (Γ : Graph k n) : Prop := ∃ L, Γ.DCT bc L

private theorem Graph.sameMol_of_comp {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind.joinsMol = true) (hx : c.x.isRight = true) (hy : c.y.isRight = true) :
    Γ.SameMol c.x c.y := by
  by_cases h : c.x = c.y
  · exact Or.inl h
  · exact Or.inr ⟨hx, hy, (SimpleGraph.fromRel_adj _ _ _).2
      ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable⟩

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

/-- The tagged component `q` of a graph with `j` more internal atoms is `p` with its atoms moved
(its label and minor may differ). -/
private def Sim (j : ℕ) (p : TC k n) (q : TC k (n + j)) : Prop :=
  q.2 = p.2 ∧ q.1.kind = p.1.kind ∧ q.1.x = liftA j p.1.x ∧ q.1.y = liftA j p.1.y

/-- Extending a doubly connected structure to a graph with `j` more internal atoms: the
components `X` are moved copies of components of `L` and the components `N` are new; waved and
dotted components and black components are kept, a blue component is kept or its ends are joined
in the blue net, and every new internal atom lies in the molecule of an old one. -/
private theorem Graph.DCT.extend {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)} (X N : List (TC k (n + j)))
    (hmap : (X ++ N).map Prod.fst = Γ'.comps)
    (hX : ∀ q ∈ X, ∃ p ∈ L, Sim j p q)
    (hNbl : ∀ q ∈ N, q.2 = some false → q.1.kind.isDiffusive = true)
    (hNbu : ∀ q ∈ N, q.2 = some true → q.1.kind.isDiffusive = true ∨ q.1.kind.blueC bc = true)
    (hret : ∀ p ∈ L, (p.1.kind.joinsMol = true ∨ p.2 = some false) → ∃ q ∈ X, Sim j p q)
    (hblue : ∀ p ∈ L, p.2 = some true → ∀ a b, p.1.x = Sum.inr a → p.1.y = Sum.inr b →
      (∃ q ∈ X, Sim j p q) ∨ (Γ'.netT (X ++ N) true).Reachable (Fin.castAdd j a) (Fin.castAdd j b))
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) : Γ'.DCT bc (X ++ N) := by
  have hf : Sum.map id (Fin.castAdd j) = (liftA j : Atom k n → Atom k (n + j)) := rfl
  refine h.transport (Fin.castAdd j) (X ++ N) hmap ?_ ?_ ?_ ?_ hnew
  · intro q hq hqt
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨p, hp, hs⟩ := hX q hq
      rw [hs.2.1]
      exact h.black p hp (hs.1 ▸ hqt)
    · exact hNbl q hq hqt
  · intro q hq hqt
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨p, hp, hs⟩ := hX q hq
      rw [hs.2.1]
      exact h.blue p hp (hs.1 ▸ hqt)
    · exact hNbu q hq hqt
  · intro c hc hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (h.map_fst ▸ hc)
    obtain ⟨q, hq, hs⟩ := hret p hp (Or.inl hk)
    have hqc : q.1 ∈ Γ'.comps := hmap ▸ List.mem_map_of_mem (List.mem_append_left _ hq)
    rw [hf, ← hs.2.2.1, ← hs.2.2.2]
    exact Graph.molReach_of_comp hqc (hs.2.1 ▸ hk)
  · intro t p hp hpt a b hx hy
    rcases t with _ | _
    · obtain ⟨q, hq, hs⟩ := hret p hp (Or.inr hpt)
      refine Graph.netT_reach_of_mem _ _ _ (List.mem_append_left _ hq) (hs.1 ▸ hpt) ?_ ?_
      · rw [hs.2.2.1, hx]; rfl
      · rw [hs.2.2.2, hy]; rfl
    · rcases hblue p hp hpt a b hx hy with ⟨q, hq, hs⟩ | hr
      · refine Graph.netT_reach_of_mem _ _ _ (List.mem_append_left _ hq) (hs.1 ▸ hpt) ?_ ?_
        · rw [hs.2.2.1, hx]; rfl
        · rw [hs.2.2.2, hy]; rfl
      · exact hr

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
    Γ.DCS .plus := by
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

/-- A doubly connected structure with blue charge `plus` gives the doubly connected property. -/
private theorem Graph.DCT.doublyConnected {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT .plus L) : Γ.DoublyConnected := by
  obtain ⟨cs, co⟩ := Γ
  obtain rfl : cs = L.map Prod.fst := h.map_fst.symm
  have hL : ∀ i : Fin (L.map Prod.fst).length, i.1 < L.length := fun i => by
    simpa using i.2
  let black : Finset (Fin (L.map Prod.fst).length) :=
    Finset.univ.filter fun i => (L[i.1]'(hL i)).2 = some false
  let blue : Finset (Fin (L.map Prod.fst).length) :=
    Finset.univ.filter fun i => (L[i.1]'(hL i)).2 = some true
  have hnet : ∀ (B : Finset (Fin (L.map Prod.fst).length)) (t : Bool),
      (∀ i : Fin (L.map Prod.fst).length, i ∈ B ↔ (L[i.1]'(hL i)).2 = some t) →
      (Graph.mk (L.map Prod.fst) co).net B = (Graph.mk (L.map Prod.fst) co).netT L t := by
    intro B t hB
    unfold Graph.net Graph.netT
    congr 1
    funext a b
    refine propext (or_congr Iff.rfl ?_)
    constructor
    · rintro ⟨i, hi, hx, hy⟩
      exact ⟨_, List.getElem_mem _, (hB i).1 hi, by simpa using hx, by simpa using hy⟩
    · rintro ⟨p, hp, ht, hx, hy⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
      exact ⟨⟨i, by simpa using hi⟩, (hB _).2 ht, by simpa using hx, by simpa using hy⟩
  refine ⟨black, blue, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hj
    simp only [black, blue, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rw [hi] at hj
    exact absurd hj (by simp)
  · intro i hi
    simp only [black, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa using h.black _ (List.getElem_mem _) hi
  · intro i hi
    simp only [blue, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have := h.blue _ (List.getElem_mem _) hi
    rw [Kind.blueC_plus] at this
    simpa using this
  · rw [Graph.Spans, hnet black false]
    · exact h.spanBlack
    · intro i
      simp [black]
  · rw [Graph.Spans, hnet blue true]
    · exact h.spanBlue
    · intro i
      simp [blue]

private theorem Kind.conj_isDiffusive (κ : Kind) : κ.conj.isDiffusive = κ.isDiffusive := by
  cases κ with
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem Kind.conj_joinsMol (κ : Kind) : κ.conj.joinsMol = κ.joinsMol := by
  cases κ with
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem Kind.conj_blueC (bc : Charge) (κ : Kind) :
    κ.conj.blueC bc.flip = κ.blueC bc := by
  cases κ with
  | G c => cases c <;> cases bc <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

/-- Complex conjugation exchanges the blue charge: a doubly connected structure with blue charge
`bc` on `Γ` gives one with blue charge `bc.flip` on `Γ.conj`. -/
private theorem Graph.DCS.conj {bc : Charge} {Γ : Graph k n} (h : Γ.DCS bc) :
    Γ.conj.DCS bc.flip := by
  obtain ⟨L, hL⟩ := h
  let cj : TC k n → TC k n := fun p => ({ p.1 with kind := p.1.kind.conj }, p.2)
  have hmol : Γ.conj.molGraph = Γ.molGraph := by
    unfold Graph.molGraph
    congr 1
    funext u v
    refine propext ⟨?_, ?_⟩
    · rintro ⟨c, hc, hj, hx, hy⟩
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      exact ⟨c₀, hc₀, by simpa [Kind.conj_joinsMol] using hj, hx, hy⟩
    · rintro ⟨c, hc, hj, hx, hy⟩
      exact ⟨{ c with kind := c.kind.conj }, List.mem_map_of_mem hc,
        by simpa [Kind.conj_joinsMol] using hj, hx, hy⟩
  have hsame : ∀ u v, Γ.conj.SameMol u v ↔ Γ.SameMol u v := by
    intro u v
    unfold Graph.SameMol
    rw [hmol]
  have hnet : ∀ t, Γ.conj.netT (L.map cj) t = Γ.netT L t := by
    intro t
    unfold Graph.netT
    congr 1
    funext a b
    refine propext (or_congr (hsame _ _) ?_)
    constructor
    · rintro ⟨p, hp, ht, hx, hy⟩
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact ⟨p₀, hp₀, ht, hx, hy⟩
    · rintro ⟨p, hp, ht, hx, hy⟩
      exact ⟨cj p, List.mem_map_of_mem hp, ht, hx, hy⟩
  refine ⟨L.map cj, ?_, ?_, ?_, ?_, ?_⟩
  · have := hL.map_fst
    simp only [Graph.conj, ← this, List.map_map]
    rfl
  · intro p hp ht
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
    simpa [cj, Kind.conj_isDiffusive] using hL.black p₀ hp₀ ht
  · intro p hp ht
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
    simpa [cj, Kind.conj_isDiffusive, Kind.conj_blueC] using hL.blue p₀ hp₀ ht
  · rw [hnet]
    exact hL.spanBlack
  · rw [hnet]
    exact hL.spanBlue

/-- A doubly connected structure with blue charge `plus` gives the doubly connected property. -/
private theorem Graph.DCS.doublyConnected {Γ : Graph k n} (h : Γ.DCS .plus) :
    Γ.DoublyConnected := by
  obtain ⟨L, hL⟩ := h
  exact hL.doublyConnected

/-- A tagged component of `L` has neither the kind `xdot` nor a weight kind if it is tagged
or joins molecules: its kind is diffusive, blue or joins molecules. -/
private theorem Graph.DCT.kind_of_tag {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {p : TC k n} (hp : p ∈ L) (ht : p.2 ≠ none) :
    p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true := by
  rcases hp2 : p.2 with _ | _ | _
  · exact absurd hp2 ht
  · exact Or.inl (h.black p hp hp2)
  · exact h.blue p hp hp2

/-- Removing the `×`-dotted components of a graph and adding any components keeps a doubly
connected structure. -/
private theorem Graph.DCS.filter_append {bc : Charge} {Γ : Graph k n} (h : Γ.DCS bc)
    {Γ' : Graph k n} (P : Comp (Atom k n) → Bool) (extra : List (Comp (Atom k n)))
    (hP : ∀ c, c.kind ≠ .xdot → P c = true) (hΓ : Γ'.comps = Γ.comps.filter P ++ extra) :
    Γ'.DCS bc := by
  obtain ⟨L, hL⟩ := h
  let L' : List (TC k n) := L.filter (fun p => P p.1) ++ extra.map fun c => (c, none)
  have hret : ∀ p ∈ L, p.2 ≠ none ∨ p.1.kind.joinsMol = true → p ∈ L.filter (fun p => P p.1) := by
    intro p hp hpp
    refine List.mem_filter.2 ⟨hp, ?_⟩
    apply hP
    rcases hpp with hpp | hpp
    · rcases hL.kind_of_tag hp hpp with h1 | h1 <;> intro hx <;> rw [hx] at h1 <;>
        simp [Kind.isDiffusive, Kind.blueC] at h1
    · intro hx; rw [hx] at hpp; simp [Kind.joinsMol] at hpp
  have hid : (Sum.map id (id : Fin n → Fin n) : Atom k n → Atom k n) = id := by
    funext u; rcases u with a | a <;> rfl
  refine ⟨L', ?_⟩
  refine hL.transport id L' ?_ ?_ ?_ ?_ ?_ (fun w => ⟨w, Or.inl rfl⟩)
  · simp only [L', List.map_append, List.map_map, hΓ]
    congr 1
    · rw [← hL.map_fst, List.filter_map]
      rfl
    · simp [Function.comp_def]
  · intro q hq hqt
    rcases List.mem_append.1 hq with hq | hq
    · exact hL.black q (List.mem_filter.1 hq).1 hqt
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
      simp at hqt
  · intro q hq hqt
    rcases List.mem_append.1 hq with hq | hq
    · exact hL.blue q (List.mem_filter.1 hq).1 hqt
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
      simp at hqt
  · intro c hc hk
    rw [hid]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hL.map_fst ▸ hc)
    have : p.1 ∈ Γ'.comps := by
      rw [hΓ]
      exact List.mem_append_left _ (List.mem_filter.2
        ⟨hc, (List.mem_filter.1 (hret p hp (Or.inr hk))).2⟩)
    exact Graph.molReach_of_comp this hk
  · intro t p hp hpt a b hx hy
    have hmem : p ∈ L' := List.mem_append_left _ (hret p hp (Or.inl (by rw [hpt]; simp)))
    simp only [id] at *
    exact Graph.netT_reach_of_mem _ _ _ hmem hpt hx hy

/-! ## `O_merge` -/

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
private def mergeC (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

/-- The atom map of `O_merge` sends internal atoms onto internal atoms and fixes external ones,
atoms with the same representative have the same image, and the components are the images. -/
private theorem mergeT_struct {Γ : Graph k n} {t : Tracked k n} (ht : Γ.mergeT = some t) :
    ∃ (rep : Atom k n → Atom k n) (φ : Fin n → Fin t.nOut), t.f = Sum.map id φ ∧
      Function.Surjective φ ∧ (∀ i j, rep (Sum.inr i) = rep (Sum.inr j) → φ i = φ j) ∧
      t.g.comps = Γ.comps.filterMap (mergeC rep t.f) := by
  unfold Graph.mergeT at ht
  dsimp only at ht
  split_ifs at ht
  obtain rfl := Option.some.inj ht
  refine ⟨blockRep (dotBlocks (allAtoms k n) Γ.comps), fun i => ⟨_, List.idxOf_lt_length_of_mem
    (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩, ?_, ?_, ?_, rfl⟩
  · funext u
    rcases u with a | i <;> rfl
  · intro j
    have hj := List.getElem_mem j.2
    obtain ⟨i, -, hi⟩ := List.mem_map.1 (List.mem_dedup.1 hj)
    refine ⟨i, Fin.ext ?_⟩
    change List.idxOf _ _ = j.1
    rw [hi]
    exact (List.nodup_dedup _).idxOf_getElem j.1 j.2
  · intro i j hij
    refine Fin.ext ?_
    change List.idxOf _ _ = List.idxOf _ _
    rw [hij]

private theorem map_fst_filterMap {α β γ : Type*} (L : List (α × γ)) (F : α → Option β)
    (τ : α × γ → β → γ) :
    (L.filterMap fun p => (F p.1).map fun c' => (c', τ p c')).map Prod.fst =
      (L.map Prod.fst).filterMap F := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rcases hF : F p.1 with _ | c' <;> simp [hF, ih]

/-- `O_merge` keeps a doubly connected structure and sends internal atoms to internal atoms. -/
private theorem Graph.DCS.mergeT {bc : Charge} {Γ : Graph k n} (h : Γ.DCS bc)
    {t : Tracked k n} (ht : Γ.mergeT = some t) :
    t.g.DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨rep, φ, hf, hsurj, hrep, hcomps⟩ := mergeT_struct ht
  have hint : ∀ u, (t.f u).isRight = u.isRight := by
    intro u
    rw [hf]
    rcases u with a | i <;> rfl
  refine ⟨?_, hint⟩
  let τ : TC k n → Comp (Atom k t.nOut) → Option Bool :=
    fun p c' => if c'.kind = p.1.kind then p.2 else none
  let L' : List (TC k t.nOut) :=
    L.filterMap fun p => (mergeC rep t.f p.1).map fun c' => (c', τ p c')
  have hmem : ∀ q ∈ L', ∃ p ∈ L, mergeC rep t.f p.1 = some q.1 ∧ q.2 = τ p q.1 := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := List.mem_filterMap.1 hq
    rcases hF : mergeC rep t.f p.1 with _ | c'
    · rw [hF] at hpq; simp at hpq
    · rw [hF] at hpq
      simp only [Option.map_some, Option.some.injEq] at hpq
      subst hpq
      exact ⟨p, hp, hF, rfl⟩
  refine ⟨L', ?_⟩
  refine hL.transport φ L' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcomps, ← hL.map_fst]
    exact map_fst_filterMap L (mergeC rep t.f) τ
  · intro q hq hqt
    obtain ⟨p, hp, -, hq2⟩ := hmem q hq
    have hk : q.1.kind = p.1.kind := by
      by_contra hne
      rw [hq2] at hqt
      simp [τ, hne] at hqt
    rw [hq2] at hqt
    simp only [τ, hk, ite_true] at hqt
    rw [hk]
    exact hL.black p hp hqt
  · intro q hq hqt
    obtain ⟨p, hp, -, hq2⟩ := hmem q hq
    have hk : q.1.kind = p.1.kind := by
      by_contra hne
      rw [hq2] at hqt
      simp [τ, hne] at hqt
    rw [hq2] at hqt
    simp only [τ, hk, ite_true] at hqt
    rw [hk]
    exact hL.blue p hp hqt
  · intro c hc hk
    rw [← hf]
    by_cases h1 : (c.kind == .dot && t.f c.x == t.f c.y) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1
      rw [h1.2]
    · have h2 : (c.kind.isSolid && rep c.x == rep c.y) = false := by
        have : c.kind.isSolid = false := by
          generalize c.kind = κ at hk
          cases κ <;> simp_all [Kind.joinsMol, Kind.isSolid]
        simp [this]
      have hc' : c.map t.f ∈ t.g.comps := by
        rw [hcomps]
        refine List.mem_filterMap.2 ⟨c, hc, ?_⟩
        simp [mergeC, h1, h2]
      exact Graph.molReach_of_comp hc' hk
  · intro t' p hp hpt a b hx hy
    have hkind : p.1.kind.isDiffusive = true ∨ p.1.kind.blueC bc = true :=
      hL.kind_of_tag hp (by rw [hpt]; simp)
    have hnd : p.1.kind ≠ .dot := by
      intro hd
      rw [hd] at hkind
      simp [Kind.isDiffusive, Kind.blueC] at hkind
    by_cases h2 : (p.1.kind.isSolid && rep p.1.x == rep p.1.y) = true
    · have hr : rep (Sum.inr a) = rep (Sum.inr b) := by
        simp only [Bool.and_eq_true, beq_iff_eq] at h2
        rw [hx, hy] at h2
        exact h2.2
      rw [hrep a b hr]
    · have hm : mergeC rep t.f p.1 = some (p.1.map t.f) := by
        simp [mergeC, hnd, h2]
      have hq : (p.1.map t.f, τ p (p.1.map t.f)) ∈ L' :=
        List.mem_filterMap.2 ⟨p, hp, by simp [hm]⟩
      have hτ : τ p (p.1.map t.f) = p.2 := by simp [τ, Comp.map]
      refine Graph.netT_reach_of_mem _ _ _ hq (hτ ▸ hpt) ?_ ?_
      · change t.f p.1.x = _
        rw [hx, hf]; rfl
      · change t.f p.1.y = _
        rw [hy, hf]; rfl
  · intro w
    obtain ⟨a, rfl⟩ := hsurj w
    exact ⟨a, Or.inl rfl⟩

/-- The dotted edge choices keep a doubly connected structure. -/
private theorem Graph.DCS.dotChoice {bc : Charge} {Γ : Graph k n} (h : Γ.DCS bc)
    (SP A : List (Atom k n × Atom k n × Bool)) : (Γ.dotChoice SP A).DCS bc := by
  refine h.filter_append _ _ ?_ rfl
  intro c hc
  simp [hc]

/-- A tracked graph with the identity map. -/
private theorem Tracked.self_dcs {bc : Charge} {Γ : Graph k n} (h : Γ.DCS bc) :
    (Tracked.self Γ).g.DCS bc ∧ ∀ u, ((Tracked.self Γ).f u).isRight = u.isRight :=
  ⟨h, fun _ => rfl⟩

/-- `O_dot` keeps a doubly connected structure and sends internal atoms to internal atoms. -/
private theorem oDotT_dcs {bc : Charge} {Γ : Graph k n} (h : Γ.DCS bc) :
    ∀ t ∈ oDotT Γ, t.g.DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight := by
  intro t ht
  unfold oDotT at ht
  dsimp only at ht
  split_ifs at ht
  · obtain rfl := List.mem_singleton.1 ht
    exact Tracked.self_dcs h
  · obtain rfl := List.mem_singleton.1 ht
    exact Tracked.self_dcs h
  · obtain ⟨A, -, hA⟩ := List.mem_filterMap.1 ht
    exact (h.dotChoice _ A).mergeT hA

/-! ## Operations on tagged lists -/

/-- The tagged components moved to a graph with `j` more internal atoms. -/
private def liftT (j : ℕ) (L : List (TC k n)) : List (TC k (n + j)) :=
  L.map fun p => (p.1.map (liftA j), p.2)

/-- New components, tagged blue exactly when their kind is blue. -/
private def newT (bc : Charge) (cs : List (Comp (Atom k m))) : List (TC k m) :=
  cs.map fun c => (c, if c.kind.blueC bc then some true else none)

private theorem liftT_map_fst (j : ℕ) (L : List (TC k n)) :
    (liftT j L).map Prod.fst = liftCs j (L.map Prod.fst) := by
  simp [liftT, liftCs, Function.comp_def]

private theorem newT_map_fst (bc : Charge) (cs : List (Comp (Atom k m))) :
    (newT bc cs).map Prod.fst = cs := by
  simp [newT, Function.comp_def]

private theorem newT_black {bc : Charge} {cs : List (Comp (Atom k m))} {q : TC k m}
    (hq : q ∈ newT bc cs) (h : q.2 = some false) : q.1.kind.isDiffusive = true := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
  simp only at h
  split_ifs at h
  simp at h

private theorem newT_blue {bc : Charge} {cs : List (Comp (Atom k m))} {q : TC k m}
    (hq : q ∈ newT bc cs) (h : q.2 = some true) :
    q.1.kind.isDiffusive = true ∨ q.1.kind.blueC bc = true := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
  simp only at h ⊢
  split_ifs at h with hb
  exact Or.inr hb

private theorem newT_mem {bc : Charge} {cs : List (Comp (Atom k m))} {c : Comp (Atom k m)}
    (hc : c ∈ cs) (hb : c.kind.blueC bc = true) : (c, some true) ∈ newT bc cs :=
  List.mem_map.2 ⟨c, hc, by simp [hb]⟩

private theorem sim_liftT (j : ℕ) (p : TC k n) : Sim j p (p.1.map (liftA j), p.2) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A tagged component not kept in a new graph is compensated there: it is neither joining
molecules nor black, and if it is blue its ends are joined in the new blue net. -/
private def Compensated (j : ℕ) (Γ' : Graph k (n + j)) (L' : List (TC k (n + j)))
    (p : TC k n) : Prop :=
  (p.1.kind.joinsMol = false ∧ p.2 ≠ some false) ∧
    (p.2 = some true → ∀ a b, p.1.x = Sum.inr a → p.1.y = Sum.inr b →
      (Γ'.netT L' true).Reachable (Fin.castAdd j a) (Fin.castAdd j b))

/-! ## Index lists -/

section Lists

variable {α β : Type*}

private theorem eraseIdxs_map (f : α → β) (is : List ℕ) (l : List α) :
    eraseIdxs is (l.map f) = (eraseIdxs is l).map f := by
  simp [eraseIdxs, List.zipIdx_map, List.filter_map, List.map_map, Function.comp_def]

private theorem pickIdxs_map (f : α → β) (is : List ℕ) (l : List α) :
    pickIdxs is (l.map f) = (pickIdxs is l).map f := by
  simp [pickIdxs, List.zipIdx_map, List.filter_map, List.map_map, Function.comp_def]

private theorem mem_eraseIdxs {is : List ℕ} {l : List α} {p : α} :
    p ∈ eraseIdxs is l ↔ ∃ i, ∃ h : i < l.length, l[i] = p ∧ i ∉ is := by
  unfold eraseIdxs
  constructor
  · intro hp
    obtain ⟨⟨a, i⟩, hmem, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hmem
    rw [List.mem_zipIdx_iff_getElem?] at h1
    have hi : i < l.length := (List.getElem?_eq_some_iff.1 h1).1
    refine ⟨i, hi, ?_, ?_⟩
    · exact (List.getElem?_eq_some_iff.1 h1).2
    · simpa using h2
  · rintro ⟨i, hi, rfl, hn⟩
    refine List.mem_map.2 ⟨(l[i], i), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
    · rw [List.mem_zipIdx_iff_getElem?]
      simp
    · simpa using hn

private theorem mem_pickIdxs {is : List ℕ} {l : List α} {p : α} :
    p ∈ pickIdxs is l ↔ ∃ i ∈ is, ∃ h : i < l.length, l[i] = p := by
  unfold pickIdxs
  constructor
  · intro hp
    obtain ⟨⟨a, i⟩, hmem, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hmem
    rw [List.mem_zipIdx_iff_getElem?] at h1
    have hi : i < l.length := (List.getElem?_eq_some_iff.1 h1).1
    refine ⟨i, by simpa using h2, hi, ?_⟩
    exact (List.getElem?_eq_some_iff.1 h1).2
  · rintro ⟨i, hn, hi, rfl⟩
    refine List.mem_map.2 ⟨(l[i], i), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
    · rw [List.mem_zipIdx_iff_getElem?]
      simp
    · simpa using hn

private theorem mem_eraseIdxs_subset {is : List ℕ} {l : List α} {p : α}
    (hp : p ∈ eraseIdxs is l) : p ∈ l := by
  obtain ⟨i, hi, rfl, -⟩ := mem_eraseIdxs.1 hp
  exact List.getElem_mem hi

private theorem mem_pickIdxs_subset {is : List ℕ} {l : List α} {p : α}
    (hp : p ∈ pickIdxs is l) : p ∈ l := by
  obtain ⟨i, -, hi, rfl⟩ := mem_pickIdxs.1 hp
  exact List.getElem_mem hi

/-- Every element is kept by `eraseIdxs` or sits at an erased index. -/
private theorem mem_eraseIdxs_or {is : List ℕ} {l : List α} {p : α} (hp : p ∈ l) :
    p ∈ eraseIdxs is l ∨ ∃ i ∈ is, ∃ h : i < l.length, l[i] = p := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  by_cases h : i ∈ is
  · exact Or.inr ⟨i, h, hi, rfl⟩
  · exact Or.inl (mem_eraseIdxs.2 ⟨i, hi, rfl, h⟩)

/-- Every element is kept by `eraseIdx` or is the erased one. -/
private theorem mem_eraseIdx_or {l : List α} {i : ℕ} {p : α} (hp : p ∈ l) :
    p ∈ l.eraseIdx i ∨ ∃ h : i < l.length, p = l[i] := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hp
  by_cases h : j = i
  · subst h; exact Or.inr ⟨hj, rfl⟩
  · exact Or.inl (List.mem_eraseIdx_iff_getElem.2 ⟨j, hj, h, rfl⟩)

private theorem mem_eraseIdx_subset {l : List α} {i : ℕ} {p : α} (hp : p ∈ l.eraseIdx i) :
    p ∈ l :=
  (List.eraseIdx_sublist l i).subset hp

end Lists

section Edges

variable {k n : ℕ}

private theorem mem_dTerms {V : Type*} [DecidableEq V] {p q : V} {cs : List (Comp V)}
    {d : List (Comp V)} : d ∈ dTerms p q cs ↔ ∃ i : Fin cs.length, ∃ ps,
      cs[i].dPieces p q = some ps ∧ d = cs.eraseIdx i ++ ps := by
  unfold dTerms
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, -, hi⟩
    obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hi
    exact ⟨i, ps, hps, rfl⟩
  · rintro ⟨i, ps, hps, rfl⟩
    exact ⟨i, List.mem_finRange i, Option.map_eq_some_iff.2 ⟨ps, hps, rfl⟩⟩

private theorem mem_edgeIdx {Γ : Graph k n} {x : Atom k n} {ch : Charge} {out : Bool} {i : ℕ}
    (h : i ∈ Γ.edgeIdx x ch out) : ∃ hi : i < Γ.comps.length, Γ.comps[i].kind = .G ch ∧
      (out = true → Γ.comps[i].x = x ∧ Γ.comps[i].y ≠ x) ∧
      (out = false → Γ.comps[i].y = x ∧ Γ.comps[i].x ≠ x) := by
  unfold Graph.edgeIdx at h
  obtain ⟨⟨c, j⟩, hmem, rfl⟩ := List.mem_map.1 h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hmem
  rw [List.mem_zipIdx_iff_getElem?] at h1
  obtain ⟨hj, hc⟩ := List.getElem?_eq_some_iff.1 h1
  dsimp only at hj hc h2 ⊢
  refine ⟨hj, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  subst hc
  refine ⟨h2.1, ?_, ?_⟩
  · intro ho
    simp only [ho, ite_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2
    exact h2.2
  · intro ho
    simp only [ho, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq] at h2
    exact h2.2

/-- The kinds with partial derivatives are solid edges and weights. -/
private theorem kind_of_dPieces {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) :
    ∃ ch, c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch := by
  cases hk : c.kind <;> simp_all [Comp.dPieces]

end Edges

/-- A local expansion without a derivative: the components `S` of `L` are kept (moved to the new
atoms), the other components are compensated, and `cs` are new components. -/
private theorem Graph.DCT.shapeE {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)} (S : List (TC k n))
    (cs : List (Comp (Atom k (n + j))))
    (hmap : (liftT j S ++ newT bc cs).map Prod.fst = Γ'.comps) (hS : ∀ q ∈ S, q ∈ L)
    (hcov : ∀ p ∈ L, p ∉ S → Compensated j Γ' (liftT j S ++ newT bc cs) p)
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) :
    Γ'.DCT bc (liftT j S ++ newT bc cs) := by
  refine h.extend (liftT j S) (newT bc cs) hmap ?_ (fun q hq => newT_black hq)
    (fun q hq => newT_blue hq) ?_ ?_ hnew
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨p, hS p hp, sim_liftT j p⟩
  · intro p hp hpp
    by_cases hpS : p ∈ S
    · exact ⟨_, List.mem_map_of_mem hpS, sim_liftT j p⟩
    · obtain ⟨⟨h1, h2⟩, -⟩ := hcov p hp hpS
      rcases hpp with hpp | hpp
      · rw [h1] at hpp; exact absurd hpp (by simp)
      · exact absurd hpp h2
  · intro p hp hpt a b hx hy
    by_cases hpS : p ∈ S
    · exact Or.inl ⟨_, List.mem_map_of_mem hpS, sim_liftT j p⟩
    · exact Or.inr ((hcov p hp hpS).2 hpt a b hx hy)

/-- If the pieces of a partial derivative of a blue solid edge `c` at joined atoms `p`, `q` are
in the blue net, the ends of `c` are joined in the blue net. -/
private theorem deriv_reach {bc : Charge} {Γ' : Graph k m} {L' : List (TC k m)}
    {c : Comp (Atom k m)} {u v p q : Fin m} (hk : c.kind = .G bc) (hx : c.x = Sum.inr u)
    (hy : c.y = Sum.inr v) {ps : List (Comp (Atom k m))}
    (hps : c.dPieces (Sum.inr p) (Sum.inr q) = some ps)
    (hL' : ∀ pc ∈ ps, pc.kind.blueC bc = true → (pc, some true) ∈ L')
    (hlink : Γ'.SameMol (Sum.inr p) (Sum.inr q)) : (Γ'.netT L' true).Reachable u v := by
  have hsolid : ∀ (ch : Charge) (a b : Fin m), ch = bc →
      solidC ch (Sum.inr a : Atom k m) (Sum.inr b) ∈ ps → (Γ'.netT L' true).Reachable a b := by
    intro ch a b hch hmem
    by_cases hab : a = b
    · rw [hab]
    · have hne : (Sum.inr a : Atom k m) ≠ Sum.inr b := by simpa using hab
      have hs : solidC ch (Sum.inr a : Atom k m) (Sum.inr b) =
          mkC (.G ch) (Sum.inr a) (Sum.inr b) := by
        simp [solidC, hne]
      rw [hs] at hmem
      have hb : (mkC (.G ch) (Sum.inr a : Atom k m) (Sum.inr b)).kind.blueC bc = true := by
        simp [mkC, Kind.blueC, hch]
      exact Graph.netT_reach_of_mem Γ' L' true (hL' _ hmem hb) rfl rfl rfl
  have hw : c.kind.isWeight = false := by rw [hk]; rfl
  unfold Comp.dPieces at hps
  rw [hk, hx, hy] at hps
  cases bc
  · simp only [Option.some.injEq] at hps
    subst hps
    exact ((hsolid .plus u p rfl (List.mem_cons_self ..)).trans
      (Graph.netT_reach_of_sameMol _ _ _ hlink)).trans
      (hsolid .plus q v rfl (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · simp only [Option.some.injEq] at hps
    subst hps
    exact ((hsolid .minus u q rfl (List.mem_cons_self ..)).trans
      (Graph.netT_reach_of_sameMol _ _ _ ((Graph.sameMol_equivalence Γ').symm hlink))).trans
      (hsolid .minus p v rfl (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-- A local expansion with one partial derivative: the component `S[i']` of `S` is replaced by its
pieces `ps` at the joined atoms `p`, `q`; the components `S₀` and the other components of `S` are
kept; the other components of `L` are compensated; `cs` are further new components. -/
private theorem Graph.DCT.shapeD {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)} (S₀ S : List (TC k n)) (i' : ℕ)
    (hi' : i' < S.length) (p q : Fin (n + j)) (ps cs : List (Comp (Atom k (n + j))))
    (hps : (S[i'].1.map (liftA j)).dPieces (Sum.inr p) (Sum.inr q) = some ps)
    (hmap : (liftT j (S₀ ++ S.eraseIdx i') ++ newT bc (ps ++ cs)).map Prod.fst = Γ'.comps)
    (hS₀ : ∀ r ∈ S₀, r ∈ L) (hS : ∀ r ∈ S, r ∈ L) (hlink : Γ'.SameMol (Sum.inr p) (Sum.inr q))
    (hcov : ∀ r ∈ L, r ∉ S₀ → r ∉ S →
      Compensated j Γ' (liftT j (S₀ ++ S.eraseIdx i') ++ newT bc (ps ++ cs)) r)
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) :
    Γ'.DCT bc (liftT j (S₀ ++ S.eraseIdx i') ++ newT bc (ps ++ cs)) := by
  obtain ⟨ch, hch⟩ := kind_of_dPieces hps
  have hkS : S[i'].1.kind = .G ch ∨ S[i'].1.kind = .weight ch ∨ S[i'].1.kind = .light ch := hch
  have hnotJ : S[i'].1.kind.joinsMol = false := by
    rcases hkS with hk | hk | hk <;> simp [hk, Kind.joinsMol]
  have hnotD : S[i'].1.kind.isDiffusive = false := by
    rcases hkS with hk | hk | hk <;> simp [hk, Kind.isDiffusive]
  refine h.extend (liftT j (S₀ ++ S.eraseIdx i')) (newT bc (ps ++ cs)) hmap ?_
    (fun q hq => newT_black hq) (fun q hq => newT_blue hq) ?_ ?_ hnew
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    refine ⟨r', ?_, sim_liftT j r'⟩
    rcases List.mem_append.1 hr' with h1 | h1
    · exact hS₀ r' h1
    · exact hS r' (mem_eraseIdx_subset h1)
  · intro r hr hrr
    by_cases h0 : r ∈ S₀
    · exact ⟨_, List.mem_map_of_mem (List.mem_append_left _ h0), sim_liftT j r⟩
    by_cases h1 : r ∈ S
    · rcases mem_eraseIdx_or (i := i') h1 with h2 | ⟨_, h2⟩
      · exact ⟨_, List.mem_map_of_mem (List.mem_append_right _ h2), sim_liftT j r⟩
      · exfalso
        rcases hrr with hrr | hrr
        · rw [h2] at hrr; rw [hnotJ] at hrr; exact absurd hrr (by simp)
        · have := h.black r hr hrr
          rw [h2, hnotD] at this
          exact absurd this (by simp)
    · obtain ⟨⟨c1, c2⟩, -⟩ := hcov r hr h0 h1
      rcases hrr with hrr | hrr
      · rw [c1] at hrr; exact absurd hrr (by simp)
      · exact absurd hrr c2
  · intro r hr hrt a b hx hy
    by_cases h0 : r ∈ S₀
    · exact Or.inl ⟨_, List.mem_map_of_mem (List.mem_append_left _ h0), sim_liftT j r⟩
    by_cases h1 : r ∈ S
    · rcases mem_eraseIdx_or (i := i') h1 with h2 | ⟨_, h2⟩
      · exact Or.inl ⟨_, List.mem_map_of_mem (List.mem_append_right _ h2), sim_liftT j r⟩
      · right
        have hb := h.blue r hr hrt
        rw [h2, hnotD] at hb
        have hbk : S[i'].1.kind = .G bc := by
          rcases hb with hb | hb
          · exact absurd hb (by simp)
          · rcases hkS with hk | hk | hk
            · rw [hk] at hb ⊢
              exact congrArg Kind.G (of_decide_eq_true hb)
            · rw [hk] at hb; exact absurd hb (by simp [Kind.blueC])
            · rw [hk] at hb; exact absurd hb (by simp [Kind.blueC])
        refine deriv_reach (u := Fin.castAdd j a) (v := Fin.castAdd j b)
          (c := S[i'].1.map (liftA j)) hbk ?_ ?_ hps ?_ hlink
        · change liftA j S[i'].1.x = _
          rw [← h2, hx]; rfl
        · change liftA j S[i'].1.y = _
          rw [← h2, hy]; rfl
        · intro pc hpc hb
          exact List.mem_append_right _ (newT_mem (List.mem_append_left _ hpc) hb)
    · exact Or.inr ((hcov r hr h0 h1).2 hrt a b hx hy)

/-- A component is inert for the nets: it is neither diffusive nor blue, and does not join
molecules. -/
private def Inert (bc : Charge) (c : Comp (Atom k n)) : Prop :=
  c.kind.isDiffusive = false ∧ c.kind.blueC bc = false ∧ c.kind.joinsMol = false

private theorem Graph.DCT.compensated_of_inert {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {j : ℕ} (Γ' : Graph k (n + j)) (L' : List (TC k (n + j))) {p : TC k n}
    (hp : p ∈ L) (hi : Inert bc p.1) : Compensated j Γ' L' p := by
  obtain ⟨h1, h2, h3⟩ := hi
  refine ⟨⟨h3, ?_⟩, ?_⟩
  · intro hp2
    have := h.black p hp hp2
    rw [h1] at this
    exact absurd this (by simp)
  · intro hp2
    have := h.blue p hp hp2
    rw [h1, h2] at this
    exact absurd this (by simp)

private theorem Graph.DCT.addAtoms {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)} (cs : List (Comp (Atom k (n + j))))
    (hΓ' : Γ'.comps = liftCs j (L.map Prod.fst) ++ cs)
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) : Γ'.DCS bc := by
  refine ⟨liftT j L ++ newT bc cs, h.shapeE L cs ?_ (fun q hq => hq) (fun p hp hpS => absurd hp hpS)
    hnew⟩
  rw [hΓ']
  simp [liftT_map_fst, newT_map_fst]

/-- A new atom with `w.val ≥ n` joined to the image of an internal atom gives the covering
hypothesis. -/
private theorem hnew_of {Γ' : Graph k (n + j)} (x₀ : Fin n)
    (h : ∀ w : Fin (n + j), n ≤ w.val → Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j x₀))) :
    ∀ w : Fin (n + j), ∃ a : Fin n, Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a)) := by
  intro w
  by_cases hw : w.val < n
  · exact ⟨⟨w.val, hw⟩, Or.inl (by simp)⟩
  · exact ⟨x₀, h w (not_lt.1 hw)⟩

private theorem Graph.sameMol_of_waved {Γ : Graph k n} {c : Comp (Atom k n)} {u v : Fin n}
    (hc : c ∈ Γ.comps) (hk : c.kind.joinsMol = true) (hx : c.x = Sum.inr u)
    (hy : c.y = Sum.inr v) : Γ.SameMol (Sum.inr u) (Sum.inr v) := by
  have := Graph.sameMol_of_comp hc hk (by rw [hx]; rfl) (by rw [hy]; rfl)
  rwa [hx, hy] at this

/-- Covering hypothesis for one new atom joined to the image of `x` by a waved edge. -/
private theorem hnew₁ {Γ' : Graph k (n + 1)} (x₀ : Fin n)
    (h : Γ'.SameMol (Sum.inr (Fin.castAdd 1 x₀)) (newA 0)) :
    ∀ w : Fin (n + 1), ∃ a : Fin n, Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd 1 a)) := by
  refine hnew_of x₀ fun w hw => ?_
  have : w = Fin.natAdd n 0 := Fin.ext (by simp; omega)
  subst this
  exact (Graph.sameMol_equivalence Γ').symm h

/-- Covering hypothesis for two new atoms `a₂`, `b₂` with `x ~ a₂ ~ b₂`. -/
private theorem hnew₂ {Γ' : Graph k (n + 2)} (x₀ : Fin n)
    (h₁ : Γ'.SameMol (Sum.inr (Fin.castAdd 2 x₀)) (newA 0))
    (h₂ : Γ'.SameMol (newA 0) (newA 1)) :
    ∀ w : Fin (n + 2), ∃ a : Fin n, Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd 2 a)) := by
  refine hnew_of x₀ fun w hw => ?_
  have hw2 : w = Fin.natAdd n 0 ∨ w = Fin.natAdd n 1 := by
    rcases (by omega : w.val = n ∨ w.val = n + 1) with h | h
    · exact Or.inl (Fin.ext (by simp [h]))
    · exact Or.inr (Fin.ext (by simp [h]))
  rcases hw2 with rfl | rfl
  · exact (Graph.sameMol_equivalence Γ').symm h₁
  · exact (Graph.sameMol_equivalence Γ').symm ((Graph.sameMol_equivalence Γ').trans h₁ h₂)

/-- Components with the same kind and the same ends. -/
private def SimC (c d : Comp (Atom k m)) : Prop := c.kind = d.kind ∧ c.x = d.x ∧ c.y = d.y

private theorem forall₂_exists_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {a}, a ∈ l → ∃ b ∈ l', R a b
  | _, _, .cons h₁ h₂, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., h₁⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_exists_left h₂ ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

private theorem forall₂_exists_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {b}, b ∈ l' → ∃ a ∈ l, R a b
  | _, _, .cons h₁ h₂, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., h₁⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_exists_right h₂ hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- A doubly connected structure is kept when components are replaced by components with the same
kinds and ends. -/
private theorem Graph.DCS.sim {bc : Charge} {Γ Γ' : Graph k n} (h : Γ.DCS bc)
    (hs : List.Forall₂ SimC Γ.comps Γ'.comps) : Γ'.DCS bc := by
  obtain ⟨L, hL⟩ := h
  have key : ∀ (cs cs' : List (Comp (Atom k n))), List.Forall₂ SimC cs cs' →
      ∀ L : List (TC k n), L.map Prod.fst = cs → ∃ L' : List (TC k n), L'.map Prod.fst = cs' ∧
        List.Forall₂ (fun p q => q.2 = p.2 ∧ SimC p.1 q.1) L L' := by
    intro cs cs' hs
    induction hs with
    | nil =>
      intro L hL
      obtain rfl : L = [] := List.map_eq_nil_iff.1 hL
      exact ⟨[], rfl, List.Forall₂.nil⟩
    | @cons c d cs cs' hr _ ih =>
      intro L hL
      obtain ⟨p, L₀, rfl⟩ : ∃ p L₀, L = p :: L₀ := by
        cases L with
        | nil => simp at hL
        | cons p L₀ => exact ⟨p, L₀, rfl⟩
      simp only [List.map_cons, List.cons.injEq] at hL
      obtain ⟨L', h1, h2⟩ := ih L₀ hL.2
      refine ⟨(d, p.2) :: L', ?_, List.Forall₂.cons ⟨rfl, hL.1 ▸ hr⟩ h2⟩
      simp [h1]
  obtain ⟨L', hmap, hrel⟩ := key _ _ hs L hL.map_fst
  have hid : (Sum.map id (id : Fin n → Fin n) : Atom k n → Atom k n) = id := by
    funext u; rcases u with a | a <;> rfl
  refine ⟨L', hL.transport id L' hmap ?_ ?_ ?_ ?_ (fun w => ⟨w, Or.inl rfl⟩)⟩
  · intro q hq hqt
    obtain ⟨p, hp, hq2, hs⟩ := forall₂_exists_right hrel hq
    rw [← hs.1]
    exact hL.black p hp (hq2 ▸ hqt)
  · intro q hq hqt
    obtain ⟨p, hp, hq2, hs⟩ := forall₂_exists_right hrel hq
    rw [← hs.1]
    exact hL.blue p hp (hq2 ▸ hqt)
  · intro c hc hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hL.map_fst ▸ hc)
    obtain ⟨q, hq, hq2, hs⟩ := forall₂_exists_left hrel hp
    have hqc : q.1 ∈ Γ'.comps := hmap ▸ List.mem_map_of_mem hq
    rw [hid]
    simp only [id]
    rw [hs.2.1, hs.2.2]
    exact Graph.molReach_of_comp hqc (hs.1 ▸ hk)
  · intro t p hp hpt a b hx hy
    obtain ⟨q, hq, hq2, hs⟩ := forall₂_exists_left hrel hp
    exact Graph.netT_reach_of_mem _ _ _ hq (hq2 ▸ hpt) (hs.2.1 ▸ hx) (hs.2.2 ▸ hy)

/-- A doubly connected structure is kept when every component is replaced by a component with
the same kind and ends. -/
private theorem Graph.DCS.map_sim {bc : Charge} {Γ Γ' : Graph k n} (h : Γ.DCS bc)
    (F : Comp (Atom k n) → Comp (Atom k n)) (hF : ∀ c, SimC c (F c))
    (hΓ' : Γ'.comps = Γ.comps.map F) : Γ'.DCS bc :=
  h.sim (hΓ' ▸ List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun c _ => hF c))

private theorem simC_labelQ (u : Atom k n) (c : Comp (Atom k n)) : SimC c (c.labelQ u) := by
  unfold Comp.labelQ
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- Labelling the random components keeps a doubly connected structure. -/
private theorem Graph.DCS.labelQ {bc : Charge} {Γ Γ' : Graph k n} (h : Γ.DCS bc)
    (u : Atom k n) (hΓ' : Γ'.comps = Γ.comps.map (Comp.labelQ u)) : Γ'.DCS bc :=
  h.map_sim _ (simC_labelQ u) hΓ'

/-- Labelling the random components of the first part of the components keeps a doubly
connected structure when the second part has no random components. -/
private theorem Graph.DCS.labelQ_append {bc : Charge} {Γ Γ' : Graph k n} (h : Γ.DCS bc)
    (u : Atom k n) (A B : List (Comp (Atom k n))) (hB : ∀ c ∈ B, c.kind.isRandom = false)
    (hΓ : Γ.comps = A ++ B) (hΓ' : Γ'.comps = labelQs u A ++ B) : Γ'.DCS bc := by
  refine h.labelQ u ?_
  rw [hΓ, hΓ', List.map_append, labelQs]
  congr 1
  refine ((List.map_congr_left fun c hc => ?_).trans (List.map_id _)).symm
  have := hB c hc
  unfold Comp.labelQ
  simp [this]

/-- A blue solid edge `G^{ch}_{x v}` leaving `x` is replaced by `G^{ch}_{w v}` at an atom `w` joined
to `x`. -/
private theorem comp_redirect_out {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (hL : Γ.DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)} (S : List (TC k n))
    (cs : List (Comp (Atom k (n + j)))) {p : TC k n} (hp : p ∈ L) {ch : Charge}
    (hk : p.1.kind = .G ch) {x₀ : Fin n} (hx : p.1.x = Sum.inr x₀) {w : Fin (n + j)}
    (hlink : Γ'.SameMol (Sum.inr (Fin.castAdd j x₀)) (Sum.inr w))
    (hc : mkC (.G ch) (Sum.inr w) (liftA j p.1.y) ∈ cs) :
    Compensated j Γ' (liftT j S ++ newT bc cs) p := by
  refine ⟨⟨by rw [hk]; rfl, ?_⟩, ?_⟩
  · intro hp2
    have := hL.black p hp hp2
    rw [hk] at this
    exact absurd this (by simp [Kind.isDiffusive])
  · intro hpt a b hx' hy'
    have hb := hL.blue p hp hpt
    rw [hk] at hb
    have hch : ch = bc := by
      rcases hb with hb | hb
      · simp [Kind.isDiffusive] at hb
      · simpa [Kind.blueC] using hb
    subst hch
    have ha : x₀ = a := by
      rw [hx] at hx'
      exact Sum.inr_injective hx'
    subst ha
    have hedge : (Γ'.netT (liftT j S ++ newT ch cs) true).Reachable w (Fin.castAdd j b) := by
      refine Graph.netT_reach_of_mem _ _ _ (List.mem_append_right _
        (newT_mem hc (by simp [mkC, Kind.blueC]))) rfl rfl ?_
      change liftA j p.1.y = _
      rw [hy']
      rfl
    exact (Graph.netT_reach_of_sameMol _ _ _ hlink).trans hedge

/-- A blue solid edge `G^{ch}_{u x}` entering `x` is replaced by `G^{ch}_{u w}` at an atom `w`
joined to `x`. -/
private theorem comp_redirect_in {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (hL : Γ.DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)} (S : List (TC k n))
    (cs : List (Comp (Atom k (n + j)))) {p : TC k n} (hp : p ∈ L) {ch : Charge}
    (hk : p.1.kind = .G ch) {x₀ : Fin n} (hy : p.1.y = Sum.inr x₀) {w : Fin (n + j)}
    (hlink : Γ'.SameMol (Sum.inr (Fin.castAdd j x₀)) (Sum.inr w))
    (hc : mkC (.G ch) (liftA j p.1.x) (Sum.inr w) ∈ cs) :
    Compensated j Γ' (liftT j S ++ newT bc cs) p := by
  refine ⟨⟨by rw [hk]; rfl, ?_⟩, ?_⟩
  · intro hp2
    have := hL.black p hp hp2
    rw [hk] at this
    exact absurd this (by simp [Kind.isDiffusive])
  · intro hpt a b hx' hy'
    have hb := hL.blue p hp hpt
    rw [hk] at hb
    have hch : ch = bc := by
      rcases hb with hb | hb
      · simp [Kind.isDiffusive] at hb
      · simpa [Kind.blueC] using hb
    subst hch
    have hb' : x₀ = b := by
      rw [hy] at hy'
      exact Sum.inr_injective hy'
    subst hb'
    have hedge : (Γ'.netT (liftT j S ++ newT ch cs) true).Reachable (Fin.castAdd j a) w := by
      refine Graph.netT_reach_of_mem _ _ _ (List.mem_append_right _
        (newT_mem hc (by simp [mkC, Kind.blueC]))) rfl ?_ rfl
      change liftA j p.1.x = _
      rw [hx']
      rfl
    exact hedge.trans (Graph.netT_reach_of_sameMol _ _ _
      ((Graph.sameMol_equivalence Γ').symm hlink))

/-- The solid edge `p` at the atom `x₀` is replaced in `cs` by a solid edge of the same charge
with the end at `x₀` moved to an atom `w` joined to `x₀`. -/
private def Redir (j : ℕ) (Γ' : Graph k (n + j)) (cs : List (Comp (Atom k (n + j))))
    (x₀ : Fin n) (p : TC k n) : Prop :=
  ∃ (ch : Charge) (w : Fin (n + j)), p.1.kind = .G ch ∧
    Γ'.SameMol (Sum.inr (Fin.castAdd j x₀)) (Sum.inr w) ∧
    ((p.1.x = Sum.inr x₀ ∧ mkC (.G ch) (Sum.inr w) (liftA j p.1.y) ∈ cs) ∨
      (p.1.y = Sum.inr x₀ ∧ mkC (.G ch) (liftA j p.1.x) (Sum.inr w) ∈ cs))

private theorem Redir.append_left {j : ℕ} {Γ' : Graph k (n + j)}
    {cs : List (Comp (Atom k (n + j)))} {x₀ : Fin n} {p : TC k n}
    (ps : List (Comp (Atom k (n + j))))
    (h : Redir j Γ' cs x₀ p) : Redir j Γ' (ps ++ cs) x₀ p := by
  obtain ⟨ch, w, hk, hl, ⟨hx, hc⟩ | ⟨hy, hc⟩⟩ := h
  · exact ⟨ch, w, hk, hl, Or.inl ⟨hx, List.mem_append_right _ hc⟩⟩
  · exact ⟨ch, w, hk, hl, Or.inr ⟨hy, List.mem_append_right _ hc⟩⟩

private theorem Graph.DCT.compensated_of_redir {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)} (S : List (TC k n))
    (cs : List (Comp (Atom k (n + j)))) {x₀ : Fin n} {p : TC k n} (hp : p ∈ L)
    (hr : Redir j Γ' cs x₀ p) : Compensated j Γ' (liftT j S ++ newT bc cs) p := by
  obtain ⟨ch, w, hk, hlink, ⟨hx, hc⟩ | ⟨hy, hc⟩⟩ := hr
  · exact comp_redirect_out h S cs hp hk hx hlink hc
  · exact comp_redirect_in h S cs hp hk hy hlink hc

private theorem mem_edgeIdx_T {L : List (TC k n)} {co : Coeff} {x : Atom k n} {ch : Charge}
    {out : Bool} {i : ℕ} (h : i ∈ (Graph.mk (L.map Prod.fst) co).edgeIdx x ch out) :
    ∃ hi : i < L.length, L[i].1.kind = .G ch ∧
      (out = true → L[i].1.x = x ∧ L[i].1.y ≠ x) ∧
      (out = false → L[i].1.y = x ∧ L[i].1.x ≠ x) := by
  obtain ⟨hi, h1, h2, h3⟩ := mem_edgeIdx h
  have hi' : i < L.length := by simpa using hi
  refine ⟨hi', ?_, ?_, ?_⟩
  · simpa using h1
  · intro ho; simpa using h2 ho
  · intro ho; simpa using h3 ho

/-- A local expansion term that keeps all components except those at the indices `E`, each of
which is replaced. -/
private theorem shapeR {bc : Charge} {L : List (TC k n)} {co : Coeff}
    (hL : (Graph.mk (L.map Prod.fst) co).DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)}
    (E : List ℕ) (cs : List (Comp (Atom k (n + j)))) (x₀ : Fin n)
    (hΓ' : Γ'.comps = liftCs j (eraseIdxs E (L.map Prod.fst)) ++ cs)
    (hcov : ∀ i ∈ E, ∀ hi : i < L.length, Redir j Γ' cs x₀ L[i])
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) : Γ'.DCS bc := by
  refine ⟨liftT j (eraseIdxs E L) ++ newT bc cs,
    hL.shapeE (eraseIdxs E L) cs ?_ (fun q hq => mem_eraseIdxs_subset hq) ?_ hnew⟩
  · rw [hΓ']
    simp [liftT_map_fst, newT_map_fst, eraseIdxs_map]
  · intro p hp hpS
    rcases mem_eraseIdxs_or (is := E) hp with h | ⟨i, hiE, hi, rfl⟩
    · exact absurd h hpS
    · exact hL.compensated_of_redir _ _ hp (hcov i hiE hi)

/-- A local expansion term with a partial derivative: the components at the indices `E` are
erased (those at `E₂` are kept) and a component of the others is replaced by its pieces. -/
private theorem shapeRD {bc : Charge} {L : List (TC k n)} {co : Coeff}
    (hL : (Graph.mk (L.map Prod.fst) co).DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)}
    (E E₂ : List ℕ) (cs d : List (Comp (Atom k (n + j)))) (x₀ : Fin n) (p q : Fin (n + j))
    (hd : d ∈ dTerms (Sum.inr p) (Sum.inr q) (liftCs j (eraseIdxs E (L.map Prod.fst))))
    (hΓ' : Γ'.comps = liftCs j (pickIdxs E₂ (L.map Prod.fst)) ++ d ++ cs)
    (hlink : Γ'.SameMol (Sum.inr p) (Sum.inr q))
    (hcov : ∀ i ∈ E, i ∉ E₂ → ∀ hi : i < L.length, Redir j Γ' cs x₀ L[i])
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) : Γ'.DCS bc := by
  obtain ⟨i', ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hF : liftCs j (eraseIdxs E (L.map Prod.fst)) = (liftT j (eraseIdxs E L)).map Prod.fst := by
    simp [liftT_map_fst, eraseIdxs_map]
  have hlen : (liftCs j (eraseIdxs E (L.map Prod.fst))).length = (eraseIdxs E L).length := by
    rw [hF]; simp [liftT]
  have hi'S : i'.1 < (eraseIdxs E L).length := lt_of_lt_of_eq i'.2 hlen
  have hps' : (((eraseIdxs E L)[i'.1]'hi'S).1.map (liftA j)).dPieces (Sum.inr p) (Sum.inr q) =
      some ps := by
    have h1 : ∀ (m : ℕ) (hm : m < (liftCs j (eraseIdxs E (L.map Prod.fst))).length)
        (hm' : m < (eraseIdxs E L).length),
        (liftCs j (eraseIdxs E (L.map Prod.fst)))[m] =
          (((eraseIdxs E L)[m]'hm').1.map (liftA j)) := by
      intro m hm hm'
      simp [liftCs, eraseIdxs_map]
    rw [← h1 i'.1 i'.2 hi'S]
    exact hps
  refine ⟨liftT j (pickIdxs E₂ L ++ (eraseIdxs E L).eraseIdx i'.1) ++ newT bc (ps ++ cs),
    hL.shapeD (pickIdxs E₂ L) (eraseIdxs E L) i'.1 hi'S p q ps cs hps' ?_
      (fun r hr => mem_pickIdxs_subset hr) (fun r hr => mem_eraseIdxs_subset hr) hlink ?_ hnew⟩
  · rw [hΓ']
    simp [newT_map_fst, eraseIdxs_map, pickIdxs_map, liftCs, liftT,
      Function.comp_def, List.eraseIdx_map]
  · intro r hr hr0 hrS
    rcases mem_eraseIdxs_or (is := E) hr with h | ⟨i, hiE, hi, rfl⟩
    · exact absurd h hrS
    · have hiE₂ : i ∉ E₂ := fun hh => hr0 (mem_pickIdxs.2 ⟨i, hh, hi, rfl⟩)
      exact hL.compensated_of_redir _ _ hr ((hcov i hiE hiE₂ hi).append_left ps)

/-- A local expansion term that keeps all components except the one at the index `i`, which is
replaced. -/
private theorem shapeR1 {bc : Charge} {L : List (TC k n)} {co : Coeff}
    (hL : (Graph.mk (L.map Prod.fst) co).DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)}
    (i : ℕ) (hi : i < L.length) (cs : List (Comp (Atom k (n + j)))) (x₀ : Fin n)
    (hΓ' : Γ'.comps = liftCs j ((L.map Prod.fst).eraseIdx i) ++ cs)
    (hcov : Redir j Γ' cs x₀ L[i])
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) : Γ'.DCS bc := by
  refine ⟨liftT j (L.eraseIdx i) ++ newT bc cs,
    hL.shapeE (L.eraseIdx i) cs ?_ (fun q hq => mem_eraseIdx_subset hq) ?_ hnew⟩
  · rw [hΓ']
    simp [liftT_map_fst, newT_map_fst, List.eraseIdx_map]
  · intro p hp hpS
    rcases mem_eraseIdx_or (i := i) hp with h | ⟨_, rfl⟩
    · exact absurd h hpS
    · exact hL.compensated_of_redir _ _ hp hcov

private theorem getD_map_fst {L : List (TC k n)} {j : ℕ} (hj : j < L.length)
    (d : Comp (Atom k n)) : (L.map Prod.fst).getD j d = L[j].1 := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- A term of the `GG` expansion with a partial derivative and no further kept components. -/
private theorem shapeRD0 {bc : Charge} {L : List (TC k n)} {co : Coeff}
    (hL : (Graph.mk (L.map Prod.fst) co).DCT bc L) {j : ℕ} {Γ' : Graph k (n + j)}
    (E : List ℕ) (cs d : List (Comp (Atom k (n + j)))) (x₀ : Fin n) (p q : Fin (n + j))
    (hd : d ∈ dTerms (Sum.inr p) (Sum.inr q) (liftCs j (eraseIdxs E (L.map Prod.fst))))
    (hΓ' : Γ'.comps = d ++ cs) (hlink : Γ'.SameMol (Sum.inr p) (Sum.inr q))
    (hcov : ∀ i ∈ E, ∀ hi : i < L.length, Redir j Γ' cs x₀ L[i])
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) : Γ'.DCS bc :=
  shapeRD hL E [] cs d x₀ p q hd (by rw [hΓ']; simp [pickIdxs, liftCs]) hlink
    (fun i hi _ hiL => hcov i hi hiL) hnew

/-- The two solid edges `G_{x y}` and `G_{y' x}` at `x` are replaced by solid edges at atoms
`wi`, `wj` joined to `x`. -/
private theorem redir_pair {j' : ℕ} {Γ' : Graph k (n + j')} {cs : List (Comp (Atom k (n + j')))}
    {x₀ : Fin n} {wi wj : Fin (n + j')} {L : List (TC k n)} {i j : ℕ} (hiL : i < L.length)
    (hjL : j < L.length) (hki : L[i].1.kind = .G .plus)
    (hxi : L[i].1.x = Sum.inr x₀) (hkj : L[j].1.kind = .G .plus)
    (hyj : L[j].1.y = Sum.inr x₀) (hli : Γ'.SameMol (Sum.inr (Fin.castAdd j' x₀)) (Sum.inr wi))
    (hlj : Γ'.SameMol (Sum.inr (Fin.castAdd j' x₀)) (Sum.inr wj))
    (hmi : mkC (.G .plus) (Sum.inr wi) (liftA j' L[i].1.y) ∈ cs)
    (hmj : mkC (.G .plus) (liftA j' L[j].1.x) (Sum.inr wj) ∈ cs) :
    ∀ i' ∈ [i, j], ∀ hi' : i' < L.length, Redir j' Γ' cs x₀ L[i'] := by
  intro i' hi' hi'L
  rcases List.mem_cons.1 hi' with rfl | hi'
  · exact ⟨.plus, wi, hki, hli, Or.inl ⟨hxi, hmi⟩⟩
  · rw [List.mem_singleton] at hi'
    subst i'
    exact ⟨.plus, wj, hkj, hlj, Or.inr ⟨hyj, hmj⟩⟩

/-- A tagged list for a graph on the same atoms, made of components of `L` and untagged new
components, that keeps every tagged component and every component joining molecules. -/
private theorem Graph.DCT.of_retain {bc : Charge} {Γ : Graph k n} {L : List (TC k n)}
    (h : Γ.DCT bc L) {Γ' : Graph k n} (L' : List (TC k n))
    (hmap : L'.map Prod.fst = Γ'.comps) (hsub : ∀ q ∈ L', q ∈ L ∨ q.2 = none)
    (hret : ∀ q ∈ L, (q.1.kind.joinsMol = true ∨ q.2 ≠ none) → q ∈ L') : Γ'.DCT bc L' := by
  have hid : (Sum.map id (id : Fin n → Fin n) : Atom k n → Atom k n) = id := by
    funext u; rcases u with a | a <;> rfl
  refine h.transport id L' hmap ?_ ?_ ?_ ?_ (fun w => ⟨w, Or.inl rfl⟩)
  · intro q hq hqt
    rcases hsub q hq with hq | hq
    · exact h.black q hq hqt
    · rw [hq] at hqt; exact absurd hqt (by simp)
  · intro q hq hqt
    rcases hsub q hq with hq | hq
    · exact h.blue q hq hqt
    · rw [hq] at hqt; exact absurd hqt (by simp)
  · intro c hc hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (h.map_fst ▸ hc)
    have hqc : p.1 ∈ Γ'.comps := hmap ▸ List.mem_map_of_mem (hret p hp (Or.inl hk))
    rw [hid]
    exact Graph.molReach_of_comp hqc hk
  · intro t p hp hpt a b hx hy
    exact Graph.netT_reach_of_mem _ _ _ (hret p hp (Or.inr (by rw [hpt]; simp))) hpt hx hy

end Tagged

section Assembly

variable {k n : ℕ}

/-- `O^{(x),1}_weight` splits weights into a constant and a light weight: the other components
are kept. -/
private theorem splitRegular_tagged (x : Atom k n) :
    ∀ (L : List (TC k n)), ∀ p ∈ splitRegular x (L.map Prod.fst), ∃ L' : List (TC k n),
      L'.map Prod.fst = p.1 ∧ (∀ q ∈ L, q.1.kind.isWeight = false → q ∈ L') ∧
        (∀ q ∈ L', q ∈ L ∨ q.2 = none) := by
  intro L
  induction L with
  | nil =>
    intro p hp
    simp only [List.map_nil, splitRegular, List.mem_singleton] at hp
    subst hp
    exact ⟨[], rfl, by simp, by simp⟩
  | cons q L ih =>
    intro p hp
    simp only [List.map_cons, splitRegular] at hp
    have hkeep : ∀ p₀ ∈ splitRegular x (L.map Prod.fst), ∃ L₀ : List (TC k n),
        L₀.map Prod.fst = p₀.1 ∧ (∀ r ∈ L, r.1.kind.isWeight = false → r ∈ L₀) ∧
          (∀ r ∈ L₀, r ∈ L ∨ r.2 = none) := ih
    have hrest : ∀ p₀ ∈ splitRegular x (L.map Prod.fst), ∃ L' : List (TC k n),
        L'.map Prod.fst = q.1 :: p₀.1 ∧
          (∀ r ∈ q :: L, r.1.kind.isWeight = false → r ∈ L') ∧
          (∀ r ∈ L', r ∈ q :: L ∨ r.2 = none) := by
      intro p₀ hp₀
      obtain ⟨L₀, h1, h2, h3⟩ := hkeep p₀ hp₀
      refine ⟨q :: L₀, by simp [h1], ?_, ?_⟩
      · intro r hr hrw
        rcases List.mem_cons.1 hr with rfl | hr
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (h2 r hr hrw)
      · intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · exact Or.inl (List.mem_cons_self ..)
        · rcases h3 r hr with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
    cases hk : q.1.kind with
    | weight ch =>
      rw [hk] at hp
      dsimp only at hp
      split_ifs at hp with hc
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
          obtain ⟨L₀, h1, h2, h3⟩ := hkeep p₀ hp₀
          refine ⟨L₀, h1, ?_, ?_⟩
          · intro r hr hrw
            rcases List.mem_cons.1 hr with rfl | hr
            · rw [hk] at hrw; simp [Kind.isWeight] at hrw
            · exact h2 r hr hrw
          · intro r hr
            rcases h3 r hr with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · exact Or.inr h
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
          obtain ⟨L₀, h1, h2, h3⟩ := hkeep p₀ hp₀
          refine ⟨({ q.1 with kind := .light ch }, none) :: L₀, by simp [h1], ?_, ?_⟩
          · intro r hr hrw
            rcases List.mem_cons.1 hr with rfl | hr
            · rw [hk] at hrw; simp [Kind.isWeight] at hrw
            · exact List.mem_cons_of_mem _ (h2 r hr hrw)
          · intro r hr
            rcases List.mem_cons.1 hr with rfl | hr
            · exact Or.inr rfl
            · rcases h3 r hr with h | h
              · exact Or.inl (List.mem_cons_of_mem _ h)
              · exact Or.inr h
      · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
        exact hrest p₀ hp₀
    | G ch =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | light ch =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | inv ch =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | wD ch D =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | waved w =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | theta o =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | thetaErr m D =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | ghost =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | aux j r b =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | dot =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀
    | xdot =>
      rw [hk] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      exact hrest p₀ hp₀

end Assembly

/-- Membership of one of the last components of a list `A ++ [c₁, …, cₘ]`. -/
local syntax "mem_tail" : tactic

macro_rules
  | `(tactic| mem_tail) => `(tactic| first
    | exact List.mem_append_right _ (List.mem_cons_self ..)
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..))))))
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))))
    | exact List.mem_append_right _ (List.mem_singleton_self _)
    | (apply List.mem_append_left; mem_tail))

/-- Membership in an explicit list `[c₁, …, cₘ]`. -/
local syntax "mem_cs" : tactic

macro_rules
  | `(tactic| mem_cs) => `(tactic| first
    | exact List.mem_cons_self ..
    | exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..))))))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))
    | exact List.mem_singleton_self _)

private theorem Graph.sameMol_of_waved' {Γ : Graph k n} {w : Wave} {u v : Fin n}
    (hc : mkC (.waved w) (Sum.inr u) (Sum.inr v) ∈ Γ.comps) :
    Γ.SameMol (Sum.inr u) (Sum.inr v) :=
  Graph.sameMol_of_waved hc rfl rfl rfl

section Weight

variable {k n : ℕ}

private theorem liftA_isRight {j : ℕ} (u : Atom k n) : (liftA j u).isRight = u.isRight := by
  cases u <;> rfl

/-- A weight expansion term that keeps all components except the light weight at index `i`. -/
private theorem weight_shapeE {bc : Charge} {L : List (TC k n)} {co : Coeff}
    (hL : (Graph.mk (L.map Prod.fst) co).DCT bc L) {i : ℕ} (hi : i < L.length)
    (hLi : L[i].1.kind = .light .plus) {j : ℕ} {Γ' : Graph k (n + j)}
    (cs : List (Comp (Atom k (n + j))))
    (hΓ' : Γ'.comps = liftCs j ((L.map Prod.fst).eraseIdx i) ++ cs)
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) : Γ'.DCS bc := by
  refine ⟨liftT j (L.eraseIdx i) ++ newT bc cs,
    hL.shapeE (L.eraseIdx i) cs ?_ (fun q hq => mem_eraseIdx_subset hq) ?_ hnew⟩
  · rw [hΓ']
    simp [liftT_map_fst, newT_map_fst, List.eraseIdx_map]
  · intro p hp hpS
    rcases mem_eraseIdx_or (i := i) hp with h | ⟨_, h⟩
    · exact absurd h hpS
    · refine hL.compensated_of_inert _ _ hp ?_
      rw [h]
      simp [Inert, hLi, Kind.isDiffusive, Kind.blueC, Kind.joinsMol]

/-- A weight expansion term with a partial derivative: the light weight at index `i` is erased
and a component of the others is replaced by its pieces. -/
private theorem weight_shapeD {bc : Charge} {L : List (TC k n)} {co : Coeff}
    (hL : (Graph.mk (L.map Prod.fst) co).DCT bc L) {i : ℕ} (hi : i < L.length)
    (hLi : L[i].1.kind = .light .plus) {j : ℕ} {Γ' : Graph k (n + j)} (p q : Fin (n + j))
    (cs d : List (Comp (Atom k (n + j))))
    (hd : d ∈ dTerms (Sum.inr p) (Sum.inr q) (liftCs j ((L.map Prod.fst).eraseIdx i)))
    (hΓ' : Γ'.comps = d ++ cs) (hlink : Γ'.SameMol (Sum.inr p) (Sum.inr q))
    (hnew : ∀ w : Fin (n + j), ∃ a : Fin n,
      Γ'.SameMol (Sum.inr w) (Sum.inr (Fin.castAdd j a))) : Γ'.DCS bc := by
  obtain ⟨i', ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hF : liftCs j ((L.map Prod.fst).eraseIdx i) = (liftT j (L.eraseIdx i)).map Prod.fst := by
    simp [liftT_map_fst, List.eraseIdx_map]
  have hlen : (liftCs j ((L.map Prod.fst).eraseIdx i)).length = (L.eraseIdx i).length := by
    rw [hF]; simp [liftT]
  have hi'S : i'.1 < (L.eraseIdx i).length := lt_of_lt_of_eq i'.2 hlen
  have hps' : (((L.eraseIdx i)[i'.1]'hi'S).1.map (liftA j)).dPieces (Sum.inr p) (Sum.inr q) =
      some ps := by
    have h1 : ∀ (m : ℕ) (hm : m < (liftCs j ((L.map Prod.fst).eraseIdx i)).length)
        (hm' : m < (L.eraseIdx i).length),
        (liftCs j ((L.map Prod.fst).eraseIdx i))[m] =
          (((L.eraseIdx i)[m]'hm').1.map (liftA j)) := by
      intro m hm hm'
      simp [liftCs, List.eraseIdx_map]
    rw [← h1 i'.1 i'.2 hi'S]
    exact hps
  refine ⟨liftT j ([] ++ (L.eraseIdx i).eraseIdx i'.1) ++ newT bc (ps ++ cs),
    hL.shapeD [] (L.eraseIdx i) i'.1 hi'S p q ps cs hps' ?_ (fun r hr => absurd hr (by simp))
      (fun r hr => mem_eraseIdx_subset hr) hlink ?_ hnew⟩
  · rw [hΓ']
    simp [newT_map_fst, List.eraseIdx_map, liftCs, liftT, Function.comp_def]
  · intro r hr _ hrS
    rcases mem_eraseIdx_or (i := i) hr with h | ⟨_, h⟩
    · exact absurd h hrS
    · refine hL.compensated_of_inert _ _ hr ?_
      rw [h]
      simp [Inert, hLi, Kind.isDiffusive, Kind.blueC, Kind.joinsMol]

private theorem oWeight2Pos_dcs {bc : Charge} {Γ : Graph k n} (x : Atom k n)
    (hx : x.isRight = true) (h : Γ.DCS bc) {E : TExpansion k n}
    (hE : oWeight2Pos x Γ = some E) :
    ∀ t ∈ E, t.g.DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, x = Sum.inr x₀ := by
    cases x with
    | inl a => simp at hx
    | inr a => exact ⟨a, rfl⟩
  obtain ⟨L, hL⟩ := h
  obtain ⟨cs, co⟩ := Γ
  obtain rfl : cs = L.map Prod.fst := hL.map_fst.symm
  unfold oWeight2Pos at hE
  dsimp only at hE
  rcases hfi : (L.map Prod.fst).findIdx? (fun c => c.kind == .light .plus && c.x == Sum.inr x₀)
    with _ | i
  · rw [hfi] at hE; simp at hE
  rw [hfi] at hE
  simp only [Option.some.injEq] at hE
  subst hE
  obtain ⟨hi', hpred, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfi
  have hi : i < L.length := by simpa using hi'
  have hLi : L[i].1.kind = .light .plus := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.getElem_map] at hpred
    exact hpred.1
  intro t ht
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ht
  rcases ht with ((((((rfl | rfl) | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩) | rfl | rfl | rfl | rfl) |
    ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩)
  · refine ⟨hL.addAtoms _ rfl ?_, fun u => liftA_isRight u⟩
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨weight_shapeE hL hi hLi _ rfl ?_, fun u => liftA_isRight u⟩
    refine hnew₂ x₀ ?_ ?_
    · exact Graph.sameMol_of_waved' (w := .plus) (by mem_tail)
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
  · refine ⟨weight_shapeD hL hi hLi (Fin.natAdd n 0) (Fin.castAdd 1 x₀) _ d hd rfl ?_ ?_,
      fun u => liftA_isRight u⟩
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨weight_shapeD hL hi hLi (Fin.natAdd n 1) (Fin.natAdd n 0) _ d hd rfl ?_ ?_,
      fun u => liftA_isRight u⟩
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · exact ⟨Graph.DCS.labelQ ⟨L, hL⟩ _ rfl, fun u => rfl⟩
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine weight_shapeE hL hi hLi _ (by rw [List.append_assoc]) ?_
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine weight_shapeE hL hi hLi _ (by rw [List.append_assoc]) ?_
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine weight_shapeE hL hi hLi _ (by rw [List.append_assoc]) ?_
    exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
      (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine weight_shapeD hL hi hLi (Fin.natAdd n 0) (Fin.castAdd 1 x₀) _ d hd
      (by rw [List.append_assoc]) ?_ ?_
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine weight_shapeD hL hi hLi (Fin.natAdd n 1) (Fin.natAdd n 0) _ d hd
      (by rw [List.append_assoc]) ?_ ?_
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))

end Weight

section MultiE

variable {k n : ℕ}

private theorem multiEOut_dcs {bc : Charge} {Γ : Graph k n} (x : Atom k n)
    (hx : x.isRight = true) (h : Γ.DCS bc) {E : TExpansion k n}
    (hE : multiEOut x Γ = some E) :
    ∀ t ∈ E, t.g.DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, x = Sum.inr x₀ := by
    cases x with
    | inl a => simp at hx
    | inr a => exact ⟨a, rfl⟩
  obtain ⟨L, hL⟩ := h
  obtain ⟨cs, co⟩ := Γ
  obtain rfl : cs = L.map Prod.fst := hL.map_fst.symm
  unfold multiEOut at hE
  dsimp only at hE
  rcases hO : (Graph.mk (L.map Prod.fst) co).edgeIdx (Sum.inr x₀) .plus true with _ | ⟨i₁, is₂⟩
  · rw [hO] at hE; simp at hE
  rw [hO] at hE
  dsimp only at hE
  rcases he₁ : (L.map Prod.fst)[i₁]? with _ | e₁
  · rw [he₁] at hE; simp at hE
  rw [he₁] at hE
  dsimp only at hE
  split at hE
  · simp at hE
  simp only [Option.some.injEq] at hE
  subst hE
  have hi₁mem : i₁ ∈ (Graph.mk (L.map Prod.fst) co).edgeIdx (Sum.inr x₀) .plus true := by
    rw [hO]; exact List.mem_cons_self ..
  obtain ⟨hi₁, hk₁, hx₁', -⟩ := mem_edgeIdx_T hi₁mem
  have hx₁ : L[i₁].1.x = Sum.inr x₀ := (hx₁' rfl).1
  have he₁' : e₁ = L[i₁].1 := by
    have := he₁
    simp [List.getElem?_eq_getElem hi₁] at this
    exact this.symm
  subst he₁'
  intro t ht
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ht
  rcases ht with ((((((((((((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl) |
    h6) | h7) | ⟨d, ⟨d', hd, rfl⟩, rfl⟩) | rfl) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl) | h13) |
    h14) | ⟨d, ⟨d', hd, rfl⟩, rfl⟩)
  · obtain ⟨hjL, hjk, hjx', -⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨shapeR hL [i₁, j] _ x₀ rfl ?_ ?_, fun u => liftA_isRight u⟩
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.minus, Fin.natAdd n 0, hjk, ?_, Or.inl ⟨(hjx' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · obtain ⟨hjL, hjk, -, hjy'⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨shapeR hL [i₁, j] _ x₀ rfl ?_ ?_, fun u => liftA_isRight u⟩
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.plus, Fin.natAdd n 0, hjk, ?_, Or.inr ⟨(hjy' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · obtain ⟨hjL, hjk, hjx', -⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨shapeR hL [i₁, j] _ x₀ (by rw [List.append_assoc]) ?_ ?_, fun u => liftA_isRight u⟩
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.minus, Fin.natAdd n 0, hjk, ?_, Or.inl ⟨(hjx' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · obtain ⟨hjL, hjk, -, hjy'⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨shapeR hL [i₁, j] _ x₀ (by rw [List.append_assoc]) ?_ ?_, fun u => liftA_isRight u⟩
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.plus, Fin.natAdd n 0, hjk, ?_, Or.inr ⟨(hjy' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨hL.addAtoms _ rfl ?_, fun u => liftA_isRight u⟩
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · split_ifs at h6 with hc
    · simp at h6
    obtain rfl := List.mem_singleton.1 h6
    refine ⟨shapeR1 hL i₁ hi₁ _ x₀ rfl ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩ ?_,
      fun u => liftA_isRight u⟩
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · split_ifs at h7 with hc
    · simp at h7
    obtain rfl := List.mem_singleton.1 h7
    refine ⟨shapeR1 hL i₁ hi₁ _ x₀ rfl ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩ ?_,
      fun u => liftA_isRight u⟩
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨shapeRD hL _ _ _ d' x₀ (Fin.natAdd n 0) (Fin.castAdd 1 x₀) hd rfl ?_ ?_ ?_,
      fun u => liftA_isRight u⟩
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · intro i hiE hiE₂ hiL
      have hi₁' : i = i₁ := by
        by_contra hne
        exact hiE₂ (List.mem_filter.2 ⟨hiE, by simpa using hne⟩)
      subst hi₁'
      refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩
      · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
      · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · exact ⟨Graph.DCS.labelQ ⟨L, hL⟩ _ rfl, fun u => rfl⟩
  · obtain ⟨hjL, hjk, hjx', -⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine shapeR hL [i₁, j] _ x₀ (by rw [List.append_assoc]) ?_ ?_
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.minus, Fin.natAdd n 0, hjk, ?_, Or.inl ⟨(hjx' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · obtain ⟨hjL, hjk, -, hjy'⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine shapeR hL [i₁, j] _ x₀ (by rw [List.append_assoc]) ?_ ?_
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.plus, Fin.natAdd n 0, hjk, ?_, Or.inr ⟨(hjy' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine hL.addAtoms _ rfl ?_
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · split_ifs at h13 with hc
    · simp at h13
    obtain rfl := List.mem_singleton.1 h13
    refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine shapeR1 hL i₁ hi₁ _ x₀ rfl ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩ ?_
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · split_ifs at h14 with hc
    · simp at h14
    obtain rfl := List.mem_singleton.1 h14
    refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine shapeR1 hL i₁ hi₁ _ x₀ rfl ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩ ?_
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine shapeRD hL _ _ _ d' x₀ (Fin.natAdd n 0) (Fin.castAdd 1 x₀) hd rfl ?_ ?_ ?_
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · intro i hiE hiE₂ hiL
      have hi₁' : i = i₁ := by
        by_contra hne
        exact hiE₂ (List.mem_filter.2 ⟨hiE, by simpa using hne⟩)
      subst hi₁'
      refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inl ⟨hx₁, ?_⟩⟩
      · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
      · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))

private theorem multiEIn_dcs {bc : Charge} {Γ : Graph k n} (x : Atom k n)
    (hx : x.isRight = true) (h : Γ.DCS bc) {E : TExpansion k n}
    (hE : multiEIn x Γ = some E) :
    ∀ t ∈ E, t.g.DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, x = Sum.inr x₀ := by
    cases x with
    | inl a => simp at hx
    | inr a => exact ⟨a, rfl⟩
  obtain ⟨L, hL⟩ := h
  obtain ⟨cs, co⟩ := Γ
  obtain rfl : cs = L.map Prod.fst := hL.map_fst.symm
  unfold multiEIn at hE
  dsimp only at hE
  rcases hO : (Graph.mk (L.map Prod.fst) co).edgeIdx (Sum.inr x₀) .plus false with _ | ⟨i₁, is₂⟩
  · rw [hO] at hE; simp at hE
  rw [hO] at hE
  dsimp only at hE
  rcases he₁ : (L.map Prod.fst)[i₁]? with _ | e₁
  · rw [he₁] at hE; simp at hE
  rw [he₁] at hE
  dsimp only at hE
  split at hE
  · simp at hE
  simp only [Option.some.injEq] at hE
  subst hE
  have hi₁mem : i₁ ∈ (Graph.mk (L.map Prod.fst) co).edgeIdx (Sum.inr x₀) .plus false := by
    rw [hO]; exact List.mem_cons_self ..
  obtain ⟨hi₁, hk₁, -, hy₁'⟩ := mem_edgeIdx_T hi₁mem
  have hy₁ : L[i₁].1.y = Sum.inr x₀ := (hy₁' rfl).1
  have he₁' : e₁ = L[i₁].1 := by
    have := he₁
    simp [List.getElem?_eq_getElem hi₁] at this
    exact this.symm
  subst he₁'
  intro t ht
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ht
  rcases ht with (((((((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | rfl) | h4) | ⟨d, ⟨d', hd, rfl⟩, rfl⟩) |
    rfl) | ⟨j, hj, rfl⟩) | rfl) | h9) | ⟨d, ⟨d', hd, rfl⟩, rfl⟩)
  · obtain ⟨hjL, hjk, -, hjy'⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨shapeR hL [i₁, j] _ x₀ rfl ?_ ?_, fun u => liftA_isRight u⟩
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inr ⟨hy₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.minus, Fin.natAdd n 0, hjk, ?_, Or.inr ⟨(hjy' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · obtain ⟨hjL, hjk, -, hjy'⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨shapeR hL [i₁, j] _ x₀ (by rw [List.append_assoc]) ?_ ?_, fun u => liftA_isRight u⟩
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inr ⟨hy₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.minus, Fin.natAdd n 0, hjk, ?_, Or.inr ⟨(hjy' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨hL.addAtoms _ rfl ?_, fun u => liftA_isRight u⟩
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · split_ifs at h4 with hc
    · simp at h4
    obtain rfl := List.mem_singleton.1 h4
    refine ⟨shapeR1 hL i₁ hi₁ _ x₀ rfl ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inr ⟨hy₁, ?_⟩⟩ ?_,
      fun u => liftA_isRight u⟩
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨shapeRD hL _ _ _ d' x₀ (Fin.castAdd 1 x₀) (Fin.natAdd n 0) hd rfl ?_ ?_ ?_,
      fun u => liftA_isRight u⟩
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · intro i hiE hiE₂ hiL
      have hi₁' : i = i₁ := by
        by_contra hne
        exact hiE₂ (List.mem_filter.2 ⟨hiE, by simpa using hne⟩)
      subst hi₁'
      refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inr ⟨hy₁, ?_⟩⟩
      · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
      · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · exact ⟨Graph.DCS.labelQ ⟨L, hL⟩ _ rfl, fun u => rfl⟩
  · obtain ⟨hjL, hjk, -, hjy'⟩ := mem_edgeIdx_T hj
    rw [getD_map_fst hjL]
    refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine shapeR hL [i₁, j] _ x₀ (by rw [List.append_assoc]) ?_ ?_
    · intro i hi hiL
      rcases List.mem_cons.1 hi with rfl | hi
      · refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inr ⟨hy₁, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
      · rw [List.mem_singleton] at hi
        subst hi
        refine ⟨.minus, Fin.natAdd n 0, hjk, ?_, Or.inr ⟨(hjy' rfl).1, ?_⟩⟩
        · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
        · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine hL.addAtoms _ rfl ?_
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · split_ifs at h9 with hc
    · simp at h9
    obtain rfl := List.mem_singleton.1 h9
    refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine shapeR1 hL i₁ hi₁ _ x₀ rfl ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inr ⟨hy₁, ?_⟩⟩ ?_
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ (Γ := ⟨_, co⟩) ?_ _ rfl, fun u => liftA_isRight u⟩
    refine shapeRD hL _ _ _ d' x₀ (Fin.castAdd 1 x₀) (Fin.natAdd n 0) hd rfl ?_ ?_ ?_
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · intro i hiE hiE₂ hiL
      have hi₁' : i = i₁ := by
        by_contra hne
        exact hiE₂ (List.mem_filter.2 ⟨hiE, by simpa using hne⟩)
      subst hi₁'
      refine ⟨.plus, Fin.natAdd n 0, hk₁, ?_, Or.inr ⟨hy₁, ?_⟩⟩
      · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
      · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))

end MultiE

section GG

variable {k n : ℕ}

private theorem liftA_zero (u : Atom k n) : liftA 0 u = u := by
  cases u <;> rfl

private theorem Comp.map_id' {V : Type*} (c : Comp V) : c.map id = c := by
  cases c; simp [Comp.map]

private theorem liftCs_zero (cs : List (Comp (Atom k n))) : liftCs 0 cs = cs := by
  have : (liftA 0 : Atom k n → Atom k n) = id := funext liftA_zero
  unfold liftCs
  rw [this]
  exact (List.map_congr_left fun c _ => Comp.map_id' c).trans (List.map_id _)

private theorem liftT_zero_map_fst (S : List (TC k n)) :
    (liftT 0 S).map Prod.fst = S.map Prod.fst := by
  rw [liftT_map_fst, liftCs_zero]

private theorem reach_of_solidC {bc : Charge} {Γ' : Graph k m} {X : List (TC k m)}
    {cs : List (Comp (Atom k m))} {a b : Fin m}
    (hmem : solidC .plus (Sum.inr a : Atom k m) (Sum.inr b) ∈ cs) (hbc : bc = .plus) :
    (Γ'.netT (X ++ newT bc cs) true).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · have hne : (Sum.inr a : Atom k m) ≠ Sum.inr b := by simpa using hab
    have hs : solidC .plus (Sum.inr a : Atom k m) (Sum.inr b) =
        mkC (.G .plus) (Sum.inr a) (Sum.inr b) := by simp [solidC, hne]
    rw [hs] at hmem
    exact Graph.netT_reach_of_mem _ _ _ (List.mem_append_right _
      (newT_mem hmem (by simp [mkC, Kind.blueC, hbc]))) rfl rfl rfl

/-- The main term of the `GG` expansion: the edges `G_{x y}` and `G_{y' x}` are replaced by
`G_{y' y}` and a waved edge `S⁺_{x y}`. -/
private theorem ggMain_dcs {bc : Charge} {L : List (TC k n)} {co : Coeff}
    (hL : (Graph.mk (L.map Prod.fst) co).DCT bc L) {x₀ : Fin n} {i j : ℕ}
    (hiL : i < L.length) (hjL : j < L.length) (hki : L[i].1.kind = .G .plus)
    (hxi : L[i].1.x = Sum.inr x₀) (hkj : L[j].1.kind = .G .plus)
    (hyj : L[j].1.y = Sum.inr x₀) (hyi : bc = .plus → ∃ b, L[i].1.y = Sum.inr b)
    {Γ' : Graph k n}
    (hΓ' : Γ'.comps = eraseIdxs [i, j] (L.map Prod.fst) ++
      [solidC .plus L[j].1.x L[i].1.y, mkC (.waved .plus) (Sum.inr x₀) L[i].1.y]) :
    Γ'.DCS bc := by
  refine ⟨liftT 0 (eraseIdxs [i, j] L) ++
    newT bc [solidC .plus L[j].1.x L[i].1.y, mkC (.waved .plus) (Sum.inr x₀) L[i].1.y],
    hL.shapeE (j := 0) (Γ' := Γ') (eraseIdxs [i, j] L)
      [solidC .plus L[j].1.x L[i].1.y, mkC (.waved .plus) (Sum.inr x₀) L[i].1.y] ?_
      (fun q hq => mem_eraseIdxs_subset hq) ?_ (fun w => ⟨w, Or.inl rfl⟩)⟩
  · rw [hΓ']
    simp [liftT_zero_map_fst, newT_map_fst, eraseIdxs_map]
  · intro p hp hpS
    rcases mem_eraseIdxs_or (is := [i, j]) hp with h | ⟨i', hi', hi'L, rfl⟩
    · exact absurd h hpS
    have hSp : ∀ b, L[i].1.y = Sum.inr b → Γ'.SameMol (Sum.inr x₀) (Sum.inr b) := by
      intro b hb
      refine Graph.sameMol_of_waved' (w := .plus) ?_
      rw [← hb, hΓ']
      mem_tail
    rcases List.mem_cons.1 hi' with rfl | hi'
    · refine ⟨⟨by rw [hki]; rfl, ?_⟩, ?_⟩
      · intro hp2
        have := hL.black _ hp hp2
        rw [hki] at this
        exact absurd this (by simp [Kind.isDiffusive])
      · intro hpt a b hx' hy'
        have hxa : x₀ = a := by
          rw [hxi] at hx'
          exact Sum.inr_injective hx'
        subst hxa
        exact Graph.netT_reach_of_sameMol _ _ _ (hSp b hy')
    · rw [List.mem_singleton] at hi'
      subst i'
      refine ⟨⟨by rw [hkj]; rfl, ?_⟩, ?_⟩
      · intro hp2
        have := hL.black _ hp hp2
        rw [hkj] at this
        exact absurd this (by simp [Kind.isDiffusive])
      · intro hpt a b hx' hy'
        have hb := hL.blue _ hp hpt
        rw [hkj] at hb
        have hbc : bc = .plus := by
          rcases hb with hb | hb
          · simp [Kind.isDiffusive] at hb
          · exact (by simpa [Kind.blueC] using hb : Charge.plus = bc).symm
        have hbx : x₀ = b := by
          rw [hyj] at hy'
          exact Sum.inr_injective hy'
        subst hbx
        obtain ⟨b₁, hb₁⟩ := hyi hbc
        have h1 : (Γ'.netT (liftT 0 (eraseIdxs [i, j] L) ++ newT bc
            [solidC .plus L[j].1.x L[i].1.y, mkC (.waved .plus) (Sum.inr x₀) L[i].1.y])
            true).Reachable a b₁ := by
          refine reach_of_solidC (Γ' := Γ') (X := liftT 0 (eraseIdxs [i, j] L)) ?_ hbc
          rw [hx', hb₁]
          mem_cs
        exact h1.trans (Graph.netT_reach_of_sameMol _ _ _
          ((Graph.sameMol_equivalence Γ').symm (hSp b₁ hb₁)))

private theorem ggPos_dcs {bc : Charge} {Γ : Graph k n} (x : Atom k n)
    (hx : x.isRight = true) (h : Γ.DCS bc)
    (hy : ∀ c ∈ Γ.comps, bc = .plus → c.kind = .G .plus → c.x = x → c.y.isRight = true)
    {E : TExpansion k n} (hE : ggPos x Γ = some E) :
    ∀ t ∈ E, t.g.DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀, x = Sum.inr x₀ := by
    cases x with
    | inl a => simp at hx
    | inr a => exact ⟨a, rfl⟩
  obtain ⟨L, hL⟩ := h
  obtain ⟨cs, co⟩ := Γ
  obtain rfl : cs = L.map Prod.fst := hL.map_fst.symm
  unfold ggPos at hE
  dsimp only at hE
  split at hE
  · simp at hE
  split at hE
  rotate_left
  · simp at hE
  rename_i i j hij hij'
  rcases he : (L.map Prod.fst)[i]? with _ | e
  · rw [he] at hE; simp at hE
  rcases he' : (L.map Prod.fst)[j]? with _ | e'
  · rw [he, he'] at hE; simp at hE
  rw [he, he'] at hE
  dsimp only at hE
  split at hE
  · simp at hE
  simp only [Option.some.injEq] at hE
  subst hE
  have himem : i ∈ (Graph.mk (L.map Prod.fst) co).edgeIdx (Sum.inr x₀) .plus true := by
    rw [hij]; exact List.mem_singleton_self _
  have hjmem : j ∈ (Graph.mk (L.map Prod.fst) co).edgeIdx (Sum.inr x₀) .plus false := by
    rw [hij']; exact List.mem_singleton_self _
  obtain ⟨hiL, hki, hxi', -⟩ := mem_edgeIdx_T himem
  obtain ⟨hjL, hkj, -, hyj'⟩ := mem_edgeIdx_T hjmem
  have hxi : L[i].1.x = Sum.inr x₀ := (hxi' rfl).1
  have hyj : L[j].1.y = Sum.inr x₀ := (hyj' rfl).1
  have hne : i ≠ j := by
    rintro rfl
    exact (hxi' rfl).2 hyj
  have he₁ : e = L[i].1 := by
    have := he
    simp [List.getElem?_eq_getElem hiL] at this
    exact this.symm
  have he₂ : e' = L[j].1 := by
    have := he'
    simp [List.getElem?_eq_getElem hjL] at this
    exact this.symm
  subst he₁ he₂
  have hyi : bc = .plus → ∃ b, L[i].1.y = Sum.inr b := by
    intro hbc
    have := hy L[i].1 (List.mem_map_of_mem (List.getElem_mem hiL)) hbc hki hxi
    cases hyy : L[i].1.y with
    | inl a => rw [hyy] at this; simp at this
    | inr b => exact ⟨b, rfl⟩
  intro t ht
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ht
  rcases ht with (((((rfl | rfl | rfl | rfl | rfl) | ⟨a, ⟨a₁, hd, rfl⟩, rfl⟩) |
    ⟨a, ⟨a₁, hd, rfl⟩, rfl⟩) | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    ⟨a, ⟨a₁, hd, rfl⟩, rfl⟩) | ⟨a, ⟨a₁, hd, rfl⟩, rfl⟩
  · exact ⟨ggMain_dcs hL hiL hjL hki hxi hkj hyj hyi (by rw [List.append_assoc]; rfl),
      fun u => rfl⟩
  · refine ⟨hL.addAtoms _ rfl ?_, fun u => liftA_isRight u⟩
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨shapeR hL [i, j] _ x₀ rfl (redir_pair hiL hjL hki hxi hkj hyj
      (wi := Fin.natAdd n 0) (wj := Fin.natAdd n 0) ?_ ?_ ?_ ?_) ?_, fun u => liftA_isRight u⟩
    · exact Graph.sameMol_of_waved' (w := .plus) (by mem_tail)
    · exact Graph.sameMol_of_waved' (w := .plus) (by mem_tail)
    · mem_cs
    · mem_cs
    · exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨shapeR hL [i, j] _ x₀ rfl (redir_pair hiL hjL hki hxi hkj hyj
      (wi := Fin.natAdd n 0) (wj := Fin.natAdd n 0) ?_ ?_ ?_ ?_) ?_, fun u => liftA_isRight u⟩
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · mem_cs
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · have hl : ∀ {Γ' : Graph k (n + 2)}, Γ'.SameMol (Sum.inr (Fin.castAdd 2 x₀)) (newA 0) →
        Γ'.SameMol (newA 0) (newA 1) →
        Γ'.SameMol (Sum.inr (Fin.castAdd 2 x₀)) (Sum.inr (Fin.natAdd n 1)) :=
      fun h1 h2 => (Graph.sameMol_equivalence _).trans h1 h2
    refine ⟨shapeR hL [i, j] _ x₀ rfl (redir_pair hiL hjL hki hxi hkj hyj
      (wi := Fin.natAdd n 1) (wj := Fin.natAdd n 1)
      (hl (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail)))
      (hl (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))) ?_ ?_) ?_,
      fun u => liftA_isRight u⟩
    · mem_cs
    · mem_cs
    · exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨shapeRD0 hL [i, j] _ a₁ x₀ (Fin.natAdd n 0) (Fin.castAdd 1 x₀) hd
      (by rw [List.append_assoc]) ?_ ?_ ?_, fun u => liftA_isRight u⟩
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · exact redir_pair hiL hjL hki hxi hkj hyj (wi := Fin.natAdd n 0) (wj := Fin.castAdd 1 x₀)
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail)) (Or.inl rfl) (by mem_cs) (by mem_cs)
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨shapeRD0 hL [i, j] _ a₁ x₀ (Fin.natAdd n 1) (Fin.natAdd n 0) hd
      (by rw [List.append_assoc]) ?_ ?_ ?_, fun u => liftA_isRight u⟩
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · exact redir_pair hiL hjL hki hxi hkj hyj (wi := Fin.natAdd n 1) (wj := Fin.natAdd n 0)
        ((Graph.sameMol_equivalence _).trans
          (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
          (Graph.sameMol_of_waved' (w := .s) (by mem_tail)))
        (Graph.sameMol_of_waved' (w := .plus) (by mem_tail)) (by mem_cs) (by mem_cs)
    · exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · exact ⟨Graph.DCS.labelQ ⟨L, hL⟩ _ rfl, fun u => rfl⟩
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine shapeR hL [i, j] _ x₀ (by rw [List.append_assoc]) (redir_pair hiL hjL hki hxi hkj hyj
      (wi := Fin.natAdd n 0) (wj := Fin.natAdd n 0) ?_ ?_ ?_ ?_) ?_
    · exact Graph.sameMol_of_waved' (w := .plus) (by mem_tail)
    · exact Graph.sameMol_of_waved' (w := .plus) (by mem_tail)
    · mem_cs
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => rfl⟩
    exact ggMain_dcs hL hiL hjL hki hxi hkj hyj hyi (by rw [List.append_assoc]; rfl)
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine hL.addAtoms _ (by rw [List.append_assoc]) ?_
    exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine shapeR hL [i, j] _ x₀ (by rw [List.append_assoc]) (redir_pair hiL hjL hki hxi hkj hyj
      (wi := Fin.natAdd n 0) (wj := Fin.natAdd n 0) ?_ ?_ ?_ ?_) ?_
    · exact Graph.sameMol_of_waved' (w := .plus) (by mem_tail)
    · exact Graph.sameMol_of_waved' (w := .plus) (by mem_tail)
    · mem_cs
    · mem_cs
    · exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine shapeR hL [i, j] _ x₀ (by rw [List.append_assoc]) (redir_pair hiL hjL hki hxi hkj hyj
      (wi := Fin.natAdd n 0) (wj := Fin.natAdd n 0) ?_ ?_ ?_ ?_) ?_
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · exact Graph.sameMol_of_waved' (w := .s) (by mem_tail)
    · mem_cs
    · mem_cs
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · have hl : ∀ {Γ' : Graph k (n + 2)}, Γ'.SameMol (Sum.inr (Fin.castAdd 2 x₀)) (newA 0) →
        Γ'.SameMol (newA 0) (newA 1) →
        Γ'.SameMol (Sum.inr (Fin.castAdd 2 x₀)) (Sum.inr (Fin.natAdd n 1)) :=
      fun h1 h2 => (Graph.sameMol_equivalence _).trans h1 h2
    refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine shapeR hL [i, j] _ x₀ (by rw [List.append_assoc]) (redir_pair hiL hjL hki hxi hkj hyj
      (wi := Fin.natAdd n 1) (wj := Fin.natAdd n 1)
      (hl (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail)))
      (hl (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))) ?_ ?_) ?_
    · mem_cs
    · mem_cs
    · exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine shapeRD0 hL [i, j] _ a₁ x₀ (Fin.natAdd n 0) (Fin.castAdd 1 x₀) hd
      (by rw [List.append_assoc]) ?_ ?_ ?_
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · exact redir_pair hiL hjL hki hxi hkj hyj (wi := Fin.natAdd n 0) (wj := Fin.castAdd 1 x₀)
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail)) (Or.inl rfl) (by mem_cs) (by mem_cs)
    · exact hnew₁ x₀ (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
  · refine ⟨Graph.DCS.labelQ_append (Γ := ⟨_ ++ _, co⟩) ?_ _ _ _
      (by simp [mkC, Kind.isRandom]) rfl rfl, fun u => liftA_isRight u⟩
    refine shapeRD0 hL [i, j] _ a₁ x₀ (Fin.natAdd n 1) (Fin.natAdd n 0) hd
      (by rw [List.append_assoc]) ?_ ?_ ?_
    · exact (Graph.sameMol_equivalence _).symm (Graph.sameMol_of_waved' (w := .s) (by mem_tail))
    · exact redir_pair hiL hjL hki hxi hkj hyj (wi := Fin.natAdd n 1) (wj := Fin.natAdd n 0)
        ((Graph.sameMol_equivalence _).trans
          (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
          (Graph.sameMol_of_waved' (w := .s) (by mem_tail)))
        (Graph.sameMol_of_waved' (w := .plus) (by mem_tail)) (by mem_cs) (by mem_cs)
    · exact hnew₂ x₀ (Graph.sameMol_of_waved' (w := .plus) (by mem_tail))
        (Graph.sameMol_of_waved' (w := .s) (by mem_tail))

end GG

section Final

variable {k n : ℕ}

/-- A tracked graph with a doubly connected structure, whose atom map keeps internal atoms
internal. -/
private def Good (bc : Charge) (t : Tracked k n) : Prop :=
  t.g.DCS bc ∧ ∀ u, (t.f u).isRight = u.isRight

private theorem good_self {bc : Charge} {Γ : Graph k n} (h : Γ.DCS bc) :
    Good bc (Tracked.self Γ) := ⟨h, fun _ => rfl⟩

private theorem flip_flip' (bc : Charge) : bc.flip.flip = bc := by cases bc <;> rfl

private theorem good_conj {bc : Charge} {t : Tracked k n} (h : Good bc.flip t) :
    Good bc ⟨t.nOut, t.g.conj, t.f⟩ := by
  refine ⟨?_, h.2⟩
  have := h.1.conj
  rwa [flip_flip'] at this

private theorem oWeight1T_good (x : Atom k n) {bc : Charge} {Γ : Graph k n} (h : Γ.DCS bc) :
    ∀ t ∈ oWeight1T x Γ, Good bc t := by
  intro t ht
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨L, hL⟩ := h
  obtain ⟨L', h1, h2, h3⟩ := splitRegular_tagged x L p (hL.map_fst ▸ hp)
  refine ⟨⟨L', hL.of_retain L' h1 h3 ?_⟩, fun _ => rfl⟩
  intro q hq hqq
  refine h2 q hq ?_
  rcases hqq with hqq | hqq
  · cases hk : q.1.kind <;> simp_all [Kind.joinsMol, Kind.isWeight]
  · rcases hL.kind_of_tag hq hqq with hh | hh <;>
      cases hk : q.1.kind <;> simp_all [Kind.isDiffusive, Kind.blueC, Kind.isWeight]

private theorem oWeight2T_good (x : Atom k n) (hx : x.isRight = true) {Γ : Graph k n}
    (h : Γ.DCS .plus) : ∀ t ∈ oWeight2T x Γ, Good .plus t := by
  intro t ht
  unfold oWeight2T at ht
  split_ifs at ht with hp
  · obtain rfl := List.mem_singleton.1 ht
    exact good_self h
  · split at ht
    · rename_i E hE
      exact oWeight2Pos_dcs x hx h hE t ht
    · split at ht
      · rename_i E hE
        obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
        exact good_conj (oWeight2Pos_dcs (bc := Charge.plus.flip) x hx h.conj hE t₀ ht₀)
      · obtain rfl := List.mem_singleton.1 ht
        exact good_self h

private theorem bind_good {bc : Charge} {E : TExpansion k n} (hE : ∀ t ∈ E, Good bc t)
    (O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n')
    (hO : ∀ {n' : ℕ} (f : Atom k n → Atom k n') (g : Graph k n'),
      (∀ u, (f u).isRight = u.isRight) → g.DCS bc → ∀ s ∈ O f g, Good bc s) :
    ∀ t ∈ E.bind O, Good bc t := by
  intro t ht
  unfold TExpansion.bind at ht
  obtain ⟨t₀, ht₀, hts⟩ := List.mem_flatMap.1 ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hts
  have h0 := hE t₀ ht₀
  have h1 := hO t₀.f t₀.g h0.2 h0.1 s hs
  exact ⟨h1.1, fun u => by simp [Function.comp, h1.2, h0.2]⟩

/-- `O^{(x)}_weight` keeps the doubly connected property. -/
private theorem oWeightT_good (x : Atom k n) (hx : x.isRight = true) {Γ : Graph k n}
    (h : Γ.DCS .plus) : ∀ t ∈ oWeightT x Γ, Good .plus t := by
  unfold oWeightT
  split_ifs with hc
  · refine bind_good (bind_good (bind_good (oWeight1T_good x h) _ ?_) _ ?_) _ ?_
    · intro n' f g hf hg s hs
      exact oWeight2T_good (f x) (by rw [hf, hx]) hg s hs
    · intro n' f g hf hg s hs
      exact oDotT_dcs hg s hs
    · intro n' f g hf hg s hs
      exact oWeight1T_good (f x) hg s hs
  · intro t ht
    obtain rfl := List.mem_singleton.1 ht
    exact good_self h

private theorem multiEHat_good (x : Atom k n) (hx : x.isRight = true) {Γ : Graph k n}
    (h : Γ.DCS .plus) {E : TExpansion k n} (hE : multiEHat x Γ = some E) :
    ∀ t ∈ E, Good .plus t := by
  unfold multiEHat at hE
  split_ifs at hE with h1 h2 h3 h4
  · exact multiEOut_dcs x hx h hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    intro t ht
    unfold TExpansion.conj at ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    exact good_conj (multiEOut_dcs (bc := Charge.plus.flip) x hx h.conj hE' t₀ ht₀)
  · exact multiEIn_dcs x hx h hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    intro t ht
    unfold TExpansion.conj at ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    exact good_conj (multiEIn_dcs (bc := Charge.plus.flip) x hx h.conj hE' t₀ ht₀)

/-- `O^{(x)}_multi-e` keeps the doubly connected property. -/
private theorem oMultiET_good (x : Atom k n) (hx : x.isRight = true) {Γ : Graph k n}
    (h : Γ.DCS .plus) : ∀ t ∈ oMultiET x Γ, Good .plus t := by
  intro t ht
  unfold oMultiET at ht
  split_ifs at ht with hp
  · obtain rfl := List.mem_singleton.1 ht
    exact good_self h
  · split at ht
    · rename_i E hE
      exact bind_good (multiEHat_good x hx h hE) (fun _ g => oDotT g)
        (fun f g hf hg s hs => oDotT_dcs hg s hs) t ht
    · obtain rfl := List.mem_singleton.1 ht
      exact good_self h

/-- `O^{(x)}_GG` keeps the doubly connected property when every blue edge leaving `x` ends at
an internal atom. -/
private theorem oGGT_good (x : Atom k n) (hx : x.isRight = true) {Γ : Graph k n}
    (h : Γ.DCS .plus)
    (hy : ∀ c ∈ Γ.comps, c.kind = .G .plus → c.x = x → c.y.isRight = true) :
    ∀ t ∈ oGGT x Γ, Good .plus t := by
  intro t ht
  unfold oGGT at ht
  split_ifs at ht with hp
  · obtain rfl := List.mem_singleton.1 ht
    exact good_self h
  · split at ht
    · rename_i E hE
      exact bind_good (ggPos_dcs x hx h (fun c hc _ hk hxc => hy c hc hk hxc) hE)
        (fun _ g => oDotT g) (fun f g hf hg s hs => oDotT_dcs hg s hs) t ht
    · split at ht
      · rename_i E hE
        refine bind_good (E := TExpansion.conj E) ?_ (fun _ g => oDotT g)
          (fun f g hf hg s hs => oDotT_dcs hg s hs) t ht
        intro t' ht'
        unfold TExpansion.conj at ht'
        obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht'
        exact good_conj (ggPos_dcs (bc := Charge.plus.flip) x hx h.conj
          (fun c hc hb => absurd hb (by decide)) hE t₀ ht₀)
      · obtain rfl := List.mem_singleton.1 ht
        exact good_self h

/-- `O^{(x)}_GḠ` keeps the doubly connected property. -/
private theorem oGGbarT_good (x : Atom k n) (hx : x.isRight = true) {Γ : Graph k n}
    (h : Γ.DCS .plus) : ∀ t ∈ oGGbarT x Γ, Good .plus t := by
  intro t ht
  unfold oGGbarT at ht
  dsimp only at ht
  split_ifs at ht with hp
  · exact oMultiET_good x hx h t ht
  · obtain rfl := List.mem_singleton.1 ht
    exact good_self h

end Final

/-- **[II, Lemma 4.10]**: the local expansions keep the doubly connected property ([II, Def 2.12]).
For a doubly connected graph `Γ`, the graphs of `O_dot` on a regular graph, and of
`O^{(x)}_weight`, `O^{(x)}_multi-e`, `O^{(x)}_GG`, `O^{(x)}_GḠ` on a normal regular graph at an
internal atom `x`, are doubly connected; for `O^{(x)}_GG` every blue solid edge `G_{x y}` leaving
`x` ends at an internal atom `y`. -/
theorem localDoublyConnected (k n C : ℕ) (x : Atom k n) (Γ : Graph k n) :
    Γ.DoublyConnected →
    (Γ.Regular C → ∀ t ∈ oDotT Γ, t.g.DoublyConnected) ∧
    (x.isRight = true → Γ.Normal C → ∀ t ∈ oWeightT x Γ, t.g.DoublyConnected) ∧
    (x.isRight = true → Γ.Normal C → ∀ t ∈ oMultiET x Γ, t.g.DoublyConnected) ∧
    (x.isRight = true → Γ.Normal C →
      (∀ c ∈ Γ.comps, c.kind = .G .plus → c.x = x → c.y.isRight = true) →
      ∀ t ∈ oGGT x Γ, t.g.DoublyConnected) ∧
    (x.isRight = true → Γ.Normal C → ∀ t ∈ oGGbarT x Γ, t.g.DoublyConnected) := by
  intro h
  have hs : Γ.DCS .plus := Graph.doublyConnected_dcs h
  refine ⟨fun _ t ht => (oDotT_dcs hs t ht).1.doublyConnected,
    fun hx _ t ht => (oWeightT_good x hx hs t ht).1.doublyConnected,
    fun hx _ t ht => (oMultiET_good x hx hs t ht).1.doublyConnected,
    fun hx _ hy t ht => (oGGT_good x hx hs hy t ht).1.doublyConnected,
    fun hx _ t ht => (oGGbarT_good x hx hs t ht).1.doublyConnected⟩

section Instances

end Instances

end RBM8D.Graphs
