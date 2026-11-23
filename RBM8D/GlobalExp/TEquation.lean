module

public import RBM8D.GlobalExp.TEqIdentity
public import RBM8D.GlobalExp.TEqCorrShape
public import RBM8D.GlobalExp.RunOutFacts
public import RBM8D.TExp.Second
public import Batteries.Tactic.OpenPrivate
import all RBM8D.GlobalExp.TEqIdentity
import all RBM8D.TExp.Second

@[expose] public section

/-!
# The `n`-th order `T`-equation: [II, Theorem 3.7]

**[II, Theorem 3.7] = [I, Lemma 5.7]** in the parallel form [II, (6.8)–(6.9)] (`tEquation`), with
the construction `TEqSigma.Strat` of [II, (6.8)] read off the run of [II, Strategy 6.6]:

* the graphs of `R`, `A`, `Q`, `Err` of the `T`-equation have the graph properties of
  [II, Def 3.2] with labels of entries in `[4, n - 1]`, the form of [II, Def 3.3 (4)] and the
  clauses of [II, Def 6.3] (`TEquation_struct`);
* the graphs of order `≤ n - 1` of `R` and `Q` and the graphs of order `≤ n` of `R`, `A`, `Q` with
  `⊕`, `⊖` in one dotted block are those of the `(n - 1)`-th order `T`-equation ([II, (6.9)]);
* the graphs of order `≤ D` do not depend on the error order `D` ([II, Def 3.3 (1)]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private TEqIdentity_classes TEqIdentity_unp from RBM8D.GlobalExp.TEqIdentity

/-! ## Lists -/

section Lists

variable {β : Type*}

/-- The count of an element in a filtered list. -/
private theorem TEquation_count_filter [DecidableEq β] (p : β → Bool) (l : List β) (a : β) :
    (l.filter p).count a = if p a = true then l.count a else 0 := by
  split_ifs with h
  · exact List.count_filter h
  · refine List.count_eq_zero.2 fun hm => h ?_
    exact (List.mem_filter.1 hm).2

/-- Two filtered lists agree up to order when the counts of every element agree. -/
private theorem TEquation_filter_perm [DecidableEq β] {l l' : List β} {p p' : β → Bool}
    (h : ∀ a, (if p a = true then l.count a else 0) = if p' a = true then l'.count a else 0) :
    (l.filter p).Perm (l'.filter p') := by
  refine List.perm_iff_count.2 fun a => ?_
  rw [TEquation_count_filter, TEquation_count_filter]
  exact h a

/-- A `flatMap` that vanishes outside a predicate is the `flatMap` of the filtered list. -/
private theorem TEquation_flatMap_filter {γ : Type*} (L : List β) (h : β → List γ) (r : β → Bool)
    (hr : ∀ g ∈ L, r g = false → h g = []) : L.flatMap h = (L.filter r).flatMap h := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ih' := ih fun g hg => hr g (List.mem_cons_of_mem _ hg)
    by_cases ha : r a = true
    · simp [ha, ih']
    · simp only [Bool.not_eq_true] at ha
      simp [ha, hr a (by simp) ha, ih']

/-- A list is its part before the index `j`, its entry at `j` and its part after `j`. -/
private theorem TEquation_split (l : List β) (j : Fin l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  conv_lhs => rw [← List.take_append_drop j l, List.drop_eq_getElem_cons j.2]
  rfl

/-- An element of a list other than its entry at `j` is in the list with the entry `j` removed. -/
private theorem TEquation_mem_eraseIdx {l : List β} (j : Fin l.length) {d : β} (hd : d ∈ l)
    (hne : d ≠ l[j]) : d ∈ l.eraseIdx j := by
  rw [List.eraseIdx_eq_take_drop_succ]
  rw [TEquation_split l j, List.mem_append, List.mem_cons] at hd
  rcases hd with hd | hd | hd
  · exact List.mem_append_left _ hd
  · exact absurd hd hne
  · exact List.mem_append_right _ hd

/-- An element of the list with the entry `j` removed is in the list. -/
private theorem TEquation_mem_of_eraseIdx {l : List β} {j : ℕ} {d : β} (hd : d ∈ l.eraseIdx j) :
    d ∈ l :=
  List.mem_of_mem_eraseIdx hd

end Lists

/-! ## Walks -/

section Walks

/-- Reachability is carried by a map that sends every related pair to two atoms joined by a
path. -/
private theorem TEquation_reach_map {V W : Type*} {r : V → V → Prop} {G : SimpleGraph W}
    (f : V → W) (h : ∀ a b, r a b → G.Reachable (f a) (f b)) {u v : V}
    (huv : (SimpleGraph.fromRel r).Reachable u v) : G.Reachable (f u) (f v) := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab _ ih =>
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with h' | h'
    · exact (h _ _ h').trans ih
    · exact (h _ _ h').symm.trans ih

/-- Two atoms in the relation are joined by a path. -/
private theorem TEquation_reach_rel {W : Type*} {r : W → W → Prop} {u v : W} (h : r u v) :
    (SimpleGraph.fromRel r).Reachable u v := by
  by_cases huv : u = v
  · subst huv; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨huv, Or.inl h⟩)

/-- A walk from a set to its complement has a related pair with one end in the set and one
outside. -/
private theorem TEquation_reach_cross {V : Type*} {r : V → V → Prop} {P : V → Prop} {u v : V}
    (h : (SimpleGraph.fromRel r).Reachable u v) (hu : P u) (hv : ¬ P v) :
    ∃ a b, r a b ∧ (P a ∧ ¬ P b ∨ P b ∧ ¬ P a) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact absurd hu hv
  | @cons a b c hab _ ih =>
    by_cases hb : P b
    · exact ih hb hv
    · rw [SimpleGraph.fromRel_adj] at hab
      rcases hab.2 with h | h
      · exact ⟨a, b, h, Or.inl ⟨hu, hb⟩⟩
      · exact ⟨b, a, h, Or.inr ⟨hu, hb⟩⟩

end Walks

/-! ## Pinned external atoms, `Graph.RgCheck`, [II, Def 3.2 (9)] -/

section Pinned

variable {N : ℕ} {Γ : Graph 3 N}

/-- An external atom whose dotted block has an internal atom gives a dotted edge between an
internal and an external atom. -/
private theorem TEquation_cross_dot {w : Atom 3 N} (hw : w.isLeft = true) (h : ¬ Γ.Unpinned w) :
    ∃ c ∈ Γ.comps, c.kind = .dot ∧
      (c.x.isRight = true ∧ c.y.isLeft = true ∨ c.x.isLeft = true ∧ c.y.isRight = true) := by
  have hb : ∃ b : Fin N, Γ.SameBlock w (.inr b) := by
    by_contra hb
    exact h ⟨hw, fun b hb' => hb ⟨b, hb'⟩⟩
  obtain ⟨b, hb⟩ := hb
  obtain ⟨u, v, ⟨c, hc, hd, rfl, rfl⟩, hcr⟩ :=
    TEquation_reach_cross (P := fun a : Atom 3 N => a.isLeft = true) hb hw (by simp)
  refine ⟨c, hc, hd, ?_⟩
  rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right
    refine ⟨h1, ?_⟩
    rcases hy : c.y with y | y
    · rw [hy] at h2; simp at h2
    · rfl
  · left
    refine ⟨?_, h1⟩
    rcases hx : c.x with x | x
    · rw [hx] at h2; simp at h2
    · rfl

/-- An external atom whose dotted block has an internal atom carries a dotted edge. -/
private theorem TEquation_dot_at {a : Fin 3} (h : ¬ Γ.Unpinned (.inl a)) :
    ∃ c ∈ Γ.comps, c.kind = .dot ∧ (c.x = .inl a ∨ c.y = .inl a) := by
  have hb : ∃ b : Fin N, Γ.SameBlock (.inl a) (.inr b) := by
    by_contra hb
    exact h ⟨rfl, fun b hb' => hb ⟨b, hb'⟩⟩
  obtain ⟨b, ⟨w⟩⟩ := hb
  cases w with
  | cons hadj _ =>
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with ⟨c, hc, hd, hx, -⟩ | ⟨c, hc, hd, -, hy⟩
    · exact ⟨c, hc, hd, Or.inl hx⟩
    · exact ⟨c, hc, hd, Or.inr hy⟩

/-- **The clause `Graph.RgCheck` from the clause on the external atoms**: some waved, diffusive or
dotted edge joins an internal and an external atom (the diffusive edge at `⊗` to an internal or
identified atom, or a dotted edge out of the block of an identified atom). -/
private theorem TEquation_rgCheck (hE : Γ.ExtClause) : Γ.RgCheck := by
  right
  have hdot : ∀ w : Atom 3 N, w.isLeft = true → ¬ Γ.Unpinned w →
      ∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧
        (c.x.isRight = true ∧ c.y.isLeft = true ∨ c.x.isLeft = true ∧ c.y.isRight = true) := by
    intro w hw hU
    obtain ⟨c, hc, hd, h⟩ := TEquation_cross_dot hw hU
    exact ⟨c, hc, Or.inl (by rw [hd]; rfl), h⟩
  by_cases hU : Γ.Unpinned (.inl 0)
  · obtain ⟨⟨c, hc, hd, h⟩, -⟩ := hE.2.2.1 hU
    rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · rcases hcy : c.y with y | y
      · rw [hcy] at hy
        exact hdot _ rfl hy
      · exact ⟨c, hc, Or.inr hd, Or.inr ⟨by rw [hx]; rfl, by rw [hcy]; rfl⟩⟩
    · rcases hcx : c.x with x | x
      · rw [hcx] at hx
        exact hdot _ rfl hx
      · exact ⟨c, hc, Or.inr hd, Or.inl ⟨by rw [hcx]; rfl, by rw [hy]; rfl⟩⟩
  · exact hdot _ rfl hU

/-- **[II, Def 3.2 (9)] from the form at `⊗`, the clause on the external atoms and the edge at
`⊖`**: a graph whose only component at `⊗` is a `Θ` edge from `⊗`, with the clause on the
external atoms (`⊕` unpinned: a blue solid or a diffusive edge at `⊕`; `⊕` pinned: a dotted edge at
`⊕`) and a red solid, diffusive or dotted edge at `⊖`. -/
private theorem TEquation_atExt
    (hO : ∃ (j : Fin Γ.comps.length) (v : Atom 3 N), v ≠ .inl 0 ∧
        Γ.comps[j].kind = .theta [] ∧ Γ.comps[j].minor = [] ∧ Γ.comps[j].label = none ∧
        (Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v) ∧
        ∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0)
    (hE : Γ.ExtClause)
    (hM : Γ.comps.any (fun c => (c.kind == .G .minus || c.kind.isDiffusive || c.kind == .dot) &&
        (c.x == .inl 2 || c.y == .inl 2)) = true) : Γ.AtExternals := by
  refine ⟨?_, ?_, hM⟩
  · obtain ⟨j, v, -, hk, -, -, ⟨hx, -⟩, hrest⟩ := hO
    have hz : ∀ c ∈ Γ.comps.take j ++ Γ.comps.drop (j + 1),
        (c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0)) = false := by
      intro c hc
      have h := hrest c (by simpa [Graph.dropComp, List.eraseIdx_eq_take_drop_succ] using hc)
      simp [h.1, h.2]
    rw [TEquation_split Γ.comps j, List.filter_append, List.filter_cons]
    rw [List.filter_eq_nil_iff.2 fun c hc => by
      rw [hz c (List.mem_append_left _ hc)]; simp]
    rw [List.filter_eq_nil_iff.2 fun c hc => by
      rw [hz c (List.mem_append_right _ hc)]; simp]
    have hk' : Γ.comps[(j : ℕ)].kind = .theta [] := hk
    have hx' : Γ.comps[(j : ℕ)].x = .inl 0 := hx
    simp [hk', hx', Kind.isDiffusive]
  · by_cases hU : Γ.Unpinned (.inl 1)
    · obtain ⟨h, -, -⟩ := hE.2.2.2.2 hU
      rcases h with ⟨c, hc, hk, h⟩ | ⟨c, hc, hd, h⟩
      · refine List.any_eq_true.2 ⟨c, hc, ?_⟩
        rcases h with h | h <;> simp [hk, h]
      · refine List.any_eq_true.2 ⟨c, hc, ?_⟩
        rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [hd, h]
    · obtain ⟨c, hc, hd, h⟩ := TEquation_dot_at hU
      refine List.any_eq_true.2 ⟨c, hc, ?_⟩
      rcases h with h | h <;> simp [hd, h]

end Pinned

/-! ## [II, Def 3.3 (4)] on a graph with one `Θ` edge at `⊗` -/

section Rooted

/-- A graph is normal regular when it is the image of a normal regular graph under a surjective
atom map `ρ` that carries every component to a loop or to the ends of a component, and under an
atom map `ρ₂` onto the internal atoms that carries every component to a loop or to a component of
the same kind, provided the local clauses of normal regularity hold. -/
private theorem TEquation_normal_of {k n k' n' C : ℕ} {Γ : Graph k n} {Γ' : Graph k' n'}
    (hN : Γ.Normal C) (ρ ρ₂ : Atom k n → Atom k' n') (hsurj : ∀ u, ∃ v, ρ v = u)
    (hE : ∀ c ∈ Γ.comps, ρ c.x = ρ c.y ∨ ∃ c' ∈ Γ'.comps, c'.x = ρ c.x ∧ c'.y = ρ c.y)
    (hint : ∀ a : Fin n', ∃ b : Fin n, ρ₂ (.inr b) = .inr a)
    (hW : ∀ c ∈ Γ.comps, ρ₂ c.x = ρ₂ c.y ∨
      ∃ c' ∈ Γ'.comps, c'.kind = c.kind ∧ c'.x = ρ₂ c.x ∧ c'.y = ρ₂ c.y)
    (h1 : ∀ c ∈ Γ'.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    (h2 : ∀ c ∈ Γ'.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (h3 : ∀ u v : Atom k' n', u ≠ v →
      ((∃ c ∈ Γ'.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ Γ'.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)))) :
    ∃ C', Γ'.Normal C' := by
  refine ⟨k' + n' + Γ'.comps.length, ⟨le_rfl, fun u' v' => ?_, fun a b => ?_, h1⟩, h2, h3⟩
  · obtain ⟨u, rfl⟩ := hsurj u'
    obtain ⟨v, rfl⟩ := hsurj v'
    refine TEquation_reach_map ρ (fun a b hab => ?_) (hN.1.connected u v)
    obtain ⟨c, hc, rfl, rfl⟩ := hab
    rcases hE c hc with h | ⟨c', hc', hx, hy⟩
    · rw [h]
    · rw [← hx, ← hy]
      exact TEquation_reach_rel ⟨c', hc', rfl, rfl⟩
  · obtain ⟨a', ha⟩ := hint a
    obtain ⟨b', hb⟩ := hint b
    rw [← ha, ← hb]
    refine TEquation_reach_map ρ₂ (fun u v huv => ?_) (hN.1.internal a' b')
    obtain ⟨c, hc, hk, rfl, rfl⟩ := huv
    rcases hW c hc with h | ⟨c', hc', hkk, hx, hy⟩
    · rw [h]
    · rw [← hx, ← hy]
      exact TEquation_reach_rel ⟨c', hc', hkk ▸ hk, rfl, rfl⟩

variable {N : ℕ} {Γ : Graph 3 N}

/-- With the `Θ` edge at `⊗` of index `j`, a component of another kind is a component of the
graph without the component `j`. -/
private theorem TEquation_mem_drop {j : Fin Γ.comps.length} (hk : Γ.comps[j].kind = .theta [])
    {d : Comp (Atom 3 N)} (hd : d ∈ Γ.comps) (hdk : d.kind ≠ .theta []) :
    d ∈ (Γ.dropComp j).comps :=
  TEquation_mem_eraseIdx j hd fun h => hdk (h ▸ hk)

/-- The index of an internal atom other than `i` after the removal of `i` determines the atom. -/
private theorem TEquation_finDrop_inj {i a b : Fin N} (ha : a ≠ i) (hb : b ≠ i)
    (h : finDrop i a ha = finDrop i b hb) : a = b := by
  have ha' := Fin.val_ne_of_ne ha
  have hb' := Fin.val_ne_of_ne hb
  unfold finDrop at h
  apply Fin.ext
  split_ifs at h with h1 h2 h2 <;> simp only [Fin.mk.injEq] at h <;> omega

/-- The atom map of `Graph.rootAt i`. -/
private def TEquation_rho (i : Fin N) : Atom 3 N → Atom 3 (N - 1)
  | .inl a => .inl a
  | .inr a => if h : a = i then .inl 0 else .inr (finDrop i a h)

/-- The components of `Graph.rootAt i` are the images under `TEquation_rho i`. -/
private theorem TEquation_rootAt_comps (Γ : Graph 3 N) (i : Fin N) :
    (Γ.rootAt i).comps = Γ.comps.map (Comp.map (TEquation_rho i)) := by
  simp only [Graph.rootAt, Graph.mapAtoms]
  congr 2

/-- `TEquation_rho i` is injective away from `⊗`. -/
private theorem TEquation_rho_inj {i : Fin N} {u w : Atom 3 N} (hu : u ≠ .inl 0)
    (hw : w ≠ .inl 0) (h : TEquation_rho i u = TEquation_rho i w) : u = w := by
  rcases u with a | a <;> rcases w with b | b
  · simpa [TEquation_rho] using h
  · by_cases hb : b = i
    · simp only [TEquation_rho, hb, ↓reduceDIte, Sum.inl.injEq] at h
      exact absurd (by rw [h]) hu
    · simp [TEquation_rho, hb] at h
  · by_cases ha : a = i
    · simp only [TEquation_rho, ha, ↓reduceDIte, Sum.inl.injEq] at h
      exact absurd (by rw [← h]) hw
    · simp [TEquation_rho, ha] at h
  · by_cases ha : a = i <;> by_cases hb : b = i
    · rw [ha, hb]
    · simp [TEquation_rho, ha, hb] at h
    · simp [TEquation_rho, ha, hb] at h
    · simp only [TEquation_rho, ha, hb, ↓reduceDIte, Sum.inr.injEq] at h
      rw [TEquation_finDrop_inj ha hb h]

/-- Every internal atom of `Graph.rootAt i` is the image of an internal atom other than `i`. -/
private theorem TEquation_rho_surj (i : Fin N) (k : Fin (N - 1)) :
    ∃ j, TEquation_rho i (.inr j) = .inr k := by
  have hk := k.2
  by_cases hlt : k.val < i.val
  · have hne : (⟨k.val, by omega⟩ : Fin N) ≠ i := fun h => by
      rw [Fin.ext_iff] at h; simp at h; omega
    refine ⟨⟨k.val, by omega⟩, ?_⟩
    simp only [TEquation_rho, hne, ↓reduceDIte, finDrop, hlt]
  · have hne : (⟨k.val + 1, by omega⟩ : Fin N) ≠ i := fun h => by
      rw [Fin.ext_iff] at h; simp at h; omega
    refine ⟨⟨k.val + 1, by omega⟩, ?_⟩
    have hlt' : ¬ k.val + 1 < i.val := by omega
    simp only [TEquation_rho, hne, ↓reduceDIte, finDrop, hlt', Nat.add_sub_cancel]

/-- The image of the ends of a component under a map that is injective on them. -/
private theorem TEquation_ends {V W : Type*} {f : V → W} {c d : Comp V} {u v : W}
    (hd : d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x)
    (hc : f c.x = u ∧ f c.y = v ∨ f c.x = v ∧ f c.y = u) :
    f d.x = u ∧ f d.y = v ∨ f d.x = v ∧ f d.y = u := by
  rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

/-- **[II, Def 3.3 (4)] on a graph with one plain `Θ` edge at `⊗`**: a normal regular graph whose
only component at `⊗` is a plain `Θ` edge `Θ_{⊗v}`, `v ≠ ⊗`, without minor and label, whose
components have no minor and whose label atoms are internal, or `⊕` without internal atoms, has the
form `∑_x Θ_{⊗x} 𝒢_{x, ⊕⊖}` with `𝒢` normal regular: for an internal `v` the graph `𝒢` is the rest
with `v` read as `⊗`; for an external `v` it is the rest with the dotted edge `⊗ = v`. -/
private theorem TEquation_thetaRooted {C : ℕ} (hN : Γ.Normal C)
    (hO : ∃ (j : Fin Γ.comps.length) (v : Atom 3 N), v ≠ .inl 0 ∧
        Γ.comps[j].kind = .theta [] ∧ Γ.comps[j].minor = [] ∧ Γ.comps[j].label = none ∧
        (Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v) ∧
        ∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0)
    (hL : ∀ c ∈ Γ.comps, ∀ (pq : PQ) (u : Atom 3 N), c.label = some (pq, u) →
        u.isRight = true ∨ (N = 0 ∧ u = .inl 1))
    (hM : ∀ c ∈ Γ.comps, c.minor = []) : Γ.ThetaRooted := by
  obtain ⟨j, v, hv, hk, hmj, hlj, ⟨hx, hy⟩, hrest⟩ := hO
  have hsub : ∀ c ∈ (Γ.dropComp j).comps, c ∈ Γ.comps := fun c hc =>
    TEquation_mem_of_eraseIdx hc
  refine ⟨j, v, hv, hk, hmj, hlj, ⟨hx, hy⟩, fun c hc => ⟨(hrest c hc).1, (hrest c hc).2, ?_, ?_⟩,
    ?_⟩
  · rw [hM c (hsub c hc)]
    exact List.not_mem_nil
  · intro h
    obtain ⟨⟨pq, u⟩, hl, hu⟩ := Option.map_eq_some_iff.1 h
    simp only at hu
    subst hu
    rcases hL c (hsub c hc) pq _ hl with h' | ⟨-, h'⟩
    · exact absurd h' (by simp)
    · exact absurd h' (by simp)
  -- the components of `Γ` are `Θ_{⊗v}` and the rest
  have hcases : ∀ c ∈ Γ.comps, c = Γ.comps[j] ∨ c ∈ (Γ.dropComp j).comps := by
    intro c hc
    by_cases h : c = Γ.comps[j]
    · exact Or.inl h
    · exact Or.inr (TEquation_mem_eraseIdx j hc h)
  have hNs := hN.2.1
  have hNx := hN.2.2
  rcases v with b | i
  · -- `v = b` external: the rest with the dotted edge `⊗ = b`
    have hb : b ≠ 0 := fun h => hv (by rw [h])
    have hx' : Γ.comps[(j : ℕ)].x = .inl 0 := hx
    have hy' : Γ.comps[(j : ℕ)].y = .inl b := hy
    let Γ' : Graph 3 N :=
      ⟨(Γ.dropComp j).comps ++ [mkC .dot (.inl 0) (.inl b)], (Γ.dropComp j).coeff⟩
    change ∃ C', Γ'.Normal C'
    have hmem : ∀ c ∈ Γ'.comps, c ∈ (Γ.dropComp j).comps ∨ c = mkC .dot (.inl 0) (.inl b) := by
      intro c hc
      simpa [Γ'] using hc
    have hmemr : ∀ c ∈ (Γ.dropComp j).comps, c ∈ Γ'.comps := fun c hc => by simp [Γ', hc]
    have hdotm : mkC .dot (.inl 0) (.inl b) ∈ Γ'.comps := by simp [Γ']
    refine TEquation_normal_of hN id (fun u => if u = .inl 0 then .inl b else u) (fun u => ⟨u, rfl⟩)
      (fun c hc => ?_) (fun a => ⟨a, by simp⟩) (fun c hc => ?_) (fun c hc hd => ?_)
      (fun c hc hs => ?_) (fun u w huw => ⟨?_, ?_⟩)
    · rcases hcases c hc with rfl | hc'
      · exact Or.inr ⟨_, hdotm, by simp [mkC, hx'], by simp [mkC, hy']⟩
      · exact Or.inr ⟨c, hmemr c hc', rfl, rfl⟩
    · rcases hcases c hc with rfl | hc'
      · left
        simp [hx', hy']
      · right
        refine ⟨c, hmemr c hc', rfl, ?_, ?_⟩
        · simp [(hrest c hc').1]
        · simp [(hrest c hc').2]
    · rcases hmem c hc with hc' | rfl
      · exact hN.1.noIntDot c (hsub c hc') hd
      · left; rfl
    · rcases hmem c hc with hc' | rfl
      · exact hNs c (hsub c hc') hs
      · simp [mkC, Kind.isSolid] at hs
    · rintro ⟨c, hc, hk', hends⟩
      rcases hmem c hc with hc' | rfl
      · obtain ⟨d, hd, hds, hde⟩ := (hNx u w huw).1 ⟨c, hsub c hc', hk', hends⟩
        refine ⟨d, hmemr d (TEquation_mem_drop hk hd fun h => by rw [h] at hds; cases hds), hds,
          hde⟩
      · simp [mkC] at hk'
    · rintro ⟨c, hc, hs, hends⟩
      rcases hmem c hc with hc' | rfl
      · obtain ⟨d, hd, hdk, hde⟩ := (hNx u w huw).2 ⟨c, hsub c hc', hs, hends⟩
        refine ⟨d, hmemr d (TEquation_mem_drop hk hd fun h => by rw [h] at hdk; cases hdk), hdk,
          hde⟩
      · simp [mkC, Kind.isSolid] at hs
  · -- `v = i` internal: the rest with `i` read as `⊗`
    let ρ := TEquation_rho (N := N) i
    change ∃ C', ((Γ.dropComp j).rootAt i).Normal C'
    have hcomps := TEquation_rootAt_comps (Γ.dropComp j) i
    have hmem : ∀ c' ∈ ((Γ.dropComp j).rootAt i).comps,
        ∃ c ∈ (Γ.dropComp j).comps, c' = c.map ρ := by
      intro c' hc'
      rw [hcomps] at hc'
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      exact ⟨c, hc, rfl⟩
    have hmemr : ∀ c ∈ (Γ.dropComp j).comps, c.map ρ ∈ ((Γ.dropComp j).rootAt i).comps :=
      fun c hc => by rw [hcomps]; exact List.mem_map_of_mem hc
    have hsurj : ∀ u, ∃ w, ρ w = u := by
      rintro (a | k)
      · exact ⟨.inl a, rfl⟩
      · obtain ⟨w, hw⟩ := TEquation_rho_surj i k
        exact ⟨_, hw⟩
    have hEW : ∀ c ∈ Γ.comps, ρ c.x = ρ c.y ∨ ∃ c' ∈ ((Γ.dropComp j).rootAt i).comps,
        c'.kind = c.kind ∧ c'.x = ρ c.x ∧ c'.y = ρ c.y := by
      intro c hc
      rcases hcases c hc with rfl | hc'
      · left
        rw [hx, hy]
        simp [ρ, TEquation_rho]
      · exact Or.inr ⟨c.map ρ, hmemr c hc', rfl, rfl, rfl⟩
    refine TEquation_normal_of hN ρ ρ hsurj (fun c hc => ?_) (fun a => ?_) hEW
      (fun c' hc' hd => ?_) (fun c' hc' hs => ?_) (fun u w huw => ⟨?_, ?_⟩)
    · rcases hEW c hc with h | ⟨c', hc', -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨c', hc', h⟩
    · obtain ⟨w, hw⟩ := TEquation_rho_surj i a
      exact ⟨w, hw⟩
    · obtain ⟨c, hc, rfl⟩ := hmem c' hc'
      rcases hN.1.noIntDot c (hsub c hc) hd with h | h
      · left
        rcases hcx : c.x with a | a
        · simp [Comp.map, hcx, ρ, TEquation_rho]
        · rw [hcx] at h; cases h
      · right
        rcases hcy : c.y with a | a
        · simp [Comp.map, hcy, ρ, TEquation_rho]
        · rw [hcy] at h; cases h
    · obtain ⟨c, hc, rfl⟩ := hmem c' hc'
      intro h
      exact hNs c (hsub c hc) hs
        (TEquation_rho_inj (hrest c hc).1 (hrest c hc).2 h)
    · rintro ⟨c', hc', hk', hends⟩
      obtain ⟨c, hc, rfl⟩ := hmem c' hc'
      have hne : c.x ≠ c.y := fun h => by
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact huw (by rw [← h1, ← h2]; simp [Comp.map, h])
        · exact huw (by rw [← h1, ← h2]; simp [Comp.map, h])
      obtain ⟨d, hd, hds, hde⟩ := (hNx c.x c.y hne).1 ⟨c, hsub c hc, hk', Or.inl ⟨rfl, rfl⟩⟩
      have hd' := TEquation_mem_drop hk hd fun h => by rw [h] at hds; cases hds
      exact ⟨d.map ρ, hmemr d hd', hds, TEquation_ends (f := ρ) hde hends⟩
    · rintro ⟨c', hc', hs, hends⟩
      obtain ⟨c, hc, rfl⟩ := hmem c' hc'
      have hne : c.x ≠ c.y := fun h => by
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact huw (by rw [← h1, ← h2]; simp [Comp.map, h])
        · exact huw (by rw [← h1, ← h2]; simp [Comp.map, h])
      obtain ⟨d, hd, hdk, hde⟩ := (hNx c.x c.y hne).2 ⟨c, hsub c hc, hs, Or.inl ⟨rfl, rfl⟩⟩
      have hd' := TEquation_mem_drop hk hd fun h => by rw [h] at hdk; cases hdk
      exact ⟨d.map ρ, hmemr d hd', hdk, TEquation_ends (f := ρ) hde hends⟩

end Rooted

/-! ## The output graphs of the run -/

section Out

/-- The kinds of `Err` ([II, Def 3.2 (2)], [II, Lemma 4.15]): the run kinds without minor and
without `(G_xx)⁻¹` weight are the kinds of [II, Def 3.2] or minor-free weights `W_d`. -/
private theorem TEquation_tKindsErr {k m K : ℕ} {Γ : Graph k m} (hK : Γ.RunKinds K)
    (hM : ∀ c ∈ Γ.comps, c.minor = []) (hI : ∀ c ∈ Γ.comps, ∀ ch, c.kind ≠ .inv ch) :
    Γ.TKindsErr K := by
  unfold Graph.TKindsErr
  rw [List.all_eq_true]
  intro c hc
  have h1 := List.all_eq_true.1 hK c hc
  have hi := hI c hc
  unfold Comp.isTKind
  unfold Comp.isRunKind at h1
  rw [hM c hc]
  cases h : c.kind with
  | inv ch => exact absurd h (hi ch)
  | _ => simp_all

/-- A graph of the class `Graph.LeafQ` carries a label. -/
private theorem TEquation_not_labelFree {m : ℕ} {Γ : Graph 3 m} (h : Γ.LeafQ) : ¬ Γ.LabelFree := by
  obtain ⟨⟨u, ⟨c, hc, hl⟩, -⟩, -⟩ := h
  intro hL
  rw [hL c hc] at hl
  cases hl

variable {n D : ℕ} {Sig : ℕ → Expansion 2} {T : TRec}

/-- **The output graphs of the run** of [II, Strategy 6.6] with the family `TEqSigma.qFam`, for
`n ≥ 3` and an `(n - 1)`-th order `T`-expansion `T` with error order `D` (given [II, Def 3.2 (9)] on
the graphs of `Q` of the second order `T`-expansion): every output graph has the clauses of
[II, Lemma 6.8] (`TerminationC_Out`), the run kinds, [II, Def 3.2 (9)], the form of
[II, Def 3.3 (4)], the clause on the external atoms and the charge pattern of the block normal form
if it has an internal atom, the clause `Graph.RgCheck`, scaling order `≥ 2`, and the kinds of `Err`
if its scaling order is `> D`. -/
private theorem TEquation_out (hn : 3 ≤ n) (hT : T.IsTExpStruct Sig (n - 1) D)
    (hQ2 : ∀ g ∈ h2Rec.Q, g.2.AtExternals) :
    ∀ g ∈ RunCompare.run TEqSigma.qFam n D T,
      TerminationC_Out n D g ∧ g.2.RunKinds (n - 1) ∧ g.2.AtExternals ∧ g.2.ThetaRooted ∧
        (g.1 ≠ 0 → g.2.ExtClause ∧ g.2.ColourInvB) ∧ g.2.RgCheck ∧ 2 ≤ g.2.ord ∧
        ((D : ℤ) < g.2.ord → g.2.TKindsErr (n - 1)) := by
  intro g hg
  have hspec := RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig T hn hT
  have hO := hspec.2.2 g hg
  obtain ⟨b1, b2, b3, -⟩ :=
    RunCompare.run_outFacts TEqSigma.qFam TEqSigma.qFam_spec n D Sig T hn hT
  have hK := (RunExports.selRun_exports _ TEqSigma.qFam_spec n D Sig T hn hT _ hspec.1 g hg).2.1
  have hot := RunOtimes.selRun_otimes _ TEqSigma.qFam_spec n D Sig T hn hT _ hspec.1 g hg
  have hmi := RunMinus.selRun_minus_atExt _ TEqSigma.qFam_spec n D Sig T hn hT _ hspec.1 g hg
  have hEC : g.1 ≠ 0 → g.2.ExtClause ∧ g.2.ColourInvB := by
    intro h0
    rcases hO.2.2.2.2.2 with h | h | h | h | h
    · exact h.2.2 h0
    · exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩
    · exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩
    · exact h.2.1 h0
    · exact ⟨h.2.2.2.1, h.2.2.2.2⟩
  have hAt : g.2.AtExternals := by
    by_cases h0 : g.1 = 0
    · exact hQ2 g (b2 g hg h0)
    · exact TEquation_atExt hot.1 (hEC h0).1 hmi.1
  obtain ⟨C, hN⟩ := hO.2.2.1
  refine ⟨hO, hK, hAt, TEquation_thetaRooted hN hot.1 hot.2.1 hot.2.2, hEC, ?_, b3 g hg,
    fun hD => TEquation_tKindsErr hK hot.2.2 (b1 g hg hD)⟩
  by_cases h0 : g.1 = 0
  · exact Or.inl h0
  · exact TEquation_rgCheck (hEC h0).1

/-- An output graph of the class `Graph.LeafQ` of scaling order `≤ D` has the clauses of the
class `Q` of [II, Lemma 6.8]: the clause on the external atoms and the charge pattern of the block
normal form if it has an internal atom, and otherwise its diffusive edge at `⊗` joins `⊗` to `⊕`,
its `Q` label is at `⊕` and it has the profile at `⊖`. -/
private theorem TEquation_qClause {g : Σ m, Graph 3 m} (hO : TerminationC_Out n D g)
    (hD : ¬ (D : ℤ) < g.2.ord) (hQ : g.2.LeafQ) :
    (g.1 ≠ 0 → g.2.ExtClause ∧ g.2.ColourInvB) ∧
      (g.1 = 0 → g.2.RootAtPlus ∧ g.2.QLabelAtPlus ∧ g.2.MinusProfile) := by
  have hL := TEquation_not_labelFree hQ
  rcases hO.2.2.2.2.2 with h | h | h | h | h
  · exact absurd h.1 hD
  · exact absurd h.2.1 hL
  · exact absurd h.2.1 hL
  · exact h.2
  · exact absurd h.1 hL

end Out

/-! ## The structure of the `T`-equation -/

section Struct

open Classical in
/-- The graphs of `R`, `A`, `Q`, `Err` of `TEqSigma.ofLeaves`: output graphs of the classes
`Graph.LeafR`, `Graph.LeafA n`, `Graph.LeafQ` of scaling order `≤ D`, output graphs of scaling
order `> D`, and the graphs of `corr` of an output graph of [II, Lemma 6.7] of order `≤ n`. -/
private theorem TEquation_mem {n D : ℕ} {sigma : (Σ m, Graph 3 m) → Expansion 2}
    {corr : (Σ m, Graph 3 m) → Expansion 3} {F : Expansion 3} {g : Σ m, Graph 3 m} :
    (g ∈ (TEqSigma.ofLeaves n D sigma corr F).R ↔
      (g ∈ F ∧ ¬ (D : ℤ) < g.2.ord ∧ g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∨
      ((∃ l, (l ∈ F ∧ l.2.LeafDet ∧ ¬ l.2.IsRecollision {1, 2} ∧ l.2.ord ≤ (n : ℤ)) ∧
        g ∈ corr l) ∧ g.2.ord ≤ (n : ℤ))) ∧
    (g ∈ (TEqSigma.ofLeaves n D sigma corr F).A ↔
      (g ∈ F ∧ ¬ (D : ℤ) < g.2.ord ∧ ¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ g.2.LeafA n) ∨
      ((∃ l, (l ∈ F ∧ l.2.LeafDet ∧ ¬ l.2.IsRecollision {1, 2} ∧ l.2.ord ≤ (n : ℤ)) ∧
        g ∈ corr l) ∧ (n : ℤ) < g.2.ord)) ∧
    (g ∈ (TEqSigma.ofLeaves n D sigma corr F).Q ↔ g ∈ F ∧ ¬ (D : ℤ) < g.2.ord ∧ g.2.LeafQ) ∧
    (g ∈ (TEqSigma.ofLeaves n D sigma corr F).Err ↔ g ∈ F ∧ (D : ℤ) < g.2.ord) := by
  simp only [TEqSigma.ofLeaves, List.mem_append, List.mem_filter, List.mem_flatMap,
    decide_eq_true_eq, iff_self, and_self]

variable {n D : ℕ} {Sig : ℕ → Expansion 2} {T : TRec}

/-- **The structure of the `n`-th order `T`-equation** ([II, Def 3.3], [II, Def 6.3],
[II, Lemma 6.8]): for `n ≥ 3`, `D > n` and an `(n - 1)`-th order `T`-expansion `T` with error
order `D`, given [II, Def 3.2 (9)] on the graphs of `Q` of the second order `T`-expansion and the
identity [II, (3.5)], the `T`-equation `TEqSigma.Strat n D T` has the structure of an `n`-th order
`T`-equation with error order `D`. -/
private theorem TEquation_struct (hn : 3 ≤ n) (hnD : n < D) (hT : T.IsTExpStruct Sig (n - 1) D)
    (hQ2 : ∀ g ∈ h2Rec.Q, g.2.AtExternals) (hId : (TEqSigma.Strat n D T).Identity Sig n) :
    (TEqSigma.Strat n D T).IsTEqStruct Sig n D := by
  have hSN := TEqSigma.sigN_shape n D T hn ⟨Sig, hT⟩
  rw [TEqSigma.Strat, TEqSigma.strat_eq hn hT] at hId hSN ⊢
  set F := RunCompare.run TEqSigma.qFam n D T with hF
  have hspec := RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig T hn hT
  have hout := TEquation_out hn hT hQ2
  have hnD' : (n : ℤ) < D := by exact_mod_cast hnD
  -- the correction graphs
  have hcorr : ∀ g, (∃ l, (l ∈ F ∧ l.2.LeafDet ∧ ¬ l.2.IsRecollision {1, 2} ∧
      l.2.ord ≤ (n : ℤ)) ∧ g ∈ TEqSigma.corr l) →
      ((∃ C, g.2.Normal C) ∧ g.2.TKinds (n - 1) ∧ g.2.AtExternals ∧ g.2.DoublyConnected ∧
        g.2.ThetaRooted) ∧ 5 ≤ g.2.ord ∧
      (g.2.ord ≤ n → g.2.LeafR ∧ g.2.LeafC ∧ g.2.Plain) ∧
      ((n : ℤ) < g.2.ord → g.2.LeafA n ∧ g.2.LeafC ∧
        (g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt) ∧ g.2.Plain ∧
        (g.1 = 0 → g.2.MinusProfile)) := by
    rintro g ⟨l, ⟨hl, hdet, hNR, hord⟩, hg⟩
    have hcc := TEqSigma.corr_classes n D Sig T hn hT l hl hdet hNR hord g hg
    have h4 := (TEqSigma.detLeaf_form n D Sig T hn hT l hl hdet hNR hord).choose_spec.choose_spec
    exact ⟨TEqSigma.corr_shape n D Sig T hn hT l hl hdet hNR hord g hg,
      by have := hcc.1.1; have := h4.2.2.2.2; omega, hcc.2.1, hcc.2.2⟩
  -- the run part below the error order
  have hlow : ∀ g ∈ F, ¬ (D : ℤ) < g.2.ord →
      (∃ C, g.2.Normal C) ∧ g.2.TKinds (n - 1) ∧ g.2.AtExternals ∧ g.2.DoublyConnected := by
    intro g hg hD
    obtain ⟨hO, hK, hAt, -⟩ := hout g hg
    exact ⟨hO.2.2.1, hK.tKinds (hO.2.2.2.2.1 hD), hAt, hO.2.1⟩
  have hRo : ∀ g ∈ F, g.2.LabelFree → 3 ≤ g.2.ord := fun g hg hL =>
    RunExports.selRun_labelFree_ord _ TEqSigma.qFam_spec n D Sig T hn hT _ hspec.1 g hg hL
  refine ⟨hnD, hId, hT.2.2.1, hSN, ⟨⟨fun g hg => ?_, fun g hg => ?_⟩, fun g hg => ?_,
    fun g hg => ?_, fun g hg => ?_, fun g hg => ?_⟩, fun g hg => ?_, ?_⟩
  · simp only [TEqRec.toTRec, List.mem_append, TEquation_mem] at hg
    rcases hg with (((hg | hg) | (hg | hg)) | hg)
    · exact hlow g hg.1 hg.2.1
    · exact ⟨(hcorr g hg.1).1.1, (hcorr g hg.1).1.2.1, (hcorr g hg.1).1.2.2.1,
        (hcorr g hg.1).1.2.2.2.1⟩
    · exact hlow g hg.1 hg.2.1
    · exact ⟨(hcorr g hg.1).1.1, (hcorr g hg.1).1.2.1, (hcorr g hg.1).1.2.2.1,
        (hcorr g hg.1).1.2.2.2.1⟩
    · exact hlow g hg.1 hg.2.1
  · simp only [TEqRec.toTRec, TEquation_mem] at hg
    obtain ⟨hO, -, hAt, -, -, -, -, hKE⟩ := hout g hg.1
    exact ⟨hO.2.2.1, hKE hg.2, hAt, hO.2.1⟩
  · simp only [TEqRec.toTRec, TEquation_mem] at hg
    rcases hg with hg | hg
    · obtain ⟨hg, -, hR, ho⟩ := hg
      exact ⟨hR.2.1, hR.1, hRo g hg hR.2.1, ho⟩
    · obtain ⟨hR, -, -⟩ := (hcorr g hg.1).2.2.1 hg.2
      exact ⟨hR.2.1, hR.1, by have := (hcorr g hg.1).2.1; omega, hg.2⟩
  · simp only [TEqRec.toTRec, TEquation_mem] at hg
    rcases hg with hg | hg
    · obtain ⟨-, -, -, hA⟩ := hg
      exact ⟨hA.2.1, by have := hA.1; omega⟩
    · exact ⟨((hcorr g hg.1).2.2.2 hg.2).1.2.1, hg.2⟩
  · simp only [TEqRec.toTRec, TEquation_mem] at hg
    exact ⟨hg.2.2.1, (hout g hg.1).2.2.2.2.2.2.1⟩
  · simp only [TEqRec.toTRec, TEquation_mem] at hg
    exact hg.2
  · simp only [List.mem_append, TEquation_mem] at hg
    rcases hg with (((hg | hg) | (hg | hg)) | hg) | hg
    · exact (hout g hg.1).2.2.2.1
    · exact (hcorr g hg.1).1.2.2.2.2
    · exact (hout g hg.1).2.2.2.1
    · exact (hcorr g hg.1).1.2.2.2.2
    · exact (hout g hg.1).2.2.2.1
    · exact (hout g hg.1).2.2.2.1
  · refine TRec.def63_of_leaves n _ (fun g hg => ?_) (fun g hg => ?_) (fun g hg => ?_)
      (fun g hg => ?_)
    · simp only [TEqRec.toTRec, TEquation_mem] at hg
      rcases hg with hg | hg
      · obtain ⟨hO, -⟩ := hout g hg.1
        exact ⟨hg.2.2.1, hO.2.2.2.1, hO.2.2.2.2.1 hg.2.1⟩
      · exact (hcorr g hg.1).2.2.1 hg.2
    · simp only [TEqRec.toTRec, TEquation_mem] at hg
      rcases hg with hg | hg
      · obtain ⟨hO, -, hAt, -⟩ := hout g hg.1
        have hA := hg.2.2.2
        refine ⟨hA, hO.2.2.2.1, fun _ hDR => rootedAtExt_of_extClause _ _ hA.2.2.2.1
          hA.2.2.2.2.1 hO.2.2.2.1.1 hAt hO.2.2.2.1.2.1 hDR, hO.2.2.2.2.1 hg.2.1,
          fun h0 => absurd h0 (Strategy_extClause_ne_zero hA.2.2.2.1)⟩
      · exact (hcorr g hg.1).2.2.2 hg.2
    · simp only [TEqRec.toTRec, TEquation_mem] at hg
      obtain ⟨hO, -, hAt, -, hEC, -⟩ := hout g hg.1
      have hq := TEquation_qClause hO hg.2.1 hg.2.2
      refine ⟨hg.2.2, hO.2.2.2.1, fun h0 hDR => rootedAtExt_of_extClause _ _ (hEC h0).1
        (hEC h0).2 hO.2.2.2.1.1 hAt hO.2.2.2.1.2.1 hDR, hq.1, hq.2, hO.2.2.2.2.1 hg.2.1⟩
    · simp only [TEqRec.toTRec, TEquation_mem] at hg
      obtain ⟨hO, -, hAt, -, hEC, hRg, -⟩ := hout g hg.1
      exact ⟨hO.2.2.2.1, hRg, fun h0 hDR => rootedAtExt_of_extClause _ _ (hEC h0).1
        (hEC h0).2 hO.2.2.2.1.1 hAt hO.2.2.2.1.2.1 hDR⟩

end Struct

/-! ## Comparison of the graphs of two `T`-equations -/

section Compare

variable [DecidableEq (Σ m, Graph 3 m)]

/-- Output lists whose graphs of every order `k ≤ K` with the property `q` agree up to order, and
whose graphs have order `≥ 0`, have the same multiplicity of every graph with `q` of order
`≤ K`. -/
private theorem TEquation_count_of_levels {F F' : Expansion 3} {K : ℕ}
    (q : (Σ m, Graph 3 m) → Bool)
    (h : ∀ k : ℕ, k ≤ K → (F.filter fun g => q g && decide (g.2.ord = (k : ℤ))).Perm
      (F'.filter fun g => q g && decide (g.2.ord = (k : ℤ))))
    (h0 : ∀ g ∈ F, 0 ≤ g.2.ord) (h0' : ∀ g ∈ F', 0 ≤ g.2.ord) :
    ∀ a : Σ m, Graph 3 m, q a = true → a.2.ord ≤ K → F.count a = F'.count a := by
  intro a hq ha
  by_cases hm : a ∈ F ∨ a ∈ F'
  · have h0a : 0 ≤ a.2.ord := by rcases hm with hm | hm; exacts [h0 a hm, h0' a hm]
    have hk : ((a.2.ord.toNat : ℕ) : ℤ) = a.2.ord := Int.toNat_of_nonneg h0a
    have := (h a.2.ord.toNat (by omega)).count_eq a
    rw [TEquation_count_filter, TEquation_count_filter] at this
    simpa [hq, hk] using this
  · rw [not_or] at hm
    rw [List.count_eq_zero_of_not_mem hm.1, List.count_eq_zero_of_not_mem hm.2]

/-- **The correction graphs of a window of orders** ([II, (6.7)]): for two output lists and leaf
predicates `P`, `P'` whose correction graphs have order `≥` the order of the leaf plus one, the
correction graphs with a property `q` of order `≤ K` agree up to order when the leaf predicates
and the multiplicities agree below the order `K`. -/
private theorem TEquation_corr_perm {corr : (Σ m, Graph 3 m) → Expansion 3} {F F' : Expansion 3}
    {P P' q : (Σ m, Graph 3 m) → Bool} {K : ℤ} (hq : ∀ x, q x = true → x.2.ord ≤ K)
    (hF : ∀ g ∈ F, P g = true → ∀ x ∈ corr g, g.2.ord + 1 ≤ x.2.ord)
    (hF' : ∀ g ∈ F', P' g = true → ∀ x ∈ corr g, g.2.ord + 1 ≤ x.2.ord)
    (hP : ∀ a : Σ m, Graph 3 m, a.2.ord < K → P a = P' a)
    (hcnt : ∀ a : Σ m, Graph 3 m, a.2.ord < K → F.count a = F'.count a) :
    (((F.filter P).flatMap corr).filter q).Perm (((F'.filter P').flatMap corr).filter q) := by
  have hv : ∀ (G : Expansion 3) (Q : (Σ m, Graph 3 m) → Bool),
      (∀ g ∈ G, Q g = true → ∀ x ∈ corr g, g.2.ord + 1 ≤ x.2.ord) →
      ∀ g ∈ G.filter Q, decide (g.2.ord < K) = false → (corr g).filter q = [] := by
    intro G Q hG g hg hK
    refine List.filter_eq_nil_iff.2 fun x hx hqx => ?_
    have h1 := hG g (List.mem_filter.1 hg).1 (List.mem_filter.1 hg).2 x hx
    have h2 := hq x hqx
    simp only [decide_eq_false_iff_not, not_lt] at hK
    omega
  rw [List.filter_flatMap, List.filter_flatMap,
    TEquation_flatMap_filter _ _ _ (hv F P hF), TEquation_flatMap_filter _ _ _ (hv F' P' hF')]
  refine List.Perm.flatMap_right _ (List.perm_iff_count.2 fun a => ?_)
  rw [TEquation_count_filter, TEquation_count_filter, TEquation_count_filter,
    TEquation_count_filter]
  by_cases ha : a.2.ord < K
  · simp [ha, hP a ha, hcnt a ha]
  · simp [ha]

open Classical in
/-- The graphs of order `k` of `R` of two `T`-equations read off output lists agree up to order
when `k` is at most both error orders, the cutoff orders agree or are both `≥ k`, and the
multiplicities of the output graphs of order `≤ k` agree. -/
private theorem TEquation_R_perm {sigma sigma' : (Σ m, Graph 3 m) → Expansion 2}
    {corr : (Σ m, Graph 3 m) → Expansion 3} {c₀ c D₀ D k : ℕ} {F₀ F : Expansion 3}
    (hcc : (k ≤ c₀ ∧ k ≤ c) ∨ c₀ = c) (hkD₀ : k ≤ D₀) (hkD : k ≤ D)
    (hcnt : ∀ a : Σ m, Graph 3 m, a.2.ord ≤ k → F₀.count a = F.count a)
    (hF₀ : ∀ g ∈ F₀, g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (c₀ : ℤ) →
      ∀ x ∈ corr g, g.2.ord + 1 ≤ x.2.ord)
    (hF : ∀ g ∈ F, g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (c : ℤ) →
      ∀ x ∈ corr g, g.2.ord + 1 ≤ x.2.ord) :
    ((TEqSigma.ofLeaves c₀ D₀ sigma corr F₀).R.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      ((TEqSigma.ofLeaves c D sigma' corr F).R.filter fun g => decide (g.2.ord = (k : ℤ))) := by
  simp only [TEqSigma.ofLeaves, List.filter_append]
  rcases hcc with ⟨hk₀, hk⟩ | rfl
  · refine List.Perm.append ?_ ?_
    · rw [List.filter_filter, List.filter_filter]
      refine TEquation_filter_perm fun a => ?_
      by_cases ho : a.2.ord = (k : ℤ)
      · simp [ho, hkD₀, hkD, hk₀, hk, hcnt a (le_of_eq ho)]
      · simp [ho]
    · rw [List.filter_filter, List.filter_filter]
      have e : ∀ (c' : ℕ), k ≤ c' → ∀ G : Expansion 3, (G.filter fun g =>
          decide (g.2.ord = (k : ℤ)) && decide (g.2.ord ≤ (c' : ℤ))) =
          G.filter fun g => decide (g.2.ord = (k : ℤ)) := by
        intro c' hc' G
        refine List.filter_congr fun g _ => ?_
        by_cases ho : g.2.ord = (k : ℤ)
        · simp [ho, hc']
        · simp [ho]
      rw [e c₀ hk₀, e c hk]
      refine TEquation_corr_perm (K := k) (fun x hx => by simp at hx; omega)
        (fun g hg hP => hF₀ g hg (by simpa using hP)) (fun g hg hP => hF g hg (by simpa using hP))
        (fun a ha => ?_) (fun a ha => hcnt a ha.le)
      have h1 : a.2.ord ≤ (c₀ : ℤ) := by omega
      have h2 : a.2.ord ≤ (c : ℤ) := by omega
      simp [h1, h2]
  · refine List.Perm.append ?_ ?_
    · rw [List.filter_filter, List.filter_filter]
      refine TEquation_filter_perm fun a => ?_
      by_cases ho : a.2.ord = (k : ℤ)
      · simp [ho, hkD₀, hkD, hcnt a (le_of_eq ho)]
      · simp [ho]
    · rw [List.filter_filter, List.filter_filter]
      exact TEquation_corr_perm (K := k) (fun x hx => by simp at hx; omega)
        (fun g hg hP => hF₀ g hg (by simpa using hP)) (fun g hg hP => hF g hg (by simpa using hP))
        (fun a _ => rfl) (fun a ha => hcnt a ha.le)

open Classical in
/-- The graphs of order `k` of `A` of two `T`-equations read off output lists at one cutoff order
agree up to order when `k` is at most both error orders and the multiplicities of the output
graphs of order `≤ k` agree. -/
private theorem TEquation_A_perm {sigma sigma' : (Σ m, Graph 3 m) → Expansion 2}
    {corr : (Σ m, Graph 3 m) → Expansion 3} {c D₀ D k : ℕ} {F₀ F : Expansion 3}
    (hkD₀ : k ≤ D₀) (hkD : k ≤ D)
    (hcnt : ∀ a : Σ m, Graph 3 m, a.2.ord ≤ k → F₀.count a = F.count a)
    (hF₀ : ∀ g ∈ F₀, g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (c : ℤ) →
      ∀ x ∈ corr g, g.2.ord + 1 ≤ x.2.ord)
    (hF : ∀ g ∈ F, g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (c : ℤ) →
      ∀ x ∈ corr g, g.2.ord + 1 ≤ x.2.ord) :
    ((TEqSigma.ofLeaves c D₀ sigma corr F₀).A.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      ((TEqSigma.ofLeaves c D sigma' corr F).A.filter fun g => decide (g.2.ord = (k : ℤ))) := by
  simp only [TEqSigma.ofLeaves, List.filter_append]
  refine List.Perm.append ?_ ?_
  · rw [List.filter_filter, List.filter_filter]
    refine TEquation_filter_perm fun a => ?_
    by_cases ho : a.2.ord = (k : ℤ)
    · simp [ho, hkD₀, hkD, hcnt a (le_of_eq ho)]
    · simp [ho]
  · rw [List.filter_filter, List.filter_filter]
    exact TEquation_corr_perm (K := k) (fun x hx => by simp at hx; omega)
      (fun g hg hP => hF₀ g hg (by simpa using hP)) (fun g hg hP => hF g hg (by simpa using hP))
      (fun a _ => rfl) (fun a ha => hcnt a ha.le)

open Classical in
/-- The graphs of order `k` of `Q` of two `T`-equations read off output lists agree up to order
when `k` is at most both error orders and the multiplicities of the output graphs of order `k`
agree. -/
private theorem TEquation_Q_perm {sigma sigma' : (Σ m, Graph 3 m) → Expansion 2}
    {corr corr' : (Σ m, Graph 3 m) → Expansion 3} {c₀ c D₀ D k : ℕ} {F₀ F : Expansion 3}
    (hkD₀ : k ≤ D₀) (hkD : k ≤ D)
    (hcnt : ∀ a : Σ m, Graph 3 m, a.2.ord ≤ k → F₀.count a = F.count a) :
    ((TEqSigma.ofLeaves c₀ D₀ sigma corr F₀).Q.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      ((TEqSigma.ofLeaves c D sigma' corr' F).Q.filter fun g => decide (g.2.ord = (k : ℤ))) := by
  simp only [TEqSigma.ofLeaves]
  rw [List.filter_filter, List.filter_filter]
  refine TEquation_filter_perm fun a => ?_
  by_cases ho : a.2.ord = (k : ℤ)
  · simp [ho, hkD₀, hkD, hcnt a (le_of_eq ho)]
  · simp [ho]

omit [DecidableEq (Σ m, Graph 3 m)] in
open Classical in
/-- `Err` of a `T`-equation read off an output list has no graph of order `k ≤ D`. -/
private theorem TEquation_Err_nil {sigma : (Σ m, Graph 3 m) → Expansion 2}
    {corr : (Σ m, Graph 3 m) → Expansion 3} {c D k : ℕ} {F : Expansion 3} (hkD : k ≤ D) :
    ((TEqSigma.ofLeaves c D sigma corr F).Err.filter fun g => decide (g.2.ord = (k : ℤ))) = [] := by
  simp only [TEqSigma.ofLeaves]
  refine List.filter_eq_nil_iff.2 fun g hg h => ?_
  have := (List.mem_filter.1 hg).2
  simp only [decide_eq_true_eq] at this h
  omega

omit [DecidableEq (Σ m, Graph 3 m)] in
open Classical in
/-- **The graphs with `⊕`, `⊖` in one dotted block of `R`, `A`, `Q`** of a `T`-equation read off an
output list in which every output graph with `⊕`, `⊖` in one dotted block of order `≤ D` lies in
exactly one of the classes `R`, `A`, `Q`: up to order, the output graphs with the property `w` and
the correction graphs with `w`, for every property `w` of graphs with `⊕`, `⊖` in one dotted block
of order `≤ D`. -/
private theorem TEquation_pm_decomp {sigma : (Σ m, Graph 3 m) → Expansion 2}
    {corr : (Σ m, Graph 3 m) → Expansion 3} {n D : ℕ} {F : Expansion 3}
    (hcls : ∀ g ∈ F, g.2.PMBlock → ¬ (D : ℤ) < g.2.ord →
      ((g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ ¬ (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ g.2.LeafA n) ∧
          ¬ g.2.LeafQ) ∨
        (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ g.2.LeafA n) ∧
          ¬ g.2.LeafQ) ∨
        (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ ¬ (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ g.2.LeafA n) ∧
          g.2.LeafQ))
    (w : (Σ m, Graph 3 m) → Bool) (hw : ∀ a, w a = true → a.2.PMBlock ∧ ¬ (D : ℤ) < a.2.ord) :
    (((TEqSigma.ofLeaves n D sigma corr F).R ++ (TEqSigma.ofLeaves n D sigma corr F).A ++
        (TEqSigma.ofLeaves n D sigma corr F).Q).filter w).Perm
      (F.filter w ++ ((F.filter fun g => decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧
        g.2.ord ≤ (n : ℤ))).flatMap corr).filter w) := by
  refine List.perm_iff_count.2 fun a => ?_
  simp only [TEqSigma.ofLeaves, List.filter_append, List.count_append, TEquation_count_filter,
    decide_eq_true_eq]
  by_cases hwa : w a = true
  · obtain ⟨hpm, hD⟩ := hw a hwa
    simp only [hwa, ite_true]
    set X := List.count a (List.flatMap corr (List.filter (fun g => decide
      (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (n : ℤ))) F)) with hXdef
    have hX : (if a.2.ord ≤ (n : ℤ) then X else 0) + (if (n : ℤ) < a.2.ord then X else 0) = X := by
      by_cases ho : a.2.ord ≤ (n : ℤ)
      · simp [ho]
      · simp [ho, show (n : ℤ) < a.2.ord by omega]
    by_cases hm : a ∈ F
    · rcases hcls a hm hpm hD with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · simp only [hD, h1, h3, not_false_eq_true, and_self, ite_true, ite_false, not_true_eq_false,
          false_and, and_false] at hX ⊢
        omega
      · simp only [hD, h1, h2.2, h3, not_false_eq_true, and_self, ite_true, ite_false,
          and_false] at hX ⊢
        omega
      · have hA : ¬ a.2.LeafA n := fun h => h2 ⟨h1, h⟩
        simp only [hD, h1, hA, h3, not_false_eq_true, and_self, ite_true, ite_false,
          and_false] at hX ⊢
        omega
    · have h0 := List.count_eq_zero_of_not_mem hm
      simp only [h0, ite_self]
      omega
  · simp [hwa]

omit [DecidableEq (Σ m, Graph 3 m)] in
/-- A record with the clauses `TRec.Def63` has no graph of `R`, `A`, `Q` with `⊕`, `⊖` in one dotted
block of order `≤ 3`. -/
private theorem TEquation_pm_nil {𝒬 : TRec} (h : 𝒬.Def63) {k : ℕ} (hk : k ≤ 3) :
    ((𝒬.R ++ 𝒬.A ++ 𝒬.Q).filter fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ))) = [] := by
  refine List.filter_eq_nil_iff.2 fun g hg hp => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  rcases List.mem_append.1 hg with hg | hg
  · have := h.2.2.2.1 g hg hp.1
    omega
  · have := h.2.2.2.2.1 g hg hp.1
    omega

end Compare

/-! ## [II, Theorem 3.7] -/

section Main

variable {n D : ℕ} {Sig : ℕ → Expansion 2} {T : TRec}

/-- An output graph of the run with `⊕`, `⊖` in one dotted block, of scaling order `≤ D`, lies in
exactly one of the classes `R` (`Graph.LeafR`, order `≤ n`), `A` (`Graph.LeafA n`, not in `R`)
and `Q` (`Graph.LeafQ`): an output graph of [II, Lemma 6.7] that is not a `⊕/⊖`-recollision graph
has no internal atom in the block of `⊕`, so `⊕`, `⊖` are not in one block. -/
private theorem TEquation_pm_cls (hn : 3 ≤ n) (hT : T.IsTExpStruct Sig (n - 1) D) (hnD : n < D) :
    ∀ g ∈ RunCompare.run TEqSigma.qFam n D T, g.2.PMBlock → ¬ (D : ℤ) < g.2.ord →
      ((g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ ¬ (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ g.2.LeafA n) ∧
          ¬ g.2.LeafQ) ∨
        (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ g.2.LeafA n) ∧
          ¬ g.2.LeafQ) ∨
        (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ ¬ (¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ g.2.LeafA n) ∧
          g.2.LeafQ) := by
  intro g hg hpm hD
  have hspec := RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig T hn hT
  obtain ⟨-, -, -, hLC, -, hO⟩ := hspec.2.2 g hg
  have hR3 := (RunExports.selRun_exports _ TEqSigma.qFam_spec n D Sig T hn hT _ hspec.1 g hg).2.2
  have hO' : g.2.LeafR ∨ g.2.LeafA n ∨ g.2.LeafQ ∨ g.2.LeafDet := by
    rcases hO with h | h | h | h | h
    · exact absurd h.1 hD
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h.1))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases TEqIdentity_classes hnD hLC.1 hO' (fun h1 h2 => hR3 h1 h2 hD) with
    ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨-, -, -, h4⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
  · exfalso
    rw [Graph.pmBlock_iff_sameBlock] at hpm
    obtain ⟨b, hb⟩ := h4.1.2.2.2.1.1 (.inl 1) (.inl 2) (by simp) hpm
    exact TEqIdentity_unp hLC.1 h4.2.1 1 b hb

/-- The correction graphs of an output graph of [II, Lemma 6.7] of order `≤ n` have order `≥` its
order plus one. -/
private theorem TEquation_corr_ord (hn : 3 ≤ n) (hT : T.IsTExpStruct Sig (n - 1) D) :
    ∀ g ∈ RunCompare.run TEqSigma.qFam n D T,
      g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (n : ℤ) →
        ∀ x ∈ TEqSigma.corr g, g.2.ord + 1 ≤ x.2.ord :=
  fun g hg h x hx => (TEqSigma.corr_classes n D Sig T hn hT g hg h.1 h.2.1 h.2.2 x hx).1.1

open Classical in
/-- **[II, Theorem 3.7] = [I, Lemma 5.7] for the construction `TEqSigma.Strat`** of [II, (6.8)], in
the parallel form [II, (6.8)–(6.9)]: for `n ≥ 3` and families of `H(n - 1)` that record
`TEqSigma.Strat`, one `Σ_n = E` serves every error order `D > n`; the `T`-equation
`TEqSigma.Strat n D (𝒯 (n - 1) D)` has the structure of [II, Def 3.3], [II, Def 6.3]; its graphs of
order `≤ n - 1` of `R` and `Q` are those of the `(n - 1)`-th order `T`-equation, and its graphs of
order `≤ n` of `R`, `A`, `Q` with `⊕`, `⊖` in one dotted block are those of the `(n - 1)`-th order
`T`-equation ([II, (6.9)]); its graphs of order `≤ D` do not depend on the error order
`D' ≥ D`. -/
theorem TEquation_strat : ∀ n : ℕ, 3 ≤ n →
    ∀ (Sig : ℕ → Expansion 2) (𝒬 : ℕ → ℕ → TEqRec) (𝒯 : ℕ → ℕ → TRec),
      HFam TEqSigma.Strat Sig (n - 1) 𝒬 𝒯 →
      ∃ E : Expansion 2, ∀ D, n < D →
        (TEqSigma.Strat n D (𝒯 (n - 1) D)).SigN = E ∧
        (TEqSigma.Strat n D (𝒯 (n - 1) D)).IsTEqStruct Sig n D ∧
        TRec.Coherent (n - 1) (𝒬 (n - 1) D).toTRec (TEqSigma.Strat n D (𝒯 (n - 1) D)).toTRec ∧
        TRec.CoherentPM n (𝒬 (n - 1) D).toTRec (TEqSigma.Strat n D (𝒯 (n - 1) D)).toTRec ∧
        ∀ D', D ≤ D' →
          (TEqSigma.Strat n D (𝒯 (n - 1) D)).toTRec.AgreeTo D
            (TEqSigma.Strat n D' (𝒯 (n - 1) D')).toTRec := by
  intro n hn Sig 𝒬 𝒯 hH
  obtain ⟨E, hE⟩ := TEqSigma.sigN_indep TEqSigma.sigma' TEqSigma.corr n hn Sig 𝒬 𝒯 hH
  refine ⟨E, fun D hD => ?_⟩
  have hTs : ∀ D', n < D' → (𝒯 (n - 1) D').IsTExpStruct Sig (n - 1) D' := fun D' hD' =>
    (hH.1 (n - 1) D' (by omega) le_rfl (by omega)).2.1
  have hT := hTs D hD
  have hQ2s : h2TEq.IsTEqStruct Sig 2 D := by
    have := (hH.1 2 D le_rfl (by omega) (by omega)).1
    rwa [hH.2.2.2.2.1 D (by omega) (by omega)] at this
  have hQ2 : ∀ g ∈ h2Rec.Q, g.2.AtExternals := fun g hg =>
    (hQ2s.2.2.2.2.1.1.1 g (List.mem_append_right _ hg)).2.2.1
  have hS := TEquation_struct hn hD hT hQ2 (TEqSigma.identity n hn Sig 𝒬 𝒯 hH D hD)
  set F := RunCompare.run TEqSigma.qFam n D (𝒯 (n - 1) D) with hF
  have hF0 : ∀ g ∈ F, 0 ≤ g.2.ord := fun g hg => by
    have := (RunCompare.run_outFacts TEqSigma.qFam TEqSigma.qFam_spec n D Sig _ hn hT).2.2.1 g hg
    omega
  have hSe : TEqSigma.Strat n D (𝒯 (n - 1) D) =
      TEqSigma.ofLeaves n D TEqSigma.sigma' TEqSigma.corr F := by
    rw [TEqSigma.Strat, TEqSigma.strat_eq hn hT]
  have hS' := hS
  rw [hSe] at hS'
  refine ⟨hE D hD, hS, ?_, ?_, ?_⟩
  · -- [II, (6.9)]: the graphs of order `≤ n - 1` of `R` and `Q`
    by_cases h3 : n = 3
    · subst h3
      have hq2 : 𝒬 (3 - 1) D = h2TEq := hH.2.2.2.2.1 D (by norm_num) (by omega)
      have b4 := (RunCompare.run_outFacts TEqSigma.qFam TEqSigma.qFam_spec 3 D Sig _ le_rfl
        hT).2.2.2 rfl
      have hc4 : ∀ a : Σ m, Graph 3 m, a.2.ord ≤ 2 → F.count a = h2Rec.Q.count a := by
        intro a ha
        have := b4.count_eq a
        rw [TEquation_count_filter, TEquation_count_filter] at this
        simpa [ha] using this
      have hLQ : ∀ g ∈ h2Rec.Q, g.2.LeafQ := by
        intro g hg
        have hDef := hQ2s.2.2.2.2.2.2
        exact ⟨(hQ2s.2.2.2.2.1.2.2.2.1 g hg).1, (hDef.1.2.2 g hg).1, (hDef.1.2.2 g hg).2.1,
          hDef.2.2.2.2.1 g hg, hDef.2.2.2.2.2.1 g (List.mem_append_left _ hg)⟩
      rw [hq2, hSe]
      intro k hk
      refine ⟨?_, ?_⟩
      · have hR0 : ((TEqSigma.ofLeaves 3 D TEqSigma.sigma' TEqSigma.corr F).toTRec.R.filter
            fun g => decide (g.2.ord = (k : ℤ))) = [] := by
          refine List.filter_eq_nil_iff.2 fun g hg h => ?_
          have := (hS'.2.2.2.2.1.2.1 g hg).2.2.1
          simp only [decide_eq_true_eq] at h
          omega
        rw [hR0]
        exact List.Perm.nil
      · refine List.perm_iff_count.2 fun a => ?_
        simp only [TEqRec.toTRec, h2TEq, TEqSigma.ofLeaves, List.filter_filter,
          TEquation_count_filter, Bool.and_eq_true, decide_eq_true_eq]
        by_cases ho : a.2.ord = (k : ℤ)
        · by_cases hm : a ∈ h2Rec.Q
          · have hDk : ¬ D < k := by omega
            simp [ho, hDk, hLQ a hm, hc4 a (by omega)]
          · have h0 := List.count_eq_zero_of_not_mem hm
            simp [h0, hc4 a (by omega)]
        · simp [ho]
    · have hT₀ : (𝒯 (n - 1 - 1) D).IsTExpStruct Sig (n - 1 - 1) D :=
        (hH.1 (n - 1 - 1) D (by omega) (by omega) (by omega)).2.1
      have hq : 𝒬 (n - 1) D = TEqSigma.Strat (n - 1) D (𝒯 (n - 1 - 1) D) :=
        hH.2.2.2.2.2 (n - 1) D (by omega) le_rfl (by omega)
      set F₀ := RunCompare.run TEqSigma.qFam (n - 1) D (𝒯 (n - 1 - 1) D) with hF₀
      have hSe₀ : TEqSigma.Strat (n - 1) D (𝒯 (n - 1 - 1) D) =
          TEqSigma.ofLeaves (n - 1) D TEqSigma.sigma' TEqSigma.corr F₀ := by
        rw [TEqSigma.Strat, TEqSigma.strat_eq (by omega) hT₀]
      have hF00 : ∀ g ∈ F₀, 0 ≤ g.2.ord := fun g hg => by
        have := (RunCompare.run_outFacts TEqSigma.qFam TEqSigma.qFam_spec (n - 1) D Sig _
          (by omega) hT₀).2.2.1 g hg
        omega
      obtain ⟨-, hC3, hPM3⟩ := hH.2.2.1 (n - 1 - 1) (n - 1) D (by omega) (by omega) le_rfl
        (by omega)
      have e1 : n - 1 - 1 + 1 = n - 1 := by omega
      rw [e1] at hPM3
      have hA : ∀ g ∈ (𝒯 (n - 1 - 1) D).A ++ (𝒯 (n - 1) D).A, ((n - 1 : ℕ) : ℤ) ≤ g.2.ord := by
        intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · have := ((hT₀.2.2.2.1).2.2.1 g hg).2
          omega
        · have := ((hT.2.2.2.1).2.2.1 g hg).2
          omega
      have hP := (RunCompare.runCompare TEqSigma.qFam TEqSigma.qFam_spec).1 Sig (n - 1) (n - 1) n
        D _ _ (by omega) le_rfl (by omega) (by omega) hT₀ hT hC3 hPM3 hA
      have hc := TEquation_count_of_levels (F := F₀) (F' := F) (K := n - 1) (fun _ => true)
        (fun k hk => by simpa using hP.1 k hk) hF00 hF0
      rw [hq, hSe₀, hSe]
      intro k hk
      exact ⟨TEquation_R_perm (sigma := TEqSigma.sigma') (sigma' := TEqSigma.sigma')
          (Or.inl ⟨by omega, by omega⟩) (by omega) (by omega)
          (fun a ha => hc a rfl (by omega)) (TEquation_corr_ord (by omega) hT₀)
          (TEquation_corr_ord hn hT),
        TEquation_Q_perm (sigma := TEqSigma.sigma') (sigma' := TEqSigma.sigma')
          (corr := TEqSigma.corr) (corr' := TEqSigma.corr) (c₀ := n - 1) (c := n) (by omega)
          (by omega) (fun a ha => hc a rfl (by omega))⟩
  · -- [II, (6.9)]: the graphs of order `≤ n` with `⊕`, `⊖` in one dotted block
    by_cases h3 : n = 3
    · subst h3
      have hq2 : 𝒬 (3 - 1) D = h2TEq := hH.2.2.2.2.1 D (by norm_num) (by omega)
      rw [hq2, hSe]
      intro k hk
      rw [TEquation_pm_nil hQ2s.2.2.2.2.2.2 hk, TEquation_pm_nil hS'.2.2.2.2.2.2 hk]
    · have hT₀ : (𝒯 (n - 1 - 1) D).IsTExpStruct Sig (n - 1 - 1) D :=
        (hH.1 (n - 1 - 1) D (by omega) (by omega) (by omega)).2.1
      have hq : 𝒬 (n - 1) D = TEqSigma.Strat (n - 1) D (𝒯 (n - 1 - 1) D) :=
        hH.2.2.2.2.2 (n - 1) D (by omega) le_rfl (by omega)
      set F₀ := RunCompare.run TEqSigma.qFam (n - 1) D (𝒯 (n - 1 - 1) D) with hF₀
      have hSe₀ : TEqSigma.Strat (n - 1) D (𝒯 (n - 1 - 1) D) =
          TEqSigma.ofLeaves (n - 1) D TEqSigma.sigma' TEqSigma.corr F₀ := by
        rw [TEqSigma.Strat, TEqSigma.strat_eq (by omega) hT₀]
      have hF00 : ∀ g ∈ F₀, 0 ≤ g.2.ord := fun g hg => by
        have := (RunCompare.run_outFacts TEqSigma.qFam TEqSigma.qFam_spec (n - 1) D Sig _
          (by omega) hT₀).2.2.1 g hg
        omega
      obtain ⟨-, hC3, hPM3⟩ := hH.2.2.1 (n - 1 - 1) (n - 1) D (by omega) (by omega) le_rfl
        (by omega)
      have e1 : n - 1 - 1 + 1 = n - 1 := by omega
      rw [e1] at hPM3
      have hA : ∀ g ∈ (𝒯 (n - 1 - 1) D).A ++ (𝒯 (n - 1) D).A, ((n - 1 : ℕ) : ℤ) ≤ g.2.ord := by
        intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · have := ((hT₀.2.2.2.1).2.2.1 g hg).2
          omega
        · have := ((hT.2.2.2.1).2.2.1 g hg).2
          omega
      have hP := (RunCompare.runCompare TEqSigma.qFam TEqSigma.qFam_spec).1 Sig (n - 1) (n - 1) n
        D _ _ (by omega) le_rfl (by omega) (by omega) hT₀ hT hC3 hPM3 hA
      have hc := TEquation_count_of_levels (F := F₀) (F' := F) (K := n - 1) (fun _ => true)
        (fun k hk => by simpa using hP.1 k hk) hF00 hF0
      have hpc := TEquation_count_of_levels (F := F₀) (F' := F) (K := n)
        (fun g => g.2.pmBlockB) (fun k hk => hP.2 k (by omega)) hF00 hF0
      rw [hq, hSe₀, hSe]
      intro k hk
      have hw : ∀ a : Σ m, Graph 3 m, (a.2.pmBlockB && decide (a.2.ord = (k : ℤ))) = true →
          a.2.PMBlock ∧ ¬ (D : ℤ) < a.2.ord := by
        intro a ha
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
        exact ⟨ha.1, by omega⟩
      refine (TEquation_pm_decomp (sigma := TEqSigma.sigma') (corr := TEqSigma.corr)
        (TEquation_pm_cls (by omega) hT₀ (by omega)) _ hw).trans
        ((List.Perm.append ?_ ?_).trans (TEquation_pm_decomp (sigma := TEqSigma.sigma')
          (corr := TEqSigma.corr) (TEquation_pm_cls hn hT hD) _ hw).symm)
      · refine TEquation_filter_perm fun a => ?_
        by_cases ha : (a.2.pmBlockB && decide (a.2.ord = (k : ℤ))) = true
        · have ha' := ha
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ha'
          rw [ite_eq_left ha, ite_eq_left ha, hpc a ha'.1 (by omega)]
        · rw [ite_eq_right ha, ite_eq_right ha]
      · have hc₀ := TEquation_corr_ord (by omega) hT₀
        have hc₁ := TEquation_corr_ord hn hT
        refine TEquation_corr_perm (K := k) (fun x hx => ?_)
          (fun g hg hP => hc₀ g hg (by simpa using hP))
          (fun g hg hP => hc₁ g hg (by simpa using hP)) (fun a ha => ?_)
          (fun a ha => hc a rfl (by omega))
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
          omega
        · have h1 : a.2.ord ≤ ((n - 1 : ℕ) : ℤ) := by omega
          have h2 : a.2.ord ≤ (n : ℤ) := by omega
          simp [h1, h2]
  · -- the graphs of order `≤ D` do not depend on the error order
    intro D' hDD' k hk
    have hD' : n < D' := by omega
    have hT' := hTs D' hD'
    set F' := RunCompare.run TEqSigma.qFam n D' (𝒯 (n - 1) D') with hF'
    have hF0' : ∀ g ∈ F', 0 ≤ g.2.ord := fun g hg => by
      have := (RunCompare.run_outFacts TEqSigma.qFam TEqSigma.qFam_spec n D' Sig _ hn hT').2.2.1
        g hg
      omega
    have hAg : (𝒯 (n - 1) D).AgreeTo D (𝒯 (n - 1) D') :=
      (hH.2.2.2.1 (n - 1) D D' (by omega) le_rfl (by omega) hDD').2
    have hP := (RunCompare.runCompare TEqSigma.qFam TEqSigma.qFam_spec).2 Sig n D D' _ _ hn hD
      hDD' hT hT' hAg
    have hc := TEquation_count_of_levels (F := F) (F' := F') (K := D) (fun _ => true)
      (fun k hk => by simpa using hP k hk) hF0 hF0'
    have hSe' : TEqSigma.Strat n D' (𝒯 (n - 1) D') =
        TEqSigma.ofLeaves n D' TEqSigma.sigma' TEqSigma.corr F' := by
      rw [TEqSigma.Strat, TEqSigma.strat_eq hn hT']
    rw [hSe, hSe']
    refine ⟨TEquation_R_perm (sigma := TEqSigma.sigma') (sigma' := TEqSigma.sigma') (Or.inr rfl)
        hk (by omega) (fun a ha => hc a rfl (by omega)) (TEquation_corr_ord hn hT)
        (TEquation_corr_ord hn hT'),
      TEquation_A_perm (sigma := TEqSigma.sigma') (sigma' := TEqSigma.sigma') hk (by omega)
        (fun a ha => hc a rfl (by omega)) (TEquation_corr_ord hn hT) (TEquation_corr_ord hn hT'),
      TEquation_Q_perm (sigma := TEqSigma.sigma') (sigma' := TEqSigma.sigma')
        (corr := TEqSigma.corr) (corr' := TEqSigma.corr) (c₀ := n) (c := n) hk (by omega)
        (fun a ha => hc a rfl (by omega)), ?_⟩
    have e1 := TEquation_Err_nil (sigma := TEqSigma.sigma') (corr := TEqSigma.corr) (c := n)
      (F := F) hk
    have e2 := TEquation_Err_nil (sigma := TEqSigma.sigma') (corr := TEqSigma.corr) (c := n)
      (F := F') (show k ≤ D' by omega)
    exact (List.Perm.of_eq e1).trans (List.Perm.of_eq e2.symm)

/-- **[II, Theorem 3.7] = [I, Lemma 5.7]** in the parallel form [II, (6.8)–(6.9)], with the
construction `TEqSigma.Strat` of [II, (6.8)] read off the run of [II, Strategy 6.6]. -/
theorem tEquation : tEquationStmt := ⟨TEqSigma.Strat, TEquation_strat⟩

end Main

section Instances

open private h2Fam from RBM8D.TExp.Second

end Instances

end RBM8D.Graphs
