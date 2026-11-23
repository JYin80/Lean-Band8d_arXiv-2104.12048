module

public import RBM8D.GlobalExp.TEqSigma
public import RBM8D.GlobalExp.RunOtimes
public import RBM8D.GlobalExp.RunMinus
public import RBM8D.GlobalExp.RunExports

@[expose] public section

/-!
# The output graphs of [II, Lemma 6.7]: the form `Θ_{⊗x} 𝒮_{xy} t_{y,⊕⊖}`

The output graphs of the run `RunCompare.run` of [II, Strategy 6.6] ([II, Lemma 6.8]) of the class
`Graph.LeafDet` that are not `⊕/⊖`-recollision graphs, of scaling order `≤ n`, are the terms
`Σ_x (Θ Σ̃^{(n)})_{𝔞x} t_{x,𝔟₁𝔟₂}` of the display before [II, (6.7)], with
`t_{x,𝔟₁𝔟₂} = |m|² Σ_α s_{xα} G_{α𝔟₁} Ḡ_{α𝔟₂} 1_{α ≠ 𝔟₁} 1_{α ≠ 𝔟₂}`:

* the leaf form `TEqSigma.LeafOf g 𝒮`: up to the names of the internal atoms and the order of the
  components, `g` is `Θ_{⊗x} 𝒮_{xy} s_{yα} G_{α⊕} Ḡ_{α⊖}` with `×`-dotted edges `α ≠ ⊕`, `α ≠ ⊖`;
  the `×`-dotted loops at `α` of `g` (value `0`) are `×`-dotted loops at `x` of `𝒮`;
* the map `TEqSigma.sigma` from an output graph to its graph `𝒮`;
* `TEqSigma.detLeaf_form`: every such output graph has the leaf form, and `𝒮` has its scaling
  order, which is even and `≥ 4` ([II, Def 2.7 (i)]).
-/

noncomputable section

namespace RBM8D.Graphs

/-! ## The leaf form -/

/-- **The leaf form** `Θ_{⊗x} 𝒮_{xy} t_{y,⊕⊖}` of an output graph `g` of [II, Lemma 6.7] (the terms
`Σ_x (Θ Σ̃^{(n)})_{𝔞x} t_{x,𝔟₁𝔟₂}` of the display before [II, (6.7)]): for internal atoms `x`, `y`,
`α` of `g` with `α ≠ x`, `α ≠ y`, up to a bijection `e` of the internal atoms and the order of the
components, `g` is `Θ_{⊗x} 𝒮_{xy} s_{yα} G_{α⊕} Ḡ_{α⊖}` with `k₁ ≥ 1` `×`-dotted edges between `α`
and `⊕` and `k₂ ≥ 1` between `α` and `⊖`, each in either orientation (the list `X`):
* the atoms `0`, `1` of `𝒮` are `x`, `y`, and the internal atom `j` of `𝒮` is `e j`; the internal
  atoms of `g` other than `x`, `y`, `α` are exactly the atoms `e j`;
* the components of `𝒮` read in `g` are those of `R`; at `x = y` the graph `𝒮` carries in addition
  the dotted edge between its atoms `0` and `1` ([I, Def 2.13 (i)]);
* the waved edge `s_{yα}` is taken in either orientation (`s` is symmetric);
* `g` has `ℓ ≥ 0` `×`-dotted loops at `α` exactly when `𝒮` has `ℓ` further `×`-dotted loops at its
  atom `0`; both have value `0`;
* the coefficient of `g` is that of `𝒮` times `m m̄`, at every value `m ≠ 0`. -/
def TEqSigma.LeafOf (g : Σ m, Graph 3 m) {m : ℕ} (𝒮 : Graph 2 m) : Prop :=
  ∃ (x y α : Fin g.1) (e : Fin m ≃ {a : Fin g.1 // a ≠ x ∧ a ≠ y ∧ a ≠ α})
    (R : List (Comp (Atom 2 m))) (sy : Comp (Atom 3 g.1)) (X : List (Comp (Atom 3 g.1)))
    (ℓ : ℕ),
    α ≠ x ∧ α ≠ y ∧
    (sy = mkC (.waved .s) (.inr y) (.inr α) ∨ sy = mkC (.waved .s) (.inr α) (.inr y)) ∧
    (∀ c ∈ X, c = mkC .xdot (.inr α) (.inl 1) ∨ c = mkC .xdot (.inl 1) (.inr α) ∨
      c = mkC .xdot (.inr α) (.inl 2) ∨ c = mkC .xdot (.inl 2) (.inr α)) ∧
    (mkC .xdot (.inr α) (.inl 1) ∈ X ∨ mkC .xdot (.inl 1) (.inr α) ∈ X) ∧
    (mkC .xdot (.inr α) (.inl 2) ∈ X ∨ mkC .xdot (.inl 2) (.inr α) ∈ X) ∧
    g.2.comps.Perm (mkC (.theta []) (.inl 0) (.inr x) ::
      R.map (Comp.map (Sum.elim ![.inr x, .inr y] fun j => .inr (e j).1)) ++
      [sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++ X ++
      List.replicate ℓ (mkC .xdot (.inr α) (.inr α))) ∧
    𝒮.comps.Perm ((if x = y then [mkC .dot (.inl 0) (.inl 1)] else []) ++ R ++
      List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))) ∧
    ∀ z : ℂ, z ≠ 0 → Coeff.eval z g.2.coeff = Coeff.eval z (𝒮.coeff * (cm * cmb))

open Classical in
/-- The graph `𝒮` of an output graph `g` of [II, Lemma 6.7] ([II, (6.7)–(6.8)]): `[𝒮]` for one graph
`𝒮` with `TEqSigma.LeafOf g 𝒮`, chosen once, if there is one; `[]` otherwise. -/
def TEqSigma.sigma (g : Σ m, Graph 3 m) : Expansion 2 :=
  if h : ∃ (m : ℕ) (𝒮 : Graph 2 m), TEqSigma.LeafOf g 𝒮 then
    [⟨h.choose, h.choose_spec.choose⟩]
  else []

/-! ## Lists and walks -/

/-- Two members of a list of length `≤ 1` are equal. -/
private theorem TEqLeaf_eq_of_len {β : Type*} {l : List β} (h : l.length ≤ 1) {a b : β}
    (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l, h, ha, hb with
  | [z], _, ha, hb => rw [List.mem_singleton] at ha hb; rw [ha, hb]

/-- Two components of distinct indices with the property `p` give two members of the filter. -/
private theorem TEqLeaf_two_le {β : Type*} (p : β → Bool) :
    ∀ (l : List β) (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≠ j →
      p l[i] = true → p l[j] = true → 2 ≤ (l.filter p).length
  | [], _, _, hi, _, _, _, _ => absurd hi (by simp)
  | a :: t, i, j, hi, hj, hij, hpi, hpj => by
    match i, j, hi, hj, hij, hpi, hpj with
    | 0, 0, _, _, hij, _, _ => exact absurd rfl hij
    | 0, j + 1, _, hj, _, hpi, hpj =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpi hpj
      have : t[j]'(by simpa using hj) ∈ t.filter p := List.mem_filter.2 ⟨List.getElem_mem _, hpj⟩
      have := List.length_pos_of_mem this
      simp [hpi]; omega
    | i + 1, 0, hi, _, _, hpi, hpj =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpi hpj
      have : t[i]'(by simpa using hi) ∈ t.filter p := List.mem_filter.2 ⟨List.getElem_mem _, hpi⟩
      have := List.length_pos_of_mem this
      simp [hpj]; omega
    | i + 1, j + 1, hi, hj, hij, hpi, hpj =>
      simp only [List.getElem_cons_succ] at hpi hpj
      have := TEqLeaf_two_le p t i j (by simpa using hi) (by simpa using hj) (by omega) hpi hpj
      rw [List.filter_cons]; split <;> simp <;> omega

/-- The filter of `p = q ∨ r` with `q`, `r` exclusive is the filter of `q` and that of `r`, up to
order. -/
private theorem TEqLeaf_filter_split {β : Type*} (p q r : β → Bool) :
    ∀ l : List β, (∀ a ∈ l, p a = (q a || r a)) → (∀ a ∈ l, ¬ (q a = true ∧ r a = true)) →
      (l.filter p).Perm (l.filter q ++ l.filter r)
  | [], _, _ => by simp
  | a :: t, h1, h2 => by
    have ih := TEqLeaf_filter_split p q r t (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
      (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
    have ha := h1 a List.mem_cons_self
    have ha2 := h2 a List.mem_cons_self
    simp only [List.filter_cons, ha]
    cases hq : q a <;> cases hr : r a
    · simpa only [Bool.or_self, Bool.false_eq_true, ↓reduceIte] using ih
    · simpa only [Bool.or_true, Bool.false_eq_true, ↓reduceIte] using
        (ih.cons a).trans List.perm_middle.symm
    · simpa only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, List.cons_append] using
        ih.cons a
    · exact absurd ⟨hq, hr⟩ ha2

/-- A walk from a set to its complement has an edge with one end in the set and one outside. -/
private theorem TEqLeaf_reach_cross {V : Type*} {r : V → V → Prop} {P : V → Prop} {u v : V}
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

/-! ## The facts of an output graph read in the leaf form -/

section Facts

variable {N : ℕ} {Γ : Graph 3 N}

/-- No dotted edge joins an external and an internal atom: at `⊗` only diffusive edges, and no
`⊕/⊖`-recollision. -/
private theorem TEqLeaf_noMixed (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    {c : Comp (Atom 3 N)} (hc : c ∈ Γ.comps) (hd : c.kind = .dot) :
    ¬ (c.x.isLeft = true ∧ c.y.isRight = true) ∧ ¬ (c.x.isRight = true ∧ c.y.isLeft = true) := by
  have htd := List.all_eq_true.1 hTD c hc
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 hx
    fin_cases a
    · simp [ha, hd, Kind.isDiffusive] at htd
    · exact hNR ⟨c, hc, hd, Or.inl ⟨⟨1, by simp, ha⟩, hy⟩⟩
    · exact hNR ⟨c, hc, hd, Or.inl ⟨⟨2, by simp, ha⟩, hy⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 hy
    fin_cases a
    · simp [ha, hd, Kind.isDiffusive] at htd
    · exact hNR ⟨c, hc, hd, Or.inr ⟨⟨1, by simp, ha⟩, hx⟩⟩
    · exact hNR ⟨c, hc, hd, Or.inr ⟨⟨2, by simp, ha⟩, hx⟩⟩

/-- No external atom is in the dotted block of an internal atom. -/
private theorem TEqLeaf_unp (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    (a : Fin 3) (b : Fin N) : ¬ Γ.SameBlock (.inl a) (.inr b) := by
  intro h
  obtain ⟨u, v, ⟨c, hc, hd, hu, hv⟩, hcr⟩ :=
    TEqLeaf_reach_cross (P := fun w : Atom 3 N => w.isLeft = true) h rfl (by simp)
  have := TEqLeaf_noMixed hTD hNR hc hd
  subst hu hv
  rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact this.1 ⟨h1, by simpa using h2⟩
  · exact this.2 ⟨by simpa using h2, h1⟩

/-- Every external atom is unpinned. -/
private theorem TEqLeaf_unpinned (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    (a : Fin 3) : Γ.Unpinned (.inl a) :=
  ⟨rfl, TEqLeaf_unp hTD hNR a⟩

/-- No dotted edge: a dotted edge has an external end ([I, Def 2.11]), not joined to an
internal atom, and two distinct external atoms in one block would need an internal atom in it. -/
private theorem TEqLeaf_dotFree (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    {C : ℕ} (hN : Γ.Normal C) (hP : Γ.Plain) (hE : Γ.ExtClause) :
    ∀ c ∈ Γ.comps, c.kind ≠ .dot := by
  intro c hc hd
  have hm := TEqLeaf_noMixed hTD hNR hc hd
  have hne := (hP c hc).2.2.2.1 hd
  have hleft : c.x.isLeft = true ∧ c.y.isLeft = true := by
    rcases hN.1.noIntDot c hc hd with h | h
    · refine ⟨h, ?_⟩
      cases hy : c.y with
      | inl _ => rfl
      | inr _ => exact absurd ⟨h, by simp [hy]⟩ hm.1
    · refine ⟨?_, h⟩
      cases hx : c.x with
      | inl _ => rfl
      | inr _ => exact absurd ⟨by simp [hx], h⟩ hm.2
  obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 hleft.1
  have hsb : Γ.SameBlock c.x c.y := by
    refine SimpleGraph.Adj.reachable ?_
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ⟨c, hc, hd, rfl, rfl⟩⟩
  obtain ⟨b, hb⟩ := hE.1 c.x c.y hne hsb
  rw [ha] at hb
  exact TEqLeaf_unp hTD hNR a b hb

/-- With every external atom unpinned, the block normal form is the graph itself. -/
private theorem TEqLeaf_blockNorm (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2}) :
    Γ.blockNorm = Γ := by
  have hfa : ∀ u, Γ.flatAtom u = u := by
    intro u
    cases u with
    | inr _ => rfl
    | inl a =>
      have : Γ.anchor (.inl a) = none :=
        List.find?_eq_none.2 fun b _ => by simpa using TEqLeaf_unp hTD hNR a b
      simp [Graph.flatAtom, this]
  have hfc : ∀ c, Γ.flatComp c = c := by
    intro c
    unfold Graph.flatComp
    split
    · rfl
    · rw [hfa, hfa]
  obtain ⟨cs, co⟩ := Γ
  simp only [Graph.blockNorm]
  congr 1
  exact (List.map_congr_left fun c _ => hfc c).trans (List.map_id _)

/-- A random component (solid edge or weight) of a graph with the charge pattern `Graph.ColourInv'`
and a deterministic maximal subgraph is `G_{u⊕}` or `Ḡ_{u⊖}` with `u` internal. -/
private theorem TEqLeaf_random (hCI : Γ.ColourInv') (hMD : Γ.MaxDeterministic)
    {c : Comp (Atom 3 N)} (hc : c ∈ Γ.comps) (hr : c.kind.isRandom = true) :
    c.x.isRight = true ∧
      (c.kind = .G .plus ∧ c.y = .inl 1 ∨ c.kind = .G .minus ∧ c.y = .inl 2) := by
  obtain ⟨hx, hy0, hy1, hy2⟩ := (hCI c hc).1 hr
  refine ⟨hx, ?_⟩
  rcases hMD c hc hr with h | h
  · cases hcx : c.x <;> simp_all
  · obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 h
    fin_cases a
    · exact absurd ha hy0
    · exact Or.inl ⟨hy1 ha, ha⟩
    · exact Or.inr ⟨hy2 ha, ha⟩

/-- A red solid edge of the molecular graph `Graph.toMG'` is a component `Ḡ` of the graph. -/
private theorem TEqLeaf_cls_minus (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    (e : Fin Γ.comps.length ⊕ Fin 3) (h : Γ.toMG'.cls e = some .minus) :
    ∃ i, e = .inl i ∧ Γ.comps[i].kind = .G .minus := by
  cases e with
  | inl i =>
    refine ⟨i, rfl, ?_⟩
    simp only [Graph.toMG'] at h
    split_ifs at h
    have hk : (Γ.flatComp Γ.comps[i]).kind = Γ.comps[i].kind := by
      unfold Graph.flatComp; split <;> rfl
    rw [hk] at h
    generalize Γ.comps[i].kind = K at h ⊢
    cases K with
    | G ch => cases ch <;> simp_all [Kind.mclass]
    | aux j r b => cases b <;> simp_all [Kind.mclass]
    | _ => simp_all [Kind.mclass]
  | inr a =>
    have : Γ.anchor (.inl a) = none :=
      List.find?_eq_none.2 fun b _ => by simpa using TEqLeaf_unp hTD hNR a b
    simp [Graph.toMG', this] at h

/-- No proper isolated subset: in a globally standard graph it would have two red solid edges to its
complement ([II, Def 6.2]), while at most one component other than dotted and `×`-dotted edges is
at `⊖`. -/
private theorem TEqLeaf_noIso (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    (hCI : Γ.ColourInv') (hMD : Γ.MaxDeterministic) (hE : Γ.ExtClause) (hgs : gsPM' Γ) :
    ∀ P, ¬ Γ.toMG'.IsProperIso Γ.toMG'.int P := by
  intro P hP
  obtain ⟨-, e, e', hne, he, he'⟩ := hgs.2 P hP
  obtain ⟨i, rfl, hi⟩ := TEqLeaf_cls_minus hTD hNR e he.1
  obtain ⟨i', rfl, hi'⟩ := TEqLeaf_cls_minus hTD hNR e' he'.1
  have hii : (i : ℕ) ≠ i' := fun h => hne (by rw [Fin.ext h])
  have hdeg := (hE.2.2.2.1 (TEqLeaf_unpinned hTD hNR 2)).2
  have hy : ∀ (j : ℕ) (hj : j < Γ.comps.length), Γ.comps[j].kind = .G .minus →
      Γ.comps[j].y = .inl 2 := by
    intro j hj hk
    have hm : Γ.comps[j] ∈ Γ.comps := List.getElem_mem _
    rcases (TEqLeaf_random hCI hMD hm (by simp [hk, Kind.isRandom])).2 with h | h
    · rw [hk] at h; cases h.1
    · exact h.2
  simp only [Fin.getElem_fin] at hi hi'
  have := TEqLeaf_two_le (fun c => decide ((c.x = .inl 2 ∨ c.y = .inl 2) ∧ c.kind ≠ .dot ∧
    c.kind ≠ .xdot)) Γ.comps i i' i.2 i'.2 hii (by simp [hy i i.2 hi, hi])
    (by simp [hy i' i'.2 hi', hi'])
  unfold Graph.nonDotDeg at hdeg
  omega

/-- An internal atom of positive degree is standard neutral: the graph is non-expandable ((S4) of
[II, §6.3]), or its minimal isolated subset, here all internal molecules, is locally standard. -/
private theorem TEqLeaf_stdNeutral {n D : ℕ} (hSL : Γ.StratLeafB n D)
    (hNR : ¬ Γ.IsRecollision {1, 2}) (hL : Γ.LabelFree) (hord : Γ.ord ≤ n) (hnD : n ≤ D)
    (hiso : ∀ P, ¬ Γ.toMG'.IsProperIso Γ.toMG'.int P) (α : Fin N)
    (hdeg : Γ.deg (.inr α) ≠ 0) : Γ.stdNeutralAt (.inr α) = true := by
  have hnQ : ¬ Γ.IsQGraph := by
    rintro ⟨u, ⟨c, hc, hl⟩, -⟩
    rw [hL c hc] at hl
    cases hl
  rcases hSL.2 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨hM, -⟩
  · rcases h with h | h | h | h
    · exact absurd h hNR
    · omega
    · exact absurd h hnQ
    · obtain ⟨h1, h2⟩ := h.1.2.2 α
      rcases h1 with h1 | h1
      · exact absurd h1 hdeg
      · exact h2 h1
  · omega
  · have hmem : Γ.molRep (.inr α) ∈ Γ.toMG'.MIS := by
      unfold MGraph.MIS
      rw [@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _)]
      exact ⟨Finset.mem_image.2 ⟨α, Finset.mem_univ _, rfl⟩, fun P hP => absurd hP (hiso P)⟩
    obtain ⟨-, h⟩ := hM.2 α hmem
    rcases h with h | h
    · exact absurd h hdeg
    · exact h.2

/-- A standard neutral atom `u` ([I, Def 3.17]): three components other than `×`-dotted edges at
`u`, among them a waved edge `s` and a blue solid edge. -/
private theorem TEqLeaf_sn_parts {u : Atom 3 N} (h : Γ.stdNeutralAt u = true) :
    (Γ.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u)).length = 3 ∧
    (∃ c ∈ Γ.comps, c.kind = .waved .s ∧ (c.x = u ∨ c.y = u)) ∧
    ∃ c ∈ Γ.comps, c.kind = .G .plus ∧ (c.x = u ∨ c.y = u) := by
  unfold Graph.stdNeutralAt at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h3, -⟩, hs⟩, he⟩ := h
  refine ⟨beq_iff_eq.1 h3, ?_, ?_⟩
  · have hs' := beq_iff_eq.1 hs
    obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos (by omega :
      0 < (List.filter (fun c => c.kind == .waved .s)
        (Γ.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u))).length)
    rw [List.mem_filter, List.mem_filter] at hc
    obtain ⟨⟨hc, hc1⟩, hc2⟩ := hc
    refine ⟨c, hc, beq_iff_eq.1 hc2, ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc1
    exact hc1.2
  · have hE : ∃ e ∈ Γ.ends u, e.2 = .plus := by
      revert he
      generalize Γ.ends u = l
      intro he
      match l, he with
      | [e₁, e₂], he =>
        rw [Bool.and_eq_true] at he
        have hne : e₁.2 ≠ e₂.2 := by simpa using he.2
        cases h1 : e₁.2
        · exact ⟨e₁, by simp, h1⟩
        · cases h2 : e₂.2
          · exact ⟨e₂, by simp, h2⟩
          · exact absurd (h1.trans h2.symm) hne
    obtain ⟨e, he, hp⟩ := hE
    unfold Graph.ends at he
    rw [List.mem_filterMap] at he
    obtain ⟨c, hc, hf⟩ := he
    refine ⟨c, hc, ?_⟩
    cases hk : c.kind with
    | G ch =>
      rw [hk] at hf
      simp only at hf
      split_ifs at hf with h1 h2
      · cases hf; exact ⟨by rw [← hp], Or.inl h1.1⟩
      · cases hf; exact ⟨by rw [← hp], Or.inr h2.1⟩
    | _ => rw [hk] at hf; cases hf

/-- A component without minor and label is determined by its kind and its two atoms. -/
private theorem TEqLeaf_comp_eq {V : Type*} {c : Comp V} {k : Kind} {u v : V} (hk : c.kind = k)
    (hu : c.x = u) (hv : c.y = v) (hm : c.minor = []) (hl : c.label = none) : c = mkC k u v := by
  obtain ⟨k', u', v', m', l'⟩ := c
  simp only at hk hu hv hm hl
  subst hk hu hv hm hl
  rfl

/-- The facts of a deterministic output graph read in the proof of the leaf form. -/
private structure TEqLeaf_Ctx {N : ℕ} (Γ : Graph 3 N) (x y α : Fin N) (sy : Comp (Atom 3 N)) :
    Prop where
  lab : Γ.LabelFree
  minor : ∀ c ∈ Γ.comps, c.minor = []
  dotFree : ∀ c ∈ Γ.comps, c.kind ≠ .dot
  unp : ∀ a : Fin 3, Γ.Unpinned (.inl a)
  ci : Γ.ColourInv'
  md : Γ.MaxDeterministic
  ext : Γ.ExtClause
  normal : ∃ C, Γ.Normal C
  otimes : ∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) →
    c = mkC (.theta []) (.inl 0) (.inr x)
  thetaMem : mkC (.theta []) (.inl 0) (.inr x) ∈ Γ.comps
  otimesL : (Γ.comps.filter fun c => c.x == .inl 0 || c.y == .inl 0) =
    [mkC (.theta []) (.inl 0) (.inr x)]
  gp : mkC (.G .plus) (.inr α) (.inl 1) ∈ Γ.comps
  gm : mkC (.G .minus) (.inr α) (.inl 2) ∈ Γ.comps
  syMem : sy ∈ Γ.comps
  syForm : sy = mkC (.waved .s) (.inr y) (.inr α) ∨ sy = mkC (.waved .s) (.inr α) (.inr y)
  csα : (Γ.comps.filter fun c => c.kind != .xdot && (c.x == .inr α || c.y == .inr α)).Perm
    [sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)]
  xα : x ≠ α

/-- **The facts `TEqLeaf_Ctx`** of a graph with the clauses of a deterministic output graph of
order `≤ n ≤ D` of the run: the plain `Θ` edge `Θ_{⊗x}` at `⊗`, the red solid edge `Ḡ_{α⊖}` at `⊖`,
the standard neutral atom `α` with `G_{α⊕}` and the waved edge `s` between `α` and `y`. -/
private theorem TEqLeaf_ctx {n D C : ℕ} (hL : Γ.LabelFree) (hmin : ∀ c ∈ Γ.comps, c.minor = [])
    (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2}) (hN : Γ.Normal C) (hP : Γ.Plain)
    (hE : Γ.ExtClause) (hCIB : Γ.ColourInvB) (hMD : Γ.MaxDeterministic) (hgs : gsPM' Γ)
    (hSL : Γ.StratLeafB n D) (hord : Γ.ord ≤ n) (hnD : n ≤ D)
    (hO : ∃ (j : Fin Γ.comps.length) (v : Atom 3 N), v ≠ .inl 0 ∧
      Γ.comps[j].kind = .theta [] ∧ Γ.comps[j].minor = [] ∧ Γ.comps[j].label = none ∧
      (Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v) ∧
      ∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0)
    (hM : Γ.Unpinned (.inl 2) →
      ∃ c ∈ Γ.comps, c.kind = .G .minus ∧ c.y = .inl 2 ∧ ¬ Γ.Unpinned c.x) :
    ∃ x y α sy, TEqLeaf_Ctx Γ x y α sy := by
  have hU := TEqLeaf_unpinned hTD hNR
  have hCI : Γ.ColourInv' := by
    have h := hCIB
    unfold Graph.ColourInvB at h
    rwa [TEqLeaf_blockNorm hTD hNR] at h
  have hint : ∀ u : Atom 3 N, ¬ Γ.Unpinned u → ∃ a, u = .inr a := by
    intro u hu
    cases u with
    | inl a => exact absurd (hU a) hu
    | inr a => exact ⟨a, rfl⟩
  -- the `Θ` edge at `⊗`
  obtain ⟨j, v, hv0, hjk, hjm, hjl, ⟨hjx, hjy⟩, hjo⟩ := hO
  simp only [Fin.getElem_fin] at hjk hjm hjl hjx hjy
  have hjmem : Γ.comps[(j : ℕ)] ∈ Γ.comps := List.getElem_mem _
  obtain ⟨x, rfl⟩ : ∃ x, v = .inr x := by
    refine hint v fun hv => ?_
    have := ((hE.2.2.1 (hU 0)).2 _ hjmem (by simp [hjk, Kind.isDiffusive])).1 hjx
    rw [hjy] at this
    exact this hv
  have hΘ : Γ.comps[(j : ℕ)] = mkC (.theta []) (.inl 0) (.inr x) :=
    TEqLeaf_comp_eq hjk hjx hjy hjm hjl
  have hot : ∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) →
      c = mkC (.theta []) (.inl 0) (.inr x) := by
    intro c hc h0
    have hp := List.getElem_cons_eraseIdx_perm (l := Γ.comps) (n := j) j.2
    rcases List.mem_cons.1 (hp.mem_iff.2 hc) with h | h
    · rw [h]; exact hΘ
    · have := hjo c h
      rcases h0 with h0 | h0
      · exact absurd h0 this.1
      · exact absurd h0 this.2
  have hotL : (Γ.comps.filter fun c => c.x == .inl 0 || c.y == .inl 0) =
      [mkC (.theta []) (.inl 0) (.inr x)] := by
    have hp := List.getElem_cons_eraseIdx_perm (l := Γ.comps) (n := j) j.2
    have h1 : ((Γ.comps[(j : ℕ)] :: Γ.comps.eraseIdx j).filter
        fun c => c.x == .inl 0 || c.y == .inl 0) = [mkC (.theta []) (.inl 0) (.inr x)] := by
      rw [List.filter_cons_of_pos (by simp [hjx]), List.filter_eq_nil_iff.2 ?_, hΘ]
      intro c hc
      have := hjo c hc
      simp [this.1, this.2]
    exact List.perm_singleton.1 (h1 ▸ (hp.filter _)).symm
  -- the red solid edge at `⊖`
  obtain ⟨cm, hcm, hcmk, hcmy, hcmx⟩ := hM (hU 2)
  obtain ⟨α, hα⟩ := hint _ hcmx
  have hgm : mkC (.G .minus) (.inr α) (.inl 2) ∈ Γ.comps := by
    rw [← TEqLeaf_comp_eq hcmk hα hcmy (hmin cm hcm) (hL cm hcm)]; exact hcm
  -- `α` is standard neutral
  have hdeg : Γ.deg (.inr α) ≠ 0 := by
    unfold Graph.deg
    refine (List.length_pos_of_mem (a := mkC (.G .minus) (.inr α) (.inl 2)) ?_).ne'
    exact List.mem_filter.2 ⟨hgm, by simp [mkC, Kind.isSolid]⟩
  have hsn := TEqLeaf_stdNeutral hSL hNR hL hord hnD
    (TEqLeaf_noIso hTD hNR hCI hMD hE hgs) α hdeg
  obtain ⟨h3, ⟨cs, hcs, hcsk, hcsα⟩, ⟨cp, hcp, hcpk, hcpα⟩⟩ := TEqLeaf_sn_parts hsn
  -- the blue solid edge at `⊕`
  have hgp : mkC (.G .plus) (.inr α) (.inl 1) ∈ Γ.comps := by
    obtain ⟨-, h⟩ := TEqLeaf_random hCI hMD hcp (by simp [hcpk, Kind.isRandom])
    have hy : cp.y = .inl 1 := by
      rcases h with h | h
      · exact h.2
      · rw [hcpk] at h; cases h.1
    have hx : cp.x = .inr α := by
      rcases hcpα with h | h
      · exact h
      · rw [hy] at h; cases h
    rw [← TEqLeaf_comp_eq hcpk hx hy (hmin cp hcp) (hL cp hcp)]; exact hcp
  -- the waved edge at `α`
  obtain ⟨hsx, hsy⟩ := (hCI cs hcs).2 hcsk
  obtain ⟨y, hsform⟩ : ∃ y : Fin N, cs = mkC (.waved .s) (.inr y) (.inr α) ∨
      cs = mkC (.waved .s) (.inr α) (.inr y) := by
    obtain ⟨a, ha⟩ := Sum.isRight_iff.1 hsx
    obtain ⟨b, hb⟩ := Sum.isRight_iff.1 hsy
    rcases hcsα with h | h
    · exact ⟨b, Or.inr (TEqLeaf_comp_eq hcsk h hb (hmin cs hcs) (hL cs hcs))⟩
    · exact ⟨a, Or.inl (TEqLeaf_comp_eq hcsk ha h (hmin cs hcs) (hL cs hcs))⟩
  have hsk : cs.kind = .waved .s := hcsk
  -- the components at `α` other than `×`-dotted edges
  have hperm : (Γ.comps.filter fun c => c.kind != .xdot && (c.x == .inr α || c.y == .inr α)).Perm
      [cs, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] := by
    refine (List.Subperm.perm_of_length_le (List.Nodup.subperm ?_ ?_) ?_).symm
    · refine List.Nodup.of_map Comp.kind ?_
      simp only [List.map_cons, List.map_nil, hsk, mkC]
      decide
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      refine List.mem_filter.2 ⟨?_, ?_⟩
      · rcases hc with rfl | rfl | rfl
        · exact hcs
        · exact hgp
        · exact hgm
      · rcases hc with rfl | rfl | rfl
        · rcases hsform with h | h <;> rw [h] <;> simp [mkC]
        · simp [mkC]
        · simp [mkC]
    · rw [h3]; simp
  refine ⟨x, y, α, cs, hL, hmin, TEqLeaf_dotFree hTD hNR hN hP hE, hU, hCI, hMD, hE, ⟨C, hN⟩,
    hot, hΘ ▸ hjmem, hotL, hgp, hgm, hcs, hsform, hperm, ?_⟩
  rintro rfl
  have : mkC (.theta []) (.inl 0) (.inr x) ∈ [cs, mkC (.G .plus) (.inr x) (.inl 1),
      mkC (.G .minus) (.inr x) (.inl 2)] :=
    hperm.mem_iff.1 (List.mem_filter.2 ⟨hΘ ▸ hjmem, by simp [mkC]⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h | h
  · have := congrArg Comp.kind h; rw [hsk] at this; cases this
  · cases h
  · cases h

end Facts

/-! ## The components of an output graph of [II, Lemma 6.7] -/

section Cls

variable {N : ℕ} {Γ : Graph 3 N} {x y α : Fin N} {sy : Comp (Atom 3 N)}

/-- A component other than a dotted or `×`-dotted edge at `⊕` is `G_{α⊕}`. -/
private theorem TEqLeaf_Ctx.atPlus (h : TEqLeaf_Ctx Γ x y α sy) {c : Comp (Atom 3 N)}
    (hc : c ∈ Γ.comps) (h1 : c.x = .inl 1 ∨ c.y = .inl 1) (hx : c.kind ≠ .xdot) :
    c = mkC (.G .plus) (.inr α) (.inl 1) := by
  have hd := (h.ext.2.2.2.2 (h.unp 1)).2.2
  unfold Graph.nonDotDeg at hd
  refine TEqLeaf_eq_of_len hd (List.mem_filter.2 ⟨hc, ?_⟩) (List.mem_filter.2 ⟨h.gp, ?_⟩)
  · simp only [decide_eq_true_eq]; exact ⟨h1, h.dotFree c hc, hx⟩
  · simp [mkC]

/-- A component other than a dotted or `×`-dotted edge at `⊖` is `Ḡ_{α⊖}`. -/
private theorem TEqLeaf_Ctx.atMinus (h : TEqLeaf_Ctx Γ x y α sy) {c : Comp (Atom 3 N)}
    (hc : c ∈ Γ.comps) (h2 : c.x = .inl 2 ∨ c.y = .inl 2) (hx : c.kind ≠ .xdot) :
    c = mkC (.G .minus) (.inr α) (.inl 2) := by
  have hd := (h.ext.2.2.2.1 (h.unp 2)).2
  unfold Graph.nonDotDeg at hd
  refine TEqLeaf_eq_of_len hd (List.mem_filter.2 ⟨hc, ?_⟩) (List.mem_filter.2 ⟨h.gm, ?_⟩)
  · simp only [decide_eq_true_eq]; exact ⟨h2, h.dotFree c hc, hx⟩
  · simp [mkC]

/-- The `×`-dotted edges: a loop at an internal atom, or an edge between `α` and `⊕` or `⊖`. -/
private theorem TEqLeaf_Ctx.xdot (h : TEqLeaf_Ctx Γ x y α sy) {c : Comp (Atom 3 N)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .xdot) :
    (∃ a, c = mkC .xdot (.inr a) (.inr a)) ∨ c = mkC .xdot (.inr α) (.inl 1) ∨
      c = mkC .xdot (.inl 1) (.inr α) ∨ c = mkC .xdot (.inr α) (.inl 2) ∨
      c = mkC .xdot (.inl 2) (.inr α) := by
  have hm := h.minor c hc
  have hl := h.lab c hc
  by_cases hxy : c.x = c.y
  · left
    cases hcx : c.x with
    | inl a =>
      exact absurd ⟨hcx ▸ h.unp a, hxy ▸ hcx ▸ h.unp a⟩ (h.ext.2.1 c hc hk)
    | inr a => exact ⟨a, TEqLeaf_comp_eq hk hcx (hxy ▸ hcx) hm hl⟩
  · right
    obtain ⟨C, hN⟩ := h.normal
    obtain ⟨c', hc', hs, hends⟩ := (hN.2.2 c.x c.y hxy).1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    have hr : c'.kind.isRandom = true := by
      revert hs; cases c'.kind <;> simp [Kind.isSolid, Kind.isRandom]
    obtain ⟨hx', hcl⟩ := TEqLeaf_random h.ci h.md hc' hr
    rcases hcl with ⟨hk', hy'⟩ | ⟨hk', hy'⟩
    · have := h.atPlus hc' (Or.inr hy') (by rw [hk']; simp)
      subst this
      rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl (TEqLeaf_comp_eq hk e1.symm e2.symm hm hl)
      · exact Or.inr (Or.inl (TEqLeaf_comp_eq hk e2.symm e1.symm hm hl))
    · have := h.atMinus hc' (Or.inr hy') (by rw [hk']; simp)
      subst this
      rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inr (Or.inr (Or.inl (TEqLeaf_comp_eq hk e1.symm e2.symm hm hl)))
      · exact Or.inr (Or.inr (Or.inr (TEqLeaf_comp_eq hk e2.symm e1.symm hm hl)))

/-- **The components of the graph**: `Θ_{⊗x}`, the waved edge at `α`, `G_{α⊕}`, `Ḡ_{α⊖}`, a
`×`-dotted edge between `α` and `⊕` or `⊖`, a `×`-dotted loop at `α`, or a component whose two
atoms are internal atoms other than `α`. -/
private theorem TEqLeaf_Ctx.cls (h : TEqLeaf_Ctx Γ x y α sy) {c : Comp (Atom 3 N)}
    (hc : c ∈ Γ.comps) :
    c = mkC (.theta []) (.inl 0) (.inr x) ∨ c = sy ∨ c = mkC (.G .plus) (.inr α) (.inl 1) ∨
      c = mkC (.G .minus) (.inr α) (.inl 2) ∨ c = mkC .xdot (.inr α) (.inl 1) ∨
      c = mkC .xdot (.inl 1) (.inr α) ∨ c = mkC .xdot (.inr α) (.inl 2) ∨
      c = mkC .xdot (.inl 2) (.inr α) ∨ c = mkC .xdot (.inr α) (.inr α) ∨
      ∃ a b : Fin N, c.x = .inr a ∧ c.y = .inr b ∧ a ≠ α ∧ b ≠ α := by
  by_cases h0 : c.x = .inl 0 ∨ c.y = .inl 0
  · exact Or.inl (h.otimes c hc h0)
  have hrest : (c.x = .inl 1 ∨ c.y = .inl 1) ∨ (c.x = .inl 2 ∨ c.y = .inl 2) ∨
      (c.x = .inr α ∨ c.y = .inr α) ∨
      ∃ a b : Fin N, c.x = .inr a ∧ c.y = .inr b ∧ a ≠ α ∧ b ≠ α := by
    by_contra hn
    simp only [not_or, not_exists, not_and] at hn h0
    obtain ⟨⟨h1x, h1y⟩, ⟨h2x, h2y⟩, ⟨hαx, hαy⟩, hab⟩ := hn
    obtain ⟨h0x, h0y⟩ := h0
    cases hcx : c.x with
    | inl a => fin_cases a <;> simp_all
    | inr a =>
      cases hcy : c.y with
      | inl b => fin_cases b <;> simp_all
      | inr b => exact hab a b hcx hcy (fun e => hαx (e ▸ hcx)) (fun e => hαy (e ▸ hcy))
  by_cases hk : c.kind = .xdot
  · rcases h.xdot hc hk with ⟨a, rfl⟩ | e | e | e | e
    · by_cases ha : a = α
      · subst ha; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl rfl))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨a, a, rfl, rfl, ha, ha⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))
  · rcases hrest with h1 | h2 | hα | hab
    · exact Or.inr (Or.inr (Or.inl (h.atPlus hc h1 hk)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h.atMinus hc h2 hk))))
    · have hmem : c ∈ [sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] :=
        h.csα.mem_iff.1 (List.mem_filter.2 ⟨hc, by
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq]
          exact ⟨hk, hα⟩⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with e | e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hab))))))))

/-- The other end `y` of the waved edge at `α` is not `α`: otherwise no component would leave
`{α, ⊕, ⊖}`, and the graph would not be connected. -/
private theorem TEqLeaf_Ctx.yα (h : TEqLeaf_Ctx Γ x y α sy) : y ≠ α := by
  rintro rfl
  obtain ⟨C, hN⟩ := h.normal
  have hS : sy = mkC (.waved .s) (.inr y) (.inr y) := by rcases h.syForm with e | e <;> exact e
  have hreach : Γ.edgeGraph.Reachable (.inr y) (.inl 0) := hN.1.connected _ _
  obtain ⟨a, b, ⟨c, hc, ha, hb⟩, hab⟩ :=
    TEqLeaf_reach_cross (P := fun u : Atom 3 N => u = .inr y ∨ u = .inl 1 ∨ u = .inl 2) hreach
      (Or.inl rfl) (by simp)
  subst ha hb
  have hxy := h.xα
  rcases h.cls hc with e | e | e | e | e | e | e | e | e | ⟨a', b', hx, hy, ha', hb'⟩
  all_goals first
    | (subst e; simp [mkC, hxy, hS] at hab)
    | (rw [hx, hy] at hab; simp [ha', hb'] at hab)

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The leaf form of a graph with the facts `TEqLeaf_Ctx`**: the graph `𝒮` read off it, with
the internal atoms other than `x`, `y`, `α` numbered by `Fintype.equivFin`, satisfies
`TEqSigma.LeafOf`. -/
private theorem TEqLeaf_Ctx.leafOf (h : TEqLeaf_Ctx Γ x y α sy) :
    ∃ (m : ℕ) (𝒮 : Graph 2 m), TEqSigma.LeafOf ⟨N, Γ⟩ 𝒮 := by
  have hyα := h.yα
  have hxα := h.xα
  set tPM : Comp (Atom 3 N) → Bool :=
    fun c => c.x == .inl 1 || c.y == .inl 1 || c.x == .inl 2 || c.y == .inl 2 with htPM
  set P : Comp (Atom 3 N) → Bool := fun c => (c.x == .inl 0 || c.y == .inl 0) || tPM c ||
    (c.x == .inr α || c.y == .inr α) with hP
  set q₂ : Comp (Atom 3 N) → Bool :=
    fun c => c.kind != .xdot && (c.x == .inr α || c.y == .inr α) with hq₂
  set q₃ : Comp (Atom 3 N) → Bool := fun c => c.kind == .xdot && tPM c with hq₃
  set q₄ : Comp (Atom 3 N) → Bool :=
    fun c => c.kind == .xdot && !tPM c && (c.x == .inr α || c.y == .inr α) with hq₄
  have hpt : ∀ c ∈ Γ.comps,
      (P c = true ↔ ((c.x == .inl 0 || c.y == .inl 0) || (q₂ c || (q₃ c || q₄ c))) = true) ∧
      ¬ ((c.x == .inl 0 || c.y == .inl 0) = true ∧ (q₂ c || (q₃ c || q₄ c)) = true) ∧
      ¬ (q₂ c = true ∧ (q₃ c || q₄ c) = true) ∧ ¬ (q₃ c = true ∧ q₄ c = true) := by
    intro c hc
    rcases h.cls hc with e | e | e | e | e | e | e | e | e | ⟨a, b, hx, hy, ha, hb⟩
    all_goals first
      | (subst e; simp [hP, hq₂, hq₃, hq₄, htPM, mkC, hxα, hyα, Ne.symm hxα, Ne.symm hyα]; done)
      | (rcases h.syForm with e' | e' <;> subst e' <;> subst e <;>
          simp [hP, hq₂, hq₃, hq₄, htPM, mkC, hxα, hyα, Ne.symm hxα, Ne.symm hyα]; done)
      | (simp [hP, hq₂, hq₃, hq₄, htPM, hx, hy, ha, hb]; done)
  -- the components split by the predicates
  have s1 := (List.filter_append_perm P Γ.comps).symm
  have s2 := TEqLeaf_filter_split P (fun c => c.x == .inl 0 || c.y == .inl 0)
    (fun c => q₂ c || (q₃ c || q₄ c)) Γ.comps
    (fun c hc => Bool.eq_iff_iff.2 (hpt c hc).1) (fun c hc => (hpt c hc).2.1)
  have s3 := TEqLeaf_filter_split (fun c => q₂ c || (q₃ c || q₄ c)) q₂ (fun c => q₃ c || q₄ c)
    Γ.comps (fun _ _ => rfl) (fun c hc => (hpt c hc).2.2.1)
  have s4 := TEqLeaf_filter_split (fun c => q₃ c || q₄ c) q₃ q₄ Γ.comps (fun _ _ => rfl)
    (fun c hc => (hpt c hc).2.2.2)
  -- the `×`-dotted loops at `α`
  set ℓ := (Γ.comps.filter q₄).length with hℓ
  have hq4 : Γ.comps.filter q₄ = List.replicate ℓ (mkC .xdot (.inr α) (.inr α)) := by
    refine List.eq_replicate_iff.2 ⟨rfl, fun c hc => ?_⟩
    obtain ⟨hc, hq⟩ := List.mem_filter.1 hc
    rcases h.cls hc with e | e | e | e | e | e | e | e | e | ⟨a, b, hx, hy, ha, hb⟩
    all_goals first
      | exact e
      | (subst e; simp [hq₄, htPM, mkC] at hq; done)
      | (rcases h.syForm with e' | e' <;> subst e' <;> subst e <;> simp [hq₄, mkC] at hq; done)
      | (simp [hq₄, htPM, hx, hy, ha, hb] at hq; done)
  -- the components away from `⊗`, `⊕`, `⊖`, `α`
  set Rest := Γ.comps.filter fun c => !P c with hRest
  have hRest' : ∀ c ∈ Rest, ∃ a b : Fin N, c = ⟨c.kind, .inr a, .inr b, [], none⟩ ∧
      a ≠ α ∧ b ≠ α := by
    intro c hc
    obtain ⟨hc, hq⟩ := List.mem_filter.1 hc
    rcases h.cls hc with e | e | e | e | e | e | e | e | e | ⟨a, b, hx, hy, ha, hb⟩
    all_goals first
      | (subst e; simp [hP, htPM, mkC] at hq; done)
      | (rcases h.syForm with e' | e' <;> subst e' <;> subst e <;> simp [hP, mkC] at hq; done)
      | skip
    refine ⟨a, b, ?_, ha, hb⟩
    rw [← hx, ← hy, ← h.minor c hc, ← h.lab c hc]
  -- the atoms of `𝒮`
  set e : Fin (Fintype.card {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) ≃
      {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α} := (Fintype.equivFin _).symm with he
  set φ : Atom 2 (Fintype.card {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) → Atom 3 N :=
    Sum.elim ![.inr x, .inr y] fun j => .inr (e j).1 with hφ
  let ψ : Atom 3 N → Atom 2 (Fintype.card {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) := fun u =>
    match u with
    | .inl _ => .inl 0
    | .inr a =>
      if hx : a = x then .inl 0 else if hy : a = y then .inl 1 else
        if hα : a = α then .inl 0 else .inr (e.symm ⟨a, hx, hy, hα⟩)
  have hφψ : ∀ a : Fin N, a ≠ α → φ (ψ (.inr a)) = .inr a := by
    intro a ha
    by_cases h1 : a = x
    · subst h1; simp [ψ, hφ]
    by_cases h2 : a = y
    · subst h2; simp [ψ, hφ, h1]
    simp [ψ, hφ, h1, h2, ha]
  set R := Rest.map (Comp.map ψ) with hR
  have hRφ : R.map (Comp.map φ) = Rest := by
    rw [hR, List.map_map]
    refine (List.map_congr_left fun c hc => ?_).trans (List.map_id _)
    obtain ⟨a, b, hc', ha, hb⟩ := hRest' c hc
    rw [hc']
    simp [Comp.map, hφψ a ha, hφψ b hb]
  -- the `×`-dotted edges between `α` and `⊕`, `⊖`
  have hXf : ∀ c ∈ Γ.comps.filter q₃, c = mkC .xdot (.inr α) (.inl 1) ∨
      c = mkC .xdot (.inl 1) (.inr α) ∨ c = mkC .xdot (.inr α) (.inl 2) ∨
      c = mkC .xdot (.inl 2) (.inr α) := by
    intro c hc
    obtain ⟨hc, hq⟩ := List.mem_filter.1 hc
    rcases h.cls hc with e | e | e | e | e | e | e | e | e | ⟨a, b, hx, hy, ha, hb⟩
    all_goals first
      | exact Or.inl e
      | exact Or.inr (Or.inl e)
      | exact Or.inr (Or.inr (Or.inl e))
      | exact Or.inr (Or.inr (Or.inr e))
      | (subst e; simp [hq₃, htPM, mkC] at hq; done)
      | (rcases h.syForm with e' | e' <;> subst e' <;> subst e <;> simp [hq₃, mkC] at hq; done)
      | (simp [hq₃, htPM, hx, hy] at hq; done)
  obtain ⟨C, hN⟩ := h.normal
  have hX : ∀ k : Fin 3, k ≠ 0 →
      ∃ c ∈ Γ.comps.filter q₃, c = mkC .xdot (.inr α) (.inl k) ∨
        c = mkC .xdot (.inl k) (.inr α) := by
    intro k hk
    have hsol : ∃ c ∈ Γ.comps, c.kind.isSolid = true ∧
        (c.x = .inr α ∧ c.y = .inl k ∨ c.x = .inl k ∧ c.y = .inr α) := by
      fin_cases k
      · exact absurd rfl hk
      · exact ⟨_, h.gp, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, h.gm, rfl, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨c, hc, hk', hends⟩ := (hN.2.2 (.inr α) (.inl k) (by simp)).2 hsol
    have hck : c = mkC .xdot (.inr α) (.inl k) ∨ c = mkC .xdot (.inl k) (.inr α) := by
      rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl (TEqLeaf_comp_eq hk' e1 e2 (h.minor c hc) (h.lab c hc))
      · exact Or.inr (TEqLeaf_comp_eq hk' e1 e2 (h.minor c hc) (h.lab c hc))
    refine ⟨c, List.mem_filter.2 ⟨hc, ?_⟩, hck⟩
    fin_cases k
    · exact absurd rfl hk
    all_goals rcases hck with rfl | rfl <;> simp [hq₃, htPM, mkC]
  obtain ⟨c1, hc1, hc1'⟩ := hX 1 (by decide)
  obtain ⟨c2, hc2, hc2'⟩ := hX 2 (by decide)
  -- the components of the graph, up to order
  have key : Γ.comps.Perm (mkC (.theta []) (.inl 0) (.inr x) :: R.map (Comp.map φ) ++
      [sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++
      Γ.comps.filter q₃ ++ List.replicate ℓ (mkC .xdot (.inr α) (.inr α))) := by
    refine s1.trans ?_
    have h5 := s2.trans (List.Perm.append_left _ (s3.trans (List.Perm.append h.csα s4)))
    rw [h.otimesL, hq4] at h5
    refine (List.Perm.append_right _ h5).trans ?_
    rw [hRφ]
    have hc := (List.perm_append_comm (l₁ := [sy, mkC (.G .plus) (.inr α) (.inl 1),
      mkC (.G .minus) (.inr α) (.inl 2)] ++ (Γ.comps.filter q₃ ++
        List.replicate ℓ (mkC .xdot (.inr α) (.inr α)))) (l₂ := Rest)).cons
      (mkC (.theta []) (.inl 0) (.inr x))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
      using hc
  refine ⟨_, ⟨(if x = y then [mkC .dot (.inl 0) (.inl 1)] else []) ++ R ++
      List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0)),
    Γ.coeff * (MvPolynomial.X .mInv * MvPolynomial.X .mBarInv)⟩, x, y, α, e, R, sy,
    Γ.comps.filter q₃, ℓ, Ne.symm hxα, Ne.symm hyα, h.syForm, hXf, ?_, ?_, key,
    List.Perm.refl _, ?_⟩
  · rcases hc1' with rfl | rfl
    · exact Or.inl hc1
    · exact Or.inr hc1
  · rcases hc2' with rfl | rfl
    · exact Or.inl hc2
    · exact Or.inr hc2
  · intro z hz
    have hz' : star z ≠ 0 := star_ne_zero.2 hz
    simp only [Coeff.eval, cm, cmb, map_mul, MvPolynomial.eval_X, CVar.eval]
    field_simp

end Cls

/-! ## The scaling order of a graph of the leaf form -/

/-- The number of internal atoms other than `x`, `y`, `α`: `n - 2` if `x = y`, `n - 3` otherwise. -/
private theorem TEqLeaf_card {N : ℕ} (x y α : Fin N) (hαx : α ≠ x) (hαy : α ≠ y) :
    Fintype.card {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α} + (if x = y then 2 else 3) = N := by
  have h1 : Fintype.card {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α} =
      Fintype.card {a : Fin N // ¬ (a ∈ ({x, y, α} : Finset (Fin N)))} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun a => by simp)
  rw [h1, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have hle : ({x, y, α} : Finset (Fin N)).card ≤ N := by
    simpa using Finset.card_le_univ ({x, y, α} : Finset (Fin N))
  split_ifs with hxy
  · subst hxy
    have : ({x, x, α} : Finset (Fin N)).card = 2 := by
      rw [Finset.insert_eq_of_mem (by simp), Finset.card_pair (Ne.symm hαx)]
    omega
  · have : ({x, y, α} : Finset (Fin N)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, Ne.symm hαx]),
        Finset.card_pair (Ne.symm hαy)]
    omega

/-- A list of even integers has an even sum. -/
private theorem TEqLeaf_even_sumZ : ∀ l : List ℤ, (∀ a ∈ l, Even a) → Even l.sum
  | [], _ => by simp
  | a :: l, h => by
    rw [List.sum_cons]
    exact (h a List.mem_cons_self).add
      (TEqLeaf_even_sumZ l fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- A list of even natural numbers has an even sum. -/
private theorem TEqLeaf_even_sum : ∀ o : List ℕ, (∀ j ∈ o, j % 2 = 0) → Even (o.sum : ℤ)
  | [], _ => by simp
  | j :: o, h => by
    have h1 := h j List.mem_cons_self
    have h2 := TEqLeaf_even_sum o fun k hk => h k (List.mem_cons_of_mem _ hk)
    simp only [List.sum_cons, Nat.cast_add]
    exact (Int.even_coe_nat j |>.2 (Nat.even_iff.2 h1)).add h2

/-- **The scaling order of the leaf form**: if `TEqSigma.LeafOf g 𝒮`, then `𝒮` has the scaling
order of `g` (`2 + (2 + 1 + 1) - 2·3 = 0` for `Θ_{⊗x}`, `s_{yα} G_{α⊕} Ḡ_{α⊖}` and `x`, `y`, `α`;
at `x = y` the dotted edge of `𝒮` counts `2` against the one atom `x = y`); and the scaling order
of `g` is even when every component of `g` between two internal atoms has an even scaling order. -/
private theorem TEqLeaf_ord {g : Σ m, Graph 3 m} {m : ℕ} {𝒮 : Graph 2 m}
    (h : TEqSigma.LeafOf g 𝒮) : 𝒮.ord = g.2.ord ∧
      ((∀ c ∈ g.2.comps, c.x.isRight = true → c.y.isRight = true → Even c.kind.ord) →
        Even g.2.ord) := by
  obtain ⟨x, y, α, e, R, sy, X, ℓ, hαx, hαy, hsy, hX, -, -, hg, hS, -⟩ := h
  have hX0 : (X.map fun c => c.kind.ord).sum = 0 := by
    refine List.sum_eq_zero fun a ha => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    rcases hX c hc with rfl | rfl | rfl | rfl <;> rfl
  have hsy2 : sy.kind.ord = 2 := by rcases hsy with rfl | rfl <;> rfl
  have hRφ : ∀ f : Atom 2 m → Atom 3 g.1,
      ((R.map (Comp.map f)).map fun c => c.kind.ord) = R.map fun c => c.kind.ord := fun f => by
    rw [List.map_map]; rfl
  have hsg : (g.2.comps.map fun c => c.kind.ord).sum = (R.map fun c => c.kind.ord).sum + 6 := by
    rw [(hg.map _).sum_eq]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, hRφ, hX0,
      hsy2, List.map_replicate, List.sum_replicate, List.map_nil, List.sum_nil]
    simp only [mkC, Kind.ord, List.sum_nil, List.length_nil]
    ring
  have hsS : (𝒮.comps.map fun c => c.kind.ord).sum =
      (if x = y then 2 else 0) + (R.map fun c => c.kind.ord).sum := by
    rw [(hS.map _).sum_eq]
    split_ifs <;> simp [mkC, Kind.ord]
  have hc := TEqLeaf_card x y α hαx hαy
  rw [← Fintype.card_congr e, Fintype.card_fin] at hc
  refine ⟨?_, fun hev => ?_⟩
  · unfold Graph.ord
    rw [hsg, hsS]
    split_ifs at hc ⊢ <;> push_cast [← hc] <;> ring
  · have hR : Even (R.map fun c => c.kind.ord).sum := by
      rw [← hRφ (Sum.elim ![.inr x, .inr y] fun j => .inr (e j).1)]
      refine TEqLeaf_even_sumZ _ fun a ha => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
      refine hev c (hg.mem_iff.2 ?_) ?_ ?_
      · simp only [List.cons_append, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (Or.inl (Or.inl hc)))
      · obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc
        simp only [Comp.map]
        cases c'.x with
        | inl i => fin_cases i <;> rfl
        | inr j => rfl
      · obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc
        simp only [Comp.map]
        cases c'.y with
        | inl i => fin_cases i <;> rfl
        | inr j => rfl
    unfold Graph.ord
    rw [hsg]
    exact (hR.add (by decide : Even (6 : ℤ))).sub (even_two_mul _)

/-- A component with the run kinds `Graph.RunKinds K` of a graph with a deterministic maximal
subgraph whose two atoms are internal has an even scaling order: it is a waved, dotted,
`×`-dotted or `Θ` edge, and the labels of `Θ` edges have even entries ([II, (2.6)]). -/
private theorem TEqLeaf_even_int {N K : ℕ} {Γ : Graph 3 N} (hK : Γ.RunKinds K)
    (hMD : Γ.MaxDeterministic) :
    ∀ c ∈ Γ.comps, c.x.isRight = true → c.y.isRight = true → Even c.kind.ord := by
  intro c hc hx hy
  have hk := List.all_eq_true.1 hK c hc
  have hnr : c.kind.isRandom = false := by
    cases h : c.kind.isRandom
    · rfl
    · rcases hMD c hc h with h' | h'
      · cases hcx : c.x <;> simp_all
      · cases hcy : c.y <;> simp_all
  unfold Comp.isRunKind at hk
  cases hck : c.kind with
  | theta o =>
    rw [hck] at hk
    have h2 := TEqLeaf_even_sum o fun j hj => by
      have := List.all_eq_true.1 hk j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
      exact this.2
    simp only [Kind.ord]
    exact (h2.add (by decide : Even (2 : ℤ))).sub (even_two_mul _)
  | waved w => simp [Kind.ord]
  | dot => simp [Kind.ord]
  | xdot => simp [Kind.ord]
  | thetaErr a b => rw [hck] at hk; cases hk
  | ghost => rw [hck] at hk; cases hk
  | aux a b d => rw [hck] at hk; cases hk
  | _ => rw [hck] at hnr; cases hnr

/-! ## The leaf form of the output graphs of [II, Lemma 6.7] -/

/-- **The output graphs of [II, Lemma 6.7] have the leaf form** ([II, Lemma 6.7], [II, (6.7)],
[II, Def 2.7 (i)]): for `n ≥ 3` and a record `𝒯` that is the structural part of an `(n - 1)`-th
order `T`-expansion with error order `D`, every output graph `g` of the run `RunCompare.run` of
[II, Strategy 6.6] with the family `TEqSigma.qFam` that is of the class `Graph.LeafDet`, not a
`⊕/⊖`-recollision graph and of scaling order `≤ n` has `TEqSigma.sigma g = [𝒮]` with
`TEqSigma.LeafOf g 𝒮`; `𝒮` has the scaling order of `g`, which is even and `≥ 4`. -/
theorem TEqSigma.detLeaf_form : ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n →
    𝒯.IsTExpStruct Sig (n - 1) D → ∀ g ∈ RunCompare.run TEqSigma.qFam n D 𝒯, g.2.LeafDet →
    ¬ g.2.IsRecollision {1, 2} → g.2.ord ≤ n →
    ∃ (m : ℕ) (𝒮 : Graph 2 m), TEqSigma.sigma g = [⟨m, 𝒮⟩] ∧ TEqSigma.LeafOf g 𝒮 ∧
      𝒮.ord = g.2.ord ∧ Even g.2.ord ∧ 4 ≤ g.2.ord := by
  intro n D Sig 𝒯 hn hT g hg hdet hNR hord
  have hspec := RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig 𝒯 hn hT
  have hsel := hspec.1
  obtain ⟨hSL, -, ⟨C, hN⟩, hLC, hPl, -⟩ := hspec.2.2 g hg
  obtain ⟨hL, hgs, hMD, hE, hCIB⟩ := hdet
  have hnD : n ≤ D := by have := hT.1; omega
  have hP : g.2.Plain := hPl (by omega)
  obtain ⟨hO, -, hmin⟩ :=
    RunOtimes.selRun_otimes _ TEqSigma.qFam_spec n D Sig 𝒯 hn hT _ hsel g hg
  have hnQ : ¬ g.2.IsQGraph := by
    rintro ⟨u, ⟨c, hc, hl⟩, -⟩
    rw [hL c hc] at hl
    cases hl
  have hM := (RunMinus.selRun_minus _ TEqSigma.qFam_spec n D Sig 𝒯 hn hT _ hsel g hg hnQ).1
  have hK := (RunExports.selRun_exports _ TEqSigma.qFam_spec n D Sig 𝒯 hn hT _ hsel g hg).2.1
  have h3 := RunExports.selRun_labelFree_ord _ TEqSigma.qFam_spec n D Sig 𝒯 hn hT _ hsel g hg hL
  obtain ⟨x, y, α, sy, hctx⟩ :=
    TEqLeaf_ctx hL hmin hLC.1 hNR hN hP hE hCIB hMD hgs hSL hord hnD hO hM
  have hex : ∃ (m : ℕ) (𝒮 : Graph 2 m), TEqSigma.LeafOf g 𝒮 := hctx.leafOf
  obtain ⟨hord', hev⟩ := TEqLeaf_ord hex.choose_spec.choose_spec
  have hE2 := hev (TEqLeaf_even_int hK hMD)
  refine ⟨hex.choose, hex.choose_spec.choose, ?_, hex.choose_spec.choose_spec, hord', hE2, ?_⟩
  · unfold TEqSigma.sigma
    rw [dite_eq_left hex]
  · obtain ⟨r, hr⟩ := hE2
    omega

section Instances

end Instances

end RBM8D.Graphs
