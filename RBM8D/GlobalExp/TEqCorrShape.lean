module

public import RBM8D.GlobalExp.TEqShape

@[expose] public section

/-!
# The shape of the correction graphs of the `n`-th order `T`-equation

The correction graphs `Θ_{⊗x} 𝒮_{xy} τ_{y,⊕⊖}` of an output graph `Θ_{⊗x} 𝒮_{xy} t_{y,⊕⊖}` of
[II, Lemma 6.7] (`TEqSigma.corr`, the `t → T` rewriting before [II, (6.7)], with the three
recollision terms `τ` of [II, (4.15)]) have the properties that [II, Def 3.3 (1), (4)] asks of the
graphs of `P_IT^{(n)}` and `A_IT^{(>n)}`: normal regular ([II, Def 3.2 (1)]), with the kinds of
[II, Def 3.2 (2)] and labels of entries in `[4, n - 1]`, with the clause on the external atoms
[II, Def 3.2 (9)], doubly connected [II, Def 3.2 (10)], and of the form `∑_x Θ_{a x} 𝒢_{x, b₁ b₂}`
of [II, Def 3.3 (4)] (`TEqSigma.corr_shape`).
-/

noncomputable section

namespace RBM8D.Graphs

/-! ## Maps of components and walks -/

/-- The image of the image of a component is its image under the composite. -/
private theorem TEqCorrShape_map_map {U V W : Type*} (f : V → W) (g : U → V) (c : Comp U) :
    (c.map g).map f = c.map (f ∘ g) := by
  obtain ⟨k, x, y, mi, lab⟩ := c
  simp only [Comp.map, List.map_map, Option.map_map, Prod.map_comp_map, Function.id_comp,
    Function.comp_apply]

/-- The image of a component without minor and label. -/
private theorem TEqCorrShape_map_mkC {V W : Type*} (f : V → W) (κ : Kind) (u v : V) :
    (mkC κ u v).map f = mkC κ (f u) (f v) := rfl

/-- Reachability is carried by a map that sends every edge to two atoms joined by a path. -/
private theorem TEqCorrShape_reach_map {V W : Type*} {r : V → V → Prop} {G : SimpleGraph W}
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
private theorem TEqCorrShape_reach_rel {W : Type*} {r : W → W → Prop} {u v : W} (h : r u v) :
    (SimpleGraph.fromRel r).Reachable u v := by
  by_cases huv : u = v
  · subst huv; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨huv, Or.inl h⟩)

/-- The image of a sublist up to order under a map. -/
private theorem TEqCorrShape_subperm_map {β γ : Type*} (f : β → γ) {l₁ l₂ : List β}
    (h : l₁.Subperm l₂) : (l₁.map f).Subperm (l₂.map f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

/-- The relation of the components of a given kind of a graph. -/
private def TEqCorrShape_rel {k n : ℕ} (Γ : Graph k n) (q : Kind → Prop) :
    Atom k n → Atom k n → Prop :=
  fun u v => ∃ c ∈ Γ.comps, q c.kind ∧ c.x = u ∧ c.y = v

/-- The graph of all components as the graph of a relation. -/
private theorem TEqCorrShape_edge_eq {k n : ℕ} (Γ : Graph k n) :
    Γ.edgeGraph = SimpleGraph.fromRel (TEqCorrShape_rel Γ fun _ => True) := by
  unfold Graph.edgeGraph TEqCorrShape_rel
  simp only [true_and]

/-- The graph of the waved and diffusive components as the graph of a relation. -/
private theorem TEqCorrShape_wt_eq {k n : ℕ} (Γ : Graph k n) :
    Γ.wavedThetaGraph = SimpleGraph.fromRel (TEqCorrShape_rel Γ
      fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true) := rfl

/-- The molecular graph as the graph of a relation. -/
private theorem TEqCorrShape_mol_eq {k n : ℕ} (Γ : Graph k n) :
    Γ.molGraph = SimpleGraph.fromRel (TEqCorrShape_rel Γ fun κ => κ.joinsMol = true) := rfl

/-! ## The recollision terms of [II, (4.15)] -/

/-- The components other than `s_{⊗α}` of the three recollision terms `τ` of [II, (4.15)] with
the internal atom `α = A`: `w⁺_α Ḡ_{α⊖} δ_{α⊕} ×_{α⊖}`, `G_{α⊕} w⁻_α ×_{α⊕} δ_{α⊖}` and
`w⁺_α w⁻_α δ_{α⊕} δ_{α⊖}`. -/
private def TEqCorrShape_tail {M : ℕ} (A : Fin M) : Fin 3 → List (Comp (Atom 3 M))
  | 0 => [mkC (.weight .plus) (.inr A) (.inr A), mkC (.G .minus) (.inr A) (.inl 2),
      mkC .dot (.inr A) (.inl 1), mkC .xdot (.inr A) (.inl 2)]
  | 1 => [mkC (.G .plus) (.inr A) (.inl 1), mkC (.weight .minus) (.inr A) (.inr A),
      mkC .xdot (.inr A) (.inl 1), mkC .dot (.inr A) (.inl 2)]
  | 2 => [mkC (.weight .plus) (.inr A) (.inr A), mkC (.weight .minus) (.inr A) (.inr A),
      mkC .dot (.inr A) (.inl 1), mkC .dot (.inr A) (.inl 2)]

/-- The image of the components of a recollision term under a map that fixes `⊕`, `⊖`. -/
private theorem TEqCorrShape_tail_map {M M' : ℕ} (f : Atom 3 M → Atom 3 M') (A : Fin M)
    (A' : Fin M') (hA : f (.inr A) = .inr A') (h1 : f (.inl 1) = .inl 1)
    (h2 : f (.inl 2) = .inl 2) (i : Fin 3) :
    (TEqCorrShape_tail A i).map (Comp.map f) = TEqCorrShape_tail A' i := by
  fin_cases i <;> simp [TEqCorrShape_tail, TEqCorrShape_map_mkC, hA, h1, h2]

/-- The components of a recollision term: no minor, no label, first atom `α`, second atom `α`,
`⊕` or `⊖`, not diffusive, joining molecules only as a dotted edge, of the kinds of
[II, Def 3.2 (2)]. -/
private theorem TEqCorrShape_tail_mem {M : ℕ} (A : Fin M) (i : Fin 3) (K : ℕ) :
    ∀ c ∈ TEqCorrShape_tail A i, c.minor = [] ∧ c.label = none ∧ c.x = .inr A ∧
      (c.y = .inr A ∨ c.y = .inl 1 ∨ c.y = .inl 2) ∧ c.kind.isDiffusive = false ∧
      (c.kind.joinsMol = true → c.kind = .dot) ∧ c.isTKind K = true := by
  intro c hc
  fin_cases i <;> simp only [TEqCorrShape_tail, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
    rcases hc with rfl | rfl | rfl | rfl <;>
    simp [mkC, Kind.isDiffusive, Kind.joinsMol, Comp.isTKind]

/-- Each recollision term has a component at `⊕` that is a blue solid or dotted edge and one at
`⊖` that is a red solid or dotted edge, both from `α`. -/
private theorem TEqCorrShape_tail_ext {M : ℕ} (A : Fin M) (i : Fin 3) :
    (∃ c ∈ TEqCorrShape_tail A i, (c.kind = .G .plus ∨ c.kind = .dot) ∧ c.x = .inr A ∧
      c.y = .inl 1) ∧
    ∃ c ∈ TEqCorrShape_tail A i, (c.kind = .G .minus ∨ c.kind = .dot) ∧ c.x = .inr A ∧
      c.y = .inl 2 := by
  fin_cases i <;> simp [TEqCorrShape_tail, mkC]

/-- **The local clauses of a normal regular graph** ([I, Def 2.11 (iii), (iv)]): if every
component is not solid, not dotted, and a loop if `×`-dotted, or is a component of a recollision
term at the internal atom `α`, all of whose components are present, then dotted edges have an
external end, solid edges join distinct atoms, and distinct atoms are joined by a `×`-dotted edge
iff they are joined by a solid edge. -/
private theorem TEqCorrShape_local {M : ℕ} {Γ : Graph 3 M} {A : Fin M} {i : Fin 3}
    (hcl : ∀ c ∈ Γ.comps, (c.kind.isSolid = false ∧ c.kind ≠ .dot ∧ (c.kind = .xdot → c.x = c.y))
      ∨ c ∈ TEqCorrShape_tail A i)
    (hT : ∀ c ∈ TEqCorrShape_tail A i, c ∈ Γ.comps) :
    (∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true) ∧
    (∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) ∧
    ∀ u v : Atom 3 M, u ≠ v →
      ((∃ c ∈ Γ.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u))) := by
  refine ⟨fun c hc hk => ?_, fun c hc hs => ?_, fun u v huv => ⟨?_, ?_⟩⟩
  · rcases hcl c hc with ⟨-, hd, -⟩ | ht
    · exact absurd hk hd
    · fin_cases i <;> simp only [TEqCorrShape_tail, List.mem_cons, List.not_mem_nil,
        or_false] at ht <;> rcases ht with rfl | rfl | rfl | rfl <;> simp_all [mkC]
  · rcases hcl c hc with ⟨hs', -, -⟩ | ht
    · rw [hs'] at hs; cases hs
    · fin_cases i <;> simp only [TEqCorrShape_tail, List.mem_cons, List.not_mem_nil,
        or_false] at ht <;> rcases ht with rfl | rfl | rfl | rfl <;> simp_all [mkC, Kind.isSolid]
  · rintro ⟨c, hc, hk, hends⟩
    rcases hcl c hc with ⟨-, -, hl⟩ | ht
    · have := hl hk
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd this huv
      · exact absurd this.symm huv
    · fin_cases i <;> simp only [TEqCorrShape_tail, List.mem_cons, List.not_mem_nil,
        or_false] at ht <;> rcases ht with rfl | rfl | rfl | rfl <;> simp only [mkC] at hk <;>
        try cases hk
      · exact ⟨mkC (.G .minus) (.inr A) (.inl 2), hT _ (by simp [TEqCorrShape_tail]), rfl, hends⟩
      · exact ⟨mkC (.G .plus) (.inr A) (.inl 1), hT _ (by simp [TEqCorrShape_tail]), rfl, hends⟩
  · rintro ⟨c, hc, hs, hends⟩
    rcases hcl c hc with ⟨hs', -, -⟩ | ht
    · rw [hs'] at hs; cases hs
    · fin_cases i <;> simp only [TEqCorrShape_tail, List.mem_cons, List.not_mem_nil,
        or_false] at ht <;> rcases ht with rfl | rfl | rfl | rfl <;>
        simp only [mkC, Kind.isSolid] at hs <;> try cases hs
      · exact ⟨mkC .xdot (.inr A) (.inl 2), hT _ (by simp [TEqCorrShape_tail]), rfl, hends⟩
      · exact ⟨mkC .xdot (.inr A) (.inl 1), hT _ (by simp [TEqCorrShape_tail]), rfl, hends⟩

/-- The image of a component has the kinds of [II, Def 3.2 (2)] iff the component has them. -/
private theorem TEqCorrShape_isTKind_map {V W : Type*} (f : V → W) (c : Comp V) (K : ℕ) :
    (c.map f).isTKind K = c.isTKind K := by
  obtain ⟨k, x, y, mi, lab⟩ := c
  simp [Comp.isTKind, Comp.map]

/-- The waved and diffusive edges are edges. -/
private theorem TEqCorrShape_wt_le {k n : ℕ} (Γ : Graph k n) : Γ.wavedThetaGraph ≤ Γ.edgeGraph := by
  intro u v h
  simp only [Graph.wavedThetaGraph, Graph.edgeGraph, SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨hne, h⟩ := h
  refine ⟨hne, ?_⟩
  rcases h with ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩
  · exact Or.inl ⟨c, hc, h1, h2⟩
  · exact Or.inr ⟨c, hc, h1, h2⟩

/-! ## The root map of [II, Def 3.3 (4)] -/

/-- The atom map of `Graph.rootAt i`: the internal atom `i` becomes `⊗`. -/
private def TEqCorrShape_rho {M : ℕ} (i : Fin M) : Atom 3 M → Atom 3 (M - 1)
  | .inl j => .inl j
  | .inr j => if h : j = i then .inl 0 else .inr (finDrop i j h)

/-- The components of `Graph.rootAt i` are the images under `TEqCorrShape_rho i`. -/
private theorem TEqCorrShape_rootAt_comps {M : ℕ} (Γ : Graph 3 M) (i : Fin M) :
    (Γ.rootAt i).comps = Γ.comps.map (Comp.map (TEqCorrShape_rho i)) := by
  simp only [Graph.rootAt, Graph.mapAtoms]
  congr 2

/-- Every internal atom of `Graph.rootAt i` is the image of an internal atom other than `i`. -/
private theorem TEqCorrShape_rho_surj {M : ℕ} (i : Fin M) (k : Fin (M - 1)) :
    ∃ j, j ≠ i ∧ TEqCorrShape_rho i (.inr j) = .inr k := by
  have hk := k.2
  by_cases hlt : k.val < i.val
  · have hne : (⟨k.val, by omega⟩ : Fin M) ≠ i := fun h => by
      rw [Fin.ext_iff] at h; simp at h; omega
    refine ⟨⟨k.val, by omega⟩, hne, ?_⟩
    simp only [TEqCorrShape_rho, hne, ↓reduceDIte, finDrop, hlt]
  · have hne : (⟨k.val + 1, by omega⟩ : Fin M) ≠ i := fun h => by
      rw [Fin.ext_iff] at h; simp at h; omega
    refine ⟨⟨k.val + 1, by omega⟩, hne, ?_⟩
    have hlt' : ¬ k.val + 1 < i.val := by omega
    simp only [TEqCorrShape_rho, hne, ↓reduceDIte, finDrop, hlt', Nat.add_sub_cancel]

/-- **The rooted graph is normal regular** ([II, Def 3.3 (4)]): for a graph `Θ_{⊗x} 𝒢` that is
connected, with any two internal atoms joined by waved and diffusive edges, whose components
other than `Θ_{⊗x}` are not solid, not dotted and loops if `×`-dotted, or are the components of a
recollision term at an internal atom `α ≠ x`, the graph `𝒢` with `x` read as `⊗` is normal
regular. -/
private theorem TEqCorrShape_root {M : ℕ} {X0 A : Fin M} {i : Fin 3}
    {rest : List (Comp (Atom 3 M))} {co : Coeff} (hAX : A ≠ X0)
    (hconn : (⟨mkC (.theta []) (.inl 0) (.inr X0) :: rest, co⟩ : Graph 3 M).edgeGraph.Preconnected)
    (hint : ∀ a b : Fin M, (⟨mkC (.theta []) (.inl 0) (.inr X0) :: rest, co⟩ :
      Graph 3 M).wavedThetaGraph.Reachable (.inr a) (.inr b))
    (hcl : ∀ c ∈ rest, (c.kind.isSolid = false ∧ c.kind ≠ .dot ∧ (c.kind = .xdot → c.x = c.y)) ∨
      c ∈ TEqCorrShape_tail A i)
    (hT : ∀ c ∈ TEqCorrShape_tail A i, c ∈ rest) :
    ∃ C, ((⟨rest, co⟩ : Graph 3 M).rootAt X0).Normal C := by
  set ρ := TEqCorrShape_rho X0 with hρ
  set Γr := (⟨rest, co⟩ : Graph 3 M).rootAt X0 with hΓr
  have hcomps : Γr.comps = rest.map (Comp.map ρ) := TEqCorrShape_rootAt_comps _ _
  have hsurj : ∀ u : Atom 3 (M - 1), ∃ v, ρ v = u := by
    rintro (j | k)
    · exact ⟨.inl j, rfl⟩
    · obtain ⟨j, -, hj⟩ := TEqCorrShape_rho_surj X0 k
      exact ⟨_, hj⟩
  have hedge : ∀ (q : Kind → Prop) (u v : Atom 3 M),
      TEqCorrShape_rel (⟨mkC (.theta []) (.inl 0) (.inr X0) :: rest, co⟩ : Graph 3 M) q u v →
      (SimpleGraph.fromRel (TEqCorrShape_rel Γr q)).Reachable (ρ u) (ρ v) := by
    rintro q u v ⟨c, hc, hq, rfl, rfl⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · have : ρ (.inr X0) = .inl 0 := by simp [hρ, TEqCorrShape_rho]
      simp only [mkC]
      rw [this]
      exact SimpleGraph.Reachable.refl _
    · refine TEqCorrShape_reach_rel ⟨c.map ρ, ?_, hq, rfl, rfl⟩
      rw [hcomps]
      exact List.mem_map_of_mem hc
  have hA : ρ (.inr A) = .inr (finDrop X0 A hAX) := by simp [hρ, TEqCorrShape_rho, hAX]
  have htail := TEqCorrShape_tail_map ρ A (finDrop X0 A hAX) hA rfl rfl i
  have hcl' : ∀ c ∈ Γr.comps, (c.kind.isSolid = false ∧ c.kind ≠ .dot ∧
      (c.kind = .xdot → c.x = c.y)) ∨ c ∈ TEqCorrShape_tail (finDrop X0 A hAX) i := by
    intro c hc
    rw [hcomps] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    rcases hcl c₀ hc₀ with ⟨h1, h2, h3⟩ | ht
    · exact Or.inl ⟨h1, h2, fun hk => by simp only [Comp.map]; rw [h3 hk]⟩
    · exact Or.inr (htail ▸ List.mem_map_of_mem ht)
  have hT' : ∀ c ∈ TEqCorrShape_tail (finDrop X0 A hAX) i, c ∈ Γr.comps := by
    intro c hc
    rw [← htail] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    rw [hcomps]
    exact List.mem_map_of_mem (hT c₀ hc₀)
  obtain ⟨h1, h2, h3⟩ := TEqCorrShape_local hcl' hT'
  refine ⟨3 + (M - 1) + Γr.comps.length, ⟨le_refl _, ?_, ?_, h1⟩, h2, h3⟩
  · intro u' v'
    obtain ⟨u, rfl⟩ := hsurj u'
    obtain ⟨v, rfl⟩ := hsurj v'
    have h := hconn u v
    rw [TEqCorrShape_edge_eq] at h ⊢
    exact TEqCorrShape_reach_map ρ (hedge _) h
  · intro a b
    obtain ⟨a', -, ha⟩ := TEqCorrShape_rho_surj X0 a
    obtain ⟨b', -, hb⟩ := TEqCorrShape_rho_surj X0 b
    rw [← hρ] at ha hb
    have h := hint a' b'
    rw [TEqCorrShape_wt_eq] at h ⊢
    have := TEqCorrShape_reach_map ρ (hedge _) h
    rwa [ha, hb] at this

/-! ## One form of the correction graphs -/

/-- The atom map of the graph `𝒮` of the leaf form `TEqSigma.LeafOf` into the output graph:
`0 ↦ x`, `1 ↦ y`, the internal atom `j ↦ e j`. -/
private def TEqCorrShape_phi {N m : ℕ} (x y α : Fin N)
    (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) : Atom 2 m → Atom 3 N :=
  Sum.elim ![.inr x, .inr y] fun j => .inr (e j).1

/-- The components of the output graph in the leaf form `TEqSigma.LeafOf`. -/
private def TEqCorrShape_gList {N m : ℕ} (x y α : Fin N)
    (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) (R : List (Comp (Atom 2 m)))
    (sy : Comp (Atom 3 N)) (X : List (Comp (Atom 3 N))) (ℓ : ℕ) : List (Comp (Atom 3 N)) :=
  mkC (.theta []) (.inl 0) (.inr x) :: R.map (Comp.map (TEqCorrShape_phi x y α e)) ++
    [sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++ X ++
    List.replicate ℓ (mkC .xdot (.inr α) (.inr α))

section Core

variable {N m M : ℕ} {Γ : Graph 3 N} {x y α : Fin N}
  {e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}} {R : List (Comp (Atom 2 m))}
  {sy : Comp (Atom 3 N)} {X : List (Comp (Atom 3 N))} {ℓ : ℕ}

/-- **The shape of a graph of the form of a correction graph** ([II, Def 3.2 (1), (2), (9), (10)],
[II, Def 3.3 (4)]): let `Γ` be a normal regular, doubly connected graph with a deterministic
maximal subgraph, the kinds of [II, Def 3.2 (2)] with labels of entries in `[4, K]`, no minor, no
label and no dotted edge, in the leaf form `Θ_{⊗x} R_{xy} s_{yα} G_{α⊕} Ḡ_{α⊖} X (×_{αα})^ℓ`.
Let `ψ` map the internal atoms of `Γ` onto those of a graph `Γc` with `ψ α ≠ ψ x`, and let the
components of `Γc` be `Θ_{⊗ψx}` followed, up to order, by the image of `R` under `ψ`, `ℓ`
`×`-dotted loops at `ψ x`, `s_{ψy ψα}` and the components other than `s_{⊗α}` of a recollision
term of [II, (4.15)] at `ψ α`. Then `Γc` is normal regular, has the kinds of [II, Def 3.2 (2)]
with labels of entries in `[4, K]`, the clause on the external atoms, is doubly connected, and
has the form of [II, Def 3.3 (4)]. -/
private theorem TEqCorrShape_core {C K : ℕ} (hN : Γ.Normal C) (hDC : Γ.DoublyConnected)
    (hMD : Γ.MaxDeterministic) (hTK : Γ.TKinds K) (hP : Γ.Plain) (hLF : Γ.LabelFree)
    (hdot : ∀ c ∈ Γ.comps, c.kind ≠ .dot) (hαx : α ≠ x) (hαy : α ≠ y)
    (hsy : sy = mkC (.waved .s) (.inr y) (.inr α) ∨ sy = mkC (.waved .s) (.inr α) (.inr y))
    (hX : ∀ c ∈ X, c = mkC .xdot (.inr α) (.inl 1) ∨ c = mkC .xdot (.inl 1) (.inr α) ∨
      c = mkC .xdot (.inr α) (.inl 2) ∨ c = mkC .xdot (.inl 2) (.inr α))
    (hg : Γ.comps.Perm (TEqCorrShape_gList x y α e R sy X ℓ))
    {Γc : Graph 3 M} (ψ : Fin N → Fin M) (hψ : Function.Surjective ψ) (hAX : ψ α ≠ ψ x)
    (i : Fin 3) {rest : List (Comp (Atom 3 M))}
    (hc : Γc.comps = mkC (.theta []) (.inl 0) (.inr (ψ x)) :: rest)
    (hrest : rest.Perm ((R.map (Comp.map (TEqCorrShape_phi x y α e))).map
        (Comp.map (Sum.map id ψ)) ++ List.replicate ℓ (mkC .xdot (.inr (ψ x)) (.inr (ψ x))) ++
      mkC (.waved .s) (.inr (ψ y)) (.inr (ψ α)) :: TEqCorrShape_tail (ψ α) i)) :
    (∃ C, Γc.Normal C) ∧ Γc.TKinds K ∧ Γc.AtExternals ∧ Γc.DoublyConnected ∧
      Γc.ThetaRooted := by
  classical
  obtain ⟨cs, co⟩ := Γc
  simp only at hc
  subst hc
  set Γc : Graph 3 M := ⟨mkC (.theta []) (.inl 0) (.inr (ψ x)) :: rest, co⟩ with hΓc
  set φ := TEqCorrShape_phi x y α e with hφ
  set ψA : Atom 3 N → Atom 3 M := Sum.map id ψ with hψA
  -- the atoms of `𝒮` go to internal atoms other than `α`
  have hφr : ∀ u, ∃ a, φ u = .inr a ∧ a ≠ α := by
    intro u
    cases u with
    | inl j =>
      fin_cases j
      · exact ⟨x, rfl, hαx.symm⟩
      · exact ⟨y, rfl, hαy.symm⟩
    | inr j => exact ⟨(e j).1, rfl, (e j).2.2.2⟩
  -- the components of `Γ`
  have hRmem : ∀ c₀ ∈ R, c₀.map φ ∈ Γ.comps := fun c₀ h => hg.mem_iff.2 (by
    simp only [TEqCorrShape_gList, List.cons_append, List.append_assoc, List.mem_cons,
      List.mem_append, List.mem_map]
    exact Or.inr (Or.inl ⟨c₀, h, rfl⟩))
  have hgcls : ∀ c ∈ Γ.comps, c = mkC (.theta []) (.inl 0) (.inr x) ∨
      (∃ c₀ ∈ R, c = c₀.map φ) ∨ c = sy ∨ c.kind = .G .plus ∨ c.kind = .G .minus ∨
      c.kind = .xdot := by
    intro c hc
    have h := hg.mem_iff.1 hc
    simp only [TEqCorrShape_gList, List.cons_append, List.append_assoc, List.mem_cons,
      List.mem_append, List.mem_map, List.mem_replicate, List.not_mem_nil, false_or] at h
    rcases h with rfl | ⟨c₀, hc₀, rfl⟩ | rfl | rfl | rfl | hcX | ⟨-, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨c₀, hc₀, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rcases hX c hcX with rfl | rfl | rfl | rfl <;> rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  -- the components of `R` are not random
  have hRnr : ∀ c₀ ∈ R, c₀.kind.isRandom = false := by
    intro c₀ h
    cases hr : c₀.kind.isRandom
    · rfl
    · obtain ⟨a, ha, -⟩ := hφr c₀.x
      obtain ⟨b, hb, -⟩ := hφr c₀.y
      rcases hMD _ (hRmem c₀ h) hr with h' | h'
      · simp [Comp.map, ha] at h'
      · simp [Comp.map, hb] at h'
  have hRsol : ∀ c₀ ∈ R, c₀.kind.isSolid = false := fun c₀ h => by
    have := hRnr c₀ h
    revert this
    cases c₀.kind <;> simp [Kind.isSolid, Kind.isRandom]
  have hRdot : ∀ c₀ ∈ R, c₀.kind ≠ .dot := fun c₀ h => hdot _ (hRmem c₀ h)
  -- the `×`-dotted edges of `R` are loops in `Γ`
  have hRx : ∀ c₀ ∈ R, c₀.kind = .xdot → φ c₀.x = φ c₀.y := by
    intro c₀ h hk
    by_contra hne
    obtain ⟨c', hc', hs, hends⟩ := (hN.2.2 (φ c₀.x) (φ c₀.y) hne).1
      ⟨c₀.map φ, hRmem c₀ h, hk, Or.inl ⟨rfl, rfl⟩⟩
    have hr : c'.kind.isRandom = true := by
      revert hs; cases c'.kind <;> simp [Kind.isSolid, Kind.isRandom]
    obtain ⟨a, ha, -⟩ := hφr c₀.x
    obtain ⟨b, hb, -⟩ := hφr c₀.y
    rcases hMD c' hc' hr with h' | h' <;> rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, ha] at h'; cases h'
    · rw [e1, hb] at h'; cases h'
    · rw [e2, hb] at h'; cases h'
    · rw [e2, ha] at h'; cases h'
  -- the components of `Γc`
  have hcR : ∀ c₀ ∈ R, (c₀.map φ).map ψA ∈ rest := fun c₀ h => hrest.mem_iff.2
    (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
      (List.mem_map_of_mem (List.mem_map_of_mem h))))))
  have hcS : mkC (.waved .s) (.inr (ψ y)) (.inr (ψ α)) ∈ rest := hrest.mem_iff.2
    (List.mem_append.2 (Or.inr List.mem_cons_self))
  have hcT : ∀ c ∈ TEqCorrShape_tail (ψ α) i, c ∈ rest := fun c h => hrest.mem_iff.2
    (List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ h)))
  have hrcls : ∀ c ∈ rest, (∃ c₀ ∈ R, c = (c₀.map φ).map ψA) ∨
      c = mkC .xdot (.inr (ψ x)) (.inr (ψ x)) ∨ c = mkC (.waved .s) (.inr (ψ y)) (.inr (ψ α)) ∨
      c ∈ TEqCorrShape_tail (ψ α) i := by
    intro c hc
    have h := hrest.mem_iff.1 hc
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 h
        obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc₁
        exact Or.inl ⟨c₀, hc₀, rfl⟩
      · exact Or.inr (Or.inl (List.mem_replicate.1 h).2)
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  -- the image of a component of `R`
  have hRimg : ∀ c₀ ∈ R, ((c₀.map φ).map ψA).minor = [] ∧ ((c₀.map φ).map ψA).label = none ∧
      (∃ a, ((c₀.map φ).map ψA).x = .inr (ψ a) ∧ φ c₀.x = .inr a) ∧
      (∃ b, ((c₀.map φ).map ψA).y = .inr (ψ b) ∧ φ c₀.y = .inr b) := by
    intro c₀ h
    obtain ⟨a, ha, -⟩ := hφr c₀.x
    obtain ⟨b, hb, -⟩ := hφr c₀.y
    refine ⟨?_, ?_, ⟨a, ?_, ha⟩, ⟨b, ?_, hb⟩⟩
    · change (c₀.map φ).minor.map ψA = []
      rw [(hP _ (hRmem c₀ h)).1]; rfl
    · change (c₀.map φ).label.map _ = none
      rw [hLF _ (hRmem c₀ h)]; rfl
    · change ψA (φ c₀.x) = _
      rw [ha]; rfl
    · change ψA (φ c₀.y) = _
      rw [hb]; rfl
  -- `TKinds`
  have hTKc : Γc.TKinds K := by
    unfold Graph.TKinds
    rw [List.all_eq_true]
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · simp [Comp.isTKind, mkC, labelOK]
    rcases hrcls c hc with ⟨c₀, hc₀, rfl⟩ | rfl | rfl | ht
    · rw [TEqCorrShape_isTKind_map]
      exact List.all_eq_true.1 hTK _ (hRmem c₀ hc₀)
    · simp [Comp.isTKind, mkC]
    · simp [Comp.isTKind, mkC]
    · exact (TEqCorrShape_tail_mem _ i K c ht).2.2.2.2.2.2
  -- `AtExternals`
  have hAE : Γc.AtExternals := by
    refine ⟨?_, ?_, ?_⟩
    · have h0 : rest.filter (fun c => c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0)) =
          [] := by
        refine List.filter_eq_nil_iff.2 fun c hc => ?_
        rcases hrcls c hc with ⟨c₀, hc₀, rfl⟩ | rfl | rfl | ht
        · obtain ⟨-, -, ⟨a, ha, -⟩, ⟨b, hb, -⟩⟩ := hRimg c₀ hc₀
          simp [ha, hb]
        · simp [mkC]
        · simp [mkC]
        · obtain ⟨-, -, -, -, hd, -⟩ := TEqCorrShape_tail_mem _ i 0 c ht
          simp [hd]
      change ((mkC (.theta []) (.inl 0) (.inr (ψ x)) :: rest).filter
        fun c => c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0)).length = 1
      rw [List.filter_cons_of_pos (by simp [mkC, Kind.isDiffusive]), h0]
      rfl
    · obtain ⟨⟨c, hc, hk, -, hy⟩, -⟩ := TEqCorrShape_tail_ext (ψ α) i
      rw [List.any_eq_true]
      refine ⟨c, List.mem_cons_of_mem _ (hcT c hc), ?_⟩
      rcases hk with hk | hk <;> simp [hk, hy]
    · obtain ⟨-, ⟨c, hc, hk, -, hy⟩⟩ := TEqCorrShape_tail_ext (ψ α) i
      rw [List.any_eq_true]
      refine ⟨c, List.mem_cons_of_mem _ (hcT c hc), ?_⟩
      rcases hk with hk | hk <;> simp [hk, hy]
  -- edges of `Γ` carried to `Γc`
  set ψ' : Atom 3 N → Atom 3 M :=
    Sum.elim (fun j => if j = 0 then .inr (ψ x) else .inr (ψ α)) (fun a => .inr (ψ a)) with hψ'
  have hpush : ∀ q : Kind → Prop, ¬ q (.G .plus) → ¬ q (.G .minus) → ¬ q .xdot →
      q (.waved .s) → ∀ u v, TEqCorrShape_rel Γ q u v →
      (SimpleGraph.fromRel (TEqCorrShape_rel Γc q)).Reachable (ψ' u) (ψ' v) := by
    rintro q h1 h2 h3 hs u v ⟨c, hc, hq, rfl, rfl⟩
    rcases hgcls c hc with rfl | ⟨c₀, hc₀, rfl⟩ | rfl | hk | hk | hk
    · exact SimpleGraph.Reachable.refl _
    · obtain ⟨-, -, ⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hRimg c₀ hc₀
      refine TEqCorrShape_reach_rel ⟨(c₀.map φ).map ψA, List.mem_cons_of_mem _ (hcR c₀ hc₀),
        hq, ?_, ?_⟩
      · rw [ha]; change _ = ψ' (φ c₀.x); rw [ha']; rfl
      · rw [hb]; change _ = ψ' (φ c₀.y); rw [hb']; rfl
    · rcases hsy with rfl | rfl
      · exact TEqCorrShape_reach_rel ⟨_, List.mem_cons_of_mem _ hcS, hs, rfl, rfl⟩
      · exact (TEqCorrShape_reach_rel ⟨_, List.mem_cons_of_mem _ hcS, hs, rfl, rfl⟩).symm
    · rw [hk] at hq; exact absurd hq h1
    · rw [hk] at hq; exact absurd hq h2
    · rw [hk] at hq; exact absurd hq h3
  -- `Normal`
  have hint : ∀ a b : Fin M, Γc.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
    intro a' b'
    obtain ⟨a, rfl⟩ := hψ a'
    obtain ⟨b, rfl⟩ := hψ b'
    have h := hN.1.internal a b
    rw [TEqCorrShape_wt_eq] at h ⊢
    exact TEqCorrShape_reach_map ψ' (hpush _ (by simp [Kind.joinsMol, Kind.isDiffusive])
      (by simp [Kind.joinsMol, Kind.isDiffusive]) (by simp [Kind.joinsMol, Kind.isDiffusive])
      (by simp [Kind.joinsMol])) h
  have hconn : Γc.edgeGraph.Preconnected := by
    have hwt : ∀ a, Γc.edgeGraph.Reachable (.inr a) (.inr (ψ x)) := fun a =>
      (hint a (ψ x)).mono (TEqCorrShape_wt_le Γc)
    have hto : ∀ u, Γc.edgeGraph.Reachable u (.inr (ψ x)) := by
      intro u
      rw [TEqCorrShape_edge_eq] at hwt ⊢
      rcases u with j | a
      · fin_cases j
        · exact TEqCorrShape_reach_rel ⟨_, List.mem_cons_self, trivial, rfl, rfl⟩
        · obtain ⟨⟨c, hc, -, hx, hy⟩, -⟩ := TEqCorrShape_tail_ext (ψ α) i
          refine (TEqCorrShape_reach_rel ⟨c, List.mem_cons_of_mem _ (hcT c hc), trivial, hx,
            hy⟩).symm.trans (hwt _)
        · obtain ⟨-, ⟨c, hc, -, hx, hy⟩⟩ := TEqCorrShape_tail_ext (ψ α) i
          refine (TEqCorrShape_reach_rel ⟨c, List.mem_cons_of_mem _ (hcT c hc), trivial, hx,
            hy⟩).symm.trans (hwt _)
      · exact hwt a
    exact fun u v => (hto u).trans (hto v).symm
  have hclr : ∀ c ∈ rest, (c.kind.isSolid = false ∧ c.kind ≠ .dot ∧
      (c.kind = .xdot → c.x = c.y)) ∨ c ∈ TEqCorrShape_tail (ψ α) i := by
    intro c hc
    rcases hrcls c hc with ⟨c₀, hc₀, rfl⟩ | rfl | rfl | ht
    · refine Or.inl ⟨hRsol c₀ hc₀, hRdot c₀ hc₀, fun hk => ?_⟩
      change ψA (φ c₀.x) = ψA (φ c₀.y)
      rw [hRx c₀ hc₀ hk]
    · exact Or.inl ⟨rfl, by simp [mkC], fun _ => rfl⟩
    · exact Or.inl ⟨rfl, by simp [mkC], fun h => by cases h⟩
    · exact Or.inr ht
  have hNc : Γc.Normal (3 + M + Γc.comps.length) := by
    have hcl : ∀ c ∈ Γc.comps, (c.kind.isSolid = false ∧ c.kind ≠ .dot ∧
        (c.kind = .xdot → c.x = c.y)) ∨ c ∈ TEqCorrShape_tail (ψ α) i := by
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact Or.inl ⟨rfl, by simp [mkC], fun h => by cases h⟩
      · exact hclr c hc
    obtain ⟨h1, h2, h3⟩ := TEqCorrShape_local hcl
      (fun c hc => List.mem_cons_of_mem _ (hcT c hc))
    exact ⟨⟨le_refl _, hconn, hint, h1⟩, h2, h3⟩
  -- `DoublyConnected`
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc hDC
  set p : Comp (Atom 3 N) → Bool :=
    fun c => c.x.isRight && c.y.isRight && (c.kind.isDiffusive || c.kind.isBlue) with hp
  have hfilt : (Γ.comps.filter p).Subperm (R.map (Comp.map φ)) := by
    refine ((hg.filter p).subperm).trans ?_
    refine List.Sublist.subperm ?_
    have hX0 : X.filter p = [] := List.filter_eq_nil_iff.2 fun c hc => by
      rcases hX c hc with rfl | rfl | rfl | rfl <;> simp [hp, mkC]
    have hl0 : (List.replicate ℓ (mkC .xdot (.inr α) (.inr α) : Comp (Atom 3 N))).filter p = [] :=
      List.filter_eq_nil_iff.2 fun c hc => by
        rw [(List.mem_replicate.1 hc).2]; simp [hp, mkC, Kind.isDiffusive, Kind.isBlue]
    have hsy0 : p sy = false := by
      rcases hsy with rfl | rfl <;> simp [hp, mkC, Kind.isDiffusive, Kind.isBlue]
    have hΘ0 : p (mkC (.theta []) (.inl 0) (.inr x)) = false := by simp [hp, mkC]
    have hG1 : p (mkC (.G .plus) (.inr α) (.inl 1)) = false := by simp [hp, mkC]
    have hG2 : p (mkC (.G .minus) (.inr α) (.inl 2)) = false := by simp [hp, mkC]
    simp only [TEqCorrShape_gList, List.cons_append, List.append_assoc, List.filter_cons,
      List.filter_append, hX0, hl0, hsy0, hΘ0, hG1, hG2, Bool.false_eq_true, ↓reduceIte,
      List.append_nil, List.nil_append]
    exact List.filter_sublist
  have hmolp : ∀ a b : Atom 3 N, Γ.molGraph.Reachable a b →
      Γc.molGraph.Reachable (ψ' a) (ψ' b) := by
    intro a b h
    rw [TEqCorrShape_mol_eq] at h ⊢
    exact TEqCorrShape_reach_map ψ' (hpush _ (by simp [Kind.joinsMol])
      (by simp [Kind.joinsMol]) (by simp [Kind.joinsMol]) (by simp [Kind.joinsMol])) h
  have hnet : ∀ B : List (Comp (Atom 3 N)),
      (∀ c ∈ B, c ∈ Γ.comps ∧ (c.kind.isDiffusive = true ∨ c.kind.isBlue = true)) →
      (SimpleGraph.fromRel (nrel Γ B)).Preconnected →
      (SimpleGraph.fromRel (nrel Γc ((B.filter p).map (Comp.map ψA)))).Preconnected := by
    intro B hB hpre a' b'
    obtain ⟨a, rfl⟩ := hψ a'
    obtain ⟨b, rfl⟩ := hψ b'
    refine TEqCorrShape_reach_map ψ (fun a b h => ?_) (hpre a b)
    rcases h with hm | ⟨c, hc, hx, hy⟩
    · rcases hm with he | ⟨-, -, hm⟩
      · cases he; exact SimpleGraph.Reachable.refl _
      · exact TEqCorrShape_reach_rel (Or.inl (Or.inr ⟨rfl, rfl, hmolp _ _ hm⟩))
    · refine TEqCorrShape_reach_rel (Or.inr ⟨c.map ψA, List.mem_map.2 ⟨c, List.mem_filter.2
        ⟨hc, ?_⟩, rfl⟩, ?_, ?_⟩)
      · have hk := (hB c hc).2
        simp only [hp, hx, hy, Sum.isRight_inr, Bool.true_and]
        rcases hk with hk | hk <;> simp [hk]
      · simp [Comp.map, hx, hψA]
      · simp [Comp.map, hy, hψA]
  have hDCc : Γc.DoublyConnected := by
    refine Graph.dc_of_dcl ⟨(Lb.filter p).map (Comp.map ψA), (Lu.filter p).map (Comp.map ψA),
      ?_, ?_, ?_, hnet Lb ?_ hsb, hnet Lu ?_ hsu⟩
    · rw [← List.map_append, ← List.filter_append]
      refine (TEqCorrShape_subperm_map (Comp.map ψA) ((hsub.filter p).trans hfilt)).trans ?_
      refine List.Subperm.trans ?_ (List.sublist_cons_self _ _).subperm
      refine List.Subperm.trans ?_ hrest.symm.subperm
      rw [List.map_map]
      exact ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)).subperm
    · intro c hc
      obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
      exact hb c₁ (List.mem_filter.1 hc₁).1
    · intro c hc
      obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
      exact hu c₁ (List.mem_filter.1 hc₁).1
    · exact fun c hc => ⟨hsub.subset (List.mem_append_left _ hc), Or.inl (hb c hc)⟩
    · exact fun c hc => ⟨hsub.subset (List.mem_append_right _ hc), hu c hc⟩
  -- `ThetaRooted`
  have hTR : Γc.ThetaRooted := by
    refine ⟨⟨0, by simp [hΓc]⟩, .inr (ψ x), by simp, rfl, rfl, rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro c hc
      change c ∈ rest at hc
      rcases hrcls c hc with ⟨c₀, hc₀, rfl⟩ | rfl | rfl | ht
      · obtain ⟨hm, hl, ⟨a, ha, -⟩, ⟨b, hb, -⟩⟩ := hRimg c₀ hc₀
        simp [ha, hb, hm, hl]
      · simp [mkC]
      · simp [mkC]
      · obtain ⟨hm, hl, hx, hy, -⟩ := TEqCorrShape_tail_mem _ i 0 c ht
        refine ⟨by simp [hx], ?_, by simp [hm], by simp [hl]⟩
        rcases hy with hy | hy | hy <;> simp [hy]
    · exact TEqCorrShape_root hAX hconn hint hclr hcT
  exact ⟨⟨_, hNc⟩, hTKc, hAE, hDCc, hTR⟩

end Core

/-! ## The recollision terms as computed -/

/-- Equality of components is decidable. -/
@[reducible] private def TEqCorrShape_decEqComp {V : Type*} [DecidableEq V] :
    DecidableEq (Comp V) :=
  fun a b => decidable_of_iff
    (a.kind = b.kind ∧ a.x = b.x ∧ a.y = b.y ∧ a.minor = b.minor ∧ a.label = b.label) (by
      obtain ⟨_, _, _, _, _⟩ := a
      obtain ⟨_, _, _, _, _⟩ := b
      simp)

section TVar

attribute [local instance] TEqCorrShape_decEqComp

set_option maxHeartbeats 4000000 in
-- kernel evaluation of the recollision terms
/-- The atoms and components of the three recollision terms of [II, (4.15)] (`tVarCorr`):
`s_{⊗α}` followed by `TEqCorrShape_tail α`. -/
private theorem TEqCorrShape_tVarCorr_eq :
    tVarCorr.map (fun t => (⟨t.1, t.2.comps⟩ : Σ n, List (Comp (Atom 3 n)))) =
      [⟨1, mkC (.waved .s) (.inl 0) (.inr 0) :: TEqCorrShape_tail 0 0⟩,
        ⟨1, mkC (.waved .s) (.inl 0) (.inr 0) :: TEqCorrShape_tail 0 1⟩,
        ⟨1, mkC (.waved .s) (.inl 0) (.inr 0) :: TEqCorrShape_tail 0 2⟩] := by
  decide +kernel

end TVar

/-- Every recollision term of [II, (4.15)] has one internal atom `α` and the components `s_{⊗α}`
and `TEqCorrShape_tail α i` for one `i`. -/
private theorem TEqCorrShape_tVarCorr : ∀ t ∈ tVarCorr, ∃ (G : Graph 3 1) (i : Fin 3),
    t = ⟨1, G⟩ ∧ G.comps = mkC (.waved .s) (.inl 0) (.inr 0) :: TEqCorrShape_tail 0 i := by
  intro t ht
  have h := List.mem_map_of_mem
    (f := fun t : Σ n, Graph 3 n => (⟨t.1, t.2.comps⟩ : Σ n, List (Comp (Atom 3 n)))) ht
  rw [TEqCorrShape_tVarCorr_eq] at h
  obtain ⟨n₁, G⟩ := t
  simp only [List.mem_cons, List.not_mem_nil, or_false, Sigma.mk.injEq] at h
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨G, 0, rfl, eq_of_heq h⟩
  · exact ⟨G, 1, rfl, eq_of_heq h⟩
  · exact ⟨G, 2, rfl, eq_of_heq h⟩

/-! ## The correction graphs of a leaf form -/

/-- The atom map of the output graph into a correction graph at `x = y`: `x ↦ x`, the atom `e j`
to the atom `j` of `𝒮`, `α` to the new atom. -/
private def TEqCorrShape_psi₁ {N m : ℕ} (x α : Fin N)
    (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ x ∧ a ≠ α}) (a : Fin N) : Fin (1 + m + 1) :=
  if hα : a = α then Fin.last _ else
    Fin.castAdd 1 (if hx : a = x then 0 else Fin.natAdd 1 (e.symm ⟨a, hx, hx, hα⟩))

/-- The atom map of the output graph into a correction graph at `x ≠ y`: `x ↦ x`, `y ↦ y`, the
atom `e j` to the atom `j` of `𝒮`, `α` to the new atom. -/
private def TEqCorrShape_psi₂ {N m : ℕ} (x y α : Fin N)
    (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) (a : Fin N) : Fin (2 + m + 1) :=
  if hα : a = α then Fin.last _ else
    Fin.castAdd 1 (if hx : a = x then 0 else if hy : a = y then 1 else
      Fin.natAdd 2 (e.symm ⟨a, hx, hy, hα⟩))

/-- **The shape of the correction graphs of a leaf form** ([II, Def 3.2 (1), (2), (9), (10)],
[II, Def 3.3 (4)]): for a normal regular, doubly connected graph `g` with a deterministic maximal
subgraph, the kinds of [II, Def 3.2 (2)] with labels of entries in `[4, K]`, no minor, no label and
no dotted edge, and a leaf form `TEqSigma.LeafOf g 𝒮`, every graph `Θ_{⊗x} 𝒮_{xy} τ_{y,⊕⊖}` of
`TEqShape_corrOf 𝒮` is normal regular, has the kinds of [II, Def 3.2 (2)] with labels of entries
in `[4, K]`, the clause on the external atoms, is doubly connected and has the form of
[II, Def 3.3 (4)]. -/
private theorem TEqCorrShape_corr {g : Σ m, Graph 3 m} {m C K : ℕ} {S : Graph 2 m}
    (hN : g.2.Normal C) (hDC : g.2.DoublyConnected) (hMD : g.2.MaxDeterministic)
    (hTK : g.2.TKinds K) (hP : g.2.Plain) (hLF : g.2.LabelFree)
    (hdot : ∀ c ∈ g.2.comps, c.kind ≠ .dot) (hL : TEqSigma.LeafOf g S) :
    ∀ c ∈ TEqShape_corrOf ⟨m, S⟩, (∃ C, c.2.Normal C) ∧ c.2.TKinds K ∧ c.2.AtExternals ∧
      c.2.DoublyConnected ∧ c.2.ThetaRooted := by
  classical
  obtain ⟨N, Γ⟩ := g
  obtain ⟨x, y, α, e, R, sy, X, ℓ, hαx, hαy, hsy, hX, -, -, hgp, hSp, -⟩ := hL
  have hgp' : Γ.comps.Perm (TEqCorrShape_gList x y α e R sy X ℓ) := hgp
  have hRdot : ∀ c₀ ∈ R, c₀.kind ≠ .dot := fun c₀ h => hdot _ (hgp.mem_iff.2 (by
    simp only [List.cons_append, List.append_assoc, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inl ⟨c₀, h, rfl⟩)))
  intro c hc
  by_cases hxy : x = y
  · subst hxy
    have hδ : mkC .dot (.inl 0) (.inl 1) ∈ S.comps := hSp.mem_iff.2 (by simp)
    simp only [TEqShape_corrOf, hδ, ↓reduceIte, Graph.globalSubst] at hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    obtain ⟨G, i, rfl, hG⟩ := TEqCorrShape_tVarCorr t ht
    set ψ := TEqCorrShape_psi₁ x α e with hψdef
    have hψx : ψ x = Fin.castAdd 1 0 := by simp [hψdef, TEqCorrShape_psi₁, Ne.symm hαx]
    have hψα : ψ α = Fin.last _ := by simp [hψdef, TEqCorrShape_psi₁]
    have hψe : ∀ j, ψ (e j).1 = Fin.castAdd 1 (Fin.natAdd 1 j) := fun j => by
      simp [hψdef, TEqCorrShape_psi₁, (e j).2.1, (e j).2.2.2]
    have hsurj : Function.Surjective ψ := by
      intro k
      refine Fin.addCases (motive := fun k => ∃ a, ψ a = k) (fun k' => ?_) (fun j => ⟨α, ?_⟩) k
      · refine Fin.addCases (motive := fun k' => ∃ a, ψ a = Fin.castAdd 1 k') (fun j => ⟨x, ?_⟩)
          (fun j => ⟨(e j).1, hψe j⟩) k'
        rw [hψx, Subsingleton.elim j 0]; rfl
      · rw [hψα]; ext; simp [Subsingleton.elim j 0]
    set φ₁ : Atom 2 m → Atom 3 (1 + m) := Sum.elim (fun _ => .inr 0) fun j => .inr (Fin.natAdd 1 j)
      with hφ₁
    have hfun : ∀ c₀ : Comp (Atom 2 m), (c₀.map φ₁).map (liftA 1) =
        (c₀.map (TEqCorrShape_phi x x α e)).map (Sum.map id ψ) := by
      intro c₀
      rw [TEqCorrShape_map_map, TEqCorrShape_map_map]
      congr 1
      funext u
      cases u with
      | inl j => fin_cases j <;> simp [hφ₁, TEqCorrShape_phi, liftA, hψx]
      | inr j => simp [hφ₁, TEqCorrShape_phi, liftA, hψe]
    have hE : (S.comps.erase (mkC .dot (.inl 0) (.inl 1))).Perm
        (R ++ List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))) := by
      have := hSp.erase (mkC .dot (.inl 0) (.inl 1))
      simpa using this
    refine TEqCorrShape_core hN hDC hMD hTK hP hLF hdot hαx hαy hsy hX hgp' ψ hsurj
      (by rw [hψα, hψx]; exact (Fin.castSucc_lt_last _).ne') i
      (rest := liftCs 1 ((S.comps.erase (mkC .dot (.inl 0) (.inl 1))).map (Comp.map φ₁)) ++
        G.comps.map (Comp.map (glueAtom (.inr 0) (.inl 1) (.inl 2)))) ?_ ?_
    · simp only [Graph.glue, TEqShape_thetaS₁, liftCs, List.map_cons, List.cons_append, hψx]
      rfl
    · have hgα : glueAtom (.inr 0) (.inl 1) (.inl 2) (.inr 0 : Atom 3 1) =
          (.inr (ψ α) : Atom 3 (1 + m + 1)) := by
        rw [hψα]; simp only [glueAtom, newA]; congr 1
      have h1 : (liftCs 1 ((S.comps.erase (mkC .dot (.inl 0) (.inl 1))).map
          (Comp.map φ₁))).Perm ((R.map (Comp.map (TEqCorrShape_phi x x α e))).map
            (Comp.map (Sum.map id ψ)) ++
          List.replicate ℓ (mkC .xdot (.inr (ψ x)) (.inr (ψ x)))) := by
        have := hE.map (fun c₀ => (c₀.map φ₁).map (liftA 1))
        rw [List.map_append, List.map_replicate] at this
        refine (List.Perm.of_eq ?_).trans (this.trans (List.Perm.of_eq ?_))
        · simp only [liftCs, List.map_map]; rfl
        · rw [List.map_map, List.map_congr_left (fun c₀ _ => hfun c₀), ← List.map_map]
          simp [hφ₁, liftA, TEqCorrShape_map_mkC, hψx]
      have h2 : G.comps.map (Comp.map (glueAtom (.inr 0) (.inl 1) (.inl 2))) =
          mkC (.waved .s) (.inr (ψ x)) (.inr (ψ α)) :: TEqCorrShape_tail (ψ α) i := by
        rw [hG, List.map_cons, TEqCorrShape_map_mkC,
          TEqCorrShape_tail_map _ 0 (ψ α) hgα rfl rfl i, hgα, hψx]
        rfl
      rw [h2]
      exact h1.append_right _
  · have hδ : mkC .dot (.inl 0) (.inl 1) ∉ S.comps := by
      intro h
      have h' := hSp.mem_iff.1 h
      simp only [hxy, ↓reduceIte, List.nil_append, List.mem_append, List.mem_replicate] at h'
      rcases h' with h' | ⟨-, h'⟩
      · exact hRdot _ h' rfl
      · cases h'
    simp only [TEqShape_corrOf, hδ, ↓reduceIte, Graph.globalSubst] at hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    obtain ⟨G, i, rfl, hG⟩ := TEqCorrShape_tVarCorr t ht
    set ψ := TEqCorrShape_psi₂ x y α e with hψdef
    have hψx : ψ x = Fin.castAdd 1 0 := by simp [hψdef, TEqCorrShape_psi₂, Ne.symm hαx]
    have hψy : ψ y = Fin.castAdd 1 1 := by
      simp [hψdef, TEqCorrShape_psi₂, Ne.symm hαy, Ne.symm hxy]
    have hψα : ψ α = Fin.last _ := by simp [hψdef, TEqCorrShape_psi₂]
    have hψe : ∀ j, ψ (e j).1 = Fin.castAdd 1 (Fin.natAdd 2 j) := fun j => by
      simp [hψdef, TEqCorrShape_psi₂, (e j).2.1, (e j).2.2.1, (e j).2.2.2]
    have h0 : (0 : Fin (2 + m)) = Fin.castAdd m 0 := rfl
    have h1' : (1 : Fin (2 + m)) = Fin.castAdd m 1 := by
      ext; simp [Nat.mod_eq_of_lt (show 1 < 2 + m by omega)]
    have hsurj : Function.Surjective ψ := by
      intro k
      refine Fin.addCases (motive := fun k => ∃ a, ψ a = k) (fun k' => ?_) (fun j => ⟨α, ?_⟩) k
      · refine Fin.addCases (motive := fun k' => ∃ a, ψ a = Fin.castAdd 1 k') (fun j => ?_)
          (fun j => ⟨(e j).1, hψe j⟩) k'
        fin_cases j
        · exact ⟨x, by rw [hψx]; rfl⟩
        · exact ⟨y, by rw [hψy, h1']; rfl⟩
      · rw [hψα]; ext; simp [Subsingleton.elim j 0]
    set φ₂ : Atom 2 m → Atom 3 (2 + m) :=
      Sum.elim (fun i => .inr (Fin.castAdd m i)) fun j => .inr (Fin.natAdd 2 j) with hφ₂
    have hfun : ∀ c₀ : Comp (Atom 2 m), (c₀.map φ₂).map (liftA 1) =
        (c₀.map (TEqCorrShape_phi x y α e)).map (Sum.map id ψ) := by
      intro c₀
      rw [TEqCorrShape_map_map, TEqCorrShape_map_map]
      congr 1
      funext u
      cases u with
      | inl j => fin_cases j <;> simp [hφ₂, TEqCorrShape_phi, liftA, hψx, hψy, h1', ← h0]
      | inr j => simp [hφ₂, TEqCorrShape_phi, liftA, hψe]
    have hE : S.comps.Perm (R ++ List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))) := by
      simpa [hxy] using hSp
    refine TEqCorrShape_core hN hDC hMD hTK hP hLF hdot hαx hαy hsy hX hgp' ψ hsurj
      (by rw [hψα, hψx]; exact (Fin.castSucc_lt_last _).ne') i
      (rest := liftCs 1 (S.comps.map (Comp.map φ₂)) ++
        G.comps.map (Comp.map (glueAtom (.inr 1) (.inl 1) (.inl 2)))) ?_ ?_
    · simp only [Graph.glue, TEqShape_thetaS, liftCs, List.map_cons, List.cons_append, hψx]
      rfl
    · have hgα : glueAtom (.inr 1) (.inl 1) (.inl 2) (.inr 0 : Atom 3 1) =
          (.inr (ψ α) : Atom 3 (2 + m + 1)) := by
        rw [hψα]; simp only [glueAtom, newA]; congr 1
      have h1 : (liftCs 1 (S.comps.map (Comp.map φ₂))).Perm
          ((R.map (Comp.map (TEqCorrShape_phi x y α e))).map (Comp.map (Sum.map id ψ)) ++
          List.replicate ℓ (mkC .xdot (.inr (ψ x)) (.inr (ψ x)))) := by
        have := hE.map (fun c₀ => (c₀.map φ₂).map (liftA 1))
        rw [List.map_append, List.map_replicate] at this
        refine (List.Perm.of_eq ?_).trans (this.trans (List.Perm.of_eq ?_))
        · simp only [liftCs, List.map_map]; rfl
        · rw [List.map_map, List.map_congr_left (fun c₀ _ => hfun c₀), ← List.map_map]
          simp [hφ₂, liftA, TEqCorrShape_map_mkC, hψx, ← h0]
      have h2 : G.comps.map (Comp.map (glueAtom (.inr 1) (.inl 1) (.inl 2))) =
          mkC (.waved .s) (.inr (ψ y)) (.inr (ψ α)) :: TEqCorrShape_tail (ψ α) i := by
        rw [hG, List.map_cons, TEqCorrShape_map_mkC,
          TEqCorrShape_tail_map _ 0 (ψ α) hgα rfl rfl i, hgα, hψy]
        rfl
      rw [h2]
      exact h1.append_right _

/-! ## The correction graphs of the run -/

/-- **The correction graphs have the shape of [II, Def 3.3 (1), (4)]** ([II, Def 3.2 (1), (2),
(9), (10)], the `t → T` rewriting before [II, (6.7)], [II, (4.15)]): for `n ≥ 3` and a record `𝒯`
that is the structural part of an `(n - 1)`-th order `T`-expansion with error order `D`, every
correction graph `Θ_{⊗x} 𝒮_{xy} τ_{y,⊕⊖}` of `TEqSigma.corr g`, for an output graph `g` of the run
`RunCompare.run` with the family `TEqSigma.qFam` of the class `Graph.LeafDet`, not a
`⊕/⊖`-recollision graph and of scaling order `≤ n`, is normal regular, has the kinds of
[II, Def 3.2 (2)] with labels of entries in `[4, n - 1]`, the clause on the external atoms
[II, Def 3.2 (9)], is doubly connected [II, Def 3.2 (10)], and has the form
`∑_x Θ_{a x} 𝒢_{x, b₁ b₂}` of [II, Def 3.3 (4)]. -/
theorem TEqSigma.corr_shape : ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n →
    𝒯.IsTExpStruct Sig (n - 1) D → ∀ g ∈ RunCompare.run TEqSigma.qFam n D 𝒯, g.2.LeafDet →
    ¬ g.2.IsRecollision {1, 2} → g.2.ord ≤ n → ∀ c ∈ TEqSigma.corr g,
      (∃ C, c.2.Normal C) ∧ c.2.TKinds (n - 1) ∧ c.2.AtExternals ∧ c.2.DoublyConnected ∧
        c.2.ThetaRooted := by
  intro n D Sig 𝒯 hn hT g hg hdet hNR hord c hc
  obtain ⟨m, 𝒮, hσ, hL, -, -, -⟩ := TEqSigma.detLeaf_form n D Sig 𝒯 hn hT g hg hdet hNR hord
  have hdot := TEqSigma.detLeaf_dotFree n D Sig 𝒯 hn hT g hg hdet hNR hord
  have hspec := RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig 𝒯 hn hT
  obtain ⟨-, hDC, ⟨C, hN⟩, -, hPl, -⟩ := hspec.2.2 g hg
  have hnD : n ≤ D := by have := hT.1; omega
  have hP : g.2.Plain := hPl (by omega)
  have hK := (RunExports.selRun_exports _ TEqSigma.qFam_spec n D Sig 𝒯 hn hT _ hspec.1 g hg).2.1
  have hL' := (TEqSigma.normS_leafOf hL hdot).1
  have hcorr : TEqSigma.corr g = TEqShape_corrOf (TEqSigma.normS ⟨m, 𝒮⟩) := by
    unfold TEqSigma.corr
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hdet, hNR⟩), TEqSigma.sigma', hσ, List.map_singleton,
      List.flatMap_singleton]
  rw [hcorr] at hc
  exact TEqCorrShape_corr hN hDC hdet.2.2.1 (hK.tKinds hP) hP hdet.1 hdot hL' c hc

section Instances

end Instances

end RBM8D.Graphs
