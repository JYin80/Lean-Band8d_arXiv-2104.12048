module

public import RBM8D.GlobalExp.TEqLeaf
public import RBM8D.TExp.Second
import all RBM8D.TExp.Second

@[expose] public section

/-!
# `Σ_n` of the construction of [II, (6.8)]: the normal form at `x = y`, the correction graphs and
the shape of `Σ_n`

For an output graph `Θ_{⊗x} 𝒮_{xy} t_{y,⊕⊖}` of [II, Lemma 6.7] with `x = y`, the graph `𝒮` of the
leaf form `TEqSigma.LeafOf` carries the dotted edge `δ_{xy}` between its external atoms `x = 0` and
`y = 1` ([I, Def 2.13 (i)]), and every other end at the atom `x = y` may be read at `0` or at `1`.
This file gives:

* the normal form `TEqSigma.normS`: every end at `1` of a component other than `δ_{xy}` is read
  at `0`;
* an output graph of [II, Lemma 6.7] has no dotted edge (`TEqSigma.detLeaf_dotFree`), and on a
  graph without dotted edge the normal form keeps the leaf form (`TEqSigma.normS_leafOf`);
* the maps `TEqSigma.sigma'` (the normal form of the graph `𝒮`) and `TEqSigma.corr` (the graphs
  `Θ_{⊗x} 𝒮_{xy} (t - T)_{y,⊕⊖}` of the `t → T` rewriting before [II, (6.7)], with the three
  recollision terms of [II, (4.15)]), and the construction `TEqSigma.Strat`;
* `Σ_n` of `TEqSigma.Strat` has the shape of an `n`-th order self-energy
  (`TEqSigma.sigN_shape`, [II, Lemma 6.8], [II, Def 2.7 (i)], [II, Def 3.3 (2), (3), (5)]).
-/

noncomputable section

namespace RBM8D.Graphs

/-! ## The normal form at `x = y` -/

/-- The map of the atoms of a graph with external atoms `x = 0`, `y = 1` that sends both external
atoms to `x = 0` and fixes the internal atoms. -/
def TEqShape_toZero {m : ℕ} : Atom 2 m → Atom 2 m := Sum.elim (fun _ => .inl 0) .inr

open Classical in
/-- **The normal form of the graph `𝒮`** of an output graph `Θ_{⊗x} 𝒮_{xy} t_{y,⊕⊖}` of
[II, Lemma 6.7] at `x = y` ([I, Def 2.13 (i)]): if the dotted edge `δ_{xy}` between the external
atoms `x = 0` and `y = 1` is a component of `𝒮`, every end at `y = 1` of every component other
than `δ_{xy}` is moved to `x = 0`; otherwise `𝒮` is unchanged. The atoms and the coefficient are
those of `𝒮`. -/
def TEqSigma.normS (𝒮 : Σ m, Graph 2 m) : Σ m, Graph 2 m :=
  ⟨𝒮.1, if mkC .dot (.inl 0) (.inl 1) ∈ 𝒮.2.comps then
      ⟨𝒮.2.comps.map fun c => if c = mkC .dot (.inl 0) (.inl 1) then c else c.map TEqShape_toZero,
        𝒮.2.coeff⟩
    else 𝒮.2⟩

open Classical in
/-- With the dotted edge `δ_{xy}`, the components of the normal form. -/
private theorem TEqShape_normS_of_dot {m : ℕ} (S : Graph 2 m)
    (h : mkC .dot (.inl 0) (.inl 1) ∈ S.comps) :
    (TEqSigma.normS ⟨m, S⟩).2.comps = S.comps.map fun c =>
      if c = mkC .dot (.inl 0) (.inl 1) then c else c.map TEqShape_toZero := by
  simp only [TEqSigma.normS]
  simp [h]

/-- Without the dotted edge `δ_{xy}`, the components of the normal form are those of `𝒮`. -/
private theorem TEqShape_normS_of_not_dot {m : ℕ} (S : Graph 2 m)
    (h : mkC .dot (.inl 0) (.inl 1) ∉ S.comps) : (TEqSigma.normS ⟨m, S⟩).2.comps = S.comps := by
  simp only [TEqSigma.normS]
  simp [h]

/-- The normal form has the scaling order of `𝒮`: its components have the kinds of those of `𝒮`. -/
private theorem TEqShape_normS_ord {m : ℕ} (S : Graph 2 m) :
    (TEqSigma.normS ⟨m, S⟩).2.ord = S.ord := by
  classical
  simp only [TEqSigma.normS]
  split
  · unfold Graph.ord
    simp only [List.map_map]
    congr 2
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply]
    split_ifs <;> rfl
  · rfl

/-- The normal form has the coefficient of `𝒮`. -/
private theorem TEqShape_normS_coeff {m : ℕ} (S : Graph 2 m) :
    (TEqSigma.normS ⟨m, S⟩).2.coeff = S.coeff := by
  simp only [TEqSigma.normS]
  split <;> rfl

/-! ## Components and maps of the atoms -/

/-- The image of the image of a component is its image under the composite. -/
private theorem TEqShape_map_map {U V W : Type*} (f : V → W) (g : U → V) (c : Comp U) :
    (c.map g).map f = c.map (f ∘ g) := by
  obtain ⟨k, x, y, mi, lab⟩ := c
  simp only [Comp.map, List.map_map, Option.map_map, Prod.map_comp_map, Function.id_comp,
    Function.comp_apply]

/-- Two maps that agree on the two atoms of a component without minor and label have the same
image of it. -/
private theorem TEqShape_map_congr {V W : Type*} {f g : V → W} {c : Comp V} (hm : c.minor = [])
    (hl : c.label = none) (hx : f c.x = g c.x) (hy : f c.y = g c.y) : c.map f = c.map g := by
  obtain ⟨k, x, y, mi, lab⟩ := c
  simp only at hm hl hx hy
  subst hm hl
  simp [Comp.map, hx, hy]

/-- A component without minor and label whose image has no minor and no label. -/
private theorem TEqShape_plain_of_map {V W : Type*} {f : V → W} {c : Comp V}
    (hm : (c.map f).minor = []) (hl : (c.map f).label = none) : c.minor = [] ∧ c.label = none := by
  obtain ⟨k, x, y, mi, lab⟩ := c
  simp only [Comp.map, List.map_eq_nil_iff, Option.map_eq_none_iff] at hm hl
  exact ⟨hm, hl⟩

/-! ## No dotted edge in an output graph of [II, Lemma 6.7] -/

section DotFree

variable {N : ℕ} {Γ : Graph 3 N}

/-- A walk from a set to its complement has an edge with one end in the set and one outside. -/
private theorem TEqShape_reach_cross {V : Type*} {r : V → V → Prop} {P : V → Prop} {u v : V}
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

/-- No dotted edge joins an external and an internal atom: at `⊗` only diffusive edges, and no
`⊕/⊖`-recollision. -/
private theorem TEqShape_noMixed (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
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
private theorem TEqShape_unp (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    (a : Fin 3) (b : Fin N) : ¬ Γ.SameBlock (.inl a) (.inr b) := by
  intro h
  obtain ⟨u, v, ⟨c, hc, hd, hu, hv⟩, hcr⟩ :=
    TEqShape_reach_cross (P := fun w : Atom 3 N => w.isLeft = true) h rfl (by simp)
  have := TEqShape_noMixed hTD hNR hc hd
  subst hu hv
  rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact this.1 ⟨h1, by simpa using h2⟩
  · exact this.2 ⟨by simpa using h2, h1⟩

/-- A graph with only diffusive edges at `⊗`, not a `⊕/⊖`-recollision graph, normal regular,
plain and with the clause on the external atoms has no dotted edge: a dotted edge has an external
end ([I, Def 2.11]), is not joined to an internal atom, and two distinct external atoms in one
block would need an internal atom in it. -/
private theorem TEqShape_dotFree (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    {C : ℕ} (hN : Γ.Normal C) (hP : Γ.Plain) (hE : Γ.ExtClause) :
    ∀ c ∈ Γ.comps, c.kind ≠ .dot := by
  intro c hc hd
  have hm := TEqShape_noMixed hTD hNR hc hd
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
  exact TEqShape_unp hTD hNR a b hb

end DotFree

/-- **An output graph of [II, Lemma 6.7] has no dotted edge** ([II, Lemma 6.7], [I, Def 2.11]):
for `n ≥ 3` and a record `𝒯` that is the structural part of an `(n - 1)`-th order `T`-expansion
with error order `D`, every output graph `g` of the run `RunCompare.run` of [II, Strategy 6.6]
with the family `TEqSigma.qFam` that is of the class `Graph.LeafDet`, not a
`⊕/⊖`-recollision graph and of scaling order `≤ n` has no component of kind `.dot`. -/
theorem TEqSigma.detLeaf_dotFree : ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n →
    𝒯.IsTExpStruct Sig (n - 1) D → ∀ g ∈ RunCompare.run TEqSigma.qFam n D 𝒯, g.2.LeafDet →
    ¬ g.2.IsRecollision {1, 2} → g.2.ord ≤ n → ∀ c ∈ g.2.comps, c.kind ≠ .dot := by
  intro n D Sig 𝒯 hn hT g hg hdet hNR hord
  obtain ⟨-, -, ⟨C, hN⟩, hLC, hPl, -⟩ :=
    (RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig 𝒯 hn hT).2.2 g hg
  have hnD : n ≤ D := by have := hT.1; omega
  exact TEqShape_dotFree hLC.1 hNR hN (hPl (by omega)) hdet.2.2.2.1

/-! ## The normal form keeps the leaf form -/

/-- The atom map of the graph `𝒮` of the leaf form into the output graph: `0 ↦ x`, `1 ↦ y`, the
internal atom `j ↦ e j`. -/
private def TEqShape_phi {N m : ℕ} (x y α : Fin N)
    (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) : Atom 2 m → Atom 3 N :=
  Sum.elim ![.inr x, .inr y] fun j => .inr (e j).1

/-- The components of `g` in the leaf form, with the components `R` of `𝒮` read in `g`. -/
private def TEqShape_gList {N m : ℕ} (x y α : Fin N)
    (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) (R : List (Comp (Atom 2 m)))
    (sy : Comp (Atom 3 N)) (X : List (Comp (Atom 3 N))) (ℓ : ℕ) : List (Comp (Atom 3 N)) :=
  mkC (.theta []) (.inl 0) (.inr x) :: R.map (Comp.map (TEqShape_phi x y α e)) ++
    [sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++ X ++
    List.replicate ℓ (mkC .xdot (.inr α) (.inr α))

/-- The components of `𝒮` in the leaf form. -/
private def TEqShape_sList {N m : ℕ} (x y : Fin N) (R : List (Comp (Atom 2 m))) (ℓ : ℕ) :
    List (Comp (Atom 2 m)) :=
  (if x = y then [mkC .dot (.inl 0) (.inl 1)] else []) ++ R ++
    List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))

/-- **The normal form of a leaf form**: for a graph `g` without dotted edge and a leaf form of `g`
with the components `R` of `𝒮`, the normal form of `𝒮` is a leaf form of `g` with the same atoms
`x`, `y`, `α`, `e`, the same `s_{yα}`, `×`-dotted edges and `ℓ`, and the components `R'` of `R`
with every end at `1` moved to `0` when `x = y`; no component of `R'` has an end at `1` when
`x = y`. -/
private theorem TEqShape_norm {N m : ℕ} {Γ : Graph 3 N} {S S' : Graph 2 m} {x y α : Fin N}
    {e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}} {R : List (Comp (Atom 2 m))}
    {sy : Comp (Atom 3 N)} {X : List (Comp (Atom 3 N))} {ℓ : ℕ}
    (hdot : ∀ c ∈ Γ.comps, c.kind ≠ .dot)
    (hg : Γ.comps.Perm (TEqShape_gList x y α e R sy X ℓ))
    (hS : S.comps.Perm (TEqShape_sList x y R ℓ))
    (hS' : S'.comps = (TEqSigma.normS ⟨m, S⟩).2.comps) :
    ∃ R' : List (Comp (Atom 2 m)), Γ.comps.Perm (TEqShape_gList x y α e R' sy X ℓ) ∧
      S'.comps.Perm (TEqShape_sList x y R' ℓ) ∧
      (x = y → ∀ c ∈ R', c.x ≠ .inl 1 ∧ c.y ≠ .inl 1) := by
  classical
  have hRd : ∀ c ∈ R, c.kind ≠ .dot := by
    intro c hc
    have : c.map (TEqShape_phi x y α e) ∈ Γ.comps := hg.mem_iff.2 (by
      simp only [TEqShape_gList, List.cons_append, List.append_assoc, List.mem_cons,
        List.mem_append, List.mem_map]
      exact Or.inr (Or.inl ⟨c, hc, rfl⟩))
    exact hdot _ this
  by_cases hxy : x = y
  · subst hxy
    have hδ : mkC .dot (.inl 0) (.inl 1) ∈ S.comps :=
      hS.mem_iff.2 (by simp [TEqShape_sList])
    rw [TEqShape_normS_of_dot S hδ] at hS'
    rw [hS']
    refine ⟨R.map (Comp.map TEqShape_toZero), ?_, ?_, fun _ c hc => ?_⟩
    · have hφ : TEqShape_phi x x α e ∘ TEqShape_toZero = TEqShape_phi x x α e := by
        funext u
        cases u with
        | inl i => fin_cases i <;> rfl
        | inr j => rfl
      have : (R.map (Comp.map TEqShape_toZero)).map (Comp.map (TEqShape_phi x x α e)) =
          R.map (Comp.map (TEqShape_phi x x α e)) := by
        rw [List.map_map]
        refine List.map_congr_left fun c _ => ?_
        simp only [Function.comp_apply, TEqShape_map_map, hφ]
      simpa only [TEqShape_gList, this] using hg
    · refine (hS.map _).trans (List.Perm.of_eq ?_)
      have h2 : ∀ c ∈ R, (if c = mkC .dot (.inl 0) (.inl 1) then c else c.map TEqShape_toZero) =
          c.map TEqShape_toZero := fun c hc => by
        have : c ≠ mkC .dot (.inl 0) (.inl 1) := fun h => hRd c hc (by rw [h]; rfl)
        simp [this]
      have h3 : (if (mkC .xdot (.inl 0) (.inl 0) : Comp (Atom 2 m)) = mkC .dot (.inl 0) (.inl 1)
          then mkC .xdot (.inl 0) (.inl 0)
          else (mkC .xdot (.inl 0) (.inl 0) : Comp (Atom 2 m)).map TEqShape_toZero) =
          (mkC .xdot (.inl 0) (.inl 0) : Comp (Atom 2 m)) := by
        simp [mkC, Comp.map, TEqShape_toZero]
      have e1 : ∀ R₀ : List (Comp (Atom 2 m)), TEqShape_sList x x R₀ ℓ =
          mkC .dot (.inl 0) (.inl 1) :: (R₀ ++ List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))) :=
        fun R₀ => by simp [TEqShape_sList]
      simp only [e1, List.map_cons, List.map_append, List.map_replicate, List.map_congr_left h2, h3]
      simp
    · obtain ⟨c₀, -, rfl⟩ := List.mem_map.1 hc
      constructor <;> simp only [Comp.map] <;>
        [cases c₀.x; cases c₀.y] <;> simp [TEqShape_toZero]
  · have hδ : mkC .dot (.inl 0) (.inl 1) ∉ S.comps := by
      intro h
      have h' := hS.mem_iff.1 h
      simp only [TEqShape_sList, hxy, ↓reduceIte, List.nil_append, List.mem_append,
        List.mem_replicate] at h'
      rcases h' with h' | ⟨-, h'⟩
      · exact hRd _ h' rfl
      · cases h'
    rw [TEqShape_normS_of_not_dot S hδ] at hS'
    rw [hS']
    exact ⟨R, hg, hS, fun h => absurd h hxy⟩

/-- **The normal form keeps the leaf form** ([I, Def 2.13 (i)], [II, (6.7)]): for a graph `g`
without dotted edge and a leaf form `TEqSigma.LeafOf g 𝒮`, the normal form of `𝒮` is a leaf form
of `g`; it has the scaling order and the coefficient of `𝒮`. -/
theorem TEqSigma.normS_leafOf {g : Σ m, Graph 3 m} {m : ℕ} {𝒮 : Graph 2 m}
    (h : TEqSigma.LeafOf g 𝒮) (hg : ∀ c ∈ g.2.comps, c.kind ≠ .dot) :
    TEqSigma.LeafOf g (TEqSigma.normS ⟨m, 𝒮⟩).2 ∧ (TEqSigma.normS ⟨m, 𝒮⟩).2.ord = 𝒮.ord ∧
      (TEqSigma.normS ⟨m, 𝒮⟩).2.coeff = 𝒮.coeff := by
  obtain ⟨x, y, α, e, R, sy, X, ℓ, hαx, hαy, hsy, hX, hX1, hX2, hgp, hSp, hc⟩ := h
  obtain ⟨R', hg', hS', -⟩ := TEqShape_norm (S' := (TEqSigma.normS ⟨m, 𝒮⟩).2) hg hgp hSp rfl
  refine ⟨⟨x, y, α, e, R', sy, X, ℓ, hαx, hαy, hsy, hX, hX1, hX2, hg', hS', ?_⟩,
    TEqShape_normS_ord 𝒮, TEqShape_normS_coeff 𝒮⟩
  rw [TEqShape_normS_coeff]; exact hc

/-! ## The shape of the normal form -/

section Shape

/-- Reachability is carried by a map that sends every edge to two atoms joined by a path. -/
private theorem TEqShape_reach_map {V W : Type*} {r : V → V → Prop} {G : SimpleGraph W}
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
private theorem TEqShape_reach_rel {W : Type*} {r : W → W → Prop} {u v : W} (h : r u v) :
    (SimpleGraph.fromRel r).Reachable u v := by
  by_cases huv : u = v
  · subst huv; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨huv, Or.inl h⟩)

/-- The image of a sublist up to order under a map. -/
private theorem TEqShape_subperm_map {β γ : Type*} (f : β → γ) {l₁ l₂ : List β}
    (h : l₁.Subperm l₂) : (l₁.map f).Subperm (l₂.map f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

/-- A fold of `dotBlocks` over components without dotted edge leaves the partition unchanged. -/
private theorem TEqShape_fold_nodot {V : Type*} [DecidableEq V] :
    ∀ (L : List (Comp V)), (∀ c ∈ L, c.kind ≠ .dot) → ∀ P : List (List V),
      L.foldl (fun P c => if c.kind = .dot then joinBlocks P c.x c.y else P) P = P
  | [], _, _ => rfl
  | c :: L, h, P => by
    rw [List.foldl_cons, ite_eq_right_iff.2 fun h' => absurd h' (h c List.mem_cons_self)]
    exact TEqShape_fold_nodot L (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) P

/-- Joining the atoms `0` and `1` in the partition of the atoms of a graph with two external
atoms and `m` internal atoms into singletons leaves `m + 1` blocks. -/
private theorem TEqShape_blocks_len (m : ℕ) :
    (joinBlocks ((allAtoms 2 m).map fun a => [a]) (.inl 0) (.inl 1)).length = m + 1 := by
  simp [joinBlocks, allAtoms, List.filter_map, Function.comp_def]

variable {N m : ℕ} {x y α : Fin N} {e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}}

/-- The projection of the atoms of the output graph onto those of `𝒮`: `⊗` and `x` to `0`; `y` to
`1` (to `0` if `x = y`), and `⊕`, `⊖`, `α` to the image of `y`; the atom `e j` to `j`. -/
private def TEqShape_pi (x y α : Fin N) (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) :
    Atom 3 N → Atom 2 m
  | .inl i => if i = 0 then .inl 0 else if x = y then .inl 0 else .inl 1
  | .inr a => if hx : a = x then .inl 0 else if hy : a = y then .inl 1 else
      if hα : a = α then (if x = y then .inl 0 else .inl 1) else .inr (e.symm ⟨a, hx, hy, hα⟩)

/-- The projection inverts the atom map, except at the atom `1` when `x = y`. -/
private theorem TEqShape_pi_phi (u : Atom 2 m) (hu : x = y → u ≠ .inl 1) :
    TEqShape_pi x y α e (TEqShape_phi x y α e u) = u := by
  cases u with
  | inl i =>
    fin_cases i
    · simp [TEqShape_phi, TEqShape_pi]
    · have hxy : y ≠ x := fun h => hu h.symm rfl
      simp [TEqShape_phi, TEqShape_pi, hxy]
  | inr j =>
    have h1 := (e j).2.1
    have h2 := (e j).2.2.1
    have h3 := (e j).2.2.2
    simp [TEqShape_phi, TEqShape_pi, h1, h2, h3]

/-- The atom map sends `1` to the image of `0` when `x = y`. -/
private theorem TEqShape_pi_phi_one (hxy : x = y) :
    TEqShape_pi x y α e (TEqShape_phi x y α e (.inl 1)) = .inl 0 := by
  subst hxy
  simp [TEqShape_phi, TEqShape_pi]

/-- The atom map sends every atom to an internal atom. -/
private theorem TEqShape_phi_right (u : Atom 2 m) : (TEqShape_phi x y α e u).isRight = true := by
  cases u with
  | inl i => fin_cases i <;> rfl
  | inr j => rfl

/-- The components of the output graph in the leaf form, read through the projection: the
components of `R` read in the output graph, or a component whose two atoms have one image. -/
private theorem TEqShape_comp {Γ : Graph 3 N} {R : List (Comp (Atom 2 m))}
    {sy : Comp (Atom 3 N)} {X : List (Comp (Atom 3 N))} {ℓ : ℕ} (hαx : α ≠ x) (hαy : α ≠ y)
    (hsy : sy = mkC (.waved .s) (.inr y) (.inr α) ∨ sy = mkC (.waved .s) (.inr α) (.inr y))
    (hX : ∀ c ∈ X, c = mkC .xdot (.inr α) (.inl 1) ∨ c = mkC .xdot (.inl 1) (.inr α) ∨
      c = mkC .xdot (.inr α) (.inl 2) ∨ c = mkC .xdot (.inl 2) (.inr α))
    (hg : Γ.comps.Perm (TEqShape_gList x y α e R sy X ℓ))
    (hcan : x = y → ∀ c ∈ R, c.x ≠ .inl 1 ∧ c.y ≠ .inl 1) :
    ∀ c ∈ Γ.comps, TEqShape_pi x y α e c.x = TEqShape_pi x y α e c.y ∨
      ∃ c₀ ∈ R, c = c₀.map (TEqShape_phi x y α e) ∧ TEqShape_pi x y α e c.x = c₀.x ∧
        TEqShape_pi x y α e c.y = c₀.y := by
  have hy : ∀ i : Fin 3, i ≠ 0 →
      TEqShape_pi x y α e (.inl i) = TEqShape_pi x y α e (.inr y) := by
    intro i hi
    by_cases hxy : x = y
    · subst hxy; simp [TEqShape_pi, hi]
    · have : y ≠ x := Ne.symm hxy
      simp [TEqShape_pi, hi, hxy, this]
  have hα : TEqShape_pi x y α e (.inr α) = TEqShape_pi x y α e (.inr y) := by
    by_cases hxy : x = y
    · subst hxy; simp [TEqShape_pi, hαx]
    · have : y ≠ x := Ne.symm hxy
      simp [TEqShape_pi, hαx, hαy, hxy, this]
  intro c hc
  have hc' := hg.mem_iff.1 hc
  simp only [TEqShape_gList, List.cons_append, List.append_assoc, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_replicate, List.not_mem_nil, false_or] at hc'
  rcases hc' with rfl | ⟨c₀, hc₀, rfl⟩ | rfl | rfl | rfl | hcX | ⟨-, rfl⟩
  · left; simp [TEqShape_pi, mkC]
  · right
    refine ⟨c₀, hc₀, rfl, ?_, ?_⟩
    · exact TEqShape_pi_phi _ fun h => (hcan h c₀ hc₀).1
    · exact TEqShape_pi_phi _ fun h => (hcan h c₀ hc₀).2
  · left; rcases hsy with rfl | rfl <;> simp [mkC, hα]
  · left; simp only [mkC]; rw [hy 1 (by decide), hα]
  · left; simp only [mkC]; rw [hy 2 (by decide), hα]
  · left
    rcases hX c hcX with rfl | rfl | rfl | rfl <;> simp only [mkC] <;>
      first | rw [hy 1 (by decide), hα] | rw [hy 2 (by decide), hα]
  · left; rfl

/-- The relation of the components of a given kind of a graph. -/
private def TEqShape_rel {k n : ℕ} (Γ : Graph k n) (q : Kind → Prop) : Atom k n → Atom k n → Prop :=
  fun u v => ∃ c ∈ Γ.comps, q c.kind ∧ c.x = u ∧ c.y = v

/-- **The shape of a leaf form without dotted edge in `R`** ([II, Def 2.7 (i)], [II, Def 3.3 (2),
(3), (5)]): for a normal regular, doubly connected graph `Γ` with a deterministic maximal subgraph,
the run kinds `Graph.RunKinds K`, no minor, no label and no dotted edge, and a leaf form of `Γ`
with the components `R` of `𝒮`, none of which has an end at `1` when `x = y`, the graph `𝒮` is
normal regular with dotted edges forming a forest, of the deterministic kinds, and doubly
connected with `x`, `y` read as internal atoms. -/
private theorem TEqShape_shape {K C : ℕ} {Γ : Graph 3 N} {S : Graph 2 m}
    {R : List (Comp (Atom 2 m))} {sy : Comp (Atom 3 N)} {X : List (Comp (Atom 3 N))} {ℓ : ℕ}
    (hN : Γ.Normal C) (hDC : Γ.DoublyConnected) (hMD : Γ.MaxDeterministic) (hK : Γ.RunKinds K)
    (hmin : ∀ c ∈ Γ.comps, c.minor = []) (hL : Γ.LabelFree) (hdot : ∀ c ∈ Γ.comps, c.kind ≠ .dot)
    (hαx : α ≠ x) (hαy : α ≠ y)
    (hsy : sy = mkC (.waved .s) (.inr y) (.inr α) ∨ sy = mkC (.waved .s) (.inr α) (.inr y))
    (hX : ∀ c ∈ X, c = mkC .xdot (.inr α) (.inl 1) ∨ c = mkC .xdot (.inl 1) (.inr α) ∨
      c = mkC .xdot (.inr α) (.inl 2) ∨ c = mkC .xdot (.inl 2) (.inr α))
    (hg : Γ.comps.Perm (TEqShape_gList x y α e R sy X ℓ))
    (hS : S.comps.Perm (TEqShape_sList x y R ℓ))
    (hcan : x = y → ∀ c ∈ R, c.x ≠ .inl 1 ∧ c.y ≠ .inl 1) :
    (∃ C, S.Normal C ∧ S.DotsAcyclic) ∧ S.comps.all (Comp.isDetKind K) = true ∧
      (S.mapAtoms (Sum.elim (fun a => Sum.inr (Fin.castAdd m a))
        (fun b => Sum.inr (Fin.natAdd 2 b))) : Graph 0 (2 + m)).DoublyConnected := by
  classical
  -- the components of `R`
  have hRmem : ∀ c ∈ R, c.map (TEqShape_phi x y α e) ∈ Γ.comps := fun c hc => hg.mem_iff.2 (by
    simp only [TEqShape_gList, List.cons_append, List.append_assoc, List.mem_cons,
      List.mem_append, List.mem_map]
    exact Or.inr (Or.inl ⟨c, hc, rfl⟩))
  have hRS : ∀ c ∈ R, c ∈ S.comps := fun c hc => hS.mem_iff.2 (by
    simp only [TEqShape_sList, List.mem_append]
    exact Or.inl (Or.inr hc))
  have hRnr : ∀ c ∈ R, c.kind.isRandom = false := by
    intro c hc
    cases h : c.kind.isRandom
    · rfl
    · rcases hMD _ (hRmem c hc) h with h' | h'
      · have := TEqShape_phi_right (x := x) (y := y) (α := α) (e := e) c.x
        simp only [Comp.map] at h'
        cases hc' : (TEqShape_phi x y α e) c.x <;> simp_all
      · have := TEqShape_phi_right (x := x) (y := y) (α := α) (e := e) c.y
        simp only [Comp.map] at h'
        cases hc' : (TEqShape_phi x y α e) c.y <;> simp_all
  have hRsol : ∀ c ∈ R, c.kind.isSolid = false := by
    intro c hc
    have := hRnr c hc
    revert this
    cases c.kind <;> simp [Kind.isSolid, Kind.isRandom]
  have hRdot : ∀ c ∈ R, c.kind ≠ .dot := fun c hc => hdot _ (hRmem c hc)
  have hRpl : ∀ c ∈ R, c.minor = [] ∧ c.label = none := fun c hc =>
    TEqShape_plain_of_map (hmin _ (hRmem c hc)) (hL _ (hRmem c hc))
  have hSmem : ∀ c ∈ S.comps, (x = y ∧ c = mkC .dot (.inl 0) (.inl 1)) ∨ c ∈ R ∨
      c = mkC .xdot (.inl 0) (.inl 0) := by
    intro c hc
    have h := hS.mem_iff.1 hc
    simp only [TEqShape_sList, List.mem_append, List.mem_replicate] at h
    rcases h with (h | h) | ⟨-, h⟩
    · split_ifs at h with hxy
      · exact Or.inl ⟨hxy, List.mem_singleton.1 h⟩
      · cases h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hcomp := TEqShape_comp hαx hαy hsy hX hg hcan
  have hδS : x = y → mkC .dot (.inl 0) (.inl 1) ∈ S.comps := fun hxy => hS.mem_iff.2 (by
    simp [TEqShape_sList, hxy])
  -- edges of `Γ` carried to `𝒮` by the projection
  have hpull : ∀ (q : Kind → Prop) (a b : Atom 3 N), TEqShape_rel Γ q a b →
      (SimpleGraph.fromRel (TEqShape_rel S q)).Reachable ((TEqShape_pi x y α e) a)
        ((TEqShape_pi x y α e) b) := by
    rintro q a b ⟨c, hc, hq, rfl, rfl⟩
    rcases hcomp c hc with h | ⟨c₀, hc₀, rfl, h1, h2⟩
    · rw [h]
    · rw [h1, h2]
      exact TEqShape_reach_rel ⟨c₀, hRS c₀ hc₀, hq, rfl, rfl⟩
  have hback : ∀ (q : Kind → Prop), q .dot → ∀ u : Atom 2 m,
      (SimpleGraph.fromRel (TEqShape_rel S q)).Reachable
        ((TEqShape_pi x y α e) ((TEqShape_phi x y α e) u)) u := by
    intro q hq u
    by_cases hu : x = y ∧ u = .inl 1
    · obtain ⟨hxy, rfl⟩ := hu
      rw [TEqShape_pi_phi_one hxy]
      exact TEqShape_reach_rel ⟨_, hδS hxy, hq, rfl, rfl⟩
    · rw [TEqShape_pi_phi u fun h h' => hu ⟨h, h'⟩]
  -- no solid edge and no `×`-dotted edge between distinct atoms in `𝒮`
  have hSsol : ∀ c ∈ S.comps, c.kind.isSolid = false := by
    intro c hc
    rcases hSmem c hc with ⟨-, rfl⟩ | h | rfl
    · rfl
    · exact hRsol c h
    · rfl
  have hSx : ∀ c ∈ S.comps, c.kind = .xdot → c.x = c.y := by
    intro c hc hk
    rcases hSmem c hc with ⟨-, rfl⟩ | h | rfl
    · cases hk
    · by_contra hne
      have hne' : (TEqShape_phi x y α e) c.x ≠ (TEqShape_phi x y α e) c.y := fun he => hne (by
        rw [← TEqShape_pi_phi (x := x) (y := y) (α := α) (e := e) c.x
            fun h' => (hcan h' c h).1,
          ← TEqShape_pi_phi (x := x) (y := y) (α := α) (e := e) c.y
            fun h' => (hcan h' c h).2]
        exact congrArg _ he)
      obtain ⟨c', hc', hs, hends⟩ :=
        (hN.2.2 ((TEqShape_phi x y α e) c.x) ((TEqShape_phi x y α e) c.y) hne').1
          ⟨c.map (TEqShape_phi x y α e), hRmem c h, hk, Or.inl ⟨rfl, rfl⟩⟩
      have hr : c'.kind.isRandom = true := by
        revert hs; cases c'.kind <;> simp [Kind.isSolid, Kind.isRandom]
      have hx := TEqShape_phi_right (x := x) (y := y) (α := α) (e := e) c.x
      have hy := TEqShape_phi_right (x := x) (y := y) (α := α) (e := e) c.y
      have hcx : c'.x.isRight = true := by
        rcases hends with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1] <;> assumption
      have hcy : c'.y.isRight = true := by
        rcases hends with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2] <;> assumption
      rcases hMD c' hc' hr with h' | h'
      · cases hh : c'.x with
        | inl _ => rw [hh] at hcx; cases hcx
        | inr _ => rw [hh] at h'; cases h'
      · cases hh : c'.y with
        | inl _ => rw [hh] at hcy; cases hcy
        | inr _ => rw [hh] at h'; cases h'
    · rfl
  -- `Normal`
  have hNorm : S.Normal (2 + m + S.comps.length) := by
    refine ⟨⟨le_refl _, ?_, ?_, ?_⟩, ?_, ?_⟩
    · have hE : ∀ {k n : ℕ} (G : Graph k n),
          G.edgeGraph = SimpleGraph.fromRel (TEqShape_rel G fun _ => True) := by
        intro k n G
        unfold Graph.edgeGraph TEqShape_rel
        simp only [true_and]
      intro u v
      have h := TEqShape_reach_map (TEqShape_pi x y α e) (r := TEqShape_rel Γ fun _ => True)
        (G := SimpleGraph.fromRel (TEqShape_rel S fun _ => True)) (hpull _)
        (u := (TEqShape_phi x y α e) u) (v := (TEqShape_phi x y α e) v)
        (hE Γ ▸ hN.1.connected ((TEqShape_phi x y α e) u) ((TEqShape_phi x y α e) v))
      rw [hE S]
      exact ((hback (fun _ => True) trivial u).symm.trans h).trans
        (hback (fun _ => True) trivial v)
    · intro a b
      have hq := TEqShape_reach_map (TEqShape_pi x y α e) (G := SimpleGraph.fromRel (TEqShape_rel S
          fun k => k.joinsMol = true ∧ k ≠ .dot ∨ k.isDiffusive = true))
        (hpull fun k => k.joinsMol = true ∧ k ≠ .dot ∨ k.isDiffusive = true)
        (hN.1.internal (e a).1 (e b).1)
      have ha : (TEqShape_pi x y α e) (.inr (e a).1) = .inr a :=
        TEqShape_pi_phi (.inr a) fun _ => by simp
      have hb : (TEqShape_pi x y α e) (.inr (e b).1) = .inr b :=
        TEqShape_pi_phi (.inr b) fun _ => by simp
      rw [ha, hb] at hq
      exact hq
    · intro c hc hk
      rcases hSmem c hc with ⟨-, rfl⟩ | h | rfl
      · exact Or.inl rfl
      · exact absurd hk (hRdot c h)
      · cases hk
    · intro c hc hs
      rw [hSsol c hc] at hs
      cases hs
    · intro u v huv
      constructor
      · rintro ⟨c, hc, hk, hends⟩
        have := hSx c hc hk
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd this huv
        · exact absurd this.symm huv
      · rintro ⟨c, hc, hs, -⟩
        rw [hSsol c hc] at hs
        cases hs
  -- `DotsAcyclic`
  have hDA : S.DotsAcyclic := by
    unfold Graph.DotsAcyclic
    have hcount : (S.comps.filter fun c => decide (c.kind = .dot)).length =
        if x = y then 1 else 0 := by
      rw [(hS.filter _).length_eq]
      simp only [TEqShape_sList, List.filter_append, List.length_append]
      have h1 : (R.filter fun c => decide (c.kind = .dot)) = [] :=
        List.filter_eq_nil_iff.2 fun c hc => by simpa using hRdot c hc
      have h2 : ((List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0) : Comp (Atom 2 m))).filter
          fun c => decide (c.kind = .dot)) = [] :=
        List.filter_eq_nil_iff.2 fun c hc => by
          rw [(List.mem_replicate.1 hc).2]; simp [mkC]
      rw [h1, h2]
      split_ifs <;> simp [mkC]
    have hblocks : (dotBlocks (allAtoms 2 m) S.comps).length =
        (dotBlocks (allAtoms 2 m) (TEqShape_sList x y R ℓ)).length := by
      have h1 := Graph.dotBlocks_length_eq_card S
      have h2 := Graph.dotBlocks_length_eq_card (⟨TEqShape_sList x y R ℓ, 1⟩ : Graph 2 m)
      have h3 : S.dotGraph = (⟨TEqShape_sList x y R ℓ, 1⟩ : Graph 2 m).dotGraph := by
        unfold Graph.dotGraph
        congr 1
        funext u v
        exact propext ⟨fun ⟨c, hc, h⟩ => ⟨c, hS.mem_iff.1 hc, h⟩,
          fun ⟨c, hc, h⟩ => ⟨c, hS.mem_iff.2 hc, h⟩⟩
      rw [h1, h2, h3]
    have hnd : ∀ c ∈ R ++ List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0)), c.kind ≠ .dot := by
      intro c hc
      rcases List.mem_append.1 hc with h | h
      · exact hRdot c h
      · rw [(List.mem_replicate.1 h).2]; simp [mkC]
    rw [hcount, hblocks]
    unfold dotBlocks
    simp only [TEqShape_sList, List.append_assoc]
    split_ifs with hxy
    · have hk : (mkC .dot (.inl 0) (.inl 1) : Comp (Atom 2 m)).kind = .dot := rfl
      simp only [List.singleton_append, List.foldl_cons, hk, ↓reduceIte,
        TEqShape_fold_nodot _ hnd]
      simp only [mkC, TEqShape_blocks_len]
      omega
    · simp only [List.nil_append, TEqShape_fold_nodot _ hnd]
      simp [allAtoms]
  -- the kinds
  have hKind : S.comps.all (Comp.isDetKind K) = true := by
    rw [List.all_eq_true]
    intro c hc
    rcases hSmem c hc with ⟨-, rfl⟩ | h | rfl
    · rfl
    · obtain ⟨hm, hl⟩ := hRpl c h
      have hk := List.all_eq_true.1 hK _ (hRmem c h)
      have hr := hRnr c h
      obtain ⟨κ, cx, cy, mi, lab⟩ := c
      simp only at hm hl hr
      subst hm hl
      simp only [Comp.isRunKind, Comp.map] at hk
      cases κ <;> simp_all [Comp.isDetKind, Kind.isRandom]
    · rfl
  -- doubly connected with `x`, `y` internal
  set ιA : Atom 2 m → Atom 0 (2 + m) :=
    Sum.elim (fun a => Sum.inr (Fin.castAdd m a)) (fun b => Sum.inr (Fin.natAdd 2 b)) with hιA
  set ι' : Atom 2 m → Fin (2 + m) := Sum.elim (Fin.castAdd m) (Fin.natAdd 2) with hι'
  have hιι : ∀ u, ιA u = .inr (ι' u) := fun u => by cases u <;> rfl
  set Γ' : Graph 0 (2 + m) := S.mapAtoms ιA with hΓ'
  have hmolS : ∀ a b : Atom 2 m, S.molGraph.Reachable a b →
      Γ'.SameMol (.inr (ι' a)) (.inr (ι' b)) := by
    intro a b h
    refine Or.inr ⟨rfl, rfl, ?_⟩
    rw [← hιι, ← hιι]
    refine TEqShape_reach_map ιA (fun a' b' hab => ?_) h
    obtain ⟨c, hc, hj, rfl, rfl⟩ := hab
    exact TEqShape_reach_rel ⟨c.map ιA, List.mem_map.2 ⟨c, hc, rfl⟩, hj, rfl, rfl⟩
  have hδreach : ∀ B, x = y → (SimpleGraph.fromRel (nrel Γ' B)).Reachable
      (ι' (.inl 1)) (ι' ((TEqShape_pi x y α e) ((TEqShape_phi x y α e) (.inl 1)))) := by
    intro B hxy
    rw [TEqShape_pi_phi_one hxy]
    refine TEqShape_reach_rel (Or.inl (hmolS _ _ ?_))
    exact (TEqShape_reach_rel ⟨_, hδS hxy, rfl, rfl, rfl⟩ :
      (SimpleGraph.fromRel (TEqShape_rel S fun k => k.joinsMol = true)).Reachable _ _).symm
  set p : Comp (Atom 3 N) → Bool :=
    fun c => c.x.isRight && c.y.isRight && (c.kind.isDiffusive || c.kind.isBlue) with hp
  set ρ : Atom 3 N → Atom 0 (2 + m) := fun u => ιA ((TEqShape_pi x y α e) u) with hρ
  have hRρ : (R.map (Comp.map (TEqShape_phi x y α e))).map (Comp.map ρ) = R.map (Comp.map ιA) := by
    rw [List.map_map]
    refine List.map_congr_left fun c hc => ?_
    simp only [Function.comp_apply, TEqShape_map_map]
    refine TEqShape_map_congr (hRpl c hc).1 (hRpl c hc).2 ?_ ?_
    · simp only [Function.comp_apply, hρ]
      rw [TEqShape_pi_phi _ fun h => (hcan h c hc).1]
    · simp only [Function.comp_apply, hρ]
      rw [TEqShape_pi_phi _ fun h => (hcan h c hc).2]
  have hfilt : (Γ.comps.filter p).Subperm (R.map (Comp.map (TEqShape_phi x y α e))) := by
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
    simp only [TEqShape_gList, List.cons_append, List.append_assoc, List.filter_cons,
      List.filter_append, hX0, hl0, hsy0, hΘ0, hG1, hG2, Bool.false_eq_true, ↓reduceIte,
      List.append_nil, List.nil_append]
    exact List.filter_sublist
  have hsurj : ∀ a' : Fin (2 + m), ∃ u, ι' u = a' := fun a' =>
    Fin.addCases (motive := fun a' => ∃ u, ι' u = a') (fun i => ⟨.inl i, rfl⟩)
      (fun j => ⟨.inr j, rfl⟩) a'
  set φi : Atom 2 m → Fin N := Sum.elim ![x, y] (fun j => (e j).1) with hφi'
  have hφi : ∀ u, TEqShape_phi x y α e u = .inr (φi u) := by
    intro u
    cases u with
    | inl i => fin_cases i <;> rfl
    | inr j => rfl
  have hnet : ∀ B : List (Comp (Atom 3 N)),
      (∀ c ∈ B, c ∈ Γ.comps ∧ (c.kind.isDiffusive = true ∨ c.kind.isBlue = true)) →
      (SimpleGraph.fromRel (nrel Γ B)).Preconnected →
      (SimpleGraph.fromRel (nrel Γ' ((B.filter p).map (Comp.map ρ)))).Preconnected := by
    intro B hB hpre a' b'
    set f : Fin N → Fin (2 + m) := fun a => ι' ((TEqShape_pi x y α e) (.inr a)) with hf
    have hedge : ∀ a b, nrel Γ B a b →
        (SimpleGraph.fromRel (nrel Γ' ((B.filter p).map (Comp.map ρ)))).Reachable (f a) (f b) := by
      rintro a b (hm | ⟨c, hc, hx, hy⟩)
      · rcases hm with he | ⟨-, -, hm⟩
        · cases he; exact SimpleGraph.Reachable.refl _
        · refine TEqShape_reach_rel (Or.inl (hmolS _ _ ?_))
          exact TEqShape_reach_map (TEqShape_pi x y α e) (hpull fun k => k.joinsMol = true) hm
      · refine TEqShape_reach_rel (Or.inr ⟨c.map ρ, List.mem_map.2 ⟨c, List.mem_filter.2
          ⟨hc, ?_⟩, rfl⟩, ?_, ?_⟩)
        · have hk := (hB c hc).2
          simp only [hp, hx, hy, Sum.isRight_inr, Bool.true_and]
          rcases hk with hk | hk <;> simp [hk]
        · simp [Comp.map, hx, hρ, hιι, hf]
        · simp [Comp.map, hy, hρ, hιι, hf]
    obtain ⟨u, rfl⟩ := hsurj a'
    obtain ⟨v, rfl⟩ := hsurj b'
    have hu : ∀ w, (SimpleGraph.fromRel (nrel Γ' ((B.filter p).map (Comp.map ρ)))).Reachable
        (ι' w) (f (φi w)) := by
      intro w
      have : f (φi w) = ι' (TEqShape_pi x y α e (TEqShape_phi x y α e w)) := by
        simp only [hf, hφi]
      rw [this]
      by_cases hw : x = y ∧ w = .inl 1
      · obtain ⟨hxy, rfl⟩ := hw
        exact hδreach _ hxy
      · rw [TEqShape_pi_phi w fun h h' => hw ⟨h, h'⟩]
    exact ((hu u).trans (TEqShape_reach_map f hedge (hpre (φi u) (φi v)))).trans (hu v).symm
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc hDC
  have hmem : ∀ c ∈ Lb ++ Lu, c ∈ Γ.comps := fun c hc => hsub.subset hc
  refine ⟨⟨_, hNorm, hDA⟩, hKind, Graph.dc_of_dcl ⟨(Lb.filter p).map (Comp.map ρ),
    (Lu.filter p).map (Comp.map ρ), ?_, ?_, ?_, hnet Lb ?_ hsb, hnet Lu ?_ hsu⟩⟩
  · rw [← List.map_append, ← List.filter_append]
    have h1 := TEqShape_subperm_map (Comp.map ρ) ((hsub.filter p).trans hfilt)
    rw [hRρ] at h1
    refine h1.trans (TEqShape_subperm_map (Comp.map ιA) ?_)
    refine List.Subperm.trans ?_ hS.symm.subperm
    refine List.Sublist.subperm ?_
    unfold TEqShape_sList
    exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)
  · intro c hc
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
    exact hb c₁ (List.mem_filter.1 hc₁).1
  · intro c hc
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
    exact hu c₁ (List.mem_filter.1 hc₁).1
  · exact fun c hc => ⟨hmem c (List.mem_append_left _ hc), Or.inl (hb c hc)⟩
  · exact fun c hc => ⟨hmem c (List.mem_append_right _ hc), hu c hc⟩

end Shape

/-! ## The maps `sigma'`, `corr` and the construction `Strat` -/

/-- The normal forms of the graphs `𝒮` of an output graph `g` of [II, Lemma 6.7]
([II, (6.7)–(6.8)]): `TEqSigma.normS` applied to each graph of `TEqSigma.sigma g`. -/
def TEqSigma.sigma' (g : Σ m, Graph 3 m) : Expansion 2 := (TEqSigma.sigma g).map TEqSigma.normS

/-- The graph `Θ_{⊗x} 𝒮_{xy}` with the atoms `x = 0`, `y = 1` of `𝒮` internal: external atoms
`⊗, ⊕, ⊖`, internal atoms `x`, `y` and then those of `𝒮`; the coefficient of `𝒮`. -/
def TEqShape_thetaS {m : ℕ} (𝒮 : Graph 2 m) : Graph 3 (2 + m) :=
  ⟨mkC (.theta []) (.inl 0) (.inr 0) :: 𝒮.comps.map (Comp.map
      (Sum.elim (fun i => .inr (Fin.castAdd m i)) fun j => .inr (Fin.natAdd 2 j))), 𝒮.coeff⟩

open Classical in
/-- The graph `Θ_{⊗x} 𝒮_{xy}` at `x = y` ([I, Def 2.13 (i)]): the atoms `x = 0` and `y = 1` of `𝒮`
are one internal atom `x`, and the dotted edge `δ_{xy}` is removed; external atoms `⊗, ⊕, ⊖`,
internal atoms `x` and then those of `𝒮`; the coefficient of `𝒮`. -/
def TEqShape_thetaS₁ {m : ℕ} (𝒮 : Graph 2 m) : Graph 3 (1 + m) :=
  ⟨mkC (.theta []) (.inl 0) (.inr 0) :: (𝒮.comps.erase (mkC .dot (.inl 0) (.inl 1))).map
      (Comp.map (Sum.elim (fun _ => .inr 0) fun j => .inr (Fin.natAdd 1 j))), 𝒮.coeff⟩

open Classical in
/-- The three graphs `Θ_{⊗x} 𝒮_{xy} τ_{y,⊕⊖}`, `τ` in `tVarCorr` (the recollision terms of
[II, (4.15)], with coefficient `-|m|²`), substituted at `y`, `⊕`, `⊖`: the coefficient is
`-𝒮.coeff · m m̄`. With the dotted edge `δ_{xy}` in `𝒮`, the atoms `x = y` are one internal atom
(`TEqShape_thetaS₁`); otherwise `TEqShape_thetaS`. -/
def TEqShape_corrOf (𝒮 : Σ m, Graph 2 m) : Expansion 3 :=
  if mkC .dot (.inl 0) (.inl 1) ∈ 𝒮.2.comps then
    (TEqShape_thetaS₁ 𝒮.2).globalSubst (.inr 0) (.inl 1) (.inl 2) tVarCorr
  else (TEqShape_thetaS 𝒮.2).globalSubst (.inr 1) (.inl 1) (.inl 2) tVarCorr

open Classical in
/-- **The correction graphs** of an output graph `g` of [II, Lemma 6.7] (the `t → T` rewriting
before [II, (6.7)], with [II, (4.15)]): for a graph `g` of the class `Graph.LeafDet` that is not a
`⊕/⊖`-recollision graph, the graphs `Θ_{⊗x} 𝒮_{xy} τ_{y,⊕⊖}`, `τ` in `tVarCorr`, of the normal form
`𝒮` of its graph of `TEqSigma.sigma g` (`TEqShape_corrOf`); `[]` for any other graph. -/
def TEqSigma.corr (g : Σ m, Graph 3 m) : Expansion 3 :=
  if g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} then (TEqSigma.sigma' g).flatMap TEqShape_corrOf
  else []

/-- **The construction of [II, (6.8)]** with the normal forms `TEqSigma.sigma'` of the graphs `𝒮`
and the correction graphs `TEqSigma.corr`. -/
def TEqSigma.Strat : ℕ → ℕ → TRec → TEqRec := TEqSigma.strat TEqSigma.sigma' TEqSigma.corr

/-! ## `Σ_n` of the construction -/

open Classical in
/-- A graph of `Σ_n` of `TEqSigma.Strat` is a normal form `TEqSigma.sigma' g` of an output graph `g`
of [II, Lemma 6.7] of scaling order `n` of the run. -/
private theorem TEqShape_mem_sigN {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {g' : Σ m, Graph 2 m}
    (hg' : g' ∈ (TEqSigma.Strat n D 𝒯).SigN) :
    ∃ g ∈ RunCompare.run TEqSigma.qFam n D 𝒯,
      (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (n : ℤ)) ∧
        g' ∈ TEqSigma.sigma' g := by
  rw [TEqSigma.Strat, TEqSigma.strat_eq hn hT] at hg'
  unfold TEqSigma.ofLeaves at hg'
  rw [Multiset.mem_toList, Multiset.mem_coe, List.mem_flatMap] at hg'
  obtain ⟨g, hgF, hg'⟩ := hg'
  rw [List.mem_filter, decide_eq_true_eq] at hgF
  exact ⟨g, hgF.1, hgF.2, hg'⟩

/-- **`Σ_n` has the shape of an `n`-th order self-energy** ([II, Lemma 6.8], [II, Def 2.7 (i)],
[II, Def 3.3 (2), (3), (5)]): for `n ≥ 3` and a record `𝒯` that is the structural part of an
`(n - 1)`-th order `T`-expansion with error order `D` over some `Sig`, every graph of `Σ_n` of
`TEqSigma.Strat n D 𝒯` is normal regular with dotted edges forming a forest, deterministic with
labels of entries in `[4, n - 1]`, of scaling order `n`, and doubly connected with `x`, `y` read
as internal atoms. -/
theorem TEqSigma.sigN_shape : ∀ (n D : ℕ) (𝒯 : TRec), 3 ≤ n →
    (∃ Sig, 𝒯.IsTExpStruct Sig (n - 1) D) → SelfEnergyShape n (TEqSigma.Strat n D 𝒯).SigN := by
  rintro n D 𝒯 hn ⟨Sig, hT⟩ g' hg'
  obtain ⟨g, hg, ⟨hdet, hNR, hord⟩, hg'⟩ := TEqShape_mem_sigN hn hT hg'
  obtain ⟨m, 𝒮, hσ, hL, hO, -, -⟩ :=
    TEqSigma.detLeaf_form n D Sig 𝒯 hn hT g hg hdet hNR hord.le
  rw [TEqSigma.sigma', hσ, List.map_singleton, List.mem_singleton] at hg'
  subst hg'
  have hspec := RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig 𝒯 hn hT
  obtain ⟨-, hDC, ⟨C, hN⟩, -, hPl, -⟩ := hspec.2.2 g hg
  have hnD : n ≤ D := by have := hT.1; omega
  have hP : g.2.Plain := hPl (by omega)
  have hK := (RunExports.selRun_exports _ TEqSigma.qFam_spec n D Sig 𝒯 hn hT _ hspec.1 g hg).2.1
  have hdot := TEqSigma.detLeaf_dotFree n D Sig 𝒯 hn hT g hg hdet hNR hord.le
  obtain ⟨x, y, α, e, R, sy, X, ℓ, hαx, hαy, hsy, hX, -, -, hgp, hSp, -⟩ := hL
  obtain ⟨R', hg'', hS', hcan⟩ :=
    TEqShape_norm (S' := (TEqSigma.normS ⟨m, 𝒮⟩).2) hdot hgp hSp rfl
  obtain ⟨h1, h2, h3⟩ := TEqShape_shape hN hDC hdet.2.2.1 hK (fun c hc => (hP c hc).1) hdet.1
    hdot hαx hαy hsy hX hg'' hS' hcan
  refine ⟨h1, h2, ?_, h3⟩
  rw [TEqShape_normS_ord, hO, hord]

section Instances

open private h2Rec_struct from RBM8D.TExp.Second

end Instances

end RBM8D.Graphs
