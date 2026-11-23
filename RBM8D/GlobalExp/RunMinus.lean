module

public import RBM8D.GlobalExp.RunCompare
public import Batteries.Tactic.OpenPrivate
public import RBM8D.GlobalExp.Local
public import RBM8D.GlobalExp.TerminationC
public import RBM8D.GlobalExp.TerminationC2
public import RBM8D.TExp.Second
import all RBM8D.GlobalExp.Local
import all RBM8D.GlobalExp.TerminationC
import all RBM8D.GlobalExp.TerminationC2
import all RBM8D.TExp.Second
import all RBM8D.GlobalExp.RunCompare

@[expose] public section

/-!
# The red solid edge at `⊖` along the run of the selector

[II, Def 3.2 (9)] at `⊖` (the third clause of `Graph.AtExternals`) on the output graphs of the run
of [II, Strategy 6.6] driven by the selector `TerminationC_sel` ([II, Lemma 6.8]) from the graphs
of `A` and `Q` of the second order `T`-expansion, with a family `𝔈` of `Q`-expansions of
[II, Lemma 4.15] (`QExpFamilyStmt`):

* `RunMinus.selRun_minus`: every output graph that is not a `Q`-graph has, if `⊖` is not
  identified with an internal atom by dotted edges (`Graph.Unpinned`), a red solid edge
  `Ḡ_{u⊖}` whose first atom `u` is internal or identified with an internal atom; and some red
  solid, diffusive or dotted edge has an end at `⊖`.
* `RunMinus.selRun_minus_atExt`: every output graph has a red solid, diffusive or dotted edge at
  `⊖`, and the red solid edge `Ḡ_{u⊖}` above when it has an internal atom.

The red solid edge at an unpinned `⊖` is the column index `𝔟₂` of `Ḡ` carried along the run. It
holds on the inputs, and every step keeps it: the atom map of every step fixes `⊗`, `⊕`, `⊖`,
sends internal atoms to internal atoms and keeps every pair of atoms joined by dotted edges joined,
so that an atom identified with an internal atom stays identified and an unpinned `⊖` of a term
is unpinned in the graph. The local expansions of [II, Defs 4.3–4.6] keep, move or split the edge
`Ḡ_{u⊖}` into edges `Ḡ_{v⊖}` with `v` internal; `O_dot` ([II, Def 4.2]) maps it by its atom map
unless `u` and `⊖` fall in one block; the substitution of Steps 2–3 keeps it in the host graph,
since the `t`-variable of [II, (4.14)] has its red solid edge at a new atom; a `Q`-expansion of
Step 3 does not lower the number of red solid edges between the internal and the external
molecules ((F6) of `QExpFamilyStmt`, [II, Lemma 6.5 (4)]), and by the charge pattern of the block
normal form such an edge ends at `⊖` when `⊖` is unpinned.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private Local_stripC Local_Dec Local_DecT Local_GM Local_MovR Local_PathOK Local_NewOK
  Local_f2_left Local_mem_liftCs Local_eraseIdxs2_perm Local_splitRegular_dec Local_liftA_zero
  Local_liftCs_zero Local_comp_proj_zero Local_rd Local_SameR Local_oW2_decT Local_decT_conj
  Local_conj_conj_comps Local_conj_labelFree Local_good_at Local_multiEHat_decT Local_ggPos_res
  Local_conj_out Local_GM_conj Local_sw_sw_comps Local_sw_labelFree Local_sw_out Local_decT_sw
  Local_GM_sw Local_mergeT_spec Local_MergeSpec Local_mergeComp Local_mrep Local_mrep_iff
  Local_merge_sameBlock Local_dotChoice_comps Local_kept Local_added Local_xonly
  from RBM8D.GlobalExp.Local
open private TerminationC_invB TerminationC_out_a from RBM8D.GlobalExp.TerminationC
open private TerminationC2_Hyp TerminationC2_Good TerminationC2_key TerminationC2_inputs
  TerminationC2_tSubst_runKinds TerminationC2_ri_lf TerminationC2_h2_invRun
  TerminationC2_runKinds_of_tKinds from RBM8D.GlobalExp.TerminationC2
open private h2Rec_struct from RBM8D.TExp.Second
open private RunCompare_def63_leaf RunCompare_q0_out
  from RBM8D.GlobalExp.RunCompare

/-! ## Pinned atoms -/

section Pinned

variable {n m : ℕ}

/-- The third clause of `Graph.AtExternals`: a red solid, diffusive or dotted edge has an end at
`⊖`. -/
private abbrev RunMinus_S2 (Γ : Graph 3 n) : Prop :=
  Γ.comps.any (fun c => (c.kind == .G .minus || c.kind.isDiffusive || c.kind == .dot) &&
    (c.x == .inl 2 || c.y == .inl 2)) = true

/-- The red solid edge at `⊖`: if `⊖` is unpinned, some red solid edge `Ḡ_{u⊖}` has a first
atom `u` that is not unpinned. -/
private def RunMinus_I (Γ : Graph 3 n) : Prop :=
  Γ.Unpinned (.inl 2) → ∃ c ∈ Γ.comps, c.kind = .G .minus ∧ c.y = .inl 2 ∧ ¬ Γ.Unpinned c.x

/-- An internal atom is not unpinned. -/
private theorem RunMinus_not_unp_inr (Γ : Graph 3 n) (i : Fin n) : ¬ Γ.Unpinned (.inr i) :=
  fun h => by simp [Graph.Unpinned] at h

private theorem RunMinus_not_unp_right {Γ : Graph 3 n} {u : Atom 3 n} (hu : u.isRight = true) :
    ¬ Γ.Unpinned u := by
  cases u with
  | inl a => simp at hu
  | inr i => exact RunMinus_not_unp_inr Γ i

/-- An atom that is not unpinned is internal or in a block with an internal atom. -/
private theorem RunMinus_pinned {Γ : Graph 3 n} {u : Atom 3 n} (h : ¬ Γ.Unpinned u) :
    u.isRight = true ∨ ∃ b : Fin n, Γ.SameBlock u (.inr b) := by
  cases u with
  | inr i => exact Or.inl rfl
  | inl a =>
    right
    by_contra hb
    exact h ⟨rfl, fun b hb' => hb ⟨b, hb'⟩⟩

/-- A dotted edge joins two atoms of one block. -/
private theorem RunMinus_dot_same {Γ : Graph 3 n} {c : Comp (Atom 3 n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : Γ.SameBlock c.x c.y := by
  by_cases he : c.x = c.y
  · rw [he]
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by
      simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
      exact ⟨he, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩)

/-- Atoms of one block go to atoms of one block under a map of the atoms that keeps the two ends
of every dotted edge in one block. -/
private theorem RunMinus_block_map {Γ : Graph 3 n} {Γ' : Graph 3 m} {f : Atom 3 n → Atom 3 m}
    (hD : ∀ c ∈ Γ.comps, c.kind = .dot → Γ'.SameBlock (f c.x) (f c.y)) {u v : Atom 3 n}
    (h : Γ.SameBlock u v) : Γ'.SameBlock (f u) (f v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab _ ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩
    · exact hD c hc hk
    · exact (hD c hc hk).symm

/-- **A pinned atom stays pinned** under a map of the atoms that sends internal atoms to internal
atoms and keeps the two ends of every dotted edge in one block. -/
private theorem RunMinus_pin_map {Γ : Graph 3 n} {Γ' : Graph 3 m} {f : Atom 3 n → Atom 3 m}
    (hfr : ∀ i : Fin n, (f (.inr i)).isRight = true)
    (hD : ∀ c ∈ Γ.comps, c.kind = .dot → Γ'.SameBlock (f c.x) (f c.y)) {u : Atom 3 n}
    (h : ¬ Γ.Unpinned u) : ¬ Γ'.Unpinned (f u) := by
  rcases RunMinus_pinned h with hu | ⟨b, hb⟩
  · cases u with
    | inl a => simp at hu
    | inr i => exact RunMinus_not_unp_right (hfr i)
  · intro hu'
    have h' := RunMinus_block_map hD hb
    have hr := hfr b
    generalize f (.inr b) = w at h' hr
    cases w with
    | inl a => simp at hr
    | inr b' => exact hu'.2 b' h'

/-- **The red solid edge at `⊖` along a map of the atoms**: if the map fixes `⊖`, sends internal
atoms to internal atoms and keeps the two ends of every dotted edge in one block, and every red
solid edge `Ḡ_{u⊖}` with `u` pinned of a graph with `⊖` unpinned has a red solid edge at `⊖` in
the image whose first atom is the image of `u` or internal, the property passes to the image. -/
private theorem RunMinus_I_of {Γ : Graph 3 n} {Γ' : Graph 3 m} {f : Atom 3 n → Atom 3 m}
    (hf2 : f (.inl 2) = .inl 2) (hfr : ∀ i : Fin n, (f (.inr i)).isRight = true)
    (hD : ∀ c ∈ Γ.comps, c.kind = .dot → Γ'.SameBlock (f c.x) (f c.y))
    (hE : ∀ c ∈ Γ.comps, c.kind = .G .minus → c.y = .inl 2 → ¬ Γ.Unpinned c.x →
      Γ.Unpinned (.inl 2) → Γ'.Unpinned (.inl 2) →
      ∃ c' ∈ Γ'.comps, c'.kind = .G .minus ∧ c'.y = .inl 2 ∧
        ((∃ v, ¬ Γ.Unpinned v ∧ c'.x = f v) ∨ c'.x.isRight = true))
    (h : RunMinus_I Γ) : RunMinus_I Γ' := by
  intro hu'
  have hu : Γ.Unpinned (.inl 2) := by
    by_contra hp
    have := RunMinus_pin_map hfr hD hp
    rw [hf2] at this
    exact this hu'
  obtain ⟨c, hc, hk, hy, hx⟩ := h hu
  obtain ⟨c', hc', hk', hy', hx'⟩ := hE c hc hk hy hx hu hu'
  refine ⟨c', hc', hk', hy', ?_⟩
  rcases hx' with ⟨v, hv, e⟩ | e
  · rw [e]
    exact RunMinus_pin_map hfr hD hv
  · exact RunMinus_not_unp_right e

/-- The property passes to a graph that contains every component other than a `×`-dotted edge. -/
private theorem RunMinus_I_sub {Γ Γ' : Graph 3 n}
    (hs : ∀ c ∈ Γ.comps, c.kind ≠ .xdot → c ∈ Γ'.comps) (h : RunMinus_I Γ) : RunMinus_I Γ' := by
  refine RunMinus_I_of (f := id) rfl (fun _ => rfl)
    (fun c hc hk => RunMinus_dot_same (hs c hc (by rw [hk]; simp)) hk)
    (fun c hc hk hy hx _ _ => ⟨c, hs c hc (by rw [hk]; simp), hk, hy, Or.inl ⟨c.x, hx, rfl⟩⟩) h

/-- In a graph without dotted edges every external atom is unpinned. -/
private theorem RunMinus_unp_dotFree {Γ : Graph 3 n} (h : Γ.DotFree) (a : Fin 3) :
    Γ.Unpinned (.inl a) := by
  refine ⟨rfl, fun b hb => ?_⟩
  obtain ⟨w⟩ := hb
  cases w with
  | cons hab _ =>
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with ⟨c, hc, hk, -⟩ | ⟨c, hc, hk, -⟩ <;> exact h c hc hk

/-- The property gives the third clause of `Graph.AtExternals`: the red solid edge at an unpinned
`⊖`, the first dotted edge of a path from `⊖` to an internal atom at a pinned `⊖`. -/
private theorem RunMinus_S2_of {Γ : Graph 3 n} (h : RunMinus_I Γ) : RunMinus_S2 Γ := by
  unfold RunMinus_S2
  rw [List.any_eq_true]
  by_cases hu : Γ.Unpinned (.inl 2)
  · obtain ⟨c, hc, hk, hy, -⟩ := h hu
    exact ⟨c, hc, by simp [hk, hy]⟩
  · rcases RunMinus_pinned hu with hr | ⟨b, hb⟩
    · simp at hr
    obtain ⟨w⟩ := hb
    cases w with
    | cons hab _ =>
      simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
      rcases hab.2 with ⟨c, hc, hk, hx, -⟩ | ⟨c, hc, hk, -, hy⟩
      · exact ⟨c, hc, by simp [hk, hx]⟩
      · exact ⟨c, hc, by simp [hk, hy]⟩

end Pinned

/-! ## The steps with one output graph, `O_dot` and the substitution -/

section Simple

variable {n : ℕ}

private theorem RunMinus_mem_erase {α : Type*} {l : List α} {i : ℕ} {c c₀ : α}
    (h₀ : l[i]? = some c₀) (hc : c ∈ l) (hne : c ≠ c₀) : c ∈ l.eraseIdx i := by
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hc
  refine List.mem_eraseIdx_iff_getElem.2 ⟨j, hj, fun hji => hne ?_, e⟩
  subst hji
  rw [List.getElem?_eq_getElem hj, e] at h₀
  exact Option.some.inj h₀

/-- **The removal of a redundant dotted edge** (`DotNormStep`): the blocks are kept. -/
private theorem RunMinus_I_dropDot {Γ Γ' : Graph 3 n} (hd : DotNormStep Γ Γ')
    (h : RunMinus_I Γ) : RunMinus_I Γ' := by
  obtain ⟨i, c₀, hc₀, hk₀, hb, rfl⟩ := hd
  have key : ∀ c ∈ Γ.comps, c ≠ c₀ → c ∈ Γ.comps.eraseIdx i :=
    fun c hc hne => RunMinus_mem_erase hc₀ hc hne
  refine RunMinus_I_of (f := id) rfl (fun _ => rfl) (fun c hc hk => ?_)
    (fun c hc hk hy hx _ _ => ⟨c, key c hc (by rintro rfl; rw [hk₀] at hk; cases hk), hk, hy,
      Or.inl ⟨c.x, hx, rfl⟩⟩) h
  by_cases e : c = c₀
  · subst e
    exact hb
  · exact RunMinus_dot_same (key c hc e) hk

/-- **A reordering** (`Graph.Reorder`): the red solid edges are mapped by the relabelling and
never turned; the dotted edges are mapped and possibly turned. -/
private theorem RunMinus_I_reorder {Γ Γ' : Graph 3 n} (hr : Γ.Reorder Γ') (h : RunMinus_I Γ) :
    RunMinus_I Γ' := by
  obtain ⟨-, π, cs, hf2, hp⟩ := hr
  have key : ∀ c ∈ Γ.comps, ∃ c' ∈ Γ'.comps, c' = c.map (Sum.map id π) ∨
      ((c.kind = .waved .s ∨ c.kind = .dot ∨ c.kind = .xdot) ∧
        c' = { c.map (Sum.map id π) with x := Sum.map id π c.y, y := Sum.map id π c.x }) := by
    intro c hc
    have hm : c.map (Sum.map id π) ∈ (Γ.relabel π).comps := List.mem_map_of_mem hc
    obtain ⟨c', hc', e⟩ := Local_f2_left hf2 hm
    exact ⟨c', hp.subset hc', e⟩
  refine RunMinus_I_of (f := Sum.map id π) rfl (fun _ => rfl) (fun c hc hk => ?_)
    (fun c hc hk hy hx _ _ => ?_) h
  · obtain ⟨c', hc', e | ⟨-, e⟩⟩ := key c hc
    · subst e
      exact RunMinus_dot_same hc' hk
    · subst e
      exact (RunMinus_dot_same hc' hk).symm
  · obtain ⟨c', hc', e | ⟨hk', -⟩⟩ := key c hc
    · subst e
      exact ⟨_, hc', hk, by simp [Comp.map, hy], Or.inl ⟨c.x, hx, rfl⟩⟩
    · rw [hk] at hk'
      rcases hk' with h' | h' | h' <;> cases h'

/-- **`O_merge`**: the atom map keeps the blocks; a red solid edge `Ḡ_{u⊖}` with `u` pinned and
`⊖` unpinned has its two ends in two blocks, so it is mapped to a red solid edge. -/
private theorem RunMinus_I_merge {D : Graph 3 n} {t : Tracked 3 n} (hm : D.mergeT = some t)
    (h : RunMinus_I D) : RunMinus_I t.g := by
  obtain ⟨hcomps, -, -, hinl, -, ⟨g, hg, -⟩, -⟩ := Local_mergeT_spec hm
  refine RunMinus_I_of (hinl 2) (fun i => by rw [hg i]; rfl)
    (fun c hc hk => (Local_merge_sameBlock hm c.x c.y).2 (RunMinus_dot_same hc hk))
    (fun c hc hk hy hx hu _ => ?_) h
  have hrep : Local_mrep D c.x ≠ Local_mrep D c.y := by
    intro e
    have hb := (Local_mrep_iff D c.x c.y).1 e
    rw [hy] at hb
    rcases RunMinus_pinned hx with hr | ⟨b, hb'⟩
    · rcases hcx : c.x with a | b
      · rw [hcx] at hr; simp at hr
      · rw [hcx] at hb; exact hu.2 b hb.symm
    · exact hu.2 b (hb.symm.trans hb')
  refine ⟨c.map t.f, ?_, by simp [Comp.map, hk], by simp [Comp.map, hy, hinl],
    Or.inl ⟨c.x, hx, rfl⟩⟩
  rw [hcomps]
  refine List.mem_filterMap.2 ⟨c, hc, ?_⟩
  unfold Local_mergeComp
  simp [hk, Kind.isSolid, hrep]

/-- **`O_dot`** ([II, Def 4.2]): the atom map of every term sends internal atoms to internal
atoms, and the property passes to every term. -/
private theorem RunMinus_oDotT {Γ : Graph 3 n} {t : Tracked 3 n} (ht : t ∈ oDotT Γ) :
    (∀ i : Fin n, (t.f (.inr i)).isRight = true) ∧ (RunMinus_I Γ → RunMinus_I t.g) := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact ⟨fun _ => rfl, id⟩
  obtain ⟨-, -, -, -, -, ⟨g, hg, -⟩, -⟩ := Local_mergeT_spec hm
  refine ⟨fun i => by rw [hg i]; rfl, fun h => RunMinus_I_merge hm (RunMinus_I_sub ?_ h)⟩
  intro c hc hk
  rw [Local_dotChoice_comps]
  refine List.mem_append_left _ (List.mem_filter.2 ⟨hc, ?_⟩)
  simp [hk]

/-- **The substitution of Steps 2–3** ([II, (4.14)–(4.15)]) at a host graph
`H.glue x y₁ y₂ (tVar true)` without dotted edges: the red solid edge at `⊖` of the host has an
internal first atom and lies in `H` (the red solid edge of the `t`-variable ends at the new atom
`α`), so every substituted graph `H.glue x y₁ y₂ 𝒢` has it. -/
private theorem RunMinus_I_glue {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}
    (hdf : (H.glue x y₁ y₂ (tVar true)).DotFree) (h : RunMinus_I (H.glue x y₁ y₂ (tVar true)))
    (𝒢 : Graph 3 n') : RunMinus_I (H.glue x y₁ y₂ 𝒢) := by
  intro _
  obtain ⟨c, hc, hk, hy, hx⟩ := h (RunMinus_unp_dotFree hdf 2)
  have hxr : c.x.isRight = true := by
    rcases hcx : c.x with a | b
    · rw [hcx] at hx
      exact absurd (RunMinus_unp_dotFree hdf a) hx
    · rfl
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    have hy₀ : c₀.y = .inl 2 := by
      have e : liftA 1 c₀.y = (.inl 2 : Atom 3 (m + 1)) := hy
      rcases hcy : c₀.y with a | b
      · rw [hcy] at e
        exact congrArg Sum.inl (Sum.inl.inj e)
      · rw [hcy] at e
        cases e
    have hx₀ : c₀.x.isRight = true := by
      have e : (liftA 1 c₀.x : Atom 3 (m + 1)).isRight = true := hxr
      rcases hcx : c₀.x with a | b <;> rw [hcx] at e <;> simp [liftA] at e ⊢
    refine ⟨c₀.map (liftA n'), List.mem_append_left _ (List.mem_map_of_mem hc₀), hk, ?_,
      RunMinus_not_unp_right ?_⟩
    · simp [Comp.map, hy₀, liftA]
    · rcases hcx : c₀.x with a | b
      · rw [hcx] at hx₀; simp at hx₀
      · simp [Comp.map, hcx, liftA]
  · exfalso
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    have hall : ∀ d ∈ (tVar true).comps, d.kind = .G .minus → d.y.isRight = true := by decide
    have hr := hall c₀ hc₀ hk
    rcases hcy : c₀.y with a | j
    · rw [hcy] at hr; simp at hr
    · have e := hy
      simp [Comp.map, hcy, glueAtom, newA] at e

end Simple

/-! ## The charge pattern of the block normal form -/

section Flat

variable {n : ℕ}

private theorem RunMinus_flat_unp {Γ : Graph 3 n} {u : Atom 3 n} (h : Γ.Unpinned u) :
    Γ.flatAtom u = u := by
  rcases SelRunIso_flatAtom_spec Γ u with e | ⟨b, -, hb⟩
  · exact e
  · exact absurd hb (h.2 b)

/-- The atom of the block normal form of an atom that is not unpinned is internal. -/
private theorem RunMinus_flat_pin {Γ : Graph 3 n} {u : Atom 3 n} (h : ¬ Γ.Unpinned u) :
    ∃ b : Fin n, Γ.flatAtom u = .inr b := by
  rcases e : Γ.flatAtom u with a | b
  · exact absurd (SelRunIso_flatAtom_inl Γ e).2 h
  · exact ⟨b, rfl⟩

/-- The block normal form of a component other than a dotted edge. -/
private theorem RunMinus_flatComp {Γ : Graph 3 n} {c : Comp (Atom 3 n)} (hk : c.kind ≠ .dot) :
    Γ.flatComp c = { c with x := Γ.flatAtom c.x, y := Γ.flatAtom c.y } := by
  unfold Graph.flatComp
  simp [hk]

/-- **The first atom of a random component is not unpinned** in a graph with the charge pattern of
the block normal form (`Graph.ColourInvB`). -/
private theorem RunMinus_randX {Γ : Graph 3 n} (hC : Γ.ColourInvB) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hr : c.kind.isRandom = true) : ¬ Γ.Unpinned c.x := by
  intro hu
  have hne : c.kind ≠ .dot := by intro e; rw [e] at hr; cases hr
  have hm : Γ.flatComp c ∈ Γ.blockNorm.comps := List.mem_map_of_mem hc
  have hk : (Γ.flatComp c).kind.isRandom = true := by rw [Graph.flatComp_kind]; exact hr
  have h1 := ((hC _ hm).1 hk).1
  rw [RunMinus_flatComp hne] at h1
  simp only at h1
  rw [RunMinus_flat_unp hu] at h1
  have h2 := hu.1
  rcases hcx : c.x with a | b
  · rw [hcx] at h1; simp at h1
  · rw [hcx] at h2; simp at h2

end Flat

/-! ## The local expansions -/

section Track

variable {n : ℕ}

/-- **The red solid edge at `⊖` in a term of `Local_Dec`** ([II, Defs 4.3–4.6]): a kept component
is lifted; a replaced red solid edge keeps its kind and its external end `⊖`; the second factor of
a path `-∂_{h_{uv}} Ḡ_{w⊖}` is `Ḡ_{v⊖}` with `v` internal; the removed components are weights and
the new components join internal atoms. The dotted edges are kept. -/
private theorem RunMinus_dec {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    (hd : Local_Dec Γ x j Γ') (h : RunMinus_I Γ) : RunMinus_I Γ' := by
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, -, -⟩ := hd
  have back : ∀ d ∈ liftCs j K ++ D' ++ P' ++ N, ∃ c'' ∈ Γ'.comps,
      c''.kind = d.kind ∧ c''.x = d.x ∧ c''.y = d.y := by
    intro d hd
    obtain ⟨c'', hc'', e⟩ := List.mem_map.1 (h2.subset hd)
    exact ⟨c'', hc'', by rw [← e]; rfl, by rw [← e]; rfl, by rw [← e]; rfl⟩
  have fwd : ∀ c ∈ Γ.comps, Local_stripC c ∈ K ++ D ++ P ++ R :=
    fun c hc => h1.subset (List.mem_map_of_mem hc)
  have kept : ∀ c ∈ Γ.comps, Local_stripC c ∈ K → ∃ c'' ∈ Γ'.comps,
      c''.kind = c.kind ∧ c''.x = liftA j c.x ∧ c''.y = liftA j c.y := by
    intro c _ hK
    obtain ⟨c'', hc'', a, b, d⟩ := back ((Local_stripC c).map (liftA j))
      (by simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl
        (Local_mem_liftCs.2 ⟨_, hK, rfl⟩))))
    exact ⟨c'', hc'', a, b, d⟩
  have nonrand : ∀ c ∈ Γ.comps, c.kind.isRandom = false → Local_stripC c ∈ K := by
    intro c hc hr
    have hm := fwd c hc
    simp only [List.mem_append] at hm
    rcases hm with ((hm | hm) | hm) | hm
    · exact hm
    · obtain ⟨_, _, hmov⟩ := Local_f2_left h3 hm
      have : c.kind.isRandom = true := hmov.2.1
      rw [hr] at this; cases this
    · exfalso
      rcases h4 with ⟨rfl, -⟩ | ⟨c₀, ch, u, v, rfl, hk, -⟩
      · simp at hm
      · rw [List.mem_singleton] at hm
        have : c.kind = c₀.kind := by have e := congrArg Comp.kind hm; exact e
        rcases hk with hk | hk | hk <;> rw [this, hk] at hr <;> cases hr
    · have := h5 _ hm
      have hw : c.kind.isWeight = true := this
      cases hk : c.kind <;> simp_all [Kind.isWeight, Kind.isRandom]
  refine RunMinus_I_of (f := liftA j) rfl (fun _ => rfl) (fun c hc hk => ?_)
    (fun c hc hk hy hx _ _ => ?_) h
  · obtain ⟨c'', hc'', a, b, d⟩ := kept c hc (nonrand c hc (by rw [hk]; rfl))
    have := RunMinus_dot_same hc'' (by rw [a, hk])
    rwa [b, d] at this
  · have hm := fwd c hc
    simp only [List.mem_append] at hm
    rcases hm with ((hm | hm) | hm) | hm
    · obtain ⟨c'', hc'', a, b, d⟩ := kept c hc hm
      exact ⟨c'', hc'', by rw [a, hk], by rw [d, hy]; rfl, Or.inl ⟨c.x, hx, b⟩⟩
    · obtain ⟨d', hd', hmov⟩ := Local_f2_left h3 hm
      obtain ⟨hk', -, hx', hy', -⟩ := hmov
      obtain ⟨c'', hc'', a, b, d⟩ := back d' (by simp [hd'])
      have hk'' : d'.kind = .G .minus := by
        rcases hk' with e | ⟨e, -⟩
        · rw [e]; exact hk
        · have : c.kind.isWeight = true := e
          rw [hk] at this; cases this
      refine ⟨c'', hc'', by rw [a, hk''], ?_, ?_⟩
      · rcases hy' with e | ⟨e, -⟩
        · rw [d, e]; exact congrArg (liftA j) hy
        · have : c.y.isRight = true := e
          rw [hy] at this; cases this
      · rcases hx' with e | ⟨-, e⟩
        · exact Or.inl ⟨c.x, hx, by rw [b, e]; rfl⟩
        · exact Or.inr (by rw [b]; exact e)
    · rcases h4 with ⟨rfl, -⟩ | ⟨c₀, ch, u, v, rfl, hk0, -, hv, -, -, hp⟩
      · simp at hm
      rw [List.mem_singleton] at hm
      have hkc : c₀.kind = .G .minus := by rw [← hm]; exact hk
      have hch : ch = .minus := by
        rcases hk0 with e | e | e <;> rw [hkc] at e <;> cases e
        rfl
      subst hch
      have hyc : c₀.y = .inl 2 := by rw [← hm]; exact hy
      have hne : v ≠ (.inl 2 : Atom 3 (n + j)) := by
        intro e; rw [e] at hv; simp at hv
      have hsol : solidC .minus v (liftA j (if c₀.kind.isWeight then c₀.x else c₀.y)) =
          mkC (.G .minus) v (.inl 2) := by
        rw [hkc]
        simp [Kind.isWeight, hyc, liftA, solidC, hne]
      have hmP : mkC (.G .minus) v (.inl 2) ∈ P' := by
        rw [← hsol]
        exact hp.symm.subset (by simp)
      have hmem : mkC (.G .minus) v (.inl 2) ∈ liftCs j K ++ D' ++ P' ++ N := by simp [hmP]
      obtain ⟨c'', hc'', a, b, d⟩ := back _ hmem
      exact ⟨c'', hc'', a, d, Or.inr (by rw [b]; exact hv)⟩
    · have : c.kind.isWeight = true := by have e := h5 _ hm; exact e
      rw [hk] at this; cases this

/-- A term of an expansion of `Γ`: its atom map sends internal atoms to internal atoms, and the red
solid edge at `⊖` passes from `Γ` to the term. -/
private def RunMinus_Track (Γ : Graph 3 n) (t : Tracked 3 n) : Prop :=
  (∀ i : Fin n, (t.f (.inr i)).isRight = true) ∧ (RunMinus_I Γ → RunMinus_I t.g)

private theorem RunMinus_track_self (Γ : Graph 3 n) : RunMinus_Track Γ (Tracked.self Γ) :=
  ⟨fun _ => rfl, id⟩

private theorem RunMinus_track_bind {Γ : Graph 3 n} {E : TExpansion 3 n}
    {O : ∀ {n' : ℕ}, (Atom 3 n → Atom 3 n') → Graph 3 n' → TExpansion 3 n'}
    (hE : ∀ t ∈ E, RunMinus_Track Γ t)
    (hO : ∀ t ∈ E, ∀ s ∈ O t.f t.g, RunMinus_Track t.g s) :
    ∀ u ∈ E.bind O, RunMinus_Track Γ u := by
  intro u hu
  unfold TExpansion.bind at hu
  obtain ⟨t, ht, hu⟩ := List.mem_flatMap.1 hu
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
  obtain ⟨a1, a2⟩ := hE t ht
  obtain ⟨b1, b2⟩ := hO t ht s hs
  refine ⟨fun i => ?_, fun h => b2 (a2 h)⟩
  change (s.f (t.f (.inr i))).isRight = true
  have := a1 i
  generalize t.f (.inr i) = w at this
  cases w with
  | inl _ => simp at this
  | inr i' => exact b1 i'

private theorem RunMinus_track_oDot (Γ : Graph 3 n) : ∀ t ∈ oDotT Γ, RunMinus_Track Γ t :=
  fun _ ht => RunMinus_oDotT ht

private theorem RunMinus_dot_after {Γ : Graph 3 n} {E : TExpansion 3 n}
    (hE : ∀ t ∈ E, RunMinus_Track Γ t) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), RunMinus_Track Γ t :=
  RunMinus_track_bind hE fun t _ s hs => RunMinus_track_oDot t.g s hs

private theorem RunMinus_track_dec {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {t : Tracked 3 n}
    (hn : t.nOut = n + j) (hf : ∀ u, t.f u = hn ▸ liftA j u) (hd : Local_Dec Γ x j (hn ▸ t.g)) :
    RunMinus_Track Γ t := by
  obtain ⟨tn, tg, tf⟩ := t
  simp only at hn
  subst hn
  simp only at hf hd
  have e : tf = liftA j := funext hf
  subst e
  exact ⟨fun _ => rfl, RunMinus_dec hd⟩

private theorem RunMinus_track_decT {Δ : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Local_DecT Δ x t) : RunMinus_Track Δ t := by
  obtain ⟨j, hn, hf, hd, -⟩ := h
  exact RunMinus_track_dec hn hf hd

/-- **The main term of the `GG` expansion**: `Ḡ_{u x} Ḡ_{x v}` is replaced by `Ḡ_{u v}`. If the
removed edge into `⊖` is `Ḡ_{x⊖}`, the new edge is `Ḡ_{u⊖}`, and `u` is not unpinned by the charge
pattern of the block normal form. The dotted edges are kept. -/
private theorem RunMinus_track_GM {Δ : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Local_GM Δ x t) (hC : Δ.ColourInvB) : RunMinus_Track Δ t := by
  obtain ⟨Γ', rfl, i, j, hi, hj, ch, w, wv, hij, hki, hkj, -, hyj, -, hperm, -⟩ := h
  have hΔ := Local_eraseIdxs2_perm Δ.comps i j hi hj hij
  have back : ∀ d ∈ (eraseIdxs [i, j] Δ.comps).map Local_stripC ++
      [solidC ch Δ.comps[j].x Δ.comps[i].y, mkC (.waved wv) (.inr x) (.inr w)],
      ∃ c'' ∈ Γ'.comps, c''.kind = d.kind ∧ c''.x = d.x ∧ c''.y = d.y := by
    intro d hd
    obtain ⟨c'', hc'', e⟩ := List.mem_map.1 (hperm.symm.subset hd)
    exact ⟨c'', hc'', by rw [← e]; rfl, by rw [← e]; rfl, by rw [← e]; rfl⟩
  have sort : ∀ c ∈ Δ.comps, c ∈ eraseIdxs [i, j] Δ.comps ∨ c = Δ.comps[i] ∨ c = Δ.comps[j] := by
    intro c hc
    have := hΔ.subset hc
    simpa using this
  have kept : ∀ c ∈ eraseIdxs [i, j] Δ.comps, ∃ c'' ∈ Γ'.comps,
      c''.kind = c.kind ∧ c''.x = c.x ∧ c''.y = c.y :=
    fun c hc => back (Local_stripC c) (List.mem_append_left _ (List.mem_map_of_mem hc))
  refine ⟨fun _ => rfl, RunMinus_I_of (f := id) rfl (fun _ => rfl) (fun c hc hk => ?_)
    (fun c hc hk hy hx hu _ => ?_)⟩
  · rcases sort c hc with hc' | rfl | rfl
    · obtain ⟨c'', hc'', a, b, d⟩ := kept c hc'
      have := RunMinus_dot_same hc'' (by rw [a, hk])
      rwa [b, d] at this
    · rw [hki] at hk; cases hk
    · rw [hkj] at hk; cases hk
  · rcases sort c hc with hc' | rfl | rfl
    · obtain ⟨c'', hc'', a, b, d⟩ := kept c hc'
      exact ⟨c'', hc'', by rw [a, hk], by rw [d, hy], Or.inl ⟨c.x, hx, b⟩⟩
    · have hch : ch = .minus := by rw [hki] at hk; cases hk; rfl
      subst hch
      have hpin : ¬ Δ.Unpinned Δ.comps[j].x :=
        RunMinus_randX hC (List.getElem_mem hj) (by rw [hkj]; rfl)
      have hne : Δ.comps[j].x ≠ Δ.comps[i].y := by
        rw [hy]; intro e; rw [e] at hpin; exact hpin hu
      have hsol : solidC .minus Δ.comps[j].x Δ.comps[i].y =
          mkC (.G .minus) Δ.comps[j].x (.inl 2) := by
        unfold solidC
        rw [hy] at hne ⊢
        simp [hne]
      obtain ⟨c'', hc'', a, b, d⟩ := back (solidC .minus Δ.comps[j].x Δ.comps[i].y)
        (List.mem_append_right _ List.mem_cons_self)
      rw [hsol] at a b d
      exact ⟨c'', hc'', a, d, Or.inl ⟨_, hpin, b⟩⟩
    · rw [hyj] at hy; cases hy

private theorem RunMinus_lf_of_plain {Γ : Graph 3 n}
    (h : ¬ (!(Γ.comps.all Comp.isPlainB)) = true) : Γ.LabelFree := by
  intro c hc
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at h
  have := h c hc
  unfold Comp.isPlainB at this
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact this.1.2

private theorem RunMinus_oWeight1 {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeight1T (.inr x) Γ, RunMinus_Track Γ t := by
  intro t ht
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := Local_splitRegular_dec (.inr x) Γ.comps p hp
  refine RunMinus_track_dec (j := 0) (x := x) rfl (fun u => (Local_liftA_zero u).symm) ?_
  refine ⟨K.map Local_stripC, D.map Local_stripC, [], R.map Local_stripC,
    D'.map Local_stripC, [], [], ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩, ?_, by simp, fun i => i.elim0⟩
  · have := h1.map Local_stripC
    simpa [List.map_append] using this
  · rw [Local_liftCs_zero]
    have := (h2.map Local_stripC).symm
    simpa [List.map_append] using this
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine h3.imp fun d d' ⟨ch, hk, hx, hl, hd'⟩ => ?_
    subst hd'
    refine ⟨Or.inr ⟨by simp [Local_stripC, hk, Kind.isWeight], by simp [Local_stripC,
      Kind.isWeight]⟩, by simp [Local_stripC, hk, Kind.isRandom],
      Or.inl (Local_liftA_zero _).symm, Or.inl (Local_liftA_zero _).symm, ?_⟩
    unfold Local_SameR
    rw [Local_comp_proj_zero]
    left
    refine ⟨?_, ?_⟩ <;> simp [Local_rd, Local_stripC, hk, Kind.mclass]
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    obtain ⟨⟨ch, hk⟩, -, -⟩ := h4 c₀ hc₀
    simp [Local_stripC, hk, Kind.isWeight]

private theorem RunMinus_oWeight2 {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeight2T (.inr x) Γ, RunMinus_Track Γ t := by
  intro t ht
  unfold oWeight2T at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunMinus_track_self Γ
  have hlf := RunMinus_lf_of_plain hp
  split at ht
  · rename_i E hE
    exact RunMinus_track_decT (Local_oW2_decT hlf x hE t ht)
  · split at ht
    · rename_i E _ hE
      unfold TExpansion.conj at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      exact RunMinus_track_decT (Local_decT_conj (Local_conj_conj_comps Γ)
        (Local_oW2_decT (Local_conj_labelFree hlf) x hE t₀ ht₀))
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunMinus_track_self Γ

private theorem RunMinus_oWeight {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeightT (.inr x) Γ, RunMinus_Track Γ t := by
  intro t ht
  unfold oWeightT at ht
  split_ifs at ht with hw
  · have h1 : ∀ t ∈ oWeight1T (.inr x) Γ, RunMinus_Track Γ t := RunMinus_oWeight1 x
    have h2 : ∀ t ∈ (oWeight1T (.inr x) Γ).bind (fun f g => oWeight2T (f (.inr x)) g),
        RunMinus_Track Γ t := by
      refine RunMinus_track_bind h1 fun t ht s hs => ?_
      exact Local_good_at ((h1 t ht).1 x) (fun u => ∀ s ∈ oWeight2T u t.g, RunMinus_Track t.g s)
        (fun x' => RunMinus_oWeight2 x') s hs
    have h3 : ∀ t ∈ ((oWeight1T (.inr x) Γ).bind (fun f g => oWeight2T (f (.inr x)) g)).bind
        (fun _ g => oDotT g), RunMinus_Track Γ t := RunMinus_dot_after h2
    refine RunMinus_track_bind h3 (fun t ht s hs => ?_) t ht
    exact Local_good_at ((h3 t ht).1 x) (fun u => ∀ s ∈ oWeight1T u t.g, RunMinus_Track t.g s)
      (fun x' => RunMinus_oWeight1 x') s hs
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunMinus_track_self Γ

private theorem RunMinus_oMultiE {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oMultiET (.inr x) Γ, RunMinus_Track Γ t := by
  intro t ht
  unfold oMultiET at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunMinus_track_self Γ
  have hlf := RunMinus_lf_of_plain hp
  split at ht
  · rename_i E hE
    exact RunMinus_dot_after
      (fun t ht => RunMinus_track_decT (Local_multiEHat_decT hlf x hE t ht)) t ht
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunMinus_track_self Γ

private theorem RunMinus_oGGbar {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oGGbarT (.inr x) Γ, RunMinus_Track Γ t := by
  intro t ht
  unfold oGGbarT at ht
  dsimp only at ht
  split_ifs at ht
  · exact RunMinus_oMultiE x t ht
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunMinus_track_self Γ

private theorem RunMinus_oGG {Γ : Graph 3 n} (x : Fin n) (hC : Γ.ColourInvB)
    (hout : Γ.GGOutInt (.inr x)) : ∀ t ∈ oGGT (.inr x) Γ, RunMinus_Track Γ t := by
  intro t ht
  unfold oGGT at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunMinus_track_self Γ
  have hlf := RunMinus_lf_of_plain hp
  split at ht
  · rename_i E hE
    refine RunMinus_dot_after (fun t ht => ?_) t ht
    rcases Local_ggPos_res hlf x hout hE t ht with h | h
    · exact RunMinus_track_decT h
    · exact RunMinus_track_GM h hC
  · split at ht
    · rename_i E _ hE
      refine RunMinus_dot_after (fun t ht => ?_) t ht
      unfold TExpansion.conj at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      have hc := Local_conj_conj_comps Γ
      rcases Local_ggPos_res (Local_conj_labelFree hlf) x (Local_conj_out hout) hE t₀ ht₀ with
        h | h
      · exact RunMinus_track_decT (Local_decT_conj hc h)
      · exact RunMinus_track_GM (Local_GM_conj hc h) hC
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunMinus_track_self Γ

private theorem RunMinus_oGGT {Γ : Graph 3 n} (x : Fin n) (hC : Γ.ColourInvB)
    (hin : Γ.GGInInt (.inr x)) : ∀ t ∈ oGGTT (.inr x) Γ, RunMinus_Track Γ t := by
  intro t ht
  unfold oGGTT at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunMinus_track_self Γ
  have hlf := RunMinus_lf_of_plain hp
  have hs := Local_sw_sw_comps Γ
  have hlfs := Local_sw_labelFree hlf
  have houts := Local_sw_out hin
  split at ht
  · rename_i E hE
    refine RunMinus_dot_after (fun t ht => ?_) t ht
    unfold TExpansion.swapSolid at ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    rcases Local_ggPos_res hlfs x houts hE t₀ ht₀ with h | h
    · exact RunMinus_track_decT (Local_decT_sw hs h)
    · exact RunMinus_track_GM (Local_GM_sw hs h) hC
  · split at ht
    · rename_i E _ hE
      refine RunMinus_dot_after (fun t ht => ?_) t ht
      unfold TExpansion.swapSolid TExpansion.conj at ht
      rw [List.map_map] at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      have hc := Local_conj_conj_comps Γ.swapSolid
      rcases Local_ggPos_res (Local_conj_labelFree hlfs) x (Local_conj_out houts) hE t₀ ht₀ with
        h | h
      · exact RunMinus_track_decT (Local_decT_sw hs (Local_decT_conj hc h))
      · exact RunMinus_track_GM (Local_GM_sw hs (Local_GM_conj hc h)) hC
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunMinus_track_self Γ

/-- **The red solid edge at `⊖` along the local expansions** ([II, Defs 4.3–4.6], in the form of
`Graph.LocSide`), on a graph with the charge pattern of the block normal form. -/
private theorem RunMinus_localOp {Γ : Graph 3 n} (x : Fin n) (o : Fin 5) (hC : Γ.ColourInvB)
    (hs : Γ.LocSide o (.inr x)) : ∀ t ∈ localOp' o (.inr x) Γ, RunMinus_Track Γ t := by
  obtain ⟨hs2, hs4⟩ := hs
  match o with
  | 0 => exact RunMinus_oWeight x
  | 1 => exact RunMinus_oMultiE x
  | 2 => exact RunMinus_oGG x hC (hs2 rfl rfl)
  | 3 => exact RunMinus_oGGbar x
  | 4 => exact RunMinus_oGGT x hC (hs4 rfl rfl)

end Track

/-! ## The `Q`-expansions: red solid edges between the internal and the external molecules -/

section QExp

variable {n m : ℕ}

private theorem RunMinus_anchor_some {Γ : Graph 3 n} {u : Atom 3 n} {b : Fin n}
    (h : Γ.anchor u = some b) : Γ.SameBlock u (.inr b) := by
  classical
  rw [MolMono_anchor_eq_find] at h
  simpa using List.find?_some h

private theorem RunMinus_mclass_minus {κ : Kind} (h : κ.mclass = some .minus) :
    κ = .G .minus := by
  cases κ with
  | G ch => cases ch <;> simp_all [Kind.mclass]
  | aux j r b => cases b <;> simp_all [Kind.mclass]
  | _ => simp_all [Kind.mclass]

/-- **The red solid edge at `⊖` gives a red solid edge of `Graph.toMG'` between the internal
molecules and `⊖`**: the edge `Ḡ_{u⊖}` itself if `⊖` is unpinned (its first atom is internal in
the block normal form), the edge from the molecule of the block of `⊖` to `⊖` (class
`pinClass 2`) if `⊖` is pinned. -/
private theorem RunMinus_red_of_I {Γ : Graph 3 n} (h : RunMinus_I Γ) :
    ∃ e, Γ.toMG'.RedCrosses Γ.toMG'.int e := by
  by_cases hu : Γ.Unpinned (.inl 2)
  · obtain ⟨c, hc, hk, hy, hx⟩ := h hu
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hc
    obtain ⟨b, hb⟩ := RunMinus_flat_pin hx
    have hne : c.kind ≠ .dot := by rw [hk]; simp
    have hfc : Γ.flatComp Γ.comps[i] = { c with x := .inr b, y := .inl 2 } := by
      rw [e, RunMinus_flatComp hne, hb, hy, RunMinus_flat_unp hu]
    obtain ⟨b', hb', -⟩ := MolMono_molRep_inr Γ b
    have hmr : Γ.molRep (.inr b) ≠ Γ.molRep (.inl 2) := by
      rw [hb']; simp [Graph.molRep]
    refine ⟨.inl ⟨i, hi⟩, ?_, ?_, ?_, ?_⟩
    · change (if (Γ.flatComp Γ.comps[i]).kind = .dot ∨ Γ.molRep (Γ.flatComp Γ.comps[i]).x =
          Γ.molRep (Γ.flatComp Γ.comps[i]).y then none
        else (Γ.flatComp Γ.comps[i]).kind.mclass) = some .minus
      rw [hfc]
      simp only [hmr, hk]
      rfl
    · change Γ.toMG'.IsVtx (Γ.molRep (Γ.flatComp Γ.comps[i]).x)
      rw [hfc]
      exact Or.inl (MolMono_molRep_mem_int Γ b)
    · change Γ.toMG'.IsVtx (Γ.molRep (Γ.flatComp Γ.comps[i]).y)
      rw [hfc]
      exact Or.inr ((MolMono_mem_ext Γ _).2 ⟨2, rfl⟩)
    · change (Γ.molRep (Γ.flatComp Γ.comps[i]).x ∈ Γ.toMG'.int ∧
          Γ.molRep (Γ.flatComp Γ.comps[i]).y ∉ Γ.toMG'.int) ∨
        (Γ.molRep (Γ.flatComp Γ.comps[i]).x ∉ Γ.toMG'.int ∧
          Γ.molRep (Γ.flatComp Γ.comps[i]).y ∈ Γ.toMG'.int)
      rw [hfc]
      exact Or.inl ⟨MolMono_molRep_mem_int Γ b, MolMono_inl_not_mem_int Γ 2⟩
  · rcases RunMinus_pinned hu with hr | ⟨b, hb⟩
    · simp at hr
    have ha : Γ.anchor (.inl 2) ≠ none := by
      classical
      intro hn
      rw [MolMono_anchor_eq_find, List.find?_eq_none] at hn
      exact hn b (List.mem_finRange b) (by simpa using hb)
    obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.1 ha
    have hcl : Γ.toMG'.cls (.inr 2) = some (pinClass (2 : Fin 3)) := by
      simp only [Graph.toMG', hb']
    have hen : Γ.toMG'.ends (.inr 2) = (Γ.molRep (.inr b'), .inl 2) := by
      simp only [Graph.toMG', hb']
    refine ⟨.inr 2, ?_, ?_, ?_, ?_⟩
    · rw [hcl]; rfl
    · rw [hen]; exact Or.inl (MolMono_molRep_mem_int Γ b')
    · rw [hen]; exact Or.inr ((MolMono_mem_ext Γ _).2 ⟨(2 : Fin 3), rfl⟩)
    · unfold MGraph.Cut
      rw [hen]
      exact Or.inl ⟨MolMono_molRep_mem_int Γ b', MolMono_inl_not_mem_int Γ 2⟩

/-- **A red solid edge of `Graph.toMG'` between the internal molecules and the external ones
gives the red solid edge at `⊖`**, in a graph with the charge pattern of the block normal form:
at an unpinned `⊖` there is no edge from the block of `⊖`, so the edge is a component `Ḡ` whose
first atom is internal in the block normal form and whose second atom is external; by the charge
pattern that atom is `⊖`. -/
private theorem RunMinus_I_of_red {Γ : Graph 3 n} (hC : Γ.ColourInvB)
    (h : ∃ e, Γ.toMG'.RedCrosses Γ.toMG'.int e) : RunMinus_I Γ := by
  intro hu
  obtain ⟨e, hcls, -, -, hcut⟩ := h
  rcases e with ⟨i, hi⟩ | a
  · set c := Γ.comps[i] with hcdef
    have hcls' : (if (Γ.flatComp c).kind = .dot ∨ Γ.molRep (Γ.flatComp c).x =
        Γ.molRep (Γ.flatComp c).y then none else (Γ.flatComp c).kind.mclass) = some .minus :=
      hcls
    split_ifs at hcls' with hif
    rw [Graph.flatComp_kind] at hcls'
    have hk := RunMinus_mclass_minus hcls'
    have hne : c.kind ≠ .dot := by rw [hk]; simp
    have hfc := RunMinus_flatComp (Γ := Γ) hne
    have hm : Γ.flatComp c ∈ Γ.blockNorm.comps := List.mem_map_of_mem (List.getElem_mem hi)
    have hr : (Γ.flatComp c).kind.isRandom = true := by
      rw [Graph.flatComp_kind, hk]; rfl
    obtain ⟨hxr, hy0, hy1, -⟩ := (hC _ hm).1 hr
    rw [hfc] at hxr hy0 hy1
    simp only at hxr hy0 hy1
    have hcut' : (Γ.molRep (Γ.flatComp c).x ∈ Γ.toMG'.int ∧
        Γ.molRep (Γ.flatComp c).y ∉ Γ.toMG'.int) ∨
        (Γ.molRep (Γ.flatComp c).x ∉ Γ.toMG'.int ∧ Γ.molRep (Γ.flatComp c).y ∈ Γ.toMG'.int) :=
      hcut
    rw [hfc] at hcut'
    simp only at hcut'
    have hxi : Γ.molRep (Γ.flatAtom c.x) ∈ Γ.toMG'.int := by
      rcases hfx : Γ.flatAtom c.x with a | b
      · rw [hfx] at hxr; simp at hxr
      · exact MolMono_molRep_mem_int Γ b
    have hyo : Γ.molRep (Γ.flatAtom c.y) ∉ Γ.toMG'.int := by
      rcases hcut' with ⟨-, h'⟩ | ⟨h', -⟩
      · exact h'
      · exact absurd hxi h'
    obtain ⟨a, ha⟩ : ∃ a : Fin 3, Γ.flatAtom c.y = .inl a := by
      rcases hfy : Γ.flatAtom c.y with a | b
      · exact ⟨a, rfl⟩
      · rw [hfy] at hyo; exact absurd (MolMono_molRep_mem_int Γ b) hyo
    have ha2 : a = 2 := by
      have h0 : a ≠ 0 := fun e => hy0 (by rw [ha, e])
      have h1 : a ≠ 1 := fun e => by
        have := hy1 (by rw [ha, e])
        rw [hk] at this
        cases this
      omega
    subst ha2
    refine ⟨c, List.getElem_mem hi, hk, (SelRunIso_flatAtom_inl Γ ha).1, fun hux => ?_⟩
    rw [RunMinus_flat_unp hux] at hxr
    have := hux.1
    rcases hcx : c.x with a | b
    · rw [hcx] at hxr; simp at hxr
    · rw [hcx] at this; simp at this
  · exfalso
    rcases hb : Γ.anchor (.inl a) with _ | b
    · have hcl : Γ.toMG'.cls (.inr a) = none := by simp only [Graph.toMG', hb]
      rw [hcl] at hcls; cases hcls
    · have hcl : Γ.toMG'.cls (.inr a) = some (pinClass a) := by simp only [Graph.toMG', hb]
      rw [hcl] at hcls
      have hp := Option.some.inj hcls
      have ha : a = 2 := by
        unfold pinClass at hp
        split_ifs at hp with h1 h2
        · exact Fin.ext h2
      subst ha
      exact hu.2 b (RunMinus_anchor_some hb)

/-- **The red solid edges are not lost along `Graph.MolMono`**: the pullback of all internal
molecules is the set of all internal molecules, and `redCount_le` applies to it. -/
private theorem RunMinus_red_mono {Γ : Graph 3 n} {Γ' : Graph 3 m} {φ : Atom 3 n → Atom 3 m}
    (hM : Γ.MolMono Γ' φ) (h : ∃ e, Γ.toMG'.RedCrosses Γ.toMG'.int e) :
    ∃ e, Γ'.toMG'.RedCrosses Γ'.toMG'.int e := by
  have hpull : Γ.molPull Γ' φ Γ'.toMG'.int = Γ.toMG'.int := by
    ext M
    simp only [Graph.molPull, Finset.mem_filter]
    refine ⟨And.left, fun hM' => ⟨hM', ?_⟩⟩
    obtain ⟨b, rfl, -⟩ := MolMono_of_mem_int Γ hM'
    have hb := hM.isRight b
    generalize φ (.inr b) = w at hb
    cases w with
    | inl _ => simp at hb
    | inr b' => exact MolMono_molRep_mem_int Γ' b'
  have h1 := hM.redCount_le _ (subset_refl _)
  rw [hpull] at h1
  obtain ⟨e, he⟩ := h
  have hpos : 0 < Γ.toMG'.redCount Γ.toMG'.int :=
    Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩⟩
  obtain ⟨e', he'⟩ := Finset.card_pos.1 (lt_of_lt_of_le hpos h1)
  exact ⟨e', (Finset.mem_filter.1 he').2⟩

/-- **A `Q`-expansion of Step 3** ([II, Lemma 4.15]) of a graph with the invariant `Graph.InvB'`
that is not a `Q`-graph keeps the red solid edge at `⊖`: by (F6) of `QExpFamilyStmt` every output
graph is reached along `Graph.MolMono`, and by `qexpClauseB` it has the charge pattern of the
block normal form. -/
private theorem RunMinus_qexp {D n₀ : ℕ}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (hF : QExpFamilyStmt 𝔈)
    {Γ : Graph 3 n₀} {x : Fin n₀} (h : RunMinus_I Γ) (hN : ∃ C, Γ.Normal C) (hP : Γ.Plain)
    (hform : Γ.IsQFormAt (.inr x)) (hnQ : ¬ Γ.IsQGraph) (hB : Γ.InvB')
    (hcl : qexpClauseB D x Γ (𝔈 D n₀ x Γ)) : ∀ u ∈ 𝔈 D n₀ x Γ, RunMinus_I u.g := by
  intro u hu
  have hmono := (hF.2.2.2.2.2 D n₀ x Γ hN hform hP hnQ hB u hu).1
  exact RunMinus_I_of_red (hcl.2 hB u hu).2.1 (RunMinus_red_mono hmono (RunMinus_red_of_I h))

end QExp

/-! ## The run of the selector -/

section Run

/-- **One step of the run** of [II, Strategy 6.6] at an admissible location of a graph of the
domain of the selector keeps the red solid edge at `⊖`. -/
private theorem RunMinus_step {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (hF : QExpFamilyStmt 𝔈)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (h : RunMinus_I g.2) (hD : TerminationC_Dom n D g)
    {l : TerminationC_Loc g.1} (hA : TerminationC_Adm n D 𝔈 g l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, RunMinus_I s.2 := by
  obtain ⟨n₀, Γ⟩ := g
  intro s hs
  cases l with
  | loc o x =>
    obtain ⟨-, hDo, ⟨C, hN⟩, hL, -, -, -, hside, -, -⟩ := hA
    have hR : TerminationC_RI n D ⟨n₀, Γ⟩ := hD.resolve_left fun h => h ⟨C, hN⟩
    obtain ⟨hB, -⟩ := TerminationC_invB hR hL hDo
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact (RunMinus_localOp x o hB.2.1 hside t ht).2 h
  | dot =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact (RunMinus_oDotT ht).2 h
  | dropDot Γ' =>
    rw [List.mem_singleton.1 hs]
    exact RunMinus_I_dropDot hA.1 h
  | reorder Γ' =>
    rw [List.mem_singleton.1 hs]
    exact RunMinus_I_reorder hA.1 h
  | xdotDup i =>
    rw [List.mem_singleton.1 hs]
    exact RunMinus_I_sub (fun c hc _ => List.mem_append_left _ hc) h
  | xdotDrop i j =>
    obtain ⟨hi, hj, ⟨-, hc, hk, -⟩, -⟩ := hA
    have hk' : Γ.comps[i].kind = .xdot := hk
    have hjk₀ : Γ.comps[j].kind = Γ.comps[i].kind := by
      rcases hc with e | e
      · exact congrArg Comp.kind e
      · have := congrArg Comp.kind e
        exact this
    have hjk : Γ.comps[j].kind = .xdot := by rw [hjk₀, hk']
    rw [List.mem_singleton.1 hs]
    exact RunMinus_I_sub (fun c hc hck => RunMinus_mem_erase (List.getElem?_eq_getElem hj) hc
      (by rintro rfl; exact hck hjk)) h
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm =>
    rw [List.mem_singleton.1 hs]
    exact RunMinus_I_sub (fun c hc _ => hc) h
  | subst m H x y₁ y₂ =>
    obtain ⟨he, -, -, hprem⟩ := hA
    obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.1 he
    cases eq_of_heq he
    obtain ⟨g', -, rfl⟩ := List.mem_map.1 hs
    exact RunMinus_I_glue hprem.2.2.1 h g'.2
  | qexp x =>
    obtain ⟨⟨C, hN⟩, hP, hDo, hform, hnQ, -, hcl⟩ := hA
    have hR : TerminationC_RI n D ⟨n₀, Γ⟩ := hD.resolve_left fun h => h ⟨C, hN⟩
    have hB : Γ.InvB' := by
      rcases hR.1 with ⟨hB, -⟩ | ⟨-, hq⟩ | ⟨hlt, -⟩
      · exact hB
      · exact absurd hq hnQ
      · exact absurd (lt_of_lt_of_le hlt (SelRun_paperOrd_le Γ)) hDo
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    exact RunMinus_qexp hF h ⟨C, hN⟩ hP hform hnQ hB hcl u hu

/-- The carried property: the red solid edge at `⊖`, or an output graph without internal atom
that is a `Q`-graph with a red solid, diffusive or dotted edge at `⊖`. -/
private def RunMinus_J (n D : ℕ) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  RunMinus_I g.2 ∨ (TerminationC_Out n D g ∧ g.1 = 0 ∧ g.2.IsQGraph ∧ RunMinus_S2 g.2)

/-- **The red solid edge at `⊖` along the run** of the selector `TerminationC_sel`. -/
private theorem RunMinus_run {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (hF : QExpFamilyStmt 𝔈)
    (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {E F : Expansion 3}
    (hr : SelRunB n D 𝒯 𝔈 TerminationC_sel E F) :
    (∀ g ∈ E, RunMinus_J n D g ∧
      (TerminationC_Out n D g ∨ ∃ r, TerminationC2_Good n D 𝒯 g r)) →
    ∀ g ∈ F, RunMinus_J n D g := by
  have hH : TerminationC2_Hyp n D Sig 𝒯 := ⟨hn, hT⟩
  have hℓ := TerminationC_sel_adm 𝔈 hF n D 𝒯
  have hkey := TerminationC2_key hH hF (TerminationC2_tSubst_runKinds hH) hℓ
  induction hr with
  | nil =>
    intro _ g hg
    simp at hg
  | out _ _ ih =>
    intro hE g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact (hE _ List.mem_cons_self).1
    · exact ih (fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')) g hg
  | @step g E F hO _ _ ih =>
    intro hE
    obtain ⟨hJ, hc⟩ := hE g List.mem_cons_self
    have hI : RunMinus_I g.2 := hJ.resolve_right fun h => hO h.1
    obtain ⟨r, hr⟩ := hc.resolve_left hO
    obtain ⟨hD, hs⟩ := hkey g r hr hO
    have hA := (hℓ g hD hO).1
    refine ih fun s hs' => ?_
    rcases List.mem_append.1 hs' with hs' | hs'
    · refine ⟨Or.inl (RunMinus_step hF hI hD hA s hs'), ?_⟩
      rcases hs s hs' with h | ⟨r', -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨r', h⟩
    · exact hE s (List.mem_cons_of_mem _ hs')

set_option maxRecDepth 100000 in
/-- The red solid edge at `⊖` or a dotted edge from `⊖` to an internal atom, and the third clause
of `Graph.AtExternals`, on the graphs of `A` and `Q` of the second order `T`-expansion; the graphs
of `A` have internal atoms. -/
private theorem RunMinus_h2_facts : (∀ g ∈ h2Rec.A, g.1 ≠ 0) ∧ ∀ g ∈ h2Rec.A ++ h2Rec.Q,
    (g.1 = 0 ∨
      g.2.comps.any (fun c => c.kind == .G .minus && c.y == .inl 2 && c.x.isRight) = true ∨
      g.2.comps.any (fun c => c.kind == .dot &&
        ((c.x == .inl 2 && c.y.isRight) || (c.y == .inl 2 && c.x.isRight))) = true) ∧
    RunMinus_S2 g.2 := by
  decide +kernel

/-- A dotted edge from `⊖` to an internal atom pins `⊖`. -/
private theorem RunMinus_pin_of_dot {n : ℕ} {Γ : Graph 3 n}
    (h : Γ.comps.any (fun c => c.kind == .dot &&
      ((c.x == .inl 2 && c.y.isRight) || (c.y == .inl 2 && c.x.isRight))) = true) :
    ¬ Γ.Unpinned (.inl 2) := by
  intro hu
  obtain ⟨c, hc, hb⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hb
  obtain ⟨hk, ⟨hx, hy⟩ | ⟨hy, hx⟩⟩ := hb
  · have hsb := RunMinus_dot_same hc hk
    rw [hx] at hsb
    rcases hcy : c.y with a | b
    · rw [hcy] at hy; simp at hy
    · rw [hcy] at hsb; exact hu.2 b hsb
  · have hsb := (RunMinus_dot_same hc hk).symm
    rw [hy] at hsb
    rcases hcx : c.x with a | b
    · rw [hcx] at hx; simp at hx
    · rw [hcx] at hsb; exact hu.2 b hsb

/-- The graphs of `A` and `Q` of the second order `T`-expansion, the inputs of the run, carry the
property `RunMinus_J`. -/
private theorem RunMinus_inputs {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) : ∀ g ∈ h2Rec.A ++ h2Rec.Q, RunMinus_J n D g := by
  have hD : 2 < D := by have := hT.1; omega
  intro g hg
  obtain ⟨hA0, hall⟩ := RunMinus_h2_facts
  obtain ⟨h0 | hred | hdot, hS2⟩ := hall g hg
  · right
    have hQ : g ∈ h2Rec.Q := by
      rcases List.mem_append.1 hg with h | h
      · exact absurd h0 (hA0 g h)
      · exact h
    have hS := h2Rec_struct (fun _ => []) D hD
    exact ⟨RunCompare_q0_out hD hQ h0, h0, (hS.2.2.2.1.2.2.2.1 g hQ).1, hS2⟩
  · left
    intro _
    obtain ⟨c, hc, hb⟩ := List.any_eq_true.1 hred
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨c, hc, hb.1.1, hb.1.2, RunMinus_not_unp_right hb.2⟩
  · left
    intro hu
    exact absurd hu (RunMinus_pin_of_dot hdot)

end Run

/-! ## [II, Def 3.2 (9)] at `⊖` on the output graphs of the run -/

/-- **The red solid edge at `⊖` on the output graphs of the run of the selector** ([II, Def 3.2 (9)]
at `⊖`, [II, Strategy 6.6], [II, Lemma 6.8]): for a family `𝔈` of `Q`-expansions of
[II, Lemma 4.15] (`QExpFamilyStmt`), a cutoff order `n ≥ 3` and an `(n - 1)`-th order
`T`-expansion `𝒯` with error order `D`, every output graph of the run driven by `TerminationC_sel`
from the graphs of `A` and `Q` of the second order `T`-expansion that is not a `Q`-graph has
* if `⊖` is unpinned (`Graph.Unpinned`: its block of dotted edges has no internal atom), a red
  solid edge `Ḡ_{u⊖}` whose first atom `u` is not unpinned;
* a red solid, diffusive or dotted edge at `⊖` (the third clause of `Graph.AtExternals`). -/
theorem RunMinus.selRun_minus :
    ∀ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 →
    ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
    ∀ F : Expansion 3, SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) F →
    ∀ g ∈ F, ¬ g.2.IsQGraph →
      (g.2.Unpinned (.inl 2) →
        ∃ c ∈ g.2.comps, c.kind = .G .minus ∧ c.y = .inl 2 ∧ ¬ g.2.Unpinned c.x) ∧
      g.2.comps.any (fun c => (c.kind == .G .minus || c.kind.isDiffusive || c.kind == .dot) &&
        (c.x == .inl 2 || c.y == .inl 2)) = true := by
  intro 𝔈 hF n D Sig 𝒯 hn hT F hr g hg hnQ
  have hJ := RunMinus_run hF hn hT hr (fun g hg => ⟨RunMinus_inputs hn hT g hg,
    TerminationC2_inputs (⟨hn, hT⟩ : TerminationC2_Hyp n D Sig 𝒯) g hg⟩) g hg
  have hI : RunMinus_I g.2 := hJ.resolve_right fun h => hnQ h.2.2.1
  exact ⟨hI, RunMinus_S2_of hI⟩

/-- **[II, Def 3.2 (9)] at `⊖` on every output graph of the run of the selector**, `Q`-graphs
included: with the hypotheses of `RunMinus.selRun_minus`, every output graph has a red solid,
diffusive or dotted edge at `⊖`; if it has an internal atom and `⊖` is unpinned, it has a red
solid edge `Ḡ_{u⊖}` whose first atom `u` is not unpinned. -/
theorem RunMinus.selRun_minus_atExt :
    ∀ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 →
    ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
    ∀ F : Expansion 3, SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) F →
    ∀ g ∈ F,
      g.2.comps.any (fun c => (c.kind == .G .minus || c.kind.isDiffusive || c.kind == .dot) &&
        (c.x == .inl 2 || c.y == .inl 2)) = true ∧
      (g.1 ≠ 0 → g.2.Unpinned (.inl 2) →
        ∃ c ∈ g.2.comps, c.kind = .G .minus ∧ c.y = .inl 2 ∧ ¬ g.2.Unpinned c.x) := by
  intro 𝔈 hF n D Sig 𝒯 hn hT F hr g hg
  have hJ := RunMinus_run hF hn hT hr (fun g hg => ⟨RunMinus_inputs hn hT g hg,
    TerminationC2_inputs (⟨hn, hT⟩ : TerminationC2_Hyp n D Sig 𝒯) g hg⟩) g hg
  rcases hJ with hI | ⟨-, h0, -, hS2⟩
  · exact ⟨RunMinus_S2_of hI, fun _ => hI⟩
  · exact ⟨hS2, fun h => absurd h0 h⟩


section Instances

end Instances

end RBM8D.Graphs
