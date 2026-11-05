import RBM8D.Joint.Words
import RBM8D.AvgBound.Defs

/-!
# Relabelling the `Θ` edge at `⊗`: the graph properties it keeps

The properties of [II, Def 3.2] and [II, Def 6.3] read by `TRec.Shape`, `TRec.Def63` and
`Graph.MinusProfile` of a graph `Σ_x Θ_{⊗x} 𝒢_x` (`G14.RootedTheta`) with its `Θ` edge at `⊗`
relabelled by `o` (`Graph.relabelRoot`): the scaling order grows by `Σ oᵢ − 2|o|` ([II, (2.5)]),
the kinds of [II, Def 3.2 (2)] stay those of the graph for a label with entries even in `[4, N']`,
and every other property is kept, because none of them reads the label of a `Θ` edge
(`G14.relabelStmt`).

The properties are read through the atoms, the minor, the `P`/`Q` label and the class of the kind
of a component, and a `Θ` edge with a label has the same class as the plain `Θ` edge. So the
argument is for a map of the components that changes only the labels of `Θ` edges
(`Relabel.ThetaBlind`).
-/

noncomputable section

namespace RBM8D

open Graphs

namespace Relabel

variable {k n : ℕ}

/-! ## Maps of the components that change only the labels of `Θ` edges -/

/-- A map `r` of the components keeps the atoms, the minor and the `P`/`Q` label, and changes
only the label of a `Θ` edge. -/
def ThetaBlind (r : Comp (Atom k n) → Comp (Atom k n)) : Prop :=
  ∀ c, (r c).x = c.x ∧ (r c).y = c.y ∧ (r c).minor = c.minor ∧ (r c).label = c.label ∧
    ((r c).kind = c.kind ∨ ∃ o o', c.kind = .theta o ∧ (r c).kind = .theta o')

/-- The graph with `r` applied to every component. -/
def mapC (r : Comp (Atom k n) → Comp (Atom k n)) (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map r, Γ.coeff⟩

variable {r : Comp (Atom k n) → Comp (Atom k n)}

/-- The first end of a component is kept. -/
theorem ThetaBlind.x (hr : ThetaBlind r) (c : Comp (Atom k n)) : (r c).x = c.x := (hr c).1

/-- The second end of a component is kept. -/
theorem ThetaBlind.y (hr : ThetaBlind r) (c : Comp (Atom k n)) : (r c).y = c.y := (hr c).2.1

/-- The minor of a component is kept. -/
theorem ThetaBlind.minor (hr : ThetaBlind r) (c : Comp (Atom k n)) : (r c).minor = c.minor :=
  (hr c).2.2.1

/-- The `P`/`Q` label of a component is kept. -/
theorem ThetaBlind.label (hr : ThetaBlind r) (c : Comp (Atom k n)) : (r c).label = c.label :=
  (hr c).2.2.2.1

/-- A function of the kind that does not distinguish the `Θ` edges is unchanged by `r`. -/
theorem ThetaBlind.kind_fun (hr : ThetaBlind r) {β : Type} (K : Kind → β)
    (hK : ∀ o o', K (.theta o) = K (.theta o')) (c : Comp (Atom k n)) :
    K (r c).kind = K c.kind := by
  rcases (hr c).2.2.2.2 with h | ⟨o, o', h1, h2⟩
  · rw [h]
  · rw [h1, h2, hK]

/-- A kind other than a `Θ` edge is the kind of `r c` exactly when it is the kind of `c`. -/
theorem ThetaBlind.eq_iff (hr : ThetaBlind r) (κ : Kind) (hκ : ∀ o, κ ≠ .theta o)
    (c : Comp (Atom k n)) : (r c).kind = κ ↔ c.kind = κ := by
  have := hr.kind_fun (fun κ' => decide (κ' = κ)) (fun o o' => by
    simp [(hκ o).symm, (hκ o').symm]) c
  simpa using this

/-- The kind stays diffusive or not. -/
theorem ThetaBlind.isDiffusive (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind.isDiffusive = c.kind.isDiffusive :=
  hr.kind_fun Kind.isDiffusive (fun _ _ => rfl) c

/-- The kind keeps joining a molecule or not. -/
theorem ThetaBlind.joinsMol (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind.joinsMol = c.kind.joinsMol :=
  hr.kind_fun Kind.joinsMol (fun _ _ => rfl) c

/-- The kind stays solid or not. -/
theorem ThetaBlind.isSolid (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind.isSolid = c.kind.isSolid :=
  hr.kind_fun Kind.isSolid (fun _ _ => rfl) c

/-- The kind stays random or not. -/
theorem ThetaBlind.isRandom (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind.isRandom = c.kind.isRandom :=
  hr.kind_fun Kind.isRandom (fun _ _ => rfl) c

/-- The kind stays a weight or not. -/
theorem ThetaBlind.isWeight (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind.isWeight = c.kind.isWeight :=
  hr.kind_fun Kind.isWeight (fun _ _ => rfl) c

/-- The kind stays blue or not. -/
theorem ThetaBlind.isBlue (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind.isBlue = c.kind.isBlue :=
  hr.kind_fun Kind.isBlue (fun _ _ => rfl) c

/-- The class of the kind as an edge of the molecular graph is kept. -/
theorem ThetaBlind.mclass (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind.mclass = c.kind.mclass :=
  hr.kind_fun Kind.mclass (fun _ _ => rfl) c

/-- The kind is a dotted edge exactly when it was. -/
theorem ThetaBlind.eq_dot (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind = .dot ↔ c.kind = .dot := hr.eq_iff _ (by simp) c

/-- The kind is a `×`-dotted edge exactly when it was. -/
theorem ThetaBlind.eq_xdot (hr : ThetaBlind r) (c : Comp (Atom k n)) :
    (r c).kind = .xdot ↔ c.kind = .xdot := hr.eq_iff _ (by simp) c

/-- The kind is a solid edge of the charge `ch` exactly when it was. -/
theorem ThetaBlind.eq_G (hr : ThetaBlind r) (ch : Charge) (c : Comp (Atom k n)) :
    (r c).kind = .G ch ↔ c.kind = .G ch := hr.eq_iff _ (by simp) c

/-- The kind is the waved edge `w` exactly when it was. -/
theorem ThetaBlind.eq_waved (hr : ThetaBlind r) (w : Wave) (c : Comp (Atom k n)) :
    (r c).kind = .waved w ↔ c.kind = .waved w := hr.eq_iff _ (by simp) c

/-- The kind is the weight `(G_{xx})⁻¹` of the charge `ch` exactly when it was. -/
theorem ThetaBlind.eq_inv (hr : ThetaBlind r) (ch : Charge) (c : Comp (Atom k n)) :
    (r c).kind = .inv ch ↔ c.kind = .inv ch := hr.eq_iff _ (by simp) c

/-- The kind is the weight `W_d` of the charge `ch` and the degree `d` exactly when it was. -/
theorem ThetaBlind.eq_wD (hr : ThetaBlind r) (ch : Charge) (d : ℕ) (c : Comp (Atom k n)) :
    (r c).kind = .wD ch d ↔ c.kind = .wD ch d := hr.eq_iff _ (by simp) c

/-! ## The graphs read through the ends of the components -/

section Graphs

variable (hr : ThetaBlind r) (Γ : Graph k n)

include hr

omit hr in
/-- The components of `mapC r Γ`. -/
theorem comps_mapC : (mapC r Γ).comps = Γ.comps.map r := rfl

omit hr in
/-- The number of components is kept. -/
theorem length_mapC : (mapC r Γ).comps.length = Γ.comps.length := by
  simp [mapC]

/-- The graph of the dotted edges is kept. -/
theorem dotGraph_mapC : (mapC r Γ).dotGraph = Γ.dotGraph := by
  unfold Graph.dotGraph
  congr 1
  funext u v
  simp only [mapC, List.mem_map, exists_exists_and_eq_and, hr.x, hr.y, hr.eq_dot]

/-- The graph of the waved and dotted edges is kept. -/
theorem molGraph_mapC : (mapC r Γ).molGraph = Γ.molGraph := by
  unfold Graph.molGraph
  congr 1
  funext u v
  simp only [mapC, List.mem_map, exists_exists_and_eq_and, hr.x, hr.y, hr.joinsMol]

/-- The graph of all edges is kept. -/
theorem edgeGraph_mapC : (mapC r Γ).edgeGraph = Γ.edgeGraph := by
  unfold Graph.edgeGraph
  congr 1
  funext u v
  simp only [mapC, List.mem_map, exists_exists_and_eq_and, hr.x, hr.y]

/-- The graph of the waved and diffusive edges is kept. -/
theorem wavedThetaGraph_mapC : (mapC r Γ).wavedThetaGraph = Γ.wavedThetaGraph := by
  unfold Graph.wavedThetaGraph
  congr 1
  funext u v
  simp only [mapC, List.mem_map, exists_exists_and_eq_and, hr.x, hr.y, hr.joinsMol, ne_eq,
    hr.eq_dot, hr.isDiffusive]

/-- The dotted blocks are kept. -/
theorem sameBlock_mapC (u v : Atom k n) : (mapC r Γ).SameBlock u v ↔ Γ.SameBlock u v := by
  unfold Graph.SameBlock
  rw [dotGraph_mapC hr]

/-- The molecules are kept. -/
theorem sameMol_mapC (u v : Atom k n) : (mapC r Γ).SameMol u v ↔ Γ.SameMol u v := by
  unfold Graph.SameMol
  rw [molGraph_mapC hr]

/-- The external atoms identified with an internal atom are kept. -/
theorem unpinned_mapC (u : Atom k n) : (mapC r Γ).Unpinned u ↔ Γ.Unpinned u := by
  simp only [Graph.Unpinned, sameBlock_mapC hr]

/-- The least internal atom of a dotted block is kept. -/
theorem anchor_mapC (u : Atom k n) : (mapC r Γ).anchor u = Γ.anchor u := by
  simp only [Graph.anchor, sameBlock_mapC hr]
  congr
  funext b
  exact decide_eq_decide.2 Iff.rfl

/-- The atom of the block normal form is kept. -/
theorem flatAtom_mapC (u : Atom k n) : (mapC r Γ).flatAtom u = Γ.flatAtom u := by
  cases u <;> simp only [Graph.flatAtom, anchor_mapC hr]

/-- The representative of a molecule is kept. -/
theorem molRep_mapC (u : Atom k n) : (mapC r Γ).molRep u = Γ.molRep u := by
  cases u <;> simp only [Graph.molRep, sameMol_mapC hr]
  congr
  funext b
  exact decide_eq_decide.2 Iff.rfl

end Graphs

/-! ## The block normal form and the molecular graph of the block reading -/

/-- The first end of a component in the block normal form. -/
theorem flatComp_x (Γ : Graph k n) (c : Comp (Atom k n)) :
    (Γ.flatComp c).x = if c.kind = .dot then c.x else Γ.flatAtom c.x := by
  unfold Graph.flatComp
  split_ifs <;> rfl

/-- The second end of a component in the block normal form. -/
theorem flatComp_y (Γ : Graph k n) (c : Comp (Atom k n)) :
    (Γ.flatComp c).y = if c.kind = .dot then c.y else Γ.flatAtom c.y := by
  unfold Graph.flatComp
  split_ifs <;> rfl

/-- Sequentially pre-deterministic, globally standard and the minimal isolated subset of a
molecular multigraph do not depend on the names of its edges: for two multigraphs with the same
vertices and edges indexed by `Fin L ⊕ Fin m` and `Fin L' ⊕ Fin m` (`L = L'`) that have the same
ends and classes under `Fin.cast`. -/
theorem mg_of_cast {V : Type} [DecidableEq V] {L L' m : ℕ} (h : L = L')
    (G : MGraph V (Fin L ⊕ Fin m)) (G' : MGraph V (Fin L' ⊕ Fin m))
    (hint : G'.int = G.int) (hext : G'.ext = G.ext)
    (hends : ∀ x, G'.ends (Sum.map (Fin.cast h) id x) = G.ends x)
    (hcls : ∀ x, G'.cls (Sum.map (Fin.cast h) id x) = G.cls x) :
    (G'.SPD ↔ G.SPD) ∧ (G'.GloballyStandard ↔ G.GloballyStandard) ∧ G'.MIS = G.MIS := by
  subst h
  have : G' = G := by
    obtain ⟨i, x, e, c⟩ := G
    obtain ⟨i', x', e', c'⟩ := G'
    simp only at hint hext
    subst hint hext
    have h1 : e' = e := funext fun x => by simpa using hends x
    have h2 : c' = c := funext fun x => by simpa using hcls x
    subst h1 h2
    rfl
  subst this
  exact ⟨Iff.rfl, Iff.rfl, rfl⟩

section Flat

variable (hr : ThetaBlind r) (Γ : Graph k n)

include hr

/-- The first end of a component in the block normal form is kept. -/
theorem flatComp_mapC_x (c : Comp (Atom k n)) :
    ((mapC r Γ).flatComp (r c)).x = (Γ.flatComp c).x := by
  simp only [flatComp_x, hr.eq_dot, hr.x, flatAtom_mapC hr]

/-- The second end of a component in the block normal form is kept. -/
theorem flatComp_mapC_y (c : Comp (Atom k n)) :
    ((mapC r Γ).flatComp (r c)).y = (Γ.flatComp c).y := by
  simp only [flatComp_y, hr.eq_dot, hr.y, flatAtom_mapC hr]

omit hr in
/-- The component with the index `i` of `mapC r Γ`. -/
theorem getElem_mapC (i : Fin Γ.comps.length) :
    (mapC r Γ).comps[Fin.cast (length_mapC Γ).symm i] = r Γ.comps[i] := by
  simp only [mapC, Fin.getElem_fin, List.getElem_map]
  rfl

/-- The molecular graph of the block reading of the graph with the components mapped is that of
the graph, up to the names of the edges. -/
theorem toMG'_mapC :
    ((mapC r Γ).toMG'.SPD ↔ Γ.toMG'.SPD) ∧
      ((mapC r Γ).toMG'.GloballyStandard ↔ Γ.toMG'.GloballyStandard) ∧
      (mapC r Γ).toMG'.MIS = Γ.toMG'.MIS := by
  refine mg_of_cast (length_mapC Γ).symm Γ.toMG' (mapC r Γ).toMG' ?_ ?_ ?_ ?_
  · simp only [Graph.toMG', molRep_mapC hr]
  · simp only [Graph.toMG']
  · rintro (i | a)
    · simp only [Sum.map_inl, Graph.toMG', getElem_mapC, flatComp_mapC_x hr, flatComp_mapC_y hr,
        molRep_mapC hr]
    · simp only [Sum.map_inr, id, Graph.toMG', anchor_mapC hr, molRep_mapC hr]
  · rintro (i | a)
    · simp only [Sum.map_inl, Graph.toMG', getElem_mapC, flatComp_mapC_x hr, flatComp_mapC_y hr,
        molRep_mapC hr, Graph.flatComp_kind, hr.eq_dot, hr.mclass]
    · simp only [Sum.map_inr, id, Graph.toMG', anchor_mapC hr, molRep_mapC hr]

end Flat

/-! ## Properties kept by a map that changes only the labels of `Θ` edges -/

section Preds

variable (hr : ThetaBlind r) (Γ : Graph k n)

include hr

/-- The test for a solid edge of the charge `ch` is kept. -/
theorem beq_G (ch : Charge) (c : Comp (Atom k n)) :
    ((r c).kind == .G ch) = (c.kind == .G ch) :=
  hr.kind_fun (fun κ => κ == .G ch) (fun o o' => by simp) c

/-- The test for a dotted edge is kept. -/
theorem beq_dot (c : Comp (Atom k n)) : ((r c).kind == .dot) = (c.kind == .dot) :=
  hr.kind_fun (fun κ => κ == .dot) (fun o o' => by simp) c

/-- The regular graphs are kept. -/
theorem regular_mapC (C : ℕ) : (mapC r Γ).Regular C ↔ Γ.Regular C := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := h.size
      rwa [length_mapC] at this
    · have := h.connected
      rwa [edgeGraph_mapC hr] at this
    · have := h.internal
      rwa [wavedThetaGraph_mapC hr] at this
    · intro c hc hk
      have := h.noIntDot (r c) (List.mem_map_of_mem hc) ((hr.eq_dot c).2 hk)
      rwa [hr.x, hr.y] at this
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [length_mapC]
      exact h.size
    · rw [edgeGraph_mapC hr]
      exact h.connected
    · rw [wavedThetaGraph_mapC hr]
      exact h.internal
    · intro c' hc' hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      have := h.noIntDot c hc ((hr.eq_dot c).1 hk)
      rwa [hr.x, hr.y]

/-- The normal regular graphs are kept. -/
theorem normal_mapC (C : ℕ) : (mapC r Γ).Normal C ↔ Γ.Normal C := by
  unfold Graph.Normal
  rw [regular_mapC hr]
  simp only [mapC, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    exists_exists_and_eq_and, hr.x, hr.y, hr.isSolid, hr.eq_xdot]

/-- The net of a set of components is kept, for the same set of indices. -/
theorem net_mapC (B : Finset (Fin Γ.comps.length)) :
    (mapC r Γ).net (B.image (Fin.cast (length_mapC (r := r) Γ).symm)) = Γ.net B := by
  unfold Graph.net
  congr 1
  funext a b
  apply propext
  rw [sameMol_mapC hr]
  constructor
  · rintro (h | ⟨i', hi', h⟩)
    · exact Or.inl h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hi'
      rw [getElem_mapC, hr.x, hr.y] at h
      exact Or.inr ⟨i, hi, h⟩
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨_, Finset.mem_image_of_mem _ hi, ?_⟩
      rw [getElem_mapC, hr.x, hr.y]
      exact h

/-- The doubly connected graphs are kept. -/
theorem doublyConnected_mapC : Γ.DoublyConnected → (mapC r Γ).DoublyConnected := by
  rintro ⟨black, blue, hd, hbk, hbl, hs1, hs2⟩
  have hinj := Fin.cast_injective (length_mapC (r := r) Γ).symm
  refine ⟨black.image (Fin.cast (length_mapC (r := r) Γ).symm),
    blue.image (Fin.cast (length_mapC (r := r) Γ).symm),
    (Finset.disjoint_image hinj).2 hd, ?_, ?_, ?_, ?_⟩
  · intro i' hi'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hi'
    rw [getElem_mapC, hr.isDiffusive]
    exact hbk i hi
  · intro i' hi'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hi'
    rw [getElem_mapC, hr.isDiffusive, hr.isBlue]
    exact hbl i hi
  · unfold Graph.Spans
    rw [net_mapC hr]
    exact hs1
  · unfold Graph.Spans
    rw [net_mapC hr]
    exact hs2

/-- The label-free graphs are kept. -/
theorem labelFree_mapC : (mapC r Γ).LabelFree ↔ Γ.LabelFree := by
  simp only [Graph.LabelFree, mapC, List.forall_mem_map, hr.label]

/-- The `Q`-graphs are kept. -/
theorem isQGraph_mapC : (mapC r Γ).IsQGraph ↔ Γ.IsQGraph := by
  simp only [Graph.IsQGraph, mapC, List.mem_map, exists_exists_and_eq_and,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hr.label, hr.isRandom]

/-- The recollision graphs are kept. -/
theorem isRecollision_mapC (B : Finset (Fin k)) :
    (mapC r Γ).IsRecollision B ↔ Γ.IsRecollision B := by
  simp only [Graph.IsRecollision, mapC, List.mem_map, exists_exists_and_eq_and, hr.eq_dot, hr.x,
    hr.y]

/-- The graphs without a labelled dotted or `×`-dotted edge are kept. -/
theorem noLabDot_mapC : (mapC r Γ).NoLabDot ↔ Γ.NoLabDot := by
  simp only [Graph.NoLabDot, mapC, List.forall_mem_map, hr.eq_dot, hr.eq_xdot, hr.label]

/-- The labels are kept. -/
theorem labels_mapC : (mapC r Γ).labels = Γ.labels := by
  have : Comp.label ∘ r = Comp.label := funext hr.label
  simp only [Graph.labels, mapC, List.filterMap_map, this]

/-- The dot excess is kept. -/
theorem dotExcess_mapC : (mapC r Γ).dotExcess = Γ.dotExcess := by
  have : (fun c => decide ((r c).kind = .dot)) = fun c => decide (c.kind = .dot) :=
    funext fun c => decide_eq_decide.2 (hr.eq_dot c)
  have hn : (mapC r Γ).nDots = Γ.nDots := by
    simp only [Graph.nDots, mapC, List.filter_map, List.length_map, Function.comp_def, this]
  unfold Graph.dotExcess
  rw [hn, dotGraph_mapC hr]

/-- The plain graphs are kept. -/
theorem plain_mapC : (mapC r Γ).Plain ↔ Γ.Plain := by
  simp only [Graph.Plain, Comp.WF, mapC, List.forall_mem_map, ne_eq, hr.minor, hr.eq_inv, hr.eq_wD,
    hr.eq_dot, hr.x, hr.y, hr.isWeight, hr.label, hr.isRandom]

/-- The partition into dotted blocks is kept. -/
theorem dotBlocks_map (as : List (Atom k n)) (cs : List (Comp (Atom k n))) :
    dotBlocks as (cs.map r) = dotBlocks as cs := by
  unfold dotBlocks
  rw [List.foldl_map]
  simp only [hr.eq_dot, hr.x, hr.y]

end Preds

/-! ## The properties of the graphs with external atoms `⊗, ⊕, ⊖` -/

section Preds3

variable {m : ℕ} {s : Comp (Atom 3 m) → Comp (Atom 3 m)} (hs : ThetaBlind s) (Δ : Graph 3 m)

include hs

/-- The property `Graph.AtExternals` is kept. -/
theorem atExternals_mapC : (mapC s Δ).AtExternals ↔ Δ.AtExternals := by
  simp only [Graph.AtExternals, mapC, List.filter_map, List.length_map, List.any_map,
    Function.comp_def, hs.isDiffusive, hs.x, hs.y, beq_G hs, beq_dot hs]

/-- The property `Graph.RootAtPlus` is kept. -/
theorem rootAtPlus_mapC : (mapC s Δ).RootAtPlus ↔ Δ.RootAtPlus := by
  simp only [Graph.RootAtPlus, mapC, List.all_map, Function.comp_def, hs.isDiffusive, hs.x, hs.y]

/-- The property `Graph.TensorDiffusive` is kept. -/
theorem tensorDiffusive_mapC : (mapC s Δ).TensorDiffusive ↔ Δ.TensorDiffusive := by
  simp only [Graph.TensorDiffusive, mapC, List.all_map, Function.comp_def, hs.isDiffusive, hs.x,
    hs.y]

/-- The property `Graph.QLabelAtPlus` is kept. -/
theorem qLabelAtPlus_mapC : (mapC s Δ).QLabelAtPlus ↔ Δ.QLabelAtPlus := by
  simp only [Graph.QLabelAtPlus, mapC, List.forall_mem_map, hs.label]

/-- The property `Graph.MinusProfile` is kept. -/
theorem minusProfile_mapC : (mapC s Δ).MinusProfile ↔ Δ.MinusProfile := by
  simp only [Graph.MinusProfile, mapC, List.forall_mem_map, List.filter_map, List.length_map,
    Function.comp_def, hs.x, hs.y, hs.eq_dot, hs.eq_xdot, hs.eq_G]

/-- The property `Graph.RgCheck` is kept. -/
theorem rgCheck_mapC : (mapC s Δ).RgCheck ↔ Δ.RgCheck := by
  simp only [Graph.RgCheck, mapC, List.mem_map, exists_exists_and_eq_and, hs.joinsMol,
    hs.isDiffusive, hs.x, hs.y]

/-- `⊕` and `⊖` lie in one dotted block exactly when they did. -/
theorem pmBlock_mapC : (mapC s Δ).PMBlock ↔ Δ.PMBlock := by
  simp only [Graph.PMBlock, Graph.pmBlockB, mapC, dotBlocks_map hs]

/-- The property `Graph.DiagRecoll` is kept. -/
theorem diagRecoll_mapC : (mapC s Δ).DiagRecoll ↔ Δ.DiagRecoll := by
  simp only [Graph.DiagRecoll, mapC, dotBlocks_map hs]

/-- The clause `Graph.ExtClause` on the external atoms is kept. -/
theorem extClause_mapC : (mapC s Δ).ExtClause ↔ Δ.ExtClause := by
  unfold Graph.ExtClause Graph.HasDiffToPinned Graph.DiffToPinned Graph.nonDotDeg
  simp only [sameBlock_mapC hs, unpinned_mapC hs, comps_mapC, List.mem_map,
    exists_exists_and_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    List.filter_map, List.length_map, Function.comp_def, hs.isDiffusive, hs.x, hs.y, hs.eq_dot,
    hs.eq_xdot, hs.eq_G, ne_eq]

/-- The charge pattern `Graph.ColourInvB` of the block normal form is kept. -/
theorem colourInvB_mapC : (mapC s Δ).ColourInvB ↔ Δ.ColourInvB := by
  unfold Graph.ColourInvB Graph.ColourInv'
  simp only [Graph.blockNorm, comps_mapC, List.forall_mem_map, flatComp_mapC_x hs,
    flatComp_mapC_y hs, Graph.flatComp_kind, hs.isRandom, hs.eq_G, hs.eq_waved]

/-- The property `Graph.RootedAtExt` is kept. -/
theorem rootedAtExt_mapC : (mapC s Δ).RootedAtExt ↔ Δ.RootedAtExt := by
  unfold Graph.RootedAtExt Graph.HasDiffToPinned Graph.DiffToPinned
  simp only [unpinned_mapC hs, comps_mapC, List.mem_map, exists_exists_and_eq_and,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hs.isDiffusive, hs.x, hs.y, hs.eq_G]

/-- The property `Graph.QLabelInMISB` is kept. -/
theorem qLabelInMISB_mapC : (mapC s Δ).QLabelInMISB ↔ Δ.QLabelInMISB := by
  unfold Graph.QLabelInMISB
  simp only [(toMG'_mapC hs Δ).2.2]
  simp only [comps_mapC, List.mem_map, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, hs.label, molRep_mapC hs, hs.eq_waved, hs.x, hs.y]

/-- The block reading of sequentially pre-deterministic graphs is kept. -/
theorem spdPM'_mapC : spdPM' (mapC s Δ) ↔ spdPM' Δ := (toMG'_mapC hs Δ).1

/-- The block reading of globally standard graphs is kept. -/
theorem gsPM'_mapC : gsPM' (mapC s Δ) ↔ gsPM' Δ := (toMG'_mapC hs Δ).2.1

end Preds3

/-! ## The map that relabels the `Θ` edge at `⊗` -/

section Root

variable {m : ℕ}

/-- The map of the components of `Graph.relabelRoot`: a plain `Θ` edge with an end at `⊗` takes the
label `o`. -/
def rootMap (o : List ℕ) (c : Comp (Atom 3 m)) : Comp (Atom 3 m) :=
  if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0) then { c with kind := .theta o } else c

/-- `Graph.relabelRoot` applies `rootMap o` to every component. -/
theorem relabelRoot_eq (o : List ℕ) (Γ : Graph 3 m) : Γ.relabelRoot o = mapC (rootMap o) Γ := rfl

/-- The map `rootMap o` changes only the label of a `Θ` edge. -/
theorem rootMap_blind (o : List ℕ) : ThetaBlind (rootMap (m := m) o) := by
  intro c
  unfold rootMap
  split_ifs with h
  · exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨[], o, h.1, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-- The entries of a label with entries even in `[4, N]` lie in `[4, N']` for `N ≤ N'`. -/
theorem labelOK_mono {N N' : ℕ} {o : List ℕ} (h : N ≤ N') (ho : labelOK N o = true) :
    labelOK N' o = true := by
  simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho ⊢
  intro e he
  obtain ⟨⟨a, b⟩, c⟩ := ho e he
  exact ⟨⟨a, by omega⟩, c⟩

/-- A component with a kind of [II, Def 3.2] for the labels in `[4, N]` has it for `N ≤ N'`. -/
theorem isTKind_mono {N N' : ℕ} (h : N ≤ N') (c : Comp (Atom 3 m)) (hc : c.isTKind N = true) :
    c.isTKind N' = true := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ <;> try exact hc
  simp only [Comp.isTKind, Bool.and_eq_true] at hc ⊢
  exact ⟨hc.1, labelOK_mono h hc.2⟩

/-- A plain `Θ` edge of a graph with the kinds of [II, Def 3.2] relabelled by `o` has the kinds of
[II, Def 3.2] for the entries of `o` even in `[4, N']`. -/
theorem isTKind_theta {N N' : ℕ} (c : Comp (Atom 3 m)) (hk : c.kind = .theta [])
    (hc : c.isTKind N = true) {o : List ℕ} (ho : labelOK N' o = true) :
    ({ c with kind := .theta o } : Comp (Atom 3 m)).isTKind N' = true := by
  simp only [Comp.isTKind, hk, labelOK, List.all_nil, Bool.and_true] at hc
  simpa only [Comp.isTKind, Bool.and_eq_true] using ⟨hc, ho⟩

/-- The kinds of [II, Def 3.2] are kept for a label with entries even in `[4, N']`. -/
theorem tKinds_relabel {N N' : ℕ} (hN : N ≤ N') {o : List ℕ} (ho : labelOK N' o = true)
    (Γ : Graph 3 m) (h : Γ.TKinds N) : (Γ.relabelRoot o).TKinds N' := by
  unfold Graph.TKinds at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
  have h1 := h c hc
  split_ifs with hk
  · exact isTKind_theta c hk.1 h1 ho
  · exact isTKind_mono hN c h1

/-- The kinds of the graphs of `Err` are kept for a label with entries even in `[4, N']`. -/
theorem tKindsErr_relabel {N N' : ℕ} (hN : N ≤ N') {o : List ℕ} (ho : labelOK N' o = true)
    (Γ : Graph 3 m) (h : Γ.TKindsErr N) : (Γ.relabelRoot o).TKindsErr N' := by
  unfold Graph.TKindsErr at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
  have h1 := h c hc
  split_ifs with hk
  · have h2 : c.isTKind N = true := by
      simp only [Bool.or_eq_true, hk.1, Bool.and_eq_true] at h1
      rcases h1 with h2 | ⟨-, h2⟩
      · exact h2
      · exact absurd h2 (by simp)
    simp only [Bool.or_eq_true]
    exact Or.inl (isTKind_theta c hk.1 h2 ho)
  · simp only [Bool.or_eq_true] at h1 ⊢
    exact h1.imp (isTKind_mono hN c) id

end Root

end Relabel

/-- Relabelling the `Θ` edge at `⊗` of a graph `Σ_x Θ_{⊗x} 𝒢_x` (`G14.RootedTheta`): the scaling
order grows by `Σ oᵢ − 2 |o|`, the kinds stay those of [II, Def 3.2] for a label with entries even
in `[4, N']`, and the other properties of [II, Def 3.2] and [II, Def 6.3] read by `TRec.Shape`,
`TRec.Def63` and `Graph.MinusProfile` are kept (the recollision, dotted-block and
`⊕`-recollision properties in both directions); these do not read the label of a `Θ` edge. -/
def G14.relabelStmt : Prop :=
  ∀ {m : ℕ} (Γ : Graph 3 m) (o : List ℕ), G14.RootedTheta Γ →
    (Γ.relabelRoot o).ord = Γ.ord + ((o.sum : ℤ) - 2 * o.length) ∧
    (∀ N N', N ≤ N' → labelOK N' o = true → Γ.TKinds N → (Γ.relabelRoot o).TKinds N') ∧
    (∀ N N', N ≤ N' → labelOK N' o = true → Γ.TKindsErr N → (Γ.relabelRoot o).TKindsErr N') ∧
    (∀ C, Γ.Normal C → (Γ.relabelRoot o).Normal C) ∧
    (Γ.AtExternals → (Γ.relabelRoot o).AtExternals) ∧
    (Γ.DoublyConnected → (Γ.relabelRoot o).DoublyConnected) ∧
    (Γ.LabelFree → (Γ.relabelRoot o).LabelFree) ∧
    (Γ.IsQGraph → (Γ.relabelRoot o).IsQGraph) ∧
    ((Γ.relabelRoot o).IsRecollision {1, 2} ↔ Γ.IsRecollision {1, 2}) ∧
    (gsPM' Γ → gsPM' (Γ.relabelRoot o)) ∧ (spdPM' Γ → spdPM' (Γ.relabelRoot o)) ∧
    (Γ.ExtClause → (Γ.relabelRoot o).ExtClause) ∧
    (Γ.ColourInvB → (Γ.relabelRoot o).ColourInvB) ∧
    (Γ.QLabelInMISB → (Γ.relabelRoot o).QLabelInMISB) ∧
    (Γ.RootAtPlus → (Γ.relabelRoot o).RootAtPlus) ∧
    (Γ.TensorDiffusive → (Γ.relabelRoot o).TensorDiffusive) ∧
    (Γ.relabelRoot o).dotExcess = Γ.dotExcess ∧
    (Γ.NoLabDot → (Γ.relabelRoot o).NoLabDot) ∧
    (Γ.relabelRoot o).labels = Γ.labels ∧
    ((Γ.relabelRoot o).PMBlock ↔ Γ.PMBlock) ∧
    (Γ.RgCheck → (Γ.relabelRoot o).RgCheck) ∧
    ((Γ.relabelRoot o).DiagRecoll ↔ Γ.DiagRecoll) ∧
    (Γ.RootedAtExt → (Γ.relabelRoot o).RootedAtExt) ∧
    (Γ.Plain → (Γ.relabelRoot o).Plain) ∧
    (Γ.QLabelAtPlus → (Γ.relabelRoot o).QLabelAtPlus) ∧
    (Γ.MinusProfile → (Γ.relabelRoot o).MinusProfile)

/-- **Relabelling the `Θ` edge at `⊗`** (`G14.relabelStmt`): the order of [II, (2.5)], the kinds of
[II, Def 3.2] and the properties of [II, Def 3.2] and [II, Def 6.3] of the relabelled graph. Only
the order reads that the graph is `Σ_x Θ_{⊗x} 𝒢_x` (one edge at `⊗`). -/
theorem G14.relabel : G14.relabelStmt := by
  intro m Γ o hΓ
  have hb : Relabel.ThetaBlind (Relabel.rootMap (m := m) o) := Relabel.rootMap_blind o
  have h1 := Words.ord_relabelRoot hΓ o
  simp only [Relabel.relabelRoot_eq] at h1 ⊢
  exact ⟨h1,
    fun N N' hN ho h => by
      simpa only [Relabel.relabelRoot_eq] using Relabel.tKinds_relabel hN ho Γ h,
    fun N N' hN ho h => by
      simpa only [Relabel.relabelRoot_eq] using Relabel.tKindsErr_relabel hN ho Γ h,
    fun C h => (Relabel.normal_mapC hb Γ C).2 h,
    (Relabel.atExternals_mapC hb Γ).2,
    Relabel.doublyConnected_mapC hb Γ,
    (Relabel.labelFree_mapC hb Γ).2,
    (Relabel.isQGraph_mapC hb Γ).2,
    Relabel.isRecollision_mapC hb Γ {1, 2},
    (Relabel.gsPM'_mapC hb Γ).2,
    (Relabel.spdPM'_mapC hb Γ).2,
    (Relabel.extClause_mapC hb Γ).2,
    (Relabel.colourInvB_mapC hb Γ).2,
    (Relabel.qLabelInMISB_mapC hb Γ).2,
    (Relabel.rootAtPlus_mapC hb Γ).2,
    (Relabel.tensorDiffusive_mapC hb Γ).2,
    Relabel.dotExcess_mapC hb Γ,
    (Relabel.noLabDot_mapC hb Γ).2,
    Relabel.labels_mapC hb Γ,
    Relabel.pmBlock_mapC hb Γ,
    (Relabel.rgCheck_mapC hb Γ).2,
    Relabel.diagRecoll_mapC hb Γ,
    (Relabel.rootedAtExt_mapC hb Γ).2,
    (Relabel.plain_mapC hb Γ).2,
    (Relabel.qLabelAtPlus_mapC hb Γ).2,
    (Relabel.minusProfile_mapC hb Γ).2⟩


/-! ## Decidability instances for concrete graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance Relabel_decRootedAtExt {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.RootedAtExt := by
  unfold Graph.RootedAtExt Graph.HasDiffToPinned Graph.DiffToPinned; infer_instance

end Instances

end RBM8D

end
