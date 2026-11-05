import RBM8D.GlobalExp.GlobalGoodRows
import RBM8D.GlobalExp.QFamily
import RBM8D.Graph.QExp.MolMonoSteps
import Batteries.Tactic.OpenPrivate

/-!
# [II, Lemma 6.5] with row (4) read on a family of `Q`-expansions

The statement `globalGoodStmtB'` of [II, Lemma 6.5] (1)–(5) in the block reading, for a plain
graph `G = H.glue x y₁ y₂ (tVar true)`, with the last conjunct of (4) taken over the output graphs
of a family `𝔈` of `Q`-expansions with the clauses `QExpFamilyStmt`, and its proof `globalGoodB'`.
Rows (1), (2), (3), (3′), (5) and the invariant `Graph.InvB'` of the substituted `Q`-graphs are
`globalGood_row1`, `globalGood_row2`, `globalGood_row3`, `globalGood_row5` and
`globalGood_row4_invB`. Row (4) for a graph `g` of `Q`:

* the crossing counts of a set `P` of molecules of `H.glue x y₁ y₂ g.swapSolid`, split into the
  components of `H` and those of `g`, and compared with those of the set of molecules of `G`
  read off `P`;
* the proper isolated subsets of `H.glue x y₁ y₂ g.swapSolid`: each contains the molecule of the
  image of the `Q` label atom of `g`, and has at least two red crossing edges if it contains a
  molecule of an atom of `H` (the proof of [II, Lemma 6.5 (4)]);
* these facts pulled back along the maps `Graph.MolMono` of `O_dot` and of the family (the map
  clause of (F6) of `QExpFamilyStmt`) to the `O_dot` forms and to the output graphs; the output
  graphs without labels whose proper isolated subsets pull back to sets without molecules of `H`
  are weakly isolated by (F6);
* the scaling order `≥ ord G + 1` of the output graphs without labels: by
  [II, Lemma 4.15 (iv)] if no unlabelled weight or solid edge is at the label atom, and otherwise
  from `y₁ ≠ y₂` and the scaling order `≥ 3` of a graph of `Q` whose label lies in the dotted
  block of `⊕` or of `⊖`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private SubstMol_molRep_spec SubstMol_molRep_eq_iff SubstMol_anchor_none SubstMol_flatAtom
  SubstMol_glue_facts SubstMol_lift SubstMol_lift_liftA SubstMol_lift_newA
  SubstMol_glueAtom_isRight SubstMol_liftA_isRight SubstMol_tVar_comps from RBM8D.GlobalExp.SubstMol
open private SubstSPD_unpinned_zero SubstSPD_flat_unpinned SubstSPD_flat_pinned SubstSPD_comp_edge
  SubstSPD_idx SubstSPD_inl_not_int SubstSPD_swap_ends SubstSPD_swap_kind SubstSPD_swap_flatAtom
  SubstSPD_swap_molRep SubstSPD_flat_cases SubstSPD_sameMol_of_comp SubstSPD_molRep_eq
  SubstSPD_host SubstSPD_length_le SubstSPD_allAtoms_nodup SubstSPD_liftA_inj
  SubstSPD_liftA_ne_newA SubstSPD_splitPairs_nil SubstSPD_dotChoice_nil SubstSPD_glue_bal
  SubstSPD_H_nodot SubstSPD_swap_otimesNoDot SubstSPD_swap_dotExcess SubstSPD_swap_labels
  SubstSPD_swap_noLabDot SubstSPD_swap_tensor SubstSPD_swap_sameBlock SubstSPD_swap_pmBlock
  SubstSPD_tVar_ord SubstSPD_mgext from RBM8D.GlobalExp.SubstSPD
open private MolMono_rep_map' from RBM8D.Graph.QExp.MolMono
open private MergeSpec.sameBlock_of_f_eq from RBM8D.Graph.Local.Strategy
open private SubstDC_swap_rgCheck from RBM8D.GlobalExp.SubstDC
open private
  GlobalGoodRows_decAdjDot GlobalGoodRows_decSameBlock GlobalGoodRows_decAdjMol
  GlobalGoodRows_decSameMol GlobalGoodRows_decUnpinned
  GlobalGoodRows_decIsRecollision GlobalGoodRows_decRgCheck
  GlobalGoodRows_decAdjEdge GlobalGoodRows_decAdjWavedTheta
  GlobalGoodRows_decRegular GlobalGoodRows_decNormal
  from RBM8D.GlobalExp.GlobalGoodRows

/-! ## Crossing counts read on the components -/

/-- A kind whose component, between two molecules, is a present edge of the molecular graph
other than a red solid edge: not a dotted edge, of a class other than `minus`. -/
private def GlobalGoodB_nrB (κ : Kind) : Bool :=
  κ != .dot && (κ.mclass.isSome && κ.mclass != some .minus)

open Classical in
/-- The number of components of `L` of a kind of `GlobalGoodB_nrB` whose two ends differ in the
property `p`. -/
private def GlobalGoodB_nc {V : Type*} (p : V → Prop) (L : List (Comp V)) : ℕ :=
  L.countP fun c => GlobalGoodB_nrB c.kind && decide (¬ (p c.x ↔ p c.y))

open Classical in
/-- The number of red solid components of `L` whose two ends differ in the property `p`. -/
private def GlobalGoodB_rc {V : Type*} (p : V → Prop) (L : List (Comp V)) : ℕ :=
  L.countP fun c => decide (c.kind.mclass = some .minus) && decide (¬ (p c.x ↔ p c.y))

private theorem GlobalGoodB_nc_append {V : Type*} (p : V → Prop) (A B : List (Comp V)) :
    GlobalGoodB_nc p (A ++ B) = GlobalGoodB_nc p A + GlobalGoodB_nc p B := by
  unfold GlobalGoodB_nc; rw [List.countP_append]

private theorem GlobalGoodB_rc_append {V : Type*} (p : V → Prop) (A B : List (Comp V)) :
    GlobalGoodB_rc p (A ++ B) = GlobalGoodB_rc p A + GlobalGoodB_rc p B := by
  unfold GlobalGoodB_rc; rw [List.countP_append]

private theorem GlobalGoodB_nc_map {V W : Type*} (p : W → Prop) (f : V → W) (L : List (Comp V)) :
    GlobalGoodB_nc p (L.map (Comp.map f)) = GlobalGoodB_nc (p ∘ f) L := by
  unfold GlobalGoodB_nc
  rw [List.countP_map]
  rfl

private theorem GlobalGoodB_rc_map {V W : Type*} (p : W → Prop) (f : V → W) (L : List (Comp V)) :
    GlobalGoodB_rc p (L.map (Comp.map f)) = GlobalGoodB_rc (p ∘ f) L := by
  unfold GlobalGoodB_rc
  rw [List.countP_map]
  rfl

private theorem GlobalGoodB_nc_congr {V : Type*} {p q : V → Prop} (L : List (Comp V))
    (h : ∀ c ∈ L, GlobalGoodB_nrB c.kind = true → ((p c.x ↔ p c.y) ↔ (q c.x ↔ q c.y))) :
    GlobalGoodB_nc p L = GlobalGoodB_nc q L := by
  classical
  unfold GlobalGoodB_nc
  refine List.countP_congr fun c hc => ?_
  by_cases hk : GlobalGoodB_nrB c.kind = true
  · simp [hk, h c hc hk]
  · simp [hk]

private theorem GlobalGoodB_nc_eq_zero {V : Type*} {p : V → Prop} {L : List (Comp V)} :
    GlobalGoodB_nc p L = 0 ↔ ∀ c ∈ L, GlobalGoodB_nrB c.kind = true → (p c.x ↔ p c.y) := by
  classical
  unfold GlobalGoodB_nc
  rw [List.countP_eq_zero]
  refine forall₂_congr fun c _ => ?_
  by_cases hk : GlobalGoodB_nrB c.kind = true <;> simp [hk]

private theorem GlobalGoodB_rc_pos {V : Type*} {p : V → Prop} {L : List (Comp V)} {c : Comp V}
    (hc : c ∈ L) (hk : c.kind.mclass = some .minus) (h : ¬ (p c.x ↔ p c.y)) :
    1 ≤ GlobalGoodB_rc p L := by
  classical
  unfold GlobalGoodB_rc
  exact List.countP_pos_iff.2 ⟨c, hc, by simp [hk, h]⟩

/-- The count of components with the property, for a property that is the same at the two ends
of every component. -/
private theorem GlobalGoodB_nc_const {V : Type*} {p : V → Prop} {L : List (Comp V)}
    (h : ∀ c ∈ L, (p c.x ↔ p c.y)) : GlobalGoodB_nc p L = 0 :=
  GlobalGoodB_nc_eq_zero.2 fun c hc _ => h c hc

section Read

variable {k n : ℕ}

/-- The crossing count of a set of internal molecules of `Graph.toMG'`, read on the components
(with the ends moved to the block normal form) and on the pin edges. -/
private theorem GlobalGoodB_cross_eq (Γ : Graph k n) (S : Finset (Atom k n)) :
    Γ.toMG'.crossCount S = GlobalGoodB_nc (fun u => Γ.molRep (Γ.flatAtom u) ∈ S) Γ.comps +
      ((List.finRange k).filterMap (MolMono_pinD Γ)).countP
        (fun t => decide (MolMono_crossT Γ.toMG'.int Γ.toMG'.ext S t)) := by
  classical
  rw [MolMono_crossCount_eq]
  unfold MolMono_crossL MolMono_edges
  rw [List.countP_append, List.countP_filterMap]
  congr 1
  unfold GlobalGoodB_nc
  refine List.countP_congr fun c _ => ?_
  unfold MolMono_edgeD
  by_cases hd : c.kind = .dot
  · simp [hd, GlobalGoodB_nrB]
  by_cases he : Γ.molRep (Γ.flatAtom c.x) = Γ.molRep (Γ.flatAtom c.y)
  · simp [hd, he]
  simp only [hd, he, or_self, ite_false]
  have hv1 := MolMono_molRep_isVtx Γ (Γ.flatAtom c.x)
  have hv2 := MolMono_molRep_isVtx Γ (Γ.flatAtom c.y)
  cases hm : c.kind.mclass with
  | none => simp [GlobalGoodB_nrB, hm]
  | some m =>
    simp only [Option.map_some, Option.getD_some, decide_eq_true_eq, MolMono_crossT,
      GlobalGoodB_nrB, hm, bne_iff_ne, ne_eq, hd, not_false_eq_true, Option.isSome_some,
      Option.some.injEq, Bool.true_and, Bool.and_eq_true, decide_not]
    simp only [MGraph.IsVtx] at hv1 hv2
    constructor
    · rintro ⟨h1, -, -, h2⟩
      refine ⟨by simpa using h1, ?_⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      tauto
    · rintro ⟨h1, h2⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h2
      refine ⟨by simpa using h1, hv1, hv2, ?_⟩
      tauto

/-- The red crossing count read on the components and on the pin edges. -/
private theorem GlobalGoodB_red_eq (Γ : Graph k n) (S : Finset (Atom k n)) :
    Γ.toMG'.redCount S = GlobalGoodB_rc (fun u => Γ.molRep (Γ.flatAtom u) ∈ S) Γ.comps +
      ((List.finRange k).filterMap (MolMono_pinD Γ)).countP
        (fun t => decide (MolMono_redT Γ.toMG'.int Γ.toMG'.ext S t)) := by
  classical
  rw [MolMono_redCount_eq]
  unfold MolMono_redL MolMono_edges
  rw [List.countP_append, List.countP_filterMap]
  congr 1
  unfold GlobalGoodB_rc
  refine List.countP_congr fun c _ => ?_
  unfold MolMono_edgeD
  by_cases hd : c.kind = .dot
  · simp [hd, Kind.mclass]
  by_cases he : Γ.molRep (Γ.flatAtom c.x) = Γ.molRep (Γ.flatAtom c.y)
  · simp [hd, he]
  simp only [hd, he, or_self, ite_false]
  have hv1 := MolMono_molRep_isVtx Γ (Γ.flatAtom c.x)
  have hv2 := MolMono_molRep_isVtx Γ (Γ.flatAtom c.y)
  cases hm : c.kind.mclass with
  | none => simp
  | some m =>
    simp only [Option.map_some, Option.getD_some, decide_eq_true_eq, MolMono_redT,
      Option.some.injEq, Bool.and_eq_true, decide_not]
    simp only [MGraph.IsVtx] at hv1 hv2
    constructor
    · rintro ⟨h1, -, -, h2⟩
      refine ⟨h1, ?_⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      tauto
    · rintro ⟨h1, h2⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h2
      exact ⟨h1, hv1, hv2, by tauto⟩

/-- Without dotted edges at external atoms there is no present pin edge. -/
private theorem GlobalGoodB_pins_nil {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) :
    (List.finRange k).filterMap (MolMono_pinD Γ) = [] := by
  refine List.filterMap_eq_nil_iff.2 fun a _ => ?_
  simp [MolMono_pinD, SubstMol_anchor_none hd a]

/-- Without dotted edges at external atoms, the crossing count read on the components. -/
private theorem GlobalGoodB_cross_eq' {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (S : Finset (Atom k n)) :
    Γ.toMG'.crossCount S = GlobalGoodB_nc (fun u => Γ.molRep u ∈ S) Γ.comps := by
  rw [GlobalGoodB_cross_eq, GlobalGoodB_pins_nil hd]
  simp [SubstMol_flatAtom hd]

/-- Without dotted edges at external atoms, the red crossing count read on the components. -/
private theorem GlobalGoodB_red_eq' {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true)
    (S : Finset (Atom k n)) :
    Γ.toMG'.redCount S = GlobalGoodB_rc (fun u => Γ.molRep u ∈ S) Γ.comps := by
  rw [GlobalGoodB_red_eq, GlobalGoodB_pins_nil hd]
  simp [SubstMol_flatAtom hd]

end Read

/-! ## Isolated subsets from the counts -/

section Iso

variable {V E : Type} [DecidableEq V] [Fintype E]

private theorem GlobalGoodB_count_of_iso (G : MGraph V E) {P : Finset V} (h : G.IsIsolated P) :
    G.crossCount P = 2 := by
  classical
  obtain ⟨-, e₁, e₂, hne, hc⟩ := h
  have : Finset.univ.filter (G.Crosses P) = {e₁, e₂} := by
    ext e
    simp [hc]
  unfold MGraph.crossCount
  rw [this, Finset.card_pair hne]

private theorem GlobalGoodB_iso_of_count (G : MGraph V E) {P : Finset V} (hP : P ⊆ G.int)
    (h : G.crossCount P = 2) : G.IsIsolated P := by
  classical
  unfold MGraph.crossCount at h
  obtain ⟨e₁, e₂, hne, heq⟩ := Finset.card_eq_two.1 h
  refine ⟨hP, e₁, e₂, hne, fun e => ?_⟩
  have := Finset.ext_iff.1 heq e
  simpa using this

private theorem GlobalGoodB_weak_iff (G : MGraph V E) {P : Finset V} :
    G.IsWeaklyIso P ↔ G.IsIsolated P ∧ 2 ≤ G.redCount P := by
  classical
  unfold MGraph.IsWeaklyIso MGraph.redCount
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨e, e', hne, h1, h2⟩
    have : ({e, e'} : Finset E) ⊆ Finset.univ.filter (G.RedCrosses P) := by
      intro f hf
      rcases Finset.mem_insert.1 hf with rfl | hf
      · simpa using h1
      · rw [Finset.mem_singleton.1 hf]; simpa using h2
    have := Finset.card_le_card this
    rwa [Finset.card_pair hne] at this
  · intro h
    have h1 : 1 < (Finset.univ.filter (G.RedCrosses P)).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1
    exact ⟨a, b, hab, (Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2⟩

/-- In a doubly connected graph a proper nonempty set of internal vertices has crossing count
at least `2`. -/
private theorem GlobalGoodB_two_le_of_DC (G : MGraph V E) (hG : G.DC) {S : Finset V}
    (hS : S ⊆ G.int)
    (hne : S.Nonempty) (hns : ¬ G.int ⊆ S) : 2 ≤ G.crossCount S :=
  (G.two_le_cHat_of_DC hG hS hne hns).trans (G.cHat_le_crossCount hS)

omit [DecidableEq V] [Fintype E] in
/-- An isolated subset is nonempty. -/
private theorem GlobalGoodB_iso_nonempty (G : MGraph V E) {P : Finset V} (h : G.IsIsolated P) :
    P.Nonempty := by
  obtain ⟨-, e₁, e₂, -, hc⟩ := h
  obtain ⟨-, -, -, -, hcut⟩ := (hc e₁).2 (Or.inl rfl)
  rcases hcut with h' | h'
  · exact ⟨_, h'.1⟩
  · exact ⟨_, h'.2⟩

omit [DecidableEq V] [Fintype E] in
/-- A proper isolated subset contains the minimal isolated subset. -/
private theorem GlobalGoodB_mis_sub (G : MGraph V E) {P : Finset V} (h : G.IsProperIso G.int P) :
    G.MIS ⊆ P := by
  classical
  intro v hv
  simp only [MGraph.MIS, Finset.mem_filter] at hv
  exact hv.2 P h

end Iso

/-! ## The counts of a substituted graph and of the graph with the `t`-variable -/

section Glue

variable {m n' : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')

private theorem GlobalGoodB_glue_comps :
    (H.glue x y₁ y₂ g).comps =
      H.comps.map (Comp.map (liftA n')) ++ g.comps.map (Comp.map (glueAtom x y₁ y₂)) := rfl

private theorem GlobalGoodB_G_comps :
    (H.glue x y₁ y₂ (tVar true)).comps = H.comps.map (Comp.map (liftA 1)) ++
      [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
        mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
        mkC .xdot (liftA 1 y₂) (newA 0)] := by
  simp [Graph.glue, liftCs, tVar, tVarGraph, Graph.swapEnds, mkC, Comp.map, glueAtom]

private theorem GlobalGoodB_lift_liftA (u : Atom 3 m) :
    SubstMol_lift n' x (liftA 1 u) = liftA n' u := SubstMol_lift_liftA n' x u

private theorem GlobalGoodB_lift_newA : SubstMol_lift n' x (newA (0 : Fin 1)) = liftA n' x :=
  SubstMol_lift_newA n' x

variable {H x y₁ y₂ g}

/-- The two crossing counts of a set `P` of internal molecules of `H.glue x y₁ y₂ g`, split into
the components of `H` and those of `g`, read on the property "the molecule lies in `P`". -/
private theorem GlobalGoodB_Gt_counts (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hx : x.isRight = true) (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    (P : Finset (Atom 3 (m + n'))) :
    let p := fun u => (H.glue x y₁ y₂ g).molRep u ∈ P
    (H.glue x y₁ y₂ g).toMG'.crossCount P =
        GlobalGoodB_nc (p ∘ liftA n') H.comps + GlobalGoodB_nc (p ∘ glueAtom x y₁ y₂) g.comps ∧
      (H.glue x y₁ y₂ g).toMG'.redCount P =
        GlobalGoodB_rc (p ∘ liftA n') H.comps + GlobalGoodB_rc (p ∘ glueAtom x y₁ y₂) g.comps := by
  intro p
  obtain ⟨-, hdt, -⟩ := SubstMol_glue_facts H x y₁ y₂ g hD hx hy₁ hy₂
  rw [GlobalGoodB_cross_eq' hdt, GlobalGoodB_red_eq' hdt, GlobalGoodB_glue_comps,
    GlobalGoodB_nc_append, GlobalGoodB_rc_append, GlobalGoodB_nc_map, GlobalGoodB_nc_map,
    GlobalGoodB_rc_map, GlobalGoodB_rc_map]
  exact ⟨rfl, rfl⟩

/-- The set of molecules of `G = H.glue x y₁ y₂ (tVar true)` read off a set `P` of molecules of
`H.glue x y₁ y₂ g`: a molecule of `G` lies in it when the molecule of its atom in
`H.glue x y₁ y₂ g` lies in `P` (the atom `α` read as `x`). -/
private def GlobalGoodB_S (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')
    (P : Finset (Atom 3 (m + n'))) : Finset (Atom 3 (m + 1)) :=
  (H.glue x y₁ y₂ (tVar true)).toMG'.int.filter fun M =>
    (H.glue x y₁ y₂ g).molRep (SubstMol_lift n' x M) ∈ P

private theorem GlobalGoodB_mem_S (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hx : x.isRight = true) (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    {P : Finset (Atom 3 (m + n'))} (hP : P ⊆ (H.glue x y₁ y₂ g).toMG'.int)
    (u : Atom 3 (m + 1)) :
    (H.glue x y₁ y₂ (tVar true)).molRep u ∈ GlobalGoodB_S H x y₁ y₂ g P ↔
      (H.glue x y₁ y₂ g).molRep (SubstMol_lift n' x u) ∈ P := by
  obtain ⟨-, -, M1, -⟩ := SubstMol_glue_facts H x y₁ y₂ g hD hx hy₁ hy₂
  rcases u with a | i
  · constructor
    · intro h
      exact absurd (Finset.mem_filter.1 h).1 (MolMono_inl_not_mem_int _ a)
    · intro h
      exact absurd (hP h) (MolMono_inl_not_mem_int _ a)
  · simp only [GlobalGoodB_S, Finset.mem_filter, MolMono_molRep_mem_int, true_and]
    rw [M1]

/-- The two crossing counts of the set `GlobalGoodB_S` in `G = H.glue x y₁ y₂ (tVar true)`: the
components of `H` as in `GlobalGoodB_Gt_counts`, and the edges `G_{y₁α}` (blue) and `Ḡ_{y₂α}`
(red) of the `t`-variable, with `α` read as `x`. -/
private theorem GlobalGoodB_G_counts (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hx : x.isRight = true) (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    {P : Finset (Atom 3 (m + n'))} (hP : P ⊆ (H.glue x y₁ y₂ g).toMG'.int) :
    let p := fun u => (H.glue x y₁ y₂ g).molRep u ∈ P
    (H.glue x y₁ y₂ (tVar true)).toMG'.crossCount (GlobalGoodB_S H x y₁ y₂ g P) =
        GlobalGoodB_nc (p ∘ liftA n') H.comps +
          (if (p (liftA n' y₁) ↔ p (liftA n' x)) then 0 else 1) ∧
      (H.glue x y₁ y₂ (tVar true)).toMG'.redCount (GlobalGoodB_S H x y₁ y₂ g P) =
        GlobalGoodB_rc (p ∘ liftA n') H.comps +
          (if (p (liftA n' y₂) ↔ p (liftA n' x)) then 0 else 1) := by
  intro p
  obtain ⟨hdG, -⟩ := SubstMol_glue_facts H x y₁ y₂ g hD hx hy₁ hy₂
  have hmem := GlobalGoodB_mem_S hD hx hy₁ hy₂ hP
  have hs : (fun u => (H.glue x y₁ y₂ (tVar true)).molRep u ∈ GlobalGoodB_S H x y₁ y₂ g P) =
      p ∘ SubstMol_lift n' x := funext fun u => propext (hmem u)
  rw [GlobalGoodB_cross_eq' hdG, GlobalGoodB_red_eq' hdG, hs, GlobalGoodB_G_comps,
    GlobalGoodB_nc_append, GlobalGoodB_rc_append, GlobalGoodB_nc_map, GlobalGoodB_rc_map]
  have hl : (p ∘ SubstMol_lift n' x) ∘ liftA 1 = p ∘ liftA n' :=
    funext fun u => by simp only [Function.comp, GlobalGoodB_lift_liftA]
  rw [hl]
  have hα : (p ∘ SubstMol_lift n' x) (newA (0 : Fin 1)) = p (liftA n' x) := by
    simp only [Function.comp, GlobalGoodB_lift_newA]
  have hY : ∀ y : Atom 3 m, (p ∘ SubstMol_lift n' x) (liftA 1 y) = p (liftA n' y) := fun y => by
    simp only [Function.comp, GlobalGoodB_lift_liftA]
  refine ⟨congrArg _ ?_, congrArg _ ?_⟩
  · classical
    unfold GlobalGoodB_nc
    simp only [List.countP_cons, List.countP_nil, mkC, GlobalGoodB_nrB, Kind.mclass, hα, hY]
    split_ifs <;> simp_all
  · classical
    unfold GlobalGoodB_rc
    simp only [List.countP_cons, List.countP_nil, mkC, Kind.mclass, hα, hY]
    split_ifs <;> simp_all

end Glue

/-! ## Properties constant along components -/

section Const

variable {k n : ℕ}

/-- A property with the same value at the two ends of every edge of a graph on the atoms has the
same value at atoms joined by a path. -/
private theorem GlobalGoodB_reach_iff {V : Type*} {G : SimpleGraph V} (f : V → Prop)
    (h : ∀ u v, G.Adj u v → (f u ↔ f v)) {u v : V} (huv : G.Reachable u v) : (f u ↔ f v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => exact Iff.rfl
  | tail _ hab ih => exact ih.trans (h _ _ hab)

/-- The property `f` has the same value at the two ends of every component of a kind of
`GlobalGoodB_nrB` or a waved or dotted component. -/
private def GlobalGoodB_Inv (Γ : Graph k n) (f : Atom k n → Prop) : Prop :=
  ∀ c ∈ Γ.comps, (GlobalGoodB_nrB c.kind = true ∨ c.kind.joinsMol = true) → (f c.x ↔ f c.y)

private theorem GlobalGoodB_Inv.dot {Γ : Graph k n} {f : Atom k n → Prop} (hf : GlobalGoodB_Inv Γ f)
    {u v : Atom k n} (h : Γ.SameBlock u v) : (f u ↔ f v) := by
  refine GlobalGoodB_reach_iff f (fun a b hab => ?_) h
  rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩
  · exact hf c hc (Or.inr (by rw [hk]; rfl))
  · exact (hf c hc (Or.inr (by rw [hk]; rfl))).symm

private theorem GlobalGoodB_nrB_diff {κ : Kind} (h : κ.isDiffusive = true) :
    GlobalGoodB_nrB κ = true := by
  cases κ <;> simp_all [Kind.isDiffusive, GlobalGoodB_nrB, Kind.mclass]

private theorem GlobalGoodB_Inv.wt {Γ : Graph k n} {f : Atom k n → Prop} (hf : GlobalGoodB_Inv Γ f)
    {u v : Atom k n} (h : Γ.wavedThetaGraph.Reachable u v) : (f u ↔ f v) := by
  refine GlobalGoodB_reach_iff f (fun a b hab => ?_) h
  rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hab
  have key : ∀ c ∈ Γ.comps, ((c.kind.joinsMol = true ∧ c.kind ≠ .dot) ∨
      c.kind.isDiffusive = true) → (f c.x ↔ f c.y) := by
    rintro c hc (⟨hj, -⟩ | hd)
    · exact hf c hc (Or.inr hj)
    · exact hf c hc (Or.inl (GlobalGoodB_nrB_diff hd))
  rcases hab.2 with ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩
  · exact key c hc hk
  · exact (key c hc hk).symm

/-- An atom identified with an internal atom has the value of `f` of an internal atom. -/
private theorem GlobalGoodB_Inv.pinned {Γ : Graph k n} {f : Atom k n → Prop}
    (hf : GlobalGoodB_Inv Γ f)
    {v : Atom k n} (h : ¬ Γ.Unpinned v) : ∃ j : Fin n, (f v ↔ f (.inr j)) := by
  rcases v with a | j
  · have : ∃ b, Γ.SameBlock (.inl a) (.inr b) := by
      by_contra hn
      push Not at hn
      exact h ⟨rfl, hn⟩
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hf.dot hb⟩
  · exact ⟨j, Iff.rfl⟩

end Const

/-! ## The atoms of a graph of `Q` joined to `⊗` -/

section Conn

variable {n : ℕ} {Γ : Graph 3 n}

/-- **The atoms of a graph of `Q` joined to `⊗`.** For a normal regular graph with only diffusive
edges at `⊗` and [II, Def 3.2 (9)], with the clause on the external atoms and the charge pattern
of the block normal form, or without internal atom and with its diffusive edge at `⊗` ending at
`⊕`: a property with the same value at the two ends of every component that is a waved, dotted,
diffusive, blue solid or ghost edge has at `⊕` and at every internal atom its value at `⊗`. -/
private theorem GlobalGoodB_conn {C : ℕ} (hN : Γ.Normal C) (hT : Γ.TensorDiffusive)
    (hA : Γ.AtExternals)
    (hcase : (n = 0 ∧ Γ.RootAtPlus) ∨ (Γ.ExtClause ∧ Γ.ColourInvB)) {f : Atom 3 n → Prop}
    (hf : GlobalGoodB_Inv Γ f) :
    (f (.inl 1) ↔ f (.inl 0)) ∧ ∀ j : Fin n, (f (.inr j) ↔ f (.inl 0)) := by
  rcases hcase with ⟨rfl, hR⟩ | ⟨hE, hC⟩
  · refine ⟨?_, fun j => j.elim0⟩
    have hlen := hA.1
    obtain ⟨c, hc⟩ : ∃ c, c ∈ Γ.comps.filter fun c =>
        c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0) := by
      rcases h : Γ.comps.filter (fun c => c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0))
        with _ | ⟨c, l⟩
      · rw [h] at hlen; simp at hlen
      · exact ⟨c, by rw [h]; exact List.mem_cons_self⟩
    obtain ⟨hcm, hcp⟩ := List.mem_filter.1 hc
    simp only [Bool.and_eq_true] at hcp
    have hr := List.all_eq_true.1 hR c hcm
    simp only [hcp.1, hcp.2, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq] at hr
    have h := hf c hcm (Or.inl (GlobalGoodB_nrB_diff hcp.1))
    rcases hr with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy] at h; exact h.symm
    · rw [hx, hy] at h; exact h
  · have hint : ∀ i j : Fin n, (f (.inr i) ↔ f (.inr j)) := fun i j =>
      hf.wt (hN.1.internal i j)
    have hU0 := SubstSPD_unpinned_zero Γ hT
    obtain ⟨c, hc, hd, hat⟩ := (hE.2.2.1 hU0).1
    have h0 : ∃ j : Fin n, (f (.inl 0) ↔ f (.inr j)) := by
      have hcf := hf c hc (Or.inl (GlobalGoodB_nrB_diff hd))
      rcases hat with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · obtain ⟨j, hj⟩ := hf.pinned hy
        rw [hx] at hcf
        exact ⟨j, hcf.trans hj⟩
      · obtain ⟨j, hj⟩ := hf.pinned hx
        rw [hy] at hcf
        exact ⟨j, hcf.symm.trans hj⟩
    obtain ⟨j₀, hj₀⟩ := h0
    have h1 : ∃ j : Fin n, (f (.inl 1) ↔ f (.inr j)) := by
      by_cases hU1 : Γ.Unpinned (.inl 1)
      · obtain ⟨hb | hb, -⟩ := hE.2.2.2.2 hU1
        · obtain ⟨c, hc, hk, hat⟩ := hb
          have hci := (hC (Γ.flatComp c) (List.mem_map.2 ⟨c, hc, rfl⟩)).1
            (by rw [Graph.flatComp_kind, hk]; rfl)
          have hfx : (Γ.flatAtom c.x).isRight = true := by
            have := hci.1
            simpa [Graph.flatComp, hk] using this
          have hcf := hf c hc (Or.inl (by rw [hk]; rfl))
          rcases hat with hx | hy
          · rw [hx, SubstSPD_flat_unpinned Γ hU1] at hfx
            simp at hfx
          · have hpx : ¬ Γ.Unpinned c.x := by
              intro hu
              rcases hcx : c.x with a | b
              · rw [hcx] at hu hfx
                rw [SubstSPD_flat_unpinned Γ hu] at hfx
                simp at hfx
              · rw [hcx] at hu
                simp [Graph.Unpinned] at hu
            obtain ⟨j, hj⟩ := hf.pinned hpx
            rw [hy] at hcf
            exact ⟨j, hcf.symm.trans hj⟩
        · obtain ⟨c, hc, hd, hat⟩ := hb
          have hcf := hf c hc (Or.inl (GlobalGoodB_nrB_diff hd))
          rcases hat with ⟨hx, hy⟩ | ⟨hy, hx⟩
          · obtain ⟨j, hj⟩ := hf.pinned hy
            rw [hx] at hcf
            exact ⟨j, hcf.trans hj⟩
          · obtain ⟨j, hj⟩ := hf.pinned hx
            rw [hy] at hcf
            exact ⟨j, hcf.symm.trans hj⟩
      · exact hf.pinned hU1
    obtain ⟨j₁, hj₁⟩ := h1
    exact ⟨hj₁.trans ((hint j₁ j₀).trans hj₀.symm), fun j => (hint j j₀).trans hj₀.symm⟩

/-- **A red solid edge on a path.** On a normal regular plain graph with the kinds of
[II, Def 3.2], a property with the same value at the two ends of every waved, dotted, diffusive,
blue solid or ghost component and with different values at two atoms has different values at
the two ends of some red solid edge. -/
private theorem GlobalGoodB_red_walk {C N : ℕ} (hN : Γ.Normal C) (hP : Γ.Plain) (hTK : Γ.TKinds N)
    {f : Atom 3 n → Prop} (hf : GlobalGoodB_Inv Γ f) (u v : Atom 3 n) (hne : ¬ (f u ↔ f v)) :
    ∃ c ∈ Γ.comps, c.kind.mclass = some .minus ∧ ¬ (f c.x ↔ f c.y) := by
  by_contra hcon
  push Not at hcon
  have hcomp : ∀ c ∈ Γ.comps, c.x ≠ c.y → (f c.x ↔ f c.y) := by
    intro c hc hxy
    have htk := List.all_eq_true.1 hTK c hc
    have hpl := hP c hc
    have hsolid : ∀ c' ∈ Γ.comps, c'.kind.isSolid = true → (f c'.x ↔ f c'.y) := by
      intro c' hc' hs
      obtain ⟨ch, hch⟩ : ∃ ch, c'.kind = .G ch := by
        cases hk : c'.kind <;> simp_all [Kind.isSolid]
      cases ch with
      | plus => exact hf c' hc' (Or.inl (by rw [hch]; rfl))
      | minus => exact hcon c' hc' (by rw [hch]; rfl)
    unfold Comp.isTKind at htk
    cases hk : c.kind with
    | G ch => exact hsolid c hc (by rw [hk]; rfl)
    | weight ch => exact absurd (hpl.2.2.2.2.1 (by rw [hk]; rfl)).symm hxy
    | light ch => exact absurd (hpl.2.2.2.2.1 (by rw [hk]; rfl)).symm hxy
    | waved w => exact hf c hc (Or.inr (by rw [hk]; rfl))
    | dot => exact hf c hc (Or.inr (by rw [hk]; rfl))
    | theta o => exact hf c hc (Or.inl (by rw [hk]; rfl))
    | xdot =>
      obtain ⟨c', hc', hs, he⟩ := (hN.2.2 c.x c.y hxy).1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
      have := hsolid c' hc' hs
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at this; exact this
      · rw [h1, h2] at this; exact this.symm
    | _ => simp [hk] at htk
  exact hne (GlobalGoodB_reach_iff f (fun a b hab => by
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with ⟨c, hc, rfl, rfl⟩ | ⟨c, hc, rfl, rfl⟩
    · exact hcomp c hc hab.1
    · exact (hcomp c hc (Ne.symm hab.1)).symm) (hN.1.connected u v))

end Conn

/-! ## Two crossing edges at the external atoms -/

section Ext

variable {n : ℕ} {Γ : Graph 3 n}

/-- At an unpinned external atom `a`, a component from `a` to an internal or identified atom whose
kind has a class other than `minus` crosses the set of all internal molecules. -/
private theorem GlobalGoodB_ext_edge {a : Fin 3} (ha : Γ.Unpinned (.inl a)) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hk : c.kind ≠ .dot) (hm : c.kind.mclass ≠ none)
    (hmm : c.kind.mclass ≠ some .minus)
    (he : (c.x = .inl a ∧ (Γ.flatAtom c.y).isRight = true) ∨
      (c.y = .inl a ∧ (Γ.flatAtom c.x).isRight = true)) :
    ∃ i : Fin Γ.comps.length, Γ.toMG'.Crosses Γ.toMG'.int (.inl i) ∧
      ∃ v ∈ Γ.toMG'.int, Γ.toMG'.ends (.inl i) = (.inl a, v) ∨
        Γ.toMG'.ends (.inl i) = (v, .inl a) := by
  obtain ⟨i, rfl⟩ := SubstSPD_idx hc
  obtain ⟨⟨v, hv, hends⟩, hcls⟩ := SubstSPD_comp_edge Γ ha i hk he
  have hna := SubstSPD_inl_not_int Γ a
  refine ⟨i, ⟨by rw [hcls]; exact hm, by rw [hcls]; exact hmm, ?_, ?_, ?_⟩, v, hv, hends⟩
  · rcases hends with h | h <;> rw [h]
    · exact Or.inr ((MolMono_mem_ext Γ _).2 ⟨a, rfl⟩)
    · exact Or.inl hv
  · rcases hends with h | h <;> rw [h]
    · exact Or.inl hv
    · exact Or.inr ((MolMono_mem_ext Γ _).2 ⟨a, rfl⟩)
  · unfold MGraph.Cut
    rcases hends with h | h <;> rw [h]
    · exact Or.inr ⟨hna, hv⟩
    · exact Or.inl ⟨hv, hna⟩

/-- **Two crossing edges of the set of all internal molecules.** A graph with the clause on the
external atoms and the charge pattern of the block normal form, with `⊗` and `⊕` not identified
with internal atoms, has an edge from `⊗` and an edge from `⊕` to internal molecules in its
molecular graph, other than red solid edges. -/
private theorem GlobalGoodB_two_ext (hE : Γ.ExtClause) (hC : Γ.ColourInvB)
    (hU0 : Γ.Unpinned (.inl 0)) (hU1 : Γ.Unpinned (.inl 1)) :
    2 ≤ Γ.toMG'.crossCount Γ.toMG'.int := by
  classical
  have hpin : ∀ v : Atom 3 n, ¬ Γ.Unpinned v → (Γ.flatAtom v).isRight = true :=
    fun v hv => SubstSPD_flat_pinned Γ hv
  have hdiff : ∀ {κ : Kind}, κ.isDiffusive = true → κ ≠ .dot ∧ κ.mclass ≠ none ∧
      κ.mclass ≠ some .minus := by
    intro κ h
    cases κ <;> simp_all [Kind.isDiffusive, Kind.mclass]
  -- the edge at `⊗`
  obtain ⟨c, hc, hd, hat⟩ := (hE.2.2.1 hU0).1
  obtain ⟨hk0, hm0, hmm0⟩ := hdiff hd
  obtain ⟨i₀, hc₀, v₀, hv₀, he₀⟩ := GlobalGoodB_ext_edge hU0 hc hk0 hm0 hmm0 (by
    rcases hat with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, hpin _ h2⟩
    · exact Or.inr ⟨h1, hpin _ h2⟩)
  -- the edge at `⊕`
  have h1 : ∃ i : Fin Γ.comps.length, Γ.toMG'.Crosses Γ.toMG'.int (.inl i) ∧
      ∃ v ∈ Γ.toMG'.int, Γ.toMG'.ends (.inl i) = (.inl 1, v) ∨
        Γ.toMG'.ends (.inl i) = (v, .inl 1) := by
    obtain ⟨hb | hb, -⟩ := hE.2.2.2.2 hU1
    · obtain ⟨c, hc, hk, hat⟩ := hb
      have hci := (hC (Γ.flatComp c) (List.mem_map.2 ⟨c, hc, rfl⟩)).1
        (by rw [Graph.flatComp_kind, hk]; rfl)
      have hfx : (Γ.flatAtom c.x).isRight = true := by
        have := hci.1
        simpa [Graph.flatComp, hk] using this
      refine GlobalGoodB_ext_edge hU1 hc (by rw [hk]; simp) (by rw [hk]; simp [Kind.mclass])
        (by rw [hk]; simp [Kind.mclass]) ?_
      rcases hat with hx | hy
      · rw [hx, SubstSPD_flat_unpinned Γ hU1] at hfx
        simp at hfx
      · exact Or.inr ⟨hy, hfx⟩
    · obtain ⟨c, hc, hd, hat⟩ := hb
      obtain ⟨hk, hm, hmm⟩ := hdiff hd
      refine GlobalGoodB_ext_edge hU1 hc hk hm hmm ?_
      rcases hat with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hpin _ h2⟩
      · exact Or.inr ⟨h1, hpin _ h2⟩
  obtain ⟨i₁, hc₁, v₁, hv₁, he₁⟩ := h1
  have hne : (Sum.inl i₀ : Fin Γ.comps.length ⊕ Fin 3) ≠ .inl i₁ := by
    intro h
    rw [h] at he₀
    have hn0 := SubstSPD_inl_not_int Γ 0
    have hn1 := SubstSPD_inl_not_int Γ 1
    rcases he₀ with h0 | h0 <;> rcases he₁ with h1 | h1 <;> rw [h1] at h0 <;>
      simp only [Prod.mk.injEq] at h0
    · exact absurd h0.1 (by simp)
    · exact hn0 (h0.1 ▸ hv₁)
    · exact hn1 (h0.1 ▸ hv₀)
    · exact absurd h0.2 (by simp)
  have hsub : ({.inl i₀, .inl i₁} : Finset (Fin Γ.comps.length ⊕ Fin 3)) ⊆
      Finset.univ.filter (Γ.toMG'.Crosses Γ.toMG'.int) := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · simpa using hc₀
    · rw [Finset.mem_singleton.1 he]; simpa using hc₁
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  exact this

end Ext

/-! ## Counts along the transposition of the solid edges -/

private theorem GlobalGoodB_swap_kind {V : Type*} (c : Comp V) : c.swapSolid.kind = c.kind := by
  unfold Comp.swapSolid; split <;> rfl

private theorem GlobalGoodB_swap_ends {V : Type*} (c : Comp V) :
    (c.swapSolid.x = c.x ∧ c.swapSolid.y = c.y) ∨ (c.swapSolid.x = c.y ∧ c.swapSolid.y = c.x) := by
  unfold Comp.swapSolid
  split
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- The minimal isolated subset consists of internal vertices. -/
private theorem GlobalGoodB_mis_int {V E : Type} (G : MGraph V E) : G.MIS ⊆ G.int := by
  classical
  unfold MGraph.MIS; exact Finset.filter_subset _ _

private theorem GlobalGoodB_ite_t {c : Prop} [Decidable c] (h : c) (a b : ℕ) :
    (if c then a else b) = a := by simp [h]

private theorem GlobalGoodB_ite_f {c : Prop} [Decidable c] (h : ¬ c) (a b : ℕ) :
    (if c then a else b) = b := by simp [h]

private theorem GlobalGoodB_nc_swap {V : Type*} (p : V → Prop) (L : List (Comp V)) :
    GlobalGoodB_nc p (L.map Comp.swapSolid) = GlobalGoodB_nc p L := by
  classical
  unfold GlobalGoodB_nc
  rw [List.countP_map]
  refine List.countP_congr fun c _ => ?_
  simp only [Function.comp, GlobalGoodB_swap_kind]
  rcases GlobalGoodB_swap_ends c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr Iff.rfl (not_congr Iff.comm)

private theorem GlobalGoodB_rc_swap {V : Type*} (p : V → Prop) (L : List (Comp V)) :
    GlobalGoodB_rc p (L.map Comp.swapSolid) = GlobalGoodB_rc p L := by
  classical
  unfold GlobalGoodB_rc
  rw [List.countP_map]
  refine List.countP_congr fun c _ => ?_
  simp only [Function.comp, GlobalGoodB_swap_kind]
  rcases GlobalGoodB_swap_ends c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr Iff.rfl (not_congr Iff.comm)

/-! ## The isolated subsets of a substituted `Q`-graph -/

section Classify

variable {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m} {g : Graph 3 n'}

/-- The internal molecules of `H.glue x y₁ y₂ g` are those of the atoms of `H` and those of the
atoms of `g`. -/
private theorem GlobalGoodB_Gt_int {M : Atom 3 (m + n')} (hM : M ∈ (H.glue x y₁ y₂ g).toMG'.int) :
    (∃ h : Fin m, M = (H.glue x y₁ y₂ g).molRep (liftA n' (.inr h))) ∨
      ∃ j : Fin n', M = (H.glue x y₁ y₂ g).molRep (glueAtom x y₁ y₂ (.inr j)) := by
  obtain ⟨a, rfl⟩ := (MolMono_mem_int _ M).1 hM
  by_cases ha : a.val < m
  · refine Or.inl ⟨⟨a.val, ha⟩, ?_⟩
    congr 1
  · refine Or.inr ⟨⟨a.val - m, by omega⟩, ?_⟩
    congr 1
    change Sum.inr a = Sum.inr (Fin.natAdd m ⟨a.val - m, _⟩)
    congr 1
    ext
    simp only [Fin.natAdd_mk]
    omega

variable (hD : (H.glue x y₁ y₂ (tVar true)).DotFree) (hx : x.isRight = true)
  (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
include hD hx hy₁ hy₂

omit hD in
/-- Waved and dotted components of `g` join atoms whose images lie in one molecule of
`H.glue x y₁ y₂ g.swapSolid`. -/
private theorem GlobalGoodB_mol_inv (P : Finset (Atom 3 (m + n'))) {c : Comp (Atom 3 n')}
    (hc : c ∈ g.comps) (hj : c.kind.joinsMol = true) :
    ((H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ c.x) ∈ P ↔
      (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ c.y) ∈ P) := by
  have hns : c.kind.isSolid = false := by
    cases hk : c.kind <;> simp_all [Kind.joinsMol, Kind.isSolid]
  have hcs : c.swapSolid = c := by simp [Comp.swapSolid, hns]
  have hmem : c.map (glueAtom x y₁ y₂) ∈ (H.glue x y₁ y₂ g.swapSolid).comps := by
    rw [GlobalGoodB_glue_comps]
    refine List.mem_append_right _ (List.mem_map.2 ⟨c, ?_, rfl⟩)
    exact List.mem_map.2 ⟨c, hc, hcs⟩
  have hgR := SubstMol_glueAtom_isRight (n' := n') hx hy₁ hy₂
  rw [SubstSPD_molRep_eq (hgR _) (hgR _)
    (SubstSPD_sameMol_of_comp hmem hj (hgR c.x) (hgR c.y))]

/-- The molecule of an atom of `g` and of its representative have images in one molecule of
`H.glue x y₁ y₂ g.swapSolid`; likewise an external atom of `g` and its atom in the block normal
form. -/
private theorem GlobalGoodB_glue_molRep (u : Atom 3 n') :
    (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ (g.molRep u)) =
        (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ u) ∧
      (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ (g.flatAtom u)) =
        (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ u) := by
  obtain ⟨-, -, -, -, M4, M6⟩ := SubstMol_glue_facts H x y₁ y₂ g.swapSolid hD hx hy₁ hy₂
  refine ⟨?_, by rw [← SubstSPD_swap_flatAtom g u]; exact M6 u⟩
  rw [SubstMol_molRep_eq_iff]
  refine M4 _ _ ?_
  rw [(swapSolid_basic 3 n' g).2.2.2.2.1]
  exact (g.sameMol_equivalence).symm (SubstMol_molRep_spec g u)

/-- The set `Q` of molecules of `g` whose images lie in `P`, read on the block normal form of
`g`: an atom has its molecule in `Q` exactly when its image has its molecule in `P`, provided no
external atom of `g` has its image in `P`. -/
private theorem GlobalGoodB_q_iff (P : Finset (Atom 3 (m + n')))
    (h0 : ∀ a : Fin 3,
      (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ (.inl a)) ∉ P) (u : Atom 3 n') :
    g.molRep (g.flatAtom u) ∈ g.toMG'.int.filter
        (fun M => (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ M) ∈ P) ↔
      (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ u) ∈ P := by
  have hm := GlobalGoodB_glue_molRep (g := g) hD hx hy₁ hy₂
  rcases SubstSPD_flat_cases g u with hr | ⟨a, rfl, -, hfl⟩
  · obtain ⟨j, hj⟩ : ∃ j, g.flatAtom u = .inr j := by
      rcases h : g.flatAtom u with a | j
      · rw [h] at hr; simp at hr
      · exact ⟨j, rfl⟩
    rw [hj, Finset.mem_filter, and_iff_right (MolMono_molRep_mem_int g j), (hm (.inr j)).1, ← hj,
      (hm u).2]
  · rw [hfl, Finset.mem_filter]
    exact ⟨fun h => absurd h.1 (MolMono_inl_not_mem_int g a), fun h => absurd h (h0 a)⟩

/-- **The classification of the proper isolated subsets of a substituted `Q`-graph**
([II, Lemma 6.5 (4)]). Let `G = H.glue x y₁ y₂ (tVar true)` be without dotted edges, with the
invariant `Graph.InvB'`, globally standard in the block reading, with the blue solid edge
`G_{y₁α}` chosen by Step 2, and let `g` be a normal regular plain graph of the kinds of
[II, Def 3.2], with [II, Def 3.2 (9)], only diffusive edges at `⊗`, the clause on the external
atoms and the charge pattern of the block normal form or no internal atom and the diffusive edge
`Θ_{⊗⊕}`, with `Graph.QLabelInMISB`, and with its `Q` labels at `⊕` if it has no internal atom.
Then every proper isolated subset `P` of the molecular graph of `H.glue x y₁ y₂ g.swapSolid`
contains the molecule of the image of every `Q` label atom of `g`, and has at least two red
crossing edges if it contains the molecule of an atom of `H`. -/
private theorem GlobalGoodB_classify
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hgs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    {C N : ℕ} (hN : g.Normal C) (hT : g.TensorDiffusive) (hA : g.AtExternals)
    (hcase : (n' = 0 ∧ g.RootAtPlus) ∨ (g.ExtClause ∧ g.ColourInvB)) (hPl : g.Plain)
    (hTK : g.TKinds N) (hQL : g.QLabelInMISB) (hQP : n' = 0 → g.QLabelAtPlus)
    {P : Finset (Atom 3 (m + n'))}
    (hP : (H.glue x y₁ y₂ g.swapSolid).toMG'.IsProperIso
      (H.glue x y₁ y₂ g.swapSolid).toMG'.int P) :
    (∀ c ∈ g.comps, ∀ u, c.label = some (.Q, u) →
      (H.glue x y₁ y₂ g.swapSolid).molRep (glueAtom x y₁ y₂ u) ∈ P) ∧
    ((∃ h : Fin m, (H.glue x y₁ y₂ g.swapSolid).molRep (liftA n' (.inr h)) ∈ P) →
      2 ≤ (H.glue x y₁ y₂ g.swapSolid).toMG'.redCount P) := by
  classical
  set Gt := H.glue x y₁ y₂ g.swapSolid with hGt
  set G := H.glue x y₁ y₂ (tVar true) with hG
  set γ : Atom 3 n' → Atom 3 (m + n') := glueAtom x y₁ y₂ with hγ
  set p : Atom 3 (m + n') → Prop := fun u => Gt.molRep u ∈ P with hp
  set f : Atom 3 n' → Prop := p ∘ γ with hf
  have hPi : P ⊆ Gt.toMG'.int := hP.1.1
  have hiso := hP.1
  have hcount := GlobalGoodB_count_of_iso _ hiso
  obtain ⟨hcGt, hrGt⟩ := GlobalGoodB_Gt_counts (g := g.swapSolid) hD hx hy₁ hy₂ P
  obtain ⟨hcG, hrG⟩ := GlobalGoodB_G_counts (g := g.swapSolid) hD hx hy₁ hy₂ hPi
  simp only [Graph.swapSolid, GlobalGoodB_nc_swap, GlobalGoodB_rc_swap] at hcGt hrGt
  change Gt.toMG'.crossCount P = GlobalGoodB_nc (p ∘ liftA n') H.comps +
    GlobalGoodB_nc f g.comps at hcGt
  change Gt.toMG'.redCount P = GlobalGoodB_rc (p ∘ liftA n') H.comps +
    GlobalGoodB_rc f g.comps at hrGt
  set S := GlobalGoodB_S H x y₁ y₂ g.swapSolid P with hS
  change G.toMG'.crossCount S = GlobalGoodB_nc (p ∘ liftA n') H.comps +
    (if (p (liftA n' y₁) ↔ p (liftA n' x)) then 0 else 1) at hcG
  change G.toMG'.redCount S = GlobalGoodB_rc (p ∘ liftA n') H.comps +
    (if (p (liftA n' y₂) ↔ p (liftA n' x)) then 0 else 1) at hrG
  have hmemS := GlobalGoodB_mem_S (g := g.swapSolid) hD hx hy₁ hy₂ hPi
  have hext : ∀ a : Fin 3, ¬ p (.inl a) := fun a h => MolMono_inl_not_mem_int Gt a (hPi h)
  have hf0 : f (.inl 0) = p (liftA n' x) := rfl
  have hf1 : f (.inl 1) = p (liftA n' y₁) := rfl
  have hf2 : f (.inl 2) = p (liftA n' y₂) := rfl
  -- invariance of `f` along waved and dotted components
  have hmol : ∀ c ∈ g.comps, c.kind.joinsMol = true → (f c.x ↔ f c.y) :=
    fun c hc hj => GlobalGoodB_mol_inv hx hy₁ hy₂ P hc hj
  have hInv0 : GlobalGoodB_nc f g.comps = 0 → GlobalGoodB_Inv g f := by
    intro h0 c hc hk
    rcases hk with hk | hk
    · exact GlobalGoodB_nc_eq_zero.1 h0 c hc hk
    · exact hmol c hc hk
  -- the molecules of `H` and of `g` in `P`
  have hall : (∀ h : Fin m, p (liftA n' (.inr h))) → (∀ j : Fin n', f (.inr j)) → False := by
    intro hH hg
    apply hP.2.ne
    refine Finset.Subset.antisymm hPi fun M hM => ?_
    rcases GlobalGoodB_Gt_int hM with ⟨h, rfl⟩ | ⟨j, rfl⟩
    · exact hH h
    · exact hg j
  -- the `Q` label atoms
  have hlab : (∀ j : Fin n', f (.inr j)) → f (.inl 1) →
      ∀ c ∈ g.comps, ∀ u, c.label = some (.Q, u) → f u := by
    intro hgj h1 c hc u hu
    rcases hQL c hc u hu with h | ⟨hu', h⟩
    · rcases u with a | j
      · exact absurd (GlobalGoodB_mis_int _ h) (MolMono_inl_not_mem_int g a)
      · exact hgj j
    · rcases h with h | ⟨c', hc', a, hw, hca, -⟩
      · rcases hu' with rfl | rfl
        · exact h1
        · exact absurd (hQP h c hc _ hu) (by simp)
      · have hj : c'.kind.joinsMol = true := by obtain ⟨w, hw⟩ := hw; rw [hw]; rfl
        have := hmol c' hc' hj
        rcases hca with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this
        · exact this.2 (hgj a)
        · exact this.1 (hgj a)
  by_cases hhost : ∃ h : Fin m, p (liftA n' (.inr h))
  · -- `P` contains a molecule of `H`
    obtain ⟨h₀, hh₀⟩ := hhost
    have hSi : S ⊆ G.toMG'.int := Finset.filter_subset _ _
    have hSne : S.Nonempty := ⟨_, (hmemS (liftA 1 (.inr h₀))).2 (by
      rw [GlobalGoodB_lift_liftA]; exact hh₀)⟩
    obtain ⟨hspd, -, -, hu₀, hu₁, hu₂, hm₀, hm₁, -⟩ := SubstSPD_host H x y₁ y₂ hx hy₁ hy₂ hD hI hst
    have hpX : ∀ y : Atom 3 m, G.molRep (liftA 1 y) ∈ S ↔ p (liftA n' y) := fun y => by
      rw [hmemS, GlobalGoodB_lift_liftA]
    have hDC : G.toMG'.DC := hspd.1
    by_cases hall' : G.toMG'.int ⊆ S
    · exfalso
      have hpx : p (liftA n' x) := (hpX x).1 (hall' hu₀)
      have hpy₁ : p (liftA n' y₁) := (hpX y₁).1 (hall' hu₁)
      have hU : ∀ a : Fin 3, G.Unpinned (.inl a) := fun a => ⟨rfl, fun b hb => by
        have := (Graph.sameBlock_iff_eq G (fun c hc hk => absurd hk (hD c hc)) _ _).1 hb
        simp at this⟩
      have h2 := GlobalGoodB_two_ext hI.2.2.1 hI.2.1 (hU 0) (hU 1)
      have hSeq : S = G.toMG'.int := Finset.Subset.antisymm hSi hall'
      rw [← hSeq, hcG, GlobalGoodB_ite_t (iff_of_true hpy₁ hpx)] at h2
      have hg0 : GlobalGoodB_nc f g.comps = 0 := by omega
      have hcn := GlobalGoodB_conn hN hT hA hcase (hInv0 hg0)
      refine hall (fun h => ?_) (fun j => (hcn.2 j).2 hpx)
      exact (hpX (.inr h)).1 (hall' (by
        exact (MolMono_mem_int G _).2 ⟨_, rfl⟩))
    · -- `S` is a proper isolated subset of `G`
      have hc2 := GlobalGoodB_two_le_of_DC _ hDC hSi hSne hall'
      have hxy : (p (liftA n' y₁) ↔ p (liftA n' x)) := by
        by_contra hne
        rw [hcG, GlobalGoodB_ite_f (hne)] at hc2
        have hg1 : 1 ≤ GlobalGoodB_nc f g.comps := by
          by_contra hlt
          have hg0 : GlobalGoodB_nc f g.comps = 0 := by omega
          exact hne ((GlobalGoodB_conn hN hT hA hcase (hInv0 hg0)).1)
        have hS2 : G.toMG'.crossCount S = 2 := by rw [hcG, GlobalGoodB_ite_f (hne)]; omega
        have hSiso := GlobalGoodB_iso_of_count _ hSi hS2
        have hmis := GlobalGoodB_mis_sub _ ⟨hSiso, Finset.ssubset_iff_subset_ne.2
          ⟨hSi, fun h => hall' (h ▸ subset_rfl)⟩⟩
        exact hne (iff_of_true ((hpX y₁).1 (hmis hm₁)) ((hpX x).1 (hmis hm₀)))
      rw [hcG, GlobalGoodB_ite_t (hxy)] at hc2
      have hg0 : GlobalGoodB_nc f g.comps = 0 := by omega
      have hS2 : G.toMG'.crossCount S = 2 := by rw [hcG, GlobalGoodB_ite_t (hxy)]; omega
      have hSp : G.toMG'.IsProperIso G.toMG'.int S := ⟨GlobalGoodB_iso_of_count _ hSi hS2,
        Finset.ssubset_iff_subset_ne.2 ⟨hSi, fun h => hall' (h ▸ subset_rfl)⟩⟩
      have hmis := GlobalGoodB_mis_sub _ hSp
      have hpx : p (liftA n' x) := (hpX x).1 (hmis hm₀)
      have hcn := GlobalGoodB_conn hN hT hA hcase (hInv0 hg0)
      refine ⟨hlab (fun j => (hcn.2 j).2 hpx) (hcn.1.2 hpx), fun _ => ?_⟩
      have hw := (GlobalGoodB_weak_iff _).1 (hgs.2 S hSp)
      rw [hrGt]
      rw [hrG] at hw
      by_cases hy₂' : p (liftA n' y₂)
      · rw [GlobalGoodB_ite_t (iff_of_true hy₂' hpx)] at hw
        omega
      · rw [GlobalGoodB_ite_f (fun h => hy₂' (h.2 hpx))] at hw
        obtain ⟨c, hc, hred, hne⟩ := GlobalGoodB_red_walk hN hPl hTK (hInv0 hg0) (.inl 2) (.inl 0)
          (fun h => hy₂' (h.2 hpx))
        have := GlobalGoodB_rc_pos hc hred hne
        omega
  · -- `P` contains no molecule of `H`
    push Not at hhost
    have hpH : ∀ u : Atom 3 m, ¬ p (liftA n' u) := by
      rintro (a | h)
      · exact hext a
      · exact hhost h
    have hH0 : GlobalGoodB_nc (p ∘ liftA n') H.comps = 0 :=
      GlobalGoodB_nc_const fun c _ => iff_of_false (hpH c.x) (hpH c.y)
    have h0 : ∀ a : Fin 3, ¬ f (.inl a) := fun a => by
      fin_cases a
      · exact hpH x
      · exact hpH y₁
      · exact hpH y₂
    set Q := g.toMG'.int.filter (fun M => f M) with hQ
    have hq : ∀ u, g.molRep (g.flatAtom u) ∈ Q ↔ f u :=
      GlobalGoodB_q_iff (g := g) hD hx hy₁ hy₂ P h0
    have hQi : Q ⊆ g.toMG'.int := Finset.filter_subset _ _
    have hQc : g.toMG'.crossCount Q = 2 := by
      rw [GlobalGoodB_cross_eq]
      have h1 : GlobalGoodB_nc (fun u => g.molRep (g.flatAtom u) ∈ Q) g.comps =
          GlobalGoodB_nc f g.comps :=
        GlobalGoodB_nc_congr _ fun c _ _ => by rw [hq c.x, hq c.y]
      have h2 : ((List.finRange 3).filterMap (MolMono_pinD g)).countP
          (fun t => decide (MolMono_crossT g.toMG'.int g.toMG'.ext Q t)) = 0 := by
        rw [List.countP_eq_zero]
        intro t ht
        obtain ⟨a, -, hat⟩ := List.mem_filterMap.1 ht
        unfold MolMono_pinD at hat
        split at hat
        · rename_i b hb
          obtain rfl := Option.some.inj hat
          have hfb : g.flatAtom (.inl a) = .inr b := by simp [Graph.flatAtom, hb]
          have hqa := hq (.inl a)
          rw [hfb] at hqa
          have hnb : g.molRep (.inr b) ∉ Q := by
            have : g.molRep (g.flatAtom (.inr b)) = g.molRep (.inr b) := rfl
            rw [← this, hq]
            intro hb'
            exact h0 a (by
              have := (GlobalGoodB_glue_molRep (g := g) hD hx hy₁ hy₂ (.inl a)).2
              rw [hfb] at this
              change Gt.molRep (γ (.inl a)) ∈ P
              rw [← this]
              exact hb')
          have hna : (Sum.inl a : Atom 3 n') ∉ Q := fun h =>
            MolMono_inl_not_mem_int g a (hQi h)
          simp [MolMono_crossT, hnb, hna]
        · exact absurd hat (by simp)
      rw [h1, h2, add_zero]
      omega
    have hQiso := GlobalGoodB_iso_of_count _ hQi hQc
    obtain ⟨M, hM⟩ := GlobalGoodB_iso_nonempty _ hiso
    have hQne : ∃ j : Fin n', f (.inr j) := by
      rcases GlobalGoodB_Gt_int (hPi hM) with ⟨h, rfl⟩ | ⟨j, rfl⟩
      · exact absurd hM (hhost h)
      · exact ⟨j, hM⟩
    obtain ⟨j₀, hj₀⟩ := hQne
    have hmisQ : g.toMG'.MIS ⊆ Q := by
      by_cases hsub : Q ⊂ g.toMG'.int
      · exact GlobalGoodB_mis_sub _ ⟨hQiso, hsub⟩
      · have : Q = g.toMG'.int := by
          by_contra hne
          exact hsub (Finset.ssubset_iff_subset_ne.2 ⟨hQi, hne⟩)
        rw [this]
        exact GlobalGoodB_mis_int _
    refine ⟨fun c hc u hu => ?_, fun ⟨h, hh⟩ => absurd hh (hhost h)⟩
    change f u
    rcases hQL c hc u hu with h | ⟨hu', h⟩
    · have hu : u.isRight = true := by
        rcases u with a | j
        · exact absurd (GlobalGoodB_mis_int _ h) (MolMono_inl_not_mem_int g a)
        · rfl
      rcases u with a | j
      · simp at hu
      · exact (hq (.inr j)).1 (hmisQ h)
    · rcases h with h | ⟨c', hc', a, hw, hca, hmis⟩
      · subst h
        exact j₀.elim0
      · have hfa : f (.inr a) := (hq (.inr a)).1 (hmisQ hmis)
        have hj : c'.kind.joinsMol = true := by obtain ⟨w, hw⟩ := hw; rw [hw]; rfl
        have := hmol c' hc' hj
        rcases hca with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this
        · exact this.2 hfa
        · exact this.1 hfa

end Classify

/-! ## The components of the `O_dot` forms -/

section ODot

variable {k n : ℕ}

private theorem GlobalGoodB_map_id {V : Type*} (c : Comp V) : c.map id = c := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  simp [Comp.map]

private theorem GlobalGoodB_map_map {U V W : Type*} (f : U → V) (g : V → W) (c : Comp U) :
    (c.map f).map g = c.map (g ∘ f) := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases lab <;> simp [Comp.map, List.map_map]
  rfl

/-- **The components of an `O_dot` form** ([II, Def 4.2]): each is the image under the atom map of
a component of the graph or of an added unlabelled dotted or `×`-dotted edge, or a solid edge
of one of these turned into the weight of the same charge at the image of its first atom. -/
private theorem GlobalGoodB_oDot_comp {Γ : Graph k n} {t : Tracked k n} (ht : t ∈ oDotT Γ)
    {c' : Comp (Atom k t.nOut)} (hc' : c' ∈ t.g.comps) :
    ∃ c : Comp (Atom k n), (c ∈ Γ.comps ∨ (c.label = none ∧ c.minor = [] ∧
      (c.kind = .dot ∨ c.kind = .xdot))) ∧
      (c' = c.map t.f ∨ (c.kind.isSolid = true ∧
        c' = { c.map t.f with kind := c.kind.toWeight, y := t.f c.x })) := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact ⟨c', Or.inl hc', Or.inl (GlobalGoodB_map_id c').symm⟩
  · obtain ⟨c, hc, hmc⟩ := (mergeT_spec hm).mem_comps.1 hc'
    have hc0 : c ∈ Γ.comps ∨ (c.label = none ∧ c.minor = [] ∧
        (c.kind = .dot ∨ c.kind = .xdot)) := by
      rw [dc_comps, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Or.inl (List.mem_filter.1 hc).1
      · obtain ⟨p, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 hc
        · exact Or.inr ⟨rfl, rfl, Or.inl rfl⟩
        · exact Or.inr ⟨rfl, rfl, Or.inr rfl⟩
    refine ⟨c, hc0, ?_⟩
    unfold mergeComp at hmc
    split_ifs at hmc with h1 h2
    · obtain rfl := Option.some.inj hmc
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact Or.inr ⟨h2.1, rfl⟩
    · exact Or.inl (Option.some.inj hmc).symm

private theorem GlobalGoodB_oDot_inl {Γ : Graph k n} {t : Tracked k n} (ht : t ∈ oDotT Γ)
    (a : Fin k) :
    t.f (.inl a) = .inl a := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · rfl
  · exact (mergeT_spec hm).f_inl a

/-- The label of a component of an `O_dot` form is the image of the label of the component it
comes from. -/
private theorem GlobalGoodB_oDot_label {Γ : Graph k n} {t : Tracked k n} (ht : t ∈ oDotT Γ)
    {c' : Comp (Atom k t.nOut)} (hc' : c' ∈ t.g.comps) {ℓ : PQ × Atom k t.nOut}
    (hl : c'.label = some ℓ) :
    ∃ c ∈ Γ.comps, ∃ w, c.label = some (ℓ.1, w) ∧ ℓ.2 = t.f w := by
  obtain ⟨c, hc, he⟩ := GlobalGoodB_oDot_comp ht hc'
  have hlab : c'.label = c.label.map (Prod.map id t.f) := by
    rcases he with rfl | ⟨-, rfl⟩ <;> rfl
  rw [hlab] at hl
  rcases hc with hc | ⟨hn, -⟩
  · obtain ⟨⟨q, w⟩, hq, hqe⟩ := Option.map_eq_some_iff.1 hl
    refine ⟨c, hc, w, ?_, ?_⟩
    · rw [hq, ← hqe]; rfl
    · rw [← hqe]; rfl
  · rw [hn] at hl; simp at hl

/-- An unlabelled weight or solid edge of an `O_dot` form comes from an unlabelled weight or
solid edge of the graph, with its atoms among the images of the atoms of that component. -/
private theorem GlobalGoodB_oDot_unl {Γ : Graph k n} {t : Tracked k n} (ht : t ∈ oDotT Γ)
    {c' : Comp (Atom k t.nOut)} (hc' : c' ∈ t.g.comps) (hl : c'.label = none)
    (hr : c'.kind.isRandom = true) :
    ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧
      ∀ u ∈ [c'.x, c'.y], ∃ v ∈ [c.x, c.y], u = t.f v := by
  obtain ⟨c, hc, he⟩ := GlobalGoodB_oDot_comp ht hc'
  rcases he with rfl | ⟨hs, rfl⟩
  · rcases hc with hc | ⟨-, -, hk | hk⟩
    · refine ⟨c, hc, ?_, hr, ?_⟩
      · simpa [Comp.map] using hl
      · intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact ⟨c.x, by simp, rfl⟩
        · exact ⟨c.y, by simp, rfl⟩
    · simp [Comp.map, hk, Kind.isRandom] at hr
    · simp [Comp.map, hk, Kind.isRandom] at hr
  · rcases hc with hc | ⟨-, -, hk | hk⟩
    · refine ⟨c, hc, ?_, ?_, ?_⟩
      · simpa [Comp.map] using hl
      · obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
          cases hk : c.kind <;> simp_all [Kind.isSolid]
        rw [hch]; rfl
      · intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact ⟨c.x, by simp, rfl⟩
        · exact ⟨c.x, by simp, rfl⟩
    · rw [hk] at hs; simp [Kind.isSolid] at hs
    · rw [hk] at hs; simp [Kind.isSolid] at hs

/-- The clauses of `Graph.Plain` other than the one on dotted loops. -/
private def GlobalGoodB_PW {V : Type*} (c : Comp V) : Prop :=
  c.minor = [] ∧ (∀ ch, c.kind ≠ .inv ch) ∧ (∀ ch d, c.kind ≠ .wD ch d) ∧ c.WF

private theorem GlobalGoodB_PW_map {V W : Type*} (f : V → W) {c : Comp V} (h : GlobalGoodB_PW c) :
    GlobalGoodB_PW (c.map f) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by simp [Comp.map, h1], h2, h3, fun hw => ?_, fun hl => ?_⟩
  · simp only [Comp.map] at hw ⊢
    rw [h4 hw]
  · simp only [Comp.map, Option.isSome_map] at hl
    exact h5 hl

private theorem GlobalGoodB_PW_of_plain {k n : ℕ} {Γ : Graph k n} (h : Γ.Plain) :
    ∀ c ∈ Γ.comps, GlobalGoodB_PW c :=
  fun c hc => ⟨(h c hc).1, (h c hc).2.1, (h c hc).2.2.1, (h c hc).2.2.2.2⟩

/-- `O_dot` keeps the clauses `GlobalGoodB_PW`. -/
private theorem GlobalGoodB_oDot_PW {Γ : Graph k n} (h : ∀ c ∈ Γ.comps, GlobalGoodB_PW c)
    {t : Tracked k n} (ht : t ∈ oDotT Γ) : ∀ c' ∈ t.g.comps, GlobalGoodB_PW c' := by
  intro c' hc'
  obtain ⟨c, hc, he⟩ := GlobalGoodB_oDot_comp ht hc'
  have hc1 : GlobalGoodB_PW c := by
    rcases hc with hc | ⟨hl, hm, hk | hk⟩
    · exact h c hc
    all_goals
      refine ⟨hm, ?_, ?_, ?_, ?_⟩
      · intro ch h; rw [hk] at h; cases h
      · intro ch d h; rw [hk] at h; cases h
      · intro hw; rw [hk] at hw; cases hw
      · intro hl'; rw [hl] at hl'; cases hl'
  rcases he with rfl | ⟨hs, rfl⟩
  · exact GlobalGoodB_PW_map t.f hc1
  · obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    obtain ⟨h1, -, -, -, h5⟩ := hc1
    refine ⟨by simp [Comp.map, h1], fun ch' h => ?_, fun ch' d h => ?_, fun _ => rfl, fun hl => ?_⟩
    · simp [hch, Kind.toWeight] at h
    · simp [hch, Kind.toWeight] at h
    · simp [hch, Kind.toWeight, Kind.isRandom]

/-- A graph without dotted edges with the clauses `GlobalGoodB_PW` is plain. -/
private theorem GlobalGoodB_plain_of {Γ : Graph k n} (h : ∀ c ∈ Γ.comps, GlobalGoodB_PW c)
    (hd : ∀ c ∈ Γ.comps, c.kind ≠ .dot) : Γ.Plain :=
  fun c hc => ⟨(h c hc).1, (h c hc).2.1, (h c hc).2.2.1, fun hk => absurd hk (hd c hc),
    (h c hc).2.2.2⟩

end ODot

/-! ## The substituted graph and its `O_dot` forms -/

section Subst

variable {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m} {g : Graph 3 n'}

/-- **Plain `O_dot` forms of a substituted graph.** If `H.glue x y₁ y₂ (tVar true)` and `g` are
plain, every component of `H.glue x y₁ y₂ g.swapSolid` satisfies the clauses of `Graph.Plain`
other than the one on dotted loops. -/
private theorem GlobalGoodB_glue_PW (hG : (H.glue x y₁ y₂ (tVar true)).Plain) (hg : g.Plain) :
    ∀ c ∈ (H.glue x y₁ y₂ g.swapSolid).comps, GlobalGoodB_PW c := by
  intro c hc
  rw [GlobalGoodB_glue_comps, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    have h1 : GlobalGoodB_PW (c₀.map (liftA 1)) :=
      GlobalGoodB_PW_of_plain hG _ (by
        rw [GlobalGoodB_G_comps]; exact List.mem_append_left _ (List.mem_map.2 ⟨c₀, hc₀, rfl⟩))
    have h2 := GlobalGoodB_PW_map (SubstMol_lift n' x) h1
    rwa [GlobalGoodB_map_map, show SubstMol_lift n' x ∘ liftA 1 = liftA n' from
      funext fun u => GlobalGoodB_lift_liftA x u] at h2
  · obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
    refine GlobalGoodB_PW_map _ ?_
    have hgs : g.swapSolid.Plain := (swapSolid_basic 3 n' g).2.2.2.1.2 hg
    exact GlobalGoodB_PW_of_plain hgs c₁ hc₁

/-- The unlabelled weights and solid edges of `H.glue x y₁ y₂ g.swapSolid`, for a `Q`-graph `g`,
are those of `H`. -/
private theorem GlobalGoodB_glue_unl (hg : g.IsQGraph) {c : Comp (Atom 3 (m + n'))}
    (hc : c ∈ (H.glue x y₁ y₂ g.swapSolid).comps) (hl : c.label = none)
    (hr : c.kind.isRandom = true) : ∃ c₀ ∈ H.comps, c = c₀.map (liftA n') := by
  rw [GlobalGoodB_glue_comps, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact ⟨c₀, hc₀, rfl⟩
  · exfalso
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc₁
    obtain ⟨u, -, hu⟩ := hg
    have hk : c₀.kind.isRandom = true := by
      simpa [Comp.map, GlobalGoodB_swap_kind] using hr
    have := hu c₀ hc₀ (Or.inl hk)
    have hl' : c₀.label = none := by
      have : (c₀.swapSolid.map (glueAtom x y₁ y₂)).label = none := hl
      unfold Comp.swapSolid at this
      split at this <;> simpa [Comp.map] using this
    rw [hl'] at this
    cases this

/-- The labels of `H.glue x y₁ y₂ g.swapSolid`, for `H` without labels, are the images of those
of `g`. -/
private theorem GlobalGoodB_glue_label (hL : H.LabelFree) {c : Comp (Atom 3 (m + n'))}
    (hc : c ∈ (H.glue x y₁ y₂ g.swapSolid).comps) {ℓ : PQ × Atom 3 (m + n')}
    (hl : c.label = some ℓ) :
    ∃ c₀ ∈ g.comps, ∃ u, c₀.label = some (ℓ.1, u) ∧ ℓ.2 = glueAtom x y₁ y₂ u := by
  rw [GlobalGoodB_glue_comps, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    rw [show (c₀.map (liftA n')).label = c₀.label.map _ from rfl, hL c₀ hc₀] at hl
    cases hl
  · obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc₁
    have hlab : c₀.swapSolid.label = c₀.label := by
      unfold Comp.swapSolid; split <;> rfl
    have : (c₀.swapSolid.map (glueAtom x y₁ y₂)).label =
        c₀.label.map (Prod.map id (glueAtom x y₁ y₂)) := by
      rw [← hlab]; rfl
    rw [this] at hl
    obtain ⟨⟨q, u⟩, hq, hqe⟩ := Option.map_eq_some_iff.1 hl
    refine ⟨c₀, hc₀, u, ?_, ?_⟩
    · rw [hq, ← hqe]; rfl
    · rw [← hqe]; rfl

end Subst

/-! ## Pullback of the minimal isolated subset -/

section Pull

variable {n m : ℕ}

private theorem GlobalGoodB_mem_mis {V E : Type} {G : MGraph V E} {v : V} (hv : v ∈ G.int)
    (h : ∀ P, G.IsProperIso G.int P → v ∈ P) : v ∈ G.MIS := by
  classical
  unfold MGraph.MIS
  exact Finset.mem_filter.2 ⟨hv, h⟩

/-- **The minimal isolated subset along a `Graph.MolMono` map.** If every proper isolated subset of
the first graph contains the molecule of `w`, every proper isolated subset of the second graph
contains the molecule of the image of `w`, which then lies in its minimal isolated subset. -/
private theorem GlobalGoodB_mis_pull {Γ₁ : Graph 3 n} {Γ₂ : Graph 3 m} {φ : Atom 3 n → Atom 3 m}
    (h : Γ₁.MolMono Γ₂ φ) (hI : Γ₁.InvB') {w : Atom 3 n} (hw : w.isRight = true)
    (hP : ∀ P, Γ₁.toMG'.IsProperIso Γ₁.toMG'.int P → Γ₁.molRep w ∈ P) :
    (∀ P', Γ₂.toMG'.IsProperIso Γ₂.toMG'.int P' → Γ₂.molRep (φ w) ∈ P') ∧
      Γ₂.molRep (φ w) ∈ Γ₂.toMG'.MIS := by
  have key : ∀ P', Γ₂.toMG'.IsProperIso Γ₂.toMG'.int P' → Γ₂.molRep (φ w) ∈ P' := by
    intro P' hP'
    have hm := hP _ (h.pull_properIso hI hP').1
    simp only [Graph.molPull, Finset.mem_filter] at hm
    rw [← MolMono_rep_map' h hw]
    exact hm.2
  refine ⟨key, GlobalGoodB_mem_mis ?_ key⟩
  rcases w with a | a
  · cases hw
  · have := h.isRight a
    rcases hφ : φ (.inr a) with b | b
    · rw [hφ] at this; cases this
    · exact MolMono_molRep_mem_int Γ₂ b

end Pull

/-! ## Counting components -/

/-- Two distinct entries of a list with the property `p`. -/
private theorem GlobalGoodB_two_le_countP {α : Type*} {p : α → Bool} {a b : α} (hab : a ≠ b)
    (hpa : p a = true) (hpb : p b = true) : ∀ {L : List α}, a ∈ L → b ∈ L → 2 ≤ L.countP p
  | [], ha, _ => absurd ha List.not_mem_nil
  | c :: L, ha, hb => by
    rw [List.countP_cons]
    rcases List.mem_cons.1 ha with rfl | ha'
    · have hb' : b ∈ L := (List.mem_cons.1 hb).resolve_left (Ne.symm hab)
      have := List.countP_pos_iff.2 ⟨b, hb', hpb⟩
      simp only [hpa, ite_true]
      omega
    · rcases List.mem_cons.1 hb with rfl | hb'
      · have := List.countP_pos_iff.2 ⟨a, ha', hpa⟩
        simp only [hpb, ite_true]
        omega
      · have := GlobalGoodB_two_le_countP hab hpa hpb ha' hb'
        omega

/-- Waved, dotted and diffusive kinds. -/
private def GlobalGoodB_isRB (κ : Kind) : Bool := κ.joinsMol || κ.isDiffusive

/-- A lower bound for the scaling order of a component of the kinds of [II, Def 3.2]: `2` for a
waved, dotted or diffusive edge, `1` for a solid edge, `0` otherwise. -/
private def GlobalGoodB_w {V : Type*} (c : Comp V) : ℤ :=
  if GlobalGoodB_isRB c.kind then 2 else if c.kind.isSolid then 1 else 0

private theorem GlobalGoodB_labelOK_sum {N : ℕ} :
    ∀ {o : List ℕ}, labelOK N o = true → 2 * o.length ≤ o.sum
  | [], _ => by simp
  | a :: o, h => by
    simp only [labelOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    have := GlobalGoodB_labelOK_sum (o := o) (by simpa [labelOK] using h.2)
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem GlobalGoodB_w_le {V : Type*} {N : ℕ} {c : Comp V} (h : c.isTKind N = true) :
    GlobalGoodB_w c ≤ c.kind.ord := by
  unfold Comp.isTKind at h
  unfold GlobalGoodB_w GlobalGoodB_isRB
  cases hk : c.kind with
  | G ch => simp [Kind.joinsMol, Kind.isDiffusive, Kind.isSolid, Kind.ord]
  | weight ch => simp [Kind.joinsMol, Kind.isDiffusive, Kind.isSolid, Kind.ord]
  | light ch => simp [Kind.joinsMol, Kind.isDiffusive, Kind.isSolid, Kind.ord]
  | waved w => simp [Kind.joinsMol, Kind.ord]
  | dot => simp [Kind.joinsMol, Kind.ord]
  | xdot => simp [Kind.joinsMol, Kind.isDiffusive, Kind.isSolid, Kind.ord]
  | theta o =>
    rw [hk] at h
    simp only [Bool.and_eq_true] at h
    have h2 := GlobalGoodB_labelOK_sum h.2
    simp only [Kind.joinsMol, Kind.isDiffusive, Bool.false_or, ite_true, Kind.ord]
    omega
  | _ => rw [hk] at h; simp at h

private theorem GlobalGoodB_w_ge {V : Type*} (c : Comp V) :
    2 * ((if GlobalGoodB_isRB c.kind then 1 else 0 : ℕ) : ℤ) +
      ((if c.kind.isSolid then 1 else 0 : ℕ) : ℤ) ≤ GlobalGoodB_w c := by
  unfold GlobalGoodB_w GlobalGoodB_isRB
  cases c.kind with
  | aux j r b => cases b <;> simp [Kind.joinsMol, Kind.isDiffusive, Kind.isSolid]
  | _ => simp [Kind.joinsMol, Kind.isDiffusive, Kind.isSolid]

private theorem GlobalGoodB_sum_w {V : Type*} :
    ∀ L : List (Comp V), 2 * ((L.countP fun c => GlobalGoodB_isRB c.kind : ℕ) : ℤ) +
      ((L.countP fun c => c.kind.isSolid : ℕ) : ℤ) ≤ (L.map GlobalGoodB_w).sum
  | [] => by simp
  | c :: L => by
    have := GlobalGoodB_sum_w L
    have h1 := GlobalGoodB_w_ge c
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    push_cast at h1 ⊢
    omega

/-! ## The order `≥ 3` of a graph of `Q` with its label at the block of `⊕` or `⊖` -/

section Ord

variable {n : ℕ} {Γ : Graph 3 n}

/-- The graph on the atoms of the waved, dotted and diffusive components. -/
private def GlobalGoodB_GR (Γ : Graph 3 n) : SimpleGraph (Atom 3 n) :=
  SimpleGraph.fromRel fun a b => ∃ c ∈ Γ.comps, GlobalGoodB_isRB c.kind = true ∧ c.x = a ∧ c.y = b

private theorem GlobalGoodB_GR_comp {c : Comp (Atom 3 n)} (hc : c ∈ Γ.comps)
    (h : GlobalGoodB_isRB c.kind = true) : (GlobalGoodB_GR Γ).Reachable c.x c.y := by
  by_cases hxy : c.x = c.y
  · rw [hxy]
  · exact SimpleGraph.Adj.reachable
      ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hxy, Or.inl ⟨c, hc, h, rfl, rfl⟩⟩)

private theorem GlobalGoodB_GR_dot {u v : Atom 3 n} (h : Γ.SameBlock u v) :
    (GlobalGoodB_GR Γ).Reachable u v := by
  refine SimpleGraph.Reachable.mono (fun a b hab => ?_) h
  rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
  rw [GlobalGoodB_GR, SimpleGraph.fromRel_adj]
  refine ⟨hab.1, ?_⟩
  rcases hab.2 with ⟨c, hc, hk, hx, hy⟩ | ⟨c, hc, hk, hx, hy⟩
  · exact Or.inl ⟨c, hc, by simp [GlobalGoodB_isRB, hk, Kind.joinsMol], hx, hy⟩
  · exact Or.inr ⟨c, hc, by simp [GlobalGoodB_isRB, hk, Kind.joinsMol], hx, hy⟩

private theorem GlobalGoodB_GR_wt {u v : Atom 3 n} (h : Γ.wavedThetaGraph.Reachable u v) :
    (GlobalGoodB_GR Γ).Reachable u v := by
  refine SimpleGraph.Reachable.mono (fun a b hab => ?_) h
  rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hab
  rw [GlobalGoodB_GR, SimpleGraph.fromRel_adj]
  refine ⟨hab.1, ?_⟩
  have key : ∀ c : Comp (Atom 3 n), ((c.kind.joinsMol = true ∧ c.kind ≠ .dot) ∨
      c.kind.isDiffusive = true) → GlobalGoodB_isRB c.kind = true := by
    rintro c (⟨h, -⟩ | h) <;> simp [GlobalGoodB_isRB, h]
  rcases hab.2 with ⟨c, hc, hk, hx, hy⟩ | ⟨c, hc, hk, hx, hy⟩
  · exact Or.inl ⟨c, hc, key c hk, hx, hy⟩
  · exact Or.inr ⟨c, hc, key c hk, hx, hy⟩

/-- The number of atoms is at most the number of classes of `GlobalGoodB_GR` plus the number of
waved, dotted and diffusive components that are not loops. -/
private theorem GlobalGoodB_GR_count (Γ : Graph 3 n) :
    3 + n ≤ Nat.card (GlobalGoodB_GR Γ).ConnectedComponent +
      Γ.comps.countP (fun c => GlobalGoodB_isRB c.kind && decide (c.x ≠ c.y)) := by
  classical
  let gR : Graph 3 n := ⟨(Γ.comps.filter fun c => GlobalGoodB_isRB c.kind).map
    (fun c => mkC .dot c.x c.y), 1⟩
  have hdg : gR.dotGraph = GlobalGoodB_GR Γ := by
    ext a b
    rw [Graph.dotGraph, GlobalGoodB_GR, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
    have key : ∀ a b, (∃ c ∈ gR.comps, c.kind = .dot ∧ c.x = a ∧ c.y = b) ↔
        ∃ c ∈ Γ.comps, GlobalGoodB_isRB c.kind = true ∧ c.x = a ∧ c.y = b := by
      intro a b
      simp only [gR, List.mem_map, List.mem_filter]
      constructor
      · rintro ⟨_, ⟨c, ⟨hc, hk⟩, rfl⟩, -, rfl, rfl⟩
        exact ⟨c, hc, hk, rfl, rfl⟩
      · rintro ⟨c, hc, hk, rfl, rfl⟩
        exact ⟨_, ⟨c, ⟨hc, hk⟩, rfl⟩, rfl, rfl, rfl⟩
    rw [key, key]
  have hle := SubstSPD_length_le (allAtoms 3 n) SubstSPD_allAtoms_nodup gR.comps
  have hlen : (allAtoms 3 n).length = 3 + n := by simp [allAtoms]
  rw [hlen, Graph.dotBlocks_length_eq_card gR, hdg] at hle
  have hcnt : ((gR.comps.filter fun c => decide (c.kind = .dot)).filter
      fun c => decide (c.x ≠ c.y)).length =
      Γ.comps.countP (fun c => GlobalGoodB_isRB c.kind && decide (c.x ≠ c.y)) := by
    have h1 : (gR.comps.filter fun c => decide (c.kind = .dot)) = gR.comps :=
      List.filter_eq_self.2 fun c hc => by
        simp only [gR, List.mem_map] at hc
        obtain ⟨_, -, rfl⟩ := hc
        simp [mkC]
    rw [h1, ← List.countP_eq_length_filter]
    simp only [gR, List.countP_map, List.countP_filter]
    refine List.countP_congr fun c _ => ?_
    simp [mkC, Bool.and_comm]
  omega

/-- The classes of `GlobalGoodB_GR`: at most two if every atom other than `w₀` is joined to `⊗`. -/
private theorem GlobalGoodB_card_le_two (w₀ : Atom 3 n)
    (h : ∀ v, (GlobalGoodB_GR Γ).Reachable (.inl 0) v ∨ v = w₀) :
    Nat.card (GlobalGoodB_GR Γ).ConnectedComponent ≤ 2 := by
  have hs : Function.Surjective (fun i : Fin 2 =>
      if i = 0 then (GlobalGoodB_GR Γ).connectedComponentMk (.inl 0)
      else (GlobalGoodB_GR Γ).connectedComponentMk w₀) := by
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      rcases h v with hv | rfl
      · exact ⟨0, by simp [SimpleGraph.ConnectedComponent.eq, hv]⟩
      · exact ⟨1, by simp⟩
  simpa using Nat.card_le_card_of_surjective _ hs

private theorem GlobalGoodB_card_le_one
    (h : ∀ v, (GlobalGoodB_GR Γ).Reachable (.inl 0) v) :
    Nat.card (GlobalGoodB_GR Γ).ConnectedComponent ≤ 1 := by
  have hs : Function.Surjective (fun _ : Fin 1 =>
      (GlobalGoodB_GR Γ).connectedComponentMk (.inl 0)) := by
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨0, SimpleGraph.ConnectedComponent.eq.2 (h v)⟩
  simpa using Nat.card_le_card_of_surjective _ hs

/-- **The order of a graph of `Q` whose label lies at the block of `⊕` or `⊖`** (the count of
[II, Lemma 6.5 (4)]): for a normal regular plain graph of the kinds of [II, Def 3.2] with
[II, Def 3.2 (9)], only diffusive edges at `⊗`, the clause on the external atoms and the charge
pattern of the block normal form, or no internal atom and the diffusive edge `Θ_{⊗⊕}`, with
`Graph.QLabelInMISB`, whose `Q` label atom lies in the dotted block of `⊕` or of `⊖`: the
scaling order is at least `3`. -/
private theorem GlobalGoodB_ord3 {C N : ℕ} (hN : Γ.Normal C) (hTK : Γ.TKinds N) (hA : Γ.AtExternals)
    (hT : Γ.TensorDiffusive) (hcase : (n = 0 ∧ Γ.RootAtPlus) ∨ (Γ.ExtClause ∧ Γ.ColourInvB))
    (hPl : Γ.Plain) (hQL : Γ.QLabelInMISB) {c₀ : Comp (Atom 3 n)} (hc₀ : c₀ ∈ Γ.comps)
    {u : Atom 3 n} (hu : c₀.label = some (.Q, u))
    (hb : Γ.SameBlock u (.inl 1) ∨ Γ.SameBlock u (.inl 2)) : 3 ≤ Γ.ord := by
  classical
  have hwle : (Γ.comps.map GlobalGoodB_w).sum ≤ (Γ.comps.map fun c => c.kind.ord).sum :=
    List.sum_le_sum fun c hc => GlobalGoodB_w_le (List.all_eq_true.1 hTK c hc)
  have hsw := GlobalGoodB_sum_w Γ.comps
  have hord : Γ.ord = (Γ.comps.map fun c => c.kind.ord).sum - 2 * n := rfl
  have hRBle : Γ.comps.countP (fun c => GlobalGoodB_isRB c.kind && decide (c.x ≠ c.y)) ≤
      Γ.comps.countP (fun c => GlobalGoodB_isRB c.kind) :=
    List.countP_mono_left fun c _ h => by simp only [Bool.and_eq_true] at h; exact h.1
  have hcnt := GlobalGoodB_GR_count Γ
  rcases hcase with ⟨rfl, hR⟩ | ⟨hE, hC⟩
  · -- no internal atom: `Θ_{⊗⊕}` and a component at `⊖`
    obtain ⟨c₁, hc₁⟩ : ∃ c, c ∈ Γ.comps.filter fun c =>
        c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0) := by
      rcases h : Γ.comps.filter (fun c => c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0))
        with _ | ⟨c, l⟩
      · have := hA.1; rw [h] at this; simp at this
      · exact ⟨c, by rw [h]; exact List.mem_cons_self⟩
    obtain ⟨hc₁m, hc₁p⟩ := List.mem_filter.1 hc₁
    simp only [Bool.and_eq_true] at hc₁p
    have hr := List.all_eq_true.1 hR c₁ hc₁m
    simp only [hc₁p.1, hc₁p.2, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq] at hr
    have hRB₁ : GlobalGoodB_isRB c₁.kind = true := by simp [GlobalGoodB_isRB, hc₁p.1]
    obtain ⟨c₂, hc₂, hp₂⟩ := List.any_eq_true.1 hA.2.2
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp₂
    obtain ⟨hk₂, hat₂⟩ := hp₂
    have hne : c₁ ≠ c₂ := by
      rintro rfl
      rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hat₂ with h | h
      · rw [h1] at h; exact absurd h (by decide)
      · rw [h2] at h; exact absurd h (by decide)
      · rw [h1] at h; exact absurd h (by decide)
      · rw [h2] at h; exact absurd h (by decide)
    rcases hk₂ with (hk₂ | hk₂) | hk₂
    · have hs : 1 ≤ Γ.comps.countP fun c => c.kind.isSolid :=
        List.countP_pos_iff.2 ⟨c₂, hc₂, by rw [hk₂]; rfl⟩
      have hrb : 1 ≤ Γ.comps.countP fun c => GlobalGoodB_isRB c.kind :=
        List.countP_pos_iff.2 ⟨c₁, hc₁m, hRB₁⟩
      simp only [CharP.cast_eq_zero, mul_zero, sub_zero] at hord
      omega
    · have := GlobalGoodB_two_le_countP (p := fun c => GlobalGoodB_isRB c.kind) hne hRB₁
        (by simp [GlobalGoodB_isRB, hk₂]) hc₁m hc₂
      simp only [CharP.cast_eq_zero, mul_zero, sub_zero] at hord
      omega
    · have := GlobalGoodB_two_le_countP (p := fun c => GlobalGoodB_isRB c.kind) hne hRB₁
        (by simp [GlobalGoodB_isRB, hk₂, Kind.joinsMol]) hc₁m hc₂
      simp only [CharP.cast_eq_zero, mul_zero, sub_zero] at hord
      omega
  · -- with internal atoms
    set R := GlobalGoodB_GR Γ with hRdef
    have hint : ∀ b b' : Fin n, R.Reachable (.inr b) (.inr b') := fun b b' =>
      GlobalGoodB_GR_wt (hN.1.internal b b')
    have hpin : ∀ v : Atom 3 n, ¬ Γ.Unpinned v → ∃ b, R.Reachable v (.inr b) := by
      rintro (a | b) hv
      · have : ∃ b, Γ.SameBlock (.inl a) (.inr b) := by
          by_contra hn
          push Not at hn
          exact hv ⟨rfl, hn⟩
        obtain ⟨b, hb⟩ := this
        exact ⟨b, GlobalGoodB_GR_dot hb⟩
      · exact ⟨b, SimpleGraph.Reachable.refl _⟩
    have hU0 := SubstSPD_unpinned_zero Γ hT
    obtain ⟨b₀, hb₀⟩ : ∃ b, R.Reachable (.inl 0) (.inr b) := by
      obtain ⟨c, hc, hd, hat⟩ := (hE.2.2.1 hU0).1
      have hrb : GlobalGoodB_isRB c.kind = true := by simp [GlobalGoodB_isRB, hd]
      have hcr := GlobalGoodB_GR_comp hc hrb
      rcases hat with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · obtain ⟨b, hb⟩ := hpin _ hy
        rw [hx] at hcr
        exact ⟨b, hcr.trans hb⟩
      · obtain ⟨b, hb⟩ := hpin _ hx
        rw [hy] at hcr
        exact ⟨b, hcr.symm.trans hb⟩
    have hall : ∀ b, R.Reachable (.inl 0) (.inr b) := fun b => hb₀.trans (hint b₀ b)
    -- the label block
    obtain ⟨i, hi, hbi⟩ : ∃ i : Fin 3, (i = 1 ∨ i = 2) ∧ Γ.SameBlock u (.inl i) := by
      rcases hb with h | h
      · exact ⟨1, Or.inl rfl, h⟩
      · exact ⟨2, Or.inr rfl, h⟩
    have hRu : R.Reachable (.inl 0) u := by
      rcases hQL c₀ hc₀ u hu with h | ⟨-, h⟩
      · rcases u with a | b
        · exact absurd (GlobalGoodB_mis_int _ h) (MolMono_inl_not_mem_int Γ a)
        · exact hall b
      · rcases h with h | ⟨c', hc', a, hw, hca, -⟩
        · subst h
          exact b₀.elim0
        · have hrb : GlobalGoodB_isRB c'.kind = true := by
            obtain ⟨w, hw⟩ := hw; simp [GlobalGoodB_isRB, hw, Kind.joinsMol]
          have hcr := GlobalGoodB_GR_comp hc' hrb
          rcases hca with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hcr
          · exact (hall a).trans hcr.symm
          · exact (hall a).trans hcr
    have hRi : R.Reachable (.inl 0) (.inl i) := hRu.trans (GlobalGoodB_GR_dot hbi)
    -- the other external atom
    obtain ⟨j, hj, hij⟩ : ∃ j : Fin 3, (j = 1 ∨ j = 2) ∧ j ≠ i := by
      rcases hi with rfl | rfl
      · exact ⟨2, Or.inr rfl, by decide⟩
      · exact ⟨1, Or.inl rfl, by decide⟩
    have hfin : ∀ a i j : Fin 3, a ≠ 0 → a ≠ i → (i = 1 ∨ i = 2) → (j = 1 ∨ j = 2) → j ≠ i →
        a = j := by decide
    have hother : ∀ v, R.Reachable (.inl 0) v ∨ v = .inl j := by
      rintro (a | b)
      · by_cases ha0 : a = 0
        · subst ha0; exact Or.inl (SimpleGraph.Reachable.refl _)
        by_cases hai : a = i
        · subst hai; exact Or.inl hRi
        exact Or.inr (congrArg Sum.inl (hfin a i j ha0 hai hi hj hij))
      · exact Or.inl (hall b)
    by_cases hRj : R.Reachable (.inl 0) (.inl j)
    · have h1 : Nat.card R.ConnectedComponent ≤ 1 := GlobalGoodB_card_le_one (Γ := Γ) fun v => by
        rcases hother v with h | rfl
        · exact h
        · exact hRj
      have hs0 : (0 : ℤ) ≤ ((Γ.comps.countP fun c => c.kind.isSolid : ℕ) : ℤ) := by positivity
      omega
    · have h2 : Nat.card R.ConnectedComponent ≤ 2 :=
        GlobalGoodB_card_le_two (Γ := Γ) (.inl j) hother
      -- a solid edge at the other external atom
      have hsol : 1 ≤ Γ.comps.countP fun c => c.kind.isSolid := by
        have hat : ∃ c ∈ Γ.comps, (c.kind = .G .plus ∨ c.kind = .G .minus ∨
            c.kind.isDiffusive = true ∨ c.kind = .dot) ∧ (c.x = .inl j ∨ c.y = .inl j) := by
          rcases hj with rfl | rfl
          · obtain ⟨c, hc, hp⟩ := List.any_eq_true.1 hA.2.1
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
            obtain ⟨hk, hat⟩ := hp
            refine ⟨c, hc, ?_, hat⟩
            rcases hk with (h | h) | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
          · obtain ⟨c, hc, hp⟩ := List.any_eq_true.1 hA.2.2
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
            obtain ⟨hk, hat⟩ := hp
            refine ⟨c, hc, ?_, hat⟩
            rcases hk with (h | h) | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
        obtain ⟨c, hc, hk, hat⟩ := hat
        have hUj : Γ.Unpinned (.inl j) := by
          by_contra hp
          obtain ⟨b, hb⟩ := hpin _ hp
          exact hRj ((hall b).trans hb.symm)
        rcases hk with hk | hk | hk | hk
        · exact List.countP_pos_iff.2 ⟨c, hc, by rw [hk]; rfl⟩
        · exact List.countP_pos_iff.2 ⟨c, hc, by rw [hk]; rfl⟩
        all_goals exfalso
        · -- a diffusive edge at the other external atom
          have hcr := GlobalGoodB_GR_comp hc (by simp [GlobalGoodB_isRB, hk])
          by_cases hloop : c.x = c.y
          · rcases hj with rfl | rfl
            · have := (hE.2.2.2.2 hUj).2.1 c hc hk
              rcases hat with h | h
              · exact (this.1 h) (hloop ▸ h ▸ hUj)
              · exact (this.2 h) (hloop.symm ▸ h ▸ hUj)
            · have := ((hE.2.2.2.1 hUj).1 c hc hk)
              rcases hat with h | h
              · exact this.1 h
              · exact this.2 h
          · rcases hat with h | h <;> rw [h] at hcr
            · rcases hother c.y with h' | h'
              · exact hRj (h'.trans hcr.symm)
              · exact hloop (h.trans h'.symm)
            · rcases hother c.x with h' | h'
              · exact hRj (h'.trans hcr)
              · exact hloop (h'.trans h.symm)
        · -- a dotted edge at the other external atom
          have hcr := GlobalGoodB_GR_comp hc (by simp [GlobalGoodB_isRB, hk, Kind.joinsMol])
          have hloop : c.x ≠ c.y := (hPl c hc).2.2.2.1 hk
          rcases hat with h | h <;> rw [h] at hcr
          · rcases hother c.y with h' | h'
            · exact hRj (h'.trans hcr.symm)
            · exact hloop (h.trans h'.symm)
          · rcases hother c.x with h' | h'
            · exact hRj (h'.trans hcr)
            · exact hloop (h'.trans h.symm)
      omega

end Ord

/-! ## The dot excess -/

section DotEx

variable {k n : ℕ}

private theorem GlobalGoodB_dotExcess_nonneg (Γ : Graph k n) : 0 ≤ Γ.dotExcess := by
  have hle := SubstSPD_length_le (allAtoms k n) SubstSPD_allAtoms_nodup Γ.comps
  have hlen : (allAtoms k n).length = k + n := by simp [allAtoms]
  rw [hlen, Graph.dotBlocks_length_eq_card] at hle
  have := List.length_filter_le (fun c : Comp (Atom k n) => decide (c.x ≠ c.y))
    (Γ.comps.filter fun c => decide (c.kind = .dot))
  unfold Graph.dotExcess Graph.nDots
  push_cast
  omega

private theorem GlobalGoodB_ite_f' {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

private theorem GlobalGoodB_foldl_id {V : Type*} [DecidableEq V] :
    ∀ (cs : List (Comp V)) (P : List (List V)), (∀ c ∈ cs, c.kind ≠ .dot) →
      cs.foldl (fun P c => if c.kind = .dot then joinBlocks P c.x c.y else P) P = P
  | [], _, _ => rfl
  | c :: cs, P, h => by
    rw [List.foldl_cons, GlobalGoodB_ite_f' (h c List.mem_cons_self)]
    exact GlobalGoodB_foldl_id cs P fun c hc => h c (List.mem_cons_of_mem _ hc)

private theorem GlobalGoodB_dotExcess_zero {Γ : Graph k n} (hd : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    Γ.dotExcess = 0 := by
  rw [← Graph.dotsAcyclic_iff_dotExcess_eq_zero]
  unfold Graph.DotsAcyclic
  have h1 : (Γ.comps.filter fun c => decide (c.kind = .dot)) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by simpa using hd c hc
  have h2 : dotBlocks (allAtoms k n) Γ.comps = (allAtoms k n).map fun a => [a] := by
    unfold dotBlocks
    exact GlobalGoodB_foldl_id _ _ hd
  rw [h1, h2]
  simp [allAtoms]

end DotEx

/-! ## The atom maps of the `O_dot` forms of a substituted graph -/

section Maps

variable {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m} {g : Graph 3 n'}

/-- On a substituted graph of normal regular graphs, `O_dot` identifies two atoms only when they
lie in one dotted block. -/
private theorem GlobalGoodB_oDot_sameBlock {C C' : ℕ} (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hgN : g.Normal C') {t : Tracked 3 (m + n')} (ht : t ∈ oDotT (H.glue x y₁ y₂ g))
    {a b : Atom 3 (m + n')} (h : t.f a = t.f b) : (H.glue x y₁ y₂ g).SameBlock a b := by
  have hb := SubstSPD_glue_bal H x y₁ y₂ g hN hgN
  rcases mem_oDotT_cases ht with rfl | ⟨A, hA, hm⟩
  · change a = b at h
    subst h
    exact SimpleGraph.Reachable.refl _
  · rw [SubstSPD_splitPairs_nil hb, List.sublist_nil] at hA
    subst hA
    rw [SubstSPD_splitPairs_nil hb, SubstSPD_dotChoice_nil] at hm
    exact MergeSpec.sameBlock_of_f_eq (mergeT_spec hm) h

private theorem GlobalGoodB_eq_newA {v : Atom 3 n'} {j : Fin n'}
    (h : glueAtom x y₁ y₂ v = newA (n := m) j) : v = .inr j := by
  rcases v with i | j'
  · exact (SubstSPD_liftA_ne_newA (j := n') (![x, y₁, y₂] i) j h).elim
  · congr 1
    have := Sum.inr.inj h
    exact Fin.natAdd_injective n' m this

private theorem GlobalGoodB_newA_ne (j : Fin n') (u : Atom 3 m) :
    (newA j : Atom 3 (m + n')) ≠ liftA n' u := fun h => SubstSPD_liftA_ne_newA u j h.symm

variable (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
include hD

/-- The dotted edges of `H.glue x y₁ y₂ g` are the images of those of `g`. -/
private theorem GlobalGoodB_glue_dot {c : Comp (Atom 3 (m + n'))}
    (hc : c ∈ (H.glue x y₁ y₂ g).comps)
    (hk : c.kind = .dot) : ∃ c₀ ∈ g.comps, c₀.kind = .dot ∧ c = c₀.map (glueAtom x y₁ y₂) := by
  rw [GlobalGoodB_glue_comps, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact absurd hk (SubstSPD_H_nodot H x y₁ y₂ hD c₀ hc₀)
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact ⟨c₀, hc₀, hk, rfl⟩

/-- A path of dotted edges of `H.glue x y₁ y₂ g` from the image of an internal atom `j` of `g` to
an atom that is not the image of an internal atom of `g` gives a path of dotted edges of `g` from
`j` to an external atom. -/
private theorem GlobalGoodB_dot_walk {z z' : Atom 3 (m + n')}
    (w : (H.glue x y₁ y₂ g).dotGraph.Walk z z') :
    ∀ j : Fin n', z = newA j → (∀ j' : Fin n', z' ≠ newA j') →
      ∃ i : Fin 3, g.SameBlock (.inr j) (.inl i) := by
  induction w with
  | nil => intro j hz hz'; exact absurd hz (hz' j)
  | @cons a b c hadj p ih =>
    intro j hz hz'
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, hrel⟩ := hadj
    have key : ∀ c₁ ∈ (H.glue x y₁ y₂ g).comps, c₁.kind = .dot → c₁.x = a → c₁.y = b →
        ∃ i : Fin 3, g.SameBlock (.inr j) (.inl i) := by
      intro c₁ hc₁ hk hx' hy'
      obtain ⟨c₀, hc₀, hk₀, rfl⟩ := GlobalGoodB_glue_dot hD hc₁ hk
      have hxj : c₀.x = .inr j := GlobalGoodB_eq_newA (by rw [← hz]; exact hx')
      have hadj₀ : g.SameBlock c₀.x c₀.y := by
        by_cases hxy : c₀.x = c₀.y
        · exact hxy ▸ SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable
            ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hxy, Or.inl ⟨c₀, hc₀, hk₀, rfl, rfl⟩⟩)
      rw [hxj] at hadj₀
      rcases hcy : c₀.y with i | j₁
      · exact ⟨i, hcy ▸ hadj₀⟩
      · obtain ⟨i, hi⟩ := ih j₁ (by rw [← hy']; simp only [Comp.map, hcy]; rfl) hz'
        exact ⟨i, (hcy ▸ hadj₀).trans hi⟩
    have key' : ∀ c₁ ∈ (H.glue x y₁ y₂ g).comps, c₁.kind = .dot → c₁.x = b → c₁.y = a →
        ∃ i : Fin 3, g.SameBlock (.inr j) (.inl i) := by
      intro c₁ hc₁ hk hx' hy'
      obtain ⟨c₀, hc₀, hk₀, rfl⟩ := GlobalGoodB_glue_dot hD hc₁ hk
      have hyj : c₀.y = .inr j := GlobalGoodB_eq_newA (by rw [← hz]; exact hy')
      have hadj₀ : g.SameBlock c₀.y c₀.x := by
        by_cases hxy : c₀.y = c₀.x
        · exact hxy ▸ SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable
            ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hxy, Or.inr ⟨c₀, hc₀, hk₀, rfl, rfl⟩⟩)
      rw [hyj] at hadj₀
      rcases hcx : c₀.x with i | j₁
      · exact ⟨i, hcx ▸ hadj₀⟩
      · obtain ⟨i, hi⟩ := ih j₁ (by rw [← hx']; simp only [Comp.map, hcx]; rfl) hz'
        exact ⟨i, (hcx ▸ hadj₀).trans hi⟩
    rcases hrel with ⟨c₁, hc₁, hk, hx', hy'⟩ | ⟨c₁, hc₁, hk, hx', hy'⟩
    · exact key c₁ hc₁ hk hx' hy'
    · exact key' c₁ hc₁ hk hx' hy'

/-- **The label atom of a substituted `Q`-graph at an atom of `H`.** If the image of an atom `u`
of `g` other than `⊗` lies in the dotted block of the image of an atom `w` of `H`, in a graph `g`
without dotted edge at `⊗`, then `w` is `y₁` or `y₂`, and `u` lies in the dotted block of `⊕` or
of `⊖`. -/
private theorem GlobalGoodB_label_host (hT : g.TensorDiffusive) {u : Atom 3 n'} (hu0 : u ≠ .inl 0)
    {w : Atom 3 m}
    (h : (H.glue x y₁ y₂ g).SameBlock (glueAtom x y₁ y₂ u) (liftA n' w)) :
    (w = y₁ ∨ w = y₂) ∧ (g.SameBlock u (.inl 1) ∨ g.SameBlock u (.inl 2)) := by
  have hU0 := SubstSPD_unpinned_zero g hT
  have hnodot0 : ∀ c ∈ g.comps, c.kind = .dot → c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
    intro c hc hk
    have := List.all_eq_true.1 hT c hc
    constructor <;> intro h0 <;> simp [h0, hk, Kind.isDiffusive] at this
  have hfin : ∀ i : Fin 3, i ≠ 0 → i = 1 ∨ i = 2 := by decide
  have hlw : ∀ i : Fin 3, i ≠ 0 → glueAtom x y₁ y₂ (.inl i) = liftA n' w → w = y₁ ∨ w = y₂ := by
    intro i hi he
    have := SubstSPD_liftA_inj he
    rcases hfin i hi with rfl | rfl
    · exact Or.inl this.symm
    · exact Or.inr this.symm
  refine ⟨?_, ?_⟩
  · by_cases heq : glueAtom x y₁ y₂ u = liftA n' w
    · rcases u with i | j
      · exact hlw i (fun h => hu0 (by rw [h])) heq
      · exact absurd heq (GlobalGoodB_newA_ne j w)
    · obtain ⟨wk⟩ := h.symm
      generalize hA : liftA n' w = A at wk
      generalize hB : glueAtom x y₁ y₂ u = B at wk
      cases wk with
      | nil => exact absurd (hB.trans hA.symm) heq
      | cons hadj _ =>
        rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
        obtain ⟨-, hrel⟩ := hadj
        rcases hrel with ⟨c₁, hc₁, hk, hx', -⟩ | ⟨c₁, hc₁, hk, -, hy'⟩
        · obtain ⟨c₀, hc₀, hk₀, rfl⟩ := GlobalGoodB_glue_dot hD hc₁ hk
          rcases hcx : c₀.x with i | j
          · refine hlw i (fun h => (hnodot0 c₀ hc₀ hk₀).1 (by rw [hcx, h])) ?_
            rw [hA, ← hx']; simp [Comp.map, hcx]
          · exfalso
            have : (c₀.map (glueAtom x y₁ y₂)).x = newA j := by simp [Comp.map, hcx]; rfl
            rw [hx', ← hA] at this
            exact GlobalGoodB_newA_ne j w this.symm
        · obtain ⟨c₀, hc₀, hk₀, rfl⟩ := GlobalGoodB_glue_dot hD hc₁ hk
          rcases hcy : c₀.y with i | j
          · refine hlw i (fun h => (hnodot0 c₀ hc₀ hk₀).2 (by rw [hcy, h])) ?_
            rw [hA, ← hy']; simp [Comp.map, hcy]
          · exfalso
            have : (c₀.map (glueAtom x y₁ y₂)).y = newA j := by simp [Comp.map, hcy]; rfl
            rw [hy', ← hA] at this
            exact GlobalGoodB_newA_ne j w this.symm
  · rcases u with i | j
    · have hi : i ≠ 0 := fun h => hu0 (by rw [h])
      rcases hfin i hi with rfl | rfl
      · exact Or.inl (SimpleGraph.Reachable.refl _)
      · exact Or.inr (SimpleGraph.Reachable.refl _)
    · obtain ⟨wk⟩ := h
      obtain ⟨i, hi⟩ := GlobalGoodB_dot_walk hD wk j rfl fun j' h' =>
        GlobalGoodB_newA_ne j' w h'.symm
      have hi0 : i ≠ 0 := by
        rintro rfl
        exact hU0.2 j hi.symm
      rcases hfin i hi0 with rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi

omit hD in
/-- **At `y₁ = y₂` no weight or solid edge of `H` is at `y₁`** ([II, Strategy 6.6, Step 1]): the
atom `y₁ = y₂` lies in the minimal isolated subset of `G = H.glue x y₁ y₂ (tVar true)`, which is
locally standard, and already carries the two solid edges `G_{y₁α}` and `Ḡ_{y₂α}`. -/
private theorem GlobalGoodB_y_free (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hx : x.isRight = true)
    (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB')
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (hM : (H.glue x y₁ y₂ (tVar true)).MISLocStdB) (hP : (H.glue x y₁ y₂ (tVar true)).Plain)
    (hy : y₁ = y₂) {c : Comp (Atom 3 m)} (hc : c ∈ H.comps) (hr : c.kind.isRandom = true) :
    c.x ≠ y₁ ∧ c.y ≠ y₁ := by
  classical
  subst hy
  obtain ⟨-, -, -, -, -, -, -, hm₁, -⟩ := SubstSPD_host H x y₁ y₁ hx hy₁ hy₂ hD hI hst
  obtain ⟨a, rfl⟩ : ∃ a, y₁ = .inr a := by
    rcases y₁ with a | a
    · simp at hy₁
    · exact ⟨a, rfl⟩
  set G := H.glue x (.inr a) (.inr a) (tVar true) with hG
  set Y : Atom 3 (m + 1) := liftA 1 (.inr a) with hY
  have hloc : G.wt Y = 0 ∧ (G.deg Y = 0 ∨ (G.deg Y = 2 ∧ G.stdNeutralAt Y = true)) :=
    hM.2 (Fin.castAdd 1 a) hm₁
  have hcm : c.map (liftA 1) ∈ G.comps := by
    rw [GlobalGoodB_G_comps]; exact List.mem_append_left _ (List.mem_map.2 ⟨c, hc, rfl⟩)
  have hdeg : G.deg Y = (H.comps.map (Comp.map (liftA 1))).countP
      (fun c => c.kind.isSolid && (c.x == Y || c.y == Y)) + 2 := by
    unfold Graph.deg
    rw [← List.countP_eq_length_filter, GlobalGoodB_G_comps, List.countP_append]
    congr 1
    simp [mkC, Kind.isSolid, hY, liftA, newA]
  have hwt : G.wt Y = (H.comps.map (Comp.map (liftA 1))).countP
      (fun c => (c.kind matches .weight _ | .light _) && c.x == Y) + 0 := by
    unfold Graph.wt
    rw [← List.countP_eq_length_filter, GlobalGoodB_G_comps, List.countP_append]
    congr 1
  have hinj : ∀ v : Atom 3 m, liftA 1 v = Y → v = .inr a := fun v h => SubstSPD_liftA_inj h
  have hpl := hP _ hcm
  obtain ⟨-, hinv, hwD, -, hwf, -⟩ := hpl
  constructor <;> intro hxy
  · cases hk : c.kind with
    | G ch =>
      have : 1 ≤ (H.comps.map (Comp.map (liftA 1))).countP
          (fun c => c.kind.isSolid && (c.x == Y || c.y == Y)) :=
        List.countP_pos_iff.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, by
          simp [Comp.map, hk, Kind.isSolid, hxy, hY]⟩
      rcases hloc.2 with h | ⟨h, -⟩ <;> omega
    | weight ch =>
      have : 1 ≤ (H.comps.map (Comp.map (liftA 1))).countP
          (fun c => (c.kind matches .weight _ | .light _) && c.x == Y) :=
        List.countP_pos_iff.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, by
          simp [Comp.map, hk, hxy, hY]⟩
      omega
    | light ch =>
      have : 1 ≤ (H.comps.map (Comp.map (liftA 1))).countP
          (fun c => (c.kind matches .weight _ | .light _) && c.x == Y) :=
        List.countP_pos_iff.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, by
          simp [Comp.map, hk, hxy, hY]⟩
      omega
    | inv ch => exact hinv ch (by simp [Comp.map, hk])
    | wD ch d => exact hwD ch d (by simp [Comp.map, hk])
    | _ => simp [hk, Kind.isRandom] at hr
  · cases hk : c.kind with
    | G ch =>
      have : 1 ≤ (H.comps.map (Comp.map (liftA 1))).countP
          (fun c => c.kind.isSolid && (c.x == Y || c.y == Y)) :=
        List.countP_pos_iff.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, by
          simp [Comp.map, hk, Kind.isSolid, hxy, hY]⟩
      rcases hloc.2 with h | ⟨h, -⟩ <;> omega
    | weight ch =>
      have hyx : c.y = c.x := SubstSPD_liftA_inj (hwf (by simp [Comp.map, hk, Kind.isWeight]))
      have : 1 ≤ (H.comps.map (Comp.map (liftA 1))).countP
          (fun c => (c.kind matches .weight _ | .light _) && c.x == Y) :=
        List.countP_pos_iff.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, by
          simp [Comp.map, hk, ← hyx, hxy, hY]⟩
      omega
    | light ch =>
      have hyx : c.y = c.x := SubstSPD_liftA_inj (hwf (by simp [Comp.map, hk, Kind.isWeight]))
      have : 1 ≤ (H.comps.map (Comp.map (liftA 1))).countP
          (fun c => (c.kind matches .weight _ | .light _) && c.x == Y) :=
        List.countP_pos_iff.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, by
          simp [Comp.map, hk, ← hyx, hxy, hY]⟩
      omega
    | inv ch => exact hinv ch (by simp [Comp.map, hk])
    | wD ch d => exact hwD ch d (by simp [Comp.map, hk])
    | _ => simp [hk, Kind.isRandom] at hr

end Maps

/-! ## Row (4) of [II, Lemma 6.5] for one graph of `Q` and one `Q`-expansion -/

/-- **Row (4) of [II, Lemma 6.5]** in the block reading, for one graph `g` of `Q` and one
`Q`-expansion `E` of each `O_dot` form at its label atom, with the hypotheses on `𝒯` of
[II, Def 3.2] at order `n - 1` and of [II, Def 6.3], under the hypotheses of [II, Lemma 6.5] on
`G = H.glue x y₁ y₂ (tVar true)` and `G` plain: the substituted graph `G̃` has the invariant
`Graph.InvB'`; every `O_dot` form `t` of `G̃` is normal regular without dotted edges, plain, with
the invariant `Graph.InvB'`, sequentially pre-deterministic with `Graph.QLabelInMISB` if it is a
`Q`-graph; and for every `Q`-expansion `E` of `t` at its label atom with the clause `qexpClauseB`,
whose output graphs are reached by `Graph.MolMono` maps with the weak isolation of (F6) of
`QExpFamilyStmt`, every output graph has dot excess `0` and is globally standard without labels of
scaling order `≥ ord G + 1`, a sequentially pre-deterministic `Q`-graph with
`Graph.QLabelInMISB`, or doubly connected of scaling order `> D`. -/
private theorem GlobalGoodB_row4 :
  ∀ (n D : ℕ) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m),
    3 ≤ n → (n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    4 ≤ (H.glue x y₁ y₂ (tVar true)).ord → (H.glue x y₁ y₂ (tVar true)).ord ≤ n →
    (H.glue x y₁ y₂ (tVar true)).InvB' → (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    gsPM' (H.glue x y₁ y₂ (tVar true)) → ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
    (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    (H.glue x y₁ y₂ (tVar true)).Plain →
    ∀ g ∈ 𝒯.Q, (H.glue x y₁ y₂ g.2.swapSolid).InvB' ∧
      ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧ t.g.DotFree ∧
        t.g.Plain ∧ t.g.InvB' ∧ (t.g.IsQGraph → spdPM' t.g ∧ t.g.QLabelInMISB) ∧
        ∀ (x' : Fin t.nOut) (E : TExpansion 3 t.nOut), t.g.IsQFormAt (.inr x') →
          ¬ t.g.IsQGraph → qexpClauseB D x' t.g E →
          (∀ s ∈ E, t.g.MolMono s.g s.f ∧
            (t.g.UnlabelledFreeAtBlock (.inr x') → s.g.LabelFree → s.g.ord ≤ D →
              ∀ P' : Finset (Atom 3 s.nOut), s.g.toMG'.IsProperIso s.g.toMG'.int P' →
                t.g.molRep (.inr x') ∈ t.g.molPull s.g s.f P' →
                (∀ c ∈ t.g.comps, c.label = none → c.kind.isRandom = true → ∀ u ∈ [c.x, c.y],
                  t.g.molRep (t.g.flatAtom u) ∉ t.g.molPull s.g s.f P') →
                s.g.toMG'.IsWeaklyIso P')) →
          ∀ s ∈ E, s.g.dotExcess = 0 ∧
            ((s.g.LabelFree ∧ gsPM' s.g ∧ (H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ s.g.ord) ∨
            (s.g.IsQGraph ∧ spdPM' s.g ∧ s.g.QLabelInMISB) ∨
            ((D : ℤ) < s.g.ord ∧ s.g.DoublyConnected)) := by
  intro n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2 hI hT hgs hnr hM hst hPG g hg
  obtain ⟨hnD, hSh, hDef⟩ := hcore
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  obtain ⟨n', g₀⟩ := g
  have hallQ : (⟨n', g₀⟩ : Σ n, Graph 3 n) ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by simp [hg]
  have hall : (⟨n', g₀⟩ : Σ n, Graph 3 n) ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
  obtain ⟨⟨C', hgN⟩, hTK, hAE, hgDC⟩ := hSh.1.1 _ hallQ
  obtain ⟨hgQ, hk2⟩ := hSh.2.2.2.1 _ hg
  obtain ⟨-, hQL, hcase⟩ := hDef.1.2.2 _ hg
  obtain ⟨hgT, hX, hNL, hlab⟩ := hDef.2.1 _ hall
  have hPM4 := hDef.2.2.2.2.1 _ hg
  have hRg : g₀.RgCheck := hDef.2.2.2.2.2.1 ⟨n', g₀⟩ (by simp [hg])
  have hroot : n' ≠ 0 → ¬ g₀.DiagRecoll → g₀.RootedAtExt :=
    hDef.2.2.2.2.2.2.1 ⟨n', g₀⟩ (by simp [hg])
  have hgPl : g₀.Plain := TRec.plain_of_def63 hDef _ hallQ
  have hQP : n' = 0 → g₀.QLabelAtPlus := TRec.qLabelAtPlus_of_def63 hDef _ hg
  set G := H.glue x y₁ y₂ (tVar true) with hG
  set Gt := H.glue x y₁ y₂ g₀.swapSolid with hGt
  set γ : Atom 3 n' → Atom 3 (m + n') := glueAtom x y₁ y₂ with hγ
  -- the substituted graph
  have hGtI : Gt.InvB' := globalGood_row4_invB n D 𝒯 m C H x y₁ y₂ hn ⟨hnD, hSh, hDef⟩
    (fun g hg => (hDef.1.2.2 g hg).2.2.imp And.left id) hL hN hd ho1 ho2 hI hT hgs hnr hM hst
    _ hg
  have h5 : n' = 0 ∨ g₀.DiagRecoll ∨ g₀.RootedAtExt := by
    by_cases h0 : n' = 0
    · exact Or.inl h0
    by_cases hDg : g₀.DiagRecoll
    · exact Or.inr (Or.inl hDg)
    exact Or.inr (Or.inr (hroot h0 hDg))
  have hGtDC : Gt.DoublyConnected := substDCB m n' H x y₁ y₂ g₀ hd hI.1 hst hgDC h5
  have hGtord : Gt.ord = G.ord - 2 + g₀.ord := by
    have e1 : Gt.ord = H.ord + g₀.swapSolid.ord := glue_ord 3 m n' H x y₁ y₂ g₀.swapSolid
    have e2 : G.ord = H.ord + (tVar true).ord := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
    have e3 : g₀.swapSolid.ord = g₀.ord := (swapSolid_basic 3 n' g₀).2.1
    rw [e1, e2, e3, SubstSPD_tVar_ord]
    ring
  have hγR : ∀ u, (γ u).isRight = true := SubstMol_glueAtom_isRight hx hy₁ hy₂
  -- the labels of `g`
  obtain ⟨u₀, -, hu₀⟩ := id hgQ
  have hlabQ : ∀ c ∈ g₀.comps, ∀ q u, c.label = some (q, u) → q = .Q ∧ u = u₀ := by
    intro c hc q u hl
    have := hu₀ c hc (Or.inr (by rw [hl]; rfl))
    rw [hl] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this
  have hclass := fun {P} (hP : Gt.toMG'.IsProperIso Gt.toMG'.int P) =>
    GlobalGoodB_classify hd hx hy₁ hy₂ hI hgs hst hgN hgT hAE hcase hgPl hTK hQL hQP hP
  refine ⟨hGtI, fun t ht => ?_⟩
  obtain ⟨hN', hd', hε, hε', hdc⟩ := glue_oDotT_normal m n' C C' H x y₁ y₂ g₀.swapSolid hx hy₁
    hy₂ hL hN hd (Graph.swapSolid_Normal hgN) (SubstSPD_swap_otimesNoDot hgT)
    (by rw [SubstSPD_swap_dotExcess]; exact hX) (SubstDC_swap_rgCheck hRg)
    (by rw [SubstSPD_swap_labels]; exact hlab) (SubstSPD_swap_noLabDot hNL) t ht
  have htI : t.g.InvB' := qElemStep_invB ⟨_, Gt⟩ ⟨t.nOut, t.g⟩ (QElemStep.dot Gt t ht) hGtI
  have htP : t.g.Plain := GlobalGoodB_plain_of
    (GlobalGoodB_oDot_PW (GlobalGoodB_glue_PW hPG hgPl) ht) hd'
  have hMD : Gt.MolMono t.g t.f := molMono_oDotT Gt hGtI t ht
  -- the label of `t`
  have hK1 : ∀ c ∈ g₀.comps, ∀ q u, c.label = some (q, u) →
      (∀ P', t.g.toMG'.IsProperIso t.g.toMG'.int P' → t.g.molRep (t.f (γ u)) ∈ P') ∧
        t.g.molRep (t.f (γ u)) ∈ t.g.toMG'.MIS := by
    intro c hc q u hl
    obtain ⟨rfl, -⟩ := hlabQ c hc q u hl
    exact GlobalGoodB_mis_pull hMD hGtI (hγR u) fun P hP =>
      (hclass hP).1 c hc u hl
  have hloc : ∀ c' ∈ t.g.comps, ∀ q w', c'.label = some (q, w') →
      ∃ c ∈ g₀.comps, ∃ u, c.label = some (q, u) ∧ w' = t.f (γ u) := by
    intro c' hc' q w' hl
    obtain ⟨c, hc, w, hcl, hw⟩ := GlobalGoodB_oDot_label ht hc' hl
    simp only at hw hcl
    obtain ⟨c₀, hc₀, u, hcl₀, hu⟩ := GlobalGoodB_glue_label hL hc hcl
    simp only at hcl₀ hu
    exact ⟨c₀, hc₀, u, hcl₀, by rw [hw, hu]⟩
  -- the unlabelled weights and solid edges of `t`
  have hunl : ∀ c' ∈ t.g.comps, c'.label = none → c'.kind.isRandom = true →
      ∀ u' ∈ [c'.x, c'.y], ∃ w : Atom 3 m, (∃ cH ∈ H.comps, cH.kind.isRandom = true ∧
        w ∈ [cH.x, cH.y]) ∧ u' = t.f (liftA n' w) := by
    intro c' hc' hl hr u' hu'
    obtain ⟨c, hc, hcl, hcr, hends⟩ := GlobalGoodB_oDot_unl ht hc' hl hr
    obtain ⟨cH, hcH, rfl⟩ := GlobalGoodB_glue_unl hgQ hc hcl hcr
    obtain ⟨v, hv, rfl⟩ := hends u' hu'
    have hr' : cH.kind.isRandom = true := by simpa [Comp.map] using hcr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Comp.map] at hv
    rcases hv with rfl | rfl
    · exact ⟨cH.x, ⟨cH, hcH, hr', by simp⟩, rfl⟩
    · exact ⟨cH.y, ⟨cH, hcH, hr', by simp⟩, rfl⟩
  have hdotfree : ∀ c ∈ t.g.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true :=
    fun c hc hk => absurd hk (hd' c hc)
  refine ⟨hN', hd', htP, htI, fun hQ => ⟨htI.1, fun c' hc' w' hl => ?_⟩, ?_⟩
  · obtain ⟨c, hc, u, hcl, rfl⟩ := hloc c' hc' .Q w' hl
    exact Or.inl (hK1 c hc .Q u hcl).2
  intro x' E hQF hnQ hqe hmap s hs
  obtain ⟨⟨C'', hout⟩, hinv⟩ := hqe
  obtain ⟨⟨hQB, hcl, -, hiv⟩, -⟩ := hout s hs
  obtain ⟨-, hordle, -, hdex, -, hDCi, -⟩ := hQB
  have hsI : s.g.InvB' := hinv htI s hs
  -- the label atom `x'`
  obtain ⟨c₁, hc₁, hl₁⟩ := hQF.1
  obtain ⟨cg, hcg, ug, hclg, hxg⟩ := hloc c₁ hc₁ .Q _ hl₁
  have hKx : ∀ P', t.g.toMG'.IsProperIso t.g.toMG'.int P' → t.g.molRep (.inr x') ∈ P' := by
    rw [hxg]; exact (hK1 cg hcg .Q ug hclg).1
  have hdex0 : s.g.dotExcess = 0 :=
    le_antisymm (hdex.trans (GlobalGoodB_dotExcess_zero hd').le)
      (GlobalGoodB_dotExcess_nonneg _)
  refine ⟨hdex0, ?_⟩
  by_cases hD' : (D : ℤ) < s.g.ord
  · exact Or.inr (Or.inr ⟨hD', hDCi (hdc hGtDC)⟩)
  push Not at hD'
  have hcl' : s.g.Plain ∧ (s.g.LabelFree ∨ s.g.IsQGraphAt (s.f (.inr x'))) := by
    rcases hcl with h | ⟨h, -⟩
    · exact h
    · omega
  rcases hcl'.2 with hLF | hQG
  · -- outputs without labels
    left
    -- the atoms of `t` read from the atoms of `H`
    have hhostQ : ∀ (Q₁ : Finset (Atom 3 t.nOut)), Q₁ ⊆ t.g.toMG'.int →
        (¬ ∃ h : Fin m, Gt.molRep (liftA n' (.inr h)) ∈ Gt.molPull t.g t.f Q₁) →
        ∀ w : Atom 3 m, t.g.molRep (t.f (liftA n' w)) ∉ Q₁ := by
      intro Q₁ hQ₁ hh w hw
      rcases w with a | h
      · have : t.f (liftA n' (.inl a)) = .inl a := GlobalGoodB_oDot_inl ht a
        rw [this] at hw
        exact MolMono_inl_not_mem_int t.g a (hQ₁ hw)
      · refine hh ⟨h, Finset.mem_filter.2 ⟨MolMono_molRep_mem_int Gt _, ?_⟩⟩
        rw [MolMono_rep_map' hMD rfl]
        exact hw
    refine ⟨hLF, ⟨hsI.1, fun P' hP' => ?_⟩, ?_⟩
    · obtain ⟨hQ₁, hred₁⟩ := (hmap s hs).1.pull_properIso htI hP'
      obtain ⟨hQ₀, hred₀⟩ := hMD.pull_properIso hGtI hQ₁
      by_cases hh : ∃ h : Fin m, Gt.molRep (liftA n' (.inr h)) ∈ Gt.molPull t.g t.f
          (t.g.molPull s.g s.f P')
      · have h2 : 2 ≤ Gt.toMG'.redCount (Gt.molPull t.g t.f (t.g.molPull s.g s.f P')) :=
          (hclass hQ₀).2 hh
        exact (GlobalGoodB_weak_iff _).2 ⟨hP'.1, by omega⟩
      · have hno := hhostQ _ hQ₁.1.1 hh
        have hfree : t.g.UnlabelledFreeAtBlock (.inr x') := by
          intro c hc hl hr
          have hsb : ∀ u v, t.g.SameBlock u v ↔ u = v :=
            Graph.sameBlock_iff_eq t.g fun c hc hk => absurd hk (hd' c hc)
          rw [hsb, hsb]
          constructor
          · intro he
            obtain ⟨w, -, hw⟩ := hunl c hc hl hr c.x (by simp)
            exact hno w (by rw [← hw, he]; exact hKx _ hQ₁)
          · intro he
            obtain ⟨w, -, hw⟩ := hunl c hc hl hr c.y (by simp)
            exact hno w (by rw [← hw, he]; exact hKx _ hQ₁)
        refine (hmap s hs).2 hfree hLF hD' P' hP' (hKx _ hQ₁) fun c hc hl hr u hu => ?_
        rw [SubstMol_flatAtom hdotfree]
        obtain ⟨w, -, rfl⟩ := hunl c hc hl hr u hu
        exact hno w
    · -- the order
      have hk2' : (2 : ℤ) ≤ g₀.ord := hk2
      by_cases hfree : t.g.UnlabelledFreeAtBlock (.inr x')
      · have h1 := (hiv hfree hLF hD').1
        by_cases hε0 : y₁ = y₂ ∧ g₀.swapSolid.PMBlock
        · have h3 : t.g.ord + 2 = Gt.ord := hε hε0
          have h4 : 4 ≤ g₀.ord := hPM4 ((SubstSPD_swap_pmBlock g₀).1 hε0.2)
          omega
        · have h3 : t.g.ord = Gt.ord := hε' hε0
          omega
      · -- the label atom carries an unlabelled weight or solid edge of `H`
        unfold Graph.UnlabelledFreeAtBlock at hfree
        push Not at hfree
        obtain ⟨c, hc, hl, hr, hsb⟩ := hfree
        have hsb' : ∀ u v, t.g.SameBlock u v ↔ u = v :=
          Graph.sameBlock_iff_eq t.g fun c hc hk => absurd hk (hd' c hc)
        have hxin : (Sum.inr x' : Atom 3 t.nOut) ∈ [c.x, c.y] := by
          by_cases h : t.g.SameBlock c.x (.inr x')
          · rw [hsb'] at h; simp [h]
          · have h' := hsb h
            rw [hsb'] at h'; simp [h']
        obtain ⟨w, ⟨cH, hcH, hcHr, hwH⟩, hw⟩ := hunl c hc hl hr _ hxin
        have hfeq : t.f (γ ug) = t.f (liftA n' w) := hxg.symm.trans hw
        have hblk := GlobalGoodB_oDot_sameBlock hN (Graph.swapSolid_Normal hgN) ht hfeq
        have hu0 : ug ≠ .inl 0 := by
          rintro rfl
          rcases hQL cg hcg _ hclg with h | ⟨h, -⟩
          · exact MolMono_inl_not_mem_int g₀ 0 (GlobalGoodB_mis_int _ h)
          · rcases h with h | h <;> exact absurd (Sum.inl.inj h) (by decide)
        obtain ⟨hwy, hub⟩ := GlobalGoodB_label_host hd (SubstSPD_swap_tensor g₀ hgT) hu0 hblk
        have hub' : g₀.SameBlock ug (.inl 1) ∨ g₀.SameBlock ug (.inl 2) := by
          rw [SubstSPD_swap_sameBlock, SubstSPD_swap_sameBlock] at hub
          exact hub
        have hk3 : 3 ≤ g₀.ord := GlobalGoodB_ord3 hgN hTK hAE hgT hcase hgPl hQL hcg hclg hub'
        have hyne : y₁ ≠ y₂ := by
          intro hy
          have := GlobalGoodB_y_free hd hx hy₁ hy₂ hI hst hM hPG hy hcH hcHr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwH
          rcases hwy with rfl | rfl <;> rcases hwH with h | h
          · exact this.1 h.symm
          · exact this.2 h.symm
          · exact this.1 (h.symm.trans hy.symm)
          · exact this.2 (h.symm.trans hy.symm)
        have h3 : t.g.ord = Gt.ord := hε' fun h => hyne h.1
        omega
  · -- `Q`-graph outputs
    right; left
    refine ⟨⟨_, hQG⟩, hsI.1, fun c hc v hv => Or.inl ?_⟩
    have hv' := hQG.2 c hc (Or.inr (by rw [hv]; rfl))
    rw [hv] at hv'
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hv'
    rw [hv']
    exact (GlobalGoodB_mis_pull (hmap s hs).1 htI rfl hKx).2

/-! ## The statement and its proof -/

/-- **[II, Lemma 6.5]** (1)–(5) in the block reading, with row (4) read on a family `𝔈` of
`Q`-expansions with the clauses `QExpFamilyStmt`, for a plain graph
`G = H.glue x y₁ y₂ (tVar true)`: the statement of [II, Lemma 6.5] with the premise
`G.Plain` added and the last conjunct of (4) taken over the output graphs of `𝔈` at the label atom
of each `O_dot` form of a substituted `Q`-graph. For `n ≥ 3`, an `(n - 1)`-th order `T`-expansion
`𝒯` with error order `D` (with the clauses `TRec.Def63`), and `G` normal regular, plain, without
dotted edges, of scaling order `o` with `4 ≤ o ≤ n`, with `H` without labels, the invariant
`Graph.InvB'`, only diffusive edges at `⊗`, globally standard in the block reading, not a
`⊕/⊖`-recollision graph, with a locally standard minimal isolated subset and the blue solid edge
chosen by Step 2, every `O_dot` form `t` of the substitution of a graph `g` is normal regular
without dotted edges, and
(1), (2) for the leading terms, the terms of `Σ_T` and of `R` and the recollision terms of
[II, (4.15)], `t` is globally standard without labels, of scaling order `≥ o + 1`, or `y₁ = y₂`
and `t` has scaling order `o` and fewer solid edges than `G`;
(3) for a graph of `A`, `t` has no labels, and is sequentially pre-deterministic of scaling order
`≥ n + 1`, or (3′) `y₁ = y₂`, `⊕`, `⊖` lie in one block of `g`, and `t` is globally standard of
scaling order `≥ o + 1`;
(4) for a `Q`-graph, the substituted graph `G̃` has the invariant `Graph.InvB'`; every `Q`-graph
among the `O_dot` forms of `G̃` is sequentially pre-deterministic with `Graph.QLabelInMISB`, and
for every `O_dot` form of `G̃` of the form `Γ₀ Q_x(Γ̃₀)` that is not a `Q`-graph, the
`Q`-expansion `𝔈` at its label atom `x` gives graphs of dot excess `0` that are globally standard
without labels of scaling order `≥ o + 1`, sequentially pre-deterministic `Q`-graphs with
`Graph.QLabelInMISB`, or doubly connected graphs of scaling order `> D`;
(5) for a graph of `Err`, `t` is doubly connected of scaling order `≥ o + D - 3`, hence `> D`. -/
def globalGoodStmtB' : Prop :=
  ∀ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 →
  ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m)
    (x y₁ y₂ : Atom 3 m),
    3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    4 ≤ (H.glue x y₁ y₂ (tVar true)).ord → (H.glue x y₁ y₂ (tVar true)).ord ≤ n →
    (H.glue x y₁ y₂ (tVar true)).InvB' → (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    gsPM' (H.glue x y₁ y₂ (tVar true)) → ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
    (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    (H.glue x y₁ y₂ (tVar true)).Plain →
    (∀ g ∈ leadExp ++ sigmaTExp (n - 1) ++ 𝒯.R ++ tVarCorr,
      ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧ t.g.DotFree ∧
        t.g.LabelFree ∧ gsPM' t.g ∧
        ((H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord ∨
          (y₁ = y₂ ∧ t.g.ord = (H.glue x y₁ y₂ (tVar true)).ord ∧
            t.g.solidN < (H.glue x y₁ y₂ (tVar true)).solidN))) ∧
    (∀ g ∈ 𝒯.A, ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ t.g.LabelFree ∧
        (((n : ℤ) + 1 ≤ t.g.ord ∧ spdPM' t.g) ∨
          (y₁ = y₂ ∧ g.2.PMBlock ∧ gsPM' t.g ∧
            (H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord))) ∧
    (∀ g ∈ 𝒯.Q, (H.glue x y₁ y₂ g.2.swapSolid).InvB' ∧
      ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧ t.g.DotFree ∧
        (t.g.IsQGraph → spdPM' t.g ∧ t.g.QLabelInMISB) ∧
        ∀ x' : Fin t.nOut, t.g.IsQFormAt (.inr x') → ¬ t.g.IsQGraph →
          ∀ s ∈ 𝔈 D t.nOut x' t.g, s.g.dotExcess = 0 ∧
            ((s.g.LabelFree ∧ gsPM' s.g ∧ (H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ s.g.ord) ∨
            (s.g.IsQGraph ∧ spdPM' s.g ∧ s.g.QLabelInMISB) ∨
            ((D : ℤ) < s.g.ord ∧ s.g.DoublyConnected))) ∧
    (∀ g ∈ 𝒯.Err, ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ t.g.DoublyConnected ∧
        (H.glue x y₁ y₂ (tVar true)).ord + D - 3 ≤ t.g.ord)

/-- **[II, Lemma 6.5]** (1)–(5) in the block reading, with row (4) read on a family of
`Q`-expansions with the clauses `QExpFamilyStmt` (`globalGoodStmtB'`). -/
theorem globalGoodB' : globalGoodStmtB' := by
  intro 𝔈 hF n D Sig 𝒯 m C H x y₁ y₂ hn h𝒯 hL hN hd ho1 ho2 hI hT hgs hnr hM hst hPG
  have hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63 :=
    ⟨h𝒯.1, h𝒯.2.2.2.1, h𝒯.2.2.2.2⟩
  refine ⟨fun g hg => ?_, globalGood_row3 n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2 hI hT
    hgs hnr hM hst, fun g hg => ?_,
    globalGood_row5 glue_oDotT_normal n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2 hI hT hgs
      hnr hM hst⟩
  · rw [List.mem_append, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact globalGood_row1 n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2 hI hT hgs hnr hM hst g
        (List.mem_append.2 (Or.inl hg))
    · exact globalGood_row2 n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2 hI hT hgs hnr hM hst g
        hg
    · exact globalGood_row1 n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2 hI hT hgs hnr hM hst g
        (List.mem_append.2 (Or.inr hg))
  · obtain ⟨hGtI, hrow⟩ := GlobalGoodB_row4 n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2 hI hT
      hgs hnr hM hst hPG g hg
    refine ⟨hGtI, fun t ht => ?_⟩
    obtain ⟨hN', hd', htP, htI, hQ, hout⟩ := hrow t ht
    refine ⟨hN', hd', hQ, fun x' hQF hnQ s hs => ?_⟩
    obtain ⟨C', hC'⟩ := hN'
    exact hout x' (𝔈 D t.nOut x' t.g) hQF hnQ (hF.1 D t.nOut x' t.g ⟨C', hC'⟩ hQF htP).2
      (hF.2.2.2.2.2 D t.nOut x' t.g ⟨C', hC'⟩ hQF htP hnQ htI) s hs

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end RBM8D.Graphs
