module

public import RBM8D.GlobalExp.Termination
public import RBM8D.GlobalExp.GlobalGoodB
public import RBM8D.Graph.QExp.SelRunIso
public import RBM8D.Graph.Local.SolidMono
public import RBM8D.Graph.Local.StrategyPart1
public import RBM8D.Graph.Local.Strategy
public import RBM8D.GlobalExp.Local
public import RBM8D.Graph.Local.DotNorm
public import RBM8D.GlobalExp.SubstSPD
public import RBM8D.GlobalExp.SubstMol
public import RBM8D.GlobalExp.RunClauses
public import RBM8D.GlobalExp.SubstDC
public import RBM8D.GlobalExp.GlobalGoodRows
public import RBM8D.TExp.Second
public import RBM8D.Graph.Local.Weight
import all RBM8D.Graph.Local.SolidMono
import all RBM8D.Graph.Local.StrategyPart1
import all RBM8D.Graph.Local.Strategy
import all RBM8D.GlobalExp.Termination
import all RBM8D.GlobalExp.Local
import all RBM8D.Graph.Local.DotNorm
import all RBM8D.GlobalExp.SubstSPD
import all RBM8D.GlobalExp.SubstMol
import all RBM8D.GlobalExp.RunClauses
import all RBM8D.GlobalExp.SubstDC
import all RBM8D.GlobalExp.GlobalGoodRows
import all RBM8D.TExp.Second
import all RBM8D.GlobalExp.GlobalGoodB
import all RBM8D.Graph.Local.Weight

@[expose] public section

/-!
# [II, Lemma 6.8] in the block reading: the descent of Steps 2–3 and the leaf invariants

The facts on the substitution of Steps 2–3 and on single steps of [II, Strategy 6.6] used for
[II, Lemma 6.8] in the block reading:

* the measure `runMu` of a run decreases from the graph `H.glue x y₁ y₂ (tVar true)` of Step 2 to
  every `O_dot` form without labels of a substituted graph, and to every output without labels of
  a `Q`-expansion of such a form (`substMu`, by [II, Lemma 6.5] (1)–(5));
* a reordering and the duplication of a `×`-dotted edge keep the measure
  (`TerminationB_runMu_reorder`, `TerminationB_runMu_xdotDup`);
* the leaf invariants of a run (`TerminationB_Inv`): plain or of order `> D` in the count of
  [II, (2.5)], the order of the graphs without labels, globally standard below the cutoff and at
  the `⊕/⊖`-recollision graphs, the order when `⊕`, `⊖` lie in one block, and the diffusive edge
  and the label of the graphs without internal atom; they hold on the inputs of the run
  (`TerminationB_inv_h2`), pass along a reordering, the duplication of a `×`-dotted edge and the
  removal of a redundant dotted edge, hold on the `O_dot` forms of the substituted graphs of
  Steps 2–3 and on the outputs of the `Q`-expansions of Step 3, and on the outputs of Step 1
  (`TerminationB_inv_loc`, which also gives the normal regular form, the doubly connected property
  and the clauses `StepOut` of these outputs);
* an output of Step 1 in which `⊕`, `⊖` lie in one dotted block has order at least the order of
  the input plus `2`, hence `≥ 5` ([II, Def 6.3]; `TerminationB_loc_pm`);
* the clause `Graph.RgCheck` from the clause on the external atoms (`TerminationB_rgCheck`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private SolidMono.dotExcess_zero SolidMono.lwN_oDotT from RBM8D.Graph.Local.SolidMono
-- (the names formerly opened from RBM8D.Graph.Local.StrategyPart1 are public)
open private oGGTT_normal from RBM8D.Graph.Local.Strategy
open private Termination_randomFirstInt from RBM8D.GlobalExp.Termination
open private Local_localOp_good from RBM8D.GlobalExp.Local
open private Termination_dup_facts Termination_sameBlock_mem Termination_not_qGraph Termination_inv1
  Termination_paperOrd_le Termination_toMG'_app Termination_anchor_congr
  Termination_flatComp_congr Termination_split from RBM8D.GlobalExp.Termination
open private DotNorm.step DotNorm.Keep DotNorm.Keep.plain DotNorm.Keep.block DotNorm.Keep.sub
  from RBM8D.Graph.Local.DotNorm
open private SubstSPD_swap_of_ns SubstSPD_swap_otimesNoDot SubstSPD_swap_dotExcess
  SubstSPD_swap_labels SubstSPD_swap_noLabDot SubstSPD_swap_pmBlock SubstSPD_swap_tensor
  SubstSPD_swap_sameBlock SubstSPD_tVar_ord SubstSPD_host SubstSPD_liftA_inj
  SubstSPD_liftA_ne_newA SubstSPD_swap_kind from RBM8D.GlobalExp.SubstSPD
open private SubstMol_glueAtom_isRight from RBM8D.GlobalExp.SubstMol
open private Local_molRep_eq_iff Local_molRep_spec Local_molRep_idem Local_anchor_none
  Local_anchor_some Local_rho Local_rho_vtx Local_pin Local_edMap Local_ELG_mapV Local_rdL_vok
  Local_pin_vok Local_RG_same Local_RG_perm Local_RG Local_carry_trans Local_carry_toRG
  Local_carry_ofRG Local_Same Local_Same.refl Local_Carry Local_rd Local_pull_gs Local_flat_block
  Local_flat_unpinned Local_flat_isRight from RBM8D.GlobalExp.Local
open private RunClauses_reorder_iso RunClauses_Iso RunClauses_iso_count RunClauses_iso_paperOrd
  RunClauses_iso_dotExcess RunClauses_iso_sameBlock RunClauses_swapR_eq RunClauses_eA
  RunClauses_eA_inr RunClauses_eA_isLeft RunClauses_SwapR RunClauses_iso_mem RunClauses_iso_mem'
  RunClauses_iso_ord RunClauses_iso_molRep RunClauses_iso_rho RunClauses_iso_unpinned
  RunClauses_molRep_of_block RunClauses_eA_isRight RunClauses_eA_inl RunClauses_iso_sameMol
  RunClauses_eA_inl_iff
  from RBM8D.GlobalExp.RunClauses
open private SubstDC_swap_rgCheck from RBM8D.GlobalExp.SubstDC
open private GlobalGoodRows_rgCheck from RBM8D.GlobalExp.GlobalGoodRows
open private h2Rec_struct from RBM8D.TExp.Second
open private GlobalGoodB_oDot_label GlobalGoodB_glue_label GlobalGoodB_oDot_unl
  GlobalGoodB_glue_unl GlobalGoodB_oDot_sameBlock GlobalGoodB_label_host GlobalGoodB_ord3
  GlobalGoodB_mis_int GlobalGoodB_G_comps GlobalGoodB_dotExcess_nonneg GlobalGoodB_row4
  GlobalGoodB_plain_of GlobalGoodB_oDot_PW GlobalGoodB_glue_PW
  from RBM8D.GlobalExp.GlobalGoodB

/-! ## The measure at a higher order and at fewer solid edges -/

section Mu

variable {k n₀ k' n₁ : ℕ}

/-- A graph of order `≥ ord Γ + 1` in the count of [II, (2.5)] has a smaller `runMu N` than `Γ`
when that order of `Γ` is at most `N`. -/
private theorem TerminationB_mu_ord {N : ℕ} {Γ : Graph k n₀} {Γ' : Graph k' n₁}
    (hle : Γ.paperOrd ≤ N) (h : Γ.paperOrd + 1 ≤ Γ'.paperOrd) : runMu N Γ' < runMu N Γ := by
  unfold runMu
  rw [Prod.Lex.toLex_lt_toLex]
  left
  omega

/-- A graph of the same order in the count of [II, (2.5)], with as many light weights and fewer
solid edges, has a smaller `runMu N`. -/
private theorem TerminationB_mu_solid {N : ℕ} {Γ : Graph k n₀} {Γ' : Graph k' n₁}
    (hp : Γ'.paperOrd = Γ.paperOrd) (hl : Γ'.lwN = Γ.lwN) (hs : Γ'.solidN < Γ.solidN) :
    runMu N Γ' < runMu N Γ := by
  unfold runMu
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨by rw [hp], ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨hl, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl hs

/-- A graph without dotted edges has the scaling order as order in the count of [II, (2.5)]. -/
private theorem TerminationB_paperOrd_of_dotFree {Γ : Graph k n₀} (h : Γ.DotFree) :
    Γ.paperOrd = Γ.ord := by
  unfold Graph.paperOrd
  rw [SolidMono.dotExcess_zero h]
  ring

end Mu

/-! ## Light weights and labels of substituted graphs -/

section Glue

variable {m n' : ℕ}

/-- The light weights of `H.glue x y₁ y₂ g` are those of `H` and those of `g`. -/
private theorem TerminationB_lwN_glue (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n') :
    (H.glue x y₁ y₂ g).lwN = H.lwN + g.lwN := by
  simp [Graph.lwN, Graph.glue, liftCs, List.filter_append, List.filter_map, Function.comp_def,
    Comp.map]

/-- Reversing the solid edges keeps the light weights. -/
private theorem TerminationB_lwN_swap {k n : ℕ} (g : Graph k n) : g.swapSolid.lwN = g.lwN := by
  simp only [Graph.lwN, Graph.swapSolid, List.filter_map, List.length_map, Function.comp_def,
    SubstSPD_swap_kind]

/-- The graph `m Θ^{[o]}_{a b₁} Ḡ_{b₁ b₂}` has no light weight. -/
private theorem TerminationB_lwN_theta (o : List ℕ) : (thetaLabelGraph o).lwN = 0 := by
  simp [Graph.lwN, thetaLabelGraph, mkC, Kind.isLt]

/-- The recollision terms of [II, (4.15)] have no light weight. -/
private theorem TerminationB_lwN_tVarCorr : ∀ g ∈ tVarCorr, g.2.lwN = 0 := by
  decide +kernel

/-- The `t`-variable has no light weight. -/
private theorem TerminationB_lwN_tVar : (tVar true).lwN = 0 := by
  decide +kernel

/-- An `O_dot` form of a graph with a labelled component other than a dotted or `×`-dotted edge
carries a label. -/
private theorem TerminationB_oDotT_label {k n : ℕ} {Γ : Graph k n} {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind ≠ .dot) (hk' : c.kind ≠ .xdot) (hl : c.label ≠ none) :
    ∀ t ∈ oDotT Γ, ¬ t.g.LabelFree := by
  intro t ht hLF
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact hl (hLF c hc)
  · have hs := mergeT_spec hm
    have hcd : c ∈ (Γ.dotChoice Γ.splitPairs A).comps := by
      unfold Graph.dotChoice
      exact List.mem_append_left _ (List.mem_filter.2 ⟨hc, by simp [hk']⟩)
    have key : ∃ c', mergeComp (Γ.dotChoice Γ.splitPairs A).mrep t.f c = some c' ∧
        c'.label = c.label.map (Prod.map id t.f) := by
      have h1 : (c.kind == .dot && t.f c.x == t.f c.y) = false := by simp [hk]
      simp only [mergeComp, h1, Bool.false_eq_true, ↓reduceIte]
      split
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    obtain ⟨c', hc', hl'⟩ := key
    have hmem : c' ∈ t.g.comps := by
      rw [hs.comps_eq]
      exact List.mem_filterMap.2 ⟨c, hcd, hc'⟩
    have h0 := hLF c' hmem
    rw [hl'] at h0
    exact hl (Option.map_eq_none_iff.1 h0)

end Glue

/-! ## The atom `y₁ = y₂` of the `t`-variable -/

section YFree

variable {m : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}

/-- **At `y₁ = y₂` only waved edges `s` and `×`-dotted edges of `H` are at `y₁`**
([II, Strategy 6.6, Steps 1–2]): the atom `y₁ = y₂` lies in the minimal isolated subset of
`G = H.glue x y₁ y₂ (tVar true)`, which is locally standard, so it is standard neutral; it already
carries the two solid edges `G_{y₁α}` and `Ḡ_{y₂α}`, and its third component other than a
`×`-dotted edge is a waved edge `s`. -/
private theorem TerminationB_y_free (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hx : x.isRight = true) (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB')
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (hM : (H.glue x y₁ y₂ (tVar true)).MISLocStdB) (hy : y₁ = y₂) {c : Comp (Atom 3 m)}
    (hc : c ∈ H.comps) (hat : c.x = y₁ ∨ c.y = y₁) (hk : c.kind ≠ .xdot) :
    c.kind = .waved .s := by
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
  have hαY : (newA 0 : Atom 3 (m + 1)) ≠ Y := fun h => SubstSPD_liftA_ne_newA _ _ h.symm
  set X : Atom 3 (m + 1) := liftA 1 x with hX
  set LH := (H.comps.map (Comp.map (liftA 1))).filter
    (fun c => c.kind != .xdot && (c.x == Y || c.y == Y)) with hLH
  have hcomps := GlobalGoodB_G_comps H x (.inr a) (.inr a)
  have hdeg : G.deg Y = (H.comps.map (Comp.map (liftA 1))).countP
      (fun c => c.kind.isSolid && (c.x == Y || c.y == Y)) + 2 := by
    unfold Graph.deg
    rw [← List.countP_eq_length_filter, hcomps, List.countP_append]
    congr 1
    simp [mkC, Kind.isSolid, ← hY]
  have hstd : G.stdNeutralAt Y = true := by
    rcases hloc.2 with h | ⟨-, h⟩
    · omega
    · exact h
  unfold Graph.stdNeutralAt at hstd
  simp only [Bool.and_eq_true, beq_iff_eq] at hstd
  obtain ⟨⟨⟨h1, -⟩, h3⟩, -⟩ := hstd
  rw [hcomps, List.filter_append] at h1 h3
  rw [List.filter_append, List.length_append] at h3
  rw [List.length_append] at h1
  change LH.length + _ = 3 at h1
  change (LH.filter fun c => c.kind == .waved .s).length + _ = 1 at h3
  have hmem : c.map (liftA 1) ∈ LH := by
    refine List.mem_filter.2 ⟨List.mem_map.2 ⟨c, hc, rfl⟩, ?_⟩
    rcases hat with h | h <;> simp [Comp.map, hk, h, hY]
  by_contra hne
  have hlt : (LH.filter fun c => c.kind == .waved .s).length < LH.length :=
    List.length_filter_lt_length_iff_exists.2 ⟨_, hmem, by simpa [Comp.map] using hne⟩
  by_cases hxY : X = Y
  · simp [mkC, ← hX, ← hY, hxY] at h1
    rw [h1] at hmem
    exact List.not_mem_nil hmem
  · simp [mkC, ← hX, ← hY, hxY, hαY] at h1 h3
    omega

end YFree

/-! ## The descent of Steps 2–3 -/

section Subst

variable {n D : ℕ} {𝒯 : TRec} {m C : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}

/-- **Row (2) of [II, Lemma 6.5] by the order**: under the hypotheses of [II, Lemma 6.5], every
`O_dot` form `t` of the substitution of a graph `g` of `R` has no dotted edge and scaling order
`≥ ord G + 1`, since `g` has scaling order `≥ 3`, and `≥ 5` when `⊕`, `⊖` lie in one block of
`g`. -/
private theorem TerminationB_rowR (hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63)
    (hL : H.LabelFree) (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hd : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    {g : Σ n, Graph 3 n} (hg : g ∈ 𝒯.R) {t : Tracked 3 (m + g.1)}
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) :
    t.g.DotFree ∧ (H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord := by
  obtain ⟨_, hSh, hDef⟩ := hcore
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hall : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
  obtain ⟨⟨C', hgN⟩, -, -, -⟩ := hSh.1.1 g (by simp [hg])
  obtain ⟨-, hRec, hk3, -⟩ := hSh.2.1 g hg
  obtain ⟨hT, hX, hNL, hlab⟩ := hDef.2.1 g hall
  have h5 := hDef.2.2.2.1 g (by simp [hg])
  have hRg : g.2.swapSolid.RgCheck := by
    obtain ⟨c, hc, hk, hb⟩ := hRec
    refine Or.inr ⟨c, List.mem_map.2 ⟨c, hc, SubstSPD_swap_of_ns (by rw [hk]; rfl)⟩,
      Or.inl (by rw [hk]; rfl), ?_⟩
    rcases hb with ⟨⟨b, -, hx'⟩, hy'⟩ | ⟨⟨b, -, hy'⟩, hx'⟩
    · exact Or.inr ⟨by rw [hx']; rfl, hy'⟩
    · exact Or.inl ⟨hx', by rw [hy']; rfl⟩
  obtain ⟨-, hd', hε, hε', -⟩ := glue_oDotT_normal m g.1 C C' H x y₁ y₂ g.2.swapSolid hx hy₁ hy₂
    hL hN hd (Graph.swapSolid_Normal hgN) (SubstSPD_swap_otimesNoDot hT)
    (by rw [SubstSPD_swap_dotExcess]; exact hX) hRg (by rw [SubstSPD_swap_labels]; exact hlab)
    (SubstSPD_swap_noLabDot hNL) t ht
  refine ⟨hd', ?_⟩
  have e1 := glue_ord 3 m g.1 H x y₁ y₂ g.2.swapSolid
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  have e3 : g.2.swapSolid.ord = g.2.ord := (swapSolid_basic 3 g.1 g.2).2.1
  rw [SubstSPD_tVar_ord] at e2
  have hk3' : (3 : ℤ) ≤ g.2.ord := hk3
  by_cases hε0 : y₁ = y₂ ∧ g.2.swapSolid.PMBlock
  · have := hε hε0
    have h5' := h5 ((SubstSPD_swap_pmBlock g.2).1 hε0.2)
    omega
  · have := hε' hε0
    omega

/-- **Row (4) of [II, Lemma 6.5] by the order, for every `Q`-expansion with the clause
`qexpClauseB`**: under the hypotheses of [II, Lemma 6.5], for a graph `g` of `Q`, an `O_dot`
form `t` of `G̃ = H.glue x y₁ y₂ g.swapSolid` and a `Q`-expansion `E` of `t` at its label atom
with the clause `qexpClauseB`, every output graph without labels has dot excess `0` and scaling
order `≥ ord G + 1`. If no weight or solid edge without label is attached to the block of the
label atom of `t`, [II, Lemma 4.15 (iv)] raises the scaling order of `t`; otherwise the label atom
of `g` lies in the block of `⊕` or of `⊖`, so `g` has scaling order `≥ 3`, and `y₁ ≠ y₂` because at
`y₁ = y₂` no weight or solid edge of `H` is at `y₁` (`TerminationB_y_free`). -/
private theorem TerminationB_rowQ (hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63)
    (hL : H.LabelFree) (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hd : (H.glue x y₁ y₂ (tVar true)).DotFree) (ho2 : (H.glue x y₁ y₂ (tVar true)).ord ≤ n)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hM : (H.glue x y₁ y₂ (tVar true)).MISLocStdB)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    {g : Σ n, Graph 3 n} (hg : g ∈ 𝒯.Q) {t : Tracked 3 (m + g.1)}
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) {x' : Fin t.nOut}
    {E : TExpansion 3 t.nOut} (hQF : t.g.IsQFormAt (.inr x')) (hqe : qexpClauseB D x' t.g E)
    {s : Tracked 3 t.nOut} (hs : s ∈ E) (hsL : s.g.LabelFree) :
    s.g.dotExcess = 0 ∧ (H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ s.g.ord := by
  obtain ⟨hnD, hSh, hDef⟩ := hcore
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  obtain ⟨n', g₀⟩ := g
  have hallQ : (⟨n', g₀⟩ : Σ n, Graph 3 n) ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by simp [hg]
  have hall : (⟨n', g₀⟩ : Σ n, Graph 3 n) ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
  obtain ⟨⟨C', hgN⟩, hTK, hAE, -⟩ := hSh.1.1 _ hallQ
  obtain ⟨-, hk2⟩ := hSh.2.2.2.1 _ hg
  obtain ⟨-, hQL, hcase⟩ := hDef.1.2.2 _ hg
  obtain ⟨hgT, hX, hNL, hlab⟩ := hDef.2.1 _ hall
  have hPM4 := hDef.2.2.2.2.1 _ hg
  have hRg : g₀.RgCheck := hDef.2.2.2.2.2.1 ⟨n', g₀⟩ (by simp [hg])
  have hgPl : g₀.Plain := TRec.plain_of_def63 hDef _ hallQ
  set G := H.glue x y₁ y₂ (tVar true) with hG
  set Gt := H.glue x y₁ y₂ g₀.swapSolid with hGt
  set γ : Atom 3 n' → Atom 3 (m + n') := glueAtom x y₁ y₂ with hγ
  have hGtord : Gt.ord = G.ord - 2 + g₀.ord := by
    have e1 : Gt.ord = H.ord + g₀.swapSolid.ord := glue_ord 3 m n' H x y₁ y₂ g₀.swapSolid
    have e2 : G.ord = H.ord + (tVar true).ord := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
    have e3 : g₀.swapSolid.ord = g₀.ord := (swapSolid_basic 3 n' g₀).2.1
    rw [e1, e2, e3, SubstSPD_tVar_ord]
    ring
  obtain ⟨-, hd', hε, hε', -⟩ := glue_oDotT_normal m n' C C' H x y₁ y₂ g₀.swapSolid hx hy₁
    hy₂ hL hN hd (Graph.swapSolid_Normal hgN) (SubstSPD_swap_otimesNoDot hgT)
    (by rw [SubstSPD_swap_dotExcess]; exact hX) (SubstDC_swap_rgCheck hRg)
    (by rw [SubstSPD_swap_labels]; exact hlab) (SubstSPD_swap_noLabDot hNL) t ht
  -- the label of `t`
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
    obtain ⟨cH, hcH, rfl⟩ := GlobalGoodB_glue_unl (hSh.2.2.2.1 _ hg).1 hc hcl hcr
    obtain ⟨v, hv, rfl⟩ := hends u' hu'
    have hr' : cH.kind.isRandom = true := by simpa [Comp.map] using hcr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Comp.map] at hv
    rcases hv with rfl | rfl
    · exact ⟨cH.x, ⟨cH, hcH, hr', by simp⟩, rfl⟩
    · exact ⟨cH.y, ⟨cH, hcH, hr', by simp⟩, rfl⟩
  obtain ⟨⟨C'', hout⟩, -⟩ := hqe
  obtain ⟨⟨hQB, -, -, hiv⟩, -⟩ := hout s hs
  obtain ⟨-, hordle, -, hdex, -, -, -⟩ := hQB
  -- the label atom `x'`
  obtain ⟨c₁, hc₁, hl₁⟩ := hQF.1
  obtain ⟨cg, hcg, ug, hclg, hxg⟩ := hloc c₁ hc₁ .Q _ hl₁
  have hdex0 : s.g.dotExcess = 0 :=
    le_antisymm (hdex.trans (SolidMono.dotExcess_zero hd').le) (GlobalGoodB_dotExcess_nonneg _)
  refine ⟨hdex0, ?_⟩
  have hnD' : (n : ℤ) ≤ D := by omega
  by_cases hD' : (D : ℤ) < s.g.ord
  · omega
  push Not at hD'
  have hk2' : (2 : ℤ) ≤ g₀.ord := hk2
  by_cases hfree : t.g.UnlabelledFreeAtBlock (.inr x')
  · have h1 := (hiv hfree hsL hD').1
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
      have hxd : cH.kind ≠ .xdot := by
        intro h; rw [h] at hcHr; cases hcHr
      have hns : cH.kind ≠ .waved .s := by
        intro h; rw [h] at hcHr; cases hcHr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwH
      have hat : cH.x = y₁ ∨ cH.y = y₁ := by
        rcases hwy with rfl | rfl <;> rcases hwH with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
        · exact Or.inl (h.symm.trans hy.symm)
        · exact Or.inr (h.symm.trans hy.symm)
      exact hns (TerminationB_y_free hd hx hy₁ hy₂ hI hst hM hy hcH hat hxd)
    have h3 : t.g.ord = Gt.ord := hε' fun h => hyne h.1
    omega

/-- The leading term, the terms of `Σ_T` and the recollision terms of [II, (4.15)] have no light
weight. -/
private theorem TerminationB_lwN_row1 (N : ℕ) :
    ∀ g ∈ leadExp ++ sigmaTExp N ++ tVarCorr, g.2.lwN = 0 := by
  intro g hg
  simp only [List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · simp only [leadExp, List.mem_singleton] at hg
    subst hg
    exact TerminationB_lwN_theta []
  · obtain ⟨o, -, rfl⟩ := List.mem_map.1 hg
    exact TerminationB_lwN_theta o
  · exact TerminationB_lwN_tVarCorr g hg

/-- **The descent of Steps 2–3** ([II, Lemma 6.8], by [II, Lemma 6.5] (1)–(5)): the statement
`substMuStmt` with the hypotheses on `𝒯` of [II, Def 3.2] at order `n - 1` and of [II, Def 6.3] in
place of `TRec.IsTExpStruct`. Every `O_dot` form `t` without labels of a substituted graph has no
dotted edge, so its order in the count of [II, (2.5)] is its scaling order. The leading term, the
terms of `Σ_T`, `R` and the recollision terms give scaling order `≥ o + 1`, or at `y₁ = y₂` the
order `o` with the light weights of `G` and fewer solid edges; `A` gives scaling order `≥ n + 1` or
`≥ o + 1`; the `O_dot` forms of a substituted `Q`-graph carry the image of its label; `Err` gives
scaling order `≥ o + D - 3 > D ≥ n`; and the outputs without labels of a `Q`-expansion have dot
excess `0` and scaling order `≥ o + 1`. Here `o = ord G ≤ n` is the scaling order of
`G = H.glue x y₁ y₂ (tVar true)`. -/
private theorem TerminationB_substMu_core (n D : ℕ) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m)
    (x y₁ y₂ : Atom 3 m) (hn : 3 ≤ n)
    (hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) (hL : H.LabelFree)
    (hN : (H.glue x y₁ y₂ (tVar true)).Normal C) (hd : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (ho1 : 4 ≤ (H.glue x y₁ y₂ (tVar true)).ord) (ho2 : (H.glue x y₁ y₂ (tVar true)).ord ≤ n)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hT : (H.glue x y₁ y₂ (tVar true)).TensorDiffusive)
    (hgs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hnr : ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2})
    (hM : (H.glue x y₁ y₂ (tVar true)).MISLocStdB)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) :
    (∀ g ∈ 𝒯.tSubst (n - 1), ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), t.g.LabelFree →
      runMu n t.g < runMu n (H.glue x y₁ y₂ (tVar true))) ∧
    (∀ g ∈ 𝒯.Q, ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid),
      ∀ (x' : Fin t.nOut) (E : TExpansion 3 t.nOut), t.g.IsQFormAt (.inr x') →
        ¬ t.g.IsQGraph → qexpClauseB D x' t.g E → ∀ s ∈ E, s.g.LabelFree →
          runMu n s.g < runMu n (H.glue x y₁ y₂ (tVar true))) := by
  obtain ⟨hnD, hSh, hDef⟩ := hcore
  set G := H.glue x y₁ y₂ (tVar true) with hG
  have hGp : G.paperOrd = G.ord := TerminationB_paperOrd_of_dotFree hd
  have hle : G.paperOrd ≤ n := by rw [hGp]; exact ho2
  have key : ∀ {n₁ : ℕ} (Γ' : Graph 3 n₁), Γ'.dotExcess = 0 → G.ord + 1 ≤ Γ'.ord →
      runMu n Γ' < runMu n G := by
    intro n₁ Γ' h0 h1
    refine TerminationB_mu_ord hle ?_
    rw [hGp]
    unfold Graph.paperOrd
    rw [h0]
    omega
  have keyD : ∀ {n₁ : ℕ} (Γ' : Graph 3 n₁), Γ'.DotFree → G.ord + 1 ≤ Γ'.ord →
      runMu n Γ' < runMu n G := fun Γ' h0 h1 => key Γ' (SolidMono.dotExcess_zero h0) h1
  have hnD' : (n : ℤ) ≤ D := by omega
  refine ⟨fun g hg t ht htL => ?_, fun g hg t ht x' E hQF _ hqe s hs hsL => ?_⟩
  · have hrow1 : g ∈ leadExp ++ sigmaTExp (n - 1) ++ tVarCorr →
        runMu n t.g < runMu n G := by
      intro hg1
      obtain ⟨-, hd', -, -, hor⟩ := globalGood_row1 n D 𝒯 m C H x y₁ y₂ hn ⟨hnD, hSh, hDef⟩ hL
        hN hd ho1 ho2 hI hT hgs hnr hM hst g hg1 t ht
      rcases hor with h | ⟨-, heq, hsol⟩
      · exact keyD t.g hd' h
      · refine TerminationB_mu_solid ?_ ?_ hsol
        · rw [TerminationB_paperOrd_of_dotFree hd', hGp, heq]
        · rw [SolidMono.lwN_oDotT ht, TerminationB_lwN_glue, TerminationB_lwN_glue,
            TerminationB_lwN_swap, TerminationB_lwN_row1 _ g hg1, TerminationB_lwN_tVar]
    simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg
    rcases hg with (((((hg | hg) | hg) | hg) | hg) | hg) | hg
    · exact hrow1 (by simp [hg])
    · exact hrow1 (by simp [hg])
    · -- `R`
      obtain ⟨hd', h⟩ := TerminationB_rowR ⟨hnD, hSh, hDef⟩ hL hN hd hst hg ht
      exact keyD t.g hd' h
    · -- `A`
      obtain ⟨-, hd', -, h⟩ := globalGood_row3 n D 𝒯 m C H x y₁ y₂ hn ⟨hnD, hSh, hDef⟩ hL hN hd
        ho1 ho2 hI hT hgs hnr hM hst g hg t ht
      refine keyD t.g hd' ?_
      rcases h with ⟨h, -⟩ | ⟨-, -, -, h⟩
      · omega
      · exact h
    · -- `Q`: the `O_dot` forms carry the image of the label of `g`
      exfalso
      have hall : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
      obtain ⟨u, ⟨c, hc, hl⟩, -⟩ := (hSh.2.2.2.1 g hg).1
      obtain ⟨-, -, hNL, -⟩ := hDef.2.1 g hall
      have hk : c.kind ≠ .dot := fun h => by rw [hNL c hc (Or.inl h)] at hl; cases hl
      have hk' : c.kind ≠ .xdot := fun h => by rw [hNL c hc (Or.inr h)] at hl; cases hl
      have hmem : c.swapSolid.map (glueAtom x y₁ y₂) ∈ (H.glue x y₁ y₂ g.2.swapSolid).comps :=
        List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, rfl⟩)
      have hlab : (c.swapSolid.map (glueAtom x y₁ y₂)).label ≠ none := by
        have : c.swapSolid.label = c.label := by unfold Comp.swapSolid; split <;> rfl
        simp [Comp.map, this, hl]
      have hkind : (c.swapSolid.map (glueAtom x y₁ y₂)).kind = c.kind := by
        simp [Comp.map, SubstSPD_swap_kind]
      exact TerminationB_oDotT_label hmem (by rw [hkind]; exact hk) (by rw [hkind]; exact hk')
        hlab t ht htL
    · -- `Err`
      obtain ⟨-, hd', -, h⟩ := globalGood_row5 glue_oDotT_normal n D 𝒯 m C H x y₁ y₂ hn
        ⟨hnD, hSh, hDef⟩ hL hN hd ho1 ho2 hI hT hgs hnr hM hst g hg t ht
      refine keyD t.g hd' ?_
      have e : (H.glue x y₁ y₂ (tVar true)).ord = G.ord := rfl
      have e' : (4 : ℤ) ≤ G.ord := ho1
      omega
    · exact hrow1 (by simp [hg])
  · obtain ⟨h0, h1⟩ := TerminationB_rowQ ⟨hnD, hSh, hDef⟩ hL hN hd ho2 hI hM hst hg ht hQF hqe
      hs hsL
    exact key s.g h0 h1

/-- **The descent of Steps 2–3**: the statement `substMuStmt`, from the hypotheses on `𝒯` of
[II, Def 3.2] at order `n - 1` and of [II, Def 6.3] that `TRec.IsTExpStruct` contains. -/
theorem substMu : substMuStmt := by
  intro n D Sig 𝒯 m C H x y₁ y₂ hn h𝒯
  exact TerminationB_substMu_core n D 𝒯 m C H x y₁ y₂ hn ⟨h𝒯.1, h𝒯.2.2.2.1, h𝒯.2.2.2.2⟩

end Subst

/-! ## The measure under a reordering and under the duplication of a `×`-dotted edge -/

section MuInv

/-- The clause of `Graph.stdNeutralAt` on the ends of the two solid edges at an atom. -/
private def TerminationB_endsOK : List (Bool × Charge) → Bool
  | [e₁, e₂] => matchedEnds e₁ e₂ && e₁.2 != e₂.2
  | _ => false

private theorem TerminationB_endsOK_perm {l l' : List (Bool × Charge)} (h : l.Perm l') :
    TerminationB_endsOK l = TerminationB_endsOK l' := by
  rcases l with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, l⟩⟩⟩
  · rw [List.nil_perm.1 h]
  · rw [List.perm_singleton.1 h.symm]
  · rcases List.pair_perm.1 h with rfl | rfl
    · rfl
    · simp only [TerminationB_endsOK, matchedEnds]
      cases e₁.1 <;> cases e₂.1 <;> cases e₁.2 <;> cases e₂.2 <;> rfl
  · have hl := h.length_eq
    rcases l' with _ | ⟨f₁, _ | ⟨f₂, _ | ⟨f₃, l'⟩⟩⟩
    all_goals first | rfl | simp at hl

private theorem TerminationB_stdNeutralAt_eq {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Γ.stdNeutralAt u =
      (((Γ.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u)).length == 3) &&
        (((Γ.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u)).filter
          fun c => c.kind.isSolid).length == 2) &&
        (((Γ.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u)).filter
          fun c => c.kind == .waved .s).length == 1) &&
        TerminationB_endsOK (Γ.ends u)) := by
  unfold Graph.stdNeutralAt
  rcases Γ.ends u with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, l⟩⟩⟩ <;> rfl

/-- Two lists related entrywise by a relation that a partial map does not see have the same
image under the partial map. -/
private theorem TerminationB_f2_filterMap {α β : Type*} {R : α → α → Prop} (F : α → Option β)
    (hF : ∀ a a', R a a' → F a' = F a) {l l' : List α} (h : List.Forall₂ R l l') :
    l'.filterMap F = l.filterMap F := by
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    rw [List.filterMap_cons, List.filterMap_cons, ih, hF _ _ hr]

section Reorder

variable {n : ℕ} {π : Equiv.Perm (Fin n)} {Γ Γ' : Graph 3 n}

/-- The number of components with a property of the kind is kept by a reordering. -/
private theorem TerminationB_iso_kind (h : RunClauses_Iso π Γ Γ') (q : Kind → Bool) :
    (Γ'.comps.filter fun c => q c.kind).length = (Γ.comps.filter fun c => q c.kind).length := by
  rw [RunClauses_iso_count h _ (fun c c' hr => by rw [(RunClauses_swapR_eq hr).1])]
  rfl

private theorem TerminationB_eA_beq (a b : Atom 3 n) :
    (RunClauses_eA π a == RunClauses_eA π b) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, (RunClauses_eA π).injective.eq_iff]

/-- The degree is read at the image of the atom after a reordering. -/
private theorem TerminationB_iso_deg (h : RunClauses_Iso π Γ Γ') (u : Atom 3 n) :
    Γ'.deg (RunClauses_eA π u) = Γ.deg u := by
  unfold Graph.deg
  rw [RunClauses_iso_count h]
  · congr 1
    refine List.filter_congr fun c _ => ?_
    simp only [Function.comp_apply, Comp.map, TerminationB_eA_beq]
  · intro c c' hr
    obtain ⟨hk, -, -, hxy, -⟩ := RunClauses_swapR_eq hr
    rw [hk]
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    simp only [Bool.or_comm]

/-- The components other than `×`-dotted edges at an atom, counted with a property of the kind,
are read at the image of the atom after a reordering. -/
private theorem TerminationB_iso_at (h : RunClauses_Iso π Γ Γ') (q : Kind → Bool) (u : Atom 3 n) :
    (Γ'.comps.filter fun c => q c.kind && (c.kind != .xdot && (c.x == RunClauses_eA π u ||
      c.y == RunClauses_eA π u))).length =
    (Γ.comps.filter fun c => q c.kind && (c.kind != .xdot && (c.x == u || c.y == u))).length := by
  rw [RunClauses_iso_count h]
  · congr 1
    refine List.filter_congr fun c _ => ?_
    simp only [Function.comp_apply, Comp.map, TerminationB_eA_beq]
  · intro c c' hr
    obtain ⟨hk, -, -, hxy, -⟩ := RunClauses_swapR_eq hr
    rw [hk]
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    simp only [Bool.or_comm]

/-- The ends of the solid edges at an atom are read at its image after a reordering, up to
order. -/
private theorem TerminationB_iso_ends (h : RunClauses_Iso π Γ Γ') (u : Atom 3 n) :
    (Γ'.ends (RunClauses_eA π u)).Perm (Γ.ends u) := by
  obtain ⟨-, cs, h1, h2⟩ := h
  unfold Graph.ends
  have e1 := (h2.filterMap (fun c : Comp (Atom 3 n) =>
    match c.kind with
    | .G ch => if c.x = RunClauses_eA π u ∧ c.y ≠ RunClauses_eA π u then some (true, ch)
        else if c.y = RunClauses_eA π u ∧ c.x ≠ RunClauses_eA π u then some (false, ch) else none
    | _ => none)).symm
  refine e1.trans (List.Perm.of_eq ?_)
  rw [TerminationB_f2_filterMap _ ?_ h1, List.filterMap_map]
  · congr 1
    funext c
    simp only [Function.comp_apply, Comp.map, (RunClauses_eA π).injective.eq_iff,
      (RunClauses_eA π).injective.ne_iff]
    split <;> (try split_ifs) <;> simp_all
  · intro c c' hr
    obtain ⟨hk, -, -, -, hr'⟩ := RunClauses_swapR_eq hr
    cases hc : c.kind with
    | G ch => rw [hr' (by simp [hc, Kind.isRandom]), hc]
    | _ => simp only [hk, hc]

/-- Standard neutrality is read at the image of the atom after a reordering. -/
private theorem TerminationB_iso_std (h : RunClauses_Iso π Γ Γ') (u : Atom 3 n) :
    Γ'.stdNeutralAt (RunClauses_eA π u) = Γ.stdNeutralAt u := by
  rw [TerminationB_stdNeutralAt_eq, TerminationB_stdNeutralAt_eq, List.filter_filter,
    List.filter_filter, List.filter_filter, List.filter_filter,
    TerminationB_endsOK_perm (TerminationB_iso_ends h u)]
  have h1 := TerminationB_iso_at h (fun _ => true) u
  simp only [Bool.true_and] at h1
  rw [h1, TerminationB_iso_at h Kind.isSolid u, TerminationB_iso_at h (· == .waved .s) u]

/-- **A reordering keeps the measure of a run**: the statement `runMu N Γ' = runMu N Γ` for
`Γ.Reorder Γ'` (`Graph.Reorder`). The order in the count of [II, (2.5)] and the dot excess are
kept; the light weights, solid edges and regular weights are counted by kind; the solid edges at
external atoms, the degrees and standard neutrality are read on the renumbered atoms, since a
reordering exchanges the atoms only of waved edges `s`, dotted and `×`-dotted edges and renumbers
only internal atoms; the blocks are carried by the renumbering. -/
theorem TerminationB_runMu_reorder (N : ℕ) {n : ℕ} {Γ Γ' : Graph 3 n} (h : Γ.Reorder Γ') :
    runMu N Γ' = runMu N Γ := by
  obtain ⟨π, hi⟩ := RunClauses_reorder_iso h
  have hp := RunClauses_iso_paperOrd hi
  have he := RunClauses_iso_dotExcess hi
  have hlw : Γ'.lwN = Γ.lwN := TerminationB_iso_kind hi Kind.isLt
  have hsol : Γ'.solidN = Γ.solidN := TerminationB_iso_kind hi Kind.isSolid
  have hrw : Γ'.rwN = Γ.rwN := TerminationB_iso_kind hi Kind.isRg
  have hext : Γ'.eextN = Γ.eextN := by
    unfold Graph.eextN
    rw [RunClauses_iso_count hi]
    · congr 1
      refine List.filter_congr fun c _ => ?_
      simp only [Function.comp_apply, Comp.map, RunClauses_eA_isLeft]
    · intro c c' hr
      obtain ⟨hk, -, -, hxy, -⟩ := RunClauses_swapR_eq hr
      rw [hk]
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      simp only [Bool.or_comm]
  have hdeg : ∀ i, Γ'.deg (.inr (π i)) = Γ.deg (.inr i) := fun i => by
    rw [← RunClauses_eA_inr]; exact TerminationB_iso_deg hi _
  have hstd : ∀ i, Γ'.stdNeutralAt (.inr (π i)) = Γ.stdNeutralAt (.inr i) := fun i => by
    rw [← RunClauses_eA_inr]; exact TerminationB_iso_std hi _
  have hdegX : Γ'.degX = Γ.degX := by
    unfold Graph.degX
    rw [← Equiv.sum_comp π]
    simp only [hdeg]
  have hbad : Γ'.badN = Γ.badN := by
    unfold Graph.badN
    refine Finset.card_bij (fun j _ => π.symm j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have e := π.apply_symm_apply j
      rw [← e, hdeg, hstd] at hj
      exact hj
    · intro a _ b _ hab
      exact π.symm.injective hab
    · intro i hi'
      refine ⟨π i, ?_, π.symm_apply_apply i⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
      rw [hdeg, hstd]
      exact hi'
  have hsep : Γ'.SepInt ↔ Γ.SepInt := by
    have hsb : ∀ a b, Γ'.SameBlock (.inr (π a)) (.inr (π b)) ↔ Γ.SameBlock (.inr a) (.inr b) :=
      fun a b => by
        rw [← RunClauses_eA_inr, ← RunClauses_eA_inr]; exact RunClauses_iso_sameBlock hi _ _
    constructor
    · intro hs a b hab
      exact π.injective (hs _ _ ((hsb a b).2 hab))
    · intro hs i j hij
      have e1 := π.apply_symm_apply i
      have e2 := π.apply_symm_apply j
      rw [← e1, ← e2] at hij ⊢
      rw [hs _ _ ((hsb _ _).1 hij)]
  have hmfl : Γ'.mfl = Γ.mfl := by
    unfold Graph.mfl
    by_cases hs : Γ.SepInt
    · rw [ite_eq_left hs, ite_eq_left (hsep.2 hs)]
    · rw [ite_eq_right hs, ite_eq_right (fun h' => hs (hsep.1 h'))]
  unfold runMu Graph.phi
  rw [hp, hlw, hsol, hmfl, hext, hdegX, hbad, hrw, he]

end Reorder

section Dup

variable {k n : ℕ}

/-- A filter that rejects the appended component sees the same list. -/
private theorem TerminationB_filter_app (p : Comp (Atom k n) → Bool) (L : List (Comp (Atom k n)))
    {c : Comp (Atom k n)} (h : p c = false) :
    ((L ++ [c]).filter p).length = (L.filter p).length := by
  simp [List.filter_append, h]

/-- **The duplication of a `×`-dotted edge keeps the measure of a run** (the step `xdotDup`): a
`×`-dotted edge enters neither the scaling order, nor the dot excess, the blocks, the weights,
the solid edges and the degrees, nor standard neutrality. -/
theorem TerminationB_runMu_xdotDup (N : ℕ) (Γ : Graph k n) (i : Fin Γ.comps.length)
    (hk : Γ.comps[i].kind = .xdot) :
    runMu N (⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩ : Graph k n) = runMu N Γ := by
  set c := Γ.comps[i] with hc
  set Γ' : Graph k n := ⟨Γ.comps ++ [c], Γ.coeff⟩ with hΓ'
  obtain ⟨hmem, -, hord, hex, -⟩ := Termination_dup_facts (g := Γ) (g' := Γ') (List.Perm.refl _)
    (List.getElem_mem _) hk
  have hf : ∀ p : Comp (Atom k n) → Bool, p c = false →
      (Γ'.comps.filter p).length = (Γ.comps.filter p).length :=
    fun p hp => TerminationB_filter_app p Γ.comps hp
  have hp : Γ'.paperOrd = Γ.paperOrd := by unfold Graph.paperOrd; rw [hord, hex]
  have hlw : Γ'.lwN = Γ.lwN := hf _ (by simp [hk, Kind.isLt])
  have hsol : Γ'.solidN = Γ.solidN := hf _ (by simp [hk, Kind.isSolid])
  have hrw : Γ'.rwN = Γ.rwN := hf _ (by simp [hk, Kind.isRg])
  have hext : Γ'.eextN = Γ.eextN := hf _ (by simp [hk, Kind.isSolid])
  have hdeg : ∀ u, Γ'.deg u = Γ.deg u := fun u => hf _ (by simp [hk, Kind.isSolid])
  have hends : ∀ u, Γ'.ends u = Γ.ends u := fun u => by
    simp [Graph.ends, hΓ', List.filterMap_append, hk]
  have hstd : ∀ u, Γ'.stdNeutralAt u = Γ.stdNeutralAt u := fun u => by
    rw [TerminationB_stdNeutralAt_eq, TerminationB_stdNeutralAt_eq, hends,
      List.filter_filter, List.filter_filter, List.filter_filter, List.filter_filter,
      hf _ (by simp [hk]), hf _ (by simp [hk]), hf _ (by simp [hk])]
  have hdegX : Γ'.degX = Γ.degX := by unfold Graph.degX; simp only [hdeg]
  have hbad : Γ'.badN = Γ.badN := by unfold Graph.badN; simp only [hdeg, hstd]
  have hmfl : Γ'.mfl = Γ.mfl := by
    have hsep : Γ'.SepInt ↔ Γ.SepInt := by
      unfold Graph.SepInt
      simp only [Termination_sameBlock_mem hmem]
    unfold Graph.mfl
    by_cases hs : Γ.SepInt
    · rw [ite_eq_left hs, ite_eq_left (hsep.2 hs)]
    · rw [ite_eq_right hs, ite_eq_right (fun h' => hs (hsep.1 h'))]
  unfold runMu Graph.phi
  rw [hp, hlw, hsol, hmfl, hext, hdegX, hbad, hrw, hex]

/-- **The removal of one of two parallel `×`-dotted edges keeps the measure of a run** (the step
`xdotDrop`): the graph is a reordering of the graph with the edge listed once more, which has the
same measure by `TerminationB_runMu_xdotDup`. -/
theorem TerminationB_runMu_xdotDrop (N : ℕ) (Γ : Graph 3 n) (i j : Fin Γ.comps.length)
    (hij : i ≠ j)
    (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) :
    runMu N (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 n) = runMu N Γ := by
  set Γ' : Graph 3 n := ⟨Γ.comps.eraseIdx j, Γ.coeff⟩ with hΓ'
  have hmem : Γ.comps[i] ∈ Γ'.comps :=
    List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, fun h => hij (Fin.ext h), rfl⟩
  obtain ⟨i', h', hi'⟩ := List.mem_iff_getElem.1 hmem
  have h1 := TerminationB_runMu_xdotDup N Γ' ⟨i', h'⟩
    (by simp only [Fin.getElem_fin, hi']; exact hk)
  simp only [Fin.getElem_fin, hi'] at h1
  rw [← TerminationB_runMu_reorder N (Strategy_reorder_xdotDrop Γ i j hc hk)]
  exact h1.symm

end Dup

end MuInv

/-! ## The leaf invariants of a run -/

/-- **The leaf invariants of a run** of [II, Strategy 6.6] at the cutoff order `n` and error
order `D` read by [II, Lemma 6.8] beyond `Graph.InvRun` (the run invariant of [II, Lemma 6.8],
[II, Def 6.3]), all orders in the count of [II, (2.5)]: the graph is plain or of order `> D`;
without labels it has order `≥ 3`, it is globally standard (`gsPM'`) if its order is `≤ n`, and
also if it is a `⊕/⊖`-recollision graph of order `≤ D`; if `⊕`, `⊖` lie in one dotted block its
order is `≥ 4`, and `≥ 5` without labels; without internal atom, the diffusive edge at `⊗` joins
`⊗` to `⊕`, the `Q` label is at `⊕` and the graph has the profile at `⊖`
(`Graph.MinusProfile`). -/
def TerminationB_Inv (n D : ℕ) {n₀ : ℕ} (Γ : Graph 3 n₀) : Prop :=
  (Γ.Plain ∨ (D : ℤ) < Γ.paperOrd) ∧ (Γ.LabelFree → 3 ≤ Γ.paperOrd) ∧
    (Γ.LabelFree → Γ.paperOrd ≤ n → gsPM' Γ) ∧
    (Γ.LabelFree → Γ.IsRecollision {1, 2} → Γ.paperOrd ≤ D → gsPM' Γ) ∧
    (Γ.PMBlock → 4 ≤ Γ.paperOrd ∧ (Γ.LabelFree → 5 ≤ Γ.paperOrd)) ∧
    (n₀ = 0 → Γ.RootAtPlus ∧ Γ.QLabelAtPlus ∧ Γ.MinusProfile)

section InvReorder

variable {n : ℕ} {π : Equiv.Perm (Fin n)} {Γ Γ' : Graph 3 n}

/-- `gsPM'` of a graph without ghost edges passes to a graph equal up to names and order. -/
private theorem TerminationB_iso_gs (h : RunClauses_Iso π Γ Γ') (hG : Γ.NoGhost)
    (hgs : gsPM' Γ) : gsPM' Γ' := by
  set F : Atom 3 n → Atom 3 n := fun v => Γ'.molRep (RunClauses_eA π v) with hFdef
  have hFmol : ∀ v, F (Γ.molRep v) = F v := RunClauses_iso_molRep h
  have hfix : ∀ v ∈ (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext : Set (Atom 3 n)), Γ.molRep v = v := by
    intro v hv
    rcases hv with hv | hv
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hv
      exact Local_molRep_idem Γ _
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hv
      rfl
  have hinj : Set.InjOn F (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext) := by
    intro v hv w hw hvw
    rw [← hfix v hv, ← hfix w hw, Local_molRep_eq_iff, ← RunClauses_iso_sameMol h,
      ← Local_molRep_eq_iff]
    exact hvw
  have hpin : ∀ a, Local_Same (Local_edMap F (Local_pin Γ a)) (Local_pin Γ' a) := by
    intro a
    have hU := RunClauses_iso_unpinned h (.inl a)
    unfold Local_pin
    rcases h1 : Γ.anchor (.inl a) with - | b <;> rcases h2 : Γ'.anchor (.inl a) with - | b'
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd (Local_anchor_some h2) ((hU.2 ⟨rfl, Local_anchor_none.1 h1⟩).2 b')
    · exact absurd (Local_anchor_some h1) ((hU.1 ⟨rfl, Local_anchor_none.1 h2⟩).2 b)
    · right
      refine ⟨rfl, Or.inl ?_⟩
      change (Γ'.molRep (.inr b'), (.inl a : Atom 3 n)) = (F (Γ.molRep (.inr b)), F (.inl a))
      rw [hFmol]
      refine Prod.ext ?_ rfl
      have hbl : Γ'.SameBlock (.inr b') (RunClauses_eA π (.inr b)) :=
        (Local_anchor_some h2).symm.trans
          ((RunClauses_iso_sameBlock h (.inl a) (.inr b)).2 (Local_anchor_some h1))
      exact RunClauses_molRep_of_block Γ' hbl (Or.inr ⟨rfl, rfl⟩)
  have c1 := Local_ELG_mapV (Pn := Fin 3) (pe' := Local_pin Γ') F (Γ.comps.map (Local_rd Γ))
    hinj hpin (Local_rdL_vok Γ Γ.comps) (Local_pin_vok Γ)
  have hI : Γ.toMG'.int.image F = Γ'.toMG'.int := by
    ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨π a, by rw [hFmol]; rfl⟩
    · rintro ⟨a', rfl⟩
      refine ⟨Γ.molRep (.inr (π.symm a')), ⟨_, rfl⟩, ?_⟩
      rw [hFmol]
      simp [hFdef, RunClauses_eA_inr]
  have hX : Γ.toMG'.ext.image F = Γ'.toMG'.ext := by
    ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨.inl a, ⟨a, rfl⟩, rfl⟩
  have hL : (Γ.comps.map (Local_rd Γ)).map (Local_edMap F) =
      (Γ.comps.map (Comp.map (RunClauses_eA π))).map (Local_rd Γ') := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    have key : Γ'.molRep (RunClauses_eA π (Local_rho Γ c.x)) =
        Γ'.molRep (RunClauses_eA π (Local_rho Γ c.y)) ↔ Local_rho Γ c.x = Local_rho Γ c.y :=
      hinj.eq_iff (Local_rho_vtx Γ _) (Local_rho_vtx Γ _)
    simp only [Function.comp_apply, Local_rd, Local_edMap, Comp.map, RunClauses_iso_rho h, key]
    rfl
  rw [hI, hX, hL] at c1
  obtain ⟨-, cs, h1, h2⟩ := id h
  have c2 : Local_Carry (Local_RG Γ' (Γ.comps.map (Comp.map (RunClauses_eA π))))
      (Local_RG Γ' cs) id := by
    refine Local_RG_same Γ' (h1.imp fun c c' hr => ?_)
    rcases hr with rfl | ⟨hk, rfl⟩
    · exact Local_Same.refl _
    · right
      refine ⟨?_, Or.inr rfl⟩
      simp only [Local_rd, @eq_comm _ (Local_rho Γ' c.y)]
  have hc := Local_carry_trans (Local_carry_trans (Local_carry_trans
    (Local_carry_trans (Local_carry_toRG Γ) c1) c2) (Local_RG_perm Γ' h2)) (Local_carry_ofRG Γ')
  obtain ⟨hs', -, -, hp⟩ := hc (Graph.toMG'_disjoint Γ) (Graph.toMG'_noGhost Γ hG) hgs.1
  exact Local_pull_gs hp hgs hs'

private theorem TerminationB_iso_plain (h : RunClauses_Iso π Γ Γ') (hP : Γ.Plain) : Γ'.Plain := by
  intro c' hc'
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  obtain ⟨hk, hl, hm, hxy, -⟩ := RunClauses_swapR_eq hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP c hc
  refine ⟨by rw [hm]; simp [Comp.map, h1], fun ch => by rw [hk]; exact h2 ch,
    fun ch d => by rw [hk]; exact h3 ch d, fun hd => ?_, fun hw => ?_, fun hs => ?_⟩
  · rw [hk] at hd
    have hne := h4 hd
    rcases hxy with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> simp only [Comp.map] <;>
      intro he <;> exact hne ((RunClauses_eA π).injective (by first | exact he | exact he.symm))
  · rw [hk] at hw
    have hw' : c.kind.isWeight = true := hw
    have e := h5 hw'
    have hr' : c.kind.isRandom = true := by
      revert hw'; cases c.kind <;> simp [Kind.isWeight, Kind.isRandom]
    obtain ⟨e1, e2⟩ : c'.x = (c.map (RunClauses_eA π)).x ∧ c'.y = (c.map (RunClauses_eA π)).y := by
      rw [(RunClauses_swapR_eq hr).2.2.2.2 (Or.inl hr')]; exact ⟨rfl, rfl⟩
    rw [e1, e2]
    simp [Comp.map, e]
  · rw [hk]
    rw [hl] at hs
    exact h6 (by simpa [Comp.map, Option.isSome_map] using hs)

private theorem TerminationB_iso_labelFree (h : RunClauses_Iso π Γ Γ') (hL : Γ'.LabelFree) :
    Γ.LabelFree := by
  intro c hc
  obtain ⟨c', hc', hr⟩ := RunClauses_iso_mem h hc
  have := hL c' hc'
  rw [(RunClauses_swapR_eq hr).2.1] at this
  simpa [Comp.map] using this

private theorem TerminationB_iso_recoll (h : RunClauses_Iso π Γ Γ')
    (hR : Γ'.IsRecollision {1, 2}) : Γ.IsRecollision {1, 2} := by
  obtain ⟨c', hc', hk', hb⟩ := hR
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  obtain ⟨-, -, -, hxy, -⟩ := RunClauses_swapR_eq hr
  have hk : c'.kind = c.kind := (RunClauses_swapR_eq hr).1
  have hinl : ∀ u (b : Fin 3), RunClauses_eA π u = .inl b → u = .inl b :=
    fun u b e => (RunClauses_eA_inl_iff π u b).1 e
  have hR' : ∀ u, (RunClauses_eA π u).isRight = true → u.isRight = true :=
    fun u e => by rwa [RunClauses_eA_isRight] at e
  refine ⟨c, hc, by rw [← hk]; exact hk', ?_⟩
  rcases hxy with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hb <;> simp only [Comp.map] at hb
  · rcases hb with ⟨⟨b, hb, e⟩, hy⟩ | ⟨⟨b, hb, e⟩, hy⟩
    · exact Or.inl ⟨⟨b, hb, hinl _ _ e⟩, hR' _ hy⟩
    · exact Or.inr ⟨⟨b, hb, hinl _ _ e⟩, hR' _ hy⟩
  · rcases hb with ⟨⟨b, hb, e⟩, hy⟩ | ⟨⟨b, hb, e⟩, hy⟩
    · exact Or.inr ⟨⟨b, hb, hinl _ _ e⟩, hR' _ hy⟩
    · exact Or.inl ⟨⟨b, hb, hinl _ _ e⟩, hR' _ hy⟩

private theorem TerminationB_iso_pm (h : RunClauses_Iso π Γ Γ') : Γ'.PMBlock ↔ Γ.PMBlock := by
  rw [Graph.pmBlock_iff_sameBlock, Graph.pmBlock_iff_sameBlock, ← RunClauses_eA_inl π 1,
    ← RunClauses_eA_inl π 2]
  exact RunClauses_iso_sameBlock h _ _

private theorem TerminationB_iso_root (h : RunClauses_Iso π Γ Γ') (hR : Γ.RootAtPlus) :
    Γ'.RootAtPlus := by
  unfold Graph.RootAtPlus at hR ⊢
  rw [List.all_eq_true] at hR ⊢
  intro c' hc'
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  have hcR := hR c hc
  by_cases hd : c.kind.isDiffusive = true
  · rw [(RunClauses_swapR_eq hr).2.2.2.2 (Or.inr hd)]
    have e0 : ∀ u (b : Fin 3), (RunClauses_eA π u == .inl b) = (u == .inl b) := fun u b => by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact RunClauses_eA_inl_iff π u b
    simpa [Comp.map, e0] using hcR
  · have hk : c'.kind = c.kind := (RunClauses_swapR_eq hr).1
    simp [hk, Bool.not_eq_true _ ▸ hd]

private theorem TerminationB_iso_qPlus (h : RunClauses_Iso π Γ Γ') (hQ : Γ.QLabelAtPlus) :
    Γ'.QLabelAtPlus := by
  intro c' hc' u hl
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  rw [(RunClauses_swapR_eq hr).2.1] at hl
  simp only [Comp.map, Option.map_eq_some_iff] at hl
  obtain ⟨⟨q, w⟩, hw, he⟩ := hl
  simp only [Prod.map, id, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [hQ c hc w hw]
  rfl

/-- The profile at `⊖` is carried by the renumbering of the internal atoms and the exchange of the
atoms of waved edges `s`, dotted and `×`-dotted edges: the components with an end at `⊖` keep their
kind, only dotted and `×`-dotted edges exchange their ends, and the red solid edges `Ḡ_{u⊖}` are
not exchanged. -/
private theorem TerminationB_iso_minus (h : RunClauses_Iso π Γ Γ') (hM : Γ.MinusProfile) :
    Γ'.MinusProfile := by
  obtain ⟨hP1, hP2⟩ := hM
  have e2 : ∀ u : Atom 3 n, RunClauses_eA π u = .inl 2 ↔ u = .inl 2 :=
    fun u => RunClauses_eA_inl_iff π u 2
  refine ⟨fun c' hc' hend => ?_, ?_⟩
  · obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
    rcases hr with rfl | ⟨hk, rfl⟩
    · have hend' : c.x = .inl 2 ∨ c.y = .inl 2 := by simpa [Comp.map, e2] using hend
      simpa only [Comp.map, ne_eq, e2] using hP1 c hc hend'
    · have hend' : c.x = .inl 2 ∨ c.y = .inl 2 := by
        simp only [Comp.map, e2] at hend
        exact hend.symm
      rcases hP1 c hc hend' with h1 | h1 | ⟨h1, -, -⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exfalso
        simp only [Comp.map] at hk
        rw [h1] at hk
        simp at hk
  · have hp : ∀ c c' : Comp (Atom 3 n), RunClauses_SwapR c c' →
        (decide (c'.kind = .G .minus ∧ c'.y = .inl 2 ∧ c'.x ≠ .inl 2) : Bool) =
          decide (c.kind = .G .minus ∧ c.y = .inl 2 ∧ c.x ≠ .inl 2) := by
      intro c c' hr
      rcases hr with rfl | ⟨hk, rfl⟩
      · rfl
      · have hn : c.kind ≠ .G .minus := fun h1 => by rw [h1] at hk; simp at hk
        simp [hn]
    have hf : ((fun c : Comp (Atom 3 n) =>
        decide (c.kind = .G .minus ∧ c.y = .inl 2 ∧ c.x ≠ .inl 2)) ∘ Comp.map (RunClauses_eA π)) =
        fun c => decide (c.kind = .G .minus ∧ c.y = .inl 2 ∧ c.x ≠ .inl 2) := by
      funext c
      refine decide_eq_decide.2 ?_
      simp only [Function.comp, Comp.map, ne_eq, e2]
    rw [RunClauses_iso_count h _ hp, hf]
    exact hP2

/-- **A reordering keeps the leaf invariants of a run** (`TerminationB_Inv`), on a graph with
the invariant of a run, for `n ≤ D`: plainness, the orders, the labels, the blocks of `⊕` and `⊖`,
the `⊕/⊖`-recollision graphs, `gsPM'` (without ghost edges), the diffusive edges at `⊗` and the
`Q` labels and the profile at `⊖` are carried by the renumbering of the internal atoms and the
exchange of the atoms of waved edges `s`, dotted and `×`-dotted edges. -/
theorem TerminationB_inv_reorder {N D : ℕ} (hND : N ≤ D) (h : Γ.Reorder Γ')
    (hI : Γ.InvRun D) (hv : TerminationB_Inv N D Γ) : TerminationB_Inv N D Γ' := by
  obtain ⟨π, hi⟩ := RunClauses_reorder_iso h
  have hp := RunClauses_iso_paperOrd hi
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hv
  have hng : Γ.LabelFree → Γ.paperOrd ≤ D → Γ.NoGhost := by
    intro hL hD
    rcases hI with ⟨hB, -⟩ | ⟨-, hQ⟩ | ⟨hD', -⟩
    · exact hB.2.2.2.1
    · exact absurd hQ (Termination_not_qGraph hL)
    · omega
  refine ⟨?_, fun hL => ?_, fun hL ho' => ?_, fun hL hR ho' => ?_, fun hP => ?_,
    fun h0 => ?_⟩
  · rcases v1 with h1 | h1
    · exact Or.inl (TerminationB_iso_plain hi h1)
    · exact Or.inr (by rw [hp]; exact h1)
  · rw [hp]; exact v2 (TerminationB_iso_labelFree hi hL)
  · have hL' := TerminationB_iso_labelFree hi hL
    rw [hp] at ho'
    exact TerminationB_iso_gs hi (hng hL' (by omega)) (v3 hL' ho')
  · have hL' := TerminationB_iso_labelFree hi hL
    rw [hp] at ho'
    exact TerminationB_iso_gs hi (hng hL' ho') (v4 hL' (TerminationB_iso_recoll hi hR) ho')
  · rw [hp]
    obtain ⟨h1, h2⟩ := v5 ((TerminationB_iso_pm hi).1 hP)
    exact ⟨h1, fun hL => h2 (TerminationB_iso_labelFree hi hL)⟩
  · obtain ⟨h1, h2, h3⟩ := v6 h0
    exact ⟨TerminationB_iso_root hi h1, TerminationB_iso_qPlus hi h2, TerminationB_iso_minus hi h3⟩

end InvReorder

section InvDup

variable {k n : ℕ}

/-- Reachability passes from `G'` to `G` when the adjacent vertices of `G'` are reachable in
`G`. -/
private theorem TerminationB_reach_of {V : Type*} {G G' : SimpleGraph V}
    (h : ∀ u v, G'.Adj u v → G.Reachable u v) {u v : V} (hr : G'.Reachable u v) :
    G.Reachable u v := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => rfl
  | cons ha _ ih => exact (h _ _ ha).trans ih

/-- A graph with one more dotted edge between two atoms of one block has the same blocks and the
same molecules. -/
private theorem TerminationB_appDot_facts {Γ : Graph k n} {d : Comp (Atom k n)}
    (hk : d.kind = .dot) (hb : Γ.SameBlock d.x d.y) :
    (∀ u v, (⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph k n).SameBlock u v ↔ Γ.SameBlock u v) ∧
      (∀ u v, (⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph k n).SameMol u v ↔ Γ.SameMol u v) := by
  set Γ'' : Graph k n := ⟨Γ.comps ++ [d], Γ.coeff⟩ with hΓ''
  have hsub : ∀ c ∈ Γ.comps, c ∈ Γ''.comps := fun c hc => List.mem_append_left _ hc
  have hcases : ∀ c ∈ Γ''.comps, c ∈ Γ.comps ∨ c = d := by
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)
  have hdm : ∀ u v, Γ.SameBlock u v → Γ.molGraph.Reachable u v := by
    intro u v huv
    refine TerminationB_reach_of (fun a b hab => ?_) huv
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
    refine SimpleGraph.Adj.reachable ?_
    rw [Graph.molGraph, SimpleGraph.fromRel_adj]
    obtain ⟨hne, ⟨c, hc, hck, h1, h2⟩ | ⟨c, hc, hck, h1, h2⟩⟩ := hab
    · exact ⟨hne, Or.inl ⟨c, hc, by rw [hck]; rfl, h1, h2⟩⟩
    · exact ⟨hne, Or.inr ⟨c, hc, by rw [hck]; rfl, h1, h2⟩⟩
  have hblk : ∀ u v, Γ''.SameBlock u v ↔ Γ.SameBlock u v := by
    intro u v
    constructor
    · intro h
      refine TerminationB_reach_of (fun a b hab => ?_) h
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨hne, ⟨c, hc, hck, h1, h2⟩ | ⟨c, hc, hck, h1, h2⟩⟩ := hab
      · rcases hcases c hc with hc | rfl
        · exact SimpleGraph.Adj.reachable (by
            rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
            exact ⟨hne, Or.inl ⟨c, hc, hck, h1, h2⟩⟩)
        · rw [← h1, ← h2]; exact hb
      · rcases hcases c hc with hc | rfl
        · exact SimpleGraph.Adj.reachable (by
            rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
            exact ⟨hne, Or.inr ⟨c, hc, hck, h1, h2⟩⟩)
        · rw [← h1, ← h2]; exact hb.symm
    · intro h
      refine TerminationB_reach_of (fun a b hab => SimpleGraph.Adj.reachable ?_) h
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab ⊢
      obtain ⟨hne, ⟨c, hc, hck, h1, h2⟩ | ⟨c, hc, hck, h1, h2⟩⟩ := hab
      · exact ⟨hne, Or.inl ⟨c, hsub c hc, hck, h1, h2⟩⟩
      · exact ⟨hne, Or.inr ⟨c, hsub c hc, hck, h1, h2⟩⟩
  refine ⟨hblk, fun u v => ?_⟩
  unfold Graph.SameMol
  refine or_congr_right (and_congr_right fun _ => and_congr_right fun _ => ?_)
  constructor
  · intro h
    refine TerminationB_reach_of (fun a b hab => ?_) h
    rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
    obtain ⟨hne, ⟨c, hc, hck, h1, h2⟩ | ⟨c, hc, hck, h1, h2⟩⟩ := hab
    · rcases hcases c hc with hc | rfl
      · exact SimpleGraph.Adj.reachable (by
          rw [Graph.molGraph, SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inl ⟨c, hc, hck, h1, h2⟩⟩)
      · rw [← h1, ← h2]; exact hdm _ _ hb
    · rcases hcases c hc with hc | rfl
      · exact SimpleGraph.Adj.reachable (by
          rw [Graph.molGraph, SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inr ⟨c, hc, hck, h1, h2⟩⟩)
      · rw [← h1, ← h2]; exact hdm _ _ hb.symm
  · intro h
    refine TerminationB_reach_of (fun a b hab => SimpleGraph.Adj.reachable ?_) h
    rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hab ⊢
    obtain ⟨hne, ⟨c, hc, hck, h1, h2⟩ | ⟨c, hc, hck, h1, h2⟩⟩ := hab
    · exact ⟨hne, Or.inl ⟨c, hsub c hc, hck, h1, h2⟩⟩
    · exact ⟨hne, Or.inr ⟨c, hsub c hc, hck, h1, h2⟩⟩

/-- The molecular graph `Graph.toMG'` of a graph with one more dotted edge between two atoms of
one block is that of the graph with one more absent edge. -/
private theorem TerminationB_toMG'_appDot {Γ : Graph k n} {d : Comp (Atom k n)}
    (hk : d.kind = .dot) (hb : Γ.SameBlock d.x d.y) :
    Γ.toMG'.Transported (⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph k n).toMG' := by
  set Γ' : Graph k n := ⟨Γ.comps ++ [d], Γ.coeff⟩ with hΓ'
  obtain ⟨hsb, hsm⟩ := TerminationB_appDot_facts hk hb
  have hrep : ∀ u, Γ'.molRep u = Γ.molRep u := by
    intro u
    unfold Graph.molRep
    rcases u with a | a
    · rfl
    · change Sum.inr _ = Sum.inr _
      congr 3
      funext b
      exact decide_eq_decide.2 (hsm _ _)
  have hfc : ∀ c, Γ'.flatComp c = Γ.flatComp c := Termination_flatComp_congr hsb
  have han : ∀ u, Γ'.anchor u = Γ.anchor u := Termination_anchor_congr hsb
  have hlt : ∀ j : Fin Γ.comps.length, (j : ℕ) < Γ'.comps.length := fun j => by
    simp only [hΓ', List.length_append, List.length_singleton]
    omega
  have hget : ∀ j : Fin Γ.comps.length, Γ'.comps[(j : ℕ)]'(hlt j) = Γ.comps[j] := fun j =>
    List.getElem_append_left _
  let ι : Fin Γ.comps.length → Fin Γ'.comps.length := fun j => ⟨j, hlt j⟩
  have hcls : ∀ j, Γ'.toMG'.cls (.inl (ι j)) = Γ.toMG'.cls (.inl j) := by
    intro j
    simp only [Graph.toMG', Fin.getElem_fin, ι, hget, hfc, hrep]
  have hends : ∀ j, Γ'.toMG'.ends (.inl (ι j)) = Γ.toMG'.ends (.inl j) := by
    intro j
    simp only [Graph.toMG', Fin.getElem_fin, ι, hget, hfc, hrep]
  have hclsr : ∀ a, Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a) := by
    intro a
    simp only [Graph.toMG', han]
  have hendsr : ∀ a, Γ'.toMG'.ends (.inr a) = Γ.toMG'.ends (.inr a) := by
    intro a
    simp only [Graph.toMG', han, hrep]
  refine ⟨id, Sum.map ι id, ?_, Set.injOn_id _, ?_, ?_,
    fun e _ => MolInsert_toMG'_ends_vtx k n Γ e, ?_, ?_, ?_⟩
  · rintro (a | a) (b | b) - - h
    · simp only [Sum.map_inl, Sum.inl.injEq] at h
      exact congrArg Sum.inl (Fin.ext (by simpa [ι] using congrArg Fin.val h))
    · simp at h
    · simp at h
    · simpa using h
  · simp only [Graph.toMG', Finset.image_id, hrep]
  · simp only [Graph.toMG', Finset.image_id]
  · rintro (j | a) _
    · exact hcls j
    · exact hclsr a
  · rintro (j | a) _
    · left
      rw [Sum.map_inl, hends j]
      rfl
    · left
      simp only [Sum.map_inr, id, hendsr a]
  · rintro (j | a) hj
    · by_cases hjl : (j : ℕ) < Γ.comps.length
      · by_contra hne
        refine hj (.inl ⟨j, hjl⟩) ?_ rfl
        rw [← hcls]
        exact hne
      · have hj' : (j : ℕ) = Γ.comps.length := by
          have := j.2
          simp [hΓ'] at this
          omega
        have hdj : Γ'.comps[j] = d := by
          simp only [Fin.getElem_fin, hΓ', hj']
          exact List.getElem_concat_length rfl _
        simp only [Graph.toMG', hdj]
        rw [ite_eq_left (Or.inl (by simp [Graph.flatComp, hk]))]
    · by_contra hne
      refine hj (.inr a) ?_ rfl
      rw [← hclsr]
      exact hne

/-- The test of a component that is a red solid edge `Ḡ_{u⊖}` with second atom `⊖` and first atom
`u ≠ ⊖`, counted by `Graph.MinusProfile`. -/
private def TerminationB_minusG {n₀ : ℕ} (c : Comp (Atom 3 n₀)) : Bool :=
  decide (c.kind = .G .minus ∧ c.y = .inl 2 ∧ c.x ≠ .inl 2)

/-- The leaf invariants other than `gsPM'` pass to a graph whose components are components of
the first graph, with the same blocks and the same order in the count of [II, (2.5)], when the
first graph has a label wherever the second has one and at least as many red solid edges
`Ḡ_{u⊖}` with `u ≠ ⊖`. -/
private theorem TerminationB_inv_sub {N D n₀ : ℕ} {Γ Γ' : Graph 3 n₀} (hND : N ≤ D)
    (hs : ∀ c ∈ Γ'.comps, c ∈ Γ.comps) (hb : ∀ u v, Γ'.SameBlock u v ↔ Γ.SameBlock u v)
    (hp : Γ'.paperOrd = Γ.paperOrd) (hL : Γ'.LabelFree → Γ.LabelFree)
    (hPl : Γ.Plain → Γ'.Plain) (hgs : Γ'.LabelFree → Γ'.paperOrd ≤ D → gsPM' Γ → gsPM' Γ')
    (hcnt : (Γ'.comps.filter TerminationB_minusG).length ≤
      (Γ.comps.filter TerminationB_minusG).length)
    (hv : TerminationB_Inv N D Γ) : TerminationB_Inv N D Γ' := by
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hv
  refine ⟨?_, fun h => by rw [hp]; exact v2 (hL h),
    fun h ho => hgs h (by omega) (v3 (hL h) (by rw [← hp]; exact ho)),
    fun h hR ho => hgs h ho (v4 (hL h) ?_ (by rw [← hp]; exact ho)), fun hP => ?_, fun h0 => ?_⟩
  · rcases v1 with h | h
    · exact Or.inl (hPl h)
    · exact Or.inr (by rw [hp]; exact h)
  · obtain ⟨c, hc, hk, h⟩ := hR
    exact ⟨c, hs c hc, hk, h⟩
  · rw [Graph.pmBlock_iff_sameBlock, hb, ← Graph.pmBlock_iff_sameBlock] at hP
    rw [hp]
    exact ⟨(v5 hP).1, fun h => (v5 hP).2 (hL h)⟩
  · obtain ⟨h1, h2, h3⟩ := v6 h0
    refine ⟨?_, fun c hc u hu => h2 c (hs c hc) u hu, fun c hc hend => h3.1 c (hs c hc) hend,
      hcnt.trans h3.2⟩
    unfold Graph.RootAtPlus at h1 ⊢
    exact List.all_eq_true.2 fun c hc => List.all_eq_true.1 h1 c (hs c hc)

/-- **The duplication of a `×`-dotted edge keeps the leaf invariants of a run**
(`TerminationB_Inv`): the components, the blocks, the order in the count of [II, (2.5)] and the
labels are kept, and `Graph.toMG'` gains one absent edge. -/
theorem TerminationB_inv_xdotDup {N D n₀ : ℕ} (hND : N ≤ D) (Γ : Graph 3 n₀)
    (i : Fin Γ.comps.length) (hk : Γ.comps[i].kind = .xdot) (hv : TerminationB_Inv N D Γ) :
    TerminationB_Inv N D (⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩ : Graph 3 n₀) := by
  have hd : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
  obtain ⟨hmem, -, hord, hex, -⟩ := Termination_dup_facts (g := Γ)
    (g' := ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩) (List.Perm.refl _) hd hk
  refine TerminationB_inv_sub hND (fun c hc => (hmem c).1 hc) (Termination_sameBlock_mem hmem)
    (by unfold Graph.paperOrd; rw [hord, hex]) (fun h c hc => h c ((hmem c).2 hc))
    (fun h c hc => h c ((hmem c).1 hc))
    (fun _ _ h => (SubstMol_gs_transport (Termination_toMG'_app hd hk)).2 h)
    (by
      have hn : TerminationB_minusG Γ.comps[i] = false := by
        unfold TerminationB_minusG
        rw [hk]
        simp
      rw [List.filter_append, List.length_append,
        List.filter_cons_of_neg (by rw [hn]; simp), List.filter_nil]
      simp) hv

/-- **The removal of one of two parallel `×`-dotted edges keeps the leaf invariants of a run**
(`TerminationB_Inv`): the graph is a reordering of the graph with the edge listed once more
(`TerminationB_inv_reorder`), which has the same components, blocks and order, and whose
`Graph.toMG'` has one more absent edge. -/
theorem TerminationB_inv_xdotDrop {N D n₀ : ℕ} (hND : N ≤ D) (Γ : Graph 3 n₀)
    (i j : Fin Γ.comps.length) (hij : i ≠ j)
    (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) (hI : Γ.InvRun D) (hv : TerminationB_Inv N D Γ) :
    TerminationB_Inv N D (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 n₀) := by
  set Γ' : Graph 3 n₀ := ⟨Γ.comps.eraseIdx j, Γ.coeff⟩ with hΓ'
  have hd : Γ.comps[i] ∈ Γ'.comps :=
    List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, fun h => hij (Fin.ext h), rfl⟩
  have hv' := TerminationB_inv_reorder hND (Strategy_reorder_xdotDrop Γ i j hc hk) hI hv
  obtain ⟨hmem, -, hord, hex, -⟩ := Termination_dup_facts (g := Γ')
    (g' := ⟨Γ'.comps ++ [Γ.comps[i]], Γ'.coeff⟩) (List.Perm.refl _) hd hk
  exact TerminationB_inv_sub (Γ := ⟨Γ'.comps ++ [Γ.comps[i]], Γ'.coeff⟩) hND
    (fun c hc => (hmem c).2 hc) (fun u v => (Termination_sameBlock_mem hmem u v).symm)
    (by unfold Graph.paperOrd; rw [hord, hex]) (fun h c hc => h c ((hmem c).1 hc))
    (fun h c hc => h c ((hmem c).2 hc))
    (fun _ _ h => (SubstMol_gs_transport (Termination_toMG'_app hd hk)).1 h)
    (by rw [List.filter_append, List.length_append]; exact Nat.le_add_right _ _) hv'

/-- **A change of the coefficient keeps the leaf invariants of a run** (in particular the step
`coeffNorm`): `TerminationB_Inv` reads the components only. -/
theorem TerminationB_inv_coeffNorm {N D n₀ : ℕ} (hND : N ≤ D) (Γ : Graph 3 n₀) (co : Coeff)
    (hv : TerminationB_Inv N D Γ) : TerminationB_Inv N D (⟨Γ.comps, co⟩ : Graph 3 n₀) :=
  TerminationB_inv_sub (Γ := Γ) (Γ' := ⟨Γ.comps, co⟩) hND (fun _ hc => hc) (fun _ _ => Iff.rfl)
    rfl (fun h => h) (fun h => h)
    (fun _ _ h => (SubstMol_gs_transport (Termination_toMG'_coeff Γ co)).2 h) le_rfl hv

/-- A component mapped by the renumbering of the internal atoms by the identity is the
component. -/
private theorem TerminationB_map_eA_refl {n : ℕ} (c : Comp (Atom 3 n)) :
    c.map (RunClauses_eA (Equiv.refl (Fin n))) = c := by
  have hf : (RunClauses_eA (Equiv.refl (Fin n)) : Atom 3 n → Atom 3 n) = id := by
    funext u; cases u <;> rfl
  rw [hf]
  cases c with
  | mk κ x y mi l => simp [Comp.map]

/-- **The removal of a redundant dotted edge keeps the leaf invariants of a run**
(`TerminationB_Inv`), on a normal regular plain graph with the invariant of a run, for `n ≤ D`:
the blocks, the order in the count of [II, (2.5)] and the components other than dotted edges are
kept, and `Graph.toMG'` loses one absent edge. -/
theorem TerminationB_inv_dropDot {N D C n₀ : ℕ} {Γ Γ' : Graph 3 n₀} (hND : N ≤ D)
    (hst : DotNormStep Γ Γ') (hN : Γ.Normal C) (hP : Γ.Plain) (hI : Γ.InvRun D)
    (hv : TerminationB_Inv N D Γ) : TerminationB_Inv N D Γ' := by
  obtain ⟨i, c, hc, hk, hr, rfl⟩ := hst
  obtain ⟨he, hord, hK⟩ := DotNorm.step hN hP hc hk hr
  obtain ⟨A, B, hA, hAB⟩ := Termination_split hc
  set Γ₁ : Graph 3 n₀ := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ with hΓ₁
  have hsub : ∀ d ∈ Γ₁.comps, d ∈ Γ.comps := fun d hd => (DotNorm.Keep.sub hK).subset hd
  have hcl : c.label = none := by
    have hcm : c ∈ Γ.comps := by rw [hA]; simp
    obtain ⟨-, -, -, -, -, h6⟩ := hP c hcm
    cases hl : c.label with
    | none => rfl
    | some l =>
      have := h6 (by rw [hl]; rfl)
      rw [hk] at this
      cases this
  have hL : Γ₁.LabelFree → Γ.LabelFree := by
    intro h d hd
    rw [hA] at hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h d (by rw [hΓ₁]; simp only [hAB]; exact List.mem_append_left _ hd)
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact hcl
      · exact h d (by rw [hΓ₁]; simp only [hAB]; exact List.mem_append_right _ hd)
  have hp : Γ₁.paperOrd = Γ.paperOrd := by unfold Graph.paperOrd; linarith
  refine TerminationB_inv_sub hND hsub (DotNorm.Keep.block hK) hp hL
    (fun _ => DotNorm.Keep.plain hK) (fun h1 hD hgs => ?_)
    (((DotNorm.Keep.sub hK).filter _).length_le) hv
  have hng : Γ.NoGhost := by
    rcases hI with ⟨hB, -⟩ | ⟨-, hQ⟩ | ⟨hD', -⟩
    · exact hB.2.2.2.1
    · exact absurd hQ (Termination_not_qGraph (hL h1))
    · rw [hp] at hD
      omega
  set Γ₂ : Graph 3 n₀ := ⟨Γ₁.comps ++ [c], Γ₁.coeff⟩ with hΓ₂
  have hiso : RunClauses_Iso (Equiv.refl (Fin n₀)) Γ Γ₂ := by
    refine ⟨rfl, Γ.comps.map (Comp.map (RunClauses_eA (Equiv.refl (Fin n₀)))),
      List.forall₂_same.2 fun _ _ => Or.inl rfl, ?_⟩
    have hmap : ∀ L : List (Comp (Atom 3 n₀)),
        L.map (Comp.map (RunClauses_eA (Equiv.refl (Fin n₀)))) = L := fun L => by
      induction L with
      | nil => rfl
      | cons d L ih => rw [List.map_cons, ih, TerminationB_map_eA_refl]
    rw [hmap]
    simp only [hΓ₂, hΓ₁, hAB]
    rw [hA]
    exact List.perm_middle.trans (List.perm_append_singleton c (A ++ B)).symm
  exact (SubstMol_gs_transport (TerminationB_toMG'_appDot hk hr)).1
    (TerminationB_iso_gs hiso hng hgs)

end InvDup

/-! ## The leaf invariants along Steps 2–3 -/

section InvSubst

variable {n D : ℕ} {𝒯 : TRec} {m C : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}

/-- An `O_dot` form of a graph with an internal atom has an internal atom. -/
private theorem TerminationB_oDotT_nOut {k n₁ : ℕ} {Γ : Graph k n₁} (h : n₁ ≠ 0)
    {t : Tracked k n₁} (ht : t ∈ oDotT Γ) : t.nOut ≠ 0 := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact h
  · obtain ⟨g, -, -⟩ := (mergeT_spec hm).f_inr
    intro h0
    have := g ⟨0, Nat.pos_of_ne_zero h⟩
    rw [h0] at this
    exact this.elim0

/-- A graph without dotted edges has `⊕`, `⊖` in different blocks and is not a
`⊕/⊖`-recollision graph. -/
private theorem TerminationB_dotFree_pm {n₁ : ℕ} {Γ : Graph 3 n₁} (h : Γ.DotFree) :
    ¬ Γ.PMBlock ∧ ¬ Γ.IsRecollision {1, 2} := by
  refine ⟨fun hP => ?_, fun ⟨c, hc, hk, _⟩ => h c hc hk⟩
  rw [Graph.pmBlock_iff_sameBlock,
    Graph.sameBlock_iff_eq Γ (fun c hc hk => absurd hk (h c hc))] at hP
  exact absurd (Sum.inl.inj hP) (by decide)

/-- The leaf invariants of a graph without dotted edges and with an internal atom, plain or of
order `> D`, from the order and `gsPM'` of its forms without labels. -/
private theorem TerminationB_inv_of_dotFree {n₁ : ℕ} {Γ : Graph 3 n₁} (hd : Γ.DotFree)
    (h0 : n₁ ≠ 0) (hP : Γ.Plain ∨ (D : ℤ) < Γ.ord) (h3 : Γ.LabelFree → 3 ≤ Γ.ord)
    (hgs : Γ.LabelFree → Γ.ord ≤ n → gsPM' Γ) : TerminationB_Inv n D Γ := by
  have hp : Γ.paperOrd = Γ.ord := TerminationB_paperOrd_of_dotFree hd
  obtain ⟨hpm, hrec⟩ := TerminationB_dotFree_pm hd
  refine ⟨by rw [hp]; exact hP, fun h => by rw [hp]; exact h3 h,
    fun h ho => hgs h (by rw [← hp]; exact ho),
    fun _ hR => absurd hR hrec, fun hpm' => absurd hpm' hpm, fun h => absurd h h0⟩

/-- **The leaf invariants of the `O_dot` forms of the substituted graphs** ([II, Lemma 6.5]
(1)–(5), [II, Lemma 6.8]): under the hypotheses of [II, Lemma 6.5], with the hypotheses on `𝒯`
of [II, Def 3.2] at order `n - 1` and of [II, Def 6.3], and `G = H.glue x y₁ y₂ (tVar true)`
plain, every `O_dot` form `t` of the substitution of a graph of `𝒯.tSubst (n - 1)` has no dotted
edge and the leaf invariants of a run (`TerminationB_Inv n D`): it is plain or of scaling order
`> D` (the graphs of `Err`); without labels it has scaling order `≥ ord G ≥ 4` and is globally
standard when of scaling order `≤ D`; it has an internal atom. -/
theorem TerminationB_inv_subst (hn : 3 ≤ n)
    (hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) (hL : H.LabelFree)
    (hN : (H.glue x y₁ y₂ (tVar true)).Normal C) (hd : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (ho1 : 4 ≤ (H.glue x y₁ y₂ (tVar true)).ord) (ho2 : (H.glue x y₁ y₂ (tVar true)).ord ≤ n)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hT : (H.glue x y₁ y₂ (tVar true)).TensorDiffusive)
    (hgs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hnr : ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2})
    (hM : (H.glue x y₁ y₂ (tVar true)).MISLocStdB)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (hPG : (H.glue x y₁ y₂ (tVar true)).Plain) :
    ∀ g ∈ 𝒯.tSubst (n - 1), ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid),
      t.g.DotFree ∧ TerminationB_Inv n D t.g := by
  obtain ⟨hnD, hSh, hDef⟩ := hcore
  have hnD' : n ≤ D := by omega
  obtain ⟨hx, -, -⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hm0 : m ≠ 0 := by
    rintro rfl
    rcases x with a | a
    · cases hx
    · exact a.elim0
  intro g hg t ht
  have h0 : t.nOut ≠ 0 := TerminationB_oDotT_nOut (by omega) ht
  have hpl : g ∈ leadExp ++ sigmaTExp (n - 1) ++ tVarCorr ∨ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q →
      ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), t.g.DotFree → t.g.Plain := by
    intro hg' t ht hd'
    have hgP : g.2.Plain := by
      rcases hg' with h | h
      · exact leadSigmaCorr_plain (n - 1) g h
      · exact TRec.plain_of_def63 hDef g h
    exact GlobalGoodB_plain_of (GlobalGoodB_oDot_PW (GlobalGoodB_glue_PW hPG hgP) ht) hd'
  have hrow1 : g ∈ leadExp ++ sigmaTExp (n - 1) ++ tVarCorr →
      t.g.DotFree ∧ TerminationB_Inv n D t.g := by
    intro hg1
    obtain ⟨-, hd', -, hgs', hor⟩ := globalGood_row1 n D 𝒯 m C H x y₁ y₂ hn ⟨hnD, hSh, hDef⟩ hL
      hN hd ho1 ho2 hI hT hgs hnr hM hst g hg1 t ht
    refine ⟨hd', TerminationB_inv_of_dotFree hd' h0 (Or.inl (hpl (Or.inl hg1) t ht hd'))
      (fun _ => ?_) (fun _ _ => hgs')⟩
    rcases hor with h | ⟨-, h, -⟩ <;> omega
  simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg
  rcases hg with (((((hg | hg) | hg) | hg) | hg) | hg) | hg
  · exact hrow1 (by simp [hg])
  · exact hrow1 (by simp [hg])
  · -- `R`
    obtain ⟨-, hd', -, hgs', hor⟩ := globalGood_row2 n D 𝒯 m C H x y₁ y₂ hn ⟨hnD, hSh, hDef⟩ hL
      hN hd ho1 ho2 hI hT hgs hnr hM hst g hg t ht
    refine ⟨hd', TerminationB_inv_of_dotFree hd' h0
      (Or.inl (hpl (Or.inr (by simp [hg])) t ht hd')) (fun _ => ?_) (fun _ _ => hgs')⟩
    rcases hor with h | ⟨-, h, -⟩ <;> omega
  · -- `A`
    obtain ⟨-, hd', -, h⟩ := globalGood_row3 n D 𝒯 m C H x y₁ y₂ hn ⟨hnD, hSh, hDef⟩ hL hN hd
      ho1 ho2 hI hT hgs hnr hM hst g hg t ht
    refine ⟨hd', TerminationB_inv_of_dotFree hd' h0
      (Or.inl (hpl (Or.inr (by simp [hg])) t ht hd')) (fun _ => ?_) (fun _ ho => ?_)⟩
    · rcases h with ⟨h, -⟩ | ⟨-, -, -, h⟩ <;> omega
    · rcases h with ⟨h, -⟩ | ⟨-, -, h, -⟩
      · omega
      · exact h
  · -- `Q`
    obtain ⟨-, hrow⟩ := GlobalGoodB_row4 n D 𝒯 m C H x y₁ y₂ hn ⟨hnD, hSh, hDef⟩ hL hN hd ho1
      ho2 hI hT hgs hnr hM hst hPG g hg
    obtain ⟨-, hd', htP, -, -, -⟩ := hrow t ht
    have hall : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
    obtain ⟨u, ⟨c, hc, hl⟩, -⟩ := (hSh.2.2.2.1 g hg).1
    obtain ⟨-, -, hNL, -⟩ := hDef.2.1 g hall
    have hk : c.kind ≠ .dot := fun h => by rw [hNL c hc (Or.inl h)] at hl; cases hl
    have hk' : c.kind ≠ .xdot := fun h => by rw [hNL c hc (Or.inr h)] at hl; cases hl
    have hmem : c.swapSolid.map (glueAtom x y₁ y₂) ∈ (H.glue x y₁ y₂ g.2.swapSolid).comps :=
      List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, rfl⟩)
    have hlab : (c.swapSolid.map (glueAtom x y₁ y₂)).label ≠ none := by
      have : c.swapSolid.label = c.label := by unfold Comp.swapSolid; split <;> rfl
      simp [Comp.map, this, hl]
    have hkind : (c.swapSolid.map (glueAtom x y₁ y₂)).kind = c.kind := by
      simp [Comp.map, SubstSPD_swap_kind]
    have hnl := TerminationB_oDotT_label hmem (by rw [hkind]; exact hk)
      (by rw [hkind]; exact hk') hlab t ht
    exact ⟨hd', TerminationB_inv_of_dotFree hd' h0 (Or.inl htP) (fun h => absurd h hnl)
      (fun h => absurd h hnl)⟩
  · -- `Err`
    obtain ⟨-, hd', -, h⟩ := globalGood_row5 glue_oDotT_normal n D 𝒯 m C H x y₁ y₂ hn
      ⟨hnD, hSh, hDef⟩ hL hN hd ho1 ho2 hI hT hgs hnr hM hst g hg t ht
    have hD : (D : ℤ) < t.g.ord := by omega
    exact ⟨hd', TerminationB_inv_of_dotFree hd' h0 (Or.inr hD) (fun _ => by omega)
      (fun _ ho => absurd ho (by omega))⟩
  · exact hrow1 (by simp [hg])

/-- The `O_dot` forms of a substituted graph of `Q` have scaling order `≥ ord G`, where
`G = H.glue x y₁ y₂ (tVar true)`: the graph `g` has scaling order `≥ 2`, and `≥ 4` when `⊕`, `⊖`
lie in one block of `g`. -/
private theorem TerminationB_rowQ_ord (hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63)
    (hL : H.LabelFree) (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hd : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    {g : Σ n, Graph 3 n} (hg : g ∈ 𝒯.Q) {t : Tracked 3 (m + g.1)}
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) :
    (H.glue x y₁ y₂ (tVar true)).ord ≤ t.g.ord := by
  obtain ⟨-, hSh, hDef⟩ := hcore
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hall : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
  obtain ⟨⟨C', hgN⟩, -, -, -⟩ := hSh.1.1 g (by simp [hg])
  obtain ⟨-, hk2⟩ := hSh.2.2.2.1 g hg
  obtain ⟨hT, hX, hNL, hlab⟩ := hDef.2.1 g hall
  have hPM4 := hDef.2.2.2.2.1 g hg
  have hRg : g.2.RgCheck := hDef.2.2.2.2.2.1 g (by simp [hg])
  obtain ⟨-, -, hε, hε', -⟩ := glue_oDotT_normal m g.1 C C' H x y₁ y₂ g.2.swapSolid hx hy₁ hy₂
    hL hN hd (Graph.swapSolid_Normal hgN) (SubstSPD_swap_otimesNoDot hT)
    (by rw [SubstSPD_swap_dotExcess]; exact hX) (SubstDC_swap_rgCheck hRg)
    (by rw [SubstSPD_swap_labels]; exact hlab) (SubstSPD_swap_noLabDot hNL) t ht
  have e1 := glue_ord 3 m g.1 H x y₁ y₂ g.2.swapSolid
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  have e3 : g.2.swapSolid.ord = g.2.ord := (swapSolid_basic 3 g.1 g.2).2.1
  rw [SubstSPD_tVar_ord] at e2
  have hk2' : (2 : ℤ) ≤ g.2.ord := hk2
  by_cases hε0 : y₁ = y₂ ∧ g.2.swapSolid.PMBlock
  · have := hε hε0
    have h4 := hPM4 ((SubstSPD_swap_pmBlock g.2).1 hε0.2)
    omega
  · have := hε' hε0
    omega

/-- **The leaf invariants of the outputs of the `Q`-expansions of Step 3** ([II, Lemma 6.5 (4)],
[II, Lemma 4.15], [II, Lemma 6.8]): under the hypotheses of `TerminationB_inv_subst`, for a
family `𝔈` of `Q`-expansions with the clauses `QExpFamilyStmt`, every output graph of `𝔈` at the
label atom of an `O_dot` form of a substituted graph of `Q` that is not a `Q`-graph has the leaf
invariants of a run (`TerminationB_Inv n D`): it is plain or of order `> D` in the count of
[II, (2.5)] ((F5)); it has dot excess `0`; without labels it has scaling order `≥ ord G + 1` and
is globally standard, or scaling order `> D`; with `⊕`, `⊖` in one block it has order `≥ ord G + 1`
in the count of [II, (2.5)] ((F4)); it has an internal atom. -/
theorem TerminationB_inv_qexp (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (hF : QExpFamilyStmt 𝔈) (hn : 3 ≤ n)
    (hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) (hL : H.LabelFree)
    (hN : (H.glue x y₁ y₂ (tVar true)).Normal C) (hd : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (ho1 : 4 ≤ (H.glue x y₁ y₂ (tVar true)).ord) (ho2 : (H.glue x y₁ y₂ (tVar true)).ord ≤ n)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hT : (H.glue x y₁ y₂ (tVar true)).TensorDiffusive)
    (hgs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hnr : ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2})
    (hM : (H.glue x y₁ y₂ (tVar true)).MISLocStdB)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (hPG : (H.glue x y₁ y₂ (tVar true)).Plain) :
    ∀ g ∈ 𝒯.Q, ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), ∀ x' : Fin t.nOut,
      t.g.IsQFormAt (.inr x') → ¬ t.g.IsQGraph → ∀ s ∈ 𝔈 D t.nOut x' t.g,
        TerminationB_Inv n D s.g := by
  intro g hg t ht x' hQF hnQ s hs
  have hnD : n ≤ D := by omega
  obtain ⟨-, hrow⟩ := GlobalGoodB_row4 n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2 hI hT hgs
    hnr hM hst hPG g hg
  obtain ⟨⟨C', hC'⟩, hd', htP, htI, -, hout⟩ := hrow t ht
  have hqe := (hF.1 D t.nOut x' t.g ⟨C', hC'⟩ hQF htP).2
  have hmap := hF.2.2.2.2.2 D t.nOut x' t.g ⟨C', hC'⟩ hQF htP hnQ htI
  obtain ⟨hdex, hcls⟩ := hout x' _ hQF hnQ hqe hmap s hs
  have hp : s.g.paperOrd = s.g.ord := by unfold Graph.paperOrd; rw [hdex]; ring
  have htord := TerminationB_rowQ_ord hcore hL hN hd hst hg ht
  have hpt : t.g.paperOrd = t.g.ord := TerminationB_paperOrd_of_dotFree hd'
  have hlf : s.g.LabelFree → (gsPM' s.g ∧ (H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ s.g.ord) ∨
      (D : ℤ) < s.g.ord := by
    intro hL'
    rcases hcls with ⟨-, h1, h2⟩ | ⟨hQ, -⟩ | ⟨h1, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd hQ (Termination_not_qGraph hL')
    · exact Or.inr h1
  refine ⟨?_, fun hL' => ?_, fun hL' ho => ?_, fun hL' _ ho => ?_, fun hP => ?_, fun h0 => ?_⟩
  · by_cases hP : s.g.Plain
    · exact Or.inl hP
    · exact Or.inr (hF.2.2.2.2.1 D t.nOut x' t.g ⟨C', hC'⟩ hQF htP s hs hP).2.2.2
  · rw [hp]
    rcases hlf hL' with ⟨-, h⟩ | h <;> omega
  · rw [hp] at ho
    rcases hlf hL' with ⟨h, -⟩ | h
    · exact h
    · omega
  · rw [hp] at ho
    rcases hlf hL' with ⟨h, -⟩ | h
    · exact h
    · omega
  · have h4 := hF.2.2.2.1 D t.nOut x' t.g ⟨C', hC'⟩ hQF htP htI
      (TerminationB_dotFree_pm hd').1 s hs hP
    rw [hpt] at h4
    exact ⟨by omega, fun _ => by omega⟩
  · exfalso
    obtain ⟨⟨C'', hout'⟩, -⟩ := hqe
    obtain ⟨⟨⟨-, -, -, -, hx, -, -⟩, -⟩, -⟩ := hout' s hs
    rcases hfx : s.f (.inr x') with a | j
    · rw [hfx] at hx; cases hx
    · exact (Fin.cast h0 j).elim0

end InvSubst

/-! ## The order of the outputs of Step 1 with `⊕`, `⊖` in one block -/

section LocPM

open private card_cc_le_of_reach dg_cons_dot_adj dg_reach_mono length_filter_le_add MergeSpec.sameBlock_of_map from RBM8D.Graph.Local.StrategyPart1
open private oDotT_normal_self from RBM8D.Graph.Local.Weight

/-- An atom without dotted edge of a list is reachable only from itself. -/
private theorem TerminationB_reach_new {k n : ℕ} {L : List (Comp (Atom k n))}
    {nw : Atom k n → Bool} (hnd : ∀ c ∈ L, c.kind = .dot → nw c.x = false ∧ nw c.y = false)
    {α β : Atom k n} (hα : nw α = true) (hr : (dg L).Reachable α β) : α = β := by
  obtain ⟨w⟩ := hr
  cases w with
  | nil => rfl
  | cons hadj _ =>
    obtain ⟨-, c, hc, hk, hxy⟩ := dg_adj.1 hadj
    obtain ⟨h1, h2⟩ := hnd c hc hk
    rcases hxy with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · rw [h1] at hα; cases hα
    · rw [h2] at hα; cases hα

open Classical in
/-- The bound on the solid edges turned into weights by `O_merge` after `dotChoice`, relative to a
list `L` of components whose dotted edges avoid the new atoms and whose blocks lie in the blocks of
the term: at most `s` plus twice the number of blocks of `L` joined by the term. -/
private theorem TerminationB_conv {k n : ℕ} {h : Graph k n} (hd : DotIn h) {s : ℕ}
    {nw : Atom k n → Bool} (hn : DotNew h s nw) {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n} (hm : (h.dotChoice h.splitPairs A).mergeT = some t)
    (L : List (Comp (Atom k n)))
    (hnd : ∀ c ∈ L, c.kind = .dot → nw c.x = false ∧ nw c.y = false)
    (hGH : ∀ a b, (dg L).Reachable a b →
      (dg (h.dotChoice h.splitPairs A).comps).Reachable a b) :
    (convN (h.dotChoice h.splitPairs A) : ℤ) ≤
      s + 2 * ((ccN L : ℤ) - ccN (h.dotChoice h.splitPairs A).comps) := by
  set dc := h.dotChoice h.splitPairs A with hdc
  have hle := convN_le hm
  rw [← hdc] at hle
  have hJ : ccN dc.comps ≤ ccN L := card_cc_le_of_reach hGH
  rcases Nat.lt_or_ge (ccN dc.comps + 1) (ccN L) with hJ2 | hJ1
  · have h4 : (h.comps.filter fun c => unpB h c &&
        decide ((dg dc.comps).Reachable c.x c.y)).length ≤ 4 :=
      (length_filter_mono _ _ _ fun c _ hc => by
        simp only [Bool.and_eq_true] at hc; exact hc.1).trans hn.four
    omega
  rcases Nat.lt_or_ge (ccN dc.comps) (ccN L) with hJ1' | hJ0
  · have hc1 : ccN L = ccN dc.comps + 1 := by omega
    obtain ⟨a, b, -, -, hab⟩ := reach_of_card_cc_succ hGH hc1
    by_cases hnab : nw a = true ∨ nw b = true
    · set α₀ := if nw a = true then a else b with hα₀
      have hα₀n : nw α₀ = true := by
        rw [hα₀]
        split_ifs with h1
        · exact h1
        · exact hnab.resolve_left h1
      have hsplit := length_filter_le_add h.comps
        (fun c => unpB h c && decide ((dg dc.comps).Reachable c.x c.y))
        (fun c => unpB h c && !nw c.x && !nw c.y)
        (fun c => unpB h c && (c.x == α₀ || c.y == α₀)) (by
          intro c hc hP
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
          obtain ⟨hu, hr⟩ := hP
          by_cases hold : nw c.x = false ∧ nw c.y = false
          · left
            simp [hu, hold.1, hold.2]
          right
          simp only [Bool.and_eq_true, hu, true_and, Bool.or_eq_true, beq_iff_eq]
          have hloop := hd.noLoop c hc (by simp only [unpB, Bool.and_eq_true] at hu; exact hu.1)
          have hnew : nw c.x = true ∨ nw c.y = true := by
            by_contra hh
            push Not at hh
            exact hold ⟨by simpa using hh.1, by simpa using hh.2⟩
          rcases hab c.x c.y hr with hr' | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
          · exfalso
            rcases hnew with hx | hy
            · exact hloop (TerminationB_reach_new hnd hx hr')
            · exact hloop (TerminationB_reach_new hnd hy hr'.symm).symm
          · rcases hnew with hx | hy
            · have := TerminationB_reach_new hnd hx hxa
              rw [hα₀]
              split_ifs with h1
              · exact Or.inl this
              · exact absurd (this ▸ hx) h1
            · have hyb' := TerminationB_reach_new hnd hy hyb
              rw [hα₀]
              split_ifs with h1
              · exact Or.inl (TerminationB_reach_new hnd h1 hxa.symm).symm
              · exact Or.inr hyb'
          · rcases hnew with hx | hy
            · have hxb' := TerminationB_reach_new hnd hx hxb
              rw [hα₀]
              split_ifs with h1
              · exact Or.inr (TerminationB_reach_new hnd h1 hya.symm).symm
              · exact Or.inl hxb'
            · have := TerminationB_reach_new hnd hy hya
              rw [hα₀]
              split_ifs with h1
              · exact Or.inr this
              · exact absurd (this ▸ hy) h1)
      have h2 := hn.two α₀ hα₀n
      have h3 := hn.old
      omega
    · push Not at hnab
      have hsub := length_filter_mono h.comps
        (fun c => unpB h c && decide ((dg dc.comps).Reachable c.x c.y))
        (fun c => unpB h c && !nw c.x && !nw c.y) (by
          intro c hc hP
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
          obtain ⟨hu, hr⟩ := hP
          have hloop := hd.noLoop c hc (by simp only [unpB, Bool.and_eq_true] at hu; exact hu.1)
          have hna : nw a = false := by simpa using hnab.1
          have hnb : nw b = false := by simpa using hnab.2
          have key : ∀ w, nw w = true → (dg L).Reachable w a ∨
              (dg L).Reachable w b → False := by
            intro w hw hr'
            rcases hr' with hr' | hr'
            · rw [TerminationB_reach_new hnd hw hr'] at hw; rw [hna] at hw; cases hw
            · rw [TerminationB_reach_new hnd hw hr'] at hw; rw [hnb] at hw; cases hw
          have hx : nw c.x = false := by
            by_contra hx
            simp only [Bool.not_eq_false] at hx
            rcases hab c.x c.y hr with hr' | ⟨hxa, -⟩ | ⟨hxb, -⟩
            · exact hloop (TerminationB_reach_new hnd hx hr')
            · exact key _ hx (Or.inl hxa)
            · exact key _ hx (Or.inr hxb)
          have hy : nw c.y = false := by
            by_contra hy
            simp only [Bool.not_eq_false] at hy
            rcases hab c.x c.y hr with hr' | ⟨-, hyb⟩ | ⟨-, hya⟩
            · exact hloop (TerminationB_reach_new hnd hy hr'.symm).symm
            · exact key _ hy (Or.inr hyb)
            · exact key _ hy (Or.inl hya)
          simp [hu, hx, hy])
      have h3 := hn.old
      omega
  · have hc0 : ccN L = ccN dc.comps := le_antisymm hJ0 hJ
    have hr0 := reach_of_card_cc_eq hGH hc0
    have hsub := length_filter_mono h.comps
      (fun c => unpB h c && decide ((dg dc.comps).Reachable c.x c.y))
      (fun c => unpB h c && !nw c.x && !nw c.y) (by
        intro c hc hP
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
        obtain ⟨hu, hr⟩ := hP
        have hr' := hr0 _ _ hr
        have hloop := hd.noLoop c hc (by simp only [unpB, Bool.and_eq_true] at hu; exact hu.1)
        have hx : nw c.x = false := by
          by_contra hx
          exact hloop (TerminationB_reach_new hnd (by simpa using hx) hr')
        have hy : nw c.y = false := by
          by_contra hy
          exact hloop (TerminationB_reach_new hnd (by simpa using hy) hr'.symm).symm
        simp [hu, hx, hy])
    have h3 := hn.old
    omega

/-- `O_dot` at a term without dotted edges whose new atoms are internal: an output in which `⊕`
and `⊖` lie in one block has scaling order minus twice the dot excess at least that of the term,
minus the order surplus `s`, plus `2`. -/
private theorem TerminationB_dot_pm {n : ℕ} {h : Graph 3 n} (hd : DotIn h) {s : ℕ}
    {nw : Atom 3 n → Bool} (hn : DotNew h s nw) (hnw : nw (.inl 1) = false ∧ nw (.inl 2) = false)
    (hdf : h.DotFree) {t : Tracked 3 n} (ht : t ∈ oDotT h) (hpm : t.g.PMBlock) :
    h.obl - s + 2 ≤ t.g.obl := by
  have hnr : ¬ (dg h.comps).Reachable (.inl 1) (.inl 2) := fun hr =>
    (TerminationB_dotFree_pm hdf).1 ((Graph.pmBlock_iff_sameBlock h).2 hr)
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact absurd hpm (TerminationB_dotFree_pm hdf).1
  set dc := h.dotChoice h.splitPairs A with hdc
  have hs := mergeT_spec hm
  have hr : (dg dc.comps).Reachable (.inl 1) (.inl 2) := by
    have h1 := (Graph.pmBlock_iff_sameBlock t.g).1 hpm
    rw [← hs.f_inl 1, ← hs.f_inl 2] at h1
    exact MergeSpec.sameBlock_of_map hs h1
  have hcc : ccN h.comps = ccN (mkC .dot (.inl 1 : Atom 3 n) (.inl 2) :: h.comps) + 1 :=
    card_cc_add_edge (dg_cons_dot_adj h.comps rfl) hnr
  have hconv := TerminationB_conv hd hn hm (mkC .dot (.inl 1 : Atom 3 n) (.inl 2) :: h.comps)
    (fun c hc hk => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hnw
      · exact hn.noDot c hc (Or.inl hk))
    (fun a b hab => by
      obtain ⟨w⟩ := hab
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons hadj _ ih =>
        refine SimpleGraph.Reachable.trans ?_ ih
        rcases (dg_cons_dot_adj h.comps rfl _ _).1 hadj with hadj | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact dc_reach h h.splitPairs A hadj.reachable
        · exact hr
        · exact hr.symm)
  rw [hs.obl_eq, dc_obl]
  push_cast [hcc] at hconv ⊢
  linarith

/-- A term of a local operation at a graph without dotted edges, followed by `O_dot`: an output
in which `⊕` and `⊖` lie in one block has scaling order minus twice the dot excess at least that
of the input plus `2`. -/
private theorem TerminationB_termOK_pm {C n : ℕ} {Γ : Graph 3 n} {x : Atom 3 n}
    {T : Tracked 3 n} (hT : TermOK Γ x T) (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree)
    (hX : Γ.XdotApart) (hdf : Γ.DotFree) {t : Tracked 3 T.nOut} (ht : t ∈ oDotT T.g)
    (hpm : t.g.PMBlock) : Γ.obl + 2 ≤ t.g.obl := by
  obtain ⟨j, R, N, lab, g, s, rfl, hS, hNo, -, hs, two, old, four, zero, -⟩ := hT
  have hNd : ∀ c ∈ N, c.kind ≠ .dot ∧ c.kind ≠ .xdot :=
    fun c hc => ⟨(hNo c hc).1.ne_dot, (hNo c hc).1.ne_xdot'⟩
  have hexc : g.dotExcess = Γ.dotExcess := hS.dotExcess fun c hc => (hNd c hc).1
  have hord := hS.ord
  have hobl : g.obl = Γ.obl + s := by
    simp only [Graph.obl, hexc]
    linarith
  have hgdf : g.DotFree := by
    intro c hc
    rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
    · rw [labF_kind]; exact hdf c₀ hc₀
    · rw [labF_kind]; exact (hNd c₁ hc₁).1
  have := TerminationB_dot_pm (hS.dotIn hN hP hL hX hNo) (hS.dotNew hN hNd two old four zero)
    ⟨rfl, rfl⟩ hgdf ht hpm
  linarith

/-- The outputs of `O_dot` over terms of a local operation at a graph without dotted edges. -/
private theorem TerminationB_bind_pm {C n : ℕ} {Γ : Graph 3 n} {x : Atom 3 n}
    {E : TExpansion 3 n} (hE : ∀ T ∈ E, TermOK Γ x T) (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hX : Γ.XdotApart) (hdf : Γ.DotFree) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), t.g.PMBlock → Γ.obl + 2 ≤ t.g.obl := by
  intro t ht hpm
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨T, hT, s, hs, rfl⟩ := ht
  exact TerminationB_termOK_pm (hE T hT) hN hP hL hX hdf hs hpm

/-- `O^{(y),1}_weight` keeps the dotted edges and does not lower the scaling order minus twice the
dot excess. -/
private theorem TerminationB_o1 {n : ℕ} {y : Atom 3 n} {g h' : Graph 3 n} (hP : g.Plain)
    (hK : g.RandomFirstInt) {R : List (Comp (Atom 3 n))} {N : List (Comp (Atom 3 (n + 0)))}
    (hSch : Sch g 0 R N none h') (hNl : N.length ≤ R.length)
    (hNR : ∀ c ∈ N, ∃ c₀ ∈ R, c = c₀.toLight) (hR : ∀ c ∈ R, IsRegU y c) :
    (∀ c ∈ h'.comps, c.kind = .dot → c ∈ g.comps) ∧ g.obl ≤ h'.obl := by
  obtain ⟨-, f2, -⟩ := o1_facts hP hK hSch hNl hNR hR
  refine ⟨fun c hc hk => ?_, by rw [f2]; omega⟩
  rcases hSch.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, he⟩
  · simpa [labF_none, Comp.map_liftA_zero] using hc₀
  · rw [he, labF_none] at hk
    obtain ⟨c₀, hc₀, rfl⟩ := hNR c₁ hc₁
    obtain ⟨ch, hk₀⟩ := (hR c₀ hc₀).1
    simp [Comp.toLight, hk₀] at hk

/-- `⊕` and `⊖` in one block of a graph whose dotted edges are dotted edges of `g`. -/
private theorem TerminationB_pm_mono {n : ℕ} {g g' : Graph 3 n}
    (h : ∀ c ∈ g'.comps, c.kind = .dot → c ∈ g.comps) (hpm : g'.PMBlock) : g.PMBlock :=
  (Graph.pmBlock_iff_sameBlock g).2 (dg_reach_mono h ((Graph.pmBlock_iff_sameBlock g').1 hpm))

/-- The weight expansion `O_weight` at a graph without dotted edges: an output in which `⊕` and
`⊖` lie in one block has scaling order minus twice the dot excess at least that of the input plus
`2`. -/
private theorem TerminationB_weight_pm {C n : ℕ} {Γ : Graph 3 n} {x : Atom 3 n}
    (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt)
    (hX : Γ.XdotApart) (hx : x.isRight = true) (hdf : Γ.DotFree) :
    ∀ t ∈ oWeightT x Γ, t.g.PMBlock → Γ.obl + 2 ≤ t.g.obl := by
  intro t ht hpm
  unfold oWeightT at ht
  split_ifs at ht with hany
  swap
  · rw [List.mem_singleton] at ht
    subst ht
    exact absurd hpm (TerminationB_dotFree_pm hdf).1
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨u₃, ⟨u₂, ⟨t₁, ht₁, t₂, ht₂, rfl⟩, t₃, ht₃, rfl⟩, t₄, ht₄, rfl⟩ := ht
  obtain ⟨R, N, g₁, rfl, hSch, hNl, hNR, hR, -⟩ := oWeight1T_spec ht₁
  obtain ⟨-, f2, -, -, -, f6, f7, f8, f9, -, f11⟩ := o1_facts hP hK hSch hNl hNR hR
  have hN₁ := f11 C hN
  simp only [Function.comp_id] at ht₂ ht₃ ht₄ hpm ⊢
  obtain ⟨hd₁, hg₁⟩ := TerminationB_o1 hP hK hSch hNl hNR hR
  have hdf₁ : g₁.DotFree := fun c hc hk => hdf c (hd₁ c hc hk) hk
  by_cases hl : HasLight g₁ x
  · have hT := oWeight2T_terms hN₁ f6 (f9 hL) f7 hx hl t₂ ht₂
    have hst := hT.step hN₁ f6 (f9 hL) f7 (f8 hX) ht₃
    obtain ⟨R', N', h', rfl, hSch', hNl', hNR', hR', -⟩ := oWeight1T_spec ht₄
    obtain ⟨hd₄, ho₄⟩ := TerminationB_o1 hst.2.2.2.2.2.1 hst.2.2.2.2.1 hSch' hNl' hNR' hR'
    have := TerminationB_termOK_pm hT hN₁ f6 (f9 hL) (f8 hX) hdf₁ ht₃
      (TerminationB_pm_mono hd₄ hpm)
    change Γ.obl + 2 ≤ h'.obl
    linarith
  · change t₂ ∈ oWeight2T x g₁ at ht₂
    rw [oWeight2T_self hl, List.mem_singleton] at ht₂
    subst ht₂
    have ht₃' : t₃ ∈ oDotT g₁ := ht₃
    rw [oDotT_normal_self hN₁] at ht₃'
    obtain rfl := List.mem_singleton.1 ht₃'
    obtain ⟨R', N', h', rfl, hSch', hNl', hNR', hR', -⟩ := oWeight1T_spec ht₄
    obtain ⟨hd₄, -⟩ := TerminationB_o1 f6 f7 hSch' hNl' hNR' hR'
    exact absurd (TerminationB_pm_mono hd₄ hpm) (TerminationB_dotFree_pm hdf₁).1

/-- **The outputs of Step 1 with `⊕`, `⊖` in one block** ([II, Strategy 6.6, Step 1],
[II, Def 6.3], [II, Lemma 6.8]; [I, Def 3.2]): for a local expansion `localOp' o` that applies at
an internal atom `x` (`Graph.LocAdm`) of a normal regular, plain graph `Γ` without labels, with
the invariant of a run and the leaf invariants of a run, no `×`-dotted edge inside a block, of
scaling order `≤ D` and not stopped, every output graph in which `⊕` and `⊖` lie in one dotted
block has order at least `ord Γ + 2 ≥ 5` in the count of [II, (2.5)]. The input has no dotted
edge; in `O_dot` ([I, Def 3.2]) the solid edges turned into weights are counted against the
blocks joined, and the block of `⊕` and `⊖` joins two blocks of the input without a new atom. -/
theorem TerminationB_loc_pm {n₀ N D C : ℕ} {Γ : Graph 3 n₀} {o : Fin 5} {x : Fin n₀}
    (hI : Γ.InvRun D) (hv : TerminationB_Inv N D Γ) (hS : ¬ Γ.StopsB N)
    (hD : ¬ (D : ℤ) < Γ.ord) (hN : Γ.Normal C) (hL : Γ.LabelFree) (hP : Γ.Plain)
    (hX : Γ.XdotApart) (hA : Γ.LocAdm o (.inr x)) :
    ∀ t ∈ localOp' o (.inr x) Γ, t.g.PMBlock →
      Γ.paperOrd + 2 ≤ t.g.paperOrd ∧ 5 ≤ t.g.paperOrd := by
  intro t ht hpm
  have hdf := locInput_dotFree N D n₀ C Γ hI hD hL hN hP hS
  obtain ⟨hB, -⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
  have hK := Termination_randomFirstInt hB.2.1 hdf
  have hx : (Sum.inr x : Atom 3 n₀).isRight = true := rfl
  have h3 := hv.2.1 hL
  have hb : Γ.obl + 2 ≤ t.g.obl := by
    rcases hA with ⟨rfl, -⟩ | ⟨rfl, hw, hdeg, hM⟩ | ⟨ho, hw, y, y', hin⟩ |
        ⟨rfl, hw, hM, y, y', hin⟩
    · exact TerminationB_weight_pm hN hP hL hK hX hx hdf t ht hpm
    · obtain ⟨E, hE, hT, -⟩ := oMultiET_rep ⟨hN, hP, hL, hK, hx, hw, hM⟩ hdeg
      change t ∈ oMultiET _ Γ at ht
      rw [hE] at ht
      exact TerminationB_bind_pm hT hN hP hL hX hdf t ht hpm
    · rcases ho with rfl | rfl
      · obtain ⟨E, hE, hT, -⟩ := oGGT_rep hN hP hL hK hx hw hin
        change t ∈ oGGT _ Γ at ht
        rw [hE] at ht
        exact TerminationB_bind_pm hT hN hP hL hX hdf t ht hpm
      · obtain ⟨E, hE, hT, -⟩ := oGGTT_rep hN hP hL hK hx hw hin
        change t ∈ oGGTT _ Γ at ht
        rw [hE] at ht
        exact TerminationB_bind_pm hT hN hP hL hX hdf t ht hpm
    · have hdeg := hin.1
      have hE : oGGbarT (.inr x) Γ = oMultiET (.inr x) Γ := by
        rcases ggbar_input hN hin with ⟨i₁, j, e₁, ej, hpt, hmt, hpf, hmf, -, -⟩ |
            ⟨i₁, j, e₁, ej, hpt, hmt, hpf, hmf, -, -⟩ <;>
          simp [oGGbarT, hdeg, hpt, hmt, hpf, hmf]
      obtain ⟨E, hE', hT, -⟩ := oMultiET_rep ⟨hN, hP, hL, hK, hx, hw, hM⟩ (by omega)
      change t ∈ oGGbarT _ Γ at ht
      rw [hE, hE'] at ht
      exact TerminationB_bind_pm hT hN hP hL hX hdf t ht hpm
  rw [Graph.paperOrd_eq_obl] at h3 ⊢
  rw [Graph.paperOrd_eq_obl]
  omega

end LocPM

/-! ## The leaf invariants along Step 1 -/

section InvLoc

variable {n₀ : ℕ}

/-- **The outputs of Step 1** ([II, Strategy 6.6, Step 1], [I, Lemmas 3.9, 3.13, 3.16, 3.19],
[II, Lemmas 4.10, 6.4, 6.8]): a local expansion `localOp' o` that applies at an internal atom `x`
(`Graph.LocAdm`, in the form of `Graph.LocSide`) of a normal regular, plain, globally standard
graph `Γ` without labels, with the invariant of a run and the leaf invariants of a run, no
`×`-dotted edge inside a block, of scaling order `≤ D` and not stopped, gives output graphs `t`
that are normal regular, doubly connected if `Γ` is, with the clauses `StepOut` of one step, and
with the leaf invariants of a run: `t` is plain, of order `≥ ord Γ ≥ 3` in the count of
[II, (2.5)], globally standard ([II, Lemma 6.4 (1)]), of order `≥ 5` if `⊕`, `⊖` lie in one
dotted block (`TerminationB_loc_pm`), and has an internal atom. -/
theorem TerminationB_inv_loc {N D C : ℕ} {Γ : Graph 3 n₀} {o : Fin 5} {x : Fin n₀}
    (hI : Γ.InvRun D) (hv : TerminationB_Inv N D Γ) (hS : ¬ Γ.StopsB N)
    (hD : ¬ (D : ℤ) < Γ.ord) (hN : Γ.Normal C) (hL : Γ.LabelFree) (hP : Γ.Plain)
    (hgs : gsPM' Γ) (hX : Γ.XdotApart) (hA : Γ.LocAdm o (.inr x)) (hside : Γ.LocSide o (.inr x)) :
    ∀ t ∈ localOp' o (.inr x) Γ, (∃ C', t.g.Normal C') ∧
      (Γ.DoublyConnected → t.g.DoublyConnected) ∧ StepOut Γ t ∧ TerminationB_Inv N D t.g := by
  intro t ht
  have hpm := TerminationB_loc_pm hI hv hS hD hN hL hP hX hA t ht
  have hdf := locInput_dotFree N D n₀ C Γ hI hD hL hN hP hS
  obtain ⟨hB, -⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
  have hK := Termination_randomFirstInt hB.2.1 hdf
  have hx : (Sum.inr x : Atom 3 n₀).isRight = true := rfl
  have hstep : StepOut Γ t := by
    rcases hA with ⟨rfl, hw⟩ | ⟨rfl, hw, hdeg, hM⟩ | ⟨ho, hw, y, y', hin⟩ |
        ⟨rfl, hw, hM, y, y', hin⟩
    · exact oWeightT_step hN hP hL hK hX hx hw t ht
    · exact oMultiET_step ⟨hN, hP, hL, hK, hx, hw, hM⟩ hX hdeg t ht
    · rcases ho with rfl | rfl
      · exact oGGT_step hN hP hL hK hX hx hw hin t ht
      · exact oGGTT_step hN hP hL hK hX hx hw hin t ht
    · exact oGGbarT_step ⟨hN, hP, hL, hK, hx, hw, hM⟩ hX hin t ht
  have hPt : t.g.Plain := hstep.2.2.2.2.2.1
  have hnorm : ∃ C', t.g.Normal C' := by
    match o, ht with
    | 0, ht => exact ⟨_, (oWeight_canonical 3 n₀ C _ Γ hx hN hP t ht).1⟩
    | 1, ht => exact ⟨_, (oMultiE_canonical 3 n₀ C _ Γ hx hN hP t ht).1⟩
    | 2, ht => exact ⟨_, (oGG_canonical 3 n₀ C _ Γ hx hN hP t ht).1⟩
    | 3, ht => exact ⟨_, (oGGbar_canonical 3 n₀ C _ Γ hx hN hP t ht).1⟩
    | 4, ht => exact ⟨_, oGGTT_normal hN hP hx ht hPt⟩
  have hdc : Γ.DoublyConnected → t.g.DoublyConnected := by
    intro hdc
    have h := localDoublyConnected 3 n₀ C (.inr x) Γ hdc
    match o, ht, hside with
    | 0, ht, _ => exact h.2.1 hx hN t ht
    | 1, ht, _ => exact h.2.2.1 hx hN t ht
    | 2, ht, hs =>
      exact h.2.2.2.1 hx hN (fun c hc hk hcx => hs.1 rfl hx c hc (by rw [hk]; rfl) hcx) t ht
    | 3, ht, _ => exact h.2.2.2.2 hx hN t ht
    | 4, ht, hs =>
      exact localDoublyConnectedT 3 n₀ C (.inr x) Γ hdc hx hN
        (fun c hc hk hcy => hs.2 rfl hx c hc (by rw [hk]; rfl) hcy) t ht
  have hgst : gsPM' t.g :=
    ((localGSB n₀ C x Γ hgs hB.2.2.1 hB.2.2.2.1 hB.2.1).2 hN hL hP o hside t ht).1
  have hobl : Γ.paperOrd ≤ t.g.paperOrd := by
    rw [Graph.paperOrd_eq_obl, Graph.paperOrd_eq_obl]; exact hstep.2.1
  have h3 := hv.2.1 hL
  have hnO : t.nOut ≠ 0 := by
    obtain ⟨-, hfx, -⟩ := Local_localOp_good ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1⟩ hL x o hside t ht
    intro h0
    rcases hf : t.f (.inr x) with a | j
    · rw [hf] at hfx; cases hfx
    · exact (Fin.cast h0 j).elim0
  refine ⟨hnorm, hdc, hstep, Or.inl hPt, fun _ => by omega, fun _ _ => hgst,
    fun _ _ _ => hgst, fun h => ⟨by have := (hpm h).2; omega, fun _ => (hpm h).2⟩,
    fun h => absurd h hnO⟩

end InvLoc

/-! ## The clause `Graph.RgCheck` and the inputs of the run -/

section Start

/-- **The clause `Graph.RgCheck` of the output graphs** ([II, Def 6.3], the graphs of `Err`): a
graph without internal atom, or with the clause on the external atoms and only diffusive edges at
`⊗`, has a waved, diffusive or dotted edge from an internal atom to an external atom. With an
internal atom, `⊗` lies in no block with an internal atom and carries a diffusive edge to an
internal atom or to an external atom whose block has an internal atom; in the second case the path
of dotted edges of that block has a dotted edge from an external atom to an internal atom. -/
theorem TerminationB_rgCheck {n₀ : ℕ} (Γ : Graph 3 n₀)
    (h : n₀ ≠ 0 → Γ.ExtClause ∧ Γ.TensorDiffusive) : Γ.RgCheck := by
  by_cases h0 : n₀ = 0
  · exact Or.inl h0
  · obtain ⟨hE, hT⟩ := h h0
    exact GlobalGoodRows_rgCheck Γ hE hT

/-- **The inputs of the run have the leaf invariants of a run**: the graphs of `A` and `Q` of the
second order `T`-expansion (`h2Rec`, [I, (2.9)]) satisfy `TerminationB_Inv N D` for every error
order `D > 2`: they are plain, of dot excess `0`, the graphs of `A` have one internal molecule and
scaling order `≥ 3`, and the clauses of [II, Def 6.3] (`TRec.Def63`) give the orders when `⊕`,
`⊖` lie in one block and the diffusive edge, the label and the profile at `⊖` of the graphs
without internal atom. -/
theorem TerminationB_inv_h2 (N D : ℕ) (hD : 2 < D) :
    ∀ g ∈ h2Rec.A ++ h2Rec.Q, TerminationB_Inv N D g.2 := by
  intro g hg
  obtain ⟨-, -, -, hSh, hDef⟩ := h2Rec_struct (fun _ => []) D hD
  have hall : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q ++ h2Rec.Err := by
    simp only [List.mem_append] at hg ⊢; tauto
  have hRAQ : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q := by
    simp only [List.mem_append] at hg ⊢; tauto
  obtain ⟨-, hX, -, -⟩ := hDef.2.1 g hall
  have hp : g.2.paperOrd = g.2.ord := by unfold Graph.paperOrd; rw [hX]; ring
  have hmol : ∀ g ∈ h2Rec.A, ∀ b c : Fin g.1, g.2.SameMol (.inr b) (.inr c) := by
    decide +kernel
  have hlf : g.2.LabelFree → g ∈ h2Rec.A := by
    intro hL
    rcases List.mem_append.1 hg with h | h
    · exact h
    · exact absurd (hSh.2.2.2.1 g h).1 (Termination_not_qGraph hL)
  refine ⟨Or.inl (TRec.plain_of_def63 hDef g hRAQ), fun hL => ?_,
    fun hL _ => gsPM'_of_oneMol 3 g.1 g.2 (hmol g (hlf hL)),
    fun hL _ _ => gsPM'_of_oneMol 3 g.1 g.2 (hmol g (hlf hL)), fun hP => ?_, fun h0 => ?_⟩
  · rw [hp]
    have := (hSh.2.2.1 g (hlf hL)).2
    push_cast at this
    omega
  · rw [hp]
    rcases List.mem_append.1 hg with h | h
    · have := hDef.2.2.2.1 g (by simp [h]) hP
      exact ⟨by omega, fun _ => this⟩
    · have := hDef.2.2.2.2.1 g h hP
      exact ⟨this, fun hL => absurd (hSh.2.2.2.1 g h).1 (Termination_not_qGraph hL)⟩
  · rcases List.mem_append.1 hg with h | h
    · rcases (hDef.1.2.1 g h).2 with ⟨-, hR⟩ | ⟨hE, -⟩
      · exact ⟨hR, fun c hc u hu => (by rw [(hSh.2.2.1 g h).1 c hc] at hu; cases hu),
          TRec.minusProfile_of_def63 hDef g hg h0⟩
      · exact absurd h0 (Strategy_extClause_ne_zero hE)
    · refine ⟨?_, TRec.qLabelAtPlus_of_def63 hDef g h h0, TRec.minusProfile_of_def63 hDef g hg h0⟩
      rcases (hDef.1.2.2 g h).2.2 with ⟨-, hR⟩ | ⟨hE, -⟩
      · exact hR
      · exact absurd h0 (Strategy_extClause_ne_zero hE)

end Start

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end Instances

end RBM8D.Graphs
