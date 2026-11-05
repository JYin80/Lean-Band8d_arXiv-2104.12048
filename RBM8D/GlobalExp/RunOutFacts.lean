import RBM8D.GlobalExp.RunOtimes
import RBM8D.GlobalExp.TEqSigma
import Batteries.Tactic.OpenPrivate

/-!
# The kinds, the internal atoms and the scaling orders of the output graphs of the run

Four facts on the output graphs of the run `RunCompare.run 𝔈 n D 𝒯` of [II, Strategy 6.6] driven
by the selector `TerminationC_sel` ([II, Lemma 6.8]) from the graphs of `A` and `Q` of the second
order `T`-expansion ([I, (2.8)–(2.9)]), for a family `𝔈` of `Q`-expansions of [II, Lemma 4.15]
with `QExpFamilyStmt`, a cutoff order `n ≥ 3` and an `(n - 1)`-th order `T`-expansion `𝒯` with
error order `D` (`RunCompare.run_outFacts`):

* no output graph carries a `(G_xx)⁻¹` weight: the inputs are plain, Step 1 gives plain graphs,
  `O_dot` ([II, Def 4.2]) keeps the kinds or turns solid edges into weights and adds dotted and
  `×`-dotted edges, the substitution of Steps 2–3 inserts graphs of the kinds of [II, Def 3.2],
  and a `Q`-expansion of Step 3 gives plain or clean graphs ((F5) of `QExpFamilyStmt`; the
  `(G_xx)⁻¹` weights of (4.17) are Taylor-expanded by (4.20) in [II, Lemma 4.11]);
* an output graph without internal atom is a graph of `Q` of the second order `T`-expansion: the
  graphs of `Q` are outputs, the graphs of `A` have internal atoms, and every step keeps an
  internal atom (the atom maps of the local expansions, of `O_dot` and of the `Q`-expansions send
  internal atoms to internal atoms, and the host `H` of Steps 2–3 has the internal atom `x`);
* every output graph has scaling order `≥ 2`, and the output graphs of scaling order `≤ 2` are the
  graphs of order `≤ 2` of `Q`, with multiplicity: the graphs of `A` have order `≥ 3`, which every
  step keeps ([II, Lemma 6.5]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private RunCompare_I RunCompare_I_inputs RunCompare_Hi RunCompare_HiN RunCompare_hi_step
  RunCompare_high RunCompare_flat RunCompare_o RunCompare_single_out RunCompare_I_step
  RunCompare_adm RunCompare_hi_normal RunCompare_q0_out RunCompare_def63_leaf
  from RBM8D.GlobalExp.RunCompare
open private RunOtimes_AtomOK RunOtimes_localOp_otimes RunOtimes_oDotT RunOtimes_q_out
  from RBM8D.GlobalExp.RunOtimes
open private Local_merge_mem Local_mergeComp_some Local_dotChoice_comps Local_added
  from RBM8D.GlobalExp.Local
open private h2Rec_struct from RBM8D.TExp.Second

set_option quotPrecheck false in
local notation "QFam" => ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀

/-! ## No `(G_xx)⁻¹` weight along one step -/

section NoInv

variable {n₀ : ℕ}

/-- No component of the list is a `(G_xx)⁻¹` weight. -/
private def RunOutFacts_NI {V : Type*} (L : List (Comp V)) : Prop :=
  ∀ c ∈ L, ∀ ch, c.kind ≠ .inv ch

private theorem RunOutFacts_ni_plain {Γ : Graph 3 n₀} (h : Γ.Plain) : RunOutFacts_NI Γ.comps :=
  fun c hc => (h c hc).2.1

private theorem RunOutFacts_ni_clean {Γ : Graph 3 n₀} (h : Γ.Clean) : RunOutFacts_NI Γ.comps :=
  fun c hc => (h c hc).2.1

private theorem RunOutFacts_ni_sub {V : Type*} {L L' : List (Comp V)} (h : RunOutFacts_NI L)
    (hs : ∀ c ∈ L', c ∈ L) : RunOutFacts_NI L' :=
  fun c hc => h c (hs c hc)

private theorem RunOutFacts_ni_map {V W : Type*} {L : List (Comp V)} (f : V → W)
    (h : RunOutFacts_NI L) : RunOutFacts_NI (L.map (Comp.map f)) := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  exact h c₀ hc₀

private theorem RunOutFacts_ni_map_inv {V W : Type*} {L : List (Comp V)} (f : V → W)
    (h : RunOutFacts_NI (L.map (Comp.map f))) : RunOutFacts_NI L :=
  fun c hc => h (c.map f) (List.mem_map_of_mem hc)

private theorem RunOutFacts_toWeight {κ : Kind} {ch : Charge} (h : κ.toWeight = .inv ch) :
    κ = .inv ch := by
  cases κ <;> simp_all [Kind.toWeight]

/-- **`O_dot`** ([II, Def 4.2]) creates no `(G_xx)⁻¹` weight: a component of a term is the image
of a component of the graph, with a solid edge between identified atoms turned into a weight, or a
new dotted or `×`-dotted edge. -/
private theorem RunOutFacts_ni_oDot {Γ : Graph 3 n₀} (h : RunOutFacts_NI Γ.comps) :
    ∀ t ∈ oDotT Γ, RunOutFacts_NI t.g.comps := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact h
  intro c' hc' ch hk
  obtain ⟨c, hc, hmc⟩ := Local_merge_mem hm hc'
  have hk' : c.kind = .inv ch := by
    rcases Local_mergeComp_some hmc with ⟨-, -, rfl⟩ | ⟨rfl, -, -⟩
    · exact RunOutFacts_toWeight hk
    · exact hk
  rw [Local_dotChoice_comps] at hc
  rcases List.mem_append.1 hc with hc | hc
  · exact h c (List.mem_filter.1 hc).1 ch hk'
  · unfold Local_added at hc
    obtain ⟨p, -, hpc⟩ := List.mem_filterMap.1 hc
    split_ifs at hpc <;> obtain rfl := Option.some.inj hpc <;> cases hk'

/-- A reordering keeps the kinds of the components. -/
private theorem RunOutFacts_ni_reorder {Γ Γ' : Graph 3 n₀} (h : RunOutFacts_NI Γ.comps)
    (hr : Γ.Reorder Γ') : RunOutFacts_NI Γ'.comps := by
  obtain ⟨-, π, cs, h2, hp⟩ := hr
  have hrel : RunOutFacts_NI (Γ.relabel π).comps := RunOutFacts_ni_map _ h
  have key : ∀ (l l' : List (Comp (Atom 3 n₀))), List.Forall₂ (fun c c' => c' = c ∨
      ((c.kind = .waved .s ∨ c.kind = .dot ∨ c.kind = .xdot) ∧
        c' = { c with x := c.y, y := c.x })) l l' → RunOutFacts_NI l → RunOutFacts_NI l' := by
    intro l l' hl
    induction hl with
    | nil => exact fun _ c hc => absurd hc List.not_mem_nil
    | @cons c c' l l' hcc _ ih =>
      intro hn d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · rcases hcc with rfl | ⟨-, rfl⟩
        · exact hn d List.mem_cons_self
        · exact hn c List.mem_cons_self
      · exact ih (fun e he => hn e (List.mem_cons_of_mem _ he)) d hd
  exact RunOutFacts_ni_sub (key _ _ h2 hrel) fun c hc => hp.symm.subset hc

/-- The graphs of the right side of [II, (4.15)] substituted in Steps 2–3 have no `(G_xx)⁻¹`
weight: `Graph.TKinds`, `Graph.TKindsErr` ([II, Def 3.2]) and plain graphs. -/
private theorem RunOutFacts_ni_tSubst {Sig : ℕ → Expansion 2} {N D : ℕ} {𝒯 : TRec}
    (hT : 𝒯.IsTExpStruct Sig N D) :
    ∀ g ∈ (𝒯.tSubst N).swapSolid, RunOutFacts_NI g.2.comps := by
  obtain ⟨-, -, -, ⟨⟨h1, h2⟩, -⟩, -⟩ := hT
  have hRAQ : ∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q, RunOutFacts_NI g.2.comps := by
    intro g hg c hc ch hk
    have := List.all_eq_true.1 (h1 g hg).2.1 c hc
    unfold Comp.isTKind at this
    rw [hk] at this
    simp at this
  have hErr : ∀ g ∈ 𝒯.Err, RunOutFacts_NI g.2.comps := by
    intro g hg c hc ch hk
    have := List.all_eq_true.1 (h2 g hg).2.1 c hc
    unfold Comp.isTKind at this
    rw [hk] at this
    simp at this
  intro g hg c hc ch hk
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  have hk₀ : c₀.kind = .inv ch := by
    unfold Comp.swapSolid at hk
    split_ifs at hk <;> exact hk
  simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg₀
  rcases hg₀ with (((((h | h) | h) | h) | h) | h) | h
  · exact RunOutFacts_ni_plain (leadSigmaCorr_plain N g₀ (by simp [h])) c₀ hc₀ ch hk₀
  · exact RunOutFacts_ni_plain (leadSigmaCorr_plain N g₀ (by simp [h])) c₀ hc₀ ch hk₀
  · exact hRAQ g₀ (by simp [h]) c₀ hc₀ ch hk₀
  · exact hRAQ g₀ (by simp [h]) c₀ hc₀ ch hk₀
  · exact hRAQ g₀ (by simp [h]) c₀ hc₀ ch hk₀
  · exact hErr g₀ h c₀ hc₀ ch hk₀
  · exact RunOutFacts_ni_plain (leadSigmaCorr_plain N g₀ (by simp [h])) c₀ hc₀ ch hk₀

/-- **One step of the run** at an admissible location of a graph of the domain of the selector
creates no `(G_xx)⁻¹` weight. -/
private theorem RunOutFacts_ni_step {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} {𝔈 : QFam}
    (hF : QExpFamilyStmt 𝔈) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {g : Σ n₀ : ℕ, Graph 3 n₀}
    (h : RunOutFacts_NI g.2.comps) (hD : TerminationC_Dom n D g) {l : TerminationC_Loc g.1}
    (hA : TerminationC_Adm n D 𝔈 g l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, RunOutFacts_NI s.2.comps := by
  obtain ⟨n₀, Γ⟩ := g
  intro s hs
  cases l with
  | loc o x =>
    obtain ⟨hS, hDo, ⟨C, hN⟩, hL, hP, hgs, -, hside, hLA, hX⟩ := hA
    have hR : TerminationC_RI n D ⟨n₀, Γ⟩ := hD.resolve_left fun h => h ⟨C, hN⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    obtain ⟨-, -, hst, -⟩ :=
      TerminationB_inv_loc hR.1 hR.2.1 hS hDo hN hL hP hgs hX hLA hside t ht
    exact RunOutFacts_ni_plain hst.2.2.2.2.2.1
  | dot =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact RunOutFacts_ni_oDot h t ht
  | dropDot Γ' =>
    rw [List.mem_singleton.1 hs]
    obtain ⟨i, c, -, -, -, rfl⟩ := hA.1
    exact RunOutFacts_ni_sub h fun c hc => List.mem_of_mem_eraseIdx hc
  | reorder Γ' =>
    rw [List.mem_singleton.1 hs]
    exact RunOutFacts_ni_reorder h hA.1
  | xdotDup i =>
    rw [List.mem_singleton.1 hs]
    refine RunOutFacts_ni_sub h fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · exact hc
    · exact List.mem_of_getElem? (Option.mem_toList.1 hc)
  | xdotDrop i j =>
    rw [List.mem_singleton.1 hs]
    exact RunOutFacts_ni_sub h fun c hc => List.mem_of_mem_eraseIdx hc
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm =>
    rw [List.mem_singleton.1 hs]
    exact h
  | subst m H x y₁ y₂ =>
    obtain ⟨he, -, -, -⟩ := hA
    obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.1 he
    cases eq_of_heq he
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hs
    have hH : RunOutFacts_NI H.comps :=
      RunOutFacts_ni_map_inv (liftA 1) (RunOutFacts_ni_sub h fun c hc => List.mem_append_left _ hc)
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact RunOutFacts_ni_map (liftA g'.1) hH c hc
    · exact RunOutFacts_ni_map (glueAtom x y₁ y₂) (RunOutFacts_ni_tSubst hT g' hg') c hc
  | qexp x =>
    obtain ⟨hN, hP, -, hform, -, -, -⟩ := hA
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    by_cases hPu : u.g.Plain
    · exact RunOutFacts_ni_plain hPu
    · exact RunOutFacts_ni_clean (hF.2.2.2.2.1 D n₀ x Γ hN hform hP u hu hPu).2.2.1

end NoInv

/-! ## An internal atom along one step -/

section Atom

private theorem RunOutFacts_pos_of_isRight {m : ℕ} {u : Atom 3 m} (h : u.isRight = true) :
    m ≠ 0 := by
  cases u with
  | inl a => simp at h
  | inr j => exact Nat.pos_iff_ne_zero.1 j.pos

/-- **One step of the run** at an admissible location of a graph of the domain of the selector
with an internal atom gives graphs with an internal atom. -/
private theorem RunOutFacts_atom_step {n D : ℕ} {𝒯 : TRec} {𝔈 : QFam} (hF : QExpFamilyStmt 𝔈)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (h : g.1 ≠ 0) (hD : TerminationC_Dom n D g)
    {l : TerminationC_Loc g.1} (hA : TerminationC_Adm n D 𝔈 g l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, s.1 ≠ 0 := by
  obtain ⟨n₀, Γ⟩ := g
  intro s hs
  cases l with
  | loc o x =>
    obtain ⟨-, -, -, -, -, -, -, hside, -, -⟩ := hA
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact RunOutFacts_pos_of_isRight ((RunOtimes_localOp_otimes x o hside t ht).2.1 x)
  | dot =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact RunOutFacts_pos_of_isRight
      ((RunOtimes_oDotT ht).1.2 ⟨0, Nat.pos_iff_ne_zero.2 h⟩)
  | dropDot Γ' => rw [List.mem_singleton.1 hs]; exact h
  | reorder Γ' => rw [List.mem_singleton.1 hs]; exact h
  | xdotDup i => rw [List.mem_singleton.1 hs]; exact h
  | xdotDrop i j => rw [List.mem_singleton.1 hs]; exact h
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm => rw [List.mem_singleton.1 hs]; exact h
  | subst m H x y₁ y₂ =>
    obtain ⟨he, -, -, hprem⟩ := hA
    obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.1 he
    cases eq_of_heq he
    obtain ⟨hx, -, -⟩ := step2EdgeB'_internal m H x y₁ y₂ hprem.2.2.2.2.2.2.2.2
    obtain ⟨g', -, rfl⟩ := List.mem_map.1 hs
    have := RunOutFacts_pos_of_isRight hx
    dsimp only
    omega
  | qexp x =>
    obtain ⟨⟨C, hN⟩, hP, hDo, hform, hnQ, -, -⟩ := hA
    have hR : TerminationC_RI n D ⟨n₀, Γ⟩ := hD.resolve_left fun h => h ⟨C, hN⟩
    have hB : Γ.InvB' := by
      rcases hR.1 with ⟨hB, -⟩ | ⟨-, hq⟩ | ⟨hlt, -⟩
      · exact hB
      · exact absurd hq hnQ
      · exact absurd (lt_of_lt_of_le hlt (SelRun_paperOrd_le Γ)) hDo
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    have hmono := (hF.2.2.2.2.2 D n₀ x Γ ⟨C, hN⟩ hform hP hnQ hB u hu).1
    exact RunOutFacts_pos_of_isRight (hmono.isRight x)

end Atom

/-! ## The run from the graphs of `A` and `Q` -/

section Run

variable {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} {𝔈 : QFam}

set_option maxRecDepth 100000 in
/-- The graphs of `A` of the second order `T`-expansion have internal atoms. -/
private theorem RunOutFacts_A_atom : ∀ g ∈ h2Rec.A, g.1 ≠ 0 := by
  decide +kernel

/-- The graphs of `A` of the second order `T`-expansion are normal regular of scaling order `≥ 3`
in the count of [II, (2.5)], and those of `Q` are output graphs of the run. -/
private theorem RunOutFacts_inputs (hD : 2 < D) :
    (∀ g ∈ h2Rec.A, (∃ C, g.2.Normal C) ∧ 3 ≤ g.2.paperOrd ∧ g.2.Plain) ∧
      (∀ g ∈ h2Rec.Q, TerminationC_Out n D g ∧ 2 ≤ g.2.ord ∧ g.2.Plain) := by
  have hS := h2Rec_struct (fun _ => []) D hD
  have hSh := hS.2.2.2.1
  have hDef := hS.2.2.2.2
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have hRAQ : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q :=
      List.mem_append_left _ (List.mem_append_right _ hg)
    have hN := (hSh.1.1 g hRAQ).1
    have h0 := (RunCompare_def63_leaf hDef g (List.mem_append_left _ hRAQ)).2.1
    have hA := (hSh.2.2.1 g hg).2
    rw [Graph.paperOrd_of_dotExcess h0]
    refine ⟨hN, by push_cast at hA; omega, TRec.plain_of_def63 hDef g hRAQ⟩
  · have hRAQ : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q := List.mem_append_right _ hg
    refine ⟨?_, (hSh.2.2.2.1 g hg).2, TRec.plain_of_def63 hDef g hRAQ⟩
    by_cases h0 : g.1 = 0
    · exact RunCompare_q0_out hD hg h0
    · exact RunOtimes_q_out hD hg h0

/-- The run is the concatenation of the runs from the graphs of `A` and of the graphs of `Q`,
which are outputs. -/
private theorem RunOutFacts_run_eq (hF : QExpFamilyStmt 𝔈) (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) :
    RunCompare.run 𝔈 n D 𝒯 =
        h2Rec.A.flatMap (RunCompare_o n D 𝒯 𝔈 TerminationC_sel) ++ h2Rec.Q ∧
      ∀ a ∈ h2Rec.A,
        SelRunB n D 𝒯 𝔈 TerminationC_sel [a] (RunCompare_o n D 𝒯 𝔈 TerminationC_sel a) := by
  have hD : 2 < D := by have := hT.1; omega
  obtain ⟨e, hs⟩ := RunCompare_flat (RunCompare.run_spec 𝔈 hF n D Sig 𝒯 hn hT).1
  refine ⟨?_, fun a ha => hs a (List.mem_append_left _ ha)⟩
  rw [e, List.flatMap_append]
  congr 1
  have hq : ∀ q ∈ h2Rec.Q, RunCompare_o n D 𝒯 𝔈 TerminationC_sel q = [q] := fun q hq =>
    RunCompare_single_out (hs q (List.mem_append_right _ hq)) ((RunOutFacts_inputs hD).2 q hq).1
  have key : ∀ L : Expansion 3, (∀ q ∈ L, RunCompare_o n D 𝒯 𝔈 TerminationC_sel q = [q]) →
      L.flatMap (RunCompare_o n D 𝒯 𝔈 TerminationC_sel) = L := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons q L ih =>
      intro hL
      rw [List.flatMap_cons, hL q List.mem_cons_self,
        ih fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')]
      rfl
  exact key _ hq

/-- The output graphs of the run from a graph of `A` have scaling order `≥ 3` and an internal
atom. -/
private theorem RunOutFacts_A_out (hF : QExpFamilyStmt 𝔈) (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {a : Σ n₀ : ℕ, Graph 3 n₀} (ha : a ∈ h2Rec.A) :
    ∀ g ∈ RunCompare_o n D 𝒯 𝔈 TerminationC_sel a, 3 ≤ g.2.ord ∧ g.1 ≠ 0 := by
  have hD : 2 < D := by have := hT.1; omega
  have hr := (RunOutFacts_run_eq hF hn hT).2 a ha
  have hIa : RunCompare_I n D 𝒯 a := RunCompare_I_inputs hn hT a (List.mem_append_left _ ha)
  have hI : ∀ g, RunCompare_I n D 𝒯 g → ¬ TerminationC_Out n D g →
      ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (TerminationC_sel g), RunCompare_I n D 𝒯 s :=
    fun _ hg hO => (RunCompare_I_step (𝔈 := 𝔈) hF hn hT hg hO).2
  obtain ⟨hN, h3, -⟩ := (RunOutFacts_inputs (n := n) hD).1 a ha
  have hHi := RunCompare_high (Hi := RunCompare_Hi false 2) hI
    (fun g hg hh hO => RunCompare_hi_step hF hn hT g hg hh hO) hr (by
      intro g hg
      rw [List.mem_singleton.1 hg]
      obtain ⟨C, hN⟩ := hN
      exact ⟨hIa, (RunCompare_hi_normal hN).2 ⟨by push_cast; omega, fun h => absurd h (by simp)⟩⟩)
  have hAt := RunCompare_high (Hi := fun g : Σ n₀ : ℕ, Graph 3 n₀ => g.1 ≠ 0) hI
    (fun g hg hh hO s hs => by
      obtain ⟨hDm, hAd⟩ := RunCompare_adm hF hn hT hg hO
      exact RunOutFacts_atom_step hF hh hDm hAd s hs) hr (by
      intro g hg
      rw [List.mem_singleton.1 hg]
      exact ⟨hIa, RunOutFacts_A_atom a ha⟩)
  intro g hg
  have hO : TerminationC_Out n D g := by
    have hm : g ∈ RunCompare.run 𝔈 n D 𝒯 := by
      rw [(RunOutFacts_run_eq hF hn hT).1]
      exact List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha, hg⟩)
    exact (RunCompare.run_spec 𝔈 hF n D Sig 𝒯 hn hT).2.2 g hm
  obtain ⟨C, hNg⟩ := hO.2.2.1
  have h1 := ((RunCompare_hi_normal hNg).1 (hHi g hg)).1
  have h2 := SelRun_paperOrd_le g.2
  exact ⟨by push_cast at h1; omega, hAt g hg⟩

end Run

/-! ## The four facts -/

/-- **The output graphs of the run of [II, Strategy 6.6]** ([II, Lemma 6.8]) driven by the
selector `TerminationC_sel` from the graphs of `A` and `Q` of the second order `T`-expansion, for
a family `𝔈` of `Q`-expansions of [II, Lemma 4.15] with `QExpFamilyStmt`, a cutoff order `n ≥ 3`
and an `(n - 1)`-th order `T`-expansion `𝒯` with error order `D`:
* an output graph of scaling order `> D` has no `(G_xx)⁻¹` weight ([II, Lemma 4.11],
  [II, Lemma 4.15]);
* an output graph without internal atom is a graph of `Q` of the second order `T`-expansion
  ([I, (2.9)]);
* every output graph has scaling order `≥ 2` ([I, (2.8)–(2.9)], [II, Lemma 6.5]);
* at `n = 3`, the output graphs of scaling order `≤ 2` are, up to order and with multiplicity, the
  graphs of `Q` of the second order `T`-expansion of scaling order `≤ 2` ([II, Def 3.2 (7)],
  [II, (6.9)]). -/
theorem RunCompare.run_outFacts (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (hF : QExpFamilyStmt 𝔈) (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec) (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) :
    -- no `(G_xx)⁻¹` weight on an output graph of scaling order `> D`
    (∀ g ∈ RunCompare.run 𝔈 n D 𝒯, (D : ℤ) < g.2.ord →
        ∀ c ∈ g.2.comps, ∀ ch, c.kind ≠ .inv ch) ∧
    -- an output graph without internal atom is a graph of `h2Rec.Q`
    (∀ g ∈ RunCompare.run 𝔈 n D 𝒯, g.1 = 0 → g ∈ h2Rec.Q) ∧
    -- every output graph has scaling order `≥ 2`
    (∀ g ∈ RunCompare.run 𝔈 n D 𝒯, 2 ≤ g.2.ord) ∧
    -- at `n = 3` the output graphs of order `≤ 2` are the graphs of `h2Rec.Q` of order `≤ 2`
    (n = 3 → ((RunCompare.run 𝔈 n D 𝒯).filter fun g => decide (g.2.ord ≤ 2)).Perm
        (h2Rec.Q.filter fun g => decide (g.2.ord ≤ 2))) := by
  have hD : 2 < D := by have := hT.1; omega
  obtain ⟨e, -⟩ := RunOutFacts_run_eq hF hn hT
  have hsplit : ∀ g ∈ RunCompare.run 𝔈 n D 𝒯, g ∈ h2Rec.Q ∨ (3 ≤ g.2.ord ∧ g.1 ≠ 0) := by
    intro g hg
    rw [e] at hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨a, ha, hga⟩ := List.mem_flatMap.1 hg
      exact Or.inr (RunOutFacts_A_out hF hn hT ha g hga)
    · exact Or.inl hg
  refine ⟨fun g hg _ => ?_, fun g hg h0 => ?_, fun g hg => ?_, fun _ => ?_⟩
  · refine RunCompare_high (Hi := fun g : Σ n₀ : ℕ, Graph 3 n₀ => RunOutFacts_NI g.2.comps)
      (fun _ hg hO => (RunCompare_I_step (𝔈 := 𝔈) hF hn hT hg hO).2)
      (fun g hg hh hO s hs => by
        obtain ⟨hDm, hAd⟩ := RunCompare_adm hF hn hT hg hO
        exact RunOutFacts_ni_step hF hT hh hDm hAd s hs)
      (RunCompare.run_spec 𝔈 hF n D Sig 𝒯 hn hT).1
      (fun a ha => ⟨RunCompare_I_inputs hn hT a ha, ?_⟩) g hg
    rcases List.mem_append.1 ha with ha | ha
    · exact RunOutFacts_ni_plain ((RunOutFacts_inputs (n := n) hD).1 a ha).2.2
    · exact RunOutFacts_ni_plain ((RunOutFacts_inputs (n := n) hD).2 a ha).2.2
  · rcases hsplit g hg with h | h
    · exact h
    · exact absurd h0 h.2
  · rcases hsplit g hg with h | h
    · exact ((RunOutFacts_inputs (n := n) hD).2 g h).2.1
    · omega
  · rw [e, List.filter_append, List.filter_flatMap]
    have hz : (h2Rec.A.flatMap fun a =>
        (RunCompare_o n D 𝒯 𝔈 TerminationC_sel a).filter fun g => decide (g.2.ord ≤ 2)) = [] := by
      refine List.flatMap_eq_nil_iff.2 fun a ha => List.filter_eq_nil_iff.2 fun g hg => ?_
      have := (RunOutFacts_A_out hF hn hT ha g hg).1
      simp only [decide_eq_true_eq]
      omega
    rw [hz, List.nil_append]

section Instances

end Instances

end RBM8D.Graphs
