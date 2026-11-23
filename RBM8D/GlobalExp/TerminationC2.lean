module

public import RBM8D.GlobalExp.TerminationK
public import RBM8D.GlobalExp.RunClauses
public import RBM8D.GlobalExp.TerminationB
public import RBM8D.GlobalExp.TerminationC
public import RBM8D.GlobalExp.GlobalGoodB
public import RBM8D.GlobalExp.SubstDC
public import RBM8D.GlobalExp.Termination
public import RBM8D.GlobalExp.Local
public import RBM8D.Graph.MolCarry
public import RBM8D.Graph.Local.DotNorm
public import RBM8D.TExp.Second
public import RBM8D.TExp.Closure
import all RBM8D.GlobalExp.RunClauses
import all RBM8D.GlobalExp.TerminationK
import all RBM8D.GlobalExp.TerminationB
import all RBM8D.GlobalExp.TerminationC
import all RBM8D.GlobalExp.GlobalGoodB
import all RBM8D.GlobalExp.SubstDC
import all RBM8D.GlobalExp.Termination
import all RBM8D.GlobalExp.Local
import all RBM8D.Graph.MolCarry
import all RBM8D.Graph.Local.DotNorm
import all RBM8D.TExp.Second
import all RBM8D.TExp.Closure

@[expose] public section

/-!
# [II, Lemma 6.8] in the block reading: the run of a selector ends

The well-founded construction of [II, Lemma 6.8] (the tree of [II, Strategy 6.6] has finite
height) for the runs driven by selectors (`TerminationC_Loc`, `AdmSelector`, `SelRunB`):

* runs of single graphs side by side are runs (`SelRunB.append`);
* the graphs of a run (normal regular graphs with the invariant of a run, the substituted graphs
  of Steps 2–3 before `O_dot` and after the steps on `×`-dotted edges and on the coefficient, the
  `O_dot` forms with labels of the substituted graphs of `Q`) carry a rank, compared
  lexicographically: a level, the measure `runMu` of the graph or of the host of Steps 2–3, a
  tier, and the measure `TerminationC_nu` of the normal form of Step 2;
* at every such graph that is not an output an admissible selector gives a step, and every graph
  of the step is an output or a graph of the run of smaller rank: Step 1 lowers `runMu`
  (`locMu`), the removal of a redundant dotted edge lowers it (`dotNormStep_mu`), the steps on
  `×`-dotted edges and on the coefficient and the reordering to a host lower `TerminationC_nu`,
  and the `O_dot` forms of a substituted graph and the outputs of its `Q`-expansions lie below the
  host (`substMu`, [II, Lemma 6.5]); the invariant of a run is kept along every step;
* **[II, Lemma 6.8]** for every admissible selector (`strategyB_sel`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Runs from runs of single graphs -/

/-- Two runs driven by one selector side by side are a run from the concatenated inputs to the
concatenated outputs. -/
theorem SelRunB.append {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    {ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1} {E₁ F₁ E₂ F₂ : Expansion 3}
    (h₁ : SelRunB n D 𝒯 𝔈 ℓ E₁ F₁) (h₂ : SelRunB n D 𝒯 𝔈 ℓ E₂ F₂) :
    SelRunB n D 𝒯 𝔈 ℓ (E₁ ++ E₂) (F₁ ++ F₂) := by
  induction h₁ with
  | nil => exact h₂
  | out hO _ ih => exact SelRunB.out hO ih
  | step hO hs _ ih => rw [List.append_assoc] at ih; exact SelRunB.step hO hs ih

/-- Runs of the single graphs of a formal sum, driven by one selector, with outputs in
`TerminationC_Out`, give such a run of the formal sum. -/
private theorem TerminationC2_runs_list {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    {ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1} :
    ∀ E : Expansion 3, (∀ g ∈ E, ∃ F, SelRunB n D 𝒯 𝔈 ℓ [g] F ∧ ∀ h ∈ F, TerminationC_Out n D h) →
      ∃ F, SelRunB n D 𝒯 𝔈 ℓ E F ∧ ∀ h ∈ F, TerminationC_Out n D h
  | [], _ => ⟨[], SelRunB.nil, fun _ h => absurd h List.not_mem_nil⟩
  | g :: E, hE => by
    obtain ⟨F₁, h₁, o₁⟩ := hE g List.mem_cons_self
    obtain ⟨F₂, h₂, o₂⟩ := TerminationC2_runs_list E fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')
    refine ⟨F₁ ++ F₂, SelRunB.append h₁ h₂, fun h hh => ?_⟩
    rcases List.mem_append.1 hh with hh | hh
    · exact o₁ h hh
    · exact o₂ h hh

/-- **The well-founded construction of a run** ([II, Lemma 6.8], the tree of the strategy has
finite height): given an admissible selector and a family `P` of graphs ranked in a
well-founded order, such that at every graph of `P` that is not an output the selector gives a
step and every graph of the step is an output or a graph of `P` of smaller rank, every formal sum
of outputs and graphs of `P` has a run driven by the selector whose outputs are outputs. -/
private theorem TerminationC2_runs {n D : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    {ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1} (hℓ : AdmSelector n D 𝒯 𝔈 ℓ)
    {ρ : Type} [Preorder ρ] [WellFoundedLT ρ] (P : (Σ n₀ : ℕ, Graph 3 n₀) → ρ → Prop)
    (hkey : ∀ g r, P g r → ¬ TerminationC_Out n D g → TerminationC_Dom n D g ∧
      ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g), TerminationC_Out n D s ∨ ∃ r', r' < r ∧ P s r') :
    ∀ E : Expansion 3, (∀ g ∈ E, TerminationC_Out n D g ∨ ∃ r, P g r) →
      ∃ F, SelRunB n D 𝒯 𝔈 ℓ E F ∧ ∀ h ∈ F, TerminationC_Out n D h := by
  have hout : ∀ g, TerminationC_Out n D g →
      ∃ F, SelRunB n D 𝒯 𝔈 ℓ [g] F ∧ ∀ h ∈ F, TerminationC_Out n D h := fun g hO =>
    ⟨[g], SelRunB.out hO SelRunB.nil, fun h hh => by rw [List.mem_singleton.1 hh]; exact hO⟩
  have hone : ∀ r g, P g r →
      ∃ F, SelRunB n D 𝒯 𝔈 ℓ [g] F ∧ ∀ h ∈ F, TerminationC_Out n D h := by
    intro r
    induction r using WellFoundedLT.induction with
    | _ r ih =>
      intro g hg
      by_cases hO : TerminationC_Out n D g
      · exact hout g hO
      obtain ⟨hD, hs⟩ := hkey g r hg hO
      obtain ⟨-, hst⟩ := hℓ g hD hO
      obtain ⟨F, hF, oF⟩ := TerminationC2_runs_list _ fun s hs' => by
        rcases hs s hs' with h | ⟨r', hr', hP⟩
        · exact hout s h
        · exact ih r' hr' s hP
      exact ⟨F, SelRunB.step hO hst (by simpa using hF), oF⟩
  intro E hE
  exact TerminationC2_runs_list E fun g hg => by
    rcases hE g hg with h | ⟨r, hP⟩
    · exact hout g h
    · exact hone r g hP

/-! ## Graphs with the same components up to `×`-dotted edges -/

section Ops

variable {n₀ : ℕ}

/-- `c'` is `c`, or `c` is a `×`-dotted edge and `c'` is `c` with its two atoms exchanged. -/
private def TerminationC2_XSw (c c' : Comp (Atom 3 n₀)) : Prop :=
  c' = c ∨ (c.kind = .xdot ∧ c' = { c with x := c.y, y := c.x })

private theorem TerminationC2_XSw.kind {c c' : Comp (Atom 3 n₀)} (h : TerminationC2_XSw c c') :
    c'.kind = c.kind := by
  rcases h with rfl | ⟨-, rfl⟩ <;> rfl

private theorem TerminationC2_XSw.eq {c c' : Comp (Atom 3 n₀)} (h : TerminationC2_XSw c c')
    (hk : c.kind ≠ .xdot) : c' = c := by
  rcases h with rfl | ⟨h, -⟩
  · rfl
  · exact absurd h hk

private theorem TerminationC2_XSw.ends {c c' : Comp (Atom 3 n₀)} (h : TerminationC2_XSw c c') :
    (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x) := by
  rcases h with rfl | ⟨-, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- A component joins `u` and `v` in either orientation iff its exchange `XSw` does. -/
private theorem TerminationC2_XSw.joins {c c' : Comp (Atom 3 n₀)} (h : TerminationC2_XSw c c')
    {u v : Atom 3 n₀} :
    (c'.x = u ∧ c'.y = v ∨ c'.x = v ∧ c'.y = u) ↔ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u) := by
  rcases h.ends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]; tauto

/-- **The normal regular form is kept** when every component of each graph is a component of the
other, up to the exchange of the two atoms of `×`-dotted edges. -/
private theorem TerminationC2_normal_of {Γ Γ' : Graph 3 n₀}
    (h1 : ∀ c' ∈ Γ'.comps, ∃ c ∈ Γ.comps, TerminationC2_XSw c c')
    (h2 : ∀ c ∈ Γ.comps, ∃ c' ∈ Γ'.comps, TerminationC2_XSw c' c) {C : ℕ} (hN : Γ.Normal C) :
    Γ'.Normal (C + Γ'.comps.length) := by
  obtain ⟨hR, hs, hx⟩ := hN
  have hex : ∀ (P : Kind → Prop) (u v : Atom 3 n₀), (∀ κ, P κ → κ = .xdot ∨ True) →
      ((∃ c ∈ Γ'.comps, P c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ Γ.comps, P c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u))) := by
    intro P u v _
    constructor
    · rintro ⟨c, hc, hk, hj⟩
      obtain ⟨c₀, hc₀, hw⟩ := h1 c hc
      exact ⟨c₀, hc₀, by rw [← hw.kind]; exact hk, hw.joins.1 hj⟩
    · rintro ⟨c, hc, hk, hj⟩
      obtain ⟨c', hc', hw⟩ := h2 c hc
      exact ⟨c', hc', by rw [← hw.kind]; exact hk, hw.joins.1 hj⟩
  refine ⟨⟨by have := hR.size; omega, hR.connected.mono ?_,
    fun a b => (hR.internal a b).mono ?_, fun c hc hk => ?_⟩, fun c hc hk => ?_,
    fun u v huv => ?_⟩
  · intro u v huv
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at huv ⊢
    obtain ⟨hne, h⟩ := huv
    have := (hex (fun _ => True) u v (fun _ _ => Or.inr trivial)).2
    rcases h with ⟨c, hc, e1, e2⟩ | ⟨c, hc, e1, e2⟩
    · obtain ⟨c', hc', -, hj⟩ := this ⟨c, hc, trivial, Or.inl ⟨e1, e2⟩⟩
      rcases hj with ⟨f1, f2⟩ | ⟨f1, f2⟩
      · exact ⟨hne, Or.inl ⟨c', hc', f1, f2⟩⟩
      · exact ⟨hne, Or.inr ⟨c', hc', f1, f2⟩⟩
    · obtain ⟨c', hc', -, hj⟩ := this ⟨c, hc, trivial, Or.inr ⟨e1, e2⟩⟩
      rcases hj with ⟨f1, f2⟩ | ⟨f1, f2⟩
      · exact ⟨hne, Or.inl ⟨c', hc', f1, f2⟩⟩
      · exact ⟨hne, Or.inr ⟨c', hc', f1, f2⟩⟩
  · intro u v huv
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at huv ⊢
    have key : ∀ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨
        c.kind.isDiffusive = true) → c ∈ Γ'.comps := by
      intro c hc hk
      obtain ⟨c', hc', hw⟩ := h2 c hc
      have hnx : c'.kind ≠ .xdot := by
        intro h
        rw [hw.kind, h] at hk
        simp [Kind.joinsMol, Kind.isDiffusive] at hk
      rw [hw.eq hnx]
      exact hc'
    obtain ⟨hne, ⟨c, hc, hk, e1, e2⟩ | ⟨c, hc, hk, e1, e2⟩⟩ := huv
    · exact ⟨hne, Or.inl ⟨c, key c hc hk, hk, e1, e2⟩⟩
    · exact ⟨hne, Or.inr ⟨c, key c hc hk, hk, e1, e2⟩⟩
  · obtain ⟨c₀, hc₀, hw⟩ := h1 c hc
    have hk' : c₀.kind ≠ .xdot := by rw [← hw.kind, hk]; simp
    rw [hw.eq hk'] at hk ⊢
    exact hR.noIntDot c₀ hc₀ hk
  · obtain ⟨c₀, hc₀, hw⟩ := h1 c hc
    have hk' : c₀.kind ≠ .xdot := by
      intro h; rw [hw.kind, h] at hk; simp [Kind.isSolid] at hk
    rw [hw.eq hk'] at hk ⊢
    exact hs c₀ hc₀ hk
  · exact (hex (fun κ => κ = .xdot) u v (fun _ _ => Or.inr trivial)).trans
      ((hx u v huv).trans (hex (fun κ => κ.isSolid = true) u v (fun _ _ => Or.inr trivial)).symm)

/-- Clauses read component by component pass to a graph whose components are components of the
graph. -/
private theorem TerminationC2_sub_facts {Γ Γ' : Graph 3 n₀} (h : ∀ c ∈ Γ'.comps, c ∈ Γ.comps)
    (N : ℕ) : (Γ.TensorDiffusive → Γ'.TensorDiffusive) ∧ (Γ.Plain → Γ'.Plain) ∧
      (Γ.LabelFree → Γ'.LabelFree) ∧ (Γ.RunKinds N → Γ'.RunKinds N) ∧
      (Γ.NoLabDot → Γ'.NoLabDot) :=
  ⟨fun hT => List.all_eq_true.2 fun c hc => List.all_eq_true.1 hT c (h c hc),
    fun hP c hc => hP c (h c hc), fun hL c hc => hL c (h c hc),
    fun hK => List.all_eq_true.2 fun c hc => List.all_eq_true.1 hK c (h c hc),
    fun hD c hc => hD c (h c hc)⟩

/-- The dot excess reads the dotted edges only. -/
private theorem TerminationC2_dotExcess_of {Γ Γ' : Graph 3 n₀}
    (h : Γ'.comps.filter (fun c => decide (c.kind = .dot)) =
      Γ.comps.filter (fun c => decide (c.kind = .dot))) :
    Γ'.dotExcess = Γ.dotExcess := by
  have hm : ∀ c, (c ∈ Γ'.comps ∧ c.kind = .dot) ↔ (c ∈ Γ.comps ∧ c.kind = .dot) := by
    intro c
    have := congrArg (c ∈ ·) h
    simpa only [List.mem_filter, decide_eq_true_eq, eq_iff_iff] using this
  have hg : Γ'.dotGraph = Γ.dotGraph := by
    unfold Graph.dotGraph
    congr 1
    funext u v
    exact propext ⟨fun ⟨c, hc, hk, h1, h2⟩ => ⟨c, ((hm c).1 ⟨hc, hk⟩).1, hk, h1, h2⟩,
      fun ⟨c, hc, hk, h1, h2⟩ => ⟨c, ((hm c).2 ⟨hc, hk⟩).1, hk, h1, h2⟩⟩
  unfold Graph.dotExcess Graph.nDots
  rw [h, hg]

/-- **The doubly connected property** passes to a graph that contains, with multiplicity, every
list of diffusive or blue components of the graph and has coarser molecules. -/
private theorem TerminationC2_dc_of {Γ Γ' : Graph 3 n₀}
    (hsub : ∀ L : List (Comp (Atom 3 n₀)), L.Subperm Γ.comps →
      (∀ c ∈ L, c.kind.isDiffusive = true ∨ c.kind.isBlue = true) → L.Subperm Γ'.comps)
    (hmol : ∀ u v, Γ.SameMol u v → Γ'.SameMol u v) (h : Γ.DoublyConnected) :
    Γ'.DoublyConnected := by
  apply Graph.dc_of_dcl
  obtain ⟨Lb, Lu, hs, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc h
  have hmono : ∀ L, SimpleGraph.fromRel (nrel Γ L) ≤ SimpleGraph.fromRel (nrel Γ' L) := by
    intro L a b hab
    rw [SimpleGraph.fromRel_adj] at hab ⊢
    obtain ⟨hne, h | h⟩ := hab
    · exact ⟨hne, Or.inl (h.imp_left (hmol _ _))⟩
    · exact ⟨hne, Or.inr (h.imp_left (hmol _ _))⟩
  refine ⟨Lb, Lu, hsub _ hs fun c hc => ?_, hb, hu, hsb.mono (hmono Lb), hsu.mono (hmono Lu)⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact Or.inl (hb c hc)
  · exact hu c hc

/-- A sublist up to order that misses the entry `j` is a sublist up to order without it. -/
private theorem TerminationC2_subperm_eraseIdx {α : Type*} {L cs : List α} (h : L.Subperm cs)
    {j : ℕ} (hj : j < cs.length) (hn : cs[j] ∉ L) : L.Subperm (cs.eraseIdx j) := by
  classical
  have h' : L.Subperm (cs[j] :: cs.eraseIdx j) :=
    h.trans (List.getElem_cons_eraseIdx_perm hj).symm.subperm
  rw [List.subperm_iff_count] at h' ⊢
  intro a
  have := h' a
  rw [List.count_cons] at this
  by_cases ha : a = cs[j]
  · subst ha
    rw [List.count_eq_zero_of_not_mem hn]
    exact Nat.zero_le _
  · have : (cs[j] == a) = false := by simpa [beq_iff_eq] using Ne.symm ha
    simp_all

/-- A component joined by a step of `List.Forall₂` that fixes `c` counts no less. -/
private theorem TerminationC2_count_forall₂ {α : Type*} [DecidableEq α] {R : α → α → Prop}
    (c : α) (hR : ∀ a b, R a b → a = c → b = c) :
    ∀ {A B : List α}, List.Forall₂ R A B → A.count c ≤ B.count c
  | _, _, .nil => le_rfl
  | a :: A, b :: B, .cons hr hl => by
    have ih := TerminationC2_count_forall₂ c hR hl
    simp only [List.count_cons, beq_iff_eq]
    by_cases ha : a = c
    · have hb := hR a b hr ha
      simp only [ha, hb, ite_true]
      omega
    · simp only [ha, ite_false]
      split_ifs <;> omega

/-- A weight is a random component. -/
private theorem TerminationC2_isRandom_of_weight {κ : Kind} (h : κ.isWeight = true) :
    κ.isRandom = true := by
  cases κ <;> simp_all [Kind.isWeight, Kind.isRandom]

end Ops

section Iso

open private RunClauses_Iso RunClauses_SwapR RunClauses_eA RunClauses_eA_inr RunClauses_iso_mem'
  RunClauses_iso_sameMol RunClauses_swapR_eq RunClauses_iso_card from RBM8D.GlobalExp.RunClauses

variable {m m' : ℕ} {e : Fin m ≃ Fin m'} {Γ : Graph 3 m} {Γ' : Graph 3 m'}

/-- **The doubly connected property is kept by a renaming and reordering** (`RunClauses_Iso`):
the two nets are carried, and the molecules are mapped to molecules. -/
private theorem TerminationC2_dc_iso (h : RunClauses_Iso e Γ Γ') (hD : Γ.DoublyConnected) :
    Γ'.DoublyConnected := by
  classical
  apply Graph.dc_of_dcl
  obtain ⟨Lb, Lu, hs, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc hD
  obtain ⟨-, cs, hF, hP⟩ := id h
  set f : Comp (Atom 3 m) → Comp (Atom 3 m') := Comp.map (RunClauses_eA e) with hf
  have hfinj : Function.Injective f := by
    intro c d hcd
    have h1 := congrArg Comp.kind hcd
    have h2 := congrArg Comp.x hcd
    have h3 := congrArg Comp.y hcd
    have h4 := congrArg Comp.minor hcd
    have h5 := congrArg Comp.label hcd
    simp only [hf, Comp.map] at h1 h2 h3 h4 h5
    have hi := (RunClauses_eA e).injective
    rcases c with ⟨ck, cx, cy, cm, cl⟩
    rcases d with ⟨dk, dx, dy, dm, dl⟩
    simp only at h1 h2 h3 h4 h5
    have hx := hi h2
    have hy := hi h3
    have hm := List.map_injective_iff.2 hi h4
    have hl : cl = dl := Option.map_injective
      (Function.Injective.prodMap Function.injective_id hi) h5
    subst h1 hx hy hm hl
    rfl
  have hnet : ∀ L : List (Comp (Atom 3 m)), (SimpleGraph.fromRel (nrel Γ L)).Preconnected →
      (SimpleGraph.fromRel (nrel Γ' (L.map f))).Preconnected := by
    intro L hL
    let φ : SimpleGraph.fromRel (nrel Γ L) →g SimpleGraph.fromRel (nrel Γ' (L.map f)) :=
      ⟨e, fun {a b} hab => by
        rw [SimpleGraph.fromRel_adj] at hab ⊢
        have key : ∀ a b, nrel Γ L a b → nrel Γ' (L.map f) (e a) (e b) := by
          intro a b hab'
          rcases hab' with hm | ⟨c, hc, h1, h2⟩
          · left
            have := (RunClauses_iso_sameMol h (.inr a) (.inr b)).2 hm
            simpa [RunClauses_eA_inr] using this
          · right
            refine ⟨f c, List.mem_map_of_mem hc, ?_, ?_⟩
            · simp [hf, Comp.map, h1, RunClauses_eA_inr]
            · simp [hf, Comp.map, h2, RunClauses_eA_inr]
        obtain ⟨hne, h | h⟩ := hab
        · exact ⟨e.injective.ne hne, Or.inl (key a b h)⟩
        · exact ⟨e.injective.ne hne, Or.inr (key b a h)⟩⟩
    exact hL.map φ e.surjective
  have hkind : ∀ c ∈ Lb ++ Lu, c.kind.isDiffusive = true ∨ c.kind.isBlue = true := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl (hb c hc)
    · exact hu c hc
  refine ⟨Lb.map f, Lu.map f, ?_, fun c hc => ?_, fun c hc => ?_, hnet Lb hsb, hnet Lu hsu⟩
  · rw [← List.map_append]
    have h1 : ((Lb ++ Lu).map f).Subperm (Γ.comps.map f) := hs.map hfinj
    refine List.Subperm.trans ?_ hP.subperm
    rw [List.subperm_iff_count] at h1 ⊢
    intro c
    by_cases hc : c ∈ (Lb ++ Lu).map f
    · refine (h1 c).trans (TerminationC2_count_forall₂ c (fun a b hr ha => ?_) hF)
      subst ha
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      rcases hr with hr | ⟨hk, -⟩
      · exact hr
      · exfalso
        have := hkind c₀ hc₀
        simp only [hf, Comp.map] at hk
        rcases hk with hk | hk | hk <;> rw [hk] at this <;>
          simp [Kind.isDiffusive, Kind.isBlue] at this
    · rw [List.count_eq_zero_of_not_mem hc]
      exact Nat.zero_le _
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact hb c₀ hc₀
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact hu c₀ hc₀

/-- Plain graphs, graphs without labels and graphs without labelled dotted edges are kept by a
renaming and reordering. -/
private theorem TerminationC2_iso_facts (h : RunClauses_Iso e Γ Γ') :
    (Γ.Plain → Γ'.Plain) ∧ (Γ.LabelFree → Γ'.LabelFree) ∧ (Γ.NoLabDot → Γ'.NoLabDot) := by
  have hi := (RunClauses_eA e).injective
  refine ⟨fun hP c' hc' => ?_, fun hL c' hc' => ?_, fun hN c' hc' hk => ?_⟩
  · obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
    obtain ⟨hk, hl, hm, hxy, hrd⟩ := RunClauses_swapR_eq hr
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP c hc
    refine ⟨by rw [hm]; simp [Comp.map, p1], fun ch => by rw [hk]; exact p2 ch,
      fun ch d => by rw [hk]; exact p3 ch d, fun hd => ?_, fun hw => ?_, fun hs => ?_⟩
    · rw [hk] at hd
      have := p4 hd
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp only [Comp.map] <;>
        exact fun h => this (hi (by first | exact h | exact h.symm))
    · rw [hk] at hw
      have hw' : c.kind.isWeight = true := by simpa [Comp.map] using hw
      have hr' : c.kind.isRandom = true := TerminationC2_isRandom_of_weight hw'
      rw [hrd (Or.inl (by simpa [Comp.map] using hr'))]
      simp [Comp.map, p5 hw']
    · rw [hk]
      apply p6
      rw [hl] at hs
      simpa [Comp.map] using hs
  · obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
    rw [(RunClauses_swapR_eq hr).2.1]
    simp [Comp.map, hL c hc]
  · obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
    obtain ⟨hk', hl, -⟩ := RunClauses_swapR_eq hr
    rw [hl]
    simp only [Comp.map]
    rw [hN c hc (by rw [hk'] at hk; simpa [Comp.map] using hk)]
    rfl

end Iso

/-! ## The invariant of a run on graphs without labels -/

section LF

open private RunClauses_Iso RunClauses_reorder_iso RunClauses_iso_normal RunClauses_iso_td
  RunClauses_iso_dotExcess from RBM8D.GlobalExp.RunClauses
open private TerminationK_runKinds_iff TerminationK_reorder from RBM8D.GlobalExp.TerminationK

variable {n₀ : ℕ}

/-- The hypotheses on the cutoff order and the `T`-expansion in [II, Lemma 6.8]: `n ≥ 3` and an
`(n - 1)`-th order `T`-expansion with error order `D`. -/
private def TerminationC2_Hyp (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec) : Prop :=
  3 ≤ n ∧ 𝒯.IsTExpStruct Sig (n - 1) D

private theorem TerminationC2_Hyp.le {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (h : TerminationC2_Hyp n D Sig 𝒯) : n ≤ D := by
  have := h.2.1
  have := h.1
  omega

/-- A graph without labels, normal regular, with the invariant of a run `TerminationC_RI` and the
run kinds of [II, Strategy 6.6] for the order `n - 1`. -/
private def TerminationC2_LF (n D : ℕ) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  (∃ C, g.2.Normal C) ∧ TerminationC_RI n D g ∧ g.2.LabelFree ∧ g.2.RunKinds (n - 1)

/-- The invariant of a run of a graph without labels from its clauses that do not read labels. -/
private theorem TerminationC2_ri_lf {n D N : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀} (hL : g.2.LabelFree)
    (hI : g.2.InvRun D) (hv : TerminationB_Inv n D g.2) (hdc : g.2.DoublyConnected)
    (hT : g.2.TensorDiffusive) (h9 : g.2.dotExcess ≠ 0 → g.2.Plain) (hK : g.2.RunKinds N) :
    TerminationC_RI n D g := by
  have hnil : g.2.comps.filterMap Comp.label = [] :=
    List.filterMap_eq_nil_iff.2 fun c hc => hL c hc
  refine ⟨hI, hv, hdc, hT, (fun c hc _ => hL c hc), (by simp [Graph.labels, hnil]),
    (fun c hc u h => by rw [hL c hc] at h; cases h), (fun hQ => ?_), h9, ?_⟩
  · obtain ⟨u, ⟨c, hc, hl⟩, -⟩ := hQ
    rw [hL c hc] at hl
    cases hl
  · rcases hv.1 with hP | hD
    · exact Or.inr ⟨N, hK.tKinds hP⟩
    · exact Or.inl hD

/-- Molecules are kept when every waved and dotted edge stays. -/
private theorem TerminationC2_sameMol_of {Γ Γ' : Graph 3 n₀}
    (h : ∀ c ∈ Γ.comps, c.kind.joinsMol = true → c ∈ Γ'.comps) {u v : Atom 3 n₀}
    (hm : Γ.SameMol u v) : Γ'.SameMol u v := by
  rcases hm with rfl | ⟨hu, hv, hr⟩
  · exact Or.inl rfl
  refine Or.inr ⟨hu, hv, hr.mono fun a b hab => ?_⟩
  rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hab ⊢
  obtain ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩ := hab
  · exact ⟨hne, Or.inl ⟨c, h c hc hk, hk, h1, h2⟩⟩
  · exact ⟨hne, Or.inr ⟨c, h c hc hk, hk, h1, h2⟩⟩

/-- Filtering ignores an erased entry that the filter drops. -/
private theorem TerminationC2_filter_eraseIdx {α : Type*} (p : α → Bool) (l : List α) {j : ℕ}
    (hj : j < l.length) (hp : p l[j] = false) : (l.eraseIdx j).filter p = l.filter p := by
  rw [List.eraseIdx_eq_take_drop_succ]
  have h1 : l.filter p = (l.take j ++ l.drop j).filter p := by rw [List.take_append_drop]
  rw [h1, List.drop_eq_getElem_cons hj, List.filter_append, List.filter_append, List.filter_cons,
    hp]
  rfl

/-- An entry of a list is an entry of the list with the entry `j` erased, or is that entry. -/
private theorem TerminationC2_mem_eraseIdx {α : Type*} {l : List α} {c : α} (hc : c ∈ l) {j : ℕ}
    (hj : j < l.length) : c ∈ l.eraseIdx j ∨ c = l[j] := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  by_cases hij : i = j
  · subst hij; exact Or.inr rfl
  · exact Or.inl (List.mem_eraseIdx_iff_getElem.2 ⟨i, hi, hij, rfl⟩)

/-- **The duplication of a `×`-dotted edge** keeps a graph without labels with the invariant of a
run, and its measure `runMu`. -/
private theorem TerminationC2_lf_dup {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) {Γ : Graph 3 n₀} (i : Fin Γ.comps.length)
    (hk : Γ.comps[i].kind = .xdot) (hx : Γ.comps[i].x.isRight = true)
    (hy : Γ.comps[i].y.isRight = true) (h : TerminationC2_LF n D ⟨n₀, Γ⟩) :
    TerminationC2_LF n D ⟨n₀, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩ ∧
      runMu n (⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩ : Graph 3 n₀) = runMu n Γ := by
  obtain ⟨⟨C, hN⟩, ⟨hI, hv, hdc, hT, -, -, -, -, h9, -⟩, hL, hK⟩ := h
  set Γ' : Graph 3 n₀ := ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩ with hΓ'
  have hmem : ∀ c ∈ Γ'.comps, c ∈ Γ.comps := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hc
    · rw [List.mem_singleton.1 hc]; exact List.getElem_mem _
  have hmem' : ∀ c ∈ Γ.comps, c ∈ Γ'.comps := fun c hc => List.mem_append_left _ hc
  obtain ⟨sT, sP, sL, sK, -⟩ := TerminationC2_sub_facts hmem (n - 1)
  have hde : Γ'.dotExcess = Γ.dotExcess :=
    TerminationC2_dotExcess_of (by
      have hk' : Γ.comps[(i : ℕ)].kind = .xdot := hk
      simp [hΓ', List.filter_append, hk'])
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 ⟨n₀, Γ⟩ _ (StrategyStepB.xdotDup Γ i hk hx hy) hI
    ⟨n₀, Γ'⟩ (List.mem_singleton_self _)
  have hv' := TerminationB_inv_xdotDup hH.le Γ i hk hv
  have hdc' : Γ'.DoublyConnected :=
    TerminationC2_dc_of (fun L hL _ => hL.trans (List.sublist_append_left _ _).subperm)
      (fun u v hm => TerminationC2_sameMol_of (fun c hc _ => hmem' c hc) hm) hdc
  exact ⟨⟨⟨_, TerminationC2_normal_of (fun c hc => ⟨c, hmem c hc, Or.inl rfl⟩)
      (fun c hc => ⟨c, hmem' c hc, Or.inl rfl⟩) hN⟩,
    TerminationC2_ri_lf (sL hL) hI' hv' hdc' (sT hT) (fun h => sP (h9 (hde ▸ h))) (sK hK),
    sL hL, sK hK⟩, TerminationB_runMu_xdotDup n Γ i hk⟩

/-- **The removal of one of two parallel `×`-dotted edges** keeps a graph without labels with the
invariant of a run, and its measure `runMu`. -/
private theorem TerminationC2_lf_drop {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) {Γ : Graph 3 n₀} (i j : Fin Γ.comps.length) (hij : i ≠ j)
    (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) (hx : Γ.comps[i].x.isRight = true)
    (hy : Γ.comps[i].y.isRight = true) (h : TerminationC2_LF n D ⟨n₀, Γ⟩) :
    TerminationC2_LF n D ⟨n₀, ⟨Γ.comps.eraseIdx j, Γ.coeff⟩⟩ ∧
      runMu n (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 n₀) = runMu n Γ := by
  obtain ⟨⟨C, hN⟩, ⟨hI, hv, hdc, hT, -, -, -, -, h9, -⟩, hL, hK⟩ := h
  set Γ' : Graph 3 n₀ := ⟨Γ.comps.eraseIdx j, Γ.coeff⟩ with hΓ'
  have hkj : Γ.comps[(j : ℕ)].kind = .xdot := by
    have : Γ.comps[j].kind = .xdot := by rcases hc with h | h <;> rw [h] <;> exact hk
    exact this
  have hmem : ∀ c ∈ Γ'.comps, c ∈ Γ.comps := fun c hc => List.mem_of_mem_eraseIdx hc
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hiin : Γ.comps[i] ∈ Γ'.comps := List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, hij', rfl⟩
  have hnx : ∀ c ∈ Γ.comps, c.kind ≠ .xdot → c ∈ Γ'.comps := by
    intro c hc hck
    rcases TerminationC2_mem_eraseIdx hc j.2 with h | h
    · exact h
    · exact absurd (h ▸ hkj) hck
  obtain ⟨sT, sP, sL, sK, -⟩ := TerminationC2_sub_facts hmem (n - 1)
  have hde : Γ'.dotExcess = Γ.dotExcess :=
    TerminationC2_dotExcess_of (TerminationC2_filter_eraseIdx _ _ j.2 (by simp [hkj]))
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 ⟨n₀, Γ⟩ _
    (StrategyStepB.xdotDrop Γ i j hij hc hk hx hy) hI ⟨n₀, Γ'⟩ (List.mem_singleton_self _)
  have hv' := TerminationB_inv_xdotDrop hH.le Γ i j hij hc hk hI hv
  have hdc' : Γ'.DoublyConnected := by
    refine TerminationC2_dc_of (fun L hL hLk => TerminationC2_subperm_eraseIdx hL j.2 fun hm => ?_)
      (fun u v hm => TerminationC2_sameMol_of (fun c hc hck => hnx c hc fun h => by
        rw [h] at hck; cases hck) hm) hdc
    rcases hLk _ hm with h | h <;> rw [hkj] at h <;> cases h
  refine ⟨⟨⟨_, TerminationC2_normal_of (fun c hc => ⟨c, hmem c hc, Or.inl rfl⟩)
      (fun c hcm => ?_) hN⟩,
    TerminationC2_ri_lf (sL hL) hI' hv' hdc' (sT hT) (fun h => sP (h9 (hde ▸ h))) (sK hK),
    sL hL, sK hK⟩, TerminationB_runMu_xdotDrop n Γ i j hij hc hk⟩
  rcases TerminationC2_mem_eraseIdx hcm j.2 with h | rfl
  · exact ⟨c, h, Or.inl rfl⟩
  · refine ⟨Γ.comps[i], hiin, ?_⟩
    rcases hc with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hk, h⟩

/-- **The identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1`** keeps a graph without labels with the
invariant of a run, and its measure `runMu`. -/
private theorem TerminationC2_lf_coeff {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) {Γ : Graph 3 n₀} (h : TerminationC2_LF n D ⟨n₀, Γ⟩) :
    TerminationC2_LF n D ⟨n₀, ⟨Γ.comps,
      Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩⟩ ∧
      runMu n (⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩ :
        Graph 3 n₀) = runMu n Γ := by
  obtain ⟨⟨C, hN⟩, ⟨hI, hv, hdc, hT, -, -, -, -, h9, -⟩, hL, hK⟩ := h
  set Γ' : Graph 3 n₀ :=
    ⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩ with hΓ'
  have hmem : ∀ c ∈ Γ'.comps, c ∈ Γ.comps := fun c hc => hc
  obtain ⟨sT, sP, sL, sK, -⟩ := TerminationC2_sub_facts hmem (n - 1)
  have hde : Γ'.dotExcess = Γ.dotExcess := TerminationC2_dotExcess_of rfl
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 ⟨n₀, Γ⟩ _ (StrategyStepB.coeffNorm Γ) hI
    ⟨n₀, Γ'⟩ (List.mem_singleton_self _)
  have hv' := TerminationB_inv_coeffNorm hH.le Γ
    (Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv) hv
  have hdc' : Γ'.DoublyConnected :=
    TerminationC2_dc_of (fun L hL _ => hL) (fun u v hm => TerminationC2_sameMol_of
      (fun c hc _ => hc) hm) hdc
  exact ⟨⟨⟨_, TerminationC2_normal_of (Γ := Γ) (Γ' := Γ') (fun c hc => ⟨c, hc, Or.inl rfl⟩)
      (fun c hc => ⟨c, hc, Or.inl rfl⟩) hN⟩,
    TerminationC2_ri_lf (sL hL) hI' hv' hdc' (sT hT) (fun h => sP (h9 (hde ▸ h))) (sK hK),
    sL hL, sK hK⟩, rfl⟩

/-- **A reordering** keeps a graph without labels with the invariant of a run, and its measure
`runMu`. -/
private theorem TerminationC2_lf_reorder {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) {Γ Γ' : Graph 3 n₀} (hr : Γ.Reorder Γ')
    (h : TerminationC2_LF n D ⟨n₀, Γ⟩) :
    TerminationC2_LF n D ⟨n₀, Γ'⟩ ∧ runMu n Γ' = runMu n Γ := by
  obtain ⟨⟨C, hN⟩, ⟨hI, hv, hdc, hT, -, -, -, -, h9, -⟩, hL, hK⟩ := h
  obtain ⟨π, hiso⟩ := RunClauses_reorder_iso hr
  obtain ⟨sP, sL, -⟩ := TerminationC2_iso_facts hiso
  have hde := RunClauses_iso_dotExcess hiso
  have hK' : Γ'.RunKinds (n - 1) :=
    (TerminationK_runKinds_iff Γ').2 (TerminationK_reorder hr ((TerminationK_runKinds_iff Γ).1 hK))
  exact ⟨⟨⟨C, RunClauses_iso_normal hiso hN⟩,
    TerminationC2_ri_lf (sL hL) (reorder_invRun n₀ D Γ Γ' hr hI)
      (TerminationB_inv_reorder hH.le hr hI hv) (TerminationC2_dc_iso hiso hdc)
      (RunClauses_iso_td hiso hT) (fun h => sP (h9 (hde ▸ h))) hK', sL hL, hK'⟩,
    TerminationB_runMu_reorder n hr⟩

end LF

/-! ## `O_dot` under the steps on `×`-dotted edges and on the coefficient -/

section Transport

open private RunClauses_Iso RunClauses_SwapR RunClauses_eA RunClauses_iso_card
  RunClauses_cand RunClauses_step RunClauses_joined RunClauses_fold RunClauses_sk
  from RBM8D.GlobalExp.RunClauses
open private TerminationB_map_eA_refl from RBM8D.GlobalExp.TerminationB
open private RunClauses_iso_oDotT from RBM8D.GlobalExp.RunClauses
open private TerminationC_iso_drop from RBM8D.GlobalExp.TerminationC

/-- The steps between `O_dot` forms of graphs related by the steps on `×`-dotted edges and on the
coefficient: a renaming and reordering, the duplication and the removal of a `×`-dotted edge
between internal atoms, and the identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1`. -/
private inductive TerminationC2_PStep :
    (Σ n₀ : ℕ, Graph 3 n₀) → (Σ n₀ : ℕ, Graph 3 n₀) → Prop
  | iso {m m' : ℕ} {Γ : Graph 3 m} {Γ' : Graph 3 m'} (e : Fin m ≃ Fin m') :
      RunClauses_Iso e Γ Γ' → TerminationC2_PStep ⟨m, Γ⟩ ⟨m', Γ'⟩
  | dup {m : ℕ} (Γ : Graph 3 m) (i : Fin Γ.comps.length) :
      Γ.comps[i].kind = .xdot → Γ.comps[i].x.isRight = true → Γ.comps[i].y.isRight = true →
      TerminationC2_PStep ⟨m, Γ⟩ ⟨m, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩
  | drop {m : ℕ} (Γ : Graph 3 m) (i j : Fin Γ.comps.length) : i ≠ j →
      (Γ.comps[j] = Γ.comps[i] ∨
        Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x }) →
      Γ.comps[i].kind = .xdot → Γ.comps[i].x.isRight = true → Γ.comps[i].y.isRight = true →
      TerminationC2_PStep ⟨m, Γ⟩ ⟨m, ⟨Γ.comps.eraseIdx j, Γ.coeff⟩⟩
  | coeff {m : ℕ} (Γ : Graph 3 m) :
      TerminationC2_PStep ⟨m, Γ⟩ ⟨m, ⟨Γ.comps,
        Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩⟩

/-- A reordering of the components is a renaming and reordering. -/
private theorem TerminationC2_iso_perm {m : ℕ} {Γ Γ' : Graph 3 m} (hc : Γ'.coeff = Γ.coeff)
    (hp : Γ.comps.Perm Γ'.comps) : RunClauses_Iso (Equiv.refl (Fin m)) Γ Γ' := by
  have hmap : Γ.comps.map (Comp.map (RunClauses_eA (Equiv.refl (Fin m)))) = Γ.comps := by
    rw [List.map_congr_left (fun c _ => TerminationB_map_eA_refl c), List.map_id']
  exact ⟨hc, Γ.comps, by rw [hmap]; exact List.forall₂_same.2 fun _ _ => Or.inl rfl, hp⟩

/-- **The invariant along the steps between `O_dot` forms** ([II, Lemma 6.8]): a graph without
labels with the invariant of a run keeps it, and its measure `runMu`, along `TerminationC2_PStep`. -/
private theorem TerminationC2_PStep.lf {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) {a b : Σ n₀ : ℕ, Graph 3 n₀}
    (hs : TerminationC2_PStep a b) (h : TerminationC2_LF n D a) :
    TerminationC2_LF n D b ∧ runMu n b.2 = runMu n a.2 := by
  cases hs with
  | iso e hiso =>
    rename_i m m' Γ Γ'
    obtain rfl := RunClauses_iso_card hiso
    exact TerminationC2_lf_reorder hH (Γ := Γ) (Γ' := Γ') ⟨hiso.1, e, hiso.2⟩ h
  | dup Γ i hk hx hy => exact TerminationC2_lf_dup hH i hk hx hy h
  | drop Γ i j hij hc hk hx hy => exact TerminationC2_lf_drop hH i j hij hc hk hx hy h
  | coeff Γ => exact TerminationC2_lf_coeff hH h

/-- The invariant along chains of steps between `O_dot` forms. -/
private theorem TerminationC2_PStep.lf_chain {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) {a b : Σ n₀ : ℕ, Graph 3 n₀}
    (hs : Relation.ReflTransGen TerminationC2_PStep a b) (h : TerminationC2_LF n D a) :
    TerminationC2_LF n D b ∧ runMu n b.2 = runMu n a.2 := by
  induction hs with
  | refl => exact ⟨h, rfl⟩
  | tail _ hst ih =>
    obtain ⟨h1, e1⟩ := ih
    obtain ⟨h2, e2⟩ := hst.lf hH h1
    exact ⟨h2, e2.trans e1⟩

/-- The roots of the blocks of the internal atoms for the representative map `rep`. -/
private def TerminationC2_roots {k n : ℕ} (rep : Atom k n → Atom k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => rep (Sum.inr i)).dedup

/-- The atom map of `O_merge` for the representative map `rep`. -/
private def TerminationC2_mf {k n : ℕ} (rep : Atom k n → Atom k n) :
    Atom k n → Atom k (TerminationC2_roots rep).length
  | .inl a => .inl a
  | .inr i => .inr ⟨(TerminationC2_roots rep).idxOf (rep (.inr i)),
      List.idxOf_lt_length_of_mem
        (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩

/-- The image of a component under `O_merge` for the representative map `rep`. -/
private def TerminationC2_mc {k n : ℕ} (rep : Atom k n → Atom k n) (c : Comp (Atom k n)) :
    Option (Comp (Atom k (TerminationC2_roots rep).length)) :=
  if c.kind == .dot && TerminationC2_mf rep c.x == TerminationC2_mf rep c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map (TerminationC2_mf rep) with kind := c.kind.toWeight, y := TerminationC2_mf rep c.x }
  else some (c.map (TerminationC2_mf rep))

/-- `O_merge` with a given partition into blocks (the body of `Graph.mergeT`). -/
private def TerminationC2_mergeP {k n : ℕ} (P : List (List (Atom k n)))
    (cs : List (Comp (Atom k n))) (co : Coeff) : Option (Tracked k n) :=
  if cs.any (fun c => c.kind == .xdot && blockRep P c.x == blockRep P c.y) then none else
  some ⟨(TerminationC2_roots (blockRep P)).length,
    ⟨cs.filterMap (TerminationC2_mc (blockRep P)), co⟩, TerminationC2_mf (blockRep P)⟩

private theorem TerminationC2_mergeT_eq {k n : ℕ} (Γ : Graph k n) :
    Γ.mergeT = TerminationC2_mergeP (dotBlocks (allAtoms k n) Γ.comps) Γ.comps Γ.coeff := by
  unfold Graph.mergeT TerminationC2_mergeP
  dsimp only
  split_ifs <;> rfl

/-- `O_merge` reads the coefficient only as the coefficient of the result. -/
private theorem TerminationC2_mergeP_coeff {k n : ℕ} (P : List (List (Atom k n)))
    (cs : List (Comp (Atom k n))) (co co' : Coeff) :
    TerminationC2_mergeP P cs co' =
      (TerminationC2_mergeP P cs co).map fun t => ⟨t.nOut, ⟨t.g.comps, co'⟩, t.f⟩ := by
  unfold TerminationC2_mergeP
  split_ifs <;> rfl

/-- The blocks do not read a component that is not a dotted edge. -/
private theorem TerminationC2_dotBlocks_ins {k n : ℕ} (as : List (Atom k n))
    (L₁ L₂ : List (Comp (Atom k n))) {d : Comp (Atom k n)} (hd : d.kind ≠ .dot) :
    dotBlocks as (L₁ ++ [d] ++ L₂) = dotBlocks as (L₁ ++ L₂) := by
  unfold dotBlocks
  rw [List.foldl_append, List.foldl_append, List.foldl_append]
  simp [hd]

/-- **`O_merge` with one more copy of a `×`-dotted edge** of the first part: both results are
`none`, or the second is the first with one more copy of a `×`-dotted edge between internal
atoms, up to order. -/
private theorem TerminationC2_mergeP_ins {n : ℕ} (P : List (List (Atom 3 n)))
    (L₁ L₂ : List (Comp (Atom 3 n))) {d : Comp (Atom 3 n)} (hd : d ∈ L₁) (hk : d.kind = .xdot)
    (hx : d.x.isRight = true) (hy : d.y.isRight = true) (co : Coeff) :
    (TerminationC2_mergeP P (L₁ ++ [d] ++ L₂) co = none ↔
      TerminationC2_mergeP P (L₁ ++ L₂) co = none) ∧
    ∀ t t'', TerminationC2_mergeP P (L₁ ++ L₂) co = some t →
      TerminationC2_mergeP P (L₁ ++ [d] ++ L₂) co = some t'' →
      Relation.ReflTransGen TerminationC2_PStep ⟨t.nOut, t.g⟩ ⟨t''.nOut, t''.g⟩ ∧
      Relation.ReflTransGen TerminationC2_PStep ⟨t''.nOut, t''.g⟩ ⟨t.nOut, t.g⟩ := by
  have hany : ∀ F : Comp (Atom 3 n) → Bool,
      (L₁ ++ [d] ++ L₂).any F = (L₁ ++ L₂).any F := by
    intro F
    simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    cases h : F d
    · simp
    · have : L₁.any F = true := List.any_eq_true.2 ⟨d, hd, h⟩
      simp [this]
  unfold TerminationC2_mergeP
  simp only [hany]
  refine ⟨by split_ifs <;> simp, fun t t'' ht ht'' => ?_⟩
  split_ifs at ht with hc
  rw [ite_cond_eq_false _ _ (eq_false hc)] at ht''
  obtain rfl := Option.some.inj ht
  obtain rfl := Option.some.inj ht''
  set rep := blockRep P with hrep
  set f := TerminationC2_mf rep with hf
  set h := TerminationC2_mc rep with hh
  have hdh : h d = some (d.map f) := by
    simp [hh, TerminationC2_mc, hk, Kind.isSolid, hf]
  have hmem : d.map f ∈ L₁.filterMap h := List.mem_filterMap.2 ⟨d, hd, hdh⟩
  set Γ : Graph 3 (TerminationC2_roots rep).length := ⟨(L₁ ++ L₂).filterMap h, co⟩ with hΓ
  have hin : d.map f ∈ Γ.comps := by
    simp only [hΓ, List.filterMap_append]
    exact List.mem_append_left _ hmem
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 hin
  have hfr : ∀ u : Atom 3 n, u.isRight = true → (f u).isRight = true := by
    intro u hu
    cases u with
    | inl a => simp at hu
    | inr j => simp [hf, TerminationC2_mf]
  have hik : Γ.comps[i].kind = .xdot := by rw [hie]; exact hk
  have hix : Γ.comps[i].x.isRight = true := by rw [hie]; exact hfr _ hx
  have hiy : Γ.comps[i].y.isRight = true := by rw [hie]; exact hfr _ hy
  have hperm : ((L₁ ++ [d] ++ L₂).filterMap h).Perm (Γ.comps ++ [Γ.comps[i]]) := by
    rw [hie]
    simp only [hΓ, List.filterMap_append, List.filterMap_cons, hdh, List.filterMap_nil]
    simp only [List.append_assoc, List.singleton_append]
    exact List.Perm.append_left _ (List.perm_append_singleton _ _).symm
  set Γ₁ : Graph 3 (TerminationC2_roots rep).length := ⟨Γ.comps ++ [Γ.comps[i]], co⟩ with hΓ₁
  set Γ'' : Graph 3 (TerminationC2_roots rep).length := ⟨(L₁ ++ [d] ++ L₂).filterMap h, co⟩ with hΓ''
  have s1 : TerminationC2_PStep ⟨(TerminationC2_roots rep).length, Γ⟩ ⟨(TerminationC2_roots rep).length, Γ₁⟩ :=
    TerminationC2_PStep.dup Γ ⟨i, hi⟩ hik hix hiy
  have s2 : TerminationC2_PStep ⟨(TerminationC2_roots rep).length, Γ₁⟩ ⟨(TerminationC2_roots rep).length, Γ''⟩ :=
    TerminationC2_PStep.iso _ (TerminationC2_iso_perm rfl hperm.symm)
  have s3 : TerminationC2_PStep ⟨(TerminationC2_roots rep).length, Γ''⟩ ⟨(TerminationC2_roots rep).length, Γ₁⟩ :=
    TerminationC2_PStep.iso _ (TerminationC2_iso_perm rfl hperm)
  have hlen : Γ.comps.length < Γ₁.comps.length := by simp [hΓ₁]
  have s4 : TerminationC2_PStep ⟨(TerminationC2_roots rep).length, Γ₁⟩
      ⟨(TerminationC2_roots rep).length, ⟨Γ₁.comps.eraseIdx Γ.comps.length, Γ₁.coeff⟩⟩ :=
    TerminationC2_PStep.drop Γ₁ ⟨i, by simp [hΓ₁]; omega⟩ ⟨Γ.comps.length, hlen⟩
      (fun h' => by simp [Fin.ext_iff] at h'; omega)
      (Or.inl (by simp [hΓ₁, List.getElem_append_left hi]))
      (by simpa [hΓ₁, List.getElem_append_left hi] using hik)
      (by simpa [hΓ₁, List.getElem_append_left hi] using hix)
      (by simpa [hΓ₁, List.getElem_append_left hi] using hiy)
  have he : (⟨Γ₁.comps.eraseIdx Γ.comps.length, Γ₁.coeff⟩ : Graph 3 (TerminationC2_roots rep).length) = Γ := by
    simp [hΓ₁, hΓ, List.eraseIdx_append_of_length_le]
  rw [he] at s4
  exact ⟨Relation.ReflTransGen.single s1 |>.tail s2,
    (Relation.ReflTransGen.single s3).tail s4⟩

/-- A list with one more copy of one of its entries satisfies `List.any` for the same tests. -/
private theorem TerminationC2_any_app {α : Type*} {cs : List α} {d : α} (hd : d ∈ cs)
    (F : α → Bool) : (cs ++ [d]).any F = cs.any F := by
  simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  cases h : F d
  · simp
  · simp [List.any_eq_true.2 ⟨d, hd, h⟩]

/-- The pairs to split of `O_dot` do not change with one more copy of a `×`-dotted edge. -/
private theorem TerminationC2_sp_app {n : ℕ} (Γ : Graph 3 n) {d : Comp (Atom 3 n)}
    (hd : d ∈ Γ.comps) : (⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph 3 n).splitPairs = Γ.splitPairs := by
  set Γ'' : Graph 3 n := ⟨Γ.comps ++ [d], Γ.coeff⟩ with hΓ''
  have hj : ∀ p u v, RunClauses_joined Γ'' p u v = RunClauses_joined Γ p u v := by
    intro p u v
    exact TerminationC2_any_app hd _
  have hcand : ∃ L, RunClauses_cand Γ'' = RunClauses_cand Γ ++ L ∧
      ∀ e ∈ L, e ∈ RunClauses_cand Γ := by
    refine ⟨[d].filterMap fun c =>
      if (c.kind.isSolid || c.kind == .xdot) && c.x != c.y then some (c.x, c.y) else none, ?_, ?_⟩
    · simp only [RunClauses_cand, hΓ'', List.filterMap_append]
    · intro e he
      obtain ⟨c, hc, he⟩ := List.mem_filterMap.1 he
      rw [List.mem_singleton.1 hc] at he
      exact List.mem_filterMap.2 ⟨d, hd, he⟩
  obtain ⟨L, hL, hLm⟩ := hcand
  have hfold : ∀ (L : List (Atom 3 n × Atom 3 n)), (∀ e ∈ L, e ∈ RunClauses_cand Γ) →
      ((RunClauses_cand Γ ++ L).foldl RunClauses_step []) =
        (RunClauses_cand Γ).foldl RunClauses_step [] := by
    intro L hL
    induction L using List.reverseRecOn with
    | nil => simp
    | append_singleton L e ih =>
      rw [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (fun e' he' => hL e' (List.mem_append_left _ he'))]
      have he : e ∈ RunClauses_cand Γ := hL e (List.mem_append_right _ (List.mem_singleton_self e))
      have hz := ((RunClauses_fold (RunClauses_cand Γ) [] List.nodup_nil).2 (RunClauses_sk e)).2
        (Or.inr (List.mem_map_of_mem he))
      obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hz
      unfold RunClauses_step
      rw [if_pos]
      refine List.any_eq_true.2 ⟨q, hq, ?_⟩
      simp only [RunClauses_sk, Sym2.eq_iff] at hqe
      rcases hqe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [Prod.ext_iff, h1, h2]
      · simp [Prod.ext_iff, Prod.swap, h1, h2]
  rw [show Γ''.splitPairs = ((RunClauses_cand Γ'').foldl RunClauses_step []).filterMap (fun p =>
      if RunClauses_joined Γ'' Kind.isSolid p.1 p.2 != RunClauses_joined Γ'' (· == .xdot) p.1 p.2
      then some (p.1, p.2, RunClauses_joined Γ'' Kind.isSolid p.1 p.2) else none) from rfl,
    show Γ.splitPairs = ((RunClauses_cand Γ).foldl RunClauses_step []).filterMap (fun p =>
      if RunClauses_joined Γ Kind.isSolid p.1 p.2 != RunClauses_joined Γ (· == .xdot) p.1 p.2
      then some (p.1, p.2, RunClauses_joined Γ Kind.isSolid p.1 p.2) else none) from rfl,
    hL, hfold L hLm]
  simp only [hj]

/-- `O_dot` written out (the definition of `oDotT`). -/
private theorem TerminationC2_oDotT_eq {k n : ℕ} (Γ : Graph k n) : oDotT Γ =
    if 2 ≤ Γ.labels.length ∨ (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) &&
      c.label.isSome) = true then [Tracked.self Γ]
    else if (Γ.splitPairs.isEmpty && !(Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) = true
    then [Tracked.self Γ]
    else Γ.splitPairs.sublists.filterMap fun A => (Γ.dotChoice Γ.splitPairs A).mergeT := rfl

/-- The choice of `O_dot` with one more copy of a component: the kept components, the copy if the
test of `Graph.dotChoice` keeps it, then the same added components with the same coefficient. -/
private theorem TerminationC2_dotChoice_app {k n : ℕ} (Γ : Graph k n) (d : Comp (Atom k n))
    (SP A : List (Atom k n × Atom k n × Bool)) :
    ∃ K Ad co, Γ.dotChoice SP A = ⟨K ++ Ad, co⟩ ∧
      (((⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph k n).dotChoice SP A = ⟨K ++ [d] ++ Ad, co⟩ ∧
          (d ∈ Γ.comps → d ∈ K)) ∨
        (⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph k n).dotChoice SP A = ⟨K ++ Ad, co⟩) := by
  refine ⟨Γ.comps.filter fun c => !(c.kind == .xdot && SP.any fun p => !p.2.2 &&
      ((p.1 == c.x && p.2.1 == c.y) || (p.1 == c.y && p.2.1 == c.x))), _, _, rfl, ?_⟩
  unfold Graph.dotChoice
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  split_ifs with hq
  · exact Or.inl ⟨by simp, fun h => List.mem_filter.2 ⟨h, hq⟩⟩
  · exact Or.inr (by simp)

/-- **`O_dot` with one more copy of a `×`-dotted edge between internal atoms**: every form of the
graph with the copy comes from a form of the graph by the steps `TerminationC2_PStep`, and every
form of the graph comes so from a form of the graph with the copy. -/
private theorem TerminationC2_oDotT_app {n : ℕ} (Γ : Graph 3 n) {d : Comp (Atom 3 n)}
    (hd : d ∈ Γ.comps) (hk : d.kind = .xdot) (hl : d.label = none) (hx : d.x.isRight = true)
    (hy : d.y.isRight = true) :
    (∀ t'' ∈ oDotT (⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph 3 n), ∃ t ∈ oDotT Γ,
      Relation.ReflTransGen TerminationC2_PStep ⟨t.nOut, t.g⟩ ⟨t''.nOut, t''.g⟩) ∧
    (∀ t ∈ oDotT Γ, ∃ t'' ∈ oDotT (⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph 3 n),
      Relation.ReflTransGen TerminationC2_PStep ⟨t''.nOut, t''.g⟩ ⟨t.nOut, t.g⟩) := by
  set Γ'' : Graph 3 n := ⟨Γ.comps ++ [d], Γ.coeff⟩ with hΓ''
  have hlab : Γ''.labels = Γ.labels := by
    simp [Graph.labels, hΓ'', List.filterMap_append, hl]
  have hany : ∀ F, Γ''.comps.any F = Γ.comps.any F := fun F => TerminationC2_any_app hd F
  have hsp : Γ''.splitPairs = Γ.splitPairs := TerminationC2_sp_app Γ hd
  -- the relation between the graph and the graph with the copy
  obtain ⟨i, hi, hid⟩ := List.mem_iff_getElem.1 hd
  have hself : Relation.ReflTransGen TerminationC2_PStep ⟨n, Γ⟩ ⟨n, Γ''⟩ ∧
      Relation.ReflTransGen TerminationC2_PStep ⟨n, Γ''⟩ ⟨n, Γ⟩ := by
    have s1 := TerminationC2_PStep.dup Γ ⟨i, hi⟩ (by simpa [hid] using hk)
      (by simpa [hid] using hx) (by simpa [hid] using hy)
    have e1 : (⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩ : Graph 3 n) = Γ'' := by simp [hΓ'', hid]
    simp only [Fin.getElem_fin] at s1
    rw [e1] at s1
    have hlen : Γ.comps.length < Γ''.comps.length := by simp [hΓ'']
    have s2 := TerminationC2_PStep.drop Γ'' ⟨i, by simp [hΓ'']; omega⟩ ⟨Γ.comps.length, hlen⟩
      (fun h' => by simp [Fin.ext_iff] at h'; omega)
      (Or.inl (by simp [hΓ'', List.getElem_append_left hi, hid]))
      (by simpa [hΓ'', List.getElem_append_left hi, hid] using hk)
      (by simpa [hΓ'', List.getElem_append_left hi, hid] using hx)
      (by simpa [hΓ'', List.getElem_append_left hi, hid] using hy)
    have e2 : (⟨Γ''.comps.eraseIdx Γ.comps.length, Γ''.coeff⟩ : Graph 3 n) = Γ := by
      simp [hΓ'', List.eraseIdx_append_of_length_le]
    rw [e2] at s2
    exact ⟨Relation.ReflTransGen.single s1, Relation.ReflTransGen.single s2⟩
  -- the choices of `O_dot`
  have hch : ∀ A, ((Γ''.dotChoice Γ.splitPairs A).mergeT = none ↔
      (Γ.dotChoice Γ.splitPairs A).mergeT = none) ∧
      ∀ t t'', (Γ.dotChoice Γ.splitPairs A).mergeT = some t →
        (Γ''.dotChoice Γ.splitPairs A).mergeT = some t'' →
        Relation.ReflTransGen TerminationC2_PStep ⟨t.nOut, t.g⟩ ⟨t''.nOut, t''.g⟩ ∧
        Relation.ReflTransGen TerminationC2_PStep ⟨t''.nOut, t''.g⟩ ⟨t.nOut, t.g⟩ := by
    intro A
    obtain ⟨K, Ad, co, e1, e2⟩ := TerminationC2_dotChoice_app Γ d Γ.splitPairs A
    rw [e1]
    rcases e2 with ⟨e2, hdK⟩ | e2
    · rw [e2]
      have hd₁ : d ∈ K := hdK hd
      rw [TerminationC2_mergeT_eq, TerminationC2_mergeT_eq]
      simp only
      rw [TerminationC2_dotBlocks_ins _ K Ad (by rw [hk]; simp)]
      exact TerminationC2_mergeP_ins _ K Ad hd₁ hk hx hy co
    · rw [e2]
      refine ⟨Iff.rfl, fun t t'' h1 h2 => ?_⟩
      rw [h1] at h2
      obtain rfl := Option.some.inj h2
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  rw [TerminationC2_oDotT_eq Γ'', TerminationC2_oDotT_eq Γ, hlab, hany, hany, hsp]
  split_ifs with c1 c2
  · simp only [List.mem_singleton, exists_eq_left, forall_eq]
    exact ⟨hself.1, hself.2⟩
  · simp only [List.mem_singleton, exists_eq_left, forall_eq]
    exact ⟨hself.1, hself.2⟩
  · constructor
    · intro t'' ht''
      obtain ⟨A, hA, hm''⟩ := List.mem_filterMap.1 ht''
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 fun h0 => by
        rw [← (hch A).1] at h0; rw [h0] at hm''; cases hm''
      exact ⟨t, List.mem_filterMap.2 ⟨A, hA, ht⟩, ((hch A).2 t t'' ht hm'').1⟩
    · intro t ht
      obtain ⟨A, hA, hm⟩ := List.mem_filterMap.1 ht
      obtain ⟨t'', ht''⟩ := Option.ne_none_iff_exists'.1 fun h0 => by
        rw [(hch A).1] at h0; rw [h0] at hm; cases hm
      exact ⟨t'', List.mem_filterMap.2 ⟨A, hA, ht''⟩, ((hch A).2 t t'' hm ht'').2⟩

/-- **`O_dot` after the identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1`**: every form is a form of the
graph with the identification applied to its coefficient. -/
private theorem TerminationC2_oDotT_coeff {n : ℕ} (Γ : Graph 3 n) :
    ∀ t' ∈ oDotT (⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb *
      MvPolynomial.X .mBarInv⟩ : Graph 3 n), ∃ t ∈ oDotT Γ,
      Relation.ReflTransGen TerminationC2_PStep ⟨t.nOut, t.g⟩ ⟨t'.nOut, t'.g⟩ := by
  set K : Coeff := cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv with hK
  set Γ' : Graph 3 n := ⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb *
    MvPolynomial.X .mBarInv⟩ with hΓ'
  intro t' ht'
  rw [TerminationC2_oDotT_eq] at ht'
  rw [show oDotT Γ = _ from TerminationC2_oDotT_eq Γ]
  change t' ∈ (if 2 ≤ Γ.labels.length ∨ (Γ.comps.any fun c => (c.kind == .dot ||
      c.kind == .xdot) && c.label.isSome) = true then [Tracked.self Γ']
    else if (Γ.splitPairs.isEmpty && !(Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) = true
    then [Tracked.self Γ']
    else Γ.splitPairs.sublists.filterMap fun A => (Γ'.dotChoice Γ.splitPairs A).mergeT) at ht'
  split_ifs at ht' ⊢ with c1 c2
  · rw [List.mem_singleton.1 ht']
    exact ⟨_, List.mem_singleton_self _, Relation.ReflTransGen.single (TerminationC2_PStep.coeff Γ)⟩
  · rw [List.mem_singleton.1 ht']
    exact ⟨_, List.mem_singleton_self _, Relation.ReflTransGen.single (TerminationC2_PStep.coeff Γ)⟩
  · obtain ⟨A, hA, hm⟩ := List.mem_filterMap.1 ht'
    have e1 : Γ'.dotChoice Γ.splitPairs A = ⟨(Γ.dotChoice Γ.splitPairs A).comps,
        (Γ.dotChoice Γ.splitPairs A).coeff * K⟩ := by
      unfold Graph.dotChoice
      simp only [hΓ', hK, Graph.mk.injEq, true_and]
      ring
    rw [e1, TerminationC2_mergeT_eq] at hm
    simp only at hm
    rw [TerminationC2_mergeP_coeff _ _ (Γ.dotChoice Γ.splitPairs A).coeff] at hm
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hm
    have ht' : (Γ.dotChoice Γ.splitPairs A).mergeT = some t := by
      rw [TerminationC2_mergeT_eq]; exact ht
    refine ⟨t, List.mem_filterMap.2 ⟨A, hA, ht'⟩, Relation.ReflTransGen.single ?_⟩
    have hc : t.g.coeff = (Γ.dotChoice Γ.splitPairs A).coeff := by
      unfold TerminationC2_mergeP at ht
      split_ifs at ht
      obtain rfl := Option.some.inj ht
      rfl
    have := TerminationC2_PStep.coeff t.g
    rw [hc] at this
    simp only [hK, ← mul_assoc] at this ⊢
    exact this

/-- **`O_dot` after the removal of one of two parallel `×`-dotted edges between internal atoms**:
every form comes from a form of the graph by the steps `TerminationC2_PStep`. -/
private theorem TerminationC2_oDotT_drop {n : ℕ} (Γ : Graph 3 n) (i j : Fin Γ.comps.length)
    (hij : i ≠ j) (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) (hl : Γ.comps[i].label = none)
    (hx : Γ.comps[i].x.isRight = true) (hy : Γ.comps[i].y.isRight = true) :
    ∀ t' ∈ oDotT (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 n), ∃ t ∈ oDotT Γ,
      Relation.ReflTransGen TerminationC2_PStep ⟨t.nOut, t.g⟩ ⟨t'.nOut, t'.g⟩ := by
  intro t' ht'
  set Γ' : Graph 3 n := ⟨Γ.comps.eraseIdx j, Γ.coeff⟩ with hΓ'
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hin : Γ.comps[i] ∈ Γ'.comps := List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, hij', rfl⟩
  obtain ⟨t'', ht'', h2⟩ := (TerminationC2_oDotT_app Γ' hin hk hl hx hy).2 t' ht'
  have hiso := TerminationC_iso_drop Γ i j hc hk
  obtain ⟨t, ht, σ, hσ⟩ := RunClauses_iso_oDotT hiso ht''
  exact ⟨t, ht, (Relation.ReflTransGen.single (TerminationC2_PStep.iso σ hσ)).trans h2⟩

/-- The steps on `×`-dotted edges and on the coefficient that a selector may take at a graph of
Steps 2–3 before `O_dot`: the identification `m · m⁻¹ · m̄ · m̄⁻¹ = 1`, the duplication of a
`×`-dotted edge without label between internal atoms, and the removal of one of two parallel such
edges. -/
private inductive TerminationC2_NuStep :
    (Σ n₀ : ℕ, Graph 3 n₀) → (Σ n₀ : ℕ, Graph 3 n₀) → Prop
  | coeff {m : ℕ} (Γ : Graph 3 m) :
      TerminationC2_NuStep ⟨m, Γ⟩ ⟨m, ⟨Γ.comps,
        Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩⟩
  | dup {m : ℕ} (Γ : Graph 3 m) (i : Fin Γ.comps.length) :
      Γ.comps[i].kind = .xdot → Γ.comps[i].label = none → Γ.comps[i].x.isRight = true →
      Γ.comps[i].y.isRight = true →
      TerminationC2_NuStep ⟨m, Γ⟩ ⟨m, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩
  | drop {m : ℕ} (Γ : Graph 3 m) (i j : Fin Γ.comps.length) : i ≠ j →
      (Γ.comps[j] = Γ.comps[i] ∨
        Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x }) →
      Γ.comps[i].kind = .xdot → Γ.comps[i].label = none → Γ.comps[i].x.isRight = true →
      Γ.comps[i].y.isRight = true →
      TerminationC2_NuStep ⟨m, Γ⟩ ⟨m, ⟨Γ.comps.eraseIdx j, Γ.coeff⟩⟩

/-- **`O_dot` along the steps `TerminationC2_NuStep`**: every form of the last graph comes from a
form of the first by the steps `TerminationC2_PStep`. -/
private theorem TerminationC2_oDotT_chain {a b : Σ n₀ : ℕ, Graph 3 n₀}
    (h : Relation.ReflTransGen TerminationC2_NuStep a b) :
    ∀ t' ∈ oDotT b.2, ∃ t ∈ oDotT a.2,
      Relation.ReflTransGen TerminationC2_PStep ⟨t.nOut, t.g⟩ ⟨t'.nOut, t'.g⟩ := by
  induction h with
  | refl => exact fun t' ht' => ⟨t', ht', Relation.ReflTransGen.refl⟩
  | @tail b' c' _ hs ih =>
    intro t'' ht''
    have step : ∃ t' ∈ oDotT b'.2, Relation.ReflTransGen TerminationC2_PStep ⟨t'.nOut, t'.g⟩
        ⟨t''.nOut, t''.g⟩ := by
      cases hs with
      | coeff Γ => exact TerminationC2_oDotT_coeff Γ t'' ht''
      | dup Γ i hk hl hx hy =>
        exact (TerminationC2_oDotT_app Γ (List.getElem_mem i.2) hk hl hx hy).1 t'' ht''
      | drop Γ i j hij hc hk hl hx hy =>
        exact TerminationC2_oDotT_drop Γ i j hij hc hk hl hx hy t'' ht''
    obtain ⟨t', ht', h2⟩ := step
    obtain ⟨t, ht, h1⟩ := ih t' ht'
    exact ⟨t, ht, h1.trans h2⟩

/-- A graph without labels after the steps `TerminationC2_NuStep` comes from a graph without
labels. -/
private theorem TerminationC2_NuStep.labelFree {a b : Σ n₀ : ℕ, Graph 3 n₀}
    (h : Relation.ReflTransGen TerminationC2_NuStep a b) (hb : b.2.LabelFree) : a.2.LabelFree := by
  induction h with
  | refl => exact hb
  | tail _ hs ih =>
    apply ih
    cases hs with
    | coeff Γ => exact hb
    | dup Γ i hk hl hx hy => exact fun c hc => hb c (List.mem_append_left _ hc)
    | drop Γ i j hij hc hk hl hx hy =>
      intro c hcm
      rcases TerminationC2_mem_eraseIdx hcm j.2 with h | rfl
      · exact hb c h
      · rcases hc with h | h
        · simp only [Fin.getElem_fin] at h
          rw [h]; exact hl
        · simp only [Fin.getElem_fin] at h
          rw [h]; exact hl

end Transport

/-! ## The substitution of Steps 2–3 and its `O_dot` forms -/

section Subst

open private TerminationK_runKinds_iff TerminationK_oDotT from RBM8D.GlobalExp.TerminationK
open private GlobalGoodB_oDot_label GlobalGoodB_glue_label GlobalGoodB_dotExcess_zero
  from RBM8D.GlobalExp.GlobalGoodB
open private SubstDC_swap_noLabDot from RBM8D.GlobalExp.SubstDC
open private TerminationC_label_eq from RBM8D.GlobalExp.TerminationC

/-- `O_dot` keeps the absence of labelled dotted and `×`-dotted edges: the added edges carry no
label, and `O_merge` keeps the kind and the label of every edge that is not a solid edge. -/
private theorem TerminationC2_oDotT_noLabDot {k n : ℕ} {Γ : Graph k n} (h : Γ.NoLabDot) :
    ∀ t ∈ oDotT Γ, t.g.NoLabDot := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact h
  rw [TerminationC2_mergeT_eq] at hm
  unfold TerminationC2_mergeP at hm
  split_ifs at hm
  obtain rfl := Option.some.inj hm
  intro c' hc' hk
  obtain ⟨c, hc, hcc⟩ := List.mem_filterMap.1 hc'
  have hcl : (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
    intro hk'
    unfold Graph.dotChoice at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact h c (List.mem_of_mem_filter hc) hk'
    · obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 hc
      split_ifs at hp <;> (obtain rfl := Option.some.inj hp; rfl)
  unfold TerminationC2_mc at hcc
  split_ifs at hcc with h1 h2
  · obtain rfl := Option.some.inj hcc
    exfalso
    have hs : c.kind.isSolid = true := by
      simp only [Bool.and_eq_true] at h2; exact h2.1
    rcases hk with hk | hk <;> revert hk hs <;> cases c.kind <;> simp [Kind.toWeight, Kind.isSolid]
  · obtain rfl := Option.some.inj hcc
    simp only [Comp.map] at hk ⊢
    rw [hcl hk]
    rfl

/-- **`O_dot` keeps the doubly connected property** ([I, Lemma 3.3]) and sends internal atoms to
internal atoms: a choice of `O_dot` keeps every component other than a `×`-dotted edge and adds
dotted and `×`-dotted edges, and `O_merge` keeps the doubly connected property. -/
private theorem TerminationC2_oDotT_dc {n : ℕ} {Γ : Graph 3 n} (h : Γ.DoublyConnected) :
    ∀ t ∈ oDotT Γ, t.g.DoublyConnected ∧ ∀ u, (t.f u).isRight = u.isRight := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact ⟨h, fun u => rfl⟩
  have hdc : (Γ.dotChoice Γ.splitPairs A).DoublyConnected := by
    refine TerminationC2_dc_of (fun L hL hLk => ?_) (fun u v hm' => TerminationC2_sameMol_of
      (fun c hc hk => ?_) hm') h
    · have h1 : L.Subperm (Γ.comps.filter fun c => !(c.kind == .xdot && Γ.splitPairs.any
          fun p => !p.2.2 && ((p.1 == c.x && p.2.1 == c.y) || (p.1 == c.y && p.2.1 == c.x)))) := by
        have := hL.filter (fun c => !(c.kind == .xdot && Γ.splitPairs.any
          fun p => !p.2.2 && ((p.1 == c.x && p.2.1 == c.y) || (p.1 == c.y && p.2.1 == c.x))))
        rwa [List.filter_eq_self.2 fun c hc => by
          rcases hLk c hc with hk | hk <;> revert hk <;> cases c.kind <;>
            simp [Kind.isDiffusive, Kind.isBlue]] at this
      exact h1.trans (List.sublist_append_left _ _).subperm
    · unfold Graph.dotChoice
      refine List.mem_append_left _ (List.mem_filter.2 ⟨hc, ?_⟩)
      revert hk; cases c.kind <;> simp [Kind.joinsMol]
  obtain ⟨h1, h2⟩ := Graph.Step3DCS.mergeT (Graph.doublyConnected_dcs hdc) hm
  exact ⟨h1.doublyConnected, h2⟩

/-- A substituted graph has no labelled dotted or `×`-dotted edge when the substituted graph has
none and the host carries no label. -/
private theorem TerminationC2_glue_noLabDot {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}
    {g : Graph 3 n'} (hL : H.LabelFree) (h : g.NoLabDot) :
    (H.glue x y₁ y₂ g.swapSolid).NoLabDot := by
  intro c hc hk
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    simp [Comp.map, hL c₀ hc₀]
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    simp only [Comp.map] at hk ⊢
    rw [SubstDC_swap_noLabDot h c₀ hc₀ hk]
    rfl

/-- A list whose entries are all equal has at most one entry without repetition. -/
private theorem TerminationC2_dedup_le_one {α : Type*} [DecidableEq α] {L : List α}
    (h : ∀ a ∈ L, ∀ b ∈ L, a = b) : L.dedup.length ≤ 1 := by
  rcases L with - | ⟨a, L⟩
  · simp
  · have hsub : (a :: L).dedup ⊆ [a] := fun b hb => List.mem_singleton.2
      (h b (List.mem_dedup.1 hb) a List.mem_cons_self)
    exact (List.Subperm.length_le ((List.nodup_dedup _).subperm hsub)).trans (by simp)

/-- **The labels of the `O_dot` forms of a substituted graph** are images of the labels of the
substituted graph `g`, with the same letter `P` or `Q`: at most one label when `g` has at most one,
and no `P` label when `g` has none. -/
private theorem TerminationC2_piece_labels {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}
    {g : Graph 3 n'} (hL : H.LabelFree) {t : Tracked 3 (m + n')}
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g.swapSolid)) :
    (g.labels.length ≤ 1 → t.g.labels.length ≤ 1) ∧
      ((∀ c ∈ g.comps, ∀ u, c.label ≠ some (.P, u)) →
        ∀ c ∈ t.g.comps, ∀ u, c.label ≠ some (.P, u)) := by
  have key : ∀ c' ∈ t.g.comps, ∀ l, c'.label = some l →
      ∃ c₀ ∈ g.comps, ∃ u, c₀.label = some (l.1, u) ∧ l.2 = t.f (glueAtom x y₁ y₂ u) := by
    intro c' hc' l hl
    obtain ⟨c, hc, w, hcw, hlw⟩ := GlobalGoodB_oDot_label ht hc' hl
    obtain ⟨c₀, hc₀, u, hu, hwu⟩ := GlobalGoodB_glue_label hL hc hcw
    exact ⟨c₀, hc₀, u, hu, by rw [hlw, ← show (l.1, w).2 = w from rfl, hwu]⟩
  refine ⟨fun h1 => ?_, fun hP c' hc' u hu => ?_⟩
  · unfold Graph.labels
    refine TerminationC2_dedup_le_one fun a ha b hb => ?_
    obtain ⟨c₁, hc₁, h₁⟩ := List.mem_filterMap.1 ha
    obtain ⟨c₂, hc₂, h₂⟩ := List.mem_filterMap.1 hb
    obtain ⟨d₁, hd₁, u₁, hu₁, e₁⟩ := key c₁ hc₁ a h₁
    obtain ⟨d₂, hd₂, u₂, hu₂, e₂⟩ := key c₂ hc₂ b h₂
    have := TerminationC_label_eq h1 hd₁ hd₂ hu₁ hu₂
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 (by rw [e₁, e₂, this.2])
  · obtain ⟨c₀, hc₀, w, hw, -⟩ := key c' hc' _ hu
    exact hP c₀ hc₀ w hw

/-- A graph with at most one internal atom is doubly connected (the nets span nothing). -/
private theorem TerminationC2_dc_small {k n : ℕ} (Γ : Graph k n) (hn : n ≤ 1) :
    Γ.DoublyConnected := by
  have hp : (Γ.net ∅).Preconnected := fun a b => by
    have : a = b := Fin.ext (by have := a.2; have := b.2; omega)
    subst this; rfl
  exact ⟨∅, ∅, Finset.disjoint_empty_left _, by simp, by simp, hp, hp⟩

/-- The graph `m Θ^{[o]}_{a b₁} Ḡ_{b₁ b₂}` has no label. -/
private theorem TerminationC2_thetaLabelGraph_lf (o : List ℕ) : (thetaLabelGraph o).LabelFree := by
  intro c hc
  simp only [thetaLabelGraph, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

/-- The sources of the substituted graphs: the graphs of rows (1), (2) of [II, Lemma 6.5], of `A`,
of `Q` and of `Err`. -/
private theorem TerminationC2_mem_tSubst {n : ℕ} {𝒯 : TRec} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hg : g ∈ 𝒯.tSubst n) :
    g ∈ leadExp ++ sigmaTExp n ++ 𝒯.R ++ tVarCorr ∨ g ∈ 𝒯.A ∨ g ∈ 𝒯.Q ∨ g ∈ 𝒯.Err := by
  simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg ⊢
  tauto

/-- **The graphs substituted in Steps 2–3** (the right side of [II, (4.15)]): doubly connected,
without internal atom, a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` or rooted at the external atoms,
without labelled dotted edges, with at most one label, and without labels unless they are graphs
of `Q` or of `Err`. -/
private theorem TerminationC2_tSubst {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.tSubst (n - 1)) :
    g.2.DoublyConnected ∧ (g.1 = 0 ∨ g.2.DiagRecoll ∨ g.2.RootedAtExt) ∧ g.2.NoLabDot ∧
      g.2.labels.length ≤ 1 ∧ (g ∈ 𝒯.Q ∨ g ∈ 𝒯.Err ∨ g.2.LabelFree) := by
  obtain ⟨-, hT⟩ := hH
  have hSh := hT.2.2.2.1
  have hDef := hT.2.2.2.2
  have lf : g.2.LabelFree → g.2.NoLabDot ∧ g.2.labels.length ≤ 1 := by
    intro hL
    refine ⟨fun c hc _ => hL c hc, ?_⟩
    have : g.2.comps.filterMap Comp.label = [] := List.filterMap_eq_nil_iff.2 fun c hc => hL c hc
    simp [Graph.labels, this]
  have root4 : g ∈ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err → g.1 = 0 ∨ g.2.DiagRecoll ∨ g.2.RootedAtExt := by
    intro hm
    by_cases h0 : g.1 = 0
    · exact Or.inl h0
    by_cases hD : g.2.DiagRecoll
    · exact Or.inr (Or.inl hD)
    exact Or.inr (Or.inr (hDef.2.2.2.2.2.2.1 g hm h0 hD))
  simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg
  rcases hg with (((((hg | hg) | hg) | hg) | hg) | hg) | hg
  · simp only [leadExp, List.mem_singleton] at hg
    subst hg
    exact ⟨TerminationC2_dc_small _ (by simp), Or.inl rfl,
      lf (TerminationC2_thetaLabelGraph_lf []) |>.1, lf (TerminationC2_thetaLabelGraph_lf []) |>.2,
      Or.inr (Or.inr (TerminationC2_thetaLabelGraph_lf []))⟩
  · obtain ⟨o, -, rfl⟩ := List.mem_map.1 hg
    exact ⟨TerminationC2_dc_small _ (by simp), Or.inl rfl,
      lf (TerminationC2_thetaLabelGraph_lf o) |>.1, lf (TerminationC2_thetaLabelGraph_lf o) |>.2,
      Or.inr (Or.inr (TerminationC2_thetaLabelGraph_lf o))⟩
  · have hRAQ : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by simp [hg]
    have h4 : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
    obtain ⟨-, -, hAt, hDC⟩ := hSh.1.1 g hRAQ
    obtain ⟨hTD, hX, hNL, hlab⟩ := hDef.2.1 g h4
    obtain ⟨-, hE, hC⟩ := hDef.1.1 g hg
    refine ⟨hDC, ?_, hNL, hlab, Or.inr (Or.inr (hSh.2.1 g hg).1)⟩
    by_cases h0 : g.1 = 0
    · exact Or.inl h0
    by_cases hD : g.2.DiagRecoll
    · exact Or.inr (Or.inl hD)
    exact Or.inr (Or.inr (rootedAtExt_of_extClause g.1 g.2 hE hC hTD hAt hX hD))
  · have hRAQ : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by simp [hg]
    have h4 : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
    obtain ⟨-, -, hNL, hlab⟩ := hDef.2.1 g h4
    exact ⟨(hSh.1.1 g hRAQ).2.2.2, root4 (by simp [hg]), hNL, hlab,
      Or.inr (Or.inr (hSh.2.2.1 g hg).1)⟩
  · have hRAQ : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by simp [hg]
    have h4 : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
    obtain ⟨-, -, hNL, hlab⟩ := hDef.2.1 g h4
    exact ⟨(hSh.1.1 g hRAQ).2.2.2, root4 (by simp [hg]), hNL, hlab, Or.inl hg⟩
  · have h4 : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
    obtain ⟨-, -, hNL, hlab⟩ := hDef.2.1 g h4
    exact ⟨(hSh.1.2 g hg).2.2.2, root4 (by simp [hg]), hNL, hlab, Or.inr (Or.inl hg)⟩
  · have hc : ∀ g ∈ tVarCorr, g.1 = 1 ∧ g.2.LabelFree ∧ (g.2.DiagRecoll ∨ g.2.RootedAtExt) := by
      unfold Graph.LabelFree
      decide +kernel
    obtain ⟨h1, hL, hr⟩ := hc g hg
    exact ⟨TerminationC2_dc_small _ (by omega), Or.inr hr, (lf hL).1, (lf hL).2,
      Or.inr (Or.inr hL)⟩

/-- The facts of a host `G = H.glue x y₁ y₂ (tVar true)` of Steps 2–3 read on the `O_dot` forms of
the substituted graphs: the order `≤ D` and `≤ n`, the graph-only premises of the substitution,
the invariant `Graph.InvB'` and plainness. -/
private def TerminationC2_Host (n D : ℕ) {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) : Prop :=
  ¬ (D : ℤ) < (H.glue x y₁ y₂ (tVar true)).ord ∧ (H.glue x y₁ y₂ (tVar true)).ord ≤ n ∧
    TerminationC_HostPrem H x y₁ y₂ ∧ (H.glue x y₁ y₂ (tVar true)).InvB' ∧
    (H.glue x y₁ y₂ (tVar true)).Plain

/-- **The `O_dot` forms of a substituted graph** ([II, Lemma 6.5] (1)–(5), [II, Lemma 6.8]): normal
regular without dotted edges, with the invariant of a run, the run kinds, doubly connected, the
leaf invariants, only diffusive edges at `⊗`, an internal atom, no labelled dotted edge and at
most one label; without labels they have a smaller `runMu` than the host; with labels they come
from a graph of `Q` (no `P` label, the clauses of the class `Q` on `Q`-graphs) or have scaling
order `> D`. -/
private theorem TerminationC2_piece {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.tSubst (n - 1))
    (hIt : (H.glue x y₁ y₂ g.2.swapSolid).InvRun D)
    (hKt : (H.glue x y₁ y₂ g.2.swapSolid).RunKinds (n - 1))
    {t : Tracked 3 (m + g.1)} (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) :
    (∃ C, t.g.Normal C) ∧ t.g.DotFree ∧ t.g.InvRun D ∧ t.g.RunKinds (n - 1) ∧
      t.g.DoublyConnected ∧ TerminationB_Inv n D t.g ∧ t.g.TensorDiffusive ∧ t.nOut ≠ 0 ∧
      t.g.NoLabDot ∧ t.g.labels.length ≤ 1 ∧
      (t.g.LabelFree → runMu n t.g < runMu n (H.glue x y₁ y₂ (tVar true))) ∧
      (¬ t.g.LabelFree → (g ∈ 𝒯.Q ∧ (∀ c ∈ t.g.comps, ∀ u, c.label ≠ some (.P, u)) ∧
        (t.g.IsQGraph → spdPM' t.g ∧ t.g.QLabelInMISB)) ∨ (D : ℤ) < t.g.ord) := by
  obtain ⟨hn, hT⟩ := hH
  obtain ⟨hD, ho2, ⟨ho1, ⟨C, hN⟩, hd, hL, hgs, hnr, hTD, hM, hst⟩, hI, hP⟩ := hG
  have hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63 :=
    ⟨hT.1, hT.2.2.2.1, hT.2.2.2.2⟩
  obtain ⟨hdf, hv⟩ :=
    TerminationB_inv_subst hn hcore hL hN hd ho1 ho2 hI hTD hgs hnr hM hst hP g hg t ht
  have hGG := globalGoodB' 𝔈 hF n D Sig 𝒯 m C H x y₁ y₂ hn hT hL hN hd ho1 ho2 hI hTD hgs hnr hM
    hst hP
  have hMu := (substMu n D Sig 𝒯 m C H x y₁ y₂ hn hT hL hN hd ho1 ho2 hI hTD hgs hnr hM hst).1
    g hg t ht
  obtain ⟨hgDC, hroot, hgNL, hglab, -⟩ := TerminationC2_tSubst ⟨hn, hT⟩ hg
  have hGtDC := substDCB m g.1 H x y₁ y₂ g.2 hd hI.1 hst hgDC hroot
  obtain ⟨hdcs, hfR⟩ := TerminationC2_oDotT_dc hGtDC t ht
  obtain ⟨hx, -, -⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hn0 : t.nOut ≠ 0 := by
    intro h0
    have hr := hfR (liftA g.1 x)
    have hxr : (liftA g.1 x : Atom 3 (m + g.1)).isRight = true := by
      cases x with
      | inl a => simp at hx
      | inr b => rfl
    rw [hxr] at hr
    rcases hfx : t.f (liftA g.1 x) with a | j
    · rw [hfx] at hr; simp at hr
    · exact (Fin.cast h0 j).elim0
  have hIt' : t.g.InvRun D :=
    invRun_step n D Sig 𝒯 hn hT _ _ (StrategyStepB.dot _) hIt ⟨t.nOut, t.g⟩
      (List.mem_map_of_mem ht)
  have hTt : t.g.TensorDiffusive := by
    rcases hIt' with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨-, -, -, h, -⟩
    · exact h
    · exact absurd h0 hn0
    · exact h
  have hNorm : ∃ C, t.g.Normal C := by
    rcases TerminationC2_mem_tSubst hg with h | h | h | h
    · exact (hGG.1 g h t ht).1
    · exact (hGG.2.1 g h t ht).1
    · exact ((hGG.2.2.1 g h).2 t ht).1
    · exact (hGG.2.2.2 g h t ht).1
  refine ⟨hNorm, hdf, hIt', (TerminationK_runKinds_iff _).2
      (TerminationK_oDotT ((TerminationK_runKinds_iff _).1 hKt) t ht), hdcs, hv,
    hTt, hn0, TerminationC2_oDotT_noLabDot (TerminationC2_glue_noLabDot hL hgNL) t ht,
    (TerminationC2_piece_labels hL ht).1 hglab, hMu, fun hlab => ?_⟩
  rcases TerminationC2_mem_tSubst hg with h | h | h | h
  · exact absurd (hGG.1 g h t ht).2.2.1 hlab
  · exact absurd (hGG.2.1 g h t ht).2.2.1 hlab
  · refine Or.inl ⟨h, (TerminationC2_piece_labels hL ht).2 ?_, ((hGG.2.2.1 g h).2 t ht).2.2.1⟩
    obtain ⟨u, -, hu⟩ := (hT.2.2.2.1.2.2.2.1 g h).1
    intro c hc w hw
    have := hu c hc (Or.inr (by rw [hw]; rfl))
    rw [hw] at this
    cases this
  · right
    have := (hGG.2.2.2 g h t ht).2.2.2
    omega

end Subst

/-! ## Graphs with labels and outputs of high order -/

section Labelled

/-- The invariant of a run from its clauses, the last one from the run kinds. -/
private theorem TerminationC2_ri_of {n D N : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hI : g.2.InvRun D) (hv : TerminationB_Inv n D g.2) (hdc : g.2.DoublyConnected)
    (hT : g.2.TensorDiffusive) (hN : g.2.NoLabDot) (hl : g.2.labels.length ≤ 1)
    (hP : ∀ c ∈ g.2.comps, ∀ u, c.label ≠ some (.P, u))
    (hQ : g.2.IsQGraph → spdPM' g.2 ∧ g.2.QLabelInMISB) (h9 : g.2.dotExcess ≠ 0 → g.2.Plain)
    (hK : g.2.RunKinds N) : TerminationC_RI n D g := by
  refine ⟨hI, hv, hdc, hT, hN, hl, hP, hQ, h9, ?_⟩
  rcases hv.1 with h | h
  · exact Or.inr ⟨N, hK.tKinds h⟩
  · exact Or.inl h

/-- A `Q`-graph has at most one label and no `P` label; with well formed components it has no
labelled dotted or `×`-dotted edge. -/
private theorem TerminationC2_qGraph_labels {k n : ℕ} {Γ : Graph k n} (hQ : Γ.IsQGraph) :
    Γ.labels.length ≤ 1 ∧ (∀ c ∈ Γ.comps, ∀ u, c.label ≠ some (.P, u)) ∧
      ((∀ c ∈ Γ.comps, c.WF) → Γ.NoLabDot) := by
  obtain ⟨u, -, hu⟩ := hQ
  have hl : ∀ c ∈ Γ.comps, ∀ l, c.label = some l → l = (.Q, u) := by
    intro c hc l hcl
    have := hu c hc (Or.inr (by rw [hcl]; rfl))
    rw [hcl] at this
    exact Option.some.inj this
  refine ⟨?_, fun c hc w hw => ?_, fun hW c hc hk => ?_⟩
  · unfold Graph.labels
    refine TerminationC2_dedup_le_one fun a ha b hb => ?_
    obtain ⟨c₁, hc₁, h₁⟩ := List.mem_filterMap.1 ha
    obtain ⟨c₂, hc₂, h₂⟩ := List.mem_filterMap.1 hb
    rw [hl c₁ hc₁ a h₁, hl c₂ hc₂ b h₂]
  · have := hl c hc _ hw
    simp at this
  · cases hcl : c.label with
    | none => rfl
    | some l =>
      have hr := (hW c hc).2 (by rw [hcl]; rfl)
      rcases hk with hk | hk <;> rw [hk] at hr <;> simp [Kind.isRandom] at hr

/-- **Outputs of order `> D`** ([II, Strategy 6.6], the class `Err` of [II, Def 6.3]): a normal
regular, doubly connected graph of dot excess `0` and scaling order `> D`, with an internal atom,
the invariant of a run, no labelled dotted edge and at most one label, is an output. -/
private theorem TerminationC2_out_high {n D : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hN : ∃ C, g.2.Normal C) (h0 : g.2.dotExcess = 0) (hD : (D : ℤ) < g.2.ord)
    (hdc : g.2.DoublyConnected) (hI : g.2.InvRun D) (hn : g.1 ≠ 0) (hNL : g.2.NoLabDot)
    (hl : g.2.labels.length ≤ 1) : TerminationC_Out n D g := by
  have hE : g.2.ExtClause ∧ g.2.ColourInvB ∧ g.2.TensorDiffusive := by
    rcases hI with ⟨⟨-, hC, hE, -⟩, hT⟩ | ⟨h, -⟩ | ⟨-, hE, hC, hT, -⟩
    · exact ⟨hE, hC, hT⟩
    · exact absurd h hn
    · exact ⟨hE, hC, hT⟩
  obtain ⟨hE, hC, hT⟩ := hE
  exact ⟨⟨h0, Or.inr (Or.inl ⟨hN, hD⟩)⟩, hdc, hN, ⟨hT, h0, hNL, hl⟩, fun h => absurd hD h,
    Or.inl ⟨hD, TerminationB_rgCheck g.2 fun _ => ⟨hE, hT⟩, fun _ => ⟨hE, hC⟩⟩⟩

end Labelled

/-! ## The outputs of Step 1 -/

section Loc

open private Termination_inv1 Termination_not_qGraph from RBM8D.GlobalExp.Termination
open private Local_localOp_good from RBM8D.GlobalExp.Local

/-- **The outputs of Step 1** ([II, Strategy 6.6, Step 1], [II, Lemma 6.8]): at an admissible local
expansion of a graph without labels with the invariant of a run, every output graph is a graph
without labels with the invariant of a run and a smaller `runMu`, or a normal regular `Q`-graph
with the invariant of a run and the run kinds. -/
private theorem TerminationC2_loc {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {g : Σ n₀ : ℕ, Graph 3 n₀}
    {o : Fin 5} {x : Fin g.1} (hA : TerminationC_Adm n D 𝔈 g (.loc o x))
    (hg : TerminationC2_LF n D g) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (.loc o x),
      (TerminationC2_LF n D s ∧ runMu n s.2 < runMu n g.2) ∨
      ((∃ C, s.2.Normal C) ∧ TerminationC_RI n D s ∧ s.2.IsQGraph ∧ s.2.RunKinds (n - 1)) := by
  intro s hs
  have hK' := TerminationK_step hF h𝒯 hA hg.2.2.2 s hs
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 g _ (TerminationC_Adm.step hA) hg.2.1.1 s hs
  obtain ⟨n₀, Γ⟩ := g
  obtain ⟨-, ⟨hI, hv, hdc, -⟩, hL, -⟩ := hg
  obtain ⟨hS, hD, ⟨C, hN⟩, -, hP, hgs, hmis, hside, hloc, hX⟩ := hA
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
  obtain ⟨hNt, hdct, hstep, hvt⟩ :=
    TerminationB_inv_loc hI hv hS hD hN hL hP hgs hX hloc hside t ht
  obtain ⟨hB, -⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
  have hn0 : t.nOut ≠ 0 := by
    obtain ⟨-, hfx, -⟩ := Local_localOp_good ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1⟩ hL x o hside t ht
    intro h0
    rcases hf : t.f (.inr x) with a | j
    · rw [hf] at hfx; cases hfx
    · exact (Fin.cast h0 j).elim0
  have hTt : t.g.TensorDiffusive := by
    rcases hI' with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨-, -, -, h, -⟩
    · exact h
    · exact absurd h0 hn0
    · exact h
  have hPt : t.g.Plain := hstep.2.2.2.2.2.1
  rcases hstep.2.2.2.2.2.2.1 with hLt | hQt
  · exact Or.inl ⟨⟨hNt, TerminationC2_ri_lf hLt hI' hvt (hdct hdc) hTt (fun _ => hPt) hK', hLt, hK'⟩,
      locMu n D n₀ C Γ o x hI hS hD hN hL hP hX hloc t ht hLt⟩
  · obtain ⟨hl1, hP1, hNL⟩ := TerminationC2_qGraph_labels hQt
    refine Or.inr ⟨hNt, TerminationC2_ri_of hI' hvt (hdct hdc) hTt (hNL fun c hc => (hPt c hc).2.2.2.2)
      hl1 hP1 (fun _ => ⟨?_, ?_⟩) (fun _ => hPt) hK', hQt, hK'⟩
    · exact ((localSPDB n₀ C x Γ hB.1 hB.2.2.1 hB.2.2.2.1 hB.2.1).2 hN hL hP o hside t ht).1
    · exact localQLabelB n₀ C x Γ hN hL hP hgs hB.2.2.1 hB.2.2.2.1 hB.2.1 hmis o hside t ht hQt

end Loc

/-! ## The removal of a redundant dotted edge -/

section DropDot

open private TrH TrH.mk TrH.spd_iff from RBM8D.Graph.MolCarry
open private TerminationC_mis_image from RBM8D.GlobalExp.TerminationC
open private Termination_anchor_congr Termination_flatComp_congr from RBM8D.GlobalExp.Termination
open private DotNorm.step DotNorm.Keep DotNorm.Keep.sub DotNorm.Keep.nondot DotNorm.Keep.block
  DotNorm.Keep.normal DotNorm.Keep.plain DotNorm.Keep.lf DotNorm.Keep.q DotNorm.Keep.mol
  DotNorm.Keep.dc DotNorm.Keep.labels from RBM8D.Graph.Local.DotNorm

/-- **The molecular graph without one redundant dotted edge** is the molecular graph with it, up
to the names of the edges: a dotted edge is an absent edge of `Graph.toMG'`, and the blocks and the
molecules are the same. -/
private theorem TerminationC2_trH_erase {k n : ℕ} {Γ : Graph k n} {i : ℕ}
    (hi : i < Γ.comps.length) (hk : Γ.comps[i].kind = .dot)
    (hsb : ∀ u v, (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).SameBlock u v ↔ Γ.SameBlock u v)
    (hsm : ∀ u v, (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).SameMol u v ↔ Γ.SameMol u v) :
    ∃ g, TrH (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).toMG' Γ.toMG' id g
      (↑(⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).toMG'.int ∪
        ↑(⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).toMG'.ext) ∧
      (∀ u, Γ.molRep u = (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).molRep u) := by
  set Γ₁ : Graph k n := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ with hΓ₁
  have hlen : Γ₁.comps.length + 1 = Γ.comps.length := by
    simp only [hΓ₁, List.length_eraseIdx, if_pos hi]; omega
  have hrep : ∀ u, Γ.molRep u = Γ₁.molRep u := by
    intro u
    unfold Graph.molRep
    rcases u with a | a
    · rfl
    · change Sum.inr _ = Sum.inr _
      congr 3
      funext b
      exact decide_eq_decide.2 (hsm _ _).symm
  have hsb' : ∀ u v, Γ.SameBlock u v ↔ Γ₁.SameBlock u v := fun u v => (hsb u v).symm
  have hfc : ∀ c, Γ.flatComp c = Γ₁.flatComp c := Termination_flatComp_congr hsb'
  have han : ∀ u, Γ.anchor u = Γ₁.anchor u := Termination_anchor_congr hsb'
  let σ : Fin Γ₁.comps.length → Fin Γ.comps.length := fun j =>
    if h : (j : ℕ) < i then ⟨j, by omega⟩ else ⟨j + 1, by omega⟩
  have hget : ∀ j : Fin Γ₁.comps.length, Γ.comps[σ j] = Γ₁.comps[j] := by
    intro j
    simp only [σ, hΓ₁, Fin.getElem_fin, List.getElem_eraseIdx]
    split_ifs <;> rfl
  have hσinj : Function.Injective σ := by
    intro a b hab
    simp only [σ] at hab
    split_ifs at hab <;> simp [Fin.ext_iff] at hab <;> exact Fin.ext (by omega)
  have hcls : ∀ j, Γ.toMG'.cls (.inl (σ j)) = Γ₁.toMG'.cls (.inl j) := by
    intro j
    simp only [Graph.toMG', hget, hfc, hrep]
  have hends : ∀ j, Γ.toMG'.ends (.inl (σ j)) = Γ₁.toMG'.ends (.inl j) := by
    intro j
    simp only [Graph.toMG', hget, hfc, hrep]
  have hclsr : ∀ a, Γ.toMG'.cls (.inr a) = Γ₁.toMG'.cls (.inr a) := by
    intro a
    simp only [Graph.toMG', han]
  have hendsr : ∀ a, Γ.toMG'.ends (.inr a) = Γ₁.toMG'.ends (.inr a) := by
    intro a
    simp only [Graph.toMG', han, hrep]
  refine ⟨Sum.map σ id, TrH.mk (Set.injOn_id _) (fun v hv => Or.inl hv) (fun v hv => Or.inr hv)
    (fun e _ => MolInsert_toMG'_ends_vtx k n Γ₁ e) ?_ ?_ ?_ ?_ ?_ ?_, hrep⟩
  · simp only [Graph.toMG', Finset.image_id, hrep]
  · simp only [Graph.toMG', Finset.image_id]
  · rintro (a | a) (b | b) - - h
    · simp only [Sum.map_inl, Sum.inl.injEq] at h
      rw [hσinj h]
    · simp at h
    · simp at h
    · simpa using h
  · rintro (j | a) _
    · exact hcls j
    · exact hclsr a
  · rintro (j | a) _
    · left
      rw [Sum.map_inl, hends j]
      rfl
    · left
      simp only [Sum.map_inr, id, hendsr a]
  · rintro (j' | a) hj'
    · by_cases hji : (j' : ℕ) = i
      · exfalso
        apply hj'
        have hc : Γ.comps[j'] = Γ.comps[i] := by simp only [Fin.getElem_fin, hji]
        simp only [Graph.toMG', hc]
        rw [if_pos (Or.inl (by simp [Graph.flatComp, hk]))]
      · have hj2 := j'.2
        let j : Fin Γ₁.comps.length :=
          if h : (j' : ℕ) < i then ⟨j', by omega⟩ else ⟨j' - 1, by omega⟩
        have hj : σ j = j' := by
          simp only [σ, j]
          split_ifs <;> simp only [Fin.ext_iff] at * <;> omega
        refine ⟨.inl j, ?_, by rw [Sum.map_inl, hj]⟩
        rw [← hcls, hj]
        exact hj'
    · exact ⟨.inr a, by rw [← hclsr]; exact hj', rfl⟩

/-- **The removal of a redundant dotted edge** (the step `dropDot`, [I, Strategy 3.21]) at a
normal regular plain graph with the invariant of a run and the run kinds gives a normal regular
graph with them, without labels or a `Q`-graph when the graph is, and lowers `runMu`. -/
private theorem TerminationC2_dropDot {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {g : Σ n₀ : ℕ, Graph 3 n₀}
    {Γ' : Graph 3 g.1} (hA : TerminationC_Adm n D 𝔈 g (.dropDot Γ'))
    (hR : TerminationC_RI n D g) (hK : g.2.RunKinds (n - 1)) :
    (∃ C, Γ'.Normal C) ∧ TerminationC_RI n D ⟨g.1, Γ'⟩ ∧ Γ'.RunKinds (n - 1) ∧
      (g.2.LabelFree → Γ'.LabelFree) ∧ (g.2.IsQGraph → Γ'.IsQGraph) ∧
      runMu n Γ' < runMu n g.2 := by
  have hK' := TerminationK_step hF h𝒯 hA hK ⟨g.1, Γ'⟩ (List.mem_singleton_self _)
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 g _ (TerminationC_Adm.step hA) hR.1 ⟨g.1, Γ'⟩
    (List.mem_singleton_self _)
  obtain ⟨n₀, Γ⟩ := g
  obtain ⟨hst, ⟨C, hN⟩, hP⟩ := hA
  obtain ⟨hI, hv, hdc, hT, hNL, hlab, hPf, hQ, -, -⟩ := hR
  have hmu := dotNormStep_mu n 3 n₀ C Γ Γ' hst hN hP
  have hv' := TerminationB_inv_dropDot hH.le hst hN hP hI hv
  obtain ⟨i, c, hc, hk, hr, rfl⟩ := hst
  obtain ⟨-, -, hKp⟩ := DotNorm.step hN hP hc hk hr
  have hsub : ∀ d ∈ (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).comps, d ∈ Γ.comps :=
    fun d hd => (DotNorm.Keep.sub hKp).subset hd
  obtain ⟨sT, sP, -, -, sN⟩ := TerminationC2_sub_facts hsub (n - 1)
  have hi : i < Γ.comps.length := (List.getElem?_eq_some_iff.1 hc).1
  have hci : Γ.comps[i] = c := (List.getElem?_eq_some_iff.1 hc).2
  have hQ' : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).IsQGraph →
      spdPM' (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀) ∧
        (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).QLabelInMISB := by
    intro hQ1
    have hcl : c.label = none := by
      cases hl : c.label with
      | none => rfl
      | some l =>
        have := (hP c (by rw [← hci]; exact List.getElem_mem hi)).2.2.2.2.2 (by rw [hl]; rfl)
        rw [hk] at this; cases this
    have hQΓ : Γ.IsQGraph := by
      obtain ⟨u, ⟨d, hd, hdl⟩, hu⟩ := hQ1
      refine ⟨u, ⟨d, hsub d hd, hdl⟩, fun d hd hdr => ?_⟩
      rcases TerminationC2_mem_eraseIdx hd hi with hd' | rfl
      · exact hu d hd' hdr
      · rw [hci] at hdr ⊢
        rw [hcl] at hdr
        rw [hk] at hdr
        simp [Kind.isRandom] at hdr
    obtain ⟨hspd, hql⟩ := hQ hQΓ
    obtain ⟨gm, htr, hrep⟩ := TerminationC2_trH_erase hi (by rw [hci]; exact hk)
      (DotNorm.Keep.block hKp) (DotNorm.Keep.mol hKp)
    have hmis := TerminationC_mis_image htr
    rw [Finset.image_id] at hmis
    refine ⟨(TrH.spd_iff htr).1 hspd, fun d hd u hu => ?_⟩
    rcases hql d (hsub d hd) u hu with h | ⟨hu', h⟩
    · left; rw [← hrep, ← hmis]; exact h
    · right
      refine ⟨hu', ?_⟩
      rcases h with h | ⟨d', hd', a, hw, hj, ha⟩
      · exact Or.inl h
      · right
        have hd'' : d' ∈ (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).comps := by
          rcases TerminationC2_mem_eraseIdx hd' hi with h | rfl
          · exact h
          · exfalso; obtain ⟨w, hw⟩ := hw; rw [hci, hk] at hw; cases hw
        exact ⟨d', hd'', a, hw, hj, by rw [← hrep, ← hmis]; exact ha⟩
  refine ⟨⟨C, DotNorm.Keep.normal hKp⟩, TerminationC2_ri_of hI' hv' (DotNorm.Keep.dc hKp hdc)
    (sT hT) (sN hNL) (by rw [DotNorm.Keep.labels hKp]; exact hlab)
    (fun d hd u hu => hPf d (hsub d hd) u hu) hQ' (fun _ => DotNorm.Keep.plain hKp) hK', hK',
    DotNorm.Keep.lf hKp, DotNorm.Keep.q hKp, hmu⟩

end DropDot

/-! ## The `Q`-expansions of Step 3 -/

section QExp

/-- Well formed components carry no label on a dotted or `×`-dotted edge. -/
private theorem TerminationC2_noLabDot_of_wf {k n : ℕ} {Γ : Graph k n}
    (h : ∀ c ∈ Γ.comps, c.WF) : Γ.NoLabDot := by
  intro c hc hk
  cases hcl : c.label with
  | none => rfl
  | some l =>
    have hr := (h c hc).2 (by rw [hcl]; rfl)
    rcases hk with hk | hk <;> rw [hk] at hr <;> simp [Kind.isRandom] at hr

/-- At most one label along a chain of elementary steps of the `Q`-expansions
(`qElemStep_labels`). -/
private theorem TerminationC2_labels_chain {a b : Σ n, Graph 3 n}
    (h : Relation.ReflTransGen QElemStep a b) (ha : a.2.labels.length ≤ 1) :
    b.2.labels.length ≤ 1 := by
  induction h with
  | refl => exact ha
  | tail _ hs ih => exact qElemStep_labels _ _ hs ih

/-- **The outputs of a `Q`-expansion of Step 3** ([II, Lemma 6.5 (4)], [II, Lemma 4.15],
[II, Lemma 6.8]) at the label atom of an `O_dot` form `t` of a substituted graph of `Q` that is not
a `Q`-graph: every output graph is an output of the run (of scaling order `> D`), or a graph
without labels with the invariant of a run and a smaller `runMu` than the host, or a normal regular
`Q`-graph with the invariant of a run and the run kinds. -/
private theorem TerminationC2_qexp {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.Q) {t : Tracked 3 (m + g.1)}
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) (hdc : t.g.DoublyConnected)
    (hlab : t.g.labels.length ≤ 1) (hK : t.g.RunKinds (n - 1)) (hIt : t.g.InvRun D)
    {x' : Fin t.nOut} (hA : TerminationC_Adm n D 𝔈 ⟨t.nOut, t.g⟩ (.qexp x')) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 ⟨t.nOut, t.g⟩ (.qexp x'),
      TerminationC_Out n D s ∨
      (TerminationC2_LF n D s ∧ runMu n s.2 < runMu n (H.glue x y₁ y₂ (tVar true))) ∨
      ((∃ C, s.2.Normal C) ∧ TerminationC_RI n D s ∧ s.2.IsQGraph ∧ s.2.RunKinds (n - 1)) := by
  intro s hs
  have hK' := TerminationK_step hF h𝒯 hA hK s hs
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 _ _ (TerminationC_Adm.step hA) hIt s hs
  obtain ⟨hn, hT⟩ := hH
  obtain ⟨hD, ho2, ⟨ho1, ⟨C, hN⟩, hd, hL, hgs, hnr, hTD, hM, hst⟩, hI, hP⟩ := hG
  have hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63 :=
    ⟨hT.1, hT.2.2.2.1, hT.2.2.2.2⟩
  have hg' : g ∈ 𝒯.tSubst (n - 1) := by simp [TRec.tSubst, TRec.rhs, hg]
  obtain ⟨-, -, -, hform, hnQ, -, hcl⟩ := hA
  obtain ⟨C', hC'⟩ := hcl.1
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
  obtain ⟨⟨hbase, hcls, -, -⟩, -⟩ := hC' u hu
  have hn0 : u.nOut ≠ 0 := by
    intro h0
    have hfx := hbase.2.2.2.2.1
    rcases hf : u.f (.inr x') with a | j
    · rw [hf] at hfx; cases hfx
    · exact (Fin.cast h0 j).elim0
  have hTu : u.g.TensorDiffusive := by
    rcases hI' with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨-, -, -, h, -⟩
    · exact h
    · exact absurd h0 hn0
    · exact h
  have hv := TerminationB_inv_qexp 𝔈 hF hn hcore hL hN hd ho1 ho2 hI hTD hgs hnr hM hst hP g hg t
    ht x' hform hnQ u hu
  have hrow := ((globalGoodB' 𝔈 hF n D Sig 𝒯 m C H x y₁ y₂ hn hT hL hN hd ho1 ho2 hI hTD hgs hnr
    hM hst hP).2.2.1 g hg).2 t ht |>.2.2.2 x' hform hnQ u hu
  have hWF : ∀ c ∈ u.g.comps, c.WF := by
    rcases hcls with ⟨hPl, -⟩ | ⟨-, hCl⟩
    · exact fun c hc => (hPl c hc).2.2.2.2
    · exact fun c hc => (hCl c hc).2.2.2
  have hNL := TerminationC2_noLabDot_of_wf hWF
  have hlab' : u.g.labels.length ≤ 1 :=
    TerminationC2_labels_chain (a := ⟨t.nOut, t.g⟩) (b := ⟨u.nOut, u.g⟩)
      hbase.2.2.2.2.2.2 hlab
  have hdcu := hbase.2.2.2.2.2.1 hdc
  have hNu : ∃ C, u.g.Normal C := ⟨C', hbase.1⟩
  rcases hrow with ⟨h0, ⟨hLu, -, -⟩ | ⟨hQu, hspd, hql⟩ | ⟨hDu, -⟩⟩
  · refine Or.inr (Or.inl ⟨⟨hNu, TerminationC2_ri_lf hLu hI' hv hdcu hTu
      (fun h => absurd h0 h) hK', hLu, hK'⟩, ?_⟩)
    exact (substMu n D Sig 𝒯 m C H x y₁ y₂ hn hT hL hN hd ho1 ho2 hI hTD hgs hnr hM hst).2 g hg t
      ht x' _ hform hnQ hcl u hu hLu
  · obtain ⟨hl1, hP1, -⟩ := TerminationC2_qGraph_labels hQu
    exact Or.inr (Or.inr ⟨hNu, TerminationC2_ri_of hI' hv hdcu hTu hNL hl1 hP1
      (fun _ => ⟨hspd, hql⟩) (fun h => absurd h0 h) hK', hQu, hK'⟩)
  · exact Or.inl (TerminationC2_out_high hNu h0 hDu hdcu hI' hn0 hNL hlab')

end QExp

/-! ## Hosts, normal forms and reorderings -/

section Hosts

open private RunClauses_Iso RunClauses_SwapR RunClauses_eA RunClauses_iso_ex RunClauses_isoG
  RunClauses_iso_reach RunClauses_iso_mem RunClauses_swapR_eq RunClauses_iso_length
  RunClauses_iso_card RunClauses_edgeGraph_eq RunClauses_reorder_iso RunClauses_iso_labels
  RunClauses_cand RunClauses_step RunClauses_joined RunClauses_joined_iff RunClauses_fold
  RunClauses_sk RunClauses_mem_cand from RBM8D.GlobalExp.RunClauses

/-- **A renaming and reordering reflects the normal regular form**: the clauses of `Graph.Normal`
are read through the bijection of the atoms. -/
private theorem TerminationC2_iso_normal_rev {m m' : ℕ} {e : Fin m ≃ Fin m'} {Γ : Graph 3 m}
    {Γ' : Graph 3 m'} (h : RunClauses_Iso e Γ Γ') {C : ℕ} (hN : Γ'.Normal C) : Γ.Normal C := by
  obtain ⟨⟨hs, hc, hi, hd⟩, hsol, hx⟩ := hN
  have hsx : ∀ (P : Kind → Prop) (u v : Atom 3 m),
      (∃ c ∈ Γ'.comps, P c.kind ∧ (c.x = RunClauses_eA e u ∧ c.y = RunClauses_eA e v ∨
        c.x = RunClauses_eA e v ∧ c.y = RunClauses_eA e u)) ↔
      (∃ c ∈ Γ.comps, P c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) := by
    intro P u v
    have := RunClauses_iso_ex h P s(u, v)
    simp only [Sym2.map_mk, Sym2.eq_iff] at this
    exact this
  refine ⟨⟨?_, ?_, fun a b => ?_, fun c hc' hk => ?_⟩, fun c hc' hk => ?_, fun u v huv => ?_⟩
  · have h1 := RunClauses_iso_length h
    have h2 := RunClauses_iso_card h
    omega
  · rw [RunClauses_edgeGraph_eq] at hc ⊢
    exact (RunClauses_isoG h _).preconnected_iff.2 hc
  · exact (RunClauses_iso_reach h
      (fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true) (.inr a) (.inr b)).1
      (hi (e a) (e b))
  · obtain ⟨c', hc'', hr⟩ := RunClauses_iso_mem h hc'
    obtain ⟨hk', -, -, hxy, -⟩ := RunClauses_swapR_eq hr
    have := hd c' hc'' (by rw [hk']; exact hk)
    have hl : ∀ u : Atom 3 m, (RunClauses_eA e u).isLeft = u.isLeft := by
      intro u; cases u <;> rfl
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this <;>
      simp only [Comp.map, hl] at this
    · exact this
    · exact this.symm
  · obtain ⟨c', hc'', hr⟩ := RunClauses_iso_mem h hc'
    obtain ⟨hk', -, -, -, hrd⟩ := RunClauses_swapR_eq hr
    have hr' : c.kind.isRandom = true := by
      revert hk; cases c.kind <;> simp [Kind.isSolid, Kind.isRandom]
    have heq := hrd (Or.inl (by simpa [Comp.map] using hr'))
    have := hsol c' hc'' (by rw [hk']; simpa [Comp.map] using hk)
    rw [heq] at this
    simp only [Comp.map] at this
    exact fun h' => this (by rw [h'])
  · rw [← hsx (fun κ => κ = .xdot), ← hsx (fun κ => κ.isSolid = true)]
    exact hx _ _ ((RunClauses_eA e).injective.ne huv)

/-- A reordering reflects the normal regular form. -/
private theorem TerminationC2_reorder_normal_rev {n₀ : ℕ} {Γ Γ' : Graph 3 n₀} (h : Γ.Reorder Γ')
    (hN : ∃ C, Γ'.Normal C) : ∃ C, Γ.Normal C := by
  obtain ⟨π, hiso⟩ := RunClauses_reorder_iso h
  obtain ⟨C, hC⟩ := hN
  exact ⟨C, TerminationC2_iso_normal_rev hiso hC⟩

/-- A reordering reflects graphs without labels. -/
private theorem TerminationC2_reorder_lf_rev {n₀ : ℕ} {Γ Γ' : Graph 3 n₀} (h : Γ.Reorder Γ')
    (hL : Γ'.LabelFree) : Γ.LabelFree := by
  obtain ⟨π, hiso⟩ := RunClauses_reorder_iso h
  have h1 := RunClauses_iso_labels hiso
  have h0 : Γ'.labels = [] := by
    have : Γ'.comps.filterMap Comp.label = [] := List.filterMap_eq_nil_iff.2 fun c hc => hL c hc
    simp [Graph.labels, this]
  rw [h0] at h1
  intro c hc
  by_contra hne
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hne
  have : l ∈ Γ.labels := List.mem_dedup.2 (List.mem_filterMap.2 ⟨c, hc, hl⟩)
  have := List.length_pos_of_mem this
  simp at h1
  omega

/-- A host of Steps 2–3 has no labels: `H` has none, and the `t`-variable has none. -/
private theorem TerminationC2_host_lf {g : Σ n₀ : ℕ, Graph 3 n₀} (h : TerminationC_GlueHost g) :
    g.2.LabelFree := by
  obtain ⟨m, H, x, y₁, y₂, rfl, hP⟩ := h
  have hL := hP.2.2.2.1
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    simp [Comp.map, hL c₀ hc₀]
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    have : ∀ d ∈ (tVar true).comps, d.label = none := by decide
    simp [Comp.map, this c₀ hc₀]

/-- **A normal regular graph is its only `O_dot` form**: it has no pair to split (a `×`-dotted
edge between two distinct atoms exactly where there is a solid edge), no dotted edge between
internal atoms and no solid loop. -/
private theorem TerminationC2_self_mem_oDotT {n : ℕ} {Γ : Graph 3 n} {C : ℕ}
    (hN : Γ.Normal C) : Tracked.self Γ ∈ oDotT Γ := by
  obtain ⟨hR, hsol, hx⟩ := hN
  have hSP : Γ.splitPairs = [] := by
    rw [show Γ.splitPairs = ((RunClauses_cand Γ).foldl RunClauses_step []).filterMap (fun p =>
      if RunClauses_joined Γ Kind.isSolid p.1 p.2 != RunClauses_joined Γ (· == .xdot) p.1 p.2
      then some (p.1, p.2, RunClauses_joined Γ Kind.isSolid p.1 p.2) else none) from rfl]
    refine List.filterMap_eq_nil_iff.2 fun p hp => ?_
    have hz := ((RunClauses_fold (RunClauses_cand Γ) [] List.nodup_nil).2 (RunClauses_sk p)).1
      (List.mem_map_of_mem hp)
    simp only [List.map_nil, List.not_mem_nil, false_or] at hz
    obtain ⟨hdiag, -⟩ := (RunClauses_mem_cand Γ _).1 hz
    have hne : p.1 ≠ p.2 := fun h => hdiag (by simp [RunClauses_sk, h])
    have key := hx p.1 p.2 hne
    have e : RunClauses_joined Γ Kind.isSolid p.1 p.2 =
        RunClauses_joined Γ (· == .xdot) p.1 p.2 := by
      rw [Bool.eq_iff_iff, RunClauses_joined_iff, RunClauses_joined_iff]
      simp only [Sym2.eq_iff, beq_iff_eq]
      exact key.symm
    rw [e]
    simp
  rw [TerminationC2_oDotT_eq]
  split_ifs with h1 h2
  · exact List.mem_singleton_self _
  · exact List.mem_singleton_self _
  · exfalso
    apply h2
    rw [hSP]
    simp only [List.isEmpty_nil, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.any_eq_false]
    intro c hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and]
    refine ⟨fun ⟨hk, hx'⟩ hy' => ?_, fun hs hxy => hsol c hc hs hxy⟩
    rcases hR.noIntDot c hc hk with h | h
    · cases hcx : c.x <;> simp_all
    · cases hcy : c.y <;> simp_all

end Hosts

/-! ## The graphs of a run and their ranks -/

section Rank

/-- The values of the measure `runMu`. -/
private abbrev TerminationC2_M : Type := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)))))

/-- The ranks of the graphs of a run, compared lexicographically: a level (`0` for `Q`-graphs),
the measure `runMu` of the graph or of the host of Steps 2–3 it comes from, a tier, and the
measure `TerminationC_nu` of the normal form of Step 2. -/
private abbrev TerminationC2_R : Type := ℕ ×ₗ (TerminationC2_M ×ₗ (ℕ ×ₗ ℕ))

/-- The rank with level `a`, measure `μ`, tier `b` and `c` as the last entry. -/
private def TerminationC2_rk (a : ℕ) (μ : TerminationC2_M) (b c : ℕ) : TerminationC2_R :=
  toLex (a, toLex (μ, toLex (b, c)))

private theorem TerminationC2_rk_lt_a {a a' : ℕ} {μ μ' : TerminationC2_M} {b b' c c' : ℕ}
    (h : a < a') : TerminationC2_rk a μ b c < TerminationC2_rk a' μ' b' c' :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

private theorem TerminationC2_rk_lt_mu {a : ℕ} {μ μ' : TerminationC2_M} {b b' c c' : ℕ}
    (h : μ < μ') : TerminationC2_rk a μ b c < TerminationC2_rk a μ' b' c' :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl h)⟩)

private theorem TerminationC2_rk_lt_b {a : ℕ} {μ : TerminationC2_M} {b b' c c' : ℕ}
    (h : b < b') : TerminationC2_rk a μ b c < TerminationC2_rk a μ b' c' :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl h)⟩)⟩)

private theorem TerminationC2_rk_lt_c {a : ℕ} {μ : TerminationC2_M} {b c c' : ℕ}
    (h : c < c') : TerminationC2_rk a μ b c < TerminationC2_rk a μ b c' :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, h⟩)⟩)⟩)

private theorem TerminationC2_rk_le_c {a : ℕ} {μ : TerminationC2_M} {b c : ℕ} :
    TerminationC2_rk a μ b 0 ≤ TerminationC2_rk a μ b c := by
  rcases Nat.eq_zero_or_pos c with rfl | h
  · exact le_rfl
  · exact (TerminationC2_rk_lt_c h).le

/-- **The graphs of a run of [II, Strategy 6.6] and their ranks** ([II, Lemma 6.8]): normal regular
graphs without labels with the invariant of a run (rank: `runMu` and `TerminationC_nu`); normal
regular `Q`-graphs with the invariant of a run (level `0`); the substituted graphs of Steps 2–3 that
are not normal regular, after steps on `×`-dotted edges and on the coefficient (rank: `runMu` of
the host, tier `1`); and the normal regular `O_dot` forms with labels of order `≤ D` of a
substituted graph of `Q` that are not `Q`-graphs (rank: `runMu` of the host, tier `0`). -/
private def TerminationC2_Good (n D : ℕ) (𝒯 : TRec) (g : Σ n₀ : ℕ, Graph 3 n₀)
    (r : TerminationC2_R) : Prop :=
  (TerminationC2_LF n D g ∧ r = TerminationC2_rk 1 (runMu n g.2) 2 (TerminationC_nu g)) ∨
  ((∃ C, g.2.Normal C) ∧ TerminationC_RI n D g ∧ g.2.IsQGraph ∧ g.2.RunKinds (n - 1) ∧
    r = TerminationC2_rk 0 (runMu n g.2) 0 0) ∨
  (∃ (m : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g' : Σ n₀ : ℕ, Graph 3 n₀),
    TerminationC2_Host n D H x y₁ y₂ ∧ g' ∈ 𝒯.tSubst (n - 1) ∧
    (H.glue x y₁ y₂ g'.2.swapSolid).InvRun D ∧
    (H.glue x y₁ y₂ g'.2.swapSolid).RunKinds (n - 1) ∧
    Relation.ReflTransGen TerminationC2_NuStep ⟨m + g'.1, H.glue x y₁ y₂ g'.2.swapSolid⟩ g ∧
    (g.2.LabelFree ∨ g = ⟨m + g'.1, H.glue x y₁ y₂ g'.2.swapSolid⟩) ∧
    (¬ ∃ C, g.2.Normal C) ∧ g.2.InvRun D ∧ g.2.RunKinds (n - 1) ∧
    r = TerminationC2_rk 1 (runMu n (H.glue x y₁ y₂ (tVar true))) 1 (TerminationC_nu g)) ∨
  (∃ (m : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g' : Σ n₀ : ℕ, Graph 3 n₀)
    (t : Tracked 3 (m + g'.1)),
    TerminationC2_Host n D H x y₁ y₂ ∧ g' ∈ 𝒯.Q ∧ t ∈ oDotT (H.glue x y₁ y₂ g'.2.swapSolid) ∧
    g = ⟨t.nOut, t.g⟩ ∧ t.g.DoublyConnected ∧ t.g.labels.length ≤ 1 ∧
    t.g.RunKinds (n - 1) ∧ t.g.InvRun D ∧ t.g.DotFree ∧ (∃ C, t.g.Normal C) ∧
    TerminationC_RI n D ⟨t.nOut, t.g⟩ ∧ ¬ t.g.LabelFree ∧ ¬ t.g.IsQGraph ∧
    r = TerminationC2_rk 1 (runMu n (H.glue x y₁ y₂ (tVar true))) 0 0)

end Rank

/-! ## Every step of a run lowers the rank -/

section Key

open private GlobalGoodB_dotExcess_zero from RBM8D.GlobalExp.GlobalGoodB

/-- **The `O_dot` forms of a substituted graph in the run** ([II, Lemma 6.5], [II, Lemma 6.8]):
each is an output of the run, or a graph of the run of a rank below that of the host at tier
`1`. -/
private theorem TerminationC2_piece_out {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.tSubst (n - 1))
    (hIt : (H.glue x y₁ y₂ g.2.swapSolid).InvRun D)
    (hKt : (H.glue x y₁ y₂ g.2.swapSolid).RunKinds (n - 1))
    {t : Tracked 3 (m + g.1)} (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) :
    TerminationC_Out n D ⟨t.nOut, t.g⟩ ∨ ∃ r', r' < TerminationC2_rk 1
      (runMu n (H.glue x y₁ y₂ (tVar true))) 1 0 ∧ TerminationC2_Good n D 𝒯 ⟨t.nOut, t.g⟩ r' := by
  obtain ⟨hN, hdf, hI, hK, hdc, hv, hT, hn0, hNL, hlab, hmu, hlb⟩ :=
    TerminationC2_piece hH hF hG hg hIt hKt ht
  have h0 : t.g.dotExcess = 0 := GlobalGoodB_dotExcess_zero hdf
  by_cases hL : t.g.LabelFree
  · exact Or.inr ⟨_, TerminationC2_rk_lt_mu (hmu hL), Or.inl ⟨⟨hN,
      TerminationC2_ri_lf hL hI hv hdc hT (fun h => absurd h0 h) hK, hL, hK⟩, rfl⟩⟩
  rcases hlb hL with ⟨hQs, hP, hQ⟩ | hD
  · by_cases hq : t.g.IsQGraph
    · exact Or.inr ⟨_, TerminationC2_rk_lt_a (by norm_num), Or.inr (Or.inl ⟨hN,
        TerminationC2_ri_of hI hv hdc hT hNL hlab hP hQ (fun h => absurd h0 h) hK, hq, hK, rfl⟩)⟩
    by_cases hD : (D : ℤ) < t.g.ord
    · exact Or.inl (TerminationC2_out_high hN h0 hD hdc hI hn0 hNL hlab)
    exact Or.inr ⟨_, TerminationC2_rk_lt_b (by norm_num), Or.inr (Or.inr (Or.inr
      ⟨m, H, x, y₁, y₂, g, t, hG, hQs, ht, rfl, hdc, hlab, hK, hI, hdf, hN,
        TerminationC2_ri_of hI hv hdc hT hNL hlab hP (fun h => absurd h hq)
          (fun h => absurd h0 h) hK, hL, hq, rfl⟩))⟩
  · exact Or.inl (TerminationC2_out_high hN h0 hD hdc hI hn0 hNL hlab)

/-- **The substituted graphs of Steps 2–3** ([II, (4.15)]): each is an output of the run, or a
graph of the run of a rank below that of the host. -/
private theorem TerminationC2_subst_out {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.tSubst (n - 1))
    (hIt : (H.glue x y₁ y₂ g.2.swapSolid).InvRun D)
    (hKt : (H.glue x y₁ y₂ g.2.swapSolid).RunKinds (n - 1)) :
    TerminationC_Out n D ⟨m + g.1, H.glue x y₁ y₂ g.2.swapSolid⟩ ∨ ∃ r', r' < TerminationC2_rk 1
      (runMu n (H.glue x y₁ y₂ (tVar true))) 2 0 ∧
      TerminationC2_Good n D 𝒯 ⟨m + g.1, H.glue x y₁ y₂ g.2.swapSolid⟩ r' := by
  by_cases hNn : ∃ C, (H.glue x y₁ y₂ g.2.swapSolid).Normal C
  · obtain ⟨C, hC⟩ := hNn
    rcases TerminationC2_piece_out hH hF hG hg hIt hKt (TerminationC2_self_mem_oDotT hC) with
      h | ⟨r', hr', hgood⟩
    · exact Or.inl h
    · exact Or.inr ⟨r', hr'.trans (TerminationC2_rk_lt_b (by norm_num)), hgood⟩
  · exact Or.inr ⟨_, TerminationC2_rk_lt_b (b := 1) (by norm_num), Or.inr (Or.inr (Or.inl
      ⟨m, H, x, y₁, y₂, g, hG, hg, hIt, hKt, Relation.ReflTransGen.refl, Or.inr rfl, hNn, hIt,
        hKt, rfl⟩))⟩

/-- A host of Steps 2–3 is normal regular. -/
private theorem TerminationC2_host_normal {g : Σ n₀ : ℕ, Graph 3 n₀}
    (h : TerminationC_GlueHost g) : ∃ C, g.2.Normal C := by
  obtain ⟨m, H, x, y₁, y₂, rfl, hP⟩ := h
  exact hP.2.1

/-- A graph in the form `Γ₀ Q_x(Γ̃₀)` has a label. -/
private theorem TerminationC2_not_lf_of_form {k n : ℕ} {Γ : Graph k n} {u : Atom k n}
    (h : Γ.IsQFormAt u) : ¬ Γ.LabelFree := by
  obtain ⟨⟨c, hc, hl⟩, -⟩ := h
  intro hL
  rw [hL c hc] at hl
  cases hl

/-- A `Q`-graph has a label. -/
private theorem TerminationC2_not_lf_of_q {k n : ℕ} {Γ : Graph k n} (h : Γ.IsQGraph) :
    ¬ Γ.LabelFree := by
  obtain ⟨u, ⟨c, hc, hl⟩, -⟩ := h
  intro hL
  rw [hL c hc] at hl
  cases hl

open private Termination_inv1 Termination_not_qGraph from RBM8D.GlobalExp.Termination
open private GlobalGoodB_dotExcess_zero from RBM8D.GlobalExp.GlobalGoodB

/-- **The steps at a graph without labels with the invariant of a run** lower the rank: Step 1,
the removal of a redundant dotted edge, the steps on `×`-dotted edges and on the coefficient, the
reordering to a host, and the substitution of Steps 2–3. -/
private theorem TerminationC2_key_lf {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hg : TerminationC2_LF n D g) {l : TerminationC_Loc g.1} (hA : TerminationC_Adm n D 𝔈 g l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, TerminationC_Out n D s ∨ ∃ r', r' <
      TerminationC2_rk 1 (runMu n g.2) 2 (TerminationC_nu g) ∧ TerminationC2_Good n D 𝒯 s r' := by
  intro s hs
  have hK' := TerminationK_step hF h𝒯 hA hg.2.2.2 s hs
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 g _ (TerminationC_Adm.step hA) hg.2.1.1 s hs
  obtain ⟨n₀, Γ⟩ := g
  cases l with
  | loc o x =>
    rcases TerminationC2_loc hH hF h𝒯 hA hg s hs with ⟨hs', hmu⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inr ⟨_, TerminationC2_rk_lt_mu hmu, Or.inl ⟨hs', rfl⟩⟩
    · exact Or.inr ⟨_, TerminationC2_rk_lt_a (by norm_num), Or.inr (Or.inl ⟨h1, h2, h3, h4, rfl⟩)⟩
  | dot => exact absurd hg.1 hA
  | dropDot Γ' =>
    obtain ⟨hN', hR', hK'', hlf, -, hmu⟩ := TerminationC2_dropDot hH hF h𝒯 hA hg.2.1 hg.2.2.2
    rw [List.mem_singleton.1 hs]
    exact Or.inr ⟨_, TerminationC2_rk_lt_mu hmu, Or.inl ⟨⟨hN', hR', hlf hg.2.2.1, hK''⟩, rfl⟩⟩
  | reorder Γ' =>
    have hnu := TerminationC_nu_reorder (𝒯 := 𝒯) hA s hs
    rw [List.mem_singleton.1 hs] at hnu ⊢
    obtain ⟨hs', hmu⟩ := TerminationC2_lf_reorder hH hA.1 hg
    refine Or.inr ⟨_, ?_, Or.inl ⟨hs', rfl⟩⟩
    simp only at hmu ⊢
    rw [hmu]
    exact TerminationC2_rk_lt_c hnu
  | xdotDup i =>
    have hnu := TerminationC_nu_xdotDup (𝒯 := 𝒯) hA s hs
    obtain ⟨hi, ⟨hk, hx, hy, -⟩, -, -⟩ := hA
    have e : s = ⟨n₀, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩ := by
      rw [List.mem_singleton.1 hs]
      simp only [List.getElem?_eq_getElem hi, Option.toList_some]
    subst e
    obtain ⟨hs', hmu⟩ := TerminationC2_lf_dup hH ⟨i, hi⟩ hk hx hy hg
    refine Or.inr ⟨_, ?_, Or.inl ⟨hs', rfl⟩⟩
    simp only [Fin.getElem_fin] at hmu ⊢
    rw [hmu]
    exact TerminationC2_rk_lt_c hnu
  | xdotDrop i j =>
    have hnu := TerminationC_nu_xdotDrop (𝒯 := 𝒯) hA s hs
    obtain ⟨hi, hj, ⟨hij, hc, hk, hx, hy, -⟩, -, -⟩ := hA
    rw [List.mem_singleton.1 hs] at hnu ⊢
    obtain ⟨hs', hmu⟩ := TerminationC2_lf_drop hH ⟨i, hi⟩ ⟨j, hj⟩ hij hc hk hx hy hg
    refine Or.inr ⟨_, ?_, Or.inl ⟨hs', rfl⟩⟩
    simp only at hmu ⊢
    rw [hmu]
    exact TerminationC2_rk_lt_c hnu
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm =>
    have hnu := TerminationC_nu_coeffNorm (𝒯 := 𝒯) hA s hs
    rw [List.mem_singleton.1 hs] at hnu ⊢
    obtain ⟨hs', hmu⟩ := TerminationC2_lf_coeff hH hg
    refine Or.inr ⟨_, ?_, Or.inl ⟨hs', rfl⟩⟩
    simp only at hmu ⊢
    rw [hmu]
    exact TerminationC2_rk_lt_c hnu
  | subst m H x y₁ y₂ =>
    obtain ⟨he, hD, hn', hP⟩ := hA
    obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.1 he
    cases eq_of_heq he
    obtain ⟨-, ⟨hI, hv, -⟩, hL, -⟩ := hg
    obtain ⟨hB, -⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
    have h0 := GlobalGoodB_dotExcess_zero hP.2.2.1
    have hPl : (H.glue x y₁ y₂ (tVar true)).Plain := by
      rcases hv.1 with h | h
      · exact h
      · rw [Graph.paperOrd_of_dotExcess h0] at h
        exact absurd h hD
    have hG : TerminationC2_Host n D H x y₁ y₂ := ⟨hD, hn', hP, hB, hPl⟩
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hs
    obtain ⟨g'', hg'', rfl⟩ := List.mem_map.1 hg'
    rcases TerminationC2_subst_out hH hF hG hg'' hI' hK' with h | ⟨r', hr', hgood⟩
    · exact Or.inl h
    · exact Or.inr ⟨r', hr'.trans_le (by
        rcases Nat.eq_zero_or_pos (TerminationC_nu ⟨m + 1, H.glue x y₁ y₂ (tVar true)⟩) with
          h | h
        · rw [h]
        · exact (TerminationC2_rk_lt_c h).le), hgood⟩
  | qexp x => exact absurd hg.2.2.1 (TerminationC2_not_lf_of_form hA.2.2.2.1)

/-- **The steps at a `Q`-graph** with the invariant of a run: only the removal of a redundant
dotted edge (and the empty sum at a `×`-dotted loop) applies, and it lowers `runMu`. -/
private theorem TerminationC2_key_qb {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hN : ∃ C, g.2.Normal C) (hR : TerminationC_RI n D g) (hQ : g.2.IsQGraph)
    (hK : g.2.RunKinds (n - 1)) {l : TerminationC_Loc g.1} (hA : TerminationC_Adm n D 𝔈 g l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, TerminationC_Out n D s ∨ ∃ r', r' <
      TerminationC2_rk 0 (runMu n g.2) 0 0 ∧ TerminationC2_Good n D 𝒯 s r' := by
  intro s hs
  have hnl := TerminationC2_not_lf_of_q hQ
  cases l with
  | loc o x => exact absurd hA.2.2.2.1 hnl
  | dot => exact absurd hN hA
  | dropDot Γ' =>
    obtain ⟨hN', hR', hK', -, hq, hmu⟩ := TerminationC2_dropDot hH hF h𝒯 hA hR hK
    rw [List.mem_singleton.1 hs]
    exact Or.inr ⟨_, TerminationC2_rk_lt_mu hmu, Or.inr (Or.inl ⟨hN', hR', hq hQ, hK', rfl⟩)⟩
  | reorder Γ' =>
    exact absurd (TerminationC2_reorder_lf_rev hA.1 (TerminationC2_host_lf hA.2.2)) hnl
  | xdotDup i => exact absurd hA.2.2.1.1 hnl
  | xdotDrop i j => exact absurd hA.2.2.2.1.1 hnl
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm => exact absurd hA.1.1 hnl
  | subst m H x y₁ y₂ =>
    exact absurd (TerminationC2_host_lf ⟨m, H, x, y₁, y₂, hA.1, hA.2.2.2⟩) hnl
  | qexp x => exact absurd hQ hA.2.2.2.2.1

open private GlobalGoodB_oDot_label from RBM8D.GlobalExp.GlobalGoodB

/-- **The steps at a substituted graph of Steps 2–3 that is not normal regular** lower the rank:
`O_dot` gives outputs and graphs of the run below the host (through `TerminationC2_PStep` when
steps on `×`-dotted edges or on the coefficient were taken before), and the steps on `×`-dotted
edges and on the coefficient lower `TerminationC_nu`. -/
private theorem TerminationC2_key_raw {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g' : Σ n₀ : ℕ, Graph 3 n₀} (hg' : g' ∈ 𝒯.tSubst (n - 1))
    (hIt : (H.glue x y₁ y₂ g'.2.swapSolid).InvRun D)
    (hKt : (H.glue x y₁ y₂ g'.2.swapSolid).RunKinds (n - 1)) {X : Σ n₀ : ℕ, Graph 3 n₀}
    (hch : Relation.ReflTransGen TerminationC2_NuStep ⟨m + g'.1, H.glue x y₁ y₂ g'.2.swapSolid⟩ X)
    (hlf : X.2.LabelFree ∨ X = ⟨m + g'.1, H.glue x y₁ y₂ g'.2.swapSolid⟩)
    (hNn : ¬ ∃ C, X.2.Normal C) (hI : X.2.InvRun D) (hK : X.2.RunKinds (n - 1))
    {l : TerminationC_Loc X.1} (hA : TerminationC_Adm n D 𝔈 X l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 X l, TerminationC_Out n D s ∨ ∃ r', r' <
      TerminationC2_rk 1 (runMu n (H.glue x y₁ y₂ (tVar true))) 1 (TerminationC_nu X) ∧
      TerminationC2_Good n D 𝒯 s r' := by
  intro s hs
  have hK' := TerminationK_step hF h𝒯 hA hK s hs
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 X _ (TerminationC_Adm.step hA) hI s hs
  have hraw : ∀ Γ' : Graph 3 X.1, TerminationC2_NuStep X ⟨X.1, Γ'⟩ → Γ'.LabelFree →
      (¬ ∃ C, Γ'.Normal C) → s = ⟨X.1, Γ'⟩ →
      TerminationC_nu ⟨X.1, Γ'⟩ < TerminationC_nu X →
      TerminationC_Out n D s ∨ ∃ r', r' <
        TerminationC2_rk 1 (runMu n (H.glue x y₁ y₂ (tVar true))) 1 (TerminationC_nu X) ∧
        TerminationC2_Good n D 𝒯 s r' := by
    intro Γ' hst hL' hN' hs' hnu
    subst hs'
    exact Or.inr ⟨_, TerminationC2_rk_lt_c hnu, Or.inr (Or.inr (Or.inl ⟨m, H, x, y₁, y₂, g', hG,
      hg', hIt, hKt, hch.tail hst, Or.inl hL', hN', hI', hK', rfl⟩))⟩
  obtain ⟨n₀, Γ⟩ := X
  cases l with
  | loc o x => exact absurd hA.2.2.1 hNn
  | dot =>
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hs
    rcases hlf with hL | he
    · obtain ⟨t, ht, hrel⟩ := TerminationC2_oDotT_chain hch t' ht'
      have hLG := TerminationC2_NuStep.labelFree hch hL
      have hLt : t.g.LabelFree := by
        intro c hc
        by_contra hne
        obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hne
        obtain ⟨c₀, hc₀, w, hw, -⟩ := GlobalGoodB_oDot_label ht hc hl
        rw [hLG c₀ hc₀] at hw
        cases hw
      obtain ⟨hN, hdf, hIt', hKt', hdc, hv, hT, -, -, -, hmu, -⟩ :=
        TerminationC2_piece hH hF hG hg' hIt hKt ht
      have h0 : t.g.dotExcess = 0 := GlobalGoodB_dotExcess_zero hdf
      obtain ⟨hLF', hmu'⟩ := TerminationC2_PStep.lf_chain hH hrel
        ⟨hN, TerminationC2_ri_lf hLt hIt' hv hdc hT (fun h => absurd h0 h) hKt', hLt, hKt'⟩
      refine Or.inr ⟨_, TerminationC2_rk_lt_mu ?_, Or.inl ⟨hLF', rfl⟩⟩
      simp only at hmu'
      rw [hmu']
      exact hmu hLt
    · simp only [Sigma.mk.inj_iff] at he
      obtain ⟨rfl, he⟩ := he
      cases eq_of_heq he
      rcases TerminationC2_piece_out hH hF hG hg' hIt hKt ht' with h | ⟨r', hr', hgood⟩
      · exact Or.inl h
      · exact Or.inr ⟨r', hr'.trans_le TerminationC2_rk_le_c, hgood⟩
  | dropDot Γ' => exact absurd hA.2.1 hNn
  | reorder Γ' =>
    exact absurd (TerminationC2_reorder_normal_rev hA.1 (TerminationC2_host_normal hA.2.2)) hNn
  | xdotDup i =>
    have hnu := TerminationC_nu_xdotDup (𝒯 := 𝒯) hA s hs
    obtain ⟨hi, ⟨hk, hx, hy, -⟩, hcell, -⟩ := hA
    have hL := hcell.1
    have e : s = ⟨n₀, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩ := by
      rw [List.mem_singleton.1 hs]
      simp only [List.getElem?_eq_getElem hi, Option.toList_some]
    have hst := TerminationC2_NuStep.dup Γ ⟨i, hi⟩ hk (hL _ (List.getElem_mem hi)) hx hy
    simp only [Fin.getElem_fin] at hst
    refine hraw _ hst (fun c hc => ?_) (fun ⟨C, hC⟩ => hNn ⟨_, TerminationC2_normal_of
      (fun c hc => ⟨c, List.mem_append_left _ hc, Or.inl rfl⟩) (fun c hc => ?_) hC⟩) e
      (by rw [← e]; exact hnu)
    · rcases List.mem_append.1 hc with hc | hc
      · exact hL c hc
      · rw [List.mem_singleton.1 hc]; exact hL _ (List.getElem_mem hi)
    · rcases List.mem_append.1 hc with hc | hc
      · exact ⟨c, hc, Or.inl rfl⟩
      · rw [List.mem_singleton.1 hc]; exact ⟨_, List.getElem_mem hi, Or.inl rfl⟩
  | xdotDrop i j =>
    have hnu := TerminationC_nu_xdotDrop (𝒯 := 𝒯) hA s hs
    obtain ⟨hi, hj, ⟨hij, hc, hk, hx, hy, -⟩, hcell, -⟩ := hA
    have hL := hcell.1
    have e : s = ⟨n₀, ⟨Γ.comps.eraseIdx j, Γ.coeff⟩⟩ := List.mem_singleton.1 hs
    have hst := TerminationC2_NuStep.drop Γ ⟨i, hi⟩ ⟨j, hj⟩ hij hc hk
      (hL _ (List.getElem_mem hi)) hx hy
    have hij' : i ≠ j := fun h => hij (Fin.ext h)
    refine hraw _ hst (fun c hc => hL c (List.mem_of_mem_eraseIdx hc))
      (fun ⟨C, hC⟩ => hNn ⟨_, TerminationC2_normal_of (fun c hcm => ?_)
        (fun c hc => ⟨c, List.mem_of_mem_eraseIdx hc, Or.inl rfl⟩) hC⟩) e
      (by rw [← e]; exact hnu)
    rcases TerminationC2_mem_eraseIdx hcm hj with h | rfl
    · exact ⟨c, h, Or.inl rfl⟩
    · refine ⟨Γ.comps[i], List.mem_eraseIdx_iff_getElem.2 ⟨i, hi, hij', rfl⟩, ?_⟩
      rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hk, h⟩
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm =>
    have hnu := TerminationC_nu_coeffNorm (𝒯 := 𝒯) hA s hs
    have hL : Γ.LabelFree := hA.1.1
    set Γ' : Graph 3 n₀ :=
      ⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩ with hΓ'
    have e : s = ⟨n₀, Γ'⟩ := List.mem_singleton.1 hs
    have hL' : Γ'.LabelFree := fun c hc => hL c hc
    have hN' : ¬ ∃ C, Γ'.Normal C := by
      rintro ⟨C, hC⟩
      exact hNn ⟨_, TerminationC2_normal_of (Γ := Γ') (Γ' := Γ)
        (fun c hc => ⟨c, hc, Or.inl rfl⟩) (fun c hc => ⟨c, hc, Or.inl rfl⟩) hC⟩
    exact hraw Γ' (TerminationC2_NuStep.coeff Γ) hL' hN' e (by rw [← e]; exact hnu)
  | subst m' H' x' y₁' y₂' =>
    exact absurd (TerminationC2_host_normal ⟨m', H', x', y₁', y₂', hA.1, hA.2.2.2⟩) hNn
  | qexp x' => exact absurd hA.1 hNn

/-- **The steps at an `O_dot` form with labels of a substituted graph of `Q`**: only the
`Q`-expansion of Step 3 (and the empty sum at a `×`-dotted loop) applies; its outputs are outputs
of the run or graphs of the run below the host. -/
private theorem TerminationC2_key_lp {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g' : Σ n₀ : ℕ, Graph 3 n₀} (hg' : g' ∈ 𝒯.Q) {t : Tracked 3 (m + g'.1)}
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g'.2.swapSolid)) (hdc : t.g.DoublyConnected)
    (hlab : t.g.labels.length ≤ 1) (hK : t.g.RunKinds (n - 1)) (hI : t.g.InvRun D)
    (hdf : t.g.DotFree) (hN : ∃ C, t.g.Normal C) (hL : ¬ t.g.LabelFree)
    {l : TerminationC_Loc t.nOut} (hA : TerminationC_Adm n D 𝔈 ⟨t.nOut, t.g⟩ l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 ⟨t.nOut, t.g⟩ l, TerminationC_Out n D s ∨ ∃ r', r' <
      TerminationC2_rk 1 (runMu n (H.glue x y₁ y₂ (tVar true))) 0 0 ∧
      TerminationC2_Good n D 𝒯 s r' := by
  intro s hs
  cases l with
  | loc o x => exact absurd hA.2.2.2.1 hL
  | dot => exact absurd hN hA
  | dropDot Γ' =>
    obtain ⟨⟨i, c, hc, hk, -, -⟩, -, -⟩ := hA
    exact absurd hk (hdf c (List.mem_of_getElem? hc))
  | reorder Γ' =>
    exact absurd (TerminationC2_reorder_lf_rev hA.1 (TerminationC2_host_lf hA.2.2)) hL
  | xdotDup i => exact absurd hA.2.2.1.1 hL
  | xdotDrop i j => exact absurd hA.2.2.2.1.1 hL
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm => exact absurd hA.1.1 hL
  | subst m' H' x' y₁' y₂' =>
    exact absurd (TerminationC2_host_lf ⟨m', H', x', y₁', y₂', hA.1, hA.2.2.2⟩) hL
  | qexp x' =>
    rcases TerminationC2_qexp hH hF h𝒯 hG hg' ht hdc hlab hK hI hA s hs with h | ⟨h1, h2⟩ | h
    · exact Or.inl h
    · exact Or.inr ⟨_, TerminationC2_rk_lt_mu h2, Or.inl ⟨h1, rfl⟩⟩
    · exact Or.inr ⟨_, TerminationC2_rk_lt_a (by norm_num), Or.inr (Or.inl ⟨h.1, h.2.1, h.2.2.1,
        h.2.2.2, rfl⟩)⟩

/-- **Every step of a run driven by an admissible selector lowers the rank** ([II, Lemma 6.8]): at
every graph of the run that is not an output, the selector gives a step (the graph lies in
`TerminationC_Dom`), and every graph of the step is an output or a graph of the run of smaller
rank. -/
private theorem TerminationC2_key {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    {ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) (hℓ : AdmSelector n D 𝒯 𝔈 ℓ) :
    ∀ g r, TerminationC2_Good n D 𝒯 g r → ¬ TerminationC_Out n D g →
      TerminationC_Dom n D g ∧ ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g),
        TerminationC_Out n D s ∨ ∃ r', r' < r ∧ TerminationC2_Good n D 𝒯 s r' := by
  intro g r hg hO
  rcases hg with ⟨hLF, rfl⟩ | ⟨hN, hR, hQ, hK, rfl⟩ |
    ⟨m, H, x, y₁, y₂, g', hG, hg', hIt, hKt, hch, hlf, hNn, hI, hK, rfl⟩ |
    ⟨m, H, x, y₁, y₂, g', t, hG, hQs, ht, rfl, hdc, hlab, hK, hI, hdf, hN, hR, hL, hq, rfl⟩
  · have hD : TerminationC_Dom n D g := Or.inr hLF.2.1
    exact ⟨hD, TerminationC2_key_lf hH hF h𝒯 hLF (hℓ g hD hO).1⟩
  · have hD : TerminationC_Dom n D g := Or.inr hR
    exact ⟨hD, TerminationC2_key_qb hH hF h𝒯 hN hR hQ hK (hℓ g hD hO).1⟩
  · have hD : TerminationC_Dom n D g := Or.inl hNn
    exact ⟨hD, TerminationC2_key_raw hH hF h𝒯 hG hg' hIt hKt hch hlf hNn hI hK (hℓ g hD hO).1⟩
  · have hD : TerminationC_Dom n D ⟨t.nOut, t.g⟩ := Or.inr hR
    exact ⟨hD, TerminationC2_key_lp hH hF h𝒯 hG hQs ht hdc hlab hK hI hdf hN hL
      (hℓ _ hD hO).1⟩

end Key

/-! ## The run kinds of the substituted formal sum and of the inputs -/

section Start

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

open private h2Rec_struct from RBM8D.TExp.Second
open private chainLabelsAux_entries mem_chainLabelsAux_succ from RBM8D.TExp.Closure

/-- Labels with entries even in `[4, N]` have entries even in `[4, N']` for `N ≤ N'`. -/
private theorem TerminationC2_labelOK_mono {N N' : ℕ} (hN : N ≤ N') {o : List ℕ}
    (h : labelOK N o = true) : labelOK N' o = true := by
  simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  intro j hj
  obtain ⟨⟨h1, h2⟩, h3⟩ := h j hj
  exact ⟨⟨h1, h2.trans hN⟩, h3⟩

/-- The run kinds for the order `N` are run kinds for every larger order. -/
private theorem TerminationC2_runKinds_mono {k n N N' : ℕ} {Γ : Graph k n} (hN : N ≤ N')
    (h : Γ.RunKinds N) : Γ.RunKinds N' := by
  unfold Graph.RunKinds at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have := h c hc
  unfold Comp.isRunKind at this ⊢
  cases hk : c.kind <;> simp only [hk] at this ⊢ <;>
    first | exact this | exact TerminationC2_labelOK_mono hN this

/-- The kinds of [II, Def 3.2] are run kinds. -/
private theorem TerminationC2_runKinds_of_tKinds {k n N : ℕ} {Γ : Graph k n} (h : Γ.TKinds N) :
    Γ.RunKinds N := by
  unfold Graph.RunKinds
  unfold Graph.TKinds at h
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have := h c hc
  unfold Comp.isTKind at this
  unfold Comp.isRunKind
  split <;> simp_all

/-- The kinds of the graphs of `Err` are run kinds. -/
private theorem TerminationC2_runKinds_of_tKindsErr {k n N : ℕ} {Γ : Graph k n}
    (h : Γ.TKindsErr N) : Γ.RunKinds N := by
  unfold Graph.RunKinds
  unfold Graph.TKindsErr at h
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have := h c hc
  unfold Comp.isTKind at this
  unfold Comp.isRunKind
  split <;> simp_all

/-- The entries of the labels `chainLabelsAux f b` are at most `b + 2`. -/
private theorem TerminationC2_chain_le : ∀ f b, ∀ o ∈ chainLabelsAux f b, ∀ e ∈ o, e ≤ b + 2 := by
  intro f
  induction f with
  | zero => intro b o ho; simp [chainLabelsAux] at ho
  | succ f ih =>
    intro b o ho e he
    obtain ⟨j, hjb, -, -, h | ⟨o', ho', h⟩⟩ := mem_chainLabelsAux_succ.1 ho
    · subst h
      simp only [List.mem_singleton] at he
      omega
    · subst h
      rcases List.mem_cons.1 he with rfl | he
      · omega
      · have := ih (b - j) o' ho' e he
        omega

/-- **The graphs substituted in Steps 2–3 have the run kinds** for the order `n - 1`: the leading
term and the labelled `Θ` edges of `Σ_T` (labels of entries even in `[4, n - 1]`), the graphs of
`R`, `A`, `Q` (the kinds of [II, Def 3.2]) and of `Err`, and the recollision terms. -/
private theorem TerminationC2_tSubst_runKinds {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1) := by
  obtain ⟨-, hT⟩ := hH
  have hSh := hT.2.2.2.1
  have hth : ∀ o : List ℕ, labelOK (n - 1) o = true → (thetaLabelGraph o).RunKinds (n - 1) := by
    intro o ho
    unfold Graph.RunKinds
    simp [thetaLabelGraph, Comp.isRunKind, mkC, ho]
  intro g hg
  simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg
  rcases hg with (((((hg | hg) | hg) | hg) | hg) | hg) | hg
  · simp only [leadExp, List.mem_singleton] at hg
    subst hg
    exact hth [] (by simp [labelOK])
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hg
    refine hth o ?_
    simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    intro e he
    have h1 := chainLabelsAux_entries _ _ o ho e he
    have h2 := TerminationC2_chain_le _ _ o ho e he
    exact ⟨⟨h1.1, by omega⟩, h1.2⟩
  · exact TerminationC2_runKinds_of_tKinds (hSh.1.1 g (by simp [hg])).2.1
  · exact TerminationC2_runKinds_of_tKinds (hSh.1.1 g (by simp [hg])).2.1
  · exact TerminationC2_runKinds_of_tKinds (hSh.1.1 g (by simp [hg])).2.1
  · exact TerminationC2_runKinds_of_tKindsErr (hSh.1.2 g hg).2.1
  · have h0 : ∀ g ∈ tVarCorr, g.2.RunKinds 0 := by
      unfold Graph.RunKinds
      decide +kernel
    exact TerminationC2_runKinds_mono (Nat.zero_le _) (h0 g hg)

/-- The inputs of the run (the graphs of `A` and `Q` of the second order `T`-expansion) have the
invariant `Graph.InvRun`: one internal molecule with the clauses of `Graph.InvB'`, or a `Q`-graph
without internal atom. -/
private theorem TerminationC2_h2_invRun (D : ℕ) : ∀ g ∈ h2Rec.A ++ h2Rec.Q, g.2.InvRun D := by
  have h0 : ∀ g ∈ h2Rec.A ++ h2Rec.Q,
      (0 < g.1 ∧ (∀ b c : Fin g.1, g.2.SameMol (.inr b) (.inr c)) ∧ g.2.ColourInvB ∧
        g.2.ExtClause ∧ g.2.NoGhost ∧ g.2.LabelsInt ∧ g.2.TensorDiffusive) ∨
      (g.1 = 0 ∧ g.2.IsQGraph) := by
    decide +kernel
  intro g hg
  rcases h0 g hg with ⟨-, h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨⟨spdPM'_of_oneMol 3 g.1 g.2 h1, h2, h3, h4, h5⟩, h6⟩
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- **The inputs of the run are graphs of the run**: the graphs of `A` of the second order
`T`-expansion are normal regular without labels with the invariant of a run, those of `Q` are
normal regular `Q`-graphs with the invariant of a run. -/
private theorem TerminationC2_inputs {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) :
    ∀ g ∈ h2Rec.A ++ h2Rec.Q, TerminationC_Out n D g ∨ ∃ r, TerminationC2_Good n D 𝒯 g r := by
  have hD : 2 < D := by have := hH.2.1; have := hH.1; omega
  have h2 := h2Rec_struct Sig D hD
  have hSh := h2.2.2.2.1
  have hDef := h2.2.2.2.2
  intro g hg
  have hRAQ : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q := by
    rcases List.mem_append.1 hg with h | h <;> simp [h]
  have h4 : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q ++ h2Rec.Err := List.mem_append_left _ hRAQ
  obtain ⟨hN, hTK, -, hdc⟩ := hSh.1.1 g hRAQ
  obtain ⟨hT, h0, hNL, hlab⟩ := hDef.2.1 g h4
  have hI := TerminationC2_h2_invRun D g hg
  have hv := TerminationB_inv_h2 n D hD g hg
  have hK : g.2.RunKinds (n - 1) :=
    TerminationC2_runKinds_mono (by have := hH.1; omega) (TerminationC2_runKinds_of_tKinds hTK)
  right
  rcases List.mem_append.1 hg with hA | hQ
  · have hL := (hSh.2.2.1 g hA).1
    exact ⟨_, Or.inl ⟨⟨hN, TerminationC2_ri_lf hL hI hv hdc hT (fun h => absurd h0 h) hK, hL,
      hK⟩, rfl⟩⟩
  · have hq := (hSh.2.2.2.1 g hQ).1
    obtain ⟨-, hP1, -⟩ := TerminationC2_qGraph_labels hq
    obtain ⟨hspd, hql, -⟩ := hDef.1.2.2 g hQ
    exact ⟨_, Or.inr (Or.inl ⟨hN, TerminationC2_ri_of hI hv hdc hT hNL hlab hP1
      (fun _ => ⟨hspd, hql⟩) (fun h => absurd h0 h) hK, hq, hK, rfl⟩)⟩

end Start

/-! ## [II, Lemma 6.8] -/

/-- **[II, Lemma 6.8]** in the block reading, for selectors: for a family `𝔈` of `Q`-expansions of
[II, Lemma 4.15] (`QExpFamilyStmt`),
(i) for `n ≥ 3`, an `(n - 1)`-th order `T`-expansion `𝒯` with error order `D` and **every**
admissible selector `ℓ` (`AdmSelector`), the run of [II, Strategy 6.6] driven by `ℓ` from the
graphs of `A` and `Q` of the second order `T`-expansion ends (`SelRunB`), and every output graph
is an output with the clauses of [II, Lemma 6.8] (`TerminationC_Out`);
(ii) one selector, a function of the graph alone, is admissible for every `n ≥ 3`, `D` and
`T`-expansion `𝒯` of order `n - 1` with error order `D`. -/
theorem strategyB_sel (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (hF : QExpFamilyStmt 𝔈) :
    (∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec)
      (ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1),
      3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D → AdmSelector n D 𝒯 𝔈 ℓ →
      ∃ F : Expansion 3, SelRunB n D 𝒯 𝔈 ℓ (h2Rec.A ++ h2Rec.Q) F ∧
        ∀ g ∈ F, TerminationC_Out n D g) ∧
    ∃ ℓ₀ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1,
      ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
        AdmSelector n D 𝒯 𝔈 ℓ₀ := by
  refine ⟨fun n D Sig 𝒯 ℓ hn hT hℓ => ?_, TerminationC_admSelector 𝔈 hF⟩
  have hH : TerminationC2_Hyp n D Sig 𝒯 := ⟨hn, hT⟩
  exact TerminationC2_runs hℓ (TerminationC2_Good n D 𝒯)
    (TerminationC2_key hH hF (TerminationC2_tSubst_runKinds hH) hℓ) _ (TerminationC2_inputs hH)

section Instances

open private h2Rec_struct from RBM8D.TExp.Second

end Instances

end RBM8D.Graphs
