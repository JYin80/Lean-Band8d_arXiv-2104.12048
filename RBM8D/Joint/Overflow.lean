module

public import RBM8D.Joint.Relabel
public import RBM8D.Joint.Words

@[expose] public section

/-!
# The leading term beyond `Σ_T^{(n)}`

[II, §6.1] after (expand_thetan), [II, Cor 3.8]: for a nonempty label `o` with entries even in
`[4, n]` that is not a label of `Σ_T^{(n)}`, the `O_dot` forms of `m Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖}` are
the two graphs `Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖} ×_{⊕⊖}` and `Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊕} •_{⊕⊖}` without internal
atom (`Overflow.formA`, `Overflow.formB`), the relabellings by `o` of the graphs with the plain `Θ`
edge (`G14.relabel`). Their properties are those of [II, Def 3.2] and the clauses of [II, Def 6.3]
for a graph of `A` without internal atom (`G14.overflowStmt`).
-/

noncomputable section

namespace RBM8D

open Graphs

namespace Overflow

/-- `Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖} ×_{⊕⊖}`: the `O_dot` term with the `×`-dotted edge on the solid edge. -/
def formA (o : List ℕ) : Graph 3 0 :=
  ⟨[mkC (.theta o) (.inl 0) (.inl 1), mkC (.G .minus) (.inl 1) (.inl 2),
    mkC .xdot (.inl 1) (.inl 2)], (-1 : Coeff) ^ 0 * cm⟩

/-- `Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊕} •_{⊕⊖}`: the `O_dot` term with the dotted edge `⊕ – ⊖`, the solid edge
having become a weight on `⊕`. -/
def formB (o : List ℕ) : Graph 3 0 :=
  ⟨[mkC (.theta o) (.inl 0) (.inl 1), mkC (.weight .minus) (.inl 1) (.inl 1),
    mkC .dot (.inl 1) (.inl 2)], (-1 : Coeff) ^ 0 * cm⟩

/-- The `O_dot` forms of `m Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖}` are `formA o` and `formB o`. -/
theorem oDot_thetaLabelGraph (o : List ℕ) :
    oDot (thetaLabelGraph o) = [⟨0, formA o⟩, ⟨0, formB o⟩] := rfl

theorem formA_relabel (o : List ℕ) : (formA []).relabelRoot o = formA o := by
  simp [Graph.relabelRoot, formA, mkC]

theorem formB_relabel (o : List ℕ) : (formB []).relabelRoot o = formB o := by
  simp [Graph.relabelRoot, formB, mkC]

section Base

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

local macro "kdec" : tactic => `(tactic| decide +kernel)

instance Overflow_decTKinds {k n : ℕ} (N : ℕ) (Γ : Graph k n) : Decidable (Γ.TKinds N) :=
  inferInstanceAs (Decidable (_ = true))

instance Overflow_decAtExternals {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.AtExternals :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance Overflow_decLabelFree {k n : ℕ} (Γ : Graph k n) : Decidable Γ.LabelFree :=
  inferInstanceAs (Decidable (∀ c ∈ Γ.comps, c.label = none))

instance Overflow_decNoLabDot {k n : ℕ} (Γ : Graph k n) : Decidable Γ.NoLabDot := by
  unfold Graph.NoLabDot; infer_instance

/-- A graph without internal atom is doubly connected (empty nets). -/
private theorem Overflow_dc_of_zero {Γ : Graph 3 0} (h : Γ.Spans ∅) : Γ.DoublyConnected :=
  ⟨∅, ∅, Finset.disjoint_empty_left _, by simp, by simp, h, h⟩

/-- The properties of a graph without internal atom that `G14.relabel` carries to the relabelling
of the root `Θ`. -/
private def Base (F : Graph 3 0) : Prop :=
  G14.RootedTheta F ∧ F.Normal 12 ∧ F.TKinds 0 ∧ F.AtExternals ∧ F.Spans ∅ ∧ F.LabelFree ∧
    ¬ F.IsRecollision {1, 2} ∧ F.RootAtPlus ∧ F.TensorDiffusive ∧ F.DotsAcyclic ∧ F.NoLabDot ∧
    F.labels.length ≤ 1 ∧ F.Plain ∧ F.MinusProfile

private theorem base_formA : Base (formA []) ∧ (formA []).ord = 3 ∧ ¬ (formA []).PMBlock := by
  refine ⟨⟨⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl, by decide, by kdec⟩, ?_⟩, ?_, ?_⟩
  · unfold formA; kdec
  · unfold formA; kdec
  · unfold formA; kdec

private theorem base_formB : Base (formB []) ∧ (formB []).ord = 4 := by
  refine ⟨⟨⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl, by decide, by kdec⟩, ?_⟩, ?_⟩
  · unfold formB; kdec
  · unfold formB; kdec

end Base

/-- The conclusion of `G14.overflowStmt` for the relabelling by `o` of a graph without internal
atom with the properties of `Base`, of order `r`, with `n + 2 ≤ r + Words.labelInc o` and
`n + 3 ≤ r + Words.labelInc o` if `⊕`, `⊖` lie in one dotted block. -/
private theorem lift {n : ℕ} {o : List ℕ} {F : Graph 3 0} (hF : Base F)
    (hlab : labelOK n o = true) (hge : (n : ℤ) + 2 ≤ F.ord + Words.labelInc o)
    (hpm : F.PMBlock → (n : ℤ) + 3 ≤ F.ord + Words.labelInc o) :
    (∃ C, (F.relabelRoot o).Normal C) ∧ (F.relabelRoot o).TKinds n ∧
      (F.relabelRoot o).AtExternals ∧ (F.relabelRoot o).DoublyConnected ∧
      (F.relabelRoot o).LabelFree ∧ (n : ℤ) + 2 ≤ (F.relabelRoot o).ord ∧
      ¬ (F.relabelRoot o).IsRecollision {1, 2} ∧ spdPM' (F.relabelRoot o) ∧
      (F.relabelRoot o).RootAtPlus ∧ (F.relabelRoot o).TensorDiffusive ∧
      (F.relabelRoot o).dotExcess = 0 ∧ (F.relabelRoot o).NoLabDot ∧
      (F.relabelRoot o).labels.length ≤ 1 ∧
      ((F.relabelRoot o).PMBlock → (n : ℤ) + 3 ≤ (F.relabelRoot o).ord) ∧
      (F.relabelRoot o).Plain ∧ (F.relabelRoot o).MinusProfile := by
  obtain ⟨hR, hN, hK, hE, hS, hL, hRec, hP, hT, hD, hX, hl, hPl, hM⟩ := hF
  have hent : ∀ e ∈ o, 2 ≤ e := fun e he => by
    have := List.all_eq_true.1 hlab e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    omega
  obtain ⟨h1, h2, -, h4, h5, h6, h7, -, h9, -, h11, -, -, -, h15, h16, h17, h18, h19, h20, -, -, -,
    h24, -, h26⟩ := G14.relabel F o hR
  have hord : (F.relabelRoot o).ord = F.ord + Words.labelInc o := by
    rw [h1, Words.labelInc_cast o hent]
  refine ⟨⟨12, h4 12 hN⟩, h2 0 n (Nat.zero_le _) hlab hK, h5 hE, h6 (Overflow_dc_of_zero hS),
    h7 hL, by rw [hord]; exact hge, fun h => hRec (h9.1 h),
    spdPM'_of_oneMol 3 0 _ fun b => b.elim0, h15 hP, h16 hT,
    by rw [h17]; exact (F.dotsAcyclic_iff_dotExcess_eq_zero).1 hD, h18 hX, by rw [h19]; exact hl,
    fun h => by rw [hord]; exact hpm (h20.1 h), h24 hPl, h26 hM⟩

end Overflow

/-- The leading term beyond `Σ_T^{(n)}` ([II, §6.1]): for a nonempty label `o` with entries even
in `[4, n]` that is not a label of `Σ_T^{(n)}`, every `O_dot` form of `m Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖}` has
no internal atom, is normal regular with the kinds of [II, Def 3.2] and the properties (9),
(10), is label-free of order `≥ n + 2` (order `≥ n + 3` if `⊕`, `⊖` lie in one dotted block), is
not a recollision graph, and has the clauses of `TRec.Def63` on a graph of `A` without internal
atom and the profile `Graph.MinusProfile` at `⊖`. -/
def G14.overflowStmt : Prop :=
  ∀ (n : ℕ) (o : List ℕ), 3 ≤ n → o ≠ [] → labelOK n o = true → o ∉ chainLabels n →
    ∀ g ∈ oDot (thetaLabelGraph o),
      g.1 = 0 ∧ (∃ C, g.2.Normal C) ∧ g.2.TKinds n ∧ g.2.AtExternals ∧ g.2.DoublyConnected ∧
      g.2.LabelFree ∧ (n : ℤ) + 2 ≤ g.2.ord ∧ ¬ g.2.IsRecollision {1, 2} ∧ spdPM' g.2 ∧
      g.2.RootAtPlus ∧ g.2.TensorDiffusive ∧ g.2.dotExcess = 0 ∧ g.2.NoLabDot ∧
      g.2.labels.length ≤ 1 ∧ (g.2.PMBlock → (n : ℤ) + 3 ≤ g.2.ord) ∧ g.2.Plain ∧
      g.2.MinusProfile

/-- The leading term beyond `Σ_T^{(n)}` holds (`G14.overflowStmt`). -/
theorem G14.overflow_stmt : G14.overflowStmt := by
  intro n o _ ho hlab hchain g hg
  have hent : ∀ e ∈ o, 4 ≤ e ∧ e % 2 = 0 := fun e he => by
    have := List.all_eq_true.1 hlab e he
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.2⟩
  have hlt : n < Words.labelInc o + 2 := by
    by_contra h
    exact hchain (Words.mem_chainLabels.2 ⟨ho, hent, by omega⟩)
  rw [Overflow.oDot_thetaLabelGraph] at hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · obtain ⟨hB, hord, hpm⟩ := Overflow.base_formA
    have := Overflow.lift (n := n) hB hlab (by rw [hord]; omega) (fun h => absurd h hpm)
    rw [Overflow.formA_relabel] at this
    exact ⟨rfl, this⟩
  · obtain ⟨hB, hord⟩ := Overflow.base_formB
    have := Overflow.lift (n := n) hB hlab (by rw [hord]; omega) (fun _ => by rw [hord]; omega)
    rw [Overflow.formB_relabel] at this
    exact ⟨rfl, this⟩

end RBM8D

end
