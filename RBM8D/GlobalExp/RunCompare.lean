module

public import RBM8D.GlobalExp.TerminationC2
public import RBM8D.TExp.Closure
public import Batteries.Tactic.OpenPrivate
public import RBM8D.Graph.Local.EdgeOrder
public import RBM8D.Graph.Local.DotNorm
public import RBM8D.GlobalExp.RunClauses
public import RBM8D.GlobalExp.TerminationB
public import RBM8D.GlobalExp.Termination
public import RBM8D.GlobalExp.SubstSPD
public import RBM8D.GlobalExp.SubstDC
public import RBM8D.GlobalExp.GlobalGoodRows
public import RBM8D.TExp.Second
import all RBM8D.Graph.Local.EdgeOrder
import all RBM8D.Graph.Local.DotNorm
import all RBM8D.GlobalExp.RunClauses
import all RBM8D.GlobalExp.TerminationB
import all RBM8D.GlobalExp.Termination
import all RBM8D.GlobalExp.TerminationC2
import all RBM8D.GlobalExp.SubstSPD
import all RBM8D.GlobalExp.SubstDC
import all RBM8D.GlobalExp.GlobalGoodRows
import all RBM8D.TExp.Closure
import all RBM8D.TExp.Second

@[expose] public section

/-!
# [II, (6.8)–(6.9)]: the run of the selector as a function, and the comparison of runs

* `RunCompare.run 𝔈 n D 𝒯`: the output graphs of the run of [II, Strategy 6.6] driven by the
  selector `TerminationC_sel` from the graphs of `A` and `Q` of the second order `T`-expansion,
  with the cutoff order `n`, the error order `D`, the `T`-expansion `𝒯` of order `n - 1`
  substituted in Steps 2–3 and the family `𝔈` of `Q`-expansions of [II, Lemma 4.15] used in
  Step 3; `RunCompare.run_spec` (it is the run of `TerminationC_sel`, a run of [II, Strategy 6.6],
  and its output graphs carry the clauses of [II, Lemma 6.8]).
* `RunCompare.runCompare`: (6.9) — at cutoff orders `n, n' ≥ m ≥ 3` and one error order `D > m`,
  for `T`-expansions with `TRec.Coherent (m - 1)`, `TRec.CoherentPM m` and graphs of `A` of order
  `≥ m`, the output graphs of every order `k ≤ m` agree up to order, and those with `⊕`, `⊖` in one
  dotted block of every order `k ≤ m + 1`; and the error order — at error orders `n < D ≤ D'`, for
  `T`-expansions with `TRec.AgreeTo D`, the output graphs of every order `k ≤ D` agree up to order.

The two runs are compared graph by graph. Along a run the order in the count of [II, (2.5)] does
not decrease, and a step that brings `⊕`, `⊖` into one dotted block raises it (Step 1 by
`TerminationB_loc_pm`, Step 3 by clause (F4) of `QExpFamilyStmt`, Steps 2–3 give graphs without
dotted edges); so a graph of order `≥ θ + 1`, and `≥ θ + 2` if `⊕`, `⊖` lie in one block, has only
output graphs of that kind. At a common graph of lower order both runs output it or both take the
same step, and the graphs of the step agree below that order: the substitution of Steps 2–3 by the
hypotheses on `𝒯`, `𝒯'` (an `O_dot` form of `H.glue x y₁ y₂ g` has scaling order
`ord G - 2 + ord g`, minus `2` when `y₁ = y₂` and `⊕`, `⊖` lie in one block of `g`, where
`G = H.glue x y₁ y₂ (tVar true)`), and the `Q`-expansion of Step 3 at two error orders by clause
(F3) of `QExpFamilyStmt`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

set_option quotPrecheck false in
local notation "QFam" => ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀
set_option quotPrecheck false in
local notation "Sel" => (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1

/-! ## Runs of single graphs -/

section Runs

variable {n D : ℕ} {𝒯 : TRec} {𝔈 : QFam} {ℓ : Sel}

/-- A run from concatenated inputs is the concatenation of the runs from the two parts. -/
private theorem RunCompare_split {E₁ E₂ F : Expansion 3}
    (h : SelRunB n D 𝒯 𝔈 ℓ (E₁ ++ E₂) F) :
    ∃ F₁ F₂, F = F₁ ++ F₂ ∧ SelRunB n D 𝒯 𝔈 ℓ E₁ F₁ ∧ SelRunB n D 𝒯 𝔈 ℓ E₂ F₂ := by
  generalize hE : E₁ ++ E₂ = E at h
  induction h generalizing E₁ with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hE
    exact ⟨[], [], rfl, SelRunB.nil, SelRunB.nil⟩
  | @out g E F hO hr ih =>
    rcases E₁ with _ | ⟨g', E₁⟩
    · simp only [List.nil_append] at hE
      subst hE
      exact ⟨[], g :: F, rfl, SelRunB.nil, SelRunB.out hO hr⟩
    · simp only [List.cons_append, List.cons.injEq] at hE
      obtain ⟨rfl, hE⟩ := hE
      obtain ⟨F₁, F₂, rfl, h₁, h₂⟩ := ih hE
      exact ⟨g' :: F₁, F₂, rfl, SelRunB.out hO h₁, h₂⟩
  | @step g E F hO hs hr ih =>
    rcases E₁ with _ | ⟨g', E₁⟩
    · simp only [List.nil_append] at hE
      subst hE
      exact ⟨[], F, rfl, SelRunB.nil, SelRunB.step hO hs hr⟩
    · simp only [List.cons_append, List.cons.injEq] at hE
      obtain ⟨rfl, hE⟩ := hE
      obtain ⟨F₁, F₂, rfl, h₁, h₂⟩ :=
        ih (E₁ := TerminationC_stepOut n D 𝒯 𝔈 g' (ℓ g') ++ E₁) (by rw [List.append_assoc, hE])
      exact ⟨F₁, F₂, rfl, SelRunB.step hO hs h₁, h₂⟩

open Classical in
/-- The outputs of the run from one graph (`[]` if there is no such run). -/
private def RunCompare_o (n D : ℕ) (𝒯 : TRec) (𝔈 : QFam) (ℓ : Sel)
    (g : Σ n₀ : ℕ, Graph 3 n₀) : Expansion 3 :=
  if h : ∃ F, SelRunB n D 𝒯 𝔈 ℓ [g] F then h.choose else []

private theorem RunCompare_o_spec {g : Σ n₀ : ℕ, Graph 3 n₀} {F : Expansion 3}
    (h : SelRunB n D 𝒯 𝔈 ℓ [g] F) : RunCompare_o n D 𝒯 𝔈 ℓ g = F := by
  have he : ∃ F, SelRunB n D 𝒯 𝔈 ℓ [g] F := ⟨F, h⟩
  unfold RunCompare_o
  simp only [he, dite_true]
  exact SelRunB.functional he.choose_spec h

/-- A run is the concatenation of the runs of its single input graphs. -/
private theorem RunCompare_flat : ∀ {E F : Expansion 3}, SelRunB n D 𝒯 𝔈 ℓ E F →
    F = E.flatMap (RunCompare_o n D 𝒯 𝔈 ℓ) ∧
      ∀ g ∈ E, SelRunB n D 𝒯 𝔈 ℓ [g] (RunCompare_o n D 𝒯 𝔈 ℓ g)
  | [], F, h => by
    cases h
    exact ⟨rfl, by simp⟩
  | g :: E, F, h => by
    obtain ⟨F₁, F₂, rfl, h₁, h₂⟩ := RunCompare_split (E₁ := [g]) h
    obtain ⟨e, hE⟩ := RunCompare_flat h₂
    refine ⟨by rw [List.flatMap_cons, RunCompare_o_spec h₁, e], ?_⟩
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · rw [RunCompare_o_spec h₁]
      exact h₁
    · exact hE g' hg'

private theorem RunCompare_single_out {g : Σ n₀ : ℕ, Graph 3 n₀} {F : Expansion 3}
    (h : SelRunB n D 𝒯 𝔈 ℓ [g] F) (hO : TerminationC_Out n D g) : F = [g] := by
  cases h with
  | out _ hr =>
    cases hr
    rfl
  | step hO' _ _ => exact absurd hO hO'

private theorem RunCompare_single_step {g : Σ n₀ : ℕ, Graph 3 n₀} {F : Expansion 3}
    (h : SelRunB n D 𝒯 𝔈 ℓ [g] F) (hO : ¬ TerminationC_Out n D g) :
    SelRunB n D 𝒯 𝔈 ℓ (TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g)) F := by
  cases h with
  | out hO' _ => exact absurd hO' hO
  | step _ _ hr => simpa using hr

/-- `s` is a graph of the step at `g` in the run. -/
private def RunCompare_Child (n D : ℕ) (𝒯 : TRec) (𝔈 : QFam) (ℓ : Sel)
    (s g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  ¬ TerminationC_Out n D g ∧ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g)

/-- The graphs of the inputs of a run are accessible for the relation `RunCompare_Child`. -/
private theorem RunCompare_acc {E F : Expansion 3} (h : SelRunB n D 𝒯 𝔈 ℓ E F) :
    ∀ g ∈ E, Acc (RunCompare_Child n D 𝒯 𝔈 ℓ) g := by
  induction h with
  | nil => intro g hg; simp at hg
  | out hO _ ih =>
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact Acc.intro _ fun s hs => absurd hO hs.1
    · exact ih g' hg'
  | step hO _ _ ih =>
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact Acc.intro _ fun s hs => ih s (List.mem_append_left _ hs.2)
    · exact ih g' (List.mem_append_right _ hg')

/-- A property `Hi` that passes from a graph of a run to the graphs of its step passes from the
inputs to the outputs. -/
private theorem RunCompare_high {I Hi : (Σ n₀ : ℕ, Graph 3 n₀) → Prop}
    (hI : ∀ g, I g → ¬ TerminationC_Out n D g →
      ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g), I s)
    (hH : ∀ g, I g → Hi g → ¬ TerminationC_Out n D g →
      ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g), Hi s)
    {E F : Expansion 3} (h : SelRunB n D 𝒯 𝔈 ℓ E F) (hE : ∀ g ∈ E, I g ∧ Hi g) :
    ∀ g ∈ F, Hi g := by
  induction h with
  | nil => intro g hg; simp at hg
  | out hO _ ih =>
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact (hE _ List.mem_cons_self).2
    · exact ih (fun g'' h'' => hE g'' (List.mem_cons_of_mem _ h'')) g' hg'
  | @step g E F hO _ _ ih =>
    refine ih fun g' hg' => ?_
    rcases List.mem_append.1 hg' with hg' | hg'
    · obtain ⟨h1, h2⟩ := hE g List.mem_cons_self
      exact ⟨hI g h1 hO g' hg', hH g h1 h2 hO g' hg'⟩
    · exact hE g' (List.mem_cons_of_mem _ hg')

end Runs

/-! ## Comparison of two runs -/

section Sim

private theorem RunCompare_flatMap_filter {α β : Type*} (q : α → Bool) (f : α → List β) :
    ∀ E : List α, (∀ a ∈ E, q a = false → f a = []) → E.flatMap f = (E.filter q).flatMap f
  | [], _ => rfl
  | a :: E, h => by
    have ih := RunCompare_flatMap_filter q f E fun b hb => h b (List.mem_cons_of_mem _ hb)
    by_cases hq : q a = true
    · simp [hq, ih]
    · have : f a = [] := h a List.mem_cons_self (by simpa using hq)
      simp [hq, this, ih]

open Classical in
/-- **Two runs with the same selector agree on the graphs without `Hi`** when they agree at every
common graph without `Hi` (the same outputs, and the graphs without `Hi` of their steps agree up
to order) and `Hi` passes from a graph of each run to the graphs of its step. -/
private theorem RunCompare_sim {n₁ D₁ n₂ D₂ : ℕ} {𝒯₁ 𝒯₂ : TRec} {𝔈 : QFam} {ℓ : Sel}
    {I₁ I₂ Hi : (Σ n₀ : ℕ, Graph 3 n₀) → Prop}
    (hI₁ : ∀ g, I₁ g → ¬ TerminationC_Out n₁ D₁ g →
      ∀ s ∈ TerminationC_stepOut n₁ D₁ 𝒯₁ 𝔈 g (ℓ g), I₁ s)
    (hI₂ : ∀ g, I₂ g → ¬ TerminationC_Out n₂ D₂ g →
      ∀ s ∈ TerminationC_stepOut n₂ D₂ 𝒯₂ 𝔈 g (ℓ g), I₂ s)
    (hH₁ : ∀ g, I₁ g → Hi g → ¬ TerminationC_Out n₁ D₁ g →
      ∀ s ∈ TerminationC_stepOut n₁ D₁ 𝒯₁ 𝔈 g (ℓ g), Hi s)
    (hH₂ : ∀ g, I₂ g → Hi g → ¬ TerminationC_Out n₂ D₂ g →
      ∀ s ∈ TerminationC_stepOut n₂ D₂ 𝒯₂ 𝔈 g (ℓ g), Hi s)
    (hO : ∀ g, I₁ g → I₂ g → ¬ Hi g →
      (TerminationC_Out n₁ D₁ g ↔ TerminationC_Out n₂ D₂ g))
    (hS : ∀ g, I₁ g → I₂ g → ¬ Hi g → ¬ TerminationC_Out n₁ D₁ g →
      ¬ TerminationC_Out n₂ D₂ g →
      ((TerminationC_stepOut n₁ D₁ 𝒯₁ 𝔈 g (ℓ g)).filter fun s => decide (¬ Hi s)).Perm
        ((TerminationC_stepOut n₂ D₂ 𝒯₂ 𝔈 g (ℓ g)).filter fun s => decide (¬ Hi s)))
    {E₁ E₂ F₁ F₂ : Expansion 3} (h₁ : SelRunB n₁ D₁ 𝒯₁ 𝔈 ℓ E₁ F₁)
    (h₂ : SelRunB n₂ D₂ 𝒯₂ 𝔈 ℓ E₂ F₂) (hE₁ : ∀ g ∈ E₁, I₁ g) (hE₂ : ∀ g ∈ E₂, I₂ g)
    (hE : (E₁.filter fun s => decide (¬ Hi s)).Perm (E₂.filter fun s => decide (¬ Hi s))) :
    (F₁.filter fun s => decide (¬ Hi s)).Perm (F₂.filter fun s => decide (¬ Hi s)) := by
  set q : (Σ n₀ : ℕ, Graph 3 n₀) → Bool := fun s => decide (¬ Hi s) with hq
  set o₁ := RunCompare_o n₁ D₁ 𝒯₁ 𝔈 ℓ with ho₁
  set o₂ := RunCompare_o n₂ D₂ 𝒯₂ 𝔈 ℓ with ho₂
  -- the outputs of a graph with `Hi` all have `Hi`
  have high₁ : ∀ g, I₁ g → Hi g → SelRunB n₁ D₁ 𝒯₁ 𝔈 ℓ [g] (o₁ g) → (o₁ g).filter q = [] := by
    intro g hg hh hr
    refine List.filter_eq_nil_iff.2 fun s hs => ?_
    have := RunCompare_high hI₁ hH₁ hr (by simpa using ⟨hg, hh⟩) s hs
    simpa [hq] using this
  have high₂ : ∀ g, I₂ g → Hi g → SelRunB n₂ D₂ 𝒯₂ 𝔈 ℓ [g] (o₂ g) → (o₂ g).filter q = [] := by
    intro g hg hh hr
    refine List.filter_eq_nil_iff.2 fun s hs => ?_
    have := RunCompare_high hI₂ hH₂ hr (by simpa using ⟨hg, hh⟩) s hs
    simpa [hq] using this
  -- the filtered outputs of a list
  have list₁ : ∀ {E F}, SelRunB n₁ D₁ 𝒯₁ 𝔈 ℓ E F → (∀ g ∈ E, I₁ g) →
      F.filter q = (E.filter q).flatMap fun g => (o₁ g).filter q := by
    intro E F h hE
    obtain ⟨rfl, hs⟩ := RunCompare_flat h
    rw [List.filter_flatMap]
    refine RunCompare_flatMap_filter q _ E fun g hg hqg => high₁ g (hE g hg) ?_ (hs g hg)
    simpa [hq] using hqg
  have list₂ : ∀ {E F}, SelRunB n₂ D₂ 𝒯₂ 𝔈 ℓ E F → (∀ g ∈ E, I₂ g) →
      F.filter q = (E.filter q).flatMap fun g => (o₂ g).filter q := by
    intro E F h hE
    obtain ⟨rfl, hs⟩ := RunCompare_flat h
    rw [List.filter_flatMap]
    refine RunCompare_flatMap_filter q _ E fun g hg hqg => high₂ g (hE g hg) ?_ (hs g hg)
    simpa [hq] using hqg
  -- one graph without `Hi`
  have node : ∀ g, Acc (RunCompare_Child n₁ D₁ 𝒯₁ 𝔈 ℓ) g → I₁ g → I₂ g →
      SelRunB n₁ D₁ 𝒯₁ 𝔈 ℓ [g] (o₁ g) → SelRunB n₂ D₂ 𝒯₂ 𝔈 ℓ [g] (o₂ g) → ¬ Hi g →
      ((o₁ g).filter q).Perm ((o₂ g).filter q) := by
    intro g hacc
    induction hacc with
    | intro g _ ih =>
      intro hg₁ hg₂ hr₁ hr₂ hh
      by_cases hO₁ : TerminationC_Out n₁ D₁ g
      · have hO₂ := (hO g hg₁ hg₂ hh).1 hO₁
        rw [RunCompare_single_out hr₁ hO₁, RunCompare_single_out hr₂ hO₂]
      · have hO₂ : ¬ TerminationC_Out n₂ D₂ g := fun h => hO₁ ((hO g hg₁ hg₂ hh).2 h)
        have hs₁ := RunCompare_single_step hr₁ hO₁
        have hs₂ := RunCompare_single_step hr₂ hO₂
        have hc₁ := hI₁ g hg₁ hO₁
        have hc₂ := hI₂ g hg₂ hO₂
        rw [list₁ hs₁ hc₁, list₂ hs₂ hc₂]
        have hP := hS g hg₁ hg₂ hh hO₁ hO₂
        refine (hP.flatMap_right _).trans (List.Perm.flatMap_left _ fun s hs => ?_)
        have hs' : s ∈ (TerminationC_stepOut n₁ D₁ 𝒯₁ 𝔈 g (ℓ g)).filter q := hP.symm.subset hs
        obtain ⟨hsm₁, hsq⟩ := List.mem_filter.1 hs'
        have hsm₂ := (List.mem_filter.1 hs).1
        refine ih s ⟨hO₁, hsm₁⟩ (hc₁ s hsm₁) (hc₂ s hsm₂) ((RunCompare_flat hs₁).2 s hsm₁)
          ((RunCompare_flat hs₂).2 s hsm₂) ?_
        simpa [hq] using hsq
  rw [list₁ h₁ hE₁, list₂ h₂ hE₂]
  have hacc := RunCompare_acc h₁
  refine (hE.flatMap_right _).trans (List.Perm.flatMap_left _ fun g hg => ?_)
  have hg' : g ∈ E₁.filter q := hE.symm.subset hg
  obtain ⟨hgm₁, hgq⟩ := List.mem_filter.1 hg'
  have hgm₂ := (List.mem_filter.1 hg).1
  refine node g (hacc g hgm₁) (hE₁ g hgm₁) (hE₂ g hgm₂) ((RunCompare_flat h₁).2 g hgm₁)
    ((RunCompare_flat h₂).2 g hgm₂) ?_
  simpa [hq] using hgq

end Sim


/-! ## Graphs of high order and the steps of the run -/

section High

open private oDotT_normal_self from RBM8D.Graph.Local.EdgeOrder
open private DotNorm.step DotNorm.Keep DotNorm.Keep.normal DotNorm.Keep.block
  from RBM8D.Graph.Local.DotNorm
open private RunClauses_Iso RunClauses_reorder_iso RunClauses_iso_paperOrd
  from RBM8D.GlobalExp.RunClauses
open private TerminationB_iso_pm TerminationB_paperOrd_of_dotFree TerminationB_dotFree_pm
  from RBM8D.GlobalExp.TerminationB
open private Termination_inv1 Termination_not_qGraph from RBM8D.GlobalExp.Termination
open private TerminationC2_XSw TerminationC2_normal_of TerminationC2_dotExcess_of
  TerminationC2_filter_eraseIdx TerminationC2_mem_eraseIdx TerminationC2_host_normal
  TerminationC2_host_lf from RBM8D.GlobalExp.TerminationC2
open private SubstSPD_swap_otimesNoDot SubstSPD_swap_dotExcess SubstSPD_swap_labels
  SubstSPD_swap_noLabDot SubstSPD_swap_pmBlock SubstSPD_tVar_ord from RBM8D.GlobalExp.SubstSPD
open private SubstDC_swap_rgCheck from RBM8D.GlobalExp.SubstDC

variable {n₀ : ℕ}

/-- Order `≥ θ + 1` in the count of [II, (2.5)], and `≥ θ + 2` if `b` and `⊕`, `⊖` lie in one
dotted block. -/
private def RunCompare_HiN (b : Bool) (θ : ℤ) {n₀ : ℕ} (Γ : Graph 3 n₀) : Prop :=
  θ + 1 ≤ Γ.paperOrd ∧ (b = true → Γ.PMBlock → θ + 2 ≤ Γ.paperOrd)

/-- Every `O_dot` form of the graph is normal regular with `RunCompare_HiN b θ`. -/
private def RunCompare_Hi (b : Bool) (θ : ℤ) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  ∀ t ∈ oDotT g.2, (∃ C, t.g.Normal C) ∧ RunCompare_HiN b θ t.g

private theorem RunCompare_hi_normal {b : Bool} {θ : ℤ} {g : Σ n₀ : ℕ, Graph 3 n₀} {C : ℕ}
    (hN : g.2.Normal C) : RunCompare_Hi b θ g ↔ RunCompare_HiN b θ g.2 := by
  unfold RunCompare_Hi
  rw [oDotT_normal_self hN]
  constructor
  · intro h
    exact (h _ (List.mem_singleton_self _)).2
  · intro h t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨⟨C, hN⟩, h⟩

/-- A normal regular graph of order at least that of `Γ`, and higher by `1` if it has `⊕`, `⊖` in
one block and `Γ` does not, keeps `RunCompare_HiN`. -/
private theorem RunCompare_hi_of {b : Bool} {θ : ℤ} {n₁ : ℕ} {Γ : Graph 3 n₀} {Γ' : Graph 3 n₁}
    {C : ℕ} (hN : Γ'.Normal C) (h : RunCompare_HiN b θ Γ) (h1 : Γ.paperOrd ≤ Γ'.paperOrd)
    (h2 : Γ'.PMBlock → ¬ Γ.PMBlock → Γ.paperOrd + 1 ≤ Γ'.paperOrd) :
    RunCompare_Hi b θ ⟨n₁, Γ'⟩ := by
  rw [RunCompare_hi_normal (g := ⟨n₁, Γ'⟩) hN]
  dsimp only
  refine ⟨h.1.trans h1, fun hb hp => ?_⟩
  by_cases hp0 : Γ.PMBlock
  · exact (h.2 hb hp0).trans h1
  · have := h2 hp hp0
    have := h.1
    omega

/-- Graphs with the same dotted edges have the same blocks. -/
private theorem RunCompare_dotGraph {Γ Γ' : Graph 3 n₀}
    (h : Γ'.comps.filter (fun c => decide (c.kind = .dot)) =
      Γ.comps.filter (fun c => decide (c.kind = .dot))) :
    Γ'.paperOrd - Γ'.ord = Γ.paperOrd - Γ.ord ∧ (Γ'.PMBlock ↔ Γ.PMBlock) := by
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
  refine ⟨?_, ?_⟩
  · unfold Graph.paperOrd
    rw [TerminationC2_dotExcess_of h]
    ring
  · rw [Graph.pmBlock_iff_sameBlock, Graph.pmBlock_iff_sameBlock]
    unfold Graph.SameBlock
    rw [hg]

/-- The order of a graph with one more `×`-dotted edge. -/
private theorem RunCompare_ord_xdot (cs : List (Comp (Atom 3 n₀))) (c : Comp (Atom 3 n₀))
    (co : Coeff) (hk : c.kind = .xdot) :
    (⟨cs ++ [c], co⟩ : Graph 3 n₀).ord = (⟨cs, co⟩ : Graph 3 n₀).ord := by
  simp [Graph.ord, hk, Kind.ord]

/-- The order of a graph with a `×`-dotted edge removed. -/
private theorem RunCompare_ord_erase (cs : List (Comp (Atom 3 n₀))) (co : Coeff) {j : ℕ}
    (hj : j < cs.length) (hk : cs[j].kind = .xdot) :
    (⟨cs.eraseIdx j, co⟩ : Graph 3 n₀).ord = (⟨cs, co⟩ : Graph 3 n₀).ord := by
  have h1 : cs = cs.take j ++ cs[j] :: cs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  rw [List.eraseIdx_eq_take_drop_succ]
  generalize cs.take j = A at h1 ⊢
  generalize cs.drop (j + 1) = B at h1 ⊢
  generalize cs[j] = c at h1 hk
  subst h1
  simp [Graph.ord, hk, Kind.ord]

/-! ### The clauses of `TRec.Def63` read by the substitution -/

private theorem RunCompare_def63_R {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.R, gsPM' g.2 ∧ g.2.ExtClause ∧ g.2.ColourInvB := h.1.1

private theorem RunCompare_def63_A {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.A, spdPM' g.2 ∧ ((g.1 = 0 ∧ g.2.RootAtPlus) ∨ g.2.ExtClause ∧ g.2.ColourInvB) :=
  h.1.2.1

private theorem RunCompare_def63_Q {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.Q, spdPM' g.2 ∧ g.2.QLabelInMISB ∧
      ((g.1 = 0 ∧ g.2.RootAtPlus) ∨ g.2.ExtClause ∧ g.2.ColourInvB) := h.1.2.2

private theorem RunCompare_def63_leaf {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, g.2.TensorDiffusive ∧ g.2.dotExcess = 0 ∧
      g.2.NoLabDot ∧ g.2.labels.length ≤ 1 := h.2.1

private theorem RunCompare_def63_pmRA {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.R ++ 𝒯.A, g.2.PMBlock → 5 ≤ g.2.ord := h.2.2.2.1

private theorem RunCompare_def63_pmQ {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.Q, g.2.PMBlock → 4 ≤ g.2.ord := h.2.2.2.2.1

private theorem RunCompare_def63_rg {𝒯 : TRec} (h : 𝒯.Def63) :
    ∀ g ∈ 𝒯.Q ++ 𝒯.Err, g.2.RgCheck := h.2.2.2.2.2.1

/-- **The `O_dot` forms of a substituted graph of `R`, `A`, `Q`, `Err`** ([II, Lemma 6.5],
[II, (2.5)]): normal regular without dotted edges, of scaling order `ord G - 2 + ord g`, minus `2`
when `y₁ = y₂` and `⊕`, `⊖` lie in one block of `g`, where `G = H.glue x y₁ y₂ (tVar true)`. -/
private theorem RunCompare_piece_T {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {m C : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}
    (hL : H.LabelFree) (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hd : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err)
    {t : Tracked 3 (m + g.1)} (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) :
    (∃ C', t.g.Normal C') ∧ t.g.DotFree ∧
      (y₁ = y₂ ∧ g.2.PMBlock → t.g.ord + 2 = (H.glue x y₁ y₂ (tVar true)).ord - 2 + g.2.ord) ∧
      (¬ (y₁ = y₂ ∧ g.2.PMBlock) → t.g.ord = (H.glue x y₁ y₂ (tVar true)).ord - 2 + g.2.ord) := by
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hSh := hT.2.2.2.1
  have hDef := hT.2.2.2.2
  obtain ⟨hTD, hX, hNL, hlab⟩ := RunCompare_def63_leaf hDef g hg
  have hgN : ∃ C', g.2.Normal C' := by
    rcases List.mem_append.1 hg with h | h
    · exact (hSh.1.1 g h).1
    · exact (hSh.1.2 g h).1
  obtain ⟨C', hgN⟩ := hgN
  have hRg : g.2.RgCheck := by
    simp only [List.mem_append] at hg
    rcases hg with ((hg | hg) | hg) | hg
    · exact TerminationB_rgCheck g.2 fun _ => ⟨(RunCompare_def63_R hDef g hg).2.1, hTD⟩
    · by_cases h0 : g.1 = 0
      · exact Or.inl h0
      · rcases (RunCompare_def63_A hDef g hg).2 with ⟨h0', -⟩ | ⟨hE, -⟩
        · exact absurd h0' h0
        · exact TerminationB_rgCheck g.2 fun _ => ⟨hE, hTD⟩
    · exact RunCompare_def63_rg hDef g (List.mem_append_left _ hg)
    · exact RunCompare_def63_rg hDef g (List.mem_append_right _ hg)
  obtain ⟨hNt, hd', hε, hε', -⟩ := glue_oDotT_normal m g.1 C C' H x y₁ y₂ g.2.swapSolid hx hy₁
    hy₂ hL hN hd (Graph.swapSolid_Normal hgN) (SubstSPD_swap_otimesNoDot hTD)
    (by rw [SubstSPD_swap_dotExcess]; exact hX) (SubstDC_swap_rgCheck hRg)
    (by rw [SubstSPD_swap_labels]; exact hlab) (SubstSPD_swap_noLabDot hNL) t ht
  have e1 := glue_ord 3 m g.1 H x y₁ y₂ g.2.swapSolid
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  have e3 : g.2.swapSolid.ord = g.2.ord := (swapSolid_basic 3 g.1 g.2).2.1
  rw [SubstSPD_tVar_ord] at e2
  refine ⟨hNt, hd', fun h => ?_, fun h => ?_⟩
  · have := hε ⟨h.1, (SubstSPD_swap_pmBlock g.2).2 h.2⟩
    omega
  · have := hε' fun h' => h ⟨h'.1, (SubstSPD_swap_pmBlock g.2).1 h'.2⟩
    omega

/-- The graphs of the right side of [II, (4.15)] in `R`, `A`, `Q`, `Err` have scaling order
`≥ 2`, and `≥ 4` with `⊕`, `⊖` in one block. -/
private theorem RunCompare_T_ord {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hg : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err) : 2 ≤ g.2.ord ∧ (g.2.PMBlock → 4 ≤ g.2.ord) := by
  have hSh := hT.2.2.2.1
  have hDef := hT.2.2.2.2
  have hnD := hT.1
  simp only [List.mem_append] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · have := (hSh.2.1 g hg).2.2.1
    exact ⟨by omega, fun hp => by
      have := RunCompare_def63_pmRA hDef g (List.mem_append_left _ hg) hp; omega⟩
  · have := (hSh.2.2.1 g hg).2
    have : (2 : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by omega
    exact ⟨by omega, fun hp => by
      have := RunCompare_def63_pmRA hDef g (List.mem_append_right _ hg) hp; omega⟩
  · have := (hSh.2.2.2.1 g hg).2
    exact ⟨this, RunCompare_def63_pmQ hDef g hg⟩
  · have := hSh.2.2.2.2 g hg
    have : (3 : ℤ) ≤ (D : ℤ) := by omega
    exact ⟨by omega, fun _ => by omega⟩

/-- **The steps of Steps 2–3 do not lower the order** ([II, Lemma 6.5]): every `O_dot` form of
every substituted graph is normal regular without dotted edges, of scaling order at least that
of the host `G = H.glue x y₁ y₂ (tVar true)`. -/
private theorem RunCompare_subst_ge {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {m : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}
    (hR : TerminationC_RI n D ⟨m + 1, H.glue x y₁ y₂ (tVar true)⟩)
    (hD : ¬ (D : ℤ) < (H.glue x y₁ y₂ (tVar true)).ord)
    (ho2 : (H.glue x y₁ y₂ (tVar true)).ord ≤ n) (hP : TerminationC_HostPrem H x y₁ y₂)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.tSubst (n - 1))
    {t : Tracked 3 (m + g.1)} (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) :
    (∃ C', t.g.Normal C') ∧ t.g.DotFree ∧ (H.glue x y₁ y₂ (tVar true)).ord ≤ t.g.ord := by
  have hP' := hP
  obtain ⟨ho1, ⟨C, hN⟩, hd, hL, hgs, hnr, hTD, hM, hst⟩ := hP'
  have hLF := TerminationC2_host_lf ⟨m, H, x, y₁, y₂, rfl, hP⟩
  obtain ⟨hB, -⟩ := Termination_inv1 hR.1 (fun h => Termination_not_qGraph hLF h.2) hD
  have hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63 :=
    ⟨hT.1, hT.2.2.2.1, hT.2.2.2.2⟩
  have hrow1 : g ∈ leadExp ++ sigmaTExp (n - 1) ++ tVarCorr → (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ (H.glue x y₁ y₂ (tVar true)).ord ≤ t.g.ord := by
    intro h1
    obtain ⟨h1, h2, -, -, h5⟩ := globalGood_row1 n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho1 ho2
      hB hTD hgs hnr hM hst g h1 t ht
    refine ⟨h1, h2, ?_⟩
    rcases h5 with h5 | ⟨-, h5, -⟩ <;> omega
  have hrowT : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err → (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ (H.glue x y₁ y₂ (tVar true)).ord ≤ t.g.ord := by
    intro h1
    obtain ⟨h1', h2, h3, h4⟩ := RunCompare_piece_T hT hL hN hd hst h1 ht
    obtain ⟨o1, o2⟩ := RunCompare_T_ord hn hT h1
    refine ⟨h1', h2, ?_⟩
    by_cases hε : y₁ = y₂ ∧ g.2.PMBlock
    · have := h3 hε
      have := o2 hε.2
      omega
    · have := h4 hε
      omega
  simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg
  rcases hg with (((((hg | hg) | hg) | hg) | hg) | hg) | hg
  · exact hrow1 (by simp [hg])
  · exact hrow1 (by simp [hg])
  · exact hrowT (by simp [hg])
  · exact hrowT (by simp [hg])
  · exact hrowT (by simp [hg])
  · exact hrowT (by simp [hg])
  · exact hrow1 (by simp [hg])

/-- At a graph that is not normal regular the selector gives the empty sum at a `×`-dotted loop
or `O_dot`. -/
private theorem RunCompare_sel_raw {g : Σ n₀ : ℕ, Graph 3 n₀} (hN : ¬ ∃ C, g.2.Normal C) :
    (∃ i, TerminationC_sel g = .xdotLoop i) ∨ TerminationC_sel g = .dot := by
  unfold TerminationC_sel
  by_cases h₁ : ∃ i : Fin g.2.comps.length, g.2.comps[i].kind = .xdot ∧
      g.2.comps[i].x = g.2.comps[i].y
  · exact Or.inl ⟨_, dite_eq_left_of_eq_true (eq_true h₁)⟩
  · rw [dite_eq_right_of_eq_false (eq_false h₁), ite_eq_left_of_eq_true _ _ (eq_true hN)]
    exact Or.inr rfl

/-- **`RunCompare_Hi` passes along the step of the selector at a graph that is not normal
regular**: its graphs are its `O_dot` forms. -/
private theorem RunCompare_mon_raw {n D : ℕ} {𝒯 : TRec} {𝔈 : QFam} {b : Bool} {θ : ℤ}
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hN : ¬ ∃ C, g.2.Normal C) (hh : RunCompare_Hi b θ g) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (TerminationC_sel g), RunCompare_Hi b θ s := by
  intro s hs
  rcases RunCompare_sel_raw hN with ⟨i, hi⟩ | hi
  · rw [hi] at hs
    exact absurd hs List.not_mem_nil
  · rw [hi] at hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    obtain ⟨⟨C, hC⟩, h2⟩ := hh t ht
    exact (RunCompare_hi_normal (g := ⟨t.nOut, t.g⟩) hC).2 h2

/-- **`RunCompare_Hi` passes along every admissible step at a normal regular graph with the
invariant of a run** ([II, Strategy 6.6]; the order in the count of [II, (2.5)] does not decrease
along a step, and a step that brings `⊕`, `⊖` into one block raises it): Step 1
(`TerminationB_inv_loc`, `TerminationB_loc_pm`), the removal of a redundant dotted edge, a
reordering, the steps on `×`-dotted edges and on the coefficient, Steps 2–3 (the `O_dot` forms of
the substituted graphs have no dotted edge and order at least that of the host) and Step 3
(`Tracked.QBase` and clause (F4) of `QExpFamilyStmt`). -/
private theorem RunCompare_mon {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} {𝔈 : QFam}
    (hF : QExpFamilyStmt 𝔈) (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {b : Bool}
    {θ : ℤ} {g : Σ n₀ : ℕ, Graph 3 n₀} (hR : TerminationC_RI n D g) {C : ℕ}
    (hN : g.2.Normal C) {l : TerminationC_Loc g.1} (hA : TerminationC_Adm n D 𝔈 g l)
    (hh : RunCompare_HiN b θ g.2) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, RunCompare_Hi b θ s := by
  intro s hs
  cases l with
  | loc o x =>
    obtain ⟨hS, hD, -, hL, hP, hgs, -, hside, hA', hX⟩ := hA
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    obtain ⟨⟨C', hN'⟩, -, hst, -⟩ :=
      TerminationB_inv_loc hR.1 hR.2.1 hS hD hN hL hP hgs hX hA' hside t ht
    refine RunCompare_hi_of hN' hh ?_ fun hp _ => ?_
    · rw [Graph.paperOrd_eq_obl, Graph.paperOrd_eq_obl]
      exact hst.2.1
    · have := (TerminationB_loc_pm hR.1 hR.2.1 hS hD hN hL hP hX hA' t ht hp).1
      omega
  | dot => exact absurd ⟨C, hN⟩ hA
  | dropDot Γ' =>
    obtain ⟨⟨i, c, hc, hk, hr, he⟩, -, hP⟩ := hA
    obtain ⟨he', hord, hK⟩ := DotNorm.step hN hP hc hk hr
    rw [List.mem_singleton.1 hs]
    subst he
    refine RunCompare_hi_of (DotNorm.Keep.normal hK) hh (le_of_eq ?_) fun hp hp0 => ?_
    · unfold Graph.paperOrd
      omega
    · rw [Graph.pmBlock_iff_sameBlock, DotNorm.Keep.block hK] at hp
      exact absurd ((Graph.pmBlock_iff_sameBlock g.2).2 hp) hp0
  | reorder Γ' =>
    obtain ⟨hRe, -, hH'⟩ := hA
    obtain ⟨C', hN'⟩ := TerminationC2_host_normal hH'
    obtain ⟨π, hiso⟩ := RunClauses_reorder_iso hRe
    rw [List.mem_singleton.1 hs]
    refine RunCompare_hi_of hN' hh (le_of_eq (RunClauses_iso_paperOrd hiso).symm)
      fun hp hp0 => absurd ((TerminationB_iso_pm hiso).1 hp) hp0
  | xdotDup i =>
    obtain ⟨hi, ⟨hk, -⟩, -⟩ := hA
    simp only [Fin.getElem_fin] at hk
    have e : (g.2.comps[i]?).toList = [g.2.comps[i]] := by
      rw [List.getElem?_eq_getElem hi]; rfl
    have hs' : s = ⟨g.1, ⟨g.2.comps ++ [g.2.comps[i]], g.2.coeff⟩⟩ := by
      rw [List.mem_singleton.1 hs]
      simp only [e]
    rw [hs']
    have hf : (⟨g.2.comps ++ [g.2.comps[i]], g.2.coeff⟩ : Graph 3 g.1).comps.filter
        (fun c => decide (c.kind = .dot)) =
          g.2.comps.filter (fun c => decide (c.kind = .dot)) := by
      simp [List.filter_append, hk]
    obtain ⟨h1, h2⟩ := RunCompare_dotGraph hf
    have ho : (⟨g.2.comps ++ [g.2.comps[i]], g.2.coeff⟩ : Graph 3 g.1).ord = g.2.ord :=
      RunCompare_ord_xdot g.2.comps _ g.2.coeff hk
    have hN' := TerminationC2_normal_of (Γ := g.2)
      (Γ' := ⟨g.2.comps ++ [g.2.comps[i]], g.2.coeff⟩)
      (fun c hc => by
        rcases List.mem_append.1 hc with hc | hc
        · exact ⟨c, hc, Or.inl rfl⟩
        · rw [List.mem_singleton.1 hc]; exact ⟨_, List.getElem_mem hi, Or.inl rfl⟩)
      (fun c hc => ⟨c, List.mem_append_left _ hc, Or.inl rfl⟩) hN
    exact RunCompare_hi_of hN' hh (le_of_eq (by omega)) fun hp hp0 => absurd (h2.1 hp) hp0
  | xdotDrop i j =>
    obtain ⟨hi, hj, ⟨hij, hc, hk, -⟩, -⟩ := hA
    simp only [Fin.getElem_fin] at hk hc
    have hkj : g.2.comps[j].kind = .xdot := by
      rcases hc with h | h <;> rw [h] <;> exact hk
    rw [List.mem_singleton.1 hs]
    have hf : (⟨g.2.comps.eraseIdx j, g.2.coeff⟩ : Graph 3 g.1).comps.filter
        (fun c => decide (c.kind = .dot)) =
          g.2.comps.filter (fun c => decide (c.kind = .dot)) :=
      TerminationC2_filter_eraseIdx _ g.2.comps hj (by simp [hkj])
    obtain ⟨h1, h2⟩ := RunCompare_dotGraph hf
    have ho : (⟨g.2.comps.eraseIdx j, g.2.coeff⟩ : Graph 3 g.1).ord = g.2.ord :=
      RunCompare_ord_erase g.2.comps g.2.coeff hj hkj
    have hij' : i ≠ j := fun h => hij (Fin.ext h)
    have hN' := TerminationC2_normal_of (Γ := g.2) (Γ' := ⟨g.2.comps.eraseIdx j, g.2.coeff⟩)
      (fun c hc => ⟨c, List.mem_of_mem_eraseIdx hc, Or.inl rfl⟩)
      (fun c hcm => by
        rcases TerminationC2_mem_eraseIdx hcm hj with h | rfl
        · exact ⟨c, h, Or.inl rfl⟩
        · refine ⟨g.2.comps[i], List.mem_eraseIdx_iff_getElem.2 ⟨i, hi, hij', rfl⟩, ?_⟩
          rcases hc with h | h
          · exact Or.inl h
          · exact Or.inr ⟨hk, h⟩) hN
    exact RunCompare_hi_of hN' hh (le_of_eq (by omega)) fun hp hp0 => absurd (h2.1 hp) hp0
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm =>
    rw [List.mem_singleton.1 hs]
    have hN' := TerminationC2_normal_of (Γ := g.2)
      (Γ' := ⟨g.2.comps, g.2.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩)
      (fun c hc => ⟨c, hc, Or.inl rfl⟩) (fun c hc => ⟨c, hc, Or.inl rfl⟩) hN
    exact RunCompare_hi_of hN' hh le_rfl fun hp hp0 => absurd hp hp0
  | subst m H x y₁ y₂ =>
    obtain ⟨he, hD, hn', hP⟩ := hA
    subst he
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hs
    obtain ⟨g'', hg'', rfl⟩ := List.mem_map.1 hg'
    intro t ht
    obtain ⟨hNt, hdt, hot⟩ := RunCompare_subst_ge hn hT hR hD hn' hP hg'' ht
    have hd := hP.2.2.1
    refine ⟨hNt, ?_, fun _ hp => absurd hp (TerminationB_dotFree_pm hdt).1⟩
    rw [TerminationB_paperOrd_of_dotFree hdt]
    have := hh.1
    rw [TerminationB_paperOrd_of_dotFree hd] at this
    omega
  | qexp x =>
    obtain ⟨-, hP, hD, hform, hQ, -, hq⟩ := hA
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    obtain ⟨C', hout⟩ := hq.1
    obtain ⟨⟨hNt, hord, -, hdex, -⟩, -⟩ := (hout t ht).1
    obtain ⟨hB, -⟩ := Termination_inv1 hR.1 (fun h => hQ h.2) hD
    refine RunCompare_hi_of hNt hh ?_ fun hp hp0 =>
      hF.2.2.2.1 D g.1 x g.2 ⟨C, hN⟩ hform hP hB hp0 t ht hp
    unfold Graph.paperOrd
    omega

end High


/-! ## The `O_dot` forms of the substituted graphs of `Σ_T` -/

section SigmaPiece

open private SubstSPD_b1 SubstSPD_Bal SubstSPD_Bal_H SubstSPD_Bal_normal SubstSPD_bb SubstSPD_bb_c2
  SubstSPD_bb_glue SubstSPD_bb_ord SubstSPD_edge_reach SubstSPD_H0 SubstSPD_lead_comps SubstSPD_lg
  SubstSPD_lg_ord_nil SubstSPD_lg_ord_x SubstSPD_lgx_c2 SubstSPD_liftA_inj SubstSPD_liftA_isRight
  SubstSPD_mergeT_a SubstSPD_mergeT_c SubstSPD_oDotT_b3_nil SubstSPD_oDotT_one SubstSPD_out_merge
  SubstSPD_out_self SubstSPD_reach_rel SubstSPD_rel_reach SubstSPD_sp_nil SubstSPD_sp_one
  SubstSPD_splitPairs_nil SubstSPD_theta_ne SubstSPD_theta_swap SubstSPD_tVar_ord SubstSPD_wtd_reach
  SubstSPD_Out SubstSPD_Out.normal SubstSPD_Out.dotFree SubstSPD_Out.ord_ge
  from RBM8D.GlobalExp.SubstSPD

/-- **The `O_dot` forms of a substituted graph of `Σ_T`** ([II, Lemma 6.5 (1)], [II, (2.5)]): for
the graph `m Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖}` substituted at a host `G = H.glue x y₁ y₂ (tVar true)` of
Steps 2–3, every `O_dot` form is normal regular without dotted edges, of scaling order at least
`ord H + ord Θ^{[o]}`. At `y₁ = y₂` the solid edge `Ḡ_{y y}` becomes a weight; otherwise the pair
`y₂ y₁` is kept (a `×`-dotted edge) or its ends are identified. -/
private theorem RunCompare_sigma_piece {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) {C : ℕ}
    (o : List ℕ) (hk : 2 * o.length ≤ o.sum)
    (hL : H.LabelFree) (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) :
    ∀ t ∈ oDotT (H.glue x y₁ y₂ (thetaLabelGraph o).swapSolid), (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ H.ord + ((o.sum : ℤ) + 2 - 2 * o.length) ≤ t.g.ord := by
  intro t ht
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  rw [SubstSPD_theta_swap] at ht
  obtain ⟨hHb, hHnd, hHl, hHsl⟩ := SubstSPD_H0 H x y₁ y₂ hN hD hL
  obtain ⟨hc0, hcx, hcd⟩ := SubstSPD_lead_comps H x y₁ y₂ o
  have hYc := SubstSPD_bb_glue H x y₁ y₂ o
  -- the scaling orders
  have e1 := glue_ord 3 m 0 H x y₁ y₂ (SubstSPD_lg o [] cm)
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  rw [SubstSPD_tVar_ord] at e2
  rw [SubstSPD_lg_ord_nil] at e1
  have e3 := glue_ord 3 m 0 H x y₁ y₂ (SubstSPD_bb o)
  rw [SubstSPD_bb_ord] at e3
  have e4 := glue_ord 3 m 0 H x y₁ y₂ (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm)
  rw [SubstSPD_lg_ord_x] at e4
  have hk' : (2 : ℤ) * o.length ≤ o.sum := by exact_mod_cast hk
  obtain ⟨bN, bO, bX, bR, bLab, bNL, bPM⟩ := SubstSPD_bb_c2 o
  have hC2Y := glue_oDotT_normal m 0 C 6 H x y₁ y₂ (SubstSPD_bb o) hx hy₁ hy₂ hL hN hD bN bO bX
    bR bLab bNL
  obtain ⟨sN, sO, sX, sR, sLab, sNL, sPM⟩ := SubstSPD_lgx_c2 o
  have hC2s := glue_oDotT_normal m 0 C 6 H x y₁ y₂ _ hx hy₁ hy₂ hL hN hD sN sO sX sR sLab sNL
  set Gt := H.glue x y₁ y₂ (SubstSPD_lg o [] cm) with hGt
  set Y := H.glue x y₁ y₂ (SubstSPD_bb o) with hY
  set Ys := H.glue x y₁ y₂ (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm) with hYs
  set Y₁ : Atom 3 (m + 0) := liftA 0 y₁ with hY₁
  set Y₂ : Atom 3 (m + 0) := liftA 0 y₂ with hY₂
  set X : Atom 3 (m + 0) := liftA 0 x with hX
  have hGtL : Gt.LabelFree := by
    intro c hc
    rw [hc0] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hHl c hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> rfl
  have hYL : Y.LabelFree := by
    intro c hc
    rw [hYc] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hHl c hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> rfl
  have hGtd : Gt.DotFree := by
    intro c hc
    rw [hc0] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hHnd c hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> simp [mkC]
  -- the graph `Y`: `O_dot` forms by `O_merge`
  have hspY : Y.splitPairs = [] := by
    refine SubstSPD_sp_nil (fun c hc hks hne => ?_) (fun c hc hkx hne => ?_)
    · rw [hYc] at hc ⊢
      rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨d, hd, h⟩ := hHb.1 c hc hks
        exact ⟨d, List.mem_append_left _ hd, h⟩
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [mkC, Kind.isSolid] at hks
    · rw [hYc] at hc ⊢
      rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨d, hd, h⟩ := hHb.2 c hc hkx hne
        exact ⟨d, List.mem_append_left _ hd, h⟩
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [mkC] at hkx
  have hbY : (Y.comps.any fun c => (c.kind == .dot && c.x.isRight && c.y.isRight) ||
      (c.kind.isSolid && c.x == c.y)) = true := by
    rw [List.any_eq_true]
    refine ⟨mkC .dot Y₂ Y₁, by rw [hYc]; simp, ?_⟩
    simp only [mkC, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inl ⟨SubstSPD_liftA_isRight hy₂, SubstSPD_liftA_isRight hy₁⟩
  by_cases hyy : y₁ = y₂
  · -- `y₁ = y₂`: the solid loop `Ḡ_{yy}` becomes a weight
    have hY12 : Y₂ = Y₁ := by rw [hY₁, hY₂, hyy]
    have hsp : Gt.splitPairs = [] := by
      refine SubstSPD_sp_nil (fun c hc hks hne => ?_) (fun c hc hkx hne => ?_)
      · rw [hc0] at hc ⊢
        rcases List.mem_append.1 hc with hc | hc
        · obtain ⟨d, hd, h⟩ := hHb.1 c hc hks
          exact ⟨d, List.mem_append_left _ hd, h⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl
          · simp [mkC, Kind.isSolid] at hks
          · exact absurd hY12 hne
      · rw [hc0] at hc ⊢
        rcases List.mem_append.1 hc with hc | hc
        · obtain ⟨d, hd, h⟩ := hHb.2 c hc hkx hne
          exact ⟨d, List.mem_append_left _ hd, h⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl <;> simp [mkC] at hkx
    have hb : (Gt.comps.any fun c => (c.kind == .dot && c.x.isRight && c.y.isRight) ||
        (c.kind.isSolid && c.x == c.y)) = true := by
      rw [List.any_eq_true]
      refine ⟨mkC (.G .minus) Y₂ Y₁, by rw [hc0]; simp, ?_⟩
      simp [mkC, Kind.isSolid, hY12]
    rw [SubstSPD_oDotT_b3_nil hGtL hsp hb] at ht
    rw [SubstSPD_mergeT_a H x y₁ y₂ hyy o] at ht
    have htY : t ∈ oDotT Y := (SubstSPD_oDotT_b3_nil hYL hspY hbY t).2 ht
    obtain ⟨hNt, hDt, hε, -, -⟩ := hC2Y t htY
    have hord := hε ⟨hyy, bPM⟩
    have q1 : t.g.ord + 2 = H.ord + ((o.sum : ℤ) + 2 - 2 * o.length + 2) := hord.trans e3
    exact ⟨hNt, hDt, by omega⟩
  · have hne12 : Y₁ ≠ Y₂ := fun h => hyy (SubstSPD_liftA_inj h)
    -- the graph `Ys` with the `×`-dotted edge `y₂ ≠ y₁`
    have hYsc : Ys.comps = Gt.comps ++ [mkC .xdot Y₂ Y₁] := hcx
    have hspYs : Ys.splitPairs = [] := by
      refine SubstSPD_sp_nil (fun c hc hks hne => ?_) (fun c hc hkx hne => ?_)
      · rw [hYsc, hc0] at hc ⊢
        rcases List.mem_append.1 hc with hc | hc
        · rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨d, hd, h⟩ := hHb.1 c hc hks
            exact ⟨d, by simp [hd], h⟩
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl
            · simp [mkC, Kind.isSolid] at hks
            · exact ⟨mkC .xdot Y₂ Y₁, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · simp only [List.mem_singleton] at hc
          subst hc; simp [mkC, Kind.isSolid] at hks
      · rw [hYsc, hc0] at hc ⊢
        rcases List.mem_append.1 hc with hc | hc
        · rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨d, hd, h⟩ := hHb.2 c hc hkx hne
            exact ⟨d, by simp [hd], h⟩
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl <;> simp [mkC] at hkx
        · simp only [List.mem_singleton] at hc
          subst hc
          exact ⟨mkC (.G .minus) Y₂ Y₁, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
    have hb2Ys : (Ys.splitPairs.isEmpty && !(Ys.comps.any fun c =>
        (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) =
        true := by
      rw [hspYs]
      simp only [List.isEmpty_nil, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.any_eq_false]
      intro c hc
      rw [hYsc, hc0] at hc
      rcases List.mem_append.1 hc with hc | hc
      · rcases List.mem_append.1 hc with hc | hc
        · have h1 := hHnd c hc
          have h2 := hHsl c hc
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and]
          refine ⟨fun h => absurd h.1 h1, fun hs h => h2 hs h⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl
          · simp [mkC, (SubstSPD_theta_ne o).2, Kind.isSolid]
          · simp [mkC, Kind.isSolid, Ne.symm hne12]
      · simp only [List.mem_singleton] at hc
        subst hc; simp [mkC, Kind.isSolid]
    have hYsL : Ys.LabelFree := by
      intro c hc
      rw [hYsc] at hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hGtL c hc
      · simp only [List.mem_singleton] at hc; subst hc; rfl
    have hNs : ∃ C'', Ys.Normal C'' := by
      have hself : Tracked.self Ys ∈ oDotT Ys := by
        rw [oDotT_branch2 (SubstSPD_b1 hYsL) hb2Ys]; exact List.mem_singleton_self _
      exact (hC2s _ hself).1
    obtain ⟨Cs, hNs⟩ := hNs
    by_cases hS : ∃ c ∈ H.comps, c.kind.isSolid = true ∧
        (c.x = y₁ ∧ c.y = y₂ ∨ c.x = y₂ ∧ c.y = y₁)
    · -- `H` has a solid edge `y₁ y₂`: no pair to split
      obtain ⟨c₀, hc₀, hk₀, he₀⟩ := hS
      obtain ⟨d₀, hd₀, hdk₀, hde₀⟩ := (SubstSPD_Bal_H H x y₁ y₂ hN).1 c₀ hc₀ hk₀
      have hxd : ∃ d ∈ liftCs 0 H.comps, d.kind = .xdot ∧
          (d.x = Y₂ ∧ d.y = Y₁ ∨ d.x = Y₁ ∧ d.y = Y₂) := by
        refine ⟨d₀.map (liftA 0), List.mem_map.2 ⟨d₀, hd₀, rfl⟩, hdk₀, ?_⟩
        simp only [Comp.map, hY₁, hY₂]
        rcases he₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hde₀ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
          simp_all
      have hbal : SubstSPD_Bal Gt.comps := by
        refine ⟨fun c hc hks => ?_, fun c hc hkx hne => ?_⟩
        · rw [hc0] at hc ⊢
          rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨d, hd, h⟩ := hHb.1 c hc hks
            exact ⟨d, List.mem_append_left _ hd, h⟩
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl
            · simp [mkC, Kind.isSolid] at hks
            · obtain ⟨d, hd, hdk, hde⟩ := hxd
              exact ⟨d, List.mem_append_left _ hd, hdk, by simpa [mkC] using hde⟩
        · rw [hc0] at hc ⊢
          rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨d, hd, h⟩ := hHb.2 c hc hkx hne
            exact ⟨d, List.mem_append_left _ hd, h⟩
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl <;> simp [mkC] at hkx
      have hb2 : (Gt.splitPairs.isEmpty && !(Gt.comps.any fun c =>
          (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) =
          true := by
        rw [SubstSPD_splitPairs_nil hbal]
        simp only [List.isEmpty_nil, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.any_eq_false]
        intro c hc
        rw [hc0] at hc
        rcases List.mem_append.1 hc with hc | hc
        · have h1 := hHnd c hc
          have h2 := hHsl c hc
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and]
          refine ⟨fun h => absurd h.1 h1, fun hs h => h2 hs h⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl
          · simp [mkC, (SubstSPD_theta_ne o).2, Kind.isSolid]
          · simp [mkC, Kind.isSolid, Ne.symm hne12]
      rw [oDotT_branch2 (SubstSPD_b1 hGtL) hb2, List.mem_singleton] at ht
      subst ht
      have hout := SubstSPD_out_self hGtd (fun c hc hks => hNs.2.1 c
        (by rw [hYsc]; exact List.mem_append_left _ hc) hks)
      refine ⟨⟨_, SubstSPD_Out.normal hout hbal ?_ ?_⟩, hGtd, ?_⟩
      · exact SubstSPD_edge_reach hYsc ⟨mkC (.G .minus) Y₂ Y₁, by rw [hc0]; simp, rfl, rfl⟩
          hNs.1.connected
      · exact SubstSPD_wtd_reach hYsc rfl hNs.1.internal
      · have q : (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).ord =
            H.ord + ((o.sum : ℤ) + 2 - 2 * o.length + 1) := e1
        change _ ≤ (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).ord
        omega
    · -- no solid edge `y₁ y₂` in `H`: the pair `y₂ y₁` is split
      have hnot : ∀ d ∈ liftCs 0 H.comps ++ [mkC (.theta o) X Y₁], (d.kind.isSolid = true ∨
          d.kind = .xdot) → ¬ (d.x = Y₂ ∧ d.y = Y₁ ∨ d.x = Y₁ ∧ d.y = Y₂) := by
        intro d hd hk hde
        rcases List.mem_append.1 hd with hd | hd
        · obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
          simp only [Comp.map, hY₁, hY₂] at hde
          have hde' : d₀.x = y₂ ∧ d₀.y = y₁ ∨ d₀.x = y₁ ∧ d₀.y = y₂ := by
            rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨SubstSPD_liftA_inj h1, SubstSPD_liftA_inj h2⟩
            · exact Or.inr ⟨SubstSPD_liftA_inj h1, SubstSPD_liftA_inj h2⟩
          rcases hk with hk | hk
          · exact hS ⟨d₀, hd₀, hk, by tauto⟩
          · have hne : d₀.x ≠ d₀.y := by
              rcases hde' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
              exacts [Ne.symm hyy, hyy]
            obtain ⟨e, he, hek, hee⟩ := (SubstSPD_Bal_H H x y₁ y₂ hN).2 d₀ hd₀ hk hne
            exact hS ⟨e, he, hek, by
              rcases hde' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hee with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
                simp_all⟩
        · simp only [List.mem_singleton] at hd
          subst hd
          rcases hk with hk | hk <;> simp [mkC, Kind.isSolid] at hk
      have hsp : Gt.splitPairs = [(Y₂, Y₁, true)] := by
        have hGt' : Gt = ⟨(liftCs 0 H.comps ++ [mkC (.theta o) X Y₁]) ++
            [mkC (.G .minus) Y₂ Y₁], Gt.coeff⟩ := by
          rw [show Gt = ⟨Gt.comps, Gt.coeff⟩ from rfl, hc0]; simp
        rw [hGt']
        refine SubstSPD_sp_one _ _ _ (fun d hd hks hne => ?_) (fun d hd hkx hne => ?_) rfl
          (Ne.symm hne12) hnot
        · rcases List.mem_append.1 hd with hd | hd
          · obtain ⟨e, he, h⟩ := hHb.1 d hd hks
            exact ⟨e, List.mem_append_left _ he, h⟩
          · simp only [List.mem_singleton] at hd; subst hd; simp [mkC, Kind.isSolid] at hks
        · rcases List.mem_append.1 hd with hd | hd
          · obtain ⟨e, he, h⟩ := hHb.2 d hd hkx hne
            exact ⟨e, List.mem_append_left _ he, h⟩
          · simp only [List.mem_singleton] at hd; subst hd; simp [mkC] at hkx
      rw [SubstSPD_oDotT_one hGtL hsp] at ht
      rcases ht with hm | hm
      · -- the `×`-dotted piece
        have hX1 : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).comps =
            Ys.comps := hYsc.symm
        have hX1d : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).DotFree := by
          intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact hGtd c hc
          · simp only [List.mem_singleton] at hc; subst hc; simp [mkC]
        have hX1b : SubstSPD_Bal (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ :
            Graph 3 (m + 0)).comps := by
          rw [hX1]; exact SubstSPD_Bal_normal hNs
        have hout := SubstSPD_out_merge hX1d hX1b hm
        have hcon : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ :
            Graph 3 (m + 0)).edgeGraph.Preconnected := by
          have : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).edgeGraph =
              Ys.edgeGraph := by simp only [Graph.edgeGraph, hYsc]
          rw [this]; exact hNs.1.connected
        have hw : ∀ a b : Fin (m + 0), (SimpleGraph.fromRel fun u v => ∃ c ∈ (⟨Gt.comps ++
            [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).comps,
            (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v).Reachable
              (.inr a) (.inr b) := by
          intro a b
          refine SubstSPD_reach_rel id (fun u v huv => ?_) (hNs.1.internal a b)
          obtain ⟨c, hc, hk, rfl, rfl⟩ := huv
          exact SubstSPD_rel_reach ⟨c, by rw [hYsc] at hc; exact hc, by tauto, rfl, rfl⟩
        refine ⟨⟨_, SubstSPD_Out.normal hout hX1b hcon hw⟩, SubstSPD_Out.dotFree hout, ?_⟩
        have h1 := SubstSPD_Out.ord_ge hout hX1d
        have h2 : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).ord =
            H.ord + ((o.sum : ℤ) + 2 - 2 * o.length + 1) := by
          refine Eq.trans ?_ e4
          simp only [Graph.ord, hYsc]
        omega
      · -- the dotted piece
        rw [SubstSPD_mergeT_c H x y₁ y₂ hy₁ hy₂ o] at hm
        have htY : t ∈ oDotT Y := (SubstSPD_oDotT_b3_nil hYL hspY hbY t).2 hm
        obtain ⟨hNt, hDt, -, hε', -⟩ := hC2Y t htY
        have hord := hε' (fun h => hyy h.1)
        have q1 : t.g.ord = H.ord + ((o.sum : ℤ) + 2 - 2 * o.length + 2) := hord.trans e3
        exact ⟨hNt, hDt, by omega⟩

end SigmaPiece

/-! ## The run of the selector `TerminationC_sel` -/

section Inv

open private TerminationC2_Good TerminationC2_R TerminationC2_key TerminationC2_Hyp
  TerminationC2_tSubst_runKinds TerminationC2_inputs from RBM8D.GlobalExp.TerminationC2

/-- The graphs of the run of `TerminationC_sel` ([II, Lemma 6.8]): outputs, or graphs of the run
with a rank that every step lowers. -/
private def RunCompare_I (n D : ℕ) (𝒯 : TRec) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  TerminationC_Out n D g ∨ ∃ r, TerminationC2_Good n D 𝒯 g r

variable {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} {𝔈 : QFam}

/-- The graphs of the step at a graph of the run that is not an output are graphs of the run, and
such a graph lies in the domain `TerminationC_Dom` of the selector. -/
private theorem RunCompare_I_step (hF : QExpFamilyStmt 𝔈) (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : RunCompare_I n D 𝒯 g)
    (hO : ¬ TerminationC_Out n D g) :
    TerminationC_Dom n D g ∧
      ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (TerminationC_sel g), RunCompare_I n D 𝒯 s := by
  rcases hg with h | ⟨r, hr⟩
  · exact absurd h hO
  have hH : TerminationC2_Hyp n D Sig 𝒯 := ⟨hn, hT⟩
  obtain ⟨hD, hs⟩ := TerminationC2_key hH hF (TerminationC2_tSubst_runKinds hH)
    (TerminationC_sel_adm 𝔈 hF n D 𝒯) g r hr hO
  refine ⟨hD, fun s hs' => ?_⟩
  rcases hs s hs' with h | ⟨r', -, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨r', h⟩

/-- The inputs of the run are graphs of the run. -/
private theorem RunCompare_I_inputs (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) :
    ∀ g ∈ h2Rec.A ++ h2Rec.Q, RunCompare_I n D 𝒯 g :=
  TerminationC2_inputs (Sig := Sig) ⟨hn, hT⟩

end Inv

section Mon

/-- **`RunCompare_Hi` passes along the run of `TerminationC_sel`** ([II, Lemma 6.5],
[II, Strategy 6.6]). -/
private theorem RunCompare_hi_step {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} {𝔈 : QFam}
    (hF : QExpFamilyStmt 𝔈) (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {b : Bool}
    {θ : ℤ} (g : Σ n₀ : ℕ, Graph 3 n₀) (hg : RunCompare_I n D 𝒯 g) (hh : RunCompare_Hi b θ g)
    (hO : ¬ TerminationC_Out n D g) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (TerminationC_sel g), RunCompare_Hi b θ s := by
  by_cases hN : ∃ C, g.2.Normal C
  · obtain ⟨C, hN⟩ := hN
    obtain ⟨hD, -⟩ := RunCompare_I_step (𝔈 := 𝔈) hF hn hT hg hO
    have hR : TerminationC_RI n D g := hD.resolve_left fun h => h ⟨C, hN⟩
    exact RunCompare_mon hF hn hT hR hN (TerminationC_sel_adm 𝔈 hF n D 𝒯 g hD hO).1
      ((RunCompare_hi_normal hN).1 hh)
  · exact RunCompare_mon_raw hN hh

/-- The location of the selector is admissible at a graph of the run that is not an output. -/
private theorem RunCompare_adm {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec} {𝔈 : QFam}
    (hF : QExpFamilyStmt 𝔈) (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : RunCompare_I n D 𝒯 g) (hO : ¬ TerminationC_Out n D g) :
    TerminationC_Dom n D g ∧ TerminationC_Adm n D 𝔈 g (TerminationC_sel g) := by
  obtain ⟨hD, -⟩ := RunCompare_I_step (𝔈 := 𝔈) hF hn hT hg hO
  exact ⟨hD, (TerminationC_sel_adm 𝔈 hF n D 𝒯 g hD hO).1⟩

end Mon

/-! ## The outputs at two cutoff orders and two error orders -/

section Out

variable {n n' D D' : ℕ} {g : Σ n₀ : ℕ, Graph 3 n₀}

/-- An output graph of order `≤ n` at the cutoff order `n` is an output graph at every cutoff
order: the stopping rule `(n : ℤ) + 1 ≤ ord` and the class `Graph.LeafA n` do not apply. -/
private theorem RunCompare_out_up (hle : g.2.ord ≤ n) (h : TerminationC_Out n D g) :
    TerminationC_Out n' D g := by
  obtain ⟨⟨h0, hs⟩, hdc, hN, hC, hpl, hcl⟩ := h
  refine ⟨⟨h0, ?_⟩, hdc, hN, hC, hpl, ?_⟩
  · rcases hs with ⟨hN', h1 | h2 | h3 | h4⟩ | h | h
    · exact Or.inl ⟨hN', Or.inl h1⟩
    · omega
    · exact Or.inl ⟨hN', Or.inr (Or.inr (Or.inl h3))⟩
    · exact Or.inl ⟨hN', Or.inr (Or.inr (Or.inr h4))⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases hcl with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have := h.1
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

open private GlobalGoodRows_recoll from RBM8D.GlobalExp.GlobalGoodRows in
/-- An output graph of order `≤ D` with `⊕`, `⊖` in one block is an output graph at every cutoff
order: it is a `⊕/⊖`-recollision graph or a `Q`-graph (the clause on the external atoms and only
diffusive edges at `⊗`), and an output of the class `Graph.LeafA n` is of the class
`Graph.LeafR`. -/
private theorem RunCompare_out_pm (hpm : g.2.PMBlock) (hD : g.2.ord ≤ D)
    (h : TerminationC_Out n D g) : TerminationC_Out n' D g := by
  obtain ⟨⟨h0, -⟩, hdc, hN, hC, hpl, hcl⟩ := h
  have hT := hC.1
  have hst : g.2.IsRecollision {1, 2} ∨ g.2.IsQGraph := by
    rcases hcl with h | h | h | h | h
    · omega
    · exact Or.inl h.1
    · exact Or.inl (GlobalGoodRows_recoll g.2 hpm h.2.2.2.1 hT)
    · exact Or.inr h.1.1
    · exact Or.inl (GlobalGoodRows_recoll g.2 hpm h.2.2.2.1 hT)
  refine ⟨⟨h0, Or.inl ⟨hN, ?_⟩⟩, hdc, hN, hC, hpl, ?_⟩
  · rcases hst with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases hcl with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨-, hL, -, hE, hCI, hgs, hp5⟩ := h
      have hr := GlobalGoodRows_recoll g.2 hpm hE hT
      exact Or.inr (Or.inl ⟨hr, hL, hgs hr, hE, hCI, hp5⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- An output graph of order `≤ D` at the error order `D` is an output graph at every error
order. -/
private theorem RunCompare_out_D (hD : g.2.ord ≤ D)
    (h : TerminationC_Out n D g) : TerminationC_Out n D' g := by
  obtain ⟨⟨h0, hs⟩, hdc, hN, hC, hpl, hcl⟩ := h
  refine ⟨⟨h0, ?_⟩, hdc, hN, hC, fun _ => hpl (by omega), ?_⟩
  · rcases hs with h | ⟨-, h⟩ | h
    · exact Or.inl h
    · omega
    · exact Or.inr (Or.inr h)
  · rcases hcl with ⟨h, -⟩ | h
    · omega
    · exact Or.inr h

end Out

/-! ## Lists of graphs -/

section Lists

private theorem RunCompare_perm_of_count {α : Type*} [DecidableEq α] {L L' : List α} {p : α → Bool}
    (h : ∀ a, p a = true → L.count a = L'.count a) : (L.filter p).Perm (L'.filter p) := by
  rw [List.perm_iff_count]
  intro a
  by_cases hp : p a = true
  · rw [List.count_filter hp, List.count_filter hp]
    exact h a hp
  · rw [List.count_eq_zero.2, List.count_eq_zero.2] <;> simp [List.mem_filter, hp]

private theorem RunCompare_count_of_perm {α : Type*} [DecidableEq α] {L L' : List α} {p : α → Bool}
    (h : (L.filter p).Perm (L'.filter p)) {a : α} (hp : p a = true) :
    L.count a = L'.count a := by
  have := h.count_eq a
  rwa [List.count_filter hp, List.count_filter hp] at this

/-- The images under `f` of two lists, filtered by `q`, agree up to order when the entries
selected by `p` agree up to order and every entry not selected by `p` has an image outside
`q`. -/
private theorem RunCompare_map_filter {α β : Type*} {E₁ E₂ : List α} (f : α → β) (q : β → Bool)
    (p : α → Bool) (h₁ : ∀ a ∈ E₁, p a = false → q (f a) = false)
    (h₂ : ∀ a ∈ E₂, p a = false → q (f a) = false) (h : (E₁.filter p).Perm (E₂.filter p)) :
    ((E₁.map f).filter q).Perm ((E₂.map f).filter q) := by
  have key : ∀ E : List α, (∀ a ∈ E, p a = false → q (f a) = false) →
      (E.map f).filter q = ((E.filter p).map f).filter q := by
    intro E hE
    rw [List.filter_map, List.filter_map, List.filter_filter]
    congr 1
    refine List.filter_congr fun a ha => ?_
    by_cases hp : p a = true
    · simp [hp]
    · simp only [Function.comp_apply, Bool.not_eq_true] at hp ⊢
      rw [hE a ha hp, hp]
      rfl
  rw [key E₁ h₁, key E₂ h₂]
  exact (h.map f).filter q

end Lists

/-! ## The substituted graphs at two cutoff orders and two error orders -/

section Split

open private SubstSPD_chain_mem SubstSPD_tVar_ord from RBM8D.GlobalExp.SubstSPD
open private TerminationB_paperOrd_of_dotFree TerminationB_dotFree_pm
  from RBM8D.GlobalExp.TerminationB
open private labelInc chainLabels_filter from RBM8D.TExp.Closure

/-- The substituted graphs of Steps 2–3 at the host `H.glue x y₁ y₂ (tVar true)`, one for each
graph of the right side of [II, (4.15)]. -/
private theorem RunCompare_gsubst_eq {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (E : Expansion 3) :
    H.globalSubst x y₁ y₂ E.swapSolid =
      E.map fun g => (⟨m + g.1, H.glue x y₁ y₂ g.2.swapSolid⟩ : Σ n₀ : ℕ, Graph 3 n₀) := by
  simp [Graph.globalSubst, Expansion.swapSolid, List.map_map, Function.comp_def]

/-- The right side of [II, (4.15)] in the order: the leading term and the recollision terms, the
terms of `Σ_T`, the graphs of `R`, `A`, `Q`, `Err`. -/
private theorem RunCompare_tSubst_perm (n : ℕ) (𝒯 : TRec) :
    (𝒯.tSubst n).Perm ((leadExp ++ tVarCorr) ++ (sigmaTExp n ++ (𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err))) := by
  classical
  rw [List.perm_iff_count]
  intro a
  simp only [TRec.tSubst, TRec.rhs, List.count_append]
  omega

private theorem RunCompare_labelInc (o : List ℕ) (h : ∀ e ∈ o, 2 ≤ e) :
    labelInc o + 2 * o.length = o.sum := by
  induction o with
  | nil => rfl
  | cons e o ih =>
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h e List.mem_cons_self
    have : labelInc (e :: o) = (e - 2) + labelInc o := by simp [labelInc]
    simp only [List.length_cons, List.sum_cons, this]
    omega

/-- The terms of `Σ_T` of scaling order `≤ m - 1` are those of `Σ_T` at every order `≥ m`. -/
private theorem RunCompare_chain_filter {m N : ℕ} (hm : 3 ≤ m) (hN : m ≤ N) :
    (chainLabels (N - 1)).filter
        (fun o => decide ((o.sum : ℤ) + 2 - 2 * o.length + 1 ≤ (m : ℤ) - 1)) =
      (chainLabels (m - 1)).filter
        (fun o => decide ((o.sum : ℤ) + 2 - 2 * o.length + 1 ≤ (m : ℤ) - 1)) := by
  refine (chainLabels_filter (m - 1) (N - 1) (by omega) _ fun o ho hp => ?_).symm
  have h4 := (SubstSPD_chain_mem _ _ o ho).2
  have hl := RunCompare_labelInc o fun e he => le_trans (by norm_num) (h4 e he)
  simp only [decide_eq_true_eq] at hp
  have : ((o.sum : ℕ) : ℤ) = (labelInc o : ℤ) + 2 * o.length := by rw [← hl]; push_cast; ring
  omega

/-- The selection of the graphs of `R`, `A`, `Q`, `Err` whose substituted graphs reach the
scaling orders `≤ m`: scaling order `≤ m - 1`, or `≤ m` with `⊕`, `⊖` in one block. -/
private def RunCompare_lowA (m : ℕ) (g : Σ n₀ : ℕ, Graph 3 n₀) : Bool :=
  decide (g.2.ord ≤ (m : ℤ) - 1 ∨ (g.2.PMBlock ∧ g.2.ord ≤ m))

/-- The graphs of `R`, `A`, `Q`, `Err` of order `≤ m - 1`, and those of order `≤ m` with `⊕`,
`⊖` in one block, of two `T`-expansions with `TRec.Coherent (m - 1)`, `TRec.CoherentPM m` and the
graphs of `A` of order `≥ m`, agree up to order. -/
private theorem RunCompare_lowA_perm {Sig : ℕ → Expansion 2} {m n n' D : ℕ} {𝒯 𝒯' : TRec}
    (hm : 3 ≤ m) (hmn : m ≤ n) (hmn' : m ≤ n') (hmD : m < D)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) (hT' : 𝒯'.IsTExpStruct Sig (n' - 1) D)
    (hC : TRec.Coherent (m - 1) 𝒯 𝒯') (hPM : TRec.CoherentPM m 𝒯 𝒯')
    (hA : ∀ g ∈ 𝒯.A ++ 𝒯'.A, (m : ℤ) ≤ g.2.ord) :
    ((𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err).filter (RunCompare_lowA m)).Perm
      ((𝒯'.R ++ 𝒯'.A ++ 𝒯'.Q ++ 𝒯'.Err).filter (RunCompare_lowA m)) := by
  classical
  refine RunCompare_perm_of_count fun a ha => ?_
  simp only [RunCompare_lowA, decide_eq_true_eq] at ha
  have hlow : a.2.ord ≤ m := by rcases ha with h | ⟨-, h⟩ <;> omega
  have hE : a ∉ 𝒯.Err := fun h => by have := hT.2.2.2.1.2.2.2.2 a h; omega
  have hE' : a ∉ 𝒯'.Err := fun h => by have := hT'.2.2.2.1.2.2.2.2 a h; omega
  simp only [List.count_append, List.count_eq_zero.2 hE, List.count_eq_zero.2 hE']
  by_cases hmem : a ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ∨ a ∈ 𝒯'.R ++ 𝒯'.A ++ 𝒯'.Q
  swap
  · simp only [List.mem_append, not_or] at hmem
    simp [List.count_eq_zero.2, hmem]
  have h0 : 0 ≤ a.2.ord := by
    rcases hmem with h | h
    · have := (RunCompare_T_ord (by omega) hT (List.mem_append_left _ h)).1; omega
    · have := (RunCompare_T_ord (by omega) hT' (List.mem_append_left _ h)).1; omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = a.2.ord := ⟨a.2.ord.toNat, Int.toNat_of_nonneg h0⟩
  by_cases hp : a.2.PMBlock
  · have := RunCompare_count_of_perm (hPM k (by omega)) (a := a)
      (by simp [Graph.PMBlock] at hp; simp [hp, hk])
    simp only [List.count_append] at this
    omega
  · have hlow' : a.2.ord ≤ (m : ℤ) - 1 := by
      rcases ha with h | ⟨h, -⟩
      · exact h
      · exact absurd h hp
    obtain ⟨hR, hQ⟩ := hC k (by omega)
    have e1 := RunCompare_count_of_perm hR (a := a) (by simp [hk])
    have e2 := RunCompare_count_of_perm hQ (a := a) (by simp [hk])
    have hA1 : a ∉ 𝒯.A := fun h => by have := hA a (List.mem_append_left _ h); omega
    have hA2 : a ∉ 𝒯'.A := fun h => by have := hA a (List.mem_append_right _ h); omega
    rw [List.count_eq_zero.2 hA1, List.count_eq_zero.2 hA2]
    omega

/-- The graphs of `R`, `A`, `Q`, `Err` of order `≤ D` of two `T`-expansions with
`TRec.AgreeTo D` agree up to order. -/
private theorem RunCompare_lowB_perm {Sig : ℕ → Expansion 2} {n D D' : ℕ} {𝒯 𝒯' : TRec}
    (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) (hT' : 𝒯'.IsTExpStruct Sig (n - 1) D')
    (hAg : 𝒯.AgreeTo D 𝒯') :
    ((𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err).filter fun g => decide (g.2.ord ≤ (D : ℤ))).Perm
      ((𝒯'.R ++ 𝒯'.A ++ 𝒯'.Q ++ 𝒯'.Err).filter fun g => decide (g.2.ord ≤ (D : ℤ))) := by
  classical
  refine RunCompare_perm_of_count fun a ha => ?_
  simp only [decide_eq_true_eq] at ha
  by_cases hmem : a ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err ∨ a ∈ 𝒯'.R ++ 𝒯'.A ++ 𝒯'.Q ++ 𝒯'.Err
  swap
  · simp only [not_or] at hmem
    rw [List.count_eq_zero.2 hmem.1, List.count_eq_zero.2 hmem.2]
  have h0 : 0 ≤ a.2.ord := by
    rcases hmem with h | h
    · have := (RunCompare_T_ord hn hT h).1; omega
    · have := (RunCompare_T_ord hn hT' h).1; omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = a.2.ord := ⟨a.2.ord.toNat, Int.toNat_of_nonneg h0⟩
  obtain ⟨hR, hA, hQ, hE⟩ := hAg k (by omega)
  have e1 := RunCompare_count_of_perm hR (a := a) (by simp [hk])
  have e2 := RunCompare_count_of_perm hA (a := a) (by simp [hk])
  have e3 := RunCompare_count_of_perm hQ (a := a) (by simp [hk])
  have e4 := RunCompare_count_of_perm hE (a := a) (by simp [hk])
  simp only [List.count_append]
  omega

/-- A substituted graph all of whose `O_dot` forms are normal regular without dotted edges of
scaling order `≥ θ + 1` has `RunCompare_Hi b θ`. -/
private theorem RunCompare_hi_dotFree {b : Bool} {θ : ℤ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (h : ∀ t ∈ oDotT g.2, (∃ C, t.g.Normal C) ∧ t.g.DotFree ∧ θ + 1 ≤ t.g.ord) :
    RunCompare_Hi b θ g := by
  intro t ht
  obtain ⟨hN, hd, ho⟩ := h t ht
  refine ⟨hN, by rw [TerminationB_paperOrd_of_dotFree hd]; exact ho, fun _ hp => ?_⟩
  exact absurd hp (TerminationB_dotFree_pm hd).1

open Classical in
private theorem RunCompare_not_q {b : Bool} {θ : ℤ} {s : Σ n₀ : ℕ, Graph 3 n₀}
    (h : RunCompare_Hi b θ s) : decide (¬ RunCompare_Hi b θ s) = false := by
  simp [h]

open Classical in
/-- **The substituted graphs of Steps 2–3 at two cutoff orders** ([II, (6.9)]): at a host of order
`≤ m`, the substituted graphs without `RunCompare_Hi true m` of two `T`-expansions with
`TRec.Coherent (m - 1)`, `TRec.CoherentPM m` and the graphs of `A` of order `≥ m` agree up to
order. The other substituted graphs (of the graphs of `R`, `A`, `Q`, `Err` of order `≥ m`, or
`≥ m + 1` with `⊕`, `⊖` in one block, and of the terms of `Σ_T` of order `≥ m`) have only
`O_dot` forms of order `≥ m + 1` without `⊕`, `⊖` in one block. -/
private theorem RunCompare_substA {Sig : ℕ → Expansion 2} {m n n' D : ℕ} {𝒯 𝒯' : TRec}
    (hm : 3 ≤ m) (hmn : m ≤ n) (hmn' : m ≤ n') (hmD : m < D)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) (hT' : 𝒯'.IsTExpStruct Sig (n' - 1) D)
    (hC : TRec.Coherent (m - 1) 𝒯 𝒯') (hPM : TRec.CoherentPM m 𝒯 𝒯')
    (hA : ∀ g ∈ 𝒯.A ++ 𝒯'.A, (m : ℤ) ≤ g.2.ord) {m₀ : ℕ} {H : Graph 3 m₀}
    {x y₁ y₂ : Atom 3 m₀} (hP : TerminationC_HostPrem H x y₁ y₂) :
    ((H.globalSubst x y₁ y₂ (𝒯.tSubst (n - 1)).swapSolid).filter
        fun s => decide (¬ RunCompare_Hi true m s)).Perm
      ((H.globalSubst x y₁ y₂ (𝒯'.tSubst (n' - 1)).swapSolid).filter
        fun s => decide (¬ RunCompare_Hi true m s)) := by
  obtain ⟨ho1, ⟨C, hN⟩, hd, hL, -, -, -, -, hst⟩ := hP
  set q : (Σ n₀ : ℕ, Graph 3 n₀) → Bool := fun s => decide (¬ RunCompare_Hi true m s) with hq
  set FF : (Σ n₀ : ℕ, Graph 3 n₀) → (Σ n₀ : ℕ, Graph 3 n₀) :=
    fun g => ⟨m₀ + g.1, H.glue x y₁ y₂ g.2.swapSolid⟩ with hFF
  have e2 := glue_ord 3 m₀ 1 H x y₁ y₂ (tVar true)
  rw [SubstSPD_tVar_ord] at e2
  rw [RunCompare_gsubst_eq, RunCompare_gsubst_eq]
  refine (((RunCompare_tSubst_perm (n - 1) 𝒯).map FF).filter q).trans
    (List.Perm.trans ?_ (((RunCompare_tSubst_perm (n' - 1) 𝒯').map FF).filter q).symm)
  simp only [List.map_append, List.filter_append]
  refine (List.Perm.refl _).append (List.Perm.append ?_ ?_)
  · -- the terms of `Σ_T`
    simp only [sigmaTExp, List.map_map]
    have hh : ∀ N, ∀ o ∈ chainLabels N,
        decide ((o.sum : ℤ) + 2 - 2 * o.length + 1 ≤ (m : ℤ) - 1) = false →
          q ((FF ∘ fun o => (⟨0, thetaLabelGraph o⟩ : Σ n₀ : ℕ, Graph 3 n₀)) o) = false := by
      intro N o ho hp
      simp only [decide_eq_false_iff_not, not_le] at hp
      refine RunCompare_not_q (RunCompare_hi_dotFree fun t ht => ?_)
      have h4 := (SubstSPD_chain_mem _ _ o ho).2
      have hk : 2 * o.length ≤ o.sum := by
        have := RunCompare_labelInc o fun e he => le_trans (by norm_num) (h4 e he)
        omega
      obtain ⟨h1, h2, h3⟩ := RunCompare_sigma_piece H x y₁ y₂ o hk hL hN hd hst t ht
      refine ⟨h1, h2, ?_⟩
      omega
    refine RunCompare_map_filter _ q _ (hh _) (hh _) ?_
    rw [RunCompare_chain_filter hm hmn, RunCompare_chain_filter hm hmn']
  · -- the graphs of `R`, `A`, `Q`, `Err`
    have hh : ∀ {𝒯₀ : TRec} {N : ℕ}, 3 ≤ N → 𝒯₀.IsTExpStruct Sig (N - 1) D →
        ∀ g ∈ 𝒯₀.R ++ 𝒯₀.A ++ 𝒯₀.Q ++ 𝒯₀.Err, RunCompare_lowA m g = false → q (FF g) = false := by
      intro 𝒯₀ N hN3 hT₀ g hg hp
      simp only [RunCompare_lowA, decide_eq_false_iff_not, not_or, not_and, not_le] at hp
      refine RunCompare_not_q (RunCompare_hi_dotFree fun t ht => ?_)
      obtain ⟨h1, h2, h3, h4⟩ := RunCompare_piece_T hT₀ hL hN hd hst hg ht
      refine ⟨h1, h2, ?_⟩
      by_cases hε : y₁ = y₂ ∧ g.2.PMBlock
      · have := h3 hε
        have := hp.2 hε.2
        omega
      · have := h4 hε
        omega
    have := RunCompare_map_filter FF q _ (hh (by omega) hT) (hh (by omega) hT')
      (RunCompare_lowA_perm hm hmn hmn' hmD hT hT' hC hPM hA)
    simpa only [List.map_append, List.filter_append] using this

open Classical in
/-- **The substituted graphs of Steps 2–3 at two error orders** ([II, Def 3.3 (1)]): the
substituted graphs without `RunCompare_Hi false D` of two `T`-expansions with
`TRec.AgreeTo D` agree up to order; the substituted graphs of the graphs of order `≥ D + 1` have
only `O_dot` forms of order `≥ D + 1`. -/
private theorem RunCompare_substB {Sig : ℕ → Expansion 2} {n D D' : ℕ} {𝒯 𝒯' : TRec}
    (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) (hT' : 𝒯'.IsTExpStruct Sig (n - 1) D')
    (hAg : 𝒯.AgreeTo D 𝒯') {m₀ : ℕ} {H : Graph 3 m₀} {x y₁ y₂ : Atom 3 m₀}
    (hP : TerminationC_HostPrem H x y₁ y₂) :
    ((H.globalSubst x y₁ y₂ (𝒯.tSubst (n - 1)).swapSolid).filter
        fun s => decide (¬ RunCompare_Hi false D s)).Perm
      ((H.globalSubst x y₁ y₂ (𝒯'.tSubst (n - 1)).swapSolid).filter
        fun s => decide (¬ RunCompare_Hi false D s)) := by
  obtain ⟨ho1, ⟨C, hN⟩, hd, hL, -, -, -, -, hst⟩ := hP
  set q : (Σ n₀ : ℕ, Graph 3 n₀) → Bool := fun s => decide (¬ RunCompare_Hi false D s) with hq
  set FF : (Σ n₀ : ℕ, Graph 3 n₀) → (Σ n₀ : ℕ, Graph 3 n₀) :=
    fun g => ⟨m₀ + g.1, H.glue x y₁ y₂ g.2.swapSolid⟩ with hFF
  rw [RunCompare_gsubst_eq, RunCompare_gsubst_eq]
  refine (((RunCompare_tSubst_perm (n - 1) 𝒯).map FF).filter q).trans
    (List.Perm.trans ?_ (((RunCompare_tSubst_perm (n - 1) 𝒯').map FF).filter q).symm)
  simp only [List.map_append, List.filter_append]
  refine (List.Perm.refl _).append ((List.Perm.refl _).append ?_)
  have hh : ∀ {𝒯₀ : TRec} {D₀ : ℕ}, 𝒯₀.IsTExpStruct Sig (n - 1) D₀ →
      ∀ g ∈ 𝒯₀.R ++ 𝒯₀.A ++ 𝒯₀.Q ++ 𝒯₀.Err, decide (g.2.ord ≤ (D : ℤ)) = false →
        q (FF g) = false := by
    intro 𝒯₀ D₀ hT₀ g hg hp
    simp only [decide_eq_false_iff_not, not_le] at hp
    refine RunCompare_not_q (RunCompare_hi_dotFree fun t ht => ?_)
    obtain ⟨h1, h2, h3, h4⟩ := RunCompare_piece_T hT₀ hL hN hd hst hg ht
    refine ⟨h1, h2, ?_⟩
    by_cases hε : y₁ = y₂ ∧ g.2.PMBlock
    · have := h3 hε
      omega
    · have := h4 hε
      omega
  have := RunCompare_map_filter FF q _ (hh hT) (hh hT') (RunCompare_lowB_perm hn hT hT' hAg)
  simpa only [List.map_append, List.filter_append] using this

end Split

/-! ## One step of the two runs -/

section Steps

variable {𝔈 : QFam}

open Classical in
/-- **(6.9) at one graph of the run** ([II, (6.8)–(6.9)]): the graphs without
`RunCompare_Hi true m` of the step of `TerminationC_sel` at a graph of the run at the cutoff order
`n` with `𝒯` and at the cutoff order `n'` with `𝒯'` agree up to order. Only the substitution of
Steps 2–3 reads the cutoff order and the `T`-expansion. -/
private theorem RunCompare_stepA {Sig : ℕ → Expansion 2} {m n n' D : ℕ} {𝒯 𝒯' : TRec}
    (hF : QExpFamilyStmt 𝔈) (hm : 3 ≤ m) (hmn : m ≤ n) (hmn' : m ≤ n') (hmD : m < D)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) (hT' : 𝒯'.IsTExpStruct Sig (n' - 1) D)
    (hC : TRec.Coherent (m - 1) 𝒯 𝒯') (hPM : TRec.CoherentPM m 𝒯 𝒯')
    (hA : ∀ g ∈ 𝒯.A ++ 𝒯'.A, (m : ℤ) ≤ g.2.ord) (g : Σ n₀ : ℕ, Graph 3 n₀)
    (hg : RunCompare_I n D 𝒯 g) (hO : ¬ TerminationC_Out n D g) :
    ((TerminationC_stepOut n D 𝒯 𝔈 g (TerminationC_sel g)).filter
        fun s => decide (¬ RunCompare_Hi true m s)).Perm
      ((TerminationC_stepOut n' D 𝒯' 𝔈 g (TerminationC_sel g)).filter
        fun s => decide (¬ RunCompare_Hi true m s)) := by
  by_cases hN : ∃ C, g.2.Normal C
  · obtain ⟨-, hAd⟩ := RunCompare_adm hF (by omega) hT hg hO
    generalize TerminationC_sel g = l at hAd ⊢
    cases l
    case subst m₀ H x y₁ y₂ =>
      exact RunCompare_substA hm hmn hmn' hmD hT hT' hC hPM hA hAd.2.2.2
    all_goals exact List.Perm.refl _
  · rcases RunCompare_sel_raw hN with ⟨i, hi⟩ | hi <;> rw [hi] <;> exact List.Perm.refl _

open Classical in
/-- **The error order at one graph of the run** ([II, Def 3.3 (1)]): the graphs without
`RunCompare_Hi false D` of the step of `TerminationC_sel` at a graph of both runs at the error
orders `D ≤ D'` agree up to order. Only the substitution of Steps 2–3 (through `𝒯`, `𝒯'`) and
the `Q`-expansion of Step 3 (through `𝔈 D`, `𝔈 D'`, clause (F3) of `QExpFamilyStmt`) read the
error order. -/
private theorem RunCompare_stepB {Sig : ℕ → Expansion 2} {n D D' : ℕ} {𝒯 𝒯' : TRec}
    (hF : QExpFamilyStmt 𝔈) (hn : 3 ≤ n) (hDD' : D ≤ D')
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) (hT' : 𝒯'.IsTExpStruct Sig (n - 1) D')
    (hAg : 𝒯.AgreeTo D 𝒯') (g : Σ n₀ : ℕ, Graph 3 n₀)
    (hg : RunCompare_I n D 𝒯 g) (hg' : RunCompare_I n D' 𝒯' g)
    (hO : ¬ TerminationC_Out n D g) (hO' : ¬ TerminationC_Out n D' g) :
    ((TerminationC_stepOut n D 𝒯 𝔈 g (TerminationC_sel g)).filter
        fun s => decide (¬ RunCompare_Hi false D s)).Perm
      ((TerminationC_stepOut n D' 𝒯' 𝔈 g (TerminationC_sel g)).filter
        fun s => decide (¬ RunCompare_Hi false D s)) := by
  by_cases hN : ∃ C, g.2.Normal C
  · obtain ⟨-, hAd⟩ := RunCompare_adm hF hn hT hg hO
    obtain ⟨-, hAd'⟩ := RunCompare_adm hF hn hT' hg' hO'
    generalize TerminationC_sel g = l at hAd hAd' ⊢
    cases l
    case subst m₀ H x y₁ y₂ =>
      exact RunCompare_substB hn hT hT' hAg hAd.2.2.2
    case qexp x =>
      obtain ⟨⟨C, hN'⟩, hP, -, hform, -, -, hq⟩ := hAd
      obtain ⟨-, -, -, -, -, -, hq'⟩ := hAd'
      set P : (Σ n₀ : ℕ, Graph 3 n₀) → Bool := fun s => decide (s.2.paperOrd ≤ D) with hPd
      have h3 := hF.2.2.1 D D' g.1 x g.2 hDD' ⟨C, hN'⟩ hform hP P
        (fun s hs => by simpa [hPd] using hs)
      have hnorm : ∀ {D₀ : ℕ}, qexpClauseB D₀ x g.2 (𝔈 D₀ g.1 x g.2) →
          ∀ s ∈ (𝔈 D₀ g.1 x g.2).forget, ∃ C, s.2.Normal C := by
        intro D₀ hq₀ s hs
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
        obtain ⟨C', hout⟩ := hq₀.1
        exact ⟨C', (hout t ht).1.1.1⟩
      have conv : ∀ L : Expansion 3, (∀ s ∈ L, ∃ C, s.2.Normal C) →
          L.filter (fun s => decide (¬ RunCompare_Hi false D s)) = L.filter P := by
        intro L hL
        refine List.filter_congr fun s hs => ?_
        obtain ⟨C, hC⟩ := hL s hs
        rw [RunCompare_hi_normal hC]
        by_cases h : s.2.paperOrd ≤ D
        · have : ¬ RunCompare_HiN false (D : ℤ) s.2 := fun h' => by have := h'.1; omega
          simp [hPd, h, this]
        · have : RunCompare_HiN false (D : ℤ) s.2 := ⟨by omega, fun h => by cases h⟩
          simp [hPd, h, this]
      change ((𝔈 D g.1 x g.2).forget.filter _).Perm ((𝔈 D' g.1 x g.2).forget.filter _)
      rw [conv _ (hnorm hq), conv _ (hnorm hq')]
      exact h3.symm
    all_goals exact List.Perm.refl _
  · rcases RunCompare_sel_raw hN with ⟨i, hi⟩ | hi <;> rw [hi] <;> exact List.Perm.refl _

/-- An output graph without `RunCompare_Hi true m` has scaling order `≤ m`, or `≤ m + 1` with
`⊕`, `⊖` in one block; at a cutoff order `n ≥ m` it is an output at every cutoff order. -/
private theorem RunCompare_outA {m n n' D : ℕ} (hmn : m ≤ n) (hmD : m < D)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hh : ¬ RunCompare_Hi true m g)
    (h : TerminationC_Out n D g) : TerminationC_Out n' D g := by
  obtain ⟨C, hN⟩ := h.2.2.1
  have h0 : g.2.dotExcess = 0 := h.2.2.2.1.2.1
  rw [RunCompare_hi_normal hN] at hh
  have hp := Graph.paperOrd_of_dotExcess h0
  by_cases hle : g.2.ord ≤ m
  · exact RunCompare_out_up (by omega) h
  · have hpm : g.2.PMBlock ∧ g.2.ord ≤ m + 1 := by
      by_contra hc
      refine hh ⟨by omega, fun _ hpm => ?_⟩
      have : ¬ g.2.ord ≤ m + 1 := fun h' => hc ⟨hpm, h'⟩
      omega
    exact RunCompare_out_pm hpm.1 (by omega) h

/-- An output graph without `RunCompare_Hi false D` has scaling order `≤ D`; at two error orders
`D ≤ D'` it is an output at both. -/
private theorem RunCompare_outB {n D D' : ℕ} (hDD' : D ≤ D') {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hh : ¬ RunCompare_Hi false D g) :
    TerminationC_Out n D g ↔ TerminationC_Out n D' g := by
  have key : ∀ {D₀ : ℕ}, TerminationC_Out n D₀ g → g.2.ord ≤ D := by
    intro D₀ h
    obtain ⟨C, hN⟩ := h.2.2.1
    have h0 : g.2.dotExcess = 0 := h.2.2.2.1.2.1
    rw [RunCompare_hi_normal hN] at hh
    have hp := Graph.paperOrd_of_dotExcess h0
    by_contra hc
    exact hh ⟨by omega, fun h => by cases h⟩
  exact ⟨fun h => RunCompare_out_D (key h) h, fun h => RunCompare_out_D (by have := key h; omega) h⟩

private theorem RunCompare_filter_sub {F : Expansion 3} {p q : (Σ n₀ : ℕ, Graph 3 n₀) → Bool}
    (h : ∀ g ∈ F, p g = true → q g = true) : F.filter p = (F.filter q).filter p := by
  rw [List.filter_filter]
  refine List.filter_congr fun g hg => ?_
  by_cases hp : p g = true
  · simp [hp, h g hg hp]
  · simp only [Bool.not_eq_true] at hp
    simp [hp]

end Steps

/-! ## The run as a function and its comparison -/

section Main

theorem RunCompare_exists {𝔈 : QFam} {n D : ℕ} {𝒯 : TRec}
    (h : 3 ≤ n ∧ (∃ Sig, 𝒯.IsTExpStruct Sig (n - 1) D) ∧ QExpFamilyStmt 𝔈) :
    ∃ F, SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) F ∧
      ∀ g ∈ F, TerminationC_Out n D g := by
  obtain ⟨hn, ⟨Sig, hT⟩, hF⟩ := h
  exact (strategyB_sel 𝔈 hF).1 n D Sig 𝒯 TerminationC_sel hn hT (TerminationC_sel_adm 𝔈 hF n D 𝒯)

open Classical in
/-- **The run of [II, Strategy 6.6]** ([II, Lemma 6.8]) driven by the selector
`TerminationC_sel`, with the cutoff order `n`, the error order `D`, the `T`-expansion `𝒯`
substituted in Steps 2–3 and the family `𝔈` of `Q`-expansions of [II, Lemma 4.15] used in Step 3,
from the graphs of `A` and `Q` of the second order `T`-expansion: its output graphs when `n ≥ 3`,
`𝒯` is the structural part of an `(n - 1)`-th order `T`-expansion with error order `D` and `𝔈`
satisfies `QExpFamilyStmt` (the run then ends, `strategyB_sel`, and is unique,
`SelRunB.functional`), and `[]` otherwise. -/
noncomputable def RunCompare.run (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (n D : ℕ) (𝒯 : TRec) : Expansion 3 :=
  if h : 3 ≤ n ∧ (∃ Sig, 𝒯.IsTExpStruct Sig (n - 1) D) ∧ QExpFamilyStmt 𝔈 then
    (RunCompare_exists h).choose
  else []

/-- **The run of `TerminationC_sel`** ([II, Lemma 6.8]): for `n ≥ 3`, an `(n - 1)`-th order
`T`-expansion `𝒯` with error order `D` and a family `𝔈` with `QExpFamilyStmt`, `RunCompare.run`
is the run driven by `TerminationC_sel` from the graphs of `A` and `Q` of the second order
`T`-expansion, a run of [II, Strategy 6.6] (`GlobalRunB`), and every output graph is an output
with the clauses of [II, Lemma 6.8] (`TerminationC_Out`). -/
theorem RunCompare.run_spec (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀)
    (hF : QExpFamilyStmt 𝔈) (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec) (hn : 3 ≤ n)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) :
    SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) (RunCompare.run 𝔈 n D 𝒯) ∧
      GlobalRunB n D 𝒯 (h2Rec.A ++ h2Rec.Q) (RunCompare.run 𝔈 n D 𝒯) ∧
      ∀ g ∈ RunCompare.run 𝔈 n D 𝒯, TerminationC_Out n D g := by
  have h : 3 ≤ n ∧ (∃ Sig, 𝒯.IsTExpStruct Sig (n - 1) D) ∧ QExpFamilyStmt 𝔈 :=
    ⟨hn, ⟨Sig, hT⟩, hF⟩
  have e : RunCompare.run 𝔈 n D 𝒯 = (RunCompare_exists h).choose := by
    unfold RunCompare.run
    exact dite_eq_left_of_eq_true (eq_true h)
  rw [e]
  obtain ⟨h1, h2⟩ := (RunCompare_exists h).choose_spec
  exact ⟨h1, h1.globalRunB, h2⟩

open Classical in
/-- **(6.9) for the run of `TerminationC_sel`**, on the outputs without `RunCompare_Hi true m`. -/
private theorem RunCompare_partA {𝔈 : QFam} (hF : QExpFamilyStmt 𝔈) {Sig : ℕ → Expansion 2}
    {m n n' D : ℕ} {𝒯 𝒯' : TRec} (hm : 3 ≤ m) (hmn : m ≤ n) (hmn' : m ≤ n') (hmD : m < D)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) (hT' : 𝒯'.IsTExpStruct Sig (n' - 1) D)
    (hC : TRec.Coherent (m - 1) 𝒯 𝒯') (hPM : TRec.CoherentPM m 𝒯 𝒯')
    (hA : ∀ g ∈ 𝒯.A ++ 𝒯'.A, (m : ℤ) ≤ g.2.ord) :
    ((RunCompare.run 𝔈 n D 𝒯).filter fun s => decide (¬ RunCompare_Hi true m s)).Perm
      ((RunCompare.run 𝔈 n' D 𝒯').filter fun s => decide (¬ RunCompare_Hi true m s)) := by
  have hn : 3 ≤ n := by omega
  have hn' : 3 ≤ n' := by omega
  refine RunCompare_sim (I₁ := RunCompare_I n D 𝒯) (I₂ := RunCompare_I n' D 𝒯')
    (fun _ hg hO => (RunCompare_I_step (𝔈 := 𝔈) hF hn hT hg hO).2)
    (fun _ hg hO => (RunCompare_I_step (𝔈 := 𝔈) hF hn' hT' hg hO).2)
    (fun g hg hh hO => RunCompare_hi_step hF hn hT g hg hh hO)
    (fun g hg hh hO => RunCompare_hi_step hF hn' hT' g hg hh hO)
    (fun _ _ _ hh => ⟨RunCompare_outA hmn hmD hh, RunCompare_outA hmn' hmD hh⟩)
    (fun g hg _ _ hO _ => RunCompare_stepA hF hm hmn hmn' hmD hT hT' hC hPM hA g hg hO)
    (RunCompare.run_spec 𝔈 hF n D Sig 𝒯 hn hT).1 (RunCompare.run_spec 𝔈 hF n' D Sig 𝒯' hn' hT').1
    (RunCompare_I_inputs hn hT) (RunCompare_I_inputs hn' hT') (List.Perm.refl _)

open Classical in
/-- **The error order for the run of `TerminationC_sel`**, on the outputs without
`RunCompare_Hi false D`. -/
private theorem RunCompare_partB {𝔈 : QFam} (hF : QExpFamilyStmt 𝔈) {Sig : ℕ → Expansion 2}
    {n D D' : ℕ} {𝒯 𝒯' : TRec} (hn : 3 ≤ n) (hDD' : D ≤ D')
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) (hT' : 𝒯'.IsTExpStruct Sig (n - 1) D')
    (hAg : 𝒯.AgreeTo D 𝒯') :
    ((RunCompare.run 𝔈 n D 𝒯).filter fun s => decide (¬ RunCompare_Hi false D s)).Perm
      ((RunCompare.run 𝔈 n D' 𝒯').filter fun s => decide (¬ RunCompare_Hi false D s)) :=
  RunCompare_sim (I₁ := RunCompare_I n D 𝒯) (I₂ := RunCompare_I n D' 𝒯')
    (fun _ hg hO => (RunCompare_I_step (𝔈 := 𝔈) hF hn hT hg hO).2)
    (fun _ hg hO => (RunCompare_I_step (𝔈 := 𝔈) hF hn hT' hg hO).2)
    (fun g hg hh hO => RunCompare_hi_step hF hn hT g hg hh hO)
    (fun g hg hh hO => RunCompare_hi_step hF hn hT' g hg hh hO)
    (fun _ _ _ hh => RunCompare_outB hDD' hh)
    (fun g hg hg' _ hO hO' => RunCompare_stepB hF hn hDD' hT hT' hAg g hg hg' hO hO')
    (RunCompare.run_spec 𝔈 hF n D Sig 𝒯 hn hT).1 (RunCompare.run_spec 𝔈 hF n D' Sig 𝒯' hn hT').1
    (RunCompare_I_inputs hn hT) (RunCompare_I_inputs hn hT') (List.Perm.refl _)

/-- An output graph of the run of scaling order `k` has no `RunCompare_Hi b θ` when `k ≤ θ`, or
when `b`, `k ≤ θ + 1` and `⊕`, `⊖` lie in one block. -/
private theorem RunCompare_not_hi {n D : ℕ} {b : Bool} {θ : ℤ} {g : Σ n₀ : ℕ, Graph 3 n₀}
    (h : TerminationC_Out n D g) (hk : g.2.ord ≤ θ ∨ (b = true ∧ g.2.PMBlock ∧ g.2.ord ≤ θ + 1)) :
    ¬ RunCompare_Hi b θ g := by
  obtain ⟨C, hN⟩ := h.2.2.1
  rw [RunCompare_hi_normal hN, RunCompare_HiN, Graph.paperOrd_of_dotExcess h.2.2.2.1.2.1]
  rintro ⟨h1, h2⟩
  rcases hk with hk | ⟨hb, hp, hk⟩
  · omega
  · have := h2 hb hp
    omega

open Classical in
/-- **The comparison of runs** ([II, (6.8)–(6.9)], [II, Def 3.2 (7)], [II, Def 3.3 (1)]) for the
run `RunCompare.run` of `TerminationC_sel`, for every family `𝔈` of `Q`-expansions of
[II, Lemma 4.15] with `QExpFamilyStmt`:
* (6.9): for cutoff orders `n, n' ≥ m ≥ 3`, one error order `D > m`, and `T`-expansions of orders
  `n - 1`, `n' - 1` whose graphs of `R`, `Q` agree up to order `m - 1` (`TRec.Coherent`), whose
  graphs with `⊕`, `⊖` in one dotted block agree up to order `m` (`TRec.CoherentPM`), and whose
  graphs of `A` have order `≥ m`, the output graphs of every order `k ≤ m` agree up to order, and
  those with `⊕`, `⊖` in one dotted block of every order `k ≤ m + 1`;
* the error order: for `3 ≤ n < D ≤ D'` and `T`-expansions of order `n - 1` with error orders `D`,
  `D'` whose graphs of order `≤ D` agree (`TRec.AgreeTo`), the output graphs of every order
  `k ≤ D` agree up to order. -/
theorem RunCompare.runCompare :
    ∀ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 →
    (∀ (Sig : ℕ → Expansion 2) (m n n' D : ℕ) (𝒯 𝒯' : TRec), 3 ≤ m → m ≤ n → m ≤ n' →
      m < D → 𝒯.IsTExpStruct Sig (n - 1) D → 𝒯'.IsTExpStruct Sig (n' - 1) D →
      TRec.Coherent (m - 1) 𝒯 𝒯' → TRec.CoherentPM m 𝒯 𝒯' →
      (∀ g ∈ 𝒯.A ++ 𝒯'.A, (m : ℤ) ≤ g.2.ord) →
      (∀ k : ℕ, k ≤ m →
        ((RunCompare.run 𝔈 n D 𝒯).filter fun g => decide (g.2.ord = (k : ℤ))).Perm
          ((RunCompare.run 𝔈 n' D 𝒯').filter fun g => decide (g.2.ord = (k : ℤ)))) ∧
      (∀ k : ℕ, k ≤ m + 1 →
        ((RunCompare.run 𝔈 n D 𝒯).filter
            fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ))).Perm
          ((RunCompare.run 𝔈 n' D 𝒯').filter
            fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ))))) ∧
    (∀ (Sig : ℕ → Expansion 2) (n D D' : ℕ) (𝒯 𝒯' : TRec), 3 ≤ n → n < D → D ≤ D' →
      𝒯.IsTExpStruct Sig (n - 1) D → 𝒯'.IsTExpStruct Sig (n - 1) D' → 𝒯.AgreeTo D 𝒯' →
      ∀ k : ℕ, k ≤ D →
        ((RunCompare.run 𝔈 n D 𝒯).filter fun g => decide (g.2.ord = (k : ℤ))).Perm
          ((RunCompare.run 𝔈 n D' 𝒯').filter fun g => decide (g.2.ord = (k : ℤ)))) := by
  intro 𝔈 hF
  refine ⟨fun Sig m n n' D 𝒯 𝒯' hm hmn hmn' hmD hT hT' hC hPM hA => ?_,
    fun Sig n D D' 𝒯 𝒯' hn hnD hDD' hT hT' hAg k hk => ?_⟩
  · have hP := RunCompare_partA hF hm hmn hmn' hmD hT hT' hC hPM hA
    have hO := (RunCompare.run_spec 𝔈 hF n D Sig 𝒯 (by omega) hT).2.2
    have hO' := (RunCompare.run_spec 𝔈 hF n' D Sig 𝒯' (by omega) hT').2.2
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [RunCompare_filter_sub (q := fun s => decide (¬ RunCompare_Hi true m s)) fun g hg hp =>
          by simpa using RunCompare_not_hi (hO g hg) (Or.inl (by simp at hp; omega)),
        RunCompare_filter_sub (F := RunCompare.run 𝔈 n' D 𝒯')
          (q := fun s => decide (¬ RunCompare_Hi true m s)) fun g hg hp =>
          by simpa using RunCompare_not_hi (hO' g hg) (Or.inl (by simp at hp; omega))]
      exact hP.filter _
    · have key : ∀ F : Expansion 3, (∀ g ∈ F, TerminationC_Out n D g ∨
          TerminationC_Out n' D g) → ∀ g ∈ F,
          (g.2.pmBlockB && decide (g.2.ord = (k : ℤ))) = true →
            decide (¬ RunCompare_Hi true m g) = true := by
        intro F hF' g hg hp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        have hk' : g.2.ord ≤ m ∨ (true = true ∧ g.2.PMBlock ∧ g.2.ord ≤ m + 1) := by
          by_cases h : g.2.ord ≤ m
          · exact Or.inl h
          · exact Or.inr ⟨rfl, hp.1, by omega⟩
        rcases hF' g hg with h | h
        · simpa using RunCompare_not_hi h hk'
        · simpa using RunCompare_not_hi h hk'
      rw [RunCompare_filter_sub (key _ fun g hg => Or.inl (hO g hg)),
        RunCompare_filter_sub (F := RunCompare.run 𝔈 n' D 𝒯') (key _ fun g hg => Or.inr (hO' g hg))]
      exact hP.filter _
  · have hP := RunCompare_partB hF hn hDD' hT hT' hAg
    have hO := (RunCompare.run_spec 𝔈 hF n D Sig 𝒯 hn hT).2.2
    have hO' := (RunCompare.run_spec 𝔈 hF n D' Sig 𝒯' hn hT').2.2
    rw [RunCompare_filter_sub (q := fun s => decide (¬ RunCompare_Hi false D s)) fun g hg hp =>
        by simpa using RunCompare_not_hi (hO g hg) (Or.inl (by simp at hp; omega)),
      RunCompare_filter_sub (F := RunCompare.run 𝔈 n D' 𝒯')
        (q := fun s => decide (¬ RunCompare_Hi false D s)) fun g hg hp =>
        by simpa using RunCompare_not_hi (hO' g hg) (Or.inl (by simp at hp; omega))]
    exact hP.filter _

end Main

/-! ## The graphs of `Q` of the second order `T`-expansion -/

section Instances

open private h2Rec_struct from RBM8D.TExp.Second

/-- The graphs of `Q` without internal atom of the second order `T`-expansion are outputs of the
run at every cutoff order and every error order `D > 2`. -/
private theorem RunCompare_q0_out {n D : ℕ} (hD : 2 < D) {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hg : g ∈ h2Rec.Q) (h0 : g.1 = 0) : TerminationC_Out n D g := by
  have hS := h2Rec_struct (fun _ => []) D hD
  have hSh := hS.2.2.2.1
  have hDef := hS.2.2.2.2
  have hRAQ : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q := List.mem_append_right _ hg
  obtain ⟨hN, -, -, hdc⟩ := hSh.1.1 g hRAQ
  obtain ⟨hTD, hX, hNL, hlab⟩ := RunCompare_def63_leaf hDef g (List.mem_append_left _ hRAQ)
  have hq := (hSh.2.2.2.1 g hg).1
  obtain ⟨hspd, hql, hcase⟩ := RunCompare_def63_Q hDef g hg
  have hroot : g.2.RootAtPlus := by
    rcases hcase with ⟨-, h⟩ | ⟨hE, -⟩
    · exact h
    · exact absurd h0 (Strategy_extClause_ne_zero hE)
  refine ⟨⟨hX, Or.inl ⟨hN, Or.inr (Or.inr (Or.inl hq))⟩⟩, hdc, hN, ⟨hTD, hX, hNL, hlab⟩,
    fun _ => TRec.plain_of_def63 hDef g hRAQ, Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hq, hspd, hql,
      RunCompare_def63_pmQ hDef g hg, RunCompare_def63_rg hDef g (List.mem_append_left _ hg)⟩,
      fun h => absurd h0 h, fun _ => ⟨hroot, TRec.qLabelAtPlus_of_def63 hDef g hg h0,
        TRec.minusProfile_of_def63 hDef g (List.mem_append_right _ hg) h0⟩⟩)))⟩

end Instances

end RBM8D.Graphs
