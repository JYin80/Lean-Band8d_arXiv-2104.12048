module

public import RBM8D.MainDefs
public import RBM8D.Deloc.Eq113
public import RBM8D.Deloc.Lemma81
public import RBM8D.Joint.Main
public import RBM8D.SelfEnergy.Assembly

@[expose] public section

/-!
# [I, Theorem 1.3]: the joint statement

`Thm13Stmt`: [I, Theorem 1.3] with (1.12) and (1.13) under one set of hypotheses and one
threshold `L₀`, one probability bound per event; it follows from the two statements
`Thm13_eq112Stmt` and `Thm13_eq113Stmt`.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Complex Matrix
open scoped ENNReal

namespace RBM8D

open Graphs

/-- `Thm13Stmt` from (1.12) and (1.13), with `L₀` the larger of the two thresholds. -/
private theorem Thm13_of_parts (h12 : Thm13_eq112Stmt) (h13 : Thm13_eq113Stmt) : Thm13Stmt := by
  intro d hd P c₀ c₁ κ hc₀ hc₁ hκ γ K hγ hγ1 hK τ D hτ hD
  obtain ⟨L₁, h₁⟩ := h12 d hd P c₀ c₁ κ hc₀ hc₁ hκ γ K hγ hγ1 hK τ D hτ hD
  obtain ⟨L₂, h₂⟩ := h13 d hd P c₀ c₁ κ hc₀ hc₁ hκ γ K hγ hγ1 hK τ D hτ hD
  exact ⟨max L₁ L₂, fun p ℓ hL hWℓ hℓ hcW hWL =>
    ⟨h₁ p ℓ (le_trans (le_max_left _ _) hL) hWℓ hℓ hcW hWL,
      h₂ p ℓ (le_trans (le_max_right _ _) hL) hWℓ hℓ hcW hWL⟩⟩

end RBM8D
