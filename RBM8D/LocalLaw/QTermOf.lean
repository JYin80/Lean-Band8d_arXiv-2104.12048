module

public import RBM8D.LocalLaw.QTerm
public import RBM8D.LocalLaw.LabelPaths

@[expose] public section

/-!
# [II, Claim 8.7]: the sum over the graphs of `Q`

The bound [II, (8.25)] on `|E T_{𝔞𝔟}^{q−1} (Q_T^{(n)})_{𝔞,𝔟𝔟}|` is proved graph by graph and
summed over the finite list of graphs of `Q`. This file contains the summation step
`QTermOf_list_int`: if every term of a list is integrable with `|E F_x| ≤ c`, the sum of the list
is integrable with `|E Σ F_x| ≤ |l| c`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

open Graphs

section Env

variable {d : ℕ} {P : Profile d} {c₀ c₁ κ ε c₀T : ℝ} {n D : ℕ} {Sig : ℕ → Expansion 2}
  {𝒯 : TRec} {ε₀ : ℝ} {U : SizeL → Type} {z : ∀ p, U p → ℂ} {Φ : ∀ p, U p → ℝ} {δ : ℝ}

end Env

section EnvFacts

variable {d : ℕ} {P : Profile d} {c₁ δ : ℝ} {W L : ℕ} [NeZero L] {zz : ℂ} {Φu : ℝ}

end EnvFacts

section Values

variable {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (zz : ℂ)

end Values

section Rooted

variable {d : ℕ} {P : Profile d} {c₀ c₁ κ ε c₀T : ℝ} {n D : ℕ} {Sig : ℕ → Expansion 2}
  {𝒯 : TRec} {ε₀ : ℝ} {U : SizeL → Type} {z : ∀ p, U p → ℂ} {Φ : ∀ p, U p → ℝ} {δ : ℝ}

end Rooted

section Recoll

variable {d : ℕ} {P : Profile d} {c₀ c₁ κ ε c₀T : ℝ} {n D : ℕ} {Sig : ℕ → Expansion 2}
  {𝒯 : TRec} {ε₀ : ℝ} {U : SizeL → Type} {z : ∀ p, U p → ℂ} {Φ : ∀ p, U p → ℝ} {δ : ℝ}

end Recoll

section Mean

variable {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (zz : ℂ)

end Mean

section MeanClass

variable {d : ℕ} {P : Profile d} {c₀ c₁ κ ε c₀T : ℝ} {n D : ℕ} {Sig : ℕ → Expansion 2}
  {𝒯 : TRec} {ε₀ : ℝ} {U : SizeL → Type} {z : ∀ p, U p → ℂ} {Φ : ∀ p, U p → ℝ} {δ : ℝ}

end MeanClass

/-! ## The sum over the graphs of `Q` -/

/-- `|E Σ_{x ∈ l} F_x| ≤ |l| c` when every `F_x` is integrable with `|E F_x| ≤ c`. -/
private lemma QTermOf_list_int {α Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (l : List α)
    (F : α → Ω → ℂ) (hF : ∀ x ∈ l, Integrable (F x) μ) (c : ℝ)
    (hc : ∀ x ∈ l, ‖∫ ω, F x ω ∂μ‖ ≤ c) :
    Integrable (fun ω => (l.map fun x => F x ω).sum) μ ∧
      ‖∫ ω, (l.map fun x => F x ω).sum ∂μ‖ ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun y hy => hF y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    have hx := hF x (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    refine ⟨hx.add ih1, ?_⟩
    rw [integral_add hx ih1]
    refine (norm_add_le _ _).trans ?_
    have := hc x (List.mem_cons_self ..)
    push_cast
    linarith

section Assembly

variable {d : ℕ} {P : Profile d} {c₀ c₁ κ ε c₀T : ℝ} {n D : ℕ} {Sig : ℕ → Expansion 2}
  {𝒯 : TRec} {ε₀ : ℝ} {U : SizeL → Type} {z : ∀ p, U p → ℂ} {Φ : ∀ p, U p → ℝ} {δ : ℝ}

end Assembly

end RBM8D
