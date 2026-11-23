module

public import RBM8D.Graph.Value

@[expose] public section

/-!
# Value lemmas

The value of a label-free graph as a random variable ([I, Def 2.9]): `Graph.valR_of_labelFree`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Relabelling -/

/-- A graph without `P`/`Q` labels has the value `Graph.val`, at every `ω`. -/
theorem Graph.valR_of_labelFree :
  ∀ (k n : ℕ) (Γ : Graph k n) (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) (e : Fin k → ι), Γ.LabelFree → Γ.valR PF D e = fun ω => Γ.val (D ω) e := by
  intro k n Γ Ω ι _ _ PF D e h
  funext ω
  have hl : Γ.labels = [] := by
    have : Γ.comps.filterMap Comp.label = [] := List.filterMap_eq_nil_iff.2 h
    simp [Graph.labels, this]
  have hf : Γ.comps.filter (fun c => c.label.isNone) = Γ.comps :=
    List.filter_eq_self.2 fun c hc => by simp [h c hc]
  simp only [Graph.valR, Graph.termR, Graph.val, Graph.term, hl, hf]
  simp

section Instances

open Complex

end Instances

end RBM8D.Graphs
