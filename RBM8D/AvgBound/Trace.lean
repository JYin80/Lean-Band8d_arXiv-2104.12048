import RBM8D.AvgBound.Defs
import RBM8D.LocalLaw.QTerm
import Batteries.Tactic.OpenPrivate

/-!
# The vanishing of `Q`-graphs in expectation

`Trace_E_Q`: `E Q_y F = 0` for a graph of the kinds of [II, Def 3.2] and ghost edges whose random
and labelled components all carry the label `Q_u` ([II, proof of Lemma 9.14]: `Q`-graphs vanish
after taking the expectation), at the data record with ghost factor `1`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Complex

namespace RBM8D

open Graphs

open private QTerm_polyMeas_prod QTerm_val_det
  from RBM8D.LocalLaw.QTerm

section PathSum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end PathSum

section GonSum

variable {d L : ℕ} [NeZero L]

end GonSum

section StochDomE

variable {Par : Type*} {Ω : Par → Type*} [∀ p, MeasurableSpace (Ω p)] {U : Par → Type*}

end StochDomE

/-! ## `E Q_u F = 0` for `Q`-graphs ([II, proof of Lemma 9.14]) -/

section EQ

/-- The data record with ghost factor `1` reads the same factor as the record itself on every
component that is not a ghost edge. -/
private lemma Trace_val_ghostOne {ι V : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : V → ι) (c : Comp V) (hc : c.kind ≠ .ghost) :
    Comp.val D.ghostOne σ c = Comp.val D σ c := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  cases κ with
  | ghost => exact absurd rfl hc
  | waved w => cases w <;> rfl
  | _ => rfl

/-- A ghost edge has the factor `1` on the data record with ghost factor `1`. -/
private lemma Trace_val_ghost {ι V : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : V → ι) (c : Comp V) (hc : c.kind = .ghost) : Comp.val D.ghostOne σ c = 1 := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  cases hc
  rfl

/-- **`E Q_u F = 0`** ([II, proof of Lemma 9.14]: `Q`-graphs vanish after taking the
expectation): let `z` have positive imaginary part, `S = S(W, L)` symmetric with nonnegative
entries, and `Γ` a graph whose components all have a kind of [II, Def 3.2] (`Comp.isTKind N`) or
are ghost edges without label, and which is a `Q`-graph with the label `Q_u`: some component
carries `Q_u` and every random or labelled component carries it. Then the expectation of the value
of `Γ` at the data record with ghost factor `1` (the record of the model, in which a ghost edge
has the value `1`) vanishes, for every labelling `e` of the external atoms. -/
theorem Trace_E_Q (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (z : ℂ)
    (hz : 0 < z.im) (hS : (Smat P.ψ W L).IsSymm) (hnn : ∀ x y, 0 ≤ Smat P.ψ W L x y)
    {k n N : ℕ} (Γ : Graph k n)
    (hΓ : ∀ c ∈ Γ.comps, c.isTKind N = true ∨ (c.kind = .ghost ∧ c.label = none))
    (u : Atom k n) (hQ : Γ.IsQGraphAt u) (e : Fin k → Zd d L) :
    ∫ ω, Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (fun ω => (rbmData d P Sig W L z ω).ghostOne) e ω
      ∂(gaussLaw (Smat P.ψ W L)) = 0 := by
  set S := Smat P.ψ W L with hSdef
  set D : Sample (Zd d L) → Data (Zd d L) := fun ω => (rbmData d P Sig W L z ω).ghostOne with hD
  have hlab : Γ.labels = [(.Q, u)] := QTerm_labels_eq Γ u hQ.1 hQ.2
  have hL := pqLaws_Pexp_poly S hS hnn
  -- a labelled component is not a ghost edge
  have hnog : ∀ c ∈ Γ.comps, c.label.isSome = true → c.kind ≠ .ghost := by
    intro c hc hl hg
    rcases hΓ c hc with h | ⟨-, h⟩
    · simp [Comp.isTKind, hg] at h
    · simp [h] at hl
  -- the graph without its ghost edges has the kinds of `T`-expansions
  set Γ' : Graph k n := ⟨Γ.comps.filter fun c => decide (c.kind ≠ .ghost), Γ.coeff⟩ with hΓ'
  have hΓ'k : Γ'.TKinds N := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨hc, hng⟩ := List.mem_filter.1 hc
    rcases hΓ c hc with h | ⟨h, -⟩
    · exact h
    · simp [h] at hng
  have hterm : ∀ σ : Atom k n → Zd d L,
      ∫ ω, Γ.termR ⟨Pexp S⟩ D σ ω ∂(gaussLaw S) = 0 ∧
        Integrable (fun ω => Γ.termR ⟨Pexp S⟩ D σ ω) (gaussLaw S) := by
    intro σ
    -- the labelled factors
    have hR : PolyMeas (QTerm_lab Γ u D σ) := by
      have heq : QTerm_lab Γ u D σ = fun ω =>
          (((Γ.comps.filter fun c => decide (c.label = some (.Q, u))).map
            (Comp.val (rbmData d P Sig W L z ω) σ))).prod := by
        funext ω
        unfold QTerm_lab
        congr 1
        refine List.map_congr_left fun c hc => ?_
        obtain ⟨hc, hl⟩ := List.mem_filter.1 hc
        exact Trace_val_ghostOne _ σ c (hnog c hc (by simp at hl; simp [hl]))
      rw [heq]
      refine QTerm_polyMeas_prod d P Sig W L z hz hS hnn Γ' hΓ'k σ _ fun c hc => ?_
      obtain ⟨hc, hl⟩ := List.mem_filter.1 hc
      refine List.mem_filter.2 ⟨hc, ?_⟩
      simpa using hnog c hc (by simp at hl; simp [hl])
    have hPR : PolyMeas (Pexp S (σ u) (QTerm_lab Γ u D σ)) := hL.adm_P (σ u) _ hR
    -- the coefficient does not depend on the sample
    have hdet : ∀ ω, QTerm_det Γ (D ω) σ = QTerm_det Γ (D 0) σ := by
      intro ω
      unfold QTerm_det
      have hm : (D ω).m = (D 0).m := rfl
      rw [hm]
      congr 1
      refine congrArg List.prod (List.map_congr_left fun c hc => ?_)
      obtain ⟨hc, hn⟩ := List.mem_filter.1 hc
      by_cases hg : c.kind = .ghost
      · rw [hD]; simp only
        rw [Trace_val_ghost _ σ c hg, Trace_val_ghost _ σ c hg]
      · have hrand : c.kind.isRandom = false := by
          by_contra h
          have := hQ.2 c hc (Or.inl (by simpa using h))
          simp [this] at hn
        rw [hD]; simp only
        rw [Trace_val_ghostOne _ σ c hg, Trace_val_ghostOne _ σ c hg]
        exact QTerm_val_det P Sig W L z ω 0 σ c hrand
    have hfun : (fun ω => Γ.termR ⟨Pexp S⟩ D σ ω) = fun ω =>
        QTerm_det Γ (D 0) σ * (QTerm_lab Γ u D σ ω - Pexp S (σ u) (QTerm_lab Γ u D σ) ω) := by
      funext ω
      rw [QTerm_termR_eq Γ u hlab S D σ ω, hdet ω]
    rw [hfun]
    refine ⟨?_, ((integrable_of_polyMeas S _ hR).sub (integrable_of_polyMeas S _ hPR)).const_mul _⟩
    rw [integral_const_mul]
    have := QTerm_E_Q S hS hnn (σ u) (QTerm_lab Γ u D σ) hR
    rw [this, mul_zero]
  unfold Graph.valR
  rw [integral_finsetSum _ fun s _ => (hterm (Sum.elim e s)).2]
  exact Finset.sum_eq_zero fun s _ => (hterm (Sum.elim e s)).1

end EQ

end RBM8D
