import RBM8D.LocalLaw.Defs
import RBM8D.LocalLaw.Eta1
import RBM8D.LocalLaw.Continuity
import RBM8D.LocalLaw.Entrywise
import RBM8D.LocalLaw.Moment
import RBM8D.LocalLaw.QTermOf
import RBM8D.LocalLaw.LabelPaths
import RBM8D.LocalLaw.LabelRemoval
import RBM8D.Prob.Net

/-!
# The local law from a T-expansion with the error order chosen after the moment index

[II, Def 3.2] reads "a large constant `D > n`", and the steps of [II, Theorem 3.6] need `D` large
in terms of the moment index `q` ([II, (9.30)]).

* `localLawTExpStmt'`: [II, Theorem 3.6] from a family of `n`-th order `T`-expansions with
  `D`-th order error, one for every `D ≥ n + 2`.
-/

open MeasureTheory Filter Complex

namespace RBM8D

open Graphs

/-! ## The statements -/

/-- **[I, Theorem 2.16] = [II, Theorem 3.6]** from a family of `T`-expansions: for `d ≥ 8`, a
profile `P`, constants `c₀, c₁ > 0` with `c₀ + c₁ < 1`, `κ, ε > 0`, the constant `c₀ᵀ > 0` of
[II, (3.15)] and an order `n`, if for every `D ≥ n + 2` there are `Σ` and an `n`-th order
`T`-expansion `𝒯` with `D`-th order error ([II, Def 3.2], [II, Def 6.3]) satisfying the clauses
`TRec.Def63G11`, then along `W → ∞` inside `adm(c₀, c₁)` with
`L²/W² ≤ W^{(n−1)d/2 − c₀ᵀ}`, `|G_{xy}(z) − m(z) δ_{xy}|² ≺ B_{xy}` uniformly in
`z ∈ 𝐃(κ, ε)` and `x, y`. -/
def localLawTExpStmt' : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → 0 < c₀T → ∀ n : ℕ,
    (∀ D : ℕ, n + 2 ≤ D → ∃ (Sig : ℕ → Expansion 2) (𝒯 : TRec),
      IsTExpansion d (smatVar P) Sig n D 𝒯 ∧ 𝒯.Def63G11) →
      StochDom (llFilter d n c₀ c₁ c₀T) sizeW (rbmLaw d P)
        (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
        (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
        (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2)

end RBM8D
