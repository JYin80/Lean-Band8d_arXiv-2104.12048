import RBM8D.AvgBound.Defs
import RBM8D.AvgBound.KeySum
import Mathlib.Algebra.Ring.GeomSum
import Batteries.Tactic.OpenPrivate

/-!
# The row sum of the kernel of [II, Lemma 9.5]

`brkSum_le`: for `W ≥ 1` and `L ≥ 2 W`, the row sum `Σ_y ⟨x − y⟩^{-d} ≤ 6^d (log₂(L/W) + 2)`
that enters the size estimates for the graphs with ghost edges ([II, (9.17)–(9.18)]).
-/

noncomputable section

open scoped BigOperators
open Filter

open private AvgKeySum_log AvgKeySum_brk_comm from RBM8D.AvgBound.KeySum

namespace RBM8D

open Graphs

/-! ## The row sum and the contraction -/

section RowSum

variable (d L W : ℕ) [NeZero L]

/-- The row sum of the kernel of [II, Lemma 9.5]: for `W ≥ 1` and `L ≥ 2 W`,
`Σ_y ⟨x − y⟩^{-d} ≤ 6^d (log₂(L/W) + 2)`. -/
theorem brkSum_le (hW : 1 ≤ W) (hWL : 2 * W ≤ L) (x : Zd d L) :
    ∑ y, (brk d L W x y ^ d)⁻¹ ≤ 6 ^ d * logF L W := by
  have := AvgKeySum_log d L W hW hWL x
  simpa only [AvgKeySum_brk_comm d L W x] using this

end RowSum

section Neumann

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Neumann

section Examples

end Examples

end RBM8D
