import RBM8D.LocalLaw.Defs
import RBM8D.Graph.DotBlocks

/-!
# From [II, Def 6.3] to the clauses read at `𝔟₁ = 𝔟₂`

The clauses `TRec.Def63` of [II, Def 6.3] in the block reading give the clauses `TRec.Def63G11`
that [II, (8.18)–(8.24)] read at `𝔟₁ = 𝔟₂`: only diffusive edges at `⊗` and dot excess `0` give
only diffusive edges at `⊗` and dotted edges forming a forest; the order bound for `⊕`, `⊖` in one
dotted block on `R` and `A` and the rooting at the external atoms on `A`, `Q`, `Err` are clauses
of `TRec.Def63`.
-/

namespace RBM8D.Graphs

/-- [II, Def 6.3] in the block reading (`TRec.Def63`) gives the clauses of [II, Def 6.3] read by
[II, (8.18)–(8.24)] at `𝔟₁ = 𝔟₂` (`TRec.Def63G11`). -/
theorem TRec.def63G11_of_def63 (𝒯 : TRec) : 𝒯.Def63 → 𝒯.Def63G11 := by
  rintro ⟨-, h2, -, h4, -, -, h7, -⟩
  exact ⟨fun g hg => ⟨(h2 g hg).1, (g.2.dotsAcyclic_iff_dotExcess_eq_zero).2 (h2 g hg).2.1⟩,
    h4, h7⟩

section Instances

set_option maxRecDepth 100000

end Instances

end RBM8D.Graphs
