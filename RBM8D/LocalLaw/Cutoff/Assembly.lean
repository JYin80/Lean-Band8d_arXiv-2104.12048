module

public import RBM8D.LocalLaw.Cutoff.Bootstrap
public import RBM8D.LocalLaw.Cutoff.Hook
public import RBM8D.LocalLaw.Cutoff.Resample
public import RBM8D.LocalLaw.Cutoff.Moment
public import RBM8D.SelfEnergy.Assembly

@[expose] public section

/-!
# [II, Theorem 3.6] and [II, Lemma 3.9] from the cutoff bootstrap

* `localLawTExp_cutoff : localLawTExpStmt'`: [II, Theorem 3.6] = [I, Theorem 2.16] in the form
  `localLawTExpStmt'` (a family of `n`-th order `T`-expansions with `D`-th order error for every
  `D ≥ n + 2`), from the cutoff bootstrap `localLawTExp_cutoff_of`, the cutoff moment recursion
  `cutMoment_of`, the hook graph sum `hookGraphSum` and the Gaussian resampling bounds
  `cutImprove`, `cutPair`. It has no hypotheses.
* `Assembly.selfEnergyStep'`: [II, Lemma 3.9] = [I, Lemma 5.8] for `d ≥ 8` and every profile `P`
  (`selfEnergyStepStmt d (smatVar P)`): the bound part is `G13.selfEnergyStepEnd` at
  `localLawTExp_cutoff`, and the shape, the symmetry and the odd orders are
  `G13.selfEnergyStep_of_boundStep`.
-/

noncomputable section

open Complex

namespace RBM8D

open Graphs

/-- **[II, Theorem 3.6] = [I, Theorem 2.16]** in the form `localLawTExpStmt'`: for `d ≥ 8`, a
profile `P`, `c₀, c₁ > 0` with `c₀ + c₁ < 1`, `κ, ε, c₀ᵀ > 0` and an order `n`, if for every
`D ≥ n + 2` there is an `n`-th order `T`-expansion with `D`-th order error satisfying
`TRec.Def63G11`, then `|G_{xy}(z) − m(z) δ_{xy}|² ≺ B_{xy}` uniformly in `z ∈ 𝐃(κ, ε)` and
`x, y`, along `W → ∞` inside `adm(c₀, c₁)` with `L²/W² ≤ W^{(n−1)d/2 − c₀ᵀ}`; from the cutoff
bootstrap with the cutoff moment recursion. -/
theorem localLawTExp_cutoff : localLawTExpStmt' :=
  localLawTExp_cutoff_of cutImprove (cutMoment_of hookGraphSum cutImprove cutPair)

/-- **[II, Lemma 3.9] = [I, Lemma 5.8]** for `d ≥ 8` and every profile `P`: the self-energy step
`selfEnergyStepStmt d (smatVar P)`, with the local law `localLawTExp_cutoff`. -/
theorem Assembly.selfEnergyStep' (d : ℕ) (hd : 8 ≤ d) (P : Profile d) :
    selfEnergyStepStmt d (smatVar P) :=
  G13.selfEnergyStep_of_boundStep d P (G13.selfEnergyStepEnd localLawTExp_cutoff d hd P)

end RBM8D
