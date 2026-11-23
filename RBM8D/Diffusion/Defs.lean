module

public import RBM8D.MainDefs
public import RBM8D.Deloc.Defs
public import RBM8D.LocalLaw.Defs
public import RBM8D.TExp.Second
public import RBM8D.Bound.Chain
public import RBM8D.Bound.GraphAbs
public import RBM8D.Kernel.Circulant
public import RBM8D.Kernel.Propagator
public import RBM8D.Input.Entry

@[expose] public section

/-!
# Quantum diffusion: statements

[I, Theorem 1.5], [I, Corollary 1.6] and [I, Corollary 1.7] as one joint statement for the law
`rbmLaw` of [I, Assumptions 1.1–1.2] on `Z_L^d`, with the objects of [I, §1.2–§1.3]: the
expectations `E T_{xy}` and `E |G_{xy}|²`, the self-energy correction `Σ̃^{(M)}`, the renormalized
diffusive matrix `Θ^{(M)}` of [I, (1.23)], the effective diffusion matrix `𝒟_eff^{(M)}`, and the
Fourier sums of [I, (1.35)–(1.36)]. The intermediate statements follow the proof of
[I, Theorem 1.5] in [I, §8] ((8.14)–(8.20)) and the computation of [I, §1.3] ((1.30)–(1.36)).

* The self-energies `Σ_l` form one family before `M`; each `Σ_l` is the value of a deterministic
  graph expansion in `m`, `S`, `S^±`, `Θ` ([I, Def 2.13 (i)]) wherever the variance matrix of the
  model is symmetric ([I, Assumption 1.1] in the regime of the model).
* `D_eff^{(M)}` and `𝒟_l` sum over `x ∈ Z_L^d`, and [I, (1.32)] carries the minus sign.
* [I, Corollary 1.7] is stated with `|p| ≤ W^{-1-δ}`, `η ≤ W^{-δ}` and the hypothesis
  `W^M ≥ L⁴` inside the quantifiers over `(W, L)`.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Complex Matrix
open scoped BigOperators

namespace RBM8D

open Graphs

/-! ## Objects of [I, §1.2–§1.3] -/

/-! ## The target statements -/

/-! ## The rooted `T`-equation and the local correction ([I, (8.14)–(8.20)]) -/

/-- The root test: a plain `Θ` edge whose first end is `⊗` ([II, Def 3.3 (4)], `Θ_{a x}`). -/
def rootTest {n : ℕ} (c : Comp (Atom 3 n)) : Bool :=
  decide (c.kind = .theta []) && decide (c.x = .inl 0)

/-- The graph `𝒢_{x, b₁ b₂}` of [II, Def 3.3 (4)] of a graph `Σ_x Θ_{a x} 𝒢_{x, b₁ b₂}`: the first
plain `Θ` edge leaving `⊗` is removed, and its second end becomes the external atom `x`
(`Graph.rootGraph`); a graph without such an edge is returned unchanged. -/
def rootRest {n : ℕ} (Γ : Graph 3 n) : Σ n' : ℕ, Graph 3 n' :=
  match Γ.comps.find? rootTest with
  | some c => (Γ.dropComp (Γ.comps.findIdx rootTest)).rootGraph c.y
  | none => ⟨n, Γ⟩

/-- No `P`/`Q` label of the graph sits at `⊗`: with `ThetaRooted`, the graph is
`Σ_x Θ_{a x} 𝒢_{x, b₁ b₂}` with `𝒢` not reading `a` ([II, Def 3.3 (4)]). -/
def noRootLabel {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∀ c ∈ Γ.comps, c.label.map Prod.snd ≠ some (.inl 0)

/-- `Σ_{g ∈ E} (𝒢_g)_{x, b b}`: the sum of the rooted graphs of the formal sum `E` at the external
atoms `x` and `b₁ = b₂ = b`. -/
def gammaVal {Ω ι : Type} [Fintype ι] [DecidableEq ι] (E : Expansion 3) (PF : PFamily Ω ι)
    (Dt : Ω → Data ι) (x b : ι) (ω : Ω) : ℂ :=
  (E.map fun g => (rootRest g.2).2.valR PF Dt ![x, b, b] ω).sum

/-- `Y'_{x b} = m δ_{x b} Ḡ_{b b} + (Γ_R + Γ_A + Γ_Q + Γ_Err)_{x, b b}`: the factor after the root
`Θ` of the leading term and of the graphs of `R`, `A`, `Q`, `Err` of the `T`-equation `𝒬`
([I, (8.14)], with `b₁ = b₂ = b`). -/
def yRoot {Ω ι : Type} [Fintype ι] [DecidableEq ι] (𝒬 : TEqRec) (PF : PFamily Ω ι)
    (Dt : Ω → Data ι) (x b : ι) (ω : Ω) : ℂ :=
  (if x = b then (Dt ω).m * star ((Dt ω).Gm ∅ b b) else 0) +
    gammaVal (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) PF Dt x b ω

/-- The data record of the Gaussian model of [I, Assumption 1.1] at the variance matrix `S`, with
the self-energy matrices `Σ_l` of `Sig` on the deterministic record of `S`. -/
def modelDataSig {ι : Type} [Fintype ι] [DecidableEq ι] (Sig : ℕ → Expansion 2)
    (S : Matrix ι ι ℝ) (z : ℂ) (ω : Sample ι) : Data ι :=
  { modelData S z hmat ω with Sig := sigMat Sig S z }

/-- `E[F]` under the law of [I, Assumption 1.1] on `Z_L^d`. -/
def expC (d : ℕ) (P : Profile d) (W L : ℕ) [NeZero L] (F : Sample (Zd d L) → ℂ) : ℂ :=
  ∫ ω, F ω ∂(rbmLaw d P (sizeOf W L))

/-- The local correction of [I, (8.16)] for the `T`-equation `𝒬`, on the model with the
self-energies `Sig`: `m δ_{x b} E(Ḡ_{b b} − m̄)` plus `E Γ` over `R` and over the graphs of `A` in
which `⊕` and `⊖` lie in one dotted block, at `(x, b, b)`. -/
def corrMat (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (𝒬 : TEqRec) (W L : ℕ) [NeZero L]
    (z : ℂ) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun x b =>
    msc z * (if x = b then expC d P W L (fun ω => star (green (hmat ω) z b b) - star (msc z))
      else 0) +
    expC d P W L (gammaVal (𝒬.R ++ 𝒬.A.filter (fun g => g.2.pmBlockB))
      ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b)

/-- The error of [I, (8.15), (8.20)] for the `T`-equation `𝒬`, on the model with the
self-energies `Sig`: `E Γ` over the other graphs of `A` and over `Err`, at `(x, b, b)`. -/
def errMat (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (𝒬 : TEqRec) (W L : ℕ) [NeZero L]
    (z : ℂ) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun x b =>
    expC d P W L (gammaVal (𝒬.A.filter (fun g => !g.2.pmBlockB) ++ 𝒬.Err)
      ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b)

/-! ## Intermediate statements -/

/-- The self-energies of [I, Theorem 1.5] from the induction: a family `Sig` with `H(n)` for every
`n ≥ 2` (for the variance family `smatVar P`) gives a family `Sig` with `H(n)` for every `n ≥ 2`
whose orders `l ≥ 4` all have the shape of self-energies, and matrices `Σ_l` with `SigmaOf`. -/
def selfEnergyFamilyStmt : Prop :=
  ∀ (d : ℕ) (P : Profile d) (Strat : ℕ → ℕ → TRec → TEqRec), jointHStmt d (smatVar P) Strat →
    ∃ Sig : ℕ → Expansion 2, (∀ n, 2 ≤ n → HWith d (smatVar P) Strat Sig n) ∧
      ∃ Sg : SigmaFam d, SigmaOf d P Sig Sg

/-- [I, (1.24), (1.26), (1.27)], the invertibility of `1 − |m|² S (1 + Σ̃^{(M)})`
([I, (8.18)–(8.19)]), and the change of order `M ≤ N` of `Θ^{(·)}` and of `(1 − X |m|² S)⁻¹`:
`|Θ^{(N)}_{xy} − Θ^{(M)}_{xy}| ≤ L^τ W^{−(M+1)d/2}` and the same for `(1 − X|m|²S)⁻¹`. In (1.26)
the diagonal term `L^τ W^{−(l−2)d/2} 1_{x=0}` is added, as in `SelfEnergyBound`. -/
def thetaMStmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ → 0 < ε →
    ∀ Sig : ℕ → Expansion 2, (∀ l, 4 ≤ l → Even l → IsSelfEnergy d (smatVar P) Sig l) →
    ∀ Sg : SigmaFam d, SigmaOf d P Sig Sg → ∀ M N : ℕ, M ≤ N → ∀ τ : ℝ, 0 < τ →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ → ∀ z ∈ specDom κ ε W L,
        IsUnit (1 - amat (Smat P.ψ W L) z * (1 + sigTildeM Sg M W L z)) ∧
        (∀ x y : Zd d L, ‖thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z x y‖ ≤
          (L : ℝ) ^ τ * bB d L W x y) ∧
        (∀ l, 4 ≤ l → l ≤ M → ∀ x : Zd d L, ‖Sg l W L z 0 x‖ ≤
          (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
            (if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)) ∧
        (∀ l, 4 ≤ l → l ≤ M → ‖∑ x : Zd d L, Sg l W L z 0 x‖ ≤
          (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) ∧
        (∀ x y : Zd d L, ‖(thetaM (Smat P.ψ W L) (1 + sigTildeM Sg N W L z) z -
            thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z) x y‖ ≤
          (L : ℝ) ^ τ * (W : ℝ) ^ (-(((M : ℝ) + 1) * d / 2))) ∧
        (∀ x y : Zd d L, ‖(resM (Smat P.ψ W L) (1 + sigTildeM Sg N W L z) z -
            resM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z) x y‖ ≤
          (L : ℝ) ^ τ * (W : ℝ) ^ (-(((M : ℝ) + 1) * d / 2)))

/-- The rooted `T`-equation ([I, (8.14)] before the expectation, [II, Def 3.3 (4)]): for a
`T`-equation `𝒬` without `P`/`Q` labels at `⊗` and every record with the model relations,
`T_{a, b b} = Σ_x Θ_{a x} (Y'_{x b} + (Σ̃^{(n)} T)_{x, b b})`, at every sample. -/
def rootedTEqStmt : Prop :=
  ∀ (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒬 : TEqRec), 𝒬.IsTEqStruct Sig n D →
    (∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2) →
  ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (Dt : Ω → Data ι),
    modelAdm Ω ι PF Dt → (∀ ω, SigConsistent Sig n (Dt ω)) → ∀ (a b : ι) (ω : Ω),
      tGraph.valR PF Dt ![a, b, b] ω = ∑ x, (Dt ω).Theta a x *
        (yRoot 𝒬 PF Dt x b ω +
          ∑ y, sigTilde n 𝒬.SigN (Dt ω) x y * tGraph.valR PF Dt ![y, b, b] ω)

/-- The identity `|G_{a b}|² − T_{a, b b} = Y'_{a b} + (Σ̃^{(n)} T)_{a, b b}` at every sample, for
the Gaussian model at every real symmetric `S ≥ 0` with row sums `1`, singular or not: the rooted
`T`-equation with the root `Θ` removed, without an inverse of `S` ([I, Corollary 1.6], the case
of a singular `S`). -/
def singularIdStmt : Prop :=
  ∀ (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒬 : TEqRec), 𝒬.IsTEqStruct Sig n D →
    (∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2) →
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ), S.IsSymm →
    (∀ x y, 0 ≤ S x y) → (∀ x, ∑ y, S x y = 1) → 0 < z.im → ∀ (a b : ι) (ω : Sample ι),
      ((‖green (hmat ω) z a b‖ ^ 2 : ℝ) : ℂ) -
          tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![a, b, b] ω =
        yRoot 𝒬 ⟨Pexp S⟩ (modelDataSig Sig S z) a b ω +
          ∑ y, sigTilde n 𝒬.SigN (modelDataSig Sig S z ω) a y *
            tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![y, b, b] ω

/-- The expectation of the diagonal resolvent entries: `|E G_{bb} − m| ≤ W^τ W^{−3d/2}`, from the
local law (the diagonal term of [I, (8.16)]). -/
def diagMeanStmt : Prop :=
  LocalLawStmt → ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ,
    0 < c₀ → 0 < c₁ → 0 < κ → 0 < ε → ∀ τ : ℝ, 0 < τ →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ b : Zd d L,
          ‖expC d P W L (fun ω => green (hmat ω) z b b) - msc z‖ ≤
            (W : ℝ) ^ τ * (W : ℝ) ^ (-(3 * (d : ℝ) / 2))

/-- The error of the `n`-th order `T`-equation ([I, (8.17), (8.20)]): `|E(Γ_A + Γ_Err)_{x, bb}| ≤
W^τ W^{−(n−1)d/2}` and `Σ_x B_{a x} |E(Γ_A + Γ_Err)_{x, bb}| ≤ W^τ W^{−(n+1)d/2}`. -/
def errBoundStmt : Prop :=
  LocalLawStmt → ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ,
    0 < c₀ → 0 < c₁ → 0 < κ → 0 < ε →
    ∀ (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒬 : TEqRec), 4 ≤ n → n + 2 ≤ D →
      𝒬.IsTEqStruct Sig n D → (∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2) →
      SelfEnergiesUpTo d (smatVar P) Sig n → ∀ τ : ℝ, 0 < τ →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ a b : Zd d L,
          ‖errMat d P Sig 𝒬 W L z a b‖ ≤ (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 1) * d / 2)) ∧
          ∑ x : Zd d L, bB d L W a x * ‖errMat d P Sig 𝒬 W L z x b‖ ≤
            (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) + 1) * d / 2))

/-- [I, (1.28)] for the local correction of the `n`-th order `T`-equation:
`|𝒢_{x b}| ≤ L^τ B_{x b}^{3/2}`, off the diagonal by [I, (6.20)] and on the diagonal through
`singularIdStmt` and the local law. -/
def localCorrStmt : Prop :=
  LocalLawStmt → ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ,
    0 < c₀ → 0 < c₁ → 0 < κ → 0 < ε →
    ∀ (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒬 : TEqRec), 4 ≤ n → n + 2 ≤ D →
      𝒬.IsTEqStruct Sig n D → (∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2) →
      SelfEnergiesUpTo d (smatVar P) Sig n → ∀ τ : ℝ, 0 < τ →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ x b : Zd d L,
          ‖corrMat d P Sig 𝒬 W L z x b‖ ≤ (L : ℝ) ^ τ * bB d L W x b ^ ((3 : ℝ) / 2)

/-- Translation invariance of the model where `S_{W,L}` is symmetric: `E T`, `E |G|²`, the local
correction and the error of a `T`-equation are translation invariant. -/
def modelTransInvStmt : Prop :=
  ∀ (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (𝒬 : TEqRec) (W L : ℕ) [NeZero L] (z : ℂ),
    (Smat P.ψ W L).IsSymm → 0 < z.im →
      TransInv (Matrix.of fun x y => (expT d P W L z x y : ℂ)) ∧
      TransInv (Matrix.of fun x y => (expG2 d P W L z x y : ℂ)) ∧
      TransInv (corrMat d P Sig 𝒬 W L z) ∧ TransInv (errMat d P Sig 𝒬 W L z)

/-- [I, (1.33)] in quantified form: `Θ̂^{(M)}(p) = r(E)(1 + u)/(η + W² p·𝒟_eff^{(M)} p + e)` with
`|u| ≤ C(η + W²|p|²)`, `|e| ≤ C(η² + W^{−d+τ}η + W³|p|³)` and a nonzero denominator, for
`|E| < 2 − κ`, `η ∈ [W²/L^{2−ε}, W^{−δ}]`, `|p| ≤ W^{−1−δ}`. -/
def symbolThetaMStmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ → 0 < ε →
    ∀ Sig : ℕ → Expansion 2, (∀ l, 4 ≤ l → Even l → IsSelfEnergy d (smatVar P) Sig l) →
    ∀ Sg : SigmaFam d, SigmaOf d P Sig Sg → ∀ M : ℕ, ∀ δ τ : ℝ, 0 < δ → 0 < τ →
      ∃ C : ℝ, ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ E η : ℝ, |E| < 2 - κ → (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ η → η ≤ (W : ℝ) ^ (-δ) →
      ∀ k : Zd d L, ‖zfreq k‖ ≤ (W : ℝ) ^ (-1 - δ) →
        ∃ u e : ℂ, ‖u‖ ≤ C * (η + (W : ℝ) ^ 2 * ‖zfreq k‖ ^ 2) ∧
          ‖e‖ ≤ C * (η ^ 2 + (W : ℝ) ^ (-(d : ℝ) + τ) * η + (W : ℝ) ^ 3 * ‖zfreq k‖ ^ 3) ∧
          (η : ℂ) + qform W k (diffEff P Sg M W L (E + η * I)) + e ≠ 0 ∧
          symbol (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L (E + η * I)) (E + η * I)) k =
            (rE E : ℂ) * (1 + u) / ((η : ℂ) + qform W k (diffEff P Sg M W L (E + η * I)) + e)

/-- The joint statement from the local law [I, Theorem 1.4] and the self-energies of every order
([II, Theorem 3.7, Corollary 3.8, Lemma 3.9]). -/
def quantumDiffusion_ofStmt : Prop :=
  LocalLawStmt →
    (∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∃ Strat : ℕ → ℕ → TRec → TEqRec,
      jointHStmt d (smatVar P) Strat) →
    quantumDiffusionStmt

/-! ## Deterministic identities -/

/-- The symbol of `(1 − K X)⁻¹ K` for translation-invariant `K`, `X` with `1 − K X` invertible is
`K̂(p) / (1 − K̂(p) X̂(p))` ([I, (1.31)] and [I, (1.33)] before the expansion in `p`). -/
theorem G16.symbol_inv_mul {d L : ℕ} [NeZero L] (K X : Matrix (Zd d L) (Zd d L) ℂ)
    (hK : TransInv K) (hX : TransInv X) (hU : IsUnit (1 - K * X)) (k : Zd d L) :
    symbol (Ring.inverse (1 - K * X) * K) k = symbol K k / (1 - symbol K k * symbol X k) := by
  have h0 : zchar k (0 : Zd d L) = 1 := by simp [zchar]
  have hsym : ∀ M : Matrix (Zd d L) (Zd d L) ℂ, symbol M k = (M *ᵥ zchar k) 0 := by
    intro M
    simp [symbol, Matrix.mulVec, dotProduct]
  have hUv : (1 - K * X) *ᵥ zchar k = (1 - symbol K k * symbol X k) • zchar k := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, mulVec_zchar X hX,
      Matrix.mulVec_smul, mulVec_zchar K hK, smul_smul, sub_smul, one_smul, mul_comm]
  obtain ⟨u, hu⟩ := hU
  have hinv : Ring.inverse (1 - K * X) * (1 - K * X) = 1 := by
    rw [← hu, Ring.inverse_mul_cancel _ u.isUnit]
  have hne : 1 - symbol K k * symbol X k ≠ 0 := by
    intro h
    have h1 := congrArg (fun v => (Ring.inverse (1 - K * X) *ᵥ v) 0) hUv
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, h, zero_smul,
      Matrix.mulVec_zero] at h1
    rw [h0] at h1
    exact one_ne_zero (h1.trans rfl)
  have hIv : Ring.inverse (1 - K * X) *ᵥ zchar k = (1 - symbol K k * symbol X k)⁻¹ • zchar k := by
    have h1 := congrArg (fun v => Ring.inverse (1 - K * X) *ᵥ v) hUv
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_smul] at h1
    rw [eq_comm]
    conv_lhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hsym, ← Matrix.mulVec_mulVec, mulVec_zchar K hK, Matrix.mulVec_smul, hIv, smul_smul]
  simp [h0, div_eq_mul_inv]

/-- `(1 − X A)⁻¹ = 1 + X (1 − A X)⁻¹ A` in a ring, when `1 − A X` is invertible: the inverse of
`1 − (1 + Σ̃^{(M)})|m|² S` is `1 + (1 + Σ̃^{(M)}) Θ^{(M)}`, with no inverse of `S`. -/
theorem G16.inverse_one_sub_mul {R : Type*} [Ring R] (A X : R) (hU : IsUnit (1 - A * X)) :
    Ring.inverse (1 - X * A) = 1 + X * Ring.inverse (1 - A * X) * A := by
  obtain ⟨u, hu⟩ := hU
  have h1 : (1 - A * X) * Ring.inverse (1 - A * X) = 1 := by
    rw [← hu, Ring.mul_inverse_cancel _ u.isUnit]
  have h2 : Ring.inverse (1 - A * X) * (1 - A * X) = 1 := by
    rw [← hu, Ring.inverse_mul_cancel _ u.isUnit]
  set v := Ring.inverse (1 - A * X)
  have e1 : (1 - X * A) * (1 + X * v * A) = 1 := by
    have : (1 - X * A) * (1 + X * v * A) = 1 - X * A + X * ((1 - A * X) * v) * A := by
      noncomm_ring
    rw [this, h1]
    noncomm_ring
  have e2 : (1 + X * v * A) * (1 - X * A) = 1 := by
    have : (1 + X * v * A) * (1 - X * A) = 1 - X * A + X * (v * (1 - A * X)) * A := by
      noncomm_ring
    rw [this, h2]
    noncomm_ring
  have hunit : IsUnit (1 - X * A) := ⟨⟨_, _, e1, e2⟩, rfl⟩
  calc Ring.inverse (1 - X * A) = Ring.inverse (1 - X * A) * ((1 - X * A) * (1 + X * v * A)) := by
        rw [e1, mul_one]
    _ = 1 + X * v * A := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul]

end RBM8D
