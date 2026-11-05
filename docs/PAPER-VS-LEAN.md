# The papers and the Lean proof: differences

**Papers.** F. Yang, H.-T. Yau and J. Yin, *Delocalization and quantum diffusion of random band matrices in high
dimensions I: Self-energy renormalization* (arXiv:2104.12048), and *II: T-expansion* (arXiv:2107.05795), in the revised
versions of this repository: [I] = `paper/I/band_Part_I.pdf` (TeX `paper/I/band_Part_I.tex`), [II] = `paper/II/arxiv.pdf`
(TeX `paper/II/arxiv.tex`). Theorem, section and equation numbers below are those printed in these PDFs, unless a number is
marked "arXiv". The revised papers keep the structure and the numbering of the arXiv versions except in the places listed in §4.

**Lean.** The library is `RBM8D` (Lean 4 `v4.36.0-rc1`, Mathlib `v4.36.0-rc1`). Its declarations are in the namespace `RBM8D`,
and the graph syntax and the `T`-expansions are in `RBM8D.Graphs`. Names below are written without the prefix `RBM8D.`
(so `Graphs.SelfEnergyShape` is `RBM8D.Graphs.SelfEnergyShape`). Names such as `Ring.inverse`, `MeasureTheory.Measure.pi`
or `ProbabilityTheory.gaussianReal` are from Mathlib. Lean text quoted below is copied from the source files, without
docstrings.

---

## 1. What is proved

### 1.1 The three Lean theorems

The five main results of [I] are three theorems in `RBM8D/Endpoints.lean`. [I, Theorem 1.5], [I, Corollary 1.6] and
[I, Corollary 1.7] form one statement, because the two corollaries are stated "with the same `Σ_l` and `𝒢^{(M)}` as in
Theorem 1.5".

| Paper | Lean statement (file) | Lean theorem | Hypotheses other than parameters |
|---|---|---|---|
| [I, Theorem 1.3], (1.12) and (1.13) | `Thm13Stmt` (`RBM8D/Deloc/Thm13.lean`) | `thm13 : Thm13Stmt` | none |
| [I, Theorem 1.4], (1.19) | `LocalLawStmt` (`RBM8D/Deloc/Defs.lean`) | `localLaw : LocalLawStmt` | none |
| [I, Theorem 1.5], (1.22)–(1.28); [I, Corollary 1.6], (1.29); [I, Corollary 1.7], (1.35)–(1.36) | `quantumDiffusionStmt`, with `SigmaOf`, `thm15Concl`, `cor17Concl` (`RBM8D/Diffusion/Defs.lean`) | `quantumDiffusion : quantumDiffusionStmt` | none |

The statements unfold to the definitions in Appendix A: the model (`Profile`, `Smat`, `fWL`, `rbmLaw`, `gaussLaw`, `hmat`),
the domains (`adm`, `specDom`), the bound `bB`, the resolvent `green`, the semicircle transform `msc`, and, for
quantum diffusion, `expT`, `expG2`, `thetaM`, `resM`, `sigTildeM`, `diffEff`, `qform`, `symbol`, `zchar`, `zfreq`, and the
self-energy predicate `Graphs.SelfEnergyShape` with the graph value `Graphs.sigMat`.

**Axioms.** `#print axioms` of the three theorems prints `[propext, Classical.choice, Quot.sound]` for each (output in
§1.5), so no `sorry` and no declared axiom enters their proofs. The three theorems have no hypotheses: every result that the papers
quote from other works is proved in the library (§3, last entries).

### 1.2 The model

- **Sizes.** A size is `p : SizeL`, a pair `(W, L) = (p.1.1, p.1.2)` of natural numbers with `L ≠ 0`. The lattice
  `Z_L^d` of [I, (1.2)] is `Zd d L = Fin d → ZMod L`; the periodic `ℓ^∞` distance `‖x − y‖_L` is
  `zdistInf d L (x − y)`, and `N = L^d` is the cardinality of `Zd d L`.
- **Profile** ([I, Assumption 1.2]). A term `P : Profile d` is a real Schwartz function `ψ` on `ℝ^d` (field `ψ`, type
  `𝓢(EuclideanSpace ℝ (Fin d), ℝ)`, which is (iii)) with `ψ(−p) = ψ(p)`, `ψ(0) = 1`, `|ψ| ≤ 1` (i), and
  `ψ(p) ≤ max(1 − c_ψ|p|², 1 − c_ψ)` with `c_ψ > 0` (ii); and two conditions on `f_{W,L}`: `f_{W,L} ≥ 0` for all
  `W ≥ 1` and `L` (field `f_nonneg`), and `f_{W,L}(−x) = f_{W,L}(x)` for `(W, L) ∈ adm(c₀, c₁)` and `W ≥ W₀(c₀, c₁)`, for
  all `c₀, c₁ > 0` (field `f_symm`).
- **Variance profile** ([I, (1.5)–(1.6)]). `fWL ψ W L x = Z_{W,L}^{-1} Re[(2π)^{-d} ∫ ψ(Wp) e^{i p·[x]_L} dp]`, with
  `[x]_L ∈ (−L/2, L/2]^d` (`zrep`, via `ZMod.valMinAbs`) and `Z_{W,L} = Σ_x` of the unnormalized function (`ZWL`). The
  integral is real when `ψ` is symmetric (`profInt_im`). `Smat ψ W L` is `S_{xy} = f_{W,L}(x − y)`.
- **Matrix and law** ([I, Assumption 1.1]). The sample space `Sample (Zd d L)` has one real coordinate for each diagonal
  entry and two (real and imaginary part) for each unordered off-diagonal pair. `gaussLaw S` is the product of centred
  real Gaussians with variance `s_xx` on the diagonal and `s_xy/2` for the real and imaginary parts, and `hmat ω` is the
  Hermitian matrix with these entries (`h_yx = conj h_xy`, `h_xx` real). `rbmLaw d P p = gaussLaw (Smat P.ψ W L)`. This
  is (1.4).
- **Domains and bounds.** `adm c₀ c₁ = {(W, L) : L^{c₁} ≤ W ≤ L^{1−c₀}}`. `specDom κ ε W L` is the set of `z` with
  `|Re z| < 2 − κ` and `W²/L^{2−ε} ≤ Im z ≤ 1`, the spectral domain of [I, Theorems 1.4 and 1.5]. `bB d L W x y` is
  `B_{xy} = W^{-2}(‖x − y‖_L + W)^{-(d−2)}` of (1.18).
- **Resolvent.** `green H z = (H − z)^{-1}` (Mathlib's matrix inverse; `H − z` is invertible for Hermitian `H` and
  `Im z ≠ 0`). `msc z` is the root of `m² + zm + 1 = 0` with `Im m > 0` when `Im z > 0`, which is `m(z)` of (1.15).
  `entryErr G m x y = G_{xy} − m δ_{xy}`.
- **Probabilities and expectations.** `rbmLaw d P p S` for a set `S` of samples is the measure of `S` as an outer
  measure; no measurability is needed. `expT` and `expG2` are the Bochner integrals of `T_{xy}` ((1.21), `Tvar`) and of
  `|G_{xy}|²`.

### 1.3 Plain-language reading of the three statements

**`Thm13Stmt`** ([I, Theorem 1.3]). For every `d ≥ 8`, every profile `P`, all `c₀, c₁, κ > 0`, all `γ ∈ (0, 1]`,
`K > 1` and all `τ, D > 0` there is `L₀` such that, for every size `(W, L)` and every real `ℓ` with `L ≥ L₀`,
`W ≤ ℓ ≤ L^{1−c₀}`, `L^{c₁} ≤ W` and `W ≤ L`:
1. the probability that there is an orthonormal eigenbasis `(u_α, λ_α)_α` of `H` (`IsOrthoEigenbasis`) with
   `|𝓑_{γ,K,ℓ}|/N > W^τ(ℓ²/L² + W^{−d/2})` is at most `L^{−D}`, where `𝓑_{γ,K,ℓ}` is `locSetB`, the set of `α` with
   `λ_α ∈ (−2+κ, 2−κ)` and `min_{x₀} Σ_x |u_α(x)|² exp((‖x − x₀‖_L/ℓ)^γ) ≤ K`;
2. the probability that there are `λ ∈ (−2+κ, 2−κ)` and a vector `u` with `Σ_x |u(x)|² = 1`, `Hu = λu` and
   `|u(x)| > W^{1+τ}/L` for some `x` is at most `L^{−D}`.

**`LocalLawStmt`** ([I, Theorem 1.4]). For every `d ≥ 8`, `P`, all `c₀, c₁, κ > 0` and all `ε, τ, D > 0` there is `L₀`
such that, for every size `(W, L) ∈ adm(c₀, c₁)` with `L ≥ L₀` and all `x, y ∈ Z_L^d`, the probability that there are
`E ∈ (−2+κ, 2−κ)` and `η ∈ [W²/L^{2−ε}, 1]` with `|G_{xy}(E + iη) − m(E + iη)δ_{xy}|² > W^τ B_{xy}` is at most `L^{−D}`.

**`quantumDiffusionStmt`** ([I, Theorem 1.5, Corollaries 1.6, 1.7]). For every `d ≥ 8`, `P` and all `c₀, c₁, κ, ε > 0`
there is a family of matrices `Σ_l(W, L, z)` on `Z_L^d` (`Sg : SigmaFam d`), and for every order `M ∈ ℕ` a family
`𝒢^{(M)}(W, L, z)` (`Gc : LocCorr d`), such that:
- (`SigmaOf`) there are formal graph sums `Sig l` such that for every `l ≥ 4`: `Sig l` has the shape of
  [I, Definition 2.13 (i)] (`Graphs.SelfEnergyShape l`: every graph is normal regular, its dotted edges form a forest,
  it is deterministic, of scaling order `l`, and doubly connected when `x` and `y` are read as internal atoms);
  `Σ_l(W, L, z)` is the value of `Sig l` on `m(z)`, `S`, `S^±`, `Θ` and the lower orders (`Graphs.sigMat`) whenever
  `S_{W,L}` is symmetric; and (1.25) holds for all `W, L, z, x, a`;
- (`thm15Concl`) for every `τ > 0` there is `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)` and
  `z ∈ specDom κ ε W L`: the matrix `1 − |m|²S(1 + Σ̃^{(M)})` is invertible, `Σ̃^{(M)} = Σ_{l=4}^{M} Σ_l`
  (`sigTildeM`); `|Θ^{(M)}_{xy}| ≤ L^τ B_{xy}` (1.24), with `Θ^{(M)}` of (1.23) (`thetaM`); (1.26) and (1.27) for
  `4 ≤ l ≤ M`; and `|𝒢^{(M)}_{xy}| ≤ L^τ B_{xy}^{3/2}` (1.28). Moreover there are `C` and `L₀` such that for the same
  `(W, L)` and `z` and all `x, y`, `|E T_{xy} − [Θ^{(M)}(|m|² + 𝒢^{(M)})]_{xy}| ≤ C W^{−Md/2}` (1.22) and
  `|E|G_{xy}|² − [(1 − (1 + Σ̃^{(M)})|m|²S)^{−1}(|m|² + 𝒢^{(M)})]_{xy}| ≤ C W^{−Md/2}` (1.29) (`resM`);
- (`cor17Concl`) for all `δ, τ > 0` there are `C` and `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)` with
  `W^M ≥ L⁴`, `|E| < 2 − κ`, `W²/L^{2−ε} ≤ η ≤ W^{−δ}`, and `p = 2πk/L ∈ 𝕋_L^d` (`zfreq k`) with `|p| ≤ W^{−1−δ}`,
  at `z = E + iη`: there are `e₁, e₃` with `|e₁| ≤ C W^{−d/2+τ}`, `|e₃| ≤ C W^{−M}` and
  `Σ_x E T_{0x} e^{ip·x} = Θ̂^{(M)}(p)(|m|² + e₁) + e₃` (1.35); and there are `e₁, e₂, e₃` with the same bounds on
  `e₁, e₃`, `|e₂| ≤ C(η² + W^{−d+τ}η + W³|p|³)`, a nonzero denominator, and
  `Σ_x E|G_{0x}|² e^{ip·x} = r(E)(|m|² + e₁)/(η + W² p·𝒟_eff^{(M)}(z) p + e₂) + e₃` (1.36). Here `Θ̂` is
  `symbol`, `e^{ip·x}` is `zchar k x`, `r(E)` is `rE E`, `𝒟_eff^{(M)}` is `diffEff` (built from `diffD`, `diffDl`
  with the sums over `x ∈ Z_L^d`), and `W² p·𝒟 p` is `qform`.

### 1.4 Non-degenerate instances

`RBM8D/Endpoints.lean` applies each theorem at concrete data in a compiled `example`. The profile is the Gaussian
`ψ(p) = e^{−|p|²/2}` on `ℝ^8` (`c_ψ = 3/8`; its `f_{W,L}` is positive and symmetric for all `W, L ≥ 1`), obtained from
`G11.inst_endpointHyp`; `n = max(L₀, 2)` with `L₀` the threshold given by the theorem.
- `localLaw` at `d = 8`, `c₀ = c₁ = 1/4`, `κ = ε = 1/2`, `τ = D = 1`, `W = n`, `L = n⁴`, `x = y = 0`: `(W, L)` lies in
  `adm(1/4, 1/4)`, the window of `η` is `[n^{−4}, 1]`, the bound `L^{−1}` is `< 1`, and the probability bound of (1.19)
  holds there.
- `thm13` at `d = 8`, `c₀ = c₁ = 1/4`, `κ = 1/2`, `γ = 1`, `K = 2`, `τ = D = 1`, `W = ℓ = n`, `L = n⁴`: the window
  `[W, L^{3/4}]` of `ℓ` is `[n, n³]`, the threshold of (1.12) is `n^{−5} + n^{−3} < 1`, the threshold `W²/L = n^{−2}` of
  (1.13) lies in `(N^{−1/2}, 1)`, and both probability bounds hold there.
- `quantumDiffusion` at `d = 8`, `(c₀, c₁, κ, ε) = (1/10, 2/5, 1/10, 1/10)`, `M = 10`, `τ = δ = 1/2`, `W ≥ 4096`,
  `L = W²`: `(W, L) ∈ adm(1/10, 2/5)`, `W^{10} ≥ L⁴`, `z = i ∈ specDom (1/10) (1/10) W L`, and `η = W^{−1}`, `k = e₁ ≠ 0` lie in the
  window of [I, Corollary 1.7]. There the invertibility, (1.24) and (1.28) at `x = y = 0`, (1.22) at `x = y = 0`, and
  (1.36) at `p = 2πe₁/L` hold.

### 1.5 Axioms

```
'RBM8D.thm13' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM8D.localLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM8D.quantumDiffusion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 2. Differences between the statements

Each entry gives the wording of the revised [I], the Lean form, and the relation. "Identical": the same statement up to
notation. "Equivalent": each implies the other. "Lean stronger": the Lean statement implies the paper's.

### 2.1 "`L` sufficiently large" and the order of the constants (identical)

- **Paper.** [I, Theorems 1.3–1.5] fix `d ≥ 8` and the constants `c₀, c₁, κ` (and `γ, K`; `ε, M`), and the estimates hold
  "for any constants `τ, D > 0`" (small `ε, τ`, large `D`) "provided that `L` is sufficiently large depending on these
  constants". In [I, Corollary 1.7] the constants of the `O(·)` terms depend only on `d, c₀, c₁, κ, ψ, ε, δ, τ, M`; the
  `O(W^{−Md/2})` of (1.22) and (1.29) is read in the same way.
- **Lean.** `∀ d ≥ 8, ∀ P, ∀ constants > 0, ∃ L₀, ∀ (W, L) …, L₀ ≤ L → …`; in `cor17Concl`, `∃ C, ∃ L₀` after `δ, τ`, which
  come after `M`, `ε` and the other constants. `L₀` and `C` do not depend on `W`, `ℓ`, `x`, `y`, `z`, `E`, `η` or `p`.
- **Relation.** Identical. "Small" `ε, τ` and "large" `D` are written as all positive `ε, τ, D`, which is the same
  family of statements, since the bounds are monotone in these constants.

### 2.2 Failure probability instead of success probability (equivalent)

- **Paper.** "`P(…) ≥ 1 − L^{−D}`" in (1.12), (1.13), (1.19).
- **Lean.** `rbmLaw d P p {ω | bad event} ≤ ENNReal.ofReal (L^{−D})`, the set being the complement of the paper's
  event, measured as an outer measure.
- **Relation.** For a measurable event `B`, `P(B) ≥ 1 − x` if and only if `P(Bᶜ) ≤ x`. Without measurability, an outer
  measure `≤ x` of `Bᶜ` gives a measurable `A ⊇ Bᶜ` with `P(A) ≤ x`, so `B` contains the event `Aᶜ` of probability
  `≥ 1 − x`.

### 2.3 [I, Theorem 1.3]: eigenvectors, and uniformity in `ℓ` (Lean stronger)

- **Paper.** `{u_α}` is "any orthonormal eigenbasis, and our results hold for any such choice"; (1.13): with probability
  `≥ 1 − L^{−D}`, `‖u_α‖_∞ ≤ W^{1+τ}/L` for all `α` with `λ_α ∈ (−2+κ, 2−κ)`. The hypotheses `W ≤ ℓ ≤ L^{1−c₀}` and
  `L^{c₁} ≤ W ≤ L` are shared by (1.12) and (1.13).
- **Lean.** The failure event of (1.12) is "there is an orthonormal eigenbasis with `|𝓑|/N > …`", and that of (1.13)
  is "some unit vector of some eigenspace with eigenvalue in `(−2+κ, 2−κ)` has an entry `> W^{1+τ}/L`". One `L₀` serves
  both, for all `ℓ ∈ [W, L^{1−c₀}]` and all `W ∈ [L^{c₁}, L]`.
- **Relation.** For any choice of eigenvectors, the paper's failure event is contained in the Lean one, so one bound
  covers every choice at once; in (1.13) the Lean event also covers unit vectors of a multiple eigenvalue that belong to
  no chosen basis. The threshold uniform in `ℓ` is the reading in which `L₀` depends on the constants only.

### 2.4 [I, Theorem 1.4] (identical)

- **Paper.** (1.19): for all `x, y`, `P(sup_{E ∈ (−2+κ,2−κ)} sup_{W²/L^{2−ε} ≤ η ≤ 1} |G_{xy}(z) − m(z)δ_{xy}|² ≤ W^τ B_{xy})
  ≥ 1 − L^{−D}` under `L^{c₁} ≤ W ≤ L^{1−c₀}`.
- **Lean.** `∀ x y`, the failure event `∃ E ∈ (−2+κ, 2−κ), ∃ η ∈ [W²/L^{2−ε}, 1], W^τ B_{xy} < |G_{xy} − m δ_{xy}|²`.
- **Relation.** The supremum is `≤ c` exactly when every value is `≤ c`; the complement is the Lean event. Identical
  (with §2.2).

### 2.5 [I, Theorem 1.5] and [I, Corollaries 1.6, 1.7]: one statement (identical; Lean stronger in three places)

- **Paper.** `{Σ_l}_{l≥4}` is a sequence of deterministic matrices "that does not depend on `M`", each a sum of
  deterministic doubly connected graphs ([I, Definition 2.13]); `1 − |m|²S(1 + Σ̃^{(M)})` is invertible; (1.26) contains
  the diagonal term `L^τ W^{−(l−2)d/2} 1_{x=0}`; Corollaries 1.6 and 1.7 use "the same `Σ_l` and `𝒢^{(M)}` as in
  Theorem 1.5"; [I, Corollary 1.7] assumes `W^M ≥ L⁴`, `|p| ≤ W^{−1−δ}`, `W²/L^{2−ε} ≤ η ≤ W^{−δ}` and states that the
  denominator of (1.36) does not vanish.
- **Lean.** `∃ Sg, (∃ Sig, SigmaOf d P Sig Sg) ∧ ∀ M, ∃ Gc, thm15Concl … ∧ cor17Concl …`: the self-energies come before
  `M`, the local correction after `M`, and the three results share them. The invertibility is the first conjunct of
  `thm15Concl`. (1.26) is written with the diagonal term. The `O(·)` terms of (1.22), (1.29), (1.35), (1.36) are
  `C W^{−Md/2}` and the explicit `e₁, e₂, e₃`.
- **Relation.** Identical, with three places where the Lean statement is stronger:
  1. (1.25) is stated for all `z ∈ ℂ`, not only `Im z > 0` (it is structural, as the paper remarks after Theorem 1.5).
  2. The Lean statement is for every `M ∈ ℕ` (for `M < 4`, `Σ̃^{(M)} = 0`), where the paper takes `M` large.
  3. (1.26), (1.27) are stated in `thm15Concl` for `4 ≤ l ≤ M`; since `Σ_l` does not depend on `M`, the order `M = l`
     gives them for every `l ≥ 4`.
- **Not in the Lean statement.** [I, Definition 2.13 (iii)] defines the infinite-space limit `Σ_l^∞` of the graphs of
  `Σ_l`. The Lean statement provides the graphs `Sig l` from which it is defined, but makes no assertion about it; it is
  an internal object of the proof (`RBM8D/SelfEnergy/*`). "At most `C_l` graphs" in Definition 2.13 (i) is the
  finiteness of the list `Sig l`, which does not depend on `W`, `L`, `z`.
- **The variance matrix in `SigmaOf`.** `Σ_l(W, L, z)` is the value of `Sig l` "whenever `S_{W,L}` is symmetric". By the
  profile assumption this holds for `(W, L) ∈ adm(c₀, c₁)` with `W ≥ W₀`, hence, since `W ≥ L^{c₁}`, for all sizes of
  the conclusions with `L ≥ W₀^{1/c₁}`.

### 2.6 The profile assumption (Lean more general)

- **Paper.** [I, Assumption 1.2]: `f_{W,L} : Z_L^d → ℝ_+ = [0, ∞)` is a nonnegative symmetric function of the form
  (1.6); [I, Assumption 1.1] is posed "for `L ≫ W ≫ 1`".
- **Lean.** `Profile.f_nonneg` for `W ≥ 1` and every `L`; `Profile.f_symm` only for `(W, L) ∈ adm(c₀, c₁)` and
  `W ≥ W₀(c₀, c₁)`, for every `c₀, c₁ > 0`.
- **Relation.** The Lean hypothesis is implied by the paper's, so the Lean theorems apply to every profile the paper
  allows. The symmetry is a condition on `f_{W,L}` beyond the symmetry of `ψ` only at the points with a coordinate equal
  to `L/2`, where `[−x]_L ≠ −[x]_L`; Lean requires it in the regime `L ≫ W ≫ 1` of the model.

### 2.7 Notation (identical)

- The entries of (1.4) are written in real coordinates (§1.2); `E h_xx² = s_xx` and `E(Re h_xy)² = E(Im h_xy)² = s_xy/2`
  as in the revised (1.4).
- `‖x‖_L` is the periodic `ℓ^∞` norm (`zdistInf`), as fixed in [I, §1.2]; the representatives `[x]_L ∈ (−L/2, L/2]^d` of
  (1.2) are `ZMod.valMinAbs`, also in `𝒟` and `𝒟_l` and in `p ∈ 𝕋_L^d = (2π/L · Z_L)^d`.
- `m(z)` is the root of `m² + zm + 1 = 0` with `Im m > 0` on `ℂ_+`, which is the closed form of (1.15) on `ℂ_+`.
- In (1.23) and (1.29) the inverses are `Ring.inverse`; the invertibility of `1 − |m|²S(1 + Σ̃^{(M)})` is a conclusion,
  and `1 − (1 + Σ̃^{(M)})|m|²S` is then invertible as well (`1 − AB` is invertible if and only if `1 − BA` is), so
  `Ring.inverse` is the inverse in both.
- `𝒟(E)`, `𝒟_l(z)` and `𝒟_eff^{(M)}(z)` of [I, §1.3] are `diffD`, `diffDl` and `diffEff` with `E = Re z`.

### 2.8 The other recorded differences

During the formalization every difference between the arXiv texts and the Lean statements was recorded, 503 in all.
212 of them (misprints, missing conditions, missing proof details, and the replaced proof route of the local law) are
taken into account in the revised papers. Of the others, those that concern the five main results are §§2.1–2.7; the
remaining ones concern conventions and the form of intermediate statements in Lean (the main ones are in §3), or parts
of the arXiv [II] (Section 9, Appendix B) that the revised [II] no longer contains.

---

## 3. Internal steps formalized in a different form

None of these changes a statement of §1.

- **Graphs as data.** A graph is a term `Graphs.Graph k n` (external and internal atoms, a list of edges and weights, a
  polynomial coefficient in `m`), a formal sum is `Graphs.Expansion k`, and its value on a data record `Graphs.Data`
  (`m`, `S`, `S^±`, `Θ`, the self-energies) is `Graphs.Graph.val`. Scaling order (`Graphs.Graph.ord`), normal regular,
  doubly connected (`Graphs.Graph.DoublyConnected`) and the other graph properties are predicates on this syntax.
  `RBM8D/Graph/Syntax.lean`, `RBM8D/Graph/Value.lean`, `RBM8D/Graph/Order.lean`, `RBM8D/Graph/Molecule.lean`.
- **`T`-expansions and `T`-equations as records.** The formal sums `R`, `A`, `Q`, `Err` of [II, Definition 3.2] are a
  record `Graphs.TRec` with the predicate `Graphs.IsTExpansion`; a `T`-equation is `Graphs.TEqRec`. `RBM8D/TExp/Defs.lean`.
- **The construction of [II, Theorem 3.7].** The expansion strategy of [II, §6] is a function that makes every choice
  deterministically, run on graphs; [II, Theorem 3.7] is `Graphs.tEquation : Graphs.tEquationStmt`. Dotted edges at the
  external atoms are read blockwise. `RBM8D/GlobalExp/*`, `RBM8D/Graph/MolRead.lean`.
- **The induction of [I, §5].** [II, Theorem 3.7], [II, Lemma 3.9] and [II, Corollary 3.8] are combined into one
  induction on the order that gives one family of self-energies and a `T`-expansion of every order `n ≥ 2` and every
  error order `D ≥ n + 2` (`G14.jointH_of_parts`, `solve`). `RBM8D/Joint/*`.
- **Stochastic domination.** `≺` ([I, Definition 2.3]) is `StochDom` along a filter of sizes, `W → ∞` inside
  `adm(c₀, c₁)` (`admFilterL`), at the scale `W`. The main results are written with an explicit `L₀`;
  `G14.localLaw_of_tExp` converts. `RBM8D/Prob/StochDom.lean`, `RBM8D/Input/Sizes.lean`, `RBM8D/Joint/Main.lean`.
- **The local law from the `T`-expansion ([II, Theorem 3.6]).** The Lean proof follows the cutoff-moment route of the
  revised [II, §§7–8], which replaces the continuity estimate and the averaged bound of the arXiv [II, §9]:
  `cutImprove : cutImproveStmt` ([II, Lemma 7.3]), `cutPair : cutPairStmt` ([II, Lemma 8.11]),
  `hookGraphSum : hookGraphSumStmt` ([II, Lemma 8.7]), `cutMoment_of` ([II, Lemma 8.1] and [II, Lemma 7.4]), the induction
  on a net of spectral parameters `localLawTExp_cutoff_of` (proof of [II, Theorem 3.6] in [II, §7]), assembled in
  `localLawTExp_cutoff : localLawTExpStmt'`. `RBM8D/LocalLaw/Cutoff/*`.
- **Self-energies for a symmetrized variance matrix.** Inside the proof the graphs are evaluated at
  `smatVar P = (S + Sᵀ)/2`, which equals `S` wherever `S` is symmetric (§2.5). `RBM8D/Bound/GraphAbs.lean`.
- **Schwartz profiles directly.** [I, Theorem 2.1] (compactly supported `ψ`) is not stated; the induction is carried
  out once for Schwartz `ψ`, and the sum-zero property (1.27) is proved with the renormalized self-energies of
  [I, Definition 8.2] and [I, Lemmas 8.3–8.5] (`Graphs.Renorm.sig`). `RBM8D/SelfEnergy/*`.
- **The propagators.** The decay of `S^±` ([I, Lemma 2.2]) and of `Θ` ((1.17)), and the infinite-space limits of [I, §7],
  are proved by Fourier analysis on the torus (dyadic shells in `p`, periodisation), not with the random walk estimate of
  [I, Appendix B]: `Splus_decay`, `Theta_decay`, `Theta_sub_ThetaInf`. `RBM8D/Kernel/*`.
- **Gaussian integration by parts.** It is proved from Stein's identity for each real coordinate of the sample
  (`integral_mul_gaussianReal`, `integral_hmat_mul`). `RBM8D/Prob/Stein.lean`, `RBM8D/Prob/IBP.lean`.
- **Results quoted from other works, proved in Lean.** (1.17) (quoted from earlier works): `Theta_decay`. The large
  deviation bounds of [II, Lemma 7.1] = [I, Lemma 5.1]: `offDiagGT` ((7.2)) and `diagGT` ((7.3)), `RBM8D/Input/GT.lean`,
  `RBM8D/Input/GTDiag.lean`. The local law at `η = 1` used from [II, Lemma 8.9]: `eta1Law`, `RBM8D/Input/GTDiag.lean`.

---

## 4. Numbering in the Lean comments

Comments and docstrings in `RBM8D/` cite the arXiv versions, arXiv:2104.12048v2 for [I] and arXiv:2107.05795v3 for [II].
The revised papers have the same numbering except in the places below. "—": no counterpart in the revised paper.

### 4.1 [II], Sections 7–9 and Appendix B

| arXiv:2107.05795v3 | revised [II] |
|---|---|
| §7; Lemmas 7.1, 7.2 | same |
| Lemma 7.3 (continuity estimates) | —; Lemma 7.3 is the improvement on the cutoff event |
| Lemma 7.4 (entrywise bounds on `T`-variables) | —; Lemma 7.4 is the high moment estimate on truncated variables |
| §8, §8.1; Definition 8.2, Claim 8.3, Lemmas 8.4, 8.5, Notation 8.8, Lemma 8.9 | same |
| Lemma 8.1 (high moment estimate) | —; Lemma 8.1 is the moment recursion (8.1) |
| Claim 8.6 | Claim 8.6, restated as bounds on the absolute-value graphs |
| Claim 8.7 (the `Q`-graphs in the high moment) | —; Lemma 8.7 is the hook bound (8.21) |
| §8.2 (proof of Lemma 8.1) | —; §8.4 proves the new Lemma 8.1 |
| §8.3 (proof of Lemma 7.2) | §8.2 |
| — | §8.3 (Gaussian estimates and resampling of one row), Lemmas 8.10–8.12 |
| §9 (continuity estimate), §§9.1–9.4: Lemma 9.1, Definitions 9.2, 9.4, 9.6, 9.9, 9.10, 9.13, Lemmas 9.3, 9.5, 9.7, 9.11, 9.12, 9.14, Strategy 9.8 | — (the revised [II] has no Section 9) |
| Appendix A | same |
| Appendix B, Lemmas B.1–B.3 | — |

Equations:

| arXiv:2107.05795v3 | revised [II] |
|---|---|
| (7.1)–(7.4) | same |
| (7.5)–(7.10) | — |
| (8.1)–(8.5) | — |
| (8.6)–(8.17) | (8.3)–(8.14) |
| (8.18), (8.19) | — |
| (8.20) | (8.19) |
| (8.21) | (8.17) |
| (8.22) | — |
| (8.23) | (8.18) |
| (8.24) | (8.20) |
| (8.25)–(8.28) | — |
| (8.29)–(8.42) | (8.22)–(8.35) |
| (8.43)–(8.49) | — |
| (8.50), (8.51) | (8.46), (8.47) |
| (8.52) | (8.49) |
| (9.1)–(9.33) | — |
| (B.1)–(B.9) | — |

The other equation numbers of the revised §§7–8 are new: (7.5)–(7.12) (the truncated variables, the cutoff, (7.8) of
Lemma 7.3, (7.9) of Lemma 7.4, the net), (8.1), (8.2), (8.15), (8.16), (8.21), (8.36)–(8.45), (8.48) and (8.50)–(8.69).
A Lean comment that cites an item of the left columns refers to the arXiv statement. Where the two columns differ, the
same number may denote a different item in the revised paper (for example Lemmas 7.3, 7.4, 8.1, Claim 8.7, (8.1) and
(8.21)). The Lean files built on the arXiv §§8–9 (for example `RBM8D/LocalLaw/Moment.lean`, `RBM8D/LocalLaw/QTerm.lean`,
`RBM8D/AvgBound/*`) cite those numbers.

### 4.2 [I], Sections 5, 6 and 9

| arXiv:2104.12048v2 | revised [I] |
|---|---|
| Lemma 5.3 (continuity estimate) | —; Lemma 5.3 is the improvement on the cutoff event (= [II, Lemma 7.3]) |
| Lemma 5.4 (entrywise bound on `T`-variables) | —; Lemma 5.4 is the high moment estimate on truncated variables (= [II, Lemma 7.4]) |
| Lemma 5.6 (averaged bound) | — |
| Lemmas 5.1, 5.2, 5.5, 5.7–5.13 | same |
| (5.1)–(5.5) | same |
| (5.6)–(5.14) | — |
| (5.15), (5.16) | (5.10), (5.11) |
| (5.17)–(5.33) | — |
| (5.34)–(5.57) | same |
| (6.44)–(6.46) | — |
| §9, (9.1)–(9.11) | §9 (main ideas for Lemmas 5.4 and 5.7), with new (9.1)–(9.3) |

The new equations (5.6)–(5.9) of the revised [I] are the truncated variables, the cutoff, (5.8) of Lemma 5.3 and (5.9)
of Lemma 5.4.

Sections 1–4, 6 (except (6.44)–(6.46)), 7, 8 and the appendices of [I], and Sections 1–6 and Appendix A of [II], have
the same numbers in both versions. In particular, every number of [I] cited in §§1–2 above is the same in both
versions.

---

## 5. Every Lean name in this document compiles

Every Lean name written in this document, in the text and in Appendix A, is checked with `#check` in a file that imports
`RBM8D`; all of them elaborate.

---

## Appendix A. The Lean statements

The three statements and the definitions they unfold to, by file, in namespace `RBM8D` (the definitions of
`RBM8D/TExp/Defs.lean` are in `RBM8D.Graphs`, and `RBM8D/Diffusion/Defs.lean` opens `Graphs`), with the variables of
their sections (`{d L : ℕ}`, `{ι : Type*} [Fintype ι] [DecidableEq ι]`).

```lean
-- RBM8D/Deloc/Thm13.lean
def Thm13Stmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ γ K : ℝ, 0 < γ → γ ≤ 1 → 1 < K → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ (p : SizeL) (ℓ : ℝ), L₀ ≤ p.1.2 → (p.1.1 : ℝ) ≤ ℓ → ℓ ≤ (p.1.2 : ℝ) ^ (1 - c₀) →
    (p.1.2 : ℝ) ^ c₁ ≤ p.1.1 → p.1.1 ≤ p.1.2 →
    rbmLaw d P p {ω | ∃ (u : Zd d p.1.2 → Zd d p.1.2 → ℂ) (lam : Zd d p.1.2 → ℝ),
        IsOrthoEigenbasis (hmat ω) u lam ∧
        (p.1.1 : ℝ) ^ τ * (ℓ ^ 2 / (p.1.2 : ℝ) ^ 2 + (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)) <
          ((locSetB d p.1.2 κ γ K ℓ u lam).card : ℝ) / (p.1.2 : ℝ) ^ d}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D)) ∧
    rbmLaw d P p {ω | ∃ lam : ℝ, lam ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ u : Zd d p.1.2 → ℂ,
        ∑ x, ‖u x‖ ^ 2 = 1 ∧ hmat ω *ᵥ u = (lam : ℂ) • u ∧
        ∃ x, (p.1.1 : ℝ) ^ (1 + τ) / (p.1.2 : ℝ) < ‖u x‖}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))
-- RBM8D/Deloc/Defs.lean
def LocalLawStmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ p : SizeL, L₀ ≤ p.1.2 → p.1 ∈ adm c₀ c₁ → ∀ x y : Zd d p.1.2,
    rbmLaw d P p {ω | ∃ E : ℝ, E ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ η : ℝ,
        (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) ≤ η ∧ η ≤ 1 ∧
        (p.1.1 : ℝ) ^ τ * bB d p.1.2 p.1.1 x y <
          ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * I)) (msc ((E : ℂ) + (η : ℂ) * I)) x y‖ ^ 2}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (u : ι → ι → ℂ) (lam : ι → ℝ) : Prop :=
  (∀ α β, ∑ x, star (u α x) * u β x = if α = β then 1 else 0) ∧
  ∀ α, H *ᵥ u α = (lam α : ℂ) • u α
def locSetB (d L : ℕ) [NeZero L] (κ γ K ℓ : ℝ) (u : Zd d L → Zd d L → ℂ) (lam : Zd d L → ℝ) :
    Finset (Zd d L) :=
  Finset.univ.filter fun α => lam α ∈ Set.Ioo (-2 + κ) (2 - κ) ∧
    ∃ x₀ : Zd d L, ∑ x, ‖u α x‖ ^ 2 * Real.exp (((zdistInf d L (x - x₀) : ℝ) / ℓ) ^ γ) ≤ K
-- RBM8D/Diffusion/Defs.lean
def quantumDiffusionStmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ → 0 < ε →
    ∃ Sg : SigmaFam d, (∃ Sig : ℕ → Expansion 2, SigmaOf d P Sig Sg) ∧
      ∀ M : ℕ, ∃ Gc : LocCorr d,
        thm15Concl d P c₀ c₁ κ ε Sg M Gc ∧ cor17Concl d P c₀ c₁ κ ε Sg M
def SigmaOf (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (Sg : SigmaFam d) : Prop :=
  (∀ l, 4 ≤ l → SelfEnergyShape l (Sig l)) ∧
  (∀ l, 4 ≤ l → ∀ (W L : ℕ) [NeZero L] (z : ℂ), (Smat P.ψ W L).IsSymm →
    Sg l W L z = sigMat Sig (Smat P.ψ W L) z l) ∧
  (∀ l, 4 ≤ l → ∀ (W L : ℕ) [NeZero L] (z : ℂ) (x a : Zd d L),
    Sg l W L z x (x + a) = Sg l W L z 0 a ∧ Sg l W L z 0 a = Sg l W L z 0 (-a))
def thm15Concl (d : ℕ) (P : Profile d) (c₀ c₁ κ ε : ℝ) (Sg : SigmaFam d) (M : ℕ)
    (Gc : LocCorr d) : Prop :=
  (∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
    ∀ z ∈ specDom κ ε W L,
      IsUnit (1 - amat (Smat P.ψ W L) z * (1 + sigTildeM Sg M W L z)) ∧
      (∀ x y : Zd d L, ‖thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z x y‖ ≤
        (L : ℝ) ^ τ * bB d L W x y) ∧
      (∀ l, 4 ≤ l → l ≤ M → ∀ x : Zd d L, ‖Sg l W L z 0 x‖ ≤
        (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
          (if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)) ∧
      (∀ l, 4 ≤ l → l ≤ M → ‖∑ x : Zd d L, Sg l W L z 0 x‖ ≤
        (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) ∧
      (∀ x y : Zd d L, ‖Gc W L z x y‖ ≤ (L : ℝ) ^ τ * bB d L W x y ^ ((3 : ℝ) / 2))) ∧
  (∃ C : ℝ, ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
    ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L,
      ‖(expT d P W L z x y : ℂ) - (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z *
          (mAbs2 z • 1 + Gc W L z)) x y‖ ≤ C * (W : ℝ) ^ (-((M : ℝ) * d / 2)) ∧
      ‖(expG2 d P W L z x y : ℂ) - (resM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z *
          (mAbs2 z • 1 + Gc W L z)) x y‖ ≤ C * (W : ℝ) ^ (-((M : ℝ) * d / 2)))
def cor17Concl (d : ℕ) (P : Profile d) (c₀ c₁ κ ε : ℝ) (Sg : SigmaFam d) (M : ℕ) : Prop :=
  ∀ δ τ : ℝ, 0 < δ → 0 < τ → ∃ C : ℝ, ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L →
    (W, L) ∈ adm c₀ c₁ → (L : ℝ) ^ 4 ≤ (W : ℝ) ^ M →
    ∀ E η : ℝ, |E| < 2 - κ → (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ η → η ≤ (W : ℝ) ^ (-δ) →
    ∀ k : Zd d L, ‖zfreq k‖ ≤ (W : ℝ) ^ (-1 - δ) →
      (∃ e₁ e₃ : ℂ, ‖e₁‖ ≤ C * (W : ℝ) ^ (-((d : ℝ) / 2) + τ) ∧
        ‖e₃‖ ≤ C * (W : ℝ) ^ (-(M : ℝ)) ∧
        ∑ x : Zd d L, zchar k x * (expT d P W L (E + η * I) 0 x : ℂ) =
          symbol (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L (E + η * I)) (E + η * I)) k *
            (mAbs2 (E + η * I) + e₁) + e₃) ∧
      (∃ e₁ e₂ e₃ : ℂ, ‖e₁‖ ≤ C * (W : ℝ) ^ (-((d : ℝ) / 2) + τ) ∧
        ‖e₂‖ ≤ C * (η ^ 2 + (W : ℝ) ^ (-(d : ℝ) + τ) * η + (W : ℝ) ^ 3 * ‖zfreq k‖ ^ 3) ∧
        ‖e₃‖ ≤ C * (W : ℝ) ^ (-(M : ℝ)) ∧
        (η : ℂ) + qform W k (diffEff P Sg M W L (E + η * I)) + e₂ ≠ 0 ∧
        ∑ x : Zd d L, zchar k x * (expG2 d P W L (E + η * I) 0 x : ℂ) =
          (rE E : ℂ) * (mAbs2 (E + η * I) + e₁) /
            ((η : ℂ) + qform W k (diffEff P Sg M W L (E + η * I)) + e₂) + e₃)
abbrev SigmaFam (d : ℕ) : Type :=
  ℕ → ℕ → ∀ (L : ℕ) [NeZero L], ℂ → Matrix (Zd d L) (Zd d L) ℂ
abbrev LocCorr (d : ℕ) : Type :=
  ℕ → ∀ (L : ℕ) [NeZero L], ℂ → Matrix (Zd d L) (Zd d L) ℂ
def sizeOf (W L : ℕ) [NeZero L] : SizeL := ⟨(W, L), NeZero.ne L⟩
def expT (d : ℕ) (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ) (x y : Zd d L) : ℝ :=
  ∫ ω, Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) x y ∂(rbmLaw d P (sizeOf W L))
def expG2 (d : ℕ) (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ) (x y : Zd d L) : ℝ :=
  ∫ ω, ‖green (hmat ω) z x y‖ ^ 2 ∂(rbmLaw d P (sizeOf W L))
def mAbs2 (z : ℂ) : ℂ := ((‖msc z‖ ^ 2 : ℝ) : ℂ)
def amat {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  mAbs2 z • cmat S
def sigTildeM {d : ℕ} (Sg : SigmaFam d) (M W L : ℕ) [NeZero L] (z : ℂ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  ∑ l ∈ Finset.Icc 4 M, Sg l W L z
def thetaM {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (X : Matrix ι ι ℂ)
    (z : ℂ) : Matrix ι ι ℂ :=
  Ring.inverse (1 - amat S z * X) * amat S z
def resM {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (X : Matrix ι ι ℂ)
    (z : ℂ) : Matrix ι ι ℂ :=
  Ring.inverse (1 - X * amat S z)
def rE (E : ℝ) : ℝ := Real.sqrt (4 - E ^ 2) / 2
def diffD {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (W : ℕ) (E : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ((rE E / 2 * ∑ x : Zd d L,
    ((x i).valMinAbs : ℝ) * ((x j).valMinAbs : ℝ) / (W : ℝ) ^ 2 * S 0 x : ℝ) : ℂ)
def diffDl {d L : ℕ} [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (W l : ℕ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => (((W : ℝ) ^ (((l : ℝ) - 2) * d / 2) / 2 : ℝ) : ℂ) * ∑ x : Zd d L,
    ((((x i).valMinAbs : ℝ) * ((x j).valMinAbs : ℝ) / (W : ℝ) ^ 2 : ℝ) : ℂ) * K 0 x
def diffEff {d : ℕ} (P : Profile d) (Sg : SigmaFam d) (M W L : ℕ) [NeZero L] (z : ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  diffD (Smat P.ψ W L) W z.re + ((rE z.re : ℝ) : ℂ) • ∑ l ∈ Finset.Icc 4 M,
    (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) • diffDl (Sg l W L z) W l
def qform {d L : ℕ} (W : ℕ) (k : Zd d L) (Dm : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ((W : ℂ) ^ 2) * ∑ i, ∑ j, ((zfreq k i : ℝ) : ℂ) * Dm i j * ((zfreq k j : ℝ) : ℂ)
-- RBM8D/Profile/Basic.lean
structure Profile (d : ℕ) where
  ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)
  cψ : ℝ
  cψ_pos : 0 < cψ
  symm : ∀ p, ψ (-p) = ψ p
  at_zero : ψ 0 = 1
  abs_le_one : ∀ p, |ψ p| ≤ 1
  le_max : ∀ p, ψ p ≤ max (1 - cψ * ‖p‖ ^ 2) (1 - cψ)
  f_nonneg : ∀ (W L : ℕ) [NeZero L], 1 ≤ W → ∀ x : Zd d L, 0 ≤ fWL ψ W L x
  f_symm : ∀ c₀ c₁ : ℝ, 0 < c₀ → 0 < c₁ → ∃ W₀ : ℕ, ∀ (W L : ℕ) [NeZero L],
    (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ x : Zd d L, fWL ψ W L (-x) = fWL ψ W L x
def zrep {L : ℕ} (x : Zd d L) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => ((x i).valMinAbs : ℝ)
def profInt (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((2 * Real.pi : ℂ) ^ d)⁻¹ * ∫ p, (ψ (W • p) : ℂ) * cexp (I * (inner ℝ p y : ℝ))
def fRaw (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) (x : Zd d L) : ℝ :=
  (profInt ψ W (zrep x)).re
def ZWL (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) [NeZero L] : ℝ :=
  ∑ x : Zd d L, fRaw ψ W L x
def fWL (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) [NeZero L] (x : Zd d L) : ℝ :=
  (ZWL ψ W L)⁻¹ * fRaw ψ W L x
def Smat (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) [NeZero L] :
    Matrix (Zd d L) (Zd d L) ℝ :=
  Matrix.of fun x y => fWL ψ W L (x - y)
-- RBM8D/Input/Sizes.lean
abbrev SizeL : Type := {p : ℕ × ℕ // p.2 ≠ 0}
def rbmLaw (d : ℕ) (P : Profile d) (p : SizeL) : Measure (Sample (Zd d p.1.2)) :=
  gaussLaw (Smat P.ψ p.1.1 p.1.2)
-- RBM8D/Prob/Model.lean
def idxKey (ι : Type u) [Fintype ι] (x : ι) : ℕ := (Fintype.equivFin ι x).val
abbrev OffPair (ι : Type u) [Fintype ι] : Type u := {p : ι × ι // idxKey ι p.1 < idxKey ι p.2}
abbrev Coord (ι : Type u) [Fintype ι] : Type u := ι ⊕ (OffPair ι × Bool)
abbrev Sample (ι : Type u) [Fintype ι] : Type u := Coord ι → ℝ
def coordVar (S : Matrix ι ι ℝ) : Coord ι → ℝ≥0
  | .inl x => (S x x).toNNReal
  | .inr (e, _) => (S e.1.1 e.1.2 / 2).toNNReal
def gaussLaw (S : Matrix ι ι ℝ) : Measure (Sample ι) :=
  Measure.pi fun c => gaussianReal 0 (coordVar S c)
def hmat (ω : Sample ι) : Matrix ι ι ℂ :=
  Matrix.of fun x y =>
    if h : idxKey ι x < idxKey ι y then
      (ω (.inr (⟨(x, y), h⟩, true)) : ℂ) + I * (ω (.inr (⟨(x, y), h⟩, false)) : ℂ)
    else if h' : idxKey ι y < idxKey ι x then
      (ω (.inr (⟨(y, x), h'⟩, true)) : ℂ) - I * (ω (.inr (⟨(y, x), h'⟩, false)) : ℂ)
    else (ω (.inl x) : ℂ)
-- RBM8D/Prob/StochDom.lean
def adm (c₀ c₁ : ℝ) : Set (ℕ × ℕ) :=
  {p | (p.2 : ℝ) ^ c₁ ≤ p.1 ∧ (p.1 : ℝ) ≤ (p.2 : ℝ) ^ (1 - c₀)}
-- RBM8D/Basic/Domain.lean
def bB (d L W : ℕ) (x y : Zd d L) : ℝ :=
  (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ))
def specDom (κ ε : ℝ) (W L : ℕ) : Set ℂ :=
  {z | |z.re| < 2 - κ ∧ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ z.im ∧ z.im ≤ 1}
-- RBM8D/Basic/Lattice.lean
abbrev Zd (d L : ℕ) : Type := Fin d → ZMod L
def zdist (L : ℕ) (u : ZMod L) : ℕ := min u.val (L - u.val)
def zdistInf (d L : ℕ) (x : Zd d L) : ℕ := Finset.univ.sup fun i => zdist L (x i)
-- RBM8D/Basic/Resolvent.lean
noncomputable def green {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
    Matrix n n ℂ := (H - z • 1)⁻¹
-- RBM8D/Basic/Semicircle.lean
noncomputable def mscDisc (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))
noncomputable def mscRoot₁ (z : ℂ) : ℂ := (-z + mscDisc z) / 2
noncomputable def mscRoot₂ (z : ℂ) : ℂ := (-z - mscDisc z) / 2
noncomputable def msc (z : ℂ) : ℂ := if 0 < (mscRoot₁ z).im then mscRoot₁ z else mscRoot₂ z
-- RBM8D/Input/Entry.lean
def entryErr (G : Matrix ι ι ℂ) (m : ℂ) (x y : ι) : ℂ := G x y - if x = y then m else 0
def Tvar (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ) (m : ℂ) (x y : ι) : ℝ :=
  ‖m‖ ^ 2 * ∑ α, S x α * ‖G α y‖ ^ 2
-- RBM8D/Kernel/Fourier.lean
def zchar [NeZero L] (k x : Zd d L) : ℂ := ∏ i, ZMod.stdAddChar (k i * x i)
def zfreq (k : Zd d L) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => 2 * Real.pi * ((k i).valMinAbs : ℝ) / L
-- RBM8D/Kernel/Circulant.lean
def symbol [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (k : Zd d L) : ℂ :=
  ∑ x, K 0 x * zchar k x
-- RBM8D/Kernel/Propagator.lean
def cmat (S : Matrix ι ι ℝ) : Matrix ι ι ℂ := S.map ((↑) : ℝ → ℂ)
-- RBM8D/TExp/Defs.lean (namespace RBM8D.Graphs)
def SelfEnergyShape (l : ℕ) (E : Expansion 2) : Prop :=
  ∀ g ∈ E, (∃ C, g.2.Normal C ∧ g.2.DotsAcyclic) ∧
    g.2.comps.all (Comp.isDetKind (l - 1)) = true ∧
    g.2.ord = l ∧
    (g.2.mapAtoms (Sum.elim (fun a => Sum.inr (Fin.castAdd g.1 a))
      (fun b => Sum.inr (Fin.natAdd 2 b))) : Graph 0 (2 + g.1)).DoublyConnected
def sigMat {ι : Type} [Fintype ι] [DecidableEq ι] (Sig : ℕ → Expansion 2) (S : Matrix ι ι ℝ)
    (z : ℂ) (l : ℕ) : Matrix ι ι ℂ :=
  Matrix.of fun x y => (Sig l).val (detData S z (sigUpTo Sig S z l)) ![x, y]
```
