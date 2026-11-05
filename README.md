# Lean formalization of Yang–Yau–Yin, "Delocalization and quantum diffusion of random band matrices in high dimensions I, II"

This repository contains a Lean 4 / Mathlib proof of the main results of

> Fan Yang, Horng-Tzer Yau and Jun Yin, *Delocalization and quantum diffusion of random band matrices in high
> dimensions I: Self-energy renormalization*, [arXiv:2104.12048](https://arxiv.org/abs/2104.12048), and
> *II: T-expansion*, [arXiv:2107.05795](https://arxiv.org/abs/2107.05795).

The revised versions of the two papers are in `paper/`: [`paper/I/band_Part_I.pdf`](paper/I/band_Part_I.pdf) and
[`paper/II/arxiv.pdf`](paper/II/arxiv.pdf), with their LaTeX sources. The proofs there differ in some details from the
arXiv versions; in particular, Sections 7–9 of Part II are different. Theorem and equation numbers in
`docs/PAPER-VS-LEAN.md` refer to these revised PDFs.

Sister projects: [RBM1D](https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718) (Yau–Yin, arXiv:2501.01718),
[RBM2D](https://github.com/JYin80/Lean-RBM2d_arxiv-2503.07606) (Dubova–Yang–Yau–Yin, arXiv:2503.07606) and
[RBM3D](https://github.com/JYin80/Lean-Band3d_arXiv-2507.20274) (Dubova–Yang–Yau–Yin, arXiv:2507.20274).

## Main results

The five main results of Part I are proved for every dimension `d ≥ 8`, as stated in the paper. They are three
theorems in [`RBM8D/Endpoints.lean`](RBM8D/Endpoints.lean); Theorem 1.5 and Corollaries 1.6 and 1.7 form one
statement, because the corollaries use the same `Σ_l` and `𝒢^{(M)}` as the theorem.

```lean
theorem RBM8D.thm13 : RBM8D.Thm13Stmt
theorem RBM8D.localLaw : RBM8D.LocalLawStmt
theorem RBM8D.quantumDiffusion : RBM8D.quantumDiffusionStmt
```

| Part I | Lean statement (file) | Lean theorem | What it says |
|---|---|---|---|
| Theorem 1.3 | `Thm13Stmt` ([`RBM8D/Deloc/Thm13.lean`](RBM8D/Deloc/Thm13.lean)) | `thm13` | Weak delocalization of bulk eigenvectors: (1.12), the fraction of localized eigenvectors, and (1.13), the sup-norm bound `‖u_α‖_∞ ≤ W^{1+τ}/L`, each with probability at least `1 − L^{−D}`. |
| Theorem 1.4 | `LocalLawStmt` ([`RBM8D/Deloc/Defs.lean`](RBM8D/Deloc/Defs.lean)) | `localLaw` | The local law (1.19): `|G_{xy}(z) − m(z)δ_{xy}|² ≤ W^τ B_{xy}` uniformly in `z = E + iη` with `|E| < 2 − κ` and `W²/L^{2−ε} ≤ η ≤ 1`, with probability at least `1 − L^{−D}`. |
| Theorem 1.5, Corollaries 1.6, 1.7 | `quantumDiffusionStmt` ([`RBM8D/Diffusion/Defs.lean`](RBM8D/Diffusion/Defs.lean)) | `quantumDiffusion` | Quantum diffusion: the self-energies `Σ_l` (sums of deterministic doubly connected graphs), the expansion (1.22) of `E T_{xy}` with the renormalized diffusive matrix `Θ^{(M)}`, the bounds (1.24)–(1.28), the expansion (1.29) of `E|G_{xy}|²`, and the diffusion approximation (1.35)–(1.36) in Fourier space. |

The three theorems have no hypotheses other than their parameters. `docs/PAPER-VS-LEAN.md` reads each Lean statement
in plain language and lists every difference from the printed statements (for example, the joint form of
Theorem 1.5 and Corollaries 1.6–1.7, and the places where the Lean statement is slightly stronger).

## The model, and no external inputs

The random band matrix is the Gaussian band matrix of Part I, Assumptions 1.1 and 1.2, on the torus `Z_L^d`: a
Hermitian matrix with independent centred Gaussian entries up to symmetry, real diagonal, and variance profile
`s_{xy} = f_{W,L}(x − y)` given by a symmetric Schwartz profile `ψ`, for sizes `L^{c₁} ≤ W ≤ L^{1−c₀}`.

The proof uses no result from the literature without proving it: every estimate that the papers quote from other
works (the large deviation bounds, the local law at `η = 1`, and the deterministic estimates) is proved in the
library.

## Axioms

Every declaration on which the three theorems depend uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorry` and no declared `axiom`. The output of `#print axioms` for the three theorems is
in `docs/PAPER-VS-LEAN.md` §1.5.

## Build

The toolchain is `leanprover/lean4:v4.36.0-rc1` (file `lean-toolchain`) with Mathlib `v4.36.0-rc1`.

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib; `lake build` builds the whole library.

The hypotheses of the theorems can be satisfied: the compiled examples at the end of
[`RBM8D/Endpoints.lean`](RBM8D/Endpoints.lean) apply each theorem at `d = 8` with a Gaussian profile and explicit
sizes; `docs/PAPER-VS-LEAN.md` §1.4 lists them.

## Map of the library

Section numbers refer to the revised papers in `paper/`.

- `RBM8D/Basic/`, `RBM8D/Profile/`: the torus `Z_L^d`, the bound `B_{xy}` and the spectral domain, resolvents and
  Schur complements, the semicircle transform; the profile `ψ`, `f_{W,L}` and `S` ([I, §1]).
- `RBM8D/Prob/`, `RBM8D/Input/`: the Gaussian model, Gaussian integration by parts, partial expectations,
  stochastic domination; large deviation bounds and the input estimates [I, (5.2), (5.3)], the local law at `η = 1`.
- `RBM8D/Kernel/`: the propagators `Θ`, `S^±` on the torus and on `ℤ^d`, their symbols and decay.
- `RBM8D/Graph/`: graphs, their values and scaling orders, molecules and the doubly connected property, the local
  expansions and the `Q`-expansions ([II, §§2, 4, 5]).
- `RBM8D/TExp/`, `RBM8D/GlobalExp/`: `T`-expansions and `T`-equations, the global expansion strategy and the
  `n`-th order `T`-equation [II, Theorem 3.7] ([II, §§3, 6]).
- `RBM8D/Bound/`: doubly connected graphs and their bounds, labelled `Θ` edges, the graph-summation estimates
  ([I, §6], [II, §8]).
- `RBM8D/LocalLaw/`: the local law from a `T`-expansion by truncated high moments ([II, §§7–8]); the averaged
  quantities in `RBM8D/AvgBound/` that it uses.
- `RBM8D/SelfEnergy/`: self-energies, their cancellation and their infinite-space limits ([I, §§5, 7, 8]).
- `RBM8D/Joint/`: the joint induction on the order of the `T`-expansion and the local law ([I, §5]).
- `RBM8D/Deloc/`, `RBM8D/Diffusion/`: weak delocalization and quantum diffusion ([I, §8]).
- `RBM8D/Endpoints.lean`: the three theorems and their compiled examples.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the papers and the Lean proof in detail: what is proved,
every difference between the Lean statements and the printed ones, the steps that the Lean proof organizes
differently, and the numbering used in the comments of the Lean files.

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

Papers: Fan Yang, Horng-Tzer Yau and Jun Yin. Lean formalization: Jun Yin.
