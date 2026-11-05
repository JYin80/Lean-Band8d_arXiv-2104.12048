import RBM8D.Input.Sizes
import RBM8D.Input.Entry
import RBM8D.Basic.Resolvent

/-!
# Weak delocalization of bulk eigenvectors: statements

[I, Theorem 1.3] ((1.12), (1.13)), the local law [I, Theorem 1.4] ((1.19)) and [I, Lemma 8.1]
((8.1)) as statements, for the law `rbmLaw` of [I, Assumptions 1.1–1.2] on `Z_L^d`, with the
eigenbases and index sets of [I, §1.2] and [I, §8].

* (1.13) is stated for every unit vector of a bulk eigenspace, and (1.12) for every orthonormal
  eigenbasis; both contain every choice of eigenvectors.
* The hypotheses of [I, Theorem 1.4] are `L^{c₁} ≤ W ≤ L^{1−c₀}` with an explicit `L₀`.
* Probabilities are the measure of an arbitrary set of samples (outer measure).
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Complex Matrix
open scoped ENNReal

namespace RBM8D

/-- **[I, Theorem 1.4], (1.19)**: for `d ≥ 8`, a profile `ψ`, constants `c₀, c₁, κ > 0` and all
`ε, τ, D > 0` there is `L₀` such that for `L ≥ L₀`, `L^{c₁} ≤ W ≤ L^{1−c₀}` and all `x, y`,
`P(∃ E ∈ (−2+κ, 2−κ), ∃ η ∈ [W²/L^{2−ε}, 1], |G_xy(E+iη) − m(E+iη) δ_xy|² > W^τ B_xy) ≤ L^{−D}`. -/
def LocalLawStmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ p : SizeL, L₀ ≤ p.1.2 → p.1 ∈ adm c₀ c₁ → ∀ x y : Zd d p.1.2,
    rbmLaw d P p {ω | ∃ E : ℝ, E ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ η : ℝ,
        (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) ≤ η ∧ η ≤ 1 ∧
        (p.1.1 : ℝ) ^ τ * bB d p.1.2 p.1.1 x y <
          ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * I)) (msc ((E : ℂ) + (η : ℂ) * I)) x y‖ ^ 2}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))

/-- `(u_α, λ_α)_α` is an orthonormal eigenbasis of `H`: `⟨u_α, u_β⟩ = δ_αβ` and `H u_α = λ_α u_α`;
the eigenvectors are indexed by the index set of `H` itself. -/
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (u : ι → ι → ℂ) (lam : ι → ℝ) : Prop :=
  (∀ α β, ∑ x, star (u α x) * u β x = if α = β then 1 else 0) ∧
  ∀ α, H *ᵥ u α = (lam α : ℂ) • u α

open scoped Classical in
/-- The set `𝓑_{γ,K,ℓ}` of [I, §1.2]: bulk indices `α` (`λ_α ∈ (−2+κ, 2−κ)`) with
`min_{x₀} Σ_x |u_α(x)|² exp((‖x − x₀‖_L / ℓ)^γ) ≤ K`. -/
def locSetB (d L : ℕ) [NeZero L] (κ γ K ℓ : ℝ) (u : Zd d L → Zd d L → ℂ) (lam : Zd d L → ℝ) :
    Finset (Zd d L) :=
  Finset.univ.filter fun α => lam α ∈ Set.Ioo (-2 + κ) (2 - κ) ∧
    ∃ x₀ : Zd d L, ∑ x, ‖u α x‖ ^ 2 * Real.exp (((zdistInf d L (x - x₀) : ℝ) / ℓ) ^ γ) ≤ K

open scoped Classical in
/-- The set `𝓑̃_{M,K,ℓ}` of [I, §8]: bulk indices `α` with
`min_{x₀} Σ_x |u_α(x)|² (‖x − x₀‖_L / ℓ + 1)^M ≤ K`. -/
def locSetBt (d L : ℕ) [NeZero L] (κ M K ℓ : ℝ) (u : Zd d L → Zd d L → ℂ) (lam : Zd d L → ℝ) :
    Finset (Zd d L) :=
  Finset.univ.filter fun α => lam α ∈ Set.Ioo (-2 + κ) (2 - κ) ∧
    ∃ x₀ : Zd d L, ∑ x, ‖u α x‖ ^ 2 * ((zdistInf d L (x - x₀) : ℝ) / ℓ + 1) ^ M ≤ K

open scoped Classical in
/-- The set `𝒜_{δ,ℓ}` of the proof of [I, Lemma 8.1]: bulk indices `α` with
`Σ_x |u_α(x)| ‖P_{x,ℓ} u_α‖ ≤ δ`, where `P_{x,ℓ}` is the indicator of `‖y − x‖_L ≥ ℓ`. -/
def locSetA (d L : ℕ) [NeZero L] (κ δ ℓ : ℝ) (u : Zd d L → Zd d L → ℂ) (lam : Zd d L → ℝ) :
    Finset (Zd d L) :=
  Finset.univ.filter fun α => lam α ∈ Set.Ioo (-2 + κ) (2 - κ) ∧
    ∑ x, ‖u α x‖ * Real.sqrt (∑ y ∈ Finset.univ.filter
      (fun y => ℓ ≤ (zdistInf d L (y - x) : ℝ)), ‖u α y‖ ^ 2) ≤ δ

/-- **[I, Theorem 1.3], (1.12)**, for every orthonormal eigenbasis: for `d ≥ 8`, `ψ`,
`c₀, c₁, κ > 0`, `γ ∈ (0, 1]`, `K > 1` and all `τ, D > 0` there is `L₀` such that for `L ≥ L₀`,
`W ≤ ℓ ≤ L^{1−c₀}` and `L^{c₁} ≤ W ≤ L`,
`P(∃ (u, λ) orthonormal eigenbasis of H, |𝓑_{γ,K,ℓ}| / N > W^τ (ℓ²/L² + W^{−d/2})) ≤ L^{−D}`. -/
def Thm13_eq112Stmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ γ K : ℝ, 0 < γ → γ ≤ 1 → 1 < K → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ (p : SizeL) (ℓ : ℝ), L₀ ≤ p.1.2 → (p.1.1 : ℝ) ≤ ℓ → ℓ ≤ (p.1.2 : ℝ) ^ (1 - c₀) →
    (p.1.2 : ℝ) ^ c₁ ≤ p.1.1 → p.1.1 ≤ p.1.2 →
    rbmLaw d P p {ω | ∃ (u : Zd d p.1.2 → Zd d p.1.2 → ℂ) (lam : Zd d p.1.2 → ℝ),
        IsOrthoEigenbasis (hmat ω) u lam ∧
        (p.1.1 : ℝ) ^ τ * (ℓ ^ 2 / (p.1.2 : ℝ) ^ 2 + (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)) <
          ((locSetB d p.1.2 κ γ K ℓ u lam).card : ℝ) / (p.1.2 : ℝ) ^ d}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))

/-- **[I, Theorem 1.3], (1.13)**, for every unit vector of a bulk eigenspace: under the hypotheses
of (1.12), `P(∃ λ ∈ (−2+κ, 2−κ), ∃ u, ‖u‖₂ = 1, H u = λ u, ‖u‖_∞ > W^{1+τ}/L) ≤ L^{−D}`. -/
def Thm13_eq113Stmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ γ K : ℝ, 0 < γ → γ ≤ 1 → 1 < K → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ (p : SizeL) (ℓ : ℝ), L₀ ≤ p.1.2 → (p.1.1 : ℝ) ≤ ℓ → ℓ ≤ (p.1.2 : ℝ) ^ (1 - c₀) →
    (p.1.2 : ℝ) ^ c₁ ≤ p.1.1 → p.1.1 ≤ p.1.2 →
    rbmLaw d P p {ω | ∃ lam : ℝ, lam ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ u : Zd d p.1.2 → ℂ,
        ∑ x, ‖u x‖ ^ 2 = 1 ∧ hmat ω *ᵥ u = (lam : ℂ) • u ∧
        ∃ x, (p.1.1 : ℝ) ^ (1 + τ) / (p.1.2 : ℝ) < ‖u x‖}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))

/-- **[I, Lemma 8.1], (8.1)**, for every orthonormal eigenbasis, with `≺` written out: for `d ≥ 8`,
`ψ`, `c₀, c₁, κ > 0`, `M, K > 1` and all `τ, D > 0` there is `L₀` such that for `L ≥ L₀`,
`W ≤ ℓ ≤ L^{1−c₀}` and `L^{c₁} ≤ W ≤ L`,
`P(∃ (u, λ), |𝓑̃_{M,K,ℓ}| / N > W^τ ((ℓ^{M/(M+4)} / L^{(M−d)/(M+4)})² + W^{−d/2})) ≤ L^{−D}`. -/
def Lemma81Stmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ M K : ℝ, 1 < M → 1 < K → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ (p : SizeL) (ℓ : ℝ), L₀ ≤ p.1.2 → (p.1.1 : ℝ) ≤ ℓ → ℓ ≤ (p.1.2 : ℝ) ^ (1 - c₀) →
    (p.1.2 : ℝ) ^ c₁ ≤ p.1.1 → p.1.1 ≤ p.1.2 →
    rbmLaw d P p {ω | ∃ (u : Zd d p.1.2 → Zd d p.1.2 → ℂ) (lam : Zd d p.1.2 → ℝ),
        IsOrthoEigenbasis (hmat ω) u lam ∧
        (p.1.1 : ℝ) ^ τ * ((ℓ ^ (M / (M + 4)) / (p.1.2 : ℝ) ^ ((M - d) / (M + 4))) ^ 2 +
            (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)) <
          ((locSetBt d p.1.2 κ M K ℓ u lam).card : ℝ) / (p.1.2 : ℝ) ^ d}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))

section Witness

open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

end RBM8D
