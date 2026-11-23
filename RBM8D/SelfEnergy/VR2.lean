module

public import RBM8D.SelfEnergy.VR1

@[expose] public section

/-!
# [I, (8.13)]: the row sum of `Σ_n` on the torus against its value on `ℤ^d`

For `d ≥ 8`, lower orders that are self-energies and `Σ_n` of the shape of an `n`-th order
self-energy, this file proves [I, (8.13)],
`|Σ_{x ∈ Z_L^d} Σ_n(0, x)(z) − R(E, W)| ≤ L^τ η W^{-(n-2)d/2}`, `E = Re z`,
with `R(E, W) = Σ'_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)(E)` the number of [I, (8.8)] (`ValZ.rowSum`):

* `VR2.rowSum`: [I, (8.13)] on the whole domain `𝐃(κ, ε)`.

As in [I, §8.1], (8.13) follows from [I, (8.5)] (`RenormDiff.rowSum`: the row sums of `Σ_n` and of
`Σ^{(r)}_n` differ by at most `L^τ η W^{-(n-2)d/2}`) and [I, (8.10)] (`VR1.v2`: the row sum of
`Σ^{(r)}_n` differs from `R(E, W)` by at most the same quantity) by the triangle inequality, each
applied with `τ/2`.

[I, (8.10)] for the orders `4 ≤ l ≤ n` is `VR1.v2` at order `l`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D

open Graphs

variable {d : ℕ}

section Main

/-- For `τ > 0` and a natural number `L ≥ ⌈2^{2/τ}⌉`, `L^{τ/2} ≥ 2`. -/
private theorem VR2_two_le_rpow {τ : ℝ} (hτ : 0 < τ) {L : ℕ}
    (hL : ⌈(2 : ℝ) ^ (2 / τ)⌉₊ ≤ L) : 2 ≤ (L : ℝ) ^ (τ / 2) := by
  have h1 : (2 : ℝ) ^ (2 / τ) ≤ L := le_trans (Nat.le_ceil _) (by exact_mod_cast hL)
  have h2 : ((2 : ℝ) ^ (2 / τ)) ^ (τ / 2) ≤ (L : ℝ) ^ (τ / 2) :=
    Real.rpow_le_rpow (by positivity) h1 (by positivity)
  rw [← Real.rpow_mul (by norm_num), show 2 / τ * (τ / 2) = 1 by field_simp,
    Real.rpow_one] at h2
  exact h2

/-- **[I, (8.13)]**: for `d ≥ 8`, lower orders `≤ n − 1` that are self-energies and `Σ_n` of the
shape of an `n`-th order self-energy: for all `κ, ε, c₀, c₁ > 0` with `c₀ + c₁ < 1` and every
`τ > 0` there is `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)` and `z ∈ 𝐃(κ, ε)`,
`|Σ_{x ∈ Z_L^d} Σ_n(0, x)(z) − R(E, W)| ≤ L^τ η W^{-(n-2)d/2}`, with
`R(E, W) = Σ'_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)(E)` the number of [I, (8.8)] (`ValZ.rowSum`) at
`E = Re z`. The bound holds on all of `𝐃(κ, ε)`, without `η ≤ L^{-ε}`. -/
theorem VR2.rowSum (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (n : ℕ) (Sig : ℕ → Expansion 2)
    (hn : 4 ≤ n) (hSig : SelfEnergiesUpTo d (smatVar P) Sig (n - 1))
    (hsh : SelfEnergyShape n (Sig n)) :
    ∀ κ ε c₀ c₁ : ℝ, 0 < κ → 0 < ε → 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L,
          ‖∑ x : Zd d L, sigMat Sig (smatVar P W L) z n 0 x - ValZ.rowSum Sig P.ψ n z.re W‖ ≤
            (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) := by
  intro κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  obtain ⟨L₁, h₁⟩ := RenormDiff.rowSum d hd P n Sig hn hSig hsh κ ε c₀ c₁ hκ hε hc₀ hc₁ hc
    (τ / 2) hτ2
  obtain ⟨L₂, h₂⟩ := VR1.v2 d hd P n Sig hn hSig hsh κ ε c₀ c₁ hκ hε hc₀ hc₁ hc (τ / 2) hτ2
  refine ⟨max (max L₁ L₂) ⌈(2 : ℝ) ^ (2 / τ)⌉₊, fun W L _ hL hadm z hz => ?_⟩
  have hL₁ : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL₂ : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL₃ : ⌈(2 : ℝ) ^ (2 / τ)⌉₊ ≤ L := le_trans (le_max_right _ _) hL
  have e₁ := h₁ W L hL₁ hadm z hz
  have e₂ := h₂ W L hL₂ hadm z hz
  set A := ∑ x : Zd d L, sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n
    0 x
  set B := ∑ x : Zd d L, sigMat Sig (smatVar P W L) z n 0 x
  set R := ValZ.rowSum Sig P.ψ n z.re W
  set M := z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2))
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hLτ : 0 < (L : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hLpos _
  have hM : 0 ≤ M := by
    have h0 : 0 ≤ (L : ℝ) ^ (τ / 2) * M := by
      rw [show (L : ℝ) ^ (τ / 2) * M = (L : ℝ) ^ (τ / 2) * z.im *
        (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) by simp only [M]; ring]
      exact le_trans (norm_nonneg _) e₁
    exact nonneg_of_mul_nonneg_right (by linarith) hLτ
  have h2 := VR2_two_le_rpow hτ hL₃
  calc ‖B - R‖ = ‖(A - R) - (A - B)‖ := by congr 1; ring
    _ ≤ ‖A - R‖ + ‖A - B‖ := norm_sub_le _ _
    _ ≤ (L : ℝ) ^ (τ / 2) * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) +
          (L : ℝ) ^ (τ / 2) * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) := add_le_add e₂ e₁
    _ = 2 * ((L : ℝ) ^ (τ / 2) * M) := by simp only [M]; ring
    _ ≤ (L : ℝ) ^ (τ / 2) * ((L : ℝ) ^ (τ / 2) * M) := by
          gcongr
    _ = (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) := by
          rw [← mul_assoc, ← Real.rpow_add hLpos, add_halves]; simp only [M]; ring

end Main

section Instances

end Instances

end RBM8D
