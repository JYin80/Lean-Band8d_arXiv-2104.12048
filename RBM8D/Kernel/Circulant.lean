import RBM8D.Kernel.Fourier

/-!
# Translation-invariant kernels and their symbols

Circulant matrices on `Z_L^d` are diagonalised by the characters; the symbol is multiplicative.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d L : ℕ}

/-- Translation invariance of a kernel on `Z_L^d`: `K(x + a, y + a) = K(x, y)`. -/
def TransInv {R : Type*} (K : Matrix (Zd d L) (Zd d L) R) : Prop :=
  ∀ x y a, K (x + a) (y + a) = K x y

/-- The symbol `K̂(p) = Σ_x K_{0x} e^{i p·x}` of a kernel on `Z_L^d` (display after [I, (1.30)]). -/
def symbol [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (k : Zd d L) : ℂ :=
  ∑ x, K 0 x * zchar k x

/-- A translation-invariant kernel depends only on the difference of its arguments. -/
private theorem transInv_apply {R : Type*} {K : Matrix (Zd d L) (Zd d L) R} (hK : TransInv K)
    (x y : Zd d L) : K x y = K 0 (y - x) := by
  have := hK x y (-x)
  rw [add_neg_cancel, ← sub_eq_add_neg] at this
  exact this.symm

private theorem zchar_neg_right [NeZero L] (k y : Zd d L) : zchar k (-y) = zchar (-k) y := by
  simp [zchar]

private theorem zchar_zero_right [NeZero L] (k : Zd d L) : zchar k 0 = 1 := by
  simp [zchar]

private theorem zchar_ne_zero [NeZero L] (k x : Zd d L) : zchar k x ≠ 0 := by
  intro h
  have := norm_zchar k x
  rw [h] at this
  simp at this

/-- Orthogonality of the characters in the frequency variable. -/
private theorem sum_zchar_freq [NeZero L] (x y : Zd d L) :
    ∑ k : Zd d L, zchar k (x - y) = if x = y then (L : ℂ) ^ d else 0 := by
  simp_rw [zchar_comm _ (x - y)]
  rw [sum_zchar]
  simp only [sub_eq_zero]

theorem mulVec_zchar :
  ∀ {d L : ℕ} [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K) (k : Zd d L),
    K *ᵥ zchar k = symbol K k • zchar k := by
  intro d L _ K hK k
  funext x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, symbol]
  rw [Finset.sum_mul]
  refine (Fintype.sum_equiv (Equiv.addRight x) _ _ fun z => ?_).symm
  simp only [Equiv.coe_addRight]
  rw [transInv_apply hK x (z + x), add_sub_cancel_right, zchar_add]
  ring

/-- Products of translation-invariant kernels are translation invariant. -/
theorem TransInv_mul :
  ∀ {d L : ℕ} [NeZero L] (K K' : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K)
    (hK' : TransInv K'), TransInv (K * K') := by
  intro d L _ K K' hK hK' x y a
  simp only [Matrix.mul_apply]
  refine (Fintype.sum_equiv (Equiv.addRight a) _ _ fun z => ?_).symm
  simp only [Equiv.coe_addRight]
  rw [hK x z a, hK' z y a]

/-- The symbol is multiplicative on translation-invariant kernels. -/
theorem symbol_mul :
  ∀ {d L : ℕ} [NeZero L] (K K' : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K)
    (hK' : TransInv K') (k : Zd d L), symbol (K * K') k = symbol K k * symbol K' k := by
  intro d L _ K K' hK hK' k
  have h2 : (K * K') *ᵥ zchar k = (symbol K k * symbol K' k) • zchar k := by
    rw [← Matrix.mulVec_mulVec, mulVec_zchar K' hK', Matrix.mulVec_smul, mulVec_zchar K hK,
      smul_smul, mul_comm]
  have h4 := congrFun (mulVec_zchar (K * K') (TransInv_mul K K' hK hK') k) 0
  rw [h2] at h4
  simpa [zchar_zero_right] using h4.symm

/-- The symbol of the identity is `1`. -/
theorem symbol_one :
  ∀ {d L : ℕ} [NeZero L] (k : Zd d L), symbol (1 : Matrix (Zd d L) (Zd d L) ℂ) k = 1 := by
  intro d L _ k
  simp [symbol, Matrix.one_apply, zchar_zero_right]

/-- The symbol is additive and homogeneous. -/
theorem symbol_add_smul :
  ∀ {d L : ℕ} [NeZero L] (K K' : Matrix (Zd d L) (Zd d L) ℂ) (w : ℂ) (k : Zd d L),
    symbol (K + K') k = symbol K k + symbol K' k ∧ symbol (w • K) k = w * symbol K k := by
  intro d L _ K K' w k
  constructor
  · simp [symbol, add_mul, Finset.sum_add_distrib]
  · simp [symbol, Finset.mul_sum, mul_assoc]

/-- A translation-invariant kernel is recovered from its symbol by Fourier inversion. -/
theorem kernel_inversion :
  ∀ {d L : ℕ} [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K) (x y : Zd d L),
    K x y = ((L : ℂ) ^ d)⁻¹ * ∑ k, symbol K k * zchar k (x - y) := by
  intro d L _ K hK x y
  have h := zdft_inversion (K 0) (y - x)
  have hs : ∀ k, zdft (K 0) k = symbol K k := fun k => by
    simp only [zdft, symbol, mul_comm]
  simp only [hs, neg_sub] at h
  rw [transInv_apply hK x y]
  exact h

theorem isUnit_iff_symbol :
  ∀ {d L : ℕ} [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K),
    IsUnit K ↔ ∀ k, symbol K k ≠ 0 := by
  intro d L _ K hK
  have hL : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  constructor
  · rintro ⟨u, rfl⟩ k hk
    have h1 : (u : Matrix (Zd d L) (Zd d L) ℂ) *ᵥ zchar k = 0 := by
      rw [mulVec_zchar _ hK, hk, zero_smul]
    have h2 : zchar k = 0 := by
      have := congrArg (Matrix.mulVec (↑u⁻¹ : Matrix (Zd d L) (Zd d L) ℂ)) h1
      simpa [Matrix.mulVec_mulVec, Matrix.mulVec_zero] using this
    exact zchar_ne_zero k 0 (by rw [h2]; rfl)
  · intro hs
    set K' : Matrix (Zd d L) (Zd d L) ℂ :=
      Matrix.of fun x y => ((L : ℂ) ^ d)⁻¹ * ∑ k, (symbol K k)⁻¹ * zchar k (x - y) with hK'def
    have hK' : TransInv K' := by
      intro x y a
      simp [hK'def]
    have hsym : ∀ j, symbol K' j = (symbol K j)⁻¹ := by
      intro j
      have e : ∀ y, K' 0 y * zchar j y =
          ∑ k, ((L : ℂ) ^ d)⁻¹ * (symbol K k)⁻¹ * (zchar (-k) y * zchar j y) := by
        intro y
        simp only [hK'def, Matrix.of_apply, zero_sub, zchar_neg_right, Finset.mul_sum,
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      have f : ∀ k : Zd d L, ∑ y : Zd d L, ((L : ℂ) ^ d)⁻¹ * (symbol K k)⁻¹ *
          (zchar (-k) y * zchar j y) = ((L : ℂ) ^ d)⁻¹ * (symbol K k)⁻¹ *
            (if j - k = 0 then (L : ℂ) ^ d else 0) := by
        intro k
        rw [← sum_zchar (j - k), Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [zchar_comm (j - k) y, sub_eq_add_neg, zchar_comm j y, zchar_comm (-k) y,
          zchar_add]
        ring
      change ∑ y, K' 0 y * zchar j y = _
      rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_comm]
      simp only [f]
      rw [Finset.sum_eq_single j]
      · simp only [sub_self, ↓reduceIte]
        field_simp
      · intro k _ hkj
        simp [sub_eq_zero, Ne.symm hkj]
      · simp
    have hmul : ∀ (A B : Matrix (Zd d L) (Zd d L) ℂ), TransInv A → TransInv B →
        (∀ k, symbol A k * symbol B k = 1) → A * B = 1 := by
      intro A B hA hB hAB
      ext x y
      rw [kernel_inversion _ (TransInv_mul A B hA hB) x y]
      simp only [symbol_mul A B hA hB, hAB, one_mul, sum_zchar_freq]
      by_cases hxy : x = y
      · subst hxy; simp [hL]
      · simp [hxy]
    have h1 : K * K' = 1 := hmul K K' hK hK' fun k => by
      rw [hsym]; exact mul_inv_cancel₀ (hs k)
    have h2 : K' * K = 1 := hmul K' K hK' hK fun k => by
      rw [hsym]; exact inv_mul_cancel₀ (hs k)
    exact ⟨⟨K, K', h1, h2⟩, rfl⟩

section Witness

end Witness

end RBM8D
