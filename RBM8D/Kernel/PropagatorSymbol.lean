import RBM8D.Kernel.Circulant
import RBM8D.Kernel.Propagator

/-!
# Symbols of the propagators

Symmetric and variance kernels, the symbol hypothesis `SymbolClose`, and the symbols of `Θ`, `S^±`.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real kernel on `Z_L^d` that is symmetric and translation invariant, with symbol of
modulus at most one. -/
structure IsSymKernel {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) : Prop where
  symm : ∀ x y, S x y = S y x
  transInv : TransInv S
  norm_symbol_le : ∀ k, ‖symbol (cmat S) k‖ ≤ 1

/-- A variance kernel as in [I, Assumption 1.1]: symmetric, translation invariant,
nonnegative, with row sums one (hence doubly stochastic). -/
structure IsVarKernel {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) : Prop where
  symm : ∀ x y, S x y = S y x
  transInv : TransInv S
  nonneg : ∀ x y, 0 ≤ S x y
  rowSum : ∀ x, ∑ y, S x y = 1

/-- (H3) at one `(W, L)` with the constants `C`: `|Ŝ(p) − ψ(W p)| ≤ C_{D′} W^{−D′}` for every
`D′ ∈ ℕ` and every `p ∈ T_L^d`. -/
def SymbolClose {d L : ℕ} [NeZero L] (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (C : ℕ → ℝ) (W : ℕ)
    (S : Matrix (Zd d L) (Zd d L) ℝ) : Prop :=
  ∀ (D' : ℕ) (k : Zd d L),
    ‖symbol (cmat S) k - (ψ ((W : ℝ) • zfreq k) : ℂ)‖ ≤ C D' / (W : ℝ) ^ D'

/-- The inverse of a translation-invariant kernel is translation invariant. -/
theorem TransInv_ringInverse :
  ∀ {d L : ℕ} [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K),
    TransInv (Ring.inverse K) := by
  intro d L _ K hK
  by_cases hu : IsUnit K
  · intro x y a
    have h1 : K.submatrix (Equiv.addRight a) (Equiv.addRight a) = K := by
      ext u v
      exact hK u v a
    have h2 := Matrix.inv_submatrix_equiv K (Equiv.addRight a) (Equiv.addRight a)
    rw [h1] at h2
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    exact (congrFun (congrFun h2 x) y).symm
  · rw [Ring.inverse_non_unit _ hu]
    intro x y a
    rfl

/-- The symbol of the inverse is the inverse of the symbol. -/
theorem symbol_ringInverse :
  ∀ {d L : ℕ} [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K) (hu : IsUnit K)
    (k : Zd d L), symbol (Ring.inverse K) k = (symbol K k)⁻¹ := by
  intro d L _ K hK hu k
  have h := symbol_mul K (Ring.inverse K) hK (TransInv_ringInverse K hK) k
  rw [Ring.mul_inverse_cancel K hu, symbol_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- A variance kernel is a symmetric kernel. -/
theorem IsVarKernel_isSymKernel :
  ∀ {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : IsVarKernel S), IsSymKernel S := by
  intro d L _ S hS
  refine ⟨hS.symm, hS.transInv, fun k => ?_⟩
  calc ‖symbol (cmat S) k‖ ≤ ∑ x, ‖cmat S 0 x * zchar k x‖ := norm_sum_le _ _
    _ = ∑ x, S 0 x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [norm_mul, norm_zchar, mul_one]
      simp [cmat, abs_of_nonneg (hS.nonneg 0 x)]
    _ = 1 := hS.rowSum 0

private theorem zchar_zero_right' [NeZero L] {d : ℕ} (k : Zd d L) : zchar k 0 = 1 := by
  simp [zchar]

private theorem zchar_neg_eq_conj [NeZero L] {d : ℕ} (k x : Zd d L) :
    zchar k (-x) = conj (zchar k x) := by
  have h1 : zchar k x * zchar k (-x) = 1 := by
    rw [← zchar_add, add_neg_cancel, zchar_zero_right']
  have h2 : conj (zchar k x) * zchar k x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_zchar]
    simp
  have hne : zchar k x ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  exact mul_left_cancel₀ hne (h1.trans (by rw [mul_comm]; exact h2.symm))

/-- The symbol of a real symmetric translation-invariant kernel is real. -/
theorem symbol_cmat_im :
  ∀ {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (hsymm : ∀ x y, S x y = S y x)
    (hS : TransInv S) (k : Zd d L), (symbol (cmat S) k).im = 0 := by
  intro d L _ S hsymm hS k
  have hneg : ∀ x, S 0 (-x) = S 0 x := fun x => by
    have := hS 0 (-x) x
    rw [zero_add, neg_add_cancel] at this
    rw [← this, hsymm]
  have h : conj (symbol (cmat S) k) = symbol (cmat S) k := by
    simp only [symbol, map_sum, map_mul, ← zchar_neg_eq_conj]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ fun x => ?_
    simp [cmat, hneg]
  exact Complex.conj_eq_iff_im.mp h

private theorem transInv_one' [NeZero L] {d : ℕ} : TransInv (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
  intro x y a
  simp [Matrix.one_apply]

private theorem transInv_cmat {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS : TransInv S) : TransInv (cmat S) := by
  intro x y a
  simp [cmat, hS x y a]

private theorem transInv_smul' {d L : ℕ} [NeZero L] (w : ℂ) (K : Matrix (Zd d L) (Zd d L) ℂ)
    (hK : TransInv K) : TransInv (w • K) := by
  intro x y a
  simp [hK x y a]

private theorem transInv_sub' {d L : ℕ} [NeZero L] (K K' : Matrix (Zd d L) (Zd d L) ℂ)
    (hK : TransInv K) (hK' : TransInv K') : TransInv (K - K') := by
  intro x y a
  simp [hK x y a, hK' x y a]

private theorem transInv_one_sub_smul {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS : TransInv S) (w : ℂ) : TransInv (1 - w • cmat S) :=
  transInv_sub' _ _ transInv_one' (transInv_smul' _ _ (transInv_cmat S hS))

private theorem symbol_one_sub_smul {d L : ℕ} [NeZero L] (C : Matrix (Zd d L) (Zd d L) ℂ) (w : ℂ)
    (k : Zd d L) : symbol (1 - w • C) k = 1 - w * symbol C k := by
  have h : (1 - w • C) = 1 + (-1 : ℂ) • (w • C) := by
    rw [neg_one_smul, sub_eq_add_neg]
  have h1 := (symbol_add_smul (1 : Matrix (Zd d L) (Zd d L) ℂ) ((-1 : ℂ) • (w • C)) 1 k).1
  have h2 := (symbol_add_smul (w • C) (w • C) (-1) k).2
  have h3 := (symbol_add_smul C C w k).2
  rw [h, h1, symbol_one, h2, h3]
  ring

/-- The symbol of a product `(wC)(1 − wC)⁻¹` for a translation-invariant `C`. -/
private theorem symbol_core {d L : ℕ} [NeZero L] (C : Matrix (Zd d L) (Zd d L) ℂ)
    (hC : TransInv C) (w : ℂ) (hw : ∀ k, w * symbol C k ≠ 1) (k : Zd d L) :
    symbol ((w • C) * Ring.inverse (1 - w • C)) k = w * symbol C k / (1 - w * symbol C k) := by
  have hB : TransInv (1 - w • C) := transInv_sub' _ _ transInv_one' (transInv_smul' _ _ hC)
  have hu : IsUnit (1 - w • C) := by
    rw [isUnit_iff_symbol _ hB]
    intro j
    rw [symbol_one_sub_smul, sub_ne_zero, ne_comm]
    exact hw j
  rw [symbol_mul _ _ (transInv_smul' _ _ hC) (TransInv_ringInverse _ hB),
    symbol_ringInverse _ hB hu, symbol_one_sub_smul, (symbol_add_smul C C w k).2, div_eq_mul_inv]

/-- The symbol of `S^+`: `m² Ŝ / (1 − m² Ŝ)`. -/
theorem symbol_Splus :
  ∀ {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : TransInv S) (m : ℂ)
    (hm : ∀ k, m ^ 2 * symbol (cmat S) k ≠ 1) (k : Zd d L),
    symbol (Splus m S) k = m ^ 2 * symbol (cmat S) k / (1 - m ^ 2 * symbol (cmat S) k) := by
  intro d L _ S hS m hm k
  exact symbol_core (cmat S) (transInv_cmat S hS) (m ^ 2) hm k

private theorem cmat_ringInverse (B : Matrix ι ι ℝ) :
    cmat (Ring.inverse B) = Ring.inverse (cmat B) := by
  let f : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  change f (Ring.inverse B) = Ring.inverse (f B)
  by_cases h : IsUnit B
  · obtain ⟨u, rfl⟩ := h
    have : f (u : Matrix ι ι ℝ) = ((Units.map f.toMonoidHom u : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) :=
      rfl
    rw [this, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have h' : ¬ IsUnit (f B) := by
      intro h2
      apply h
      rw [Matrix.isUnit_iff_isUnit_det] at h2 ⊢
      rw [isUnit_iff_ne_zero] at h2 ⊢
      intro h0
      apply h2
      have := RingHom.map_det Complex.ofRealHom B
      change Complex.ofRealHom B.det = (f B).det at this
      rw [← this, h0, map_zero]
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h']
    ext i j
    simp

private theorem cmat_Theta {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (m : ℂ) :
    cmat (Theta m S) =
      (((‖m‖ : ℂ) ^ 2) • cmat S) * Ring.inverse (1 - ((‖m‖ : ℂ) ^ 2) • cmat S) := by
  have h1 : ∀ T : Matrix (Zd d L) (Zd d L) ℝ,
      cmat (‖m‖ ^ 2 • T) = ((‖m‖ : ℂ) ^ 2) • cmat T := fun T => by
    ext i j
    simp [cmat]
  have h2 : cmat (1 - ‖m‖ ^ 2 • S) = 1 - ((‖m‖ : ℂ) ^ 2) • cmat S := by
    ext i j
    simp only [cmat, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
    split_ifs <;> simp
  have h3 : ∀ A B : Matrix (Zd d L) (Zd d L) ℝ, cmat (A * B) = cmat A * cmat B := fun A B =>
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [Theta, h3, cmat_ringInverse, h1, h2]

/-- The symbol of `Θ`: `|m|² Ŝ / (1 − |m|² Ŝ)` (display after [I, (1.30)]). -/
theorem symbol_Theta :
  ∀ {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : TransInv S) (m : ℂ)
    (hm : ∀ k, (‖m‖ ^ 2 : ℂ) * symbol (cmat S) k ≠ 1) (k : Zd d L),
    symbol (cmat (Theta m S)) k =
      (‖m‖ ^ 2 : ℂ) * symbol (cmat S) k / (1 - (‖m‖ ^ 2 : ℂ) * symbol (cmat S) k) := by
  intro d L _ S hS m hm k
  rw [cmat_Theta]
  exact symbol_core (cmat S) (transInv_cmat S hS) _ hm k

/-- `S^+`, `S^-` and `Θ` are translation invariant. -/
theorem TransInv_propagators :
  ∀ {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : TransInv S) (m : ℂ),
    TransInv (Splus m S) ∧ TransInv (Sminus m S) ∧ TransInv (Theta m S) := by
  intro d L _ S hS m
  have hC := transInv_cmat S hS
  have key : ∀ w : ℂ, TransInv ((w • cmat S) * Ring.inverse (1 - w • cmat S)) := fun w =>
    TransInv_mul _ _ (transInv_smul' _ _ hC)
      (TransInv_ringInverse _ (transInv_one_sub_smul S hS w))
  have hp : TransInv (Splus m S) := key (m ^ 2)
  refine ⟨hp, ?_, ?_⟩
  · intro x y a
    simp only [Sminus, Matrix.map_apply, hp x y a]
  · intro x y a
    have h := key ((‖m‖ : ℂ) ^ 2) x y a
    rw [← cmat_Theta] at h
    simpa [cmat] using h

section Witness

end Witness

end RBM8D
