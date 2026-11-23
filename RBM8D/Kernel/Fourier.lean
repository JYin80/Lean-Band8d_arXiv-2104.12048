module

public import RBM8D.MainDefs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import RBM8D.Basic.Lattice
public import RBM8D.Basic.Semicircle
public import RBM8D.Prob.StochDom

@[expose] public section

/-!
# Fourier analysis on `Z_L^d`

Characters, the discrete Fourier transform, inversion and Plancherel.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d L : ℕ}

/-- The discrete Fourier transform `f̂(k) = Σ_x e^{i p·x} f(x)`, `p = 2πk/L`. -/
def zdft [NeZero L] (f : Zd d L → ℂ) (k : Zd d L) : ℂ := ∑ x, zchar k x * f x

/-- The characters of `Z_L^d` are additive in the space variable. -/
theorem zchar_add :
  ∀ {d L : ℕ} [NeZero L] (k x y : Zd d L), zchar k (x + y) = zchar k x * zchar k y := by
  intro d L _ k x y
  simp only [zchar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

/-- The pairing `zchar k x` is symmetric in the frequency `k` and the point `x`. -/
theorem zchar_comm :
  ∀ {d L : ℕ} [NeZero L] (k x : Zd d L), zchar k x = zchar x k := by
  intro d L _ k x
  simp only [zchar, mul_comm (k _)]

/-- The characters of `Z_L^d` have modulus one. -/
theorem norm_zchar :
  ∀ {d L : ℕ} [NeZero L] (k x : Zd d L), ‖zchar k x‖ = 1 := by
  intro d L _ k x
  simp [zchar, norm_prod, AddChar.norm_apply]

/-- Orthogonality of the characters: `Σ_x e^{i p·x} = L^d δ_{k0}` ([I, App B]). -/
theorem sum_zchar :
  ∀ {d L : ℕ} [NeZero L] (k : Zd d L), ∑ x, zchar k x = if k = 0 then (L : ℂ) ^ d else 0 := by
  intro d L _ k
  have h1 : ∑ x : Zd d L, zchar k x = ∏ i, ∑ a : ZMod L, ZMod.stdAddChar (k i * a) := by
    rw [Fintype.prod_sum]
    rfl
  have h2 : ∀ i, ∑ a : ZMod L, (ZMod.stdAddChar (N := L)) (k i * a)
      = if k i = 0 then (L : ℂ) else 0 := by
    intro i
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar (N := L))) (k i)
      (ZMod.isPrimitive_stdAddChar L)
    simpa [mul_comm, ZMod.card] using this
  rw [h1]
  simp only [h2]
  by_cases hk : k = 0
  · subst hk; simp
  · obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (funext h)
    simpa [hk] using Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- Fourier inversion on `Z_L^d` with the normalisation `L^{-d}`. -/
theorem zdft_inversion :
  ∀ {d L : ℕ} [NeZero L] (f : Zd d L → ℂ) (x : Zd d L),
    f x = ((L : ℂ) ^ d)⁻¹ * ∑ k, zdft f k * zchar k (-x) := by
  intro d L _ f x
  have hL : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  have key : ∑ k : Zd d L, zdft f k * zchar k (-x) = (L : ℂ) ^ d * f x := by
    simp only [zdft, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ y : Zd d L, ∑ k : Zd d L, zchar k y * f y * zchar k (-x)
        = f y * (if y - x = 0 then (L : ℂ) ^ d else 0) := by
      intro y
      rw [← sum_zchar (y - x), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zchar_comm (y - x) k, sub_eq_add_neg, zchar_add]
      ring
    simp only [this, sub_eq_zero]
    simp [mul_comm]
  rw [key]
  field_simp

/-- Plancherel on `Z_L^d`: `Σ_x |f(x)|² = L^{-d} Σ_k |f̂(k)|²`. -/
theorem zdft_plancherel :
  ∀ {d L : ℕ} [NeZero L] (f : Zd d L → ℂ),
    ∑ x, ‖f x‖ ^ 2 = ((L : ℝ) ^ d)⁻¹ * ∑ k, ‖zdft f k‖ ^ 2 := by
  intro d L _ f
  have hL : ((L : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  have hconj : ∀ k x : Zd d L, conj (zchar k x) = zchar k (-x) := by
    intro k x
    have h1 : zchar k x * zchar k (-x) = 1 := by
      rw [← zchar_add]; simp [zchar]
    have h2 : conj (zchar k x) * zchar k x = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_zchar]; simp
    have hne : zchar k x ≠ 0 := by
      intro h; rw [h] at h1; simp at h1
    exact mul_left_cancel₀ hne (by rw [h1, mul_comm]; exact h2)
  have hsum : ∀ x y : Zd d L, ∑ k : Zd d L, zchar k (x - y)
      = if x = y then (L : ℂ) ^ d else 0 := by
    intro x y
    simp_rw [zchar_comm _ (x - y)]
    rw [sum_zchar]
    simp only [sub_eq_zero]
  have hC : ((∑ k : Zd d L, ‖zdft f k‖ ^ 2 : ℝ) : ℂ)
      = (L : ℂ) ^ d * ((∑ x : Zd d L, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    have e1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
      intro z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.ofReal_sum, Complex.ofReal_sum]
    simp_rw [e1]
    have e2 : ∀ k : Zd d L, zdft f k * conj (zdft f k)
        = ∑ x : Zd d L, ∑ y : Zd d L, (f x * conj (f y)) * zchar k (x - y) := by
      intro k
      simp only [zdft, map_sum]
      rw [Finset.sum_mul_sum]
      simp only [map_mul, hconj]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [sub_eq_add_neg, zchar_add]
      ring
    simp_rw [e2]
    have e3 : ∀ x y : Zd d L, ∑ k : Zd d L, (f x * conj (f y)) * zchar k (x - y)
        = (f x * conj (f y)) * (if x = y then (L : ℂ) ^ d else 0) := by
      intro x y
      rw [← Finset.mul_sum, hsum]
    calc ∑ k : Zd d L, ∑ x : Zd d L, ∑ y : Zd d L, (f x * conj (f y)) * zchar k (x - y)
        = ∑ x : Zd d L, ∑ y : Zd d L, ∑ k : Zd d L, (f x * conj (f y)) * zchar k (x - y) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = (L : ℂ) ^ d * ∑ x : Zd d L, f x * conj (f x) := by
          simp only [e3, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
  have hR : ∑ k : Zd d L, ‖zdft f k‖ ^ 2 = (L : ℝ) ^ d * ∑ x : Zd d L, ‖f x‖ ^ 2 := by
    exact_mod_cast hC
  rw [hR]
  field_simp

end RBM8D
