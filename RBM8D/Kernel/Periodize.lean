import Mathlib.Algebra.Module.ZLattice.Summable
import RBM8D.Kernel.Lattice

/-!
# Periodisation

The torus `Z_L^d` and `ℤ^d`: lifts, casts, the frequencies of `T_L^d` in `[-π, π]^d`, and the exact periodisation of a summable kernel.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d L : ℕ}

/-- The representative `[x]_L ∈ (-L/2, L/2]^d` of `x ∈ Z_L^d`. -/
def zlift (x : Zd d L) : Fin d → ℤ := fun i => (x i).valMinAbs

/-- The reduction `ℤ^d → Z_L^d`. -/
def zcast (L : ℕ) (x : Fin d → ℤ) : Zd d L := fun i => (x i : ZMod L)

/-- The frequency `p = 2πk/L ∈ (-π, π]^d` as a point of `ℝ^d` (coordinates of `zfreq k`). -/
def zfreqPi (k : Zd d L) : Fin d → ℝ := fun i => 2 * Real.pi * ((k i).valMinAbs : ℝ) / L

/-- The periodisation `Σ_{n ∈ ℤ^d} K([x]_L + L n)` of a kernel on `ℤ^d`. -/
def periodize (L : ℕ) (K : (Fin d → ℤ) → ℂ) (x : Zd d L) : ℂ :=
  ∑' n : Fin d → ℤ, K (zlift x + (L : ℤ) • n)

/-- The character at the reduction of `y ∈ ℤ^d` is the plane wave at the centred frequency. -/
private theorem zchar_zcast [NeZero L] (k : Zd d L) (y : Fin d → ℤ) :
    zchar k (zcast L y) = zexp (zfreqPi k) y := by
  unfold zchar zexp
  have h : ∀ i, ZMod.stdAddChar (k i * zcast L y i) =
      Complex.exp (((2 * Real.pi * ((k i).valMinAbs : ℝ) / L * (y i : ℝ) : ℝ) : ℂ) * I) := by
    intro i
    have h1 : k i * zcast L y i = (((k i).valMinAbs * y i : ℤ) : ZMod L) := by
      push_cast
      rfl
    rw [h1, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  simp only [zfreqPi]
  push_cast
  rfl

/-- The reduction of `[x]_L + L n` is `x`. -/
private theorem zcast_zlift_add_smul (x : Zd d L) (n : Fin d → ℤ) :
    zcast L (zlift x + (L : ℤ) • n) = x := by
  funext i
  simp [zcast, zlift, ZMod.coe_valMinAbs]

/-- The points of `ℤ^d` reducing to `x` are exactly `[x]_L + L n`, `n ∈ ℤ^d`. -/
private theorem exists_eq_zlift_add_smul (x : Zd d L) (y : Fin d → ℤ) (h : zcast L y = x) :
    ∃ n : Fin d → ℤ, zlift x + (L : ℤ) • n = y := by
  have hi : ∀ i, ∃ m : ℤ, y i - zlift x i = L * m := by
    intro i
    have h1 : ((zlift x i : ℤ) : ZMod L) = ((y i : ℤ) : ZMod L) := by
      have := congrFun h i
      simp only [zcast] at this
      simp [zlift, ZMod.coe_valMinAbs, this]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  choose n hn using hi
  refine ⟨n, funext fun i => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith [hn i]

/-- Periodisation in Fourier space: for a summable kernel `K` on `ℤ^d`,
`Σ_n K([x]_L + L n) = L^{-d} Σ_{p ∈ T_L^d} K̂(p) e^{-ip·x}`, with `p = 2πk/L ∈ (-π, π]^d`
([I, App B]). -/
theorem periodize_eq :
  ∀ {d L : ℕ} [NeZero L] (K : (Fin d → ℤ) → ℂ) (hK : Summable fun x => ‖K x‖) (x : Zd d L),
    periodize L K x = ((L : ℂ) ^ d)⁻¹ * ∑ k, zdSeries K (zfreqPi k) * zchar k (-x) := by
  intro d L _ K hK x
  have hL : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  -- the double sum over `k` and `y`
  have hsum : ∀ k : Zd d L,
      Summable fun y : Fin d → ℤ => K y * zexp (zfreqPi k) y * zchar k (-x) := by
    intro k
    refine Summable.of_norm_bounded hK fun y => ?_
    simp [norm_zexp, norm_zchar]
  have h1 : ∑ k : Zd d L, zdSeries K (zfreqPi k) * zchar k (-x) =
      ∑' y : Fin d → ℤ, K y * ∑ k : Zd d L, zchar k (zcast L y - x) := by
    simp_rw [zdSeries, ← tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun k _ => hsum k)]
    refine tsum_congr fun y => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sub_eq_add_neg, zchar_add, zchar_zcast, mul_assoc]
  have h2 : ∀ y : Fin d → ℤ, ∑ k : Zd d L, zchar k (zcast L y - x) =
      if zcast L y = x then (L : ℂ) ^ d else 0 := by
    intro y
    simp_rw [zchar_comm _ (zcast L y - x)]
    rw [sum_zchar]
    simp only [sub_eq_zero]
  simp_rw [h2] at h1
  have h3 : ∑' y : Fin d → ℤ, K y * (if zcast L y = x then (L : ℂ) ^ d else 0) =
      (L : ℂ) ^ d * periodize L K x := by
    have hinj : Function.Injective fun n : Fin d → ℤ => zlift x + (L : ℤ) • n := by
      intro a b hab
      have hL' : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
      funext i
      have := congrFun hab i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
      exact mul_left_cancel₀ hL' this
    have hsupp : Function.support (fun y : Fin d → ℤ =>
        K y * (if zcast L y = x then (L : ℂ) ^ d else 0)) ⊆
        Set.range fun n : Fin d → ℤ => zlift x + (L : ℤ) • n := by
      intro y hy
      have hy' : zcast L y = x := by
        by_contra hne
        exact hy (by simp [hne])
      obtain ⟨n, hn⟩ := exists_eq_zlift_add_smul x y hy'
      exact ⟨n, hn⟩
    rw [← hinj.tsum_eq hsupp]
    unfold periodize
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [zcast_zlift_add_smul, ite_true]
    ring
  rw [h1, h3]
  field_simp

/-- The weight `|n|_∞^{-M}` is summable over `ℤ^d` for `M > d` (and vanishes at `n = 0`). -/
private theorem summable_zdInf_inv_pow (d M : ℕ) (hM : d < M) :
    Summable fun n : Fin d → ℤ => (((zdInf n : ℕ) : ℝ) ^ M)⁻¹ := by
  let Λ : Submodule ℤ (Fin d → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))
  have hΛ : ∀ n : Fin d → ℤ, (fun i => (n i : ℝ)) ∈ Λ := by
    intro n
    refine ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ _).mpr fun i => ⟨n i, ?_⟩
    simp
  let g : (Fin d → ℤ) → Λ := fun n => ⟨fun i => (n i : ℝ), hΛ n⟩
  have hg : Function.Injective g := by
    intro a b hab
    funext i
    have := congrFun (congrArg Subtype.val hab) i
    simp only [g] at this
    exact_mod_cast this
  have hrank : Module.finrank ℤ Λ = d := by
    rw [ZLattice.rank ℝ Λ]
    simp
  have hs := ZLattice.summable_norm_rpow Λ (-(M : ℝ))
    (by rw [hrank]; exact_mod_cast (by omega : -(M : ℤ) < -d))
  have hcomp := hs.comp_injective hg
  refine hcomp.congr fun n => ?_
  have hnorm : ‖g n‖ = ((zdInf n : ℕ) : ℝ) := by
    have h1 : ‖g n‖ = ‖(fun i => (n i : ℝ))‖ := rfl
    rw [h1]
    refine le_antisymm ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr fun i => ?_
      rw [Real.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs]
      exact_mod_cast Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ i)
    · refine (Nat.floor_le (norm_nonneg _)).trans' ?_
      refine Nat.cast_le.mpr (Finset.sup_le fun i _ => Nat.le_floor ?_)
      have h2 : (((n i).natAbs : ℕ) : ℝ) = ‖(n i : ℝ)‖ := by simp
      rw [h2]
      exact norm_le_pi_norm (fun i => (n i : ℝ)) i
  simp only [Function.comp, hnorm]
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]

/-- The wrap-around lower bound: `|[x]_L + L n|_∞ ≥ L |n|_∞ / 2` for `n ≠ 0`. -/
private theorem zdInf_zlift_add_smul_ge [NeZero L] (x : Zd d L) (n : Fin d → ℤ) (hn : n ≠ 0) :
    L * zdInf n ≤ 2 * zdInf (zlift x + (L : ℤ) • n) := by
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    ⟨j, Finset.mem_univ j⟩ (fun i => (n i).natAbs)
  have hni : (n i).natAbs = zdInf n := hi.symm
  have hn1 : 1 ≤ (n i).natAbs := by
    rw [hni]
    have : (n j).natAbs ≤ zdInf n := Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ j)
    omega
  have hv : 2 * (zlift x i).natAbs ≤ L := by
    have := ZMod.natAbs_valMinAbs_le (x i)
    simp only [zlift]
    omega
  have hle : ((zlift x + (L : ℤ) • n) i).natAbs ≤ zdInf (zlift x + (L : ℤ) • n) :=
    Finset.le_sup (f := fun i => ((zlift x + (L : ℤ) • n) i).natAbs) (Finset.mem_univ i)
  have hmain : L * (n i).natAbs ≤ 2 * ((zlift x + (L : ℤ) • n) i).natAbs := by
    have e1 : ((zlift x + (L : ℤ) • n) i) = zlift x i + (L : ℤ) * n i := by simp
    rw [e1]
    have e2 : ((L : ℤ) * n i).natAbs = L * (n i).natAbs := by
      rw [Int.natAbs_mul]; simp
    have h3 := Int.natAbs_add_le (zlift x i + (L : ℤ) * n i) (-(zlift x i))
    have e3 : zlift x i + (L : ℤ) * n i + -zlift x i = (L : ℤ) * n i := by ring
    rw [e3, Int.natAbs_neg, e2] at h3
    nlinarith
  rw [← hni]
  omega

/-- The `ℓ^∞` norm of a nonzero point of `ℤ^d` is positive. -/
private theorem zdInf_pos_of_ne_zero {n : Fin d → ℤ} (hn : n ≠ 0) : 0 < zdInf n := by
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have : (n j).natAbs ≤ zdInf n := Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ j)
  have : 0 < (n j).natAbs := Int.natAbs_pos.mpr hj
  omega

/-- Termwise bound for `n ≠ 0`:
`(1 + |[x]_L + L n|/R)^{-M} ≤ 2^M (R/L)^M |n|_∞^{-M}`. -/
private theorem periodize_term_le [NeZero L] (M : ℕ) (R : ℝ) (hR : 0 < R) (x : Zd d L)
    (n : Fin d → ℤ) (hn : n ≠ 0) :
    ((1 + (zdInf (zlift x + (L : ℤ) • n) : ℝ) / R) ^ M)⁻¹ ≤
      2 ^ M * (R / L) ^ M * (((zdInf n : ℕ) : ℝ) ^ M)⁻¹ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have ha : (0 : ℝ) < ((zdInf n : ℕ) : ℝ) := by exact_mod_cast zdInf_pos_of_ne_zero hn
  have hge : (L : ℝ) * ((zdInf n : ℕ) : ℝ) ≤ 2 * ((zdInf (zlift x + (L : ℤ) • n) : ℕ) : ℝ) := by
    exact_mod_cast zdInf_zlift_add_smul_ge x n hn
  set b : ℝ := (L : ℝ) * ((zdInf n : ℕ) : ℝ) / (2 * R) with hb
  have hbpos : 0 < b := by positivity
  have hb1 : b ≤ 1 + (zdInf (zlift x + (L : ℤ) • n) : ℝ) / R := by
    have h1 : b ≤ ((zdInf (zlift x + (L : ℤ) • n) : ℕ) : ℝ) / R := by
      rw [hb, div_le_div_iff₀ (by positivity) hR]
      nlinarith
    have : (0 : ℝ) ≤ 1 := zero_le_one
    linarith
  calc ((1 + (zdInf (zlift x + (L : ℤ) • n) : ℝ) / R) ^ M)⁻¹ ≤ (b ^ M)⁻¹ :=
        inv_anti₀ (pow_pos hbpos M) (pow_le_pow_left₀ hbpos.le hb1 M)
    _ = 2 ^ M * (R / L) ^ M * (((zdInf n : ℕ) : ℝ) ^ M)⁻¹ := by
        have h2 : ((zdInf n : ℕ) : ℝ) = b * 2 * (R / L) := by
          rw [hb]
          field_simp
        have hRL : (0 : ℝ) < R / L := by positivity
        rw [h2, mul_pow, mul_pow]
        field_simp

/-- The terms `(1 + |[x]_L + L n|/R)^{-M}`, `n ≠ 0`, are summable for `M ≥ d + 1`. -/
private theorem periodize_term_summable [NeZero L] (d M : ℕ) (hM : d + 1 ≤ M) (R : ℝ) (hR : 0 < R)
    (x : Zd d L) :
    Summable fun n : {n : Fin d → ℤ // n ≠ 0} =>
      ((1 + (zdInf (zlift x + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹ := by
  have hs := summable_zdInf_inv_pow d M (by omega)
  have hsub : Summable fun n : {n : Fin d → ℤ // n ≠ 0} => (((zdInf n.1 : ℕ) : ℝ) ^ M)⁻¹ :=
    hs.subtype _
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => periodize_term_le M R hR x n.1 n.2) (hsub.mul_left (2 ^ M * (R / L) ^ M))

/-- The image sum: `Σ_{n ≠ 0} (1 + |[x]_L + L n|/R)^{-M} ≤ C_{d,M} (R/L)^M` for `M ≥ d + 1` and
`0 < R ≤ L`, with `C_{d,M}` independent of `L`, `R` and `x`. These are the wrap-around terms of the
periodisation in the decay bound [I, (1.17)]. -/
theorem tsum_periodize_le :
  ∀ (d M : ℕ) (hM : d + 1 ≤ M), ∃ C : ℝ, ∀ (L : ℕ) [NeZero L] (R : ℝ), 0 < R → R ≤ L →
    ∀ x : Zd d L,
      ∑' n : {n : Fin d → ℤ // n ≠ 0},
          ((1 + (zdInf (zlift x + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹ ≤ C * (R / L) ^ M := by
  intro d M hM
  have hs := summable_zdInf_inv_pow d M (by omega)
  refine ⟨2 ^ M * ∑' n : Fin d → ℤ, (((zdInf n : ℕ) : ℝ) ^ M)⁻¹, ?_⟩
  intro L _ R hR hRL x
  have hsub : Summable fun n : {n : Fin d → ℤ // n ≠ 0} => (((zdInf n.1 : ℕ) : ℝ) ^ M)⁻¹ :=
    hs.subtype _
  have hb : ∀ n : {n : Fin d → ℤ // n ≠ 0},
      ((1 + (zdInf (zlift x + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹ ≤
        2 ^ M * (R / L) ^ M * (((zdInf n.1 : ℕ) : ℝ) ^ M)⁻¹ :=
    fun n => periodize_term_le M R hR x n.1 n.2
  have hsum := periodize_term_summable (L := L) d M hM R hR x
  have hzero : Function.support (fun n : Fin d → ℤ => (((zdInf n : ℕ) : ℝ) ^ M)⁻¹) ⊆
      {n | n ≠ 0} := by
    intro n hn
    by_contra h
    simp only [Set.mem_ofPred_eq, not_not] at h
    subst h
    have hM0 : M ≠ 0 := by omega
    exact hn (by simp [zdInf, hM0])
  calc ∑' n : {n : Fin d → ℤ // n ≠ 0},
        ((1 + (zdInf (zlift x + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹
      ≤ ∑' n : {n : Fin d → ℤ // n ≠ 0},
          2 ^ M * (R / L) ^ M * (((zdInf n.1 : ℕ) : ℝ) ^ M)⁻¹ :=
        hsum.tsum_le_tsum hb (hsub.mul_left _)
    _ = 2 ^ M * (R / L) ^ M * ∑' n : {n : Fin d → ℤ // n ≠ 0}, (((zdInf n.1 : ℕ) : ℝ) ^ M)⁻¹ :=
        tsum_mul_left
    _ = 2 ^ M * (∑' n : Fin d → ℤ, (((zdInf n : ℕ) : ℝ) ^ M)⁻¹) * (R / L) ^ M := by
        rw [show (∑' n : {n : Fin d → ℤ // n ≠ 0}, (((zdInf n.1 : ℕ) : ℝ) ^ M)⁻¹) =
          ∑' n : Fin d → ℤ, (((zdInf n : ℕ) : ℝ) ^ M)⁻¹ from
            tsum_subtype_eq_of_support_subset hzero]
        ring

section Witness

end Witness

end RBM8D
