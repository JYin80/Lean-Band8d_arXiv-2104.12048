module

public import RBM8D.Kernel.Periodize
public import RBM8D.Kernel.Sinf
public import RBM8D.Kernel.ZdCancel
public import RBM8D.Kernel.PropagatorSymbol
public import RBM8D.Basic.Domain

@[expose] public section

/-!
# Decay of `Θ` on the torus

[I, (1.17)], [I, Lemma 6.1], the row sum and the ball sum of `Θ` ([I, (sumTheta)]); the bound `B_{xy}` and the spectral domain `𝐃(κ, ε)`.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

/-- The right side of [I, (1.17)]:
`W^τ 1(|x - y| ≤ η^{-1/2} W^{1+τ}) B_{xy} + ⟨x - y⟩^{-D}`, with `⟨x⟩ = ‖x‖_L + W`. -/
def thetaBound {d L : ℕ} (W : ℕ) (η τ D : ℝ) (x y : Zd d L) : ℝ :=
  (if (zdistInf d L (x - y) : ℝ) ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + τ) then
      (W : ℝ) ^ τ * bB d L W x y else 0) +
    ((zdistInf d L (x - y) : ℝ) + W) ^ (-D)

/-! ## The semicircle law in the bulk -/

section Bulk

/-- `η |m|² = Im m (1 - |m|²)` for `m = m(z)`, from `m (m + z) = -1`. -/
private theorem ThetaDecay_im_identity (z : ℂ) :
    z.im * ‖msc z‖ ^ 2 = (msc z).im * (1 - ‖msc z‖ ^ 2) := by
  have h := msc_mul z
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.one_re, Complex.one_im] at h1 h2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  linear_combination (-(msc z).im) * h1 + (msc z).re * h2

/-- `1 - |m(z)|² ≥ η/2` for `0 < η ≤ 1`. -/
private theorem ThetaDecay_one_sub_ge {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    z.im / 2 ≤ 1 - ‖msc z‖ ^ 2 := by
  have hid := ThetaDecay_im_identity z
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hm0 : 0 ≤ ‖msc z‖ := norm_nonneg _
  have him : (msc z).im ≤ ‖msc z‖ := Complex.im_le_norm _
  have him0 : 0 < (msc z).im := msc_im_pos hz
  set a := ‖msc z‖ ^ 2 with ha
  have ha1 : a < 1 := by rw [ha]; nlinarith
  have ha0 : 0 ≤ a := by positivity
  rcases le_or_gt (1 / 2) a with h | h
  · have : z.im * a ≤ 1 - a := by
      rw [hid]
      have : (msc z).im ≤ 1 := by linarith
      nlinarith
    nlinarith
  · linarith

/-- `|m(z)|² < 1` for `η > 0`. -/
private theorem ThetaDecay_sq_lt_one {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ ^ 2 < 1 := by
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hm0 : 0 ≤ ‖msc z‖ := norm_nonneg _
  nlinarith

/-- `|m|²/(1 - |m|²) = Im m / η` for `η > 0`. -/
private theorem ThetaDecay_ratio {z : ℂ} (hz : 0 < z.im) :
    ‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) = (msc z).im / z.im := by
  have h1 := ThetaDecay_sq_lt_one hz
  rw [div_eq_div_iff (by linarith) hz.ne']
  linarith [ThetaDecay_im_identity z]

end Bulk

/-! ## Lifts, casts and periodisation -/

section Lift

variable {d L : ℕ}

private theorem ThetaDecay_zcast_zlift (x : Zd d L) : zcast L (zlift x) = x := by
  funext i
  simp [zcast, zlift, ZMod.coe_valMinAbs]

private theorem ThetaDecay_zcast_add (u v : Fin d → ℤ) :
    zcast L (u + v) = zcast L u + zcast L v := by
  funext i
  simp [zcast]

private theorem ThetaDecay_zcast_neg (u : Fin d → ℤ) : zcast L (-u) = -zcast L u := by
  funext i
  simp [zcast]

/-- The points of `ℤ^d` reducing to `x` are exactly `[x]_L + L n`, `n ∈ ℤ^d`. -/
private theorem ThetaDecay_exists_eq_zlift_add_smul (x : Zd d L) (y : Fin d → ℤ)
    (h : zcast L y = x) : ∃ n : Fin d → ℤ, zlift x + (L : ℤ) • n = y := by
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

/-- `|[x]_L|_∞ = ‖x‖_L`. -/
private theorem ThetaDecay_zdInf_zlift [NeZero L] (x : Zd d L) :
    zdInf (zlift x) = zdistInf d L x := by
  simp only [zdInf, zlift, zdistInf, zdist_eq_natAbs_valMinAbs]

/-- For `2|v_i| < L`, the representative of the reduction of `v` is `v`. -/
private theorem ThetaDecay_zlift_zcast [NeZero L] {K : ℕ} (hKL : 2 * K < L) {v : Fin d → ℤ}
    (hv : v ∈ boxZ d K) : zlift (zcast L v) = v := by
  funext i
  simp only [boxZ, Fintype.mem_piFinset, Finset.mem_Icc] at hv
  obtain ⟨h1, h2⟩ := hv i
  simp only [zlift, zcast]
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_, ?_⟩
  · have : (2 * K : ℤ) < L := by exact_mod_cast hKL
    linarith
  · have : (2 * K : ℤ) < L := by exact_mod_cast hKL
    linarith

private theorem ThetaDecay_zlift_mem_boxZ [NeZero L] {K : ℕ} {y : Zd d L}
    (hy : zdistInf d L y ≤ K) : zlift y ∈ boxZ d K := by
  simp only [boxZ, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : (zlift y i).natAbs ≤ K := by
    have := zdist_le_zdistInf d L y i
    rw [zdist_eq_natAbs_valMinAbs] at this
    simp only [zlift]
    omega
  have h2 : |zlift y i| ≤ (K : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  exact abs_le.mp h2

/-- A sum over `Z_L^d` of a function supported on `‖y‖_L ≤ K`, `2K < L`, is the sum over the
box `⟦-K, K⟧^d` of `ℤ^d`. -/
private theorem ThetaDecay_sum_eq_sum_boxZ [NeZero L] {R : Type*} [AddCommMonoid R] {K : ℕ}
    (hKL : 2 * K < L) (F : Zd d L → R) (hF : ∀ y, K < zdistInf d L y → F y = 0) :
    ∑ y, F y = ∑ v ∈ boxZ d K, F (zcast L v) := by
  rw [← Finset.sum_filter_of_ne (p := fun y => zdistInf d L y ≤ K)
    (fun y _ hy => by by_contra h; exact hy (hF y (not_le.mp h)))]
  refine Finset.sum_nbij' zlift (zcast L) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact ThetaDecay_zlift_mem_boxZ hy
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← ThetaDecay_zdInf_zlift, ThetaDecay_zlift_zcast hKL hv]
    simp only [boxZ, Fintype.mem_piFinset, Finset.mem_Icc] at hv
    refine Finset.sup_le fun i _ => ?_
    obtain ⟨h1, h2⟩ := hv i
    omega
  · intro y _
    exact ThetaDecay_zcast_zlift y
  · intro v hv
    exact ThetaDecay_zlift_zcast hKL hv
  · intro y _
    rw [ThetaDecay_zcast_zlift]

/-- `‖[v]‖_L = |v|_∞` on the box `⟦-K, K⟧^d`, `2K < L`. -/
private theorem ThetaDecay_zdistInf_zcast [NeZero L] {K : ℕ} (hKL : 2 * K < L) {v : Fin d → ℤ}
    (hv : v ∈ boxZ d K) : zdistInf d L (zcast L v) = zdInf v := by
  rw [← ThetaDecay_zdInf_zlift, ThetaDecay_zlift_zcast hKL hv]

/-- The periodisation at the reduction of `v ∈ ℤ^d` is `Σ_n K(v + L n)`. -/
private theorem ThetaDecay_periodize_zcast [NeZero L] (K : (Fin d → ℤ) → ℂ) (v : Fin d → ℤ) :
    periodize L K (zcast L v) = ∑' n : Fin d → ℤ, K (v + (L : ℤ) • n) := by
  obtain ⟨n₀, hn₀⟩ := ThetaDecay_exists_eq_zlift_add_smul (zcast L v) v rfl
  unfold periodize
  have hz : zlift (zcast L v) = v - (L : ℤ) • n₀ := eq_sub_iff_add_eq.mpr hn₀
  rw [hz]
  rw [← (Equiv.addRight n₀).tsum_eq]
  refine tsum_congr fun n => ?_
  congr 1
  simp only [Equiv.coe_addRight, smul_add]
  abel

/-- The `ℓ^∞` norm of a nonzero point of `ℤ^d` is positive. -/
private theorem ThetaDecay_zdInf_pos {n : Fin d → ℤ} (hn : n ≠ 0) : 0 < zdInf n := by
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have : (n j).natAbs ≤ zdInf n := Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ j)
  have : 0 < (n j).natAbs := Int.natAbs_pos.mpr hj
  omega

/-- The wrap-around lower bound: `|[x]_L + L n|_∞ ≥ L |n|_∞ / 2` for `n ≠ 0`. -/
private theorem ThetaDecay_zdInf_add_smul_ge [NeZero L] (x : Zd d L) (n : Fin d → ℤ)
    (hn : n ≠ 0) : L * zdInf n ≤ 2 * zdInf (zlift x + (L : ℤ) • n) := by
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    ⟨j, Finset.mem_univ j⟩ (fun i => (n i).natAbs)
  have hni : (n i).natAbs = zdInf n := hi.symm
  have hv : 2 * (zlift x i).natAbs ≤ L := by
    have := ZMod.natAbs_valMinAbs_le (x i)
    simp only [zlift]
    omega
  have hle : ((zlift x + (L : ℤ) • n) i).natAbs ≤ zdInf (zlift x + (L : ℤ) • n) :=
    Finset.le_sup (f := fun i => ((zlift x + (L : ℤ) • n) i).natAbs) (Finset.mem_univ i)
  have hn1 : 1 ≤ (n i).natAbs := by
    rw [hni]
    have : (n j).natAbs ≤ zdInf n := Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ j)
    have : 0 < (n j).natAbs := Int.natAbs_pos.mpr hj
    omega
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

/-- `|[x]_L + L n|_∞ ≥ ‖x‖_L` for every `n`. -/
private theorem ThetaDecay_zdistInf_le_zdInf [NeZero L] (x : Zd d L) (n : Fin d → ℤ) :
    zdistInf d L x ≤ zdInf (zlift x + (L : ℤ) • n) := by
  by_cases hn : n = 0
  · subst hn; simp [ThetaDecay_zdInf_zlift]
  · have h1 := ThetaDecay_zdInf_add_smul_ge x n hn
    have h2 := ThetaDecay_zdInf_pos hn
    have h3 := zdistInf_le_half d L x
    have : L ≤ L * zdInf n := Nat.le_mul_of_pos_right L h2
    omega

/-- `|[x]_L + L n|_∞ ≥ L/2` for `n ≠ 0`. -/
private theorem ThetaDecay_half_le_zdInf [NeZero L] (x : Zd d L) (n : Fin d → ℤ) (hn : n ≠ 0) :
    (L : ℝ) / 2 ≤ zdInf (zlift x + (L : ℤ) • n) := by
  have h1 := ThetaDecay_zdInf_add_smul_ge x n hn
  have h2 := ThetaDecay_zdInf_pos hn
  have : L ≤ 2 * zdInf (zlift x + (L : ℤ) • n) := le_trans (Nat.le_mul_of_pos_right L h2) h1
  have : (L : ℝ) ≤ 2 * (zdInf (zlift x + (L : ℤ) • n) : ℝ) := by exact_mod_cast this
  linarith

/-- The weight `|n|_∞^{-M}` is summable over `ℤ^d` for `M > d` (and vanishes at `n = 0`). -/
private theorem ThetaDecay_summable_zdInf_inv_pow (d M : ℕ) (hM : d < M) :
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

/-- Termwise bound for `n ≠ 0`:
`(1 + |[x]_L + L n|/R)^{-M} ≤ 2^M (R/L)^M |n|_∞^{-M}`. -/
private theorem ThetaDecay_term_le [NeZero L] (M : ℕ) (R : ℝ) (hR : 0 < R) (x : Zd d L)
    (n : Fin d → ℤ) (hn : n ≠ 0) :
    ((1 + (zdInf (zlift x + (L : ℤ) • n) : ℝ) / R) ^ M)⁻¹ ≤
      2 ^ M * (R / L) ^ M * (((zdInf n : ℕ) : ℝ) ^ M)⁻¹ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have ha : (0 : ℝ) < ((zdInf n : ℕ) : ℝ) := by exact_mod_cast ThetaDecay_zdInf_pos hn
  have hge : (L : ℝ) * ((zdInf n : ℕ) : ℝ) ≤ 2 * ((zdInf (zlift x + (L : ℤ) • n) : ℕ) : ℝ) := by
    exact_mod_cast ThetaDecay_zdInf_add_smul_ge x n hn
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
private theorem ThetaDecay_term_summable [NeZero L] (M : ℕ) (hM : d + 1 ≤ M) (R : ℝ)
    (hR : 0 < R) (x : Zd d L) :
    Summable fun n : {n : Fin d → ℤ // n ≠ 0} =>
      ((1 + (zdInf (zlift x + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹ := by
  have hs := ThetaDecay_summable_zdInf_inv_pow d M (by omega)
  have hsub : Summable fun n : {n : Fin d → ℤ // n ≠ 0} => (((zdInf n.1 : ℕ) : ℝ) ^ M)⁻¹ :=
    hs.subtype _
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ThetaDecay_term_le M R hR x n.1 n.2) (hsub.mul_left (2 ^ M * (R / L) ^ M))

/-- `‖Σ_n f(n)‖ ≤ ‖f(0)‖ + Σ_{n ≠ 0} b(n)` for `‖f(n)‖ ≤ b(n)`, `n ≠ 0`. -/
private theorem ThetaDecay_norm_tsum_le (f : (Fin d → ℤ) → ℂ) (hf : Summable fun n => ‖f n‖)
    (b : {n : Fin d → ℤ // n ≠ 0} → ℝ) (hb : Summable b) (hfb : ∀ n, ‖f n.1‖ ≤ b n) :
    ‖∑' n, f n‖ ≤ ‖f 0‖ + ∑' n, b n := by
  refine (norm_tsum_le_tsum_norm hf).trans ?_
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton (0 : Fin d → ℤ)
    (fun n => ‖f n‖)]
  gcongr
  have e : (({0} : Set (Fin d → ℤ))ᶜ : Set (Fin d → ℤ)) = {n | n ≠ 0} := by
    ext n; simp
  have hf' : Summable fun n : {n : Fin d → ℤ // n ≠ 0} => ‖f n.1‖ := hf.subtype _
  calc ∑' n : ↑(({0} : Set (Fin d → ℤ))ᶜ), ‖f n‖ = ∑' n : {n : Fin d → ℤ // n ≠ 0}, ‖f n.1‖ :=
        rfl
    _ ≤ ∑' n, b n := hf'.tsum_le_tsum hfb hb

end Lift

/-! ## The Fourier series of `Θ_{ℤ^d}(a)` for `a < 1` -/

section ThetaSeries

variable {d : ℕ}

private theorem ThetaDecay_summable_s {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ} {W : ℕ}
    {s : (Fin d → ℤ) → ℝ} (hs : InfKernel ψ C W s) : Summable s := by
  by_contra h
  have := hs.sum_one
  rw [tsum_eq_zero_of_not_summable h] at this
  exact zero_ne_one this

private theorem ThetaDecay_measurableSet_cubePi : MeasurableSet (cubePi d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

private theorem ThetaDecay_isCompact_cubePi : IsCompact (cubePi d) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem ThetaDecay_continuous_zexp (y : Fin d → ℤ) :
    Continuous fun p : Fin d → ℝ => zexp p y := by
  unfold zexp; fun_prop

private theorem ThetaDecay_integrableOn_mul_zexp {F : (Fin d → ℝ) → ℂ}
    (hF : IntegrableOn F (cubePi d)) (x : Fin d → ℤ) :
    IntegrableOn (fun p => F p * zexp p (-x)) (cubePi d) :=
  hF.mul_continuousOn (ThetaDecay_continuous_zexp _).continuousOn ThetaDecay_isCompact_cubePi

private theorem ThetaDecay_latticeFourier_add {F G : (Fin d → ℝ) → ℂ}
    (hF : IntegrableOn F (cubePi d)) (hG : IntegrableOn G (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => F p + G p) x = latticeFourier F x + latticeFourier G x := by
  unfold latticeFourier
  rw [← mul_add, ← integral_add (ThetaDecay_integrableOn_mul_zexp hF x)
    (ThetaDecay_integrableOn_mul_zexp hG x)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only; ring

private theorem ThetaDecay_latticeFourier_const_mul (c : ℂ) (F : (Fin d → ℝ) → ℂ)
    (x : Fin d → ℤ) : latticeFourier (fun p => c * F p) x = c * latticeFourier F x := by
  unfold latticeFourier
  simp_rw [mul_assoc c]
  rw [integral_const_mul]; ring

private theorem ThetaDecay_latticeFourier_congr {F G : (Fin d → ℝ) → ℂ}
    (h : ∀ p ∈ cubePi d, F p = G p) (x : Fin d → ℤ) : latticeFourier F x = latticeFourier G x := by
  unfold latticeFourier
  congr 1
  exact setIntegral_congr_fun ThetaDecay_measurableSet_cubePi fun p hp => by simp only [h p hp]

/-- Multiplying the symbol by the Fourier series of a summable kernel `K` convolves with `K`. -/
private theorem ThetaDecay_latticeFourier_zdSeries_mul {K : (Fin d → ℤ) → ℂ}
    (hsum : Summable fun y => ‖K y‖) {Φ : (Fin d → ℝ) → ℂ} (hΦ : IntegrableOn Φ (cubePi d))
    (x : Fin d → ℤ) :
    latticeFourier (fun p => zdSeries K p * Φ p) x = ∑' y, K y * latticeFourier Φ (x - y) := by
  unfold latticeFourier
  set F : (Fin d → ℤ) → (Fin d → ℝ) → ℂ := fun y p => K y * (Φ p * zexp p (-(x - y)))
  have hF : ∀ y, Integrable (F y) (volume.restrict (cubePi d)) := fun y =>
    (ThetaDecay_integrableOn_mul_zexp hΦ (x - y)).const_mul _
  have hnorm : ∀ y, ∫ p in cubePi d, ‖F y p‖ = ‖K y‖ * ∫ p in cubePi d, ‖Φ p‖ := by
    intro y
    simp only [F, norm_mul, norm_zexp, mul_one]
    rw [integral_const_mul]
  have hsumm : Summable fun y => ∫ p in cubePi d, ‖F y p‖ := by
    simp_rw [hnorm]; exact hsum.mul_right _
  have h := integral_tsum_of_summable_integral_norm hF hsumm
  have hpt : ∀ p, zdSeries K p * Φ p * zexp p (-x) = ∑' y, F y p := by
    intro p
    unfold zdSeries
    rw [mul_assoc, ← tsum_mul_right]
    refine tsum_congr fun y => ?_
    simp only [F]
    have : zexp p (-(x - y)) = zexp p y * zexp p (-x) := by
      rw [← zexp_add]; congr 1; abel
    rw [this]; ring
  simp_rw [hpt]
  rw [← h, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  simp only [F]
  rw [integral_const_mul]; ring

/-- The Fourier series of a convolution of summable kernels is the product of their Fourier
series. -/
private theorem ThetaDecay_zdSeries_conv {K₁ K₂ : (Fin d → ℤ) → ℂ}
    (h₁ : Summable fun y => ‖K₁ y‖) (h₂ : Summable fun y => ‖K₂ y‖) (p : Fin d → ℝ) :
    ∑' x, (∑' y, K₁ y * K₂ (x - y)) * zexp p x = zdSeries K₁ p * zdSeries K₂ p := by
  have hn₁ : Summable fun y => ‖K₁ y * zexp p y‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using h₁
  have hn₂ : Summable fun y => ‖K₂ y * zexp p y‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using h₂
  have hprod := tsum_mul_tsum_of_summable_norm (f := fun y => K₁ y * zexp p y)
    (g := fun y => K₂ y * zexp p y) hn₁ hn₂
  set G : (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun q => K₁ q.1 * zexp p q.1 * (K₂ q.2 * zexp p q.2)
  have hG : Summable G := summable_mul_of_summable_norm (f := fun y => K₁ y * zexp p y)
    (g := fun y => K₂ y * zexp p y) hn₁ hn₂
  set e : (Fin d → ℤ) × (Fin d → ℤ) ≃ (Fin d → ℤ) × (Fin d → ℤ) :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := fun q => by simp
      right_inv := fun q => by simp } with he
  have hGe : Summable (G ∘ e) := e.summable_iff.2 hG
  have hval : ∀ q : (Fin d → ℤ) × (Fin d → ℤ),
      G (e q) = K₁ q.2 * K₂ (q.1 - q.2) * zexp p q.1 := by
    intro q
    simp only [G, he, Equiv.coe_fn_mk]
    have : zexp p q.2 * zexp p (q.1 - q.2) = zexp p q.1 := by rw [← zexp_add]; congr 1; abel
    rw [← this]; ring
  have hGe' : Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      K₁ q.2 * K₂ (q.1 - q.2) * zexp p q.1 := hGe.congr hval
  unfold zdSeries
  rw [hprod, ← e.tsum_eq G, tsum_congr hval, hGe'.tsum_prod]
  refine tsum_congr fun x => ?_
  rw [← tsum_mul_right]

/-- `1 - a σ ≥ (1 - a)/2` for `σ ≤ 1` and `0 ≤ a ≤ 1`. -/
private theorem ThetaDecay_one_sub_mul_ge_half {a σ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hσ : σ ≤ 1) : (1 - a) / 2 ≤ 1 - a * σ := by
  rcases le_or_gt (1 / 2) σ with h | h
  · nlinarith
  · rcases le_or_gt 0 σ with h' | h'
    · nlinarith
    · nlinarith

/-- Summability of `Θ_{ℤ^d}(a)` for `a < 1` from the decay `(1 + |x|(1 - a)^{1/2}/W)^{-(d+1)}`. -/
private theorem ThetaDecay_summable_of_bound {f : (Fin d → ℤ) → ℂ} {A κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ z, ‖f z‖ * (1 + (zdInf z : ℝ) * κ) ^ (d + 1) ≤ A) : Summable fun z => ‖f z‖ := by
  have hs := (ThetaDecay_summable_zdInf_inv_pow d (d + 1) (by omega)).mul_left (|A| * (κ ^ (d + 1))⁻¹)
  have h0 : Summable fun z : Fin d → ℤ => if z = 0 then ‖f 0‖ else 0 :=
    (hasSum_ite_eq (0 : Fin d → ℤ) ‖f 0‖).summable
  refine Summable.of_nonneg_of_le (fun z => norm_nonneg _) (fun z => ?_) (hs.add h0)
  by_cases hz : z = 0
  · subst hz
    simp only [ite_true]
    have : 0 ≤ |A| * (κ ^ (d + 1))⁻¹ * (((zdInf (0 : Fin d → ℤ) : ℕ) : ℝ) ^ (d + 1))⁻¹ := by
      positivity
    linarith
  · simp only [hz, ite_false, add_zero]
    have hpos : (0 : ℝ) < zdInf z := by exact_mod_cast ThetaDecay_zdInf_pos hz
    have h1 : (κ * zdInf z) ^ (d + 1) ≤ (1 + (zdInf z : ℝ) * κ) ^ (d + 1) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    have h2 : ‖f z‖ * (κ * zdInf z) ^ (d + 1) ≤ |A| :=
      ((mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (hb z)).trans (le_abs_self A)
    rw [mul_pow] at h2
    rw [mul_assoc, ← mul_inv, le_mul_inv_iff₀ (by positivity)]
    linarith

/-- For `a < 1`, `Θ_{ℤ^d}(a)` is summable and its Fourier series is its symbol
`a ŝ/(1 - a ŝ)` on `[-π, π]^d`; this uses `Θ = a s + a s * Θ`. -/
private theorem ThetaDecay_theta_series (d : ℕ) (hd : 3 ≤ d)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) :
    ∃ W₀ : ℝ, 1 ≤ W₀ ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ (a : ℝ), 0 ≤ a → a < 1 →
        Summable (fun z => ‖ThetaZd a s z‖) ∧
        ∀ p ∈ cubePi d, zdSeries (ThetaZd a s) p =
          (a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p) := by
  obtain ⟨C₁, W₁, h1⟩ := ThetaZd_decay d hd ψ cψ hψ C (d + 1)
  obtain ⟨c, W₂, hc, hW₂⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  obtain ⟨K₀, hK₀⟩ := zdSymbol_smooth d ψ C 0
  refine ⟨max (max W₁ W₂) 1, le_max_right _ _, ?_⟩
  intro W hW s hs a ha0 ha
  have hW1' : W₁ ≤ (W : ℝ) := le_trans (by simp) hW
  have hW2' : W₂ ≤ (W : ℝ) := le_trans (by simp) hW
  have hW1 : (1 : ℝ) ≤ W := le_trans (by simp) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hFi, hb⟩ := h1 W hW1' s hs a ha0 ha.le
  set thetaSym : (Fin d → ℝ) → ℂ := fun p =>
    (a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p) with hthetaSym
  -- summability of `Θ_{ℤ^d}(a)`
  have hκ0 : 0 < Real.sqrt (1 - a) / W := by
    have : 0 < Real.sqrt (1 - a) := Real.sqrt_pos.2 (by linarith)
    positivity
  have hΘs : Summable fun z => ‖ThetaZd a s z‖ := by
    refine ThetaDecay_summable_of_bound (A := |C₁|) hκ0 fun z => ?_
    have h := hb z
    have hw : (1 + (zdInf z : ℝ) * Real.sqrt (1 - a) / W) =
        1 + (zdInf z : ℝ) * (Real.sqrt (1 - a) / W) := by ring
    rw [hw] at h
    have hden : 1 ≤ (W : ℝ) ^ 2 * ((zdInf z : ℝ) + W) ^ (d - 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) (one_le_pow₀ (by linarith [
        (Nat.cast_nonneg (zdInf z) : (0 : ℝ) ≤ zdInf z)]))
    exact h.trans ((div_le_self (abs_nonneg _) hden).trans' (div_le_div_of_nonneg_right
        (le_abs_self _) (by positivity)))
  refine ⟨hΘs, ?_⟩
  -- the identity `Θ = a s + a s * Θ`
  obtain ⟨hcd, -, hK0⟩ := hK₀ W hWn s hs
  have hsn : Summable fun y => ‖((s y : ℝ) : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      summable_abs_iff.2 (ThetaDecay_summable_s hs)
  have hden' : ∀ p ∈ cubePi d, (1 : ℂ) - (a : ℂ) * zdSymbol s p ≠ 0 ∧
      zdSymbol s p = (((zdSymbol s p).re : ℝ) : ℂ) := by
    intro p hp
    obtain ⟨him, hge⟩ := hW₂ W hW2' s hs p hp
    set σ := (zdSymbol s p).re with hσ
    have hse : zdSymbol s p = (σ : ℂ) := Complex.ext (by simp [hσ]) (by simp [him])
    have hσ1 : σ ≤ 1 := by
      have : 0 ≤ c * min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
        mul_nonneg hc.le (le_min (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun i _ => sq_nonneg (p i))) zero_le_one)
      linarith
    have hpos : 0 < 1 - a * σ := by
      have := ThetaDecay_one_sub_mul_ge_half ha0 ha.le hσ1; linarith
    refine ⟨?_, hse⟩
    rw [hse]
    have : ((1 - a * σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    simpa using this
  have hsym : ∀ p ∈ cubePi d, thetaSym p =
      (a : ℂ) * zdSymbol s p + (a : ℂ) * (zdSymbol s p * thetaSym p) := by
    intro p hp
    have hne := (hden' p hp).1
    simp only [hthetaSym]
    field_simp
    ring
  have hscont : IntegrableOn (zdSymbol s) (cubePi d) :=
    hcd.continuous.continuousOn.integrableOn_compact ThetaDecay_isCompact_cubePi
  have hsF : IntegrableOn (fun p => zdSymbol s p * thetaSym p) (cubePi d) := by
    refine Integrable.bdd_mul (c := K₀) hFi hcd.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have := hK0 p
    rwa [norm_iteratedFDeriv_zero, pow_zero, mul_one] at this
  have hreal : ∀ x, ThetaZd a s x =
      (a : ℂ) * (s x : ℂ) + (a : ℂ) * ∑' y, (s y : ℂ) * ThetaZd a s (x - y) := by
    intro x
    have h1 : ThetaZd a s x = latticeFourier (fun p => (a : ℂ) * zdSymbol s p +
        (a : ℂ) * (zdSymbol s p * thetaSym p)) x := ThetaDecay_latticeFourier_congr hsym x
    rw [h1, ThetaDecay_latticeFourier_add (F := fun p => (a : ℂ) * zdSymbol s p)
      (G := fun p => (a : ℂ) * (zdSymbol s p * thetaSym p)) (hscont.const_mul _)
      (hsF.const_mul _), ThetaDecay_latticeFourier_const_mul,
      ThetaDecay_latticeFourier_const_mul (F := fun p => zdSymbol s p * thetaSym p)]
    have h2 : latticeFourier (zdSymbol s) x = (s x : ℂ) := latticeFourier_zdSeries _ hsn x
    have h3 : latticeFourier (fun p => zdSymbol s p * thetaSym p) x =
        ∑' y, (s y : ℂ) * ThetaZd a s (x - y) :=
      ThetaDecay_latticeFourier_zdSeries_mul hsn hFi x
    rw [h2, h3]
  intro p hp
  have hden := (hden' p hp).1
  have hsz : Summable fun x => ‖(s x : ℂ) * zexp p x‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using hsn
  have hΘz : Summable fun x => ‖ThetaZd a s x * zexp p x‖ := by
    simpa only [norm_mul, norm_zexp, mul_one] using hΘs
  have hsplit : ∀ x, ThetaZd a s x * zexp p x = (a : ℂ) * ((s x : ℂ) * zexp p x) +
      (a : ℂ) * ((∑' y, (s y : ℂ) * ThetaZd a s (x - y)) * zexp p x) := fun x => by
    rw [hreal x]; ring
  have hA : Summable fun x => (a : ℂ) * ((s x : ℂ) * zexp p x) := hsz.of_norm.mul_left _
  have hB : Summable fun x =>
      (a : ℂ) * ((∑' y, (s y : ℂ) * ThetaZd a s (x - y)) * zexp p x) :=
    (hΘz.of_norm.sub hA).congr fun x => by rw [hsplit x]; ring
  have hconv := ThetaDecay_zdSeries_conv hsn hΘs p
  have hkey : zdSeries (ThetaZd a s) p =
      (a : ℂ) * zdSymbol s p + (a : ℂ) * (zdSymbol s p * zdSeries (ThetaZd a s) p) := by
    calc zdSeries (ThetaZd a s) p = ∑' x, ThetaZd a s x * zexp p x := rfl
      _ = _ := by
        rw [tsum_congr hsplit, hA.tsum_add hB, tsum_mul_left, tsum_mul_left, hconv]
        rfl
  rw [eq_div_iff hden]
  linear_combination hkey

end ThetaSeries

/-! ## `Θ` on the torus and the periodisation of `Θ_{ℤ^d}` -/

section Replacement

variable {d L : ℕ}

/-- `|F_a(t) - F_a(σ)| ≤ |t - σ|/(1 - a)²` for `F_a(t) = a t/(1 - a t)`, `|t| ≤ 1`, real
`σ ≤ 1`, `0 ≤ a < 1`. -/
private theorem ThetaDecay_F_sub_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {t : ℂ} (ht : ‖t‖ ≤ 1)
    {σ : ℝ} (hσ : σ ≤ 1) :
    ‖(a : ℂ) * t / (1 - (a : ℂ) * t) - (a : ℂ) * (σ : ℂ) / (1 - (a : ℂ) * (σ : ℂ))‖ ≤
      ‖t - (σ : ℂ)‖ / (1 - a) ^ 2 := by
  have h1a : 0 < 1 - a := by linarith
  have hn1 : 1 - a ≤ ‖1 - (a : ℂ) * t‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((a : ℂ) * t)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0] at h
    nlinarith
  have hn2 : 1 - a ≤ ‖1 - (a : ℂ) * (σ : ℂ)‖ := by
    have e : (1 : ℂ) - (a : ℂ) * (σ : ℂ) = ((1 - a * σ : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    have : a * σ ≤ a := by nlinarith
    exact (by linarith : 1 - a ≤ 1 - a * σ).trans (le_abs_self _)
  have hne1 : (1 : ℂ) - (a : ℂ) * t ≠ 0 := by
    intro h; rw [h, norm_zero] at hn1; linarith
  have hne2 : (1 : ℂ) - (a : ℂ) * (σ : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn2; linarith
  have e : (a : ℂ) * t / (1 - (a : ℂ) * t) - (a : ℂ) * (σ : ℂ) / (1 - (a : ℂ) * (σ : ℂ)) =
      (a : ℂ) * (t - σ) / ((1 - (a : ℂ) * t) * (1 - (a : ℂ) * (σ : ℂ))) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hp : (1 - a) ^ 2 ≤ ‖1 - (a : ℂ) * t‖ * ‖1 - (a : ℂ) * (σ : ℂ)‖ := by
    rw [sq]; exact mul_le_mul hn1 hn2 h1a.le (by positivity)
  have := norm_nonneg (t - (σ : ℂ))
  calc a * ‖t - (σ : ℂ)‖ * (1 - a) ^ 2 ≤ 1 * ‖t - (σ : ℂ)‖ * (1 - a) ^ 2 := by gcongr
    _ ≤ ‖t - (σ : ℂ)‖ * (‖1 - (a : ℂ) * t‖ * ‖1 - (a : ℂ) * (σ : ℂ)‖) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left hp this

/-- The frequencies `2πk/L` of `T_L^d` lie in `[-π, π]^d`. -/
private theorem ThetaDecay_zfreqPi_mem [NeZero L] (k : Zd d L) : zfreqPi k ∈ cubePi d := by
  intro i _
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨h1, h2⟩ := (k i).valMinAbs_mem_Ioc
  have h1' : -(L : ℝ) < ((k i).valMinAbs : ℝ) * 2 := by exact_mod_cast h1
  have h2' : ((k i).valMinAbs : ℝ) * 2 ≤ L := by exact_mod_cast h2
  have hpi := Real.pi_pos
  simp only [zfreqPi, Set.mem_Icc]
  constructor
  · rw [le_div_iff₀ hL]; nlinarith
  · rw [div_le_iff₀ hL]; nlinarith

/-- The kernel of `Θ`: `Θ_{0x} = L^{-d} Σ_k Θ̂(k) e^{-ip·x}`, and `Θ̂ = F_a(Ŝ)`. -/
private theorem ThetaDecay_Theta_eq [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS : IsSymKernel S) (m : ℂ) (hm : ‖m‖ < 1) (x : Zd d L) :
    (Theta m S 0 x : ℂ) = ((L : ℂ) ^ d)⁻¹ * ∑ k, ((‖m‖ ^ 2 : ℝ) : ℂ) * symbol (cmat S) k /
      (1 - ((‖m‖ ^ 2 : ℝ) : ℂ) * symbol (cmat S) k) * zchar k (-x) := by
  have hTI : TransInv (cmat (Theta m S)) := by
    have h := (TransInv_propagators S hS.transInv m).2.2
    intro x y a
    simp only [cmat, Matrix.map_apply, h x y a]
  have hm' : ∀ k, (‖m‖ ^ 2 : ℂ) * symbol (cmat S) k ≠ 1 := by
    intro k h
    have h1 := congrArg norm h
    rw [norm_mul, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm] at h1
    have h2 := hS.norm_symbol_le k
    have h3 : ‖m‖ ^ 2 < 1 := by nlinarith [norm_nonneg m]
    nlinarith [norm_nonneg (symbol (cmat S) k), sq_nonneg ‖m‖]
  have h1 := kernel_inversion (cmat (Theta m S)) hTI 0 x
  have e : (Theta m S 0 x : ℂ) = cmat (Theta m S) 0 x := rfl
  rw [e, h1]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [symbol_Theta S hS.transInv m hm' k, zero_sub]
  push_cast
  rfl

/-- The replacement step: if `|Ŝ(k) - ŝ(2πk/L)| ≤ δ` for all `k`, then
`|Θ_{0x} - Σ_n Θ_{ℤ^d}([x]_L + L n)| ≤ δ/(1 - |m|²)²`. -/
private theorem ThetaDecay_sub_periodize_le [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS : IsSymKernel S) (s : (Fin d → ℤ) → ℝ) (m : ℂ) (hm : ‖m‖ < 1) (δ : ℝ)
    (hΘs : Summable fun z => ‖ThetaZd (‖m‖ ^ 2) s z‖)
    (hser : ∀ p ∈ cubePi d, zdSeries (ThetaZd (‖m‖ ^ 2) s) p =
      ((‖m‖ ^ 2 : ℝ) : ℂ) * zdSymbol s p / (1 - ((‖m‖ ^ 2 : ℝ) : ℂ) * zdSymbol s p))
    (hreal : ∀ p ∈ cubePi d, (zdSymbol s p).im = 0 ∧ (zdSymbol s p).re ≤ 1)
    (hclose : ∀ k, ‖symbol (cmat S) k - zdSymbol s (zfreqPi k)‖ ≤ δ) (x : Zd d L) :
    ‖(Theta m S 0 x : ℂ) - periodize L (ThetaZd (‖m‖ ^ 2) s) x‖ ≤ δ / (1 - ‖m‖ ^ 2) ^ 2 := by
  set a : ℝ := ‖m‖ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 := by rw [ha]; nlinarith [norm_nonneg m]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [ThetaDecay_Theta_eq S hS m hm x, periodize_eq _ hΘs x, ← mul_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ k : Zd d L,
      ‖(a : ℂ) * symbol (cmat S) k / (1 - (a : ℂ) * symbol (cmat S) k) * zchar k (-x) -
        zdSeries (ThetaZd a s) (zfreqPi k) * zchar k (-x)‖ ≤ δ / (1 - a) ^ 2 := by
    intro k
    have hp := ThetaDecay_zfreqPi_mem k
    obtain ⟨him, hre⟩ := hreal _ hp
    have hse : zdSymbol s (zfreqPi k) = (((zdSymbol s (zfreqPi k)).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    rw [← sub_mul, norm_mul, norm_zchar, mul_one, hser _ hp, hse]
    refine (ThetaDecay_F_sub_le ha0 ha1 (hS.norm_symbol_le k) hre).trans ?_
    rw [← hse]
    gcongr
    exact hclose k
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((L : ℝ) ^ d)⁻¹ * ‖∑ k : Zd d L, ((a : ℂ) * symbol (cmat S) k /
          (1 - (a : ℂ) * symbol (cmat S) k) * zchar k (-x) -
        zdSeries (ThetaZd a s) (zfreqPi k) * zchar k (-x))‖
      ≤ ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, δ / (1 - a) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hterm k)
    _ = δ / (1 - a) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast
        field_simp

end Replacement

/-! ## Consequences of `(W, L) ∈ adm(c₀, c₁)` and `z ∈ 𝐃(κ, ε)` -/

section Window

variable {d L : ℕ}

/-- `1 ≤ L`, `W ≤ L`, `L^{c₁} ≤ W` and `η ≥ L^{-2}`, `η ≥ W²/L^{2-ε}` for
`(W, L) ∈ adm(c₀, c₁)`, `W ≥ 1`, `z ∈ 𝐃(κ, ε)`. -/
private theorem ThetaDecay_window {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hε : 0 < ε) {W L : ℕ}
    [NeZero L] (hadm : (W, L) ∈ adm c₀ c₁) (hW1 : (1 : ℝ) ≤ W) {z : ℂ}
    (hz : z ∈ specDom κ ε W L) :
    (1 : ℝ) ≤ L ∧ (W : ℝ) ≤ L ∧ (L : ℝ) ^ c₁ ≤ W ∧ 1 / (L : ℝ) ^ 2 ≤ z.im ∧ 0 < z.im ∧
      z.im ≤ 1 := by
  obtain ⟨hre, hη, hη1⟩ := hz
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hWL : (W : ℝ) ≤ L := hadm.2.trans (Real.rpow_le_self_of_one_le hL1 (by linarith))
  have hηL : 1 / (L : ℝ) ^ 2 ≤ z.im := by
    refine le_trans ?_ hη
    have h1 : (L : ℝ) ^ (2 - ε) ≤ (L : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    rw [Real.rpow_two] at h1
    have h0 : 0 < (L : ℝ) ^ (2 - ε) := by positivity
    calc 1 / (L : ℝ) ^ 2 ≤ 1 / (L : ℝ) ^ (2 - ε) := one_div_le_one_div_of_le h0 h1
      _ ≤ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) := by gcongr; nlinarith
  exact ⟨hL1, hWL, hadm.1, hηL, lt_of_lt_of_le (by positivity) hηL, hη1⟩

/-- `⟨x⟩ = ‖x‖_L + W ≤ 2L` for `W ≤ L`. -/
private theorem ThetaDecay_bracket_le [NeZero L] {W : ℕ} (hWL : (W : ℝ) ≤ L) (x : Zd d L) :
    (zdistInf d L x : ℝ) + W ≤ 2 * L := by
  have h1 : zdistInf d L x ≤ L := (zdistInf_le_half d L x).trans (Nat.div_le_self L 2)
  have h2 : (zdistInf d L x : ℝ) ≤ L := by exact_mod_cast h1
  linarith

/-- `(2L)^{-D} ≤ ⟨x⟩^{-D}` for `1 ≤ W ≤ L`, `D ≥ 0`. -/
private theorem ThetaDecay_two_L_rpow_le [NeZero L] {W : ℕ} (hW1 : (1 : ℝ) ≤ W)
    (hWL : (W : ℝ) ≤ L) {D : ℝ} (hD : 0 ≤ D) (x : Zd d L) :
    2 ^ (-D) * (L : ℝ) ^ (-D) ≤ ((zdistInf d L x : ℝ) + W) ^ (-D) := by
  have hX : 0 < (zdistInf d L x : ℝ) + W := by positivity
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos hX (ThetaDecay_bracket_le hWL x) (by linarith)

/-- `A L^{-(D+1)} ≤ (2L)^{-D}` for `2^D A ≤ L`, `L > 0`. -/
private theorem ThetaDecay_absorb {A Lr D : ℝ} (hL : 0 < Lr) (hA : 2 ^ D * A ≤ Lr) :
    A * Lr ^ (-(D + 1)) ≤ 2 ^ (-D) * Lr ^ (-D) := by
  have e : Lr ^ (-D) = Lr ^ (-(D + 1)) * Lr := by
    rw [show -D = -(D + 1) + 1 by ring, Real.rpow_add hL, Real.rpow_one]
  rw [e]
  have h2 : 0 < (2 : ℝ) ^ D := by positivity
  have h3 : (2 : ℝ) ^ (-D) * 2 ^ D = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have h4 : 0 < Lr ^ (-(D + 1)) := by positivity
  have h5 : A ≤ 2 ^ (-D) * Lr := by
    calc A = 2 ^ (-D) * (2 ^ D * A) := by rw [← mul_assoc, h3, one_mul]
      _ ≤ 2 ^ (-D) * Lr := by gcongr
  calc A * Lr ^ (-(D + 1)) ≤ 2 ^ (-D) * Lr * Lr ^ (-(D + 1)) := by gcongr
    _ = 2 ^ (-D) * (Lr ^ (-(D + 1)) * Lr) := by ring

/-- `L^{e} ≤ W^{n}` for `L^{c₁} ≤ W`, `e ≤ c₁ n`, `1 ≤ L`. -/
private theorem ThetaDecay_L_rpow_le_W_pow {Lr Wr c₁ e : ℝ} (hc₁ : 0 < c₁) (hL1 : 1 ≤ Lr)
    (hLc : Lr ^ c₁ ≤ Wr) {n : ℕ} (hn : e ≤ c₁ * n) : Lr ^ e ≤ Wr ^ n := by
  calc Lr ^ e ≤ Lr ^ (c₁ * n) := Real.rpow_le_rpow_of_exponent_le hL1 hn
    _ = (Lr ^ c₁) ^ n := Real.rpow_mul_natCast (by linarith) _ _
    _ ≤ Wr ^ n := pow_le_pow_left₀ (by positivity) hLc n

end Window

/-! ## The replacement `Θ ↔ Σ_n Θ_{ℤ^d}(· + L n)` -/

/-- `Θ` on `Z_L^d` is the periodisation of `Θ_{ℤ^d}` at `a = |m(z)|²` up to `⟨x⟩^{-D}`: for
`d ≥ 3`, `(W, L) ∈ adm(c₀, c₁)`, `W ≥ W₀`, a symmetric kernel `S` on `Z_L^d` and a kernel `s`
on `ℤ^d` whose symbols are both close to `ψ(W·)` with the constants `C`, and
`z ∈ 𝐃(κ, ε)`: `|Θ_{0x}(z) - Σ_{n ∈ ℤ^d} Θ_{ℤ^d}([x]_L + L n)| ≤ (‖x‖_L + W)^{-D}`. This is the
step from the torus to `ℤ^d` in the proof of [I, (1.17)]; the paper does this through
[I, Appendix B]. -/
theorem Theta_sub_periodize :
  ∀ (d : ℕ) (hd : 3 ≤ d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ)
    (κ ε D : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (hD : 0 < D),
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsSymKernel S → SymbolClose ψ C W S →
      ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        ‖(Theta (msc z) S 0 x : ℂ) - periodize L (ThetaZd (‖msc z‖ ^ 2) s) x‖ ≤
          ((zdistInf d L x : ℝ) + W) ^ (-D) := by
  intro d hd c₀ c₁ hc₀ hc₁ ψ cψ hψ C κ ε D hκ hε hD
  obtain ⟨Wt, hWt1, ht⟩ := ThetaDecay_theta_series d hd ψ cψ hψ C
  obtain ⟨c, W₂, hc, hW₂⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  set D' : ℕ := ⌈(D + 5) / c₁⌉₊ with hD'
  set A : ℝ := 8 * |C D'| with hA
  refine ⟨max (max Wt W₂) (2 ^ D * A), ?_⟩
  intro W L _ hadm hW S hS hSc s hs z hz x
  have hWt : Wt ≤ (W : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ (W : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWA : 2 ^ D * A ≤ (W : ℝ) := le_trans (le_max_right _ _) hW
  have hW1 : (1 : ℝ) ≤ W := hWt1.trans hWt
  obtain ⟨hL1, hWL, hLc, hηL, hηpos, hη1⟩ := ThetaDecay_window hc₀ hε hadm hW1 hz
  have hL0 : (0 : ℝ) < L := by linarith
  have hm1 := norm_msc_lt_one hηpos
  have hgap := ThetaDecay_one_sub_ge hηpos hη1
  obtain ⟨hΘs, hser⟩ := ht W hWt s hs _ (by positivity) (ThetaDecay_sq_lt_one hηpos)
  have hreal : ∀ p ∈ cubePi d, (zdSymbol s p).im = 0 ∧ (zdSymbol s p).re ≤ 1 := by
    intro p hp
    obtain ⟨him, hge⟩ := hW₂ W hW2 s hs p hp
    refine ⟨him, ?_⟩
    have : 0 ≤ c * min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
      mul_nonneg hc.le (le_min (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => sq_nonneg (p i))) zero_le_one)
    linarith
  set δ : ℝ := 2 * (|C D'| / (W : ℝ) ^ D') with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hclose : ∀ k, ‖symbol (cmat S) k - zdSymbol s (zfreqPi k)‖ ≤ δ := by
    intro k
    have h1 := hSc D' k
    have h2 := hs.close D' (zfreqPi k) (ThetaDecay_zfreqPi_mem k)
    have e : zfreq k = WithLp.toLp 2 (zfreqPi k) := rfl
    rw [e] at h1
    have h3 : C D' / (W : ℝ) ^ D' ≤ |C D'| / (W : ℝ) ^ D' :=
      div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
    calc ‖symbol (cmat S) k - zdSymbol s (zfreqPi k)‖ =
          ‖(symbol (cmat S) k - (ψ ((W : ℝ) • WithLp.toLp 2 (zfreqPi k)) : ℂ)) -
            (zdSymbol s (zfreqPi k) - (ψ ((W : ℝ) • WithLp.toLp 2 (zfreqPi k)) : ℂ))‖ := by
          congr 1; ring
      _ ≤ _ := norm_sub_le _ _
      _ ≤ δ := by rw [hδ]; linarith
  have hmain := ThetaDecay_sub_periodize_le S hS s (msc z) hm1 δ hΘs hser hreal hclose x
  refine hmain.trans ?_
  -- the numerics: `δ/(1 - a)² ≤ 4 δ L⁴ ≤ A L^{-(D+1)} ≤ (2L)^{-D} ≤ ⟨x⟩^{-D}`
  have hη2 : 0 < z.im / 2 := by positivity
  have h1 : δ / (1 - ‖msc z‖ ^ 2) ^ 2 ≤ δ / (z.im / 2) ^ 2 :=
    div_le_div_of_nonneg_left hδ0 (by positivity) (pow_le_pow_left₀ hη2.le hgap 2)
  have h2 : δ / (z.im / 2) ^ 2 ≤ 4 * δ * (L : ℝ) ^ 4 := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : 1 ≤ z.im * (L : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hηL; linarith
    have h4 : 1 ≤ (z.im * (L : ℝ) ^ 2) ^ 2 := by nlinarith
    nlinarith
  have hWD : (L : ℝ) ^ (D + 5) ≤ (W : ℝ) ^ D' := by
    refine ThetaDecay_L_rpow_le_W_pow hc₁ hL1 hLc ?_
    have := Nat.le_ceil ((D + 5) / c₁)
    rw [← hD'] at this
    rw [div_le_iff₀ hc₁] at this
    linarith
  have h5 : 4 * δ * (L : ℝ) ^ 4 ≤ A * (L : ℝ) ^ (-(D + 1)) := by
    have hL5 : 0 < (L : ℝ) ^ (D + 5) := by positivity
    have e : (L : ℝ) ^ (-(D + 1)) = (L : ℝ) ^ 4 / (L : ℝ) ^ (D + 5) := by
      rw [show -(D + 1) = (4 : ℕ) - (D + 5) by push_cast; ring, Real.rpow_sub hL0,
        Real.rpow_natCast]
    rw [e, hδ, hA]
    have hWp : 0 < (W : ℝ) ^ D' := by positivity
    have : |C D'| / (W : ℝ) ^ D' ≤ |C D'| / (L : ℝ) ^ (D + 5) :=
      div_le_div_of_nonneg_left (abs_nonneg _) hL5 hWD
    have hL4 : 0 ≤ (L : ℝ) ^ 4 := by positivity
    calc 4 * (2 * (|C D'| / (W : ℝ) ^ D')) * (L : ℝ) ^ 4 =
          8 * (|C D'| / (W : ℝ) ^ D') * (L : ℝ) ^ 4 := by ring
      _ ≤ 8 * (|C D'| / (L : ℝ) ^ (D + 5)) * (L : ℝ) ^ 4 := by gcongr
      _ = 8 * |C D'| * ((L : ℝ) ^ 4 / (L : ℝ) ^ (D + 5)) := by ring
  have h6 := ThetaDecay_absorb hL0 (hWA.trans hWL)
  have h7 := ThetaDecay_two_L_rpow_le hW1 hWL hD.le x
  linarith

/-! ## The row sum -/

/-- The row sum of `Θ` for a symmetric kernel with row sums one ([I, (sumTheta)]):
`Σ_y Θ_{xy}(z) = |m|²/(1 - |m|²) = Im m(z)/η` for `η = Im z > 0`. -/
theorem Theta_rowSum :
  ∀ {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : IsSymKernel S)
    (hS1 : ∀ x, ∑ y, S x y = 1) (z : ℂ) (hz : 0 < z.im) (x : Zd d L),
    ∑ y, Theta (msc z) S x y = (msc z).im / z.im := by
  intro d L _ S hS hS1 z hz x
  set m := msc z with hmdef
  have hm1 : ‖m‖ < 1 := norm_msc_lt_one hz
  have hT := (TransInv_propagators S hS.transInv m).2.2
  have hm' : ∀ k, (‖m‖ ^ 2 : ℂ) * symbol (cmat S) k ≠ 1 := by
    intro k h
    have h1 := congrArg norm h
    rw [norm_mul, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm] at h1
    have h2 := hS.norm_symbol_le k
    have h3 : ‖m‖ ^ 2 < 1 := by nlinarith [norm_nonneg m]
    nlinarith [norm_nonneg (symbol (cmat S) k), sq_nonneg ‖m‖]
  have hrow : ∑ y, Theta m S x y = ∑ y, Theta m S 0 y := by
    have e : ∀ y, Theta m S x y = Theta m S 0 (y - x) := by
      intro y
      have := hT x y (-x)
      rw [← this]
      congr 1 <;> abel
    simp_rw [e]
    exact Fintype.sum_equiv (Equiv.subRight x) _ _ fun y => rfl
  have hsym : ((∑ y, Theta m S 0 y : ℝ) : ℂ) = symbol (cmat (Theta m S)) 0 := by
    simp [symbol, zchar, cmat]
  have hS0 : symbol (cmat S) 0 = 1 := by
    have : ((∑ y, S 0 y : ℝ) : ℂ) = symbol (cmat S) 0 := by simp [symbol, zchar, cmat]
    rw [← this, hS1 0]; simp
  have ha1 := ThetaDecay_sq_lt_one hz
  have hval : ((∑ y, Theta m S 0 y : ℝ) : ℂ) = ((‖m‖ ^ 2 / (1 - ‖m‖ ^ 2) : ℝ) : ℂ) := by
    rw [hsym, symbol_Theta S hS.transInv m hm' 0, hS0]
    push_cast
    ring
  rw [hrow, ← ThetaDecay_ratio hz]
  exact_mod_cast hval

/-! ## Bookkeeping for the decay bounds -/

section Bookkeeping

variable {d L : ℕ}

private theorem ThetaDecay_infKernel_mono {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C C' : ℕ → ℝ}
    {W : ℕ} {s : (Fin d → ℤ) → ℝ} (hs : InfKernel ψ C W s) (hC : ∀ n, C n ≤ C' n) :
    InfKernel ψ C' W s where
  symm := hs.symm
  sum_one := hs.sum_one
  decay k x := (hs.decay k x).trans (div_le_div_of_nonneg_right (hC k) (by positivity))
  close D' p hp := (hs.close D' p hp).trans (div_le_div_of_nonneg_right (hC D') (by positivity))

private theorem ThetaDecay_symbolClose_mono [NeZero L] {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)}
    {C C' : ℕ → ℝ} {W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ} (hS : SymbolClose ψ C W S)
    (hC : ∀ n, C n ≤ C' n) : SymbolClose ψ C' W S := fun D' k =>
  (hS D' k).trans (div_le_div_of_nonneg_right (hC D') (by positivity))

/-- `Θ_{xy} = Θ_{0, y - x}`. -/
private theorem ThetaDecay_Theta_translate [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS : IsSymKernel S) (m : ℂ) (x y : Zd d L) : Theta m S x y = Theta m S 0 (y - x) := by
  have hT := (TransInv_propagators S hS.transInv m).2.2
  have := hT x y (-x)
  rw [← this]
  congr 1 <;> abel

/-- `B_{xy} = W^{-2} (‖x - y‖_L + W)^{-(d-2)}` with natural exponents. -/
private theorem ThetaDecay_bB_eq [NeZero L] (hd : 2 ≤ d) {W : ℕ} (hW : (0 : ℝ) < W)
    (x y : Zd d L) :
    bB d L W x y = 1 / ((W : ℝ) ^ 2 * ((zdistInf d L (x - y) : ℝ) + W) ^ (d - 2)) := by
  unfold bB
  have hX : 0 < (zdistInf d L (x - y) : ℝ) + W := by positivity
  rw [show (2 - (d : ℝ)) = -((d - 2 : ℕ) : ℝ) by rw [Nat.cast_sub hd]; push_cast; ring,
    Real.rpow_neg hX.le, Real.rpow_natCast, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hW.le, Real.rpow_natCast, one_div, mul_inv]

/-- `R/L ≤ 2 L^{-ε/2}` for `R = W/σ`, `σ² ≥ W²/(2 L^{2-ε})`. -/
private theorem ThetaDecay_R_div_L_le {Lr Wr σ ε : ℝ} (hL1 : 1 ≤ Lr) (hW : 0 < Wr) (hσ : 0 < σ)
    (hσ2 : Wr ^ 2 / Lr ^ (2 - ε) / 2 ≤ σ ^ 2) : Wr / σ / Lr ≤ 2 * Lr ^ (-(ε / 2)) := by
  have hL0 : 0 < Lr := by linarith
  have hq0 : 0 ≤ Wr / σ / Lr := by positivity
  have h2 : 0 ≤ 2 * Lr ^ (-(ε / 2)) := by positivity
  refine (pow_le_pow_iff_left₀ hq0 h2 (two_ne_zero)).mp ?_
  have e1 : (2 * Lr ^ (-(ε / 2))) ^ 2 = 4 * Lr ^ (-ε) := by
    rw [mul_pow, ← Real.rpow_natCast (Lr ^ (-(ε / 2))), ← Real.rpow_mul hL0.le]
    norm_num
  have e2 : Lr ^ (2 - ε) = Lr ^ 2 * Lr ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hL0, Real.rpow_two]
  rw [e2, div_div, div_le_iff₀ (by positivity)] at hσ2
  have hLe : 0 < Lr ^ (-ε) := by positivity
  rw [e1, div_pow, div_pow, div_div, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg σ, sq_nonneg Lr]

/-- `(R/L)^M ≤ 2^M L^{-(D+1)}` for `R/L ≤ 2 L^{-e}`, `D + 1 ≤ e M`. -/
private theorem ThetaDecay_RL_pow_le {Lr q e D : ℝ} (hL1 : 1 ≤ Lr) (hq : 0 ≤ q)
    (hqL : q ≤ 2 * Lr ^ (-e)) {M : ℕ} (hM : D + 1 ≤ e * M) :
    q ^ M ≤ 2 ^ M * Lr ^ (-(D + 1)) := by
  have hL0 : 0 < Lr := by linarith
  calc q ^ M ≤ (2 * Lr ^ (-e)) ^ M := pow_le_pow_left₀ hq hqL M
    _ = 2 ^ M * Lr ^ (-e * M) := by rw [mul_pow, Real.rpow_mul_natCast hL0.le]
    _ ≤ 2 ^ M * Lr ^ (-(D + 1)) := by
        gcongr
        linarith

/-- `2 L^{-ε/2} ≤ 1` for `L ≥ 2^{2/ε}`. -/
private theorem ThetaDecay_two_rpow_le_one {Lr ε : ℝ} (hε : 0 < ε) (hL : (2 : ℝ) ^ (2 / ε) ≤ Lr) :
    2 * Lr ^ (-(ε / 2)) ≤ 1 := by
  have h0 : 0 < (2 : ℝ) ^ (2 / ε) := by positivity
  have hL0 : 0 < Lr := lt_of_lt_of_le h0 hL
  have h1 : (2 : ℝ) ≤ Lr ^ (ε / 2) := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul (by norm_num), show 2 / ε * (ε / 2) = 1 by field_simp,
            Real.rpow_one]
      _ ≤ Lr ^ (ε / 2) := Real.rpow_le_rpow h0.le hL (by positivity)
  rw [Real.rpow_neg hL0.le]
  have : 0 < Lr ^ (ε / 2) := by positivity
  rw [← div_eq_mul_inv, div_le_one this]
  exact h1

/-- Outside the cutoff `|x| > η^{-1/2} W^{1+τ}` and for `σ² ≥ η/2`: `|x| σ/W ≥ W^τ/2`. -/
private theorem ThetaDecay_outside {r η σ Wr τ : ℝ} (hη : 0 < η) (hW : 0 < Wr) (hσ : 0 ≤ σ)
    (hσ2 : η / 2 ≤ σ ^ 2) (hr : η ^ (-(1 / 2 : ℝ)) * Wr ^ (1 + τ) < r) :
    Wr ^ τ / 2 ≤ r * σ / Wr := by
  have hsq : Real.sqrt η / 2 ≤ σ := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h1 : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
    nlinarith [Real.sqrt_nonneg η]
  have he : η ^ (-(1 / 2 : ℝ)) = (Real.sqrt η)⁻¹ := by
    rw [Real.rpow_neg hη.le, Real.sqrt_eq_rpow]
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  rw [he, Real.rpow_add hW, Real.rpow_one] at hr
  rw [le_div_iff₀ hW]
  have hWt : 0 < Wr ^ τ := by positivity
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have h2 : (Real.sqrt η)⁻¹ * (Wr * Wr ^ τ) * (Real.sqrt η / 2) ≤ r * σ := by
    have := mul_le_mul hr.le hsq (by positivity) hr0.le
    linarith
  have e : (Real.sqrt η)⁻¹ * (Wr * Wr ^ τ) * (Real.sqrt η / 2) = Wr ^ τ / 2 * Wr := by
    field_simp
  linarith

/-- `L^{e} ≤ (W^τ)^M` for `L^{c₁} ≤ W`, `e ≤ c₁ τ M`, `1 ≤ L`. -/
private theorem ThetaDecay_L_rpow_le_W_rpow_pow {Lr Wr c₁ τ e : ℝ} (hc₁ : 0 < c₁) (hτ : 0 < τ)
    (hL1 : 1 ≤ Lr) (hLc : Lr ^ c₁ ≤ Wr) {M : ℕ} (hM : e ≤ c₁ * (τ * M)) :
    Lr ^ e ≤ (Wr ^ τ) ^ M := by
  have hL0 : 0 < Lr := by linarith
  have hWr : 0 < Wr := lt_of_lt_of_le (by positivity) hLc
  calc Lr ^ e ≤ Lr ^ (c₁ * (τ * M)) := Real.rpow_le_rpow_of_exponent_le hL1 hM
    _ = (Lr ^ c₁) ^ (τ * M) := Real.rpow_mul hL0.le _ _
    _ ≤ Wr ^ (τ * M) := Real.rpow_le_rpow (by positivity) hLc (by positivity)
    _ = (Wr ^ τ) ^ M := Real.rpow_mul_natCast hWr.le _ _

/-- `C₀ ≤ W^τ` for `W ≥ C₀^{1/τ}`. -/
private theorem ThetaDecay_le_rpow {A Wr τ : ℝ} (hτ : 0 < τ) (hA : 0 ≤ A)
    (hW : A ^ (1 / τ) ≤ Wr) : A ≤ Wr ^ τ := by
  calc A = (A ^ (1 / τ)) ^ τ := by
        rw [← Real.rpow_mul hA, show 1 / τ * τ = 1 by field_simp, Real.rpow_one]
    _ ≤ Wr ^ τ := Real.rpow_le_rpow (by positivity) hW hτ.le

end Bookkeeping

/-! ## The decay of `Θ` -/

/-- [I, (1.17)]: for `d ≥ 3` and `W ≥ W₀`, uniformly in `(W, L) ∈ adm(c₀, c₁)`, in symmetric
kernels `S` on `Z_L^d` whose symbol is close to `ψ(W·)` with the constants `C`, in
`z ∈ 𝐃(κ, ε)` and in `x, y ∈ Z_L^d`:
`|Θ_{xy}(z)| ≤ W^τ 1(‖x - y‖_L ≤ η^{-1/2} W^{1+τ}) B_{xy} + (‖x - y‖_L + W)^{-D}`, with
`B_{xy}` of [I, (1.18)] and `η = Im z`. The constant in front of the right side is `1`. -/
theorem Theta_decay :
  ∀ (d : ℕ) (hd : 3 ≤ d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ)
    (κ ε τ D : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (hτ : 0 < τ) (hD : 0 < D),
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsSymKernel S → SymbolClose ψ C W S →
      ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L,
        |Theta (msc z) S x y| ≤ thetaBound W z.im τ D x y := by
  intro d hd c₀ c₁ hc₀ hc₁ ψ cψ hψ C κ ε τ D hκ hε hτ hD
  obtain ⟨Ci, Wi, hinf⟩ := Sinf_infKernel d ψ cψ hψ
  set C' : ℕ → ℝ := fun n => max (C n) (Ci n) with hC'
  have hCC' : ∀ n, C n ≤ C' n := fun n => le_max_left _ _
  have hCiC' : ∀ n, Ci n ≤ C' n := fun n => le_max_right _ _
  obtain ⟨Wr, hrep⟩ := Theta_sub_periodize d hd c₀ c₁ hc₀ hc₁ ψ cψ hψ C' κ ε (D + 1) hκ hε
    (by linarith)
  set M : ℕ := max (d + 1) (max ⌈2 * (D + 1) / ε⌉₊ ⌈(D + 1) / (c₁ * τ)⌉₊) with hM
  have hMd : d + 1 ≤ M := le_max_left _ _
  have hMε : D + 1 ≤ ε / 2 * M := by
    have h1 : (⌈2 * (D + 1) / ε⌉₊ : ℝ) ≤ M := by
      exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
    have h2 := Nat.le_ceil (2 * (D + 1) / ε)
    rw [div_le_iff₀ hε] at h2
    nlinarith
  have hMτ : D + 1 ≤ c₁ * (τ * M) := by
    have h1 : (⌈(D + 1) / (c₁ * τ)⌉₊ : ℝ) ≤ M := by
      exact_mod_cast (le_max_right _ _).trans (le_max_right _ _)
    have h2 := Nat.le_ceil ((D + 1) / (c₁ * τ))
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith [mul_pos hc₁ hτ]
  obtain ⟨C₀, Wd, hdec⟩ := ThetaZd_decay d hd ψ cψ hψ C' M
  obtain ⟨Wt, hWt1, ht⟩ := ThetaDecay_theta_series d hd ψ cψ hψ C'
  obtain ⟨CT, hCT⟩ := tsum_periodize_le d M hMd
  set A : ℝ := |C₀| * 2 ^ M * (|CT| + 1) with hA
  refine ⟨max (max (max Wi Wr) (max Wd Wt))
    (max (max (2 ^ D * (2 * A)) 2) (max (|C₀| ^ (1 / τ)) (2 ^ (2 / ε)))), ?_⟩
  intro W L _ hadm hW S hS hSc z hz x y
  have hWi : Wi ≤ (W : ℝ) := le_trans (by simp) hW
  have hWr : Wr ≤ (W : ℝ) := le_trans (by simp) hW
  have hWd : Wd ≤ (W : ℝ) := le_trans (by simp) hW
  have hWt : Wt ≤ (W : ℝ) := le_trans (by simp) hW
  have hWA : 2 ^ D * (2 * A) ≤ (W : ℝ) := le_trans (by simp) hW
  have hW2 : (2 : ℝ) ≤ W := le_trans (by simp) hW
  have hWC : |C₀| ^ (1 / τ) ≤ (W : ℝ) := le_trans (by simp) hW
  have hWe : (2 : ℝ) ^ (2 / ε) ≤ W := le_trans (by simp) hW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hL1, hWL, hLc, hηL, hηpos, hη1⟩ := ThetaDecay_window hc₀ hε hadm hW1 hz
  have hL0 : (0 : ℝ) < L := by linarith
  have hs : InfKernel ψ C' W (Sinf ψ W) := ThetaDecay_infKernel_mono (hinf W hWi) hCiC'
  have hSc' := ThetaDecay_symbolClose_mono hSc hCC'
  have ha0 : 0 ≤ ‖msc z‖ ^ 2 := by positivity
  have ha1 := ThetaDecay_sq_lt_one hηpos
  have hgap := ThetaDecay_one_sub_ge hηpos hη1
  set a : ℝ := ‖msc z‖ ^ 2 with ha
  set σ : ℝ := Real.sqrt (1 - a) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by linarith)
  have hσ2 : σ ^ 2 = 1 - a := Real.sq_sqrt (by linarith)
  obtain ⟨hΘs, -⟩ := ht W hWt (Sinf ψ W) hs a ha0 ha1
  obtain ⟨-, hb⟩ := hdec W hWd (Sinf ψ W) hs a ha0 ha1.le
  set u : Zd d L := y - x with hu
  have hxy : zdistInf d L (x - y) = zdistInf d L u := by
    rw [hu, ← zdistInf_neg d L (y - x), neg_sub]
  rw [ThetaDecay_Theta_translate S hS (msc z) x y, ← hu]
  have hP1 := hrep W L hadm hWr S hS hSc' (Sinf ψ W) hs z hz u
  -- the scale `R = W (1 - a)^{-1/2}`
  set R : ℝ := W / σ with hR
  have hR0 : 0 < R := by positivity
  have hRL : R / L ≤ 2 * (L : ℝ) ^ (-(ε / 2)) := by
    refine ThetaDecay_R_div_L_le hL1 hW0 hσ0 ?_
    rw [hσ2]
    have := hz.2.1
    linarith
  have h2L : 2 * (L : ℝ) ^ (-(ε / 2)) ≤ 1 := ThetaDecay_two_rpow_le_one hε (hWe.trans hWL)
  have hRleL : R ≤ L := by
    have := hRL.trans h2L
    rwa [div_le_one hL0] at this
  have hrpow : (R / L) ^ M ≤ 2 ^ M * (L : ℝ) ^ (-(D + 1)) :=
    ThetaDecay_RL_pow_le hL1 (by positivity) hRL hMε
  have hterm : ∀ v : Fin d → ℤ, ‖ThetaZd a (Sinf ψ W) v‖ ≤
      C₀ / ((W : ℝ) ^ 2 * ((zdInf v : ℝ) + W) ^ (d - 2)) / (1 + (zdInf v : ℝ) * σ / W) ^ M := by
    intro v
    rw [le_div_iff₀ (by positivity)]
    exact hb v
  have hden1 : ∀ v : Fin d → ℤ, 1 ≤ (W : ℝ) ^ 2 * ((zdInf v : ℝ) + W) ^ (d - 2) := fun v =>
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1)
      (one_le_pow₀ (by linarith [(Nat.cast_nonneg (zdInf v) : (0 : ℝ) ≤ zdInf v)]))
  have hterm2 : ∀ v : Fin d → ℤ, ‖ThetaZd a (Sinf ψ W) v‖ ≤
      |C₀| * ((1 + (zdInf v : ℝ) / R) ^ M)⁻¹ := by
    intro v
    have e : (zdInf v : ℝ) / R = (zdInf v : ℝ) * σ / W := by rw [hR]; field_simp
    rw [e]
    refine (hterm v).trans ?_
    rw [div_eq_mul_inv _ ((1 + _) ^ M)]
    gcongr
    exact (div_le_div_of_nonneg_right (le_abs_self C₀) (by positivity)).trans
      (div_le_self (abs_nonneg _) (hden1 v))
  -- the periodisation: the term `n = 0` and the images `n ≠ 0`
  have hwrap : ‖periodize L (ThetaZd a (Sinf ψ W)) u‖ ≤
      ‖ThetaZd a (Sinf ψ W) (zlift u)‖ + |C₀| * |CT| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by
    have hinj : Function.Injective fun n : Fin d → ℤ => zlift u + (L : ℤ) • n := by
      intro n₁ n₂ h
      have hL' : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
      funext i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
      exact mul_left_cancel₀ hL' this
    have hf : Summable fun n => ‖ThetaZd a (Sinf ψ W) (zlift u + (L : ℤ) • n)‖ :=
      hΘs.comp_injective hinj
    have hbs := (ThetaDecay_term_summable M hMd R hR0 u).mul_left |C₀|
    have h := ThetaDecay_norm_tsum_le _ hf _ hbs (fun n => hterm2 _)
    simp only [smul_zero, add_zero] at h
    unfold periodize
    refine h.trans ?_
    gcongr
    rw [tsum_mul_left]
    have hT := hCT L R hR0 hRleL u
    have hq : 0 ≤ (R / L) ^ M := by positivity
    calc |C₀| * ∑' n : {n : Fin d → ℤ // n ≠ 0},
          ((1 + (zdInf (zlift u + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹
        ≤ |C₀| * (|CT| * (2 ^ M * (L : ℝ) ^ (-(D + 1)))) := by
          gcongr
          calc _ ≤ CT * (R / L) ^ M := hT
            _ ≤ |CT| * (R / L) ^ M := by gcongr; exact le_abs_self _
            _ ≤ _ := by gcongr
      _ = |C₀| * |CT| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by ring
  -- the term `n = 0`
  have hz0 : zdInf (zlift u) = zdistInf d L u := ThetaDecay_zdInf_zlift u
  have hX : (2 : ℝ) ≤ (zdistInf d L u : ℝ) + W := by
    have := (Nat.cast_nonneg (zdistInf d L u) : (0 : ℝ) ≤ _); linarith
  have hX0 : (0 : ℝ) < (zdistInf d L u : ℝ) + W := by linarith
  have hhalf : ((zdistInf d L u : ℝ) + W) ^ (-(D + 1)) ≤
      ((zdistInf d L u : ℝ) + W) ^ (-D) / 2 := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hX0, Real.rpow_neg_one]
    rw [div_eq_mul_inv]
    gcongr
  have hAbs := ThetaDecay_absorb (A := 2 * A) hL0 (hWA.trans hWL)
  have h2L' := ThetaDecay_two_L_rpow_le hW1 hWL hD.le u
  have hA0 : 0 ≤ |C₀| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by positivity
  have hCT0 : 0 ≤ |C₀| * |CT| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by positivity
  have hsplit : |Theta (msc z) S 0 u| ≤ ((zdistInf d L u : ℝ) + W) ^ (-(D + 1)) +
      (‖ThetaZd a (Sinf ψ W) (zlift u)‖ + |C₀| * |CT| * 2 ^ M * (L : ℝ) ^ (-(D + 1))) := by
    have e : |Theta (msc z) S 0 u| = ‖(Theta (msc z) S 0 u : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [e]
    calc ‖(Theta (msc z) S 0 u : ℂ)‖ ≤
          ‖(Theta (msc z) S 0 u : ℂ) - periodize L (ThetaZd a (Sinf ψ W)) u‖ +
            ‖periodize L (ThetaZd a (Sinf ψ W)) u‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add hP1 hwrap
  have hAsplit : A * (L : ℝ) ^ (-(D + 1)) = |C₀| * |CT| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) +
      |C₀| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by rw [hA]; ring
  have hX0' : 0 ≤ ((zdistInf d L u : ℝ) + W) ^ (-D) := by positivity
  unfold thetaBound
  rw [hxy]
  split_ifs with hin
  · have hmain : ‖ThetaZd a (Sinf ψ W) (zlift u)‖ ≤ (W : ℝ) ^ τ * bB d L W x y := by
      rw [ThetaDecay_bB_eq (by omega) hW0, hxy]
      refine (hterm _).trans ?_
      rw [hz0]
      have h1 : 1 ≤ (1 + (zdistInf d L u : ℝ) * σ / W) ^ M := one_le_pow₀ (by
        have : 0 ≤ (zdistInf d L u : ℝ) * σ / W := by positivity
        linarith)
      have hC0 : |C₀| ≤ (W : ℝ) ^ τ := ThetaDecay_le_rpow hτ (abs_nonneg _) hWC
      calc C₀ / ((W : ℝ) ^ 2 * ((zdistInf d L u : ℝ) + W) ^ (d - 2)) /
            (1 + (zdistInf d L u : ℝ) * σ / W) ^ M
          ≤ |C₀| / ((W : ℝ) ^ 2 * ((zdistInf d L u : ℝ) + W) ^ (d - 2)) /
            (1 + (zdistInf d L u : ℝ) * σ / W) ^ M := by
            gcongr; exact le_abs_self _
        _ ≤ |C₀| / ((W : ℝ) ^ 2 * ((zdistInf d L u : ℝ) + W) ^ (d - 2)) :=
            div_le_self (by positivity) h1
        _ ≤ (W : ℝ) ^ τ / ((W : ℝ) ^ 2 * ((zdistInf d L u : ℝ) + W) ^ (d - 2)) := by
            gcongr
        _ = (W : ℝ) ^ τ * (1 / ((W : ℝ) ^ 2 * ((zdistInf d L u : ℝ) + W) ^ (d - 2))) := by
            ring
    linarith only [hsplit, hhalf, hmain, hAsplit, hA0, hAbs, h2L']
  · have hout : ‖ThetaZd a (Sinf ψ W) (zlift u)‖ ≤ |C₀| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by
      refine (hterm _).trans ?_
      rw [hz0]
      have hgap' : z.im / 2 ≤ σ ^ 2 := by rw [hσ2]; exact hgap
      have hw := ThetaDecay_outside hηpos hW0 hσ0.le hgap' (not_le.mp hin)
      have hWτ : 0 < (W : ℝ) ^ τ / 2 := by positivity
      have hpow : ((W : ℝ) ^ τ / 2) ^ M ≤ (1 + (zdistInf d L u : ℝ) * σ / W) ^ M :=
        pow_le_pow_left₀ hWτ.le (le_add_of_nonneg_of_le zero_le_one hw) M
      have hLW : (L : ℝ) ^ (D + 1) ≤ ((W : ℝ) ^ τ) ^ M :=
        ThetaDecay_L_rpow_le_W_rpow_pow hc₁ hτ hL1 hLc hMτ
      have hLp : 0 < (L : ℝ) ^ (D + 1) := by positivity
      have e : (L : ℝ) ^ (-(D + 1)) = ((L : ℝ) ^ (D + 1))⁻¹ := Real.rpow_neg hL0.le _
      rw [e]
      have hd1 := hden1 (zlift u)
      rw [hz0] at hd1
      have h1 : C₀ / ((W : ℝ) ^ 2 * ((zdistInf d L u : ℝ) + W) ^ (d - 2)) ≤ |C₀| :=
        (div_le_div_of_nonneg_right (le_abs_self C₀) (by positivity)).trans
          (div_le_self (abs_nonneg _) hd1)
      calc C₀ / ((W : ℝ) ^ 2 * ((zdistInf d L u : ℝ) + W) ^ (d - 2)) /
            (1 + (zdistInf d L u : ℝ) * σ / W) ^ M
          ≤ |C₀| / (1 + (zdistInf d L u : ℝ) * σ / W) ^ M := by gcongr
        _ ≤ |C₀| / ((W : ℝ) ^ τ / 2) ^ M := by gcongr
        _ = |C₀| * 2 ^ M / ((W : ℝ) ^ τ) ^ M := by
            rw [div_pow]; field_simp
        _ ≤ |C₀| * 2 ^ M / (L : ℝ) ^ (D + 1) := by gcongr
        _ = |C₀| * 2 ^ M * ((L : ℝ) ^ (D + 1))⁻¹ := by ring
    linarith only [hsplit, hhalf, hout, hAsplit, hAbs, h2L', hX0']

section Shells

variable {d L : ℕ}

end Shells

/-! ## Ingredients of the cancellation bound -/

section CancelParts

variable {d L : ℕ}

/-- The sum `Σ_x Φ_{x} g(x - x₀)` for `g` supported on `‖y‖_L ≤ K`, `2K < L`, split into the
replacement errors `Φ - Σ_n G(· + L n)` at `x₀ + [v]` and the image sums
`Σ_n Σ_{v ∈ ⟦-K, K⟧^d} G([x₀]_L + L n + v) g([v])`. -/
private theorem ThetaDecay_cancel_decomp [NeZero L] {K : ℕ} (hKL : 2 * K < L)
    (Φ : Zd d L → ℂ) (G : (Fin d → ℤ) → ℂ) (hG : Summable fun y => ‖G y‖) (g : Zd d L → ℝ)
    (hg : ∀ y, K < zdistInf d L y → g y = 0) (x₀ : Zd d L) :
    ∑ x, Φ x * (g (x - x₀) : ℂ) =
      ∑ v ∈ boxZ d K, (Φ (zcast L (zlift x₀ + v)) - periodize L G (zcast L (zlift x₀ + v))) *
          (g (zcast L v) : ℂ) +
        ∑' n : Fin d → ℤ, ∑ v ∈ boxZ d K,
          G (zlift x₀ + (L : ℤ) • n + v) * (g (zcast L v) : ℂ) := by
  have h1 : ∑ x, Φ x * (g (x - x₀) : ℂ) = ∑ y, Φ (x₀ + y) * (g y : ℂ) := by
    refine Fintype.sum_equiv (Equiv.subRight x₀) _ _ fun x => ?_
    simp
  rw [h1, ThetaDecay_sum_eq_sum_boxZ hKL _ (fun y hy => by rw [hg y hy]; simp)]
  have h2 : ∀ v, x₀ + zcast L v = zcast L (zlift x₀ + v) := by
    intro v; rw [ThetaDecay_zcast_add, ThetaDecay_zcast_zlift]
  simp_rw [h2]
  have h3 : ∀ v, periodize L G (zcast L (zlift x₀ + v)) =
      ∑' n : Fin d → ℤ, G (zlift x₀ + (L : ℤ) • n + v) := by
    intro v
    rw [ThetaDecay_periodize_zcast]
    refine tsum_congr fun n => ?_
    congr 1; abel
  have hsum : ∀ v ∈ boxZ d K, Summable fun n : Fin d → ℤ =>
      G (zlift x₀ + (L : ℤ) • n + v) * (g (zcast L v) : ℂ) := by
    intro v _
    have hinj : Function.Injective fun n : Fin d → ℤ => zlift x₀ + (L : ℤ) • n + v := by
      intro n₁ n₂ h
      have hL' : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
      funext i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj, add_right_inj] at this
      exact mul_left_cancel₀ hL' this
    exact ((hG.comp_injective hinj).of_norm).mul_right _
  rw [Summable.tsum_finsetSum hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [tsum_mul_right, ← h3]
  ring

/-- For `Σ_{v ∈ ⟦-K, K⟧^d} f(v) = 0`: `Σ_v |f(v)| ≤ 2 X² Σ_v (|v|/X)² |f(v)|`, `X > 0`. -/
private theorem ThetaDecay_sum_abs_le {K : ℕ} (f : (Fin d → ℤ) → ℝ)
    (hf : ∑ v ∈ boxZ d K, f v = 0) {X : ℝ} (hX : 0 < X) :
    ∑ v ∈ boxZ d K, |f v| ≤ 2 * X ^ 2 * ∑ v ∈ boxZ d K, ((zdInf v : ℝ) / X) ^ 2 * |f v| := by
  have h0 : (0 : Fin d → ℤ) ∈ boxZ d K := by
    simp only [boxZ, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i; simp
  rw [← Finset.add_sum_erase _ _ h0] at hf
  rw [← Finset.add_sum_erase _ _ h0]
  have hA : ∑ v ∈ (boxZ d K).erase 0, |f v| ≤
      X ^ 2 * ∑ v ∈ boxZ d K, ((zdInf v : ℝ) / X) ^ 2 * |f v| := by
    rw [Finset.mul_sum]
    calc ∑ v ∈ (boxZ d K).erase 0, |f v| ≤
          ∑ v ∈ (boxZ d K).erase 0, X ^ 2 * (((zdInf v : ℝ) / X) ^ 2 * |f v|) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hv0 := Finset.ne_of_mem_erase hv
          have h1 : (1 : ℝ) ≤ zdInf v := by exact_mod_cast ThetaDecay_zdInf_pos hv0
          have e : X ^ 2 * (((zdInf v : ℝ) / X) ^ 2 * |f v|) = (zdInf v : ℝ) ^ 2 * |f v| := by
            field_simp
          rw [e]
          have : (1 : ℝ) ≤ (zdInf v : ℝ) ^ 2 := one_le_pow₀ h1
          nlinarith [abs_nonneg (f v)]
      _ ≤ ∑ v ∈ boxZ d K, X ^ 2 * (((zdInf v : ℝ) / X) ^ 2 * |f v|) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun v _ _ => by positivity
  have hB : |f 0| ≤ ∑ v ∈ (boxZ d K).erase 0, |f v| := by
    have : f 0 = -∑ v ∈ (boxZ d K).erase 0, f v := by linarith
    rw [this, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have h3 : ∑ v ∈ (boxZ d K).erase 0, ((zdInf v : ℝ) / X) ^ 2 * |f v| ≤
      ∑ v ∈ boxZ d K, ((zdInf v : ℝ) / X) ^ 2 * |f v| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun v _ _ => by positivity
  have h4 : 0 ≤ ((zdInf (0 : Fin d → ℤ) : ℝ) / X) ^ 2 * |f 0| := by positivity
  nlinarith

/-- `2 X² (X/2)^{-(D+3)} ≤ X^{-D}/4` for `X ≥ 2^{D+6}`, `D ≥ 0`. -/
private theorem ThetaDecay_err_le {X D : ℝ} (hD : 0 ≤ D) (hX : (2 : ℝ) ^ (D + 6) ≤ X) :
    2 * X ^ 2 * (X / 2) ^ (-(D + 3)) ≤ X ^ (-D) / 4 := by
  have h2 : (0 : ℝ) < 2 ^ (D + 6) := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le h2 hX
  have e1 : (X / 2) ^ (-(D + 3)) = 2 ^ (D + 3) * X ^ (-D) * (X ^ 3)⁻¹ := by
    rw [Real.div_rpow hX0.le (by norm_num), Real.rpow_neg hX0.le, Real.rpow_neg (by norm_num),
      Real.rpow_neg hX0.le, Real.rpow_add hX0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    field_simp
  have e2 : (2 : ℝ) ^ (D + 6) = 2 ^ (D + 3) * 8 := by
    rw [show D + 6 = (D + 3) + 3 by ring, Real.rpow_add (by norm_num)]; norm_num
  rw [e1]
  have hXD : 0 < X ^ (-D) := by positivity
  have h3 : 0 < (2 : ℝ) ^ (D + 3) := by positivity
  rw [show 2 * X ^ 2 * (2 ^ (D + 3) * X ^ (-D) * (X ^ 3)⁻¹) =
      X ^ (-D) * (2 * 2 ^ (D + 3) / X) by field_simp]
  rw [div_eq_mul_inv (X ^ (-D)) 4]
  gcongr
  rw [div_le_iff₀ hX0]
  nlinarith

end CancelParts

/-! ## The cancellation lemma -/

/-- [I, Lemma 6.1]: for `d ≥ 3` and `W ≥ W₀`, uniformly in `(W, L) ∈ adm(c₀, c₁)`, in
symmetric kernels `S` whose symbol is close to `ψ(W·)`, in `z ∈ 𝐃(κ, ε)`, in `K ≥ W`, in
`g : Z_L^d → ℝ` symmetric, supported on `‖x‖_L ≤ K`, with `Σ_x g(x) = 0`, and in `x₀` with
`‖x₀‖_L ≥ K^{1+c}`:
`|Σ_x Θ_{0x}(z) g(x - x₀)| ≤ (Σ_x (‖x‖_L/‖x₀‖_L)² |g(x)|)
  (‖x₀‖_L^τ B_{0x₀} 1(‖x₀‖_L ≤ η^{-1/2} W^{1+τ}) + ‖x₀‖_L^{-D})`. -/
theorem Theta_cancel :
  ∀ (d : ℕ) (hd : 3 ≤ d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ)
    (κ ε c τ D : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (hc : 0 < c) (hτ : 0 < τ) (hD : 0 < D),
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsSymKernel S → SymbolClose ψ C W S →
      ∀ z ∈ specDom κ ε W L, ∀ (K : ℕ), W ≤ K → ∀ g : Zd d L → ℝ,
        (∀ x, g (-x) = g x) → (∀ x, K < zdistInf d L x → g x = 0) → ∑ x, g x = 0 →
        ∀ x₀ : Zd d L, (K : ℝ) ^ (1 + c) ≤ zdistInf d L x₀ →
          |∑ x, Theta (msc z) S 0 x * g (x - x₀)| ≤
            (∑ x, ((zdistInf d L x : ℝ) / zdistInf d L x₀) ^ 2 * |g x|) *
              ((if (zdistInf d L x₀ : ℝ) ≤ z.im ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + τ) then
                  (zdistInf d L x₀ : ℝ) ^ τ * bB d L W 0 x₀ else 0) +
                (zdistInf d L x₀ : ℝ) ^ (-D)) := by
  intro d hd c₀ c₁ hc₀ hc₁ ψ cψ hψ C κ ε c τ D hκ hε hc hτ hD
  obtain ⟨Ci, Wi, hinf⟩ := Sinf_infKernel d ψ cψ hψ
  set C' : ℕ → ℝ := fun n => max (C n) (Ci n) with hC'
  have hCC' : ∀ n, C n ≤ C' n := fun n => le_max_left _ _
  have hCiC' : ∀ n, Ci n ≤ C' n := fun n => le_max_right _ _
  obtain ⟨Wr, hrep⟩ := Theta_sub_periodize d hd c₀ c₁ hc₀ hc₁ ψ cψ hψ C' κ ε (D + 3) hκ hε
    (by linarith)
  set M : ℕ := max (d + 1) (max ⌈2 * (D + 1) / ε⌉₊ ⌈(D + 1) / (c₁ * τ)⌉₊) with hM
  have hMd : d + 1 ≤ M := le_max_left _ _
  have hMε : D + 1 ≤ ε / 2 * M := by
    have h1 : (⌈2 * (D + 1) / ε⌉₊ : ℝ) ≤ M := by
      exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
    have h2 := Nat.le_ceil (2 * (D + 1) / ε)
    rw [div_le_iff₀ hε] at h2
    nlinarith
  have hMτ : D + 1 ≤ c₁ * (τ * M) := by
    have h1 : (⌈(D + 1) / (c₁ * τ)⌉₊ : ℝ) ≤ M := by
      exact_mod_cast (le_max_right _ _).trans (le_max_right _ _)
    have h2 := Nat.le_ceil ((D + 1) / (c₁ * τ))
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith [mul_pos hc₁ hτ]
  set M' : ℕ := ⌈D⌉₊ + d + 1 with hM'
  have hM'd : d + 1 ≤ M' := by omega
  have hM'D : D + 1 ≤ (M' : ℝ) := by
    have := Nat.le_ceil D
    rw [hM']; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨C₀, Wc, hcan⟩ := ThetaZd_cancel d hd ψ cψ hψ C' c (M' : ℝ) hc (by positivity) M
  obtain ⟨Wt, hWt1, ht⟩ := ThetaDecay_theta_series d hd ψ cψ hψ C'
  obtain ⟨CT, hCT⟩ := tsum_periodize_le d M hMd
  obtain ⟨CT', hCT'⟩ := tsum_periodize_le d M' hM'd
  set A : ℝ := |C₀| * 2 ^ M * (|CT| + 1) + |CT'| * 3 ^ M' with hA
  refine ⟨max (max (max Wi Wr) (max Wc Wt)) (max (max (2 ^ D * (4 * A)) (2 ^ (D + 6)))
    (max (max (|C₀| ^ (1 / τ)) (2 ^ (2 / ε))) (2 ^ (1 / c)))), ?_⟩
  intro W L _ hadm hW S hS hSc z hz K hK g hgs hgK hg0 x₀ hx₀
  have hWi : Wi ≤ (W : ℝ) := le_trans (by simp) hW
  have hWr : Wr ≤ (W : ℝ) := le_trans (by simp) hW
  have hWc : Wc ≤ (W : ℝ) := le_trans (by simp) hW
  have hWt : Wt ≤ (W : ℝ) := le_trans (by simp) hW
  have hWA : 2 ^ D * (4 * A) ≤ (W : ℝ) := le_trans (by simp) hW
  have hW64 : (2 : ℝ) ^ (D + 6) ≤ W := le_trans (by simp) hW
  have hWC : |C₀| ^ (1 / τ) ≤ (W : ℝ) := le_trans (by simp) hW
  have hWe : (2 : ℝ) ^ (2 / ε) ≤ W := le_trans (by simp) hW
  have hWcc : (2 : ℝ) ^ (1 / c) ≤ W := le_trans (by simp) hW
  have hW4 : (4 : ℝ) ≤ W := by
    have : (2 : ℝ) ^ (2 : ℝ) ≤ 2 ^ (D + 6) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith)
    norm_num at this
    linarith only [this, hW64]
  have hW1 : (1 : ℝ) ≤ W := by linarith only [hW4]
  have hW0 : (0 : ℝ) < W := by linarith only [hW4]
  obtain ⟨hL1, hWL, hLc, hηL, hηpos, hη1⟩ := ThetaDecay_window hc₀ hε hadm hW1 hz
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  have hs : InfKernel ψ C' W (Sinf ψ W) := ThetaDecay_infKernel_mono (hinf W hWi) hCiC'
  have hSc' := ThetaDecay_symbolClose_mono hSc hCC'
  have ha0 : 0 ≤ ‖msc z‖ ^ 2 := by positivity
  have ha1 := ThetaDecay_sq_lt_one hηpos
  have hgap := ThetaDecay_one_sub_ge hηpos hη1
  set a : ℝ := ‖msc z‖ ^ 2 with ha
  set σ : ℝ := Real.sqrt (1 - a) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by linarith only [ha1])
  have hσ2 : σ ^ 2 = 1 - a := Real.sq_sqrt (by linarith only [ha1])
  obtain ⟨hΘs, -⟩ := ht W hWt (Sinf ψ W) hs a ha0 ha1
  set R : ℝ := W / σ with hR
  have hR0 : 0 < R := by positivity
  have hRL : R / L ≤ 2 * (L : ℝ) ^ (-(ε / 2)) := by
    refine ThetaDecay_R_div_L_le hL1 hW0 hσ0 ?_
    rw [hσ2]
    have := hz.2.1
    linarith only [this, hgap]
  have h2L : 2 * (L : ℝ) ^ (-(ε / 2)) ≤ 1 := ThetaDecay_two_rpow_le_one hε (hWe.trans hWL)
  have hRleL : R ≤ L := by
    have := hRL.trans h2L
    rwa [div_le_one hL0] at this
  have hrpow : (R / L) ^ M ≤ 2 ^ M * (L : ℝ) ^ (-(D + 1)) :=
    ThetaDecay_RL_pow_le hL1 (by positivity) hRL hMε
  -- the geometry of `x₀` and `K`
  set X : ℝ := (zdistInf d L x₀ : ℝ) with hXdef
  have hKr : (W : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith only [hKr, hW0]
  have hKc : (2 : ℝ) ≤ (K : ℝ) ^ c := by
    have h := Real.rpow_le_rpow (by positivity) (hWcc.trans hKr) hc.le
    rwa [← Real.rpow_mul (by norm_num), show 1 / c * c = 1 by field_simp, Real.rpow_one] at h
  have h2K : 2 * (K : ℝ) ≤ X := by
    have e : (K : ℝ) ^ (1 + c) = K * K ^ c := by rw [Real.rpow_add hK0, Real.rpow_one]
    rw [e] at hx₀
    nlinarith only [hx₀, hKc, hK0]
  have hXL : X ≤ (L : ℝ) / 2 := by
    have h := zdistInf_le_half d L x₀
    have : ((L / 2 : ℕ) : ℝ) ≤ (L : ℝ) / 2 := Nat.cast_div_le
    exact (Nat.cast_le.mpr h).trans this
  have hKLn : 2 * K < L := by
    have : (2 * K : ℝ) < L := by linarith only [h2K, hXL, hL0, hK0]
    exact_mod_cast this
  have hXW : (W : ℝ) ≤ X := by linarith only [h2K, hKr]
  have hX0 : 0 < X := by linarith only [hXW, hW0]
  have hX4 : (4 : ℝ) ≤ X := by linarith only [hXW, hW4]
  -- the test function on the box
  set gt : (Fin d → ℤ) → ℝ := fun v => g (zcast L v) with hgt
  set Q : ℝ := ∑ v ∈ boxZ d K, ((zdInf v : ℝ) / X) ^ 2 * |gt v| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun v _ => by positivity
  have hQeq : ∑ x, ((zdistInf d L x : ℝ) / zdistInf d L x₀) ^ 2 * |g x| = Q := by
    rw [ThetaDecay_sum_eq_sum_boxZ hKLn _ (fun y hy => by rw [hgK y hy]; simp)]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [ThetaDecay_zdistInf_zcast hKLn hv]
  have hgt0 : ∑ v ∈ boxZ d K, gt v = 0 := by
    rw [← ThetaDecay_sum_eq_sum_boxZ hKLn g hgK]; exact hg0
  have hgts : ∀ v, gt (-v) = gt v := by
    intro v; simp only [hgt, ThetaDecay_zcast_neg, hgs]
  -- to `ℂ` and the decomposition
  have hcast : ((∑ x, Theta (msc z) S 0 x * g (x - x₀) : ℝ) : ℂ) =
      ∑ x, (Theta (msc z) S 0 x : ℂ) * (g (x - x₀) : ℂ) := by push_cast; rfl
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hcast,
    ThetaDecay_cancel_decomp hKLn (fun y => (Theta (msc z) S 0 y : ℂ)) (ThetaZd a (Sinf ψ W)) hΘs g
      hgK x₀, hQeq]
  refine (norm_add_le _ _).trans ?_
  -- the replacement errors
  have hErr : ‖∑ v ∈ boxZ d K, ((Theta (msc z) S 0 (zcast L (zlift x₀ + v)) : ℂ) -
        periodize L (ThetaZd a (Sinf ψ W)) (zcast L (zlift x₀ + v))) * (gt v : ℂ)‖ ≤
      Q * (2 * X ^ 2 * (X / 2) ^ (-(D + 3))) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ v ∈ boxZ d K, ‖((Theta (msc z) S 0 (zcast L (zlift x₀ + v)) : ℂ) -
        periodize L (ThetaZd a (Sinf ψ W)) (zcast L (zlift x₀ + v))) * (gt v : ℂ)‖ ≤
        (X / 2) ^ (-(D + 3)) * |gt v| := by
      intro v hv
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      refine (hrep W L hadm hWr S hS hSc' (Sinf ψ W) hs z hz _).trans ?_
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith only [hD])
      have h1 : zcast L (zlift x₀ + v) = x₀ + zcast L v := by
        rw [ThetaDecay_zcast_add, ThetaDecay_zcast_zlift]
      have h2 := zdistInf_add_le d L (x₀ + zcast L v) (-zcast L v)
      rw [add_neg_cancel_right, zdistInf_neg, ThetaDecay_zdistInf_zcast hKLn hv] at h2
      have hvK : zdInf v ≤ K := by
        simp only [boxZ, Fintype.mem_piFinset, Finset.mem_Icc] at hv
        refine Finset.sup_le fun i _ => ?_
        obtain ⟨h1, h2⟩ := hv i
        omega
      rw [h1]
      have h3 : X ≤ (zdistInf d L (x₀ + zcast L v) : ℝ) + zdInf v := by
        rw [hXdef]; exact_mod_cast h2
      have h4 : (zdInf v : ℝ) ≤ K := by exact_mod_cast hvK
      linarith only [h3, h4, h2K, hW0]
    calc ∑ v ∈ boxZ d K, ‖((Theta (msc z) S 0 (zcast L (zlift x₀ + v)) : ℂ) -
            periodize L (ThetaZd a (Sinf ψ W)) (zcast L (zlift x₀ + v))) * (gt v : ℂ)‖
        ≤ ∑ v ∈ boxZ d K, (X / 2) ^ (-(D + 3)) * |gt v| := Finset.sum_le_sum hpt
      _ = (X / 2) ^ (-(D + 3)) * ∑ v ∈ boxZ d K, |gt v| := by rw [Finset.mul_sum]
      _ ≤ (X / 2) ^ (-(D + 3)) * (2 * X ^ 2 * Q) := by
          gcongr; exact ThetaDecay_sum_abs_le gt hgt0 hX0
      _ = Q * (2 * X ^ 2 * (X / 2) ^ (-(D + 3))) := by ring
  -- the image sums
  set F : (Fin d → ℤ) → ℂ := fun n => ∑ v ∈ boxZ d K,
    ThetaZd a (Sinf ψ W) (zlift x₀ + (L : ℤ) • n + v) * (gt v : ℂ) with hF
  set brp : (Fin d → ℤ) → ℝ := fun V =>
    |C₀| / ((W : ℝ) ^ 2 * ((zdInf V : ℝ) + W) ^ (d - 2)) / (1 + (zdInf V : ℝ) * σ / W) ^ M +
      (zdInf V : ℝ) ^ (-(M' : ℝ)) with hbrp
  have hcanB : ∀ n, ‖F n‖ ≤ Q * brp (zlift x₀ + (L : ℤ) • n) := by
    intro n
    have hXV : X ≤ zdInf (zlift x₀ + (L : ℤ) • n) := by
      rw [hXdef]; exact_mod_cast ThetaDecay_zdistInf_le_zdInf x₀ n
    have hV0 : 0 < (zdInf (zlift x₀ + (L : ℤ) • n) : ℝ) := by linarith only [hXV, hX0]
    have h := hcan W hWc (Sinf ψ W) hs a ha0 ha1.le K hK gt hgts hgt0
      (zlift x₀ + (L : ℤ) • n) (hx₀.trans hXV)
    refine h.trans ?_
    have hPV : ∑ v ∈ boxZ d K, ((zdInf v : ℝ) / zdInf (zlift x₀ + (L : ℤ) • n)) ^ 2 * |gt v| ≤
        Q := by
      refine Finset.sum_le_sum fun v _ => ?_
      gcongr
    have hbr : C₀ / ((W : ℝ) ^ 2 * ((zdInf (zlift x₀ + (L : ℤ) • n) : ℝ) + W) ^ (d - 2)) /
          (1 + (zdInf (zlift x₀ + (L : ℤ) • n) : ℝ) * Real.sqrt (1 - a) / W) ^ M +
          (zdInf (zlift x₀ + (L : ℤ) • n) : ℝ) ^ (-(M' : ℝ)) ≤
        brp (zlift x₀ + (L : ℤ) • n) := by
      simp only [hbrp]
      gcongr
      exact le_abs_self _
    have hbr0 : 0 ≤ brp (zlift x₀ + (L : ℤ) • n) := by simp only [hbrp]; positivity
    have hP0 : 0 ≤ ∑ v ∈ boxZ d K,
        ((zdInf v : ℝ) / zdInf (zlift x₀ + (L : ℤ) • n)) ^ 2 * |gt v| :=
      Finset.sum_nonneg fun v _ => by positivity
    exact (mul_le_mul_of_nonneg_left hbr hP0).trans (mul_le_mul_of_nonneg_right hPV hbr0)
  have hFs : Summable fun n => ‖F n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_sum_le _ _) ?_
    refine summable_sum fun v _ => ?_
    have hinj : Function.Injective fun n : Fin d → ℤ => zlift x₀ + (L : ℤ) • n + v := by
      intro n₁ n₂ h
      have hL' : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
      funext i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj, add_right_inj] at this
      exact mul_left_cancel₀ hL' this
    simp only [norm_mul]
    exact (hΘs.comp_injective hinj).mul_right _
  set b : {n : Fin d → ℤ // n ≠ 0} → ℝ := fun n => Q *
    (|C₀| * ((1 + (zdInf (zlift x₀ + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹ +
      (3 / (L : ℝ)) ^ M' * ((1 + (zdInf (zlift x₀ + (L : ℤ) • n.1) : ℝ) / L) ^ M')⁻¹) with hb
  have hbs : Summable b :=
    (((ThetaDecay_term_summable M hMd R hR0 x₀).mul_left |C₀|).add
      ((ThetaDecay_term_summable M' hM'd L hL0 x₀).mul_left ((3 / (L : ℝ)) ^ M'))).mul_left Q
  have hFb : ∀ n : {n : Fin d → ℤ // n ≠ 0}, ‖F n.1‖ ≤ b n := by
    intro n
    refine (hcanB n.1).trans ?_
    have hV := ThetaDecay_half_le_zdInf x₀ n.1 n.2
    have hV0 : 0 < (zdInf (zlift x₀ + (L : ℤ) • n.1) : ℝ) := by linarith only [hV, hL0]
    simp only [hb, hbrp]
    set V := zlift x₀ + (L : ℤ) • n.1
    gcongr
    · have e : (zdInf V : ℝ) / R = (zdInf V : ℝ) * σ / W := by rw [hR]; field_simp
      rw [e, ← div_eq_mul_inv]
      have hden : 1 ≤ (W : ℝ) ^ 2 * ((zdInf V : ℝ) + W) ^ (d - 2) :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) (one_le_pow₀ (by linarith only [hV0, hW1]))
      gcongr
      exact div_le_self (abs_nonneg _) hden
    · rw [Real.rpow_neg hV0.le, Real.rpow_natCast]
      have h1 : (1 + (zdInf V : ℝ) / L) ^ M' ≤ (3 / (L : ℝ)) ^ M' * (zdInf V : ℝ) ^ M' := by
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        rw [div_mul_eq_mul_div, le_div_iff₀ hL0, add_mul, div_mul_cancel₀ _ hL0.ne']
        linarith only [hV]
      have h2 : 0 < (1 + (zdInf V : ℝ) / L) ^ M' := by positivity
      have h3 : 0 < (3 / (L : ℝ)) ^ M' := by positivity
      rw [← div_eq_mul_inv, le_div_iff₀ h2]
      calc ((zdInf V : ℝ) ^ M')⁻¹ * (1 + (zdInf V : ℝ) / L) ^ M'
          ≤ ((zdInf V : ℝ) ^ M')⁻¹ * ((3 / (L : ℝ)) ^ M' * (zdInf V : ℝ) ^ M') := by gcongr
        _ = (3 / (L : ℝ)) ^ M' := by field_simp
  have hT := ThetaDecay_norm_tsum_le F hFs b hbs hFb
  have hF0 : ‖F 0‖ ≤ Q * brp (zlift x₀) := by
    have := hcanB 0
    simpa only [smul_zero, add_zero] using this
  have hz0 : (zdInf (zlift x₀) : ℝ) = X := by rw [hXdef, ThetaDecay_zdInf_zlift]
  -- the sum over `n ≠ 0`
  have hbsum : ∑' n, b n ≤ Q * ((|C₀| * |CT| * 2 ^ M + |CT'| * 3 ^ M') * (L : ℝ) ^ (-(D + 1))) := by
    simp only [hb]
    rw [tsum_mul_left]
    gcongr
    rw [(((ThetaDecay_term_summable M hMd R hR0 x₀).mul_left |C₀|)).tsum_add
      (((ThetaDecay_term_summable M' hM'd L hL0 x₀).mul_left ((3 / (L : ℝ)) ^ M'))),
      tsum_mul_left, tsum_mul_left]
    have h1 := hCT L R hR0 hRleL x₀
    have h2 := hCT' L L hL0 le_rfl x₀
    rw [div_self hL0.ne', one_pow, mul_one] at h2
    have h3 : (3 / (L : ℝ)) ^ M' ≤ 3 ^ M' * (L : ℝ) ^ (-(D + 1)) := by
      rw [div_pow]
      rw [div_eq_mul_inv]
      gcongr
      rw [← Real.rpow_natCast, ← Real.rpow_neg hL0.le]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hM'D])
    have hq : 0 ≤ (R / L) ^ M := by positivity
    have h4 : CT * (R / L) ^ M ≤ |CT| * (2 ^ M * (L : ℝ) ^ (-(D + 1))) :=
      (mul_le_mul_of_nonneg_right (le_abs_self CT) hq).trans (by gcongr)
    have h5 : 0 ≤ (3 / (L : ℝ)) ^ M' := by positivity
    have hs1 : 0 ≤ ∑' n : {n : Fin d → ℤ // n ≠ 0},
        ((1 + (zdInf (zlift x₀ + (L : ℤ) • n.1) : ℝ) / L) ^ M')⁻¹ :=
      tsum_nonneg fun n => by positivity
    calc |C₀| * ∑' n : {n : Fin d → ℤ // n ≠ 0},
            ((1 + (zdInf (zlift x₀ + (L : ℤ) • n.1) : ℝ) / R) ^ M)⁻¹ +
          (3 / (L : ℝ)) ^ M' * ∑' n : {n : Fin d → ℤ // n ≠ 0},
            ((1 + (zdInf (zlift x₀ + (L : ℤ) • n.1) : ℝ) / L) ^ M')⁻¹
        ≤ |C₀| * (|CT| * (2 ^ M * (L : ℝ) ^ (-(D + 1)))) +
          3 ^ M' * (L : ℝ) ^ (-(D + 1)) * |CT'| := by
          gcongr
          · exact h1.trans h4
          · exact h2.trans (le_abs_self _)
      _ = (|C₀| * |CT| * 2 ^ M + |CT'| * 3 ^ M') * (L : ℝ) ^ (-(D + 1)) := by ring
  -- the numerics
  have hE := ThetaDecay_err_le hD.le (hW64.trans hXW)
  have hXM : X ^ (-(M' : ℝ)) ≤ X ^ (-D) / 4 := by
    have h1 : X ^ (-(M' : ℝ)) ≤ X ^ (-(D + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hX4]) (by linarith only [hM'D])
    have h2 : X ^ (-(D + 1)) = X ^ (-D) * X⁻¹ := by
      rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hX0, Real.rpow_neg_one]
    have h3 : X⁻¹ ≤ 1 / 4 := by rw [inv_eq_one_div]; gcongr
    have h4 : 0 ≤ X ^ (-D) := by positivity
    rw [h2] at h1
    nlinarith only [h1, h3, h4, mul_le_mul_of_nonneg_left h3 h4]
  have hAbs := ThetaDecay_absorb (A := 4 * A) hL0 (hWA.trans hWL)
  have h2LX : 2 ^ (-D) * (L : ℝ) ^ (-D) ≤ X ^ (-D) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos hX0 (by linarith only [hXL, hL0]) (by linarith only [hD])
  have hAsplit : A * (L : ℝ) ^ (-(D + 1)) = (|C₀| * |CT| * 2 ^ M + |CT'| * 3 ^ M') *
      (L : ℝ) ^ (-(D + 1)) + |C₀| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by rw [hA]; ring
  have hA0 : 0 ≤ |C₀| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by positivity
  have hbrp0 : brp (zlift x₀) = |C₀| / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) /
      (1 + X * σ / W) ^ M + X ^ (-(M' : ℝ)) := by
    simp only [hbrp, hz0]
  -- the bracket
  have hkey : 2 * X ^ 2 * (X / 2) ^ (-(D + 3)) + brp (zlift x₀) +
      (|C₀| * |CT| * 2 ^ M + |CT'| * 3 ^ M') * (L : ℝ) ^ (-(D + 1)) ≤
      (if X ≤ z.im ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + τ) then X ^ τ * bB d L W 0 x₀ else 0) +
        X ^ (-D) := by
    rw [hbrp0]
    have hden1 : 1 ≤ (W : ℝ) ^ 2 * (X + W) ^ (d - 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) (one_le_pow₀ (by linarith only [hX0, hW1]))
    have hAL : A * (L : ℝ) ^ (-(D + 1)) ≤ X ^ (-D) / 4 := by
      have : 4 * A * (L : ℝ) ^ (-(D + 1)) = 4 * (A * (L : ℝ) ^ (-(D + 1))) := by ring
      linarith only [hAbs, h2LX, this]
    have hS1 : (|C₀| * |CT| * 2 ^ M + |CT'| * 3 ^ M') * (L : ℝ) ^ (-(D + 1)) +
        |C₀| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) ≤ X ^ (-D) / 4 := by
      rw [← hAsplit]; exact hAL
    have hXD0 : 0 ≤ X ^ (-D) := by positivity
    split_ifs with hin
    · have hmain : |C₀| / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) / (1 + X * σ / W) ^ M ≤
          X ^ τ * bB d L W 0 x₀ := by
        have hb0 : zdistInf d L (0 - x₀) = zdistInf d L x₀ := by
          rw [zero_sub, zdistInf_neg]
        rw [ThetaDecay_bB_eq (by omega) hW0, hb0, ← hXdef]
        have h1 : 1 ≤ (1 + X * σ / W) ^ M := one_le_pow₀ (by
          have : 0 ≤ X * σ / W := by positivity
          linarith only [this])
        have hC0 : |C₀| ≤ X ^ τ :=
          (ThetaDecay_le_rpow hτ (abs_nonneg _) hWC).trans
            (Real.rpow_le_rpow hW0.le hXW hτ.le)
        calc |C₀| / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) / (1 + X * σ / W) ^ M
            ≤ |C₀| / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) := div_le_self (by positivity) h1
          _ ≤ X ^ τ / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) := by gcongr
          _ = X ^ τ * (1 / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2))) := by ring
      linarith only [hE, hXM, hmain, hS1, hA0, hXD0]
    · have hout : |C₀| / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) / (1 + X * σ / W) ^ M ≤
          |C₀| * 2 ^ M * (L : ℝ) ^ (-(D + 1)) := by
        have hgap' : z.im / 2 ≤ σ ^ 2 := by rw [hσ2]; exact hgap
        have hw := ThetaDecay_outside hηpos hW0 hσ0.le hgap' (not_le.mp hin)
        have hWτ : 0 < (W : ℝ) ^ τ / 2 := by positivity
        have hpow : ((W : ℝ) ^ τ / 2) ^ M ≤ (1 + X * σ / W) ^ M :=
          pow_le_pow_left₀ hWτ.le (le_add_of_nonneg_of_le zero_le_one hw) M
        have hLW : (L : ℝ) ^ (D + 1) ≤ ((W : ℝ) ^ τ) ^ M :=
          ThetaDecay_L_rpow_le_W_rpow_pow hc₁ hτ hL1 hLc hMτ
        have hLp : 0 < (L : ℝ) ^ (D + 1) := by positivity
        have e : (L : ℝ) ^ (-(D + 1)) = ((L : ℝ) ^ (D + 1))⁻¹ := Real.rpow_neg hL0.le _
        rw [e]
        calc |C₀| / ((W : ℝ) ^ 2 * (X + W) ^ (d - 2)) / (1 + X * σ / W) ^ M
            ≤ |C₀| / (1 + X * σ / W) ^ M := by
              gcongr; exact div_le_self (abs_nonneg _) hden1
          _ ≤ |C₀| / ((W : ℝ) ^ τ / 2) ^ M := by gcongr
          _ = |C₀| * 2 ^ M / ((W : ℝ) ^ τ) ^ M := by
              rw [div_pow]; field_simp
          _ ≤ |C₀| * 2 ^ M / (L : ℝ) ^ (D + 1) := by gcongr
          _ = |C₀| * 2 ^ M * ((L : ℝ) ^ (D + 1))⁻¹ := by ring
      linarith only [hE, hXM, hout, hS1, hXD0]
  calc ‖∑ v ∈ boxZ d K, ((Theta (msc z) S 0 (zcast L (zlift x₀ + v)) : ℂ) -
          periodize L (ThetaZd a (Sinf ψ W)) (zcast L (zlift x₀ + v))) * (gt v : ℂ)‖ +
        ‖∑' n, F n‖
      ≤ Q * (2 * X ^ 2 * (X / 2) ^ (-(D + 3))) + (Q * brp (zlift x₀) +
          Q * ((|C₀| * |CT| * 2 ^ M + |CT'| * 3 ^ M') * (L : ℝ) ^ (-(D + 1)))) := by
        gcongr
        exact hT.trans (add_le_add hF0 hbsum)
    _ = Q * (2 * X ^ 2 * (X / 2) ^ (-(D + 3)) + brp (zlift x₀) +
          (|C₀| * |CT| * 2 ^ M + |CT'| * 3 ^ M') * (L : ℝ) ^ (-(D + 1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkey hQ0


section Witness

end Witness

end RBM8D
