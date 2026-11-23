module

public import RBM8D.Kernel.InfSymbol
public import RBM8D.Profile.Poisson

@[expose] public section

/-!
# The infinite-space kernel `S_∞`

[I, (7.3)]: `S_∞ = φ_W/Σφ_W` is an `InfKernel`, by d-dimensional Poisson summation.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d : ℕ}

/-- `φ_W(x) = (2π)^{-d} ∫_{ℝ^d} ψ(Wq) cos(q·x) dq`, the integral of [I, (1.6)] on `ℤ^d`
(for symmetric `ψ` it equals `(2π)^{-d} ∫ ψ(Wq) e^{iq·x} dq`). -/
def phiW (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) (x : Fin d → ℤ) : ℝ :=
  ((2 * Real.pi) ^ d)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin d),
    ψ ((W : ℝ) • q) * Real.cos (∑ i, q i * (x i : ℝ))

/-- `S_∞` of [I, (7.3)]: `(S_∞)_{0x} = lim_L f_{W,L}(x) = φ_W(x) / Σ_{y ∈ ℤ^d} φ_W(y)`. -/
def Sinf (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) (x : Fin d → ℤ) : ℝ :=
  phiW ψ W x / ∑' y, phiW ψ W y

/-! ## `φ_W` as the real part of the integral of [I, (1.6)] -/

private theorem inner_intVec (P : EuclideanSpace ℝ (Fin d)) (x : Fin d → ℤ) :
    (inner ℝ P (intVec x) : ℝ) = ∑ i, P i * (x i : ℝ) := by
  simp [intVec, PiLp.inner_apply, mul_comm]

/-- `φ_W(x) = Re[(2π)^{-d} ∫ ψ(Wq) e^{iq·x} dq]` for `W ≠ 0`. -/
private theorem phiW_eq_re (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) (hW : 1 ≤ W)
    (x : Fin d → ℤ) : phiW ψ W x = (profInt ψ W (intVec x)).re := by
  have hW' : (W : ℝ) ≠ 0 := by positivity
  have hint : Integrable (fun q : EuclideanSpace ℝ (Fin d) =>
      (ψ ((W : ℝ) • q) : ℂ) * cexp (I * (inner ℝ q (intVec x) : ℝ))) := by
    refine (((ψ.integrable (μ := volume)).comp_smul hW').ofReal (𝕜 := ℂ)).mono ?_
      (ae_of_all _ fun q => ?_)
    · exact (Complex.continuous_ofReal.comp (ψ.continuous.comp (continuous_const_smul _))).mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_id.inner continuous_const)))) |>.aestronglyMeasurable
    · rw [norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one]
      rfl
  unfold phiW profInt
  have h3 : ((2 * Real.pi : ℂ) ^ d)⁻¹ = ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h3, Complex.re_ofReal_mul]
  congr 1
  have := integral_re hint
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only
  rw [Complex.re_ofReal_mul, mul_comm I, Complex.exp_ofReal_mul_I_re, inner_intVec]

/-- For symmetric `ψ`, `φ_W(x) = (2π)^{-d} ∫ ψ(Wq) e^{iq·x} dq`. -/
private theorem phiW_eq_profInt (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (hψ : ∀ p, ψ (-p) = ψ p)
    (W : ℕ) (hW : 1 ≤ W) (x : Fin d → ℤ) : (phiW ψ W x : ℂ) = profInt ψ W (intVec x) := by
  rw [phiW_eq_re ψ W hW x]
  exact Complex.ext (by simp) (by simp [profInt_im d ψ hψ W (intVec x)])

/-- `|x|_∞ ≤ ‖x‖₂` on `ℤ^d`. -/
private theorem zdInf_le_norm (x : Fin d → ℤ) : (zdInf x : ℝ) ≤ ‖intVec x‖ := by
  have hi : ∀ i, (((x i).natAbs : ℕ) : ℝ) ≤ ‖intVec x‖ := by
    intro i
    have := PiLp.norm_apply_le (intVec x) i
    simpa [intVec, Nat.cast_natAbs] using this
  have h : zdInf x ≤ ⌊‖intVec x‖⌋₊ :=
    Finset.sup_le fun i _ => Nat.le_floor (hi i)
  exact (Nat.cast_le.mpr h).trans (Nat.floor_le (norm_nonneg _))

/-- `φ_W(x) = W^{-d} φ_1(x/W)` decays: `|φ_W(x)| (1 + |x|/W)^k ≤ C_k W^{-d}` ([I, (1.8)] on
`ℤ^d`), with `C_k` depending on `d`, `ψ`, `k` only. -/
theorem phiW_decay :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (k : ℕ), ∃ C : ℝ, ∀ (W : ℕ), 1 ≤ W →
    ∀ x : Fin d → ℤ, |phiW ψ W x| * (1 + (zdInf x : ℝ) / W) ^ k ≤ C / (W : ℝ) ^ d := by
  intro d ψ k
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin d)) (2 * Real.pi)
      h2pi).toContinuousLinearEquiv
  let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
      (SchwartzMap.postcompCLM (Complex.ofRealCLM) ψ)
  have hg : ∀ y, (𝓕⁻ G) y = profInt ψ 1 y := by
    intro y
    rw [SchwartzMap.fourierInv_coe, profInt_eq_fourierInv d ψ 1 y, mul_one]
    rfl
  refine ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕⁻ G),
    fun W hW x => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set y : EuclideanSpace ℝ (Fin d) := (W : ℝ)⁻¹ • intVec x
  have key := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl
    (𝓕⁻ G) y
  rw [norm_iteratedFDeriv_zero, hg] at key
  have hscale : ‖profInt ψ W (intVec x)‖ = ((W : ℝ) ^ d)⁻¹ * ‖profInt ψ 1 y‖ := by
    rw [profInt_scale d ψ W hW0 (intVec x), norm_mul, norm_inv, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hW0.le]
  have h1 : |phiW ψ W x| ≤ ((W : ℝ) ^ d)⁻¹ * ‖profInt ψ 1 y‖ := by
    rw [phiW_eq_re ψ W hW x, ← hscale]
    exact Complex.abs_re_le_norm _
  have h2 : 1 + (zdInf x : ℝ) / W ≤ 1 + ‖y‖ := by
    have : ‖y‖ = (W : ℝ)⁻¹ * ‖intVec x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW0)]
    rw [this, div_eq_inv_mul]
    gcongr
    exact zdInf_le_norm x
  have hpos : 0 < ((W : ℝ) ^ d) := by positivity
  calc |phiW ψ W x| * (1 + (zdInf x : ℝ) / W) ^ k
      ≤ (((W : ℝ) ^ d)⁻¹ * ‖profInt ψ 1 y‖) * (1 + ‖y‖) ^ k := by
        gcongr
    _ = ((W : ℝ) ^ d)⁻¹ * ((1 + ‖y‖) ^ k * ‖profInt ψ 1 y‖) := by ring
    _ ≤ ((W : ℝ) ^ d)⁻¹ *
        (2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕⁻ G)) := by
        gcongr
    _ = _ := by rw [div_eq_inv_mul]

/-- Poisson summation for `φ_W`: `Σ_x φ_W(x) e^{ip·x} = Σ_{k ∈ ℤ^d} ψ(W(p + 2πk))` for symmetric
`ψ` and `W ≥ 1` (the numerator of `ŝ_∞(p)` in [I, §7.1]). -/
theorem zdSymbol_phiW :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ) (W : ℕ),
    1 ≤ W → ∀ p : Fin d → ℝ,
      zdSymbol (phiW ψ W) p =
        ∑' k : Fin d → ℤ, (ψ ((W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ))) : ℂ) := by
  intro d ψ cψ hψ W hW p
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, h⟩ := poisson_profile d ψ W hW0 (-(WithLp.toLp 2 p))
  have hterm : (fun z : Fin d → ℤ => profInt ψ W (intVec z) *
      cexp (-(I * (inner ℝ (-(WithLp.toLp 2 p)) (intVec z) : ℝ)))) =
      fun z => (phiW ψ W z : ℂ) * zexp p z := by
    funext z
    rw [phiW_eq_profInt ψ hψ.symm W hW z, zexp, inner_neg_left, inner_intVec]
    congr 2
    push_cast
    ring
  rw [hterm] at h
  unfold zdSymbol zdSeries
  rw [h.tsum_eq, ← (Equiv.neg (Fin d → ℤ)).tsum_eq]
  refine tsum_congr fun j => ?_
  congr 1
  rw [← hψ.symm]
  congr 1
  ext i
  simp [intVec]
  ring

/-! ## The aliases `ψ(W(p + 2πk))`, `k ≠ 0` -/

/-- The weight `∏ᵢ (1 + kᵢ²)⁻¹` on `ℤ^d`. -/
private def latWt (k : Fin d → ℤ) : ℝ := ∏ i, (1 + (k i : ℝ) ^ 2)⁻¹

private theorem latWt_nonneg (k : Fin d → ℤ) : 0 ≤ latWt k :=
  Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by positivity)

private theorem summable_inv_one_add_sq_int :
    Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded_eventually
    (Real.summable_one_div_int_pow.mpr one_lt_two) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (by positivity)), one_div]
  exact inv_anti₀ (by positivity) (by linarith)

private theorem summable_latWt : Summable (latWt (d := d)) := by
  set S := ∑' k : ℤ, (1 + (k : ℝ) ^ 2)⁻¹
  refine summable_of_sum_le (c := S ^ d) (fun n => latWt_nonneg _) fun u => ?_
  classical
  calc ∑ n ∈ u, latWt n
      ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n : Fin d → ℤ => n i)), latWt n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => latWt_nonneg _
        rw [Fintype.mem_piFinset]
        exact fun i => Finset.mem_image_of_mem _ hn
    _ = ∏ i : Fin d, ∑ k ∈ u.image (fun n : Fin d → ℤ => n i), (1 + (k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.prod_univ_sum]; rfl
    _ ≤ ∏ i : Fin d, S := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => by positivity)
          fun i _ => ?_
        exact summable_inv_one_add_sq_int.sum_le_tsum _ (fun k _ => by positivity)
    _ = S ^ d := by simp

/-- `|a + 2πm| ≥ π|m|` for `|a| ≤ π` and `m ∈ ℤ`. -/
private theorem pi_mul_abs_le_abs_add (a : ℝ) (ha : |a| ≤ Real.pi) (m : ℤ) :
    Real.pi * |(m : ℝ)| ≤ |a + 2 * Real.pi * m| := by
  rcases eq_or_ne m 0 with hm | hm
  · simp [hm]
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  have h2 : |2 * Real.pi * m| ≤ |a + 2 * Real.pi * m| + |a| := by
    have := abs_sub (a + 2 * Real.pi * m) a
    simpa using this
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two] at h2
  nlinarith [Real.pi_pos]

/-- `‖W(p + 2πk)‖ ≥ Wπ|k_i|` for `p ∈ [-π, π]^d`. -/
private theorem norm_alias_ge (W : ℕ) (p : Fin d → ℝ) (hp : p ∈ cubePi d) (k : Fin d → ℤ)
    (i : Fin d) :
    (W : ℝ) * (Real.pi * |(k i : ℝ)|) ≤
      ‖(W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ))‖ := by
  have hpi : |p i| ≤ Real.pi := abs_le.mpr (Set.mem_univ_pi.mp hp i)
  have h := PiLp.norm_apply_le ((W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ))) i
  refine le_trans ?_ h
  simp only [PiLp.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  gcongr
  exact pi_mul_abs_le_abs_add (p i) hpi (k i)

/-- For `k ≠ 0`, `W ≥ 1` and `p ∈ [-π, π]^d`: `‖W(p + 2πk)‖ ≥ W` and
`‖W(p + 2πk)‖² ≥ 1 + k_i²` for every `i`. -/
private theorem norm_alias_bounds (W : ℕ) (hW : 1 ≤ W) (p : Fin d → ℝ) (hp : p ∈ cubePi d)
    (k : Fin d → ℤ) (hk : k ≠ 0) :
    (W : ℝ) * Real.pi ≤ ‖(W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ))‖ ∧
      ∀ i, 1 + (k i : ℝ) ^ 2 ≤
        ‖(W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ))‖ ^ 2 := by
  set N := ‖(W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ))‖
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hk
  have h1 : (1 : ℝ) ≤ |(k i₀ : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi₀
  have hN : (W : ℝ) * Real.pi ≤ N := by
    have h2 : (W : ℝ) * (Real.pi * |(k i₀ : ℝ)|) ≤ N := norm_alias_ge W p hp k i₀
    have h3 : (W : ℝ) * Real.pi ≤ (W : ℝ) * (Real.pi * |(k i₀ : ℝ)|) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right Real.pi_pos.le h1) (by positivity)
    exact h3.trans h2
  refine ⟨hN, fun i => ?_⟩
  have hi : (W : ℝ) * (Real.pi * |(k i : ℝ)|) ≤ N := norm_alias_ge W p hp k i
  have hpi := Real.two_le_pi
  have hNi : Real.pi * |(k i : ℝ)| ≤ N :=
    le_trans (le_mul_of_one_le_left (by positivity) hW1) hi
  have hNp : Real.pi ≤ N := le_trans (le_mul_of_one_le_left Real.pi_pos.le hW1) hN
  have a1 : (Real.pi * |(k i : ℝ)|) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by positivity) hNi 2
  have a2 : Real.pi ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hNp 2
  have a3 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have a4 : 4 * |(k i : ℝ)| ^ 2 ≤ Real.pi ^ 2 * |(k i : ℝ)| ^ 2 :=
    mul_le_mul_of_nonneg_right a3 (sq_nonneg _)
  rw [← sq_abs (k i : ℝ)]
  nlinarith

/-- `|ψ(W(p + 2πk))| ≤ S_{D+2d}(ψ) W^{-D} ∏ᵢ (1 + kᵢ²)⁻¹` for `k ≠ 0`, `W ≥ 1`,
`p ∈ [-π, π]^d`, with `S_M(ψ) = sup_v ‖v‖^M |ψ(v)|`. -/
private theorem abs_alias_le (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (D W : ℕ) (hW : 1 ≤ W)
    (p : Fin d → ℝ) (hp : p ∈ cubePi d) (k : Fin d → ℤ) (hk : k ≠ 0) :
    |ψ ((W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ)))| ≤
      SchwartzMap.seminorm ℝ (D + 2 * d) 0 ψ / (W : ℝ) ^ D * latWt k := by
  set v := (W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ))
  set S := SchwartzMap.seminorm ℝ (D + 2 * d) 0 ψ
  obtain ⟨hN, hNi⟩ := norm_alias_bounds W hW p hp k hk
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hs := SchwartzMap.norm_pow_mul_le_seminorm ℝ ψ (D + 2 * d) v
  rw [Real.norm_eq_abs] at hs
  set P := ∏ i, (1 + (k i : ℝ) ^ 2)
  have hP : 0 < P := Finset.prod_pos fun i _ => by positivity
  have hWv : (W : ℝ) ≤ ‖v‖ := by nlinarith [Real.two_le_pi]
  have hlow : (W : ℝ) ^ D * P ≤ ‖v‖ ^ (D + 2 * d) := by
    rw [pow_add, pow_mul]
    have : P ≤ (‖v‖ ^ 2) ^ d :=
      (Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => hNi i).trans_eq
        (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])
    gcongr
  have hWD : 0 < (W : ℝ) ^ D * P := by positivity
  have hlatWt : latWt k = P⁻¹ := by
    simp only [latWt, P, Finset.prod_inv_distrib]
  rw [hlatWt, ← div_eq_mul_inv, div_div, le_div_iff₀ hWD]
  calc |ψ v| * ((W : ℝ) ^ D * P) ≤ |ψ v| * ‖v‖ ^ (D + 2 * d) := by gcongr
    _ = ‖v‖ ^ (D + 2 * d) * |ψ v| := mul_comm _ _
    _ ≤ S := hs

/-- `|Σ_k ψ(W(p + 2πk)) − ψ(Wp)| ≤ A_D W^{-D}` on `[-π, π]^d` for `W ≥ 1`, with
`A_D = S_{D+2d}(ψ) Σ_k ∏ᵢ (1 + kᵢ²)⁻¹`; the series is summable. -/
private theorem alias_sum_le (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (D W : ℕ) (hW : 1 ≤ W)
    (p : Fin d → ℝ) (hp : p ∈ cubePi d) :
    |(∑' k : Fin d → ℤ, ψ ((W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ)))) -
        ψ ((W : ℝ) • WithLp.toLp 2 p)| ≤
      SchwartzMap.seminorm ℝ (D + 2 * d) 0 ψ * (∑' k : Fin d → ℤ, latWt k) / (W : ℝ) ^ D := by
  classical
  set f : (Fin d → ℤ) → ℝ :=
    fun k => ψ ((W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ)))
  set c := SchwartzMap.seminorm ℝ (D + 2 * d) 0 ψ / (W : ℝ) ^ D
  have hc : 0 ≤ c := by positivity
  have hg : HasSum (fun k => c * latWt k) (c * ∑' k : Fin d → ℤ, latWt k) :=
    summable_latWt.hasSum.mul_left c
  have hf : Summable f := by
    refine Summable.of_norm_bounded_eventually hg.summable ?_
    filter_upwards [(Set.finite_singleton (0 : Fin d → ℤ)).compl_mem_cofinite] with k hk
    rw [Real.norm_eq_abs]
    exact abs_alias_le ψ D W hW p hp k hk
  have hf0 : f 0 = ψ ((W : ℝ) • WithLp.toLp 2 p) := by
    have h0 : (fun i => (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = 0 := by funext i; simp
    simp only [f, h0, smul_zero, add_zero]
  change |(∑' k, f k) - _| ≤ _
  rw [hf.tsum_eq_add_tsum_ite 0, hf0, add_sub_cancel_left]
  have := tsum_of_norm_bounded (f := fun k => if k = 0 then 0 else f k) hg fun k => by
    split_ifs with hk
    · simpa using mul_nonneg hc (latWt_nonneg k)
    · rw [Real.norm_eq_abs]; exact abs_alias_le ψ D W hW p hp k hk
  rw [Real.norm_eq_abs] at this
  calc _ ≤ c * ∑' k : Fin d → ℤ, latWt k := this
    _ = _ := by simp only [c]; ring

private theorem zero_mem_cubePi : (0 : Fin d → ℝ) ∈ cubePi d :=
  Set.mem_univ_pi.mpr fun i => ⟨by simp [Real.pi_pos.le], by simp [Real.pi_pos.le]⟩

/-- `Σ_x φ_W(x) e^{ip·x}` as the real series `Σ_k ψ(W(p + 2πk))`. -/
private theorem zdSymbol_phiW_real (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (W : ℕ) (hW : 1 ≤ W) (p : Fin d → ℝ) :
    zdSymbol (phiW ψ W) p =
      ((∑' k : Fin d → ℤ, ψ ((W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ))) :
        ℝ) : ℂ) := by
  rw [zdSymbol_phiW d ψ cψ hψ W hW p, Complex.ofReal_tsum]

/-- `Σ_x φ_W(x) = Σ_k ψ(2πWk)`. -/
private theorem tsum_phiW_eq (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (W : ℕ) (hW : 1 ≤ W) :
    ∑' x, phiW ψ W x =
      ∑' k : Fin d → ℤ, ψ ((W : ℝ) • WithLp.toLp 2 ((0 : Fin d → ℝ) +
        (2 * Real.pi) • fun i => (k i : ℝ))) := by
  have h := zdSymbol_phiW_real ψ cψ hψ W hW 0
  have h0 : zdSymbol (phiW ψ W) 0 = ((∑' x, phiW ψ W x : ℝ) : ℂ) := by
    unfold zdSymbol zdSeries
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun x => ?_
    simp [zexp]
  rw [h0] at h
  exact_mod_cast h

/-- `|Σ_x φ_W(x) − 1| ≤ A_D W^{-D}` for `W ≥ 1`, with `A_D` as in the alias bound. -/
private theorem abs_tsum_phiW_sub_le (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (D W : ℕ) (hW : 1 ≤ W) :
    |∑' x, phiW ψ W x - 1| ≤
      SchwartzMap.seminorm ℝ (D + 2 * d) 0 ψ * (∑' k : Fin d → ℤ, latWt k) / (W : ℝ) ^ D := by
  have h := alias_sum_le ψ D W hW 0 zero_mem_cubePi
  rw [tsum_phiW_eq ψ cψ hψ W hW]
  simpa [hψ.at_zero] using h

/-- `Z_{W,∞} = Σ_x φ_W(x) = 1 + O(W^{-D})` ([I, (1.10)] on `ℤ^d`), uniformly in `W ≥ 1`. -/
theorem tsum_phiW :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ) (D : ℕ),
    ∃ C : ℝ, ∀ (W : ℕ), 1 ≤ W → |∑' x, phiW ψ W x - 1| ≤ C / (W : ℝ) ^ D := by
  intro d ψ cψ hψ D
  exact ⟨SchwartzMap.seminorm ℝ (D + 2 * d) 0 ψ * (∑' k : Fin d → ℤ, latWt k),
    fun W hW => abs_tsum_phiW_sub_le ψ cψ hψ D W hW⟩

/-! ## `S_∞` is an `InfKernel` -/

/-- The constants `C_n = max(2 C_n^{dec}, 2 (1 + ‖ψ‖_∞) A_n)`, with `C_n^{dec}` from the decay of
`φ_W` and `A_n` from the alias bound. -/
private def SinfC (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (n : ℕ) : ℝ :=
  max (2 * (phiW_decay d ψ n).choose)
    (2 * (1 + SchwartzMap.seminorm ℝ 0 0 ψ) *
      (SchwartzMap.seminorm ℝ (n + 2 * d) 0 ψ * ∑' k : Fin d → ℤ, latWt k))

private theorem phiW_neg (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) (x : Fin d → ℤ) :
    phiW ψ W (-x) = phiW ψ W x := by
  unfold phiW
  congr 1
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, Real.cos_neg]

/-- `S_∞ = φ_W/Σφ_W` is an `InfKernel` with the constants `SinfC ψ` at every `W ≥ 1` with
`Σ_x φ_W(x) ≥ 1/2`. -/
private theorem Sinf_infKernel_of (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (W : ℕ) (hW : 1 ≤ W) (hZ : 1 / 2 ≤ ∑' x, phiW ψ W x) :
    InfKernel ψ (SinfC ψ) W (Sinf ψ W) := by
  set Z := ∑' y, phiW ψ W y with hZdef
  have hZ0 : 0 < Z := by linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  refine ⟨fun x => ?_, ?_, fun k x => ?_, fun D' p hp => ?_⟩
  · simp only [Sinf, phiW_neg]
  · unfold Sinf
    rw [tsum_div_const, ← hZdef, div_self hZ0.ne']
  · have hd := (phiW_decay d ψ k).choose_spec W hW x
    have h2 : |Sinf ψ W x| ≤ 2 * |phiW ψ W x| := by
      rw [Sinf, ← hZdef, abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
      nlinarith [abs_nonneg (phiW ψ W x)]
    have hpow : 0 < (W : ℝ) ^ d := by positivity
    calc |Sinf ψ W x| * (1 + (zdInf x : ℝ) / W) ^ k
        ≤ 2 * |phiW ψ W x| * (1 + (zdInf x : ℝ) / W) ^ k := by gcongr
      _ = 2 * (|phiW ψ W x| * (1 + (zdInf x : ℝ) / W) ^ k) := by ring
      _ ≤ 2 * ((phiW_decay d ψ k).choose / (W : ℝ) ^ d) := by gcongr
      _ = 2 * (phiW_decay d ψ k).choose / (W : ℝ) ^ d := by ring
      _ ≤ SinfC ψ k / (W : ℝ) ^ d := by
        gcongr
        exact le_max_left _ _
  · set T := ∑' k : Fin d → ℤ,
      ψ ((W : ℝ) • WithLp.toLp 2 (p + (2 * Real.pi) • fun i => (k i : ℝ)))
    set a := ψ ((W : ℝ) • WithLp.toLp 2 p)
    set B := SchwartzMap.seminorm ℝ 0 0 ψ
    set A := SchwartzMap.seminorm ℝ (D' + 2 * d) 0 ψ * (∑' k : Fin d → ℤ, latWt k)
    have hS : zdSymbol (Sinf ψ W) p = zdSymbol (phiW ψ W) p / (Z : ℂ) := by
      unfold zdSymbol zdSeries Sinf
      rw [← tsum_div_const]
      refine tsum_congr fun x => ?_
      rw [← hZdef]
      push_cast
      ring
    rw [hS, zdSymbol_phiW_real ψ cψ hψ W hW p, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have hA : 0 ≤ A := mul_nonneg (apply_nonneg _ _) (tsum_nonneg latWt_nonneg)
    have hB : 0 ≤ B := apply_nonneg _ _
    set e := A / (W : ℝ) ^ D'
    have he : 0 ≤ e := by positivity
    have h1 : |T - a| ≤ e := alias_sum_le ψ D' W hW p hp
    have h2 : |Z - 1| ≤ e := abs_tsum_phiW_sub_le ψ cψ hψ D' W hW
    have h3 : |a| ≤ B := by
      have := SchwartzMap.norm_le_seminorm ℝ ψ ((W : ℝ) • WithLp.toLp 2 p)
      rwa [Real.norm_eq_abs] at this
    have key : |T / Z - a| ≤ 2 * ((1 + B) * e) := by
      have heq : T / Z - a = ((T - a) - (Z - 1) * a) / Z := by
        field_simp
        ring
      rw [heq, abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
      have hBe : 0 ≤ (1 + B) * e := by positivity
      calc |(T - a) - (Z - 1) * a| ≤ |T - a| + |Z - 1| * |a| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ e + e * B := by gcongr
        _ ≤ 2 * ((1 + B) * e) * Z := by
            nlinarith [mul_nonneg hBe (by linarith : (0 : ℝ) ≤ 2 * Z - 1)]
    calc |T / Z - a| ≤ 2 * ((1 + B) * e) := key
      _ = 2 * (1 + B) * A / (W : ℝ) ^ D' := by simp only [e]; ring
      _ ≤ SinfC ψ D' / (W : ℝ) ^ D' := by
        gcongr
        exact le_max_right _ _

/-- `S_∞ = φ_W/Σφ_W` of [I, (7.3)] is an `InfKernel ψ C W` (symmetric, sum one, the decay
[I, (1.8)] and the symbol closeness `|ŝ_∞(p) − ψ(Wp)| ≤ C_{D′} W^{-D′}` on `[-π, π]^d`) for all
`W ≥ W₀`, with `C` and `W₀` depending on `d`, `ψ`, `c_ψ` only. -/
theorem Sinf_infKernel :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ),
    ∃ (C : ℕ → ℝ) (W₀ : ℝ), ∀ W : ℕ, W₀ ≤ W → InfKernel ψ C W (Sinf ψ W) := by
  intro d ψ cψ hψ
  set A₁ := SchwartzMap.seminorm ℝ (1 + 2 * d) 0 ψ * (∑' k : Fin d → ℤ, latWt k)
  refine ⟨SinfC ψ, max 1 (2 * A₁), fun W hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hWA : 2 * A₁ ≤ W := le_trans (le_max_right _ _) hW
  have hW' : 1 ≤ W := by exact_mod_cast hW1
  refine Sinf_infKernel_of ψ cψ hψ W hW' ?_
  have h := abs_tsum_phiW_sub_le ψ cψ hψ 1 W hW'
  rw [pow_one] at h
  have hW0 : (0 : ℝ) < W := by linarith
  have : A₁ / W ≤ 1 / 2 := by rw [div_le_iff₀ hW0]; linarith
  have := (abs_le.mp (h.trans this)).1
  linarith

section Witness

end Witness

end RBM8D
