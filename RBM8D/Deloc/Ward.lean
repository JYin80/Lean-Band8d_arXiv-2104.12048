import RBM8D.Deloc.Defs

/-!
# The estimate (8.2) of [I, §8] in deterministic form

For a Hermitian matrix with an orthonormal eigenbasis: the spectral form of the resolvent, the
bulk energy average, and the bound on the number of bulk indices of `𝒜_{δ,ℓ̃}` by the near-diagonal
resolvent sums.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Complex Matrix
open scoped ENNReal

namespace RBM8D

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {u : ι → ι → ℂ}
  {lam : ι → ℝ}

/-- `(λ_α − z) Σ_y conj(u_α(y)) G_yx(z) = conj(u_α(x))`. -/
private theorem coeff_green (hH : H.IsHermitian) (hu : IsOrthoEigenbasis H u lam) {z : ℂ}
    (hz : z.im ≠ 0) (α x : ι) :
    ((lam α : ℂ) - z) * ∑ y, star (u α y) * green H z y x = star (u α x) := by
  have hrow : star (u α) ᵥ* H = (lam α : ℂ) • star (u α) := by
    have h := congrArg star (hu.2 α)
    rw [Matrix.star_mulVec, hH.eq, star_smul] at h
    rw [h]
    simp
  have hsub : star (u α) ᵥ* (H - z • (1 : Matrix ι ι ℂ)) = ((lam α : ℂ) - z) • star (u α) := by
    rw [Matrix.vecMul_sub, hrow, Matrix.vecMul_smul, Matrix.vecMul_one, sub_smul]
  have key : star (u α) ᵥ* (H - z • (1 : Matrix ι ι ℂ)) ᵥ* green H z = star (u α) := by
    rw [Matrix.vecMul_vecMul, sub_mul_green hH hz, Matrix.vecMul_one]
  rw [hsub, Matrix.smul_vecMul] at key
  have h := congrFun key x
  simpa [Matrix.vecMul, dotProduct] using h

/-- Completeness of an orthonormal eigenbasis: `Σ_α u_α(y) conj(u_α(w)) = δ_yw`. -/
private theorem sum_mul_star (hu : IsOrthoEigenbasis H u lam) (y w : ι) :
    ∑ α, u α y * star (u α w) = if y = w then 1 else 0 := by
  set V : Matrix ι ι ℂ := Matrix.of fun y α => u α y with hV
  have h1 : Vᴴ * V = 1 := by
    ext α β
    simp only [V, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    exact hu.1 α β
  have h2 : V * Vᴴ = 1 := mul_eq_one_comm.mp h1
  have h := congrFun (congrFun h2 y) w
  simpa [V, Matrix.mul_apply, Matrix.one_apply] using h

/-- `λ_α − z ≠ 0` off the real axis. -/
private theorem sub_ne_zero_of_im (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) : (r : ℂ) - z ≠ 0 := by
  intro h
  apply hz
  have := congrArg Complex.im h
  simpa using this.symm

/-- Spectral form of a column of the resolvent:
`G_yx(z) = Σ_α conj(u_α(x)) / (λ_α − z) · u_α(y)`. -/
private theorem green_col (hH : H.IsHermitian) (hu : IsOrthoEigenbasis H u lam) {z : ℂ}
    (hz : z.im ≠ 0) (x y : ι) :
    green H z y x = ∑ α, star (u α x) / ((lam α : ℂ) - z) * u α y := by
  have hc : ∀ α, star (u α x) / ((lam α : ℂ) - z) = ∑ w, star (u α w) * green H z w x := by
    intro α
    rw [div_eq_iff (sub_ne_zero_of_im (lam α) hz), mul_comm, coeff_green hH hu hz α x]
  simp_rw [hc]
  calc green H z y x = ∑ w, (if y = w then 1 else 0) * green H z w x := by simp
    _ = ∑ w, (∑ α, u α y * star (u α w)) * green H z w x := by simp_rw [sum_mul_star hu]
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun w _ => by ring

/-- `Σ_x |u_α(x)|² = 1`. -/
private theorem sum_norm_sq_eq_one (hu : IsOrthoEigenbasis H u lam) (α : ι) :
    ∑ x, ‖u α x‖ ^ 2 = 1 := by
  have h := hu.1 α α
  simp only [↓reduceIte] at h
  have hc : ((∑ x, ‖u α x‖ ^ 2 : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast hc

/-- The eigenvectors as vectors of `ℓ²` form an orthonormal family. -/
private theorem orthonormal_toLp (hu : IsOrthoEigenbasis H u lam) :
    Orthonormal ℂ (fun α => WithLp.toLp 2 (u α) : ι → EuclideanSpace ℂ ι) := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [EuclideanSpace.inner_toLp_toLp, ← hu.1 α β]
  simp only [dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

omit [DecidableEq ι] in
/-- `‖Σ_{α ∈ s} c_α e_α‖² = Σ_{α ∈ s} |c_α|²` for an orthonormal family `e`. -/
private theorem norm_sq_sum_orthonormal {v : ι → EuclideanSpace ℂ ι} (hon : Orthonormal ℂ v)
    (c : ι → ℂ) (s : Finset ι) : ‖∑ α ∈ s, c α • v α‖ ^ 2 = ∑ α ∈ s, ‖c α‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hon.inner_sum]
  simp only [RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Complex.conj_mul']
  norm_cast

/-- Restriction of a vector to a set `F` (the indicator of `F` as an operator). -/
private def restrictTo (F : Finset ι) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun v := WithLp.toLp 2 (fun y => if y ∈ F then v y else 0)
  map_add' v w := by
    ext y
    by_cases h : y ∈ F <;> simp [h]
  map_smul' c v := by
    ext y
    by_cases h : y ∈ F <;> simp [h]

private theorem norm_sq_restrictTo (F : Finset ι) (v : EuclideanSpace ℂ ι) :
    ‖restrictTo F v‖ ^ 2 = ∑ y ∈ F, ‖v y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [restrictTo, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ F)]
  have h1 : ∑ y ∈ Finset.univ.filter (· ∈ F), ‖(if y ∈ F then v y else 0)‖ ^ 2 =
      ∑ y ∈ F, ‖v y‖ ^ 2 := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.sum_congr rfl fun y hy => by simp [hy]
  have h2 : ∑ y ∈ Finset.univ.filter (fun y => ¬ y ∈ F), ‖(if y ∈ F then v y else 0)‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun y hy => by simp [(Finset.mem_filter.mp hy).2]
  rw [h1, h2, add_zero]

private theorem norm_restrictTo_le (F : Finset ι) (v : EuclideanSpace ℂ ι) :
    ‖restrictTo F v‖ ≤ ‖v‖ := by
  have h : ‖restrictTo F v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_sq_restrictTo, EuclideanSpace.norm_sq_eq]
    exact Finset.sum_le_univ_sum_of_nonneg fun y => by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The pointwise estimate at one `x` and one `z = E + iη`: with `F` the far set and `A` any set
of indices, if `Im G_xx ≤ 2` and `η Σ_{y ∉ F} |G_yx|² ≤ Φ`, then
`η Σ_{α ∈ A} |u_α(x)|² / |λ_α − z|² ≤ Φ + 3 √(2η) Σ_{α ∈ A} |u_α(x)| ‖1_F u_α‖ / |λ_α − z|`. -/
private theorem pointwise (hH : H.IsHermitian) (hu : IsOrthoEigenbasis H u lam) {z : ℂ}
    (hz : 0 < z.im) (x : ι) (A F : Finset ι) (Φ : ℝ) (him : (green H z x x).im ≤ 2)
    (hnear : z.im * ∑ y ∈ Fᶜ, ‖green H z y x‖ ^ 2 ≤ Φ) :
    z.im * ∑ α ∈ A, ‖u α x‖ ^ 2 / ‖(lam α : ℂ) - z‖ ^ 2 ≤
      Φ + 3 * Real.sqrt (2 * z.im) *
        ∑ α ∈ A, ‖u α x‖ * Real.sqrt (∑ y ∈ F, ‖u α y‖ ^ 2) / ‖(lam α : ℂ) - z‖ := by
  set η := z.im with hη
  set e : ι → EuclideanSpace ℂ ι := fun α => WithLp.toLp 2 (u α) with he
  have hon : Orthonormal ℂ e := orthonormal_toLp hu
  set c : ι → ℂ := fun α => star (u α x) / ((lam α : ℂ) - z) with hc
  have hcn : ∀ α, ‖c α‖ = ‖u α x‖ / ‖(lam α : ℂ) - z‖ := by
    intro α
    simp [c]
  set g : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun y => green H z y x) with hgdef
  have hgsum : g = ∑ α, c α • e α := by
    ext y
    simp [g, e, c, green_col hH hu hz.ne' x y, WithLp.ofLp_sum]
  set a : EuclideanSpace ℂ ι := ∑ α ∈ Aᶜ, c α • e α with ha
  set b : EuclideanSpace ℂ ι := ∑ α ∈ A, c α • e α with hb
  have hgab : g = a + b := by
    rw [hgsum, ha, hb, add_comm, Finset.sum_add_sum_compl]
  -- squared norms
  have hS : ‖g‖ ^ 2 = (green H z x x).im / η := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [g] using sum_norm_sq_green_col hH hz x
  have hg2 : ‖g‖ ^ 2 = ∑ α, ‖c α‖ ^ 2 := by rw [hgsum, norm_sq_sum_orthonormal hon]
  have ha2 : ‖a‖ ^ 2 = ∑ α ∈ Aᶜ, ‖c α‖ ^ 2 := norm_sq_sum_orthonormal hon c _
  have hb2 : ‖b‖ ^ 2 = ∑ α ∈ A, ‖c α‖ ^ 2 := norm_sq_sum_orthonormal hon c _
  have hsplit2 : ‖g‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [hg2, ha2, hb2, add_comm, Finset.sum_add_sum_compl]
  -- the far part
  set P := restrictTo F with hP
  have hPg2 : ‖P g‖ ^ 2 = ∑ y ∈ F, ‖green H z y x‖ ^ 2 := by
    rw [norm_sq_restrictTo]
  have hfar : ‖g‖ ^ 2 = ‖P g‖ ^ 2 + ∑ y ∈ Fᶜ, ‖green H z y x‖ ^ 2 := by
    rw [hPg2, Finset.sum_add_sum_compl, EuclideanSpace.norm_sq_eq]
  set T : ℝ := ∑ α ∈ A, ‖c α‖ * ‖P (e α)‖ with hT
  have hPb : ‖P b‖ ≤ T := by
    rw [hb, map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_smul, norm_smul]
  have hTeq : T = ∑ α ∈ A, ‖u α x‖ * Real.sqrt (∑ y ∈ F, ‖u α y‖ ^ 2) / ‖(lam α : ℂ) - z‖ := by
    refine Finset.sum_congr rfl fun α _ => ?_
    have hPe : ‖P (e α)‖ = Real.sqrt (∑ y ∈ F, ‖u α y‖ ^ 2) := by
      rw [← norm_sq_restrictTo F (e α), Real.sqrt_sq (norm_nonneg _)]
    rw [hcn, hPe]
    ring
  have hlhs : ∑ α ∈ A, ‖u α x‖ ^ 2 / ‖(lam α : ℂ) - z‖ ^ 2 = ‖b‖ ^ 2 := by
    rw [hb2]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hcn, div_pow]
  rw [hlhs, ← hTeq]
  -- real inequalities
  have hη0 : 0 < η := hz
  have hna : ‖a‖ ≤ ‖g‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [hsplit2]
    nlinarith [sq_nonneg ‖b‖]
  have hnb : ‖b‖ ≤ ‖g‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [hsplit2]
    nlinarith [sq_nonneg ‖a‖]
  have hPb' : ‖P b‖ ≤ ‖g‖ := (norm_restrictTo_le F b).trans hnb
  have hPg : ‖P g‖ ≤ ‖a‖ + ‖P b‖ := by
    rw [hgab, map_add]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_restrictTo_le F a)
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hPb
  have hImG : η * ‖g‖ ^ 2 = (green H z x x).im := by
    rw [hS]
    field_simp
  have hηg : η * ‖g‖ ≤ Real.sqrt (2 * η) := by
    apply Real.le_sqrt_of_sq_le
    have : (η * ‖g‖) ^ 2 = η * (η * ‖g‖ ^ 2) := by ring
    rw [this, hImG]
    nlinarith
  have hPg2' : ‖P g‖ ^ 2 ≤ ‖a‖ ^ 2 + 3 * ‖g‖ * T := by
    have h1 : ‖P g‖ ^ 2 ≤ (‖a‖ + ‖P b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hPg 2
    have h2 : ‖a‖ * ‖P b‖ ≤ ‖g‖ * T := mul_le_mul hna hPb (norm_nonneg _) (norm_nonneg _)
    have h3 : ‖P b‖ * ‖P b‖ ≤ ‖g‖ * T := mul_le_mul hPb' hPb (norm_nonneg _) (norm_nonneg _)
    nlinarith
  have hfinal : η * ‖b‖ ^ 2 ≤ Φ + 3 * (η * ‖g‖) * T := by
    have e1 : η * ‖b‖ ^ 2 = η * ‖P g‖ ^ 2 + η * ∑ y ∈ Fᶜ, ‖green H z y x‖ ^ 2 - η * ‖a‖ ^ 2 := by
      rw [← mul_add, ← hfar, hsplit2]
      ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hPg2' hη0.le
    linarith
  calc η * ‖b‖ ^ 2 ≤ Φ + 3 * (η * ‖g‖) * T := hfinal
    _ ≤ Φ + 3 * Real.sqrt (2 * η) * T := by gcongr

end Spectral

/-! ## The energy integrals -/

/-- `∫_a^b η / ((λ − E)² + η²) dE = arctan((b − λ)/η) − arctan((a − λ)/η)`. -/
private theorem integral_lorentz (lam η a b : ℝ) (hη : 0 < η) :
    ∫ E in a..b, η / ((lam - E) ^ 2 + η ^ 2) =
      Real.arctan ((b - lam) / η) - Real.arctan ((a - lam) / η) := by
  have hpos : ∀ E : ℝ, 0 < (lam - E) ^ 2 + η ^ 2 := fun E => by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun E => Real.arctan ((E - lam) / η))]
  · intro E _
    have h := (((hasDerivAt_id E).sub_const lam).div_const η).arctan
    simp only [id_eq] at h
    convert h using 1
    have hE := hpos E
    field_simp
    ring
  · exact (continuous_const.div (by fun_prop) fun E => (hpos E).ne').intervalIntegrable _ _

/-- The bulk weight: for `λ ∈ (a, b)` with `b − a ≥ 2η`,
`arctan((b − λ)/η) − arctan((a − λ)/η) ≥ π/4`. -/
private theorem quarter_le_arctan_sub (lam η a b : ℝ) (hη : 0 < η) (ha : a < lam) (hb : lam < b)
    (hab : 2 * η ≤ b - a) :
    Real.pi / 4 ≤ Real.arctan ((b - lam) / η) - Real.arctan ((a - lam) / η) := by
  have h1 : 0 < (b - lam) / η := div_pos (by linarith) hη
  have h2 : (a - lam) / η < 0 := div_neg_of_neg_of_pos (by linarith) hη
  have hp : 0 < Real.arctan ((b - lam) / η) := by
    rw [← Real.arctan_zero]; exact Real.arctan_strictMono h1
  have hn : Real.arctan ((a - lam) / η) < 0 := by
    rw [← Real.arctan_zero]; exact Real.arctan_strictMono h2
  rcases le_total 1 ((b - lam) / η) with h | h
  · have : Real.pi / 4 ≤ Real.arctan ((b - lam) / η) := by
      rw [← Real.arctan_one]; exact Real.arctan_strictMono.monotone h
    linarith
  · have h' : (a - lam) / η ≤ -1 := by
      rw [div_le_iff₀ hη] at h ⊢
      linarith
    have : Real.arctan ((a - lam) / η) ≤ -(Real.pi / 4) := by
      rw [← Real.arctan_one, ← Real.arctan_neg]; exact Real.arctan_strictMono.monotone h'
    linarith

private theorem arctan_sub_le_pi (p q : ℝ) : Real.arctan p - Real.arctan q ≤ Real.pi := by
  linarith [Real.arctan_lt_pi_div_two p, Real.neg_pi_div_two_lt_arctan q]

/-- `3 √(2η) δ / r ≤ (3√2 δ/√π) η/r² + 3√2 δ √π / 4` for `r > 0`, `δ ≥ 0`. -/
private theorem amgm_cross (η δ r : ℝ) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (hr : 0 < r) :
    3 * Real.sqrt (2 * η) * δ / r ≤
      3 * Real.sqrt 2 * δ / Real.sqrt Real.pi * (η / r ^ 2) +
        3 * Real.sqrt 2 * δ * Real.sqrt Real.pi / 4 := by
  set σ := Real.sqrt Real.pi with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr Real.pi_pos
  set t := Real.sqrt η / r with ht
  have ht2 : η / r ^ 2 = t ^ 2 := by rw [ht, div_pow, Real.sq_sqrt hη]
  have hkey : t ≤ t ^ 2 / σ + σ / 4 := by
    have : t ^ 2 / σ + σ / 4 - t = (t - σ / 2) ^ 2 / σ := by field_simp; ring
    have : 0 ≤ (t - σ / 2) ^ 2 / σ := by positivity
    linarith
  have hc : 0 ≤ 3 * Real.sqrt 2 * δ := by positivity
  have hl : 3 * Real.sqrt (2 * η) * δ / r = 3 * Real.sqrt 2 * δ * t := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ht]
    ring
  rw [hl, ht2]
  calc 3 * Real.sqrt 2 * δ * t ≤ 3 * Real.sqrt 2 * δ * (t ^ 2 / σ + σ / 4) :=
        mul_le_mul_of_nonneg_left hkey hc
    _ = _ := by ring

/-- (8.2) in deterministic form: for `H` Hermitian with an orthonormal eigenbasis `(u, λ)`,
`0 < κ`, `0 < η ≤ 2 − κ`, `δ ≥ 0`, if for every `x` and every `E ∈ (−2+κ, 2−κ)`
at `z = E + iη`, `Im G_xx(z) ≤ 2` and `η Σ_{‖y − x‖_L < ℓ̃} |G_yx(z)|² ≤ Φ`, then
`(π/4 − 6√(2π) δ) |𝒜_{δ,ℓ̃}| ≤ (4 − 2κ) N Φ`. -/
theorem eq82Det :
  ∀ (d L : ℕ) [NeZero L] (H : Matrix (Zd d L) (Zd d L) ℂ), H.IsHermitian →
  ∀ (u : Zd d L → Zd d L → ℂ) (lam : Zd d L → ℝ), IsOrthoEigenbasis H u lam →
  ∀ κ η ℓt δ Φ : ℝ, 0 < κ → 0 < η → η ≤ 2 - κ → 0 ≤ δ →
    (∀ x, ∀ E ∈ Set.Ioo (-2 + κ) (2 - κ),
      (green H ((E : ℂ) + (η : ℂ) * I) x x).im ≤ 2 ∧
      η * ∑ y ∈ Finset.univ.filter (fun y => (zdistInf d L (y - x) : ℝ) < ℓt),
        ‖green H ((E : ℂ) + (η : ℂ) * I) y x‖ ^ 2 ≤ Φ) →
    (Real.pi / 4 - 6 * Real.sqrt (2 * Real.pi) * δ) * (locSetA d L κ δ ℓt u lam).card ≤
      (4 - 2 * κ) * (L : ℝ) ^ d * Φ := by
  intro d L _ H hH u lam hu κ η ℓt δ Φ hκ hη hηκ hδ hyp
  set A := locSetA d L κ δ ℓt u lam with hA
  set σ := Real.sqrt Real.pi with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr Real.pi_pos
  set K := 3 * Real.sqrt 2 * δ / σ with hK
  set K' := 3 * Real.sqrt 2 * δ * σ / 4 with hK'
  set g : Zd d L → ℝ → ℝ := fun α E => η / ((lam α - E) ^ 2 + η ^ 2) with hg
  have hgpos : ∀ α E, 0 < (lam α - E) ^ 2 + η ^ 2 := fun α E => by positivity
  have hgc : ∀ α, Continuous (g α) := fun α =>
    continuous_const.div (by fun_prop) fun E => (hgpos α E).ne'
  set F : Zd d L → Finset (Zd d L) :=
    fun x => Finset.univ.filter fun y => ℓt ≤ (zdistInf d L (y - x) : ℝ) with hF
  -- the pointwise estimate summed over `x`
  have hpt : ∀ E ∈ Set.Ioo (-2 + κ) (2 - κ),
      ∑ α ∈ A, g α E ≤ (L : ℝ) ^ d * Φ + ∑ α ∈ A, (K * g α E + K') := by
    intro E hE
    set z : ℂ := (E : ℂ) + (η : ℂ) * I with hz
    have hzim : z.im = η := by simp [z]
    have hr2 : ∀ α, ‖(lam α : ℂ) - z‖ ^ 2 = (lam α - E) ^ 2 + η ^ 2 := by
      intro α
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [z]
      ring
    have hr0 : ∀ α, 0 < ‖(lam α : ℂ) - z‖ := fun α =>
      norm_pos_iff.mpr (sub_ne_zero_of_im (lam α) (by rw [hzim]; exact hη.ne'))
    have hx : ∀ x, η * ∑ α ∈ A, ‖u α x‖ ^ 2 / ‖(lam α : ℂ) - z‖ ^ 2 ≤
        Φ + 3 * Real.sqrt (2 * η) *
          ∑ α ∈ A, ‖u α x‖ * Real.sqrt (∑ y ∈ F x, ‖u α y‖ ^ 2) / ‖(lam α : ℂ) - z‖ := by
      intro x
      have hnear : z.im * ∑ y ∈ (F x)ᶜ, ‖green H z y x‖ ^ 2 ≤ Φ := by
        have hc : (F x)ᶜ =
            Finset.univ.filter (fun y => (zdistInf d L (y - x) : ℝ) < ℓt) := by
          rw [hF, Finset.compl_filter]
          exact Finset.filter_congr fun y _ => not_le
        rw [hc, hzim]
        exact (hyp x E hE).2
      have h := pointwise hH hu (z := z) (by rw [hzim]; exact hη) x A (F x) Φ (hyp x E hE).1
        hnear
      rwa [hzim] at h
    have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hx x
    have hL : ∑ x : Zd d L, η * ∑ α ∈ A, ‖u α x‖ ^ 2 / ‖(lam α : ℂ) - z‖ ^ 2 =
        ∑ α ∈ A, g α E := by
      rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_div, sum_norm_sq_eq_one hu α, hr2]
      simp only [g]
      ring
    have hR1 : ∑ x : Zd d L, Φ = (L : ℝ) ^ d * Φ := by
      rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
      push_cast
      ring
    have hR2 : ∑ x : Zd d L, ∑ α ∈ A,
          ‖u α x‖ * Real.sqrt (∑ y ∈ F x, ‖u α y‖ ^ 2) / ‖(lam α : ℂ) - z‖ ≤
        ∑ α ∈ A, δ / ‖(lam α : ℂ) - z‖ := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun α hα => ?_
      rw [← Finset.sum_div]
      refine div_le_div_of_nonneg_right ?_ (hr0 α).le
      exact (Finset.mem_filter.mp hα).2.2
    have hR3 : ∀ α, 3 * Real.sqrt (2 * η) * (δ / ‖(lam α : ℂ) - z‖) ≤ K * g α E + K' := by
      intro α
      have h := amgm_cross η δ _ hη.le hδ (hr0 α)
      rw [hr2] at h
      simp only [g, hK, hK']
      calc 3 * Real.sqrt (2 * η) * (δ / ‖(lam α : ℂ) - z‖)
          = 3 * Real.sqrt (2 * η) * δ / ‖(lam α : ℂ) - z‖ := by ring
        _ ≤ _ := h
        _ = _ := by ring
    rw [Finset.sum_add_distrib, hL, hR1] at hsum
    calc ∑ α ∈ A, g α E
        ≤ (L : ℝ) ^ d * Φ + ∑ x : Zd d L, 3 * Real.sqrt (2 * η) * ∑ α ∈ A,
            ‖u α x‖ * Real.sqrt (∑ y ∈ F x, ‖u α y‖ ^ 2) / ‖(lam α : ℂ) - z‖ := hsum
      _ ≤ (L : ℝ) ^ d * Φ + 3 * Real.sqrt (2 * η) * ∑ α ∈ A, δ / ‖(lam α : ℂ) - z‖ := by
        rw [← Finset.mul_sum]
        gcongr
      _ ≤ (L : ℝ) ^ d * Φ + ∑ α ∈ A, (K * g α E + K') := by
        rw [Finset.mul_sum]
        gcongr with α
        exact hR3 α
  -- integrate over `E ∈ (−2+κ, 2−κ)`
  have hκ2 : -2 + κ ≤ 2 - κ := by linarith
  have hgi : ∀ α, IntervalIntegrable (g α) volume (-2 + κ) (2 - κ) := fun α =>
    (hgc α).intervalIntegrable _ _
  have hIt : ∀ α, IntervalIntegrable (fun E => K * g α E + K') volume (-2 + κ) (2 - κ) :=
    fun α => ((hgi α).const_mul K).add intervalIntegrable_const
  have hI1 : IntervalIntegrable (fun E => ∑ α ∈ A, g α E) volume (-2 + κ) (2 - κ) :=
    (continuous_finsetSum _ fun α _ => hgc α).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun E => ∑ α ∈ A, (K * g α E + K')) volume (-2 + κ) (2 - κ) :=
    (continuous_finsetSum _ fun α _ =>
      ((hgc α).const_mul K).add continuous_const).intervalIntegrable _ _
  have hint : ∫ E in (-2 + κ)..(2 - κ), ∑ α ∈ A, g α E ≤
      ∫ E in (-2 + κ)..(2 - κ), ((L : ℝ) ^ d * Φ + ∑ α ∈ A, (K * g α E + K')) :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hκ2 hI1
      (intervalIntegrable_const.add hI2) hpt
  rw [intervalIntegral.integral_finsetSum fun α _ => hgi α,
    intervalIntegral.integral_add intervalIntegrable_const hI2,
    intervalIntegral.integral_finsetSum fun α _ => hIt α,
    intervalIntegral.integral_const] at hint
  have hItem : ∀ α, ∫ E in (-2 + κ)..(2 - κ), K * g α E + K' =
      K * (∫ E in (-2 + κ)..(2 - κ), g α E) + (2 - κ - (-2 + κ)) * K' := by
    intro α
    rw [intervalIntegral.integral_add ((hgi α).const_mul K) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  simp_rw [hItem, smul_eq_mul] at hint
  have hFα : ∀ α, ∫ E in (-2 + κ)..(2 - κ), g α E =
      Real.arctan ((2 - κ - lam α) / η) - Real.arctan ((-2 + κ - lam α) / η) :=
    fun α => integral_lorentz (lam α) η _ _ hη
  simp_rw [hFα] at hint
  -- the bulk weight and the cross term, per index
  have hK0 : 0 ≤ K := by positivity
  have hK'0 : 0 ≤ K' := by positivity
  have hσ2 : σ ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hconst : K * Real.pi + 4 * K' = 6 * Real.sqrt (2 * Real.pi) * δ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hK, hK', ← hσ, ← hσ2]
    field_simp
    ring
  have hlow : ∑ α ∈ A, Real.pi / 4 ≤ ∑ α ∈ A,
      (Real.arctan ((2 - κ - lam α) / η) - Real.arctan ((-2 + κ - lam α) / η)) := by
    refine Finset.sum_le_sum fun α hα => ?_
    have hb := (Finset.mem_filter.mp hα).2.1
    exact quarter_le_arctan_sub (lam α) η _ _ hη hb.1 hb.2 (by linarith)
  have hup : ∑ α ∈ A, (K * (Real.arctan ((2 - κ - lam α) / η) -
        Real.arctan ((-2 + κ - lam α) / η)) + (2 - κ - (-2 + κ)) * K') ≤
      ∑ α ∈ A, 6 * Real.sqrt (2 * Real.pi) * δ := by
    refine Finset.sum_le_sum fun α _ => ?_
    rw [← hconst]
    have h1 := arctan_sub_le_pi ((2 - κ - lam α) / η) ((-2 + κ - lam α) / η)
    have h2 : K * (Real.arctan ((2 - κ - lam α) / η) -
        Real.arctan ((-2 + κ - lam α) / η)) ≤ K * Real.pi := mul_le_mul_of_nonneg_left h1 hK0
    have h3 : (2 - κ - (-2 + κ)) * K' ≤ 4 * K' := mul_le_mul_of_nonneg_right (by linarith) hK'0
    linarith
  rw [Finset.sum_const, nsmul_eq_mul] at hlow hup
  have : (Real.pi / 4) * (A.card : ℝ) ≤
      (2 - κ - (-2 + κ)) * ((L : ℝ) ^ d * Φ) +
        (A.card : ℝ) * (6 * Real.sqrt (2 * Real.pi) * δ) := by
    linarith
  nlinarith

end RBM8D
