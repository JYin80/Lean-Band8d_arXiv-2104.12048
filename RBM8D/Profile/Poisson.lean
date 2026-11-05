import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.PSeries
import RBM8D.Profile.Basic

/-!
# Poisson summation on `ℝ^d`

d-dimensional Poisson summation for Schwartz functions, for the profile, and on the torus.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

namespace RBM8D

section Lattice

variable {d : ℕ}

/-- The weight `∏ᵢ (1 + xᵢ²)⁻¹` on `ℝ^d`. -/
private def wt (x : Fin d → ℝ) : ℝ := ∏ i, (1 + x i ^ 2)⁻¹

private theorem wt_nonneg (x : Fin d → ℝ) : 0 ≤ wt x :=
  Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by positivity)

private theorem summable_inv_one_add_sq :
    Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded_eventually
    (Real.summable_one_div_int_pow.mpr one_lt_two) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (by positivity)), one_div]
  exact inv_anti₀ (by positivity) (by linarith)

private theorem summable_wt :
    Summable (fun n : Fin d → ℤ => wt (fun i => (n i : ℝ))) := by
  set S := ∑' k : ℤ, (1 + (k : ℝ) ^ 2)⁻¹
  refine summable_of_sum_le (c := S ^ d) (fun n => wt_nonneg _) fun u => ?_
  classical
  calc ∑ n ∈ u, wt (fun i => (n i : ℝ))
      ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n : Fin d → ℤ => n i)),
          wt (fun i => (n i : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => wt_nonneg _
        rw [Fintype.mem_piFinset]
        exact fun i => Finset.mem_image_of_mem _ hn
    _ = ∏ i : Fin d, ∑ k ∈ u.image (fun n : Fin d → ℤ => n i), (1 + (k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.prod_univ_sum]; rfl
    _ ≤ ∏ i : Fin d, S := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => by positivity)
          fun i _ => ?_
        exact summable_inv_one_add_sq.sum_le_tsum _ (fun k _ => by positivity)
    _ = S ^ d := by simp

/-- `(1 + (x + y)²)⁻¹ ≤ 2 (1 + x²) (1 + y²)⁻¹`. -/
private theorem inv_one_add_sq_add_le (x y : ℝ) :
    (1 + (x + y) ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2) * (1 + y ^ 2)⁻¹ := by
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  rw [show 2 * (1 + x ^ 2) * (1 + y ^ 2)⁻¹ * (1 + (x + y) ^ 2) =
    (2 * (1 + x ^ 2) * (1 + (x + y) ^ 2)) / (1 + y ^ 2) by ring]
  rw [one_le_div (by positivity)]
  nlinarith [sq_nonneg (x + y + x), sq_nonneg x, sq_nonneg (x + y), sq_nonneg (x * (x + y))]

private theorem wt_add_le (x y : Fin d → ℝ) (R : ℝ) (hx : ∀ i, |x i| ≤ R) :
    wt (x + y) ≤ (2 * (1 + R ^ 2)) ^ d * wt y := by
  unfold wt
  rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => inv_nonneg.mpr (by positivity)) fun i _ => ?_
  refine (inv_one_add_sq_add_le (x i) (y i)).trans ?_
  have : x i ^ 2 ≤ R ^ 2 := sq_le_sq' (abs_le.mp (hx i)).1 (abs_le.mp (hx i)).2
  gcongr

/-- Schwartz decay against the weight `∏ᵢ (1 + xᵢ²)⁻¹`. -/
private theorem schwartz_le_wt (h : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    ∃ C, 0 ≤ C ∧ ∀ x : Fin d → ℝ, ‖h (WithLp.toLp 2 x)‖ ≤ C * wt x := by
  set C := 2 ^ (2 * d) * (Finset.Iic ((2 * d, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h
  have hC : ∀ v, (1 + ‖v‖) ^ (2 * d) * ‖h v‖ ≤ C := by
    intro v
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (2 * d, 0)) le_rfl le_rfl h v
    rwa [norm_iteratedFDeriv_zero] at this
  refine ⟨C, le_trans (by positivity) (hC 0), fun x => ?_⟩
  set v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  have hxi : ∀ i, x i ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i
    rw [EuclideanSpace.norm_sq_eq]
    have := Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    simpa [v] using this
  have hprod : ∏ i, (1 + x i ^ 2) ≤ (1 + ‖v‖) ^ (2 * d) := by
    rw [pow_mul, ← Fin.prod_const]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    nlinarith [hxi i, norm_nonneg v]
  have hpos : 0 < ∏ i, (1 + x i ^ 2) := Finset.prod_pos fun i _ => by positivity
  have hw : wt x = (∏ i, (1 + x i ^ 2))⁻¹ := by
    unfold wt; rw [Finset.prod_inv_distrib]
  rw [hw, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖h v‖ * ∏ i, (1 + x i ^ 2) ≤ ‖h v‖ * (1 + ‖v‖) ^ (2 * d) := by gcongr
    _ ≤ C := by rw [mul_comm]; exact hC v

/-- A point of `ℤ^d` as a point of `Fin d → ℝ`. -/
private def icast (n : Fin d → ℤ) : Fin d → ℝ := fun i => (n i : ℝ)

private theorem icast_add (m n : Fin d → ℤ) : icast (m + n) = icast m + icast n := by
  ext i; simp [icast]

/-- A Schwartz function on `ℝ^d` read on `Fin d → ℝ`. -/
private def gpi (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : Fin d → ℝ) : ℂ := g (WithLp.toLp 2 x)

private theorem continuous_gpi (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : Continuous (gpi g) :=
  g.continuous.comp (PiLp.continuous_toLp 2 _)

private theorem integrable_gpi (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : Integrable (gpi g) := by
  have h := (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding (g := g)
  exact h.mpr g.integrable

private theorem gpi_add_le (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    ∃ C, 0 ≤ C ∧ ∀ (R : ℝ) (x : Fin d → ℝ), (∀ i, |x i| ≤ R) → ∀ n : Fin d → ℤ,
      ‖gpi g (x + icast n)‖ ≤ C * (2 * (1 + R ^ 2)) ^ d * wt (icast n) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_le_wt g
  refine ⟨C, hC0, fun R x hx n => ?_⟩
  calc ‖gpi g (x + icast n)‖ ≤ C * wt (x + icast n) := hC _
    _ ≤ C * ((2 * (1 + R ^ 2)) ^ d * wt (icast n)) := by
        gcongr; exact wt_add_le x (icast n) R hx
    _ = _ := by ring

private theorem summable_norm_gpi (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    Summable (fun n : Fin d → ℤ => ‖g (intVec n)‖) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_le_wt g
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hC (icast n))
    (summable_wt.mul_left C)

/-- The periodisation `x ↦ Σ_{n∈ℤ^d} g(x + n)`. -/
private def per (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : Fin d → ℝ) : ℂ :=
  ∑' n : Fin d → ℤ, gpi g (x + icast n)

private theorem per_add (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : Fin d → ℝ) (k : Fin d → ℤ) :
    per g (x + icast k) = per g x := by
  unfold per
  rw [← (Equiv.addLeft k).tsum_eq (fun n => gpi g (x + icast n))]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addLeft, icast_add, add_assoc]

private theorem continuous_per (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : Continuous (per g) := by
  obtain ⟨C, hC0, hC⟩ := gpi_add_le g
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  set R := ‖x₀‖ + 1
  have hs : {x : Fin d → ℝ | ∀ i, |x i| ≤ R} ∈ nhds x₀ := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x₀ one_pos) fun x hx i => ?_
    have h1 : |x i| ≤ ‖x‖ := by simpa using norm_le_pi_norm x i
    have h2 : ‖x‖ - ‖x₀‖ ≤ ‖x - x₀‖ := norm_sub_norm_le x x₀
    rw [Metric.mem_ball, dist_eq_norm] at hx
    simp only [R]
    linarith
  refine ContinuousOn.continuousAt ?_ hs
  exact continuousOn_tsum
    (fun n => ((continuous_gpi g).comp (continuous_id.add continuous_const)).continuousOn)
    (summable_wt.mul_left (C * (2 * (1 + R ^ 2)) ^ d)) fun n x hx => hC R x hx n

/-- The quotient map `ℝ^d → ℝ^d/ℤ^d`. -/
private def tq : C(Fin d → ℝ, UnitAddTorus (Fin d)) :=
  ⟨fun x i => (x i : UnitAddCircle), by fun_prop⟩

private theorem isQuotientMap_tq : Topology.IsQuotientMap (tq (d := d)) :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

private theorem per_factors (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    Function.FactorsThrough (per g) (tq (d := d)) := by
  intro a b h
  have hi : ∀ i, ∃ k : ℤ, (k : ℝ) = b i - a i := by
    intro i
    have h' : ((a i : ℝ) : UnitAddCircle) = (b i : UnitAddCircle) := congrFun h i
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h')
    exact ⟨k, by rw [zsmul_eq_mul, mul_one] at hk; linarith⟩
  choose k hk using hi
  have hb : b = a + icast k := by
    ext i; simp [icast, hk]
  rw [hb, per_add]

/-- The periodisation as a continuous function on the torus `ℝ^d/ℤ^d`. -/
private def perT (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : C(UnitAddTorus (Fin d), ℂ) :=
  isQuotientMap_tq.lift ⟨per g, continuous_per g⟩ (per_factors g)

private theorem perT_tq (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : Fin d → ℝ) :
    perT g (tq x) = per g x := by
  exact DFunLike.congr_fun
    (isQuotientMap_tq.lift_comp ⟨per g, continuous_per g⟩ (per_factors g)) x

/-- The unit box `(0, 1]^d`. -/
private def box : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1

/-- Tiling `ℝ^d` by the translates `(0, 1]^d + n`, `n ∈ ℤ^d`. -/
private theorem tsum_integral_box (H : (Fin d → ℝ) → ℂ) (hH : Integrable H) :
    ∑' n : Fin d → ℤ, ∫ x in box, H (x + icast n) = ∫ x, H x := by
  set S : (Fin d → ℤ) → Set (Fin d → ℝ) :=
    fun n => Set.univ.pi fun i => Set.Ioc (n i : ℝ) (n i + 1) with hS
  have hm : ∀ n, MeasurableSet (S n) := fun n => MeasurableSet.univ_pi fun i => measurableSet_Ioc
  have hceil : ∀ (y : ℝ) (k : ℤ), y ∈ Set.Ioc (k : ℝ) (k + 1) → ⌈y⌉ = k + 1 := by
    intro y k hy
    rw [Int.ceil_eq_iff]
    push_cast
    exact ⟨by linarith [hy.1], hy.2⟩
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro n n' hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy hy'
    apply hne
    funext i
    have h1 := hceil _ _ (hy i (Set.mem_univ i))
    have h2 := hceil _ _ (hy' i (Set.mem_univ i))
    omega
  have hU : (⋃ n, S n) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ⟨fun i => ⌈y i⌉ - 1, ?_⟩
    intro i _
    push_cast
    exact ⟨by linarith [Int.ceil_lt_add_one (y i)], by linarith [Int.le_ceil (y i)]⟩
  have h1 := integral_iUnion hm hd hH.integrableOn
  rw [hU, setIntegral_univ] at h1
  rw [h1]
  refine tsum_congr fun n => ?_
  have hmp := measurePreserving_add_right (volume : Measure (Fin d → ℝ)) (icast n)
  rw [← hmp.setIntegral_preimage_emb (measurableEmbedding_addRight (icast n)) H (S n)]
  congr 2
  ext x
  simp only [box, hS, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc,
    Pi.add_apply, icast]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The character `x ↦ e^{−2πi m·x}` on `Fin d → ℝ`. -/
private def ech (m : Fin d → ℤ) (x : Fin d → ℝ) : ℂ :=
  cexp (((-2 * Real.pi * ∑ i, x i * (m i : ℝ) : ℝ) : ℂ) * I)

private theorem norm_ech (m : Fin d → ℤ) (x : Fin d → ℝ) : ‖ech m x‖ = 1 := by
  unfold ech; exact Complex.norm_exp_ofReal_mul_I _

private theorem ech_add (m n : Fin d → ℤ) (x : Fin d → ℝ) : ech m (x + icast n) = ech m x := by
  unfold ech
  have hsplit : ∑ i, (x + icast n) i * (m i : ℝ) = ∑ i, x i * (m i : ℝ) +
      ((∑ i, n i * m i : ℤ) : ℝ) := by
    simp only [Pi.add_apply, icast, add_mul, Finset.sum_add_distrib]
    push_cast; rfl
  rw [hsplit]
  have h1 : (((-2 * Real.pi * (∑ i, x i * (m i : ℝ) + ((∑ i, n i * m i : ℤ) : ℝ)) : ℝ) : ℂ) * I) =
      (((-2 * Real.pi * ∑ i, x i * (m i : ℝ) : ℝ) : ℂ) * I) +
        ((-(∑ i, n i * m i) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem mFourier_tq (m : Fin d → ℤ) (x : Fin d → ℝ) :
    UnitAddTorus.mFourier (-m) (tq x) = ech m x := by
  simp only [UnitAddTorus.mFourier, tq, ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply,
    ech]
  rw [show (((-2 * Real.pi * ∑ i, x i * (m i : ℝ) : ℝ) : ℂ) * I) =
      ∑ i, (2 * Real.pi * I * ((-m i : ℤ) : ℂ) * (x i : ℂ) / ((1 : ℝ) : ℂ)) by
    push_cast; rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring]
  rw [Complex.exp_sum]

private theorem integral_ech_gpi (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (m : Fin d → ℤ) :
    ∫ x, ech m x * gpi g x = 𝓕 (g : EuclideanSpace ℝ (Fin d) → ℂ) (intVec m) := by
  rw [Real.fourier_eq']
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm.integral_comp'
    (fun v : EuclideanSpace ℝ (Fin d) =>
      cexp (((-2 * Real.pi * inner ℝ v (intVec m) : ℝ) : ℂ) * I) • g v)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ech, gpi, smul_eq_mul, intVec]
  congr 4
  simp [PiLp.inner_apply, mul_comm]

private theorem mFourierCoeff_perT (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (m : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (perT g) m = 𝓕 (g : EuclideanSpace ℝ (Fin d) → ℂ) (intVec m) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ 0, ← integral_ech_gpi g m]
  have hset : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin d → ℝ) i) ((0 : Fin d → ℝ) i + 1)} =
      box := by
    ext x; simp [box, Set.mem_pi]
  rw [hset]
  set H : (Fin d → ℝ) → ℂ := fun x => ech m x * gpi g x with hH
  have hHi : Integrable H := by
    refine (integrable_gpi g).bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Continuous.aestronglyMeasurable (by unfold ech; fun_prop))
    · rw [norm_ech]
  have hpt : ∀ x : Fin d → ℝ, UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
      perT g (fun i => (x i : UnitAddCircle)) = ∑' n : Fin d → ℤ, H (x + icast n) := by
    intro x
    change UnitAddTorus.mFourier (-m) (tq x) • perT g (tq x) = _
    rw [mFourier_tq, perT_tq, per, smul_eq_mul, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [hH, ech_add]
  simp_rw [hpt]
  rw [← tsum_integral_box H hHi]
  obtain ⟨C, hC0, hC⟩ := gpi_add_le g
  have hbox : volume (box : Set (Fin d → ℝ)) < ⊤ := by
    simp [box, Real.volume_pi_Ioc]
  refine (integral_tsum_of_summable_integral_norm (fun n => ?_) ?_).symm
  · exact (hHi.comp_add_right (icast n)).integrableOn
  · refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) ((summable_wt.mul_left (C * (2 * (1 + 1 ^ 2)) ^ d)).mul_right
        (volume.real (box : Set (Fin d → ℝ))))
    have hb := norm_setIntegral_le_of_norm_le_const (f := fun x => ‖H (x + icast n)‖) hbox
      (C := C * (2 * (1 + 1 ^ 2)) ^ d * wt (icast n)) (fun x hx => by
        rw [norm_norm]
        simp only [hH, norm_mul, norm_ech, one_mul]
        refine hC 1 x (fun i => ?_) n
        have := hx i (Set.mem_univ i)
        rw [abs_le]; constructor <;> linarith [this.1, this.2])
    exact (Real.le_norm_self _).trans hb

/-- Poisson summation on `Fin d → ℝ` through the Fourier series of the periodisation. -/
private theorem poisson_aux (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    HasSum (fun m : Fin d → ℤ => 𝓕 (g : EuclideanSpace ℝ (Fin d) → ℂ) (intVec m))
      (∑' n : Fin d → ℤ, g (intVec n)) := by
  have hsum : Summable (UnitAddTorus.mFourierCoeff (perT g)) := by
    have h := summable_norm_gpi (SchwartzMap.fourierTransformCLM ℂ g)
    refine (Summable.of_norm ?_)
    refine h.congr fun m => ?_
    rw [mFourierCoeff_perT]
    rfl
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum 0
  have h0 : perT g 0 = ∑' n : Fin d → ℤ, g (intVec n) := by
    have : (0 : UnitAddTorus (Fin d)) = tq 0 := by
      funext i; simp [tq]
    rw [this, perT_tq, per]
    refine tsum_congr fun n => ?_
    simp only [gpi, zero_add]
    rfl
  rw [h0] at h
  refine h.congr_fun fun m => ?_
  rw [mFourierCoeff_perT]
  simp [UnitAddTorus.mFourier]

end Lattice

/-- Poisson summation on `ℝ^d` for Schwartz functions (the Poisson summation formula behind
[I, (1.10)]), with Mathlib's Fourier transform `𝓕 g (w) = ∫ e^{−2πi⟨v,w⟩} g(v) dv`:
`Σ_{n∈ℤ^d} g(n) = Σ_{m∈ℤ^d} 𝓕 g (m)`, both series being summable. -/
theorem poisson :
  ∀ (d : ℕ) (g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)),
    Summable (fun n : Fin d → ℤ => g (intVec n)) ∧
      Summable (fun m : Fin d → ℤ => 𝓕 (g : EuclideanSpace ℝ (Fin d) → ℂ) (intVec m)) ∧
      ∑' n : Fin d → ℤ, g (intVec n) =
        ∑' m : Fin d → ℤ, 𝓕 (g : EuclideanSpace ℝ (Fin d) → ℂ) (intVec m) := by
  intro d g
  have h := poisson_aux g
  exact ⟨(summable_norm_gpi g).of_norm, h.summable, h.tsum_eq.symm⟩

section ProfileSum

variable {d : ℕ}

/-- `w ↦ ψ(W(p + 2πw))` as a complex Schwartz function. -/
private def psiShift (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (hW : 0 < W)
    (p : EuclideanSpace ℝ (Fin d)) : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin d)) (2 * Real.pi * W)
      (by positivity)).toContinuousLinearEquiv
    (SchwartzMap.compSubConstCLM ℂ (-(W • p)) (SchwartzMap.postcompCLM Complex.ofRealCLM ψ))

private theorem psiShift_apply (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (hW : 0 < W)
    (p w : EuclideanSpace ℝ (Fin d)) :
    psiShift ψ W hW p w = (ψ (W • (p + (2 * Real.pi) • w)) : ℂ) := by
  simp only [psiShift, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.compSubConstCLM_apply, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply]
  congr 2
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
    sub_neg_eq_add,
    smul_add, smul_smul]
  rw [add_comm, mul_comm W]

/-- `𝓕⁻[w ↦ ψ(W(p + 2πw))](y) = (2π)^{−d} ∫ ψ(Wq) e^{iq·y} dq · e^{−ip·y}`. -/
private theorem fourierInv_psiShift (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (hW : 0 < W)
    (p y : EuclideanSpace ℝ (Fin d)) :
    𝓕⁻ (psiShift ψ W hW p : EuclideanSpace ℝ (Fin d) → ℂ) y =
      profInt ψ W y * cexp (-(I * (inner ℝ p y : ℝ))) := by
  rw [profInt_eq_fourierInv d ψ W y, Real.fourierInv_eq', Real.fourierInv_eq']
  set a : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • p
  set F : EuclideanSpace ℝ (Fin d) → ℂ := fun u => cexp (-(I * (inner ℝ p y : ℝ))) *
    (cexp (((2 * Real.pi * inner ℝ u y : ℝ) : ℂ) * I) • (ψ ((2 * Real.pi * W) • u) : ℂ)) with hF
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have key : ∀ v, cexp (((2 * Real.pi * inner ℝ v y : ℝ) : ℂ) * I) • psiShift ψ W hW p v =
      F (v + a) := by
    intro v
    simp only [hF, smul_eq_mul, psiShift_apply, inner_add_left, real_inner_smul_left, a]
    have hpt : W • (p + (2 * Real.pi) • v) = (2 * Real.pi * W) • (v + (2 * Real.pi)⁻¹ • p) := by
      have hc : 2 * Real.pi * W * (2 * Real.pi)⁻¹ = W := by field_simp
      rw [smul_add, smul_add, smul_smul, smul_smul, hc, add_comm, mul_comm W]
    rw [hpt, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [key]
  rw [integral_add_right_eq_self F a]
  simp only [hF]
  rw [integral_const_mul, mul_comm]

end ProfileSum

/-- Poisson summation for the integral of [I, (1.6)]: for `W > 0` and `p ∈ ℝ^d`,
`Σ_{z∈ℤ^d} [(2π)^{−d} ∫ ψ(Wq) e^{iq·z} dq] e^{−ip·z} = Σ_{j∈ℤ^d} ψ(W(p + 2πj))`, the right side
being summable. -/
theorem poisson_profile :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (hW : 0 < W)
    (p : EuclideanSpace ℝ (Fin d)),
    Summable (fun j : Fin d → ℤ => ψ (W • (p + (2 * Real.pi) • intVec j))) ∧
      HasSum
        (fun z : Fin d → ℤ => profInt ψ W (intVec z) * cexp (-(I * (inner ℝ p (intVec z) : ℝ))))
        (∑' j : Fin d → ℤ, (ψ (W • (p + (2 * Real.pi) • intVec j)) : ℂ)) := by
  intro d ψ W hW p
  set g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := 𝓕⁻ (psiShift ψ W hW p)
  have hg : ∀ y, g y = profInt ψ W y * cexp (-(I * (inner ℝ p y : ℝ))) := by
    intro y
    rw [show g y = 𝓕⁻ (psiShift ψ W hW p : EuclideanSpace ℝ (Fin d) → ℂ) y by
      rw [← SchwartzMap.fourierInv_coe]]
    exact fourierInv_psiShift ψ W hW p y
  have hFg : ∀ w, 𝓕 (g : EuclideanSpace ℝ (Fin d) → ℂ) w =
      (ψ (W • (p + (2 * Real.pi) • w)) : ℂ) := by
    intro w
    rw [← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq, psiShift_apply]
  obtain ⟨h1, h2, h3⟩ := poisson d g
  simp only [hFg] at h2 h3
  simp only [hg] at h1 h3
  refine ⟨Complex.summable_ofReal.mp h2, ?_⟩
  rw [← h3]
  exact h1.hasSum

section TorusSum

variable {d : ℕ}

end TorusSum

section Witness

end Witness

end RBM8D
