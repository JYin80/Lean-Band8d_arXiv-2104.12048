module

public import RBM8D.Profile.Poisson

@[expose] public section

/-!
# The normaliser `Z_{W,L}`

[I, (1.6)], (1.10): `Z_{W,L} → 1` with explicit error, on `adm` and for `L ≥ W^{1+ε}`.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

namespace RBM8D

section Aux

variable {d : ℕ}

/-- The constant `Σ_{k∈ℤ} (1 + |k|)^{−2}`. -/
private def Kc : ℝ := ∑' k : ℤ, ((1 + |(k : ℝ)|) ^ 2)⁻¹

private theorem summable_Kc : Summable (fun k : ℤ => ((1 + |(k : ℝ)|) ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_one_div_int_pow.mpr one_lt_two) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hpos : 0 < |(k : ℝ)| := abs_pos.mpr hk'
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (by positivity)), one_div]
  refine inv_anti₀ (by positivity) ?_
  rw [← sq_abs (k : ℝ)]
  exact pow_le_pow_left₀ hpos.le (by linarith) 2

private theorem Kc_nonneg : 0 ≤ Kc := tsum_nonneg fun k => by positivity

/-- A finite sum of `∏ᵢ a(jᵢ)` over `ℤ^d` is at most `(Σ_k a(k))^d`. -/
private theorem prod_sum_le (a : ℤ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a)
    (u : Finset (Fin d → ℤ)) : ∑ j ∈ u, ∏ i, a (j i) ≤ (∑' k, a k) ^ d := by
  classical
  calc ∑ j ∈ u, ∏ i, a (j i)
      ≤ ∑ j ∈ Fintype.piFinset (fun i => u.image (fun n : Fin d → ℤ => n i)), ∏ i, a (j i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ =>
          Finset.prod_nonneg fun i _ => ha0 _
        rw [Fintype.mem_piFinset]
        exact fun i => Finset.mem_image_of_mem _ hn
    _ = ∏ i : Fin d, ∑ k ∈ u.image (fun n : Fin d → ℤ => n i), a k := by
        rw [Finset.prod_univ_sum]
    _ ≤ ∏ i : Fin d, ∑' k, a k := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => ha0 k) fun i _ => ?_
        exact ha.sum_le_tsum _ (fun k _ => ha0 k)
    _ = (∑' k, a k) ^ d := by simp

private theorem summable_prod_weight (a : ℤ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a) :
    Summable (fun j : Fin d → ℤ => ∏ i, a (j i)) :=
  summable_of_sum_le (c := (∑' k, a k) ^ d) (fun j => Finset.prod_nonneg fun i _ => ha0 _)
    fun u => prod_sum_le a ha0 ha u

private theorem tsum_prod_weight_le (a : ℤ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha : Summable a) :
    ∑' j : Fin d → ℤ, ∏ i, a (j i) ≤ (∑' k, a k) ^ d :=
  Real.tsum_le_of_sum_le (fun j => Finset.prod_nonneg fun i _ => ha0 _)
    fun u => prod_sum_le a ha0 ha u

/-- `(1 + c|k|)^{−2} ≤ (min 1 c)^{−2} (1 + |k|)^{−2}` for `c > 0`. -/
private theorem weight_le (c : ℝ) (hc : 0 < c) (k : ℤ) :
    ((1 + c * |(k : ℝ)|) ^ 2)⁻¹ ≤ ((min 1 c) ^ 2)⁻¹ * ((1 + |(k : ℝ)|) ^ 2)⁻¹ := by
  have hm : 0 < min 1 c := lt_min one_pos hc
  have h1 : min 1 c * (1 + |(k : ℝ)|) ≤ 1 + c * |(k : ℝ)| := by
    have h2 := min_le_left 1 c
    have h3 := min_le_right 1 c
    nlinarith [abs_nonneg (k : ℝ)]
  rw [← mul_inv, ← mul_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 2)

/-- The sum `Σ_{j∈ℤ^d} ∏ᵢ (1 + c|jᵢ|)^{−2}` converges and is at most `((min 1 c)^{−2} K)^d`. -/
private theorem lat_weight (c : ℝ) (hc : 0 < c) :
    Summable (fun j : Fin d → ℤ => ∏ i, ((1 + c * |(j i : ℝ)|) ^ 2)⁻¹) ∧
      ∑' j : Fin d → ℤ, ∏ i, ((1 + c * |(j i : ℝ)|) ^ 2)⁻¹ ≤ (((min 1 c) ^ 2)⁻¹ * Kc) ^ d := by
  have hm : 0 < min 1 c := lt_min one_pos hc
  set a : ℤ → ℝ := fun k => ((1 + c * |(k : ℝ)|) ^ 2)⁻¹ with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => inv_nonneg.mpr (sq_nonneg _)
  have hsum : Summable a :=
    Summable.of_nonneg_of_le ha0 (fun k => weight_le c hc k) (summable_Kc.mul_left _)
  refine ⟨summable_prod_weight a ha0 hsum, (tsum_prod_weight_le a ha0 hsum).trans ?_⟩
  refine pow_le_pow_left₀ (tsum_nonneg ha0) ?_ d
  calc ∑' k, a k ≤ ∑' k : ℤ, ((min 1 c) ^ 2)⁻¹ * ((1 + |(k : ℝ)|) ^ 2)⁻¹ :=
        hsum.tsum_le_tsum (fun k => weight_le c hc k) (summable_Kc.mul_left _)
    _ = ((min 1 c) ^ 2)⁻¹ * Kc := by rw [tsum_mul_left]; rfl

/-- Schwartz decay in product form: `‖h(v)‖ ≤ C ∏ᵢ (1 + |vᵢ|)^{−n}`. -/
private theorem schwartz_prod_decay {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : 𝓢(EuclideanSpace ℝ (Fin d), F)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : EuclideanSpace ℝ (Fin d), ‖h v‖ ≤ C * ∏ i, ((1 + |v i|) ^ n)⁻¹ := by
  set C := 2 ^ (n * d) * (Finset.Iic ((n * d, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hCdef
  have hC : ∀ v, (1 + ‖v‖) ^ (n * d) * ‖h v‖ ≤ C := by
    intro v
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (n * d, 0)) le_rfl le_rfl h v
    rwa [norm_iteratedFDeriv_zero] at this
  refine ⟨C, le_trans (by positivity) (hC 0), fun v => ?_⟩
  have hprod : ∏ i, (1 + |v i|) ^ n ≤ (1 + ‖v‖) ^ (n * d) := by
    rw [pow_mul, ← Fin.prod_const]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    have : |v i| ≤ ‖v‖ := by simpa using PiLp.norm_apply_le v i
    gcongr
  have hpos : 0 < ∏ i, (1 + |v i|) ^ n := Finset.prod_pos fun i _ => by positivity
  rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖h v‖ * ∏ i, (1 + |v i|) ^ n ≤ ‖h v‖ * (1 + ‖v‖) ^ (n * d) := by gcongr
    _ ≤ C := by rw [mul_comm]; exact hC v

/-- The tail bound at the lattice point `c·z`, when some coordinate satisfies `|zᵢ| ≥ T`:
`‖h(c z)‖ ≤ C (1 + cT)^{−N} ∏ᵢ (1 + c|zᵢ|)^{−2}`. -/
private theorem tail_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : 𝓢(EuclideanSpace ℝ (Fin d), F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c T : ℝ), 0 < c → 0 ≤ T → ∀ z : Fin d → ℤ, (∃ i, T ≤ |(z i : ℝ)|) →
      ‖h (c • intVec z)‖ ≤ C * ((1 + c * T) ^ N)⁻¹ * ∏ i, ((1 + c * |(z i : ℝ)|) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := schwartz_prod_decay h (N + 2)
  refine ⟨C, hC0, fun c T hc hT z ⟨i0, hi0⟩ => ?_⟩
  have hcoord : ∀ i, |(c • intVec z) i| = c * |(z i : ℝ)| := by
    intro i
    simp [intVec, abs_mul, abs_of_pos hc]
  have hnn : ∀ i, 0 ≤ c * |(z i : ℝ)| := fun i => mul_nonneg hc.le (abs_nonneg _)
  refine (hC _).trans ?_
  simp only [hcoord]
  have hsplit : ∏ i, ((1 + c * |(z i : ℝ)|) ^ (N + 2))⁻¹ =
      (∏ i, ((1 + c * |(z i : ℝ)|) ^ N)⁻¹) * ∏ i, ((1 + c * |(z i : ℝ)|) ^ 2)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_add, mul_inv]
  have hle : ∏ i, ((1 + c * |(z i : ℝ)|) ^ N)⁻¹ ≤ ((1 + c * T) ^ N)⁻¹ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
    have h1 : ∏ i ∈ Finset.univ.erase i0, ((1 + c * |(z i : ℝ)|) ^ N)⁻¹ ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => inv_nonneg.mpr (pow_nonneg (by linarith [hnn i]) N))
        (fun i _ => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hnn i])))
    have h2 : ((1 + c * |(z i0 : ℝ)|) ^ N)⁻¹ ≤ ((1 + c * T) ^ N)⁻¹ := by
      have : 0 < 1 + c * T := by positivity
      refine inv_anti₀ (pow_pos this N) (pow_le_pow_left₀ this.le ?_ N)
      have := mul_le_mul_of_nonneg_left hi0 hc.le
      linarith
    have h3 : 0 ≤ ((1 + c * |(z i0 : ℝ)|) ^ N)⁻¹ :=
      inv_nonneg.mpr (pow_nonneg (by linarith [hnn i0]) N)
    calc ((1 + c * |(z i0 : ℝ)|) ^ N)⁻¹ * ∏ i ∈ Finset.univ.erase i0,
          ((1 + c * |(z i : ℝ)|) ^ N)⁻¹ ≤ ((1 + c * |(z i0 : ℝ)|) ^ N)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ _ := by rw [mul_one]; exact h2
  have hB : 0 ≤ ∏ i, ((1 + c * |(z i : ℝ)|) ^ 2)⁻¹ :=
    Finset.prod_nonneg fun i _ => inv_nonneg.mpr (sq_nonneg _)
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC0) hB

/-- A series over `ℤ^d` dominated by `M ∏ᵢ (1 + c|zᵢ|)^{−2}` has sum of absolute value at most
`M ((min 1 c)^{−2} K)^d`. -/
private theorem hasSum_bound (c : ℝ) (hc : 0 < c) (M : ℝ) (hM : 0 ≤ M)
    (F : (Fin d → ℤ) → ℝ) (a : ℝ) (hF : HasSum F a)
    (hb : ∀ z, ‖F z‖ ≤ M * ∏ i, ((1 + c * |(z i : ℝ)|) ^ 2)⁻¹) :
    |a| ≤ M * (((min 1 c) ^ 2)⁻¹ * Kc) ^ d := by
  obtain ⟨hs, hle⟩ := lat_weight (d := d) c hc
  have hg := (hs.mul_left M).hasSum
  have h1 := hF.norm_le_of_bounded hg hb
  rw [tsum_mul_left] at h1
  rw [← Real.norm_eq_abs]
  exact h1.trans (mul_le_mul_of_nonneg_left hle hM)

/-- The density `φ(y) = (2π)^{−d} ∫ ψ(q) e^{iq·y} dq` is a Schwartz function. -/
private theorem exists_phi (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) :
    ∃ Φ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ), ∀ y, profInt ψ 1 y = Φ y := by
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin d)) (2 * Real.pi)
      h2pi).toContinuousLinearEquiv
  let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
      (SchwartzMap.postcompCLM (Complex.ofRealCLM) ψ)
  have hprof : profInt ψ 1 = 𝓕⁻ (G : EuclideanSpace ℝ (Fin d) → ℂ) := by
    funext y
    rw [profInt_eq_fourierInv d ψ 1 y]
    simp only [mul_one]
    congr 1
  exact ⟨𝓕⁻ G, fun y => by rw [hprof, SchwartzMap.fourierInv_coe]⟩

/-- Poisson summation at `p = 0`, on real parts: `Σ_z Re φ_W(z) = Σ_j ψ(2πWj)`, `W > 0`. -/
private theorem poisson_re (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (hW : 0 < W) :
    HasSum (fun j : Fin d → ℤ => ψ (W • ((2 * Real.pi) • intVec j)))
        (∑' j : Fin d → ℤ, ψ (W • ((2 * Real.pi) • intVec j))) ∧
      HasSum (fun z : Fin d → ℤ => (profInt ψ W (intVec z)).re)
        (∑' j : Fin d → ℤ, ψ (W • ((2 * Real.pi) • intVec j))) := by
  obtain ⟨h1, h2⟩ := poisson_profile d ψ W hW 0
  simp only [zero_add] at h1 h2
  refine ⟨h1.hasSum, ?_⟩
  have h3 := Complex.hasSum_re h2
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    mul_one] at h3
  rw [← Complex.ofReal_tsum, Complex.ofReal_re] at h3
  exact h3

/-- The dual lattice term: `|Σ_{j∈ℤ^d} ψ(2πWj) − ψ(0)| ≤ C W^{−D}` for `W ≥ 1`. -/
private theorem close_A (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (h0 : ψ 0 = 1) (D : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 1 ≤ W →
      |(∑' j : Fin d → ℤ, ψ (W • ((2 * Real.pi) • intVec j))) - 1| ≤ C / W ^ D := by
  obtain ⟨C, hC0, hC⟩ := tail_bound ψ D
  refine ⟨C * Kc ^ d, mul_nonneg hC0 (pow_nonneg Kc_nonneg d), fun W hW => ?_⟩
  have hW0 : 0 < W := by linarith
  have hpi : 1 ≤ 2 * Real.pi * W := by nlinarith [Real.two_le_pi]
  have hc : 0 < 2 * Real.pi * W := by linarith
  obtain ⟨hs, -⟩ := poisson_re ψ W hW0
  have hF : HasSum (fun j : Fin d → ℤ =>
      ψ (W • ((2 * Real.pi) • intVec j)) - if j = 0 then 1 else 0)
      ((∑' j : Fin d → ℤ, ψ (W • ((2 * Real.pi) • intVec j))) - 1) :=
    hs.sub (hasSum_ite_eq 0 1)
  have hM : 0 ≤ C * ((1 + 2 * Real.pi * W * 1) ^ D)⁻¹ :=
    mul_nonneg hC0 (inv_nonneg.mpr (pow_nonneg (by linarith) D))
  have hbd := hasSum_bound (2 * Real.pi * W) hc _ hM _ _ hF (fun j => by
    by_cases hj : j = 0
    · subst hj
      have h00 : intVec (0 : Fin d → ℤ) = 0 := by ext i; simp [intVec]
      rw [h00, smul_zero, smul_zero, h0]
      simp only [↓reduceIte, sub_self, norm_zero]
      exact mul_nonneg hM (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (sq_nonneg _))
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
      have hi1 : 1 ≤ |(j i : ℝ)| := by
        have : (1 : ℤ) ≤ |j i| := Int.one_le_abs hi
        exact_mod_cast this
      rw [show (if j = 0 then (1 : ℝ) else 0) = 0 from by simp [hj], sub_zero, smul_smul,
        mul_comm W]
      exact hC (2 * Real.pi * W) 1 hc zero_le_one j ⟨i, hi1⟩)
  rw [min_eq_left hpi] at hbd
  refine hbd.trans ?_
  have h1 : ((1 + 2 * Real.pi * W * 1) ^ D)⁻¹ ≤ (W ^ D)⁻¹ :=
    inv_anti₀ (pow_pos hW0 D) (pow_le_pow_left₀ hW0.le (by nlinarith [Real.two_le_pi]) D)
  have hK : 0 ≤ (((1 : ℝ) ^ 2)⁻¹ * Kc) ^ d := pow_nonneg (by simpa using Kc_nonneg) d
  calc C * ((1 + 2 * Real.pi * W * 1) ^ D)⁻¹ * (((1 : ℝ) ^ 2)⁻¹ * Kc) ^ d
      ≤ C * (W ^ D)⁻¹ * (((1 : ℝ) ^ 2)⁻¹ * Kc) ^ d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC0) hK
    _ = C * Kc ^ d / W ^ D := by simp; ring

/-- The truncation term: `|Σ_{j∈ℤ^d} ψ(2πWj) − Z_{W,L}| ≤ C W^d (1 + L/(2W))^{−N}`, the part of
`Σ_{z∈ℤ^d} Re φ_W(z)` outside `Z_L^d`. -/
private theorem close_B (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W L : ℕ) [NeZero L], 1 ≤ W →
      |(∑' j : Fin d → ℤ, ψ ((W : ℝ) • ((2 * Real.pi) • intVec j))) - ZWL ψ W L| ≤
        C * (W : ℝ) ^ d * ((1 + (L : ℝ) / (2 * W)) ^ N)⁻¹ := by
  obtain ⟨Φ, hΦ⟩ := exists_phi ψ
  obtain ⟨C, hC0, hC⟩ := tail_bound Φ N
  refine ⟨C * Kc ^ d, mul_nonneg hC0 (pow_nonneg Kc_nonneg d), fun W L _ hW => ?_⟩
  classical
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨-, hg⟩ := poisson_re ψ (W : ℝ) hW0
  set g : (Fin d → ℤ) → ℝ := fun z => (profInt ψ (W : ℝ) (intVec z)).re with hgdef
  set v : Zd d L → (Fin d → ℤ) := fun x i => (x i).valMinAbs with hv
  have hvinj : Function.Injective v := fun x y hxy =>
    funext fun i => ZMod.injective_valMinAbs (congrFun hxy i)
  set s : Finset (Fin d → ℤ) := Finset.univ.image v with hs
  have hZ : ZWL ψ W L = ∑ z ∈ s, g z := by
    rw [hs, Finset.sum_image (fun x _ y _ hxy => hvinj hxy)]
    rfl
  have hind : HasSum (fun z => if z ∈ s then g z else 0) (∑ z ∈ s, g z) := by
    have h1 : HasSum (fun z => if z ∈ s then g z else 0)
        (∑ z ∈ s, (if z ∈ s then g z else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun z hz => by simp [hz])
    have h2 : ∑ z ∈ s, (if z ∈ s then g z else 0) = ∑ z ∈ s, g z :=
      Finset.sum_congr rfl (fun z hz => by simp [hz])
    rwa [h2] at h1
  have hF := hg.sub hind
  rw [← hZ] at hF
  have hmem : ∀ z : Fin d → ℤ, z ∉ s → ∃ i, (L : ℝ) / 2 ≤ |(z i : ℝ)| := by
    intro z hz
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    apply hz
    rw [hs, Finset.mem_image]
    refine ⟨fun i => (z i : ZMod L), Finset.mem_univ _, funext fun i => ?_⟩
    simp only [hv]
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    have h1 := abs_lt.mp (hcon i)
    constructor
    · have : ((-(L : ℤ) : ℤ) : ℝ) < ((z i * 2 : ℤ) : ℝ) := by push_cast; linarith [h1.1]
      exact_mod_cast this
    · have : ((z i * 2 : ℤ) : ℝ) ≤ (((L : ℤ) : ℤ) : ℝ) := by push_cast; linarith [h1.2]
      exact_mod_cast this
  set ρ : ℝ := ((1 + (W : ℝ)⁻¹ * ((L : ℝ) / 2)) ^ N)⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := inv_nonneg.mpr (pow_nonneg (by positivity) N)
  have hM : 0 ≤ ((W : ℝ) ^ d)⁻¹ * (C * ρ) :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hW0.le d)) (mul_nonneg hC0 hρ0)
  have hbd := hasSum_bound ((W : ℝ)⁻¹) (inv_pos.mpr hW0) _ hM _ _ hF (fun z => by
    by_cases hz : z ∈ s
    · rw [show (if z ∈ s then g z else 0) = g z from by simp [hz], sub_self, norm_zero]
      exact mul_nonneg hM (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (sq_nonneg _))
    · rw [show (if z ∈ s then g z else 0) = 0 from by simp [hz], sub_zero]
      obtain ⟨i, hi⟩ := hmem z hz
      have h1 : ‖g z‖ ≤ ‖profInt ψ (W : ℝ) (intVec z)‖ := Complex.abs_re_le_norm _
      have h2 : ‖profInt ψ (W : ℝ) (intVec z)‖ =
          ((W : ℝ) ^ d)⁻¹ * ‖Φ ((W : ℝ)⁻¹ • intVec z)‖ := by
        rw [profInt_scale d ψ (W : ℝ) hW0, hΦ, norm_mul, norm_inv, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg hW0.le]
      have h3 := hC ((W : ℝ)⁻¹) ((L : ℝ) / 2) (inv_pos.mpr hW0) (by positivity) z ⟨i, hi⟩
      calc ‖g z‖ ≤ ((W : ℝ) ^ d)⁻¹ * ‖Φ ((W : ℝ)⁻¹ • intVec z)‖ := h2 ▸ h1
        _ ≤ ((W : ℝ) ^ d)⁻¹ * (C * ρ * ∏ i, ((1 + (W : ℝ)⁻¹ * |(z i : ℝ)|) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr (pow_nonneg hW0.le d))
        _ = _ := by ring)
  rw [min_eq_right (inv_le_one_of_one_le₀ hW1)] at hbd
  refine hbd.trans (le_of_eq ?_)
  have hρ' : ρ = ((1 + (L : ℝ) / (2 * W)) ^ N)⁻¹ := by
    rw [hρ]; congr 3; field_simp
  rw [hρ']
  have hKW : ((W : ℝ) ^ d)⁻¹ * (((W : ℝ)⁻¹ ^ 2)⁻¹ * Kc) ^ d = Kc ^ d * (W : ℝ) ^ d := by
    rw [inv_pow, inv_inv, mul_pow, ← pow_mul, two_mul, pow_add]
    field_simp
  calc ((W : ℝ) ^ d)⁻¹ * (C * ((1 + (L : ℝ) / (2 * W)) ^ N)⁻¹) * (((W : ℝ)⁻¹ ^ 2)⁻¹ * Kc) ^ d
      = C * ((1 + (L : ℝ) / (2 * W)) ^ N)⁻¹ *
        (((W : ℝ) ^ d)⁻¹ * (((W : ℝ)⁻¹ ^ 2)⁻¹ * Kc) ^ d) := by ring
    _ = C * ((1 + (L : ℝ) / (2 * W)) ^ N)⁻¹ * (Kc ^ d * (W : ℝ) ^ d) := by rw [hKW]
    _ = C * Kc ^ d * (W : ℝ) ^ d * ((1 + (L : ℝ) / (2 * W)) ^ N)⁻¹ := by ring

/-- For `L ≥ W^{1+ε}` and `D + d ≤ εN`: `W^d (1 + L/(2W))^{−N} ≤ 2^N W^{−D}`. -/
private theorem rho_le (d D N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : (D : ℝ) + d ≤ ε * N) (W L : ℝ)
    (hW : 1 ≤ W) (hWL : W ^ (1 + ε) ≤ L) :
    W ^ d * ((1 + L / (2 * W)) ^ N)⁻¹ ≤ 2 ^ N / W ^ D := by
  have hW0 : 0 < W := by linarith
  have h1 : W ^ ε / 2 ≤ L / (2 * W) := by
    rw [le_div_iff₀ (by positivity)]
    calc W ^ ε / 2 * (2 * W) = W ^ (1 + ε) := by
          rw [Real.rpow_add hW0, Real.rpow_one]; ring
      _ ≤ L := hWL
  have hpos : 0 < W ^ ε / 2 := by positivity
  have h2 : (W ^ ε / 2) ^ N ≤ (1 + L / (2 * W)) ^ N :=
    pow_le_pow_left₀ hpos.le (by linarith) N
  have h3 : W ^ (D + d) ≤ (W ^ ε) ^ N := by
    rw [← Real.rpow_natCast (W ^ ε) N, ← Real.rpow_mul hW0.le, ← Real.rpow_natCast W (D + d)]
    exact Real.rpow_le_rpow_of_exponent_le hW (by push_cast; linarith)
  have h4 : 0 < (W ^ ε) ^ N := by positivity
  calc W ^ d * ((1 + L / (2 * W)) ^ N)⁻¹ ≤ W ^ d * ((W ^ ε / 2) ^ N)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hpos N) h2) (by positivity)
    _ = W ^ d * (2 ^ N / (W ^ ε) ^ N) := by rw [div_pow, inv_div]
    _ ≤ W ^ d * (2 ^ N / W ^ (D + d)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) h3)
          (by positivity)
    _ = 2 ^ N / W ^ D := by rw [pow_add]; field_simp

/-- On `adm(c₀, c₁)` with `c₀ > 0`: `W ≥ 1` and `W^{1+ε} ≤ L` for `ε = c₀/(1 − c₀)` (or `1`). -/
private theorem adm_exponent (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ W L : ℕ, 1 ≤ L → (W, L) ∈ adm c₀ c₁ → 1 ≤ W ∧ (W : ℝ) ^ (1 + ε) ≤ L := by
  have hW1 : ∀ W L : ℕ, 1 ≤ L → (W, L) ∈ adm c₀ c₁ → 1 ≤ W := by
    intro W L hL hm
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    have h : (0 : ℝ) < W := lt_of_lt_of_le (Real.rpow_pos_of_pos hL' c₁) hm.1
    exact Nat.succ_le_of_lt (by exact_mod_cast h)
  by_cases hc : c₀ < 1
  · have hc1 : 0 < 1 - c₀ := by linarith
    refine ⟨c₀ / (1 - c₀), div_pos hc₀ hc1, fun W L hL hm => ⟨hW1 W L hL hm, ?_⟩⟩
    have hexp : 1 + c₀ / (1 - c₀) = (1 - c₀)⁻¹ := by field_simp; ring
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    calc (W : ℝ) ^ (1 + c₀ / (1 - c₀)) ≤ ((L : ℝ) ^ (1 - c₀)) ^ (1 + c₀ / (1 - c₀)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg W) hm.2 (by rw [hexp]; positivity)
      _ = L := by
          rw [← Real.rpow_mul hL0, hexp, mul_inv_cancel₀ hc1.ne', Real.rpow_one]
  · refine ⟨1, one_pos, fun W L hL hm => ⟨hW1 W L hL hm, ?_⟩⟩
    have h2 : (W : ℝ) ≤ 1 :=
      hm.2.trans (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hL) (by linarith))
    have hWe : W = 1 := le_antisymm (by exact_mod_cast h2) (hW1 W L hL hm)
    subst hWe
    simpa using (by exact_mod_cast hL : (1 : ℝ) ≤ L)

end Aux

/-- [I, (1.10)]: `|Z_{W,L} − 1| ≤ C_D W^{−D}` for `W ≥ 1`, `L ≥ W^{1+ε}`, for every Schwartz
`ψ` with `ψ(0) = 1`. The proof applies Poisson summation to the series `Σ_{z∈ℤ^d} Re φ_W(z)`,
whose value is `Σ_{j∈ℤ^d} ψ(2πWj) = 1 + O(W^{−D})`; `Z_{W,L}` is the part of that series over
`Z_L^d`, and the rest is `O(W^{−D})` because `L ≥ W^{1+ε}`. -/
theorem ZWL_close :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (h0 : ψ 0 = 1) (ε : ℝ) (hε : 0 < ε) (D : ℕ),
    ∃ C : ℝ, ∀ (W L : ℕ) [NeZero L], 1 ≤ W → (W : ℝ) ^ (1 + ε) ≤ L →
      |ZWL ψ W L - 1| ≤ C / (W : ℝ) ^ D := by
  intro d ψ h0 ε hε D
  obtain ⟨CA, hCA0, hA⟩ := close_A ψ h0 D
  obtain ⟨CB, hCB0, hB⟩ := close_B ψ ⌈((D : ℝ) + d) / ε⌉₊
  refine ⟨CA + CB * 2 ^ ⌈((D : ℝ) + d) / ε⌉₊, fun W L _ hW hWL => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hN : (D : ℝ) + d ≤ ε * ⌈((D : ℝ) + d) / ε⌉₊ := by
    have := Nat.le_ceil (((D : ℝ) + d) / ε)
    rwa [div_le_iff₀ hε, mul_comm] at this
  have h1 := hA (W : ℝ) hW1
  have h2 := hB W L hW
  have h3 := rho_le d D _ ε hε hN (W : ℝ) (L : ℝ) hW1 hWL
  set S := ∑' j : Fin d → ℤ, ψ ((W : ℝ) • ((2 * Real.pi) • intVec j)) with hS
  have h4 : |ZWL ψ W L - 1| ≤ |S - 1| + |S - ZWL ψ W L| := by
    have := abs_sub (S - 1) (S - ZWL ψ W L)
    rwa [show S - 1 - (S - ZWL ψ W L) = ZWL ψ W L - 1 by ring] at this
  have h5 : CB * (W : ℝ) ^ d * ((1 + (L : ℝ) / (2 * W)) ^ ⌈((D : ℝ) + d) / ε⌉₊)⁻¹ ≤
      CB * (2 ^ ⌈((D : ℝ) + d) / ε⌉₊ / (W : ℝ) ^ D) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h3 hCB0
  calc |ZWL ψ W L - 1| ≤ |S - 1| + |S - ZWL ψ W L| := h4
    _ ≤ CA / (W : ℝ) ^ D + CB * (2 ^ ⌈((D : ℝ) + d) / ε⌉₊ / (W : ℝ) ^ D) :=
        add_le_add h1 (h2.trans h5)
    _ = (CA + CB * 2 ^ ⌈((D : ℝ) + d) / ε⌉₊) / (W : ℝ) ^ D := by ring

/-- [I, (1.10)] on `adm(c₀, c₁)`: `|Z_{W,L} − 1| ≤ C_D W^{−D}`, for `c₀ > 0`. -/
theorem ZWL_close_adm :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (h0 : ψ 0 = 1) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀)
    (D : ℕ), ∃ C : ℝ,
    ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → |ZWL ψ W L - 1| ≤ C / (W : ℝ) ^ D := by
  intro d ψ h0 c₀ c₁ hc₀ D
  obtain ⟨ε, hε, hadm⟩ := adm_exponent c₀ c₁ hc₀
  obtain ⟨C, hC⟩ := ZWL_close d ψ h0 ε hε D
  refine ⟨C, fun W L _ hm => ?_⟩
  obtain ⟨h1, h2⟩ := hadm W L (Nat.pos_of_ne_zero (NeZero.ne L)) hm
  exact hC W L h1 h2

/-- `Z_{W,L} ≥ 1/2` on `adm(c₀, c₁)` for `W ≥ W₀`, from [I, (1.10)] with `D = 1`. -/
theorem ZWL_half_adm :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (h0 : ψ 0 = 1) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀),
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → 1 / 2 ≤ ZWL ψ W L := by
  intro d ψ h0 c₀ c₁ hc₀
  obtain ⟨C, hC⟩ := ZWL_close_adm d ψ h0 c₀ c₁ hc₀ 1
  refine ⟨max 1 (2 * C), fun W L _ hm hW => ?_⟩
  have h1 := hC W L hm
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : 2 * C ≤ W := le_trans (le_max_right _ _) hW
  have hWpos : (0 : ℝ) < W := by linarith
  rw [pow_one] at h1
  have h5 : C / W ≤ 1 / 2 := by rw [div_le_iff₀ hWpos]; linarith
  have h6 := abs_le.mp (h1.trans h5)
  linarith [h6.1]

section Witness

end Witness

end RBM8D
