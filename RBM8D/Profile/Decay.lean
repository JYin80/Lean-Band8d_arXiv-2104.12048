module

public import RBM8D.Profile.Norm
public import RBM8D.Profile.Density

@[expose] public section

/-!
# [I, (1.8)]–[I, (1.10)]

Sub-polynomial decay, band structure, symmetry, nonnegativity and double stochasticity of `S_{W,L}`.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

namespace RBM8D

section Aux

variable {d : ℕ}

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

/-- The periodic `ℓ^∞` distance of `x` is at most the Euclidean norm of its representative. -/
private theorem zdistInf_le_norm_zrep {L : ℕ} [NeZero L] (x : Zd d L) :
    (zdistInf d L x : ℝ) ≤ ‖zrep x‖ := by
  have hi : ∀ i : Fin d, (zdist L (x i) : ℝ) ≤ ‖zrep x‖ := by
    intro i
    have h1 : |(zrep x) i| ≤ ‖zrep x‖ := by simpa using PiLp.norm_apply_le (zrep x) i
    have h2 : (zdist L (x i) : ℝ) = |(zrep x) i| := by
      rw [zdist_eq_natAbs_valMinAbs]
      simp [zrep]
    rw [h2]; exact h1
  rcases (Finset.univ : Finset (Fin d)).eq_empty_or_nonempty with h | h
  · have : zdistInf d L x = 0 := by simp [zdistInf, h]
    rw [this]; simp
  · obtain ⟨i, _, hi'⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) h
      (fun i => zdist L (x i))
    have : zdistInf d L x = zdist L (x i) := hi'
    rw [this]; exact hi i

/-- `f_{W,L}` before normalisation is `W^{−d} φ([x]_L / W)` ([I, (1.6)]). -/
private theorem fRaw_eq (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) (hW : 1 ≤ W)
    (x : Zd d L) :
    fRaw ψ W L x = ((W : ℝ) ^ d)⁻¹ * profPhi ψ ((W : ℝ)⁻¹ • zrep x) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [fRaw, profInt_scale d ψ (W : ℝ) hW' (zrep x), profPhi]
  have h : (((W : ℝ) : ℂ) ^ d)⁻¹ = ((((W : ℝ) ^ d)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.re_ofReal_mul]

/-- Schwartz decay of the density: `sup_y ‖y‖^k |φ(y)| < ∞`. -/
private theorem profPhi_decay (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ^ k * |profPhi ψ y| ≤ M := by
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
  have hG : ∀ y, profInt ψ 1 y = ((𝓕⁻ G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : _ → ℂ) y := by
    intro y
    rw [hprof, ← SchwartzMap.fourierInv_coe]
  refine ⟨SchwartzMap.seminorm ℝ k 0 (𝓕⁻ G), apply_nonneg _ _, fun y => ?_⟩
  have h1 := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕⁻ G) k y
  refine le_trans ?_ h1
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← hG y]
  exact Complex.abs_re_le_norm _

/-- The normaliser `Z_{W,L}` is nondecreasing in `L`, when `φ ≥ 0`. -/
private theorem ZWL_mono (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) (hW : 1 ≤ W)
    (hφ : ∀ y, 0 ≤ profPhi ψ y) {L L' : ℕ} [NeZero L] [NeZero L'] (h : L ≤ L') :
    ZWL ψ W L ≤ ZWL ψ W L' := by
  classical
  let ι : Zd d L → Zd d L' := fun x i => (((x i).valMinAbs : ℤ) : ZMod L')
  have hζ : ∀ (x : Zd d L) (i : Fin d), ((ι x) i).valMinAbs = (x i).valMinAbs := by
    intro x i
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    have := ZMod.valMinAbs_mem_Ioc (x i)
    have hLL : (L : ℤ) ≤ L' := by exact_mod_cast h
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hz : ∀ x : Zd d L, zrep (ι x) = zrep x := by
    intro x
    ext i
    simp [zrep, hζ]
  have hinj : Function.Injective ι := by
    intro x y hxy
    funext i
    have h1 : (ι x) i = (ι y) i := congrFun hxy i
    have h2 := congrArg ZMod.valMinAbs h1
    rw [hζ, hζ] at h2
    exact ZMod.injective_valMinAbs h2
  have hnn : ∀ x : Zd d L', 0 ≤ fRaw ψ W L' x := by
    intro x
    rw [fRaw_eq ψ W L' hW x]
    exact mul_nonneg (by positivity) (hφ _)
  have hfe : ∀ x : Zd d L, fRaw ψ W L x = fRaw ψ W L' (ι x) := by
    intro x
    simp only [fRaw, hz]
  calc ZWL ψ W L = ∑ x : Zd d L, fRaw ψ W L' (ι x) := Finset.sum_congr rfl fun x _ => hfe x
    _ = ∑ x' ∈ Finset.univ.image ι, fRaw ψ W L' x' := by
        rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    _ ≤ ∑ x' : Zd d L', fRaw ψ W L' x' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => hnn x
    _ = ZWL ψ W L' := rfl

/-- `(‖x‖_L/W)^k f_{W,L}(x)` before normalisation is at most `M_k W^{−d}`. -/
private theorem raw_bound (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (k : ℕ) (M : ℝ)
    (hM : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ^ k * |profPhi ψ y| ≤ M) (W L : ℕ) [NeZero L]
    (hW : 1 ≤ W) (x : Zd d L) :
    ((zdistInf d L x : ℝ) / W) ^ k * |fRaw ψ W L x| ≤ M / (W : ℝ) ^ d := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  rw [fRaw_eq ψ W L hW x, abs_mul, abs_of_pos (inv_pos.mpr hWd)]
  have h1 : (zdistInf d L x : ℝ) / W ≤ ‖(W : ℝ)⁻¹ • zrep x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hW'.le), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (zdistInf_le_norm_zrep x) hW'.le
  have h2 : ((zdistInf d L x : ℝ) / W) ^ k ≤ ‖(W : ℝ)⁻¹ • zrep x‖ ^ k :=
    pow_le_pow_left₀ (by positivity) h1 k
  calc ((zdistInf d L x : ℝ) / W) ^ k * (((W : ℝ) ^ d)⁻¹ * |profPhi ψ ((W : ℝ)⁻¹ • zrep x)|)
      = ((W : ℝ) ^ d)⁻¹ * (((zdistInf d L x : ℝ) / W) ^ k * |profPhi ψ ((W : ℝ)⁻¹ • zrep x)|) := by
        ring
    _ ≤ ((W : ℝ) ^ d)⁻¹ * (‖(W : ℝ)⁻¹ • zrep x‖ ^ k * |profPhi ψ ((W : ℝ)⁻¹ • zrep x)|) := by
        gcongr
    _ ≤ ((W : ℝ) ^ d)⁻¹ * M := by
        gcongr
        exact hM _
    _ = M / (W : ℝ) ^ d := by rw [inv_mul_eq_div]

/-- For fixed `W ≥ 1`, the values `Z_{W,L}` with `L ≥ W^{1+ε}` are either `0` or bounded below by
a positive constant, because `L ↦ Z_{W,L}` is nondecreasing. -/
private theorem ZWL_lower (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) (hW : 1 ≤ W)
    (hφ : ∀ y, 0 ≤ profPhi ψ y) (ε : ℝ) :
    ∃ z : ℝ, 0 < z ∧ ∀ (L : ℕ) [NeZero L], (W : ℝ) ^ (1 + ε) ≤ L →
      ZWL ψ W L = 0 ∨ z ≤ ZWL ψ W L := by
  classical
  have hZnn : ∀ (L : ℕ) [NeZero L], 0 ≤ ZWL ψ W L := by
    intro L _
    refine Finset.sum_nonneg fun x _ => ?_
    rw [fRaw_eq ψ W L hW x]
    exact mul_nonneg (by positivity) (hφ _)
  by_cases hex : ∃ L : ℕ, ∃ _ : NeZero L, (W : ℝ) ^ (1 + ε) ≤ L ∧ 0 < ZWL ψ W L
  · obtain ⟨hL, hQ, hz⟩ := Nat.find_spec hex
    refine ⟨ZWL ψ W (Nat.find hex), hz, fun L _ hQL => ?_⟩
    rcases (hZnn L).eq_or_lt with h0 | hpos
    · exact Or.inl h0.symm
    · right
      have hmin : Nat.find hex ≤ L := Nat.find_min' hex ⟨inferInstance, hQL, hpos⟩
      exact ZWL_mono ψ W hW hφ hmin
  · refine ⟨1, one_pos, fun L _ hQL => Or.inl ?_⟩
    exact le_antisymm (not_lt.mp fun hlt => hex ⟨L, inferInstance, hQL, hlt⟩) (hZnn L)

/-- If `Z_{W,L} ≥ z > 0` the normalised bound follows from the unnormalised one. -/
private theorem norm_bound_of_lower (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (k : ℕ) (M : ℝ)
    (hM : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ^ k * |profPhi ψ y| ≤ M) (W L : ℕ) [NeZero L]
    (hW : 1 ≤ W) (hφ : ∀ y, 0 ≤ profPhi ψ y) (z : ℝ) (hz : 0 < z) (hZ : z ≤ ZWL ψ W L)
    (x : Zd d L) :
    ((zdistInf d L x : ℝ) / W) ^ k * |fWL ψ W L x| ≤ (M / z) / (W : ℝ) ^ d := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have hZpos : 0 < ZWL ψ W L := lt_of_lt_of_le hz hZ
  have h1 := raw_bound ψ k M hM W L hW x
  have hinv : (ZWL ψ W L)⁻¹ ≤ z⁻¹ := inv_anti₀ hz hZ
  have hz0 : 0 ≤ (((zdistInf d L x : ℝ) / W) ^ k * |fRaw ψ W L x|) := by positivity
  calc ((zdistInf d L x : ℝ) / W) ^ k * |fWL ψ W L x|
      = (ZWL ψ W L)⁻¹ * (((zdistInf d L x : ℝ) / W) ^ k * |fRaw ψ W L x|) := by
        rw [fWL, abs_mul, abs_of_pos (inv_pos.mpr hZpos)]; ring
    _ ≤ z⁻¹ * (M / (W : ℝ) ^ d) := mul_le_mul hinv h1 hz0 (inv_nonneg.mpr hz.le)
    _ = (M / z) / (W : ℝ) ^ d := by field_simp

/-- For fixed `W ≥ 1`, the bound `(‖x‖_L/W)^k |f_{W,L}(x)| ≤ c W^{−d}` holds for all `L ≥ W^{1+ε}`
with a constant `c` depending on `W`. -/
private theorem subpoly_fixed (P : Profile d) (ε : ℝ) (k : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ^ k * |profPhi P.ψ y| ≤ M) (W : ℕ) (hW : 1 ≤ W)
    (hφ : ∀ y, 0 ≤ profPhi P.ψ y) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (L : ℕ) [NeZero L], (W : ℝ) ^ (1 + ε) ≤ L → ∀ x : Zd d L,
      ((zdistInf d L x : ℝ) / W) ^ k * |fWL P.ψ W L x| ≤ c / (W : ℝ) ^ d := by
  obtain ⟨z, hz, hlow⟩ := ZWL_lower P.ψ W hW hφ ε
  refine ⟨M / z, div_nonneg hM0 hz.le, fun L _ hQ x => ?_⟩
  rcases hlow L hQ with h0 | hZ
  · have : fWL P.ψ W L x = 0 := by simp [fWL, h0]
    rw [this, abs_zero, mul_zero]
    positivity
  · exact norm_bound_of_lower P.ψ k M hM W L hW hφ z hz hZ x

/-- `S_{xy} = f(x − y)` is doubly stochastic when `f ≥ 0` and `Σ_x f(x) = 1`. -/
private theorem Smat_mem_doublyStochastic (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ)
    [NeZero L] (hnn : ∀ x : Zd d L, 0 ≤ fWL ψ W L x) (hsum : ∑ x : Zd d L, fWL ψ W L x = 1) :
    Smat ψ W L ∈ doublyStochastic ℝ (Zd d L) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun x y => hnn _, fun x => ?_, fun y => ?_⟩
  · simp only [Smat, Matrix.of_apply]
    rw [← hsum]
    exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)
  · simp only [Smat, Matrix.of_apply]
    rw [← hsum]
    exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)

/-- `S_{xy} = f(x − y)` is symmetric when `f(−x) = f(x)`. -/
private theorem Smat_isSymm_of_neg (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) [NeZero L]
    (hsymm : ∀ x : Zd d L, fWL ψ W L (-x) = fWL ψ W L x) : (Smat ψ W L).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, Smat, Matrix.of_apply]
  rw [← neg_sub x y]
  exact hsymm (x - y)

end Aux

/-- [I, (1.8)], sub-polynomial decay of `f_{W,L}` for `L ≥ W^{1+ε}`: for every `k`,
`(‖x‖_L/W)^k |f_{W,L}(x)| ≤ C_k W^{−d}` with `C_k` independent of `W ≥ 1` and `L`. -/
theorem subpoly :
  ∀ (d : ℕ) (P : Profile d) (ε : ℝ) (hε : 0 < ε) (k : ℕ), ∃ C : ℝ,
    ∀ (W L : ℕ) [NeZero L], 1 ≤ W → (W : ℝ) ^ (1 + ε) ≤ L → ∀ x : Zd d L,
      ((zdistInf d L x : ℝ) / W) ^ k * |fWL P.ψ W L x| ≤ C / (W : ℝ) ^ d := by
  intro d P ε hε k
  have hφ : ∀ y, 0 ≤ profPhi P.ψ y := (profPhi_prob d P).1
  obtain ⟨M, hM0, hM⟩ := profPhi_decay P.ψ k
  obtain ⟨C₁, hC₁⟩ := ZWL_close d P.ψ P.at_zero ε hε 1
  have key : ∀ W : ℕ, ∃ c : ℝ, 0 ≤ c ∧ (1 ≤ W → ∀ (L : ℕ) [NeZero L], (W : ℝ) ^ (1 + ε) ≤ L →
      ∀ x : Zd d L, ((zdistInf d L x : ℝ) / W) ^ k * |fWL P.ψ W L x| ≤ c / (W : ℝ) ^ d) := by
    intro W
    by_cases hW : 1 ≤ W
    · obtain ⟨c, hc0, hc⟩ := subpoly_fixed P ε k M hM0 hM W hW hφ
      exact ⟨c, hc0, fun _ => hc⟩
    · exact ⟨0, le_rfl, fun h => absurd h hW⟩
  choose c hc0 hc using key
  refine ⟨2 * M + ∑ W ∈ Finset.range (⌈max 1 (2 * C₁)⌉₊ + 1), c W, fun W L _ hW hQ x => ?_⟩
  have hWpos : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  have hsum0 : 0 ≤ ∑ W ∈ Finset.range (⌈max 1 (2 * C₁)⌉₊ + 1), c W :=
    Finset.sum_nonneg fun W _ => hc0 W
  by_cases hbig : max 1 (2 * C₁) ≤ (W : ℝ)
  · -- large `W`: `Z_{W,L} ≥ 1/2`
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have hW2 : 2 * C₁ ≤ W := le_trans (le_max_right _ _) hbig
    have hWp : (0 : ℝ) < W := by linarith
    have h1 := hC₁ W L hW hQ
    rw [pow_one] at h1
    have h5 : C₁ / W ≤ 1 / 2 := by rw [div_le_iff₀ hWp]; linarith
    have h6 := abs_le.mp (h1.trans h5)
    have hZ : (1 / 2 : ℝ) ≤ ZWL P.ψ W L := by linarith [h6.1]
    have := norm_bound_of_lower P.ψ k M hM W L hW hφ (1 / 2) (by norm_num) hZ x
    refine this.trans ?_
    rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hWpos]
    linarith
  · have hlt : (W : ℝ) < max 1 (2 * C₁) := not_le.mp hbig
    have hWn : W ≤ ⌈max 1 (2 * C₁)⌉₊ := by
      have := Nat.le_ceil (max 1 (2 * C₁))
      exact_mod_cast (hlt.le.trans this)
    have hmem : W ∈ Finset.range (⌈max 1 (2 * C₁)⌉₊ + 1) := Finset.mem_range.mpr (by omega)
    have hcle : c W ≤ ∑ W ∈ Finset.range (⌈max 1 (2 * C₁)⌉₊ + 1), c W :=
      Finset.single_le_sum (fun i _ => hc0 i) hmem
    refine (hc W hW L hQ x).trans ?_
    exact div_le_div_of_nonneg_right (by linarith) hWpos.le

/-- [I, (1.8)] on `adm(c₀, c₁)` with `c₀ > 0`: `(‖x‖_L/W)^k |f_{W,L}(x)| ≤ C_k W^{−d}`
uniformly on the window. -/
theorem subpoly_adm :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (k : ℕ), ∃ C : ℝ,
    ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → ∀ x : Zd d L,
      ((zdistInf d L x : ℝ) / W) ^ k * |fWL P.ψ W L x| ≤ C / (W : ℝ) ^ d := by
  intro d P c₀ c₁ hc₀ k
  obtain ⟨ε, hε, hadm⟩ := adm_exponent c₀ c₁ hc₀
  obtain ⟨C, hC⟩ := subpoly d P ε hε k
  refine ⟨C, fun W L _ hm x => ?_⟩
  obtain ⟨h1, h2⟩ := hadm W L (Nat.pos_of_ne_zero (NeZero.ne L)) hm
  exact hC W L h1 h2 x

/-- [I, (1.9)], band structure of `S`: for `L ≥ W^{1+ε}` and `W ≥ W₀`, the entries with
`‖x − y‖_L ≥ W^{1+τ}` satisfy `|S_{xy}| ≤ W^{−D}`. -/
theorem banded :
  ∀ (d : ℕ) (P : Profile d) (ε τ D : ℝ) (hε : 0 < ε) (hτ : 0 < τ) (hD : 0 < D), ∃ W₀ : ℝ,
    ∀ (W L : ℕ) [NeZero L], W₀ ≤ W → (W : ℝ) ^ (1 + ε) ≤ L → ∀ x y : Zd d L,
      (W : ℝ) ^ (1 + τ) ≤ zdistInf d L (x - y) → |Smat P.ψ W L x y| ≤ (W : ℝ) ^ (-D) := by
  intro d P ε τ D hε hτ hD
  obtain ⟨C, hC⟩ := subpoly d P ε hε (⌈D / τ⌉₊ + 1)
  set k : ℕ := ⌈D / τ⌉₊ + 1 with hk
  set C' : ℝ := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' := by linarith
  refine ⟨C' ^ (1 / τ), fun W L _ hW0 hQ x y hxy => ?_⟩
  have hW0' : (1 : ℝ) ≤ C' ^ (1 / τ) := Real.one_le_rpow hC'1 (by positivity)
  have hW1 : (1 : ℝ) ≤ W := hW0'.trans hW0
  have hWpos : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  -- `C' ≤ W^τ`
  have hCW : C' ≤ (W : ℝ) ^ τ := by
    calc C' = (C' ^ (1 / τ)) ^ τ := by
          rw [← Real.rpow_mul hC'pos.le, one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ τ := Real.rpow_le_rpow (by positivity) hW0 hτ.le
  set r : ℝ := (zdistInf d L (x - y) : ℝ) with hr
  have hWτ : (W : ℝ) ^ τ ≤ r / W := by
    rw [le_div_iff₀ hWpos]
    calc (W : ℝ) ^ τ * W = (W : ℝ) ^ (1 + τ) := by
          rw [Real.rpow_add hWpos, Real.rpow_one, mul_comm]
      _ ≤ r := hxy
  have h1 := hC W L hWn hQ (x - y)
  have h2 : ((W : ℝ) ^ τ) ^ k * |fWL P.ψ W L (x - y)| ≤ C' / (W : ℝ) ^ d := by
    refine le_trans ?_ (h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hWτ k) (abs_nonneg _)
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have ha : (0 : ℝ) < ((W : ℝ) ^ τ) ^ k := by positivity
  -- the exponent
  have hkτ : D + τ ≤ τ * k := by
    have h3 : D / τ ≤ ⌈D / τ⌉₊ := Nat.le_ceil _
    have h4 : D ≤ τ * ⌈D / τ⌉₊ := by
      have := mul_le_mul_of_nonneg_left h3 hτ.le
      rwa [mul_div_cancel₀ _ hτ.ne'] at this
    rw [hk]; push_cast; nlinarith
  have hpow : (W : ℝ) ^ (-D) * ((W : ℝ) ^ d * ((W : ℝ) ^ τ) ^ k) =
      (W : ℝ) ^ (-D + d + τ * k) := by
    rw [← Real.rpow_natCast (W : ℝ) d, ← Real.rpow_natCast ((W : ℝ) ^ τ) k,
      ← Real.rpow_mul hWpos.le, ← Real.rpow_add hWpos, ← Real.rpow_add hWpos]
    congr 1
    ring
  have hexp : (W : ℝ) ^ τ ≤ (W : ℝ) ^ (-D + d + τ * k) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  have hmain : |fWL P.ψ W L (x - y)| * ((W : ℝ) ^ d * ((W : ℝ) ^ τ) ^ k) ≤ C' := by
    have h3 := (le_div_iff₀ hWd).mp h2
    calc |fWL P.ψ W L (x - y)| * ((W : ℝ) ^ d * ((W : ℝ) ^ τ) ^ k)
        = ((W : ℝ) ^ τ) ^ k * |fWL P.ψ W L (x - y)| * (W : ℝ) ^ d := by ring
      _ ≤ C' := h3
  change |fWL P.ψ W L (x - y)| ≤ (W : ℝ) ^ (-D)
  have hcpos : 0 < (W : ℝ) ^ d * ((W : ℝ) ^ τ) ^ k := by positivity
  refine le_of_mul_le_mul_right ?_ hcpos
  exact (hmain.trans (hCW.trans hexp)).trans_eq hpow.symm

/-- [I, Assumption 1.1]: on `adm(c₀, c₁)` for `W ≥ W₀`, the matrix `S_{xy} = f_{W,L}(x − y)`
is symmetric and has nonnegative entries. -/
theorem Smat_symm_nonneg :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁), ∃ W₀ : ℝ,
    ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      (Smat P.ψ W L).IsSymm ∧ ∀ x y, 0 ≤ Smat P.ψ W L x y := by
  intro d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₀, hW₀⟩ := P.f_symm c₀ c₁ hc₀ hc₁
  obtain ⟨ε, hε, hadm⟩ := adm_exponent c₀ c₁ hc₀
  refine ⟨W₀, fun W L _ hm hW => ?_⟩
  have hW1 : 1 ≤ W := (hadm W L (Nat.pos_of_ne_zero (NeZero.ne L)) hm).1
  have hsymm := hW₀ W L hm (by exact_mod_cast hW)
  exact ⟨Smat_isSymm_of_neg P.ψ W L hsymm, fun x y => P.f_nonneg W L hW1 _⟩

/-- [I, Assumption 1.1]: on `adm(c₀, c₁)` for `W ≥ W₀`, the matrix `S_{xy} = f_{W,L}(x − y)` is
doubly stochastic, since `Z_{W,L} ≥ 1/2` there ([I, (1.10)]). -/
theorem Smat_doublyStochastic_adm :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀), ∃ W₀ : ℝ,
    ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      Smat P.ψ W L ∈ doublyStochastic ℝ (Zd d L) := by
  intro d P c₀ c₁ hc₀
  obtain ⟨W₀, hW₀⟩ := ZWL_half_adm d P.ψ P.at_zero c₀ c₁ hc₀
  obtain ⟨ε, hε, hadm⟩ := adm_exponent c₀ c₁ hc₀
  refine ⟨W₀, fun W L _ hm hW => ?_⟩
  have hW1 : 1 ≤ W := (hadm W L (Nat.pos_of_ne_zero (NeZero.ne L)) hm).1
  have hZ : ZWL P.ψ W L ≠ 0 := by
    have := hW₀ W L hm hW
    intro h
    rw [h] at this
    norm_num at this
  exact Smat_mem_doublyStochastic P.ψ W L (P.f_nonneg W L hW1) (sum_fWL d L P.ψ W hZ)


section Witness

end Witness

end RBM8D
