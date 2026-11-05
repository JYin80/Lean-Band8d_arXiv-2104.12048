import RBM8D.Profile.Poisson
import RBM8D.Profile.Norm
import RBM8D.Profile.Density
import RBM8D.Profile.Decay
import RBM8D.Kernel.PropagatorSymbol

/-!
# The symbol hypothesis of [I, Lemma 2.2] for `S_{W,L}`

The symbol of `S_{W,L}`, translation invariance, `IsSymKernel`, `IsVarKernel`, (H3) on `adm`, and the discharge of the hypotheses of the G3 statements.
-/

noncomputable section

set_option linter.unusedVariables false

open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

namespace RBM8D

section Aux

variable {d : ℕ}

/-- `e^{i p·(−x)} = conj e^{i p·x}` for the characters of `Z_L^d`. -/
private theorem zchar_neg_eq_conj {L : ℕ} [NeZero L] (k x : Zd d L) :
    zchar k (-x) = (starRingEnd ℂ) (zchar k x) := by
  have h0 : zchar k 0 = 1 := by simp [zchar]
  have h1 : zchar k x * zchar k (-x) = 1 := by
    rw [← zchar_add, add_neg_cancel, h0]
  have h2 : (starRingEnd ℂ) (zchar k x) * zchar k x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_zchar]
    simp
  have hne : zchar k x ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  exact mul_left_cancel₀ hne (h1.trans (by rw [mul_comm]; exact h2.symm))

/-- On `adm(c₀, c₁)` with `L ≥ 1`: `W ≥ 1`, since `W ≥ L^{c₁} > 0`. -/
private theorem adm_one_le (c₀ c₁ : ℝ) (W L : ℕ) (hL : 1 ≤ L) (hm : (W, L) ∈ adm c₀ c₁) :
    1 ≤ W := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have h : (0 : ℝ) < W := lt_of_lt_of_le (Real.rpow_pos_of_pos hL' c₁) hm.1
  exact Nat.succ_le_of_lt (by exact_mod_cast h)

/-- The centred frequency `p = 2πk/L` lies in `[−π, π]^d`. -/
private theorem abs_zfreq_le {L : ℕ} [NeZero L] (k : Zd d L) (i : Fin d) :
    |zfreq k i| ≤ Real.pi := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hm := ZMod.valMinAbs_mem_Ioc (k i)
  have h1 : (-(L : ℝ)) < ((k i).valMinAbs : ℝ) * 2 := by exact_mod_cast hm.1
  have h2 : ((k i).valMinAbs : ℝ) * 2 ≤ L := by exact_mod_cast hm.2
  have hv : |((k i).valMinAbs : ℝ)| ≤ L / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : zfreq k i = 2 * Real.pi * ((k i).valMinAbs : ℝ) / L := rfl
  rw [he, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    abs_of_pos hL, div_le_iff₀ hL]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  calc 2 * Real.pi * |((k i).valMinAbs : ℝ)| ≤ 2 * Real.pi * (L / 2) :=
        mul_le_mul_of_nonneg_left hv hpi
    _ = Real.pi * L := by ring

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

/-- Schwartz decay in product form: `|h(v)| ≤ C ∏ᵢ (1 + |vᵢ|)^{−n}`. -/
private theorem schwartz_prod_decay (h : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (n : ℕ) :
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

/-- `|p + 2πj| ≥ π|j|` for `|p| ≤ π` and `j ∈ ℤ`. -/
private theorem abs_add_two_pi_mul (t : ℝ) (ht : |t| ≤ Real.pi) (j : ℤ) :
    Real.pi * |(j : ℝ)| ≤ |t + 2 * Real.pi * j| := by
  rcases eq_or_ne j 0 with hj | hj
  · subst hj; simp
  · have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
      have : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
      exact_mod_cast this
    have h1 : |2 * Real.pi * (j : ℝ)| - |t| ≤ |t + 2 * Real.pi * j| := by
      have := abs_sub_abs_le_abs_sub (2 * Real.pi * (j : ℝ)) (-t)
      rwa [abs_neg, sub_neg_eq_add, add_comm] at this
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
    nlinarith [Real.pi_pos]

/-- The aliasing term `E₁(p) = Σ_{j≠0} ψ(W(p + 2πj))`: `|E₁(p)| ≤ C W^{−D}` for `W ≥ 1` and
`p ∈ [−π, π]^d`. -/
private theorem alias_bound (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (D : ℕ) :
    ∃ C : ℝ, ∀ W : ℝ, 1 ≤ W → ∀ p : EuclideanSpace ℝ (Fin d), (∀ i, |p i| ≤ Real.pi) →
      |(∑' j : Fin d → ℤ, ψ (W • (p + (2 * Real.pi) • intVec j))) - ψ (W • p)| ≤ C / W ^ D := by
  obtain ⟨K, hK0, hK⟩ := schwartz_prod_decay ψ (D + 2)
  set a : ℤ → ℝ := fun k => ((1 + |(k : ℝ)|) ^ 2)⁻¹ with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => inv_nonneg.mpr (sq_nonneg _)
  have hsa : Summable (fun j : Fin d → ℤ => ∏ i, a (j i)) :=
    summable_of_sum_le (c := (∑' k, a k) ^ d) (fun j => Finset.prod_nonneg fun i _ => ha0 _)
      fun u => prod_sum_le a ha0 summable_Kc u
  have hle : ∑' j : Fin d → ℤ, ∏ i, a (j i) ≤ Kc ^ d :=
    Real.tsum_le_of_sum_le (fun j => Finset.prod_nonneg fun i _ => ha0 _)
      fun u => prod_sum_le a ha0 summable_Kc u
  refine ⟨K * Kc ^ d, fun W hW p hp => ?_⟩
  have hW0 : 0 < W := by linarith
  have hWD : 0 < W ^ D := pow_pos hW0 D
  obtain ⟨hs, -⟩ := poisson_profile d ψ W hW0 p
  have hF : HasSum (fun j : Fin d → ℤ =>
      ψ (W • (p + (2 * Real.pi) • intVec j)) - if j = 0 then ψ (W • p) else 0)
      ((∑' j : Fin d → ℤ, ψ (W • (p + (2 * Real.pi) • intVec j))) - ψ (W • p)) :=
    hs.hasSum.sub (hasSum_ite_eq 0 _)
  have hg : HasSum (fun j : Fin d → ℤ => K * (W ^ D)⁻¹ * ∏ i, a (j i))
      (K * (W ^ D)⁻¹ * ∑' j : Fin d → ℤ, ∏ i, a (j i)) := hsa.hasSum.mul_left _
  have hb : ∀ j : Fin d → ℤ, ‖ψ (W • (p + (2 * Real.pi) • intVec j)) -
      (if j = 0 then ψ (W • p) else 0)‖ ≤ K * (W ^ D)⁻¹ * ∏ i, a (j i) := by
    intro j
    have hprod0 : 0 ≤ ∏ i, a (j i) := Finset.prod_nonneg fun i _ => ha0 _
    by_cases hj : j = 0
    · subst hj
      have h00 : intVec (0 : Fin d → ℤ) = 0 := by ext i; simp [intVec]
      rw [h00, smul_zero, add_zero]
      simp only [↓reduceIte, sub_self, norm_zero]
      positivity
    · obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hj
      rw [show (if j = 0 then ψ (W • p) else 0) = 0 from by simp [hj], sub_zero]
      set v := W • (p + (2 * Real.pi) • intVec j) with hv
      have hcoord : ∀ i, |(j i : ℝ)| ≤ |v i| ∧ W * |(j i : ℝ)| ≤ |v i| := by
        intro i
        have hvi : v i = W * (p i + 2 * Real.pi * (j i : ℝ)) := by simp [hv, intVec, mul_add]
        have h1 := abs_add_two_pi_mul (p i) (hp i) (j i)
        rw [hvi, abs_mul, abs_of_pos hW0]
        have hj0 := abs_nonneg (j i : ℝ)
        have e1 : |(j i : ℝ)| ≤ |p i + 2 * Real.pi * (j i : ℝ)| := by
          nlinarith [Real.two_le_pi]
        exact ⟨e1.trans (le_mul_of_one_le_left (abs_nonneg _) hW),
          mul_le_mul_of_nonneg_left e1 hW0.le⟩
      have hi1 : (1 : ℝ) ≤ |(j i0 : ℝ)| := by
        have : (1 : ℤ) ≤ |j i0| := Int.one_le_abs hi0
        exact_mod_cast this
      have hfac : ∀ i, ((1 + |v i|) ^ (D + 2))⁻¹ ≤ a (j i) := by
        intro i
        have h1 : 1 + |(j i : ℝ)| ≤ 1 + |v i| := by linarith [(hcoord i).1]
        have h0 : (1 : ℝ) ≤ 1 + |(j i : ℝ)| := by linarith [abs_nonneg (j i : ℝ)]
        refine inv_anti₀ (by positivity) ?_
        calc (1 + |(j i : ℝ)|) ^ 2 ≤ (1 + |v i|) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
          _ ≤ (1 + |v i|) ^ (D + 2) := pow_le_pow_right₀ (by linarith) (by omega)
      have hfac0 : ((1 + |v i0|) ^ (D + 2))⁻¹ ≤ (W ^ D)⁻¹ * a (j i0) := by
        have h1 : 1 + |(j i0 : ℝ)| ≤ 1 + |v i0| := by linarith [(hcoord i0).1]
        have h2 : W ≤ 1 + |v i0| := by nlinarith [(hcoord i0).2]
        have h0 : (1 : ℝ) ≤ 1 + |(j i0 : ℝ)| := by linarith [abs_nonneg (j i0 : ℝ)]
        rw [← mul_inv]
        refine inv_anti₀ (by positivity) ?_
        rw [pow_add]
        exact mul_le_mul (pow_le_pow_left₀ hW0.le h2 D)
          (pow_le_pow_left₀ (by linarith) h1 2) (by positivity) (by positivity)
      have hprod : ∏ i, ((1 + |v i|) ^ (D + 2))⁻¹ ≤ (W ^ D)⁻¹ * ∏ i, a (j i) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0),
          ← Finset.mul_prod_erase _ (fun i => a (j i)) (Finset.mem_univ i0), ← mul_assoc]
        exact mul_le_mul hfac0
          (Finset.prod_le_prod₀ (fun i _ => inv_nonneg.mpr (by positivity)) fun i _ => hfac i)
          (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by positivity))
          (mul_nonneg (inv_nonneg.mpr hWD.le) (ha0 _))
      calc ‖ψ v‖ ≤ K * ∏ i, ((1 + |v i|) ^ (D + 2))⁻¹ := hK v
        _ ≤ K * ((W ^ D)⁻¹ * ∏ i, a (j i)) := mul_le_mul_of_nonneg_left hprod hK0
        _ = K * (W ^ D)⁻¹ * ∏ i, a (j i) := by ring
  have h1 := hF.norm_le_of_bounded hg hb
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  calc K * (W ^ D)⁻¹ * ∑' j : Fin d → ℤ, ∏ i, a (j i) ≤ K * (W ^ D)⁻¹ * Kc ^ d :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg hK0 (inv_nonneg.mpr hWD.le))
    _ = K * Kc ^ d / W ^ D := by ring

/-- `|e^{−i t}| = 1` for real `t`. -/
private theorem norm_cexp_neg_I_mul (t : ℝ) : ‖cexp (-(I * (t : ℂ)))‖ = 1 := by
  rw [show -(I * (t : ℂ)) = ((-t : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

end Aux

/-- The characters of `Z_L^d` are `e^{i p·[x]_L}`, with `p = 2πk/L` the centred frequency of
[I, (1.30)] and `[x]_L` the representative of [I, (1.2)]. -/
theorem zchar_eq_cexp :
  ∀ (d L : ℕ) [NeZero L] (k x : Zd d L),
    zchar k x = cexp (I * (inner ℝ (zfreq k) (zrep x) : ℝ)) := by
  intro d L _ k x
  have hk : ∀ i, k i * x i = (((k i).valMinAbs * (x i).valMinAbs : ℤ) : ZMod L) := by
    intro i
    push_cast
    rfl
  simp only [zchar, hk, ZMod.stdAddChar_coe]
  rw [← Complex.exp_sum]
  congr 1
  simp only [zfreq, zrep, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The symbol of `S_{W,L}` (display after [I, (1.30)]):
`Ŝ(p) = Z_{W,L}^{−1} Σ_{x∈Z_L^d} [(2π)^{−d}∫ψ(Wq)e^{iq·[x]_L}dq] e^{−i p·[x]_L}`, for every `ψ`,
`W` and `L` (both sides vanish when `Z_{W,L} = 0`). -/
theorem symbol_Smat :
  ∀ (d L : ℕ) [NeZero L] (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) (k : Zd d L),
    symbol (cmat (Smat ψ W L)) k =
      ((ZWL ψ W L : ℂ))⁻¹ * ∑ x : Zd d L,
        (fRaw ψ W L x : ℂ) * cexp (-(I * (inner ℝ (zfreq k) (zrep x) : ℝ))) := by
  intro d L _ ψ W k
  have hc : ∀ x : Zd d L, zchar k (-x) = cexp (-(I * (inner ℝ (zfreq k) (zrep x) : ℝ))) := by
    intro x
    rw [zchar_neg_eq_conj, zchar_eq_cexp, ← Complex.exp_conj, map_mul, Complex.conj_I,
      Complex.conj_ofReal, neg_mul]
  have h1 : symbol (cmat (Smat ψ W L)) k = ∑ x : Zd d L, (fWL ψ W L x : ℂ) * zchar k (-x) := by
    simp only [symbol, cmat, Matrix.map_apply, Smat, Matrix.of_apply, zero_sub]
    exact Fintype.sum_equiv (Equiv.neg _) _ _ fun x => by simp
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hc, fWL]
  push_cast
  ring

/-- `S_{xy} = f_{W,L}([x − y]_L)` is translation invariant ([I, (1.5)]), for every `ψ`, `W`
and `L`. -/
theorem Smat_transInv :
  ∀ (d L : ℕ) [NeZero L] (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ), TransInv (Smat ψ W L) := by
  intro d L _ ψ W x y a
  simp only [Smat, Matrix.of_apply, add_sub_add_right_eq_sub]

/-- [I, Assumption 1.1]: on `adm(c₀, c₁)` for `W ≥ W₀`, `S_{W,L}` is a variance kernel:
symmetric, translation invariant, nonnegative, with row sums one. -/
theorem Smat_isVarKernel_adm :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁), ∃ W₀ : ℝ,
    ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → IsVarKernel (Smat P.ψ W L) := by
  intro d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₁, hW₁⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, hW₂⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  refine ⟨max W₁ W₂, fun W L _ hm hW => ?_⟩
  obtain ⟨hs, hn⟩ := hW₁ W L hm (le_trans (le_max_left _ _) hW)
  obtain ⟨-, hrow, -⟩ := mem_doublyStochastic_iff_sum.mp
    (hW₂ W L hm (le_trans (le_max_right _ _) hW))
  exact ⟨fun x y => hs.apply y x, Smat_transInv d L P.ψ W, hn, hrow⟩

/-- On `adm(c₀, c₁)` for `W ≥ W₀`, `S_{W,L}` is symmetric and translation invariant with
`|Ŝ(p)| ≤ 1`. -/
theorem Smat_isSymKernel_adm :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁), ∃ W₀ : ℝ,
    ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → IsSymKernel (Smat P.ψ W L) := by
  intro d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₀, hW₀⟩ := Smat_isVarKernel_adm d P c₀ c₁ hc₀ hc₁
  exact ⟨W₀, fun W L _ hm hW => IsVarKernel_isSymKernel _ (hW₀ W L hm hW)⟩

/-- (H3) on `adm(c₀, c₁)`: `|Ŝ_{W,L}(p) − ψ(Wp)| ≤ C_{D′} W^{−D′}` for every `D′` and every
`p ∈ T_L^d`, with constants `C_{D′}` fixed by `ψ`, `c₀`, `c₁` before `(W, L)`. Here `Ŝ_{W,L}` is the
symbol of `S_{W,L}` (display after [I, (1.30)]); the bound combines Poisson summation, the
nonnegativity of `φ` ([I, Assumption 1.2]) and [I, (1.10)]. -/
theorem symbolClose_adm :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀), ∃ C : ℕ → ℝ,
    ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → SymbolClose P.ψ C W (Smat P.ψ W L) := by
  intro d P c₀ c₁ hc₀
  choose Cz hCz using fun D : ℕ => ZWL_close_adm d P.ψ P.at_zero c₀ c₁ hc₀ D
  choose Ce hCe using fun D : ℕ => alias_bound P.ψ D
  refine ⟨fun D => 2 * Cz D + 2 * Ce D, fun W L _ hm D k => ?_⟩
  have hW1 : 1 ≤ W := adm_one_le c₀ c₁ W L (Nat.pos_of_ne_zero (NeZero.ne L)) hm
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hWD : (0 : ℝ) < (W : ℝ) ^ D := pow_pos hW0 D
  -- the integral of [I, (1.6)] is real and nonnegative
  have hreal : ∀ y, profInt P.ψ W y = (((profInt P.ψ W y).re : ℝ) : ℂ) := fun y =>
    Complex.ext rfl (by simp [profInt_im d P.ψ P.symm W y])
  have hnn : ∀ y, 0 ≤ (profInt P.ψ W y).re := by
    intro y
    rw [profInt_scale d P.ψ W hW0 y]
    have h : (((W : ℝ) : ℂ) ^ d)⁻¹ = ((((W : ℝ) ^ d)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) ((profPhi_prob d P).1 _)
  -- `Z_L^d` inside `ℤ^d` through the representatives `[x]_L`
  set ι : Zd d L → (Fin d → ℤ) := fun x i => (x i).valMinAbs with hι
  have hιinj : Function.Injective ι := by
    intro x y h
    funext i
    exact ZMod.injective_valMinAbs (congrFun h i)
  have hιrep : ∀ x, intVec (ι x) = zrep x := fun x => rfl
  set s : Finset (Fin d → ℤ) := Finset.univ.image ι with hs
  set p := zfreq k with hp
  set fP : (Fin d → ℤ) → ℂ := fun z =>
    profInt P.ψ W (intVec z) * cexp (-(I * (inner ℝ p (intVec z) : ℝ))) with hfP
  set a : (Fin d → ℤ) → ℝ := fun z => (profInt P.ψ W (intVec z)).re with ha
  set Λs : ℂ := ∑ x : Zd d L, (fRaw P.ψ W L x : ℂ) * cexp (-(I * (inner ℝ p (zrep x) : ℝ)))
    with hΛs
  set Z := ZWL P.ψ W L with hZ
  have hsumΛ : ∑ z ∈ s, fP z = Λs := by
    rw [hs, Finset.sum_image (fun x _ y _ h => hιinj h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hfP, hιrep, fRaw]
    rw [← hreal]
  have hsuma : ∑ z ∈ s, a z = Z := by
    rw [hs, Finset.sum_image (fun x _ y _ h => hιinj h)]
    rfl
  -- Poisson summation at `p` and at `0`
  obtain ⟨-, hP⟩ := poisson_profile d P.ψ W hW0 p
  obtain ⟨-, hP0⟩ := poisson_profile d P.ψ W hW0 0
  rw [← Complex.ofReal_tsum] at hP hP0
  set T : ℝ := ∑' j : Fin d → ℤ, P.ψ ((W : ℝ) • (p + (2 * Real.pi) • intVec j)) with hT
  set T0 : ℝ := ∑' j : Fin d → ℤ, P.ψ ((W : ℝ) • (0 + (2 * Real.pi) • intVec j)) with hT0
  have ha0 : HasSum a T0 := by
    have h := Complex.hasSum_re hP0
    simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
      mul_one, Complex.ofReal_re] at h
    exact h
  have hPc := (Finset.hasSum_iff_compl s).mp hP
  have hac := (Finset.hasSum_iff_compl s).mp ha0
  -- the part of the lattice sum outside `Z_L^d`
  have hE2 : ‖(T : ℂ) - Λs‖ ≤ T0 - Z := by
    rw [← hsumΛ, ← hsuma]
    refine hPc.norm_le_of_bounded hac fun z => ?_
    change ‖fP z‖ ≤ a z
    simp only [hfP, ha]
    rw [norm_mul, norm_cexp_neg_I_mul, mul_one, hreal, Complex.norm_real,
      Real.norm_of_nonneg (hnn _)]
    exact le_of_eq (Complex.ofReal_re _).symm
  -- `|Σ_x f_{W,L}(x) e^{−ip·[x]_L}| ≤ Z_{W,L}`
  have hZnn : 0 ≤ Z := Finset.sum_nonneg fun x _ => hnn _
  have hΛle : ‖Λs‖ ≤ Z := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, norm_cexp_neg_I_mul, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ fRaw P.ψ W L x from hnn _)]
  have hS : symbol (cmat (Smat P.ψ W L)) k = (Z : ℂ)⁻¹ * Λs := symbol_Smat d L P.ψ W k
  set Sh : ℂ := (Z : ℂ)⁻¹ * Λs with hSh
  have hZS : Sh * (Z : ℂ) = Λs := by
    by_cases hZ0 : Z = 0
    · have h0 : Λs = 0 := norm_le_zero_iff.mp (hZ0 ▸ hΛle)
      rw [hSh, h0, mul_zero, zero_mul]
    · rw [hSh, mul_comm, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hZ0), one_mul]
  have hSle : ‖Sh‖ ≤ 1 := by
    rw [hSh, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hZnn]
    by_cases hZ0 : Z = 0
    · simp [hZ0]
    · rw [inv_mul_le_iff₀ (lt_of_le_of_ne hZnn (Ne.symm hZ0)), mul_one]
      exact hΛle
  -- the three error terms
  have hE1p := hCe D W hW1r p (fun i => abs_zfreq_le k i)
  have hE10 := hCe D W hW1r 0 (fun i => by simp [Real.pi_pos.le])
  rw [smul_zero, P.at_zero] at hE10
  have hZc := hCz D W L hm
  rw [hS]
  have key : Sh - (P.ψ ((W : ℝ) • p) : ℂ) =
      Sh * (1 - (Z : ℂ)) + (Λs - (T : ℂ)) + ((T : ℂ) - (P.ψ ((W : ℝ) • p) : ℂ)) := by
    linear_combination hZS
  have h1 : ‖Sh * (1 - (Z : ℂ))‖ ≤ |Z - 1| := by
    rw [norm_mul, show (1 : ℂ) - (Z : ℂ) = ((1 - Z : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact mul_le_of_le_one_left (abs_nonneg _) hSle
  have h2 : ‖Λs - (T : ℂ)‖ ≤ |T0 - 1| + |Z - 1| := by
    rw [norm_sub_rev]
    refine hE2.trans ?_
    have := le_abs_self (T0 - 1)
    have := neg_abs_le (Z - 1)
    linarith
  have h3 : ‖(T : ℂ) - (P.ψ ((W : ℝ) • p) : ℂ)‖ = |T - P.ψ ((W : ℝ) • p)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [key]
  calc ‖Sh * (1 - (Z : ℂ)) + (Λs - (T : ℂ)) + ((T : ℂ) - (P.ψ ((W : ℝ) • p) : ℂ))‖
      ≤ ‖Sh * (1 - (Z : ℂ))‖ + ‖Λs - (T : ℂ)‖ + ‖(T : ℂ) - (P.ψ ((W : ℝ) • p) : ℂ)‖ :=
        norm_add₃_le
    _ ≤ |Z - 1| + (|T0 - 1| + |Z - 1|) + |T - P.ψ ((W : ℝ) • p)| := by
        rw [h3]; exact add_le_add (add_le_add h1 h2) le_rfl
    _ ≤ Cz D / (W : ℝ) ^ D + (Ce D / (W : ℝ) ^ D + Cz D / (W : ℝ) ^ D) + Ce D / (W : ℝ) ^ D :=
        add_le_add (add_le_add hZc (add_le_add hE10 hZc)) hE1p
    _ = (2 * Cz D + 2 * Ce D) / (W : ℝ) ^ D := by ring

/-- All hypotheses on `(ψ, S)` of [I, (B.19)] and [I, Lemma 2.2] (`SymbolBound`, `SymbolClose`,
`IsSymKernel`, `IsVarKernel`) and the shape conditions `ProfileShape`, from [I, Assumption 1.2]:
the constants `c′` and `C_{D′}` depend only on `ψ`, `c₀`, `c₁`, and the kernel conditions hold on
`adm(c₀, c₁)` for `W ≥ W₀`. -/
theorem discharge :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁),
    (∃ c' : ℝ, SymbolBound P.ψ c') ∧ ProfileShape P.ψ P.cψ ∧
    (∃ C : ℕ → ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ →
      SymbolClose P.ψ C W (Smat P.ψ W L)) ∧
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      IsSymKernel (Smat P.ψ W L) ∧ IsVarKernel (Smat P.ψ W L) := by
  intro d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₁, h₁⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, h₂⟩ := Smat_isVarKernel_adm d P c₀ c₁ hc₀ hc₁
  exact ⟨symbolBound_of_profile d P, profileShape_of_profile d P, symbolClose_adm d P c₀ c₁ hc₀,
    max W₁ W₂, fun W L _ hm hW => ⟨h₁ W L hm (le_trans (le_max_left _ _) hW),
      h₂ W L hm (le_trans (le_max_right _ _) hW)⟩⟩

section Witness

end Witness

end RBM8D
