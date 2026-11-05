import RBM8D.SelfEnergy.FT1a
import RBM8D.SelfEnergy.InfBound
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Momentum forms of the self-energies on `ℤ^d` ([I, (7.28)–(7.30)], [I, Claim 7.8])

On `ℤ^d` with `S_∞ = Sinf P.ψ W` ([I, (7.3)]), `m = m(E)` and the label kernels
`Σ̊^∞ = ValZ.sigKer Sig P.ψ E` of [I, Def 8.2]; `Q = [−π, π]^d`, `|p|² = Σ_i p_i²` and
`D_W(p) = max(1, (W²|p|²)⁻¹)` (`FT1b.dW`).

* `FT1b.edgeSymbols`: the kernels `S_∞`, `S^±_∞(m)` and `Θ_∞` are `latticeFourier` of the symbols
  `ŝ`, `ψ_+ = m²ŝ/(1 − m²ŝ)`, `ψ_− = m̄²ŝ/(1 − m̄²ŝ)` (`FT1b.plusSym`, `FT1b.minusSym`) and
  `ψ_Θ = ŝ/(1 − ŝ)` (`FT1b.thetaSym`); the four symbols are measurable, `2π`-periodic and in
  `L²(Q)`, with `|ŝ| ≤ 1`, `|ψ_±| ≤ b⁻¹` and `|ψ_Θ| ≤ c⁻¹ D_W` on `Q`.
* `FT1b.chainFourier`: [I, (7.28)] on `ℤ^d`: the chain `Θ_∞ Σ̊^∞_{o₁} Θ_∞ ⋯ Σ̊^∞_{o_r} Θ_∞`
  (`chainZ`) is `latticeFourier ψ_o`, `ψ_o = ψ_Θ^{r+1} Π_i ψ_{Σ̊^∞_{o_i}}` (`FT1b.chainSym`), with
  `ψ_o ∈ L¹ ∩ L²(Q)` and `|ψ_o| ≤ C W^{rτ − Σ_i (o_i − 2)d/2} D_W` on `Q`, for labels with entries
  even in `[4, N]`. Each convolution is computed by Parseval's identity for inner products on the
  torus; the bound combines the exact symbol bound `InfBound.symbolBound` of `Σ̊^∞_l` with
  `Σ_x |Σ̊^∞_l(0, x)| ≲ W^τ W^{-(l-2)d/2}`, so that `|ψ_Θ ψ_{Σ̊^∞_l}| ≲ W^τ W^{-(l-2)d/2}`.
* `FT1b.rowSumFourier`: [I, (7.29)–(7.30)] for the number `R(E, W) = ValZ.rowSum` of [I, (8.8)]
  and for the symbol of `Σ^{(r),∞}_l`: after the contraction of [I, Def 3.1] every graph `g` of
  `Σ_l` has two spanning trees of its atoms ([I, Def 6.5]), and `FT1a.graphFourier` gives
  `Σ_x g^∞(0, x) e^{ip·x} = c_g(m) M_g(p)`, with `M_g(p)` the momentum integral `FT1b.momInt` of the
  component symbols `FT1b.kindSym` (`FT1b.MomGraph`). A diagonal graph keeps its dotted edge
  `x – y` as an edge with symbol `1`; at odd `n`, `Σ_n = []` and `R = 0`.
* `FT1b.symbolCompare`: [I, Claim 7.8] as comparisons of `ŝ`, `ψ_±` and `ψ_Θ` with the same
  functions of `ψ(Wp)` on `Q`, up to `C W^{-D}` (`C W^{-D} D_W²` for `ψ_Θ`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace RBM8D

open Graphs

open private FT1a_parseval FT1a_continuous_zdSeries FT1a_norm_zdSeries_le FT1a_zdSeries_periodic
  FT1a_memLp_zdSeries FT1a_zexp_periodic FT1a_integral_tor FT1a_mFourier_tor FT1a_lift1 FT1a_mpQ
  FT1a_μQ FT1a_μQ_eq FT1a_rep FT1a_tor1 FT1a_measurable_rep FT1a_isFinite_cube FT1a_integral_eq_lf
  FT1a_zexp_neg from RBM8D.SelfEnergy.FT1a

variable {d : ℕ}

/-! ## Fourier series on `[−π, π]^d` -/

section Fourier

attribute [local instance] FT1a_isFinite_cube

private theorem FT1b_measurableSet_cube : MeasurableSet (cubePi d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

private theorem FT1b_neg_preimage_cube : (Neg.neg ⁻¹' cubePi d : Set (Fin d → ℝ)) = cubePi d := by
  ext p
  simp only [Set.mem_preimage, cubePi, Set.mem_univ_pi, Set.mem_Icc, Pi.neg_apply]
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]

/-- `p ↦ −p` preserves Lebesgue measure on `[−π, π]^d`. -/
private theorem FT1b_mp_neg :
    MeasurePreserving (Neg.neg : (Fin d → ℝ) → (Fin d → ℝ)) (volume.restrict (cubePi d))
      (volume.restrict (cubePi d)) := by
  have h := (Measure.measurePreserving_neg (volume : Measure (Fin d → ℝ))).restrict_preimage
    (FT1b_measurableSet_cube (d := d))
  rwa [FT1b_neg_preimage_cube] at h

/-- `∫_{[−π,π]^d} F(−p) dp = ∫_{[−π,π]^d} F(p) dp`. -/
private theorem FT1b_integral_neg (F : (Fin d → ℝ) → ℂ) :
    ∫ p in cubePi d, F (-p) = ∫ p in cubePi d, F p := by
  have h := (Measure.measurePreserving_neg (volume : Measure (Fin d → ℝ))).setIntegral_preimage_emb
    (MeasurableEquiv.neg (Fin d → ℝ)).measurableEmbedding F (cubePi d)
  rw [FT1b_neg_preimage_cube] at h
  exact h

private theorem FT1b_zexp_neg_left (p : Fin d → ℝ) (x : Fin d → ℤ) :
    zexp (-p) x = zexp p (-x) := by
  unfold zexp
  congr 3
  simp [Finset.sum_neg_distrib]

private theorem FT1b_zexp_zero (p : Fin d → ℝ) : zexp p 0 = 1 := by
  simp [zexp]

private theorem FT1b_zexp_zero_left (x : Fin d → ℤ) : zexp 0 x = 1 := by
  simp [zexp]

/-- `conj (k(x)) = latticeFourier (p ↦ conj F(−p)) (x)` for `k = latticeFourier F`. -/
private theorem FT1b_conj_lf (F : (Fin d → ℝ) → ℂ) (x : Fin d → ℤ) :
    conj (latticeFourier F x) = latticeFourier (fun p => conj (F (-p))) x := by
  unfold latticeFourier
  rw [map_mul, ← integral_conj]
  congr 1
  · simp [map_ofNat]
  · rw [← FT1b_integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [map_mul, FT1a_zexp_neg, FT1b_zexp_neg_left, RCLike.conj_conj]

/-- The constant symbol `1` is the kernel `δ_0`. -/
theorem FT1b.lf_one (x : Fin d → ℤ) :
    latticeFourier (fun _ => (1 : ℂ)) x = if x = 0 then 1 else 0 := by
  have h := latticeFourier_zexp x 0
  simp only [FT1b_zexp_zero] at h
  exact h

/-- The symbol `0` is the kernel `0`. -/
private theorem FT1b_lf_zero (x : Fin d → ℤ) : latticeFourier (fun _ => (0 : ℂ)) x = 0 := by
  simp [latticeFourier]

/-- The Fourier series of `δ_0` is `1`. -/
private theorem FT1b_zdSeries_delta (p : Fin d → ℝ) :
    zdSeries (fun x : Fin d → ℤ => if x = 0 then (1 : ℂ) else 0) p = 1 := by
  unfold zdSeries
  rw [tsum_eq_single 0 (fun x hx => by simp [hx])]
  simp [FT1b_zexp_zero]

/-- A periodic function in `L²([−π, π]^d)` composed with `p ↦ −p`. -/
private theorem FT1b_memLp_neg {φ : (Fin d → ℝ) → ℂ}
    (h : MemLp φ 2 (volume.restrict (cubePi d))) :
    MemLp (fun p => φ (-p)) 2 (volume.restrict (cubePi d)) :=
  h.comp_measurePreserving FT1b_mp_neg

/-- **Parseval's identity for inner products** on `[−π, π]^d`:
`Σ_x conj k(x) k'(x) = (2π)^{-d} ∫ conj f f'` for `k = latticeFourier f`, `k' = latticeFourier f'`
with `f, f'` measurable, periodic and in `L²([−π, π]^d)`. -/
private theorem FT1b_parsevalProd (φ χ : (Fin d → ℝ) → ℂ) (hmφ : Measurable φ)
    (hmχ : Measurable χ)
    (hpφ : ∀ p (z : Fin d → ℤ), φ (p + fun i => 2 * Real.pi * z i) = φ p)
    (hpχ : ∀ p (z : Fin d → ℤ), χ (p + fun i => 2 * Real.pi * z i) = χ p)
    (hLφ : MemLp φ 2 (volume.restrict (cubePi d))) (hLχ : MemLp χ 2 (volume.restrict (cubePi d))) :
    HasSum (fun n => conj (latticeFourier φ n) * latticeFourier χ n)
      (((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, conj (φ p) * χ p) := by
  have htor : ∀ (H : (Fin d → ℝ) → ℂ), Measurable H →
      (∀ p (z : Fin d → ℤ), H (p + fun i => 2 * Real.pi * z i) = H p) →
      MemLp H 2 (volume.restrict (cubePi d)) →
      ∃ Ht : UnitAddTorus (Fin d) → ℂ, Measurable Ht ∧
        (∀ p, Ht (fun i => FT1a_tor1 (p i)) = H p) ∧
        MemLp Ht 2 (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    intro H hm hper hL2
    let Ht : UnitAddTorus (Fin d) → ℂ := fun y => H (fun i => 2 * Real.pi * FT1a_rep (y i))
    have hHt : ∀ p, Ht (fun i => FT1a_tor1 (p i)) = H p := FT1a_lift1 H hper
    have hmt : Measurable Ht := hm.comp (measurable_pi_iff.2 fun i =>
      measurable_const.mul (FT1a_measurable_rep.comp (measurable_pi_apply i)))
    refine ⟨Ht, hmt, hHt, ?_⟩
    have hae : AEStronglyMeasurable Ht (Measure.map (fun (p : Fin d → ℝ) i => FT1a_tor1 (p i))
        (FT1a_μQ d)) := by
      rw [FT1a_mpQ.map_eq]
      exact hmt.aestronglyMeasurable
    rw [← FT1a_mpQ.map_eq, memLp_map_measure_iff hae FT1a_mpQ.measurable.aemeasurable]
    have : Ht ∘ (fun (p : Fin d → ℝ) i => FT1a_tor1 (p i)) = H := funext hHt
    rw [this, FT1a_μQ_eq, ENNReal.smul_def]
    exact hL2.smul_measure ENNReal.coe_ne_top
  obtain ⟨φt, hmφt, hφt, hLφt⟩ := htor φ hmφ hpφ hLφ
  obtain ⟨χt, hmχt, hχt, hLχt⟩ := htor χ hmχ hpχ hLχ
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (d := Fin d) (hLφt.toLp φt) (hLχt.toLp χt)
  have hcoef : ∀ (Ht : UnitAddTorus (Fin d) → ℂ) (H : (Fin d → ℝ) → ℂ), Measurable Ht →
      (∀ p, Ht (fun i => FT1a_tor1 (p i)) = H p) →
      ∀ (hL : MemLp Ht 2
        (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))) n,
      UnitAddTorus.mFourierCoeff (hL.toLp Ht : UnitAddTorus (Fin d) → ℂ) n =
        latticeFourier H n := by
    intro Ht H hmt hHt hL n
    have h1 : UnitAddTorus.mFourierCoeff (hL.toLp Ht : UnitAddTorus (Fin d) → ℂ) n =
        UnitAddTorus.mFourierCoeff Ht n :=
      integral_congr_ae ((hL.coeFn_toLp).mono fun t ht => by simp only [ht])
    rw [h1]
    change ∫ t, UnitAddTorus.mFourier (-n) t • Ht t
      ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) = _
    rw [FT1a_integral_tor (fun t => UnitAddTorus.mFourier (-n) t • Ht t)
      ((UnitAddTorus.mFourier (-n)).continuous.measurable.smul hmt).aestronglyMeasurable]
    simp only [FT1a_mFourier_tor, hHt, smul_eq_mul]
    unfold latticeFourier
    rw [Complex.real_smul]
    push_cast
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)
  simp only [hcoef φt φ hmφt hφt hLφt, hcoef χt χ hmχt hχt hLχt] at h
  have hval : ∫ t, conj ((hLφt.toLp φt : UnitAddTorus (Fin d) → ℂ) t) *
      (hLχt.toLp χt : UnitAddTorus (Fin d) → ℂ) t
      ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, conj (φ p) * χ p := by
    rw [integral_congr_ae (g := fun t => conj (φt t) * χt t)
      (((hLφt.coeFn_toLp).and (hLχt.coeFn_toLp)).mono fun t ht => by simp only [ht.1, ht.2]),
      FT1a_integral_tor (fun t => conj (φt t) * χt t)
        (((Complex.continuous_conj.measurable.comp hmφt).mul hmχt).aestronglyMeasurable)]
    simp only [hφt, hχt]
    rw [Complex.real_smul]
  convert h using 1
  exact hval.symm

/-- **Convolution theorem** on `ℤ^d` for two kernels with symbols in `L²([−π, π]^d)`:
`Σ_α k(α) k'(x − α) = latticeFourier (f f') (x)` for `k = latticeFourier f`,
`k' = latticeFourier f'`, the sum being absolutely convergent. -/
private theorem FT1b_hasSum_conv (φ χ : (Fin d → ℝ) → ℂ) (hmφ : Measurable φ) (hmχ : Measurable χ)
    (hpφ : ∀ p (z : Fin d → ℤ), φ (p + fun i => 2 * Real.pi * z i) = φ p)
    (hpχ : ∀ p (z : Fin d → ℤ), χ (p + fun i => 2 * Real.pi * z i) = χ p)
    (hLφ : MemLp φ 2 (volume.restrict (cubePi d))) (hLχ : MemLp χ 2 (volume.restrict (cubePi d)))
    (x : Fin d → ℤ) :
    HasSum (fun α => latticeFourier φ α * latticeFourier χ (x - α))
      (latticeFourier (fun p => φ p * χ p) x) := by
  set φ' : (Fin d → ℝ) → ℂ := fun p => conj (φ (-p)) with hφ'
  set g : (Fin d → ℝ) → ℂ := fun p => χ (-p) * zexp p x with hg
  have hzc : Continuous fun p : Fin d → ℝ => zexp p x := by unfold zexp; fun_prop
  have hneg : ∀ (p : Fin d → ℝ) (z : Fin d → ℤ),
      -(p + fun i => 2 * Real.pi * z i) = -p + fun i => 2 * Real.pi * ((-z) i : ℤ) := by
    intro p z
    funext i
    simp only [Pi.neg_apply, Pi.add_apply, Int.cast_neg]
    ring
  have h1 := FT1b_parsevalProd φ' g
    (Complex.continuous_conj.measurable.comp (hmφ.comp measurable_neg))
    ((hmχ.comp measurable_neg).mul hzc.measurable)
    (fun p z => by simp only [hφ', hneg, hpφ])
    (fun p z => by simp only [hg, hneg, hpχ, FT1a_zexp_periodic])
    (by
      have : MemLp (fun p => φ (-p)) 2 (volume.restrict (cubePi d)) := FT1b_memLp_neg hLφ
      exact this.congr_norm
        (Complex.continuous_conj.measurable.comp (hmφ.comp measurable_neg)).aestronglyMeasurable
        (Eventually.of_forall fun p => (Complex.norm_conj _).symm))
    (by
      have h2 : MemLp (fun p => χ (-p)) 2 (volume.restrict (cubePi d)) := FT1b_memLp_neg hLχ
      refine h2.of_le_mul (c := 1) ((hmχ.comp measurable_neg).mul hzc.measurable).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      simp only [hg, norm_mul, norm_zexp, mul_one, one_mul, le_refl])
  have ha : ∀ α, conj (latticeFourier φ' α) = latticeFourier φ α := by
    intro α
    rw [FT1b_conj_lf]
    congr 1
    funext p
    simp [hφ']
  have hb : ∀ α, latticeFourier g α = latticeFourier χ (x - α) := by
    intro α
    unfold latticeFourier
    congr 1
    rw [← FT1b_integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [hg, neg_neg, FT1b_zexp_neg_left]
    rw [mul_assoc, ← zexp_add]
    congr 2
    abel
  simp only [ha, hb] at h1
  convert h1 using 1
  unfold latticeFourier
  push_cast
  congr 1
  rw [← FT1b_integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [hφ', hg, neg_neg, RCLike.conj_conj, FT1b_zexp_neg_left]
  ring

/-- Every point of `ℝ^d` is a point of `[−π, π]^d` up to a vector of `2πℤ^d`. -/
private theorem FT1b_reduce (p : Fin d → ℝ) :
    ∃ z : Fin d → ℤ, (p + fun i => 2 * Real.pi * z i) ∈ cubePi d := by
  refine ⟨fun i => -round (p i / (2 * Real.pi)), fun i _ => ?_⟩
  have h := abs_sub_round (p i / (2 * Real.pi))
  have hpi := Real.pi_pos
  rw [abs_le] at h
  simp only [Pi.add_apply, Int.cast_neg]
  have e : p i + 2 * Real.pi * -(round (p i / (2 * Real.pi)) : ℝ) =
      2 * Real.pi * (p i / (2 * Real.pi) - round (p i / (2 * Real.pi))) := by
    field_simp
    ring
  rw [e]
  constructor <;> nlinarith [h.1, h.2]

/-- **Uniqueness of the symbol**: a continuous `2π`-periodic `f` whose kernel
`k = latticeFourier f` is in `ℓ¹` is the Fourier series of `k`. -/
private theorem FT1b_eq_zdSeries (φ : (Fin d → ℝ) → ℂ) (hc : Continuous φ)
    (hp : ∀ p (z : Fin d → ℤ), φ (p + fun i => 2 * Real.pi * z i) = φ p)
    (hk : Summable fun x => ‖latticeFourier φ x‖) :
    φ = zdSeries (latticeFourier φ) := by
  set k := latticeFourier φ with hkdef
  set ψ : (Fin d → ℝ) → ℂ := fun p => φ p - zdSeries k p with hψ
  have hcs : Continuous (zdSeries k) := FT1a_continuous_zdSeries k hk
  have hψc : Continuous ψ := hc.sub hcs
  have hcube : IsCompact (cubePi d) := isCompact_univ_pi fun _ => isCompact_Icc
  have hint : ∀ (G : (Fin d → ℝ) → ℂ), Continuous G → ∀ x : Fin d → ℤ,
      Integrable (fun p => G p * zexp p (-x)) (volume.restrict (cubePi d)) := by
    intro G hG x
    have : Continuous fun p => G p * zexp p (-x) := hG.mul (by unfold zexp; fun_prop)
    exact this.continuousOn.integrableOn_compact hcube
  have hlf : ∀ x, latticeFourier ψ x = 0 := by
    intro x
    have h1 : latticeFourier ψ x = latticeFourier φ x - latticeFourier (zdSeries k) x := by
      unfold latticeFourier
      rw [← mul_sub, ← integral_sub (hint φ hc x) (hint _ hcs x)]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [hψ]
      ring
    rw [h1, latticeFourier_zdSeries k hk x, sub_self]
  have hL2 : MemLp ψ 2 (volume.restrict (cubePi d)) := by
    obtain ⟨M, hM⟩ := hcube.exists_bound_of_continuousOn hψc.continuousOn
    refine MemLp.of_bound hψc.aestronglyMeasurable M ?_
    exact (ae_restrict_iff' FT1b_measurableSet_cube).2 (Eventually.of_forall hM)
  have hper : ∀ p (z : Fin d → ℤ), ψ (p + fun i => 2 * Real.pi * z i) = ψ p := by
    intro p z
    simp only [hψ, hp, FT1a_zdSeries_periodic]
  have hpar := FT1a_parseval ψ hψc.measurable hper hL2
  simp only [hlf, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hpar
  have h0 : ∫ p in cubePi d, ‖ψ p‖ ^ 2 = 0 := by
    have := hpar.unique hasSum_zero
    have hne : ((2 * Real.pi) ^ d)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ Real.two_pi_pos.ne')
    exact (mul_eq_zero.1 this).resolve_left hne
  have hint2 : Integrable (fun p => ‖ψ p‖ ^ 2) (volume.restrict (cubePi d)) :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  have hae : (fun p => ‖ψ p‖ ^ 2) =ᵐ[volume.restrict (cubePi d)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p => by positivity) hint2).1 h0
  have hae' : ψ =ᵐ[volume.restrict (cubePi d)] 0 :=
    hae.mono fun p hp => by simpa using hp
  have hsub : cubePi d ⊆ closure (interior (cubePi d)) := by
    unfold cubePi
    rw [interior_pi_set Set.finite_univ, closure_pi_set]
    intro p hp i _
    simp only [interior_Icc, closure_Ioo (by linarith [Real.pi_pos] : -Real.pi ≠ Real.pi)]
    exact hp i (Set.mem_univ i)
  have heq := Measure.eqOn_of_ae_eq hae' hψc.continuousOn continuousOn_const hsub
  funext p
  obtain ⟨z, hz⟩ := FT1b_reduce p
  have := heq hz
  rw [hper] at this
  simpa [hψ, sub_eq_zero] using this

end Fourier

/-! ## The edge symbols -/

section Symbols

open private q_lower one_sub_mul_conj InfKernel.weighted_sum from RBM8D.Kernel.ShellKernel
open private ValZ_shape ValZ_zdSymbol_neg ValZ_wave_bound ValZ_wb from RBM8D.SelfEnergy.ValZ
open private latSum from RBM8D.Bound.AuxTreeZ

attribute [local instance] FT1a_isFinite_cube

/-- `D_W(p) = max(1, (W²|p|²)⁻¹)`, `|p|² = Σ_i p_i²`. -/
def FT1b.dW (W : ℕ) (p : Fin d → ℝ) : ℝ := max 1 ((W : ℝ) ^ 2 * sqNorm p)⁻¹

/-- The symbol `ψ_Θ = ŝ/(1 − ŝ)` of `Θ_∞` ([I, (7.5)]). -/
def FT1b.thetaSym (s : (Fin d → ℤ) → ℝ) (p : Fin d → ℝ) : ℂ :=
  zdSymbol s p / (1 - zdSymbol s p)

/-- The symbol `ψ_+ = m² ŝ/(1 − m² ŝ)` of `S^+_∞(m)` ([I, (7.4)]). -/
def FT1b.plusSym (m : ℂ) (s : (Fin d → ℤ) → ℝ) (p : Fin d → ℝ) : ℂ :=
  m ^ 2 * zdSymbol s p / (1 - m ^ 2 * zdSymbol s p)

/-- The symbol `ψ_− = m̄² ŝ/(1 − m̄² ŝ)` of `S^−_∞(m)` ([I, (7.4)]). -/
def FT1b.minusSym (m : ℂ) (s : (Fin d → ℤ) → ℝ) (p : Fin d → ℝ) : ℂ :=
  conj m ^ 2 * zdSymbol s p / (1 - conj m ^ 2 * zdSymbol s p)

/-- The symbol `ψ_o = ψ_Θ^{|o|+1} Π_{l ∈ o} ψ_{K_l}` of the chain `Θ_∞ K_{o₁} Θ_∞ ⋯ K_{o_r} Θ_∞`
([I, (7.28)]), with `ψ_{K_l}` the Fourier series of the label kernel `K_l` at `W`. -/
def FT1b.chainSym (s : (Fin d → ℤ) → ℝ) (K : KerInf d) (W : ℕ) (o : List ℕ)
    (p : Fin d → ℝ) : ℂ :=
  FT1b.thetaSym s p ^ (o.length + 1) * (o.map fun l => zdSeries (K l W) p).prod

/-- The symbol of a component kind on `ℤ^d` ([I, (7.29)]): `ŝ`, `ψ_±`, the chain symbol `ψ_o` of a
`Θ` edge with label `o`, the constant `1` for a dotted edge (the kernel `δ_0`), and `0` for every
other kind (a `×`-dotted edge of a graph of `Σ` is a loop, where its kernel `1_{a ≠ 0}` is read at
`a = 0`). -/
def FT1b.kindSym (s : (Fin d → ℤ) → ℝ) (K : KerInf d) (W : ℕ) (m : ℂ) :
    Kind → (Fin d → ℝ) → ℂ
  | .waved .s => zdSymbol s
  | .waved .plus => FT1b.plusSym m s
  | .waved .minus => FT1b.minusSym m s
  | .theta o => FT1b.chainSym s K W o
  | .dot => fun _ => 1
  | _ => fun _ => 0

private theorem FT1b_sq_norm_le (p : Fin d → ℝ) : ‖p‖ ^ 2 ≤ sqNorm p := by
  have h0 : 0 ≤ sqNorm p := Finset.sum_nonneg fun i _ => sq_nonneg (p i)
  have h : ‖p‖ ≤ Real.sqrt (sqNorm p) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun j => p j ^ 2) (fun j _ => sq_nonneg (p j))
      (Finset.mem_univ i)
  calc ‖p‖ ^ 2 ≤ Real.sqrt (sqNorm p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sqNorm p := Real.sq_sqrt h0

private theorem FT1b_sqNorm_nonneg (p : Fin d → ℝ) : 0 ≤ sqNorm p :=
  Finset.sum_nonneg fun i _ => sq_nonneg (p i)

private theorem FT1b_sqNorm_eq_zero {p : Fin d → ℝ} (h : sqNorm p = 0) : p = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (p j))).1 h i
    (Finset.mem_univ i)
  simpa using this

private theorem FT1b_dW_pos (W : ℕ) (p : Fin d → ℝ) : 0 < FT1b.dW W p :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

private theorem FT1b_measurable_dW (W : ℕ) : Measurable (FT1b.dW (d := d) W) := by
  unfold FT1b.dW sqNorm
  exact measurable_const.max (measurable_const.mul (by fun_prop)).inv

/-- `D_W · min(W²|p|², 1) = 1` away from `p = 0`, and `≤ 1` everywhere. -/
private theorem FT1b_dW_mul_min (W : ℕ) (p : Fin d → ℝ) :
    FT1b.dW W p * min ((W : ℝ) ^ 2 * sqNorm p) 1 ≤ 1 := by
  unfold FT1b.dW
  set a := (W : ℝ) ^ 2 * sqNorm p
  have ha : 0 ≤ a := mul_nonneg (by positivity) (FT1b_sqNorm_nonneg p)
  rcases le_or_gt 1 a with h | h
  · rw [min_eq_right h, mul_one, max_le_iff]
    exact ⟨le_rfl, inv_le_one_of_one_le₀ h⟩
  · rw [min_eq_left h.le]
    rcases eq_or_lt_of_le ha with h0 | h0
    · rw [← h0]; simp
    · rw [max_eq_right ((one_le_inv₀ h0).2 h.le), inv_mul_cancel₀ h0.ne']

/-- `(|p|²)⁻¹ ∈ L²([−π, π]^d)` for `d ≥ 5`. -/
private theorem FT1b_integrableOn_inv_sq (hd : 5 ≤ d) :
    IntegrableOn (fun p : Fin d → ℝ => ((sqNorm p)⁻¹) ^ 2) (cubePi d) := by
  have hsub : cubePi d ⊆ Metric.ball (0 : Fin d → ℝ) 5 := by
    intro p hp
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
      (by linarith [Real.pi_le_four] : Real.pi < 5)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(hp i (Set.mem_univ i)).1, (hp i (Set.mem_univ i)).2⟩
  have hfin : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
  refine IntegrableOn.mono_set (integrableOn_ball_of_norm_le_rpow (μ := volume)
    (by rw [hfin]; omega) (C := 1) (α := 4) (by rw [hfin]; exact_mod_cast (by omega : 4 < d))
    (Eventually.of_forall fun p => ?_) ?_) hsub
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), one_mul]
    rcases eq_or_ne p 0 with rfl | hp
    · simp [sqNorm]
    · have hn : 0 < ‖p‖ := norm_pos_iff.2 hp
      have hs : 0 < sqNorm p := lt_of_lt_of_le (by positivity) (FT1b_sq_norm_le p)
      rw [Real.rpow_neg (norm_nonneg _), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, inv_pow]
      refine inv_anti₀ (by positivity) ?_
      calc ‖p‖ ^ 4 = (‖p‖ ^ 2) ^ 2 := by ring
        _ ≤ sqNorm p ^ 2 := pow_le_pow_left₀ (by positivity) (FT1b_sq_norm_le p) 2
  · unfold sqNorm
    exact ((by fun_prop : Continuous fun p : Fin d → ℝ => ∑ i, p i ^ 2).measurable.inv.pow_const
      2).aestronglyMeasurable

/-- `D_W ∈ L²([−π, π]^d)` for `d ≥ 5` and `W ≥ 1`. -/
private theorem FT1b_memLp_dW (hd : 5 ≤ d) {W : ℕ} (hW : 1 ≤ W) :
    MemLp (FT1b.dW (d := d) W) 2 (volume.restrict (cubePi d)) := by
  have hm := (FT1b_measurable_dW (d := d) W).aestronglyMeasurable (μ := volume.restrict (cubePi d))
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have hI : Integrable (fun p : Fin d → ℝ => 2 + 2 * ((sqNorm p)⁻¹) ^ 2)
      (volume.restrict (cubePi d)) :=
    (integrable_const 2).add ((FT1b_integrableOn_inv_sq hd).const_mul 2)
  refine hI.mono' (hm.norm.pow 2) (Eventually.of_forall fun p => ?_)
  have hW1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW)
  have hs := FT1b_sqNorm_nonneg p
  have hle : FT1b.dW W p ≤ 1 + (sqNorm p)⁻¹ := by
    unfold FT1b.dW
    refine max_le (by linarith [inv_nonneg.2 hs]) ?_
    rcases eq_or_lt_of_le hs with h0 | h0
    · rw [← h0]; simp
    · have : ((W : ℝ) ^ 2 * sqNorm p)⁻¹ ≤ (sqNorm p)⁻¹ :=
        inv_anti₀ h0 (le_mul_of_one_le_left h0.le hW1)
      linarith
  have h0 := (FT1b_dW_pos W p).le
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith [sq_nonneg (1 - (sqNorm p)⁻¹), inv_nonneg.2 hs]

/-- A measurable function bounded by `B D_W` on `[−π, π]^d` is in `L²([−π, π]^d)` (`d ≥ 5`). -/
private theorem FT1b_memLp_of_dW (hd : 5 ≤ d) {W : ℕ} (hW : 1 ≤ W) {f : (Fin d → ℝ) → ℂ}
    (hm : Measurable f) {B : ℝ} (hB : ∀ p ∈ cubePi d, ‖f p‖ ≤ B * FT1b.dW W p) :
    MemLp f 2 (volume.restrict (cubePi d)) := by
  refine (FT1b_memLp_dW hd hW).of_le_mul (c := B) hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' FT1b_measurableSet_cube).2 (Eventually.of_forall fun p hp => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (FT1b_dW_pos W p).le]
  exact hB p hp

/-- The symbol `ŝ` of `S_∞ = Sinf P.ψ W` for `W ≥ W₀`: `S_∞` is an `InfKernel`, `ŝ` is real with
`−1 + c′/2 ≤ ŝ ≤ 1` everywhere and `c min(W²|p|², 1) ≤ 1 − ŝ(p)` on `[−π, π]^d`. -/
private theorem FT1b_sinf (P : Profile d) : ∃ (C : ℕ → ℝ) (c c' W₀ : ℝ), 0 < c ∧
    SymbolBound P.ψ c' ∧ 1 ≤ W₀ ∧ ∀ W : ℕ, W₀ ≤ W → InfKernel P.ψ C W (Sinf P.ψ W) ∧
      (∀ p, (zdSymbol (Sinf P.ψ W) p).im = 0 ∧ -1 + c' / 2 ≤ (zdSymbol (Sinf P.ψ W) p).re ∧
        (zdSymbol (Sinf P.ψ W) p).re ≤ 1) ∧
      ∀ p ∈ cubePi d, c * min ((W : ℝ) ^ 2 * sqNorm p) 1 ≤ 1 - (zdSymbol (Sinf P.ψ W) p).re := by
  obtain ⟨C, W₁, hC⟩ := Sinf_infKernel d P.ψ P.cψ (ValZ_shape P)
  obtain ⟨c, W₂, hc, h2⟩ := one_sub_zdSymbol_ge d P.ψ P.cψ (ValZ_shape P) C
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨W₃, h3⟩ := zdSymbol_ge d P.ψ c' hc' C
  refine ⟨C, c, c', max (max (max W₁ W₂) W₃) 1, hc, hc', le_max_right _ _, fun W hW => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hs := hC W hW1
  refine ⟨hs, fun p => ?_, fun p hp => (h2 W hW2 _ hs p hp).2⟩
  obtain ⟨z, hz⟩ := FT1b_reduce p
  have hper : zdSymbol (Sinf P.ψ W) p = zdSymbol (Sinf P.ψ W) (p + fun i => 2 * Real.pi * z i) :=
    (FT1a_zdSeries_periodic _ p z).symm
  rw [hper]
  obtain ⟨him, hre⟩ := h2 W hW2 _ hs _ hz
  have hmin : 0 ≤ c * min ((W : ℝ) ^ 2 * sqNorm (p + fun i => 2 * Real.pi * z i)) 1 :=
    mul_nonneg hc.le (le_min (mul_nonneg (by positivity) (FT1b_sqNorm_nonneg _)) zero_le_one)
  exact ⟨him, h3 W hW3 _ hs _ hz, by linarith⟩

private theorem FT1b_shat_real {s : (Fin d → ℤ) → ℝ} {p : Fin d → ℝ}
    (h : (zdSymbol s p).im = 0) : zdSymbol s p = ((zdSymbol s p).re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

private theorem FT1b_norm_shat_le {s : (Fin d → ℤ) → ℝ} {p : Fin d → ℝ} {c' : ℝ} (hc' : 0 < c')
    (h : (zdSymbol s p).im = 0 ∧ -1 + c' / 2 ≤ (zdSymbol s p).re ∧ (zdSymbol s p).re ≤ 1) :
    ‖zdSymbol s p‖ ≤ 1 := by
  rw [FT1b_shat_real h.1, Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [h.2.1], h.2.2⟩

/-- The denominator of `ψ_±`: `|1 − m(E)² t| ≥ b > 0` for real `t ≥ −1 + c′/2`, `|E| ≤ 2 − κ`. -/
private theorem FT1b_denom {κ c' : ℝ} (hκ : 0 < κ) (hc' : 0 < c') :
    ∃ b : ℝ, 0 < b ∧ ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℝ, -1 + c' / 2 ≤ t →
      b ≤ ‖1 - mE E ^ 2 * t‖ ∧ b ≤ ‖1 - conj (mE E) ^ 2 * t‖ := by
  set δ : ℝ := Real.sqrt (2 * κ) / 5
  set q : ℝ := min (min 1 (δ ^ 2 / 2)) ((c' / 2) ^ 2)
  have hq : 0 < q := lt_min (lt_min one_pos (by positivity)) (by positivity)
  refine ⟨Real.sqrt q, Real.sqrt_pos.2 hq, fun E hE t ht => ?_⟩
  obtain ⟨hm1, hmδ⟩ := mE_bulk κ hκ E hE
  set w : ℂ := mE E ^ 2
  have hw1 : ‖w‖ = 1 := by simp [w, norm_pow, hm1]
  have hql := q_lower hw1 (by positivity) hmδ hc' ht
  have hprod := one_sub_mul_conj hw1 t
  have hn : ‖1 - w * t‖ ^ 2 = 1 - 2 * w.re * t + t ^ 2 := by
    have h1 : ‖(1 - w * t) * (1 - conj w * t)‖ = ‖1 - w * t‖ ^ 2 := by
      have hc : (1 - conj w * (t : ℂ)) = conj (1 - w * t) := by simp
      rw [hc, norm_mul, Complex.norm_conj, sq]
    rw [← h1, hprod, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hq.le hql)]
  have hb : Real.sqrt q ≤ ‖1 - w * t‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (1 - w * t)), hn]
    exact Real.sqrt_le_sqrt hql
  refine ⟨hb, ?_⟩
  have hc : (1 - conj (mE E) ^ 2 * (t : ℂ)) = conj (1 - w * t) := by simp [w]
  rw [hc, Complex.norm_conj]
  exact hb

section Edge

variable {ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ} {C : ℕ → ℝ} {W : ℕ}
  {s : (Fin d → ℤ) → ℝ}

private theorem FT1b_summable_s (hs : InfKernel ψ C W s) :
    Summable fun x => ‖((s x : ℝ) : ℂ)‖ := by
  have hsum : Summable s := by
    by_contra h
    have := hs.sum_one
    rw [tsum_eq_zero_of_not_summable h] at this
    exact zero_ne_one this
  simpa only [Complex.norm_real, Real.norm_eq_abs] using summable_abs_iff.2 hsum

private theorem FT1b_continuous_shat (hs : InfKernel ψ C W s) : Continuous (zdSymbol s) :=
  FT1a_continuous_zdSeries _ (FT1b_summable_s hs)

private theorem FT1b_shat_periodic (p : Fin d → ℝ) (z : Fin d → ℤ) :
    zdSymbol s (p + fun i => 2 * Real.pi * z i) = zdSymbol s p :=
  FT1a_zdSeries_periodic _ p z

private theorem FT1b_lf_shat (hs : InfKernel ψ C W s) (x : Fin d → ℤ) :
    latticeFourier (zdSymbol s) x = s x :=
  latticeFourier_zdSeries _ (FT1b_summable_s hs) x

private theorem FT1b_shat_zero (hs : InfKernel ψ C W s) : zdSymbol s 0 = 1 := by
  unfold zdSymbol zdSeries
  simp only [FT1b_zexp_zero_left, mul_one]
  rw [← Complex.ofReal_tsum, hs.sum_one, Complex.ofReal_one]

/-- `Θ_∞ = latticeFourier ψ_Θ`. -/
theorem FT1b.thetaInf_eq (s : (Fin d → ℤ) → ℝ) :
    ThetaInf s = latticeFourier (FT1b.thetaSym s) := by
  funext x
  unfold ThetaInf ThetaZd zdKernel FT1b.thetaSym
  congr 1
  funext p
  simp

private theorem FT1b_measurable_theta (hs : InfKernel ψ C W s) :
    Measurable (FT1b.thetaSym s) :=
  (FT1b_continuous_shat hs).measurable.div
    (measurable_const.sub (FT1b_continuous_shat hs).measurable)

private theorem FT1b_theta_periodic (p : Fin d → ℝ) (z : Fin d → ℤ) :
    FT1b.thetaSym s (p + fun i => 2 * Real.pi * z i) = FT1b.thetaSym s p := by
  simp only [FT1b.thetaSym, FT1b_shat_periodic]

/-- `|ψ_Θ| ≤ c⁻¹ D_W` on `[−π, π]^d`. -/
private theorem FT1b_theta_le (hs : InfKernel ψ C W s) (hW : 1 ≤ W) {c c' : ℝ} (hc : 0 < c)
    (hc' : 0 < c')
    (hr : ∀ p, (zdSymbol s p).im = 0 ∧ -1 + c' / 2 ≤ (zdSymbol s p).re ∧ (zdSymbol s p).re ≤ 1)
    (hQ : ∀ p ∈ cubePi d, c * min ((W : ℝ) ^ 2 * sqNorm p) 1 ≤ 1 - (zdSymbol s p).re)
    (p : Fin d → ℝ) (hp : p ∈ cubePi d) :
    ‖FT1b.thetaSym s p‖ ≤ c⁻¹ * FT1b.dW W p := by
  unfold FT1b.thetaSym
  have hn := FT1b_norm_shat_le hc' (hr p)
  have hW0 : (0 : ℝ) < (W : ℝ) ^ 2 := pow_pos (by exact_mod_cast (show 0 < W by omega)) 2
  rcases eq_or_lt_of_le (FT1b_sqNorm_nonneg p) with h0 | h0
  · have hp0 : p = 0 := FT1b_sqNorm_eq_zero h0.symm
    rw [hp0, FT1b_shat_zero hs, sub_self, div_zero, norm_zero]
    exact mul_nonneg (inv_nonneg.2 hc.le) (FT1b_dW_pos W 0).le
  · set a := (W : ℝ) ^ 2 * sqNorm p
    have ha : 0 < a := mul_pos hW0 h0
    have hm : 0 < min a 1 := lt_min ha one_pos
    have h1 := hQ p hp
    have hden : 0 < 1 - (zdSymbol s p).re := lt_of_lt_of_le (mul_pos hc hm) h1
    have he : (1 : ℂ) - zdSymbol s p = ((1 - (zdSymbol s p).re : ℝ) : ℂ) := by
      rw [FT1b_shat_real (hr p).1]; push_cast; simp
    rw [norm_div, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden, div_le_iff₀ hden]
    have hdm := FT1b_dW_mul_min W p
    have hdW : FT1b.dW W p * min a 1 = 1 := by
      unfold FT1b.dW
      rcases le_or_gt 1 a with h | h
      · rw [min_eq_right h, mul_one, max_eq_left (inv_le_one_of_one_le₀ h)]
      · rw [min_eq_left h.le, max_eq_right ((one_le_inv₀ ha).2 h.le), inv_mul_cancel₀ ha.ne']
    calc ‖zdSymbol s p‖ ≤ 1 := hn
      _ = c⁻¹ * FT1b.dW W p * (c * min a 1) := by field_simp; linarith [hdW]
      _ ≤ c⁻¹ * FT1b.dW W p * (1 - (zdSymbol s p).re) := by
          gcongr
          exact mul_nonneg (inv_nonneg.2 hc.le) (FT1b_dW_pos W p).le

private theorem FT1b_plus_periodic (m : ℂ) (p : Fin d → ℝ) (z : Fin d → ℤ) :
    FT1b.plusSym m s (p + fun i => 2 * Real.pi * z i) = FT1b.plusSym m s p := by
  simp only [FT1b.plusSym, FT1b_shat_periodic]

private theorem FT1b_minus_periodic (m : ℂ) (p : Fin d → ℝ) (z : Fin d → ℤ) :
    FT1b.minusSym m s (p + fun i => 2 * Real.pi * z i) = FT1b.minusSym m s p := by
  simp only [FT1b.minusSym, FT1b_shat_periodic]

/-- `ψ_±` are continuous and bounded by `b⁻¹` for `|E| ≤ 2 − κ`. -/
private theorem FT1b_pm (hs : InfKernel ψ C W s) {κ c' b E : ℝ} (hκ : 0 < κ) (hb : 0 < b)
    (hE : |E| ≤ 2 - κ)
    (hr : ∀ p, (zdSymbol s p).im = 0 ∧ -1 + c' / 2 ≤ (zdSymbol s p).re ∧ (zdSymbol s p).re ≤ 1)
    (hden : ∀ t : ℝ, -1 + c' / 2 ≤ t →
      b ≤ ‖1 - mE E ^ 2 * t‖ ∧ b ≤ ‖1 - conj (mE E) ^ 2 * t‖) (hc' : 0 < c') :
    Continuous (FT1b.plusSym (mE E) s) ∧ Continuous (FT1b.minusSym (mE E) s) ∧
      ∀ p, ‖FT1b.plusSym (mE E) s p‖ ≤ b⁻¹ ∧ ‖FT1b.minusSym (mE E) s p‖ ≤ b⁻¹ := by
  have hκ2 : |E| ≤ 2 := by linarith
  have hm1 : ‖mE E‖ = 1 := norm_mE hκ2
  have hcs := FT1b_continuous_shat hs
  have hd1 : ∀ p, b ≤ ‖1 - mE E ^ 2 * zdSymbol s p‖ := fun p => by
    rw [FT1b_shat_real (hr p).1]; exact (hden _ (hr p).2.1).1
  have hd2 : ∀ p, b ≤ ‖1 - conj (mE E) ^ 2 * zdSymbol s p‖ := fun p => by
    rw [FT1b_shat_real (hr p).1]; exact (hden _ (hr p).2.1).2
  have hn : ∀ p, ‖zdSymbol s p‖ ≤ 1 := fun p => FT1b_norm_shat_le hc' (hr p)
  refine ⟨?_, ?_, fun p => ⟨?_, ?_⟩⟩
  · exact (continuous_const.mul hcs).div (continuous_const.sub (continuous_const.mul hcs))
      fun p h => by have := hd1 p; rw [h, norm_zero] at this; linarith
  · exact (continuous_const.mul hcs).div (continuous_const.sub (continuous_const.mul hcs))
      fun p h => by have := hd2 p; rw [h, norm_zero] at this; linarith
  · unfold FT1b.plusSym
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le hb (hd1 p)), norm_mul, norm_pow, hm1, one_pow,
      one_mul]
    calc ‖zdSymbol s p‖ ≤ 1 := hn p
      _ = b⁻¹ * b := (inv_mul_cancel₀ hb.ne').symm
      _ ≤ b⁻¹ * ‖1 - mE E ^ 2 * zdSymbol s p‖ := by gcongr; exact hd1 p
  · unfold FT1b.minusSym
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le hb (hd2 p)), norm_mul, norm_pow, Complex.norm_conj,
      hm1, one_pow, one_mul]
    calc ‖zdSymbol s p‖ ≤ 1 := hn p
      _ = b⁻¹ * b := (inv_mul_cancel₀ hb.ne').symm
      _ ≤ b⁻¹ * ‖1 - conj (mE E) ^ 2 * zdSymbol s p‖ := by gcongr; exact hd2 p

/-- `S^+_∞(m) = latticeFourier ψ_+`. -/
theorem FT1b.splusInf_eq (m : ℂ) (s : (Fin d → ℤ) → ℝ) :
    SplusInf m s = latticeFourier (FT1b.plusSym m s) :=
  rfl

/-- `S^−_∞(m) = latticeFourier ψ_−` for an even summable real kernel `s`. -/
private theorem FT1b_sminusInf_eq (m : ℂ) {s : (Fin d → ℤ) → ℝ} (hs : ∀ x, s (-x) = s x)
    (hsum : Summable s) : SminusInf m s = latticeFourier (FT1b.minusSym m s) := by
  funext x
  unfold SminusInf
  rw [FT1b.splusInf_eq, FT1b_conj_lf]
  congr 1
  funext p
  have he : zdSymbol s (-p) = zdSymbol s p := ValZ_zdSymbol_neg hs p
  have hc : conj (zdSymbol s p) = zdSymbol s p :=
    Complex.conj_eq_iff_im.2 (zdSymbol_im s hs hsum p)
  simp only [FT1b.plusSym, FT1b.minusSym, he, map_div₀, map_mul, map_pow, map_sub, map_one, hc]

end Edge

/-- The kernels `S^±_∞(m(E))` are in `ℓ¹`, for `W ≥ W₀` and `|E| < 2 − κ` ([I, (7.6)]). -/
private theorem FT1b_wave_summable (hd : 6 ≤ d) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (c' : ℝ) (hψ : SymbolBound ψ c') (C : ℕ → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ E : ℝ, |E| < 2 - κ →
        Summable (fun x => ‖SplusInf (mE E) s x‖) ∧ Summable (fun x => ‖SminusInf (mE E) s x‖) := by
  obtain ⟨Kw, W₁, hKw, hb⟩ := ValZ_wave_bound hd ψ c' hψ C hκ (τc := 1) one_pos
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨CL, -, hL⟩ := latSum d (2 * d - 4) (by linarith)
  refine ⟨max W₁ 1, fun W hW s hs E hE => ?_⟩
  have hW1 : 1 ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hsum := ((hL W hW1).1).mul_left (Kw * (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ ((d : ℝ) - 4))
  have hle : ∀ x, ValZ_wb d W Kw 1 x =
      Kw * (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ ((d : ℝ) - 4) *
        ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)) := by
    intro x
    unfold ValZ_wb
    ring
  have h := hb W (le_trans (le_max_left _ _) hW) s hs E hE
  refine ⟨Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hsum,
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hsum⟩
  · rw [← hle]; exact (h x).2.1
  · rw [← hle]; exact (h x).2.2

/-! ## [I, (7.28)] on `ℤ^d` -/

end Symbols

section Chain

attribute [local instance] FT1a_isFinite_cube

open private InfKernel.weighted_sum from RBM8D.Kernel.ShellKernel

/-- The symbol of `Σ̊^∞_l` ([I, Def 8.2] on `ℤ^d`): for `d ≥ 8`, even `l ∈ [4, N]` and `τ > 0`
there are `A ≥ 0` and `W₀` with `Σ̊^∞_l ∈ ℓ¹` and
`|ψ_{Σ̊^∞_l}(p)| ≤ A W^τ W^{-(l-2)d/2} min(W²|p|², 1)` on `[−π, π]^d`, uniformly in
`|E| < 2 − κ`: the exact symbol bound together with `Σ_x |Σ̊^∞_l(0, x)| ≲ W^τ W^{-(l-2)d/2}`. -/
private theorem FT1b_labelSym (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (l : ℕ) (hl4 : 4 ≤ l) (hlN : l ≤ N)
    (hle : Even l) {τ : ℝ} (hτ : 0 < τ) :
    ∃ A W₀ : ℝ, 0 ≤ A ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      Summable (fun x => ‖ValZ.sigKer Sig P.ψ E l W x‖) ∧
      ∀ p ∈ cubePi d, ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p‖ ≤
        A * ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) *
          min ((W : ℝ) ^ 2 * sqNorm p) 1 := by
  obtain ⟨C₁, W₁, hC₁, h1⟩ := InfBound.symbolBound hd P Sig N hSig hκ l hl4 hlN hle τ hτ
  obtain ⟨W₂, h2⟩ := InfBound.sigRBound (by omega) P Sig N hSig hκ l hl4 hlN hle τ hτ
  obtain ⟨W₃, h3⟩ := InfBound.sigKerBound (by omega) P Sig N hSig hκ l hl4 hlN hle τ hτ
  obtain ⟨C, c, c', W₄, -, -, hW₄, h4⟩ := FT1b_sinf P
  set A₂ : ℝ := 1 + 3 ^ d * C (0 + 2 * d)
  refine ⟨max C₁ A₂, max (max (max W₁ W₂) W₃) W₄, le_trans hC₁ (le_max_left _ _),
    fun W hW E hE => ?_⟩
  have hW1' : W₁ ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hW
  have hW2' : W₂ ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hW
  have hW3' : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW4' : W₄ ≤ W := le_trans (le_max_right _ _) hW
  have hW1 : 1 ≤ W := by exact_mod_cast le_trans hW₄ hW4'
  have hs := (h4 W hW4').1
  obtain ⟨-, hRs, hRsum⟩ := h2 W hW2' E hE
  have hKs := (h3 W hW3' E hE).2
  refine ⟨hKs, fun p hp => ?_⟩
  set R := ∑' x, ValZ.sigR Sig (Sinf P.ψ W) W E l x
  have hws := InfKernel.weighted_sum hW1 hs 0
  simp only [pow_zero, mul_one] at hws
  have hsabs : Summable fun x => |Sinf P.ψ W x| := hws.1
  have hR : ‖R‖ ≤ ∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ := norm_tsum_le_tsum_norm hRs
  have hker : ∀ x, ‖ValZ.sigKer Sig P.ψ E l W x‖ ≤
      ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ + ‖R‖ * |Sinf P.ψ W x| := by
    intro x
    rw [ValZ.sigKer_of_tsum Sig P.ψ E l W hs.sum_one x]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hl1 : ∑' x, ‖ValZ.sigKer Sig P.ψ E l W x‖ ≤
      A₂ * ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) := by
    calc ∑' x, ‖ValZ.sigKer Sig P.ψ E l W x‖
        ≤ ∑' x, (‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ + ‖R‖ * |Sinf P.ψ W x|) :=
          hKs.tsum_le_tsum hker (hRs.add (hsabs.mul_left _))
      _ = (∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖) + ‖R‖ * ∑' x, |Sinf P.ψ W x| := by
          rw [hRs.tsum_add (hsabs.mul_left _), tsum_mul_left]
      _ ≤ (∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖) +
            (∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖) * (3 ^ d * C (0 + 2 * d)) := by
          gcongr
          exact hws.2
      _ = A₂ * ∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ := by ring
      _ ≤ A₂ * ((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ) := by
          have hA₂ : 0 ≤ A₂ := le_trans zero_le_one (le_trans (le_of_eq rfl)
            (by have := (tsum_nonneg fun x => abs_nonneg (Sinf P.ψ W x)).trans hws.2
                simp only [A₂]; linarith))
          exact mul_le_mul_of_nonneg_left hRsum hA₂
      _ = A₂ * ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) := by ring
  have hWp : (0 : ℝ) ≤ (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by positivity
  have hb1 : ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p‖ ≤
      A₂ * ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) :=
    (FT1a_norm_zdSeries_le _ hKs p).trans hl1
  have hb2 : ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p‖ ≤
      C₁ * ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) * ((W : ℝ) ^ 2 * sqNorm p) := by
    refine (h1 W hW1' E hE p hp).trans ?_
    calc C₁ * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ 2 * ‖p‖ ^ 2
        ≤ C₁ * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ 2 * sqNorm p := by
          gcongr; exact FT1b_sq_norm_le p
      _ = _ := by ring
  rcases le_total ((W : ℝ) ^ 2 * sqNorm p) 1 with h | h
  · rw [min_eq_left h]
    refine hb2.trans ?_
    gcongr
    · exact mul_nonneg (by positivity) (FT1b_sqNorm_nonneg p)
    · exact le_max_left _ _
  · rw [min_eq_right h, mul_one]
    exact hb1.trans (by gcongr; exact le_max_right _ _)

/-- One step of the chain: `(F ∗ K) ∗ Θ_∞` for `F = latticeFourier φ`, `|φ| ≤ B D_W`,
`K ∈ ℓ¹` with `|K̂| ≤ A min(W²|p|², 1)` and `Θ_∞ = latticeFourier θ`, `|θ| ≤ c⁻¹ D_W`. -/
private theorem FT1b_step (hd : 5 ≤ d) {W : ℕ} (hW : 1 ≤ W) {s : (Fin d → ℤ) → ℝ}
    {θ : (Fin d → ℝ) → ℂ} (hθ : ThetaInf s = latticeFourier θ) (hθm : Measurable θ)
    (hθp : ∀ p (z : Fin d → ℤ), θ (p + fun i => 2 * Real.pi * z i) = θ p) {c : ℝ} (hc : 0 < c)
    (hθb : ∀ p ∈ cubePi d, ‖θ p‖ ≤ c⁻¹ * FT1b.dW W p)
    {K : (Fin d → ℤ) → ℂ} (hK : Summable fun x => ‖K x‖) {A : ℝ} (hA : 0 ≤ A)
    (hKb : ∀ p ∈ cubePi d, ‖zdSeries K p‖ ≤ A * min ((W : ℝ) ^ 2 * sqNorm p) 1)
    {φ : (Fin d → ℝ) → ℂ} (hφm : Measurable φ)
    (hφp : ∀ p (z : Fin d → ℤ), φ (p + fun i => 2 * Real.pi * z i) = φ p) {B : ℝ} (hB : 0 ≤ B)
    (hφb : ∀ p ∈ cubePi d, ‖φ p‖ ≤ B * FT1b.dW W p) :
    convZ (convZ (latticeFourier φ) K) (ThetaInf s) =
        latticeFourier (fun p => φ p * zdSeries K p * θ p) ∧
      Measurable (fun p => φ p * zdSeries K p * θ p) ∧
      (∀ p (z : Fin d → ℤ), φ (p + fun i => 2 * Real.pi * z i) *
          zdSeries K (p + fun i => 2 * Real.pi * z i) * θ (p + fun i => 2 * Real.pi * z i) =
        φ p * zdSeries K p * θ p) ∧
      ∀ p ∈ cubePi d, ‖φ p * zdSeries K p * θ p‖ ≤ B * A * c⁻¹ * FT1b.dW W p := by
  have hKc := FT1a_continuous_zdSeries K hK
  have hKe : K = latticeFourier (zdSeries K) := funext fun x => (latticeFourier_zdSeries K hK x).symm
  have hφK : ∀ p ∈ cubePi d, ‖φ p * zdSeries K p‖ ≤ B * A * FT1b.dW W p := by
    intro p hp
    have hmin : min ((W : ℝ) ^ 2 * sqNorm p) 1 ≤ 1 := min_le_right _ _
    rw [norm_mul]
    calc ‖φ p‖ * ‖zdSeries K p‖ ≤ (B * FT1b.dW W p) * (A * 1) := by
          refine mul_le_mul (hφb p hp) ((hKb p hp).trans ?_) (norm_nonneg _)
            (mul_nonneg hB (FT1b_dW_pos W p).le)
          exact mul_le_mul_of_nonneg_left hmin hA
      _ = B * A * FT1b.dW W p := by ring
  have hconv1 : convZ (latticeFourier φ) K = latticeFourier (fun p => φ p * zdSeries K p) := by
    funext x
    calc convZ (latticeFourier φ) K x =
        ∑' α, latticeFourier φ α * latticeFourier (zdSeries K) (x - α) := by
          unfold convZ
          congr 1
          funext α
          rw [latticeFourier_zdSeries K hK]
      _ = _ := (FT1b_hasSum_conv φ (zdSeries K) hφm hKc.measurable hφp (FT1a_zdSeries_periodic K)
          (FT1b_memLp_of_dW hd hW hφm hφb) (FT1a_memLp_zdSeries K hK) x).tsum_eq
  have hm2 : Measurable fun p => φ p * zdSeries K p := hφm.mul hKc.measurable
  have hconv2 : convZ (latticeFourier fun p => φ p * zdSeries K p) (ThetaInf s) =
      latticeFourier (fun p => φ p * zdSeries K p * θ p) := by
    funext x
    rw [hθ]
    exact (FT1b_hasSum_conv _ θ hm2 hθm (fun p z => by simp only [hφp, FT1a_zdSeries_periodic])
      hθp (FT1b_memLp_of_dW hd hW hm2 hφK) (FT1b_memLp_of_dW hd hW hθm hθb) x).tsum_eq
  refine ⟨by rw [hconv1, hconv2], hm2.mul hθm,
    fun p z => by simp only [hφp, FT1a_zdSeries_periodic, hθp], fun p hp => ?_⟩
  have hmin := FT1b_dW_mul_min W p
  have hdW := (FT1b_dW_pos W p).le
  have hmin0 : 0 ≤ min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
    le_min (mul_nonneg (by positivity) (FT1b_sqNorm_nonneg p)) zero_le_one
  rw [norm_mul, norm_mul]
  calc ‖φ p‖ * ‖zdSeries K p‖ * ‖θ p‖
      ≤ (B * FT1b.dW W p) * (A * min ((W : ℝ) ^ 2 * sqNorm p) 1) * (c⁻¹ * FT1b.dW W p) :=
        mul_le_mul (mul_le_mul (hφb p hp) (hKb p hp) (norm_nonneg _) (mul_nonneg hB hdW))
          (hθb p hp) (norm_nonneg _) (mul_nonneg (mul_nonneg hB hdW) (mul_nonneg hA hmin0))
    _ = B * A * c⁻¹ * FT1b.dW W p * (FT1b.dW W p * min ((W : ℝ) ^ 2 * sqNorm p) 1) := by ring
    _ ≤ B * A * c⁻¹ * FT1b.dW W p * 1 :=
        mul_le_mul_of_nonneg_left hmin
          (mul_nonneg (mul_nonneg (mul_nonneg hB hA) (inv_nonneg.2 hc.le)) hdW)
    _ = B * A * c⁻¹ * FT1b.dW W p := mul_one _

/-- The chain `Θ_∞ K_{o₁} Θ_∞ ⋯ K_{o_r} Θ_∞`, started at `F = latticeFourier φ`: induction along
the labels. -/
private theorem FT1b_foldl (hd : 5 ≤ d) {W : ℕ} (hW : 1 ≤ W) {s : (Fin d → ℤ) → ℝ}
    {θ : (Fin d → ℝ) → ℂ} (hθ : ThetaInf s = latticeFourier θ) (hθm : Measurable θ)
    (hθp : ∀ p (z : Fin d → ℤ), θ (p + fun i => 2 * Real.pi * z i) = θ p) {c : ℝ} (hc : 0 < c)
    (hθb : ∀ p ∈ cubePi d, ‖θ p‖ ≤ c⁻¹ * FT1b.dW W p) (K : KerInf d) (A : ℕ → ℝ) :
    ∀ (o : List ℕ), (∀ l ∈ o, Summable (fun x => ‖K l W x‖) ∧ 0 ≤ A l ∧
      ∀ p ∈ cubePi d, ‖zdSeries (K l W) p‖ ≤ A l * min ((W : ℝ) ^ 2 * sqNorm p) 1) →
    ∀ (φ : (Fin d → ℝ) → ℂ) (B : ℝ), Measurable φ →
      (∀ p (z : Fin d → ℤ), φ (p + fun i => 2 * Real.pi * z i) = φ p) → 0 ≤ B →
      (∀ p ∈ cubePi d, ‖φ p‖ ≤ B * FT1b.dW W p) →
      o.foldl (fun F l => convZ (convZ F (K l W)) (ThetaInf s)) (latticeFourier φ) =
          latticeFourier (fun p => φ p * θ p ^ o.length *
            (o.map fun l => zdSeries (K l W) p).prod) ∧
        Measurable (fun p => φ p * θ p ^ o.length * (o.map fun l => zdSeries (K l W) p).prod) ∧
        (∀ p (z : Fin d → ℤ),
          φ (p + fun i => 2 * Real.pi * z i) * θ (p + fun i => 2 * Real.pi * z i) ^ o.length *
            (o.map fun l => zdSeries (K l W) (p + fun i => 2 * Real.pi * z i)).prod =
          φ p * θ p ^ o.length * (o.map fun l => zdSeries (K l W) p).prod) ∧
        ∀ p ∈ cubePi d, ‖φ p * θ p ^ o.length * (o.map fun l => zdSeries (K l W) p).prod‖ ≤
          B * ((o.map A).prod * c⁻¹ ^ o.length) * FT1b.dW W p := by
  intro o
  induction o with
  | nil =>
    intro _ φ B hφm hφp _ hφb
    refine ⟨by simp, by simpa using hφm, fun p z => by simp [hφp], fun p hp => by
      simpa using hφb p hp⟩
  | cons l o ih =>
    intro hK φ B hφm hφp hB hφb
    obtain ⟨hKs, hA, hKb⟩ := hK l List.mem_cons_self
    obtain ⟨h1, h2, h3, h4⟩ := FT1b_step hd hW hθ hθm hθp hc hθb hKs hA hKb hφm hφp hB hφb
    have hB' : 0 ≤ B * A l * c⁻¹ := mul_nonneg (mul_nonneg hB hA) (inv_nonneg.2 hc.le)
    obtain ⟨g1, g2, g3, g4⟩ := ih (fun l' hl' => hK l' (List.mem_cons_of_mem l hl')) _ _ h2 h3 hB'
      h4
    have hfun : (fun p => (φ p * zdSeries (K l W) p * θ p) * θ p ^ o.length *
        (o.map fun l => zdSeries (K l W) p).prod) =
        (fun p => φ p * θ p ^ (l :: o).length *
          ((l :: o).map fun l => zdSeries (K l W) p).prod) := by
      funext p
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      ring
    rw [hfun] at g1 g2
    refine ⟨by rw [List.foldl_cons, h1, g1], g2, fun p z => ?_, fun p hp => ?_⟩
    · have := g3 p z
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ] at this ⊢
      linear_combination this
    · have e : φ p * θ p ^ (l :: o).length *
          ((l :: o).map fun l => zdSeries (K l W) p).prod =
          φ p * zdSeries (K l W) p * θ p * θ p ^ o.length *
            (o.map fun l => zdSeries (K l W) p).prod := by
        simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
        ring
      rw [e]
      refine (g4 p hp).trans (le_of_eq ?_)
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      ring

/-- `Π_{l ∈ o} W^τ W^{-(l-2)d/2} = W^{|o|τ − Σ_{l ∈ o} (l-2)d/2}` for `W > 0`. -/
private theorem FT1b_prod_rpow {W : ℝ} (hW : 0 < W) (τ : ℝ) (o : List ℕ) :
    (o.map fun l : ℕ => W ^ τ * W ^ (-(((l : ℝ) - 2) * d / 2))).prod =
      W ^ ((o.length : ℝ) * τ - (o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) := by
  induction o with
  | nil => simp
  | cons l o ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons, ih]
    rw [← Real.rpow_add hW, ← Real.rpow_add hW]
    congr 1
    push_cast
    ring

/-- **[I, (7.28)] on `ℤ^d`**: for `d ≥ 8`, a profile `P`, a family `Sig` whose even orders
`4 ≤ k ≤ N` have the shape of a `k`-th order self-energy, `κ > 0`, a label `o` with entries even in
`[4, N]` and `τ > 0`, there are `C ≥ 0` and `W₀` such that for `W ≥ W₀` and `|E| < 2 − κ` the chain
`Θ_∞ Σ̊^∞_{o₁} Θ_∞ ⋯ Σ̊^∞_{o_r} Θ_∞` (`chainZ` at `S_∞ = Sinf P.ψ W` and the label kernels
`Σ̊^∞ = ValZ.sigKer Sig P.ψ E`) is `latticeFourier ψ_o` with
`ψ_o = ψ_Θ^{r+1} Π_i ψ_{Σ̊^∞_{o_i}}` (`FT1b.chainSym`) measurable, `2π`-periodic, in
`L¹ ∩ L²([−π, π]^d)`, and `|ψ_o(p)| ≤ C W^{rτ − Σ_i (o_i − 2)d/2} D_W(p)` on `[−π, π]^d`. -/
theorem FT1b.chainFourier (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (o : List ℕ)
    (ho : labelOK N o = true) {τ : ℝ} (hτ : 0 < τ) :
    ∃ C W₀ : ℝ, 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o =
          latticeFourier (FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o) ∧
        Measurable (FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o) ∧
        (∀ p (z : Fin d → ℤ),
          FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o
              (p + fun i => 2 * Real.pi * z i) =
            FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p) ∧
        MemLp (FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o) 2
          (volume.restrict (cubePi d)) ∧
        IntegrableOn (FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o) (cubePi d) ∧
        ∀ p ∈ cubePi d, ‖FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p‖ ≤
          C * (W : ℝ) ^ ((o.length : ℝ) * τ - (o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) *
            FT1b.dW W p := by
  have hlab : ∀ l ∈ o, 4 ≤ l ∧ l ≤ N ∧ Even l := by
    intro l hl
    have h := List.all_eq_true.1 ho l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, Nat.even_iff.2 h.2⟩
  have hex : ∀ l : ℕ, ∃ A W₀ : ℝ, (4 ≤ l → l ≤ N → Even l → 0 ≤ A ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E : ℝ, |E| < 2 - κ → Summable (fun x => ‖ValZ.sigKer Sig P.ψ E l W x‖) ∧
        ∀ p ∈ cubePi d, ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p‖ ≤
          A * ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) *
            min ((W : ℝ) ^ 2 * sqNorm p) 1) := by
    intro l
    by_cases h : 4 ≤ l ∧ l ≤ N ∧ Even l
    · obtain ⟨A, W₀, hA, hW⟩ := FT1b_labelSym hd P Sig N hSig hκ l h.1 h.2.1 h.2.2 hτ
      exact ⟨A, W₀, fun _ _ _ => ⟨hA, hW⟩⟩
    · exact ⟨0, 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose Af Wf hAW using hex
  obtain ⟨C, c, c', W₁, hc, hc', hW₁, hsym⟩ := FT1b_sinf P
  refine ⟨c⁻¹ * ((o.map Af).prod * c⁻¹ ^ o.length), (o.map Wf).foldr max W₁, ?_,
    fun W hW E hE => ?_⟩
  · refine mul_nonneg (inv_nonneg.2 hc.le) (mul_nonneg ?_ (pow_nonneg (inv_nonneg.2 hc.le) _))
    exact List.prod_nonneg fun a ha => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ha
      exact (hAW l (hlab l hl).1 (hlab l hl).2.1 (hlab l hl).2.2).1
  have hWl : ∀ l ∈ o, Wf l ≤ W := by
    intro l hl
    refine le_trans ?_ hW
    clear hW hlab hAW ho
    induction o with
    | nil => exact absurd hl List.not_mem_nil
    | cons a o ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.1 hl with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)
  have hW1' : W₁ ≤ W := by
    refine le_trans ?_ hW
    clear hW hWl hlab hAW ho
    induction o with
    | nil => exact le_rfl
    | cons a o ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact le_trans ih (le_max_right _ _)
  obtain ⟨hs, hr, hQ⟩ := hsym W hW1'
  have hW1 : 1 ≤ W := by exact_mod_cast le_trans hW₁ hW1'
  have hd5 : 5 ≤ d := by omega
  have hθb := FT1b_theta_le hs hW1 hc hc'.pos hr hQ
  have hθm := FT1b_measurable_theta hs
  obtain ⟨g1, g2, g3, g4⟩ := FT1b_foldl hd5 hW1 (FT1b.thetaInf_eq (Sinf P.ψ W)) hθm
    FT1b_theta_periodic hc hθb (ValZ.sigKer Sig P.ψ E)
    (fun l => Af l * ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)))) o
    (fun l hl => by
      obtain ⟨hA, hWA⟩ := hAW l (hlab l hl).1 (hlab l hl).2.1 (hlab l hl).2.2
      obtain ⟨h1, h2⟩ := hWA W (hWl l hl) E hE
      exact ⟨h1, by positivity, h2⟩)
    (FT1b.thetaSym (Sinf P.ψ W)) c⁻¹ hθm FT1b_theta_periodic (inv_nonneg.2 hc.le) hθb
  have hfun : (fun p => FT1b.thetaSym (Sinf P.ψ W) p * FT1b.thetaSym (Sinf P.ψ W) p ^ o.length *
      (o.map fun l => zdSeries (ValZ.sigKer Sig P.ψ E l W) p).prod) =
      FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o := by
    funext p
    simp only [FT1b.chainSym, pow_succ]
    ring
  rw [hfun] at g1 g2
  have hchain : chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o =
      latticeFourier (FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o) := by
    unfold chainZ
    rw [FT1b.thetaInf_eq (Sinf P.ψ W)] at g1 ⊢
    rw [← g1]
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hprod : (o.map fun l => Af l * ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)))).prod =
      (o.map Af).prod * (W : ℝ) ^ ((o.length : ℝ) * τ -
        (o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) := by
    rw [← FT1b_prod_rpow hWpos τ o, ← List.prod_map_mul]
  have hbound : ∀ p ∈ cubePi d, ‖FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p‖ ≤
      c⁻¹ * ((o.map Af).prod * c⁻¹ ^ o.length) *
        (W : ℝ) ^ ((o.length : ℝ) * τ - (o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) *
          FT1b.dW W p := by
    intro p hp
    rw [← congrFun hfun p]
    refine (g4 p hp).trans (le_of_eq ?_)
    rw [hprod]
    ring
  have hL2 := FT1b_memLp_of_dW hd5 hW1 g2 hbound
  refine ⟨hchain, g2, fun p z => ?_, hL2, hL2.integrable one_le_two, hbound⟩
  have e1 := congrFun hfun (p + fun i => 2 * Real.pi * z i)
  have e2 := congrFun hfun p
  rw [← e1, ← e2]
  exact g3 p z

/-- **The edge symbols** ([I, (7.3)–(7.5)] on `ℤ^d`): for `d ≥ 5`, a profile `P` and `κ > 0` there
are `c, b > 0` and `W₀` such that for `W ≥ W₀` and `|E| < 2 − κ`, with `s = S_∞ = Sinf P.ψ W` and
`m = m(E)`: `s`, `S^±_∞(m)` and `Θ_∞` are the kernels `latticeFourier` of `ŝ`, `ψ_±` and
`ψ_Θ = ŝ/(1 − ŝ)`; the four symbols are measurable, `2π`-periodic and in `L²([−π, π]^d)`;
`|ŝ| ≤ 1`, `|ψ_±| ≤ b⁻¹` everywhere and `|ψ_Θ| ≤ c⁻¹ D_W` on `[−π, π]^d`. -/
theorem FT1b.edgeSymbols (hd : 5 ≤ d) (P : Profile d) {κ : ℝ} (hκ : 0 < κ) :
    ∃ c b W₀ : ℝ, 0 < c ∧ 0 < b ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      latticeFourier (zdSymbol (Sinf P.ψ W)) = (fun x => (Sinf P.ψ W x : ℂ)) ∧
      SplusInf (mE E) (Sinf P.ψ W) = latticeFourier (FT1b.plusSym (mE E) (Sinf P.ψ W)) ∧
      SminusInf (mE E) (Sinf P.ψ W) = latticeFourier (FT1b.minusSym (mE E) (Sinf P.ψ W)) ∧
      ThetaInf (Sinf P.ψ W) = latticeFourier (FT1b.thetaSym (Sinf P.ψ W)) ∧
      Measurable (zdSymbol (Sinf P.ψ W)) ∧ Measurable (FT1b.plusSym (mE E) (Sinf P.ψ W)) ∧
      Measurable (FT1b.minusSym (mE E) (Sinf P.ψ W)) ∧ Measurable (FT1b.thetaSym (Sinf P.ψ W)) ∧
      (∀ p (z : Fin d → ℤ),
        zdSymbol (Sinf P.ψ W) (p + fun i => 2 * Real.pi * z i) = zdSymbol (Sinf P.ψ W) p ∧
        FT1b.plusSym (mE E) (Sinf P.ψ W) (p + fun i => 2 * Real.pi * z i) =
          FT1b.plusSym (mE E) (Sinf P.ψ W) p ∧
        FT1b.minusSym (mE E) (Sinf P.ψ W) (p + fun i => 2 * Real.pi * z i) =
          FT1b.minusSym (mE E) (Sinf P.ψ W) p ∧
        FT1b.thetaSym (Sinf P.ψ W) (p + fun i => 2 * Real.pi * z i) =
          FT1b.thetaSym (Sinf P.ψ W) p) ∧
      MemLp (zdSymbol (Sinf P.ψ W)) 2 (volume.restrict (cubePi d)) ∧
      MemLp (FT1b.plusSym (mE E) (Sinf P.ψ W)) 2 (volume.restrict (cubePi d)) ∧
      MemLp (FT1b.minusSym (mE E) (Sinf P.ψ W)) 2 (volume.restrict (cubePi d)) ∧
      MemLp (FT1b.thetaSym (Sinf P.ψ W)) 2 (volume.restrict (cubePi d)) ∧
      (∀ p, ‖zdSymbol (Sinf P.ψ W) p‖ ≤ 1 ∧ ‖FT1b.plusSym (mE E) (Sinf P.ψ W) p‖ ≤ b⁻¹ ∧
        ‖FT1b.minusSym (mE E) (Sinf P.ψ W) p‖ ≤ b⁻¹) ∧
      ∀ p ∈ cubePi d, ‖FT1b.thetaSym (Sinf P.ψ W) p‖ ≤ c⁻¹ * FT1b.dW W p := by
  obtain ⟨C, c, c', W₁, hc, hc', hW₁, hsym⟩ := FT1b_sinf P
  obtain ⟨b, hb, hden⟩ := FT1b_denom hκ hc'.pos
  refine ⟨c, b, W₁, hc, hb, fun W hW E hE => ?_⟩
  obtain ⟨hs, hr, hQ⟩ := hsym W hW
  have hW1 : 1 ≤ W := by exact_mod_cast le_trans hW₁ hW
  obtain ⟨hpc, hmc, hpm⟩ := FT1b_pm hs hκ hb hE.le hr (hden E hE.le) hc'.pos
  have hsum : Summable (Sinf P.ψ W) := by
    by_contra h
    have := hs.sum_one
    rw [tsum_eq_zero_of_not_summable h] at this
    exact zero_ne_one this
  have hθb := FT1b_theta_le hs hW1 hc hc'.pos hr hQ
  have hθm := FT1b_measurable_theta hs
  exact ⟨funext (FT1b_lf_shat hs), FT1b.splusInf_eq _ _,
    FT1b_sminusInf_eq _ (ValZ.Sinf_neg P.ψ W) hsum, FT1b.thetaInf_eq _,
    (FT1b_continuous_shat hs).measurable, hpc.measurable, hmc.measurable, hθm,
    fun p z => ⟨FT1b_shat_periodic p z, FT1b_plus_periodic _ p z, FT1b_minus_periodic _ p z,
      FT1b_theta_periodic p z⟩,
    FT1a_memLp_zdSeries _ (FT1b_summable_s hs),
    MemLp.of_bound hpc.aestronglyMeasurable b⁻¹ (Eventually.of_forall fun p => (hpm p).1),
    MemLp.of_bound hmc.aestronglyMeasurable b⁻¹ (Eventually.of_forall fun p => (hpm p).2),
    FT1b_memLp_of_dW hd hW1 hθm hθb,
    fun p => ⟨FT1b_norm_shat_le hc'.pos (hr p), (hpm p).1, (hpm p).2⟩, hθb⟩

end Chain


/-! ## The momentum form of a graph of `Σ` -/

section Graphs

attribute [local instance] FT1a_isFinite_cube

/-- The external momenta of [I, (7.29)] for a graph of `Σ_l`: `−p` at `x = 0`, `p` at `y = 1` and
`0` at the internal atoms. -/
def FT1b.extP {n : ℕ} (p : Fin d → ℝ) : Atom 2 n → Fin d → ℝ :=
  Sum.elim ![-p, p] 0

/-- The ends `(x_c, y_c)` of the components of a graph. -/
def FT1b.ends {n : ℕ} (Γ : Graph 2 n) (c : Fin Γ.comps.length) : Atom 2 n × Atom 2 n :=
  (Γ.comps[c].x, Γ.comps[c].y)

/-- The momentum integral of [I, (7.30)] for a graph `Γ` of `Σ_l`, a spanning tree `T` of its atoms
and the symbols `f` of the component kinds:
`(2π)^{-dL} ∫_{[−π,π]^{dL}} Π_c f_{κ_c}(ℓ_c(q) + λ_c(P)) dq` with `L = |E| − |T|` loop momenta and
the external momenta `P = (−p, p, 0, …)` (`FT1a.edgeMom`). -/
def FT1b.momInt {n : ℕ} (Γ : Graph 2 n) (T : List (Fin Γ.comps.length))
    (f : Kind → (Fin d → ℝ) → ℂ) (p : Fin d → ℝ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T}))⁻¹ *
    ∫ q in Set.univ.pi fun _ => cubePi d,
      ∏ c, f Γ.comps[c].kind (FT1a.edgeMom (FT1b.ends Γ) T (FT1b.extP p) q c)

/-- A graph of `Σ_l` in momentum form: a graph `Γ` and two lists `T₁`, `T₂` of its components. -/
structure FT1b.MomGraph where
  n : ℕ
  Γ : Graph 2 n
  T₁ : List (Fin Γ.comps.length)
  T₂ : List (Fin Γ.comps.length)

/-- `G` is a momentum form of the graph `g` of `Σ_l`: `G.Γ` has the shape of an `l`-th order
self-energy and the value of `g` on every record on `ℤ^d`; `T₁`, `T₂` are spanning trees of its
atoms whose common components are waved or dotted, unless `G.Γ` has a `×`-dotted edge (then its
value is `0`). -/
def FT1b.MomGraph.Spec (l : ℕ) (g : Σ n : ℕ, Graph 2 n) (G : FT1b.MomGraph) : Prop :=
  SelfEnergyShape l [⟨G.n, G.Γ⟩] ∧
    (∀ (d : ℕ) (D : ValZ.Rec d) (e : Fin 2 → Fin d → ℤ), ValZ.val G.Γ D e = ValZ.val g.2 D e) ∧
    TreeEdges (G.T₁.map (FT1b.ends G.Γ)) ∧ TreeEdges (G.T₂.map (FT1b.ends G.Γ)) ∧
    ((∀ c ∈ G.T₁, c ∈ G.T₂ → (∃ w, G.Γ.comps[c].kind = .waved w) ∨ G.Γ.comps[c].kind = .dot) ∨
      ∃ c : Fin G.Γ.comps.length, G.Γ.comps[c].kind = .xdot)

/-- The term `c_Γ(m) M_Γ(p)` of the momentum form: the coefficient at `m` times the momentum
integral over the tree `T₁` with the symbols `FT1b.kindSym s K W m`. -/
def FT1b.MomGraph.sym (G : FT1b.MomGraph) (s : (Fin d → ℤ) → ℝ) (K : KerInf d) (W : ℕ) (m : ℂ)
    (p : Fin d → ℝ) : ℂ :=
  G.Γ.coeff.eval m * FT1b.momInt G.Γ G.T₁ (FT1b.kindSym s K W m) p

/-- The labellings with `σ_x = 0` are the pairs `(σ_y, σ_int)`. -/
private def FT1b_equiv (n : ℕ) :
    {σ : Atom 2 n → Fin d → ℤ // σ (Sum.inl 0) = 0} ≃ (Fin d → ℤ) × (Fin n → Fin d → ℤ) where
  toFun σ := (σ.1 (Sum.inl 1), fun j => σ.1 (Sum.inr j))
  invFun ys := ⟨Sum.elim ![0, ys.1] ys.2, rfl⟩
  left_inv σ := by
    apply Subtype.ext
    funext u
    rcases u with a | j
    · fin_cases a
      · exact σ.2.symm
      · rfl
    · rfl
  right_inv ys := rfl

private theorem FT1b_prod_extP {n : ℕ} (p : Fin d → ℝ) (x : Fin d → ℤ)
    (s : Fin n → Fin d → ℤ) :
    ∏ v, zexp (FT1b.extP p v) (Sum.elim ![0, x] s v) = zexp p x := by
  rw [Fintype.prod_sum_type]
  simp [FT1b.extP, Fin.prod_univ_two, FT1b_zexp_zero, FT1b_zexp_zero_left]

/-- The row sum with a phase as a sum over the labellings with `σ_x = 0`. -/
private theorem FT1b_hasSum_row {n : ℕ} (Γ : Graph 2 n) (D : ValZ.Rec d) (p : Fin d → ℝ)
    (hsum : Summable fun xs : (Fin d → ℤ) × (Fin n → Fin d → ℤ) =>
      ‖ValZ.term Γ D (Sum.elim ![0, xs.1] xs.2)‖) :
    HasSum (fun x => ValZ.val Γ D ![0, x] * zexp p x)
      (Γ.coeff.eval D.m * ∑' σ : {σ : Atom 2 n → Fin d → ℤ // σ (Sum.inl 0) = 0},
        (∏ c : Fin Γ.comps.length, ValZ.compVal D σ.1 Γ.comps[c]) *
          ∏ v, zexp (FT1b.extP p v) (σ.1 v)) := by
  set T : (Fin d → ℤ) × (Fin n → Fin d → ℤ) → ℂ :=
    fun xs => ValZ.term Γ D (Sum.elim ![0, xs.1] xs.2) * zexp p xs.1 with hT
  have hTs : Summable T := by
    refine Summable.of_norm ?_
    simpa [hT, norm_mul, norm_zexp] using hsum
  have hfib : ∀ x, HasSum (fun s => T (x, s)) (ValZ.val Γ D ![0, x] * zexp p x) := by
    intro x
    unfold ValZ.val
    rw [← tsum_mul_right]
    exact (hTs.prod_factor x).hasSum
  have h1 := hTs.hasSum.prod_fiberwise hfib
  convert h1 using 1
  set G : {σ : Atom 2 n → Fin d → ℤ // σ (Sum.inl 0) = 0} → ℂ := fun σ =>
    (∏ c : Fin Γ.comps.length, ValZ.compVal D σ.1 Γ.comps[c]) *
      ∏ v, zexp (FT1b.extP p v) (σ.1 v)
  have hTG : ∀ xs, T xs = Γ.coeff.eval D.m * G ((FT1b_equiv n).symm xs) := by
    rintro ⟨x, s⟩
    have he : ((FT1b_equiv (d := d) n).symm (x, s)).1 = Sum.elim ![0, x] s := rfl
    simp only [hT, G, ValZ.term, he, FT1b_prod_extP]
    rw [← Fin.prod_univ_fun_getElem]
    simp only [Fin.getElem_fin]
    ring
  rw [← tsum_mul_left, ← (FT1b_equiv n).symm.tsum_eq]
  exact (tsum_congr hTG).symm

open private InfBound_W₀_list from RBM8D.SelfEnergy.InfBound

/-- The components of a deterministic graph of `Σ_l` on `ℤ^d`, for `W ≥ W₀` and `|E| < 2 − κ`:
every symbol `FT1b.kindSym` of a component kind is measurable, `2π`-periodic and in
`L²([−π, π]^d)`; for a waved or dotted edge the kernel is in `ℓ¹` and the symbol is its Fourier
series; and the factor of a component on `ℤ^d` is the kernel `latticeFourier` of its symbol at
`σ_y − σ_x` (a `×`-dotted edge being a loop). -/
private theorem FT1b_edgeData (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig (l - 1)) {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (Γ : Graph 2 n)
    (hdet : Γ.comps.all (Comp.isDetKind (l - 1)) = true) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ c ∈ Γ.comps,
      Measurable (FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) c.kind) ∧
      (∀ p (z : Fin d → ℤ),
        FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) c.kind
            (p + fun i => 2 * Real.pi * z i) =
          FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) c.kind p) ∧
      MemLp (FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) c.kind) 2
        (volume.restrict (cubePi d)) ∧
      ((∃ w, c.kind = .waved w) ∨ c.kind = .dot →
        (Summable fun x => ‖latticeFourier
          (FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) c.kind) x‖) ∧
        FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) c.kind =
          zdSeries (latticeFourier
            (FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) c.kind))) ∧
      ((c.kind = .xdot → c.x = c.y) → ∀ σ : Atom 2 n → Fin d → ℤ,
        ValZ.compVal (ValZ.rec (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W E) σ c =
          latticeFourier (FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) c.kind)
            (σ c.y - σ c.x)) := by
  obtain ⟨C, c₀, c', W₁, hc₀, hc', hW₁, hsym⟩ := FT1b_sinf P
  obtain ⟨b, hb, hden⟩ := FT1b_denom hκ hc'.pos
  obtain ⟨W₂, hwave⟩ := FT1b_wave_summable (by omega) P.ψ c' hc' C hκ
  obtain ⟨W₃, hW₃⟩ := InfBound_W₀_list Γ.comps (fun c W => ∀ o, c.kind = .theta o →
      ∀ E : ℝ, |E| < 2 - κ →
        chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o =
            latticeFourier (FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o) ∧
          Measurable (FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o) ∧
          (∀ p (z : Fin d → ℤ),
            FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o
                (p + fun i => 2 * Real.pi * z i) =
              FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p) ∧
          MemLp (FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o) 2
            (volume.restrict (cubePi d)))
    (fun c hc => by
      by_cases hk : ∃ o, c.kind = .theta o
      · obtain ⟨o, ho⟩ := hk
        have h := List.all_eq_true.1 hdet c hc
        simp only [Comp.isDetKind, ho, Bool.and_eq_true] at h
        obtain ⟨Cc, Wc, -, hWc⟩ := FT1b.chainFourier hd P Sig (l - 1) hSig hκ o h.2 one_pos
        refine ⟨Wc, fun W hW o' ho' E hE => ?_⟩
        rw [ho] at ho'
        cases ho'
        obtain ⟨g1, g2, g3, g4, -, -⟩ := hWc W hW E hE
        exact ⟨g1, g2, g3, g4⟩
      · exact ⟨0, fun W _ o ho => absurd ⟨o, ho⟩ hk⟩)
  refine ⟨max (max (max W₁ W₂) W₃) 1, fun W hW E hE c hc => ?_⟩
  have hW1' : W₁ ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hW
  have hW2' : W₂ ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hW
  have hW3' : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  obtain ⟨hs, hr, -⟩ := hsym W hW1'
  obtain ⟨hpc, hmc, hpm⟩ := FT1b_pm hs hκ hb hE.le hr (hden E hE.le) hc'.pos
  obtain ⟨hSp, hSm⟩ := hwave W hW2' _ hs E hE
  have hsum : Summable (Sinf P.ψ W) := by
    by_contra h
    have := hs.sum_one
    rw [tsum_eq_zero_of_not_summable h] at this
    exact zero_ne_one this
  have hdc := List.all_eq_true.1 hdet c hc
  rcases hkc : c.kind with ch | ch | ch | ch | ⟨ch, D'⟩ | w | o | ⟨n', D'⟩ | _ | ⟨j, r, bb⟩ | _ | _
  all_goals simp only [Comp.isDetKind, hkc, Bool.and_false, Bool.false_eq_true] at hdc
  · -- waved
    cases w with
    | s =>
      have hlf : latticeFourier (zdSymbol (Sinf P.ψ W)) = fun x => ((Sinf P.ψ W x : ℝ) : ℂ) :=
        funext (FT1b_lf_shat hs)
      refine ⟨(FT1b_continuous_shat hs).measurable, FT1b_shat_periodic,
        FT1a_memLp_zdSeries _ (FT1b_summable_s hs), fun _ => ?_, fun _ σ => ?_⟩
      · simp only [FT1b.kindSym, hlf]
        exact ⟨FT1b_summable_s hs, rfl⟩
      · simp only [FT1b.kindSym, ValZ.compVal, hkc, ValZ.rec, FT1b_lf_shat hs]
    | plus =>
      refine ⟨hpc.measurable, FT1b_plus_periodic (mE E), MemLp.of_bound hpc.aestronglyMeasurable b⁻¹
        (Eventually.of_forall fun p => (hpm p).1), fun _ => ?_, fun _ σ => ?_⟩
      · simp only [FT1b.kindSym]
        exact ⟨hSp, FT1b_eq_zdSeries _ hpc (FT1b_plus_periodic (mE E)) hSp⟩
      · simp only [FT1b.kindSym, ValZ.compVal, hkc, ValZ.rec, FT1b.splusInf_eq]
    | minus =>
      have hm' : SminusInf (mE E) (Sinf P.ψ W) =
          latticeFourier (FT1b.minusSym (mE E) (Sinf P.ψ W)) :=
        FT1b_sminusInf_eq (mE E) (ValZ.Sinf_neg P.ψ W) hsum
      have hSm' : Summable fun x => ‖latticeFourier (FT1b.minusSym (mE E) (Sinf P.ψ W)) x‖ := by
        rw [← hm']; exact hSm
      refine ⟨hmc.measurable, FT1b_minus_periodic (mE E),
        MemLp.of_bound hmc.aestronglyMeasurable b⁻¹ (Eventually.of_forall fun p => (hpm p).2),
        fun _ => ⟨hSm', FT1b_eq_zdSeries _ hmc (FT1b_minus_periodic (mE E)) hSm'⟩,
        fun _ σ => ?_⟩
      simp only [FT1b.kindSym, ValZ.compVal, hkc, ValZ.rec, hm']
  · -- theta
    obtain ⟨g1, g2, g3, g4⟩ := hW₃ W hW3' c hc o hkc E hE
    refine ⟨g2, g3, g4, fun h => ?_, fun _ σ => ?_⟩
    · rcases h with ⟨w, hw⟩ | hw <;> cases hw
    · simp only [FT1b.kindSym, ValZ.compVal, hkc, ValZ.rec, g1]
  · -- dot
    have hlf : latticeFourier (fun _ : Fin d → ℝ => (1 : ℂ)) =
        fun x : Fin d → ℤ => if x = 0 then (1 : ℂ) else 0 := funext FT1b.lf_one
    refine ⟨measurable_const, fun _ _ => rfl, memLp_const 1, fun _ => ?_, fun _ σ => ?_⟩
    · simp only [FT1b.kindSym, hlf]
      refine ⟨summable_of_ne_finset_zero (s := {0}) fun x hx => ?_, ?_⟩
      · simp only [Finset.mem_singleton] at hx
        simp [hx]
      · funext p
        exact (FT1b_zdSeries_delta p).symm
    · simp only [FT1b.kindSym, ValZ.compVal, hkc, FT1b.lf_one, sub_eq_zero]
      by_cases h : σ c.x = σ c.y
      · simp [h]
      · simp [h, Ne.symm h]
  · -- xdot
    refine ⟨measurable_const, fun _ _ => rfl, memLp_const 0, fun h => ?_, fun hxy σ => ?_⟩
    · rcases h with ⟨w, hw⟩ | hw <;> cases hw
    · simp only [FT1b.kindSym, ValZ.compVal, hkc, hxy rfl, FT1b_lf_zero, ite_true]

open private dc_trees from RBM8D.Bound.DoublyDet
open private ValZ_shape from RBM8D.SelfEnergy.ValZ
open private latSum from RBM8D.Bound.AuxTreeZ

/-- Atoms with the same image under `f` are joined by the edge `e i₀` of the list. -/
private theorem FT1b_fiber_reach {V V' ι : Type*} (f : V → V') (e : ι → V × V) (i₀ : ι)
    (L : List ι) (hi : i₀ ∈ L)
    (hfib : ∀ u v, f u = f v → u = v ∨ (u, v) = e i₀ ∨ (v, u) = e i₀) {u v : V} (h : f u = f v) :
    (SimpleGraph.fromRel fun a b => (a, b) ∈ L.map e).Reachable u v := by
  rcases hfib u v h with rfl | h1 | h1
  · rfl
  · by_cases huv : u = v
    · rw [huv]
    · exact SimpleGraph.Adj.reachable ⟨huv, Or.inl (List.mem_map.2 ⟨i₀, hi, h1.symm⟩)⟩
  · by_cases huv : u = v
    · rw [huv]
    · exact SimpleGraph.Adj.reachable ⟨huv, Or.inr (List.mem_map.2 ⟨i₀, hi, h1.symm⟩)⟩

/-- A spanning tree of the graph with two atoms identified (by `f`), with the edge `e i₀` joining
the two identified atoms added, is a spanning tree. -/
private theorem FT1b_lift_tree {V V' ι ι' : Type*} [Fintype V] [Fintype V'] (f : V → V')
    (e : ι → V × V) (e' : ι' → V' × V') (j : ι' → ι)
    (hj : ∀ k, e' k = (f (e (j k)).1, f (e (j k)).2)) (T' : List ι') (hT' : TreeEdges (T'.map e'))
    (i₀ : ι) (hcard : Fintype.card V = Fintype.card V' + 1)
    (hfib : ∀ u v, f u = f v → u = v ∨ (u, v) = e i₀ ∨ (v, u) = e i₀) :
    TreeEdges ((i₀ :: T'.map j).map e) := by
  set L := i₀ :: T'.map j
  refine ⟨?_, ?_⟩
  · simp only [L, List.map_cons, List.length_cons, List.length_map]
    have := hT'.1
    simp only [List.length_map] at this
    omega
  · have hmem : i₀ ∈ L := List.mem_cons_self
    have key : ∀ a b : V', (SimpleGraph.fromRel fun u v => (u, v) ∈ T'.map e').Reachable a b →
        ∀ u v, f u = a → f v = b →
          (SimpleGraph.fromRel fun a b => (a, b) ∈ L.map e).Reachable u v := by
      intro a b hab
      obtain ⟨w⟩ := hab
      induction w with
      | nil => intro u v hu hv; exact FT1b_fiber_reach f e i₀ L hmem hfib (hu.trans hv.symm)
      | @cons a c b hadj w ih =>
        intro u v hu hv
        obtain ⟨-, hr⟩ := hadj
        have hedge : ∃ k ∈ T', (e' k = (a, c) ∨ e' k = (c, a)) := by
          rcases hr with h | h
          · obtain ⟨k, hk, he⟩ := List.mem_map.1 h
            exact ⟨k, hk, Or.inl he⟩
          · obtain ⟨k, hk, he⟩ := List.mem_map.1 h
            exact ⟨k, hk, Or.inr he⟩
        obtain ⟨k, hk, hek⟩ := hedge
        have hjL : j k ∈ L := List.mem_cons_of_mem _ (List.mem_map.2 ⟨k, hk, rfl⟩)
        have hjk := hj k
        have hxy : (SimpleGraph.fromRel fun a b => (a, b) ∈ L.map e).Reachable
            (e (j k)).1 (e (j k)).2 := by
          by_cases h : (e (j k)).1 = (e (j k)).2
          · rw [h]
          · exact SimpleGraph.Adj.reachable ⟨h, Or.inl (List.mem_map.2 ⟨j k, hjL, rfl⟩)⟩
        rcases hek with h | h
        · rw [h] at hjk
          obtain ⟨h1, h2⟩ := Prod.mk.inj hjk
          exact (FT1b_fiber_reach f e i₀ L hmem hfib (hu.trans h1)).trans
            (hxy.trans (ih (e (j k)).2 v h2.symm hv))
        · rw [h] at hjk
          obtain ⟨h1, h2⟩ := Prod.mk.inj hjk
          exact (FT1b_fiber_reach f e i₀ L hmem hfib (hu.trans h2)).trans
            (hxy.symm.trans (ih (e (j k)).1 v h1.symm hv))
    intro u v
    exact key (f u) (f v) (hT'.2 (f u) (f v)) u v rfl rfl

/-- Two spanning trees of the atoms of a graph of `Σ_l` after the contraction: from the doubly
connected internal form ([I, Def 6.5]) when it is normal regular (common components waved), with
the dotted edge `x – y` added to the two trees of the identified graph when it is diagonal, or any
spanning tree when it has a `×`-dotted edge. -/
private theorem FT1b_trees {l n : ℕ} (Γ : Graph 2 n) (hΓ : SelfEnergyShape l [⟨n, Γ⟩])
    (hcase : (∃ C, Γ.internalize.Normal C) ∨ G13.IsDiag Γ) :
    ∃ T₁ T₂ : List (Fin Γ.comps.length), TreeEdges (T₁.map (FT1b.ends Γ)) ∧
      TreeEdges (T₂.map (FT1b.ends Γ)) ∧
      ((∀ c ∈ T₁, c ∈ T₂ → (∃ w, Γ.comps[c].kind = .waved w) ∨ Γ.comps[c].kind = .dot) ∨
        ∃ c : Fin Γ.comps.length, Γ.comps[c].kind = .xdot) := by
  obtain ⟨⟨Cn, hN, hA⟩, hKd, -, hDC⟩ := hΓ _ (List.mem_singleton_self _)
  have hKd : Γ.comps.all (Comp.isDetKind (l - 1)) = true := hKd
  have hDC : Γ.internalize.DoublyConnected := hDC
  have hN : Γ.Normal Cn := hN
  have hA : Γ.DotsAcyclic := hA
  by_cases hX : ∃ c : Fin Γ.comps.length, Γ.comps[c].kind = .xdot
  · have hconn : (SimpleGraph.fromRel fun u v =>
        ∃ i ∈ (Set.univ : Set (Fin Γ.comps.length)), FT1b.ends Γ i = (u, v)).Connected := by
      have hg : (SimpleGraph.fromRel fun u v =>
          ∃ i ∈ (Set.univ : Set (Fin Γ.comps.length)), FT1b.ends Γ i = (u, v)) = Γ.edgeGraph := by
        unfold Graph.edgeGraph
        congr 1
        funext u v
        apply propext
        constructor
        · rintro ⟨i, -, hi⟩
          exact ⟨Γ.comps[i], List.getElem_mem _, (Prod.mk.inj hi).1, (Prod.mk.inj hi).2⟩
        · rintro ⟨c, hc, rfl, rfl⟩
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
          exact ⟨⟨i, hi⟩, Set.mem_univ _, rfl⟩
      rw [hg]
      exact ⟨hN.1.connected⟩
    obtain ⟨T, -, -, hT⟩ := exists_tree (FT1b.ends Γ) Set.univ hconn
    exact ⟨T, T, hT, hT, Or.inr hX⟩
  push Not at hX
  rcases hcase with ⟨C', hN'⟩ | hD
  · obtain ⟨bl, bu, -, -, -, -, hboth, hTb, hTu⟩ := dc_trees (by norm_num) Γ C' hN'.1 hDC
    exact ⟨bl, bu, hTb, hTu, Or.inl fun c h1 h2 => Or.inl (hboth c h1 h2)⟩
  · obtain ⟨i, hi, hk, hrest⟩ := Diag.dot_unique Γ hD hA
    have hxy := hD.2 _ (List.getElem_mem hi) hk
    cases n with
    | zero =>
      refine ⟨[⟨i, hi⟩], [⟨i, hi⟩], ?_, ?_, Or.inl fun c h1 _ => ?_⟩
      rotate_left 2
      · rw [List.mem_singleton] at h1
        subst h1
        exact Or.inr hk
      all_goals
        refine ⟨by simp, fun u v => ?_⟩
        have hall : ∀ w : Atom 2 0, w = .inl 0 ∨ w = .inl 1 := by
          rintro (a | a)
          · fin_cases a <;> simp
          · exact a.elim0
        by_cases huv : u = v
        · rw [huv]
        · refine SimpleGraph.Adj.reachable ⟨huv, ?_⟩
          simp only [List.map_cons, List.map_nil, List.mem_singleton, FT1b.ends]
          rcases hall u with rfl | rfl <;> rcases hall v with rfl | rfl
          · exact absurd rfl huv
          · rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl (by simp [Fin.getElem_fin, h1, h2])
            · exact Or.inr (by simp [Fin.getElem_fin, h1, h2])
          · rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inr (by simp [Fin.getElem_fin, h1, h2])
            · exact Or.inl (by simp [Fin.getElem_fin, h1, h2])
          · exact absurd rfl huv
    | succ m =>
      have hrest' : ∀ c ∈ Γ.comps.eraseIdx i,
          c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false := by
        intro c hc
        have hc' := List.mem_of_mem_eraseIdx hc
        refine ⟨hrest c hc, fun h => ?_, ?_⟩
        · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc'
          exact hX ⟨j, hj⟩ h
        · have h := List.all_eq_true.1 hKd c hc'
          rcases hkc : c.kind with ch | ch | ch | ch | ⟨ch, D'⟩ | w | o | ⟨n', D'⟩ | _ |
            ⟨j, r, bb⟩ | _ | _
          all_goals simp_all [Comp.isDetKind, Kind.isSolid]
      obtain ⟨hN'', hDC''⟩ := Diag.internal Γ i hi hk hD hrest' hDC
      set G' := Diag.graph Γ i
      obtain ⟨bl, bu, -, -, -, -, hboth, hTb, hTu⟩ := dc_trees (by norm_num) G' _ hN''.1 hDC''
      have hlen : G'.comps.length + 1 = Γ.comps.length := by
        simp only [G', Diag.graph, List.length_map, List.length_eraseIdx_of_lt hi]
        omega
      set j : Fin G'.comps.length → Fin Γ.comps.length := fun k =>
        if k.1 < i then ⟨k.1, by omega⟩ else ⟨k.1 + 1, by omega⟩
      have hGk : ∀ k : Fin G'.comps.length, G'.comps[k] = Γ.comps[j k].map (Diag.atomMap m) := by
        intro k
        show ((Γ.comps.eraseIdx i).map (Comp.map (Diag.atomMap m)))[k.1] = _
        rw [List.getElem_map, List.getElem_eraseIdx]
        by_cases h : k.1 < i
        · simp [j, h]
        · simp [j, h]
      have hjne : ∀ k, j k ≠ ⟨i, hi⟩ := by
        intro k h
        simp only [j] at h
        split_ifs at h with h' <;> simp only [Fin.mk.injEq] at h <;> omega
      have hjinj : Function.Injective j := by
        intro k k' h
        simp only [j] at h
        apply Fin.ext
        split_ifs at h with h1 h2 h2 <;> simp only [Fin.mk.injEq] at h <;> omega
      have hfib : ∀ u v : Atom 2 (m + 1), Diag.atomMap m u = Diag.atomMap m v →
          u = v ∨ (u, v) = FT1b.ends Γ ⟨i, hi⟩ ∨ (v, u) = FT1b.ends Γ ⟨i, hi⟩ := by
        intro u v h
        have he : FT1b.ends Γ ⟨i, hi⟩ = (Γ.comps[i].x, Γ.comps[i].y) := rfl
        rw [he]
        rcases u with a | a <;> rcases v with b | b
        · fin_cases a <;> fin_cases b
          · exact Or.inl rfl
          · rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inr (Or.inl (by rw [h1, h2]; rfl))
            · exact Or.inr (Or.inr (by rw [h1, h2]; rfl))
          · rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inr (Or.inr (by rw [h1, h2]; rfl))
            · exact Or.inr (Or.inl (by rw [h1, h2]; rfl))
          · exact Or.inl rfl
        · exfalso
          simp only [Diag.atomMap, Sum.elim_inl, Sum.elim_inr] at h
          refine Fin.cases (motive := fun b => (Sum.inl 0 : Atom 2 m) =
            Fin.cons (α := fun _ => Atom 2 m) (Sum.inl 1) Sum.inr b → False) ?_ ?_ b h
          · simp
          · intro b' hb'; simp at hb'
        · exfalso
          simp only [Diag.atomMap, Sum.elim_inl, Sum.elim_inr] at h
          refine Fin.cases (motive := fun a => Fin.cons (α := fun _ => Atom 2 m) (Sum.inl 1)
            Sum.inr a = (Sum.inl 0 : Atom 2 m) → False) ?_ ?_ a h
          · simp
          · intro a' ha'; simp at ha'
        · left
          simp only [Diag.atomMap, Sum.elim_inr] at h
          congr 1
          refine Fin.cases (motive := fun a => ∀ b, Fin.cons (α := fun _ => Atom 2 m) (Sum.inl 1)
            Sum.inr a = Fin.cons (α := fun _ => Atom 2 m) (Sum.inl 1) Sum.inr b → a = b)
            ?_ ?_ a b h
          · intro b hb
            refine Fin.cases (motive := fun b => Fin.cons (α := fun _ => Atom 2 m) (Sum.inl 1)
              Sum.inr 0 = Fin.cons (α := fun _ => Atom 2 m) (Sum.inl 1) Sum.inr b → 0 = b)
              (fun _ => rfl) (fun b' hb' => by simp at hb') b hb
          · intro a' b hb
            refine Fin.cases (motive := fun b => Fin.cons (α := fun _ => Atom 2 m) (Sum.inl 1)
              Sum.inr a'.succ = Fin.cons (α := fun _ => Atom 2 m) (Sum.inl 1) Sum.inr b →
                a'.succ = b) (fun hb' => by simp at hb') (fun b' hb' => by simp at hb'; rw [hb'])
              b hb
      have hcard : Fintype.card (Atom 2 (m + 1)) = Fintype.card (Atom 2 m) + 1 := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        ring
      have hj' : ∀ k, FT1b.ends G' k =
          (Diag.atomMap m (FT1b.ends Γ (j k)).1, Diag.atomMap m (FT1b.ends Γ (j k)).2) := by
        intro k
        simp only [FT1b.ends, hGk k, Comp.map]
      refine ⟨⟨i, hi⟩ :: bl.map j, ⟨i, hi⟩ :: bu.map j,
        FT1b_lift_tree (Diag.atomMap m) (FT1b.ends Γ) (FT1b.ends G') j hj' bl hTb _ hcard hfib,
        FT1b_lift_tree (Diag.atomMap m) (FT1b.ends Γ) (FT1b.ends G') j hj' bu hTu _ hcard hfib,
        Or.inl fun c h1 h2 => ?_⟩
      rcases List.mem_cons.1 h1 with rfl | h1
      · exact Or.inr hk
      rcases List.mem_cons.1 h2 with rfl | h2
      · exact Or.inr hk
      obtain ⟨k, hk1, rfl⟩ := List.mem_map.1 h1
      obtain ⟨k', hk2, hkk⟩ := List.mem_map.1 h2
      rw [hjinj hkk] at hk2
      obtain ⟨w, hw⟩ := hboth k hk1 hk2
      refine Or.inl ⟨w, ?_⟩
      rw [hGk k] at hw
      exact hw

/-- A `×`-dotted edge of a graph with the shape of a self-energy is a loop: it would otherwise need
a solid edge between its ends (normal regularity). -/
private theorem FT1b_xdot_loop {l n : ℕ} (Γ : Graph 2 n) (hΓ : SelfEnergyShape l [⟨n, Γ⟩])
    (c : Comp (Atom 2 n)) (hc : c ∈ Γ.comps) (hk : c.kind = .xdot) : c.x = c.y := by
  obtain ⟨⟨Cn, hN, -⟩, hKd, -, -⟩ := hΓ _ (List.mem_singleton_self _)
  have hKd : Γ.comps.all (Comp.isDetKind (l - 1)) = true := hKd
  by_contra hxy
  obtain ⟨c', hc', hs, -⟩ := ((hN.2.2 c.x c.y hxy).1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩)
  have h := List.all_eq_true.1 hKd c' hc'
  rcases hkc : c'.kind with ch | ch | ch | ch | ⟨ch, D'⟩ | w | o | ⟨n', D'⟩ | _ | ⟨j, r, bb⟩ | _ | _
  all_goals simp_all [Comp.isDetKind, Kind.isSolid]

/-- **The momentum form of one graph of `Σ_l`** ([I, (7.29)–(7.30)] on `ℤ^d`): for `d ≥ 8`, a
profile `P`, a family `Sig` whose even orders `4 ≤ k ≤ l − 1` have the shape of a self-energy,
`κ > 0` and a graph `g` with the shape of an `l`-th order self-energy, there are a momentum form
`G` of `g` and `W₀` such that for `W ≥ W₀`, `|E| < 2 − κ` and every `p`,
`Σ_x g^∞(0, x) e^{ip·x} = c_G(m(E)) M_G(p)`, absolutely convergent, on the record of [I, Def 7.1]
at `S_∞ = Sinf P.ψ W` with the label kernels `Σ̊^∞`. -/
private theorem FT1b_graph (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig (l - 1)) {κ : ℝ} (hκ : 0 < κ) (g : Σ n : ℕ, Graph 2 n)
    (hg : SelfEnergyShape l [g]) :
    ∃ G : FT1b.MomGraph, G.Spec l g ∧ ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      ∀ p : Fin d → ℝ,
        HasSum (fun x => ValZ.val g.2 (ValZ.rec (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W E) ![0, x] *
            zexp p x)
          (G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p) := by
  obtain ⟨n, g⟩ := g
  obtain ⟨n', Γ', hsh', -, hval, hcase⟩ := G13.dotContract' l n g hg
  obtain ⟨T₁, T₂, hT₁, hT₂, hsh⟩ := FT1b_trees Γ' hsh' hcase
  refine ⟨⟨n', Γ', T₁, T₂⟩, ⟨hsh', fun d D e => (hval d D e).1, hT₁, hT₂, hsh⟩, ?_⟩
  obtain ⟨⟨Cn, hN, -⟩, hKd, -, hDC⟩ := hsh' _ (List.mem_singleton_self _)
  have hKd : Γ'.comps.all (Comp.isDetKind (l - 1)) = true := hKd
  have hDC : Γ'.internalize.DoublyConnected := hDC
  obtain ⟨W₁, hW₁⟩ := FT1b_edgeData hd P Sig l hSig hκ Γ' hKd
  obtain ⟨C, c₀, c', W₂, -, hc', hW₂, hsym⟩ := FT1b_sinf P
  have hK := InfBound.selUnif (by omega) P Sig (l - 1) hSig hκ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨CL, -, hL⟩ := latSum d (2 * d - 4 - 1) (by linarith)
  -- the summability of the graph value over `(x, σ_int)`
  have hsumW : ∃ W₃ : ℝ, ∀ W : ℕ, W₃ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      Summable fun xs : (Fin d → ℤ) × (Fin n' → Fin d → ℤ) =>
        ‖ValZ.term Γ' (ValZ.rec (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W E)
          (Sum.elim ![0, xs.1] xs.2)‖ := by
    rcases hcase with ⟨C', hN'⟩ | hD
    · obtain ⟨W₃, hW₃⟩ := ValZ.corBound d (by omega) P.ψ P.cψ c' (ValZ_shape P) hc' C κ hκ
        (l - 1) (ValZ.sigKer Sig P.ψ) hK n' C' Γ' hN' hDC hKd 1 one_pos
      refine ⟨max (max W₃ W₂) 1, fun W hW E hE => ?_⟩
      have hs := (hsym W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW)).1
      have hW1 : 1 ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
      have h := hW₃ W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW) _ hs E hE
      refine (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun x => (h 0 x).1, ?_⟩
      refine Summable.of_nonneg_of_le (fun x => tsum_nonneg fun _ => norm_nonneg _)
        (fun x => (h 0 x).2) ?_
      simp only [zero_sub, zdInf_neg]
      have := (hL W hW1).1
      exact this.mul_left _
    · obtain ⟨W₃, hW₃⟩ := InfBound.diagBound (by omega) P.ψ P.cψ c' (ValZ_shape P) hc' C hκ
        (ValZ.sigKer Sig P.ψ) hK Γ' hsh' hD 1 one_pos
      refine ⟨max W₃ W₂, fun W hW E hE => ?_⟩
      have hs := (hsym W (le_trans (le_max_right _ _) hW)).1
      have h := hW₃ W (le_trans (le_max_left _ _) hW) _ hs E hE
      refine (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun x => (h 0 x).1, ?_⟩
      refine summable_of_ne_finset_zero (s := {0}) fun x hx => ?_
      have hx0 : (0 : Fin d → ℤ) ≠ x := fun h' => hx (by simp [← h'])
      have := (h 0 x).2
      simp only [hx0, ite_false] at this
      exact le_antisymm this (tsum_nonneg fun _ => norm_nonneg _)
  obtain ⟨W₃, hW₃⟩ := hsumW
  refine ⟨max W₁ W₃, fun W hW E hE p => ?_⟩
  have hW1' : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW3' : W₃ ≤ W := le_trans (le_max_right _ _) hW
  set D := ValZ.rec (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W E with hD
  set f : Fin Γ'.comps.length → (Fin d → ℝ) → ℂ := fun c =>
    FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) Γ'.comps[c].kind with hf
  have hvalg : ∀ x, ValZ.val g D ![0, x] = ValZ.val Γ' D ![0, x] := fun x => ((hval d D _).1).symm
  simp only [hvalg]
  -- the degenerate cases: a vanishing coefficient, or a `×`-dotted edge
  by_cases h0 : Γ'.coeff.eval (mE E) = 0 ∨ ∃ c : Fin Γ'.comps.length, Γ'.comps[c].kind = .xdot
  · have hz : ∀ x, ValZ.val Γ' D ![0, x] = 0 := by
      intro x
      unfold ValZ.val
      refine (tsum_congr fun t => ?_).trans tsum_zero
      unfold ValZ.term
      rcases h0 with h0 | ⟨c, hc⟩
      · rw [show D.m = mE E from rfl, h0, zero_mul]
      · refine mul_eq_zero_of_right _ (List.prod_eq_zero (List.mem_map.2 ⟨Γ'.comps[c],
          List.getElem_mem _, ?_⟩))
        have hl := FT1b_xdot_loop Γ' hsh' _ (List.getElem_mem _) hc
        simp only [Fin.getElem_fin] at hl hc ⊢
        simp [ValZ.compVal, hc, hl]
    simp only [hz, zero_mul]
    have hr : FT1b.MomGraph.sym ⟨n', Γ', T₁, T₂⟩ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E)
        p = 0 := by
      unfold FT1b.MomGraph.sym
      rcases h0 with h0 | ⟨c, hc⟩
      · simp only [h0, zero_mul]
      · refine mul_eq_zero_of_right _ (mul_eq_zero_of_right _ ?_)
        refine (integral_congr_ae (Eventually.of_forall fun q => ?_)).trans (integral_zero _ _)
        refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
        simp only [Fin.getElem_fin] at hc ⊢
        simp [hc, FT1b.kindSym]
    rw [hr]
    exact hasSum_zero
  push Not at h0
  obtain ⟨hcoef, hX⟩ := h0
  have hed := hW₁ W hW1' E hE
  have hsum := hW₃ W hW3' E hE
  have hrow := FT1b_hasSum_row Γ' D p hsum
  have hkey : ∀ σ : Atom 2 n' → Fin d → ℤ, ∀ c : Fin Γ'.comps.length,
      ValZ.compVal D σ Γ'.comps[c] =
        latticeFourier (f c) (σ (FT1b.ends Γ' c).2 - σ (FT1b.ends Γ' c).1) := by
    intro σ c
    exact (hed _ (List.getElem_mem _)).2.2.2.2 (fun h => absurd h (hX c)) σ
  have hP : ∑ v, FT1b.extP (n := n') p v = 0 := by
    rw [Fintype.sum_sum_type]
    simp [FT1b.extP, Fin.sum_univ_two]
  have hH3 : Summable fun σ : {σ : Atom 2 n' → Fin d → ℤ // σ (Sum.inl 0) = 0} =>
      ∏ c, ‖latticeFourier (f c) (σ.1 (FT1b.ends Γ' c).2 - σ.1 (FT1b.ends Γ' c).1)‖ := by
    have h1 : Summable fun σ : {σ : Atom 2 n' → Fin d → ℤ // σ (Sum.inl 0) = 0} =>
        ‖ValZ.term Γ' D σ.1‖ := by
      rw [← (FT1b_equiv n').symm.summable_iff]
      exact hsum
    refine (h1.mul_left ‖Γ'.coeff.eval (mE E)‖⁻¹).congr fun σ => ?_
    unfold ValZ.term
    rw [norm_mul, ← mul_assoc, show D.m = mE E from rfl,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hcoef), one_mul, ← Fin.prod_univ_fun_getElem,
      norm_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← hkey]
    rfl
  obtain ⟨-, hFT⟩ := FT1a.graphFourier (Sum.inl 0) (FT1b.ends Γ') T₁ T₂ hT₁ hT₂ (FT1b.extP p) hP
    (fun c => latticeFourier (f c)) f (fun c => (hed _ (List.getElem_mem _)).1)
    (fun c => (hed _ (List.getElem_mem _)).2.1)
    (fun c => ⟨rfl, (hed _ (List.getElem_mem _)).2.2.1⟩)
    (fun c h1 h2 => by
      rcases hsh with hsh | ⟨c', hc'⟩
      · exact (hed _ (List.getElem_mem _)).2.2.2.1 (hsh c h1 h2)
      · exact absurd hc' (hX c'))
    hH3
  convert hrow using 1
  unfold FT1b.MomGraph.sym FT1b.momInt
  simp only
  rw [← hFT, show D.m = mE E from rfl]
  congr 1
  refine tsum_congr fun σ => ?_
  congr 1
  exact Finset.prod_congr rfl fun c _ => (hkey σ.1 c).symm

open private ValZ_val_congr from RBM8D.SelfEnergy.ValZ

/-- `Σ^{(r),∞}_l(0, x)` is the value of `Sig l` on the record whose labels are `Σ̊^∞`, when the
labels of `Sig l` have entries in `[4, l − 1]` (`ValZ.sigR_eq` for `l ≥ 1`; at `l = 0` every label
is empty). -/
private theorem FT1b_sigR_eq (Sig : ℕ → Expansion 2) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (W : ℕ) (E : ℝ) (l : ℕ)
    (hdet : ∀ g ∈ Sig l, g.2.comps.all (Comp.isDetKind (l - 1)) = true) (x : Fin d → ℤ) :
    ValZ.sigR Sig (Sinf ψ W) W E l x =
      ValZ.expVal (Sig l) (ValZ.rec (Sinf ψ W) (ValZ.sigKer Sig ψ E) W E) ![0, x] := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · unfold ValZ.sigR ValZ.expVal
    congr 1
    refine List.map_congr_left fun g hg => ValZ_val_congr g.2
      (D := ValZ.rec (Sinf ψ W) (fun l' _ => ValZ.sigUpTo Sig (Sinf ψ W) W E 0 l') W E)
      (D' := ValZ.rec (Sinf ψ W) (ValZ.sigKer Sig ψ E) W E) rfl rfl rfl rfl
      (fun c hc o ho => ?_) _
    have h := List.all_eq_true.1 (hdet g hg) c hc
    simp only [Comp.isDetKind, ho, Bool.and_eq_true] at h
    have ho' : o = [] := by
      cases o with
      | nil => rfl
      | cons j o =>
        have := h.2
        simp only [labelOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at this
        omega
    subst ho'
    rfl
  · exact ValZ.sigR_eq Sig ψ W E hl hdet x

/-- Momentum forms for every graph of a list, with one threshold. -/
private theorem FT1b_list {α β : Type*} (R : α → β → Prop) (Q : α → β → ℕ → Prop) (L : List α)
    (h : ∀ a ∈ L, ∃ b, R a b ∧ ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → Q a b W) :
    ∃ M : List β, List.Forall₂ R L M ∧
      ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → List.Forall₂ (fun a b => Q a b W) L M := by
  induction L with
  | nil => exact ⟨[], List.Forall₂.nil, 0, fun _ _ => List.Forall₂.nil⟩
  | cons a L ih =>
    obtain ⟨b, hR, W₁, hW₁⟩ := h a List.mem_cons_self
    obtain ⟨M, hM, W₂, hW₂⟩ := ih fun a' ha' => h a' (List.mem_cons_of_mem a ha')
    exact ⟨b :: M, List.Forall₂.cons hR hM, max W₁ W₂, fun W hW =>
      List.Forall₂.cons (hW₁ W (le_trans (le_max_left _ _) hW))
        (hW₂ W (le_trans (le_max_right _ _) hW))⟩

/-- The sum over the graphs of a formal sum. -/
private theorem FT1b_hasSum_expVal (D : ValZ.Rec d) (p : Fin d → ℝ) (r : FT1b.MomGraph → ℂ) :
    ∀ (L : Expansion 2) (M : List FT1b.MomGraph),
      List.Forall₂ (fun g G => HasSum (fun x => ValZ.val g.2 D ![0, x] * zexp p x) (r G)) L M →
      HasSum (fun x => ValZ.expVal L D ![0, x] * zexp p x) (M.map r).sum := by
  intro L M h
  induction h with
  | nil => simp [ValZ.expVal]
  | cons h1 _ ih =>
    simp only [ValZ.expVal, List.map_cons, List.sum_cons, add_mul] at ih ⊢
    exact h1.add ih

/-- **[I, (7.29)–(7.30)] for `R(E, W)` and for the symbol of `Σ^{(r),∞}_l`** on `ℤ^d`: for
`d ≥ 8`, a profile `P`, a family `Sig` whose even orders `4 ≤ k ≤ n − 1` have the shape of a
self-energy, `Σ_n = Sig n` with the shape of an `n`-th order self-energy and `κ > 0`, every graph
`g` of `Sig l` (`l = n`, or `l ∈ [4, n]` even) has a momentum form `G` (`FT1b.MomGraph.Spec`, the
list `M l`), and there is `W₀` such that for `W ≥ W₀` and `|E| < 2 − κ`:
* `R(E, W) = Σ_x Σ^{(r),∞}_n(0, x) = Σ_{G ∈ M n} c_G(m(E)) M_G(0)` (`ValZ.rowSum`);
* for every even `l ∈ [4, n]` and `p`, `Σ_x Σ^{(r),∞}_l(0, x) e^{ip·x} = Σ_{G ∈ M l} c_G(m(E)) M_G(p)`,
  absolutely convergent;
with `M_G(p) = (2π)^{-dL} ∫ Π_c ψ_c(ℓ_c(q) + λ_c(P)) dq` over the loop momenta of the tree `T₁`, the
symbols `ŝ`, `ψ_±`, `ψ_o` ([I, (7.28)]) and `1` (dotted edge) of the components
(`FT1b.MomGraph.sym`). At odd `n`, `Sig n = []` and `R = 0`. -/
theorem FT1b.rowSumFourier (hd : 8 ≤ d) (P : Profile d) (n : ℕ) (Sig : ℕ → Expansion 2)
    (hSig : SelfEnergyShapesUpTo Sig (n - 1)) (hn : SelfEnergyShape n (Sig n)) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ M : ℕ → List FT1b.MomGraph,
      (∀ l, (l = n ∨ 4 ≤ l ∧ l ≤ n ∧ Even l) →
        List.Forall₂ (FT1b.MomGraph.Spec l) (Sig l) (M l)) ∧
      ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
        ValZ.rowSum Sig P.ψ n E W =
            ((M n).map fun G => G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) 0).sum ∧
        ∀ l, 4 ≤ l → l ≤ n → Even l → ∀ p : Fin d → ℝ,
          HasSum (fun x => ValZ.sigR Sig (Sinf P.ψ W) W E l x * zexp p x)
            ((M l).map fun G => G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p).sum := by
  have hshape : ∀ l, (l = n ∨ 4 ≤ l ∧ l ≤ n ∧ Even l) → SelfEnergyShape l (Sig l) := by
    intro l hl
    by_cases h : l = n
    · rw [h]; exact hn
    · rcases hl with h' | ⟨h4, hln, he⟩
      · exact absurd h' h
      · exact hSig l h4 (by omega) he
  have hex : ∀ l, ∃ M : List FT1b.MomGraph, (l = n ∨ 4 ≤ l ∧ l ≤ n ∧ Even l) →
      List.Forall₂ (FT1b.MomGraph.Spec l) (Sig l) M ∧ ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W →
        List.Forall₂ (fun g G => ∀ E : ℝ, |E| < 2 - κ → ∀ p : Fin d → ℝ,
          HasSum (fun x => ValZ.val g.2 (ValZ.rec (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W E)
              ![0, x] * zexp p x)
            (FT1b.MomGraph.sym G (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p)) (Sig l) M := by
    intro l
    by_cases hl : l = n ∨ 4 ≤ l ∧ l ≤ n ∧ Even l
    · have hS' : SelfEnergyShapesUpTo Sig (l - 1) := by
        intro k h4 hk he
        rcases hl with rfl | ⟨-, hln, -⟩ <;> exact hSig k h4 (by omega) he
      obtain ⟨M, h1, h2⟩ := FT1b_list (FT1b.MomGraph.Spec l) _ (Sig l) fun g hg => by
        obtain ⟨G, hG, W₀, hW⟩ := FT1b_graph hd P Sig l hS' hκ g fun g' hg' => by
          rw [List.mem_singleton] at hg'
          rw [hg']
          exact hshape l hl g hg
        exact ⟨G, hG, W₀, fun W hW' E hE p => hW W hW' E hE p⟩
      exact ⟨M, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨[], fun h => absurd h hl⟩
  choose M hM using hex
  refine ⟨M, fun l hl => (hM l hl).1, ?_⟩
  obtain ⟨W₀, hW₀⟩ := InfBound_W₀_list (List.range (n + 1)) (fun l W =>
      (l = n ∨ 4 ≤ l ∧ l ≤ n ∧ Even l) →
        List.Forall₂ (fun g G => ∀ E : ℝ, |E| < 2 - κ → ∀ p : Fin d → ℝ,
          HasSum (fun x => ValZ.val g.2 (ValZ.rec (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W E)
              ![0, x] * zexp p x)
            (FT1b.MomGraph.sym G (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p)) (Sig l) (M l))
    (fun l _ => by
      by_cases hl : l = n ∨ 4 ≤ l ∧ l ≤ n ∧ Even l
      · obtain ⟨W₀, hW⟩ := (hM l hl).2
        exact ⟨W₀, fun W hW' _ => hW W hW'⟩
      · exact ⟨0, fun W _ h => absurd h hl⟩)
  have hsig : ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ l,
      (l = n ∨ 4 ≤ l ∧ l ≤ n ∧ Even l) → ∀ p : Fin d → ℝ,
      HasSum (fun x => ValZ.sigR Sig (Sinf P.ψ W) W E l x * zexp p x)
        ((M l).map fun G => G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p).sum := by
    intro W hW E hE l hl p
    have hf := hW₀ W hW l (List.mem_range.2 (by rcases hl with rfl | ⟨-, h, -⟩ <;> omega)) hl
    have hdet : ∀ g ∈ Sig l, g.2.comps.all (Comp.isDetKind (l - 1)) = true :=
      fun g hg => (hshape l hl g hg).2.1
    simp only [FT1b_sigR_eq Sig P.ψ W E l hdet]
    exact FT1b_hasSum_expVal _ p _ (Sig l) (M l) (hf.imp fun g G h => h E hE p)
  refine ⟨W₀, fun W hW E hE => ⟨?_, fun l h4 hln he p => hsig W hW E hE l (Or.inr ⟨h4, hln, he⟩) p⟩⟩
  have h := (hsig W hW E hE n (Or.inl rfl) 0).tsum_eq
  simp only [FT1b_zexp_zero_left, mul_one] at h
  exact h

end Graphs

/-! ## [I, Claim 7.8] as symbol comparisons -/

section Compare

open private ValZ_shape from RBM8D.SelfEnergy.ValZ

private theorem FT1b_norm_smul_sq (W : ℝ) (p : Fin d → ℝ) :
    ‖W • WithLp.toLp 2 p‖ ^ 2 = W ^ 2 * sqNorm p := by
  rw [norm_smul, mul_pow, EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs]
  simp [sqNorm]

/-- `|F(a) − F(b)| ≤ |a − b| / β²` for `F(z) = w z/(1 − w z)`, `|w| = 1`, `|1 − w a|, |1 − w b| ≥ β`. -/
private theorem FT1b_frac_sub {w a b : ℂ} {β : ℝ} (hw : ‖w‖ = 1) (hβ : 0 < β)
    (ha : β ≤ ‖1 - w * a‖) (hb : β ≤ ‖1 - w * b‖) :
    ‖w * a / (1 - w * a) - w * b / (1 - w * b)‖ ≤ ‖a - b‖ / β ^ 2 := by
  have ha0 : (1 - w * a) ≠ 0 := fun h => by rw [h, norm_zero] at ha; linarith
  have hb0 : (1 - w * b) ≠ 0 := fun h => by rw [h, norm_zero] at hb; linarith
  have he : w * a / (1 - w * a) - w * b / (1 - w * b) = w * (a - b) / ((1 - w * a) * (1 - w * b)) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul, hw, one_mul, norm_mul]
  refine div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) ?_
  rw [sq]
  exact mul_le_mul ha hb hβ.le (norm_nonneg _)

/-- **[I, Claim 7.8] as symbol comparisons on `ℤ^d`** ([I, (7.25)–(7.27)] with `S̃` replaced by
the kernel whose symbol is `ψ(W·)`): for a profile `P`, `κ > 0` and every `D`, there are `C ≥ 0`
and `W₀` such that for `W ≥ W₀`, `|E| < 2 − κ` and `p ∈ [−π, π]^d`, with `t = ψ(Wp)`,
* `|ŝ(p) − t| ≤ C W^{-D}`;
* `|ψ_+(p) − m²t/(1 − m²t)| ≤ C W^{-D}` and `|ψ_−(p) − m̄²t/(1 − m̄²t)| ≤ C W^{-D}`, `m = m(E)`;
* `|ψ_Θ(p) − t/(1 − t)| ≤ C W^{-D} D_W(p)²`. -/
theorem FT1b.symbolCompare (P : Profile d) {κ : ℝ} (hκ : 0 < κ) (D : ℕ) :
    ∃ C W₀ : ℝ, 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ p ∈ cubePi d,
      ‖zdSymbol (Sinf P.ψ W) p - (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ)‖ ≤ C / (W : ℝ) ^ D ∧
      ‖FT1b.plusSym (mE E) (Sinf P.ψ W) p -
          mE E ^ 2 * (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ) /
            (1 - mE E ^ 2 * (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ))‖ ≤ C / (W : ℝ) ^ D ∧
      ‖FT1b.minusSym (mE E) (Sinf P.ψ W) p -
          conj (mE E) ^ 2 * (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ) /
            (1 - conj (mE E) ^ 2 * (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ))‖ ≤ C / (W : ℝ) ^ D ∧
      ‖FT1b.thetaSym (Sinf P.ψ W) p -
          (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ) / (1 - (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ))‖ ≤
        C / (W : ℝ) ^ D * FT1b.dW W p ^ 2 := by
  obtain ⟨C, c₀, c', W₁, hc₀, hc', hW₁, hsym⟩ := FT1b_sinf P
  obtain ⟨β, hβ, hden⟩ := FT1b_denom hκ hc'.pos
  have hψ := ValZ_shape P
  set K : ℝ := max 1 (max (β ^ 2)⁻¹ (c₀ * P.cψ)⁻¹)
  have hK1 : 1 ≤ K := le_max_left _ _
  refine ⟨K * |C D|, W₁, by positivity, fun W hW E hE p hp => ?_⟩
  obtain ⟨hs, hr, hQ⟩ := hsym W hW
  have hW1 : (1 : ℝ) ≤ W := le_trans hW₁ hW
  have hWD : (0 : ℝ) < (W : ℝ) ^ D := by positivity
  set a := zdSymbol (Sinf P.ψ W) p
  set t : ℝ := P.ψ ((W : ℝ) • WithLp.toLp 2 p)
  have hclose : ‖a - (t : ℂ)‖ ≤ |C D| / (W : ℝ) ^ D :=
    (hs.close D p hp).trans (div_le_div_of_nonneg_right (le_abs_self _) hWD.le)
  have hd0 : 0 ≤ |C D| / (W : ℝ) ^ D := by positivity
  have h1 : ‖a - (t : ℂ)‖ ≤ K * |C D| / (W : ℝ) ^ D := by
    refine hclose.trans (div_le_div_of_nonneg_right ?_ hWD.le)
    exact le_mul_of_one_le_left (abs_nonneg _) hK1
  have hare : a = ((a.re : ℝ) : ℂ) := FT1b_shat_real (hr p).1
  have hrange := hc'.range ((W : ℝ) • WithLp.toLp 2 p)
  have ht : -1 + c' / 2 ≤ t := by have := hc'.pos; linarith [hrange.1]
  have hm1 : ‖mE E‖ = 1 := norm_mE (by linarith)
  obtain ⟨hda1, hda2⟩ := hden E hE.le a.re (hr p).2.1
  obtain ⟨hdt1, hdt2⟩ := hden E hE.le t ht
  rw [← hare] at hda1 hda2
  refine ⟨h1, ?_, ?_, ?_⟩
  · refine (FT1b_frac_sub (by rw [norm_pow, hm1, one_pow]) hβ hda1 hdt1).trans ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc ‖a - (t : ℂ)‖ * (β ^ 2)⁻¹ ≤ (|C D| / (W : ℝ) ^ D) * K :=
          mul_le_mul hclose (le_trans (le_max_left _ _) (le_max_right _ _)) (by positivity) hd0
      _ = K * |C D| * ((W : ℝ) ^ D)⁻¹ := by ring
  · refine (FT1b_frac_sub (by rw [norm_pow, Complex.norm_conj, hm1, one_pow]) hβ hda2 hdt2).trans ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc ‖a - (t : ℂ)‖ * (β ^ 2)⁻¹ ≤ (|C D| / (W : ℝ) ^ D) * K :=
          mul_le_mul hclose (le_trans (le_max_left _ _) (le_max_right _ _)) (by positivity) hd0
      _ = K * |C D| * ((W : ℝ) ^ D)⁻¹ := by ring
  · show ‖a / (1 - a) - (t : ℂ) / (1 - t)‖ ≤ _
    rcases eq_or_lt_of_le (FT1b_sqNorm_nonneg p) with h0 | h0
    · have hp0 : p = 0 := FT1b_sqNorm_eq_zero h0.symm
      have hat : a = 1 := by simp only [a, hp0]; exact FT1b_shat_zero hs
      have htt : t = 1 := by simp only [t, hp0]; simpa using hψ.at_zero
      rw [hat, htt]
      simp only [Complex.ofReal_one, sub_self, div_zero, norm_zero]
      positivity
    · set u := (W : ℝ) ^ 2 * sqNorm p
      have hu : 0 < u := mul_pos (by positivity) h0
      have hmu : 0 < min u 1 := lt_min hu one_pos
      have hla : c₀ * min u 1 ≤ 1 - a.re := hQ p hp
      have hlt : P.cψ * min u 1 ≤ 1 - t := by
        have hmax := hψ.le_max ((W : ℝ) • WithLp.toLp 2 p)
        rw [FT1b_norm_smul_sq] at hmax
        rcases le_total u 1 with h | h
        · rw [min_eq_left h]
          have : 1 - P.cψ * u ≥ 1 - P.cψ := by nlinarith [hψ.pos]
          rw [max_eq_left this] at hmax
          linarith
        · rw [min_eq_right h, mul_one]
          have : 1 - P.cψ * u ≤ 1 - P.cψ := by nlinarith [hψ.pos]
          rw [max_eq_right this] at hmax
          linarith
      have hA : 0 < 1 - a.re := lt_of_lt_of_le (mul_pos hc₀ hmu) hla
      have hT : 0 < 1 - t := lt_of_lt_of_le (mul_pos hψ.pos hmu) hlt
      have hdW : FT1b.dW W p * min u 1 = 1 := by
        unfold FT1b.dW
        rcases le_or_gt 1 u with h | h
        · rw [min_eq_right h, mul_one, max_eq_left (inv_le_one_of_one_le₀ h)]
        · rw [min_eq_left h.le, max_eq_right ((one_le_inv₀ hu).2 h.le), inv_mul_cancel₀ hu.ne']
      have hea : (1 : ℂ) - a = ((1 - a.re : ℝ) : ℂ) := by rw [hare]; push_cast; simp
      have he : a / (1 - a) - (t : ℂ) / (1 - t) = (a - t) / ((1 - a) * (1 - t)) := by
        have h1' : (1 : ℂ) - a ≠ 0 := by rw [hea]; exact_mod_cast hA.ne'
        have h2' : (1 : ℂ) - t ≠ 0 := by exact_mod_cast hT.ne'
        field_simp
        ring
      rw [he, norm_div, norm_mul, hea, show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hA,
        abs_of_pos hT]
      have hprod : c₀ * P.cψ * (min u 1) ^ 2 ≤ (1 - a.re) * (1 - t) := by
        have := mul_le_mul hla hlt (mul_pos hψ.pos hmu).le hA.le
        nlinarith
      rw [div_le_iff₀ (mul_pos hA hT)]
      have hK2 : (c₀ * P.cψ)⁻¹ ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
      calc ‖a - (t : ℂ)‖ ≤ |C D| / (W : ℝ) ^ D := hclose
        _ = |C D| / (W : ℝ) ^ D * ((c₀ * P.cψ)⁻¹ * (FT1b.dW W p * min u 1) ^ 2 *
              (c₀ * P.cψ)) := by
            rw [hdW, one_pow, mul_one, inv_mul_cancel₀ (mul_pos hc₀ hψ.pos).ne', mul_one]
        _ = (|C D| / (W : ℝ) ^ D * (c₀ * P.cψ)⁻¹ * FT1b.dW W p ^ 2) *
              (c₀ * P.cψ * (min u 1) ^ 2) := by ring
        _ ≤ (K * |C D| / (W : ℝ) ^ D * FT1b.dW W p ^ 2) * ((1 - a.re) * (1 - t)) := by
            refine mul_le_mul ?_ hprod (mul_nonneg (mul_pos hc₀ hψ.pos).le (sq_nonneg _))
              (by positivity)
            have : |C D| / (W : ℝ) ^ D * (c₀ * P.cψ)⁻¹ ≤ K * |C D| / (W : ℝ) ^ D := by
              rw [mul_div_assoc]
              calc |C D| / (W : ℝ) ^ D * (c₀ * P.cψ)⁻¹ = (c₀ * P.cψ)⁻¹ * (|C D| / (W : ℝ) ^ D) :=
                    mul_comm _ _
                _ ≤ K * (|C D| / (W : ℝ) ^ D) := mul_le_mul_of_nonneg_right hK2 hd0
            exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

end Compare

section Instances

end Instances

end RBM8D
