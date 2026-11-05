import RBM8D.SelfEnergy.VR2
import RBM8D.SelfEnergy.FT1b
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Function.Floor

/-!
# [I, (8.8)]: the scaling of the row sum `R(E, W)` ([I, (7.29)] → [I, (7.30)])

On `ℤ^d`, `d ≥ 8`, with `S_∞ = Sinf P.ψ W`, `m = m(E)` and the label kernels `Σ̊^∞` of [I, Def 8.2],
`R(E, W) = Σ_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)` (`ValZ.rowSum`) is a sum of momentum integrals
(`FT1b.rowSumFourier`). This file proves [I, (8.8)]:
`R(E, W) = W^{-(n-2)d/2} 𝔖_n(E) + O(W^{-D})` for every `D`, uniformly in `|E| < 2 − κ`, with
`𝔖_n` independent of `W` and of `κ`.

* `FT1c.rowSumExpand`: [I, (8.8)] for lower orders of the shape of a self-energy and `Σ_n` of the
  shape of an `n`-th order self-energy; `𝔖_n(E) = lim_{W → ∞} W^{(n-2)d/2} R(E, W)`.

The proof follows [I, §7.3] with Remark 7.10 (Schwartz `ψ`):
* each symbol `f_c` of a component (`ŝ`, `ψ_±`, the chain symbol `ψ_o` of [I, (7.28)], `1` for a
  dotted edge) is `W^{-α_c} g_c(W p) + O(W^{-D})` on `[−π, π]^d` with a `W`-free `g_c` ([I, Claim
  7.8], and, for the labels `Σ̊^∞_l` of the chains, the same statement at the lower orders, by
  induction on `l`);
* in one momentum integral the symbols are replaced by `W^{-α_c} g_c(W ρ(·))`, `ρ` the reduction
  modulo `2π`; outside a neighbourhood of `q = 0` some momentum not on a dotted edge is of size `1`
  modulo `2π` (the dotted edges form a forest, `Graph.DotsAcyclic`, so every dotted edge is a bridge
  of a cut crossed only by edges that are not dotted), and the integrand is `O(W^{-D})` there;
* the scaling `q = k/W` turns the integral into `W^{-dL}` times an integral over the box
  `‖k‖ ≤ Wπ`, whose complement in `ℝ^{dL}` contributes `O(W^{-D})`; integrability on `ℝ^{dL}` uses
  the momentum Cauchy–Schwarz bound `FT1a.momentumCS` on dyadic boxes;
* the count `Σ_c α_c + dL = (l − 2)d/2` is [I, (2.12)] for a graph of scaling order `l`.

The weights are `ω(k) = max(1, ‖k‖⁻¹)` (sup norm); the error of the `Θ` symbols, of order
`W^{-D} ω(W p)^{2r+6}`, is interpolated with the sup bounds down to `ω(W p)^3`, square integrable
for `d ≥ 8`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace RBM8D

open Graphs

open private FT1a_incr_eq FT1a_pot_eq FT1a_sum_split FT1a_continuous_edgeMom FT1a_prod_split3
  FT1a_nodup FT1a_card_tree from RBM8D.SelfEnergy.FT1a
open private FT1b_sq_norm_le FT1b_denom FT1b_labelSym FT1b_summable_s from RBM8D.SelfEnergy.FT1b
open private ValZ_coeff_bound from RBM8D.SelfEnergy.ValZ

variable {d : ℕ}

/-! ## The weight `ω(k) = max(1, ‖k‖⁻¹)` and the reduction to `[−π, π]^d` -/

/-- `ω(k) = max(1, ‖k‖⁻¹)` (sup norm). -/
private def FT1c_om (k : Fin d → ℝ) : ℝ := max 1 ‖k‖⁻¹

private theorem FT1c_one_le_om (k : Fin d → ℝ) : 1 ≤ FT1c_om k := le_max_left _ _

private theorem FT1c_om_pos (k : Fin d → ℝ) : 0 < FT1c_om k := lt_of_lt_of_le one_pos (FT1c_one_le_om k)

private theorem FT1c_measurable_om : Measurable (FT1c_om (d := d)) :=
  measurable_const.max (continuous_norm.measurable.inv)

/-- `ω(k) = 1` for `‖k‖ ≥ 1`. -/
private theorem FT1c_om_eq_one {k : Fin d → ℝ} (hk : 1 ≤ ‖k‖) : FT1c_om k = 1 :=
  max_eq_left (inv_le_one_of_one_le₀ hk)

/-- `ω(k) ≤ ‖k‖⁻¹` for `0 < ‖k‖ ≤ 1`. -/
private theorem FT1c_om_le_inv {k : Fin d → ℝ} (h0 : 0 < ‖k‖) (h1 : ‖k‖ ≤ 1) : FT1c_om k = ‖k‖⁻¹ :=
  max_eq_right ((one_le_inv₀ h0).2 h1)

/-- `ω(k)⁻¹ = min(‖k‖, 1)` away from `0`. -/
private theorem FT1c_om_inv (k : Fin d → ℝ) (hk : k ≠ 0) : (FT1c_om k)⁻¹ = min ‖k‖ 1 := by
  have h0 : 0 < ‖k‖ := norm_pos_iff.2 hk
  rcases le_total ‖k‖ 1 with h | h
  · rw [FT1c_om_le_inv h0 h, inv_inv, min_eq_left h]
  · rw [FT1c_om_eq_one h, inv_one, min_eq_right h]

/-- The reduction `ρ(r)` of `r ∈ ℝ^d` to `[−π, π]^d` modulo `2πℤ^d`. -/
private def FT1c_red (r : Fin d → ℝ) : Fin d → ℝ :=
  fun i => r i - 2 * Real.pi * (round ((2 * Real.pi)⁻¹ * r i) : ℝ)

private theorem FT1c_red_coord (t : ℝ) :
    |t - 2 * Real.pi * (round ((2 * Real.pi)⁻¹ * t) : ℝ)| =
      2 * Real.pi * |(2 * Real.pi)⁻¹ * t - (round ((2 * Real.pi)⁻¹ * t) : ℝ)| := by
  have hp : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have h : t - 2 * Real.pi * (round ((2 * Real.pi)⁻¹ * t) : ℝ) =
      2 * Real.pi * ((2 * Real.pi)⁻¹ * t - (round ((2 * Real.pi)⁻¹ * t) : ℝ)) := by
    field_simp
  rw [h, abs_mul, abs_of_pos hp]

private theorem FT1c_red_mem (r : Fin d → ℝ) : FT1c_red r ∈ cubePi d := by
  intro i _
  have h := abs_sub_round ((2 * Real.pi)⁻¹ * r i)
  have h' := FT1c_red_coord (r i)
  have hp : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have : |FT1c_red r i| ≤ Real.pi := by
    simp only [FT1c_red]
    rw [h']
    nlinarith
  exact abs_le.1 this

private theorem FT1c_abs_red_le (t : ℝ) :
    |t - 2 * Real.pi * (round ((2 * Real.pi)⁻¹ * t) : ℝ)| ≤ |t| := by
  have h := round_le ((2 * Real.pi)⁻¹ * t) 0
  rw [FT1c_red_coord]
  have hp : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  simp only [Int.cast_zero, sub_zero] at h
  calc 2 * Real.pi * |(2 * Real.pi)⁻¹ * t - (round ((2 * Real.pi)⁻¹ * t) : ℝ)|
      ≤ 2 * Real.pi * |(2 * Real.pi)⁻¹ * t| := mul_le_mul_of_nonneg_left h hp.le
    _ = |t| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hp), ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

private theorem FT1c_norm_red_le (r : Fin d → ℝ) : ‖FT1c_red r‖ ≤ ‖r‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg r)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact le_trans (FT1c_abs_red_le (r i)) (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm r i)

private theorem FT1c_red_of_norm_lt {r : Fin d → ℝ} (hr : ‖r‖ < Real.pi) : FT1c_red r = r := by
  funext i
  have hi : |r i| < Real.pi := lt_of_le_of_lt (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm r i) hr
  have hp : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have h0 : round ((2 * Real.pi)⁻¹ * r i) = 0 := by
    rw [round_eq_zero_iff, Set.mem_Ico]
    rw [abs_lt] at hi
    have hq : (2 * Real.pi)⁻¹ * Real.pi = 1 / 2 := by field_simp
    constructor
    · have := mul_le_mul_of_nonneg_left hi.1.le (inv_pos.2 hp).le
      rw [mul_neg, hq] at this
      linarith
    · have := mul_lt_mul_of_pos_left hi.2 (inv_pos.2 hp)
      rw [hq] at this
      linarith
  simp only [FT1c_red, h0, Int.cast_zero, mul_zero, sub_zero]

/-- `r = ρ(r) + 2π z` with `z` integral. -/
private theorem FT1c_red_add (r : Fin d → ℝ) :
    r = FT1c_red r + fun i => 2 * Real.pi * ((round ((2 * Real.pi)⁻¹ * r i) : ℤ) : ℝ) := by
  funext i
  simp [FT1c_red]

private theorem FT1c_red_periodic (r : Fin d → ℝ) (z : Fin d → ℤ) :
    FT1c_red (r + fun i => 2 * Real.pi * z i) = FT1c_red r := by
  funext i
  have hp : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
  simp only [FT1c_red, Pi.add_apply]
  have : (2 * Real.pi)⁻¹ * (r i + 2 * Real.pi * (z i : ℝ)) = (2 * Real.pi)⁻¹ * r i + (z i : ℝ) := by
    field_simp
  rw [this, round_add_intCast]
  push_cast
  ring

private theorem FT1c_measurable_red : Measurable (FT1c_red (d := d)) := by
  refine Measurable.of_eval fun i => ?_
  simp only [FT1c_red]
  have hr : Measurable fun t : ℝ => ((round t : ℤ) : ℝ) := by
    simp_rw [round_eq]
    exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.add_const _))
  exact (measurable_pi_apply i).sub (measurable_const.mul
    (hr.comp (measurable_const.mul (measurable_pi_apply i))))

/-- A `2π`-periodic function is determined by its values on `[−π, π]^d`: `f(r) = f(ρ(r))`. -/
private theorem FT1c_periodic_red {β : Type*} {f : (Fin d → ℝ) → β}
    (hf : ∀ p (z : Fin d → ℤ), f (p + fun i => 2 * Real.pi * z i) = f p) (r : Fin d → ℝ) :
    f r = f (FT1c_red r) := by
  conv_lhs => rw [FT1c_red_add r]
  exact hf _ _

/-- `ω(R r) ≤ ω(R ρ(r))` for `R ≥ 1`. -/
private theorem FT1c_om_le_red {R : ℝ} (hR : 1 ≤ R) (r : Fin d → ℝ) :
    FT1c_om (R • r) ≤ FT1c_om (R • FT1c_red r) := by
  by_cases h : ‖r‖ < Real.pi
  · rw [FT1c_red_of_norm_lt h]
  · push Not at h
    rw [FT1c_om_eq_one]
    · exact FT1c_one_le_om _
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      nlinarith [Real.two_le_pi]

/-! ## The torus norm -/

/-- The projection of `ℝ^d` to `(ℝ/2πℤ)^d`. -/
private def FT1c_tor : (Fin d → ℝ) →+ (Fin d → AddCircle (2 * Real.pi)) where
  toFun r i := (r i : AddCircle (2 * Real.pi))
  map_zero' := by funext i; simp
  map_add' r s := by funext i; simp

private theorem FT1c_norm_tor_coord (t : ℝ) :
    ‖(t : AddCircle (2 * Real.pi))‖ = |t - 2 * Real.pi * (round ((2 * Real.pi)⁻¹ * t) : ℝ)| := by
  rw [AddCircle.norm_eq]
  ring_nf

/-- `‖ρ(r)‖` is the torus norm of `r`. -/
private theorem FT1c_norm_red_eq (r : Fin d → ℝ) : ‖FT1c_red r‖ = ‖FT1c_tor r‖ := by
  rw [Pi.norm_def, Pi.norm_def]
  congr 2
  funext i
  apply NNReal.eq
  simp only [coe_nnnorm]
  rw [Real.norm_eq_abs]
  exact (FT1c_norm_tor_coord (r i)).symm

private theorem FT1c_norm_tor_le (r : Fin d → ℝ) : ‖FT1c_tor r‖ ≤ ‖r‖ := by
  rw [← FT1c_norm_red_eq]; exact FT1c_norm_red_le r

/-- On `[−π, π]^d` the torus norm is the norm. -/
private theorem FT1c_norm_tor_cube {r : Fin d → ℝ} (hr : r ∈ cubePi d) : ‖FT1c_tor r‖ = ‖r‖ := by
  rw [Pi.norm_def, Pi.norm_def]
  congr 2
  funext i
  apply NNReal.eq
  simp only [coe_nnnorm]
  have hi := hr i (Set.mem_univ i)
  change ‖((r i : ℝ) : AddCircle (2 * Real.pi))‖ = ‖r i‖
  rw [Real.norm_eq_abs, AddCircle.norm_coe_eq_abs_iff _ Real.two_pi_pos.ne',
    abs_of_pos Real.two_pi_pos, abs_le]
  constructor <;> linarith [hi.1, hi.2]

/-! ## Conservation of momentum and the cut bound -/

section Flow

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- **Conservation of momentum**: for the momenta of a spanning tree `T` and `Σ_v P_v = 0`,
`Σ_c (σ_{h_c} − σ_{t_c}) ℓ_c = Σ_v σ_v P_v` for every integer vertex function `σ`. -/
private theorem FT1c_conserv {e : ι → V × V} {T : List ι} (hT : TreeEdges (T.map e))
    (P : V → Fin d → ℝ) (hP : ∑ v, P v = 0) (q : {c // c ∉ T} → Fin d → ℝ) (σ : V → ℤ) :
    ∑ c, ((σ (e c).2 - σ (e c).1 : ℤ) : ℝ) • FT1a.edgeMom e T P q c = ∑ v, (σ v : ℝ) • P v := by
  have hV : Nonempty V := by
    have h := hT.1
    rw [List.length_map] at h
    exact Fintype.card_pos_iff.1 (by omega)
  obtain ⟨v₀⟩ := hV
  rw [FT1a_sum_split T]
  have h1 : ∀ f : {f // f ∈ T}, FT1a.edgeMom e T P q f.1 =
      FT1a.extMom e T P f.1 - ∑ c' : {c // c ∉ T}, (FT1a.cutCoef e T f.1 c'.1 : ℝ) • q c' :=
    fun f => FT1a.edgeMom_of_mem P q f.2
  have h2 : ∀ c : {c // c ∉ T}, FT1a.edgeMom e T P q c.1 = q c :=
    fun c => FT1a.edgeMom_of_not_mem P q c.2
  simp_rw [h1, h2, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun (f : {f // f ∈ T}) (c' : {c // c ∉ T}) =>
      (((σ (e f.1).2 - σ (e f.1).1 : ℤ) : ℝ) * (FT1a.cutCoef e T f.1 c'.1 : ℝ)) • q c')]
  have h3 : ∀ c' : {c // c ∉ T}, ∑ f : {f // f ∈ T},
      (((σ (e f.1).2 - σ (e f.1).1 : ℤ) : ℝ) * (FT1a.cutCoef e T f.1 c'.1 : ℝ)) • q c' =
        ((σ (e c'.1).2 - σ (e c'.1).1 : ℤ) : ℝ) • q c' := by
    intro c'
    rw [← Finset.sum_smul]
    congr 1
    have h := FT1a_incr_eq hT σ c'.1
    rw [h, Int.cast_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [smul_eq_mul]
    push_cast
    ring
  simp_rw [h3, sub_add_cancel]
  -- `Σ_f Δ_f λ_f = Σ_v σ_v P_v`
  unfold FT1a.extMom
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have h4 : ∀ v, ∑ f : {f // f ∈ T}, (((σ (e f.1).2 - σ (e f.1).1 : ℤ) : ℝ) *
      (FT1a.cutInd e T f.1 v : ℝ)) • P v =
      ((σ v : ℝ) - σ v₀ + ∑ f : {f // f ∈ T}, (FT1a.cutInd e T f.1 v₀ : ℝ) *
        ((σ (e f.1).2 - σ (e f.1).1 : ℤ) : ℝ)) • P v := by
    intro v
    rw [← Finset.sum_smul]
    congr 1
    have h := FT1a_pot_eq hT σ v v₀
    have h' : ((σ v - σ v₀ : ℤ) : ℝ) = ∑ f : {f // f ∈ T},
        ((FT1a.cutInd e T f.1 v - FT1a.cutInd e T f.1 v₀ : ℤ) : ℝ) *
          ((σ (e f.1).2 - σ (e f.1).1 : ℤ) : ℝ) := by
      rw [h, Int.cast_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [smul_eq_mul]
      push_cast
      ring
    push_cast at h' ⊢
    have h'' : ∑ f : {f // f ∈ T}, ((σ (e f.1).2 : ℝ) - σ (e f.1).1) * (FT1a.cutInd e T f.1 v : ℝ) =
        ∑ f : {f // f ∈ T}, ((FT1a.cutInd e T f.1 v : ℝ) - FT1a.cutInd e T f.1 v₀) *
          ((σ (e f.1).2 : ℝ) - σ (e f.1).1) +
        ∑ f : {f // f ∈ T}, (FT1a.cutInd e T f.1 v₀ : ℝ) * ((σ (e f.1).2 : ℝ) - σ (e f.1).1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      ring
    rw [h'', ← h']
  simp_rw [h4, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum, hP, smul_zero, sub_zero, add_zero]

/-- **The cut bound**: if every dotted edge `c` has a cut `S` (a set of vertices containing `h_c`,
not `t_c`, and not separating the ends of any other dotted edge), then the momentum of every edge
is controlled, in any seminorm image `φ` of `ℝ^d`, by the external momenta and the momenta of the
edges that are not dotted. -/
private theorem FT1c_cutBound {e : ι → V × V} {T : List ι} (hT : TreeEdges (T.map e))
    (dot : ι → Prop) [DecidablePred dot]
    (hcut : ∀ c, dot c → ∃ S : V → Prop, S (e c).2 ∧ ¬ S (e c).1 ∧
      ∀ c', dot c' → c' ≠ c → (S (e c').2 ↔ S (e c').1))
    {G : Type*} [SeminormedAddCommGroup G] (φ : (Fin d → ℝ) →+ G)
    (P : V → Fin d → ℝ) (hP : ∑ v, P v = 0) (q : {c // c ∉ T} → Fin d → ℝ) (c : ι) :
    ‖φ (FT1a.edgeMom e T P q c)‖ ≤
      ∑ v, ‖φ (P v)‖ + ∑ c' ∈ Finset.univ.filter (fun c' => ¬ dot c'),
        ‖φ (FT1a.edgeMom e T P q c')‖ := by
  classical
  set ℓ := FT1a.edgeMom e T P q
  by_cases hc : dot c
  · obtain ⟨S, hSh, hSt, hS⟩ := hcut c hc
    set σ : V → ℤ := fun v => if S v then 1 else 0
    have hcons := FT1c_conserv hT P hP q σ
    have hφ := congrArg φ hcons
    simp only [map_sum] at hφ
    have hz : ∀ (n : ℤ) (x : Fin d → ℝ), φ ((n : ℝ) • x) = n • φ x := fun n x => by
      rw [Int.cast_smul_eq_zsmul, map_zsmul]
    simp_rw [hz] at hφ
    have hΔc : σ (e c).2 - σ (e c).1 = 1 := by simp [σ, hSh, hSt]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), hΔc, one_smul] at hφ
    have hrest : ∑ c' ∈ Finset.univ.erase c, (σ (e c').2 - σ (e c').1) • φ (ℓ c') =
        ∑ c' ∈ (Finset.univ.erase c).filter (fun c' => ¬ dot c'),
          (σ (e c').2 - σ (e c').1) • φ (ℓ c') := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c' hc' => ?_
      by_cases hd : dot c'
      · have := hS c' hd (Finset.ne_of_mem_erase hc')
        have h0 : σ (e c').2 - σ (e c').1 = 0 := by simp [σ, this]
        simp [hd, h0]
      · simp [hd]
    rw [hrest] at hφ
    have hc' : φ (ℓ c) = ∑ v, σ v • φ (P v) -
        ∑ c' ∈ (Finset.univ.erase c).filter (fun c' => ¬ dot c'),
          (σ (e c').2 - σ (e c').1) • φ (ℓ c') := by
      rw [← hφ]; abel
    rw [hc']
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun v _ => ?_)
      refine le_trans (norm_zsmul_le _ _) ?_
      by_cases hv : S v <;> simp [σ, hv]
    · refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum fun c' _ => norm_zsmul_le _ _) ?_
      refine le_trans (Finset.sum_le_sum fun c' _ => ?_ : _ ≤ ∑ c' ∈ (Finset.univ.erase c).filter
        (fun c' => ¬ dot c'), ‖φ (ℓ c')‖) ?_
      · have h1 : ‖σ (e c').2 - σ (e c').1‖ ≤ 1 := by
          by_cases h2 : S (e c').2 <;> by_cases h1 : S (e c').1 <;> simp [σ, h1, h2]
        calc ‖σ (e c').2 - σ (e c').1‖ * ‖φ (ℓ c')‖ ≤ 1 * ‖φ (ℓ c')‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = ‖φ (ℓ c')‖ := one_mul _
      · exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ (Finset.erase_subset _ _)) fun _ _ _ => norm_nonneg _
  · have h1 : ‖φ (ℓ c)‖ ≤ ∑ c' ∈ Finset.univ.filter (fun c' => ¬ dot c'), ‖φ (ℓ c')‖ :=
      Finset.single_le_sum (f := fun c' => ‖φ (ℓ c')‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)
    exact le_trans h1 (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _))

end Flow

/-- Removing one component keeps the graph of dotted edges when its ends stay joined. -/
private theorem FT1c_reach_erase {k n : ℕ} (Γ : Graph k n) (i : ℕ) (hi : i < Γ.comps.length)
    (h : (Graph.dotGraph ⟨Γ.comps.eraseIdx i, Γ.coeff⟩).Reachable Γ.comps[i].x Γ.comps[i].y)
    (u v : Atom k n) :
    Γ.dotGraph.Reachable u v ↔ (Graph.dotGraph ⟨Γ.comps.eraseIdx i, Γ.coeff⟩).Reachable u v := by
  set Γ' : Graph k n := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩
  have hsub : ∀ c ∈ Γ'.comps, c ∈ Γ.comps := fun c hc => List.mem_of_mem_eraseIdx hc
  have hmem : ∀ c ∈ Γ.comps, c ∈ Γ'.comps ∨ c = Γ.comps[i] := by
    intro c hc
    have hperm := List.getElem_cons_eraseIdx_perm hi
    rcases List.mem_cons.1 (hperm.mem_iff.2 hc) with h | h
    · exact Or.inr h
    · exact Or.inl h
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | @cons a b c' hadj _ ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨hab, hr⟩ := hadj
      have key : ∀ x y, (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = x ∧ c.y = y) → x ≠ y →
          Γ'.dotGraph.Reachable x y := by
        rintro x y ⟨c, hc, hk, rfl, rfl⟩ hxy
        rcases hmem c hc with h' | h'
        · exact SimpleGraph.Adj.reachable (by
            simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
            exact ⟨hxy, Or.inl ⟨c, h', hk, rfl, rfl⟩⟩)
        · rw [h']; exact h
      rcases hr with hr | hr
      · exact key a b hr hab
      · exact (key b a hr hab.symm).symm
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | @cons a b c' hadj _ ih =>
      refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) ih
      simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj ⊢
      obtain ⟨hab, ⟨c, hc, hk, hx, hy⟩ | ⟨c, hc, hk, hx, hy⟩⟩ := hadj
      · exact ⟨hab, Or.inl ⟨c, hsub c hc, hk, hx, hy⟩⟩
      · exact ⟨hab, Or.inr ⟨c, hsub c hc, hk, hx, hy⟩⟩

/-- **A dotted edge is a bridge of the dotted forest** (`Graph.DotsAcyclic`): the atoms joined to
its head by the other dotted edges form a set `S` that contains the head, not the tail, and is not
crossed by any other dotted edge. -/
private theorem FT1c_cutSet {k n : ℕ} (Γ : Graph k n) (hA : Γ.DotsAcyclic) (i : Fin Γ.comps.length)
    (hi : Γ.comps[i].kind = .dot) :
    ∃ S : Atom k n → Prop, S Γ.comps[i].y ∧ ¬ S Γ.comps[i].x ∧
      ∀ j : Fin Γ.comps.length, Γ.comps[j].kind = .dot → j ≠ i →
        (S Γ.comps[j].y ↔ S Γ.comps[j].x) := by
  set Γ' : Graph k n := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ with hΓ'
  refine ⟨fun v => Γ'.dotGraph.Reachable Γ.comps[i].y v, SimpleGraph.Reachable.refl _, ?_, ?_⟩
  · intro hr
    have hr' : Γ'.dotGraph.Reachable Γ.comps[i.1].x Γ.comps[i.1].y := hr.symm
    have heq := FT1c_reach_erase Γ i.1 i.2 hr'
    have hcard : Nat.card Γ.dotGraph.ConnectedComponent =
        Nat.card Γ'.dotGraph.ConnectedComponent :=
      Nat.card_congr (Quot.congr (Equiv.refl _) fun a b => heq a b)
    have hperm := List.getElem_cons_eraseIdx_perm i.2
    have hn : Γ.nDots = Γ'.nDots + 1 := by
      unfold Graph.nDots
      rw [← (hperm.filter _).length_eq, List.filter_cons_of_pos (by simpa using hi),
        List.length_cons]
    have h0 := (Graph.dotsAcyclic_iff_dotExcess_eq_zero Γ).1 hA
    have h1 := SelRun_dotExcess_nonneg Γ'
    unfold Graph.dotExcess at h0 h1
    rw [hcard, hn] at h0
    push_cast at h0 h1
    omega
  · intro j hj hji
    have hjm : Γ.comps[j] ∈ Γ'.comps := by
      rw [List.mem_eraseIdx_iff_getElem]
      exact ⟨j.1, j.2, fun h => hji (Fin.ext h), rfl⟩
    have hr : Γ'.dotGraph.Reachable Γ.comps[j].x Γ.comps[j].y := by
      by_cases hxy : Γ.comps[j].x = Γ.comps[j].y
      · rw [hxy]
      · exact SimpleGraph.Adj.reachable (by
          simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
          exact ⟨hxy, Or.inl ⟨_, hjm, hj, rfl, rfl⟩⟩)
    exact ⟨fun h => h.trans hr.symm, fun h => h.trans hr⟩

/-! ## Square integrability of `ω^γ` on `[−π, π]^d` -/

private theorem FT1c_measurableSet_cube : MeasurableSet (cubePi d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

private theorem FT1c_cube_lt_top : volume (cubePi d) < ∞ :=
  (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top

private theorem FT1c_om_pow_le (γ : ℕ) (p : Fin d → ℝ) : FT1c_om p ^ γ ≤ 1 + (‖p‖⁻¹) ^ γ := by
  unfold FT1c_om
  rcases le_total 1 ‖p‖⁻¹ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (inv_nonneg.2 (norm_nonneg p)) γ]

private theorem FT1c_om_smul_le {R : ℝ} (hR : 1 ≤ R) (p : Fin d → ℝ) : FT1c_om (R • p) ≤ FT1c_om p := by
  unfold FT1c_om
  refine max_le_max le_rfl ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rcases eq_or_lt_of_le (norm_nonneg p) with h | h
  · rw [← h]; simp
  · exact inv_anti₀ h (le_mul_of_one_le_left h.le hR)

private theorem FT1c_om_congr {p p' : Fin d → ℝ} (h : ‖p‖ = ‖p'‖) : FT1c_om p = FT1c_om p' := by
  unfold FT1c_om; rw [h]

private theorem FT1c_integrableOn_om {γ : ℕ} (hγ : 2 * γ < d) :
    IntegrableOn (fun p => FT1c_om p ^ (2 * γ)) (cubePi d) := by
  have hsub : cubePi d ⊆ Metric.ball (0 : Fin d → ℝ) 5 := by
    intro p hp
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun i => ?_)
      (by linarith [Real.pi_le_four] : Real.pi < 5)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(hp i (Set.mem_univ i)).1, (hp i (Set.mem_univ i)).2⟩
  have hfin : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
  have h1 : IntegrableOn (fun p : Fin d → ℝ => ‖p‖ ^ (-((2 * γ : ℕ) : ℝ))) (cubePi d) := by
    refine IntegrableOn.mono_set (integrableOn_ball_of_norm_le_rpow (μ := volume)
      (by rw [hfin]; omega) (C := 1) (α := ((2 * γ : ℕ) : ℝ)) (by rw [hfin]; exact_mod_cast hγ)
      (Eventually.of_forall fun p => ?_) ?_) hsub
    · rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  have h2 : IntegrableOn (fun _ : Fin d → ℝ => (1 : ℝ)) (cubePi d) :=
    integrableOn_const FT1c_cube_lt_top.ne
  refine (h2.add h1).mono' ((FT1c_measurable_om.pow_const _).aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (FT1c_om_pos p).le _)]
  refine le_trans (FT1c_om_pow_le _ p) (le_of_eq ?_)
  simp only [Pi.add_apply]
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, inv_pow]

/-- `C_γ = ∫_{[−π,π]^d} ω^{2γ}`. -/
private def FT1c_Cg (d γ : ℕ) : ℝ := ∫ p in cubePi d, FT1c_om p ^ (2 * γ)

/-- `∫_{[−π,π]^d} A² ω(R ρ(p))^{2γ} ≤ A² C_γ` for `R ≥ 1`. -/
private theorem FT1c_int_sq_le {γ : ℕ} (hγ : 2 * γ < d) {R : ℝ} (hR : 1 ≤ R) (A : ℝ) :
    IntegrableOn (fun p => (A * FT1c_om (R • FT1c_red p) ^ γ) ^ 2) (cubePi d) ∧
      ∫ p in cubePi d, (A * FT1c_om (R • FT1c_red p) ^ γ) ^ 2 ≤ A ^ 2 * FT1c_Cg d γ := by
  have heq : ∀ p ∈ cubePi d, (A * FT1c_om (R • FT1c_red p) ^ γ) ^ 2 =
      A ^ 2 * FT1c_om (R • p) ^ (2 * γ) := by
    intro p hp
    have hn : ‖R • FT1c_red p‖ = ‖R • p‖ := by
      rw [norm_smul, norm_smul, FT1c_norm_red_eq, FT1c_norm_tor_cube hp]
    rw [FT1c_om_congr hn, mul_pow, ← pow_mul, mul_comm γ 2]
  have hm : Measurable fun p : Fin d → ℝ => FT1c_om (R • p) ^ (2 * γ) :=
    (FT1c_measurable_om.comp (measurable_const_smul R)).pow_const _
  have hI : IntegrableOn (fun p => FT1c_om (R • p) ^ (2 * γ)) (cubePi d) := by
    refine (FT1c_integrableOn_om hγ).mono' hm.aestronglyMeasurable
      ((ae_restrict_iff' FT1c_measurableSet_cube).2 (Eventually.of_forall fun p _ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (FT1c_om_pos _).le _)]
    exact pow_le_pow_left₀ (FT1c_om_pos _).le (FT1c_om_smul_le hR p) _
  have hI' : IntegrableOn (fun p => A ^ 2 * FT1c_om (R • p) ^ (2 * γ)) (cubePi d) :=
    Integrable.const_mul hI (A ^ 2)
  constructor
  · exact IntegrableOn.congr_fun hI' (fun p hp => (heq p hp).symm) FT1c_measurableSet_cube
  · rw [setIntegral_congr_fun FT1c_measurableSet_cube heq, integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg A)
    refine setIntegral_mono_on hI (FT1c_integrableOn_om hγ) FT1c_measurableSet_cube
      fun p _ => pow_le_pow_left₀ (FT1c_om_pos _).le (FT1c_om_smul_le hR p) _

/-! ## The momentum Cauchy–Schwarz bound for the majorants `A ω(R ρ(·))^γ` -/

section CS

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- The constant of the momentum Cauchy–Schwarz bound for the majorants. -/
private def FT1c_K0 (d : ℕ) (γ : ι → ℕ) : ℝ :=
  (∏ c, (1 + √(FT1c_Cg d (γ c)))) * (2 * Real.pi) ^ (d * Fintype.card ι)

private theorem FT1c_K0_pos (γ : ι → ℕ) : 0 < FT1c_K0 d γ :=
  mul_pos (Finset.prod_pos fun c _ => by positivity) (pow_pos Real.two_pi_pos _)

private theorem FT1c_measurable_maj (R A : ℝ) (γ : ℕ) :
    Measurable fun p : Fin d → ℝ => A * FT1c_om (R • FT1c_red p) ^ γ :=
  measurable_const.mul ((FT1c_measurable_om.comp ((measurable_const_smul R).comp
    FT1c_measurable_red)).pow_const _)

/-- **The momentum Cauchy–Schwarz bound for the majorants**: for `R ≥ 1`, exponents `γ_c` with
`2γ_c < d`, `γ_c = 0` on `T₁ ∩ T₂`, and `A_c ≥ 0`, the product `Π_c A_c ω(R ρ(ℓ_c(q)))^{γ_c}` is
integrable on `([−π, π]^d)^L` with integral at most `K₀ Π_c A_c`, uniformly in `R` and in the
external momenta. -/
private theorem FT1c_cs {e : ι → V × V} {T₁ T₂ : List ι} (hT₁ : TreeEdges (T₁.map e))
    (hT₂ : TreeEdges (T₂.map e)) (γ : ι → ℕ) (hγ : ∀ c, 2 * γ c < d)
    (hγ0 : ∀ c, c ∈ T₁ → c ∈ T₂ → γ c = 0) {R : ℝ} (hR : 1 ≤ R) (A : ι → ℝ)
    (hA : ∀ c, 0 ≤ A c) (P : V → Fin d → ℝ) :
    IntegrableOn (fun q => ∏ c, A c * FT1c_om (R • FT1c_red (FT1a.edgeMom e T₁ P q c)) ^ γ c)
        (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d) ∧
      ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
          ∏ c, A c * FT1c_om (R • FT1c_red (FT1a.edgeMom e T₁ P q c)) ^ γ c ≤
        FT1c_K0 d γ * ∏ c, A c := by
  set g : ι → (Fin d → ℝ) → ℝ := fun c p => A c * FT1c_om (R • FT1c_red p) ^ γ c with hg
  have hg0 : ∀ c p, 0 ≤ g c p := fun c p => mul_nonneg (hA c) (pow_nonneg (FT1c_om_pos _).le _)
  have hgm : ∀ c, Measurable (g c) := fun c => FT1c_measurable_maj R (A c) (γ c)
  have hgp : ∀ c p (z : Fin d → ℤ), g c (p + fun i => 2 * Real.pi * z i) = g c p := by
    intro c p z; simp only [hg, FT1c_red_periodic]
  have hM : ∀ c, c ∈ T₁ → c ∈ T₂ → ∀ p, g c p ≤ A c := by
    intro c h1 h2 p; simp [hg, hγ0 c h1 h2]
  have hL2 : ∀ c, ¬ (c ∈ T₁ ∧ c ∈ T₂) → IntegrableOn (fun p => g c p ^ 2) (cubePi d) :=
    fun c _ => (FT1c_int_sq_le (hγ c) hR (A c)).1
  obtain ⟨hint, hle⟩ := FT1a.momentumCS e T₁ T₂ hT₁ hT₂ P g hg0 hgm hgp A hM hL2
  refine ⟨hint, le_trans hle ?_⟩
  have hsq : ∀ c, √(∫ p in cubePi d, g c p ^ 2) ≤ A c * (1 + √(FT1c_Cg d (γ c))) := by
    intro c
    have h := (FT1c_int_sq_le (hγ c) hR (A c)).2
    calc √(∫ p in cubePi d, g c p ^ 2) ≤ √(A c ^ 2 * FT1c_Cg d (γ c)) := Real.sqrt_le_sqrt h
      _ = A c * √(FT1c_Cg d (γ c)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hA c)]
      _ ≤ A c * (1 + √(FT1c_Cg d (γ c))) := by nlinarith [hA c]
  have hpi : √((2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
      Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂}))) ≤ (2 * Real.pi) ^ (d * Fintype.card ι) := by
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    have hx : (1 : ℝ) ≤ (2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
        Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂})) := one_le_pow₀ h1
    set x := (2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
        Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂}))
    calc √x ≤ √(x ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = x := Real.sqrt_sq (by linarith)
      _ ≤ _ := pow_le_pow_right₀ h1 (Nat.mul_le_mul_left _
          (le_trans (Nat.sub_le _ _) (Fintype.card_subtype_le _)))
  have hprod' : ∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, A c.1 ≤
      ∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, A c.1 * (1 + √(FT1c_Cg d (γ c.1))) :=
    Finset.prod_le_prod₀ (fun c _ => hA _) fun c _ => by
      nlinarith [hA c.1, Real.sqrt_nonneg (FT1c_Cg d (γ c.1))]
  have hsplit := FT1a_prod_split3 T₁ T₂ fun c => A c * (1 + √(FT1c_Cg d (γ c)))
  have hK : FT1c_K0 d γ * ∏ c, A c =
      (∏ c, A c * (1 + √(FT1c_Cg d (γ c)))) * (2 * Real.pi) ^ (d * Fintype.card ι) := by
    unfold FT1c_K0; rw [Finset.prod_mul_distrib]; ring
  rw [hK, hsplit]
  have hA0 : 0 ≤ ∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, A c.1 := Finset.prod_nonneg fun c _ => hA _
  calc (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, A c.1) *
        (∏ c : {c // c ∉ T₁}, √(∫ p in cubePi d, g c.1 p ^ 2)) *
        √((2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
          Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂}))) *
        ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, √(∫ p in cubePi d, g c.1 p ^ 2)
      ≤ (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, A c.1 * (1 + √(FT1c_Cg d (γ c.1)))) *
        (∏ c : {c // c ∉ T₁}, A c.1 * (1 + √(FT1c_Cg d (γ c.1)))) *
        (2 * Real.pi) ^ (d * Fintype.card ι) *
        ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, A c.1 * (1 + √(FT1c_Cg d (γ c.1))) := by
        have e1 : ∏ c : {c // c ∉ T₁}, √(∫ p in cubePi d, g c.1 p ^ 2) ≤
            ∏ c : {c // c ∉ T₁}, A c.1 * (1 + √(FT1c_Cg d (γ c.1))) :=
          Finset.prod_le_prod₀ (fun c _ => Real.sqrt_nonneg _) fun c _ => hsq c.1
        have e2 : ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, √(∫ p in cubePi d, g c.1 p ^ 2) ≤
            ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, A c.1 * (1 + √(FT1c_Cg d (γ c.1))) :=
          Finset.prod_le_prod₀ (fun c _ => Real.sqrt_nonneg _) fun c _ => hsq c.1
        have p1 : 0 ≤ ∏ c : {c // c ∉ T₁}, √(∫ p in cubePi d, g c.1 p ^ 2) :=
          Finset.prod_nonneg fun c _ => Real.sqrt_nonneg _
        have p2 : 0 ≤ ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, √(∫ p in cubePi d, g c.1 p ^ 2) :=
          Finset.prod_nonneg fun c _ => Real.sqrt_nonneg _
        have q0 : 0 ≤ ∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, A c.1 * (1 + √(FT1c_Cg d (γ c.1))) :=
          Finset.prod_nonneg fun c _ => mul_nonneg (hA _) (by positivity)
        have q1 : 0 ≤ ∏ c : {c // c ∉ T₁}, A c.1 * (1 + √(FT1c_Cg d (γ c.1))) :=
          Finset.prod_nonneg fun c _ => mul_nonneg (hA _) (by positivity)
        have hs0 := Real.sqrt_nonneg ((2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
          Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂})))
        have h2p : (0 : ℝ) ≤ (2 * Real.pi) ^ (d * Fintype.card ι) := by positivity
        refine mul_le_mul (mul_le_mul (mul_le_mul hprod' e1 p1 q0) hpi hs0
          (mul_nonneg q0 q1)) e2 p2 (mul_nonneg (mul_nonneg q0 q1) h2p)
    _ = _ := by ring

end CS

private theorem FT1c_cubeL_eq (A : Type*) [Fintype A] :
    (Set.univ.pi fun _ : A => cubePi d) = Metric.closedBall (0 : A → Fin d → ℝ) Real.pi := by
  ext k
  simp only [Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg Real.pi_pos.le]
  refine forall_congr' fun c => ?_
  rw [pi_norm_le_iff_of_nonneg Real.pi_pos.le]
  simp only [cubePi, Set.mem_univ_pi, Set.mem_Icc, Real.norm_eq_abs, abs_le]

section Box

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

private theorem FT1c_extMom_smul (e : ι → V × V) (T : List ι) (a : ℝ) (P : V → Fin d → ℝ) (f : ι) :
    FT1a.extMom e T (a • P) f = a • FT1a.extMom e T P f := by
  unfold FT1a.extMom
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.smul_apply, smul_comm a]

/-- The momenta are linear: `ℓ_c(a q; a P) = a ℓ_c(q; P)`. -/
private theorem FT1c_edgeMom_smul (e : ι → V × V) (T : List ι) (a : ℝ) (P : V → Fin d → ℝ)
    (q : {c // c ∉ T} → Fin d → ℝ) (c : ι) :
    FT1a.edgeMom e T (a • P) (a • q) c = a • FT1a.edgeMom e T P q c := by
  by_cases hc : c ∈ T
  · rw [FT1a.edgeMom_of_mem _ _ hc, FT1a.edgeMom_of_mem _ _ hc, FT1c_extMom_smul, smul_sub,
      Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp only [Pi.smul_apply, smul_comm a]
  · rw [FT1a.edgeMom_of_not_mem _ _ hc, FT1a.edgeMom_of_not_mem _ _ hc]
    rfl

private theorem FT1c_measurable_omProd {e : ι → V × V} {T : List ι} (γ : ι → ℕ) (P : V → Fin d → ℝ) :
    Measurable fun k : {c // c ∉ T} → Fin d → ℝ =>
      ∏ c, FT1c_om (FT1a.edgeMom e T P k c) ^ γ c :=
  Finset.measurable_prod _ fun c _ =>
    (FT1c_measurable_om.comp (FT1a_continuous_edgeMom P c).measurable).pow_const _

/-- `∫⁻ F = R^n ∫⁻ F(R ·)` for `R > 0` on `ℝ^n`, `n = dL`. -/
private theorem FT1c_lintegral_scale (A : Type*) [Fintype A] {R : ℝ} (hR : 0 < R)
    (F : (A → Fin d → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ k, F k = ENNReal.ofReal (R ^ (d * Fintype.card A)) * ∫⁻ y, F (R • y) := by
  have : (volume : Measure (A → Fin d → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hfin : Module.finrank ℝ (A → Fin d → ℝ) = d * Fintype.card A := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  have hmap := Measure.map_addHaar_smul (volume : Measure (A → Fin d → ℝ)) hR.ne'
  have h := lintegral_map (μ := volume) hF
    (measurable_const_smul R : Measurable fun y : A → Fin d → ℝ => R • y)
  rw [hmap, lintegral_smul_measure, hfin] at h
  rw [← h, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hR' : R ^ (d * Fintype.card A) * |(R ^ (d * Fintype.card A))⁻¹| = 1 := by
    rw [abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity)]
  rw [hR', ENNReal.ofReal_one, one_mul]

/-- **The momentum bound on a box**: `∫_{‖k‖ ≤ Rπ} Π_c ω(ℓ_c(k; P))^{γ_c} dk ≤ R^{dL} K₀` for `R ≥ 1`,
uniformly in the external momenta. -/
private theorem FT1c_box {e : ι → V × V} {T₁ T₂ : List ι} (hT₁ : TreeEdges (T₁.map e))
    (hT₂ : TreeEdges (T₂.map e)) (γ : ι → ℕ) (hγ : ∀ c, 2 * γ c < d)
    (hγ0 : ∀ c, c ∈ T₁ → c ∈ T₂ → γ c = 0) {R : ℝ} (hR : 1 ≤ R) (P : V → Fin d → ℝ) :
    ∫⁻ k in Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) (R * Real.pi),
        ENNReal.ofReal (∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c) ≤
      ENNReal.ofReal (R ^ (d * Fintype.card {c // c ∉ T₁}) * FT1c_K0 d γ) := by
  have hR0 : 0 < R := by linarith
  set F : ({c // c ∉ T₁} → Fin d → ℝ) → ℝ := fun k => ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c
  have hFm : Measurable F := FT1c_measurable_omProd γ P
  have hball : MeasurableSet (Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) (R * Real.pi)) :=
    measurableSet_closedBall
  rw [← lintegral_indicator hball, FT1c_lintegral_scale _ hR0 _
    ((hFm.ennreal_ofReal).indicator hball)]
  have hpt : ∀ y : {c // c ∉ T₁} → Fin d → ℝ,
      (Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) (R * Real.pi)).indicator
        (fun k => ENNReal.ofReal (F k)) (R • y) ≤
      (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d).indicator (fun q => ENNReal.ofReal
        (∏ c, 1 * FT1c_om (R • FT1c_red (FT1a.edgeMom e T₁ (R⁻¹ • P) q c)) ^ γ c)) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) Real.pi
    · have hy' : R • y ∈ Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) (R * Real.pi) := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hR0]
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        exact mul_le_mul_of_nonneg_left hy hR0.le
      rw [Set.indicator_of_mem hy', Set.indicator_of_mem (by rwa [FT1c_cubeL_eq])]
      refine ENNReal.ofReal_le_ofReal (Finset.prod_le_prod₀
        (fun c _ => pow_nonneg (FT1c_om_pos _).le _) fun c _ => ?_)
      rw [one_mul]
      have hm : FT1a.edgeMom e T₁ P (R • y) c = R • FT1a.edgeMom e T₁ (R⁻¹ • P) y c := by
        rw [← FT1c_edgeMom_smul, smul_smul, mul_inv_cancel₀ hR0.ne', one_smul]
      rw [hm]
      exact pow_le_pow_left₀ (FT1c_om_pos _).le (FT1c_om_le_red hR _) _
    · have hy' : R • y ∉ Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) (R * Real.pi) := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hR0]
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
        exact not_le.2 (mul_lt_mul_of_pos_left hy hR0)
      rw [Set.indicator_of_notMem hy']
      exact bot_le
  obtain ⟨hint, hle⟩ := FT1c_cs hT₁ hT₂ γ hγ hγ0 hR (fun _ => 1) (fun _ => zero_le_one)
    (R⁻¹ • P)
  have hnn : ∀ q, 0 ≤ ∏ c, (1 : ℝ) * FT1c_om (R • FT1c_red (FT1a.edgeMom e T₁ (R⁻¹ • P) q c)) ^ γ c :=
    fun q => Finset.prod_nonneg fun c _ => mul_nonneg zero_le_one (pow_nonneg (FT1c_om_pos _).le _)
  calc ENNReal.ofReal (R ^ (d * Fintype.card {c // c ∉ T₁})) *
        ∫⁻ y, (Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) (R * Real.pi)).indicator
          (fun k => ENNReal.ofReal (F k)) (R • y)
      ≤ ENNReal.ofReal (R ^ (d * Fintype.card {c // c ∉ T₁})) *
        ∫⁻ y, (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d).indicator (fun q => ENNReal.ofReal
          (∏ c, 1 * FT1c_om (R • FT1c_red (FT1a.edgeMom e T₁ (R⁻¹ • P) q c)) ^ γ c)) y := by
        gcongr with y
        exact hpt y
    _ = ENNReal.ofReal (R ^ (d * Fintype.card {c // c ∉ T₁})) * ENNReal.ofReal
          (∫ q in Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d,
            ∏ c, 1 * FT1c_om (R • FT1c_red (FT1a.edgeMom e T₁ (R⁻¹ • P) q c)) ^ γ c) := by
        rw [lintegral_indicator (MeasurableSet.univ_pi fun _ => FT1c_measurableSet_cube),
          ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
    _ ≤ ENNReal.ofReal (R ^ (d * Fintype.card {c // c ∉ T₁})) *
          ENNReal.ofReal (FT1c_K0 d γ * ∏ _c : ι, (1 : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (R ^ (d * Fintype.card {c // c ∉ T₁}) * FT1c_K0 d γ) := by
        rw [Finset.prod_const_one, mul_one, ← ENNReal.ofReal_mul (by positivity)]

/-- **The momentum bound on `ℝ^{dL}`**: for `N ≥ dL + 1`,
`∫ (1 + ‖k‖)^{-N} Π_c ω(ℓ_c(k; P))^{γ_c} dk ≤ 2^{N+1} K₀`, uniformly in the external momenta. -/
private theorem FT1c_whole {e : ι → V × V} {T₁ T₂ : List ι} (hT₁ : TreeEdges (T₁.map e))
    (hT₂ : TreeEdges (T₂.map e)) (γ : ι → ℕ) (hγ : ∀ c, 2 * γ c < d)
    (hγ0 : ∀ c, c ∈ T₁ → c ∈ T₂ → γ c = 0) (N : ℕ)
    (hN : d * Fintype.card {c // c ∉ T₁} + 1 ≤ N) (P : V → Fin d → ℝ) :
    ∫⁻ k, ENNReal.ofReal (((1 + ‖k‖) ^ N)⁻¹ *
        ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c) ≤
      ENNReal.ofReal (2 ^ (N + 1) * FT1c_K0 d γ) := by
  set n := d * Fintype.card {c // c ∉ T₁}
  set F : ({c // c ∉ T₁} → Fin d → ℝ) → ℝ := fun k => ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c
  have hFm : Measurable F := FT1c_measurable_omProd γ P
  have hF0 : ∀ k, 0 ≤ F k := fun k => Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _
  set B : ℕ → Set ({c // c ∉ T₁} → Fin d → ℝ) := fun j => Metric.closedBall 0 (2 ^ j * Real.pi)
  set a : ℕ → ℝ := fun j => (2 : ℝ) ^ N / ((2 : ℝ) ^ j) ^ N
  have hpt : ∀ k, ENNReal.ofReal (((1 + ‖k‖) ^ N)⁻¹ * F k) ≤
      ∑' j, ENNReal.ofReal (a j) * (B j).indicator (fun k => ENNReal.ofReal (F k)) k := by
    intro k
    have hex : ∃ j : ℕ, ‖k‖ ≤ 2 ^ j * Real.pi := by
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ‖k‖ (by norm_num : (1 : ℝ) < 2)
      exact ⟨j, le_trans hj.le (le_mul_of_one_le_right (by positivity)
        (by linarith [Real.two_le_pi]))⟩
    classical
    set j₀ := Nat.find hex
    refine le_trans ?_ (ENNReal.le_tsum j₀)
    rw [Set.indicator_of_mem (by
      simp only [B, Metric.mem_closedBall, dist_zero_right]; exact Nat.find_spec hex),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (hF0 k))
    have h1 : (1 : ℝ) ≤ 1 + ‖k‖ := le_add_of_nonneg_right (norm_nonneg k)
    rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
    · simp only [a, h0, pow_zero, one_pow, div_one]
      calc ((1 + ‖k‖) ^ N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
        _ ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    · have hlt : ¬ ‖k‖ ≤ 2 ^ (j₀ - 1) * Real.pi := Nat.find_min hex (by omega)
      push Not at hlt
      have h2 : (2 : ℝ) ^ (j₀ - 1) ≤ 1 + ‖k‖ := by
        have : (2 : ℝ) ^ (j₀ - 1) ≤ 2 ^ (j₀ - 1) * Real.pi :=
          le_mul_of_one_le_right (by positivity) (by linarith [Real.two_le_pi])
        linarith
      have h3 : a j₀ = (((2 : ℝ) ^ (j₀ - 1)) ^ N)⁻¹ := by
        simp only [a]
        have : (2 : ℝ) ^ j₀ = 2 * 2 ^ (j₀ - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [this, mul_pow, div_mul_eq_div_div, div_self (by positivity), one_div]
      rw [h3]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2 N)
  have hterm : ∀ j, ∫⁻ k, ENNReal.ofReal (a j) * (B j).indicator (fun k => ENNReal.ofReal (F k)) k ≤
      ENNReal.ofReal (2 ^ N * FT1c_K0 d γ * (1 / 2) ^ j) := by
    intro j
    rw [lintegral_const_mul _ ((hFm.ennreal_ofReal).indicator measurableSet_closedBall),
      lintegral_indicator measurableSet_closedBall]
    have hb := FT1c_box hT₁ hT₂ γ hγ hγ0 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ j) P
    refine le_trans (mul_le_mul_right hb _) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hK := (FT1c_K0_pos (d := d) γ).le
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    simp only [a]
    have hpow : ((2 : ℝ) ^ j) ^ n / ((2 : ℝ) ^ j) ^ N ≤ (1 / 2) ^ j := by
      have hN' : ((2 : ℝ) ^ j) ^ n * 2 ^ j ≤ ((2 : ℝ) ^ j) ^ N := by
        calc ((2 : ℝ) ^ j) ^ n * 2 ^ j = ((2 : ℝ) ^ j) ^ (n + 1) := by rw [pow_succ]
          _ ≤ ((2 : ℝ) ^ j) ^ N := pow_le_pow_right₀ h2j hN
      rw [div_le_iff₀ (by positivity)]
      calc ((2 : ℝ) ^ j) ^ n = ((2 : ℝ) ^ j) ^ n * 2 ^ j * (1 / 2) ^ j := by
            rw [mul_assoc, ← mul_pow]; norm_num
        _ ≤ ((2 : ℝ) ^ j) ^ N * (1 / 2) ^ j := by gcongr
        _ = (1 / 2) ^ j * ((2 : ℝ) ^ j) ^ N := mul_comm _ _
    calc (2 : ℝ) ^ N / ((2 : ℝ) ^ j) ^ N * (((2 : ℝ) ^ j) ^ n * FT1c_K0 d γ)
        = 2 ^ N * FT1c_K0 d γ * (((2 : ℝ) ^ j) ^ n / ((2 : ℝ) ^ j) ^ N) := by ring
      _ ≤ 2 ^ N * FT1c_K0 d γ * (1 / 2) ^ j := by gcongr
  calc ∫⁻ k, ENNReal.ofReal (((1 + ‖k‖) ^ N)⁻¹ * F k)
      ≤ ∫⁻ k, ∑' j, ENNReal.ofReal (a j) * (B j).indicator (fun k => ENNReal.ofReal (F k)) k :=
        lintegral_mono hpt
    _ = ∑' j, ∫⁻ k, ENNReal.ofReal (a j) * (B j).indicator (fun k => ENNReal.ofReal (F k)) k :=
        lintegral_tsum fun j => (((hFm.ennreal_ofReal).indicator
          measurableSet_closedBall).const_mul _).aemeasurable
    _ ≤ ∑' j, ENNReal.ofReal (2 ^ N * FT1c_K0 d γ * (1 / 2) ^ j) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (2 ^ (N + 1) * FT1c_K0 d γ) := by
        have hs : Summable fun j : ℕ => 2 ^ N * FT1c_K0 d γ * ((1 : ℝ) / 2) ^ j :=
          (summable_geometric_two).mul_left _
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by
          have := (FT1c_K0_pos (d := d) γ).le; positivity) hs, tsum_mul_left, tsum_geometric_two]
        congr 1
        ring

end Box

/-- `|Π a − Π b| ≤ |ι| ε Π m` when `|a_c|, |b_c| ≤ m_c` and `|a_c − b_c| ≤ ε m_c`. -/
private theorem FT1c_telescope {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) (m : ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (ha : ∀ c, ‖a c‖ ≤ m c) (hb : ∀ c, ‖b c‖ ≤ m c)
    (hab : ∀ c, ‖a c - b c‖ ≤ ε * m c) :
    ‖∏ c, a c - ∏ c, b c‖ ≤ Fintype.card ι * ε * ∏ c, m c := by
  have hm : ∀ c, 0 ≤ m c := fun c => le_trans (norm_nonneg _) (ha c)
  have key : ∀ s : Finset ι, ‖∏ c ∈ s, a c - ∏ c ∈ s, b c‖ ≤ s.card * ε * ∏ c ∈ s, m c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi,
        Finset.card_insert_of_notMem hi]
      have hpb : ‖∏ c ∈ s, b c‖ ≤ ∏ c ∈ s, m c := by
        rw [norm_prod]; exact Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) fun c _ => hb c
      have hpm : 0 ≤ ∏ c ∈ s, m c := Finset.prod_nonneg fun c _ => hm c
      have he : a i * ∏ c ∈ s, a c - b i * ∏ c ∈ s, b c =
          a i * (∏ c ∈ s, a c - ∏ c ∈ s, b c) + (a i - b i) * ∏ c ∈ s, b c := by ring
      rw [he]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
      calc ‖a i‖ * ‖∏ c ∈ s, a c - ∏ c ∈ s, b c‖ + ‖a i - b i‖ * ‖∏ c ∈ s, b c‖
          ≤ m i * (s.card * ε * ∏ c ∈ s, m c) + ε * m i * ∏ c ∈ s, m c := by
            exact add_le_add (mul_le_mul (ha i) ih (norm_nonneg _) (hm i))
              (mul_le_mul (hab i) hpb (norm_nonneg _) (mul_nonneg hε (hm i)))
        _ = ((s.card + 1 : ℕ) : ℝ) * ε * (m i * ∏ c ∈ s, m c) := by push_cast; ring
  exact key Finset.univ

/-- If a nonnegative sum over `s ⊆ ι` is at least `t > 0`, one term is at least `t / (|ι| + 1)`. -/
private theorem FT1c_exists_big {ι : Type*} [Fintype ι] (s : Finset ι) (f : ι → ℝ) (_hf : ∀ c, 0 ≤ f c)
    {t : ℝ} (ht : 0 < t) (hs : t ≤ ∑ c ∈ s, f c) :
    ∃ c ∈ s, t / (Fintype.card ι + 1) ≤ f c := by
  by_contra h
  push Not at h
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty] at hs; linarith
  · have h1 : ∑ c ∈ s, f c < ∑ _c ∈ s, t / (Fintype.card ι + 1) :=
      Finset.sum_lt_sum_of_nonempty hne h
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : (s.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ s
    have h3 : (s.card : ℝ) * (t / (Fintype.card ι + 1)) ≤ t := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith

section Graph

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- The product of the decay factors, `1` on the dotted edges. -/
private def FT1c_dec (dot : ι → Prop) [DecidablePred dot] (K : ℕ) (r : ι → Fin d → ℝ) : ℝ :=
  ∏ c, if dot c then 1 else ((1 + ‖r c‖) ^ K)⁻¹

private theorem FT1c_dec_nonneg (dot : ι → Prop) [DecidablePred dot] (K : ℕ) (r : ι → Fin d → ℝ) :
    0 ≤ FT1c_dec dot K r :=
  Finset.prod_nonneg fun c _ => by split_ifs <;> positivity

private theorem FT1c_dec_le_one (dot : ι → Prop) [DecidablePred dot] (K : ℕ) (r : ι → Fin d → ℝ) :
    FT1c_dec dot K r ≤ 1 :=
  Finset.prod_le_one₀ (fun c _ => by split_ifs <;> positivity) fun c _ => by
    split_ifs
    · exact le_rfl
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))

private theorem FT1c_dec_le (dot : ι → Prop) [DecidablePred dot] (K : ℕ) (r : ι → Fin d → ℝ) {c : ι}
    (hc : ¬ dot c) : FT1c_dec dot K r ≤ ((1 + ‖r c‖) ^ K)⁻¹ := by
  unfold FT1c_dec
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), if_neg hc]
  refine mul_le_of_le_one_right (by positivity) ?_
  exact Finset.prod_le_one₀ (fun c _ => by split_ifs <;> positivity) fun c _ => by
    split_ifs
    · exact le_rfl
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))

/-- `(1 + t/a)^{-K} ≤ a^K (1 + t)^{-K}` for `a ≥ 1`, `t ≥ 0`. -/
private theorem FT1c_inv_pow_div {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) (K : ℕ) :
    ((1 + t / a) ^ K)⁻¹ ≤ a ^ K * ((1 + t) ^ K)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have h1 : (1 + t) ≤ a * (1 + t / a) := by
    rw [mul_add, mul_div_cancel₀ _ ha0.ne', mul_one]; linarith
  have hx : 0 < (1 + t / a) ^ K := by positivity
  have hy : 0 < (1 + t) ^ K := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hy, inv_mul_eq_div, div_le_iff₀ hx, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h1 K

/-- **The decay on `ℝ^{dL}`**: the product of the decay factors of the edge momenta is at most
`(2|ι| + 2)^K (1 + 2 Σ_v ‖P_v‖)^K (1 + ‖k‖)^{-K}`, and at most `(2|ι| + 2)^K (1 + ‖k‖)^{-K}` when
`‖k‖ ≥ 2 Σ_v ‖P_v‖`. -/
private theorem FT1c_dec_bound {e : ι → V × V} {T : List ι} (hT : TreeEdges (T.map e))
    (dot : ι → Prop) [DecidablePred dot]
    (hcut : ∀ c, dot c → ∃ S : V → Prop, S (e c).2 ∧ ¬ S (e c).1 ∧
      ∀ c', dot c' → c' ≠ c → (S (e c').2 ↔ S (e c').1))
    (P : V → Fin d → ℝ) (hP : ∑ v, P v = 0) (K : ℕ) (k : {c // c ∉ T} → Fin d → ℝ) :
    FT1c_dec dot K (FT1a.edgeMom e T P k) ≤
        (2 * Fintype.card ι + 2) ^ K * (1 + 2 * ∑ v, ‖P v‖) ^ K * ((1 + ‖k‖) ^ K)⁻¹ ∧
      (2 * ∑ v, ‖P v‖ ≤ ‖k‖ →
        FT1c_dec dot K (FT1a.edgeMom e T P k) ≤ (2 * Fintype.card ι + 2) ^ K * ((1 + ‖k‖) ^ K)⁻¹) := by
  set ℓ := FT1a.edgeMom e T P k
  set SP := ∑ v, ‖P v‖
  have hSP : 0 ≤ SP := Finset.sum_nonneg fun v _ => norm_nonneg _
  have hcb := FT1c_cutBound hT dot hcut (AddMonoidHom.id _) P hP k
  simp only [AddMonoidHom.id_apply] at hcb
  have hk : ‖k‖ ≤ SP + ∑ c' ∈ Finset.univ.filter (fun c' => ¬ dot c'), ‖ℓ c'‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c => ?_
    have := hcb c.1
    rw [FT1a.edgeMom_of_not_mem P k c.2] at this
    exact this
  have hι : (1 : ℝ) ≤ 2 * Fintype.card ι + 2 := by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  have hbig : 2 * SP ≤ ‖k‖ →
      FT1c_dec dot K ℓ ≤ (2 * Fintype.card ι + 2) ^ K * ((1 + ‖k‖) ^ K)⁻¹ := by
    intro h2
    rcases eq_or_lt_of_le (norm_nonneg k) with h0 | hpos
    · rw [← h0, add_zero, one_pow, inv_one, mul_one]
      exact le_trans (FT1c_dec_le_one dot K ℓ) (one_le_pow₀ hι)
    · obtain ⟨c, hc, hcbig⟩ := FT1c_exists_big (Finset.univ.filter fun c' => ¬ dot c')
        (fun c' => ‖ℓ c'‖) (fun _ => norm_nonneg _)
        (by positivity : 0 < ‖k‖ / 2) (by linarith)
      have hc' : ¬ dot c := (Finset.mem_filter.1 hc).2
      refine le_trans (FT1c_dec_le dot K ℓ hc') ?_
      have h3 : ‖k‖ / (2 * Fintype.card ι + 2) ≤ ‖ℓ c‖ := by
        calc ‖k‖ / (2 * Fintype.card ι + 2) = ‖k‖ / 2 / (Fintype.card ι + 1) := by
              rw [div_div]; ring_nf
          _ ≤ ‖ℓ c‖ := hcbig
      calc ((1 + ‖ℓ c‖) ^ K)⁻¹ ≤ ((1 + ‖k‖ / (2 * Fintype.card ι + 2)) ^ K)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) K)
        _ ≤ _ := FT1c_inv_pow_div hι (norm_nonneg k) K
  refine ⟨?_, hbig⟩
  by_cases h2 : 2 * SP ≤ ‖k‖
  · refine le_trans (hbig h2) ?_
    have h1 : (1 : ℝ) ≤ (1 + 2 * SP) ^ K := one_le_pow₀ (by linarith)
    calc (2 * (Fintype.card ι : ℝ) + 2) ^ K * ((1 + ‖k‖) ^ K)⁻¹
        = (2 * (Fintype.card ι : ℝ) + 2) ^ K * 1 * ((1 + ‖k‖) ^ K)⁻¹ := by ring
      _ ≤ (2 * (Fintype.card ι : ℝ) + 2) ^ K * (1 + 2 * SP) ^ K * ((1 + ‖k‖) ^ K)⁻¹ := by
        gcongr
  · push Not at h2
    refine le_trans (FT1c_dec_le_one dot K ℓ) ?_
    have h4 : ((1 + ‖k‖) ^ K)⁻¹ * (1 + 2 * SP) ^ K ≥ 1 := by
      rw [ge_iff_le, inv_mul_eq_div, one_le_div (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (by linarith) K
    calc (1 : ℝ) ≤ ((1 + ‖k‖) ^ K)⁻¹ * (1 + 2 * SP) ^ K := h4
      _ ≤ (2 * Fintype.card ι + 2) ^ K * (1 + 2 * SP) ^ K * ((1 + ‖k‖) ^ K)⁻¹ := by
        rw [mul_comm (((1 + ‖k‖) ^ K)⁻¹)]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hι)

end Graph

section Graph

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- The product of bounds `‖g_c(r_c)‖ ≤ B ω(r_c)^{γ_c} (1 or (1 + ‖r_c‖)^{-K})`. -/
private theorem FT1c_prod_bound (dot : ι → Prop) [DecidablePred dot] (γ : ι → ℕ) (K : ℕ) {B : ℝ}
    (_hB : 0 ≤ B) (g : ι → (Fin d → ℝ) → ℂ)
    (hg : ∀ c r, ‖g c r‖ ≤ B * FT1c_om r ^ γ c * (if dot c then 1 else ((1 + ‖r‖) ^ K)⁻¹))
    (r : ι → Fin d → ℝ) :
    ‖∏ c, g c (r c)‖ ≤ B ^ Fintype.card ι * FT1c_dec dot K r * ∏ c, FT1c_om (r c) ^ γ c := by
  rw [norm_prod]
  calc ∏ c, ‖g c (r c)‖ ≤ ∏ c, B * FT1c_om (r c) ^ γ c *
        (if dot c then 1 else ((1 + ‖r c‖) ^ K)⁻¹) :=
        Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) fun c _ => hg c (r c)
    _ = _ := by
        unfold FT1c_dec
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        ring

private theorem FT1c_cutCoef_abs_le (e : ι → V × V) (T : List ι) (f c : ι) :
    |(FT1a.cutCoef e T f c : ℝ)| ≤ 1 := by
  unfold FT1a.cutCoef FT1a.cutInd
  split_ifs <;> simp

private theorem FT1c_extMom_norm_le (e : ι → V × V) (T : List ι) (P : V → Fin d → ℝ) (f : ι) :
    ‖FT1a.extMom e T P f‖ ≤ ∑ v, ‖P v‖ := by
  unfold FT1a.extMom
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun v _ => ?_)
  rw [norm_smul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  unfold FT1a.cutInd
  split_ifs <;> simp

/-- `‖ℓ_c(q; P)‖ ≤ Σ_v ‖P_v‖ + |ι| ‖q‖`. -/
private theorem FT1c_edgeMom_norm_le (e : ι → V × V) (T : List ι) (P : V → Fin d → ℝ)
    (q : {c // c ∉ T} → Fin d → ℝ) (c : ι) :
    ‖FT1a.edgeMom e T P q c‖ ≤ ∑ v, ‖P v‖ + Fintype.card ι * ‖q‖ := by
  have hP : 0 ≤ ∑ v, ‖P v‖ := Finset.sum_nonneg fun v _ => norm_nonneg _
  by_cases hc : c ∈ T
  · rw [FT1a.edgeMom_of_mem P q hc]
    refine le_trans (norm_sub_le _ _) (add_le_add (FT1c_extMom_norm_le e T P c) ?_)
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ c' : {c // c ∉ T}, ‖(FT1a.cutCoef e T c c'.1 : ℝ) • q c'‖
        ≤ ∑ _c' : {c // c ∉ T}, ‖q‖ := Finset.sum_le_sum fun c' _ => by
          rw [norm_smul, Real.norm_eq_abs]
          exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (FT1c_cutCoef_abs_le e T c c'.1))
            (norm_le_pi_norm q c')
      _ = Fintype.card {c // c ∉ T} * ‖q‖ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card ι * ‖q‖ := by
        gcongr
        exact_mod_cast Fintype.card_subtype_le _
  · rw [FT1a.edgeMom_of_not_mem P q hc]
    have h1 : (1 : ℝ) ≤ Fintype.card ι := by
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨c⟩
      exact_mod_cast this
    calc ‖q ⟨c, hc⟩‖ ≤ ‖q‖ := norm_le_pi_norm q _
      _ ≤ Fintype.card ι * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) h1
      _ ≤ _ := le_add_of_nonneg_left hP

/-- The external momenta `P_v = a_v p`. -/
private theorem FT1c_sum_ext (a : V → ℝ) (ha : ∑ v, a v = 0) (p : Fin d → ℝ) :
    ∑ v, a v • p = 0 := by rw [← Finset.sum_smul, ha, zero_smul]

private theorem FT1c_norm_ext (a : V → ℝ) (ha1 : ∀ v, |a v| ≤ 1) (p : Fin d → ℝ) :
    ∑ v, ‖a v • p‖ ≤ Fintype.card V * ‖p‖ := by
  calc ∑ v, ‖a v • p‖ ≤ ∑ _v : V, ‖p‖ := Finset.sum_le_sum fun v _ => by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (ha1 v)
    _ = Fintype.card V * ‖p‖ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem FT1c_continuous_edgeMom2 (e : ι → V × V) (T : List ι) (a : V → ℝ) (c : ι) :
    Continuous fun z : (Fin d → ℝ) × ({c // c ∉ T} → Fin d → ℝ) =>
      FT1a.edgeMom e T (fun v => a v • z.1) z.2 c := by
  by_cases hc : c ∈ T
  · simp_rw [FT1a.edgeMom_of_mem _ _ hc, FT1a.extMom]
    fun_prop
  · simp_rw [FT1a.edgeMom_of_not_mem _ _ hc]
    fun_prop

/-- The scaling `q = k / R` on `([−π, π]^d)^L`. -/
private theorem FT1c_integral_scale (A : Type*) [Fintype A] {R : ℝ} (hR : 0 < R)
    (F : (A → Fin d → ℝ) → ℂ) :
    ∫ q in Set.univ.pi (fun _ : A => cubePi d), F (R • q) =
      ((R ^ (d * Fintype.card A) : ℝ) : ℂ)⁻¹ *
        ∫ k in Metric.closedBall (0 : A → Fin d → ℝ) (R * Real.pi), F k := by
  have : (volume : Measure (A → Fin d → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hfin : Module.finrank ℝ (A → Fin d → ℝ) = d * Fintype.card A := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  set G := (Metric.closedBall (0 : A → Fin d → ℝ) (R * Real.pi)).indicator F
  have hG : ∀ q, G (R • q) = (Set.univ.pi fun _ : A => cubePi d).indicator (fun q => F (R • q)) q := by
    intro q
    rw [FT1c_cubeL_eq]
    by_cases hq : q ∈ Metric.closedBall (0 : A → Fin d → ℝ) Real.pi
    · rw [Set.indicator_of_mem hq]
      show (Metric.closedBall (0 : A → Fin d → ℝ) (R * Real.pi)).indicator F (R • q) = _
      rw [Set.indicator_of_mem]
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      rw [Metric.mem_closedBall, dist_zero_right] at hq
      exact mul_le_mul_of_nonneg_left hq hR.le
    · rw [Set.indicator_of_notMem hq]
      show (Metric.closedBall (0 : A → Fin d → ℝ) (R * Real.pi)).indicator F (R • q) = _
      rw [Set.indicator_of_notMem]
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hq
      exact not_le.2 (mul_lt_mul_of_pos_left hq hR)
  have h := Measure.integral_comp_smul (volume : Measure (A → Fin d → ℝ)) G R
  simp_rw [hG] at h
  rw [integral_indicator (MeasurableSet.univ_pi fun _ => FT1c_measurableSet_cube),
    integral_indicator measurableSet_closedBall, hfin] at h
  rw [h, abs_of_pos (by positivity), Complex.real_smul, Complex.ofReal_inv]

/-- The weight integral of `FT1c_whole` as a Bochner integral. -/
private theorem FT1c_whole_int {e : ι → V × V} {T₁ T₂ : List ι} (hT₁ : TreeEdges (T₁.map e))
    (hT₂ : TreeEdges (T₂.map e)) (γ : ι → ℕ) (hγ : ∀ c, 2 * γ c < d)
    (hγ0 : ∀ c, c ∈ T₁ → c ∈ T₂ → γ c = 0) (N : ℕ)
    (hN : d * Fintype.card {c // c ∉ T₁} + 1 ≤ N) (P : V → Fin d → ℝ) :
    Integrable (fun k : {c // c ∉ T₁} → Fin d → ℝ => ((1 + ‖k‖) ^ N)⁻¹ *
        ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c) ∧
      ∫ k, ((1 + ‖k‖) ^ N)⁻¹ * ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c ≤
        2 ^ (N + 1) * FT1c_K0 d γ := by
  have hm : Measurable fun k : {c // c ∉ T₁} → Fin d → ℝ => ((1 + ‖k‖) ^ N)⁻¹ *
      ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c :=
    ((measurable_const.add continuous_norm.measurable).pow_const _).inv.mul
      (FT1c_measurable_omProd γ P)
  have h0 : ∀ k : {c // c ∉ T₁} → Fin d → ℝ, 0 ≤ ((1 + ‖k‖) ^ N)⁻¹ *
      ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c :=
    fun k => mul_nonneg (by positivity)
      (Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _)
  have hl := FT1c_whole hT₁ hT₂ γ hγ hγ0 N hN P
  have hfin : HasFiniteIntegral (fun k : {c // c ∉ T₁} → Fin d → ℝ => ((1 + ‖k‖) ^ N)⁻¹ *
      ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c) :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).2
      (lt_of_le_of_lt hl ENNReal.ofReal_lt_top)
  refine ⟨⟨hm.aestronglyMeasurable, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by have := (FT1c_K0_pos (d := d) γ).le; positivity) hl

end Graph

section Graph

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- The `W`-free momentum integral `Ψ(k) = (2π)^{-dL} ∫_{ℝ^{dL}} Π_c G_c(ℓ_c(k'; a k)) dk'` with the
external momenta `a_v k`. -/
private def FT1c_Psi (e : ι → V × V) (T : List ι) (a : V → ℝ) (G : ι → (Fin d → ℝ) → ℂ)
    (k : Fin d → ℝ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T}))⁻¹ *
    ∫ k', ∏ c, G c (FT1a.edgeMom e T (fun v => a v • k) k' c)

private theorem FT1c_measurable_Psi (e : ι → V × V) (T : List ι) (a : V → ℝ)
    (G : ι → (Fin d → ℝ) → ℂ) (hG : ∀ c, Measurable (G c)) :
    Measurable (FT1c_Psi e T a G) := by
  have hm : Measurable fun z : (Fin d → ℝ) × ({c // c ∉ T} → Fin d → ℝ) =>
      ∏ c, G c (FT1a.edgeMom e T (fun v => a v • z.1) z.2 c) :=
    Finset.measurable_prod _ fun c _ => (hG c).comp (FT1c_continuous_edgeMom2 e T a c).measurable
  have h := (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  exact measurable_const.mul h

private theorem FT1c_integrableOn_of_le {A : Type*} [Fintype A] {s : Set (A → Fin d → ℝ)}
    (hs : MeasurableSet s) {F : (A → Fin d → ℝ) → ℂ} {M : (A → Fin d → ℝ) → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict s)) (hM : IntegrableOn M s)
    (hle : ∀ q ∈ s, ‖F q‖ ≤ M q) : IntegrableOn F s :=
  hM.mono' hF ((ae_restrict_iff' hs).2 (Eventually.of_forall hle))

/-- **The `W`-free integrand on `ℝ^{dL}`**: under the bounds `‖G_c(r)‖ ≤ B ω(r)^{γ_c}` times
`(1 + ‖r‖)^{-2N}` off the dotted edges, `N ≥ dL + 1`, the integrand is integrable, and outside the
box `‖k‖ ≤ Rπ` with `2 Σ_v ‖P_v‖ ≤ Rπ` its integral is at most `c (1 + Rπ)^{-N}`. -/
private theorem FT1c_wfree {e : ι → V × V} {T₁ T₂ : List ι} (hT₁ : TreeEdges (T₁.map e))
    (hT₂ : TreeEdges (T₂.map e)) (dot : ι → Prop) [DecidablePred dot]
    (hcut : ∀ c, dot c → ∃ S : V → Prop, S (e c).2 ∧ ¬ S (e c).1 ∧
      ∀ c', dot c' → c' ≠ c → (S (e c').2 ↔ S (e c').1))
    (γ : ι → ℕ) (hγ : ∀ c, 2 * γ c < d) (hγ0 : ∀ c, c ∈ T₁ → c ∈ T₂ → γ c = 0)
    (N : ℕ) (hN : d * Fintype.card {c // c ∉ T₁} + 1 ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (G : ι → (Fin d → ℝ) → ℂ) (hGm : ∀ c, Measurable (G c))
    (hG : ∀ c r, ‖G c r‖ ≤ B * FT1c_om r ^ γ c *
      (if dot c then 1 else ((1 + ‖r‖) ^ (2 * N))⁻¹))
    (P : V → Fin d → ℝ) (hP : ∑ v, P v = 0) :
    Integrable (fun k => ∏ c, G c (FT1a.edgeMom e T₁ P k c)) ∧
      ∀ R : ℝ, 2 * ∑ v, ‖P v‖ ≤ R * Real.pi →
        ‖∫ k in (Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) (R * Real.pi))ᶜ,
            ∏ c, G c (FT1a.edgeMom e T₁ P k c)‖ ≤
          B ^ Fintype.card ι * (2 * Fintype.card ι + 2) ^ (2 * N) *
            ((1 + R * Real.pi) ^ N)⁻¹ * (2 ^ (N + 1) * FT1c_K0 d γ) := by
  obtain ⟨hwi, hwle⟩ := FT1c_whole_int hT₁ hT₂ γ hγ hγ0 N hN P
  set w : ({c // c ∉ T₁} → Fin d → ℝ) → ℝ := fun k => ((1 + ‖k‖) ^ N)⁻¹ *
    ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c
  have hw0 : ∀ k, 0 ≤ w k := fun k => mul_nonneg (by positivity)
    (Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _)
  have hFm : AEStronglyMeasurable (fun k : {c // c ∉ T₁} → Fin d → ℝ =>
      ∏ c, G c (FT1a.edgeMom e T₁ P k c)) volume :=
    (Finset.measurable_prod _ fun c _ =>
      (hGm c).comp (FT1a_continuous_edgeMom P c).measurable).aestronglyMeasurable
  have hpb := fun k : {c // c ∉ T₁} → Fin d → ℝ =>
    FT1c_prod_bound dot γ (2 * N) hB G hG (FT1a.edgeMom e T₁ P k)
  obtain ⟨hdb⟩ := And.intro (fun k => FT1c_dec_bound hT₁ dot hcut P hP (2 * N) k) True.intro
  set SP := ∑ v, ‖P v‖
  have hι : (1 : ℝ) ≤ 2 * Fintype.card ι + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  have hpow : ∀ k : {c // c ∉ T₁} → Fin d → ℝ,
      ((1 + ‖k‖) ^ (2 * N))⁻¹ ≤ ((1 + ‖k‖) ^ N)⁻¹ := fun k =>
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg k))
      (by omega))
  refine ⟨?_, fun R hR => ?_⟩
  · refine (hwi.const_mul (B ^ Fintype.card ι * (2 * Fintype.card ι + 2) ^ (2 * N) *
      (1 + 2 * SP) ^ (2 * N))).mono' hFm (Eventually.of_forall fun k => ?_)
    refine le_trans (hpb k) ?_
    have h1 := (hdb k).1
    have hprod : 0 ≤ ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c :=
      Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _
    calc B ^ Fintype.card ι * FT1c_dec dot (2 * N) (FT1a.edgeMom e T₁ P k) *
          ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c
        ≤ B ^ Fintype.card ι * ((2 * Fintype.card ι + 2) ^ (2 * N) * (1 + 2 * SP) ^ (2 * N) *
          ((1 + ‖k‖) ^ N)⁻¹) * ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c := by
          gcongr
          refine le_trans h1 ?_
          exact mul_le_mul_of_nonneg_left (hpow k) (by positivity)
      _ = _ := by simp only [w]; ring
  · have hint : IntegrableOn (fun k => B ^ Fintype.card ι * (2 * Fintype.card ι + 2) ^ (2 * N) *
        ((1 + R * Real.pi) ^ N)⁻¹ * w k)
        (Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) (R * Real.pi))ᶜ :=
      (hwi.const_mul _).integrableOn
    refine le_trans (norm_integral_le_of_norm_le hint ((ae_restrict_iff'
      measurableSet_closedBall.compl).2 (Eventually.of_forall fun k hk => ?_))) ?_
    · refine le_trans (hpb k) ?_
      rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hk
      have h2 := (hdb k).2 (by linarith)
      have hprod : 0 ≤ ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c :=
        Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _
      have h3 : ((1 + ‖k‖) ^ (2 * N))⁻¹ ≤ ((1 + R * Real.pi) ^ N)⁻¹ * ((1 + ‖k‖) ^ N)⁻¹ := by
        rw [← mul_inv, two_mul, pow_add]
        refine inv_anti₀ (by have : 0 ≤ R * Real.pi := le_trans (by positivity) hR; positivity) ?_
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by
          have : 0 ≤ R * Real.pi := le_trans (by positivity) hR; linarith) (by linarith) N)
          (by positivity)
      calc B ^ Fintype.card ι * FT1c_dec dot (2 * N) (FT1a.edgeMom e T₁ P k) *
            ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c
          ≤ B ^ Fintype.card ι * ((2 * Fintype.card ι + 2) ^ (2 * N) *
            (((1 + R * Real.pi) ^ N)⁻¹ * ((1 + ‖k‖) ^ N)⁻¹)) *
            ∏ c, FT1c_om (FT1a.edgeMom e T₁ P k c) ^ γ c := by
            gcongr
            exact le_trans h2 (by gcongr)
        _ = _ := by simp only [w]; ring
    · rw [integral_const_mul]
      have hR0 : 0 ≤ 1 + R * Real.pi := by
        have : 0 ≤ R * Real.pi := le_trans (by positivity) hR; linarith
      refine mul_le_mul_of_nonneg_left (le_trans (setIntegral_le_integral hwi
        (Eventually.of_forall hw0)) hwle) (by positivity)

end Graph

section Graph

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- The loop scale `η = π/(2|ι| + 2)`. -/
private def FT1c_eta (ι : Type*) [Fintype ι] : ℝ := Real.pi / (2 * Fintype.card ι + 2)

private theorem FT1c_eta_pos (ι : Type*) [Fintype ι] : 0 < FT1c_eta ι := by
  unfold FT1c_eta; positivity

/-- **The reduction modulo `2π` on `([−π, π]^d)^L`**: for `R ≥ 1`, `‖p‖ ≤ η/(2|V| + 2)` and
`q ∈ ([−π, π]^d)^L`, the products of `G_c(R ρ(ℓ_c))` and of `G_c(R ℓ_c)` differ by at most
`2 B^{|ι|} (1 + R η')^{-K} Π_c ω(R ρ(ℓ_c))^{γ_c}`, `η' = η/(2|ι| + 2)`: they agree when all loop
momenta are below `η`, and otherwise a momentum not on a dotted edge is at least `η'` modulo `2π`
(`FT1c_cutBound` on the torus). -/
private theorem FT1c_reduce {e : ι → V × V} {T₁ : List ι} (hT₁ : TreeEdges (T₁.map e))
    (dot : ι → Prop) [DecidablePred dot]
    (hcut : ∀ c, dot c → ∃ S : V → Prop, S (e c).2 ∧ ¬ S (e c).1 ∧
      ∀ c', dot c' → c' ≠ c → (S (e c').2 ↔ S (e c').1))
    (a : V → ℝ) (ha : ∑ v, a v = 0) (ha1 : ∀ v, |a v| ≤ 1) (γ : ι → ℕ) (K : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (G : ι → (Fin d → ℝ) → ℂ)
    (hG : ∀ c r, ‖G c r‖ ≤ B * FT1c_om r ^ γ c * (if dot c then 1 else ((1 + ‖r‖) ^ K)⁻¹))
    {R : ℝ} (hR : 1 ≤ R) {p : Fin d → ℝ}
    (hp : ‖p‖ ≤ FT1c_eta ι / (2 * Fintype.card V + 2))
    {q : {c // c ∉ T₁} → Fin d → ℝ} (hq : q ∈ Set.univ.pi fun _ => cubePi d) :
    ‖∏ c, G c (R • FT1c_red (FT1a.edgeMom e T₁ (fun v => a v • p) q c)) -
        ∏ c, G c (R • FT1a.edgeMom e T₁ (fun v => a v • p) q c)‖ ≤
      2 * (B ^ Fintype.card ι * ((1 + R * (FT1c_eta ι / (2 * Fintype.card ι + 2))) ^ K)⁻¹ *
        ∏ c, FT1c_om (R • FT1c_red (FT1a.edgeMom e T₁ (fun v => a v • p) q c)) ^ γ c) := by
  set η := FT1c_eta ι
  have hη := FT1c_eta_pos ι
  set P : V → Fin d → ℝ := fun v => a v • p
  set ℓ := FT1a.edgeMom e T₁ P q
  have hP : ∑ v, P v = 0 := FT1c_sum_ext a ha p
  have hSP : ∑ v, ‖P v‖ ≤ η / 2 := by
    refine le_trans (FT1c_norm_ext a ha1 p) ?_
    have hV : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    calc (Fintype.card V : ℝ) * ‖p‖ ≤ Fintype.card V * (η / (2 * Fintype.card V + 2)) :=
          mul_le_mul_of_nonneg_left hp hV
      _ ≤ η / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hR0 : 0 < R := by linarith
  have hprod0 : 0 ≤ ∏ c, FT1c_om (R • FT1c_red (ℓ c)) ^ γ c :=
    Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _
  by_cases hsmall : ‖q‖ < η
  · -- all momenta are in the open cube: the two products agree
    have hle : ∀ c, ‖ℓ c‖ < Real.pi := by
      intro c
      refine lt_of_le_of_lt (FT1c_edgeMom_norm_le e T₁ P q c) ?_
      have hι : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
      have h1 : (Fintype.card ι : ℝ) * ‖q‖ ≤ Fintype.card ι * η :=
        mul_le_mul_of_nonneg_left hsmall.le hι
      have h2 : (Fintype.card ι : ℝ) * η + η / 2 < Real.pi := by
        have hηeq : η * (2 * Fintype.card ι + 2) = Real.pi := by
          simp only [η, FT1c_eta]; field_simp
        have : 0 < η * (Fintype.card ι + 3 / 2) := by positivity
        linarith
      linarith
    have heq : ∀ c, FT1c_red (ℓ c) = ℓ c := fun c => FT1c_red_of_norm_lt (hle c)
    simp only [heq, sub_self, norm_zero]
    have h1 : 0 ≤ 1 + R * (η / (2 * Fintype.card ι + 2)) := by positivity
    exact mul_nonneg zero_le_two (mul_nonneg (mul_nonneg (pow_nonneg hB _)
      (inv_nonneg.2 (pow_nonneg h1 _))) (Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _))
  · push Not at hsmall
    -- a loop momentum of size `≥ η`
    obtain ⟨c₁, hc₁⟩ : ∃ c₁ : {c // c ∉ T₁}, η ≤ ‖q c₁‖ := by
      by_contra h
      push Not at h
      exact absurd hsmall (not_le.2 ((pi_norm_lt_iff hη).2 h))
    have hcb := FT1c_cutBound hT₁ dot hcut FT1c_tor P hP q c₁.1
    have hl1 : ℓ c₁.1 = q c₁ := FT1a.edgeMom_of_not_mem P q c₁.2
    have ht1 : ‖FT1c_tor (ℓ c₁.1)‖ = ‖q c₁‖ := by rw [hl1]; exact FT1c_norm_tor_cube (hq c₁ trivial)
    have htP : ∑ v, ‖FT1c_tor (P v)‖ ≤ η / 2 :=
      le_trans (Finset.sum_le_sum fun v _ => FT1c_norm_tor_le (P v)) hSP
    obtain ⟨c, hc, hcbig⟩ := FT1c_exists_big (Finset.univ.filter fun c' => ¬ dot c')
      (fun c' => ‖FT1c_tor (ℓ c')‖) (fun _ => norm_nonneg _) (by positivity : 0 < η / 2)
      (by linarith)
    have hc' : ¬ dot c := (Finset.mem_filter.1 hc).2
    set η' := η / (2 * Fintype.card ι + 2)
    have hη' : η' ≤ ‖FT1c_tor (ℓ c)‖ := by
      calc η' = η / 2 / (Fintype.card ι + 1) := by
            simp only [η']; rw [div_div]; ring_nf
        _ ≤ _ := hcbig
    have hdec1 : FT1c_dec dot K (fun c => R • FT1c_red (ℓ c)) ≤ ((1 + R * η') ^ K)⁻¹ := by
      refine le_trans (FT1c_dec_le dot K _ hc') (inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) ?_ K))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR0, FT1c_norm_red_eq]
      linarith [mul_le_mul_of_nonneg_left hη' hR0.le]
    have hdec2 : FT1c_dec dot K (fun c => R • ℓ c) ≤ ((1 + R * η') ^ K)⁻¹ := by
      refine le_trans (FT1c_dec_le dot K _ hc') (inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) ?_ K))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
      have := FT1c_norm_tor_le (ℓ c)
      nlinarith [mul_le_mul_of_nonneg_left hη' hR0.le]
    have hb1 := FT1c_prod_bound dot γ K hB G hG (fun c => R • FT1c_red (ℓ c))
    have hb2 := FT1c_prod_bound dot γ K hB G hG (fun c => R • ℓ c)
    have hom : ∏ c, FT1c_om (R • ℓ c) ^ γ c ≤ ∏ c, FT1c_om (R • FT1c_red (ℓ c)) ^ γ c :=
      Finset.prod_le_prod₀ (fun c _ => pow_nonneg (FT1c_om_pos _).le _) fun c _ =>
        pow_le_pow_left₀ (FT1c_om_pos _).le (FT1c_om_le_red hR _) _
    have hBn : 0 ≤ B ^ Fintype.card ι := pow_nonneg hB _
    refine le_trans (norm_sub_le _ _) ?_
    have e1 : ‖∏ c, G c (R • FT1c_red (ℓ c))‖ ≤ B ^ Fintype.card ι * ((1 + R * η') ^ K)⁻¹ *
        ∏ c, FT1c_om (R • FT1c_red (ℓ c)) ^ γ c :=
      le_trans hb1 (by gcongr)
    have e2 : ‖∏ c, G c (R • ℓ c)‖ ≤ B ^ Fintype.card ι * ((1 + R * η') ^ K)⁻¹ *
        ∏ c, FT1c_om (R • FT1c_red (ℓ c)) ^ γ c := by
      refine le_trans hb2 ?_
      have h0 : 0 ≤ FT1c_dec dot K (fun c => R • ℓ c) := FT1c_dec_nonneg _ _ _
      calc B ^ Fintype.card ι * FT1c_dec dot K (fun c => R • ℓ c) * ∏ c, FT1c_om (R • ℓ c) ^ γ c
          ≤ B ^ Fintype.card ι * ((1 + R * η') ^ K)⁻¹ * ∏ c, FT1c_om (R • ℓ c) ^ γ c :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdec2 hBn)
              (Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _)
        _ ≤ _ := by gcongr
    linarith

end Graph

/-- `(W^K)⁻¹ ≤ W^{-D}` for `W ≥ 1` and `D ≤ K`. -/
private theorem FT1c_inv_pow_le_rpow {W : ℝ} (hW : 1 ≤ W) {K : ℕ} {D : ℝ} (hD : D ≤ K) :
    (W ^ K)⁻¹ ≤ W ^ (-D) := by
  rw [Real.rpow_neg (by linarith), ← Real.rpow_natCast]
  exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hW hD)

section Graph

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- **The scaling of one momentum integral** ([I, (7.29)] → [I, (7.30)] with the scaling
`q = k/W`): for a graph with two spanning trees, dotted edges with cuts (`FT1c_cutSet`), external
momenta `a_v p`, and edge symbols `f_c` (`W`-dependent, `2π`-periodic, bounded by `B W^β ω(Wp)^{γ_c}`
on `[−π, π]^d`) that agree with `W^{-α_c} g_c(W p)` up to `C W^{-D} ω(Wp)^{γ_c}` for every `D`, the
`W`-free symbols `g_c` decaying faster than any power off the dotted edges, the momentum integral is
`W^{-(Σ_c α_c + dL)} Ψ(W p) + O(W^{-D})` for every `D`, uniformly in `‖p‖ ≤ η/(2|V| + 2)` and in the
parameter `x ∈ A`, with `Ψ = FT1c_Psi` the `W`-free integral over `ℝ^{dL}`. -/
private theorem FT1c_graph {e : ι → V × V} {T₁ T₂ : List ι} (hT₁ : TreeEdges (T₁.map e))
    (hT₂ : TreeEdges (T₂.map e)) (dot : ι → Prop) [DecidablePred dot]
    (hcut : ∀ c, dot c → ∃ S : V → Prop, S (e c).2 ∧ ¬ S (e c).1 ∧
      ∀ c', dot c' → c' ≠ c → (S (e c').2 ↔ S (e c').1))
    (a : V → ℝ) (ha : ∑ v, a v = 0) (ha1 : ∀ v, |a v| ≤ 1)
    (γ : ι → ℕ) (hγ : ∀ c, 2 * γ c < d) (hγ0 : ∀ c, c ∈ T₁ → c ∈ T₂ → γ c = 0)
    (α : ι → ℝ) (hα : ∀ c, 0 ≤ α c)
    {X : Type*} (A : Set X) (f : X → ℕ → ι → (Fin d → ℝ) → ℂ) (g : X → ι → (Fin d → ℝ) → ℂ)
    (hf : ∃ B β W₀ : ℝ, 0 ≤ β ∧ ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ A, ∀ c, Measurable (f x W c) ∧
      (∀ p (z : Fin d → ℤ), f x W c (p + fun i => 2 * Real.pi * z i) = f x W c p) ∧
      ∀ p ∈ cubePi d, ‖f x W c p‖ ≤ B * (W : ℝ) ^ β * FT1c_om ((W : ℝ) • p) ^ γ c)
    (hfc : ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ A, ∀ c, ∀ p ∈ cubePi d,
      ‖f x W c p - (((W : ℝ) ^ (-α c) : ℝ) : ℂ) * g x c ((W : ℝ) • p)‖ ≤
        C * (W : ℝ) ^ (-D) * FT1c_om ((W : ℝ) • p) ^ γ c)
    (hgm : ∀ x ∈ A, ∀ c, Measurable (g x c))
    (hgb : ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ A, ∀ c r,
      ‖g x c r‖ ≤ B * FT1c_om r ^ γ c * (if dot c then 1 else ((1 + ‖r‖) ^ K)⁻¹)) :
    ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ A, ∀ p : Fin d → ℝ,
      ‖p‖ ≤ FT1c_eta ι / (2 * Fintype.card V + 2) →
      ‖((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T₁}))⁻¹ *
          (∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
            ∏ c, f x W c (FT1a.edgeMom e T₁ (fun v => a v • p) q c)) -
        (((W : ℝ) ^ (-(∑ c, α c + ((d * Fintype.card {c // c ∉ T₁} : ℕ) : ℝ))) : ℝ) : ℂ) *
          FT1c_Psi e T₁ a (g x) ((W : ℝ) • p)‖ ≤ C * (W : ℝ) ^ (-D) := by
  intro D
  obtain ⟨B₁, β, W₁, hβ, hf'⟩ := hf
  set n := Fintype.card ι
  set L := Fintype.card {c // c ∉ T₁}
  set N : ℕ := d * L + 1 + ⌈D⌉₊
  have hN : d * L + 1 ≤ N := by omega
  have hDN : D ≤ (N : ℝ) := by
    have := Nat.le_ceil D
    have h2 : (⌈D⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈D⌉₊ ≤ N)
    linarith
  obtain ⟨B₂, hB₂, hg'⟩ := hgb (2 * N)
  set B := max (max B₁ B₂) 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hBB₁ : B₁ ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
  have hBB₂ : B₂ ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨C₃, W₃, hfc'⟩ := hfc (D + β * n)
  set K0 := FT1c_K0 d γ
  have hK0 : 0 < K0 := FT1c_K0_pos γ
  set η := FT1c_eta ι
  have hη := FT1c_eta_pos ι
  set η' := η / (2 * (n : ℝ) + 2)
  have hη' : 0 < η' := by positivity
  set c1 := n * |C₃| * K0 * B ^ n
  set c2 := 2 * (B₂ ^ n * K0) * (η' ^ (2 * N))⁻¹
  set c4 := B₂ ^ n * (2 * (n : ℝ) + 2) ^ (2 * N) * (2 ^ (N + 1) * K0)
  refine ⟨c1 + c2 + c4, max (max W₁ W₃) 1, fun W hW x hx p hp => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWf := hf' W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW) x hx
  have hWc := hfc' W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW) x hx
  set Pp : V → Fin d → ℝ := fun v => a v • p
  set ℓ := FT1a.edgeMom e T₁ Pp
  set QL := Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d)
  have hQL : MeasurableSet QL := MeasurableSet.univ_pi fun _ => FT1c_measurableSet_cube
  have hℓm : ∀ c, Measurable fun q : {c // c ∉ T₁} → Fin d → ℝ => ℓ q c :=
    fun c => (FT1a_continuous_edgeMom Pp c).measurable
  have hWβ : 1 ≤ (W : ℝ) ^ β := Real.one_le_rpow hW1 hβ
  have hWα : ∀ c, ‖((((W : ℝ) ^ (-α c) : ℝ)) : ℂ)‖ ≤ 1 := fun c => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hW0 _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith [hα c])
  ------------------------------------------------------------------ E1
  set m : ({c // c ∉ T₁} → Fin d → ℝ) → ι → ℝ := fun q c =>
    B * (W : ℝ) ^ β * FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c
  set a_ : ({c // c ∉ T₁} → Fin d → ℝ) → ι → ℂ := fun q c => f x W c (ℓ q c)
  set b_ : ({c // c ∉ T₁} → Fin d → ℝ) → ι → ℂ := fun q c =>
    (((W : ℝ) ^ (-α c) : ℝ) : ℂ) * g x c ((W : ℝ) • FT1c_red (ℓ q c))
  have hred : ∀ q c, a_ q c = f x W c (FT1c_red (ℓ q c)) := fun q c =>
    FT1c_periodic_red (hWf c).2.1 _
  have hom0 : ∀ q c, 0 ≤ FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c :=
    fun q c => pow_nonneg (FT1c_om_pos _).le _
  have hma : ∀ q c, ‖a_ q c‖ ≤ m q c := by
    intro q c
    rw [hred]
    refine le_trans ((hWf c).2.2 _ (FT1c_red_mem _)) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBB₁ (by linarith)) (hom0 q c)
  have hgbW : ∀ c r, ‖g x c r‖ ≤ B₂ * FT1c_om r ^ γ c := fun c r => by
    refine le_trans (hg' x hx c r) ?_
    have h1 : (if dot c then (1 : ℝ) else ((1 + ‖r‖) ^ (2 * N))⁻¹) ≤ 1 := by
      split_ifs
      · exact le_rfl
      · exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))
    have h0 : 0 ≤ B₂ * FT1c_om r ^ γ c := mul_nonneg hB₂ (pow_nonneg (FT1c_om_pos _).le _)
    calc B₂ * FT1c_om r ^ γ c * (if dot c then (1 : ℝ) else ((1 + ‖r‖) ^ (2 * N))⁻¹)
        ≤ B₂ * FT1c_om r ^ γ c * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := mul_one _
  have hmb : ∀ q c, ‖b_ q c‖ ≤ m q c := by
    intro q c
    simp only [b_, m, norm_mul]
    calc ‖((((W : ℝ) ^ (-α c) : ℝ)) : ℂ)‖ * ‖g x c ((W : ℝ) • FT1c_red (ℓ q c))‖
        ≤ 1 * (B₂ * FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c) :=
          mul_le_mul (hWα c) (hgbW c _) (norm_nonneg _) zero_le_one
      _ ≤ B * (W : ℝ) ^ β * FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c := by
          rw [one_mul]
          refine mul_le_mul_of_nonneg_right ?_ (hom0 q c)
          nlinarith
  set ε := |C₃| * (W : ℝ) ^ (-(D + β * n)) / (B * (W : ℝ) ^ β)
  have hε : 0 ≤ ε := by positivity
  have hmab : ∀ q c, ‖a_ q c - b_ q c‖ ≤ ε * m q c := by
    intro q c
    rw [hred]
    have hBW : 0 < B * (W : ℝ) ^ β := by positivity
    calc ‖f x W c (FT1c_red (ℓ q c)) - (((W : ℝ) ^ (-α c) : ℝ) : ℂ) *
          g x c ((W : ℝ) • FT1c_red (ℓ q c))‖
        ≤ C₃ * (W : ℝ) ^ (-(D + β * n)) * FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c :=
          hWc c _ (FT1c_red_mem _)
      _ ≤ |C₃| * (W : ℝ) ^ (-(D + β * n)) * FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
            (Real.rpow_nonneg hW0.le _)) (hom0 q c)
      _ = ε * m q c := by simp only [ε, m]; field_simp
  obtain ⟨hmint, hmle⟩ := FT1c_cs hT₁ hT₂ γ hγ hγ0 hW1 (fun _ => B * (W : ℝ) ^ β)
    (fun _ => by positivity) Pp
  have hmint' : IntegrableOn (fun q => ∏ c, m q c) QL := hmint
  have haint : IntegrableOn (fun q => ∏ c, a_ q c) QL := by
    refine FT1c_integrableOn_of_le hQL ?_ hmint' fun q _ => ?_
    · exact (Finset.measurable_prod _ fun c _ =>
        (hWf c).1.comp (hℓm c)).aestronglyMeasurable
    · rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) fun c _ => hma q c
  have hbint : IntegrableOn (fun q => ∏ c, b_ q c) QL := by
    refine FT1c_integrableOn_of_le hQL ?_ hmint' fun q _ => ?_
    · exact (Finset.measurable_prod _ fun c _ => measurable_const.mul
        ((hgm x hx c).comp ((measurable_const_smul _).comp
          (FT1c_measurable_red.comp (hℓm c))))).aestronglyMeasurable
    · rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) fun c _ => hmb q c
  have hE1 : ‖(∫ q in QL, ∏ c, a_ q c) - ∫ q in QL, ∏ c, b_ q c‖ ≤ c1 * (W : ℝ) ^ (-D) := by
    rw [← integral_sub haint hbint]
    have hle : ∀ q ∈ QL, ‖∏ c, a_ q c - ∏ c, b_ q c‖ ≤ n * ε * ∏ c, m q c := fun q _ =>
      FT1c_telescope (a_ q) (b_ q) (m q) hε (hma q) (hmb q) (hmab q)
    refine le_trans (norm_integral_le_of_norm_le (hmint'.const_mul (n * ε))
      ((ae_restrict_iff' hQL).2 (Eventually.of_forall hle))) ?_
    rw [integral_const_mul]
    have hint_le : ∫ q in QL, ∏ c, m q c ≤ K0 * (B * (W : ℝ) ^ β) ^ n := by
      refine le_trans (le_of_eq ?_) (le_trans hmle (le_of_eq ?_))
      · rfl
      · rw [Finset.prod_const, Finset.card_univ]
    have hBW : 1 ≤ B * (W : ℝ) ^ β := by nlinarith
    calc (n : ℝ) * ε * ∫ q in QL, ∏ c, m q c ≤ n * ε * (K0 * (B * (W : ℝ) ^ β) ^ n) :=
          mul_le_mul_of_nonneg_left hint_le (by positivity)
      _ = n * |C₃| * K0 * (W : ℝ) ^ (-(D + β * n)) * ((B * (W : ℝ) ^ β) ^ n / (B * (W : ℝ) ^ β)) := by
          simp only [ε]; ring
      _ ≤ n * |C₃| * K0 * (W : ℝ) ^ (-(D + β * n)) * (B * (W : ℝ) ^ β) ^ n := by
          gcongr
          exact div_le_self (by positivity) hBW
      _ = c1 * (W : ℝ) ^ (-D) := by
          simp only [c1]
          rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ β), ← Real.rpow_mul hW0.le]
          have : (W : ℝ) ^ (-(D + β * n)) * (W : ℝ) ^ (β * (n : ℝ)) = (W : ℝ) ^ (-D) := by
            rw [← Real.rpow_add hW0]; congr 1; ring
          calc (n : ℝ) * |C₃| * K0 * (W : ℝ) ^ (-(D + β * n)) * (B ^ n * (W : ℝ) ^ (β * (n : ℝ)))
              = n * |C₃| * K0 * B ^ n * ((W : ℝ) ^ (-(D + β * n)) * (W : ℝ) ^ (β * (n : ℝ))) := by
                ring
            _ = _ := by rw [this]
  ------------------------------------------------------------------ factor `W^{-Σα}`
  set u : ℂ := (((W : ℝ) ^ (-∑ c, α c) : ℝ) : ℂ)
  set Ig := ∫ q in QL, ∏ c, g x c ((W : ℝ) • FT1c_red (ℓ q c))
  have hb : (∫ q in QL, ∏ c, b_ q c) = u * Ig := by
    have hpt : ∀ q, ∏ c, b_ q c = u * ∏ c, g x c ((W : ℝ) • FT1c_red (ℓ q c)) := by
      intro q
      simp only [b_, Finset.prod_mul_distrib, u]
      congr 1
      rw [← Complex.ofReal_prod, ← Real.rpow_sum_of_pos hW0, Finset.sum_neg_distrib]
    simp_rw [hpt]
    rw [integral_const_mul]
  ------------------------------------------------------------------ E2
  set Ig' := ∫ q in QL, ∏ c, g x c ((W : ℝ) • ℓ q c)
  obtain ⟨hoint, hole⟩ := FT1c_cs hT₁ hT₂ γ hγ hγ0 hW1 (fun _ => 1) (fun _ => zero_le_one) Pp
  have hoint' : IntegrableOn (fun q => B₂ ^ n * ∏ c, FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c)
      QL := by
    refine Integrable.const_mul ?_ _
    refine hoint.congr_fun (fun q _ => ?_) hQL
    simp only [one_mul]
    rfl
  have hgint1 : IntegrableOn (fun q => ∏ c, g x c ((W : ℝ) • FT1c_red (ℓ q c))) QL := by
    refine FT1c_integrableOn_of_le hQL ?_ hoint' fun q _ => ?_
    · exact (Finset.measurable_prod _ fun c _ => (hgm x hx c).comp ((measurable_const_smul _).comp
        (FT1c_measurable_red.comp (hℓm c)))).aestronglyMeasurable
    · rw [norm_prod]
      calc ∏ c, ‖g x c ((W : ℝ) • FT1c_red (ℓ q c))‖
          ≤ ∏ c, B₂ * FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c :=
            Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) fun c _ => hgbW c _
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hgint2 : IntegrableOn (fun q => ∏ c, g x c ((W : ℝ) • ℓ q c)) QL := by
    refine FT1c_integrableOn_of_le hQL ?_ hoint' fun q _ => ?_
    · exact (Finset.measurable_prod _ fun c _ => (hgm x hx c).comp ((measurable_const_smul _).comp
        (hℓm c))).aestronglyMeasurable
    · rw [norm_prod]
      calc ∏ c, ‖g x c ((W : ℝ) • ℓ q c)‖
          ≤ ∏ c, B₂ * FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c :=
            Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) fun c _ =>
              le_trans (hgbW c _) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (FT1c_om_pos _).le
                (FT1c_om_le_red hW1 _) _) hB₂)
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hE2 : ‖Ig - Ig'‖ ≤ c2 * (W : ℝ) ^ (-D) := by
    rw [← integral_sub hgint1 hgint2]
    have hle : ∀ q ∈ QL, ‖∏ c, g x c ((W : ℝ) • FT1c_red (ℓ q c)) - ∏ c, g x c ((W : ℝ) • ℓ q c)‖ ≤
        2 * (B₂ ^ n * ((1 + (W : ℝ) * η') ^ (2 * N))⁻¹ *
          ∏ c, FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c) := fun q hq =>
      FT1c_reduce hT₁ dot hcut a ha ha1 γ (2 * N) hB₂ (g x) (hg' x hx) hW1 hp hq
    have hint3 : IntegrableOn (fun q => 2 * (B₂ ^ n * ((1 + (W : ℝ) * η') ^ (2 * N))⁻¹ *
        ∏ c, FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c)) QL := by
      refine Integrable.const_mul (Integrable.const_mul ?_ _) _
      exact hoint.congr_fun (fun q _ => by simp only [one_mul]; rfl) hQL
    refine le_trans (norm_integral_le_of_norm_le hint3
      ((ae_restrict_iff' hQL).2 (Eventually.of_forall hle))) ?_
    rw [integral_const_mul, integral_const_mul]
    have hI : ∫ q in QL, ∏ c, FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c ≤ K0 := by
      have h := hole
      simp only [one_mul, Finset.prod_const_one, mul_one] at h
      exact h
    have hpw : ((1 + (W : ℝ) * η') ^ (2 * N))⁻¹ ≤ (η' ^ (2 * N))⁻¹ * (W : ℝ) ^ (-D) := by
      have h1 : (η' ^ (2 * N)) * (W : ℝ) ^ (2 * N) ≤ (1 + (W : ℝ) * η') ^ (2 * N) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
      have h2 := FT1c_inv_pow_le_rpow hW1 (K := 2 * N) (D := D) (by push_cast; linarith)
      calc ((1 + (W : ℝ) * η') ^ (2 * N))⁻¹ ≤ (η' ^ (2 * N) * (W : ℝ) ^ (2 * N))⁻¹ :=
            inv_anti₀ (by positivity) h1
        _ = (η' ^ (2 * N))⁻¹ * ((W : ℝ) ^ (2 * N))⁻¹ := mul_inv _ _
        _ ≤ (η' ^ (2 * N))⁻¹ * (W : ℝ) ^ (-D) := by gcongr
    have hI0 : 0 ≤ ∫ q in QL, ∏ c, FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c :=
      setIntegral_nonneg hQL fun q _ => Finset.prod_nonneg fun c _ => pow_nonneg (FT1c_om_pos _).le _
    calc 2 * (B₂ ^ n * ((1 + (W : ℝ) * η') ^ (2 * N))⁻¹ *
          ∫ q in QL, ∏ c, FT1c_om ((W : ℝ) • FT1c_red (ℓ q c)) ^ γ c)
        ≤ 2 * (B₂ ^ n * ((η' ^ (2 * N))⁻¹ * (W : ℝ) ^ (-D)) * K0) := by gcongr
      _ = c2 * (W : ℝ) ^ (-D) := by simp only [c2]; ring
  ------------------------------------------------------------------ E3, E4
  set F : ({c // c ∉ T₁} → Fin d → ℝ) → ℂ := fun k =>
    ∏ c, g x c (FT1a.edgeMom e T₁ (fun v => a v • ((W : ℝ) • p)) k c)
  have hPW : (fun v => a v • ((W : ℝ) • p)) = (W : ℝ) • Pp := by
    funext v; simp only [Pp, Pi.smul_apply, smul_comm (a v)]
  have hFW : ∀ q, F ((W : ℝ) • q) = ∏ c, g x c ((W : ℝ) • ℓ q c) := by
    intro q
    simp only [F, hPW, FT1c_edgeMom_smul]
    rfl
  have hscale := FT1c_integral_scale (d := d) {c // c ∉ T₁} hW0 F
  simp_rw [hFW] at hscale
  set v : ℂ := (((W : ℝ) ^ (d * L) : ℝ) : ℂ)⁻¹
  set IB := ∫ k in Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) ((W : ℝ) * Real.pi), F k
  have hIg' : Ig' = v * IB := hscale
  have hgW : ∀ c r, ‖g x c r‖ ≤ B₂ * FT1c_om r ^ γ c *
      (if dot c then 1 else ((1 + ‖r‖) ^ (2 * N))⁻¹) := hg' x hx
  obtain ⟨hFint, htail⟩ := FT1c_wfree hT₁ hT₂ dot hcut γ hγ hγ0 N hN hB₂ (g x) (hgm x hx) hgW
    (fun v => a v • ((W : ℝ) • p)) (FT1c_sum_ext a ha _)
  set Tl := ∫ k in (Metric.closedBall (0 : {c // c ∉ T₁} → Fin d → ℝ) ((W : ℝ) * Real.pi))ᶜ, F k
  have hIB : IB = (∫ k, F k) - Tl := by
    rw [← integral_add_compl measurableSet_closedBall hFint]; ring
  have hE4 : ‖Tl‖ ≤ c4 * (W : ℝ) ^ (-D) := by
    have hR : 2 * ∑ v, ‖a v • ((W : ℝ) • p)‖ ≤ (W : ℝ) * Real.pi := by
      have h1 := FT1c_norm_ext a ha1 ((W : ℝ) • p)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hW0] at h1
      have hV : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      have h2 : (Fintype.card V : ℝ) * ‖p‖ ≤ η / 2 := by
        calc (Fintype.card V : ℝ) * ‖p‖ ≤ Fintype.card V * (η / (2 * Fintype.card V + 2)) :=
              mul_le_mul_of_nonneg_left hp hV
          _ ≤ η / 2 := by
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith
      have h3 : η ≤ Real.pi := by
        simp only [η, FT1c_eta]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]
      nlinarith
    refine le_trans (htail (W : ℝ) hR) ?_
    have hpw : ((1 + (W : ℝ) * Real.pi) ^ N)⁻¹ ≤ (W : ℝ) ^ (-D) := by
      refine le_trans (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity)
        (by nlinarith [Real.two_le_pi] : (W : ℝ) ≤ 1 + (W : ℝ) * Real.pi) N)) ?_
      exact FT1c_inv_pow_le_rpow hW1 hDN
    calc B₂ ^ n * (2 * (n : ℝ) + 2) ^ (2 * N) * ((1 + (W : ℝ) * Real.pi) ^ N)⁻¹ *
          (2 ^ (N + 1) * K0)
        ≤ B₂ ^ n * (2 * (n : ℝ) + 2) ^ (2 * N) * (W : ℝ) ^ (-D) * (2 ^ (N + 1) * K0) := by
          gcongr
      _ = c4 * (W : ℝ) ^ (-D) := by simp only [c4]; ring
  ------------------------------------------------------------------ assembly
  have hexp : (((W : ℝ) ^ (-(∑ c, α c + ((d * L : ℕ) : ℝ))) : ℝ) : ℂ) = u * v := by
    simp only [u, v]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, neg_add, Real.rpow_add hW0,
      Real.rpow_neg hW0.le ((d * L : ℕ) : ℝ), Real.rpow_natCast]
  have hPsi : FT1c_Psi e T₁ a (g x) ((W : ℝ) • p) =
      ((2 * Real.pi : ℂ) ^ (d * L))⁻¹ * ∫ k, F k := rfl
  set c0 : ℂ := ((2 * Real.pi : ℂ) ^ (d * L))⁻¹
  have hc0 : ‖c0‖ ≤ 1 := by
    simp only [c0, norm_inv, norm_pow]
    refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.two_pi_pos]
    linarith [Real.two_le_pi]
  have hu : ‖u‖ ≤ 1 := by
    simp only [u]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hW0 _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1
      (neg_nonpos.2 (Finset.sum_nonneg fun c _ => hα c))
  have hv : ‖v‖ ≤ 1 := by
    simp only [v, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have hkey : c0 * (∫ q in QL, ∏ c, a_ q c) -
      (((W : ℝ) ^ (-(∑ c, α c + ((d * L : ℕ) : ℝ))) : ℝ) : ℂ) * (c0 * ∫ k, F k) =
      c0 * (((∫ q in QL, ∏ c, a_ q c) - ∫ q in QL, ∏ c, b_ q c) + u * (Ig - Ig') - u * v * Tl) := by
    rw [hexp, hb, hIg', hIB]; ring
  have hgoal : ((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T₁}))⁻¹ *
        (∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
          ∏ c, f x W c (FT1a.edgeMom e T₁ (fun v => a v • p) q c)) -
      (((W : ℝ) ^ (-(∑ c, α c + ((d * Fintype.card {c // c ∉ T₁} : ℕ) : ℝ))) : ℝ) : ℂ) *
        FT1c_Psi e T₁ a (g x) ((W : ℝ) • p) =
      c0 * (((∫ q in QL, ∏ c, a_ q c) - ∫ q in QL, ∏ c, b_ q c) + u * (Ig - Ig') - u * v * Tl) := by
    rw [hPsi]; exact hkey
  rw [hgoal, norm_mul]
  have hW_D : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  calc ‖c0‖ * ‖((∫ q in QL, ∏ c, a_ q c) - ∫ q in QL, ∏ c, b_ q c) + u * (Ig - Ig') - u * v * Tl‖
      ≤ 1 * (c1 * (W : ℝ) ^ (-D) + 1 * (c2 * (W : ℝ) ^ (-D)) + 1 * 1 * (c4 * (W : ℝ) ^ (-D))) := by
        refine mul_le_mul hc0 ?_ (norm_nonneg _) zero_le_one
        refine le_trans (norm_sub_le _ _) (add_le_add (le_trans (norm_add_le _ _)
          (add_le_add hE1 ?_)) ?_)
        · rw [norm_mul]; exact mul_le_mul hu hE2 (norm_nonneg _) zero_le_one
        · rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul hu hv (norm_nonneg _) zero_le_one) hE4 (norm_nonneg _)
            (by positivity)
    _ = (c1 + c2 + c4) * (W : ℝ) ^ (-D) := by ring

end Graph

/-! ## The `W`-free symbols -/

/-- `ψ(k)` for `k ∈ ℝ^d` as a complex number. -/
private def FT1c_psi (P : Profile d) (k : Fin d → ℝ) : ℂ := (P.ψ (WithLp.toLp 2 k) : ℂ)

private theorem FT1c_measurable_psi (P : Profile d) : Measurable (FT1c_psi P) :=
  Complex.measurable_ofReal.comp (P.ψ.continuous.measurable.comp
    (PiLp.continuous_toLp 2 _).measurable)

private theorem FT1c_norm_le_toLp (k : Fin d → ℝ) : ‖k‖ ≤ ‖(WithLp.toLp 2 k : EuclideanSpace ℝ (Fin d))‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    PiLp.norm_apply_le (WithLp.toLp 2 k : EuclideanSpace ℝ (Fin d)) i

private theorem FT1c_norm_psi_le_one (P : Profile d) (k : Fin d → ℝ) : ‖FT1c_psi P k‖ ≤ 1 := by
  rw [FT1c_psi, Complex.norm_real, Real.norm_eq_abs]; exact P.abs_le_one _

/-- **Schwartz decay of `ψ`**: `|ψ(k)| ≤ C_K (1 + ‖k‖)^{-K}`. -/
private theorem FT1c_psi_decay (P : Profile d) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ‖FT1c_psi P k‖ ≤ C * ((1 + ‖k‖) ^ K)⁻¹ := by
  set S := 2 ^ K * ((Finset.Iic (K, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) P.ψ
  have hS : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨S, hS, fun k => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (K, 0)) le_rfl le_rfl P.ψ
    (WithLp.toLp 2 k)
  rw [norm_iteratedFDeriv_zero] at h
  have hk := FT1c_norm_le_toLp k
  rw [FT1c_psi, Complex.norm_real, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖P.ψ (WithLp.toLp 2 k)‖ * (1 + ‖k‖) ^ K
      ≤ ‖P.ψ (WithLp.toLp 2 k)‖ * (1 + ‖(WithLp.toLp 2 k : EuclideanSpace ℝ (Fin d))‖) ^ K := by
        gcongr
    _ = (1 + ‖(WithLp.toLp 2 k : EuclideanSpace ℝ (Fin d))‖) ^ K * ‖P.ψ (WithLp.toLp 2 k)‖ :=
        mul_comm _ _
    _ ≤ S := h

/-- `1 − ψ(k) ≥ c_ψ min(‖k‖², 1)`. -/
private theorem FT1c_one_sub_psi (P : Profile d) (k : Fin d → ℝ) :
    P.cψ * min (‖k‖ ^ 2) 1 ≤ 1 - P.ψ (WithLp.toLp 2 k) := by
  have h := P.le_max (WithLp.toLp 2 k)
  have hk := FT1c_norm_le_toLp k
  have hc := P.cψ_pos
  rcases le_total (1 - P.cψ * ‖(WithLp.toLp 2 k : EuclideanSpace ℝ (Fin d))‖ ^ 2) (1 - P.cψ) with
    h1 | h1
  · rw [max_eq_right h1] at h
    have : P.cψ * min (‖k‖ ^ 2) 1 ≤ P.cψ := by
      have := min_le_right (‖k‖ ^ 2) 1; nlinarith
    linarith
  · rw [max_eq_left h1] at h
    have h2 : ‖k‖ ^ 2 ≤ ‖(WithLp.toLp 2 k : EuclideanSpace ℝ (Fin d))‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hk 2
    have : P.cψ * min (‖k‖ ^ 2) 1 ≤ P.cψ * ‖(WithLp.toLp 2 k : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
      have := min_le_left (‖k‖ ^ 2) 1; nlinarith
    linarith

/-- `ψ_Θ(k) = ψ(k)/(1 − ψ(k))`, the `W`-free symbol of `Θ`. -/
private def FT1c_gth (P : Profile d) (k : Fin d → ℝ) : ℂ := FT1c_psi P k / (1 - FT1c_psi P k)

private theorem FT1c_measurable_gth (P : Profile d) : Measurable (FT1c_gth P) :=
  (FT1c_measurable_psi P).div (measurable_const.sub (FT1c_measurable_psi P))

/-- `|ψ_Θ(k)| ≤ c_ψ⁻¹ |ψ(k)| ω(k)²`. -/
private theorem FT1c_gth_le (P : Profile d) (k : Fin d → ℝ) :
    ‖FT1c_gth P k‖ ≤ P.cψ⁻¹ * ‖FT1c_psi P k‖ * FT1c_om k ^ 2 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [FT1c_gth, FT1c_psi, WithLp.toLp_zero, P.at_zero, Complex.ofReal_one, sub_self,
      div_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (inv_pos.2 P.cψ_pos).le (norm_nonneg _))
      (pow_nonneg (FT1c_om_pos _).le _)
  have h0 : 0 < ‖k‖ := norm_pos_iff.2 hk
  have h1 := FT1c_one_sub_psi P k
  have hc := P.cψ_pos
  have hmin : 0 < min (‖k‖ ^ 2) 1 := lt_min (by positivity) one_pos
  have hden : ‖1 - FT1c_psi P k‖ = 1 - P.ψ (WithLp.toLp 2 k) := by
    rw [FT1c_psi, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
  have hom : FT1c_om k ^ 2 = (min (‖k‖ ^ 2) 1)⁻¹ := by
    rw [← inv_inv (FT1c_om k), FT1c_om_inv k hk, inv_pow]
    congr 1
    rcases le_total ‖k‖ 1 with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]
    · rw [min_eq_right h, min_eq_right (by nlinarith), one_pow]
  rw [FT1c_gth, norm_div, hden, hom, div_eq_mul_inv]
  rw [mul_comm P.cψ⁻¹, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← mul_inv]
  exact inv_anti₀ (by positivity) (by linarith)

/-- `|ψ_Θ(k)| ≤ c_ψ⁻¹ ω(k)²`. -/
private theorem FT1c_gth_le' (P : Profile d) (k : Fin d → ℝ) :
    ‖FT1c_gth P k‖ ≤ P.cψ⁻¹ * FT1c_om k ^ 2 := by
  refine le_trans (FT1c_gth_le P k) ?_
  have := FT1c_norm_psi_le_one P k
  have hc := (inv_pos.2 P.cψ_pos).le
  have h2 : 0 ≤ FT1c_om k ^ 2 := by positivity
  calc P.cψ⁻¹ * ‖FT1c_psi P k‖ * FT1c_om k ^ 2 ≤ P.cψ⁻¹ * 1 * FT1c_om k ^ 2 := by gcongr
    _ = _ := by ring

/-- `D_W(p) ≤ ω(W p)²`. -/
private theorem FT1c_dW_le (W : ℕ) (p : Fin d → ℝ) : FT1b.dW W p ≤ FT1c_om ((W : ℝ) • p) ^ 2 := by
  unfold FT1b.dW FT1c_om
  refine max_le (one_le_pow₀ (le_max_left _ _)) ?_
  by_cases hp : (W : ℝ) • p = 0
  · rcases smul_eq_zero.1 hp with h | h
    · rw [h]; simp
    · rw [h]; simp [sqNorm]
  · have hpos : 0 < ‖(W : ℝ) • p‖ := norm_pos_iff.2 hp
    have h1 : ‖(W : ℝ) • p‖ ^ 2 ≤ (W : ℝ) ^ 2 * sqNorm p := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_left (FT1b_sq_norm_le p) (sq_nonneg _)
    calc ((W : ℝ) ^ 2 * sqNorm p)⁻¹ ≤ (‖(W : ℝ) • p‖ ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
      _ = (‖(W : ℝ) • p‖⁻¹) ^ 2 := by rw [inv_pow]
      _ ≤ (max 1 ‖(W : ℝ) • p‖⁻¹) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (le_max_right _ _) 2

/-! ## Algebra: telescoping along a list, interpolation -/

/-- Products along a list of factors bounded by `M ≥ 1`, differing by at most `ε`. -/
private theorem FT1c_list_tel (o : List ℕ) (X Y : ℕ → ℂ) {M ε : ℝ} (hM : 1 ≤ M)
    (hX : ∀ l ∈ o, ‖X l‖ ≤ M) (hY : ∀ l ∈ o, ‖Y l‖ ≤ M) (hXY : ∀ l ∈ o, ‖X l - Y l‖ ≤ ε) :
    ‖(o.map X).prod‖ ≤ M ^ o.length ∧ ‖(o.map Y).prod‖ ≤ M ^ o.length ∧
      ‖(o.map X).prod - (o.map Y).prod‖ ≤ o.length * ε * M ^ o.length := by
  induction o with
  | nil => simp
  | cons l o ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun l' hl' => hX l' (List.mem_cons_of_mem _ hl'))
      (fun l' hl' => hY l' (List.mem_cons_of_mem _ hl'))
      (fun l' hl' => hXY l' (List.mem_cons_of_mem _ hl'))
    have hXl := hX l List.mem_cons_self
    have hYl := hY l List.mem_cons_self
    have hXYl := hXY l List.mem_cons_self
    have hε : 0 ≤ ε := le_trans (norm_nonneg _) hXYl
    have hM0 : 0 ≤ M := by linarith
    simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul, pow_succ]
    refine ⟨?_, ?_, ?_⟩
    · calc ‖X l‖ * ‖(o.map X).prod‖ ≤ M * M ^ o.length :=
            mul_le_mul hXl h1 (norm_nonneg _) hM0
        _ = M ^ o.length * M := by ring
    · calc ‖Y l‖ * ‖(o.map Y).prod‖ ≤ M * M ^ o.length :=
            mul_le_mul hYl h2 (norm_nonneg _) hM0
        _ = M ^ o.length * M := by ring
    · have he : X l * (o.map X).prod - Y l * (o.map Y).prod =
          X l * ((o.map X).prod - (o.map Y).prod) + (X l - Y l) * (o.map Y).prod := by ring
      rw [he]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
      have hMo : M ^ o.length ≤ M ^ o.length * M := le_mul_of_one_le_right (pow_nonneg hM0 _) hM
      calc ‖X l‖ * ‖(o.map X).prod - (o.map Y).prod‖ + ‖X l - Y l‖ * ‖(o.map Y).prod‖
          ≤ M * (o.length * ε * M ^ o.length) + ε * M ^ o.length :=
            add_le_add (mul_le_mul hXl h3 (norm_nonneg _) hM0)
              (mul_le_mul hXYl h2 (norm_nonneg _) hε)
        _ ≤ M * (o.length * ε * M ^ o.length) + ε * (M ^ o.length * M) := by gcongr
        _ = ((o.length + 1 : ℕ) : ℝ) * ε * (M ^ o.length * M) := by push_cast; ring

/-- `|x^n − y^n| ≤ n ε M^n` for `|x|, |y| ≤ M`, `M ≥ 1`, `|x − y| ≤ ε`. -/
private theorem FT1c_pow_tel (n : ℕ) {x y : ℂ} {M ε : ℝ} (hM : 1 ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M)
    (hxy : ‖x - y‖ ≤ ε) : ‖x ^ n - y ^ n‖ ≤ n * ε * M ^ n := by
  have h := (FT1c_list_tel (List.replicate n 0) (fun _ => x) (fun _ => y) hM
    (fun _ _ => hx) (fun _ _ => hy) (fun _ _ => hxy)).2.2
  simpa [List.map_replicate, List.prod_replicate] using h

/-- **Interpolation**: `min(x, y) ≤ x^θ y^{1−θ}` for `x, y ≥ 0`, `θ ∈ [0, 1]`. -/
private theorem FT1c_interp {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    min x y ≤ x ^ θ * y ^ (1 - θ) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    calc x = x ^ θ * x ^ (1 - θ) := by
          rw [← Real.rpow_add' hx (by linarith : θ + (1 - θ) ≠ 0)]; simp
      _ ≤ x ^ θ * y ^ (1 - θ) := by
          gcongr
  · rw [min_eq_right h]
    calc y = y ^ θ * y ^ (1 - θ) := by
          rw [← Real.rpow_add' hy (by linarith : θ + (1 - θ) ≠ 0)]; simp
      _ ≤ x ^ θ * y ^ (1 - θ) := by
          gcongr

/-! ## Label kernels: the `W`-free form and its bound -/

/-- `Φ̊` is a `W`-free form of the symbol of `Σ̊^∞_l` near `p = 0`: `Φ̊(E, ·)` is measurable and
`ψ_{Σ̊^∞_l}(p) = W^{-(l-2)d/2} Φ̊(E, W p) + O(W^{-D})` for every `D`, uniformly in `|E| < 2 − κ` and
`‖p‖ ≤ δ`. -/
private def FT1c_LabGood (P : Profile d) (Sig : ℕ → Expansion 2) (κ : ℝ) (l : ℕ)
    (Φ : ℝ → (Fin d → ℝ) → ℂ) : Prop :=
  (∀ E : ℝ, |E| < 2 - κ → Measurable (Φ E)) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      ∀ p : Fin d → ℝ, ‖p‖ ≤ δ →
        ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p -
            (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * Φ E ((W : ℝ) • p)‖ ≤
          C * (W : ℝ) ^ (-D)

private theorem FT1c_sqNorm_le (k : Fin d → ℝ) : sqNorm k ≤ d * ‖k‖ ^ 2 := by
  unfold sqNorm
  calc ∑ i, k i ^ 2 ≤ ∑ _i : Fin d, ‖k‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [← sq_abs, ← Real.norm_eq_abs]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm k i) 2
    _ = d * ‖k‖ ^ 2 := by simp

/-- **The bound of a `W`-free label form** (from the symbol bound of `Σ̊^∞_l`): for `τ ∈ (0, 1]`,
`|Φ̊(E, k)| ≤ C min(‖k‖, 1)^{2−τ} (1 + ‖k‖)^τ` for `k ≠ 0`. -/
private theorem FT1c_labBound (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (l : ℕ) (hl4 : 4 ≤ l)
    (hlN : l ≤ N) (hle : Even l) {Φ : ℝ → (Fin d → ℝ) → ℂ} (hG : FT1c_LabGood P Sig κ l Φ)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| < 2 - κ → ∀ k : Fin d → ℝ, k ≠ 0 →
      ‖Φ E k‖ ≤ C * min ‖k‖ 1 ^ (2 - τ) * (1 + ‖k‖) ^ τ := by
  obtain ⟨A, W₂, hA, hlab⟩ := FT1b_labelSym hd P Sig N hSig hκ l hl4 hlN hle hτ
  obtain ⟨-, δ, hδ, hcmp⟩ := hG
  set a : ℝ := ((l : ℝ) - 2) * d / 2
  have ha : 0 ≤ a := by
    have : (4 : ℝ) ≤ l := by exact_mod_cast hl4
    have : (0 : ℝ) ≤ ((l : ℝ) - 2) * d := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    simp only [a]; linarith
  obtain ⟨C₁, W₁, h1⟩ := hcmp (a + 2)
  set δ' := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  set M := max (max (max W₁ W₂) 1) (1 / δ')
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hC0 : 0 ≤ A * d * (2 * M) ^ τ := mul_nonneg (mul_nonneg hA (Nat.cast_nonneg _))
    (Real.rpow_nonneg (by linarith) _)
  refine ⟨A * d * (2 * M) ^ τ + |C₁|, add_nonneg hC0 (abs_nonneg _), fun E hE k hk => ?_⟩
  set t := ‖k‖
  have ht : 0 < t := norm_pos_iff.2 hk
  set u := max t (1 / t)
  have hu1 : 1 ≤ u := by
    rcases le_total t 1 with h | h
    · exact le_trans (by rw [le_div_iff₀ ht]; linarith) (le_max_right _ _)
    · exact le_trans h (le_max_left _ _)
  set W : ℕ := ⌈M * u⌉₊
  have hWge : M * u ≤ W := Nat.le_ceil _
  have hWle : (W : ℝ) ≤ 2 * M * u := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ M * u)
    nlinarith
  have hW1 : (1 : ℝ) ≤ W := le_trans (by nlinarith) hWge
  have hW0 : (0 : ℝ) < W := by linarith
  have hWM : M ≤ W := le_trans (le_mul_of_one_le_right (by linarith) hu1) hWge
  have hWt : t / δ' ≤ W := by
    calc t / δ' = (1 / δ') * t := by ring
      _ ≤ M * u := mul_le_mul (le_max_right _ _) (le_max_left _ _) ht.le (by linarith)
      _ ≤ W := hWge
  have hWit : 1 / t ≤ W := le_trans (le_trans (le_max_right t (1 / t))
    (le_mul_of_one_le_left (by linarith) hM1)) hWge
  set p : Fin d → ℝ := (W : ℝ)⁻¹ • k
  have hWp : (W : ℝ) • p = k := by simp only [p, smul_smul, mul_inv_cancel₀ hW0.ne', one_smul]
  have hp : ‖p‖ = t / W := by
    simp only [p, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hW0, t]; ring
  have hpδ : ‖p‖ ≤ δ' := by
    rw [hp, div_le_iff₀ hW0]; rw [div_le_iff₀ hδ'] at hWt; linarith
  have hpcube : p ∈ cubePi d := by
    intro i _
    have h := le_trans (norm_le_pi_norm p i) (le_trans hpδ (min_le_right _ _))
    rw [Real.norm_eq_abs, abs_le] at h
    constructor <;> linarith [Real.two_le_pi]
  have hcmpW := h1 W (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hWM) E hE p (le_trans hpδ (min_le_left _ _))
  rw [hWp] at hcmpW
  have hlabW := (hlab W (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hWM) E hE).2 p hpcube
  have hsq : (W : ℝ) ^ 2 * sqNorm p = sqNorm k := by
    rw [← hWp]; unfold sqNorm; simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hsq] at hlabW
  have hmin : min (sqNorm k) 1 ≤ d * min t 1 ^ 2 := by
    rcases le_total t 1 with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (FT1c_sqNorm_le k)
    · rw [min_eq_right h, one_pow, mul_one]; exact le_trans (min_le_right _ _) hd1
  -- `|W^{-a} Φ(E, k)| ≤ A W^τ W^{-a} d min(t,1)^2 + |C₁| W^{-(a+2)}`
  have hWa : (0 : ℝ) < (W : ℝ) ^ (-a) := Real.rpow_pos_of_pos hW0 _
  have hstep : ‖(((W : ℝ) ^ (-a) : ℝ) : ℂ) * Φ E k‖ ≤
      A * ((W : ℝ) ^ τ * (W : ℝ) ^ (-a)) * (d * min t 1 ^ 2) + |C₁| * (W : ℝ) ^ (-(a + 2)) := by
    have h3 := norm_sub_le_norm_sub_add_norm_sub ((((W : ℝ) ^ (-a) : ℝ) : ℂ) * Φ E k)
      (zdSeries (ValZ.sigKer Sig P.ψ E l W) p) 0
    simp only [sub_zero] at h3
    have h4 : ‖(((W : ℝ) ^ (-a) : ℝ) : ℂ) * Φ E k‖ ≤
        ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p‖ +
          ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Φ E k‖ := by
      have := norm_sub_norm_le (zdSeries (ValZ.sigKer Sig P.ψ E l W) p)
        (zdSeries (ValZ.sigKer Sig P.ψ E l W) p - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Φ E k)
      simp only [sub_sub_cancel] at this
      linarith [norm_sub_rev (zdSeries (ValZ.sigKer Sig P.ψ E l W) p)
        ((((W : ℝ) ^ (-a) : ℝ) : ℂ) * Φ E k)]
    refine le_trans h4 (add_le_add (le_trans hlabW ?_) (le_trans hcmpW ?_))
    · gcongr
    · exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hW0.le _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWa] at hstep
  have hΦ : ‖Φ E k‖ ≤ A * (W : ℝ) ^ τ * (d * min t 1 ^ 2) + |C₁| * ((W : ℝ) ^ 2)⁻¹ := by
    have h5 : (W : ℝ) ^ (-(a + 2)) = (W : ℝ) ^ (-a) * ((W : ℝ) ^ 2)⁻¹ := by
      rw [neg_add, Real.rpow_add hW0, Real.rpow_neg hW0.le 2, Real.rpow_two]
    rw [h5] at hstep
    have h6 : (W : ℝ) ^ (-a) * ‖Φ E k‖ ≤ (W : ℝ) ^ (-a) *
        (A * (W : ℝ) ^ τ * (d * min t 1 ^ 2) + |C₁| * ((W : ℝ) ^ 2)⁻¹) := by
      calc (W : ℝ) ^ (-a) * ‖Φ E k‖ ≤ _ := hstep
        _ = _ := by ring
    exact le_of_mul_le_mul_left h6 hWa
  refine le_trans hΦ ?_
  have hWτ : (W : ℝ) ^ τ ≤ (2 * M) ^ τ * u ^ τ := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow hW0.le (by linarith) hτ.le
  have hτ2 : 0 ≤ 2 - τ := by linarith
  rcases le_total t 1 with h | h
  · -- small `k`: `u = 1/t`
    have hu : u = 1 / t := max_eq_right (by
      rw [le_div_iff₀ ht]; nlinarith)
    rw [min_eq_left h]
    have hW2 : ((W : ℝ) ^ 2)⁻¹ ≤ t ^ 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity), ← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (by rwa [one_div] at hWit) 2
    have ht2 : t ^ 2 ≤ t ^ (2 - τ) := by
      rw [← Real.rpow_natCast]; push_cast
      exact Real.rpow_le_rpow_of_exponent_ge ht h (by linarith)
    have hut : u ^ τ * t ^ 2 = t ^ (2 - τ) := by
      rw [hu, Real.div_rpow zero_le_one ht.le, Real.one_rpow, ← Real.rpow_natCast,
        div_mul_eq_mul_div, one_mul, ← Real.rpow_sub ht]
      push_cast; ring_nf
    have h1t : (1 : ℝ) ≤ (1 + t) ^ τ := Real.one_le_rpow (by linarith) hτ.le
    have hpos : 0 ≤ t ^ (2 - τ) := Real.rpow_nonneg ht.le _
    calc A * (W : ℝ) ^ τ * (d * t ^ 2) + |C₁| * ((W : ℝ) ^ 2)⁻¹
        ≤ A * ((2 * M) ^ τ * u ^ τ) * (d * t ^ 2) + |C₁| * t ^ (2 - τ) := by
          gcongr; exact le_trans hW2 ht2
      _ = (A * d * (2 * M) ^ τ + |C₁|) * t ^ (2 - τ) := by rw [← hut]; ring
      _ ≤ (A * d * (2 * M) ^ τ + |C₁|) * t ^ (2 - τ) * (1 + t) ^ τ :=
          le_mul_of_one_le_right (by positivity) h1t
  · -- large `k`: `u = t`
    have hu : u = t := max_eq_left (by
      rw [div_le_iff₀ ht]; nlinarith)
    rw [min_eq_right h, Real.one_rpow, mul_one]
    have hW2 : ((W : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
    have htt : t ^ τ ≤ (1 + t) ^ τ := Real.rpow_le_rpow ht.le (by linarith) hτ.le
    have h1t : (1 : ℝ) ≤ (1 + t) ^ τ := Real.one_le_rpow (by linarith) hτ.le
    calc A * (W : ℝ) ^ τ * (d * 1 ^ 2) + |C₁| * ((W : ℝ) ^ 2)⁻¹
        ≤ A * ((2 * M) ^ τ * u ^ τ) * (d * 1 ^ 2) + |C₁| * 1 := by
          gcongr
      _ = A * d * (2 * M) ^ τ * t ^ τ + |C₁| := by rw [hu]; ring
      _ ≤ A * d * (2 * M) ^ τ * (1 + t) ^ τ + |C₁| * (1 + t) ^ τ :=
          add_le_add (mul_le_mul_of_nonneg_left htt hC0)
            (le_mul_of_one_le_right (abs_nonneg _) h1t)
      _ = (A * d * (2 * M) ^ τ + |C₁|) * (1 + t) ^ τ := by ring

/-- The hypotheses of `FT1c_graph` for one edge: the `W`-dependent symbol `f` (measurable,
`2π`-periodic, `‖f‖ ≤ B W^β ω(W p)^γ` on `[−π, π]^d`), its comparison with `W^{-α} g(W p)` up to
`C W^{-D} ω(W p)^γ` for every `D`, and the `W`-free symbol `g` (measurable, bounded by
`B ω^γ (1 + ‖k‖)^{-K}` for every `K`, without the decay factor on a dotted edge), uniformly in
`E ∈ A`. -/
private def FT1c_EdgeOK (A : Set ℝ) (f : ℝ → ℕ → (Fin d → ℝ) → ℂ) (g : ℝ → (Fin d → ℝ) → ℂ) (α : ℝ)
    (γ : ℕ) (isDot : Bool) : Prop :=
  (∃ B β W₀ : ℝ, 0 ≤ β ∧ ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ A, Measurable (f x W) ∧
      (∀ p (z : Fin d → ℤ), f x W (p + fun i => 2 * Real.pi * z i) = f x W p) ∧
      ∀ p ∈ cubePi d, ‖f x W p‖ ≤ B * (W : ℝ) ^ β * FT1c_om ((W : ℝ) • p) ^ γ) ∧
    (∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ A, ∀ p ∈ cubePi d,
      ‖f x W p - (((W : ℝ) ^ (-α) : ℝ) : ℂ) * g x ((W : ℝ) • p)‖ ≤
        C * (W : ℝ) ^ (-D) * FT1c_om ((W : ℝ) • p) ^ γ) ∧
    (∀ x ∈ A, Measurable (g x)) ∧
    (∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ A, ∀ r,
      ‖g x r‖ ≤ B * FT1c_om r ^ γ * (if isDot then 1 else ((1 + ‖r‖) ^ K)⁻¹))

/-- `C / W^{⌈D⌉} ≤ |C| W^{-D}` for `W ≥ 1`. -/
private theorem FT1c_div_pow_le {W : ℝ} (hW : 1 ≤ W) (C D : ℝ) :
    C / W ^ ⌈D⌉₊ ≤ |C| * W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  rw [div_eq_mul_inv]
  refine mul_le_mul (le_abs_self C) ?_ (by positivity) (abs_nonneg _)
  exact FT1c_inv_pow_le_rpow hW (Nat.le_ceil D)

private theorem FT1c_psi_smul (P : Profile d) (W : ℝ) (p : Fin d → ℝ) :
    FT1c_psi P (W • p) = (P.ψ (W • WithLp.toLp 2 p) : ℂ) := by
  rw [FT1c_psi, WithLp.toLp_smul]

private theorem FT1c_rpow_neg_zero (W : ℝ) : (((W : ℝ) ^ (-(0 : ℝ)) : ℝ) : ℂ) = 1 := by simp

/-- The waved edge `s`: `ŝ` against `ψ(W p)`. -/
private theorem FT1c_edge_s (hd : 5 ≤ d) (P : Profile d) {κ : ℝ} (hκ : 0 < κ) :
    FT1c_EdgeOK {E : ℝ | |E| < 2 - κ} (fun _ W => zdSymbol (Sinf P.ψ W))
      (fun _ => FT1c_psi P) 0 0 false := by
  obtain ⟨c, b, W₁, hc, hb, hsym⟩ := FT1b.edgeSymbols hd P hκ
  refine ⟨⟨1, 0, W₁, le_rfl, fun W hW E hE => ?_⟩, fun D => ?_, fun _ _ => FT1c_measurable_psi P,
    fun K => ?_⟩
  · obtain ⟨-, -, -, -, hm, -, -, -, hper, -, -, -, -, hb', -⟩ := hsym W hW E hE
    refine ⟨hm, fun p z => (hper p z).1, fun p _ => ?_⟩
    simp only [Real.rpow_zero, pow_zero, mul_one]
    exact (hb' p).1
  · obtain ⟨C, W₂, -, hcmp⟩ := FT1b.symbolCompare P hκ ⌈D⌉₊
    refine ⟨|C|, max W₂ 1, fun W hW E hE p hp => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
    rw [FT1c_rpow_neg_zero, one_mul]
    simp only [FT1c_psi_smul, pow_zero, mul_one]
    exact le_trans (hcmp W (le_trans (le_max_left _ _) hW) E hE p hp).1
      (FT1c_div_pow_le hW1 C D)
  · obtain ⟨C, hC, h⟩ := FT1c_psi_decay P K
    refine ⟨C, hC, fun _ _ r => ?_⟩
    simp only [pow_zero, mul_one, Bool.false_eq_true, if_false]
    exact h r

/-- The `W`-free symbol of `S^±`: `w ψ(k)/(1 − w ψ(k))` with `w = m²` or `m̄²`. -/
private def FT1c_gpm (P : Profile d) (w : ℂ) (k : Fin d → ℝ) : ℂ :=
  w * FT1c_psi P k / (1 - w * FT1c_psi P k)

private theorem FT1c_measurable_gpm (P : Profile d) (w : ℂ) : Measurable (FT1c_gpm P w) :=
  (measurable_const.mul (FT1c_measurable_psi P)).div
    (measurable_const.sub (measurable_const.mul (FT1c_measurable_psi P)))

/-- `|w ψ/(1 − w ψ)| ≤ b⁻¹ |ψ|` for `w = m(E)²` or `m̄(E)²`, `|E| < 2 − κ`. -/
private theorem FT1c_gpm_le (P : Profile d) {κ : ℝ} (hκ : 0 < κ) :
    ∃ b : ℝ, 0 < b ∧ ∀ E : ℝ, |E| < 2 - κ → ∀ k : Fin d → ℝ,
      ‖FT1c_gpm P (mE E ^ 2) k‖ ≤ b⁻¹ * ‖FT1c_psi P k‖ ∧
        ‖FT1c_gpm P (conj (mE E) ^ 2) k‖ ≤ b⁻¹ * ‖FT1c_psi P k‖ := by
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨b, hb, hden⟩ := FT1b_denom hκ hc'.pos
  refine ⟨b, hb, fun E hE k => ?_⟩
  have hm1 : ‖mE E‖ = 1 := (mE_bulk κ hκ E hE.le).1
  have ht : -1 + c' / 2 ≤ P.ψ (WithLp.toLp 2 k) := by
    have := hc'.range (WithLp.toLp 2 k); have := hc'.pos; linarith [this]
  obtain ⟨h1, h2⟩ := hden E hE.le _ ht
  constructor
  · rw [FT1c_gpm, norm_div, norm_mul, norm_pow, hm1, one_pow, one_mul, div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right (inv_anti₀ hb h1) (norm_nonneg _)
  · rw [FT1c_gpm, norm_div, norm_mul, norm_pow, Complex.norm_conj, hm1, one_pow, one_mul,
      div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right (inv_anti₀ hb h2) (norm_nonneg _)

/-- The waved edges `S^±`: `ψ_±` against `w ψ(W p)/(1 − w ψ(W p))`. -/
private theorem FT1c_edge_pm (hd : 5 ≤ d) (P : Profile d) {κ : ℝ} (hκ : 0 < κ) (plus : Bool) :
    FT1c_EdgeOK {E : ℝ | |E| < 2 - κ}
      (fun E W => if plus then FT1b.plusSym (mE E) (Sinf P.ψ W) else FT1b.minusSym (mE E) (Sinf P.ψ W))
      (fun E => FT1c_gpm P (if plus then mE E ^ 2 else conj (mE E) ^ 2)) 0 0 false := by
  obtain ⟨c, b, W₁, hc, hb, hsym⟩ := FT1b.edgeSymbols hd P hκ
  obtain ⟨b', hb', hgpm⟩ := FT1c_gpm_le P hκ
  refine ⟨⟨b⁻¹, 0, W₁, le_rfl, fun W hW E hE => ?_⟩, fun D => ?_, fun _ _ =>
    FT1c_measurable_gpm P _, fun K => ?_⟩
  · obtain ⟨-, -, -, -, -, hmp, hmm, -, hper, -, -, -, -, hb2, -⟩ := hsym W hW E hE
    simp only [Real.rpow_zero, pow_zero, mul_one]
    cases plus
    · exact ⟨hmm, fun p z => (hper p z).2.2.1, fun p _ => (hb2 p).2.2⟩
    · exact ⟨hmp, fun p z => (hper p z).2.1, fun p _ => (hb2 p).2.1⟩
  · obtain ⟨C, W₂, -, hcmp⟩ := FT1b.symbolCompare P hκ ⌈D⌉₊
    refine ⟨|C|, max W₂ 1, fun W hW E hE p hp => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
    rw [FT1c_rpow_neg_zero, one_mul, pow_zero, mul_one]
    obtain ⟨-, h2, h3, -⟩ := hcmp W (le_trans (le_max_left _ _) hW) E hE p hp
    cases plus
    · simp only [Bool.false_eq_true, if_false, FT1c_gpm, FT1c_psi_smul]
      exact le_trans h3 (FT1c_div_pow_le hW1 C D)
    · simp only [if_true, FT1c_gpm, FT1c_psi_smul]
      exact le_trans h2 (FT1c_div_pow_le hW1 C D)
  · obtain ⟨C, hC, h⟩ := FT1c_psi_decay P K
    refine ⟨b'⁻¹ * C, by positivity, fun E hE r => ?_⟩
    simp only [pow_zero, mul_one, Bool.false_eq_true, if_false]
    have hg : ‖FT1c_gpm P (if plus then mE E ^ 2 else conj (mE E) ^ 2) r‖ ≤ b'⁻¹ * ‖FT1c_psi P r‖ := by
      cases plus
      · exact (hgpm E hE r).2
      · exact (hgpm E hE r).1
    calc _ ≤ b'⁻¹ * ‖FT1c_psi P r‖ := hg
      _ ≤ b'⁻¹ * (C * ((1 + ‖r‖) ^ K)⁻¹) := by gcongr; exact h r
      _ = _ := by ring

/-- The dotted edge: the symbol `1` on both sides. -/
private theorem FT1c_edge_dot (A : Set ℝ) :
    FT1c_EdgeOK (d := d) A (fun _ _ _ => 1) (fun _ _ => 1) 0 0 true := by
  refine ⟨⟨1, 0, 0, le_rfl, fun W _ _ _ => ⟨measurable_const, fun _ _ => rfl, fun p _ => ?_⟩⟩,
    fun D => ⟨0, 0, fun W _ _ _ p _ => ?_⟩, fun _ _ => measurable_const, fun K => ⟨1, zero_le_one,
      fun _ _ r => ?_⟩⟩
  · simp
  · simp
  · simp

private theorem FT1c_measurable_listProd (o : List ℕ) (F : ℕ → (Fin d → ℝ) → ℂ)
    (hF : ∀ l ∈ o, Measurable (F l)) : Measurable fun k => (o.map fun l => F l k).prod := by
  induction o with
  | nil => simp only [List.map_nil, List.prod_nil]; exact measurable_const
  | cons l o ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF l List.mem_cons_self).mul (ih fun l' hl' => hF l' (List.mem_cons_of_mem _ hl'))

private theorem FT1c_norm_listProd_le (o : List ℕ) (X : ℕ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hX : ∀ l ∈ o, ‖X l‖ ≤ M) : ‖(o.map X).prod‖ ≤ M ^ o.length := by
  induction o with
  | nil => simp
  | cons l o ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul, pow_succ]
    rw [mul_comm]
    exact mul_le_mul (ih fun l' hl' => hX l' (List.mem_cons_of_mem _ hl')) (hX l List.mem_cons_self)
      (norm_nonneg _) (pow_nonneg hM _)

/-- `Π_{l ∈ o} W^{-a_l} = W^{-Σ_l a_l}`. -/
private theorem FT1c_listProd_rpow (o : List ℕ) (a : ℕ → ℝ) {W : ℝ} (hW : 0 < W) :
    (o.map fun l => (((W ^ (-a l) : ℝ)) : ℂ)).prod = (((W ^ (-(o.map a).sum) : ℝ)) : ℂ) := by
  induction o with
  | nil => simp
  | cons l o ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, neg_add, Real.rpow_add hW]
    push_cast; ring

/-- `ω(k)^τ ≤ ω(k)` for `τ ≤ 1`, and `(1 + ‖k‖)^τ ≤ 1 + ‖k‖`. -/
private theorem FT1c_rpow_le_self {x τ : ℝ} (hx : 1 ≤ x) (hτ : τ ≤ 1) : x ^ τ ≤ x := by
  calc x ^ τ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hτ
    _ = x := Real.rpow_one x

/-- **The `W`-free chain symbol** `ψ_Θ^{r+1} Π_{l ∈ o} Φ̊_l`: measurable, and
`|ψ_Θ^{r+1} Π Φ̊_l| ≤ B_K ω^{2 + rτ} (1 + ‖k‖)^{-K}` for every `K`, with `τ = 1/(4(r + 1))`. -/
private theorem FT1c_theta_g (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (o : List ℕ)
    (ho : labelOK N o = true) (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ)
    (hΦ : ∀ l ∈ o, FT1c_LabGood P Sig κ l (Φ l)) :
    (∀ E : ℝ, |E| < 2 - κ →
      Measurable fun k => FT1c_gth P k ^ (o.length + 1) * (o.map fun l => Φ l E k).prod) ∧
    ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ E : ℝ, |E| < 2 - κ → ∀ k : Fin d → ℝ,
      ‖FT1c_gth P k ^ (o.length + 1) * (o.map fun l => Φ l E k).prod‖ ≤
        B * FT1c_om k ^ (2 + (o.length : ℝ) / (4 * (o.length + 1))) * ((1 + ‖k‖) ^ K)⁻¹ := by
  have hlab : ∀ l ∈ o, 4 ≤ l ∧ l ≤ N ∧ Even l := by
    intro l hl
    have h := List.all_eq_true.1 ho l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, Nat.even_iff.2 h.2⟩
  set r := o.length
  set τ : ℝ := 1 / (4 * (r + 1))
  have hτ : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by
    simp only [τ]; rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ r := Nat.cast_nonneg _; linarith
  have hrτ : (r : ℝ) * τ ≤ 1 / 4 := by
    simp only [τ]; rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine ⟨fun E hE => (FT1c_measurable_gth P).pow_const _ |>.mul
    (FT1c_measurable_listProd o _ fun l hl => (hΦ l hl).1 E hE), fun K => ?_⟩
  -- the label bounds
  have hbd : ∀ l ∈ o, ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, |E| < 2 - κ → ∀ k : Fin d → ℝ, k ≠ 0 →
      ‖Φ l E k‖ ≤ C * min ‖k‖ 1 ^ (2 - τ) * (1 + ‖k‖) ^ τ := fun l hl =>
    FT1c_labBound hd P Sig N hSig hκ l (hlab l hl).1 (hlab l hl).2.1 (hlab l hl).2.2 (hΦ l hl)
      hτ hτ1
  choose! Cl hCl0 hCl using hbd
  set Cm := (o.map Cl).sum + 1
  have hCm : ∀ l ∈ o, Cl l ≤ Cm := fun l hl => by
    have := List.single_le_sum (fun l' hl' => by
      obtain ⟨l'', hl'', rfl⟩ := List.mem_map.1 hl'; exact hCl0 l'' hl'') (Cl l)
      (List.mem_map.2 ⟨l, hl, rfl⟩)
    simp only [Cm]; linarith
  have hCm0 : 0 ≤ Cm := by
    have : 0 ≤ (o.map Cl).sum := List.sum_nonneg fun x hx => by
      obtain ⟨l'', hl'', rfl⟩ := List.mem_map.1 hx; exact hCl0 l'' hl''
    simp only [Cm]; linarith
  obtain ⟨Cψ, hCψ, hψd⟩ := FT1c_psi_decay P (K + 1)
  set cc := P.cψ⁻¹
  have hcc : 0 < cc := inv_pos.2 P.cψ_pos
  refine ⟨cc ^ (r + 1) * Cm ^ r * Cψ, by positivity, fun E hE k => ?_⟩
  rcases eq_or_ne k 0 with rfl | hk
  · have : FT1c_gth P 0 = 0 := by simp [FT1c_gth, FT1c_psi, P.at_zero]
    rw [this, zero_pow (Nat.succ_ne_zero _), zero_mul, norm_zero]
    have : 0 ≤ FT1c_om (0 : Fin d → ℝ) ^ (2 + (r : ℝ) / (4 * (r + 1))) :=
      Real.rpow_nonneg (FT1c_om_pos _).le _
    positivity
  set ω := FT1c_om k
  have hω1 : 1 ≤ ω := FT1c_one_le_om k
  have hω0 : 0 < ω := FT1c_om_pos k
  set t := ‖k‖
  have hmin : min t 1 = ω⁻¹ := (FT1c_om_inv k hk).symm
  -- each label factor
  have hlbl : ∀ l ∈ o, ‖Φ l E k‖ ≤ Cm * (ω ^ τ * (ω ^ 2)⁻¹ * (1 + t) ^ τ) := by
    intro l hl
    refine le_trans (hCl l hl E hE k hk) ?_
    rw [hmin, Real.inv_rpow hω0.le, ← Real.rpow_neg hω0.le, neg_sub, Real.rpow_sub hω0,
      Real.rpow_two]
    have h0 : 0 ≤ ω ^ τ / ω ^ 2 * (1 + t) ^ τ := by positivity
    calc Cl l * (ω ^ τ / ω ^ 2) * (1 + t) ^ τ = Cl l * (ω ^ τ / ω ^ 2 * (1 + t) ^ τ) := by ring
      _ ≤ Cm * (ω ^ τ / ω ^ 2 * (1 + t) ^ τ) := mul_le_mul_of_nonneg_right (hCm l hl) h0
      _ = _ := by rw [div_eq_mul_inv]
  have hprod := FT1c_norm_listProd_le o (fun l => Φ l E k) (by positivity) hlbl
  have hg1 : ‖FT1c_gth P k‖ ≤ cc * ‖FT1c_psi P k‖ * ω ^ 2 := FT1c_gth_le P k
  have hg2 : ‖FT1c_gth P k‖ ≤ cc * ω ^ 2 := FT1c_gth_le' P k
  have hψ1 := FT1c_norm_psi_le_one P k
  have hgp : ‖FT1c_gth P k ^ (r + 1)‖ ≤ cc * ‖FT1c_psi P k‖ * ω ^ 2 * (cc * ω ^ 2) ^ r := by
    rw [norm_pow, pow_succ']
    exact mul_le_mul hg1 (pow_le_pow_left₀ (norm_nonneg _) hg2 r) (by positivity) (by positivity)
  rw [norm_mul]
  have hψk := hψd k
  have h1t : (1 : ℝ) ≤ 1 + t := le_add_of_nonneg_right (norm_nonneg k)
  calc ‖FT1c_gth P k ^ (r + 1)‖ * ‖(o.map fun l => Φ l E k).prod‖
      ≤ cc * ‖FT1c_psi P k‖ * ω ^ 2 * (cc * ω ^ 2) ^ r *
          (Cm * (ω ^ τ * (ω ^ 2)⁻¹ * (1 + t) ^ τ)) ^ r :=
        mul_le_mul hgp hprod (norm_nonneg _) (by positivity)
    _ = cc ^ (r + 1) * Cm ^ r * ‖FT1c_psi P k‖ * ω ^ 2 * ((ω ^ τ) ^ r * ((1 + t) ^ τ) ^ r) := by
        have h : (ω ^ 2) ^ r * ((ω ^ 2)⁻¹) ^ r = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
        rw [mul_pow, mul_pow, mul_pow, mul_pow]
        calc _ = cc ^ (r + 1) * Cm ^ r * ‖FT1c_psi P k‖ * ω ^ 2 * ((ω ^ τ) ^ r * ((1 + t) ^ τ) ^ r) *
              ((ω ^ 2) ^ r * ((ω ^ 2)⁻¹) ^ r) := by ring
          _ = _ := by rw [h, mul_one]
    _ ≤ cc ^ (r + 1) * Cm ^ r * (Cψ * ((1 + t) ^ (K + 1))⁻¹) * ω ^ 2 *
          (ω ^ ((r : ℝ) * τ) * (1 + t)) := by
        gcongr
        · rw [← Real.rpow_natCast, ← Real.rpow_mul hω0.le, mul_comm]
        · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), mul_comm]
          exact FT1c_rpow_le_self h1t (by linarith)
    _ = cc ^ (r + 1) * Cm ^ r * Cψ * (ω ^ (2 : ℝ) * ω ^ ((r : ℝ) * τ)) * ((1 + t) ^ K)⁻¹ := by
        have h : (1 + t) * ((1 + t) ^ (K + 1))⁻¹ = ((1 + t) ^ K)⁻¹ := by
          rw [pow_succ, mul_inv, ← mul_assoc, mul_comm (1 + t), mul_assoc,
            mul_inv_cancel₀ (by positivity), mul_one]
        rw [Real.rpow_two, ← h]
        ring
    _ = cc ^ (r + 1) * Cm ^ r * Cψ * ω ^ (2 + (r : ℝ) / (4 * (r + 1))) * ((1 + t) ^ K)⁻¹ := by
        rw [← Real.rpow_add hω0]
        congr 3
        simp only [τ]; ring

/-- `x ^ a ≤ x ^ b` for `x ≥ 1`, `a ≤ b` (natural exponents). -/
private theorem FT1c_pow_mono {x : ℝ} (hx : 1 ≤ x) {a b : ℕ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
  pow_le_pow_right₀ hx h

/-- A label factor away from `p = 0`: `|W^{-a} Φ̊(k)| ≤ C · 5 W^τ` when
`|Φ̊(k)| ≤ C min(‖k‖, 1)^{2−τ} (1 + ‖k‖)^τ`, `1 ≤ ‖k‖ ≤ 4W`. -/
private theorem FT1c_far_b {W τ a C t : ℝ} (hW1 : 1 ≤ W) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (ht1 : 1 ≤ t) (htW : t ≤ 4 * W) {Φk : ℂ}
    (hΦ : ‖Φk‖ ≤ C * min t 1 ^ (2 - τ) * (1 + t) ^ τ) :
    ‖(((W ^ (-a) : ℝ)) : ℂ) * Φk‖ ≤ C * (5 * W ^ τ) := by
  have hW0 : 0 < W := by linarith
  have hWa : ‖(((W ^ (-a) : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hW0 _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have h5 : (1 + t) ^ τ ≤ 5 * W ^ τ := by
    calc (1 + t) ^ τ ≤ (5 * W) ^ τ := Real.rpow_le_rpow (by linarith) (by linarith) hτ0.le
      _ = 5 ^ τ * W ^ τ := Real.mul_rpow (by norm_num) hW0.le
      _ ≤ 5 * W ^ τ := by
          gcongr; exact FT1c_rpow_le_self (by norm_num) hτ1
  have hmin : min t 1 ^ (2 - τ) = 1 := by rw [min_eq_right ht1, Real.one_rpow]
  rw [hmin, mul_one] at hΦ
  rw [norm_mul]
  calc ‖(((W ^ (-a) : ℝ)) : ℂ)‖ * ‖Φk‖ ≤ 1 * (C * (5 * W ^ τ)) :=
        mul_le_mul hWa (le_trans hΦ (mul_le_mul_of_nonneg_left h5 hC)) (norm_nonneg _)
          zero_le_one
    _ = C * (5 * W ^ τ) := one_mul _

set_option maxHeartbeats 1000000 in
/-- **The raw comparison of the chain symbols** ([I, (7.28)] against its `W`-free form):
`|ψ_o(p) − W^{-α} g_o(W p)| ≤ R W^{-D} W^{rτ} ω(W p)^{2r+6}` on `[−π, π]^d`, for every `D`, with
`r = |o|`, `τ = 1/(4(r + 1))`. Near `p = 0` it combines [I, Claim 7.8] for `ψ_Θ` with the label
forms; away from `0` both sides are `O(W^{-D})`. -/
private theorem FT1c_theta_raw (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (o : List ℕ)
    (ho : labelOK N o = true) (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ)
    (hΦ : ∀ l ∈ o, FT1c_LabGood P Sig κ l (Φ l)) {Dr : ℝ} (hDr : 0 ≤ Dr) :
    ∃ R W₀ : ℝ, 0 ≤ R ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ p ∈ cubePi d,
      ‖FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p -
          ((((W : ℝ) ^ (-(o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) : ℝ)) : ℂ) *
            (FT1c_gth P ((W : ℝ) • p) ^ (o.length + 1) *
              (o.map fun l => Φ l E ((W : ℝ) • p)).prod)‖ ≤
        R * (W : ℝ) ^ (-Dr) * (W : ℝ) ^ ((o.length : ℝ) / (4 * (o.length + 1))) *
          FT1c_om ((W : ℝ) • p) ^ (2 * o.length + 6) := by
  have hlab : ∀ l ∈ o, 4 ≤ l ∧ l ≤ N ∧ Even l := by
    intro l hl
    have h := List.all_eq_true.1 ho l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, Nat.even_iff.2 h.2⟩
  set r := o.length
  set τ : ℝ := 1 / (4 * (r + 1))
  have hτ : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by
    simp only [τ]; rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ r := Nat.cast_nonneg _; linarith
  set a : ℕ → ℝ := fun l => ((l : ℝ) - 2) * d / 2
  have ha : ∀ l ∈ o, 0 ≤ a l := fun l hl => by
    have : (4 : ℝ) ≤ l := by exact_mod_cast (hlab l hl).1
    have : (0 : ℝ) ≤ ((l : ℝ) - 2) * d := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    simp only [a]; linarith
  set Dn := ⌈Dr⌉₊
  -- the Θ factors
  obtain ⟨C₁, W₁, -, hcmp⟩ := FT1b.symbolCompare P hκ Dn
  obtain ⟨c, b, We, hc, hb, hsym⟩ := FT1b.edgeSymbols (by omega) P hκ
  obtain ⟨Cψ, hCψ, hψd⟩ := FT1c_psi_decay P Dn
  -- the label factors
  have hL : ∀ l ∈ o, ∃ (Al Wl δl Cl Wl' Cl'' : ℝ), 0 ≤ Al ∧ 0 < δl ∧ 0 ≤ Cl'' ∧
      (∀ W : ℕ, Wl ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ p ∈ cubePi d,
        ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p‖ ≤
          Al * ((W : ℝ) ^ τ * (W : ℝ) ^ (-a l)) * min ((W : ℝ) ^ 2 * sqNorm p) 1) ∧
      (∀ W : ℕ, Wl' ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ p : Fin d → ℝ, ‖p‖ ≤ δl →
        ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p -
          (((W : ℝ) ^ (-a l) : ℝ) : ℂ) * Φ l E ((W : ℝ) • p)‖ ≤ Cl * (W : ℝ) ^ (-Dr)) ∧
      (∀ E : ℝ, |E| < 2 - κ → ∀ k : Fin d → ℝ, k ≠ 0 →
        ‖Φ l E k‖ ≤ Cl'' * min ‖k‖ 1 ^ (2 - τ) * (1 + ‖k‖) ^ τ) := by
    intro l hl
    obtain ⟨Al, Wl, hAl, hlb⟩ := FT1b_labelSym hd P Sig N hSig hκ l (hlab l hl).1 (hlab l hl).2.1
      (hlab l hl).2.2 hτ
    obtain ⟨-, δl, hδl, hcl⟩ := hΦ l hl
    obtain ⟨Cl, Wl', hcl'⟩ := hcl Dr
    obtain ⟨Cl'', hCl'', hbd⟩ := FT1c_labBound hd P Sig N hSig hκ l (hlab l hl).1 (hlab l hl).2.1
      (hlab l hl).2.2 (hΦ l hl) hτ hτ1
    exact ⟨Al, Wl, δl, Cl, Wl', Cl'', hAl, hδl, hCl'', fun W hW E hE p hp => (hlb W hW E hE).2 p hp,
      hcl', hbd⟩
  choose! Al Wl δl Cl Wl' Cl'' hAl hδl hCl'' hlB hlC hlΦ using hL
  set sumL : (ℕ → ℝ) → ℝ := fun F => (o.map fun l => |F l|).sum
  have hsumL : ∀ (F : ℕ → ℝ), ∀ l ∈ o, |F l| ≤ sumL F := fun F l hl =>
    List.single_le_sum (fun x hx => by
      obtain ⟨l', -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _) _
      (List.mem_map.2 ⟨l, hl, rfl⟩)
  have hsumL0 : ∀ F : ℕ → ℝ, 0 ≤ sumL F := fun F => List.sum_nonneg fun x hx => by
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
  set δ' : ℝ := 1 / (sumL (fun l => 1 / δl l) + 1)
  have hδ' : 0 < δ' := by have := hsumL0 (fun l => 1 / δl l); positivity
  have hδ'1 : δ' ≤ 1 := by
    have := hsumL0 (fun l => 1 / δl l)
    simp only [δ']; rw [div_le_one (by linarith)]; linarith
  have hδ'l : ∀ l ∈ o, δ' ≤ δl l := by
    intro l hl
    have h1 := hsumL (fun l => 1 / δl l) l hl
    have hδ := hδl l hl
    rw [abs_of_pos (by positivity)] at h1
    simp only [δ']
    rw [div_le_iff₀ (by have := hsumL0 (fun l => 1 / δl l); linarith)]
    rw [one_div, inv_le_iff_one_le_mul₀ hδ] at h1
    nlinarith
  set AB := sumL Al + 1
  set CB := sumL Cl + 1
  set CΦ := sumL Cl'' + 1
  set Mc := AB + CB + 5 * CΦ
  have hAB : 1 ≤ AB := by have := hsumL0 Al; simp only [AB]; linarith
  have hCB : 1 ≤ CB := by have := hsumL0 Cl; simp only [CB]; linarith
  have hCΦ : 1 ≤ CΦ := by have := hsumL0 Cl''; simp only [CΦ]; linarith
  have hMc : 1 ≤ Mc := by simp only [Mc]; linarith
  set cψ' := P.cψ⁻¹
  have hcψ' : 0 < cψ' := inv_pos.2 P.cψ_pos
  set Cθ := c⁻¹ + cψ' + 1
  have hCθ : 1 ≤ Cθ := by have := inv_pos.2 hc; simp only [Cθ]; linarith
  set R := ((r : ℝ) + 1) * |C₁| * Cθ ^ (r + 1) * Mc ^ r + Cθ ^ (r + 1) * r * CB * Mc ^ r +
    2 * (cψ' * Cψ * (δ' ^ Dn)⁻¹) * Cθ ^ r * Mc ^ r
  set W₀ := max (max (max W₁ We) (max (sumL Wl) (sumL Wl'))) (max (1 / δ') 1)
  have hCθ0 : 0 ≤ Cθ := by linarith
  have hMc0 : 0 ≤ Mc := by linarith
  have hCB0 : 0 ≤ CB := by linarith
  have hK0' : 0 ≤ cψ' * Cψ * (δ' ^ Dn)⁻¹ :=
    mul_nonneg (mul_nonneg hcψ'.le hCψ) (inv_nonneg.2 (pow_nonneg hδ'.le _))
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hR0 : 0 ≤ R := add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith)
    (abs_nonneg _)) (pow_nonneg hCθ0 _)) (pow_nonneg hMc0 _)) (mul_nonneg (mul_nonneg
      (mul_nonneg (pow_nonneg hCθ0 _) hr0) hCB0) (pow_nonneg hMc0 _))) (mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) hK0') (pow_nonneg hCθ0 _)) (pow_nonneg hMc0 _))
  refine ⟨R, W₀, hR0, fun W hW E hE p hp => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWδ : 1 / δ' ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWl : ∀ l ∈ o, Wl l ≤ W := fun l hl => le_trans (le_trans (le_abs_self _)
    (hsumL Wl l hl)) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_left _ _) hW))
  have hWl' : ∀ l ∈ o, Wl' l ≤ W := fun l hl => le_trans (le_trans (le_abs_self _)
    (hsumL Wl' l hl)) (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_left _ _) hW))
  have hW1' : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hW)
  have hWe : We ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hW)
  set x := FT1c_om ((W : ℝ) • p)
  have hx1 : 1 ≤ x := FT1c_one_le_om _
  have hx0 : 0 ≤ x := by linarith
  set A := FT1b.thetaSym (Sinf P.ψ W) p
  set aθ := FT1c_gth P ((W : ℝ) • p)
  set B : ℕ → ℂ := fun l => zdSeries (ValZ.sigKer Sig P.ψ E l W) p
  set bL : ℕ → ℂ := fun l => (((W : ℝ) ^ (-a l) : ℝ) : ℂ) * Φ l E ((W : ℝ) • p)
  -- rewrite both sides
  have hf : FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p = A ^ (r + 1) * (o.map B).prod :=
    rfl
  have hg : ((((W : ℝ) ^ (-(o.map a).sum) : ℝ)) : ℂ) *
      (aθ ^ (r + 1) * (o.map fun l => Φ l E ((W : ℝ) • p)).prod) = aθ ^ (r + 1) * (o.map bL).prod := by
    simp only [bL, List.prod_map_mul, FT1c_listProd_rpow o a hW0]; ring
  rw [hf, hg]
  -- the Θ bounds
  have hDW : FT1b.dW W p ≤ x ^ 2 := FT1c_dW_le W p
  have hA : ‖A‖ ≤ Cθ * x ^ 2 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hth⟩ := hsym W hWe E hE
    refine le_trans (hth p hp) ?_
    have := inv_pos.2 hc
    calc c⁻¹ * FT1b.dW W p ≤ c⁻¹ * x ^ 2 := by gcongr
      _ ≤ Cθ * x ^ 2 := by gcongr; simp only [Cθ]; linarith
  have haθ : ‖aθ‖ ≤ Cθ * x ^ 2 := by
    refine le_trans (FT1c_gth_le' P _) ?_
    gcongr; simp only [Cθ]; linarith [inv_pos.2 hc]
  have hAa : ‖A - aθ‖ ≤ |C₁| * (W : ℝ) ^ (-Dr) * x ^ 4 := by
    obtain ⟨-, -, -, h4⟩ := hcmp W hW1' E hE p hp
    have h5 : aθ = (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ) /
        (1 - (P.ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ)) := by
      simp only [aθ, FT1c_gth, FT1c_psi_smul]
    rw [h5]
    refine le_trans h4 ?_
    have h6 : FT1b.dW W p ^ 2 ≤ x ^ 4 := by
      calc FT1b.dW W p ^ 2 ≤ (x ^ 2) ^ 2 := pow_le_pow_left₀ (by
            unfold FT1b.dW; exact le_trans zero_le_one (le_max_left _ _)) hDW 2
        _ = x ^ 4 := by ring
    exact mul_le_mul (FT1c_div_pow_le hW1 C₁ Dr) h6
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hW0.le _))
  have hMθ : 1 ≤ Cθ * x ^ 2 := one_le_mul_of_one_le_of_one_le hCθ (one_le_pow₀ hx1)
  have hT1 : ‖A ^ (r + 1) - aθ ^ (r + 1)‖ ≤
      (r + 1 : ℕ) * (|C₁| * (W : ℝ) ^ (-Dr) * x ^ 4) * (Cθ * x ^ 2) ^ (r + 1) :=
    FT1c_pow_tel (r + 1) hMθ hA haθ hAa
  -- the label bounds
  set MB := Mc * (W : ℝ) ^ τ
  have hWτ : 1 ≤ (W : ℝ) ^ τ := Real.one_le_rpow hW1 hτ.le
  have hMB : 1 ≤ MB := one_le_mul_of_one_le_of_one_le hMc hWτ
  have hWD : 0 ≤ (W : ℝ) ^ (-Dr) := Real.rpow_nonneg hW0.le _
  have hWD1 : (W : ℝ) ^ (-Dr) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hBl' : ∀ l ∈ o, ‖B l‖ ≤ AB * (W : ℝ) ^ τ := by
    intro l hl
    refine le_trans (hlB l hl W (hWl l hl) E hE p hp) ?_
    have hWa : (W : ℝ) ^ (-a l) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1
      (by linarith [ha l hl])
    have hsq : 0 ≤ sqNorm p := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hmin0 : 0 ≤ min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
      le_min (mul_nonneg (sq_nonneg _) hsq) zero_le_one
    have hAl' : Al l ≤ AB := by
      have := hsumL Al l hl; rw [abs_of_nonneg (hAl l hl)] at this
      simp only [AB]; linarith
    have hWτ0 : 0 ≤ (W : ℝ) ^ τ := Real.rpow_nonneg hW0.le _
    have hWa0 : 0 ≤ (W : ℝ) ^ (-a l) := Real.rpow_nonneg hW0.le _
    have e1 : (W : ℝ) ^ τ * (W : ℝ) ^ (-a l) ≤ (W : ℝ) ^ τ :=
      mul_le_of_le_one_right hWτ0 hWa
    have e2 : Al l * ((W : ℝ) ^ τ * (W : ℝ) ^ (-a l)) ≤ AB * (W : ℝ) ^ τ :=
      mul_le_mul hAl' e1 (mul_nonneg hWτ0 hWa0) (by linarith)
    calc Al l * ((W : ℝ) ^ τ * (W : ℝ) ^ (-a l)) * min ((W : ℝ) ^ 2 * sqNorm p) 1
        ≤ AB * (W : ℝ) ^ τ * 1 :=
          mul_le_mul e2 (min_le_right _ _) hmin0 (mul_nonneg (by linarith) hWτ0)
      _ = AB * (W : ℝ) ^ τ := mul_one _
  have hBl : ∀ l ∈ o, ‖B l‖ ≤ MB := fun l hl => le_trans (hBl' l hl)
    (mul_le_mul_of_nonneg_right (by simp only [Mc]; linarith) (by linarith))
  have hprodB : ‖(o.map B).prod‖ ≤ MB ^ r :=
    FT1c_norm_listProd_le o B (by linarith) hBl
  have hRest : ‖aθ ^ (r + 1) * ((o.map B).prod - (o.map bL).prod)‖ ≤
      (Cθ * x ^ 2) ^ (r + 1) * (r * (CB * (W : ℝ) ^ (-Dr)) * MB ^ r) +
        (cψ' * Cψ * (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr)) * (Cθ * x ^ 2) ^ r * (2 * MB ^ r) := by
    rw [norm_mul, norm_pow]
    have hMB0 : 0 ≤ MB := by linarith
    have hCx : 0 ≤ Cθ * x ^ 2 := mul_nonneg hCθ0 (sq_nonneg x)
    have hnn1 : 0 ≤ (Cθ * x ^ 2) ^ (r + 1) * (r * (CB * (W : ℝ) ^ (-Dr)) * MB ^ r) :=
      mul_nonneg (pow_nonneg hCx _) (mul_nonneg (mul_nonneg hr0 (mul_nonneg hCB0 hWD))
        (pow_nonneg hMB0 _))
    have hnn2 : 0 ≤ (cψ' * Cψ * (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr)) * (Cθ * x ^ 2) ^ r *
        (2 * MB ^ r) :=
      mul_nonneg (mul_nonneg (mul_nonneg hK0' hWD) (pow_nonneg hCx _))
        (mul_nonneg (by norm_num) (pow_nonneg hMB0 _))
    by_cases hnear : ‖p‖ ≤ δ'
    · -- near `p = 0`: the label forms
      have hBb : ∀ l ∈ o, ‖B l - bL l‖ ≤ CB * (W : ℝ) ^ (-Dr) := by
        intro l hl
        refine le_trans (hlC l hl W (hWl' l hl) E hE p (le_trans hnear (hδ'l l hl))) ?_
        gcongr
        have := hsumL Cl l hl
        simp only [CB]; linarith [le_abs_self (Cl l)]
      have hbl : ∀ l ∈ o, ‖bL l‖ ≤ MB := by
        intro l hl
        have h1 : ‖bL l‖ ≤ ‖B l‖ + ‖B l - bL l‖ := by
          calc ‖bL l‖ = ‖B l - (B l - bL l)‖ := by rw [sub_sub_cancel]
            _ ≤ ‖B l‖ + ‖B l - bL l‖ := norm_sub_le _ _
        have h2 := hBb l hl
        have h3 := hBl' l hl
        have h4 : CB * (W : ℝ) ^ (-Dr) ≤ CB * (W : ℝ) ^ τ := by
          gcongr; linarith
        have h5 : AB * (W : ℝ) ^ τ + CB * (W : ℝ) ^ τ ≤ MB := by
          have hWτ0 : 0 ≤ (W : ℝ) ^ τ := Real.rpow_nonneg hW0.le _
          have : AB + CB ≤ Mc := by simp only [Mc]; linarith
          calc AB * (W : ℝ) ^ τ + CB * (W : ℝ) ^ τ = (AB + CB) * (W : ℝ) ^ τ := by ring
            _ ≤ Mc * (W : ℝ) ^ τ := mul_le_mul_of_nonneg_right this hWτ0
        linarith
      have htel := (FT1c_list_tel o B bL hMB hBl hbl hBb).2.2
      have ha1 : ‖aθ‖ ^ (r + 1) ≤ (Cθ * x ^ 2) ^ (r + 1) := pow_le_pow_left₀ (norm_nonneg _) haθ _
      calc ‖aθ‖ ^ (r + 1) * ‖(o.map B).prod - (o.map bL).prod‖
          ≤ (Cθ * x ^ 2) ^ (r + 1) * (r * (CB * (W : ℝ) ^ (-Dr)) * MB ^ r) :=
            mul_le_mul ha1 htel (norm_nonneg _) (pow_nonneg hCx _)
        _ ≤ _ := le_add_of_nonneg_right hnn2
    · -- away from `0`: both sides are small
      push Not at hnear
      have hWp : 1 ≤ ‖(W : ℝ) • p‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hW0]
        have h1 : (1 : ℝ) ≤ W * δ' := by rw [div_le_iff₀ hδ'] at hWδ; exact hWδ
        exact le_trans h1 (mul_le_mul_of_nonneg_left hnear.le hW0.le)
      have hx : x = 1 := FT1c_om_eq_one hWp
      have hpπ : ‖p‖ ≤ Real.pi := (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun i => by
        rw [Real.norm_eq_abs, abs_le]; exact hp i trivial
      have haθs : ‖aθ‖ ≤ cψ' * Cψ * (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr) := by
        have hg := FT1c_gth_le P ((W : ℝ) • p)
        rw [show FT1c_om ((W : ℝ) • p) = 1 from hx, one_pow, mul_one] at hg
        refine le_trans hg ?_
        have h1 := hψd ((W : ℝ) • p)
        have h2 : ((1 + ‖(W : ℝ) • p‖) ^ Dn)⁻¹ ≤ (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr) := by
          have h3 : δ' * W ≤ 1 + ‖(W : ℝ) • p‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hW0, mul_comm δ']
            exact le_trans (mul_le_mul_of_nonneg_left hnear.le hW0.le)
              (le_add_of_nonneg_left zero_le_one)
          calc ((1 + ‖(W : ℝ) • p‖) ^ Dn)⁻¹ ≤ ((δ' * W) ^ Dn)⁻¹ :=
                inv_anti₀ (pow_pos (mul_pos hδ' hW0) _)
                  (pow_le_pow_left₀ (mul_nonneg hδ'.le hW0.le) h3 _)
            _ = (δ' ^ Dn)⁻¹ * ((W : ℝ) ^ Dn)⁻¹ := by rw [mul_pow, mul_inv]
            _ ≤ (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr) := by
                gcongr; exact FT1c_inv_pow_le_rpow hW1 (Nat.le_ceil Dr)
        calc cψ' * ‖FT1c_psi P ((W : ℝ) • p)‖ ≤ cψ' * (Cψ * ((1 + ‖(W : ℝ) • p‖) ^ Dn)⁻¹) := by
              gcongr
          _ ≤ cψ' * (Cψ * ((δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr))) := by gcongr
          _ = _ := by ring
      have hbl : ∀ l ∈ o, ‖bL l‖ ≤ MB := by
        intro l hl
        have hp0 : (W : ℝ) • p ≠ 0 := by
          intro h; rw [h, norm_zero] at hWp; exact absurd hWp (by norm_num)
        have hCl : Cl'' l ≤ CΦ := by
          have := hsumL Cl'' l hl; rw [abs_of_nonneg (hCl'' l hl)] at this
          simp only [CΦ]; linarith
        have h6 : ‖(W : ℝ) • p‖ ≤ 4 * W := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hW0, mul_comm]
          exact mul_le_mul_of_nonneg_right (le_trans hpπ Real.pi_le_four) hW0.le
        have hb := FT1c_far_b hW1 hτ hτ1 (ha l hl) (hCl'' l hl) hWp h6
          (hlΦ l hl E hE ((W : ℝ) • p) hp0)
        have hWτ0 : 0 ≤ (W : ℝ) ^ τ := Real.rpow_nonneg hW0.le _
        have hMB' : Cl'' l * (5 * (W : ℝ) ^ τ) ≤ MB := by
          have : 5 * Cl'' l ≤ Mc := by simp only [Mc]; linarith
          calc Cl'' l * (5 * (W : ℝ) ^ τ) = (5 * Cl'' l) * (W : ℝ) ^ τ := by ring
            _ ≤ Mc * (W : ℝ) ^ τ := mul_le_mul_of_nonneg_right this hWτ0
        exact le_trans hb hMB'
      have hpb : ‖(o.map bL).prod‖ ≤ MB ^ r := FT1c_norm_listProd_le o bL hMB0 hbl
      have ha1 : ‖aθ‖ ^ (r + 1) ≤ (cψ' * Cψ * (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr)) * (Cθ * x ^ 2) ^ r := by
        rw [pow_succ']
        exact mul_le_mul haθs (pow_le_pow_left₀ (norm_nonneg _) haθ _)
          (pow_nonneg (norm_nonneg _) _) (mul_nonneg hK0' hWD)
      calc ‖aθ‖ ^ (r + 1) * ‖(o.map B).prod - (o.map bL).prod‖
          ≤ ((cψ' * Cψ * (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr)) * (Cθ * x ^ 2) ^ r) * (2 * MB ^ r) := by
            refine mul_le_mul ha1 (le_trans (norm_sub_le _ _)
              (le_trans (add_le_add hprodB hpb) (le_of_eq (by ring)))) (norm_nonneg _)
              (mul_nonneg (mul_nonneg hK0' hWD) (pow_nonneg hCx _))
        _ ≤ _ := le_add_of_nonneg_left hnn1
  have hsplit : A ^ (r + 1) * (o.map B).prod - aθ ^ (r + 1) * (o.map bL).prod =
      (A ^ (r + 1) - aθ ^ (r + 1)) * (o.map B).prod +
        aθ ^ (r + 1) * ((o.map B).prod - (o.map bL).prod) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul]
  have hMBr : MB ^ r = Mc ^ r * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) := by
    simp only [MB, mul_pow]
    rw [← Real.rpow_natCast ((W : ℝ) ^ τ), ← Real.rpow_mul hW0.le]
    congr 2; simp only [τ]; ring
  have hx2 : ∀ k ≤ 2 * r + 6, x ^ k ≤ x ^ (2 * r + 6) := fun k hk => FT1c_pow_mono hx1 hk
  set X := (W : ℝ) ^ (-Dr) * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) * x ^ (2 * r + 6)
  have hXa : ‖A ^ (r + 1) - aθ ^ (r + 1)‖ * ‖(o.map B).prod‖ ≤
      (((r : ℝ) + 1) * |C₁| * Cθ ^ (r + 1) * Mc ^ r) * X := by
    have hT1nn : 0 ≤ ((r + 1 : ℕ) : ℝ) * (|C₁| * (W : ℝ) ^ (-Dr) * x ^ 4) *
        (Cθ * x ^ 2) ^ (r + 1) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (abs_nonneg _) hWD)
        (pow_nonneg hx0 _))) (pow_nonneg (mul_nonneg hCθ0 (sq_nonneg x)) _)
    refine le_trans (mul_le_mul hT1 hprodB (norm_nonneg _) hT1nn) (le_of_eq ?_)
    rw [hMBr, mul_pow, ← pow_mul]
    simp only [X]
    rw [show 2 * r + 6 = 4 + 2 * (r + 1) by ring, pow_add]
    push_cast; ring
  have hXb : (Cθ * x ^ 2) ^ (r + 1) * (r * (CB * (W : ℝ) ^ (-Dr)) * MB ^ r) ≤
      (Cθ ^ (r + 1) * r * CB * Mc ^ r) * X := by
    rw [hMBr, mul_pow, ← pow_mul]
    have h := hx2 (2 * (r + 1)) (by omega)
    simp only [X]
    have h0 : 0 ≤ Cθ ^ (r + 1) * r * CB * Mc ^ r * ((W : ℝ) ^ (-Dr) *
        (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1)))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hCθ0 _) hr0) hCB0)
        (pow_nonneg hMc0 _)) (mul_nonneg hWD (Real.rpow_nonneg hW0.le _))
    calc Cθ ^ (r + 1) * x ^ (2 * (r + 1)) * (r * (CB * (W : ℝ) ^ (-Dr)) *
          (Mc ^ r * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1)))))
        = Cθ ^ (r + 1) * r * CB * Mc ^ r * ((W : ℝ) ^ (-Dr) *
            (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1)))) * x ^ (2 * (r + 1)) := by ring
      _ ≤ Cθ ^ (r + 1) * r * CB * Mc ^ r * ((W : ℝ) ^ (-Dr) *
            (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1)))) * x ^ (2 * r + 6) :=
          mul_le_mul_of_nonneg_left h h0
      _ = _ := by ring
  have hXc : (cψ' * Cψ * (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr)) * (Cθ * x ^ 2) ^ r * (2 * MB ^ r) ≤
      (2 * (cψ' * Cψ * (δ' ^ Dn)⁻¹) * Cθ ^ r * Mc ^ r) * X := by
    rw [hMBr, mul_pow, ← pow_mul]
    have h := hx2 (2 * r) (by omega)
    simp only [X]
    have h0 : 0 ≤ 2 * (cψ' * Cψ * (δ' ^ Dn)⁻¹) * Cθ ^ r * Mc ^ r * ((W : ℝ) ^ (-Dr) *
        (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1)))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0') (pow_nonneg hCθ0 _))
        (pow_nonneg hMc0 _)) (mul_nonneg hWD (Real.rpow_nonneg hW0.le _))
    calc (cψ' * Cψ * (δ' ^ Dn)⁻¹ * (W : ℝ) ^ (-Dr)) * (Cθ ^ r * x ^ (2 * r)) *
          (2 * (Mc ^ r * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1)))))
        = 2 * (cψ' * Cψ * (δ' ^ Dn)⁻¹) * Cθ ^ r * Mc ^ r * ((W : ℝ) ^ (-Dr) *
            (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1)))) * x ^ (2 * r) := by ring
      _ ≤ 2 * (cψ' * Cψ * (δ' ^ Dn)⁻¹) * Cθ ^ r * Mc ^ r * ((W : ℝ) ^ (-Dr) *
            (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1)))) * x ^ (2 * r + 6) :=
          mul_le_mul_of_nonneg_left h h0
      _ = _ := by ring
  calc ‖A ^ (r + 1) - aθ ^ (r + 1)‖ * ‖(o.map B).prod‖ +
        ‖aθ ^ (r + 1) * ((o.map B).prod - (o.map bL).prod)‖
      ≤ (((r : ℝ) + 1) * |C₁| * Cθ ^ (r + 1) * Mc ^ r) * X +
          ((Cθ ^ (r + 1) * r * CB * Mc ^ r) * X +
            (2 * (cψ' * Cψ * (δ' ^ Dn)⁻¹) * Cθ ^ r * Mc ^ r) * X) :=
        add_le_add hXa (le_trans hRest (add_le_add hXb hXc))
    _ = R * (W : ℝ) ^ (-Dr) * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) * x ^ (2 * r + 6) := by
        simp only [R, X]; ring

/-- **Interpolation of two bounds**: `e ≤ x₀ W^a ω^u` and `e ≤ y₀ W^b ω^v` give
`e ≤ x₀^θ y₀^{1−θ} W^{θa + (1−θ)b} ω^{θu + (1−θ)v}`. -/
private theorem FT1c_interp_bound {e x₀ y₀ W ω a b u v θ : ℝ} (hW : 0 < W) (hω : 0 < ω) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (he1 : e ≤ x₀ * W ^ a * ω ^ u)
    (he2 : e ≤ y₀ * W ^ b * ω ^ v) :
    e ≤ x₀ ^ θ * y₀ ^ (1 - θ) * W ^ (θ * a + (1 - θ) * b) * ω ^ (θ * u + (1 - θ) * v) := by
  have hX : 0 ≤ x₀ * W ^ a * ω ^ u := by positivity
  have hY : 0 ≤ y₀ * W ^ b * ω ^ v := by positivity
  refine le_trans (le_min he1 he2) (le_trans (FT1c_interp hX hY hθ0 hθ1) (le_of_eq ?_))
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hx₀ (by positivity),
    Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hy₀ (by positivity),
    ← Real.rpow_mul hW.le, ← Real.rpow_mul hω.le, ← Real.rpow_mul hW.le, ← Real.rpow_mul hω.le,
    Real.rpow_add hW, Real.rpow_add hω]
  ring_nf

/-- **The chain edge** `Θ_∞ Σ̊_{o₁} Θ_∞ ⋯ Σ̊_{o_r} Θ_∞` with label forms `Φ̊_l` ([I, (7.28)] against
`W^{-Σ(o_i − 2)d/2} ψ_Θ(W p)^{r+1} Π Φ̊_{o_i}(W p)`): the hypotheses of `FT1c_graph` with `γ = 3`;
[I, Claim 7.8] gives the comparison up to `W^{-D} ω^{2r+6}`, interpolated with the sup bounds of
order `ω^{2 + rτ}` down to `ω^3`. -/
private theorem FT1c_edge_theta (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (o : List ℕ)
    (ho : labelOK N o = true) (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ)
    (hΦ : ∀ l ∈ o, FT1c_LabGood P Sig κ l (Φ l)) :
    FT1c_EdgeOK {E : ℝ | |E| < 2 - κ}
      (fun E W => FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o)
      (fun E k => FT1c_gth P k ^ (o.length + 1) * (o.map fun l => Φ l E k).prod)
      ((o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) 3 false := by
  obtain ⟨hgm, hgb⟩ := FT1c_theta_g hd P Sig N hSig hκ o ho Φ hΦ
  set r := o.length
  set τ : ℝ := 1 / (4 * (r + 1))
  have hτ : 0 < τ := by positivity
  set s : ℝ := 2 + (r : ℝ) / (4 * (r + 1))
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrτ : (r : ℝ) / (4 * (r + 1)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hrτ' : (r : ℝ) / (4 * (r + 1)) = r * τ := by simp only [τ]; ring
  have hs3 : s ≤ 3 := by simp only [s]; linarith
  have hs2 : 2 ≤ s := by simp only [s]; have : 0 ≤ (r : ℝ) / (4 * (r + 1)) := by positivity
                         linarith
  have hα : 0 ≤ (o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum := by
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    have h := List.all_eq_true.1 ho l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have : (4 : ℝ) ≤ l := by exact_mod_cast h.1.1
    have : (0 : ℝ) ≤ ((l : ℝ) - 2) * d := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  obtain ⟨Cc, Wc, hCc, hch⟩ := FT1b.chainFourier hd P Sig N hSig hκ o ho hτ
  -- the bound of `ψ_o` with `ω`
  have hfb : ∀ W : ℕ, max Wc 1 ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ p ∈ cubePi d,
      ‖FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p‖ ≤
        Cc * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) * FT1c_om ((W : ℝ) • p) ^ (2 : ℝ) := by
    intro W hW E hE p hp
    have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
    have hW0' : (0 : ℝ) < W := by linarith
    obtain ⟨-, -, -, -, -, hb⟩ := hch W (le_trans (le_max_left _ _) hW) E hE
    refine le_trans (hb p hp) ?_
    rw [Real.rpow_two]
    have h1 : (W : ℝ) ^ ((r : ℝ) * τ - (o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) ≤
        (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) := by
      rw [hrτ']; exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have h2 := FT1c_dW_le W p
    have h3 : 0 ≤ FT1b.dW W p := by unfold FT1b.dW; exact le_trans zero_le_one (le_max_left _ _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hCc) h2 h3
      (mul_nonneg hCc (Real.rpow_nonneg hW0'.le _))
  refine ⟨⟨Cc, (r : ℝ) / (4 * (r + 1)), max Wc 1, by positivity, fun W hW E hE => ?_⟩,
    fun D => ?_, hgm, fun K => ?_⟩
  · obtain ⟨-, hm, hper, -, -, -⟩ := hch W (le_trans (le_max_left _ _) hW) E hE
    refine ⟨hm, hper, fun p hp => le_trans (hfb W hW E hE p hp) ?_⟩
    have hω1 := FT1c_one_le_om ((W : ℝ) • p)
    gcongr
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hω1 (by norm_num)
  · -- interpolation of the raw comparison and the sup bounds
    obtain ⟨B₀, hB₀, hg0⟩ := hgb 0
    set N₀ : ℕ := 2 * r + 6
    set θ : ℝ := 1 / (2 * N₀)
    have hN₀ : (0 : ℝ) < N₀ := by positivity
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := by
      simp only [θ]; rw [div_le_one (by positivity)]
      have : (6 : ℝ) ≤ N₀ := by simp only [N₀]; push_cast; linarith
      linarith
    set Dr : ℝ := (r : ℝ) / (4 * (r + 1)) + (|D| + (r : ℝ) / (4 * (r + 1))) / θ
    have hDr : 0 ≤ Dr := by
      have : 0 ≤ (r : ℝ) / (4 * (r + 1)) := by positivity
      have : 0 < θ := by positivity
      positivity
    obtain ⟨R, Wr, hR, hraw⟩ := FT1c_theta_raw hd P Sig N hSig hκ o ho Φ hΦ hDr
    refine ⟨R ^ θ * (Cc + B₀) ^ (1 - θ), max (max Wc 1) Wr, fun W hW E hE p hp => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
    have hW0 : (0 : ℝ) < W := by linarith
    set ω := FT1c_om ((W : ℝ) • p)
    have hω1 : 1 ≤ ω := FT1c_one_le_om _
    have hω0 : 0 < ω := by linarith
    set e := ‖FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p -
      ((((W : ℝ) ^ (-(o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) : ℝ)) : ℂ) *
        (FT1c_gth P ((W : ℝ) • p) ^ (r + 1) * (o.map fun l => Φ l E ((W : ℝ) • p)).prod)‖
    have he1 : e ≤ R * (W : ℝ) ^ (-Dr + (r : ℝ) / (4 * (r + 1))) * ω ^ (N₀ : ℝ) := by
      have h := hraw W (le_trans (le_max_right _ _) hW) E hE p hp
      rw [Real.rpow_add hW0, Real.rpow_natCast, ← mul_assoc]
      exact h
    have he2 : e ≤ (Cc + B₀) * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) * ω ^ s := by
      refine le_trans (norm_sub_le _ _) ?_
      have h1 := hfb W (le_trans (le_max_left _ _) hW) E hE p hp
      have h2 : ‖((((W : ℝ) ^ (-(o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) : ℝ)) : ℂ) *
          (FT1c_gth P ((W : ℝ) • p) ^ (r + 1) * (o.map fun l => Φ l E ((W : ℝ) • p)).prod)‖ ≤
          B₀ * ω ^ s := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hW0 _)]
        have h3 := hg0 E hE ((W : ℝ) • p)
        rw [pow_zero, inv_one, mul_one] at h3
        have h4 : (W : ℝ) ^ (-(o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
        calc (W : ℝ) ^ (-(o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) *
              ‖FT1c_gth P ((W : ℝ) • p) ^ (r + 1) * (o.map fun l => Φ l E ((W : ℝ) • p)).prod‖
            ≤ 1 * (B₀ * ω ^ s) := mul_le_mul h4 h3 (norm_nonneg _) zero_le_one
          _ = B₀ * ω ^ s := one_mul _
      have hWr : 1 ≤ (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) := Real.one_le_rpow hW1 (by positivity)
      have hω2 : ω ^ (2 : ℝ) ≤ ω ^ s := Real.rpow_le_rpow_of_exponent_le hω1 hs2
      have hωs : 0 ≤ ω ^ s := Real.rpow_nonneg hω0.le _
      calc ‖FT1b.chainSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W o p‖ +
            ‖((((W : ℝ) ^ (-(o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum) : ℝ)) : ℂ) *
              (FT1c_gth P ((W : ℝ) • p) ^ (r + 1) *
                (o.map fun l => Φ l E ((W : ℝ) • p)).prod)‖
          ≤ Cc * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) * ω ^ s +
              B₀ * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) * ω ^ s := by
            refine add_le_add (le_trans h1 ?_) (le_trans h2 ?_)
            · gcongr
            · calc B₀ * ω ^ s = B₀ * 1 * ω ^ s := by ring
                _ ≤ B₀ * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) * ω ^ s := by gcongr
        _ = (Cc + B₀) * (W : ℝ) ^ ((r : ℝ) / (4 * (r + 1))) * ω ^ s := by ring
    have hint := FT1c_interp_bound hW0 hω0 hR (add_nonneg hCc hB₀) hθ0 hθ1 he1 he2
    refine le_trans hint ?_
    have hexpW : θ * (-Dr + (r : ℝ) / (4 * (r + 1))) + (1 - θ) * ((r : ℝ) / (4 * (r + 1))) ≤ -D := by
      have hθpos : 0 < θ := by positivity
      have hDr' : θ * Dr = θ * ((r : ℝ) / (4 * (r + 1))) + (|D| + (r : ℝ) / (4 * (r + 1))) := by
        simp only [Dr]; field_simp
      have : 0 ≤ θ * ((r : ℝ) / (4 * (r + 1))) := by positivity
      linarith [le_abs_self D, hDr']
    have hexpω : θ * (N₀ : ℝ) + (1 - θ) * s ≤ 3 := by
      have h1 : θ * (N₀ : ℝ) = 1 / 2 := by simp only [θ]; field_simp
      have h2 : (1 - θ) * s ≤ s := by nlinarith
      have : s ≤ 5 / 2 := by simp only [s]; linarith
      linarith
    have hpow1 : (W : ℝ) ^ (θ * (-Dr + (r : ℝ) / (4 * (r + 1))) +
        (1 - θ) * ((r : ℝ) / (4 * (r + 1)))) ≤ (W : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_exponent_le hW1 hexpW
    have hpow2 : ω ^ (θ * (N₀ : ℝ) + (1 - θ) * s) ≤ ω ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]; push_cast
      exact Real.rpow_le_rpow_of_exponent_le hω1 hexpω
    have hc0 : 0 ≤ R ^ θ * (Cc + B₀) ^ (1 - θ) :=
      mul_nonneg (Real.rpow_nonneg hR _) (Real.rpow_nonneg (add_nonneg hCc hB₀) _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow1 hc0) hpow2 (Real.rpow_nonneg hω0.le _)
      (mul_nonneg hc0 (Real.rpow_nonneg hW0.le _))
  · obtain ⟨B, hB, h⟩ := hgb K
    refine ⟨B, hB, fun E hE k => ?_⟩
    simp only [Bool.false_eq_true, if_false]
    refine le_trans (h E hE k) ?_
    have hω1 := FT1c_one_le_om k
    have h3 : FT1c_om k ^ (2 + (r : ℝ) / (4 * (r + 1))) ≤ FT1c_om k ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]; push_cast
      exact Real.rpow_le_rpow_of_exponent_le hω1 (by linarith)
    gcongr

/-! ## Uniform constants over the edges -/

/-- The per-edge hypotheses `FT1c_EdgeOK` with constants uniform over the finitely many edges:
the hypotheses of `FT1c_graph`. -/
private theorem FT1c_uniform {ι : Type*} [Fintype ι] (A : Set ℝ) (f : ℝ → ℕ → ι → (Fin d → ℝ) → ℂ)
    (g : ℝ → ι → (Fin d → ℝ) → ℂ) (α : ι → ℝ) (γ : ι → ℕ) (dot : ι → Bool)
    (h : ∀ c, FT1c_EdgeOK A (fun x W => f x W c) (fun x => g x c) (α c) (γ c) (dot c)) :
    (∃ B β W₀ : ℝ, 0 ≤ β ∧ ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ A, ∀ c, Measurable (f x W c) ∧
      (∀ p (z : Fin d → ℤ), f x W c (p + fun i => 2 * Real.pi * z i) = f x W c p) ∧
      ∀ p ∈ cubePi d, ‖f x W c p‖ ≤ B * (W : ℝ) ^ β * FT1c_om ((W : ℝ) • p) ^ γ c) ∧
    (∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ x ∈ A, ∀ c, ∀ p ∈ cubePi d,
      ‖f x W c p - (((W : ℝ) ^ (-α c) : ℝ) : ℂ) * g x c ((W : ℝ) • p)‖ ≤
        C * (W : ℝ) ^ (-D) * FT1c_om ((W : ℝ) • p) ^ γ c) ∧
    (∀ x ∈ A, ∀ c, Measurable (g x c)) ∧
    (∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ A, ∀ c r,
      ‖g x c r‖ ≤ B * FT1c_om r ^ γ c * (if dot c then 1 else ((1 + ‖r‖) ^ K)⁻¹)) := by
  refine ⟨?_, fun D => ?_, fun x hx c => (h c).2.2.1 x hx, fun K => ?_⟩
  · choose B β W₀ hβ hc using fun c => (h c).1
    refine ⟨∑ c, |B c|, ∑ c, β c, max (∑ c, |W₀ c|) 1,
      Finset.sum_nonneg fun c _ => hβ c, fun W hW x hx c => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
    have hWc : W₀ c ≤ W := le_trans (le_trans (le_abs_self _) (Finset.single_le_sum
      (f := fun c => |W₀ c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c)))
      (le_trans (le_max_left _ _) hW)
    obtain ⟨hm, hp, hb⟩ := hc c W hWc x hx
    refine ⟨hm, hp, fun p hp' => le_trans (hb p hp') ?_⟩
    have hω : 0 ≤ FT1c_om ((W : ℝ) • p) ^ γ c := pow_nonneg (FT1c_om_pos _).le _
    have h1 : B c * (W : ℝ) ^ β c ≤ (∑ c, |B c|) * (W : ℝ) ^ (∑ c, β c) := by
      have hWβ : (W : ℝ) ^ β c ≤ (W : ℝ) ^ (∑ c, β c) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (Finset.single_le_sum (f := β)
          (fun c _ => hβ c) (Finset.mem_univ c))
      have hB : |B c| ≤ ∑ c, |B c| := Finset.single_le_sum (f := fun c => |B c|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
      calc B c * (W : ℝ) ^ β c ≤ |B c| * (W : ℝ) ^ β c :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ (∑ c, |B c|) * (W : ℝ) ^ (∑ c, β c) :=
            mul_le_mul hB hWβ (Real.rpow_nonneg (by linarith) _)
              (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact mul_le_mul_of_nonneg_right h1 hω
  · choose C W₀ hc using fun c => (h c).2.1 D
    refine ⟨∑ c, |C c|, ∑ c, |W₀ c|, fun W hW x hx c p hp => ?_⟩
    have hWc : W₀ c ≤ W := le_trans (le_trans (le_abs_self _) (Finset.single_le_sum
      (f := fun c => |W₀ c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))) hW
    refine le_trans (hc c W hWc x hx p hp) ?_
    have hω : 0 ≤ FT1c_om ((W : ℝ) • p) ^ γ c := pow_nonneg (FT1c_om_pos _).le _
    have hWD : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hC : C c ≤ ∑ c, |C c| := le_trans (le_abs_self _) (Finset.single_le_sum
      (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hWD) hω
  · choose B hB hc using fun c => (h c).2.2.2 K
    refine ⟨∑ c, B c, Finset.sum_nonneg fun c _ => hB c, fun x hx c r => ?_⟩
    refine le_trans (hc c x hx r) ?_
    have hω : 0 ≤ FT1c_om r ^ γ c := pow_nonneg (FT1c_om_pos _).le _
    have hif : 0 ≤ (if dot c = true then (1 : ℝ) else ((1 + ‖r‖) ^ K)⁻¹) := by
      split_ifs <;> positivity
    have hBc : B c ≤ ∑ c, B c := Finset.single_le_sum (f := B) (fun c _ => hB c)
      (Finset.mem_univ c)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBc hω) hif

/-! ## The `W`-free symbols of the component kinds -/

/-- The `W`-free symbol of a component kind ([I, (7.30)]): `ψ`, `w ψ/(1 − w ψ)` with `w = m²` or
`m̄²`, `ψ_Θ^{|o|+1} Π_{l ∈ o} Φ̊_l` for a `Θ` edge with label `o`, `1` for a dotted edge and `0`
for every other kind. -/
private def FT1c_gK (P : Profile d) (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ) (E : ℝ) :
    Kind → (Fin d → ℝ) → ℂ
  | .waved .s => FT1c_psi P
  | .waved .plus => FT1c_gpm P (mE E ^ 2)
  | .waved .minus => FT1c_gpm P (conj (mE E) ^ 2)
  | .theta o => fun k => FT1c_gth P k ^ (o.length + 1) * (o.map fun l => Φ l E k).prod
  | .dot => fun _ => 1
  | _ => fun _ => 0

/-- The scaling exponent `α` of a component kind: `Σ_{l ∈ o} (l − 2)d/2` for a `Θ` edge with label
`o`, `0` otherwise. -/
private def FT1c_alpha (d : ℕ) : Kind → ℝ
  | .theta o => (o.map fun l : ℕ => ((l : ℝ) - 2) * d / 2).sum
  | _ => 0

/-- The weight exponent `γ` of a component kind: `3` for a `Θ` edge, `0` otherwise. -/
private def FT1c_gam : Kind → ℕ
  | .theta _ => 3
  | _ => 0

/-- The external momenta `−p` at `x = 0`, `p` at `y = 1`, `0` at the internal atoms, as `a_v p`. -/
private def FT1c_aext {n : ℕ} : Atom 2 n → ℝ := Sum.elim ![-1, 1] 0

private theorem FT1c_extP_eq {n : ℕ} (p : Fin d → ℝ) :
    (FT1b.extP p : Atom 2 n → Fin d → ℝ) = fun v => FT1c_aext v • p := by
  funext v
  rcases v with i | i
  · fin_cases i <;> simp [FT1b.extP, FT1c_aext]
  · simp [FT1b.extP, FT1c_aext]

private theorem FT1c_aext_sum {n : ℕ} : ∑ v : Atom 2 n, FT1c_aext v = 0 := by
  rw [Fintype.sum_sum_type]
  simp [FT1c_aext, Fin.sum_univ_two]

private theorem FT1c_aext_le {n : ℕ} (v : Atom 2 n) : |FT1c_aext v| ≤ 1 := by
  rcases v with i | i
  · fin_cases i <;> simp [FT1c_aext]
  · simp [FT1c_aext]

/-- The `W`-free form `c_G(m(E)) Ψ_G(E, k)` of a momentum graph. -/
private def FT1c_PsiG (P : Profile d) (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ) (G : FT1b.MomGraph) (E : ℝ)
    (k : Fin d → ℝ) : ℂ :=
  G.Γ.coeff.eval (mE E) *
    FT1c_Psi (FT1b.ends G.Γ) G.T₁ FT1c_aext (fun c => FT1c_gK P Φ E G.Γ.comps[c].kind) k

/-- The dotted kind, as a boolean. -/
private def FT1c_isDot : Kind → Bool
  | .dot => true
  | _ => false

private theorem FT1c_isDot_iff (k : Kind) : FT1c_isDot k = true ↔ k = .dot := by
  cases k <;> simp [FT1c_isDot]

/-- The hypotheses of `FT1c_graph` for one component kind of a graph of `Σ_l` (waved, dotted, or a
`Θ` edge whose label entries have `W`-free forms). -/
private theorem FT1c_edge_kind (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ)
    (k : Kind) (hk : (∃ w, k = .waved w) ∨ k = .dot ∨ ∃ o, k = .theta o ∧ labelOK N o = true ∧
      ∀ l ∈ o, FT1c_LabGood P Sig κ l (Φ l)) :
    FT1c_EdgeOK {E : ℝ | |E| < 2 - κ}
      (fun E W => FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) k)
      (fun E => FT1c_gK P Φ E k) (FT1c_alpha d k) (FT1c_gam k) (FT1c_isDot k) := by
  rcases hk with ⟨w, rfl⟩ | rfl | ⟨o, rfl, ho, hΦ⟩
  · cases w
    · exact FT1c_edge_s (by omega) P hκ
    · exact FT1c_edge_pm (by omega) P hκ true
    · exact FT1c_edge_pm (by omega) P hκ false
  · exact FT1c_edge_dot _
  · exact FT1c_edge_theta hd P Sig N hSig hκ o ho Φ hΦ

private theorem FT1c_alpha_eq (k : Kind) (hk : (∃ w, k = .waved w) ∨ k = .dot ∨ ∃ o, k = .theta o) :
    FT1c_alpha d k = (d : ℝ) / 2 * ((k.ord : ℝ) - 2) := by
  rcases hk with ⟨w, rfl⟩ | rfl | ⟨o, rfl⟩
  · simp [FT1c_alpha, Kind.ord]
  · simp [FT1c_alpha, Kind.ord]
  · simp only [FT1c_alpha, Kind.ord]
    push_cast
    induction o with
    | nil => simp
    | cons l o ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      push_cast
      ring

/-- **The scaling count** ([I, (2.12)] with the loop count of the tree): for a graph of `Σ_l` without
`×`-dotted edge, `Σ_c α_c + d L = (l − 2)d/2`, `L` the number of loop momenta. -/
private theorem FT1c_exponent {n l : ℕ} (Γ : Graph 2 n) (T₁ : List (Fin Γ.comps.length))
    (hT₁ : TreeEdges (T₁.map (FT1b.ends Γ))) (hord : Γ.ord = l)
    (hk : ∀ c : Fin Γ.comps.length, (∃ w, Γ.comps[c].kind = .waved w) ∨ Γ.comps[c].kind = .dot ∨
      ∃ o, Γ.comps[c].kind = .theta o) :
    ∑ c : Fin Γ.comps.length, FT1c_alpha d Γ.comps[c].kind +
        ((d * Fintype.card {c // c ∉ T₁} : ℕ) : ℝ) = ((l : ℝ) - 2) * d / 2 := by
  have hnd := FT1a_nodup hT₁
  have hcard1 := FT1a_card_tree hnd
  have hlen := hT₁.1
  rw [List.length_map] at hlen
  have hV : Fintype.card (Atom 2 n) = 2 + n := by simp [Atom]
  rw [hV] at hlen
  have hcard : Fintype.card {c // c ∉ T₁} + Fintype.card {c // c ∈ T₁} = Γ.comps.length := by
    rw [add_comm, Fintype.card_subtype_compl, Fintype.card_fin]
    have : Fintype.card {c // c ∈ T₁} ≤ Fintype.card (Fin Γ.comps.length) :=
      Fintype.card_subtype_le _
    rw [Fintype.card_fin] at this
    omega
  have hα : ∑ c : Fin Γ.comps.length, FT1c_alpha d Γ.comps[c].kind =
      ∑ c : Fin Γ.comps.length, (d : ℝ) / 2 * ((Γ.comps[c].kind.ord : ℝ) - 2) :=
    Finset.sum_congr rfl fun c _ => FT1c_alpha_eq _ (hk c)
  have key : ∀ F : Comp (Atom 2 n) → ℝ, ∑ c : Fin Γ.comps.length, F Γ.comps[c] =
      (Γ.comps.map F).sum := fun F => by
    rw [← Fin.sum_ofFn]
    simp only [Fin.getElem_fin]
    rw [List.ofFn_getElem_eq_map]
  have hS : ∑ c : Fin Γ.comps.length, ((Γ.comps[c].kind.ord : ℤ) : ℝ) = (l : ℝ) + 2 * n := by
    rw [key (fun c => ((c.kind.ord : ℤ) : ℝ))]
    have h1 : (Γ.comps.map fun c => ((c.kind.ord : ℤ) : ℝ)).sum =
        (((Γ.comps.map fun c => c.kind.ord).sum : ℤ) : ℝ) := by
      rw [Int.cast_list_sum, List.map_map]; rfl
    rw [h1]
    have h2 : (Γ.comps.map fun c => c.kind.ord).sum = (l : ℤ) + 2 * n := by
      unfold Graph.ord at hord; omega
    rw [h2]; push_cast; ring
  have hL : ((Fintype.card {c // c ∉ T₁} : ℕ) : ℝ) = Γ.comps.length - n - 1 := by
    have : Fintype.card {c // c ∉ T₁} = Γ.comps.length - n - 1 := by omega
    rw [this]
    have h3 : n + 1 ≤ Γ.comps.length := by omega
    push_cast [Nat.sub_sub, Nat.cast_sub h3]
    ring
  rw [hα, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, hS]
  push_cast
  rw [hL]
  simp only [nsmul_eq_mul]
  ring

/-- The components of a graph of `Σ_l` are waved, dotted, `×`-dotted, or `Θ` edges with labels of
entries even in `[4, l − 1]`. -/
private theorem FT1c_kinds {n l : ℕ} (Γ : Graph 2 n) (hKd : Γ.comps.all (Comp.isDetKind (l - 1)) = true)
    (c : Fin Γ.comps.length) :
    (∃ w, Γ.comps[c].kind = .waved w) ∨ Γ.comps[c].kind = .dot ∨ Γ.comps[c].kind = .xdot ∨
      ∃ o, Γ.comps[c].kind = .theta o ∧ labelOK (l - 1) o = true := by
  have h := List.all_eq_true.1 hKd Γ.comps[c] (List.getElem_mem _)
  simp only [Comp.isDetKind, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  revert h
  generalize Γ.comps[c].kind = k
  intro h
  cases k with
  | waved w => exact Or.inl ⟨w, rfl⟩
  | dot => exact Or.inr (Or.inl rfl)
  | xdot => exact Or.inr (Or.inr (Or.inl rfl))
  | theta o => exact Or.inr (Or.inr (Or.inr ⟨o, rfl, h⟩))
  | _ => simp at h

private theorem FT1c_labelOK_mono {N N' : ℕ} (h : N ≤ N') {o : List ℕ} (ho : labelOK N o = true) :
    labelOK N' o = true := by
  unfold labelOK at *
  rw [List.all_eq_true] at *
  intro j hj
  have := ho j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this ⊢
  exact ⟨⟨this.1.1, le_trans this.1.2 h⟩, this.2⟩

/-- **The scaling of the momentum form of one graph of `Σ_l`** ([I, (7.29)] → [I, (7.30)] with
`q = k/W`): for a momentum form `G` of a graph of `Σ_l` (`FT1b.MomGraph.Spec`) whose labelled `Θ`
edges read `Σ̊^∞` of orders with `W`-free forms `Φ̊`, there is `δ > 0` with
`c_G(m) M_G(p) = W^{-(l-2)d/2} c_G(m) Ψ_G(E, W p) + O(W^{-D})` for every `D`, uniformly in
`|E| < 2 − κ` and `‖p‖ ≤ δ`; `Ψ_G(E, ·)` is measurable. -/
private theorem FT1c_momGraph (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (l : ℕ) (hlN : l - 1 ≤ N)
    (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ)
    (hΦ : ∀ l', 4 ≤ l' → l' ≤ l - 1 → Even l' → FT1c_LabGood P Sig κ l' (Φ l'))
    (g : Σ n : ℕ, Graph 2 n) (G : FT1b.MomGraph) (hG : G.Spec l g) :
    (∀ E : ℝ, |E| < 2 - κ → Measurable (FT1c_PsiG P Φ G E)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
        ∀ p : Fin d → ℝ, ‖p‖ ≤ δ →
          ‖G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p -
              (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) *
                FT1c_PsiG P Φ G E ((W : ℝ) • p)‖ ≤ C * (W : ℝ) ^ (-D) := by
  obtain ⟨hsh, -, hT₁, hT₂, hcomm⟩ := hG
  obtain ⟨⟨Cn, -, hA⟩, hKd, hord, -⟩ := hsh _ (List.mem_singleton_self _)
  have hKd : G.Γ.comps.all (Comp.isDetKind (l - 1)) = true := hKd
  have hord : G.Γ.ord = l := hord
  have hA : G.Γ.DotsAcyclic := hA
  by_cases hx : ∃ c : Fin G.Γ.comps.length, G.Γ.comps[c].kind = .xdot
  · -- a `×`-dotted edge: both sides vanish
    obtain ⟨c₀, hc₀⟩ := hx
    have hsym0 : ∀ W E p, G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p = 0 := by
      intro W E p
      simp only [FT1b.MomGraph.sym, FT1b.momInt]
      have : ∀ q, ∏ c, FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E)
          G.Γ.comps[c].kind (FT1a.edgeMom (FT1b.ends G.Γ) G.T₁ (FT1b.extP p) q c) = 0 :=
        fun q => Finset.prod_eq_zero (Finset.mem_univ c₀) (by rw [hc₀]; rfl)
      simp only [this, MeasureTheory.integral_zero, mul_zero]
    have hPsi0 : ∀ E k, FT1c_PsiG P Φ G E k = 0 := by
      intro E k
      simp only [FT1c_PsiG, FT1c_Psi]
      have : ∀ k', ∏ c, FT1c_gK P Φ E G.Γ.comps[c].kind
          (FT1a.edgeMom (FT1b.ends G.Γ) G.T₁ (fun v => FT1c_aext v • k) k' c) = 0 :=
        fun k' => Finset.prod_eq_zero (Finset.mem_univ c₀) (by rw [hc₀]; rfl)
      simp only [this, MeasureTheory.integral_zero, mul_zero]
    refine ⟨fun E _ => ?_, 1, one_pos, fun D => ⟨0, 0, fun W _ E _ p _ => ?_⟩⟩
    · have : FT1c_PsiG P Φ G E = fun _ => 0 := funext (hPsi0 E)
      rw [this]; exact measurable_const
    · rw [hsym0, hPsi0]; simp
  -- no `×`-dotted edge
  have hcomm' := hcomm.resolve_right hx
  push Not at hx
  have hk : ∀ c : Fin G.Γ.comps.length, (∃ w, G.Γ.comps[c].kind = .waved w) ∨
      G.Γ.comps[c].kind = .dot ∨ ∃ o, G.Γ.comps[c].kind = .theta o ∧ labelOK N o = true ∧
        ∀ l' ∈ o, FT1c_LabGood P Sig κ l' (Φ l') := by
    intro c
    rcases FT1c_kinds G.Γ hKd c with h | h | h | ⟨o, ho, hlo⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h (hx c)
    · refine Or.inr (Or.inr ⟨o, ho, FT1c_labelOK_mono hlN hlo, fun l' hl' => ?_⟩)
      have h := List.all_eq_true.1 hlo l' hl'
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact hΦ l' h.1.1 h.1.2 (Nat.even_iff.2 h.2)
  set A := {E : ℝ | |E| < 2 - κ}
  set f : ℝ → ℕ → Fin G.Γ.comps.length → (Fin d → ℝ) → ℂ := fun E W c =>
    FT1b.kindSym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) G.Γ.comps[c].kind
  set gg : ℝ → Fin G.Γ.comps.length → (Fin d → ℝ) → ℂ := fun E c =>
    FT1c_gK P Φ E G.Γ.comps[c].kind
  have hedge : ∀ c, FT1c_EdgeOK A (fun x W => f x W c) (fun x => gg x c)
      (FT1c_alpha d G.Γ.comps[c].kind) (FT1c_gam G.Γ.comps[c].kind)
      (FT1c_isDot G.Γ.comps[c].kind) := fun c =>
    FT1c_edge_kind hd P Sig N hSig hκ Φ _ (hk c)
  obtain ⟨hf, hfc, hgm, hgb⟩ := FT1c_uniform A f gg (fun c => FT1c_alpha d G.Γ.comps[c].kind)
    (fun c => FT1c_gam G.Γ.comps[c].kind) (fun c => FT1c_isDot G.Γ.comps[c].kind) hedge
  have hcut : ∀ c, FT1c_isDot G.Γ.comps[c].kind = true → ∃ S : Atom 2 G.n → Prop,
      S (FT1b.ends G.Γ c).2 ∧ ¬ S (FT1b.ends G.Γ c).1 ∧
        ∀ c', FT1c_isDot G.Γ.comps[c'].kind = true → c' ≠ c →
          (S (FT1b.ends G.Γ c').2 ↔ S (FT1b.ends G.Γ c').1) := by
    intro c hc
    obtain ⟨S, h1, h2, h3⟩ := FT1c_cutSet G.Γ hA c ((FT1c_isDot_iff _).1 hc)
    exact ⟨S, h1, h2, fun c' hc' hne => h3 c' ((FT1c_isDot_iff _).1 hc') hne⟩
  have hγ : ∀ c : Fin G.Γ.comps.length, 2 * FT1c_gam G.Γ.comps[c].kind < d := fun c => by
    generalize G.Γ.comps[c].kind = k
    cases k <;> simp only [FT1c_gam] <;> omega
  have hγ0 : ∀ c : Fin G.Γ.comps.length, c ∈ G.T₁ → c ∈ G.T₂ →
      FT1c_gam G.Γ.comps[c].kind = 0 := by
    intro c h1 h2
    rcases hcomm' c h1 h2 with ⟨w, hw⟩ | hw <;> rw [hw] <;> rfl
  have hα : ∀ c : Fin G.Γ.comps.length, 0 ≤ FT1c_alpha d G.Γ.comps[c].kind := by
    intro c
    rcases hk c with ⟨w, hw⟩ | hw | ⟨o, hw, ho, -⟩
    · rw [hw]; simp [FT1c_alpha]
    · rw [hw]; simp [FT1c_alpha]
    · rw [hw]
      refine List.sum_nonneg fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      have h := List.all_eq_true.1 ho j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have : (4 : ℝ) ≤ j := by exact_mod_cast h.1.1
      have : (0 : ℝ) ≤ ((j : ℝ) - 2) * d := mul_nonneg (by linarith) (Nat.cast_nonneg _)
      linarith
  have hmain := FT1c_graph hT₁ hT₂
    (fun c : Fin G.Γ.comps.length => FT1c_isDot G.Γ.comps[c].kind = true) hcut
    FT1c_aext FT1c_aext_sum FT1c_aext_le (fun c => FT1c_gam G.Γ.comps[c].kind) hγ hγ0
    (fun c => FT1c_alpha d G.Γ.comps[c].kind) hα A f gg hf hfc hgm hgb
  have hexp := FT1c_exponent (d := d) G.Γ G.T₁ hT₁ hord fun c => by
    rcases hk c with h | h | ⟨o, h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨o, h⟩)
  obtain ⟨Cc, hCc0, hCc⟩ := ValZ_coeff_bound hκ G.Γ.coeff
  refine ⟨fun E hE => ?_, ?_⟩
  · show Measurable fun k => G.Γ.coeff.eval (mE E) *
      FT1c_Psi (FT1b.ends G.Γ) G.T₁ FT1c_aext (fun c => FT1c_gK P Φ E G.Γ.comps[c].kind) k
    exact measurable_const.mul (FT1c_measurable_Psi _ _ _ _ fun c => hgm E hE c)
  refine ⟨FT1c_eta (Fin G.Γ.comps.length) / (2 * Fintype.card (Atom 2 G.n) + 2),
    div_pos (FT1c_eta_pos _) (by positivity), fun D => ?_⟩
  obtain ⟨C, W₀, hC⟩ := hmain D
  refine ⟨Cc * C, W₀, fun W hW E hE p hp => ?_⟩
  have h := hC W hW E hE p hp
  rw [hexp] at h
  have hsym : G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p =
      G.Γ.coeff.eval (mE E) * (((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ G.T₁}))⁻¹ *
        ∫ q in Set.univ.pi (fun _ : {c // c ∉ G.T₁} => cubePi d),
          ∏ c, f E W c (FT1a.edgeMom (FT1b.ends G.Γ) G.T₁ (fun v => FT1c_aext v • p) q c)) := by
    simp only [FT1b.MomGraph.sym, FT1b.momInt, FT1c_extP_eq, f]
  rw [hsym]
  simp only [FT1c_PsiG]
  rw [show G.Γ.coeff.eval (mE E) * (((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ G.T₁}))⁻¹ *
        ∫ q in Set.univ.pi (fun _ : {c // c ∉ G.T₁} => cubePi d),
          ∏ c, f E W c (FT1a.edgeMom (FT1b.ends G.Γ) G.T₁ (fun v => FT1c_aext v • p) q c)) -
      (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * (G.Γ.coeff.eval (mE E) *
        FT1c_Psi (FT1b.ends G.Γ) G.T₁ FT1c_aext (fun c => gg E c) ((W : ℝ) • p)) =
      G.Γ.coeff.eval (mE E) * ((((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ G.T₁}))⁻¹ *
        ∫ q in Set.univ.pi (fun _ : {c // c ∉ G.T₁} => cubePi d),
          ∏ c, f E W c (FT1a.edgeMom (FT1b.ends G.Γ) G.T₁ (fun v => FT1c_aext v • p) q c)) -
      (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) *
        FT1c_Psi (FT1b.ends G.Γ) G.T₁ FT1c_aext (fun c => gg E c) ((W : ℝ) • p)) by ring]
  rw [norm_mul]
  exact le_trans (mul_le_mul (hCc E hE) h (norm_nonneg _) hCc0) (le_of_eq (by ring))

/-- The momentum forms of a formal sum: the sum of the `W`-free forms of its graphs. -/
private theorem FT1c_listSum (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (l : ℕ) (hlN : l - 1 ≤ N)
    (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ)
    (hΦ : ∀ l', 4 ≤ l' → l' ≤ l - 1 → Even l' → FT1c_LabGood P Sig κ l' (Φ l'))
    (L : Expansion 2) (M : List FT1b.MomGraph) (hLM : List.Forall₂ (FT1b.MomGraph.Spec l) L M) :
    (∀ E : ℝ, |E| < 2 - κ → Measurable fun k => (M.map fun G => FT1c_PsiG P Φ G E k).sum) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
        ∀ p : Fin d → ℝ, ‖p‖ ≤ δ →
          ‖(M.map fun G => G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p).sum -
              (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) *
                (M.map fun G => FT1c_PsiG P Φ G E ((W : ℝ) • p)).sum‖ ≤ C * (W : ℝ) ^ (-D) := by
  induction hLM with
  | nil =>
    refine ⟨fun E _ => by simp only [List.map_nil, List.sum_nil]; exact measurable_const, 1,
      one_pos, fun D => ⟨0, 0, fun W _ E _ p _ => ?_⟩⟩
    simp
  | @cons g G L M hgG _ ih =>
    obtain ⟨hm1, δ₁, hδ₁, h1⟩ := FT1c_momGraph hd P Sig N hSig hκ l hlN Φ hΦ g G hgG
    obtain ⟨hm2, δ₂, hδ₂, h2⟩ := ih
    refine ⟨fun E hE => ?_, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun D => ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact (hm1 E hE).add (hm2 E hE)
    · obtain ⟨C₁, W₁, hC₁⟩ := h1 D
      obtain ⟨C₂, W₂, hC₂⟩ := h2 D
      refine ⟨C₁ + C₂, max W₁ W₂, fun W hW E hE p hp => ?_⟩
      have e1 := hC₁ W (le_trans (le_max_left _ _) hW) E hE p (le_trans hp (min_le_left _ _))
      have e2 := hC₂ W (le_trans (le_max_right _ _) hW) E hE p (le_trans hp (min_le_right _ _))
      simp only [List.map_cons, List.sum_cons]
      have : G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p +
            (M.map fun G => G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p).sum -
          (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * (FT1c_PsiG P Φ G E ((W : ℝ) • p) +
            (M.map fun G => FT1c_PsiG P Φ G E ((W : ℝ) • p)).sum) =
          (G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p -
            (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * FT1c_PsiG P Φ G E ((W : ℝ) • p)) +
          ((M.map fun G => G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p).sum -
            (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) *
              (M.map fun G => FT1c_PsiG P Φ G E ((W : ℝ) • p)).sum) := by ring
      rw [this]
      exact le_trans (norm_add_le _ _) (le_trans (add_le_add e1 e2) (le_of_eq (by ring)))

/-- **[I, (7.29)–(7.30)] with the scaling, for `Σ^{(r),∞}_l`**: for `l ≥ 4` with lower orders of the
shape of a self-energy and label forms `Φ̊` of the lower even orders, there are a `W`-free
`Ψ_l(E, ·)` (measurable) and `δ > 0` with
`R(E, W) = W^{-(l-2)d/2} Ψ_l(E, 0) + O(W^{-D})` and, for even `l`, the symbol of `Σ^{(r),∞}_l`
equal to `W^{-(l-2)d/2} Ψ_l(E, W p) + O(W^{-D})` for `‖p‖ ≤ δ`, for every `D`, uniformly in
`|E| < 2 − κ`. -/
private theorem FT1c_level (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ) (hl4 : 4 ≤ l)
    (hSigl : SelfEnergyShapesUpTo Sig (l - 1)) (hshl : SelfEnergyShape l (Sig l)) {κ : ℝ}
    (hκ : 0 < κ) (Φ : ℕ → ℝ → (Fin d → ℝ) → ℂ)
    (hΦ : ∀ l', 4 ≤ l' → l' ≤ l - 1 → Even l' → FT1c_LabGood P Sig κ l' (Φ l')) :
    ∃ Ψ : ℝ → (Fin d → ℝ) → ℂ, (∀ E : ℝ, |E| < 2 - κ → Measurable (Ψ E)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
        ‖ValZ.rowSum Sig P.ψ l E W - (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * Ψ E 0‖ ≤
            C * (W : ℝ) ^ (-D) ∧
          (Even l → ∀ p : Fin d → ℝ, ‖p‖ ≤ δ →
            ‖zdSeries (ValZ.sigR Sig (Sinf P.ψ W) W E l) p -
                (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * Ψ E ((W : ℝ) • p)‖ ≤
              C * (W : ℝ) ^ (-D)) := by
  obtain ⟨M, hM, W₁, hW₁⟩ := FT1b.rowSumFourier hd P l Sig hSigl hshl hκ
  obtain ⟨hmeas, δ, hδ, hcmp⟩ := FT1c_listSum hd P Sig (l - 1) hSigl hκ l le_rfl Φ hΦ (Sig l) (M l)
    (hM l (Or.inl rfl))
  refine ⟨fun E k => ((M l).map fun G => FT1c_PsiG P Φ G E k).sum, hmeas, δ, hδ, fun D => ?_⟩
  obtain ⟨C, W₂, hC⟩ := hcmp D
  refine ⟨C, max W₁ W₂, fun W hW E hE => ⟨?_, fun hle p hp => ?_⟩⟩
  · obtain ⟨hR, -⟩ := hW₁ W (le_trans (le_max_left _ _) hW) E hE
    rw [hR]
    have h := hC W (le_trans (le_max_right _ _) hW) E hE 0 (by rw [norm_zero]; exact hδ.le)
    rwa [smul_zero] at h
  · obtain ⟨-, hS⟩ := hW₁ W (le_trans (le_max_left _ _) hW) E hE
    have hsum := (hS l hl4 le_rfl hle p).tsum_eq
    have hz : zdSeries (ValZ.sigR Sig (Sinf P.ψ W) W E l) p =
        ((M l).map fun G => G.sym (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ E) W (mE E) p).sum := hsum
    rw [hz]
    exact hC W (le_trans (le_max_right _ _) hW) E hE p hp

/-- **The label forms** ([I, Def 8.2] on `ℤ^d` with the scaling): from the form `Ψ_l` of
`Σ^{(r),∞}_l`, `Φ̊_l(E, k) = Ψ_l(E, k) − Ψ_l(E, 0) ψ(k)` is a `W`-free form of the symbol of
`Σ̊^∞_l = Σ^{(r),∞}_l − [Σ_y Σ^{(r),∞}_l(0, y)] S_∞`. -/
private theorem FT1c_good (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) (l : ℕ) (hl4 : 4 ≤ l) (hlN : l ≤ N)
    (hle : Even l) (Ψ : ℝ → (Fin d → ℝ) → ℂ) (hΨm : ∀ E : ℝ, |E| < 2 - κ → Measurable (Ψ E))
    (δ : ℝ) (hδ : 0 < δ)
    (hΨ : ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
        ‖ValZ.rowSum Sig P.ψ l E W - (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * Ψ E 0‖ ≤
            C * (W : ℝ) ^ (-D) ∧
          (Even l → ∀ p : Fin d → ℝ, ‖p‖ ≤ δ →
            ‖zdSeries (ValZ.sigR Sig (Sinf P.ψ W) W E l) p -
                (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * Ψ E ((W : ℝ) • p)‖ ≤
              C * (W : ℝ) ^ (-D))) :
    FT1c_LabGood P Sig κ l (fun E k => Ψ E k - Ψ E 0 * FT1c_psi P k) := by
  refine ⟨fun E hE => (hΨm E hE).sub (measurable_const.mul (FT1c_measurable_psi P)), min δ 1,
    lt_min hδ one_pos, fun D => ?_⟩
  set a : ℝ := ((l : ℝ) - 2) * d / 2
  have ha : 1 ≤ a := by
    have : (4 : ℝ) ≤ l := by exact_mod_cast hl4
    have : (8 : ℝ) ≤ d := by exact_mod_cast hd
    have : (16 : ℝ) ≤ ((l : ℝ) - 2) * d := by nlinarith
    simp only [a]; linarith
  set D' := max D 0
  obtain ⟨C₁, W₁, hC₁⟩ := hΨ D'
  obtain ⟨C₂, W₂, -, hcmp⟩ := FT1b.symbolCompare P hκ ⌈D'⌉₊
  obtain ⟨W₃, hR⟩ := InfBound.sigRBound (by omega) P Sig N hSig hκ l hl4 hlN hle 1 one_pos
  obtain ⟨Cs, W₄, hs⟩ := Sinf_infKernel d P.ψ P.cψ ⟨P.cψ_pos, P.at_zero, P.le_max, P.symm⟩
  obtain ⟨c, b, W₅, -, -, hsym⟩ := FT1b.edgeSymbols (by omega) P hκ
  refine ⟨2 * |C₁| + (1 + |C₁|) * |C₂|, max (max (max W₁ W₂) (max W₃ W₄)) (max W₅ 1),
    fun W hW E hE p hp => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWa : (0 : ℝ) < (W : ℝ) ^ (-a) := Real.rpow_pos_of_pos hW0 _
  have hWD' : (W : ℝ) ^ (-D') ≤ (W : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by simp only [D']; linarith [le_max_left D 0])
  have hWD'1 : (W : ℝ) ^ (-D') ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by simp only [D']; linarith [le_max_right D 0])
  have hWD0 : 0 ≤ (W : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  obtain ⟨hRow, hZ⟩ := hC₁ W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hW)) E hE
  have hpδ : ‖p‖ ≤ δ := le_trans hp (min_le_left _ _)
  have hp1 : ‖p‖ ≤ 1 := le_trans hp (min_le_right _ _)
  have hpc : p ∈ cubePi d := by
    intro i _
    have h := le_trans (norm_le_pi_norm p i) hp1
    rw [Real.norm_eq_abs, abs_le] at h
    constructor <;> linarith [Real.two_le_pi]
  have hZp := hZ hle p hpδ
  have hsW := hs W (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hW))
  obtain ⟨-, hRs, hRsum⟩ := hR W (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hW)) E hE
  -- `ψ_{Σ̊}(p) = ψ_{Σ^{(r)}}(p) − R ŝ(p)`
  set R := ValZ.rowSum Sig P.ψ l E W
  set Z := zdSeries (ValZ.sigR Sig (Sinf P.ψ W) W E l) p
  set sh := zdSymbol (Sinf P.ψ W) p
  have hker : zdSeries (ValZ.sigKer Sig P.ψ E l W) p = Z - R * sh := by
    have hs1 : Summable fun x => ValZ.sigR Sig (Sinf P.ψ W) W E l x * zexp p x :=
      Summable.of_norm (by simpa [norm_mul, norm_zexp] using hRs)
    have hs2 : Summable fun x => ((Sinf P.ψ W x : ℝ) : ℂ) * zexp p x :=
      Summable.of_norm (by simpa [norm_mul, norm_zexp] using FT1b_summable_s hsW)
    unfold zdSeries
    simp_rw [ValZ.sigKer_of_tsum Sig P.ψ E l W hsW.sum_one, sub_mul, mul_assoc]
    rw [show (∑' y, ValZ.sigR Sig (Sinf P.ψ W) W E l y) = R from rfl]
    rw [hs1.tsum_sub (hs2.mul_left R), tsum_mul_left]
    rfl
  have hsh1 : ‖sh‖ ≤ 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := hsym W (le_trans (le_trans
      (le_max_left _ _) (le_max_right _ _)) hW) E hE
    exact (hb p).1
  have hshψ : ‖sh - FT1c_psi P ((W : ℝ) • p)‖ ≤ |C₂| * (W : ℝ) ^ (-D') := by
    rw [FT1c_psi_smul]
    exact le_trans (hcmp W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (le_max_left _ _) hW)) E hE p hpc).1 (FT1c_div_pow_le hW1 C₂ D')
  have hRabs : ‖R‖ ≤ 1 := by
    have h1 : ‖R‖ ≤ ∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ := norm_tsum_le_tsum_norm hRs
    have h2 : (W : ℝ) ^ (-a) * (W : ℝ) ^ (1 : ℝ) ≤ 1 := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
    exact le_trans h1 (le_trans hRsum h2)
  have hΨ0 : ‖(((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0‖ ≤ 1 + |C₁| := by
    have h1 : ‖(((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0‖ ≤ ‖R‖ +
        ‖R - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0‖ := by
      calc _ = ‖R - (R - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have h2 : C₁ * (W : ℝ) ^ (-D') ≤ |C₁| := by
      calc C₁ * (W : ℝ) ^ (-D') ≤ |C₁| * (W : ℝ) ^ (-D') :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hWD0
        _ ≤ |C₁| * 1 := mul_le_mul_of_nonneg_left hWD'1 (abs_nonneg _)
        _ = |C₁| := mul_one _
    linarith
  -- the comparison
  show ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p - (((W : ℝ) ^ (-a) : ℝ) : ℂ) *
    (Ψ E ((W : ℝ) • p) - Ψ E 0 * FT1c_psi P ((W : ℝ) • p))‖ ≤ _
  rw [hker]
  have hsplit : Z - R * sh - (((W : ℝ) ^ (-a) : ℝ) : ℂ) *
      (Ψ E ((W : ℝ) • p) - Ψ E 0 * FT1c_psi P ((W : ℝ) • p)) =
      (Z - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E ((W : ℝ) • p)) -
        (R - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0) * sh -
          ((((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0) * (sh - FT1c_psi P ((W : ℝ) • p)) := by ring
  rw [hsplit]
  have e1 : ‖Z - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E ((W : ℝ) • p)‖ ≤ |C₁| * (W : ℝ) ^ (-D) :=
    le_trans hZp (le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) hWD0)
      (mul_le_mul_of_nonneg_left hWD' (abs_nonneg _)))
  have e2 : ‖(R - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0) * sh‖ ≤ |C₁| * (W : ℝ) ^ (-D) := by
    rw [norm_mul]
    calc ‖R - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0‖ * ‖sh‖ ≤ (|C₁| * (W : ℝ) ^ (-D)) * 1 :=
          mul_le_mul (le_trans hRow (le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) hWD0)
            (mul_le_mul_of_nonneg_left hWD' (abs_nonneg _)))) hsh1 (norm_nonneg _)
            (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hW0.le _))
      _ = |C₁| * (W : ℝ) ^ (-D) := mul_one _
  have e3 : ‖((((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0) * (sh - FT1c_psi P ((W : ℝ) • p))‖ ≤
      (1 + |C₁|) * |C₂| * (W : ℝ) ^ (-D) := by
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hΨ0 (le_trans hshψ (mul_le_mul_of_nonneg_left hWD' (abs_nonneg _)))
      (norm_nonneg _) (by positivity)
  calc ‖(Z - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E ((W : ℝ) • p)) -
        (R - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0) * sh -
          ((((W : ℝ) ^ (-a) : ℝ) : ℂ) * Ψ E 0) * (sh - FT1c_psi P ((W : ℝ) • p))‖
      ≤ |C₁| * (W : ℝ) ^ (-D) + |C₁| * (W : ℝ) ^ (-D) + (1 + |C₁|) * |C₂| * (W : ℝ) ^ (-D) :=
        le_trans (norm_sub_le _ _) (add_le_add (le_trans (norm_sub_le _ _) (add_le_add e1 e2)) e3)
    _ = (2 * |C₁| + (1 + |C₁|) * |C₂|) * (W : ℝ) ^ (-D) := by ring

/-- Every even order `4 ≤ l ≤ N` whose lower orders have the shape of a self-energy has a `W`-free
label form (induction on `l`; the labels of `Σ_l` have entries below `l`). -/
private theorem FT1c_allGood (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) :
    ∀ l, 4 ≤ l → l ≤ N → Even l → ∃ Φ, FT1c_LabGood P Sig κ l Φ := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    intro hl4 hlN hle
    classical
    set Φf : ℕ → ℝ → (Fin d → ℝ) → ℂ := fun l' =>
      if h : 4 ≤ l' ∧ l' < l ∧ Even l' then Classical.choose (ih l' h.2.1 h.1 (by omega) h.2.2)
      else 0
    have hΦ : ∀ l', 4 ≤ l' → l' ≤ l - 1 → Even l' → FT1c_LabGood P Sig κ l' (Φf l') := by
      intro l' h4 h' he
      have h : 4 ≤ l' ∧ l' < l ∧ Even l' := ⟨h4, by omega, he⟩
      simp only [Φf, dif_pos h]
      exact Classical.choose_spec (ih l' h.2.1 h.1 (by omega) h.2.2)
    have hSigl : SelfEnergyShapesUpTo Sig (l - 1) := fun k h4 hk he => hSig k h4 (by omega) he
    obtain ⟨Ψ, hΨm, δ, hδ, hΨ⟩ := FT1c_level hd P Sig l hl4 hSigl (hSig l hl4 hlN hle) hκ Φf hΦ
    exact ⟨_, FT1c_good hd P Sig N hSig hκ l hl4 hlN hle Ψ hΨm δ hδ hΨ⟩

/-- **[I, (8.8)] for one `κ`**: `R(E, W) = W^{-(n-2)d/2} 𝔖_κ(E) + O(W^{-D})` for every `D`, uniformly
in `|E| < 2 − κ`, with `𝔖_κ` independent of `W`. -/
private theorem FT1c_expand (hd : 8 ≤ d) (P : Profile d) (n : ℕ) (Sig : ℕ → Expansion 2) (hn : 4 ≤ n)
    (hSig : SelfEnergyShapesUpTo Sig (n - 1)) (hsh : SelfEnergyShape n (Sig n)) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ 𝔖κ : ℝ → ℂ, ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      ‖ValZ.rowSum Sig P.ψ n E W - (((W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * 𝔖κ E‖ ≤
        C * (W : ℝ) ^ (-D) := by
  classical
  have hG := FT1c_allGood hd P Sig (n - 1) hSig hκ
  set Φf : ℕ → ℝ → (Fin d → ℝ) → ℂ := fun l' =>
    if h : 4 ≤ l' ∧ l' ≤ n - 1 ∧ Even l' then Classical.choose (hG l' h.1 h.2.1 h.2.2) else 0
  have hΦ : ∀ l', 4 ≤ l' → l' ≤ n - 1 → Even l' → FT1c_LabGood P Sig κ l' (Φf l') := by
    intro l' h4 h' he
    have h : 4 ≤ l' ∧ l' ≤ n - 1 ∧ Even l' := ⟨h4, h', he⟩
    simp only [Φf, dif_pos h]
    exact Classical.choose_spec (hG l' h.1 h.2.1 h.2.2)
  obtain ⟨Ψ, -, δ, -, hΨ⟩ := FT1c_level hd P Sig n hn hSig hsh hκ Φf hΦ
  refine ⟨fun E => Ψ E 0, fun D => ?_⟩
  obtain ⟨C, W₀, h⟩ := hΨ D
  exact ⟨C, W₀, fun W hW E hE => (h W hW E hE).1⟩

/-- `W^a R(E, W) → 𝔖_κ(E)` along `W → ∞` under the expansion of `FT1c_expand`. -/
private theorem FT1c_tendsto {a : ℝ} {R : ℕ → ℂ} {S : ℂ}
    (h : ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ‖R W - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * S‖ ≤
      C * (W : ℝ) ^ (-(a + 1))) :
    Tendsto (fun W : ℕ => (((W : ℝ) ^ a : ℝ) : ℂ) * R W) atTop (𝓝 S) := by
  obtain ⟨C, W₀, hC⟩ := h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat |C|)
  filter_upwards [eventually_ge_atTop (max ⌈W₀⌉₊ 1)] with W hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWW₀ : W₀ ≤ W := le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) hW)
  have hWa : 0 < (W : ℝ) ^ a := Real.rpow_pos_of_pos hW0 _
  have hid : (((W : ℝ) ^ a : ℝ) : ℂ) * R W - S =
      (((W : ℝ) ^ a : ℝ) : ℂ) * (R W - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * S) := by
    rw [mul_sub, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hW0, add_neg_cancel,
      Real.rpow_zero, Complex.ofReal_one, one_mul]
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWa]
  calc (W : ℝ) ^ a * ‖R W - (((W : ℝ) ^ (-a) : ℝ) : ℂ) * S‖
      ≤ (W : ℝ) ^ a * (|C| * (W : ℝ) ^ (-(a + 1))) :=
        mul_le_mul_of_nonneg_left (le_trans (hC W hWW₀)
          (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hW0.le _))) hWa.le
    _ = |C| / W := by
        rw [mul_left_comm, ← Real.rpow_add hW0, show a + -(a + 1) = -1 by ring,
          Real.rpow_neg_one, div_eq_mul_inv]

/-- **[I, (8.8)]**: for `d ≥ 8`, a profile `P`, lower orders `4 ≤ k ≤ n − 1` of the shape of a
self-energy and `Σ_n` of the shape of an `n`-th order self-energy, there is `𝔖_n : ℝ → ℂ`,
independent of `W`, with `|R(E, W) − W^{-(n-2)d/2} 𝔖_n(E)| ≤ C W^{-D}` for every `κ > 0` and `D`,
`W ≥ W₀(κ, D)` and `|E| < 2 − κ`, where `R(E, W) = Σ_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)` (`ValZ.rowSum`).
`𝔖_n(E) = lim_{W → ∞} W^{(n-2)d/2} R(E, W)`; on `|E| < 2 − κ` it is the `W`-free momentum integral
of [I, (7.30)] at `p = 0`. -/
theorem FT1c.rowSumExpand (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (n : ℕ) (Sig : ℕ → Expansion 2)
    (hn : 4 ≤ n) (hSig : SelfEnergyShapesUpTo Sig (n - 1)) (hsh : SelfEnergyShape n (Sig n)) :
    ∃ 𝔖 : ℝ → ℂ, ∀ κ : ℝ, 0 < κ → ∀ D : ℝ, ∃ C W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ,
      |E| < 2 - κ →
        ‖ValZ.rowSum Sig P.ψ n E W - (((W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) : ℝ) : ℂ) * 𝔖 E‖ ≤
          C * (W : ℝ) ^ (-D) := by
  refine ⟨fun E => limUnder atTop fun W : ℕ =>
    (((W : ℝ) ^ (((n : ℝ) - 2) * d / 2) : ℝ) : ℂ) * ValZ.rowSum Sig P.ψ n E W,
    fun κ hκ D => ?_⟩
  obtain ⟨𝔖κ, h𝔖⟩ := FT1c_expand hd P n Sig hn hSig hsh hκ
  obtain ⟨C, W₀, hC⟩ := h𝔖 D
  refine ⟨C, W₀, fun W hW E hE => ?_⟩
  have hlim : (limUnder atTop fun W : ℕ =>
      (((W : ℝ) ^ (((n : ℝ) - 2) * d / 2) : ℝ) : ℂ) * ValZ.rowSum Sig P.ψ n E W) = 𝔖κ E := by
    refine (FT1c_tendsto ?_).limUnder_eq
    obtain ⟨C', W₀', hC'⟩ := h𝔖 ((((n : ℝ) - 2) * d / 2) + 1)
    exact ⟨C', W₀', fun W hW => hC' W hW E hE⟩
  simp only
  rw [hlim]
  exact hC W hW E hE

end RBM8D
